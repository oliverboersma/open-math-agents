import FormalConjectures.ErdosProblems.«1164»

/-!
Assembled proof of erdos-1164 from upstream reductions R1, R1.H2.R1 and
verified step proofs R1.H1, R1.H2.R1.H1, and R1.H2.R1.H2.
-/

section R1Defs
open MeasureTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace OMA.R_Erdos1164_erdos_1164_R1

open Erdos1165 Erdos1164

-- H1 (lower half: the disc of radius e^{c √(log n)} is covered). Révész (1990) and Kesten; see
-- Dembo, Peres, Rosen and Zeitouni, Ann. of Math. 160 (2004), Section 1.3: the probability that the
-- disc of radius r is covered by time e^{t (log r)^2} has liminf at least e^{-b/t}, so it tends to 1
-- as t → ∞. Elementary proof: the walk makes at least δ log n returns to the origin with probability
-- at least 1 - ε/2, and each excursion from the origin hits a given x with |x| ≤ r before returning
-- with probability at least c₀ / log r. A union bound over the (2r + 1)^2 sites finishes the proof.
def H1 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (ℙ {ω | c * Real.sqrt (Real.log n) ≤ Real.log (coveringRadius X n ω)}).toReal

-- H2 (upper half: some site within radius e^{C √(log n)} is missed). Révész (1990) and Kesten; DPRZ04,
-- Section 1.3: the probability that the disc of radius r is covered by time e^{t (log r)^2} has limsup
-- at most e^{-a/t}, which tends to 0 as t → 0. DPRZ04, Theorem 1.4, gives the exact limit e^{-4/t}.
def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ},
    IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (ℙ {ω | Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n)}).toReal

lemma coveringRadius_congr {Ω Ω' : Type*} {X : ℕ → Ω → ℤ × ℤ} {Y : ℕ → Ω' → ℤ × ℤ} {ω : Ω}
    {ω' : Ω'} {n : ℕ} (h : ∀ i < n, X i ω = Y i ω') :
    coveringRadius X n ω = coveringRadius Y n ω' := by
  have hp : ∀ k ≤ n, position X k ω = position Y k ω' := fun k hk ↦
    Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)
  unfold coveringRadius Covers
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hc x hx
    obtain ⟨k, hk, hpos⟩ := hc x hx
    exact ⟨k, hk, (hp k hk).symm.trans hpos⟩
  · intro hc x hx
    obtain ⟨k, hk, hpos⟩ := hc x hx
    exact ⟨k, hk, (hp k hk).trans hpos⟩

lemma measurable_coveringRadius {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable fun ω ↦ coveringRadius X n ω := by
  let g : (Fin n → ℤ × ℤ) → ℕ := fun z ↦
    coveringRadius (fun i (z : Fin n → ℤ × ℤ) ↦ if h : i < n then z ⟨i, h⟩ else 0) n z
  have hg : Measurable g := measurable_of_countable g
  have hF : Measurable fun ω (i : Fin n) ↦ X i ω := measurable_pi_iff.mpr fun i ↦ hX i
  have e : (fun ω ↦ coveringRadius X n ω) = g ∘ fun ω (i : Fin n) ↦ X i ω := by
    funext ω
    exact coveringRadius_congr fun i hi ↦ by simp [hi]
  rw [e]
  exact hg.comp hF

lemma meas_event {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : ∀ k, Measurable (X k)) (n : ℕ) (P : ℕ → Prop) :
    MeasurableSet {ω | P (coveringRadius X n ω)} :=
  measurable_coveringRadius hX n (Set.to_countable {k : ℕ | P k}).measurableSet

end OMA.R_Erdos1164_erdos_1164_R1
end R1Defs

section H1Sec
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165

namespace OMA.H1Proof

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

/-- Number of visits to the origin at times `0, …, n`. -/
def visits (y : ℕ → ℤ × ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun t ↦ pos y t = 0).card

def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` coordinates. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

lemma visits_congr {y y' : ℕ → ℤ × ℤ} {n : ℕ} (h : ∀ i < n, y i = y' i) :
    visits y n = visits y' n := by
  unfold visits
  congr 1
  refine Finset.filter_congr fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [pos_congr h (by omega)]

/-- extension by zero of a finite window -/
def ext (m : ℕ) (z : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ if h : i < m then z ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma det_pre {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A)
    (j : ℕ) : {ω | sh j (path X ω) ∈ A} =
      (fun ω (i : Fin m) ↦ X (j + i) ω) ⁻¹' {z | ext m z ∈ A} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]

lemma meas_window {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (m j : ℕ) :
    Measurable (fun ω (i : Fin m) ↦ X (j + i) ω) :=
  measurable_pi_iff.mpr fun _ ↦ hX.measurable _

lemma det_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (j : ℕ) :
    MeasurableSet {ω | sh j (path X ω) ∈ A} := by
  rw [det_pre X hA j]
  exact meas_window hX m j (Set.to_countable _).measurableSet

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

/-- fixed-time Markov property: shifting does not change probabilities -/
lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]

end OMA.H1Proof

namespace OMA.H1Proof

lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

/-- independence of disjoint blocks, combined with the Markov property -/
lemma prob_block {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {t s : ℕ}
    {A B : Set (ℕ → ℤ × ℤ)} (hA : Det t A) (hB : Det s B) :
    ℙ {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      ℙ {ω | path X ω ∈ A} * ℙ {ω | path X ω ∈ B} := by
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hind := hX.indep.indepFun_finset (Finset.range t) (Finset.Ico t (t + s)) hdisj
    hX.measurable
  have hset : {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      {ω | path X ω ∈ A} ∩ {ω | sh t (path X ω) ∈ B} := rfl
  rw [hset, ← prob_shift hX hB t, preA X hA, preB X hB]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet

end OMA.H1Proof

namespace OMA.H1Proof

/-- number of `±1` paths of length `t` ending at `u` -/
def c : ℕ → ℤ → ℕ
  | 0, u => if u = 0 then 1 else 0
  | t + 1, u => c t (u - 1) + c t (u + 1)

lemma c_neg : ∀ (t : ℕ) (u : ℤ), u < -(t : ℤ) → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_neg t (u - 1) (by push_cast at h; omega), c_neg t (u + 1) (by push_cast at h; omega)]

lemma c_odd : ∀ (t : ℕ) (u : ℤ), ((t : ℤ) + u) % 2 = 1 → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_odd t (u - 1) (by push_cast at h; omega), c_odd t (u + 1) (by push_cast at h; omega)]

lemma c_choose : ∀ (t i : ℕ), c t (2 * (i : ℤ) - t) = t.choose i
  | 0, i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [c]
    · simp [c, Nat.choose_eq_zero_of_lt h]; omega
  | t + 1, 0 => by
    simp only [c, Nat.choose_zero_right]
    rw [c_neg t _ (by push_cast; omega)]
    have := c_choose t 0
    simp only [Nat.choose_zero_right] at this
    rw [show (2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((0 : ℕ) : ℤ) - (t : ℤ) by
      push_cast; ring, this]
  | t + 1, i + 1 => by
    simp only [c, Nat.choose_succ_succ]
    have h1 := c_choose t i
    have h2 := c_choose t (i + 1)
    rw [show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) - 1) = 2 * (i : ℤ) - t by push_cast; ring,
      show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((i + 1 : ℕ) : ℤ) - t by
        push_cast; ring, h1, h2]

lemma c_even (j : ℕ) : c (2 * j) 0 = j.centralBinom := by
  have := c_choose (2 * j) j
  rw [show (2 * (j : ℤ) - ((2 * j : ℕ) : ℤ)) = 0 by push_cast; ring] at this
  rw [this, Nat.centralBinom_eq_two_mul_choose]

lemma c_odd0 (j : ℕ) : c (2 * j + 1) 0 = 0 := c_odd _ _ (by push_cast; omega)

/-- the 2D count factorizes after the 45 degree rotation -/
lemma c_step (t : ℕ) (a b : ℤ) :
    c (t + 1) (a + b) * c (t + 1) (a - b) =
      c t ((a - 1) + b) * c t ((a - 1) - b) + c t ((a + 1) + b) * c t ((a + 1) - b) +
      c t (a + (b - 1)) * c t (a - (b - 1)) + c t (a + (b + 1)) * c t (a - (b + 1)) := by
  simp only [c]
  rw [show a - 1 + b = a + b - 1 by ring, show a - 1 - b = a - b - 1 by ring,
    show a + 1 + b = a + b + 1 by ring, show a + 1 - b = a - b + 1 by ring,
    show a + (b - 1) = a + b - 1 by ring, show a - (b - 1) = a - b + 1 by ring,
    show a + (b + 1) = a + b + 1 by ring, show a - (b + 1) = a - b - 1 by ring]
  ring

end OMA.H1Proof

namespace OMA.H1Proof

def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

lemma steps_eq : steps = (stepsF : Set (ℤ × ℤ)) := by
  simp [steps, stepsF]

lemma prob_step {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) (S : Set (ℤ × ℤ)) :
    ℙ (X k ⁻¹' S) = (4 : ℝ≥0∞)⁻¹ * Measure.count (steps ∩ S) := by
  have hu : Measure.map (X k) ℙ = ProbabilityTheory.cond Measure.count steps := hX.isUniform k
  rw [← Measure.map_apply (hX.measurable k) (Set.to_countable S).measurableSet, hu,
    ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet, steps_eq,
    Measure.count_apply_finset]
  rfl

lemma prob_step_eq {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) {e : ℤ × ℤ} (he : e ∈ steps) :
    ℙ (X k ⁻¹' {e}) = (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_step hX, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr he),
    Measure.count_singleton, mul_one]

lemma prob_step_bad {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) : ℙ (X k ⁻¹' stepsᶜ) = 0 := by
  rw [prob_step hX, Set.inter_compl_self, measure_empty, mul_zero]

lemma det_pos (t : ℕ) (z : ℤ × ℤ) : Det t {y | pos y t = z} := fun y y' h hy ↦ by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← pos_congr h le_rfl, hy]

lemma det_zero (e : ℤ × ℤ) : Det 1 {y | y 0 = e} := fun y y' h hy ↦ by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← h 0 one_pos, hy]

lemma prob_pos_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ)
    (he : e ∈ steps) :
    ℙ {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} =
      ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_block hX (det_pos t (x - e)) (det_zero e)]
  congr 1
  exact prob_step_eq hX 0 he

lemma pos_succ (y : ℕ → ℤ × ℤ) (t : ℕ) : pos y (t + 1) = pos y t + y t :=
  Finset.sum_range_succ _ _

/-- the return probability bound, in counting form -/
lemma prob_pos_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t ≤
      ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞)
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      simp only [c, add_zero, sub_self, if_true, mul_one, Nat.cast_one]
      exact prob_le_one
    · have : {ω | pos (path X ω) 0 = (a, b)} = ∅ := by
        ext ω
        simp only [pos, Finset.range_zero, Finset.sum_empty, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        exact fun h' ↦ h h'.symm
      rw [this, measure_empty]
      simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hsub : {ω | pos (path X ω) (t + 1) = x} ⊆
        (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ∪ X t ⁻¹' stepsᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq, pos_succ] at hω
      by_cases hs : X t ω ∈ steps
      · have hx : pos (path X ω) t = x - X t ω := by rw [← hω]; simp [path]
        have hE : ω ∈ E (X t ω) := ⟨hx, rfl⟩
        simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h | h | h | h <;> rw [h] at hE <;> simp [hE]
      · exact Or.inr hs
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) ≤
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      apply le_of_eq
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hm : ℙ {ω | pos (path X ω) (t + 1) = x} ≤
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [prob_step_bad hX t, add_zero]
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      exact measure_union_le _ _
    calc ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1)
        ≤ (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) :=
          by gcongr
      _ = ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by ring
      _ ≤ ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
        gcongr
        · refine (hE _ h1).trans ?_
          have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h2).trans ?_
          have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h3).trans ?_
          have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h4).trans ?_
          have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
      _ = ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞) := by
        rw [c_step]; push_cast; ring

end OMA.H1Proof

namespace OMA.H1Proof

lemma cb_sq_le (j : ℕ) (hj : 1 ≤ j) :
    ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j ≤ 1 / (Real.pi * j) := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.le_W j
  have h1 : Real.pi * j / (2 * j + 1) ≤ (2 * (j : ℝ) + 1) / (2 * j + 2) * (Real.pi / 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * (j : ℝ) + 1) * Real.pi * (2 * j + 1) =
        Real.pi * j * ((2 * j + 2) * 2) + Real.pi := by ring
    rw [this]
    linarith [Real.pi_pos]
  have h2 : Real.pi * j ≤ Real.Wallis.W j * (2 * j + 1) := by
    have := h1.trans hle
    rwa [div_le_iff₀ (by positivity)] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc (j.centralBinom : ℝ) ^ 2 * (Real.pi * j)
      ≤ (j.centralBinom : ℝ) ^ 2 * (Real.Wallis.W j * (2 * j + 1)) := by gcongr
    _ = Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by ring

/-- return probability, as a real number -/
noncomputable def u {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = 0}).toReal

lemma prob_zero_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) :
    u X t * 4 ^ t ≤ (c t 0 : ℝ) ^ 2 := by
  have h := prob_pos_le hX t 0 0
  simp only [add_zero, sub_zero] at h
  change ℙ {ω | pos (path X ω) t = 0} * 4 ^ t ≤ _ at h
  have h' : (ℙ {ω | pos (path X ω) t = 0} * 4 ^ t).toReal ≤ ((c t 0 * c t 0 : ℕ) : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  unfold u
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at h'
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal * 4 ^ t ≤ ((c t 0 * c t 0 : ℕ) : ℝ) := h'
    _ = (c t 0 : ℝ) ^ 2 := by push_cast; ring

lemma u_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : 0 ≤ u X t :=
  ENNReal.toReal_nonneg

lemma u_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : u X t ≤ 1 := by
  unfold u
  have : ℙ {ω | pos (path X ω) t = 0} ≤ 1 := prob_le_one
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) this
    _ = 1 := by simp

lemma u_odd {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) : u X (2 * j + 1) = 0 := by
  have h := prob_zero_le hX (2 * j + 1)
  rw [c_odd0] at h
  have h0 := u_nonneg X (2 * j + 1)
  have hp : (0 : ℝ) < 4 ^ (2 * j + 1) := by positivity
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  nlinarith

lemma u_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) (hj : 1 ≤ j) :
    u X (2 * j) ≤ 1 / (Real.pi * j) := by
  have h := prob_zero_le hX (2 * j)
  rw [c_even, pow_mul] at h
  norm_num at h
  refine le_trans ?_ (cb_sq_le j hj)
  rw [le_div_iff₀ (by positivity)]
  exact h

lemma u_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (ht : 1 ≤ t) :
    u X t ≤ 2 / (Real.pi * t) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
  · have hj : 1 ≤ j := by omega
    refine (u_even hX j hj).trans (le_of_eq ?_)
    have : (j : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [u_odd hX]
    positivity

lemma u_pair {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    u X (2 * j + 1) + u X (2 * j + 2) ≤ 1 / (Real.pi * ((j : ℝ) + 1)) := by
  rw [u_odd hX, zero_add, show 2 * j + 2 = 2 * (j + 1) by ring]
  have := u_even hX (j + 1) (by omega)
  push_cast at this
  exact this

end OMA.H1Proof

namespace OMA.H1Proof

def NoRet (m : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ s, 1 ≤ s → s ≤ m → pos y s ≠ 0}

def FR (t : ℕ) : Set (ℕ → ℤ × ℤ) := {y | pos y t = 0 ∧ ∀ s, 1 ≤ s → s < t → pos y s ≠ 0}

def Vis (n k : ℕ) : Set (ℕ → ℤ × ℤ) := {y | k ≤ visits y n}

lemma det_noRet (m : ℕ) : Det m (NoRet m) := fun y y' h hy s h1 h2 ↦ by
  rw [← pos_congr h h2]; exact hy s h1 h2

lemma det_FR (t : ℕ) : Det t (FR t) := fun y y' h hy ↦
  ⟨by rw [← pos_congr h le_rfl]; exact hy.1,
   fun s h1 h2 ↦ by rw [← pos_congr h h2.le]; exact hy.2 s h1 h2⟩

lemma det_vis (n k : ℕ) : Det n (Vis n k) := fun y y' h hy ↦ by
  simp only [Vis, Set.mem_setOf_eq] at hy ⊢
  rw [← visits_congr h]; exact hy

lemma visits_mono (y : ℕ → ℤ × ℤ) {m n : ℕ} (h : m ≤ n) : visits y m ≤ visits y n :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

lemma pos_zero (y : ℕ → ℤ × ℤ) : pos y 0 = 0 := by simp [pos]

lemma pos_sh (y : ℕ → ℤ × ℤ) {t : ℕ} (ht : pos y t = 0) (s : ℕ) :
    pos (sh t y) s = pos y (t + s) := by
  rw [pos_shift, ht, zero_add]

lemma renewal_subset (n k : ℕ) (hk : 1 ≤ k) :
    Vis n (k + 1) ⊆ {y | ∃ t ∈ Finset.Icc 1 n, y ∈ FR t ∧ sh t y ∈ Vis (n - t) k} := by
  intro y hy
  simp only [Vis, Set.mem_setOf_eq, visits] at hy
  set V := (Finset.range (n + 1)).filter fun t ↦ pos y t = 0 with hV
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hcard : k ≤ (V.erase 0).card := by rw [Finset.card_erase_of_mem h0]; omega
  have hne : (V.erase 0).Nonempty := Finset.card_pos.mp (by omega)
  set t := (V.erase 0).min' hne with ht
  have htm : t ∈ V.erase 0 := Finset.min'_mem _ hne
  have htm' := Finset.mem_erase.mp htm
  have htV := Finset.mem_filter.mp htm'.2
  have htn : t < n + 1 := Finset.mem_range.mp htV.1
  refine ⟨t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨htV.2, fun s h1 h2 hs ↦ ?_⟩, ?_⟩
  · have hsV : s ∈ V.erase 0 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩⟩
    have := Finset.min'_le (V.erase 0) s hsV
    omega
  · simp only [Vis, Set.mem_setOf_eq, visits]
    refine hcard.trans (Finset.card_le_card_of_injOn (fun a ↦ a - t) ?_ ?_)
    · intro a ha
      have ha' := Finset.mem_erase.mp ha
      have haV := Finset.mem_filter.mp ha'.2
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have han : a < n + 1 := Finset.mem_range.mp haV.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (show a - t < n - t + 1 by omega), ?_⟩
      rw [pos_sh y htV.2, show t + (a - t) = a by omega]
      exact haV.2
    · intro a ha b hb hab
      have hta : t ≤ a := Finset.min'_le (V.erase 0) a ha
      have htb : t ≤ b := Finset.min'_le (V.erase 0) b hb
      have hab' : a - t = b - t := hab
      omega

lemma lastexit_subset (n : ℕ) :
    Set.univ ⊆ {y | ∃ t ∈ Finset.range (n + 1), y ∈ {y | pos y t = 0} ∧ sh t y ∈ NoRet (n - t)} := by
  intro y _
  set V := (Finset.range (n + 1)).filter fun t ↦ pos y t = 0 with hV
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hne : V.Nonempty := ⟨0, h0⟩
  set t := V.max' hne with ht
  have htV := Finset.mem_filter.mp (Finset.max'_mem V hne)
  refine ⟨t, htV.1, htV.2, fun s h1 h2 hs ↦ ?_⟩
  rw [pos_sh y htV.2] at hs
  have htn : t < n + 1 := Finset.mem_range.mp htV.1
  have hsV : t + s ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩
  have := Finset.le_max' V (t + s) hsV
  omega

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma renewal_step (hX : IsSimpleRandomWalkSteps X) (n k : ℕ) (hk : 1 ≤ k) :
    ℙ {ω | path X ω ∈ Vis n (k + 1)} ≤
      ℙ {ω | path X ω ∈ NoRet n}ᶜ * ℙ {ω | path X ω ∈ Vis n k} := by
  have hU : {ω | path X ω ∈ NoRet n}ᶜ = ⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, NoRet, Set.mem_iUnion, FR,
      Finset.mem_Icc, exists_prop, not_forall, not_not]
    constructor
    · rintro ⟨s, h1, h2, hs⟩
      classical
      let P : ℕ → Prop := fun s ↦ 1 ≤ s ∧ s ≤ n ∧ pos (path X ω) s = 0
      have hex : ∃ s, P s := ⟨s, h1, h2, hs⟩
      refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1⟩,
        (Nat.find_spec hex).2.2, fun r hr1 hr2 hr ↦ ?_⟩
      exact Nat.find_min hex hr2 ⟨hr1, by have := (Nat.find_spec hex).2.1; omega, hr⟩
    · rintro ⟨t, ⟨h1, h2⟩, ht, -⟩
      exact ⟨t, h1, h2, ht⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ FR t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  have hmeasFR : ∀ t, MeasurableSet {ω | path X ω ∈ FR t} := fun t ↦ by
    rw [path_eq]; exact det_meas hX (det_FR t) 0
  have hsum : ℙ {ω | path X ω ∈ NoRet n}ᶜ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} := by
    rw [hU, measure_biUnion_finset hdisj fun t _ ↦ hmeasFR t]
  calc ℙ {ω | path X ω ∈ Vis n (k + 1)}
      ≤ ℙ (⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (n - t) k}) := by
        refine measure_mono fun ω hω ↦ ?_
        obtain ⟨t, ht, h⟩ := renewal_subset n k hk hω
        exact Set.mem_iUnion₂.mpr ⟨t, ht, h⟩
    _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (n - t) k} :=
        measure_biUnion_finset_le _ _
    _ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} * ℙ {ω | path X ω ∈ Vis (n - t) k} :=
        Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_FR t) (det_vis (n - t) k)
    _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} * ℙ {ω | path X ω ∈ Vis n k} := by
        gcongr with t ht
        intro ω hω
        simp only [Set.mem_setOf_eq, Vis] at hω ⊢
        exact hω.trans (visits_mono _ (Nat.sub_le n t))
    _ = ℙ {ω | path X ω ∈ NoRet n}ᶜ * ℙ {ω | path X ω ∈ Vis n k} := by
        rw [hsum, Finset.sum_mul]

lemma renewal (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ∀ k : ℕ, ℙ {ω | path X ω ∈ Vis n (k + 1)} ≤ ℙ {ω | path X ω ∈ NoRet n}ᶜ ^ k
  | 0 => by rw [pow_zero]; exact prob_le_one
  | k + 1 => by
    rw [pow_succ']
    refine (renewal_step hX n (k + 1) (by omega)).trans ?_
    gcongr
    exact renewal hX n k

lemma lastexit (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    1 ≤ ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} := by
  calc (1 : ℝ≥0∞) = ℙ (Set.univ : Set Ω) := measure_univ.symm
    _ ≤ ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)}) := by
        refine measure_mono fun ω _ ↦ ?_
        obtain ⟨t, ht, h⟩ := lastexit_subset n (Set.mem_univ (path X ω))
        exact Set.mem_iUnion₂.mpr ⟨t, ht, h⟩
    _ ≤ ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} :=
        measure_biUnion_finset_le _ _
    _ = _ := Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_pos t 0) (det_noRet (n - t))

end OMA.H1Proof

namespace OMA.H1Proof

open Real

lemma sum_pairs (u : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ Finset.range (2 * M + 1), u t =
      u 0 + ∑ j ∈ Finset.range M, (u (2 * j + 1) + u (2 * j + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

lemma green_le (u : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu00 : u 0 ≤ 1)
    (hpair : ∀ j : ℕ, u (2 * j + 1) + u (2 * j + 2) ≤ 1 / (π * ((j : ℝ) + 1))) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), u t ≤ 1 + (1 + Real.log n) / π := by
  have hsub : ∑ t ∈ Finset.range (n + 1), u t ≤ ∑ t ∈ Finset.range (2 * n + 1), u t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun t _ _ ↦ hu0 t
  refine hsub.trans ?_
  rw [sum_pairs]
  have hh : ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2)) ≤ (harmonic n : ℝ) / π := by
    calc ∑ j ∈ Finset.range n, (u (2 * j + 1) + u (2 * j + 2))
        ≤ ∑ j ∈ Finset.range n, 1 / (π * ((j : ℝ) + 1)) := Finset.sum_le_sum fun j _ ↦ hpair j
      _ = (harmonic n : ℝ) / π := by
        rw [harmonic, Rat.cast_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        push_cast
        rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  have hlog := harmonic_le_one_add_log n
  have : (harmonic n : ℝ) / π ≤ (1 + Real.log n) / π := by gcongr
  linarith

/-- the two-scale lower bound on the escape probability -/
lemma q_lower (u q : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu00 : u 0 ≤ 1)
    (hut : ∀ t : ℕ, 1 ≤ t → u t ≤ 2 / (π * t))
    (hpair : ∀ j : ℕ, u (2 * j + 1) + u (2 * j + 2) ≤ 1 / (π * ((j : ℝ) + 1)))
    (hq0 : ∀ m, 0 ≤ q m) (hq1 : ∀ m, q m ≤ 1) (hqa : Antitone q)
    (hle : ∀ n, 1 ≤ ∑ t ∈ Finset.range (n + 1), u t * q (n - t))
    (L : ℕ) (hL : 2 ≤ L) (m : ℕ) (hm : 1 ≤ m) :
    (1 - 2 / (π * ((L : ℝ) - 1))) * π ≤ q m * (π + 1 + Real.log L + Real.log m) := by
  set n := m * L with hn
  have hmn : m ≤ n := by rw [hn]; nlinarith
  have hsplit := Finset.sum_range_add_sum_Ico (fun t ↦ u t * q (n - t))
    (show n - m + 1 ≤ n + 1 by omega)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) - 1 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  -- the near part
  have hnear : ∑ t ∈ Finset.Ico (n - m + 1) (n + 1), u t * q (n - t) ≤
      2 / (π * ((L : ℝ) - 1)) := by
    have hb : ∀ t ∈ Finset.Ico (n - m + 1) (n + 1), u t * q (n - t) ≤ 2 / (π * (m * ((L : ℝ) - 1))) := by
      intro t ht
      have ht' := Finset.mem_Ico.mp ht
      have hnat : m * (L - 1) ≤ t := by
        have : m * (L - 1) = n - m := by rw [hn, Nat.mul_sub_one]
        omega
      have hreal : (m : ℝ) * ((L : ℝ) - 1) ≤ t := by
        have := (Nat.cast_le (α := ℝ)).mpr hnat
        push_cast [Nat.cast_sub (show 1 ≤ L by omega)] at this
        exact this
      calc u t * q (n - t) ≤ u t * 1 := by gcongr; exact hu0 t; exact hq1 _
        _ = u t := mul_one _
        _ ≤ 2 / (π * t) := hut t (by
            have : 1 ≤ m * (L - 1) := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
            omega)
        _ ≤ 2 / (π * (m * ((L : ℝ) - 1))) := by gcongr
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      show n + 1 - (n - m + 1) = m by omega]
    rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- the far part
  have hfar : ∑ t ∈ Finset.range (n - m + 1), u t * q (n - t) ≤
      q m * (1 + (1 + Real.log n) / π) := by
    calc ∑ t ∈ Finset.range (n - m + 1), u t * q (n - t)
        ≤ ∑ t ∈ Finset.range (n - m + 1), u t * q m := by
          refine Finset.sum_le_sum fun t ht ↦ ?_
          have := Finset.mem_range.mp ht
          gcongr
          · exact hu0 t
          · exact hqa (by omega)
      _ ≤ ∑ t ∈ Finset.range (n + 1), u t * q m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            fun t _ _ ↦ mul_nonneg (hu0 t) (hq0 m)
      _ = q m * ∑ t ∈ Finset.range (n + 1), u t := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ q m * (1 + (1 + Real.log n) / π) := by
          gcongr
          · exact hq0 m
          · exact green_le u hu0 hu00 hpair n
  have h1 := hle n
  rw [← hsplit] at h1
  have hlogn : Real.log n = Real.log m + Real.log L := by
    rw [hn, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  rw [hlogn] at hfar
  have key : 1 - 2 / (π * ((L : ℝ) - 1)) ≤
      q m * (1 + (1 + (Real.log m + Real.log L)) / π) := by linarith
  have e : q m * (1 + (1 + (Real.log m + Real.log L)) / π) * π =
      q m * (π + 1 + Real.log L + Real.log m) := by
    rw [mul_assoc, add_mul, div_mul_cancel₀ _ hpi.ne']; ring
  rw [← e]
  exact mul_le_mul_of_nonneg_right key hpi.le

end OMA.H1Proof

namespace OMA.H1Proof

open Real

noncomputable def q {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (m : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ NoRet m}).toReal

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma q_nonneg (m : ℕ) : 0 ≤ q X m := ENNReal.toReal_nonneg

lemma q_le_one (m : ℕ) : q X m ≤ 1 := by
  unfold q
  calc (ℙ {ω | path X ω ∈ NoRet m}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) prob_le_one
    _ = 1 := by simp

lemma q_anti : Antitone (q X) := by
  intro a b hab
  unfold q
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω s h1 h2 ↦ ?_)
  exact hω s h1 (h2.trans hab)

lemma q_lastexit (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    1 ≤ ∑ t ∈ Finset.range (n + 1), u X t * q X (n - t) := by
  have h := lastexit hX n
  have hne : ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun t _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono hne h
  rw [ENNReal.toReal_sum fun t _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
    at h'
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul] at h'
  exact h'

lemma tail (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    ℙ {ω | path X ω ∈ Vis n (j + 1)} ≤ ENNReal.ofReal ((1 - q X n) ^ j) := by
  refine (renewal hX n j).trans (le_of_eq ?_)
  have hmeas : MeasurableSet {ω | path X ω ∈ NoRet n} := by
    rw [path_eq]; exact det_meas hX (det_noRet n) 0
  rw [prob_compl_eq_one_sub hmeas, ENNReal.ofReal_pow (by linarith [q_le_one (X := X) n])]
  congr 1
  unfold q
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

end OMA.H1Proof

namespace OMA.H3Proof
open OMA.H1Proof

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma meas_block (hX : IsSimpleRandomWalkSteps X) {t s : ℕ} {A B : Set (ℕ → ℤ × ℤ)}
    (hA : Det t A) (hB : Det s B) :
    MeasurableSet {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} := by
  have h1 : MeasurableSet {ω | path X ω ∈ A} := by rw [path_eq]; exact det_meas hX hA 0
  exact h1.inter (det_meas hX hB t)

/-- the return probability lower bound, in counting form -/
lemma prob_pos_ge (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞) ≤
      ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      have : {ω | pos (path X ω) 0 = ((0 : ℤ), (0 : ℤ))} = Set.univ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, pos_zero]; rfl
      rw [this, measure_univ]
      simp [c]
    · have hc : c 0 (a + b) * c 0 (a - b) = 0 := by
        simp only [c]
        by_cases ha : a + b = 0
        · have : a - b ≠ 0 := by
            intro hb; apply h; ext <;> simp <;> omega
          simp [this]
        · simp [ha]
      rw [hc]; simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hEm : ∀ e, MeasurableSet (E e) := fun e ↦ meas_block hX (det_pos t _) (det_zero e)
    have hsub : (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ⊆
        {ω | pos (path X ω) (t + 1) = x} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, pos_succ]
      have key : ∀ e, ω ∈ E e → pos (path X ω) t + path X ω t = x := by
        rintro e ⟨h1, h2⟩
        simp only [Set.mem_setOf_eq] at h1 h2
        have : path X ω t = e := h2
        rw [h1, this]; abel
      rcases hω with ((h | h) | h) | h <;> exact key _ h
    have hd : ∀ e e', e ≠ e' → Disjoint (E e) (E e') := by
      intro e e' hne
      rw [Set.disjoint_left]
      rintro ω ⟨-, h1⟩ ⟨-, h2⟩
      exact hne ((show path X ω t = e from h1).symm.trans h2)
    have hsum : ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) ≤
        ℙ {ω | pos (path X ω) (t + 1) = x} := by
      refine le_trans (le_of_eq ?_) (measure_mono hsub)
      rw [measure_union _ (hEm _), measure_union _ (hEm _), measure_union _ (hEm _)]
      · exact hd _ _ (by decide)
      · exact Disjoint.union_left (hd _ _ (by decide)) (hd _ _ (by decide))
      · exact Disjoint.union_left (Disjoint.union_left (hd _ _ (by decide))
          (hd _ _ (by decide))) (hd _ _ (by decide))
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) =
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    calc ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞)
        = ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
          rw [c_step]; push_cast; ring
      _ ≤ ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by
        rw [hE _ h1, hE _ h2, hE _ h3, hE _ h4]
        gcongr
        · have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
      _ = (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) := by ring
      _ ≤ ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1) := by gcongr

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma cb_sq_ge (j : ℕ) : 1 / (π * ((j : ℝ) + 1)) ≤ ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.W_le j
  have hpi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1))
      ≤ π / 2 * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by gcongr
    _ ≤ (j.centralBinom : ℝ) ^ 2 * (π * ((j : ℝ) + 1)) := by nlinarith

lemma u_even_ge (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    1 / (π * ((j : ℝ) + 1)) ≤ u X (2 * j) := by
  have h := prob_pos_ge hX (2 * j) 0 0
  simp only [add_zero, sub_zero] at h
  change _ ≤ ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j) at h
  have h' : ((c (2 * j) 0 * c (2 * j) 0 : ℕ) : ℝ≥0∞).toReal ≤
      (ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, c_even, pow_mul] at h'
  norm_num at h'
  refine (cb_sq_ge j).trans ?_
  rw [div_le_iff₀ (by positivity)]
  unfold u
  nlinarith

lemma green_ge (hX : IsSimpleRandomWalkSteps X) (M : ℕ) :
    Real.log (M + 1) / π ≤ ∑ t ∈ Finset.range (2 * M + 1), u X t := by
  have hpi := Real.pi_pos
  rw [sum_pairs]
  have h0 : 1 ≤ u X 0 := by
    have hu : u X 0 = 1 := by
      unfold u
      have : {ω | pos (path X ω) 0 = 0} = Set.univ := by
        ext ω; simp [pos_zero]
      rw [this, measure_univ]; simp
    rw [hu]
  have hs : ∑ j ∈ Finset.range M, 1 / (π * (((j + 1 : ℕ) : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range M, (u X (2 * j + 1) + u X (2 * j + 2)) := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have := u_even_ge hX (j + 1)
    rw [show 2 * (j + 1) = 2 * j + 2 by ring] at this
    linarith [u_nonneg X (2 * j + 1)]
  have hH : ∑ j ∈ Finset.range M, 1 / (π * (((j + 1 : ℕ) : ℝ) + 1)) =
      ((harmonic (M + 1) : ℝ) - 1) / π := by
    rw [harmonic, Finset.sum_range_succ', Rat.cast_add, Rat.cast_sum]
    simp only [Nat.cast_add, Nat.cast_one, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, zero_add, inv_one, add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  have hlog := log_add_one_le_harmonic (M + 1)
  have hcast : Real.log ((M : ℝ) + 1) ≤ Real.log (((M + 1 + 1 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have e : Real.log (M + 1) / π ≤ 1 + ((harmonic (M + 1) : ℝ) - 1) / π := by
    have h1 : Real.log (M + 1) / π ≤ (harmonic (M + 1) : ℝ) / π := by
      gcongr; exact hcast.trans hlog
    have h2 : (harmonic (M + 1) : ℝ) / π = ((harmonic (M + 1) : ℝ) - 1) / π + 1 / π := by ring
    have h3 : 1 / π ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
    linarith
  linarith

lemma lastexit_le (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1),
      ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)} ≤ 1 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1))) fun t ↦
      {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_setOf_eq] at h1 h3
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    rcases lt_or_gt_of_ne hab with h | h
    · apply h2 (b - a) (by omega) (by omega)
      rw [pos_sh _ h1, show a + (b - a) = b by omega]; exact h3
    · apply h4 (a - b) (by omega) (by omega)
      rw [pos_sh _ h3, show b + (a - b) = a by omega]; exact h1
  calc ∑ t ∈ Finset.range (n + 1),
        ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ NoRet (n - t)}
      = ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)} :=
        Finset.sum_congr rfl fun t _ ↦ (prob_block hX (det_pos t 0) (det_noRet (n - t))).symm
    _ = ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ NoRet (n - t)}) :=
        (measure_biUnion_finset hdisj fun t _ ↦ meas_block hX (det_pos t 0)
          (det_noRet (n - t))).symm
    _ ≤ 1 := prob_le_one

lemma q_green (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    q X n * ∑ t ∈ Finset.range (n + 1), u X t ≤ 1 := by
  have h := lastexit_le hX n
  have hne : ∀ t ∈ Finset.range (n + 1), ℙ {ω | pos (path X ω) t = 0} *
      ℙ {ω | path X ω ∈ NoRet (n - t)} ≠ ⊤ := fun t _ ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono ENNReal.one_ne_top h
  rw [ENNReal.toReal_sum hne] at h'
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul] at h'
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun t ht ↦ ?_) h'
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (q_anti (Nat.sub_le n t)) (u_nonneg X t)

/-- the upper bound on the escape probability at even times -/
lemma q_le (hX : IsSimpleRandomWalkSteps X) (M : ℕ) :
    q X (2 * M) * Real.log (M + 1) ≤ π := by
  have hpi := Real.pi_pos
  have h1 := q_green hX (2 * M)
  have h2 := green_ge hX M
  have h3 : q X (2 * M) * (Real.log (M + 1) / π) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left h2 (q_nonneg _)) h1
  have e : q X (2 * M) * Real.log (M + 1) = q X (2 * M) * (Real.log (M + 1) / π) * π := by
    rw [mul_assoc, div_mul_cancel₀ _ hpi.ne']
  rw [e]
  nlinarith

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real

lemma visits_sh_le (y : ℕ → ℤ × ℤ) {t n N : ℕ} (ht : 1 ≤ t) (hp : pos y t = 0)
    (hN : t + n ≤ N) : visits (sh t y) n + 1 ≤ visits y N := by
  unfold visits
  set V := (Finset.range (N + 1)).filter fun a ↦ pos y a = 0
  have h0 : 0 ∈ V := Finset.mem_filter.mpr ⟨by simp, pos_zero y⟩
  have hc := Finset.card_erase_of_mem h0
  have hle : ((Finset.range (n + 1)).filter fun a ↦ pos (sh t y) a = 0).card ≤ (V.erase 0).card := by
    refine Finset.card_le_card_of_injOn (fun a ↦ t + a) ?_ ?_
    · intro a ha
      have ha' := Finset.mem_filter.mp ha
      have han := Finset.mem_range.mp ha'.1
      refine Finset.mem_erase.mpr ⟨show t + a ≠ 0 by omega, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (show t + a < N + 1 by omega), ?_⟩⟩
      show pos y (t + a) = 0
      rw [← pos_sh y hp]; exact ha'.2
    · intro a _ b _ hab
      have : t + a = t + b := hab
      omega
  have hpos : 0 < V.card := Finset.card_pos.mpr ⟨0, h0⟩
  omega

lemma det_compl {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) : Det m Aᶜ :=
  fun y y' h hy hy' ↦ hy (hA y' y (fun i hi ↦ (h i hi).symm) hy')

lemma sh_sh (a b : ℕ) (y : ℕ → ℤ × ℤ) : sh a (sh b y) = sh (b + a) y :=
  funext fun i ↦ by simp [sh, add_assoc]

/-- no block of length `M` among the first `N` blocks has `v` visits to its start -/
def Bad (M v N : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ i < N, sh (i * M) y ∉ Vis M v}

lemma det_bad (M v N : ℕ) : Det (N * M) (Bad M v N) := by
  intro y y' h hy i hi hv
  apply hy i hi
  refine det_vis M v _ _ (fun j hj ↦ ?_) hv
  simp only [sh]
  have : i * M + j < N * M := by
    have : (i + 1) * M ≤ N * M := Nat.mul_le_mul_right M hi
    nlinarith
  exact (h _ this).symm

lemma bad_succ (M v N : ℕ) :
    Bad M v (N + 1) = {y | y ∈ (Vis M v)ᶜ ∧ sh M y ∈ Bad M v N} := by
  ext y
  simp only [Bad, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · intro h
    refine ⟨?_, fun i hi ↦ ?_⟩
    · have := h 0 (by omega)
      rwa [Nat.zero_mul, sh_zero] at this
    rw [sh_sh, show M + i * M = (i + 1) * M by ring]
    exact h (i + 1) (by omega)
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · rw [Nat.zero_mul, sh_zero]; exact h0
    · have := h i (by omega)
      rwa [sh_sh, show M + i * M = (i + 1) * M by ring] at this

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma prob_bad (hX : IsSimpleRandomWalkSteps X) (M v : ℕ) :
    ∀ N, ℙ {ω | path X ω ∈ Bad M v N} = ℙ {ω | path X ω ∈ (Vis M v)ᶜ} ^ N
  | 0 => by
    have : {ω | path X ω ∈ Bad M v 0} = Set.univ := by
      ext ω; simp [Bad]
    rw [this, measure_univ, pow_zero]
  | N + 1 => by
    rw [bad_succ, pow_succ', ← prob_bad hX M v N]
    exact prob_block hX (det_compl (det_vis M v)) (det_bad M v N)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma compl_noRet (hX : IsSimpleRandomWalkSteps X) (n : ℕ) :
    ℙ {ω | path X ω ∈ NoRet n}ᶜ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ FR t} := by
  have hU : {ω | path X ω ∈ NoRet n}ᶜ = ⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ FR t} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, NoRet, Set.mem_iUnion, FR,
      Finset.mem_Icc, exists_prop, not_forall, not_not]
    constructor
    · rintro ⟨s, h1, h2, hs⟩
      classical
      let P : ℕ → Prop := fun s ↦ 1 ≤ s ∧ s ≤ n ∧ pos (path X ω) s = 0
      have hex : ∃ s, P s := ⟨s, h1, h2, hs⟩
      refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.1⟩,
        (Nat.find_spec hex).2.2, fun r hr1 hr2 hr ↦ ?_⟩
      exact Nat.find_min hex hr2 ⟨hr1, by have := (Nat.find_spec hex).2.1; omega, hr⟩
    · rintro ⟨t, ⟨h1, h2⟩, ht, -⟩
      exact ⟨t, h1, h2, ht⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ FR t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  rw [hU, measure_biUnion_finset hdisj fun t _ ↦ by rw [path_eq]; exact det_meas hX (det_FR t) 0]

lemma renewal_lower (hX : IsSimpleRandomWalkSteps X) (s : ℕ) :
    ∀ k, ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ k ≤ ℙ {ω | path X ω ∈ Vis (k * s) (k + 1)}
  | 0 => by
    have : {ω | path X ω ∈ Vis (0 * s) (0 + 1)} = Set.univ := by
      ext ω
      simp only [Vis, Set.mem_setOf_eq, Set.mem_univ, iff_true, visits]
      exact Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨by simp, pos_zero _⟩⟩
    rw [this, measure_univ, pow_zero]
  | k + 1 => by
    have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 s)) fun t ↦
        {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)} := by
      intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨h1, -⟩ ⟨h2, -⟩
      simp only [FR, Set.mem_setOf_eq] at h1 h2
      rcases lt_or_gt_of_ne hab with h | h
      · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
      · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
    calc ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ (k + 1)
        = ℙ {ω | path X ω ∈ NoRet s}ᶜ * ℙ {ω | path X ω ∈ NoRet s}ᶜ ^ k := pow_succ' _ _
      _ ≤ ℙ {ω | path X ω ∈ NoRet s}ᶜ * ℙ {ω | path X ω ∈ Vis (k * s) (k + 1)} := by
          gcongr; exact renewal_lower hX s k
      _ = ∑ t ∈ Finset.Icc 1 s,
            ℙ {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)} := by
          rw [compl_noRet hX, Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ ↦
            (prob_block hX (det_FR t) (det_vis (k * s) (k + 1))).symm
      _ = ℙ (⋃ t ∈ Finset.Icc 1 s,
            {ω | path X ω ∈ FR t ∧ sh t (path X ω) ∈ Vis (k * s) (k + 1)}) :=
          (measure_biUnion_finset hdisj fun t _ ↦
            meas_block hX (det_FR t) (det_vis _ _)).symm
      _ ≤ ℙ {ω | path X ω ∈ Vis ((k + 1) * s) (k + 1 + 1)} := by
          refine measure_mono fun ω hω ↦ ?_
          obtain ⟨t, ht, h1, h2⟩ := Set.mem_iUnion₂.mp hω
          have ht' := Finset.mem_Icc.mp ht
          simp only [Vis, Set.mem_setOf_eq] at h2 ⊢
          have := visits_sh_le (path X ω) ht'.1 h1.1
            (show t + k * s ≤ (k + 1) * s by nlinarith)
          omega

end OMA.H3Proof

namespace OMA.H3Proof
open Real

lemma one_sub_ge_exp {x : ℝ} (h1 : x < 1) : Real.exp (-(x / (1 - x))) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  have h := Real.add_one_le_exp (x / (1 - x))
  have e : x / (1 - x) + 1 = 1 / (1 - x) := by
    rw [div_add_one hp.ne', show x + (1 - x) = 1 by ring]
  rw [e] at h
  rw [Real.exp_neg]
  calc (Real.exp (x / (1 - x)))⁻¹ ≤ (1 / (1 - x))⁻¹ := by
        gcongr
    _ = 1 - x := by rw [one_div, inv_inv]

lemma fail_bound (b k N : ℕ) (hb : 2 ≤ b) (θ ℓ q : ℝ) (hθ0 : 0 ≤ θ) (hθ : 2 * b ≤ (1 - θ) * b ^ 2)
    (hℓ : b * π + 1 ≤ ℓ) (hk : (k : ℝ) * π ≤ θ * b ^ 2 * ℓ ^ 2 + π) (hq0 : 0 ≤ q)
    (hq : q * ((b - 1) * ℓ) ≤ π) (hN : (N : ℝ) = Real.exp (b * ℓ)) :
    (1 - (1 - q) ^ k) ^ N ≤ Real.exp (-(ℓ / 2)) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hℓ0 : 0 < ℓ := by nlinarith
  have hD : 0 < (b - 1) * ℓ := by nlinarith
  set x := π / ((b - 1) * ℓ) with hx
  have hqx : q ≤ x := by rw [hx, le_div_iff₀ hD]; exact hq
  have hx1 : x < 1 := by
    rw [hx, div_lt_one hD]; nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hD2 : 0 < (b - 1) * ℓ - π := by nlinarith
  -- k x/(1-x) ≤ (b - 1/2) ℓ
  have hkx : (k : ℝ) * (x / (1 - x)) ≤ (b - 1 / 2) * ℓ := by
    have e : x / (1 - x) = π / ((b - 1) * ℓ - π) := by
      rw [hx, one_sub_div hD.ne', div_div_div_cancel_right₀ hD.ne']
    rw [e, mul_div_assoc', div_le_iff₀ hD2]
    have hgap : 1 ≤ ((b : ℝ) - 1 / 2) * (b - 1) - θ * b ^ 2 := by nlinarith
    have hl : (b : ℝ) * π * ℓ + π ≤ ℓ ^ 2 := by nlinarith
    nlinarith
  have hpow : Real.exp (-((b - 1 / 2) * ℓ)) ≤ (1 - q) ^ k := by
    calc Real.exp (-((b - 1 / 2) * ℓ)) ≤ Real.exp (-((k : ℝ) * (x / (1 - x)))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-(x / (1 - x))) ^ k := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (1 - x) ^ k := pow_le_pow_left₀ (by positivity) (one_sub_ge_exp hx1) k
      _ ≤ (1 - q) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  have hr1 : (1 - q) ^ k ≤ 1 := by
    rcases le_or_gt q 1 with h | h
    · exact pow_le_one₀ (by linarith) (by linarith)
    · linarith [hqx]
  have hbase : 1 - (1 - q) ^ k ≤ Real.exp (-Real.exp (-((b - 1 / 2) * ℓ))) := by
    have := Real.one_sub_le_exp_neg (Real.exp (-((b - 1 / 2) * ℓ)))
    linarith
  calc (1 - (1 - q) ^ k) ^ N ≤ Real.exp (-Real.exp (-((b - 1 / 2) * ℓ))) ^ N :=
        pow_le_pow_left₀ (by linarith) hbase N
    _ = Real.exp (-(N * Real.exp (-((b - 1 / 2) * ℓ)))) := by rw [← Real.exp_nat_mul]; ring_nf
    _ = Real.exp (-Real.exp (ℓ / 2)) := by
        rw [hN, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(ℓ / 2)) := by
        have := Real.add_one_le_exp (ℓ / 2)
        exact Real.exp_le_exp.mpr (by linarith)

end OMA.H3Proof

namespace OMA.H3Proof
open OMA.H1Proof Real Filter

lemma interp_lower (f : ℕ → ℕ) (hf : Monotone f) (B : ℕ) (hB : 2 ≤ B) {κ κ1 ε : ℝ}
    (hε : 0 < ε) (hκ0 : 0 < κ) (hκ1 : κ1 = κ + ε / 2) (hκ : κ < 1)
    (h : ∀ᶠ j : ℕ in atTop, κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2 ≤ f (B ^ j)) :
    ∀ᶠ n : ℕ in atTop, κ * Real.log n ^ 2 ≤ f n := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp h
  set J2 := max J (⌈6 / ε⌉₊ + 1)
  refine eventually_atTop.mpr ⟨B ^ J2, fun n hn ↦ ?_⟩
  set j := Nat.log B n
  have hjJ : J2 ≤ j := Nat.le_log_of_pow_le (by omega) hn
  have hn0 : n ≠ 0 := by
    have : 0 < B ^ J2 := by positivity
    omega
  have hlow : B ^ j ≤ n := Nat.pow_log_le_self B hn0
  have hup : n < B ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have hfj := hJ j (le_trans (le_max_left _ _) hjJ)
  have hfn : (f (B ^ j) : ℝ) ≤ f n := by exact_mod_cast hf hlow
  have hLB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogj : Real.log ((B ^ j : ℕ) : ℝ) = j * Real.log B := by
    push_cast; rw [Real.log_pow]
  have hlogn : Real.log n ≤ (j + 1) * Real.log B := by
    calc Real.log n ≤ Real.log ((B ^ (j + 1) : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hup.le)
      _ = (j + 1) * Real.log B := by push_cast; rw [Real.log_pow]; push_cast; ring
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
  have hj6 : 6 / ε ≤ (j : ℝ) := by
    have h1 : ⌈6 / ε⌉₊ + 1 ≤ j := le_trans (le_max_right _ _) hjJ
    have h2 : (6 / ε) ≤ (⌈6 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈6 / ε⌉₊ : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h1
    linarith
  have hej : 6 ≤ ε * j := by
    have := (div_le_iff₀ hε).mp hj6
    linarith
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hsq : κ * ((j : ℝ) + 1) ^ 2 ≤ κ1 * (j : ℝ) ^ 2 := by
    have hj1 : (1 : ℝ) ≤ j := by
      have hne : j ≠ 0 := by
        rintro h0
        rw [h0, Nat.cast_zero, mul_zero] at hej
        linarith
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have h3j : 3 * (j : ℝ) ≤ ε / 2 * (j : ℝ) ^ 2 := by nlinarith
    have hk2 : κ * (2 * j + 1) ≤ 2 * j + 1 := by nlinarith
    rw [hκ1]; nlinarith
  calc κ * Real.log n ^ 2 ≤ κ * (((j : ℝ) + 1) * Real.log B) ^ 2 := by
        gcongr
    _ = κ * ((j : ℝ) + 1) ^ 2 * Real.log B ^ 2 := by ring
    _ ≤ κ1 * (j : ℝ) ^ 2 * Real.log B ^ 2 := by gcongr
    _ = κ1 * Real.log ((B ^ j : ℕ) : ℝ) ^ 2 := by rw [hlogj]; ring
    _ ≤ f (B ^ j) := hfj
    _ ≤ f n := hfn

end OMA.H3Proof


namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

/-- binomial coefficients near the centre: `C(2j, j+k) ≥ C(2j, j) (1 - 2k²/j)` -/
lemma choose_near (j : ℕ) (hj : 1 ≤ j) :
    ∀ k : ℕ, k ≤ j → (j.centralBinom : ℝ) * (1 - 2 * (k : ℝ) ^ 2 / j) ≤ ((2 * j).choose (j + k) : ℝ)
  | 0, _ => by simp [Nat.centralBinom_eq_two_mul_choose]
  | k + 1, hk => by
    have ih := choose_near j hj k (by omega)
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    have hrec := Nat.choose_succ_right_eq (2 * j) (j + k)
    have hrec' : ((2 * j).choose (j + k + 1) : ℝ) * ((j + k + 1 : ℕ) : ℝ) =
        ((2 * j).choose (j + k) : ℝ) * ((j - k : ℕ) : ℝ) := by
      have : 2 * j - (j + k) = j - k := by omega
      rw [this] at hrec
      exact_mod_cast hrec
    have hjk : ((j - k : ℕ) : ℝ) = j - k := by push_cast [Nat.cast_sub (show k ≤ j by omega)]; ring
    rw [hjk] at hrec'
    push_cast at hrec'
    have hpos : (0 : ℝ) < j + k + 1 := by positivity
    have hcb : (0 : ℝ) ≤ j.centralBinom := by positivity
    have hf : ((2 * j).choose (j + k + 1) : ℝ) =
        ((2 * j).choose (j + k) : ℝ) * ((j - k) / (j + k + 1)) := by
      rw [mul_div_assoc', eq_div_iff hpos.ne']
      exact hrec'
    rw [show j + (k + 1) = j + k + 1 by ring, hf]
    have hρ0 : 0 ≤ ((j : ℝ) - k) / (j + k + 1) := by
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
      apply div_nonneg <;> linarith
    have hρ : 1 - (2 * k + 1) / (j : ℝ) ≤ ((j : ℝ) - k) / (j + k + 1) := by
      rw [le_div_iff₀ hpos, sub_mul, div_mul_eq_mul_div, one_mul]
      have : (2 * (k : ℝ) + 1) * (j + k + 1) / j ≥ 2 * k + 1 := by
        rw [ge_iff_le, le_div_iff₀ hj']; nlinarith
      linarith
    have hk1 : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
    rcases le_or_gt (1 - 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j) 0 with hT | hT
    · exact (mul_nonpos_of_nonneg_of_nonpos hcb hT).trans (by positivity)
    have hT' : 2 * ((k + 1 : ℕ) : ℝ) ^ 2 < j := by
      have := (div_lt_one hj').mp (by linarith : 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j < 1)
      exact this
    push_cast at hT'
    have ha : 0 ≤ 1 - 2 * (k : ℝ) ^ 2 / j := by
      rw [sub_nonneg, div_le_one hj']; nlinarith
    have hb : 0 ≤ 1 - (2 * (k : ℝ) + 1) / j := by
      rw [sub_nonneg, div_le_one hj']; nlinarith
    calc (j.centralBinom : ℝ) * (1 - 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j)
        ≤ (j.centralBinom : ℝ) * ((1 - 2 * (k : ℝ) ^ 2 / j) * (1 - (2 * k + 1) / (j : ℝ))) := by
          gcongr
          have e : (1 - 2 * (k : ℝ) ^ 2 / j) * (1 - (2 * k + 1) / (j : ℝ)) =
              1 - (2 * k ^ 2 + 2 * k + 1) / j + 2 * k ^ 2 / j * ((2 * k + 1) / j) := by ring
          rw [e]
          have : 0 ≤ 2 * (k : ℝ) ^ 2 / j * ((2 * k + 1) / j) := by positivity
          have h2 : (2 * (k : ℝ) ^ 2 + 2 * k + 1) / j ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 / j := by
            gcongr; push_cast; nlinarith
          linarith
      _ = ((j.centralBinom : ℝ) * (1 - 2 * (k : ℝ) ^ 2 / j)) * (1 - (2 * k + 1) / (j : ℝ)) := by
          ring
      _ ≤ ((2 * j).choose (j + k) : ℝ) * (1 - (2 * k + 1) / (j : ℝ)) := by gcongr
      _ ≤ ((2 * j).choose (j + k) : ℝ) * (((j : ℝ) - k) / (j + k + 1)) := by gcongr

lemma choose_half (j k : ℕ) (hj : 1 ≤ j) (hk : 4 * k ^ 2 ≤ j) :
    (j.centralBinom : ℝ) / 2 ≤ ((2 * j).choose (j + k) : ℝ) := by
  have hkj : k ≤ j := by nlinarith
  refine le_trans ?_ (choose_near j hj k hkj)
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have : 2 * (k : ℝ) ^ 2 / j ≤ 1 / 2 := by
    rw [div_le_iff₀ hj']
    have : (4 * k ^ 2 : ℝ) ≤ j := by exact_mod_cast hk
    linarith
  have hcb : (0 : ℝ) ≤ j.centralBinom := by positivity
  nlinarith

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma c_symm : ∀ (t : ℕ) (u : ℤ), c t (-u) = c t u
  | 0, u => by simp [c]
  | t + 1, u => by
    simp only [c]
    rw [show -u - 1 = -(u + 1) by ring, show -u + 1 = -(u - 1) by ring, c_symm t, c_symm t]
    ring

lemma c_even_ge (j : ℕ) (hj : 1 ≤ j) (u : ℤ) (hu : Even u) (hu2 : u ^ 2 ≤ j) :
    (j.centralBinom : ℝ) / 2 ≤ (c (2 * j) u : ℝ) := by
  obtain ⟨k, rfl⟩ := hu
  have key : ∀ k' : ℕ, (k' : ℤ) = |k| → (j.centralBinom : ℝ) / 2 ≤ (c (2 * j) (k + k) : ℝ) := by
    intro k' hk'
    have hk2 : 4 * k' ^ 2 ≤ j := by
      have : ((4 * k' ^ 2 : ℕ) : ℤ) ≤ j := by
        push_cast; rw [hk']
        have : |k| ^ 2 = k ^ 2 := sq_abs k
        nlinarith
      exact_mod_cast this
    have hkj : k' ≤ j := by nlinarith
    have e : c (2 * j) (k + k) = c (2 * j) (2 * ((j + k' : ℕ) : ℤ) - ((2 * j : ℕ) : ℤ)) := by
      rcases le_or_gt 0 k with h | h
      · rw [abs_of_nonneg h] at hk'; congr 1; push_cast; rw [hk']; ring
      · rw [abs_of_neg h] at hk'
        rw [← c_symm]; congr 1; push_cast; rw [hk']; ring
    rw [e, c_choose]
    exact choose_half j k' hj hk2
  exact key k.natAbs (by simp)

/-- the probability of being at `x` at a given time, as a real number -/
noncomputable def v (X : ℕ → Ω → ℤ × ℤ) (x : ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = x}).toReal

lemma prob_even_ge (hX : IsSimpleRandomWalkSteps X) (a b : ℤ) (j : ℕ) (hj : 1 ≤ j)
    (hpar : Even (a + b)) (hu : (a + b) ^ 2 ≤ j) (hv : (a - b) ^ 2 ≤ j) :
    1 / (4 * π * ((j : ℝ) + 1)) ≤ v X (a, b) (2 * j) := by
  have h := prob_pos_ge hX (2 * j) a b
  have h' : ((c (2 * j) (a + b) * c (2 * j) (a - b) : ℕ) : ℝ≥0∞).toReal ≤
      (ℙ {ω | pos (path X ω) (2 * j) = (a, b)} * 4 ^ (2 * j)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, pow_mul] at h'
  norm_num at h'
  have hpar2 : Even (a - b) := by
    have : a - b = (a + b) - 2 * b := by ring
    rw [this]; exact hpar.sub (even_two_mul b)
  have h1 := c_even_ge j hj (a + b) hpar hu
  have h2 := c_even_ge j hj (a - b) hpar2 hv
  have hcb0 : (0 : ℝ) ≤ (j.centralBinom : ℝ) / 2 := by positivity
  have hprod : ((j.centralBinom : ℝ) / 2) * ((j.centralBinom : ℝ) / 2) ≤
      (c (2 * j) (a + b) : ℝ) * (c (2 * j) (a - b) : ℝ) := mul_le_mul h1 h2 hcb0 (by positivity)
  have hw := cb_sq_ge j
  have hpi := Real.pi_pos
  have h16 : (0 : ℝ) < 16 ^ j := by positivity
  unfold v
  set P := (ℙ {ω | pos (path X ω) (2 * j) = (a, b)}).toReal
  have : (j.centralBinom : ℝ) ^ 2 / 16 ^ j ≤ 4 * P := by
    rw [div_le_iff₀ h16]; nlinarith
  have e : 1 / (4 * π * ((j : ℝ) + 1)) = (1 / (π * ((j : ℝ) + 1))) / 4 := by
    rw [div_div, show π * ((j : ℝ) + 1) * 4 = 4 * π * ((j : ℝ) + 1) by ring]
  rw [e]
  linarith

lemma prob_succ_ge (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ) (he : e ∈ steps) :
    v X (x - e) t / 4 ≤ v X x (t + 1) := by
  have hsub : {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} ⊆
      {ω | pos (path X ω) (t + 1) = x} := by
    rintro ω ⟨h1, h2⟩
    simp only [Set.mem_setOf_eq] at h1 h2 ⊢
    rw [pos_succ, h1, show path X ω t = e from h2]; abel
  have hm := measure_mono (μ := ℙ) hsub
  rw [prob_pos_step hX t x e he] at hm
  have hm' := ENNReal.toReal_mono (measure_ne_top _ _) hm
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at hm'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at hm'
  unfold v
  rw [div_eq_mul_inv]
  exact hm'

/-- the pair of times `2j, 2j+1` carries probability at least `1/(16 π (j+1))` at `x` -/
lemma pair_ge (hX : IsSimpleRandomWalkSteps X) (a b : ℤ) (j : ℕ)
    (hj : ((|a| + |b| + 1) ^ 2 : ℤ) ≤ j) :
    1 / (16 * π * ((j : ℝ) + 1)) ≤ v X (a, b) (2 * j) + v X (a, b) (2 * j + 1) := by
  have hpi := Real.pi_pos
  have hj1 : 1 ≤ j := by
    have : (1 : ℤ) ≤ j := le_trans (by nlinarith [abs_nonneg a, abs_nonneg b]) hj
    exact_mod_cast this
  have hv0 : ∀ y t, 0 ≤ v X y t := fun _ _ ↦ ENNReal.toReal_nonneg
  have hA : (a + b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 ∧ (a - b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 ∧
      (a - 1 + b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 ∧ (a - 1 - b) ^ 2 ≤ (|a| + |b| + 1) ^ 2 := by
    have h1 := abs_nonneg a
    have h2 := abs_nonneg b
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← sq_abs] <;> apply pow_le_pow_left₀ (abs_nonneg _) <;>
      [have := abs_add_le a b; have := abs_sub a b; have := abs_add_le (a - 1) b;
       have := abs_sub (a - 1) b] <;> have := abs_sub a 1 <;> simp at * <;> linarith
  rcases Int.even_or_odd (a + b) with hpar | hpar
  · have := prob_even_ge hX a b j hj1 hpar (hA.1.trans hj) (hA.2.1.trans hj)
    have h4 : 1 / (16 * π * ((j : ℝ) + 1)) ≤ 1 / (4 * π * ((j : ℝ) + 1)) := by
      gcongr; norm_num
    linarith [hv0 (a, b) (2 * j + 1)]
  · have hpar' : Even (a - 1 + b) := by
      have : a - 1 + b = (a + b) - 1 := by ring
      rw [this]; exact hpar.sub_odd odd_one
    have h1 := prob_even_ge hX (a - 1) b j hj1 hpar' (hA.2.2.1.trans hj) (hA.2.2.2.trans hj)
    have h2 := prob_succ_ge hX (2 * j) (a, b) (1, 0) (by simp [steps])
    have e : ((a, b) : ℤ × ℤ) - (1, 0) = (a - 1, b) := by simp
    rw [e] at h2
    have h3 : 1 / (16 * π * ((j : ℝ) + 1)) = 1 / (4 * π * ((j : ℝ) + 1)) / 4 := by
      rw [div_div, show 4 * π * ((j : ℝ) + 1) * 4 = 16 * π * ((j : ℝ) + 1) by ring]
    linarith [hv0 (a, b) (2 * j)]

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

def FH (x : ℤ × ℤ) (t : ℕ) : Set (ℕ → ℤ × ℤ) := {y | pos y t = x ∧ ∀ s < t, pos y s ≠ x}

def Hit (x : ℤ × ℤ) (n : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∃ t ≤ n, pos y t = x}

/-- hit `x` within `n` steps before returning to the origin -/
def A (x : ℤ × ℤ) (n : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {y | ∃ τ ≤ n, pos y τ = x ∧ ∀ s, 1 ≤ s → s ≤ τ → pos y s ≠ 0}

lemma det_FH (x : ℤ × ℤ) (t : ℕ) : Det t (FH x t) := fun y y' h hy ↦
  ⟨by rw [← pos_congr h le_rfl]; exact hy.1, fun s hs ↦ by rw [← pos_congr h hs.le]; exact hy.2 s hs⟩

lemma det_hit (x : ℤ × ℤ) (n : ℕ) : Det n (Hit x n) := fun y y' h ⟨t, ht, hy⟩ ↦
  ⟨t, ht, by rw [← pos_congr h ht]; exact hy⟩

lemma det_A (x : ℤ × ℤ) (n : ℕ) : Det n (A x n) := fun y y' h ⟨τ, hτ, h1, h2⟩ ↦
  ⟨τ, hτ, by rw [← pos_congr h hτ]; exact h1,
    fun s hs1 hs2 ↦ by rw [← pos_congr h (hs2.trans hτ)]; exact h2 s hs1 hs2⟩

lemma A_mono (x : ℤ × ℤ) {m n : ℕ} (h : m ≤ n) : A x m ⊆ A x n :=
  fun _ ⟨τ, hτ, h1, h2⟩ ↦ ⟨τ, hτ.trans h, h1, h2⟩

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

/-- expected number of visits to `x` up to time `n`, and the Green function -/
noncomputable def EN (X : ℕ → Ω → ℤ × ℤ) (x : ℤ × ℤ) (n : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range (n + 1), ℙ {ω | pos (path X ω) t = x}

lemma first_visit (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (n : ℕ) :
    EN X x n ≤ ℙ {ω | path X ω ∈ Hit x n} * EN X 0 n := by
  have hpt : ∀ t, ℙ {ω | pos (path X ω) t = x} ≤ ∑ τ ∈ Finset.range (t + 1),
      ℙ {ω | path X ω ∈ FH x τ} * ℙ {ω | pos (path X ω) (t - τ) = 0} := by
    intro t
    calc ℙ {ω | pos (path X ω) t = x}
        ≤ ℙ (⋃ τ ∈ Finset.range (t + 1),
            {ω | path X ω ∈ FH x τ ∧ sh τ (path X ω) ∈ {y | pos y (t - τ) = 0}}) := by
          refine measure_mono fun ω hω ↦ ?_
          simp only [Set.mem_setOf_eq] at hω
          classical
          have hex : ∃ s, s ≤ t ∧ pos (path X ω) s = x := ⟨t, le_rfl, hω⟩
          set τ := Nat.find hex
          have hτ := Nat.find_spec hex
          refine Set.mem_iUnion₂.mpr ⟨τ, Finset.mem_range.mpr (by omega), ⟨hτ.2, fun s hs h ↦ ?_⟩, ?_⟩
          · exact Nat.find_min hex hs ⟨by omega, h⟩
          · simp only [Set.mem_setOf_eq]
            have e := pos_shift (path X ω) τ (t - τ)
            rw [show τ + (t - τ) = t by omega, hω, hτ.2] at e
            have : x + pos (sh τ (path X ω)) (t - τ) - x = 0 := by rw [← e]; abel
            simpa using this
      _ ≤ ∑ τ ∈ Finset.range (t + 1),
            ℙ {ω | path X ω ∈ FH x τ ∧ sh τ (path X ω) ∈ {y | pos y (t - τ) = 0}} :=
          measure_biUnion_finset_le _ _
      _ = _ := Finset.sum_congr rfl fun τ _ ↦ prob_block hX (det_FH x τ) (det_pos _ 0)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (n + 1))) fun τ ↦ {ω | path X ω ∈ FH x τ} := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hab with h | h
    · exact h4 a h h1
    · exact h2 b h h3
  have hFH : ∑ τ ∈ Finset.range (n + 1), ℙ {ω | path X ω ∈ FH x τ} ≤
      ℙ {ω | path X ω ∈ Hit x n} := by
    rw [← measure_biUnion_finset hdisj fun τ _ ↦ by rw [path_eq]; exact det_meas hX (det_FH x τ) 0]
    refine measure_mono fun ω hω ↦ ?_
    obtain ⟨τ, hτ, h1, -⟩ := Set.mem_iUnion₂.mp hω
    exact ⟨τ, by have := Finset.mem_range.mp hτ; omega, h1⟩
  calc EN X x n
      ≤ ∑ t ∈ Finset.range (n + 1), ∑ τ ∈ Finset.range (t + 1),
          ℙ {ω | path X ω ∈ FH x τ} * ℙ {ω | pos (path X ω) (t - τ) = 0} :=
        Finset.sum_le_sum fun t _ ↦ hpt t
    _ = ∑ τ ∈ Finset.range (n + 1), ∑ t ∈ Finset.Ico τ (n + 1),
          ℙ {ω | path X ω ∈ FH x τ} * ℙ {ω | pos (path X ω) (t - τ) = 0} := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm]
        simp only [Finset.range_eq_Ico]
    _ ≤ ∑ τ ∈ Finset.range (n + 1), ℙ {ω | path X ω ∈ FH x τ} * EN X 0 n := by
        refine Finset.sum_le_sum fun τ hτ ↦ ?_
        rw [← Finset.mul_sum]
        gcongr
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = (∑ τ ∈ Finset.range (n + 1), ℙ {ω | path X ω ∈ FH x τ}) * EN X 0 n := by
        rw [Finset.sum_mul]
    _ ≤ ℙ {ω | path X ω ∈ Hit x n} * EN X 0 n := by gcongr

lemma last_zero (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (hx : x ≠ 0) (n : ℕ) :
    ℙ {ω | path X ω ∈ Hit x n} ≤ EN X 0 n * ℙ {ω | path X ω ∈ A x n} := by
  calc ℙ {ω | path X ω ∈ Hit x n}
      ≤ ℙ (⋃ t ∈ Finset.range (n + 1),
          {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ A x (n - t)}) := by
        refine measure_mono fun ω hω ↦ ?_
        obtain ⟨t0, ht0, hx0⟩ := hω
        classical
        have hex : ∃ s, s ≤ n ∧ pos (path X ω) s = x := ⟨t0, ht0, hx0⟩
        set τ := Nat.find hex
        have hτ := Nat.find_spec hex
        set Z := (Finset.range (τ + 1)).filter fun s ↦ pos (path X ω) s = 0
        have hZ0 : 0 ∈ Z := Finset.mem_filter.mpr ⟨by simp, pos_zero _⟩
        set t := Z.max' ⟨0, hZ0⟩
        have htZ := Finset.mem_filter.mp (Finset.max'_mem Z ⟨0, hZ0⟩)
        have htτ : t ≤ τ := by have := Finset.mem_range.mp htZ.1; omega
        have htne : t ≠ τ := by
          intro h
          have h0 : pos (path X ω) τ = 0 := h ▸ htZ.2
          exact hx (hτ.2.symm.trans h0)
        refine Set.mem_iUnion₂.mpr ⟨t, Finset.mem_range.mpr (by omega), htZ.2,
          τ - t, by omega, ?_, fun s hs1 hs2 hs ↦ ?_⟩
        · rw [pos_sh _ htZ.2, show t + (τ - t) = τ by omega]; exact hτ.2
        · rw [pos_sh _ htZ.2] at hs
          have : t + s ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩
          have := Finset.le_max' Z (t + s) this
          omega
    _ ≤ ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | path X ω ∈ {y | pos y t = 0} ∧ sh t (path X ω) ∈ A x (n - t)} :=
        measure_biUnion_finset_le _ _
    _ = ∑ t ∈ Finset.range (n + 1),
          ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ A x (n - t)} :=
        Finset.sum_congr rfl fun t _ ↦ prob_block hX (det_pos t 0) (det_A x _)
    _ ≤ ∑ t ∈ Finset.range (n + 1), ℙ {ω | pos (path X ω) t = 0} * ℙ {ω | path X ω ∈ A x n} := by
        gcongr with t ht
        exact fun ω hω ↦ A_mono x (Nat.sub_le n t) hω
    _ = EN X 0 n * ℙ {ω | path X ω ∈ A x n} := by rw [EN, Finset.sum_mul]

/-- hitting before returning: `EN_x ≤ G² P(A)` -/
lemma hit_before_return (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (hx : x ≠ 0) (n : ℕ) :
    EN X x n ≤ EN X 0 n ^ 2 * ℙ {ω | path X ω ∈ A x n} := by
  calc EN X x n ≤ ℙ {ω | path X ω ∈ Hit x n} * EN X 0 n := first_visit hX x n
    _ ≤ EN X 0 n * ℙ {ω | path X ω ∈ A x n} * EN X 0 n := by gcongr; exact last_zero hX x hx n
    _ = EN X 0 n ^ 2 * ℙ {ω | path X ω ∈ A x n} := by ring

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

def Avoid (x : ℤ × ℤ) (n : ℕ) : Set (ℕ → ℤ × ℤ) := {y | ∀ t ≤ n, pos y t ≠ x}

def RB (x : ℤ × ℤ) (t : ℕ) : Set (ℕ → ℤ × ℤ) := FR t ∩ Avoid x t

lemma det_avoid (x : ℤ × ℤ) (n : ℕ) : Det n (Avoid x n) := fun y y' h hy t ht ↦ by
  rw [← pos_congr h ht]; exact hy t ht

lemma det_RB (x : ℤ × ℤ) (t : ℕ) : Det t (RB x t) := fun y y' h hy ↦
  ⟨det_FR t y y' h hy.1, det_avoid x t y y' h hy.2⟩

lemma det_inter {m : ℕ} {A B : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (hB : Det m B) : Det m (A ∩ B) :=
  fun y y' h hy ↦ ⟨hA y y' h hy.1, hB y y' h hy.2⟩

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma rb_sum_le (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (n m : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} ≤ 1 - ℙ {ω | path X ω ∈ A x m} := by
  have hmA : MeasurableSet {ω | path X ω ∈ A x m} := by rw [path_eq]; exact det_meas hX (det_A x m) 0
  have hmR : ∀ t, MeasurableSet {ω | path X ω ∈ RB x t} := fun t ↦ by
    rw [path_eq]; exact det_meas hX (det_RB x t) 0
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n)) fun t ↦ {ω | path X ω ∈ RB x t} := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    simp only [Set.mem_setOf_eq, FR] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · exact h2.2 a (Finset.mem_Icc.mp ha).1 h h1.1
    · exact h1.2 b (Finset.mem_Icc.mp hb).1 h h2.1
  have hd2 : Disjoint (⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ RB x t}) {ω | path X ω ∈ A x m} := by
    rw [Set.disjoint_left]
    intro ω hω hA
    obtain ⟨t, ht, ⟨h1, h2⟩⟩ := Set.mem_iUnion₂.mp hω
    obtain ⟨τ, -, h3, h4⟩ := hA
    rcases le_or_gt τ t with h | h
    · exact h2 τ h h3
    · exact h4 t (Finset.mem_Icc.mp ht).1 h.le h1.1
  have hsum : ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} + ℙ {ω | path X ω ∈ A x m} ≤ 1 := by
    rw [← measure_biUnion_finset hdisj fun t _ ↦ hmR t, ← measure_union hd2 hmA]
    exact prob_le_one
  exact ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) hsum

/-- many returns to the origin and still no visit to `x` -/
lemma avoid_renewal (hX : IsSimpleRandomWalkSteps X) (x : ℤ × ℤ) (m : ℕ) :
    ∀ k n, ℙ {ω | path X ω ∈ Vis n (k + 1) ∩ Avoid x n} ≤ (1 - ℙ {ω | path X ω ∈ A x m}) ^ k
  | 0, n => by rw [pow_zero]; exact prob_le_one
  | k + 1, n => by
    set ρ := 1 - ℙ {ω | path X ω ∈ A x m}
    calc ℙ {ω | path X ω ∈ Vis n (k + 1 + 1) ∩ Avoid x n}
        ≤ ℙ (⋃ t ∈ Finset.Icc 1 n, {ω | path X ω ∈ RB x t ∧
            sh t (path X ω) ∈ Vis (n - t) (k + 1) ∩ Avoid x (n - t)}) := by
          refine measure_mono fun ω hω ↦ ?_
          obtain ⟨hv, hav⟩ := hω
          obtain ⟨t, ht, hFR, hsh⟩ := renewal_subset n (k + 1) (by omega) hv
          have ht' := Finset.mem_Icc.mp ht
          refine Set.mem_iUnion₂.mpr ⟨t, ht, ⟨hFR, fun s hs ↦ hav s (by omega)⟩, hsh, ?_⟩
          intro s hs
          rw [pos_sh _ hFR.1]
          exact hav (t + s) (by omega)
      _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t ∧
            sh t (path X ω) ∈ Vis (n - t) (k + 1) ∩ Avoid x (n - t)} :=
          measure_biUnion_finset_le _ _
      _ = ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} *
            ℙ {ω | path X ω ∈ Vis (n - t) (k + 1) ∩ Avoid x (n - t)} :=
          Finset.sum_congr rfl fun t _ ↦
            prob_block hX (det_RB x t) (det_inter (det_vis _ _) (det_avoid x _))
      _ ≤ ∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t} * ρ ^ k := by
          gcongr with t ht
          exact avoid_renewal hX x m k (n - t)
      _ = (∑ t ∈ Finset.Icc 1 n, ℙ {ω | path X ω ∈ RB x t}) * ρ ^ k := by rw [Finset.sum_mul]
      _ ≤ ρ * ρ ^ k := by gcongr; exact rb_sum_le hX x n m
      _ = ρ ^ (k + 1) := (pow_succ' _ _).symm

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real Erdos1164

lemma covers_bdd {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) :
    BddAbove {r : ℕ | Covers X n ω (closedDisc r)} := by
  refine ⟨n, fun r hr ↦ ?_⟩
  simp only [Set.mem_setOf_eq] at hr
  classical
  have hmem : ∀ j : ℕ, j ≤ r → ((j : ℤ), (0 : ℤ)) ∈ closedDisc r := by
    intro j hj
    simp only [closedDisc, Set.mem_setOf_eq]
    have : (j : ℤ) ≤ r := by exact_mod_cast hj
    nlinarith
  have hk : ∀ j : ℕ, ∃ k, j ≤ r → k ≤ n ∧ position X k ω = ((j : ℤ), (0 : ℤ)) := by
    intro j
    by_cases hj : j ≤ r
    · obtain ⟨k, hk, hpos⟩ := hr _ (hmem j hj)
      exact ⟨k, fun _ ↦ ⟨hk, hpos⟩⟩
    · exact ⟨0, fun h ↦ absurd h hj⟩
  choose f hf using hk
  have hcard : (Finset.range (r + 1)).card ≤ (Finset.range (n + 1)).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro j hj
      have hj' : j ≤ r := by have := Finset.mem_range.mp hj; omega
      exact Finset.mem_range.mpr (by have := (hf j hj').1; omega)
    · intro a ha b hb hab
      have ha' : a ≤ r := by have := Finset.mem_range.mp ha; omega
      have hb' : b ≤ r := by have := Finset.mem_range.mp hb; omega
      have h1 := (hf a ha').2
      have h2 := (hf b hb').2
      have hab' : f a = f b := hab
      rw [hab', h2] at h1
      have := congrArg Prod.fst h1
      simp only at this
      exact_mod_cast this.symm
  simp only [Finset.card_range] at hcard
  omega

lemma le_coveringRadius {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) (r : ℕ)
    (h : Covers X n ω (closedDisc r)) : r ≤ coveringRadius X n ω :=
  le_csSup (covers_bdd X n ω) h

/-- the box containing the closed disc -/
def box (r : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(r : ℤ)) r ×ˢ Finset.Icc (-(r : ℤ)) r

lemma disc_sub_box (r : ℕ) (x : ℤ × ℤ) (hx : x ∈ closedDisc r) : x ∈ box r := by
  simp only [closedDisc, Set.mem_setOf_eq] at hx
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  have hr : (0 : ℤ) ≤ r := by positivity
  have h1 : x.1 ^ 2 ≤ (r : ℤ) ^ 2 := by nlinarith [sq_nonneg x.2]
  have h2 : x.2 ^ 2 ≤ (r : ℤ) ^ 2 := by nlinarith [sq_nonneg x.1]
  have a1 := abs_le_of_sq_le_sq' h1 hr
  have a2 := abs_le_of_sq_le_sq' h2 hr
  exact ⟨a1, a2⟩

lemma card_box (r : ℕ) : ((box r).card : ℝ) = (2 * r + 1) ^ 2 := by
  simp only [box, Finset.card_product, Int.card_Icc]
  have : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
  rw [this]; push_cast; ring

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma not_cover_le (n r K : ℕ) :
    ℙ {ω | ¬ Covers X n ω (closedDisc r)} ≤ ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} +
      ∑ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} := by
  calc ℙ {ω | ¬ Covers X n ω (closedDisc r)}
      ≤ ℙ ({ω | path X ω ∈ (Vis n (K + 1))ᶜ} ∪
          ⋃ x ∈ (box r).erase 0, {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n}) := by
        refine measure_mono fun ω hω ↦ ?_
        simp only [Set.mem_setOf_eq, Covers, not_forall] at hω
        obtain ⟨x, hx, hnot⟩ := hω
        by_cases hv : path X ω ∈ Vis n (K + 1)
        · right
          have hx0 : x ≠ 0 := by
            rintro rfl
            exact hnot ⟨0, Nat.zero_le _, by simp [position]⟩
          refine Set.mem_iUnion₂.mpr ⟨x, Finset.mem_erase.mpr ⟨hx0, disc_sub_box r x hx⟩, hv, ?_⟩
          intro t ht h
          exact hnot ⟨t, ht, h⟩
        · left; exact hv
    _ ≤ ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} +
          ℙ (⋃ x ∈ (box r).erase 0, {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n}) :=
        measure_union_le _ _
    _ ≤ _ := by gcongr; exact measure_biUnion_finset_le _ _

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real

lemma sum_pairs2 (f : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ Finset.range (2 * M), f t = ∑ j ∈ Finset.range M, (f (2 * j) + f (2 * j + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

lemma harm_Ico (J M : ℕ) (h : J ≤ M + 1) :
    Real.log (M + 2) - (1 + Real.log J) ≤ ∑ j ∈ Finset.Ico J (M + 1), 1 / ((j : ℝ) + 1) := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) h
  have hH : ∀ n : ℕ, (harmonic n : ℝ) = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
    intro n
    rw [harmonic, Rat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast; rw [one_div]
  have h1 := log_add_one_le_harmonic (M + 1)
  have h2 := harmonic_le_one_add_log J
  rw [hH] at h1 h2
  have e : Real.log (((M + 1 + 1 : ℕ) : ℝ)) = Real.log ((M : ℝ) + 2) := by push_cast; ring_nf
  rw [e] at h1
  linarith

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma EN_toReal (X : ℕ → Ω → ℤ × ℤ) (x : ℤ × ℤ) (n : ℕ) :
    (EN X x n).toReal = ∑ t ∈ Finset.range (n + 1), v X x t :=
  ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _

/-- the probability of reaching `x` before returning is at least `1/(300 log r)` -/
lemma h_lower (hX : IsSimpleRandomWalkSteps X) (r : ℕ) (hr : 4 ≤ Real.log r) (x : ℤ × ℤ)
    (hx : x ∈ box r) (hx0 : x ≠ 0) :
    1 / (300 * Real.log r) ≤ (ℙ {ω | path X ω ∈ A x (2 * r ^ 4 + 1)}).toReal := by
  set L := Real.log r with hL
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hr0 : (0 : ℝ) < r := by
    by_contra h
    have : (r : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg r)
    rw [hL, this, Real.log_zero] at hr; linarith
  have hr1 : (1 : ℝ) ≤ r := by
    have : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hr0)
    exact_mod_cast this
  obtain ⟨a, b⟩ := x
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hx
  set M := r ^ 4 with hM
  set J := (2 * r + 1) ^ 2 with hJ
  -- `r ≥ e^4 > 50`, so `J ≤ M`
  have hr54 : (50 : ℝ) ≤ r := by
    have h1 : Real.exp 4 ≤ r := by rw [← Real.exp_log hr0]; exact Real.exp_le_exp.mpr hr
    have h2 : (50 : ℝ) ≤ Real.exp 4 := by
      have h3 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have := pow_le_pow_left₀ (by norm_num) h27 4
      norm_num at this
      linarith
    linarith
  have hJM : J ≤ M + 1 := by
    have h1 : 2 * (r : ℝ) + 1 ≤ (r : ℝ) ^ 2 := by nlinarith
    have h2 : (2 * (r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have : ((J : ℕ) : ℝ) ≤ M := by
      rw [hJ, hM]; push_cast
      calc (2 * (r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) ^ 2) ^ 2 := h2
        _ = (r : ℝ) ^ 4 := by ring
    have : J ≤ M := by exact_mod_cast this
    omega
  -- lower bound on the expected visits to x
  have hEN : 3 * L / (64 * π) ≤ (EN X (a, b) (2 * r ^ 4 + 1)).toReal := by
    rw [EN_toReal, show 2 * r ^ 4 + 1 + 1 = 2 * (M + 1) by ring, sum_pairs2]
    have hv0 : ∀ y t, 0 ≤ v X y t := fun _ _ ↦ ENNReal.toReal_nonneg
    calc 3 * L / (64 * π) ≤ (Real.log (M + 2) - (1 + Real.log J)) / (16 * π) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h4 : 4 * L ≤ Real.log ((M : ℝ) + 2) := by
            have e : Real.log ((r : ℝ) ^ 4) = 4 * L := by rw [hL, Real.log_pow]; norm_num
            rw [← e]
            exact Real.log_le_log (by positivity) (by rw [hM]; push_cast; linarith)
          have h5 : Real.log (J : ℝ) ≤ 4 + 2 * L := by
            have e : Real.log (J : ℝ) = 2 * Real.log (2 * r + 1) := by
              rw [hJ]; push_cast; rw [Real.log_pow]; push_cast; ring
            have h6 : Real.log (2 * (r : ℝ) + 1) ≤ Real.log 3 + L := by
              rw [hL, ← Real.log_mul (by norm_num) hr0.ne']
              exact Real.log_le_log (by positivity) (by linarith)
            have h7 : Real.log 3 ≤ 2 := by
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
            rw [e]; linarith
          nlinarith
      _ ≤ ∑ j ∈ Finset.Ico J (M + 1), 1 / (16 * π * ((j : ℝ) + 1)) := by
          rw [show (∑ j ∈ Finset.Ico J (M + 1), 1 / (16 * π * ((j : ℝ) + 1))) =
              (∑ j ∈ Finset.Ico J (M + 1), 1 / ((j : ℝ) + 1)) / (16 * π) by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [div_div, mul_comm]]
          gcongr
          exact harm_Ico J M hJM
      _ ≤ ∑ j ∈ Finset.Ico J (M + 1), (v X (a, b) (2 * j) + v X (a, b) (2 * j + 1)) := by
          refine Finset.sum_le_sum fun j hj ↦ pair_ge hX a b j ?_
          have hj := (Finset.mem_Ico.mp hj).1
          have h1 : |a| ≤ r := abs_le.mpr hx.1
          have h2 : |b| ≤ r := abs_le.mpr hx.2
          have : ((J : ℕ) : ℤ) ≤ j := by exact_mod_cast hj
          rw [hJ] at this; push_cast at this
          nlinarith [abs_nonneg a, abs_nonneg b]
      _ ≤ ∑ j ∈ Finset.range (M + 1), (v X (a, b) (2 * j) + v X (a, b) (2 * j + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun j hj ↦ Finset.mem_range.mpr
            (Finset.mem_Ico.mp hj).2) fun j _ _ ↦ add_nonneg (hv0 _ _) (hv0 _ _)
  -- upper bound on the Green function
  have hG : (EN X 0 (2 * r ^ 4 + 1)).toReal ≤ 6 * L / π := by
    rw [EN_toReal]
    have := green_le (u X) (u_nonneg X) (u_le_one X 0) (u_pair hX) (2 * r ^ 4 + 1)
    have hlog : Real.log (((2 * r ^ 4 + 1 : ℕ) : ℝ)) ≤ 2 + 4 * L := by
      have h1 : Real.log (((2 * r ^ 4 + 1 : ℕ) : ℝ)) ≤ Real.log (3 * (r : ℝ) ^ 4) := by
        apply Real.log_le_log (by positivity)
        have : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hr1
        push_cast; linarith
      have e : Real.log ((r : ℝ) ^ 4) = 4 * L := by rw [hL, Real.log_pow]; norm_num
      rw [Real.log_mul (by norm_num) (by positivity), e] at h1
      have h7 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
      linarith
    have e : ∑ t ∈ Finset.range (2 * r ^ 4 + 1 + 1), v X 0 t =
        ∑ t ∈ Finset.range (2 * r ^ 4 + 1 + 1), u X t := rfl
    rw [e]
    refine this.trans ?_
    rw [le_div_iff₀ hpi, add_mul, div_mul_cancel₀ _ hpi.ne', one_mul]
    have := Real.pi_le_four
    linarith

  have hkey := hit_before_return hX (a, b) hx0 (2 * r ^ 4 + 1)
  have hkey' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top
    (ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _)) (measure_ne_top _ _)) hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hkey'
  set P := (ℙ {ω | path X ω ∈ A (a, b) (2 * r ^ 4 + 1)}).toReal
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ (EN X 0 (2 * r ^ 4 + 1)).toReal := ENNReal.toReal_nonneg
  have hL0 : 0 < L := by linarith
  have hEN' : 3 * L ≤ 64 * π * (EN X (a, b) (2 * r ^ 4 + 1)).toReal := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * π)).mp hEN
    linarith
  have hG' : π * (EN X 0 (2 * r ^ 4 + 1)).toReal ≤ 6 * L := by
    have := (le_div_iff₀ hpi).mp hG
    linarith
  set G := (EN X 0 (2 * r ^ 4 + 1)).toReal
  have h1 : 3 * L ≤ 64 * π * (G ^ 2 * P) := hEN'.trans (by gcongr; exact hkey')
  have h2 : (π * G) ^ 2 ≤ (6 * L) ^ 2 := pow_le_pow_left₀ (by positivity) hG' 2
  have h3 : (L * π) * (3 * π) ≤ (L * π) * (2304 * L * P) := by
    have e1 : (L * π) * (3 * π) = π ^ 2 * (3 * L) := by ring
    have e2 : (L * π) * (2304 * L * P) = 64 * π * P * (6 * L) ^ 2 := by ring
    rw [e1, e2]
    calc π ^ 2 * (3 * L) ≤ π ^ 2 * (64 * π * (G ^ 2 * P)) := by gcongr
      _ = 64 * π * P * (π * G) ^ 2 := by ring
      _ ≤ 64 * π * P * (6 * L) ^ 2 := by gcongr
  have h4 := le_of_mul_le_mul_left h3 (by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real Erdos1164 Filter

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

lemma noRet_compl (hX : IsSimpleRandomWalkSteps X) (s : ℕ) :
    ℙ {ω | path X ω ∈ NoRet s}ᶜ = ENNReal.ofReal (1 - q X s) := by
  have hmN : MeasurableSet {ω | path X ω ∈ NoRet s} := by
    rw [path_eq]; exact det_meas hX (det_noRet s) 0
  rw [prob_compl_eq_one_sub hmN]
  unfold q
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- few returns to the origin is unlikely -/
lemma few_returns (hX : IsSimpleRandomWalkSteps X) (n K M : ℕ) (hKM : K * (2 * M) ≤ n) :
    ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} ≤ ENNReal.ofReal (K * q X (2 * M)) := by
  have hmV : MeasurableSet {ω | path X ω ∈ Vis n (K + 1)} := by
    rw [path_eq]; exact det_meas hX (det_vis _ _) 0
  have h1 : ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} = 1 - ℙ {ω | path X ω ∈ Vis n (K + 1)} :=
    prob_compl_eq_one_sub hmV
  have h2 : ENNReal.ofReal ((1 - q X (2 * M)) ^ K) ≤ ℙ {ω | path X ω ∈ Vis n (K + 1)} := by
    have hq1 := q_le_one (X := X) (2 * M)
    rw [ENNReal.ofReal_pow (by linarith), ← noRet_compl hX]
    refine (renewal_lower hX (2 * M) K).trans (measure_mono fun ω hω ↦ ?_)
    simp only [Set.mem_setOf_eq, Vis] at hω ⊢
    exact hω.trans (visits_mono _ (by rw [mul_comm] at hKM; linarith))
  rw [h1]
  have hq0 := q_nonneg (X := X) (2 * M)
  have hq1 := q_le_one (X := X) (2 * M)
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -q X (2 * M) by linarith) K
  calc 1 - ℙ {ω | path X ω ∈ Vis n (K + 1)} ≤ 1 - ENNReal.ofReal ((1 - q X (2 * M)) ^ K) :=
        tsub_le_tsub_left h2 _
    _ = ENNReal.ofReal (1 - (1 - q X (2 * M)) ^ K) := by
        rw [ENNReal.ofReal_sub _ (pow_nonneg (by linarith) K), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (K * q X (2 * M)) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (1 + -q X (2 * M)) = 1 - q X (2 * M) := by ring
        rw [e] at hb
        linarith

/-- a point of the box is missed despite many returns -/
lemma miss_point (hX : IsSimpleRandomWalkSteps X) (n K r : ℕ) (hr : 4 ≤ Real.log r)
    (x : ℤ × ℤ) (hx : x ∈ box r) (hx0 : x ≠ 0) :
    ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} ≤
      ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r)))) := by
  have hA := h_lower hX r hr x hx hx0
  refine (avoid_renewal hX x (2 * r ^ 4 + 1) K n).trans ?_
  set P := ℙ {ω | path X ω ∈ A x (2 * r ^ 4 + 1)}
  have hP1 : P.toReal ≤ 1 := by
    have : P ≤ 1 := prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (this.trans_eq ENNReal.ofReal_one.symm)
  have e : 1 - P = ENNReal.ofReal (1 - P.toReal) := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [e, ← ENNReal.ofReal_pow (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  calc (1 - P.toReal) ^ K ≤ Real.exp (-P.toReal) ^ K :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) K
    _ = Real.exp (-(K * P.toReal)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-(K / (300 * Real.log r))) := by
        apply Real.exp_le_exp.mpr
        have : (K : ℝ) / (300 * Real.log r) ≤ K * P.toReal := by
          rw [div_eq_mul_one_div]; gcongr
        linarith

end OMA.C64

namespace OMA.C64
open OMA.H1Proof OMA.H3Proof Real Erdos1164 Filter

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

/-- the lower half for one `n`, with explicit conditions -/
lemma lower_fixed (hX : IsSimpleRandomWalkSteps X) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ)
    (hn8 : 64 ≤ n) (hℓ1 : 16 * π / ε ≤ Real.log n)
    (hℓ2 : 4 ≤ ε / (16 * π) / 3000 * √(Real.log n))
    (hℓ3 : Real.log (100 / ε) ≤ 4 * √(Real.log n)) :
    1 - ε ≤ (ℙ {ω | ε / (16 * π) / 3000 * √(Real.log n) ≤
      Real.log (coveringRadius X n ω)}).toReal := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set δ := ε / (16 * π) with hδ
  set c := δ / 3000 with hc
  set ℓ := Real.log n with hℓ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 16 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hn0 : (0 : ℝ) < n := by
    have : (64 : ℝ) ≤ n := by exact_mod_cast hn8
    linarith
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hsq8 : (8 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; norm_num; exact_mod_cast hn8
  have hℓ0 : 0 < ℓ := by
    have : 0 < 16 * π / ε := by positivity
    linarith
  set K := ⌈δ * ℓ⌉₊ with hK
  set M := ⌊√(n : ℝ)⌋₊ with hM
  set E := Real.exp (c * √ℓ) with hE
  set r := ⌈E⌉₊ with hr
  -- the radius
  have hE4 : Real.exp 4 ≤ E := Real.exp_le_exp.mpr hℓ2
  have hE1 : 1 ≤ E := le_trans (Real.one_le_exp (by norm_num)) hE4
  have hrE : E ≤ r := Nat.le_ceil E
  have hrE2 : (r : ℝ) ≤ 2 * E := by
    have := Nat.ceil_lt_add_one (show 0 ≤ E by linarith); linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr1 : c * √ℓ ≤ Real.log r := by
    rw [← Real.log_exp (c * √ℓ)]; exact Real.log_le_log (Real.exp_pos _) hrE
  have hlogr2 : Real.log r ≤ 2 * (c * √ℓ) := by
    have h1 : Real.log r ≤ Real.log (2 * E) := Real.log_le_log hr0 hrE2
    rw [Real.log_mul (by norm_num) (by positivity), hE, Real.log_exp] at h1
    have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hlogr4 : 4 ≤ Real.log r := hℓ2.trans hlogr1
  -- the returns
  have hKℓ : δ * ℓ ≤ K := Nat.le_ceil _
  have hKℓ2 : (K : ℝ) ≤ δ * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hMle : (M : ℝ) ≤ √(n : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hMge : √(n : ℝ) < M + 1 := Nat.lt_floor_add_one _
  have hlogsq : ℓ ≤ 2 * √(n : ℝ) := by
    have h1 : Real.log √(n : ℝ) = ℓ / 2 := Real.log_sqrt hn0.le
    have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn0)
    linarith
  have h2K : 2 * (K : ℝ) ≤ √(n : ℝ) := by nlinarith
  have hKM : K * (2 * M) ≤ n := by
    have : ((K * (2 * M) : ℕ) : ℝ) ≤ n := by
      push_cast
      calc (K : ℝ) * (2 * M) = (2 * K) * M := by ring
        _ ≤ √(n : ℝ) * √(n : ℝ) := by gcongr
        _ = n := by rw [← sq, hsq]
    exact_mod_cast this
  have hq : q X (2 * M) * ℓ ≤ 2 * π := by
    have h1 := q_le hX M
    have h2 : ℓ / 2 ≤ Real.log ((M : ℝ) + 1) := by
      rw [← Real.log_sqrt hn0.le]; exact Real.log_le_log (Real.sqrt_pos.mpr hn0) hMge.le
    have := mul_le_mul_of_nonneg_left h2 (q_nonneg (X := X) (2 * M))
    linarith
  have hKq : (K : ℝ) * q X (2 * M) ≤ ε / 4 := by
    have hq0 := q_nonneg (X := X) (2 * M)
    have h1 : q X (2 * M) ≤ ε / 8 := by
      have : q X (2 * M) * ℓ ≤ ε / 8 * ℓ := by
        have : 16 * π ≤ ε * ℓ := by rw [div_le_iff₀ hε] at hℓ1; linarith
        nlinarith
      exact le_of_mul_le_mul_right this hℓ0
    have h2 : δ * ℓ * q X (2 * M) ≤ ε / 8 := by
      have : δ * ℓ * q X (2 * M) = δ * (q X (2 * M) * ℓ) := by ring
      rw [this]
      calc δ * (q X (2 * M) * ℓ) ≤ δ * (2 * π) := by gcongr
        _ = ε / 8 := by
          rw [hδ, show ε / (16 * π) * (2 * π) = ε * (π / π) / 8 by ring, div_self hpi.ne', mul_one]
    calc (K : ℝ) * q X (2 * M) ≤ (δ * ℓ + 1) * q X (2 * M) := by gcongr
      _ = δ * ℓ * q X (2 * M) + q X (2 * M) := by ring
      _ ≤ ε / 4 := by linarith
  have hfew := few_returns hX n K M hKM
  -- the misses
  have hmiss : ∑ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} ≤
      ENNReal.ofReal (ε / 4) := by
    have hterm : ∀ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n} ≤
        ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r)))) := fun x hx ↦
      miss_point hX n K r hlogr4 x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((box r).erase 0).card : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * r + 1) ^ 2) := by
      rw [← card_box, ENNReal.ofReal_natCast]
      exact_mod_cast Finset.card_erase_le
    calc (((box r).erase 0).card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r))))
        ≤ ENNReal.ofReal ((2 * r + 1) ^ 2) *
            ENNReal.ofReal (Real.exp (-(K / (300 * Real.log r)))) := by gcongr
      _ = ENNReal.ofReal ((2 * r + 1) ^ 2 * Real.exp (-(K / (300 * Real.log r)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (ε / 4) := by
          apply ENNReal.ofReal_le_ofReal
          have hsqℓ : 0 < √ℓ := Real.sqrt_pos.mpr hℓ0
          have hℓsq : √ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
          have hexp : (K : ℝ) / (300 * Real.log r) ≥ 5 * √ℓ := by
            rw [ge_iff_le, le_div_iff₀ (by positivity)]
            calc 5 * √ℓ * (300 * Real.log r) ≤ 5 * √ℓ * (300 * (2 * (c * √ℓ))) := by gcongr
              _ = δ * √ℓ ^ 2 := by rw [hc]; ring
              _ = δ * ℓ := by rw [hℓsq]
              _ ≤ K := hKℓ
          have h1 : (2 * (r : ℝ) + 1) ^ 2 ≤ 25 * E ^ 2 := by nlinarith
          have h2 : E ^ 2 = Real.exp (2 * (c * √ℓ)) := by rw [hE, ← Real.exp_nat_mul]; norm_num
          have hc1 : c ≤ 1 / 2 := by rw [hc]; linarith
          have h3 : Real.exp (2 * (c * √ℓ)) * Real.exp (-(K / (300 * Real.log r))) ≤
              Real.exp (-(4 * √ℓ)) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
            have : c * √ℓ ≤ 1 / 2 * √ℓ := by gcongr
            linarith
          have h4 : 25 * Real.exp (-(4 * √ℓ)) ≤ ε / 4 := by
            have : Real.exp (Real.log (100 / ε)) ≤ Real.exp (4 * √ℓ) := Real.exp_le_exp.mpr hℓ3
            rw [Real.exp_log (by positivity)] at this
            rw [Real.exp_neg]
            have hpos : 0 < Real.exp (4 * √ℓ) := Real.exp_pos _
            rw [← div_eq_mul_inv, div_le_iff₀ hpos]
            have h6 : 100 / ε * ε = 100 := div_mul_cancel₀ _ hε.ne'
            have h5 : ε / 4 * (100 / ε) = 25 := by
              rw [show ε / 4 * (100 / ε) = (100 / ε * ε) / 4 by ring, h6]; norm_num
            calc (25 : ℝ) = ε / 4 * (100 / ε) := h5.symm
              _ ≤ ε / 4 * Real.exp (4 * √ℓ) := by gcongr
          calc (2 * (r : ℝ) + 1) ^ 2 * Real.exp (-(K / (300 * Real.log r)))
              ≤ 25 * E ^ 2 * Real.exp (-(K / (300 * Real.log r))) := by gcongr
            _ = 25 * (Real.exp (2 * (c * √ℓ)) * Real.exp (-(K / (300 * Real.log r)))) := by
                rw [h2]; ring
            _ ≤ 25 * Real.exp (-(4 * √ℓ)) := by gcongr
            _ ≤ ε / 4 := h4
  -- combine
  have hnc := not_cover_le (X := X) n r K
  have hbad : ℙ {ω | ¬ Covers X n ω (closedDisc r)} ≤ ENNReal.ofReal ε := by
    refine hnc.trans ?_
    calc ℙ {ω | path X ω ∈ (Vis n (K + 1))ᶜ} +
          ∑ x ∈ (box r).erase 0, ℙ {ω | path X ω ∈ Vis n (K + 1) ∩ Avoid x n}
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
          gcongr
          exact hfew.trans (ENNReal.ofReal_le_ofReal hKq)
      _ = ENNReal.ofReal (ε / 4 + ε / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  set S := {ω | c * √ℓ ≤ Real.log (coveringRadius X n ω)}
  have hSc : Sᶜ ⊆ {ω | ¬ Covers X n ω (closedDisc r)} := by
    intro ω hω hcov
    apply hω
    have h1 := le_coveringRadius X n ω r hcov
    have h2 : (r : ℝ) ≤ coveringRadius X n ω := by exact_mod_cast h1
    exact hlogr1.trans (Real.log_le_log hr0 h2)
  have h1 : (1 : ℝ≥0∞) ≤ ℙ S + ENNReal.ofReal ε := by
    calc (1 : ℝ≥0∞) = ℙ (S ∪ Sᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ ℙ S + ℙ Sᶜ := measure_union_le _ _
      _ ≤ ℙ S + ENNReal.ofReal ε := by gcongr; exact (measure_mono hSc).trans hbad
  have h2 : ENNReal.ofReal (1 - ε) ≤ ℙ S := by
    rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
    exact tsub_le_iff_right.mpr h1
  have h3 := ENNReal.toReal_mono (measure_ne_top _ _) h2
  rwa [ENNReal.toReal_ofReal (by linarith)] at h3

theorem lower : ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X → ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop, 1 - ε ≤
        (ℙ {ω | c * √(Real.log n) ≤ Real.log (coveringRadius X n ω)}).toReal := by
  intro Ω _ _ X hX ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hpi := Real.pi_pos
  refine ⟨ε' / (16 * π) / 3000, by positivity, ?_⟩
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  set T := max (16 * π / ε') (max ((4 / (ε' / (16 * π) / 3000)) ^ 2) ((Real.log (100 / ε') / 4) ^ 2))
  filter_upwards [eventually_ge_atTop 64, hlog.eventually_ge_atTop T] with n hn hT
  have hT1 : 16 * π / ε' ≤ Real.log n := le_trans (le_max_left _ _) hT
  have hT2 : (4 / (ε' / (16 * π) / 3000)) ^ 2 ≤ Real.log n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT3 : (Real.log (100 / ε') / 4) ^ 2 ≤ Real.log n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hc0 : 0 < ε' / (16 * π) / 3000 := by positivity
  have h2 : 4 ≤ ε' / (16 * π) / 3000 * √(Real.log n) := by
    have : 4 / (ε' / (16 * π) / 3000) ≤ √(Real.log n) := Real.le_sqrt_of_sq_le hT2
    rw [div_le_iff₀ hc0] at this; linarith
  have h3 : Real.log (100 / ε') ≤ 4 * √(Real.log n) := by
    have : Real.log (100 / ε') / 4 ≤ √(Real.log n) := Real.le_sqrt_of_sq_le hT3
    linarith
  have := lower_fixed hX ε' hε'0 hε'1 n hn hT1 h2 h3
  have hmin : 1 - ε ≤ 1 - ε' := by linarith [min_le_left ε 1]
  exact hmin.trans this

end OMA.C64

lemma h1_solution : OMA.R_Erdos1164_erdos_1164_R1.H1 :=
  fun hX ε hε ↦ OMA.C64.lower hX ε hε
end H1Sec

section H2R1Sec
open MeasureTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace OMA.R_Erdos1164_erdos_1164_R1_H2_R1

open Erdos1165 Erdos1164 OMA.R_Erdos1164_erdos_1164_R1

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
      ∀ (n d : ℕ), 4 ≤ d → d ≤ n → ∀ a : ℤ, 2 ∣ a → (d : ℤ) ≤ |a| →
        c * Real.log d / Real.log n ≤
          1 - ∑' k : ℕ, (1 - (1 : ℝ) / n) ^ (k + 1) *
            (ℙ {ω | position X (k + 1) ω = (a, 0) ∧
              ∀ j < k + 1, position X j ω ≠ (a, 0)}).toReal

def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
    ∀ (n : ℕ), 2 ≤ n → ∀ (S : Finset (ℤ × ℤ)),
      S.Nonempty → (0 : ℤ × ℤ) ∉ S → ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      (∀ z ∈ S, ∀ w ∈ insert (0 : ℤ × ℤ) S, w ≠ z →
        q ≤ 1 - ∑' k : ℕ, (1 - (1 : ℝ) / n) ^ (k + 1) *
          (ℙ {ω | position X (k + 1) ω = z - w ∧
            ∀ j < k + 1, position X j ω ≠ z - w}).toReal) →
      (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal ≤
        4 * Real.exp (-(q / 2) * Real.log S.card)

lemma closedDisc_mono {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : closedDisc r₁ ⊆ closedDisc r₂ := by
  intro x hx
  have h1 : (r₁ : ℤ) ^ 2 ≤ (r₂ : ℤ) ^ 2 := by
    have : (r₁ : ℤ) ≤ (r₂ : ℤ) := Int.ofNat_le.mpr h
    nlinarith [Int.natCast_nonneg r₁]
  exact le_trans hx h1

lemma coveringRadius_le_of_not_covers {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω)
    {r : ℕ} (h : ¬ Covers X n ω (closedDisc r)) :
    coveringRadius X n ω ≤ r := by
  refine csSup_le ⟨0, covers_closedDisc_zero X n ω⟩ ?_
  intro r' hr'
  by_contra hlt
  have hle : r ≤ r' := by omega
  exact h fun x hx ↦ hr' x (closedDisc_mono hle hx)

lemma log_coveringRadius_le_of_le {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω)
    {C : ℝ} (hC : 0 ≤ C) {r : ℕ} (hr : (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)))
    (hcov : coveringRadius X n ω ≤ r) :
    Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n) := by
  rcases Nat.eq_zero_or_pos (coveringRadius X n ω) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg hC (Real.sqrt_nonneg _)
  · have hpos' : (0 : ℝ) < (coveringRadius X n ω : ℝ) := Nat.cast_pos.mpr hpos
    have hle : (coveringRadius X n ω : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hcov
    calc Real.log (coveringRadius X n ω) ≤ Real.log (r : ℝ) := Real.log_le_log hpos' hle
      _ ≤ Real.log (Real.exp (C * Real.sqrt (Real.log n))) :=
          Real.log_le_log (lt_of_lt_of_le hpos' hle) hr
      _ = C * Real.sqrt (Real.log n) := Real.log_exp _

lemma large_n_params {C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ r d M : ℕ,
        4 ≤ d ∧ 2 ∣ d ∧ d ≤ n ∧ 1 ≤ M ∧ M * d ≤ r ∧
        (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) ∧
        0 < Real.log n ∧
        (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) ≤ Real.log d ∧
        (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) ≤ Real.log M := by
  let B : ℝ := max (max (Real.log 64 / C) (4 * Real.log 4 / C)) C
  refine ⟨⌈Real.exp (B ^ 2 + 1)⌉₊ + 4, fun n hn ↦ ?_⟩
  have hn4 : 4 ≤ n := by omega
  have hlogn_ge : B ^ 2 + 1 ≤ Real.log n := by
    have h1 : Real.exp (B ^ 2 + 1) ≤ (⌈Real.exp (B ^ 2 + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (B ^ 2 + 1)⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : ⌈Real.exp (B ^ 2 + 1)⌉₊ ≤ n)
    have h3 : Real.exp (B ^ 2 + 1) ≤ (n : ℝ) := h1.trans h2
    have h4 := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at h4
  have hlogn_pos : 0 < Real.log n := by
    have : 0 ≤ B ^ 2 := sq_nonneg B
    linarith
  have hsqrt_ge_B : B ≤ Real.sqrt (Real.log n) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hC_sqrt_le : C * Real.sqrt (Real.log n) ≤ Real.log n := by
    have h1 : C ≤ Real.sqrt (Real.log n) := (le_max_right _ _).trans hsqrt_ge_B
    calc C * Real.sqrt (Real.log n) ≤ Real.sqrt (Real.log n) * Real.sqrt (Real.log n) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ = Real.log n := Real.mul_self_sqrt hlogn_pos.le
  have hlog64_le : Real.log 64 ≤ C * Real.sqrt (Real.log n) := by
    have h1 : Real.log 64 / C ≤ Real.sqrt (Real.log n) :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hsqrt_ge_B
    exact ((div_le_iff₀ hC).mp h1).trans_eq (mul_comm _ _)
  have hlog4_le : 4 * Real.log 4 ≤ C * Real.sqrt (Real.log n) := by
    have h1 : 4 * Real.log 4 / C ≤ Real.sqrt (Real.log n) :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hsqrt_ge_B
    exact ((div_le_iff₀ hC).mp h1).trans_eq (mul_comm _ _)
  let r : ℕ := ⌊Real.exp (C * Real.sqrt (Real.log n))⌋₊
  have hr_le_exp : (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) :=
    Nat.floor_le (Real.exp_pos _).le
  have hr_le_n : r ≤ n := by
    have h1 : (r : ℝ) ≤ (n : ℝ) := by
      calc (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) := hr_le_exp
        _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hC_sqrt_le
        _ = (n : ℝ) := Real.exp_log (by exact_mod_cast (by omega : 0 < n))
    exact Nat.cast_le.mp h1
  have hexp64 : (64 : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) := by
    calc (64 : ℝ) = Real.exp (Real.log 64) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (C * Real.sqrt (Real.log n)) := Real.exp_le_exp.mpr hlog64_le
  have hr_ge_64 : 64 ≤ r := Nat.le_floor hexp64
  have hr_half_exp : Real.exp (C * Real.sqrt (Real.log n)) / 2 ≤ (r : ℝ) := by
    have h1 : Real.exp (C * Real.sqrt (Real.log n)) < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  let sr : ℕ := Nat.sqrt r
  have hsr_ge_8 : 8 ≤ sr := Nat.le_sqrt.mpr (by omega)
  have hsr_sq : sr * sr ≤ r := Nat.sqrt_le r
  have hr_lt_sq : r < (sr + 1) * (sr + 1) := Nat.lt_succ_sqrt r
  let d : ℕ := 2 * (sr / 2)
  have hd_even : 2 ∣ d := ⟨sr / 2, rfl⟩
  have hd_le_sr : d ≤ sr := by omega
  have hd_ge_4 : 4 ≤ d := by omega
  have hd_le_r : d ≤ r := by
    have : sr ≤ r := by nlinarith
    omega
  have hd_le_n : d ≤ n := hd_le_r.trans hr_le_n
  have hd_ge_half : (sr + 1 : ℝ) / 2 ≤ (d : ℝ) := by
    have : sr + 1 ≤ 2 * d := by omega
    have : (sr + 1 : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast this
    linarith
  let M : ℕ := r / d
  have hM_ge_sr : sr ≤ M := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hM_ge_half : (sr + 1 : ℝ) / 2 ≤ (M : ℝ) := by
    have : (sr : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM_ge_sr
    have : sr + 1 ≤ 2 * sr := by omega
    have : (sr + 1 : ℝ) ≤ 2 * (sr : ℝ) := by exact_mod_cast this
    linarith
  have hM_pos : 1 ≤ M := by omega
  have hMd_le_r : M * d ≤ r := Nat.div_mul_le_self r d
  have hsqrt_r_lt : Real.sqrt (r : ℝ) < (sr : ℝ) + 1 := by
    refine (Real.sqrt_lt' (by positivity)).mpr ?_
    have h1 : r < (sr + 1) ^ 2 := by rw [sq]; exact hr_lt_sq
    have h2 : (r : ℝ) < ((sr + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
    push_cast at h2
    exact h2
  have hE_half : Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 4 ≤ (sr + 1 : ℝ) / 2 := by
    have h1 : Real.exp (C * Real.sqrt (Real.log n)) / 4 ≤ (r : ℝ) / 2 := by linarith
    have h2 : Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 2 ≤ Real.sqrt (r : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hsq : (Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n)))) ^ 2 =
          Real.exp (C * Real.sqrt (Real.log n)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc (Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 2) ^ 2
          = Real.exp (C * Real.sqrt (Real.log n)) / 4 := by rw [div_pow, hsq]; norm_num
        _ ≤ (r : ℝ) / 2 := h1
        _ ≤ (r : ℝ) := by linarith [show (0 : ℝ) ≤ (r : ℝ) by positivity]
    linarith
  have hexp_pos : 0 < Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 4 := by positivity
  have hlow : (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) ≤
      Real.log (Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 4) := by
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
    linarith
  exact ⟨r, d, M, hd_ge_4, hd_even, hd_le_n, hM_pos, hMd_le_r, hr_le_exp, hlogn_pos,
    hlow.trans (Real.log_le_log hexp_pos (hE_half.trans hd_ge_half)),
    hlow.trans (Real.log_le_log hexp_pos (hE_half.trans hM_ge_half))⟩

theorem main : H1 → H2 → OMA.R_Erdos1164_erdos_1164_R1.H2 := by
  intro h1 h2 Ω _ _ X hX ε hε
  obtain ⟨c₀, hc₀, hc₀_bound⟩ := h1
  let c : ℝ := min c₀ 1
  have hc_pos : 0 < c := lt_min hc₀ zero_lt_one
  have hc_le1 : c ≤ 1 := min_le_right _ _
  have hc_le0 : c ≤ c₀ := min_le_left _ _
  let C : ℝ := Real.sqrt (32 * (4 / ε) / c) + 1
  have hC_pos : 0 < C := by positivity
  have hC_sq : 4 / ε ≤ (c / 32) * C ^ 2 := by
    have h1' : 32 * (4 / ε) / c ≤ C ^ 2 := by
      have hnon : 0 ≤ 32 * (4 / ε) / c := by positivity
      have hsq : Real.sqrt (32 * (4 / ε) / c) ≤ C := by dsimp [C]; linarith
      calc 32 * (4 / ε) / c = (Real.sqrt (32 * (4 / ε) / c)) ^ 2 := (Real.sq_sqrt hnon).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
    have h2' : (c / 32) * (32 * (4 / ε) / c) ≤ (c / 32) * C ^ 2 :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    have h3' : (c / 32) * (32 * (4 / ε) / c) = 4 / ε := by field_simp
    linarith
  have hC_exp : 4 * Real.exp (-((c / 32) * C ^ 2)) ≤ ε := by
    have h1' : 4 / ε ≤ Real.exp ((c / 32) * C ^ 2) := by
      have := Real.add_one_le_exp ((c / 32) * C ^ 2)
      linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have := (div_le_iff₀ hε).mp h1'
    linarith
  obtain ⟨N₀, hN₀⟩ := large_n_params hC_pos
  refine ⟨C, eventually_atTop.mpr ⟨N₀ + 4, fun n hn ↦ ?_⟩⟩
  have hn2 : 2 ≤ n := by omega
  obtain ⟨r, d, M, hd_ge_4, hd_even, hd_le_n, hM_pos, hMd_le_r, hr_le_exp, hlogn_pos,
    hlogd_low, hlogM_low⟩ := hN₀ n (by omega)
  let S : Finset (ℤ × ℤ) := (Finset.Icc 1 M).image (fun j ↦ (((j * d : ℕ) : ℤ), (0 : ℤ)))
  have hS_ne : S.Nonempty :=
    ⟨(((1 * d : ℕ) : ℤ), (0 : ℤ)),
      Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM_pos⟩, rfl⟩⟩
  have hS_zero : (0 : ℤ × ℤ) ∉ S := by
    intro h0
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp h0
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjd : (j * d : ℕ) = 0 := by
      have := congrArg Prod.fst hj0
      simpa using this
    nlinarith
  have hS_card : S.card = M := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have h1' : (a * d : ℕ) = b * d := by
        have := congrArg Prod.fst hab
        simpa using this
      exact Nat.eq_of_mul_eq_mul_right (by omega) h1'
  have hS_sub : (S : Set (ℤ × ℤ)) ⊆ closedDisc r := by
    intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
    have hjd : j * d ≤ r := (Nat.mul_le_mul_right d hjM).trans hMd_le_r
    show ((j * d : ℕ) : ℤ) ^ 2 + (0 : ℤ) ^ 2 ≤ (r : ℤ) ^ 2
    have hjd' : ((j * d : ℕ) : ℤ) ≤ (r : ℤ) := Int.ofNat_le.mpr hjd
    nlinarith [Int.natCast_nonneg (j * d)]
  let q : ℝ := c * Real.log d / Real.log n
  have hlogd_pos : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hlogd_le : Real.log d ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast hd_le_n)
  have hq_nonneg : 0 ≤ q := by positivity
  have hq_le1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hlogn_pos]
    calc c * Real.log d ≤ 1 * Real.log d := mul_le_mul_of_nonneg_right hc_le1 hlogd_pos.le
      _ = Real.log d := one_mul _
      _ ≤ Real.log n := hlogd_le
  have hq_pair : ∀ z ∈ S, ∀ w ∈ insert (0 : ℤ × ℤ) S, w ≠ z →
      q ≤ 1 - ∑' k : ℕ, (1 - (1 : ℝ) / n) ^ (k + 1) *
        (ℙ {ω | position X (k + 1) ω = z - w ∧
          ∀ j < k + 1, position X j ω ≠ z - w}).toReal := by
    intro z hz w hw hwz
    obtain ⟨jz, hjz, rfl⟩ := Finset.mem_image.mp hz
    have hw_ex : ∃ iw : ℕ, iw ≤ M ∧ w = (((iw * d : ℕ) : ℤ), (0 : ℤ)) := by
      rcases Finset.mem_insert.mp hw with rfl | hwS
      · refine ⟨0, by omega, ?_⟩
        ext <;> simp
      · obtain ⟨iw, hiw, rfl⟩ := Finset.mem_image.mp hwS
        exact ⟨iw, (Finset.mem_Icc.mp hiw).2, rfl⟩
    obtain ⟨iw, -, rfl⟩ := hw_ex
    have hne : iw ≠ jz := by
      intro heq
      subst heq
      exact hwz rfl
    have hzw_eq : (((jz * d : ℕ) : ℤ), (0 : ℤ)) - (((iw * d : ℕ) : ℤ), (0 : ℤ)) =
        (((jz : ℤ) - iw) * (d : ℤ), (0 : ℤ)) := by
      ext <;> simp <;> ring
    rw [hzw_eq]
    have hdiv : (2 : ℤ) ∣ (((jz : ℤ) - iw) * (d : ℤ)) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hd_even) _
    have habs : (d : ℤ) ≤ |((jz : ℤ) - iw) * (d : ℤ)| := by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg d)]
      have h1' : (1 : ℤ) ≤ |(jz : ℤ) - iw| := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rw [abs_of_pos (by omega)]; omega
        · rw [abs_of_neg (by omega)]; omega
      calc (d : ℤ) = 1 * (d : ℤ) := (one_mul _).symm
        _ ≤ |(jz : ℤ) - iw| * (d : ℤ) := mul_le_mul_of_nonneg_right h1' (Int.natCast_nonneg d)
    have hbound := hc₀_bound hX n d hd_ge_4 hd_le_n (((jz : ℤ) - iw) * (d : ℤ)) hdiv habs
    have hc_mul : q ≤ c₀ * Real.log d / Real.log n := by
      dsimp [q]
      gcongr
    exact hc_mul.trans hbound
  have hprob_cov : (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal ≤
      4 * Real.exp (-(q / 2) * Real.log S.card) :=
    h2 hX n hn2 S hS_ne hS_zero q hq_nonneg hq_le1 hq_pair
  have hexp_bound : (c / 32) * C ^ 2 ≤ (q / 2) * Real.log S.card := by
    rw [hS_card]
    dsimp [q]
    have h0 : 0 ≤ (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) := by positivity
    have hmul : ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) ^ 2 ≤ Real.log d * Real.log M := by
      calc ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) ^ 2
          = ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) * ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) := sq _
        _ ≤ Real.log d * Real.log M := mul_le_mul hlogd_low hlogM_low h0 hlogd_pos.le
    have hsq : ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) ^ 2 = (1 / 16 : ℝ) * C ^ 2 * Real.log n := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hlogn_pos.le]
      ring
    rw [hsq] at hmul
    have hln_ne : Real.log n ≠ 0 := hlogn_pos.ne'
    have hc2_nonneg : (0 : ℝ) ≤ c / 2 := by positivity
    calc (c / 32) * C ^ 2 = (c / 2) * ((1 / 16 : ℝ) * C ^ 2 * Real.log n) / Real.log n := by
          field_simp [hln_ne]; norm_num
      _ ≤ (c / 2) * (Real.log d * Real.log M) / Real.log n := by gcongr
      _ = (c * Real.log d / Real.log n / 2) * Real.log M := by ring
  have hprob_small : (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal ≤ ε := by
    refine hprob_cov.trans ?_
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)).trans hC_exp
  let E_good : Set Ω := {ω | Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n)}
  have hmeas_good : MeasurableSet E_good :=
    meas_event hX.measurable n (fun k ↦ Real.log (k : ℝ) ≤ C * Real.sqrt (Real.log n))
  have hcompl_sub : E_goodᶜ ⊆ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x} := by
    intro ω hω
    simp only [E_good, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    have hcov_r : Covers X n ω (closedDisc r) := by
      by_contra hncov
      have hle := coveringRadius_le_of_not_covers X n ω hncov
      have hlog := log_coveringRadius_le_of_le X n ω hC_pos.le hr_le_exp hle
      linarith
    intro x hx
    exact hcov_r x (hS_sub hx)
  have hcompl_le : (ℙ E_goodᶜ).toReal ≤ ε := by
    calc (ℙ E_goodᶜ).toReal ≤ (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcompl_sub)
      _ ≤ ε := hprob_small
  rw [prob_compl_eq_one_sub hmeas_good, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one] at hcompl_le
  linarith

end OMA.R_Erdos1164_erdos_1164_R1_H2_R1
end H2R1Sec

section H2H1Sec
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165

namespace OMA.AxisGreen

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` coordinates. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

/-- extension by zero of a finite window -/
def ext (m : ℕ) (z : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ if h : i < m then z ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma det_pre {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A)
    (j : ℕ) : {ω | sh j (path X ω) ∈ A} =
      (fun ω (i : Fin m) ↦ X (j + i) ω) ⁻¹' {z | ext m z ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]

lemma meas_window {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (m j : ℕ) :
    Measurable (fun ω (i : Fin m) ↦ X (j + i) ω) :=
  measurable_pi_iff.mpr fun _ ↦ hX.measurable _

lemma det_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (j : ℕ) :
    MeasurableSet {ω | sh j (path X ω) ∈ A} := by
  rw [det_pre X hA j]
  exact meas_window hX m j (Set.to_countable _).measurableSet

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

/-- fixed-time Markov property: shifting does not change probabilities -/
lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]


lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

/-- independence of disjoint blocks, combined with the Markov property -/
lemma prob_block {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {t s : ℕ}
    {A B : Set (ℕ → ℤ × ℤ)} (hA : Det t A) (hB : Det s B) :
    ℙ {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      ℙ {ω | path X ω ∈ A} * ℙ {ω | path X ω ∈ B} := by
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hind := hX.indep.indepFun_finset (Finset.range t) (Finset.Ico t (t + s)) hdisj
    hX.measurable
  have hset : {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      {ω | path X ω ∈ A} ∩ {ω | sh t (path X ω) ∈ B} := rfl
  rw [hset, ← prob_shift hX hB t, preA X hA, preB X hB]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet


/-- number of `±1` paths of length `t` ending at `u` -/
def c : ℕ → ℤ → ℕ
  | 0, u => if u = 0 then 1 else 0
  | t + 1, u => c t (u - 1) + c t (u + 1)

lemma c_neg : ∀ (t : ℕ) (u : ℤ), u < -(t : ℤ) → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_neg t (u - 1) (by push_cast at h; omega), c_neg t (u + 1) (by push_cast at h; omega)]

lemma c_odd : ∀ (t : ℕ) (u : ℤ), ((t : ℤ) + u) % 2 = 1 → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_odd t (u - 1) (by push_cast at h; omega), c_odd t (u + 1) (by push_cast at h; omega)]

lemma c_choose : ∀ (t i : ℕ), c t (2 * (i : ℤ) - t) = t.choose i
  | 0, i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [c]
    · simp [c, Nat.choose_eq_zero_of_lt h]; omega
  | t + 1, 0 => by
    simp only [c, Nat.choose_zero_right]
    rw [c_neg t _ (by push_cast; omega)]
    have := c_choose t 0
    simp only [Nat.choose_zero_right] at this
    rw [show (2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((0 : ℕ) : ℤ) - (t : ℤ) by
      push_cast; ring, this]
  | t + 1, i + 1 => by
    simp only [c, Nat.choose_succ_succ]
    have h1 := c_choose t i
    have h2 := c_choose t (i + 1)
    rw [show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) - 1) = 2 * (i : ℤ) - t by push_cast; ring,
      show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((i + 1 : ℕ) : ℤ) - t by
        push_cast; ring, h1, h2]

lemma c_even (j : ℕ) : c (2 * j) 0 = j.centralBinom := by
  have := c_choose (2 * j) j
  rw [show (2 * (j : ℤ) - ((2 * j : ℕ) : ℤ)) = 0 by push_cast; ring] at this
  rw [this, Nat.centralBinom_eq_two_mul_choose]

lemma c_odd0 (j : ℕ) : c (2 * j + 1) 0 = 0 := c_odd _ _ (by push_cast; omega)

/-- the 2D count factorizes after the 45 degree rotation -/
lemma c_step (t : ℕ) (a b : ℤ) :
    c (t + 1) (a + b) * c (t + 1) (a - b) =
      c t ((a - 1) + b) * c t ((a - 1) - b) + c t ((a + 1) + b) * c t ((a + 1) - b) +
      c t (a + (b - 1)) * c t (a - (b - 1)) + c t (a + (b + 1)) * c t (a - (b + 1)) := by
  simp only [c]
  rw [show a - 1 + b = a + b - 1 by ring, show a - 1 - b = a - b - 1 by ring,
    show a + 1 + b = a + b + 1 by ring, show a + 1 - b = a - b + 1 by ring,
    show a + (b - 1) = a + b - 1 by ring, show a - (b - 1) = a - b + 1 by ring,
    show a + (b + 1) = a + b + 1 by ring, show a - (b + 1) = a - b - 1 by ring]
  ring


def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

lemma steps_eq : steps = (stepsF : Set (ℤ × ℤ)) := by
  simp [steps, stepsF]

lemma prob_step {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) (S : Set (ℤ × ℤ)) :
    ℙ (X k ⁻¹' S) = (4 : ℝ≥0∞)⁻¹ * Measure.count (steps ∩ S) := by
  have hu : Measure.map (X k) ℙ = ProbabilityTheory.cond Measure.count steps := hX.isUniform k
  rw [← Measure.map_apply (hX.measurable k) (Set.to_countable S).measurableSet, hu,
    ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet, steps_eq,
    Measure.count_apply_finset]
  rfl

lemma prob_step_eq {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) {e : ℤ × ℤ} (he : e ∈ steps) :
    ℙ (X k ⁻¹' {e}) = (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_step hX, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr he),
    Measure.count_singleton, mul_one]

lemma prob_step_bad {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) : ℙ (X k ⁻¹' stepsᶜ) = 0 := by
  rw [prob_step hX, Set.inter_compl_self, measure_empty, mul_zero]

lemma det_pos (t : ℕ) (z : ℤ × ℤ) : Det t {y | pos y t = z} := fun y y' h hy ↦ by
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [← pos_congr h le_rfl, hy]

lemma det_zero (e : ℤ × ℤ) : Det 1 {y | y 0 = e} := fun y y' h hy ↦ by
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [← h 0 one_pos, hy]

lemma prob_pos_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ)
    (he : e ∈ steps) :
    ℙ {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} =
      ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_block hX (det_pos t (x - e)) (det_zero e)]
  congr 1
  exact prob_step_eq hX 0 he

lemma pos_succ (y : ℕ → ℤ × ℤ) (t : ℕ) : pos y (t + 1) = pos y t + y t :=
  Finset.sum_range_succ _ _

/-- the return probability bound, in counting form -/
lemma prob_pos_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t ≤
      ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞)
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      simp only [c, add_zero, sub_self, if_true, mul_one, Nat.cast_one]
      exact prob_le_one
    · have : {ω | pos (path X ω) 0 = (a, b)} = ∅ := by
        ext ω
        simp only [pos, Finset.range_zero, Finset.sum_empty, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        exact fun h' ↦ h h'.symm
      rw [this, measure_empty]
      simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hsub : {ω | pos (path X ω) (t + 1) = x} ⊆
        (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ∪ X t ⁻¹' stepsᶜ := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, pos_succ] at hω
      by_cases hs : X t ω ∈ steps
      · have hx : pos (path X ω) t = x - X t ω := by rw [← hω]; simp [path]
        have hE : ω ∈ E (X t ω) := ⟨hx, rfl⟩
        simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h | h | h | h <;> rw [h] at hE <;> simp [hE]
      · exact Or.inr hs
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) ≤
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      apply le_of_eq
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hm : ℙ {ω | pos (path X ω) (t + 1) = x} ≤
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [prob_step_bad hX t, add_zero]
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      exact measure_union_le _ _
    calc ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1)
        ≤ (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) :=
          by gcongr
      _ = ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by ring
      _ ≤ ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
        gcongr
        · refine (hE _ h1).trans ?_
          have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h2).trans ?_
          have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h3).trans ?_
          have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h4).trans ?_
          have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
      _ = ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞) := by
        rw [c_step]; push_cast; ring


lemma cb_sq_le (j : ℕ) (hj : 1 ≤ j) :
    ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j ≤ 1 / (Real.pi * j) := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.le_W j
  have h1 : Real.pi * j / (2 * j + 1) ≤ (2 * (j : ℝ) + 1) / (2 * j + 2) * (Real.pi / 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * (j : ℝ) + 1) * Real.pi * (2 * j + 1) =
        Real.pi * j * ((2 * j + 2) * 2) + Real.pi := by ring
    rw [this]
    linarith [Real.pi_pos]
  have h2 : Real.pi * j ≤ Real.Wallis.W j * (2 * j + 1) := by
    have := h1.trans hle
    rwa [div_le_iff₀ (by positivity)] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc (j.centralBinom : ℝ) ^ 2 * (Real.pi * j)
      ≤ (j.centralBinom : ℝ) ^ 2 * (Real.Wallis.W j * (2 * j + 1)) := by gcongr
    _ = Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by ring

/-- return probability, as a real number -/
noncomputable def u {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = 0}).toReal

lemma prob_zero_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) :
    u X t * 4 ^ t ≤ (c t 0 : ℝ) ^ 2 := by
  have h := prob_pos_le hX t 0 0
  simp only [add_zero, sub_zero] at h
  change ℙ {ω | pos (path X ω) t = 0} * 4 ^ t ≤ _ at h
  have h' : (ℙ {ω | pos (path X ω) t = 0} * 4 ^ t).toReal ≤ ((c t 0 * c t 0 : ℕ) : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  unfold u
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at h'
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal * 4 ^ t ≤ ((c t 0 * c t 0 : ℕ) : ℝ) := h'
    _ = (c t 0 : ℝ) ^ 2 := by push_cast; ring

lemma u_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : 0 ≤ u X t :=
  ENNReal.toReal_nonneg

lemma u_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : u X t ≤ 1 := by
  unfold u
  have : ℙ {ω | pos (path X ω) t = 0} ≤ 1 := prob_le_one
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) this
    _ = 1 := by simp

lemma u_odd {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) : u X (2 * j + 1) = 0 := by
  have h := prob_zero_le hX (2 * j + 1)
  rw [c_odd0] at h
  have h0 := u_nonneg X (2 * j + 1)
  have hp : (0 : ℝ) < 4 ^ (2 * j + 1) := by positivity
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  nlinarith

lemma u_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) (hj : 1 ≤ j) :
    u X (2 * j) ≤ 1 / (Real.pi * j) := by
  have h := prob_zero_le hX (2 * j)
  rw [c_even, pow_mul] at h
  norm_num at h
  refine le_trans ?_ (cb_sq_le j hj)
  rw [le_div_iff₀ (by positivity)]
  exact h

lemma u_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (ht : 1 ≤ t) :
    u X t ≤ 2 / (Real.pi * t) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
  · have hj : 1 ≤ j := by omega
    refine (u_even hX j hj).trans (le_of_eq ?_)
    have : (j : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [u_odd hX]
    positivity

lemma pos_zero (y : ℕ → ℤ × ℤ) : pos y 0 = 0 := by simp [pos]
variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma meas_block (hX : IsSimpleRandomWalkSteps X) {t s : ℕ} {A B : Set (ℕ → ℤ × ℤ)}
    (hA : Det t A) (hB : Det s B) :
    MeasurableSet {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} := by
  have h1 : MeasurableSet {ω | path X ω ∈ A} := by rw [path_eq]; exact det_meas hX hA 0
  exact h1.inter (det_meas hX hB t)

/-- the return probability lower bound, in counting form -/
lemma prob_pos_ge (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞) ≤
      ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      have : {ω | pos (path X ω) 0 = ((0 : ℤ), (0 : ℤ))} = Set.univ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, pos_zero]; rfl
      rw [this, measure_univ]
      simp [c]
    · have hc : c 0 (a + b) * c 0 (a - b) = 0 := by
        simp only [c]
        by_cases ha : a + b = 0
        · have : a - b ≠ 0 := by
            intro hb; apply h; ext <;> simp <;> omega
          simp [this]
        · simp [ha]
      rw [hc]; simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hEm : ∀ e, MeasurableSet (E e) := fun e ↦ meas_block hX (det_pos t _) (det_zero e)
    have hsub : (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ⊆
        {ω | pos (path X ω) (t + 1) = x} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, pos_succ]
      have key : ∀ e, ω ∈ E e → pos (path X ω) t + path X ω t = x := by
        rintro e ⟨h1, h2⟩
        simp only [Set.mem_ofPred_eq] at h1 h2
        have : path X ω t = e := h2
        rw [h1, this]; abel
      rcases hω with ((h | h) | h) | h <;> exact key _ h
    have hd : ∀ e e', e ≠ e' → Disjoint (E e) (E e') := by
      intro e e' hne
      rw [Set.disjoint_left]
      rintro ω ⟨-, h1⟩ ⟨-, h2⟩
      exact hne ((show path X ω t = e from h1).symm.trans h2)
    have hsum : ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) ≤
        ℙ {ω | pos (path X ω) (t + 1) = x} := by
      refine le_trans (le_of_eq ?_) (measure_mono hsub)
      rw [measure_union _ (hEm _), measure_union _ (hEm _), measure_union _ (hEm _)]
      · exact hd _ _ (by decide)
      · exact Disjoint.union_left (hd _ _ (by decide)) (hd _ _ (by decide))
      · exact Disjoint.union_left (Disjoint.union_left (hd _ _ (by decide))
          (hd _ _ (by decide))) (hd _ _ (by decide))
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) =
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    calc ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞)
        = ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
          rw [c_step]; push_cast; ring
      _ ≤ ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by
        rw [hE _ h1, hE _ h2, hE _ h3, hE _ h4]
        gcongr
        · have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
      _ = (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) := by ring
      _ ≤ ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1) := by gcongr

open Real

lemma cb_sq_ge (j : ℕ) : 1 / (π * ((j : ℝ) + 1)) ≤ ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.W_le j
  have hpi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1))
      ≤ π / 2 * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by gcongr
    _ ≤ (j.centralBinom : ℝ) ^ 2 * (π * ((j : ℝ) + 1)) := by nlinarith

lemma u_even_ge (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    1 / (π * ((j : ℝ) + 1)) ≤ u X (2 * j) := by
  have h := prob_pos_ge hX (2 * j) 0 0
  simp only [add_zero, sub_zero] at h
  change _ ≤ ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j) at h
  have h' : ((c (2 * j) 0 * c (2 * j) 0 : ℕ) : ℝ≥0∞).toReal ≤
      (ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, c_even, pow_mul] at h'
  norm_num at h'
  refine (cb_sq_ge j).trans ?_
  rw [div_le_iff₀ (by positivity)]
  unfold u
  nlinarith

noncomputable def p (X : ℕ → Ω → ℤ × ℤ) (z : ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = z}).toReal

lemma axis_count (hX : IsSimpleRandomWalkSteps X) (a : ℤ) (t : ℕ) :
    p X (a, 0) t * 4 ^ t = (c t a : ℝ) ^ 2 := by
  have h := le_antisymm (prob_pos_le hX t a 0) (prob_pos_ge hX t a 0)
  have he := congrArg ENNReal.toReal h
  simp only [add_zero, sub_zero, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, Nat.cast_mul] at he
  change _ * _ ^ t = _ at he
  simpa only [p, show (4 : ℝ≥0∞).toReal = 4 by norm_num, pow_two] using he

lemma axis_max (hX : IsSimpleRandomWalkSteps X) {a : ℤ} (ha : 2 ∣ a) (t : ℕ) :
    p X (a, 0) t ≤ u X t := by
  have hc : c t a ≤ c t 0 := by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
    · by_cases h : a < -((2 * j : ℕ) : ℤ)
      · simp [c_neg _ _ h]
      · let i := ((a + (2 * j : ℕ)) / 2).toNat
        have hi : 2 * (i : ℤ) - (2 * j : ℕ) = a := by dsimp [i]; omega
        rw [← hi, c_choose, c_even]
        exact Nat.choose_le_centralBinom _ _
    · rw [c_odd (2 * j + 1) a (by push_cast; omega)]
      exact Nat.zero_le _
  have h0 : u X t * 4 ^ t = (c t 0 : ℝ) ^ 2 := axis_count hX 0 t
  apply le_of_mul_le_mul_right (a := (4 : ℝ) ^ t) ?_ (by positivity)
  rw [axis_count hX, h0]
  gcongr

lemma c_far : ∀ (t : ℕ) (a : ℤ), (t : ℤ) < |a| → c t a = 0
  | 0, a, h => by simp [c, abs_pos.mp (show 0 < |a| from h)]
  | t + 1, a, h => by
    simp only [c]
    rw [c_far t (a - 1) (by
      push_cast at h
      rcases lt_abs.mp h with hp | hn <;> apply lt_abs.mpr <;> omega),
      c_far t (a + 1) (by
      push_cast at h
      rcases lt_abs.mp h with hp | hn <;> apply lt_abs.mpr <;> omega), add_zero]

lemma axis_far (hX : IsSimpleRandomWalkSteps X) {t : ℕ} {a : ℤ} (ht : (t : ℤ) < |a|) :
    p X (a, 0) t = 0 := by
  have h := axis_count hX a t
  rw [c_far t a ht] at h
  simpa using h

def firstAt (z : ℤ × ℤ) (h : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {y | pos y h = z ∧ ∀ j < h, pos y j ≠ z}

lemma det_first (z : ℤ × ℤ) (t : ℕ) : Det t (firstAt z t) :=
  fun _ _ h hy ↦ ⟨(pos_congr h le_rfl).symm.trans hy.1,
    fun j hj he ↦ hy.2 j hj ((pos_congr h hj.le).trans he)⟩

noncomputable def f (X : ℕ → Ω → ℤ × ℤ) (z : ℤ × ℤ) (h : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ firstAt z h}).toReal

lemma renewal (hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) (t : ℕ) :
    p X z t = ∑ h ∈ Finset.range (t + 1), f X z h * u X (t - h) := by
  classical
  let E (h : ℕ) : Set Ω := {ω | path X ω ∈ firstAt z h ∧
    sh h (path X ω) ∈ {y | pos y (t - h) = 0}}
  have hd : Set.PairwiseDisjoint (↑(Finset.range (t + 1))) E := by
    intro h _ k _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨hh, -⟩ ⟨hk, -⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hk.2 h hlt hh.1
    · exact hh.2 k hlt hk.1
  have hU : {ω | pos (path X ω) t = z} = ⋃ h ∈ Finset.range (t + 1), E h := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro ht
      have hex : ∃ j, pos (path X ω) j = z := ⟨t, ht⟩
      let h := Nat.find hex
      have hh : pos (path X ω) h = z := Nat.find_spec hex
      have hle : h ≤ t := Nat.find_min' hex ht
      refine ⟨h, by omega, ⟨hh, fun j hj ↦ Nat.find_min hex hj⟩, ?_⟩
      have eq := pos_shift (path X ω) h (t - h)
      rw [Nat.add_sub_of_le hle, ht, hh] at eq
      exact add_left_cancel (show z + pos (sh h (path X ω)) (t - h) = z + 0 by simpa using eq.symm)
    · rintro ⟨h, hle, hh, hz⟩
      have eq := pos_shift (path X ω) h (t - h)
      rw [Nat.add_sub_of_le (by omega), hh.1, show pos (sh h (path X ω)) (t-h) = 0 from hz,
        add_zero] at eq
      exact eq
  unfold p
  rw [hU, measure_biUnion_finset hd (fun h _ ↦ meas_block hX (det_first z h) (det_pos (t-h) 0)),
    ENNReal.toReal_sum (fun h _ ↦ measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro h _
  change (ℙ {ω | path X ω ∈ firstAt z h ∧ sh h (path X ω) ∈ {y | pos y (t-h) = 0}}).toReal = _
  rw [prob_block hX (det_first z h) (det_pos (t-h) 0), ENNReal.toReal_mul]
  rfl

lemma weighted_summable {v : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (hv : ∀ t, 0 ≤ v t) (hv1 : ∀ t, v t ≤ 1) : Summable (fun t ↦ s ^ t * v t) :=
  Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg hs t) (hv t))
    (fun t ↦ mul_le_of_le_one_right (pow_nonneg hs t) (hv1 t))
    (summable_geometric_of_lt_one hs hs1)

lemma prob_real_le_one (E : Set Ω) : (ℙ E).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (prob_le_one (s := E))

noncomputable def green (X : ℕ → Ω → ℤ × ℤ) (s : ℝ) (z : ℤ × ℤ) : ℝ :=
  ∑' t, s ^ t * p X z t

lemma sum_p {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (z : ℤ × ℤ) :
    Summable (fun t ↦ s ^ t * p X z t) :=
  weighted_summable hs hs1 (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ prob_real_le_one _)

lemma green_renewal (hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) (hz : z ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    green X s z = (∑' k : ℕ, s ^ (k + 1) * f X z (k + 1)) * green X s 0 := by
  have hf : Summable (fun t ↦ s ^ t * f X z t) :=
    weighted_summable hs hs1 (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ prob_real_le_one _)
  have hzero : f X z 0 = 0 := by
    have he : {ω | path X ω ∈ firstAt z 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      exact hz (h.1.symm.trans (pos_zero _))
    simp [f, he]
  have hshift := hf.tsum_eq_zero_add
  simp only [pow_zero, one_mul, hzero, zero_add] at hshift
  rw [← hshift]
  unfold green
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf.norm (sum_p (X := X) hs hs1 0).norm]
  apply tsum_congr
  intro t
  rw [renewal hX z t, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he : k + (t - k) = t := Nat.add_sub_of_le (by simpa using hk : k ≤ t)
  change s ^ t * (f X z k * u X (t-k)) = s ^ k * f X z k * (s ^ (t-k) * u X (t-k))
  calc _ = (s ^ k * s ^ (t-k)) * (f X z k * u X (t-k)) := by rw [← pow_add, he]
       _ = _ := by ring

lemma green_upper (hX : IsSimpleRandomWalkSteps X) {n : ℕ} (hn : 4 ≤ n) :
    green X (1 - 1 / (n : ℝ)) 0 ≤ 2 * log n := by
  let s : ℝ := 1 - 1 / n
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_iff₀ hn0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hn0]
  have hseries := hasSum_pow_div_log_of_abs_lt_one (show |s| < 1 by rwa [abs_of_nonneg hs])
  have hu := sum_p (X := X) hs hs1 0
  have hu' := (summable_nat_add_iff 1).mpr hu
  have htail : ∑' k : ℕ, s ^ (k + 1) * p X 0 (k+1) ≤ -log (1-s) := by
    rw [← hseries.tsum_eq]
    apply hu'.tsum_le_tsum _ hseries.summable
    intro k
    change s ^ (k+1) * u X (k+1) ≤ _
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    refine (u_le hX (k+1) (by omega)).trans ?_
    rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [Real.pi_gt_three, mul_nonneg (show 0 ≤ π - 2 by linarith [Real.pi_gt_three])
      (show 0 ≤ (k : ℝ) by positivity)]
  have hlog : 1 ≤ log (n : ℝ) := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 4) hn4
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, log_pow] at h
    norm_num at h
    linarith [Real.log_two_gt_d9]
  have he : 1-s = (n : ℝ)⁻¹ := by simp [s, one_div]
  rw [he, log_inv, neg_neg] at htail
  change (∑' t, s ^ t * p X 0 t) ≤ _
  rw [hu.tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  linarith [show p X 0 0 ≤ 1 from prob_real_le_one _]

lemma green_gap (hX : IsSimpleRandomWalkSteps X) {n d : ℕ} (hd : 4 ≤ d) (hdn : d ≤ n)
    {a : ℤ} (ha : 2 ∣ a) (had : (d : ℤ) ≤ |a|) :
    log d ≤ 4 * π * (green X (1 - 1 / (n : ℝ)) 0 - green X (1 - 1 / (n : ℝ)) (a,0)) := by
  let s : ℝ := 1 - 1 / n
  let m := d / 4
  let D (t : ℕ) := s ^ t * p X 0 t - s ^ t * p X (a,0) t
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_iff₀ hn0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hn0]
  have hD : Summable D := (sum_p (X := X) hs hs1 0).sub (sum_p hs hs1 (a,0))
  have hDpos (t : ℕ) : 0 ≤ D t :=
    sub_nonneg.mpr (mul_le_mul_of_nonneg_left (axis_max hX ha t) (pow_nonneg hs _))
  have hearly {j : ℕ} (hj : j ≤ m) : ((j : ℝ) + 1)⁻¹ ≤ 2 * π * D (2 * j) := by
    have ht : 2 * j < d := by dsimp [m] at hj; omega
    have hreach := axis_far hX ((show ((2*j : ℕ) : ℤ) < d by exact_mod_cast ht).trans_le had)
    have ht' : 4 * (j : ℝ) ≤ n := by exact_mod_cast (show 4*j ≤ n by dsimp [m] at hj; omega)
    have hpow : (1 / 2 : ℝ) ≤ s ^ (2*j) := by
      have hb := one_add_mul_le_pow (a := -(1 / (n : ℝ))) (by linarith : -2 ≤ -(1 / (n : ℝ))) (2*j)
      change _ ≤ (1 + -(1 / (n : ℝ))) ^ (2*j)
      apply le_trans _ hb
      push_cast
      field_simp
      linarith
    dsimp only [D]
    rw [hreach, mul_zero, sub_zero]
    have hlo := mul_le_mul hpow (u_even_ge hX j) (by positivity) (pow_nonneg hs _)
    change _ ≤ 2 * π * (s ^ (2*j) * u X (2*j))
    calc ((j : ℝ) + 1)⁻¹ = 2 * π * ((1/2) * (1 / (π * ((j:ℝ)+1)))) := by
          field_simp [Real.pi_ne_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  have hsub : ∑ j ∈ Finset.range (m+1), D (2*j) ≤ ∑' t, D t := by
    have he := hD.sum_le_tsum ((Finset.range (m+1)).image (fun j ↦ 2*j)) (fun t _ ↦ hDpos t)
    rwa [Finset.sum_image (by intro i _ j _ hij; dsimp at hij; omega)] at he
  have hH : (harmonic (m+1) : ℝ) ≤ 2 * π * ∑' t, D t := by
    calc (harmonic (m+1) : ℝ) = ∑ j ∈ Finset.range (m+1), ((j : ℝ)+1)⁻¹ := by
          simp [harmonic, Rat.cast_sum]
      _ ≤ ∑ j ∈ Finset.range (m+1), 2 * π * D (2*j) :=
          Finset.sum_le_sum fun j hj ↦ hearly (by simpa using hj)
      _ ≤ _ := by rw [← Finset.mul_sum]; gcongr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hmsq : (d : ℝ) ≤ ((m:ℝ) + 2)^2 := by
    have hm : (d : ℝ) ≤ 4 * (m:ℝ) + 3 := by exact_mod_cast (show d ≤ 4*m+3 by dsimp [m]; omega)
    nlinarith [sq_nonneg (m:ℝ)]
  have hlog := log_le_log hdpos hmsq
  rw [log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hh := log_add_one_le_harmonic (m+1)
  push_cast at hh
  rw [show (m:ℝ) + 1 + 1 = (m:ℝ) + 2 by ring] at hh
  have hsum : (∑' t, D t) = green X s 0 - green X s (a,0) :=
    (sum_p hs hs1 0).tsum_sub (sum_p hs hs1 (a,0))
  rw [hsum] at hH
  change log d ≤ 4 * π * (green X s 0 - green X s (a,0))
  linarith only [hlog, hh, hH]

end OMA.AxisGreen

open OMA.AxisGreen Real

-- Credit: @MrSeizy
lemma h2_h1_solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1.H1 := by
  refine ⟨1 / (8 * π), by positivity, ?_⟩
  intro Ω _ _ X hX n d hd hdn a ha had
  let s : ℝ := 1 - 1 / n
  let z : ℤ × ℤ := (a,0)
  let F := ∑' k : ℕ, s ^ (k+1) * f X z (k+1)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_iff₀ hn0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hn0]
  have hz : z ≠ 0 := by
    intro he
    have h : a = 0 := congrArg Prod.fst he
    rw [h, abs_zero] at had
    omega
  have hr : green X s z = F * green X s 0 := green_renewal hX z hz hs hs1
  have hg : log d ≤ 4 * π * (green X s 0 - green X s z) := green_gap hX hd hdn ha had
  have hupper : green X s 0 ≤ 2 * log n := green_upper hX (hd.trans hdn)
  have hdlog : 0 < log (d:ℝ) := log_pos (by exact_mod_cast (show 1 < d by omega))
  have hnlog : 0 < log (n:ℝ) := log_pos (by linarith)
  rw [hr, ← one_sub_mul] at hg
  have hG : 0 ≤ green X s 0 := tsum_nonneg fun t ↦ mul_nonneg (pow_nonneg hs t) ENNReal.toReal_nonneg
  have hF : 0 ≤ 1-F := by
    by_contra! hneg
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * π by positivity)
      (mul_nonpos_of_nonpos_of_nonneg hneg.le hG)
    linarith
  have hbound := hg.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hF)
    (show 0 ≤ 4 * π by positivity))
  change 1 / (8 * π) * log d / log n ≤ 1-F
  rw [div_le_iff₀ hnlog, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith
end H2H1Sec

section H2H2Sec
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165

namespace OMA.DiscountedCover

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` coordinates. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

/-- extension by zero of a finite window -/
def ext (m : ℕ) (z : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ if h : i < m then z ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma det_pre {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A)
    (j : ℕ) : {ω | sh j (path X ω) ∈ A} =
      (fun ω (i : Fin m) ↦ X (j + i) ω) ⁻¹' {z | ext m z ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]

lemma meas_window {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (m j : ℕ) :
    Measurable (fun ω (i : Fin m) ↦ X (j + i) ω) :=
  measurable_pi_iff.mpr fun _ ↦ hX.measurable _

lemma det_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (j : ℕ) :
    MeasurableSet {ω | sh j (path X ω) ∈ A} := by
  rw [det_pre X hA j]
  exact meas_window hX m j (Set.to_countable _).measurableSet

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

/-- fixed-time Markov property: shifting does not change probabilities -/
lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]

lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

/-- independence of disjoint blocks, combined with the Markov property -/
lemma prob_block {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {t s : ℕ}
    {A B : Set (ℕ → ℤ × ℤ)} (hA : Det t A) (hB : Det s B) :
    ℙ {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      ℙ {ω | path X ω ∈ A} * ℙ {ω | path X ω ∈ B} := by
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hind := hX.indep.indepFun_finset (Finset.range t) (Finset.Ico t (t + s)) hdisj
    hX.measurable
  have hset : {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      {ω | path X ω ∈ A} ∩ {ω | sh t (path X ω) ∈ B} := rfl
  rw [hset, ← prob_shift hX hB t, preA X hA, preB X hB]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet

abbrev Site := ℤ × ℤ
abbrev Walk := ℕ → Site

def doneBy (A : Finset Site) (t : ℕ) (y : Walk) : Prop :=
  ∀ z ∈ A, ∃ i ≤ t, pos y i = z

def first (A : Finset Site) (t : ℕ) : Set Walk :=
  {y | doneBy A t y ∧ ∀ i < t, ¬doneBy A i y}

def hit (z : Site) (t : ℕ) : Set Walk :=
  {y | pos y t = z ∧ ∀ i < t, pos y i ≠ z}

def lastAt (A : Finset Site) (z : Site) (t : ℕ) := first A t ∩ hit z t

def missing (B : Finset Site) (z : Site) (t : ℕ) : Set Walk :=
  {y | y ∈ first B t ∧ ∀ i ≤ t, pos y i ≠ z}

def endpoint (E : Set Walk) (w : Site) (t : ℕ) : Set Walk :=
  {y | y ∈ E ∧ pos y t = w}

lemma done_congr {A : Finset Site} {i t : ℕ} {y y' : Walk}
    (h : ∀ j < t, y j = y' j) (hi : i ≤ t) : doneBy A i y ↔ doneBy A i y' := by
  unfold doneBy
  constructor <;> intro hd z hz <;> obtain ⟨j, hj, he⟩ := hd z hz
  · exact ⟨j, hj, (pos_congr h (hj.trans hi)).symm.trans he⟩
  · exact ⟨j, hj, (pos_congr h (hj.trans hi)).trans he⟩

lemma det_first (A : Finset Site) (t : ℕ) : Det t (first A t) := by
  intro y y' h ⟨hd, he⟩
  exact ⟨(done_congr h le_rfl).mp hd, fun i hi hd' ↦
    he i hi ((done_congr h hi.le).mpr hd')⟩

lemma det_hit (z : Site) (t : ℕ) : Det t (hit z t) := by
  intro y y' h ⟨he, hn⟩
  exact ⟨(pos_congr h le_rfl).symm.trans he, fun i hi h' ↦
    hn i hi ((pos_congr h hi.le).trans h')⟩

lemma det_missing (B : Finset Site) (z : Site) (t : ℕ) : Det t (missing B z t) := by
  intro y y' h ⟨hf, hm⟩
  exact ⟨det_first B t y y' h hf, fun i hi he ↦ hm i hi ((pos_congr h hi).trans he)⟩

lemma det_endpoint {E : Set Walk} {t : ℕ} (hE : Det t E) (w : Site) :
    Det t (endpoint E w t) := by
  intro y y' h ⟨he, hp⟩
  exact ⟨hE _ _ h he, (pos_congr h le_rfl).symm.trans hp⟩

lemma exists_first {A : Finset Site} {t : ℕ} {y : Walk} (h : doneBy A t y) :
    ∃ i ≤ t, y ∈ first A i := by
  classical
  have hex : ∃ i, doneBy A i y := ⟨t, h⟩
  exact ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun _ ↦ Nat.find_min hex⟩

lemma first_endpoint {A : Finset Site} {t : ℕ} {y : Walk} (hf : y ∈ first A t) :
    pos y t ∈ insert 0 A := by
  classical
  cases t with
  | zero => simp [pos]
  | succ k =>
    have hn := hf.2 k (Nat.lt_succ_self k)
    unfold doneBy at hn
    push Not at hn
    obtain ⟨z, hz, hn⟩ := hn
    obtain ⟨i, hi, he⟩ := hf.1 z hz
    have : i = k + 1 := by by_contra hh; exact hn i (by omega) he
    subst i
    exact Finset.mem_insert_of_mem (he ▸ hz)

lemma exists_last {A : Finset Site} (ha : A.Nonempty) (h0 : 0 ∉ A) {t : ℕ} {y : Walk}
    (hf : y ∈ first A t) : ∃ z ∈ A, y ∈ lastAt A z t := by
  classical
  cases t with
  | zero =>
    obtain ⟨z, hz⟩ := ha
    obtain ⟨i, hi, he⟩ := hf.1 z hz
    have : z = 0 := by simpa [Nat.le_zero.mp hi, pos] using he.symm
    exact (h0 (this ▸ hz)).elim
  | succ k =>
    have hn := hf.2 k (Nat.lt_succ_self k)
    unfold doneBy at hn
    push Not at hn
    obtain ⟨z, hz, hn⟩ := hn
    obtain ⟨i, hi, he⟩ := hf.1 z hz
    have : i = k + 1 := by by_contra hh; exact hn i (by omega) he
    subst i
    exact ⟨z, hz, hf, he, fun i hi ↦ hn i (by omega)⟩

lemma first_split {A : Finset Site} {z : Site} (hz : z ∈ A) {t : ℕ} :
    first A t ⊆ (first (A.erase z) t \ missing (A.erase z) z t) ∪ lastAt A z t := by
  classical
  intro y hf
  have hb : doneBy (A.erase z) t y := fun x hx ↦ hf.1 x (Finset.mem_of_mem_erase hx)
  obtain ⟨j, hj, he⟩ := hf.1 z hz
  by_cases hl : y ∈ hit z t
  · exact Or.inr ⟨hf, hl⟩
  left
  have hprev : ∃ k < t, pos y k = z := by
    by_contra! hn
    exact hl ⟨by rwa [show t = j by by_contra h; exact hn j (by omega) he], hn⟩
  obtain ⟨k, hk, he'⟩ := hprev
  refine ⟨⟨hb, ?_⟩, fun hm ↦ hm.2 j hj he⟩
  intro i hi hd
  apply hf.2 (max i k) (max_lt hi hk)
  intro x hx
  by_cases h : x = z
  · exact ⟨k, le_max_right .., he'.trans h.symm⟩
  · obtain ⟨a, ha, he⟩ := hd x (Finset.mem_erase.mpr ⟨h, hx⟩)
    exact ⟨a, ha.trans (le_max_left ..), he⟩

/-- Split a cover ending at z at the first time it covered all sites other than z. -/
lemma last_blocks {A : Finset Site} {z : Site} (h0 : z ≠ 0) {r : ℕ} {y : Walk}
    (hl : y ∈ lastAt A z r) :
    ∃ t < r, ∃ w ∈ insert 0 (A.erase z), ∃ k < r, t + (k+1) = r ∧
      y ∈ endpoint (missing (A.erase z) z t) w t ∧ sh t y ∈ hit (z-w) (k+1) := by
  classical
  obtain ⟨hf, hp, hn⟩ := hl
  cases r with
  | zero => exact (h0 (by simpa [pos] using hp.symm)).elim
  | succ r =>
    have hb : doneBy (A.erase z) r y := by
      intro x hx
      obtain ⟨j, hj, he⟩ := hf.1 x (Finset.mem_of_mem_erase hx)
      exact ⟨j, by by_contra hh; have : j = r+1 := by omega
                   exact (Finset.ne_of_mem_erase hx) (he.symm.trans (this ▸ hp)), he⟩
    obtain ⟨t, ht, hft⟩ := exists_first hb
    have heq : t + (r-t+1) = r+1 := by omega
    refine ⟨t, by omega, pos y t, first_endpoint hft, r-t, by omega, heq,
      ⟨⟨hft, fun i hi ↦ hn i (by omega)⟩, rfl⟩, ?_, ?_⟩
    · rw [← heq, pos_shift] at hp
      exact eq_sub_of_add_eq' hp
    · intro i hi he
      apply hn (t+i) (by omega)
      rw [pos_shift, he, add_sub_cancel]

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {X : ℕ → Ω → Site}

noncomputable def pr (X : ℕ → Ω → Site) (E : Set Walk) : ℝ := (ℙ : Measure Ω).real (path X ⁻¹' E)

noncomputable def weight (X : ℕ → Ω → Site) (s : ℝ) (n : ℕ) (E : ℕ → Set Walk) : ℝ :=
  ∑ t ∈ Finset.range (n+1), s^t * pr X (E t)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma pr_nonneg (E : Set Walk) : 0 ≤ pr X E := measureReal_nonneg
lemma pr_le_one (E : Set Walk) : pr X E ≤ 1 := by
  unfold pr Measure.real
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (show (ℙ : Measure Ω) (path X ⁻¹' E) ≤ 1 from prob_le_one)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma meas_pre (hX : IsSimpleRandomWalkSteps X) {t : ℕ} {E : Set Walk} (h : Det t E) :
    MeasurableSet (path X ⁻¹' E) := by
  simpa only [sh_zero, Set.preimage] using det_meas hX h 0

lemma pr_cover {ι : Type*} {I : Finset ι} {D : ι → Set Walk} {E : Set Walk}
    (h : ∀ y ∈ E, ∃ i ∈ I, y ∈ D i) : pr X E ≤ ∑ i ∈ I, pr X (D i) := by
  apply le_trans (b := (ℙ : Measure Ω).real (⋃ i ∈ I, path X ⁻¹' D i))
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    simpa only [Set.mem_iUnion, exists_prop, Set.mem_preimage] using h _ hω
  · exact measureReal_biUnion_finset_le _ _

lemma weight_cover {ι : Type*} {I : Finset ι} {D : ι → Set Walk} {time : ι → ℕ}
    {E : ℕ → Set Walk} {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ r ≤ n, ∀ y ∈ E r, ∃ i ∈ I, time i = r ∧ y ∈ D i) :
    weight X s n E ≤ ∑ i ∈ I, s^(time i) * pr X (D i) := by
  classical
  calc
    _ ≤ ∑ r ∈ Finset.range (n+1), ∑ i ∈ I,
          if time i = r then s^(time i) * pr X (D i) else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      have hb : pr X (E r) ≤ ∑ i ∈ I.filter (fun i ↦ time i = r), pr X (D i) := by
        apply pr_cover
        intro y hy
        obtain ⟨i, hi, he, hd⟩ := h r (by simpa using hr) y hy
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩, hd⟩
      apply (mul_le_mul_of_nonneg_left hb (pow_nonneg hs r)).trans_eq
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with he <;> simp_all
    _ ≤ _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.sum_ite_eq]
      split_ifs <;> first | rfl | exact mul_nonneg (pow_nonneg hs _) (pr_nonneg _)

lemma endpoint_sum (hX : IsSimpleRandomWalkSteps X) {t : ℕ} {E : Set Walk} (hE : Det t E)
    (W : Finset Site) (hc : ∀ y ∈ E, pos y t ∈ W) :
    ∑ w ∈ W, pr X (endpoint E w t) = pr X E := by
  classical
  unfold pr
  rw [← measureReal_biUnion_finset]
  · congr 1
    ext ω
    simp only [Set.mem_iUnion, exists_prop, Set.mem_preimage]
    exact ⟨fun ⟨_, _, he⟩ ↦ he.1, fun he ↦ ⟨_, hc _ he, he, rfl⟩⟩
  · intro a ha b hb hab
    exact Set.disjoint_left.mpr fun _ h₁ h₂ ↦ hab (h₁.2.symm.trans h₂.2)
  · exact fun w _ ↦ meas_pre hX (det_endpoint hE w)

lemma hit_sum (z : Site) {n : ℕ} {s q : ℝ} (hs : 0 ≤ s) (hs' : s < 1)
    (hq : q ≤ 1 - ∑' k : ℕ, s^(k+1) * pr X (hit z (k+1))) :
    ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit z (k+1)) ≤ 1-q := by
  have hg := summable_geometric_of_lt_one hs hs'
  have hsm : Summable (fun k : ℕ ↦ s^(k+1) * pr X (hit z (k+1))) := by
    apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (pow_nonneg hs _) (pr_nonneg _))
      (f := fun k : ℕ ↦ s^k * s)
    · intro k
      rw [← pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hs _) (pr_le_one _)
    · exact hg.mul_right _
  exact (hsm.sum_le_tsum _ (fun _ _ ↦ mul_nonneg (pow_nonneg hs _) (pr_nonneg _))).trans
    (by linarith)

/-- The discounted weight of a final visit to the missing site is bounded by the
weight of eligible prefixes times the discounted hitting bound. -/
lemma last_bound (hX : IsSimpleRandomWalkSteps X) {A : Finset Site} {z : Site} (hz : z ≠ 0)
    {s q : ℝ} {n : ℕ} (hs : 0 ≤ s)
    (hh : ∀ w ∈ insert 0 (A.erase z),
      ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) ≤ 1-q) :
    weight X s n (lastAt A z) ≤ (1-q) * weight X s n (missing (A.erase z) z) := by
  classical
  let B := A.erase z
  let W := insert 0 B
  let R := Finset.range (n+1)
  let I := R ×ˢ (W ×ˢ Finset.range n)
  let D (i : ℕ × Site × ℕ) : Set Walk :=
    {y | y ∈ endpoint (missing B z i.1) i.2.1 i.1 ∧
      sh i.1 y ∈ hit (z-i.2.1) (i.2.2+1)}
  let time (i : ℕ × Site × ℕ) := i.1 + (i.2.2+1)
  have hcov : weight X s n (lastAt A z) ≤ ∑ i ∈ I, s^(time i) * pr X (D i) := by
    apply weight_cover hs
    intro r hr y hy
    obtain ⟨t, ht, w, hw, k, hk, he, hp⟩ := last_blocks hz hy
    refine ⟨(t,w,k), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_product.mpr ⟨hw, Finset.mem_range.mpr (hk.trans_le hr)⟩⟩, he, hp⟩
  refine hcov.trans ?_
  have hblock (t : ℕ) (w : Site) (k : ℕ) :
      pr X (D (t,w,k)) = pr X (endpoint (missing B z t) w t) * pr X (hit (z-w) (k+1)) := by
    unfold pr Measure.real
    rw [← ENNReal.toReal_mul]
    exact congrArg ENNReal.toReal (prob_block hX
      (det_endpoint (det_missing B z t) w) (det_hit (z-w) (k+1)))
  simp only [I, Finset.sum_product, time, hblock, pow_add]
  unfold weight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    _ = ∑ w ∈ W, (s^t * pr X (endpoint (missing B z t) w t)) *
          ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ ∑ w ∈ W, (s^t * pr X (endpoint (missing B z t) w t)) * (1-q) :=
      Finset.sum_le_sum fun w hw ↦ mul_le_mul_of_nonneg_left (hh w hw)
        (mul_nonneg (pow_nonneg hs _) (pr_nonneg _))
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, endpoint_sum hX (det_missing B z t) W
        (fun _ h ↦ first_endpoint h.1)]
      ring

/-- Covers ending at any other site also finish the erased set at the same time. -/
lemma split_bound (hX : IsSimpleRandomWalkSteps X) {A : Finset Site} {z : Site} (hz : z ∈ A)
    {s : ℝ} {n : ℕ} (hs : 0 ≤ s) :
    weight X s n (first A) + weight X s n (missing (A.erase z) z) ≤
      weight X s n (first (A.erase z)) + weight X s n (lastAt A z) := by
  unfold weight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  rw [← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
  let B := A.erase z
  have hsub : path X ⁻¹' first A t ⊆
      (path X ⁻¹' first B t \ path X ⁻¹' missing B z t) ∪ path X ⁻¹' lastAt A z t :=
    fun _ h ↦ first_split hz h
  have hm := (measureReal_mono (μ := (ℙ : Measure Ω)) hsub).trans (measureReal_union_le _ _)
  rw [measureReal_sdiff (μ := (ℙ : Measure Ω)) (s₁ := path X ⁻¹' first B t) (fun _ h ↦ h.1) (meas_pre hX (det_missing B z t))] at hm
  change pr X (first A t) ≤ pr X (first B t) - pr X (missing B z t) + pr X (lastAt A z t) at hm
  dsimp [B] at hm
  linarith

lemma sum_last (A : Finset Site) (ha : A.Nonempty) (h0 : 0 ∉ A) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    weight X s n (first A) ≤ ∑ z ∈ A, weight X s n (lastAt A z) := by
  unfold weight
  rw [Finset.sum_comm (s := A)]
  apply Finset.sum_le_sum
  intro t ht
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (pr_cover (fun _ h ↦ exists_last ha h0 h)) (pow_nonneg hs _)

/-- Sum the deletion inequalities over all possible last sites. -/
lemma recurrence (hX : IsSimpleRandomWalkSteps X) {A : Finset Site} (ha : A.Nonempty) (h0 : 0 ∉ A)
    {s q : ℝ} {n : ℕ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hh : ∀ z ∈ A, ∀ w ∈ insert 0 (A.erase z),
      ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) ≤ 1-q) :
    ((A.card : ℝ) * (1-q) + q) * weight X s n (first A) ≤
      (1-q) * ∑ z ∈ A, weight X s n (first (A.erase z)) := by
  let F := weight X s n (first A)
  let L := fun z ↦ weight X s n (lastAt A z)
  have hi (z : Site) (hz : z ∈ A) :
      (1-q)*F + q*L z ≤ (1-q)*weight X s n (first (A.erase z)) := by
    have hl := last_bound hX (fun he ↦ h0 (he ▸ hz)) hs (hh z hz)
    have hd := mul_le_mul_of_nonneg_left (split_bound (n := n) hX hz hs) (sub_nonneg.mpr hq')
    dsimp [F,L]
    linarith only [hl, hd]
  have hsum := Finset.sum_le_sum hi
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hL := mul_le_mul_of_nonneg_left (sum_last (X := X) A ha h0 hs n) hq
  change q * F ≤ q * ∑ z ∈ A, L z at hL
  change (_ * _ + _) * F ≤ _
  linarith only [hsum, hL]

lemma weight_empty (s : ℝ) (n : ℕ) : weight X s n (first ∅) = 1 := by
  classical
  have h (t : ℕ) : first ∅ t = if t = 0 then Set.univ else ∅ := by
    ext y
    by_cases ht : t = 0
    · simp [ht, first, doneBy]
    · simp [ht, first, doneBy]
      exact ⟨0, Nat.pos_of_ne_zero ht⟩
  simp [weight, h, pr, apply_ite, Finset.sum_ite_eq', Measure.real]

lemma scalar_step {k q f : ℝ} (hk : 1 ≤ k) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (h : (k*(1-q)+q)*f ≤ (1-q)*k*Real.exp (-q*Real.log k)) :
    f ≤ Real.exp (-q*Real.log (k+1)) := by
  let e := Real.exp (-q*Real.log k)
  have hk0 : 0 < k := by linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hc : 0 < k*(1-q)+q := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hq')]
  have hfac : (1-q)*k ≤ (k*(1-q)+q)*(1-q/k) := by
    field_simp [hk0.ne']
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg q)]
  have hf : f ≤ (1-q/k)*e := by
    apply le_of_mul_le_mul_left _ hc
    calc
      _ ≤ (1-q)*k*e := h
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfac he
  have hstep : Real.log (k+1) - Real.log k ≤ 1/k := by
    rw [← Real.log_div (by linarith) hk0.ne']
    have hl := Real.log_le_sub_one_of_pos (show 0 < (k+1)/k by positivity)
    convert hl using 1
    field_simp
    ring
  calc
    f ≤ (1-q/k)*e := hf
    _ ≤ Real.exp (-(q/k))*e := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) he
    _ = Real.exp (-(q/k) + -q*Real.log k) := (Real.exp_add ..).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hstep hq
      simp only [div_eq_mul_inv, one_mul] at hh ⊢
      linarith only [hh]

lemma weight_bound (hX : IsSimpleRandomWalkSteps X) {S : Finset Site} (h0 : 0 ∉ S)
    {s q : ℝ} {n : ℕ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hh : ∀ z ∈ S, ∀ w ∈ insert 0 S, w ≠ z →
      ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) ≤ 1-q) :
    weight X s n (first S) ≤ Real.exp (-q * Real.log ((S.card : ℝ)+1)) := by
  classical
  suffices H : ∀ A : Finset Site, A ⊆ S →
      weight X s n (first A) ≤ Real.exp (-q * Real.log ((A.card : ℝ)+1)) from H S (by rfl)
  intro A
  induction A using Finset.eraseInduction with
  | H A ih =>
    intro hA
    rcases A.eq_empty_or_nonempty with rfl | ha
    · simp [weight_empty]
    have h0A : 0 ∉ A := fun h ↦ h0 (hA h)
    have hrec := recurrence (n := n) hX ha h0A hs hq hq' (fun z hz w hw ↦ by
      apply hh z (hA hz) w
      · exact Finset.insert_subset_insert 0 (Finset.erase_subset _ _ |>.trans hA) hw
      · rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact fun he ↦ h0A (he ▸ hz)
        · exact Finset.ne_of_mem_erase hw')
    have he (z : Site) (hz : z ∈ A) :
        weight X s n (first (A.erase z)) ≤ Real.exp (-q*Real.log A.card) := by
      have h := ih z hz ((Finset.erase_subset _ _).trans hA)
      have hc : ((A.erase z).card : ℝ) + 1 = A.card := by
        exact_mod_cast Finset.card_erase_add_one hz
      rwa [hc] at h
    have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum he) (sub_nonneg.mpr hq')
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    apply scalar_step (by exact_mod_cast ha.card_pos) hq hq'
    simpa only [mul_assoc] using hrec.trans hsum

lemma remove_discount (A : Finset Site) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    s^n * pr X {y | doneBy A n y} ≤ weight X s n (first A) := by
  have hcov : pr X {y | doneBy A n y} ≤ ∑ t ∈ Finset.range (n+1), pr X (first A t) := by
    apply pr_cover
    intro y hy
    obtain ⟨t, ht, he⟩ := exists_first hy
    exact ⟨t, Finset.mem_range.mpr (by omega), he⟩
  apply (mul_le_mul_of_nonneg_left hcov (pow_nonneg hs _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs hs' (by simpa using ht)) (pr_nonneg _)

lemma discount_quarter (n : ℕ) (hn : 2 ≤ n) : 1/4 ≤ (1 - (1 : ℝ)/n)^n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hs : 0 < 1 - (1 : ℝ)/n := sub_pos.mpr ((div_lt_one hp).mpr (by linarith))
  have hj := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1/2 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 0 ≤ 2/(n : ℝ) by positivity) (sub_nonneg.mpr ((div_le_one hp).mpr hn')) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, mul_one] at hj
  rw [show 2/(n : ℝ)*(1/2) + (1-2/n) = 1-1/n by ring] at hj
  apply (Real.log_le_log_iff (by norm_num) (pow_pos hs _)).mp
  rw [show (1/4 : ℝ) = (1/2 : ℝ)^2 by norm_num, Real.log_pow, Real.log_pow]
  have hm := mul_le_mul_of_nonneg_left hj hp.le
  rw [← mul_assoc, show (n : ℝ) * (2/n) = 2 by field_simp] at hm
  exact_mod_cast hm

end OMA.DiscountedCover

open OMA.DiscountedCover

lemma h2_h2_solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1.H2 := by
  intro Ω _ _ X hX n hn S hS h0 q hq hq' hh
  let s := 1 - (1 : ℝ)/n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := sub_nonneg.mpr ((div_le_one hp).mpr (by linarith))
  have hs' : s < 1 := sub_lt_self _ (by positivity)
  have hW := weight_bound (n := n) hX h0 hs hq hq' (fun z hz w hw hne ↦
    hit_sum (X := X) (z-w) hs hs' (hh z hz w hw hne))
  let p := pr X {y | doneBy S n y}
  have hP : 1/4*p ≤ Real.exp (-q*Real.log ((S.card : ℝ)+1)) :=
    (mul_le_mul_of_nonneg_right (discount_quarter n hn) (pr_nonneg _)).trans
      ((remove_discount S n hs hs'.le).trans hW)
  have hc : 1 ≤ (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hlog := Real.log_nonneg hc
  have hlog' := Real.log_le_log (by linarith : 0 < (S.card : ℝ))
    (show (S.card : ℝ) ≤ S.card+1 by linarith)
  have hex : Real.exp (-q*Real.log ((S.card : ℝ)+1)) ≤
      Real.exp (-(q/2)*Real.log (S.card : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog' hq, mul_nonneg hq hlog]
  change p ≤ _
  linarith only [hP, hex]
end H2H2Sec

open MeasureTheory Filter OMA.R_Erdos1164_erdos_1164_R1 Erdos1165 Erdos1164 in
open scoped ProbabilityTheory Real ENNReal in
theorem OMA.solution : type_of% @Erdos1164.erdos_1164 := by
  intro Ω _ _ X hX ε hε
  have h1 : H1 := h1_solution
  have h2 : H2 := OMA.R_Erdos1164_erdos_1164_R1_H2_R1.main h2_h1_solution h2_h2_solution
  have hF : Measurable (fun ω i ↦ X i ω) := measurable_pi_iff.mpr hX.measurable
  letI : MeasureSpace (ℕ → ℤ × ℤ) := ⟨Measure.map (fun ω i ↦ X i ω) ℙ⟩
  haveI : IsProbabilityMeasure (ℙ : Measure (ℕ → ℤ × ℤ)) := by
    constructor
    change Measure.map (fun ω i ↦ X i ω) ℙ Set.univ = 1
    rw [Measure.map_apply hF MeasurableSet.univ]
    simp
  have hX' : IsSimpleRandomWalkSteps (fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i) := by
    refine ⟨fun k ↦ measurable_pi_apply k, ?_, ?_⟩
    · rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro S sets hs
      have key := hX.indep.measure_inter_preimage_eq_mul S hs
      have hm : ∀ T : Set (ℕ → ℤ × ℤ), MeasurableSet T →
          (ℙ : Measure (ℕ → ℤ × ℤ)) T = ℙ ((fun ω i ↦ X i ω) ⁻¹' T) := fun T hT ↦
        Measure.map_apply hF hT
      rw [hm _ (Finset.measurableSet_biInter S fun i hi ↦ measurable_pi_apply i (hs i hi))]
      rw [Finset.prod_congr rfl fun i hi ↦ hm _ (measurable_pi_apply i (hs i hi))]
      simp only [Set.preimage_iInter₂]
      exact key
    · intro k
      exact (Measure.map_map (measurable_pi_apply k) hF).trans (hX.isUniform k)
  have hmc : ∀ k, Measurable (fun (ω' : ℕ → ℤ × ℤ) ↦ ω' k) := fun k ↦ measurable_pi_apply k
  -- probabilities of covering-radius events agree on the two spaces
  have htr : ∀ (n : ℕ) (P : ℕ → Prop), ℙ {ω | P (coveringRadius X n ω)} =
      (ℙ : Measure (ℕ → ℤ × ℤ)) {ω' | P (coveringRadius (fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i) n ω')} := by
    intro n P
    change _ = Measure.map (fun ω i ↦ X i ω) ℙ _
    rw [Measure.map_apply hF (meas_event hmc n P)]
    rfl
  obtain ⟨c, hc, hlow⟩ := h1 hX' (ε / 2) (by positivity)
  obtain ⟨C, hup⟩ := h2 hX' (ε / 2) (by positivity)
  refine ⟨c, C, hc, ?_⟩
  filter_upwards [hlow, hup] with n hl hu
  set Y := fun i (ω' : ℕ → ℤ × ℤ) ↦ ω' i
  set A := {ω' : ℕ → ℤ × ℤ | c * Real.sqrt (Real.log n) ≤ Real.log (coveringRadius Y n ω')}
  set B := {ω' : ℕ → ℤ × ℤ | Real.log (coveringRadius Y n ω') ≤ C * Real.sqrt (Real.log n)}
  have hA : MeasurableSet A :=
    meas_event hmc n (fun k ↦ c * Real.sqrt (Real.log n) ≤ Real.log (k : ℝ))
  have hB : MeasurableSet B :=
    meas_event hmc n (fun k ↦ Real.log (k : ℝ) ≤ C * Real.sqrt (Real.log n))
  have e : ℙ {ω | c * Real.sqrt (Real.log n) ≤ Real.log (coveringRadius X n ω) ∧
      Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n)} =
      (ℙ : Measure (ℕ → ℤ × ℤ)) (A ∩ B) :=
    htr n (fun k ↦ c * Real.sqrt (Real.log n) ≤ Real.log (k : ℝ) ∧
      Real.log (k : ℝ) ≤ C * Real.sqrt (Real.log n))
  rw [e]
  have hAc : ((ℙ : Measure (ℕ → ℤ × ℤ)) Aᶜ).toReal ≤ ε / 2 := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
    linarith
  have hBc : ((ℙ : Measure (ℕ → ℤ × ℤ)) Bᶜ).toReal ≤ ε / 2 := by
    rw [prob_compl_eq_one_sub hB, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
    linarith
  have hu' : (ℙ : Measure (ℕ → ℤ × ℤ)) (A ∩ B)ᶜ ≤ ℙ Aᶜ + ℙ Bᶜ := by
    rw [Set.compl_inter]; exact measure_union_le _ _
  have hu'' : ((ℙ : Measure (ℕ → ℤ × ℤ)) (A ∩ B)ᶜ).toReal ≤
      ((ℙ : Measure (ℕ → ℤ × ℤ)) Aᶜ).toReal + ((ℙ : Measure (ℕ → ℤ × ℤ)) Bᶜ).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hu'
  rw [prob_compl_eq_one_sub (hA.inter hB), ENNReal.toReal_sub_of_le prob_le_one
    ENNReal.one_ne_top, ENNReal.toReal_one] at hu''
  linarith

