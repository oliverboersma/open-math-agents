import FormalConjectures.Paper.WeakTiling

/-!
An endpoint-balance reduction for WeakTiling.problem_4_2.

The signed semigroup support theorem of Kolountzakis, Lev and Matolcsi
(Geometric implications of weak tiling, Theorem 3.7) motivates the lattice model
in H1. H2 asks for an integral complement to a fractional tiling of the integers.
-/

open MeasureTheory Set ENNReal Filter Topology

namespace OMA.R_WeakTiling_problem_4_2_R1

private def ordered {α : Type*} [LT α] {n : ℕ} (a b : Fin n → α) : Prop :=
  (∀ i, a i < b i) ∧ (∀ i j, i < j → b i < a j)

private def intervals {n : ℕ} (a b : Fin n → ℝ) : Set ℝ :=
  ⋃ i, Ioo (a i) (b i)

private def cells {n : ℕ} (a b : Fin n → ℤ) : Finset ℤ :=
  Finset.univ.biUnion (fun i ↦ Finset.Ico (a i) (b i))

private def Fractional (A : Finset ℤ) : Prop :=
  ∃ w : ℤ → ℝ≥0∞, w 0 = 1 ∧ ∀ j, ∑ c ∈ A, w (j - c) = 1

private theorem mem_cells {n : ℕ} (a b : Fin n → ℤ) (c : ℤ) :
    c ∈ cells a b ↔ ∃ i, a i ≤ c ∧ c < b i := by
  classical
  simp [cells]

private theorem jump_cover {n : ℕ} (u v : Fin n → ℤ)
    (hord : ordered u v) (w : ℤ → ℝ≥0∞) (hfin : ∀ m, w m ≠ ∞)
    (hbal : ∀ m, ∑ i, w (m - u i) = ∑ i, w (m - v i))
    (z : ℤ) (hz : ∑ c ∈ cells u v, w (z - c) = 1) :
    ∀ m : ℤ, ∑ c ∈ cells u v, w (m - c) = 1 := by
  let F (m : ℤ) := ∑ c ∈ cells u v, w (m - c)
  have hsplit (m : ℤ) : F m = ∑ i, ∑ c ∈ Finset.Ico (u i) (v i), w (m - c) := by
    apply Finset.sum_biUnion
    intro i _ j _ hij
    change Disjoint (Finset.Ico (u i) (v i)) (Finset.Ico (u j) (v j))
    rw [Finset.disjoint_left]
    intro c hci hcj
    have hi := Finset.mem_Ico.mp hci
    have hj := Finset.mem_Ico.mp hcj
    rcases lt_or_gt_of_ne hij with h | h
    · have hf := hord.2 i j h
      omega
    · have hf := hord.2 j i h
      omega
  have hstep (m : ℤ) : F (m + 1) = F m := by
    have hlocal (i : Fin n) :
        (∑ c ∈ Finset.Ico (u i) (v i), w (m+1-c)) + w (m+1-v i) =
          (∑ c ∈ Finset.Ico (u i) (v i), w (m-c)) + w (m+1-u i) := by
      let f : ℤ → ℝ≥0∞ := fun c ↦ w (m+1-c)
      have hshift : (∑ c ∈ Finset.Ico (u i) (v i), w (m-c)) =
          ∑ c ∈ Finset.Ico (u i + 1) (v i + 1), f c := by
        rw [← Finset.sum_Ico_add' f (u i) (v i) 1]
        apply Finset.sum_congr rfl
        intro c _
        dsimp [f]
        congr 1
        omega
      have hui := hord.1 i
      rw [hshift, ← Finset.sum_Ico_add_eq_sum_Ico_add_one (f := f) (by omega : u i + 1 ≤ v i)]
      have hbase : (∑ c ∈ Finset.Ico (u i) (v i), f c) =
          f (u i) + ∑ c ∈ Finset.Ico (u i + 1) (v i), f c := by
        rw [← Finset.insert_Ico_succ_left_eq_Ico (hord.1 i)]
        simp [Order.succ_eq_add_one, Finset.sum_insert]
      change (∑ c ∈ Finset.Ico (u i) (v i), f c) + f (v i) =
        ((∑ c ∈ Finset.Ico (u i+1) (v i), f c) + f (v i)) + f (u i)
      rw [hbase]
      ac_rfl
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ hlocal i)
    simp only [Finset.sum_add_distrib, ← hsplit, ← hbal (m+1)] at h
    exact (ENNReal.add_left_inj (ENNReal.sum_ne_top.mpr fun _ _ ↦ hfin _)).mp h
  have hall (m : ℤ) : F (z + m) = 1 := by
    induction m using Int.induction_on with
    | zero => simpa [F] using hz
    | succ m hm => rwa [← add_assoc, hstep]
    | pred m hm =>
      have h := hstep (z + (- (m : ℤ) - 1))
      rw [show z + (-(m : ℤ) - 1) + 1 = z + (-(m : ℤ)) by omega] at h
      exact h.symm.trans hm
  intro m
  have hm := hall (m - z)
  rw [show z + (m - z) = m by omega] at hm
  exact hm

private noncomputable def pushW {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)
    (w : G → ℝ≥0∞) (j : ℤ) : ℝ≥0∞ :=
  ∑' p : G, if φ p = j then w p else 0

private theorem push_balance {G : Type*} [AddCommGroup G] {n : ℕ}
    (a b : Fin n → G) (w : G → ℝ≥0∞) (φ : G →+ ℤ)
    (hbal : ∀ p, ∑ i, w (p - a i) = ∑ i, w (p - b i)) (j : ℤ) :
    ∑ i, pushW φ w (j - φ (a i)) = ∑ i, pushW φ w (j - φ (b i)) := by
  classical
  have hform (u : Fin n → G) :
      ∑ i, pushW φ w (j - φ (u i)) =
        ∑' p : G, if φ p = j then ∑ i, w (p - u i) else 0 := by
    have hshift (i : Fin n) :
        pushW φ w (j - φ (u i)) = ∑' p : G, if φ p = j then w (p - u i) else 0 := by
      unfold pushW
      rw [← (Equiv.subRight (u i)).tsum_eq]
      simp [map_sub, sub_left_inj]
    simp only [hshift, ← tsum_fintype (L := SummationFilter.unconditional _)]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun p ↦ ?_
    by_cases hp : φ p = j <;> simp [hp]
  rw [hform a, hform b]
  exact tsum_congr fun p ↦ by rw [hbal]

private theorem pushed_cover {G : Type*} [AddCommGroup G] {n : ℕ}
    (a b : Fin n → G) (w : G → ℝ≥0∞) (φ : G →+ ℤ) (z : G)
    (hord : ordered (φ ∘ a) (φ ∘ b))
    (hfin : ∀ j, pushW φ w j ≠ ∞)
    (hbal : ∀ p, ∑ i, w (p - a i) = ∑ i, w (p - b i)) (h₀ : w 0 = 1)
    (hker : ∀ p, w p ≠ 0 → φ p = 0 → p = 0)
    (hz : ∃ i, φ (a i) ≤ φ z ∧ φ z < φ (b i))
    (hunique : ∀ p, w p ≠ 0 → (∃ i, φ (a i) + φ p ≤ φ z ∧ φ z < φ (b i) + φ p) → p = 0) :
    Fractional (cells (φ ∘ a) (φ ∘ b)) := by
  have hpush₀ : pushW φ w 0 = 1 := by
    rw [pushW, tsum_eq_single 0]
    · simpa using h₀
    · intro p hp
      split
      · exact not_not.mp fun hw ↦ hp (hker p hw ‹φ p = 0›)
      · rfl
  refine ⟨pushW φ w, hpush₀, jump_cover _ _ hord _ hfin (push_balance a b w φ hbal) (φ z) ?_⟩
  rw [Finset.sum_eq_single (φ z)]
  · simpa
  · intro c hc hne
    rw [pushW, ENNReal.tsum_eq_zero]
    intro p
    split
    · by_contra hw
      have hcod : φ p = φ z - c := ‹φ p = φ z - c›
      obtain ⟨i, ha, hb⟩ := (mem_cells _ _ _).mp hc
      have hp : p = 0 := hunique p hw ⟨i, by dsimp at ha; omega, by dsimp at hb; omega⟩
      subst p
      simp at hcod
      omega
    · rfl
  · intro h
    exact (h ((mem_cells _ _ _).mpr hz)).elim

private abbrev Codes (d : ℕ) := Fin d → ℤ

private def decode {d : ℕ} (r : Fin d → ℝ) (p : Codes d) : ℝ :=
  ∑ i, (p i : ℝ) * r i

private def codeSize {d : ℕ} (p : Codes d) : ℝ :=
  ∑ i, |(p i : ℝ)|

/-- A normalized balance of endpoint weights on a finite-rank lattice. -/
private def LatticeModel {n : ℕ} (a b : Fin n → ℝ) : Prop :=
  ∃ (d : ℕ) (r : Fin d → ℝ) (u v : Fin n → Codes d) (z : Codes d)
    (w : Codes d → ℝ≥0∞) (D : ℝ),
    0 < D ∧
    (∀ i, decode r (u i) = a i) ∧ (∀ i, decode r (v i) = b i) ∧
    (∀ p, w p ≠ ∞) ∧ w 0 = 1 ∧
    (∀ p, w p ≠ 0 → codeSize p ≤ D * |decode r p|) ∧
    (∀ p, ∑ i, w (p - u i) = ∑ i, w (p - v i)) ∧
    (∃ i, a i < decode r z ∧ decode r z < b i) ∧
    (∀ p, p ≠ 0 → w p ≠ 0 → ∀ i,
      decode r z < a i + decode r p ∨ b i + decode r p < decode r z)

private def encode {d : ℕ} (r : Fin d → ℤ) : Codes d →+ ℤ where
  toFun p := ∑ i, p i * r i
  map_zero' := by simp
  map_add' p q := by simp [add_mul, Finset.sum_add_distrib]

private theorem grid_encode {d : ℕ} (v : Fin d → ℤ) (θ : ℝ) (p : Codes d) :
    decode (fun i ↦ θ * (v i : ℝ)) p = θ * (encode v p : ℝ) := by
  simp only [decode, encode, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem abs_le_codeSize {d : ℕ} (p : Codes d) (i : Fin d) :
    |(p i : ℝ)| ≤ codeSize p :=
  Finset.single_le_sum (fun j _ ↦ abs_nonneg (p j : ℝ)) (Finset.mem_univ i)

private theorem code_bounded_finite (d : ℕ) (R : ℝ) :
    ({p : Codes d | codeSize p ≤ R} : Set (Codes d)).Finite := by
  have h := Set.Finite.pi (ι := Fin d) (fun _ ↦ Set.finite_Icc (-⌈R⌉) ⌈R⌉)
  refine h.subset ?_
  intro p hp i _
  have habs : |(p i : ℝ)| ≤ R := (abs_le_codeSize p i).trans hp
  have hr := Int.le_ceil R
  change -⌈R⌉ ≤ p i ∧ p i ≤ ⌈R⌉
  have h₁ : (-⌈R⌉ : ℤ) ≤ p i := by
    have h' : (- (⌈R⌉ : ℤ) : ℝ) ≤ (p i : ℝ) := by
      linarith [(abs_le.mp habs).1]
    exact_mod_cast h'
  have h₂ : (p i : ℝ) ≤ (⌈R⌉ : ℤ) := (abs_le.mp habs).2.trans hr
  exact ⟨h₁, Int.cast_le.mp h₂⟩

private theorem decode_error {d : ℕ} (r s : Fin d → ℝ) (p : Codes d) (ε : ℝ)
    (hε : ∀ i, |s i - r i| ≤ ε) :
    |decode s p - decode r p| ≤ ε * codeSize p := by
  simp only [decode, ← Finset.sum_sub_distrib, ← mul_sub, codeSize, Finset.mul_sum]
  calc
    _ ≤ ∑ i, |(p i : ℝ) * (s i - r i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
      rw [abs_mul, mul_comm ε]
      exact mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _)

private theorem perturbed_support_bound {d : ℕ} {r s : Fin d → ℝ} {D : ℝ}
    (hD : 0 < D) (hnear : ∀ i, |s i - r i| ≤ 1 / (2 * D))
    (p : Codes d) (hp : codeSize p ≤ D * |decode r p|) :
    codeSize p ≤ (2 * D) * |decode s p| := by
  have he := decode_error r s p _ hnear
  have htriangle : |decode r p| ≤ |decode s p| + |decode s p - decode r p| := by
    calc
      |decode r p| = |decode s p - (decode s p - decode r p)| := by
        congr 1
        ring
      _ ≤ _ := abs_sub _ _
  have he' := mul_le_mul_of_nonneg_left he hD.le
  have ht := mul_le_mul_of_nonneg_left htriangle hD.le
  have heval : D * (1 / (2 * D) * codeSize p) = codeSize p / 2 := by
    field_simp [hD.ne']
  rw [heval] at he'
  linarith

private theorem code_zero {d : ℕ} (p : Codes d) (hp : codeSize p ≤ 0) : p = 0 := by
  funext i
  have h := (abs_le_codeSize p i).trans hp
  have hh : (p i : ℝ) = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  exact_mod_cast hh

private theorem stable_grid {n d : ℕ} (r : Fin d → ℝ) (u v : Fin n → Codes d)
    (z : Codes d) (w : Codes d → ℝ≥0∞) (D : ℝ) (hD : 0 < D)
    (hord : ordered (fun i ↦ decode r (u i)) (fun i ↦ decode r (v i)))
    (hfin : ∀ p, w p ≠ ∞) (h₀ : w 0 = 1)
    (hsupport : ∀ p, w p ≠ 0 → codeSize p ≤ D * |decode r p|)
    (hbal : ∀ p, ∑ i, w (p - u i) = ∑ i, w (p - v i))
    (hanchor : ∃ i, decode r (u i) < decode r z ∧ decode r z < decode r (v i))
    (havoid : ∀ p, p ≠ 0 → w p ≠ 0 → ∀ i,
        decode r z < decode r (u i) + decode r p ∨ decode r (v i) + decode r p < decode r z)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (θ : ℝ) (U V : Fin n → ℤ), 0 < θ ∧ ordered U V ∧ Fractional (cells U V) ∧
      (∀ i, |θ * (U i : ℝ) - decode r (u i)| < ε) ∧
      (∀ i, |θ * (V i : ℝ) - decode r (v i)| < ε) := by
  classical
  let θ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  let grid : ℕ → Fin d → ℤ := fun m i ↦ ⌊((m : ℝ) + 1) * r i⌋
  let s : ℕ → Fin d → ℝ := fun m i ↦ θ m * (grid m i : ℝ)
  have hθ (m : ℕ) : 0 < θ m := by dsimp [θ]; positivity
  have hθt : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hst (i : Fin d) : Tendsto (fun m ↦ s m i) atTop (𝓝 (r i)) := by
    rw [Metric.tendsto_atTop] at hθt ⊢
    intro l hl
    obtain ⟨N, hN⟩ := hθt l hl
    refine ⟨N, fun m hm ↦ ?_⟩
    have hsmall := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_pos (hθ m)] at hsmall
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    have hp : s m i ≤ r i := by
      dsimp [s, θ, grid]
      rw [one_div_mul_eq_div, div_le_iff₀ hmpos, mul_comm]
      exact Int.floor_le _
    have hq : r i - s m i < θ m := by
      have h := (lt_div_iff₀ hmpos).mpr (show r i * ((m : ℝ) + 1) <
          (grid m i : ℝ) + 1 from by
        simpa only [grid, mul_comm] using Int.lt_floor_add_one (((m : ℝ) + 1) * r i))
      rw [add_div, ← one_div_mul_eq_div] at h
      change r i < s m i + θ m at h
      linarith
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hp)]
    linarith
  have hdec (p : Codes d) : Tendsto (fun m ↦ decode (s m) p) atTop (𝓝 (decode r p)) := by
    exact tendsto_finsetSum _ fun i _ ↦ tendsto_const_nhds.mul (hst i)
  let R : ℝ := 2 + |decode r z| + ∑ i, (|decode r (u i)| + |decode r (v i)|)
  have hRu (i : Fin n) : 2 + |decode r z| + |decode r (u i)| ≤ R := by
    have hh := Finset.single_le_sum
      (f := fun j ↦ |decode r (u j)| + |decode r (v j)|)
      (fun j _ ↦ by positivity) (Finset.mem_univ i)
    dsimp [R]
    linarith [abs_nonneg (decode r (v i))]
  have hRv (i : Fin n) : 2 + |decode r z| + |decode r (v i)| ≤ R := by
    have hh := Finset.single_le_sum
      (f := fun j ↦ |decode r (u j)| + |decode r (v j)|)
      (fun j _ ↦ by positivity) (Finset.mem_univ i)
    dsimp [R]
    linarith [abs_nonneg (decode r (u i))]
  let K : Set (Codes d) := {p | codeSize p ≤ (2 * D) * R}
  have hK : K.Finite := code_bounded_finite _ _
  have hnear : ∀ᶠ m in atTop, ∀ i, |s m i - r i| ≤ 1 / (2 * D) := by
    rw [eventually_all]
    intro i
    have h := (Metric.tendsto_nhds.mp (hst i)) _ (by positivity : 0 < 1 / (2 * D))
    exact h.mono fun m hm ↦ le_of_lt (by simpa only [Real.dist_eq] using hm)
  have hclos (p : Codes d) : ∀ᶠ m in atTop, |decode (s m) p - decode r p| < min ε 1 :=
    (Metric.tendsto_nhds.mp (hdec p) _ (lt_min hε zero_lt_one)).mono
      fun _ h ↦ by simpa only [Real.dist_eq] using h
  have hclosUV : ∀ᶠ m in atTop,
      (∀ i, |decode (s m) (u i) - decode r (u i)| < min ε 1) ∧
      (∀ i, |decode (s m) (v i) - decode r (v i)| < min ε 1) :=
    ((eventually_all).2 fun i ↦ hclos (u i)).and ((eventually_all).2 fun i ↦ hclos (v i))
  have hord' : ∀ᶠ m in atTop,
      ordered (fun i ↦ decode (s m) (u i)) (fun i ↦ decode (s m) (v i)) := by
    apply Eventually.and
    · exact (eventually_all).2 fun i ↦ (hdec (u i)).eventually_lt (hdec (v i)) (hord.1 i)
    · simp only [eventually_all]
      intro i j hij
      exact (hdec (v i)).eventually_lt (hdec (u j)) (hord.2 i j hij)
  obtain ⟨i₀, hi₀, hi₁⟩ := hanchor
  have hanchor' : ∀ᶠ m in atTop,
      decode (s m) (u i₀) < decode (s m) z ∧ decode (s m) z < decode (s m) (v i₀) :=
    ((hdec (u i₀)).eventually_lt (hdec z) hi₀).and ((hdec z).eventually_lt (hdec (v i₀)) hi₁)
  have havoid' : ∀ᶠ m in atTop, ∀ p ∈ K, p ≠ 0 → w p ≠ 0 → ∀ i,
      decode (s m) z < decode (s m) (u i) + decode (s m) p ∨
        decode (s m) (v i) + decode (s m) p < decode (s m) z := by
    rw [eventually_all_finite hK]
    intro p hp
    simp only [eventually_all]
    intro hp₀ hpw i
    rcases havoid p hp₀ hpw i with h | h
    · exact ((hdec z).eventually_lt ((hdec (u i)).add (hdec p)) h).mono fun _ h ↦ Or.inl h
    · exact (((hdec (v i)).add (hdec p)).eventually_lt (hdec z) h).mono fun _ h ↦ Or.inr h
  have hall := hnear.and (hclosUV.and ((hclos z).and (hord'.and (hanchor'.and havoid'))))
  obtain ⟨m, hmnear, ⟨hmu, hmv⟩, hmz, hmord, ⟨hma₀, hma₁⟩, hmavoid⟩ := hall.exists
  let φ := encode (grid m)
  have hφ (p : Codes d) : decode (s m) p = θ m * (φ p : ℝ) := grid_encode _ _ p
  have hbφ (p : Codes d) (hp : w p ≠ 0) :
      codeSize p ≤ (2 * D) * |decode (s m) p| :=
    perturbed_support_bound hD hmnear p (hsupport p hp)
  have hker (p : Codes d) (hp : w p ≠ 0) (h : φ p = 0) : p = 0 := by
    apply code_zero
    simpa [hφ, h] using hbφ p hp
  have hfinφ (j : ℤ) : pushW φ w j ≠ ∞ := by
    let f := (code_bounded_finite d ((2 * D) * |θ m * (j : ℝ)|)).toFinset
    unfold pushW
    rw [tsum_eq_sum (s := f)]
    · exact ENNReal.sum_ne_top.mpr fun p _ ↦ by
        split <;> simp_all
    · intro p hp
      by_cases hc : φ p = j
      · simp only [if_pos hc]
        by_contra hs
        apply hp
        simpa [f, hφ, hc] using hbφ p hs
      · simp [hc]
  have hr : ordered (φ ∘ u) (φ ∘ v) := by
    have hcast {p q : Codes d} (h : decode (s m) p < decode (s m) q) : φ p < φ q := by
      rw [hφ, hφ] at h
      exact Int.cast_lt.mp ((mul_lt_mul_iff_right₀ (hθ m)).mp h)
    exact ⟨fun i ↦ hcast (hmord.1 i), fun i j h ↦ hcast (hmord.2 i j h)⟩
  have hz : ∃ i, φ (u i) ≤ φ z ∧ φ z < φ (v i) := by
    rw [hφ, hφ] at hma₀ hma₁
    exact ⟨i₀, (Int.cast_lt.mp ((mul_lt_mul_iff_right₀ (hθ m)).mp hma₀)).le,
      Int.cast_lt.mp ((mul_lt_mul_iff_right₀ (hθ m)).mp hma₁)⟩
  have hunique (p : Codes d) (hp : w p ≠ 0)
      (h : ∃ i, φ (u i) + φ p ≤ φ z ∧ φ z < φ (v i) + φ p) : p = 0 := by
    by_contra hp₀
    obtain ⟨i, h₁, h₂⟩ := h
    have hl : decode (s m) (u i) + decode (s m) p ≤ decode (s m) z := by
      simp only [hφ, ← mul_add, ← Int.cast_add]
      exact mul_le_mul_of_nonneg_left (Int.cast_le.mpr h₁) (hθ m).le
    have hu : decode (s m) z < decode (s m) (v i) + decode (s m) p := by
      simp only [hφ, ← mul_add, ← Int.cast_add]
      exact mul_lt_mul_of_pos_left (Int.cast_lt.mpr h₂) (hθ m)
    have hup := abs_lt.mp ((hmu i).trans_le (min_le_right ε 1))
    have hvp := abs_lt.mp ((hmv i).trans_le (min_le_right ε 1))
    have hzp := abs_lt.mp (hmz.trans_le (min_le_right ε 1))
    have hb : |decode (s m) p| ≤ R := by
      apply abs_le.mpr
      constructor
      · linarith [hRv i, neg_abs_le (decode r z), le_abs_self (decode r (v i))]
      · linarith [hRu i, le_abs_self (decode r z), neg_abs_le (decode r (u i))]
    have hpK : p ∈ K := (hbφ p hp).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
    rcases hmavoid p hpK hp₀ hp i with h | h <;> linarith
  refine ⟨θ m, φ ∘ u, φ ∘ v, hθ m, hr,
    pushed_cover u v w φ z hr hfinφ hbal h₀ hker hz hunique, ?_, ?_⟩
  · intro i
    rw [Function.comp_apply, ← hφ]
    exact (hmu i).trans_le (min_le_left ε 1)
  · intro i
    rw [Function.comp_apply, ← hφ]
    exact (hmv i).trans_le (min_le_left ε 1)

private theorem lattice_approx {n : ℕ} {a b : Fin n → ℝ}
    (hord : ordered a b) (h : LatticeModel a b) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (θ : ℝ) (U V : Fin n → ℤ), 0 < θ ∧ ordered U V ∧ Fractional (cells U V) ∧
        (∀ i, |θ * (U i : ℝ) - a i| < ε) ∧
        (∀ i, |θ * (V i : ℝ) - b i| < ε) := by
  obtain ⟨d, r, u, v, z, w, D, hD, hua, hvb, hfin, h₀, hs, hb, hanchor, havoid⟩ := h
  have hₐ : (fun i ↦ decode r (u i)) = a := funext hua
  have hᵦ : (fun i ↦ decode r (v i)) = b := funext hvb
  rw [← hₐ, ← hᵦ] at hord hanchor havoid ⊢
  exact stable_grid r u v z w D hD hord hfin h₀ hs hb hanchor havoid

private def hit {n : ℕ} (a b : Fin n → ℝ) (x t : ℝ) : Prop :=
  ∃ i, a i + t < x ∧ x < b i + t

private def closedHit {n : ℕ} (a b : Fin n → ℝ) (x t : ℝ) : Prop :=
  ∃ i, a i + t ≤ x ∧ x ≤ b i + t

private def packed {n : ℕ} (a b : Fin n → ℝ) (S : Set ℝ) : Prop :=
  ∀ ⦃x s t : ℝ⦄, s ∈ S → t ∈ S → hit a b x s → hit a b x t → s = t

private theorem scale_hitting {n : ℕ} (r : ℝ) (hr : 0 < r)
    (u v : Fin n → ℤ) (t : ℤ) (x : ℝ) :
    (hit (fun i ↦ r * (u i : ℝ)) (fun i ↦ r * (v i : ℝ)) x (r * (t : ℝ)) →
      ⌊x / r⌋ - t ∈ cells u v) ∧
    (⌊x / r⌋ - t ∈ cells u v →
      closedHit (fun i ↦ r * (u i : ℝ)) (fun i ↦ r * (v i : ℝ)) x (r * (t : ℝ))) := by
  rw [mem_cells]
  constructor
  · rintro ⟨i, hlo, hhi⟩
    refine ⟨i, ?_, ?_⟩
    · have hh : ((u i + t : ℤ) : ℝ) ≤ x / r := by
        apply (le_div_iff₀ hr).mpr
        push_cast
        linarith
      have hh' := Int.le_floor.mpr hh
      omega
    · have hh : x / r < ((v i + t : ℤ) : ℝ) := by
        apply (div_lt_iff₀ hr).mpr
        push_cast
        linarith
      have hh' := Int.floor_lt.mpr hh
      omega
  · rintro ⟨i, hlo, hhi⟩
    refine ⟨i, ?_, ?_⟩
    · have hh : ((u i + t : ℤ) : ℝ) ≤ x / r :=
        le_trans (Int.cast_le.mpr (by omega)) (Int.floor_le _)
      have hh' := (le_div_iff₀ hr).mp hh
      push_cast at hh'
      linarith
    · have hb : ((⌊x / r⌋ + 1 : ℤ) : ℝ) ≤ ((v i + t : ℤ) : ℝ) :=
        Int.cast_le.mpr (by omega)
      have hh := Int.lt_floor_add_one (x / r)
      push_cast at hb
      have hh' := (div_le_iff₀ hr).mp (show x / r ≤ (v i : ℝ) + t by linarith)
      linarith

private theorem scale_cover {n : ℕ} (r : ℝ) (hr : 0 < r) (u v : Fin n → ℤ)
    (C : Set ℤ) (hC₀ : 0 ∈ C) (hC : ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j - t ∈ cells u v) :
    ∃ S : Set ℝ, 0 ∈ S ∧ packed (fun i ↦ r * (u i : ℝ)) (fun i ↦ r * (v i : ℝ)) S ∧
      ∀ x, ∃ t ∈ S, closedHit (fun i ↦ r * (u i : ℝ)) (fun i ↦ r * (v i : ℝ)) x t := by
  let S := (fun t : ℤ ↦ r * (t : ℝ)) '' C
  refine ⟨S, ⟨0, hC₀, by simp⟩, ?_, ?_⟩
  · rintro x _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ hxs hxt
    obtain ⟨z, _, hz⟩ := hC ⌊x / r⌋
    have heq : s = t := (hz s ⟨hs, (scale_hitting r hr u v s x).1 hxs⟩).trans
      (hz t ⟨ht, (scale_hitting r hr u v t x).1 hxt⟩).symm
    rw [heq]
  · intro x
    obtain ⟨t, ht, _⟩ := hC ⌊x / r⌋
    exact ⟨r * (t : ℝ), ⟨t, ht.1, rfl⟩, (scale_hitting r hr u v t x).2 ht.2⟩

private theorem approximation_cover {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (h₂ : ∀ A : Finset ℤ, A.Nonempty → Fractional A →
      ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j - t ∈ A)
    (h₁ : ∀ ε : ℝ, 0 < ε →
        ∃ (r : ℝ) (u v : Fin n → ℤ), 0 < r ∧ ordered u v ∧ Fractional (cells u v) ∧
          (∀ i, |r * (u i : ℝ) - a i| < ε) ∧
          (∀ i, |r * (v i : ℝ) - b i| < ε)) :
    ∃ S : Set ℝ, 0 ∈ S ∧ packed a b S ∧ ∀ x, ∃ t ∈ S, closedHit a b x t := by
  classical
  let e : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hepos (m : ℕ) : 0 < e m := by dsimp [e]; positivity
  have hele (m : ℕ) : e m ≤ 1 := by
    dsimp [e]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  choose r u v hr huv hfrac hA hB using fun m ↦ h₁ (e m) (hepos m)
  let α : ℕ → Fin n → ℝ := fun m i ↦ r m * (u m i : ℝ)
  let β : ℕ → Fin n → ℝ := fun m i ↦ r m * (v m i : ℝ)
  have hnonempty (m : ℕ) : (cells (u m) (v m)).Nonempty := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨u m i, (mem_cells (u m) (v m) _).mpr ⟨i, le_rfl, (huv m).1 i⟩⟩
  choose C hC₀ hC using fun m ↦ h₂ _ (hnonempty m) (hfrac m)
  choose S hS₀ hpack hcover using fun m ↦ scale_cover (r m) (hr m) (u m) (v m) (C m)
    (hC₀ m) (hC m)
  choose t ht hxt using hcover
  let w : ℕ → Option ℝ → ℝ := fun m o ↦ o.elim 0 (t m)
  have hw (m : ℕ) (o : Option ℝ) : w m o ∈ S m := by
    cases o with
    | none => exact hS₀ m
    | some x => exact ht m x
  let M : ℝ := 1 + ∑ i : Fin n, (|a i| + |b i|)
  have hMa (i : Fin n) : |a i| + 1 ≤ M := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun j ↦ |a j| + |b j|) (fun j _ ↦ by positivity) (Finset.mem_univ i)
    dsimp [M]
    linarith [abs_nonneg (b i)]
  have hMb (i : Fin n) : |b i| + 1 ≤ M := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun j ↦ |a j| + |b j|) (fun j _ ↦ by positivity) (Finset.mem_univ i)
    dsimp [M]
    linarith [abs_nonneg (a i)]
  have hbound (x : ℝ) (m : ℕ) : t m x ∈ Icc (x-M) (x+M) := by
    obtain ⟨i, hlo, hhi⟩ := hxt m x
    change α m i + t m x ≤ x at hlo
    change x ≤ β m i + t m x at hhi
    have ha := abs_lt.mp (hA m i)
    have hb := abs_lt.mp (hB m i)
    change -(e m) < α m i - a i ∧ α m i - a i < e m at ha
    change -(e m) < β m i - b i ∧ β m i - b i < e m at hb
    exact ⟨by linarith [hMb i, le_abs_self (b i), hele m],
      by linarith [hMa i, neg_abs_le (a i), hele m]⟩
  let U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hex (o : Option ℝ) : ∃ v : ℝ, Tendsto (fun m ↦ w m o) U (𝓝 v) := by
    cases o with
    | none => exact ⟨0, tendsto_const_nhds⟩
    | some x =>
      have hmem : Icc (x-M) (x+M) ∈ Ultrafilter.map (fun m ↦ t m x) U := by
        change Icc (x-M) (x+M) ∈ (↑(Ultrafilter.map (fun m ↦ t m x) U) : Filter ℝ)
        rw [Ultrafilter.coe_map, Filter.mem_map]
        exact Filter.Eventually.of_forall (hbound x)
      obtain ⟨v, _, hv⟩ := isCompact_Icc.ultrafilter_le_nhds' _ hmem
      exact ⟨v, by simpa only [Ultrafilter.coe_map, Filter.Tendsto, w, Option.elim_some] using hv⟩
  choose τ hτ using hex
  have hτ₀ : τ none = 0 :=
    tendsto_nhds_unique (hτ none) (tendsto_const_nhds (x := (0 : ℝ)))
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hα (i : Fin n) : Tendsto (fun m ↦ α m i) U (𝓝 (a i)) := by
    apply Tendsto.mono_left _ hU
    rw [Metric.tendsto_atTop] at he ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := he ε hε
    refine ⟨N, fun m hm ↦ ?_⟩
    have hh := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_pos (hepos m)] at hh
    rw [Real.dist_eq]
    exact (hA m i).trans hh
  have hβ (i : Fin n) : Tendsto (fun m ↦ β m i) U (𝓝 (b i)) := by
    apply Tendsto.mono_left _ hU
    rw [Metric.tendsto_atTop] at he ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := he ε hε
    refine ⟨N, fun m hm ↦ ?_⟩
    have hh := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_pos (hepos m)] at hh
    rw [Real.dist_eq]
    exact (hB m i).trans hh
  refine ⟨Set.range τ, ⟨none, hτ₀⟩, ?_, ?_⟩
  · rintro x _ _ ⟨o, rfl⟩ ⟨p, rfl⟩ ⟨i, hi₁, hi₂⟩ ⟨j, hj₁, hj₂⟩
    have e₁ := ((hα i).add (hτ o)).eventually_lt tendsto_const_nhds hi₁
    have e₂ := tendsto_const_nhds.eventually_lt ((hβ i).add (hτ o)) hi₂
    have e₃ := ((hα j).add (hτ p)).eventually_lt tendsto_const_nhds hj₁
    have e₄ := tendsto_const_nhds.eventually_lt ((hβ j).add (hτ p)) hj₂
    have ee : ∀ᶠ m in (U : Filter ℕ), w m o = w m p := by
      filter_upwards [e₁, e₂, e₃, e₄] with m v₁ v₂ v₃ v₄
      exact hpack m (hw m o) (hw m p) ⟨i, v₁, v₂⟩ ⟨j, v₃, v₄⟩
    exact tendsto_nhds_unique (hτ o) ((hτ p).congr' (ee.mono fun _ h ↦ h.symm))
  · intro x
    refine ⟨τ (some x), ⟨some x, rfl⟩, ?_⟩
    have hsel : ∀ᶠ m in (U : Filter ℕ), ∃ i : Fin n,
        α m i + w m (some x) ≤ x ∧ x ≤ β m i + w m (some x) :=
      Filter.Eventually.of_forall (fun m ↦ hxt m x)
    obtain ⟨i, hi⟩ := Ultrafilter.eventually_exists_iff.mp hsel
    exact ⟨i, le_of_tendsto ((hα i).add (hτ (some x))) (hi.mono fun _ h ↦ h.1),
      ge_of_tendsto ((hβ i).add (hτ (some x))) (hi.mono fun _ h ↦ h.2)⟩

private theorem injFloor {n : ℕ} {a b : Fin n → ℝ} {S : Set ℝ}
    (hp : packed a b S) (i : Fin n) (hi : a i < b i) :
    InjOn (fun t : ℝ ↦ ⌊t / (b i - a i)⌋) S := by
  let d := b i - a i
  have hd : 0 < d := sub_pos.mpr hi
  intro s hs t ht he
  change ⌊s / d⌋ = ⌊t / d⌋ at he
  have hfst : s / d < t / d + 1 := by
    have h := Int.lt_floor_add_one (s / d)
    rw [he] at h
    linarith [Int.floor_le (t / d)]
  have hfts : t / d < s / d + 1 := by
    have h := Int.lt_floor_add_one (t / d)
    rw [← he] at h
    linarith [Int.floor_le (s / d)]
  have h₁ : s < t + d := by
    have h := (div_lt_iff₀ hd).mp hfst
    rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at h
    exact h
  have h₂ : t < s + d := by
    have h := (div_lt_iff₀ hd).mp hfts
    rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at h
    exact h
  obtain hst | hts := le_total s t
  · let x := (a i + t + (b i + s)) / 2
    apply hp (x := x) hs ht
    · refine ⟨i, ?_, ?_⟩ <;> dsimp [x] <;> linarith [show d = b i - a i by rfl]
    · refine ⟨i, ?_, ?_⟩ <;> dsimp [x] <;> linarith [show d = b i - a i by rfl]
  · let x := (a i + s + (b i + t)) / 2
    apply hp (x := x) hs ht
    · refine ⟨i, ?_, ?_⟩ <;> dsimp [x] <;> linarith [show d = b i - a i by rfl]
    · refine ⟨i, ?_, ?_⟩ <;> dsimp [x] <;> linarith [show d = b i - a i by rfl]

private theorem floorBounded {S : Set ℝ} {d : ℝ} (hd : 0 < d)
    (hi : InjOn (fun t : ℝ ↦ ⌊t / d⌋) S) (l u : ℝ) :
    (S ∩ Icc l u).Finite := by
  apply Set.Finite.of_finite_image (f := fun t : ℝ ↦ ⌊t / d⌋) _ (hi.mono inter_subset_left)
  refine (Set.finite_Icc ⌊l / d⌋ ⌊u / d⌋).subset ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨Int.floor_le_floor ((div_le_div_iff_of_pos_right hd).mpr ht.2.1),
    Int.floor_le_floor ((div_le_div_iff_of_pos_right hd).mpr ht.2.2)⟩

private theorem packed_locally_finite {S : Set ℝ}
    (hf : ∀ l u : ℝ, (S ∩ Icc l u).Finite) (T : Set ℝ) (hTS : T ⊆ S) :
    IsLocallyFiniteMeasure (Measure.sum (fun t : T ↦ Measure.dirac (t : ℝ))) := by
  constructor
  intro x
  let I := Ioo (x - 1) (x + 1)
  have hI : MeasurableSet I := measurableSet_Ioo
  refine ⟨I, isOpen_Ioo.mem_nhds (by constructor <;> linarith), ?_⟩
  have hfin : ({t : T | (t : ℝ) ∈ I} : Set T).Finite := by
    refine ((hf (x - 1) (x + 1)).preimage
      (Subtype.val_injective.injOn : InjOn (Subtype.val : T → ℝ) _)).subset ?_
    intro t ht
    exact ⟨hTS t.property, Ioo_subset_Icc_self ht⟩
  rw [Measure.sum_apply _ hI, tsum_eq_sum (s := hfin.toFinset)]
  · exact ENNReal.sum_lt_top.mpr fun t _ ↦ by
      by_cases h : (t : ℝ) ∈ I <;> simp [h]
  · intro t ht
    have hn : (t : ℝ) ∉ I := by simpa using ht
    simp [hn]

private theorem geometry_proper {n : ℕ} {a b : Fin n → ℝ} (hn : 0 < n)
    (ho : ordered a b) {S : Set ℝ} (hS₀ : 0 ∈ S) (hP : packed a b S)
    (hC : ∀ x, ∃ t ∈ S, closedHit a b x t) :
    WeakTiling.IsProperTiling (intervals a b) (S \ {0}) := by
  let i₀ : Fin n := ⟨0, hn⟩
  let d := b i₀ - a i₀
  have hd : 0 < d := sub_pos.mpr (ho.1 i₀)
  have hi : InjOn (fun t : ℝ ↦ ⌊t / d⌋) S := injFloor hP i₀ (ho.1 i₀)
  have hfin : ∀ l u : ℝ, (S ∩ Icc l u).Finite := floorBounded hd hi
  have hSc : Countable S := Function.Injective.countable
    (f := fun t : S ↦ ⌊(t : ℝ) / d⌋) (fun s t h ↦ Subtype.ext (hi s.property t.property h))
  let T := S \ {0}
  let μ := Measure.sum (fun t : T ↦ Measure.dirac (t : ℝ))
  let Ω := intervals a b
  have hm : MeasurableSet Ω := MeasurableSet.iUnion fun _ ↦ measurableSet_Ioo
  have hb : Bornology.IsBounded Ω :=
    Bornology.isBounded_iUnion.mpr (fun i ↦ Metric.isBounded_Ioo (a i) (b i))
  refine ⟨hb, hm, packed_locally_finite hfin T sdiff_subset, ?_⟩
  let Ends : Set ℝ := Set.range (fun p : (S × Fin n) × Bool ↦
    if p.2 then a p.1.2 + (p.1.1 : ℝ) else b p.1.2 + (p.1.1 : ℝ))
  have hEnds : Ends.Countable := Set.countable_range _
  filter_upwards [hEnds.ae_notMem (volume : Measure ℝ)] with x hx
  obtain ⟨s, hs, i, hlo, hhi⟩ := hC x
  have hxl : a i + s ≠ x := by
    intro h
    exact hx ⟨((⟨s, hs⟩, i), true), by simpa using h⟩
  have hxh : x ≠ b i + s := by
    intro h
    exact hx ⟨((⟨s, hs⟩, i), false), by simpa using h.symm⟩
  have hhit : hit a b x s := ⟨i, lt_of_le_of_ne hlo hxl, lt_of_le_of_ne hhi hxh⟩
  have mh (t : ℝ) : x - t ∈ Ω ↔ hit a b x t := by
    simp only [Ω, intervals, Set.mem_iUnion, Set.mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add]
    rfl
  let P : Set ℝ := (fun t : ℝ ↦ x - t) ⁻¹' Ω
  have hPm : MeasurableSet P := hm.preimage (measurable_const.sub measurable_id)
  have hI : (∫ t, Ω.indicator (fun _ ↦ (1 : ℝ)) (x - t) ∂μ) = μ.real P := by
    have hh (t : ℝ) : P.indicator (fun _ ↦ (1 : ℝ)) t =
        Ω.indicator (fun _ ↦ (1 : ℝ)) (x - t) := by
      by_cases ht : x - t ∈ Ω <;> simp [Set.indicator, P, ht]
    simp only [← hh, integral_indicator_const (μ := μ) (1 : ℝ) hPm, smul_eq_mul, mul_one]
  change (∫ t, Ω.indicator (fun _ ↦ (1 : ℝ)) (x - t) ∂μ) = Ωᶜ.indicator (fun _ ↦ 1) x
  rw [hI, Measure.real_def]
  change ((Measure.sum (fun t : T ↦ Measure.dirac (t : ℝ))) P).toReal = _
  rw [Measure.sum_apply _ hPm]
  by_cases hxΩ : x ∈ Ω
  · have hno (t : T) : (t : ℝ) ∉ P := by
      intro ht
      have h : (t : ℝ) = 0 := hP t.property.1 hS₀ ((mh t).mp ht)
        ((mh 0).mp (by simpa using hxΩ))
      exact t.property.2 (Set.mem_singleton_iff.mpr h)
    have hc : x ∉ Ωᶜ := fun h ↦ h hxΩ
    simp [hno, Set.indicator_of_notMem hc]
  · have hsne : s ≠ 0 := fun h ↦ hxΩ (by simpa [h] using (mh s).mpr hhit)
    let z : T := ⟨s, hs, by simpa using hsne⟩
    have hz : (z : ℝ) ∈ P := (mh s).mpr hhit
    have hrest (t : T) (ht : t ≠ z) : (t : ℝ) ∉ P := by
      intro h
      exact ht (Subtype.ext (hP t.property.1 hs ((mh t).mp h) hhit))
    rw [tsum_eq_single z]
    · have hc : x ∈ Ωᶜ := hxΩ
      simp [Measure.dirac_apply_of_mem hz, Set.indicator_of_mem hc]
    · intro t ht
      simp [hrest t ht]

/-- Every real weak tiling has an anchored finite-rank endpoint balance model. -/
def H1 : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (a b : Fin n → ℝ),
    (∀ i, a i < b i) → (∀ i j, i < j → b i < a j) →
    ∀ ν : Measure ℝ, WeakTiling.IsWeakTilingMeasure (⋃ i, Ioo (a i) (b i)) ν →
      ∃ (d : ℕ) (r : Fin d → ℝ) (u v : Fin n → Fin d → ℤ) (z : Fin d → ℤ)
        (w : (Fin d → ℤ) → ℝ≥0∞) (D : ℝ),
        let x (p : Fin d → ℤ) := ∑ i, (p i : ℝ) * r i
        0 < D ∧ (∀ i, x (u i) = a i) ∧ (∀ i, x (v i) = b i) ∧
        (∀ p, w p ≠ ∞) ∧ w 0 = 1 ∧
        (∀ p, w p ≠ 0 → (∑ i, |(p i : ℝ)|) ≤ D * |x p|) ∧
        (∀ p, ∑ i, w (p - u i) = ∑ i, w (p - v i)) ∧
        (∃ i, a i < x z ∧ x z < b i) ∧
        (∀ p, p ≠ 0 → w p ≠ 0 → ∀ i, x z < a i + x p ∨ b i + x p < x z)

/-- An anchored fractional exact cover of the integers admits an anchored exact cover. -/
def H2 : Prop :=
  ∀ A : Finset ℤ, A.Nonempty →
    (∃ w : ℤ → ℝ≥0∞, w 0 = 1 ∧ ∀ j, ∑ a ∈ A, w (j - a) = 1) →
    ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j - t ∈ A

theorem main : H1 → H2 → type_of% @WeakTiling.problem_4_2 := by
  intro h₁ h₂ n hn Ω hΩ ν hν
  obtain ⟨a, b, ha, hb, rfl⟩ := hΩ
  change WeakTiling.IsWeakTilingMeasure (intervals a b) ν at hν
  have horder : ordered a b := ⟨ha, hb⟩
  have hmodel : LatticeModel a b := h₁ n hn a b ha hb ν hν
  obtain ⟨S, hS₀, hP, hC⟩ := approximation_cover (by omega) a b h₂ (lattice_approx horder hmodel)
  exact ⟨S \ {0}, geometry_proper (by omega) horder hS₀ hP hC⟩

end OMA.R_WeakTiling_problem_4_2_R1
