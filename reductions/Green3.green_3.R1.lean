import FormalConjectures.GreensOpenProblems.«3»

/-!
# A finite integer formulation of Green's product problem

At resolution N=2^k, retain the open cells (i/N,(i+1)/N) lying in the given set.
A product of the cells numbered i,j meets cell l exactly when
i*j < (l+1)*N and l*N < (i+1)*(j+1). The forward implication uses the integer
endpoints. For the converse, interpolate between both endpoint products.
The finite problem does not mention real numbers or measures.

Green's problem was solved by Franchi, Gowers and Yip, arXiv:2607.06073.
This discretization and Lean proof are by @Deldor14.
-/

namespace OMA.R_Green3_green_3_R1

open Set MeasureTheory Finset

private lemma product_cells {i j l N : ℕ} (hN : 0<N)
    (hlo : i*j < (l+1)*N) (hhi : l*N < (i+1)*(j+1)) :
    ∃ x ∈ Set.Ioo ((i:ℝ)/N) (((i:ℝ)+1)/N), ∃ y ∈ Set.Ioo ((j:ℝ)/N) (((j:ℝ)+1)/N), x*y ∈ Set.Ioo ((l:ℝ)/N) (((l:ℝ)+1)/N) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) ≤ i := by positivity
  have hj : (0:ℝ) ≤ j := by positivity
  have hl : (i:ℝ)*j < ((l:ℝ)+1)*N := by exact_mod_cast hlo
  have hh : (l:ℝ)*N < ((i:ℝ)+1)*(j+1) := by exact_mod_cast hhi
  have hself : (i:ℝ)*j < ((i:ℝ)+1)*(j+1) := by nlinarith
  have hcross : (l:ℝ)*N < ((l:ℝ)+1)*N := by linarith
  obtain ⟨w,hw₁,hw₂⟩ := exists_between
    (max_lt (lt_min hself hl) (lt_min hh hcross))
  have hwi := (max_lt_iff.mp hw₁).1
  have hwl := (max_lt_iff.mp hw₁).2
  have hwj := (lt_min_iff.mp hw₂).1
  have hwr := (lt_min_iff.mp hw₂).2
  let f : ℝ → ℝ := fun t => ((i:ℝ)+t)*((j:ℝ)+t)
  have hc : Continuous f := by fun_prop
  have hwf : w ∈ Set.Icc (f 0) (f 1) := by simpa [f] using And.intro hwi.le hwj.le
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hc.continuousOn hwf
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by rintro rfl; simp [f] at he; linarith)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by rintro rfl; simp [f] at he; linarith)
  refine ⟨((i:ℝ)+t)/N,⟨(div_lt_div_iff_of_pos_right hNr).2 (by linarith),
    (div_lt_div_iff_of_pos_right hNr).2 (by linarith)⟩, ((j:ℝ)+t)/N,
    ⟨(div_lt_div_iff_of_pos_right hNr).2 (by linarith),
    (div_lt_div_iff_of_pos_right hNr).2 (by linarith)⟩,?_⟩
  rw [div_mul_div_comm, show ((i:ℝ)+t)*((j:ℝ)+t) = w from he]
  constructor
  · apply (div_lt_div_iff₀ hNr (mul_pos hNr hNr)).mpr
    nlinarith only [mul_lt_mul_of_pos_right hwl hNr]
  · apply (div_lt_div_iff₀ (mul_pos hNr hNr) hNr).mpr
    nlinarith only [mul_lt_mul_of_pos_right hwr hNr]

/-- Inner approximation by dyadic cells at one common resolution. -/
def H1 : Prop := ∀ A : Set ℝ, IsOpen A → A ⊆ Set.Icc 0 1 → 1/3 < volume A →
    ∃ k : ℕ, ∃ S : Finset ℕ, S ⊆ range (2^k) ∧ 2^k < 3*S.card ∧
      ∀ i ∈ S, Set.Ioo ((i:ℝ)/((2^k:ℕ):ℝ)) (((i:ℝ)+1)/((2^k:ℕ):ℝ)) ⊆ A

/-- A finite extremal problem on the integer cell indices. -/
def H2 : Prop := ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ range (2^k) → 2^k < 3*S.card →
    ∃ i ∈ S, ∃ j ∈ S, ∃ l ∈ S, i*j < (l+1)*2^k ∧ l*2^k < (i+1)*(j+1)

theorem main : H1 → H2 → type_of% @Green3.green_3 := by
  intro approx finiteCover A hA hsub hvol
  obtain ⟨k,S,hS,hcard,hcell⟩ := approx A hA hsub hvol
  obtain ⟨i,hi,j,hj,l,hl,hle,hgt⟩ := finiteCover k S hS hcard
  obtain ⟨x,hx,y,hy,hxy⟩ := product_cells (by positivity) hle hgt
  exact ⟨x,y,x*y,hcell i hi hx,hcell j hj hy,hcell l hl hxy,rfl⟩


/-- The continuous theorem also implies the finite integer statement, so the
discretization retains exactly the original extremal problem. -/
theorem finite_of_green (h : type_of% @Green3.green_3) : H2 := by
  classical
  intro k S hS hcard
  let N : ℕ := 2^k
  have hNr : (0:ℝ) < N := by dsimp [N]; positivity
  let I := fun i : ℕ => Set.Ioo ((i:ℝ)/N) (((i:ℝ)+1)/N)
  let U := ⋃ i ∈ S, I i
  have hopen : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo
  have hsub : U ⊆ Set.Icc 0 1 := by
    rintro x hx
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    have hiN : i+1 ≤ N := Nat.succ_le_of_lt (mem_range.mp (hS hi))
    have hri : (i:ℝ)+1 ≤ N := by exact_mod_cast hiN
    have hlo : 0 ≤ (i:ℝ)/N := by positivity
    exact ⟨hlo.trans hx.1.le,hx.2.le.trans ((div_le_one hNr).mpr hri)⟩
  have hd : (S : Set ℕ).PairwiseDisjoint I := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hle : (i:ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hlt)
      exact (not_lt_of_ge (div_le_div_of_nonneg_right hle hNr.le)) (hy.1.trans hx.2)
    · have hle : (j:ℝ)+1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt hlt)
      exact (not_lt_of_ge (div_le_div_of_nonneg_right hle hNr.le)) (hx.1.trans hy.2)
  have hmeas (i : ℕ) : volume (I i) = ENNReal.ofReal (1/(N:ℝ)) := by
    dsimp only [I]
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hvol : volume U = ENNReal.ofReal ((S.card:ℝ)/N) := calc
    volume U = ∑ i ∈ S, volume (I i) := measure_biUnion_finset hd (fun _ _ => measurableSet_Ioo)
    _ = ∑ _i ∈ S, ENNReal.ofReal (1/(N:ℝ)) := sum_congr rfl fun i _ => hmeas i
    _ = ENNReal.ofReal (∑ _i ∈ S, 1/(N:ℝ)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ = ENNReal.ofReal ((S.card:ℝ)/N) := by simp [nsmul_eq_mul,div_eq_mul_inv]
  have hNcard : (N:ℝ) < 3*S.card := by exact_mod_cast hcard
  have hreal : (1:ℝ)/3 < S.card/N := (lt_div_iff₀ hNr).mpr (by linarith)
  have hlarge : 1/3 < volume U := by
    rw [hvol]
    have hh := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr hreal
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)] at hh
    simpa using hh
  obtain ⟨x,y,z,hx,hy,hz,rfl⟩ := h U hopen hsub hlarge
  obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨j,hj,hy⟩ := mem_iUnion₂.mp hy
  obtain ⟨l,hl,hz⟩ := mem_iUnion₂.mp hz
  have hx0 : 0<x := lt_of_le_of_lt (by positivity : 0 ≤ (i:ℝ)/N) hx.1
  have hlow : ((i:ℝ)/N)*(j/N) < ((l:ℝ)+1)/N :=
    ((mul_le_mul_of_nonneg_right hx.1.le (by positivity)).trans_lt
      (mul_lt_mul_of_pos_left hy.1 hx0)).trans hz.2
  have hhigh : (l:ℝ)/N < (((i:ℝ)+1)/N)*(((j:ℝ)+1)/N) :=
    hz.1.trans ((mul_lt_mul_of_pos_left hy.2 hx0).trans
      (mul_lt_mul_of_pos_right hx.2 (by positivity)))
  rw [div_mul_div_comm,div_lt_div_iff₀ (mul_pos hNr hNr) hNr] at hlow
  rw [div_mul_div_comm,div_lt_div_iff₀ hNr (mul_pos hNr hNr)] at hhigh
  have hL : (i:ℝ)*j*N < (((l:ℝ)+1)*N)*N := by linarith only [hlow]
  have hR : (l:ℝ)*N*N < (((i:ℝ)+1)*(j+1))*N := by linarith only [hhigh]
  refine ⟨i,hi,j,hj,l,hl,?_,?_⟩
  · exact_mod_cast (lt_of_mul_lt_mul_right hL hNr.le)
  · exact_mod_cast (lt_of_mul_lt_mul_right hR hNr.le)

end OMA.R_Green3_green_3_R1
