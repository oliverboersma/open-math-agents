import FormalConjectures.GreensOpenProblems.«14»
import Mathlib.Combinatorics.HalesJewett

-- Reduction Green14.W_3_13.R2 of Ben Green's Open Problem 14 — W 3 13
-- Credit: @ZedingZhang

/-!
# A four-progression reduction for W(3,13) = 160

On the interval from 0 to 159, exactly four progressions of length 13 have
common difference 13. They start at 0, 1, 2 and 3. If each meets a red set,
choose one red point on each, with respective heights i, j, k and l (the
point on the third progression, for example, is 13k + 2). If the red set
contains no three-term progression, neither second difference of the four
heights can vanish. Reflection about the centre exchanges the differences
and negates both. This leaves the three sign patterns in H1, H2 and H3.
For mixed signs we choose the orientation with the lexicographically smaller
pair of height sums (i+l, j+k), allowing equality. Each remaining
search starts with four prescribed red points and only has to enforce the
blue-progression constraints for common differences 1 through 12.

The lower bound uses an explicit red set on 159 points. Lean checks every
start and positive difference for both forbidden lengths. Hales--Jewett
supplies a finite upper bound independently of the cases. This proves
the numerical inequality 160 ≤ W 3 13 outright. The
interval and progression lemmas adapt the project's reductions for W(3,12)
and W(3,11). They and the finite Hales--Jewett argument build on Dominic
Dabish's Apache-2.0 proofs. The first reduction of this problem splits by
the nearest red point to the centre. The four selected red points here
come from progressions of common difference 13.
-/

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_13_R2

/-- Both second differences of the four selected heights are positive. -/
def H1 : Prop :=
  ∀ (R : Finset ℕ) (i j k l : Fin 13),
    (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z) →
    (∀ a d : ℕ, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, a + t.val*d ∈ R) →
    13*i.val ∈ R → 13*j.val + 1 ∈ R → 13*k.val + 2 ∈ R → 13*l.val + 3 ∈ R →
    2*j.val < i.val + k.val → 2*k.val < j.val + l.val → False

/-- The first second difference is positive and the second is negative. -/
def H2 : Prop :=
  ∀ (R : Finset ℕ) (i j k l : Fin 13),
    (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z) →
    (∀ a d : ℕ, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, a + t.val*d ∈ R) →
    13*i.val ∈ R → 13*j.val + 1 ∈ R → 13*k.val + 2 ∈ R → 13*l.val + 3 ∈ R →
    2*j.val < i.val + k.val → j.val + l.val < 2*k.val →
    (i.val + l.val < 12 ∨ (i.val + l.val = 12 ∧ j.val + k.val ≤ 12)) → False

/-- The first second difference is negative and the second is positive. -/
def H3 : Prop :=
  ∀ (R : Finset ℕ) (i j k l : Fin 13),
    (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z) →
    (∀ a d : ℕ, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, a + t.val*d ∈ R) →
    13*i.val ∈ R → 13*j.val + 1 ∈ R → 13*k.val + 2 ∈ R → 13*l.val + 3 ∈ R →
    i.val + k.val < 2*j.val → 2*k.val < j.val + l.val →
    (i.val + l.val < 12 ∨ (i.val + l.val = 12 ∧ j.val + k.val ≤ 12)) → False

theorem mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) :
    N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x ↦ ⟨x, x.2.1, x.2.2.trans hMN⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Icc 1 N ↦ (z : Nat)) h⟩
  let restricted : Icc 1 M → Fin 2 := fun x ↦ coloring (emb x)
  rcases hM restricted with hzero | hone
  · left
    rcases hzero with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

/-- One bad coloring of `{1, ..., N}` proves the numerical lower bound
`W(k,r) ≥ N+1`. -/
private theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

private lemma progression_at {N k a d : Nat} (hd : 0 < d)
    (c : Icc 1 N → Fin 2) (color : Fin 2)
    (bound : ∀ i : Fin k, a+i.val*d < N)
    (mono : ∀ (i : Fin k) (hi : a+i.val*d < N), c ⟨a+i.val*d+1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val*d + 1
  have inj : Function.Injective value := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (by simpa [value] using h)
  let point : Fin k ↪ Icc 1 N := ⟨fun i => ⟨value i, by
    have := bound i
    dsimp [value]
    constructor <;> omega⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  let s := Finset.univ.map point
  have eqs : ({(z : Nat) | z ∈ s} : Set Nat) = range value := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨point i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a+1,d,?_,?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]; omega⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)


private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val-1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k-1)*d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val*d.val) = col := by
  obtain ⟨s,⟨a,d,hcard,hset⟩,hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i*d := by
    change a + i*d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k-1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k-1)*d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k-1 by omega)
  refine ⟨⟨a-1,by omega⟩,⟨d,by omega⟩,hpos,by change a-1+(k-1)*d < N; omega,?_⟩
  intro i
  obtain ⟨x,hx,hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val*d) = col
  convert he using 2; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lower_witness : 159 ∉ mixedMonoAPGuaranteeSet 3 13 := by
  let q (i : ℕ) : Fin 2 := if (0x1400808110682005024002c40410828100082401 : ℕ).testBit i then 0 else 1
  have red : ∀ a d : Fin 159, 0 < d.val → a.val + 2*d.val < 159 →
      ¬ ∀ i : Fin 3, q (a.val + i.val*d.val) = 0 := by decide +kernel
  have blue : ∀ a d : Fin 159, 0 < d.val → a.val + 12*d.val < 159 →
      ¬ ∀ i : Fin 13, q (a.val + i.val*d.val) = 1 := by decide +kernel
  intro h
  rcases h (fun x => q (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    exact red a d hd hbound hc
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 13) q 1 hb
    exact blue a d hd hbound hc

/-- Hales--Jewett supplies an interval on which a monochromatic 13-term
progression is forced. This establishes the numerical lower bound independently
of all three finite upper-bound hypotheses. -/
theorem lower_bound : 160 ≤ W 3 13 := by
  classical
  apply W_ge_succ_of_not_mem 3 13 159 _ lower_witness
  obtain ⟨ι, inst, cube⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin 13) (Fin 2)
  let : Fintype ι := inst
  let N := Fintype.card ι * 12 + 1
  let point (v : ι → Fin 13) : Icc 1 N :=
    ⟨1 + ∑ i, (v i).val, by
      have hsum : ∑ i, (v i).val ≤ ∑ _i : ι, 12 :=
        Finset.sum_le_sum (fun i _ => show (v i).val ≤ 12 by omega)
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at hsum
      dsimp only [N]
      constructor <;> omega⟩
  refine ⟨N, ?_⟩
  intro c
  obtain ⟨line, col, mono⟩ := cube (fun v => c (point v))
  let active : Finset ι := Finset.univ.filter (fun u => line.idxFun u = none)
  let d := active.card
  let b : ℕ := ∑ u ∈ activeᶜ, ((line.idxFun u).map Fin.val).getD 0
  have hd : 0 < d := Finset.card_pos.mpr
    ⟨line.proper.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, line.proper.choose_spec⟩⟩
  have linePoint (x : Fin 13) : (point (line x)).val = b + x.val*d + 1 := by
    change 1 + ∑ u, (line x u).val = _
    rw [← Finset.sum_add_sum_compl active]
    have moving : ∑ u ∈ active, (line x u).val = x.val*d := by
      calc
        ∑ u ∈ active, (line x u).val = ∑ _u ∈ active, x.val := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [line.apply_none x u (Finset.mem_filter.mp hu).2]
        _ = x.val*d := by simp [d, Nat.mul_comm]
    have fixed : ∑ u ∈ activeᶜ, (line x u).val = b := by
      apply Finset.sum_congr rfl
      intro u hu
      cases ho : line.idxFun u with
      | none => exact (Finset.mem_compl.mp hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩)).elim
      | some v => simp [Combinatorics.Line.coe_apply, ho]
    rw [moving, fixed]
    omega
  have build (q : ℕ) (hq : q ≤ 13) : ∃ s : Finset (Icc 1 N),
      ({(z : ℕ) | z ∈ s}).IsAPOfLength q ∧ ∀ z ∈ s, c z = col := by
    apply progression_at (a := b) hd c col
    · intro i
      have hp := (point (line (Fin.castLE hq i))).property.2
      rw [linePoint] at hp
      change b + i.val*d + 1 ≤ N at hp
      omega
    · intro i hi
      have hp := linePoint (Fin.castLE hq i)
      have eqp : (⟨b + i.val*d + 1, by constructor <;> omega⟩ : Icc 1 N) =
          point (line (Fin.castLE hq i)) := Subtype.ext hp.symm
      rw [eqp]
      exact mono _
  fin_cases col
  · exact Or.inl (build 3 (by decide))
  · exact Or.inr (build 13 (by decide))

private theorem normalized (h₁ : H1) (h₂ : H2) (h₃ : H3)
    (R : Finset ℕ) (i j k l : Fin 13)
    (free : ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z)
    (hit : ∀ a d : ℕ, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, a + t.val*d ∈ R)
    (hi : 13*i.val ∈ R) (hj : 13*j.val + 1 ∈ R)
    (hk : 13*k.val + 2 ∈ R) (hl : 13*l.val + 3 ∈ R) :
    ¬ ((2*j.val < i.val + k.val ∧ 2*k.val < j.val + l.val) ∨
       ((2*j.val < i.val + k.val ∧ j.val + l.val < 2*k.val) ∨
        (i.val + k.val < 2*j.val ∧ 2*k.val < j.val + l.val)) ∧
       (i.val + l.val < 12 ∨ (i.val + l.val = 12 ∧ j.val + k.val ≤ 12))) := by
  rintro (⟨u, v⟩ | ⟨h, w⟩)
  · exact h₁ R i j k l free hit hi hj hk hl u v
  · rcases h with ⟨u, v⟩ | ⟨u, v⟩
    · exact h₂ R i j k l free hit hi hj hk hl u v w
    · exact h₃ R i j k l free hit hi hj hk hl u v w

/-- Each of the four progressions of common difference 13 contributes one red
point. Reflection negates and exchanges the two second differences. -/
private theorem four_rays (h₁ : H1) (h₂ : H2) (h₃ : H3) (R : Finset ℕ)
    (free : ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z)
    (hit : ∀ a d : ℕ, 0 < d → a + 12*d < 160 → ∃ t : Fin 13, a + t.val*d ∈ R) :
    False := by
  have anchor (b : ℕ) (hb : b < 4) : ∃ t : Fin 13, 13*t.val + b ∈ R := by
    obtain ⟨t, ht⟩ := hit b 13 (by decide) (by omega)
    exact ⟨t, by simpa only [Nat.mul_comm t.val 13, Nat.add_comm b] using ht⟩
  obtain ⟨i, hi⟩ := anchor 0 (by decide)
  obtain ⟨j, hj⟩ := anchor 1 (by decide)
  obtain ⟨k, hk⟩ := anchor 2 (by decide)
  obtain ⟨l, hl⟩ := anchor 3 (by decide)
  have ne₁ : i.val + k.val ≠ 2*j.val := by
    intro e
    have := free _ hi _ hj _ hk (by omega)
    omega
  have ne₂ : j.val + l.val ≠ 2*k.val := by
    intro e
    have := free _ hj _ hk _ hl (by omega)
    omega
  have forward := normalized h₁ h₂ h₃ R i j k l free (fun a d hd _ => hit a d hd) hi hj hk hl

  let M := (Finset.range 160).filter (fun x => 159 - x ∈ R)
  let rev (s : Fin 13) : Fin 13 := ⟨12 - s.val, by omega⟩
  have mfree : ∀ x ∈ M, ∀ y ∈ M, ∀ z ∈ M, x + z = 2*y → x = z := by
    intro x hx y hy z hz e
    obtain ⟨xb, xr⟩ := Finset.mem_filter.mp hx
    obtain ⟨yb, yr⟩ := Finset.mem_filter.mp hy
    obtain ⟨zb, zr⟩ := Finset.mem_filter.mp hz
    have xb' := Finset.mem_range.mp xb
    have yb' := Finset.mem_range.mp yb
    have zb' := Finset.mem_range.mp zb
    have := free _ xr _ yr _ zr (by omega)
    omega
  have mhit (a d : ℕ) (hd : 0 < d) (_ : d ≤ 12) (he : a + 12*d < 160) :
      ∃ t : Fin 13, a + t.val*d ∈ M := by
    obtain ⟨t, ht⟩ := hit (159 - (a + 12*d)) d hd (by omega)
    have htd := Nat.mul_le_mul_right d (show t.val ≤ 12 by omega)
    refine ⟨rev t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
    · change a + (12 - t.val)*d < 160
      rw [Nat.sub_mul]
      omega
    · change 159 - (a + (12 - t.val)*d) ∈ R
      rw [Nat.sub_mul, show 159 - (a + (12*d - t.val*d)) = 159 - (a + 12*d) + t.val*d by omega]
      exact ht
  have mpoint (s : Fin 13) (b : ℕ) (hb : b < 4) (hp : 13*s.val + b ∈ R) :
      13*(rev s).val + (3 - b) ∈ M := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      dsimp [rev]
      omega
    · change 159 - (13*(12 - s.val) + (3 - b)) ∈ R
      rwa [show 159 - (13*(12 - s.val) + (3 - b)) = 13*s.val + b by omega]
  have backward := normalized h₁ h₂ h₃ M (rev l) (rev k) (rev j) (rev i) mfree mhit
    (mpoint l 3 (by decide) hl) (mpoint k 2 (by decide) hk)
    (mpoint j 1 (by decide) hj) (mpoint i 0 (by decide) hi)
  dsimp [rev] at backward
  omega

private theorem some_progression (h₁ : H1) (h₂ : H2) (h₃ : H3) (r : ℕ → Bool) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 12 else 2)*d < 160 ∧
      ∀ t ≤ (if b then 12 else 2), r (a + t*d) = b := by
  classical
  by_contra h
  let R := (Finset.range 160).filter (fun x => r x = false)
  have no_red (a d : ℕ) (hd : 0 < d) (he : a + 2*d < 160)
      (h₀ : r a = false) (h₁' : r (a+d) = false) (h₂' : r (a+2*d) = false) : False := by
    apply h
    refine ⟨false, a, d, hd, he, ?_⟩
    intro t ht
    change t ≤ 2 at ht
    interval_cases t <;> simp_all only [Nat.zero_mul, Nat.add_zero, Nat.one_mul]
  apply four_rays h₁ h₂ h₃ R
  · intro x hx y hy z hz e
    obtain ⟨xb, xr⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, yr⟩ := Finset.mem_filter.mp hy
    obtain ⟨zb, zr⟩ := Finset.mem_filter.mp hz
    have xb' := Finset.mem_range.mp xb
    have zb' := Finset.mem_range.mp zb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact no_red x (y-x) (by omega) (by omega) xr
        (by rwa [show x + (y-x) = y by omega])
        (by rwa [show x + 2*(y-x) = z by omega])
    · exact no_red z (y-z) (by omega) (by omega) zr
        (by rwa [show z + (y-z) = y by omega])
        (by rwa [show z + 2*(y-z) = x by omega])
  · intro a d hd he
    by_contra! hmiss
    apply h
    refine ⟨true, a, d, hd, he, ?_⟩
    intro t ht
    change t ≤ 12 at ht
    have htd := Nat.mul_le_mul_right d ht
    cases hc : r (a+t*d) with
    | false =>
      exfalso
      have hred : a + t*d ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩
      exact hmiss ⟨t, by omega⟩ hred
    | true => rfl

theorem main : H1 → H2 → H3 → type_of% @Green14.W_3_13 := by
  intro h₁ h₂ h₃
  have upper : 160 ∈ mixedMonoAPGuaranteeSet 3 13 := by
    intro c
    let r (i : ℕ) : Bool := if hi : i < 160 then decide (c ⟨i+1, by constructor <;> omega⟩ = 1) else false
    obtain ⟨b,a,d,hd,he,hm⟩ := some_progression h₁ h₂ h₃ r
    cases b
    · left
      apply progression_at (a := a) hd c 0
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
        simp only [Bool.false_eq_true, if_false] at he
        omega
      · intro i hi
        have hh := hm i.val (by simp only [Bool.false_eq_true, if_false]; omega)
        have hv : ¬ c ⟨a+i.val*d+1, by constructor <;> omega⟩ = 1 := by
          simpa [r, hi] using hh
        exact (show ∀ x : Fin 2, ¬ x = 1 → x = 0 by decide) _ hv
    · right
      apply progression_at (a := a) hd c 1
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 12 by omega)
        simp only [if_true] at he
        omega
      · intro i hi
        have hh := hm i.val (by simp only [if_true]; omega)
        simpa [r, hi] using hh
  exact le_antisymm (Nat.sInf_le upper) lower_bound

end OMA.R_Green14_W_3_13_R2
