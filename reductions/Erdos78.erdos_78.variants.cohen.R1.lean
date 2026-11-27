import FormalConjectures.ErdosProblems.«78»

/-! Reduce Cohen’s Ramsey graph theorem to Theorem 1.2 of arXiv:1506.04428 and a polynomial-time encoding adapter. -/

open Filter Real ComplexityTheory Erdos78

namespace OMA.R_Erdos78_erdos_78_variants_cohen_R1

/-- A uniform explicit bipartite Ramsey family, formulated as a Boolean matrix.
Every sufficiently large rectangle in the matrix contains both Boolean values. -/
def H1 : Prop :=
  ∃ D > (0 : ℝ), ∃ f : ℕ × ℕ × ℕ → Bool, IsPolyTime f ∧
    ∀ᶠ n : ℕ in atTop, ∀ A B : Finset (Fin n),
      ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊ ≤ A.card →
      ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊ ≤ B.card →
      ∀ b : Bool, ∃ u ∈ A, ∃ v ∈ B, f (n, u.val, v.val) = b

/-- Reading a unary dimension and sorting the two binary vertex labels
preserves polynomial-time computability under the canonical encodings. -/
def H2 : Prop :=
  ∀ f : ℕ × ℕ × ℕ → Bool, IsPolyTime f →
    ∃ g : List Bool × ℕ × ℕ → Bool, IsPolyTime g ∧
      ∀ (s : List Bool) (u v : ℕ),
        g (s, u, v) = f (s.length, min u v, max u v)

lemma ordered_rectangles {n m k : ℕ} (s : Finset (Fin n)) (hs : s.card = m)
    (hm : 2 * k ≤ m) :
    ∃ A B : Finset (Fin n), A ⊆ s ∧ B ⊆ s ∧ A.card = k ∧ B.card = k ∧
      ∀ u ∈ A, ∀ v ∈ B, u < v := by
  let e := s.orderEmbOfFin hs
  let lo (i : Fin k) : Fin m := ⟨i.val, by have := i.isLt; omega⟩
  let hi (i : Fin k) : Fin m := ⟨k + i.val, by have := i.isLt; omega⟩
  have hlo : Function.Injective lo := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin m => x.val) h)
  have hhi : Function.Injective hi := by
    intro i j h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun x : Fin m => x.val) h)
  let a : Fin k ↪ Fin n := ⟨e ∘ lo, e.injective.comp hlo⟩
  let b : Fin k ↪ Fin n := ⟨e ∘ hi, e.injective.comp hhi⟩
  refine ⟨Finset.univ.map a, Finset.univ.map b, ?_, ?_, by simp, by simp, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem hs (lo i)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem hs (hi i)
  · intro u hu v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    change e (lo i) < e (hi j)
    apply e.strictMono
    change i.val < k + j.val
    have := i.isLt
    omega

lemma doubled_ceiling_eventually (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop,
      2 * ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊ ≤
        ⌈(2 : ℝ) ^ (log (log n)) ^ (D + 1)⌉₊ := by
  have ht : Tendsto (fun n : ℕ => log (log n)) atTop atTop :=
    (tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (3 : ℝ))] with n hn
  let t := log (log (n : ℝ))
  change 3 ≤ t at hn
  have ht1 : 1 ≤ t := by linarith
  have hq : 1 ≤ t ^ D := Real.one_le_rpow ht1 hD.le
  have hx : 1 ≤ (2 : ℝ) ^ (t ^ D) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hexp : t ^ D + 2 ≤ t ^ (D + 1) := by
    rw [Real.rpow_add (by positivity) D 1, Real.rpow_one]
    calc
      t ^ D + 2 ≤ t ^ D * 3 := by linarith
      _ ≤ t ^ D * t := mul_le_mul_of_nonneg_left hn (by positivity)
  have hpow : (2 : ℝ) ^ (t ^ D) * 4 ≤ (2 : ℝ) ^ (t ^ (D + 1)) := by
    calc
      (2 : ℝ) ^ (t ^ D) * 4 = (2 : ℝ) ^ (t ^ D + 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num [Real.rpow_two]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ (t ^ D) by positivity)
  change 2 * ⌈(2 : ℝ) ^ (t ^ D)⌉₊ ≤ ⌈(2 : ℝ) ^ (t ^ (D + 1))⌉₊
  exact_mod_cast
    (show 2 * (⌈(2 : ℝ) ^ (t ^ D)⌉₊ : ℝ) ≤ (⌈(2 : ℝ) ^ (t ^ (D + 1))⌉₊ : ℝ) by
      calc
        _ ≤ (2 : ℝ) ^ (t ^ D) * 4 := by linarith
        _ ≤ _ := hpow.trans (Nat.le_ceil _))

theorem main : H1 → H2 → type_of% @Erdos78.erdos_78.variants.cohen := by
  intro h₁ h₂
  obtain ⟨D, hD, f, hf, hrect⟩ := h₁
  obtain ⟨g, hg, hsort⟩ := h₂ f hf
  refine ⟨D + 1, by linarith, g, hg, ?_⟩
  filter_upwards [hrect, doubled_ceiling_eventually D hD] with n hrectn hsize
  let k := ⌈(2 : ℝ) ^ (log (log n)) ^ D⌉₊
  let m := ⌈(2 : ℝ) ^ (log (log n)) ^ (D + 1)⌉₊
  change 2 * k ≤ m at hsize
  have hadj (u v : Fin n) (huv : u < v) :
      (explicitGraph g n).Adj u v ↔ f (n, u.val, v.val) = true := by
    have hval : u.val ≤ v.val := huv.le
    simp [explicitGraph, hsort, min_eq_left hval, max_eq_right hval,
      min_eq_right hval, max_eq_left hval, huv.ne]
  change (explicitGraph g n).CliqueFree m ∧ (explicitGraph g n)ᶜ.CliqueFree m
  constructor
  · intro s hs
    obtain ⟨A, B, hA, hB, hAk, hBk, hlt⟩ := ordered_rectangles s hs.card_eq hsize
    obtain ⟨u, hu, v, hv, hfalse⟩ := hrectn A B hAk.ge hBk.ge false
    have huv := hlt u hu v hv
    have htrue := (hadj u v huv).mp (hs.isClique (hA hu) (hB hv) huv.ne)
    rw [hfalse] at htrue
    contradiction
  · intro s hs
    obtain ⟨A, B, hA, hB, hAk, hBk, hlt⟩ := ordered_rectangles s hs.card_eq hsize
    obtain ⟨u, hu, v, hv, htrue⟩ := hrectn A B hAk.ge hBk.ge true
    have huv := hlt u hu v hv
    have hnAdj := (SimpleGraph.compl_adj _ _ _).mp (hs.isClique (hA hu) (hB hv) huv.ne)
    exact hnAdj.2 ((hadj u v huv).mpr htrue)

end OMA.R_Erdos78_erdos_78_variants_cohen_R1
