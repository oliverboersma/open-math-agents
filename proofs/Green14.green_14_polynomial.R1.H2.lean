import OMAReductions.R_Green14_green_14_polynomial_R1
import Mathlib

/-! # Existence of a good Diophantine rotation on the torus

We prove step H2 of the Hunter (2021) reduction for Ben Green's Open Problem 14
by finite counting over a prime grid `(ZMod P)^D` for a sufficiently large prime `P`.
-/

namespace Green14PolyH2Proof

open scoped Classical Matrix

noncomputable section

private def badResidues (P K : ℕ) : Finset (ZMod P) :=
  (Finset.Icc (-(P / K : ℤ)) (P / K : ℤ)).image (Int.cast : ℤ → ZMod P)

private lemma card_badResidues_mul_le {P K : ℕ} (hK : 0 < K) (hKP : K ≤ P) :
    K * (badResidues P K).card ≤ 3 * P := by
  have hBpos : 1 ≤ P / K := Nat.div_pos hKP hK
  have hcard1 : (badResidues P K).card ≤ (Finset.Icc (-(P / K : ℤ)) (P / K : ℤ)).card :=
    Finset.card_image_le
  have hcard2 : (Finset.Icc (-(P / K : ℤ)) (P / K : ℤ)).card = 2 * (P / K) + 1 := by
    rw [Int.card_Icc]
    omega
  have hcard3 : (badResidues P K).card ≤ 3 * (P / K) := by omega
  calc K * (badResidues P K).card
      ≤ K * (3 * (P / K)) := Nat.mul_le_mul_left K hcard3
    _ = 3 * (K * (P / K)) := by ring
    _ ≤ 3 * P := Nat.mul_le_mul_left 3 (Nat.mul_div_le P K)

private lemma cast_mem_badResidues_of_abs_sub_round_le {P K : ℕ} (hP : 0 < P) (hK : 0 < K)
    (m : ℤ) (h : |(m : ℝ) / (P : ℝ) - (round ((m : ℝ) / (P : ℝ)) : ℝ)| ≤ ((K : ℝ))⁻¹) :
    (m : ZMod P) ∈ badResidues P K := by
  set q : ℤ := round ((m : ℝ) / (P : ℝ))
  set k : ℤ := m - q * (P : ℤ)
  have hP_pos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr hP
  have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hk_div : (k : ℝ) / (P : ℝ) = (m : ℝ) / (P : ℝ) - (q : ℝ) := by
    have hP_ne : (P : ℝ) ≠ 0 := ne_of_gt hP_pos
    rw [div_eq_iff hP_ne, sub_mul, div_mul_cancel₀ _ hP_ne]
    dsimp only [k]
    push_cast
    ring
  have habs_div : |(k : ℝ)| / (P : ℝ) ≤ 1 / (K : ℝ) := by
    rw [← abs_of_pos hP_pos, ← abs_div, hk_div, one_div]
    exact h
  have habs_mul : |(k : ℝ)| * (K : ℝ) ≤ (P : ℝ) := by
    rwa [div_le_div_iff₀ hP_pos hK_pos, one_mul] at habs_div
  have hnat_mul : k.natAbs * K ≤ P := by
    have hk_abs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    have hcast : ((k.natAbs * K : ℕ) : ℝ) ≤ (P : ℝ) := by
      rw [Nat.cast_mul, hk_abs]
      exact habs_mul
    exact_mod_cast hcast
  have hnat_le : k.natAbs ≤ P / K := (Nat.le_div_iff_mul_le hK).mpr hnat_mul
  have hk_Icc : k ∈ Finset.Icc (-(P / K : ℤ)) (P / K : ℤ) := by
    rw [Finset.mem_Icc]
    have habs_int : |k| ≤ (P / K : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hnat_le
    exact abs_le.mp habs_int
  rw [badResidues, Finset.mem_image]
  refine ⟨k, hk_Icc, ?_⟩
  have hm_eq : m = k + q * (P : ℤ) := by omega
  conv_rhs => rw [hm_eq]
  push_cast
  simp

private lemma surjective_addMonoidHom_card_preimage {G H : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (f : G →+ H) (hf : Function.Surjective f) (T : Finset H) :
    Fintype.card H * (Finset.univ.filter (fun g : G => f g ∈ T)).card =
      T.card * Fintype.card G := by
  let K : Finset G := Finset.univ.filter (fun g : G => f g = 0)
  have hfiber : ∀ y : H, (Finset.univ.filter (fun g : G => f g = y)).card = K.card := by
    intro y
    obtain ⟨g₀, hg₀⟩ := hf y
    symm
    refine Finset.card_bij (fun k _ => k + g₀) ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨Finset.mem_univ _, by rw [map_add, hk.2, zero_add, hg₀]⟩
    · intro k₁ _ k₂ _ h
      exact add_right_cancel h
    · intro g hg
      rw [Finset.mem_filter] at hg
      refine ⟨g - g₀, ?_, sub_add_cancel g g₀⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [map_sub, hg.2, hg₀, sub_self]⟩
  have hsum : ∀ S : Finset H,
      (Finset.univ.filter (fun g : G => f g ∈ S)).card = S.card * K.card := by
    intro S
    have hbi : Finset.univ.filter (fun g : G => f g ∈ S) =
        S.biUnion (fun y => Finset.univ.filter (fun g : G => f g = y)) := by
      ext g
      simp
    rw [hbi, Finset.card_biUnion]
    · simp [hfiber]
    · intro y₁ _ y₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro g hg₁ hg₂
      rw [Finset.mem_filter] at hg₁ hg₂
      exact hne (hg₁.2.symm.trans hg₂.2)
  have huniv : Fintype.card G = Fintype.card H * K.card := by
    simpa using hsum Finset.univ
  rw [hsum T, huniv]
  ring

private lemma zmod_natCast_ne_zero {P d : ℕ} (hd1 : 1 ≤ d) (hdP : d < P) : (d : ZMod P) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact Nat.not_dvd_of_pos_of_lt hd1 hdP h0

private lemma zmod_intCast_ne_zero {P : ℕ} {z : ℤ} (hz0 : z ≠ 0) (hzP : z.natAbs < P) :
    (z : ZMod P) ≠ 0 := by
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hz0) hzP (Int.natCast_dvd.mp h0)

private lemma extract_linearIndependent_of_finrank {D r : ℕ} (S : Set (Fin D → ℚ))
    (hr : r ≤ Module.finrank ℚ (Submodule.span ℚ S)) :
    ∃ g : Fin r → (Fin D → ℚ), (∀ i, g i ∈ S) ∧ LinearIndependent ℚ g := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℚ S
  have : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hspan' : Submodule.span ℚ (Set.range ((↑) : b → Fin D → ℚ)) = Submodule.span ℚ S := by
    rwa [Subtype.range_coe]
  let B : Module.Basis b ℚ (Submodule.span ℚ S) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan')
  have hcard : r ≤ Fintype.card b := by
    rwa [Module.finrank_eq_card_basis B] at hr
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := b) (by simpa using hcard)
  refine ⟨fun i => (emb i : Fin D → ℚ), fun i => hbS (emb i).2, ?_⟩
  exact hli.comp emb emb.injective

private lemma exists_det_ne_zero_of_linearIndependent {r D : ℕ} (M : Matrix (Fin r) (Fin D) ℚ)
    (hli : LinearIndependent ℚ (fun i : Fin r => M i)) :
    ∃ ι : Fin r → Fin D, (M.submatrix id ι).det ≠ 0 := by
  induction r with
  | zero =>
    exact ⟨Fin.elim0, by simp⟩
  | succ r ih =>
    let M' : Matrix (Fin r) (Fin D) ℚ := M.submatrix Fin.succ id
    have hli' : LinearIndependent ℚ (fun i : Fin r => M' i) :=
      hli.comp Fin.succ (Fin.succ_injective r)
    obtain ⟨ι', hdetB⟩ := ih M' hli'
    let B : Matrix (Fin r) (Fin r) ℚ := M'.submatrix id ι'
    have hB_unit : IsUnit B.det := Ne.isUnit hdetB
    let u : Fin r → ℚ := fun j => M 0 (ι' j)
    let c : Fin r → ℚ := B⁻¹.vecMul u
    have hc_eq : B.vecMul c = u := by
      dsimp only [c]
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hB_unit, Matrix.vecMul_one]
    let w : Fin D → ℚ := M 0 - ∑ i : Fin r, c i • M i.succ
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hrel : (1 : ℚ) • M 0 + ∑ i : Fin r, (-c i) • M i.succ = 0 := by
        ext b
        have hwb : w b = 0 := congrFun hw0 b
        dsimp only [w] at hwb
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
          smul_eq_mul, one_mul, neg_mul, Finset.sum_neg_distrib, Pi.zero_apply] at hwb ⊢
        linarith
      let coeff : Fin (r + 1) → ℚ := Fin.cons 1 (-c)
      have hsum0 : ∑ k : Fin (r + 1), coeff k • M k = 0 := by
        rw [Fin.sum_univ_succ]
        simpa [coeff] using hrel
      have hcoeff0 : coeff 0 = 0 :=
        Fintype.linearIndependent_iff.mp hli coeff hsum0 0
      simp [coeff] at hcoeff0
    obtain ⟨b₀, hb₀⟩ := Function.ne_iff.mp hw_ne
    let ι : Fin (r + 1) → Fin D := Fin.cons b₀ ι'
    refine ⟨ι, ?_⟩
    let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ := M.submatrix id ι
    let E : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ :=
      Matrix.of (Fin.cons (Fin.cons 1 (-c)) (fun i => Fin.cons 0 (Pi.single i 1)))
    have hEA_00 : (E * A) 0 0 = w b₀ := by
      simp only [Matrix.mul_apply, Fin.sum_univ_succ, E, A, ι, w, Matrix.of_apply,
        Fin.cons_zero, Fin.cons_succ, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
        Matrix.submatrix_apply, id_eq, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hEA_0succ : ∀ j : Fin r, (E * A) 0 j.succ = 0 := by
      intro j
      have hcj : (B.vecMul c) j = u j := congrFun hc_eq j
      dsimp only [Matrix.vecMul, dotProduct, B, M', u, Matrix.submatrix_apply, id_eq] at hcj
      simp only [Matrix.mul_apply, Fin.sum_univ_succ, E, A, ι, Matrix.of_apply,
        Fin.cons_zero, Fin.cons_succ, Pi.neg_apply, one_mul, neg_mul,
        Finset.sum_neg_distrib, Matrix.submatrix_apply, id_eq]
      linarith
    have hEA_sub : (E * A).submatrix Fin.succ Fin.succ = B := by
      ext i j
      simp [Matrix.mul_apply, Fin.sum_univ_succ, E, A, B, M', ι, Pi.single_apply]
    have hdetEA : (E * A).det = w b₀ * B.det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      simp [hEA_00, hEA_0succ, hEA_sub]
    have hdetEA_ne : (E * A).det ≠ 0 := by
      rw [hdetEA]
      exact mul_ne_zero hb₀ hdetB
    rw [Matrix.det_mul] at hdetEA_ne
    exact right_ne_zero_of_mul hdetEA_ne

private lemma det_natAbs_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (B : ℕ)
    (hA : ∀ i j, |A i j| ≤ (B : ℤ)) :
    A.det.natAbs ≤ r.factorial * B ^ r := by
  have hdet_abs : |A.det| ≤ (r.factorial : ℤ) * (B : ℤ) ^ r := by
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ • ∏ i : Fin r, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin r), |Equiv.Perm.sign σ • ∏ i : Fin r, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin r), (B : ℤ) ^ r := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hterm : |Equiv.Perm.sign σ • ∏ i : Fin r, A (σ i) i| =
              ∏ i : Fin r, |A (σ i) i| := by
            rw [Units.smul_def, zsmul_eq_mul, abs_mul, Finset.abs_prod]
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
          rw [hterm]
          calc ∏ i : Fin r, |A (σ i) i|
              ≤ ∏ _i : Fin r, (B : ℤ) :=
                Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
            _ = (B : ℤ) ^ r := by simp
      _ = (r.factorial : ℤ) * (B : ℤ) ^ r := by
          simp [Fintype.card_perm]
  have hcast : (A.det.natAbs : ℤ) ≤ ((r.factorial * B ^ r : ℕ) : ℤ) := by
    simpa [Int.natCast_natAbs] using hdet_abs
  exact Int.ofNat_le.mp hcast

private def evalHom (P D r d : ℕ) (ξ : Fin r → Fin D → ℤ) :
    (Fin D → ZMod P) →+ (Fin r → ZMod P) where
  toFun v i := (d : ZMod P) * ∑ b : Fin D, (ξ i b : ZMod P) * v b
  map_zero' := by ext i; simp
  map_add' u v := by ext i; simp [mul_add, Finset.sum_add_distrib]

private lemma evalHom_surjective {P D r d B : ℕ} [Fact P.Prime]
    (hd1 : 1 ≤ d) (hdP : d < P)
    (ξ : Fin r → Fin D → ℤ) (hξB : ∀ i b, |ξ i b| ≤ (B : ℤ))
    (hli : LinearIndependent ℚ (fun i : Fin r => fun b : Fin D => (ξ i b : ℚ)))
    (hBP : r.factorial * B ^ r < P) :
    Function.Surjective (evalHom P D r d ξ) := by
  let Mℚ : Matrix (Fin r) (Fin D) ℚ := Matrix.of (fun i b => (ξ i b : ℚ))
  obtain ⟨ι, hdetℚ⟩ := exists_det_ne_zero_of_linearIndependent Mℚ hli
  let Aℤ : Matrix (Fin r) (Fin r) ℤ := Matrix.of (fun i j => ξ i (ι j))
  have hmapℚ : (Int.castRingHom ℚ).mapMatrix Aℤ = Mℚ.submatrix id ι := by
    ext i j
    simp [Aℤ, Mℚ]
  have hdetℤ_ne : Aℤ.det ≠ 0 := by
    intro h0
    apply hdetℚ
    rw [← hmapℚ, ← RingHom.map_det, h0, map_zero]
  have hdetℤ_lt : Aℤ.det.natAbs < P :=
    lt_of_le_of_lt (det_natAbs_le Aℤ B (fun i j => hξB i (ι j))) hBP
  have hdetP_ne : (Aℤ.det : ZMod P) ≠ 0 := zmod_intCast_ne_zero hdetℤ_ne hdetℤ_lt
  let AP : Matrix (Fin r) (Fin r) (ZMod P) := (Int.castRingHom (ZMod P)).mapMatrix Aℤ
  have hAP_det : AP.det ≠ 0 := by
    rw [← RingHom.map_det]
    exact hdetP_ne
  have hAP_unit : IsUnit AP.det := Ne.isUnit hAP_det
  have hd_ne : (d : ZMod P) ≠ 0 := zmod_natCast_ne_zero hd1 hdP
  intro y
  let w : Fin r → ZMod P := AP⁻¹.mulVec (fun i => (d : ZMod P)⁻¹ * y i)
  have hw_eq : AP.mulVec w = fun i => (d : ZMod P)⁻¹ * y i := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAP_unit, Matrix.one_mulVec]
  let v : Fin D → ZMod P := fun b => ∑ j : Fin r, if b = ι j then w j else 0
  refine ⟨v, ?_⟩
  ext i
  have hsum_eq : ∑ b : Fin D, (ξ i b : ZMod P) * v b = (AP.mulVec w) i := by
    dsimp only [v, AP, Aℤ, Matrix.mulVec, dotProduct]
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  change (d : ZMod P) * ∑ b : Fin D, (ξ i b : ZMod P) * v b = y i
  rw [hsum_eq, congrFun hw_eq i, mul_inv_cancel_left₀ hd_ne]

private def badSet1 (P D N K₁ : ℕ) [Fact P.Prime] : Finset (Fin D → ZMod P) :=
  (Finset.Icc 1 N).biUnion (fun d =>
    Fintype.piFinset (fun _ : Fin D =>
      (badResidues P K₁).image (fun y => (d : ZMod P)⁻¹ * y)))

private lemma card_badSet1_lt {P D N K₁ : ℕ} [Fact P.Prime]
    (hP : 0 < P) (hK₁ : 0 < K₁) (hK₁P : K₁ ≤ P)
    (hexp1 : 2 * N * 3 ^ D < K₁ ^ D) :
    2 * (badSet1 P D N K₁).card < P ^ D := by
  let badCoord (d : ℕ) : Finset (ZMod P) :=
    (badResidues P K₁).image (fun y => (d : ZMod P)⁻¹ * y)
  let badV (d : ℕ) : Finset (Fin D → ZMod P) :=
    Fintype.piFinset (fun _ : Fin D => badCoord d)
  have hbadV_bound : ∀ d ∈ Finset.Icc 1 N, K₁ ^ D * (badV d).card ≤ 3 ^ D * P ^ D := by
    intro d _
    have hcard_coord : (badCoord d).card ≤ (badResidues P K₁).card := Finset.card_image_le
    have hmul : K₁ * (badCoord d).card ≤ 3 * P :=
      (Nat.mul_le_mul_left K₁ hcard_coord).trans (card_badResidues_mul_le hK₁ hK₁P)
    have hpi : (badV d).card = (badCoord d).card ^ D := by simp [badV]
    rw [hpi, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left hmul D
  have hbi : (badSet1 P D N K₁).card ≤ ∑ d ∈ Finset.Icc 1 N, (badV d).card :=
    Finset.card_biUnion_le
  have hsum : K₁ ^ D * (badSet1 P D N K₁).card ≤ N * (3 ^ D * P ^ D) := by
    calc K₁ ^ D * (badSet1 P D N K₁).card
        ≤ K₁ ^ D * ∑ d ∈ Finset.Icc 1 N, (badV d).card := Nat.mul_le_mul_left _ hbi
      _ = ∑ d ∈ Finset.Icc 1 N, K₁ ^ D * (badV d).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 N, 3 ^ D * P ^ D := Finset.sum_le_sum hbadV_bound
      _ = N * (3 ^ D * P ^ D) := by simp
  have h2sum : K₁ ^ D * (2 * (badSet1 P D N K₁).card) ≤ (2 * N * 3 ^ D) * P ^ D := by
    calc K₁ ^ D * (2 * (badSet1 P D N K₁).card)
        = 2 * (K₁ ^ D * (badSet1 P D N K₁).card) := by ring
      _ ≤ 2 * (N * (3 ^ D * P ^ D)) := Nat.mul_le_mul_left 2 hsum
      _ = (2 * N * 3 ^ D) * P ^ D := by ring
  have hstrict : K₁ ^ D * (2 * (badSet1 P D N K₁).card) < K₁ ^ D * P ^ D :=
    lt_of_le_of_lt h2sum (Nat.mul_lt_mul_of_pos_right hexp1 (pow_pos hP D))
  exact Nat.lt_of_mul_lt_mul_left hstrict

private def indepBoundedTuples (D r B : ℕ) : Finset (Fin r → Fin D → ℤ) :=
  (Fintype.piFinset (fun _ : Fin r =>
    Fintype.piFinset (fun _ : Fin D => Finset.Icc (-(B : ℤ)) (B : ℤ)))).filter
    (fun ξ => LinearIndependent ℚ (fun i : Fin r => fun b : Fin D => (ξ i b : ℚ)))

private lemma card_indepBoundedTuples_le {D r B : ℕ} (hD3 : 3 ≤ D) (hB : 1 ≤ B) :
    (indepBoundedTuples D r B).card ≤ (D * B) ^ (D * r) := by
  have hIcc : (Finset.Icc (-(B : ℤ)) (B : ℤ)).card ≤ D * B := by
    have hc : (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
      rw [Int.card_Icc]
      omega
    have h1 : 2 * B + 1 ≤ 3 * B := by omega
    exact hc ▸ h1.trans (Nat.mul_le_mul_right B hD3)
  let box : Finset (Fin D → ℤ) :=
    Fintype.piFinset (fun _ : Fin D => Finset.Icc (-(B : ℤ)) (B : ℤ))
  have hbox : box.card ≤ (D * B) ^ D := by
    have hb : box.card = (Finset.Icc (-(B : ℤ)) (B : ℤ)).card ^ D := by simp [box]
    rw [hb]
    exact Nat.pow_le_pow_left hIcc D
  let tuples : Finset (Fin r → Fin D → ℤ) := Fintype.piFinset (fun _ : Fin r => box)
  have htuples : tuples.card ≤ (D * B) ^ (D * r) := by
    have ht : tuples.card = box.card ^ r := by simp [tuples]
    rw [ht, pow_mul]
    exact Nat.pow_le_pow_left hbox r
  exact (Finset.card_filter_le _ _).trans htuples

private def badSet2 (P D r N B K₂ : ℕ) [Fact P.Prime] : Finset (Fin D → ZMod P) :=
  let T₂ : Finset (Fin r → ZMod P) := Fintype.piFinset (fun _ : Fin r => badResidues P K₂)
  (Finset.Icc 1 N).biUnion (fun d =>
    (indepBoundedTuples D r B).biUnion (fun ξ =>
      Finset.univ.filter (fun v : Fin D → ZMod P => evalHom P D r d ξ v ∈ T₂)))

private lemma card_badSet2_lt {P D r N B K₂ : ℕ} [Fact P.Prime]
    (hP : 0 < P) (hNP : N < P) (hK₂ : 0 < K₂) (hK₂P : K₂ ≤ P)
    (hBP : r.factorial * B ^ r < P)
    (hexp2 : 2 * N * (indepBoundedTuples D r B).card * 3 ^ r < K₂ ^ r) :
    2 * (badSet2 P D r N B K₂).card < P ^ D := by
  let T₂ : Finset (Fin r → ZMod P) := Fintype.piFinset (fun _ : Fin r => badResidues P K₂)
  have hT₂_bound : K₂ ^ r * T₂.card ≤ 3 ^ r * P ^ r := by
    have hT₂_eq : T₂.card = (badResidues P K₂).card ^ r := by simp [T₂]
    rw [hT₂_eq, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (card_badResidues_mul_le hK₂ hK₂P) r
  let badV (d : ℕ) (ξ : Fin r → Fin D → ℤ) : Finset (Fin D → ZMod P) :=
    Finset.univ.filter (fun v : Fin D → ZMod P => evalHom P D r d ξ v ∈ T₂)
  have hbadV_bound : ∀ d ∈ Finset.Icc 1 N, ∀ ξ ∈ indepBoundedTuples D r B,
      K₂ ^ r * (badV d ξ).card ≤ 3 ^ r * P ^ D := by
    intro d hd ξ hξ
    rw [Finset.mem_Icc] at hd
    rw [indepBoundedTuples, Finset.mem_filter] at hξ
    have hξB : ∀ i b, |ξ i b| ≤ (B : ℤ) := by
      intro i b
      have h1 := (Fintype.mem_piFinset.mp hξ.1) i
      have h2 := (Fintype.mem_piFinset.mp h1) b
      rw [Finset.mem_Icc] at h2
      exact abs_le.mpr h2
    have hsurj : Function.Surjective (evalHom P D r d ξ) :=
      evalHom_surjective hd.1 (lt_of_le_of_lt hd.2 hNP) ξ hξB hξ.2 hBP
    have hfib := surjective_addMonoidHom_card_preimage (evalHom P D r d ξ) hsurj T₂
    have hcardH : Fintype.card (Fin r → ZMod P) = P ^ r := by simp
    have hcardG : Fintype.card (Fin D → ZMod P) = P ^ D := by simp
    rw [hcardH, hcardG] at hfib
    have hmul : P ^ r * (K₂ ^ r * (badV d ξ).card) ≤ P ^ r * (3 ^ r * P ^ D) := by
      calc P ^ r * (K₂ ^ r * (badV d ξ).card)
          = K₂ ^ r * (P ^ r * (badV d ξ).card) := by ring
        _ = (K₂ ^ r * T₂.card) * P ^ D := by rw [hfib]; ring
        _ ≤ (3 ^ r * P ^ r) * P ^ D := Nat.mul_le_mul_right _ hT₂_bound
        _ = P ^ r * (3 ^ r * P ^ D) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos hP r)
  let S := indepBoundedTuples D r B
  have hinner : ∀ d ∈ Finset.Icc 1 N,
      K₂ ^ r * (S.biUnion (fun ξ => badV d ξ)).card ≤ S.card * (3 ^ r * P ^ D) := by
    intro d hd
    calc K₂ ^ r * (S.biUnion (fun ξ => badV d ξ)).card
        ≤ K₂ ^ r * ∑ ξ ∈ S, (badV d ξ).card := Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ ξ ∈ S, K₂ ^ r * (badV d ξ).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _ξ ∈ S, 3 ^ r * P ^ D := Finset.sum_le_sum (fun ξ hξ => hbadV_bound d hd ξ hξ)
      _ = S.card * (3 ^ r * P ^ D) := by simp
  have houter : K₂ ^ r * (badSet2 P D r N B K₂).card ≤ N * (S.card * (3 ^ r * P ^ D)) := by
    calc K₂ ^ r * (badSet2 P D r N B K₂).card
        ≤ K₂ ^ r * ∑ d ∈ Finset.Icc 1 N, (S.biUnion (fun ξ => badV d ξ)).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ d ∈ Finset.Icc 1 N, K₂ ^ r * (S.biUnion (fun ξ => badV d ξ)).card :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 N, S.card * (3 ^ r * P ^ D) := Finset.sum_le_sum hinner
      _ = N * (S.card * (3 ^ r * P ^ D)) := by simp
  have h2outer : K₂ ^ r * (2 * (badSet2 P D r N B K₂).card) ≤
      (2 * N * S.card * 3 ^ r) * P ^ D := by
    calc K₂ ^ r * (2 * (badSet2 P D r N B K₂).card)
        = 2 * (K₂ ^ r * (badSet2 P D r N B K₂).card) := by ring
      _ ≤ 2 * (N * (S.card * (3 ^ r * P ^ D))) := Nat.mul_le_mul_left 2 houter
      _ = (2 * N * S.card * 3 ^ r) * P ^ D := by ring
  have hstrict : K₂ ^ r * (2 * (badSet2 P D r N B K₂).card) < K₂ ^ r * P ^ D :=
    lt_of_le_of_lt h2outer (Nat.mul_lt_mul_of_pos_right hexp2 (pow_pos hP D))
  exact Nat.lt_of_mul_lt_mul_left hstrict

private lemma exp1_le {t D : ℕ} (ht : 2 ≤ t) (hD : D = 200 * t) :
    1 + 200 * t ^ 2 + D ≤ 2 * t * D := by
  subst hD
  nlinarith

private lemma exp2_le {t D r : ℕ} (ht : 2 ≤ t) (hD : D = 200 * t) (hr : r = 2 * t + 1) :
    1 + 200 * t ^ 2 + 13 * D * r + r ≤ 8400 * t * r := by
  subst hD hr
  nlinarith

private lemma h2_for_params (t D N X r B K₁ K₂ : ℕ) (ht : 2 ≤ t)
    (hD : D = 200 * t) (hN : N = D ^ (200 * t ^ 2)) (hX : X = D ^ (10000 * t))
    (hr : r = 2 * t + 1) (hB : B = D ^ 12)
    (hK₁ : K₁ = 2 * D ^ (2 * t)) (hK₂ : K₂ = D ^ (8400 * t)) :
    ∃ θ : Fin D → ℝ,
      (∀ d : ℕ, 1 ≤ d → d ≤ N →
        ∃ b : Fin D, (2 * (D : ℝ) ^ (2 * t))⁻¹ <
          |(d : ℝ) * θ b - (round ((d : ℝ) * θ b) : ℝ)|) ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ N →
        Module.finrank ℚ (Submodule.span ℚ
          ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) ''
            {ξ : Fin D → ℤ | (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) ∧
              |(d : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b) -
                (round ((d : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b)) : ℝ)| ≤
                (D : ℝ) ^ (8 * D) / (X : ℝ)})) ≤ 2 * t) := by
  have hD_ge : 200 ≤ D := by omega
  have hD_pos : 0 < D := by omega
  have hr_le_D : r ≤ D := by omega
  have hN_pos : 0 < N := hN ▸ pow_pos hD_pos _
  have hB_pos : 1 ≤ B := hB ▸ Nat.one_le_pow 12 D hD_pos
  have hK₁_pos : 0 < K₁ := hK₁ ▸ Nat.mul_pos (by omega) (pow_pos hD_pos _)
  have hK₂_pos : 0 < K₂ := hK₂ ▸ pow_pos hD_pos _
  obtain ⟨P, hP_ge, hP_prime⟩ := Nat.exists_infinite_primes (N + X + 1)
  have _ : Fact P.Prime := ⟨hP_prime⟩
  have hP_pos : 0 < P := hP_prime.pos
  have hN_lt_P : N < P := by omega
  have hX_lt_P : X < P := by omega
  have hK₁_le_P : K₁ ≤ P := by
    have h1 : K₁ < D * D ^ (2 * t) := by
      rw [hK₁]
      exact Nat.mul_lt_mul_of_pos_right (by omega : 2 < D) (pow_pos hD_pos _)
    have h2 : D * D ^ (2 * t) = D ^ (2 * t + 1) := (pow_succ' D (2 * t)).symm
    have h3 : D ^ (2 * t + 1) ≤ X := by
      rw [hX]
      exact Nat.pow_le_pow_right hD_pos (by omega)
    omega
  have hK₂_le_P : K₂ ≤ P := by
    have h1 : K₂ ≤ X := by
      rw [hK₂, hX]
      exact Nat.pow_le_pow_right hD_pos (by omega)
    omega
  have hdet_bound_P : r.factorial * B ^ r < P := by
    have h1 : r.factorial ≤ D ^ r :=
      (Nat.factorial_le_pow r).trans (Nat.pow_le_pow_left hr_le_D r)
    have h2 : r.factorial * B ^ r ≤ D ^ (13 * r) := by
      calc r.factorial * B ^ r
          ≤ D ^ r * B ^ r := Nat.mul_le_mul_right _ h1
        _ = D ^ r * D ^ (12 * r) := by rw [hB, ← pow_mul]
        _ = D ^ (13 * r) := by rw [← pow_add]; congr 1; ring
    have h3 : D ^ (13 * r) ≤ X := by
      rw [hX]
      exact Nat.pow_le_pow_right hD_pos (by omega)
    omega
  have hexp1 : 2 * N * 3 ^ D < K₁ ^ D := by
    have h3D : 3 ^ D ≤ D ^ D := Nat.pow_le_pow_left (by omega : 3 ≤ D) D
    have hpos1 : 0 < N * D ^ D := mul_pos hN_pos (pow_pos hD_pos D)
    have hexp_le : 1 + 200 * t ^ 2 + D ≤ 2 * t * D := exp1_le ht hD
    calc 2 * N * 3 ^ D
        ≤ 2 * (N * D ^ D) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left N h3D)
      _ < D * (N * D ^ D) := Nat.mul_lt_mul_of_pos_right (by omega : 2 < D) hpos1
      _ = D ^ (1 + 200 * t ^ 2 + D) := by
          rw [hN, ← pow_add, ← pow_succ']
          congr 1
          ring
      _ ≤ D ^ (2 * t * D) := Nat.pow_le_pow_right hD_pos hexp_le
      _ = (D ^ (2 * t)) ^ D := pow_mul D (2 * t) D
      _ ≤ K₁ ^ D := by
          rw [hK₁]
          exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by omega : 0 < 2)) D
  have hexp2 : 2 * N * (indepBoundedTuples D r B).card * 3 ^ r < K₂ ^ r := by
    have hindep : (indepBoundedTuples D r B).card ≤ D ^ (13 * D * r) := by
      have hcard := card_indepBoundedTuples_le (r := r) (by omega : 3 ≤ D) hB_pos
      have hDB : (D * B) ^ (D * r) = D ^ (13 * D * r) := by
        rw [hB, ← pow_succ', ← pow_mul]
        congr 1
        ring
      rwa [hDB] at hcard
    have h3r : 3 ^ r ≤ D ^ r := Nat.pow_le_pow_left (by omega : 3 ≤ D) r
    have hpos2 : 0 < N * D ^ (13 * D * r) * D ^ r :=
      mul_pos (mul_pos hN_pos (pow_pos hD_pos _)) (pow_pos hD_pos _)
    have hexp_le : 1 + 200 * t ^ 2 + 13 * D * r + r ≤ 8400 * t * r := exp2_le ht hD hr
    calc 2 * N * (indepBoundedTuples D r B).card * 3 ^ r
        ≤ 2 * (N * D ^ (13 * D * r) * D ^ r) := by
          have hmul1 : (indepBoundedTuples D r B).card * 3 ^ r ≤ D ^ (13 * D * r) * D ^ r :=
            Nat.mul_le_mul hindep h3r
          calc 2 * N * (indepBoundedTuples D r B).card * 3 ^ r
              = 2 * (N * ((indepBoundedTuples D r B).card * 3 ^ r)) := by ring
            _ ≤ 2 * (N * (D ^ (13 * D * r) * D ^ r)) :=
                Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left N hmul1)
            _ = 2 * (N * D ^ (13 * D * r) * D ^ r) := by ring
      _ < D * (N * D ^ (13 * D * r) * D ^ r) :=
          Nat.mul_lt_mul_of_pos_right (by omega : 2 < D) hpos2
      _ = D ^ (1 + 200 * t ^ 2 + 13 * D * r + r) := by
          rw [hN, ← pow_add, ← pow_add, ← pow_succ']
          congr 1
          ring
      _ ≤ D ^ (8400 * t * r) := Nat.pow_le_pow_right hD_pos hexp_le
      _ = K₂ ^ r := by rw [hK₂, pow_mul]
  have hbad1_lt : 2 * (badSet1 P D N K₁).card < P ^ D :=
    card_badSet1_lt hP_pos hK₁_pos hK₁_le_P hexp1
  have hbad2_lt : 2 * (badSet2 P D r N B K₂).card < P ^ D :=
    card_badSet2_lt hP_pos hN_lt_P hK₂_pos hK₂_le_P hdet_bound_P hexp2
  have hunion_lt :
      (badSet1 P D N K₁ ∪ badSet2 P D r N B K₂).card <
        (Finset.univ : Finset (Fin D → ZMod P)).card := by
    have hu := Finset.card_union_le (badSet1 P D N K₁) (badSet2 P D r N B K₂)
    have huniv_card : (Finset.univ : Finset (Fin D → ZMod P)).card = P ^ D := by simp
    rw [huniv_card]
    omega
  have hsdiff_ne :
      ((Finset.univ : Finset (Fin D → ZMod P)) \
        (badSet1 P D N K₁ ∪ badSet2 P D r N B K₂)).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h_empty
    exact absurd (Finset.card_le_card h_empty) (not_le_of_gt hunion_lt)
  obtain ⟨v, hv⟩ := hsdiff_ne
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hv
  obtain ⟨_, hv1, hv2⟩ := hv
  let θ : Fin D → ℝ := fun b => ((v b).val : ℝ) / (P : ℝ)
  refine ⟨θ, ?_, ?_⟩
  · intro d hd1 hdN
    by_contra hbad
    push Not at hbad
    apply hv1
    rw [badSet1, Finset.mem_biUnion]
    refine ⟨d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩, Fintype.mem_piFinset.mpr fun b => ?_⟩
    let m : ℤ := (d : ℤ) * ((v b).val : ℤ)
    have hm_div : (m : ℝ) / (P : ℝ) = (d : ℝ) * θ b := by
      dsimp only [m, θ]
      push_cast
      ring
    have hK₁_cast : ((K₁ : ℝ))⁻¹ = (2 * (D : ℝ) ^ (2 * t))⁻¹ := by
      rw [hK₁]
      push_cast
      rfl
    have hm_mem : (m : ZMod P) ∈ badResidues P K₁ := by
      apply cast_mem_badResidues_of_abs_sub_round_le hP_pos hK₁_pos m
      rw [hm_div, hK₁_cast]
      exact hbad b
    have hm_zmod : (m : ZMod P) = (d : ZMod P) * v b := by
      dsimp only [m]
      push_cast
      rw [ZMod.natCast_zmod_val]
    have hd_ne : (d : ZMod P) ≠ 0 := zmod_natCast_ne_zero hd1 (lt_of_le_of_lt hdN hN_lt_P)
    rw [Finset.mem_image]
    exact ⟨(m : ZMod P), hm_mem, by rw [hm_zmod, inv_mul_cancel_left₀ hd_ne]⟩
  · intro d hd1 hdN
    by_contra hbad
    have hr_le : r ≤ Module.finrank ℚ (Submodule.span ℚ
        ((fun (ξ : Fin D → ℤ) (b : Fin D) => (ξ b : ℚ)) ''
          {ξ : Fin D → ℤ | (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) ∧
            |(d : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b) -
              (round ((d : ℝ) * (∑ b : Fin D, (ξ b : ℝ) * θ b)) : ℝ)| ≤
              (D : ℝ) ^ (8 * D) / (X : ℝ)})) := by
      omega
    obtain ⟨g, hg_mem, hg_li⟩ := extract_linearIndependent_of_finrank _ hr_le
    choose ξ hξ_set hξ_eq using hg_mem
    have hξ_li : LinearIndependent ℚ (fun i : Fin r => fun b : Fin D => (ξ i b : ℚ)) := by
      convert hg_li using 1
      ext i b
      exact congrFun (hξ_eq i) b
    have hξ_indep : ξ ∈ indepBoundedTuples D r B := by
      rw [indepBoundedTuples, Finset.mem_filter]
      refine ⟨Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mpr fun b => ?_, hξ_li⟩
      rw [Finset.mem_Icc]
      have hb_cast : (B : ℤ) = (D : ℤ) ^ 12 := by rw [hB]; push_cast; rfl
      rw [hb_cast]
      exact abs_le.mp ((hξ_set i).1 b)
    have hratio : (D : ℝ) ^ (8 * D) / (X : ℝ) = ((K₂ : ℝ))⁻¹ := by
      have hX_split : X = D ^ (8 * D) * K₂ := by
        rw [hX, hK₂, ← pow_add]
        congr 1
        omega
      have hD8_ne : (D : ℝ) ^ (8 * D) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
      rw [hX_split, Nat.cast_mul, Nat.cast_pow, div_mul_eq_div_div, div_self hD8_ne, one_div]
    apply hv2
    rw [badSet2, Finset.mem_biUnion]
    refine ⟨d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨ξ, hξ_indep, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun i => ?_⟩
    let m : ℤ := (d : ℤ) * ∑ b : Fin D, ξ i b * ((v b).val : ℤ)
    have hm_div : (m : ℝ) / (P : ℝ) = (d : ℝ) * ∑ b : Fin D, (ξ i b : ℝ) * θ b := by
      dsimp only [m, θ]
      push_cast
      simp only [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hm_mem : (m : ZMod P) ∈ badResidues P K₂ := by
      apply cast_mem_badResidues_of_abs_sub_round_le hP_pos hK₂_pos m
      rw [hm_div, ← hratio]
      exact (hξ_set i).2
    have hm_zmod : (m : ZMod P) = evalHom P D r d ξ v i := by
      dsimp only [m, evalHom]
      push_cast
      simp
    rwa [← hm_zmod]

end

end Green14PolyH2Proof

theorem OMA.solution : OMA.R_Green14_green_14_polynomial_R1.H2 := by
  exact ⟨2, fun t ht =>
    Green14PolyH2Proof.h2_for_params t _ _ _ _ _ _ _ ht rfl rfl rfl rfl rfl rfl rfl⟩
