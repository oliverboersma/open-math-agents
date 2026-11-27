import FormalConjectures.ErdosProblems.«510»
import Mathlib

/-! A kernel-checked counterexample to Chowla’s cosine conjecture. -/

/-
Original counterexample by Shengtong Zhang and formalization contributors.
Apache-2.0 source: https://github.com/shengtongz/chowla-cosine-counterexample/tree/23b05e1a1668ee82b595de99a9e870db95adb927
Adapted by inlining the source modules and targeting the pinned Formal Conjectures declaration.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/- Adapted from ChowlaOpus/Basic.lean. -/
section

/-
# Basic notation for the counterexample to Chowla's cosine conjecture

Notation shared by all components: `ee x = exp(2πix)`, the cosine sum `cosineSum`,
multiplicative independence, trigonometric polynomials in several variables, Fejér
coefficients and kernels, and the characters and Gauss-type sums modulo `p²` used in §4–§5.
-/

open scoped FourierTransform
open Real MeasureTheory

namespace ChowlaOpus

/-- `ee x = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

lemma ee_ne_zero (x : ℝ) : ee x ≠ 0 := Complex.exp_ne_zero _

lemma ee_intCast (n : ℤ) : ee n = 1 := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * Complex.I * (n : ℝ) = n * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma ee_add_intCast (x : ℝ) (n : ℤ) : ee (x + n) = ee x := by
  rw [ee_add, ee_intCast, mul_one]

lemma ee_neg (x : ℝ) : ee (-x) = starRingEnd ℂ (ee x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

lemma ee_re (x : ℝ) : (ee x).re = Real.cos (2 * Real.pi * x) := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℝ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

lemma ee_im (x : ℝ) : (ee x).im = Real.sin (2 * Real.pi * x) := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℝ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im]

lemma ee_mul_intCast (x : ℝ) (n : ℤ) : ee (x * n) = ee x ^ n := by
  unfold ee
  rw [← Complex.exp_int_mul]
  congr 1; push_cast; ring

lemma fourier_eq_ee (f : ℝ → ℂ) (w : ℝ) : 𝓕 f w = ∫ v, ee (-(v * w)) * f v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; ext v
  simp only [smul_eq_mul, ee]
  congr 2
  push_cast; ring

/-- The cosine sum `f_A(t) = ∑_{a ∈ A} cos(2π a t)`. -/
noncomputable def cosineSum (A : Finset ℕ+) (t : ℝ) : ℝ :=
  ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t)

/-- Multiplicative independence of a finite family of naturals: the only integer exponent
vector giving a trivial rational product is zero. -/
def MultIndep {ι : Type*} [Fintype ι] (n : ι → ℕ) : Prop :=
  ∀ e : ι → ℤ, ∏ i, ((n i : ℚ) ^ e i) = 1 → e = 0

/-- Evaluation of a trigonometric polynomial on the torus `ℝ^k / ℤ^k` with frequency set `S`
and coefficients `f`. -/
noncomputable def trigEval {k : ℕ} (S : Finset (Fin k → ℤ)) (f : (Fin k → ℤ) → ℂ)
    (θ : Fin k → ℝ) : ℂ :=
  ∑ v ∈ S, f v * ee (∑ i, (v i : ℝ) * θ i)

/- ## Fejér kernel (definitions only) -/

/-- Fejér coefficient `(1 - |k|/(R+1))₊`. -/
noncomputable def fejerCoeff (R : ℕ) (k : ℤ) : ℝ := max 0 (1 - |(k : ℝ)| / ((R : ℝ) + 1))

/-- Fejér kernel of degree `R` on `ℝ/ℤ`, as a cosine polynomial. -/
noncomputable def fejer (R : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(R : ℤ)) R, fejerCoeff R k * Real.cos (2 * Real.pi * k * t)

lemma fejerCoeff_nonneg (R : ℕ) (k : ℤ) : 0 ≤ fejerCoeff R k := le_max_left _ _

lemma fejerCoeff_le_one (R : ℕ) (k : ℤ) : fejerCoeff R k ≤ 1 := by
  unfold fejerCoeff
  apply max_le zero_le_one
  have : 0 ≤ |(k : ℝ)| / ((R : ℝ) + 1) := by positivity
  linarith

lemma fejerCoeff_zero (R : ℕ) : fejerCoeff R 0 = 1 := by simp [fejerCoeff]

lemma fejerCoeff_neg (R : ℕ) (k : ℤ) : fejerCoeff R (-k) = fejerCoeff R k := by
  simp [fejerCoeff, abs_neg]

lemma fejerCoeff_eq_zero (R : ℕ) (k : ℤ) (h : (R : ℤ) < |k|) : fejerCoeff R k = 0 := by
  unfold fejerCoeff
  apply max_eq_left
  have h' : (R : ℝ) + 1 ≤ |(k : ℝ)| := by
    have : (R : ℤ) + 1 ≤ |k| := h
    exact_mod_cast this
  have hpos : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  rw [sub_nonpos, le_div_iff₀ hpos]; linarith

/- ## Characters modulo `p²` -/

/-- An even character mod `p²` which restricts to `1 + p t ↦ e(t/p)` on the kernel of reduction. -/
def KernelChar (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) : Prop :=
  χ (-1) = 1 ∧ ∀ t : ℤ, χ (((1 + (p : ℤ) * t : ℤ)) : ZMod (p ^ 2)) = ee ((t : ℝ) / p)

/-- The normalized Gauss phase `t_n = e(-n/p²) χ(n)^n` of display (7). -/
noncomputable def gaussPhase (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) : ℂ :=
  ee (-(n : ℝ) / (p : ℝ) ^ 2) * (χ (n : ZMod (p ^ 2))) ^ n

/-- Row sum `∑*_{r mod p²} χ(r)^n e(k r / p²)` over residues coprime to `p`. -/
noncomputable def rowSum (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (n k : ℤ) : ℂ :=
  ∑ r ∈ (Finset.range (p ^ 2)).filter (fun r => Nat.Coprime r p),
    (χ (r : ZMod (p ^ 2))) ^ n * ee ((k : ℝ) * (r : ℝ) / (p : ℝ) ^ 2)

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Profile/Defs.lean. -/
section

/-
# Definitions for §1–§2 of the paper (Lemma 2 and Lemma 3)

Conventions.
* The label variable `σ ∈ ℝ` is the logarithm of the radius; the annulus slice is
  `B_σ(x) = 1{|x| ≤ e^σ ≤ √(1+x²)}` (`annB σ x`).
* The label transform at (cyclic) frequency `ξ` is `∫ v(σ) e(-ξσ) dσ`
  (angular frequency `τ = 2πξ`).
* In Lemma 3 the label has period `T`; after rescaling `σ = T s` the label `s` has period one,
  and the `l`-th mode corresponds to `ξ = l / T`.
* `h = (T²)⁻¹`, `X = T²`.
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

/- ## The annulus slice and its label transforms -/

/-- Horizontal slice of the annulus: `B_σ(x) = 1{|x| ≤ e^σ ∧ e^{2σ} ≤ 1 + x²}`. -/
noncomputable def annB (σ x : ℝ) : ℝ :=
  if |x| ≤ Real.exp σ ∧ Real.exp σ ^ 2 ≤ 1 + x ^ 2 then 1 else 0

/-- Label mean `ℓ(x) = ∫ B_σ(x) dσ` (equal to `½ log(1 + x⁻²)` for `x ≠ 0`). -/
noncomputable def ellF (x : ℝ) : ℝ := ∫ σ, annB σ x

/-- Label transform of the slice at cyclic frequency `ξ`: `β_ξ(x) = ∫ B_σ(x) e(-ξσ) dσ`. -/
noncomputable def betaF (ξ x : ℝ) : ℂ := ∫ σ, (annB σ x : ℂ) * ee (-(ξ * σ))

/-- Periodization in the label with period `T`: `P_σ(x) = ∑_j B_{σ + jT}(x)`. -/
noncomputable def perB (T σ x : ℝ) : ℝ := ∑' j : ℤ, annB (σ + j * T) x

/- ## Bessel profile and the multiplier (Lemma 2) -/

/-- `J₀(r) = (1/2π) ∫_0^{2π} cos(r cos θ) dθ`. -/
noncomputable def J0 (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (r * Real.cos θ)

/-- `G_σ(x) = J₀(e^{-σ}|x|) - J₀(e^{-σ}√(1+x²))`. -/
noncomputable def besselG (σ x : ℝ) : ℝ :=
  J0 (Real.exp (-σ) * |x|) - J0 (Real.exp (-σ) * Real.sqrt (1 + x ^ 2))

/-- The unimodular multiplier `m(τ) = 2^{iτ} Γ(1 + iτ/2) / Γ(1 - iτ/2)`. -/
noncomputable def mult (τ : ℝ) : ℂ :=
  (2 : ℂ) ^ (Complex.I * τ) * Complex.Gamma (1 + Complex.I * τ / 2) /
    Complex.Gamma (1 - Complex.I * τ / 2)

/- ## The bump and the profile coefficients (Lemma 3) -/

/-- An even nonnegative smooth probability density supported in `[-1,1]` with real,
nonnegative Fourier transform, maximal at `0`. -/
structure IsBump (ρ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ρ
  nonneg : ∀ x, 0 ≤ ρ x
  even : ∀ x, ρ (-x) = ρ x
  supp : ∀ x, 1 ≤ |x| → ρ x = 0
  integral_eq : ∫ x, ρ x = 1
  fourier_im : ∀ y, (𝓕 (fun x => (ρ x : ℂ)) y).im = 0
  fourier_nonneg : ∀ y, 0 ≤ (𝓕 (fun x => (ρ x : ℂ)) y).re
  le_at_zero : ∀ x, ρ x ≤ ρ 0

/-- `ψ(x) = ρ(x)/ρ(0)`. -/
noncomputable def psiF (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ρ x / ρ 0

/-- `ρ_h(x) = h⁻¹ ρ(x/h)`. -/
noncomputable def rhoH (ρ : ℝ → ℝ) (h x : ℝ) : ℝ := ρ (x / h) / h

/-- The scale `h = T⁻²`. -/
noncomputable def hT (T : ℝ) : ℝ := (T ^ 2)⁻¹

/-- Normalization constant `a = 8 ρ(0) T² e^{-T}` (dominates `‖ρ_h‖_∞ · ∫ (P_σ - 1)₊`). -/
noncomputable def aT (ρ : ℝ → ℝ) (T : ℝ) : ℝ := 8 * ρ 0 * T ^ 2 * Real.exp (-T)

/-- Physically smoothed slice `(ρ_h ∗ B_σ)(x) = ∫ ρ_h(y) B_σ(x - y) dy`. -/
noncomputable def smB (ρ : ℝ → ℝ) (T σ x : ℝ) : ℝ :=
  ∫ y, rhoH ρ (hT T) y * annB σ (x - y)

/-- Physically smoothed Bessel profile `(ρ_h ∗ G_σ)(x) = ∫ ρ_h(y) G_σ(x - y) dy`. -/
noncomputable def smG (ρ : ℝ → ℝ) (T σ x : ℝ) : ℝ :=
  ∫ y, rhoH ρ (hT T) y * besselG σ (x - y)

/-- The label coefficients of Lemma 3 (label rescaled to period one):
`b_l(x) = (φ_J(l) / (T(1+a))) ψ(x/T²) (ρ_h ∗ β_{l/T})(x)`, where `φ_J` is the Fejér coefficient. -/
noncomputable def bL (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (l : ℤ) (x : ℝ) : ℂ :=
  ((fejerCoeff J l / (T * (1 + aT ρ T)) * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
    ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ((l : ℝ) / T) (x - y)

/-- The profile `W_s(x) = ∑_{|l| ≤ J} b_l(x) e(l s)` (period one in `s`). -/
noncomputable def Wsum (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (s x : ℝ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(J : ℤ)) J, bL ρ T J l x * ee (l * s)

/-- The output profile `Q_s(x) = ∑_{|l| ≤ J} m(2πl/T) b_l(x) e(l s)` of display (6). -/
noncomputable def Qsum (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (s x : ℝ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(J : ℤ)) J, mult (2 * Real.pi * l / T) * bL ρ T J l x * ee (l * s)

/- ## Auxiliary circle coordinates (§3) -/

/-- The sawtooth phase `t ↦ e(α {t})`, one-periodic in `t`. -/
noncomputable def saw (α t : ℝ) : ℂ := ee (α * Int.fract t)

/-- Fourier coefficients of `saw α` on `[0, 1]`. -/
noncomputable def sawCoeff (α : ℝ) (k : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, saw α t * ee (-((k : ℝ) * t))

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Statements.lean. -/
section

/-
# Statements of the components of the proof

Each `...Statement` is a `Prop` proved by exactly one file in `ChowlaOpus/Parts/`, possibly
assuming other statements as hypotheses. `ChowlaOpus/Main.lean` composes them.

Dependency graph (component : proves  ⟸  assumes). A few hypotheses are taken but unused:
`BesselPlaneStatement` in `mellinStatement_holds` and `AnnulusStatement` in `qposStatement_holds`.
* Fejer     : FejerStatement
* Bump      : BumpStatement
* J0        : J0Statement, BesselPlaneStatement
* Mellin    : MultStatement; MellinStatement             ⟸ J0Statement
* Annulus   : AnnulusStatement
* Coeff     : CoeffStatement, CoeffMassStatement         ⟸ AnnulusStatement
* W         : WrepStatement, WboundStatement             ⟸ AnnulusStatement, FejerStatement
* Q         : QposStatement                              ⟸ J0, BesselPlane, Mult, Mellin, Fejer
* Var       : VarStatement                               ⟸ AnnulusStatement, FejerStatement,
                                                            WrepStatement, WboundStatement
* AsmA      : Lemma3Statement                            ⟸ Bump, Coeff, CoeffMass, Wbound, Qpos, Var
* Saw       : SawStatement
* Aux3      : ProfileStatement                           ⟸ Lemma3, Saw, Fejer, FourierDecay
* Poisson   : PoissonStatement, PlainPoissonStatement, FourierDecayStatement
* Gauss     : RowSumStatement
* KChar     : KernelCharStatement
* Phase     : PhaseStatement                             ⟸ KernelCharStatement
* CRT       : CRTStatement
* W9        : W9Statement                                ⟸ RowSum, Poisson, PlainPoisson, Mult
* W10       : W10Statement                               ⟸ RowSum, Poisson, FourierDecay
* AsmB      : WeightsStatement                           ⟸ Profile, CRT, Phase, RowSum, Mult, W9, W10
* Partial   : PartialColoringStatement
* Spencer   : SpencerStatement                           ⟸ PartialColoringStatement
* Mesh      : MeshStatement
* Rounding  : RoundingStatement                          ⟸ SpencerStatement, MeshStatement
* MainOf    : cosine_counterexample_of                   ⟸ WeightsStatement, RoundingStatement
* Main      : main_theorem (restated as `cosine_counterexample` in `Solution.lean`)
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

/- ## Rounding (§6, Lemma 4) -/

/-- Partial colouring (entropy/pigeonhole step of Spencer's theorem), rectangular form. -/
def PartialColoringStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) →
    ∃ x : Fin v → ℤ, (∀ j, |x j| ≤ 1) ∧
      v ≤ 10 * (Finset.univ.filter (fun j => x j ≠ 0)).card ∧
      ∀ i, |∑ j, A i j * (x j : ℝ)| ≤ C * Real.sqrt (v * Real.log (2 * M / v))

/-- Spencer's theorem, rectangular form: a full signing of an `M × v` matrix (`v ≤ M`) with
entries in `[-1,1]` has all row sums `O(√(v log(2M/v)))`. -/
def SpencerStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) →
    ∃ ε : Fin v → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, A i j * ε j| ≤ C * Real.sqrt (v * Real.log (2 * M / v))

/-- Mesh bound (consequence of Bernstein's inequality): a cosine polynomial of degree `≤ N`
bounded by `E` on a mesh of `M ≥ K N` equally spaced points is bounded by `2E` everywhere. -/
def MeshStatement : Prop :=
  ∃ K : ℕ, 1 ≤ K ∧ ∀ (N M : ℕ) (c : ℕ → ℝ) (E : ℝ), K * N ≤ M → 0 < M →
    (∀ i < M, |∑ d ∈ Finset.Icc 1 N, c d * Real.cos (2 * Real.pi * d * ((i : ℝ) / M))| ≤ E) →
    ∀ t : ℝ, |∑ d ∈ Finset.Icc 1 N, c d * Real.cos (2 * Real.pi * d * t)| ≤ 2 * E

/-- Lemma 4 (rounding), with an upper bound `S` for the rounding variance. -/
def RoundingStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (w : ℕ → ℝ) (S : ℝ), 1 ≤ N → (∀ d, 0 ≤ w d ∧ w d ≤ 1) →
    0 < S → S ≤ N → ∑ d ∈ Finset.Icc 1 N, w d * (1 - w d) ≤ S →
    ∃ a : ℕ → ℝ, (∀ d, a d = 0 ∨ a d = 1) ∧
      ∀ t : ℝ, |∑ d ∈ Finset.Icc 1 N, (a d - w d) * Real.cos (2 * Real.pi * d * t)| ≤
        C * Real.sqrt (S * Real.log (2 * N / S))

/- ## Weights (§5, displays (9) and (10)) -/

/-- Fractional weights with a small negative cosine sum, large mass and small rounding
variance, for arbitrarily large `T` and then arbitrarily large `p`. -/
def WeightsStatement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧ ∀ p₀ : ℕ,
    ∃ (p N : ℕ) (w : ℕ → ℝ), p₀ ≤ p ∧ 1 ≤ N ∧ (N : ℝ) ≤ 2 * (p : ℝ) ^ 2 * T ^ 2 ∧
      (∀ d, 0 ≤ w d ∧ w d ≤ 1) ∧
      (∀ t : ℝ, -(C * p * Real.log T / T) ≤
        ∑ d ∈ Finset.Icc 1 N, w d * Real.cos (2 * Real.pi * d * t)) ∧
      c * (p : ℝ) ^ 2 / T ≤ ∑ d ∈ Finset.Icc 1 N, w d ∧
      ∑ d ∈ Finset.Icc 1 N, w d * (1 - w d) ≤ C * (p : ℝ) ^ 2 * Real.log T / T ^ 3

/- ## Profiles (Lemma 3 and §3) -/

/-- Output of Lemma 3 (label rescaled to period one). `W_s = ∑ b_l e(ls) ∈ [0,1]`,
`Q_s = ∑ m(2πl/T) b_l e(ls)` has nonnegative physical Fourier transform, (4) and (5). -/
def Lemma3Statement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ (J : ℕ) (b : ℤ → ℝ → ℂ),
      (∀ l, (J : ℤ) < |l| → b l = 0) ∧
      (∀ l, ContDiff ℝ 2 (b l)) ∧
      (∀ l x, T ^ 2 < |x| → b l x = 0) ∧
      (∀ l x, b l (-x) = b l x) ∧
      (∀ l x, b (-l) x = starRingEnd ℂ (b l x)) ∧
      (∀ x, (b 0 x).im = 0 ∧ 0 ≤ (b 0 x).re) ∧
      (∀ y, (𝓕 (b 0) y).im = 0 ∧ 0 ≤ (𝓕 (b 0) y).re) ∧
      Summable (fun j : ℤ => (b 0 j).re) ∧
      ∑' j : ℤ, (b 0 j).re ≤ C * Real.log T / T ∧
      c / T ≤ ∫ x, (b 0 x).re ∧
      (∀ s x, (∑ l ∈ Finset.Icc (-(J : ℤ)) J, b l x * ee (l * s)).im = 0 ∧
        0 ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J, b l x * ee (l * s)).re ∧
        (∑ l ∈ Finset.Icc (-(J : ℤ)) J, b l x * ee (l * s)).re ≤ 1) ∧
      (∀ s y, (∑ l ∈ Finset.Icc (-(J : ℤ)) J,
          mult (2 * Real.pi * l / T) * 𝓕 (b l) y * ee (l * s)).im = 0 ∧
        0 ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J,
          mult (2 * Real.pi * l / T) * 𝓕 (b l) y * ee (l * s)).re) ∧
      ∫ x, ((b 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖b l x‖ ^ 2) ≤
        C * Real.log T / T ^ 3

/-- The structural properties of a separated profile at scale `T` (output of §3):
frequency set `S ⊆ ℤ^{k+1}` (coordinate `0` is the label frequency), coefficients `cf`
supported in `[-R, R]` with Fourier decay constant `K`. -/
structure IsProfile {k : ℕ} (T : ℝ) (S : Finset (Fin (k + 1) → ℤ))
    (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ) (K R : ℝ) : Prop where
  zero_mem : 0 ∈ S
  neg_mem : ∀ v ∈ S, -v ∈ S
  label_ne : ∀ v ∈ S, v ≠ 0 → v 0 ≠ 0
  nonprop : ∀ v ∈ S, ∀ w ∈ S, 0 < v 0 → 0 < w 0 → (∀ i j, v i * w j = v j * w i) → v = w
  zero_off : ∀ v, v ∉ S → cf v = 0
  smooth : ∀ v, ContDiff ℝ 2 (cf v)
  supp : ∀ v x, R < |x| → cf v x = 0
  even : ∀ v x, cf v (-x) = cf v x
  conj : ∀ v x, cf (-v) x = starRingEnd ℂ (cf v x)
  decay : ∀ v y, ‖𝓕 (cf v) y‖ ≤ K / (1 + y ^ 2)
  b0 : ∀ x, (cf 0 x).im = 0 ∧ 0 ≤ (cf 0 x).re
  fourier_b0 : ∀ y, (𝓕 (cf 0) y).im = 0 ∧ 0 ≤ (𝓕 (cf 0) y).re
  range : ∀ (θ : Fin (k + 1) → ℝ) (x : ℝ), (trigEval S (fun v => cf v x) θ).im = 0 ∧
    0 ≤ (trigEval S (fun v => cf v x) θ).re ∧ (trigEval S (fun v => cf v x) θ).re ≤ 1
  pos : ∀ (θ : Fin (k + 1) → ℝ) (y : ℝ),
    (trigEval S (fun v => mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y) θ).im = 0 ∧
    0 ≤ (trigEval S (fun v => mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y) θ).re

/-- Output of §3: separated profiles for all large `T`, with the bounds (4), (5). -/
def ProfileStatement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ (k : ℕ) (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ) (K : ℝ),
      IsProfile T S cf K (T ^ 2) ∧
      Summable (fun j : ℤ => (cf 0 j).re) ∧
      ∑' j : ℤ, (cf 0 j).re ≤ C * Real.log T / T ∧
      c / T ≤ ∫ x, (cf 0 x).re ∧
      ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2) ≤ C * Real.log T / T ^ 3

/- ## Arithmetic (§4) -/

/-- Chinese remainder construction: pairwise non-proportional integer vectors with positive
first coordinate are sent by a linear form to positive, multiplicatively independent integers. -/
def CRTStatement : Prop :=
  ∀ (k : ℕ) (S : Finset (Fin (k + 1) → ℤ)), (∀ v ∈ S, 0 < v 0) →
    (∀ v ∈ S, ∀ w ∈ S, (∀ i j, v i * w j = v j * w i) → v = w) →
    ∃ L : Fin (k + 1) → ℤ, (∀ v ∈ S, 0 < ∑ i, L i * v i) ∧
      MultIndep (fun v : S => (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)

/-- Existence of an even character mod `p²` restricting to `1 + pt ↦ e(t/p)`. -/
def KernelCharStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ

/-- Display (8): prescribed unimodular phases are approximated by Gauss phases of even kernel
characters at every sufficiently large prime. -/
def PhaseStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ), (∀ i, 0 < n i) → MultIndep n →
    ∀ η : ℝ, 0 < η → ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ μ : ι → ℂ, (∀ i, ‖μ i‖ = 1) →
      ∃ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ ∧
        ∀ i, ‖gaussPhase p χ (n i) - μ i‖ < η

/-- Display (7) and the row sums of §5. -/
def RowSumStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ →
    (∀ n k : ℤ, ¬ (p : ℤ) ∣ n → ¬ (p : ℤ) ∣ k →
      rowSum p χ n k = p * ((χ (k : ZMod (p ^ 2)))⁻¹) ^ n * gaussPhase p χ n) ∧
    (∀ n k : ℤ, ¬ (p : ℤ) ∣ n → (p : ℤ) ∣ k → rowSum p χ n k = 0) ∧
    (∀ k : ℤ, rowSum p χ 0 k =
      (if (p : ℤ) ^ 2 ∣ k then ((p : ℂ) ^ 2) else 0) - (if (p : ℤ) ∣ k then (p : ℂ) else 0)) ∧
    (∀ n : ℤ, ¬ (p : ℤ) ∣ n → ‖gaussPhase p χ n‖ = 1) ∧
    (∀ n : ℤ, gaussPhase p χ (-n) = starRingEnd ℂ (gaussPhase p χ n))

/- ## Fourier analysis utilities -/

/-- Fourier decay of `C²` compactly supported functions. -/
def FourierDecayStatement : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖𝓕 f y‖ ≤ K / (1 + y ^ 2)

/-- Poisson summation for a profile sampled at `d / p²`, twisted by `χ(d)^n`, restricted to
`p ∤ d`. -/
def PoissonStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) (f : ℝ → ℂ) (K : ℝ),
    Continuous f → HasCompactSupport f → (∀ y, ‖𝓕 f y‖ ≤ K / (1 + y ^ 2)) → ∀ t : ℝ,
      Summable (fun k : ℤ => 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k) ∧
      HasSum (fun d : ℤ => (if (p : ℤ) ∣ d then 0 else
          f ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ n) * ee (d * t))
        (∑' k : ℤ, 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k)

/-- Plain Poisson summation `∑_k 𝓕f(k + y) = ∑_j f(j) e(-jy)`. -/
def PlainPoissonStatement : Prop :=
  ∀ (f : ℝ → ℂ) (K : ℝ), Continuous f → HasCompactSupport f →
    (∀ y, ‖𝓕 f y‖ ≤ K / (1 + y ^ 2)) → ∀ y : ℝ,
      Summable (fun j : ℤ => f j * ee (-((j : ℝ) * y))) ∧
      HasSum (fun k : ℤ => 𝓕 f (k + y)) (∑' j : ℤ, f j * ee (-((j : ℝ) * y)))

/- ## The weights of §5 -/

/-- `w_d = Re ∑_{v ∈ S} c_v(d/p²) χ(d)^{L·v}` for `p ∤ d`, and `0` otherwise. -/
noncomputable def wgt {k : ℕ} (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ)
    (L : Fin (k + 1) → ℤ) (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ) : ℝ :=
  if (p : ℤ) ∣ d then 0 else
    (∑ v ∈ S, cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i)).re

/-- Display (9): lower bound for the cosine sum of the weights. -/
def W9Statement : Prop :=
  ∀ (k : ℕ) (T K : ℝ) (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ),
    IsProfile T S cf K (T ^ 2) → 0 < T →
    ∀ (L : Fin (k + 1) → ℤ) (p : ℕ), p.Prime → p ≠ 2 →
    (∀ v ∈ S, 2 * |∑ i, L i * v i| < p) →
    (∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w) →
    ∀ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ →
    ∀ η : ℝ, 0 ≤ η → η * (5 * K * S.card) ≤ 1 / T →
    (∀ v ∈ S, v ≠ 0 → ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η) →
    ∀ N : ℕ, (p : ℝ) ^ 2 * T ^ 2 ≤ N → ∀ t : ℝ,
      -((p : ℝ) / 2 * (∑' j : ℤ, (cf 0 j).re + 1 / T)) ≤
        ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * Real.cos (2 * Real.pi * d * t)

/-- Display (10): mass and rounding variance of the weights, up to `O_T(p)`. -/
def W10Statement : Prop :=
  ∀ (k : ℕ) (T K : ℝ) (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ),
    IsProfile T S cf K (T ^ 2) → 0 < T →
    ∀ L : Fin (k + 1) → ℤ, (∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w) →
    ∃ E : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 → (∀ v ∈ S, 2 * |∑ i, L i * v i| < p) →
      ∀ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ → ∀ N : ℕ, (p : ℝ) ^ 2 * T ^ 2 ≤ N →
        |∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d - ((p : ℝ) ^ 2 - p) / 2 * ∫ x, (cf 0 x).re|
          ≤ E * p ∧
        |∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * (1 - wgt S cf L p χ d) -
          ((p : ℝ) ^ 2 - p) / 2 * ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2)| ≤ E * p

/- ## Internal statements for Lemma 2 and Lemma 3 -/

/-- Fejér kernel facts. -/
def FejerStatement : Prop :=
  (∀ R : ℕ, Continuous (fejer R)) ∧
  (∀ (R : ℕ) (t : ℝ), 0 ≤ fejer R t) ∧
  (∀ (R : ℕ) (t : ℝ), fejer R (t + 1) = fejer R t) ∧
  (∀ (R : ℕ) (t : ℝ), fejer R (-t) = fejer R t) ∧
  (∀ R : ℕ, ∫ t in (0 : ℝ)..1, fejer R t = 1) ∧
  (∀ (R : ℕ) (t : ℝ),
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * t) = fejer R t) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
    ∫ t in (-(1 / 2) : ℝ)..(1 / 2), fejer R t * Real.sqrt |t| ≤ C / Real.sqrt R)

/-- Existence of the bump `ρ` of §2. -/
def BumpStatement : Prop := ∃ ρ : ℝ → ℝ, IsBump ρ

/-- Facts about `J₀`: bounds, decay and the Laplace transform. -/
def J0Statement : Prop :=
  Continuous J0 ∧ (∀ r, |J0 r| ≤ 1) ∧ (∀ r, J0 (-r) = J0 r) ∧ J0 0 = 1 ∧
  (∀ r, |J0 r - 1| ≤ r ^ 2 / 4) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → |J0 r| ≤ C / Real.sqrt r) ∧
  (∀ lam c : ℝ, 0 < lam → 0 ≤ c →
    IntegrableOn (fun a => Real.exp (-(lam * a)) * J0 (a * c)) (Set.Ioi 0) ∧
    ∫ a in Set.Ioi (0 : ℝ), Real.exp (-(lam * a)) * J0 (a * c) = 1 / Real.sqrt (lam ^ 2 + c ^ 2))

/-- Display (2): averaging a plane wave over the circle. -/
def BesselPlaneStatement : Prop :=
  ∀ σ x : ℝ, besselG σ x = (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (1 - Real.cos (Real.exp (-σ) * Real.sin θ)) * Real.cos (Real.exp (-σ) * x * Real.cos θ)

/-- Elementary properties of the multiplier `m`. -/
def MultStatement : Prop :=
  (∀ τ : ℝ, ‖mult τ‖ = 1) ∧ mult 0 = 1 ∧ (∀ τ : ℝ, mult (-τ) = starRingEnd ℂ (mult τ))

/-- Lemma 2: the label transform of `G` is `m` times the label transform of `B`. -/
def MellinStatement : Prop :=
  ∀ ξ x : ℝ, x ≠ 0 → Integrable (fun σ => besselG σ x) ∧
    ∫ σ, (besselG σ x : ℂ) * ee (-(ξ * σ)) = mult (2 * Real.pi * ξ) * betaF ξ x

/-- Facts about the annulus slice `B_σ(x)`, its label mean `ℓ`, the periodization and `β_ξ`. -/
def AnnulusStatement : Prop :=
  Measurable (Function.uncurry annB) ∧
  (∀ σ x, 0 ≤ annB σ x ∧ annB σ x ≤ 1) ∧
  (∀ σ x, annB σ (-x) = annB σ x) ∧
  (∀ x, x ≠ 0 → Integrable (fun σ => annB σ x)) ∧
  (∀ x, x ≠ 0 → ellF x = Real.log (1 + (x ^ 2)⁻¹) / 2) ∧
  (∀ x, 0 ≤ ellF x) ∧
  (∀ x, x ≠ 0 → ellF x ≤ 1 / (2 * x ^ 2)) ∧
  Integrable ellF ∧ ∫ x, ellF x = Real.pi ∧
  (∀ σ, Integrable (annB σ) ∧ ∫ x, annB σ x ≤ 2 * Real.exp (-|σ|)) ∧
  (∀ x δ, x ≠ 0 → ∫ σ, |annB (σ - δ) x - annB σ x| ≤ 2 * min |δ| (ellF x)) ∧
  (∀ σ u, ∫ x, |annB σ (x - u) - annB σ x| ≤ min (4 * |u|) (4 * Real.exp (-|σ|))) ∧
  (∀ T σ x, 1 ≤ T → x ≠ 0 → Summable (fun j : ℤ => annB (σ + j * T) x)) ∧
  (∀ T σ, 1 ≤ T → Integrable (fun x => max (perB T σ x - 1) 0) ∧
    ∫ x, max (perB T σ x - 1) 0 ≤ 5 * Real.exp (-T)) ∧
  (∀ ξ, Measurable (betaF ξ)) ∧
  (∀ ξ x, ‖betaF ξ x‖ ≤ ellF x) ∧ (∀ x, betaF 0 x = ellF x) ∧
  (∀ ξ x, betaF (-ξ) x = starRingEnd ℂ (betaF ξ x)) ∧ (∀ ξ x, betaF ξ (-x) = betaF ξ x)

/-- Structural properties of the coefficients `b_l`. -/
def CoeffStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ (J : ℕ) (l : ℤ),
    ContDiff ℝ 2 (bL ρ T J l) ∧
    (∀ x, T ^ 2 < |x| → bL ρ T J l x = 0) ∧
    (∀ x, bL ρ T J l (-x) = bL ρ T J l x) ∧
    (∀ x, bL ρ T J (-l) x = starRingEnd ℂ (bL ρ T J l x)) ∧
    (∀ x, (bL ρ T J 0 x).im = 0 ∧ 0 ≤ (bL ρ T J 0 x).re) ∧
    ((J : ℤ) < |l| → bL ρ T J l = 0)

/-- Display (5) and the lower bound for the mass in (4). -/
def CoeffMassStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∀ J : ℕ,
    Summable (fun j : ℤ => (bL ρ T J 0 j).re) ∧
    ∑' j : ℤ, (bL ρ T J 0 j).re ≤ C * Real.log T / T ∧
    c / T ≤ ∫ x, (bL ρ T J 0 x).re

/-- The label representation of `W` as a Fejér average of smoothed slices. -/
def WrepStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ (J : ℕ) (s x : ℝ),
    Integrable (fun σ => fejer J (s - σ / T) * smB ρ T σ x) ∧
    Wsum ρ T J s x = ((psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) *
      ∫ σ, fejer J (s - σ / T) * smB ρ T σ x : ℝ) : ℂ)

/-- `0 ≤ W ≤ 1`. -/
def WboundStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ (J : ℕ) (s x : ℝ),
    (Wsum ρ T J s x).im = 0 ∧ 0 ≤ (Wsum ρ T J s x).re ∧ (Wsum ρ T J s x).re ≤ 1

/-- Spectral positivity of the output profile `Q` (display (6)), and of `b̂₀`. -/
def QposStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ J : ℕ,
    (∀ s y : ℝ,
      (∑ l ∈ Finset.Icc (-(J : ℤ)) J, mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y *
        ee (l * s)).im = 0 ∧
      0 ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J, mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y *
        ee (l * s)).re) ∧
    (∀ y : ℝ, (𝓕 (bL ρ T J 0) y).im = 0 ∧ 0 ≤ (𝓕 (bL ρ T J 0) y).re)

/-- The integrated rounding variance in (4). -/
def VarStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∃ C T₀ : ℝ, 0 < C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ J : ℕ, T ^ 8 ≤ J →
    ∫ x, ((bL ρ T J 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖bL ρ T J l x‖ ^ 2) ≤
      C * Real.log T / T ^ 3

/-- Fourier coefficients of the sawtooth phases `e(α{t})` (used in §3). -/
def SawStatement : Prop :=
  (∀ α : ℝ, HasSum (fun k : ℤ => ‖sawCoeff α k‖ ^ 2) 1) ∧
  (∀ (α : ℝ) (k : ℤ), sawCoeff (-α) (-k) = starRingEnd ℂ (sawCoeff α k)) ∧
  (∀ m k : ℤ, sawCoeff m k = if k = m then 1 else 0) ∧
  (∀ (α : ℝ) (R : ℕ) (u : ℝ),
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * sawCoeff α k * ee (k * u) =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * saw α t)

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Fejer.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.FejerAux

lemma fejer_complex (R : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * t) = fejer R t := by
  apply Complex.ext
  · rw [Complex.re_sum, Complex.ofReal_re]
    unfold fejer
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul, ee_re]
    ring_nf
  · rw [Complex.im_sum, Complex.ofReal_im]
    refine Finset.sum_involution (fun k _ => -k) ?_ ?_ ?_ ?_
    · intro k _
      simp only [Complex.im_ofReal_mul, ee_im, fejerCoeff_neg, Int.cast_neg]
      rw [show 2 * π * (-(k : ℝ) * t) = -(2 * π * (k * t)) by ring, Real.sin_neg]
      ring
    · intro k _ hk h
      apply hk
      have : k = 0 := by omega
      subst this
      simp [ee_im]
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k _
      simp

lemma fiber_card (R : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (-(R : ℤ)) R) :
    ((Finset.range (R + 1) ×ˢ Finset.range (R + 1)).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = k)).card = R + 1 - k.natAbs := by
  rw [Finset.mem_Icc] at hk
  have himg : (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = k) =
      (Finset.range (R + 1 - k.natAbs)).image (fun i => (i + k.toNat, i + (-k).toNat)) := by
    ext ⟨j, j'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hj, hj'⟩, h⟩
      refine ⟨j - k.toNat, ?_, ?_, ?_⟩ <;> omega
    · rintro ⟨i, hi, rfl, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injective, Finset.card_range]
  intro i i' h
  simp only [Prod.mk.injEq] at h
  omega

lemma sum_sub_eq (R : ℕ) (g : ℤ → ℂ) :
    ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (R + 1), g ((p.1 : ℤ) - p.2) =
      ∑ k ∈ Finset.Icc (-(R : ℤ)) R, ((R + 1 - k.natAbs : ℕ) : ℂ) * g k := by
  rw [← Finset.sum_fiberwise_of_maps_to' (t := Finset.Icc (-(R : ℤ)) R)
    (g := fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_const, fiber_card R k hk, nsmul_eq_mul]
  · rintro ⟨j, j'⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    simp only [Finset.mem_Icc]
    omega

/-- The Dirichlet-type sum `∑_{j=0}^{R} e(j t)`. -/
noncomputable def dir (R : ℕ) (t : ℝ) : ℂ := ∑ j ∈ Finset.range (R + 1), ee (j * t)

lemma natCast_mul_fejerCoeff (R : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (-(R : ℤ)) R) :
    ((R : ℝ) + 1) * fejerCoeff R k = ((R + 1 - k.natAbs : ℕ) : ℝ) := by
  rw [Finset.mem_Icc] at hk
  have habs : |(k : ℝ)| ≤ R := by
    rw [← Int.cast_abs]; exact_mod_cast abs_le.mpr hk
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have h1 : 0 ≤ 1 - |(k : ℝ)| / ((R : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one hpos]; linarith
  unfold fejerCoeff
  rw [max_eq_right h1, Nat.cast_sub (by omega), Nat.cast_natAbs, Int.cast_abs]
  field_simp
  push_cast
  ring

lemma dir_mul_conj (R : ℕ) (t : ℝ) :
    dir R t * starRingEnd ℂ (dir R t) =
      ((R : ℂ) + 1) * ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * t) := by
  unfold dir
  rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  have : ∀ p : ℕ × ℕ, ee (p.1 * t) * starRingEnd ℂ (ee (p.2 * t)) =
      (fun k : ℤ => ee (k * t)) ((p.1 : ℤ) - p.2) := by
    intro p
    rw [← ee_neg, ← ee_add]
    congr 1
    push_cast; ring
  rw [Finset.sum_congr rfl (fun p _ => this p), sum_sub_eq R (fun k : ℤ => ee (k * t)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← mul_assoc]
  congr 1
  exact_mod_cast (natCast_mul_fejerCoeff R k hk).symm

lemma fejer_eq_normSq (R : ℕ) (t : ℝ) : ((R : ℝ) + 1) * fejer R t = ‖dir R t‖ ^ 2 := by
  have h := dir_mul_conj R t
  rw [fejer_complex R t, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h.symm

lemma fejer_nonneg (R : ℕ) (t : ℝ) : 0 ≤ fejer R t := by
  have h := fejer_eq_normSq R t
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have : 0 ≤ ((R : ℝ) + 1) * fejer R t := by rw [h]; positivity
  nlinarith

lemma norm_dir_le (R : ℕ) (t : ℝ) : ‖dir R t‖ ≤ R + 1 := by
  unfold dir
  refine (norm_sum_le _ _).trans ?_
  simp [norm_ee]

lemma fejer_le (R : ℕ) (t : ℝ) : fejer R t ≤ R + 1 := by
  have h := fejer_eq_normSq R t
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have h1 := norm_dir_le R t
  have h2 : ‖dir R t‖ ^ 2 ≤ ((R : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith

lemma dir_eq_geom (R : ℕ) (t : ℝ) : dir R t = ∑ j ∈ Finset.range (R + 1), ee t ^ j := by
  unfold dir
  refine Finset.sum_congr rfl fun j _ => ?_
  have := ee_mul_intCast t (j : ℤ)
  rw [zpow_natCast] at this
  rw [← this]
  congr 1
  push_cast; ring

lemma norm_ee_sub_one_sq (t : ℝ) : ‖ee t - 1‖ ^ 2 = 4 * Real.sin (π * t) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ee_re, ee_im,
    Complex.one_re, Complex.one_im]
  have hc : Real.cos (2 * π * t) = 2 * Real.cos (π * t) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hs : Real.sin (2 * π * t) = 2 * Real.sin (π * t) * Real.cos (π * t) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [hc, hs]
  linear_combination (4 * (Real.cos (π * t) ^ 2 - 1)) * Real.sin_sq_add_cos_sq (π * t)

lemma sixteen_sq_le (t : ℝ) (ht : |t| ≤ 1 / 2) : 16 * t ^ 2 ≤ ‖ee t - 1‖ ^ 2 := by
  rw [norm_ee_sub_one_sq]
  have h1 : 2 / π * (π * |t|) ≤ Real.sin (π * |t|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos])
  have h2 : 2 / π * (π * |t|) = 2 * |t| := by field_simp
  rw [h2] at h1
  have h3 : Real.sin (π * |t|) ^ 2 = Real.sin (π * t) ^ 2 := by
    rcases abs_choice t with h | h <;> rw [h]
    rw [mul_neg, Real.sin_neg, neg_sq]
  have h4 : (2 * |t|) ^ 2 ≤ Real.sin (π * |t|) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [← h3]
  have : (2 * |t|) ^ 2 = 4 * t ^ 2 := by rw [mul_pow, sq_abs]; ring
  linarith

lemma fejer_le_inv (R : ℕ) (t : ℝ) (ht0 : t ≠ 0) (ht : |t| ≤ 1 / 2) :
    fejer R t ≤ 1 / (4 * ((R : ℝ) + 1) * t ^ 2) := by
  have h := fejer_eq_normSq R t
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have hgeom : dir R t * (ee t - 1) = ee t ^ (R + 1) - 1 := by
    rw [dir_eq_geom, geom_sum_mul]
  have hnum : ‖ee t ^ (R + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_ee]; norm_num
  have hprod : ‖dir R t‖ ^ 2 * ‖ee t - 1‖ ^ 2 ≤ 4 := by
    rw [← mul_pow, ← norm_mul, hgeom]
    have := pow_le_pow_left₀ (norm_nonneg _) hnum 2
    linarith
  have h16 := sixteen_sq_le t ht
  have ht2 : 0 < t ^ 2 := by positivity
  have hD : ‖dir R t‖ ^ 2 * (16 * t ^ 2) ≤ 4 :=
    (mul_le_mul_of_nonneg_left h16 (by positivity)).trans hprod
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma fejer_continuous (R : ℕ) : Continuous (fejer R) := by
  unfold fejer
  fun_prop

lemma fejer_even (R : ℕ) (t : ℝ) : fejer R (-t) = fejer R t := by
  simp only [fejer]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 2 * π * (k : ℝ) * (-t) = -(2 * π * k * t) by ring, Real.cos_neg]

lemma moment_half (R : ℕ) (hR : 1 ≤ R) :
    ∫ t in (0 : ℝ)..(1 / 2), fejer R t * √|t| ≤ 3 / (2 * √((R : ℝ) + 1)) := by
  set N : ℝ := (R : ℝ) + 1 with hN
  have hN2 : 2 ≤ N := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hNpos : 0 < N := by linarith
  set δ : ℝ := 1 / N with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hNpos (by norm_num)]; linarith
  have hδN : δ * N = 1 := by rw [hδ]; field_simp
  have hsN : 0 < √N := Real.sqrt_pos.mpr hNpos
  have hsq : √N * √N = N := Real.mul_self_sqrt hNpos.le
  have hsδ : √δ = 1 / √N := by
    rw [hδ, Real.sqrt_div' _ hNpos.le, Real.sqrt_one]
  have hcont : Continuous (fun t => fejer R t * √|t|) := by
    have := fejer_continuous R
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := δ)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..δ, fejer R t * √|t| ≤ √δ := by
    calc ∫ t in (0 : ℝ)..δ, fejer R t * √|t| ≤ ∫ t in (0 : ℝ)..δ, N * √δ := by
          refine intervalIntegral.integral_mono_on hδpos.le (hcont.intervalIntegrable _ _)
            intervalIntegrable_const ?_
          intro t ht
          have hs : √|t| ≤ √δ := Real.sqrt_le_sqrt (by rw [abs_of_nonneg ht.1]; exact ht.2)
          exact mul_le_mul (fejer_le R t) hs (Real.sqrt_nonneg _) hNpos.le
      _ = √δ := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc, hδN, one_mul]
  have h0 : (0 : ℝ) ∉ Set.uIcc δ (1 / 2) := by
    rw [Set.uIcc_of_le hδle]
    intro h
    exact absurd h.1 (not_le.mpr hδpos)
  have h2 : ∫ t in δ..(1 / 2), fejer R t * √|t| ≤
      ∫ t in δ..(1 / 2), (1 / (4 * N)) * t ^ (-(3 / 2 : ℝ)) := by
    refine intervalIntegral.integral_mono_on hδle (hcont.intervalIntegrable _ _)
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _) ?_
    intro t ht
    have htpos : 0 < t := hδpos.trans_le ht.1
    have hb := fejer_le_inv R t htpos.ne' (by rw [abs_of_pos htpos]; exact ht.2)
    rw [abs_of_pos htpos]
    have hrw : t ^ (-(3 / 2 : ℝ)) = √t / t ^ 2 := by
      rw [show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub htpos, Real.sqrt_eq_rpow,
        Real.rpow_two]
    rw [hrw]
    calc fejer R t * √t ≤ 1 / (4 * N * t ^ 2) * √t :=
          mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)
      _ = 1 / (4 * N) * (√t / t ^ 2) := by field_simp
  have h3 : ∫ t in δ..(1 / 2), (1 / (4 * N)) * t ^ (-(3 / 2 : ℝ)) ≤ 1 / (2 * √N) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    have e1 : (-(3 / 2 : ℝ)) + 1 = -(1 / 2) := by norm_num
    have e2 : δ ^ (-(1 / 2 : ℝ)) = √N := by
      rw [Real.rpow_neg hδpos.le, ← Real.sqrt_eq_rpow, hsδ, one_div, inv_inv]
    have e3 : 0 < (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    rw [e1, e2]
    calc 1 / (4 * N) * (((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) - √N) / -(1 / 2))
        = 1 / (4 * N) * (2 * (√N - (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ 1 / (4 * N) * (2 * √N) := by gcongr; linarith
      _ = 1 / (2 * √N) := by
          have h4N : 4 * N = (2 * √N) * (2 * √N) := by linear_combination (-4) * hsq
          rw [h4N]
          field_simp
  have h4 : √δ + 1 / (2 * √N) = 3 / (2 * √N) := by rw [hsδ]; field_simp; ring
  linarith

lemma moment (R : ℕ) (hR : 1 ≤ R) :
    ∫ t in (-(1 / 2) : ℝ)..(1 / 2), fejer R t * √|t| ≤ 3 / √R := by
  have hcont : Continuous (fun t => fejer R t * √|t|) := by
    have := fejer_continuous R
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hneg : ∫ t in (-(1 / 2) : ℝ)..0, fejer R t * √|t| =
      ∫ t in (0 : ℝ)..(1 / 2), fejer R t * √|t| := by
    have := intervalIntegral.integral_comp_neg (a := -(1 / 2 : ℝ)) (b := 0)
      (fun t => fejer R t * √|t|)
    simp only [fejer_even, abs_neg, neg_zero, neg_neg] at this
    exact this
  rw [hneg]
  have h := moment_half R hR
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hsR : 0 < √(R : ℝ) := Real.sqrt_pos.mpr hR'
  have hle : √(R : ℝ) ≤ √((R : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  calc _ ≤ 3 / (2 * √((R : ℝ) + 1)) + 3 / (2 * √((R : ℝ) + 1)) := by linarith
    _ = 3 / √((R : ℝ) + 1) := by field_simp; ring
    _ ≤ 3 / √R := by gcongr

lemma fejer_periodic (R : ℕ) (t : ℝ) : fejer R (t + 1) = fejer R t := by
  simp only [fejer]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : 2 * π * (k : ℝ) * (t + 1) = 2 * π * k * t + (k : ℤ) * (2 * π) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

lemma integral_cos_int (k : ℤ) :
    ∫ t in (0 : ℝ)..1, Real.cos (2 * π * k * t) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * π * k : ℝ) ≠ 0 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have : 2 * π * (k : ℝ) * 1 = ((2 * k : ℤ) : ℝ) * π := by push_cast; ring
    rw [this, Real.sin_int_mul_pi]
    simp

lemma fejer_integral (R : ℕ) : ∫ t in (0 : ℝ)..1, fejer R t = 1 := by
  unfold fejer
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_cos_int]
    simp [fejerCoeff_zero]
  · intro k _
    exact (by fun_prop : Continuous fun t => fejerCoeff R k * Real.cos (2 * π * k * t)
      ).intervalIntegrable _ _

end ChowlaOpus.FejerAux

namespace ChowlaOpus

open FejerAux in
theorem fejerStatement_holds : FejerStatement :=
  ⟨fejer_continuous, fejer_nonneg, fejer_periodic, fejer_even, fejer_integral, fejer_complex,
    ⟨3, by norm_num, moment⟩⟩

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Bump.lean. -/
section

open scoped FourierTransform ContDiff Convolution
open Real MeasureTheory

/-
# The bump `ρ`

We take `φ` a normalized smooth bump supported in `(-1/2, 1/2)` and set `ρ = φ ⋆ φ`.
Then `𝓕 ρ = (𝓕 φ)²` with `𝓕 φ` real since `φ` is real and even.
-/

namespace ChowlaOpus.BumpAux

/-- The underlying bump function data. -/
noncomputable def bump0 : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The normalized bump `φ`. -/
noncomputable def phi : ℝ → ℝ := bump0.normed volume

lemma phi_contDiff : ContDiff ℝ ∞ phi := bump0.contDiff_normed

lemma phi_continuous : Continuous phi := bump0.continuous_normed

lemma phi_nonneg (x : ℝ) : 0 ≤ phi x := bump0.nonneg_normed x

lemma phi_neg (x : ℝ) : phi (-x) = phi x := bump0.normed_neg x

lemma phi_integral : ∫ x, phi x = 1 := bump0.integral_normed

lemma phi_hasCompactSupport : HasCompactSupport phi := bump0.hasCompactSupport_normed

lemma phi_integrable : Integrable phi := bump0.integrable_normed

lemma phi_eq_zero {x : ℝ} (hx : 1 / 2 ≤ |x|) : phi x = 0 := by
  have h := bump0.support_normed_eq (μ := volume)
  by_contra hne
  have hx' : x ∈ Function.support phi := hne
  rw [phi, h] at hx'
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx'
  have : bump0.rOut = 1 / 2 := rfl
  linarith

/-- Complex-valued version of `φ`. -/
noncomputable def phiC (x : ℝ) : ℂ := (phi x : ℂ)

lemma phiC_integrable : Integrable phiC := phi_integrable.ofReal

/-- `ρ = φ ⋆ φ`. -/
noncomputable def rho : ℝ → ℝ := phi ⋆[ContinuousLinearMap.mul ℝ ℝ] phi

lemma rho_apply (x : ℝ) : rho x = ∫ y, phi y * phi (x - y) := by
  simp [rho, convolution_def]

lemma rho_contDiff : ContDiff ℝ ∞ rho :=
  phi_hasCompactSupport.contDiff_convolution_left _ phi_contDiff
    phi_integrable.locallyIntegrable

lemma rho_nonneg (x : ℝ) : 0 ≤ rho x := by
  rw [rho_apply]
  exact integral_nonneg fun y => mul_nonneg (phi_nonneg _) (phi_nonneg _)

lemma rho_even (x : ℝ) : rho (-x) = rho x := by
  rw [rho_apply, rho_apply, ← integral_neg_eq_self]
  congr 1; ext y
  rw [phi_neg, show -x - -y = -(x - y) by ring, phi_neg]

lemma rho_supp (x : ℝ) (hx : 1 ≤ |x|) : rho x = 0 := by
  rw [rho_apply]
  have : ∀ y, phi y * phi (x - y) = 0 := by
    intro y
    by_cases hy : 1 / 2 ≤ |y|
    · rw [phi_eq_zero hy, zero_mul]
    · have : 1 / 2 ≤ |x - y| := by
        have := abs_sub_abs_le_abs_sub x y
        rw [not_le] at hy
        linarith
      rw [phi_eq_zero this, mul_zero]
  simp [this]

lemma rho_integral : ∫ x, rho x = 1 := by
  rw [rho]
  refine (integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
    phi_integrable phi_integrable).trans ?_
  rw [phi_integral]
  simp

lemma phi_sq_integrable : Integrable (fun y => phi y ^ 2) := by
  have hc : Continuous (fun y => phi y ^ 2) := phi_continuous.pow 2
  exact hc.integrable_of_hasCompactSupport
    (phi_hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))

lemma phi_mul_integrable (x : ℝ) : Integrable (fun y => phi y * phi (x - y)) :=
  (phi_continuous.mul (phi_continuous.comp (continuous_const.sub continuous_id)))
    |>.integrable_of_hasCompactSupport
      (phi_hasCompactSupport.mul_right (f' := fun y => phi (x - y)))

lemma rho_zero : rho 0 = ∫ y, phi y ^ 2 := by
  rw [rho_apply]
  congr 1; ext y
  rw [zero_sub, phi_neg, sq]

lemma rho_le_zero (x : ℝ) : rho x ≤ rho 0 := by
  rw [rho_zero, rho_apply]
  have hint : Integrable (fun y => (phi y ^ 2 + phi (x - y) ^ 2) / 2) :=
    (phi_sq_integrable.add (phi_sq_integrable.comp_sub_left x)).div_const 2
  calc ∫ y, phi y * phi (x - y) ≤ ∫ y, (phi y ^ 2 + phi (x - y) ^ 2) / 2 :=
        integral_mono (phi_mul_integrable x) hint
          (fun y => by nlinarith [sq_nonneg (phi y - phi (x - y))])
    _ = ∫ y, phi y ^ 2 := by
        rw [integral_div, integral_add phi_sq_integrable (phi_sq_integrable.comp_sub_left x),
          integral_sub_left_eq_self (fun y => phi y ^ 2)]
        ring

lemma rhoC_eq : (fun x => (rho x : ℂ)) = phiC ⋆[ContinuousLinearMap.mul ℂ ℂ] phiC := by
  ext x
  rw [rho_apply, convolution_def]
  simp only [ContinuousLinearMap.mul_apply', phiC]
  rw [← integral_complex_ofReal]
  push_cast
  rfl

lemma fourier_phiC_conj (w : ℝ) : starRingEnd ℂ (𝓕 phiC w) = 𝓕 phiC w := by
  rw [fourier_eq_ee, ← integral_conj, ← integral_neg_eq_self]
  congr 1; ext v
  rw [map_mul, show -(-v * w) = v * w by ring, ee_neg (v * w)]
  simp [phiC, phi_neg]

lemma fourier_phiC_im (w : ℝ) : (𝓕 phiC w).im = 0 :=
  Complex.conj_eq_iff_im.mp (fourier_phiC_conj w)

lemma fourier_rho (w : ℝ) : 𝓕 (fun x => (rho x : ℂ)) w = 𝓕 phiC w * 𝓕 phiC w := by
  rw [rhoC_eq, Real.fourier_mul_convolution_eq phiC_integrable phiC_integrable]

lemma isBump_rho : IsBump rho where
  smooth := rho_contDiff
  nonneg := rho_nonneg
  even := rho_even
  supp := rho_supp
  integral_eq := rho_integral
  fourier_im := fun y => by
    rw [fourier_rho, Complex.mul_im, fourier_phiC_im]; ring
  fourier_nonneg := fun y => by
    rw [fourier_rho, Complex.mul_re, fourier_phiC_im]
    nlinarith [sq_nonneg (𝓕 phiC y).re]
  le_at_zero := rho_le_zero

end ChowlaOpus.BumpAux

namespace ChowlaOpus

theorem bumpStatement_holds : BumpStatement := ⟨BumpAux.rho, BumpAux.isBump_rho⟩

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/J0.lean. -/
section

/-
# Component J0: elementary properties of `J₀` and the plane-wave average (display (2))
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.J0Aux

lemma continuous_integrand : Continuous (fun p : ℝ × ℝ => Real.cos (p.1 * Real.cos p.2)) := by
  fun_prop

lemma j0_continuous : Continuous J0 := by
  unfold J0
  have : Continuous fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (r * Real.cos θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => Real.cos (r * Real.cos θ)) continuous_integrand _ _
  exact continuous_const.mul this

lemma j0_abs_le_one (r : ℝ) : |J0 r| ≤ 1 := by
  unfold J0
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (C := 1) (f := fun θ => Real.cos (r * Real.cos θ)) (fun θ _ => by
      simpa using Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs] at h
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  have hp : |2 * π - 0| = 2 * π := by rw [sub_zero, abs_of_pos (by positivity)]
  rw [hp, one_mul] at h
  calc 1 / (2 * π) * |∫ θ in (0:ℝ)..2 * π, Real.cos (r * Real.cos θ)|
      ≤ 1 / (2 * π) * (2 * π) := by gcongr
    _ = 1 := by field_simp

lemma j0_neg (r : ℝ) : J0 (-r) = J0 r := by
  unfold J0
  simp [neg_mul, Real.cos_neg]

lemma j0_zero : J0 0 = 1 := by
  unfold J0
  simp
  field_simp

lemma j0_sub_one (r : ℝ) : |J0 r - 1| ≤ r ^ 2 / 4 := by
  have hI : IntervalIntegrable (fun θ => Real.cos (r * Real.cos θ)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ => Real.cos (r * Real.cos θ)).intervalIntegrable _ _
  have hJ : J0 r - 1 = 1 / (2 * π) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.cos (r * Real.cos θ) - 1) := by
    unfold J0
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    field_simp
  have hbound : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.cos (r * Real.cos θ) - 1)‖ ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), r ^ 2 / 2 * Real.cos θ ^ 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by positivity)
    · refine Filter.Eventually.of_forall (fun θ _ => ?_)
      rw [Real.norm_eq_abs]
      have h1 := Real.one_sub_sq_div_two_le_cos (x := r * Real.cos θ)
      have h2 := Real.cos_le_one (r * Real.cos θ)
      rw [abs_of_nonpos (by linarith)]
      nlinarith
    · exact (by fun_prop : Continuous fun θ => r ^ 2 / 2 * Real.cos θ ^ 2).intervalIntegrable _ _
  have hcos : ∫ θ in (0 : ℝ)..(2 * Real.pi), r ^ 2 / 2 * Real.cos θ ^ 2 = r ^ 2 / 2 * π := by
    rw [intervalIntegral.integral_const_mul, integral_cos_sq]
    simp
  rw [hcos, Real.norm_eq_abs] at hbound
  rw [hJ, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  calc 1 / (2 * π) * |∫ θ in (0:ℝ)..2 * π, (Real.cos (r * Real.cos θ) - 1)|
      ≤ 1 / (2 * π) * (r ^ 2 / 2 * π) := by gcongr
    _ = r ^ 2 / 4 := by field_simp; ring

lemma j0_abs_arg (a x : ℝ) :
    J0 (a * |x|) = (1 / (2 * π)) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (a * x * Real.cos θ) := by
  unfold J0
  refine congrArg (fun I => 1 / (2 * π) * I) ?_
  apply intervalIntegral.integral_congr
  intro θ _
  rcases abs_choice x with h | h
  · simp only [h]
  · simp only [h]
    rw [show a * -x * Real.cos θ = -(a * x * Real.cos θ) by ring, Real.cos_neg]

lemma rot_identity (x θ : ℝ) :
    Real.sqrt (1 + x ^ 2) * Real.cos (θ + (Real.arctan x - π / 2)) =
      x * Real.cos θ + Real.sin θ := by
  have hR : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [show θ + (Real.arctan x - π / 2) = (θ + Real.arctan x) - π / 2 by ring,
    Real.cos_sub_pi_div_two, Real.sin_add, Real.sin_arctan, Real.cos_arctan]
  field_simp
  ring

lemma j0_sqrt_arg (a x : ℝ) :
    J0 (a * Real.sqrt (1 + x ^ 2)) = (1 / (2 * π)) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (a * (x * Real.cos θ + Real.sin θ)) := by
  unfold J0
  refine congrArg (fun I => 1 / (2 * π) * I) ?_
  set f : ℝ → ℝ := fun θ => Real.cos (a * Real.sqrt (1 + x ^ 2) * Real.cos θ) with hf
  have hper : Function.Periodic f (2 * π) := by
    intro θ; simp only [hf, Real.cos_add_two_pi]
  set β := Real.arctan x - π / 2
  have h1 : ∫ θ in (0 : ℝ)..(2 * Real.pi), f (θ + β) = ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ := by
    rw [intervalIntegral.integral_comp_add_right, zero_add]
    have := hper.intervalIntegral_add_eq β 0
    rw [zero_add] at this
    rw [add_comm (2 * π) β, this]
  rw [← h1]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [hf]
  rw [mul_assoc, rot_identity]

lemma integral_sin_sin_eq_zero (a x : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ)
      = 0 := by
  set g : ℝ → ℝ := fun θ => Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ) with hg
  have h1 : ∫ θ in (0 : ℝ)..(2 * Real.pi), g (2 * π - θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
    rw [intervalIntegral.integral_comp_sub_left]
    simp
  have h2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), g (2 * π - θ) =
      -∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [hg, Real.cos_two_pi_sub, Real.sin_two_pi_sub, mul_neg, Real.sin_neg]
  change ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ = 0
  linarith

lemma besselPlane (σ x : ℝ) : besselG σ x = (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (1 - Real.cos (Real.exp (-σ) * Real.sin θ)) * Real.cos (Real.exp (-σ) * x * Real.cos θ) := by
  unfold besselG
  rw [j0_abs_arg, j0_sqrt_arg, ← mul_sub]
  refine congrArg (fun I => 1 / (2 * π) * I) ?_
  generalize Real.exp (-σ) = a
  have hc : ∀ θ, Real.cos (a * (x * Real.cos θ + Real.sin θ)) =
      Real.cos (a * x * Real.cos θ) * Real.cos (a * Real.sin θ) -
        Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ) := by
    intro θ
    rw [show a * (x * Real.cos θ + Real.sin θ) = a * x * Real.cos θ + a * Real.sin θ by ring,
      Real.cos_add]
  simp_rw [hc]
  have i1 : IntervalIntegrable (fun θ => Real.cos (a * x * Real.cos θ)) volume 0 (2 * π) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => Real.cos (a * x * Real.cos θ) * Real.cos (a * Real.sin θ))
      volume 0 (2 * π) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ => Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ))
      volume 0 (2 * π) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i2 i3, integral_sin_sin_eq_zero, sub_zero,
    ← intervalIntegral.integral_sub i1 i2]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

lemma laplace_cos (lam w : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun a => Real.exp (-(lam * a)) * Real.cos (a * w)) (Set.Ioi 0) ∧
    ∫ a in Set.Ioi (0:ℝ), Real.exp (-(lam * a)) * Real.cos (a * w) = lam / (lam ^ 2 + w ^ 2) := by
  set z : ℂ := -lam + w * Complex.I with hzdef
  have hz : z.re < 0 := by simp [z]; linarith
  have hint := integrableOn_exp_mul_complex_Ioi hz 0
  have hval := integral_exp_mul_complex_Ioi hz 0
  have hpt : ∀ a : ℝ, (Complex.exp (z * a)).re = Real.exp (-(lam * a)) * Real.cos (a * w) := by
    intro a
    rw [Complex.exp_re]
    simp [z]
    ring_nf
  constructor
  · have := hint.re
    simpa [IntegrableOn, hpt] using this
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    simp_rw [hpt] at h
    rw [h, hval]
    simp [z, Complex.div_re, Complex.normSq_apply]
    field_simp

/-- The globally smooth antiderivative `θ - arctan(...)` of `k / (cos² θ + k² sin² θ)`. -/
noncomputable def Gk (k θ : ℝ) : ℝ :=
  θ - Real.arctan ((1 - k) * Real.sin θ * Real.cos θ / (Real.cos θ ^ 2 + k * Real.sin θ ^ 2))

lemma alg_Gk (k s c : ℝ) (_hk : 0 < k) (hsc : s ^ 2 + c ^ 2 = 1) (hD : 0 < c ^ 2 + k * s ^ 2)
    (hE : 0 < c ^ 2 + k ^ 2 * s ^ 2) :
    1 - 1 / (1 + ((1 - k) * s * c / (c ^ 2 + k * s ^ 2)) ^ 2) *
      (((1 - k) * (c ^ 2 - s ^ 2) * (c ^ 2 + k * s ^ 2) -
        (1 - k) * s * c * (-(2 * (1 - k) * s * c))) / (c ^ 2 + k * s ^ 2) ^ 2) =
      k / (c ^ 2 + k ^ 2 * s ^ 2) := by
  have e1 : (1 - k) * (c ^ 2 - s ^ 2) * (c ^ 2 + k * s ^ 2) -
      (1 - k) * s * c * (-(2 * (1 - k) * s * c)) = (1 - k) * (c ^ 2 - k * s ^ 2) := by
    linear_combination (1 - k) * (c ^ 2 - k * s ^ 2) * hsc
  have e2 : 1 + ((1 - k) * s * c / (c ^ 2 + k * s ^ 2)) ^ 2 =
      (c ^ 2 + k ^ 2 * s ^ 2) / (c ^ 2 + k * s ^ 2) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    linear_combination (c ^ 2 + k ^ 2 * s ^ 2) * hsc
  rw [e1, e2]
  field_simp
  linear_combination k * hsc

lemma posE (k θ : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1) :
    0 < Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2 := by
  have hsc := Real.sin_sq_add_cos_sq θ
  have hk2 : k ^ 2 ≤ 1 := by nlinarith
  have hk2' : 0 < k ^ 2 := by positivity
  have : k ^ 2 * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by
    nlinarith [sq_nonneg (Real.cos θ)]
  nlinarith

lemma hasDerivAt_Gk (k θ : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1) :
    HasDerivAt (Gk k) (k / (Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2)) θ := by
  have hsc := Real.sin_sq_add_cos_sq θ
  have hD : 0 < Real.cos θ ^ 2 + k * Real.sin θ ^ 2 := by
    nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]
  have hE := posE k θ hk0 hk1
  have hN : HasDerivAt (fun θ => (1 - k) * Real.sin θ * Real.cos θ)
      ((1 - k) * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) θ := by
    convert ((hasDerivAt_sin θ).const_mul (1 - k)).mul (hasDerivAt_cos θ) using 1 <;>
      first | rfl | ring
  have hDd : HasDerivAt (fun θ => Real.cos θ ^ 2 + k * Real.sin θ ^ 2)
      (-(2 * (1 - k) * Real.sin θ * Real.cos θ)) θ := by
    convert ((hasDerivAt_cos θ).pow 2).add (((hasDerivAt_sin θ).pow 2).const_mul k) using 1 <;>
      first | rfl | (try simp) <;> ring
  have h := (hasDerivAt_id θ).sub ((hN.fun_div hDd hD.ne').arctan)
  convert h using 1 <;> try rfl
  exact (alg_Gk k (Real.sin θ) (Real.cos θ) hk0 hsc hD hE).symm

lemma Gk_zero (k : ℝ) : Gk k 0 = 0 := by simp [Gk]

lemma Gk_two_pi (k : ℝ) : Gk k (2 * π) = 2 * π := by simp [Gk]

lemma angular_integral (lam c : ℝ) (hlam : 0 < lam) :
    ∫ θ in (0:ℝ)..(2 * π), lam / (lam ^ 2 + (c * Real.cos θ) ^ 2) =
      2 * π / Real.sqrt (lam ^ 2 + c ^ 2) := by
  set s := Real.sqrt (lam ^ 2 + c ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = lam ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  set k := lam / s with hk
  have hk0 : 0 < k := div_pos hlam hs0
  have hk1 : k ≤ 1 := by
    rw [hk, div_le_one hs0]
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg c]
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * π),
      HasDerivAt (fun θ => Gk k θ / s) (lam / (lam ^ 2 + (c * Real.cos θ) ^ 2)) θ := by
    intro θ _
    have hsc := Real.sin_sq_add_cos_sq θ
    have hF : 0 < lam ^ 2 + (c * Real.cos θ) ^ 2 := by positivity
    have key : Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2 =
        (lam ^ 2 + (c * Real.cos θ) ^ 2) / s ^ 2 := by
      rw [hk, div_pow, eq_div_iff (by positivity)]
      field_simp
      linear_combination (Real.cos θ ^ 2) * hs2 + lam ^ 2 * hsc
    convert (hasDerivAt_Gk k θ hk0 hk1).div_const s using 1 <;> try rfl
    rw [key, hk]
    field_simp
  have hint : IntervalIntegrable (fun θ => lam / (lam ^ 2 + (c * Real.cos θ) ^ 2)) volume 0
      (2 * π) := by
    have hc : Continuous fun θ : ℝ => lam ^ 2 + (c * Real.cos θ) ^ 2 := by fun_prop
    exact (continuous_const.div hc (fun θ => by positivity)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Gk_zero, Gk_two_pi]
  ring

lemma laplace_j0 (lam c : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun a => Real.exp (-(lam * a)) * J0 (a * c)) (Set.Ioi 0) ∧
    ∫ a in Set.Ioi (0 : ℝ), Real.exp (-(lam * a)) * J0 (a * c) =
      1 / Real.sqrt (lam ^ 2 + c ^ 2) := by
  have hexp : IntegrableOn (fun a => Real.exp (-(lam * a))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 hlam
    simpa [neg_mul] using this
  constructor
  · refine Integrable.mono' hexp ?_ ?_
    · exact ((by fun_prop : Continuous fun a : ℝ => Real.exp (-(lam * a))).mul
        (j0_continuous.comp (by fun_prop : Continuous fun a : ℝ => a * c))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun a => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (j0_abs_le_one _)
  · let F : ℝ → ℝ → ℝ := fun a θ => Real.exp (-(lam * a)) * Real.cos (a * (c * Real.cos θ))
    have hF : Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioc 0 (2 * π)))) := by
      have hg : Integrable (fun z : ℝ × ℝ => Real.exp (-(lam * z.1)) * (fun _ : ℝ => (1:ℝ)) z.2)
          ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioc 0 (2 * π)))) :=
        Integrable.mul_prod hexp continuous_const.integrableOn_Ioc
      refine Integrable.mono' hg ?_ ?_
      · exact (by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun z => ?_)
        simp only [Function.uncurry, F, mul_one]
        rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have step1 : ∫ a in Set.Ioi (0:ℝ), Real.exp (-(lam * a)) * J0 (a * c) =
        1 / (2 * π) * ∫ a in Set.Ioi (0:ℝ), ∫ θ in Set.Ioc 0 (2 * π), F a θ := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun a _ => ?_)
      simp only [J0, F]
      rw [intervalIntegral.integral_of_le (by positivity), ← integral_const_mul,
        ← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only
      ring_nf
    have step2 := integral_integral_swap hF
    have step3 : ∀ θ, ∫ a in Set.Ioi (0:ℝ), F a θ = lam / (lam ^ 2 + (c * Real.cos θ) ^ 2) := by
      intro θ
      exact (laplace_cos lam (c * Real.cos θ) hlam).2
    rw [step1, step2]
    simp_rw [step3]
    rw [← intervalIntegral.integral_of_le (by positivity), angular_integral lam c hlam]
    field_simp

lemma j0_quarter (r : ℝ) :
    J0 r = (2 / π) * ∫ θ in (0:ℝ)..(π / 2), Real.cos (r * Real.cos θ) := by
  let f : ℝ → ℝ := fun θ => Real.cos (r * Real.cos θ)
  have hcont : Continuous f := by fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hcont.intervalIntegrable a b
  have h1 : ∫ θ in (0:ℝ)..(2 * π), f θ = (∫ θ in (0:ℝ)..π, f θ) + ∫ θ in π..(2 * π), f θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hi 0 π) (hi π (2 * π))).symm
  have h2 : ∫ θ in π..(2 * π), f θ = ∫ θ in (0:ℝ)..π, f θ := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) f (2 * π)
    rw [show 2 * π - π = π by ring, sub_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [f, Real.cos_two_pi_sub]
  have h3 : ∫ θ in (0:ℝ)..π, f θ = (∫ θ in (0:ℝ)..(π / 2), f θ) + ∫ θ in (π / 2)..π, f θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hi 0 (π / 2)) (hi (π / 2) π)).symm
  have h4 : ∫ θ in (π / 2)..π, f θ = ∫ θ in (0:ℝ)..(π / 2), f θ := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2) f π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [f, Real.cos_pi_sub, mul_neg, Real.cos_neg]
  unfold J0
  change 1 / (2 * π) * ∫ θ in (0:ℝ)..(2 * π), f θ = 2 / π * ∫ θ in (0:ℝ)..(π / 2), f θ
  rw [h1, h2, h3, h4]
  field_simp
  ring

lemma tail_bound (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ ≤ π / 2) :
    |∫ θ in δ..(π / 2), Real.cos (r * Real.cos θ)| ≤ 2 / (r * Real.sin δ) := by
  have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hsin_pos : ∀ θ ∈ Set.uIcc δ (π / 2), 0 < Real.sin θ := by
    intro θ hθ
    rw [Set.uIcc_of_le hδ'] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  let u : ℝ → ℝ := fun θ => -(r * Real.sin θ)⁻¹
  let u' : ℝ → ℝ := fun θ => Real.cos θ / (r * Real.sin θ ^ 2)
  let v : ℝ → ℝ := fun θ => Real.sin (r * Real.cos θ)
  let v' : ℝ → ℝ := fun θ => Real.cos (r * Real.cos θ) * (-(r * Real.sin θ))
  have hu_deriv : ∀ θ ∈ Set.uIcc δ (π / 2), HasDerivAt u (u' θ) θ := by
    intro θ hθ
    have hs := hsin_pos θ hθ
    have h := (((hasDerivAt_sin θ).const_mul r).fun_inv (by positivity)).neg
    convert h using 1 <;> try rfl
    try simp only [u']
    field_simp
  have hv_deriv : ∀ θ, HasDerivAt v (v' θ) θ := by
    intro θ
    have h := ((hasDerivAt_cos θ).const_mul r).sin
    convert h using 1 <;> try rfl
    try simp only [v']
    ring
  have hu'_int : IntervalIntegrable u' volume δ (π / 2) := by
    have hc1 : Continuous fun θ : ℝ => Real.cos θ := Real.continuous_cos
    have hc2 : Continuous fun θ : ℝ => r * Real.sin θ ^ 2 := by fun_prop
    have : ContinuousOn (fun θ : ℝ => Real.cos θ / (r * Real.sin θ ^ 2)) (Set.uIcc δ (π / 2)) :=
      hc1.continuousOn.div hc2.continuousOn (fun θ hθ => by
        have := hsin_pos θ hθ
        positivity)
    exact this.intervalIntegrable
  have hv'_int : IntervalIntegrable v' volume δ (π / 2) := by
    have : Continuous fun θ : ℝ => Real.cos (r * Real.cos θ) * (-(r * Real.sin θ)) := by
      fun_prop
    exact this.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv
    (fun θ _ => hv_deriv θ) hu'_int hv'_int
  have heq : ∫ θ in δ..(π / 2), Real.cos (r * Real.cos θ) =
      ∫ θ in δ..(π / 2), u θ * v' θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hs := hsin_pos θ hθ
    simp only [u, v']
    field_simp
  rw [heq, hibp]
  have hend : u (π / 2) * v (π / 2) = 0 := by simp [u, v]
  have hstart : |u δ * v δ| ≤ 1 / (r * Real.sin δ) := by
    simp only [u, v]
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos (by positivity : 0 < r * Real.sin δ), one_div]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hint_bound : |∫ θ in δ..(π / 2), u' θ * v θ| ≤ 1 / (r * Real.sin δ) := by
    have h1 : ‖∫ θ in δ..(π / 2), u' θ * v θ‖ ≤ ∫ θ in δ..(π / 2), u' θ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hδ'
      · refine Filter.Eventually.of_forall (fun θ hθ => ?_)
        have hθ' : θ ∈ Set.uIcc δ (π / 2) := by
          rw [Set.uIcc_of_le hδ']; exact Set.Ioc_subset_Icc_self hθ
        have hs := hsin_pos θ hθ'
        have hc : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
        have hu'0 : 0 ≤ u' θ := by simp only [u']; positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu'0]
        exact mul_le_of_le_one_right hu'0 (Real.abs_sin_le_one _)
      · exact hu'_int
    have h2 : ∫ θ in δ..(π / 2), u' θ = u (π / 2) - u δ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hu_deriv hu'_int
    rw [h2, Real.norm_eq_abs] at h1
    have h3 : u (π / 2) - u δ ≤ 1 / (r * Real.sin δ) := by
      simp only [u, Real.sin_pi_div_two, mul_one]
      have : 0 < r⁻¹ := inv_pos.mpr hr
      rw [one_div]
      linarith
    linarith
  rw [hend, zero_sub]
  obtain ⟨a1, a1'⟩ := abs_le.mp hstart
  obtain ⟨a2, a2'⟩ := abs_le.mp hint_bound
  have h2 : 2 / (r * Real.sin δ) = 1 / (r * Real.sin δ) + 1 / (r * Real.sin δ) := by ring
  rw [abs_le, h2]
  constructor <;> linarith

lemma head_bound (r δ : ℝ) (hδ : 0 ≤ δ) :
    |∫ θ in (0:ℝ)..δ, Real.cos (r * Real.cos θ)| ≤ δ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
    (C := 1) (f := fun θ => Real.cos (r * Real.cos θ)) (fun θ _ => by
      simpa using Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hδ, one_mul] at h
  exact h

lemma quarter_bound (t : ℝ) (ht : 1 ≤ t) :
    |∫ θ in (0:ℝ)..(π / 2), Real.cos (t ^ 2 * Real.cos θ)| ≤ (1 + π) / t := by
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < t ^ 2 := by positivity
  set δ := 1 / t with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one ht0]; exact ht
  have hδπ : δ ≤ π / 2 := by linarith [Real.pi_gt_three]
  have hcont : Continuous fun θ => Real.cos (t ^ 2 * Real.cos θ) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 δ)
    (hcont.intervalIntegrable δ (π / 2))]
  have hhead := head_bound (t ^ 2) δ hδ0.le
  have htail := tail_bound (t ^ 2) δ hr0 hδ0 hδπ
  have hjordan : 2 / π * δ ≤ Real.sin δ := Real.mul_le_sin hδ0.le hδπ
  have htail' : 2 / (t ^ 2 * Real.sin δ) ≤ π / t := by
    have hpos : 0 < 2 / π * δ := by positivity
    calc 2 / (t ^ 2 * Real.sin δ) ≤ 2 / (t ^ 2 * (2 / π * δ)) := by gcongr
      _ = π / t := by
        rw [hδdef]
        field_simp
  calc |(∫ θ in (0:ℝ)..δ, Real.cos (t ^ 2 * Real.cos θ)) +
        ∫ θ in δ..(π / 2), Real.cos (t ^ 2 * Real.cos θ)|
      ≤ |∫ θ in (0:ℝ)..δ, Real.cos (t ^ 2 * Real.cos θ)| +
        |∫ θ in δ..(π / 2), Real.cos (t ^ 2 * Real.cos θ)| := abs_add_le _ _
    _ ≤ δ + π / t := by linarith
    _ = (1 + π) / t := by rw [hδdef]; ring

lemma j0_decay : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → |J0 r| ≤ C / Real.sqrt r := by
  refine ⟨3, by norm_num, fun r hr => ?_⟩
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  rcases le_or_gt 1 r with h1 | h1
  · have ht : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr h1
    have hr_eq : r = Real.sqrt r ^ 2 := (Real.sq_sqrt hr.le).symm
    rw [j0_quarter, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / π)]
    have hq := quarter_bound (Real.sqrt r) ht
    rw [← hr_eq] at hq
    have hpi := Real.pi_gt_three
    calc 2 / π * |∫ θ in (0:ℝ)..(π / 2), Real.cos (r * Real.cos θ)|
        ≤ 2 / π * ((1 + π) / Real.sqrt r) := by gcongr
      _ = (2 / π + 2) / Real.sqrt r := by field_simp
      _ ≤ 3 / Real.sqrt r := by
          gcongr
          have : 2 / π ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          linarith
  · have hsq1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr h1.le
    calc |J0 r| ≤ 1 := j0_abs_le_one r
      _ ≤ 3 / Real.sqrt r := by rw [le_div_iff₀ hsq]; linarith

end ChowlaOpus.J0Aux

namespace ChowlaOpus

open J0Aux in
theorem j0Statement_holds : J0Statement :=
  ⟨j0_continuous, j0_abs_le_one, j0_neg, j0_zero, j0_sub_one, j0_decay,
    fun lam c hlam _ => laplace_j0 lam c hlam⟩

theorem besselPlaneStatement_holds : BesselPlaneStatement := J0Aux.besselPlane

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Mellin.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.MellinAux

/-- `g(a) = J₀(a|x|) − J₀(a√(1+x²))`, so that `g(e^{-σ}) = G_σ(x)`. -/
noncomputable def gF (x : ℝ) (a : ℝ) : ℂ :=
  ((J0 (a * |x|) - J0 (a * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ)

/-- Laplace transform of `g`: `(λ² + A)^{-1/2} − (λ² + B)^{-1/2}`. -/
noncomputable def LF (A B : ℝ) (l : ℝ) : ℂ :=
  ((1 / Real.sqrt (l ^ 2 + A) - 1 / Real.sqrt (l ^ 2 + B) : ℝ) : ℂ)

/-- `e^{-At} − e^{-Bt}`. -/
noncomputable def hF (A B : ℝ) (t : ℝ) : ℂ :=
  ((Real.exp (-(A * t)) - Real.exp (-(B * t)) : ℝ) : ℂ)

/-- Indicator of `[A, B]`. -/
noncomputable def IF (A B : ℝ) : ℝ → ℂ := Set.indicator (Set.Icc A B) (fun _ => 1)

lemma norm_cpow_of_re_zero {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z.re = 0) :
    ‖(t : ℂ) ^ z‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, hz, Real.rpow_zero]

lemma one_div_cpow_eq {y : ℝ} (hy : 0 < y) (a : ℂ) : (1 / (y : ℂ)) ^ a = (y : ℂ) ^ (-a) := by
  rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg]

lemma lhs_eq_mellin (ξ x : ℝ) :
    ∫ σ, (besselG σ x : ℂ) * ee (-(ξ * σ)) =
      mellin (gF x) (Complex.I * ((2 * π * ξ : ℝ) : ℂ)) := by
  rw [mellin_eq_fourier, fourier_eq_ee]
  have h1 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).re = 0 := by simp
  have h2 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).im / (2 * π) = ξ := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    field_simp
  rw [h1, h2]
  congr 1; ext σ
  simp [gF, besselG, mul_comm]

lemma betaF_eq_mellin (ξ x : ℝ) :
    betaF ξ x = (1 / 2 : ℂ) *
      mellin (IF (x ^ 2) (1 + x ^ 2)) (-(Complex.I * ((2 * π * ξ : ℝ) : ℂ)) / 2) := by
  have hc := mellin_comp_rpow (IF (x ^ 2) (1 + x ^ 2)) (Complex.I * ((2 * π * ξ : ℝ) : ℂ)) (-2)
  rw [show (Complex.I * ((2 * π * ξ : ℝ) : ℂ)) / ((-2 : ℝ) : ℂ) =
    -(Complex.I * ((2 * π * ξ : ℝ) : ℂ)) / 2 by push_cast; ring] at hc
  have h12 : |(-2 : ℝ)|⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [h12, Complex.real_smul, show (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at hc
  rw [← hc, mellin_eq_fourier, fourier_eq_ee]
  have h1 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).re = 0 := by simp
  have h2 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).im / (2 * π) = ξ := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    field_simp
  rw [h1, h2]
  unfold betaF
  congr 1; ext σ
  have he : Real.exp (-σ) ^ (-2 : ℝ) = Real.exp σ ^ 2 := by
    rw [← Real.exp_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have key : (|x| ≤ Real.exp σ) ↔ x ^ 2 ≤ Real.exp σ ^ 2 := by
    rw [← sq_abs]; exact (sq_le_sq₀ (abs_nonneg x) (Real.exp_pos σ).le).symm
  simp only [neg_zero, zero_mul, Real.exp_zero, one_smul, he, IF, annB, Set.indicator_apply,
    Set.mem_Icc, key]
  split_ifs <;> simp [mul_comm]

lemma gF_continuous (hJ : J0Statement) (x : ℝ) : Continuous (gF x) := by
  have hc := hJ.1
  unfold gF
  fun_prop

lemma gF_bound_small (hJ : J0Statement) (x a : ℝ) :
    ‖gF x a‖ ≤ (1 + 2 * x ^ 2) / 4 * a ^ 2 := by
  obtain ⟨-, -, -, -, hquad, -⟩ := hJ
  have h1 := hquad (a * |x|)
  have h2 := hquad (a * Real.sqrt (1 + x ^ 2))
  rw [gF, Complex.norm_real, Real.norm_eq_abs]
  have e1 : (a * |x|) ^ 2 = a ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
  have e2 : (a * Real.sqrt (1 + x ^ 2)) ^ 2 = a ^ 2 * (1 + x ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [e1] at h1
  rw [e2] at h2
  calc |J0 (a * |x|) - J0 (a * Real.sqrt (1 + x ^ 2))|
      = |(J0 (a * |x|) - 1) - (J0 (a * Real.sqrt (1 + x ^ 2)) - 1)| := by ring_nf
    _ ≤ |J0 (a * |x|) - 1| + |J0 (a * Real.sqrt (1 + x ^ 2)) - 1| := abs_sub _ _
    _ ≤ a ^ 2 * x ^ 2 / 4 + a ^ 2 * (1 + x ^ 2) / 4 := add_le_add h1 h2
    _ = (1 + 2 * x ^ 2) / 4 * a ^ 2 := by ring

lemma gF_bound_large (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) :
    ∃ K, 0 < K ∧ ∀ a, 0 < a → ‖gF x a‖ ≤ K * a ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨-, -, -, -, -, ⟨C, hC, hdecay⟩, -⟩ := hJ
  have hu : 0 < |x| := abs_pos.mpr hx
  refine ⟨2 * C / Real.sqrt |x|, by positivity, fun a ha => ?_⟩
  have hv : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h1 := hdecay (a * |x|) (by positivity)
  have h2 := hdecay (a * Real.sqrt (1 + x ^ 2)) (by positivity)
  have h3 : C / Real.sqrt (a * Real.sqrt (1 + x ^ 2)) ≤ C / Real.sqrt (a * |x|) := by
    apply div_le_div_of_nonneg_left hC.le (by positivity)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv ha.le)
  have h4 : C / Real.sqrt (a * |x|) = C / Real.sqrt |x| * a ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_mul ha.le, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
    have : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    have : Real.sqrt |x| ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
    field_simp
  rw [gF, Complex.norm_real, Real.norm_eq_abs]
  calc |J0 (a * |x|) - J0 (a * Real.sqrt (1 + x ^ 2))|
      ≤ |J0 (a * |x|)| + |J0 (a * Real.sqrt (1 + x ^ 2))| := abs_sub _ _
    _ ≤ C / Real.sqrt (a * |x|) + C / Real.sqrt (a * |x|) := add_le_add h1 (h2.trans h3)
    _ = 2 * C / Real.sqrt |x| * a ^ (-(1 / 2 : ℝ)) := by rw [h4]; ring

lemma integrableOn_gF_div (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (fun a => ‖gF x a‖ / a) (Set.Ioi 0) := by
  obtain ⟨K, hK, hbd⟩ := gF_bound_large hJ hx
  have hmeas : Measurable (fun a => ‖gF x a‖ / a) :=
    ((gF_continuous hJ x).measurable.norm).div measurable_id
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · refine Integrable.mono' (integrable_const ((1 + 2 * x ^ 2) / 4)) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun a ha => ?_)
    obtain ⟨ha0, ha1⟩ := ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ha0]
    calc ‖gF x a‖ ≤ (1 + 2 * x ^ 2) / 4 * a ^ 2 := gF_bound_small hJ x a
      _ ≤ (1 + 2 * x ^ 2) / 4 * a := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-(3 / 2) : ℝ) < -1) zero_lt_one).const_mul K) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun a ha => ?_)
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ha0]
    calc ‖gF x a‖ ≤ K * a ^ (-(1 / 2 : ℝ)) := hbd a ha0
      _ = K * a ^ (-(3 / 2) : ℝ) * a := by
        rw [mul_assoc, ← Real.rpow_add_one ha0.ne']; norm_num

lemma integrable_besselG (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) :
    Integrable (fun σ => besselG σ x) := by
  obtain ⟨K, hK, hbd⟩ := gF_bound_large hJ hx
  have hnorm : ∀ σ, ‖besselG σ x‖ = ‖gF x (Real.exp (-σ))‖ := fun σ => by
    simp only [gF, besselG, Complex.norm_real]
  have hcont : Continuous (fun σ => besselG σ x) := by
    have hc := hJ.1
    unfold besselG
    fun_prop
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
  constructor
  · refine Integrable.mono' ((integrableOn_exp_mul_Iic (by norm_num : (0:ℝ) < 1 / 2) 0).const_mul K)
      hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun σ => ?_)
    rw [hnorm]
    calc ‖gF x (Real.exp (-σ))‖ ≤ K * Real.exp (-σ) ^ (-(1 / 2 : ℝ)) := hbd _ (Real.exp_pos _)
      _ = K * Real.exp (1 / 2 * σ) := by rw [← Real.exp_mul]; congr 2; ring
  · refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 2)).const_mul
      ((1 + 2 * x ^ 2) / 4)) hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun σ => ?_)
    rw [hnorm]
    calc ‖gF x (Real.exp (-σ))‖ ≤ (1 + 2 * x ^ 2) / 4 * Real.exp (-σ) ^ 2 := gF_bound_small hJ x _
      _ = (1 + 2 * x ^ 2) / 4 * Real.exp (-2 * σ) := by
        rw [← Real.exp_nat_mul]; congr 2; push_cast; ring

lemma step1 (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) {s : ℂ} (hs : s.re = 0) :
    Complex.Gamma (1 - s) * mellin (gF x) s = mellin (LF (x ^ 2) (1 + x ^ 2)) (1 - s) := by
  have hlap := hJ.2.2.2.2.2.2
  set f : ℝ → ℝ → ℂ := fun a l =>
    gF x a * ((l : ℂ) ^ ((1 - s) - 1) * Complex.exp (-((a : ℂ) * l))) with hf
  have hmeas : Measurable (Function.uncurry f) := by
    have := (gF_continuous hJ x).measurable
    simp only [hf]
    fun_prop
  have hnorm : ∀ a l, 0 < l → ‖f a l‖ = ‖gF x a‖ * Real.exp (-a * l) := by
    intro a l hl
    have hn : ‖(l : ℂ) ^ ((1 - s) - 1)‖ = 1 := norm_cpow_of_re_zero hl (by simp [hs])
    simp only [hf, norm_mul, hn, one_mul, Complex.norm_exp]
    congr 2
    simp
  have hexp_int : ∀ a, 0 < a → ∫ l in Set.Ioi (0:ℝ), Real.exp (-a * l) = 1 / a := by
    intro a ha
    have := integral_exp_mul_Ioi (a := -a) (by linarith) 0
    rw [this]
    simp
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      have ha' : 0 < a := ha
      refine ((exp_neg_integrableOn_Ioi 0 ha').const_mul ‖gF x a‖).mono'
        (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun l hl => (hnorm a l hl).le)
    · have heq : ∀ a ∈ Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), ‖f a l‖ = ‖gF x a‖ / a := by
        intro a ha
        rw [setIntegral_congr_fun measurableSet_Ioi (fun l (hl : l ∈ Set.Ioi (0:ℝ)) => hnorm a l hl),
          integral_const_mul,
          hexp_int a ha]
        ring
      exact (integrableOn_gF_div hJ hx).congr ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun a ha => (heq a ha).symm)))
  have hswap := integral_integral_swap hint
  have hL : ∫ a in Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), f a l =
      Complex.Gamma (1 - s) * mellin (gF x) s := by
    unfold mellin
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun a ha => ?_)
    have ha' : 0 < a := ha
    simp only [hf]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi (by simp [hs]) ha',
      one_div_cpow_eq ha', smul_eq_mul, show -(1 - s) = s - 1 by ring]
    ring
  have hR : ∫ l in Set.Ioi (0:ℝ), ∫ a in Set.Ioi (0:ℝ), f a l =
      mellin (LF (x ^ 2) (1 + x ^ 2)) (1 - s) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun l hl => ?_)
    have hl' : 0 < l := hl
    have e : ∀ a, f a l = (l : ℂ) ^ ((1 - s) - 1) *
        ((Real.exp (-(l * a)) * J0 (a * |x|) -
          Real.exp (-(l * a)) * J0 (a * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ) := by
      intro a
      simp only [hf, gF]
      push_cast
      ring_nf
    simp_rw [e]
    obtain ⟨hi1, he1⟩ := hlap l |x| hl' (abs_nonneg x)
    obtain ⟨hi2, he2⟩ := hlap l (Real.sqrt (1 + x ^ 2)) hl' (Real.sqrt_nonneg _)
    rw [integral_const_mul, integral_complex_ofReal, integral_sub hi1 hi2, he1, he2, smul_eq_mul]
    simp only [LF, sq_abs, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + x ^ 2)]
  rw [← hL, hswap, hR]

lemma mellin_gauss {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 < z.re) :
    ∫ l in Set.Ioi (0:ℝ), (l : ℂ) ^ (z - 1) * ((Real.exp (-t * l ^ 2) : ℝ) : ℂ) =
      1 / 2 * ((t : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) := by
  have h1 := mellin_comp_rpow (fun y => ((Real.exp (-(t * y)) : ℝ) : ℂ)) z 2
  have h2 := mellin_comp_mul_left (fun y => ((Real.exp (-y) : ℝ) : ℂ)) (z / 2) ht
  have h3 : mellin (fun y => ((Real.exp (-y) : ℝ) : ℂ)) (z / 2) = Complex.Gamma (z / 2) := by
    rw [← Complex.GammaIntegral_eq_mellin, Complex.Gamma_eq_integral (by simp; linarith)]
  rw [show z / ((2:ℝ):ℂ) = z / 2 by norm_num, h2, h3] at h1
  unfold mellin at h1
  simp_rw [smul_eq_mul, Real.rpow_two] at h1
  rw [show |(2:ℝ)|⁻¹ = 1 / 2 by norm_num, Complex.real_smul] at h1
  simp_rw [neg_mul]
  rw [h1]
  push_cast; ring

lemma sub_exp_div_le {A B t : ℝ} (hAB : A ≤ B) (ht : 0 < t) :
    0 ≤ (Real.exp (-(A * t)) - Real.exp (-(B * t))) / t ∧
      (Real.exp (-(A * t)) - Real.exp (-(B * t))) / t ≤ (B - A) * Real.exp (-(A * t)) := by
  have hle : Real.exp (-(B * t)) ≤ Real.exp (-(A * t)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  refine ⟨div_nonneg (by linarith) ht.le, ?_⟩
  rw [div_le_iff₀ ht]
  have h1 := Real.add_one_le_exp (-((B - A) * t))
  have h2 : Real.exp (-(B * t)) = Real.exp (-(A * t)) * Real.exp (-((B - A) * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  have h3 := Real.exp_pos (-(A * t))
  nlinarith

lemma integral_rpow_exp_half {r : ℝ} (hr : 0 < r) :
    ∫ t in Set.Ioi (0:ℝ), t ^ (-(1 / 2 : ℝ)) * Real.exp (-(r * t)) = Real.sqrt π / Real.sqrt r := by
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := r) (by norm_num) hr
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.Gamma_one_half_eq] at this
  rw [this, Real.sqrt_eq_rpow r, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
  ring

lemma integrableOn_rpow_exp_half {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(r * t))) (Set.Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2)) (p := 1) (b := r)
    (by norm_num) one_pos hr
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

lemma step2 {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {s : ℂ} (hs : s.re = 0) :
    mellin (LF A B) (1 - s) * (Real.sqrt π : ℂ) =
      Complex.Gamma ((1 - s) / 2) / 2 * mellin (hF A B) (s / 2) := by
  set k : ℝ → ℝ → ℝ := fun l t => t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * l ^ 2) *
    (Real.exp (-(A * t)) - Real.exp (-(B * t))) with hk
  set f : ℝ → ℝ → ℂ := fun l t => (l : ℂ) ^ (-s) * (k l t : ℂ) with hf
  have hk_nonneg : ∀ l t, 0 < t → 0 ≤ k l t := by
    intro l t ht
    have hle : Real.exp (-(B * t)) ≤ Real.exp (-(A * t)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    simp only [hk]
    have := Real.rpow_pos_of_pos ht (-(1 / 2 : ℝ))
    have := Real.exp_pos (-t * l ^ 2)
    apply mul_nonneg (by positivity) (by linarith)
  have hnorm : ∀ l t, 0 < l → 0 < t → ‖f l t‖ = k l t := by
    intro l t hl ht
    simp only [hf, norm_mul, norm_cpow_of_re_zero hl (z := -s) (by simp [hs]), one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk_nonneg l t ht)]
  have hmeas : Measurable (Function.uncurry f) := by
    simp only [hf, hk]
    fun_prop
  have hkint : ∀ t, 0 < t → ∫ l in Set.Ioi (0:ℝ), k l t =
      Real.sqrt π / 2 * ((Real.exp (-(A * t)) - Real.exp (-(B * t))) / t) := by
    intro t ht
    have e : ∀ l, k l t = (t ^ (-(1 / 2 : ℝ)) * (Real.exp (-(A * t)) - Real.exp (-(B * t)))) *
        Real.exp (-t * l ^ 2) := fun l => by simp only [hk]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_gaussian_Ioi, Real.sqrt_div' _ ht.le,
      Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp
    rw [Real.sq_sqrt ht.le]
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht' : 0 < t := ht
      have hbd : Integrable (fun l => k l t) (volume.restrict (Set.Ioi 0)) := by
        have := ((integrable_exp_neg_mul_sq ht').integrableOn (s := Set.Ioi 0)).const_mul
          (t ^ (-(1 / 2 : ℝ)) * (Real.exp (-(A * t)) - Real.exp (-(B * t))))
        refine this.congr (Filter.Eventually.of_forall (fun l => ?_))
        simp only [hk]; ring
      refine hbd.mono' (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun l hl => ?_)
      exact (hnorm l t hl ht').le
    · have heq : ∀ t ∈ Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), ‖f l t‖ =
          Real.sqrt π / 2 * ((Real.exp (-(A * t)) - Real.exp (-(B * t))) / t) := by
        intro t ht
        rw [← hkint t ht]
        exact setIntegral_congr_fun measurableSet_Ioi (fun l hl => hnorm l t hl ht)
      refine Integrable.congr ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun t ht => (heq t ht).symm)))
      refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hA).const_mul
        (Real.sqrt π / 2 * (B - A))) (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      obtain ⟨h0, h1⟩ := sub_exp_div_le hAB (show 0 < t from ht)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hpi : 0 ≤ Real.sqrt π / 2 := by positivity
      calc Real.sqrt π / 2 * ((Real.exp (-(A * t)) - Real.exp (-(B * t))) / t)
          ≤ Real.sqrt π / 2 * ((B - A) * Real.exp (-(A * t))) :=
            mul_le_mul_of_nonneg_left h1 hpi
        _ = Real.sqrt π / 2 * (B - A) * Real.exp (-A * t) := by rw [neg_mul]; ring
  have hswap := integral_integral_swap hint
  have hL : ∫ l in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ), f l t =
      mellin (LF A B) (1 - s) * (Real.sqrt π : ℂ) := by
    unfold mellin
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi (fun l hl => ?_)
    have hl' : 0 < l := hl
    simp only [hf]
    rw [integral_const_mul, integral_complex_ofReal]
    have e : ∀ t, k l t = t ^ (-(1 / 2 : ℝ)) * Real.exp (-((l ^ 2 + A) * t)) -
        t ^ (-(1 / 2 : ℝ)) * Real.exp (-((l ^ 2 + B) * t)) := by
      intro t
      simp only [hk]
      rw [mul_assoc, mul_sub, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    simp_rw [e]
    have hA' : 0 < l ^ 2 + A := by nlinarith [sq_nonneg l]
    have hB' : 0 < l ^ 2 + B := by nlinarith [sq_nonneg l]
    rw [integral_sub (integrableOn_rpow_exp_half hA') (integrableOn_rpow_exp_half hB'),
      integral_rpow_exp_half hA', integral_rpow_exp_half hB']
    simp only [LF, smul_eq_mul, show (1 : ℂ) - s - 1 = -s by ring]
    push_cast
    ring
  have hR : ∫ t in Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), f l t =
      Complex.Gamma ((1 - s) / 2) / 2 * mellin (hF A B) (s / 2) := by
    unfold mellin
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    have e : ∀ l, f l t = ((l : ℂ) ^ ((1 - s) - 1) * ((Real.exp (-t * l ^ 2) : ℝ) : ℂ)) *
        ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hF A B t := by
      intro l
      simp only [hf, hk, hF, show (1 : ℂ) - s - 1 = -s by ring]
      push_cast; ring
    simp_rw [e]
    rw [integral_mul_const, integral_mul_const, mellin_gauss ht' (by simp [hs])]
    rw [Complex.ofReal_cpow ht'.le, smul_eq_mul]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
    have hc : (t : ℂ) ^ (s / 2 - 1) = (t : ℂ) ^ (-((1 - s) / 2)) * (t : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ htc]; congr 1; push_cast; ring
    rw [hc]
    ring
  rw [← hL, hswap, hR]

lemma integral_Icc_cexp {A B t : ℝ} (hAB : A ≤ B) (ht : 0 < t) :
    ∫ y in Set.Icc A B, Complex.exp (-((y : ℂ) * t)) =
      (Complex.exp (-(A * t)) - Complex.exp (-(B * t))) / t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
  have hc : (-(t : ℂ)) ≠ 0 := by simp [ht.ne']
  have := integral_exp_mul_complex (a := A) (b := B) hc
  simp_rw [show ∀ y : ℝ, -((y : ℂ) * t) = -(t : ℂ) * y from fun y => by ring]
  rw [this]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring_nf

lemma mellin_IF {A B : ℝ} (hA : 0 < A) (z : ℂ) :
    mellin (IF A B) z = ∫ y in Set.Icc A B, (y : ℂ) ^ (z - 1) := by
  unfold mellin
  rw [show (fun y : ℝ => (y : ℂ) ^ (z - 1) • IF A B y) =
      Set.indicator (Set.Icc A B) (fun y => (y : ℂ) ^ (z - 1)) from ?_]
  · have hsubset : Set.Icc A B ⊆ Set.Ioi (0 : ℝ) :=
      fun _ hy => lt_of_lt_of_le hA hy.1
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsubset]
  · ext y
    simp only [IF, Set.indicator_apply, smul_eq_mul]
    split_ifs <;> simp

lemma step3 {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {s : ℂ} (hs : s.re = 0) :
    mellin (hF A B) (s / 2) = Complex.Gamma (1 + s / 2) * mellin (IF A B) (-s / 2) := by
  set f : ℝ → ℝ → ℂ := fun t y => (t : ℂ) ^ (s / 2) * Complex.exp (-((y : ℂ) * t)) with hf
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Icc A B))) := by
    have hbound : Integrable (fun p : ℝ × ℝ => Real.exp (-A * p.1) * (1 : ℝ))
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Icc A B))) := by
      exact Integrable.mul_prod (f := fun t => Real.exp (-A * t)) (g := fun _ => (1:ℝ))
        (exp_neg_integrableOn_Ioi 0 hA) (integrable_const _)
    refine hbound.mono' ?_ ?_
    · apply Measurable.aestronglyMeasurable
      simp only [hf]
      fun_prop
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Icc)]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      simp only [Set.mem_Icc] at hp2
      have hn : ‖(p.1 : ℂ) ^ (s / 2)‖ = 1 := norm_cpow_of_re_zero hp1 (by simp [hs])
      simp only [Function.uncurry, hf, norm_mul, hn, Complex.norm_exp, mul_one, one_mul]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      apply Real.exp_le_exp.mpr; nlinarith
  have hswap := integral_integral_swap hint
  have hL : ∫ t in Set.Ioi (0:ℝ), ∫ y in Set.Icc A B, f t y = mellin (hF A B) (s / 2) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [hf]
    rw [integral_const_mul, integral_Icc_cexp hAB ht]
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Set.mem_Ioi.mp ht))
    rw [smul_eq_mul, Complex.cpow_sub _ _ ht', Complex.cpow_one]
    simp only [hF]; push_cast
    field_simp
  have hR : ∫ y in Set.Icc A B, ∫ t in Set.Ioi (0:ℝ), f t y =
      Complex.Gamma (1 + s / 2) * mellin (IF A B) (-s / 2) := by
    have h1 : ∀ y ∈ Set.Icc A B, ∫ t in Set.Ioi (0:ℝ), f t y =
        Complex.Gamma (1 + s / 2) * (y : ℂ) ^ (-s / 2 - 1) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hA hy.1
      have := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := 1 + s / 2) (r := y)
        (by simp [hs]) hy0
      rw [show (1 + s / 2 - 1) = s / 2 by ring] at this
      simp only [hf]
      rw [this, one_div_cpow_eq hy0, mul_comm]
      congr 2; ring
    rw [setIntegral_congr_fun measurableSet_Icc h1, integral_const_mul, mellin_IF hA]
  rw [← hL, hswap, hR]

lemma gamma_identity {s : ℂ} (hs : s.re = 0) :
    Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 + s / 2) =
      (Real.sqrt π : ℂ) * Complex.Gamma (1 - s) *
        ((2 : ℂ) ^ s * Complex.Gamma (1 + s / 2) / Complex.Gamma (1 - s / 2)) := by
  have h := Complex.Gamma_mul_Gamma_add_half ((1 - s) / 2)
  rw [show (1 - s) / 2 + 1 / 2 = 1 - s / 2 by ring, show 2 * ((1 - s) / 2) = 1 - s by ring,
    show (1 : ℂ) - (1 - s) = s by ring] at h
  have hne : Complex.Gamma (1 - s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs])
  rw [mul_div_assoc', eq_div_iff hne]
  linear_combination Complex.Gamma (1 + s / 2) * h

end ChowlaOpus.MellinAux

namespace ChowlaOpus

theorem multStatement_holds : MultStatement := by
  have hconj : ∀ τ : ℝ, starRingEnd ℂ (1 + Complex.I * τ / 2) = 1 - Complex.I * (τ : ℂ) / 2 := by
    intro τ
    simp only [map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one, map_ofNat]
    ring
  have hre : ∀ τ : ℝ, 0 < (1 - Complex.I * (τ : ℂ) / 2).re := by
    intro τ; simp
  have h2 : ∀ τ : ℝ, ‖(2 : ℂ) ^ (Complex.I * τ)‖ = 1 := by
    intro τ
    have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2) (Complex.I * τ)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    unfold mult
    rw [norm_div, norm_mul, h2, one_mul, ← hconj, Complex.Gamma_conj, Complex.norm_conj]
    apply div_self
    rw [norm_ne_zero_iff]
    have := Complex.Gamma_ne_zero_of_re_pos (hre τ)
    rwa [← hconj, Complex.Gamma_conj, map_ne_zero] at this
  · simp [mult]
  · intro τ
    unfold mult
    rw [map_div₀, map_mul, ← Complex.Gamma_conj, ← Complex.Gamma_conj, hconj]
    have harg : (2 : ℂ).arg ≠ Real.pi := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_pos.ne
    have e1 : starRingEnd ℂ ((2 : ℂ) ^ (Complex.I * τ)) = (2 : ℂ) ^ (Complex.I * ((-τ : ℝ) : ℂ)) := by
      have := Complex.conj_cpow 2 (starRingEnd ℂ (Complex.I * τ)) harg
      rw [Complex.conj_conj, map_ofNat] at this
      rw [← this]
      congr 1
      simp
    have e2 : starRingEnd ℂ (1 - Complex.I * (τ : ℂ) / 2) = 1 - Complex.I * ((-τ : ℝ) : ℂ) / 2 := by
      simp only [map_sub, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one,
        map_ofNat, Complex.ofReal_neg]
      ring
    rw [e1, e2, show (1:ℂ) - Complex.I * τ / 2 = 1 + Complex.I * ((-τ:ℝ):ℂ) / 2 by push_cast; ring]

theorem mellinStatement_holds (hJ : J0Statement) (_hB : BesselPlaneStatement) :
    MellinStatement := by
  intro ξ x hx
  refine ⟨MellinAux.integrable_besselG hJ hx, ?_⟩
  set s : ℂ := Complex.I * ((2 * π * ξ : ℝ) : ℂ) with hs_def
  have hs : s.re = 0 := by simp [s]
  have hA : 0 < x ^ 2 := by positivity
  have hAB : x ^ 2 ≤ 1 + x ^ 2 := by linarith
  rw [MellinAux.lhs_eq_mellin, MellinAux.betaF_eq_mellin]
  have h1 := MellinAux.step1 hJ hx hs
  have h2 := MellinAux.step2 hA hAB hs
  have h3 := MellinAux.step3 hA hAB hs
  have h4 := MellinAux.gamma_identity hs
  have hmult : mult (2 * π * ξ) =
      (2 : ℂ) ^ s * Complex.Gamma (1 + s / 2) / Complex.Gamma (1 - s / 2) := rfl
  rw [hmult]
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs])
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  apply mul_left_cancel₀ (mul_ne_zero hpi hG)
  linear_combination (Real.sqrt π : ℂ) * h1 + h2 + Complex.Gamma ((1 - s) / 2) / 2 * h3 +
    (mellin (MellinAux.IF (x ^ 2) (1 + x ^ 2)) (-s / 2) / 2) * h4

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Annulus.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace AnnulusAux

open Set Filter Topology

lemma item2 (σ x : ℝ) : 0 ≤ annB σ x ∧ annB σ x ≤ 1 := by
  unfold annB; split_ifs <;> norm_num

/-- `L x = log (1 + x⁻²)`, twice the label mean. -/
noncomputable def L (x : ℝ) : ℝ := Real.log (1 + (x ^ 2)⁻¹)

lemma annB_meas (σ : ℝ) : Measurable (annB σ) := by
  unfold annB
  refine Measurable.ite ?_ measurable_const measurable_const
  rw [Set.ofPred_and]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

lemma int_ind_one {s : Set ℝ} (hs : MeasurableSet s) (h : volume s ≠ ⊤) :
    Integrable (s.indicator (1 : ℝ → ℝ)) :=
  (integrable_indicator_iff hs).2 (integrableOn_const h)

/-- For `x ≠ 0`, `σ ↦ annB σ x` is the indicator of `[log |x|, log (1 + x²) / 2]`. -/
lemma annB_sigma {x : ℝ} (hx : x ≠ 0) (σ : ℝ) :
    annB σ x = (Icc (Real.log |x|) (Real.log (1 + x ^ 2) / 2)).indicator 1 σ := by
  have hax : 0 < |x| := abs_pos.2 hx
  have h1 : |x| ≤ Real.exp σ ↔ Real.log |x| ≤ σ := (Real.log_le_iff_le_exp hax).symm
  have h2 : Real.exp σ ^ 2 ≤ 1 + x ^ 2 ↔ σ ≤ Real.log (1 + x ^ 2) / 2 := by
    rw [← Real.exp_nat_mul, le_div_iff₀ (by norm_num : (0:ℝ) < 2),
      Real.le_log_iff_exp_le (by positivity)]
    norm_num [mul_comm]
  unfold annB
  by_cases h : |x| ≤ Real.exp σ ∧ Real.exp σ ^ 2 ≤ 1 + x ^ 2
  · rw [if_pos h, indicator_of_mem]
    · rfl
    · exact ⟨h1.1 h.1, h2.1 h.2⟩
  · rw [if_neg h, indicator_of_notMem]
    rintro ⟨h3, h4⟩
    exact h ⟨h1.2 h3, h2.2 h4⟩

lemma annB_zero (σ : ℝ) : annB σ 0 = (Iic 0).indicator 1 σ := by
  unfold annB
  have : Real.exp σ ^ 2 ≤ 1 + 0 ^ 2 ↔ σ ≤ 0 := by
    rw [← Real.exp_nat_mul]; simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero, Real.exp_le_one_iff]
    constructor <;> intro <;> linarith
  by_cases h : σ ≤ 0
  · rw [if_pos ⟨by simp [(Real.exp_pos σ).le], this.2 h⟩, indicator_of_mem (by exact h)]
    rfl
  · rw [if_neg (fun h' => h (this.1 h'.2)), indicator_of_notMem (by exact h)]

lemma ellF_zero : ellF 0 = 0 := by
  unfold ellF
  apply integral_undef
  simp_rw [annB_zero]
  rw [integrable_indicator_iff measurableSet_Iic]
  intro h
  have := (integrableOn_const_iff (C := (1:ℝ)) (s := Iic (0:ℝ)) (μ := volume)).1 h
  simp [Real.volume_Iic] at this

lemma L_eq {x : ℝ} (hx : x ≠ 0) :
    L x = Real.log (1 + x ^ 2) - 2 * Real.log |x| := by
  unfold L
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  rw [show 1 + (x ^ 2)⁻¹ = (1 + x ^ 2) / x ^ 2 by field_simp; ring,
    Real.log_div (by positivity) hx2, Real.log_pow, Real.log_abs]
  push_cast; ring

lemma ellF_eq (x : ℝ) : ellF x = L x / 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ellF_zero, L]
  unfold ellF
  simp_rw [annB_sigma hx]
  have hle : Real.log |x| ≤ Real.log (1 + x ^ 2) / 2 := by
    have h2 : Real.log (|x| ^ 2) = 2 * Real.log |x| := by rw [Real.log_pow]; norm_num
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), mul_comm, ← h2, sq_abs]
    exact Real.log_le_log (by positivity) (by linarith)
  rw [integral_indicator_one measurableSet_Icc, Real.volume_real_Icc_of_le hle, L_eq hx]
  ring

lemma item4 (x : ℝ) (hx : x ≠ 0) : Integrable (fun σ => annB σ x) := by
  simp_rw [annB_sigma hx]
  exact int_ind_one measurableSet_Icc measure_Icc_lt_top.ne

lemma item5 (x : ℝ) (_hx : x ≠ 0) : ellF x = Real.log (1 + (x ^ 2)⁻¹) / 2 := ellF_eq x

lemma item6 (x : ℝ) : 0 ≤ ellF x := integral_nonneg (fun σ => (item2 σ x).1)

lemma item7 (x : ℝ) (hx : x ≠ 0) : ellF x ≤ 1 / (2 * x ^ 2) := by
  rw [ellF_eq, L]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + (x ^ 2)⁻¹ by positivity)
  rw [one_div, mul_inv, div_eq_mul_inv]
  nlinarith [show (0:ℝ) ≤ (x ^ 2)⁻¹ by positivity]

/-- The `x`-slice of the annulus: `[-r, r] \ (-s, s)` with `r = e^σ`, `s = √(r² - 1)`. -/
lemma annB_x (σ x : ℝ) : annB σ x =
    (Icc (-Real.exp σ) (Real.exp σ)).indicator 1 x -
      (Ioo (-Real.sqrt (Real.exp σ ^ 2 - 1)) (Real.sqrt (Real.exp σ ^ 2 - 1))).indicator 1 x := by
  set r := Real.exp σ with hr
  set s := Real.sqrt (r ^ 2 - 1) with hs
  have hsr : s < r := (Real.sqrt_lt' (Real.exp_pos σ)).2 (by linarith)
  have key : r ^ 2 ≤ 1 + x ^ 2 ↔ s ≤ |x| := by
    rw [hs, Real.sqrt_le_left (abs_nonneg x), sq_abs]; constructor <;> intro <;> linarith
  unfold annB
  rw [← hr]
  by_cases h1 : |x| ≤ r
  · rw [indicator_of_mem (show x ∈ Icc (-r) r from abs_le.1 h1)]
    by_cases h2 : r ^ 2 ≤ 1 + x ^ 2
    · rw [if_pos ⟨h1, h2⟩, indicator_of_notMem]
      · simp
      · intro h; have := abs_lt.2 h; linarith [key.1 h2]
    · rw [if_neg (fun h => h2 h.2), indicator_of_mem]
      · simp
      · exact abs_lt.1 (lt_of_not_ge (fun h => h2 (key.2 h)))
  · have hm : x ∉ Icc (-r) r := fun h => h1 (abs_le.mpr h)
    rw [if_neg (fun h => h1 h.1), indicator_of_notMem hm, indicator_of_notMem]
    · simp
    · intro h; have := abs_lt.2 h; linarith

lemma annB_integrable (σ : ℝ) : Integrable (annB σ) := by
  have : annB σ = fun x => (Icc (-Real.exp σ) (Real.exp σ)).indicator 1 x -
      (Ioo (-Real.sqrt (Real.exp σ ^ 2 - 1)) (Real.sqrt (Real.exp σ ^ 2 - 1))).indicator 1 x :=
    funext (annB_x σ)
  rw [this]
  exact (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne).sub
    (int_ind_one measurableSet_Ioo measure_Ioo_lt_top.ne)

lemma item10 (σ : ℝ) : Integrable (annB σ) ∧ ∫ x, annB σ x ≤ 2 * Real.exp (-|σ|) := by
  refine ⟨annB_integrable σ, ?_⟩
  simp_rw [annB_x σ]
  set r := Real.exp σ with hr
  set s := Real.sqrt (r ^ 2 - 1) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 < r := Real.exp_pos σ
  rw [integral_sub (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne)
      (int_ind_one measurableSet_Ioo measure_Ioo_lt_top.ne),
    integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Ioo,
    Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Ioo_of_le (by linarith)]
  rcases le_or_gt σ 0 with hσ | hσ
  · rw [abs_of_nonpos hσ, neg_neg, ← hr]; linarith
  · rw [abs_of_pos hσ, Real.exp_neg, ← hr]
    have hr1 : 1 < r := by rw [hr]; exact Real.one_lt_exp_iff.2 hσ
    have hss : s ^ 2 = r ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    have hsr : s ≤ r := by nlinarith
    rw [show r - -r - (s - -s) = 2 * (r - s) by ring]
    have : r - s ≤ 1 / r :=
      (le_div_iff₀ hr0).2 (by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hsr)])
    rw [one_div] at this
    linarith

/-- Pointwise bound for translating an interval indicator. -/
lemma shift_pt (I : Set ℝ) (a b δ : ℝ) (hδ : 0 ≤ δ) (h1 : Ioo a b ⊆ I) (h2 : I ⊆ Icc a b)
    (t : ℝ) : |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| ≤
      (Icc a (a + δ)).indicator (1 : ℝ → ℝ) t + (Icc b (b + δ)).indicator 1 t := by
  have hA : 0 ≤ (Icc a (a + δ)).indicator (1 : ℝ → ℝ) t :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  have hB : 0 ≤ (Icc b (b + δ)).indicator (1 : ℝ → ℝ) t :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases ht1 : t - δ ∈ I <;> by_cases ht2 : t ∈ I
  · rw [indicator_of_mem ht1, indicator_of_mem ht2]
    simp only [Pi.one_apply, sub_self, abs_zero]; linarith
  · rw [indicator_of_mem ht1, indicator_of_notMem ht2]
    simp only [Pi.one_apply, sub_zero, abs_one]
    have h4 := h2 ht1
    have h3 : ¬ (a < t ∧ t < b) := fun h => ht2 (h1 h)
    by_cases htb : b ≤ t
    · rw [indicator_of_mem (show t ∈ Icc b (b + δ) from ⟨htb, by linarith [h4.2]⟩)]
      simp only [Pi.one_apply]; linarith
    · have : t ≤ a := by
        by_contra h; exact h3 ⟨lt_of_not_ge h, lt_of_not_ge htb⟩
      rw [indicator_of_mem (show t ∈ Icc a (a + δ) from ⟨by linarith [h4.1], by linarith⟩)]
      simp only [Pi.one_apply]; linarith
  · rw [indicator_of_notMem ht1, indicator_of_mem ht2]
    simp only [Pi.one_apply, zero_sub, abs_neg, abs_one]
    have h4 := h2 ht2
    have h3 : ¬ (a < t - δ ∧ t - δ < b) := fun h => ht1 (h1 h)
    by_cases hta : t - δ ≤ a
    · rw [indicator_of_mem (show t ∈ Icc a (a + δ) from ⟨h4.1, by linarith⟩)]
      simp only [Pi.one_apply]; linarith
    · have : b ≤ t - δ := by
        by_contra h; exact h3 ⟨lt_of_not_ge hta, lt_of_not_ge h⟩
      rw [indicator_of_mem (show t ∈ Icc b (b + δ) from ⟨by linarith, by linarith [h4.2]⟩)]
      simp only [Pi.one_apply]; linarith
  · rw [indicator_of_notMem ht1, indicator_of_notMem ht2]
    simp only [sub_self, abs_zero]; linarith

lemma shift_int (I : Set ℝ) (a b δ : ℝ) (hI : MeasurableSet I) (h1 : Ioo a b ⊆ I)
    (h2 : I ⊆ Icc a b) :
    ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| ≤ 2 * |δ| := by
  have hg : Integrable (I.indicator (1 : ℝ → ℝ)) :=
    int_ind_one hI (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono h2))
  have key : ∀ δ : ℝ, 0 ≤ δ →
      ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| ≤ 2 * δ := by
    intro δ hδ
    calc ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t|
        ≤ ∫ t, ((Icc a (a + δ)).indicator (1 : ℝ → ℝ) t + (Icc b (b + δ)).indicator 1 t) :=
          integral_mono ((hg.comp_sub_right δ).sub hg).abs
            ((int_ind_one measurableSet_Icc measure_Icc_lt_top.ne).add
              (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne))
            (fun t => shift_pt I a b δ hδ h1 h2 t)
      _ = 2 * δ := by
          rw [integral_add (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne)
              (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne),
            integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
            Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le (by linarith)]
          ring
  rcases le_total 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ]; exact key δ hδ
  · rw [abs_of_nonpos hδ]
    have : ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| =
        ∫ t, |I.indicator (1 : ℝ → ℝ) (t - -δ) - I.indicator 1 t| := by
      rw [← integral_add_right_eq_self
        (fun t => |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t|) δ]
      congr 1; ext t
      simp only [add_sub_cancel_right, sub_neg_eq_add]
      rw [abs_sub_comm]
    rw [this]; exact key (-δ) (by linarith)

lemma abs_sub_le_add_of_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : |p - q| ≤ p + q :=
  abs_le.2 ⟨by linarith, by linarith⟩

lemma item11 (x δ : ℝ) (hx : x ≠ 0) :
    ∫ σ, |annB (σ - δ) x - annB σ x| ≤ 2 * min |δ| (ellF x) := by
  have hint := item4 x hx
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  apply le_min
  · simp_rw [annB_sigma hx]
    exact shift_int _ _ _ δ measurableSet_Icc Ioo_subset_Icc_self subset_rfl
  · calc ∫ σ, |annB (σ - δ) x - annB σ x|
        ≤ ∫ σ, (annB (σ - δ) x + annB σ x) :=
          integral_mono ((hint.comp_sub_right δ).sub hint).abs
            ((hint.comp_sub_right δ).add hint)
            (fun σ => abs_sub_le_add_of_nonneg (item2 _ _).1 (item2 _ _).1)
      _ = 2 * ellF x := by
          rw [integral_add (hint.comp_sub_right δ) hint,
            integral_sub_right_eq_self (fun σ => annB σ x) δ]
          unfold ellF; ring

lemma item12 (σ u : ℝ) :
    ∫ x, |annB σ (x - u) - annB σ x| ≤ min (4 * |u|) (4 * Real.exp (-|σ|)) := by
  obtain ⟨hint, hle⟩ := item10 σ
  apply le_min
  · set r := Real.exp σ with hr
    set s := Real.sqrt (r ^ 2 - 1) with hs
    have hg1 : Integrable ((Icc (-r) r).indicator (1 : ℝ → ℝ)) :=
      int_ind_one measurableSet_Icc measure_Icc_lt_top.ne
    have hg2 : Integrable ((Ioo (-s) s).indicator (1 : ℝ → ℝ)) :=
      int_ind_one measurableSet_Ioo measure_Ioo_lt_top.ne
    have hi1 : Integrable (fun x =>
        |(Icc (-r) r).indicator (1 : ℝ → ℝ) (x - u) - (Icc (-r) r).indicator 1 x|) :=
      ((hg1.comp_sub_right u).sub hg1).abs
    have hi2 : Integrable (fun x =>
        |(Ioo (-s) s).indicator (1 : ℝ → ℝ) (x - u) - (Ioo (-s) s).indicator 1 x|) :=
      ((hg2.comp_sub_right u).sub hg2).abs
    calc ∫ x, |annB σ (x - u) - annB σ x|
        ≤ ∫ x, (|(Icc (-r) r).indicator (1 : ℝ → ℝ) (x - u) - (Icc (-r) r).indicator 1 x| +
            |(Ioo (-s) s).indicator (1 : ℝ → ℝ) (x - u) - (Ioo (-s) s).indicator 1 x|) := by
          refine integral_mono ((hint.comp_sub_right u).sub hint).abs
            (hi1.add hi2)
            (fun x => ?_)
          simp only
          rw [annB_x σ (x - u), annB_x σ x, ← hr, ← hs]
          refine le_trans (le_of_eq ?_) (abs_sub _ _)
          ring_nf
      _ = (∫ x, |(Icc (-r) r).indicator (1 : ℝ → ℝ) (x - u) - (Icc (-r) r).indicator 1 x|) +
            ∫ x, |(Ioo (-s) s).indicator (1 : ℝ → ℝ) (x - u) - (Ioo (-s) s).indicator 1 x| :=
          integral_add hi1 hi2
      _ ≤ 2 * |u| + 2 * |u| :=
          add_le_add (shift_int _ _ _ u measurableSet_Icc Ioo_subset_Icc_self subset_rfl)
            (shift_int _ _ _ u measurableSet_Ioo subset_rfl Ioo_subset_Icc_self)
      _ = 4 * |u| := by ring
  · calc ∫ x, |annB σ (x - u) - annB σ x|
        ≤ ∫ x, (annB σ (x - u) + annB σ x) :=
          integral_mono ((hint.comp_sub_right u).sub hint).abs
            ((hint.comp_sub_right u).add hint)
            (fun x => abs_sub_le_add_of_nonneg (item2 _ _).1 (item2 _ _).1)
      _ = 2 * ∫ x, annB σ x := by
          rw [integral_add (hint.comp_sub_right u) hint,
            integral_sub_right_eq_self (fun x => annB σ x) u]
          ring
      _ ≤ 4 * Real.exp (-|σ|) := by linarith

/-- Integers `j` with `σ + j T` in the label interval of `x`. -/
lemma annB_shift_eq_zero {x : ℝ} (hx : x ≠ 0) {T : ℝ} (hT : 0 < T) (σ : ℝ) (j : ℤ)
    (hj : j ∉ Finset.Icc ⌈(Real.log |x| - σ) / T⌉ ⌊(Real.log (1 + x ^ 2) / 2 - σ) / T⌋) :
    annB (σ + j * T) x = 0 := by
  rw [annB_sigma hx, indicator_of_notMem]
  rintro ⟨h1, h2⟩
  apply hj
  rw [Finset.mem_Icc]
  constructor
  · exact Int.ceil_le.2 (by rw [div_le_iff₀ hT]; linarith)
  · exact Int.le_floor.2 (by rw [le_div_iff₀ hT]; linarith)

lemma item13 (T σ x : ℝ) (hT : 1 ≤ T) (hx : x ≠ 0) :
    Summable (fun j : ℤ => annB (σ + j * T) x) :=
  summable_of_ne_finset_zero (fun j hj => annB_shift_eq_zero hx (by linarith) σ j hj)


lemma L_nonneg (x : ℝ) : 0 ≤ L x :=
  Real.log_nonneg (by have : 0 ≤ (x ^ 2)⁻¹ := by positivity
                      linarith)

lemma L_abs (x : ℝ) : L |x| = L x := by simp [L, sq_abs]

/-- Antiderivative of `L` on `(0, ∞)`. -/
noncomputable def F (x : ℝ) : ℝ := x * L x + 2 * Real.arctan x

lemma mulL_eq (x : ℝ) : x * L x = x * Real.log (1 + x ^ 2) - 2 * (x * Real.log x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [L_eq hx, Real.log_abs]; ring

lemma F_cont : Continuous F := by
  have : F = fun x => x * Real.log (1 + x ^ 2) - 2 * (x * Real.log x) + 2 * Real.arctan x :=
    funext (fun x => by unfold F; rw [mulL_eq])
  rw [this]
  have h1 : Continuous (fun x : ℝ => Real.log (1 + x ^ 2)) :=
    Continuous.log (by fun_prop) (fun x => by positivity)
  exact ((continuous_id.mul h1).sub (continuous_const.mul Real.continuous_mul_log)).add
    (continuous_const.mul Real.continuous_arctan)

lemma F_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt F (L x) x := by
  have hx2 : x ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 * x) / (x ^ 2) ^ 2) x := h1.inv hx2
  have h3 : HasDerivAt (fun y : ℝ => 1 + (y ^ 2)⁻¹) (-(2 * x) / (x ^ 2) ^ 2) x :=
    h2.const_add 1
  have h4 : HasDerivAt (fun y : ℝ => Real.log (1 + (y ^ 2)⁻¹))
      ((-(2 * x) / (x ^ 2) ^ 2) / (1 + (x ^ 2)⁻¹)) x := h3.log (by positivity)
  have h5 : HasDerivAt (fun y : ℝ => y * Real.log (1 + (y ^ 2)⁻¹))
      (1 * Real.log (1 + (x ^ 2)⁻¹) + x * ((-(2 * x) / (x ^ 2) ^ 2) / (1 + (x ^ 2)⁻¹))) x :=
    (hasDerivAt_id' x).mul h4
  have h6 : HasDerivAt (fun y => 2 * Real.arctan y) (2 * (1 / (1 + x ^ 2))) x :=
    (Real.hasDerivAt_arctan x).const_mul 2
  have h7 := h5.add h6
  unfold F L
  convert h7 using 1 <;> try rfl
  all_goals (try field_simp) <;> ring

lemma F_zero : F 0 = 0 := by simp [F, L]

lemma F_tendsto : Tendsto F atTop (𝓝 Real.pi) := by
  have h1 : Tendsto (fun x => x * L x) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact mul_nonneg hx.le (L_nonneg x)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + (x ^ 2)⁻¹ by positivity)
      unfold L
      calc x * Real.log (1 + (x ^ 2)⁻¹) ≤ x * (x ^ 2)⁻¹ := by gcongr; linarith
        _ = x⁻¹ := by field_simp
  have h2 : Tendsto (fun x => 2 * Real.arctan x) atTop (𝓝 Real.pi) := by
    have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul 2
    convert this using 2; ring
  have := h1.add h2
  rw [zero_add] at this
  exact this

lemma L_integrableOn : IntegrableOn L (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg F_cont.continuousWithinAt (fun _ hx => F_deriv hx)
    (fun x _ => L_nonneg x) F_tendsto

lemma L_integral : ∫ x in Ioi (0:ℝ), L x = Real.pi := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg (g := F) (a := 0) F_cont.continuousWithinAt
    (fun _ hx => F_deriv hx) (fun x _ => L_nonneg x) F_tendsto
  rw [this, F_zero, sub_zero]

lemma integrable_comp_abs' {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by show f x = f |x|; rw [abs_of_pos (mem_Ioi.1 hx)])
      measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ))]
  exact int_Iic.union hf'

lemma ellF_eq_abs : ellF = fun x => L |x| / 2 := funext fun x => by rw [ellF_eq, L_abs]

lemma item8 : Integrable ellF := by
  rw [ellF_eq_abs]; exact (integrable_comp_abs' L_integrableOn).div_const 2

lemma item9 : ∫ x, ellF x = Real.pi := by
  rw [ellF_eq_abs, integral_div, integral_comp_abs (f := L), L_integral]; ring

/- ### The periodization -/

/-- Threshold `δ_T = (e^{2T} - 1)^{-1/2}`: `ℓ(x) ≥ T ⇒ |x| ≤ δ_T`. -/
noncomputable def dT (T : ℝ) : ℝ := Real.sqrt ((Real.exp (2 * T) - 1)⁻¹)

lemma perB_meas (T σ : ℝ) : Measurable (perB T σ) := by
  unfold perB
  exact Measurable.tsum (fun j => annB_meas _)

lemma ellF_eq_sub {x : ℝ} (hx : x ≠ 0) :
    ellF x = Real.log (1 + x ^ 2) / 2 - Real.log |x| := by
  rw [ellF_eq, L_eq hx]; ring

lemma mem_dT {T x : ℝ} (hT : 0 < T) (hx : x ≠ 0) (h : T ≤ ellF x) :
    x ∈ Icc (-dT T) (dT T) := by
  rw [ellF_eq, L] at h
  have h1 : Real.exp (2 * T) ≤ 1 + (x ^ 2)⁻¹ :=
    (Real.le_log_iff_exp_le (by positivity)).1 (by linarith)
  have hE : 0 < Real.exp (2 * T) - 1 := by
    have := Real.add_one_le_exp (2 * T); linarith
  have h2 : x ^ 2 ≤ (Real.exp (2 * T) - 1)⁻¹ :=
    (le_inv_comm₀ hE (by positivity)).1 (by linarith)
  exact abs_le.1 (Real.abs_le_sqrt h2)

lemma perB_bound {T σ x : ℝ} (hT : 0 < T) (hx : x ≠ 0) :
    max (perB T σ x - 1) 0 ≤ (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x := by
  set a := Real.log |x|
  set b := Real.log (1 + x ^ 2) / 2
  set m := ⌈(a - σ) / T⌉ with hm
  set M := ⌊(b - σ) / T⌋ with hM
  have hsum : perB T σ x = ∑ j ∈ Finset.Icc m M, annB (σ + j * T) x :=
    tsum_eq_sum (fun j hj => annB_shift_eq_zero hx hT σ j hj)
  have hle : perB T σ x ≤ ((Finset.Icc m M).card : ℝ) := by
    rw [hsum]
    refine (Finset.sum_le_card_nsmul _ _ 1 (fun j _ => (item2 _ _).2)).trans ?_
    simp
  have hMm : (M : ℝ) - m ≤ ellF x / T := by
    have h1 : (M : ℝ) ≤ (b - σ) / T := Int.floor_le _
    have h2 : (a - σ) / T ≤ m := Int.le_ceil _
    rw [ellF_eq_sub hx]
    have : (b - σ) / T - (a - σ) / T = (b - a) / T := by ring
    linarith
  have hpos : 0 ≤ (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x :=
    indicator_nonneg (fun y _ => div_nonneg (item6 y) hT.le) _
  rcases le_or_gt M m with hk | hk
  · have : (Finset.Icc m M).card ≤ 1 := by rw [Int.card_Icc]; omega
    have : ((Finset.Icc m M).card : ℝ) ≤ 1 := by exact_mod_cast this
    rw [max_eq_right (by linarith)]; exact hpos
  · have hcard : ((Finset.Icc m M).card : ℝ) = M + 1 - m := by
      have := Int.card_Icc_of_le m M (show m ≤ M + 1 by omega)
      have h' : (((Finset.Icc m M).card : ℤ) : ℝ) = ((M + 1 - m : ℤ) : ℝ) := by rw [this]
      push_cast at h'; exact h'
    have h1 : 1 ≤ ellF x / T := by
      have : (1 : ℝ) ≤ M - m := by exact_mod_cast (by omega : (1 : ℤ) ≤ M - m)
      linarith
    have hxδ : x ∈ Icc (-dT T) (dT T) :=
      mem_dT hT hx (by rwa [le_div_iff₀ hT, one_mul] at h1)
    rw [indicator_of_mem hxδ]
    exact max_le (by linarith) (div_nonneg (item6 x) hT.le)

lemma bound_integral {T : ℝ} (hT : 0 < T) :
    ∫ x, (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x = F (dT T) / T := by
  have hδ0 : 0 ≤ dT T := Real.sqrt_nonneg _
  have : (fun x => (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x) =
      fun x => (Iic (dT T)).indicator (fun y => L y / (2 * T)) |x| := by
    funext x
    by_cases hx : |x| ≤ dT T
    · have hl : x ∈ Icc (-dT T) (dT T) := abs_le.mp hx
      have hr : |x| ∈ Iic (dT T) := hx
      rw [indicator_of_mem hl, indicator_of_mem hr, ellF_eq, L_abs]
      field_simp
    · have hl : x ∉ Icc (-dT T) (dT T) := fun h => hx (abs_le.mpr h)
      have hr : |x| ∉ Iic (dT T) := hx
      rw [indicator_of_notMem hl, indicator_of_notMem hr]
  rw [this, integral_comp_abs, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le hδ0, intervalIntegral.integral_div,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ0 F_cont.continuousOn
      (fun x hx => F_deriv hx.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ0).2
        (L_integrableOn.mono_set Ioc_subset_Ioi_self)), F_zero]
  field_simp
  ring

lemma F_dT_le {T : ℝ} (hT : 0 < T) : F (dT T) ≤ 2 * T * dT T + 2 * dT T := by
  have hδ0 : 0 ≤ dT T := Real.sqrt_nonneg _
  have hE : 0 < Real.exp (2 * T) - 1 := by
    have := Real.add_one_le_exp (2 * T); linarith
  have hL : L (dT T) = 2 * T := by
    unfold L dT
    rw [Real.sq_sqrt (inv_nonneg.2 hE.le), inv_inv, add_sub_cancel, Real.log_exp]
  unfold F
  rw [hL]
  have hmono : Monotone (fun x : ℝ => x - Real.arctan x) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hasDerivAt_id' x).sub (Real.hasDerivAt_arctan x))
    intro x
    apply sub_nonneg.mpr
    exact (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).mpr (by nlinarith [sq_nonneg x])
  have hs := hmono hδ0
  simp only [Real.arctan_zero, sub_zero] at hs
  linarith

lemma dT_le {T : ℝ} (hT : 1 ≤ T) : 4 * dT T ≤ 5 * Real.exp (-T) := by
  have hu : 2 ≤ Real.exp T := by have := Real.add_one_le_exp T; linarith
  have hE : Real.exp (2 * T) = Real.exp T ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 : dT T ≤ 5 / 4 * Real.exp (-T) := by
    unfold dT
    rw [Real.sqrt_le_left (by positivity), hE, Real.exp_neg]
    rw [show (5 / 4 * (Real.exp T)⁻¹) ^ 2 = 25 / (16 * Real.exp T ^ 2) by field_simp; ring,
      inv_eq_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  linarith

lemma item14 (T σ : ℝ) (hT : 1 ≤ T) : Integrable (fun x => max (perB T σ x - 1) 0) ∧
    ∫ x, max (perB T σ x - 1) 0 ≤ 5 * Real.exp (-T) := by
  have hT0 : 0 < T := by linarith
  have hg : Integrable ((Icc (-dT T) (dT T)).indicator (fun y => ellF y / T)) :=
    (item8.div_const T).indicator measurableSet_Icc
  have hmeas : Measurable (fun x => max (perB T σ x - 1) 0) :=
    ((perB_meas T σ).sub_const 1).max measurable_const
  have hae : ∀ᵐ x ∂volume, max (perB T σ x - 1) 0 ≤
      (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x := by
    filter_upwards [Measure.ae_ne volume 0] with x hx
    exact perB_bound hT0 hx
  refine ⟨hg.mono' hmeas.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hae] with x hx
    rwa [Real.norm_of_nonneg (le_max_right _ _)]
  · calc ∫ x, max (perB T σ x - 1) 0
        ≤ ∫ x, (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => le_max_right _ _)) hg hae
      _ = F (dT T) / T := bound_integral hT0
      _ ≤ (2 * T * dT T + 2 * dT T) / T := by gcongr; exact F_dT_le hT0
      _ ≤ 4 * dT T := by
          rw [div_le_iff₀ hT0]
          have : 0 ≤ dT T := Real.sqrt_nonneg _
          nlinarith
      _ ≤ 5 * Real.exp (-T) := dT_le hT


/- ### Measurability, symmetry and the label transform `β_ξ` -/

lemma item1 : Measurable (Function.uncurry annB) := by
  unfold Function.uncurry annB
  refine Measurable.ite ?_ measurable_const measurable_const
  rw [Set.ofPred_and]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

lemma item3 (σ x : ℝ) : annB σ (-x) = annB σ x := by
  simp [annB]

lemma ee_continuous : Continuous ee := by
  unfold ee; fun_prop

lemma annB_meas_swap : Measurable (fun p : ℝ × ℝ => annB p.2 p.1) := by
  have := item1.comp measurable_swap
  simp only [Function.comp_def, Function.uncurry_def, Prod.fst_swap, Prod.snd_swap] at this
  exact this

lemma item15 (ξ : ℝ) : Measurable (betaF ξ) := by
  have h2 : Measurable (fun p : ℝ × ℝ => ee (-(ξ * p.2))) :=
    (ee_continuous.comp (by fun_prop)).measurable
  have h : Measurable (fun p : ℝ × ℝ => ((annB p.2 p.1 : ℝ) : ℂ) * ee (-(ξ * p.2))) :=
    (Complex.measurable_ofReal.comp annB_meas_swap).mul h2
  have := h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  exact this.measurable

lemma item16 (ξ x : ℝ) : ‖betaF ξ x‖ ≤ ellF x := by
  unfold betaF ellF
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext σ
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (item2 σ x).1]

lemma item17 (x : ℝ) : betaF 0 x = ellF x := by
  unfold betaF ellF
  simp only [zero_mul, neg_zero, ee_zero, mul_one]
  exact integral_ofReal

lemma item18 (ξ x : ℝ) : betaF (-ξ) x = starRingEnd ℂ (betaF ξ x) := by
  unfold betaF
  rw [← integral_conj]
  congr 1; ext σ
  rw [map_mul, Complex.conj_ofReal, ← ee_neg]
  congr 2; ring

lemma item19 (ξ x : ℝ) : betaF ξ (-x) = betaF ξ x := by
  unfold betaF
  simp_rw [item3]

end AnnulusAux

open AnnulusAux in
theorem annulusStatement_holds : AnnulusStatement :=
  ⟨item1, item2, item3, item4, item5, item6, item7, item8, item9, item10, item11, item12,
    item13, item14, item15, item16, item17, item18, item19⟩

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Coeff.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace CoeffAux

variable {ρ : ℝ → ℝ}

/- ### The bump `ρ`, the cutoff `ψ` and the mollifier `ρ_h` -/

lemma rho0_pos (hρ : IsBump ρ) : 0 < ρ 0 := by
  by_contra h
  push Not at h
  have h0 : ∀ x, ρ x = 0 := fun x => le_antisymm ((hρ.le_at_zero x).trans h) (hρ.nonneg x)
  have h1 := hρ.integral_eq
  simp [h0] at h1

lemma psi_nonneg (hρ : IsBump ρ) (u : ℝ) : 0 ≤ psiF ρ u :=
  div_nonneg (hρ.nonneg u) (rho0_pos hρ).le

lemma psi_le_one (hρ : IsBump ρ) (u : ℝ) : psiF ρ u ≤ 1 :=
  div_le_one_of_le₀ (hρ.le_at_zero u) (rho0_pos hρ).le

lemma psi_zero (hρ : IsBump ρ) : psiF ρ 0 = 1 := div_self (rho0_pos hρ).ne'

lemma psi_supp (hρ : IsBump ρ) (u : ℝ) (hu : 1 ≤ |u|) : psiF ρ u = 0 := by
  simp [psiF, hρ.supp u hu]

lemma psi_even (hρ : IsBump ρ) (u : ℝ) : psiF ρ (-u) = psiF ρ u := by
  simp [psiF, hρ.even u]

lemma psi_contDiff (hρ : IsBump ρ) : ContDiff ℝ ∞ (psiF ρ) :=
  hρ.smooth.div_const _

lemma rhoH_nonneg (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ rhoH ρ h y :=
  div_nonneg (hρ.nonneg _) hh.le

lemma rhoH_even (hρ : IsBump ρ) (h y : ℝ) : rhoH ρ h (-y) = rhoH ρ h y := by
  simp [rhoH, neg_div, hρ.even]

lemma rhoH_supp (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) (hy : h ≤ |y|) :
    rhoH ρ h y = 0 := by
  have : 1 ≤ |y / h| := by
    rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]; linarith
  simp [rhoH, hρ.supp _ this]

lemma rhoH_le (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : rhoH ρ h y ≤ ρ 0 / h :=
  div_le_div_of_nonneg_right (hρ.le_at_zero _) hh.le

lemma rhoH_contDiff (hρ : IsBump ρ) (h : ℝ) : ContDiff ℝ ∞ (rhoH ρ h) :=
  (hρ.smooth.comp (contDiff_id.div_const h)).div_const h

lemma rhoH_continuous (hρ : IsBump ρ) (h : ℝ) : Continuous (rhoH ρ h) :=
  (rhoH_contDiff hρ h).continuous

lemma rhoH_hasCompactSupport (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) :
    HasCompactSupport (rhoH ρ h) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -h) (b := h)) (fun y hy => ?_)
  apply rhoH_supp hρ hh
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  rcases hy with hy | hy
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma rhoH_integral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : ∫ y, rhoH ρ h y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div (fun y => ρ y) h, hρ.integral_eq, abs_of_pos hh,
    smul_eq_mul, mul_one, div_self hh.ne']

lemma rhoH_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : Integrable (rhoH ρ h) :=
  (rhoH_continuous hρ h).integrable_of_hasCompactSupport (rhoH_hasCompactSupport hρ hh)

lemma hT_pos {T : ℝ} (hTpos : 0 < T) : 0 < hT T := by unfold hT; positivity

lemma aT_nonneg (hρ : IsBump ρ) (T : ℝ) : 0 ≤ aT ρ T := by
  unfold aT; have := (rho0_pos hρ).le; positivity

/-- Integrability of `ρ_h · g(x - ·)` for integrable `g`. -/
lemma integrable_rhoH_mul (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {g : ℝ → ℝ}
    (hg : Integrable g) (x : ℝ) : Integrable (fun y => rhoH ρ h y * g (x - y)) := by
  refine (hg.comp_sub_left x).bdd_mul (c := ρ 0 / h)
    (rhoH_continuous hρ h).aestronglyMeasurable ?_
  refine ae_of_all _ (fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hh y)]
  exact rhoH_le hρ hh y

/- ### Consequences of `AnnulusStatement` -/

lemma ellF_nonneg (hA : AnnulusStatement) (x : ℝ) : 0 ≤ ellF x := hA.2.2.2.2.2.1 x

lemma ellF_integrable (hA : AnnulusStatement) : Integrable ellF := hA.2.2.2.2.2.2.2.1

lemma ellF_even (hA : AnnulusStatement) (x : ℝ) : ellF (-x) = ellF x := by
  obtain ⟨-, -, hBeven, -⟩ := hA
  simp [ellF, hBeven]

lemma betaF_integrable (hA : AnnulusStatement) (ξ : ℝ) : Integrable (betaF ξ) := by
  obtain ⟨-, -, -, -, -, -, -, hellint, -, -, -, -, -, -, hβm, hβle, -⟩ := hA
  exact hellint.mono' (hβm ξ).aestronglyMeasurable (ae_of_all _ (hβle ξ))

/- ### Smoothness -/

lemma conv_contDiff (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (ξ : ℝ) :
    ContDiff ℝ 2 (fun x => ∫ y, (rhoH ρ h y : ℂ) * betaF ξ (x - y)) := by
  have heq : (fun x => ∫ y, (rhoH ρ h y : ℂ) * betaF ξ (x - y)) =
      convolution (rhoH ρ h) (betaF ξ) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    ext x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul]
  rw [heq]
  exact (rhoH_hasCompactSupport hρ hh).contDiff_convolution_left (n := 2) _
    ((rhoH_contDiff hρ h).of_le (by norm_cast))
    (betaF_integrable hA ξ).locallyIntegrable

lemma psi_scaled_contDiff (hρ : IsBump ρ) (c T : ℝ) :
    ContDiff ℝ 2 (fun x => ((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
    (((psi_contDiff hρ).of_le (by norm_cast)).comp (contDiff_id.div_const _)))

/- ### The zeroth coefficient -/

/-- The smoothed label mean `(ρ_h ∗ ℓ)(x)`. -/
noncomputable def Sm (ρ : ℝ → ℝ) (h x : ℝ) : ℝ := ∫ y, rhoH ρ h y * ellF (x - y)

lemma bL_zero_eq (hA : AnnulusStatement) (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (x : ℝ) :
    bL ρ T J 0 x = ((psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) * Sm ρ (hT T) x : ℝ) : ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hβ0, -⟩ := hA
  unfold bL Sm
  simp only [Int.cast_zero, zero_div, hβ0, fejerCoeff_zero]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, ← Complex.ofReal_mul]
  congr 1; ring

lemma Sm_nonneg (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 ≤ Sm ρ h x :=
  integral_nonneg (fun y => mul_nonneg (rhoH_nonneg hρ hh y) (ellF_nonneg hA _))

lemma ellF_le_log_add (hA : AnnulusStatement) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (y : ℝ)
    (hy : y ≠ 0) : ellF y ≤ Real.log h⁻¹ + ellF (y / h) := by
  obtain ⟨-, -, -, -, hell, -⟩ := hA
  have hyh : y / h ≠ 0 := div_ne_zero hy hh.ne'
  rw [hell y hy, hell _ hyh]
  have hy2 : 0 < y ^ 2 := by positivity
  have h1 : 1 ≤ h⁻¹ ^ 2 := by
    have : 1 ≤ h⁻¹ := one_le_inv_iff₀.mpr ⟨hh, hh1⟩
    nlinarith
  have heq : h⁻¹ ^ 2 * (1 + ((y / h) ^ 2)⁻¹) = h⁻¹ ^ 2 + (y ^ 2)⁻¹ := by
    field_simp
  have hle : Real.log (1 + (y ^ 2)⁻¹) ≤ Real.log (h⁻¹ ^ 2 * (1 + ((y / h) ^ 2)⁻¹)) := by
    apply Real.log_le_log (by positivity)
    rw [heq]; linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hle
  push_cast at hle
  linarith

lemma Sm_zero_le (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Sm ρ h 0 ≤ Real.log h⁻¹ + ρ 0 * π := by
  have hellint := ellF_integrable hA
  have hellpi : ∫ x, ellF x = π := hA.2.2.2.2.2.2.2.2.1
  have hρint : Integrable (fun z => ρ z * ellF z) := by
    refine hellint.bdd_mul (c := ρ 0) hρ.smooth.continuous.aestronglyMeasurable
      (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg z)]
    exact hρ.le_at_zero z
  have i2 : Integrable (fun y => rhoH ρ h y * ellF (y / h)) := by
    refine (hellint.comp_div hh.ne').bdd_mul (c := ρ 0 / h)
      (rhoH_continuous hρ h).aestronglyMeasurable (ae_of_all _ (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hh y)]
    exact rhoH_le hρ hh y
  have i1 : Integrable (fun y => rhoH ρ h y * Real.log h⁻¹) :=
    (rhoH_integrable hρ hh).mul_const _
  have h1 : Sm ρ h 0 ≤ ∫ y, rhoH ρ h y * (Real.log h⁻¹ + ellF (y / h)) := by
    unfold Sm
    refine integral_mono_ae (integrable_rhoH_mul hρ hh hellint 0) ?_ ?_
    · simp_rw [mul_add]
      exact i1.add i2
    · filter_upwards [Measure.ae_ne volume 0] with y hy
      rw [zero_sub, ellF_even hA]
      exact mul_le_mul_of_nonneg_left (ellF_le_log_add hA hh hh1 y hy) (rhoH_nonneg hρ hh y)
  have h2 : ∫ y, rhoH ρ h y * (Real.log h⁻¹ + ellF (y / h)) =
      Real.log h⁻¹ + ∫ z, ρ z * ellF z := by
    simp_rw [mul_add]
    rw [integral_add i1 i2, integral_mul_const, rhoH_integral hρ hh, one_mul]
    congr 1
    unfold rhoH
    have : (fun y => ρ (y / h) / h * ellF (y / h)) =
        fun y => h⁻¹ * ((fun z => ρ z * ellF z) (y / h)) := by
      ext y; simp only; ring
    rw [this, integral_const_mul, Measure.integral_comp_div (fun z => ρ z * ellF z) h, abs_of_pos hh,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
  have h3 : ∫ z, ρ z * ellF z ≤ ρ 0 * π := by
    rw [← hellpi, ← integral_const_mul]
    refine integral_mono hρint (hellint.const_mul _) (fun z => ?_)
    exact mul_le_mul_of_nonneg_right (hρ.le_at_zero z) (ellF_nonneg hA z)
  linarith

lemma Sm_int_le (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2)
    (j : ℤ) (hj : j ≠ 0) : Sm ρ h j ≤ 2 / (j : ℝ) ^ 2 := by
  have hellint := ellF_integrable hA
  have hellle : ∀ x, x ≠ 0 → ellF x ≤ 1 / (2 * x ^ 2) := hA.2.2.2.2.2.2.1
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj
  have pw : ∀ y, rhoH ρ h y * ellF (j - y) ≤ rhoH ρ h y * (2 / (j : ℝ) ^ 2) := by
    intro y
    by_cases hy : h ≤ |y|
    · rw [rhoH_supp hρ hh y hy]; simp
    · push Not at hy
      apply mul_le_mul_of_nonneg_left _ (rhoH_nonneg hρ hh y)
      have hjy : |(j : ℝ)| / 2 ≤ |(j : ℝ) - y| := by
        have := abs_sub_abs_le_abs_sub (j : ℝ) y
        linarith
      have hpos : 0 < |(j : ℝ)| / 2 := by linarith
      have hne : (j : ℝ) - y ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hjy; linarith
      calc ellF (j - y) ≤ 1 / (2 * ((j : ℝ) - y) ^ 2) := hellle _ hne
        _ ≤ 1 / (2 * (|(j : ℝ)| / 2) ^ 2) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (|(j : ℝ)| / 2) ^ 2 ≤ ((j : ℝ) - y) ^ 2 := by
            rw [← sq_abs ((j : ℝ) - y)]; exact pow_le_pow_left₀ hpos.le hjy 2
          linarith
        _ = 2 / (j : ℝ) ^ 2 := by
          rw [div_pow, sq_abs]
          have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
          field_simp
  unfold Sm
  calc ∫ y, rhoH ρ h y * ellF (j - y) ≤ ∫ y, rhoH ρ h y * (2 / (j : ℝ) ^ 2) :=
        integral_mono (integrable_rhoH_mul hρ hh hellint _)
          ((rhoH_integrable hρ hh).mul_const _) pw
    _ = 2 / (j : ℝ) ^ 2 := by rw [integral_mul_const, rhoH_integral hρ hh, one_mul]

lemma Sm_ge (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2)
    (x : ℝ) (hx : |x| ≤ 1 / 2) : Real.log 2 / 2 ≤ Sm ρ h x := by
  have hellint := ellF_integrable hA
  have hell : ∀ x, x ≠ 0 → ellF x = Real.log (1 + (x ^ 2)⁻¹) / 2 := hA.2.2.2.2.1
  have pw : ∀ᵐ y, rhoH ρ h y * (Real.log 2 / 2) ≤ rhoH ρ h y * ellF (x - y) := by
    filter_upwards [Measure.ae_ne volume x] with y hyx
    by_cases hy : h ≤ |y|
    · rw [rhoH_supp hρ hh y hy]; simp
    · push Not at hy
      apply mul_le_mul_of_nonneg_left _ (rhoH_nonneg hρ hh y)
      have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
      rw [hell _ hne]
      have h1 : |x - y| ≤ 1 := by
        have := abs_sub x y
        linarith
      have h2 : (x - y) ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (x - y)]
      have h3 : 1 ≤ ((x - y) ^ 2)⁻¹ := one_le_inv_iff₀.mpr ⟨by positivity, h2⟩
      have : Real.log 2 ≤ Real.log (1 + ((x - y) ^ 2)⁻¹) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
  unfold Sm
  calc Real.log 2 / 2 = ∫ y, rhoH ρ h y * (Real.log 2 / 2) := by
        rw [integral_mul_const, rhoH_integral hρ hh, one_mul]
    _ ≤ _ := integral_mono_ae ((rhoH_integrable hρ hh).mul_const _)
          (integrable_rhoH_mul hρ hh hellint x) pw

lemma hasSum_int_inv_sq : HasSum (fun j : ℤ => 1 / (j : ℝ) ^ 2) (π ^ 2 / 3) := by
  have h1 : HasSum (fun n : ℕ => 1 / (((n : ℤ) : ℝ)) ^ 2) (π ^ 2 / 6) := by
    have := hasSum_zeta_two
    simp only [Int.cast_natCast]
    exact this
  have h2 : HasSum (fun n : ℕ => 1 / (((-((n : ℤ) + 1)) : ℤ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have h0 := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    have e : (fun n : ℕ => 1 / (((-((n : ℤ) + 1)) : ℤ) : ℝ) ^ 2) =
        fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
      ext n; push_cast; ring
    rw [e]
    simpa using h0
  have := HasSum.of_nat_of_neg_add_one (f := fun j : ℤ => 1 / (j : ℝ) ^ 2) h1 h2
  rw [show π ^ 2 / 3 = π ^ 2 / 6 + π ^ 2 / 6 by ring]
  exact this

end CoeffAux

open CoeffAux in
theorem coeffStatement_holds (hA : AnnulusStatement) : CoeffStatement := by
  intro ρ hρ T hT1 J l
  have hT0 : 0 < T := by linarith
  have hh : 0 < hT T := hT_pos hT0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hβc, hβe⟩ := id hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (psi_scaled_contDiff hρ _ _).mul (conv_contDiff hA hρ hh _)
  · intro x hx
    have hT2 : 0 < T ^ 2 := by positivity
    have : 1 ≤ |x / T ^ 2| := by
      rw [abs_div, abs_of_pos hT2, le_div_iff₀ hT2]; linarith
    simp [bL, psi_supp hρ _ this]
  · intro x
    unfold bL
    rw [neg_div, psi_even hρ]
    congr 1
    rw [← integral_neg_eq_self]
    congr 1; ext y
    rw [rhoH_even hρ, show -x - -y = -(x - y) by ring, hβe]
  · intro x
    unfold bL
    rw [fejerCoeff_neg, Int.cast_neg, neg_div]
    simp_rw [hβc]
    rw [map_mul, Complex.conj_ofReal, ← integral_conj]
    congr 1; congr 1; ext y
    rw [map_mul, Complex.conj_ofReal]
  · intro x
    rw [bL_zero_eq hA]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    have ha := aT_nonneg hρ T
    exact mul_nonneg (div_nonneg (psi_nonneg hρ _) (by positivity)) (Sm_nonneg hA hρ hh x)
  · intro hl
    funext x
    simp [bL, fejerCoeff_eq_zero J l hl]

open CoeffAux in
theorem coeffMassStatement_holds (hA : AnnulusStatement) : CoeffMassStatement := by
  intro ρ hρ
  have hρ0 := rho0_pos hρ
  -- `ψ ≥ 1/2` near `0`
  obtain ⟨δ, hδ, hψδ⟩ : ∃ δ > 0, ∀ u, |u| < δ → 1 / 2 ≤ psiF ρ u := by
    have hc : ContinuousAt (psiF ρ) 0 := (psi_contDiff hρ).continuous.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδ, hδ'⟩ := hc (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun u hu => ?_⟩
    have := hδ' (x := u) (by simpa [Real.dist_eq] using hu)
    rw [Real.dist_eq, psi_zero hρ] at this
    have := (abs_lt.mp this).1
    linarith
  -- `a → 0`
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, ∀ T ≥ T₁, aT ρ T ≤ 1 := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (8 * ρ 0)
    rw [mul_zero] at ht
    obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
      (ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
    refine ⟨T₁, fun T hT => ?_⟩
    have := hT₁ T hT
    unfold aT
    linarith [this, show 8 * ρ 0 * T ^ 2 * Real.exp (-T) = 8 * ρ 0 * (T ^ 2 * Real.exp (-T))
      by ring]
  refine ⟨9 + ρ 0 * π, Real.log 2 / 8, max (max 3 T₁) (1 / δ), by positivity, by positivity, ?_⟩
  intro T hTle J
  have hT3 : 3 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTle
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTle
  have hTδ : 1 / δ ≤ T := le_trans (le_max_right _ _) hTle
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hh : 0 < hT T := hT_pos hT0
  have hh2 : hT T ≤ 1 / 2 := by
    unfold hT
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨hsmooth, hsupp, -, -, hb0, -⟩ := coeffStatement_holds hA ρ hρ T hT1 J 0
  have ha0 := aT_nonneg hρ T
  set b : ℝ → ℝ := fun x => (bL ρ T J 0 x).re with hb
  have hbeq : ∀ x, b x = psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) * Sm ρ (hT T) x := by
    intro x; simp only [hb, bL_zero_eq hA, Complex.ofReal_re]
  have hbnn : ∀ x, 0 ≤ b x := fun x => (hb0 x).2
  have hble : ∀ x, b x ≤ Sm ρ (hT T) x / T := by
    intro x
    rw [hbeq]
    have hS := Sm_nonneg hA hρ hh x
    have : psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) ≤ 1 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      nlinarith [psi_le_one hρ (x / T ^ 2), psi_nonneg hρ (x / T ^ 2)]
    calc _ ≤ 1 / T * Sm ρ (hT T) x := mul_le_mul_of_nonneg_right this hS
      _ = Sm ρ (hT T) x / T := by ring
  -- comparison function on `ℤ`
  set A := (2 * Real.log T + ρ 0 * π) / T with hA_def
  set g : ℤ → ℝ := fun j => (2 / T) * (1 / (j : ℝ) ^ 2) + (if j = 0 then A else 0) with hg
  have hg_sum : HasSum g ((2 / T) * (π ^ 2 / 3) + A) :=
    (hasSum_int_inv_sq.mul_left (2 / T)).add (hasSum_ite_eq 0 A)
  have hbg : ∀ j : ℤ, b j ≤ g j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [hg, Int.cast_zero, ite_true]
      have := Sm_zero_le hA hρ hh (by linarith)
      calc b 0 ≤ Sm ρ (hT T) 0 / T := by simpa using hble 0
        _ ≤ (Real.log (hT T)⁻¹ + ρ 0 * π) / T := div_le_div_of_nonneg_right this hT0.le
        _ = 2 / T * (1 / 0 ^ 2) + A := by
          rw [hA_def]; unfold hT; rw [inv_inv, Real.log_pow]; push_cast; ring
    · have := Sm_int_le hA hρ hh hh2 j hj
      simp only [hg, hj, ite_false, add_zero]
      calc b j ≤ Sm ρ (hT T) j / T := hble j
        _ ≤ (2 / (j : ℝ) ^ 2) / T := div_le_div_of_nonneg_right this hT0.le
        _ = 2 / T * (1 / (j : ℝ) ^ 2) := by ring
  have hbsum : Summable (fun j : ℤ => b j) :=
    Summable.of_nonneg_of_le (fun j => hbnn j) hbg hg_sum.summable
  refine ⟨hbsum, ?_, ?_⟩
  · have hlog : 1 ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le hT0]
      have := Real.exp_one_lt_d9
      linarith
    have hpi : π < 3.15 := Real.pi_lt_d2
    have hpi0 : 0 < π := Real.pi_pos
    calc ∑' j : ℤ, b j ≤ ∑' j, g j := hbsum.tsum_le_tsum hbg hg_sum.summable
      _ = (2 / T) * (π ^ 2 / 3) + A := hg_sum.tsum_eq
      _ = (2 * π ^ 2 / 3 + 2 * Real.log T + ρ 0 * π) / T := by rw [hA_def]; ring
      _ ≤ (9 + ρ 0 * π) * Real.log T / T := by
        apply div_le_div_of_nonneg_right _ hT0.le
        have : ρ 0 * π ≤ ρ 0 * π * Real.log T := by
          have := mul_pos hρ0 hpi0
          nlinarith
        nlinarith
  · have hbcont : Continuous b := Complex.continuous_re.comp hsmooth.continuous
    have hbcs : HasCompactSupport b := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -T ^ 2) (b := T ^ 2)) (fun x hx => ?_)
      have hT2 : 0 < T ^ 2 := by positivity
      have : T ^ 2 < |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp [hb, hsupp x this]
    have hbint : Integrable b := hbcont.integrable_of_hasCompactSupport hbcs
    have hlow : ∀ x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Real.log 2 / 8 / T ≤ b x := by
      intro x hx
      have hx' : |x| ≤ 1 / 2 := abs_le.mpr hx
      rw [hbeq]
      have hψ : 1 / 2 ≤ psiF ρ (x / T ^ 2) := by
        apply hψδ
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < T ^ 2),
          div_lt_iff₀ (by positivity)]
        have : 1 ≤ δ * T := by rw [div_le_iff₀ hδ] at hTδ; linarith
        nlinarith
      have hS := Sm_ge hA hρ hh hh2 x hx'
      have ha1 := hT₁ T hTT₁
      have h1 : 1 / 2 / (2 * T) ≤ psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) :=
        div_le_div₀ (psi_nonneg hρ _) hψ (by positivity) (by nlinarith)
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc Real.log 2 / 8 / T = (1 / 2 / (2 * T)) * (Real.log 2 / 2) := by
            field_simp; ring
        _ ≤ _ := mul_le_mul h1 hS (by positivity)
            (div_nonneg (psi_nonneg hρ _) (by positivity))
    calc Real.log 2 / 8 / T
        = Real.log 2 / 8 / T * volume.real (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
          rw [Real.volume_real_Icc_of_le (by norm_num)]; ring
      _ ≤ ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), b x :=
          setIntegral_ge_of_const_le_real measurableSet_Icc (by simp) hlow hbint.integrableOn
      _ ≤ ∫ x, b x := setIntegral_le_integral hbint (ae_of_all _ hbnn)

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/W.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.WAux

open ChowlaOpus

variable {ρ : ℝ → ℝ}

lemma rho_integrable (hρ : IsBump ρ) : Integrable ρ :=
  Integrable.of_integral_ne_zero (by rw [hρ.integral_eq]; norm_num)

lemma hT_pos {T : ℝ} (hT1 : 1 ≤ T) : 0 < hT T := by unfold hT; positivity

lemma rhoH_eq {T : ℝ} (y : ℝ) : rhoH ρ (hT T) y = ρ (y * T ^ 2) * T ^ 2 := by
  unfold rhoH hT; simp [div_inv_eq_mul]

lemma rhoH_nonneg (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (y : ℝ) : 0 ≤ rhoH ρ (hT T) y := by
  unfold rhoH; exact div_nonneg (hρ.nonneg _) (hT_pos hT1).le

lemma rhoH_le (hρ : IsBump ρ) {T : ℝ} (y : ℝ) : rhoH ρ (hT T) y ≤ ρ 0 * T ^ 2 := by
  rw [rhoH_eq]; exact mul_le_mul_of_nonneg_right (hρ.le_at_zero _) (by positivity)

lemma rhoH_continuous (hρ : IsBump ρ) (T : ℝ) : Continuous (rhoH ρ (hT T)) := by
  unfold rhoH; exact (hρ.smooth.continuous.comp (continuous_id.div_const _)).div_const _

lemma rhoH_integrable (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) : Integrable (rhoH ρ (hT T)) := by
  unfold rhoH; exact ((rho_integrable hρ).comp_div (hT_pos hT1).ne').div_const _

lemma rhoH_integral (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) : ∫ y, rhoH ρ (hT T) y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div, hρ.integral_eq, abs_of_pos (hT_pos hT1)]
  simp [(hT_pos hT1).ne']

lemma ee_continuous : Continuous ee := by unfold ee; fun_prop

lemma fejer_abs_le (J : ℕ) (t : ℝ) : |fejer J t| ≤ (Finset.Icc (-(J : ℤ)) J).card := by
  unfold fejer
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul, abs_of_nonneg (fejerCoeff_nonneg _ _)]
  calc fejerCoeff J k * |Real.cos (2 * Real.pi * k * t)| ≤ 1 * 1 :=
        mul_le_mul (fejerCoeff_le_one J k) (abs_cos_le_one _) (abs_nonneg _) zero_le_one
    _ = ((1 : ℕ) : ℝ) := by norm_num

variable (ρ) in
/-- The integrand `(σ, y) ↦ ρ_h(y) B_σ(x - y)`. -/
noncomputable def G (T x : ℝ) (p : ℝ × ℝ) : ℝ := rhoH ρ (hT T) p.2 * annB p.1 (x - p.2)

lemma annB_measurable_snd (hA : AnnulusStatement) (σ : ℝ) : Measurable (annB σ) := by
  have h : Measurable (Function.uncurry annB) := hA.1
  have e : annB σ = Function.uncurry annB ∘ (fun y => (σ, y)) := rfl
  rw [e]; exact h.comp (measurable_const.prodMk measurable_id)

lemma G_measurable (hA : AnnulusStatement) (hρ : IsBump ρ) (T x : ℝ) :
    Measurable (G ρ T x) := by
  have h : Measurable (Function.uncurry annB) := hA.1
  have h1 : Measurable fun p : ℝ × ℝ => rhoH ρ (hT T) p.2 :=
    (rhoH_continuous hρ T).measurable.comp measurable_snd
  have e : (fun p : ℝ × ℝ => annB p.1 (x - p.2)) =
      Function.uncurry annB ∘ (fun p : ℝ × ℝ => (p.1, x - p.2)) := rfl
  have h2 : Measurable fun p : ℝ × ℝ => annB p.1 (x - p.2) := by
    rw [e]; exact h.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  exact h1.mul h2

lemma G_integrable (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (x : ℝ) :
    Integrable (G ρ T x) (volume.prod volume) := by
  rw [integrable_prod_iff' (G_measurable hA hρ T x).aestronglyMeasurable]
  constructor
  · filter_upwards [Measure.ae_ne volume x] with y hy
    have hi : Integrable (fun σ => annB σ (x - y)) :=
      hA.2.2.2.1 (x - y) (sub_ne_zero.mpr (Ne.symm hy))
    have e : (fun σ => G ρ T x (σ, y)) = fun σ => rhoH ρ (hT T) y * annB σ (x - y) := rfl
    rw [e]; exact hi.const_mul _
  · have : (fun y => ∫ σ, ‖G ρ T x (σ, y)‖) = fun y => rhoH ρ (hT T) y * ellF (x - y) := by
      ext y
      simp only [G, norm_mul, Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hT1 y),
        abs_of_nonneg (hA.2.1 _ _).1]
      rw [integral_const_mul]; rfl
    rw [this]
    refine (hA.2.2.2.2.2.2.2.1.comp_sub_left x).bdd_mul (c := ρ 0 * T ^ 2)
      (rhoH_continuous hρ T).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hT1 y)]
    exact rhoH_le hρ y

lemma smB_eq (T σ x : ℝ) : smB ρ T σ x = ∫ y, G ρ T x (σ, y) := rfl

lemma smB_integrable (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (x : ℝ) :
    Integrable (fun σ => smB ρ T σ x) :=
  (G_integrable hA hρ hT1 x).integral_prod_left

lemma smB_nonneg (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (σ x : ℝ) :
    0 ≤ smB ρ T σ x :=
  integral_nonneg fun y => mul_nonneg (rhoH_nonneg hρ hT1 y) (hA.2.1 _ _).1

lemma fubini_beta (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (x ξ : ℝ) :
    ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y) =
      ∫ σ, ee (-(ξ * σ)) * (smB ρ T σ x : ℂ) := by
  set F : ℝ → ℝ → ℂ := fun σ y => (G ρ T x (σ, y) : ℂ) * ee (-(ξ * σ)) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    have : Function.uncurry F = fun p : ℝ × ℝ => (G ρ T x p : ℂ) * ee (-(ξ * p.1)) := rfl
    rw [this]
    exact (Complex.measurable_ofReal.comp (G_measurable hA hρ T x)).mul
      ((ee_continuous.comp (continuous_fst.const_mul ξ).neg).measurable)
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (G_integrable hA hρ hT1 x).mono' hFm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have : Function.uncurry F p = (G ρ T x p : ℂ) * ee (-(ξ * p.1)) := rfl
    rw [this, norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (mul_nonneg (rhoH_nonneg hρ hT1 _) (hA.2.1 _ _).1))
  have hswap := integral_integral_swap hFi
  have hL : ∀ y, ∫ σ, F σ y = (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y) := by
    intro y
    unfold betaF
    rw [← integral_const_mul]
    congr 1; ext σ
    simp only [hFdef, G]; push_cast; ring
  have hR : ∀ σ, ∫ y, F σ y = ee (-(ξ * σ)) * (smB ρ T σ x : ℂ) := by
    intro σ
    simp only [hFdef]
    rw [integral_mul_const, integral_complex_ofReal, smB_eq, mul_comm]
  simp_rw [hL, hR] at hswap
  exact hswap.symm

lemma smB_measurable (hA : AnnulusStatement) (hρ : IsBump ρ) (T x : ℝ) :
    Measurable (fun σ => smB ρ T σ x) :=
  (G_measurable hA hρ T x).stronglyMeasurable.integral_prod_right'.measurable

lemma fejer_smB_integrable (hA : AnnulusStatement) (hF : FejerStatement) (hρ : IsBump ρ)
    {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) (s x : ℝ) :
    Integrable (fun σ => fejer J (s - σ / T) * smB ρ T σ x) := by
  refine (smB_integrable hA hρ hT1 x).bdd_mul (c := (Finset.Icc (-(J : ℤ)) J).card) ?_ ?_
  · exact ((hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))).aestronglyMeasurable
  · exact ae_of_all _ fun σ => fejer_abs_le J _

lemma lintegral_unfold {T : ℝ} (hT : 0 < T) (g : ℝ → ENNReal) :
    ∫⁻ σ, g σ = ∑' n : ℤ, ∫⁻ σ in Set.Ico 0 T, g (σ + n * T) := by
  have hU := iUnion_Ico_add_zsmul hT (0 : ℝ)
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion (fun n => measurableSet_Ico)
    (Set.pairwise_disjoint_Ico_add_zsmul (0 : ℝ) T)]
  congr 1; ext n
  rw [← lintegral_indicator measurableSet_Ico, ← lintegral_indicator measurableSet_Ico,
    ← lintegral_add_right_eq_self _ ((n : ℝ) * T)]
  congr 1; ext σ
  simp only [Set.indicator, Set.mem_Ico, zsmul_eq_mul, zero_add]
  push_cast
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; exact h2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
  · exfalso; exact h1 ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · rfl

lemma fejer_integral_Ico (hF : FejerStatement) {T : ℝ} (hT : 0 < T) (J : ℕ) (s : ℝ) :
    ∫ σ in Set.Ico 0 T, fejer J (s - σ / T) = T := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  have hper : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  rw [intervalIntegral.integral_comp_div (fun u => fejer J (s - u)) hT.ne',
    intervalIntegral.integral_comp_sub_left (fun u => fejer J u)]
  simp only [zero_div, div_self hT.ne', sub_zero, smul_eq_mul]
  have := hper.intervalIntegral_add_eq (s - 1) 0
  rw [sub_add_cancel, zero_add] at this
  rw [this, hF.2.2.2.2.1 J, mul_one]

lemma smB_periodized_le (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T)
    (σ x : ℝ) :
    ∑' n : ℤ, ENNReal.ofReal (smB ρ T (σ + n * T) x) ≤ ENNReal.ofReal (1 + aT ρ T) := by
  have hannm : ∀ τ, Measurable (fun y => annB τ (x - y)) := fun τ =>
    (annB_measurable_snd hA τ).comp (measurable_const.sub measurable_id)
  have hint : ∀ τ, Integrable (fun y => rhoH ρ (hT T) y * annB τ (x - y)) := fun τ =>
    (rhoH_integrable hρ hT1).mul_bdd (c := 1) (hannm τ).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA.2.1 _ _).1]; exact (hA.2.1 _ _).2)
  have hmeas : ∀ τ, Measurable (fun y => ENNReal.ofReal (rhoH ρ (hT T) y * annB τ (x - y))) :=
    fun τ => ENNReal.measurable_ofReal.comp ((rhoH_continuous hρ T).measurable.mul (hannm τ))
  have h1 : ∀ n : ℤ, ENNReal.ofReal (smB ρ T (σ + n * T) x) =
      ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y * annB (σ + n * T) (x - y)) := fun n =>
    ofReal_integral_eq_lintegral_ofReal (hint _)
      (ae_of_all _ fun y => mul_nonneg (rhoH_nonneg hρ hT1 y) (hA.2.1 _ _).1)
  simp_rw [h1]
  rw [← lintegral_tsum (fun n => (hmeas _).aemeasurable)]
  set m : ℝ → ℝ := fun z => max (perB T σ z - 1) 0 with hm
  have h2 : ∀ᵐ y ∂volume, ∑' n : ℤ, ENNReal.ofReal (rhoH ρ (hT T) y * annB (σ + n * T) (x - y))
      ≤ ENNReal.ofReal (rhoH ρ (hT T) y) +
        ENNReal.ofReal (ρ 0 * T ^ 2) * ENNReal.ofReal (m (x - y)) := by
    filter_upwards [Measure.ae_ne volume x] with y hy
    have hz : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    simp_rw [ENNReal.ofReal_mul (rhoH_nonneg hρ hT1 y)]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => (hA.2.1 _ _).1)
      (hA.2.2.2.2.2.2.2.2.2.2.2.2.1 T σ (x - y) hT1 hz)]
    have hP : perB T σ (x - y) ≤ 1 + m (x - y) := by
      simp only [hm]; linarith [le_max_left (perB T σ (x - y) - 1) 0]
    calc ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal (perB T σ (x - y))
        ≤ ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal (1 + m (x - y)) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hP) _
      _ = ENNReal.ofReal (rhoH ρ (hT T) y) +
          ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal (m (x - y)) := by
          rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one, mul_add,
            mul_one]
      _ ≤ ENNReal.ofReal (rhoH ρ (hT T) y) +
          ENNReal.ofReal (ρ 0 * T ^ 2) * ENNReal.ofReal (m (x - y)) := by
          gcongr
          exact rhoH_le hρ y
  refine (lintegral_mono_ae h2).trans ?_
  rw [lintegral_add_left (show Measurable (fun a => ENNReal.ofReal (rhoH ρ (hT T) a)) from
      ENNReal.measurable_ofReal.comp (rhoH_continuous hρ T).measurable),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (rhoH_integrable hρ hT1)
      (ae_of_all _ (rhoH_nonneg hρ hT1)), rhoH_integral hρ hT1,
    lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (m z)) x]
  obtain ⟨hmI, hm5⟩ := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.1 T σ hT1
  have hρ0 : 0 ≤ ρ 0 * T ^ 2 := mul_nonneg (hρ.nonneg 0) (sq_nonneg T)
  have hmI0 : 0 ≤ ∫ z, m z := integral_nonneg fun z => le_max_right _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hmI (ae_of_all _ fun z => le_max_right _ _),
    ← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add zero_le_one (mul_nonneg hρ0 hmI0)]
  apply ENNReal.ofReal_le_ofReal
  have h5 := mul_le_mul_of_nonneg_left hm5 hρ0
  have he : 0 ≤ ρ 0 * T ^ 2 * Real.exp (-T) := mul_nonneg hρ0 (Real.exp_pos _).le
  unfold aT
  nlinarith

lemma integral_fejer_smB_le (hA : AnnulusStatement) (hF : FejerStatement) (hρ : IsBump ρ)
    {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) (s x : ℝ) :
    ∫ σ, fejer J (s - σ / T) * smB ρ T σ x ≤ T * (1 + aT ρ T) := by
  have hT0 : 0 < T := by linarith
  have haT : 0 ≤ aT ρ T := by
    unfold aT; have := hρ.nonneg 0; positivity
  have hnn : ∀ σ, 0 ≤ fejer J (s - σ / T) * smB ρ T σ x := fun σ =>
    mul_nonneg (hF.2.1 _ _) (smB_nonneg hA hρ hT1 σ x)
  have hFc : Continuous (fun σ => fejer J (s - σ / T)) :=
    (hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn)
    (fejer_smB_integrable hA hF hρ hT1 J s x).aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  rw [lintegral_unfold hT0]
  have hper : ∀ σ (n : ℤ), fejer J (s - (σ + n * T) / T) = fejer J (s - σ / T) := by
    intro σ n
    rw [show s - (σ + n * T) / T = (s - σ / T) - n * 1 by field_simp; ring]
    exact (show Function.Periodic (fejer J) 1 from hF.2.2.1 J).sub_int_mul_eq n
  simp_rw [hper, ENNReal.ofReal_mul (hF.2.1 _ _)]
  rw [← lintegral_tsum (fun n : ℤ => (show Measurable (fun σ => ENNReal.ofReal (fejer J (s - σ / T)) *
      ENNReal.ofReal (smB ρ T (σ + (n : ℝ) * T) x)) from
    (ENNReal.measurable_ofReal.comp hFc.measurable).mul
    (ENNReal.measurable_ofReal.comp ((smB_measurable hA hρ T x).comp
      (measurable_id.add_const _)))).aemeasurable)]
  simp_rw [ENNReal.tsum_mul_left]
  calc ∫⁻ σ in Set.Ico 0 T, ENNReal.ofReal (fejer J (s - σ / T)) *
        ∑' n : ℤ, ENNReal.ofReal (smB ρ T (σ + n * T) x)
      ≤ ∫⁻ σ in Set.Ico 0 T, ENNReal.ofReal (fejer J (s - σ / T)) *
        ENNReal.ofReal (1 + aT ρ T) :=
        lintegral_mono fun σ => mul_le_mul_right (smB_periodized_le hA hρ hT1 σ x) _
    _ = ENNReal.ofReal (∫ σ in Set.Ico 0 T, fejer J (s - σ / T)) *
        ENNReal.ofReal (1 + aT ρ T) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal
            ((hFc.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
            (ae_of_all _ fun σ => hF.2.1 _ _)]
    _ = ENNReal.ofReal (T * (1 + aT ρ T)) := by
        rw [fejer_integral_Ico hF hT0, ← ENNReal.ofReal_mul hT0.le]

end ChowlaOpus.WAux

namespace ChowlaOpus

open WAux

theorem wrepStatement_holds (hA : AnnulusStatement) (hF : FejerStatement) :
    WrepStatement := by
  intro ρ hρ T hT1 J s x
  have hsmI := smB_integrable hA hρ hT1 x
  have hfejI : Integrable (fun σ => fejer J (s - σ / T) * smB ρ T σ x) := by
    refine hsmI.bdd_mul (c := (Finset.Icc (-(J : ℤ)) J).card) ?_ ?_
    · exact ((hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))).aestronglyMeasurable
    · exact ae_of_all _ fun σ => fejer_abs_le J _
  refine ⟨hfejI, ?_⟩
  unfold Wsum bL
  simp_rw [fubini_beta hA hρ hT1 x]
  have hfe := hF.2.2.2.2.2.1 J
  set K : ℝ := T * (1 + aT ρ T)
  set ψ : ℝ := psiF ρ (x / T ^ 2)
  have key : ∀ l ∈ Finset.Icc (-(J : ℤ)) J,
      ((fejerCoeff J l / K * ψ : ℝ) : ℂ) *
        (∫ σ, ee (-((l : ℝ) / T * σ)) * (smB ρ T σ x : ℂ)) * ee (l * s) =
      ((ψ / K : ℝ) : ℂ) *
        ∫ σ, ((fejerCoeff J l : ℂ) * ee (l * (s - σ / T))) * (smB ρ T σ x : ℂ) := by
    intro l _
    rw [← integral_const_mul, ← integral_mul_const, ← integral_const_mul]
    congr 1; ext σ
    rw [show (l : ℝ) * (s - σ / T) = l * s + (-((l : ℝ) / T * σ)) by ring, ee_add]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← integral_finsetSum]
  · simp_rw [← Finset.sum_mul, hfe]
    rw [show (fun σ => (fejer J (s - σ / T) : ℂ) * (smB ρ T σ x : ℂ)) =
      fun σ => ((fejer J (s - σ / T) * smB ρ T σ x : ℝ) : ℂ) by ext; push_cast; rfl]
    rw [integral_complex_ofReal]; push_cast; ring
  · intro l _
    refine (hsmI.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) ?_ (ae_of_all _ fun σ => ?_)
    · exact (continuous_const.mul (ee_continuous.comp
        (continuous_const.mul (continuous_const.sub (continuous_id.div_const T))))).aestronglyMeasurable
    · rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fejerCoeff_nonneg _ _)]
      exact fejerCoeff_le_one _ _

theorem wboundStatement_holds (hA : AnnulusStatement) (hF : FejerStatement) :
    WboundStatement := by
  intro ρ hρ T hT1 J s x
  obtain ⟨_, hW⟩ := wrepStatement_holds hA hF ρ hρ T hT1 J s x
  rw [hW, Complex.ofReal_im, Complex.ofReal_re]
  have hψ0 : 0 ≤ psiF ρ (x / T ^ 2) := div_nonneg (hρ.nonneg _) (hρ.nonneg 0)
  have hψ1 : psiF ρ (x / T ^ 2) ≤ 1 := div_le_one_of_le₀ (hρ.le_at_zero _) (hρ.nonneg 0)
  have haT : 0 ≤ aT ρ T := by
    unfold aT; have := hρ.nonneg 0; positivity
  have hK : 0 < T * (1 + aT ρ T) := by positivity
  have hI0 : 0 ≤ ∫ σ, fejer J (s - σ / T) * smB ρ T σ x :=
    integral_nonneg fun σ => mul_nonneg (hF.2.1 _ _) (smB_nonneg hA hρ hT1 σ x)
  have hI := integral_fejer_smB_le hA hF hρ hT1 J s x
  refine ⟨rfl, mul_nonneg (div_nonneg hψ0 hK.le) hI0, ?_⟩
  rw [div_mul_eq_mul_div, div_le_one hK]
  calc psiF ρ (x / T ^ 2) * ∫ σ, fejer J (s - σ / T) * smB ρ T σ x
      ≤ 1 * ∫ σ, fejer J (s - σ / T) * smB ρ T σ x := mul_le_mul_of_nonneg_right hψ1 hI0
    _ ≤ T * (1 + aT ρ T) := by rw [one_mul]; exact hI

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Q.lean. -/
section

open scoped FourierTransform ContDiff ComplexOrder
open Real MeasureTheory

namespace ChowlaOpus.QAux

open ChowlaOpus

/- ### Generalities -/

lemma cnonneg_iff {z : ℂ} : 0 ≤ z ↔ z.im = 0 ∧ 0 ≤ z.re :=
  ⟨fun h => ⟨(Complex.nonneg_iff.1 h).2.symm, (Complex.nonneg_iff.1 h).1⟩,
    fun h => Complex.nonneg_iff.2 ⟨h.2, h.1.symm⟩⟩

lemma integral_cnonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂μ := by
  have hfe : ∫ a, f a ∂μ = ∫ a, ((f a).re : ℂ) ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    apply Complex.ext
    · simp
    · simp [(cnonneg_iff.1 (hf a)).1]
  rw [hfe, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun a => (cnonneg_iff.1 (hf a)).2)

lemma continuous_ee : Continuous ee := by unfold ee; fun_prop

lemma ae_ne' (x : ℝ) : ∀ᵐ y : ℝ, y ≠ x := by
  rw [ae_iff]; simp

lemma le_abs_of_nmem {c x : ℝ} (hx : x ∉ Set.Icc (-c) c) : c ≤ |x| := by
  by_contra h
  push Not at h
  exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

lemma abs_one_sub_cos_le (u : ℝ) : |1 - cos u| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [cos_le_one u, neg_one_le_cos u]

lemma ofReal_cos_eq_ee (t : ℝ) : ((cos (2 * π * t) : ℝ) : ℂ) = (ee t + ee (-t)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  unfold ee
  congr 2
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring

/- ### The bump -/

section bump

variable {ρ : ℝ → ℝ} {T : ℝ}

lemma hT_pos (hT1 : 1 ≤ T) : 0 < hT T := by
  unfold ChowlaOpus.hT; have : 0 < T := by linarith
  positivity

lemma hT_le_one (hT1 : 1 ≤ T) : hT T ≤ 1 := by
  unfold ChowlaOpus.hT; apply inv_le_one_of_one_le₀; nlinarith

lemma rho_dil_zero (hρ : IsBump ρ) {c x : ℝ} (hc : 0 < c) (hx : c ≤ |x|) : ρ (x / c) = 0 := by
  apply hρ.supp
  rw [abs_div, abs_of_pos hc, le_div_iff₀ hc, one_mul]; exact hx

lemma rhoH_nonneg (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ rhoH ρ h y :=
  div_nonneg (hρ.nonneg _) hh.le

lemma rhoH_le (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : rhoH ρ h y ≤ ρ 0 / h :=
  div_le_div_of_nonneg_right (hρ.le_at_zero _) hh.le

lemma rhoH_eq_zero (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {y : ℝ} (hy : h ≤ |y|) :
    rhoH ρ h y = 0 := by
  unfold rhoH; rw [rho_dil_zero hρ hh hy, zero_div]

lemma rhoH_cont (hρ : IsBump ρ) {h : ℝ} : Continuous (rhoH ρ h) := by
  have := hρ.smooth.continuous
  unfold rhoH; fun_prop

lemma rhoH_hcs (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : HasCompactSupport (rhoH ρ h) :=
  HasCompactSupport.intro (isCompact_Icc (a := -h) (b := h))
    (fun _ hy => rhoH_eq_zero hρ hh (le_abs_of_nmem hy))

lemma rhoH_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : Integrable (rhoH ρ h) :=
  (rhoH_cont hρ).integrable_of_hasCompactSupport (rhoH_hcs hρ hh)

lemma rhoH_even (hρ : IsBump ρ) (h y : ℝ) : rhoH ρ h (-y) = rhoH ρ h y := by
  unfold rhoH; rw [neg_div, hρ.even]

lemma rhoH_integral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : ∫ y, rhoH ρ h y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div ρ h, hρ.integral_eq, abs_of_pos hh, smul_eq_mul,
    mul_one, div_self hh.ne']

lemma rhoH_mul_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun y => rhoH ρ h y * f y) :=
  ((rhoH_cont hρ).mul hf).integrable_of_hasCompactSupport (rhoH_hcs hρ hh).mul_right

lemma psi_zero (hρ : IsBump ρ) (hT1 : 1 ≤ T) {x : ℝ} (hx : T ^ 2 ≤ |x|) :
    psiF ρ (x / T ^ 2) = 0 := by
  have : 0 < T ^ 2 := by have : 0 < T := by linarith
                         positivity
  unfold psiF; rw [rho_dil_zero hρ this hx, zero_div]

lemma psiF_meas (hρ : IsBump ρ) : Measurable (psiF ρ) := by
  have := hρ.smooth.continuous
  exact (by unfold psiF; fun_prop : Continuous (psiF ρ)).measurable

lemma psi_cont (hρ : IsBump ρ) : Continuous (fun x => psiF ρ (x / T ^ 2)) := by
  have := hρ.smooth.continuous
  unfold psiF; fun_prop

lemma psi_hcs (hρ : IsBump ρ) (hT1 : 1 ≤ T) : HasCompactSupport (fun x => psiF ρ (x / T ^ 2)) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(T ^ 2)) (b := T ^ 2))
    (fun _ hx => psi_zero hρ hT1 (le_abs_of_nmem hx))

lemma psi_integrable (hρ : IsBump ρ) (hT1 : 1 ≤ T) : Integrable (fun x => psiF ρ (x / T ^ 2)) :=
  (psi_cont hρ).integrable_of_hasCompactSupport (psi_hcs hρ hT1)

lemma rho_dil_hcs (hρ : IsBump ρ) {c : ℝ} (hc : 0 < c) :
    HasCompactSupport (fun x => (ρ (x / c) : ℂ)) :=
  HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c))
    (fun _ hx => by rw [rho_dil_zero hρ hc (le_abs_of_nmem hx), Complex.ofReal_zero])

lemma ee_rho_dil_integrable (hρ : IsBump ρ) {c : ℝ} (hc : 0 < c) (η : ℝ) :
    Integrable (fun x => ee (-(x * η)) * (ρ (x / c) : ℂ)) := by
  have := hρ.smooth.continuous
  have hee := continuous_ee
  exact (by fun_prop : Continuous (fun x => ee (-(x * η)) * (ρ (x / c) : ℂ))).integrable_of_hasCompactSupport
    (rho_dil_hcs hρ hc).mul_left

lemma FT_rho_nonneg (hρ : IsBump ρ) (η : ℝ) : 0 ≤ 𝓕 (fun u => (ρ u : ℂ)) η :=
  cnonneg_iff.2 ⟨hρ.fourier_im η, hρ.fourier_nonneg η⟩

/-- Fourier transform of a dilate. -/
lemma FT_dil {c : ℝ} (hc : 0 < c) (η : ℝ) :
    ∫ x, ee (-(x * η)) * (ρ (x / c) : ℂ) = (c : ℂ) * 𝓕 (fun u => (ρ u : ℂ)) (c * η) := by
  rw [fourier_eq_ee]
  have := Measure.integral_comp_div (fun u => ee (-(u * (c * η))) * (ρ u : ℂ)) c
  rw [abs_of_pos hc, Complex.real_smul] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [show x / c * (c * η) = x * η by field_simp]

/- ### The cosine transform `Rr` of `ρ_h` -/

/-- `R(om) = ∫ ρ_h(y) cos(omy) dy`. -/
noncomputable def Rr (ρ : ℝ → ℝ) (T om : ℝ) : ℝ := ∫ y, rhoH ρ (hT T) y * cos (om * y)

lemma Rr_eq (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om : ℝ) :
    Rr ρ T om = (𝓕 (fun u => (ρ u : ℂ)) (hT T * (om / (2 * π)))).re := by
  have hh := hT_pos hT1
  have hπ : (2 * π) ≠ 0 := by positivity
  have hint := ee_rho_dil_integrable hρ hh (om / (2 * π))
  have key := FT_dil (ρ := ρ) hh (om / (2 * π))
  have hre := integral_re hint
  rw [key] at hre
  have e : ∀ x, RCLike.re (ee (-(x * (om / (2 * π)))) * (ρ (x / hT T) : ℂ)) =
      ρ (x / hT T) * cos (om * x) := by
    intro x
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, ee_re]
    rw [show 2 * π * -(x * (om / (2 * π))) = -(x * (2 * π * (om / (2 * π)))) by ring,
      mul_div_cancel₀ om hπ, cos_neg, mul_comm x om, mul_comm]
  simp_rw [e] at hre
  unfold Rr rhoH
  have e2 : ∫ y, ρ (y / hT T) / hT T * cos (om * y) = (∫ y, ρ (y / hT T) * cos (om * y)) / hT T := by
    rw [← integral_div]; congr 1; ext y; ring
  rw [e2, hre]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  exact mul_div_cancel_left₀ _ hh.ne'

lemma Rr_nonneg (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om : ℝ) : 0 ≤ Rr ρ T om := by
  rw [Rr_eq hρ hT1]; exact hρ.fourier_nonneg _

lemma Rr_abs_le (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om : ℝ) : |Rr ρ T om| ≤ 1 := by
  have hh := hT_pos hT1
  unfold Rr
  calc |∫ y, rhoH ρ (hT T) y * cos (om * y)| ≤ ∫ y, |rhoH ρ (hT T) y * cos (om * y)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, rhoH ρ (hT T) y := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
          (rhoH_integrable hρ hh) (ae_of_all _ fun y => ?_)
        show |rhoH ρ (hT T) y * cos (om * y)| ≤ rhoH ρ (hT T) y
        rw [abs_mul, abs_of_nonneg (rhoH_nonneg hρ hh y)]
        exact mul_le_of_le_one_right (rhoH_nonneg hρ hh y) (abs_cos_le_one _)
    _ = 1 := rhoH_integral hρ hh

lemma Rr_meas (hρ : IsBump ρ) : Measurable (Rr ρ T) := by
  have hc := rhoH_cont hρ (h := hT T)
  have hcont : Continuous (fun p : ℝ × ℝ => rhoH ρ (hT T) p.2 * cos (p.1 * p.2)) := by fun_prop
  exact (hcont.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma Sr_zero (hρ : IsBump ρ) (h om : ℝ) : ∫ y, rhoH ρ h y * sin (om * y) = 0 := by
  have h1 := integral_neg_eq_self (fun y => rhoH ρ h y * sin (om * y)) volume
  have e : ∀ y, rhoH ρ h (-y) * sin (om * -y) = -(rhoH ρ h y * sin (om * y)) := by
    intro y; rw [rhoH_even hρ, mul_neg, sin_neg]; ring
  simp only [e, integral_neg] at h1
  linarith

/- ### Plane-wave formula for `smG` -/

lemma inner_eq (hρ : IsBump ρ) (hT1 : 1 ≤ T) (a θ x : ℝ) :
    ∫ y, rhoH ρ (hT T) y * ((1 - cos (a * sin θ)) * cos (a * (x - y) * cos θ)) =
      (1 - cos (a * sin θ)) * Rr ρ T (a * cos θ) * cos (a * cos θ * x) := by
  have hh := hT_pos hT1
  have e : ∀ y, rhoH ρ (hT T) y * ((1 - cos (a * sin θ)) * cos (a * (x - y) * cos θ)) =
      ((1 - cos (a * sin θ)) * cos (a * cos θ * x)) * (rhoH ρ (hT T) y * cos (a * cos θ * y)) +
      ((1 - cos (a * sin θ)) * sin (a * cos θ * x)) * (rhoH ρ (hT T) y * sin (a * cos θ * y)) := by
    intro y
    rw [show a * (x - y) * cos θ = a * cos θ * x - a * cos θ * y by ring, cos_sub]; ring
  simp_rw [e]
  rw [integral_add ((rhoH_mul_integrable hρ hh (by fun_prop)).const_mul _)
      ((rhoH_mul_integrable hρ hh (by fun_prop)).const_mul _), integral_const_mul,
    integral_const_mul, Sr_zero hρ]
  unfold Rr; ring

lemma plane_wave (hB : BesselPlaneStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) (σ x : ℝ) :
    smG ρ T σ x = (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π),
      (1 - cos (exp (-σ) * sin θ)) * Rr ρ T (exp (-σ) * cos θ) * cos (exp (-σ) * cos θ * x) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hh := hT_pos hT1
  let G2 : ℝ → ℝ → ℝ := fun y θ =>
    rhoH ρ (hT T) y * ((1 - cos (exp (-σ) * sin θ)) * cos (exp (-σ) * (x - y) * cos θ))
  have hG2 : Integrable (Function.uncurry G2)
      (volume.prod (volume.restrict (Set.Ioc 0 (2 * π)))) := by
    refine Integrable.mono' ((rhoH_integrable hρ hh).mul_prod (integrable_const (2 : ℝ))) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have := rhoH_cont hρ (h := hT T)
      show Continuous (fun p : ℝ × ℝ => rhoH ρ (hT T) p.1 *
        ((1 - cos (exp (-σ) * sin p.2)) * cos (exp (-σ) * (x - p.1) * cos p.2)))
      fun_prop
    · filter_upwards with p
      simp only [Function.uncurry, G2, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (rhoH_nonneg hρ hh _)]
      apply mul_le_mul_of_nonneg_left _ (rhoH_nonneg hρ hh _)
      have h1 := abs_one_sub_cos_le (exp (-σ) * sin p.2)
      have h2 := abs_cos_le_one (exp (-σ) * (x - p.1) * cos p.2)
      calc |1 - cos (exp (-σ) * sin p.2)| * |cos (exp (-σ) * (x - p.1) * cos p.2)| ≤ 2 * 1 := by
            gcongr
        _ = 2 := by ring
  unfold smG
  simp_rw [hB σ, intervalIntegral.integral_of_le h2π]
  calc ∫ y, rhoH ρ (hT T) y * (1 / (2 * π) * ∫ θ in Set.Ioc 0 (2 * π),
          (1 - cos (exp (-σ) * sin θ)) * cos (exp (-σ) * (x - y) * cos θ))
      = ∫ y, 1 / (2 * π) * ∫ θ in Set.Ioc 0 (2 * π), G2 y θ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [G2]
        rw [integral_const_mul]; ring
    _ = 1 / (2 * π) * ∫ θ in Set.Ioc 0 (2 * π), ∫ y, G2 y θ := by
        rw [integral_const_mul, integral_integral_swap hG2]
    _ = _ := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun θ => ?_)
        simp only [G2]
        exact inner_eq hρ hT1 _ θ x

/- ### Fourier transform of a modulated dilate of `ψ` -/

/-- `P(om, y) = ∫ ψ(x/X) cos(omx) e(-xy) dx`. -/
noncomputable def Pm (ρ : ℝ → ℝ) (T om y : ℝ) : ℂ :=
  ∫ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * cos (om * x) : ℝ) : ℂ)

lemma Pm_eq (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om y : ℝ) :
    Pm ρ T om y = (((ρ 0)⁻¹ / 2 * T ^ 2 : ℝ) : ℂ) *
      (𝓕 (fun u => (ρ u : ℂ)) (T ^ 2 * (y - om / (2 * π))) +
        𝓕 (fun u => (ρ u : ℂ)) (T ^ 2 * (y + om / (2 * π)))) := by
  have hX : 0 < T ^ 2 := by have : 0 < T := by linarith
                            positivity
  have hπ : (2 * π) ≠ 0 := by positivity
  have e : ∀ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * cos (om * x) : ℝ) : ℂ) =
      (((ρ 0)⁻¹ / 2 : ℝ) : ℂ) * (ee (-(x * (y - om / (2 * π)))) * (ρ (x / T ^ 2) : ℂ) +
        ee (-(x * (y + om / (2 * π)))) * (ρ (x / T ^ 2) : ℂ)) := by
    intro x
    have hc : cos (om * x) = cos (2 * π * (x * (om / (2 * π)))) := by
      congr 1
      rw [show 2 * π * (x * (om / (2 * π))) = x * (2 * π * (om / (2 * π))) by ring,
        mul_div_cancel₀ om hπ, mul_comm]
    have e1 : ee (-(x * (y - om / (2 * π)))) = ee (-(x * y)) * ee (x * (om / (2 * π))) := by
      rw [← ee_add]; congr 1; ring
    have e2 : ee (-(x * (y + om / (2 * π)))) = ee (-(x * y)) * ee (-(x * (om / (2 * π)))) := by
      rw [← ee_add]; congr 1; ring
    rw [hc, Complex.ofReal_mul, ofReal_cos_eq_ee, e1, e2]
    unfold psiF; push_cast; ring
  unfold Pm
  simp_rw [e]
  rw [integral_const_mul, integral_add (ee_rho_dil_integrable hρ hX _)
    (ee_rho_dil_integrable hρ hX _), FT_dil hX, FT_dil hX]
  push_cast; ring

lemma Pm_nonneg (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om y : ℝ) : 0 ≤ Pm ρ T om y := by
  rw [Pm_eq hρ hT1]
  refine mul_nonneg (Complex.zero_le_real.2 ?_) (add_nonneg (FT_rho_nonneg hρ _) (FT_rho_nonneg hρ _))
  exact mul_nonneg (div_nonneg (inv_nonneg.2 (hρ.nonneg 0)) two_pos.le) (sq_nonneg T)

/- ### Positivity of the Fourier transform of a single label -/

/-- `Φ(σ, y) = 𝓕[x ↦ ψ(x/X) (ρ_h ∗ G_σ)(x)](y)`. -/
noncomputable def Phi (ρ : ℝ → ℝ) (T σ y : ℝ) : ℂ :=
  ∫ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * smG ρ T σ x : ℝ) : ℂ)

lemma Phi_eq (hB : BesselPlaneStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) (σ y : ℝ) :
    Phi ρ T σ y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
      (((1 - cos (exp (-σ) * sin θ)) * Rr ρ T (exp (-σ) * cos θ) : ℝ) : ℂ) *
        Pm ρ T (exp (-σ) * cos θ) y := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  let H : ℝ → ℝ → ℂ := fun x θ => ee (-(x * y)) * ((psiF ρ (x / T ^ 2) *
    ((1 - cos (exp (-σ) * sin θ)) * Rr ρ T (exp (-σ) * cos θ) * cos (exp (-σ) * cos θ * x)) : ℝ) : ℂ)
  have hH : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Set.Ioc 0 (2 * π)))) := by
    refine Integrable.mono' ((psi_integrable hρ hT1).abs.mul_prod (integrable_const (2 : ℝ))) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      have hR := Rr_meas hρ (T := T)
      have hee : Measurable ee := continuous_ee.measurable
      have hψ : Measurable (psiF ρ) := psiF_meas hρ
      show Measurable (fun p : ℝ × ℝ => ee (-(p.1 * y)) * ((psiF ρ (p.1 / T ^ 2) *
        ((1 - cos (exp (-σ) * sin p.2)) * Rr ρ T (exp (-σ) * cos p.2) *
          cos (exp (-σ) * cos p.2 * p.1)) : ℝ) : ℂ))
      fun_prop
    · filter_upwards with p
      simp only [Function.uncurry, H, norm_mul, norm_ee, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h1 := abs_one_sub_cos_le (exp (-σ) * sin p.2)
      have h2 := Rr_abs_le hρ hT1 (exp (-σ) * cos p.2)
      have h3 := abs_cos_le_one (exp (-σ) * cos p.2 * p.1)
      calc |1 - cos (exp (-σ) * sin p.2)| * |Rr ρ T (exp (-σ) * cos p.2)| *
            |cos (exp (-σ) * cos p.2 * p.1)| ≤ 2 * 1 * 1 := by gcongr
        _ = 2 := by ring
  have step1 : ∀ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * smG ρ T σ x : ℝ) : ℂ) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ θ in Set.Ioc 0 (2 * π), H x θ := by
    intro x
    rw [plane_wave hB hρ hT1 σ x, intervalIntegral.integral_of_le h2π]
    simp only [H]
    rw [integral_const_mul, integral_complex_ofReal, integral_const_mul]
    push_cast; ring
  unfold Phi
  rw [intervalIntegral.integral_of_le h2π]
  simp_rw [step1]
  rw [integral_const_mul, integral_integral_swap hH]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [H]
  unfold Pm
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  push_cast; ring

lemma Phi_nonneg (hB : BesselPlaneStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) (σ y : ℝ) :
    0 ≤ Phi ρ T σ y := by
  rw [Phi_eq hB hρ hT1 σ y]
  refine mul_nonneg (Complex.zero_le_real.2 (by positivity)) ?_
  rw [intervalIntegral.integral_of_le (by positivity)]
  refine integral_cnonneg fun θ => mul_nonneg (Complex.zero_le_real.2 ?_) (Pm_nonneg hρ hT1 _ y)
  exact mul_nonneg (by linarith [cos_le_one (exp (-σ) * sin θ)]) (Rr_nonneg hρ hT1 _)

end bump

/- ### Bounds for the Bessel profile -/

/-- The locally integrable majorant `k(z) = 1 + |z|^{-1/2}`. -/
noncomputable def kq (z : ℝ) : ℝ := 1 + 1 / Real.sqrt |z|

lemma kq_ge_one (z : ℝ) : 1 ≤ kq z := by
  unfold kq; have : 0 ≤ 1 / √|z| := by positivity
  linarith

lemma kq_meas : Measurable kq := by
  unfold kq; fun_prop

lemma inv_sqrt_abs_intervalIntegrable {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun z : ℝ => 1 / √|z|) volume (-R) R := by
  have hpos : IntervalIntegrable (fun z : ℝ => 1 / √|z|) volume 0 R := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (r := -(1 / 2))
      (by norm_num)
    refine IntervalIntegrable.congr ?_ this
    intro z hz
    rw [Set.uIoc_of_le hR] at hz
    simp only
    rw [abs_of_pos hz.1, Real.rpow_neg hz.1.le, ← Real.sqrt_eq_rpow, one_div]
  have hneg : IntervalIntegrable (fun z : ℝ => 1 / √|z|) volume (-R) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa [abs_neg] using hpos.symm
  exact hneg.trans hpos

lemma kq_integrableOn {R : ℝ} (hR : 0 ≤ R) : IntegrableOn kq (Set.Icc (-R) R) := by
  have h1 : IntegrableOn (fun z : ℝ => 1 / √|z|) (Set.Icc (-R) R) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1
      (inv_sqrt_abs_intervalIntegrable hR)
  have h0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-R) R) :=
    continuous_const.integrableOn_Icc
  exact h0.add h1

lemma G_unif (hB : BesselPlaneStatement) (σ z : ℝ) : |besselG σ z| ≤ exp (-σ) ^ 2 / 2 := by
  rw [hB σ z, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  have hb : ‖∫ θ in (0 : ℝ)..(2 * π), (1 - cos (exp (-σ) * sin θ)) *
      cos (exp (-σ) * z * cos θ)‖ ≤ exp (-σ) ^ 2 / 2 * |2 * π - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ _
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : 0 ≤ 1 - cos (exp (-σ) * sin θ) := by linarith [cos_le_one (exp (-σ) * sin θ)]
    have h2 : 1 - cos (exp (-σ) * sin θ) ≤ (exp (-σ) * sin θ) ^ 2 / 2 := by
      linarith [one_sub_sq_div_two_le_cos (x := exp (-σ) * sin θ)]
    have h3 : (exp (-σ) * sin θ) ^ 2 ≤ exp (-σ) ^ 2 := by
      rw [mul_pow]; exact mul_le_of_le_one_right (by positivity) (sin_sq_le_one θ)
    rw [abs_of_nonneg h1]
    calc (1 - cos (exp (-σ) * sin θ)) * |cos (exp (-σ) * z * cos θ)|
        ≤ (1 - cos (exp (-σ) * sin θ)) * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one _) h1
      _ ≤ exp (-σ) ^ 2 / 2 := by linarith
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hb
  calc 1 / (2 * π) * |∫ θ in (0 : ℝ)..(2 * π), (1 - cos (exp (-σ) * sin θ)) *
        cos (exp (-σ) * z * cos θ)| ≤ 1 / (2 * π) * (exp (-σ) ^ 2 / 2 * (2 * π)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = exp (-σ) ^ 2 / 2 := by field_simp

lemma G_decay (hJ : J0Statement) : ∃ C : ℝ, 0 < C ∧ ∀ σ z : ℝ, z ≠ 0 →
    |besselG σ z| ≤ C * exp (σ / 2) * kq z := by
  obtain ⟨C, hC, hdec⟩ := hJ.2.2.2.2.2.1
  refine ⟨C, hC, fun σ z hz => ?_⟩
  have hs : √(exp (-σ)) = exp (-(σ / 2)) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (exp_pos _).le (exp_pos _).le, ← Real.exp_add]; ring_nf
  have hz' : 0 < |z| := abs_pos.2 hz
  have h1 : |J0 (exp (-σ) * |z|)| ≤ C * exp (σ / 2) * (1 / √|z|) := by
    have := hdec (exp (-σ) * |z|) (by positivity)
    rw [Real.sqrt_mul (exp_pos _).le, hs] at this
    calc _ ≤ C / (exp (-(σ / 2)) * √|z|) := this
      _ = C * exp (σ / 2) * (1 / √|z|) := by rw [Real.exp_neg]; field_simp
  have hq : 1 ≤ √(1 + z ^ 2) := Real.one_le_sqrt.2 (by nlinarith)
  have h2 : |J0 (exp (-σ) * √(1 + z ^ 2))| ≤ C * exp (σ / 2) := by
    have := hdec (exp (-σ) * √(1 + z ^ 2)) (by positivity)
    rw [Real.sqrt_mul (exp_pos _).le, hs] at this
    calc _ ≤ C / (exp (-(σ / 2)) * √(√(1 + z ^ 2))) := this
      _ ≤ C / (exp (-(σ / 2)) * 1) := by
          apply div_le_div_of_nonneg_left hC.le (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.one_le_sqrt.2 hq) (exp_pos _).le
      _ = C * exp (σ / 2) := by rw [mul_one, Real.exp_neg]; field_simp
  unfold besselG kq
  calc |J0 (exp (-σ) * |z|) - J0 (exp (-σ) * √(1 + z ^ 2))|
      ≤ |J0 (exp (-σ) * |z|)| + |J0 (exp (-σ) * √(1 + z ^ 2))| := abs_sub _ _
    _ ≤ C * exp (σ / 2) * (1 / √|z|) + C * exp (σ / 2) := add_le_add h1 h2
    _ = C * exp (σ / 2) * (1 + 1 / √|z|) := by ring

lemma exp_half_le {σ : ℝ} (hσ : σ ≤ 0) : exp (σ / 2) ≤ 8 * (1 + σ ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (x := -σ / 2) (by linarith)
  have hprod : exp (σ / 2) * exp (-σ / 2) = 1 := by
    rw [← Real.exp_add, show σ / 2 + -σ / 2 = 0 by ring, Real.exp_zero]
  have hpos : 0 < exp (σ / 2) := exp_pos _
  have key : exp (σ / 2) * (1 + σ ^ 2) ≤ 8 := by nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; exact key

lemma exp_two_le {σ : ℝ} (hσ : 0 ≤ σ) : exp (-σ) ^ 2 ≤ (1 + σ ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 2 * σ) (by linarith)
  have hprod : exp (-σ) ^ 2 * exp (2 * σ) = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, show -σ + -σ + 2 * σ = 0 by ring, Real.exp_zero]
  have h1 : 1 + σ ^ 2 ≤ exp (2 * σ) := by nlinarith
  rw [← one_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (exp (-σ)))]

lemma G_bound (hJ : J0Statement) (hB : BesselPlaneStatement) : ∃ Cg : ℝ, 0 < Cg ∧
    ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹) := by
  obtain ⟨C, hC, hdec⟩ := G_decay hJ
  refine ⟨8 * C + 1, by positivity, fun σ z hz => ?_⟩
  have hk := kq_ge_one z
  have hw : 0 ≤ (1 + σ ^ 2)⁻¹ := by positivity
  have hkw : 0 ≤ kq z * (1 + σ ^ 2)⁻¹ := mul_nonneg (by linarith) hw
  rcases le_total σ 0 with hσ | hσ
  · calc |besselG σ z| ≤ C * exp (σ / 2) * kq z := hdec σ z hz
      _ ≤ C * (8 * (1 + σ ^ 2)⁻¹) * kq z := by
          gcongr; exact exp_half_le hσ
      _ ≤ kq z * ((8 * C + 1) * (1 + σ ^ 2)⁻¹) := by linarith
  · calc |besselG σ z| ≤ exp (-σ) ^ 2 / 2 := G_unif hB σ z
      _ ≤ (1 + σ ^ 2)⁻¹ := by linarith [exp_two_le hσ, sq_nonneg (exp (-σ))]
      _ = 1 * (1 * (1 + σ ^ 2)⁻¹) := by ring
      _ ≤ kq z * ((8 * C + 1) * (1 + σ ^ 2)⁻¹) := by
          gcongr; linarith

/- ### Step 2: bounds for the smoothed profile -/

section steps

variable {ρ : ℝ → ℝ} {T : ℝ}

lemma conv_bound_pt (hρ : IsBump ρ) (hT1 : 1 ≤ T) {x R : ℝ} (hx : |x| ≤ R) (y : ℝ) :
    rhoH ρ (hT T) y * kq (x - y) ≤
      (ρ 0 / hT T) * Set.indicator (Set.Icc (-(R + 1)) (R + 1)) kq (x - y) := by
  have hh := hT_pos hT1
  have hh1 := hT_le_one hT1
  have hk := kq_ge_one (x - y)
  by_cases hy : |y| < hT T
  · have hmem : x - y ∈ Set.Icc (-(R + 1)) (R + 1) := by
      rw [Set.mem_Icc, ← abs_le]
      calc |x - y| ≤ |x| + |y| := abs_sub _ _
        _ ≤ R + 1 := by linarith
    rw [Set.indicator_of_mem hmem]
    exact mul_le_mul_of_nonneg_right (rhoH_le hρ hh y) (by linarith)
  · push Not at hy
    rw [rhoH_eq_zero hρ hh hy, zero_mul]
    apply mul_nonneg (div_nonneg (hρ.nonneg 0) hh.le)
    exact Set.indicator_nonneg (fun z _ => by linarith [kq_ge_one z]) _

lemma dom_integrable (T ρ0 R x : ℝ) (hR : 0 ≤ R) :
    Integrable (fun y => (ρ0 / hT T) * Set.indicator (Set.Icc (-(R + 1)) (R + 1)) kq (x - y)) :=
  (((kq_integrableOn (by linarith : (0 : ℝ) ≤ R + 1)).integrable_indicator
    measurableSet_Icc).comp_sub_left x).const_mul _

lemma conv_integrable (hρ : IsBump ρ) (hT1 : 1 ≤ T) (x : ℝ) :
    Integrable (fun y => rhoH ρ (hT T) y * kq (x - y)) := by
  have hh := hT_pos hT1
  refine Integrable.mono' (dom_integrable T (ρ 0) |x| x (abs_nonneg x)) ?_ ?_
  · exact ((rhoH_cont hρ).measurable.mul
      (kq_meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rhoH_nonneg hρ hh y)
      (by linarith [kq_ge_one (x - y)]))]
    exact conv_bound_pt hρ hT1 le_rfl y

/-- The uniform constant bounding `∫ ρ_h(y) k(x - y) dy` for `|x| ≤ T²`. -/
noncomputable def Kx (ρ : ℝ → ℝ) (T : ℝ) : ℝ :=
  (ρ 0 / hT T) * ∫ z in Set.Icc (-(T ^ 2 + 1)) (T ^ 2 + 1), kq z

lemma conv_le (hρ : IsBump ρ) (hT1 : 1 ≤ T) {x : ℝ} (hx : |x| ≤ T ^ 2) :
    ∫ y, rhoH ρ (hT T) y * kq (x - y) ≤ Kx ρ T := by
  calc ∫ y, rhoH ρ (hT T) y * kq (x - y)
      ≤ ∫ y, (ρ 0 / hT T) * Set.indicator (Set.Icc (-(T ^ 2 + 1)) (T ^ 2 + 1)) kq (x - y) :=
        integral_mono (conv_integrable hρ hT1 x) (dom_integrable T (ρ 0) _ x (sq_nonneg T))
          (fun y => conv_bound_pt hρ hT1 hx y)
    _ = Kx ρ T := by
        rw [integral_const_mul, integral_sub_left_eq_self
          (fun z => Set.indicator (Set.Icc (-(T ^ 2 + 1)) (T ^ 2 + 1)) kq z) volume x,
          integral_indicator measurableSet_Icc]
        rfl

lemma smG_bound (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ} (hCg : 0 < Cg)
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹))
    (σ : ℝ) {x : ℝ} (hx : |x| ≤ T ^ 2) :
    |smG ρ T σ x| ≤ Kx ρ T * (Cg * (1 + σ ^ 2)⁻¹) := by
  have hh := hT_pos hT1
  unfold smG
  calc |∫ y, rhoH ρ (hT T) y * besselG σ (x - y)|
      ≤ ∫ y, |rhoH ρ (hT T) y * besselG σ (x - y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, rhoH ρ (hT T) y * kq (x - y) * (Cg * (1 + σ ^ 2)⁻¹) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
          ((conv_integrable hρ hT1 x).mul_const _) ?_
        filter_upwards [ae_ne' x] with y hy
        rw [abs_mul, abs_of_nonneg (rhoH_nonneg hρ hh y), mul_assoc]
        exact mul_le_mul_of_nonneg_left (hG σ (x - y) (sub_ne_zero.2 (Ne.symm hy)))
          (rhoH_nonneg hρ hh y)
    _ = (∫ y, rhoH ρ (hT T) y * kq (x - y)) * (Cg * (1 + σ ^ 2)⁻¹) := integral_mul_const _ _
    _ ≤ Kx ρ T * (Cg * (1 + σ ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right (conv_le hρ hT1 hx) (by positivity)

lemma smG_sm (hJ : J0Statement) (hρ : IsBump ρ) :
    StronglyMeasurable (fun p : ℝ × ℝ => smG ρ T p.2 p.1) := by
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ => rhoH ρ (hT T) q.2 * besselG q.1.2 (q.1.1 - q.2)) := by
    have := hρ.smooth.continuous
    have := hJ.1
    simp only [rhoH, besselG]
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

/- ### Step 3: label representation -/

lemma step3 (hJ : J0Statement) (hMe : MellinStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ}
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹)) (ξ x : ℝ) :
    mult (2 * π * ξ) * ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y) =
      ∫ σ, ee (-(ξ * σ)) * (smG ρ T σ x : ℂ) := by
  have hh := hT_pos hT1
  have hint : Integrable (Function.uncurry fun (y σ : ℝ) =>
      (rhoH ρ (hT T) y : ℂ) * ((besselG σ (x - y) : ℂ) * ee (-(ξ * σ))))
      (volume.prod volume) := by
    refine Integrable.mono' ((conv_integrable hρ hT1 x).mul_prod
      (integrable_inv_one_add_sq.const_mul Cg)) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have := hρ.smooth.continuous
      have := hJ.1
      have := continuous_ee
      show Continuous (fun p : ℝ × ℝ =>
        (rhoH ρ (hT T) p.1 : ℂ) * ((besselG p.2 (x - p.1) : ℂ) * ee (-(ξ * p.2))))
      simp only [rhoH, besselG]
      fun_prop
    · have hae : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), p.1 ≠ x := by
        rw [ae_iff]
        have : {p : ℝ × ℝ | ¬p.1 ≠ x} = {x} ×ˢ Set.univ := by
          ext p; simp
        rw [this, Measure.prod_prod]; simp
      filter_upwards [hae] with p hp
      simp only [Function.uncurry, norm_mul, norm_ee, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hh _)]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hG p.2 (x - p.1) (sub_ne_zero.2 (Ne.symm hp)))
        (rhoH_nonneg hρ hh _)
  calc mult (2 * π * ξ) * ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y)
      = ∫ y, (rhoH ρ (hT T) y : ℂ) * (mult (2 * π * ξ) * betaF ξ (x - y)) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only; ring
    _ = ∫ y, ∫ σ, (rhoH ρ (hT T) y : ℂ) * ((besselG σ (x - y) : ℂ) * ee (-(ξ * σ))) := by
        apply integral_congr_ae
        filter_upwards [ae_ne' x] with y hy
        rw [← (hMe ξ (x - y) (sub_ne_zero.2 (Ne.symm hy))).2, integral_const_mul]
    _ = ∫ σ, ∫ y, (rhoH ρ (hT T) y : ℂ) * ((besselG σ (x - y) : ℂ) * ee (-(ξ * σ))) :=
        integral_integral_swap hint
    _ = ∫ σ, ee (-(ξ * σ)) * (smG ρ T σ x : ℂ) := by
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        simp only
        unfold smG
        rw [← integral_complex_ofReal, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only
        push_cast; ring

/- ### Step 4: Fubini in `(x, σ)` -/

lemma step4_int (hJ : J0Statement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ} (hCg : 0 < Cg)
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹)) (ξ y : ℝ) :
    Integrable (Function.uncurry fun (x σ : ℝ) => ee (-(x * y)) *
      ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ)))) (volume.prod volume) := by
  refine Integrable.mono' ((psi_integrable hρ hT1).abs.mul_prod
    ((integrable_inv_one_add_sq.const_mul Cg).const_mul (Kx ρ T))) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    have hm : Measurable (fun p : ℝ × ℝ => smG ρ T p.2 p.1) := (smG_sm hJ hρ).measurable
    have hee : Measurable ee := continuous_ee.measurable
    have hψ : Measurable (psiF ρ) := psiF_meas hρ
    show Measurable (fun p : ℝ × ℝ => ee (-(p.1 * y)) *
      ((psiF ρ (p.1 / T ^ 2) : ℂ) * (ee (-(ξ * p.2)) * (smG ρ T p.2 p.1 : ℂ))))
    fun_prop
  · filter_upwards with p
    simp only [Function.uncurry, norm_mul, norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hx : |p.1| ≤ T ^ 2
    · exact mul_le_mul_of_nonneg_left (smG_bound hρ hT1 hCg hG p.2 hx) (abs_nonneg _)
    · push Not at hx
      rw [psi_zero hρ hT1 hx.le]
      simp only [abs_zero, zero_mul, le_refl]

lemma Phi_int (hJ : J0Statement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ} (hCg : 0 < Cg)
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹)) (ξ y : ℝ) :
    Integrable (fun σ => ee (-(ξ * σ)) * Phi ρ T σ y) := by
  have := (step4_int hJ hρ hT1 hCg hG ξ y).integral_prod_right
  refine this.congr (ae_of_all _ fun σ => ?_)
  simp only [Function.uncurry]
  unfold Phi
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  push_cast; ring

lemma core (hJ : J0Statement) (hMe : MellinStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ}
    (hCg : 0 < Cg) (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹))
    (ξ c y : ℝ) :
    mult (2 * π * ξ) * ∫ x, ee (-(x * y)) * (((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
      ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y')) =
    (c : ℂ) * ∫ σ, ee (-(ξ * σ)) * Phi ρ T σ y := by
  calc mult (2 * π * ξ) * ∫ x, ee (-(x * y)) * (((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
        ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y'))
      = ∫ x, (c : ℂ) * ∫ σ, ee (-(x * y)) *
          ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        have h3 := step3 hJ hMe hρ hT1 hG ξ x
        calc mult (2 * π * ξ) * (ee (-(x * y)) * (((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
              ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y')))
            = ee (-(x * y)) * ((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
              (mult (2 * π * ξ) * ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y')) := by ring
          _ = ee (-(x * y)) * ((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
              ∫ σ, ee (-(ξ * σ)) * (smG ρ T σ x : ℂ) := by rw [h3]
          _ = (c : ℂ) * ∫ σ, ee (-(x * y)) *
              ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) := by
              rw [← integral_const_mul, ← integral_const_mul]
              refine integral_congr_ae (ae_of_all _ fun σ => ?_)
              simp only
              push_cast; ring
    _ = (c : ℂ) * ∫ x, ∫ σ, ee (-(x * y)) *
          ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) :=
        integral_const_mul _ _
    _ = (c : ℂ) * ∫ σ, ∫ x, ee (-(x * y)) *
          ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) := by
        rw [integral_integral_swap (step4_int hJ hρ hT1 hCg hG ξ y)]
    _ = (c : ℂ) * ∫ σ, ee (-(ξ * σ)) * Phi ρ T σ y := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        simp only
        unfold Phi
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        push_cast; ring

end steps

end ChowlaOpus.QAux

namespace ChowlaOpus

theorem qposStatement_holds (hJ : J0Statement) (hB : BesselPlaneStatement)
    (hM : MultStatement) (hMe : MellinStatement) (_hA : AnnulusStatement)
    (hF : FejerStatement) : QposStatement := by
  intro ρ hρ T hT1 J
  obtain ⟨Cg, hCg, hG⟩ := QAux.G_bound hJ hB
  have hT0 : 0 < T := by linarith
  have hD : 0 < T * (1 + aT ρ T) := by
    have : 0 ≤ aT ρ T := by
      unfold aT; have := hρ.nonneg 0
      positivity
    positivity
  have hFT : ∀ l : ℤ, ∀ y, mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y =
      ((fejerCoeff J l / (T * (1 + aT ρ T)) : ℝ) : ℂ) *
        ∫ σ, ee (-(((l : ℝ) / T) * σ)) * QAux.Phi ρ T σ y := by
    intro l y
    rw [fourier_eq_ee, show 2 * Real.pi * (l : ℝ) / T = 2 * Real.pi * ((l : ℝ) / T) by ring]
    exact QAux.core hJ hMe hρ hT1 hCg hG ((l : ℝ) / T) (fejerCoeff J l / (T * (1 + aT ρ T))) y
  refine ⟨fun s y => ?_, fun y => ?_⟩
  · have hsum : ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
        mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y * ee (l * s) =
        ∫ σ, (((T * (1 + aT ρ T))⁻¹ : ℝ) : ℂ) * ((fejer J (s - σ / T) : ℝ) : ℂ) *
          QAux.Phi ρ T σ y := by
      calc ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
            mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y * ee (l * s)
          = ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ∫ σ,
              ((fejerCoeff J l / (T * (1 + aT ρ T)) : ℝ) : ℂ) * ee (l * s) *
                (ee (-(((l : ℝ) / T) * σ)) * QAux.Phi ρ T σ y) := by
            apply Finset.sum_congr rfl
            intro l _
            rw [hFT, integral_const_mul]; ring
        _ = ∫ σ, ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
              ((fejerCoeff J l / (T * (1 + aT ρ T)) : ℝ) : ℂ) * ee (l * s) *
                (ee (-(((l : ℝ) / T) * σ)) * QAux.Phi ρ T σ y) := by
            rw [integral_finsetSum]
            intro l _
            exact (QAux.Phi_int hJ hρ hT1 hCg hG _ y).const_mul _
        _ = _ := by
            refine integral_congr_ae (ae_of_all _ fun σ => ?_)
            simp only
            rw [← hF.2.2.2.2.2.1 J (s - σ / T), Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro l _
            have e : ee (l * s) * ee (-(((l : ℝ) / T) * σ)) = ee (l * (s - σ / T)) := by
              rw [← ee_add]; congr 1; ring
            rw [← e]
            push_cast; ring
    rw [hsum]
    have hnn : 0 ≤ ∫ σ, (((T * (1 + aT ρ T))⁻¹ : ℝ) : ℂ) * ((fejer J (s - σ / T) : ℝ) : ℂ) *
        QAux.Phi ρ T σ y :=
      QAux.integral_cnonneg fun σ => mul_nonneg (mul_nonneg
        (Complex.zero_le_real.2 (inv_nonneg.2 hD.le)) (Complex.zero_le_real.2 (hF.2.1 J _)))
        (QAux.Phi_nonneg hB hρ hT1 σ y)
    exact QAux.cnonneg_iff.1 hnn
  · have h0 := hFT 0 y
    simp only [Int.cast_zero, mul_zero, zero_div, zero_mul, neg_zero, ee_zero, one_mul] at h0
    rw [hM.2.1, one_mul] at h0
    rw [h0]
    have hnn : 0 ≤ ((fejerCoeff J 0 / (T * (1 + aT ρ T)) : ℝ) : ℂ) * ∫ σ, QAux.Phi ρ T σ y :=
      mul_nonneg (Complex.zero_le_real.2 (div_nonneg (fejerCoeff_nonneg _ _) hD.le))
        (QAux.integral_cnonneg fun σ => QAux.Phi_nonneg hB hρ hT1 σ y)
    exact QAux.cnonneg_iff.1 hnn

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Var.lean. -/
section

open scoped FourierTransform ContDiff ENNReal
open Real MeasureTheory Set

namespace ChowlaOpus.VarAux

/- ### Generic tools -/

lemma lintegral_comp_mul_left' (g : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, g (a * x) = ENNReal.ofReal a⁻¹ * ∫⁻ y, g y := by
  have h1 : ∫⁻ y, g y ∂(Measure.map (a * ·) volume) = ∫⁻ x, g (a * x) :=
    lintegral_map_equiv g (Homeomorph.mulLeft₀ a ha.ne').toMeasurableEquiv
  rw [← h1, Real.map_volume_mul_left ha.ne', lintegral_smul_measure, abs_of_pos (inv_pos.mpr ha)]
  rfl

lemma lintegral_unfold (f : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ r, f r = ∑' j : ℤ, ∫⁻ r in Ioc c (c + 1), f (r + j) := by
  rw [← setLIntegral_univ, ← iUnion_Ioc_add_intCast c,
    lintegral_iUnion (fun n => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast c)]
  congr 1; ext j
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    ← lintegral_add_right_eq_self _ (j : ℝ)]
  congr 1; ext r
  simp only [indicator, mem_Ioc]
  have : (c + j < r + j ∧ r + j ≤ c + j + 1) ↔ (c < r ∧ r ≤ c + 1) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [this]

lemma lintegral_unfold' (f : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ r, f r = ∑' j : ℤ, ∫⁻ r in Ioc c (c + 1), f (r - j) := by
  rw [lintegral_unfold f c, ← (Equiv.neg ℤ).tsum_eq]
  congr 1
  ext j
  simp [sub_eq_add_neg]

lemma lintegral_unfold_T (g : ℝ → ℝ≥0∞) {T : ℝ} (hT : 0 < T) :
    ∑' j : ℤ, ∫⁻ s in Ioc 0 1, g (T * s + j * T) = ENNReal.ofReal T⁻¹ * ∫⁻ σ, g σ := by
  rw [← lintegral_comp_mul_left' g hT, lintegral_unfold (fun u => g (T * u)) 0]
  simp only [zero_add]
  congr 1; ext j; congr 1; ext s; ring_nf

lemma ofReal_abs_sub_le {a p : ℝ} {Γ : ℝ≥0∞} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (h1 : ENNReal.ofReal a ≤ ENNReal.ofReal p + Γ) (h2 : ENNReal.ofReal p ≤ ENNReal.ofReal a + Γ) :
    ENNReal.ofReal |a - p| ≤ Γ := by
  rcases eq_or_ne Γ ⊤ with h | h
  · simp [h]
  · have hg : 0 ≤ Γ.toReal := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_toReal h] at h1 h2 ⊢
    rw [← ENNReal.ofReal_add hp hg, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    rw [← ENNReal.ofReal_add ha hg, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩)

lemma mul_one_sub_le_abs_sub_nat {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) (n : ℕ) :
    w * (1 - w) ≤ |w - n| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, sub_zero]; rw [abs_of_nonneg h0]; nlinarith
  · have : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; nlinarith

lemma annB_eq_zero_or_one (σ x : ℝ) : annB σ x = 0 ∨ annB σ x = 1 := by
  unfold annB; split_ifs <;> simp

lemma annB_nonneg (σ x : ℝ) : 0 ≤ annB σ x := by
  rcases annB_eq_zero_or_one σ x with h | h <;> rw [h] <;> norm_num

lemma annB_le_one (σ x : ℝ) : annB σ x ≤ 1 := by
  rcases annB_eq_zero_or_one σ x with h | h <;> rw [h] <;> norm_num

lemma annB_support {σ x : ℝ} (h : annB σ x ≠ 0) : |x| ≤ Real.exp σ := by
  unfold annB at h
  split_ifs at h with h'
  · exact h'.1
  · exact absurd rfl h

lemma perB_nat {T σ x : ℝ} (hs : Summable (fun j : ℤ => annB (σ + j * T) x)) :
    ∃ n : ℕ, perB T σ x = n := by
  have hfin : {j : ℤ | annB (σ + j * T) x ≠ 0}.Finite := by
    have h2 : ∀ᶠ j : ℤ in Filter.cofinite, annB (σ + (j:ℝ) * T) x ∈ Ioo (-1/2 : ℝ) (1/2) :=
      hs.tendsto_cofinite_zero (Ioo_mem_nhds (by norm_num : (-1/2:ℝ) < 0)
        (by norm_num : (0:ℝ) < 1/2))
    rw [Filter.eventually_cofinite] at h2
    refine h2.subset ?_
    intro j hj
    simp only [mem_setOf_eq, mem_Ioo] at hj ⊢
    rcases annB_eq_zero_or_one (σ + j*T) x with h | h
    · exact absurd h hj
    · rw [h]; norm_num
  refine ⟨hfin.toFinset.card, ?_⟩
  unfold perB
  rw [tsum_eq_sum (s := hfin.toFinset) (fun j hj => by simpa using hj)]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Set.Finite.mem_toFinset, mem_setOf_eq] at hj
  rcases annB_eq_zero_or_one (σ + j*T) x with h | h
  · exact absurd h hj
  · simp [h]

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma integral_ee_int (k : ℤ) :
    ∫ s in (0:ℝ)..1, ee (k * s) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [ee_zero]
  · have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have : ∀ s : ℝ, ee (k * s) = Complex.exp ((2 * π * Complex.I * k) * s) := by
      intro s; unfold ee; congr 1; push_cast; ring
    simp_rw [this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * k) = 1 := by
      have := ee_intCast k; unfold ee at this; rw [← this]; congr 1
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, h1,
      sub_self, zero_div]

lemma parseval (J : ℕ) (b : ℤ → ℂ)
    (hW : ∀ s : ℝ, (∑ l ∈ Finset.Icc (-(J:ℤ)) J, b l * ee (l * s)).im = 0) :
    ∫ s in (0:ℝ)..1, (∑ l ∈ Finset.Icc (-(J:ℤ)) J, b l * ee (l * s)).re *
        (1 - (∑ l ∈ Finset.Icc (-(J:ℤ)) J, b l * ee (l * s)).re)
      = (b 0).re - ∑ l ∈ Finset.Icc (-(J:ℤ)) J, ‖b l‖ ^ 2 := by
  set S := Finset.Icc (-(J:ℤ)) J with hS
  set W : ℝ → ℂ := fun s => ∑ l ∈ S, b l * ee (l * s) with hWdef
  have hee : ∀ l : ℤ, Continuous (fun s : ℝ => ee (l * s)) :=
    fun l => continuous_ee.comp (continuous_const.mul continuous_id)
  have hWc : Continuous W := continuous_finsetSum _ (fun l _ => continuous_const.mul (hee l))
  have h0S : (0:ℤ) ∈ S := by simp [hS]
  have hpt : ∀ s, (((W s).re * (1 - (W s).re) : ℝ) : ℂ) = W s - W s * starRingEnd ℂ (W s) := by
    intro s
    have hre : W s = ((W s).re : ℂ) := by apply Complex.ext <;> simp [hW s, hWdef]
    rw [hre]; simp only [Complex.ofReal_re, Complex.conj_ofReal]; push_cast; ring
  have h1 : ∫ s in (0:ℝ)..1, W s = b 0 := by
    simp only [hWdef]
    rw [intervalIntegral.integral_finsetSum
      (fun l _ => ((hee l).const_mul (b l) |>.intervalIntegrable _ _))]
    simp_rw [intervalIntegral.integral_const_mul, integral_ee_int]
    simp [Finset.sum_ite_eq', h0S]
  have hprod : ∀ s, W s * starRingEnd ℂ (W s) =
      ∑ l ∈ S, ∑ m ∈ S, b l * starRingEnd ℂ (b m) * ee (((l - m : ℤ) : ℝ) * s) := by
    intro s
    have hc : starRingEnd ℂ (W s) = ∑ m ∈ S, starRingEnd ℂ (b m) * ee (-(m * s)) := by
      simp only [hWdef, map_sum, map_mul, ee_neg]
    rw [hc]
    show (∑ l ∈ S, b l * ee (l * s)) * _ = _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro m _
    rw [show ee (((l - m : ℤ) : ℝ) * s) = ee (l * s) * ee (-(m * s)) by
      rw [← ee_add]; congr 1; push_cast; ring]
    ring
  have h2 : ∫ s in (0:ℝ)..1, W s * starRingEnd ℂ (W s) = ∑ l ∈ S, ((‖b l‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hprod]
    rw [intervalIntegral.integral_finsetSum
      (f := fun l s => ∑ m ∈ S, b l * starRingEnd ℂ (b m) * ee (((l - m : ℤ) : ℝ) * s))
      (fun l _ => (continuous_finsetSum _ (fun m _ =>
      continuous_const.mul (hee (l - m)))).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl; intro l hl
    rw [intervalIntegral.integral_finsetSum
      (f := fun m s => b l * starRingEnd ℂ (b m) * ee (((l - m : ℤ) : ℝ) * s))
      (fun m _ => ((hee (l - m)).const_mul _ |>.intervalIntegrable _ _))]
    simp_rw [intervalIntegral.integral_const_mul, integral_ee_int, sub_eq_zero]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [hl, if_true]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint : ∫ s in (0:ℝ)..1, (((W s).re * (1 - (W s).re) : ℝ) : ℂ)
      = b 0 - ∑ l ∈ S, ((‖b l‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    have hi1 : IntervalIntegrable W volume 0 1 := hWc.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => W s * starRingEnd ℂ (W s)) volume 0 1 :=
      (hWc.mul (Complex.continuous_conj.comp hWc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2, h1, h2]
  rw [intervalIntegral.integral_ofReal] at hint
  have := congrArg Complex.re hint
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.re_sum] at this
  exact this

/- ### Integral computations -/

lemma lint_min_exp {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    ∫⁻ σ, ENNReal.ofReal (min h (exp (-|σ|))) ≤ ENNReal.ofReal (2 * h * (Real.log h⁻¹ + 1)) := by
  set M := Real.log h⁻¹ with hM
  have hM0 : 0 ≤ M := Real.log_nonneg ((one_le_inv₀ h0).mpr h1)
  have heM : exp (-M) = h := by rw [hM, Real.log_inv, neg_neg, Real.exp_log h0]
  have hpt : ∀ σ, ENNReal.ofReal (min h (exp (-|σ|))) ≤
      (Icc (-M) M).indicator (fun _ => ENNReal.ofReal h) σ +
      ((Ioi M).indicator (fun σ => ENNReal.ofReal (exp (-σ))) σ +
       (Iio (-M)).indicator (fun σ => ENNReal.ofReal (exp σ)) σ) := by
    intro σ
    by_cases hσ : σ ∈ Icc (-M) M
    · rw [indicator_of_mem hσ]
      exact le_add_right (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    · rw [indicator_of_notMem hσ, zero_add]
      simp only [mem_Icc, not_and_or, not_le] at hσ
      rcases hσ with hσ | hσ
      · have h2 : σ ∈ Iio (-M) := hσ
        rw [indicator_of_mem h2, indicator_of_notMem (by simp only [mem_Ioi, not_lt]; linarith),
          zero_add]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_neg (by linarith), neg_neg]; exact min_le_right _ _
      · have h2 : σ ∈ Ioi M := hσ
        rw [indicator_of_mem h2, indicator_of_notMem (by simp only [mem_Iio, not_lt]; linarith),
          add_zero]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_pos (by linarith)]; exact min_le_right _ _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left (measurable_const.indicator measurableSet_Icc),
    lintegral_add_left ((Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioi)]
  rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ioi,
    lintegral_indicator measurableSet_Iio, setLIntegral_const, Real.volume_Icc]
  have hI1 : ∫⁻ σ in Ioi M, ENNReal.ofReal (exp (-σ)) = ENNReal.ofReal h := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi M)
      (ae_of_all _ (fun _ => (exp_pos _).le)), integral_exp_neg_Ioi, heM]
  have hI2 : ∫⁻ σ in Iio (-M), ENNReal.ofReal (exp σ) = ENNReal.ofReal h := by
    rw [setLIntegral_congr Iio_ae_eq_Iic, ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_exp_Iic (-M)) (ae_of_all _ (fun _ => (exp_pos _).le)), integral_exp_Iic, heM]
  rw [hI1, hI2, ← ENNReal.ofReal_mul h0.le, ← ENNReal.ofReal_add h0.le h0.le,
    ← ENNReal.ofReal_add (by nlinarith) (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

lemma lint_min_inv_sq {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ x, ENNReal.ofReal (min c (1 / (2 * x ^ 2))) ≤ ENNReal.ofReal (π * √(2 * c)) := by
  rcases hc.eq_or_lt with rfl | hc'
  · have : ∀ x : ℝ, min 0 (1 / (2 * x ^ 2)) = 0 := fun x => min_eq_left (by positivity)
    simp [this]
  set k := √(2 * c) with hk
  have hk0 : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hk2 : k ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
  have hpt : ∀ x, min c (1 / (2 * x ^ 2)) ≤ 2 * c * (1 + (k * x) ^ 2)⁻¹ := by
    intro x
    rw [mul_pow, hk2]
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero,
        add_zero, inv_one, mul_one]
      exact (min_le_right _ _).trans (by linarith)
    have hx2 : 0 < x ^ 2 := by positivity
    by_cases h : 2 * c * x ^ 2 ≤ 1
    · refine (min_le_left _ _).trans ?_
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; nlinarith
    · push_neg at h
      refine (min_le_right _ _).trans ?_
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hcomp := lintegral_comp_mul_left' (fun y => ENNReal.ofReal ((1 + y ^ 2)⁻¹)) hk0
  calc ∫⁻ x, ENNReal.ofReal (min c (1 / (2 * x ^ 2)))
      ≤ ∫⁻ x, ENNReal.ofReal (2 * c * (1 + (k * x) ^ 2)⁻¹) :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hpt x))
    _ = ENNReal.ofReal (2 * c) * ∫⁻ x, ENNReal.ofReal ((1 + (k * x) ^ 2)⁻¹) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; congr 1; ext x
        rw [ENNReal.ofReal_mul (by linarith)]
    _ = ENNReal.ofReal (2 * c) * (ENNReal.ofReal k⁻¹ * ENNReal.ofReal π) := by
        rw [hcomp, ← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
          (ae_of_all _ (fun _ => by positivity)), integral_univ_inv_one_add_sq]
    _ = ENNReal.ofReal (π * √(2 * c)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← hk, ← hk2]; field_simp

/- ### Facts about the bump -/

variable {ρ : ℝ → ℝ}

lemma rho_cont (hρ : IsBump ρ) : Continuous ρ := hρ.smooth.continuous

lemma rho_zero_pos (hρ : IsBump ρ) : 0 < ρ 0 := by
  by_contra h
  push_neg at h
  have h0 : ∀ x, ρ x = 0 := fun x => le_antisymm ((hρ.le_at_zero x).trans h) (hρ.nonneg x)
  have h1 := hρ.integral_eq
  simp [h0] at h1

lemma psi_nonneg (hρ : IsBump ρ) (u : ℝ) : 0 ≤ psiF ρ u :=
  div_nonneg (hρ.nonneg u) (rho_zero_pos hρ).le

lemma psi_le_one (hρ : IsBump ρ) (u : ℝ) : psiF ρ u ≤ 1 :=
  (div_le_one (rho_zero_pos hρ)).mpr (hρ.le_at_zero u)

lemma psi_cont (hρ : IsBump ρ) : Continuous (psiF ρ) := (rho_cont hρ).div_const _

lemma psi_lip (hρ : IsBump ρ) : ∃ L : ℝ, 0 ≤ L ∧ ∀ u, 1 - psiF ρ u ≤ L * |u| := by
  have hcs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1)) (fun x hx => ?_)
    apply hρ.supp
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hρ.smooth (by simp)
  have h0 := rho_zero_pos hρ
  refine ⟨K / ρ 0, by positivity, fun u => ?_⟩
  have := hK.dist_le_mul u 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
  unfold psiF
  have e : 1 - ρ u / ρ 0 = (ρ 0 - ρ u) / ρ 0 := by field_simp
  rw [e, div_le_iff₀ h0]
  have e2 : (K:ℝ) / ρ 0 * |u| * ρ 0 = K * |u| := by field_simp
  rw [e2]
  have := le_abs_self (ρ 0 - ρ u)
  rw [abs_sub_comm] at this
  linarith

lemma rhoH_cont (hρ : IsBump ρ) (h : ℝ) : Continuous (rhoH ρ h) := by
  unfold rhoH; exact ((rho_cont hρ).comp (continuous_id.div_const h)).div_const h

lemma rhoH_nonneg (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ rhoH ρ h y :=
  div_nonneg (hρ.nonneg _) hh.le

lemma rhoH_eq_zero (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {y : ℝ} (hy : h ≤ |y|) :
    rhoH ρ h y = 0 := by
  unfold rhoH; rw [hρ.supp (y/h) ?_, zero_div]
  rw [abs_div, abs_of_pos hh, le_div_iff₀ hh, one_mul]; exact hy

lemma rhoH_integral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : ∫ y, rhoH ρ h y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div (fun y => ρ y) h, hρ.integral_eq, abs_of_pos hh,
    smul_eq_mul, mul_one, div_self hh.ne']

lemma rhoH_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : Integrable (rhoH ρ h) := by
  by_contra hni
  have := integral_undef hni
  rw [rhoH_integral hρ hh] at this; norm_num at this

lemma rhoH_lintegral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) :
    ∫⁻ y, ENNReal.ofReal (rhoH ρ h y) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (rhoH_integrable hρ hh)
    (ae_of_all _ (rhoH_nonneg hρ hh)), rhoH_integral hρ hh, ENNReal.ofReal_one]

lemma hT_pos {T : ℝ} (hT0 : 0 < T) : 0 < hT T := by unfold hT; positivity

/- ### Facts about the Fejér kernel -/

lemma fejer_per_int (hF : FejerStatement) (J : ℕ) (t : ℝ) (n : ℤ) :
    fejer J (t + n) = fejer J t := by
  have hp : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  simpa using hp.int_mul n t

lemma fejer_int_shift (hF : FejerStatement) (J : ℕ) (c : ℝ) :
    ∫ s in (0:ℝ)..1, fejer J (s - c) = 1 := by
  rw [intervalIntegral.integral_comp_sub_right (fun s => fejer J s) c]
  have hp : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  rw [show (1:ℝ) - c = (0 - c) + 1 by ring, hp.intervalIntegral_add_eq (0 - c) 0, zero_add]
  exact hF.2.2.2.2.1 J

lemma fejer_lint_shift (hF : FejerStatement) (J : ℕ) (c : ℝ) :
    ∫⁻ s in Ioc 0 1, ENNReal.ofReal (fejer J (s - c)) = 1 := by
  have hc : Continuous (fun s => fejer J (s - c)) :=
    (hF.1 J).comp (continuous_id.sub continuous_const)
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (fun s => hF.2.1 J _)), ← intervalIntegral.integral_of_le zero_le_one,
    fejer_int_shift hF J c, ENNReal.ofReal_one]

lemma fejer_lint_half (hF : FejerStatement) (J : ℕ) :
    ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hF.1 J).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (fun s => hF.2.1 J _)), ← intervalIntegral.integral_of_le (by norm_num)]
  have hp : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  rw [show (∫ t in (-(1/2):ℝ)..(1/2), fejer J t) = ∫ t in (-(1/2):ℝ)..(-(1/2) + 1), fejer J t by
    norm_num, hp.intervalIntegral_add_eq (-(1/2)) 0, zero_add, hF.2.2.2.2.1 J, ENNReal.ofReal_one]

lemma fejer_moment_lint (hF : FejerStatement) : ∃ C : ℝ, 0 < C ∧ ∀ J : ℕ, 1 ≤ J →
    ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r * √|r|) ≤
      ENNReal.ofReal (C / √J) := by
  obtain ⟨C, hC, hmom⟩ := hF.2.2.2.2.2.2
  refine ⟨C, hC, fun J hJ => ?_⟩
  have hc : Continuous (fun r => fejer J r * √|r|) := (hF.1 J).mul (continuous_abs.sqrt)
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (fun r => mul_nonneg (hF.2.1 J r) (Real.sqrt_nonneg _))),
    ← intervalIntegral.integral_of_le (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (hmom J hJ)

lemma fejer_abs_le (J : ℕ) (t : ℝ) : |fejer J t| ≤ (Finset.Icc (-(J:ℤ)) J).card := by
  unfold fejer
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [abs_mul, Nat.cast_one]
  have h1 := Real.abs_cos_le_one (2 * π * k * t)
  have h2 : |fejerCoeff J k| ≤ 1 := by
    rw [abs_of_nonneg (fejerCoeff_nonneg J k)]; exact fejerCoeff_le_one J k
  nlinarith [abs_nonneg (fejerCoeff J k), abs_nonneg (Real.cos (2 * π * k * t))]

/- ### Facts about the annulus slice -/

lemma A_meas (hA : AnnulusStatement) : Measurable (Function.uncurry annB) := hA.1
lemma A_int_sigma (hA : AnnulusStatement) : ∀ x, x ≠ 0 → Integrable (fun σ => annB σ x) :=
  hA.2.2.2.1
lemma A_ell_le (hA : AnnulusStatement) : ∀ x, x ≠ 0 → ellF x ≤ 1 / (2 * x ^ 2) :=
  hA.2.2.2.2.2.2.1
lemma A_slice (hA : AnnulusStatement) :
    ∀ σ, Integrable (annB σ) ∧ ∫ x, annB σ x ≤ 2 * Real.exp (-|σ|) :=
  hA.2.2.2.2.2.2.2.2.2.1
lemma A_E1 (hA : AnnulusStatement) :
    ∀ x δ, x ≠ 0 → ∫ σ, |annB (σ - δ) x - annB σ x| ≤ 2 * min |δ| (ellF x) :=
  hA.2.2.2.2.2.2.2.2.2.2.1
lemma A_E2 (hA : AnnulusStatement) :
    ∀ σ u, ∫ x, |annB σ (x - u) - annB σ x| ≤ min (4 * |u|) (4 * Real.exp (-|σ|)) :=
  hA.2.2.2.2.2.2.2.2.2.2.2.1
lemma A_summ (hA : AnnulusStatement) :
    ∀ T σ x, 1 ≤ T → x ≠ 0 → Summable (fun j : ℤ => annB (σ + j * T) x) :=
  hA.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma measurable_annB_comp (hA : AnnulusStatement) {α : Type*} [MeasurableSpace α]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => annB (f p) (g p)) := by
  have h := (A_meas hA).comp (hf.prodMk hg)
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

lemma measurable_annB_diff (hA : AnnulusStatement) {α : Type*} [MeasurableSpace α]
    {f g h k : α → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hk : Measurable k) :
    Measurable (fun p => ENNReal.ofReal |annB (f p) (g p) - annB (h p) (k p)|) :=
  (continuous_abs.measurable.comp ((measurable_annB_comp hA hf hg).sub
    (measurable_annB_comp hA hh hk))).ennreal_ofReal

lemma smB_measurable (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) :
    Measurable (fun p : ℝ × ℝ => smB ρ T p.1 p.2) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => rhoH ρ (hT T) q.2 * annB q.1.1 (q.1.2 - q.2)) :=
    ((rhoH_cont hρ _).measurable.comp measurable_snd).mul
      (measurable_annB_comp hA (measurable_fst.comp measurable_fst)
        ((measurable_snd.comp measurable_fst).sub measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma smB_comp (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) {α : Type*} [MeasurableSpace α]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => smB ρ T (f p) (g p)) := by
  have h := (smB_measurable hρ hA T).comp (hf.prodMk hg)
  simpa only [Function.comp_def] using h

lemma smB_diff_meas (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) {α : Type*}
    [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => ENNReal.ofReal |smB ρ T (f p) (g p) - annB (f p) (g p)|) :=
  (continuous_abs.measurable.comp ((smB_comp hρ hA T hf hg).sub
    (measurable_annB_comp hA hf hg))).ennreal_ofReal

lemma smB_sub_le (hρ : IsBump ρ) (hA : AnnulusStatement) {T : ℝ} (hT0 : 0 < T) (σ x : ℝ) :
    ENNReal.ofReal |smB ρ T σ x - annB σ x| ≤
      ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal |annB σ (x - y) - annB σ x| := by
  have hh := hT_pos hT0
  have hint1 : Integrable (fun y => rhoH ρ (hT T) y * annB σ (x - y)) := by
    refine (rhoH_integrable hρ hh).mul_bdd (c := 1) ?_ (ae_of_all _ (fun y => ?_))
    · exact (measurable_annB_comp hA measurable_const
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (annB_nonneg _ _)]; exact annB_le_one _ _
  have hint2 : Integrable (fun y => rhoH ρ (hT T) y * annB σ x) :=
    (rhoH_integrable hρ hh).mul_const _
  have heq : smB ρ T σ x - annB σ x =
      ∫ y, rhoH ρ (hT T) y * (annB σ (x - y) - annB σ x) := by
    simp_rw [mul_sub]
    rw [integral_sub hint1 hint2, integral_mul_const, rhoH_integral hρ hh, one_mul]
    rfl
  rw [heq, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr (fun y => ?_)
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (rhoH_nonneg hρ hh y),
    ENNReal.ofReal_mul (rhoH_nonneg hρ hh y)]

lemma E2_lint (hA : AnnulusStatement) (σ u : ℝ) :
    ∫⁻ x, ENNReal.ofReal |annB σ (x - u) - annB σ x| ≤
      ENNReal.ofReal (min (4 * |u|) (4 * Real.exp (-|σ|))) := by
  have hint : Integrable (fun x => |annB σ (x - u) - annB σ x|) :=
    (((A_slice hA σ).1.comp_sub_right u).sub (A_slice hA σ).1).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (A_E2 hA σ u)

lemma E1_lint (hA : AnnulusStatement) {x : ℝ} (hx : x ≠ 0) (δ : ℝ) :
    ∫⁻ σ, ENNReal.ofReal |annB (σ - δ) x - annB σ x| ≤ ENNReal.ofReal (2 * min |δ| (ellF x)) := by
  have hint : Integrable (fun σ => |annB (σ - δ) x - annB σ x|) :=
    (((A_int_sigma hA x hx).comp_sub_right δ).sub (A_int_sigma hA x hx)).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (A_E1 hA x δ hx)

lemma slice_lint (hA : AnnulusStatement) (σ : ℝ) :
    ∫⁻ x, ENNReal.ofReal (annB σ x) ≤ ENNReal.ofReal (2 * Real.exp (-|σ|)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (A_slice hA σ).1 (ae_of_all _ (annB_nonneg σ))]
  exact ENNReal.ofReal_le_ofReal (A_slice hA σ).2

lemma smooth_err (hρ : IsBump ρ) (hA : AnnulusStatement) {T : ℝ} (hT0 : 0 < T) (σ : ℝ) :
    ∫⁻ x, ENNReal.ofReal |smB ρ T σ x - annB σ x| ≤
      ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
  have hh := hT_pos hT0
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (rhoH ρ (hT T) p.2) *
      ENNReal.ofReal |annB σ (p.1 - p.2) - annB σ p.1|) :=
    ((rhoH_cont hρ _).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_annB_diff hA measurable_const (by fun_prop) measurable_const measurable_fst)
  calc ∫⁻ x, ENNReal.ofReal |smB ρ T σ x - annB σ x|
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ENNReal.ofReal |annB σ (x - y) - annB σ x| :=
        lintegral_mono (fun x => smB_sub_le hρ hA hT0 σ x)
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ENNReal.ofReal |annB σ (x - y) - annB σ x| :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ∫⁻ x, ENNReal.ofReal |annB σ (x - y) - annB σ x| := by
        refine lintegral_congr (fun y => ?_); rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
        refine lintegral_mono (fun y => ?_)
        by_cases hy : |y| < hT T
        · gcongr
          refine (E2_lint hA σ y).trans (ENNReal.ofReal_le_ofReal ?_)
          rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
          exact min_le_min (by linarith) le_rfl
        · push_neg at hy; rw [rhoH_eq_zero hρ hh hy]; simp
    _ = ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, rhoH_lintegral hρ hh, one_mul]

/- ### The three error functions -/

/-- Physical smoothing error. -/
noncomputable def G1 (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal (fejer J (s - σ / T)) *
    ENNReal.ofReal |smB ρ T σ x - annB σ x|

/-- Label smoothing error. -/
noncomputable def G2 (T : ℝ) (J : ℕ) (s x : ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
    ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x|

/-- Taper/normalization error. -/
noncomputable def G3 (ρ : ℝ → ℝ) (T : ℝ) (s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| *
    ∑' j : ℤ, ENNReal.ofReal (annB (T * s + j * T) x)

lemma G1_meas (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement) (T : ℝ) (J : ℕ) :
    Measurable (fun p : ℝ × ℝ => G1 ρ T J p.1 p.2) := by
  unfold G1
  refine measurable_const.mul ?_
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (fejer J (q.1.1 - q.2 / T)) *
      ENNReal.ofReal |smB ρ T q.2 q.1.2 - annB q.2 q.1.2|) := by
    refine ((hF.1 J).measurable.comp ((measurable_fst.comp measurable_fst).sub
      (measurable_snd.div_const T))).ennreal_ofReal.mul ?_
    exact (continuous_abs.measurable.comp (((smB_measurable hρ hA T).comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).sub
      (measurable_annB_comp hA measurable_snd (measurable_snd.comp measurable_fst)))).ennreal_ofReal
  exact hm.lintegral_prod_right'

lemma G2_meas (hA : AnnulusStatement) (hF : FejerStatement) (T : ℝ) (J : ℕ) :
    Measurable (fun p : ℝ × ℝ => G2 T J p.1 p.2) := by
  unfold G2
  refine Measurable.tsum (fun j => ?_)
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (fejer J q.2) *
      ENNReal.ofReal |annB (T * q.1.1 + j * T - T * q.2) q.1.2 - annB (T * q.1.1 + j * T) q.1.2|) :=
    ((hF.1 J).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_annB_diff hA (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  exact hm.lintegral_prod_right'

lemma G3_meas (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) :
    Measurable (fun p : ℝ × ℝ => G3 ρ T p.1 p.2) := by
  unfold G3
  refine Measurable.mul ?_ (Measurable.tsum (fun j => ?_))
  · exact (continuous_abs.comp ((((psi_cont hρ).comp (continuous_snd.div_const _)).div_const
      _).sub continuous_const)).measurable.ennreal_ofReal
  · exact (measurable_annB_comp hA (by fun_prop) measurable_snd).ennreal_ofReal

/- ### Pointwise bounds -/

lemma fejer_annB_integrable (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (J : ℕ)
    {x : ℝ} (hx : x ≠ 0) (s : ℝ) : Integrable (fun σ => fejer J (s - σ / T) * annB σ x) := by
  refine (A_int_sigma hA x hx).bdd_mul (c := (Finset.Icc (-(J:ℤ)) J).card) ?_
    (ae_of_all _ (fun σ => ?_))
  · exact ((hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact fejer_abs_le J _

lemma SA_bound (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement)
    (hW : WrepStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) {x : ℝ} (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal (T⁻¹ * |(∫ σ, fejer J (s - σ / T) * smB ρ T σ x) -
      ∫ σ, fejer J (s - σ / T) * annB σ x|) ≤ G1 ρ T J s x := by
  have hT0 : 0 < T := by linarith
  have hint1 := (hW ρ hρ T hT1 J s x).1
  have hint2 := fejer_annB_integrable hA hF (T := T) J hx s
  rw [← integral_sub hint1 hint2, ENNReal.ofReal_mul (by positivity)]
  unfold G1
  gcongr
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr (fun σ => ?_)
  rw [Real.enorm_eq_ofReal_abs, ← mul_sub, abs_mul, abs_of_nonneg (hF.2.1 J _),
    ENNReal.ofReal_mul (hF.2.1 J _)]

lemma AP_bound (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ)
    {x : ℝ} (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal |T⁻¹ * (∫ σ, fejer J (s - σ / T) * annB σ x) - perB T (T * s) x| ≤
      G2 T J s x := by
  have hT0 : 0 < T := by linarith
  have hsum := A_summ hA T (T * s) x hT1 hx
  have hφint := fejer_annB_integrable hA hF (T := T) J hx s
  have hφnn : ∀ σ, 0 ≤ fejer J (s - σ / T) * annB σ x :=
    fun σ => mul_nonneg (hF.2.1 J _) (annB_nonneg _ _)
  set F : ℝ → ℝ≥0∞ := fun σ => ENNReal.ofReal (fejer J (s - σ / T) * annB σ x) with hFdef
  have hcv : ENNReal.ofReal T⁻¹ * ∫⁻ σ, F σ = ∫⁻ r, F (T * (s - r)) := by
    rw [← lintegral_comp_mul_left' F hT0]
    exact (lintegral_sub_left_eq_self (fun u => F (T * u)) s).symm
  have hA_eq : ENNReal.ofReal (T⁻¹ * ∫ σ, fejer J (s - σ / T) * annB σ x) =
      ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal (annB (T * s + j * T - T * r) x) := by
    rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal hφint
      (ae_of_all _ hφnn), hcv, lintegral_unfold' _ (-(1/2))]
    have hI : Ioc (-(1/2):ℝ) (-(1/2) + 1) = Ioc (-(1/2)) (1/2) := by norm_num
    rw [hI]
    refine tsum_congr (fun j => ?_)
    refine lintegral_congr (fun r => ?_)
    simp only [hFdef]
    have e1 : s - T * (s - (r - j)) / T = r - j := by
      rw [mul_div_cancel_left₀ _ hT0.ne']; ring
    have e2 : T * (s - (r - j)) = T * s + j * T - T * r := by ring
    have e3 : fejer J (r - j) = fejer J r := by
      have := fejer_per_int hF J (r - j) j
      rw [sub_add_cancel] at this; exact this.symm
    rw [e1, e2, e3, ENNReal.ofReal_mul (hF.2.1 J r)]
  have hP_eq : ENNReal.ofReal (perB T (T * s) x) =
      ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal (annB (T * s + j * T) x) := by
    unfold perB
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => annB_nonneg _ _) hsum]
    refine tsum_congr (fun j => ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, fejer_lint_half hF J, one_mul]
  have hIA0 : 0 ≤ T⁻¹ * ∫ σ, fejer J (s - σ / T) * annB σ x :=
    mul_nonneg (by positivity) (integral_nonneg hφnn)
  have hP0 : 0 ≤ perB T (T * s) x := tsum_nonneg (fun j => annB_nonneg _ _)
  have hfm : Measurable (fun r => ENNReal.ofReal (fejer J r)) := (hF.1 J).measurable.ennreal_ofReal
  have key : ∀ u v : ℝ, ENNReal.ofReal u ≤ ENNReal.ofReal v + ENNReal.ofReal |u - v| := by
    intro u v
    exact (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (u - v)])).trans
      ENNReal.ofReal_add_le
  have hαm : ∀ j : ℤ, Measurable (fun r => ENNReal.ofReal (fejer J r) *
      ENNReal.ofReal (annB (T * s + j * T - T * r) x)) :=
    fun j => hfm.mul (measurable_annB_comp hA (by fun_prop) measurable_const).ennreal_ofReal
  have hβm : ∀ j : ℤ, Measurable (fun r => ENNReal.ofReal (fejer J r) *
      ENNReal.ofReal (annB (T * s + j * T) x)) := fun j => hfm.mul measurable_const
  apply ofReal_abs_sub_le hIA0 hP0
  · rw [hA_eq, hP_eq]; unfold G2; rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum (fun j => ?_)
    refine le_trans (lintegral_mono (fun r => ?_)) (le_of_eq (lintegral_add_left (hβm j) _))
    rw [← mul_add]; gcongr; exact key _ _
  · rw [hA_eq, hP_eq]; unfold G2; rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum (fun j => ?_)
    refine le_trans (lintegral_mono (fun r => ?_)) (le_of_eq (lintegral_add_left (hαm j) _))
    rw [← mul_add]; gcongr
    rw [abs_sub_comm]; exact key _ _

lemma kappa_bound {ψ a B : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ 1) (ha : 0 ≤ a) (hB : 1 - ψ ≤ B) :
    |ψ / (1 + a) - 1| ≤ min 1 B + a := by
  have h1a : 0 < 1 + a := by linarith
  have hk1 : ψ / (1 + a) ≤ 1 := (div_le_one h1a).mpr (by linarith)
  rw [abs_of_nonpos (by linarith)]
  have : ψ - a ≤ ψ / (1 + a) := by rw [le_div_iff₀ h1a]; nlinarith
  have hmin : 1 - ψ ≤ min 1 B := le_min (by linarith) hB
  linarith

lemma real_core {W P IS IA κ T : ℝ} (hT0 : 0 < T) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hP0 : 0 ≤ P)
    (hW : W = κ * (T⁻¹ * IS)) :
    |W - P| ≤ T⁻¹ * |IS - IA| + |T⁻¹ * IA - P| + |κ - 1| * P := by
  rw [hW]
  have e : κ * (T⁻¹ * IS) - P = κ * (T⁻¹ * (IS - IA)) + κ * (T⁻¹ * IA - P) + (κ - 1) * P := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_pos (inv_pos.mpr hT0)]
    exact mul_le_of_le_one_left (by positivity) hκ1
  · rw [abs_mul, abs_of_nonneg hκ0]; exact mul_le_of_le_one_left (abs_nonneg _) hκ1
  · rw [abs_mul, abs_of_nonneg hP0]

lemma ennreal_core {a b c d : ℝ} {G1 G2 G3 : ℝ≥0∞} (h : a ≤ b + c + d)
    (h1 : ENNReal.ofReal b ≤ G1) (h2 : ENNReal.ofReal c ≤ G2) (h3 : ENNReal.ofReal d = G3) :
    ENNReal.ofReal a ≤ G1 + G2 + G3 :=
  (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_add_le.trans
    (add_le_add (ENNReal.ofReal_add_le.trans (add_le_add h1 h2)) h3.le))

lemma pointwise (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement)
    (hW : WrepStatement) (hWb : WboundStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) {x : ℝ}
    (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal ((Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re)) ≤
      G1 ρ T J s x + G2 T J s x + G3 ρ T s x := by
  have hT0 : 0 < T := by linarith
  obtain ⟨-, hrep⟩ := hW ρ hρ T hT1 J s x
  obtain ⟨-, hW0, hW1⟩ := hWb ρ hρ T hT1 J s x
  have ha : 0 ≤ aT ρ T := by unfold aT; have := rho_zero_pos hρ; positivity
  have hκ0 : 0 ≤ psiF ρ (x / T ^ 2) / (1 + aT ρ T) := div_nonneg (psi_nonneg hρ _) (by linarith)
  have hκ1 : psiF ρ (x / T ^ 2) / (1 + aT ρ T) ≤ 1 :=
    (div_le_one (by linarith)).mpr ((psi_le_one hρ _).trans (by linarith))
  have hWeq : (Wsum ρ T J s x).re = psiF ρ (x / T ^ 2) / (1 + aT ρ T) *
      (T⁻¹ * ∫ σ, fejer J (s - σ / T) * smB ρ T σ x) := by
    rw [hrep, Complex.ofReal_re]; simp only [div_eq_mul_inv, mul_inv]; ring
  have hsum := A_summ hA T (T * s) x hT1 hx
  obtain ⟨n, hn⟩ := perB_nat hsum
  have hP0 : 0 ≤ perB T (T * s) x := by rw [hn]; exact Nat.cast_nonneg n
  have hstep1 : (Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re) ≤
      |(Wsum ρ T J s x).re - perB T (T * s) x| := by
    rw [hn]; exact mul_one_sub_le_abs_sub_nat hW0 hW1 n
  have hstep2 := real_core (IA := ∫ σ, fejer J (s - σ / T) * annB σ x) hT0 hκ0 hκ1 hP0 hWeq
  have hPe : ENNReal.ofReal (perB T (T * s) x) =
      ∑' j : ℤ, ENNReal.ofReal (annB (T * s + j * T) x) :=
    ENNReal.ofReal_tsum_of_nonneg (fun j => annB_nonneg _ _) hsum
  have h3 : ENNReal.ofReal (|psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| * perB T (T * s) x) =
      G3 ρ T s x := by
    unfold G3
    exact (ENNReal.ofReal_mul (abs_nonneg _)).trans
      (congrArg (ENNReal.ofReal |psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| * ·) hPe)
  exact ennreal_core (hstep1.trans hstep2) (SA_bound hρ hA hF hW hT1 J hx s)
    (AP_bound hA hF hT1 J hx s) h3

/- ### Integrated bounds -/

lemma G1_integral (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ}
    (hT1 : 1 ≤ T) (J : ℕ) :
    ∫⁻ x, ∫⁻ s in Ioc 0 1, G1 ρ T J s x ≤
      ENNReal.ofReal (T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1)))) := by
  have hT0 : 0 < T := by linarith
  have hh0 := hT_pos hT0
  have hh1 : hT T ≤ 1 := by unfold hT; exact inv_le_one_of_one_le₀ (by nlinarith)
  have step1 : ∀ x, ∫⁻ s in Ioc 0 1, G1 ρ T J s x =
      ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal |smB ρ T σ x - annB σ x| := by
    intro x
    have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (fejer J (p.1 - p.2 / T)) *
        ENNReal.ofReal |smB ρ T p.2 x - annB p.2 x|) :=
      ((hF.1 J).measurable.comp (measurable_fst.sub (measurable_snd.div_const T))).ennreal_ofReal.mul
        (smB_diff_meas hρ hA T measurable_snd measurable_const)
    unfold G1
    refine (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
      (congrArg (ENNReal.ofReal T⁻¹ * ·) ?_)
    refine (lintegral_lintegral_swap (f := fun s σ => ENNReal.ofReal (fejer J (s - σ / T)) *
        ENNReal.ofReal |smB ρ T σ x - annB σ x|) hm.aemeasurable).trans
      (lintegral_congr (fun σ => ?_))
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, fejer_lint_shift hF J (σ / T), one_mul]
  have hD' : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal |smB ρ T p.2 p.1 - annB p.2 p.1|) :=
    smB_diff_meas hρ hA T measurable_snd measurable_fst
  simp_rw [step1]
  calc ∫⁻ x, ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal |smB ρ T σ x - annB σ x|
      = ENNReal.ofReal T⁻¹ * ∫⁻ x, ∫⁻ σ, ENNReal.ofReal |smB ρ T σ x - annB σ x| :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal T⁻¹ * ∫⁻ σ, ∫⁻ x, ENNReal.ofReal |smB ρ T σ x - annB σ x| :=
        congrArg (ENNReal.ofReal T⁻¹ * ·) (lintegral_lintegral_swap
          (f := fun x σ => ENNReal.ofReal |smB ρ T σ x - annB σ x|) hD'.aemeasurable)
    _ ≤ ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
        gcongr with σ; exact smooth_err hρ hA hT0 σ
    _ ≤ ENNReal.ofReal T⁻¹ * ENNReal.ofReal (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) := by
        gcongr
        have : ∀ σ, ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) =
            ENNReal.ofReal 4 * ENNReal.ofReal (min (hT T) (Real.exp (-|σ|))) :=
          fun σ => ENNReal.ofReal_mul (by norm_num)
        simp_rw [this]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by norm_num)]
        gcongr; exact lint_min_exp hh0 hh1
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

lemma G2_inner (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ)
    {x : ℝ} (hx : x ≠ 0) :
    ∫⁻ s in Ioc 0 1, G2 T J s x ≤ ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
      (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) := by
  have hT0 : 0 < T := by linarith
  have hmeas : ∀ j : ℤ, Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (fejer J p.2) *
      ENNReal.ofReal |annB (T * p.1 + j * T - T * p.2) x - annB (T * p.1 + j * T) x|) :=
    fun j => ((hF.1 J).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_annB_diff hA (by fun_prop) measurable_const (by fun_prop) measurable_const)
  have hmeas2 : ∀ j : ℤ, Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal |annB (T * p.1 + j * T - T * p.2) x - annB (T * p.1 + j * T) x|) :=
    fun j => measurable_annB_diff hA (by fun_prop) measurable_const (by fun_prop) measurable_const
  unfold G2
  rw [lintegral_tsum (fun j => ((hmeas j).lintegral_prod_right').aemeasurable)]
  calc ∑' j : ℤ, ∫⁻ s in Ioc 0 1, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x|
      = ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ∫⁻ s in Ioc 0 1, ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x| := by
        exact tsum_congr (fun j => lintegral_lintegral_swap (hmeas j).aemeasurable)
    _ = ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) * ∫⁻ s in Ioc 0 1,
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x| := by
        exact tsum_congr (fun j => lintegral_congr (fun r =>
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))
    _ = ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ∑' j : ℤ, ENNReal.ofReal (fejer J r) * ∫⁻ s in Ioc 0 1,
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x| := by
        rw [lintegral_tsum]
        intro j
        exact (((hF.1 J).measurable.ennreal_ofReal).mul
          ((hmeas2 j).lintegral_prod_left')).aemeasurable
    _ = ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) * (ENNReal.ofReal T⁻¹ *
        ∫⁻ σ, ENNReal.ofReal |annB (σ - T * r) x - annB σ x|) := by
        refine lintegral_congr (fun r => ?_)
        rw [ENNReal.tsum_mul_left,
          lintegral_unfold_T (fun σ => ENNReal.ofReal |annB (σ - T * r) x - annB σ x|) hT0]
    _ ≤ ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) := by
        refine lintegral_mono (fun r => ?_)
        gcongr
        refine (E1_lint hA hx (T * r)).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [abs_mul, abs_of_pos hT0]
        gcongr
        exact A_ell_le hA x hx

lemma G2_integral (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ)
    {CF : ℝ} (hmom : ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r * √|r|) ≤
      ENNReal.ofReal (CF / √J)) (hCF : 0 ≤ CF) :
    ∫⁻ x, ∫⁻ s in Ioc 0 1, G2 T J s x ≤
      ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T)) * (CF / √J)) := by
  have hT0 : 0 < T := by linarith
  have hK : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (fejer J p.2) *
      (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |p.2|) (1 / (2 * p.1 ^ 2))))) :=
    ((hF.1 J).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_const.mul (Measurable.ennreal_ofReal (by fun_prop)))
  calc ∫⁻ x, ∫⁻ s in Ioc 0 1, G2 T J s x
      ≤ ∫⁻ x, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) :=
        lintegral_mono_ae ((Measure.ae_ne volume 0).mono fun x hx => G2_inner hA hF hT1 J hx)
    _ = ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ∫⁻ x, ENNReal.ofReal (fejer J r) *
        (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) :=
        lintegral_lintegral_swap hK.aemeasurable
    _ ≤ ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) *
        ENNReal.ofReal (fejer J r * √|r|) := by
        refine lintegral_mono (fun r => ?_)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hfr := hF.2.1 J r
        calc ENNReal.ofReal (fejer J r) * (ENNReal.ofReal T⁻¹ *
              ∫⁻ x, ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2))))
            ≤ ENNReal.ofReal (fejer J r) * (ENNReal.ofReal T⁻¹ *
              ENNReal.ofReal (2 * (π * √(2 * (T * |r|))))) := by
              gcongr
              have : ∀ x : ℝ, ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2))) =
                  ENNReal.ofReal 2 * ENNReal.ofReal (min (T * |r|) (1 / (2 * x ^ 2))) :=
                fun x => ENNReal.ofReal_mul (by norm_num)
              simp_rw [this]
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by norm_num)]
              gcongr
              exact lint_min_inv_sq (by positivity)
          _ = ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) * ENNReal.ofReal (fejer J r * √|r|) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hfr,
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [show 2 * (T * |r|) = (2 * T) * |r| by ring, Real.sqrt_mul (by positivity)]
              ring
    _ = ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) *
        ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r * √|r|) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) * ENNReal.ofReal (CF / √J) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

lemma step4_ineq {L a T σ : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hT : 0 < T) :
    (min 1 (L * exp σ / T ^ 2) + a) * (2 * exp (-|σ|)) ≤
      2 * max L 1 * min (T ^ 2)⁻¹ (exp (-|σ|)) + 2 * a * min 1 (exp (-|σ|)) := by
  have he : exp (-|σ|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg σ])
  rw [min_eq_right he]
  have key : min 1 (L * exp σ / T ^ 2) * exp (-|σ|) ≤ max L 1 * min (T ^ 2)⁻¹ (exp (-|σ|)) := by
    rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ max L 1)]
    apply le_min
    · calc min 1 (L * exp σ / T ^ 2) * exp (-|σ|) ≤ (L * exp σ / T ^ 2) * exp (-|σ|) := by
            gcongr; exact min_le_right _ _
        _ = L * (exp σ * exp (-|σ|)) / T ^ 2 := by ring
        _ ≤ L * 1 / T ^ 2 := by
            gcongr; rw [← exp_add]; exact exp_le_one_iff.mpr (by linarith [le_abs_self σ])
        _ ≤ max L 1 * (T ^ 2)⁻¹ := by
            rw [mul_one, div_eq_mul_inv]; gcongr; exact le_max_left _ _
    · calc min 1 (L * exp σ / T ^ 2) * exp (-|σ|) ≤ 1 * exp (-|σ|) := by
            gcongr; exact min_le_left _ _
        _ ≤ max L 1 * exp (-|σ|) := by gcongr; exact le_max_right _ _
  nlinarith [key, exp_pos (-|σ|)]

lemma G3_integral (hρ : IsBump ρ) (hA : AnnulusStatement) {T : ℝ} (hT1 : 1 ≤ T) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ u, 1 - psiF ρ u ≤ L * |u|) :
    ∫⁻ x, ∫⁻ s in Ioc 0 1, G3 ρ T s x ≤
      ENNReal.ofReal (T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1)))) := by
  have hT0 : 0 < T := by linarith
  have ha : 0 ≤ aT ρ T := by unfold aT; have := rho_zero_pos hρ; positivity
  set c : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal |psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| with hc
  have hcm : Measurable c := (continuous_abs.comp ((((psi_cont hρ).comp
    (continuous_id.div_const _)).div_const _).sub continuous_const)).measurable.ennreal_ofReal
  have step1 : ∀ x, ∫⁻ s in Ioc 0 1, G3 ρ T s x =
      ENNReal.ofReal T⁻¹ * ∫⁻ σ, c x * ENNReal.ofReal (annB σ x) := by
    intro x
    unfold G3
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_tsum (fun j => ((measurable_annB_comp hA (by fun_prop)
        measurable_const).ennreal_ofReal).aemeasurable),
      lintegral_unfold_T (fun σ => ENNReal.ofReal (annB σ x)) hT0,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  have step3 : ∀ σ, ∫⁻ x, c x * ENNReal.ofReal (annB σ x) ≤
      ENNReal.ofReal (min 1 (L * exp σ / T ^ 2) + aT ρ T) *
        ENNReal.ofReal (2 * exp (-|σ|)) := by
    intro σ
    calc ∫⁻ x, c x * ENNReal.ofReal (annB σ x)
        ≤ ∫⁻ x, ENNReal.ofReal (min 1 (L * exp σ / T ^ 2) + aT ρ T) *
            ENNReal.ofReal (annB σ x) := by
          refine lintegral_mono (fun x => ?_)
          rcases annB_eq_zero_or_one σ x with h0 | h1
          · rw [h0]; simp
          · gcongr
            have hx : |x| ≤ exp σ := annB_support (by rw [h1]; norm_num)
            refine ENNReal.ofReal_le_ofReal
              (kappa_bound (psi_nonneg hρ _) (psi_le_one hρ _) ha ((hL _).trans ?_))
            rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < T ^ 2), mul_div_assoc']
            gcongr
      _ = ENNReal.ofReal (min 1 (L * exp σ / T ^ 2) + aT ρ T) *
            ∫⁻ x, ENNReal.ofReal (annB σ x) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact slice_lint hA σ
  have hm2 : Measurable (fun p : ℝ × ℝ => c p.1 * ENNReal.ofReal (annB p.2 p.1)) :=
    (hcm.comp measurable_fst).mul
      (measurable_annB_comp hA measurable_snd measurable_fst).ennreal_ofReal
  simp_rw [step1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hm2.aemeasurable]
  have hmexp : Measurable (fun σ : ℝ => ENNReal.ofReal (min (T ^ 2)⁻¹ (exp (-|σ|)))) :=
    Measurable.ennreal_ofReal (by fun_prop)
  calc ENNReal.ofReal T⁻¹ * ∫⁻ σ, ∫⁻ x, c x * ENNReal.ofReal (annB σ x)
      ≤ ENNReal.ofReal T⁻¹ * ∫⁻ σ, (ENNReal.ofReal (2 * max L 1) *
          ENNReal.ofReal (min (T ^ 2)⁻¹ (exp (-|σ|))) +
          ENNReal.ofReal (2 * aT ρ T) * ENNReal.ofReal (min 1 (exp (-|σ|)))) := by
        gcongr with σ
        refine (step3 σ).trans ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := step4_ineq (σ := σ) hL0 ha hT0
        linarith
    _ = ENNReal.ofReal T⁻¹ * (ENNReal.ofReal (2 * max L 1) *
          (∫⁻ σ, ENNReal.ofReal (min (T ^ 2)⁻¹ (exp (-|σ|)))) +
          ENNReal.ofReal (2 * aT ρ T) * ∫⁻ σ, ENNReal.ofReal (min 1 (exp (-|σ|)))) := by
        rw [lintegral_add_left (hmexp.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal T⁻¹ * (ENNReal.ofReal (2 * max L 1) *
          ENNReal.ofReal (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
          ENNReal.ofReal (2 * aT ρ T) * ENNReal.ofReal (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) := by
        have i1 := lint_min_exp (h := (T ^ 2)⁻¹) (by positivity) (inv_le_one_of_one_le₀ (by nlinarith))
        have i2 := lint_min_exp (h := (1:ℝ)) one_pos le_rfl
        gcongr
    _ = _ := by
        have hl : 0 ≤ Real.log ((T ^ 2)⁻¹)⁻¹ := by
          rw [inv_inv]; exact Real.log_nonneg (by nlinarith)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by simp; positivity),
          ← ENNReal.ofReal_mul (by positivity)]

/- ### Assembly -/

lemma meas_slice {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2)) (x : ℝ) :
    Measurable (fun s => f s x) := hf.comp (measurable_id.prodMk measurable_const)

lemma meas_lint_slice {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (μ : Measure ℝ) [SFinite μ] : Measurable (fun x => ∫⁻ s, f s x ∂μ) :=
  hf.lintegral_prod_left'

lemma lint_add3 {μ : Measure ℝ} {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ s, (f s + g s + h s) ∂μ = (∫⁻ s, f s ∂μ) + (∫⁻ s, g s ∂μ) + ∫⁻ s, h s ∂μ := by
  have hfg : Measurable (fun s => f s + g s) := hf.add hg
  rw [lintegral_add_left hfg, lintegral_add_left hf]

lemma final_arith {ρ : ℝ → ℝ} {T CF L : ℝ} {J : ℕ} (hT3 : 3 ≤ T) (hJ : T ^ 8 ≤ J)
    (hCF : 0 < CF) (hρ0 : 0 < ρ 0) :
    T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) +
      T⁻¹ * (2 * π * √(2 * T)) * (CF / √J) +
      T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) ≤
    (24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0) * Real.log T / T ^ 3 := by
  have hT0 : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hl2 : Real.log ((T ^ 2)⁻¹)⁻¹ = 2 * Real.log T := by
    rw [inv_inv, Real.log_pow]; push_cast; ring
  have hM : 1 ≤ max L 1 := le_max_right _ _
  have hT3' : 0 < T ^ 3 := by positivity
  have hBa : T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) ≤ 24 * Real.log T / T ^ 3 := by
    unfold hT
    rw [hl2]
    have e : T⁻¹ * (4 * (2 * (T ^ 2)⁻¹ * (2 * Real.log T + 1))) =
        8 * (2 * Real.log T + 1) / T ^ 3 := by ring
    rw [e]
    exact (div_le_div_iff_of_pos_right hT3').mpr (by linarith)
  have hBb : T⁻¹ * (2 * π * √(2 * T)) * (CF / √J) ≤ 4 * π * CF * Real.log T / T ^ 3 := by
    have hsq1 : √(2 * T) ≤ 2 * T := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hsq2 : T ^ 4 ≤ √J := by
      have h : √((T ^ 4) ^ 2) = T ^ 4 := Real.sqrt_sq (by positivity)
      calc T ^ 4 = √((T ^ 4) ^ 2) := h.symm
        _ ≤ √J := Real.sqrt_le_sqrt (by rw [← pow_mul]; exact hJ)
    have hT4 : 0 < T ^ 4 := by positivity
    calc T⁻¹ * (2 * π * √(2 * T)) * (CF / √J)
        ≤ T⁻¹ * (2 * π * (2 * T)) * (CF / T ^ 4) := by gcongr
      _ = 4 * π * CF / T ^ 4 := by field_simp; ring
      _ ≤ 4 * π * CF * Real.log T / T ^ 3 := by
        rw [div_le_div_iff₀ hT4 hT3']
        have h1 : T ^ 3 ≤ Real.log T * T ^ 4 := by
          have : T ^ 3 ≤ T ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
          nlinarith
        have hk : 0 ≤ 4 * π * CF := by positivity
        have := mul_le_mul_of_nonneg_left h1 hk
        linarith
  have hBc : T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) ≤
      12 * max L 1 * Real.log T / T ^ 3 + 768 * ρ 0 * Real.log T / T ^ 3 := by
    rw [hl2, show Real.log (1:ℝ)⁻¹ = 0 by simp]
    have e : T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (2 * Real.log T + 1)) +
        2 * aT ρ T * (2 * 1 * (0 + 1))) =
        4 * max L 1 * (2 * Real.log T + 1) / T ^ 3 + 4 * aT ρ T / T := by ring
    rw [e]
    have h1 : 4 * max L 1 * (2 * Real.log T + 1) / T ^ 3 ≤ 12 * max L 1 * Real.log T / T ^ 3 := by
      refine (div_le_div_iff_of_pos_right hT3').mpr ?_
      nlinarith
    have h2 : 4 * aT ρ T / T ≤ 768 * ρ 0 * Real.log T / T ^ 3 := by
      unfold aT
      rw [div_le_div_iff₀ hT0 hT3']
      have hexp : T ^ 4 ≤ 24 * Real.exp T := by
        have := Real.pow_div_factorial_le_exp T hT0.le 4
        norm_num [Nat.factorial] at this
        linarith
      have hu : T ^ 4 * Real.exp (-T) ≤ 24 := by
        have := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-T)).le
        rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
      have ha := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℝ) ≤ 32 * ρ 0 * T)
      have hb := mul_le_mul_of_nonneg_left hlogT (by positivity : (0:ℝ) ≤ 768 * ρ 0 * T)
      nlinarith
    linarith
  have e : (24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0) * Real.log T / T ^ 3 =
      24 * Real.log T / T ^ 3 + 4 * π * CF * Real.log T / T ^ 3 +
      (12 * max L 1 * Real.log T / T ^ 3 + 768 * ρ 0 * Real.log T / T ^ 3) := by ring
  rw [e]
  linarith

lemma Wsum_cont (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (x : ℝ) : Continuous (fun s => Wsum ρ T J s x) := by
  unfold Wsum
  exact continuous_finsetSum _ (fun l _ => continuous_const.mul
    (continuous_ee.comp (continuous_const.mul continuous_id)))

end ChowlaOpus.VarAux

namespace ChowlaOpus

open VarAux in
theorem varStatement_holds (hA : AnnulusStatement) (hF : FejerStatement)
    (hW : WrepStatement) (hWb : WboundStatement) : VarStatement := by
  intro ρ hρ
  obtain ⟨L, hL0, hL⟩ := psi_lip hρ
  obtain ⟨CF, hCF, hmom⟩ := fejer_moment_lint hF
  have hρ0 := rho_zero_pos hρ
  refine ⟨24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0, 3, by positivity, ?_⟩
  intro T hT3 J hJ
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hJ1 : 1 ≤ J := by
    have : (1:ℝ) ≤ J := le_trans (one_le_pow₀ hT1) hJ
    exact_mod_cast this
  set Fx := fun x => (bL ρ T J 0 x).re -
    ∑ l ∈ Finset.Icc (-(J:ℤ)) J, ‖bL ρ T J l x‖ ^ 2 with hFx
  have hFeq : ∀ x, Fx x =
      ∫ s in (0:ℝ)..1, (Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re) := fun x =>
    (parseval J (fun l => bL ρ T J l x) (fun s => (hWb ρ hρ T hT1 J s x).1)).symm
  have hF0 : ∀ x, 0 ≤ Fx x := by
    intro x; rw [hFeq x]
    refine intervalIntegral.integral_nonneg zero_le_one (fun s _ => ?_)
    obtain ⟨-, h0, h1⟩ := hWb ρ hρ T hT1 J s x
    exact mul_nonneg h0 (by linarith)
  set Ba := T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) with hBa
  set Bb := T⁻¹ * (2 * π * √(2 * T)) * (CF / √J) with hBb
  set Bc := T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) with hBc
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hl2 : Real.log (hT T)⁻¹ = 2 * Real.log T := by
    unfold hT; rw [inv_inv, Real.log_pow]; push_cast; ring
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hBa0 : 0 ≤ Ba := by rw [hBa, hl2]; have := hT_pos hT0; positivity
  have hBb0 : 0 ≤ Bb := by positivity
  have ha : 0 ≤ aT ρ T := by unfold aT; positivity
  have hBc0 : 0 ≤ Bc := by
    rw [hBc]
    have : Real.log ((T ^ 2)⁻¹)⁻¹ = 2 * Real.log T := hl2
    rw [this]; simp only [inv_one, Real.log_one, zero_add]; positivity
  have hlint : ∫⁻ x, ENNReal.ofReal (Fx x) ≤ ENNReal.ofReal (Ba + Bb + Bc) := by
    have hm1 := G1_meas hρ hA hF T J
    have hm2 := G2_meas hA hF T J
    have hm3 := G3_meas hρ hA T
    calc ∫⁻ x, ENNReal.ofReal (Fx x)
        ≤ ∫⁻ x, ∫⁻ s in Ioc 0 1, (G1 ρ T J s x + G2 T J s x + G3 ρ T s x) := by
          refine lintegral_mono_ae ((Measure.ae_ne volume 0).mono (fun x hx => ?_))
          have hc : Continuous (fun s => (Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re)) :=
            (Complex.continuous_re.comp (Wsum_cont ρ T J x)).mul
              (continuous_const.sub (Complex.continuous_re.comp (Wsum_cont ρ T J x)))
          rw [hFeq x, intervalIntegral.integral_of_le zero_le_one,
            ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              (ae_of_all _ (fun s => ?_))]
          · exact lintegral_mono (fun s => pointwise hρ hA hF hW hWb hT1 J hx s)
          · obtain ⟨-, h0, h1⟩ := hWb ρ hρ T hT1 J s x
            exact mul_nonneg h0 (by linarith)
      _ = ∫⁻ x, ((∫⁻ s in Ioc 0 1, G1 ρ T J s x) + (∫⁻ s in Ioc 0 1, G2 T J s x) +
            ∫⁻ s in Ioc 0 1, G3 ρ T s x) :=
          lintegral_congr (fun x => lint_add3 (meas_slice hm1 x) (meas_slice hm2 x))
      _ = (∫⁻ x, ∫⁻ s in Ioc 0 1, G1 ρ T J s x) + (∫⁻ x, ∫⁻ s in Ioc 0 1, G2 T J s x) +
            ∫⁻ x, ∫⁻ s in Ioc 0 1, G3 ρ T s x :=
          lint_add3 (meas_lint_slice hm1 _) (meas_lint_slice hm2 _)
      _ ≤ ENNReal.ofReal Ba + ENNReal.ofReal Bb + ENNReal.ofReal Bc :=
          add_le_add (add_le_add (G1_integral hρ hA hF hT1 J)
            (G2_integral hA hF hT1 J (hmom J hJ1) hCF.le)) (G3_integral hρ hA hT1 hL0 hL)
      _ = ENNReal.ofReal (Ba + Bb + Bc) := by
          rw [ENNReal.ofReal_add (by positivity) hBc0, ENNReal.ofReal_add hBa0 hBb0]
  have hbound : Ba + Bb + Bc ≤ (24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0) *
      Real.log T / T ^ 3 := final_arith hT3 hJ hCF hρ0
  by_cases hi : Integrable Fx
  · have h1 := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hF0)
    rw [← h1] at hlint
    have h2 : ∫ x, Fx x ≤ Ba + Bb + Bc :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlint
    exact h2.trans hbound
  · rw [integral_undef hi]
    have : 0 < Real.log T := by linarith
    positivity

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/AsmA.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

theorem lemma3Statement_holds (hBump : BumpStatement) (hC : CoeffStatement)
    (hCM : CoeffMassStatement) (hWb : WboundStatement) (hQ : QposStatement)
    (hV : VarStatement) : Lemma3Statement := by
  obtain ⟨ρ, hρ⟩ := hBump
  obtain ⟨C₁, c, T₁, hC₁, hc, hmass⟩ := hCM ρ hρ
  obtain ⟨C₂, T₂, hC₂, hvar⟩ := hV ρ hρ
  refine ⟨max C₁ C₂, c, lt_max_of_lt_left hC₁, hc, max (max T₁ T₂) 1, ?_⟩
  intro T hT
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T / T := div_nonneg (Real.log_nonneg hT1) hTpos.le
  have hlogT3 : 0 ≤ Real.log T / T ^ 3 := div_nonneg (Real.log_nonneg hT1) (by positivity)
  set J : ℕ := ⌈T ^ 8⌉₊ with hJ
  have hJ8 : T ^ 8 ≤ (J : ℝ) := Nat.le_ceil _
  refine ⟨J, bL ρ T J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact (hC ρ hρ T hT1 J l).2.2.2.2.2 hl
  · intro l
    exact (hC ρ hρ T hT1 J l).1
  · intro l x hx
    exact (hC ρ hρ T hT1 J l).2.1 x hx
  · intro l x
    exact (hC ρ hρ T hT1 J l).2.2.1 x
  · intro l x
    exact (hC ρ hρ T hT1 J l).2.2.2.1 x
  · intro x
    exact (hC ρ hρ T hT1 J 0).2.2.2.2.1 x
  · intro y
    exact (hQ ρ hρ T hT1 J).2 y
  · exact (hmass T hT₁ J).1
  · calc ∑' j : ℤ, (bL ρ T J 0 j).re ≤ C₁ * Real.log T / T := (hmass T hT₁ J).2.1
      _ = C₁ * (Real.log T / T) := by ring
      _ ≤ max C₁ C₂ * (Real.log T / T) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogT
      _ = max C₁ C₂ * Real.log T / T := by ring
  · exact (hmass T hT₁ J).2.2
  · intro s x
    have h := hWb ρ hρ T hT1 J s x
    simpa only [Wsum] using h
  · intro s y
    exact (hQ ρ hρ T hT1 J).1 s y
  · calc ∫ x, ((bL ρ T J 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖bL ρ T J l x‖ ^ 2)
        ≤ C₂ * Real.log T / T ^ 3 := hvar T hT₂ J hJ8
      _ = C₂ * (Real.log T / T ^ 3) := by ring
      _ ≤ max C₁ C₂ * (Real.log T / T ^ 3) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hlogT3
      _ = max C₁ C₂ * Real.log T / T ^ 3 := by ring

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Saw.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.SawAux

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma measurable_saw (α : ℝ) : Measurable (saw α) := by
  unfold saw
  exact continuous_ee.measurable.comp (measurable_const.mul measurable_fract)

lemma norm_saw (α t : ℝ) : ‖saw α t‖ = 1 := norm_ee _

lemma intervalIntegrable_saw_mul_ee (α c : ℝ) :
    IntervalIntegrable (fun t => saw α t * ee (c * t)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ ?_
  · exact ((measurable_saw α).mul
      (continuous_ee.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by simp [norm_saw, norm_ee]

lemma sawCoeff_eq_fourierCoeffOn (α : ℝ) (k : ℤ) :
    sawCoeff α k = fourierCoeffOn zero_lt_one (saw α) k := by
  rw [fourierCoeffOn_eq_integral, show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
  unfold sawCoeff
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [smul_eq_mul]
  rw [fourier_coe_apply, mul_comm]
  unfold ee
  congr 2
  push_cast
  ring

/-- Parseval for the sawtooth phase. -/
lemma hasSum_sq_sawCoeff (α : ℝ) : HasSum (fun k : ℤ => ‖sawCoeff α k‖ ^ 2) 1 := by
  have hL2 : MemLp (saw α) 2 (volume.restrict (Set.Ioc 0 1)) :=
    MemLp.of_bound (measurable_saw α).aestronglyMeasurable 1
      (ae_of_all _ fun t => (norm_saw α t).le)
  have h := hasSum_sq_fourierCoeffOn zero_lt_one hL2
  simp_rw [← sawCoeff_eq_fourierCoeffOn] at h
  convert h using 1
  simp [norm_saw]

lemma sawCoeff_neg_neg (α : ℝ) (k : ℤ) :
    sawCoeff (-α) (-k) = starRingEnd ℂ (sawCoeff α k) := by
  unfold sawCoeff
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun t _ => ?_
  unfold saw
  rw [map_mul, ← ee_neg, ← ee_neg]
  congr 2 <;> push_cast <;> ring

lemma integral_ee_int (n : ℤ) : ∫ t in (0 : ℝ)..1, ee (n * t) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · simp [hn, ee_zero]
  · have hc : (2 * Real.pi * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have h1 : ∀ t : ℝ, ee (n * t) = Complex.exp ((2 * Real.pi * Complex.I * n : ℂ) * t) := by
      intro t; unfold ee; congr 1; push_cast; ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((2 * Real.pi * Complex.I * n : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← h1, mul_one, ee_intCast]
    rw [h2]
    simp

lemma sawCoeff_intCast (m k : ℤ) : sawCoeff m k = if k = m then 1 else 0 := by
  unfold sawCoeff
  have h : ∀ t : ℝ, saw m t * ee (-((k : ℝ) * t)) = ee (((m - k : ℤ) : ℝ) * t) := by
    intro t
    unfold saw
    rw [← Int.self_sub_floor, ← ee_add]
    have : (m : ℝ) * (t - ⌊t⌋) + -(k * t) = ((m - k : ℤ) : ℝ) * t + ((-(m * ⌊t⌋) : ℤ) : ℝ) := by
      push_cast; ring
    rw [this, ee_add_intCast]
  simp_rw [h]
  rw [integral_ee_int]
  by_cases hkm : k = m
  · simp [hkm]
  · have : m - k ≠ 0 := by omega
    simp [hkm, this]

/-- The Fejér kernel as an exponential sum. -/
lemma fejer_complex (R : ℕ) (x : ℝ) :
    (fejer R x : ℂ) = ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * x) := by
  have hcos : ∀ k : ℤ, ((Real.cos (2 * Real.pi * k * x) : ℝ) : ℂ) =
      (ee (k * x) + ee (-(k * x))) / 2 := by
    intro k
    rw [ee_neg, Complex.add_conj, ee_re]
    push_cast
    ring_nf
  have hS : ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (-(k * x)) =
      ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * x) := by
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k _; simp
    · intro k _; simp
    · intro k _; simp [fejerCoeff_neg]
  unfold fejer
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, hcos]
  have hsplit : ∀ k : ℤ, (fejerCoeff R k : ℂ) * ((ee (k * x) + ee (-(k * x))) / 2) =
      (fejerCoeff R k : ℂ) * ee (k * x) / 2 + (fejerCoeff R k : ℂ) * ee (-(k * x)) / 2 := by
    intro k; ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_div, hS]
  ring

lemma fejer_sum_sawCoeff (α : ℝ) (R : ℕ) (u : ℝ) :
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * sawCoeff α k * ee (k * u) =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * saw α t := by
  have h : ∀ t : ℝ, (fejer R (u - t) : ℂ) * saw α t = ∑ k ∈ Finset.Icc (-(R : ℤ)) R,
      ((fejerCoeff R k : ℂ) * ee (k * u)) * (saw α t * ee (-(k : ℝ) * t)) := by
    intro t
    rw [fejer_complex, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (k : ℝ) * (u - t) = k * u + -(k : ℝ) * t by ring, ee_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (intervalIntegrable_saw_mul_ee α _).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  unfold sawCoeff
  simp_rw [neg_mul]
  ring

end ChowlaOpus.SawAux

namespace ChowlaOpus

theorem sawStatement_holds : SawStatement :=
  ⟨SawAux.hasSum_sq_sawCoeff, SawAux.sawCoeff_neg_neg, SawAux.sawCoeff_intCast,
    SawAux.fejer_sum_sawCoeff⟩

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Aux3.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace Aux3Aux

open Finset Filter Topology

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ee_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ee_add, ih]

lemma measurable_saw (α : ℝ) : Measurable (saw α) := by
  show Measurable (fun t => ee (α * Int.fract t))
  exact continuous_ee.measurable.comp (measurable_const.mul measurable_fract)

lemma hasCompactSupport_of_supp {E : Type*} [Zero E] [TopologicalSpace E] (g : ℝ → E) (X : ℝ)
    (h : ∀ x, X < |x| → g x = 0) : HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := -X) (b := X)) (fun x hx => h x (by
    by_contra hcon
    exact hx (abs_le.mp (not_lt.mp hcon))))

/-- The coefficient of the mode `v` (before multiplying by `b (v 0)`). -/
noncomputable def coef (J R : ℕ) (v : Fin (J + 1) → ℤ) : ℂ :=
  ∏ j : Fin J, (fejerCoeff R (v j.succ) : ℂ) * sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ)

/-- The box `[-J,J] × [-R,R]^J`. -/
def box (J R : ℕ) : Finset (Fin (J + 1) → ℤ) :=
  ((Finset.Icc (-(J : ℤ)) J) ×ˢ (Fintype.piFinset fun _ : Fin J => Finset.Icc (-(R : ℤ)) R)).image
    (fun p => (Fin.cons p.1 p.2 : Fin (J + 1) → ℤ))

/-- Structural condition on the modes. -/
def good (J : ℕ) (v : Fin (J + 1) → ℤ) : Prop :=
  (v 0 = 0 → ∀ j : Fin J, v j.succ = 0) ∧
    ∀ j : Fin J, ((j : ℤ) + 1 = |v 0| → v j.succ = (v 0).sign)

instance (J : ℕ) : DecidablePred (good J) := fun v => by unfold good; infer_instance

/-- The frequency set. -/
def Sset (J R : ℕ) : Finset (Fin (J + 1) → ℤ) := (box J R).filter (good J)

/-- Fejér-smoothed sawtooth multiplier. -/
noncomputable def Dfun (R : ℕ) (d u : ℝ) (l : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * sawCoeff ((l : ℝ) / d) k * ee (k * u)

noncomputable def aR (R : ℕ) (α : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(R : ℤ)) R, fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2

noncomputable def AR (J R : ℕ) (l : ℤ) : ℝ := ∏ j : Fin J, aR R ((l : ℝ) / ((j : ℝ) + 1))

lemma mem_box {J R : ℕ} {v : Fin (J + 1) → ℤ} :
    v ∈ box J R ↔ v 0 ∈ Finset.Icc (-(J : ℤ)) J ∧
      ∀ j : Fin J, v j.succ ∈ Finset.Icc (-(R : ℤ)) R := by
  unfold box
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨l, k⟩, hp, rfl⟩
    rw [Finset.mem_product, Fintype.mem_piFinset] at hp
    exact ⟨by simpa using hp.1, fun j => by simpa using hp.2 j⟩
  · rintro ⟨h0, hj⟩
    refine ⟨(v 0, Fin.tail v), ?_, Fin.cons_self_tail v⟩
    rw [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨h0, hj⟩

lemma box_sum {M : Type*} [CommSemiring M] (J R : ℕ) (g : ℤ → M) (h : ℤ → Fin J → ℤ → M) :
    ∑ v ∈ box J R, g (v 0) * ∏ j : Fin J, h (v 0) j (v j.succ) =
      ∑ l ∈ Finset.Icc (-(J : ℤ)) J, g l * ∏ j : Fin J, ∑ k ∈ Finset.Icc (-(R : ℤ)) R, h l j k := by
  unfold box
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Finset.mul_sum, Finset.sum_prod_piFinset]
  · rintro ⟨l, k⟩ _ ⟨l', k'⟩ _ hlk
    obtain ⟨rfl, rfl⟩ := Fin.cons_inj.mp hlk
    rfl

lemma good_of_coef_ne (hS : SawStatement) {J R : ℕ} {v : Fin (J + 1) → ℤ}
    (h : coef J R v ≠ 0) : good J v := by
  have hfac : ∀ j : Fin J, sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ) ≠ 0 := by
    intro j hj
    apply h
    unfold coef
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, mul_zero])
  refine ⟨fun h0 j => ?_, fun j hj => ?_⟩
  · have h1 := hfac j
    rw [h0] at h1
    have h3 := hS.2.2.1 0 (v j.succ)
    simp only [Int.cast_zero, zero_div] at h1 h3
    rw [h3] at h1
    by_contra hne
    exact h1 (by simp [hne])
  · have hv0 : v 0 ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hj
      omega
    have hv0' : (v 0 : ℝ) ≠ 0 := by exact_mod_cast hv0
    have hd : ((v 0 : ℝ) / ((j : ℝ) + 1)) = (((v 0).sign : ℤ) : ℝ) := by
      have hj' : ((j : ℝ) + 1) = |(v 0 : ℝ)| := by exact_mod_cast hj
      rw [hj']
      rcases lt_or_gt_of_ne hv0 with hneg | hpos
      · rw [Int.sign_eq_neg_one_of_neg hneg, abs_of_neg (by exact_mod_cast hneg), div_neg,
          div_self hv0']
        norm_num
      · rw [Int.sign_eq_one_of_pos hpos, abs_of_pos (by exact_mod_cast hpos), div_self hv0']
        norm_num
    have h1 := hfac j
    rw [hd, hS.2.2.1] at h1
    by_contra hne
    exact h1 (by simp [hne])

lemma coef_zero (hS : SawStatement) (J R : ℕ) : coef J R 0 = 1 := by
  unfold coef
  apply Finset.prod_eq_one
  intro j _
  have h3 := hS.2.2.1 0 0
  simp only [Int.cast_zero] at h3
  simp [fejerCoeff_zero, h3]

lemma coef_neg (hS : SawStatement) (J R : ℕ) (v : Fin (J + 1) → ℤ) :
    coef J R (-v) = starRingEnd ℂ (coef J R v) := by
  unfold coef
  rw [map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [Pi.neg_apply]
  rw [map_mul, Complex.conj_ofReal, fejerCoeff_neg, ← hS.2.1]
  rw [show (((-v 0 : ℤ)) : ℝ) / ((j : ℝ) + 1) = -((v 0 : ℝ) / ((j : ℝ) + 1)) by push_cast; ring]

lemma norm_sawCoeff_le (hS : SawStatement) (α : ℝ) (k : ℤ) : ‖sawCoeff α k‖ ≤ 1 := by
  have h := le_hasSum (hS.1 α) k (fun j _ => by positivity)
  have h0 : 0 ≤ ‖sawCoeff α k‖ := norm_nonneg _
  nlinarith

lemma norm_coef_le (hS : SawStatement) (J R : ℕ) (v : Fin (J + 1) → ℤ) : ‖coef J R v‖ ≤ 1 := by
  unfold coef
  rw [norm_prod]
  apply Finset.prod_le_one (fun j _ => norm_nonneg _)
  intro j _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerCoeff_nonneg _ _)]
  have h0 := norm_sawCoeff_le hS ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ)
  have h1 := fejerCoeff_le_one R (v j.succ)
  have h2 := fejerCoeff_nonneg R (v j.succ)
  nlinarith [norm_nonneg (sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ))]

lemma coef_mul_eq_zero (hS : SawStatement) {J R : ℕ} (β : ℤ → ℂ)
    (hβ : ∀ l, (J : ℤ) < |l| → β l = 0) {v : Fin (J + 1) → ℤ} (hv : v ∉ Sset J R) :
    coef J R v * β (v 0) = 0 := by
  unfold Sset at hv
  rw [Finset.mem_filter, not_and_or] at hv
  rcases hv with hv | hv
  · rw [mem_box, not_and_or] at hv
    rcases hv with hv | hv
    · rw [Finset.mem_Icc] at hv
      rw [hβ (v 0) (by rw [lt_abs]; omega), mul_zero]
    · push Not at hv
      obtain ⟨j, hj⟩ := hv
      rw [Finset.mem_Icc] at hj
      have hf : fejerCoeff R (v j.succ) = 0 := fejerCoeff_eq_zero R _ (by rw [lt_abs]; omega)
      unfold coef
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hf]; simp), zero_mul]
  · by_contra hne
    exact hv (good_of_coef_ne hS (left_ne_zero_of_mul hne))

lemma zero_mem_Sset (J R : ℕ) : (0 : Fin (J + 1) → ℤ) ∈ Sset J R := by
  unfold Sset
  rw [Finset.mem_filter, mem_box]
  refine ⟨⟨by simp, fun j => by simp⟩, fun _ j => rfl, fun j hj => ?_⟩
  rw [Pi.zero_apply, abs_zero] at hj
  omega

lemma neg_mem_Sset {J R : ℕ} {v : Fin (J + 1) → ℤ} (hv : v ∈ Sset J R) : -v ∈ Sset J R := by
  unfold Sset at hv ⊢
  rw [Finset.mem_filter, mem_box] at hv ⊢
  obtain ⟨⟨h0, hj⟩, g1, g2⟩ := hv
  simp only [Pi.neg_apply, Finset.mem_Icc] at h0 hj ⊢
  refine ⟨⟨⟨by omega, by omega⟩, fun j => ?_⟩, fun h j => ?_, fun j h => ?_⟩
  · have := hj j
    constructor <;> omega
  · have := g1 (by simpa using h) j
    rw [Pi.neg_apply, this, neg_zero]
  · simp only [Pi.neg_apply, abs_neg] at h ⊢
    rw [g2 j h, Int.sign_neg]

lemma trigEval_expand (hS : SawStatement) (J R : ℕ) (c : ℤ → ℂ) (θ : Fin (J + 1) → ℝ) :
    trigEval (Sset J R) (fun v => coef J R v * c (v 0)) θ =
      ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
        c l * (∏ j : Fin J, Dfun R ((j : ℝ) + 1) (θ j.succ) l) * ee (l * θ 0) := by
  unfold trigEval Sset
  rw [Finset.sum_filter_of_ne (fun v _ hv => good_of_coef_ne hS (R := R) (by
    intro h0; apply hv; simp only [h0, zero_mul]))]
  have key : ∀ v : Fin (J + 1) → ℤ, coef J R v * c (v 0) * ee (∑ i, (v i : ℝ) * θ i) =
      (c (v 0) * ee ((v 0 : ℝ) * θ 0)) * ∏ j : Fin J, ((fejerCoeff R (v j.succ) : ℂ) *
        sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ) * ee ((v j.succ : ℝ) * θ j.succ)) := by
    intro v
    rw [Fin.sum_univ_succ, ee_add, ee_sum, Finset.prod_mul_distrib]
    unfold coef
    ring
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  have hb := box_sum J R (fun l => c l * ee ((l : ℝ) * θ 0))
    (fun l j k => (fejerCoeff R k : ℂ) * sawCoeff ((l : ℝ) / ((j : ℝ) + 1)) k *
      ee ((k : ℝ) * θ j.succ))
  beta_reduce at hb
  rw [hb]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold Dfun
  ring

/-- Multipliers preserving a property of the label profile. -/
def MulPres (P : ℂ → Prop) (I : Finset ℤ) (D : ℤ → ℂ) : Prop :=
  ∀ c : ℤ → ℂ, (∀ s : ℝ, P (∑ l ∈ I, c l * ee (l * s))) →
    ∀ s : ℝ, P (∑ l ∈ I, c l * D l * ee (l * s))

lemma mulPres_prod {P : ℂ → Prop} {I : Finset ℤ} {ι : Type*} (s : Finset ι) (D : ι → ℤ → ℂ)
    (h : ∀ i ∈ s, MulPres P I (D i)) : MulPres P I (fun l => ∏ i ∈ s, D i l) := by
  have := Finset.prod_induction D (MulPres P I) ?_ ?_ h
  · have heq : (fun l => ∏ i ∈ s, D i l) = ∏ i ∈ s, D i := by
      funext l; rw [Finset.prod_apply]
    rw [heq]; exact this
  · intro D₁ D₂ h₁ h₂ c hc s'
    have := h₂ (fun l => c l * D₁ l) (h₁ c hc) s'
    simpa only [Pi.mul_apply, mul_assoc] using this
  · intro c hc s'
    simpa only [Pi.one_apply, mul_one] using hc s'

lemma intInt_fejer_mul_C (hF : FejerStatement) (R : ℕ) (u : ℝ) (h : ℝ → ℂ) (hm : Measurable h)
    (B : ℝ) (hb : ∀ t, ‖h t‖ ≤ B) :
    IntervalIntegrable (fun t => (fejer R (u - t) : ℂ) * h t) volume 0 1 := by
  have h1 : IntervalIntegrable h volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B (ae_of_all _ hb))
  exact h1.continuousOn_mul (Complex.continuous_ofReal.comp
    ((hF.1 R).comp (continuous_const.sub continuous_id))).continuousOn

lemma intInt_fejer_mul_R (hF : FejerStatement) (R : ℕ) (u : ℝ) (h : ℝ → ℝ) (hm : Measurable h)
    (B : ℝ) (hb : ∀ t, ‖h t‖ ≤ B) :
    IntervalIntegrable (fun t => fejer R (u - t) * h t) volume 0 1 := by
  have h1 : IntervalIntegrable h volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B (ae_of_all _ hb))
  exact h1.continuousOn_mul ((hF.1 R).comp (continuous_const.sub continuous_id)).continuousOn

lemma fejer_shift_integral (hF : FejerStatement) (R : ℕ) (u : ℝ) :
    ∫ t in (0 : ℝ)..1, fejer R (u - t) = 1 := by
  rw [intervalIntegral.integral_comp_sub_left (fejer R) u]
  have hper : Function.Periodic (fejer R) 1 := fun t => hF.2.2.1 R t
  have h1 := hper.intervalIntegral_add_eq (u - 1) 0
  rw [sub_add_cancel, zero_add] at h1
  rw [sub_zero, h1]
  exact hF.2.2.2.2.1 R

lemma Dfun_sum_eq (hS : SawStatement) (hF : FejerStatement) (R : ℕ) (d u : ℝ) (I : Finset ℤ)
    (c : ℤ → ℂ) (s : ℝ) :
    ∑ l ∈ I, c l * Dfun R d u l * ee (l * s) =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * ∑ l ∈ I, c l * ee (l * (s + Int.fract t / d)) := by
  have hD : ∀ l : ℤ, Dfun R d u l =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t :=
    fun l => hS.2.2.2 _ R u
  have hint : ∀ l : ℤ, IntervalIntegrable
      (fun t => (fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t) volume 0 1 :=
    fun l => intInt_fejer_mul_C hF R u _ (measurable_saw _) 1 (fun t => (norm_ee _).le)
  calc ∑ l ∈ I, c l * Dfun R d u l * ee (l * s)
      = ∑ l ∈ I, ∫ t in (0 : ℝ)..1,
          (c l * ee (l * s)) * ((fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [intervalIntegral.integral_const_mul, hD]; ring
    _ = ∫ t in (0 : ℝ)..1, ∑ l ∈ I,
          (c l * ee (l * s)) * ((fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t) := by
        rw [intervalIntegral.integral_finsetSum]
        intro l _
        exact (hint l).const_mul _
    _ = _ := by
        congr 1; ext t
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        unfold saw
        rw [show (l : ℝ) * (s + Int.fract t / d) = (l : ℝ) / d * Int.fract t + l * s by ring,
          ee_add]
        ring

def P1 (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1

def P2 (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

lemma avg_P1 (hF : FejerStatement) (R : ℕ) (u : ℝ) (G : ℝ → ℂ) (hG : Measurable G)
    (hP : ∀ t, P1 (G t)) : P1 (∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * G t) := by
  have heq : (fun t => (fejer R (u - t) : ℂ) * G t) =
      fun t => ((fejer R (u - t) * (G t).re : ℝ) : ℂ) := by
    funext t
    apply Complex.ext <;> simp [(hP t).1]
  rw [heq, intervalIntegral.integral_ofReal]
  have hw : ∫ t in (0 : ℝ)..1, fejer R (u - t) = 1 := fejer_shift_integral hF R u
  refine ⟨Complex.ofReal_im _, ?_, ?_⟩
  · rw [Complex.ofReal_re]
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => mul_nonneg (hF.2.1 R _) (hP t).2.1)
  · rw [Complex.ofReal_re]
    refine le_trans ?_ hw.le
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact intInt_fejer_mul_R hF R u _ (Complex.measurable_re.comp hG) 1 (fun t => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hP t).2.1, (hP t).2.2])
    · exact ((hF.1 R).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    · intro t _
      exact mul_le_of_le_one_right (hF.2.1 R _) (hP t).2.2

lemma avg_P2 (hF : FejerStatement) (R : ℕ) (u : ℝ) (G : ℝ → ℂ)
    (hP : ∀ t, P2 (G t)) : P2 (∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * G t) := by
  have heq : (fun t => (fejer R (u - t) : ℂ) * G t) =
      fun t => ((fejer R (u - t) * (G t).re : ℝ) : ℂ) := by
    funext t
    apply Complex.ext <;> simp [(hP t).1]
  rw [heq, intervalIntegral.integral_ofReal]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun t _ => mul_nonneg (hF.2.1 R _) (hP t).2)

lemma measurable_shifted (I : Finset ℤ) (c : ℤ → ℂ) (s d : ℝ) :
    Measurable (fun t : ℝ => ∑ l ∈ I, c l * ee (l * (s + Int.fract t / d))) := by
  have hcont : Continuous (fun s' : ℝ => ∑ l ∈ I, c l * ee (l * s')) :=
    continuous_finsetSum _ (fun l _ => continuous_const.mul
      (continuous_ee.comp (continuous_const.mul continuous_id)))
  exact hcont.measurable.comp (measurable_const.add (measurable_fract.div_const d))

lemma mulPres_Dfun_P1 (hS : SawStatement) (hF : FejerStatement) (R : ℕ) (d u : ℝ)
    (I : Finset ℤ) : MulPres P1 I (Dfun R d u) := by
  intro c hc s
  rw [Dfun_sum_eq hS hF R d u I c s]
  exact avg_P1 hF R u _ (measurable_shifted I c s d) (fun t => hc _)

lemma mulPres_Dfun_P2 (hS : SawStatement) (hF : FejerStatement) (R : ℕ) (d u : ℝ)
    (I : Finset ℤ) : MulPres P2 I (Dfun R d u) := by
  intro c hc s
  rw [Dfun_sum_eq hS hF R d u I c s]
  exact avg_P2 hF R u _ (fun t => hc _)

lemma sum_normsq (hS : SawStatement) (J R : ℕ) (β : ℤ → ℂ) :
    ∑ v ∈ Sset J R, ‖coef J R v * β (v 0)‖ ^ 2 =
      ∑ l ∈ Finset.Icc (-(J : ℤ)) J, AR J R l * ‖β l‖ ^ 2 := by
  unfold Sset
  rw [Finset.sum_filter_of_ne (fun v _ hv => good_of_coef_ne hS (R := R) (by
    intro h0; apply hv; simp only [h0, zero_mul, norm_zero]; ring))]
  have key : ∀ v : Fin (J + 1) → ℤ, ‖coef J R v * β (v 0)‖ ^ 2 =
      ‖β (v 0)‖ ^ 2 * ∏ j : Fin J, (fejerCoeff R (v j.succ) ^ 2 *
        ‖sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ)‖ ^ 2) := by
    intro v
    unfold coef
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow, mul_comm]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (fejerCoeff_nonneg _ _)]
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  have hb := box_sum J R (fun l => ‖β l‖ ^ 2)
    (fun l j k => fejerCoeff R k ^ 2 * ‖sawCoeff ((l : ℝ) / ((j : ℝ) + 1)) k‖ ^ 2)
  beta_reduce at hb
  rw [hb]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold AR aR
  ring

lemma tendsto_fejerCoeff (k : ℤ) : Tendsto (fun R : ℕ => fejerCoeff R k) atTop (𝓝 1) := by
  have h1 : Tendsto (fun R : ℕ => |(k : ℝ)| / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |(k : ℝ)|
    rw [mul_zero] at this
    refine this.congr (fun R => ?_)
    ring
  have h2 : Tendsto (fun R : ℕ => max 0 (1 - |(k : ℝ)| / ((R : ℝ) + 1))) atTop
      (𝓝 (max 0 (1 - 0))) :=
    tendsto_const_nhds.max (tendsto_const_nhds.sub h1)
  have h3 : max (0 : ℝ) (1 - 0) = 1 := by norm_num
  rw [h3] at h2
  exact h2

lemma tendsto_aR (hS : SawStatement) (α : ℝ) : Tendsto (fun R : ℕ => aR R α) atTop (𝓝 1) := by
  have heq : ∀ R : ℕ, aR R α = ∑' k : ℤ, fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2 := by
    intro R
    unfold aR
    rw [tsum_eq_sum (s := Finset.Icc (-(R : ℤ)) R)]
    intro k hk
    rw [Finset.mem_Icc, not_and_or] at hk
    rw [fejerCoeff_eq_zero R k (by rw [lt_abs]; omega)]
    ring
  have hab : ∀ k : ℤ, Tendsto (fun R : ℕ => fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2) atTop
      (𝓝 (‖sawCoeff α k‖ ^ 2)) := by
    intro k
    have := ((tendsto_fejerCoeff k).pow 2).mul_const (‖sawCoeff α k‖ ^ 2)
    rwa [one_pow, one_mul] at this
  have hbound : ∀ᶠ R : ℕ in atTop, ∀ k : ℤ,
      ‖fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2‖ ≤ ‖sawCoeff α k‖ ^ 2 := by
    refine Eventually.of_forall (fun R k => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h0 := fejerCoeff_nonneg R k
    have h1 := fejerCoeff_le_one R k
    have : fejerCoeff R k ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖sawCoeff α k‖]
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun (R : ℕ) (k : ℤ) => fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2)
    (g := fun k => ‖sawCoeff α k‖ ^ 2) (bound := fun k => ‖sawCoeff α k‖ ^ 2)
    (hS.1 α).summable hab hbound
  beta_reduce at h
  rw [(hS.1 α).tsum_eq] at h
  exact h.congr (fun R => (heq R).symm)

lemma tendsto_AR (hS : SawStatement) (J : ℕ) (l : ℤ) :
    Tendsto (fun R : ℕ => AR J R l) atTop (𝓝 1) := by
  unfold AR
  have := tendsto_finsetProd (Finset.univ : Finset (Fin J))
    (fun j _ => tendsto_aR hS ((l : ℝ) / ((j : ℝ) + 1)))
  simpa using this

lemma fourier_const_mul (a : ℂ) (f : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun x => a * f x) y = a * 𝓕 f y := by
  rw [fourier_eq_ee, fourier_eq_ee, ← integral_const_mul]
  congr 1; ext v; ring

lemma nonprop_aux {J R : ℕ} (v w : Fin (J + 1) → ℤ) (hv : v ∈ Sset J R) (hw : w ∈ Sset J R)
    (hv0 : 0 < v 0) (hw0 : 0 < w 0) (h : ∀ i j, v i * w j = v j * w i) : v = w := by
  unfold Sset at hv hw
  rw [Finset.mem_filter, mem_box] at hv hw
  obtain ⟨⟨hv1, -⟩, -, hv2⟩ := hv
  obtain ⟨⟨hw1, -⟩, -, hw2⟩ := hw
  rw [Finset.mem_Icc] at hv1 hw1
  have hJv : (v 0).toNat - 1 < J := by omega
  have hJw : (w 0).toNat - 1 < J := by omega
  obtain ⟨a, ha_def⟩ : ∃ a : Fin J, (a : ℤ) + 1 = v 0 :=
    ⟨⟨(v 0).toNat - 1, hJv⟩, by show (((v 0).toNat - 1 : ℕ) : ℤ) + 1 = v 0; omega⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Fin J, (b : ℤ) + 1 = w 0 :=
    ⟨⟨(w 0).toNat - 1, hJw⟩, by show (((w 0).toNat - 1 : ℕ) : ℤ) + 1 = w 0; omega⟩
  have ha : v a.succ = 1 := by
    rw [hv2 a (by rw [abs_of_pos hv0]; exact ha_def), Int.sign_eq_one_of_pos hv0]
  have hb : w b.succ = 1 := by
    rw [hw2 b (by rw [abs_of_pos hw0]; exact hb_def), Int.sign_eq_one_of_pos hw0]
  have e1 := h 0 a.succ
  have e2 := h 0 b.succ
  rw [ha] at e1
  rw [hb] at e2
  have hwa : 0 < w a.succ := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hprod : v b.succ * w a.succ = 1 := by
    have h4 : v 0 * (v b.succ * w a.succ - 1) = 0 := by linear_combination (v b.succ) * e1 - e2
    rcases mul_eq_zero.mp h4 with h0 | h0
    · omega
    · linarith
  have hwa1 : w a.succ = 1 := Int.eq_one_of_mul_eq_one_left hwa.le hprod
  have hvw0 : w 0 = v 0 := by rw [hwa1] at e1; linarith
  funext i
  have e3 := h 0 i
  rw [hvw0] at e3
  have h5 : v 0 * (w i - v i) = 0 := by linear_combination e3
  rcases mul_eq_zero.mp h5 with h0 | h0
  · omega
  · linarith

end Aux3Aux

open Aux3Aux Finset Filter Topology

theorem profileStatement_holds (h3 : Lemma3Statement) (hS : SawStatement)
    (hF : FejerStatement) (hD : FourierDecayStatement) : ProfileStatement := by
  obtain ⟨C, c, hC, hc, T₀, hT₀⟩ := h3
  refine ⟨C + 1, c, by linarith, hc, max T₀ 3, fun T hT => ?_⟩
  obtain ⟨J, b, hbJ, hbsmooth, hbsupp, hbeven, hbconj, hb0, hfb0, hsum, htsum, hmass, hW, hQ,
    hvar⟩ := hT₀ T (le_trans (le_max_left _ _) hT)
  have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
  have hpos : 0 < Real.log T / T ^ 3 :=
    div_pos (Real.log_pos (by linarith)) (by positivity)
  have hbcs : ∀ l, HasCompactSupport (b l) := fun l => hasCompactSupport_of_supp _ _ (hbsupp l)
  have hbcont : ∀ l, Continuous (b l) := fun l => (hbsmooth l).continuous
  have hMint : ∀ l, Integrable (fun x => ‖b l x‖ ^ 2) := fun l =>
    ((hbcont l).norm.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_supp _ (T ^ 2) (fun x hx => by simp [hbsupp l x hx]))
  have hb0int : Integrable (fun x => (b 0 x).re) :=
    (Complex.continuous_re.comp (hbcont 0)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_supp _ (T ^ 2) (fun x hx => by simp [hbsupp 0 x hx]))
  have hE : Tendsto (fun R : ℕ => ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
      (1 - AR J R l) * ∫ x, ‖b l x‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.Icc (-(J : ℤ)) J) (fun l _ =>
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_AR hS J l)).mul_const
        (∫ x, ‖b l x‖ ^ 2))
    simpa using this
  obtain ⟨R, hR⟩ := (hE.eventually (gt_mem_nhds hpos)).exists
  choose K hK0 hK using fun l => hD (b l) (hbsmooth l) (hbcs l)
  have hcoef0 := coef_zero hS J R
  refine ⟨J, Sset J R, fun v x => coef J R v * b (v 0) x, ∑ l ∈ Finset.Icc (-(J : ℤ)) J, K l,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine
      { zero_mem := zero_mem_Sset J R
        neg_mem := fun v hv => neg_mem_Sset hv
        label_ne := ?_
        nonprop := fun v hv w hw hv0 hw0 h => nonprop_aux v w hv hw hv0 hw0 h
        zero_off := ?_
        smooth := fun v => contDiff_const.mul (hbsmooth (v 0))
        supp := ?_
        even := ?_
        conj := ?_
        decay := ?_
        b0 := ?_
        fourier_b0 := ?_
        range := ?_
        pos := ?_ }
    · intro v hv hne h0
      apply hne
      unfold Sset at hv
      rw [Finset.mem_filter] at hv
      have hz := hv.2.1 h0
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact h0
      · exact hz j
    · intro v hv
      funext x
      exact coef_mul_eq_zero hS (fun l => b l x) (fun l hl => by
        show b l x = 0
        rw [hbJ l hl]; rfl) hv
    · intro v x hx
      show coef J R v * b (v 0) x = 0
      rw [hbsupp _ x hx, mul_zero]
    · intro v x
      show coef J R v * b (v 0) (-x) = coef J R v * b (v 0) x
      rw [hbeven]
    · intro v x
      show coef J R (-v) * b ((-v) 0) x = starRingEnd ℂ (coef J R v * b (v 0) x)
      rw [coef_neg hS, Pi.neg_apply, hbconj, map_mul]
    · intro v y
      show ‖𝓕 (fun x => coef J R v * b (v 0) x) y‖ ≤ _
      rw [fourier_const_mul, norm_mul]
      have h1 := norm_coef_le hS J R v
      have h2 : ‖𝓕 (b (v 0)) y‖ ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J, K l) / (1 + y ^ 2) := by
        by_cases hl : v 0 ∈ Finset.Icc (-(J : ℤ)) J
        · calc ‖𝓕 (b (v 0)) y‖ ≤ K (v 0) / (1 + y ^ 2) := hK _ y
            _ ≤ _ := by
              gcongr
              exact Finset.single_le_sum (fun l _ => hK0 l) hl
        · have hz : b (v 0) = 0 := hbJ _ (by rw [Finset.mem_Icc] at hl; rw [lt_abs]; omega)
          rw [hz]
          have h0 : 𝓕 (0 : ℝ → ℂ) y = 0 := by rw [fourier_eq_ee]; simp
          rw [h0, norm_zero]
          exact div_nonneg (Finset.sum_nonneg (fun l _ => hK0 l)) (by positivity)
      calc ‖coef J R v‖ * ‖𝓕 (b (v 0)) y‖ ≤ 1 * ‖𝓕 (b (v 0)) y‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    · intro x
      simp only [hcoef0, one_mul, Pi.zero_apply]
      exact hb0 x
    · intro y
      simp only [hcoef0, one_mul, Pi.zero_apply]
      exact hfb0 y
    · intro θ x
      show P1 (trigEval (Sset J R) (fun v => coef J R v * (fun l => b l x) (v 0)) θ)
      rw [trigEval_expand hS J R (fun l => b l x) θ]
      exact mulPres_prod _ _ (fun j _ => mulPres_Dfun_P1 hS hF R _ _ _) (fun l => b l x)
        (fun s => hW s x) (θ 0)
    · intro θ y
      have hfun : (fun v : Fin (J + 1) → ℤ => mult (2 * Real.pi * v 0 / T) *
          𝓕 (fun x => coef J R v * b (v 0) x) y) =
          fun v => coef J R v * (fun l : ℤ => mult (2 * Real.pi * l / T) * 𝓕 (b l) y) (v 0) := by
        funext v
        rw [fourier_const_mul]; ring
      show P2 (trigEval (Sset J R) (fun v : Fin (J + 1) → ℤ => mult (2 * Real.pi * v 0 / T) *
          𝓕 (fun x => coef J R v * b (v 0) x) y) θ)
      rw [hfun, trigEval_expand hS J R (fun l : ℤ => mult (2 * Real.pi * l / T) * 𝓕 (b l) y) θ]
      exact mulPres_prod _ _ (fun j _ => mulPres_Dfun_P2 hS hF R _ _ _) _
        (fun s => hQ s y) (θ 0)
  · simpa [hcoef0] using hsum
  · have h6 : C * Real.log T / T ≤ (C + 1) * Real.log T / T := by
      have : 0 < Real.log T / T := div_pos (Real.log_pos (by linarith)) (by linarith)
      rw [mul_div_assoc, mul_div_assoc]; nlinarith
    simpa [hcoef0] using htsum.trans h6
  · simpa [hcoef0] using hmass
  · have hpt : (fun x => (coef J R 0 * b ((0 : Fin (J + 1) → ℤ) 0) x).re -
        ∑ v ∈ Sset J R, ‖coef J R v * b (v 0) x‖ ^ 2) =
        fun x => ((b 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖b l x‖ ^ 2) +
          ∑ l ∈ Finset.Icc (-(J : ℤ)) J, (1 - AR J R l) * ‖b l x‖ ^ 2 := by
      funext x
      rw [sum_normsq hS J R (fun l => b l x), hcoef0, one_mul, Pi.zero_apply]
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
      ring
    show ∫ x, ((coef J R 0 * b ((0 : Fin (J + 1) → ℤ) 0) x).re -
        ∑ v ∈ Sset J R, ‖coef J R v * b (v 0) x‖ ^ 2) ≤ _
    rw [hpt, integral_add, integral_finsetSum]
    · simp_rw [integral_const_mul]
      have h5 : (C + 1) * Real.log T / T ^ 3 = C * Real.log T / T ^ 3 + Real.log T / T ^ 3 := by
        ring
      rw [h5]
      linarith [hvar, hR]
    · intro l _
      exact (hMint l).const_mul _
    · exact hb0int.sub (integrable_finsetSum _ (fun l _ => hMint l))
    · exact integrable_finsetSum _ (fun l _ => (hMint l).const_mul _)

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Poisson.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.PoissonAux

open Filter Asymptotics

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma finite_support_shift (h : ℝ → ℂ) (hcs : HasCompactSupport h) (x : ℝ) :
    (Function.support fun m : ℤ => h (x + m)).Finite := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  apply (Finset.Icc (-⌈R + |x|⌉) ⌈R + |x|⌉).finite_toSet.subset
  intro m hm
  have h1 : x + m ∈ tsupport h := subset_tsupport _ hm
  have h2 := hR h1
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h2
  have h3 : |(m : ℝ)| ≤ ⌈R + |x|⌉ := by
    have h4 : |(m:ℝ)| ≤ |x + m| + |x| := by
      have := abs_add_le (x + m) (-x)
      simp only [add_neg_cancel_comm, abs_neg] at this
      linarith
    linarith [Int.le_ceil (R + |x|)]
  have h5 : |m| ≤ ⌈R + |x|⌉ := by exact_mod_cast h3
  simp only [Finset.coe_Icc, Set.mem_Icc]
  exact abs_le.mp h5

lemma summable_shift (h : ℝ → ℂ) (hcs : HasCompactSupport h) (x : ℝ) :
    Summable fun m : ℤ => h (x + m) := by
  apply summable_of_ne_finset_zero (s := (finite_support_shift h hcs x).toFinset)
  intro m hm
  simpa using hm

lemma isBigO_of_hasCompactSupport (h : ℝ → ℂ) (hcs : HasCompactSupport h) (b : ℝ) :
    h =O[cocompact ℝ] (|·| ^ (-b)) := by
  have : h =ᶠ[cocompact ℝ] 0 := by
    filter_upwards [hcs.isCompact.compl_mem_cocompact] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  exact this.trans_isBigO (isBigO_zero _ _)

lemma summable_inv_one_add_sq_shift (a : ℝ) :
    Summable fun k : ℤ => 1 / (1 + ((k : ℝ) + a) ^ 2) := by
  have hs := (Real.summable_one_div_int_add_rpow a 2).mpr one_lt_two
  apply Summable.of_norm_bounded_eventually hs
  have hfin : {k : ℤ | (k : ℝ) + a = 0}.Subsingleton := by
    intro k hk l hl
    simp only [Set.mem_ofPred_eq] at hk hl
    exact_mod_cast (by linarith : (k : ℝ) = l)
  filter_upwards [hfin.finite.compl_mem_cofinite] with k hk
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hk
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), Real.rpow_two, sq_abs]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

lemma summable_norm_decay (F : ℝ → ℂ) (K : ℝ) (hK : ∀ y, ‖F y‖ ≤ K / (1 + y ^ 2)) (a : ℝ) :
    Summable fun k : ℤ => ‖F (k + a)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hK _) ?_
  exact ((summable_inv_one_add_sq_shift a).mul_left K).congr fun k => mul_one_div _ _

lemma fourier_modulate (f : ℝ → ℂ) (c w : ℝ) :
    𝓕 (fun x => f x * ee (x * c)) w = 𝓕 f (w - c) := by
  rw [fourier_eq_ee, fourier_eq_ee]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [mul_comm (f v), ← mul_assoc, ← ee_add]
  congr 2; ring

lemma poisson_core (h : ℝ → ℂ) (hc : Continuous h) (hcs : HasCompactSupport h)
    (hF : Summable fun n : ℤ => 𝓕 h n) (x : ℝ) :
    ∑' m : ℤ, h (x + m) = ∑' k : ℤ, 𝓕 h k * ee (k * x) := by
  have hb : (1 : ℝ) < 2 := one_lt_two
  have hO := isBigO_of_hasCompactSupport h hcs 2
  have := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc hb hO hF x
  rw [this]
  refine tsum_congr fun k => ?_
  rw [fourier_coe_apply]
  have he : 2 * (π : ℂ) * Complex.I * (k : ℂ) * (x : ℂ) / ((1 : ℝ) : ℂ) =
      2 * π * Complex.I * (((k : ℝ) * x : ℝ) : ℂ) := by
    push_cast; ring
  rw [he]
  rfl

end ChowlaOpus.PoissonAux

namespace ChowlaOpus

open PoissonAux

theorem fourierDecayStatement_holds : FourierDecayStatement := by
  intro f hf hcs
  have hint : ∀ k ≤ 2, Integrable (iteratedDeriv k f) := by
    intro k hk
    have hc : Continuous (iteratedDeriv k f) :=
      hf.continuous_iteratedDeriv k (by exact_mod_cast hk)
    have hs : HasCompactSupport (iteratedDeriv k f) := by
      rw [iteratedDeriv_eq_iterate]
      clear hc hk
      induction k with
      | zero => simpa using hcs
      | succ k ih => rw [Function.iterate_succ_apply']; exact ih.deriv
    exact hc.integrable_of_hasCompactSupport hs
  refine ⟨(∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖, ?_, ?_⟩
  · have h1 : 0 ≤ ∫ v, ‖f v‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ v, ‖iteratedDeriv 2 f v‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  · intro y
    rw [le_div_iff₀ (by positivity), mul_comm]
    have base (g : ℝ → ℂ) : ‖𝓕 g y‖ ≤ ∫ x, ‖g x‖ := by
      rw [Real.fourier_eq]
      refine (norm_integral_le_integral_norm _).trans ?_
      simp only [Circle.norm_smul]
      exact le_rfl
    have hderiv := base (iteratedDeriv 2 f)
    rw [Real.fourier_iteratedDeriv hf (fun k hk => hint k (by exact_mod_cast hk)) le_rfl] at hderiv
    have hCoeff :
        ‖(2 * (π : ℂ) * Complex.I * (y : ℂ)) ^ 2‖ = 4 * π ^ 2 * y ^ 2 := by
      rw [norm_pow]
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow, sq_abs]
      norm_num
    simp only [norm_smul, hCoeff] at hderiv
    have hy : y ^ 2 * ‖𝓕 f y‖ ≤ (4 * π ^ 2)⁻¹ * ∫ x, ‖iteratedDeriv 2 f x‖ := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ (by positivity : 0 < 4 * π ^ 2)).mpr
        (by simpa only [mul_comm, mul_assoc, mul_left_comm] using hderiv)
    calc (1 + y ^ 2) * ‖𝓕 f y‖ = ‖𝓕 f y‖ + y ^ 2 * ‖𝓕 f y‖ := by ring
      _ ≤ _ := add_le_add (base f) hy

theorem plainPoissonStatement_holds : PlainPoissonStatement := by
  intro f K hc hcs hK y
  set g : ℝ → ℂ := fun x => f x * ee (x * (-y)) with hg
  have hgc : Continuous g := hc.mul (continuous_ee.comp (continuous_id.mul continuous_const))
  have hgcs : HasCompactSupport g := hcs.mul_right
  have hFg : ∀ w, 𝓕 g w = 𝓕 f (w + y) := by
    intro w; rw [hg, fourier_modulate, sub_neg_eq_add]
  have hsumF : Summable fun k : ℤ => 𝓕 f (k + y) :=
    (summable_norm_decay _ K hK y).of_norm
  have hgj : ∀ j : ℤ, f j * ee (-((j : ℝ) * y)) = g (0 + j) := by
    intro j; simp [hg]
  refine ⟨?_, ?_⟩
  · simp_rw [hgj]; exact summable_shift g hgcs 0
  · convert hsumF.hasSum using 1
    simp_rw [hgj]
    rw [poisson_core g hgc hgcs (by simpa [hFg] using hsumF) 0]
    simp [hFg, ee_zero]


theorem poissonStatement_holds : PoissonStatement := by
  intro p hp χ n f K hc hcs hK t
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := pow_pos (by exact_mod_cast hp.pos) 2
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℂ, h = fun x => f x * ee (x * ((p : ℝ) ^ 2 * t)) := ⟨_, rfl⟩
  have hhc : Continuous h := by
    rw [hh]; exact hc.mul (continuous_ee.comp (continuous_id.mul continuous_const))
  have hhcs : HasCompactSupport h := by rw [hh]; exact hcs.mul_right
  have hFh : ∀ w, 𝓕 h w = 𝓕 f (w - (p : ℝ) ^ 2 * t) := fun w => by rw [hh, fourier_modulate]
  have hsumF : Summable fun k : ℤ => ‖𝓕 h k‖ := by
    refine (summable_norm_decay _ K hK (-((p : ℝ) ^ 2 * t))).congr fun k => ?_
    rw [hFh, sub_eq_add_neg]
  set R := (Finset.range (p ^ 2)).filter (fun r => Nat.Coprime r p) with hR
  have hterm_sum : ∀ x : ℝ, Summable fun k : ℤ => 𝓕 h k * ee (k * x) := by
    intro x
    refine Summable.of_norm_bounded hsumF (fun k => ?_)
    rw [norm_mul, norm_ee, mul_one]
  have key : ∀ k : ℤ, 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k =
      ∑ r ∈ R, (χ (r : ZMod (p ^ 2))) ^ n * (𝓕 h k * ee (k * ((r : ℝ) / (p : ℝ) ^ 2))) := by
    intro k
    rw [rowSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hFh, mul_div_assoc]; ring
  have hsumk : Summable fun k : ℤ => 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k := by
    simp_rw [key]
    exact summable_sum fun r _ => (hterm_sum _).mul_left _
  refine ⟨hsumk, ?_⟩
  have hRHS : ∑' k : ℤ, 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k =
      ∑ r ∈ R, (χ (r : ZMod (p ^ 2))) ^ n * ∑' m : ℤ, h ((r : ℝ) / (p : ℝ) ^ 2 + m) := by
    simp_rw [key]
    rw [Summable.tsum_finsetSum fun r _ => (hterm_sum _).mul_left _]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [tsum_mul_left, poisson_core h hhc hhcs hsumF.of_norm]
  rw [hRHS]
  set a : ℤ → ℂ := fun d => (if (p : ℤ) ∣ d then 0 else
          f ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ n) * ee (d * t) with ha
  set b : ℕ → ℤ → ℂ := fun r d => if d % ((p : ℤ) ^ 2) = r then a d else 0 with hb
  have hab : ∀ d, ∑ r ∈ R, b r d = a d := by
    intro d
    simp only [hb]
    obtain ⟨r0, hr0⟩ : ∃ r0 : ℕ, (r0 : ℤ) = d % (p : ℤ) ^ 2 :=
      ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ hp2.ne')⟩
    have hiff : ∀ r : ℕ, (d % (p : ℤ) ^ 2 = (r : ℤ)) ↔ r0 = r := by
      intro r; rw [← hr0, Nat.cast_inj]
    simp_rw [hiff]
    rw [Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · have hlt : r0 < p ^ 2 := by
        have := Int.emod_lt_of_pos d hp2
        rw [← hr0] at this
        exact_mod_cast this
      have hnc : ¬ Nat.Coprime r0 p := by
        intro hc'
        exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc'⟩)
      have hpr : p ∣ r0 := by
        by_contra hnd
        exact hnc (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
      have hpd : (p : ℤ) ∣ d := by
        have h1 : (p : ℤ) ∣ d % (p : ℤ) ^ 2 := by
          rw [← hr0]; exact Int.natCast_dvd_natCast.mpr hpr
        have h2 : (p : ℤ) ∣ (p : ℤ) ^ 2 * (d / (p : ℤ) ^ 2) :=
          Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _
        have := dvd_add h1 h2
        rwa [Int.emod_add_mul_ediv] at this
      simp [ha, hpd]
  have hbr : ∀ r ∈ R, HasSum (b r)
      ((χ (r : ZMod (p ^ 2))) ^ n * ∑' m : ℤ, h ((r : ℝ) / (p : ℝ) ^ 2 + m)) := by
    intro r hr
    have hrR := Finset.mem_filter.mp hr
    have hrlt : r < p ^ 2 := Finset.mem_range.mp hrR.1
    have hcop : Nat.Coprime r p := hrR.2
    have hginj : Function.Injective (fun m : ℤ => (r : ℤ) + (p : ℤ) ^ 2 * m) := by
      intro m1 m2 hm
      simp only at hm
      exact mul_left_cancel₀ hp2.ne' (add_left_cancel hm)
    have hout : ∀ d, d ∉ Set.range (fun m : ℤ => (r : ℤ) + (p : ℤ) ^ 2 * m) → b r d = 0 := by
      intro d hd
      simp only [hb]
      rw [if_neg]
      intro hdr
      apply hd
      refine ⟨d / (p : ℤ) ^ 2, ?_⟩
      simp only
      rw [← hdr]; exact Int.emod_add_mul_ediv d _
    rw [← hginj.hasSum_iff hout]
    have hcomp : b r ∘ (fun m : ℤ => (r : ℤ) + (p : ℤ) ^ 2 * m) =
        fun m : ℤ => (χ (r : ZMod (p ^ 2))) ^ n * h ((r : ℝ) / (p : ℝ) ^ 2 + m) := by
      funext m
      simp only [Function.comp, hb]
      have hmod : ((r : ℤ) + (p : ℤ) ^ 2 * m) % (p : ℤ) ^ 2 = r := by
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hrlt)
      rw [if_pos hmod]
      have hndvd : ¬ (p : ℤ) ∣ (r : ℤ) + (p : ℤ) ^ 2 * m := by
        intro hdv
        have h2 : (p : ℤ) ∣ (p : ℤ) ^ 2 * m := Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _
        have h3 : (p : ℤ) ∣ (r : ℤ) := (dvd_add_left h2).mp hdv
        have h4 : p ∣ r := Int.natCast_dvd_natCast.mp h3
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hcop) h4
      simp only [ha, if_neg hndvd]
      have hchi : χ ((((r : ℤ) + (p : ℤ) ^ 2 * m : ℤ)) : ZMod (p ^ 2)) = χ (r : ZMod (p ^ 2)) := by
        congr 1
        have hz : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by exact_mod_cast ZMod.natCast_self (p ^ 2)
        push_cast
        rw [hz]; ring
      rw [hchi, hh]
      have e1 : (((r : ℤ) + (p : ℤ) ^ 2 * m : ℤ) : ℝ) / (p : ℝ) ^ 2 = (r : ℝ) / (p : ℝ) ^ 2 + m := by
        push_cast; field_simp
      have e2 : (((r : ℤ) + (p : ℤ) ^ 2 * m : ℤ) : ℝ) * t =
          ((r : ℝ) / (p : ℝ) ^ 2 + m) * ((p : ℝ) ^ 2 * t) := by
        push_cast; field_simp
      rw [e1, e2]; ring
    rw [hcomp]
    exact ((summable_shift h hhcs _).hasSum).mul_left _
  have hfin := hasSum_sum hbr
  convert hfin using 1
  funext d
  exact (hab d).symm

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Gauss.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.GaussAux

open Finset ChowlaOpus

/- ### Exponential sums -/

lemma ee_eq_one_iff_int (x : ℝ) : ee x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ h
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

lemma ee_geom_sum (N : ℕ) (hN : 0 < N) (k : ℤ) :
    ∑ r ∈ range N, ee ((k : ℝ) * (r : ℝ) / (N : ℝ)) = if (N : ℤ) ∣ k then (N : ℂ) else 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hterm : ∀ r : ℕ, ee ((k : ℝ) * (r : ℝ) / (N : ℝ)) = ee ((k : ℝ) / N) ^ r := by
    intro r
    rw [← zpow_natCast, ← ee_mul_intCast]
    congr 1; push_cast; ring
  simp_rw [hterm]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have : ee ((((N : ℤ) * m : ℤ) : ℝ) / N) = 1 := by
      rw [show (((N : ℤ) * m : ℤ) : ℝ) / N = (m : ℝ) by push_cast; field_simp]
      exact ee_intCast m
    rw [this]
    simp
  · have hne : ee ((k : ℝ) / N) ≠ 1 := by
      intro h1
      rw [ee_eq_one_iff_int] at h1
      obtain ⟨m, hm⟩ := h1
      apply h
      refine ⟨m, ?_⟩
      have : (k : ℝ) = N * m := by
        rw [div_eq_iff hN'] at hm; rw [hm]; ring
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have : ee ((k : ℝ) / N) ^ N = 1 := by
      rw [← zpow_natCast, ← ee_mul_intCast]
      rw [show (k : ℝ) / N * ((N : ℤ) : ℝ) = (k : ℝ) by push_cast; field_simp]
      exact ee_intCast k
    rw [this, sub_self, zero_div]

variable {p : ℕ} [hp : Fact p.Prime]

/- ### The additive character mod `p²` -/

/-- The standard additive character `x ↦ e(x/p²)` on `ZMod (p²)`. -/
noncomputable def psi (p : ℕ) (x : ZMod (p ^ 2)) : ℂ := ee ((x.val : ℝ) / (p : ℝ) ^ 2)

lemma psi_intCast (m : ℤ) : psi p (m : ZMod (p ^ 2)) = ee ((m : ℝ) / (p : ℝ) ^ 2) := by
  unfold psi
  have hp0 : ((p : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have h1 : (((m : ZMod (p ^ 2)).val : ℝ)) = ((m % ((p ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, ZMod.val_intCast]
  have h2 : (m : ℝ) = ((m % ((p ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) +
      (p : ℝ) ^ 2 * ((m / ((p ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) := by
    have := Int.emod_add_mul_ediv m ((p ^ 2 : ℕ) : ℤ)
    have h' : ((m % ((p ^ 2 : ℕ) : ℤ) + ((p ^ 2 : ℕ) : ℤ) * (m / ((p ^ 2 : ℕ) : ℤ)) : ℤ) : ℝ) =
        (m : ℝ) := by rw [this]
    push_cast at h' ⊢
    linarith
  rw [h1]
  conv_rhs => rw [h2, add_div, mul_div_cancel_left₀ _ hp0, ee_add_intCast]

lemma psi_add (x y : ZMod (p ^ 2)) : psi p (x + y) = psi p x * psi p y := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  rw [← Int.cast_add, psi_intCast, psi_intCast, psi_intCast, ← ee_add]
  congr 1; push_cast; ring

/- ### Values of `χ` -/

lemma norm_chi_of_isUnit (χ : MulChar (ZMod (p ^ 2)) ℂ) {x : ZMod (p ^ 2)} (hx : IsUnit x) :
    ‖χ x‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 : (χ u) ^ (p ^ 2).totient = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  have h2 : ‖χ u‖ ^ (p ^ 2).totient = 1 := by rw [← norm_pow, h1, norm_one]
  have hpos : (p ^ 2).totient ≠ 0 := (Nat.totient_pos.mpr (pow_pos hp.out.pos 2)).ne'
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).mp h2

lemma isUnit_intCast_of_not_dvd {n : ℤ} (h : ¬ (p : ℤ) ∣ n) : IsUnit (n : ZMod (p ^ 2)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  push_cast
  exact ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.out)).mpr h).pow_left

omit hp in
lemma chi_neg (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (x : ZMod (p ^ 2)) :
    χ (-x) = χ x := by
  rw [neg_eq_neg_one_mul, map_mul, hχ.1, one_mul]

omit hp in
lemma chi_one_add (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (j : ℕ) :
    χ (1 + (p : ZMod (p ^ 2)) * j) = ee ((j : ℝ) / p) := by
  have := hχ.2 j
  push_cast at this
  exact this

omit hp in
lemma isUnit_one_add (j : ℕ) : IsUnit (1 + (p : ZMod (p ^ 2)) * j) := by
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  refine IsUnit.of_mul_eq_one (1 - (p : ZMod (p ^ 2)) * j) ?_
  linear_combination (-(j : ZMod (p ^ 2)) ^ 2) * hp2

lemma one_add_injOn : Set.InjOn (fun j : ℕ => 1 + (p : ZMod (p ^ 2)) * j) (range p) := by
  intro a ha b hb h
  have ha' : a < p := Finset.mem_range.mp (Finset.mem_coe.mp ha)
  have hb' : b < p := Finset.mem_range.mp (Finset.mem_coe.mp hb)
  have h' : ((p * a : ℕ) : ZMod (p ^ 2)) = ((p * b : ℕ) : ZMod (p ^ 2)) := by
    push_cast; exact add_left_cancel h
  have hpos := hp.out.pos
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by nlinarith),
    Nat.mod_eq_of_lt (by nlinarith)] at h'
  exact Nat.eq_of_mul_eq_mul_left hpos h'

/- ### Row sums as sums over `ZMod (p²)` -/

lemma sum_range_eq_sum_zmod (f : ZMod (p ^ 2) → ℂ) :
    ∑ r ∈ range (p ^ 2), f (r : ZMod (p ^ 2)) = ∑ x : ZMod (p ^ 2), f x := by
  refine Finset.sum_nbij' (fun r => (r : ZMod (p ^ 2))) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intros; exact mem_univ _
  · intro x _; exact mem_range.mpr (ZMod.val_lt x)
  · intro r hr; exact ZMod.val_cast_of_lt (mem_range.mp hr)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intros; rfl

lemma rowSum_eq (χ : MulChar (ZMod (p ^ 2)) ℂ) (n k : ℤ) (hn : n ≠ 0) :
    rowSum p χ n k = ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) := by
  unfold rowSum
  rw [Finset.sum_filter_of_ne, ← sum_range_eq_sum_zmod]
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    rw [show ((k : ZMod (p ^ 2)) * (r : ZMod (p ^ 2))) = ((k * (r : ℤ) : ℤ) : ZMod (p ^ 2)) by
      push_cast; ring, psi_intCast]
    push_cast
    ring_nf
  · intro r _ hne
    by_contra hc
    apply hne
    have : ¬ IsUnit (r : ZMod (p ^ 2)) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff two_pos]; exact hc
    rw [MulChar.map_nonunit χ this, zero_zpow n hn, zero_mul]

/-- Averaging over the kernel `{1 + p j}` of reduction mod `p`. -/
lemma averaged (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n k : ℤ) :
    (p : ℂ) * ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) *
        (if (p : ℤ) ∣ n + k * (x.val : ℤ) then (p : ℂ) else 0) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hshift : ∀ (j : ℕ) (x : ZMod (p ^ 2)),
      χ (x * (1 + (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)))) ^ n *
          psi p ((k : ZMod (p ^ 2)) * (x * (1 + (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))))) =
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) *
          ee (((n + k * (x.val : ℤ) : ℤ) : ℝ) * (j : ℝ) / (p : ℝ)) := by
    intro j x
    rw [map_mul, chi_one_add χ hχ j, mul_zpow, ← ee_mul_intCast]
    have hxv : ((x.val : ℤ) : ZMod (p ^ 2)) = x := by simp
    have : (k : ZMod (p ^ 2)) * (x * (1 + (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)))) =
        (k : ZMod (p ^ 2)) * x + ((k * (x.val : ℤ) * p * j : ℤ) : ZMod (p ^ 2)) := by
      rw [Int.cast_mul, Int.cast_mul, Int.cast_mul, hxv]; push_cast; ring
    rw [this, psi_add, psi_intCast]
    rw [show ((n + k * (x.val : ℤ) : ℤ) : ℝ) * (j : ℝ) / (p : ℝ) =
        (j : ℝ) / p * (n : ℝ) + ((k * (x.val : ℤ) * p * j : ℤ) : ℝ) / (p : ℝ) ^ 2 by
      push_cast; field_simp]
    rw [ee_add]
    ring
  have hsum : ∀ j ∈ range p, ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ x : ZMod (p ^ 2), χ (x * (1 + (p : ZMod (p ^ 2)) * j)) ^ n *
        psi p ((k : ZMod (p ^ 2)) * (x * (1 + (p : ZMod (p ^ 2)) * j))) := by
    intro j _
    exact (Equiv.sum_comp (Units.mulRight (isUnit_one_add (p := p) j).unit)
      (fun x => χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x))).symm
  have hpS : (p : ℂ) * ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ j ∈ range p, ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) := by
    rw [sum_const, card_range, nsmul_eq_mul]
  rw [hpS, sum_congr rfl hsum, sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  rw [sum_congr rfl (fun j _ => hshift j x), ← mul_sum, ee_geom_sum p hp.out.pos]

lemma cond_iff (n k : ℤ) (hn : ¬ (p : ℤ) ∣ n) (u : ZMod (p ^ 2))
    (hu : (k : ZMod (p ^ 2)) * u = -(n : ZMod (p ^ 2))) (y : ZMod (p ^ 2)) :
    (p : ℤ) ∣ n + k * ((u * y).val : ℤ) ↔
      y ∈ (range p).image (fun j : ℕ => 1 + (p : ZMod (p ^ 2)) * j) := by
  set red : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
    with hred
  have hval : ∀ x : ZMod (p ^ 2), ((x.val : ℤ) : ZMod p) = red x := by
    intro x
    rw [hred, ZMod.castHom_apply, ZMod.cast_eq_val, Int.cast_natCast]
  have hku : (k : ZMod p) * red u = -(n : ZMod p) := by
    rw [← map_intCast red k, ← map_mul, hu, map_neg, map_intCast]
  have hn' : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have step1 : (p : ℤ) ∣ n + k * ((u * y).val : ℤ) ↔ red y = 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_mul, hval, map_mul]
    have key : (n : ZMod p) + (k : ZMod p) * (red u * red y) = (n : ZMod p) * (1 - red y) := by
      linear_combination (red y) * hku
    rw [key, mul_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hn'
      · exact h.symm
    · intro h; right; exact h.symm
  rw [step1, mem_image]
  constructor
  · intro hy
    have h1 : y.val % p = 1 := by
      have : ((y.val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        have := hval y
        rw [Int.cast_natCast] at this
        rw [this, hy, Nat.cast_one]
      rw [ZMod.natCast_eq_natCast_iff'] at this
      rw [this, Nat.mod_eq_of_lt hp.out.one_lt]
    refine ⟨y.val / p, ?_, ?_⟩
    · rw [mem_range, Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_two]
      exact ZMod.val_lt y
    · have := Nat.mod_add_div y.val p
      rw [h1] at this
      conv_rhs => rw [← ZMod.natCast_zmod_val y, ← this]
      push_cast
      ring
  · rintro ⟨j, _, rfl⟩
    rw [map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

lemma rowSum_a (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n k : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) (hk : ¬ (p : ℤ) ∣ k) :
    rowSum p χ n k = p * ((χ (k : ZMod (p ^ 2)))⁻¹) ^ n * gaussPhase p χ n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hav := averaged χ hχ n k
  rw [rowSum_eq χ n k hn0]
  have h1 : ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ x : ZMod (p ^ 2), if (p : ℤ) ∣ n + k * (x.val : ℤ) then
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) else 0 := by
    apply mul_left_cancel₀ hpne
    rw [hav, mul_sum]
    refine sum_congr rfl (fun x _ => ?_)
    split_ifs <;> ring
  have hku : IsUnit (k : ZMod (p ^ 2)) := isUnit_intCast_of_not_dvd hk
  have hnu : IsUnit (n : ZMod (p ^ 2)) := isUnit_intCast_of_not_dvd hn
  have hkk : (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hku
  have hkinv : IsUnit ((k : ZMod (p ^ 2))⁻¹) := IsUnit.of_mul_eq_one_right _ hkk
  obtain ⟨u, hu_def⟩ : ∃ u : ZMod (p ^ 2), u = -(n : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ :=
    ⟨_, rfl⟩
  have hku' : (k : ZMod (p ^ 2)) * u = -(n : ZMod (p ^ 2)) := by
    rw [hu_def]; linear_combination (-(n : ZMod (p ^ 2))) * hkk
  have hu : IsUnit u := by rw [hu_def]; exact hnu.neg.mul hkinv
  have hχk : χ (k : ZMod (p ^ 2)) ≠ 0 := by
    intro h
    have := norm_chi_of_isUnit χ hku
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hχu : χ u = χ (n : ZMod (p ^ 2)) * (χ (k : ZMod (p ^ 2)))⁻¹ := by
    have : χ (k : ZMod (p ^ 2)) * χ u = χ (n : ZMod (p ^ 2)) := by
      rw [← map_mul, hku', chi_neg χ hχ]
    rw [eq_mul_inv_iff_mul_eq₀ hχk, mul_comm]
    exact this
  have h2 : (∑ x : ZMod (p ^ 2), if (p : ℤ) ∣ n + k * (x.val : ℤ) then
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) else 0) =
      ∑ y : ZMod (p ^ 2), if (p : ℤ) ∣ n + k * ((u * y).val : ℤ) then
        χ (u * y) ^ n * psi p ((k : ZMod (p ^ 2)) * (u * y)) else 0 :=
    (Equiv.sum_comp (Units.mulLeft hu.unit) (fun x => if (p : ℤ) ∣ n + k * (x.val : ℤ) then
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) else 0)).symm
  rw [h1, h2, ← sum_filter]
  have hfilt : univ.filter (fun y : ZMod (p ^ 2) => (p : ℤ) ∣ n + k * ((u * y).val : ℤ)) =
      (range p).image (fun j : ℕ => 1 + (p : ZMod (p ^ 2)) * j) := by
    ext y
    rw [mem_filter, cond_iff n k hn u hku' y]
    simp only [mem_univ, true_and]
  rw [hfilt, sum_image one_add_injOn]
  have hterm : ∀ j ∈ range p, χ (u * (1 + (p : ZMod (p ^ 2)) * j)) ^ n *
      psi p ((k : ZMod (p ^ 2)) * (u * (1 + (p : ZMod (p ^ 2)) * j))) =
      χ (n : ZMod (p ^ 2)) ^ n * (χ (k : ZMod (p ^ 2)))⁻¹ ^ n * ee (-(n : ℝ) / (p : ℝ) ^ 2) := by
    intro j _
    rw [map_mul, chi_one_add χ hχ j, hχu, mul_zpow, mul_zpow, ← ee_mul_intCast]
    rw [show (k : ZMod (p ^ 2)) * (u * (1 + (p : ZMod (p ^ 2)) * j)) =
        ((-n - n * p * j : ℤ) : ZMod (p ^ 2)) by rw [← mul_assoc, hku']; push_cast; ring]
    rw [psi_intCast]
    have he : ee ((j : ℝ) / p * (n : ℝ)) * ee (((-n - n * p * j : ℤ) : ℝ) / (p : ℝ) ^ 2) =
        ee (-(n : ℝ) / (p : ℝ) ^ 2) := by
      rw [← ee_add]; congr 1; push_cast; field_simp; ring
    linear_combination (χ (n : ZMod (p ^ 2)) ^ n * (χ (k : ZMod (p ^ 2)))⁻¹ ^ n) * he
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
  unfold gaussPhase
  ring

lemma rowSum_b (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n k : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) (hk : (p : ℤ) ∣ k) : rowSum p χ n k = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hav := averaged χ hχ n k
  have hnd : ∀ x : ZMod (p ^ 2), ¬ (p : ℤ) ∣ n + k * (x.val : ℤ) := by
    intro x h
    exact hn ((dvd_add_left (dvd_mul_of_dvd_left hk _)).mp h)
  have h0 : ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) *
      (if (p : ℤ) ∣ n + k * (x.val : ℤ) then (p : ℂ) else 0) = 0 :=
    sum_eq_zero (fun x _ => by rw [if_neg (hnd x), mul_zero])
  rw [h0] at hav
  rw [rowSum_eq χ n k hn0]
  exact (mul_eq_zero.mp hav).resolve_left hpne

lemma rowSum_c (χ : MulChar (ZMod (p ^ 2)) ℂ) (k : ℤ) :
    rowSum p χ 0 k =
      (if (p : ℤ) ^ 2 ∣ k then ((p : ℂ) ^ 2) else 0) - (if (p : ℤ) ∣ k then (p : ℂ) else 0) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  unfold rowSum
  simp only [zpow_zero, one_mul]
  have hfull : ∑ r ∈ range (p ^ 2), ee ((k : ℝ) * (r : ℝ) / (p : ℝ) ^ 2) =
      if (p : ℤ) ^ 2 ∣ k then (p : ℂ) ^ 2 else 0 := by
    have := ee_geom_sum (p ^ 2) (pow_pos hp.out.pos 2) k
    push_cast at this
    exact this
  have hnot : (range (p ^ 2)).filter (fun r => ¬ Nat.Coprime r p) =
      (range p).image (fun m => p * m) := by
    ext r
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hr, hc⟩
      have hd : p ∣ r := by
        by_contra hd
        exact hc (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd))
      obtain ⟨m, rfl⟩ := hd
      refine ⟨m, ?_, rfl⟩
      by_contra hm
      have : p * p ≤ p * m := Nat.mul_le_mul_left p (not_lt.mp hm)
      rw [← pow_two] at this
      exact absurd hr (not_lt.mpr this)
    · rintro ⟨m, hm, rfl⟩
      have hpos := hp.out.pos
      refine ⟨by nlinarith, ?_⟩
      intro hc
      have h1 : Nat.Coprime p p := Nat.Coprime.coprime_dvd_left (dvd_mul_right p m) hc
      rw [Nat.coprime_self] at h1
      exact hp.out.one_lt.ne' h1
  have hpart : ∑ r ∈ (range (p ^ 2)).filter (fun r => ¬ Nat.Coprime r p),
      ee ((k : ℝ) * (r : ℝ) / (p : ℝ) ^ 2) = if (p : ℤ) ∣ k then (p : ℂ) else 0 := by
    rw [hnot, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.out.pos h),
      ← ee_geom_sum p hp.out.pos k]
    refine sum_congr rfl (fun m _ => ?_)
    congr 1
    push_cast
    field_simp
  rw [← hfull, ← hpart,
    ← Finset.sum_filter_add_sum_filter_not (range (p ^ 2)) (fun r => Nat.Coprime r p)]
  ring

lemma gauss_d (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    ‖gaussPhase p χ n‖ = 1 := by
  unfold gaussPhase
  rw [norm_mul, norm_ee, norm_zpow, norm_chi_of_isUnit χ (isUnit_intCast_of_not_dvd hn),
    one_zpow, one_mul]

lemma conj_chi_zpow (χ : MulChar (ZMod (p ^ 2)) ℂ) (x : ZMod (p ^ 2)) (n : ℤ) :
    starRingEnd ℂ (χ x ^ n) = χ x ^ (-n) := by
  by_cases hx : IsUnit x
  · have h1 := norm_chi_of_isUnit χ hx
    have hconj : starRingEnd ℂ (χ x) = (χ x)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
    rw [map_zpow₀, hconj, inv_zpow']
  · rw [MulChar.map_nonunit χ hx, map_zpow₀, map_zero]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [zero_zpow _ hn, zero_zpow _ (neg_ne_zero.mpr hn)]

lemma gauss_e (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n : ℤ) :
    gaussPhase p χ (-n) = starRingEnd ℂ (gaussPhase p χ n) := by
  unfold gaussPhase
  rw [map_mul, ← ee_neg, conj_chi_zpow]
  simp only [Int.cast_neg]
  rw [chi_neg χ hχ]
  congr 2
  ring

end ChowlaOpus.GaussAux

namespace ChowlaOpus

open GaussAux in
theorem rowSumStatement_holds : RowSumStatement := by
  intro p hp _ χ hχ
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨fun n k hn hk => rowSum_a χ hχ n k hn hk, fun n k hn hk => rowSum_b χ hχ n k hn hk,
    fun k => rowSum_c χ k, fun n hn => gauss_d χ n hn, fun n => gauss_e χ hχ n⟩

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/KChar.lean. -/
section

/-
# The kernel character mod `p²`

For an odd prime `p` we construct the Fermat-quotient character
`χ(u) = e((1 - u^(p-1)) / p²)` on `(ZMod (p²))ˣ`. Since `u^(p-1) ≡ 1 (mod p)`, the product
`(u^(p-1) - 1)(v^(p-1) - 1)` vanishes in `ZMod (p²)`, which makes `χ` multiplicative, and
`(1 + pt)^(p-1) = 1 - pt` in `ZMod (p²)` gives `χ(1 + pt) = e(t/p)`.
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.KCharAux

lemma one_add_pow {R : Type*} [CommRing R] (x : R) (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (n : R) * hx

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
lemma p_sq_eq_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

lemma exists_mul_of_unit (u : (ZMod (p ^ 2))ˣ) :
    ∃ y : ℕ, (u : ZMod (p ^ 2)) ^ (p - 1) - 1 = (p : ZMod (p ^ 2)) * y := by
  set w : ZMod (p ^ 2) := (u : ZMod (p ^ 2)) ^ (p - 1) - 1 with hw
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have hu : ((ZMod.castHom hdvd (ZMod p)) (u : ZMod (p ^ 2))) ≠ 0 :=
    ((u.isUnit.map (ZMod.castHom hdvd (ZMod p)))).ne_zero
  have h0 : ZMod.castHom hdvd (ZMod p) w = 0 := by
    rw [hw, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one hu, sub_self]
  have h1 : ((w.val : ℕ) : ZMod p) = 0 := by
    rw [← h0, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, ?_⟩
  rw [← ZMod.natCast_zmod_val w, hy]
  push_cast; ring

lemma prod_eq_zero (u v : (ZMod (p ^ 2))ˣ) :
    ((u : ZMod (p ^ 2)) ^ (p - 1) - 1) * ((v : ZMod (p ^ 2)) ^ (p - 1) - 1) = 0 := by
  obtain ⟨a, ha⟩ := exists_mul_of_unit p u
  obtain ⟨b, hb⟩ := exists_mul_of_unit p v
  rw [ha, hb]
  linear_combination ((a : ZMod (p ^ 2)) * b) * p_sq_eq_zero p

/-- `u ↦ e((1 - u^(p-1)) / p²)` as a homomorphism of unit groups. -/
noncomputable def unitHom : (ZMod (p ^ 2))ˣ →* ℂˣ where
  toFun u := Units.mk0 (ZMod.stdAddChar (1 - (u : ZMod (p ^ 2)) ^ (p - 1)))
    (by rw [ZMod.stdAddChar_apply]; exact Circle.coe_ne_zero _)
  map_one' := by ext; simp
  map_mul' u v := by
    ext
    simp only [Units.val_mul, Units.val_mk0, mul_pow, ← AddChar.map_add_eq_mul]
    congr 1
    linear_combination -(prod_eq_zero p u v)

/-- The kernel character mod `p²`. -/
noncomputable def chi : MulChar (ZMod (p ^ 2)) ℂ := MulChar.ofUnitHom (unitHom p)

lemma chi_unit (u : (ZMod (p ^ 2))ˣ) :
    chi p (u : ZMod (p ^ 2)) = ZMod.stdAddChar (1 - (u : ZMod (p ^ 2)) ^ (p - 1)) := by
  rw [chi, MulChar.ofUnitHom_coe]
  rfl

lemma chi_one_add (t : ℤ) :
    chi p (((1 + (p : ℤ) * t : ℤ)) : ZMod (p ^ 2)) = ee ((t : ℝ) / p) := by
  set x : ZMod (p ^ 2) := (p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2)) with hx
  have hx2 : x ^ 2 = 0 := by
    rw [hx, mul_pow, p_sq_eq_zero, zero_mul]
  have hcast : (((1 + (p : ℤ) * t : ℤ)) : ZMod (p ^ 2)) = 1 + x := by
    rw [hx]; push_cast; ring
  let u : (ZMod (p ^ 2))ˣ :=
    { val := 1 + x, inv := 1 - x,
      val_inv := by linear_combination -hx2,
      inv_val := by linear_combination -hx2 }
  have hu : (u : ZMod (p ^ 2)) = 1 + x := rfl
  rw [hcast, ← hu, chi_unit, hu, one_add_pow x hx2]
  have hp1 : 1 ≤ p := hp.out.one_le
  have h1 : 1 - (1 + ((p - 1 : ℕ) : ZMod (p ^ 2)) * x) = (((p : ℤ) * t : ℤ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_sub hp1, hx]
    push_cast
    linear_combination -(t : ZMod (p ^ 2)) * p_sq_eq_zero p
  rw [h1, ZMod.stdAddChar_coe, ee]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  congr 1
  push_cast
  field_simp

lemma chi_neg_one (hp2 : p ≠ 2) : chi p (-1 : ZMod (p ^ 2)) = 1 := by
  have h : ((-1 : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) = -1 := by simp
  rw [← h, chi_unit, h]
  have hev : Even (p - 1) := hp.out.even_sub_one hp2
  rw [hev.neg_one_pow, sub_self, AddChar.map_zero_eq_one]

end ChowlaOpus.KCharAux

namespace ChowlaOpus

theorem kernelCharStatement_holds : KernelCharStatement := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨KCharAux.chi p, KCharAux.chi_neg_one p hp2, KCharAux.chi_one_add p⟩

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Phase.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.PhaseAux

open Finset ComplexConjugate

/- ### Generalities on characters -/

lemma norm_apply_of_isUnit {R : Type*} [CommRing R] [Finite Rˣ] (χ : MulChar R ℂ) {a : R}
    (ha : IsUnit a) : ‖χ a‖ = 1 := by
  cases nonempty_fintype Rˣ
  have : NeZero (Fintype.card Rˣ) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨u, rfl⟩ := ha
  rw [← MulChar.coe_equivToUnitHom]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

lemma conj_apply {p : ℕ} [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    conj (χ a) = χ a⁻¹ := by
  rw [← MulChar.inv_apply', ← MulChar.star_apply']; rfl

lemma mul_conj_eq_one (v : ℂ) (hv : ‖v‖ = 1) : v * conj v = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]; norm_num

lemma natCast_ne_zero_of_lt {p n : ℕ} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd hn h
  omega

/-- Lift of a character mod `p` to a character mod `p²` through reduction mod `p`. -/
noncomputable def lift (p : ℕ) [Fact p.Prime] (ξ : MulChar (ZMod p) ℂ) :
    MulChar (ZMod (p ^ 2)) ℂ where
  toFun a := ξ (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) a)
  map_one' := by simp
  map_mul' a b := by simp
  map_nonunit' a ha := by
    apply MulChar.map_nonunit
    intro hu
    apply ha
    have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨v, rfl⟩ : ∃ v : ℕ, (v : ZMod (p ^ 2)) = a := ⟨a.val, ZMod.natCast_zmod_val a⟩
    rw [map_natCast, ZMod.isUnit_iff_coprime] at hu
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 2 hu

lemma lift_apply (p : ℕ) [Fact p.Prime] (ξ : MulChar (ZMod p) ℂ) (a : ZMod (p ^ 2)) :
    lift p ξ a = ξ (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) a) := rfl

lemma gaussPhase_mul_lift (p : ℕ) [Fact p.Prime] (χ₀ : MulChar (ZMod (p ^ 2)) ℂ)
    (ξ : MulChar (ZMod p) ℂ) (m : ℕ) :
    gaussPhase p (χ₀ * lift p ξ) (m : ℤ) =
      gaussPhase p χ₀ (m : ℤ) * ξ ((m ^ m : ℕ) : ZMod p) := by
  unfold gaussPhase
  rw [MulChar.mul_apply, mul_zpow, lift_apply]
  simp only [Int.cast_natCast, map_natCast, zpow_natCast, Nat.cast_pow, map_pow]
  ring

lemma kernelChar_mul_lift (p : ℕ) [Fact p.Prime] (χ₀ : MulChar (ZMod (p ^ 2)) ℂ)
    (hχ₀ : KernelChar p χ₀) (ψ : MulChar (ZMod p) ℂ) :
    KernelChar p (χ₀ * lift p (ψ * ψ)) := by
  obtain ⟨h1, h2⟩ := hχ₀
  refine ⟨?_, fun t => ?_⟩
  · rw [MulChar.mul_apply, h1, lift_apply, map_neg, map_one, MulChar.mul_apply, ← map_mul]
    norm_num
  · rw [MulChar.mul_apply, h2, lift_apply, map_intCast]
    have : (((1 + (p : ℤ) * t : ℤ)) : ZMod p) = 1 := by
      push_cast; rw [ZMod.natCast_self]; ring
    rw [this, map_one, mul_one]

lemma norm_gaussPhase (p : ℕ) [Fact p.Prime] (χ : MulChar (ZMod (p ^ 2)) ℂ) (m : ℕ)
    (hm0 : 0 < m) (hmp : m < p) : ‖gaussPhase p χ (m : ℤ)‖ = 1 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
  have hu : IsUnit ((m : ℤ) : ZMod (p ^ 2)) := by
    rw [Int.cast_natCast, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2
      (fun h => absurd (Nat.le_of_dvd hm0 h) (by omega))).symm
  unfold gaussPhase
  rw [norm_mul, norm_ee, norm_zpow, norm_apply_of_isUnit χ hu, one_zpow, one_mul]

lemma multIndep_pow {ι : Type} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (h : MultIndep n) : MultIndep (fun i => n i ^ n i) := by
  intro e he
  have := h (fun i => (n i : ℤ) * e i) (by
    rw [← he]
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    rw [zpow_mul, zpow_natCast])
  funext i
  have hi := congrFun this i
  simp only [Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at hi
  rcases hi with hi | hi
  · exact absurd hi (hn i).ne'
  · exact hi

/- ### Elementary estimates -/

lemma diag_lower (K : ℕ) :
    1 / ((K : ℝ) + 1) ≤ ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) := by
  have h1 : (∑ j ∈ range (K + 1), (K.choose j : ℝ)) ^ 2 ≤
      ((range (K + 1)).card : ℝ) * ∑ j ∈ range (K + 1), (K.choose j : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : ∑ j ∈ range (K + 1), (K.choose j : ℝ) = 2 ^ K := by
    exact_mod_cast Nat.sum_range_choose K
  have h4 : ((2 : ℝ) ^ K) ^ 2 = 4 ^ K := by rw [sq, ← mul_pow]; norm_num
  rw [h2, card_range, h4] at h1
  rw [← Finset.sum_div, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at h1
  linarith

lemma exists_K (d : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ K : ℕ, r ^ K < (1 / ((K : ℝ) + 1)) ^ d := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one d (r := r)
    (by rwa [abs_of_nonneg hr0])
  have hev : ∀ᶠ K : ℕ in Filter.atTop, (K : ℝ) ^ d * r ^ K < 1 / 2 ^ d :=
    (tendsto_order.1 ht).2 _ (by positivity)
  obtain ⟨K, hK, hK1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨K, ?_⟩
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have h2 : ((K : ℝ) + 1) ^ d ≤ 2 ^ d * (K : ℝ) ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
  rw [div_pow, one_pow, lt_div_iff₀ (by positivity)]
  calc r ^ K * ((K : ℝ) + 1) ^ d ≤ r ^ K * (2 ^ d * (K : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hr0 K)
    _ = 2 ^ d * ((K : ℝ) ^ d * r ^ K) := by ring
    _ < 2 ^ d * (1 / 2 ^ d) := by gcongr
    _ = 1 := by field_simp

lemma norm_half_sq (w : ℂ) (hw : ‖w‖ = 1) : ‖(1 + w) / 2‖ ^ 2 = 1 - ‖w - 1‖ ^ 2 / 4 := by
  have h2 : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]; norm_num
  have h4 : ‖(2 : ℂ)‖ ^ 2 = 4 := by norm_num
  rw [norm_div, div_pow, h4]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  linear_combination (1 / 2 : ℝ) * h2

lemma prod_le_of_far {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ) (u v : ι → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) {η' : ℝ} (hη' : 0 ≤ η') (i₀ : ι)
    (h : η' ≤ ‖u i₀ - v i₀‖) :
    ∏ i, ‖(1 + u i * conj (v i)) / 2‖ ^ (2 * K) ≤ (1 - η' ^ 2 / 4) ^ K := by
  have key : ∀ i, ‖(1 + u i * conj (v i)) / 2‖ ^ 2 = 1 - ‖u i - v i‖ ^ 2 / 4 := by
    intro i
    have hw : ‖u i * conj (v i)‖ = 1 := by rw [norm_mul, Complex.norm_conj, hu, hv, one_mul]
    have hw1 : ‖u i * conj (v i) - 1‖ = ‖u i - v i‖ := by
      have h3 : u i * conj (v i) - 1 = (u i - v i) * conj (v i) := by
        have := mul_conj_eq_one (v i) (hv i)
        linear_combination this
      rw [h3, norm_mul, Complex.norm_conj, hv, mul_one]
    rw [norm_half_sq _ hw, hw1]
  calc ∏ i, ‖(1 + u i * conj (v i)) / 2‖ ^ (2 * K)
      ≤ ∏ i, (if i = i₀ then (1 - η' ^ 2 / 4) ^ K else 1) := by
        apply Finset.prod_le_prod (fun i _ => by positivity)
        intro i _
        rw [pow_mul, key i]
        split_ifs with hi
        · rw [hi]
          have h0 := key i₀
          apply pow_le_pow_left₀ (by rw [← h0]; positivity)
          have : η' ^ 2 ≤ ‖u i₀ - v i₀‖ ^ 2 := pow_le_pow_left₀ hη' h 2
          linarith
        · have h0 := key i
          apply pow_le_one₀ (by rw [← h0]; positivity)
          have : 0 ≤ ‖u i - v i‖ ^ 2 := by positivity
          linarith
    _ = (1 - η' ^ 2 / 4) ^ K := by simp

/- ### The Fourier expansion of the test function -/

/-- Coefficient of `w^j \bar w^l` in `|(1 + w \bar z)/2|^{2K}` (after factoring out `z`). -/
noncomputable def coef (K : ℕ) (z : ℂ) (s : ℕ × ℕ) : ℂ :=
  (K.choose s.1 * K.choose s.2 : ℂ) / 4 ^ K * conj z ^ s.1 * z ^ s.2

lemma one_add_div_two_pow (w : ℂ) (K : ℕ) :
    ((1 + w) / 2) ^ K = ∑ j ∈ range (K + 1), (K.choose j : ℂ) / 2 ^ K * w ^ j := by
  rw [div_pow, add_comm, add_pow, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one]; ring

lemma expand_one (w : ℂ) (K : ℕ) :
    ((‖(1 + w) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      ∑ s ∈ range (K + 1) ×ˢ range (K + 1),
        (K.choose s.1 * K.choose s.2 : ℂ) / 4 ^ K * w ^ s.1 * conj w ^ s.2 := by
  have hu : ((‖(1 + w) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      ((1 + w) / 2) ^ K * (conj ((1 + w) / 2)) ^ K := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]; push_cast; ring
  have hc : conj ((1 + w) / 2) = (1 + conj w) / 2 := by
    rw [map_div₀, map_add, map_one, map_ofNat]
  rw [hu, hc, one_add_div_two_pow, one_add_div_two_pow, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have h4 : (4 : ℂ) ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  dsimp only
  rw [h4]; ring

lemma expand_prod {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ) (u v : ι → ℂ) :
    ((∏ i, ‖(1 + u i * conj (v i)) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
        (∏ i, coef K (v i) (x i)) * ((∏ i, u i ^ (x i).1) * conj (∏ i, u i ^ (x i).2)) := by
  rw [Complex.ofReal_prod]
  simp_rw [expand_one]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [coef, map_mul, map_pow, Complex.conj_conj, mul_pow]
  ring

lemma diag_sum (K : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ∑ s ∈ range (K + 1) ×ˢ range (K + 1), (coef K z s * if s.1 = s.2 then (1 : ℂ) else 0) =
      ((∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) : ℝ) : ℂ) := by
  rw [Finset.sum_product, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hj]
  have h1 : conj z * z = 1 := by rw [mul_comm]; exact mul_conj_eq_one z hz
  have h2 : conj z ^ j * z ^ j = 1 := by rw [← mul_pow, h1, one_pow]
  simp only [coef]
  push_cast
  linear_combination ((K.choose j : ℂ) * K.choose j / 4 ^ K) * h2

/- ### Orthogonality -/

lemma char_sum_sq {p : ℕ} [Fact p.Prime] (α β : ZMod p) (hβ : β ≠ 0) :
    ∑ ψ : MulChar (ZMod p) ℂ, (ψ * ψ) α * conj ((ψ * ψ) β) =
      if β * β = α * α then (p.totient : ℂ) else 0 := by
  have hu : IsUnit (β * β) := (mul_ne_zero hβ hβ).isUnit
  rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (α * α)]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [conj_apply, MulChar.mul_apply, MulChar.mul_apply, ← map_mul, ← map_mul, mul_inv, mul_comm]

lemma diag_iff {ι : Type} [Fintype ι] (B : ι → ℕ) (hB : ∀ i, 0 < B i) (hind : MultIndep B)
    (p : ℕ) [Fact p.Prime] (x : ι → ℕ × ℕ)
    (hab : (∏ i, B i ^ (x i).1) + (∏ i, B i ^ (x i).2) < p) :
    ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p) * ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p) =
        ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) * ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) ↔
      ∀ i, (x i).1 = (x i).2 := by
  have hpos : 0 < ∏ i, B i ^ (x i).2 := Finset.prod_pos fun i _ => pow_pos (hB i) _
  constructor
  · intro h
    have hab' : (∏ i, B i ^ (x i).1) = ∏ i, B i ^ (x i).2 := by
      rcases mul_self_eq_mul_self_iff.1 h with h | h
      · rw [ZMod.natCast_eq_natCast_iff'] at h
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
        exact h.symm
      · exfalso
        have h2 : (((∏ i, B i ^ (x i).2) + (∏ i, B i ^ (x i).1) : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, h]; ring
        rw [ZMod.natCast_eq_zero_iff] at h2
        have := Nat.le_of_dvd (by omega) h2
        omega
    have hB0 : ∀ i, (B i : ℚ) ≠ 0 := fun i => by exact_mod_cast (hB i).ne'
    have hq : ∏ i, (B i : ℚ) ^ (((x i).1 : ℤ) - (x i).2) = 1 := by
      rw [show ∏ i, (B i : ℚ) ^ (((x i).1 : ℤ) - (x i).2) =
          ∏ i, ((B i : ℚ) ^ (x i).1 / (B i : ℚ) ^ (x i).2) from
        Finset.prod_congr rfl fun i _ => by rw [zpow_sub₀ (hB0 i), zpow_natCast, zpow_natCast]]
      rw [Finset.prod_div_distrib, div_eq_one_iff_eq
        (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hB0 i))]
      exact_mod_cast hab'
    have he := hind _ hq
    intro i
    have := congrFun he i
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    exact this
  · intro h
    have : (∏ i, B i ^ (x i).1) = ∏ i, B i ^ (x i).2 :=
      Finset.prod_congr rfl fun i _ => by rw [h i]
    rw [this]

/- ### The averaging identity -/

lemma sum_Phi_eq {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → ℕ) (hB : ∀ i, 0 < B i)
    (hind : MultIndep B) (K p : ℕ) [Fact p.Prime] (hp : 2 * (∏ i, B i ^ K) < p)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ((∑ ψ : MulChar (ZMod p) ℂ,
        ∏ i, ‖(1 + (ψ * ψ) (B i : ZMod p) * conj (z i)) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      (p.totient : ℂ) *
        ((∏ _i : ι, ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) : ℝ) : ℂ) := by
  have hbound : ∀ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
      ∀ i, (x i).1 ≤ K ∧ (x i).2 ≤ K := by
    intro x hx i
    have := Fintype.mem_piFinset.1 hx i
    simp only [Finset.mem_product, Finset.mem_range] at this
    omega
  have hle : ∀ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
      (∏ i, B i ^ (x i).1) ≤ ∏ i, B i ^ K ∧ (∏ i, B i ^ (x i).2) ≤ ∏ i, B i ^ K := by
    intro x hx
    exact ⟨Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => Nat.pow_le_pow_right (hB i) (hbound x hx i).1,
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => Nat.pow_le_pow_right (hB i) (hbound x hx i).2⟩
  have hpos : ∀ x : ι → ℕ × ℕ, 0 < ∏ i, B i ^ (x i).2 :=
    fun x => Finset.prod_pos fun i _ => pow_pos (hB i) _
  rw [Complex.ofReal_sum]
  calc ∑ ψ : MulChar (ZMod p) ℂ,
        ((∏ i, ‖(1 + (ψ * ψ) (B i : ZMod p) * conj (z i)) / 2‖ ^ (2 * K) : ℝ) : ℂ)
      = ∑ ψ : MulChar (ZMod p) ℂ,
          ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
            (∏ i, coef K (z i) (x i)) *
              ((ψ * ψ) ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) *
                conj ((ψ * ψ) ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p))) := by
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [expand_prod K (fun i => (ψ * ψ) (B i : ZMod p)) z]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Nat.cast_prod, Nat.cast_pow, map_prod, map_pow]
    _ = ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
          (∏ i, coef K (z i) (x i)) * ∑ ψ : MulChar (ZMod p) ℂ,
            ((ψ * ψ) ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) *
              conj ((ψ * ψ) ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p))) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
          (∏ i, coef K (z i) (x i)) *
            ((p.totient : ℂ) * ∏ i, (if (x i).1 = (x i).2 then (1 : ℂ) else 0)) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hx' := hle x hx
        rw [char_sum_sq _ _ (natCast_ne_zero_of_lt (hpos x) (by omega)), Finset.prod_boole]
        have hd := diag_iff B hB hind p x (by omega)
        by_cases h : ∀ i, (x i).1 = (x i).2
        · rw [if_pos (hd.2 h), if_pos (fun i _ => h i)]; ring
        · rw [if_neg (fun h' => h (hd.1 h')),
            if_neg (fun h' => h (fun i => h' i (Finset.mem_univ i)))]
          ring
    _ = (p.totient : ℂ) * ∏ i, ∑ s ∈ range (K + 1) ×ˢ range (K + 1),
          (coef K (z i) s * if s.1 = s.2 then (1 : ℂ) else 0) := by
        rw [Finset.prod_univ_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = _ := by
        congr 1
        rw [Complex.ofReal_prod]
        exact Finset.prod_congr rfl fun i _ => diag_sum K (z i) (hz i)

/- ### The equidistribution statement for squares of characters -/

theorem exists_char {ι : Type} [Fintype ι] (B : ι → ℕ) (hB : ∀ i, 0 < B i)
    (hind : MultIndep B) (η : ℝ) (hη : 0 < η) :
    ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ z : ι → ℂ, (∀ i, ‖z i‖ = 1) →
      ∃ ψ : MulChar (ZMod p) ℂ, ∀ i, ‖(ψ * ψ) (B i : ZMod p) - z i‖ < η := by
  classical
  have hη'0 : 0 < min η 1 := lt_min hη one_pos
  have hη'1 : min η 1 ≤ 1 := min_le_right _ _
  have hη'η : min η 1 ≤ η := min_le_left _ _
  have hr0 : 0 ≤ 1 - (min η 1) ^ 2 / 4 := by nlinarith
  have hr1 : 1 - (min η 1) ^ 2 / 4 < 1 := by have := pow_pos hη'0 2; linarith
  obtain ⟨K, hKr⟩ := exists_K (Fintype.card ι) hr0 hr1
  refine ⟨2 * (∏ i, B i ^ K) + ∑ i, B i + 1, fun p hp hpP z hz => ?_⟩
  have := Fact.mk hp
  have hpM : 2 * (∏ i, B i ^ K) < p := by omega
  have hBp : ∀ i, B i < p := fun i => by
    have := Finset.single_le_sum (f := B) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hsum := sum_Phi_eq B hB hind K p hpM z hz
  have hDlow : (1 / ((K : ℝ) + 1)) ^ Fintype.card ι ≤
      ∏ _i : ι, ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) := by
    rw [Finset.prod_const, Finset.card_univ]
    exact pow_le_pow_left₀ (by positivity) (diag_lower K) _
  have hcard : (Fintype.card (MulChar (ZMod p) ℂ) : ℂ) = (p.totient : ℂ) := by
    have := DirichletCharacter.sum_characters_eq ℂ (1 : ZMod p)
    simpa using this
  have hreal : ∑ _ψ : MulChar (ZMod p) ℂ,
        ∏ _i : ι, ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) ≤
      ∑ ψ : MulChar (ZMod p) ℂ,
        ∏ i, ‖(1 + (ψ * ψ) (B i : ZMod p) * conj (z i)) / 2‖ ^ (2 * K) := by
    apply le_of_eq
    apply Complex.ofReal_injective
    rw [hsum, Complex.ofReal_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  obtain ⟨ψ, -, hψ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hreal
  refine ⟨ψ, fun i => ?_⟩
  by_contra hcon
  replace hcon := not_lt.1 hcon
  have hunit : ∀ j, ‖(ψ * ψ) (B j : ZMod p)‖ = 1 := fun j =>
    norm_apply_of_isUnit _ (natCast_ne_zero_of_lt (hB j) (hBp j)).isUnit
  have hle := prod_le_of_far K (fun j => (ψ * ψ) (B j : ZMod p)) z hunit hz hη'0.le i
    (le_trans hη'η hcon)
  exact absurd (hle.trans_lt (hKr.trans_le hDlow)) (not_lt.2 hψ)

end ChowlaOpus.PhaseAux

namespace ChowlaOpus

open ComplexConjugate

theorem phaseStatement_holds (hK : KernelCharStatement) : PhaseStatement := by
  intro ι _ n hn hind η hη
  obtain ⟨P₁, hP₁⟩ := PhaseAux.exists_char (fun i => n i ^ n i) (fun i => pow_pos (hn i) _)
    (PhaseAux.multIndep_pow n hn hind) η hη
  refine ⟨max P₁ (∑ i, n i + 3), fun p hp hpP μ hμ => ?_⟩
  have hp1 : P₁ ≤ p := le_trans (le_max_left _ _) hpP
  have hp2 : ∑ i, n i + 3 ≤ p := le_trans (le_max_right _ _) hpP
  have hnp : ∀ i, n i < p := fun i => by
    have := Finset.single_le_sum (f := n) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hp2' : p ≠ 2 := by omega
  have := Fact.mk hp
  obtain ⟨χ₀, hχ₀⟩ := hK p hp hp2'
  have hg : ∀ i, ‖gaussPhase p χ₀ (n i)‖ = 1 := fun i =>
    PhaseAux.norm_gaussPhase p χ₀ (n i) (hn i) (hnp i)
  obtain ⟨ψ, hψ⟩ := hP₁ p hp hp1 (fun i => μ i * conj (gaussPhase p χ₀ (n i))) (fun i => by
    rw [norm_mul, Complex.norm_conj, hμ, hg, one_mul])
  refine ⟨χ₀ * PhaseAux.lift p (ψ * ψ), PhaseAux.kernelChar_mul_lift p χ₀ hχ₀ ψ, fun i => ?_⟩
  rw [PhaseAux.gaussPhase_mul_lift]
  have key : gaussPhase p χ₀ (n i) * (ψ * ψ) ((n i ^ n i : ℕ) : ZMod p) - μ i =
      gaussPhase p χ₀ (n i) *
        ((ψ * ψ) ((n i ^ n i : ℕ) : ZMod p) - μ i * conj (gaussPhase p χ₀ (n i))) := by
    have := PhaseAux.mul_conj_eq_one _ (hg i)
    linear_combination (μ i) * this
  rw [key, norm_mul, hg, one_mul]
  exact hψ i

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/CRT.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.CRTAux

open Finset Polynomial

/-- The polynomial `∑ i, c i X^i` attached to a coefficient vector. -/
noncomputable def vecPoly {k : ℕ} (c : Fin (k + 1) → ℤ) : ℤ[X] :=
  ∑ i : Fin (k + 1), Polynomial.C (c i) * X ^ (i : ℕ)

lemma vecPoly_coeff {k : ℕ} (c : Fin (k + 1) → ℤ) (j : Fin (k + 1)) :
    (vecPoly c).coeff j = c j := by
  rw [vecPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    exact ite_eq_right_iff.mpr fun h => absurd (Fin.ext h).symm hb
  · simp

lemma vecPoly_ne_zero {k : ℕ} {c : Fin (k + 1) → ℤ} (hc : c ≠ 0) : vecPoly c ≠ 0 := by
  intro h
  apply hc
  funext j
  rw [← vecPoly_coeff c j, h]
  simp

lemma vecPoly_eval {k : ℕ} (c : Fin (k + 1) → ℤ) (x : ℤ) :
    (vecPoly c).eval x = ∑ i : Fin (k + 1), x ^ (i : ℕ) * c i := by
  simp [vecPoly, Polynomial.eval_finsetSum, mul_comm]

lemma exists_avoid {k : ℕ} (C : Finset (Fin (k + 1) → ℤ)) (hC : ∀ c ∈ C, c ≠ 0) :
    ∃ y : Fin (k + 1) → ℤ, ∀ c ∈ C, ∑ i, y i * c i ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ :=
    Infinite.exists_notMem_finset (C.biUnion fun c => (vecPoly c).roots.toFinset)
  refine ⟨fun i => x ^ (i : ℕ), fun c hc h => hx ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨c, hc, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (vecPoly_ne_zero (hC c hc)),
    Polynomial.IsRoot, vecPoly_eval]
  exact h

lemma minor_ne_zero {k : ℕ} {v w : Fin (k + 1) → ℤ} (hv : v 0 ≠ 0)
    (h : ¬ ∀ i j, v i * w j = v j * w i) : (fun i => v 0 * w i - w 0 * v i) ≠ 0 := by
  intro h0
  apply h
  intro i j
  have hi : v 0 * w i = w 0 * v i := sub_eq_zero.mp (congrFun h0 i)
  have hj : v 0 * w j = w 0 * v j := sub_eq_zero.mp (congrFun h0 j)
  apply mul_left_cancel₀ hv
  calc v 0 * (v i * w j) = v i * (v 0 * w j) := by ring
    _ = v i * (w 0 * v j) := by rw [hj]
    _ = v j * (w 0 * v i) := by ring
    _ = v j * (v 0 * w i) := by rw [hi]
    _ = v 0 * (v j * w i) := by ring

lemma padicValRat_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- Private-prime criterion for multiplicative independence. -/
lemma multIndep_of_primes {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, (r i).Prime) (hdvd : ∀ i, r i ∣ n i)
    (hndvd : ∀ i j, i ≠ j → ¬ r i ∣ n j) : MultIndep n := by
  classical
  intro e he
  funext i
  have : Fact (r i).Prime := ⟨hr i⟩
  have h1 := congrArg (padicValRat (r i)) he
  rw [padicValRat_prod _ _ _ (fun j _ => zpow_ne_zero _ (Nat.cast_ne_zero.mpr (hn j))),
    padicValRat.one] at h1
  simp only [padicValRat.zpow, padicValRat.of_nat] at h1
  rw [Finset.sum_eq_single i] at h1
  · have hp : 1 ≤ padicValNat (r i) (n i) := one_le_padicValNat_of_dvd (hn i) (hdvd i)
    have hpn : (padicValNat (r i) (n i) : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp h1).resolve_right hpn
  · intro j _ hji
    rw [padicValNat.eq_zero_of_not_dvd (hndvd i j (Ne.symm hji))]
    simp
  · simp

/-- Main lemma for an indexed family. -/
lemma main {ι : Type*} [Fintype ι] {k : ℕ} (V : ι → Fin (k + 1) → ℤ) (hpos : ∀ i, 0 < V i 0)
    (hnp : ∀ i j, (∀ a b, V i a * V j b = V i b * V j a) → i = j) :
    ∃ L : Fin (k + 1) → ℤ, (∀ i, 0 < ∑ a, L a * V i a) ∧
      MultIndep (fun i => (∑ a, L a * V i a).toNat) := by
  classical
  -- the minors `c i j`
  set c : ι → ι → Fin (k + 1) → ℤ := fun i j b => V i 0 * V j b - V j 0 * V i b with hc
  have hc0 : ∀ i j, i ≠ j → c i j ≠ 0 := fun i j hij =>
    minor_ne_zero (hpos i).ne' (fun h => hij (hnp i j h))
  obtain ⟨y, hy⟩ := exists_avoid
    ((univ.filter fun p : ι × ι => p.1 ≠ p.2).image fun p => c p.1 p.2)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact hc0 _ _ (Finset.mem_filter.mp hp).2)
  -- the integer forms `a i j = ℓ_i · V j`
  set a : ι → ι → ℤ := fun i j => V i 0 * (y ⬝ᵥ V j) - (y ⬝ᵥ V i) * V j 0 with ha
  have haii : ∀ i, a i i = 0 := fun i => by simp only [ha]; ring
  have hane : ∀ i j, i ≠ j → a i j ≠ 0 := by
    intro i j hij
    have := hy (c i j) (Finset.mem_image.mpr ⟨(i, j), by simp [hij], rfl⟩)
    convert this using 1
    simp only [ha, hc, dotProduct]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  set B : ℕ := ∑ i, ∑ j, (a i j).natAbs with hB
  have haB : ∀ i j, (a i j).natAbs ≤ B := fun i j =>
    (Finset.single_le_sum (f := fun j => (a i j).natAbs) (fun _ _ => Nat.zero_le _)
      (mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, (a i j).natAbs) (fun _ _ => Nat.zero_le _)
        (mem_univ i))
  -- distinct primes `r i > B`
  set idx : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with hidx
  have hidx_inj : Function.Injective idx := fun i j h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set r : ι → ℕ := fun i => Nat.nth Nat.Prime (B + 1 + idx i) with hr
  have hrp : ∀ i, (r i).Prime := fun i => Nat.prime_nth_prime _
  have hr_inj : Function.Injective r := fun i j h =>
    hidx_inj (Nat.add_left_cancel (Nat.nth_injective Nat.infinite_setOfPred_prime h))
  have hrB : ∀ i, B < r i := fun i => by
    have : B + 1 + idx i ≤ Nat.nth Nat.Prime (B + 1 + idx i) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le (B + 1 + idx i)
    show B < Nat.nth Nat.Prime (B + 1 + idx i)
    omega
  -- products of the primes
  set Q : ℤ := ∏ i, (r i : ℤ) with hQ
  set Qx : ι → ℤ := fun i => ∏ j ∈ univ.erase i, (r j : ℤ) with hQx
  have hQpos : 1 ≤ Q := by
    have : 0 < Q := Finset.prod_pos fun i _ => by exact_mod_cast (hrp i).pos
    omega
  set X : ι → ℤ := fun j => ∑ i, Qx i * a i j with hX
  set M : ℤ := ∑ j, |X j| + 1 with hM
  set L : Fin (k + 1) → ℤ :=
    ∑ i, Qx i • (V i 0 • y - (y ⬝ᵥ V i) • Pi.single 0 1) + (M * Q) • Pi.single 0 1 with hL
  set n : ι → ℤ := fun j => X j + M * Q * V j 0 with hn
  have hLv : ∀ j, ∑ b, L b * V j b = n j := by
    intro j
    show L ⬝ᵥ V j = _
    simp only [hL, add_dotProduct, sum_dotProduct, smul_dotProduct, sub_dotProduct,
      single_dotProduct, smul_eq_mul, hn, hX, ha, one_mul]
  have hnpos : ∀ j, 0 < n j := by
    intro j
    have h1 : |X j| ≤ ∑ j, |X j| :=
      Finset.single_le_sum (f := fun j => |X j|) (fun _ _ => abs_nonneg _) (mem_univ j)
    have h2 : -|X j| ≤ X j := neg_abs_le _
    have h3 : 1 ≤ V j 0 := hpos j
    have h4 : 1 ≤ Q * V j 0 := by nlinarith
    have h6 : 1 ≤ M := by rw [hM]; linarith [abs_nonneg (X j)]
    have h5 : M ≤ M * Q * V j 0 := by rw [mul_assoc]; nlinarith
    simp only [hn]
    linarith
  have hcong : ∀ i j, (r i : ℤ) ∣ n j - Qx i * a i j := by
    intro i j
    simp only [hn, hX]
    rw [← Finset.add_sum_erase univ (fun l => Qx l * a l j) (mem_univ i)]
    have h1 : (r i : ℤ) ∣ ∑ l ∈ univ.erase i, Qx l * a l j := Finset.dvd_sum fun l hl =>
      Dvd.dvd.mul_right (by
        simp only [hQx]
        exact Finset.dvd_prod_of_mem _
          (Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hl).1 h.symm, mem_univ _⟩)) _
    have hQ' : (r i : ℤ) ∣ Q := Finset.dvd_prod_of_mem _ (mem_univ i)
    have h2 : Qx i * a i j + ∑ l ∈ univ.erase i, Qx l * a l j + M * Q * V j 0 - Qx i * a i j
        = ∑ l ∈ univ.erase i, Qx l * a l j + M * Q * V j 0 := by ring
    rw [h2]
    exact dvd_add h1 (Dvd.dvd.mul_right (Dvd.dvd.mul_left hQ' _) _)
  have hdvd : ∀ i, (r i : ℤ) ∣ n i := by
    intro i
    simpa [haii] using hcong i i
  have hndvd : ∀ i j, i ≠ j → ¬ (r i : ℤ) ∣ n j := by
    intro i j hij hd
    have h1 : (r i : ℤ) ∣ Qx i * a i j := by
      have := dvd_sub hd (hcong i j)
      rwa [sub_sub_cancel] at this
    have hpr : Prime (r i : ℤ) := Nat.prime_iff_prime_int.mp (hrp i)
    rcases hpr.dvd_or_dvd h1 with h2 | h2
    · simp only [hQx] at h2
      obtain ⟨l, hl, h3⟩ := (Prime.dvd_finsetProd_iff hpr _).mp h2
      have h4 : r i ∣ r l := Int.natCast_dvd_natCast.mp h3
      have h5 : r i = r l := (Nat.prime_dvd_prime_iff_eq (hrp i) (hrp l)).mp h4
      exact (Finset.mem_erase.mp hl).1 (hr_inj h5).symm
    · have h3 : r i ∣ (a i j).natAbs := Int.ofNat_dvd_left.mp h2
      have h4 := Nat.le_of_dvd (Int.natAbs_pos.mpr (hane i j hij)) h3
      have := haB i j
      have := hrB i
      omega
  refine ⟨L, fun j => hLv j ▸ hnpos j, ?_⟩
  simp_rw [hLv]
  have hnat : ∀ j, ((n j).toNat : ℤ) = n j := fun j => Int.toNat_of_nonneg (hnpos j).le
  refine multIndep_of_primes _ (fun j => by have := hnpos j; omega) r hrp
    (fun i => ?_) (fun i j hij => ?_)
  · rw [← Int.natCast_dvd_natCast, hnat]
    exact hdvd i
  · rw [← Int.natCast_dvd_natCast, hnat]
    exact hndvd i j hij

end ChowlaOpus.CRTAux

namespace ChowlaOpus

theorem crtStatement_holds : CRTStatement := by
  intro k S hpos hnp
  obtain ⟨L, hL1, hL2⟩ := CRTAux.main (fun v : S => (v : Fin (k + 1) → ℤ))
    (fun v => hpos v v.2) (fun v w h => Subtype.ext (hnp v v.2 w w.2 h))
  exact ⟨L, fun v hv => hL1 ⟨v, hv⟩, hL2⟩

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/W9.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.W9Aux

lemma exists_ee_eq {u : ℂ} (hu : ‖u‖ = 1) : ∃ z : ℝ, ee z = u := by
  refine ⟨Complex.arg u / (2 * Real.pi), ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu] at h
  simp only [Complex.ofReal_one, one_mul] at h
  rw [ee]
  convert h using 2
  push_cast
  field_simp

lemma norm_chi_eq_one {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (k : ℤ)
    (hk : ¬ (p : ℤ) ∣ k) : ‖χ (k : ZMod (p ^ 2))‖ = 1 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcop : IsCoprime ((p ^ 2 : ℕ) : ℤ) k := by
    push_cast
    exact ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hk).pow_left
  have hu : IsUnit (k : ZMod (p ^ 2)) := (ZMod.coe_int_isUnit_iff_isCoprime k (p ^ 2)).mpr hcop
  obtain ⟨u, hu⟩ := hu
  rw [← hu, ← MulChar.coe_equivToUnitHom]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

lemma hasCompactSupport_of_supp {f : ℝ → ℂ} {R : ℝ} (h : ∀ x, R < |x| → f x = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) (fun x hx => h x ?_)
  by_contra hc
  push Not at hc
  exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

lemma summable_b : Summable (fun n : ℕ => 1 / (1 + ((n : ℝ) + 1) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    push_cast at this
    exact this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
  apply one_div_le_one_div_of_le (by positivity)
  linarith

lemma tsum_b_le : ∑' n : ℕ, 1 / (1 + ((n : ℝ) + 1) ^ 2) ≤ π ^ 2 / 6 - 1 / 2 := by
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 2).mpr hasSum_zeta_two
    convert this using 1 <;> try rfl
    · ext n; push_cast; ring
    · norm_num [Finset.sum_range_succ]
  rw [summable_b.tsum_eq_zero_add]
  have hle : ∑' n : ℕ, 1 / (1 + (((n + 1 : ℕ) : ℝ) + 1) ^ 2) ≤ π ^ 2 / 6 - 1 := by
    refine (Summable.tsum_le_tsum (fun n => ?_)
      ((summable_nat_add_iff 1).mpr summable_b) hz.summable).trans hz.tsum_eq.le
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h0 : (1 : ℝ) / (1 + (((0 : ℕ) : ℝ) + 1) ^ 2) = 1 / 2 := by norm_num
  rw [h0]
  linarith

lemma aux_G (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    Summable (fun j : ℤ => 1 / (1 + ((j : ℝ) - f) ^ 2)) ∧
      ∑' j : ℤ, 1 / (1 + ((j : ℝ) - f) ^ 2) ≤ 5 := by
  have hb := summable_b
  have hb1 : Summable (fun n : ℕ => 1 / (1 + (n : ℝ) ^ 2)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (1 + (n : ℝ) ^ 2)) 1).mp
      (by push_cast; exact hb)
  have hN1 : Summable (fun n : ℕ => 1 / (1 + ((((n + 1 : ℕ) : ℤ) : ℝ) - f) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb1
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hN : Summable (fun n : ℕ => 1 / (1 + ((((n : ℕ) : ℤ) : ℝ) - f) ^ 2)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (1 + ((((n : ℕ) : ℤ) : ℝ) - f) ^ 2)) 1).mp hN1
  have hNeg : Summable (fun n : ℕ => 1 / (1 + (((-((n : ℤ) + 1) : ℤ) : ℝ) - f) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine ⟨Summable.of_nat_of_neg_add_one (f := fun j : ℤ => 1 / (1 + ((j : ℝ) - f) ^ 2)) hN hNeg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one (f := fun j : ℤ => 1 / (1 + ((j : ℝ) - f) ^ 2)) hN hNeg,
    hN.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / (1 + ((((0 : ℕ) : ℤ) : ℝ) - f) ^ 2) ≤ 1 := by
    apply div_le_one_of_le₀ _ (by positivity)
    nlinarith
  have h1 : ∑' n : ℕ, 1 / (1 + ((((n + 1 : ℕ) : ℤ) : ℝ) - f) ^ 2) ≤
      ∑' n : ℕ, 1 / (1 + (n : ℝ) ^ 2) := by
    refine Summable.tsum_le_tsum (fun n => ?_) hN1 hb1
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h1' : ∑' n : ℕ, 1 / (1 + (n : ℝ) ^ 2) = 1 + ∑' n : ℕ, 1 / (1 + ((n : ℝ) + 1) ^ 2) := by
    rw [hb1.tsum_eq_zero_add]
    push_cast
    norm_num
  have h2 : ∑' n : ℕ, 1 / (1 + (((-((n : ℤ) + 1) : ℤ) : ℝ) - f) ^ 2) ≤
      ∑' n : ℕ, 1 / (1 + ((n : ℝ) + 1) ^ 2) := by
    refine Summable.tsum_le_tsum (fun n => ?_) hNeg hb
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h3 := tsum_b_le
  have hpi : π ^ 2 < 12 := by
    have := Real.pi_lt_d2
    have := Real.pi_pos
    nlinarith
  linarith

lemma sum_inv_one_add_sq (y : ℝ) :
    Summable (fun k : ℤ => 1 / (1 + ((k : ℝ) - y) ^ 2)) ∧
      ∑' k : ℤ, 1 / (1 + ((k : ℝ) - y) ^ 2) ≤ 5 := by
  obtain ⟨h1, h2⟩ := aux_G (y - ⌊y⌋) (Int.fract_nonneg y) (Int.fract_lt_one y).le
  have key : (fun k : ℤ => 1 / (1 + ((k : ℝ) - y) ^ 2)) =
      (fun j : ℤ => 1 / (1 + ((j : ℝ) - (y - ⌊y⌋)) ^ 2)) ∘ (Equiv.subRight ⌊y⌋) := by
    ext k
    simp only [Function.comp_apply, Equiv.subRight_apply, Int.cast_sub]
    ring_nf
  rw [key]
  refine ⟨(Equiv.summable_iff _).mpr h1, ?_⟩
  rw [Function.comp_def, Equiv.tsum_eq (Equiv.subRight ⌊y⌋)
    (fun j : ℤ => 1 / (1 + ((j : ℝ) - (y - ⌊y⌋)) ^ 2))]
  exact h2

/-- Lower bound for the real part of a single row of the dual sum. -/
lemma row_re_ge (hR : RowSumStatement) (hM : MultStatement) {k : ℕ} {T K : ℝ}
    {S : Finset (Fin (k + 1) → ℤ)} {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}
    (hcf : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hLp : ∀ v ∈ S, 2 * |∑ i, L i * v i| < p)
    (hLinj : ∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w)
    {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) {η : ℝ} (hη0 : 0 ≤ η)
    (hphase : ∀ v ∈ S, v ≠ 0 →
      ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η)
    (y : ℝ) (kk : ℤ) :
    -((p : ℝ) * (𝓕 (cf 0) y).re + (p : ℝ) * η * S.card * K * (1 / (1 + y ^ 2))) ≤
      (∑ v ∈ S, 𝓕 (cf v) y * rowSum p χ (∑ i, L i * v i) kk).re := by
  obtain ⟨hRa, hRb, hRc, -, -⟩ := hR p hp hp2 χ hχ
  have hK : 0 ≤ K := by
    have h1 := hcf.decay 0 0
    have h2 : 0 ≤ ‖𝓕 (cf 0) 0‖ := norm_nonneg _
    norm_num at h1
    linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hF0 := hcf.fourier_b0 y
  have herr : 0 ≤ (p : ℝ) * η * S.card * K * (1 / (1 + y ^ 2)) := by positivity
  have hn0 : (∑ i, L i * (0 : Fin (k + 1) → ℤ) i) = 0 := by simp
  have hndvd : ∀ v ∈ S, v ≠ 0 → ¬ (p : ℤ) ∣ ∑ i, L i * v i := by
    intro v hv hv0 hdvd
    have hlt : |∑ i, L i * v i| < (p : ℤ) := by
      have := hLp v hv
      have := abs_nonneg (∑ i, L i * v i)
      linarith
    have h0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    exact hv0 (hLinj v hv 0 hcf.zero_mem (by rw [h0, hn0]))
  rw [← Finset.add_sum_erase S _ hcf.zero_mem, hn0]
  by_cases hk : (p : ℤ) ∣ kk
  · have hrest : ∑ v ∈ S.erase 0, 𝓕 (cf v) y * rowSum p χ (∑ i, L i * v i) kk = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨hv0, hvS⟩ := Finset.mem_erase.mp hv
      rw [hRb _ kk (hndvd v hvS hv0) hk, mul_zero]
    rw [hrest, add_zero, hRc kk, if_pos hk]
    obtain ⟨r, hr, hrge⟩ : ∃ r : ℝ, ((if (p : ℤ) ^ 2 ∣ kk then ((p : ℂ) ^ 2) else 0) - (p : ℂ)) =
        (r : ℂ) ∧ -(p : ℝ) ≤ r := by
      split_ifs
      · exact ⟨(p : ℝ) ^ 2 - p, by push_cast; ring, by nlinarith⟩
      · exact ⟨-(p : ℝ), by push_cast; ring, le_refl _⟩
    rw [hr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [hF0.2]
  · have hR0 : rowSum p χ 0 kk = 0 := by
      rw [hRc kk, if_neg hk,
        if_neg (fun h => hk (dvd_trans (dvd_pow_self _ two_ne_zero) h))]
      simp
    rw [hR0, mul_zero, zero_add]
    have hχk := norm_chi_eq_one hp χ kk hk
    obtain ⟨z, hz⟩ := exists_ee_eq hχk
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (χ (kk : ZMod (p ^ 2)))⁻¹ := ⟨_, rfl⟩
    have hcz : c = ee (-z) := by
      rw [hc, ← hz]
      exact inv_eq_of_mul_eq_one_right (by rw [← ee_add, add_neg_cancel, ee_zero])
    have hcn : ‖c‖ = 1 := by rw [hc, norm_inv, hχk, inv_one]
    have hee : ∀ v : Fin (k + 1) → ℤ,
        ee (∑ i, (v i : ℝ) * (-z * L i)) = c ^ (∑ i, L i * v i) := by
      intro v
      rw [hcz, ← ee_mul_intCast]
      congr 1
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hpos := hcf.pos (fun i => -z * L i) y
    obtain ⟨Sp, hSp⟩ : ∃ s : ℂ, s = trigEval S
        (fun v => mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y) (fun i => -z * L i) := ⟨_, rfl⟩
    rw [← hSp] at hpos
    have hSpeq : Sp = 𝓕 (cf 0) y + ∑ v ∈ S.erase 0,
        mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y * c ^ (∑ i, L i * v i) := by
      rw [hSp, trigEval, ← Finset.add_sum_erase S _ hcf.zero_mem]
      congr 1
      · simp [hM.2.1, ee_zero]
      · apply Finset.sum_congr rfl
        intro v _
        rw [hee]
    obtain ⟨E, hE⟩ : ∃ e : ℂ, e = ∑ v ∈ S.erase 0, 𝓕 (cf v) y * c ^ (∑ i, L i * v i) *
        (gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)) := ⟨_, rfl⟩
    have hrow : ∑ v ∈ S.erase 0, 𝓕 (cf v) y * rowSum p χ (∑ i, L i * v i) kk =
        (p : ℂ) * Sp - (p : ℂ) * 𝓕 (cf 0) y + (p : ℂ) * E := by
      rw [hSpeq, hE, mul_add, add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨hv0, hvS⟩ := Finset.mem_erase.mp hv
      rw [hRa _ kk (hndvd v hvS hv0) hk, ← hc]
      ring
    have hEnorm : ‖E‖ ≤ S.card * K * (1 / (1 + y ^ 2)) * η := by
      rw [hE]
      calc ‖∑ v ∈ S.erase 0, 𝓕 (cf v) y * c ^ (∑ i, L i * v i) *
            (gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T))‖
          ≤ ∑ v ∈ S.erase 0, ‖𝓕 (cf v) y * c ^ (∑ i, L i * v i) *
            (gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ v ∈ S.erase 0, K / (1 + y ^ 2) * η := by
            apply Finset.sum_le_sum
            intro v hv
            obtain ⟨hv0, hvS⟩ := Finset.mem_erase.mp hv
            rw [norm_mul, norm_mul, norm_zpow, hcn, one_zpow, mul_one]
            exact mul_le_mul (hcf.decay v y) (hphase v hvS hv0) (norm_nonneg _)
              (by positivity)
        _ = (S.erase 0).card * (K / (1 + y ^ 2) * η) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ S.card * (K / (1 + y ^ 2) * η) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_erase_le
        _ = S.card * K * (1 / (1 + y ^ 2)) * η := by ring
    rw [hrow]
    have hEre : -‖E‖ ≤ E.re := by
      have := Complex.abs_re_le_norm E
      linarith [neg_abs_le E.re]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
    have h1 : 0 ≤ (p : ℝ) * Sp.re := mul_nonneg hp0 hpos.2
    have h2 : (p : ℝ) * (-(S.card * K * (1 / (1 + y ^ 2)) * η)) ≤ p * E.re :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    nlinarith

/-- The real part of the Poisson sum is twice the cosine sum of the weights. -/
lemma lhs_eq {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)}
    {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}
    (hcf : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ} (hp : p.Prime)
    {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) {N : ℕ}
    (hN : (p : ℝ) ^ 2 * T ^ 2 ≤ N) (t : ℝ) {X : ℂ}
    (hX : HasSum (fun d : ℤ => ∑ v ∈ S, (if (p : ℤ) ∣ d then 0 else
          cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i)) *
            ee (d * t)) X) :
    X.re = 2 * ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * Real.cos (2 * Real.pi * d * t) := by
  obtain ⟨B, hB⟩ : ∃ B : ℤ → ℂ, B = fun d => if (p : ℤ) ∣ d then 0 else
      ∑ v ∈ S, cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i) :=
    ⟨_, rfl⟩
  have hX' : HasSum (fun d : ℤ => B d * ee (d * t)) X := by
    convert hX using 1
    ext d
    rw [hB]
    dsimp only
    split_ifs <;> simp [Finset.sum_mul]
  have hχneg : ∀ a : ZMod (p ^ 2), χ (-a) = χ a := fun a => by
    rw [← neg_one_mul, map_mul, hχ.1, one_mul]
  have hBneg : ∀ d, B (-d) = B d := by
    intro d
    rw [hB]
    dsimp only
    by_cases h : (p : ℤ) ∣ d
    · rw [if_pos (dvd_neg.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (dvd_neg.mp h')), if_neg h]
      apply Finset.sum_congr rfl
      intro v _
      simp only [Int.cast_neg, neg_div, hcf.even, hχneg]
  have hwgt : ∀ d : ℤ, wgt S cf L p χ d = (B d).re := by
    intro d
    rw [hB]
    simp only [wgt]
    split_ifs <;> simp
  have hPpos : (0 : ℝ) < (p : ℝ) ^ 2 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact pow_pos this 2
  have hBzero : ∀ n : ℕ, N < n → B n = 0 := by
    intro n hn
    rw [hB]
    dsimp only
    split_ifs with h
    · rfl
    · apply Finset.sum_eq_zero
      intro v _
      rw [hcf.supp v _ ?_, zero_mul]
      have hnN : (N : ℝ) < n := by exact_mod_cast hn
      rw [Int.cast_natCast, abs_of_nonneg (by positivity), lt_div_iff₀ hPpos]
      nlinarith [sq_nonneg T]
  have h2 := hX'.nat_add_neg
  have hB0 : B 0 = 0 := by rw [hB]; simp
  have hfin : HasSum (fun n : ℕ => B n * ee (((n : ℤ) : ℝ) * t) +
      B (-(n : ℤ)) * ee (((-(n : ℤ) : ℤ) : ℝ) * t))
      (∑ n ∈ Finset.Icc 1 N, (B n * ee (((n : ℤ) : ℝ) * t) +
        B (-(n : ℤ)) * ee (((-(n : ℤ) : ℤ) : ℝ) * t))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have : n = 0 := by omega
      subst this
      simp [hB0]
    · rw [hBneg, hBzero n hn]
      simp
  have hXeq := h2.unique hfin
  rw [hB0, zero_mul, add_zero] at hXeq
  rw [hXeq, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [hBneg, hwgt]
  simp only [Complex.add_re, Complex.mul_re, ee_re, ee_im, Int.cast_neg, Int.cast_natCast]
  rw [show 2 * π * (n : ℝ) * t = 2 * π * ((n : ℝ) * t) by ring,
    show 2 * π * (-(n : ℝ) * t) = -(2 * π * ((n : ℝ) * t)) by ring, Real.cos_neg, Real.sin_neg]
  ring

/-- `Re ∑_j c_0(j) e(jx) ≤ ∑_j c_0(j)`. -/
lemma re_tsum_le {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)}
    {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}
    (hcf : IsProfile T S cf K (T ^ 2)) (x : ℝ)
    (hs : Summable (fun j : ℤ => cf 0 j * ee (-((j : ℝ) * x)))) :
    (∑' j : ℤ, cf 0 j * ee (-((j : ℝ) * x))).re ≤ ∑' j : ℤ, (cf 0 j).re := by
  have hfin : Summable (fun j : ℤ => (cf 0 j).re) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-⌈T ^ 2⌉) ⌈T ^ 2⌉)
    intro j hj
    have hc := Int.le_ceil (T ^ 2)
    rw [hcf.supp 0 j ?_, Complex.zero_re]
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with hj | hj
    · have : (j : ℝ) < -⌈T ^ 2⌉ := by exact_mod_cast hj
      exact lt_abs.mpr (Or.inr (by linarith))
    · have : (⌈T ^ 2⌉ : ℝ) < j := by exact_mod_cast hj
      exact lt_abs.mpr (Or.inl (by linarith))
  rw [Complex.re_tsum hs]
  refine Summable.tsum_le_tsum (fun j => ?_) (Complex.hasSum_re hs.hasSum).summable hfin
  rw [Complex.mul_re, (hcf.b0 j).1, zero_mul, sub_zero, ee_re]
  have := (hcf.b0 j).2
  have := Real.cos_le_one (2 * π * -((j : ℝ) * x))
  nlinarith

end ChowlaOpus.W9Aux

namespace ChowlaOpus

theorem w9Statement_holds (hR : RowSumStatement) (hP : PoissonStatement)
    (hPP : PlainPoissonStatement) (hM : MultStatement) : W9Statement := by
  intro k T K S cf hcf hT L p hp hp2 hLp hLinj χ hχ η hη0 hηK hphase N hN t
  have hK : 0 ≤ K := by
    have h1 := hcf.decay 0 0
    have h2 : 0 ≤ ‖𝓕 (cf 0) 0‖ := norm_nonneg _
    norm_num at h1
    linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hcont : ∀ v, Continuous (cf v) := fun v => (hcf.smooth v).continuous
  have hcs : ∀ v, HasCompactSupport (cf v) :=
    fun v => W9Aux.hasCompactSupport_of_supp (hcf.supp v)
  have hPv := fun v => hP p hp χ (∑ i, L i * v i) (cf v) K (hcont v) (hcs v) (hcf.decay v) t
  have hLHS : HasSum (fun d : ℤ => ∑ v ∈ S, (if (p : ℤ) ∣ d then 0 else
      cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i)) * ee (d * t))
      (∑ v ∈ S, ∑' kk : ℤ, 𝓕 (cf v) (kk - (p : ℝ) ^ 2 * t) * rowSum p χ (∑ i, L i * v i) kk) :=
    hasSum_sum (fun v _ => (hPv v).2)
  have hRHS : HasSum (fun kk : ℤ => ∑ v ∈ S,
      𝓕 (cf v) (kk - (p : ℝ) ^ 2 * t) * rowSum p χ (∑ i, L i * v i) kk)
      (∑ v ∈ S, ∑' kk : ℤ, 𝓕 (cf v) (kk - (p : ℝ) ^ 2 * t) * rowSum p χ (∑ i, L i * v i) kk) :=
    hasSum_sum (fun v _ => (hPv v).1.hasSum)
  have hXre := W9Aux.lhs_eq hcf L hp hχ hN t hLHS
  obtain ⟨hs5, h5⟩ := W9Aux.sum_inv_one_add_sq ((p : ℝ) ^ 2 * t)
  obtain ⟨hPPs, hPPh⟩ := hPP (cf 0) K (hcont 0) (hcs 0) (hcf.decay 0) (-((p : ℝ) ^ 2 * t))
  have hF0 : HasSum (fun kk : ℤ => (𝓕 (cf 0) (kk - (p : ℝ) ^ 2 * t)).re)
      (∑' j : ℤ, cf 0 j * ee (-((j : ℝ) * -((p : ℝ) ^ 2 * t)))).re := by
    have := Complex.hasSum_re hPPh
    simpa only [← sub_eq_add_neg] using this
  have hZ := W9Aux.re_tsum_le hcf (-((p : ℝ) ^ 2 * t)) hPPs
  have hg := ((hF0.mul_left (p : ℝ)).add (hs5.hasSum.mul_left
    ((p : ℝ) * η * S.card * K))).neg
  have hle := hasSum_le (fun (kk : ℤ) => W9Aux.row_re_ge hR hM hcf L hp hp2 hLp hLinj hχ hη0 hphase
    ((kk : ℝ) - (p : ℝ) ^ 2 * t) kk) hg (Complex.hasSum_re hRHS)
  rw [hXre] at hle
  set C := ∑' j : ℤ, (cf 0 j).re
  set Z := (∑' j : ℤ, cf 0 j * ee (-((j : ℝ) * -((p : ℝ) ^ 2 * t)))).re
  set W := ∑' kk : ℤ, 1 / (1 + ((kk : ℝ) - (p : ℝ) ^ 2 * t) ^ 2)
  set F := ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * Real.cos (2 * Real.pi * d * t)
  have hc0 : 0 ≤ (p : ℝ) * η * S.card * K := by positivity
  have h1 : (p : ℝ) * Z ≤ p * C := mul_le_mul_of_nonneg_left hZ hp0
  have h2 : (p : ℝ) * η * S.card * K * W ≤ (p : ℝ) * η * S.card * K * 5 :=
    mul_le_mul_of_nonneg_left h5 hc0
  have h3 : (p : ℝ) * (η * (5 * K * S.card)) ≤ p * (1 / T) :=
    mul_le_mul_of_nonneg_left hηK hp0
  have h4 : (p : ℝ) * η * S.card * K * 5 = (p : ℝ) * (η * (5 * K * S.card)) := by ring
  have h6 : -((p : ℝ) / 2 * (C + 1 / T)) = -((p : ℝ) * C + p * (1 / T)) / 2 := by ring
  rw [h6]
  linarith

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/W10.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.W10Aux

lemma summable_inv_one_add_sq : Summable (fun k : ℤ => 1 / (1 + (k:ℝ)^2)) := by
  refine Summable.of_norm_bounded (((summable_one_div_int_pow (p := 2)).mpr one_lt_two).add
    (hasSum_ite_eq (0:ℤ) (1:ℝ)).summable) ?_
  intro k
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, ite_false, add_zero]
    have : (0:ℝ) < (k:ℝ)^2 := by
      have : (k:ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    exact one_div_le_one_div_of_le this (by linarith)

/-- `∑_{k ∈ ℤ} 1/(1+k²)`. -/
noncomputable def S0 : ℝ := ∑' k : ℤ, 1 / (1 + (k:ℝ)^2)

lemma hasSum_S0 : HasSum (fun k : ℤ => 1 / (1 + (k:ℝ)^2)) S0 :=
  summable_inv_one_add_sq.hasSum

lemma S0_nonneg : 0 ≤ S0 := tsum_nonneg (fun k => by positivity)

lemma norm_chi {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) {d : ℤ}
    (hd : ¬ (p:ℤ) ∣ d) : ‖χ (d : ZMod (p^2))‖ = 1 := by
  have hu : IsUnit (d : ZMod (p^2)) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
    have : IsCoprime (p:ℤ) d := (Prime.coprime_iff_not_dvd hpz).mpr hd
    push_cast
    exact this.pow_left
  obtain ⟨u, hu⟩ := hu
  rw [← hu]
  have h1 : χ (u : ZMod (p^2)) ^ (orderOf u) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  have hpos : 0 < orderOf u := orderOf_pos u
  have h2 : ‖χ (u : ZMod (p^2))‖ ^ (orderOf u) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h2

lemma exists_ee {c : ℂ} (hc : ‖c‖ = 1) : ∃ z : ℝ, c = ee z := by
  refine ⟨Complex.arg c / (2 * Real.pi), ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [hc, Complex.ofReal_one, one_mul] at h
  rw [ee]
  conv_lhs => rw [← h]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

lemma hcs_of {E : Type*} [Zero E] {T : ℝ} {g : ℝ → E} (hg : ∀ x, T^2 < |x| → g x = 0) :
    HasCompactSupport g := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -T^2) (b := T^2))
  intro x hx
  apply hg
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  exact lt_abs.mpr (hx.elim (fun h => Or.inr (by linarith)) (fun h => Or.inl h))

/-- Lattice sums `m ∑_j 𝓕f(mj)` are `m 𝓕f(0) + O(K)`. -/
lemma lattice_bound {f : ℝ → ℂ} {Kf : ℝ} (hKf0 : 0 ≤ Kf) (hKf : ∀ y, ‖𝓕 f y‖ ≤ Kf / (1 + y^2))
    {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun k : ℤ => if (m:ℤ) ∣ k then 𝓕 f k else 0) ∧
    ‖(m:ℂ) * (∑' k : ℤ, if (m:ℤ) ∣ k then 𝓕 f k else 0) - (m:ℂ) * 𝓕 f 0‖ ≤ 2 * Kf * S0 := by
  have hdom : ∀ k : ℤ, ‖if (m:ℤ) ∣ k then 𝓕 f k else 0‖ ≤ Kf * (1 / (1 + (k:ℝ)^2)) := by
    intro k
    split_ifs
    · rw [mul_one_div]; exact hKf k
    · rw [norm_zero]; positivity
  have hsum : Summable (fun k : ℤ => if (m:ℤ) ∣ k then 𝓕 f k else 0) :=
    Summable.of_norm_bounded (hasSum_S0.summable.mul_left Kf) hdom
  refine ⟨hsum, ?_⟩
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hinj : Function.Injective (fun j : ℤ => (m:ℤ) * j) := by
    intro a b h
    have hm0 : (m:ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    exact mul_left_cancel₀ hm0 h
  have hre : (∑' j : ℤ, 𝓕 f ((m:ℝ) * (j:ℝ))) =
      ∑' k : ℤ, if (m:ℤ) ∣ k then 𝓕 f k else 0 := by
    rw [← hinj.tsum_eq (f := fun k : ℤ => if (m:ℤ) ∣ k then 𝓕 f k else 0)]
    · refine tsum_congr (fun j => ?_)
      rw [if_pos (dvd_mul_right _ _)]
      push_cast; rfl
    · intro k hk
      rw [Function.mem_support] at hk
      split_ifs at hk with h
      · obtain ⟨j, rfl⟩ := h; exact ⟨j, rfl⟩
      · exact absurd rfl hk
  rw [← hre]
  have hdom2 : ∀ j : ℤ, ‖𝓕 f ((m:ℝ) * (j:ℝ))‖ ≤ Kf * (1 / (1 + (j:ℝ)^2)) := by
    intro j
    refine (hKf _).trans ?_
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left hKf0 (by positivity)
    have : (j:ℝ)^2 ≤ ((m:ℝ) * j)^2 := by
      rw [mul_pow]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hm1)
    linarith
  have hs2 : Summable (fun j : ℤ => 𝓕 f ((m:ℝ) * (j:ℝ))) :=
    Summable.of_norm_bounded (hasSum_S0.summable.mul_left Kf) hdom2
  have hH : HasSum (fun j : ℤ => (m:ℂ) * (𝓕 f ((m:ℝ) * (j:ℝ)) - if j = 0 then 𝓕 f 0 else 0))
      ((m:ℂ) * (∑' j : ℤ, 𝓕 f ((m:ℝ) * (j:ℝ))) - (m:ℂ) * 𝓕 f 0) := by
    rw [← mul_sub]
    exact (hs2.hasSum.sub (hasSum_ite_eq (0:ℤ) (𝓕 f 0))).mul_left (m:ℂ)
  refine hH.norm_le_of_bounded (hasSum_S0.mul_left (2 * Kf)) (fun j => ?_)
  by_cases hj : j = 0
  · subst hj
    have e : (m:ℂ) * (𝓕 f ((m:ℝ) * ((0:ℤ):ℝ)) - if (0:ℤ) = 0 then 𝓕 f 0 else 0) = 0 := by simp
    rw [e, norm_zero]
    exact mul_nonneg (by linarith) (by positivity)
  · simp only [hj, ite_false, sub_zero]
    rw [norm_mul, Complex.norm_natCast]
    have hj1 : (1:ℝ) ≤ (j:ℝ)^2 := by
      have h := Int.one_le_abs hj
      have h' : (1:ℝ) ≤ |(j:ℝ)| := by exact_mod_cast h
      rw [← sq_abs]; nlinarith
    calc (m:ℝ) * ‖𝓕 f ((m:ℝ) * (j:ℝ))‖ ≤ m * (Kf / (1 + ((m:ℝ) * j)^2)) := by
          gcongr; exact hKf _
      _ = Kf * (m / (1 + ((m:ℝ) * j)^2)) := by ring
      _ ≤ Kf * (2 / (1 + (j:ℝ)^2)) := by
          apply mul_le_mul_of_nonneg_left _ hKf0
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (m:ℝ) ≤ (m:ℝ)^2 * (j:ℝ)^2 := by nlinarith
          have h2 : (m:ℝ) * (j:ℝ)^2 ≤ (m:ℝ)^2 * (j:ℝ)^2 := by nlinarith
          nlinarith
      _ = 2 * Kf * (1 / (1 + (j:ℝ)^2)) := by ring

/-- Poisson summation at `t = 0`. -/
lemma poisson0 (hP : PoissonStatement) {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ)
    (n : ℤ) {f : ℝ → ℂ} {Kf : ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hKf : ∀ y, ‖𝓕 f y‖ ≤ Kf / (1 + y^2)) :
    HasSum (fun d : ℤ => if (p:ℤ) ∣ d then 0 else
        f ((d:ℝ) / (p:ℝ)^2) * (χ (d : ZMod (p^2)))^n)
      (∑' k : ℤ, 𝓕 f k * rowSum p χ n k) := by
  obtain ⟨-, h⟩ := hP p hp χ n f Kf hf hfc hKf 0
  simp only [mul_zero, sub_zero, ee_zero, mul_one] at h
  exact h

/-- The row sum expansion `∑_k 𝓕f(k) rowSum(n,k)` equals `[n = 0](p² - p) 𝓕f(0) + O(p)`. -/
lemma row_bound (hR : RowSumStatement) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) {f : ℝ → ℂ} {Kf : ℝ}
    (hKf0 : 0 ≤ Kf) (hKf : ∀ y, ‖𝓕 f y‖ ≤ Kf / (1 + y^2)) {n : ℤ}
    (hn : n = 0 ∨ ¬ (p:ℤ) ∣ n) :
    ‖(∑' k : ℤ, 𝓕 f k * rowSum p χ n k) -
      (if n = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 f 0 else 0)‖ ≤ 5 * p * Kf * S0 := by
  obtain ⟨hRa, hRb, hRc, hRd, -⟩ := hR p hp hp2 χ hχ
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hS0 := S0_nonneg
  have hKS : 0 ≤ Kf * S0 := mul_nonneg hKf0 hS0
  by_cases hn0 : n = 0
  · subst hn0
    rw [if_pos rfl]
    have hpp : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    obtain ⟨hs1, hb1⟩ := lattice_bound hKf0 hKf hpp
    obtain ⟨hs2, hb2⟩ := lattice_bound hKf0 hKf hp.one_lt.le
    have heq : (fun k : ℤ => 𝓕 f k * rowSum p χ 0 k) = fun k =>
        ((p^2 : ℕ) : ℂ) * (if ((p^2:ℕ):ℤ) ∣ k then 𝓕 f k else 0) -
          (p:ℂ) * (if (p:ℤ) ∣ k then 𝓕 f k else 0) := by
      ext k; rw [hRc k]; push_cast; split_ifs <;> ring
    rw [heq, (hs1.mul_left _).tsum_sub (hs2.mul_left _), tsum_mul_left, tsum_mul_left]
    calc _ = ‖(((p^2:ℕ):ℂ) * (∑' k : ℤ, if ((p^2:ℕ):ℤ) ∣ k then 𝓕 f k else 0) -
            ((p^2:ℕ):ℂ) * 𝓕 f 0) -
          ((p:ℂ) * (∑' k : ℤ, if (p:ℤ) ∣ k then 𝓕 f k else 0) - (p:ℂ) * 𝓕 f 0)‖ := by
          congr 1; push_cast; ring
      _ ≤ 2 * Kf * S0 + 2 * Kf * S0 := norm_sub_le_of_le hb1 hb2
      _ ≤ 5 * p * Kf * S0 := by nlinarith
  · rw [if_neg hn0, sub_zero]
    have hn' : ¬ (p:ℤ) ∣ n := hn.resolve_left hn0
    have hbd : ∀ k : ℤ, ‖rowSum p χ n k‖ ≤ p := by
      intro k
      by_cases hk : (p:ℤ) ∣ k
      · rw [hRb n k hn' hk, norm_zero]; positivity
      · rw [hRa n k hn' hk, norm_mul, norm_mul, hRd n hn', norm_zpow, norm_inv, norm_chi hp χ hk]
        simp
    have h1 : ‖∑' k : ℤ, 𝓕 f k * rowSum p χ n k‖ ≤ p * Kf * S0 := by
      refine tsum_of_norm_bounded (hasSum_S0.mul_left (p * Kf)) (fun k => ?_)
      rw [norm_mul]
      calc ‖𝓕 f k‖ * ‖rowSum p χ n k‖ ≤ (Kf / (1 + (k:ℝ)^2)) * p :=
            mul_le_mul (hKf k) (hbd k) (norm_nonneg _) (by positivity)
        _ = p * Kf * (1 / (1 + (k:ℝ)^2)) := by ring
    calc _ ≤ p * Kf * S0 := h1
      _ ≤ 5 * p * Kf * S0 := by nlinarith

/-- The exponent `n_v = L · v`. -/
def nL {k : ℕ} (L : Fin (k + 1) → ℤ) (v : Fin (k + 1) → ℤ) : ℤ := ∑ i, L i * v i

lemma nL_neg {k : ℕ} (L v : Fin (k + 1) → ℤ) : nL L (-v) = - nL L v := by
  simp [nL, Finset.sum_neg_distrib]

lemma nL_zero {k : ℕ} (L : Fin (k + 1) → ℤ) : nL L 0 = 0 := by
  simp [nL]

/-- The summand `[p ∤ d] f(d/p²) χ(d)^n`. -/
noncomputable def gfun (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) (f : ℝ → ℂ) (d : ℤ) : ℂ :=
  if (p:ℤ) ∣ d then 0 else f ((d:ℝ) / (p:ℝ)^2) * (χ (d : ZMod (p^2)))^n

section Weights

variable {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)} {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}

lemma wgt_eq (L : Fin (k + 1) → ℤ) (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ) :
    wgt S cf L p χ d = (∑ v ∈ S, gfun p χ (nL L v) (cf v) d).re := by
  unfold wgt gfun
  by_cases hd : (p:ℤ) ∣ d
  · simp [hd]
  · simp only [hd, ite_false]
    rfl

lemma wgt_sq_eq (hS : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ}
    (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ) :
    (wgt S cf L p χ d) ^ 2 =
      (∑ v ∈ S, ∑ w ∈ S, gfun p χ (nL L v + nL L w) (fun x => cf v x * cf w x) d).re := by
  unfold wgt gfun
  by_cases hd : (p:ℤ) ∣ d
  · simp [hd]
  · simp only [hd, ite_false]
    set x := (d:ℝ) / (p:ℝ)^2
    set c := χ (d : ZMod (p^2)) with hcdef
    have hc : ‖c‖ = 1 := norm_chi hp χ hd
    have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
    obtain ⟨z, hz⟩ := exists_ee hc
    have him : (∑ v ∈ S, cf v x * c ^ (∑ i, L i * v i)).im = 0 := by
      have := (hS.range (fun i => z * L i) x).1
      convert this using 2
      unfold trigEval
      refine Finset.sum_congr rfl (fun v _ => ?_)
      congr 1
      rw [hz, ← ee_mul_intCast]
      congr 1
      dsimp only
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    set A := ∑ v ∈ S, cf v x * c ^ (∑ i, L i * v i) with hA
    have hsq : A.re ^ 2 = (A * A).re := by rw [Complex.mul_re, him]; ring
    rw [hsq, hA, Finset.sum_mul_sum]
    refine congrArg Complex.re
      (Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_)))
    simp only [nL]
    rw [zpow_add₀ hc0]; ring

lemma wgt_neg (hS : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ}
    {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) (d : ℤ) :
    wgt S cf L p χ (-d) = wgt S cf L p χ d := by
  unfold wgt
  have h1 : ((p:ℤ) ∣ -d) ↔ (p:ℤ) ∣ d := dvd_neg
  have h2 : χ ((-d : ℤ) : ZMod (p^2)) = χ (d : ZMod (p^2)) := by
    rw [Int.cast_neg, neg_eq_neg_one_mul, map_mul, hχ.1, one_mul]
  have h3 : ∀ v, cf v (((-d:ℤ):ℝ) / (p:ℝ)^2) = cf v ((d:ℝ)/(p:ℝ)^2) := by
    intro v; rw [Int.cast_neg, neg_div, hS.even]
  simp only [h1, h2, h3]

lemma wgt_zero (L : Fin (k + 1) → ℤ) (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) :
    wgt S cf L p χ 0 = 0 := by
  simp [wgt]

lemma wgt_large (hS : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ}
    (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ)
    (hd : (p:ℝ)^2 * T^2 < |(d:ℝ)|) : wgt S cf L p χ d = 0 := by
  unfold wgt
  split_ifs
  · rfl
  have hP : (0:ℝ) < (p:ℝ)^2 := by have := hp.pos; positivity
  have : ∀ v, cf v ((d:ℝ)/(p:ℝ)^2) = 0 := fun v => hS.supp v _ (by
    rw [abs_div, abs_of_pos hP, lt_div_iff₀ hP, mul_comm]; exact hd)
  simp [this]

end Weights

lemma sum_Icc_half {u : ℤ → ℝ} {s : ℝ} {N : ℕ} (hs : HasSum u s) (heven : ∀ d, u (-d) = u d)
    (h0 : u 0 = 0) (hN : ∀ n : ℕ, N < n → u n = 0) :
    ∑ d ∈ Finset.Icc 1 N, u d = s / 2 := by
  have e : ∀ n : ℕ, u n + u (-n) = 2 * u n := by intro n; rw [heven]; ring
  have h1 := hs.nat_add_neg
  rw [h0, add_zero] at h1
  have h2 : HasSum (fun n : ℕ => u n + u (-n)) (∑ n ∈ Finset.Icc 1 N, (u n + u (-(n:ℤ)))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have : n = 0 := by omega
      subst this; simp [h0]
    · rw [heven, hN n hn]; ring
  simp only [e] at h1 h2
  rw [← Finset.mul_sum] at h2
  have := h1.unique h2
  linarith

end ChowlaOpus.W10Aux

namespace ChowlaOpus

open W10Aux in
theorem w10Statement_holds (hR : RowSumStatement) (hP : PoissonStatement)
    (hD : FourierDecayStatement) : W10Statement := by
  intro k T K S cf hS hT L hL
  have hcont : ∀ v, Continuous (cf v) := fun v => (hS.smooth v).continuous
  have hcsv : ∀ v, HasCompactSupport (cf v) := fun v => hcs_of (hS.supp v)
  have hK0 : 0 ≤ K := by
    have h := hS.decay 0 0
    rw [show (1:ℝ) + 0^2 = 1 by norm_num, div_one] at h
    exact (norm_nonneg _).trans h
  have hpair : ∀ v w, ∃ Kp : ℝ, 0 ≤ Kp ∧
      ∀ y, ‖𝓕 (fun x => cf v x * cf w x) y‖ ≤ Kp / (1 + y^2) := fun v w =>
    hD _ ((hS.smooth v).mul (hS.smooth w))
      (hcs_of (fun x hx => by rw [hS.supp v x hx, zero_mul]))
  choose Kp hKp0 hKp using hpair
  have hS0 := S0_nonneg
  refine ⟨(S.card * (5 * K * S0)) / 2 + (∑ v ∈ S, ∑ w ∈ S, 5 * Kp v w * S0) / 2, ?_⟩
  intro p hp hp2 hn χ hχ N hN
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0:ℝ) ≤ p := by positivity
  -- arithmetic of the exponents `n_v`
  have hlt : ∀ m : ℤ, m ≠ 0 → |m| < p → ¬ (p:ℤ) ∣ m := fun m hm hlt hdvd =>
    hm (Int.eq_zero_of_abs_lt_dvd hdvd hlt)
  have hnL0 : ∀ v ∈ S, nL L v = 0 ↔ v = 0 := by
    intro v hv
    constructor
    · intro h
      refine hL v hv 0 hS.zero_mem ?_
      have h0 := nL_zero L
      unfold nL at h h0
      rw [h, h0]
    · rintro rfl; exact nL_zero L
  have hpair0 : ∀ v ∈ S, ∀ w ∈ S, nL L v + nL L w = 0 ↔ w = -v := by
    intro v hv w hw
    constructor
    · intro h
      refine hL w hw (-v) (hS.neg_mem v hv) ?_
      have h1 := nL_neg L v
      unfold nL at h h1
      rw [h1]; linarith
    · rintro rfl; rw [nL_neg]; ring
  have hdivv : ∀ v ∈ S, nL L v = 0 ∨ ¬ (p:ℤ) ∣ nL L v := by
    intro v hv
    by_cases h : nL L v = 0
    · exact Or.inl h
    · right
      apply hlt _ h
      have h1 : 2 * |nL L v| < (p:ℤ) := hn v hv
      linarith [abs_nonneg (nL L v)]
  have hdivvw : ∀ v ∈ S, ∀ w ∈ S, nL L v + nL L w = 0 ∨ ¬ (p:ℤ) ∣ (nL L v + nL L w) := by
    intro v hv w hw
    by_cases h : nL L v + nL L w = 0
    · exact Or.inl h
    · right
      apply hlt _ h
      have h1 : 2 * |nL L v| < (p:ℤ) := hn v hv
      have h2 : 2 * |nL L w| < (p:ℤ) := hn w hw
      have := abs_add_le (nL L v) (nL L w)
      linarith [abs_nonneg (nL L v), abs_nonneg (nL L w)]
  -- Poisson summation for the first and second moments
  have hmass : HasSum (fun d : ℤ => wgt S cf L p χ d)
      (∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k).re := by
    have h := hasSum_sum (fun v (_ : v ∈ S) =>
      poisson0 hP hp χ (nL L v) (hcont v) (hcsv v) (hS.decay v))
    convert Complex.hasSum_re h using 1
    ext d; rw [wgt_eq]; rfl
  have hsq : HasSum (fun d : ℤ => (wgt S cf L p χ d) ^ 2)
      (∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
        rowSum p χ (nL L v + nL L w) k).re := by
    have h := hasSum_sum (fun v (_ : v ∈ S) => hasSum_sum (fun w (_ : w ∈ S) =>
      poisson0 (f := fun x => cf v x * cf w x) hP hp χ (nL L v + nL L w)
        ((hcont v).mul (hcont w))
        (hcs_of (fun x hx => by rw [hS.supp v x hx, zero_mul])) (hKp v w)))
    convert Complex.hasSum_re h using 1
    ext d; rw [wgt_sq_eq hS L hp χ d]; rfl
  -- folding the sums over `ℤ` to `1 ≤ d ≤ N`
  have hlarge : ∀ n : ℕ, N < n → (p:ℝ)^2 * T^2 < |((n:ℤ):ℝ)| := by
    intro n hn'
    have : (N:ℝ) < n := by exact_mod_cast hn'
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; linarith
  have hsum1 := sum_Icc_half (N := N) hmass (wgt_neg hS L hχ) (wgt_zero L p χ)
    (fun n hn' => wgt_large hS L hp χ n (hlarge n hn'))
  have hsum2 := sum_Icc_half (N := N) hsq (fun d => by rw [wgt_neg hS L hχ])
    (by rw [wgt_zero]; ring) (fun n hn' => by rw [wgt_large hS L hp χ n (hlarge n hn')]; ring)
  -- main terms
  have hF0 : ∀ f : ℝ → ℂ, 𝓕 f 0 = ∫ x, f x := by
    intro f; rw [fourier_eq_ee]; simp [ee_zero]
  have hint0 : Integrable (fun x => cf 0 x) :=
    (hcont 0).integrable_of_hasCompactSupport (hcsv 0)
  have hintRe : Integrable (fun x => (cf 0 x).re) :=
    (Complex.continuous_re.comp (hcont 0)).integrable_of_hasCompactSupport
      (hcs_of (T := T) (fun x hx => by simp [hS.supp 0 x hx]))
  have hint2 : ∀ v, Integrable (fun x => ‖cf v x‖ ^ 2) := fun v =>
    (show Continuous (fun x => ‖cf v x‖ ^ 2) from
      (hcont v).norm.pow 2).integrable_of_hasCompactSupport
      (hcs_of (T := T) (fun x hx => by rw [hS.supp v x hx, norm_zero]; ring))
  have hI0 : (𝓕 (cf 0) 0).re = ∫ x, (cf 0 x).re := by
    rw [hF0]; exact (integral_re hint0).symm
  have hI2 : (∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0).re =
      ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2 := by
    rw [integral_finsetSum _ (fun v _ => hint2 v), Complex.re_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have e : ∀ x, cf v x * cf (-v) x = ((‖cf v x‖ ^ 2 : ℝ) : ℂ) := by
      intro x; rw [hS.conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [hF0, e, integral_complex_ofReal, Complex.ofReal_re]
  -- error terms
  have hP0 : ∀ v ∈ S, ‖(∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
      (if nL L v = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf v) 0 else 0)‖ ≤
        5 * p * K * S0 :=
    fun v hv => row_bound hR hp hp2 hχ hK0 (hS.decay v) (hdivv v hv)
  have hmassErr : ‖(∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
      (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf 0) 0‖ ≤ S.card * (5 * p * K * S0) := by
    have e : (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf 0) 0 = ∑ v ∈ S,
        (if nL L v = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf v) 0 else 0) := by
      rw [Finset.sum_eq_single 0]
      · rw [if_pos (nL_zero L)]
      · intro v hv hv0; rw [if_neg (fun h => hv0 ((hnL0 v hv).mp h))]
      · intro h; exact absurd hS.zero_mem h
    rw [e, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ v ∈ S, ‖(∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
          (if nL L v = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf v) 0 else 0)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ v ∈ S, 5 * p * K * S0 := Finset.sum_le_sum hP0
      _ = S.card * (5 * p * K * S0) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hP2 : ∀ v ∈ S, ∀ w ∈ S, ‖(∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
        rowSum p χ (nL L v + nL L w) k) -
      (if nL L v + nL L w = 0 then
        (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (fun x => cf v x * cf w x) 0 else 0)‖ ≤
        5 * p * Kp v w * S0 :=
    fun v hv w hw => row_bound hR hp hp2 hχ (hKp0 v w) (hKp v w) (hdivvw v hv w hw)
  have hsqErr : ‖(∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
        rowSum p χ (nL L v + nL L w) k) -
      (((p:ℝ)^2 - p : ℝ) : ℂ) * ∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0‖ ≤
      ∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0 := by
    have e : (((p:ℝ)^2 - p : ℝ) : ℂ) * ∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0 =
        ∑ v ∈ S, ∑ w ∈ S, (if nL L v + nL L w = 0 then
          (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (fun x => cf v x * cf w x) 0 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      rw [Finset.sum_eq_single (-v)]
      · rw [if_pos ((hpair0 v hv (-v) (hS.neg_mem v hv)).mpr rfl)]
      · intro w hw hwv; rw [if_neg (fun h => hwv ((hpair0 v hv w hw).mp h))]
      · intro h; exact absurd (hS.neg_mem v hv) h
    rw [e, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => ?_))
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun w hw => hP2 v hv w hw))
  -- conclusion
  have hb1 : |∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
      ((p:ℝ)^2 - p) / 2 * ∫ x, (cf 0 x).re| ≤ S.card * (5 * p * K * S0) / 2 := by
    rw [hsum1]
    have e : (∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k).re / 2 -
        ((p:ℝ)^2 - p) / 2 * ∫ x, (cf 0 x).re =
        ((∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
          (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf 0) 0).re / 2 := by
      rw [Complex.sub_re, Complex.re_ofReal_mul, hI0]; ring
    rw [e, abs_div, abs_two]
    gcongr
    exact (Complex.abs_re_le_norm _).trans hmassErr
  have hb2 : |∑ d ∈ Finset.Icc 1 N, (wgt S cf L p χ d) ^ 2 -
      ((p:ℝ)^2 - p) / 2 * ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2| ≤
      (∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0) / 2 := by
    rw [hsum2]
    have e : (∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
          rowSum p χ (nL L v + nL L w) k).re / 2 -
        ((p:ℝ)^2 - p) / 2 * ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2 =
        ((∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
          rowSum p χ (nL L v + nL L w) k) -
          (((p:ℝ)^2 - p : ℝ) : ℂ) * ∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0).re / 2 := by
      rw [Complex.sub_re, Complex.re_ofReal_mul, hI2]; ring
    rw [e, abs_div, abs_two]
    gcongr
    exact (Complex.abs_re_le_norm _).trans hsqErr
  have hE2 : 0 ≤ (∑ v ∈ S, ∑ w ∈ S, 5 * Kp v w * S0) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun w _ => by
      have := hKp0 v w; positivity))
  have hE2' : (∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0) =
      p * ∑ v ∈ S, ∑ w ∈ S, 5 * Kp v w * S0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  constructor
  · calc _ ≤ S.card * (5 * p * K * S0) / 2 := hb1
      _ ≤ _ := by nlinarith [mul_nonneg hp0 hE2]
  · have hsplit : ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * (1 - wgt S cf L p χ d) =
        ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
          ∑ d ∈ Finset.Icc 1 N, (wgt S cf L p χ d) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    have hint : ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2) =
        (∫ x, (cf 0 x).re) - ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2 :=
      integral_sub hintRe (integrable_finsetSum _ (fun v _ => hint2 v))
    rw [hsplit, hint]
    calc _ = |(∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
            ((p:ℝ)^2 - p) / 2 * ∫ x, (cf 0 x).re) -
          (∑ d ∈ Finset.Icc 1 N, (wgt S cf L p χ d) ^ 2 -
            ((p:ℝ)^2 - p) / 2 * ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2)| := by
          congr 1; ring
      _ ≤ _ := abs_sub _ _
      _ ≤ S.card * (5 * p * K * S0) / 2 + (∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0) / 2 :=
          add_le_add hb1 hb2
      _ = _ := by rw [hE2']; ring

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/AsmB.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.AsmBAux

open ChowlaOpus

lemma exists_ee_of_norm_eq_one (u : ℂ) (hu : ‖u‖ = 1) : ∃ z : ℝ, ee z = u := by
  refine ⟨Complex.arg u / (2 * Real.pi), ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, Complex.ofReal_one, one_mul] at h
  unfold ee
  conv_rhs => rw [← h]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

lemma norm_chi_eq_one {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℕ)
    (hd : ¬ p ∣ d) : ‖χ (d : ZMod (p ^ 2))‖ = 1 := by
  have hu : IsUnit (d : ZMod (p ^ 2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by norm_num)).mpr hd
  obtain ⟨u, hu⟩ := hu
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine Complex.norm_eq_one_of_pow_eq_one (n := orderOf u) ?_ (orderOf_pos u).ne'
  rw [← hu, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one,
    map_one]

lemma wgt_mem {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)}
    {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ} (hP : IsProfile T S cf K (T ^ 2))
    (L : Fin (k + 1) → ℤ) {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℕ) :
    0 ≤ wgt S cf L p χ d ∧ wgt S cf L p χ d ≤ 1 := by
  unfold wgt
  split_ifs with h
  · simp
  · have hd : ¬ p ∣ d := fun h' => h (Int.natCast_dvd_natCast.mpr h')
    obtain ⟨z, hz⟩ := exists_ee_of_norm_eq_one _ (norm_chi_eq_one hp χ d hd)
    have key : (∑ v ∈ S, cf v (((d : ℤ) : ℝ) / (p : ℝ) ^ 2) *
        (χ ((d : ℤ) : ZMod (p ^ 2))) ^ (∑ i, L i * v i)) =
        trigEval S (fun v => cf v (((d : ℤ) : ℝ) / (p : ℝ) ^ 2)) (fun i => z * L i) := by
      unfold trigEval
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Int.cast_natCast (R := ZMod (p ^ 2)), ← hz, ← ee_mul_intCast]
      congr 2
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [key]
    exact ⟨(hP.range _ _).2.1, (hP.range _ _).2.2⟩

lemma pos_inj {k : ℕ} (Sp : Finset (Fin (k + 1) → ℤ)) (L : Fin (k + 1) → ℤ)
    (hpos : ∀ v ∈ Sp, 0 < ∑ i, L i * v i)
    (hind : MultIndep (fun v : Sp => (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)) :
    ∀ v ∈ Sp, ∀ w ∈ Sp, ∑ i, L i * v i = ∑ i, L i * w i → v = w := by
  intro v hv w hw hvw
  by_contra hne
  set v' : Sp := ⟨v, hv⟩ with hv'
  set w' : Sp := ⟨w, hw⟩ with hw'
  have hne' : v' ≠ w' := fun h => hne (congrArg Subtype.val h)
  set x : Sp → ℚ := fun u => ((∑ i, L i * (u : Fin (k + 1) → ℤ) i).toNat : ℚ) with hx
  have hxw : x w' ≠ 0 := by
    simp only [hx, hw']
    have := hpos w hw
    exact_mod_cast (by omega : (∑ i, L i * w i).toNat ≠ 0)
  have hxvw : x v' = x w' := by simp only [hx, hv', hw', hvw]
  set e : Sp → ℤ := fun u => (if u = v' then 1 else 0) - (if u = w' then 1 else 0) with he
  have hterm : ∀ u, x u ^ e u =
      (if u = v' then x u else 1) * (if u = w' then (x u)⁻¹ else 1) := by
    intro u
    by_cases h1 : u = v'
    · rw [h1]; simp [he, hne']
    · by_cases h2 : u = w'
      · rw [h2]; simp [he, Ne.symm hne']
      · simp [he, h1, h2]
  have hprod : ∏ u, x u ^ e u = 1 := by
    rw [Finset.prod_congr rfl (fun u _ => hterm u), Finset.prod_mul_distrib,
      Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [hxvw, mul_inv_cancel₀ hxw]
  have he0 := hind e hprod
  have : e v' = 0 := by rw [he0]; rfl
  simp [he, hne'] at this

lemma L_inj {k : ℕ} {S : Finset (Fin (k + 1) → ℤ)}
    (hneg : ∀ v ∈ S, -v ∈ S) (hlab : ∀ v ∈ S, v ≠ 0 → v 0 ≠ 0) (L : Fin (k + 1) → ℤ)
    (hpos : ∀ v ∈ S.filter (fun v => 0 < v 0), 0 < ∑ i, L i * v i)
    (hind : MultIndep (fun v : S.filter (fun v => 0 < v 0) =>
      (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)) :
    ∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w := by
  have hpi := pos_inj _ L hpos hind
  have hnegf : ∀ v : Fin (k + 1) → ℤ, ∑ i, L i * (-v) i = -∑ i, L i * v i := by
    intro v; simp [Finset.sum_neg_distrib]
  have hf0 : ∑ i, L i * (0 : Fin (k + 1) → ℤ) i = 0 := by simp
  have hsign : ∀ v ∈ S, v = 0 ∨ (v ∈ S.filter (fun v => 0 < v 0)) ∨
      (-v ∈ S.filter (fun v => 0 < v 0)) := by
    intro v hv
    by_cases h : v = 0
    · exact Or.inl h
    · rcases lt_or_gt_of_ne (hlab v hv h) with hlt | hgt
      · right; right; exact Finset.mem_filter.mpr ⟨hneg v hv, by simp; omega⟩
      · right; left; exact Finset.mem_filter.mpr ⟨hv, hgt⟩
  intro v hv w hw hvw
  rcases hsign v hv with h1 | h1 | h1 <;> rcases hsign w hw with h2 | h2 | h2
  · rw [h1, h2]
  · exfalso; have := hpos w h2; rw [h1, hf0] at hvw; omega
  · exfalso; have := hpos _ h2; rw [hnegf] at this; rw [h1, hf0] at hvw; omega
  · exfalso; have := hpos v h1; rw [h2, hf0] at hvw; omega
  · exact hpi v h1 w h2 hvw
  · exfalso; have := hpos v h1; have := hpos _ h2; rw [hnegf] at this; omega
  · exfalso; have := hpos _ h1; rw [hnegf] at this; rw [h2, hf0] at hvw; omega
  · exfalso; have := hpos _ h1; rw [hnegf] at this; have := hpos w h2; omega
  · have := hpi _ h1 _ h2 (by rw [hnegf, hnegf, hvw]); exact neg_inj.mp this

end ChowlaOpus.AsmBAux

namespace ChowlaOpus

open ChowlaOpus.AsmBAux in
theorem weightsStatement_holds (hPr : ProfileStatement) (hC : CRTStatement)
    (hPh : PhaseStatement) (hR : RowSumStatement) (hM : MultStatement)
    (h9 : W9Statement) (h10 : W10Statement) : WeightsStatement := by
  obtain ⟨C, c, hC0, hc0, T₀, hPrT⟩ := hPr
  refine ⟨C + 1, c / 8, by linarith, by positivity, fun T₀' => ?_⟩
  set T : ℝ := max (max T₀ T₀') 3 with hTdef
  have hT3 : 3 ≤ T := le_max_right _ _
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hTT₀' : T₀' ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨T, hTT₀', hT3, ?_⟩
  obtain ⟨k, S, cf, K, hP, -, hsumle, hmass, hvar⟩ := hPrT T hTT₀
  have hTpos : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    have h1 : Real.exp 1 ≤ T := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) h1
  have hK : 0 ≤ K := by
    have h := hP.decay 0 0
    have h1 : (1 : ℝ) + 0 ^ 2 = 1 := by norm_num
    rw [h1, div_one] at h
    exact le_trans (norm_nonneg _) h
  -- positive half of the frequency set
  set Sp := S.filter (fun v => 0 < v 0) with hSp
  obtain ⟨L, hLpos, hLind⟩ := hC k Sp (fun v hv => (Finset.mem_filter.mp hv).2)
    (fun v hv w hw hvw => hP.nonprop v (Finset.mem_filter.mp hv).1 w
      (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2 hvw)
  have hinj := L_inj hP.neg_mem hP.label_ne L hLpos hLind
  obtain ⟨E, hE⟩ := h10 k T K S cf hP hTpos L hinj
  set η : ℝ := 1 / (T * (5 * K * S.card + 1)) with hηdef
  have hA : 0 ≤ 5 * K * (S.card : ℝ) := by positivity
  have hη : 0 < η := by positivity
  have hηK : η * (5 * K * S.card) ≤ 1 / T := by
    rw [hηdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hTpos]
    nlinarith
  obtain ⟨P₀, hP₀⟩ := hPh Sp (fun v => (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)
    (fun v => by have := hLpos v v.2; omega) hLind η hη
  intro p₀
  set D : ℕ := ∑ v ∈ S, (∑ i, L i * v i).natAbs with hD
  set M₁ : ℕ := ⌈8 * E * T / c⌉₊ with hM₁
  set M₂ : ℕ := ⌈2 * E * T ^ 3 / (C * Real.log T)⌉₊ with hM₂
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (p₀ + P₀ + 3 + (2 * D + 1) + M₁ + M₂)
  have hp3 : 3 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hbound : ∀ v ∈ S, 2 * |∑ i, L i * v i| < p := by
    intro v hv
    have h1 : (∑ i, L i * v i).natAbs ≤ D :=
      Finset.single_le_sum (f := fun v => (∑ i, L i * v i).natAbs)
        (fun _ _ => Nat.zero_le _) hv
    rw [Int.abs_eq_natAbs]
    omega
  obtain ⟨χ, hχ, hχphase⟩ := hP₀ p hp (by omega)
    (fun v => mult (2 * Real.pi * (v : Fin (k + 1) → ℤ) 0 / T)) (fun v => hM.1 _)
  have hphase : ∀ v ∈ S, v ≠ 0 →
      ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η := by
    have hposcase : ∀ v ∈ Sp,
        ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η := by
      intro v hv
      have h1 := hχphase ⟨v, hv⟩
      simp only at h1
      rw [Int.toNat_of_nonneg (hLpos v hv).le] at h1
      exact h1.le
    intro v hv hv0
    rcases lt_or_gt_of_ne (hP.label_ne v hv hv0) with hlt | hgt
    · have hmem : -v ∈ Sp := Finset.mem_filter.mpr ⟨hP.neg_mem v hv, by simp; omega⟩
      have h1 := hposcase (-v) hmem
      have e1 : ∑ i, L i * v i = -(∑ i, L i * (-v) i) := by simp [Finset.sum_neg_distrib]
      have e2 : mult (2 * Real.pi * v 0 / T) =
          starRingEnd ℂ (mult (2 * Real.pi * ((-v) 0 : ℤ) / T)) := by
        rw [← hM.2.2]; congr 1; simp; ring
      rw [e1, (hR p hp hp2 χ hχ).2.2.2.2, e2, ← map_sub, Complex.norm_conj]
      exact h1
    · exact hposcase v (Finset.mem_filter.mpr ⟨hv, hgt⟩)
  set N : ℕ := ⌈(p : ℝ) ^ 2 * T ^ 2⌉₊ with hNdef
  have hN : (p : ℝ) ^ 2 * T ^ 2 ≤ N := Nat.le_ceil _
  have hN' : (N : ℝ) < (p : ℝ) ^ 2 * T ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hq0 : (0 : ℝ) ≤ p := by positivity
  have hpT : (1 : ℝ) ≤ (p : ℝ) ^ 2 * T ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith))
  have hpp : 0 ≤ (p : ℝ) ^ 2 - p := by
    have : (p : ℝ) ^ 2 - p = p * (p - 1) := by ring
    rw [this]; exact mul_nonneg hq0 (by linarith)
  refine ⟨p, N, fun d => wgt S cf L p χ d, by omega, ?_, ?_, fun d => wgt_mem hP L hp χ d,
    ?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ N := le_trans hpT hN
    exact_mod_cast this
  · linarith
  · intro t
    have h := h9 k T K S cf hP hTpos L p hp hp2 hbound hinj χ hχ η hη.le hηK hphase N hN t
    refine le_trans ?_ h
    have h1 : ∑' j : ℤ, (cf 0 j).re + 1 / T ≤ (C + 1) * Real.log T / T := by
      have : 1 / T ≤ Real.log T / T := div_le_div_of_nonneg_right hlogT hTpos.le
      have : (C + 1) * Real.log T / T = C * Real.log T / T + Real.log T / T := by ring
      linarith
    have hX : 0 ≤ (C + 1) * Real.log T / T := by
      apply div_nonneg _ hTpos.le
      apply mul_nonneg (by linarith) (by linarith)
    have h2 : (p : ℝ) / 2 * (∑' j : ℤ, (cf 0 j).re + 1 / T) ≤ (C + 1) * p * Real.log T / T := by
      calc (p : ℝ) / 2 * (∑' j : ℤ, (cf 0 j).re + 1 / T)
          ≤ (p : ℝ) / 2 * ((C + 1) * Real.log T / T) := by gcongr
        _ ≤ (p : ℝ) * ((C + 1) * Real.log T / T) := by
          have := mul_nonneg hq0 hX; linarith
        _ = (C + 1) * p * Real.log T / T := by ring
    linarith
  · have h := (hE p hp hp2 hbound χ hχ N hN).1
    rw [abs_le] at h
    have hM1 : 8 * E * T / c ≤ p :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : M₁ ≤ p))
    rw [div_le_iff₀ hc0] at hM1
    have hTI : c ≤ T * ∫ x, (cf 0 x).re := by
      rw [div_le_iff₀ hTpos] at hmass; linarith
    beta_reduce
    rw [div_le_iff₀ hTpos]
    have k0 : 0 ≤ (∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
        ((p : ℝ) ^ 2 - p) / 2 * (∫ x, (cf 0 x).re) + E * p) * T :=
      mul_nonneg (by linarith [h.1]) hTpos.le
    have k1' : 0 ≤ T * (∫ x, (cf 0 x).re) - c := by linarith
    have k1 : 0 ≤ ((p : ℝ) ^ 2 - p) * (T * (∫ x, (cf 0 x).re) - c) := mul_nonneg hpp k1'
    have k2' : 0 ≤ (p : ℝ) * c - 8 * E * T := by linarith
    have k2 : 0 ≤ (p : ℝ) * ((p : ℝ) * c - 8 * E * T) := mul_nonneg hq0 k2'
    have k3' : 0 ≤ (p : ℝ) - 2 := by linarith
    have k3 : 0 ≤ (p : ℝ) * ((p : ℝ) - 2) * c := mul_nonneg (mul_nonneg hq0 k3') hc0.le
    linarith
  · have h := (hE p hp hp2 hbound χ hχ N hN).2
    rw [abs_le] at h
    have hCl : 0 < C * Real.log T := mul_pos hC0 (by linarith)
    have hM2 : 2 * E * T ^ 3 / (C * Real.log T) ≤ p :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : M₂ ≤ p))
    rw [div_le_iff₀ hCl] at hM2
    set V := ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2) with hV
    have hT3pos : 0 < T ^ 3 := by positivity
    have hVT : V * T ^ 3 ≤ C * Real.log T := by
      rw [le_div_iff₀ hT3pos] at hvar; linarith
    beta_reduce
    rw [le_div_iff₀ hT3pos]
    have k0 : 0 ≤ (E * p - ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * (1 - wgt S cf L p χ d) +
        ((p : ℝ) ^ 2 - p) / 2 * V) * T ^ 3 :=
      mul_nonneg (by linarith [h.2]) hT3pos.le
    have k1' : 0 ≤ C * Real.log T - V * T ^ 3 := by linarith
    have k1 : 0 ≤ ((p : ℝ) ^ 2 - p) * (C * Real.log T - V * T ^ 3) := mul_nonneg hpp k1'
    have k2' : 0 ≤ (p : ℝ) * (C * Real.log T) - 2 * E * T ^ 3 := by linarith
    have k2 : 0 ≤ (p : ℝ) * ((p : ℝ) * (C * Real.log T) - 2 * E * T ^ 3) := mul_nonneg hq0 k2'
    have k3 : 0 ≤ (p : ℝ) * (C * Real.log T) := mul_nonneg hq0 hCl.le
    have k4' : 0 ≤ Real.log T := by linarith
    have k4 : 0 ≤ (p : ℝ) ^ 2 * Real.log T := mul_nonneg (sq_nonneg _) k4'
    linarith

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Partial.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace PartialAux

open Finset

/-- Real sign attached to a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Row sum of `a` against the sign vector `σ`. -/
noncomputable def rowS {v : ℕ} (a : Fin v → ℝ) (σ : Fin v → Bool) : ℝ := ∑ j, a j * sgn (σ j)

lemma sum_exp_rowS_le {v : ℕ} (a : Fin v → ℝ) (ha : ∀ j, |a j| ≤ 1) (t : ℝ) :
    ∑ σ : Fin v → Bool, Real.exp (t * rowS a σ) ≤ 2 ^ v * Real.exp (t ^ 2 * v / 2) := by
  have h1 : ∀ σ : Fin v → Bool,
      Real.exp (t * rowS a σ) = ∏ j, Real.exp (t * (a j * sgn (σ j))) := by
    intro σ
    rw [rowS, Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun j (b : Bool) => Real.exp (t * (a j * sgn b)))]
  have h2 : ∀ j, ∑ b : Bool, Real.exp (t * (a j * sgn b)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
    intro j
    have hc : ∑ b : Bool, Real.exp (t * (a j * sgn b)) = 2 * Real.cosh (t * a j) := by
      rw [Fintype.sum_bool]
      show Real.exp (t * (a j * 1)) + Real.exp (t * (a j * -1)) = _
      have e1 : t * (a j * 1) = t * a j := by ring
      have e2 : t * (a j * -1) = -(t * a j) := by ring
      rw [Real.cosh_eq, e1, e2]
      ring
    rw [hc]
    have hcosh := Real.cosh_le_exp_half_sq (t * a j)
    have hsq : (t * a j) ^ 2 / 2 ≤ t ^ 2 / 2 := by
      have haj : a j ^ 2 ≤ 1 := by
        have := abs_le.mp (ha j)
        nlinarith
      rw [mul_pow]
      nlinarith [sq_nonneg t]
    have := Real.exp_le_exp.mpr hsq
    linarith
  calc ∏ j, ∑ b : Bool, Real.exp (t * (a j * sgn b))
      ≤ ∏ _j : Fin v, (2 * Real.exp (t ^ 2 / 2)) :=
        Finset.prod_le_prod (fun j _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
          (fun j _ => h2 j)
    _ = 2 ^ v * Real.exp (t ^ 2 * v / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring

lemma sum_exp_abs_rowS_le {v : ℕ} (a : Fin v → ℝ) (ha : ∀ j, |a j| ≤ 1) (t : ℝ) :
    ∑ σ : Fin v → Bool, Real.exp (t * |rowS a σ|) ≤ 2 * 2 ^ v * Real.exp (t ^ 2 * v / 2) := by
  have h : ∀ σ, Real.exp (t * |rowS a σ|) ≤
      Real.exp (t * rowS a σ) + Real.exp ((-t) * rowS a σ) := by
    intro σ
    rcases abs_cases (rowS a σ) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      linarith [Real.exp_pos ((-t) * rowS a σ)]
    · rw [h1]
      have : t * -rowS a σ = -t * rowS a σ := by ring
      rw [this]
      linarith [Real.exp_pos (t * rowS a σ)]
  calc ∑ σ, Real.exp (t * |rowS a σ|)
      ≤ ∑ σ, (Real.exp (t * rowS a σ) + Real.exp ((-t) * rowS a σ)) :=
        Finset.sum_le_sum (fun σ _ => h σ)
    _ = ∑ σ, Real.exp (t * rowS a σ) + ∑ σ, Real.exp ((-t) * rowS a σ) :=
        Finset.sum_add_distrib
    _ ≤ 2 ^ v * Real.exp (t ^ 2 * v / 2) + 2 ^ v * Real.exp ((-t) ^ 2 * v / 2) :=
        add_le_add (sum_exp_rowS_le a ha t) (sum_exp_rowS_le a ha (-t))
    _ = 2 * 2 ^ v * Real.exp (t ^ 2 * v / 2) := by rw [neg_sq]; ring

lemma abs_round_le {Δ w X : ℝ} (hΔ : 0 < Δ) (hw : 0 < w) (h : w ≤ Δ ^ 2) :
    |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ Real.exp (Δ / w * |X| - Δ ^ 2 / w) := by
  by_cases hX : |X| < Δ
  · have h0 : round (X / (2 * Δ)) = 0 := by
      rw [round_eq_zero_iff, Set.mem_Ico]
      have := abs_lt.mp hX
      constructor
      · rw [le_div_iff₀ (by positivity)]
        linarith
      · rw [div_lt_iff₀ (by positivity)]
        linarith
    rw [h0, Int.cast_zero, abs_zero]
    positivity
  · push Not at hX
    have h1 : |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ |X| / Δ := by
      have h2 := abs_sub_round (X / (2 * Δ))
      have h3 : |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤
          |X / (2 * Δ)| + |X / (2 * Δ) - round (X / (2 * Δ))| := by
        calc |((round (X / (2 * Δ)) : ℤ) : ℝ)|
            = |X / (2 * Δ) - (X / (2 * Δ) - round (X / (2 * Δ)))| := by ring_nf
          _ ≤ _ := abs_sub _ _
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Δ)] at h3
      have h4 : 1 / 2 ≤ |X| / (2 * Δ) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ |X| / (2 * Δ) + 1 / 2 := by linarith
        _ ≤ |X| / (2 * Δ) + |X| / (2 * Δ) := by linarith
        _ = |X| / Δ := by field_simp; ring
    have hu : 1 ≤ |X| / Δ := by
      rw [le_div_iff₀ hΔ]
      linarith
    have hD : 1 ≤ Δ ^ 2 / w := by
      rw [le_div_iff₀ hw]
      linarith
    have heq : Δ / w * |X| - Δ ^ 2 / w = (Δ ^ 2 / w) * (|X| / Δ - 1) := by
      field_simp
    rw [heq]
    calc |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ |X| / Δ := h1
      _ ≤ (|X| / Δ - 1) + 1 := by linarith
      _ ≤ Real.exp (|X| / Δ - 1) := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

lemma sum_abs_round_le {v : ℕ} (hv : 0 < v) (a : Fin v → ℝ) (ha : ∀ j, |a j| ≤ 1) {Δ : ℝ}
    (hΔ : 0 < Δ) (h : (v : ℝ) ≤ Δ ^ 2) :
    ∑ σ : Fin v → Bool, |((round (rowS a σ / (2 * Δ)) : ℤ) : ℝ)| ≤
      2 * 2 ^ v * Real.exp (-(Δ ^ 2 / (2 * v))) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have e : -(Δ ^ 2 / v) + (Δ / v) ^ 2 * v / 2 = -(Δ ^ 2 / (2 * v)) := by
    field_simp
    ring
  calc ∑ σ : Fin v → Bool, |((round (rowS a σ / (2 * Δ)) : ℤ) : ℝ)|
      ≤ ∑ σ : Fin v → Bool, Real.exp (Δ / v * |rowS a σ| - Δ ^ 2 / v) :=
        Finset.sum_le_sum (fun σ _ => abs_round_le hΔ hv' h)
    _ = Real.exp (-(Δ ^ 2 / v)) * ∑ σ : Fin v → Bool, Real.exp (Δ / v * |rowS a σ|) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(Δ ^ 2 / v)) * (2 * 2 ^ v * Real.exp ((Δ / v) ^ 2 * v / 2)) :=
        mul_le_mul_of_nonneg_left (sum_exp_abs_rowS_le a ha _) (Real.exp_pos _).le
    _ = 2 * 2 ^ v * Real.exp (-(Δ ^ 2 / v) + (Δ / v) ^ 2 * v / 2) := by
        rw [Real.exp_add]
        ring
    _ = 2 * 2 ^ v * Real.exp (-(Δ ^ 2 / (2 * v))) := by rw [e]

lemma sum_exp_neg_abs_le {β : ℝ} (hβ : 0 < β) (T : Finset ℤ) :
    ∑ k ∈ T, Real.exp (-(β * |(k : ℝ)|)) ≤ (1 + Real.exp (-β)) / (1 - Real.exp (-β)) := by
  set r := Real.exp (-β) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hf : ∀ k : ℤ, Real.exp (-(β * |(k : ℝ)|)) = r ^ k.natAbs := by
    intro k
    rw [hr, ← Real.exp_nat_mul, Nat.cast_natAbs, Int.cast_abs]
    congr 1
    ring
  have hS : HasSum (fun k : ℤ => r ^ k.natAbs) ((1 - r)⁻¹ + r * (1 - r)⁻¹) := by
    apply HasSum.of_nat_of_neg_add_one
    · simpa using hasSum_geometric_of_lt_one hr0 hr1
    · change HasSum (fun n : ℕ => r ^ (-((n : ℤ) + 1)).natAbs) (r * (1 - r)⁻¹)
      have hfun : (fun n : ℕ => r ^ (-((n : ℤ) + 1)).natAbs) = fun n => r * r ^ n := by
        funext n
        have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
        rw [hn, pow_succ, mul_comm]
      rw [hfun]
      exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := sum_le_hasSum T (fun k _ => by positivity) hS
  simp_rw [hf]
  calc ∑ k ∈ T, r ^ k.natAbs ≤ (1 - r)⁻¹ + r * (1 - r)⁻¹ := hle
    _ = (1 + r) / (1 - r) := by
        have : 1 - r ≠ 0 := by linarith
        field_simp

lemma weighted_pigeonhole {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω] (M : ℕ)
    (b : Ω → Fin M → ℤ) {β : ℝ} (hβ : 0 < β) :
    ∃ p₀, (Fintype.card Ω : ℝ) *
        Real.exp (-(β / Fintype.card Ω * ∑ p, ∑ i, |(b p i : ℝ)|)) ≤
      (univ.filter (fun p => b p = b p₀)).card *
        ((1 + Real.exp (-β)) / (1 - Real.exp (-β))) ^ M := by
  set N := Fintype.card Ω with hNdef
  have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  set q := (1 + Real.exp (-β)) / (1 - Real.exp (-β)) with hq
  set W : (Fin M → ℤ) → ℝ := fun c => Real.exp (-(β * ∑ i, |(c i : ℝ)|)) with hW
  have hW0 : ∀ c, 0 ≤ W c := fun c => (Real.exp_pos _).le
  -- Jensen
  have hJ : (N : ℝ) * Real.exp (-(β / N * ∑ p, ∑ i, |(b p i : ℝ)|)) ≤ ∑ p, W (b p) := by
    have hw1 : ∑ _p : Ω, (1 / N : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, ← hNdef, nsmul_eq_mul]
      field_simp
    have hjen := (convexOn_exp).map_sum_le (t := univ) (w := fun _ => (1 / N : ℝ))
      (p := fun p => -(β * ∑ i, |(b p i : ℝ)|))
      (fun _ _ => by positivity) hw1 (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hjen
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hjen
    have e : 1 / (N : ℝ) * ∑ p, -(β * ∑ i, |(b p i : ℝ)|) =
        -(β / N * ∑ p, ∑ i, |(b p i : ℝ)|) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
    rw [e] at hjen
    calc (N : ℝ) * Real.exp (-(β / N * ∑ p, ∑ i, |(b p i : ℝ)|))
        ≤ (N : ℝ) * (1 / N * ∑ p, W (b p)) := mul_le_mul_of_nonneg_left hjen hN.le
      _ = ∑ p, W (b p) := by field_simp
  -- fibres
  set I := univ.image b with hI
  have hIne : I.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  obtain ⟨c₀, hc₀I, hc₀max⟩ :=
    I.exists_max_image (fun c => (univ.filter (fun p => b p = c)).card) hIne
  obtain ⟨p₀, -, hp₀⟩ := Finset.mem_image.mp hc₀I
  refine ⟨p₀, ?_⟩
  rw [hp₀]
  have hfib : ∑ p, W (b p) = ∑ c ∈ I, ((univ.filter (fun p => b p = c)).card : ℝ) * W c := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := I) (g := b)
      (fun p _ => Finset.mem_image_of_mem b (Finset.mem_univ p))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hbox : ∑ c ∈ I, W c ≤ q ^ M := by
    set T : Fin M → Finset ℤ := fun i => I.image (fun c => c i) with hT
    set P : Finset (Fin M → ℤ) := Fintype.piFinset T with hP
    have hsub : I ⊆ P := by
      intro c hc
      rw [hP, Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ hc
    have hWp : ∀ c : Fin M → ℤ, W c = ∏ i : Fin M, Real.exp (-(β * |((c i : ℤ) : ℝ)|)) := by
      intro c
      simp only [hW]
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    calc ∑ c ∈ I, W c ≤ ∑ c ∈ P, W c :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => hW0 c)
      _ = ∑ c ∈ P, ∏ i : Fin M, Real.exp (-(β * |((c i : ℤ) : ℝ)|)) :=
          Finset.sum_congr rfl (fun c _ => hWp c)
      _ = ∏ i : Fin M, ∑ k ∈ T i, Real.exp (-(β * |((k : ℤ) : ℝ)|)) :=
          (Finset.prod_univ_sum T (fun _ k => Real.exp (-(β * |((k : ℤ) : ℝ)|)))).symm
      _ ≤ ∏ _i : Fin M, q :=
          Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
            (fun i _ => sum_exp_neg_abs_le hβ _)
      _ = q ^ M := by simp
  calc (N : ℝ) * Real.exp (-(β / N * ∑ p, ∑ i, |(b p i : ℝ)|)) ≤ ∑ p, W (b p) := hJ
    _ = ∑ c ∈ I, ((univ.filter (fun p => b p = c)).card : ℝ) * W c := hfib
    _ ≤ ∑ c ∈ I, ((univ.filter (fun p => b p = c₀)).card : ℝ) * W c :=
        Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_right
          (by exact_mod_cast hc₀max c hc) (hW0 c))
    _ = ((univ.filter (fun p => b p = c₀)).card : ℝ) * ∑ c ∈ I, W c := by
        rw [Finset.mul_sum]
    _ ≤ ((univ.filter (fun p => b p = c₀)).card : ℝ) * q ^ M :=
        mul_le_mul_of_nonneg_left hbox (by positivity)

lemma hamming_ball_card_le {v : ℕ} (σ : Fin v → Bool) :
    ((univ.filter (fun τ : Fin v → Bool =>
        10 * (univ.filter (fun j => σ j ≠ τ j)).card < v)).card : ℝ) ≤
      ((1 + (4 / 5 : ℝ) ^ 10) / (4 / 5)) ^ v := by
  set s : ℝ := (4 / 5 : ℝ) ^ 10 with hs
  set B := univ.filter (fun τ : Fin v → Bool =>
    10 * (univ.filter (fun j => σ j ≠ τ j)).card < v) with hB
  have hprod : ∀ τ : Fin v → Bool, s ^ (univ.filter (fun j => σ j ≠ τ j)).card =
      ∏ j, (if σ j ≠ τ j then s else 1) := by
    intro τ
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hsum : ∑ τ : Fin v → Bool, s ^ (univ.filter (fun j => σ j ≠ τ j)).card =
      (1 + s) ^ v := by
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun j (c : Bool) => if σ j ≠ c then s else 1)]
    have : ∀ j, ∑ c : Bool, (if σ j ≠ c then s else 1) = 1 + s := by
      intro j
      rw [Fintype.sum_bool]
      cases σ j <;> simp [add_comm]
    rw [Finset.prod_congr rfl (fun j _ => this j), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hlow : ∀ τ ∈ B, (4 / 5 : ℝ) ^ v ≤ s ^ (univ.filter (fun j => σ j ≠ τ j)).card := by
    intro τ hτ
    have h := (Finset.mem_filter.mp hτ).2
    rw [hs, ← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmain : (B.card : ℝ) * (4 / 5) ^ v ≤ (1 + s) ^ v := by
    calc (B.card : ℝ) * (4 / 5) ^ v = ∑ τ ∈ B, (4 / 5 : ℝ) ^ v := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ τ ∈ B, s ^ (univ.filter (fun j => σ j ≠ τ j)).card := Finset.sum_le_sum hlow
      _ ≤ ∑ τ : Fin v → Bool, s ^ (univ.filter (fun j => σ j ≠ τ j)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by positivity)
      _ = (1 + s) ^ v := hsum
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact hmain

lemma key_ineq {v M : ℝ} (hv : 0 < v) (hvM : v ≤ M) :
    Real.log ((40 * M + v) / v) * (2 * M * Real.exp (-(50 * Real.log (2 * M / v)))) ≤
      v / 20 := by
  have hM : 0 < M := by linarith
  set y := 2 * M / v with hy
  have hy2 : 2 ≤ y := by
    rw [hy, le_div_iff₀ hv]
    linarith
  have hy0 : 0 < y := by linarith
  have hMy : M = y * v / 2 := by
    rw [hy]
    field_simp
  have hlog : Real.log ((40 * M + v) / v) ≤ 20 * y := by
    have := Real.log_le_sub_one_of_pos (show 0 < (40 * M + v) / v by positivity)
    have e : (40 * M + v) / v - 1 = 20 * y := by
      rw [hy]
      field_simp
      ring
    linarith
  have hexp : Real.exp (-(50 * Real.log y)) = 1 / y ^ 50 := by
    rw [Real.exp_neg, show (50 : ℝ) * Real.log y = Real.log (y ^ 50) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div]
  rw [hexp]
  have hpow : 400 * y ^ 2 ≤ y ^ 50 := by
    have h0 : (2 : ℝ) ^ 48 ≤ y ^ 48 := pow_le_pow_left₀ (by norm_num) hy2 48
    have h1 : (2 : ℝ) ^ 48 * y ^ 2 ≤ y ^ 48 * y ^ 2 :=
      mul_le_mul_of_nonneg_right h0 (sq_nonneg y)
    have h2 : 400 * y ^ 2 ≤ (2 : ℝ) ^ 48 * y ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg y)
    have e : y ^ 50 = y ^ 48 * y ^ 2 := by ring
    linarith
  have hpos : 0 ≤ 2 * M * (1 / y ^ 50) := by positivity
  have hvy := mul_le_mul_of_nonneg_left hpow hv.le
  calc Real.log ((40 * M + v) / v) * (2 * M * (1 / y ^ 50))
      ≤ 20 * y * (2 * M * (1 / y ^ 50)) := mul_le_mul_of_nonneg_right hlog hpos
    _ = 20 * v * y ^ 2 / y ^ 50 := by
        rw [hMy]
        field_simp
    _ ≤ v / 20 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

lemma q_pow_le {v : ℝ} (hv : 0 < v) {M : ℕ} (hM : 0 < M) :
    ((1 + Real.exp (-Real.log ((40 * M + v) / v))) /
        (1 - Real.exp (-Real.log ((40 * M + v) / v)))) ^ M ≤ Real.exp (v / 20) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hM'
  have hden : (40 * M + v : ℝ) ≠ 0 := by positivity
  have hr : Real.exp (-Real.log ((40 * M + v) / v)) = v / (40 * M + v) := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  rw [hr]
  have h1 : 1 - v / (40 * M + v) = 40 * M / (40 * M + v) := by
    field_simp
    ring
  have h2 : 1 + v / (40 * M + v) = (40 * M + 2 * v) / (40 * M + v) := by
    field_simp
    ring
  have e : (1 + v / (40 * M + v)) / (1 - v / (40 * M + v)) = v / (20 * M) + 1 := by
    rw [h1, h2]
    field_simp
    ring
  rw [e]
  calc (v / (20 * M) + 1) ^ M ≤ Real.exp (v / (20 * M)) ^ M :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) M
    _ = Real.exp (v / 20) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp

lemma final_ineq {v : ℕ} (hv : 1 ≤ v) :
    ((1 + (4 / 5 : ℝ) ^ 10) / (4 / 5)) ^ v < 2 ^ v * Real.exp (-(v / 10 : ℝ)) := by
  have he : Real.exp (-(v / 10 : ℝ)) = Real.exp (-(1 / 10)) ^ v := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, ← mul_pow]
  have h1 : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 10)) := by
    have := Real.add_one_le_exp (-(1 / 10) : ℝ)
    linarith
  apply pow_lt_pow_left₀ _ (by positivity) (by omega)
  calc (1 + (4 / 5 : ℝ) ^ 10) / (4 / 5) < 2 * (9 / 10) := by norm_num
    _ ≤ 2 * Real.exp (-(1 / 10)) := by linarith

end PartialAux

open PartialAux in
theorem partialColoringStatement_holds : PartialColoringStatement := by
  refine ⟨10, by norm_num, ?_⟩
  intro M v hv hvM A hA
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hvM' : (v : ℝ) ≤ M := by exact_mod_cast hvM
  have hMpos : 0 < M := by omega
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  set L := Real.log (2 * M / v) with hL
  have h2le : (2 : ℝ) ≤ 2 * M / v := by
    rw [le_div_iff₀ hvpos]
    linarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) h2le
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLpos : 0 < L := by linarith
  set Δ := 10 * Real.sqrt (v * L) with hΔ
  have hΔpos : 0 < Δ := by positivity
  have hΔsq : Δ ^ 2 = 100 * (v * L) := by
    rw [hΔ, mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hvΔ : (v : ℝ) ≤ Δ ^ 2 := by
    rw [hΔsq]
    nlinarith
  set b : (Fin v → Bool) → Fin M → ℤ := fun σ i => round (rowS (A i) σ / (2 * Δ)) with hb
  set β := Real.log ((40 * M + v) / v) with hβdef
  have hβ : 0 < β := Real.log_pos (by rw [lt_div_iff₀ hvpos]; linarith)
  obtain ⟨σ₀, hσ₀⟩ := weighted_pigeonhole M b hβ
  have hcard : (Fintype.card (Fin v → Bool) : ℝ) = 2 ^ v := by simp
  rw [hcard] at hσ₀
  have hrow : ∀ i, ∑ σ, |(b σ i : ℝ)| ≤ 2 * 2 ^ v * Real.exp (-(50 * L)) := by
    intro i
    have := sum_abs_round_le hv (A i) (hA i) hΔpos hvΔ
    have e : Δ ^ 2 / (2 * v) = 50 * L := by
      rw [hΔsq]
      field_simp
      ring
    rw [e] at this
    exact this
  have hS : ∑ σ, ∑ i, |(b σ i : ℝ)| ≤ M * (2 * 2 ^ v * Real.exp (-(50 * L))) := by
    rw [Finset.sum_comm]
    calc ∑ i, ∑ σ, |(b σ i : ℝ)| ≤ ∑ _i : Fin M, (2 * 2 ^ v * Real.exp (-(50 * L))) :=
          Finset.sum_le_sum (fun i _ => hrow i)
      _ = M * (2 * 2 ^ v * Real.exp (-(50 * L))) := by simp
  have havg : β / 2 ^ v * ∑ σ, ∑ i, |(b σ i : ℝ)| ≤ v / 20 := by
    calc β / 2 ^ v * ∑ σ, ∑ i, |(b σ i : ℝ)|
        ≤ β / 2 ^ v * (M * (2 * 2 ^ v * Real.exp (-(50 * L)))) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = β * (2 * M * Real.exp (-(50 * L))) := by
          field_simp
      _ ≤ v / 20 := key_ineq hvpos hvM'
  have hq := q_pow_le hvpos hMpos
  set F := Finset.univ.filter (fun σ => b σ = b σ₀) with hF
  have hFbig : (2 : ℝ) ^ v * Real.exp (-(v / 10 : ℝ)) ≤ F.card := by
    have h1 : (2 : ℝ) ^ v * Real.exp (-(v / 20 : ℝ)) ≤ F.card * Real.exp (v / 20) := by
      calc (2 : ℝ) ^ v * Real.exp (-(v / 20 : ℝ))
          ≤ 2 ^ v * Real.exp (-(β / 2 ^ v * ∑ σ, ∑ i, |(b σ i : ℝ)|)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
        _ ≤ _ := hσ₀
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
    have h2 : Real.exp (-(v / 10 : ℝ)) =
        Real.exp (-(v / 20 : ℝ)) * Real.exp (-(v / 20 : ℝ)) := by
      rw [← Real.exp_add]
      ring_nf
    have h3 : Real.exp (v / 20) * Real.exp (-(v / 20 : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (2 : ℝ) ^ v * Real.exp (-(v / 10 : ℝ))
        = (2 ^ v * Real.exp (-(v / 20 : ℝ))) * Real.exp (-(v / 20 : ℝ)) := by
          rw [h2]
          ring
      _ ≤ (F.card * Real.exp (v / 20)) * Real.exp (-(v / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = F.card := by rw [mul_assoc, h3, mul_one]
  have hball := hamming_ball_card_le σ₀
  have hfin := final_ineq hv
  set B := Finset.univ.filter (fun τ : Fin v → Bool =>
    10 * (Finset.univ.filter (fun j => σ₀ j ≠ τ j)).card < v) with hB
  have hlt : B.card < F.card := by
    have : (B.card : ℝ) < F.card := by linarith
    exact_mod_cast this
  obtain ⟨σ₁, hσ₁F, hσ₁B⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hbeq : b σ₁ = b σ₀ := (Finset.mem_filter.mp hσ₁F).2
  have hfar : v ≤ 10 * (Finset.univ.filter (fun j => σ₀ j ≠ σ₁ j)).card := by
    have : ¬ (10 * (Finset.univ.filter (fun j => σ₀ j ≠ σ₁ j)).card < v) := fun h =>
      hσ₁B (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  set x : Fin v → ℤ := fun j => if σ₀ j = σ₁ j then 0 else (if σ₀ j then 1 else -1) with hx
  refine ⟨x, ?_, ?_, ?_⟩
  · intro j
    simp only [hx]
    split_ifs <;> simp
  · have : Finset.univ.filter (fun j => x j ≠ 0) =
        Finset.univ.filter (fun j => σ₀ j ≠ σ₁ j) := by
      apply Finset.filter_congr
      intro j _
      simp only [hx]
      by_cases h : σ₀ j = σ₁ j
      · simp [h]
      · simp only [h, ite_false, ne_eq, not_false_eq_true, iff_true]
        split_ifs <;> norm_num
    rw [this]
    exact hfar
  · intro i
    have hxr : ∀ j, ((x j : ℤ) : ℝ) = (sgn (σ₀ j) - sgn (σ₁ j)) / 2 := by
      intro j
      simp only [hx]
      cases σ₀ j <;> cases σ₁ j <;> norm_num [sgn]
    have hsum : ∑ j, A i j * ((x j : ℤ) : ℝ) = (rowS (A i) σ₀ - rowS (A i) σ₁) / 2 := by
      simp_rw [hxr]
      rw [rowS, rowS, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsum]
    have hbi : round (rowS (A i) σ₀ / (2 * Δ)) = round (rowS (A i) σ₁ / (2 * Δ)) := by
      have := congrFun hbeq i
      simp only [hb] at this
      exact this.symm
    have h0 := abs_sub_round (rowS (A i) σ₀ / (2 * Δ))
    have h1 := abs_sub_round (rowS (A i) σ₁ / (2 * Δ))
    rw [hbi] at h0
    have h2 : |rowS (A i) σ₀ / (2 * Δ) - rowS (A i) σ₁ / (2 * Δ)| ≤ 1 := by
      calc |rowS (A i) σ₀ / (2 * Δ) - rowS (A i) σ₁ / (2 * Δ)|
          = |(rowS (A i) σ₀ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ))) -
              (rowS (A i) σ₁ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ)))| := by ring_nf
        _ ≤ |rowS (A i) σ₀ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ))| +
              |rowS (A i) σ₁ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ))| := abs_sub _ _
        _ ≤ 1 := by linarith
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Δ),
      div_le_iff₀ (by positivity)] at h2
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    linarith

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Spencer.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.SpencerAux

/-- The hypothesis of the partial colouring statement, for a fixed constant. -/
def PC (C : ℝ) : Prop :=
  ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) →
    ∃ x : Fin v → ℤ, (∀ j, |x j| ≤ 1) ∧
      v ≤ 10 * (Finset.univ.filter (fun j => x j ≠ 0)).card ∧
      ∀ i, |∑ j, A i j * (x j : ℝ)| ≤ C * Real.sqrt (v * Real.log (2 * M / v))

/-- Partial colouring transported to an arbitrary finite index type. -/
lemma pc_fintype {C : ℝ} (hC : PC C) {ι : Type} [Fintype ι] (M : ℕ)
    (h1 : 1 ≤ Fintype.card ι) (h2 : Fintype.card ι ≤ M) (A : Fin M → ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ∃ x : ι → ℤ, (∀ j, |x j| ≤ 1) ∧
      Fintype.card ι ≤ 10 * (Finset.univ.filter (fun j => x j ≠ 0)).card ∧
      ∀ i, |∑ j, A i j * (x j : ℝ)| ≤
        C * Real.sqrt (Fintype.card ι * Real.log (2 * M / Fintype.card ι)) := by
  set e := Fintype.equivFin ι
  obtain ⟨x, hx1, hx2, hx3⟩ := hC M (Fintype.card ι) h1 h2 (fun i k => A i (e.symm k))
    (fun i k => hA _ _)
  refine ⟨fun j => x (e j), fun j => hx1 _, ?_, ?_⟩
  · have : (Finset.univ.filter (fun j => x (e j) ≠ 0)).card =
        (Finset.univ.filter (fun k => x k ≠ 0)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      exact Equiv.sum_comp e (fun k => if x k ≠ 0 then 1 else 0)
    rw [this]; exact hx2
  · intro i
    have : ∑ j, A i j * (x (e j) : ℝ) = ∑ k, A i (e.symm k) * (x k : ℝ) := by
      rw [← Equiv.sum_comp e.symm]
      simp
    rw [this]; exact hx3 i

lemma log_ge (v M : ℕ) (hv : 1 ≤ v) (hvM : v ≤ M) :
    Real.log 2 ≤ Real.log (2 * M / v) := by
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have hvM' : (v:ℝ) ≤ M := by exact_mod_cast hvM
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hv']
  linarith

lemma log_nonneg' (v M : ℕ) (hv : 1 ≤ v) (hvM : v ≤ M) :
    0 ≤ Real.log (2 * M / v) := by
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have hvM' : (v:ℝ) ≤ M := by exact_mod_cast hvM
  apply Real.log_nonneg
  rw [le_div_iff₀ hv']
  linarith

/-- Key numerical inequality closing the induction. -/
lemma key_ineq (u v M : ℕ) (hv : 1 ≤ v) (hvM : v ≤ M) (huv : 10 * u ≤ 9 * v) :
    (u : ℝ) * (Real.log (2 * M / u) + 20) ≤
      (39 / 40) ^ 2 * ((v : ℝ) * (Real.log (2 * M / v) + 20)) := by
  have hL := log_nonneg' v M hv hvM
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have hvM' : (v:ℝ) ≤ M := by exact_mod_cast hvM
  have huv' : (10:ℝ) * u ≤ 9 * v := by exact_mod_cast huv
  rcases Nat.eq_zero_or_pos u with hu | hu
  · subst hu
    simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (by norm_num) (mul_nonneg hv'.le (by linarith))
  · have hu' : (0:ℝ) < u := by exact_mod_cast hu
    have hM' : (0:ℝ) < M := by linarith
    have hsplit : Real.log (2 * M / u) = Real.log (2 * M / v) + Real.log (v / u) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hlog : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlog' : (u:ℝ) * Real.log (v / u) ≤ v - u := by
      have h1 := mul_le_mul_of_nonneg_left hlog hu'.le
      have h2 : (u:ℝ) * (v / u) = v := by field_simp
      rw [mul_sub, h2] at h1
      linarith
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right huv' hL, mul_nonneg hv'.le hL]

lemma main (C : ℝ) (hC0 : 0 < C) (hC : PC C) (M : ℕ) :
    ∀ (v : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = v → v ≤ M →
      ∀ A : Fin M → ι → ℝ, (∀ i j, |A i j| ≤ 1) →
      ∃ ε : ι → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ i, |∑ j, A i j * ε j| ≤
          40 * C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro ι _ hcard hvM A hA
  rcases Nat.eq_zero_or_pos v with hv0 | hv0
  · subst hv0
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
    simp
  · obtain ⟨x, hx1, hx2, hx3⟩ := pc_fintype hC M (by omega) (by omega) A hA
    rw [hcard] at hx2 hx3
    set ι' := {j : ι // x j = 0}
    set u := Fintype.card ι' with hu
    have hu_eq : u = (Finset.univ.filter (fun j => x j = 0)).card := by
      rw [hu, Fintype.card_subtype]
    have hsum_card : (Finset.univ.filter (fun j => x j = 0)).card +
        (Finset.univ.filter (fun j => x j ≠ 0)).card = v := by
      rw [← hcard]
      exact Finset.card_filter_add_card_filter_not _
    have h10 : 10 * u ≤ 9 * v := by omega
    have huv : u < v := by omega
    obtain ⟨ε', hε'1, hε'2⟩ :=
      ih u huv ι' rfl (by omega) (fun i k => A i k.1) (fun i k => hA _ _)
    let ε : ι → ℝ := fun j => if h : x j = 0 then ε' ⟨j, h⟩ else (x j : ℝ)
    refine ⟨ε, ?_, ?_⟩
    · intro j
      by_cases h : x j = 0
      · simp only [ε, dif_pos h]; exact hε'1 _
      · simp only [ε, dif_neg h]
        have := abs_le.mp (hx1 j)
        have : x j = 1 ∨ x j = -1 := by omega
        rcases this with h' | h'
        · left; rw [h']; norm_num
        · right; rw [h']; norm_num
    · intro i
      have hdecomp : ∑ j, A i j * ε j =
          ∑ j, A i j * (x j : ℝ) + ∑ k : ι', A i k.1 * ε' k := by
        have h1 : ∑ j, A i j * ε j =
            ∑ j, (A i j * (x j : ℝ) + if x j = 0 then A i j * ε j else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : x j = 0
          · simp [h]
          · simp [h, ε]
        have h2 : ∑ j, (if x j = 0 then A i j * ε j else 0) = ∑ k : ι', A i k.1 * ε' k := by
          rw [← Finset.sum_filter, Finset.sum_subtype (p := fun j => x j = 0) _ (by simp)]
          apply Finset.sum_congr rfl
          intro k _
          simp only [ε, dif_pos k.2]
        rw [h1, Finset.sum_add_distrib, h2]
      rw [hdecomp]
      have hL := log_nonneg' v M hv0 hvM
      have hv' : (0:ℝ) ≤ v := by positivity
      have hY : (0:ℝ) ≤ v * (Real.log (2 * M / v) + 20) := mul_nonneg hv' (by linarith)
      have b1 : |∑ j, A i j * (x j : ℝ)| ≤
          C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by
        refine (hx3 i).trans ?_
        apply mul_le_mul_of_nonneg_left _ hC0.le
        apply Real.sqrt_le_sqrt
        nlinarith
      have b2 : |∑ k : ι', A i k.1 * ε' k| ≤
          40 * C * ((39 / 40) * Real.sqrt (v * (Real.log (2 * M / v) + 20))) := by
        refine (hε'2 i).trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hk := key_ineq u v M hv0 hvM h10
        calc Real.sqrt (u * (Real.log (2 * M / u) + 20))
            ≤ Real.sqrt ((39 / 40) ^ 2 * ((v : ℝ) * (Real.log (2 * M / v) + 20))) :=
              Real.sqrt_le_sqrt hk
          _ = (39 / 40) * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by
            rw [Real.sqrt_mul' _ hY, Real.sqrt_sq (by norm_num)]
      calc |∑ j, A i j * (x j : ℝ) + ∑ k : ι', A i k.1 * ε' k|
          ≤ |∑ j, A i j * (x j : ℝ)| + |∑ k : ι', A i k.1 * ε' k| := abs_add_le _ _
        _ ≤ C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) +
            40 * C * ((39 / 40) * Real.sqrt (v * (Real.log (2 * M / v) + 20))) :=
              add_le_add b1 b2
        _ = 40 * C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by ring

end ChowlaOpus.SpencerAux

namespace ChowlaOpus

theorem spencerStatement_holds (h : PartialColoringStatement) : SpencerStatement := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨280 * C, by positivity, ?_⟩
  intro M v hv hvM A hA
  obtain ⟨ε, hε1, hε2⟩ :=
    SpencerAux.main C hC0 hC M v (Fin v) (Fintype.card_fin v) hvM A hA
  refine ⟨ε, hε1, fun i => (hε2 i).trans ?_⟩
  have hL2 := SpencerAux.log_ge v M hv hvM
  have hlog2 := Real.log_two_gt_d9
  have hv' : (0:ℝ) ≤ v := by positivity
  have hL : 0 ≤ Real.log (2 * M / v) := by linarith
  calc 40 * C * Real.sqrt (v * (Real.log (2 * M / v) + 20))
      ≤ 40 * C * Real.sqrt (7 ^ 2 * (v * Real.log (2 * M / v))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.sqrt_le_sqrt
        nlinarith [mul_le_mul_of_nonneg_left
          (show (0.6931471803:ℝ) ≤ Real.log (2 * M / v) by linarith) hv']
    _ = 280 * C * Real.sqrt (v * Real.log (2 * M / v)) := by
        rw [Real.sqrt_mul' _ (mul_nonneg hv' hL), Real.sqrt_sq (by norm_num)]
        ring

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Mesh.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.MeshAux

open Finset

/-- Dirichlet sum `∑_{a<L} e(a s)`. -/
noncomputable def dir (L : ℕ) (s : ℝ) : ℂ := ∑ a ∈ range L, ee ((a : ℝ) * s)

/-- Unnormalised Fejér kernel `|∑_{a<L} e(a s)|²`. -/
noncomputable def fej (L : ℕ) (s : ℝ) : ℝ := Complex.normSq (dir L s)

lemma fej_nonneg (L : ℕ) (s : ℝ) : 0 ≤ fej L s := Complex.normSq_nonneg _

lemma fej_eq (L : ℕ) (s : ℝ) :
    (fej L s : ℂ) = ∑ a ∈ range L, ∑ b ∈ range L, ee (((a : ℝ) - b) * s) := by
  rw [fej, ← Complex.mul_conj, dir, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← ee_neg, ← ee_add]; congr 1; ring

lemma ee_natMul (x : ℝ) (i : ℕ) : ee ((i : ℝ) * x) = ee x ^ i := by
  unfold ee
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma sum_ee_int (M : ℕ) (hM : 0 < M) (m : ℤ) (hm : |m| < M) :
    ∑ i ∈ range M, ee ((m : ℝ) * i / M) = if m = 0 then (M : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp [ee_zero]
  · set z := ee ((m : ℝ) / M) with hz
    have hMr : (M : ℝ) ≠ 0 := by positivity
    have hpow : ∀ i : ℕ, ee ((m : ℝ) * i / M) = z ^ i := by
      intro i
      rw [hz, ← ee_natMul]; congr 1; ring
    have hz1 : z ≠ 1 := by
      intro h1
      have hc : Real.cos (2 * π * ((m : ℝ) / M)) = 1 := by
        rw [← ee_re, ← hz, h1, Complex.one_re]
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hc
      have hn' : (n : ℝ) * M = m := by
        field_simp at hn
        nlinarith [Real.pi_pos]
      have hn'' : n * (M : ℤ) = m := by exact_mod_cast hn'
      have : n = 0 := by
        by_contra hne
        have h1 : 1 ≤ |n| := Int.one_le_abs hne
        rw [← hn'', abs_mul] at hm
        have : |(M : ℤ)| = M := abs_of_nonneg (by positivity)
        rw [this] at hm
        nlinarith
      apply h
      rw [← hn'', this, zero_mul]
    have hzM : z ^ M = 1 := by
      rw [← hpow, mul_div_assoc, div_self hMr, mul_one, ee_intCast]
    simp_rw [hpow]
    have := geom_sum_mul z M
    rw [hzM, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hz1)

/-- Discrete Fourier coefficients of the Fejér-type kernel on a mesh of `M` points. -/
lemma key (L M d : ℕ) (hM : 0 < M) (h : d + L ≤ M) (t : ℝ) :
    ∑ i ∈ range M, ee ((d : ℝ) * ((i : ℝ) / M)) * (fej L (t - i / M) : ℂ)
      = (((M : ℝ) * ((L - d : ℕ) : ℝ) : ℝ) : ℂ) * ee ((d : ℝ) * t) := by
  simp_rw [fej_eq, Finset.mul_sum]
  have step : ∀ i a b : ℕ, ee ((d : ℝ) * ((i : ℝ) / M)) * ee (((a : ℝ) - b) * (t - i / M)) =
      ee (((a : ℝ) - b) * t) * ee ((((d : ℤ) - a + b : ℤ) : ℝ) * i / M) := by
    intro i a b; rw [← ee_add, ← ee_add]; congr 1; push_cast; ring
  simp_rw [step]
  rw [Finset.sum_comm]
  have inner : ∀ a ∈ range L, ∑ i ∈ range M, ∑ b ∈ range L,
      ee (((a : ℝ) - b) * t) * ee ((((d : ℤ) - a + b : ℤ) : ℝ) * i / M) =
      ∑ b ∈ range L, if a = b + d then (M : ℂ) * ee ((d : ℝ) * t) else 0 := by
    intro a ha
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← Finset.mul_sum]
    have hab : |((d : ℤ) - a + b : ℤ)| < M := by
      simp only [Finset.mem_range] at ha hb
      rw [abs_lt]; constructor <;> omega
    rw [sum_ee_int M hM _ hab]
    by_cases hc : a = b + d
    · subst hc
      have : ((d : ℤ) - ((b + d : ℕ) : ℤ) + b : ℤ) = 0 := by push_cast; ring
      simp only [this, ↓reduceIte]
      push_cast
      rw [mul_comm]; congr 2; ring
    · have : ((d : ℤ) - (a : ℤ) + b : ℤ) ≠ 0 := by omega
      simp only [this, hc, ↓reduceIte, mul_zero]
  rw [Finset.sum_congr rfl inner, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq', Finset.mem_range]
  rw [← Finset.sum_filter, Finset.sum_const]
  have hf : (range L).filter (fun b => b + d < L) = range (L - d) := by
    ext b; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

lemma key_re (L M d : ℕ) (hM : 0 < M) (h : d + L ≤ M) (t : ℝ) :
    ∑ i ∈ range M, Real.cos (2 * π * d * ((i : ℝ) / M)) * fej L (t - i / M)
      = (M : ℝ) * ((L - d : ℕ) : ℝ) * Real.cos (2 * π * d * t) := by
  have := congrArg Complex.re (key L M d hM h t)
  rw [Complex.re_sum] at this
  simp only [Complex.re_mul_ofReal, Complex.re_ofReal_mul, ee_re] at this
  have e1 : ∀ x : ℝ, 2 * π * d * x = 2 * π * (d * x) := fun x => by ring
  simp_rw [e1]
  exact this

lemma key0 (L M : ℕ) (hM : 0 < M) (h : L ≤ M) (t : ℝ) :
    ∑ i ∈ range M, fej L (t - i / M) = (M : ℝ) * L := by
  have := key_re L M 0 hM (by omega) t
  simpa using this

end ChowlaOpus.MeshAux

namespace ChowlaOpus

open Finset MeshAux

theorem meshStatement_holds : MeshStatement := by
  refine ⟨4, by norm_num, ?_⟩
  intro N M c E hKM hM hmesh t
  have hE : 0 ≤ E := (abs_nonneg _).trans (hmesh 0 hM)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; linarith
  set P : ℝ → ℝ := fun x => ∑ d ∈ Finset.Icc 1 N, c d * Real.cos (2 * Real.pi * d * x) with hP
  set W : ℝ → ℝ := fun s => fej (3 * N) s - fej N s with hW
  have h3 : ∀ d ∈ Icc 1 N, ∑ i ∈ range M, Real.cos (2 * π * d * ((i : ℝ) / M)) *
      W (t - i / M) = M * (2 * N) * Real.cos (2 * π * d * t) := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    simp only [hW, mul_sub, Finset.sum_sub_distrib]
    rw [key_re (3 * N) M d hM (by omega) t, key_re N M d hM (by omega) t,
      Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hsum : (M : ℝ) * (2 * N) * P t = ∑ i ∈ range M, P (i / M) * W (t - i / M) := by
    calc (M : ℝ) * (2 * N) * P t
        = ∑ d ∈ Icc 1 N, c d * ((M : ℝ) * (2 * N) * Real.cos (2 * π * d * t)) := by
          rw [hP, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
      _ = ∑ d ∈ Icc 1 N, c d * ∑ i ∈ range M, Real.cos (2 * π * d * ((i : ℝ) / M)) *
            W (t - i / M) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [h3 d hd]
      _ = ∑ i ∈ range M, P (i / M) * W (t - i / M) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hP, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
  have hbound : |∑ i ∈ range M, P (i / M) * W (t - i / M)| ≤
      ∑ i ∈ range M, E * (fej (3 * N) (t - i / M) + fej N (t - i / M)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [abs_mul]
    have hi' : i < M := Finset.mem_range.mp hi
    have h1 : |P (i / M)| ≤ E := hmesh i hi'
    have h2 : |W (t - i / M)| ≤ fej (3 * N) (t - i / M) + fej N (t - i / M) := by
      have := fej_nonneg (3 * N) (t - i / M)
      have := fej_nonneg N (t - i / M)
      rw [hW, abs_le]; constructor <;> linarith
    calc |P (i / M)| * |W (t - i / M)| ≤ E * |W (t - i / M)| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hE
  rw [← Finset.mul_sum, Finset.sum_add_distrib, key0 (3 * N) M hM (by omega) t,
    key0 N M hM (by omega) t, ← hsum, abs_mul] at hbound
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < M * (2 * N) := by positivity
  rw [abs_of_pos hpos] at hbound
  have : (M : ℝ) * (2 * N) * |P t| ≤ (M * (2 * N)) * (2 * E) := by
    push_cast at hbound; nlinarith
  exact le_of_mul_le_mul_left this hpos

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/Rounding.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.RoundingAux

open Finset

/-- `x ↦ x log (A / x)` is monotone on `[0, A / e]`. -/
lemma mul_log_div_mono {A x y : ℝ} (hA : 0 < A) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy1 : 1 ≤ Real.log (A / y)) :
    x * Real.log (A / x) ≤ y * Real.log (A / y) := by
  have hy : 0 < y := by
    rcases (hx.trans hxy).eq_or_lt with h | h
    · rw [← h] at hy1; simp at hy1; linarith
    · exact h
  rcases hx.eq_or_lt with h | hx'
  · rw [← h]; simp; exact mul_nonneg hy.le (by linarith)
  · have h1 : Real.log (A / x) = Real.log (A / y) + Real.log (y / x) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h2 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : x * Real.log (y / x) ≤ y - x := by
      calc x * Real.log (y / x) ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left h2 hx
        _ = y - x := by field_simp
    rw [h1]; nlinarith

/-- The cost of one rounding level. -/
lemma cost_bound {A N U Δ L x : ℝ} (hA : 0 < A) (hN : 0 < N) (hU : 0 < U) (hΔ : 0 < Δ)
    (hΔ1 : Δ ≤ 1) (hx : 0 ≤ x) (hxN : x ≤ N) (hxU : x * Δ ≤ U)
    (hAN : 1 ≤ Real.log (A / N)) (hLN : Real.log (A / N) ≤ L) (hLU : Real.log (A / U) ≤ L) :
    Δ ^ 2 * (x * Real.log (A / x)) ≤ Δ * U * L := by
  rcases le_or_gt (N * Δ) U with h | h
  · have hm := mul_log_div_mono hA hx hxN hAN
    calc Δ ^ 2 * (x * Real.log (A / x)) ≤ Δ ^ 2 * (N * Real.log (A / N)) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = Δ * (N * Δ) * Real.log (A / N) := by ring
      _ ≤ Δ * U * Real.log (A / N) := by gcongr
      _ ≤ Δ * U * L := by gcongr
  · set y := U / Δ with hy
    have hypos : 0 < y := by positivity
    have hyN : y < N := by rw [hy, div_lt_iff₀ hΔ]; linarith
    have hxy : x ≤ y := by rw [hy, le_div_iff₀ hΔ]; linarith
    have hy1 : 1 ≤ Real.log (A / y) := le_trans hAN
      (Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hA.le hypos hyN.le))
    have hm := mul_log_div_mono hA hx hxy hy1
    have hlog : Real.log (A / y) ≤ L := by
      calc Real.log (A / y) = Real.log (A * Δ / U) := by
            congr 1; rw [hy]; field_simp
        _ ≤ Real.log (A / U) := Real.log_le_log (by positivity)
            (div_le_div_of_nonneg_right (by nlinarith) hU.le)
        _ ≤ L := hLU
    calc Δ ^ 2 * (x * Real.log (A / x)) ≤ Δ ^ 2 * (y * Real.log (A / y)) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = Δ * U * Real.log (A / y) := by rw [hy]; field_simp
      _ ≤ Δ * U * L := by gcongr

/-- The per-level cost, in the form used by the iteration. -/
lemma level_bound {CS U L : ℝ} {N M : ℕ} (hCS : 0 ≤ CS) (hN : 0 < N) (hU : 0 < U) (hM : 0 < M)
    (hAN : 1 ≤ Real.log (2 * M / N)) (hLN : Real.log (2 * M / N) ≤ L)
    (hLU : Real.log (2 * M / U) ≤ L) (k v : ℕ) (hvN : v ≤ N) (hvU : (v : ℝ) / 2 ^ (k + 1) ≤ U) :
    CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤
      CS * Real.sqrt (U * L) * (3 / 4) ^ (k + 1) := by
  set Δ : ℝ := 1 / 2 ^ (k + 1) with hΔ
  have hΔpos : 0 < Δ := by positivity
  have hΔ1 : Δ ≤ 1 := by
    rw [hΔ, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hc := cost_bound (A := 2 * M) (N := N) (U := U) (Δ := Δ) (L := L) (x := v)
    (by positivity) (by exact_mod_cast hN) hU hΔpos hΔ1 (by positivity)
    (by exact_mod_cast hvN) (by rw [hΔ, mul_one_div]; exact hvU) hAN hLN hLU
  have hsq : Real.sqrt Δ ≤ (3 / 4) ^ (k + 1) := by
    rw [Real.sqrt_le_left (by positivity), hΔ, ← pow_mul, mul_comm, pow_mul, ← one_div_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have key : Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤
      Real.sqrt (U * L) * (3 / 4) ^ (k + 1) := by
    calc Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1)
          = Real.sqrt (Δ ^ 2 * (v * Real.log (2 * M / v))) := by
          rw [Real.sqrt_mul (sq_nonneg Δ) (↑v * _), Real.sqrt_sq hΔpos.le, hΔ]; ring
      _ ≤ Real.sqrt (Δ * U * L) := Real.sqrt_le_sqrt hc
      _ = Real.sqrt Δ * Real.sqrt (U * L) := by rw [mul_assoc, Real.sqrt_mul hΔpos.le]
      _ ≤ (3 / 4) ^ (k + 1) * Real.sqrt (U * L) := by gcongr
      _ = _ := by ring
  calc CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1)
        = CS * (Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1)) := by ring
    _ ≤ CS * (Real.sqrt (U * L) * (3 / 4) ^ (k + 1)) := by gcongr
    _ = _ := by ring

/-- Spencer's theorem in the form used below. -/
def SpencerProp (CS : ℝ) : Prop :=
  ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) → ∃ ε : Fin v → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, A i j * ε j| ≤ CS * Real.sqrt (v * Real.log (2 * M / v))

/-- One dyadic rounding step: numerators `m` at level `k + 1` become numerators `m'` at
level `k`. -/
lemma step {CS : ℝ} (hSp : SpencerProp CS) (N M : ℕ) (hNM : N ≤ M) (σ : ℕ → ℝ)
    (hσ : ∀ d, |σ d| ≤ 1) (k : ℕ) (m : ℕ → ℕ) (hm : ∀ d ∈ Icc 1 N, m d ≤ 2 ^ (k + 1)) :
    ∃ m' : ℕ → ℕ, (∀ d ∈ Icc 1 N, m' d ≤ 2 ^ k) ∧
      (∑ d ∈ Icc 1 N, (2 * (m' d : ℝ))) ≤ ∑ d ∈ Icc 1 N, (m d : ℝ) ∧
      ∀ i < M, |∑ d ∈ Icc 1 N, σ d * (2 * (m' d : ℝ) - m d) *
          Real.cos (2 * π * d * ((i : ℝ) / M))| ≤
        CS * Real.sqrt (((Icc 1 N).filter (fun d => Odd (m d))).card *
          Real.log (2 * M / ((Icc 1 N).filter (fun d => Odd (m d))).card)) := by
  classical
  set J := (Icc 1 N).filter (fun d => Odd (m d)) with hJ
  set v := J.card with hv
  let e : Fin v ≃ J := J.equivFin.symm
  obtain ⟨ε, hε1, hεsum, hεrow⟩ : ∃ ε : Fin v → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∑ j, ε j ≤ 0 ∧
      ∀ i < M, |∑ j, σ (e j) * Real.cos (2 * π * ((e j : ℕ) : ℝ) * ((i : ℝ) / M)) * ε j| ≤
        CS * Real.sqrt (v * Real.log (2 * M / v)) := by
    rcases Nat.eq_zero_or_pos v with hv0 | hvpos
    · have : IsEmpty (Fin v) := by rw [hv0]; infer_instance
      refine ⟨fun _ => 1, fun _ => Or.inl rfl, by simp, fun i _ => ?_⟩
      simp [hv0]
    · have hvM : v ≤ M := by
        have : v ≤ (Icc 1 N).card := card_le_card (filter_subset _ _)
        simp at this; omega
      obtain ⟨ε, hε1, hεb⟩ := hSp M v hvpos hvM
        (fun i j => σ (e j) * Real.cos (2 * π * ((e j : ℕ) : ℝ) * (((i : ℕ) : ℝ) / M))) (by
          intro i j; rw [abs_mul]
          calc |σ (e j)| * |Real.cos (2 * π * ((e j : ℕ) : ℝ) * (((i : ℕ) : ℝ) / M))|
              ≤ 1 * 1 := mul_le_mul (hσ _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1)
      by_cases hs : ∑ j, ε j ≤ 0
      · exact ⟨ε, hε1, hs, fun i hi => hεb ⟨i, hi⟩⟩
      · refine ⟨fun j => -ε j, fun j => (hε1 j).elim (fun h => Or.inr (by simp [h]))
          (fun h => Or.inl (by simp [h])), ?_, ?_⟩
        · rw [Finset.sum_neg_distrib]; linarith
        · intro i hi
          have := hεb ⟨i, hi⟩
          simp only [mul_neg, Finset.sum_neg_distrib, abs_neg]
          exact this
  let δ : ℕ → ℝ := fun d => if h : d ∈ J then ε (e.symm ⟨d, h⟩) else 0
  have hδsum : ∀ f : ℕ → ℝ, ∑ d ∈ Icc 1 N, δ d * f d = ∑ j, ε j * f (e j) := by
    intro f
    have h1 : ∑ d ∈ J, δ d * f d = ∑ d ∈ Icc 1 N, δ d * f d :=
      Finset.sum_subset (filter_subset _ _) (fun d _ hdJ => by simp [δ, hdJ])
    rw [← h1, ← Finset.sum_coe_sort J, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [δ]
  have hex : ∀ d, ∃ n : ℕ, d ∈ Icc 1 N → n ≤ 2 ^ k ∧ (2 * (n : ℝ)) = m d + δ d := by
    intro d
    by_cases hd : d ∈ Icc 1 N
    · have hmd := hm d hd
      rw [pow_succ] at hmd
      by_cases hdJ : d ∈ J
      · obtain ⟨q, hq⟩ : Odd (m d) := (mem_filter.mp hdJ).2
        have hδ : δ d = ε (e.symm ⟨d, hdJ⟩) := by simp [δ, hdJ]
        rcases hε1 (e.symm ⟨d, hdJ⟩) with h | h
        · refine ⟨q + 1, fun _ => ⟨?_, ?_⟩⟩
          · omega
          · rw [hδ, h, hq]; push_cast; ring
        · refine ⟨q, fun _ => ⟨?_, ?_⟩⟩
          · omega
          · rw [hδ, h, hq]; push_cast; ring
      · have heven : Even (m d) := by
          have : ¬ Odd (m d) := fun h => hdJ (mem_filter.mpr ⟨hd, h⟩)
          exact Nat.not_odd_iff_even.mp this
        obtain ⟨q, hq⟩ := heven
        have hδ : δ d = 0 := by simp [δ, hdJ]
        refine ⟨q, fun _ => ⟨?_, ?_⟩⟩
        · omega
        · rw [hδ, hq]; push_cast; ring
    · exact ⟨0, fun h => absurd h hd⟩
  choose m' hm' using hex
  refine ⟨m', fun d hd => (hm' d hd).1, ?_, ?_⟩
  · have h2 : ∑ d ∈ Icc 1 N, 2 * (m' d : ℝ) =
        ∑ d ∈ Icc 1 N, (m d : ℝ) + ∑ d ∈ Icc 1 N, δ d * 1 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun d hd => by rw [(hm' d hd).2]; ring)
    rw [h2, hδsum]; simp only [mul_one]; linarith
  · intro i hi
    have h3 : ∑ d ∈ Icc 1 N, σ d * (2 * (m' d : ℝ) - m d) *
          Real.cos (2 * π * d * ((i : ℝ) / M)) =
        ∑ d ∈ Icc 1 N, δ d * (σ d * Real.cos (2 * π * d * ((i : ℝ) / M))) :=
      sum_congr rfl (fun d hd => by rw [(hm' d hd).2]; ring)
    rw [h3, hδsum]
    calc _ = |∑ j, σ (e j) * Real.cos (2 * π * ((e j : ℕ) : ℝ) * ((i : ℝ) / M)) * ε j| := by
          congr 1; exact sum_congr rfl (fun j _ => by ring)
      _ ≤ _ := hεrow i hi

/-- The full dyadic rounding process, from level `k` down to level `0`. -/
lemma iterate {CS : ℝ} (hSp : SpencerProp CS) (N M : ℕ) (hNM : N ≤ M) (σ : ℕ → ℝ)
    (hσ : ∀ d, |σ d| ≤ 1) (U G : ℝ)
    (hlevel : ∀ k v : ℕ, v ≤ N → (v : ℝ) / 2 ^ (k + 1) ≤ U →
      CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤ G * (3 / 4) ^ (k + 1)) :
    ∀ k (m : ℕ → ℕ), (∀ d ∈ Icc 1 N, m d ≤ 2 ^ k) → ∑ d ∈ Icc 1 N, (m d : ℝ) / 2 ^ k ≤ U →
      ∃ a : ℕ → ℕ, (∀ d ∈ Icc 1 N, a d ≤ 1) ∧ ∀ i < M,
        |∑ d ∈ Icc 1 N, σ d * ((a d : ℝ) - m d / 2 ^ k) *
            Real.cos (2 * π * d * ((i : ℝ) / M))| ≤
          ∑ j ∈ range k, G * (3 / 4) ^ (j + 1) := by
  intro k
  induction k with
  | zero =>
    intro m hm _
    exact ⟨m, by simpa using hm, fun i _ => by simp⟩
  | succ k ih =>
    intro m hm hU
    obtain ⟨m', hm'1, hm'2, hm'3⟩ := step hSp N M hNM σ hσ k m hm
    set J := (Icc 1 N).filter (fun d => Odd (m d))
    have hvN : J.card ≤ N := by
      calc J.card ≤ (Icc 1 N).card := card_le_card (filter_subset _ _)
        _ = N := by simp
    have hvm : (J.card : ℝ) ≤ ∑ d ∈ Icc 1 N, (m d : ℝ) := by
      calc (J.card : ℝ) = ∑ d ∈ J, (1 : ℝ) := by simp
        _ ≤ ∑ d ∈ J, (m d : ℝ) := sum_le_sum (fun d hd => by
            have := (mem_filter.mp hd).2; exact_mod_cast this.pos)
        _ ≤ ∑ d ∈ Icc 1 N, (m d : ℝ) := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => by positivity)
    have hvU : (J.card : ℝ) / 2 ^ (k + 1) ≤ U := by
      calc (J.card : ℝ) / 2 ^ (k + 1) ≤ (∑ d ∈ Icc 1 N, (m d : ℝ)) / 2 ^ (k + 1) := by gcongr
        _ = ∑ d ∈ Icc 1 N, (m d : ℝ) / 2 ^ (k + 1) := by rw [sum_div]
        _ ≤ U := hU
    have hU' : ∑ d ∈ Icc 1 N, (m' d : ℝ) / 2 ^ k ≤ U := by
      calc ∑ d ∈ Icc 1 N, (m' d : ℝ) / 2 ^ k
            = (∑ d ∈ Icc 1 N, 2 * (m' d : ℝ)) / 2 ^ (k + 1) := by
            rw [sum_div]; refine sum_congr rfl (fun d _ => ?_); rw [pow_succ]; field_simp
        _ ≤ (∑ d ∈ Icc 1 N, (m d : ℝ)) / 2 ^ (k + 1) := by gcongr
        _ = ∑ d ∈ Icc 1 N, (m d : ℝ) / 2 ^ (k + 1) := by rw [sum_div]
        _ ≤ U := hU
    obtain ⟨a, ha1, ha2⟩ := ih m' hm'1 hU'
    refine ⟨a, ha1, fun i hi => ?_⟩
    have hsplit : ∑ d ∈ Icc 1 N, σ d * ((a d : ℝ) - m d / 2 ^ (k + 1)) *
          Real.cos (2 * π * d * ((i : ℝ) / M)) =
        ∑ d ∈ Icc 1 N, σ d * ((a d : ℝ) - m' d / 2 ^ k) *
          Real.cos (2 * π * d * ((i : ℝ) / M)) +
        (∑ d ∈ Icc 1 N, σ d * (2 * (m' d : ℝ) - m d) *
          Real.cos (2 * π * d * ((i : ℝ) / M))) / 2 ^ (k + 1) := by
      rw [sum_div, ← sum_add_distrib]
      refine sum_congr rfl (fun d _ => ?_)
      rw [pow_succ]; field_simp; ring
    rw [hsplit, sum_range_succ]
    refine (abs_add_le _ _).trans (add_le_add (ha2 i hi) ?_)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (k + 1))]
    calc _ ≤ CS * Real.sqrt (J.card * Real.log (2 * M / J.card)) / 2 ^ (k + 1) := by
          gcongr; exact hm'3 i hi
      _ ≤ G * (3 / 4) ^ (k + 1) := hlevel k J.card hvN hvU

end ChowlaOpus.RoundingAux

namespace ChowlaOpus

open Finset RoundingAux in
theorem roundingStatement_holds (hS : SpencerStatement) (hM : MeshStatement) :
    RoundingStatement := by
  obtain ⟨CS, hCS, hSp⟩ := hS
  obtain ⟨K, hK1, hMesh⟩ := hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1'
  set cK : ℝ := Real.log K / Real.log 2 + 2 with hcK
  have hcK0 : 0 ≤ cK := by positivity
  set κ : ℝ := 3 * (CS * Real.sqrt (2 * cK)) + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨2 * κ, by positivity, ?_⟩
  intro N w S hN hw hS0 hSN hvar
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set lam := Real.log (2 * N / S) with hlam_def
  have hlam : Real.log 2 ≤ lam :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hS0]; linarith)
  have hlampos : 0 < lam := lt_of_lt_of_le hlog2 hlam
  have hSlam : 0 < S * lam := mul_pos hS0 hlampos
  set M : ℕ := 2 * K * N with hM_def
  have hMpos : 0 < M := by positivity
  have hNM : N ≤ M := by rw [hM_def]; nlinarith
  have hMR : (M : ℝ) = 2 * K * N := by rw [hM_def]; push_cast; ring
  -- decomposition `w = c + σ u`
  let σ : ℕ → ℝ := fun d => if w d ≤ 1 / 2 then 1 else -1
  let u : ℕ → ℝ := fun d => if w d ≤ 1 / 2 then w d else 1 - w d
  let c : ℕ → ℝ := fun d => if w d ≤ 1 / 2 then 0 else 1
  have hσ : ∀ d, |σ d| ≤ 1 := fun d => by simp only [σ]; split_ifs <;> simp
  have hu0 : ∀ d, 0 ≤ u d := fun d => by
    simp only [u]; split_ifs <;> linarith [hw d]
  have hu1 : ∀ d, u d ≤ 1 := fun d => by
    simp only [u]; split_ifs <;> linarith [hw d]
  have hwcu : ∀ d, w d = c d + σ d * u d := fun d => by
    simp only [c, σ, u]; split_ifs <;> ring
  have huvar : ∀ d, u d ≤ 2 * (w d * (1 - w d)) := fun d => by
    simp only [u]; split_ifs with h <;> nlinarith [hw d]
  set U : ℝ := 2 * S with hU_def
  have hUpos : 0 < U := by positivity
  have hsumu : ∑ d ∈ Icc 1 N, u d ≤ U := by
    calc ∑ d ∈ Icc 1 N, u d ≤ ∑ d ∈ Icc 1 N, 2 * (w d * (1 - w d)) := sum_le_sum (fun d _ => huvar d)
      _ = 2 * ∑ d ∈ Icc 1 N, w d * (1 - w d) := by rw [mul_sum]
      _ ≤ U := by rw [hU_def]; linarith
  -- constants of the level bound
  set L : ℝ := cK * lam with hL_def
  have hAN_eq : 2 * (M : ℝ) / N = 4 * K := by rw [hMR]; field_simp; ring
  have hAN : 1 ≤ Real.log (2 * M / N) := by
    rw [hAN_eq]
    have h4 : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    exact le_trans h4.le (Real.log_le_log (by norm_num) (by linarith))
  have hlogK' : Real.log K ≤ Real.log K / Real.log 2 * lam := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]; exact mul_le_mul_of_nonneg_left hlam hlogK
  have hLN : Real.log (2 * M / N) ≤ L := by
    rw [hAN_eq, Real.log_mul (by norm_num) (by positivity),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, hL_def, hcK]
    push_cast; nlinarith
  have hLU : Real.log (2 * M / U) ≤ L := by
    have : 2 * (M : ℝ) / U = K * (2 * N / S) := by rw [hMR, hU_def]; field_simp
    rw [this, Real.log_mul (by positivity) (by positivity), hL_def, hcK]
    nlinarith
  set G : ℝ := CS * Real.sqrt (U * L) with hG_def
  have hG0 : 0 ≤ G := by positivity
  have hGeq : G = CS * Real.sqrt (2 * cK) * Real.sqrt (S * lam) := by
    rw [hG_def, mul_assoc CS, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * cK)]
    congr 2; rw [hU_def, hL_def]; ring
  have hlevel : ∀ k v : ℕ, v ≤ N → (v : ℝ) / 2 ^ (k + 1) ≤ U →
      CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤ G * (3 / 4) ^ (k + 1) :=
    fun k v hvN hvU => level_bound hCS.le hN hUpos hMpos hAN hLN hLU k v hvN hvU
  -- truncation
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt ((N : ℝ) / Real.sqrt (S * lam)) one_lt_two
  have hsqrtpos : 0 < Real.sqrt (S * lam) := Real.sqrt_pos.mpr hSlam
  have hk₀' : (N : ℝ) / 2 ^ k₀ ≤ Real.sqrt (S * lam) := by
    rw [div_lt_iff₀ hsqrtpos] at hk₀
    rw [div_le_iff₀ (by positivity)]; linarith
  have hP : (0 : ℝ) < 2 ^ k₀ := by positivity
  let m₀ : ℕ → ℕ := fun d => ⌊u d * 2 ^ k₀⌋₊
  have hm₀le : ∀ d, (m₀ d : ℝ) ≤ u d * 2 ^ k₀ := fun d =>
    Nat.floor_le (mul_nonneg (hu0 d) hP.le)
  have hm₀lt : ∀ d, u d * 2 ^ k₀ < m₀ d + 1 := fun d => Nat.lt_floor_add_one _
  have hm₀ : ∀ d ∈ Icc 1 N, m₀ d ≤ 2 ^ k₀ := fun d _ => Nat.floor_le_of_le (by
    push_cast; nlinarith [hu1 d])
  have hm₀u : ∀ d, (m₀ d : ℝ) / 2 ^ k₀ ≤ u d := fun d => by
    rw [div_le_iff₀ hP]; exact hm₀le d
  have hm₀sum : ∑ d ∈ Icc 1 N, (m₀ d : ℝ) / 2 ^ k₀ ≤ U :=
    (sum_le_sum (fun d _ => hm₀u d)).trans hsumu
  have htrunc : ∀ d, |(m₀ d : ℝ) / 2 ^ k₀ - u d| ≤ 1 / 2 ^ k₀ := fun d => by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hm₀u d])]
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hP]; linarith [hm₀lt d]
  -- the dyadic rounding
  obtain ⟨af, haf1, haf2⟩ := iterate hSp N M hNM σ hσ U G hlevel k₀ m₀ hm₀ hm₀sum
  have hgeom : ∑ j ∈ range k₀, G * (3 / 4 : ℝ) ^ (j + 1) ≤ 3 * G := by
    have h1 : ∑ j ∈ range k₀, G * (3 / 4 : ℝ) ^ (j + 1) =
        G * (3 / 4) * ∑ j ∈ range k₀, (3 / 4 : ℝ) ^ j := by
      rw [mul_sum]; exact sum_congr rfl (fun j _ => by ring)
    have h2 : ∑ j ∈ range k₀, (3 / 4 : ℝ) ^ j ≤ (3 / 4 : ℝ) ^ 0 / (1 - 3 / 4) := by
      rw [range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    rw [h1]
    calc G * (3 / 4) * ∑ j ∈ range k₀, (3 / 4 : ℝ) ^ j
          ≤ G * (3 / 4) * ((3 / 4 : ℝ) ^ 0 / (1 - 3 / 4)) := by gcongr
      _ = 3 * G := by ring
  let a : ℕ → ℝ := fun d => if d ∈ Icc 1 N then c d + σ d * af d else 0
  refine ⟨a, ?_, ?_⟩
  · intro d
    simp only [a]
    split_ifs with hd
    · have : af d = 0 ∨ af d = 1 := by have := haf1 d hd; omega
      simp only [c, σ]
      rcases this with h | h <;> rw [h] <;> split_ifs <;> norm_num
    · exact Or.inl rfl
  · intro t
    have hE : ∀ i < M, |∑ d ∈ Icc 1 N, (a d - w d) * Real.cos (2 * π * d * ((i : ℝ) / M))| ≤
        κ * Real.sqrt (S * lam) := by
      intro i hi
      have hsplit : ∑ d ∈ Icc 1 N, (a d - w d) * Real.cos (2 * π * d * ((i : ℝ) / M)) =
          ∑ d ∈ Icc 1 N, σ d * ((af d : ℝ) - m₀ d / 2 ^ k₀) *
            Real.cos (2 * π * d * ((i : ℝ) / M)) +
          ∑ d ∈ Icc 1 N, σ d * ((m₀ d : ℝ) / 2 ^ k₀ - u d) *
            Real.cos (2 * π * d * ((i : ℝ) / M)) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl (fun d hd => ?_)
        simp only [a, hd, ↓reduceIte]; rw [hwcu d]; ring
      have hT : |∑ d ∈ Icc 1 N, σ d * ((m₀ d : ℝ) / 2 ^ k₀ - u d) *
            Real.cos (2 * π * d * ((i : ℝ) / M))| ≤ Real.sqrt (S * lam) := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ d ∈ Icc 1 N, |σ d * ((m₀ d : ℝ) / 2 ^ k₀ - u d) *
              Real.cos (2 * π * d * ((i : ℝ) / M))| ≤ ∑ d ∈ Icc 1 N, (1 / 2 ^ k₀ : ℝ) := by
              refine sum_le_sum (fun d _ => ?_)
              rw [abs_mul, abs_mul]
              calc |σ d| * |(m₀ d : ℝ) / 2 ^ k₀ - u d| * |Real.cos (2 * π * d * ((i : ℝ) / M))|
                  ≤ 1 * (1 / 2 ^ k₀) * 1 := by
                    gcongr
                    · exact hσ d
                    · exact htrunc d
                    · exact Real.abs_cos_le_one _
                _ = 1 / 2 ^ k₀ := by ring
          _ = (N : ℝ) / 2 ^ k₀ := by simp; ring
          _ ≤ Real.sqrt (S * lam) := hk₀'
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      calc _ ≤ 3 * G + Real.sqrt (S * lam) := add_le_add ((haf2 i hi).trans hgeom) hT
        _ = κ * Real.sqrt (S * lam) := by rw [hGeq, hκ]; ring
    have := hMesh N M (fun d => a d - w d) (κ * Real.sqrt (S * lam))
      (by rw [hM_def]; nlinarith) hMpos hE t
    calc _ ≤ 2 * (κ * Real.sqrt (S * lam)) := this
      _ = 2 * κ * Real.sqrt (S * Real.log (2 * N / S)) := by rw [hlam_def]; ring

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Parts/MainOf.lean. -/
section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.MainOfAux

/-- The asymptotic conditions on `T` used in the assembly. -/
lemma exists_T₀ (C c K ε : ℝ) (hC : 0 < C) (hc : 0 < c) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      C * Real.log T / T ^ 2 ≤ c ∧ 4 ≤ C * T * Real.log T ∧
      2 * K ^ 2 * Real.log T ^ 2 < ε ^ 2 * c * T := by
  have h1 : ∀ᶠ T in Filter.atTop,
      2 * K ^ 2 * (Real.log T ^ 2 / (1 * T + 0)) < ε ^ 2 * c := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul (2 * K ^ 2)
    rw [mul_zero] at this
    exact this.eventually_lt_const (by positivity)
  have h2 : ∀ᶠ T in Filter.atTop, max (max (Real.exp 1) (4 / C)) (max (C / c) 1) ≤ T :=
    Filter.eventually_ge_atTop _
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (h1.and h2)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hA, hB⟩ := hT₀ T hT
  have he : Real.exp 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have h4 : 4 / C ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hCc : C / c ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hTpos : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 he
  have hLT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos hTpos).trans (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have h : C ≤ T * c := (div_le_iff₀ hc).1 hCc
    have h' : C * Real.log T ≤ C * T := mul_le_mul_of_nonneg_left hLT hC.le
    have h'' : C * T ≤ T * c * T := mul_le_mul_of_nonneg_right h hTpos.le
    linarith
  · have h : 4 ≤ T * C := (div_le_iff₀ hC).1 h4
    have h' : C * T * 1 ≤ C * T * Real.log T :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    linarith
  · simp only [one_mul, add_zero] at hA
    rw [mul_div_assoc', div_lt_iff₀ hTpos] at hA
    linarith

end ChowlaOpus.MainOfAux

namespace ChowlaOpus

theorem cosine_counterexample_of (hW : WeightsStatement) (hR : RoundingStatement)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧ ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) < cosineSum A t := by
  obtain ⟨C, c, hC, hc, hW⟩ := hW
  obtain ⟨CR, hCR, hR⟩ := hR
  set C₁ : ℝ := CR * Real.sqrt (6 * C) with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  set K : ℝ := C + C₁ with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨T₀, hT₀⟩ := MainOfAux.exists_T₀ C c K ε hC hc hε
  obtain ⟨T, hTT₀, hT3, hWT⟩ := hW T₀
  obtain ⟨hi, hii, hiii⟩ := hT₀ T hTT₀
  set L := Real.log T with hL
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  obtain ⟨p, Nw, w, hp, hNw1, hNw, hw01, hlow, hmass, hvar⟩ :=
    hWT (⌈2 * C₁ * L / c + 2 * T * N / c⌉₊ + 1)
  have hpR : 2 * C₁ * L / c + 2 * T * N / c + 1 ≤ (p : ℝ) := by
    have h1 := Nat.le_ceil (2 * C₁ * L / c + 2 * T * N / c)
    have h2 : ((⌈2 * C₁ * L / c + 2 * T * N / c⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
    push_cast at h2
    linarith
  have hA1 : 0 ≤ 2 * C₁ * L / c := by positivity
  have hA2 : 0 ≤ 2 * T * N / c := by positivity
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hppos : (0 : ℝ) < p := by linarith
  have hpC₁ : 2 * C₁ * L ≤ c * p := by
    have : 2 * C₁ * L / c ≤ p := by linarith
    rw [div_le_iff₀ hc] at this; linarith
  have hpN : 2 * T * N ≤ c * p := by
    have : 2 * T * N / c ≤ p := by linarith
    rw [div_le_iff₀ hc] at this; linarith
  set S : ℝ := C * p ^ 2 * L / T ^ 3 with hS
  have hSpos : 0 < S := by positivity
  have hsumw_le : ∑ d ∈ Finset.Icc 1 Nw, w d ≤ Nw := by
    calc ∑ d ∈ Finset.Icc 1 Nw, w d ≤ ∑ _d ∈ Finset.Icc 1 Nw, (1 : ℝ) :=
          Finset.sum_le_sum fun d _ => (hw01 d).2
      _ = Nw := by simp
  have hS_le_mass : S ≤ c * p ^ 2 / T := by
    have hi' : C * L ≤ c * T ^ 2 := (div_le_iff₀ (by positivity)).1 hi
    rw [hS, div_le_div_iff₀ (by positivity) hTpos]
    have : C * L * (p ^ 2 * T) ≤ c * T ^ 2 * (p ^ 2 * T) :=
      mul_le_mul_of_nonneg_right hi' (by positivity)
    linarith
  have hSN : S ≤ Nw := by linarith
  obtain ⟨a, ha01, hround⟩ := hR Nw w S hNw1 hw01 hSpos hSN hvar
  -- the rounding error
  have hlog : Real.log (2 * Nw / S) ≤ 6 * L := by
    have hNwpos : (1 : ℝ) ≤ Nw := by exact_mod_cast hNw1
    have hpos : 0 < 2 * (Nw : ℝ) / S := by positivity
    have hle : 2 * (Nw : ℝ) / S ≤ T ^ 6 := by
      rw [div_le_iff₀ hSpos]
      have h6 : T ^ 6 * S = C * T * L * (p ^ 2 * T ^ 2) := by
        rw [hS]; field_simp
      rw [h6]
      have h4 : 4 * (p ^ 2 * T ^ 2) ≤ C * T * L * (p ^ 2 * T ^ 2) :=
        mul_le_mul_of_nonneg_right hii (by positivity)
      linarith
    calc Real.log (2 * Nw / S) ≤ Real.log (T ^ 6) := Real.log_le_log hpos hle
      _ = 6 * L := by rw [Real.log_pow, ← hL]; norm_num
  have hX : S * Real.log (2 * Nw / S) ≤ (Real.sqrt (6 * C) * p * L / T) ^ 2 := by
    have h1 : S * Real.log (2 * Nw / S) ≤ S * (6 * L) := mul_le_mul_of_nonneg_left hlog hSpos.le
    have h2 : (Real.sqrt (6 * C) * p * L / T) ^ 2 = 6 * C * p ^ 2 * L ^ 2 / T ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have h3 : S * (6 * L) = 6 * C * p ^ 2 * L ^ 2 / T ^ 3 := by
      rw [hS]; ring
    have h4 : 6 * C * p ^ 2 * L ^ 2 / T ^ 3 ≤ 6 * C * p ^ 2 * L ^ 2 / T ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hT1 (by norm_num))
    linarith
  have herr : CR * Real.sqrt (S * Real.log (2 * Nw / S)) ≤ C₁ * p * L / T := by
    have h := Real.sqrt_le_sqrt hX
    rw [Real.sqrt_sq (by positivity)] at h
    calc CR * Real.sqrt (S * Real.log (2 * Nw / S))
        ≤ CR * (Real.sqrt (6 * C) * p * L / T) := mul_le_mul_of_nonneg_left h hCR.le
      _ = C₁ * p * L / T := by rw [hC₁]; ring
  have hdiff : ∀ t : ℝ,
      |(∑ d ∈ Finset.Icc 1 Nw, a d * Real.cos (2 * Real.pi * d * t)) -
        ∑ d ∈ Finset.Icc 1 Nw, w d * Real.cos (2 * Real.pi * d * t)| ≤ C₁ * p * L / T := by
    intro t
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    exact (hround t).trans herr
  -- the set `A`
  set F := (Finset.Icc 1 Nw).filter (fun d => a d = 1) with hF
  set A : Finset ℕ+ := F.image Nat.toPNat' with hA
  have hFpos : ∀ d ∈ F, 0 < d := by
    intro d hd
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hd
    omega
  have hinj : Set.InjOn Nat.toPNat' (F : Set ℕ) := by
    intro x hx y hy hxy
    have hx1 := hFpos x hx
    have hy1 := hFpos y hy
    have h := congrArg (fun z : ℕ+ => (z : ℕ)) hxy
    simpa [Nat.toPNat'_coe, hx1, hy1] using h
  have hcos : ∀ t : ℝ,
      cosineSum A t = ∑ d ∈ Finset.Icc 1 Nw, a d * Real.cos (2 * Real.pi * d * t) := by
    intro t
    unfold cosineSum
    rw [hA, Finset.sum_image hinj, hF, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 0 < d := by rw [Finset.mem_Icc] at hd; omega
    have hd' : ((Nat.toPNat' d : ℕ+) : ℕ) = d := by rw [Nat.toPNat'_coe]; simp [hd1]
    rw [hd']
    rcases ha01 d with h | h <;> simp [h]
  have hcard : (A.card : ℝ) = ∑ d ∈ Finset.Icc 1 Nw, a d := by
    have h := hcos 0
    simp only [mul_zero, Real.cos_zero, mul_one] at h
    rw [← h]
    simp [cosineSum]
  have hbig : C₁ * p * L / T ≤ c * p ^ 2 / (2 * T) := by
    rw [div_le_div_iff₀ hTpos (by positivity)]
    have : 2 * C₁ * L * (p * T) ≤ c * p * (p * T) :=
      mul_le_mul_of_nonneg_right hpC₁ (by positivity)
    linarith
  have hcardM : c * p ^ 2 / (2 * T) ≤ A.card := by
    have h0 := hdiff 0
    simp only [mul_zero, Real.cos_zero, mul_one] at h0
    have h1 := (abs_le.1 h0).1
    have h2 : c * p ^ 2 / T = 2 * (c * p ^ 2 / (2 * T)) := by field_simp
    rw [hcard]
    linarith
  have hMN : (N : ℝ) ≤ c * p ^ 2 / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]
    have : 2 * T * N * 1 ≤ c * p * p := mul_le_mul hpN hp1 (by norm_num) (by positivity)
    linarith
  refine ⟨A, ?_, ?_⟩
  · exact_mod_cast hMN.trans hcardM
  · intro t
    rw [hcos t]
    have h1 := (abs_le.1 (hdiff t)).1
    have h2 := hlow t
    have hsq : K * p * L / T < ε * Real.sqrt (A.card : ℝ) := by
      have hx : 0 ≤ K * p * L / T / ε := by positivity
      have hlt : (K * p * L / T / ε) ^ 2 < (A.card : ℝ) := by
        refine lt_of_lt_of_le ?_ hcardM
        rw [div_pow, div_pow, mul_pow, mul_pow, div_div,
          div_lt_div_iff₀ (by positivity) (by positivity)]
        have hp2 : 0 < (p : ℝ) ^ 2 * T := by positivity
        have := mul_lt_mul_of_pos_left hiii hp2
        linarith
      have h := (Real.lt_sqrt hx).2 hlt
      rw [div_lt_iff₀ hε] at h
      linarith
    have hKsplit : K * p * L / T = C * p * L / T + C₁ * p * L / T := by rw [hK]; ring
    linarith

end ChowlaOpus

end

/- Adapted from ChowlaOpus/Main.lean. -/
section

/-
# Theorem 1: a counterexample to Chowla's cosine conjecture
-/

namespace ChowlaOpus

theorem lemma3_final : Lemma3Statement :=
  lemma3Statement_holds bumpStatement_holds
    (coeffStatement_holds annulusStatement_holds)
    (coeffMassStatement_holds annulusStatement_holds)
    (wboundStatement_holds annulusStatement_holds fejerStatement_holds)
    (qposStatement_holds j0Statement_holds besselPlaneStatement_holds multStatement_holds
      (mellinStatement_holds j0Statement_holds besselPlaneStatement_holds)
      annulusStatement_holds fejerStatement_holds)
    (varStatement_holds annulusStatement_holds fejerStatement_holds
      (wrepStatement_holds annulusStatement_holds fejerStatement_holds)
      (wboundStatement_holds annulusStatement_holds fejerStatement_holds))

theorem profile_final : ProfileStatement :=
  profileStatement_holds lemma3_final sawStatement_holds fejerStatement_holds
    fourierDecayStatement_holds

theorem weights_final : WeightsStatement :=
  weightsStatement_holds profile_final crtStatement_holds
    (phaseStatement_holds kernelCharStatement_holds) rowSumStatement_holds multStatement_holds
    (w9Statement_holds rowSumStatement_holds poissonStatement_holds
      plainPoissonStatement_holds multStatement_holds)
    (w10Statement_holds rowSumStatement_holds poissonStatement_holds
      fourierDecayStatement_holds)

theorem rounding_final : RoundingStatement :=
  roundingStatement_holds (spencerStatement_holds partialColoringStatement_holds)
    meshStatement_holds

/-- **Theorem 1.** For every `ε > 0` there are arbitrarily large finite sets `A` of positive
integers with `f_A(t) > -ε √|A|` for every real `t`. -/
theorem main_theorem (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧ ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) < cosineSum A t :=
  cosine_counterexample_of weights_final rounding_final ε hε N

end ChowlaOpus

end

section
open Real Filter
open scoped Finset

theorem OMA.disproof : ¬ (type_of% @Erdos510.erdos_510) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  obtain ⟨A, hcard, hA⟩ := ChowlaOpus.main_theorem c hc N₀
  obtain ⟨θ, hθ⟩ := hN₀ A.card hcard (A.map ⟨PNat.val, PNat.coe_injective⟩)
    (by simp) (by simp)
  have key : -c * Real.sqrt (A.card : ℝ) <
      ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * (θ / (2 * π))) :=
    hA (θ / (2 * π))
  have hsum : ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * (θ / (2 * π))) =
      ∑ n ∈ A.map ⟨PNat.val, PNat.coe_injective⟩, cos (n * θ) := by
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hπ : π ≠ 0 := Real.pi_ne_zero
    congr 1
    field_simp
  linarith
end
