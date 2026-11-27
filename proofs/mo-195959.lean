import OMAStatements.S_mo_195959

/-
The Bernstein-Widder representation below is adapted from work of the Tau Ceti contributors,
Copyright (c) 2026. Source revision afb1aacb3632d3236eee756ea1683290c07270a3:
https://github.com/TauCetiProject/TauCeti/tree/afb1aacb3632d3236eee756ea1683290c07270a3
This version collects the required results in one compilation unit and ports them to the
project's pinned Mathlib. The copula comparison follows those results. The license for the
Tau Ceti portions follows.
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

/- TauCeti.Analysis.Calculus.IteratedDerivWithin -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



/-!
# Generic lemmas for iterated derivatives within sets

This file records calculus lemmas about `iteratedDerivWithin` that are independent of any
completely-monotone or Bernstein-function structure.

## Main declarations

* `TauCeti.ContDiffOn.hasDerivAt_iteratedDerivWithin`: differentiability of an
  `iteratedDerivWithin` on a neighbourhood inside a unique-differentiability set.
For the plain fundamental-theorem identity on a compact interval use Mathlib's
`intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc` together with
`iteratedDerivWithin_one`.
-/


open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- At a point `x` in the interior of a unique-differentiability set `s` (`s ∈ 𝓝 x`),
the derivative of the `k`-th iterated derivative-within-`s` of a `C^(k+1)` function is the
`(k+1)`-th iterated derivative-within-`s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {g : 𝕜 → E} {s : Set 𝕜} {k : ℕ} (hf : ContDiffOn 𝕜 ((k + 1 : ℕ) : WithTop ℕ∞) g s)
    (hs : UniqueDiffOn 𝕜 s) {x : 𝕜} (hx : s ∈ nhds x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hx]
  exact (hf.differentiableOn_iteratedDerivWithin
    (by exact_mod_cast Nat.lt_succ_self k) hs).hasDerivAt hx

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Basic -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/







/-!
# Completely monotone functions

A function `f : ℝ → ℝ` is *completely monotone* if it is smooth on the closed half-line
`[0, ∞)` and its iterated derivatives there alternate in sign:
`(-1)ⁿ f⁽ⁿ⁾(t) ≥ 0` for every `n` and every `t ≥ 0`. Equivalently `f` is nonnegative,
nonincreasing, convex, and so on through every order. Bernstein's theorem identifies the
completely monotone functions on the *open* half-line `(0, ∞)` with the Laplace transforms of
positive measures on `[0, ∞)`. Demanding smoothness up to the boundary point `0`, as we do
here, is a genuine strengthening: it carves out the subclass whose representing measure has
every moment finite. (It thereby excludes some Laplace transforms of finite measures, such as
`t ↦ ∫₀^∞ e^{-x t} (1 + x)⁻² dx`, which is finite at `0` yet has `f'(0⁺) = -∞`.) The
prototypes `t ↦ e^{-x t}` (`x ≥ 0`) are the extreme rays out of which Bernstein's theorem
builds the general member.

The smoothness clause is essential and is not folded into the sign condition: an iterated
derivative defaults to a junk value where the function fails to be differentiable, so
without it a badly behaved `f` could satisfy `0 ≤ 0` vacuously. We phrase the sign condition
through `iteratedDerivWithin _ (Set.Ici 0)`, the derivative *within* the closed half-line,
which is the object that pairs cleanly with `ContDiffOn` (in particular at the boundary
point `0`); on the open half-line it agrees with the ordinary iterated derivative.

## Main declarations

* `TauCeti.IsCompletelyMonotone`: the predicate that `f` is smooth and sign-alternating on
  `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.congr`: complete monotonicity only depends on the values of the
  function on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.nonneg`, `TauCeti.IsCompletelyMonotone.derivWithin_nonpos`,
  `TauCeti.IsCompletelyMonotone.antitoneOn`: a completely monotone function is nonnegative
  and nonincreasing on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotoneOnIci.exists_nonneg_tendsto_atTop`,
  `TauCeti.IsCompletelyMonotoneOnIci.le_of_tendsto_atTop`: order-limit consequences of
  nonnegativity and monotonicity on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_iteratedDeriv_nonneg`: on the open half-line,
  the sign condition also holds for ordinary iterated derivatives.
* `TauCeti.IsCompletelyMonotone.add`, `TauCeti.IsCompletelyMonotone.sum`,
  `TauCeti.IsCompletelyMonotone.smul`: closure under addition, finite sums, and nonnegative
  scalar multiples.
* `TauCeti.IsCompletelyMonotoneOnIoi`: the open-half-line analogue, using ordinary iterated
  derivatives on `(0, ∞)`.
* `TauCeti.IsCompletelyMonotoneOnIci`: the closed-half-line predicate used by the
  finite-measure Hausdorff--Bernstein--Widder theorem: continuity on `[0, ∞)` plus complete
  monotonicity on `(0, ∞)`.
* `TauCeti.isCompletelyMonotone_const`: a nonnegative constant is completely monotone.
* `TauCeti.isCompletelyMonotone_exp_neg_mul`: the building block `t ↦ e^{-x t}` for `x ≥ 0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/


open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A function `f : ℝ → ℝ` is **completely monotone** if it is `C^∞` on the closed half-line
`[0, ∞)` and its iterated derivatives within `[0, ∞)` alternate in sign:
`0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. The smoothness clause prevents the sign
condition from being satisfied vacuously by a junk iterated derivative. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ici 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t

/-- `IsCompletelyMonotone f` unfolds to its defining conjunction: `f` is `C^∞` on `[0, ∞)`
and its iterated derivatives within `[0, ∞)` alternate in sign. -/
lemma isCompletelyMonotone_iff {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔
      ContDiffOn ℝ ∞ f (Ici 0) ∧
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t :=
  Iff.rfl

/-- Completely monotone functions are exactly absolutely monotone functions after reflecting the
closed half-line through zero. -/
lemma isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔ AbsolutelyMonotoneOn (fun u => f (-u)) (Iic 0) := by
  rw [isCompletelyMonotone_iff,
    AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg (uniqueDiffOn_Iic 0)]
  constructor
  -- Reflect smoothness and the alternating-sign condition from `[0, ∞)` to `(-∞, 0]`.
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n u hu => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Ici 0) = Iic 0 := by
        ext x
        simp
      rw [← hpre]
      simpa [Function.comp_def] using
        hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)
    · rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) u]
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset]
      simpa [smul_eq_mul] using hsign n (-u) (neg_nonneg.mpr hu)
  -- Reflect the absolutely-monotone data back to the original closed half-line.
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n t ht => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Iic 0) = Ici 0 := by
        ext x
        simp
      rw [← hpre]
      simpa [Function.comp_def] using
        hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)
    · have hsign' := hsign n (-t) (mem_Iic.mpr (neg_nonpos.mpr ht))
      rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) (-t)] at hsign'
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset] at hsign'
      simpa [smul_eq_mul] using hsign'

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- A completely monotone function is `C^∞` on `[0, ∞)`. -/
lemma contDiffOn (hf : IsCompletelyMonotone f) : ContDiffOn ℝ ∞ f (Ici 0) := hf.1

/-- The sign-alternation property of the iterated derivatives of a completely monotone
function: `0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. -/
lemma neg_one_pow_mul_iteratedDerivWithin_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t := hf.2 n t ht

/-- On the open half-line, the completely monotone sign condition can be read using ordinary
iterated derivatives instead of derivatives within `[0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := by
  have hnhds : Ici (0 : ℝ) ∈ 𝓝 t :=
    mem_of_superset (isOpen_Ioi.mem_nhds ht) Ioi_subset_Ici_self
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
    (mem_Ici.mpr ht.le)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le

/-- A completely monotone function is nonnegative on `[0, ∞)`. -/
lemma nonneg (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  simpa [iteratedDerivWithin_zero] using hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 0 ht

/-- The derivative within `[0, ∞)` of a completely monotone function is nonpositive: it is
nonincreasing. -/
lemma derivWithin_nonpos (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin f (Ici 0) t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 1 ht
  rw [pow_one, iteratedDerivWithin_one] at h
  linarith

/-- Complete monotonicity is determined by the values of the function on `[0, ∞)`: if `g` agrees
with a completely monotone `f` throughout `[0, ∞)`, then `g` is completely monotone too. Both the
smoothness clause and the sign condition only see the function within `[0, ∞)`. -/
lemma congr (hf : IsCompletelyMonotone f) (h : Set.EqOn g f (Ici 0)) :
    IsCompletelyMonotone g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_congr h (mem_Ici.mpr ht)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht


end IsCompletelyMonotone

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- For a completely monotone `f`, the `k`-th iterated derivative within `[0, ∞)` is
differentiable at any `t > 0`, with derivative the `(k+1)`-th iterated derivative. -/
lemma hasDerivAt_iteratedDerivWithin_succ
    (hcm : IsCompletelyMonotone f) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDerivWithin k f (Ici 0))
      (iteratedDerivWithin (k + 1) f (Ici 0) t) t := by
  have horder : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  exact ContDiffOn.hasDerivAt_iteratedDerivWithin (k := k)
    (hcm.contDiffOn.of_le horder) (uniqueDiffOn_Ici 0) (Ici_mem_nhds ht)

/-- Completely monotone functions are closed under addition. -/
lemma add (hf : IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    IsCompletelyMonotone (f + g) := by
  rw [isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg]
  convert (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hf).add
    (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hg) using 1
  ext u
  simp [Pi.add_apply]

end IsCompletelyMonotone

/-- A nonnegative constant function is completely monotone. -/
lemma isCompletelyMonotone_const {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (fun _ : ℝ => c) := by
  refine ⟨contDiffOn_const, fun n t _ => ?_⟩
  rcases n with _ | n
  · simpa [iteratedDerivWithin_const] using hc
  · simp [iteratedDerivWithin_const]

/-- Complete monotonicity on the open half-line `(0, ∞)`: the function is `C^∞` there and its
ordinary iterated derivatives alternate in sign. This is the version used for derivatives of
Bernstein functions, whose right derivatives need not be finite at `0`. -/
def IsCompletelyMonotoneOnIoi (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1) ^ n * iteratedDeriv n f t

namespace IsCompletelyMonotoneOnIoi

variable {f g : ℝ → ℝ}

/-- A completely monotone function on `(0, ∞)` is smooth there. -/
lemma contDiffOn (hf : IsCompletelyMonotoneOnIoi f) : ContDiffOn ℝ ∞ f (Ioi 0) := hf.1

/-- The sign-alternation property on `(0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotoneOnIoi f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := hf.2 n t ht

/-- A completely monotone function on `(0, ∞)` is nonnegative there. -/
lemma nonneg (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  simpa [iteratedDeriv_zero] using hf.neg_one_pow_mul_iteratedDeriv_nonneg 0 ht

/-- A function completely monotone on `(0, ∞)` that is continuous within `[0, ∞)` at the origin
is nonnegative on all of `[0, ∞)`: nonnegativity on `(0, ∞)` passes to the boundary point `0` in
the limit. -/
lemma nonneg_of_continuousWithinAt (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousWithinAt f (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases ht.lt_or_eq with h | h
  · exact hf.nonneg h
  · subst h
    have htends : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (nhds (f 0)) :=
      hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact ge_of_tendsto htends (eventually_mem_nhdsWithin.mono fun x hx => hf.nonneg hx)

/-- The derivative of a completely monotone function on `(0, ∞)` is nonpositive there. -/
lemma deriv_nonpos (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) :
    deriv f t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDeriv_nonneg 1 ht
  rw [pow_one, iteratedDeriv_one] at h
  linarith

/-- Complete monotonicity on `(0, ∞)` is preserved by pointwise equality there. -/
lemma congr (hf : IsCompletelyMonotoneOnIoi f) (h : Set.EqOn g f (Ioi 0)) :
    IsCompletelyMonotoneOnIoi g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [Filter.EventuallyEq.iteratedDeriv_eq n (h.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht))]
  exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht

/-- Complete monotonicity on `(0, ∞)` is closed under addition. -/
lemma add (hf : IsCompletelyMonotoneOnIoi f) (hg : IsCompletelyMonotoneOnIoi g) :
    IsCompletelyMonotoneOnIoi (f + g) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun n t ht => ?_⟩
  rw [iteratedDeriv_add
    ((hf.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))
    ((hg.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))]
  simpa [mul_add] using add_nonneg (hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht)
    (hg.neg_one_pow_mul_iteratedDeriv_nonneg n ht)

/-- The closed-half-line Tau Ceti predicate restricts to complete monotonicity on `(0, ∞)`. -/
lemma _root_.TauCeti.IsCompletelyMonotone.isCompletelyMonotoneOnIoi
    (hf : IsCompletelyMonotone f) : IsCompletelyMonotoneOnIoi f :=
  ⟨hf.contDiffOn.mono Ioi_subset_Ici_self,
    fun n _ ht => hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht⟩

/-- Positive right-translates of a function completely monotone on `(0, ∞)` satisfy the
strong closed-half-line predicate: the shift moves the boundary into the open half-line, where
all derivatives exist. Compare `IsCompletelyMonotone.comp_add_const`, which keeps the strong
predicate under nonnegative translates. -/
lemma isCompletelyMonotone_comp_add_const (hf : IsCompletelyMonotoneOnIoi f) {a : ℝ}
    (ha : 0 < a) :
    IsCompletelyMonotone (fun t : ℝ => f (t + a)) := by
  refine ⟨?_, fun n t ht => ?_⟩
  · have hmaps : MapsTo (fun t : ℝ => t + a) (Ici 0) (Ioi 0) := fun t ht =>
      mem_Ioi.mpr (by linarith [mem_Ici.mp ht])
    exact hf.contDiffOn.comp (by fun_prop) hmaps
  · have htpa : 0 < t + a := by linarith
    have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => f (t + a)) t := by
      have hc : ContDiffAt ℝ (n : WithTop ℕ∞) f (t + a) :=
        (hf.contDiffOn.contDiffAt
          (isOpen_Ioi.mem_nhds htpa)).of_le (by exact_mod_cast le_top)
      simpa [Function.comp_def] using hc.comp t
        (by fun_prop : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => t + a) t)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont (mem_Ici.mpr ht),
      iteratedDeriv_comp_add_const]
    exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n htpa

end IsCompletelyMonotoneOnIoi

/-! ## Closed-half-line complete monotonicity -/

/-- Roadmap-level complete monotonicity on the closed half-line.

This is the classical finite-measure hypothesis: the function is continuous on `[0, ∞)` and
completely monotone on the open half-line `(0, ∞)`. It is weaker at the endpoint than the existing
`IsCompletelyMonotone`, which requires all derivatives within `[0, ∞)` to exist at `0`. -/
def IsCompletelyMonotoneOnIci (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ici 0) ∧ IsCompletelyMonotoneOnIoi f

namespace IsCompletelyMonotoneOnIci

variable {f g : ℝ → ℝ}

/-- A closed-half-line completely monotone function is continuous on `[0, ∞)`. -/
lemma continuousOn (hf : IsCompletelyMonotoneOnIci f) : ContinuousOn f (Ici 0) := hf.1

/-- A closed-half-line completely monotone function is completely monotone on `(0, ∞)`. -/
lemma isCompletelyMonotoneOnIoi (hf : IsCompletelyMonotoneOnIci f) :
    IsCompletelyMonotoneOnIoi f := hf.2

/-- The existing strong Tau Ceti predicate implies the roadmap-level closed-half-line predicate. -/
lemma of_isCompletelyMonotone (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotoneOnIci f :=
  ⟨hf.contDiffOn.continuousOn, hf.isCompletelyMonotoneOnIoi⟩

/-- Closed-half-line complete monotonicity is closed under addition. -/
lemma add (hf : IsCompletelyMonotoneOnIci f) (hg : IsCompletelyMonotoneOnIci g) :
    IsCompletelyMonotoneOnIci (f + g) :=
  ⟨hf.continuousOn.add hg.continuousOn,
    hf.isCompletelyMonotoneOnIoi.add hg.isCompletelyMonotoneOnIoi⟩



/-- A closed-half-line completely monotone function is nonincreasing on `[0, ∞)`: the
derivative is nonpositive on the interior and continuity extends the monotonicity to the
endpoint. -/
lemma antitoneOn (hf : IsCompletelyMonotoneOnIci f) : AntitoneOn f (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hf.continuousOn
    (by
      simpa [interior_Ici] using
        hf.isCompletelyMonotoneOnIoi.contDiffOn.differentiableOn (by simp))
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact hf.isCompletelyMonotoneOnIoi.deriv_nonpos hx

/-- A closed-half-line completely monotone function is nonnegative on `[0, ∞)`:
nonnegativity on the open half-line passes to `0` by continuity. -/
lemma nonneg (hf : IsCompletelyMonotoneOnIci f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t :=
  hf.isCompletelyMonotoneOnIoi.nonneg_of_continuousWithinAt
    (hf.continuousOn.continuousWithinAt (by simp)) ht

/-- A closed-half-line completely monotone function is nonnegative at `0`. -/
lemma nonneg_zero (hf : IsCompletelyMonotoneOnIci f) : 0 ≤ f 0 :=
  hf.nonneg le_rfl

/-- A closed-half-line completely monotone function lies below its value at `0` on `[0, ∞)`. -/
lemma le_apply_zero (hf : IsCompletelyMonotoneOnIci f) {t : ℝ} (ht : 0 ≤ t) : f t ≤ f 0 :=
  hf.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht


/-- Closed-half-line complete monotonicity is determined by values on `[0, ∞)`. -/
lemma congr (hf : IsCompletelyMonotoneOnIci f) (h : EqOn g f (Ici 0)) :
    IsCompletelyMonotoneOnIci g := by
  refine ⟨hf.continuousOn.congr fun x hx => h hx, ?_⟩
  exact hf.isCompletelyMonotoneOnIoi.congr fun x hx => h (Ioi_subset_Ici_self hx)

end IsCompletelyMonotoneOnIci

/-- The `max`-truncation of a function antitone on a closed half-line is antitone everywhere:
the shared totalization step of the half-line limit lemmas below. -/
private lemma antitone_comp_max {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a)) :
    Antitone fun t : ℝ => f (max t a) := fun _ _ hab =>
  hf (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max_right a hab)

/-- A function antitone and bounded below on a closed half-line converges at infinity. -/
private lemma exists_tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    (hbdd : BddBelow (f '' Ici a)) :
    ∃ L, Tendsto f atTop (𝓝 L) := by
  set g := fun t : ℝ => f (max t a) with hg
  have hg_anti : Antitone g := antitone_comp_max hf
  have hg_bdd : BddBelow (Set.range g) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨b, by rintro y ⟨t, rfl⟩; exact hb ⟨max t a, mem_Ici.mpr (le_max_right _ _), rfl⟩⟩
  refine ⟨⨅ i, g i, ?_⟩
  exact (tendsto_atTop_ciInf hg_anti hg_bdd).congr'
    (eventually_atTop.mpr ⟨a, fun t ht => by simp [hg, max_eq_left ht]⟩)

/-- A function antitone on a closed half-line lies above its limit at infinity there. -/
private lemma le_of_tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    {L : ℝ} (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : a ≤ T) : L ≤ f T := by
  set g₀ := fun t : ℝ => f (max t a) with hg₀
  have hg_anti : Antitone g₀ := antitone_comp_max hf
  have := hg_anti.le_of_tendsto
    (hL.congr' (eventually_atTop.mpr ⟨a, fun t ht => by simp [hg₀, max_eq_left ht]⟩)) T
  simpa [hg₀, max_eq_left hT] using this

namespace IsCompletelyMonotoneOnIci

variable {f : ℝ → ℝ}

/-- A closed-half-line completely monotone function has a limit `L ≥ 0` at infinity: it is
antitone on `[0, ∞)` and bounded below by `0`. -/
lemma exists_nonneg_tendsto_atTop (hf : IsCompletelyMonotoneOnIci f) :
    ∃ L, Tendsto f atTop (𝓝 L) ∧ 0 ≤ L := by
  obtain ⟨L, hL⟩ := exists_tendsto_atTop_of_antitoneOn_Ici hf.antitoneOn
    ⟨0, by rintro y ⟨x, hx, rfl⟩; exact hf.nonneg hx⟩
  exact ⟨L, hL, ge_of_tendsto hL (eventually_atTop.mpr ⟨0, fun t ht => hf.nonneg ht⟩)⟩

/-- A closed-half-line completely monotone function lies above its limit at infinity on
`[0, ∞)`. -/
lemma le_of_tendsto_atTop (hcm : IsCompletelyMonotoneOnIci f) {L : ℝ}
    (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : 0 ≤ T) : L ≤ f T :=
  le_of_tendsto_atTop_of_antitoneOn_Ici hcm.antitoneOn hL hT

end IsCompletelyMonotoneOnIci

namespace IsCompletelyMonotone

variable {f : ℝ → ℝ}

/-- A completely monotone function is nonincreasing on `[0, ∞)`: the strong predicate
implies the closed-half-line one, whose monotonicity applies. -/
lemma antitoneOn (hf : IsCompletelyMonotone f) : AntitoneOn f (Ici 0) :=
  (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hf).antitoneOn

end IsCompletelyMonotone

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



/-!
# The Laplace kernel on `ℝ≥0`

The exponential kernel `p ↦ e^{-xp}` of the Laplace transform on `ℝ≥0`, as a plain function
and as a bundled bounded continuous function, together with its basic bounds and its
integrability against finite measures. This lightweight module is shared by the Chafaï
approximating-measure machinery and the Laplace-representation theory, which otherwise do not
depend on each other.

## Main declarations

* `TauCeti.laplaceKernelBoundedContinuous`: the kernel as a bounded continuous function.
* `TauCeti.integrable_exp_neg_mul`: the kernel is integrable against any finite measure.
-/


open MeasureTheory
open scoped BoundedContinuousFunction NNReal

namespace TauCeti

/-- The Laplace kernel `p ↦ e^{-tp}` is continuous in the coordinate variable. -/
lemma continuous_exp_neg_mul (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ x` the Laplace kernel is bounded by `1` on `ℝ≥0`. -/
lemma exp_neg_mul_le_one {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    Real.exp (-(x * (p : ℝ))) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hx p.coe_nonneg)

/-- The Laplace kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed nonnegative `x`. -/
noncomputable def laplaceKernelBoundedContinuous {x : ℝ} (hx : 0 ≤ x) : ℝ≥0 →ᵇ ℝ where
  toFun := fun p => Real.exp (-(x * (p : ℝ)))
  continuous_toFun := continuous_exp_neg_mul x
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 < Real.exp (-(x * (p : ℝ))) := Real.exp_pos _
      have hp1 := exp_neg_mul_le_one hx p
      have hq0 : 0 < Real.exp (-(x * (q : ℝ))) := Real.exp_pos _
      have hq1 := exp_neg_mul_le_one hx q
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled Laplace kernel evaluates to the usual exponential kernel on `ℝ≥0`. -/
@[simp]
lemma laplaceKernelBoundedContinuous_apply {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    laplaceKernelBoundedContinuous hx p = Real.exp (-(x * (p : ℝ))) := by
  rw [laplaceKernelBoundedContinuous]; rfl

/-- **The Laplace kernel is integrable against a finite measure.** For `0 ≤ x` the kernel
`p ↦ e^{-xp}` is bounded and continuous on `ℝ≥0`, hence integrable against any finite measure. -/
lemma integrable_exp_neg_mul (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ := by
  have h := (laplaceKernelBoundedContinuous hx).integrable μ
  rwa [funext (laplaceKernelBoundedContinuous_apply hx)] at h

end TauCeti
end

/- TauCeti.Probability.Moments.Determinacy -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/





/-!
# Moment determinacy of finite measures with finite exponential moments

A finite measure on `ℝ` whose exponential moments are finite in a neighbourhood of the origin is
determined by its sequence of polynomial moments `∫ xⁿ dμ`.  This is the analytic engine behind the
completeness step (**B1**) of the `OrthogonalL2Bases` roadmap
(`TauCetiRoadmap/OrthogonalL2Bases/README.md`, *Part B1 — Completeness toolkit (moment
determinacy)*): the roadmap's `ae_eq_zero_of_forall_moment_eq_zero`-style lemmas rest on the fact
that "vanishing moments" pins a distribution down, which for finite measures is exactly the
determinacy result proved here.

The mechanism is the one the roadmap describes — the (complex) moment-generating function is
analytic on a strip around the imaginary axis, and its Taylor coefficients at `0` are the moments,
so matching moments force the two functions to agree, hence the characteristic functions agree and
the measures coincide.  The proof stays inside Mathlib's `ProbabilityTheory.complexMGF` /
`MeasureTheory.charFun` API:

* `ProbabilityTheory.analyticAt_complexMGF` and `analyticOnNhd_complexMGF` supply the analyticity
  on the strip `{z | z.re ∈ interior (integrableExpSet id μ)}`;
* `ProbabilityTheory.iteratedDeriv_complexMGF` identifies the `n`-th derivative at `0` with the
  `n`-th complex moment;
* the identity principle (`analyticOrderAt_eq_top`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) propagates equality from `0` to the whole
  strip, in particular to the imaginary axis;
* `ProbabilityTheory.complexMGF_id_mul_I` turns the imaginary-axis values into `charFun`, and
  `MeasureTheory.Measure.ext_of_charFun` concludes.

The strip-propagation core of `charFun_eq_of_forall_integral_pow_eq` adapts Mathlib's
`ProbabilityTheory.eqOn_complexMGF_of_mgf'` (`Mathlib/Probability/Moments/ComplexMGF.lean`): it
reuses the same analyticity strip and the same
`convex_integrableExpSet.interior.…linear_preimage Complex.reLm |>.isPreconnected`
identity-principle idiom.  That file's `## TODO` note ("once we know that equal `mgf` implies equal
distributions …")
records the determinacy fact as an open gap in Mathlib; the results here complete it for finite
measures via the polynomial-moment route.

## Main declarations

* `TauCeti.charFun_eq_of_forall_integral_pow_eq`: matching moments (and finite exponential moments
  near `0`) give equal characteristic functions.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq`: matching moments determine a finite measure on
  `ℝ`.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp`: the same conclusion from
  the roadmap's exponential-moment hypothesis `∃ a > 0, Integrable (fun x => exp (a * |x|)) μ`,
  which already puts `0` in the interior of the integrability strip.  This is the form the
  completeness argument consumes: the hypothesis holds for Gaussian decay and automatically for
  compactly supported measures.
-/


namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology

variable {μ ν : Measure ℝ}

end TauCeti
end

/- TauCeti.Probability.Moments.LaplaceDeterminacy -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# A finite measure on `ℝ≥0` is determined by its Laplace transform

## Main results

* `TauCeti.Measure.ext_of_forall_integral_exp_neg_natCast_mul_eq` — the sharp form: the transform's
  values at the natural numbers already determine the measure.
* `TauCeti.Measure.ext_of_forall_integral_exp_neg_mul_eq` — the convenience form, hypothesis at
  every nonnegative real.

## Implementation

The substitution `y = e^{-x}` converts the Laplace transform into a moment sequence: at a natural
argument `n`, `∫ e^{-n x} dμ = ∫ yⁿ d(μ.map (x ↦ e^{-x}))`. So matching Laplace transforms give
pushforwards with matching moments, and the pushforwards are moment-determinate because they are
carried by `(0, 1]` — bounded support makes the exponential-moment hypothesis of
`Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp` automatic. Finally `x ↦ e^{-x}` is
injective and measurable between standard Borel spaces, hence a measurable embedding by
Lusin–Souslin, and `MeasurableEmbedding.map_injective` recovers `μ = ν` from the equal pushforwards.

Only the transform's values at *natural* arguments are used, which is why the primary statement
quantifies over `ℕ`; the real-argument form is a one-line corollary for callers that have it.

This is the uniqueness half of the Bernstein milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B. The existence half is a separate,
independent development, and the two are combined in the Hausdorff--Bernstein--Widder theorem
(`TauCeti.hausdorff_bernstein_widder_existsUnique` in
`Analysis/CompletelyMonotone/Bernstein/HausdorffBernsteinWidder.lean`).
Nothing here mentions complete monotonicity — the statement is about two arbitrary
finite measures — which is why it lives beside the other determinacy results rather than under
`Analysis/CompletelyMonotone/`.
-/



open MeasureTheory Set Filter
open scoped NNReal

namespace TauCeti

/-- The substitution `x ↦ e^{-x}`, which turns Laplace transforms into moments. -/
private def expNeg (x : ℝ≥0) : ℝ := Real.exp (-(x : ℝ))

@[simp]
private theorem expNeg_apply (x : ℝ≥0) : expNeg x = Real.exp (-(x : ℝ)) := rfl

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Laplace.Representation -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




-- Non-public: dominated convergence and the `mgf` derivative and analyticity calculus, all
-- consumed inside proofs only (the latter through the bridge `laplaceTransform_eq_mgf`).


-- Non-public: `Measure.ext_of_forall_integral_exp_neg_natCast_mul_eq` supplies the
-- Laplace-determinacy step in the uniqueness proof.


/-!
# Laplace representations for completely monotone functions

This file contains the Laplace-transform side of the finite-measure
Hausdorff--Bernstein--Widder theorem on `ℝ≥0`: helper lemmas for finite-measure Laplace
transforms and the predicate that a finite measure represents a function by its Laplace transform.

## Main declarations

* `TauCeti.laplaceTransform`: the Laplace transform of a measure on `ℝ≥0`, with its algebraic
  API and the bridge `TauCeti.laplaceTransform_eq_mgf` to Mathlib's moment-generating function.
* `TauCeti.RepresentsLaplace`: the predicate that a finite measure represents a function by its
  Laplace transform on `[0, ∞)`, with `congr`/`add`/`smul`/`unique` API.
* `TauCeti.isCompletelyMonotoneOnIci_laplaceTransform`,
  `TauCeti.isCompletelyMonotone_laplaceTransform_of_moments`: the easy direction of the
  representation theorem, in the closed-half-line and all-moments forms.
* `TauCeti.Measure.ext_of_forall_laplaceTransform_natCast_eq`: finite measures are determined
  by their Laplace transforms at the natural numbers.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV; see also
R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012),
Theorem 1.4. This file provides the Laplace-transform API used by the representation theorem.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/


open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Pointwise Topology

namespace TauCeti

/-! ## Laplace transforms of finite measures on `ℝ≥0` -/

/-- The Laplace transform of a measure on `ℝ≥0`, evaluated at a real parameter `t`.

The theorem statements in this file use the transform only for `0 ≤ t`; for negative `t`, the
Bochner integral is still a total Lean term, but may be the default value when the integrand is not
integrable. -/
noncomputable def laplaceTransform (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ

/-- The defining formula for `laplaceTransform`. Not `@[simp]`: simp should not unfold the
abstraction into a raw integral; the evaluation lemmas below are the simp normal forms. -/
lemma laplaceTransform_apply (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform μ t = ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ := by
  rw [laplaceTransform]



/-- The Laplace transform is the moment-generating function of the coordinate negation
`p ↦ -p` on `ℝ≥0`. This bridge lets the transform consume Mathlib's `mgf` calculus. -/
lemma laplaceTransform_eq_mgf (μ : Measure ℝ≥0) :
    laplaceTransform μ = mgf (fun p : ℝ≥0 => -(p : ℝ)) μ := by
  ext t
  simp only [laplaceTransform, mgf, mul_neg]

/-- The value of the Laplace transform at the parameter `0` is the total mass (under the
total Bochner-integral convention both sides are `0` for an infinite measure). -/
@[simp]
lemma laplaceTransform_zero (μ : Measure ℝ≥0) :
    laplaceTransform μ 0 = μ.real univ := by
  rw [laplaceTransform_eq_mgf, mgf_zero']

/-- The Laplace transform of the zero measure vanishes identically. -/
@[simp]
lemma laplaceTransform_zero_measure (t : ℝ) :
    laplaceTransform (0 : Measure ℝ≥0) t = 0 := by
  simp [laplaceTransform_eq_mgf, mgf_zero_measure]

/-- Additivity of the Laplace transform in the measure, wherever the kernel is integrable
against both summands. -/
lemma laplaceTransform_add_measure (μ ν : Measure ℝ≥0) {t : ℝ}
    (hμ : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ)
    (hν : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) ν) :
    laplaceTransform (μ + ν) t = laplaceTransform μ t + laplaceTransform ν t := by
  simp only [laplaceTransform_eq_mgf]
  exact mgf_add_measure (by simpa [integrableExpSet, mul_neg] using hμ)
    (by simpa [integrableExpSet, mul_neg] using hν)

/-- The Laplace transform of the Dirac mass at `x₀` is the exponential kernel `exp (-(t · x₀))`;
the point masses are the building blocks of the representing mixtures. -/
@[simp]
lemma laplaceTransform_dirac (x₀ : ℝ≥0) (t : ℝ) :
    laplaceTransform (Measure.dirac x₀) t = Real.exp (-(t * (x₀ : ℝ))) := by
  rw [laplaceTransform_eq_mgf, mgf_dirac', mul_neg]

/-! ## Easy direction: finite measures give completely monotone Laplace transforms -/

/-! ## Representation predicate -/

/-- A finite measure represents a function by its Laplace transform on the nonnegative
half-line. -/
def RepresentsLaplace (μ : Measure ℝ≥0) (f : ℝ → ℝ) : Prop :=
  IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t

/-- `RepresentsLaplace μ f` unfolds to finiteness of `μ` and equality with the Laplace transform
on the nonnegative half-line. -/
lemma representsLaplace_iff {f : ℝ → ℝ} {μ : Measure ℝ≥0} :
    RepresentsLaplace μ f ↔
      IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t :=
  Iff.rfl

namespace RepresentsLaplace

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- A representing measure is finite. -/
lemma isFiniteMeasure (h : RepresentsLaplace μ f) : IsFiniteMeasure μ := h.1

/-- A representing measure has the advertised Laplace-transform values on `[0, ∞)`. -/
lemma eq_laplaceTransform (h : RepresentsLaplace μ f) {t : ℝ} (ht : 0 ≤ t) :
    f t = laplaceTransform μ t :=
  h.2 t ht

/-- A representation transports along agreement on the nonnegative half-line: the predicate
constrains `f` only there. -/
protected lemma congr {g : ℝ → ℝ} (hf : RepresentsLaplace μ f) (h : EqOn g f (Ici 0)) :
    RepresentsLaplace μ g :=
  ⟨hf.isFiniteMeasure, fun _ ht => (h (mem_Ici.mpr ht)).trans (hf.eq_laplaceTransform ht)⟩

/-- The sum of two representing measures represents the sum of the functions. -/
protected lemma add {f g : ℝ → ℝ} {μ ν : Measure ℝ≥0}
    (hf : RepresentsLaplace μ f) (hg : RepresentsLaplace ν g) :
    RepresentsLaplace (μ + ν) (f + g) := by
  have := hf.isFiniteMeasure
  have := hg.isFiniteMeasure
  refine ⟨inferInstance, fun t ht => ?_⟩
  rw [Pi.add_apply, hf.eq_laplaceTransform ht, hg.eq_laplaceTransform ht,
    laplaceTransform_add_measure μ ν (integrable_exp_neg_mul μ ht) (integrable_exp_neg_mul ν ht)]

end RepresentsLaplace

/-! ## Uniqueness: finite measures are determined by their Laplace transforms -/

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Closure -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# Closure of completely monotone functions under products and differentiation

This file extends the basic API of `TauCeti.IsCompletelyMonotone` (sums and nonnegative scalar
multiples, in `TauCeti.Analysis.CompletelyMonotone.Basic`) with two further closure properties
called for by the `OneParameterSemigroups` roadmap:

* the **product** of two completely monotone functions is completely monotone, hence so is any
  finite product and any natural power;
* if `f` is completely monotone then so is `t ↦ -f'(t)`, the **negated derivative**.

Both are elementary consequences of the sign-alternation definition. For the product, the
Leibniz rule expands `(-1)ⁿ (fg)⁽ⁿ⁾` as a nonnegative combination
`∑ₖ (n choose k) · [(-1)ᵏ f⁽ᵏ⁾] · [(-1)ⁿ⁻ᵏ g⁽ⁿ⁻ᵏ⁾]` of products of the (nonnegative) alternating
derivatives of `f` and `g`. For the negated derivative, the `(n+1)`-st alternating derivative of
`f` is the `n`-th alternating derivative of `-f'`. Mathlib has the analogous closure lemmas for
`AbsolutelyMonotoneOn` only up to sums and scalar multiples (`AbsolutelyMonotoneOn.add`,
`AbsolutelyMonotoneOn.smul`), so the multiplicative and differential closure built here is new.

These workhorses combine with the prototypes `t ↦ e^{-x t}` to manufacture completely monotone
functions: e.g. any finite sum `∑ⱼ cⱼ e^{-xⱼ t}` with `cⱼ, xⱼ ≥ 0`, or a product like
`t ↦ e^{-x t} / (1 + t)`-style mixtures once their factors are known completely monotone. The
negated-derivative closure is the first step towards the completely-monotone ↔ Bernstein-function
correspondence (a Bernstein function is a nonnegative function whose derivative is completely
monotone).

## Main declarations

* `TauCeti.IsCompletelyMonotone.mul`: completely monotone functions are closed under pointwise
  multiplication.
* `TauCeti.IsCompletelyMonotone.prod`: closure under finite products.
* `TauCeti.IsCompletelyMonotone.pow`: closure under natural powers.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_iteratedDerivWithin`: every alternating
  iterated derivative of a completely monotone function is completely monotone.
* `TauCeti.IsCompletelyMonotone.neg_derivWithin`: the negated derivative within `[0, ∞)` of a
  completely monotone function is completely monotone.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/


open Set
open scoped ContDiff

namespace TauCeti

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- Completely monotone functions are closed under pointwise multiplication. -/
theorem mul (hf : IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    IsCompletelyMonotone (f * g) := by
  refine ⟨hf.contDiffOn.mul hg.contDiffOn, fun n t ht => ?_⟩
  have hmem : t ∈ Ici (0 : ℝ) := mem_Ici.mpr ht
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hfn : ContDiffWithinAt ℝ n f (Ici 0) t :=
    (hf.contDiffOn.contDiffWithinAt hmem).of_le (by exact_mod_cast le_top)
  have hgn : ContDiffWithinAt ℝ n g (Ici 0) t :=
    (hg.contDiffOn.contDiffWithinAt hmem).of_le (by exact_mod_cast le_top)
  rw [iteratedDerivWithin_mul hmem hu hfn hgn, Finset.mul_sum]
  refine Finset.sum_nonneg fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e1 := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg i ht
  have e2 := hg.neg_one_pow_mul_iteratedDerivWithin_nonneg (n - i) ht
  have hsign : ((-1 : ℝ)) ^ n = (-1) ^ i * (-1) ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hin]
  have key : (-1 : ℝ) ^ n * ((n.choose i : ℝ) * iteratedDerivWithin i f (Ici 0) t
        * iteratedDerivWithin (n - i) g (Ici 0) t)
      = (n.choose i : ℝ) * ((-1) ^ i * iteratedDerivWithin i f (Ici 0) t)
        * ((-1) ^ (n - i) * iteratedDerivWithin (n - i) g (Ici 0) t) := by
    rw [hsign]; ring
  rw [key]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) e1) e2

/-- Completely monotone functions are closed under taking natural powers. -/
theorem pow (hf : IsCompletelyMonotone f) (k : ℕ) : IsCompletelyMonotone (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isCompletelyMonotone_const zero_le_one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

/-- Every alternating iterated derivative of a completely monotone function is completely
monotone. -/
theorem neg_one_pow_mul_iteratedDerivWithin (hf : IsCompletelyMonotone f) (k : ℕ) :
    IsCompletelyMonotone (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hcont : ContDiffOn ℝ ∞ (iteratedDerivWithin k f (Ici 0)) (Ici 0) := by
    induction k with
    | zero => simpa [iteratedDerivWithin_zero] using hf.contDiffOn
    | succ k ih =>
        simpa [iteratedDerivWithin_succ] using ih.derivWithin (m := ∞) hu (by simp)
  refine ⟨?_, fun n t ht => ?_⟩
  · simpa [smul_eq_mul] using hcont.const_smul ((-1 : ℝ) ^ k)
  have hshift :
      iteratedDerivWithin n (iteratedDerivWithin k f (Ici 0)) (Ici 0) =
        iteratedDerivWithin (n + k) f (Ici 0) := by
    induction n with
    | zero => simp [iteratedDerivWithin_zero]
    | succ n ih =>
        rw [iteratedDerivWithin_succ, ih, ← iteratedDerivWithin_succ]
        congr 1
        omega
  have hsign := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg (n + k) ht
  have hiter :
      iteratedDerivWithin n
          (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) (Ici 0) t =
        (-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [iteratedDerivWithin_const_mul_field, hshift]
  rw [hiter]
  have key :
      (-1 : ℝ) ^ n * ((-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t) =
        (-1 : ℝ) ^ (n + k) * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [pow_add]
    ring
  rwa [key]

/-- The negated derivative within `[0, ∞)` of a completely monotone function is completely
monotone. -/
theorem neg_derivWithin (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotone (fun t => -derivWithin f (Ici 0) t) := by
  simpa [pow_one, iteratedDerivWithin_one] using hf.neg_one_pow_mul_iteratedDerivWithin 1

end IsCompletelyMonotone

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Integral -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/






/-!
# Integral lemmas for completely monotone functions

Taylor-remainder sign bounds and finite- and improper-integral facts about completely monotone
functions.

These extend the object API in `CompletelyMonotone/Basic.lean` with the sign of the Taylor
integral remainder, the finite-interval integral-of-`(-f')` identity, and improper-integral facts
for the first derivative within `[0, ∞)`.

## Main declarations

* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_taylor_remainder_nonneg`: the Taylor integral
  remainder has sign `(-1)ⁿ`.
* `TauCeti.IsCompletelyMonotone.continuousOn_iteratedDerivWithin_uIcc`: every iterated derivative
  within `[0, ∞)` is continuous on a compact interval `[x, T] ⊆ [0, ∞)`.
* `TauCeti.IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub`: on a compact
  interval in `[0, ∞)`, the integral of `-f'` is the endpoint drop `f x - f T`.
* `TauCeti.IsCompletelyMonotone.neg_iteratedDerivWithin_one_integrableOn`,
  `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one`: integrability and the
  improper integral of `-f'` on `(0, ∞)`, represented as `iteratedDerivWithin 1`.
* `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg`: the same
  improper integral from an arbitrary nonnegative endpoint, `∫ₓ^∞ (-f') = f x - L`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/


open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- For a completely monotone function the `n`-th iterated derivative within a compact interval
`[x, T]` agrees with the one taken within the half-line `[0, ∞)` at any strictly positive interior
point. Complete monotonicity supplies the local `ContDiffAt` hypothesis, and both sides reduce to
the unrestricted iterated derivative at `t`. -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_Icc_eq_Ici (hf : IsCompletelyMonotone f)
    {x T t : ℝ} {n : ℕ} (ht_pos : 0 < t) (ht : t ∈ Ioo x T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici 0) t := by
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (nat_le_top _)
  have hxT : x < T := lt_trans ht.1 ht.2
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hcont
        (Ioo_subset_Icc_self ht),
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
        (mem_Ici.mpr ht_pos.le)]

namespace IsCompletelyMonotone

end IsCompletelyMonotone

/-! ## Smoothness-index helpers -/

/-- The first iterated derivative within `[0, ∞)` of a completely monotone function is
nonpositive (the `derivWithin` sign condition restated for `iteratedDerivWithin 1`). -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_one_nonpos
    (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Ici 0) t ≤ 0 := by
  rw [iteratedDerivWithin_one]; exact hf.derivWithin_nonpos ht

/-- Every iterated derivative within `[0, ∞)` of a completely monotone function is continuous on
the interval spanned by any two nonnegative endpoints. The endpoints need no ordering: `uIcc` is
the unordered interval, and `[0, ∞)` is order-connected. -/
lemma IsCompletelyMonotone.continuousOn_iteratedDerivWithin_uIcc (hcm : IsCompletelyMonotone f)
    (m : ℕ) {x T : ℝ} (hx : 0 ≤ x) (hT : 0 ≤ T) :
    ContinuousOn (iteratedDerivWithin m f (Ici 0)) (uIcc x T) :=
  (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top m)
    (uniqueDiffOn_Ici 0)).mono (ordConnected_Ici.uIcc_subset hx hT)

/-- On a compact interval in `[0, ∞)`, the integral of `-f'` for a completely monotone
function is the endpoint drop, with the derivative taken within `[0, ∞)`. -/
lemma IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub
    (hcm : IsCompletelyMonotone f) {x T : ℝ} (hx : 0 ≤ x) (hxT : x ≤ T) :
    ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t = f x - f T := by
  by_cases h_eq : x = T
  · subst T
    simp
  have htransfer :
      ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t =
      ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hxT] at ht
    have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
    exact congrArg Neg.neg (hcm.iteratedDerivWithin_Icc_eq_Ici ht_pos ht)
  rw [← htransfer]
  simpa [iteratedDerivWithin_one, intervalIntegral.integral_neg, neg_sub] using
    congrArg Neg.neg (intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
      ((hcm.contDiffOn.mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx))).of_le (nat_le_top _)) hxT)

/-- The improper integral `∫ₓ^∞ (-f') dt = f x - L` from an arbitrary nonnegative endpoint `x`,
for a completely monotone function with limit `L` at infinity. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg
    (hcm : IsCompletelyMonotone f) {x : ℝ} (hx : 0 ≤ x) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, -iteratedDerivWithin 1 f (Ici 0) t = f x - L := by
  have hcont : ContinuousWithinAt f (Ici x) x :=
    (hcm.contDiffOn.continuousOn.continuousWithinAt hx).mono (Ici_subset_Ici.mpr hx)
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt f (iteratedDerivWithin 1 f (Ici 0) t) t :=
    fun t ht => hcm.hasDerivAt_iteratedDerivWithin_succ 0 (hx.trans_lt ht)
  have hneg : ∀ t ∈ Ioi x, iteratedDerivWithin 1 f (Ici 0) t ≤ 0 :=
    fun t ht => hcm.iteratedDerivWithin_one_nonpos (hx.trans ht.le)
  have hFTC : ∫ t in Ioi x, iteratedDerivWithin 1 f (Ici 0) t = L - f x :=
    integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hneg hL
  rw [MeasureTheory.integral_neg, hFTC]
  ring

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.Measures -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/





-- Non-public: the bundled Laplace kernel and its integrability.


/-!
# Approximating measures for Bernstein's theorem

The Chafaï-style approximating measures for the **non-constant part** of a completely monotone
function in Bernstein's theorem. For a completely monotone `f` with `L = lim_{t→∞} f t`, the
densities `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` are nonnegative on `[0, ∞)`, the positive
support used by `chafaiMeasure`; they define finite measures whose total mass is bounded by
`f(0) - f(∞) = f(0) - L`, and after the rescaling `t ↦ (n-1)/t` give measures `chafaiRescaled f n`
on `ℝ≥0` whose Laplace kernels `(1 - xp/(n-1))₊ⁿ⁻¹` converge to `e^{-xp}`. These feed the Prokhorov
tightness argument and, in the limit, represent `f - L` (mass `f(0) - L`), i.e. the non-constant
part; the **full** Bernstein representing measure adds the atom `L · δ₀` at `0` (the constant `L =
∫ e^{-tx} d(L·δ₀)`). That final assembly — recovering `f` itself, not merely `f - L` — is performed
downstream in the Bernstein-theorem file, not here. This file supplies only the approximating
infrastructure.

These build on the `IsCompletelyMonotone` API in `CompletelyMonotone/Basic.lean` and
`CompletelyMonotone/Integral.lean`.

## Main declarations

* `TauCeti.chafaiDensity`, `TauCeti.chafaiMeasure`: the approximating densities and measures.
* `TauCeti.bernsteinKernel`, `TauCeti.continuous_bernsteinKernel`,
  `TauCeti.bernsteinKernel_nonneg`, `TauCeti.bernsteinKernel_le_one`,
  `TauCeti.bernsteinKernelBoundedContinuous`,
  `TauCeti.bernsteinKernelBoundedContinuous_apply`, `TauCeti.integrable_bernsteinKernel`,
  `TauCeti.bernsteinKernel_tendsto`: the rescaled Laplace kernel, its bundled
  bounded-continuous `p`-dependence on the nonnegative half-line, and its pointwise limit
  `e^{-xp}` (bundled as `TauCeti.laplaceKernelBoundedContinuous` in
  `CompletelyMonotone/Laplace/Kernel.lean`).
* `TauCeti.integral_exp_neg_mul_add_smul_dirac_zero`: adjoining an atom `c • δ₀` adds exactly
  `c` to the transform, the kernel being `1` at `0`.
* `TauCeti.chafaiRescaled`, `TauCeti.chafaiRescaled_mass_eq`: the `ℝ≥0`-valued pushed-forward
  measures and mass preservation.
* `TauCeti.chafaiRescaled_integral_bernsteinKernel`,
  `TauCeti.chafaiRescaled_integral_bernsteinKernelBoundedContinuous`,
  `TauCeti.ae_nonneg_bernsteinKernel_chafaiRescaled`: characteristic lemmas pairing the
  rescaled Chafaï measures with the Bernstein kernel without unfolding either definition.
* `TauCeti.chafaiMeasure_finite_mass`, `TauCeti.chafaiRescaled_finite_mass`: finiteness and the
  total-mass bound `≤ f(0) - L`.
* `TauCeti.chafaiRescaled_prokhorov_mass_bound`,
  `TauCeti.chafaiRescaled_tendsto_laplace_integral_of_weak`: Prokhorov-ready mass bounds and
  the Laplace test-function specialization of weak convergence for the rescaled measures.
* `TauCeti.chafaiRescaled_lintegral_coe_le`: first-moment / coe-lintegral bound.
* `TauCeti.chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop`: Chafaï
  reconstruction identity `f x - L = ∫ bernsteinKernel ∂chafaiRescaled`.
* `TauCeti.integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound`:
  Bernstein-kernel to Laplace-kernel error tends to `0`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/


open MeasureTheory Set intervalIntegral Filter
open scoped BoundedContinuousFunction ContDiff NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Smoothness-index helpers -/



/-! ## Measure construction for Bernstein -/

/-- The density `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` for nonzero `n`, used for the `n`-th
approximating measure in the Bernstein proof (Chafaï 2013). By convention the `n = 0` branch
returns `0`. -/
noncomputable def chafaiDensity (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
    t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t

/-- `chafaiDensity f 0 = 0`. -/
@[simp] lemma chafaiDensity_zero (f : ℝ → ℝ) (t : ℝ) : chafaiDensity f 0 t = 0 := by
  rw [chafaiDensity, if_pos rfl]

/-- The defining formula for `chafaiDensity` at a nonzero order. -/
@[simp]
lemma chafaiDensity_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    chafaiDensity f n t = (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  rw [chafaiDensity, if_neg hn]

/-- `chafaiDensity f n` is continuous on `[0, ∞)` when `f` has `n` continuous derivatives
there. -/
lemma continuousOn_chafaiDensity {n : ℕ} (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Ici 0)) :
    ContinuousOn (chafaiDensity f n) (Ici 0) := by
  by_cases hn : n = 0
  · subst n
    have hzero : chafaiDensity f 0 = fun _ : ℝ => 0 := funext (chafaiDensity_zero f)
    rw [hzero]
    exact continuousOn_const
  have heq : chafaiDensity f n = fun t => (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t :=
    funext (chafaiDensity_of_ne_zero hn f)
  rw [heq]
  exact (continuousOn_const.mul ((continuousOn_pow _).mono fun _ _ => trivial)).mul
    (hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0))

/-- The `n`-th Chafaï approximating measure `σ_n` for the Bernstein representation, with density
`ρ_n` on
`(0, ∞)`. -/
noncomputable def chafaiMeasure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t))

/-- `chafaiMeasure` as a `withDensity`, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiMeasure_eq_withDensity (f : ℝ → ℝ) (n : ℕ) :
    chafaiMeasure f n =
      (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t)) := by
  rw [chafaiMeasure]

/-- The mass `chafaiMeasure f n` assigns to a measurable set, as a set lintegral of the density. -/
@[simp]
lemma chafaiMeasure_apply (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    chafaiMeasure f n s =
      ∫⁻ t in s, ENNReal.ofReal (chafaiDensity f n t) ∂(volume.restrict (Ioi 0)) := by
  rw [chafaiMeasure, withDensity_apply _ hs]

/-- The density `ρ_n(t)` is nonnegative when `t ≥ 0` and the `n`-th derivative has the
alternating sign at `t`. -/
lemma chafaiDensity_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hsign : 0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) :
    0 ≤ chafaiDensity f n t := by
  simp only [chafaiDensity]
  split_ifs with hn
  · exact le_refl 0
  · have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
          iteratedDerivWithin n f (Ici 0) t
        = t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg ht _) hfact_pos.le) hsign

/-- For `n = 1`, the density simplifies to `-f'(t)`. -/
lemma chafaiDensity_one (t : ℝ) :
    chafaiDensity f 1 t = -iteratedDerivWithin 1 f (Ici 0) t := by
  simp [chafaiDensity]

/-- Difference of two successive Chafaï densities, in the algebraic form used by integration by
parts. -/
private lemma chafaiDensity_succ_succ_sub_succ (f : ℝ → ℝ) (m : ℕ) (t : ℝ) :
    chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t =
      ↑(m + 1) * t ^ m *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 1) f (Ici 0) t) +
        t ^ (m + 1) *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 2) f (Ici 0) t) := by
  -- Put both densities into their nonzero defining branches.
  have hm2 : m + 2 ≠ 0 := by omega
  have hm1 : m + 1 ≠ 0 := by omega
  have hdens_m2 :
      chafaiDensity f (m + 2) t =
        (-1 : ℝ) ^ (m + 2) / ((m + 1).factorial : ℝ) *
          t ^ (m + 1) * iteratedDerivWithin (m + 2) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm2]
    norm_num
  have hdens_m1 :
      chafaiDensity f (m + 1) t =
        (-1 : ℝ) ^ (m + 1) / (m.factorial : ℝ) *
          t ^ m * iteratedDerivWithin (m + 1) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm1]
    norm_num
  rw [hdens_m2, hdens_m1]
  -- Move the two factorial denominators to the same `(m + 1)!` denominator and normalize the
  -- alternating sign.
  have hfact : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * ↑m.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  have hfact_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsucc_ne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hneg : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
  rw [hneg]
  field_simp
  ring

/-! ## Rescaled measures and Prokhorov extraction -/

/-- The Bernstein kernel `φ_n(x,p) = max(1 - xp/(n-1), 0)ⁿ⁻¹` for `n ≥ 2`. After the change of
variable `p = (n-1)/t`, the Taylor integral kernel on `[0, T]` becomes `φ_n(x, p)`, which
converges pointwise to `e^{-xp}` as `n → ∞` (the classical `(1-x/n)ⁿ → e^{-x}` limit). -/
noncomputable def bernsteinKernel (n : ℕ) (x p : ℝ) : ℝ :=
  if n ≤ 1 then 0 else (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1)

/-- The Bernstein kernel vanishes for `n ≤ 1`. -/
@[simp] lemma bernsteinKernel_of_le_one {n : ℕ} (hn : n ≤ 1) (x p : ℝ) :
    bernsteinKernel n x p = 0 := by
  rw [bernsteinKernel, if_pos hn]

/-- The defining formula for the Bernstein kernel at `2 ≤ n`. -/
@[simp]
lemma bernsteinKernel_of_two_le {n : ℕ} (hn : 2 ≤ n) (x p : ℝ) :
    bernsteinKernel n x p = (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1) := by
  have hnle : ¬ n ≤ 1 := by omega
  rw [bernsteinKernel, if_neg hnle]

/-- The Bernstein kernel is continuous in `p` for fixed `n` and `x`. -/
lemma continuous_bernsteinKernel (n : ℕ) (x : ℝ) : Continuous (bernsteinKernel n x) := by
  unfold bernsteinKernel
  split_ifs <;> fun_prop

/-- The Bernstein kernel is nonnegative. -/
@[simp] lemma bernsteinKernel_nonneg (n : ℕ) (x p : ℝ) : 0 ≤ bernsteinKernel n x p := by
  rw [bernsteinKernel]; split_ifs <;> positivity

/-- On the nonnegative half-plane, the Bernstein kernel is bounded above by `1`. -/
lemma bernsteinKernel_le_one {n : ℕ} {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) :
    bernsteinKernel n x p ≤ 1 := by
  rw [bernsteinKernel]
  split_ifs with hn
  · norm_num
  · have hn_pos : (0 : ℝ) < (↑(n - 1) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio_nonneg : 0 ≤ x * p / (↑(n - 1) : ℝ) :=
      div_nonneg (mul_nonneg hx hp) hn_pos.le
    have hbase_nonneg : 0 ≤ max (1 - x * p / (↑(n - 1) : ℝ)) 0 := le_max_right _ _
    have hbase_le_one : max (1 - x * p / (↑(n - 1) : ℝ)) 0 ≤ 1 := by
      exact max_le (by linarith) zero_le_one
    exact pow_le_one₀ hbase_nonneg hbase_le_one

/-- The Bernstein kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed `n` and nonnegative `x`. -/
noncomputable def bernsteinKernelBoundedContinuous (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ℝ≥0 →ᵇ ℝ where
  toFun := fun p => bernsteinKernel n x (p : ℝ)
  continuous_toFun := (continuous_bernsteinKernel n x).comp continuous_subtype_val
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 ≤ bernsteinKernel n x (p : ℝ) := bernsteinKernel_nonneg n x (p : ℝ)
      have hp1 : bernsteinKernel n x (p : ℝ) ≤ 1 := bernsteinKernel_le_one hx p.2
      have hq0 : 0 ≤ bernsteinKernel n x (q : ℝ) := bernsteinKernel_nonneg n x (q : ℝ)
      have hq1 : bernsteinKernel n x (q : ℝ) ≤ 1 := bernsteinKernel_le_one hx q.2
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled Bernstein kernel evaluates to the unbundled kernel on `ℝ≥0`. -/
@[simp]
lemma bernsteinKernelBoundedContinuous_apply (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    bernsteinKernelBoundedContinuous n hx p = bernsteinKernel n x (p : ℝ) := by
  rw [bernsteinKernelBoundedContinuous]; rfl

/-- **The Bernstein kernel at a nonnegative point is integrable against a finite measure.** For
`0 ≤ x`, the map `p ↦ bernsteinKernel n x p` is integrable against any finite measure on `ℝ≥0`.
The companion of `TauCeti.integrable_exp_neg_mul`, which says the same of the Laplace kernel. -/
lemma integrable_bernsteinKernel (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : Integrable (fun p : ℝ≥0 => bernsteinKernel n x (p : ℝ)) μ := by
  have h := (bernsteinKernelBoundedContinuous n hx).integrable μ
  rwa [funext (bernsteinKernelBoundedContinuous_apply n hx)] at h

/-- **An atom at `0` shifts the Laplace transform by its mass.** The kernel takes the value `1` at
`p = 0`, so adjoining `c • δ₀` to a finite measure adds exactly `c`. -/
@[simp]
lemma integral_exp_neg_mul_add_smul_dirac_zero (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (c : ℝ≥0)
    {x : ℝ} (hx : 0 ≤ x) :
    ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂(μ + c • Measure.dirac (0 : ℝ≥0))
      = (∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ) + c := by
  rw [integral_add_measure (integrable_exp_neg_mul μ hx)
      (integrable_exp_neg_mul (c • Measure.dirac (0 : ℝ≥0)) hx),
    integral_smul_nnreal_measure, integral_dirac]
  simp [NNReal.smul_def]

/-- The Bernstein kernel is measurable in `p` for fixed `n` and `x`. -/
lemma measurable_bernsteinKernel (n : ℕ) (x : ℝ) : Measurable (bernsteinKernel n x) := by
  unfold bernsteinKernel; split_ifs
  · exact measurable_const
  · fun_prop

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`. -/
noncomputable def chafaiRescaling (n : ℕ) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (((n : ℝ) - 1) / t)

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`, is measurable. -/
lemma measurable_chafaiRescaling (n : ℕ) :
    Measurable (chafaiRescaling n) :=
  continuous_real_toNNReal.measurable.comp (measurable_const.div measurable_id)

/-- On the positive part of the source, the `ℝ≥0` rescaling coerces back to `(n-1)/t`. -/
@[simp]
lemma chafaiRescaling_coe_of_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    (chafaiRescaling n t : ℝ) = ((n : ℝ) - 1) / t := by
  have hnum : 0 ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  have hnonneg : 0 ≤ ((n : ℝ) - 1) / t := div_nonneg hnum ht.le
  simp [chafaiRescaling, Real.coe_toNNReal', max_eq_left hnonneg]

/-- The rescaled measure `σ̃_n`: pushforward of `chafaiMeasure f n` under the `ℝ≥0` rescaling. -/
noncomputable def chafaiRescaled (f : ℝ → ℝ) (n : ℕ) : Measure ℝ≥0 :=
  Measure.map (chafaiRescaling n) (chafaiMeasure f n)

/-- `chafaiRescaled` as a pushforward, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiRescaled_eq_map (f : ℝ → ℝ) (n : ℕ) :
    chafaiRescaled f n = Measure.map (chafaiRescaling n) (chafaiMeasure f n) := by
  rw [chafaiRescaled]

/-- The mass `chafaiRescaled f n` assigns to a measurable set, as the pushforward formula. -/
@[simp]
lemma chafaiRescaled_apply (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    chafaiRescaled f n s = chafaiMeasure f n ((chafaiRescaling n) ⁻¹' s) := by
  rw [chafaiRescaled, Measure.map_apply (measurable_chafaiRescaling n) hs]

/-- Integrating against `chafaiRescaled f n` is integrating the pullback along the Chafaï
rescaling against `chafaiMeasure f n`. -/
lemma chafaiRescaled_integral (f : ℝ → ℝ) (n : ℕ) {g : ℝ≥0 → ℝ}
    (hg : AEStronglyMeasurable g (chafaiRescaled f n)) :
    ∫ x, g x ∂(chafaiRescaled f n) =
      ∫ t, g (chafaiRescaling n t) ∂(chafaiMeasure f n) := by
  rw [chafaiRescaled_eq_map] at hg ⊢
  exact MeasureTheory.integral_map (measurable_chafaiRescaling n).aemeasurable hg

/-- On positive source points, pulling the Bernstein kernel back along the Chafaï rescaling
gives the classical finite-order kernel `(max (1 - x / t) 0) ^ (n - 1)`. -/
lemma bernsteinKernel_chafaiRescaling_of_pos {n : ℕ} (hn : 2 ≤ n) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    bernsteinKernel n x (chafaiRescaling n t : ℝ) = (max (1 - x / t) 0) ^ (n - 1) := by
  rw [bernsteinKernel_of_two_le hn]
  rw [chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht]
  congr 2
  have hcast : ((n : ℝ) - 1) = (↑(n - 1) : ℝ) := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hn1 : (↑(n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 1 ≠ 0)
  rw [hcast]
  field_simp [hn1, ht.ne']

/-- The Bernstein kernel is nonnegative almost everywhere against every rescaled Chafaï measure.
This is the public positivity lemma consumers need before using monotone or positivity facts for
the kernel pairing. -/
@[simp]
lemma ae_nonneg_bernsteinKernel_chafaiRescaled (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ᵐ[chafaiRescaled f n] fun p : ℝ≥0 => bernsteinKernel n x (p : ℝ) := by
  exact Filter.Eventually.of_forall fun p => bernsteinKernel_nonneg n x (p : ℝ)

/-- Characteristic pairing of the rescaled Chafaï measure with the Bernstein kernel: integrating
`p ↦ φ_n(x,p)` against `chafaiRescaled f n` is the same as integrating its Chafaï-rescaling
pullback against the original Chafaï measure. -/
@[simp]
lemma chafaiRescaled_integral_bernsteinKernel (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    ∫ p, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) =
      ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) := by
  exact chafaiRescaled_integral f n
    (((continuous_bernsteinKernel n x).comp continuous_subtype_val).measurable.aestronglyMeasurable)

/-- Pushforward preserves total mass. -/
lemma chafaiRescaled_mass_eq (f : ℝ → ℝ) (n : ℕ) :
    (chafaiRescaled f n) univ = (chafaiMeasure f n) univ := by
  unfold chafaiRescaled
  rw [Measure.map_apply (measurable_chafaiRescaling n) MeasurableSet.univ, Set.preimage_univ]

private lemma aemeasurable_chafaiDensity_ofReal (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) (n : ℕ) :
    AEMeasurable (fun t => ENNReal.ofReal (chafaiDensity f n t))
      (volume.restrict (Ioi 0)) := by
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) :=
    continuousOn_chafaiDensity (n := n) (hcm.contDiffOn.of_le (nat_le_top n))
  exact ((hcont.mono Ioi_subset_Ici_self).aemeasurable measurableSet_Ioi).ennreal_ofReal

private lemma chafaiDensity_neg_derivWithin_pred (f : ℝ → ℝ)
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    chafaiDensity (fun t => -derivWithin f (Ici 0) t) (n - 1) t =
      ((n : ℝ) - 1) / t * chafaiDensity f n t := by
  have hn0 : n ≠ 0 := by omega
  have hn10 : n - 1 ≠ 0 := by omega
  rw [chafaiDensity_of_ne_zero hn10, chafaiDensity_of_ne_zero hn0]
  have hiter : iteratedDerivWithin (n - 1)
        (fun t => -derivWithin f (Ici 0) t) (Ici 0) t =
      -iteratedDerivWithin n f (Ici 0) t := by
    -- The negated function elaborates as negation of `derivWithin`; expose that defeq.
    change iteratedDerivWithin (n - 1) (-(derivWithin f (Ici 0))) (Ici 0) t =
      -iteratedDerivWithin n f (Ici 0) t
    rw [iteratedDerivWithin_neg]
    congr 1
    rw [← iteratedDerivWithin_succ']
    congr 1
    omega
  rw [hiter]
  have hfact : ((n - 1).factorial : ℝ) =
      ((n - 1 : ℕ) : ℝ) * ((n - 2).factorial : ℝ) := by
    rw [show n - 1 = (n - 2) + 1 by omega, Nat.factorial_succ]
    norm_num
  rw [hfact]
  have hnp : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hsub : n - 1 - 1 = n - 2 := by omega
  have hpow' : t ^ (n - 2) * t = t ^ (n - 1) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
  have hsign : -((-1 : ℝ) ^ (n - 1)) = (-1 : ℝ) ^ n := by
    have hpow : ((-1 : ℝ) ^ n) = (-1 : ℝ) ^ ((n - 1) + 1) := by
      congr
      omega
    rw [hpow, pow_succ]
    ring
  have hden : (n : ℝ) - 1 ≠ 0 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [hnp, hsub]
  field_simp [ht.ne', hden]
  calc
    -(((-1 : ℝ) ^ (n - 1) * t ^ (n - 2) *
          iteratedDerivWithin n f (Ici 0) t * t))
        = -((-1 : ℝ) ^ (n - 1)) * (t ^ (n - 2) * t) *
            iteratedDerivWithin n f (Ici 0) t := by ring
    _ = (-1 : ℝ) ^ n * t ^ (n - 1) *
            iteratedDerivWithin n f (Ici 0) t := by rw [hsign, hpow']
    _ = iteratedDerivWithin n f (Ici 0) t * (-1 : ℝ) ^ n * t ^ (n - 1) := by
          ring

private lemma chafaiRescaled_lintegral_coe_eq_chafaiMeasure_neg_derivWithin
    (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n) =
      (chafaiMeasure (fun t => -derivWithin f (Ici 0) t) (n - 1)) univ := by
  rw [chafaiRescaled_eq_map]
  rw [lintegral_map]
  swap
  · exact ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
  swap
  · exact measurable_chafaiRescaling n
  rw [chafaiMeasure_eq_withDensity]
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  swap
  · exact aemeasurable_chafaiDensity_ofReal f hcm n
  swap
  · exact ((NNReal.continuous_coe.measurable.comp (measurable_chafaiRescaling n)).aemeasurable)
      |>.ennreal_ofReal
  rw [chafaiMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  have hscale : (chafaiRescaling n t : ℝ) = ((n : ℝ) - 1) / t :=
    chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) htpos
  have hdens_nonneg : 0 ≤ chafaiDensity f n t :=
    chafaiDensity_nonneg htpos.le (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n htpos.le)
  have hdens_eq := chafaiDensity_neg_derivWithin_pred f hn htpos
  simp only [Pi.mul_apply]
  rw [hscale, ← ENNReal.ofReal_mul hdens_nonneg, mul_comm, ← hdens_eq]

/-- The Chafaï density of order `n` is interval-integrable on `[0, T]`: it is continuous on
`Ici 0` given `n`-fold differentiability there, and `[0, T]` sits inside that ray. -/
private lemma intervalIntegrable_chafaiDensity {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) f (Ici 0)) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => chafaiDensity f n t) volume 0 T :=
  ((continuousOn_chafaiDensity hf).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hT

/-- **IBP identity** for the CM density:
`∫₀ᵀ ρ_{m+2}(t) dt = B_{m+2}(T) + ∫₀ᵀ ρ_{m+1}(t) dt`. -/
private lemma chafaiDensity_ibp_identity (f : ℝ → ℝ) {m : ℕ}
    (hf : ContDiffOn ℝ ((m + 2 : ℕ) : WithTop ℕ∞) f (Ici 0)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 2) t =
    (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      iteratedDerivWithin (m + 1) f (Ici 0) T +
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 1) t := by
  set c : ℝ := (-1) ^ (m + 2) / ↑(m + 1).factorial
  set g := iteratedDerivWithin (m + 1) f (Ici 0)
  set F := fun t : ℝ => t ^ (m + 1) * (c * g t)
  have hf_m1 : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f (Ici 0) :=
    hf.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))
  -- The primitive is continuous up to the endpoints, and differentiates to the density difference.
  have hF_cont : ContinuousOn F (Icc 0 T) :=
    ((continuous_pow _).continuousOn).mul (continuousOn_const.mul
      ((hf_m1.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0)).mono
        Icc_subset_Ici_self))
  -- The product rule gives two summands; `chafaiDensity_succ_succ_sub_succ` identifies them with
  -- the density difference, which is the form the integrability and FTC steps below want.
  have hF_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t) t := fun t ht => by
    have hg : HasDerivAt g (iteratedDerivWithin (m + 2) f (Ici 0) t) t :=
      ContDiffOn.hasDerivAt_iteratedDerivWithin hf (uniqueDiffOn_Ici 0) (Ici_mem_nhds ht.1)
    exact (chafaiDensity_succ_succ_sub_succ f m t).symm ▸
      (hasDerivAt_pow (m + 1) t).mul (hg.const_mul _)
  -- Both density branches are interval-integrable, so the difference is too.
  have h_int_m2 : IntervalIntegrable (fun t => chafaiDensity f (m + 2) t) volume 0 T :=
    intervalIntegrable_chafaiDensity hf hT.le
  have h_int_m1 : IntervalIntegrable (fun t => chafaiDensity f (m + 1) t) volume 0 T :=
    intervalIntegrable_chafaiDensity hf_m1 hT.le
  -- FTC now reads off the difference of the two integrals directly.
  have hstep1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF_cont hF_deriv
    (h_int_m2.sub h_int_m1)
  have hF0 : F 0 = 0 := by simp [F, zero_pow (by omega : m + 1 ≠ 0)]
  rw [hF0, sub_zero, intervalIntegral.integral_sub h_int_m2 h_int_m1] at hstep1
  -- The lower endpoint vanishes; the upper endpoint is the boundary term in the statement.
  suffices hgoal : (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial * g T = F T by linarith
  simp only [F, c]; ring

/-- Monotonicity of the finite-interval Chafaï-density integrals in the order:
for `2 ≤ k` and `0 ≤ T`, the integral of the `k`-th density on `[0,T]` is bounded above by the
integral of the preceding density, assuming the endpoint has the required alternating sign. -/
lemma integral_chafaiDensity_le_pred (f : ℝ → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f (Ici 0)) (T : ℝ) (hT : 0 ≤ T)
    (hsign : 0 ≤ (-1 : ℝ) ^ (k - 1) * iteratedDerivWithin (k - 1) f (Ici 0) T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f k t ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f (k - 1) t := by
  -- The degenerate interval is immediate; otherwise reindex `k` as `m + 2` for the IBP lemma.
  rcases hT.eq_or_lt with rfl | hT_pos
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  have hibp := chafaiDensity_ibp_identity (m := m) f hf T hT_pos
  set B := (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
    iteratedDerivWithin (m + 1) f (Ici 0) T
  -- The boundary term in the IBP identity is nonpositive by complete-monotone sign alternation.
  have hB : B ≤ 0 := by
    have hsign_m : 0 ≤ (-1 : ℝ) ^ (m + 1) * iteratedDerivWithin (m + 1) f (Ici 0) T := by
      simpa [hsub] using hsign
    have h_neg : (-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T ≤ 0 := by
      have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
      rw [this]; nlinarith [hsign_m]
    suffices B = T ^ (m + 1) / ↑(m + 1).factorial *
        ((-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T) by
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (pow_nonneg hT_pos.le _) (Nat.cast_nonneg _)) h_neg
    simp only [B]; ring
  linarith

/-- The public `n = 0` convention for Chafaï measures: the zeroth approximating measure is
zero. -/
@[simp]
lemma chafaiMeasure_zero (f : ℝ → ℝ) : chafaiMeasure f 0 = 0 := by
  rw [chafaiMeasure_eq_withDensity]
  ext s hs
  rw [withDensity_apply _ hs]
  simp

/-- The rescaled Chafaï measure on the target type `ℝ≥0` shares the `n = 0` zero convention:
`chafaiRescaled f 0 = 0`, as the pushforward of the zero measure. -/
@[simp]
lemma chafaiRescaled_zero (f : ℝ → ℝ) : chafaiRescaled f 0 = 0 := by
  rw [chafaiRescaled_eq_map, chafaiMeasure_zero, Measure.map_zero]

private lemma integral_chafaiDensity_one_eq (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t = f 0 - f T := by
  have h1 : ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t =
      ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t _ => chafaiDensity_one t)
  rw [h1]
  exact IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub hcm le_rfl hT.le

private lemma integral_chafaiDensity_le_sub (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (j : ℕ) (hj : 1 ≤ j) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f j t ≤ f 0 - f T := by
  induction j with
  | zero => omega
  | succ p ih =>
    by_cases hp : p = 0
    · subst hp
      exact le_of_eq (integral_chafaiDensity_one_eq f hcm T hT)
    · calc ∫ t in (0 : ℝ)..T, chafaiDensity f (p + 1) t
          ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f p t := by
            exact integral_chafaiDensity_le_pred f (k := p + 1) (by omega)
              (hcm.contDiffOn.of_le (nat_le_top (p + 1)))
              T hT.le (by
                simpa using hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg p hT.le)
        _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp)

private lemma integral_chafaiDensity_le_tendsto_sub (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto f atTop (nhds L)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f n t ≤ f 0 - L := by
  linarith [integral_chafaiDensity_le_sub f hcm n hn T hT,
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).le_of_tendsto_atTop hL hT.le]

private lemma chafaiDensity_integrableOn_Ioi_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (chafaiDensity f n) (Ioi 0) := by
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) :=
    continuousOn_chafaiDensity (n := n) ((hcm.contDiffOn).of_le (nat_le_top n))
  -- The improper-integrability criterion reduces the proof to compact integrability on each
  -- interval and a uniform bound for interval integrals of `|ρ_n|`.
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
    (l := atTop) (b := id)
  -- Compact integrability comes from continuity of the density on `[0, ∞)`.
  · intro T
    exact (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  · exact tendsto_id
  -- On positive intervals the density is nonnegative, so the norm integral is the density
  -- integral, bounded by the finite-interval Chafaï estimate.
  · filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [id]
    calc ∫ t in (0 : ℝ)..T, ‖chafaiDensity f n t‖
        = ∫ t in (0 : ℝ)..T, chafaiDensity f n t := by
          apply intervalIntegral.integral_congr_ae
          apply ae_of_all
          intro t ht
          rw [uIoc_of_le hT.le] at ht
          rw [Real.norm_eq_abs,
            abs_of_nonneg (chafaiDensity_nonneg ht.1.le
              (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.1.le))]
      _ ≤ f 0 - L := integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T hT

private lemma chafaiMeasure_mass_le_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (hL : Tendsto f atTop (nhds L))
    (hint : IntegrableOn (chafaiDensity f n) (Ioi 0)) :
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  rw [chafaiMeasure_eq_withDensity]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
      chafaiDensity_nonneg ht.le (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le))]
  exact ENNReal.ofReal_le_ofReal
    (le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
      (eventually_atTop.mpr ⟨1, fun T hT =>
        integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T (by linarith)⟩))

/-- **Total mass bound with a chosen limit**: `chafaiMeasure f n` is finite with total mass
`≤ f(0) - L` whenever `f(t) → L` at infinity. -/
lemma chafaiMeasure_finite_mass_of_tendsto (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IsFiniteMeasure (chafaiMeasure f n) ∧
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  by_cases hn0 : n = 0
  · subst n
    rw [chafaiMeasure_zero]
    exact ⟨inferInstance, by simp⟩
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hint : IntegrableOn (chafaiDensity f n) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm n hn L hL
  have hfin : IsFiniteMeasure (chafaiMeasure f n) := by
    unfold chafaiMeasure
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hmass : (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) :=
    chafaiMeasure_mass_le_of_tendsto f hcm n hn L hL hint
  exact ⟨hfin, hmass⟩

/-- **Natural total mass bound**: for a completely monotone `f`, the Chafaï measures are finite
and uniformly bounded by `f(0) - L`, where `L` is the automatically obtained limit of `f` at
infinity. -/
lemma chafaiMeasure_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiMeasure f n) ∧
        (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn⟩ :=
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).exists_nonneg_tendsto_atTop
  exact ⟨L, hL, hL_nn, fun n => chafaiMeasure_finite_mass_of_tendsto f hcm n L hL⟩

/-- **Natural rescaled total mass bound**: for a completely monotone `f`, the rescaled
Chafaï measures on `ℝ≥0` are finite and uniformly bounded by `f(0) - L`, where `L` is the
automatically obtained limit of `f` at infinity. -/
lemma chafaiRescaled_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiRescaled f n) ∧
        (chafaiRescaled f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn, hfinite⟩ := chafaiMeasure_finite_mass f hcm
  refine ⟨L, hL, hL_nn, fun n => ?_⟩
  have hmass := chafaiRescaled_mass_eq f n
  refine ⟨?_, ?_⟩
  · exact ⟨by rw [hmass]; exact (hfinite n).1.measure_univ_lt_top⟩
  · rw [hmass]
    exact (hfinite n).2

/-- Uniform first-moment bound for the rescaled Chafaï measures. -/
lemma chafaiRescaled_lintegral_coe_le (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∀ n,
      ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n) ≤
        ENNReal.ofReal (-derivWithin f (Ici 0) 0) := by
  intro n
  have hderiv_nonneg : 0 ≤ -derivWithin f (Ici 0) 0 := by
    linarith [hcm.derivWithin_nonpos le_rfl]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [chafaiRescaled_zero]
      simp
    · rw [chafaiRescaled_eq_map, lintegral_map]
      swap
      · exact ENNReal.measurable_ofReal.comp
          (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
      swap
      · exact measurable_chafaiRescaling 1
      simp [chafaiRescaling]
  · obtain ⟨L, _hL, hL_nonneg, hfinite⟩ :=
      chafaiMeasure_finite_mass (fun t => -derivWithin f (Ici 0) t) hcm.neg_derivWithin
    calc
      ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n)
          = (chafaiMeasure (fun t => -derivWithin f (Ici 0) t) (n - 1)) univ :=
              chafaiRescaled_lintegral_coe_eq_chafaiMeasure_neg_derivWithin f hcm hn
      _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0 - L) := (hfinite (n - 1)).2
      _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) :=
          ENNReal.ofReal_le_ofReal (by linarith)

/-- Prokhorov-ready mass bound for the rescaled Chafaï measures: a completely monotone function
supplies a nonnegative real mass constant `C = f(0) - L`, where `L` is the limit of `f` at
infinity, such that every `chafaiRescaled f n` is finite and has total mass at most `C`. -/
lemma chafaiRescaled_prokhorov_mass_bound (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, ∃ C : ℝ≥0, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧ (C : ℝ) = f 0 - L ∧
      ∀ n,
        IsFiniteMeasure (chafaiRescaled f n) ∧
        (chafaiRescaled f n) univ ≤ (C : ENNReal) := by
  obtain ⟨L, hL, hL_nn, hfinite⟩ := chafaiRescaled_finite_mass f hcm
  have hL_le : L ≤ f 0 :=
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).le_of_tendsto_atTop hL le_rfl
  let C : ℝ≥0 := ⟨f 0 - L, sub_nonneg.mpr hL_le⟩
  refine ⟨L, C, hL, hL_nn, rfl, fun n => ?_⟩
  refine ⟨(hfinite n).1, ?_⟩
  have hC : (C : ENNReal) = ENNReal.ofReal (f 0 - L) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := C)]
    rfl
  rw [hC]
  exact (hfinite n).2

/-! ## Chafaï reconstruction and Bernstein-to-Laplace replacement -/

private lemma chafai_kernel_density_eq (f : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in Ioi 0, bernsteinKernel n x (((n : ℝ) - 1) / t) *
      chafaiDensity f n t =
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : ¬ n ≤ 1 := by omega
  have hsubset : Ioi x ⊆ Ioi 0 := Ioi_subset_Ioi hx
  have hvanish : ∀ t ∈ Ioi 0 \ Ioi x,
      bernsteinKernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t = 0 := by
    intro t ht
    simp only [Set.mem_sdiff, mem_Ioi, not_lt] at ht
    rw [← chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht.1,
      bernsteinKernel_chafaiRescaling_of_pos hn x ht.1,
      max_eq_right (by rw [sub_nonpos, le_div_iff₀ ht.1]; linarith)]
    rw [zero_pow (by omega : n - 1 ≠ 0), zero_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubset hvanish]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [mem_Ioi] at ht
  have ht_pos : 0 < t := lt_of_le_of_lt hx ht
  dsimp only
  rw [← chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht_pos,
    bernsteinKernel_chafaiRescaling_of_pos hn x ht_pos,
    max_eq_left (by rw [sub_nonneg, div_le_one₀ ht_pos]; linarith)]
  rw [chafaiDensity_of_ne_zero hn0]
  have key : (1 - x / t) ^ (n - 1) * t ^ (n - 1) = (t - x) ^ (n - 1) := by
    rw [← mul_pow]
    congr 1
    field_simp [ne_of_gt ht_pos]
  calc
    (1 - x / t) ^ (n - 1) *
        (((-1 : ℝ) ^ n / ↑(n - 1).factorial * t ^ (n - 1)) *
          iteratedDerivWithin n f (Ici 0) t)
        = (-1 : ℝ) ^ n / ↑(n - 1).factorial *
          ((1 - x / t) ^ (n - 1) * t ^ (n - 1)) *
          iteratedDerivWithin n f (Ici 0) t := by ring
    _ = _ := by rw [key]

/-- For `k ≠ 0`, dividing by `k!` and multiplying by `k` is dividing by `(k - 1)!`. This is the
coefficient bookkeeping produced by differentiating the order-`k` kernel. -/
private lemma div_factorial_mul_natCast {k : ℕ} (hk : k ≠ 0) (c z : ℝ) :
    c / ↑k.factorial * ((k : ℝ) * z) = c / ↑(k - 1).factorial * z := by
  have hfact : k.factorial = k * (k - 1).factorial := (Nat.mul_factorial_pred hk).symm
  rw [hfact]
  push_cast
  field_simp

private lemma ibp_finite_interval (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x T : ℝ) (hx : 0 ≤ x) (hxT : x < T) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t =
    (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Ici 0) T -
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t := by
  set c := (-1 : ℝ) ^ (k + 1) / ↑k.factorial
  set g := iteratedDerivWithin k f (Ici 0)
  set g' := iteratedDerivWithin (k + 1) f (Ici 0)
  set u := fun t : ℝ => c * (t - x) ^ k
  set u' := fun t : ℝ => c * (↑k * (t - x) ^ (k - 1))
  have hu'_eq : ∀ t, u' t =
      (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) := fun t => by
    simp only [u', c]
    exact div_factorial_mul_natCast hk _ _
  have hu_cont : ContinuousOn u (uIcc x T) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow _)
  have hg_cont : ContinuousOn g (uIcc x T) :=
    hcm.continuousOn_iteratedDerivWithin_uIcc k hx (hx.trans hxT.le)
  have hu_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt u (u' t) (Ioi t) t := by
    intro t _ht
    apply HasDerivAt.hasDerivWithinAt
    simpa [u, u', mul_assoc] using
      (((hasDerivAt_pow k (t - x)).comp t
        ((hasDerivAt_id t).sub_const x)).const_mul c)
  have hg_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt g (g' t) (Ioi t) t := by
    intro t ht
    rw [min_eq_left hxT.le, max_eq_right hxT.le] at ht
    exact (hcm.hasDerivAt_iteratedDerivWithin_succ k (lt_of_le_of_lt hx ht.1)).hasDerivWithinAt
  have hu'_int : IntervalIntegrable u' volume x T :=
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _))).intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume x T :=
    (hcm.continuousOn_iteratedDerivWithin_uIcc (k + 1) hx (hx.trans hxT.le)).intervalIntegrable
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu_cont hg_cont hu_deriv hg_deriv hu'_int hg'_int
  have hu0 : u x = 0 := by simp [u, sub_self, zero_pow hk]
  rw [hu0, zero_mul, sub_zero] at hibp
  have h1 : ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
        iteratedDerivWithin (k + 1) f (Ici 0) t =
      ∫ t in x..T, u t * g' t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by ring)
  have h2 : ∫ t in x..T, u' t * g t =
      ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by rw [hu'_eq])
  linarith

private lemma normalized_iteratedDerivWithin_nonneg_antitone (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) :
    (∀ T, 0 ≤ T → 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T) ∧
      AntitoneOn (fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T) (Ici 0) := by
  constructor
  · intro T hT
    exact hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k hT
  · apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top k)
        (uniqueDiffOn_Ici 0)).const_mul ((-1 : ℝ) ^ k)
    · rw [interior_Ici]
      intro T hT
      exact ((hcm.hasDerivAt_iteratedDerivWithin_succ k hT).const_mul
        ((-1 : ℝ) ^ k)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro T hT
      have hderiv : deriv (fun T => (-1 : ℝ) ^ k *
            iteratedDerivWithin k f (Ici 0) T) T =
          (-1 : ℝ) ^ k * iteratedDerivWithin (k + 1) f (Ici 0) T := by
        simpa using
          ((hcm.hasDerivAt_iteratedDerivWithin_succ k hT).const_mul
            ((-1 : ℝ) ^ k)).deriv
      rw [hderiv]
      have hsign : 0 ≤ (-1 : ℝ) ^ (k + 1) *
          iteratedDerivWithin (k + 1) f (Ici 0) T :=
        hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg (k + 1) hT.le
      have hneg : 0 ≤ -(((-1 : ℝ) ^ k) *
          iteratedDerivWithin (k + 1) f (Ici 0) T) := by
        simpa [pow_succ, mul_assoc] using hsign
      linarith

/-- Pointwise lower bound for the density on `Icc (T/2) T`: at each such point `t`,
`chafaiDensity f k` is at least the constant `(1/(k-1)!)·(T/2)^(k-1)·h T`. -/
private lemma chafaiDensity_ge_const_on_Icc (f : ℝ → ℝ) (k : ℕ) (h : ℝ → ℝ)
    (T : ℝ) (hhT_nonneg : 0 ≤ h T) {t : ℝ} (ht : t ∈ Icc (T / 2) T) (hT_le_ht : h T ≤ h t)
    (h_density_eq_t :
      chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t) :
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T ≤ chafaiDensity f k t := by
  -- `0 ≤ T/2` follows from the membership hypothesis `T/2 ≤ t ≤ T`.
  have hT_nonneg : 0 ≤ T := by have := ht.1.trans ht.2; linarith
  -- Combine the power monotonicity `(T/2)^(k-1) ≤ t^(k-1)` with the pointwise bound `h T ≤ h t`.
  have hhalf_nonneg : 0 ≤ T / 2 := by linarith
  have ht_nonneg : 0 ≤ t := le_trans hhalf_nonneg ht.1
  have hpow : (T / 2) ^ (k - 1) ≤ t ^ (k - 1) := pow_le_pow_left₀ hhalf_nonneg ht.1 _
  have hcoeff_nonneg : (0 : ℝ) ≤ 1 / ↑((k - 1).factorial) := by positivity
  have hright_nonneg : 0 ≤ (1 / ↑((k - 1).factorial)) * t ^ (k - 1) :=
    mul_nonneg hcoeff_nonneg (pow_nonneg ht_nonneg _)
  rw [h_density_eq_t]
  calc
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T
        ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h T := by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoeff_nonneg) hhT_nonneg
    _ ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h t :=
          mul_le_mul_of_nonneg_left hT_le_ht hright_nonneg

/-- Interval-integral form of the tail lower bound: integrating the pointwise bound
`chafaiDensity_ge_const_on_Icc` over `[T/2, T]` gives
`(1/(k-1)!)·(T/2)^k·h T ≤ ∫ t in T/2..T, chafaiDensity f k t`. -/
private lemma const_le_intervalIntegral_chafaiDensity (f : ℝ → ℝ) (k : ℕ) (hk : k ≠ 0)
    (h : ℝ → ℝ) (h_antitone : AntitoneOn h (Ici 0)) (T : ℝ) (hT_nonneg : 0 ≤ T) (h_density_eq :
      ∀ t ∈ Icc (T / 2) T,
        chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t)
    (hdens_int : IntervalIntegrable (chafaiDensity f k) volume (T / 2) T)
    (hhT_nonneg : 0 ≤ h T) :
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T ≤
      ∫ t in T / 2..T, chafaiDensity f k t := by
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ =>
        (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) volume (T / 2) T :=
    intervalIntegrable_const
  -- Integrate the pointwise bound `chafaiDensity_ge_const_on_Icc` directly over `[T/2, T]`.
  have hmono_int :=
    intervalIntegral.integral_mono_on (by linarith) hconst_int hdens_int
      (fun t ht => chafaiDensity_ge_const_on_Icc f k h T hhT_nonneg ht
        (h_antitone (le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1) hT_nonneg ht.2)
        (h_density_eq t ht))
  have hlen : T - T / 2 = T / 2 := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono_int
  -- Recombine `(T/2)·(T/2)^(k-1) = (T/2)^k` (uses `k ≠ 0`), as a named algebraic equality.
  have hpow : (T / 2) ^ (k - 1) * (T / 2) = (T / 2) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
  have hconst_eq :
      T / 2 * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) =
        (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T := by
    rw [← hpow]; ring
  rwa [hconst_eq] at hmono_int

/-- Boundary-term tail estimate, the engine of
`tendsto_sub_pow_mul_normalized_iteratedDerivWithin`: `(T-x)^k · h T` is
eventually squeezed by a multiple of the vanishing density tail `∫_{Ioi (T/2)}`. -/
private lemma density_tail_lower_bound_eventually (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) (hk : k ≠ 0) (x : ℝ)
    (h : ℝ → ℝ) (h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T) (h_antitone : AntitoneOn h (Ici 0))
    (h_density_eq : ∀ t, chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t)
    (hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0)) :
    ∀ᶠ T in atTop,
      (T - x) ^ k * h T ≤
        ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t := by
  have hcont_density : ContinuousOn (chafaiDensity f k) (Ici 0) :=
    continuousOn_chafaiDensity (n := k) (hcm.contDiffOn.of_le (nat_le_top k))
  filter_upwards [eventually_gt_atTop (max (2 * |x|) 2)] with T hT
  have hT2 : (2 : ℝ) < T := lt_of_le_of_lt (le_max_right (2 * |x|) 2) hT
  have hTpos : 0 < T := by linarith
  have hTabs : 2 * |x| < T := lt_of_le_of_lt (le_max_left (2 * |x|) 2) hT
  -- the shift is dominated by `T` in both directions, so `T - x` sits between `0` and `2 * T`
  have hTx_nonneg : 0 ≤ T - x := by linarith [le_abs_self x, abs_nonneg x]
  have hTx_le : T - x ≤ 2 * T := by linarith [neg_abs_le x, abs_nonneg x]
  have hhalf_nonneg : 0 ≤ T / 2 := by linarith
  have hhT_nonneg : 0 ≤ h T := h_nonneg T hTpos.le
  have h_interval_le :
      ∫ t in T / 2..T, chafaiDensity f k t ≤ ∫ t in Ioi (T / 2), chafaiDensity f k t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (hint_density.mono_set (Ioi_subset_Ioi hhalf_nonneg))
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
        chafaiDensity_nonneg (lt_of_le_of_lt hhalf_nonneg ht).le
          (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k (lt_of_le_of_lt hhalf_nonneg ht).le))
      (ae_of_all _ fun _ ht => Ioc_subset_Ioi_self ht)
  have hhalf_le :
      (T / 2) ^ k * h T ≤ ↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t := by
    have hfact_pos : (0 : ℝ) < ↑((k - 1).factorial) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hIcc_subset : Icc (T / 2) T ⊆ Ici 0 := fun t ht => le_trans hhalf_nonneg ht.1
    have hmul := mul_le_mul_of_nonneg_left
      ((const_le_intervalIntegral_chafaiDensity f k hk h h_antitone T hTpos.le
        (fun t _ => h_density_eq t)
        ((hcont_density.mono hIcc_subset).intervalIntegrable_of_Icc (by linarith))
        hhT_nonneg).trans h_interval_le) hfact_pos.le
    have hfact_cancel :
        ↑((k - 1).factorial) * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T) =
          (T / 2) ^ k * h T := by field_simp
    rwa [hfact_cancel] at hmul
  calc
    (T - x) ^ k * h T ≤ (2 * T) ^ k * h T := by gcongr
    _ = (4 : ℝ) ^ k * ((T / 2) ^ k * h T) := by
      -- doubling the bound and halving the argument each cost a factor `2 ^ k`
      have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      rw [mul_pow, div_pow, h4]
      field_simp
    _ ≤ (4 : ℝ) ^ k * (↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t) := by gcongr
    _ = ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t := by ring

/-- **The weighted normalized derivative vanishes at infinity.** Let `f` be completely monotone,
let `k` be a nonzero order and let `x` be any real shift. Writing `h T` for the normalized
derivative
`(-1) ^ k * iteratedDerivWithin k f (Ici 0) T`, the products `(T - x) ^ k * h T` tend to `0` as
`T → ∞`. -/
private lemma tendsto_sub_pow_mul_normalized_iteratedDerivWithin (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) (hk : k ≠ 0) (x : ℝ) :
    Tendsto (fun T => (T - x) ^ k * ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T))
      atTop (nhds 0) := by
  -- complete monotonicity already supplies the limit at infinity that integrability needs
  obtain ⟨L, hL, -⟩ :=
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).exists_nonneg_tendsto_atTop
  set h := fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  obtain ⟨h_nonneg₀, h_antitone₀⟩ :=
    normalized_iteratedDerivWithin_nonneg_antitone f hcm k
  have h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T := by simpa [h] using h_nonneg₀
  have h_antitone : AntitoneOn h (Ici 0) := by simpa [h] using h_antitone₀
  have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm k hk1 L hL
  -- `tendsto_integral_Ioi_zero` takes the cut point along any map to `atTop`, so `T / 2` needs
  -- no separate composition argument.
  have htail_half : Tendsto (fun T : ℝ => ∫ t in Ioi (T / 2), chafaiDensity f k t)
      atTop (nhds 0) :=
    tendsto_integral_Ioi_zero (b := fun T : ℝ => T / 2)
      (tendsto_id.atTop_div_const (by norm_num))
  have hupper := density_tail_lower_bound_eventually f hcm k hk x h h_nonneg h_antitone
    (by
      intro t
      rw [chafaiDensity_of_ne_zero hk]
      simp only [h]
      field_simp)
    hint_density
  have hnonneg_event : ∀ᶠ T in atTop, 0 ≤ (T - x) ^ k * h T := by
    filter_upwards [eventually_gt_atTop (max x 0)] with T hT
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right x 0) hT
    have hxT : x < T := lt_of_le_of_lt (le_max_left x 0) hT
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hxT.le) _) (h_nonneg T hT0.le)
  have hupper_tendsto :
      Tendsto (fun T : ℝ =>
        ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t) atTop (nhds 0) := by
    simpa [mul_zero] using htail_half.const_mul (((4 : ℝ) ^ k) * ↑((k - 1).factorial))
  -- squeeze between nonnegativity and the vanishing tail bound
  exact squeeze_zero' hnonneg_event hupper hupper_tendsto

/-- **The shifted order-`k` kernel is dominated by the Chafaï density.** For `0 ≤ x ≤ t` the
kernel built from `(t - x) ^ (k - 1)` is nonnegative and bounded by the density built from
`t ^ (k - 1)`. -/
private lemma norm_ibp_kernel_le_chafaiDensity (f : ℝ → ℝ)
    {k : ℕ} (hk0 : k ≠ 0) {x t : ℝ} (hx : 0 ≤ x) (ht : x ≤ t)
    (hcm_sign : 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) :
    ‖(-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t‖ ≤ chafaiDensity f k t := by
  have htx : 0 ≤ t - x := by linarith
  have htx_le : t - x ≤ t := by linarith
  rw [chafaiDensity_of_ne_zero hk0]
  have hfact : (0 : ℝ) < ↑(k - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hval_nn : 0 ≤ (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t := by
    calc
      (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t
          = (t - x) ^ (k - 1) / ↑(k - 1).factorial *
            ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg htx _) hfact.le) hcm_sign
  rw [Real.norm_eq_abs, abs_of_nonneg hval_nn]
  calc
    (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t
        = (1 / ↑(k - 1).factorial) * (t - x) ^ (k - 1) *
          ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
    _ ≤ (1 / ↑(k - 1).factorial) * t ^ (k - 1) *
        ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htx htx_le _) (by positivity))
            hcm_sign
    _ = (-1 : ℝ) ^ k / ↑(k - 1).factorial * t ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t := by field_simp

private lemma ibp_kernel_integrableOn (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (fun t => (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t) (Ioi x) := by
  have hk0 : k ≠ 0 := by omega
  have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm k hk L hL
  apply Integrable.mono' (hint_density.mono_set (Ioi_subset_Ioi hx))
  · apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi)
    exact ((continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _)).mul
      ((hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top k)
        (uniqueDiffOn_Ici 0)).mono
        (fun t ht => mem_Ici.mpr (lt_of_le_of_lt hx ht).le)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun t ht => norm_ibp_kernel_le_chafaiDensity f hk0 hx (le_of_lt ht)
      (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k (le_trans hx (le_of_lt ht)))

/-- Raising the sign exponent of the order-`k` kernel by one negates its integral. -/
private lemma intervalIntegral_neg_one_pow_succ_kernel (f : ℝ → ℝ) (k : ℕ) (x T : ℝ) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t =
      -(∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t) := by
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => ?_)
  rw [pow_succ (-1 : ℝ) k]
  ring

/-- For a completely monotone `f` with limit `L` at infinity, `0 ≤ x` and `k ≠ 0`, the order-`k`
kernel identity implies the order-`k + 1` one: if the order-`k` kernel integrates against the
`k`-th derivative to `f x - L` on `(x, ∞)`, then so does the order-`k + 1` kernel against the
`(k + 1)`-st derivative. -/
private lemma chafai_repeated_ibp_succ (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L))
    (ih : ∫ t in Ioi x, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t = f x - L) :
    ∫ t in Ioi x, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t = f x - L := by
  -- Integrate by parts on `[x, T]`; the boundary term decays, so `T → ∞` transfers `ih`.
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hintk := ibp_kernel_integrableOn f hcm k hk1 x hx L hL
  have hintkp1 := ibp_kernel_integrableOn f hcm (k + 1) (by omega) x hx L hL
  simp only [show k + 1 - 1 = k by omega] at hintkp1
  have htend_k : Tendsto (fun T => ∫ t in x..T,
      (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
    rw [← ih]
    exact intervalIntegral_tendsto_integral_Ioi x hintk tendsto_id
  have htend_sum : Tendsto (fun T =>
      (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
        iteratedDerivWithin k f (Ici 0) T +
      ∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
    have hbdry : Tendsto (fun T => (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
        iteratedDerivWithin k f (Ici 0) T) atTop (nhds 0) := by
      have heq : ∀ T, -(1 / (k.factorial : ℝ)) *
          ((T - x) ^ k * ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T)) =
          (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
            iteratedDerivWithin k f (Ici 0) T := fun T => by
        simp only [pow_succ]
        ring
      simpa using
        (((tendsto_sub_pow_mul_normalized_iteratedDerivWithin f hcm k hk x).const_mul
          (-(1 / (k.factorial : ℝ)))).congr heq)
    simpa [zero_add] using hbdry.add htend_k
  have htend_via_ibp : Tendsto (fun T => ∫ t in x..T,
      (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t) atTop (nhds (f x - L)) :=
    Tendsto.congr' ((eventually_gt_atTop x).mono fun T hxT => by
      have := ibp_finite_interval f hcm k hk x T hx hxT
      linarith [intervalIntegral_neg_one_pow_succ_kernel f k x T]) htend_sum
  exact tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral_Ioi x hintkp1 tendsto_id).congr
      (fun T => by simp [id])) htend_via_ibp

/-- **Repeated integration by parts for a completely monotone function.** For `n ≥ 1`, `0 ≤ x`
and `f` tending to `L` at infinity, integrating the order-`n` kernel
`(-1) ^ n / (n - 1)! * (t - x) ^ (n - 1)` against the `n`-th derivative of `f` over `(x, ∞)`
recovers `f x - L`. This is the analytic identity behind the Chafaï reconstruction of `f` from
its derivatives. -/
private lemma chafai_repeated_ibp (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) *
      iteratedDerivWithin n f (Ici 0) t = f x - L := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      simpa using hcm.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg hx hL
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      simp only [show k + 1 - 1 = k by omega]
      exact chafai_repeated_ibp_succ f hcm k hk x hx L hL (ih hk1)

/-- **Chafaï reconstruction identity** for the nonconstant part. -/
lemma chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop
    (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    ∫ p, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) = f x - L := by
  have h_integral_pullback :
      ∫ p : ℝ≥0, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) =
        ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) := by
    exact chafaiRescaled_integral f n
      ((measurable_bernsteinKernel n x).comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
        |>.aestronglyMeasurable)
  have h_integral_density :
      ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) =
        ∫ t in Ioi 0,
          bernsteinKernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t := by
    rw [chafaiMeasure_eq_withDensity]
    have hcont_density : ContinuousOn (chafaiDensity f n) (Ici 0) :=
      continuousOn_chafaiDensity (n := n) (hcm.contDiffOn.of_le (nat_le_top n))
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (AEMeasurable.ennreal_ofReal
        ((hcont_density.mono Ioi_subset_Ici_self).aestronglyMeasurable
          measurableSet_Ioi |>.aemeasurable))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact setIntegral_congr_ae measurableSet_Ioi
      (ae_of_all _ fun t ht => by
        simp only [smul_eq_mul, mem_Ioi] at ht ⊢
        rw [chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht]
        rw [ENNReal.toReal_ofReal
          (chafaiDensity_nonneg ht.le
            (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le))]
        ring)
  have hkernel := chafai_kernel_density_eq f n hn x hx
  have hibp := chafai_repeated_ibp f hcm n (by omega) x hx L hL
  rw [h_integral_pullback, h_integral_density, hkernel]
  exact hibp

private lemma bernsteinKernel_le_exp {n : ℕ} (hn : 2 ≤ n) {x p : ℝ} (_hx : 0 ≤ x) (_hp : 0 ≤ p) :
    bernsteinKernel n x p ≤ Real.exp (-(x * p)) := by
  rw [bernsteinKernel_of_two_le hn]
  by_cases h : 1 - x * p / ↑(n - 1) ≤ 0
  · rw [max_eq_right h]
    rw [zero_pow (by omega : n - 1 ≠ 0)]
    exact le_of_lt (Real.exp_pos _)
  · push Not at h
    rw [max_eq_left h.le]
    have hden_pos : (0 : ℝ) < ↑(n - 1) := Nat.cast_pos.mpr (by omega)
    have hle : 1 - x * p / ↑(n - 1) ≤ Real.exp (-(x * p / ↑(n - 1))) := by
      linarith [Real.add_one_le_exp (-(x * p / ↑(n - 1)))]
    calc
      (1 - x * p / ↑(n - 1)) ^ (n - 1)
          ≤ (Real.exp (-(x * p / ↑(n - 1)))) ^ (n - 1) :=
            pow_le_pow_left₀ h.le hle _
      _ = Real.exp (↑(n - 1) * -(x * p / ↑(n - 1))) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (-(x * p)) := by
            congr 1
            field_simp [hden_pos.ne']

/-- **Local error bound for the Bernstein truncation.** For `0 ≤ u < 1` and `m : ℕ`, the
difference `exp (-(m·u)) - (1 - u) ^ m` is bounded above by the second-order term
`m·u² / (1 - u)`. This is the pointwise estimate driving the uniform convergence of the
Bernstein kernel to the Laplace kernel. -/
private lemma exp_neg_mul_sub_one_sub_pow_le (u : ℝ) (hu_nn : 0 ≤ u) (hu_lt_1 : u < 1) (m : ℕ) :
    Real.exp (-(↑m * u)) - (1 - u) ^ m ≤ ↑m * u ^ 2 / (1 - u) := by
  have h1u : 0 < 1 - u := by linarith
  -- The logarithmic lower bound converts the power into an exponential with a Taylor-tail term.
  have hpow_ge : (1 - u) ^ m ≥ Real.exp (-(↑m * u) - ↑m * u ^ 2 / (1 - u)) := by
    have heq : (1 - u) ^ m = Real.exp (↑m * Real.log (1 - u)) := by
      rw [← Real.rpow_natCast (1 - u) m, Real.rpow_def_of_pos h1u, mul_comm]
    rw [heq]
    gcongr
    have hfactor : -(↑m * u) - ↑m * u ^ 2 / (1 - u) = ↑m * (-u - u ^ 2 / (1 - u)) := by ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    have habs : |u| < 1 := by rwa [abs_of_nonneg hu_nn]
    have hlog := Real.abs_log_sub_add_sum_range_le habs 1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one] at hlog
    have hu_sq : u ^ (1 + 1) = u ^ 2 := by ring
    rw [abs_of_nonneg hu_nn, hu_sq] at hlog
    linarith [(abs_le.mp hlog).1]
  set b := ↑m * u ^ 2 / (1 - u) with hb_def
  have hb_nn : 0 ≤ b := div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)) h1u.le
  have hmu_nn : 0 ≤ ↑m * u := mul_nonneg (Nat.cast_nonneg m) hu_nn
  -- `exp` sits above its tangent line at `0`, so the exponential gap is at most `b`.
  suffices h : Real.exp (-(↑m * u)) - Real.exp (-(↑m * u) - b) ≤ b by linarith
  have hsplit : Real.exp (-(↑m * u) - b) = Real.exp (-(↑m * u)) * Real.exp (-b) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit]
  nlinarith [Real.exp_pos (-(↑m * u)), Real.exp_pos (-b),
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmu_nn), Real.add_one_le_exp (-b)]

/-- **Compact-support tail estimate.** Once `M` exceeds `C + 2C²/ε`, the error parameter
`xp² / (M - xp)` stays below `ε / 2` for every `0 ≤ xp ≤ C`. Positivity of `M - C` follows
from the size hypothesis, so the only inputs are the pointwise bounds on `xp`. -/
private lemma sq_div_sub_lt_div_two (xp C ε M : ℝ) (hxp_nn : 0 ≤ xp) (hxp_le_C : xp ≤ C)
    (hε : 0 < ε) (hM : 2 * C ^ 2 / ε < M - C) :
    xp ^ 2 / (M - xp) < ε / 2 := by
  have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
  have hMC_pos : 0 < M - C := by linarith
  -- Monotone in the numerator and the denominator: `xp²/(M-xp) ≤ C²/(M-C)`.
  have hmono : xp ^ 2 / (M - xp) ≤ C ^ 2 / (M - C) :=
    div_le_div₀ (sq_nonneg C) (sq_le_sq' (by linarith) hxp_le_C) hMC_pos (by linarith)
  -- The size hypothesis on `M` forces `C²/(M-C) < ε/2`.
  have hsmall : C ^ 2 / (M - C) < ε / 2 := by
    rw [div_lt_div_iff₀ hMC_pos (by positivity : (0 : ℝ) < 2)]
    have h2 : ε * (M - C) > ε * (2 * C ^ 2 / ε) := mul_lt_mul_of_pos_left hM hε
    rw [mul_div_cancel₀ _ (ne_of_gt hε)] at h2
    linarith
  linarith

private lemma kernel_uniform_conv_compact (x R ε : ℝ) (hx : 0 < x) (hR : 0 < R) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p → p ≤ R →
      |bernsteinKernel n x p - Real.exp (-(x * p))| < ε := by
  set C := x * R
  have hC_pos : 0 < C := mul_pos hx hR
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C + 2 + 2 * C ^ 2 / ε)
  refine ⟨N₀, fun n hn p hp hpR => ?_⟩
  have hn_gt : (↑n : ℝ) > C + 2 + 2 * C ^ 2 / ε := lt_of_lt_of_le hN₀ (Nat.cast_le.mpr hn)
  have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
  have hn_ge2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) < ↑n by linarith [hC_pos]).le
  have hle := bernsteinKernel_le_exp hn_ge2 hx.le hp
  rw [abs_of_nonpos (by linarith), neg_sub]
  set m := n - 1
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
  have hm_eq : (↑m : ℝ) = ↑n - 1 := by rw [Nat.cast_sub (show 1 ≤ n by omega)]; simp
  have hxp_nn : 0 ≤ x * p := mul_nonneg hx.le hp
  have hxp_le_C : x * p ≤ C := mul_le_mul_of_nonneg_left hpR hx.le
  set u := x * p / ↑m with hu_def
  have hu_nn : 0 ≤ u := div_nonneg hxp_nn hm_pos.le
  have hu_lt_1 : u < 1 := by rw [div_lt_one hm_pos]; linarith [hm_eq]
  have hkernel_eq : bernsteinKernel n x p = (1 - u) ^ m := by
    rw [bernsteinKernel_of_two_le hn_ge2]
    congr 1
    exact max_eq_left (by
      -- `max_eq_left` needs the truncated factor `1 - x*p/m` nonneg; expose it as the defeq goal.
      change 0 ≤ 1 - x * p / (↑m : ℝ)
      rw [← hu_def]; linarith)
  rw [hkernel_eq]
  set b := ↑m * u ^ 2 / (1 - u) with hb_def
  have hmu : ↑m * u = x * p := by simp only [hu_def]; field_simp [hm_pos.ne']
  -- Assemble the two phase estimates: the local error is `≤ b`, and `b < ε/2` on `p ≤ R`.
  have hstep : Real.exp (-(x * p)) - (1 - u) ^ m ≤ b := by
    rw [hb_def, ← hmu]
    exact exp_neg_mul_sub_one_sub_pow_le u hu_nn hu_lt_1 m
  have hb_eq : b = (x * p) ^ 2 / (↑m - x * p) := by
    simp only [hb_def, hu_def]
    field_simp [hm_pos.ne']
  have hb_small : b < ε / 2 := by
    rw [hb_eq]
    exact sq_div_sub_lt_div_two (x * p) C ε ↑m hxp_nn hxp_le_C hε (by linarith [hm_eq])
  linarith

private lemma kernel_uniform_conv (x : ℝ) (hx : 0 < x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p →
      |bernsteinKernel n x p - Real.exp (-(x * p))| < ε := by
  have htail : Tendsto (fun R => Real.exp (-(x * R))) atTop (nhds 0) := by
    apply Tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    exact tendsto_id.const_mul_atTop hx
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (half_pos hε)
  set R := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
  have hR_tail : Real.exp (-(x * R)) < ε / 2 := by
    have h1 := hR₀ R (le_max_left _ _)
    rwa [dist_zero_right, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  obtain ⟨N₁, hN₁⟩ := kernel_uniform_conv_compact x R (ε / 2) hx hR_pos (half_pos hε)
  refine ⟨max N₁ 2, fun n hn p hp => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right N₁ 2) hn
  by_cases hpR : p ≤ R
  · linarith [hN₁ n (le_trans (le_max_left _ _) hn) p hp hpR]
  · push Not at hpR
    have h1 := bernsteinKernel_le_exp hn2 hx.le hp
    rw [abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-(x * p)) ≤ Real.exp (-(x * R)) := by
      apply Real.exp_le_exp_of_le
      linarith [mul_le_mul_of_nonneg_left (le_of_lt hpR) hx.le]
    linarith [bernsteinKernel_nonneg n x p]

/-- Bernstein-to-Laplace replacement against a uniformly finite sequence of measures. -/
lemma integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound (σ : ℕ → Measure ℝ≥0)
    (hmass : ∀ᶠ n in atTop, (σ n) univ ≤ ENNReal.ofReal C) (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p : ℝ≥0,
        (bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))) ∂(σ n))
      atTop (nhds 0) := by
  by_cases hx0 : x = 0
  · subst hx0
    suffices h : ∀ᶠ n in atTop, ∫ p : ℝ≥0,
        (bernsteinKernel n 0 (p : ℝ) - Real.exp (-(0 * (p : ℝ)))) ∂(σ n) = 0 by
      exact Tendsto.congr' (EventuallyEq.symm h) tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply integral_eq_zero_of_ae
    apply ae_of_all
    intro p
    -- At `x = 0` the integrand is defeq to this explicit difference; expose it before rewriting.
    change bernsteinKernel n 0 (p : ℝ) - Real.exp (-(0 * (p : ℝ))) = 0
    rw [bernsteinKernel_of_two_le hn]
    simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hmax_pos : 0 < max C 1 := lt_max_of_lt_right one_pos
    obtain ⟨N, hN⟩ := kernel_uniform_conv x hx_pos
      (ε / (2 * max C 1)) (div_pos hε (by positivity))
    refine eventually_atTop.1 <| ((eventually_ge_atTop N).and hmass).mono fun n hn => ?_
    rcases hn with ⟨hn, hmass_n⟩
    rw [dist_zero_right]
    have : IsFiniteMeasure (σ n) := ⟨hmass_n.trans_lt ENNReal.ofReal_lt_top⟩
    calc
      ‖∫ p : ℝ≥0, (bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))) ∂(σ n)‖
          ≤ ∫ p : ℝ≥0,
              ‖bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))‖ ∂(σ n) :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ _ : ℝ≥0, (ε / (2 * max C 1)) ∂(σ n) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
          exact ae_of_all _ fun p => by
            simpa [Real.norm_eq_abs] using le_of_lt (hN n hn (p : ℝ) p.2)
      _ = ε / (2 * max C 1) * ((σ n) univ).toReal := by
          simp [MeasureTheory.integral_const, smul_eq_mul, Measure.real, mul_comm]
      _ ≤ ε / (2 * max C 1) * max C 1 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos hε (by positivity)))
          exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hmax_pos)
            (le_trans hmass_n (ENNReal.ofReal_le_ofReal (le_max_left C 1)))
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε

/-- Weak convergence of the rescaled Chafaï measures specializes to the Laplace kernel:
if all bounded-continuous test integrals for `chafaiRescaled f n` converge to those for `μ₀`,
then the integrals of `p ↦ exp (-x * p)` converge for every `x ≥ 0`. -/
lemma chafaiRescaled_tendsto_laplace_integral_of_weak {μ₀ : Measure ℝ≥0} {l : Filter ℕ}
    (hweak : ∀ g : BoundedContinuousFunction ℝ≥0 ℝ,
        Tendsto (fun n => ∫ p, g p ∂(chafaiRescaled f n)) l
          (nhds (∫ p, g p ∂μ₀)))
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p, Real.exp (-(x * (p : ℝ))) ∂(chafaiRescaled f n)) l
      (nhds (∫ p, Real.exp (-(x * (p : ℝ))) ∂μ₀)) := by
  simpa using hweak (laplaceKernelBoundedContinuous hx)

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.Tightness -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/






/-!
# Tightness of the Chafaï approximating measures

This file proves the tightness input for the Prokhorov extraction step in Bernstein's theorem.
For a completely monotone function `f`, the rescaled Chafaï measures have uniformly bounded
first moment:

`∫⁻ p, p ∂(chafaiRescaled f n) ≤ -f'(0)`.

Markov's inequality therefore bounds their mass outside `[0, R]` by `-f'(0) / R`, uniformly in
`n`. Since the intervals `[0, R]` are compact in `ℝ≥0`, this proves that the whole family is
tight.

## Main declarations

* `TauCeti.chafaiRescaled_measure_Ioi_le`: the uniform first-moment tail bound.
* `TauCeti.isTightMeasureSet_range_chafaiRescaled`: the rescaled Chafaï measures form a tight
  family.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B, Bernstein's theorem
  milestone (“measure extraction via Prokhorov tightness”).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Ch. 1.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/


open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- The rescaled Chafaï measures satisfy the uniform Markov tail estimate

`chafaiRescaled f n (R, ∞) ≤ ofReal (-f'(0)) / R`

for every positive `R`. The derivative is taken within `[0, ∞)`, as in the definition of
complete monotonicity. -/
lemma chafaiRescaled_measure_Ioi_le (hcm : IsCompletelyMonotone f) (n : ℕ) {R : ℝ≥0} (hR : R ≠ 0) :
    chafaiRescaled f n (Ioi R) ≤
      ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) := by
  let μ := chafaiRescaled f n
  let moment : ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (p : ℝ)
  have hmoment_meas : AEMeasurable moment μ :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ)))
      |>.aemeasurable
  have hsubset : Ioi R ⊆ {p | (R : ℝ≥0∞) ≤ moment p} := by
    intro p hp
    simpa [moment, ENNReal.ofReal_coe_nnreal] using hp.le
  calc
    μ (Ioi R) ≤ μ {p | (R : ℝ≥0∞) ≤ moment p} := measure_mono hsubset
    _ ≤ (∫⁻ p, moment p ∂μ) / (R : ℝ≥0∞) :=
      meas_ge_le_lintegral_div hmoment_meas (by simpa using hR) (by simp)
    _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) :=
      ENNReal.div_le_div_right (chafaiRescaled_lintegral_coe_le f hcm n) _

/-- The family of all rescaled Chafaï approximating measures of a completely monotone function
is tight. Equivalently, for every positive error tolerance there is a compact interval
`[0, R] ⊆ ℝ≥0` whose complement has at most that much mass for every approximation order. -/
theorem isTightMeasureSet_range_chafaiRescaled (hcm : IsCompletelyMonotone f) :
    IsTightMeasureSet (range (chafaiRescaled f)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ∞
  · refine ⟨∅, isCompact_empty, fun μ _ => ?_⟩
    simp [hε_top]
  let D : ℝ≥0 := ⟨-derivWithin f (Ici 0) 0,
    neg_nonneg.mpr (hcm.derivWithin_nonpos le_rfl)⟩
  let R : ℝ≥0 := D / ε.toNNReal + 1
  have hR : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_self))
  have hcompact : IsCompact (Iic R) := by
    have hset : Iic R = Icc (0 : ℝ≥0) R := by
      ext p
      simp
    rw [hset]
    exact isCompact_Icc
  refine ⟨Iic R, hcompact, ?_⟩
  intro μ hμ
  obtain ⟨n, rfl⟩ := hμ
  rw [compl_Iic]
  refine (chafaiRescaled_measure_Ioi_le hcm n hR).trans ?_
  have hD : ENNReal.ofReal (-derivWithin f (Ici 0) 0) = (D : ℝ≥0∞) := by
    exact (ENNReal.coe_nnreal_eq D).symm
  rw [hD]
  have hR_gt : D / ε.toNNReal < R := lt_add_one _
  have hε_toNNReal : ε.toNNReal ≠ 0 :=
    ENNReal.toNNReal_ne_zero.mpr ⟨hε.ne', hε_top⟩
  have hR_gt' : (D : ℝ≥0∞) / (ε.toNNReal : ℝ≥0∞) < (R : ℝ≥0∞) := by
    rw [← ENNReal.coe_div hε_toNNReal]
    exact_mod_cast hR_gt
  rw [ENNReal.coe_toNNReal hε_top] at hR_gt'
  exact (ENNReal.div_le_iff (by simpa using hR) (by simp)).2
    ((ENNReal.div_le_iff' hε.ne' hε_top).1 hR_gt'.le)

end TauCeti
end

/- TauCeti.MeasureTheory.Measure.Prokhorov -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# Weak cluster limits of tight finite measures

This file contains a generic finite-measure extraction lemma based on Mathlib's Prokhorov
compactness theorem for finite measures. It has no real-line support condition and no
normalization step: tightness and a uniform mass bound place the sequence in a compact set of
`FiniteMeasure`s, and compactness gives a weak cluster limit.

## Main declarations

* `TauCeti.finite_measure_cluster_limit`: a tight, mass-bounded sequence of finite measures has a
  weak cluster limit along an ultrafilter below `atTop`.
* `TauCeti.finite_measure_subseq_limit`: the corresponding subsequence form when the weak topology
  on `FiniteMeasure α` is first-countable.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
-/


open MeasureTheory Set Filter Topology
open scoped NNReal Topology

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [T2Space α] [BorelSpace α]

omit [T2Space α] [BorelSpace α] in
/-- A tight family of measures admits a **monotone** exhaustion by compact sets whose complements
carry uniformly small mass: given tolerances `u j > 0`, there are compact `K j`, increasing in `j`,
with `σ n (K j)ᶜ ≤ u j` for every `n`. Accumulating the sets supplied by tightness is what turns
the unrelated compact sets into the monotone family Mathlib's Prokhorov criterion expects. -/
private lemma exists_monotone_isCompact_measure_compl_le
    {σ : ℕ → Measure α} (hTight : IsTightMeasureSet (Set.range σ))
    {u : ℕ → ℝ≥0} (hu_pos : ∀ j, 0 < u j) :
    ∃ K : ℕ → Set α, Monotone K ∧ (∀ j, IsCompact (K j)) ∧
      ∀ j n, (σ n) (K j)ᶜ ≤ (u j : ENNReal) := by
  have hchoose : ∀ j, ∃ K : Set α, IsCompact K ∧ ∀ n, (σ n) Kᶜ ≤ (u j : ENNReal) := by
    intro j
    obtain ⟨K, hK, htail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight
        (u j : ENNReal) (by exact_mod_cast hu_pos j)
    exact ⟨K, hK, fun n => htail (σ n) (Set.mem_range_self n)⟩
  choose K hK_comp hK_tail using hchoose
  refine ⟨Set.accumulate K, Set.monotone_accumulate,
    fun j => isCompact_accumulate hK_comp j, fun j n => ?_⟩
  exact (measure_mono (compl_subset_compl.mpr (Set.subset_accumulate (s := K) (x := j)))).trans
    (hK_tail j n)

/-- A tight, uniformly mass-bounded sequence of finite measures has a weak cluster limit.

Given tightness of the sequence and a common total-mass bound, the conclusion is a finite limiting
measure with the same mass bound and weak convergence of all bounded-continuous test-function
integrals along an ultrafilter `U ≤ atTop`; no first-countability assumption on `FiniteMeasure α`
is needed. -/
lemma finite_measure_cluster_limit (σ : ℕ → Measure α) (C : ℝ≥0)
    (hmass : ∀ n, (σ n) univ ≤ (C : ENNReal)) (hTight : IsTightMeasureSet (Set.range σ)) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop ∧ IsFiniteMeasure μ₀ ∧
      μ₀ univ ≤ (C : ENNReal) ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun n => ∫ x, g x ∂(σ n)) (U : Filter ℕ)
          (nhds (∫ x, g x ∂μ₀)) := by
  -- First coerce the sequence to `FiniteMeasure`; the uniform mass bound supplies finiteness.
  have hfin : ∀ n, IsFiniteMeasure (σ n) := fun n =>
    ⟨(hmass n).trans_lt ENNReal.coe_lt_top⟩
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  -- Choose a positive sequence decreasing to zero; these values are the tail tolerances in
  -- Prokhorov's compact set criterion.
  obtain ⟨u, -, hu_pos, hu_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  obtain ⟨K, hKmono, hK_comp, hK_tail⟩ :=
    exists_monotone_isCompact_measure_compl_le hTight hu_pos
  let S : Set (FiniteMeasure α) := {μ | μ.mass ≤ C ∧ ∀ j, μ (K j)ᶜ ≤ u j}
  have hcompact : IsCompact S := by
    simpa [S] using
      isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
        (E := α) (C := C) (u := u) (K := K) hu_lim hK_comp (Or.inr hKmono)
  -- The finite-measure sequence lies in the compact Prokhorov set.
  have hσ_mem : ∀ n, σf n ∈ S := by
    refine fun n => ⟨?_, fun j => ?_⟩
    · dsimp [σf, S, FiniteMeasure.mass]
      exact ENNReal.coe_le_coe.mp (by simpa using hmass n)
    · exact ENNReal.coe_le_coe.mp (by simpa [σf] using hK_tail j n)
  -- Compactness gives a cluster point and an ultrafilter below `atTop` along which `σf`
  -- converges weakly.
  have hmap_le : map σf atTop ≤ 𝓟 S :=
    tendsto_principal.mpr (Eventually.of_forall hσ_mem)
  obtain ⟨μf, hμfS, hcluster⟩ := hcompact hmap_le
  have hmapcluster : MapClusterPt μf atTop σf := hcluster
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hmapcluster
  refine ⟨(μf : Measure α), U, hUle, inferInstance, ?_, ?_⟩
  -- Finally unwrap the compact-set membership into the mass bound and weak convergence of
  -- integrals against bounded continuous test functions.
  · have hle : (μf.mass : ENNReal) ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr hμfS.1
    rw [← FiniteMeasure.ennreal_mass]
    simpa using hle
  · intro g
    have hweak :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend) g
    simpa [σf] using hweak

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


-- Non-public: the Chafaï approximating measures, their tightness, and the Prokhorov extraction are
-- used only inside the proof; the statement mentions none of them.



/-!
# Bernstein's theorem: existence of a representing measure

A completely monotone function on `[0, ∞)` is the Laplace transform of a finite positive measure
on `ℝ≥0`.

## Main results

* `TauCeti.exists_representsLaplace_of_isCompletelyMonotone`

## Scope

This is the **existence** half of the Bernstein milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B. Uniqueness of the representing measure
is `TauCeti.RepresentsLaplace.unique`, the converse direction is
`TauCeti.isCompletelyMonotoneOnIci_laplaceTransform`, and all three combine in
`Bernstein/HausdorffBernsteinWidder.lean` as `TauCeti.hausdorff_bernstein_widder` and
`TauCeti.hausdorff_bernstein_widder_existsUnique`.

Finiteness of the representing measure is not an extra hypothesis but a consequence of complete
monotonicity on the *closed* half-line: `IsCompletelyMonotone` builds in `Set.Ici 0`, so `f` takes a
real value at `0`, and the representing measure has total mass `f 0`. On the open half-line alone
the value at `0` need not exist and the representing measure can be infinite — `1/t` is completely
monotone on `(0, ∞)` with representing measure Lebesgue.

## Implementation

`Bernstein/Measures.lean` supplies the Chafaï approximating measures `chafaiRescaled f n` on `ℝ≥0`
and the reconstruction identity `f x - L = ∫ bernsteinKernel n x ∂(chafaiRescaled f n)`, where
`L = lim_{t→∞} f t`. Those measures are uniformly mass-bounded and, by `Bernstein/Tightness.lean`,
tight. The three remaining steps are:

1. extract a weak limit `μ₀` from tightness;
2. pass the reconstruction identity to that limit, replacing the Bernstein kernel by `e^{-xp}`,
   which represents the non-constant part `f - L`;
3. add the atom `L • δ₀`, whose Laplace transform is the constant `L`, to represent `f` itself.

Step 1 uses `finite_measure_cluster_limit` rather than its subsequence form
`finite_measure_subseq_limit`: the latter needs `FirstCountableTopology (FiniteMeasure ℝ≥0)`, and
Mathlib's metrizability instances for spaces of measures are stated for `ProbabilityMeasure`, not
`FiniteMeasure`. No subsequence is actually required — every ingredient is a filter limit, so an
ultrafilter below `atTop` suffices, and being `NeBot` it still gives uniqueness of limits.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013) — the approximating measures this proof
  passes to the limit.
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/


open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **The weak limit represents the non-constant part.** Along the ultrafilter `U`, the Chafaï
measures converge weakly to `μ₀`; passing the reconstruction identity to that limit replaces the
Bernstein kernel by `e^{-tp}` and exhibits `μ₀` as a representing measure for `f - L`, where `L` is
the limit of `f` at infinity. The atom carrying `L` itself is added by the caller.

Stated pointwise in `t`, which is how the caller consumes it. -/
private theorem sub_eq_integral_exp_neg_mul_of_weak_limit {L : ℝ} {C : ℝ≥0} {μ₀ : Measure ℝ≥0}
    {U : Ultrafilter ℕ} (hcm : IsCompletelyMonotone f) (hL : Tendsto f atTop (nhds L))
    (hmass' : ∀ᶠ n in atTop, (chafaiRescaled f n) univ ≤ (C : ℝ≥0∞)) (hU : (U : Filter ℕ) ≤ atTop)
    (hweak : ∀ g : BoundedContinuousFunction ℝ≥0 ℝ,
      Tendsto (fun n => ∫ x, g x ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds (∫ x, g x ∂μ₀)))
    {t : ℝ} (ht : 0 ≤ t) :
    f t - L = ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ₀ := by
  have : (U : Filter ℕ).NeBot := U.neBot'
  have hlap : Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
      (U : Filter ℕ) (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀)) :=
    chafaiRescaled_tendsto_laplace_integral_of_weak hweak ht
  have herr : Tendsto (fun n => ∫ p : ℝ≥0,
      (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
        ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) :=
    (integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound
      (C := (C : ℝ)) (chafaiRescaled f)
      (hmass'.mono fun n hn => hn.trans
        (by simp [ENNReal.ofReal_coe_nnreal])) t ht).mono_left hU
  -- the mass bound makes the Chafaï measures eventually finite along `U`
  have hfin : ∀ᶠ n in (U : Filter ℕ), IsFiniteMeasure (chafaiRescaled f n) :=
    Filter.Eventually.mono (hU hmass') fun n hn => ⟨hn.trans_lt ENNReal.coe_lt_top⟩
  have hsplit : ∀ᶠ n in (U : Filter ℕ), ∫ p : ℝ≥0,
      (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ)))) ∂(chafaiRescaled f n)
        = (∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n))
          - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n) := by
    filter_upwards [hfin] with n hn
    exact integral_sub (integrable_bernsteinKernel (chafaiRescaled f n) n ht)
      (integrable_exp_neg_mul (chafaiRescaled f n) ht)
  -- The Bernstein integral is constantly `f t - L` once `n ≥ 2`.
  have hconst : ∀ᶠ n in (U : Filter ℕ),
      ∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n) = f t - L := by
    have h2 : ∀ᶠ n in (U : Filter ℕ), 2 ≤ n := hU (eventually_ge_atTop 2)
    filter_upwards [h2] with n hn
    exact chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop f hcm n hn t ht L hL
  -- Pass to the limit: `(f t - L) - ∫ laplace → 0`.
  have hdiff : Tendsto (fun n => (f t - L)
      - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) := by
    refine herr.congr' ?_
    filter_upwards [hconst, hsplit] with n hn hs
    rw [hs, hn]
  have hlim := hdiff.add hlap
  simp only [sub_add_cancel, zero_add] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- **Bernstein's theorem, existence half.** A completely monotone function on `[0, ∞)` is the
Laplace transform of a finite positive measure on `ℝ≥0`.

Uniqueness of that measure is not asserted here; it is `TauCeti.RepresentsLaplace.unique`, and
the two combine in the Hausdorff--Bernstein--Widder theorem. -/
theorem exists_representsLaplace_of_isCompletelyMonotone
    (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  obtain ⟨L, C, hL, hL_nn, -, hmass⟩ := chafaiRescaled_prokhorov_mass_bound f hcm
  have hmass' : ∀ n, (chafaiRescaled f n) univ ≤ (C : ℝ≥0∞) := fun n => (hmass n).2
  obtain ⟨μ₀, U, hU, hμ₀fin, -, hweak⟩ :=
    finite_measure_cluster_limit (chafaiRescaled f) C hmass'
      (isTightMeasureSet_range_chafaiRescaled hcm)
  -- The limit represents the non-constant part `f - L`.
  have key : ∀ t : ℝ, 0 ≤ t → f t - L = ∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀ :=
    fun t ht => sub_eq_integral_exp_neg_mul_of_weak_limit hcm hL (.of_forall hmass') hU hweak ht
  -- Add the atom `L · δ₀` to recover `f` itself.
  have := hμ₀fin
  refine ⟨μ₀ + L.toNNReal • Measure.dirac 0,
    representsLaplace_iff.mpr ⟨inferInstance, fun t ht => ?_⟩⟩
  rw [laplaceTransform_apply,
    integral_exp_neg_mul_add_smul_dirac_zero μ₀ _ ht, Real.coe_toNNReal L hL_nn]
  linarith [key t ht]

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


-- Non-public: the metrizability class of the finite-set tightness lemmas.

-- Non-public: Bernstein's existence theorem supplies the representing measures of the shifts.

-- Non-public: `finite_measure_cluster_limit` extracts the weak cluster point.


/-!
# Hausdorff--Bernstein--Widder theorem

This file proves the finite-measure form of the Hausdorff--Bernstein--Widder theorem for
completely monotone functions on the closed half-line: a function is continuous on `[0, ∞)`
and completely monotone on `(0, ∞)` if and only if it is the Laplace transform of a (unique)
finite positive measure on `ℝ≥0`.

The hard direction applies Bernstein's existence theorem
(`TauCeti.exists_representsLaplace_of_isCompletelyMonotone`) to the
positive shifts `t ↦ f (t + a)`, which satisfy the strong `IsCompletelyMonotone` predicate,
and passes to a weak cluster point of the representing measures as `a ↓ 0`; the tightness of
that family is an elementary Laplace-kernel tail estimate. The easy direction and the
uniqueness both live in `Laplace/Representation.lean`.

## Main declarations

* `TauCeti.exists_representsLaplace_of_isCompletelyMonotoneOnIci`
* `TauCeti.hausdorff_bernstein_widder`, `TauCeti.hausdorff_bernstein_widder_existsUnique`

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/


open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-! ## Hard direction: tightness of the shifted representing measures -/

/-- A finite set of finite measures is tight: singletons are tight and tightness is closed
under unions. (The empty case routes through an arbitrary singleton, as Mathlib has no
dedicated empty-set tightness lemma.) -/
private lemma isTightMeasureSet_of_finite {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
    [BorelSpace α] {S : Set (Measure α)} (hS : S.Finite)
    (hfin : ∀ ν ∈ S, IsFiniteMeasure ν) : IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact (isTightMeasureSet_singleton (μ := (0 : Measure α))).subset (empty_subset _)
  | @insert ν S _ _ ih =>
      have : IsFiniteMeasure ν := hfin ν (mem_insert _ _)
      rw [insert_eq]
      exact isTightMeasureSet_singleton.union (ih fun ρ hρ => hfin ρ (mem_insert_of_mem _ hρ))

/-- A finite family of finite measures is tight. -/
private lemma isTightMeasureSet_range_finite
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
    [BorelSpace α] [Finite ι] (μ : ι → Measure α)
    (hfin : ∀ i, IsFiniteMeasure (μ i)) :
    IsTightMeasureSet (Set.range μ) :=
  isTightMeasureSet_of_finite (finite_range μ) (by rintro ν ⟨i, rfl⟩; exact hfin i)

/-- Along a positive null sequence `aₙ ↓ 0`, the values `f (c + aₙ)` of a function continuous
within `[0, ∞)` converge to `f c`, for any `c ≥ 0`. -/
private lemma tendsto_apply_add_of_continuousOn
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {c : ℝ} (hc : 0 ≤ c)
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => f (c + a n)) atTop (𝓝 (f c)) := by
  have hmem : Tendsto (fun n => c + a n) atTop (𝓝[Ici (0 : ℝ)] c) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using tendsto_const_nhds.add ha,
        .of_forall fun n => mem_Ici.mpr (add_nonneg hc (ha_pos n).le)⟩
  exact (hf.continuousWithinAt (mem_Ici.mpr hc)).tendsto.comp hmem

/-- The Markov denominator `1 - e^{-xR}` is positive for `x, R > 0`. -/
private lemma one_sub_exp_neg_mul_pos {x R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    0 < 1 - Real.exp (-(x * R)) := by
  have : Real.exp (-(x * R)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

/-- The `∫⁻` of the bounded coordinate `p ↦ 1 - exp(-x·p)` against a measure that represents
`t ↦ f (t + δ)` by its Laplace transform equals `f δ - f (x + δ)` (for `x > 0`). This is the
Laplace-value identity behind the shifted-measure tail estimate. -/
private lemma lintegral_ofReal_one_sub_exp_eq_of_representsLaplace
    {f : ℝ → ℝ} {μ : Measure ℝ≥0}
    {δ x : ℝ} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ))) (hx : 0 < x) :
    ∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
      = ENNReal.ofReal (f δ - f (x + δ)) := by
  have := hμ.isFiniteMeasure
  have h_one : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) μ := integrable_const 1
  have h_exp : Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ :=
    integrable_exp_neg_mul μ hx.le
  have h_nonneg : 0 ≤ᵐ[μ] fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ))) := by
    refine Filter.Eventually.of_forall fun p => ?_
    exact sub_nonneg.mpr (exp_neg_mul_le_one hx.le p)
  have hint : Integrable (fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))) μ :=
    h_one.sub h_exp
  have h_int :
      ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ = f δ - f (x + δ) := by
    calc
      ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
          = (∫ _p : ℝ≥0, (1 : ℝ) ∂μ) -
              ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ := by
            rw [integral_sub h_one h_exp]
      _ = μ.real univ - laplaceTransform μ x := by
            simp [laplaceTransform_apply]
      _ = f δ - f (x + δ) := by
            have h0 := hμ.eq_laplaceTransform (t := 0) le_rfl
            have hxrep := hμ.eq_laplaceTransform (t := x) hx.le
            have h0' : f δ = μ.real univ := by
              simpa [laplaceTransform_zero] using h0
            rw [← h0', ← hxrep]
  rw [← ofReal_integral_eq_lintegral_ofReal hint h_nonneg, h_int]

/-- Markov tail bound: the mass outside the closed ball of radius `R` is controlled by the `∫⁻`
of `p ↦ 1 - exp(-x·p)` divided by its boundary value `1 - exp(-x·R)` (for `x, R > 0`). -/
private lemma measure_closedBall_compl_le_lintegral_div
    {μ : Measure ℝ≥0} {x R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
        / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
  set c : ℝ := 1 - Real.exp (-(x * R)) with hc_def
  have hc_pos : 0 < c := one_sub_exp_neg_mul_pos hx hR
  have hc_ne_zero : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc_pos
  have hc_ne_top : ENNReal.ofReal c ≠ (∞ : ENNReal) := ENNReal.ofReal_ne_top
  have hcoord_meas :
      AEMeasurable (fun p : ℝ≥0 => ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ))))) μ :=
    (ENNReal.measurable_ofReal.comp
      (by fun_prop : Measurable fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))))
        |>.aemeasurable
  refine (measure_mono ?_).trans (meas_ge_le_lintegral_div hcoord_meas hc_ne_zero hc_ne_top)
  intro p hp
  have hpdist : R < dist p (0 : ℝ≥0) := by
    simpa [Metric.mem_closedBall, not_le] using hp
  have hdist : dist p (0 : ℝ≥0) = (p : ℝ) := by
    simp [NNReal.dist_eq]
  have hRp : R ≤ (p : ℝ) := by linarith
  have hxp : x * R ≤ x * (p : ℝ) := mul_le_mul_of_nonneg_left hRp hx.le
  have hexp_le : Real.exp (-(x * (p : ℝ))) ≤ Real.exp (-(x * R)) :=
    Real.exp_le_exp.mpr (neg_le_neg hxp)
  have hreal : c ≤ 1 - Real.exp (-(x * (p : ℝ))) := by
    rw [hc_def]; linarith
  exact ENNReal.ofReal_le_ofReal hreal

/-- Tail bound for a Laplace-representing measure of a positive shift: the mass outside the
ball of radius `R` is controlled by the Laplace gap `f δ - f (x + δ)`. This is the tightness
input, not a decay rate in `R`: the denominator tends to `1` as `R → ∞`.

The estimate is Markov's inequality on the bounded coordinate `p ↦ 1 - exp (-x * p)`, factored into
`measure_closedBall_compl_le_lintegral_div` (the Markov bound) and
`lintegral_ofReal_one_sub_exp_eq_of_representsLaplace` (the Laplace-value identity). It is the
tightness input for shifting Bernstein's existence theorem back to the closed-half-line
theorem. -/
private lemma measure_closedBall_compl_le_of_representsLaplace_shift
    {f : ℝ → ℝ} {μ : Measure ℝ≥0}
    {δ x R : ℝ} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ)))
    (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
  have hc_pos : 0 < 1 - Real.exp (-(x * R)) := one_sub_exp_neg_mul_pos hx hR
  calc
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ
        ≤ (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
            / ENNReal.ofReal (1 - Real.exp (-(x * R))) :=
          measure_closedBall_compl_le_lintegral_div hx hR
    _ = ENNReal.ofReal (f δ - f (x + δ)) / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
          rw [lintegral_ofReal_one_sub_exp_eq_of_representsLaplace hμ hx]
    _ = ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
          rw [ENNReal.ofReal_div_of_pos hc_pos]

/-- The continuity-at-`0` step behind the tightness of the shifted representing measures: for any
`η > 0` there is a positive shift `x` and an index `N` beyond which the Laplace gap-quotient
`(f (aₙ) - f (x + aₙ)) / (1 - e⁻¹)` is at most `η`: the uniform-tail input to the tightness
of the shifted representing measures. The denominator `1 - e⁻¹` is the Markov constant
`1 - exp (-(x * R))` of `measure_closedBall_compl_le_of_representsLaplace_shift` at the radius
`R = x⁻¹` that the tightness proof chooses, so that `x * R = 1`. -/
private lemma exists_shift_uniform_gap_bound
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ x, 0 < x ∧ ∃ N, ∀ n, N ≤ n →
      (f (a n) - f (x + a n)) / (1 - Real.exp (-1)) ≤ η := by
  have hf_tendsto0 : Tendsto (fun n => f (a n)) atTop (𝓝 (f 0)) := by
    simpa using tendsto_apply_add_of_continuousOn hf le_rfl ha_pos ha
  let c0 : ℝ := 1 - Real.exp (-1)
  have hc0_pos : 0 < c0 := by
    have hexp_lt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    dsimp [c0]
    linarith
  have hetac : 0 < η * c0 := mul_pos hη hc0_pos
  obtain ⟨m, hm⟩ :=
    (hf_tendsto0.eventually (eventually_gt_nhds (by linarith : f 0 - η * c0 < f 0))).exists
  let x : ℝ := a m
  have hx_pos : 0 < x := ha_pos m
  have hlim_lt : f 0 - f x < η * c0 := by
    simpa [x, sub_lt_comm] using hm
  have hfx_tendsto : Tendsto (fun n => f (x + a n)) atTop (𝓝 (f x)) :=
    tendsto_apply_add_of_continuousOn hf hx_pos.le ha_pos ha
  have hgap_tendsto :
      Tendsto (fun n => f (a n) - f (x + a n)) atTop (𝓝 (f 0 - f x)) :=
    hf_tendsto0.sub hfx_tendsto
  have hgap_event :
      ∀ᶠ n : ℕ in atTop, (f (a n) - f (x + a n)) / c0 ≤ η := by
    filter_upwards [hgap_tendsto.eventually_lt_const hlim_lt] with n hn
    rw [div_le_iff₀ hc0_pos]
    exact le_of_lt hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgap_event
  exact ⟨x, hx_pos, N, hN⟩

/-- The representing measures of positive shifts of a closed-half-line completely monotone
function are uniformly tight as the shifts tend to `0`.

The proof combines the finite initial-segment tightness with a uniform tail estimate for the
remaining shifts (`exists_shift_uniform_gap_bound`) and the Laplace-kernel tail bound
`measure_closedBall_compl_le_of_representsLaplace_shift`. -/
private lemma isTightMeasureSet_range_of_representsLaplace_shift
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0))
    {μ : ℕ → Measure ℝ≥0}
    (hμ : ∀ n, RepresentsLaplace (μ n) (fun t : ℝ => f (t + a n))) :
    IsTightMeasureSet (Set.range μ) := by
  have hμ_fin : ∀ n, IsFiniteMeasure (μ n) := fun n => (hμ n).isFiniteMeasure
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = (∞ : ENNReal)
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ν _hν
    rw [hε_top]
    exact le_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  obtain ⟨x, hx_pos, N, hN⟩ :=
    exists_shift_uniform_gap_bound hf ha_pos ha hε_real_pos
  let μfin : {n // n < N} → Measure ℝ≥0 := fun n => μ n
  have hfin_tight : IsTightMeasureSet (Set.range μfin) :=
    isTightMeasureSet_range_finite μfin (fun n => hμ_fin n)
  obtain ⟨Kfin, hKfin_comp, hKfin_tail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hfin_tight ε hε
  -- The radius is tied to the shift so that `x * R = 1`, matching the `1 - e⁻¹` denominator
  -- in the gap bound above.
  let R : ℝ := x⁻¹
  have hR_pos : 0 < R := inv_pos.mpr hx_pos
  refine ⟨Kfin ∪ Metric.closedBall (0 : ℝ≥0) R,
    hKfin_comp.union (isCompact_closedBall _ _), ?_⟩
  intro ν hν
  rcases hν with ⟨n, rfl⟩
  by_cases hnlt : n < N
  · have hmem_fin : μ n ∈ Set.range μfin := ⟨⟨n, hnlt⟩, rfl⟩
    have hsubset : (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆ Kfinᶜ :=
      compl_subset_compl.mpr (subset_union_left)
    exact (measure_mono hsubset).trans (hKfin_tail (μ n) hmem_fin)
  · have hNn : N ≤ n := le_of_not_gt hnlt
    have hball_subset :
        (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆
          (Metric.closedBall (0 : ℝ≥0) R)ᶜ :=
      compl_subset_compl.mpr (subset_union_right)
    have htail :=
      measure_closedBall_compl_le_of_representsLaplace_shift (hμ n) hx_pos hR_pos
    have hden : 1 - Real.exp (-(x * R)) = 1 - Real.exp (-1) := by
      dsimp [R]
      rw [mul_inv_cancel₀ hx_pos.ne']
    have hquot :
        ENNReal.ofReal
          ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) ≤ ε := by
      rw [hden]
      exact ENNReal.ofReal_le_of_le_toReal (hN n hNn)
    calc
      μ n (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ
          ≤ μ n (Metric.closedBall (0 : ℝ≥0) R)ᶜ := measure_mono hball_subset
      _ ≤ ENNReal.ofReal
            ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) := htail
      _ ≤ ε := hquot

/-- The representing measure of the positive shift `t ↦ f (t + δ)` has total mass
`f δ ≤ f 0`. -/
private lemma measure_univ_le_of_representsLaplace_shift
    {f : ℝ → ℝ} (hf : IsCompletelyMonotoneOnIci f) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : Measure ℝ≥0} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ))) :
    μ univ ≤ ENNReal.ofReal (f 0) := by
  have := hμ.isFiniteMeasure
  have hreal : μ.real univ = f δ := by
    simpa [laplaceTransform_zero] using (hμ.eq_laplaceTransform (t := 0) le_rfl).symm
  calc
    μ univ = ENNReal.ofReal (μ.real univ) := by rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (f 0) :=
        ENNReal.ofReal_le_ofReal (hreal ▸ hf.le_apply_zero hδ)

/-- **Existence half of the Hausdorff--Bernstein--Widder theorem**: a function continuous on
`[0, ∞)` and completely monotone on `(0, ∞)` is the Laplace transform of a finite positive
measure on `ℝ≥0`. -/
theorem exists_representsLaplace_of_isCompletelyMonotoneOnIci
    {f : ℝ → ℝ} (hf : IsCompletelyMonotoneOnIci f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  classical
  -- Stage 1: the positive null sequence of shifts `aₙ = 1/(n+1)`.
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Stage 2: representing measures for the shifted functions, from Bernstein's theorem.
  have hshift_cm : ∀ n, IsCompletelyMonotone (fun t : ℝ => f (t + a n)) :=
    fun n => hf.isCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const (ha_pos n)
  choose μ hμ using fun n =>
    exists_representsLaplace_of_isCompletelyMonotone (hshift_cm n)
  -- Stage 3: a uniform mass bound and tightness give a weak cluster point.
  let C : ℝ≥0 := ⟨f 0, hf.nonneg_zero⟩
  have hmass : ∀ n, (μ n) univ ≤ (C : ENNReal) := fun n =>
    calc
      (μ n) univ ≤ ENNReal.ofReal (f 0) :=
        measure_univ_le_of_representsLaplace_shift hf (ha_pos n).le (hμ n)
      _ = (C : ENNReal) := ENNReal.ofReal_eq_coe_nnreal hf.nonneg_zero
  have htight : IsTightMeasureSet (Set.range μ) :=
    isTightMeasureSet_range_of_representsLaplace_shift hf.continuousOn ha_pos ha hμ
  obtain ⟨μ₀, U, hUle, hμ₀_fin, _hmass₀, hweak⟩ :=
    finite_measure_cluster_limit (σ := μ) C hmass htight
  -- Stage 4: identify the cluster point as a representing measure via continuity at `0⁺`.
  refine ⟨μ₀, representsLaplace_iff.mpr ⟨hμ₀_fin, fun t ht => ?_⟩⟩
  have hf_arg_U : Tendsto (fun n => f (t + a n)) (U : Filter ℕ) (𝓝 (f t)) :=
    (tendsto_apply_add_of_continuousOn hf.continuousOn ht ha_pos ha).mono_left hUle
  have hshift_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (𝓝 (f t)) := by
    refine Tendsto.congr (fun n => ?_) hf_arg_U
    rw [(hμ n).eq_laplaceTransform (t := t) ht, laplaceTransform_apply]
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (𝓝 (laplaceTransform μ₀ t)) := by
    rw [laplaceTransform_apply]
    simpa using hweak (laplaceKernelBoundedContinuous ht)
  exact tendsto_nhds_unique hshift_laplace hweak_laplace

/-! ## Headline theorem -/

end TauCeti
end


open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction

namespace CopulaProof

lemma crossing (t s m : ℝ) (x y : ℝ≥0)
    (hx : Real.exp (-(x:ℝ)*m) < (Real.exp (-(x:ℝ)*t)+Real.exp (-(x:ℝ)*s))/2)
    (hy : (Real.exp (-(y:ℝ)*t)+Real.exp (-(y:ℝ)*s))/2 < Real.exp (-(y:ℝ)*m)) :
    y ≤ x := by
  by_contra! hxy
  let F := fun z : ℝ => Real.exp ((m-t)*z) + Real.exp ((m-s)*z)
  have linear_exp (c : ℝ) : ConvexOn ℝ Set.univ (fun z : ℝ => Real.exp (c*z)) := by
    convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ c) using 1
  have cv : ConvexOn ℝ Set.univ F := (linear_exp _).add (linear_exp _)
  have hrep (z : ℝ) : F z =
      (Real.exp (-z*t)+Real.exp (-z*s))*Real.exp (z*m) := by
    dsimp [F]
    rw [add_mul,← Real.exp_add,← Real.exp_add]
    congr 2 <;> ring
  have one (z : ℝ) : Real.exp (-z*m)*Real.exp (z*m)=1 := by
    rw [← Real.exp_add,show -z*m+z*m=0 by ring,Real.exp_zero]
  have xgt := mul_lt_mul_of_pos_right hx (Real.exp_pos ((x:ℝ)*m))
  have ylt := mul_lt_mul_of_pos_right hy (Real.exp_pos ((y:ℝ)*m))
  rw [one] at xgt ylt
  have hx' : 2 < F x := by rw [hrep]; linarith
  have hy' : F y < 2 := by rw [hrep]; linarith
  have hz : F 0 = 2 := by norm_num [F]
  have inside : (x:ℝ) ∈ segment ℝ 0 (y:ℝ) := by
    exact Icc_subset_segment (show (x:ℝ) ∈ Set.Icc (0:ℝ) (y:ℝ) from ⟨x.2,hxy.le⟩)
  have h := cv.le_on_segment (Set.mem_univ 0) (Set.mem_univ _) inside
  rw [hz,max_eq_left hy'.le] at h
  linarith

lemma threshold (Z H : ℝ≥0 → ℝ) (hZ : Antitone Z) (hH : Antitone H)
    (bounded : ∀ x, 0≤Z x+H x ∧ Z x+H x≤2)
    (order : ∀ x y, Z x < H x → H y < Z y → y ≤ x) :
    ∃ d : ℝ, ∀ x, 0 ≤ (Z x-H x)*(Z x+H x-d) := by
  let S : Set ℝ := insert 0 ((fun x => Z x+H x) '' {x | Z x < H x})
  have bdd : BddAbove S := by
    refine ⟨2,?_⟩
    rintro a (rfl | ⟨x,_,rfl⟩)
    · norm_num
    · exact (bounded x).2
  refine ⟨sSup S, fun x => ?_⟩
  rcases lt_trichotomy (Z x) (H x) with h|h|h
  · have hh : Z x+H x ≤ sSup S := le_csSup bdd (Or.inr ⟨x,h,rfl⟩)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · simp [h]
  · have hh : sSup S ≤ Z x+H x := by
      apply csSup_le (Set.insert_nonempty _ _)
      rintro a (rfl | ⟨y,hy,rfl⟩)
      · exact (bounded x).1
      · exact add_le_add (hZ (order y x hy h)) (hH (order y x hy h))
    exact mul_nonneg (by linarith) (by linarith)

lemma positive_variance (E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ) (unity : E 1=1)
    (pos : ∀ g : ℝ≥0 →ᵇ ℝ, (∀ x, 0≤g x) → 0≤E g) (D : ℝ≥0 →ᵇ ℝ) :
    (E D)^2 ≤ E (D*D) := by
  have h := pos (D*D - (2*E D) • D + ((E D)^2) • 1) (fun x => by
    change 0 ≤ D x * D x - (2*E D)*D x + (E D)^2*1
    nlinarith [sq_nonneg (D x-E D)])
  simp only [map_add,map_sub,map_smul,smul_eq_mul,unity,mul_one] at h
  nlinarith

lemma compare (E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ) (unity : E 1=1)
    (pos : ∀ g : ℝ≥0 →ᵇ ℝ, (∀ x, 0≤g x) → 0≤E g)
    (A B Z : ℝ≥0 →ᵇ ℝ) (avg : E Z = (E A+E B)/2)
    (cross : ∃ d : ℝ, ∀ x, 0 ≤ (Z x-(A x+B x)/2)*(Z x+(A x+B x)/2-d)) :
    E (A*B)-E A*E B ≤ E (Z*Z)-(E Z)^2 := by
  let H : ℝ≥0 →ᵇ ℝ := (1/2:ℝ) • (A+B)
  let D : ℝ≥0 →ᵇ ℝ := (1/2:ℝ) • (A-B)
  have hH : E H = (E A+E B)/2 := by simp [H]; ring
  have hD : E D = (E A-E B)/2 := by simp [D]; ring
  obtain ⟨d,hd⟩ := cross
  have hz := pos (Z*Z - H*H - d • (Z-H)) (fun x => by
    change 0 ≤ Z x*Z x - (1/2*(A x+B x))*(1/2*(A x+B x))-d*(Z x-1/2*(A x+B x))
    nlinarith [hd x])
  have prod : H*H-D*D = A*B := by
    ext x
    change (1/2*(A x+B x))*(1/2*(A x+B x)) -
      (1/2*(A x-B x))*(1/2*(A x-B x)) = A x*B x
    ring
  have hh := congrArg E prod
  simp only [map_sub,map_smul,smul_eq_mul,hH,avg,sub_self,mul_zero,sub_zero] at hz
  rw [map_sub] at hh
  have hv := positive_variance E unity pos D
  rw [hD] at hv
  rw [avg]
  nlinarith


open OMA.S_mo_195959

/-- Finite-measure Bernstein-Widder representation on the open positive half-line. -/
def H1 : Prop := ∀ f : ℝ → ℝ, ContinuousOn f (Set.Ici 0) → f 0 = 1 →
    CompletelyMonotoneOn f (Set.Ioi 0) →
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 < t → f t = ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ

/-- The right limit at zero of a finite measure's Laplace transform is its mass. -/
def H2 : Prop := ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ →
    Tendsto (fun t : ℝ => ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ _ : ℝ≥0, (1:ℝ) ∂μ))

lemma normalized_integral (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (mass : (∫ _ : ℝ≥0, (1:ℝ) ∂μ) = 1) :
    ∃ E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ, E 1 = 1 ∧
      (∀ g : ℝ≥0 →ᵇ ℝ, (∀ x, 0≤g x) → 0≤E g) ∧
      ∀ g : ℝ≥0 →ᵇ ℝ, E g = ∫ r, g r ∂μ := by
  let E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => ∫ r, g r ∂μ
      map_add' := fun g h => integral_add (BoundedContinuousFunction.integrable μ g)
        (BoundedContinuousFunction.integrable μ h)
      map_smul' := fun c g => integral_const_mul c (fun x => g x) }
  refine ⟨E,?_,fun g hg => integral_nonneg hg,fun _ => rfl⟩
  change (∫ _ : ℝ≥0, (1:ℝ) ∂μ) = 1
  exact mass

lemma inverse_value {f : ℝ → ℝ} (hc : ContinuousOn f (Set.Ici 0)) (h₀ : f 0=1)
    (hl : Tendsto f atTop (𝓝 0)) (u : ℝ) (hu : 0<u) (h1 : u≤1) :
    0 ≤ Function.invFunOn f (Set.Ici 0) u ∧ f (Function.invFunOn f (Set.Ici 0) u) = u := by
  obtain ⟨N,hN,hfN⟩ := ((eventually_ge_atTop (0:ℝ)).and (hl.eventually (Iio_mem_nhds hu))).exists
  have hx : u ∈ f '' Set.Icc 0 N :=
    intermediate_value_Icc' hN (hc.mono (fun _ h => h.1)) ⟨hfN.le, h₀ ▸ h1⟩
  obtain ⟨z,hz,he⟩ := hx
  have h : ∃ z ∈ Set.Ici (0:ℝ), f z = u := ⟨z,hz.1,he⟩
  exact ⟨Function.invFunOn_mem h,Function.invFunOn_eq h⟩

theorem main : H1 → H2 → type_of% @OMA.S_mo_195959.main := by
  intro repr atZero f hc h₀ hl hcm u hu v hv
  obtain ⟨μ,hμ,repPos⟩ := repr f hc h₀ hcm
  let _ := hμ
  have ft : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 1) := by
    rw [← h₀]
    exact (hc 0 (Set.mem_Ici.mpr le_rfl)).mono (Set.Ioi_subset_Ici_self)
  have eqp : f =ᶠ[𝓝[>] (0:ℝ)] (fun t => ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ) :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => repPos t ht)
  have mass := tendsto_nhds_unique (atZero μ hμ) (ft.congr' eqp)
  have rep (t : ℝ) (ht : 0 ≤ t) : f t = ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ := by
    rcases eq_or_lt_of_le ht with he|hp
    · subst t
      simpa only [mul_zero,Real.exp_zero,h₀] using mass.symm
    · exact repPos t hp
  obtain ⟨E,one,pos,eval⟩ := normalized_integral μ mass
  let K (t : ℝ) (ht : 0≤t) : ℝ≥0 →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℝ≥0 => Real.exp (-(x:ℝ)*t)) (by fun_prop) 1 (fun x => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr x.2) ht)
  have bounds (t : ℝ) (ht : 0≤t) (x : ℝ≥0) : 0≤K t ht x ∧ K t ht x≤1 := by
    exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr x.2) ht)⟩
  have anti (t : ℝ) (ht : 0≤t) : Antitone (K t ht) := by
    intro x y hxy
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hxy) ht)
  have mean (t : ℝ) (ht : 0≤t) : E (K t ht) = f t := (eval _).trans (rep t ht).symm
  have both (t s : ℝ) (ht : 0≤t) (hs : 0 ≤ s) : E (K t ht*K s hs) = f (t+s) := by
    have eq : K t ht * K s hs = K (t+s) (add_nonneg ht hs) := by
      ext r
      change Real.exp (-(r:ℝ)*t)*Real.exp (-(r:ℝ)*s) = Real.exp (-(r:ℝ)*(t+s))
      rw [← Real.exp_add,mul_add]
    rw [eq]
    exact mean (t+s) (add_nonneg ht hs)
  let a := (u+v)/2
  have hu₀ := hu.1
  have hv₀ := hv.1
  have hu₁ := hu.2
  have hv₁ := hv.2
  change archC f u v-u*v ≤ archC f a a - a^2
  by_cases ha : a = 0
  · have u0 : u = 0 := by dsimp [a] at ha; linarith
    have v0 : v = 0 := by dsimp [a] at ha; linarith
    simp [ha,u0,v0,archC]
  let m := Function.invFunOn f (Set.Ici 0) a
  have ha₀ : 0<a := lt_of_le_of_ne (by dsimp [a]; linarith) (Ne.symm ha)
  have ha₁ : a≤1 := by dsimp [a]; linarith
  obtain ⟨hm,hmv⟩ := inverse_value hc h₀ hl a ha₀ ha₁
  have mmean : E (K m hm) = a := (mean m hm).trans hmv
  have md : archC f a a = E (K m hm * K m hm) := by
    simp only [archC, if_neg (not_or.mpr ⟨ha,ha⟩)]
    exact (both m m hm hm).symm
  rw [md]
  by_cases hzero : u=0 ∨ v=0
  · have hvar := positive_variance E one pos (K m hm)
    rw [mmean] at hvar
    have uvzero : u*v=0 := mul_eq_zero.mpr hzero
    simp only [archC,if_pos hzero,uvzero,sub_self]
    linarith
  have hn := not_or.mp hzero
  let t := Function.invFunOn f (Set.Ici 0) u
  let s := Function.invFunOn f (Set.Ici 0) v
  obtain ⟨ht,htu⟩ := inverse_value hc h₀ hl u (lt_of_le_of_ne hu₀ (Ne.symm hn.1)) hu₁
  obtain ⟨hs,hsv⟩ := inverse_value hc h₀ hl v (lt_of_le_of_ne hv₀ (Ne.symm hn.2)) hv₁
  have tmean : E (K t ht) = u := (mean t ht).trans htu
  have smean : E (K s hs) = v := (mean s hs).trans hsv
  have huv : archC f u v = E (K t ht*K s hs) := by
    rw [archC,if_neg hzero]; exact (both t s ht hs).symm
  have meanEq : E (K m hm) = (E (K t ht)+E (K s hs))/2 := by rw [mmean,tmean,smean]
  have cross := threshold (K m hm) (fun x => (K t ht x+K s hs x)/2) (anti m hm)
    (fun x y hxy => by linarith [anti t ht hxy,anti s hs hxy])
    (fun x => by
      obtain ⟨h₁,h₂⟩ := bounds m hm x
      obtain ⟨h₃,h₄⟩ := bounds t ht x
      obtain ⟨h₅,h₆⟩ := bounds s hs x
      constructor <;> linarith) (crossing t s m)
  have conclusion := compare E one pos (K t ht) (K s hs) (K m hm) meanEq cross
  rwa [← huv,tmean,smean,mmean] at conclusion

end CopulaProof

theorem CopulaProof.laplace_mass (μ : Measure ℝ≥0) (hμ : IsFiniteMeasure μ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ _ : ℝ≥0, (1:ℝ) ∂μ)) := by
  let _ := hμ
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun t => (show Continuous (fun x : ℝ≥0 =>
      Real.exp (-(x:ℝ)*t)) by fun_prop).aestronglyMeasurable)
  · refine ⟨1, Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => ?_)⟩
    change ∀ᵐ x : ℝ≥0 ∂μ, ‖Real.exp (-(x:ℝ)*t)‖ ≤ 1
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr x.2) (le_of_lt ht))
  · refine Eventually.of_forall (fun x => ?_)
    have h : Continuous (fun t : ℝ => Real.exp (-(x:ℝ)*t)) := by fun_prop
    have hc : Tendsto (fun t : ℝ => Real.exp (-(x:ℝ)*t)) (𝓝[>] (0:ℝ))
        (𝓝 (Real.exp (-(x:ℝ)*0))) := h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero,Real.exp_zero] using hc

theorem OMA.solution : type_of% @OMA.S_mo_195959.main := by
  apply CopulaProof.main _ CopulaProof.laplace_mass
  intro f hc _ hcm
  have hf : TauCeti.IsCompletelyMonotoneOnIci f := by
    refine ⟨hc,hcm.1,fun n t ht => ?_⟩
    have hh := hcm.2 n t ht
    rwa [iteratedDerivWithin_of_isOpen isOpen_Ioi ht] at hh
  obtain ⟨μ,hμ,hfμ⟩ := TauCeti.exists_representsLaplace_of_isCompletelyMonotoneOnIci hf
  refine ⟨μ,hμ,fun t ht => ?_⟩
  simpa only [TauCeti.laplaceTransform, neg_mul, mul_comm t] using hfμ t ht.le
