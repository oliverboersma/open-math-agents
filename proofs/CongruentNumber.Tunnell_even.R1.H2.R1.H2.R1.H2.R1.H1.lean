import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
# The logarithmic derivative of the elliptic unit

The square lattice of the congruent-number curve scales the Gaussian zeta
trace by its real period. A multiplication formula for Weierstrass zeta
identifies the scaled trace with the logarithmic derivative of the stated
product of translates of the Weierstrass function.

The Weierstrass sigma, zeta and degree-two results in the following sections
come from the LSG project, with its copyright notices and Apache 2.0
license reproduced in this file. The material is arranged as a single Lean
module for this verifier.
-/


/-
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
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

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

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# The Weierstrass `ζ` function

For a period pair `L` we define the Weierstrass zeta function as the lattice sum
`ζ(z) = 1/z + Σ'_{ω ≠ 0} (1/(z - ω) + 1/ω + z/ω²)`.

In Lean the term for `ω = 0` is `1/(z - 0) + 1/0 + z/0² = 1/z` (junk value `1/0 = 0`), so we can
sum over the whole lattice.

## Main results
* `LSG.Weierstrass.hasSumLocallyUniformly_zeta`: the series converges locally uniformly on `ℂ`.
* `LSG.Weierstrass.differentiableOn_zeta`: `ζ` is holomorphic off the lattice.
* `LSG.Weierstrass.hasDerivAt_zeta`: `ζ' = -℘` off the lattice.
* `LSG.Weierstrass.zeta_neg`: `ζ` is odd.
-/

open Module Filter
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/-- The summand of the Weierstrass `ζ` series: `1/(z - l) + 1/l + z/l²`. For `l = 0` it equals
`1/z`. -/
def zetaSummand (l z : ℂ) : ℂ := 1 / (z - l) + 1 / l + z / l ^ 2

lemma zetaSummand_eq (l z : ℂ) (hl : l ≠ 0) (hz : z ≠ l) :
    zetaSummand l z = z ^ 2 / (l ^ 2 * (z - l)) := by
  have : z - l ≠ 0 := sub_ne_zero.mpr hz
  unfold zetaSummand
  field_simp
  ring

/-- Bound on the summands for `‖z‖ < r ≤ ‖l‖/2`. -/
lemma zetaSummand_bound (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < r) (l : ℂ)
    (h : 2 * r ≤ ‖l‖) : ‖zetaSummand l z‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hl : l ≠ 0 := norm_pos_iff.mp hl0
  have hzl : z ≠ l := by rintro rfl; linarith
  have hzl' : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]
    have := norm_sub_norm_le l z
    linarith
  rw [zetaSummand_eq l z hl hzl, Real.rpow_neg hl0.le, norm_div, norm_mul, norm_pow, norm_pow]
  have h3 : ‖l‖ ^ (3 : ℝ) = ‖l‖ ^ 3 := by norm_cast
  rw [h3, div_le_iff₀ (mul_pos (by positivity) (by linarith))]
  have hz2 : ‖z‖ ^ 2 ≤ r ^ 2 := by gcongr
  calc ‖z‖ ^ 2 ≤ r ^ 2 := hz2
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * (‖l‖ / 2)) := by field_simp
    _ ≤ 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * ‖z - l‖) := by gcongr

/-- The Weierstrass `ζ` function `ζ(z) = 1/z + Σ'_{ω ≠ 0} (1/(z - ω) + 1/ω + z/ω²)`. -/
def zeta (z : ℂ) : ℂ := ∑' l : L.lattice, zetaSummand l z

lemma hasSumLocallyUniformly_zeta :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ zetaSummand l z) (zeta L) := by
  refine PeriodPair.hasSumLocallyUniformly_aux L (u := fun r l ↦ 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ)) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  exact zetaSummand_bound r hr s hs l h

lemma hasSum_zeta (z : ℂ) : HasSum (fun l : L.lattice ↦ zetaSummand l z) (zeta L z) :=
  (hasSumLocallyUniformly_zeta L).hasSum

lemma summable_zetaSummand (z : ℂ) : Summable (fun l : L.lattice ↦ zetaSummand l z) :=
  (hasSum_zeta L z).summable

lemma isOpen_compl_coe_lattice : IsOpen (L.latticeᶜ : Set ℂ) :=
  L.isClosed_lattice.isOpen_compl

lemma hasDerivAt_zetaSummand (l x : ℂ) (hxl : x - l ≠ 0) :
    HasDerivAt (zetaSummand l) (-(1 / (x - l) ^ 2 - 1 / l ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℂ ↦ y - l) 1 x := (hasDerivAt_id x).sub_const _
  have h2 : HasDerivAt (fun y : ℂ ↦ 1 / (y - l)) (-(1 : ℂ) / (x - l) ^ 2) x := by
    simpa only [one_div] using! h1.inv hxl
  have h3 : HasDerivAt (fun y : ℂ ↦ y / l ^ 2) (1 / l ^ 2) x :=
    (hasDerivAt_id x).div_const _
  have h4 : HasDerivAt (fun y ↦ 1 / (y - l) + 1 / l + y / l ^ 2)
      (-(1 : ℂ) / (x - l) ^ 2 + 0 + 1 / l ^ 2) x :=
    (h2.add (hasDerivAt_const x (1 / l))).add h3
  have : zetaSummand l = fun y ↦ 1 / (y - l) + 1 / l + y / l ^ 2 := rfl
  rw [this]
  convert h4 using 1
  ring

lemma sub_coe_ne_zero {x : ℂ} (hx : x ∉ L.lattice) (l : L.lattice) : x - l ≠ 0 :=
  fun e ↦ hx (by rw [sub_eq_zero.mp e]; exact l.2)

lemma differentiableOn_zetaSummand (l : L.lattice) :
    DifferentiableOn ℂ (zetaSummand l) L.latticeᶜ := fun x hx ↦
  (hasDerivAt_zetaSummand l x (sub_coe_ne_zero L hx l)).differentiableAt.differentiableWithinAt

lemma deriv_zetaSummand (l : L.lattice) (x : ℂ) (hx : x ∉ L.lattice) :
    deriv (zetaSummand l) x = -(1 / (x - l) ^ 2 - 1 / (l : ℂ) ^ 2) :=
  (hasDerivAt_zetaSummand l x (sub_coe_ne_zero L hx l)).deriv

/-- `ζ` is holomorphic off the lattice. -/
lemma differentiableOn_zeta : DifferentiableOn ℂ (zeta L) L.latticeᶜ := by
  refine (hasSumLocallyUniformly_zeta L).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun i _ ↦ differentiableOn_zetaSummand L i)
    (isOpen_compl_coe_lattice L)

lemma hasSumLocallyUniformly_neg_weierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ -(1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
      (fun z ↦ -℘[L] z) := by
  have := PeriodPair.hasSumLocallyUniformly_aux L
    (fun (l : L.lattice) (z : ℂ) ↦ -(1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
    (u := fun r l ↦ 10 * r * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, by
      rintro _ h s hs l rfl
      rw [norm_neg]
      exact PeriodPair.weierstrassP_bound r hr s hs l h⟩
  convert this using 2 with z
  rw [tsum_neg, PeriodPair.weierstrassP]

/-- `ζ' = -℘` off the lattice. -/
lemma eqOn_deriv_zeta : Set.EqOn (deriv (zeta L)) (fun z ↦ -℘[L] z) L.latticeᶜ := by
  refine ((hasSumLocallyUniformly_zeta L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ ?_) (isOpen_compl_coe_lattice L)).unique ?_
  · exact .fun_sum fun i _ ↦ differentiableOn_zetaSummand L i
  · have := (hasSumLocallyUniformly_neg_weierstrassP L).tendstoLocallyUniformlyOn
      (s := L.latticeᶜ)
    refine this.congr ?_
    intro s x hx
    simp only [Function.comp_apply]
    rw [deriv_fun_sum (fun i _ ↦ (differentiableOn_zetaSummand L i x hx).differentiableAt
      ((isOpen_compl_coe_lattice L).mem_nhds hx))]
    exact Finset.sum_congr rfl fun i _ ↦ (deriv_zetaSummand L i x hx).symm

/-- `ζ' = -℘` off the lattice. -/
lemma hasDerivAt_zeta {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt (zeta L) (-℘[L] z) z := by
  have hd : DifferentiableAt ℂ (zeta L) z :=
    (differentiableOn_zeta L z hz).differentiableAt ((isOpen_compl_coe_lattice L).mem_nhds hz)
  have := hd.hasDerivAt
  rwa [eqOn_deriv_zeta L hz] at this

lemma zetaSummand_neg (l z : ℂ) : zetaSummand (-l) (-z) = -zetaSummand l z := by
  unfold zetaSummand
  have h1 : -z - -l = -(z - l) := by ring
  rw [h1]
  simp only [one_div, inv_neg, neg_sq, neg_div]
  ring

/-- `ζ` is odd. -/
lemma zeta_neg (z : ℂ) : zeta L (-z) = -zeta L z := by
  calc zeta L (-z) = ∑' l : L.lattice, zetaSummand ((Equiv.neg L.lattice l : L.lattice) : ℂ) (-z) :=
        ((Equiv.neg L.lattice).tsum_eq (fun l : L.lattice ↦ zetaSummand (l : ℂ) (-z))).symm
    _ = ∑' l : L.lattice, -zetaSummand (l : ℂ) z := by
        congr 1 with l
        simp only [Equiv.neg_apply, NegMemClass.coe_neg, zetaSummand_neg]
    _ = -zeta L z := tsum_neg

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# The Weierstrass `σ` function

For a period pair `L` we define the Weierstrass sigma function as the Weierstrass product
`σ(z) = z ∏'_{ω ≠ 0} E(z/ω)`, `E(u) = (1 - u) exp (u + u²/2)`.

In Lean the factor for `ω = 0` is `E(z/0) = E 0 = 1`, so we take the product over the whole
lattice.

## Main results
* `LSG.Weierstrass.differentiable_sigma`: `σ` is entire.
* `LSG.Weierstrass.sigma_eq_zero_iff`: `σ z = 0 ↔ z ∈ L.lattice`.
* `LSG.Weierstrass.sigma_neg`: `σ` is odd.
* `LSG.Weierstrass.hasDerivAt_sigma_zero`: `σ'(0) = 1`.
* `LSG.Weierstrass.logDeriv_sigma`: `σ'/σ = ζ` off the lattice.
* `LSG.Weierstrass.deriv_sigma`: `σ' = ζ σ` off the lattice.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

/- ### The elementary factor -/

/-- Weierstrass' elementary factor of genus two, `E(u) = (1 - u) exp (u + u²/2)`. -/
def weierstrassFactor (u : ℂ) : ℂ := (1 - u) * exp (u + u ^ 2 / 2)

@[simp] lemma weierstrassFactor_zero : weierstrassFactor 0 = 1 := by
  simp [weierstrassFactor]

@[simp] lemma weierstrassFactor_one : weierstrassFactor 1 = 0 := by
  simp [weierstrassFactor]

lemma weierstrassFactor_eq_zero_iff {u : ℂ} : weierstrassFactor u = 0 ↔ u = 1 := by
  rw [weierstrassFactor, mul_eq_zero, sub_eq_zero, or_iff_left (exp_ne_zero _), eq_comm]

lemma differentiable_weierstrassFactor : Differentiable ℂ weierstrassFactor := by
  unfold weierstrassFactor; fun_prop

/-- `E'(u) = -u² exp (u + u²/2)`. -/
lemma hasDerivAt_weierstrassFactor (u : ℂ) :
    HasDerivAt weierstrassFactor (-u ^ 2 * exp (u + u ^ 2 / 2)) u := by
  have h1 : HasDerivAt (fun v : ℂ ↦ v + v ^ 2 / 2) (1 + u) u :=
    ((hasDerivAt_id' u).add ((hasDerivAt_pow 2 u).div_const 2)).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun v : ℂ ↦ (1 - v) * exp (v + v ^ 2 / 2))
      ((0 - 1) * exp (u + u ^ 2 / 2) + (1 - u) * (exp (u + u ^ 2 / 2) * (1 + u))) u :=
    ((hasDerivAt_const u (1 : ℂ)).sub (hasDerivAt_id' u)).mul h1.cexp
  exact h2.congr_deriv (by ring)

lemma logTaylor_three (z : ℂ) : logTaylor 3 z = z - z ^ 2 / 2 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring

/-- The key estimate `‖E(u) - 1‖ ≤ 2‖u‖³` for `‖u‖ ≤ 1/2`. -/
lemma norm_weierstrassFactor_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖weierstrassFactor u - 1‖ ≤ 2 * ‖u‖ ^ 3 := by
  have hu1 : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  have hne : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this] at hu; norm_num at hu
  set w := log (1 + -u) - logTaylor (2 + 1) (-u) with hw
  have hwb := norm_log_sub_logTaylor_le 2 hu1
  rw [← hw, norm_neg] at hwb
  have hw' : w = log (1 - u) + (u + u ^ 2 / 2) := by
    rw [hw, show (2 + 1 : ℕ) = 3 from rfl, logTaylor_three, ← sub_eq_add_neg]; ring
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hwle : ‖w‖ ≤ ‖u‖ ^ 3 := by
    calc ‖w‖ ≤ ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / (2 + 1) := by exact_mod_cast hwb
      _ ≤ ‖u‖ ^ 3 * 2 / 3 := by
          norm_num
          gcongr
      _ ≤ ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]
  have hu3 : ‖u‖ ^ 3 ≤ 1 := by
    calc ‖u‖ ^ 3 ≤ (1 / 2) ^ 3 := by gcongr
      _ ≤ 1 := by norm_num
  have hexp : weierstrassFactor u = exp w := by
    rw [hw', exp_add, exp_log hne, weierstrassFactor]
  rw [hexp]
  calc ‖exp w - 1‖ ≤ 2 * ‖w‖ := norm_exp_sub_one_le (hwle.trans hu3)
    _ ≤ 2 * ‖u‖ ^ 3 := by gcongr

/- ### Lattice bookkeeping -/

variable (L : PeriodPair)

/-- All but finitely many lattice points have norm at least `R`. -/
lemma eventually_le_norm (R : ℝ) : ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  rw [Filter.eventually_cofinite]
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intro l hl
  simp only [Set.mem_ofPred_eq, not_le] at hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hl.le

lemma summable_norm_rpow_neg_three :
    Summable (fun l : L.lattice ↦ ‖(l : ℂ)‖ ^ (-3 : ℝ)) :=
  ZLattice.summable_norm_rpow _ _ (by simp; norm_num)

/-- Bound on the factors of the product for `‖z‖ ≤ r` and `‖l‖ ≥ 2r`. -/
lemma norm_weierstrassFactor_div_sub_one_le {r : ℝ} (hr : 0 < r) {z l : ℂ} (hz : ‖z‖ ≤ r)
    (hl : 2 * r ≤ ‖l‖) : ‖weierstrassFactor (z / l) - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hzl : ‖z / l‖ ≤ r / ‖l‖ := by rw [norm_div]; gcongr
  have hrl : r / ‖l‖ ≤ 1 / 2 := by rw [div_le_iff₀ hl0]; linarith
  refine (norm_weierstrassFactor_sub_one_le (hzl.trans hrl)).trans ?_
  rw [Real.rpow_neg hl0.le, show ‖l‖ ^ (3 : ℝ) = ‖l‖ ^ 3 by norm_cast]
  calc 2 * ‖z / l‖ ^ 3 ≤ 2 * (r / ‖l‖) ^ 3 := by gcongr
    _ = 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by field_simp

lemma summable_norm_weierstrassFactor_div_sub_one (z : ℂ) :
    Summable (fun l : L.lattice ↦ ‖weierstrassFactor (z / l) - 1‖) := by
  set r := ‖z‖ + 1
  have hr : 0 < r := by positivity
  refine ((summable_norm_rpow_neg_three L).mul_left (2 * r ^ 3)).of_norm_bounded_eventually ?_
  filter_upwards [eventually_le_norm L (2 * r)] with l hl
  rw [norm_norm]
  exact norm_weierstrassFactor_div_sub_one_le hr (by simp [r]) hl

/- ### The product -/

/-- The product `∏'_{ω} E(z/ω)`, so that `σ(z) = z · sigmaProd L z`. -/
def sigmaProd (z : ℂ) : ℂ := ∏' l : L.lattice, weierstrassFactor (z / l)

/-- The Weierstrass sigma function `σ(z) = z ∏'_{ω ≠ 0} (1 - z/ω) exp (z/ω + z²/(2ω²))`. -/
def sigma (z : ℂ) : ℂ := z * sigmaProd L z

lemma hasProdLocallyUniformlyOn_sigmaProd :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) ↦ weierstrassFactor (z / l))
      (sigmaProd L) Set.univ := by
  have key : HasProdLocallyUniformlyOn
      (fun (l : L.lattice) (z : ℂ) ↦ 1 + (weierstrassFactor (z / l) - 1))
      (fun z ↦ ∏' l : L.lattice, (1 + (weierstrassFactor (z / l) - 1))) Set.univ := by
    refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK ↦ ?_
    obtain ⟨r₀, hr₀⟩ := hK.isBounded.subset_closedBall 0
    set r := max r₀ 1
    have hr : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine Summable.hasProdUniformlyOn_one_add hK
      ((summable_norm_rpow_neg_three L).mul_left (2 * r ^ 3)) ?_ fun l ↦ ?_
    · filter_upwards [eventually_le_norm L (2 * r)] with l hl x hx
      refine norm_weierstrassFactor_div_sub_one_le hr ?_ hl
      have := hr₀ hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    · exact ((differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).sub_const
        _).continuous.continuousOn
  rw [show sigmaProd L = fun z ↦ ∏' l : L.lattice, weierstrassFactor (z / l) from rfl]
  simpa only [add_sub_cancel] using key

/-- The product is entire. -/
lemma differentiable_sigmaProd : Differentiable ℂ (sigmaProd L) := by
  have := (hasProdLocallyUniformlyOn_sigmaProd L).differentiableOn
    (.of_forall fun s ↦ ?_) isOpen_univ
  · exact fun x ↦ (this x (Set.mem_univ x)).differentiableAt (isOpen_univ.mem_nhds trivial)
  · simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ ↦
      (differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).differentiableOn)

/-- `σ` is entire. -/
lemma differentiable_sigma : Differentiable ℂ (sigma L) :=
  differentiable_id.mul (differentiable_sigmaProd L)

lemma weierstrassFactor_div_ne_zero {z : ℂ} (hz : z ∉ L.lattice) (l : L.lattice) :
    weierstrassFactor (z / l) ≠ 0 := by
  rw [Ne, weierstrassFactor_eq_zero_iff]
  intro h
  have hl : (l : ℂ) ≠ 0 := by rintro h'; rw [h', div_zero] at h; exact zero_ne_one h
  rw [div_eq_one_iff_eq hl] at h
  exact hz (h ▸ l.2)

lemma sigmaProd_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : sigmaProd L z ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable
    (f := fun l : L.lattice ↦ weierstrassFactor (z / l) - 1)
    (fun l ↦ by simpa using weierstrassFactor_div_ne_zero L hz l)
    (summable_norm_weierstrassFactor_div_sub_one L z)
  simpa only [add_sub_cancel, sigmaProd] using this

lemma sigmaProd_coe (l : L.lattice) (hl : (l : ℂ) ≠ 0) : sigmaProd L l = 0 :=
  tprod_of_exists_eq_zero ⟨l, by simp [div_self hl]⟩

@[simp] lemma sigmaProd_zero : sigmaProd L 0 = 1 := by
  simp [sigmaProd]

/-- The zeros of `σ` are exactly the lattice points. -/
lemma sigma_eq_zero_iff {z : ℂ} : sigma L z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro h
    by_contra hz
    have hz0 : z ≠ 0 := fun h0 ↦ hz (h0 ▸ L.lattice.zero_mem)
    exact mul_ne_zero hz0 (sigmaProd_ne_zero L hz) h
  · intro hz
    by_cases hz0 : z = 0
    · simp [sigma, hz0]
    · simp [sigma, sigmaProd_coe L ⟨z, hz⟩ hz0]

lemma sigma_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : sigma L z ≠ 0 :=
  fun h ↦ hz ((sigma_eq_zero_iff L).mp h)

@[simp] lemma sigma_zero : sigma L 0 = 0 := by simp [sigma]

lemma sigma_coe (l : L.lattice) : sigma L l = 0 := (sigma_eq_zero_iff L).mpr l.2

lemma sigmaProd_neg (z : ℂ) : sigmaProd L (-z) = sigmaProd L z := by
  unfold sigmaProd
  rw [← (Equiv.neg L.lattice).tprod_eq]
  congr 1 with l
  simp [neg_div, div_neg]

/-- `σ` is odd. -/
lemma sigma_neg (z : ℂ) : sigma L (-z) = -sigma L z := by
  simp [sigma, sigmaProd_neg]

/-- `σ'(0) = 1`. -/
lemma hasDerivAt_sigma_zero : HasDerivAt (sigma L) 1 0 := by
  have := (hasDerivAt_id' (0 : ℂ)).mul (differentiable_sigmaProd L 0).hasDerivAt
  simpa only [mul_one,one_mul,zero_mul,add_zero,sigmaProd_zero] using! this

lemma deriv_sigma_zero : deriv (sigma L) 0 = 1 := (hasDerivAt_sigma_zero L).deriv

/- ### Logarithmic derivative -/

lemma hasDerivAt_weierstrassFactor_div (l x : ℂ) :
    HasDerivAt (fun z ↦ weierstrassFactor (z / l))
      (-(x / l) ^ 2 * exp (x / l + (x / l) ^ 2 / 2) * (1 / l)) x := by
  have h := (hasDerivAt_weierstrassFactor (x / l)).comp x ((hasDerivAt_id' x).div_const l)
  exact h

lemma logDeriv_weierstrassFactor_div (l x : ℂ) (hx : x ≠ l) :
    logDeriv (fun z ↦ weierstrassFactor (z / l)) x = if l = 0 then 0 else zetaSummand l x := by
  rw [logDeriv_apply, (hasDerivAt_weierstrassFactor_div l x).deriv]
  split_ifs with hl
  · simp [hl]
  · rw [zetaSummand_eq l x hl hx, weierstrassFactor]
    have h1 : (1 : ℂ) - x / l ≠ 0 := by
      rw [sub_ne_zero, ne_eq, eq_div_iff hl, one_mul]; exact fun h ↦ hx h.symm
    have h2 : x - l ≠ 0 := sub_ne_zero.mpr hx
    have h3 : (1 : ℂ) - x / l = -(x - l) / l := by field_simp; ring
    rw [h3]
    field_simp

lemma summable_logDeriv_weierstrassFactor_div {x : ℂ} (hx : x ∉ L.lattice) :
    Summable fun l : L.lattice ↦ logDeriv (fun z ↦ weierstrassFactor (z / l)) x := by
  have hxl : ∀ l : L.lattice, x ≠ l := fun l h ↦ hx (h ▸ l.2)
  simp_rw [logDeriv_weierstrassFactor_div _ _ (hxl _)]
  refine (summable_zetaSummand L x).congr_cofinite ?_
  filter_upwards [eventually_le_norm L 1] with l hl
  have : (l : ℂ) ≠ 0 := by rintro h; rw [h, norm_zero] at hl; norm_num at hl
  simp [this]

lemma tsum_logDeriv_weierstrassFactor_div {x : ℂ} (hx : x ∉ L.lattice) :
    ∑' l : L.lattice, logDeriv (fun z ↦ weierstrassFactor (z / l)) x = zeta L x - 1 / x := by
  have hxl : ∀ l : L.lattice, x ≠ l := fun l h ↦ hx (h ▸ l.2)
  simp_rw [logDeriv_weierstrassFactor_div _ _ (hxl _)]
  have hs := summable_zetaSummand L x
  have e : ∀ l : L.lattice, (if (l : ℂ) = 0 then 0 else zetaSummand l x) =
      zetaSummand l x - if l = 0 then 1 / x else 0 := by
    intro l
    by_cases hl : l = 0
    · simp [hl, zetaSummand]
    · have : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
      simp [hl, this]
  simp_rw [e]
  rw [hs.tsum_sub (summable_of_hasFiniteSupport ((Set.finite_singleton 0).subset (by
    intro l hl; by_contra h; simp_all))), tsum_ite_eq]
  rfl

lemma logDeriv_sigmaProd {x : ℂ} (hx : x ∉ L.lattice) :
    logDeriv (sigmaProd L) x = zeta L x - 1 / x := by
  have h := logDeriv_tprod_eq_tsum (isOpen_compl_coe_lattice L) hx
    (f := fun (l : L.lattice) (z : ℂ) ↦ weierstrassFactor (z / l))
    (weierstrassFactor_div_ne_zero L hx)
    (fun l ↦
      (differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).differentiableOn)
    (summable_logDeriv_weierstrassFactor_div L hx)
    ((hasProdLocallyUniformlyOn_sigmaProd L).multipliableLocallyUniformlyOn.mono
      (Set.subset_univ _))
    (sigmaProd_ne_zero L hx)
  rw [← tsum_logDeriv_weierstrassFactor_div L hx, ← h]
  rfl

/-- `σ'/σ = ζ` off the lattice. -/
lemma logDeriv_sigma {x : ℂ} (hx : x ∉ L.lattice) : logDeriv (sigma L) x = zeta L x := by
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ L.lattice.zero_mem)
  have := logDeriv_mul (f := id) (g := sigmaProd L) x hx0 (sigmaProd_ne_zero L hx)
    differentiableAt_id (differentiable_sigmaProd L x)
  rw [show sigma L = (fun z => id z * sigmaProd L z) from rfl, this, logDeriv_id, logDeriv_sigmaProd L hx]
  ring

/-- `σ' = ζ σ` off the lattice. -/
lemma deriv_sigma {x : ℂ} (hx : x ∉ L.lattice) : deriv (sigma L) x = zeta L x * sigma L x := by
  have := logDeriv_sigma L hx
  rw [logDeriv_apply, div_eq_iff (sigma_ne_zero L hx)] at this
  exact this

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# Quasi-periodicity of `ζ` and `σ`

For `ω` in the period lattice, `ζ(z + ω) - ζ(z)` is a constant `η(ω)` (the quasi-period), since
its derivative `-℘(z + ω) + ℘(z)` vanishes on the connected open set `ℂ ∖ Λ`. Consequently
`σ(z + ω) = c · exp (η(ω) z) σ(z)`, and evaluating at `z = -ω/2` (using that `σ` is odd) gives
`σ(z + ω) = -exp (η(ω) (z + ω/2)) σ(z)` when `ω/2 ∉ Λ`.

## Main results
* `LSG.Weierstrass.eta`: the quasi-period map `η : ℂ → ℂ` (meaningful on the lattice).
* `LSG.Weierstrass.zeta_add_eta`: `ζ(z + ω) = ζ(z) + η(ω)` for `ω ∈ Λ`, `z ∉ Λ`.
* `LSG.Weierstrass.eta_add`: `η` is additive on `Λ`.
* `LSG.Weierstrass.eta_eq_two_mul_zeta_half`: `η(ω) = 2 ζ(ω/2)` if `ω/2 ∉ Λ`.
* `LSG.Weierstrass.sigma_add_of_half_notMem`: `σ(z + ω) = -exp (η(ω) (z + ω/2)) σ(z)` if
  `ω ∈ Λ`, `ω/2 ∉ Λ`.
* `LSG.Weierstrass.sigma_add_ω₁`, `sigma_add_ω₂`: the two basis cases.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

lemma countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : Countable L.lattice := L.latticeEquivProd.injective.countable
  exact Set.countable_coe_iff.mp this

/-- The complement of the lattice is connected. -/
lemma isConnected_compl_lattice : IsConnected (L.lattice : Set ℂ)ᶜ :=
  Set.Countable.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
    (countable_lattice L)

lemma add_notMem_lattice {z ω : ℂ} (hz : z ∉ L.lattice) (hω : ω ∈ L.lattice) :
    z + ω ∉ L.lattice := fun h ↦ hz ((Submodule.add_mem_iff_left _ hω).mp h)

lemma zero_mem_lattice : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem

lemma ne_zero_of_notMem_lattice {z : ℂ} (hz : z ∉ L.lattice) : z ≠ 0 :=
  fun h ↦ hz (h ▸ zero_mem_lattice L)

/-- A function on `ℂ ∖ Λ` with vanishing derivative is constant there. -/
lemma eq_of_hasDerivAt_zero {g : ℂ → ℂ} (hg : ∀ z ∉ L.lattice, HasDerivAt g 0 z) {z w : ℂ}
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) : g z = g w :=
  (isOpen_compl_coe_lattice L).is_const_of_deriv_eq_zero
    (isConnected_compl_lattice L).isPreconnected
    (fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt) (fun x hx ↦ (hg x hx).deriv)
    hz hw

/- ### The quasi-periods of `ζ` -/

/-- The quasi-period `η(ω) = ζ(z + ω) - ζ(z)` (independent of `z ∉ Λ` when `ω ∈ Λ`); we use the
base point `z = ω₁/2`. -/
def eta (ω : ℂ) : ℂ := zeta L (L.ω₁ / 2 + ω) - zeta L (L.ω₁ / 2)

lemma hasDerivAt_zeta_add_sub {ω : ℂ} (hω : ω ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (fun z ↦ zeta L (z + ω) - zeta L z) 0 z := by
  have h1 := (hasDerivAt_zeta L (add_notMem_lattice L hz hω)).comp_add_const z ω
  have h2 : HasDerivAt (fun z ↦ zeta L (z + ω) - zeta L z) (-℘[L] (z + ω) - -℘[L] z) z :=
    h1.sub (hasDerivAt_zeta L hz)
  have hp : ℘[L] (z + ω) = ℘[L] z := L.weierstrassP_add_coe z ⟨ω, hω⟩
  rwa [hp, sub_self] at h2

/-- `ζ(z + ω) = ζ(z) + η(ω)` for `ω ∈ Λ` and `z ∉ Λ`. -/
lemma zeta_add_eta {ω : ℂ} (hω : ω ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    zeta L (z + ω) = zeta L z + eta L ω := by
  have : zeta L (z + ω) - zeta L z = zeta L (L.ω₁ / 2 + ω) - zeta L (L.ω₁ / 2) :=
    eq_of_hasDerivAt_zero L (g := fun z ↦ zeta L (z + ω) - zeta L z)
      (fun x hx ↦ hasDerivAt_zeta_add_sub L hω hx) hz L.ω₁_div_two_notMem_lattice
  rw [eta]
  linear_combination this

@[simp] lemma eta_zero : eta L 0 = 0 := by simp [eta]

/-- `η` is additive on the lattice. -/
lemma eta_add {ω ω' : ℂ} (hω : ω ∈ L.lattice) (hω' : ω' ∈ L.lattice) :
    eta L (ω + ω') = eta L ω + eta L ω' := by
  have h0 := L.ω₁_div_two_notMem_lattice
  have h1 := zeta_add_eta L (add_mem hω hω') h0
  have h2 := zeta_add_eta L hω' (add_notMem_lattice L h0 hω)
  have h3 := zeta_add_eta L hω h0
  rw [← add_assoc, h2, h3] at h1
  linear_combination -h1

lemma eta_neg {ω : ℂ} (hω : ω ∈ L.lattice) : eta L (-ω) = -eta L ω := by
  have := eta_add L hω (neg_mem hω)
  rw [add_neg_cancel, eta_zero] at this
  linear_combination -this

lemma eta_sub {ω ω' : ℂ} (hω : ω ∈ L.lattice) (hω' : ω' ∈ L.lattice) :
    eta L (ω - ω') = eta L ω - eta L ω' := by
  rw [sub_eq_add_neg, eta_add L hω (neg_mem hω'), eta_neg L hω', sub_eq_add_neg]

lemma eta_zsmul {ω : ℂ} (hω : ω ∈ L.lattice) (n : ℤ) : eta L (n * ω) = n * eta L ω := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℂ) * ω ∈ L.lattice := by
      simpa [zsmul_eq_mul] using L.lattice.smul_mem (n : ℤ) hω
    push_cast at ih ⊢
    rw [add_mul, one_mul, eta_add L hn hω, ih]; ring
  | pred n ih =>
    have hn : (-(n : ℂ)) * ω ∈ L.lattice := by
      simpa [zsmul_eq_mul] using L.lattice.smul_mem (-(n : ℤ)) hω
    push_cast at ih ⊢
    rw [sub_mul, one_mul, eta_sub L hn hω, ih]; ring

/-- `η(ω) = 2 ζ(ω/2)` when `ω/2 ∉ Λ`. -/
lemma eta_eq_two_mul_zeta_half {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) :
    eta L ω = 2 * zeta L (ω / 2) := by
  have hm : -(ω / 2) ∉ L.lattice := fun h ↦ hω2 (by simpa using neg_mem h)
  have := zeta_add_eta L hω hm
  rw [show -(ω / 2) + ω = ω / 2 by ring, zeta_neg] at this
  linear_combination -this

/- ### Quasi-periodicity of `σ` -/

lemma hasDerivAt_sigma (z : ℂ) : HasDerivAt (sigma L) (deriv (sigma L) z) z :=
  (differentiable_sigma L z).hasDerivAt

/-- `σ(z + ω) = c · exp (η(ω) z) · σ(z)` for some constant `c`, for every `ω ∈ Λ`. -/
lemma exists_sigma_add {ω : ℂ} (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, ∀ z, sigma L (z + ω) = c * exp (eta L ω * z) * sigma L z := by
  let G : ℂ → ℂ := fun z ↦ sigma L (z + ω) * exp (-(eta L ω * z)) / sigma L z
  have hG : ∀ z ∉ L.lattice, HasDerivAt G 0 z := by
    intro z hz
    have hz' := add_notMem_lattice L hz hω
    have h1 := (hasDerivAt_sigma L (z + ω)).comp_add_const z ω
    have h2 : HasDerivAt (fun z ↦ exp (-(eta L ω * z))) (exp (-(eta L ω * z)) * -(eta L ω * 1))
        z := ((hasDerivAt_id' z).const_mul (eta L ω)).neg.cexp
    have h3 := (h1.mul h2).div (hasDerivAt_sigma L z) (sigma_ne_zero L hz)
    refine h3.congr_deriv ?_
    rw [deriv_sigma L hz', deriv_sigma L hz, zeta_add_eta L hω hz]
    simp only [Pi.mul_apply]
    ring
  refine ⟨G (L.ω₁ / 2), fun z ↦ ?_⟩
  by_cases hz : z ∈ L.lattice
  · rw [sigma_coe L ⟨z, hz⟩, sigma_coe L ⟨z + ω, add_mem hz hω⟩, mul_zero]
  · have := eq_of_hasDerivAt_zero L hG hz L.ω₁_div_two_notMem_lattice
    have h1 := sigma_ne_zero L hz
    have h2 : exp (-(eta L ω * z)) * exp (eta L ω * z) = 1 := by rw [← exp_add]; simp
    have h3 : sigma L (z + ω) * exp (-(eta L ω * z)) = G (L.ω₁ / 2) * sigma L z := by
      rw [← this]; simp only [G]; rw [div_mul_cancel₀ _ h1]
    calc sigma L (z + ω) = sigma L (z + ω) * (exp (-(eta L ω * z)) * exp (eta L ω * z)) := by
          rw [h2, mul_one]
      _ = (sigma L (z + ω) * exp (-(eta L ω * z))) * exp (eta L ω * z) := by ring
      _ = _ := by rw [h3]; ring

/-- `σ(z + ω) = -exp (η(ω) (z + ω/2)) σ(z)` for `ω ∈ Λ` with `ω/2 ∉ Λ`. -/
lemma sigma_add_of_half_notMem {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) (z : ℂ) :
    sigma L (z + ω) = -exp (eta L ω * (z + ω / 2)) * sigma L z := by
  obtain ⟨c, hc⟩ := exists_sigma_add L hω
  set e := eta L ω
  have hs := sigma_ne_zero L hω2
  have h := hc (-(ω / 2))
  rw [show -(ω / 2) + ω = ω / 2 by ring, sigma_neg] at h
  have he : exp (e * -(ω / 2)) * exp (e * (ω / 2)) = 1 := by rw [← exp_add]; ring_nf; simp
  have hce : c * exp (e * -(ω / 2)) = -1 := by
    have : sigma L (ω / 2) * (c * exp (e * -(ω / 2)) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hs
    · linear_combination h'
  have hc' : c = -exp (e * (ω / 2)) := by linear_combination exp (e * (ω / 2)) * hce - c * he
  rw [hc z, hc', mul_add, exp_add]
  ring

lemma sigma_add_ω₁ (z : ℂ) :
    sigma L (z + L.ω₁) = -exp (eta L L.ω₁ * (z + L.ω₁ / 2)) * sigma L z :=
  sigma_add_of_half_notMem L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice z

lemma sigma_add_ω₂ (z : ℂ) :
    sigma L (z + L.ω₂) = -exp (eta L L.ω₂ * (z + L.ω₂ / 2)) * sigma L z :=
  sigma_add_of_half_notMem L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice z

/-- The inverse form: `σ(z - ω) = -exp (-η(ω) (z - ω/2)) σ(z)` for `ω ∈ Λ`, `ω/2 ∉ Λ`. -/
lemma sigma_sub_of_half_notMem {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) (z : ℂ) :
    sigma L (z - ω) = -exp (-(eta L ω * (z - ω / 2))) * sigma L z := by
  have h := sigma_add_of_half_notMem L hω hω2 (z - ω)
  rw [sub_add_cancel, show z - ω + ω / 2 = z - ω / 2 by ring] at h
  have : exp (-(eta L ω * (z - ω / 2))) * exp (eta L ω * (z - ω / 2)) = 1 := by
    rw [← exp_add]; simp
  linear_combination exp (-(eta L ω * (z - ω / 2))) * h - sigma L (z - ω) * this

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# Quasi-periodicity of `ζ` at every point

`zeta_add_eta` proves `ζ(z + ω) = ζ(z) + η(ω)` off the lattice. Here we extend it to all `z`,
including the lattice points, where Lean's junk value of the series is the regular part
`lim_{w → l} (ζ(w) - 1/(w - l))`. The tool is `zetaExcept l₀`, the `ζ`-series with the
`l₀`-term removed, which is holomorphic at `l₀`.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/-- The `ζ`-series with the `l₀`-term removed. -/
def zetaExcept (l₀ : L.lattice) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l = l₀ then 0 else zetaSummand l z

lemma hasSumLocallyUniformly_zetaExcept (l₀ : L.lattice) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ if l = l₀ then 0 else zetaSummand l z)
      (zetaExcept L l₀) := by
  refine PeriodPair.hasSumLocallyUniformly_aux L (u := fun r l ↦ 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    _ (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · rw [norm_zero]; positivity
  · exact zetaSummand_bound r hr s hs l h

lemma zeta_eq_zetaExcept_add (l₀ : L.lattice) (z : ℂ) :
    zeta L z = zetaExcept L l₀ z + zetaSummand l₀ z := by
  have h := ((hasSumLocallyUniformly_zetaExcept L l₀).hasSum (x := z)).add
    (hasSum_ite_eq l₀ (zetaSummand l₀ z))
  refine (hasSum_zeta L z).unique ?_
  convert h using 1
  funext l
  by_cases hl : l = l₀
  · simp [hl]
  · simp [hl]

lemma continuousAt_zetaExcept (l₀ : L.lattice) : ContinuousAt (zetaExcept L l₀) l₀ := by
  have hU : IsOpen (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := L.isOpen_compl_lattice_sdiff
  have hd : DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := by
    refine (hasSumLocallyUniformly_zetaExcept L l₀).tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) hU
    intro x hx
    split_ifs with hl
    · exact differentiableWithinAt_const _
    · have hxl : x - l ≠ 0 := by
        intro e
        have hxe : x = l := sub_eq_zero.mp e
        apply hx
        refine ⟨hxe ▸ l.2, ?_⟩
        rw [Set.mem_singleton_iff, hxe]
        exact fun h' ↦ hl (Subtype.ext h')
      exact (hasDerivAt_zetaSummand l x hxl).differentiableAt.differentiableWithinAt
  exact ((hd _ (by simp)).differentiableAt (hU.mem_nhds (by simp))).continuousAt

/-- **Quasi-periodicity of `ζ`** at every point (including lattice points, with Lean's junk
values): `ζ(z + ω) = ζ(z) + η(ω)` for `ω ∈ Λ`. -/
theorem zeta_add {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    zeta L (z + ω) = zeta L z + eta L ω := by
  by_cases hz : z ∉ L.lattice
  · exact zeta_add_eta L hω hz
  replace hz := not_not.mp hz
  set l₀ : L.lattice := ⟨z, hz⟩
  set l₁ : L.lattice := ⟨z + ω, add_mem hz hω⟩
  let G : ℂ → ℂ := fun w ↦ zetaExcept L l₁ (w + ω) - zetaExcept L l₀ w +
    (1 / (z + ω) + (w + ω) / (z + ω) ^ 2 - 1 / z - w / z ^ 2) - eta L ω
  have hG : ∀ w, zeta L (w + ω) - zeta L w - eta L ω = G w := by
    intro w
    rw [zeta_eq_zetaExcept_add L l₁ (w + ω), zeta_eq_zetaExcept_add L l₀ w]
    simp only [G, zetaSummand, l₀, l₁]
    rw [show w + ω - (z + ω) = w - z by ring]
    ring
  have hc : ContinuousAt G z := by
    have h1 : ContinuousAt (fun w ↦ zetaExcept L l₁ (w + ω)) z :=
      (continuousAt_zetaExcept L l₁).comp (f := fun w ↦ w + ω) (continuousAt_id.add_const ω)
    have h2 : ContinuousAt (zetaExcept L l₀) z := continuousAt_zetaExcept L l₀
    exact ((h1.sub h2).add (by fun_prop)).sub continuousAt_const
  have hev : G =ᶠ[𝓝[≠] z] fun _ ↦ 0 := by
    have := L.compl_lattice_sdiff_singleton_mem_nhds z
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with w hw hwz
    have hw' : w ∉ L.lattice := fun h ↦ hw ⟨h, hwz⟩
    rw [← hG, zeta_add_eta L hω hw']
    ring
  have hlim : Tendsto G (𝓝[≠] z) (𝓝 (G z)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : G z = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  have := hG z
  rw [h0] at this
  linear_combination this

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# The boundary integral of `1/z` over a rectangle centred at `0`

`LSG.Weierstrass.rectIntegral F z w` is the (counterclockwise) boundary integral of `F` over the
rectangle with opposite corners `z, w`, in the form used by Mathlib's Cauchy–Goursat theorem
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

* `LSG.Weierstrass.rectIntegral_inv`: for `a, b > 0`, the boundary integral of `z⁻¹` over
  `[-a, a] × [-b, b]` is `2πi`. Proof: explicit antiderivatives (branches of `log`) on the four
  sides, then `arg`-bookkeeping.
-/

open Complex MeasureTheory intervalIntegral Set
open scoped Real ComplexConjugate Interval

noncomputable section

namespace LSG.Weierstrass

/-- The counterclockwise boundary integral of `F` over the rectangle with corners `z`, `w`
(Mathlib's normalisation). -/
def rectIntegral (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))

/-- Cauchy–Goursat on a rectangle, in terms of `rectIntegral`. -/
lemma rectIntegral_eq_zero {F : ℂ → ℂ} {z w : ℂ}
    (H : DifferentiableOn ℂ F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : rectIntegral F z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w H

lemma intervalIntegrable_comp {F : ℂ → ℂ} {s t : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (hF : ∀ x ∈ [[s, t]], ContinuousAt F (g x)) :
    IntervalIntegrable (fun x => F (g x)) volume s t :=
  ContinuousOn.intervalIntegrable fun x hx => ((hF x hx).comp hg.continuousAt).continuousWithinAt

/-- Additivity of `rectIntegral`, given continuity on the four sides. -/
lemma rectIntegral_add {F₁ F₂ : ℂ → ℂ} {z w : ℂ}
    (h₁ : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F₁ p)
    (h₂ : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F₂ p) :
    rectIntegral (fun p => F₁ p + F₂ p) z w = rectIntegral F₁ z w + rectIntegral F₂ z w := by
  have hz : z.im ∈ [[z.im, w.im]] := left_mem_uIcc
  have hw : w.im ∈ [[z.im, w.im]] := right_mem_uIcc
  have hz' : z.re ∈ [[z.re, w.re]] := left_mem_uIcc
  have hw' : w.re ∈ [[z.re, w.re]] := right_mem_uIcc
  have hor : ∀ (F : ℂ → ℂ), (∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F p) →
      ∀ c ∈ ({z.im, w.im} : Set ℝ),
      IntervalIntegrable (fun x : ℝ => F (x + c * I)) volume z.re w.re := by
    intro F hF c hc
    refine intervalIntegrable_comp (g := fun x : ℝ => (x : ℂ) + c * I) (by fun_prop) ?_
    intro x hx
    rcases hc with rfl | rfl
    · exact hF _ (by simp [mem_reProdIm, hx, hz]) (by simp)
    · exact hF _ (by simp [mem_reProdIm, hx, hw]) (by simp)
  have ver : ∀ (F : ℂ → ℂ), (∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F p) →
      ∀ c ∈ ({z.re, w.re} : Set ℝ),
      IntervalIntegrable (fun y : ℝ => F (c + y * I)) volume z.im w.im := by
    intro F hF c hc
    refine intervalIntegrable_comp (g := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop) ?_
    intro y hy
    rcases hc with rfl | rfl
    · exact hF _ (by simp [mem_reProdIm, hy, hz']) (by simp)
    · exact hF _ (by simp [mem_reProdIm, hy, hw']) (by simp)
  unfold rectIntegral
  rw [integral_add (hor F₁ h₁ _ (by simp)) (hor F₂ h₂ _ (by simp)),
    integral_add (hor F₁ h₁ _ (by simp)) (hor F₂ h₂ _ (by simp)),
    integral_add (ver F₁ h₁ _ (by simp)) (ver F₂ h₂ _ (by simp)),
    integral_add (ver F₁ h₁ _ (by simp)) (ver F₂ h₂ _ (by simp))]
  simp only [smul_add]
  ring

/- ### Antiderivatives -/

lemma hasDerivAt_log_line {c d : ℂ} {x : ℝ} (h : c + x * d ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => log (c + t * d)) ((c + x * d)⁻¹ * d) x := by
  have h1 : HasDerivAt (fun w : ℂ => log (c + w * d)) ((c + x * d)⁻¹ * d) (x : ℂ) := by
    have := (hasDerivAt_log h).comp (x : ℂ) (((hasDerivAt_id (x : ℂ)).mul_const d).const_add c)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal

lemma integral_inv_line {c d : ℂ} {s t : ℝ} (hd : d ≠ 0)
    (h : ∀ x ∈ [[s, t]], c + x * d ∈ slitPlane) :
    ∫ x : ℝ in s..t, (c + x * d)⁻¹ = d⁻¹ * (log (c + t * d) - log (c + s * d)) := by
  have hcont : ∀ x ∈ [[s, t]], c + x * d ≠ 0 := fun x hx => slitPlane_ne_zero (h x hx)
  have := integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_log_line (h x hx))
    (ContinuousOn.intervalIntegrable (u := fun x : ℝ => (c + x * d)⁻¹ * d) (by
      refine ContinuousOn.mul ?_ continuousOn_const
      exact ContinuousOn.inv₀ (by fun_prop) hcont))
  rw [intervalIntegral.integral_mul_const] at this
  rw [← this, mul_comm _ d, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- The boundary integral of `z⁻¹` over `[-a, a] × [-b, b]` is `2πi`. -/
theorem rectIntegral_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    rectIntegral (fun z => z⁻¹) ⟨-a, -b⟩ ⟨a, b⟩ = 2 * π * I := by
  unfold rectIntegral
  simp only
  -- bottom and top: `c + x * 1` with `c = ± b i`
  have hB : ∫ x : ℝ in (-a)..a, ((x : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹ =
      log (((-b : ℝ) : ℂ) * I + a) - log (((-b : ℝ) : ℂ) * I + (-a : ℝ)) := by
    have := integral_inv_line (c := ((-b : ℝ) : ℂ) * I) (d := 1) (s := -a) (t := a) one_ne_zero
      (fun x _ => by rw [mem_slitPlane_iff]; right; simp; linarith)
    simpa [add_comm] using this
  have hT : ∫ x : ℝ in (-a)..a, ((x : ℂ) + (b : ℂ) * I)⁻¹ =
      log ((b : ℂ) * I + a) - log ((b : ℂ) * I + (-a : ℝ)) := by
    have := integral_inv_line (c := (b : ℂ) * I) (d := 1) (s := -a) (t := a) one_ne_zero
      (fun x _ => by rw [mem_slitPlane_iff]; right; simp; linarith)
    simpa [add_comm] using this
  have hR : ∫ y : ℝ in (-b)..b, ((a : ℂ) + y * I)⁻¹ =
      I⁻¹ * (log ((a : ℂ) + b * I) - log ((a : ℂ) + (-b : ℝ) * I)) :=
    integral_inv_line I_ne_zero (fun x _ => by rw [mem_slitPlane_iff]; left; simpa using ha)
  have hL : ∫ y : ℝ in (-b)..b, (((-a : ℝ) : ℂ) + y * I)⁻¹ =
      I⁻¹ * (log ((a : ℂ) + (-b : ℝ) * I) - log ((a : ℂ) + b * I)) := by
    have := integral_inv_line (c := (a : ℂ)) (d := -I) (s := -b) (t := b) (neg_ne_zero.mpr I_ne_zero)
      (fun x _ => by rw [mem_slitPlane_iff]; left; simpa using ha)
    have e : ∀ y : ℝ, (((-a : ℝ) : ℂ) + y * I)⁻¹ = -((a : ℂ) + y * -I)⁻¹ := by
      intro y; rw [← inv_neg]; congr 1; push_cast; ring
    simp_rw [e, intervalIntegral.integral_neg, this]
    push_cast
    rw [inv_neg]
    ring_nf
  rw [hB, hT, hR, hL]
  -- now the `arg` bookkeeping, with `p = a + b i`
  set p : ℂ := (a : ℂ) + b * I with hp
  have hpre : p.re = a := by simp [hp]
  have hpim : p.im = b := by simp [hp]
  have e1 : ((-b : ℝ) : ℂ) * I + a = conj p := by
    apply Complex.ext <;> simp [hp]
  have e2 : ((-b : ℝ) : ℂ) * I + (-a : ℝ) = -p := by
    apply Complex.ext <;> simp [hp]
  have e3 : (b : ℂ) * I + a = p := by rw [hp]; ring
  have e4 : (b : ℂ) * I + (-a : ℝ) = -conj p := by
    apply Complex.ext <;> simp [hp]
  have e5 : (a : ℂ) + (-b : ℝ) * I = conj p := by
    apply Complex.ext <;> simp [hp]
  rw [e1, e2, e3, e4, e5]
  have hargp : arg p ≠ π := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.2, hpim]
  have harg1 : arg (conj p) = -arg p := by rw [arg_conj, ite_eq_right_iff.mpr (fun h => absurd h hargp)]
  have harg2 : arg (-p) = arg p - π := arg_neg_eq_arg_sub_pi_of_im_pos (by rw [hpim]; exact hb)
  have harg3 : arg (-conj p) = -arg p + π := by
    rw [arg_neg_eq_arg_add_pi_of_im_neg (by simp [hpim, hb]), harg1]
  have hn1 : ‖conj p‖ = ‖p‖ := Complex.norm_conj p
  have hn2 : ‖-p‖ = ‖p‖ := norm_neg p
  have hn3 : ‖-conj p‖ = ‖p‖ := by rw [norm_neg, hn1]
  have key : log (-conj p) - log (-p) + log p - log (conj p) = 2 * π * I := by
    apply Complex.ext
    · simp only [sub_re, add_re, log_re, hn1, hn2, hn3]
      simp
    · simp only [sub_im, add_im, log_im, harg1, harg2, harg3]
      simp
      ring
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
  linear_combination key

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# Basic facts about `℘` for a `PeriodPair`

* `LSG.Weierstrass.hasDerivAt_derivWeierstrassP` : `℘'' = 6 ℘² - g₂ / 2` off the lattice.
* Half periods: `℘'(ω/2) = 0`, `4 e³ - g₂ e - g₃ = 0` for `e = ℘(ω/2)`, algebraicity of `e`,
  translates `ω/2 + kω`.
* `LSG.Weierstrass.exists_primitive` : every nonzero period is `m • ω₀` with `ω₀/2 ∉ Λ`.
* Algebraic independence of `(z, ℘ z)` and of `(℘ z, exp (2πi z / ω))` over any field
  `K → ℂ`.
-/

open Complex Filter Topology PeriodPair Real

namespace LSG.Weierstrass

variable (L : PeriodPair)

/- ### Generalities on the lattice -/

lemma intCast_mul_mem {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℤ) : (k : ℂ) * ω ∈ L.lattice := by
  simpa [zsmul_eq_mul] using L.lattice.smul_mem k hω

lemma natCast_mul_mem {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℕ) : (k : ℂ) * ω ∈ L.lattice := by
  simpa using (intCast_mul_mem L) hω k

lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0

lemma ω₂_ne_zero : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1

/-- Integer coordinates with respect to `ω₁, ω₂` are unique. -/
lemma int_coords_eq {a b c d : ℤ} (h : (a : ℂ) * L.ω₁ + b * L.ω₂ = c * L.ω₁ + d * L.ω₂) :
    a = c ∧ b = d := by
  have := LinearIndependent.pair_iff.mp L.indep ((a : ℝ) - c) ((b : ℝ) - d)
    (by simp only [Complex.real_smul]; push_cast; linear_combination h)
  constructor
  · have h1 := this.1; rw [sub_eq_zero] at h1; exact_mod_cast h1
  · have h2 := this.2; rw [sub_eq_zero] at h2; exact_mod_cast h2

lemma lattice_countable : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + p.2 * L.ω₂) := by
    intro x hx
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hx
    exact ⟨(m, n), h⟩
  exact (Set.countable_range _).mono this

lemma isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
  ((lattice_countable L).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

lemma isOpen_compl_lattice : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl

lemma add_mem_lattice_iff {z ω : ℂ} (hω : ω ∈ L.lattice) : z + ω ∈ L.lattice ↔ z ∈ L.lattice :=
  L.lattice.add_mem_iff_left hω

/- ### `℘` is unbounded (near `0`) -/

/-- `℘` takes arbitrarily large values off the lattice. -/
lemma exists_norm_weierstrassP_gt (M : ℝ) : ∃ z, z ∉ L.lattice ∧ M < ‖℘[L] z‖ := by
  have hc : ContinuousAt (L.weierstrassPExcept 0) 0 :=
    (L.analyticAt_weierstrassPExcept 0).continuousAt
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.mp (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  set B := ‖(L.weierstrassPExcept 0) 0‖ + 1
  have hB : 0 ≤ B := by positivity
  set A := |M| + B + 2
  have hA : 2 ≤ A := by have := abs_nonneg M; linarith
  set t : ℝ := min (min δ₁ δ₂ / 2) (1 / A)
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : t < min δ₁ δ₂ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htA : t ≤ 1 / A := min_le_right _ _
  have htn : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht0]
  have ht1 : ‖(t : ℂ)‖ < δ₁ := by rw [htn]; exact lt_of_lt_of_le htδ (min_le_left _ _)
  have ht2 : ‖(t : ℂ)‖ < δ₂ := by rw [htn]; exact lt_of_lt_of_le htδ (min_le_right _ _)
  have hnot : (t : ℂ) ∉ L.lattice := by
    have := hball (show (t : ℂ) ∈ Metric.ball 0 δ₂ by
      rw [Metric.mem_ball, dist_zero_right]; exact ht2)
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not] at this
    intro hm
    have := this hm
    exact (ne_of_gt ht0) (by exact_mod_cast this)
  refine ⟨t, hnot, ?_⟩
  have hbd : ‖(L.weierstrassPExcept 0) t‖ ≤ B := by
    have := hb (x := (t : ℂ)) (by rw [dist_zero_right]; exact ht1)
    rw [dist_eq_norm] at this
    have := norm_le_norm_add_norm_sub' (L.weierstrassPExcept 0 t) (L.weierstrassPExcept 0 0)
    simp only [B]
    linarith
  have hdecomp : ℘[L] t = (L.weierstrassPExcept 0) t + 1 / (t : ℂ) ^ 2 := by
    rw [← L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩]; simp
  have hinv : A ≤ 1 / t ^ 2 := by
    have h1 : A * t ≤ 1 := by rw [le_div_iff₀ (by linarith)] at htA; linarith
    have ht1' : t ≤ 1 := by
      have : 1 / A ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hnorm : ‖1 / (t : ℂ) ^ 2‖ = 1 / t ^ 2 := by
    simp [norm_pow, abs_of_pos ht0]
  rw [hdecomp]
  have := norm_sub_norm_le (1 / (t : ℂ) ^ 2) (-(L.weierstrassPExcept 0) t)
  rw [sub_neg_eq_add, norm_neg, hnorm, add_comm] at this
  have hM := le_abs_self M
  linarith

lemma infinite_image_weierstrassP : (℘[L] '' (L.lattice : Set ℂ)ᶜ).Infinite := by
  intro hfin
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hfin.isBounded
  obtain ⟨z, hz, hM⟩ := (exists_norm_weierstrassP_gt L) R
  exact absurd (hR _ ⟨z, hz, rfl⟩) (not_le.mpr hM)

/- ### `℘'' = 6 ℘² - g₂/2` -/

lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘[L] (℘'[L] z) z := by
  have := (L.differentiableOn_weierstrassP.differentiableAt
    ((isOpen_compl_lattice L).mem_nhds hz)).hasDerivAt
  rwa [L.deriv_weierstrassP] at this

lemma differentiableAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ ℘'[L] z :=
  L.differentiableOn_derivWeierstrassP.differentiableAt ((isOpen_compl_lattice L).mem_nhds hz)

/-- `℘'` does not vanish identically near any point off the lattice. -/
lemma derivWeierstrassP_not_eventually_zero {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) :
    ¬ (℘'[L] =ᶠ[𝓝 z₀] 0) := by
  intro h
  have hEq := L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_compl_lattice L) hz₀ h
  have hconst : ∀ x ∈ (L.lattice : Set ℂ)ᶜ, ℘[L] x = ℘[L] z₀ := fun x hx =>
    (isOpen_compl_lattice L).is_const_of_deriv_eq_zero (isPreconnected_compl_lattice L)
      L.differentiableOn_weierstrassP (by intro y hy; simp [hEq hy]) hx hz₀
  obtain ⟨z, hz, hM⟩ := (exists_norm_weierstrassP_gt L) ‖℘[L] z₀‖
  rw [hconst z hz] at hM
  exact lt_irrefl _ hM

/-- **`℘'' = 6 ℘² - g₂ / 2`** off the lattice. -/
theorem hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  -- the product identity `℘' (℘'' - 6℘² + g₂/2) = 0` off the lattice
  have key : ∀ w, w ∉ L.lattice →
      ℘'[L] w * (deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2)) = 0 := by
    intro w hw
    have h1 : HasDerivAt (fun x => ℘'[L] x ^ 2) (↑2 * ℘'[L] w ^ (2 - 1) * deriv ℘'[L] w) w :=
      ((differentiableAt_derivWeierstrassP L) hw).hasDerivAt.pow 2
    have hP := (hasDerivAt_weierstrassP L) hw
    have h2 : HasDerivAt (fun x => 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃)
        (4 * (↑3 * ℘[L] w ^ (3 - 1) * ℘'[L] w) - L.g₂ * ℘'[L] w) w :=
      (((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃
    have hev : (fun x => ℘'[L] x ^ 2) =ᶠ[𝓝 w] (fun x => 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃) := by
      filter_upwards [(isOpen_compl_lattice L).mem_nhds hw] with x hx
      exact L.derivWeierstrassP_sq x hx
    have := h1.unique (h2.congr_of_eventuallyEq hev)
    norm_num at this
    linear_combination this / 2
  set F : ℂ → ℂ := fun w => deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2) with hF
  have hFa : AnalyticAt ℂ F z := by
    have h1 := (L.analyticOnNhd_derivWeierstrassP z hz).deriv
    have h2 := L.analyticOnNhd_weierstrassP z hz
    exact h1.sub ((analyticAt_const.mul (h2.pow 2)).sub analyticAt_const)
  have hne : ∀ᶠ w in 𝓝[≠] z, ℘'[L] w ≠ 0 :=
    (L.analyticOnNhd_derivWeierstrassP z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      ((derivWeierstrassP_not_eventually_zero L) hz)
  have hU : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice :=
    nhdsWithin_le_nhds ((isOpen_compl_lattice L).mem_nhds hz)
  have hfreq : ∃ᶠ w in 𝓝[≠] z, F w = 0 := by
    refine (hne.and hU).mono ?_ |>.frequently
    rintro w ⟨h1, h2⟩
    exact (mul_eq_zero.mp (key w h2)).resolve_left h1
  have hFz : F z = 0 := (hFa.frequently_zero_iff_eventually_zero.mp hfreq).self_of_nhds
  have hd := ((differentiableAt_derivWeierstrassP L) hz).hasDerivAt
  rwa [sub_eq_zero.mp hFz] at hd

/- ### Half periods -/

/-- `℘'(ω/2) = 0` for every period `ω` (if `ω/2 ∈ Λ` this is the junk value). -/
lemma derivWeierstrassP_half {ω : ℂ} (hω : ω ∈ L.lattice) : ℘'[L] (ω / 2) = 0 := by
  have h1 : ℘'[L] (ω / 2) = ℘'[L] (-(ω / 2)) := by
    rw [← L.derivWeierstrassP_sub_coe (ω / 2) ⟨ω, hω⟩]
    congr 1; ring
  rw [L.derivWeierstrassP_neg] at h1
  linear_combination h1 / 2

/-- `e = ℘(ω/2)` is a root of `4X³ - g₂X - g₃`. -/
lemma weierstrassP_half_cubic {ω : ℂ} (hω : ω ∈ L.lattice) (h2 : ω / 2 ∉ L.lattice) :
    4 * ℘[L] (ω / 2) ^ 3 - L.g₂ * ℘[L] (ω / 2) - L.g₃ = 0 := by
  have := L.derivWeierstrassP_sq (ω / 2) h2
  rw [(derivWeierstrassP_half L) hω] at this
  linear_combination -this

/-- If `g₂, g₃` are algebraic, so is `℘(ω/2)`. -/
lemma isAlgebraic_weierstrassP_half (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {ω : ℂ} (hω : ω ∈ L.lattice) (h2 : ω / 2 ∉ L.lattice) : IsAlgebraic ℚ (℘[L] (ω / 2)) := by
  set F := IntermediateField.adjoin ℚ ({L.g₂, L.g₃} : Set ℂ)
  have : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl)
    · exact hg₂.isIntegral
    · exact hg₃.isIntegral)
  have m₂ : L.g₂ ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have m₃ : L.g₃ ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have hF : IsAlgebraic F (℘[L] (ω / 2)) := by
    refine ⟨4 * Polynomial.X ^ 3 - Polynomial.C ⟨L.g₂, m₂⟩ * Polynomial.X
      - Polynomial.C ⟨L.g₃, m₃⟩, ?_, ?_⟩
    · intro hp
      have := congrArg (Polynomial.coeff · 3) hp
      simp at this
    · simpa [map_ofNat] using (weierstrassP_half_cubic L) hω h2
  exact hF.restrictScalars (R := ℚ)

lemma half_add_mul_notMem {ω : ℂ} (hω : ω ∈ L.lattice) (h2 : ω / 2 ∉ L.lattice) (k : ℤ) :
    ω / 2 + k * ω ∉ L.lattice := by
  rwa [(add_mem_lattice_iff L) ((intCast_mul_mem L) hω k)]

lemma weierstrassP_half_add_mul {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℤ) :
    ℘[L] (ω / 2 + k * ω) = ℘[L] (ω / 2) :=
  L.weierstrassP_add_coe (ω / 2) ⟨_, (intCast_mul_mem L) hω k⟩

lemma derivWeierstrassP_half_add_mul {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℤ) :
    ℘'[L] (ω / 2 + k * ω) = 0 := by
  rw [L.derivWeierstrassP_add_coe (ω / 2) ⟨_, intCast_mul_mem L hω k⟩,
    derivWeierstrassP_half L hω]

/- ### Primitive periods -/

/-- Every nonzero period is a positive integer multiple of a period `ω₀` with `ω₀/2 ∉ Λ`. -/
theorem exists_primitive {ω : ℂ} (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) :
    ∃ (m : ℕ) (ω₀ : ℂ), 1 ≤ m ∧ ω₀ ∈ L.lattice ∧ ω = (m : ℂ) * ω₀ ∧ ω₀ / 2 ∉ L.lattice := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hω
  set g := Int.gcd a b with hg
  have hg0 : 0 < g := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h
    exact h0 (by simp [← hab])
  set a' := a / g
  set b' := b / g
  have ha : a = a' * g := (Int.ediv_mul_cancel (Int.gcd_dvd_left a b)).symm
  have hb : b = b' * g := (Int.ediv_mul_cancel (Int.gcd_dvd_right a b)).symm
  have hcop : Int.gcd a' b' = 1 := Int.gcd_div_gcd_div_gcd hg0
  refine ⟨g, a' * L.ω₁ + b' * L.ω₂, hg0, ?_, ?_, ?_⟩
  · exact add_mem (intCast_mul_mem L L.ω₁_mem_lattice a') (intCast_mul_mem L L.ω₂_mem_lattice b')
  · rw [← hab, ha, hb]; push_cast; ring
  · intro hmem
    obtain ⟨c, d, hcd⟩ := PeriodPair.mem_lattice.mp hmem
    have := int_coords_eq L (show ((2 * c : ℤ) : ℂ) * L.ω₁ + ((2 * d : ℤ) : ℂ) * L.ω₂ =
      (a' : ℂ) * L.ω₁ + (b' : ℂ) * L.ω₂ by push_cast; linear_combination 2 * hcd)
    have h2 : (2 : ℤ) ∣ (Int.gcd a' b' : ℤ) :=
      Int.dvd_coe_gcd ⟨c, this.1.symm⟩ ⟨d, this.2.symm⟩
    rw [hcop] at h2
    norm_num at h2

/- ### Algebraic independence -/

section AlgIndep

variable {K : Type*} [Field K] [Algebra K ℂ]

lemma mvPoly_one_eq_zero (c : MvPolynomial (Fin 1) ℂ) {Y : Set ℂ} (hY : Y.Infinite)
    (h : ∀ y ∈ Y, MvPolynomial.eval ![y] c = 0) : c = 0 := by
  obtain ⟨t, ht, htc⟩ := hY.exists_subset_card_eq (c.degreeOf 0 + 1)
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset c (fun _ => t) ?_ ?_
  · intro i
    fin_cases i
    simp [htc]
  · intro x hx
    have hx' : x = ![x 0] := by ext i; fin_cases i; rfl
    rw [hx']
    exact h _ (ht (hx 0))

/-- A polynomial in two variables vanishing on infinitely many horizontal lines' worth of
infinitely many points is zero: if for infinitely many `y` the polynomial `P(·, y)` has infinitely
many roots, then `P = 0`. -/
theorem mvPoly_eq_zero_of_infinite_fibres (P : MvPolynomial (Fin 2) K) {Y : Set ℂ}
    (hY : Y.Infinite) (hfib : ∀ y ∈ Y, {x : ℂ | MvPolynomial.aeval ![x, y] P = 0}.Infinite) :
    P = 0 := by
  set P' := MvPolynomial.map (algebraMap K ℂ) P
  have hP' : ∀ v : Fin 2 → ℂ, MvPolynomial.aeval v P = MvPolynomial.eval v P' := by
    intro v
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  suffices hP0 : P' = 0 by
    exact MvPolynomial.map_injective _ (algebraMap K ℂ).injective (hP0.trans (map_zero _).symm)
  set Q := MvPolynomial.finSuccEquiv ℂ 1 P'
  have hQy : ∀ y ∈ Y, Polynomial.map (MvPolynomial.eval ![y]) Q = 0 := by
    intro y hy
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (hfib y hy).mono ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [hP'] at hx
    rw [Polynomial.IsRoot, ← MvPolynomial.eval_eq_eval_mv_eval']
    exact hx
  have hQ : Q = 0 := by
    refine Polynomial.ext fun j => ?_
    simp only [Polynomial.coeff_zero]
    refine mvPoly_one_eq_zero _ hY fun y hy => ?_
    have := congrArg (Polynomial.coeff · j) (hQy y hy)
    simpa [Polynomial.coeff_map] using this
  exact (MvPolynomial.finSuccEquiv ℂ 1).injective (hQ.trans (map_zero _).symm)

/-- Variant of `mvPoly_eq_zero_of_infinite_fibres` with the roles of the variables swapped. -/
theorem mvPoly_eq_zero_of_infinite_fibres' (P : MvPolynomial (Fin 2) K) {X : Set ℂ}
    (hX : X.Infinite) (hfib : ∀ x ∈ X, {y : ℂ | MvPolynomial.aeval ![x, y] P = 0}.Infinite) :
    P = 0 := by
  set σ := Equiv.swap (0 : Fin 2) 1
  have hsw : ∀ x y : ℂ, MvPolynomial.aeval ![y, x] (MvPolynomial.rename σ P) =
      MvPolynomial.aeval ![x, y] P := by
    intro x y
    rw [MvPolynomial.aeval_rename]
    congr 2
    funext i
    fin_cases i <;> rfl
  have : MvPolynomial.rename σ P = 0 :=
    mvPoly_eq_zero_of_infinite_fibres _ hX fun x hx => by simpa [hsw] using hfib x hx
  exact MvPolynomial.rename_injective σ σ.injective (by rw [this, map_zero])

/-- **`z` and `℘(z)` are algebraically independent** over any field `K → ℂ`. -/
theorem algIndep_id_weierstrassP (P : MvPolynomial (Fin 2) K)
    (hP : ∀ z, z ∉ L.lattice → MvPolynomial.aeval ![z, ℘[L] z] P = 0) : P = 0 := by
  refine mvPoly_eq_zero_of_infinite_fibres P (infinite_image_weierstrassP L) ?_
  rintro _ ⟨z₀, hz₀, rfl⟩
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => z₀ + k * L.ω₁) ?_ ?_
  · intro k l hkl
    have := (ω₁_ne_zero L)
    simp only [add_right_inj] at hkl
    exact_mod_cast mul_right_cancel₀ this hkl
  · intro k
    have hmem := (intCast_mul_mem L) L.ω₁_mem_lattice k
    have hz : z₀ + k * L.ω₁ ∉ L.lattice := by rwa [(add_mem_lattice_iff L) hmem]
    have := hP _ hz
    rwa [L.weierstrassP_add_coe z₀ ⟨_, hmem⟩] at this

/-- For `ω ≠ 0` there is a period `ω'` with `‖exp (2πi ω'/ω)‖ ≠ 1`. -/
lemma exists_norm_exp_ne_one {ω : ℂ} (h0 : ω ≠ 0) :
    ∃ ω' ∈ L.lattice, ‖cexp (2 * π * I / ω * ω')‖ ≠ 1 := by
  by_contra! H
  have him : ∀ ω' ∈ L.lattice, (ω' / ω).im = 0 := by
    intro ω' hω'
    have := H ω' hω'
    rw [Complex.norm_exp, Real.exp_eq_one_iff] at this
    have he : 2 * π * I / ω * ω' = 2 * π * I * (ω' / ω) := by field_simp
    rw [he] at this
    generalize ω' / ω = u at this ⊢
    have hu : (2 * (π : ℂ) * I * u).re = -(2 * π) * u.im := by simp [Complex.mul_re]
    rw [hu] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by have := Real.pi_pos; linarith)
    · exact h
  have hre : ∀ ω' ∈ L.lattice, ω' = ((ω' / ω).re : ℂ) * ω := by
    intro ω' hω'
    have : ((ω' / ω).re : ℂ) = ω' / ω := Complex.ext (by simp) (by simp [him ω' hω'])
    rw [this]; field_simp
  obtain ⟨s, hs1⟩ : ∃ s : ℝ, L.ω₁ = s * ω := ⟨_, hre _ L.ω₁_mem_lattice⟩
  obtain ⟨t, ht2⟩ : ∃ t : ℝ, L.ω₂ = t * ω := ⟨_, hre _ L.ω₂_mem_lattice⟩
  have := LinearIndependent.pair_iff.mp L.indep t (-s)
    (by simp only [Complex.real_smul]; rw [hs1, ht2]; push_cast; ring)
  have hs : s = 0 := by simpa using this.2
  exact (ω₁_ne_zero L) (by rw [hs1, hs]; simp)

/-- **`℘(z)` and `exp (2πi z/ω)` are algebraically independent** over any field `K → ℂ`, for
a nonzero period `ω`. -/
theorem algIndep_weierstrassP_exp {ω : ℂ} (h0 : ω ≠ 0) (P : MvPolynomial (Fin 2) K)
    (hP : ∀ z, z ∉ L.lattice → MvPolynomial.aeval ![℘[L] z, cexp (2 * π * I / ω * z)] P = 0) :
    P = 0 := by
  obtain ⟨ω', hω', hc⟩ := (exists_norm_exp_ne_one L) h0
  set c := cexp (2 * π * I / ω * ω')
  refine mvPoly_eq_zero_of_infinite_fibres' P (infinite_image_weierstrassP L) ?_
  rintro _ ⟨z₀, hz₀, rfl⟩
  have hexp : ∀ k : ℕ,
      cexp (2 * π * I / ω * (z₀ + k * ω')) = cexp (2 * π * I / ω * z₀) * c ^ k := by
    intro k
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; ring
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => cexp (2 * π * I / ω * (z₀ + k * ω'))) ?_ ?_
  · intro k l hkl
    simp only [hexp] at hkl
    have h' := congrArg norm hkl
    simp only [norm_mul, norm_pow] at h'
    have hn : ‖cexp (2 * π * I / ω * z₀)‖ ≠ 0 := by simp [Complex.exp_ne_zero]
    have h'' := mul_left_cancel₀ hn h'
    exact pow_right_injective₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _)) hc h''
  · intro k
    have hmem := (natCast_mul_mem L) hω' k
    have hz : z₀ + k * ω' ∉ L.lattice := by rwa [(add_mem_lattice_iff L) hmem]
    have := hP _ hz
    rwa [L.weierstrassP_add_coe z₀ ⟨_, hmem⟩] at this

end AlgIndep

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# Legendre's relation

For a period pair `L` with quasi-periods `η₁ = η(ω₁)`, `η₂ = η(ω₂)`:

  `η₁ ω₂ - η₂ ω₁ = 2πi`   if `Im (ω₂/ω₁) > 0`,   and `= -2πi` if `Im (ω₂/ω₁) < 0`.

(Mathlib's `PeriodPair` carries no orientation assumption.)

## Proof
Let `(α, β)` be a basis of `Λ` with `τ = β/α` in the upper half-plane. The function
`f(z) = α ζ(αz) - α η(α) z` is `1`-periodic, satisfies `f(z + τ) = f(z) + c` with
`c = α η(β) - η(α) β`, and `f(z) = G(z) + 1/z` with `G` holomorphic near the closed rectangle
`R = [-1/2, 1/2] × [-Im τ/2, Im τ/2]` (`G` is built from the `ζ`-series with the `0`-term removed).
On `∂R`: the vertical sides cancel by periodicity, and the top side is the bottom side shifted by
`τ` (up to a horizontal translation, harmless by periodicity), so `∮_{∂R} f = -c`. On the other hand
`∮ G = 0` (Cauchy–Goursat on a rectangle) and `∮ 1/z = 2πi` (`rectIntegral_inv`). Only rectangle
integrals appear; no residue theorem or parallelogram contour is needed.
-/

open Module Filter Complex MeasureTheory intervalIntegral Set
open scoped Topology Real Interval

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

lemma differentiableOn_zetaExcept (l₀ : L.lattice) :
    DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := by
  refine (hasSumLocallyUniformly_zetaExcept L l₀).tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) L.isOpen_compl_lattice_sdiff
  intro x hx
  split_ifs with hl
  · exact differentiableWithinAt_const _
  · have hxl : x - l ≠ 0 := by
      intro e
      have hxe : x = l := sub_eq_zero.mp e
      apply hx
      refine ⟨hxe ▸ l.2, ?_⟩
      rw [Set.mem_singleton_iff, hxe]
      exact fun h' ↦ hl (Subtype.ext h')
    exact (hasDerivAt_zetaSummand l x hxl).differentiableAt.differentiableWithinAt

lemma differentiableAt_zetaExcept_zero {w : ℂ} (hw : w ∉ L.lattice ∨ w = 0) :
    DifferentiableAt ℂ (zetaExcept L 0) w := by
  refine (differentiableOn_zetaExcept L 0 w ?_).differentiableAt
    (L.isOpen_compl_lattice_sdiff.mem_nhds ?_) <;>
  · rintro ⟨h1, h2⟩
    rcases hw with hw | hw
    · exact hw h1
    · exact h2 (by simp [hw])

/-- `ζ(w) = ζ₀(w) + 1/w` for every `w`, where `ζ₀` is the series without the `0`-term. -/
lemma zeta_eq_zetaExcept_zero_add (w : ℂ) : zeta L w = zetaExcept L 0 w + w⁻¹ := by
  rw [zeta_eq_zetaExcept_add L 0 w]
  simp [zetaSummand]

/-- **Legendre's relation** for a basis `(α, β)` of the lattice with `Im (β/α) > 0`. -/
theorem legendre_of_basis {α β : ℂ} (hα : α ∈ L.lattice) (hβ : β ∈ L.lattice)
    (hspan : ∀ l ∈ L.lattice, ∃ m n : ℤ, l = m * α + n * β) (him : 0 < (β / α).im) :
    eta L α * β - eta L β * α = 2 * π * I := by
  have hα0 : α ≠ 0 := by rintro rfl; simp at him
  set τ := β / α with hτ
  set b := τ.im / 2 with hb_def
  have hb : 0 < b := by positivity
  have hατ : α * τ = β := by rw [hτ]; field_simp
  set c := α * eta L β - eta L α * β with hc
  set f : ℂ → ℂ := fun z => α * zeta L (α * z) - α * eta L α * z with hf
  set G : ℂ → ℂ := fun z => α * zetaExcept L 0 (α * z) - α * eta L α * z with hG
  have hfG : f = fun z => G z + z⁻¹ := by
    funext z
    simp only [hf, hG]
    rw [zeta_eq_zetaExcept_zero_add, mul_inv, mul_add, mul_inv_cancel_left₀ hα0]
    ring
  have hf1 : ∀ z, f (z + 1) = f z := by
    intro z
    simp only [hf]
    rw [mul_add, mul_one, zeta_add L hα]
    ring
  have hfτ : ∀ z, f (z + τ) = f z + c := by
    intro z
    simp only [hf, hc]
    rw [mul_add, hατ, zeta_add L hβ, mul_add (α * eta L α), ← hατ]
    ring
  -- the lattice points `α z` with `z` in the closed rectangle
  have hmem : ∀ z : ℂ, α * z ∈ L.lattice → ∃ m n : ℤ, z = m + n * τ := by
    intro z hz
    obtain ⟨m, n, hmn⟩ := hspan _ hz
    refine ⟨m, n, ?_⟩
    rw [hτ]
    field_simp
    linear_combination hmn
  have hpole : ∀ z : ℂ, z.re ∈ Icc (-1/2 : ℝ) (1/2) → z.im ∈ Icc (-b) b →
      α * z ∈ L.lattice → z = 0 := by
    intro z hre him' hz
    obtain ⟨m, n, rfl⟩ := hmem z hz
    have hi : ((m : ℂ) + n * τ).im = n * (2 * b) := by
      simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add]
      rw [hb_def]; ring
    rw [hi] at him'
    have hn : n = 0 := by
      have h1 : (n : ℝ) * (2 * b) ≤ b := him'.2
      have h2 : -b ≤ (n : ℝ) * (2 * b) := him'.1
      have h3 : (n : ℝ) < 1 := by nlinarith
      have h4 : (-1 : ℝ) < n := by nlinarith
      have : n < 1 := by exact_mod_cast h3
      have : -1 < n := by exact_mod_cast h4
      omega
    subst hn
    have hr : ((m : ℂ) + ((0 : ℤ) : ℂ) * τ).re = m := by simp
    rw [hr] at hre
    have hm : m = 0 := by
      have h3 : (m : ℝ) < 1 := by linarith [hre.2]
      have h4 : (-1 : ℝ) < m := by linarith [hre.1]
      have : m < 1 := by exact_mod_cast h3
      have : -1 < m := by exact_mod_cast h4
      omega
    subst hm
    simp
  -- the horizontal lines `Im z = ± b` avoid the poles
  have hline : ∀ z : ℂ, (z.im = -b ∨ z.im = b) → α * z ∉ L.lattice := by
    intro z hz hzm
    obtain ⟨m, n, rfl⟩ := hmem z hzm
    have hi : ((m : ℂ) + n * τ).im = n * (2 * b) := by
      simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add]
      rw [hb_def]; ring
    rw [hi] at hz
    rcases hz with hz | hz
    · have : (n : ℝ) * 2 = -1 := by nlinarith
      have : n * 2 = -1 := by exact_mod_cast this
      omega
    · have : (n : ℝ) * 2 = 1 := by nlinarith
      have : n * 2 = 1 := by exact_mod_cast this
      omega
  have hfcont : ∀ z : ℂ, α * z ∉ L.lattice → ContinuousAt f z := by
    intro z hz
    have h1 : DifferentiableAt ℂ (zeta L) (α * z) :=
      (differentiableOn_zeta L _ hz).differentiableAt ((isOpen_compl_coe_lattice L).mem_nhds hz)
    have : DifferentiableAt ℂ f z := by
      simp only [hf]
      fun_prop
    exact this.continuousAt
  -- `G` is holomorphic on the closed rectangle
  set z₀ : ℂ := ⟨-1/2, -b⟩
  set w₀ : ℂ := ⟨1/2, b⟩
  have hrect : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]],
      p.re ∈ Icc (-1/2 : ℝ) (1/2) ∧ p.im ∈ Icc (-b) b := by
    intro p hp
    rw [mem_reProdIm] at hp
    simp only [z₀, w₀] at hp
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by linarith)] at hp
    exact hp
  have hGd : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]], DifferentiableAt ℂ G p := by
    intro p hp
    obtain ⟨h1, h2⟩ := hrect p hp
    have hz : α * p ∉ L.lattice ∨ α * p = 0 := by
      by_cases h : α * p ∈ L.lattice
      · right; rw [hpole p h1 h2 h, mul_zero]
      · left; exact h
    have := differentiableAt_zetaExcept_zero L hz
    simp only [hG]
    fun_prop
  have hGzero : rectIntegral G z₀ w₀ = 0 :=
    rectIntegral_eq_zero fun p hp => (hGd p hp).differentiableWithinAt
  -- `1/z` on the boundary
  have hinv : rectIntegral (fun z => z⁻¹) z₀ w₀ = 2 * π * I := by
    have := rectIntegral_inv (a := 1/2) (b := b) (by norm_num) hb
    convert this using 2
    simp [z₀]
    norm_num
  have hbd_ne : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]],
      (p.re = z₀.re ∨ p.re = w₀.re ∨ p.im = z₀.im ∨ p.im = w₀.im) → p ≠ 0 := by
    rintro p - h rfl
    simp only [zero_re, zero_im, z₀, w₀] at h
    rcases h with h | h | h | h <;> linarith
  have hsplit : rectIntegral f z₀ w₀ = 2 * π * I := by
    rw [hfG, rectIntegral_add (fun p hp _ => (hGd p hp).continuousAt)
      (fun p hp hb' => continuousAt_inv₀ (hbd_ne p hp hb')), hGzero, hinv, zero_add]
  -- periodicity computation of the boundary integral of `f`
  have hver : (∫ y : ℝ in z₀.im..w₀.im, f (w₀.re + y * I)) =
      ∫ y : ℝ in z₀.im..w₀.im, f (z₀.re + y * I) := by
    refine integral_congr fun y _ => ?_
    rw [← hf1 ((z₀.re : ℂ) + y * I)]
    congr 1
    simp only [z₀, w₀]
    push_cast
    ring
  set g : ℝ → ℂ := fun x => f (x + z₀.im * I) with hg
  have hgper : Function.Periodic g 1 := by
    intro x
    simp only [hg]
    rw [← hf1 ((x : ℂ) + z₀.im * I)]
    congr 1
    push_cast
    ring
  have hgcont : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have : ContinuousAt f ((x : ℂ) + z₀.im * I) :=
      hfcont _ (hline _ (Or.inl (by simp [z₀])))
    exact this.comp (g := f) (f := fun x : ℝ => (x : ℂ) + z₀.im * I) (by fun_prop)
  have htop : (∫ x : ℝ in z₀.re..w₀.re, f (x + w₀.im * I)) =
      (∫ x : ℝ in z₀.re..w₀.re, f (x + z₀.im * I)) + c := by
    have e : ∀ x : ℝ, f (x + w₀.im * I) = g (x - τ.re) + c := by
      intro x
      simp only [hg]
      rw [← hfτ]
      congr 1
      apply Complex.ext
      · simp [z₀, w₀, hb_def]
      · simp [z₀, w₀, hb_def]
        ring
    simp_rw [e]
    have hint : IntervalIntegrable (fun x => g (x - τ.re)) volume z₀.re w₀.re :=
      (hgcont.comp (continuous_sub_right τ.re)).intervalIntegrable _ _
    rw [integral_add hint _root_.intervalIntegrable_const, integral_comp_sub_right, intervalIntegral.integral_const]
    have hw : w₀.re - τ.re = (z₀.re - τ.re) + 1 := by simp [z₀, w₀]; ring
    have hw' : w₀.re = z₀.re + 1 := by simp [z₀, w₀]; norm_num
    rw [hw, hgper.intervalIntegral_add_eq (z₀.re - τ.re) z₀.re, ← hw']
    have h1 : w₀.re - z₀.re = 1 := by simp [z₀, w₀]; norm_num
    rw [h1, one_smul]
  have hper : rectIntegral f z₀ w₀ = -c := by
    unfold rectIntegral
    rw [hver, htop]
    ring
  rw [hper] at hsplit
  rw [hc] at hsplit
  linear_combination hsplit

lemma im_div_ne_zero : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h
  have h1 := ω₁_ne_zero L
  set t := (L.ω₂ / L.ω₁).re
  have ht : L.ω₂ / L.ω₁ = (t : ℂ) := Complex.ext (by simp [t]) (by simp [h])
  have hω : L.ω₂ = t * L.ω₁ := by rw [← ht]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep t (-1) (by
    simp only [Complex.real_smul, hω]; push_cast; ring)
  norm_num at this

/-- **Legendre's relation**, positively oriented case. -/
theorem legendre_of_im_pos (h : 0 < (L.ω₂ / L.ω₁).im) :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ = 2 * π * I :=
  legendre_of_basis L L.ω₁_mem_lattice L.ω₂_mem_lattice
    (fun l hl => by obtain ⟨m, n, h⟩ := mem_lattice.mp hl; exact ⟨m, n, h.symm⟩) h

/-- **Legendre's relation**, negatively oriented case. -/
theorem legendre_of_im_neg (h : (L.ω₂ / L.ω₁).im < 0) :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ = -(2 * π * I) := by
  have h' : 0 < (L.ω₁ / L.ω₂).im := by
    have : L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ := by rw [inv_div]
    rw [this, inv_im, neg_div]
    apply neg_pos.mpr
    apply div_neg_of_neg_of_pos h
    rw [normSq_pos]
    intro h0
    rw [h0] at h
    simp at h
  have := legendre_of_basis L L.ω₂_mem_lattice L.ω₁_mem_lattice
    (fun l hl => by
      obtain ⟨m, n, h⟩ := mem_lattice.mp hl
      exact ⟨n, m, by rw [← h]; ring⟩) h'
  linear_combination -this

/-- **Legendre's relation**: `η₁ ω₂ - η₂ ω₁ = ±2πi`, with sign `+` iff `Im (ω₂/ω₁) > 0`. -/
theorem legendre :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ =
      2 * π * I * (if 0 < (L.ω₂ / L.ω₁).im then 1 else -1) := by
  split_ifs with h
  · rw [mul_one]; exact legendre_of_im_pos L h
  · rw [legendre_of_im_neg L (lt_of_le_of_ne (not_lt.mp h) (im_div_ne_zero L))]
    ring

lemma legendre_ne_zero : eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ ≠ 0 := by
  rw [legendre]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  split_ifs <;> simp [hπ, I_ne_zero]

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# Elliptic functions with at most one simple pole are constant

This file provides the "Liouville + removable singularities" toolkit for elliptic functions,
without any residue theorem.

* `LSG.Weierstrass.LocBdd f s`: `f` is bounded on a punctured neighbourhood of `s`.
* `LSG.Weierstrass.Discr S`: every point has a punctured neighbourhood disjoint from `S`.
* `exists_differentiable_extension`: a function holomorphic off a discrete set `S` and bounded
  near each point of `S` agrees off `S` with an entire function (Riemann's removable singularity
  theorem, applied at every point of `S`).
* `eq_linear_of_add_sub_const`: an entire function whose `Λ`-differences are constant is linear
  (its derivative is entire and periodic, hence constant by Liouville).
* `eq_const_of_simple_pole` (**sum of residues**): an elliptic function whose only possible poles
  are simple poles at `a + Λ` is constant. Proof (the `ζ`-subtraction trick): with `r` the residue
  at `a`, `g = f - r ζ(· - a)` extends to an entire function with constant `Λ`-differences
  `-r η(ω)`, hence `g = αz + β`; so `α ω = -r η(ω)` on `Λ`, and Legendre's relation
  (`η₁ω₂ - η₂ω₁ ≠ 0`) forces `r = 0`, then `α = 0`.
-/

open Module Filter Complex Set
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

/-- `f` is bounded on a punctured neighbourhood of `s`. -/
def LocBdd (f : ℂ → ℂ) (s : ℂ) : Prop := ∃ M : ℝ, ∀ᶠ u in 𝓝[≠] s, ‖f u‖ ≤ M

/-- Every point has a punctured neighbourhood disjoint from `S`. -/
def Discr (S : Set ℂ) : Prop := ∀ x, ∀ᶠ y in 𝓝[≠] x, y ∉ S

/- ### Local boundedness -/

section LocBdd

variable {f g : ℂ → ℂ} {s : ℂ}

lemma LocBdd.of_continuousAt (h : ContinuousAt f s) : LocBdd f s := by
  refine ⟨‖f s‖ + 1, nhdsWithin_le_nhds ?_⟩
  exact (h.norm.eventually (Iio_mem_nhds (lt_add_one _))).mono fun u hu => le_of_lt hu

lemma LocBdd.congr (h : LocBdd f s) (hfg : ∀ᶠ u in 𝓝[≠] s, f u = g u) : LocBdd g s := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, (hM.and hfg).mono fun u hu => hu.2 ▸ hu.1⟩

lemma LocBdd.add (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u + g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, (hM.and hN).mono fun u hu => (norm_add_le _ _).trans (add_le_add hu.1 hu.2)⟩

lemma LocBdd.sub (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u - g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, (hM.and hN).mono fun u hu => (norm_sub_le _ _).trans (add_le_add hu.1 hu.2)⟩

lemma LocBdd.mul (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u * g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨max M 0 * max N 0, (hM.and hN).mono fun u hu => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hu.1.trans (le_max_left _ _)) (hu.2.trans (le_max_left _ _)) (norm_nonneg _)
    (le_max_right _ _)

lemma tendsto_sub_nhdsNE (s ω : ℂ) : Tendsto (fun u => u - ω) (𝓝[≠] (s + ω)) (𝓝[≠] s) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := (continuous_sub_right ω).tendsto (s + ω)
    simp only [add_sub_cancel_right] at this
    exact this.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    simp only [mem_compl_iff, mem_singleton_iff] at hu ⊢
    intro h
    exact hu (by rw [← h]; ring)

lemma tendsto_neg_nhdsNE (s : ℂ) : Tendsto (fun u => -u) (𝓝[≠] (-s)) (𝓝[≠] s) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := continuous_neg.tendsto (-s)
    simp only [neg_neg] at this
    exact this.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    simp only [mem_compl_iff, mem_singleton_iff] at hu ⊢
    intro h
    exact hu (by rw [← h]; ring)

lemma LocBdd.of_periodic {ω : ℂ} (hper : ∀ u, f (u + ω) = f u) (h : LocBdd f s) :
    LocBdd f (s + ω) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ((tendsto_sub_nhdsNE s ω).eventually hM).mono fun u hu => ?_⟩
  have := hper (u - ω)
  rw [sub_add_cancel] at this
  rw [this]; exact hu

lemma LocBdd.of_even (heven : ∀ u, f (-u) = f u) (h : LocBdd f s) : LocBdd f (-s) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ((tendsto_neg_nhdsNE s).eventually hM).mono fun u hu => ?_⟩
  have := heven u
  rwa [this] at hu

end LocBdd

/-- Two functions continuous at `u` that agree on a punctured neighbourhood agree at `u`. -/
lemma eq_of_eventuallyEq_nhdsNE {F₁ F₂ : ℂ → ℂ} {u : ℂ} (h₁ : ContinuousAt F₁ u)
    (h₂ : ContinuousAt F₂ u) (h : ∀ᶠ v in 𝓝[≠] u, F₁ v = F₂ v) : F₁ u = F₂ u :=
  tendsto_nhds_unique ((h₁.tendsto.mono_left nhdsWithin_le_nhds).congr' h)
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)

/- ### Discrete sets -/

section Discr

variable (L : PeriodPair)

lemma Discr.union {S T : Set ℂ} (hS : Discr S) (hT : Discr T) : Discr (S ∪ T) := fun x =>
  ((hS x).and (hT x)).mono fun _ hy h => h.elim hy.1 hy.2

lemma Discr.eventually_nhds {S : Set ℂ} (hS : Discr S) {x : ℂ} (hx : x ∉ S) :
    ∀ᶠ y in 𝓝 x, y ∉ S := by
  have := hS x
  rw [eventually_nhdsWithin_iff] at this
  filter_upwards [this] with y hy
  by_cases h : y = x
  · rw [h]; exact hx
  · exact hy h

lemma Discr.exists_notMem {S : Set ℂ} (hS : Discr S) : ∃ u, u ∉ S := (hS 0).exists

/-- `{u | c u + d ∈ Λ}` is discrete for `c ≠ 0`. -/
lemma discr_affine {c : ℂ} (hc : c ≠ 0) (d : ℂ) : Discr {u | c * u + d ∈ L.lattice} := by
  intro x
  have h1 := L.compl_lattice_sdiff_singleton_mem_nhds (c * x + d)
  have h2 : Tendsto (fun u => c * u + d) (𝓝 x) (𝓝 (c * x + d)) :=
    ((continuous_const.mul continuous_id).add continuous_const).tendsto x
  filter_upwards [nhdsWithin_le_nhds (h2.eventually h1), self_mem_nhdsWithin] with u hu hux
  intro hmem
  apply hu
  refine ⟨hmem, fun h => hux ?_⟩
  simp only [mem_singleton_iff, add_left_inj] at h ⊢
  exact mul_left_cancel₀ hc h

lemma discr_sub (a : ℂ) : Discr {u | u - a ∈ L.lattice} := by
  have := discr_affine L one_ne_zero (-a)
  simpa [sub_eq_add_neg] using this

lemma discr_add (a : ℂ) : Discr {u | u + a ∈ L.lattice} := by
  have := discr_affine L one_ne_zero a
  simpa using this

end Discr

/- ### Removable singularities and Liouville -/

/-- A function holomorphic off a discrete set `S` and bounded near every point of `S` agrees
off `S` with an entire function. -/
theorem exists_differentiable_extension {f : ℂ → ℂ} {S : Set ℂ} (hS : Discr S)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x) (hb : ∀ s ∈ S, LocBdd f s) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x ∉ S, F x = f x := by
  classical
  set F : ℂ → ℂ := fun x => if x ∈ S then limUnder (𝓝[≠] x) f else f x with hF
  refine ⟨F, fun x => ?_, fun x hx => by simp [hF, hx]⟩
  by_cases hx : x ∈ S
  · obtain ⟨M, hM⟩ := hb x hx
    have h := (hS x).and hM
    rw [eventually_nhdsWithin_iff] at h
    set U := {y | y ≠ x → y ∉ S ∧ ‖f y‖ ≤ M}
    have hU : U ∈ 𝓝 x := h
    have hdU : DifferentiableOn ℂ f (U \ {x}) := fun y hy =>
      (hd y (hy.1 hy.2).1).differentiableWithinAt
    have hbU : BddAbove (norm ∘ f '' (U \ {x})) :=
      ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (hy.1 hy.2).2⟩
    have hD := (Complex.differentiableOn_update_limUnder_of_bddAbove hU hdU hbU).differentiableAt hU
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [hU] with y hy
    by_cases hyx : y = x
    · subst hyx; simp [hF, hx]
    · simp [hF, (hy hyx).1, Function.update_of_ne hyx]
  · refine (hd x hx).congr_of_eventuallyEq ?_
    filter_upwards [hS.eventually_nhds hx] with y hy
    simp [hF, hy]

variable (L : PeriodPair)

/-- An entire function with constant `Λ`-differences is linear. -/
theorem eq_linear_of_add_sub_const {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∀ ω ∈ L.lattice, ∃ c, ∀ u, F (u + ω) = F u + c) :
    ∃ α β : ℂ, ∀ u, F u = α * u + β := by
  have hd : Differentiable ℂ (deriv F) := hF.deriv
  have hper : ∀ u ω, ω ∈ L.lattice → deriv F (u + ω) = deriv F u := by
    intro u ω hω
    obtain ⟨c, hc⟩ := h ω hω
    have e : (fun v => F (v + ω)) = fun v => F v + c := funext hc
    have h1 : deriv (fun v => F (v + ω)) u = deriv F (u + ω) := deriv_comp_add_const F ω u
    rw [← h1, e, deriv_add_const]
  have hc := IsZLattice.isCompact_range_of_periodic L.lattice _ hd.continuous
    (fun z w hw => hper z w hw)
  set α := deriv F 0
  have hconst : ∀ u, deriv F u = α := fun u => hd.apply_eq_apply_of_bounded hc.isBounded u 0
  refine ⟨α, F 0, fun u => ?_⟩
  have hG : Differentiable ℂ (fun v => F v - α * v) := hF.sub (differentiable_id.const_mul α)
  have hG' : ∀ v, deriv (fun v => F v - α * v) v = 0 := by
    intro v
    have : HasDerivAt (fun v => F v - α * v) (deriv F v - α * 1) v :=
      (hF v).hasDerivAt.sub ((hasDerivAt_id' v).const_mul α)
    rw [this.deriv, hconst v]
    ring
  have := is_const_of_deriv_eq_zero hG hG' u 0
  simp only [mul_zero, sub_zero] at this
  linear_combination this

/-- **Sum of residues, one simple pole.** An elliptic function whose only possible poles are
simple poles along `a + Λ` is constant (off its singular set). -/
theorem eq_const_of_simple_pole {f : ℂ → ℂ} {S : Set ℂ} (a : ℂ) (hS : Discr S)
    (hSinv : ∀ u ∈ S, ∀ ω ∈ L.lattice, u + ω ∈ S)
    (hper : ∀ u ∉ S, ∀ ω ∈ L.lattice, f (u + ω) = f u)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x)
    (hb : ∀ s ∈ S, s - a ∉ L.lattice → LocBdd f s)
    (ha : LocBdd (fun u => (u - a) * f u) a) :
    ∃ C, ∀ u ∉ S, f u = C := by
  set A : Set ℂ := {u | u - a ∈ L.lattice} with hA_def
  set S' := S ∪ A with hS'_def
  have hS' : Discr S' := hS.union (discr_sub L a)
  have hS'inv : ∀ u ∉ S', ∀ ω ∈ L.lattice, u + ω ∉ S' := by
    intro u hu ω hω h
    apply hu
    rcases h with h | h
    · left
      have := hSinv _ h (-ω) (neg_mem hω)
      rwa [add_neg_cancel_right] at this
    · right
      change u + ω - a ∈ L.lattice at h
      change u - a ∈ L.lattice
      have := sub_mem h hω
      rwa [show u + ω - a - ω = u - a by ring] at this
  -- the residue at `a`
  set h : ℂ → ℂ := fun u => (u - a) * f u with hh_def
  obtain ⟨M, hM⟩ := ha
  have hh := (hS a).and hM
  rw [eventually_nhdsWithin_iff] at hh
  set U := {y | y ≠ a → y ∉ S ∧ ‖h y‖ ≤ M}
  have hU : U ∈ 𝓝 a := hh
  have hdU : DifferentiableOn ℂ h (U \ {a}) := fun y hy =>
    ((differentiableAt_id.sub_const a).mul (hd y (hy.1 hy.2).1)).differentiableWithinAt
  have hbU : BddAbove (norm ∘ h '' (U \ {a})) :=
    ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (hy.1 hy.2).2⟩
  set r := limUnder (𝓝[≠] a) h
  set H := Function.update h a r with hH_def
  have hH : DifferentiableAt ℂ H a :=
    (Complex.differentiableOn_update_limUnder_of_bddAbove hU hdU hbU).differentiableAt hU
  have hdsl : ContinuousAt (dslope H a) a := continuousAt_dslope_same.mpr hH
  have hloc : ∀ u, u ≠ a → f u - r * (u - a)⁻¹ = dslope H a u := by
    intro u hu
    have hu' : u - a ≠ 0 := sub_ne_zero.mpr hu
    rw [dslope_of_ne _ hu, slope_def_field]
    simp only [hH_def, Function.update_of_ne hu, Function.update_self, hh_def]
    field_simp
  -- subtract `r ζ(· - a)`
  set g : ℂ → ℂ := fun u => f u - r * zeta L (u - a) with hg_def
  have hzc : ∀ x, x - a ∉ L.lattice → DifferentiableAt ℂ (fun u => zeta L (u - a)) x := by
    intro x hx
    have := (differentiableOn_zeta L _ hx).differentiableAt
      ((isOpen_compl_coe_lattice L).mem_nhds hx)
    exact this.comp x (differentiableAt_id.sub_const a)
  have hgd : ∀ x ∉ S', DifferentiableAt ℂ g x := by
    intro x hx
    have h1 : x ∉ S := fun h => hx (Or.inl h)
    have h2 : x - a ∉ L.lattice := fun h => hx (Or.inr h)
    exact (hd x h1).sub ((hzc x h2).const_mul r)
  have hgper : ∀ u ∉ S', ∀ ω ∈ L.lattice, g (u + ω) = g u + -(r * eta L ω) := by
    intro u hu ω hω
    have h1 : u ∉ S := fun h => hu (Or.inl h)
    simp only [hg_def]
    rw [hper u h1 ω hω, show u + ω - a = (u - a) + ω by ring, zeta_add L hω]
    ring
  have hga : LocBdd g a := by
    have hc : ContinuousAt (fun u => dslope H a u - r * zetaExcept L 0 (u - a)) a := by
      have h1 : ContinuousAt (fun u => zetaExcept L 0 (u - a)) a := by
        have := (differentiableAt_zetaExcept_zero L (w := a - a) (Or.inr (sub_self a))).continuousAt
        exact this.comp (f := fun u => u - a) (continuousAt_id.sub continuousAt_const)
      exact hdsl.sub (continuousAt_const.mul h1)
    refine (LocBdd.of_continuousAt hc).congr ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [← hloc u hu]
    simp only [hg_def]
    rw [zeta_eq_zetaExcept_zero_add]
    ring
  have hgb : ∀ s ∈ S', LocBdd g s := by
    intro s hs
    by_cases hsa : s - a ∈ L.lattice
    · obtain ⟨M', hM'⟩ := hga
      refine ⟨M' + ‖r * eta L (s - a)‖, ?_⟩
      have h1 := (tendsto_sub_nhdsNE a (s - a)).eventually (hM'.and (hS' a))
      rw [show a + (s - a) = s by ring] at h1
      filter_upwards [h1] with u hu
      have := hgper (u - (s - a)) hu.2 (s - a) hsa
      rw [sub_add_cancel] at this
      rw [this]
      exact (norm_add_le _ _).trans (by rw [norm_neg]; linarith [hu.1])
    · have hsS : s ∈ S := hs.resolve_right hsa
      exact (hb s hsS hsa).sub
        (LocBdd.of_continuousAt (continuousAt_const.mul (hzc s hsa).continuousAt))
  obtain ⟨G, hGd, hGg⟩ := exists_differentiable_extension hS' hgd hgb
  have hGper : ∀ ω ∈ L.lattice, ∃ c, ∀ u, G (u + ω) = G u + c := by
    intro ω hω
    refine ⟨-(r * eta L ω), fun u => ?_⟩
    refine eq_of_eventuallyEq_nhdsNE (F₁ := fun u => G (u + ω)) (F₂ := fun u => G u + -(r * eta L ω))
      ((hGd _).continuousAt.comp (continuousAt_id.add continuousAt_const))
      ((hGd u).continuousAt.add continuousAt_const) ?_
    filter_upwards [hS' u] with v hv
    rw [hGg _ (hS'inv v hv ω hω), hGg v hv, hgper v hv ω hω]
  obtain ⟨α, β, hαβ⟩ := eq_linear_of_add_sub_const L hGd hGper
  obtain ⟨u₀, hu₀⟩ := hS'.exists_notMem
  have hαω : ∀ ω ∈ L.lattice, α * ω = -(r * eta L ω) := by
    intro ω hω
    have h1 := hgper u₀ hu₀ ω hω
    rw [← hGg _ (hS'inv u₀ hu₀ ω hω), ← hGg u₀ hu₀, hαβ, hαβ] at h1
    linear_combination h1
  have hr : r = 0 := by
    have h1 := hαω _ L.ω₁_mem_lattice
    have h2 := hαω _ L.ω₂_mem_lattice
    have hl := legendre_ne_zero L
    have : r * (eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁) = 0 := by
      linear_combination L.ω₂ * h1 - L.ω₁ * h2
    exact (mul_eq_zero.mp this).resolve_right hl
  have hα : α = 0 := by
    have h1 := hαω _ L.ω₁_mem_lattice
    rw [hr, zero_mul, neg_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right (ω₁_ne_zero L)
  have hfG : ∀ v ∉ S', f v = β := by
    intro v hv
    have := hGg v hv
    rw [hαβ, hα, zero_mul, zero_add] at this
    simp only [hg_def, hr, zero_mul, sub_zero] at this
    exact this.symm
  refine ⟨β, fun u hu => ?_⟩
  by_cases hua : u - a ∈ L.lattice
  · refine eq_of_eventuallyEq_nhdsNE (F₂ := fun _ => β) (hd u hu).continuousAt continuousAt_const ?_
    filter_upwards [hS' u] with v hv
    exact hfG v hv
  · exact hfG u (fun h => h.elim hu hua)

/-- An elliptic function bounded near each point of its (discrete) singular set is constant. -/
theorem eq_const_of_locBdd {f : ℂ → ℂ} {S : Set ℂ} (hS : Discr S)
    (hSinv : ∀ u ∈ S, ∀ ω ∈ L.lattice, u + ω ∈ S)
    (hper : ∀ u ∉ S, ∀ ω ∈ L.lattice, f (u + ω) = f u)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x) (hb : ∀ s ∈ S, LocBdd f s) :
    ∃ C, ∀ u ∉ S, f u = C := by
  by_cases h0 : (0 : ℂ) ∈ S
  · exact eq_const_of_simple_pole L 0 hS hSinv hper hd (fun s hs _ => hb s hs)
      ((LocBdd.of_continuousAt (f := fun u => u - 0) (by fun_prop)).mul (hb 0 h0))
  · exact eq_const_of_simple_pole L 0 hS hSinv hper hd (fun s hs _ => hb s hs)
      (LocBdd.of_continuousAt (((continuous_id.sub continuous_const).continuousAt).mul
        (hd 0 h0).continuousAt))

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# Quasi-periodicity of `σ` for every period

For every `ω ∈ Λ`,
`σ(z + ω) = ε(ω) · exp (η(ω) (z + ω/2)) · σ(z)`, with `ε(ω) = 1` if `ω/2 ∈ Λ` and `ε(ω) = -1`
otherwise.

The case `ω/2 ∉ Λ` is `sigma_add_of_half_notMem`. If `ω/2 ∈ Λ`, apply the formula for `ω/2`
twice (the signs cancel); the recursion terminates by strong induction on `|m| + |n|`,
`ω = m ω₁ + n ω₂`. No use of Legendre's relation is needed.

As a consequence the zeros of `σ` are simple: `σ'(ω) = ε(ω) exp (η(ω) ω/2) ≠ 0` for `ω ∈ Λ`.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

open scoped Classical in
/-- The sign `ε(ω)` in the quasi-periodicity of `σ`: `1` if `ω/2 ∈ Λ`, `-1` otherwise. -/
def sigmaSign (ω : ℂ) : ℂ := if ω / 2 ∈ L.lattice then 1 else -1

lemma sigmaSign_sq (ω : ℂ) : sigmaSign L ω ^ 2 = 1 := by
  unfold sigmaSign; split_ifs <;> norm_num

lemma sigmaSign_ne_zero (ω : ℂ) : sigmaSign L ω ≠ 0 := by
  unfold sigmaSign; split_ifs <;> norm_num

lemma sigmaSign_of_half_notMem {ω : ℂ} (h : ω / 2 ∉ L.lattice) : sigmaSign L ω = -1 := by
  simp [sigmaSign, h]

lemma sigmaSign_of_half_mem {ω : ℂ} (h : ω / 2 ∈ L.lattice) : sigmaSign L ω = 1 := by
  simp [sigmaSign, h]

/-- The doubling step: the formula for `ω'` implies the formula for `2ω'`. -/
lemma sigma_add_two_mul {ω' : ℂ} (hω' : ω' ∈ L.lattice)
    (ih : ∀ z, sigma L (z + ω') = sigmaSign L ω' * exp (eta L ω' * (z + ω' / 2)) * sigma L z)
    (z : ℂ) :
    sigma L (z + 2 * ω') = sigmaSign L (2 * ω') * exp (eta L (2 * ω') * (z + 2 * ω' / 2)) *
      sigma L z := by
  have h2 : (2 * ω') / 2 ∈ L.lattice := by simpa using hω'
  rw [sigmaSign_of_half_mem L h2, two_mul ω', eta_add L hω' hω',
    show z + (ω' + ω') = (z + ω') + ω' by ring, ih, ih]
  have hs := sigmaSign_sq L ω'
  have e : exp (eta L ω' * (z + ω' + ω' / 2)) * exp (eta L ω' * (z + ω' / 2)) =
      exp ((eta L ω' + eta L ω') * (z + (ω' + ω') / 2)) := by
    rw [← exp_add]; ring_nf
  linear_combination (exp (eta L ω' * (z + ω' + ω' / 2)) * exp (eta L ω' * (z + ω' / 2)) *
    sigma L z) * hs + sigma L z * e

/-- **Quasi-periodicity of `σ`.** For every `ω ∈ Λ`,
`σ(z + ω) = ε(ω) · exp (η(ω) (z + ω/2)) · σ(z)`. -/
theorem sigma_add {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    sigma L (z + ω) = sigmaSign L ω * exp (eta L ω * (z + ω / 2)) * sigma L z := by
  obtain ⟨m, n, rfl⟩ := mem_lattice.mp hω
  revert z
  induction h : m.natAbs + n.natAbs using Nat.strong_induction_on generalizing m n with
  | _ N ih =>
  intro z
  by_cases h2 : ((m : ℂ) * L.ω₁ + n * L.ω₂) / 2 ∈ L.lattice
  · obtain ⟨m', n', hmn⟩ := mem_lattice.mp h2
    -- coordinates of `ω/2` are half those of `ω`
    have hind := LinearIndependent.pair_iff.mp L.indep ((2 * m' - m : ℤ) : ℝ)
      ((2 * n' - n : ℤ) : ℝ) (by
        simp only [Complex.real_smul]
        push_cast
        linear_combination 2 * hmn)
    have hm : 2 * m' = m := by have := Int.cast_eq_zero.mp hind.1; omega
    have hn : 2 * n' = n := by have := Int.cast_eq_zero.mp hind.2; omega
    by_cases h0 : N = 0
    · have hm0 : m = 0 := by omega
      have hn0 : n = 0 := by omega
      subst hm0 hn0
      simp [sigmaSign]
    · have hlt : m'.natAbs + n'.natAbs < N := by omega
      have ih' := ih _ hlt m' n' (by rw [hmn]; exact h2) rfl
      have e : (m : ℂ) * L.ω₁ + n * L.ω₂ = 2 * ((m' : ℂ) * L.ω₁ + n' * L.ω₂) := by
        rw [← hm, ← hn]; push_cast; ring
      rw [e]
      exact sigma_add_two_mul L (by rw [hmn]; exact h2) ih' z
  · rw [sigmaSign_of_half_notMem L h2, sigma_add_of_half_notMem L hω h2 z]
    ring

/-- `σ'(ω) = ε(ω) exp (η(ω) ω/2)` for `ω ∈ Λ`. -/
lemma deriv_sigma_of_mem {ω : ℂ} (hω : ω ∈ L.lattice) :
    deriv (sigma L) ω = sigmaSign L ω * exp (eta L ω * (ω / 2)) := by
  have h1 : HasDerivAt (fun z ↦ sigma L (z + ω)) (deriv (sigma L) (0 + ω)) 0 :=
    (differentiable_sigma L (0 + ω)).hasDerivAt.comp_add_const 0 ω
  have hE : HasDerivAt (fun z ↦ exp (eta L ω * (z + ω / 2)))
      (exp (eta L ω * (0 + ω / 2)) * (eta L ω * 1)) 0 :=
    (((hasDerivAt_id' (0 : ℂ)).add_const (ω / 2)).const_mul (eta L ω)).cexp
  have h2 := ((hasDerivAt_const (0 : ℂ) (sigmaSign L ω)).mul hE).mul (hasDerivAt_sigma_zero L)
  have h3 : HasDerivAt (fun z ↦ sigma L (z + ω)) (((0 * exp (eta L ω * (0 + ω / 2)) +
      sigmaSign L ω * (exp (eta L ω * (0 + ω / 2)) * (eta L ω * 1))) * sigma L 0 +
      sigmaSign L ω * exp (eta L ω * (0 + ω / 2)) * 1)) 0 := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
    exact sigma_add L hω z
  have := h1.unique h3
  rw [zero_add] at this
  rw [this, sigma_zero, zero_add]
  ring

/-- The zeros of `σ` are simple. -/
lemma deriv_sigma_ne_zero_of_mem {ω : ℂ} (hω : ω ∈ L.lattice) : deriv (sigma L) ω ≠ 0 := by
  rw [deriv_sigma_of_mem L hω]
  exact mul_ne_zero (sigmaSign_ne_zero L ω) (exp_ne_zero _)

end LSG.Weierstrass

end

section

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-
# `℘` has degree two

For `z ∉ Λ` the elliptic function
`F(u) = (℘(u) - ℘(z)) σ(u)² / (σ(u - z) σ(u + z))`
has no poles except possibly a simple pole along `z + Λ` (when `2z ∈ Λ`, where `σ(u-z)σ(u+z)` has
a double zero but `℘ - ℘(z)` only a known simple one). By `eq_const_of_simple_pole` it is a
constant `C`, and `C ≠ 0` since `℘` is not constant. Hence

* `sigma_identity`: `(℘(u) - ℘(z)) σ(u)² = C σ(u - z) σ(u + z)` for `u ∉ Λ`, with `C ≠ 0`;
* `weierstrassP_eq_iff`: **`℘(w) = ℘(z) ↔ w ≡ ±z (mod Λ)`** for `z, w ∉ Λ`;
* `derivWeierstrassP_eq_zero_iff`: `℘'(z) = 0 ↔ 2z ∈ Λ` for `z ∉ Λ` (differentiate the identity
  at `u = z`: `℘'(z) σ(z)² = C σ(2z)`).
-/

open Module Filter Complex Set
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/- ### Small facts -/

lemma sigma_eq_mul_sigmaProd (u : ℂ) : sigma L u = u * sigmaProd L u := rfl

lemma continuous_sigma : Continuous (sigma L) := (differentiable_sigma L).continuous

lemma continuous_sigmaProd : Continuous (sigmaProd L) := (differentiable_sigmaProd L).continuous

lemma differentiableAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ ℘[L] z :=
  L.differentiableOn_weierstrassP.differentiableAt ((isOpen_compl_lattice L).mem_nhds hz)

lemma continuousAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : ContinuousAt ℘[L] z :=
  (differentiableAt_weierstrassP L hz).continuousAt

lemma continuousAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) : ContinuousAt ℘'[L] z :=
  (differentiableAt_derivWeierstrassP L hz).continuousAt

lemma weierstrassP_add_mem (u : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) : ℘[L] (u + ω) = ℘[L] u :=
  L.weierstrassP_add_coe u ⟨ω, hω⟩

lemma derivWeierstrassP_add_mem (u : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) :
    ℘'[L] (u + ω) = ℘'[L] u :=
  L.derivWeierstrassP_add_coe u ⟨ω, hω⟩

/-- `℘(u) = ℘₀(u) + 1/u²`, `℘₀` the series without the `0`-term. -/
lemma weierstrassP_eq_except_zero (u : ℂ) : ℘[L] u = L.weierstrassPExcept 0 u + 1 / u ^ 2 := by
  have := L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩ u
  simp only [sub_zero, div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at this
  rw [← this]

/-- `℘'(u) = ℘'₀(u) - 2/u³`. -/
lemma derivWeierstrassP_eq_except_zero (u : ℂ) : ℘'[L] u = L.derivWeierstrassPExcept 0 u - 2 / u ^ 3 := by
  have := L.derivWeierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ u
  simp only [sub_zero] at this
  rw [this]
  ring

lemma continuousAt_weierstrassPExcept_zero : ContinuousAt (L.weierstrassPExcept 0) 0 :=
  (L.analyticAt_weierstrassPExcept 0).continuousAt

lemma continuousAt_derivWeierstrassPExcept_zero : ContinuousAt (L.derivWeierstrassPExcept 0) 0 :=
  (L.analyticAt_derivWeierstrassPExcept 0).continuousAt

/-- `σ(u + ω) / σ(u)` is a nonvanishing multiplier. -/
lemma sigma_add' {ω : ℂ} (hω : ω ∈ L.lattice) (u : ℂ) :
    sigma L (u + ω) = (sigmaSign L ω * exp (eta L ω * (u + ω / 2))) * sigma L u :=
  sigma_add L hω u

lemma sigmaSign_mul_exp_ne_zero (ω v : ℂ) : sigmaSign L ω * exp v ≠ 0 :=
  mul_ne_zero (sigmaSign_ne_zero L ω) (exp_ne_zero v)

lemma exp_mul_exp_eq {e a b c : ℂ} (h : a + b = 2 * c) :
    exp (e * a) * exp (e * b) = exp (e * c) * exp (e * c) := by
  rw [← exp_add, ← exp_add]
  congr 1
  linear_combination e * h

/-- `dslope` form of a difference quotient. -/
lemma dslope_eq_div {f : ℂ → ℂ} {a u : ℂ} (hu : u ≠ a) :
    dslope f a u = (f u - f a) / (u - a) := by
  rw [dslope_of_ne _ hu, slope_def_field]

/- ### The function `F` -/

/-- `F(u) = (℘(u) - ℘(z)) σ(u)² / (σ(u - z) σ(u + z))`. -/
def degF (z u : ℂ) : ℂ :=
  (℘[L] u - ℘[L] z) * sigma L u ^ 2 / (sigma L (u - z) * sigma L (u + z))

lemma degF_add (z : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) (u : ℂ) :
    degF L z (u + ω) = degF L z u := by
  unfold degF
  rw [weierstrassP_add_mem L u hω, sigma_add' L hω u, show u + ω - z = (u - z) + ω by ring,
    sigma_add' L hω (u - z), show u + ω + z = (u + z) + ω by ring, sigma_add' L hω (u + z)]
  set s := sigmaSign L ω
  set e := eta L ω
  have hE := exp_mul_exp_eq (e := e) (a := u - z + ω / 2) (b := u + z + ω / 2) (c := u + ω / 2)
    (by ring)
  have hK : s * s * (exp (e * (u + ω / 2)) * exp (e * (u + ω / 2))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sigmaSign_ne_zero L ω) (sigmaSign_ne_zero L ω))
      (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _))
  rw [show s * exp (e * (u - z + ω / 2)) * sigma L (u - z) *
      (s * exp (e * (u + z + ω / 2)) * sigma L (u + z)) =
      sigma L (u - z) * sigma L (u + z) *
        (s * s * (exp (e * (u - z + ω / 2)) * exp (e * (u + z + ω / 2)))) by ring, hE,
    show (℘[L] u - ℘[L] z) * (s * exp (e * (u + ω / 2)) * sigma L u) ^ 2 =
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 *
        (s * s * (exp (e * (u + ω / 2)) * exp (e * (u + ω / 2)))) by ring,
    mul_div_mul_right _ _ hK]

lemma degF_neg (z u : ℂ) : degF L z (-u) = degF L z u := by
  unfold degF
  rw [weierstrassP_neg, sigma_neg, show -u - z = -(u + z) by ring, sigma_neg,
    show -u + z = -(u - z) by ring, sigma_neg]
  ring

/-- The singular set `Λ ∪ (z + Λ) ∪ (-z + Λ)`. -/
def degS (z : ℂ) : Set ℂ := {u | u ∈ L.lattice ∨ u - z ∈ L.lattice ∨ u + z ∈ L.lattice}

lemma discr_degS (z : ℂ) : Discr (degS L z) := by
  have h := ((discr_add L 0).union (discr_sub L z)).union (discr_add L z)
  convert h using 1
  ext u
  simp [degS, or_assoc]

lemma degS_add {z u ω : ℂ} (hu : u ∈ degS L z) (hω : ω ∈ L.lattice) : u + ω ∈ degS L z := by
  rcases hu with h | h | h
  · exact Or.inl (add_mem h hω)
  · right; left
    rw [show u + ω - z = (u - z) + ω by ring]; exact add_mem h hω
  · right; right
    rw [show u + ω + z = (u + z) + ω by ring]; exact add_mem h hω

lemma differentiableAt_degF {z x : ℂ} (hx : x ∉ degS L z) : DifferentiableAt ℂ (degF L z) x := by
  have h0 : x ∉ L.lattice := fun h => hx (Or.inl h)
  have h1 : x - z ∉ L.lattice := fun h => hx (Or.inr (Or.inl h))
  have h2 : x + z ∉ L.lattice := fun h => hx (Or.inr (Or.inr h))
  have hP := differentiableAt_weierstrassP L h0
  have hs := differentiable_sigma L
  unfold degF
  refine DifferentiableAt.div ?_ ?_ (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))
  · exact (hP.sub_const _).mul ((hs x).pow 2)
  · exact ((hs _).comp x (differentiableAt_id.sub_const z)).mul
      ((hs _).comp x (differentiableAt_id.add_const z))

/-- Near `0`: `F` is bounded. -/
lemma locBdd_degF_zero {z : ℂ} (hz : z ∉ L.lattice) : LocBdd (degF L z) 0 := by
  have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
  set g : ℂ → ℂ := fun u => (1 + u ^ 2 * L.weierstrassPExcept 0 u - u ^ 2 * ℘[L] z) * sigmaProd L u ^ 2 /
    (sigma L (u - z) * sigma L (u + z))
  have hc : ContinuousAt g 0 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact ((continuousAt_const.add ((continuousAt_id.pow 2).mul
        (continuousAt_weierstrassPExcept_zero L))).sub ((continuousAt_id.pow 2).mul
        continuousAt_const)).mul ((continuous_sigmaProd L).continuousAt.pow 2)
    · exact ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [zero_sub, zero_add]
      exact mul_ne_zero (sigma_ne_zero L hz') (sigma_ne_zero L hz)
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u ≠ 0 := hu
  simp only [g, degF, sigma_eq_mul_sigmaProd L u, weierstrassP_eq_except_zero L u]
  congr 1
  field_simp
  ring

/-- Near `z`, if `2z ∉ Λ`: `F` is bounded. -/
lemma locBdd_degF_self {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    LocBdd (degF L z) z := by
  set g : ℂ → ℂ := fun u => dslope ℘[L] z u * sigma L u ^ 2 /
    (sigmaProd L (u - z) * sigma L (u + z))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)).mul
        ((continuous_sigma L).continuousAt.pow 2)
    · exact ((continuous_sigmaProd L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [sub_self, sigmaProd_zero, one_mul]
      exact sigma_ne_zero L (by rwa [← two_mul])
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u - z ≠ 0 := sub_ne_zero.mpr hu
  simp only [g, degF, dslope_eq_div hu, sigma_eq_mul_sigmaProd L (u - z)]
  field_simp

/-- Near `z`, if `2z ∈ Λ`: `(u - z) F(u)` is bounded. -/
lemma locBdd_mul_degF_self_of_two_mul_mem {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∈ L.lattice) :
    LocBdd (fun u => (u - z) * degF L z u) z := by
  set s := sigmaSign L (2 * z)
  set e := eta L (2 * z)
  set g : ℂ → ℂ := fun u => dslope ℘[L] z u * sigma L u ^ 2 /
    (sigmaProd L (u - z) ^ 2 * (s * exp (e * u)))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)).mul
        ((continuous_sigma L).continuousAt.pow 2)
    · exact (((continuous_sigmaProd L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).pow 2).mul (by fun_prop)
    · simp only [sub_self, sigmaProd_zero, one_pow, one_mul]
      exact sigmaSign_mul_exp_ne_zero L _ _
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u - z ≠ 0 := sub_ne_zero.mpr hu
  have hσ : sigma L (u + z) = s * exp (e * u) * sigma L (u - z) := by
    have := sigma_add L h2 (u - z)
    rw [show u - z + 2 * z = u + z by ring, show u - z + 2 * z / 2 = u by ring] at this
    exact this
  have hne := sigmaSign_mul_exp_ne_zero L (2 * z) (e * u)
  simp only [g, degF, dslope_eq_div hu, hσ, sigma_eq_mul_sigmaProd L (u - z)]
  field_simp

/-- **The `σ`-identity.** For `z ∉ Λ` there is `C ≠ 0` with
`(℘(u) - ℘(z)) σ(u)² = C σ(u - z) σ(u + z)` for all `u ∉ Λ`. -/
theorem sigma_identity {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ u ∉ L.lattice,
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 = C * (sigma L (u - z) * sigma L (u + z)) := by
  have hb : ∀ s ∈ degS L z, s - z ∉ L.lattice → LocBdd (degF L z) s := by
    intro s hs hsz
    rcases hs with h | h | h
    · have := (locBdd_degF_zero L hz).of_periodic (ω := s) (fun u => degF_add L z h u)
      rwa [zero_add] at this
    · exact absurd h hsz
    · have h2 : 2 * z ∉ L.lattice := by
        intro h2
        apply hsz
        have := sub_mem h h2
        rwa [show s + z - 2 * z = s - z by ring] at this
      have h1 := ((locBdd_degF_self L hz h2).of_even (degF_neg L z)).of_periodic (ω := s + z)
        (fun u => degF_add L z h u)
      rwa [show -z + (s + z) = s by ring] at h1
  have ha : LocBdd (fun u => (u - z) * degF L z u) z := by
    by_cases h2 : 2 * z ∈ L.lattice
    · exact locBdd_mul_degF_self_of_two_mul_mem L hz h2
    · exact (LocBdd.of_continuousAt (f := fun u => u - z) (by fun_prop)).mul
        (locBdd_degF_self L hz h2)
  obtain ⟨C, hC⟩ := eq_const_of_simple_pole L z (discr_degS L z)
    (fun u hu ω hω => degS_add L hu hω) (fun u _ ω hω => degF_add L z hω u)
    (fun x hx => differentiableAt_degF L hx) hb ha
  have key : ∀ u ∉ L.lattice,
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 = C * (sigma L (u - z) * sigma L (u + z)) := by
    intro u hu
    by_cases hS : u ∈ degS L z
    · rcases hS with h | h | h
      · exact absurd h hu
      · have hP : ℘[L] u = ℘[L] z := by
          have := weierstrassP_add_mem L z h
          rwa [show z + (u - z) = u by ring] at this
        rw [hP, (sigma_eq_zero_iff L).mpr h]
        ring
      · have hP : ℘[L] u = ℘[L] z := by
          have := weierstrassP_add_mem L (-z) h
          rwa [show -z + (u + z) = u by ring, weierstrassP_neg] at this
        rw [hP, (sigma_eq_zero_iff L).mpr h]
        ring
    · have h1 : u - z ∉ L.lattice := fun h => hS (Or.inr (Or.inl h))
      have h2 : u + z ∉ L.lattice := fun h => hS (Or.inr (Or.inr h))
      have := hC u hS
      unfold degF at this
      rw [div_eq_iff (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))] at this
      exact this
  refine ⟨C, fun hC0 => ?_, key⟩
  obtain ⟨u, hu, hM⟩ := exists_norm_weierstrassP_gt L ‖℘[L] z‖
  have := key u hu
  rw [hC0, zero_mul, mul_eq_zero] at this
  rcases this with h | h
  · rw [sub_eq_zero.mp h] at hM
    exact lt_irrefl _ hM
  · exact sigma_ne_zero L hu (pow_eq_zero_iff (by norm_num) |>.mp h)

/-- **Degree two.** For `z, w ∉ Λ`: `℘(w) = ℘(z) ↔ w ≡ z ∨ w ≡ -z (mod Λ)`. -/
theorem weierstrassP_eq_iff {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    ℘[L] w = ℘[L] z ↔ w - z ∈ L.lattice ∨ w + z ∈ L.lattice := by
  constructor
  · intro h
    obtain ⟨C, hC, key⟩ := sigma_identity L hz
    have := key w hw
    rw [h, sub_self, zero_mul, eq_comm, mul_eq_zero, mul_eq_zero] at this
    rcases this with h0 | h0 | h0
    · exact absurd h0 hC
    · exact Or.inl ((sigma_eq_zero_iff L).mp h0)
    · exact Or.inr ((sigma_eq_zero_iff L).mp h0)
  · rintro (h | h)
    · have := weierstrassP_add_mem L z h
      rwa [show z + (w - z) = w by ring] at this
    · have := weierstrassP_add_mem L (-z) h
      rwa [show -z + (w + z) = w by ring, weierstrassP_neg] at this

/-- The zeros of `℘'` off the lattice are exactly the half periods. -/
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ 2 * z ∈ L.lattice := by
  constructor
  · intro h
    obtain ⟨C, hC, key⟩ := sigma_identity L hz
    have hs := differentiable_sigma L
    have hL : HasDerivAt (fun u => (℘[L] u - ℘[L] z) * sigma L u ^ 2)
        (℘'[L] z * sigma L z ^ 2 + (℘[L] z - ℘[L] z) * (2 * sigma L z ^ 1 * deriv (sigma L) z))
        z := by
      have := ((hasDerivAt_weierstrassP L hz).sub_const (℘[L] z)).mul ((hs z).hasDerivAt.pow 2)
      simpa only [Pi.pow_apply, Pi.mul_apply, sub_self, zero_mul, add_zero] using! this
    have hR : HasDerivAt (fun u => C * (sigma L (u - z) * sigma L (u + z)))
        (C * (deriv (sigma L) (z - z) * 1 * sigma L (z + z) +
          sigma L (z - z) * (deriv (sigma L) (z + z) * 1))) z := by
      have h1 : HasDerivAt (fun u => sigma L (u - z)) (deriv (sigma L) (z - z) * 1) z :=
        (hs (z - z)).hasDerivAt.comp (h := fun u => u - z) z ((hasDerivAt_id' z).sub_const z)
      have h2 : HasDerivAt (fun u => sigma L (u + z)) (deriv (sigma L) (z + z) * 1) z :=
        (hs (z + z)).hasDerivAt.comp (h := fun u => u + z) z ((hasDerivAt_id' z).add_const z)
      exact (h1.mul h2).const_mul C
    have heq : (fun u => (℘[L] u - ℘[L] z) * sigma L u ^ 2) =ᶠ[𝓝 z]
        fun u => C * (sigma L (u - z) * sigma L (u + z)) := by
      filter_upwards [(isOpen_compl_lattice L).mem_nhds hz] with u hu
      exact key u hu
    have := hL.unique (hR.congr_of_eventuallyEq heq)
    rw [h, sub_self, sub_self, deriv_sigma_zero, sigma_zero] at this
    simp only [zero_mul, add_zero, mul_one, one_mul] at this
    have h0 : sigma L (z + z) = 0 := by
      rcases mul_eq_zero.mp this.symm with h' | h'
      · exact absurd h' hC
      · exact h'
    rw [← two_mul] at h0
    exact (sigma_eq_zero_iff L).mp h0
  · intro h
    have := derivWeierstrassP_half L h
    rwa [mul_div_cancel_left₀ _ two_ne_zero] at this

end LSG.Weierstrass

end

section

/- Primary generators in the Gaussian coefficient formula for η(4τ)²η(8τ)². -/

namespace TunnellGaussian

open GaussianInt

def Primary (z : GaussianInt) : Prop := (⟨2,2⟩ : GaussianInt) ∣ z-1

lemma primary_iff (z : GaussianInt) :
    Primary z ↔ z.im % 2 = 0 ∧ (z.re + z.im) % 4 = 1 := by
  constructor
  · rintro ⟨⟨u,v⟩,h⟩
    have ha := congrArg Zsqrtd.re h
    have hb := congrArg Zsqrtd.im h
    change z.re - 1 = 2*u + -1*2*v at ha
    change z.im - 0 = 2*v + 2*u at hb
    omega
  · rintro ⟨h₁,h₂⟩
    refine ⟨⟨(z.re + z.im - 1)/4, (z.im - z.re + 1)/4⟩, ?_⟩
    ext
    · change z.re - 1 = 2*((z.re + z.im - 1)/4) + -1*2*((z.im - z.re + 1)/4)
      omega
    · change z.im - 0 = 2*((z.im - z.re + 1)/4) + 2*((z.re + z.im - 1)/4)
      omega

end TunnellGaussian

end

section

/- Grouping the Hecke character by its Gaussian residue classes. -/

namespace TunnellCMLSeries

open TunnellGaussian Finset

abbrev Residues (n : ℕ) := ZMod (4*n) × ZMod (4*n)

def residue (n : ℕ) (z : GaussianInt) : Residues n := (z.re, z.im)

def liftResidue {n : ℕ} (r : Residues n) : GaussianInt := ⟨r.1.val,r.2.val⟩

noncomputable def twistSign (n m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0
noncomputable def charWeight (n : ℕ) (z : GaussianInt) : ℤ := by
  classical exact if Primary z then twistSign n z.norm.natAbs else 0

end TunnellCMLSeries

end

section

/- The regularized Weierstrass zeta function for constructing logarithmic derivatives of elliptic units. -/

namespace TunnellEllipticZeta

open Complex Filter Set
open scoped Topology PeriodPair

noncomputable def summand (w z : ℂ) := (z-w)⁻¹ + w⁻¹ + z/w^2
noncomputable def zeta (L : PeriodPair) (z : ℂ) := ∑' w : L.lattice, summand w z

lemma bound (r : ℝ) (hr : 0<r) (w z : ℂ) (hz : ‖z‖<r) (hw : 2*r≤‖w‖) :
    ‖summand w z‖ ≤ 2*r^2*‖w‖^(-3:ℝ) := by
  have hp : 0<‖w‖ := by linarith
  have hw0 := norm_pos_iff.mp hp
  have hzw : z-w≠0 := sub_ne_zero.mpr (fun e => by rw [e] at hz; linarith)
  have hdist : ‖w‖/2 ≤ ‖z-w‖ := by
    rw [norm_sub_rev]
    linarith [norm_sub_norm_le w z]
  have e : summand w z = z^2/(w^2*(z-w)) := by
    unfold summand
    field_simp
    ring
  rw [e,norm_div,norm_pow,norm_mul,norm_pow]
  calc
    _ ≤ r^2/(‖w‖^2*(‖w‖/2)) := by gcongr
    _ = 2*r^2*‖w‖^(-3:ℝ) := by
      rw [Real.rpow_neg hp.le, Real.rpow_ofNat]
      field_simp

theorem locally_uniform (L : PeriodPair) :
    HasSumLocallyUniformly (fun (w : L.lattice) z => summand w z) (zeta L) := by
  refine L.hasSumLocallyUniformly_aux _ (fun r w => 2*r^2*‖w‖^(-3:ℝ))
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) ?_
  intro r hr
  filter_upwards [eventually_ge_atTop (2*r)] with R hR
  rintro z hz w rfl
  exact bound r hr w z hz hR

lemma summand_deriv (w z : ℂ) (hz : z≠w) :
    HasDerivAt (summand w) (-(1/(z-w)^2-1/w^2)) z := by
  have h := ((((hasDerivAt_id z).sub_const w).inv (sub_ne_zero.mpr hz)).add_const w⁻¹).add
    ((hasDerivAt_id z).div_const (w^2))
  apply h.congr_deriv
  dsimp
  ring

theorem zeta_deriv (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt (zeta L) (-L.weierstrassP z) z := by
  let U := (L.lattice : Set ℂ)ᶜ
  have ho : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hdiff (s : Finset L.lattice) : DifferentiableOn ℂ (fun u => ∑ w ∈ s, summand w u) U := by
    apply DifferentiableOn.fun_sum
    intro w _
    exact fun u hu => (summand_deriv w u (fun e => hu (e ▸ w.property))).differentiableAt.differentiableWithinAt
  have hfun := (locally_uniform L).tendstoLocallyUniformlyOn (s := U)
  have hd := (hfun.deriv (.of_forall hdiff) ho).tendsto_at hz
  have e : deriv (zeta L) z = -L.weierstrassP z := by
    apply tendsto_nhds_unique hd
    apply ((L.hasSum_weierstrassP z).neg).congr'
    apply Filter.Eventually.of_forall
    intro s
    simp only [Function.comp_def]
    rw [deriv_fun_sum (fun (w : L.lattice) _ => (summand_deriv w z (fun e => hz (e ▸ w.property))).differentiableAt)]
    apply Finset.sum_congr rfl
    intro w _
    exact (summand_deriv w z (fun e => hz (e ▸ w.property))).deriv.symm
  rw [← e]
  exact (hfun.differentiableOn (.of_forall hdiff) ho).differentiableAt (ho.mem_nhds hz) |>.hasDerivAt

lemma zeta_neg (L : PeriodPair) (z : ℂ) : zeta L (-z) = -zeta L z := by
  unfold zeta
  rw [← tsum_neg]
  convert (Equiv.neg L.lattice).tsum_eq (fun w : L.lattice => -summand w z) using 1
  apply tsum_congr
  intro w
  simp only [Equiv.neg_apply,Submodule.coe_neg,summand]
  rw [show -z-(w:ℂ) = -(z-(-w:ℂ)) by ring, inv_neg]
  simp only [inv_neg,neg_sq,neg_div]
  ring

lemma quasi_period (L : PeriodPair) (l : L.lattice) :
    ∃ A : ℂ, ∀ z ∉ L.lattice, zeta L (z+l)=zeta L z+A := by
  let U := (L.lattice : Set ℂ)ᶜ
  have hcnt : (L.lattice : Set ℂ).Countable := by
    let : Countable L.lattice := Countable.of_equiv _ L.latticeEquivProd.toEquiv.symm
    exact to_countable _
  have hr : 1 < Module.rank ℝ ℂ := by simp
  have hc : IsPreconnected U := (hcnt.isPathConnected_compl_of_one_lt_rank hr).isConnected.isPreconnected
  have ho : IsOpen U := L.isClosed_lattice.isOpen_compl
  have hu {z : ℂ} (hz : z∈U) : z+(l:ℂ)∈U := fun e => hz (by
    simpa using sub_mem e l.property)
  have da {z : ℂ} (hz : z∈U) : HasDerivAt (fun w : ℂ => zeta L (w+l)) (-L.weierstrassP z) z := by
    simpa only [L.weierstrassP_add_coe,mul_one,Function.comp_def,id_eq] using! (zeta_deriv L _ (hu hz)).comp z ((hasDerivAt_id z).add_const (l:ℂ))
  obtain ⟨A,hA⟩ := ho.exists_eq_add_of_deriv_eq hc
    (fun z hz => (da hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (zeta_deriv L z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (da hz).deriv.trans (zeta_deriv L z hz).deriv.symm)
  exact ⟨A,fun z hz => hA hz⟩

private lemma translate_outside (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (l : L.lattice) : z+(l:ℂ) ∉ L.lattice := fun e => hz (by simpa using sub_mem e l.property)

noncomputable def increment (L : PeriodPair) (l : L.lattice) : ℂ :=
  zeta L (L.ω₁/2 + l) - zeta L (L.ω₁/2)

lemma zeta_shift (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (l : L.lattice) :
    zeta L (z+l) = zeta L z + increment L l := by
  obtain ⟨A, hA⟩ := quasi_period L l
  rw [increment, hA _ L.ω₁_div_two_notMem_lattice, hA _ hz]
  ring

noncomputable def quasiPeriods (L : PeriodPair) : L.lattice →+ ℂ where
  toFun := increment L
  map_zero' := by simp [increment]
  map_add' l k := by
    change zeta L (L.ω₁/2 + ((l+k : L.lattice):ℂ)) - _ = _
    rw [Submodule.coe_add, ← add_assoc,
      zeta_shift L (translate_outside L L.ω₁_div_two_notMem_lattice l) k,
      zeta_shift L L.ω₁_div_two_notMem_lattice l]
    ring

/-- The logarithmic derivative of the integer-multiplication elliptic unit. -/
noncomputable def multiplicationZeta (L : PeriodPair) (a : ℕ) (z : ℂ) : ℂ :=
  (a:ℂ) * zeta L ((a:ℂ)*z) - (a:ℂ)^2 * zeta L z

lemma multiplicationZeta_periodic (L : PeriodPair) (a : ℕ) (z : ℂ) (l : L.lattice)
    (hz : z ∉ L.lattice) (haz : (a:ℂ)*z ∉ L.lattice) :
    multiplicationZeta L a (z+l) = multiplicationZeta L a z := by
  have H : increment L (a • l) = (a:ℂ) * increment L l :=
    (map_nsmul (quasiPeriods L) a l).trans (nsmul_eq_mul a _)
  have e : (a:ℂ)*(l:ℂ) = ((a • l : L.lattice):ℂ) := by simp [nsmul_eq_mul]
  unfold multiplicationZeta
  rw [mul_add, e, zeta_shift L haz, zeta_shift L hz, H]
  ring

lemma multiplicationZeta_odd (L : PeriodPair) (a : ℕ) (z : ℂ) :
    multiplicationZeta L a (-z) = -multiplicationZeta L a z := by
  simp only [multiplicationZeta, mul_neg, zeta_neg]
  ring

end TunnellEllipticZeta

end

section

/- The critical CM L-value as a finite trace of multiplication-zeta values. -/

namespace TunnellCMCritical

open Complex Filter Set TunnellCMLSeries
open scoped Topology ComplexConjugate

noncomputable def periods (n : ℕ) (hn : 0<n) : PeriodPair where
  ω₁ := (4*n:ℕ)
  ω₂ := ((4*n:ℕ):ℂ)*I
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro x y he
    have hr := congrArg re he
    have hi := congrArg im he
    simp [Complex.mul_re,Complex.mul_im,hn.ne'] at hr hi
    exact ⟨hr,hi⟩

noncomputable def aux (n : ℕ) := 1+3*(4*n)

lemma aux_integral (n : ℕ) (hn : 0<n) (z : GaussianInt) :
    (((aux n:ℕ):ℂ)-1)*(z:ℂ) ∈ (periods n hn).lattice := by
  apply PeriodPair.mem_lattice.mpr
  refine ⟨3*z.re,3*z.im,?_⟩
  rw [GaussianInt.toComplex_def]
  simp [periods,aux]
  ring

end TunnellCMCritical

end

section

/- Distribution of logarithmic derivatives under integer multiplication on a complex torus. -/
namespace TunnellCMDistribution

open Complex Filter Set
open scoped Topology PeriodPair

abbrev Grid (a : ℕ) := Fin a × Fin a

noncomputable def liftGrid (L : PeriodPair) {a : ℕ} (j : Grid a) : ℂ :=
  ((j.1.val:ℂ)*L.ω₁+(j.2.val:ℂ)*L.ω₂)/(a:ℂ)

noncomputable def gridEquiv (L : PeriodPair) (a : ℕ) [NeZero a] :
    Grid a × L.lattice ≃ L.lattice :=
  (Equiv.prodComm _ _).trans <|
  (L.latticeEquivProd.toEquiv.prodCongr (Equiv.refl _)).trans <|
  (Equiv.prodProdProdComm ℤ ℤ (Fin a) (Fin a)).trans <|
  ((Int.divModEquiv a).symm.prodCongr (Int.divModEquiv a).symm).trans L.latticeEquivProd.symm.toEquiv

lemma coe_gridEquiv (L : PeriodPair) (a : ℕ) [NeZero a] (j : Grid a) (w : L.lattice) :
    (gridEquiv L a (j,w):ℂ) = (a:ℂ)*((w:ℂ)+liftGrid L j) := by
  obtain ⟨v,rfl⟩ := L.latticeEquivProd.symm.surjective w
  change (L.latticeEquivProd.symm
      ((Int.divModEquiv a).symm ((L.latticeEquivProd (L.latticeEquivProd.symm v)).1,j.1),
       (Int.divModEquiv a).symm ((L.latticeEquivProd (L.latticeEquivProd.symm v)).2,j.2)):ℂ) = _
  rw [LinearEquiv.apply_symm_apply,L.latticeEquiv_symm_apply,L.latticeEquiv_symm_apply]
  simp only [Int.divModEquiv_symm_apply,Int.cast_add,Int.cast_mul,Int.cast_natCast,liftGrid]
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  field_simp
  <;> ring

theorem derivP_distribution (L : PeriodPair) (a : ℕ) [NeZero a] (z : ℂ) :
    (∑ j : Grid a, L.derivWeierstrassP (z-liftGrid L j)) =
      (a:ℂ)^3 * L.derivWeierstrassP ((a:ℂ)*z) := by
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  let term (p : Grid a × L.lattice) := -2/(z-liftGrid L p.1-(p.2:ℂ))^3
  have h0 := ((L.hasSum_derivWeierstrassP ((a:ℂ)*z)).mul_left ((a:ℂ)^3))
  have heq : (fun p : Grid a × L.lattice => (a:ℂ)^3 *
      (-2/((a:ℂ)*z-(gridEquiv L a p:ℂ))^3))=term := by
    funext ⟨j,w⟩
    change (a:ℂ)^3 * (-2/((a:ℂ)*z-(gridEquiv L a (j,w):ℂ))^3) = _
    rw [coe_gridEquiv,← mul_sub,mul_pow,div_mul_eq_div_div]
    dsimp [term]
    rw [show z-((w:ℂ)+liftGrid L j) = z-liftGrid L j-w by ring]
    field_simp
  have h : HasSum term ((a:ℂ)^3*L.derivWeierstrassP ((a:ℂ)*z)) := by
    rw [← heq]
    exact ((gridEquiv L a).hasSum_iff (f := fun w : L.lattice =>
      (a:ℂ)^3 * (-2/((a:ℂ)*z-(w:ℂ))^3))).mpr h0
  rw [← h.tsum_eq,h.summable.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  exact (L.hasSum_derivWeierstrassP (z-liftGrid L j)).tsum_eq.symm

def regular (L : PeriodPair) (a : ℕ) := {z : ℂ | (a:ℂ)*z ∉ L.lattice}

lemma regular_open (L : PeriodPair) (a : ℕ) : IsOpen (regular L a) :=
  L.isClosed_lattice.isOpen_compl.preimage (continuous_const.mul continuous_id)

lemma regular_connected (L : PeriodPair) (a : ℕ) [NeZero a] : IsPreconnected (regular L a) := by
  let : Countable L.lattice := Countable.of_equiv _ L.latticeEquivProd.toEquiv.symm
  have count : (L.lattice : Set ℂ).Countable := to_countable _
  have ha : (a:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne a
  exact ((count.preimage (mul_right_injective₀ ha)).isPathConnected_compl_of_one_lt_rank
    (by simp : 1 < Module.rank ℝ ℂ)).isConnected.isPreconnected

lemma mul_lift (L : PeriodPair) {a : ℕ} [NeZero a] (j : Grid a) :
    (a:ℂ)*liftGrid L j ∈ L.lattice := by
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  rw [liftGrid,← mul_div_assoc,mul_div_cancel_left₀ _ ha]
  exact PeriodPair.mem_lattice.mpr ⟨(j.1.val:ℤ),(j.2.val:ℤ),by simp⟩

lemma mul_mem (L : PeriodPair) (a : ℕ) {z : ℂ} (hz : z ∈ L.lattice) :
    (a:ℂ)*z ∈ L.lattice := by
  rw [← nsmul_eq_mul]
  exact L.lattice.nsmul_mem hz _

lemma sub_regular (L : PeriodPair) {a : ℕ} [NeZero a] {z : ℂ} (hz : z∈regular L a) (j : Grid a) :
    z-liftGrid L j ∉ L.lattice := fun h => hz (by simpa [mul_sub] using add_mem (mul_mem L a h) (mul_lift L j))

lemma add_regular (L : PeriodPair) {a : ℕ} [NeZero a] {z : ℂ} (hz : z∈regular L a) (j : Grid a) :
    z+liftGrid L j ∉ L.lattice := fun h => hz (by simpa [mul_add] using sub_mem (mul_mem L a h) (mul_lift L j))

lemma neg_regular (L : PeriodPair) {a : ℕ} {z : ℂ} (hz : z∈regular L a) : -z∈regular L a := by
  simpa [regular] using hz

lemma hasDerivP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  simpa only [L.deriv_weierstrassP] using
    (L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt

theorem traceP (L : PeriodPair) (a : ℕ) [NeZero a] :
    ∃ A : ℂ, ∀ z ∈ regular L a,
      (∑ j : Grid a, L.weierstrassP (z-liftGrid L j)) = (a:ℂ)^2*L.weierstrassP ((a:ℂ)*z)+A := by
  let f (z : ℂ) := ∑ j : Grid a, L.weierstrassP (z-liftGrid L j)
  let g (z : ℂ) := (a:ℂ)^2*L.weierstrassP ((a:ℂ)*z)
  have h1 {z : ℂ} (hz : z∈regular L a) : HasDerivAt f ((a:ℂ)^3*L.derivWeierstrassP ((a:ℂ)*z)) z := by
    rw [← derivP_distribution]
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [mul_one] using! (hasDerivP L (sub_regular L hz j)).comp z ((hasDerivAt_id' z).sub_const (liftGrid L j))
  have h2 {z : ℂ} (hz : z∈regular L a) : HasDerivAt g ((a:ℂ)^3*L.derivWeierstrassP ((a:ℂ)*z)) z := by
    apply (((hasDerivP L hz).comp z ((hasDerivAt_id' z).const_mul (a:ℂ))).const_mul ((a:ℂ)^2)).congr_deriv
    ring
  exact (regular_open L a).exists_eq_add_of_deriv_eq (regular_connected L a)
    (fun _ hz => (h1 hz).differentiableAt.differentiableWithinAt)
    (fun _ hz => (h2 hz).differentiableAt.differentiableWithinAt)
    (fun _ hz => (h1 hz).deriv.trans (h2 hz).deriv.symm)

open TunnellEllipticZeta

noncomputable def zetaTrace (L : PeriodPair) (a : ℕ) (z : ℂ) :=
    (∑ j : Grid a, (zeta L (z-liftGrid L j)+zeta L (z+liftGrid L j))) - 2*(a:ℂ)*zeta L ((a:ℂ)*z)

lemma zetaTrace_neg (L : PeriodPair) (a : ℕ) (z : ℂ) : zetaTrace L a (-z) = -zetaTrace L a z := by
  have e (u : ℂ) : zeta L (-z-u)+zeta L (-z+u) = -(zeta L (z-u)+zeta L (z+u)) := by
    rw [show -z-u=-(z+u) by ring,show -z+u=-(z-u) by ring,zeta_neg,zeta_neg]
    ring
  simp only [zetaTrace,e,Finset.sum_neg_distrib,mul_neg,zeta_neg]
  ring

lemma zetaTrace_shift (L : PeriodPair) {a : ℕ} [NeZero a] {z : ℂ} (hz : z∈regular L a) (l : L.lattice) :
    zetaTrace L a (z+l) = zetaTrace L a z := by
  have hl : (a:ℂ)*(l:ℂ)=((a • l : L.lattice):ℂ) := by simp [nsmul_eq_mul]
  have hinc : increment L (a • l)=(a:ℂ)*increment L l :=
    (map_nsmul (quasiPeriods L) a l).trans (nsmul_eq_mul a _)
  have e (j : Grid a) :
      zeta L (z+l-liftGrid L j)+zeta L (z+l+liftGrid L j) =
        (zeta L (z-liftGrid L j)+zeta L (z+liftGrid L j)) + 2*increment L l := by
    rw [show z+l-liftGrid L j=z-liftGrid L j+l by ring,
      show z+l+liftGrid L j=z+liftGrid L j+l by ring,zeta_shift L (sub_regular L hz j),
      zeta_shift L (add_regular L hz j)]
    ring
  simp only [zetaTrace,e,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Grid,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,mul_add,hl,zeta_shift L hz,hinc]
  ring

theorem zeta_distribution (L : PeriodPair) (a : ℕ) [NeZero a] {z : ℂ} (hz : z∈regular L a) :
    zetaTrace L a z = 0 := by
  obtain ⟨A,hA⟩ := traceP L a
  have plus (v : ℂ) (hv : v∈regular L a) : (∑ j : Grid a, L.weierstrassP (v+liftGrid L j)) =
      (a:ℂ)^2*L.weierstrassP ((a:ℂ)*v)+A := by
    have E (u : ℂ) : L.weierstrassP (-v-u)=L.weierstrassP (v+u) := by
      rw [show -v-u=-(v+u) by ring,L.weierstrassP_neg]
    simpa only [E,mul_neg,L.weierstrassP_neg] using hA (-v) (neg_regular L hv)
  have hD (v : ℂ) (hv : v∈regular L a) : HasDerivAt (zetaTrace L a) (-2*A) v := by
    have D₁ (j : Grid a) : HasDerivAt (fun w => zeta L (w-liftGrid L j)+zeta L (w+liftGrid L j))
        (-(L.weierstrassP (v-liftGrid L j))-L.weierstrassP (v+liftGrid L j)) v := by
      simpa only [mul_one,sub_eq_add_neg] using!
        ((zeta_deriv L _ (sub_regular L hv j)).comp v ((hasDerivAt_id' v).sub_const (liftGrid L j))).add
          ((zeta_deriv L _ (add_regular L hv j)).comp v ((hasDerivAt_id' v).add_const (liftGrid L j)))
    apply ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => D₁ j)).sub
      (((zeta_deriv L _ hv).comp v ((hasDerivAt_id' v).const_mul (a:ℂ))).const_mul (2*(a:ℂ)))).congr_deriv
    rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib,hA v hv,plus v hv]
    ring
  have lin (v : ℂ) : HasDerivAt (fun x : ℂ => (-2*A)*x) (-2*A) v := by
    simpa using (hasDerivAt_id' v).const_mul (-2*A)
  obtain ⟨B,hB⟩ := (regular_open L a).exists_eq_add_of_deriv_eq (regular_connected L a)
    (fun v hv => (hD v hv).differentiableAt.differentiableWithinAt)
    (fun v _ => (lin v).differentiableAt.differentiableWithinAt)
    (fun v hv => (hD v hv).deriv.trans (lin v).deriv.symm)
  let l : L.lattice := ⟨L.ω₁,L.ω₁_mem_lattice⟩
  have hp : z+(l:ℂ) ∈ regular L a := fun h => hz (by
    simpa only [mul_add,add_sub_cancel_right] using sub_mem h (mul_mem L a l.property))
  have hlin (v : ℂ) (hv : v∈regular L a) : zetaTrace L a v=(-2*A)*v+B := hB hv
  have d := zetaTrace_shift L hz l
  rw [hlin _ hp,hlin _ hz] at d
  have hzero : A*(l:ℂ)=0 := by linear_combination -d/2
  have he : (l:ℂ) ≠ 0 := L.indep.ne_zero (0 : Fin 2)
  have ha := (mul_eq_zero.mp hzero).resolve_right he
  have n := zetaTrace_neg L a z
  rw [hlin _ (neg_regular L hz),hlin _ hz,ha] at n
  rw [hlin _ hz,ha]
  linear_combination n/2

end TunnellCMDistribution

end

section

/- Expression of the multiplication-zeta value as the logarithmic derivative of the
product over nonzero division points. -/

namespace TunnellCMEllipticUnit

open Complex Set Filter TunnellEllipticZeta TunnellCMDistribution
open scoped Topology PeriodPair
open LSG.Weierstrass (sigma sigma_identity logDeriv_sigma weierstrassP_eq_iff)

lemma same_zeta (L : PeriodPair) (z : ℂ) : LSG.Weierstrass.zeta L z=zeta L z := by
  simp only [LSG.Weierstrass.zeta,LSG.Weierstrass.zetaSummand,zeta,summand,one_div]

lemma log_pair (L : PeriodPair) {z u : ℂ} (hz : z∉L.lattice) (hu : u∉L.lattice)
    (hm : z-u∉L.lattice) (hp : z+u∉L.lattice) :
    logDeriv (fun w => L.weierstrassP w - L.weierstrassP u) z =
      zeta L (z-u)+zeta L (z+u)-2*zeta L z := by
  obtain ⟨c,hc,h⟩ := sigma_identity L hu
  have hP := hasDerivP L hz
  have hne : L.weierstrassP z - L.weierstrassP u ≠ 0 := sub_ne_zero.mpr (fun e =>
    ((weierstrassP_eq_iff L hu hz).mp e).elim hm hp)
  have hS := LSG.Weierstrass.differentiable_sigma L
  have hSn {v : ℂ} (hv : v∉L.lattice) : sigma L v≠0 := LSG.Weierstrass.sigma_ne_zero L hv
  have elm := (hasDerivAt_id' z).sub_const u
  have elp := (hasDerivAt_id' z).add_const u
  have hds : logDeriv (fun w : ℂ => sigma L (w-u)) z = zeta L (z-u) := by
    change logDeriv ((sigma L) ∘ (fun w : ℂ => w-u)) z = _
    rw [logDeriv_comp (hS _) elm.differentiableAt,elm.deriv,logDeriv_sigma L hm,same_zeta,mul_one]
  have hda : logDeriv (fun w : ℂ => sigma L (w+u)) z = zeta L (z+u) := by
    change logDeriv ((sigma L) ∘ (fun w : ℂ => w+u)) z = _
    rw [logDeriv_comp (hS _) elp.differentiableAt,elp.deriv,logDeriv_sigma L hp,same_zeta,mul_one]
  have ev : (fun w => (L.weierstrassP w-L.weierstrassP u)*sigma L w^2) =ᶠ[𝓝 z]
      fun w => c*(sigma L (w-u)*sigma L (w+u)) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw using h w hw
  have he := (logDeriv_congr_nhds ev).self_of_nhds
  rw [logDeriv_mul (f := fun w => L.weierstrassP w-L.weierstrassP u) (g := fun w => sigma L w^2)
    z hne (pow_ne_zero 2 (hSn hz)) (hP.sub_const _).differentiableAt ((hS z).pow 2),
    logDeriv_fun_pow (hS z),logDeriv_sigma L hz,same_zeta,logDeriv_const_mul z c hc,
    logDeriv_mul (f := fun w => sigma L (w-u)) (g := fun w => sigma L (w+u)) z
      (hSn hm) (hSn hp) ((hS _).comp z elm.differentiableAt) ((hS _).comp z elp.differentiableAt),
    hds,hda] at he
  linear_combination he

noncomputable def divisionGrid (L : PeriodPair) (a : ℕ) : Finset (Grid a) := by
  classical exact Finset.univ.filter (fun j => liftGrid L j ∉ L.lattice)

noncomputable def divisionProduct (L : PeriodPair) (a : ℕ) (z : ℂ) :=
  ∏ j ∈ divisionGrid L a, (L.weierstrassP z - L.weierstrassP (liftGrid L j))

theorem log_divisionProduct (L : PeriodPair) (a : ℕ) [NeZero a] {z : ℂ} (hz : z∈regular L a) :
    logDeriv (divisionProduct L a) z = 2*multiplicationZeta L a z := by
  classical
  have hs : z ∉ L.lattice := fun h => hz (mul_mem L a h)
  let term (j : Grid a) := zeta L (z-liftGrid L j)+zeta L (z+liftGrid L j)-2*zeta L z
  have e (j : Grid a) (hj : j ∈ divisionGrid L a) : liftGrid L j ∉ L.lattice := (Finset.mem_filter.mp hj).2
  have hn (j : Grid a) (hj : j ∈ divisionGrid L a) :
      L.weierstrassP z-L.weierstrassP (liftGrid L j)≠0 :=
    sub_ne_zero.mpr (fun h => ((weierstrassP_eq_iff L (e j hj) hs).mp h).elim (sub_regular L hz j) (add_regular L hz j))
  have hg (j : Grid a) (hj : j ∉ divisionGrid L a) : term j=0 := by
    have hm : liftGrid L j ∈ L.lattice := by simpa [divisionGrid] using hj
    let l : L.lattice := ⟨liftGrid L j,hm⟩
    have hneg : increment L (-l) = -increment L l := map_neg (quasiPeriods L) l
    change zeta L (z-l)+zeta L (z+l)-2*zeta L z=0
    rw [show z-(l:ℂ)=z+((-l : L.lattice):ℂ) by simp [sub_eq_add_neg],
      zeta_shift L hs (-l),zeta_shift L hs l,hneg]
    ring
  have hlog : logDeriv (divisionProduct L a) z = ∑ j ∈ divisionGrid L a, term j := by
    unfold divisionProduct
    rw [logDeriv_prod hn (fun j _ => ((hasDerivP L hs).sub_const _).differentiableAt)]
    exact Finset.sum_congr rfl (fun j hj => log_pair L hs (e j hj) (sub_regular L hz j) (add_regular L hz j))
  rw [hlog,Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hg j hj)]
  dsimp only [term]
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ]
  have h := zeta_distribution L a hz
  unfold zetaTrace at h
  simp only [Grid,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,multiplicationZeta]
  linear_combination h

end TunnellCMEllipticUnit

end

section

/- Homogeneity of the Weierstrass zeta function under scaling a period lattice. -/

namespace TunnellCMScale

open TunnellEllipticZeta

noncomputable def equiv (L M : PeriodPair) : L.lattice ≃ M.lattice :=
  L.latticeEquivProd.toEquiv.trans M.latticeEquivProd.symm.toEquiv

lemma coe_equiv (L M : PeriodPair) {c : ℂ} (h₁ : M.ω₁=c*L.ω₁) (h₂ : M.ω₂=c*L.ω₂) (l : L.lattice) :
    (equiv L M l:ℂ) = c*(l:ℂ) := by
  obtain ⟨x,rfl⟩ := L.latticeEquivProd.symm.surjective l
  change (M.latticeEquivProd.symm (L.latticeEquivProd (L.latticeEquivProd.symm x)):ℂ) = _
  rw [LinearEquiv.apply_symm_apply,M.latticeEquiv_symm_apply,L.latticeEquiv_symm_apply,h₁,h₂]
  ring

lemma lattice_mem (L M : PeriodPair) {c : ℂ} (hc : c≠0) (h₁ : M.ω₁=c*L.ω₁) (h₂ : M.ω₂=c*L.ω₂) (z : ℂ) :
    c*z ∈ M.lattice ↔ z∈L.lattice := by
  constructor
  · intro h
    obtain ⟨v,hv⟩ := (equiv L M).surjective ⟨_,h⟩
    have e := congrArg Subtype.val hv
    rw [coe_equiv L M h₁ h₂] at e
    exact (mul_left_cancel₀ hc e) ▸ v.property
  · intro h
    rw [← coe_equiv L M h₁ h₂ (⟨z,h⟩ : L.lattice)]
    exact (equiv L M ⟨_,h⟩).property

lemma zeta_scale (L M : PeriodPair) {c : ℂ} (hc : c≠0) (h₁ : M.ω₁=c*L.ω₁) (h₂ : M.ω₂=c*L.ω₂) (z : ℂ) :
    zeta M (c*z)=c⁻¹ * zeta L z := by
  unfold zeta
  rw [← (equiv L M).tsum_eq,← tsum_mul_left]
  apply tsum_congr
  intro w
  rw [coe_equiv L M h₁ h₂,summand,summand,← mul_sub,mul_inv_rev,mul_inv_rev,mul_pow]
  rw [div_eq_mul_inv,div_eq_mul_inv,mul_inv_rev]
  field_simp [hc]
  <;> ring

theorem multiplication_scale (L M : PeriodPair) {c : ℂ} (hc : c≠0) (h₁ : M.ω₁=c*L.ω₁)
    (h₂ : M.ω₂=c*L.ω₂) (a : ℕ) (z : ℂ) :
    multiplicationZeta M a (c*z)=c⁻¹*multiplicationZeta L a z := by
  unfold multiplicationZeta
  rw [mul_left_comm (a:ℂ) c,zeta_scale L M hc h₁ h₂,zeta_scale L M hc h₁ h₂]
  ring

end TunnellCMScale

end

section

/- # The real-period integral for the congruent-number family -/

namespace TunnellCoates

open MeasureTheory Set Filter
open scoped Topology

noncomputable def realPeriod (n : ℝ) : ℝ :=
  ∫ x in Ioi n, (Real.sqrt (x^3-n^2*x))⁻¹

end TunnellCoates

end

section

namespace TunnellCMLemniscate
open Complex TunnellCoates
noncomputable def twistPeriods (n : ℕ) (hn : 0<n) : PeriodPair where
  ω₁ := (realPeriod n:ℂ)
  ω₂ := I * (realPeriod n:ℂ)
  indep := by
    have h : realPeriod n ≠ 0 := (realPeriod_pos (show (0:ℝ)<n by exact_mod_cast hn)).ne'
    apply LinearIndependent.pair_iff.mpr
    intro x y he
    have hr := congrArg re he
    have hi := congrArg im he
    simp [Complex.mul_re,Complex.mul_im,h] at hr hi
    exact ⟨hr,hi⟩

end TunnellCMLemniscate

end

section

/- The first logarithmic derivative at the origin of an explicit elliptic function,
with the real period and conductor factors of the congruent-number twist. -/
namespace TunnellCMUnitTrace

open Complex Finset TunnellCMLSeries TunnellCMCritical TunnellCMLemniscate
open TunnellCMEllipticUnit TunnellCMDistribution TunnellEllipticZeta TunnellCoates
open scoped ComplexConjugate

noncomputable def dilation (n : ℕ) : ℝ := realPeriod n / (4*n)

lemma dilation_ne (n : ℕ) (hn : 0<n) : (dilation n:ℂ)≠0 :=
  ofReal_ne_zero.mpr (div_ne_zero (realPeriod_pos (by exact_mod_cast hn)).ne' (by positivity))

lemma base_dilations (n : ℕ) (hn : 0<n) :
    (twistPeriods n hn).ω₁=(dilation n:ℂ)*(periods n hn).ω₁ ∧
    (twistPeriods n hn).ω₂=(dilation n:ℂ)*(periods n hn).ω₂ := by
  dsimp [twistPeriods,periods,dilation]
  push_cast
  have hn' : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  constructor <;> field_simp [hn'] <;> ring

noncomputable def point (n : ℕ) (r : Residues n) : ℂ := (dilation n:ℂ)*(liftResidue r:ℂ)

lemma shift_regular (n : ℕ) (hn : 0<n) (r : Residues n) (hr : charWeight n (liftResidue r)≠0) :
    point n r∈regular (twistPeriods n hn) (aux n) := by
  let x := liftResidue r
  have hpr : TunnellGaussian.Primary x := by
    classical by_contra h
    exact hr (by change charWeight n x=0; simp [charWeight,h])
  have hout : (x:ℂ) ∉ (periods n hn).lattice := by
    rintro hx
    obtain ⟨k,l,h⟩ := PeriodPair.mem_lattice.mp hx
    have hr := congrArg re h
    have hi := congrArg im h
    rw [GaussianInt.toComplex_def] at hr hi
    simp [periods,mul_re,mul_im] at hr hi
    have xr : (x:ℂ).re=(x.re:ℝ) := by rw [GaussianInt.toComplex_def₂]
    have xi : (x:ℂ).im=(x.im:ℝ) := by rw [GaussianInt.toComplex_def₂]
    rw [xr] at hr
    rw [xi] at hi
    have e₁ : k*(4*n)=x.re := by exact_mod_cast hr
    have e₂ : l*(4*n)=x.im := by exact_mod_cast hi
    have e := (TunnellGaussian.primary_iff _).mp hpr |>.2
    rw [← e₁,← e₂,show k*(4*(n:ℤ))+l*(4*n)=(k*n+l*n)*4 by ring] at e
    omega
  intro h
  change (aux n:ℂ)*((dilation n:ℂ)*(x:ℂ)) ∈ (twistPeriods n hn).lattice at h
  rw [mul_left_comm] at h
  obtain ⟨h1,h2⟩ := base_dilations n hn
  have h' := (TunnellCMScale.lattice_mem _ _ (dilation_ne n hn) h1 h2 _).mp h
  exact hout (by simpa [sub_mul] using sub_mem h' (aux_integral n hn x))

noncomputable def weight (n : ℕ) (r : Residues n) := charWeight n (liftResidue r)

noncomputable def traceUnit (n : ℕ) (hn : 0<n) (Z : ℂ) : ℂ := by
  classical
  letI : NeZero (4*n) := ⟨by omega⟩
  exact ∏ r ∈ univ.filter (fun r => weight n r ≠ 0),
    divisionProduct (twistPeriods n hn) (aux n) (Z+point n r) ^ weight n r

lemma division_nonzero (M : PeriodPair) (a : ℕ) [NeZero a] {z : ℂ} (hz : z∈regular M a) :
    divisionProduct M a z ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hs : z∉M.lattice := fun h => hz (mul_mem M a h)
  have ht : liftGrid M j∉M.lattice := (Finset.mem_filter.mp hj).2
  exact sub_ne_zero.mpr (fun h => ((LSG.Weierstrass.weierstrassP_eq_iff M ht hs).mp h).elim
    (sub_regular M hz j) (add_regular M hz j))

lemma division_diff (M : PeriodPair) (a : ℕ) [NeZero a] {z : ℂ} (hz : z∈regular M a) :
    DifferentiableAt ℂ (divisionProduct M a) z := by
  have hs : z∉M.lattice := fun h => hz (mul_mem M a h)
  exact .fun_finsetProd (fun j _ => ((hasDerivP M hs).sub_const _).differentiableAt)

theorem derivative_sum (n : ℕ) (hn : 0<n) :
    logDeriv (traceUnit n hn) 0 =
      letI : NeZero (4*n) := ⟨by omega⟩
      ∑ r : Residues n, (weight n r:ℂ)*
        (2*multiplicationZeta (twistPeriods n hn) (aux n) (point n r)) := by
  classical
  letI : NeZero (4*n) := ⟨by omega⟩
  letI : NeZero (aux n) := ⟨by unfold aux; omega⟩
  let M := twistPeriods n hn
  let f (r : Residues n) (Z : ℂ) := divisionProduct M (aux n) (Z+point n r)
  have he {r : Residues n} (hr : weight n r≠0) : (0:ℂ)+point n r ∈ regular M (aux n) := by
    simpa using shift_regular n hn r hr
  have hdiff {r : Residues n} (hr : weight n r≠0) : DifferentiableAt ℂ (f r) 0 := by
    change DifferentiableAt ℂ ((divisionProduct M (aux n)) ∘ (fun Z : ℂ => Z+point n r)) 0
    exact (division_diff M (aux n) (he hr)).comp 0 (differentiableAt_id.add_const _)
  have hnz {r : Residues n} (hr : weight n r≠0) : f r 0≠0 := division_nonzero M (aux n) (he hr)
  change logDeriv (fun Z => ∏ r ∈ univ.filter (fun r => weight n r≠0), f r Z ^ weight n r) 0 = _
  rw [logDeriv_prod (f := fun r Z => f r Z ^ weight n r) (s := univ.filter (fun r => weight n r≠0))
    (fun r hr => zpow_ne_zero _ (hnz (mem_filter.mp hr).2))
    (fun r hr => (hdiff (mem_filter.mp hr).2).zpow (.inl (hnz (mem_filter.mp hr).2)))]
  rw [← Finset.sum_filter_of_ne (p := fun r => weight n r≠0) (s := univ)
    (fun r _ h => by contrapose! h; simp [h])]
  apply Finset.sum_congr rfl
  intro r hr
  have h := (mem_filter.mp hr).2
  rw [logDeriv_fun_zpow (hdiff h)]
  congr 1
  change logDeriv ((divisionProduct M (aux n)) ∘ (fun Z : ℂ => Z+point n r)) 0 = _
  rw [logDeriv_comp (g := fun Z : ℂ => Z+point n r) (x := 0)
    (division_diff M (aux n) (he h)) (differentiableAt_id.add_const _),
    ((hasDerivAt_id' (0:ℂ)).add_const (point n r)).deriv,zero_add,mul_one,log_divisionProduct M _ (shift_regular n hn r h)]

end TunnellCMUnitTrace

end

section

/- The critical finite zeta trace gives the rational derivative without
any choice of analytic continuation or auxiliary L-function. -/
namespace TunnellCMTraceSlope
open Complex TunnellCMLSeries TunnellCMCritical TunnellCMUnitTrace TunnellEllipticZeta
open TunnellCMLemniscate TunnellCMEllipticUnit TunnellCoates TunnellCMDistribution Finset
open scoped ComplexConjugate Classical
noncomputable section
def trace (n : ℕ) (hn : 0<n) : ℂ :=
  letI : NeZero (4*n):=⟨by omega⟩
  ∑ v : Residues n, (charWeight n (liftResidue v):ℂ) *
    (-conj (multiplicationZeta (periods n hn) (aux n) (liftResidue v:ℂ)))

theorem derivative (n : ℕ) (hn : 0<n) (r : ℚ)
    (h : ((aux n:ℂ)^2-(aux n:ℂ))*((r:ℂ)*(realPeriod n:ℂ))=trace n hn) :
    logDeriv (traceUnit n hn) 0 = -2*(4*n:ℂ)*((aux n:ℂ)^2-(aux n:ℂ))*(r:ℂ) := by
  classical
  letI : NeZero (4*n):=⟨by omega⟩
  have eL := h
  unfold trace at eL
  let Z (r : Residues n) := multiplicationZeta (periods n hn) (aux n) (liftResidue r:ℂ)
  have ce : ∑ v : Residues n, (weight n v:ℂ)*Z v =
      -(((aux n:ℂ)^2-(aux n:ℂ))*(r:ℂ)*(realPeriod n:ℂ)) := by
    have e := congrArg (fun y : ℂ => -conj y) eL.symm
    simpa only [weight,Z,map_mul,map_sub,map_pow,map_natCast,map_ratCast,Complex.conj_ofReal,
      map_sum,map_neg,map_intCast,Complex.conj_conj,mul_neg,Finset.sum_neg_distrib,neg_neg,mul_assoc] using e
  obtain ⟨h1,h2⟩ := base_dilations n hn
  have hZ (v : Residues n) : multiplicationZeta (twistPeriods n hn) (aux n) (point n v) =
      (dilation n:ℂ)⁻¹*Z v := TunnellCMScale.multiplication_scale _ _ (dilation_ne n hn) h1 h2 _ _
  rw [derivative_sum]
  calc
    _ = (2*(dilation n:ℂ)⁻¹) * ∑ v : Residues n, (weight n v:ℂ)*Z v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [hZ]
      ring
    _ = _ := by
      rw [ce,dilation]
      have hΩ : (realPeriod n:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (realPeriod_pos (by exact_mod_cast hn)).ne'
      push_cast
      field_simp [hΩ]
      <;> ring

theorem nonzero (n : ℕ) (hn : 0<n) (r : ℚ) (hr : r≠0)
    (h : ((aux n:ℂ)^2-(aux n:ℂ))*((r:ℂ)*(realPeriod n:ℂ))=trace n hn) :
    ∃ c : ℚ, c≠0 ∧ logDeriv (traceUnit n hn) 0=(c:ℂ) := by
  let a : ℚ:=aux n
  have ha : 1<a := by dsimp [a,aux]; exact_mod_cast (by omega : 1<1+3*(4*n))
  have hpos : 0<a^2-a := by nlinarith [mul_pos (sub_pos.mpr ha) (lt_trans zero_lt_one ha)]
  have hfirst : (-2:ℚ)*(4*(n:ℚ))≠0:=mul_ne_zero (by norm_num) (by positivity)
  refine ⟨-2*(4*(n:ℚ))*(a^2-a)*r,mul_ne_zero (mul_ne_zero hfirst hpos.ne') hr,?_⟩
  rw [derivative n hn r h]
  simp [a]

end
end TunnellCMTraceSlope

end

lemma TunnellCMTraceSlope.period_ext (M L : PeriodPair) (hx : M.ω₁=L.ω₁) (hy : M.ω₂=L.ω₂) : M=L := by
  cases M
  cases L
  simp only at hx hy
  subst_vars
  rfl

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1.H1 := by
  classical
  refine fun n hn M hx hy r hr h => ?_
  have eq : M=TunnellCMLemniscate.twistPeriods n hn := TunnellCMTraceSlope.period_ext _ _ hx hy
  subst M
  exact TunnellCMTraceSlope.nonzero n hn r hr h
