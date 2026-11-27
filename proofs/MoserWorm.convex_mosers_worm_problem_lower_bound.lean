import FormalConjectures.Wikipedia.MoserWorm

import Mathlib

/-
Port of Lech Mazur's Moser worm mixed-area development (Apache-2.0).
Source: ProofAtlas, commit c9254797b42c2a89acb00281c0822c7d6fc21923.
https://www.proofatlas.ai/sources/moser-worm-mixed-area-lower-bound/
Changes: merged the necessary source modules and adapted them to the pinned
Lean toolchain and to the Formal Conjectures definitions.

MoserWorm formalization source package

MoserWorm/Polygon/TriangleArea.lean adapts
MathLab/Geometry/PlanarArea.lean from SilverAsh7/p5-kernel-deficit-lean at
commit e62a622ed1ff1a70f4a10a860b4088ee35ee6b68.

Copyright (c) 2026 Lech Mazur
Licensed under the Apache License, Version 2.0.

The source header of MoserWorm/Polygon/TriangleArea.lean records the following
notice for its Euclidean-space auxiliary proof.

Copyright (c) 2026 Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.

The auxiliary Euclidean-space proof below is adapted from
`MathLab/Geometry/PlanarArea.lean` at commit
`e62a622ed1ff1a70f4a10a860b4088ee35ee6b68` of
`SilverAsh7/p5-kernel-deficit-lean`. Local changes restrict the imported
surface to the inclusive triangle theorem and transport it to the project's
complex-plane representation.


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


-- MoserWorm.Payoff.Definitions
section

namespace MoserWorm

noncomputable section

namespace Payoff

def M (θ γ : ℝ) : ℝ :=
  max 0
    (max (Real.cos (θ - γ))
      (Real.cos (θ + Real.pi / 3 - γ)))

def A (θ φ : ℝ) : ℝ :=
  max |Real.sin φ|
    ((1 / 2 : ℝ) *
      max
        (max |Real.sin (θ - φ)|
          |Real.sin (θ - φ + Real.pi / 3)|)
        |Real.cos (θ - φ + Real.pi / 6)|)

def Q (β φ : ℝ) : ℝ :=
  max |2 * Real.cos β * Real.sin φ|
    (max |Real.sin (β + φ)| |Real.sin (β - φ)|)

def P (θ β φ : ℝ) : ℝ :=
  Real.cos β * M θ (φ - Real.pi / 2) +
    (1 / 2 : ℝ) * M θ (φ + Real.pi / 2 - β) +
    (1 / 2 : ℝ) * M θ (φ + Real.pi / 2 + β)

def B (θ β φ : ℝ) : ℝ := max (Q β φ) (P θ β φ)

theorem M_periodic (θ : ℝ) : Function.Periodic (M θ) (2 * Real.pi) := by
  intro γ
  unfold M
  rw [show θ - (γ + 2 * Real.pi) = (θ - γ) - 2 * Real.pi by ring,
    show θ + Real.pi / 3 - (γ + 2 * Real.pi) =
      (θ + Real.pi / 3 - γ) - 2 * Real.pi by ring,
    Real.cos_sub_two_pi, Real.cos_sub_two_pi]

theorem A_periodic (θ : ℝ) : Function.Periodic (A θ) (2 * Real.pi) := by
  intro φ
  unfold A
  rw [Real.sin_add_two_pi,
    show θ - (φ + 2 * Real.pi) + Real.pi / 3 =
      (θ - φ + Real.pi / 3) - 2 * Real.pi by ring,
    Real.sin_sub_two_pi,
    show θ - (φ + 2 * Real.pi) + Real.pi / 6 =
      (θ - φ + Real.pi / 6) - 2 * Real.pi by ring,
    Real.cos_sub_two_pi,
    show θ - (φ + 2 * Real.pi) = (θ - φ) - 2 * Real.pi by ring,
    Real.sin_sub_two_pi]

theorem Q_periodic (β : ℝ) : Function.Periodic (Q β) (2 * Real.pi) := by
  intro φ
  unfold Q
  rw [Real.sin_add_two_pi,
    show β + (φ + 2 * Real.pi) = (β + φ) + 2 * Real.pi by ring,
    Real.sin_add_two_pi,
    show β - (φ + 2 * Real.pi) = (β - φ) - 2 * Real.pi by ring,
    Real.sin_sub_two_pi]

theorem P_periodic (θ β : ℝ) : Function.Periodic (P θ β) (2 * Real.pi) := by
  intro φ
  unfold P
  rw [show φ + 2 * Real.pi - Real.pi / 2 =
      (φ - Real.pi / 2) + 2 * Real.pi by ring,
    M_periodic θ,
    show φ + 2 * Real.pi + Real.pi / 2 - β =
      (φ + Real.pi / 2 - β) + 2 * Real.pi by ring,
    M_periodic θ,
    show φ + 2 * Real.pi + Real.pi / 2 + β =
      (φ + Real.pi / 2 + β) + 2 * Real.pi by ring,
    M_periodic θ]

theorem B_periodic (θ β : ℝ) : Function.Periodic (B θ β) (2 * Real.pi) := by
  intro φ
  unfold B
  rw [Q_periodic β, P_periodic θ β]

theorem M_nonneg (θ γ : ℝ) : 0 ≤ M θ γ := by
  exact le_max_left _ _

theorem M_ge_leftVertex (θ γ : ℝ) :
    Real.cos (θ - γ) ≤ M θ γ := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem M_ge_rightVertex (θ γ : ℝ) :
    Real.cos (θ + Real.pi / 3 - γ) ≤ M θ γ := by
  exact (le_max_right _ _).trans (le_max_right _ _)

end Payoff

end

end MoserWorm

end


-- MoserWorm.Basic.Plane
section

namespace MoserWorm

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

abbrev Point := ℂ

def point (x y : ℝ) : Point := x + y * Complex.I

def px (p : Point) : ℝ := p.re

def py (p : Point) : ℝ := p.im

@[simp] theorem px_point (x y : ℝ) : px (point x y) = x := by
  simp [px, point]

@[simp] theorem py_point (x y : ℝ) : py (point x y) = y := by
  simp [py, point]

def unitVec (θ : ℝ) : Point :=
  ((θ : Real.Angle).toCircle : ℂ)

@[simp] theorem unitVec_re (θ : ℝ) : (unitVec θ).re = Real.cos θ := by
  simp [unitVec]

@[simp] theorem unitVec_im (θ : ℝ) : (unitVec θ).im = Real.sin θ := by
  simp [unitVec]

@[simp] theorem unitVec_zero : unitVec 0 = 1 := by
  simp [unitVec]

@[simp] theorem unitVec_add_pi (θ : ℝ) :
    unitVec (θ + Real.pi) = -unitVec θ := by
  apply Complex.ext
  · simp only [unitVec_re, Complex.neg_re, Real.cos_add, Real.cos_pi,
      Real.sin_pi, mul_neg, mul_one, mul_zero, sub_zero]
  · simp only [unitVec_im, Complex.neg_im, Real.sin_add, Real.cos_pi,
      Real.sin_pi, mul_neg, mul_one, mul_zero, add_zero]

@[simp] theorem norm_unitVec (θ : ℝ) : ‖unitVec θ‖ = 1 := by
  exact Circle.norm_coe _

def rot (θ : ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  _root_.rotation (θ : Real.Angle).toCircle

@[simp] theorem rot_apply (θ : ℝ) (p : Point) :
    rot θ p = unitVec θ * p := by
  rfl

@[simp] theorem rot_apply_unitVec (θ α : ℝ) :
    rot θ (unitVec α) = unitVec (α + θ) := by
  simp only [rot_apply, unitVec]
  rw [mul_comm, ← Circle.coe_mul, ← Real.Angle.toCircle_add]
  rfl

theorem rot_add_apply (α β : ℝ) (p : Point) :
    rot (α + β) p = rot α (rot β p) := by
  have h := rot_apply_unitVec α β
  rw [rot_apply, add_comm β α] at h
  simp only [rot_apply, ← h, mul_assoc]

@[simp] theorem rot_neg_apply_rot (α : ℝ) (p : Point) :
    rot (-α) (rot α p) = p := by
  rw [← rot_add_apply, neg_add_cancel]
  simp [rot_apply]

@[simp] theorem rot_pi (p : Point) : rot Real.pi p = -p := by
  rw [rot_apply]
  have hunit : unitVec Real.pi = (-1 : Point) := by
    apply Complex.ext <;> simp [unitVec]
  rw [hunit]
  ring

def reflectX : Point ≃ₗᵢ[ℝ] Point := Complex.conjLIE

@[simp] theorem reflectX_apply (p : Point) : reflectX p = star p := by
  rfl

@[simp] theorem reflectX_unitVec (θ : ℝ) :
    reflectX (unitVec θ) = unitVec (-θ) := by
  apply Complex.ext
  · simp
  · simp

@[simp] theorem reflectX_rot (θ : ℝ) (p : Point) :
    reflectX (rot θ p) = rot (-θ) (reflectX p) := by
  simp only [reflectX_apply, rot_apply, star_mul']
  rw [show star (unitVec θ) = unitVec (-θ) by
    simpa only [reflectX_apply] using reflectX_unitVec θ]

@[simp] theorem reflectX_reflectX (p : Point) :
    reflectX (reflectX p) = p := by
  simp [reflectX_apply]

def quarterTurnCW (p : Point) : Point := -Complex.I * p

end

end MoserWorm

end


-- MoserWorm.Polygon.AffineNull
section

namespace MoserWorm

noncomputable section

open MeasureTheory

def linearLevelSet (L : Point →ₗ[ℝ] ℝ) (c : ℝ) : Set Point :=
  {p | L p = c}

theorem linearLevelSet_eq_affineSubspace
    (L : Point →ₗ[ℝ] ℝ) {c : ℝ} {p : Point} (hp : L p = c) :
    linearLevelSet L c = (AffineSubspace.mk' p L.ker : Set Point) := by
  ext x
  simp [linearLevelSet, AffineSubspace.mem_mk', hp, sub_eq_zero]

theorem volume_linearLevelSet_eq_zero
    (L : Point →ₗ[ℝ] ℝ) (hL : L ≠ 0) (c : ℝ) :
    volume (linearLevelSet L c) = 0 := by
  by_cases hne : (linearLevelSet L c).Nonempty
  · obtain ⟨p, hp⟩ := hne
    rw [linearLevelSet_eq_affineSubspace L hp]
    apply Measure.addHaar_affineSubspace
    intro htop
    have hker : L.ker = ⊤ := by
      have := congrArg AffineSubspace.direction htop
      simpa using this
    exact hL (LinearMap.ker_eq_top.mp hker)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

theorem aedisjoint_of_forall_le_of_forall_ge
    {s t : Set Point} (L : Point →ₗ[ℝ] ℝ) (hL : L ≠ 0) (c : ℝ)
    (hs : ∀ x ∈ s, L x ≤ c) (ht : ∀ x ∈ t, c ≤ L x) :
    AEDisjoint volume s t := by
  apply measure_mono_null (t := linearLevelSet L c)
  · rintro x ⟨hxs, hxt⟩
    exact le_antisymm (hs x hxs) (ht x hxt)
  · exact volume_linearLevelSet_eq_zero L hL c

end

end MoserWorm

end


-- MoserWorm.Polygon.FiniteHull
section

namespace MoserWorm

noncomputable section

open scoped InnerProductSpace Pointwise RealInnerProductSpace

structure FiniteHull where
  vertices : Finset Point
  nonempty : vertices.Nonempty

namespace FiniteHull

noncomputable def translate (H : FiniteHull) (t : Point) : FiniteHull := by
  classical
  exact
    { vertices := H.vertices.image (fun p => t + p)
      nonempty := H.nonempty.image (fun p => t + p) }

def carrier (H : FiniteHull) : Set Point :=
  convexHull ℝ (H.vertices : Set Point)

theorem vertices_subset_carrier (H : FiniteHull) :
    (H.vertices : Set Point) ⊆ H.carrier := by
  exact subset_convexHull ℝ _

theorem carrier_convex (H : FiniteHull) : Convex ℝ H.carrier := by
  exact convex_convexHull ℝ _

theorem carrier_translate (H : FiniteHull) (t : Point) :
    (H.translate t).carrier = t +ᵥ H.carrier := by
  change
    convexHull ℝ ((H.vertices.image (fun p => t + p) : Finset Point) : Set Point) =
      t +ᵥ convexHull ℝ (H.vertices : Set Point)
  rw [show
      ((H.vertices.image (fun p => t + p) : Finset Point) : Set Point) =
        t +ᵥ (H.vertices : Set Point) by
    ext p
    simp only [Finset.coe_image, Set.mem_image, Set.mem_vadd_set]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩]
  exact convexHull_vadd t (H.vertices : Set Point)

end FiniteHull

def supportFunctional (u : Point) : Point →ₗ[ℝ] ℝ :=
  (innerₗ Point).flip u

@[simp] theorem supportFunctional_apply (u p : Point) :
    supportFunctional u p = ⟪p, u⟫_ℝ := by
  rfl

def supportHull (H : FiniteHull) (u : Point) : ℝ :=
  H.vertices.sup' H.nonempty (supportFunctional u)

theorem supportHull_nonneg_smul (H : FiniteHull) (u : Point) (a : ℝ)
    (ha : 0 ≤ a) :
    supportHull H (a • u) = a * supportHull H u := by
  classical
  unfold supportHull
  rw [Finset.mul₀_sup' ha]
  congr 1
  funext p
  simp [supportFunctional_apply]
  ring

theorem supportHull_translate (H : FiniteHull) (t u : Point) :
    supportHull (H.translate t) u = supportHull H u + ⟪t, u⟫_ℝ := by
  classical
  simp only [supportHull, FiniteHull.translate, Finset.sup'_image,
    Function.comp_apply, supportFunctional_apply, inner_add_left]
  simpa only [add_comm] using
    (Finset.sup'_add H.vertices (fun p => ⟪p, u⟫_ℝ) ⟪t, u⟫_ℝ H.nonempty).symm

theorem inner_le_supportHull_of_mem_vertices
    (H : FiniteHull) (u p : Point) (hp : p ∈ H.vertices) :
    ⟪p, u⟫_ℝ ≤ supportHull H u := by
  unfold supportHull
  exact Finset.le_sup' (supportFunctional u) hp

theorem inner_le_supportHull_of_mem_carrier
    (H : FiniteHull) (u p : Point) (hp : p ∈ H.carrier) :
    ⟪p, u⟫_ℝ ≤ supportHull H u := by
  have hconv : ConvexOn ℝ Set.univ (supportFunctional u) :=
    (supportFunctional u).convexOn convex_univ
  have hbound := hconv.le_sup_of_mem_convexHull
    (Set.subset_univ (H.vertices : Set Point)) hp
  simpa [FiniteHull.carrier, supportHull] using hbound

theorem supportHull_attained (H : FiniteHull) (u : Point) :
    ∃ p ∈ H.vertices, supportHull H u = ⟪p, u⟫_ℝ := by
  simpa [supportHull] using
    H.vertices.exists_mem_eq_sup' H.nonempty (supportFunctional u)

theorem supportHull_mono_of_carrier_subset
    {H R : FiniteHull} (u : Point) (hHR : H.carrier ⊆ R.carrier) :
    supportHull H u ≤ supportHull R u := by
  obtain ⟨p, hp, hsupport⟩ := supportHull_attained H u
  rw [hsupport]
  exact inner_le_supportHull_of_mem_carrier R u p
    (hHR (H.vertices_subset_carrier hp))

end

end MoserWorm

end


-- MoserWorm.Polygon.JointHull
section

namespace MoserWorm

noncomputable section

namespace FiniteHull

def join (H R : FiniteHull) : FiniteHull where
  vertices := H.vertices ∪ R.vertices
  nonempty := H.nonempty.mono Finset.subset_union_left

theorem carrier_subset_join_left (H R : FiniteHull) :
    H.carrier ⊆ (H.join R).carrier := by
  apply convexHull_mono
  intro p hp
  exact Finset.mem_union_left R.vertices hp

theorem carrier_subset_join_right (H R : FiniteHull) :
    R.carrier ⊆ (H.join R).carrier := by
  apply convexHull_mono
  intro p hp
  exact Finset.mem_union_right H.vertices hp

theorem join_carrier_subset
    (H R : FiniteHull) {C : Set Point} (hC : Convex ℝ C)
    (hH : H.carrier ⊆ C) (hR : R.carrier ⊆ C) :
    (H.join R).carrier ⊆ C := by
  apply convexHull_min _ hC
  intro p hp
  simp only [join, Finset.coe_union, Set.mem_union] at hp
  rcases hp with hp | hp
  · exact hH (H.vertices_subset_carrier hp)
  · exact hR (R.vertices_subset_carrier hp)

end FiniteHull

theorem supportHull_le_join_left (H R : FiniteHull) (u : Point) :
    supportHull H u ≤ supportHull (H.join R) u := by
  exact supportHull_mono_of_carrier_subset u (H.carrier_subset_join_left R)

theorem supportHull_le_join_right (H R : FiniteHull) (u : Point) :
    supportHull R u ≤ supportHull (H.join R) u := by
  exact supportHull_mono_of_carrier_subset u (H.carrier_subset_join_right R)

end

end MoserWorm

end


-- MoserWorm.Polygon.MixedSupport
section

namespace MoserWorm

noncomputable section

structure BoundaryWalk where
  n : ℕ
  vertex : Fin (n + 1) → Point

namespace BoundaryWalk

def edge (Q : BoundaryWalk) (i : Fin (Q.n + 1)) : Point :=
  Q.vertex (i + 1) - Q.vertex i

theorem sum_edge_eq_zero (Q : BoundaryWalk) :
    ∑ i, Q.edge i = 0 := by
  classical
  simp only [edge, Finset.sum_sub_distrib]
  have hshift :
      (∑ i, Q.vertex (i + 1)) = ∑ i, Q.vertex i := by
    exact
      Equiv.sum_comp (Equiv.addRight (1 : Fin (Q.n + 1))) Q.vertex
  rw [hshift, sub_self]

def rawOutNormal (Q : BoundaryWalk) (i : Fin (Q.n + 1)) : Point :=
  quarterTurnCW (Q.edge i)

theorem sum_rawOutNormal_eq_zero (Q : BoundaryWalk) :
    ∑ i, Q.rawOutNormal i = 0 := by
  simp only [rawOutNormal, quarterTurnCW, ← Finset.mul_sum]
  rw [Q.sum_edge_eq_zero, mul_zero]

abbrev translate (Q : BoundaryWalk) (t : Point) : BoundaryWalk :=
  { n := Q.n
    vertex := fun i => t + Q.vertex i }

@[simp] theorem translate_edge (Q : BoundaryWalk) (t : Point)
    (i : Fin (Q.n + 1)) :
    (Q.translate t).edge i = Q.edge i := by
  simp [translate, edge]

@[simp] theorem translate_rawOutNormal (Q : BoundaryWalk) (t : Point)
    (i : Fin (Q.n + 1)) :
    (Q.translate t).rawOutNormal i = Q.rawOutNormal i := by
  simp [rawOutNormal]

noncomputable def toFiniteHull (Q : BoundaryWalk) : FiniteHull := by
  classical
  exact
    { vertices := Finset.univ.image Q.vertex
      nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty }

theorem vertex_mem_toFiniteHull_carrier
    (Q : BoundaryWalk) (i : Fin (Q.n + 1)) :
    Q.vertex i ∈ Q.toFiniteHull.carrier := by
  apply Q.toFiniteHull.vertices_subset_carrier
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end BoundaryWalk

def mixedSupport (H : FiniteHull) (Q : BoundaryWalk) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, supportHull H (Q.rawOutNormal i)

theorem mixedSupport_translate_first
    (H : FiniteHull) (Q : BoundaryWalk) (t : Point) :
    mixedSupport (H.translate t) Q = mixedSupport H Q := by
  simp only [mixedSupport, supportHull_translate, Finset.sum_add_distrib]
  rw [← inner_sum, Q.sum_rawOutNormal_eq_zero]
  simp

@[simp] theorem mixedSupport_translate_second
    (H : FiniteHull) (Q : BoundaryWalk) (t : Point) :
    mixedSupport H (Q.translate t) = mixedSupport H Q := by
  simp [mixedSupport]

end

end MoserWorm

end


-- MoserWorm.Polygon.TriangleArea
section

namespace MoserWorm

noncomputable section

open MeasureTheory Set Pointwise

namespace TriangleAreaAux

abbrev Plane2 := EuclideanSpace ℝ (Fin 2)

def det2 (u v : Plane2) : ℝ := u 0 * v 1 - u 1 * v 0

def linOf (M : Matrix (Fin 2) (Fin 2) ℝ) : Plane2 →ₗ[ℝ] Plane2 :=
  Matrix.toLin (PiLp.basisFun 2 ℝ (Fin 2)) (PiLp.basisFun 2 ℝ (Fin 2)) M

@[simp] theorem linOf_apply (M : Matrix (Fin 2) (Fin 2) ℝ) (p : Plane2) (i : Fin 2) :
    linOf M p i = ∑ j, M i j * p j := rfl

@[simp] theorem det_linOf (M : Matrix (Fin 2) (Fin 2) ℝ) :
    LinearMap.det (linOf M) = M.det :=
  LinearMap.det_toLin _ _

theorem smul_add_smul_apply (s t : ℝ) (x y : Plane2) (i : Fin 2) :
    (s • x + t • y) i = s * x i + t * y i := by
  simp

def square : Set Plane2 :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}

theorem convex_square : Convex ℝ square := by
  rintro x ⟨hx0, hx1, hx2, hx3⟩ y ⟨hy0, hy1, hy2, hy3⟩ s t hs ht hst
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [smul_add_smul_apply] <;> nlinarith

theorem volume_square : volume square = 1 := by
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane2) ⁻¹' square = Set.Icc 0 1 := by
    ext x
    change
      (0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1) ↔
        ((∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ 1)
    simp only [Fin.forall_fin_two]
    tauto
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    (convex_square.nullMeasurableSet _), hpre, Real.volume_Icc_pi]
  simp

def diagonal : Submodule ℝ Plane2 where
  carrier := {p : Plane2 | p 0 = p 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change (a + b) 0 = (a + b) 1
    simp [show a 0 = a 1 from ha, show b 0 = b 1 from hb]
  smul_mem' := by
    intro c a ha
    change (c • a) 0 = (c • a) 1
    simp [show a 0 = a 1 from ha]

theorem volume_diagonal : volume {p : Plane2 | p 0 = p 1} = 0 := by
  have hne : diagonal ≠ ⊤ := by
    intro h
    have hm : (!₂[(1 : ℝ), 0] : Plane2) ∈ diagonal := by
      rw [h]
      trivial
    have : (1 : ℝ) = 0 := hm
    norm_num at this
  exact Measure.addHaar_submodule volume diagonal hne

def lowerTriangle : Set Plane2 :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ p 0 ∧ p 0 ≤ 1}

def upperTriangle : Set Plane2 :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ p 1 ∧ p 1 ≤ 1}

theorem convex_lowerTriangle : Convex ℝ lowerTriangle := by
  rintro x ⟨hx0, hx1, hx2⟩ y ⟨hy0, hy1, hy2⟩ s t hs ht hst
  refine ⟨?_, ?_, ?_⟩ <;> simp only [smul_add_smul_apply] <;> nlinarith

theorem convex_upperTriangle : Convex ℝ upperTriangle := by
  rintro x ⟨hx0, hx1, hx2⟩ y ⟨hy0, hy1, hy2⟩ s t hs ht hst
  refine ⟨?_, ?_, ?_⟩ <;> simp only [smul_add_smul_apply] <;> nlinarith

theorem lower_union_upper : lowerTriangle ∪ upperTriangle = square := by
  ext p
  constructor
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · exact ⟨by linarith, h2, h0, by linarith⟩
    · exact ⟨h0, by linarith, by linarith, h2⟩
  · rintro ⟨h0, h1, h2, h3⟩
    rcases le_total (p 1) (p 0) with h | h
    · exact Or.inl ⟨h2, h, h1⟩
    · exact Or.inr ⟨h0, h, h3⟩

theorem lower_inter_upper_subset_diagonal :
    lowerTriangle ∩ upperTriangle ⊆ {p : Plane2 | p 0 = p 1} := by
  rintro p ⟨⟨-, h1, -⟩, ⟨-, h2, -⟩⟩
  exact le_antisymm h2 h1

theorem swap_preimage_lower :
    (linOf !![0, 1; 1, 0] : Plane2 → Plane2) ⁻¹' lowerTriangle = upperTriangle := by
  ext p
  have e0 : (linOf !![(0 : ℝ), 1; 1, 0] p) 0 = p 1 := by
    simp [linOf_apply, Fin.sum_univ_two]
  have e1 : (linOf !![(0 : ℝ), 1; 1, 0] p) 1 = p 0 := by
    simp [linOf_apply, Fin.sum_univ_two]
  change
    (0 ≤ (linOf !![(0 : ℝ), 1; 1, 0] p) 1 ∧
      (linOf !![(0 : ℝ), 1; 1, 0] p) 1 ≤ (linOf !![(0 : ℝ), 1; 1, 0] p) 0 ∧
      (linOf !![(0 : ℝ), 1; 1, 0] p) 0 ≤ 1) ↔
      (0 ≤ p 0 ∧ p 0 ≤ p 1 ∧ p 1 ≤ 1)
  rw [e0, e1]

theorem volume_upperTriangle : volume upperTriangle = volume lowerTriangle := by
  have hdet : LinearMap.det (linOf !![(0 : ℝ), 1; 1, 0]) ≠ 0 := by
    rw [det_linOf, Matrix.det_fin_two]
    norm_num
  rw [← swap_preimage_lower, Measure.addHaar_preimage_linearMap volume hdet, det_linOf,
    Matrix.det_fin_two]
  norm_num

theorem lowerTriangle_subset_square : lowerTriangle ⊆ square := by
  rw [← lower_union_upper]
  exact Set.subset_union_left

theorem volume_lowerTriangle_ne_top : volume lowerTriangle ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [volume_square]; exact ENNReal.one_ne_top)
    (measure_mono lowerTriangle_subset_square)

theorem volume_lowerTriangle : volume lowerTriangle = ENNReal.ofReal (1 / 2) := by
  have hinter : volume (lowerTriangle ∩ upperTriangle) = 0 :=
    measure_mono_null lower_inter_upper_subset_diagonal volume_diagonal
  have hsum :
      volume (lowerTriangle ∪ upperTriangle) + volume (lowerTriangle ∩ upperTriangle) =
        volume lowerTriangle + volume upperTriangle :=
    measure_union_add_inter₀ lowerTriangle (convex_upperTriangle.nullMeasurableSet volume)
  rw [lower_union_upper, hinter, volume_square, volume_upperTriangle, add_zero] at hsum
  have hfin := volume_lowerTriangle_ne_top
  have htwo : (volume lowerTriangle).toReal + (volume lowerTriangle).toReal = 1 := by
    have := congrArg ENNReal.toReal hsum.symm
    rwa [ENNReal.toReal_add hfin hfin, ENNReal.toReal_one] at this
  have hhalf : (volume lowerTriangle).toReal = 1 / 2 := by
    linarith
  rw [← ENNReal.ofReal_toReal hfin, hhalf]

theorem convexHull_base :
    convexHull ℝ ({0, !₂[1, 0], !₂[1, 1]} : Set Plane2) = lowerTriangle := by
  refine subset_antisymm (convexHull_min ?_ convex_lowerTriangle) ?_
  · rintro x (rfl | rfl | rfl)
    · exact ⟨le_refl 0, le_refl 0, zero_le_one⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
  · rintro p ⟨h0, h1, h2⟩
    have hsum :
        ∑ i : Fin 3, (![1 - p 0, p 0 - p 1, p 1] : Fin 3 → ℝ) i •
          (![0, !₂[1, 0], !₂[1, 1]] : Fin 3 → Plane2) i = p := by
      ext i
      fin_cases i <;> simp [Fin.sum_univ_three]
    refine hsum ▸ (convex_convexHull ℝ _).sum_mem ?_ ?_ ?_
    · intro i _
      fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_three]
    · intro i _
      fin_cases i <;> exact subset_convexHull ℝ _ (by simp)

theorem volume_convexHull_zero (u v : Plane2) :
    volume (convexHull ℝ ({0, u, v} : Set Plane2)) =
      ENNReal.ofReal (|det2 u v| / 2) := by
  set M : Matrix (Fin 2) (Fin 2) ℝ :=
    !![u 0, v 0 - u 0; u 1, v 1 - u 1] with hM
  have hL0 : linOf M 0 = 0 := map_zero _
  have hL1 : linOf M !₂[1, 0] = u := by
    ext i
    fin_cases i <;> simp [hM, linOf_apply, Fin.sum_univ_two]
  have hL2 : linOf M !₂[1, 1] = v := by
    ext i
    fin_cases i <;> simp [hM, linOf_apply, Fin.sum_univ_two]
  have himg :
      (linOf M) '' ({0, !₂[1, 0], !₂[1, 1]} : Set Plane2) = {0, u, v} := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hL0, hL1, hL2]
  have hdet : LinearMap.det (linOf M) = det2 u v := by
    rw [det_linOf, hM, Matrix.det_fin_two_of, det2]
    ring
  rw [← himg, ← LinearMap.image_convexHull, convexHull_base,
    Measure.addHaar_image_linearMap, volume_lowerTriangle, hdet,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

theorem volume_convexHull_three (a b c : Plane2) :
    volume (convexHull ℝ ({a, b, c} : Set Plane2)) =
      ENNReal.ofReal (|det2 (b - a) (c - a)| / 2) := by
  have hset : ({a, b, c} : Set Plane2) = a +ᵥ ({0, b - a, c - a} : Set Plane2) := by
    rw [← Set.image_vadd]
    simp [Set.image_insert_eq]
  rw [hset, convexHull_vadd, measure_vadd, volume_convexHull_zero]

end TriangleAreaAux

def detC (u v : Point) : ℝ := u.re * v.im - u.im * v.re

theorem volume_convexHull_three (a b c : Point) :
    volume (convexHull ℝ ({a, b, c} : Set Point)) =
      ENNReal.ofReal (|detC (b - a) (c - a)| / 2) := by
  let e := Complex.orthonormalBasisOneI.repr
  have hpre :
      e.symm ⁻¹' convexHull ℝ ({a, b, c} : Set Point) =
        e '' convexHull ℝ ({a, b, c} : Set Point) := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hmeasure :
      volume (e '' convexHull ℝ ({a, b, c} : Set Point)) =
        volume (convexHull ℝ ({a, b, c} : Set Point)) := by
    rw [← hpre]
    exact Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
      ((convex_convexHull ℝ _).nullMeasurableSet volume)
  have himage :
      e '' convexHull ℝ ({a, b, c} : Set Point) =
        convexHull ℝ ({e a, e b, e c} : Set TriangleAreaAux.Plane2) := by
    change e.toLinearEquiv.toLinearMap '' convexHull ℝ ({a, b, c} : Set Point) = _
    rw [e.toLinearEquiv.toLinearMap.image_convexHull]
    simp [Set.image_insert_eq]
  rw [← hmeasure, himage, TriangleAreaAux.volume_convexHull_three]
  simp [TriangleAreaAux.det2, detC, e]

theorem volume_convexHull_three_toReal (a b c : Point) :
    (volume (convexHull ℝ ({a, b, c} : Set Point))).toReal =
      |detC (b - a) (c - a)| / 2 := by
  rw [volume_convexHull_three, ENNReal.toReal_ofReal (by positivity)]

theorem volume_convexHull_three_ne_top (a b c : Point) :
    volume (convexHull ℝ ({a, b, c} : Set Point)) ≠ ⊤ := by
  rw [volume_convexHull_three]
  exact ENNReal.ofReal_ne_top

end

end MoserWorm

end


-- MoserWorm.Polygon.SupportCap
section

namespace MoserWorm

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace FiniteHull

noncomputable def supportPoint (H : FiniteHull) (u : Point) : Point :=
  Classical.choose (supportHull_attained H u)

theorem supportPoint_mem_vertices (H : FiniteHull) (u : Point) :
    H.supportPoint u ∈ H.vertices :=
  (Classical.choose_spec (supportHull_attained H u)).1

theorem supportHull_eq_inner_supportPoint (H : FiniteHull) (u : Point) :
    supportHull H u = ⟪H.supportPoint u, u⟫_ℝ :=
  (Classical.choose_spec (supportHull_attained H u)).2

end FiniteHull

theorem detC_eq_neg_inner_quarterTurnCW (u v : Point) :
    detC u v = -⟪v, quarterTurnCW u⟫_ℝ := by
  rw [Complex.inner]
  simp [detC, quarterTurnCW]
  ring

def supportExcess (H : FiniteHull) (Q : BoundaryWalk)
    (i : Fin (Q.n + 1)) : ℝ :=
  supportHull H (Q.rawOutNormal i) -
    ⟪Q.vertex i, Q.rawOutNormal i⟫_ℝ

def supportCapTriangle (H : FiniteHull) (Q : BoundaryWalk)
    (i : Fin (Q.n + 1)) : Set Point :=
  convexHull ℝ
    {Q.vertex i, Q.vertex (i + 1), H.supportPoint (Q.rawOutNormal i)}

theorem supportPoint_sub_vertex_inner_rawOutNormal
    (H : FiniteHull) (Q : BoundaryWalk) (i : Fin (Q.n + 1)) :
    ⟪H.supportPoint (Q.rawOutNormal i) - Q.vertex i,
      Q.rawOutNormal i⟫_ℝ = supportExcess H Q i := by
  rw [inner_sub_left, ← H.supportHull_eq_inner_supportPoint]
  rfl

theorem supportCapTriangle_volume_toReal
    (H : FiniteHull) (Q : BoundaryWalk) (i : Fin (Q.n + 1)) :
    (volume (supportCapTriangle H Q i)).toReal =
      |supportExcess H Q i| / 2 := by
  rw [supportCapTriangle, volume_convexHull_three_toReal]
  change
    |detC (Q.edge i)
      (H.supportPoint (Q.rawOutNormal i) - Q.vertex i)| / 2 = _
  rw [detC_eq_neg_inner_quarterTurnCW,
    show quarterTurnCW (Q.edge i) = Q.rawOutNormal i by rfl,
    supportPoint_sub_vertex_inner_rawOutNormal, abs_neg]

theorem supportCapTriangle_volume_toReal_of_nonneg
    (H : FiniteHull) (Q : BoundaryWalk) (i : Fin (Q.n + 1))
    (hactive : 0 ≤ supportExcess H Q i) :
    (volume (supportCapTriangle H Q i)).toReal =
      supportExcess H Q i / 2 := by
  rw [supportCapTriangle_volume_toReal, abs_of_nonneg hactive]

theorem supportCapTriangle_subset_of_convex
    (H : FiniteHull) (Q : BoundaryWalk) (i : Fin (Q.n + 1))
    {C : Set Point} (hC : Convex ℝ C)
    (hH : H.carrier ⊆ C) (hQ : Q.toFiniteHull.carrier ⊆ C) :
    supportCapTriangle H Q i ⊆ C := by
  apply convexHull_min _ hC
  rintro p (rfl | rfl | rfl)
  · exact hQ (Q.vertex_mem_toFiniteHull_carrier i)
  · exact hQ (Q.vertex_mem_toFiniteHull_carrier (i + 1))
  · exact hH (H.vertices_subset_carrier (H.supportPoint_mem_vertices _))

end

end MoserWorm

end


-- MoserWorm.Polygon.PositiveBoundary
section

namespace MoserWorm

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

structure PositiveSupportBoundary where
  walk : BoundaryWalk
  center : Point
  center_mem : center ∈ walk.toFiniteHull.carrier
  edge_support : ∀ i p, p ∈ walk.toFiniteHull.carrier →
    ⟪p, walk.rawOutNormal i⟫_ℝ ≤
      ⟪walk.vertex i, walk.rawOutNormal i⟫_ℝ
  center_strict : ∀ i,
    ⟪center, walk.rawOutNormal i⟫_ℝ <
      ⟪walk.vertex i, walk.rawOutNormal i⟫_ℝ
  normal_ne_zero : ∀ i, walk.rawOutNormal i ≠ 0
  distinct_positive_rays : ∀ {i j}, i ≠ j → ∀ {r s : ℝ},
    0 < r → 0 < s →
      r • walk.rawOutNormal i ≠ s • walk.rawOutNormal j

namespace PositiveSupportBoundary

def fanSlack (P : PositiveSupportBoundary) (i : Fin (P.walk.n + 1)) : ℝ :=
  ⟪P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ -
    ⟪P.center, P.walk.rawOutNormal i⟫_ℝ

theorem fanSlack_pos (P : PositiveSupportBoundary)
    (i : Fin (P.walk.n + 1)) : 0 < P.fanSlack i := by
  exact sub_pos.mpr (P.center_strict i)

def fanTriangle (P : PositiveSupportBoundary)
    (i : Fin (P.walk.n + 1)) : Set Point :=
  convexHull ℝ {P.center, P.walk.vertex i, P.walk.vertex (i + 1)}

theorem detC_fan_eq_fanSlack (P : PositiveSupportBoundary)
    (i : Fin (P.walk.n + 1)) :
    detC (P.walk.vertex i - P.center)
      (P.walk.vertex (i + 1) - P.center) = P.fanSlack i := by
  simp [detC, fanSlack, BoundaryWalk.rawOutNormal, BoundaryWalk.edge,
    quarterTurnCW, Complex.inner]
  ring

theorem fanTriangle_volume_toReal (P : PositiveSupportBoundary)
    (i : Fin (P.walk.n + 1)) :
    (volume (P.fanTriangle i)).toReal = P.fanSlack i / 2 := by
  rw [fanTriangle, volume_convexHull_three_toReal,
    P.detC_fan_eq_fanSlack i, abs_of_pos (P.fanSlack_pos i)]

theorem fanTriangle_subset_carrier (P : PositiveSupportBoundary)
    (i : Fin (P.walk.n + 1)) :
    P.fanTriangle i ⊆ P.walk.toFiniteHull.carrier := by
  apply convexHull_min _ P.walk.toFiniteHull.carrier_convex
  rintro p (rfl | rfl | rfl)
  · exact P.center_mem
  · exact P.walk.vertex_mem_toFiniteHull_carrier i
  · exact P.walk.vertex_mem_toFiniteHull_carrier (i + 1)

end PositiveSupportBoundary

end

end MoserWorm

end


-- MoserWorm.Polygon.PackingSeparators
section

namespace MoserWorm

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace PositiveSupportBoundary

def fanSeparatorNormal (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) : Point :=
  P.fanSlack i • P.walk.rawOutNormal j -
    P.fanSlack j • P.walk.rawOutNormal i

def fanSeparatorLevel (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) : ℝ :=
  P.fanSlack i * ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ -
    P.fanSlack j * ⟪P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ

@[simp] theorem supportFunctional_fanSeparatorNormal (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) (x : Point) :
    supportFunctional (P.fanSeparatorNormal i j) x =
      P.fanSlack i * ⟪x, P.walk.rawOutNormal j⟫_ℝ -
        P.fanSlack j * ⟪x, P.walk.rawOutNormal i⟫_ℝ := by
  simp [supportFunctional_apply, fanSeparatorNormal, Complex.inner]
  ring

theorem fanSeparatorNormal_ne_zero (P : PositiveSupportBoundary)
    {i j : Fin (P.walk.n + 1)} (hij : i ≠ j) :
    P.fanSeparatorNormal i j ≠ 0 := by
  intro hzero
  have heq :
      P.fanSlack j • P.walk.rawOutNormal i =
        P.fanSlack i • P.walk.rawOutNormal j := by
    exact (sub_eq_zero.mp hzero).symm
  exact P.distinct_positive_rays hij (P.fanSlack_pos j) (P.fanSlack_pos i) heq

theorem vertex_succ_inner_rawOutNormal (P : PositiveSupportBoundary)
    (i : Fin (P.walk.n + 1)) :
    ⟪P.walk.vertex (i + 1), P.walk.rawOutNormal i⟫_ℝ =
      ⟪P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ := by
  simp [BoundaryWalk.rawOutNormal, BoundaryWalk.edge, quarterTurnCW, Complex.inner]
  ring

private theorem fanSeparator_le_at_center (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) :
    supportFunctional (P.fanSeparatorNormal i j) P.center ≤
      P.fanSeparatorLevel i j := by
  rw [P.supportFunctional_fanSeparatorNormal]
  unfold fanSeparatorLevel fanSlack
  exact le_of_eq (by ring)

private theorem fanSeparator_le_at_leftVertex (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) :
    supportFunctional (P.fanSeparatorNormal i j) (P.walk.vertex i) ≤
      P.fanSeparatorLevel i j := by
  have hsup := P.edge_support j (P.walk.vertex i)
    (P.walk.vertex_mem_toFiniteHull_carrier i)
  have hmul := mul_le_mul_of_nonneg_left hsup (le_of_lt (P.fanSlack_pos i))
  rw [P.supportFunctional_fanSeparatorNormal]
  exact sub_le_sub_right hmul _

private theorem fanSeparator_le_at_leftSucc (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) :
    supportFunctional (P.fanSeparatorNormal i j) (P.walk.vertex (i + 1)) ≤
      P.fanSeparatorLevel i j := by
  have hsup := P.edge_support j (P.walk.vertex (i + 1))
    (P.walk.vertex_mem_toFiniteHull_carrier (i + 1))
  have hmul := mul_le_mul_of_nonneg_left hsup (le_of_lt (P.fanSlack_pos i))
  have hi := P.vertex_succ_inner_rawOutNormal i
  rw [P.supportFunctional_fanSeparatorNormal, hi]
  exact sub_le_sub_right hmul _

theorem fanSeparator_le_on_left (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) :
    ∀ x ∈ P.fanTriangle i,
      supportFunctional (P.fanSeparatorNormal i j) x ≤
        P.fanSeparatorLevel i j := by
  apply convexHull_min _
    (convex_halfSpace_le (supportFunctional _).isLinear _)
  rintro x (rfl | rfl | rfl)
  · exact P.fanSeparator_le_at_center i j
  · exact P.fanSeparator_le_at_leftVertex i j
  · exact P.fanSeparator_le_at_leftSucc i j

theorem fanSeparator_ge_on_right (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) :
    ∀ x ∈ P.fanTriangle j,
      P.fanSeparatorLevel i j ≤
        supportFunctional (P.fanSeparatorNormal i j) x := by
  have hleft := P.fanSeparator_le_on_left j i
  intro x hx
  have h := hleft x hx
  rw [P.supportFunctional_fanSeparatorNormal] at h ⊢
  unfold fanSeparatorLevel at h ⊢
  linarith

theorem supportFunctional_ne_zero_of_vector_ne_zero
    {u : Point} (hu : u ≠ 0) : supportFunctional u ≠ 0 := by
  intro hzero
  have hinner : ⟪u, u⟫_ℝ = 0 := by
    have hfun := LinearMap.congr_fun hzero u
    simpa using hfun
  exact hu (inner_self_eq_zero.mp hinner)

theorem fanTriangles_aedisjoint (P : PositiveSupportBoundary)
    {i j : Fin (P.walk.n + 1)} (hij : i ≠ j) :
    AEDisjoint volume (P.fanTriangle i) (P.fanTriangle j) := by
  apply aedisjoint_of_forall_le_of_forall_ge
    (supportFunctional (P.fanSeparatorNormal i j))
    (supportFunctional_ne_zero_of_vector_ne_zero
      (P.fanSeparatorNormal_ne_zero hij))
    (P.fanSeparatorLevel i j)
  · exact P.fanSeparator_le_on_left i j
  · exact P.fanSeparator_ge_on_right i j

def capSeparatorNormal (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1)) : Point :=
  supportExcess H P.walk i • P.walk.rawOutNormal j -
    supportExcess H P.walk j • P.walk.rawOutNormal i

def capSeparatorLevel (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1)) : ℝ :=
  supportExcess H P.walk i *
      ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ -
    supportExcess H P.walk j *
      ⟪P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ

@[simp] theorem supportFunctional_capSeparatorNormal
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1)) (x : Point) :
    supportFunctional (P.capSeparatorNormal H i j) x =
      supportExcess H P.walk i * ⟪x, P.walk.rawOutNormal j⟫_ℝ -
        supportExcess H P.walk j * ⟪x, P.walk.rawOutNormal i⟫_ℝ := by
  simp [supportFunctional_apply, capSeparatorNormal, Complex.inner]
  ring

theorem capSeparatorNormal_ne_zero
    (P : PositiveSupportBoundary) (H : FiniteHull)
    {i j : Fin (P.walk.n + 1)} (hij : i ≠ j)
    (hi : 0 < supportExcess H P.walk i)
    (hj : 0 < supportExcess H P.walk j) :
    P.capSeparatorNormal H i j ≠ 0 := by
  intro hzero
  have heq :
      supportExcess H P.walk j • P.walk.rawOutNormal i =
        supportExcess H P.walk i • P.walk.rawOutNormal j := by
    exact (sub_eq_zero.mp hzero).symm
  exact P.distinct_positive_rays hij hj hi heq

private theorem capSeparator_le_at_leftVertex
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1))
    (hi : 0 < supportExcess H P.walk i) :
    supportFunctional (P.capSeparatorNormal H i j) (P.walk.vertex i) ≤
      P.capSeparatorLevel H i j := by
  have hsup := P.edge_support j (P.walk.vertex i)
    (P.walk.vertex_mem_toFiniteHull_carrier i)
  have hmul := mul_le_mul_of_nonneg_left hsup (le_of_lt hi)
  rw [P.supportFunctional_capSeparatorNormal]
  exact sub_le_sub_right hmul _

private theorem capSeparator_le_at_leftSucc
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1))
    (hi : 0 < supportExcess H P.walk i) :
    supportFunctional (P.capSeparatorNormal H i j) (P.walk.vertex (i + 1)) ≤
      P.capSeparatorLevel H i j := by
  have hsup := P.edge_support j (P.walk.vertex (i + 1))
    (P.walk.vertex_mem_toFiniteHull_carrier (i + 1))
  have hmul := mul_le_mul_of_nonneg_left hsup (le_of_lt hi)
  have hii := P.vertex_succ_inner_rawOutNormal i
  rw [P.supportFunctional_capSeparatorNormal, hii]
  exact sub_le_sub_right hmul _

private theorem capSeparator_le_at_leftApex
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1))
    (hi : 0 < supportExcess H P.walk i) :
    supportFunctional (P.capSeparatorNormal H i j)
        (H.supportPoint (P.walk.rawOutNormal i)) ≤
      P.capSeparatorLevel H i j := by
  have hsup := inner_le_supportHull_of_mem_vertices H
    (P.walk.rawOutNormal j) (H.supportPoint (P.walk.rawOutNormal i))
    (H.supportPoint_mem_vertices (P.walk.rawOutNormal i))
  have hmul := mul_le_mul_of_nonneg_left hsup (le_of_lt hi)
  rw [P.supportFunctional_capSeparatorNormal,
    ← H.supportHull_eq_inner_supportPoint]
  unfold supportExcess at hmul
  unfold capSeparatorLevel supportExcess
  nlinarith

theorem capSeparator_le_on_left
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1))
    (hi : 0 < supportExcess H P.walk i) :
    ∀ x ∈ supportCapTriangle H P.walk i,
      supportFunctional (P.capSeparatorNormal H i j) x ≤
        P.capSeparatorLevel H i j := by
  apply convexHull_min _
    (convex_halfSpace_le (supportFunctional _).isLinear _)
  rintro x (rfl | rfl | rfl)
  · exact P.capSeparator_le_at_leftVertex H i j hi
  · exact P.capSeparator_le_at_leftSucc H i j hi
  · exact P.capSeparator_le_at_leftApex H i j hi

theorem capSeparator_ge_on_right
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1))
    (hj : 0 < supportExcess H P.walk j) :
    ∀ x ∈ supportCapTriangle H P.walk j,
      P.capSeparatorLevel H i j ≤
        supportFunctional (P.capSeparatorNormal H i j) x := by
  have hleft := P.capSeparator_le_on_left H j i hj
  intro x hx
  have h := hleft x hx
  rw [P.supportFunctional_capSeparatorNormal] at h ⊢
  unfold capSeparatorLevel at h ⊢
  linarith

theorem supportCapTriangles_aedisjoint
    (P : PositiveSupportBoundary) (H : FiniteHull)
    {i j : Fin (P.walk.n + 1)} (hij : i ≠ j)
    (hi : 0 < supportExcess H P.walk i)
    (hj : 0 < supportExcess H P.walk j) :
    AEDisjoint volume (supportCapTriangle H P.walk i)
      (supportCapTriangle H P.walk j) := by
  apply aedisjoint_of_forall_le_of_forall_ge
    (supportFunctional (P.capSeparatorNormal H i j))
    (supportFunctional_ne_zero_of_vector_ne_zero
      (P.capSeparatorNormal_ne_zero H hij hi hj))
    (P.capSeparatorLevel H i j)
  · exact P.capSeparator_le_on_left H i j hi
  · exact P.capSeparator_ge_on_right H i j hj

theorem fan_le_edgeSupport (P : PositiveSupportBoundary)
    (i j : Fin (P.walk.n + 1)) :
    ∀ x ∈ P.fanTriangle i,
      supportFunctional (P.walk.rawOutNormal j) x ≤
        ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ := by
  intro x hx
  rw [supportFunctional_apply]
  exact P.edge_support j x (P.fanTriangle_subset_carrier i hx)

private theorem cap_ge_edgeSupport_at_leftVertex
    (P : PositiveSupportBoundary) (j : Fin (P.walk.n + 1)) :
    ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ ≤
      supportFunctional (P.walk.rawOutNormal j) (P.walk.vertex j) := by
  simp

private theorem cap_ge_edgeSupport_at_leftSucc
    (P : PositiveSupportBoundary) (j : Fin (P.walk.n + 1)) :
    ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ ≤
      supportFunctional (P.walk.rawOutNormal j) (P.walk.vertex (j + 1)) := by
  rw [supportFunctional_apply, P.vertex_succ_inner_rawOutNormal]

private theorem cap_ge_edgeSupport_at_apex
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (j : Fin (P.walk.n + 1))
    (hj : 0 < supportExcess H P.walk j) :
    ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ ≤
      supportFunctional (P.walk.rawOutNormal j)
        (H.supportPoint (P.walk.rawOutNormal j)) := by
  rw [supportFunctional_apply, ← H.supportHull_eq_inner_supportPoint]
  unfold supportExcess at hj
  linarith

theorem supportCap_ge_edgeSupport
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (j : Fin (P.walk.n + 1))
    (hj : 0 < supportExcess H P.walk j) :
    ∀ x ∈ supportCapTriangle H P.walk j,
      ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ ≤
        supportFunctional (P.walk.rawOutNormal j) x := by
  apply convexHull_min _
    (convex_halfSpace_ge (supportFunctional _).isLinear _)
  rintro x (rfl | rfl | rfl)
  · exact P.cap_ge_edgeSupport_at_leftVertex j
  · exact P.cap_ge_edgeSupport_at_leftSucc j
  · exact P.cap_ge_edgeSupport_at_apex H j hj

theorem fan_supportCap_aedisjoint
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i j : Fin (P.walk.n + 1))
    (hj : 0 < supportExcess H P.walk j) :
    AEDisjoint volume (P.fanTriangle i)
      (supportCapTriangle H P.walk j) := by
  apply aedisjoint_of_forall_le_of_forall_ge
    (supportFunctional (P.walk.rawOutNormal j))
    (supportFunctional_ne_zero_of_vector_ne_zero (P.normal_ne_zero j))
    ⟪P.walk.vertex j, P.walk.rawOutNormal j⟫_ℝ
  · exact P.fan_le_edgeSupport i j
  · exact P.supportCap_ge_edgeSupport H j hj

abbrev ActiveCapIndex (P : PositiveSupportBoundary) (H : FiniteHull) :=
  {i : Fin (P.walk.n + 1) // 0 < supportExcess H P.walk i}

abbrev PackingIndex (P : PositiveSupportBoundary) (H : FiniteHull) :=
  Fin (P.walk.n + 1) ⊕ P.ActiveCapIndex H

def packingPiece (P : PositiveSupportBoundary) (H : FiniteHull) :
    P.PackingIndex H → Set Point
  | Sum.inl i => P.fanTriangle i
  | Sum.inr i => supportCapTriangle H P.walk i.1

theorem packingPiece_pairwise_aedisjoint
    (P : PositiveSupportBoundary) (H : FiniteHull) :
    Pairwise fun i j =>
      AEDisjoint volume (P.packingPiece H i) (P.packingPiece H j) := by
  rintro (i | i) (j | j) hne
  · have hij : i ≠ j := by
      intro hij
      subst j
      exact hne rfl
    simpa [packingPiece] using P.fanTriangles_aedisjoint hij
  · simpa [packingPiece] using P.fan_supportCap_aedisjoint H i j.1 j.2
  · simpa [packingPiece] using
      (P.fan_supportCap_aedisjoint H j i.1 i.2).symm
  · have hij : i.1 ≠ j.1 := by
      intro hij
      apply hne
      exact congrArg Sum.inr (Subtype.ext hij)
    simpa [packingPiece] using
      P.supportCapTriangles_aedisjoint H hij i.2 j.2

end PositiveSupportBoundary

end

end MoserWorm

end


-- MoserWorm.Polygon.FiniteEnvelope
section

namespace MoserWorm

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace PositiveSupportBoundary

def positiveSupportExcess (P : PositiveSupportBoundary) (H : FiniteHull)
    (i : Fin (P.walk.n + 1)) : ℝ :=
  if 0 < supportExcess H P.walk i then supportExcess H P.walk i else 0

theorem supportHull_le_edgeLevel_add_positiveSupportExcess
    (P : PositiveSupportBoundary) (H : FiniteHull)
    (i : Fin (P.walk.n + 1)) :
    supportHull H (P.walk.rawOutNormal i) ≤
      ⟪P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ +
        P.positiveSupportExcess H i := by
  by_cases hactive : 0 < supportExcess H P.walk i
  · rw [positiveSupportExcess, if_pos hactive]
    unfold supportExcess
    ring_nf
    exact le_rfl
  · rw [positiveSupportExcess, if_neg hactive, add_zero]
    unfold supportExcess at hactive
    linarith

theorem sum_positiveSupportExcess_eq_sum_active
    (P : PositiveSupportBoundary) (H : FiniteHull) :
    (∑ i, P.positiveSupportExcess H i) =
      ∑ i : P.ActiveCapIndex H, supportExcess H P.walk i.1 := by
  classical
  rw [show (Finset.univ : Finset (P.ActiveCapIndex H)) =
      (Finset.univ : Finset (Fin (P.walk.n + 1))).subtype
        (fun i ↦ 0 < supportExcess H P.walk i) by ext; simp]
  rw [Finset.sum_subtype_eq_sum_filter]
  exact
    (Finset.sum_filter (fun i ↦ 0 < supportExcess H P.walk i)
      (fun i ↦ supportExcess H P.walk i)).symm

theorem sum_fanSlack_eq_sum_edgeLevel (P : PositiveSupportBoundary) :
    (∑ i, P.fanSlack i) =
      ∑ i, ⟪P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ := by
  simp only [fanSlack, Finset.sum_sub_distrib]
  have hcenter :
      (∑ i, ⟪P.center, P.walk.rawOutNormal i⟫_ℝ) = 0 := by
    rw [← inner_sum, P.walk.sum_rawOutNormal_eq_zero]
    simp
  rw [hcenter, sub_zero]

theorem mixedSupport_le_packingData
    (P : PositiveSupportBoundary) (H : FiniteHull) :
    mixedSupport H P.walk ≤
      (1 / 2 : ℝ) *
        ((∑ i, P.fanSlack i) +
          ∑ i : P.ActiveCapIndex H, supportExcess H P.walk i.1) := by
  rw [mixedSupport, P.sum_fanSlack_eq_sum_edgeLevel,
    ← P.sum_positiveSupportExcess_eq_sum_active H,
    ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i hi
  exact P.supportHull_le_edgeLevel_add_positiveSupportExcess H i

theorem packingPiece_volumeReal (P : PositiveSupportBoundary) (H : FiniteHull)
    (k : P.PackingIndex H) :
    volume.real (P.packingPiece H k) =
      Sum.elim (fun i ↦ P.fanSlack i / 2)
        (fun i ↦ supportExcess H P.walk i.1 / 2) k := by
  cases k with
  | inl i =>
      simpa [packingPiece, Measure.real] using P.fanTriangle_volume_toReal i
  | inr i =>
      simpa [packingPiece, Measure.real] using
        supportCapTriangle_volume_toReal_of_nonneg H P.walk i.1
          (le_of_lt i.2)

theorem sum_packingPiece_volumeReal (P : PositiveSupportBoundary)
    (H : FiniteHull) :
    (∑ k : P.PackingIndex H, volume.real (P.packingPiece H k)) =
      (1 / 2 : ℝ) *
        ((∑ i, P.fanSlack i) +
          ∑ i : P.ActiveCapIndex H, supportExcess H P.walk i.1) := by
  simp_rw [P.packingPiece_volumeReal H]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

theorem packingPiece_nullMeasurable (P : PositiveSupportBoundary)
    (H : FiniteHull) (k : P.PackingIndex H) :
    NullMeasurableSet (P.packingPiece H k) volume := by
  cases k with
  | inl i =>
      have hs :
          ({P.center, P.walk.vertex i,
            P.walk.vertex (i + 1)} : Set Point).Finite := by simp
      exact (hs.isCompact_convexHull ℝ).measurableSet.nullMeasurableSet
  | inr i =>
      have hs :
          ({P.walk.vertex i.1, P.walk.vertex (i.1 + 1),
            H.supportPoint (P.walk.rawOutNormal i.1)} : Set Point).Finite := by simp
      exact (hs.isCompact_convexHull ℝ).measurableSet.nullMeasurableSet

theorem packingPiece_volume_ne_top (P : PositiveSupportBoundary)
    (H : FiniteHull) (k : P.PackingIndex H) :
    volume (P.packingPiece H k) ≠ ⊤ := by
  cases k with
  | inl i =>
      simpa [packingPiece, fanTriangle] using
        volume_convexHull_three_ne_top P.center (P.walk.vertex i)
          (P.walk.vertex (i + 1))
  | inr i =>
      simpa [packingPiece, supportCapTriangle] using
        volume_convexHull_three_ne_top (P.walk.vertex i.1)
          (P.walk.vertex (i.1 + 1))
          (H.supportPoint (P.walk.rawOutNormal i.1))

theorem packingUnion_volumeReal (P : PositiveSupportBoundary)
    (H : FiniteHull) :
    volume.real (⋃ k, P.packingPiece H k) =
      ∑ k : P.PackingIndex H, volume.real (P.packingPiece H k) := by
  classical
  have hpairwise :
      Set.Pairwise
        (↑(Finset.univ : Finset (P.PackingIndex H)))
        (fun i j ↦
          AEDisjoint volume (P.packingPiece H i) (P.packingPiece H j)) := by
    intro i hi j hj hij
    exact P.packingPiece_pairwise_aedisjoint H hij
  simpa using
    (measureReal_biUnion_finset₀ hpairwise
      (fun k hk ↦ P.packingPiece_nullMeasurable H k)
      (fun k hk ↦ P.packingPiece_volume_ne_top H k))

theorem packingUnion_subset_of_convex
    (P : PositiveSupportBoundary) (H : FiniteHull)
    {C : Set Point} (hC : Convex ℝ C)
    (hH : H.carrier ⊆ C)
    (hP : P.walk.toFiniteHull.carrier ⊆ C) :
    (⋃ k, P.packingPiece H k) ⊆ C := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hx⟩ := hx
  cases k with
  | inl i =>
      exact hP (P.fanTriangle_subset_carrier i hx)
  | inr i =>
      exact supportCapTriangle_subset_of_convex H P.walk i.1 hC hH hP hx

theorem mixedSupport_le_volumeReal_of_positiveSupportBoundary
    (P : PositiveSupportBoundary) (H : FiniteHull)
    {C : Set Point} (hC : Convex ℝ C)
    (hCfinite : volume C ≠ ⊤)
    (hH : H.carrier ⊆ C)
    (hP : P.walk.toFiniteHull.carrier ⊆ C) :
    mixedSupport H P.walk ≤ volume.real C := by
  calc
    mixedSupport H P.walk ≤
        (1 / 2 : ℝ) *
          ((∑ i, P.fanSlack i) +
            ∑ i : P.ActiveCapIndex H, supportExcess H P.walk i.1) :=
      P.mixedSupport_le_packingData H
    _ = ∑ k : P.PackingIndex H, volume.real (P.packingPiece H k) :=
      (P.sum_packingPiece_volumeReal H).symm
    _ = volume.real (⋃ k, P.packingPiece H k) :=
      (P.packingUnion_volumeReal H).symm
    _ ≤ volume.real C :=
      measureReal_mono (P.packingUnion_subset_of_convex H hC hH hP) hCfinite

end PositiveSupportBoundary

end

end MoserWorm

end


-- MoserWorm.Polygon.PositiveBoundaryMotion
section

namespace MoserWorm

noncomputable section

open scoped InnerProductSpace Pointwise RealInnerProductSpace

namespace BoundaryWalk

abbrev rotate (Q : BoundaryWalk) (θ : ℝ) : BoundaryWalk :=
  { n := Q.n
    vertex := fun i ↦ rot θ (Q.vertex i) }

@[simp] theorem rotate_vertex (Q : BoundaryWalk) (θ : ℝ)
    (i : Fin (Q.n + 1)) :
    (Q.rotate θ).vertex i = rot θ (Q.vertex i) := rfl

@[simp] theorem rotate_edge (Q : BoundaryWalk) (θ : ℝ)
    (i : Fin (Q.n + 1)) :
    (Q.rotate θ).edge i = rot θ (Q.edge i) := by
  change
    rot θ (Q.vertex (i + 1)) - rot θ (Q.vertex i) =
      rot θ (Q.vertex (i + 1) - Q.vertex i)
  exact ((rot θ).map_sub _ _).symm

@[simp] theorem rotate_rawOutNormal (Q : BoundaryWalk) (θ : ℝ)
    (i : Fin (Q.n + 1)) :
    (Q.rotate θ).rawOutNormal i = rot θ (Q.rawOutNormal i) := by
  simp [BoundaryWalk.rawOutNormal, quarterTurnCW, rot_apply]
  ring

theorem rotate_toFiniteHull_carrier (Q : BoundaryWalk) (θ : ℝ) :
    (Q.rotate θ).toFiniteHull.carrier = rot θ '' Q.toFiniteHull.carrier := by
  change
    convexHull ℝ
        (((Finset.univ : Finset (Fin (Q.n + 1))).image
          (fun i ↦ rot θ (Q.vertex i)) : Finset Point) : Set Point) =
      rot θ ''
        convexHull ℝ
          (((Finset.univ : Finset (Fin (Q.n + 1))).image Q.vertex :
            Finset Point) : Set Point)
  rw [show
      (((Finset.univ : Finset (Fin (Q.n + 1))).image
          (fun i ↦ rot θ (Q.vertex i)) : Finset Point) : Set Point) =
      rot θ ''
          (((Finset.univ : Finset (Fin (Q.n + 1))).image Q.vertex :
            Finset Point) : Set Point) by
    simp only [Finset.coe_image, Set.image_image]]
  exact
    ((rot θ).toLinearEquiv.toLinearMap.image_convexHull
      ((((Finset.univ : Finset (Fin (Q.n + 1))).image Q.vertex :
        Finset Point) : Set Point))).symm

theorem translate_toFiniteHull_carrier (Q : BoundaryWalk) (t : Point) :
    (Q.translate t).toFiniteHull.carrier =
      t +ᵥ Q.toFiniteHull.carrier := by
  rw [← Q.toFiniteHull.carrier_translate]
  unfold FiniteHull.carrier
  rw [show (Q.translate t).toFiniteHull.vertices =
      (Q.toFiniteHull.translate t).vertices by
    change
      ((Finset.univ : Finset (Fin (Q.n + 1))).image
          (fun i ↦ t + Q.vertex i) : Finset Point) =
        ((Finset.univ : Finset (Fin (Q.n + 1))).image Q.vertex).image
          (fun p ↦ t + p)
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Q.vertex i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩]

abbrev reflectX (Q : BoundaryWalk) : BoundaryWalk :=
  { n := Q.n
    vertex := fun i ↦ MoserWorm.reflectX (Q.vertex i) }

theorem reflectX_toFiniteHull_carrier (Q : BoundaryWalk) :
    Q.reflectX.toFiniteHull.carrier =
      MoserWorm.reflectX '' Q.toFiniteHull.carrier := by
  change
    convexHull ℝ
        (((Finset.univ : Finset (Fin (Q.n + 1))).image
          (fun i ↦ MoserWorm.reflectX (Q.vertex i)) : Finset Point) : Set Point) =
      MoserWorm.reflectX ''
        convexHull ℝ
          (((Finset.univ : Finset (Fin (Q.n + 1))).image Q.vertex :
            Finset Point) : Set Point)
  rw [show
      (((Finset.univ : Finset (Fin (Q.n + 1))).image
          (fun i ↦ MoserWorm.reflectX (Q.vertex i)) : Finset Point) : Set Point) =
      MoserWorm.reflectX ''
          (((Finset.univ : Finset (Fin (Q.n + 1))).image Q.vertex :
            Finset Point) : Set Point) by
    simp only [Finset.coe_image, Set.image_image]]
  exact
    (MoserWorm.reflectX.toLinearEquiv.toLinearMap.image_convexHull
      ((((Finset.univ : Finset (Fin (Q.n + 1))).image Q.vertex :
        Finset Point) : Set Point))).symm

end BoundaryWalk

namespace PositiveSupportBoundary

abbrev translate (P : PositiveSupportBoundary) (t : Point) :
    PositiveSupportBoundary where
  walk := P.walk.translate t
  center := t + P.center
  center_mem := by
    rw [P.walk.translate_toFiniteHull_carrier]
    exact ⟨P.center, P.center_mem, rfl⟩
  edge_support := by
    intro i p hp
    rw [P.walk.translate_toFiniteHull_carrier] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [P.walk.translate_rawOutNormal]
    change
      ⟪t + q, P.walk.rawOutNormal i⟫_ℝ ≤
        ⟪t + P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ
    rw [inner_add_left, inner_add_left]
    linarith [P.edge_support i q hq]
  center_strict := by
    intro i
    rw [P.walk.translate_rawOutNormal]
    change
      ⟪t + P.center, P.walk.rawOutNormal i⟫_ℝ <
        ⟪t + P.walk.vertex i, P.walk.rawOutNormal i⟫_ℝ
    rw [inner_add_left, inner_add_left]
    linarith [P.center_strict i]
  normal_ne_zero := by
    intro i
    simpa only [BoundaryWalk.translate_rawOutNormal] using P.normal_ne_zero i
  distinct_positive_rays := by
    intro i j hij r s hr hs
    simpa only [BoundaryWalk.translate_rawOutNormal] using
      P.distinct_positive_rays hij hr hs

abbrev rotate (P : PositiveSupportBoundary) (θ : ℝ) :
    PositiveSupportBoundary where
  walk := P.walk.rotate θ
  center := rot θ P.center
  center_mem := by
    rw [P.walk.rotate_toFiniteHull_carrier]
    exact ⟨P.center, P.center_mem, rfl⟩
  edge_support := by
    intro i p hp
    rw [P.walk.rotate_toFiniteHull_carrier] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simpa only [BoundaryWalk.rotate_vertex,
      BoundaryWalk.rotate_rawOutNormal,
      LinearIsometryEquiv.inner_map_map] using P.edge_support i q hq
  center_strict := by
    intro i
    simpa only [BoundaryWalk.rotate_vertex,
      BoundaryWalk.rotate_rawOutNormal,
      LinearIsometryEquiv.inner_map_map] using P.center_strict i
  normal_ne_zero := by
    intro i hzero
    apply P.normal_ne_zero i
    exact (rot θ).injective (by simpa using hzero)
  distinct_positive_rays := by
    intro i j hij r s hr hs heq
    apply P.distinct_positive_rays hij hr hs
    apply (rot θ).injective
    simpa only [map_smul, BoundaryWalk.rotate_rawOutNormal] using heq

end PositiveSupportBoundary

end

end MoserWorm

end


-- MoserWorm.Witness.Equilateral
section

namespace MoserWorm

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

def equilateralVertex : Fin 3 → Point :=
  ![
    point 0 0,
    point (1 / 2) 0,
    point (1 / 4) (Real.sqrt 3 / 4)]

abbrev equilateralWalk : BoundaryWalk where
  n := 2
  vertex := equilateralVertex

def equilateralCenter : Point :=
  point (1 / 4) (Real.sqrt 3 / 12)

@[simp] private theorem point_re_coord (x y : ℝ) : (point x y).re = x := by
  simpa [px] using px_point x y

@[simp] private theorem point_im_coord (x y : ℝ) : (point x y).im = y := by
  simpa [py] using py_point x y

@[simp] private theorem inner_point_point (x y a b : ℝ) :
    ⟪point x y, point a b⟫_ℝ = x * a + y * b := by
  simp [Complex.inner, point]
  ring

@[simp] theorem equilateralWalk_vertex_zero :
    equilateralWalk.vertex (0 : Fin (equilateralWalk.n + 1)) = point 0 0 := by
  rfl

@[simp] theorem equilateralWalk_vertex_one :
    equilateralWalk.vertex (1 : Fin (equilateralWalk.n + 1)) =
      point (1 / 2) 0 := by
  rfl

@[simp] theorem equilateralWalk_vertex_two :
    equilateralWalk.vertex (2 : Fin (equilateralWalk.n + 1)) =
      point (1 / 4) (Real.sqrt 3 / 4) := by
  rfl

@[simp] theorem equilateralWalk_rawOutNormal_zero :
    equilateralWalk.rawOutNormal (0 : Fin (equilateralWalk.n + 1)) =
      point 0 (-1 / 2) := by
  change quarterTurnCW (point (1 / 2) 0 - point 0 0) = point 0 (-1 / 2)
  apply Complex.ext <;>
    norm_num [quarterTurnCW, point]

@[simp] theorem equilateralWalk_rawOutNormal_one :
    equilateralWalk.rawOutNormal (1 : Fin (equilateralWalk.n + 1)) =
      point (Real.sqrt 3 / 4) (1 / 4) := by
  change
    quarterTurnCW
        (point (1 / 4) (Real.sqrt 3 / 4) - point (1 / 2) 0) =
      point (Real.sqrt 3 / 4) (1 / 4)
  apply Complex.ext <;>
    norm_num [quarterTurnCW, point]

@[simp] theorem equilateralWalk_rawOutNormal_two :
    equilateralWalk.rawOutNormal (2 : Fin (equilateralWalk.n + 1)) =
      point (-Real.sqrt 3 / 4) (1 / 4) := by
  change
    quarterTurnCW (point 0 0 - point (1 / 4) (Real.sqrt 3 / 4)) =
      point (-Real.sqrt 3 / 4) (1 / 4)
  apply Complex.ext
  · norm_num [quarterTurnCW, point]
    ring
  ·
    norm_num [quarterTurnCW, point]

@[simp] theorem equilateralWalk_rawOutNormal_by_val
    (i : Fin (equilateralWalk.n + 1)) :
    equilateralWalk.rawOutNormal i =
      if i.val = 0 then point 0 (-1 / 2)
      else if i.val = 1 then point (Real.sqrt 3 / 4) (1 / 4)
      else point (-Real.sqrt 3 / 4) (1 / 4) := by
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    subst i
    rw [equilateralWalk_rawOutNormal_zero]
    norm_num [equilateralWalk]
  by_cases h1 : i.val = 1
  · have hi : i = 1 := Fin.ext h1
    subst i
    rw [equilateralWalk_rawOutNormal_one]
    norm_num [equilateralWalk]
  · have hlt := i.isLt
    change i.val < 3 at hlt
    have h2 : i.val = 2 := by omega
    have hi : i = 2 := Fin.ext h2
    subst i
    rw [equilateralWalk_rawOutNormal_two]
    norm_num [equilateralWalk]

private theorem sqrt_three_pos : 0 < Real.sqrt 3 := by
  exact Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num)

theorem equilateral_supportHull_eq_edgeLevel
    (i : Fin (equilateralWalk.n + 1)) :
    supportHull equilateralWalk.toFiniteHull
        (equilateralWalk.rawOutNormal i) =
      ⟪equilateralWalk.vertex i, equilateralWalk.rawOutNormal i⟫_ℝ := by
  apply le_antisymm
  · obtain ⟨p, hp, hsupport⟩ :=
      supportHull_attained equilateralWalk.toFiniteHull
        (equilateralWalk.rawOutNormal i)
    rw [hsupport]
    rcases Finset.mem_image.mp hp with ⟨j, -, rfl⟩
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [equilateralWalk, equilateralVertex, inner_point_point]
    all_goals nlinarith [sqrt_three_pos, sqrt_three_sq]
  · apply inner_le_supportHull_of_mem_vertices
    classical
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem equilateralCenter_mem :
    equilateralCenter ∈ equilateralWalk.toFiniteHull.carrier := by
  let H := equilateralWalk.toFiniteHull
  have h0 : equilateralWalk.vertex (0 : Fin (equilateralWalk.n + 1)) ∈ H.carrier :=
    equilateralWalk.vertex_mem_toFiniteHull_carrier 0
  have h1 : equilateralWalk.vertex (1 : Fin (equilateralWalk.n + 1)) ∈ H.carrier :=
    equilateralWalk.vertex_mem_toFiniteHull_carrier 1
  have h2 : equilateralWalk.vertex (2 : Fin (equilateralWalk.n + 1)) ∈ H.carrier :=
    equilateralWalk.vertex_mem_toFiniteHull_carrier 2
  have hmid :
      (1 / 2 : ℝ) •
          equilateralWalk.vertex (1 : Fin (equilateralWalk.n + 1)) +
        (1 / 2 : ℝ) •
          equilateralWalk.vertex (2 : Fin (equilateralWalk.n + 1)) ∈ H.carrier :=
    (convex_iff_add_mem.mp H.carrier_convex) h1 h2
      (by norm_num) (by norm_num) (by norm_num)
  have hcenter :
      (1 / 3 : ℝ) •
          equilateralWalk.vertex (0 : Fin (equilateralWalk.n + 1)) +
          (2 / 3 : ℝ) •
            ((1 / 2 : ℝ) •
                equilateralWalk.vertex (1 : Fin (equilateralWalk.n + 1)) +
              (1 / 2 : ℝ) •
                equilateralWalk.vertex
                  (2 : Fin (equilateralWalk.n + 1))) ∈ H.carrier :=
    (convex_iff_add_mem.mp H.carrier_convex) h0 hmid
      (by norm_num) (by norm_num) (by norm_num)
  have heq :
      equilateralCenter =
        (1 / 3 : ℝ) •
            equilateralWalk.vertex (0 : Fin (equilateralWalk.n + 1)) +
          (2 / 3 : ℝ) •
            ((1 / 2 : ℝ) •
                equilateralWalk.vertex (1 : Fin (equilateralWalk.n + 1)) +
              (1 / 2 : ℝ) •
                equilateralWalk.vertex
                  (2 : Fin (equilateralWalk.n + 1))) := by
    rw [equilateralWalk_vertex_zero, equilateralWalk_vertex_one, equilateralWalk_vertex_two]
    apply Complex.ext <;> norm_num [equilateralCenter, point] <;> ring
  change equilateralCenter ∈ H.carrier
  rw [heq]
  exact hcenter

theorem equilateral_center_gap (i : Fin (equilateralWalk.n + 1)) :
    ⟪equilateralWalk.vertex i, equilateralWalk.rawOutNormal i⟫_ℝ -
        ⟪equilateralCenter, equilateralWalk.rawOutNormal i⟫_ℝ =
      Real.sqrt 3 / 24 := by
  fin_cases i
  all_goals
    norm_num [equilateralCenter, equilateralWalk, equilateralVertex,
      inner_point_point]
  all_goals nlinarith [sqrt_three_sq]

def equilateralPositiveSupportBoundary : PositiveSupportBoundary where
  walk := equilateralWalk
  center := equilateralCenter
  center_mem := equilateralCenter_mem
  edge_support := by
    intro i p hp
    rw [← equilateral_supportHull_eq_edgeLevel i]
    exact inner_le_supportHull_of_mem_carrier _ _ _ hp
  center_strict := by
    intro i
    have hgap := equilateral_center_gap i
    nlinarith [sqrt_three_pos]
  normal_ne_zero := by
    intro i hzero
    have him := congrArg Complex.im hzero
    fin_cases i
    all_goals norm_num at him
  distinct_positive_rays := by
    intro i j hij r s hr hs heq
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    fin_cases i <;> fin_cases j
    all_goals simp at hij
    all_goals norm_num at hre him
    all_goals nlinarith [sqrt_three_pos]

theorem equilateralWalk_vertex_one_eq_unitVec :
    equilateralWalk.vertex (1 : Fin (equilateralWalk.n + 1)) =
      (1 / 2 : ℝ) • unitVec 0 := by
  rw [equilateralWalk_vertex_one]
  apply Complex.ext <;> norm_num [point]

theorem equilateralWalk_vertex_two_eq_unitVec :
    equilateralWalk.vertex (2 : Fin (equilateralWalk.n + 1)) =
      (1 / 2 : ℝ) • unitVec (Real.pi / 3) := by
  rw [equilateralWalk_vertex_two]
  apply Complex.ext <;> norm_num [point, Real.cos_pi_div_three,
      Real.sin_pi_div_three] <;> ring

theorem equilateral_rotate_vertex (θ : ℝ) :
    (equilateralWalk.rotate θ).vertex = ![
      0,
      (1 / 2 : ℝ) • unitVec θ,
      (1 / 2 : ℝ) • unitVec (θ + Real.pi / 3)] := by
  change (fun i : Fin 3 ↦ rot θ (equilateralWalk.vertex i)) = _
  funext i
  fin_cases i
  · change rot θ (point 0 0) = 0
    rw [show point 0 0 = 0 by simp [point], map_zero]
  · change rot θ (point (1 / 2) 0) = (1 / 2 : ℝ) • unitVec θ
    have hv : point (1 / 2) 0 = (1 / 2 : ℝ) • unitVec 0 := by
      exact equilateralWalk_vertex_one_eq_unitVec
    rw [hv, map_smul, rot_apply_unitVec]
    simp
  · change rot θ (point (1 / 4) (Real.sqrt 3 / 4)) =
      (1 / 2 : ℝ) • unitVec (θ + Real.pi / 3)
    have hv : point (1 / 4) (Real.sqrt 3 / 4) =
        (1 / 2 : ℝ) • unitVec (Real.pi / 3) := by
      exact equilateralWalk_vertex_two_eq_unitVec
    rw [hv, map_smul, rot_apply_unitVec]
    rw [add_comm]

def equilateralPositiveSupportBoundaryAt (θ : ℝ) : PositiveSupportBoundary :=
  equilateralPositiveSupportBoundary.rotate θ

def placedEquilateralPositiveSupportBoundary (θ : ℝ) (t : Point) :
    PositiveSupportBoundary :=
  (equilateralPositiveSupportBoundaryAt θ).translate t

def equilateralThirdTurnIndex : Fin 3 → Fin 3 := ![1, 2, 0]

def equilateralThirdTurnIndexInv : Fin 3 → Fin 3 := ![2, 0, 1]

@[simp] theorem equilateralThirdTurnIndex_left_inv (i : Fin 3) :
    equilateralThirdTurnIndex
        (equilateralThirdTurnIndexInv i) = i := by
  fin_cases i <;> rfl

theorem unitVec_add_thirdTurn (θ : ℝ) :
    unitVec θ + unitVec (θ + 2 * Real.pi / 3) =
      unitVec (θ + Real.pi / 3) := by
  have htwo : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by
    ring
  apply Complex.ext
  · simp only [Complex.add_re, unitVec_re, Real.cos_add]
    rw [htwo, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    ring
  · simp only [Complex.add_im, unitVec_im, Real.sin_add]
    rw [htwo, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    ring

@[simp] theorem equilateral_thirdTurn_translate_vertex
    (θ : ℝ) (i : Fin 3) :
    (((equilateralWalk.rotate (θ + 2 * Real.pi / 3)).translate
      ((1 / 2 : ℝ) • unitVec θ)).vertex i) =
      (equilateralWalk.rotate θ).vertex
        (equilateralThirdTurnIndex i) := by
  change
    (1 / 2 : ℝ) • unitVec θ +
        (equilateralWalk.rotate (θ + 2 * Real.pi / 3)).vertex i =
      (equilateralWalk.rotate θ).vertex
        (equilateralThirdTurnIndex i)
  rw [equilateral_rotate_vertex (θ + 2 * Real.pi / 3),
    equilateral_rotate_vertex θ]
  fin_cases i
  · simp [equilateralThirdTurnIndex]
  · change
      (1 / 2 : ℝ) • unitVec θ +
          (1 / 2 : ℝ) • unitVec (θ + 2 * Real.pi / 3) =
        (1 / 2 : ℝ) • unitVec (θ + Real.pi / 3)
    calc
      (1 / 2 : ℝ) • unitVec θ +
          (1 / 2 : ℝ) • unitVec (θ + 2 * Real.pi / 3) =
          (1 / 2 : ℝ) •
            (unitVec θ + unitVec (θ + 2 * Real.pi / 3)) := by
              exact (smul_add (1 / 2 : ℝ) _ _).symm
      _ = (1 / 2 : ℝ) • unitVec (θ + Real.pi / 3) := by
        rw [unitVec_add_thirdTurn]
  · change
      (1 / 2 : ℝ) • unitVec θ +
          (1 / 2 : ℝ) •
            unitVec ((θ + 2 * Real.pi / 3) + Real.pi / 3) = 0
    rw [show (θ + 2 * Real.pi / 3) + Real.pi / 3 = θ + Real.pi by ring,
      unitVec_add_pi]
    module

theorem equilateral_thirdTurn_translate_vertices_eq (θ : ℝ) :
    (((equilateralWalk.rotate (θ + 2 * Real.pi / 3)).translate
      ((1 / 2 : ℝ) • unitVec θ)).toFiniteHull.vertices) =
      (equilateralWalk.rotate θ).toFiniteHull.vertices := by
  classical
  ext p
  simp only [BoundaryWalk.toFiniteHull, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨equilateralThirdTurnIndex i,
      (equilateral_thirdTurn_translate_vertex θ i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨equilateralThirdTurnIndexInv i, ?_⟩
    change
      (((equilateralWalk.rotate (θ + 2 * Real.pi / 3)).translate
          ((1 / 2 : ℝ) • unitVec θ)).vertex
        (equilateralThirdTurnIndexInv i)) =
        (equilateralWalk.rotate θ).vertex i
    rw [equilateral_thirdTurn_translate_vertex,
      equilateralThirdTurnIndex_left_inv]

theorem equilateral_thirdTurn_translate_carrier (θ : ℝ) :
    (((equilateralWalk.rotate (θ + 2 * Real.pi / 3)).translate
      ((1 / 2 : ℝ) • unitVec θ)).toFiniteHull.carrier) =
      (equilateralWalk.rotate θ).toFiniteHull.carrier := by
  unfold FiniteHull.carrier
  rw [equilateral_thirdTurn_translate_vertices_eq]

def equilateralReflectionIndex : Fin 3 → Fin 3 := ![0, 2, 1]

@[simp] theorem equilateralReflectionIndex_involutive (i : Fin 3) :
    equilateralReflectionIndex (equilateralReflectionIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem equilateral_reflect_vertex (θ : ℝ) (i : Fin 3) :
    reflectX ((equilateralWalk.rotate θ).vertex i) =
      (equilateralWalk.rotate (-θ - Real.pi / 3)).vertex
        (equilateralReflectionIndex i) := by
  rw [equilateral_rotate_vertex θ,
    equilateral_rotate_vertex (-θ - Real.pi / 3)]
  fin_cases i
  · simp [equilateralReflectionIndex]
  · change
      reflectX ((1 / 2 : ℝ) • unitVec θ) =
        (1 / 2 : ℝ) • unitVec ((-θ - Real.pi / 3) + Real.pi / 3)
    rw [map_smul, reflectX_unitVec]
    congr 2
    ring
  · change
      reflectX ((1 / 2 : ℝ) • unitVec (θ + Real.pi / 3)) =
        (1 / 2 : ℝ) • unitVec (-θ - Real.pi / 3)
    rw [map_smul, reflectX_unitVec]
    congr 2
    ring

theorem equilateral_reflect_vertices_eq (θ : ℝ) :
    ((equilateralWalk.rotate θ).reflectX.toFiniteHull.vertices) =
      (equilateralWalk.rotate (-θ - Real.pi / 3)).toFiniteHull.vertices := by
  classical
  ext p
  simp only [BoundaryWalk.toFiniteHull, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨equilateralReflectionIndex i,
      (equilateral_reflect_vertex θ i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨equilateralReflectionIndex i, ?_⟩
    change
      reflectX ((equilateralWalk.rotate θ).vertex
          (equilateralReflectionIndex i)) =
        (equilateralWalk.rotate (-θ - Real.pi / 3)).vertex i
    rw [equilateral_reflect_vertex,
      equilateralReflectionIndex_involutive]

theorem reflectX_image_equilateral_carrier (θ : ℝ) :
    reflectX '' (equilateralWalk.rotate θ).toFiniteHull.carrier =
      (equilateralWalk.rotate (-θ - Real.pi / 3)).toFiniteHull.carrier := by
  rw [← BoundaryWalk.reflectX_toFiniteHull_carrier]
  unfold FiniteHull.carrier
  rw [equilateral_reflect_vertices_eq]

end

end MoserWorm

end


-- MoserWorm.Witness.LargeAngle
section

namespace MoserWorm

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

def segmentHull : FiniteHull where
  vertices := {0, unitVec 0}
  nonempty := by simp

def segmentHullAt (θ : ℝ) : FiniteHull where
  vertices := {0, unitVec θ}
  nonempty := by simp

theorem segmentHullAt_add_pi_translate_vertices (θ : ℝ) :
    ((segmentHullAt (θ + Real.pi)).translate (unitVec θ)).vertices =
      (segmentHullAt θ).vertices := by
  classical
  ext p
  simp only [FiniteHull.translate, segmentHullAt, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  rw [unitVec_add_pi]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl
    · simp
    · simp
  · intro hp
    rcases hp with rfl | rfl
    · exact ⟨-unitVec θ, by simp, by simp⟩
    · exact ⟨0, by simp, by simp⟩

theorem segmentHullAt_add_pi_translate_carrier (θ : ℝ) :
    ((segmentHullAt (θ + Real.pi)).translate (unitVec θ)).carrier =
      (segmentHullAt θ).carrier := by
  unfold FiniteHull.carrier
  rw [segmentHullAt_add_pi_translate_vertices]

@[simp] theorem supportHull_segmentHull (u : Point) :
    supportHull segmentHull u = max 0 u.re := by
  classical
  simp [supportHull, segmentHull, Complex.inner]

def largeAngleFloor : ℝ :=
  (1 / 4 : ℝ) * Real.cos (Real.pi / 10)

theorem mixedSupport_segment_equilateral
    (θ : ℝ) (hθ_lower : Real.pi / 15 ≤ θ)
    (hθ_upper : θ ≤ Real.pi / 6) :
    mixedSupport segmentHull (equilateralWalk.rotate θ) =
      (1 / 4 : ℝ) * Real.cos (Real.pi / 6 - θ) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hθ_nonneg : 0 ≤ θ := by linarith
  have hθ_le_pi : θ ≤ Real.pi := by linarith
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ_nonneg hθ_le_pi
  have hcos_one : 0 ≤ Real.cos (θ + Real.pi / 6) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hcos_two : Real.cos (θ + 5 * Real.pi / 6) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
  simp only [mixedSupport, supportHull_segmentHull]
  change
    (1 / 2 : ℝ) * ∑ x : Fin 3,
        max 0 ((equilateralWalk.rotate θ).rawOutNormal x).re =
      (1 / 4 : ℝ) * Real.cos (Real.pi / 6 - θ)
  rw [Fin.sum_univ_three]
  simp only [BoundaryWalk.rotate_rawOutNormal,
    equilateralWalk_rawOutNormal_by_val]
  norm_num [equilateralWalk, rot_apply, point]
  have hnormal_zero :
      Real.sin θ * (1 / 2 : ℝ) = (1 / 2 : ℝ) * Real.sin θ := by
    ring
  have hnormal_one :
      Real.cos θ * (Real.sqrt 3 / 4) - Real.sin θ * (1 / 4) =
        (1 / 2 : ℝ) * Real.cos (θ + Real.pi / 6) := by
    rw [Real.cos_add, Real.cos_pi_div_six, Real.sin_pi_div_six]
    ring
  have hnormal_two :
      Real.cos θ * (-Real.sqrt 3 / 4) - Real.sin θ * (1 / 4) =
        (1 / 2 : ℝ) * Real.cos (θ + 5 * Real.pi / 6) := by
    have hfive : (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 := by
      ring
    rw [hfive, Real.cos_add, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_six, Real.sin_pi_div_six]
    ring
  rw [hnormal_zero, hnormal_one, hnormal_two]
  rw [max_eq_right (mul_nonneg (by norm_num) hsin),
    max_eq_right (mul_nonneg (by norm_num) hcos_one),
    max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hcos_two)]
  rw [Real.cos_add, Real.cos_sub, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  ring

theorem mixedSupport_placed_segment_equilateral
    (θ : ℝ) (tS tE : Point) (hθ_lower : Real.pi / 15 ≤ θ)
    (hθ_upper : θ ≤ Real.pi / 6) :
    mixedSupport (segmentHull.translate tS)
        (placedEquilateralPositiveSupportBoundary θ tE).walk =
      (1 / 4 : ℝ) * Real.cos (Real.pi / 6 - θ) := by
  change
    mixedSupport (segmentHull.translate tS)
        ((equilateralWalk.rotate θ).translate tE) = _
  rw [mixedSupport_translate_second, mixedSupport_translate_first,
    mixedSupport_segment_equilateral θ hθ_lower hθ_upper]

theorem largeAngleFloor_le_mixedSupport_placed_segment_equilateral
    (θ : ℝ) (tS tE : Point) (hθ_lower : Real.pi / 15 ≤ θ)
    (hθ_upper : θ ≤ Real.pi / 6) :
    largeAngleFloor ≤
      mixedSupport (segmentHull.translate tS)
        (placedEquilateralPositiveSupportBoundary θ tE).walk := by
  rw [mixedSupport_placed_segment_equilateral θ tS tE hθ_lower hθ_upper]
  unfold largeAngleFloor
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
    (by linarith)

theorem largeAngleFloor_le_volumeReal_of_contains_segment_equilateral
    (θ : ℝ) (tS tE : Point) (hθ_lower : Real.pi / 15 ≤ θ)
    (hθ_upper : θ ≤ Real.pi / 6) {C : Set Point} (hC : Convex ℝ C)
    (hCfinite : volume C ≠ ⊤)
    (hSegment : (segmentHull.translate tS).carrier ⊆ C)
    (hEquilateral :
      (placedEquilateralPositiveSupportBoundary θ tE).walk.toFiniteHull.carrier ⊆ C) :
    largeAngleFloor ≤ volume.real C := by
  calc
    largeAngleFloor ≤
        mixedSupport (segmentHull.translate tS)
          (placedEquilateralPositiveSupportBoundary θ tE).walk :=
      largeAngleFloor_le_mixedSupport_placed_segment_equilateral
        θ tS tE hθ_lower hθ_upper
    _ ≤ volume.real C :=
      PositiveSupportBoundary.mixedSupport_le_volumeReal_of_positiveSupportBoundary
        (placedEquilateralPositiveSupportBoundary θ tE)
        (segmentHull.translate tS) hC hCfinite hSegment hEquilateral

end

end MoserWorm

end


-- MoserWorm.Witness.OneCap
section

namespace MoserWorm

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

def oneCapSpan (β : ℝ) : ℝ :=
  (1 + 2 * Real.cos β) / 3

def oneCapVertex (β : ℝ) : Fin 4 → Point
  | 0 => point 0 0
  | 1 => point (oneCapSpan β) 0
  | 2 => point ((1 + Real.cos β) / 3) (Real.sin β / 3)
  | 3 => point (Real.cos β / 3) (Real.sin β / 3)

abbrev oneCapWalk (β : ℝ) : BoundaryWalk where
  n := 3
  vertex := oneCapVertex β

def oneCapCenter (β : ℝ) : Point :=
  point (oneCapSpan β / 2) (Real.sin β / 6)

@[simp] private theorem oneCap_inner_point_point (x y a b : ℝ) :
    ⟪point x y, point a b⟫_ℝ = x * a + y * b := by
  simp [Complex.inner, point]
  ring

@[simp] theorem oneCapWalk_vertex_zero (β : ℝ) :
    (oneCapWalk β).vertex 0 = point 0 0 := rfl

@[simp] theorem oneCapWalk_vertex_one (β : ℝ) :
    (oneCapWalk β).vertex 1 = point (oneCapSpan β) 0 := rfl

@[simp] theorem oneCapWalk_vertex_two (β : ℝ) :
    (oneCapWalk β).vertex 2 =
      point ((1 + Real.cos β) / 3) (Real.sin β / 3) := rfl

@[simp] theorem oneCapWalk_vertex_three (β : ℝ) :
    (oneCapWalk β).vertex 3 =
      point (Real.cos β / 3) (Real.sin β / 3) := rfl

@[simp] theorem oneCapWalk_edge_zero (β : ℝ) :
    (oneCapWalk β).edge 0 = point (oneCapSpan β) 0 := by
  change point (oneCapSpan β) 0 - point 0 0 = point (oneCapSpan β) 0
  apply Complex.ext <;>
    simp [point]

@[simp] theorem oneCapWalk_edge_one (β : ℝ) :
    (oneCapWalk β).edge 1 =
      point (-Real.cos β / 3) (Real.sin β / 3) := by
  change
    point ((1 + Real.cos β) / 3) (Real.sin β / 3) -
        point (oneCapSpan β) 0 =
      point (-Real.cos β / 3) (Real.sin β / 3)
  apply Complex.ext <;>
    simp [oneCapSpan, point] <;>
    ring

@[simp] theorem oneCapWalk_edge_two (β : ℝ) :
    (oneCapWalk β).edge 2 = point (-1 / 3) 0 := by
  change
    point (Real.cos β / 3) (Real.sin β / 3) -
        point ((1 + Real.cos β) / 3) (Real.sin β / 3) =
      point (-1 / 3) 0
  apply Complex.ext <;>
    simp [point] <;>
    ring

@[simp] theorem oneCapWalk_edge_three (β : ℝ) :
    (oneCapWalk β).edge 3 =
      point (-Real.cos β / 3) (-Real.sin β / 3) := by
  rw [BoundaryWalk.edge]
  change
    oneCapVertex β ((3 : Fin 4) + 1) - oneCapVertex β 3 =
      point (-Real.cos β / 3) (-Real.sin β / 3)
  rw [show (3 : Fin 4) + 1 = 0 by decide]
  change
    point 0 0 - point (Real.cos β / 3) (Real.sin β / 3) =
      point (-Real.cos β / 3) (-Real.sin β / 3)
  apply Complex.ext <;>
    simp [point] <;>
    ring

@[simp] theorem oneCapWalk_rawOutNormal_zero (β : ℝ) :
    (oneCapWalk β).rawOutNormal 0 = point 0 (-oneCapSpan β) := by
  rw [BoundaryWalk.rawOutNormal, oneCapWalk_edge_zero]
  apply Complex.ext <;> simp [quarterTurnCW, point]

@[simp] theorem oneCapWalk_rawOutNormal_one (β : ℝ) :
    (oneCapWalk β).rawOutNormal 1 =
      point (Real.sin β / 3) (Real.cos β / 3) := by
  rw [BoundaryWalk.rawOutNormal, oneCapWalk_edge_one]
  apply Complex.ext <;> simp [quarterTurnCW, point] <;> ring

@[simp] theorem oneCapWalk_rawOutNormal_two (β : ℝ) :
    (oneCapWalk β).rawOutNormal 2 = point 0 (1 / 3) := by
  rw [BoundaryWalk.rawOutNormal, oneCapWalk_edge_two]
  apply Complex.ext <;> norm_num [quarterTurnCW, point]

@[simp] theorem oneCapWalk_rawOutNormal_three (β : ℝ) :
    (oneCapWalk β).rawOutNormal 3 =
      point (-Real.sin β / 3) (Real.cos β / 3) := by
  rw [BoundaryWalk.rawOutNormal, oneCapWalk_edge_three]
  apply Complex.ext <;> simp [quarterTurnCW, point] <;> ring

@[simp] theorem oneCapWalk_rawOutNormal_by_val (β : ℝ)
    (i : Fin ((oneCapWalk β).n + 1)) :
    (oneCapWalk β).rawOutNormal i =
      if i.val = 0 then point 0 (-oneCapSpan β)
      else if i.val = 1 then
        point (Real.sin β / 3) (Real.cos β / 3)
      else if i.val = 2 then point 0 (1 / 3)
      else point (-Real.sin β / 3) (Real.cos β / 3) := by
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    subst i
    rw [oneCapWalk_rawOutNormal_zero]
    norm_num [oneCapWalk]
  by_cases h1 : i.val = 1
  · have hi : i = 1 := Fin.ext h1
    subst i
    rw [oneCapWalk_rawOutNormal_one]
    norm_num [oneCapWalk, h0]
  by_cases h2 : i.val = 2
  · have hi : i = 2 := Fin.ext h2
    subst i
    rw [oneCapWalk_rawOutNormal_two]
    norm_num [oneCapWalk, h0, h1]
  · have hlt := i.isLt
    change i.val < 4 at hlt
    have h3 : i.val = 3 := by omega
    have hi : i = 3 := Fin.ext h3
    subst i
    rw [oneCapWalk_rawOutNormal_three]
    norm_num [oneCapWalk, h0, h1, h2]

@[simp] theorem oneCapWalk_rotate_rawOutNormal_zero (β φ : ℝ) :
    ((oneCapWalk β).rotate φ).rawOutNormal 0 =
      oneCapSpan β • unitVec (φ - Real.pi / 2) := by
  rw [BoundaryWalk.rotate_rawOutNormal,
    oneCapWalk_rawOutNormal_by_val]
  norm_num [oneCapWalk, BoundaryWalk.rotate]
  apply Complex.ext <;>
    simp [rot_apply, Real.cos_sub, Real.sin_sub] <;>
    ring

@[simp] theorem oneCapWalk_rotate_rawOutNormal_one (β φ : ℝ) :
    ((oneCapWalk β).rotate φ).rawOutNormal 1 =
      (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 - β) := by
  rw [BoundaryWalk.rotate_rawOutNormal,
    oneCapWalk_rawOutNormal_by_val]
  norm_num [oneCapWalk, BoundaryWalk.rotate]
  apply Complex.ext <;>
    simp [rot_apply, Real.cos_sub, Real.sin_sub, Real.cos_add,
      Real.sin_add] <;>
    ring

@[simp] theorem oneCapWalk_rotate_rawOutNormal_two (β φ : ℝ) :
    ((oneCapWalk β).rotate φ).rawOutNormal 2 =
      (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2) := by
  rw [BoundaryWalk.rotate_rawOutNormal,
    oneCapWalk_rawOutNormal_by_val]
  norm_num [oneCapWalk, BoundaryWalk.rotate]
  apply Complex.ext <;>
    simp [rot_apply, Real.cos_add, Real.sin_add] <;>
    ring

@[simp] theorem oneCapWalk_rotate_rawOutNormal_three (β φ : ℝ) :
    ((oneCapWalk β).rotate φ).rawOutNormal 3 =
      (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 + β) := by
  rw [BoundaryWalk.rotate_rawOutNormal,
    oneCapWalk_rawOutNormal_by_val]
  norm_num [oneCapWalk, BoundaryWalk.rotate]
  apply Complex.ext <;>
    simp [rot_apply, Real.cos_add, Real.sin_add] <;>
    ring

theorem oneCap_sin_pos {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) : 0 < Real.sin β := by
  exact Real.sin_pos_of_pos_of_lt_pi hβ0 (by nlinarith [Real.pi_pos])

theorem oneCap_cos_pos {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) : 0 < Real.cos β := by
  exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hβ⟩

theorem oneCapSpan_pos {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) : 0 < oneCapSpan β := by
  have hc := oneCap_cos_pos hβ0 hβ
  unfold oneCapSpan
  nlinarith

theorem oneCap_supportHull_eq_edgeLevel {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) (i : Fin ((oneCapWalk β).n + 1)) :
    supportHull (oneCapWalk β).toFiniteHull
        ((oneCapWalk β).rawOutNormal i) =
      ⟪(oneCapWalk β).vertex i,
        (oneCapWalk β).rawOutNormal i⟫_ℝ := by
  have hsin := oneCap_sin_pos hβ0 hβ
  have hcos := oneCap_cos_pos hβ0 hβ
  have hspan := oneCapSpan_pos hβ0 hβ
  apply le_antisymm
  · obtain ⟨p, hp, hsupport⟩ :=
      supportHull_attained (oneCapWalk β).toFiniteHull
        ((oneCapWalk β).rawOutNormal i)
    rw [hsupport]
    rcases Finset.mem_image.mp hp with ⟨j, -, rfl⟩
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [oneCapWalk, oneCapVertex, oneCapSpan,
        oneCap_inner_point_point]
    all_goals nlinarith
  · apply inner_le_supportHull_of_mem_vertices
    classical
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem oneCapCenter_mem (β : ℝ) :
    oneCapCenter β ∈ (oneCapWalk β).toFiniteHull.carrier := by
  let H := (oneCapWalk β).toFiniteHull
  have h0 :
      (oneCapWalk β).vertex 0 ∈ H.carrier :=
    (oneCapWalk β).vertex_mem_toFiniteHull_carrier 0
  have h1 :
      (oneCapWalk β).vertex 1 ∈ H.carrier :=
    (oneCapWalk β).vertex_mem_toFiniteHull_carrier 1
  have h2 :
      (oneCapWalk β).vertex 2 ∈ H.carrier :=
    (oneCapWalk β).vertex_mem_toFiniteHull_carrier 2
  have h3 :
      (oneCapWalk β).vertex 3 ∈ H.carrier :=
    (oneCapWalk β).vertex_mem_toFiniteHull_carrier 3
  have hbottom :
      (1 / 2 : ℝ) • (oneCapWalk β).vertex 0 +
          (1 / 2 : ℝ) • (oneCapWalk β).vertex 1 ∈ H.carrier :=
    (convex_iff_add_mem.mp H.carrier_convex) h0 h1
      (by norm_num) (by norm_num) (by norm_num)
  have htop :
      (1 / 2 : ℝ) • (oneCapWalk β).vertex 3 +
          (1 / 2 : ℝ) • (oneCapWalk β).vertex 2 ∈ H.carrier :=
    (convex_iff_add_mem.mp H.carrier_convex) h3 h2
      (by norm_num) (by norm_num) (by norm_num)
  have hcenter :
      (1 / 2 : ℝ) •
            ((1 / 2 : ℝ) • (oneCapWalk β).vertex 0 +
              (1 / 2 : ℝ) • (oneCapWalk β).vertex 1) +
          (1 / 2 : ℝ) •
            ((1 / 2 : ℝ) • (oneCapWalk β).vertex 3 +
              (1 / 2 : ℝ) • (oneCapWalk β).vertex 2) ∈ H.carrier :=
    (convex_iff_add_mem.mp H.carrier_convex) hbottom htop
      (by norm_num) (by norm_num) (by norm_num)
  have heq :
      oneCapCenter β =
        (1 / 2 : ℝ) •
            ((1 / 2 : ℝ) • (oneCapWalk β).vertex 0 +
              (1 / 2 : ℝ) • (oneCapWalk β).vertex 1) +
          (1 / 2 : ℝ) •
            ((1 / 2 : ℝ) • (oneCapWalk β).vertex 3 +
              (1 / 2 : ℝ) • (oneCapWalk β).vertex 2) := by
    rw [oneCapWalk_vertex_zero, oneCapWalk_vertex_one, oneCapWalk_vertex_three,
      oneCapWalk_vertex_two]
    apply Complex.ext <;> norm_num [oneCapCenter, oneCapSpan, point] <;> ring
  change oneCapCenter β ∈ H.carrier
  rw [heq]
  exact hcenter

theorem oneCap_center_strict {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) (i : Fin ((oneCapWalk β).n + 1)) :
    ⟪oneCapCenter β, (oneCapWalk β).rawOutNormal i⟫_ℝ <
      ⟪(oneCapWalk β).vertex i,
        (oneCapWalk β).rawOutNormal i⟫_ℝ := by
  have hsin := oneCap_sin_pos hβ0 hβ
  have hcos := oneCap_cos_pos hβ0 hβ
  have hspan := oneCapSpan_pos hβ0 hβ
  fin_cases i
  all_goals
    norm_num [oneCapCenter, oneCapWalk, oneCapVertex, oneCapSpan,
      oneCap_inner_point_point]
  all_goals nlinarith

def oneCapPositiveSupportBoundary (β : ℝ) (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) : PositiveSupportBoundary where
  walk := oneCapWalk β
  center := oneCapCenter β
  center_mem := oneCapCenter_mem β
  edge_support := by
    intro i p hp
    rw [← oneCap_supportHull_eq_edgeLevel hβ0 hβ i]
    exact inner_le_supportHull_of_mem_carrier _ _ _ hp
  center_strict := oneCap_center_strict hβ0 hβ
  normal_ne_zero := by
    intro i hzero
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    have hsin := oneCap_sin_pos hβ0 hβ
    have hspan := oneCapSpan_pos hβ0 hβ
    fin_cases i
    all_goals norm_num [oneCapWalk] at hre him
    all_goals nlinarith
  distinct_positive_rays := by
    intro i j hij r s hr hs heq
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    have hsin := oneCap_sin_pos hβ0 hβ
    have hspan := oneCapSpan_pos hβ0 hβ
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsin0 : Real.sin β ≠ 0 := ne_of_gt hsin
    fin_cases i <;> fin_cases j
    all_goals simp at hij
    all_goals norm_num [oneCapWalk, hr0, hs0, hsin0] at hre
    all_goals norm_num [oneCapWalk, hr0, hs0, hsin0] at him
    all_goals nlinarith

def oneCapPathVertex (β : ℝ) : Fin 4 → Point
  | 0 => point 0 0
  | 1 => point (Real.cos β / 3) (Real.sin β / 3)
  | 2 => point ((1 + Real.cos β) / 3) (Real.sin β / 3)
  | 3 => point (oneCapSpan β) 0

def oneCapPathBoundaryIndex : Fin 4 → Fin 4 :=
  ![0, 3, 2, 1]

@[simp] theorem oneCapPathBoundaryIndex_involutive (i : Fin 4) :
    oneCapPathBoundaryIndex (oneCapPathBoundaryIndex i) = i := by
  fin_cases i <;> rfl

theorem oneCapPathVertex_eq_boundaryVertex (β : ℝ) (i : Fin 4) :
    oneCapPathVertex β i =
      (oneCapWalk β).vertex (oneCapPathBoundaryIndex i) := by
  fin_cases i <;> rfl

def oneCapPathHull (β : ℝ) : FiniteHull := by
  classical
  exact
    { vertices := Finset.univ.image (oneCapPathVertex β)
      nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty }

theorem oneCapPathHull_vertices_eq (β : ℝ) :
    (oneCapPathHull β).vertices = (oneCapWalk β).toFiniteHull.vertices := by
  classical
  ext p
  simp only [oneCapPathHull, BoundaryWalk.toFiniteHull, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact
      ⟨oneCapPathBoundaryIndex i,
        (oneCapPathVertex_eq_boundaryVertex β i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨oneCapPathBoundaryIndex i, ?_⟩
    rw [oneCapPathVertex_eq_boundaryVertex,
      oneCapPathBoundaryIndex_involutive]

theorem oneCapPathHull_carrier_eq (β : ℝ) :
    (oneCapPathHull β).carrier = (oneCapWalk β).toFiniteHull.carrier := by
  unfold FiniteHull.carrier
  rw [oneCapPathHull_vertices_eq]

def oneCapPathStep (β : ℝ) (i : Fin 3) : Point :=
  oneCapPathVertex β i.succ - oneCapPathVertex β i.castSucc

@[simp] theorem oneCapPathStep_zero (β : ℝ) :
    oneCapPathStep β 0 = (1 / 3 : ℝ) • unitVec β := by
  apply Complex.ext <;>
    simp [oneCapPathStep, oneCapPathVertex] <;>
    ring

@[simp] theorem oneCapPathStep_one (β : ℝ) :
    oneCapPathStep β 1 = (1 / 3 : ℝ) • unitVec 0 := by
  apply Complex.ext <;>
    simp [oneCapPathStep, oneCapPathVertex] <;>
    ring

@[simp] theorem oneCapPathStep_two (β : ℝ) :
    oneCapPathStep β 2 = (1 / 3 : ℝ) • unitVec (-β) := by
  apply Complex.ext <;>
    simp [oneCapPathStep, oneCapPathVertex, oneCapSpan,
      Real.cos_neg, Real.sin_neg] <;>
    ring

theorem norm_oneCapPathStep (β : ℝ) (i : Fin 3) :
    ‖oneCapPathStep β i‖ = 1 / 3 := by
  fin_cases i
  all_goals simp

theorem oneCapPath_length (β : ℝ) :
    ∑ i : Fin 3, ‖oneCapPathStep β i‖ = 1 := by
  simp [norm_oneCapPathStep]

def oneCapReflectionIndex : Fin 4 → Fin 4 :=
  ![1, 0, 3, 2]

@[simp] theorem oneCapReflectionIndex_involutive (i : Fin 4) :
    oneCapReflectionIndex (oneCapReflectionIndex i) = i := by
  fin_cases i <;> rfl

theorem oneCap_reflect_vertex (β : ℝ) (i : Fin 4) :
    reflectX ((oneCapWalk β).vertex i) =
      (oneCapWalk β).vertex 1 -
        (oneCapWalk β).vertex (oneCapReflectionIndex i) := by
  fin_cases i
  · change reflectX ((oneCapWalk β).vertex 0) =
      (oneCapWalk β).vertex 1 - (oneCapWalk β).vertex 1
    rw [oneCapWalk_vertex_zero, oneCapWalk_vertex_one]
    apply Complex.ext <;> norm_num [oneCapSpan, reflectX_apply, point] <;> ring
  · change reflectX ((oneCapWalk β).vertex 1) =
      (oneCapWalk β).vertex 1 - (oneCapWalk β).vertex 0
    rw [oneCapWalk_vertex_zero, oneCapWalk_vertex_one]
    apply Complex.ext <;> norm_num [oneCapSpan, reflectX_apply, point] <;> ring
  · change reflectX ((oneCapWalk β).vertex 2) =
      (oneCapWalk β).vertex 1 - (oneCapWalk β).vertex 3
    rw [oneCapWalk_vertex_one, oneCapWalk_vertex_two, oneCapWalk_vertex_three]
    apply Complex.ext <;> norm_num [oneCapSpan, reflectX_apply, point] <;> ring
  · change reflectX ((oneCapWalk β).vertex 3) =
      (oneCapWalk β).vertex 1 - (oneCapWalk β).vertex 2
    rw [oneCapWalk_vertex_one, oneCapWalk_vertex_two, oneCapWalk_vertex_three]
    apply Complex.ext <;> norm_num [oneCapSpan, reflectX_apply, point] <;> ring

theorem oneCap_reflect_vertices_eq_direct (β : ℝ) :
    ((oneCapWalk β).reflectX.toFiniteHull.vertices) =
      (((oneCapWalk β).rotate Real.pi).translate
        ((oneCapWalk β).vertex 1)).toFiniteHull.vertices := by
  classical
  ext p
  simp only [BoundaryWalk.toFiniteHull, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨oneCapReflectionIndex i, ?_⟩
    change
      (oneCapWalk β).vertex 1 +
          rot Real.pi ((oneCapWalk β).vertex (oneCapReflectionIndex i)) =
        reflectX ((oneCapWalk β).vertex i)
    rw [rot_pi]
    simpa only [sub_eq_add_neg] using (oneCap_reflect_vertex β i).symm
  · rintro ⟨i, rfl⟩
    refine ⟨oneCapReflectionIndex i, ?_⟩
    change
      reflectX ((oneCapWalk β).vertex (oneCapReflectionIndex i)) =
        (oneCapWalk β).vertex 1 + rot Real.pi ((oneCapWalk β).vertex i)
    rw [oneCap_reflect_vertex, oneCapReflectionIndex_involutive, rot_pi]
    rfl

theorem reflectX_image_oneCap_carrier_eq_direct (β : ℝ) :
    reflectX '' (oneCapWalk β).toFiniteHull.carrier =
      (((oneCapWalk β).rotate Real.pi).translate
        ((oneCapWalk β).vertex 1)).toFiniteHull.carrier := by
  rw [← BoundaryWalk.reflectX_toFiniteHull_carrier]
  unfold FiniteHull.carrier
  rw [oneCap_reflect_vertices_eq_direct]

end

end MoserWorm

end


-- MoserWorm.Payoff.Semantics
section

namespace MoserWorm

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

@[simp] private theorem equilateral_rotate_vertex_by_val
    (θ : ℝ) (i : Fin 3) :
    (equilateralWalk.rotate θ).vertex i =
      if i.val = 0 then 0
      else if i.val = 1 then (1 / 2 : ℝ) • unitVec θ
      else (1 / 2 : ℝ) • unitVec (θ + Real.pi / 3) := by
  rw [equilateral_rotate_vertex]
  fin_cases i <;> rfl

@[simp] private theorem inner_real_smul_unitVec
    (a α γ : ℝ) :
    ⟪a • unitVec α, unitVec γ⟫_ℝ = a * Real.cos (α - γ) := by
  simp [Complex.inner, Real.cos_sub]
  ring

theorem supportHull_rotatedEquilateral_unitVec_eq_half_M (θ γ : ℝ) :
    supportHull (equilateralWalk.rotate θ).toFiniteHull (unitVec γ) =
      (1 / 2 : ℝ) * Payoff.M θ γ := by
  apply le_antisymm
  · obtain ⟨p, hp, hsupport⟩ :=
      supportHull_attained (equilateralWalk.rotate θ).toFiniteHull (unitVec γ)
    rw [hsupport]
    rcases Finset.mem_image.mp hp with ⟨i, -, rfl⟩
    rw [equilateral_rotate_vertex_by_val]
    fin_cases i
    · change ⟪(0 : Point), unitVec γ⟫_ℝ ≤ (1 / 2 : ℝ) * Payoff.M θ γ
      simpa using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (Payoff.M_nonneg θ γ)
    · change
        ⟪(1 / 2 : ℝ) • unitVec θ, unitVec γ⟫_ℝ ≤
          (1 / 2 : ℝ) * Payoff.M θ γ
      rw [inner_real_smul_unitVec]
      exact
        mul_le_mul_of_nonneg_left (Payoff.M_ge_leftVertex θ γ) (by norm_num)
    · change
        ⟪(1 / 2 : ℝ) • unitVec (θ + Real.pi / 3), unitVec γ⟫_ℝ ≤
          (1 / 2 : ℝ) * Payoff.M θ γ
      rw [inner_real_smul_unitVec]
      exact
        mul_le_mul_of_nonneg_left (Payoff.M_ge_rightVertex θ γ) (by norm_num)
  · classical
    let H := (equilateralWalk.rotate θ).toFiniteHull
    have hvertex (i : Fin 3) :
        ⟪(equilateralWalk.rotate θ).vertex i, unitVec γ⟫_ℝ ≤
          supportHull H (unitVec γ) := by
      apply inner_le_supportHull_of_mem_vertices
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have h0 : 0 ≤ supportHull H (unitVec γ) := by
      have h := hvertex 0
      rw [equilateral_rotate_vertex_by_val] at h
      simpa using h
    have h1 :
        (1 / 2 : ℝ) * Real.cos (θ - γ) ≤
          supportHull H (unitVec γ) := by
      have h := hvertex 1
      rw [equilateral_rotate_vertex_by_val] at h
      change
        ⟪(1 / 2 : ℝ) • unitVec θ, unitVec γ⟫_ℝ ≤
          supportHull H (unitVec γ) at h
      rw [inner_real_smul_unitVec] at h
      exact h
    have h2 :
        (1 / 2 : ℝ) * Real.cos (θ + Real.pi / 3 - γ) ≤
          supportHull H (unitVec γ) := by
      have h := hvertex 2
      rw [equilateral_rotate_vertex_by_val] at h
      change
        ⟪(1 / 2 : ℝ) • unitVec (θ + Real.pi / 3), unitVec γ⟫_ℝ ≤
          supportHull H (unitVec γ) at h
      rw [inner_real_smul_unitVec] at h
      exact h
    rw [Payoff.M, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [mul_zero]
    exact max_le h0 (max_le h1 h2)

theorem supportHull_rotatedEquilateral_nonneg_smul_eq
    (θ γ a : ℝ) (ha : 0 ≤ a) :
    supportHull (equilateralWalk.rotate θ).toFiniteHull (a • unitVec γ) =
      (a / 2) * Payoff.M θ γ := by
  rw [supportHull_nonneg_smul _ _ _ ha,
    supportHull_rotatedEquilateral_unitVec_eq_half_M]
  ring

def oneCapCentralSupport (H : FiniteHull) (φ : ℝ) : ℝ :=
  supportHull H ((1 / 3 : ℝ) • unitVec (φ - Real.pi / 2)) +
    supportHull H ((1 / 3 : ℝ) • unitVec (φ + Real.pi / 2))

def oneCapCapSupport (H : FiniteHull) (β φ : ℝ) : ℝ :=
  supportHull H (((2 / 3 : ℝ) * Real.cos β) •
      unitVec (φ - Real.pi / 2)) +
    supportHull H ((1 / 3 : ℝ) •
      unitVec (φ + Real.pi / 2 - β)) +
    supportHull H ((1 / 3 : ℝ) •
      unitVec (φ + Real.pi / 2 + β))

private theorem supportHull_oneCapSpan_smul_split
    (H : FiniteHull) {β : ℝ} (φ : ℝ) (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) :
    supportHull H (oneCapSpan β • unitVec (φ - Real.pi / 2)) =
      supportHull H ((1 / 3 : ℝ) • unitVec (φ - Real.pi / 2)) +
        supportHull H (((2 / 3 : ℝ) * Real.cos β) •
          unitVec (φ - Real.pi / 2)) := by
  have hc : 0 ≤ Real.cos β := (oneCap_cos_pos hβ0 hβ).le
  rw [supportHull_nonneg_smul H _ _ (oneCapSpan_pos hβ0 hβ).le,
    supportHull_nonneg_smul H _ _ (by norm_num),
    supportHull_nonneg_smul H _ _ (mul_nonneg (by norm_num) hc)]
  unfold oneCapSpan
  ring

theorem mixedSupport_rotate_oneCap_eq_blocks
    (H : FiniteHull) {β : ℝ} (φ : ℝ) (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) :
    mixedSupport H ((oneCapWalk β).rotate φ) =
      (1 / 2 : ℝ) *
        (oneCapCentralSupport H φ + oneCapCapSupport H β φ) := by
  simp only [mixedSupport]
  change
    (1 / 2 : ℝ) * ∑ i : Fin 4,
        supportHull H (((oneCapWalk β).rotate φ).rawOutNormal i) = _
  have hn0 :
      ((oneCapWalk β).rotate φ).rawOutNormal (0 : Fin 4) =
        oneCapSpan β • unitVec (φ - Real.pi / 2) := by
    simpa [oneCapWalk, BoundaryWalk.rotate] using
      oneCapWalk_rotate_rawOutNormal_zero β φ
  have hn1 :
      ((oneCapWalk β).rotate φ).rawOutNormal (1 : Fin 4) =
        (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 - β) := by
    simpa [oneCapWalk, BoundaryWalk.rotate] using
      oneCapWalk_rotate_rawOutNormal_one β φ
  have hn2 :
      ((oneCapWalk β).rotate φ).rawOutNormal (2 : Fin 4) =
        (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2) := by
    simpa [oneCapWalk, BoundaryWalk.rotate] using
      oneCapWalk_rotate_rawOutNormal_two β φ
  have hn3 :
      ((oneCapWalk β).rotate φ).rawOutNormal (3 : Fin 4) =
        (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 + β) := by
    simpa [oneCapWalk, BoundaryWalk.rotate] using
      oneCapWalk_rotate_rawOutNormal_three β φ
  rw [Fin.sum_univ_four, hn0, hn1, hn2, hn3]
  rw [supportHull_oneCapSpan_smul_split H φ hβ0 hβ]
  unfold oneCapCentralSupport oneCapCapSupport
  ring

private theorem oneCapCentralDirections_add_eq_zero (φ : ℝ) :
    (1 / 3 : ℝ) • unitVec (φ - Real.pi / 2) +
      (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2) = 0 := by
  apply Complex.ext <;>
    simp [Real.cos_sub, Real.sin_sub, Real.cos_add, Real.sin_add]

private theorem oneCapCapDirections_add_eq_zero (β φ : ℝ) :
    ((2 / 3 : ℝ) * Real.cos β) • unitVec (φ - Real.pi / 2) +
          (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 - β) +
        (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 + β) = 0 := by
  have hcos : (Complex.cos (β : ℂ)).re = Real.cos β := by
    exact Complex.cos_ofReal_re β
  apply Complex.ext <;>
    simp [Real.cos_sub, Real.sin_sub, Real.cos_add, Real.sin_add] <;>
    rw [hcos] <;>
    ring

theorem oneCapCentralSupport_translate (H : FiniteHull) (t : Point) (φ : ℝ) :
    oneCapCentralSupport (H.translate t) φ = oneCapCentralSupport H φ := by
  let u := (1 / 3 : ℝ) • unitVec (φ - Real.pi / 2)
  let v := (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2)
  have huv : u + v = 0 := oneCapCentralDirections_add_eq_zero φ
  have hinner : ⟪t, u⟫_ℝ + ⟪t, v⟫_ℝ = 0 := by
    rw [← inner_add_right, huv, inner_zero_right]
  unfold oneCapCentralSupport
  rw [supportHull_translate, supportHull_translate]
  change
    supportHull H u + ⟪t, u⟫_ℝ +
        (supportHull H v + ⟪t, v⟫_ℝ) =
      supportHull H u + supportHull H v
  linarith

theorem oneCapCapSupport_translate
    (H : FiniteHull) (t : Point) (β φ : ℝ) :
    oneCapCapSupport (H.translate t) β φ = oneCapCapSupport H β φ := by
  let u := ((2 / 3 : ℝ) * Real.cos β) • unitVec (φ - Real.pi / 2)
  let v := (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 - β)
  let w := (1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 + β)
  have huv : u + v + w = 0 := oneCapCapDirections_add_eq_zero β φ
  have hinner : ⟪t, u⟫_ℝ + ⟪t, v⟫_ℝ + ⟪t, w⟫_ℝ = 0 := by
    have h := congrArg (fun z : Point ↦ ⟪t, z⟫_ℝ) huv
    simpa only [inner_add_right, inner_zero_right] using h
  unfold oneCapCapSupport
  rw [supportHull_translate, supportHull_translate, supportHull_translate]
  change
    supportHull H u + ⟪t, u⟫_ℝ +
          (supportHull H v + ⟪t, v⟫_ℝ) +
        (supportHull H w + ⟪t, w⟫_ℝ) =
      supportHull H u + supportHull H v + supportHull H w
  linarith

theorem oneCapCentralSupport_le_join_left
    (H R : FiniteHull) (φ : ℝ) :
    oneCapCentralSupport H φ ≤ oneCapCentralSupport (H.join R) φ := by
  unfold oneCapCentralSupport
  linarith [
    supportHull_le_join_left H R
      ((1 / 3 : ℝ) • unitVec (φ - Real.pi / 2)),
    supportHull_le_join_left H R
      ((1 / 3 : ℝ) • unitVec (φ + Real.pi / 2))]

theorem oneCapCentralSupport_le_join_right
    (H R : FiniteHull) (φ : ℝ) :
    oneCapCentralSupport R φ ≤ oneCapCentralSupport (H.join R) φ := by
  unfold oneCapCentralSupport
  linarith [
    supportHull_le_join_right H R
      ((1 / 3 : ℝ) • unitVec (φ - Real.pi / 2)),
    supportHull_le_join_right H R
      ((1 / 3 : ℝ) • unitVec (φ + Real.pi / 2))]

theorem oneCapCapSupport_le_join_left
    (H R : FiniteHull) (β φ : ℝ) :
    oneCapCapSupport H β φ ≤ oneCapCapSupport (H.join R) β φ := by
  unfold oneCapCapSupport
  linarith [
    supportHull_le_join_left H R
      (((2 / 3 : ℝ) * Real.cos β) • unitVec (φ - Real.pi / 2)),
    supportHull_le_join_left H R
      ((1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 - β)),
    supportHull_le_join_left H R
      ((1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 + β))]

theorem oneCapCapSupport_le_join_right
    (H R : FiniteHull) (β φ : ℝ) :
    oneCapCapSupport R β φ ≤ oneCapCapSupport (H.join R) β φ := by
  unfold oneCapCapSupport
  linarith [
    supportHull_le_join_right H R
      (((2 / 3 : ℝ) * Real.cos β) • unitVec (φ - Real.pi / 2)),
    supportHull_le_join_right H R
      ((1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 - β)),
    supportHull_le_join_right H R
      ((1 / 3 : ℝ) • unitVec (φ + Real.pi / 2 + β))]

theorem oneCapCentralSupport_segmentHull (φ : ℝ) :
    oneCapCentralSupport segmentHull φ =
      (1 / 3 : ℝ) * |Real.sin φ| := by
  rw [oneCapCentralSupport]
  rw [supportHull_nonneg_smul segmentHull _ _ (by norm_num),
    supportHull_nonneg_smul segmentHull _ _ (by norm_num)]
  simp only [supportHull_segmentHull, unitVec_re]
  have hsouth : Real.cos (φ - Real.pi / 2) = Real.sin φ := by
    rw [Real.cos_sub]
    simp
  have hnorth : Real.cos (φ + Real.pi / 2) = -Real.sin φ := by
    rw [Real.cos_add]
    simp
  rw [hsouth, hnorth]
  by_cases hs : 0 ≤ Real.sin φ
  · rw [abs_of_nonneg hs, max_eq_right hs,
      max_eq_left (neg_nonpos.mpr hs)]
    ring
  · have hs' : Real.sin φ ≤ 0 := le_of_not_ge hs
    rw [abs_of_nonpos hs', max_eq_left hs',
      max_eq_right (neg_nonneg.mpr hs')]
    ring

private theorem abs_le_sum_max_zero_of_sum_zero
    (x y z : ℝ) (hxyz : x + y + z = 0) :
    |x| ≤ max 0 x + max 0 y + max 0 z := by
  rw [abs_le]
  constructor
  · linarith [le_max_left 0 x, le_max_right 0 y, le_max_right 0 z]
  · linarith [le_max_right 0 x, le_max_left 0 y, le_max_left 0 z]

theorem oneCapCapSupport_segmentHull_eq_positiveParts
    {β : ℝ} (φ : ℝ) (hβ0 : 0 < β) (hβ : β < Real.pi / 2) :
    oneCapCapSupport segmentHull β φ =
      (1 / 3 : ℝ) *
        (max 0 (2 * Real.cos β * Real.sin φ) +
          max 0 (Real.sin (β - φ)) +
          max 0 (-Real.sin (β + φ))) := by
  have hc : 0 ≤ Real.cos β := (oneCap_cos_pos hβ0 hβ).le
  rw [oneCapCapSupport]
  rw [supportHull_nonneg_smul segmentHull _ _
      (mul_nonneg (by norm_num) hc),
    supportHull_nonneg_smul segmentHull _ _ (by norm_num),
    supportHull_nonneg_smul segmentHull _ _ (by norm_num)]
  simp only [supportHull_segmentHull, unitVec_re]
  have hsouth : Real.cos (φ - Real.pi / 2) = Real.sin φ := by
    rw [Real.cos_sub]
    simp
  have hleft : Real.cos (φ + Real.pi / 2 - β) = Real.sin (β - φ) := by
    rw [Real.cos_sub, Real.cos_add, Real.sin_add]
    simp [Real.sin_sub]
    ring
  have hright : Real.cos (φ + Real.pi / 2 + β) = -Real.sin (β + φ) := by
    rw [Real.cos_add, Real.cos_add, Real.sin_add]
    simp [Real.sin_add]
    ring
  rw [hsouth, hleft, hright]
  have hscale :
      (2 * Real.cos β) * max 0 (Real.sin φ) =
        max 0 (2 * Real.cos β * Real.sin φ) := by
    rw [mul_max_of_nonneg _ _ (mul_nonneg (by norm_num) hc), mul_zero]
  rw [← hscale]
  ring

theorem oneCapCapSupport_segmentHull_ge_Q
    {β : ℝ} (φ : ℝ) (hβ0 : 0 < β) (hβ : β < Real.pi / 2) :
    (1 / 3 : ℝ) * Payoff.Q β φ ≤
      oneCapCapSupport segmentHull β φ := by
  let x := 2 * Real.cos β * Real.sin φ
  let y := Real.sin (β - φ)
  let z := -Real.sin (β + φ)
  have hxyz : x + y + z = 0 := by
    dsimp [x, y, z]
    rw [Real.sin_sub, Real.sin_add]
    ring
  let S := max 0 x + max 0 y + max 0 z
  have hx : |x| ≤ S := abs_le_sum_max_zero_of_sum_zero x y z hxyz
  have hy : |y| ≤ S := by
    simpa [S, add_comm, add_left_comm, add_assoc] using
      abs_le_sum_max_zero_of_sum_zero y z x (by linarith)
  have hz : |z| ≤ S := by
    simpa [S, add_comm, add_left_comm, add_assoc] using
      abs_le_sum_max_zero_of_sum_zero z x y (by linarith)
  rw [oneCapCapSupport_segmentHull_eq_positiveParts φ hβ0 hβ]
  unfold Payoff.Q
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact max_le (by simpa [x, S] using hx)
    (max_le (by simpa [z, S] using hz) (by simpa [y, S] using hy))

theorem oneCapCapSupport_rotatedEquilateral_eq_P
    (θ : ℝ) {β : ℝ} (φ : ℝ) (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) :
    oneCapCapSupport (equilateralWalk.rotate θ).toFiniteHull β φ =
      (1 / 3 : ℝ) * Payoff.P θ β φ := by
  have hc : 0 ≤ Real.cos β := (oneCap_cos_pos hβ0 hβ).le
  rw [oneCapCapSupport]
  rw [supportHull_rotatedEquilateral_nonneg_smul_eq _ _ _
      (mul_nonneg (by norm_num) hc),
    supportHull_rotatedEquilateral_nonneg_smul_eq _ _ _ (by norm_num),
    supportHull_rotatedEquilateral_nonneg_smul_eq _ _ _ (by norm_num)]
  unfold Payoff.P
  ring

theorem oneCapCentralSupport_rotatedEquilateral_ge_triangle
    (θ φ : ℝ) :
    (1 / 6 : ℝ) *
        max
          (max |Real.sin (θ - φ)|
            |Real.sin (θ - φ + Real.pi / 3)|)
          |Real.cos (θ - φ + Real.pi / 6)| ≤
      oneCapCentralSupport (equilateralWalk.rotate θ).toFiniteHull φ := by
  let x := θ - φ
  let mS := Payoff.M θ (φ - Real.pi / 2)
  let mN := Payoff.M θ (φ + Real.pi / 2)
  have hLs : -Real.sin x ≤ mS := by
    have h := Payoff.M_ge_leftVertex θ (φ - Real.pi / 2)
    have hangle : θ - (φ - Real.pi / 2) = x + Real.pi / 2 := by
      dsimp [x]
      ring
    rw [hangle, Real.cos_add_pi_div_two] at h
    exact h
  have hLn : Real.sin x ≤ mN := by
    have h := Payoff.M_ge_leftVertex θ (φ + Real.pi / 2)
    have hangle : θ - (φ + Real.pi / 2) = x - Real.pi / 2 := by
      dsimp [x]
      ring
    rw [hangle, Real.cos_sub_pi_div_two] at h
    exact h
  have hRs : -Real.sin (x + Real.pi / 3) ≤ mS := by
    have h := Payoff.M_ge_rightVertex θ (φ - Real.pi / 2)
    have hangle : θ + Real.pi / 3 - (φ - Real.pi / 2) =
        (x + Real.pi / 3) + Real.pi / 2 := by
      dsimp [x]
      ring
    rw [hangle, Real.cos_add_pi_div_two] at h
    exact h
  have hRn : Real.sin (x + Real.pi / 3) ≤ mN := by
    have h := Payoff.M_ge_rightVertex θ (φ + Real.pi / 2)
    have hangle : θ + Real.pi / 3 - (φ + Real.pi / 2) =
        (x + Real.pi / 3) - Real.pi / 2 := by
      dsimp [x]
      ring
    rw [hangle, Real.cos_sub_pi_div_two] at h
    exact h
  have hmS0 : 0 ≤ mS := Payoff.M_nonneg _ _
  have hmN0 : 0 ≤ mN := Payoff.M_nonneg _ _
  have hx : |Real.sin x| ≤ mS + mN := by
    rw [abs_le]
    constructor <;> linarith
  have hx3 : |Real.sin (x + Real.pi / 3)| ≤ mS + mN := by
    rw [abs_le]
    constructor <;> linarith
  have hchord :
      Real.sin (x + Real.pi / 3) - Real.sin x =
        Real.cos (x + Real.pi / 6) := by
    rw [Real.sin_add, Real.cos_add, Real.sin_pi_div_three,
      Real.cos_pi_div_three, Real.sin_pi_div_six, Real.cos_pi_div_six]
    ring
  have hc : |Real.cos (x + Real.pi / 6)| ≤ mS + mN := by
    rw [abs_le]
    constructor <;> linarith
  have hmax :
      max (max |Real.sin x| |Real.sin (x + Real.pi / 3)|)
          |Real.cos (x + Real.pi / 6)| ≤ mS + mN :=
    max_le (max_le hx hx3) hc
  rw [oneCapCentralSupport]
  rw [supportHull_nonneg_smul _ _ _ (by norm_num),
    supportHull_nonneg_smul _ _ _ (by norm_num),
    supportHull_rotatedEquilateral_unitVec_eq_half_M,
    supportHull_rotatedEquilateral_unitVec_eq_half_M]
  change
    (1 / 6 : ℝ) *
        max (max |Real.sin x| |Real.sin (x + Real.pi / 3)|)
          |Real.cos (x + Real.pi / 6)| ≤
      (1 / 3 : ℝ) * ((1 / 2 : ℝ) * mS) +
        (1 / 3 : ℝ) * ((1 / 2 : ℝ) * mN)
  nlinarith

theorem oneCapCentralSupport_join_ge_A
    (θ φ : ℝ) (tS tE : Point) :
    (1 / 3 : ℝ) * Payoff.A θ φ ≤
      oneCapCentralSupport
        ((segmentHull.translate tS).join
          ((equilateralWalk.rotate θ).toFiniteHull.translate tE)) φ := by
  let J :=
    (segmentHull.translate tS).join
      ((equilateralWalk.rotate θ).toFiniteHull.translate tE)
  have hsegment :
      (1 / 3 : ℝ) * |Real.sin φ| ≤ oneCapCentralSupport J φ := by
    calc
      (1 / 3 : ℝ) * |Real.sin φ| =
          oneCapCentralSupport segmentHull φ :=
        (oneCapCentralSupport_segmentHull φ).symm
      _ = oneCapCentralSupport (segmentHull.translate tS) φ :=
        (oneCapCentralSupport_translate segmentHull tS φ).symm
      _ ≤ oneCapCentralSupport J φ := by
        exact oneCapCentralSupport_le_join_left _ _ φ
  have hequilateral :
      (1 / 6 : ℝ) *
          max
            (max |Real.sin (θ - φ)|
              |Real.sin (θ - φ + Real.pi / 3)|)
            |Real.cos (θ - φ + Real.pi / 6)| ≤
        oneCapCentralSupport J φ := by
    calc
      _ ≤ oneCapCentralSupport (equilateralWalk.rotate θ).toFiniteHull φ :=
        oneCapCentralSupport_rotatedEquilateral_ge_triangle θ φ
      _ = oneCapCentralSupport
          ((equilateralWalk.rotate θ).toFiniteHull.translate tE) φ :=
        (oneCapCentralSupport_translate _ tE φ).symm
      _ ≤ oneCapCentralSupport J φ := by
        exact oneCapCentralSupport_le_join_right _ _ φ
  unfold Payoff.A
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  apply max_le hsegment
  nlinarith

theorem oneCapCapSupport_join_ge_B
    (θ : ℝ) {β : ℝ} (φ : ℝ) (hβ0 : 0 < β)
    (hβ : β < Real.pi / 2) (tS tE : Point) :
    (1 / 3 : ℝ) * Payoff.B θ β φ ≤
      oneCapCapSupport
        ((segmentHull.translate tS).join
          ((equilateralWalk.rotate θ).toFiniteHull.translate tE)) β φ := by
  let J :=
    (segmentHull.translate tS).join
      ((equilateralWalk.rotate θ).toFiniteHull.translate tE)
  have hsegment :
      (1 / 3 : ℝ) * Payoff.Q β φ ≤ oneCapCapSupport J β φ := by
    calc
      _ ≤ oneCapCapSupport segmentHull β φ :=
        oneCapCapSupport_segmentHull_ge_Q φ hβ0 hβ
      _ = oneCapCapSupport (segmentHull.translate tS) β φ :=
        (oneCapCapSupport_translate segmentHull tS β φ).symm
      _ ≤ oneCapCapSupport J β φ := by
        exact oneCapCapSupport_le_join_left _ _ β φ
  have hequilateral :
      (1 / 3 : ℝ) * Payoff.P θ β φ ≤ oneCapCapSupport J β φ := by
    calc
      _ = oneCapCapSupport (equilateralWalk.rotate θ).toFiniteHull β φ :=
        (oneCapCapSupport_rotatedEquilateral_eq_P θ φ hβ0 hβ).symm
      _ = oneCapCapSupport
          ((equilateralWalk.rotate θ).toFiniteHull.translate tE) β φ :=
        (oneCapCapSupport_translate _ tE β φ).symm
      _ ≤ oneCapCapSupport J β φ := by
        exact oneCapCapSupport_le_join_right _ _ β φ
  unfold Payoff.B
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  exact max_le hsegment hequilateral

theorem oneCap_mixedSupport_ge_payoff
    (θ φ β : ℝ) (hβ0 : 0 < β) (hβ : β < Real.pi / 2)
    (tS tE : Point) :
    (Payoff.A θ φ + Payoff.B θ β φ) / 6 ≤
      mixedSupport
        ((segmentHull.translate tS).join
          ((equilateralWalk.rotate θ).toFiniteHull.translate tE))
        ((oneCapPositiveSupportBoundary β hβ0 hβ).rotate φ).walk := by
  let J :=
    (segmentHull.translate tS).join
      ((equilateralWalk.rotate θ).toFiniteHull.translate tE)
  have hcentral :
      (1 / 3 : ℝ) * Payoff.A θ φ ≤ oneCapCentralSupport J φ :=
    oneCapCentralSupport_join_ge_A θ φ tS tE
  have hcap :
      (1 / 3 : ℝ) * Payoff.B θ β φ ≤ oneCapCapSupport J β φ :=
    oneCapCapSupport_join_ge_B θ φ hβ0 hβ tS tE
  change
    (Payoff.A θ φ + Payoff.B θ β φ) / 6 ≤
      mixedSupport J ((oneCapWalk β).rotate φ)
  rw [mixedSupport_rotate_oneCap_eq_blocks J φ hβ0 hβ]
  linarith

theorem oneCapPayoff_le_volumeReal_of_contains_witnesses
    (θ φ β : ℝ) (hβ0 : 0 < β) (hβ : β < Real.pi / 2)
    (tS tE tK : Point) {C : Set Point} (hC : Convex ℝ C)
    (hCfinite : volume C ≠ ⊤)
    (hSegment : (segmentHull.translate tS).carrier ⊆ C)
    (hEquilateral :
      ((equilateralWalk.rotate θ).toFiniteHull.translate tE).carrier ⊆ C)
    (hOneCap :
      (((oneCapPositiveSupportBoundary β hβ0 hβ).rotate φ).translate tK).walk.toFiniteHull.carrier ⊆ C) :
    (Payoff.A θ φ + Payoff.B θ β φ) / 6 ≤ volume.real C := by
  let H :=
    (segmentHull.translate tS).join
      ((equilateralWalk.rotate θ).toFiniteHull.translate tE)
  let P :=
    ((oneCapPositiveSupportBoundary β hβ0 hβ).rotate φ).translate tK
  have hH : H.carrier ⊆ C := by
    exact FiniteHull.join_carrier_subset _ _ hC hSegment hEquilateral
  calc
    (Payoff.A θ φ + Payoff.B θ β φ) / 6 ≤
        mixedSupport H
          ((oneCapPositiveSupportBoundary β hβ0 hβ).rotate φ).walk :=
      oneCap_mixedSupport_ge_payoff θ φ β hβ0 hβ tS tE
    _ = mixedSupport H P.walk := by
      change
        mixedSupport H ((oneCapWalk β).rotate φ) =
          mixedSupport H (((oneCapWalk β).rotate φ).translate tK)
      rw [mixedSupport_translate_second]
    _ ≤ volume.real C :=
      PositiveSupportBoundary.mixedSupport_le_volumeReal_of_positiveSupportBoundary
        P H hC hCfinite hH hOneCap


end

end MoserWorm

end


-- MoserWorm.Basic.RigidPlacement
section

namespace MoserWorm

noncomputable section

open MeasureTheory

structure RigidPlacement where
  mirror : Bool
  angle : ℝ
  shift : Point

namespace RigidPlacement

def linearPart (g : RigidPlacement) : Point ≃ₗᵢ[ℝ] Point :=
  match g.mirror with
  | false => rot g.angle
  | true => reflectX.trans (rot g.angle)

def direct (angle : ℝ) (shift : Point) : RigidPlacement where
  mirror := false
  angle := angle
  shift := shift

def reflected (angle : ℝ) (shift : Point) : RigidPlacement where
  mirror := true
  angle := angle
  shift := shift

@[simp] theorem direct_mirror (angle : ℝ) (shift : Point) :
    (direct angle shift).mirror = false := rfl

@[simp] theorem linearPart_direct (angle : ℝ) (shift : Point) :
    (direct angle shift).linearPart = rot angle := rfl

def toAffineIsometryEquiv (g : RigidPlacement) : Point ≃ᵃⁱ[ℝ] Point :=
  g.linearPart.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ Point g.shift)

instance : CoeFun RigidPlacement (fun _ ↦ Point → Point) where
  coe g := g.toAffineIsometryEquiv

@[simp] theorem apply_eq (g : RigidPlacement) (p : Point) :
    g p = g.shift + g.linearPart p := by
  rfl

@[simp] theorem direct_apply (angle : ℝ) (shift p : Point) :
    direct angle shift p = shift + rot angle p := by
  rfl

@[simp] theorem reflected_apply (angle : ℝ) (shift p : Point) :
    reflected angle shift p = shift + rot angle (reflectX p) := by
  rfl

def compose (g h : RigidPlacement) : RigidPlacement where
  mirror := Bool.xor g.mirror h.mirror
  angle := g.angle + if g.mirror then -h.angle else h.angle
  shift := g.shift + g.linearPart h.shift

def inverse (g : RigidPlacement) : RigidPlacement where
  mirror := g.mirror
  angle := if g.mirror then g.angle else -g.angle
  shift := -g.linearPart.symm g.shift

theorem linearPart_compose_apply (g h : RigidPlacement) (p : Point) :
    (g.compose h).linearPart p = g.linearPart (h.linearPart p) := by
  rcases g with ⟨gm, ga, gs⟩
  rcases h with ⟨hm, ha, hs⟩
  cases gm <;> cases hm
  all_goals
    simp only [compose, linearPart, Bool.xor_false, Bool.xor_true,
      Bool.not_true, if_true, LinearIsometryEquiv.trans_apply]
  · exact rot_add_apply ga ha p
  · exact rot_add_apply ga ha (reflectX p)
  · rw [reflectX_rot, ← rot_add_apply]
  · rw [reflectX_rot, reflectX_reflectX, ← rot_add_apply]

@[simp] theorem compose_apply (g h : RigidPlacement) (p : Point) :
    g.compose h p = g (h p) := by
  simp only [apply_eq]
  change
    (g.shift + g.linearPart h.shift) + (g.compose h).linearPart p =
      g.shift + g.linearPart (h.shift + h.linearPart p)
  rw [linearPart_compose_apply, map_add]
  abel

theorem inverse_linearPart_apply_linearPart (g : RigidPlacement) (p : Point) :
    g.inverse.linearPart (g.linearPart p) = p := by
  rcases g with ⟨gm, ga, gs⟩
  cases gm
  · change rot (-ga) (rot ga p) = p
    exact rot_neg_apply_rot ga p
  · change rot ga (reflectX (rot ga (reflectX p))) = p
    rw [reflectX_rot, reflectX_reflectX]
    rw [← rot_add_apply]
    simp [rot_apply]

theorem inverse_linearPart_eq_symm_apply (g : RigidPlacement) (p : Point) :
    g.inverse.linearPart p = g.linearPart.symm p := by
  calc
    g.inverse.linearPart p =
        g.inverse.linearPart (g.linearPart (g.linearPart.symm p)) := by
      rw [g.linearPart.apply_symm_apply]
    _ = g.linearPart.symm p :=
      g.inverse_linearPart_apply_linearPart (g.linearPart.symm p)

@[simp] theorem inverse_apply_apply (g : RigidPlacement) (p : Point) :
    g.inverse (g p) = p := by
  simp only [apply_eq]
  change
    -g.linearPart.symm g.shift +
        g.inverse.linearPart (g.shift + g.linearPart p) = p
  rw [inverse_linearPart_eq_symm_apply, map_add,
    LinearIsometryEquiv.symm_apply_apply]
  abel

@[simp] theorem inverse_image_image (g : RigidPlacement) (s : Set Point) :
    g.inverse '' (g '' s) = s := by
  ext p
  constructor
  · rintro ⟨-, ⟨q, hq, rfl⟩, rfl⟩
    rw [g.inverse_apply_apply]
    exact hq
  · intro hp
    exact ⟨g p, ⟨p, hp, rfl⟩, g.inverse_apply_apply p⟩

theorem injective (g : RigidPlacement) : Function.Injective g :=
  g.toAffineIsometryEquiv.injective

theorem measurePreserving (g : RigidPlacement) :
    MeasureTheory.MeasurePreserving g := by
  have hlinear : MeasureTheory.MeasurePreserving g.linearPart :=
    LinearIsometryEquiv.measurePreserving g.linearPart
  have htranslate :
      MeasureTheory.MeasurePreserving (fun p : Point ↦ g.shift + p) :=
    measurePreserving_add_left volume g.shift
  convert htranslate.comp hlinear using 1 <;> funext p <;> exact g.apply_eq p

theorem volume_image (g : RigidPlacement) (s : Set Point) :
    volume (g '' s) = volume s := by
  let e : Point ≃ᵐ Point :=
    g.toAffineIsometryEquiv.toHomeomorph.toMeasurableEquiv
  have he : MeasureTheory.MeasurePreserving e := by
    simpa [e] using g.measurePreserving
  calc
    volume (g '' s) = volume (e '' s) := rfl
    _ = volume (e.symm ⁻¹' s) := by rw [e.image_eq_preimage_symm]
    _ = volume s :=
      (MeasureTheory.MeasurePreserving.symm e he).measure_preimage_equiv s

theorem isCompact_image_iff (g : RigidPlacement) (s : Set Point) :
    IsCompact (g '' s) ↔ IsCompact s := by
  exact g.toAffineIsometryEquiv.toHomeomorph.isCompact_image

theorem convex_image (g : RigidPlacement) {s : Set Point}
    (hs : Convex ℝ s) : Convex ℝ (g '' s) := by
  exact hs.affine_image g.toAffineIsometryEquiv.toAffineEquiv.toAffineMap

theorem image_convexHull (g : RigidPlacement) (s : Set Point) :
    g '' convexHull ℝ s = convexHull ℝ (g '' s) := by
  exact g.toAffineIsometryEquiv.toAffineEquiv.toAffineMap.image_convexHull s

end RigidPlacement

inductive MotionMode where
  | direct
  | reflectionAllowed
  deriving DecidableEq

def placementAllowed (mode : MotionMode) (g : RigidPlacement) : Prop :=
  match mode with
  | .direct => g.mirror = false
  | .reflectionAllowed => True

@[simp] theorem placementAllowed_direct_iff (g : RigidPlacement) :
    placementAllowed .direct g ↔ g.mirror = false := by
  rfl

@[simp] theorem placementAllowed_reflectionAllowed (g : RigidPlacement) :
    placementAllowed .reflectionAllowed g := by
  trivial

theorem placementAllowed.compose {mode : MotionMode} {g h : RigidPlacement}
    (hg : placementAllowed mode g) (hh : placementAllowed mode h) :
    placementAllowed mode (g.compose h) := by
  cases mode
  · simp only [placementAllowed] at hg hh ⊢
    simp [RigidPlacement.compose, hg, hh]
  · trivial

theorem placementAllowed.inverse {mode : MotionMode} {g : RigidPlacement}
    (hg : placementAllowed mode g) :
    placementAllowed mode g.inverse := by
  cases mode
  · simpa [placementAllowed, RigidPlacement.inverse] using hg
  · trivial

end

end MoserWorm

end


-- MoserWorm.Geometry.Polyline
section

namespace MoserWorm

noncomputable section

structure Polyline (n : ℕ) where
  vertex : Fin (n + 1) → Point

namespace Polyline

def edge {n : ℕ} (P : Polyline n) (i : Fin n) : Point :=
  P.vertex i.succ - P.vertex i.castSucc

def edgeLengthSum {n : ℕ} (P : Polyline n) : ℝ :=
  ∑ i : Fin n, ‖P.edge i‖

def toFiniteHull {n : ℕ} (P : Polyline n) : FiniteHull := by
  classical
  exact
    { vertices := Finset.univ.image P.vertex
      nonempty := by
        refine ⟨P.vertex 0, ?_⟩
        exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩ }

theorem vertex_mem_toFiniteHull_vertices {n : ℕ} (P : Polyline n)
    (i : Fin (n + 1)) : P.vertex i ∈ P.toFiniteHull.vertices := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem vertex_mem_toFiniteHull_carrier {n : ℕ} (P : Polyline n)
    (i : Fin (n + 1)) : P.vertex i ∈ P.toFiniteHull.carrier :=
  P.toFiniteHull.vertices_subset_carrier (P.vertex_mem_toFiniteHull_vertices i)

def image {n : ℕ} (P : Polyline n) : Set Point :=
  Set.range P.vertex ∪
    ⋃ i : Fin n, segment ℝ (P.vertex i.castSucc) (P.vertex i.succ)

theorem vertex_mem_image {n : ℕ} (P : Polyline n) (i : Fin (n + 1)) :
    P.vertex i ∈ P.image := by
  exact Set.mem_union_left _ ⟨i, rfl⟩

theorem image_subset_toFiniteHull_carrier {n : ℕ} (P : Polyline n) :
    P.image ⊆ P.toFiniteHull.carrier := by
  rintro p (hp | hp)
  · obtain ⟨i, rfl⟩ := hp
    exact P.vertex_mem_toFiniteHull_carrier i
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    exact P.toFiniteHull.carrier_convex.segment_subset
      (P.vertex_mem_toFiniteHull_carrier i.castSucc)
      (P.vertex_mem_toFiniteHull_carrier i.succ) hi

theorem vertices_subset_image {n : ℕ} (P : Polyline n) :
    (P.toFiniteHull.vertices : Set Point) ⊆ P.image := by
  classical
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨i, -, rfl⟩
  exact P.vertex_mem_image i

theorem convexHull_image_eq_toFiniteHull_carrier {n : ℕ} (P : Polyline n) :
    convexHull ℝ P.image = P.toFiniteHull.carrier := by
  apply Set.Subset.antisymm
  · exact convexHull_min P.image_subset_toFiniteHull_carrier
      P.toFiniteHull.carrier_convex
  · unfold FiniteHull.carrier
    exact convexHull_mono P.vertices_subset_image

theorem placed_hull_subset {n : ℕ} (P : Polyline n)
    (g : RigidPlacement) {C : Set Point} (hC : Convex ℝ C)
    (hP : g '' P.image ⊆ C) :
    g '' P.toFiniteHull.carrier ⊆ C := by
  rw [← P.convexHull_image_eq_toFiniteHull_carrier,
    g.image_convexHull]
  exact convexHull_min hP hC

end Polyline

structure UnitPolyline where
  n : ℕ
  path : Polyline n
  length_le_one : path.edgeLengthSum ≤ 1

end

end MoserWorm

end


-- MoserWorm.Geometry.ConvexCover
section

namespace MoserWorm

noncomputable section

open MeasureTheory

structure ConvexCover where
  carrier : Set Point
  nonempty : carrier.Nonempty
  compact : IsCompact carrier
  convex : Convex ℝ carrier

def areaReal (A : Set Point) : ℝ :=
  (volume A).toReal

def coverArea (C : ConvexCover) : ℝ :=
  areaReal C.carrier

namespace ConvexCover

theorem volume_ne_top (C : ConvexCover) : volume C.carrier ≠ ⊤ :=
  C.compact.measure_ne_top

def transform (C : ConvexCover) (g : RigidPlacement) : ConvexCover where
  carrier := g '' C.carrier
  nonempty := C.nonempty.image g
  compact := (g.isCompact_image_iff C.carrier).2 C.compact
  convex := g.convex_image C.convex

@[simp] theorem transform_carrier (C : ConvexCover) (g : RigidPlacement) :
    (C.transform g).carrier = g '' C.carrier := rfl

@[simp] theorem coverArea_transform (C : ConvexCover) (g : RigidPlacement) :
    coverArea (C.transform g) = coverArea C := by
  simp only [coverArea, areaReal, transform_carrier, g.volume_image C.carrier]

end ConvexCover

def PlacesEveryUnitPolyline (C : ConvexCover) (mode : MotionMode) : Prop :=
  ∀ P : UnitPolyline,
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧ g '' P.path.image ⊆ C.carrier

namespace PlacesEveryUnitPolyline

theorem transform {C : ConvexCover} {mode : MotionMode}
    (hC : PlacesEveryUnitPolyline C mode) (h : RigidPlacement)
    (hh : placementAllowed mode h) :
    PlacesEveryUnitPolyline (C.transform h) mode := by
  intro P
  obtain ⟨g, hg, hP⟩ := hC P
  refine ⟨h.compose g, hh.compose hg, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [RigidPlacement.compose_apply]
  exact ⟨g p, hP ⟨p, hp, rfl⟩, rfl⟩

theorem placed_hull_subset {C : ConvexCover} {mode : MotionMode}
    (hC : PlacesEveryUnitPolyline C mode) (P : UnitPolyline) :
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧
        g '' P.path.toFiniteHull.carrier ⊆ C.carrier := by
  obtain ⟨g, hg, hP⟩ := hC P
  exact ⟨g, hg, P.path.placed_hull_subset g C.convex hP⟩

end PlacesEveryUnitPolyline

end

end MoserWorm

end


-- MoserWorm.Geometry.UniversalCover
section

namespace MoserWorm

noncomputable section

open Set
open scoped ENNReal NNReal

structure UnitWorm where
  curve : ℝ → Point
  continuousOn : ContinuousOn curve (Icc 0 1)
  variation_le_one : eVariationOn curve (Icc 0 1) ≤ 1

namespace UnitWorm

def carrier (W : UnitWorm) : Set Point :=
  W.curve '' Icc 0 1

end UnitWorm

def UniversalForUnitWorms (C : ConvexCover) (mode : MotionMode) : Prop :=
  ∀ W : UnitWorm,
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧ g '' W.carrier ⊆ C.carrier

namespace Polyline

def vertexAt {n : ℕ} (P : Polyline n) (i : ℕ) : Point :=
  P.vertex ⟨min i n, Nat.lt_succ_of_le (Nat.min_le_right i n)⟩

theorem vertexAt_eq {n i : ℕ} (P : Polyline n) (hi : i ≤ n) :
    P.vertexAt i = P.vertex ⟨i, Nat.lt_succ_of_le hi⟩ := by
  simp [vertexAt, Nat.min_eq_left hi]

@[simp] theorem vertexAt_zero {n : ℕ} (P : Polyline n) :
    P.vertexAt 0 = P.vertex 0 := by
  rw [P.vertexAt_eq (Nat.zero_le n)]
  congr

def edgeAt {n : ℕ} (P : Polyline n) (i : ℕ) : Point :=
  P.vertexAt (i + 1) - P.vertexAt i

theorem edgeAt_eq_edge {n i : ℕ} (P : Polyline n) (hi : i < n) :
    P.edgeAt i = P.edge ⟨i, hi⟩ := by
  simp only [edgeAt, edge, P.vertexAt_eq hi.le,
    P.vertexAt_eq (Nat.succ_le_iff.2 hi)]
  congr

def knot (n k : ℕ) : ℝ :=
  (k : ℝ) / ((n + 1 : ℕ) : ℝ)

def ramp (n i : ℕ) (t : ℝ) : ℝ :=
  min 1 (max 0 (((n + 1 : ℕ) : ℝ) * t - (i : ℝ)))

theorem continuous_ramp (n i : ℕ) : Continuous (ramp n i) := by
  unfold ramp
  fun_prop

theorem monotone_ramp (n i : ℕ) : Monotone (ramp n i) := by
  intro a b hab
  unfold ramp
  apply min_le_min le_rfl
  apply max_le_max le_rfl
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))) _

@[simp] theorem ramp_zero (n i : ℕ) : ramp n i 0 = 0 := by
  simp [ramp, Nat.cast_nonneg]

theorem ramp_one {n i : ℕ} (hi : i < n) : ramp n i 1 = 1 := by
  unfold ramp
  have hi' : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi.le
  have h : (1 : ℝ) ≤ (n + 1 : ℕ) * 1 - i := by
    norm_num only [Nat.cast_add, Nat.cast_one, mul_one]
    linarith
  rw [max_eq_right (zero_le_one.trans h), min_eq_left h]

theorem scale_mul_knot (n k : ℕ) :
    ((n + 1 : ℕ) : ℝ) * knot n k = k := by
  unfold knot
  rw [mul_comm, div_mul_cancel₀]
  positivity

theorem ramp_knot_of_lt {n i k : ℕ} (hik : i < k) :
    ramp n i (knot n k) = 1 := by
  unfold ramp
  rw [scale_mul_knot]
  have hik' : (i : ℝ) < (k : ℝ) := by exact_mod_cast hik
  have h : (1 : ℝ) ≤ (k : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_iff.2 hik
    linarith
  rw [max_eq_right (zero_le_one.trans h), min_eq_left h]

theorem ramp_knot_of_le {n i k : ℕ} (hki : k ≤ i) :
    ramp n i (knot n k) = 0 := by
  unfold ramp
  rw [scale_mul_knot]
  have h : (k : ℝ) - i ≤ 0 := sub_nonpos.2 (by exact_mod_cast hki)
  rw [max_eq_left h]
  simp

def curve {n : ℕ} (P : Polyline n) (t : ℝ) : Point :=
  P.vertex 0 + ∑ i ∈ Finset.range n, ramp n i t • P.edgeAt i

theorem continuous_curve {n : ℕ} (P : Polyline n) : Continuous P.curve := by
  unfold curve
  exact continuous_const.add <| continuous_finset_sum (Finset.range n) fun i _ ↦
    by
      exact (continuous_ramp n i).smul continuous_const

theorem knot_mem_unitInterval {n : ℕ} (k : Fin (n + 1)) :
    knot n k ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).2
    exact_mod_cast k.isLt.le

theorem curve_knot {n : ℕ} (P : Polyline n) (k : Fin (n + 1)) :
    P.curve (knot n k) = P.vertex k := by
  have hk : k.val ≤ n := Nat.lt_succ_iff.1 k.isLt
  unfold curve
  have hsmul (i : ℕ) :
      ramp n i (knot n k.val) • P.edgeAt i =
        if i < k.val then P.edgeAt i else 0 := by
    by_cases hik : i < k.val
    · rw [ramp_knot_of_lt hik, if_pos hik]
      simp
    · rw [ramp_knot_of_le (Nat.le_of_not_gt hik), if_neg hik]
      simp
  simp_rw [hsmul]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range n).filter (fun i ↦ i < k.val) =
      Finset.range k.val := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  simp only [edgeAt, Finset.sum_range_sub]
  rw [P.vertexAt_eq hk, P.vertexAt_zero]
  abel

theorem vertex_mem_curve_carrier {n : ℕ} (P : Polyline n)
    (k : Fin (n + 1)) : P.vertex k ∈ P.curve '' Icc (0 : ℝ) 1 := by
  exact ⟨knot n k, knot_mem_unitInterval k, P.curve_knot k⟩

theorem eVariationOn_add_le (f g : ℝ → Point) (s : Set ℝ) :
    eVariationOn (fun t ↦ f t + g t) s ≤
      eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨m, u, hu, hs⟩
  calc
    (∑ i ∈ Finset.range m,
        edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))) ≤
        ∑ i ∈ Finset.range m,
          (edist (f (u (i + 1))) (f (u i)) +
            edist (g (u (i + 1))) (g (u i))) := by
      exact Finset.sum_le_sum fun i _ ↦ edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range m, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range m, edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f s + eVariationOn g s :=
      add_le_add (eVariationOn.sum_le hu hs) (eVariationOn.sum_le hu hs)

theorem eVariationOn_finset_sum_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → Point) (s : Set ℝ) :
    eVariationOn (fun t ↦ ∑ i ∈ S, f i t) s ≤
      ∑ i ∈ S, eVariationOn (f i) s := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact le_of_eq <| (eVariationOn.eq_zero_iff _).2 (by simp)
  | @insert a S ha ih =>
      simpa only [Finset.sum_insert ha] using
        (eVariationOn_add_le (f a) (fun t ↦ ∑ i ∈ S, f i t) s).trans
          (add_le_add le_rfl ih)

theorem eVariationOn_const_add (c : Point) (f : ℝ → Point) (s : Set ℝ) :
    eVariationOn (fun t ↦ c + f t) s = eVariationOn f s := by
  simp [eVariationOn]

theorem eVariationOn_ramp_le_one {n i : ℕ} (hi : i < n) :
    eVariationOn (ramp n i) (Icc (0 : ℝ) 1) ≤ 1 := by
  have hmon : MonotoneOn (ramp n i) Set.univ :=
    (monotone_ramp n i).monotoneOn _
  have h := MonotoneOn.eVariationOn_le hmon
    (s := Set.univ) (a := (0 : ℝ)) (b := 1)
    (Set.mem_univ 0) (Set.mem_univ 1)
  simpa [ramp_zero, ramp_one hi] using h

theorem eVariationOn_ramp_smul_edgeAt_le {n i : ℕ}
    (P : Polyline n) (hi : i < n) :
    eVariationOn (fun t ↦ ramp n i t • P.edgeAt i) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ‖P.edgeAt i‖ := by
  have h := (lipschitzWith_lineMap (0 : Point) (P.edgeAt i)).lipschitzOnWith
    |>.comp_eVariationOn_le (g := ramp n i) (s := Icc (0 : ℝ) 1)
      (t := Set.univ) (Set.mapsTo_univ _ _)
  calc
    eVariationOn (fun t ↦ ramp n i t • P.edgeAt i) (Icc (0 : ℝ) 1) =
        eVariationOn (AffineMap.lineMap 0 (P.edgeAt i) ∘ ramp n i)
          (Icc (0 : ℝ) 1) := by
      congr 1
      funext t
      simp only [Function.comp_apply, AffineMap.lineMap_apply_module, smul_zero,
        zero_add]
    _ ≤ (nndist (0 : Point) (P.edgeAt i) : ℝ≥0∞) *
        eVariationOn (ramp n i) (Icc (0 : ℝ) 1) := h
    _ ≤ (nndist (0 : Point) (P.edgeAt i) : ℝ≥0∞) * 1 := by
      gcongr
      exact eVariationOn_ramp_le_one hi
    _ = ENNReal.ofReal ‖P.edgeAt i‖ := by
      simp [nndist_eq_nnnorm, ofReal_norm, enorm_eq_nnnorm]

theorem sum_edgeAt_norm_eq_edgeLengthSum {n : ℕ} (P : Polyline n) :
    ∑ i ∈ Finset.range n, ‖P.edgeAt i‖ = P.edgeLengthSum := by
  rw [edgeLengthSum, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [dif_pos hi, P.edgeAt_eq_edge hi]

theorem curve_eVariationOn_le_edgeLengthSum {n : ℕ} (P : Polyline n) :
    eVariationOn P.curve (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal P.edgeLengthSum := by
  calc
    eVariationOn P.curve (Icc (0 : ℝ) 1) =
        eVariationOn (fun t ↦ ∑ i ∈ Finset.range n,
          ramp n i t • P.edgeAt i) (Icc (0 : ℝ) 1) := by
      exact eVariationOn_const_add (P.vertex 0) _ _
    _ ≤ ∑ i ∈ Finset.range n,
        eVariationOn (fun t ↦ ramp n i t • P.edgeAt i) (Icc (0 : ℝ) 1) :=
      eVariationOn_finset_sum_le (Finset.range n) _ _
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal ‖P.edgeAt i‖ := by
      exact Finset.sum_le_sum fun i hi ↦
        eVariationOn_ramp_smul_edgeAt_le P (Finset.mem_range.1 hi)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ‖P.edgeAt i‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun _ _ ↦ norm_nonneg _
    _ = ENNReal.ofReal P.edgeLengthSum := by
      rw [P.sum_edgeAt_norm_eq_edgeLengthSum]

def toUnitWorm {n : ℕ} (P : Polyline n) (hP : P.edgeLengthSum ≤ 1) : UnitWorm where
  curve := P.curve
  continuousOn := P.continuous_curve.continuousOn
  variation_le_one := P.curve_eVariationOn_le_edgeLengthSum.trans <| by
    simpa using ENNReal.ofReal_le_ofReal hP

theorem vertex_mem_toUnitWorm_carrier {n : ℕ} (P : Polyline n)
    (hP : P.edgeLengthSum ≤ 1) (k : Fin (n + 1)) :
    P.vertex k ∈ (P.toUnitWorm hP).carrier := by
  exact P.vertex_mem_curve_carrier k

end Polyline

namespace UniversalForUnitWorms

theorem transform {C : ConvexCover} {mode : MotionMode}
    (hC : UniversalForUnitWorms C mode) (h : RigidPlacement)
    (hh : placementAllowed mode h) :
    UniversalForUnitWorms (C.transform h) mode := by
  intro W
  obtain ⟨g, hg, hW⟩ := hC W
  refine ⟨h.compose g, hh.compose hg, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [RigidPlacement.compose_apply]
  exact ⟨g p, hW ⟨p, hp, rfl⟩, rfl⟩

theorem placesEveryUnitPolyline {C : ConvexCover} {mode : MotionMode}
    (hC : UniversalForUnitWorms C mode) : PlacesEveryUnitPolyline C mode := by
  intro P
  obtain ⟨g, hg, hcurve⟩ := hC (P.path.toUnitWorm P.length_le_one)
  refine ⟨g, hg, ?_⟩
  have hhull : g '' P.path.toFiniteHull.carrier ⊆ C.carrier := by
    rw [FiniteHull.carrier, g.image_convexHull]
    apply convexHull_min _ C.convex
    rintro _ ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hp with ⟨k, -, rfl⟩
    exact hcurve ⟨P.path.vertex k,
      P.path.vertex_mem_toUnitWorm_carrier P.length_le_one k, rfl⟩
  exact Set.image_mono P.path.image_subset_toFiniteHull_carrier |>.trans hhull

end UniversalForUnitWorms

end

end MoserWorm

end


-- MoserWorm.Witness.AngleNormalization
section

namespace MoserWorm

noncomputable section

open scoped Pointwise

def TranslationEquivalent (A B : Set Point) : Prop :=
  ∃ t : Point, t +ᵥ A = B

namespace TranslationEquivalent

theorem refl (A : Set Point) : TranslationEquivalent A A := by
  refine ⟨0, ?_⟩
  simp

theorem symm {A B : Set Point} (h : TranslationEquivalent A B) :
    TranslationEquivalent B A := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨-t, ?_⟩
  rw [← add_vadd]
  simp

theorem trans {A B C : Set Point} (hAB : TranslationEquivalent A B)
    (hBC : TranslationEquivalent B C) : TranslationEquivalent A C := by
  obtain ⟨t, ht⟩ := hAB
  obtain ⟨u, hu⟩ := hBC
  refine ⟨u + t, ?_⟩
  rw [add_vadd, ht, hu]

theorem target_vadd {A B : Set Point} (h : TranslationEquivalent A B)
    (u : Point) : ∃ v : Point, v +ᵥ A = u +ᵥ B := by
  obtain ⟨t, ht⟩ := h
  refine ⟨u + t, ?_⟩
  rw [add_vadd, ht]

end TranslationEquivalent

private theorem translationEquivalent_nat_mul
    (F : ℝ → Set Point) (p a : ℝ)
    (hstep : ∀ x : ℝ, TranslationEquivalent (F (x + p)) (F x)) :
    ∀ n : ℕ,
      TranslationEquivalent (F (a + (n : ℝ) * p)) (F a) := by
  intro n
  induction n with
  | zero =>
      simpa using TranslationEquivalent.refl (F a)
  | succ n ih =>
      have hs := hstep (a + (n : ℝ) * p)
      have harg :
          a + ((n + 1 : ℕ) : ℝ) * p =
            (a + (n : ℝ) * p) + p := by
        push_cast
        ring
      rw [harg]
      exact hs.trans ih

private theorem translationEquivalent_nat_neg_mul
    (F : ℝ → Set Point) (p a : ℝ)
    (hstep : ∀ x : ℝ, TranslationEquivalent (F (x + p)) (F x)) :
    ∀ n : ℕ,
      TranslationEquivalent (F (a - (n : ℝ) * p)) (F a) := by
  intro n
  induction n with
  | zero =>
      simpa using TranslationEquivalent.refl (F a)
  | succ n ih =>
      have hs := hstep (a - ((n + 1 : ℕ) : ℝ) * p)
      have harg :
          (a - ((n + 1 : ℕ) : ℝ) * p) + p =
            a - (n : ℝ) * p := by
        push_cast
        ring
      have hback :
          TranslationEquivalent
            (F (a - ((n + 1 : ℕ) : ℝ) * p))
            (F (a - (n : ℝ) * p)) := by
        rw [← harg]
        exact hs.symm
      exact hback.trans ih

theorem translationEquivalent_int_mul
    (F : ℝ → Set Point) (p a : ℝ)
    (hstep : ∀ x : ℝ, TranslationEquivalent (F (x + p)) (F x))
    (k : ℤ) :
    TranslationEquivalent (F (a + (k : ℝ) * p)) (F a) := by
  cases k with
  | ofNat n =>
      simpa using translationEquivalent_nat_mul F p a hstep n
  | negSucc n =>
      have hneg := translationEquivalent_nat_neg_mul F p a hstep (n + 1)
      simpa only [Int.cast_negSucc, neg_mul, sub_eq_add_neg] using hneg

theorem segmentHullAt_int_pi_translationEquivalent (α : ℝ) (k : ℤ) :
    TranslationEquivalent
      (segmentHullAt (α + (k : ℝ) * Real.pi)).carrier
      (segmentHullAt α).carrier := by
  refine translationEquivalent_int_mul
    (fun x ↦ (segmentHullAt x).carrier) Real.pi α ?_ k
  intro x
  refine ⟨unitVec x, ?_⟩
  rw [← FiniteHull.carrier_translate]
  exact segmentHullAt_add_pi_translate_carrier x

theorem equilateral_int_thirdTurn_translationEquivalent (β : ℝ) (k : ℤ) :
    TranslationEquivalent
      (equilateralWalk.rotate
        (β + (k : ℝ) * (2 * Real.pi / 3))).toFiniteHull.carrier
      (equilateralWalk.rotate β).toFiniteHull.carrier := by
  refine translationEquivalent_int_mul
    (fun x ↦ (equilateralWalk.rotate x).toFiniteHull.carrier)
    (2 * Real.pi / 3) β ?_ k
  intro x
  refine ⟨(1 / 2 : ℝ) • unitVec x, ?_⟩
  rw [← BoundaryWalk.translate_toFiniteHull_carrier]
  exact equilateral_thirdTurn_translate_carrier x

def relativeAnglePeriod : ℝ := Real.pi / 3

theorem relativeAnglePeriod_pos : 0 < relativeAnglePeriod := by
  unfold relativeAnglePeriod
  positivity

def centeredRelativeIndex (θ : ℝ) : ℤ :=
  ⌊θ / relativeAnglePeriod + 1 / 2⌋

def centeredRelativeAngle (θ : ℝ) : ℝ :=
  θ - (centeredRelativeIndex θ : ℝ) * relativeAnglePeriod

theorem relativeAngle_int_rebase (α β : ℝ) (k : ℤ) :
    (β + (k : ℝ) * (2 * Real.pi / 3)) -
        (α + (k : ℝ) * Real.pi) =
      (β - α) - (k : ℝ) * relativeAnglePeriod := by
  unfold relativeAnglePeriod
  ring

theorem centeredRelativeAngle_placed_carriers
    (α β : ℝ) (tS tE : Point) :
    ∃ tS' tE' : Point,
      ((segmentHullAt
        (α + (centeredRelativeIndex (β - α) : ℝ) * Real.pi)).translate
          tS').carrier =
        ((segmentHullAt α).translate tS).carrier ∧
      (((equilateralWalk.rotate
        (β + (centeredRelativeIndex (β - α) : ℝ) *
          (2 * Real.pi / 3))).toFiniteHull.translate tE').carrier =
        (((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier)) ∧
      (β + (centeredRelativeIndex (β - α) : ℝ) *
          (2 * Real.pi / 3)) -
          (α + (centeredRelativeIndex (β - α) : ℝ) * Real.pi) =
        centeredRelativeAngle (β - α) := by
  let k : ℤ := centeredRelativeIndex (β - α)
  have hS := segmentHullAt_int_pi_translationEquivalent α k
  have hE := equilateral_int_thirdTurn_translationEquivalent β k
  obtain ⟨tS', htS'⟩ := hS.target_vadd tS
  obtain ⟨tE', htE'⟩ := hE.target_vadd tE
  refine ⟨tS', tE', ?_, ?_, ?_⟩
  · simpa only [FiniteHull.carrier_translate] using htS'
  · simpa only [FiniteHull.carrier_translate] using htE'
  · rw [relativeAngle_int_rebase]
    unfold centeredRelativeAngle
    rfl

theorem centeredRelativeAngle_mem (θ : ℝ) :
    centeredRelativeAngle θ ∈
      Set.Ico (-Real.pi / 6) (Real.pi / 6) := by
  let p : ℝ := relativeAnglePeriod
  let x : ℝ := θ / p + 1 / 2
  let k : ℤ := ⌊x⌋
  have hp : 0 < p := by
    simpa [p] using relativeAnglePeriod_pos
  have hfloor : (k : ℝ) ≤ x := by
    dsimp [k]
    exact Int.floor_le x
  have hceil : x < (k : ℝ) + 1 := by
    dsimp [k]
    exact Int.lt_floor_add_one x
  have hmul_lower : (k : ℝ) * p ≤ x * p :=
    mul_le_mul_of_nonneg_right hfloor hp.le
  have hmul_upper : x * p < ((k : ℝ) + 1) * p :=
    mul_lt_mul_of_pos_right hceil hp
  have hdiv : θ / p * p = θ := div_mul_cancel₀ θ hp.ne'
  have hxmul : (θ / p + 1 / 2) * p = θ + p / 2 := by
    rw [add_mul, hdiv]
    ring
  have hkmul : ((k : ℝ) + 1) * p = (k : ℝ) * p + p := by
    ring
  dsimp [x] at hmul_lower hmul_upper
  rw [hxmul] at hmul_lower hmul_upper
  rw [hkmul] at hmul_upper
  change
    -Real.pi / 6 ≤
        θ - (centeredRelativeIndex θ : ℝ) * relativeAnglePeriod ∧
      θ - (centeredRelativeIndex θ : ℝ) * relativeAnglePeriod <
        Real.pi / 6
  change
    -Real.pi / 6 ≤ θ - (k : ℝ) * p ∧
      θ - (k : ℝ) * p < Real.pi / 6
  constructor
  ·
    dsimp [p, relativeAnglePeriod] at hp hmul_lower ⊢
    linarith
  ·
    dsimp [p, relativeAnglePeriod] at hp hmul_upper ⊢
    linarith

theorem exists_centered_placed_carrier_rebase
    (α β : ℝ) (tS tE : Point) :
    ∃ α' β' : ℝ, ∃ tS' tE' : Point,
      ((segmentHullAt α').translate tS').carrier =
        ((segmentHullAt α).translate tS).carrier ∧
      (((equilateralWalk.rotate β').toFiniteHull.translate tE').carrier =
        (((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier)) ∧
      β' - α' ∈ Set.Ico (-Real.pi / 6) (Real.pi / 6) := by
  obtain ⟨tS', tE', hS, hE, hangle⟩ :=
    centeredRelativeAngle_placed_carriers α β tS tE
  refine
    ⟨α + (centeredRelativeIndex (β - α) : ℝ) * Real.pi,
      β + (centeredRelativeIndex (β - α) : ℝ) *
        (2 * Real.pi / 3), tS', tE', hS, hE, ?_⟩
  rw [hangle]
  exact centeredRelativeAngle_mem (β - α)

end

end MoserWorm

end


-- MoserWorm.Witness.UniversalAdmission
section

namespace MoserWorm

noncomputable section

open scoped Pointwise

namespace RigidPlacement

theorem apply_eq_shift_add_rot_of_direct {g : RigidPlacement}
    (hg : placementAllowed .direct g) (p : Point) :
    g p = g.shift + rot g.angle p := by
  rw [apply_eq]
  simp only [placementAllowed] at hg
  simp [linearPart, hg]

theorem image_boundaryWalk_carrier_of_direct {g : RigidPlacement}
    (hg : placementAllowed .direct g) (Q : BoundaryWalk) :
    g '' Q.toFiniteHull.carrier =
      ((Q.rotate g.angle).translate g.shift).toFiniteHull.carrier := by
  rw [BoundaryWalk.translate_toFiniteHull_carrier,
    BoundaryWalk.rotate_toFiniteHull_carrier]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [g.apply_eq_shift_add_rot_of_direct hg]
    exact ⟨rot g.angle q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, g.apply_eq_shift_add_rot_of_direct hg r⟩

end RigidPlacement

namespace BoundaryWalk

theorem rotate_rotate_toFiniteHull_carrier (Q : BoundaryWalk) (α β : ℝ) :
    ((Q.rotate α).rotate β).toFiniteHull.carrier =
      (Q.rotate (β + α)).toFiniteHull.carrier := by
  rw [rotate_toFiniteHull_carrier, rotate_toFiniteHull_carrier,
    rotate_toFiniteHull_carrier, Set.image_image]
  congr 1
  funext p
  exact (rot_add_apply β α p).symm

theorem translate_toFiniteHull_carrier_eq_finiteHull_translate
    (Q : BoundaryWalk) (t : Point) :
    (Q.translate t).toFiniteHull.carrier =
      (Q.toFiniteHull.translate t).carrier := by
  rw [translate_toFiniteHull_carrier, FiniteHull.carrier_translate]

end BoundaryWalk

def segmentPolyline : Polyline 1 where
  vertex := ![0, unitVec 0]

@[simp] theorem segmentPolyline_edgeLengthSum :
    segmentPolyline.edgeLengthSum = 1 := by
  simp [Polyline.edgeLengthSum, Polyline.edge, segmentPolyline]

theorem segmentPolyline_toFiniteHull_carrier :
    segmentPolyline.toFiniteHull.carrier = segmentHull.carrier := by
  unfold FiniteHull.carrier
  congr 1
  ext p
  simp [Polyline.toFiniteHull, segmentPolyline, segmentHull, or_comm]

def segmentUnitPolyline : UnitPolyline where
  n := 1
  path := segmentPolyline
  length_le_one := segmentPolyline_edgeLengthSum.le

private abbrev segmentCarrierWalk : BoundaryWalk where
  n := 1
  vertex := ![0, unitVec 0]

private theorem segmentCarrierWalk_toFiniteHull_carrier :
    segmentCarrierWalk.toFiniteHull.carrier = segmentHull.carrier := by
  unfold FiniteHull.carrier
  congr 1
  ext p
  simp [BoundaryWalk.toFiniteHull, segmentCarrierWalk, segmentHull, or_comm]

private theorem segmentCarrierWalk_rotate_translate_carrier
    (θ : ℝ) (t : Point) :
    (((segmentCarrierWalk.rotate θ).translate t).toFiniteHull.carrier) =
      ((segmentHullAt θ).translate t).carrier := by
  rw [BoundaryWalk.translate_toFiniteHull_carrier,
    FiniteHull.carrier_translate]
  congr 1
  unfold FiniteHull.carrier
  congr 1
  ext p
  simp [BoundaryWalk.toFiniteHull, BoundaryWalk.rotate, segmentCarrierWalk,
    segmentHullAt, or_comm, eq_comm]

namespace RigidPlacement

theorem image_segmentHull_carrier_of_direct {g : RigidPlacement}
    (hg : placementAllowed .direct g) :
    g '' segmentHull.carrier =
      ((segmentHullAt g.angle).translate g.shift).carrier := by
  rw [← segmentCarrierWalk_toFiniteHull_carrier,
    g.image_boundaryWalk_carrier_of_direct hg,
    segmentCarrierWalk_rotate_translate_carrier]

theorem reflectX_image_segmentHull_carrier :
    reflectX '' segmentHull.carrier = segmentHull.carrier := by
  rw [← segmentCarrierWalk_toFiniteHull_carrier,
    ← BoundaryWalk.reflectX_toFiniteHull_carrier]
  unfold FiniteHull.carrier
  congr 1
  ext p
  simp [BoundaryWalk.toFiniteHull, BoundaryWalk.reflectX,
    segmentCarrierWalk, or_comm, eq_comm]

theorem image_segmentHull_carrier (g : RigidPlacement) :
    g '' segmentHull.carrier =
      ((segmentHullAt g.angle).translate g.shift).carrier := by
  cases hm : g.mirror
  · exact g.image_segmentHull_carrier_of_direct (by simpa [placementAllowed])
  · let d := RigidPlacement.direct g.angle g.shift
    calc
      g '' segmentHull.carrier =
          d '' (reflectX '' segmentHull.carrier) := by
        rw [Set.image_image]
        congr 1
        funext p
        simp [d, apply_eq, linearPart, hm]; rfl
      _ = d '' segmentHull.carrier := by
        rw [reflectX_image_segmentHull_carrier]
      _ = ((segmentHullAt g.angle).translate g.shift).carrier := by
        exact d.image_segmentHull_carrier_of_direct (by simp [d])

theorem image_equilateral_carrier (g : RigidPlacement) :
    g '' equilateralWalk.toFiniteHull.carrier =
      (((equilateralWalk.rotate
          (if g.mirror then g.angle - Real.pi / 3 else g.angle)).translate
        g.shift).toFiniteHull.carrier) := by
  cases hm : g.mirror
  · simpa [hm] using
      g.image_boundaryWalk_carrier_of_direct
        (Q := equilateralWalk) (by simp [placementAllowed, hm])
  · let d := RigidPlacement.direct g.angle g.shift
    have hreflect :
        reflectX '' equilateralWalk.toFiniteHull.carrier =
          (equilateralWalk.rotate (-(Real.pi / 3))).toFiniteHull.carrier := by
      have hrotate0 :
          (equilateralWalk.rotate 0).toFiniteHull.carrier =
            equilateralWalk.toFiniteHull.carrier := by
        rw [BoundaryWalk.rotate_toFiniteHull_carrier]
        simp [rot_apply]
      have h := reflectX_image_equilateral_carrier (0 : ℝ)
      rw [hrotate0] at h
      simpa only [neg_zero, zero_sub] using h
    calc
      g '' equilateralWalk.toFiniteHull.carrier =
          d '' (reflectX '' equilateralWalk.toFiniteHull.carrier) := by
        rw [Set.image_image]
        congr 1
        funext p
        simp [d, apply_eq, linearPart, hm]; rfl
      _ = d '' (equilateralWalk.rotate (-(Real.pi / 3))).toFiniteHull.carrier := by
        rw [hreflect]
      _ = (((equilateralWalk.rotate (-(Real.pi / 3))).rotate g.angle).translate
          g.shift).toFiniteHull.carrier := by
        exact d.image_boundaryWalk_carrier_of_direct (by simp [d])
          (equilateralWalk.rotate (-(Real.pi / 3)))
      _ = (((equilateralWalk.rotate (g.angle - Real.pi / 3)).translate
          g.shift).toFiniteHull.carrier) := by
        rw [BoundaryWalk.translate_toFiniteHull_carrier,
          BoundaryWalk.translate_toFiniteHull_carrier,
          BoundaryWalk.rotate_rotate_toFiniteHull_carrier]
        congr 2

theorem image_oneCap_carrier (g : RigidPlacement) (β : ℝ) :
    g '' (oneCapWalk β).toFiniteHull.carrier =
      (((oneCapWalk β).rotate
          (if g.mirror then g.angle + Real.pi else g.angle)).translate
        (if g.mirror then
          g.shift + rot g.angle ((oneCapWalk β).vertex 1)
        else g.shift)).toFiniteHull.carrier := by
  cases hm : g.mirror
  · simpa [hm] using
      g.image_boundaryWalk_carrier_of_direct
        (Q := oneCapWalk β) (by simp [placementAllowed, hm])
  · let q := (oneCapWalk β).vertex 1
    let d := RigidPlacement.direct g.angle g.shift
    let k := RigidPlacement.direct Real.pi q
    have hd : placementAllowed .direct d := by simp [d]
    have hk : placementAllowed .direct k := by simp [k]
    have hdk : placementAllowed .direct (d.compose k) := hd.compose hk
    have hkimage :
        k '' (oneCapWalk β).toFiniteHull.carrier =
          (((oneCapWalk β).rotate Real.pi).translate q).toFiniteHull.carrier :=
      k.image_boundaryWalk_carrier_of_direct hk (oneCapWalk β)
    calc
      g '' (oneCapWalk β).toFiniteHull.carrier =
          d '' (reflectX '' (oneCapWalk β).toFiniteHull.carrier) := by
        rw [Set.image_image]
        congr 1
        funext p
        simp [d, apply_eq, linearPart, hm]
        rfl
      _ = d '' (((oneCapWalk β).rotate Real.pi).translate q).toFiniteHull.carrier := by
        rw [reflectX_image_oneCap_carrier_eq_direct]
      _ = d '' (k '' (oneCapWalk β).toFiniteHull.carrier) := by
        rw [hkimage]
      _ = d.compose k '' (oneCapWalk β).toFiniteHull.carrier := by
        rw [Set.image_image]
        congr 1
        funext p
        exact (d.compose_apply k p).symm
      _ = (((oneCapWalk β).rotate (g.angle + Real.pi)).translate
          (g.shift + rot g.angle ((oneCapWalk β).vertex 1))).toFiniteHull.carrier := by
        simpa only [d, k, q, RigidPlacement.compose, RigidPlacement.direct, RigidPlacement.linearPart,
          RigidPlacement.linearPart_direct, Bool.xor_false, Bool.false_eq_true, if_false] using
          (d.compose k).image_boundaryWalk_carrier_of_direct hdk (oneCapWalk β)

end RigidPlacement

def equilateralPolyline : Polyline 2 where
  vertex := equilateralWalk.vertex

@[simp] theorem equilateralPolyline_edge_zero :
    equilateralPolyline.edge 0 = (1 / 2 : ℝ) • unitVec 0 := by
  change equilateralWalk.vertex 1 - equilateralWalk.vertex 0 = _
  rw [equilateralWalk_vertex_zero, equilateralWalk_vertex_one_eq_unitVec]
  simp [point]

@[simp] theorem equilateralPolyline_edge_one :
    equilateralPolyline.edge 1 =
      (1 / 2 : ℝ) • unitVec (2 * Real.pi / 3) := by
  change point (1 / 4) (Real.sqrt 3 / 4) - point (1 / 2) 0 = _
  have htwo : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by
    ring
  rw [htwo]
  apply Complex.ext <;>
    norm_num [point, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]; ring

@[simp] theorem equilateralPolyline_edgeLengthSum :
    equilateralPolyline.edgeLengthSum = 1 := by
  rw [Polyline.edgeLengthSum, Fin.sum_univ_two]
  norm_num

theorem equilateralPolyline_toFiniteHull_carrier :
    equilateralPolyline.toFiniteHull.carrier =
      equilateralWalk.toFiniteHull.carrier := by
  rfl

def equilateralUnitPolyline : UnitPolyline where
  n := 2
  path := equilateralPolyline
  length_le_one := equilateralPolyline_edgeLengthSum.le

def oneCapPolyline (β : ℝ) : Polyline 3 where
  vertex := oneCapPathVertex β

@[simp] theorem oneCapPolyline_edgeLengthSum (β : ℝ) :
    (oneCapPolyline β).edgeLengthSum = 1 := by
  change ∑ i : Fin 3, ‖oneCapPathStep β i‖ = 1
  exact oneCapPath_length β

theorem oneCapPolyline_toFiniteHull_carrier (β : ℝ) :
    (oneCapPolyline β).toFiniteHull.carrier =
      (oneCapWalk β).toFiniteHull.carrier := by
  change (oneCapPathHull β).carrier =
    (oneCapWalk β).toFiniteHull.carrier
  exact oneCapPathHull_carrier_eq β

def oneCapUnitPolyline (β : ℝ) : UnitPolyline where
  n := 3
  path := oneCapPolyline β
  length_le_one := (oneCapPolyline_edgeLengthSum β).le

namespace PlacesEveryUnitPolyline

theorem places_segmentHull {C : ConvexCover} {mode : MotionMode}
    (hC : PlacesEveryUnitPolyline C mode) :
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧ g '' segmentHull.carrier ⊆ C.carrier := by
  obtain ⟨g, hg, hseg⟩ := hC.placed_hull_subset segmentUnitPolyline
  refine ⟨g, hg, ?_⟩
  rwa [segmentUnitPolyline, segmentPolyline_toFiniteHull_carrier] at hseg

theorem places_equilateral {C : ConvexCover} {mode : MotionMode}
    (hC : PlacesEveryUnitPolyline C mode) :
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧
        g '' equilateralWalk.toFiniteHull.carrier ⊆ C.carrier := by
  obtain ⟨g, hg, heq⟩ := hC.placed_hull_subset equilateralUnitPolyline
  refine ⟨g, hg, ?_⟩
  rwa [equilateralUnitPolyline,
    equilateralPolyline_toFiniteHull_carrier] at heq

theorem places_oneCap {C : ConvexCover} {mode : MotionMode}
    (hC : PlacesEveryUnitPolyline C mode) (β : ℝ) :
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧
        g '' (oneCapWalk β).toFiniteHull.carrier ⊆ C.carrier := by
  obtain ⟨g, hg, hcap⟩ := hC.placed_hull_subset (oneCapUnitPolyline β)
  refine ⟨g, hg, ?_⟩
  rwa [oneCapUnitPolyline, oneCapPolyline_toFiniteHull_carrier] at hcap

theorem exists_placed_oneCap_of_reflectionAllowed {C : ConvexCover}
    (hC : PlacesEveryUnitPolyline C .reflectionAllowed) (β : ℝ) :
    ∃ φ : ℝ, ∃ t : Point,
      ((((oneCapWalk β).rotate φ).translate t).toFiniteHull.carrier ⊆
        C.carrier) := by
  obtain ⟨g, -, hcap⟩ := hC.places_oneCap β
  refine ⟨if g.mirror then g.angle + Real.pi else g.angle,
    if g.mirror then
      g.shift + rot g.angle ((oneCapWalk β).vertex 1)
    else g.shift, ?_⟩
  rwa [← g.image_oneCap_carrier β]

theorem exists_placed_segment_equilateral {C : ConvexCover}
    (hC : PlacesEveryUnitPolyline C .reflectionAllowed) :
    ∃ α β : ℝ, ∃ tS tE : Point,
      ((segmentHullAt α).translate tS).carrier ⊆ C.carrier ∧
      (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier ⊆
        C.carrier) := by
  obtain ⟨gS, -, hS⟩ := hC.places_segmentHull
  obtain ⟨gE, -, hE⟩ := hC.places_equilateral
  refine ⟨gS.angle,
    if gE.mirror then gE.angle - Real.pi / 3 else gE.angle,
    gS.shift, gE.shift, ?_, ?_⟩
  · rwa [← gS.image_segmentHull_carrier]
  · rwa [← gE.image_equilateral_carrier]

theorem exists_centered_placed_segment_equilateral {C : ConvexCover}
    (hC : PlacesEveryUnitPolyline C .reflectionAllowed) :
    ∃ α β : ℝ, ∃ tS tE : Point,
      ((segmentHullAt α).translate tS).carrier ⊆ C.carrier ∧
      (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier ⊆
        C.carrier) ∧
      β - α ∈ Set.Ico (-Real.pi / 6) (Real.pi / 6) := by
  obtain ⟨α, β, tS, tE, hS, hE⟩ :=
    hC.exists_placed_segment_equilateral
  obtain ⟨α', β', tS', tE', hSeq, hEeq, hangle⟩ :=
    exists_centered_placed_carrier_rebase α β tS tE
  refine ⟨α', β', tS', tE', ?_, ?_, hangle⟩
  · rw [hSeq]
    exact hS
  · rw [BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate,
      hEeq, ← BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
    exact hE

end PlacesEveryUnitPolyline

namespace UniversalForUnitWorms

theorem places_segmentHull {C : ConvexCover} {mode : MotionMode}
    (hC : UniversalForUnitWorms C mode) :
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧ g '' segmentHull.carrier ⊆ C.carrier :=
  hC.placesEveryUnitPolyline.places_segmentHull

theorem places_equilateral {C : ConvexCover} {mode : MotionMode}
    (hC : UniversalForUnitWorms C mode) :
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧
        g '' equilateralWalk.toFiniteHull.carrier ⊆ C.carrier :=
  hC.placesEveryUnitPolyline.places_equilateral

theorem places_oneCap {C : ConvexCover} {mode : MotionMode}
    (hC : UniversalForUnitWorms C mode) (β : ℝ) :
    ∃ g : RigidPlacement,
      placementAllowed mode g ∧
        g '' (oneCapWalk β).toFiniteHull.carrier ⊆ C.carrier :=
  hC.placesEveryUnitPolyline.places_oneCap β

theorem exists_placed_oneCap_of_reflectionAllowed {C : ConvexCover}
    (hC : UniversalForUnitWorms C .reflectionAllowed) (β : ℝ) :
    ∃ φ : ℝ, ∃ t : Point,
      ((((oneCapWalk β).rotate φ).translate t).toFiniteHull.carrier ⊆
        C.carrier) := by
  obtain ⟨g, -, hcap⟩ := hC.places_oneCap β
  refine ⟨if g.mirror then g.angle + Real.pi else g.angle,
    if g.mirror then
      g.shift + rot g.angle ((oneCapWalk β).vertex 1)
    else g.shift, ?_⟩
  rwa [← g.image_oneCap_carrier β]

theorem exists_placed_segment_equilateral {C : ConvexCover}
    (hC : UniversalForUnitWorms C .reflectionAllowed) :
    ∃ α β : ℝ, ∃ tS tE : Point,
      ((segmentHullAt α).translate tS).carrier ⊆ C.carrier ∧
      (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier ⊆
        C.carrier) :=
  hC.placesEveryUnitPolyline.exists_placed_segment_equilateral

theorem exists_centered_placed_segment_equilateral {C : ConvexCover}
    (hC : UniversalForUnitWorms C .reflectionAllowed) :
    ∃ α β : ℝ, ∃ tS tE : Point,
      ((segmentHullAt α).translate tS).carrier ⊆ C.carrier ∧
      (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier ⊆
        C.carrier) ∧
      β - α ∈ Set.Ico (-Real.pi / 6) (Real.pi / 6) :=
  hC.placesEveryUnitPolyline.exists_centered_placed_segment_equilateral

end UniversalForUnitWorms

end

end MoserWorm

end


-- MoserWorm.Witness.CoverNormalization
section

namespace MoserWorm

noncomputable section

namespace RigidPlacement

theorem compose_image (g h : RigidPlacement) (s : Set Point) :
    g.compose h '' s = g '' (h '' s) := by
  rw [Set.image_image]
  congr 1
  funext p
  exact g.compose_apply h p

end RigidPlacement

namespace PlacesEveryUnitPolyline

theorem exists_common_normalized_segment_equilateral
    {C : ConvexCover} (hC : PlacesEveryUnitPolyline C .reflectionAllowed)
    (α β : ℝ) (tS tE : Point)
    (hS : ((segmentHullAt α).translate tS).carrier ⊆ C.carrier)
    (hE : (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier ⊆
      C.carrier)) :
    ∃ C' : ConvexCover, ∃ tE' : Point,
      PlacesEveryUnitPolyline C' .reflectionAllowed ∧
      coverArea C' = coverArea C ∧
      segmentHull.carrier ⊆ C'.carrier ∧
      (((equilateralWalk.rotate (β - α)).toFiniteHull.translate tE').carrier ⊆
        C'.carrier) := by
  let gS := RigidPlacement.direct α tS
  let gE := RigidPlacement.direct β tE
  let h := gS.inverse
  let gRel := h.compose gE
  have hgS : placementAllowed .direct gS := by simp [gS]
  have hgE : placementAllowed .direct gE := by simp [gE]
  have hh : placementAllowed .reflectionAllowed h := by simp
  have hgRel : placementAllowed .direct gRel := by
    exact hgS.inverse.compose hgE
  have hangle : gRel.angle = β - α := by
    change -α + β = β - α
    ring
  refine ⟨C.transform h, gRel.shift, hC.transform h hh,
    C.coverArea_transform h, ?_, ?_⟩
  · have himage :
        h '' ((segmentHullAt α).translate tS).carrier ⊆ h '' C.carrier :=
      Set.image_mono hS
    have hSimage :
        gS '' segmentHull.carrier =
          ((segmentHullAt α).translate tS).carrier := by
      exact gS.image_segmentHull_carrier_of_direct hgS
    rw [← hSimage] at himage
    change gS.inverse '' (gS '' segmentHull.carrier) ⊆
      gS.inverse '' C.carrier at himage
    rw [gS.inverse_image_image] at himage
    exact himage
  · have himage :
        h '' (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier) ⊆
          h '' C.carrier :=
      Set.image_mono hE
    have hEimage :
        gE '' equilateralWalk.toFiniteHull.carrier =
          ((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier := by
      exact gE.image_boundaryWalk_carrier_of_direct hgE equilateralWalk
    rw [← hEimage] at himage
    rw [← h.compose_image gE] at himage
    rw [gRel.image_boundaryWalk_carrier_of_direct hgRel, hangle] at himage
    rw [BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
      at himage
    exact himage

theorem exists_whole_reflected_segment_equilateral
    {C : ConvexCover} (hC : PlacesEveryUnitPolyline C .reflectionAllowed)
    (α β : ℝ) (tS tE : Point)
    (hS : ((segmentHullAt α).translate tS).carrier ⊆ C.carrier)
    (hE : ((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier ⊆
      C.carrier) :
    ∃ C' : ConvexCover, ∃ tS' tE' : Point,
      PlacesEveryUnitPolyline C' .reflectionAllowed ∧
      coverArea C' = coverArea C ∧
      ((segmentHullAt (-α)).translate tS').carrier ⊆ C'.carrier ∧
      ((equilateralWalk.rotate (-β - Real.pi / 3)).toFiniteHull.translate tE').carrier ⊆
        C'.carrier := by
  let j := RigidPlacement.reflected 0 0
  let gS := RigidPlacement.direct α tS
  let gE := RigidPlacement.direct β tE
  let rS := j.compose gS
  let rE := j.compose gE
  have hj : placementAllowed .reflectionAllowed j := by simp
  have hgS : placementAllowed .direct gS := by simp [gS]
  have hgE : placementAllowed .direct gE := by simp [gE]
  have hrSangle : rS.angle = -α := by
    dsimp [rS, j, gS, RigidPlacement.compose, RigidPlacement.reflected,
      RigidPlacement.direct]
    ring
  have hrEangle :
      (if rE.mirror then rE.angle - Real.pi / 3 else rE.angle) =
        -β - Real.pi / 3 := by
    dsimp [rE, j, gE, RigidPlacement.compose, RigidPlacement.reflected,
      RigidPlacement.direct]
    ring
  refine ⟨C.transform j, rS.shift, rE.shift, hC.transform j hj,
    C.coverArea_transform j, ?_, ?_⟩
  · have himage :
        j '' ((segmentHullAt α).translate tS).carrier ⊆ j '' C.carrier :=
      Set.image_mono hS
    have hSimage :
        gS '' segmentHull.carrier =
          ((segmentHullAt α).translate tS).carrier := by
      exact gS.image_segmentHull_carrier_of_direct hgS
    rw [← hSimage, ← j.compose_image gS,
      rS.image_segmentHull_carrier, hrSangle] at himage
    exact himage
  · have himage :
        j '' ((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier ⊆
          j '' C.carrier := Set.image_mono hE
    have hEimage :
        gE '' equilateralWalk.toFiniteHull.carrier =
          ((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier := by
      rw [← BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
      exact gE.image_boundaryWalk_carrier_of_direct hgE equilateralWalk
    rw [← hEimage, ← j.compose_image gE,
      rE.image_equilateral_carrier, hrEangle,
      BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
      at himage
    exact himage

theorem exists_nonnegative_normalized_segment_equilateral
    {C : ConvexCover} (hC : PlacesEveryUnitPolyline C .reflectionAllowed) :
    ∃ C' : ConvexCover, ∃ θ : ℝ, ∃ tE : Point,
      PlacesEveryUnitPolyline C' .reflectionAllowed ∧
      coverArea C' = coverArea C ∧
      0 ≤ θ ∧ θ ≤ Real.pi / 6 ∧
      segmentHull.carrier ⊆ C'.carrier ∧
      ((equilateralWalk.rotate θ).toFiniteHull.translate tE).carrier ⊆
        C'.carrier := by
  obtain ⟨α, β, tS, tE, hS, hE, hangle⟩ :=
    hC.exists_centered_placed_segment_equilateral
  by_cases hnonneg : 0 ≤ β - α
  · obtain ⟨C', tE', hC', harea, hS', hE'⟩ :=
      hC.exists_common_normalized_segment_equilateral α β tS tE hS hE
    exact ⟨C', β - α, tE', hC', harea, hnonneg, hangle.2.le, hS', hE'⟩
  · have hneg : β - α < 0 := lt_of_not_ge hnonneg
    obtain ⟨CR, tSR, tER, hCR, hareaR, hSR, hER⟩ :=
      hC.exists_whole_reflected_segment_equilateral α β tS tE hS <| by
        rw [← BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
        exact hE
    let αR : ℝ := -α
    let βR : ℝ := -β - Real.pi / 3
    have hSsym := segmentHullAt_int_pi_translationEquivalent αR (-1)
    have hEsym := equilateral_int_thirdTurn_translationEquivalent βR (-1)
    obtain ⟨tS', htS'⟩ := hSsym.target_vadd tSR
    obtain ⟨tE', htE'⟩ := hEsym.target_vadd tER
    have hSrebase :
        ((segmentHullAt (αR - Real.pi)).translate tS').carrier =
          ((segmentHullAt αR).translate tSR).carrier := by
      simpa [FiniteHull.carrier_translate, sub_eq_add_neg] using htS'
    have hErebase :
        ((equilateralWalk.rotate (βR - 2 * Real.pi / 3)).toFiniteHull.translate
            tE').carrier =
          ((equilateralWalk.rotate βR).toFiniteHull.translate tER).carrier := by
      simpa [FiniteHull.carrier_translate, sub_eq_add_neg] using htE'
    have hSR' :
        ((segmentHullAt (αR - Real.pi)).translate tS').carrier ⊆ CR.carrier := by
      rw [hSrebase]
      exact hSR
    have hER' :
        ((equilateralWalk.rotate (βR - 2 * Real.pi / 3)).toFiniteHull.translate
            tE').carrier ⊆ CR.carrier := by
      rw [hErebase]
      exact hER
    obtain ⟨C', tE'', hC', harea', hS', hE'⟩ :=
      hCR.exists_common_normalized_segment_equilateral
        (αR - Real.pi) (βR - 2 * Real.pi / 3) tS' tE' hSR' <| by
          rw [BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
          exact hER'
    have hrel :
        (βR - 2 * Real.pi / 3) - (αR - Real.pi) = -(β - α) := by
      dsimp [αR, βR]
      ring
    rw [hrel] at hE'
    refine ⟨C', -(β - α), tE'', hC', harea'.trans hareaR,
      neg_nonneg.2 hneg.le, ?_, hS', hE'⟩
    linarith [hangle.1]

end PlacesEveryUnitPolyline

namespace UniversalForUnitWorms

theorem exists_common_normalized_segment_equilateral
    {C : ConvexCover} (hC : UniversalForUnitWorms C .reflectionAllowed)
    (α β : ℝ) (tS tE : Point)
    (hS : ((segmentHullAt α).translate tS).carrier ⊆ C.carrier)
    (hE : (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier ⊆
      C.carrier)) :
    ∃ C' : ConvexCover, ∃ tE' : Point,
      UniversalForUnitWorms C' .reflectionAllowed ∧
      coverArea C' = coverArea C ∧
      segmentHull.carrier ⊆ C'.carrier ∧
      (((equilateralWalk.rotate (β - α)).toFiniteHull.translate tE').carrier ⊆
        C'.carrier) := by
  let gS := RigidPlacement.direct α tS
  let gE := RigidPlacement.direct β tE
  let h := gS.inverse
  let gRel := h.compose gE
  have hgS : placementAllowed .direct gS := by simp [gS]
  have hgE : placementAllowed .direct gE := by simp [gE]
  have hh : placementAllowed .reflectionAllowed h := by simp
  have hgRel : placementAllowed .direct gRel := by
    exact hgS.inverse.compose hgE
  have hangle : gRel.angle = β - α := by
    change -α + β = β - α
    ring
  refine ⟨C.transform h, gRel.shift, hC.transform h hh,
    C.coverArea_transform h, ?_, ?_⟩
  · have himage :
        h '' ((segmentHullAt α).translate tS).carrier ⊆ h '' C.carrier :=
      Set.image_mono hS
    have hSimage :
        gS '' segmentHull.carrier =
          ((segmentHullAt α).translate tS).carrier := by
      exact gS.image_segmentHull_carrier_of_direct hgS
    rw [← hSimage] at himage
    change gS.inverse '' (gS '' segmentHull.carrier) ⊆
      gS.inverse '' C.carrier at himage
    rw [gS.inverse_image_image] at himage
    exact himage
  · have himage :
        h '' (((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier) ⊆
          h '' C.carrier :=
      Set.image_mono hE
    have hEimage :
        gE '' equilateralWalk.toFiniteHull.carrier =
          ((equilateralWalk.rotate β).translate tE).toFiniteHull.carrier := by
      exact gE.image_boundaryWalk_carrier_of_direct hgE equilateralWalk
    rw [← hEimage] at himage
    rw [← h.compose_image gE] at himage
    rw [gRel.image_boundaryWalk_carrier_of_direct hgRel, hangle] at himage
    rw [BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
      at himage
    exact himage

theorem exists_whole_reflected_segment_equilateral
    {C : ConvexCover} (hC : UniversalForUnitWorms C .reflectionAllowed)
    (α β : ℝ) (tS tE : Point)
    (hS : ((segmentHullAt α).translate tS).carrier ⊆ C.carrier)
    (hE : ((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier ⊆
      C.carrier) :
    ∃ C' : ConvexCover, ∃ tS' tE' : Point,
      UniversalForUnitWorms C' .reflectionAllowed ∧
      coverArea C' = coverArea C ∧
      ((segmentHullAt (-α)).translate tS').carrier ⊆ C'.carrier ∧
      ((equilateralWalk.rotate (-β - Real.pi / 3)).toFiniteHull.translate tE').carrier ⊆
        C'.carrier := by
  let j := RigidPlacement.reflected 0 0
  let gS := RigidPlacement.direct α tS
  let gE := RigidPlacement.direct β tE
  let rS := j.compose gS
  let rE := j.compose gE
  have hj : placementAllowed .reflectionAllowed j := by simp
  have hgS : placementAllowed .direct gS := by simp [gS]
  have hgE : placementAllowed .direct gE := by simp [gE]
  have hrSangle : rS.angle = -α := by
    dsimp [rS, j, gS, RigidPlacement.compose, RigidPlacement.reflected,
      RigidPlacement.direct]
    ring
  have hrEangle :
      (if rE.mirror then rE.angle - Real.pi / 3 else rE.angle) =
        -β - Real.pi / 3 := by
    dsimp [rE, j, gE, RigidPlacement.compose, RigidPlacement.reflected,
      RigidPlacement.direct]
    ring
  refine ⟨C.transform j, rS.shift, rE.shift, hC.transform j hj,
    C.coverArea_transform j, ?_, ?_⟩
  · have himage :
        j '' ((segmentHullAt α).translate tS).carrier ⊆ j '' C.carrier :=
      Set.image_mono hS
    have hSimage :
        gS '' segmentHull.carrier =
          ((segmentHullAt α).translate tS).carrier := by
      exact gS.image_segmentHull_carrier_of_direct hgS
    rw [← hSimage, ← j.compose_image gS,
      rS.image_segmentHull_carrier, hrSangle] at himage
    exact himage
  · have himage :
        j '' ((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier ⊆
          j '' C.carrier := Set.image_mono hE
    have hEimage :
        gE '' equilateralWalk.toFiniteHull.carrier =
          ((equilateralWalk.rotate β).toFiniteHull.translate tE).carrier := by
      rw [← BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
      exact gE.image_boundaryWalk_carrier_of_direct hgE equilateralWalk
    rw [← hEimage, ← j.compose_image gE,
      rE.image_equilateral_carrier, hrEangle,
      BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
      at himage
    exact himage

theorem exists_nonnegative_normalized_segment_equilateral
    {C : ConvexCover} (hC : UniversalForUnitWorms C .reflectionAllowed) :
    ∃ C' : ConvexCover, ∃ θ : ℝ, ∃ tE : Point,
      UniversalForUnitWorms C' .reflectionAllowed ∧
      coverArea C' = coverArea C ∧
      0 ≤ θ ∧ θ ≤ Real.pi / 6 ∧
      segmentHull.carrier ⊆ C'.carrier ∧
      ((equilateralWalk.rotate θ).toFiniteHull.translate tE).carrier ⊆
        C'.carrier := by
  obtain ⟨α, β, tS, tE, hS, hE, hangle⟩ :=
    hC.exists_centered_placed_segment_equilateral
  by_cases hnonneg : 0 ≤ β - α
  · obtain ⟨C', tE', hC', harea, hS', hE'⟩ :=
      hC.exists_common_normalized_segment_equilateral α β tS tE hS hE
    exact ⟨C', β - α, tE', hC', harea, hnonneg, hangle.2.le, hS', hE'⟩
  · have hneg : β - α < 0 := lt_of_not_ge hnonneg
    obtain ⟨CR, tSR, tER, hCR, hareaR, hSR, hER⟩ :=
      hC.exists_whole_reflected_segment_equilateral α β tS tE hS <| by
        rw [← BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
        exact hE
    let αR : ℝ := -α
    let βR : ℝ := -β - Real.pi / 3
    have hSsym := segmentHullAt_int_pi_translationEquivalent αR (-1)
    have hEsym := equilateral_int_thirdTurn_translationEquivalent βR (-1)
    obtain ⟨tS', htS'⟩ := hSsym.target_vadd tSR
    obtain ⟨tE', htE'⟩ := hEsym.target_vadd tER
    have hSrebase :
        ((segmentHullAt (αR - Real.pi)).translate tS').carrier =
          ((segmentHullAt αR).translate tSR).carrier := by
      simpa [FiniteHull.carrier_translate, sub_eq_add_neg] using htS'
    have hErebase :
        ((equilateralWalk.rotate (βR - 2 * Real.pi / 3)).toFiniteHull.translate
            tE').carrier =
          ((equilateralWalk.rotate βR).toFiniteHull.translate tER).carrier := by
      simpa [FiniteHull.carrier_translate, sub_eq_add_neg] using htE'
    have hSR' :
        ((segmentHullAt (αR - Real.pi)).translate tS').carrier ⊆ CR.carrier := by
      rw [hSrebase]
      exact hSR
    have hER' :
        ((equilateralWalk.rotate (βR - 2 * Real.pi / 3)).toFiniteHull.translate
            tE').carrier ⊆ CR.carrier := by
      rw [hErebase]
      exact hER
    obtain ⟨C', tE'', hC', harea', hS', hE'⟩ :=
      hCR.exists_common_normalized_segment_equilateral
        (αR - Real.pi) (βR - 2 * Real.pi / 3) tS' tE' hSR' <| by
          rw [BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
          exact hER'
    have hrel :
        (βR - 2 * Real.pi / 3) - (αR - Real.pi) = -(β - α) := by
      dsimp [αR, βR]
      ring
    rw [hrel] at hE'
    refine ⟨C', -(β - α), tE'', hC', harea'.trans hareaR,
      neg_nonneg.2 hneg.le, ?_, hS', hE'⟩
    linarith [hangle.1]

end UniversalForUnitWorms

end

end MoserWorm

end

/-! Arc-length and compactness transfer for the Moser convex worm-cover lower bound. -/


section
open EuclideanGeometry MeasureTheory TopologicalSpace Set
open scoped Topology Pointwise ENNReal BigOperators EuclideanGeometry

-- Normalization and finite-area boundedness adapted from Ian Qvist, OMA #2118.
namespace WormInball

private abbrev Time := Set.Icc (0 : ℝ) 1

private def point (x y : ℝ) : ℝ² := WithLp.toLp 2 ![x,y]

private lemma point_zero (x y : ℝ) : point x y 0 = x := rfl

private lemma point_one (x y : ℝ) : point x y 1 = y := rfl

private noncomputable def worm (t : Time) : ℝ² :=
  point (min t.val (1/2)) (max (t.val - 1/2) 0)

private lemma sum_coords (t : ℝ) : min t (1/2) + max (t - 1/2) 0 = t := by
  by_cases ht : t ≤ 1/2
  · rw [min_eq_left ht, max_eq_right (sub_nonpos.2 ht), add_zero]
  · rw [min_eq_right (le_of_not_ge ht), max_eq_left (sub_nonneg.2 (le_of_not_ge ht))]
    ring

private lemma worm_lipschitz : LipschitzWith 1 worm := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul]
  wlog hst : s.val ≤ t.val generalizing s t
  · rw [dist_comm (worm s),dist_comm s t]
    exact this t s (le_of_not_ge hst)
  have hm : min s.val (1/2) ≤ min t.val (1/2) := min_le_min_right _ hst
  have hM : max (s.val - 1/2) 0 ≤ max (t.val - 1/2) 0 :=
    max_le_max_right _ (sub_le_sub_right hst _)
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Subtype.dist_eq]
  simp only [worm, point_zero, point_one, Real.dist_eq, sq_abs]
  have hsum : min t.val (1/2) - min s.val (1/2) +
       (max (t.val - 1/2) 0 - max (s.val - 1/2) 0) = t.val - s.val := by
    linarith only [sum_coords s.val,sum_coords t.val]
  calc
    _ ≤ (min t.val (1/2) - min s.val (1/2) +
        (max (t.val - 1/2) 0 - max (s.val - 1/2) 0)) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hM)]
    _ = _ := by rw [hsum, ← neg_sub, neg_sq]

private noncomputable def vertices : Fin 3 → ℝ² := ![point 0 0,point (1/2) 0,point (1/2) (1/2)]

private lemma vertices_in_worm (i : Fin 3) : vertices i ∈ Set.range worm := by
  fin_cases i
  · refine ⟨⟨0,by constructor <;> norm_num⟩,?_⟩
    change point (min 0 (1/2)) (max (0-1/2) 0) = point 0 0
    norm_num [min_def,max_def]
  · refine ⟨⟨1/2,by constructor <;> norm_num⟩,?_⟩
    change point (min (1/2) (1/2)) (max ((1/2)-(1/2)) 0) = point (1/2) 0
    norm_num
  · refine ⟨⟨1,by constructor <;> norm_num⟩,?_⟩
    change point (min 1 (1/2)) (max (1-1/2) 0) = point (1/2) (1/2)
    norm_num [min_def,max_def]

private noncomputable def center : ℝ² := point (3/8) (1/8)

private lemma ball_in_convexHull : Metric.closedBall center (1/16) ⊆ convexHull ℝ (Set.range worm) := by
  intro z hz
  have hd : dist z center ≤ 1/16 := Metric.mem_closedBall.1 hz
  have hs : dist z center ^ 2 ≤ (1/16 : ℝ) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (by norm_num)).2 hd
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hs
  simp only [center, point_zero, point_one, Real.dist_eq, sq_abs] at hs
  have hxAbs : |z 0 - 3/8| ≤ 1/16 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1
    rw [sq_abs]
    nlinarith only [hs,sq_nonneg (z 1 - 1/8)]
  have hyAbs : |z 1 - 1/8| ≤ 1/16 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1
    rw [sq_abs]
    nlinarith only [hs,sq_nonneg (z 0 - 3/8)]
  rw [abs_le] at hxAbs hyAbs
  have hx : z 0 ≤ 1/2 := by linarith only [hxAbs.2]
  have hy : 0 ≤ z 1 := by linarith only [hyAbs.1]
  have hxy : z 1 ≤ z 0 := by linarith only [hyAbs.2,hxAbs.1]
  let w : Fin 3 → ℝ := ![1-2*z 0,2*(z 0-z 1),2*z 1]
  have hw (i : Fin 3) : 0 ≤ w i := by
    fin_cases i
    · change 0 ≤ 1-2*z 0
      linarith
    · exact mul_nonneg (by norm_num) (sub_nonneg.2 hxy)
    · exact mul_nonneg (by norm_num) hy
  have hwSum : ∑ i : Fin 3, w i = 1 := by
    rw [Fin.sum_univ_three]
    change 1-2*z 0 + 2*(z 0-z 1) + 2*z 1 = 1
    ring
  have hsum : (∑ i : Fin 3, w i • vertices i) = z := by
    rw [Fin.sum_univ_three]
    ext i
    fin_cases i
    · change (1-2*z 0)*0 + (2*(z 0-z 1))*(1/2) + (2*z 1)*(1/2) = z 0
      ring
    · change (1-2*z 0)*0 + (2*(z 0-z 1))*0 + (2*z 1)*(1/2) = z 1
      ring
  rw [← hsum]
  exact (convex_convexHull ℝ (Set.range worm)).sum_mem (fun i _ => hw i) hwSum
    (fun i _ => subset_convexHull ℝ _ (vertices_in_worm i))

private lemma translated_worm_cover {X : Set ℝ²} (hX : X ∈ MoserWorm.WormCovers) (p : ℝ²) :
    ((p + ·) ⁻¹' X) ∈ MoserWorm.WormCovers := by
  refine ⟨hX.1.preimage (continuous_const.add continuous_id).measurable, ?_⟩
  intro W hW
  obtain ⟨e,v,hdet,hSub⟩ := hX.2 W hW
  refine ⟨e,e p + v,hdet,?_⟩
  intro z hz
  obtain ⟨x,hx,rfl⟩ := hSub hz
  refine ⟨x-p,?_,?_⟩
  · change p + (x-p) ∈ X
    rwa [show p + (x-p) = x by abel]
  · change e (x-p) + (e p + v) = e x + v
    rw [map_sub]
    abel

theorem normalize :
    ∃ r : ℝ, 0 < r ∧ ∀ X : Set ℝ², X ∈ MoserWorm.WormCovers → Convex ℝ X →
      ∃ Y : Set ℝ², Y ∈ MoserWorm.WormCovers ∧ Convex ℝ Y ∧
        Metric.closedBall 0 r ⊆ Y ∧ volume Y = volume X := by
  refine ⟨1/16,by norm_num,?_⟩
  intro X hX hConv
  obtain ⟨e,v,_,hW⟩ := hX.2 (Set.range worm) ⟨worm,worm_lipschitz,rfl⟩
  have hConvImage : Convex ℝ ((fun x => e x + v) '' X) := by
    let L := e.toLinearEquiv.toLinearMap
    have h := (hConv.linear_image L).translate v
    rw [Set.image_image] at h
    have he : (fun x => v + L x) = (fun x => e x + v) := by
      ext x
      exact add_comm _ _
    rw [he] at h
    exact h
  have hC : Metric.closedBall center (1/16) ⊆ (fun x => e x + v) '' X :=
    ball_in_convexHull.trans (convexHull_min hW hConvImage)
  let p := e.symm (center-v)
  have hp : e p + v = center := by simp [p]
  have hBall : Metric.closedBall p (1/16) ⊆ X := by
    intro x hx
    have hDist : dist (e x + v) center = dist x p := by
      rw [← hp, dist_eq_norm, show e x + v - (e p + v) = e x - e p by abel, ← dist_eq_norm,
        e.isometry.dist_eq]
    obtain ⟨y,hy,heq⟩ := hC (Metric.mem_closedBall.2 (hDist.trans_le (Metric.mem_closedBall.1 hx)))
    have hEq : y = x := e.injective (add_right_cancel heq)
    exact hEq ▸ hy
  let Y : Set ℝ² := (p + ·) ⁻¹' X
  refine ⟨Y, translated_worm_cover hX p, hConv.translate_preimage_right p, ?_, ?_⟩
  · intro x hx
    apply hBall
    have hdist : dist (p+x) p = dist x 0 := by
      rw [dist_eq_norm,dist_zero_right,show p+x-p=x by abel]
    exact Metric.mem_closedBall.2 (hdist.trans_le (Metric.mem_closedBall.1 hx))
  · exact measure_preimage_vadd (volume : Measure ℝ²) p X

end WormInball

namespace WormBound

open EuclideanGeometry MeasureTheory
open scoped ENNReal

private lemma one_le_abs_cast_sub {i j : ℕ} (h : i ≠ j) :
    1 ≤ |(i : ℝ) - (j : ℝ)| := by
  rcases lt_or_gt_of_ne h with hij | hji
  · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hij
    exact (show 1 ≤ -((i : ℝ) - j) by linarith).trans (neg_le_abs _)
  · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hji
    exact (show 1 ≤ (i : ℝ) - j by linarith).trans (le_abs_self _)

/-- Convex sets containing an origin-centered ball and with bounded area have a common radius. -/
theorem exists_radius (r : ℝ) (hr : 0 < r) (M : ℝ≥0∞) (hM : M < ⊤) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ Y : Set ℝ², Convex ℝ Y → Metric.closedBall 0 r ⊆ Y →
      volume Y ≤ M → Y ⊆ Metric.closedBall 0 R := by
  let v : ℝ≥0∞ := volume (Metric.ball (0 : ℝ²) (r / 2))
  have hv : 0 < v := Metric.measure_ball_pos volume _ (half_pos hr)
  obtain ⟨N, hNpos, hN⟩ := ENNReal.exists_nat_pos_mul_gt hv.ne' hM.ne
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  let D : ℝ := 2 * N
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * r, mul_nonneg hD.le hr.le, ?_⟩
  intro Y hY hball hvol y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hFar
  let t (i : Fin N) : ℝ := (i.val : ℝ) / D
  let center (i : Fin N) : ℝ² := t i • y
  have ht0 (i : Fin N) : 0 ≤ t i := div_nonneg (Nat.cast_nonneg _) hD.le
  have htHalf (i : Fin N) : t i ≤ 1 / 2 := by
    change (i.val : ℝ) / D ≤ 1 / 2
    apply (div_le_iff₀ hD).2
    have h : (i.val : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    dsimp [D]
    linarith
  have hContained (i : Fin N) : Metric.ball (center i) (r / 2) ⊆ Y := by
    intro z hz
    let d := 1 - t i
    have hHalf : (1 / 2 : ℝ) ≤ d := by dsimp [d]; linarith [htHalf i]
    have hd : 0 < d := by linarith
    let w := d⁻¹ • (z - center i)
    have hw : w ∈ Metric.closedBall (0 : ℝ²) r := by
      have hz' : ‖z - center i‖ < r / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖d⁻¹ • (z - center i)‖ ≤ r
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
      apply (inv_mul_le_iff₀ hd).2
      have hle := mul_le_mul_of_nonneg_right hHalf hr.le
      exact hz'.le.trans (by linarith)
    have hsum : d + t i = 1 := sub_add_cancel _ _
    have hmem := hY (hball hw) hy hd.le (ht0 i) hsum
    have hwc : d • w = z - center i := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
    change d • w + center i ∈ Y at hmem
    rwa [hwc, sub_add_cancel] at hmem
  have hDisjoint : Pairwise (fun i j : Fin N =>
      Disjoint (Metric.ball (center i) (r / 2)) (Metric.ball (center j) (r / 2))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    rw [add_halves]
    have hi : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hgap := one_le_abs_cast_sub hi
    change r ≤ dist (t i • y) (t j • y)
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    dsimp [t]
    rw [← sub_div, abs_div, abs_of_pos hD, div_mul_eq_mul_div]
    apply (le_div_iff₀ hD).2
    calc
      r * D ≤ ‖y‖ := by simpa only [mul_comm] using hFar.le
      _ ≤ |(i.val : ℝ) - (j.val : ℝ)| * ‖y‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap (norm_nonneg y)
  have hSameVolume (i : Fin N) : volume (Metric.ball (center i) (r / 2)) = v := by
    simp [v, EuclideanSpace.volume_ball]
  have hVolume : volume (⋃ i : Fin N, Metric.ball (center i) (r / 2)) =
      (N : ℝ≥0∞) * v := by
    rw [measure_iUnion hDisjoint (fun _ => measurableSet_ball)]
    simp only [hSameVolume, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hUpper := (measure_mono (Set.iUnion_subset hContained)).trans hvol
  rw [hVolume] at hUpper
  exact (not_lt_of_ge hUpper) hN

/-- The closure of a convex set has the same area. -/
theorem volume_closure {Y : Set ℝ²} (hY : Convex ℝ Y) :
    volume (closure Y) = volume Y := by
  apply le_antisymm _ (measure_mono subset_closure)
  have hsub : closure Y ⊆ Y ∪ frontier Y := by
    intro x hx
    by_cases hy : x ∈ Y
    · exact Or.inl hy
    · exact Or.inr ⟨hx, fun hi => hy (interior_subset hi)⟩
  calc
    volume (closure Y) ≤ volume (Y ∪ frontier Y) := measure_mono hsub
    _ ≤ volume Y + volume (frontier Y) := measure_union_le _ _
    _ = volume Y := by rw [hY.addHaar_frontier volume, add_zero]

/-- Closing a worm cover preserves its covering property. -/
theorem closure_cover {Y : Set ℝ²} (hY : Y ∈ MoserWorm.WormCovers) :
    closure Y ∈ MoserWorm.WormCovers := by
  refine ⟨isClosed_closure.measurableSet, ?_⟩
  intro w hw
  obtain ⟨e, v, he, hwY⟩ := hY.2 w hw
  exact ⟨e, v, he, hwY.trans (Set.image_mono subset_closure)⟩

end WormBound

end

namespace OMA.MoserTransfer

open Set MeasureTheory
open scoped ENNReal EuclideanGeometry

private lemma variation_to_lipschitz
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hvar : eVariationOn f (Icc (0 : ℝ) 1) ≤ 1) :
    ∃ g : Icc (0 : ℝ) 1 → ℂ, LipschitzWith 1 g ∧
      f '' Icc 0 1 ⊆ range g := by
  let s := Icc (0 : ℝ) 1
  let v := variationOnFromTo f s 0
  have hzero : (0 : ℝ) ∈ s := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ s := ⟨zero_le_one, le_rfl⟩
  have hb : BoundedVariationOn f s := (hvar.trans_lt ENNReal.one_lt_top).ne
  have hloc := hb.locallyBoundedVariationOn
  have hv0 : v 0 = 0 := by
    dsimp [v]
    rw [variationOnFromTo.eq_of_le f s le_rfl, eVariationOn.subsingleton]
    · simp
    · intro a ha b hb
      have ha0 : a = 0 := by simpa using ha.2
      have hb0 : b = 0 := by simpa using hb.2
      exact ha0.trans hb0.symm
  have hv1 : v 1 ≤ 1 := by
    dsimp [v]
    rw [variationOnFromTo.eq_of_le f s zero_le_one, inter_self]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hvar).trans_eq ENNReal.toReal_one
  have hmon : MonotoneOn v s := variationOnFromTo.monotoneOn hloc hzero
  have hcont : ContinuousOn v s := by
    intro x hx
    apply continuousWithinAt_iff_continuous_left'_right'.2
    constructor
    · simpa [v, ContinuousWithinAt] using variationOnFromTo.tendsto_left hzero hx hloc
        ((hf x hx).mono (inter_subset_left : s ∩ Iio x ⊆ s))
    · simpa [v, ContinuousWithinAt] using variationOnFromTo.tendsto_right hzero hx hloc
        ((hf x hx).mono (inter_subset_left : s ∩ Ioi x ⊆ s))
  have hrange : v '' s = Icc 0 (v 1) := by
    rw [← hv0]
    exact hcont.image_Icc_of_monotoneOn zero_le_one hmon
  have hs' : (0 : ℝ) ≤ v 1 := hv0 ▸ hmon hzero hone zero_le_one
  let G := naturalParameterization f s 0
  have hGspeed := has_unit_speed_naturalParameterization f hloc hzero
  have hG : LipschitzOnWith 1 G (Icc 0 (v 1)) := by
    have hspeed : HasConstantSpeedOnWith G (Icc 0 (v 1)) 1 := by
      change HasConstantSpeedOnWith G (v '' s) 1 at hGspeed
      rwa [hrange] at hGspeed
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    simp only [NNReal.coe_one, one_mul]
    wlog hab : a ≤ b generalizing a b
    · rw [dist_comm (G a), dist_comm a]
      exact this b hb a ha (le_of_not_ge hab)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub, dist_edist]
    have hd := eVariationOn.edist_le G
      (show a ∈ Icc 0 (v 1) ∩ Icc a b from ⟨ha, le_rfl, hab⟩)
      (show b ∈ Icc 0 (v 1) ∩ Icc a b from ⟨hb, hab, le_rfl⟩)
    rw [(hasConstantSpeedOnWith_iff_ordered.mp hspeed) ha hb hab,
      NNReal.coe_one, one_mul] at hd
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hd).trans_eq
      (ENNReal.toReal_ofReal (sub_nonneg.mpr hab))
  let p := projIcc (0 : ℝ) (v 1) hs'
  refine ⟨fun t ↦ G (p t), ?_, ?_⟩
  · have hp : LipschitzWith 1 p := LipschitzWith.projIcc hs'
    have hGl : LipschitzWith 1 (fun t : Icc (0 : ℝ) (v 1) ↦ G t) := hG.to_restrict
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hg := hGl.dist_le_mul (p u) (p v)
    have hproj := hp.dist_le_mul (u : ℝ) (v : ℝ)
    simp only [NNReal.coe_one, one_mul] at hg hproj ⊢
    exact hg.trans hproj
  · rintro _ ⟨t, ht, rfl⟩
    have hvt : v t ∈ Icc 0 (v 1) := hrange ▸ mem_image_of_mem v ht
    refine ⟨⟨v t, hvt.1, hvt.2.trans hv1⟩, ?_⟩
    change G (p (v t)) = f t
    have hp : (p (v t) : ℝ) = v t := congrArg Subtype.val (projIcc_of_mem hs' hvt)
    rw [hp]
    exact edist_eq_zero.mp (edist_naturalParameterization_eq_zero hloc hzero ht)

end OMA.MoserTransfer

namespace OMA.MoserTransfer

open Set MeasureTheory
open scoped ENNReal EuclideanGeometry

noncomputable section

private abbrev toComplex : ℝ² ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

/-- Every finite-area convex cover can be translated and closed to obtain a
compact convex cover of the same area. -/
lemma compact_cover_of_finite_area {X : Set ℝ²} (hX : X ∈ MoserWorm.WormCovers)
    (hconv : Convex ℝ X) (hfinite : volume X < ⊤) :
    ∃ Y : Set ℝ², Y ∈ MoserWorm.WormCovers ∧ Convex ℝ Y ∧
      IsCompact Y ∧ Y.Nonempty ∧ volume Y = volume X := by
  obtain ⟨r, hr, hnormalized⟩ := WormInball.normalize
  obtain ⟨Y, hY, hconvY, hball, hvol⟩ := hnormalized X hX hconv
  obtain ⟨R, _, hbound⟩ := WormBound.exists_radius r hr (volume X) hfinite
  have hbounded := hbound Y hconvY hball hvol.le
  refine ⟨closure Y, WormBound.closure_cover hY, hconvY.closure,
    (isCompact_closedBall (0 : ℝ²) R).of_isClosed_subset isClosed_closure
      (closure_minimal hbounded Metric.isClosed_closedBall), ?_, ?_⟩
  · exact ⟨0, subset_closure (hball (Metric.mem_closedBall_self hr.le))⟩
  · rw [WormBound.volume_closure hconvY, hvol]

/-- Transport the desk's cover property from the Euclidean coordinate space
to the complex plane, using arc length as the parameter. -/
lemma places_rectifiable_worm
    {Y : Set ℝ²} (hY : Y ∈ MoserWorm.WormCovers)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hvar : eVariationOn f (Icc (0 : ℝ) 1) ≤ 1) :
    ∃ (l : ℂ ≃ₗᵢ[ℝ] ℂ) (a : ℂ),
      (fun z ↦ l z + a) '' (f '' Icc 0 1) ⊆ toComplex '' Y := by
  obtain ⟨g, hglip, htrace⟩ := variation_to_lipschitz f hf hvar
  let w : Icc (0 : ℝ) 1 → ℝ² := fun t ↦ toComplex.symm (g t)
  have hw : LipschitzWith 1 w := by
    simpa [w, Function.comp_def] using toComplex.symm.isometry.lipschitz.comp hglip
  obtain ⟨e, v, _, hCover⟩ := hY.2 (range w) ⟨w, hw, rfl⟩
  let l := (toComplex.symm.trans e.symm).trans toComplex
  let a := -toComplex (e.symm v)
  refine ⟨l, a, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨t, ht⟩ := htrace hz
  obtain ⟨y, hy, heq⟩ := hCover ⟨t, rfl⟩
  refine ⟨y, hy, ?_⟩
  have hey : y = e.symm (toComplex.symm z - v) := by
    apply e.injective
    simp only [LinearIsometryEquiv.apply_symm_apply]
    change e y + v = toComplex.symm (g t) at heq
    rw [ht] at heq
    exact eq_sub_of_add_eq heq
  rw [hey, map_sub, map_sub, sub_eq_add_neg]
  rfl

/-- A compact-cover estimate in the complex plane implies the precise
infimum inequality in the desk statement. -/
lemma lower_bound_transfer
    (bound : ∀ C : Set ℂ, C.Nonempty → IsCompact C → Convex ℝ C →
      (∀ f : ℝ → ℂ, ContinuousOn f (Icc (0 : ℝ) 1) →
        eVariationOn f (Icc (0 : ℝ) 1) ≤ 1 →
        ∃ (l : ℂ ≃ₗᵢ[ℝ] ℂ) (a : ℂ), (fun z ↦ l z + a) '' (f '' Icc 0 1) ⊆ C) →
      (0.232239 : ℝ≥0∞) ≤ volume C) :
    (0.232239 : ℝ≥0∞) ≤ MoserWorm.convexWormCoverConstant := by
  apply le_sInf
  rintro _ ⟨X, hX, hconv, rfl⟩
  by_cases htop : volume X = ∞
  · simp [htop]
  obtain ⟨Y, hY, hconvY, hcompactY, hnonemptyY, hvol⟩ :=
    compact_cover_of_finite_area hX hconv (lt_top_iff_ne_top.mpr htop)
  have hVol : volume (toComplex '' Y) = volume Y := by
    have hp : toComplex '' Y = toComplex.symm ⁻¹' Y := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        change toComplex.symm (toComplex y) ∈ Y
        rwa [toComplex.symm_apply_apply]
      · intro hz
        exact ⟨toComplex.symm z, hz, toComplex.apply_symm_apply z⟩
    rw [hp]
    exact toComplex.symm.measurePreserving.measure_preimage hcompactY.measurableSet.nullMeasurableSet
  rw [← hvol, ← hVol]
  exact bound (toComplex '' Y) (hnonemptyY.image toComplex)
    (hcompactY.image toComplex.continuous) (hconvY.linear_image toComplex.toLinearMap)
    (places_rectifiable_worm hY)

end

end OMA.MoserTransfer

/-! Rational interval bounds for the one-cap mixed-area payoff. -/

namespace OMA.MoserScalar

open Set

private def derivSign (cosine : Bool) (k : ℕ) : ℤ :=
  if k % 2 = (if cosine then 0 else 1)
    then (-1) ^ (k / 2)
    else 0

private def series (cosine : Bool) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 41, (derivSign cosine k : ℚ) * x ^ k / k.factorial

private noncomputable def realTrig (cosine : Bool) : ℝ → ℝ :=
  if cosine then Real.cos else Real.sin

private lemma derivative_zero (c : Bool) (k : ℕ) :
    iteratedDeriv k (realTrig c) 0 = (derivSign c k : ℝ) := by
  have hk : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  generalize hj : k / 2 = j at hk
  rcases hk with h | h <;> subst k <;> cases c <;>
    simp [realTrig, derivSign, Real.iteratedDeriv_even_sin, Real.iteratedDeriv_even_cos,
      Real.iteratedDeriv_odd_sin, Real.iteratedDeriv_odd_cos, Nat.mul_mod, Nat.add_mod,
      Nat.mul_div_cancel_left, hj, show (2 : ℕ) * j + 1 = 2 * j + 1 by rfl] <;>
    try omega

private lemma series_nonneg_bound (c : Bool) (x : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 10) :
    |realTrig c x - (series c x : ℝ)| ≤ 1 / 100000 := by
  have hB : (0 : ℝ) ≤ 10 := by norm_num
  have hp : (x : ℝ) ∈ Icc (0 : ℝ) 10 := by
    exact ⟨by exact_mod_cast hx, by exact_mod_cast hx'⟩
  have hc : ContDiff ℝ ⊤ (realTrig c) := by
    cases c
    · exact Real.contDiff_sin
    · exact Real.contDiff_cos
  have he := taylor_mean_remainder_bound (n := 40) (C := 1) hB
    (hc.contDiffOn.of_le (by simp)) hp
    (by
      intro y hy
      cases c
      · rw [show realTrig false = Real.sin by rfl,
          Real.iteratedDerivWithin_sin_Icc 41 (by norm_num : (0 : ℝ) < 10) hy, Real.norm_eq_abs]
        exact Real.abs_iteratedDeriv_sin_le_one _ _
      · rw [show realTrig true = Real.cos by rfl,
          Real.iteratedDerivWithin_cos_Icc 41 (by norm_num : (0 : ℝ) < 10) hy, Real.norm_eq_abs]
        exact Real.abs_iteratedDeriv_cos_le_one _ _)
  have hseries :
      taylorWithinEval (realTrig c) 40 (Icc (0 : ℝ) 10) 0 x = (series c x : ℝ) := by
    rw [taylor_within_apply]
    push_cast [series]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 10))
      ((hc.of_le le_top).contDiffAt) (show (0 : ℝ) ∈ Icc 0 10 by norm_num [Set.mem_Icc]), derivative_zero]
    simp [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  rw [Real.norm_eq_abs, hseries] at he
  apply he.trans
  rw [sub_zero, one_mul]
  apply (div_le_iff₀ (show (0 : ℝ) < (↑(Nat.factorial 40) : ℝ) by positivity)).2
  calc
    (x : ℝ) ^ 41 ≤ 10 ^ 41 := pow_le_pow_left₀ hp.1 hp.2 _
    _ ≤ 1 / 100000 * (↑(Nat.factorial 40) : ℝ) := by norm_num [Nat.factorial]

private def approx (c : Bool) (x : ℚ) : ℚ :=
  if 0 ≤ x then series c x else if c then series c (-x) else -series c (-x)

private lemma approx_bound (c : Bool) (x : ℚ) (hx : |x| ≤ 10) :
    |realTrig c x - (approx c x : ℝ)| ≤ 1 / 100000 := by
  by_cases h : 0 ≤ x
  · simpa only [approx, if_pos h] using series_nonneg_bound c x h ((le_abs_self _).trans hx)
  · have hn : 0 ≤ -x := by linarith
    have hx' : -x ≤ 10 := (neg_le_abs _).trans hx
    have hs := series_nonneg_bound c (-x) hn hx'
    cases c
    · change |Real.sin ((-x : ℚ) : ℝ) - (series false (-x) : ℝ)| ≤ _ at hs
      rw [Rat.cast_neg, Real.sin_neg] at hs
      simp only [approx, if_neg h, Bool.false_eq_true, if_false, Rat.cast_neg]
      change |Real.sin (x : ℝ) - -(series false (-x) : ℝ)| ≤ _
      calc
        |Real.sin (x : ℝ) - -(series false (-x) : ℝ)|
            = |-Real.sin (x : ℝ) - (series false (-x) : ℝ)| := by
              rw [← abs_neg (Real.sin (x : ℝ) - -(series false (-x) : ℝ))]
              congr 1
              ring
        _ ≤ _ := hs
    · change |Real.cos ((-x : ℚ) : ℝ) - (series true (-x) : ℝ)| ≤ _ at hs
      rw [Rat.cast_neg, Real.cos_neg] at hs
      simpa only [approx, if_neg h, realTrig, if_true] using hs

private def seriesNum (c : Bool) (n d : ℤ) : ℕ → ℤ
  | 0 => derivSign c 0
  | k + 1 => (k + 1 : ℤ) * d * seriesNum c n d k + derivSign c (k + 1) * n ^ (k + 1)

private def seriesAt (c : Bool) (x : ℚ) (j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (j + 1), (derivSign c k : ℚ) * x ^ k / k.factorial

private lemma seriesNum_eq (c : Bool) (x : ℚ) (j : ℕ) :
    (seriesNum c x.num x.den j : ℚ) =
      (x.den : ℚ) ^ j * (j.factorial : ℚ) * seriesAt c x j := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : (x.num : ℚ) = (x.den : ℚ) * x := by
    have h := (div_eq_iff hd).mp x.num_div_den
    simpa only [mul_comm] using h
  induction j with
  | zero => simp [seriesNum, seriesAt]
  | succ j ih =>
    rw [seriesNum, seriesAt, Finset.sum_range_succ]
    push_cast
    rw [ih, hx, mul_pow, Nat.factorial_succ, Nat.cast_mul, pow_succ (x.den : ℚ)]
    have hf : ((j + 1).factorial : ℚ) ≠ 0 := by positivity
    have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
    have hfact : (j.factorial : ℚ) ≠ 0 := by positivity
    change _ = _ * (seriesAt c x j + _)
    push_cast at hf ⊢
    field_simp

private def seriesPacked (c : Bool) (x : ℚ) : ℚ :=
  (seriesNum c x.num x.den 40 : ℚ) / (↑x.den ^ 40 * ↑(Nat.factorial 40))

private lemma seriesPacked_eq (c : Bool) (x : ℚ) : seriesPacked c x = series c x := by
  unfold seriesPacked
  rw [seriesNum_eq]
  apply mul_div_cancel_left₀
  positivity

private def center (c : Bool) (x : ℚ) : ℚ :=
  let y := if 0 ≤ x then seriesPacked c x else if c then seriesPacked c (-x) else -seriesPacked c (-x)
  (⌊y * 100000000⌋ : ℤ) / (100000000 : ℚ)

private lemma center_eq (c : Bool) (x : ℚ) :
    center c x = (⌊approx c x * 100000000⌋ : ℤ) / (100000000 : ℚ) := by
  simp [center, approx, seriesPacked_eq]

private lemma center_bound (c : Bool) (x : ℚ) (hx : |x| ≤ 10) :
    |realTrig c x - (center c x : ℝ)| ≤ 1 / 50000 := by
  have hl := Int.floor_le (approx c x * 100000000)
  have hu := Int.lt_floor_add_one (approx c x * 100000000)
  have hround : |approx c x - center c x| ≤ (1 : ℚ) / 100000000 := by
    rw [center_eq, abs_le]
    constructor <;> linarith only [hl, hu]
  have hround' : |(approx c x : ℝ) - (center c x : ℝ)| ≤ (1 : ℝ) / 100000000 := by
    have hh : (↑(|approx c x - center c x|) : ℝ) ≤ ((1 / 100000000 : ℚ) : ℝ) := by
      exact_mod_cast hround
    push_cast at hh
    exact hh
  exact (abs_sub_le (realTrig c x) (approx c x : ℝ) (center c x : ℝ)).trans
    ((add_le_add (approx_bound c x hx) hround').trans (by norm_num))

private structure Interval where
  lo : ℚ
  hi : ℚ

namespace Interval

private def holds (i : Interval) (x : ℝ) : Prop := (i.lo : ℝ) ≤ x ∧ x ≤ (i.hi : ℝ)
private def point (x : ℚ) : Interval := ⟨x, x⟩
private def plus (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩
private def minus (a b : Interval) : Interval := ⟨a.lo - b.hi, a.hi - b.lo⟩
private def larger (a b : Interval) : Interval := ⟨max a.lo b.lo, max a.hi b.hi⟩
private def times (a b : Interval) : Interval :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩
private def absolute (i : Interval) : Interval := ⟨max 0 (max i.lo (-i.hi)), max (-i.lo) i.hi⟩
private def middle (i : Interval) : ℚ := (i.lo + i.hi) / 2
private def radius (i : Interval) : ℚ := (i.hi - i.lo) / 2
private def trig (c : Bool) (i : Interval) : Interval :=
  if |i.middle| ≤ 10 then
    let v := center c i.middle
    let delta := i.radius + 1 / 50000
    ⟨v - delta, v + delta⟩
  else ⟨-1, 1⟩

private lemma holds_point (q : ℚ) : (point q).holds q := ⟨le_rfl, le_rfl⟩

private lemma holds_plus {a b : Interval} {x y : ℝ} (hx : a.holds x) (hy : b.holds y) :
    (a.plus b).holds (x + y) := by
  unfold holds plus
  push_cast
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

private lemma holds_minus {a b : Interval} {x y : ℝ} (hx : a.holds x) (hy : b.holds y) :
    (a.minus b).holds (x - y) := by
  unfold holds minus
  push_cast
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

private lemma holds_larger {a b : Interval} {x y : ℝ} (hx : a.holds x) (hy : b.holds y) :
    (a.larger b).holds (max x y) := by
  unfold holds larger
  push_cast
  exact ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩

private lemma holds_absolute {a : Interval} {x : ℝ} (hx : a.holds x) :
    a.absolute.holds |x| := by
  unfold holds absolute
  push_cast
  constructor
  · exact max_le (abs_nonneg _) (max_le (hx.1.trans (le_abs_self _))
      ((neg_le_neg hx.2).trans (neg_le_abs _)))
  · rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
      exact hx.2.trans (le_max_right _ _)
    · rw [abs_of_nonpos h]
      exact (neg_le_neg hx.1).trans (le_max_left _ _)

private lemma holds_times {a b : Interval} {x y : ℝ} (hx : a.holds x) (hy : b.holds y) :
    (a.times b).holds (x * y) := by
  unfold holds times
  push_cast
  constructor
  · simp only [min_le_iff]
    by_cases hx0 : 0 ≤ x
    · by_cases h : 0 ≤ b.lo
      · exact Or.inl (Or.inl ((mul_le_mul_of_nonneg_right hx.1 (by exact_mod_cast h)).trans
          (mul_le_mul_of_nonneg_left hy.1 hx0)))
      · exact Or.inr (Or.inl ((mul_le_mul_of_nonpos_right hx.2 (by exact_mod_cast le_of_not_ge h)).trans
          (mul_le_mul_of_nonneg_left hy.1 hx0)))
    · by_cases h : 0 ≤ b.hi
      · exact Or.inl (Or.inr ((mul_le_mul_of_nonneg_right hx.1 (by exact_mod_cast h)).trans
          (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hx0))))
      · exact Or.inr (Or.inr ((mul_le_mul_of_nonpos_right hx.2 (by exact_mod_cast le_of_not_ge h)).trans
          (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hx0))))
  · simp only [le_max_iff]
    by_cases hx0 : 0 ≤ x
    · by_cases h : 0 ≤ b.hi
      · exact Or.inr (Or.inr ((mul_le_mul_of_nonneg_left hy.2 hx0).trans
          (mul_le_mul_of_nonneg_right hx.2 (by exact_mod_cast h))))
      · exact Or.inl (Or.inr ((mul_le_mul_of_nonneg_left hy.2 hx0).trans
          (mul_le_mul_of_nonpos_right hx.1 (by exact_mod_cast le_of_not_ge h))))
    · by_cases h : 0 ≤ b.lo
      · exact Or.inr (Or.inl ((mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hx0)).trans
          (mul_le_mul_of_nonneg_right hx.2 (by exact_mod_cast h))))
      · exact Or.inl (Or.inl ((mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hx0)).trans
          (mul_le_mul_of_nonpos_right hx.1 (by exact_mod_cast le_of_not_ge h))))

private lemma holds_trig {a : Interval} {x : ℝ} (hx : a.holds x) (c : Bool) :
    (a.trig c).holds (realTrig c x) := by
  unfold trig
  split_ifs with hm
  · have hwithin : |x - (a.middle : ℝ)| ≤ (a.radius : ℝ) := by
      rw [abs_le]
      unfold middle radius
      push_cast
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have htr : |realTrig c x - realTrig c a.middle| ≤ |x - (a.middle : ℝ)| := by
      cases c
      · exact Real.abs_sin_sub_sin_le _ _
      · exact Real.abs_cos_sub_cos_le _ _
    have h := (abs_sub_le (realTrig c x) (realTrig c a.middle) (center c a.middle : ℝ)).trans
      (add_le_add (htr.trans hwithin) (center_bound c a.middle hm))
    rw [abs_le] at h
    unfold holds
    push_cast
    constructor <;> linarith only [h.1, h.2]
  · cases c
    · simpa [holds, realTrig] using abs_le.mp (Real.abs_sin_le_one x)
    · simpa [holds, realTrig] using abs_le.mp (Real.abs_cos_le_one x)

end Interval
end OMA.MoserScalar

namespace OMA.MoserScalar

open Set

namespace Interval

private def piBox : Interval := ⟨314159265358 / 100000000000, 314159265359 / 100000000000⟩

private def smallPayoff (t φ : Interval) : Interval :=
  let p := piBox
  let half := point (1 / 2)
  let b := (point (29 / 20)).minus t
  let d := t.minus φ
  let a := (φ.trig false).absolute.larger (half.times
    (((d.trig false).absolute.larger
      (((d.plus (p.times (point (1 / 3)))).trig false).absolute)).larger
      (((d.plus (p.times (point (1 / 6)))).trig true).absolute)))
  let q := ((((point 2).times (b.trig true)).times (φ.trig false)).absolute).larger
    (((b.plus φ).trig false).absolute.larger (((b.minus φ).trig false).absolute))
  let m := fun g ↦ (point 0).larger
    (((t.minus g).trig true).larger
      ((t.plus (p.times (point (1 / 3)))).minus g |>.trig true))
  let pHalf := p.times half
  let plusHalf := φ.plus pHalf
  let z := (((b.trig true).times (m (φ.minus pHalf))).plus
      (half.times (m (plusHalf.minus b)))).plus
      (half.times (m (plusHalf.plus b)))
  (point (1 / 6)).times (a.plus (q.larger z))

private def left (i : Interval) : Interval := ⟨i.lo, i.middle⟩
private def right (i : Interval) : Interval := ⟨i.middle, i.hi⟩

private lemma split_holds {i : Interval} {x : ℝ} (hx : i.holds x) :
    i.left.holds x ∨ i.right.holds x := by
  rcases le_total x (i.middle : ℝ) with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

private def passes (t φ : Interval) : Bool := decide ((232239 / 1000000 : ℚ) ≤ (smallPayoff t φ).lo)

private def checkBox : ℕ → Interval → Interval → Bool
  | 0, t, φ => passes t φ
  | fuel + 1, t, φ =>
    if passes t φ then true
    else if t.hi - t.lo > φ.hi - φ.lo then
      checkBox fuel t.left φ && checkBox fuel t.right φ
    else checkBox fuel t φ.left && checkBox fuel t φ.right

private def thetaBox : Interval := ⟨0, 21 / 100⟩
private def phiBox : Interval := ⟨0, 63 / 10⟩

private lemma mergePhi {t p : Interval} {fuel : ℕ}
    (hw : ¬ t.hi - t.lo > p.hi - p.lo)
    (hL : checkBox fuel t p.left = true) (hR : checkBox fuel t p.right = true) :
    checkBox (fuel + 1) t p = true := by
  simp [checkBox, hw, hL, hR]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLLLL : checkBox 9 thetaBox phiBox.left.left.left.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLLLR : checkBox 9 thetaBox phiBox.left.left.left.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLLRL : checkBox 9 thetaBox phiBox.left.left.left.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLLRR : checkBox 9 thetaBox phiBox.left.left.left.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLRLL : checkBox 9 thetaBox phiBox.left.left.right.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLRLR : checkBox 9 thetaBox phiBox.left.left.right.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLRRL : checkBox 9 thetaBox phiBox.left.left.right.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLRRR : checkBox 9 thetaBox phiBox.left.left.right.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRLLL : checkBox 9 thetaBox phiBox.left.right.left.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRLLR : checkBox 9 thetaBox phiBox.left.right.left.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRLRL : checkBox 9 thetaBox phiBox.left.right.left.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRLRR : checkBox 9 thetaBox phiBox.left.right.left.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRRLL : checkBox 9 thetaBox phiBox.left.right.right.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRRLR : checkBox 9 thetaBox phiBox.left.right.right.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRRRL : checkBox 9 thetaBox phiBox.left.right.right.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRRRR : checkBox 9 thetaBox phiBox.left.right.right.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLLLL : checkBox 9 thetaBox phiBox.right.left.left.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLLLR : checkBox 9 thetaBox phiBox.right.left.left.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLLRL : checkBox 9 thetaBox phiBox.right.left.left.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLLRR : checkBox 9 thetaBox phiBox.right.left.left.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLRLL : checkBox 9 thetaBox phiBox.right.left.right.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLRLR : checkBox 9 thetaBox phiBox.right.left.right.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLRRL : checkBox 9 thetaBox phiBox.right.left.right.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLRRR : checkBox 9 thetaBox phiBox.right.left.right.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRLLL : checkBox 9 thetaBox phiBox.right.right.left.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRLLR : checkBox 9 thetaBox phiBox.right.right.left.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRLRL : checkBox 9 thetaBox phiBox.right.right.left.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRLRR : checkBox 9 thetaBox phiBox.right.right.left.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRRLL : checkBox 9 thetaBox phiBox.right.right.right.left.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRRLR : checkBox 9 thetaBox phiBox.right.right.right.left.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRRRL : checkBox 9 thetaBox phiBox.right.right.right.right.left = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRRRR : checkBox 9 thetaBox phiBox.right.right.right.right.right = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLLL : checkBox 10 thetaBox phiBox.left.left.left.left = true := by
  exact mergePhi (by decide +kernel) verifiedLLLLL verifiedLLLLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLLR : checkBox 10 thetaBox phiBox.left.left.left.right = true := by
  exact mergePhi (by decide +kernel) verifiedLLLRL verifiedLLLRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLRL : checkBox 10 thetaBox phiBox.left.left.right.left = true := by
  exact mergePhi (by decide +kernel) verifiedLLRLL verifiedLLRLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLRR : checkBox 10 thetaBox phiBox.left.left.right.right = true := by
  exact mergePhi (by decide +kernel) verifiedLLRRL verifiedLLRRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRLL : checkBox 10 thetaBox phiBox.left.right.left.left = true := by
  exact mergePhi (by decide +kernel) verifiedLRLLL verifiedLRLLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRLR : checkBox 10 thetaBox phiBox.left.right.left.right = true := by
  exact mergePhi (by decide +kernel) verifiedLRLRL verifiedLRLRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRRL : checkBox 10 thetaBox phiBox.left.right.right.left = true := by
  exact mergePhi (by decide +kernel) verifiedLRRLL verifiedLRRLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRRR : checkBox 10 thetaBox phiBox.left.right.right.right = true := by
  exact mergePhi (by decide +kernel) verifiedLRRRL verifiedLRRRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLLL : checkBox 10 thetaBox phiBox.right.left.left.left = true := by
  exact mergePhi (by decide +kernel) verifiedRLLLL verifiedRLLLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLLR : checkBox 10 thetaBox phiBox.right.left.left.right = true := by
  exact mergePhi (by decide +kernel) verifiedRLLRL verifiedRLLRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLRL : checkBox 10 thetaBox phiBox.right.left.right.left = true := by
  exact mergePhi (by decide +kernel) verifiedRLRLL verifiedRLRLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLRR : checkBox 10 thetaBox phiBox.right.left.right.right = true := by
  exact mergePhi (by decide +kernel) verifiedRLRRL verifiedRLRRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRLL : checkBox 10 thetaBox phiBox.right.right.left.left = true := by
  exact mergePhi (by decide +kernel) verifiedRRLLL verifiedRRLLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRLR : checkBox 10 thetaBox phiBox.right.right.left.right = true := by
  exact mergePhi (by decide +kernel) verifiedRRLRL verifiedRRLRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRRL : checkBox 10 thetaBox phiBox.right.right.right.left = true := by
  exact mergePhi (by decide +kernel) verifiedRRRLL verifiedRRRLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRRR : checkBox 10 thetaBox phiBox.right.right.right.right = true := by
  exact mergePhi (by decide +kernel) verifiedRRRRL verifiedRRRRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLL : checkBox 11 thetaBox phiBox.left.left.left = true := by
  exact mergePhi (by decide +kernel) verifiedLLLL verifiedLLLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLLR : checkBox 11 thetaBox phiBox.left.left.right = true := by
  exact mergePhi (by decide +kernel) verifiedLLRL verifiedLLRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRL : checkBox 11 thetaBox phiBox.left.right.left = true := by
  exact mergePhi (by decide +kernel) verifiedLRLL verifiedLRLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLRR : checkBox 11 thetaBox phiBox.left.right.right = true := by
  exact mergePhi (by decide +kernel) verifiedLRRL verifiedLRRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLL : checkBox 11 thetaBox phiBox.right.left.left = true := by
  exact mergePhi (by decide +kernel) verifiedRLLL verifiedRLLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRLR : checkBox 11 thetaBox phiBox.right.left.right = true := by
  exact mergePhi (by decide +kernel) verifiedRLRL verifiedRLRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRL : checkBox 11 thetaBox phiBox.right.right.left = true := by
  exact mergePhi (by decide +kernel) verifiedRRLL verifiedRRLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRRR : checkBox 11 thetaBox phiBox.right.right.right = true := by
  exact mergePhi (by decide +kernel) verifiedRRRL verifiedRRRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLL : checkBox 12 thetaBox phiBox.left.left = true := by
  exact mergePhi (by decide +kernel) verifiedLLL verifiedLLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedLR : checkBox 12 thetaBox phiBox.left.right = true := by
  exact mergePhi (by decide +kernel) verifiedLRL verifiedLRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRL : checkBox 12 thetaBox phiBox.right.left = true := by
  exact mergePhi (by decide +kernel) verifiedRLL verifiedRLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedRR : checkBox 12 thetaBox phiBox.right.right = true := by
  exact mergePhi (by decide +kernel) verifiedRRL verifiedRRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedL : checkBox 13 thetaBox phiBox.left = true := by
  exact mergePhi (by decide +kernel) verifiedLL verifiedLR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem verifiedR : checkBox 13 thetaBox phiBox.right = true := by
  exact mergePhi (by decide +kernel) verifiedRL verifiedRR

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem all_checked : checkBox 14 thetaBox phiBox = true := by
  exact mergePhi (by decide +kernel) verifiedL verifiedR

private lemma hpi : piBox.holds Real.pi := by
  constructor
  · norm_num [piBox]
    exact Real.pi_gt_d20.le.trans' (by norm_num)
  · norm_num [piBox]
    exact Real.pi_lt_d20.le.trans (by norm_num)

end Interval
end OMA.MoserScalar

namespace OMA.MoserScalar

open Set
open MoserWorm

set_option maxHeartbeats 800000 in
private lemma holds_smallPayoff {t p : Interval} {θ φ : ℝ}
    (ht : t.holds θ) (hp : p.holds φ) :
    (Interval.smallPayoff t p).holds ((Payoff.A θ φ + Payoff.B θ (29 / 20 - θ) φ) / 6) := by
  have oneHalf : (Interval.point (1/2)).holds (1/2 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using Interval.holds_point (1/2)
  have oneThird : (Interval.point (1/3)).holds (1/3 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using Interval.holds_point (1/3)
  have oneSixth : (Interval.point (1/6)).holds (1/6 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using Interval.holds_point (1/6)
  have π₂ : (Interval.piBox.times (Interval.point (1/2))).holds (Real.pi / 2) := by
    simpa only [div_eq_mul_inv, one_mul] using Interval.holds_times Interval.hpi oneHalf
  have π₃ : (Interval.piBox.times (Interval.point (1/3))).holds (Real.pi / 3) := by
    simpa only [div_eq_mul_inv, one_mul] using Interval.holds_times Interval.hpi oneThird
  have π₆ : (Interval.piBox.times (Interval.point (1/6))).holds (Real.pi / 6) := by
    simpa only [div_eq_mul_inv, one_mul] using Interval.holds_times Interval.hpi oneSixth
  have hconst : (Interval.point (29/20)).holds (29/20 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using Interval.holds_point (29/20)
  have h0 : (Interval.point 0).holds 0 := by
    simpa only [Rat.cast_zero] using Interval.holds_point 0
  have h2 : (Interval.point 2).holds 2 := by
    simpa only [Rat.cast_ofNat] using Interval.holds_point 2
  have hb := Interval.holds_minus hconst ht
  have hd := Interval.holds_minus ht hp
  have hsφ := Interval.holds_trig hp false
  have hcb := Interval.holds_trig hb true
  have hA := Interval.holds_larger (Interval.holds_absolute hsφ)
    (Interval.holds_times oneHalf
      (Interval.holds_larger
        (Interval.holds_larger (Interval.holds_absolute (Interval.holds_trig hd false))
          (Interval.holds_absolute (Interval.holds_trig (Interval.holds_plus hd π₃) false)))
        (Interval.holds_absolute (Interval.holds_trig (Interval.holds_plus hd π₆) true))))
  have hQ := Interval.holds_larger
    (Interval.holds_absolute (Interval.holds_times (Interval.holds_times h2 hcb) hsφ))
    (Interval.holds_larger
      (Interval.holds_absolute (Interval.holds_trig (Interval.holds_plus hb hp) false))
      (Interval.holds_absolute (Interval.holds_trig (Interval.holds_minus hb hp) false)))
  let m := fun g : Interval ↦ (Interval.point 0).larger
    (((t.minus g).trig true).larger
      ((t.plus (Interval.piBox.times (Interval.point (1 / 3)))).minus g |>.trig true))
  have hm {g : Interval} {x : ℝ} (hg : g.holds x) :
      (m g).holds (Payoff.M θ x) :=
    Interval.holds_larger h0
      (Interval.holds_larger (Interval.holds_trig (Interval.holds_minus ht hg) true)
        (Interval.holds_trig (Interval.holds_minus (Interval.holds_plus ht π₃) hg) true))
  have hP := Interval.holds_plus
    (Interval.holds_plus (Interval.holds_times hcb (hm (Interval.holds_minus hp π₂)))
      (Interval.holds_times oneHalf (hm (Interval.holds_minus (Interval.holds_plus hp π₂) hb))))
    (Interval.holds_times oneHalf (hm (Interval.holds_plus (Interval.holds_plus hp π₂) hb)))
  have final := Interval.holds_times oneSixth (Interval.holds_plus hA (Interval.holds_larger hQ hP))
  rw [div_eq_inv_mul, ← one_div]
  simpa only [Interval.smallPayoff, Payoff.A, Payoff.B, Payoff.Q, Payoff.P, realTrig, Bool.false_eq_true,
    ↓reduceIte] using final

private lemma checked_smallPayoff {t p : Interval} {θ φ : ℝ}
    (ht : t.holds θ) (hp : p.holds φ) {fuel : ℕ}
    (hcheck : Interval.checkBox fuel t p = true) :
    0.232239 ≤ (Payoff.A θ φ + Payoff.B θ (29 / 20 - θ) φ) / 6 := by
  have pass {t p : Interval} (ht : t.holds θ) (hp : p.holds φ)
      (h : Interval.passes t p = true) :
      0.232239 ≤ (Payoff.A θ φ + Payoff.B θ (29 / 20 - θ) φ) / 6 := by
    have hq := of_decide_eq_true h
    have hcast : ((232239 / 1000000 : ℚ) : ℝ) ≤ ((t.smallPayoff p).lo : ℝ) := by
      exact_mod_cast hq
    exact (by norm_num at hcast ⊢; exact hcast.trans (holds_smallPayoff ht hp).1)
  induction fuel generalizing t p with
  | zero => exact pass ht hp hcheck
  | succ n ih =>
      by_cases hd : Interval.passes t p = true
      · exact pass ht hp hd
      rw [Interval.checkBox, if_neg hd] at hcheck
      by_cases hw : t.hi - t.lo > p.hi - p.lo
      · rw [if_pos hw] at hcheck
        have hcases := Bool.and_eq_true_iff.mp hcheck
        rcases Interval.split_holds ht with h | h
        · exact ih h hp hcases.1
        · exact ih h hp hcases.2
      · rw [if_neg hw] at hcheck
        have hcases := Bool.and_eq_true_iff.mp hcheck
        rcases Interval.split_holds hp with h | h
        · exact ih ht h hcases.1
        · exact ih ht h hcases.2

theorem small_angle_bound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθhi : θ ≤ Real.pi / 15) (φ : ℝ) :
    0.232239 ≤ (Payoff.A θ φ + Payoff.B θ (29 / 20 - θ) φ) / 6 := by
  have hper : Function.Periodic
      (fun x ↦ (Payoff.A θ x + Payoff.B θ (29 / 20 - θ) x) / 6) (2 * Real.pi) := by
    intro x
    simp only [Payoff.A_periodic θ x, Payoff.B_periodic θ (29 / 20 - θ) x]
  obtain ⟨x, hx, heq⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos φ
  rw [heq]
  apply checked_smallPayoff _ _ Interval.all_checked
  · exact ⟨by simpa [Interval.thetaBox] using hθ0,
      by norm_num [Interval.thetaBox]; linarith only [hθhi, Real.pi_lt_d4]⟩
  · exact ⟨by simpa [Interval.phiBox] using hx.1,
      by norm_num [Interval.phiBox]; linarith only [hx.2, Real.pi_lt_d4]⟩

end OMA.MoserScalar

namespace OMA.MoserLower

open MoserWorm MeasureTheory Set
open scoped ENNReal

private lemma cover_of_isometries
    (C : ConvexCover)
    (h : ∀ f : ℝ → ℂ, ContinuousOn f (Icc (0 : ℝ) 1) →
      eVariationOn f (Icc (0 : ℝ) 1) ≤ 1 →
      ∃ (l : ℂ ≃ₗᵢ[ℝ] ℂ) (a : ℂ), (fun z ↦ l z + a) '' (f '' Icc 0 1) ⊆ C.carrier) :
    UniversalForUnitWorms C .reflectionAllowed := by
  intro W
  obtain ⟨l, a, hplace⟩ := h W.curve W.continuousOn W.variation_le_one
  obtain ⟨u, hr | hr⟩ := linear_isometry_complex l
  all_goals
    obtain ⟨α, hα⟩ := Circle.exp_surjective u
    have hrot : rot α = rotation u := by
      rw [rot, Real.Angle.toCircle_coe, hα]
  · refine ⟨RigidPlacement.direct α a, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [RigidPlacement.direct_apply, hrot, ← hr, add_comm]
    exact hplace ⟨z, hz, rfl⟩
  · refine ⟨RigidPlacement.reflected α a, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [RigidPlacement.reflected_apply, hrot, reflectX, add_comm]
    exact hplace ⟨z, hz, congrArg (fun M : ℂ ≃ₗᵢ[ℝ] ℂ ↦ M z + a) hr⟩

private lemma largeAngleFloor_lower : (0.232239 : ℝ) ≤ largeAngleFloor := by
  unfold largeAngleFloor
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 10)
  have hq : (Real.pi / 10) ^ 2 ≤ (0.32 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [Real.pi_lt_d4]) 2
  linarith

private lemma planar_lower (C : ConvexCover)
    (h : UniversalForUnitWorms C .reflectionAllowed) :
    (0.232239 : ℝ) ≤ coverArea C := by
  obtain ⟨C', θ, tE, hC', harea, hθ0, hθhi, hS, hE⟩ :=
    h.placesEveryUnitPolyline.exists_nonnegative_normalized_segment_equilateral
  have hS' : (segmentHull.translate 0).carrier ⊆ C'.carrier := by
    rw [FiniteHull.carrier_translate]
    intro z hz
    rcases Set.mem_vadd_set.mp hz with ⟨p, hp, rfl⟩
    simpa only [vadd_eq_add, zero_add] using hS hp
  rw [← harea]
  by_cases hlarge : Real.pi / 15 ≤ θ
  · have hE' : (placedEquilateralPositiveSupportBoundary θ tE).walk.toFiniteHull.carrier
          ⊆ C'.carrier := by
      change (((equilateralWalk.rotate θ).translate tE).toFiniteHull.carrier ⊆ C'.carrier)
      rw [BoundaryWalk.translate_toFiniteHull_carrier_eq_finiteHull_translate]
      exact hE
    exact largeAngleFloor_lower.trans
      (largeAngleFloor_le_volumeReal_of_contains_segment_equilateral θ 0 tE hlarge hθhi
        C'.convex C'.volume_ne_top hS' hE')
  · let β : ℝ := 29 / 20 - θ
    have hb0 : 0 < β := by
      dsimp [β]
      linarith only [lt_of_not_ge hlarge, Real.pi_lt_d4]
    have hbhi : β < Real.pi / 2 := by
      dsimp [β]
      linarith only [hθ0, Real.pi_gt_three]
    obtain ⟨φ, tK, hK⟩ := hC'.exists_placed_oneCap_of_reflectionAllowed β
    refine (OMA.MoserScalar.small_angle_bound hθ0 (le_of_not_ge hlarge) φ).trans ?_
    exact oneCapPayoff_le_volumeReal_of_contains_witnesses θ φ β hb0 hbhi 0 tE tK
      C'.convex C'.volume_ne_top hS' hE hK

end OMA.MoserLower

open Set MeasureTheory MoserWorm
open scoped ENNReal

theorem OMA.solution : type_of% @MoserWorm.convex_mosers_worm_problem_lower_bound := by
  apply OMA.MoserTransfer.lower_bound_transfer
  intro C hne hcompact hconv hcover
  let body : ConvexCover := ⟨C, hne, hcompact, hconv⟩
  have hl := OMA.MoserLower.planar_lower body (OMA.MoserLower.cover_of_isometries body hcover)
  have hreal : (0.232239 : ℝ) ≤ (volume C).toReal := hl
  have hvol := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_toReal hcompact.measure_ne_top] at hvol
  have hw : ENNReal.ofReal (0.232239 : ℝ) = (0.232239 : ℝ≥0∞) := by
    change ENNReal.ofReal (↑(0.232239 : NNReal) : ℝ) = (↑(0.232239 : NNReal) : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  rwa [hw] at hvol
