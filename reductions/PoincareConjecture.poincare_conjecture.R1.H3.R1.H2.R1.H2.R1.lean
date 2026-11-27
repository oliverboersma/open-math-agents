import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1
import Mathlib

-- Credit: @NicholasWierenga

/-!
Cairns' smoothing construction first produces an ambient field of transverse leaves.
The local chart theorem then restricts the normalized projections to the carrier.
The split follows the PoincareLib contributors' SmoothNormalPosition,
SmoothTransverseFrames, FiniteComplexProjectionChart, and the kernel leaf lemmas
at LehengChen/PoincareConjecture revision 60de1a94ca7038d04ed123b490a3229f8aa5fa75.
Copyright (c) 2026 The PoincareLib contributors. Licensed under Apache-2.0.
-/

open Set Filter Geometry Metric unitInterval
open scoped ContDiff NNReal Topology

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1

private theorem eq_of_sub_mem_ker_of_convex {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Q : E → E →L[ℝ] V} {U : Set E} (hQ : ContinuousOn Q U) (hU : Convex ℝ U)
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ (Q y).ker → Q z = Q y)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hxy : y - x ∈ (Q x).ker) : Q y = Q x := by
  let c : I → E := fun t => AffineMap.lineMap x y (t : ℝ)
  have hc : Continuous c := by
    simp only [c, AffineMap.lineMap_apply_module']
    fun_prop
  have hcU (t : I) : c t ∈ U := hU.lineMap_mem hx hy t.property
  have hcont : Continuous (fun t : I => Q (c t)) := hQ.comp_continuous hc hcU
  let S : Set I := {t | Q (c t) = Q x}
  have hclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hnear := hc.continuousAt.eventually (hleaf (c t) (hcU t))
    filter_upwards [hnear] with u hu
    change Q (c u) = Q x
    rw [hu, ht]
    rw [ht]
    have hdiff : c u - c t = ((u : ℝ) - (t : ℝ)) • (y - x) := by
      simp only [c, AffineMap.lineMap_apply_module', sub_smul]
      abel
    rw [hdiff]
    exact (Q x).ker.smul_mem _ hxy
  have hnonempty : S.Nonempty := ⟨0, by simp [S, c]⟩
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  have h1 : (1 : I) ∈ S := hall.symm ▸ mem_univ _
  simpa [S, c] using h1

private theorem normalized_slice_neighborhood {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : E} {U : Set E} {Q : E → E →L[ℝ] V} (hU : IsOpen U) (ha : a ∈ U)
    (hQ : ContinuousOn Q U) (J : V →L[ℝ] E)
    (hJ : ∀ y ∈ U, Function.RightInverse J (Q y))
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ (Q y).ker → Q z = Q y) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, a + J (Q y (y - a)) ∈ U ∧
        Q (a + J (Q y (y - a))) = Q y ∧ a + J (Q y (y - a)) - y ∈ (Q y).ker := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU a ha
  let f := fun y => a + J (Q y (y - a))
  have hf : ContinuousOn f (ball a r) :=
    continuousOn_const.add (J.continuous.comp_continuousOn
      ((hQ.mono hball).clm_apply (continuous_id.sub continuous_const).continuousOn))
  let W := ball a r ∩ f ⁻¹' ball a r
  have hW : IsOpen W := hf.isOpen_inter_preimage isOpen_ball isOpen_ball
  have haW : a ∈ W := by simp [W, f, hr]
  refine ⟨W, hW, haW, fun y hy => hball hy.1, fun y hy => ?_⟩
  have hyU := hball hy.1
  have hfyU := hball hy.2
  have hker : f y - y ∈ (Q y).ker := by
    change Q y (a + J (Q y (y - a)) - y) = 0
    rw [map_sub, map_add, hJ y hyU, map_sub]
    abel
  exact ⟨hfyU, eq_of_sub_mem_ker_of_convex (hQ.mono hball) (convex_ball a r)
    (fun z hz => hleaf z (hball hz)) hy.1 hy.2 hker, hker⟩

/-- Produce a common leaf direction and smooth local projections normalized by fixed frames. -/
def H1 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    let V := EuclideanSpace ℝ (Fin 3)
    letI : DecidableEq E := Classical.decEq E
    let C (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (s : Finset E) := {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}
    AffineIndependent ℝ ((↑) : K.vertices → E) → K.faces.Finite →
    (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    (∀ s ∈ K.faces, s.card = 2 → IsConnected (C (link s))) →
    (∀ s ∈ K.faces, s.card = 3 → ({p : E | {p} ∈ link s} : Set E).ncard = 2) →
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → V,
      (∀ s ∈ star {p}, ∃ a : E →ᴬ[ℝ] V, EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (C (star {p})) ∧ (interior (f '' C (star {p}))).Nonempty) →
    ∃ P : E → Submodule ℝ E,
      ∀ a : K.space, ∃ (s : Finset E) (U : Set E) (J : V →L[ℝ] E) (Q : E → E →L[ℝ] V),
          s ∈ K.faces ∧ (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
          IsOpen U ∧ (a : E) ∈ U ∧ ContDiffOn ℝ ∞ Q U ∧
          (∃ L : ℝ≥0, ∀ x ∈ C (star s), ∀ y ∈ C (star s),
            ‖x - y‖ ≤ L * ‖Q a x - Q a y‖) ∧
          ∀ y ∈ U, Function.RightInverse J (Q y) ∧ (Q y).ker = P y ∧
            ∀ᶠ z in 𝓝 y, z - y ∈ P y → Q z = Q y

/-- Turn the normalized projections into local charts on the geometric carrier. -/
def H2 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    let V := EuclideanSpace ℝ (Fin 3)
    letI : DecidableEq E := Classical.decEq E
    K.faces.Finite → (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    (∀ s ∈ K.faces, s.card = 3 →
      ({p : E | {p} ∈ K.faces ∧ Disjoint s {p} ∧ s ∪ {p} ∈ K.faces} : Set E).ncard = 2) →
    ∀ s ∈ K.faces, ∀ a : K.space, (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) →
      ∀ (Q : E → E →L[ℝ] V) (J : V →L[ℝ] E) (W : Set K.space),
        ContDiffAt ℝ ∞ Q (a : E) → Function.RightInverse J (Q a) →
        (let S := ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)
         ∃ L : ℝ≥0, ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖Q a x - Q a y‖) → W ∈ 𝓝 a →
        ∃ c : OpenPartialHomeomorph K.space V, a ∈ c.source ∧ c.source ⊆ W ∧
          ∀ y ∈ c.source, c y = Q y ((y : E) - a)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1.H2 := by
  classical
  intro hfield hchart m K hind hgood
  obtain ⟨hfinite, hpure, he, ht, hv⟩ := hgood
  obtain ⟨P, hP⟩ := hfield m K hind hfinite hpure he ht hv
  let E := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℝ (Fin 3)
  have hcharts (a : K.space) :
      ∃ (c : OpenPartialHomeomorph K.space V) (b : V →ᴬ[ℝ] E) (Q : E → E →L[ℝ] V),
        a ∈ c.source ∧ (∀ z ∈ c.target, ContDiffAt ℝ ∞ Q (b z)) ∧
        ∀ y ∈ c.source, Function.RightInverse b.contLinear (Q y) ∧
          (Q y).ker = P y ∧ Q (b (c y)) = Q y ∧ b (c y) - y ∈ P y := by
    obtain ⟨s, U, J, Q, hs, ha, hU, haU, hQ, hbound, hproj⟩ := hP a
    obtain ⟨W, hW, haW, hWU, hslice⟩ := normalized_slice_neighborhood hU haU hQ.continuousOn J
      (fun y hy => (hproj y hy).1) (fun y hy => by
        rw [(hproj y hy).2.1]
        exact (hproj y hy).2.2)
    have hn : (Subtype.val ⁻¹' W : Set K.space) ∈ 𝓝 a :=
      (hW.preimage continuous_subtype_val).mem_nhds haW
    obtain ⟨c, hc, hsub, hformula⟩ := hchart m K hfinite hpure ht s hs a ha Q J _
      (hQ.contDiffAt (hU.mem_nhds haU)) (hproj a haU).1 hbound hn
    let b : V →ᴬ[ℝ] E := ContinuousAffineMap.const ℝ V (a : E) + J.toContinuousAffineMap
    have hlinear : b.contLinear = J := by
      apply ContinuousLinearMap.ext
      intro z
      change (0 : E) + J z = J z
      exact zero_add _
    have hdata (y : K.space) (hy : y ∈ c.source) :
        b (c y) ∈ U ∧ Q (b (c y)) = Q y ∧ b (c y) - y ∈ (Q y).ker := by
      change (a : E) + J (c y) ∈ U ∧ Q (a + J (c y)) = Q y ∧
        (a : E) + J (c y) - y ∈ (Q y).ker
      rw [hformula y hy]
      exact hslice y (hsub hy)
    refine ⟨c, b, Q, hc, ?_, fun y hy => ?_⟩
    · intro z hz
      have h := (hdata (c.symm z) (c.map_target hz)).1
      rw [c.right_inv hz] at h
      exact hQ.contDiffAt (hU.mem_nhds h)
    · have hyU := hWU (hsub hy)
      obtain ⟨_, heq, hker⟩ := hdata y hy
      rw [(hproj y hyU).2.1] at hker
      exact ⟨hlinear.symm ▸ (hproj y hyU).1, (hproj y hyU).2.1, heq, hker⟩
  choose c b Q hc hQ hspec using hcharts
  dsimp only
  intro M _ e
  let cM := fun i : M => e.transOpenPartialHomeomorph (c (e i))
  refine ⟨cM, fun y => P (e y), fun i => b (e i), fun i => Q (e i), ?_, ?_, ?_⟩
  · intro y
    exact ⟨y, hc (e y)⟩
  · intro i z hz
    exact hQ (e i) z hz
  · intro i y hy
    exact hspec (e i) (e y) hy

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1

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
