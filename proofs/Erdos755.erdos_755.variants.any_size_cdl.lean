import FormalConjectures.ErdosProblems.«755»
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
The asymptotic theorem is due to Felix Christian Clemen, Adrian Dumitrescu,
and Dingyuan Liu, The number of regular simplices in higher dimensions,
arXiv:2507.19841, doi:10.1112/blms.70452.

Parts of the geometry and graph counting are adapted from the fixed-unit
formalization by Codex and GPT-5.6 Sol at
https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos755.lean
Modified from the Apache 2.0 original. Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0
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


open Filter Metric Finset SimpleGraph
open scoped BigOperators EuclideanGeometry Asymptotics RealInnerProductSpace SimpleGraph Topology

namespace Erdos755.AnySize


private def subtypeEmbedding { α : Type* } (P : Finset α) : {x // x ∈ P} ↪ α :=
  Function.Embedding.subtype _

private def liftEmbedding { α : Type* } [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) : {x // x ∈ T} ↪ {x // x ∈ P} where
  toFun x := ⟨x, hTP x.property⟩
  inj' x y h :=
    Subtype.ext (congrArg (fun z : {x // x ∈ P} ↦ (z : α)) h)

private def liftFinset { α : Type* } [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) : Finset {x // x ∈ P} :=
  T.attach.map (liftEmbedding P T hTP)

@[simp] private lemma map_liftFinset { α : Type* } [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) :
    (liftFinset P T hTP).map (subtypeEmbedding P) = T := by
  unfold liftFinset
  rw [Finset.map_map]
  exact Finset.attach_map_val



abbrev E6 := EuclideanSpace ℝ (Fin 6)

lemma inner_sub_sub_eq_zero_of_cross_dist
    {a b c d : E6} {r : ℝ}
    (hac : dist a c = r) (had : dist a d = r)
    (hbc : dist b c = r) (hbd : dist b d = r) :
    inner ℝ (b - a) (d - c) = 0 := by
  have h_ac : inner ℝ (a - c) (a - c) = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hac]
  have h_ad : inner ℝ (a - d) (a - d) = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, had]
  have h_bc : inner ℝ (b - c) (b - c) = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbc]
  have h_bd : inner ℝ (b - d) (b - d) = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbd]
  rw [real_inner_sub_sub_self] at h_ac h_ad h_bc h_bd
  simp only [inner_sub_left, inner_sub_right] at ⊢
  linarith

lemma three_points_on_sphere_independent
    {a b c q : E6} {r : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haq : dist a q = r) (hbq : dist b q = r) (hcq : dist c q = r) :
    LinearIndependent ℝ ![b - a, c - a] := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [LinearIndependent.pair_iff' hu]
  intro t ht
  have h_a : inner ℝ (a - q) (a - q) = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, haq]
  have h_b : inner ℝ (b - q) (b - q) = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbq]
  have h_c : inner ℝ (c - q) (c - q) = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hcq]
  have hu_pos : 0 < inner ℝ (b - a) (b - a) := (real_inner_self_pos).2 hu
  have hb_split : b - q = (a - q) + (b - a) := by abel
  have hc_split : c - q = (a - q) + (c - a) := by abel
  rw [hb_split] at h_b
  rw [hc_split, ← ht] at h_c
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at h_b h_c
  rw [real_inner_comm (a - q) (b - a)] at h_b h_c
  have hpoly : (t * (t - 1)) * inner ℝ (b - a) (b - a) = 0 := by
    linear_combination h_c - h_a - t * h_b + t * h_a
  have ht_factor : t * (t - 1) = 0 :=
    (mul_eq_zero.mp hpoly).resolve_right (ne_of_gt hu_pos)
  have ht_cases : t = 0 ∨ t = 1 := by
    rcases mul_eq_zero.mp ht_factor with ht0 | ht1
    · exact Or.inl ht0
    · exact Or.inr (sub_eq_zero.mp ht1)
  rcases ht_cases with rfl | rfl
  · apply hac
    have hca : c = a := sub_eq_zero.mp (by simpa using ht.symm)
    exact hca.symm
  · apply hbc
    have huv : b - a = c - a := by simpa using ht
    calc
      b = (b - a) + a := (sub_add_cancel b a).symm
      _ = (c - a) + a := congrArg (fun z : E6 ↦ z + a) huv
      _ = c := sub_add_cancel c a

def direction4 (x : Fin 4 → Fin 3 → E6) (p : Fin 4 × Fin 2) : E6 :=
  x p.1 p.2.succ - x p.1 0

lemma eight_directions_independent
    {x : Fin 4 → Fin 3 → E6}
    (hinj : Function.Injective (fun p : Fin 4 × Fin 3 ↦ x p.1 p.2))
    (s : Fin 4 → Fin 4 → ℝ)
    (hdist : ∀ {i j : Fin 4}, i ≠ j → ∀ a b, dist (x i a) (x j b) = s i j) :
    LinearIndependent ℝ (direction4 x) := by
  have hne (i : Fin 4) {a b : Fin 3} (hab : a ≠ b) : x i a ≠ x i b := by
    intro h
    apply hab
    exact congrArg Prod.snd (hinj (a₁ := (i, a)) (a₂ := (i, b)) h)
  have hblock (i : Fin 4) :
      LinearIndependent ℝ (fun k : Fin 2 ↦ direction4 x (i, k)) := by
    obtain ⟨j, hji⟩ := exists_ne i
    have h := three_points_on_sphere_independent
      (a := x i 0) (b := x i 1) (c := x i 2) (q := x j 0)
      (hne i (by decide)) (hne i (by decide)) (hne i (by decide))
      (hdist hji.symm 0 0) (hdist hji.symm 1 0) (hdist hji.symm 2 0)
    convert h using 1
    funext k
    fin_cases k <;> rfl
  have hortho {i j : Fin 4} (hij : i ≠ j) (k l : Fin 2) :
      inner ℝ (direction4 x (i, k)) (direction4 x (j, l)) = 0 := by
    exact inner_sub_sub_eq_zero_of_cross_dist
      (hdist hij 0 0) (hdist hij 0 l.succ)
      (hdist hij k.succ 0) (hdist hij k.succ l.succ)
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  let z : Fin 4 → E6 := fun i ↦ ∑ k : Fin 2, g (i, k) • direction4 x (i, k)
  have hsum : ∑ i : Fin 4, z i = 0 := by
    change (∑ i : Fin 4, ∑ k : Fin 2, g (i, k) • direction4 x (i, k)) = 0
    calc
      _ = ∑ p : Fin 4 × Fin 2, g p • direction4 x p :=
        (Fintype.sum_prod_type (fun p : Fin 4 × Fin 2 ↦ g p • direction4 x p)).symm
      _ = 0 := hg
  have hcross {i j : Fin 4} (hij : i ≠ j) : inner ℝ (z i) (z j) = 0 := by
    simp only [z, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    exact Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ by
      rw [hortho hij]
      ring
  have hz (i : Fin 4) : z i = 0 := by
    have hi := congrArg (fun y : E6 ↦ inner ℝ y (z i)) hsum
    simp only [sum_inner, inner_zero_left] at hi
    have hii : inner ℝ (z i) (z i) = 0 := by
      rw [← hi]
      symm
      exact Finset.sum_eq_single i
        (fun j _ hji ↦ hcross hji)
        (by intro hiu; exact (hiu (Finset.mem_univ i)).elim)
    exact inner_self_eq_zero.mp hii
  exact (Fintype.linearIndependent_iff.mp (hblock p.1)
    (fun k ↦ g (p.1, k)) (hz p.1)) p.2

lemma no_four_cross_constant_triples
    {x : Fin 4 → Fin 3 → E6}
    (hinj : Function.Injective (fun p : Fin 4 × Fin 3 ↦ x p.1 p.2))
    (s : Fin 4 → Fin 4 → ℝ)
    (hdist : ∀ {i j : Fin 4}, i ≠ j → ∀ a b, dist (x i a) (x j b) = s i j) : False := by
  have hli := eight_directions_independent hinj s hdist
  have hdim := hli.fintype_card_le_finrank
  norm_num at hdim



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


lemma linearIndependent_two_differences
    {x₀ x₁ x₂ : E}
    (hn₀ : ‖x₀‖ = 1) (hn₁ : ‖x₁‖ = 1) (hn₂ : ‖x₂‖ = 1)
    (h₀₁ : x₀ ≠ x₁) (h₀₂ : x₀ ≠ x₂) (h₁₂ : x₁ ≠ x₂) :
    LinearIndependent ℝ ![x₁ - x₀, x₂ - x₀] := by
  apply (LinearIndependent.pair_iff' (sub_ne_zero.mpr h₀₁.symm)).2
  intro a ha
  have hx₂ : x₂ = a • (x₁ - x₀) +ᵥ x₀ := by
    rw [ha]
    simp
  have heqa : dist (a • (x₁ - x₀) +ᵥ x₀) 0 = dist x₀ 0 := by
    rw [← hx₂]
    simpa [dist_eq_norm] using hn₂.trans hn₀.symm
  have heq1 : dist ((1 : ℝ) • (x₁ - x₀) +ᵥ x₀) 0 = dist x₀ 0 := by
    simp [dist_eq_norm, hn₀, hn₁]
  have hra := (EuclideanGeometry.dist_smul_vadd_eq_dist x₀ 0
    (sub_ne_zero.mpr h₀₁.symm) a).mp heqa
  have hr1 := (EuclideanGeometry.dist_smul_vadd_eq_dist x₀ 0
    (sub_ne_zero.mpr h₀₁.symm) 1).mp heq1
  have ha01 : a = 0 ∨ a = 1 := by
    rcases hra with hzero | hother
    · exact .inl hzero
    · rcases hr1 with hbad | hgood
      · exact (one_ne_zero hbad).elim
      · exact .inr (hother.trans hgood.symm)
  rcases ha01 with rfl | rfl
  · simp only [zero_smul] at ha
    apply h₀₂
    exact (sub_eq_zero.mp ha.symm).symm
  · simp only [one_smul] at ha
    apply h₁₂
    simpa using congrArg (fun z : E ↦ z + x₀) ha

lemma linearIndependent_three_orthogonal_pairs
    (u : Fin 3 → Fin 2 → E)
    (hli : ∀ i, LinearIndependent ℝ (u i))
    (hortho : ∀ i j, i ≠ j → ∀ k l : Fin 2, ⟪u i k, u j l⟫ = 0) :
    LinearIndependent ℝ (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let b : Fin 3 → E := fun j ↦ ∑ k, g (j, k) • u j k
  have hsum : ∑ j, b j = 0 := by
    rw [← Finset.univ_product_univ, Finset.sum_product] at hg
    simpa only [b] using hg
  have hb : ∀ j, b j = 0 := by
    intro j
    have hinner : ⟪b j, b j⟫ = 0 := by
      have := congrArg (fun z : E ↦ ⟪z, b j⟫) hsum
      simp only [inner_zero_left] at this
      have hqorth : ∀ q, q ≠ j → ⟪b q, b j⟫ = 0 := by
        intro q hqj
        simp only [b, sum_inner, real_inner_smul_left, inner_sum,
          real_inner_smul_right, hortho q j hqj, mul_zero, Finset.sum_const_zero]
      rw [sum_inner] at this
      rw [Finset.sum_eq_single j (fun q _ hqj ↦ hqorth q hqj)
        (fun hj ↦ False.elim (hj (Finset.mem_univ j)))] at this
      exact this
    exact inner_self_eq_zero.mp hinner
  have hcoeff := Fintype.linearIndependent_iff.mp (hli i.1) (fun k ↦ g (i.1, k))
  apply hcoeff
  simpa only [b] using hb i.1

lemma inner_eq_zero_of_mem_orthogonal_spans
    {I J : Type*} {u : I → E} {v : J → E}
    (horth : ∀ i j, ⟪u i, v j⟫ = 0) {x y : E}
    (hx : x ∈ Submodule.span ℝ (Set.range u))
    (hy : y ∈ Submodule.span ℝ (Set.range v)) : ⟪x, y⟫ = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb => obtain ⟨j, rfl⟩ := hb; exact horth i j
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
    | smul c y _ hy => simp only [inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x z _ _ hx hz => simp [inner_add_left, hx, hz]
  | smul c x _ hx => simp only [inner_smul_left, hx, mul_zero]

lemma mem_one_span_of_orthogonal_block_basis
    (u : Fin 3 → Fin 2 → E)
    (hortho : ∀ i j, i ≠ j → ∀ k l : Fin 2, ⟪u i k, u j l⟫ = 0)
    (hspan : Submodule.span ℝ (Set.range (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2)) = ⊤)
    (i : Fin 3) (x : E)
    (hxorth : ∀ q, q ≠ i → ∀ k, ⟪x, u q k⟫ = 0) :
    x ∈ Submodule.span ℝ (Set.range (u i)) := by
  have hxspan : x ∈ Submodule.span ℝ
      (Set.range (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxspan
  let b : Fin 3 → E := fun q ↦ ∑ k, c (q, k) • u q k
  have hsum : ∑ q, b q = x := by
    rw [← Finset.univ_product_univ, Finset.sum_product] at hc
    simpa only [b] using hc
  have hbzero : ∀ q, q ≠ i → b q = 0 := by
    intro q hqi
    have hxb : ⟪x, b q⟫ = 0 := by
      simp only [b, inner_sum, real_inner_smul_right, hxorth q hqi, mul_zero,
        Finset.sum_const_zero]
    rw [← hsum, sum_inner] at hxb
    have hrorth : ∀ r, r ≠ q → ⟪b r, b q⟫ = 0 := by
      intro r hrq
      simp only [b, sum_inner, real_inner_smul_left, inner_sum, real_inner_smul_right,
        hortho r q hrq, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single q (fun r _ hrq ↦ hrorth r hrq)
      (fun hq ↦ False.elim (hq (Finset.mem_univ q)))] at hxb
    exact inner_self_eq_zero.mp hxb
  rw [← hsum]
  apply Submodule.sum_mem
  intro q hq
  by_cases hqi : q = i
  · subst q
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  · rw [hbzero q hqi]
    exact Submodule.zero_mem _

lemma inner_eq_half_of_unit_norm_and_distance {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ = 1) :
    ⟪x, y⟫ = (1 / 2 : ℝ) := by
  have h := norm_sub_sq_real x y
  rw [hx, hy, hxy] at h
  linarith

lemma no_three_unit_cross_classes
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 6)
    (x : Fin 3 → Fin 3 → E)
    (hinj : ∀ i, Function.Injective (x i))
    (hnorm : ∀ i j, ‖x i j‖ = 1)
    (hcross : ∀ i j, i ≠ j → ∀ k l, ‖x i k - x j l‖ = 1) : False := by
  let u : Fin 3 → Fin 2 → E := fun i k ↦ x i k.succ - x i 0
  have hli : ∀ i, LinearIndependent ℝ (u i) := by
    intro i
    have h₀₁ : x i 0 ≠ x i 1 := (hinj i).ne (by decide)
    have h₀₂ : x i 0 ≠ x i 2 := (hinj i).ne (by decide)
    have h₁₂ : x i 1 ≠ x i 2 := (hinj i).ne (by decide)
    have h := linearIndependent_two_differences
      (hnorm i 0) (hnorm i 1) (hnorm i 2)
      h₀₁ h₀₂ h₁₂
    convert h using 1
    funext k
    fin_cases k <;> rfl
  have hhalf : ∀ i j, i ≠ j → ∀ k l, ⟪x i k, x j l⟫ = (1 / 2 : ℝ) := by
    intro i j hij k l
    exact inner_eq_half_of_unit_norm_and_distance
      (hnorm i k) (hnorm j l) (hcross i j hij k l)
  have hortho : ∀ i j, i ≠ j → ∀ k l : Fin 2, ⟪u i k, u j l⟫ = 0 := by
    intro i j hij k l
    simp only [u, inner_sub_left, inner_sub_right, hhalf i j hij]
    ring
  have htotal : LinearIndependent ℝ (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2) :=
    linearIndependent_three_orthogonal_pairs u hli hortho
  have hspan : Submodule.span ℝ (Set.range (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2)) = ⊤ :=
    htotal.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  have hbase : ∀ i, x i 0 ∈ Submodule.span ℝ (Set.range (u i)) := by
    intro i
    apply mem_one_span_of_orthogonal_block_basis u hortho hspan i (x i 0)
    intro q hqi k
    simp only [u, inner_sub_right, hhalf i q hqi.symm, sub_self]
  have hzero : ⟪x 0 0, x 1 0⟫ = 0 :=
    inner_eq_zero_of_mem_orthogonal_spans (fun k l ↦ hortho 0 1 (by decide) k l)
      (hbase 0) (hbase 1)
  have hpositive : ⟪x 0 0, x 1 0⟫ = (1 / 2 : ℝ) := hhalf 0 1 (by decide) 0 0
  linarith



namespace EdgeExtremal

open Finset Fintype SimpleGraph

theorem extremalNumber_le_quadratic_of_minDegree
    {W : Type*} (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hmd : ∀ n, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      H.Free G → (G.minDegree : ℝ) < c * n) :
    ∀ n, (extremalNumber n H : ℝ) ≤ (N : ℝ) ^ 2 + c * n * (n + 1) / 2 := by
  intro n
  induction n with
  | zero =>
    conv_lhs => rw [← Fintype.card_fin 0]
    rw [extremalNumber_le_iff_of_nonneg H]
    · intro G _ _
      have he : (#G.edgeFinset : ℕ) ≤ 0 := by
        simpa using G.card_edgeFinset_le_card_choose_two
      have he0 : (#G.edgeFinset : ℝ) = 0 := by
        exact_mod_cast Nat.eq_zero_of_le_zero he
      rw [he0]
      positivity
    · positivity
  | succ n ih =>
    conv_lhs => rw [← Fintype.card_fin (n + 1)]
    rw [extremalNumber_le_iff_of_nonneg H]
    · intro G _ hfree
      norm_num at ⊢
      by_cases hn : N ≤ n + 1
      · letI : Nonempty (Fin (n + 1)) := Fin.pos_iff_nonempty.mp (by omega)
        obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
        have hdeg : (G.degree v : ℝ) < c * (n + 1) := by
          rw [← hv]
          simpa only [Nat.cast_add, Nat.cast_one] using hmd (n + 1) hn G hfree
        have hdel : (#(G.deleteIncidenceSet v).edgeFinset : ℝ) ≤
            (extremalNumber n H : ℝ) := by
          simpa using G.card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
        have hsplit : #G.edgeFinset = #(G.deleteIncidenceSet v).edgeFinset + G.degree v := by
          rw [G.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (G.degree_le_card_edgeFinset (v := v))]
        rw [hsplit, Nat.cast_add]
        calc
          (#(G.deleteIncidenceSet v).edgeFinset : ℝ) + G.degree v
              ≤ (extremalNumber n H : ℝ) + G.degree v := add_le_add hdel le_rfl
          _ ≤ ((N : ℝ) ^ 2 + c * n * (n + 1) / 2) + G.degree v :=
            add_le_add ih le_rfl
          _ ≤ (N : ℝ) ^ 2 + c * (n + 1) * (n + 1 + 1) / 2 := by
            norm_num at hdeg ⊢
            nlinarith
      · have hnlt : n + 1 < N := by omega
        calc
          (#G.edgeFinset : ℝ) ≤ (((n + 1).choose 2 : ℕ) : ℝ) := by
            exact_mod_cast (by simpa using G.card_edgeFinset_le_card_choose_two)
          _ ≤ ((N ^ 2 : ℕ) : ℝ) := by
            exact_mod_cast (calc
              (n + 1).choose 2 ≤ (n + 1) ^ 2 := Nat.choose_le_pow _ _
              _ ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) _)
          _ ≤ ((N : ℝ) ^ 2 + c * (n + 1) * (n + 1 + 1) / 2 : ℝ) := by
            norm_num
            positivity
    · positivity

theorem card_edgeFinset_le_quadratic_of_minDegree
    {V W : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hmd : ∀ n, N ≤ n → ∀ (J : SimpleGraph (Fin n)) [DecidableRel J.Adj],
      H.Free J → (J.minDegree : ℝ) < c * n)
    (hfree : H.Free G) :
    (#G.edgeFinset : ℝ) ≤
      (N : ℝ) ^ 2 + c * Fintype.card V * (Fintype.card V + 1) / 2 := by
  have hcard : (#G.edgeFinset : ℝ) ≤ (extremalNumber (Fintype.card V) H : ℝ) := by
    exact_mod_cast G.card_edgeFinset_le_extremalNumber hfree
  exact hcard.trans
    (extremalNumber_le_quadratic_of_minDegree H c hc N hmd (Fintype.card V))

theorem exists_card_edgeFinset_le_completeEquipartite
    (r t : ℕ) (hr : 0 < r) { δ : ℝ } (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (completeEquipartiteGraph (r + 1) t).Free G →
      (#G.edgeFinset : ℝ) ≤ (N : ℝ) ^ 2 +
        (1 - 1 / (r : ℝ) + δ) * Fintype.card V * (Fintype.card V + 1) / 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_completeEquipartiteGraph_isContained_of_minDegree hδ r t)
  refine ⟨N, fun V _ G _ hfree ↦ card_edgeFinset_le_quadratic_of_minDegree
    (completeEquipartiteGraph (r + 1) t) (1 - 1 / (r : ℝ) + δ) ?_ N ?_ hfree⟩
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have : 1 / (r : ℝ) ≤ 1 := (div_le_one hr0).mpr hr1
    linarith
  · intro n hn J _ hfreeJ
    by_contra hlt
    apply hfreeJ
    exact hN n hn (le_of_not_gt hlt)

theorem exists_card_edgeFinset_le_K3_3 { δ : ℝ } (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (completeEquipartiteGraph 3 3).Free G →
      (#G.edgeFinset : ℝ) ≤ (N : ℝ) ^ 2 +
        (1 / 2 + δ) * Fintype.card V * (Fintype.card V + 1) / 2 := by
  obtain ⟨N, hN⟩ := exists_card_edgeFinset_le_completeEquipartite 2 3 (by norm_num) hδ
  refine ⟨N, fun V _ G _ hfree ↦ ?_⟩
  convert hN V G hfree using 1 <;> norm_num

theorem exists_uniform_card_edgeFinset_le_K3_3 { η : ℝ } (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (completeEquipartiteGraph 3 3).Free G →
        (#G.edgeFinset : ℝ) ≤ (1 / 4 + η) * (Fintype.card V : ℝ) ^ 2 + C := by
  obtain ⟨N, hN⟩ := exists_card_edgeFinset_le_K3_3 hη
  let c : ℝ := 1 / 2 + η
  let C : ℝ := (N : ℝ) ^ 2 + c ^ 2 / (8 * η)
  refine ⟨C, by dsimp [C]; positivity, fun V _ G _ hfree ↦ ?_⟩
  let m : ℝ := Fintype.card V
  have hm : 0 ≤ m := by positivity
  have hb := hN V G hfree
  have hyoung : c / 2 * m - η / 2 * m ^ 2 ≤ c ^ 2 / (8 * η) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * η)).2
    nlinarith [sq_nonneg (2 * η * m - c)]
  dsimp [m, c] at hyoung
  dsimp [C, c] at ⊢
  nlinarith

end EdgeExtremal


namespace GraphCounting

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The triangles containing a given vertex. -/
def trianglesAt (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (v ∈ ·)

/-- The edges of the graph induced on the neighbors of `v`. -/
def linkEdges (v : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ G.neighborFinset v

private lemma edge_eq_of_toFinset_eq {e₁ e₂ : Sym2 V}
    (he₁ : e₁ ∈ G.edgeFinset) (he₂ : e₂ ∈ G.edgeFinset)
    (h : e₁.toFinset = e₂.toFinset) : e₁ = e₂ := by
  induction e₁ with
  | _ u₁ v₁ =>
    induction e₂ with
    | _ u₂ v₂ =>
      have hne₁ : u₁ ≠ v₁ := by
        have : G.Adj u₁ v₁ := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he₁
        exact this.ne
      have hne₂ : u₂ ≠ v₂ := by
        have : G.Adj u₂ v₂ := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he₂
        exact this.ne
      have hset : ({u₁, v₁} : Set V) = {u₂, v₂} := by
        have hfin : ({u₁, v₁} : Finset V) = {u₂, v₂} := by
          simpa [Sym2.toFinset_mk_eq] using h
        simpa using congrArg (↑· : Finset V → Set V) hfin
      rcases Set.pair_eq_pair_iff.mp hset with h | h
      · rcases h with ⟨rfl, rfl⟩
        rfl
      · rcases h with ⟨rfl, rfl⟩
        exact Sym2.eq_swap

lemma card_linkEdges_eq_card_trianglesAt (v : V) :
    #(linkEdges G v) = #(trianglesAt G v) := by
  classical
  apply Finset.card_bij (fun e _ ↦ insert v e.toFinset)
  · intro e he
    rw [linkEdges, mem_filter] at he
    induction e with
    | _ u w =>
      have huw : G.Adj u w := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he.1
      have hvu : G.Adj v u := by
        exact (G.mem_neighborFinset v u).mp (he.2 (by simp [Sym2.toFinset_mk_eq]))
      have hvw : G.Adj v w := by
        exact (G.mem_neighborFinset v w).mp (he.2 (by simp [Sym2.toFinset_mk_eq]))
      simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff]
      constructor
      · simpa [Sym2.toFinset_mk_eq] using
          (SimpleGraph.is3Clique_triple_iff.mpr ⟨hvu, hvw, huw⟩)
      · simp
  · intro e₁ he₁ e₂ he₂ heq
    rw [linkEdges, mem_filter] at he₁ he₂
    have hvnot₁ : v ∉ e₁.toFinset := by
      intro hv
      exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp (he₁.2 hv))
    have hvnot₂ : v ∉ e₂.toFinset := by
      intro hv
      exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp (he₂.2 hv))
    apply edge_eq_of_toFinset_eq G he₁.1 he₂.1
    have herase := congrArg (fun s : Finset V ↦ s.erase v) heq
    simpa [hvnot₁, hvnot₂] using herase
  · intro K hK
    simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff] at hK
    have hErase := hK.1.erase_of_mem hK.2
    obtain ⟨u, w, huw, hpair⟩ := card_eq_two.mp (by simpa using hErase.card_eq)
    refine ⟨s(u, w), ?_, ?_⟩
    · rw [linkEdges, mem_filter]
      constructor
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        apply hErase.isClique
        · rw [hpair]; simp
        · rw [hpair]; simp
        · exact huw
      · intro x hx
        have hxErase : x ∈ K.erase v := by
          rw [hpair]
          simpa [Sym2.toFinset_mk_eq] using hx
        exact (G.mem_neighborFinset v x).mpr
          (hK.1.isClique hK.2 (mem_of_mem_erase hxErase)
            (by simpa using (ne_of_mem_erase hxErase).symm))
    · simpa [Sym2.toFinset_mk_eq, ← hpair] using insert_erase hK.2

lemma card_linkEdges_eq_card_induce_neighborFinset (v : V) :
    #(linkEdges G v) =
      #((G.induce (↑(G.neighborFinset v) : Set V)).edgeFinset) := by
  simpa [linkEdges] using
    G.card_filter_edgeFinset_toFinset_subset (G.neighborFinset v)

lemma sum_card_trianglesAt :
    ∑ v, #(trianglesAt G v) = 3 * #(G.cliqueFinset 3) := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun v (K : Finset V) ↦ v ∈ K)
    (s := (univ : Finset V)) (t := G.cliqueFinset 3)
  have hcard : ∀ K ∈ G.cliqueFinset 3, #K = 3 := fun _ hK ↦
    (mem_cliqueFinset_iff.mp hK).card_eq
  calc
    ∑ v, #(trianglesAt G v) =
        ∑ K ∈ G.cliqueFinset 3, #((univ : Finset V).bipartiteBelow (· ∈ ·) K) := by
      simpa [trianglesAt, Finset.bipartiteAbove] using hdc
    _ = ∑ K ∈ G.cliqueFinset 3, #K := by simp [Finset.bipartiteBelow]
    _ = ∑ _K ∈ G.cliqueFinset 3, 3 := sum_congr rfl hcard
    _ = 3 * #(G.cliqueFinset 3) := by simp [mul_comm]

/-- The vertices adjacent to both endpoints of an unordered pair. -/
def edgeCommonFinset (e : Sym2 V) : Finset V :=
  univ.filter fun w ↦ ∀ v ∈ e.toFinset, G.Adj v w

/-- The triangles containing both endpoints of an unordered pair. -/
def trianglesAtEdge (e : Sym2 V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (e.toFinset ⊆ ·)

lemma edgeCommonFinset_mk (u v : V) :
    edgeCommonFinset G s(u, v) = G.neighborFinset u ∩ G.neighborFinset v := by
  ext w
  simp [edgeCommonFinset, SimpleGraph.mem_neighborFinset]

lemma card_edgeCommonFinset_eq_card_trianglesAtEdge_mk {u v : V} (huv : G.Adj u v) :
    #(edgeCommonFinset G s(u, v)) = #(trianglesAtEdge G s(u, v)) := by
  classical
  apply Finset.card_bij (fun w _ ↦ {u, v, w})
  · intro w hw
    have hw' : G.Adj u w ∧ G.Adj v w := by
      simpa [edgeCommonFinset] using hw
    simp only [trianglesAtEdge, mem_filter, mem_cliqueFinset_iff]
    constructor
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, hw'.1, hw'.2⟩
    · simp [Sym2.toFinset_mk_eq]
  · intro w₁ hw₁ w₂ hw₂ heq
    have h₁ : G.Adj u w₁ ∧ G.Adj v w₁ := by
      simpa [edgeCommonFinset] using hw₁
    have h₂ : G.Adj u w₂ ∧ G.Adj v w₂ := by
      simpa [edgeCommonFinset] using hw₂
    have hm : w₁ ∈ ({u, v, w₂} : Finset V) := by rw [← heq]; simp
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with h | h | h
    · exact False.elim (h₁.1.ne h.symm)
    · exact False.elim (h₁.2.ne h.symm)
    · exact h
  · intro K hK
    simp only [trianglesAtEdge, mem_filter, mem_cliqueFinset_iff] at hK
    have hpair : {u, v} ⊆ K := by
      simpa [Sym2.toFinset_mk_eq] using hK.2
    have hnot : ¬ K ⊆ {u, v} := by
      intro hsub
      have hc := card_le_card hsub
      have hcardK : #K = 3 := hK.1.card_eq
      have huvne : u ≠ v := huv.ne
      simp [hcardK, huvne] at hc
    simp only [not_subset] at hnot
    obtain ⟨w, hwK, hwpair⟩ := hnot
    have hwne : w ≠ u ∧ w ≠ v := by simpa [eq_comm] using hwpair
    have htriple : {u, v, w} = K := by
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hpair (by simp)
        · exact hpair (by simp)
        · exact hwK
      · have htripleCard : #{u, v, w} = 3 := by
          have hreorder : ({u, v, w} : Finset V) = insert w {u, v} := by
            ext x
            simp [or_comm, or_left_comm]
          rw [hreorder]
          rw [card_insert_of_notMem]
          · simp [huv.ne]
          · simpa [eq_comm] using hwne
        rw [hK.1.card_eq, htripleCard]
    have hwAdj : G.Adj u w ∧ G.Adj v w := by
      have hc := hK.1.isClique
      constructor
      · exact hc (hpair (by simp)) hwK (by simpa using hwne.1.symm)
      · exact hc (hpair (by simp)) hwK (by simpa using hwne.2.symm)
    refine ⟨w, ?_, htriple⟩
    simpa [edgeCommonFinset] using hwAdj

lemma card_edgeCommonFinset_eq_card_trianglesAtEdge (e : Sym2 V)
    (he : e ∈ G.edgeFinset) :
    #(edgeCommonFinset G e) = #(trianglesAtEdge G e) := by
  induction e with
  | _ u v =>
    apply card_edgeCommonFinset_eq_card_trianglesAtEdge_mk
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he

private lemma card_edges_inside_triangle (K : Finset V) (hK : G.IsNClique 3 K) :
    #((G.edgeFinset).filter fun e ↦ e.toFinset ⊆ K) = 3 := by
  classical
  calc
    #((G.edgeFinset).filter fun e ↦ e.toFinset ⊆ K) = #(K.powersetCard 2) := by
      apply Finset.card_bij (fun e _ ↦ e.toFinset)
      · intro e he
        rw [mem_filter] at he
        rw [mem_powersetCard]
        exact ⟨he.2, G.card_toFinset_mem_edgeFinset ⟨e, he.1⟩⟩
      · intro e₁ he₁ e₂ he₂ heq
        rw [mem_filter] at he₁ he₂
        exact edge_eq_of_toFinset_eq G he₁.1 he₂.1 heq
      · intro s hs
        rw [mem_powersetCard] at hs
        obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hs.2
        refine ⟨s(u, v), ?_, ?_⟩
        · rw [mem_filter]
          constructor
          · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact hK.isClique (hs.1 (by simp)) (hs.1 (by simp)) huv
          · simpa [Sym2.toFinset_mk_eq] using hs.1
        · simp [Sym2.toFinset_mk_eq]
    _ = 3 := by simp [hK.card_eq]

lemma sum_card_edgeCommonFinset :
    ∑ e ∈ G.edgeFinset, #(edgeCommonFinset G e) =
      3 * #(G.cliqueFinset 3) := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun (e : Sym2 V) (K : Finset V) ↦ e.toFinset ⊆ K)
    (s := G.edgeFinset) (t := G.cliqueFinset 3)
  calc
    ∑ e ∈ G.edgeFinset, #(edgeCommonFinset G e) =
        ∑ e ∈ G.edgeFinset, #(trianglesAtEdge G e) := by
      apply sum_congr rfl
      intro e he
      exact card_edgeCommonFinset_eq_card_trianglesAtEdge G e he
    _ = ∑ K ∈ G.cliqueFinset 3,
          #((G.edgeFinset).bipartiteBelow (fun e K ↦ e.toFinset ⊆ K) K) := by
      simpa [trianglesAtEdge, Finset.bipartiteAbove] using hdc
    _ = ∑ _K ∈ G.cliqueFinset 3, 3 := by
      apply sum_congr rfl
      intro K hK
      simpa [Finset.bipartiteBelow] using
        card_edges_inside_triangle G K (mem_cliqueFinset_iff.mp hK)
    _ = 3 * #(G.cliqueFinset 3) := by simp [mul_comm]

lemma sum_degree_sq_eq_sum_edges :
    ∑ v, (G.degree v) ^ 2 =
      ∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, G.degree v := by
  classical
  have hdc := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow
    (r := fun (v : V) (e : Sym2 V) ↦ v ∈ e)
    (s := (univ : Finset V)) (t := G.edgeFinset)
    (f := fun v (_e : Sym2 V) ↦ G.degree v)
  calc
    ∑ v, (G.degree v) ^ 2 =
        ∑ v, ∑ _e ∈ G.incidenceFinset v, G.degree v := by
      apply sum_congr rfl
      intro v _
      simp [pow_two, SimpleGraph.card_incidenceFinset_eq_degree]
    _ = ∑ e ∈ G.edgeFinset,
          ∑ v ∈ (univ : Finset V).bipartiteBelow (fun v e ↦ v ∈ e) e,
            G.degree v := by
      simpa [SimpleGraph.incidenceFinset_eq_filter, Finset.bipartiteAbove] using hdc
    _ = ∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, G.degree v := by
      apply sum_congr rfl
      intro e _
      congr 1
      ext v
      simp [Finset.bipartiteBelow]

lemma sum_degrees_on_edge_le (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (∑ v ∈ e.toFinset, G.degree v) ≤
      Fintype.card V + #(edgeCommonFinset G e) := by
  classical
  induction e with
  | _ u v =>
    have huv : G.Adj u v := by
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have hunion : #(G.neighborFinset u ∪ G.neighborFinset v) ≤ Fintype.card V := by
      simpa using card_le_card
        (show G.neighborFinset u ∪ G.neighborFinset v ⊆ univ by simp)
    have hcard := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    rw [edgeCommonFinset_mk]
    rw [Sym2.toFinset_mk_eq]
    simp [huv.ne]
    change #(G.neighborFinset u) + #(G.neighborFinset v) ≤
      Fintype.card V + #(G.neighborFinset u ∩ G.neighborFinset v)
    omega

lemma sum_degree_sq_le :
    ∑ v, (G.degree v) ^ 2 ≤
      Fintype.card V * #(G.edgeFinset) + 3 * #(G.cliqueFinset 3) := by
  classical
  rw [sum_degree_sq_eq_sum_edges]
  calc
    ∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, G.degree v ≤
        ∑ e ∈ G.edgeFinset, (Fintype.card V + #(edgeCommonFinset G e)) := by
      exact sum_le_sum fun e he ↦ sum_degrees_on_edge_le G e he
    _ = Fintype.card V * #(G.edgeFinset) +
          ∑ e ∈ G.edgeFinset, #(edgeCommonFinset G e) := by
      simp [sum_add_distrib, mul_comm]
    _ = Fintype.card V * #(G.edgeFinset) + 3 * #(G.cliqueFinset 3) := by
      rw [sum_card_edgeCommonFinset]

end GraphCounting


lemma three_mul_card_cliqueFinset_le_of_links
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a C : ℝ)
    (hlink : ∀ v,
      ((G.induce (↑(G.neighborFinset v) : Set V)).edgeFinset.card : ℝ) ≤
        a * (G.degree v : ℝ) ^ 2 + C) :
    3 * ((G.cliqueFinset 3).card : ℝ) ≤
      a * ((∑ v, (G.degree v) ^ 2 : ℕ) : ℝ) + C * Fintype.card V := by
  classical
  have hv (v : V) :
      ((GraphCounting.trianglesAt G v).card : ℝ) ≤
        a * (G.degree v : ℝ) ^ 2 + C := by
    rw [← GraphCounting.card_linkEdges_eq_card_trianglesAt G v,
      GraphCounting.card_linkEdges_eq_card_induce_neighborFinset G v]
    exact hlink v
  have hsum := Finset.sum_le_sum
    (fun v (_hv : v ∈ (Finset.univ : Finset V)) ↦ hv v)
  rw [← Nat.cast_sum] at hsum
  rw [GraphCounting.sum_card_trianglesAt] at hsum
  norm_num at hsum ⊢
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_pow,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Finset.mul_sum, nsmul_eq_mul, Nat.cast_id, mul_assoc, mul_comm] using hsum



noncomputable def distanceGraph (P : Finset E6) (r : ℝ) : SimpleGraph P where
  Adj u v := u ≠ v ∧ dist (u : E6) (v : E6) = r
  symm.symm := fun _ _ h ↦ ⟨h.1.symm, (_root_.dist_comm _ _).trans h.2⟩
  loopless.irrefl := fun _ h ↦ h.1 rfl

noncomputable instance (P : Finset E6) (r : ℝ) : DecidableRel (distanceGraph P r).Adj :=
  Classical.decRel _

theorem distanceGraph_link_free (P : Finset E6) (r : ℝ) (v : P) :
    (completeEquipartiteGraph 3 3).Free
      ((distanceGraph P r).induce (↑((distanceGraph P r).neighborFinset v) : Set P)) := by
  rintro ⟨f⟩
  let x (i : Fin 3) (j : Fin 3) : E6 := (((f (i, j)).val : P) : E6) - (v : E6)
  have hnorm : ∀ i j, ‖x i j‖ = r := by
    intro i j
    have h := ((distanceGraph P r).mem_neighborFinset v ((f (i, j)).val : P)).mp (f (i, j)).prop
    rw [← dist_eq_norm]
    exact (_root_.dist_comm _ _).trans h.2
  have hpos : 0 < r := by
    have h := ((distanceGraph P r).mem_neighborFinset v ((f (0, 0)).val : P)).mp (f (0, 0)).prop
    exact h.2 ▸ dist_pos.mpr (fun he ↦ h.1 (Subtype.ext he))
  have hcross : ∀ i j, i ≠ j → ∀ k l, ‖x i k - x j l‖ = r := by
    intro i j hij k l
    have hadj := f.toHom.map_adj
      (show (completeEquipartiteGraph 3 3).Adj (i, k) (j, l) from hij)
    have hd : dist (((f (i, k)).val : P) : E6) (((f (j, l)).val : P) : E6) = r := hadj.2
    rw [dist_eq_norm] at hd
    simpa only [x, sub_sub_sub_cancel_right] using hd
  let y (i : Fin 3) (j : Fin 3) : E6 := r⁻¹ • x i j
  refine no_three_unit_cross_classes (E := E6) (by simp) y ?_ ?_ ?_
  · intro i j k hjk
    have hxy : x i j = x i k := by
      have h := congrArg (fun z : E6 ↦ r • z) hjk
      simpa [y, smul_smul, ne_of_gt hpos] using h
    have hf : f (i, j) = f (i, k) := Subtype.ext (Subtype.ext (sub_left_inj.mp hxy))
    exact congrArg Prod.snd (f.injective hf)
  · intro i j
    simp [y, norm_smul, hnorm, abs_of_pos hpos, ne_of_gt hpos]
  · intro i j hij k l
    rw [show y i k - y j l = r⁻¹ • (x i k - x j l) from (smul_sub _ _ _).symm,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, hcross i j hij,
      inv_mul_cancel₀ (ne_of_gt hpos)]

theorem distanceGraph_triangle_bound {η : ℝ} (hη : 0 < η) (hsmall : η ≤ 1 / 10) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset E6) (r : ℝ),
      (#((distanceGraph P r).cliqueFinset 3) : ℝ) ≤
        (1 / 9 + η) * #P * #((distanceGraph P r).edgeFinset) + C * #P := by
  obtain ⟨C, hC, hc⟩ := EdgeExtremal.exists_uniform_card_edgeFinset_le_K3_3 hη
  refine ⟨C, hC, fun P r ↦ ?_⟩
  classical
  let G := distanceGraph P r
  let t : ℝ := #(G.cliqueFinset 3)
  let e : ℝ := #G.edgeFinset
  let n : ℝ := #P
  let S : ℝ := (∑ v, (G.degree v) ^ 2 : ℕ)
  have hS : S ≤ n * e + 3 * t := by
    simpa [S, n, e, t] using (Nat.cast_le (α := ℝ)).2 (GraphCounting.sum_degree_sq_le G)
  have ht : 3 * t ≤ (1 / 4 + η) * S + C * n := by
    have h := three_mul_card_cliqueFinset_le_of_links G (1 / 4 + η) C (fun v ↦ by
      have hh := hc _ _ (distanceGraph_link_free P r v)
      rw [show Fintype.card (↑((distanceGraph P r).neighborFinset v) : Set P) =
        (distanceGraph P r).degree v from Fintype.card_of_subtype _ (fun _ ↦ Iff.rfl)] at hh
      exact hh)
    simpa [t, S, n] using h
  have ha : 0 ≤ (1 / 4 + η : ℝ) := by positivity
  have hb : 1 ≤ (3 * (1 - (1 / 4 + η)) : ℝ) := by linarith
  have he : 0 ≤ n * e := by positivity
  have hCn : 0 ≤ C * n := by positivity
  have hcoef : (1 / 4 + η : ℝ) ≤ 3 * (1 - (1 / 4 + η)) * (1 / 9 + η) := by
    nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hsmall)]
  have hbound : 3 * (1 - (1 / 4 + η)) * t ≤ (1 / 4 + η) * (n * e) + C * n := by
    nlinarith [mul_le_mul_of_nonneg_left hS ha]
  have hscale := add_le_add (mul_le_mul_of_nonneg_right hcoef he)
    (mul_le_mul_of_nonneg_right hb hCn)
  change t ≤ (1 / 9 + η) * n * e + C * n
  apply le_of_mul_le_mul_left _ (show 0 < 3 * (1 - (1 / 4 + η)) by linarith)
  calc
    _ ≤ _ := hbound.trans (by simpa only [one_mul] using hscale)
    _ = _ := by ring

theorem graph_triangle_count_sq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (3 * (#(G.cliqueFinset 3) : ℝ)) ^ 2 ≤ 4 * (#G.edgeFinset : ℝ) ^ 3 := by
  classical
  let S := G.edgeFinset
  let c (e : Sym2 V) : ℝ := #(GraphCounting.edgeCommonFinset G e)
  let d (v : V) : ℝ := G.degree v
  let i : Sym2 V ↪ V × V := ⟨Quot.out, fun x y h ↦ by
    have h' := congrArg (fun z : V × V ↦ s(z.1, z.2)) h
    change s(x.out.1, x.out.2) = s(y.out.1, y.out.2) at h'
    rw [Sym2.mk, Sym2.mk, x.out_eq, y.out_eq] at h'
    exact h'⟩
  have hc (e : Sym2 V) : c e ^ 2 ≤ d (i e).1 * d (i e).2 := by
    have hre : s((i e).1, (i e).2) = e := Quot.out_eq _
    nth_rw 1 [← hre]
    simp only [c, GraphCounting.edgeCommonFinset_mk]
    have h1 : (#(G.neighborFinset (i e).1 ∩ G.neighborFinset (i e).2) : ℝ) ≤ d (i e).1 := by
      dsimp [d]
      exact_mod_cast (card_le_card inter_subset_left).trans_eq (G.card_neighborFinset_eq_degree _)
    have h2 : (#(G.neighborFinset (i e).1 ∩ G.neighborFinset (i e).2) : ℝ) ≤ d (i e).2 := by
      dsimp [d]
      exact_mod_cast (card_le_card inter_subset_right).trans_eq (G.card_neighborFinset_eq_degree _)
    rw [pow_two]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hsum : ∑ e ∈ S, c e = 3 * (#(G.cliqueFinset 3) : ℝ) := by
    change ∑ e ∈ G.edgeFinset, (↑(#(GraphCounting.edgeCommonFinset G e)) : ℝ) = _
    exact_mod_cast GraphCounting.sum_card_edgeCommonFinset G
  have hdeg : ∑ v, d v = 2 * (#G.edgeFinset : ℝ) := by
    change ∑ v, (G.degree v : ℝ) = _
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hsumSq : ∑ e ∈ S, c e ^ 2 ≤ (2 * (#G.edgeFinset : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ e ∈ S, d (i e).1 * d (i e).2 := sum_le_sum fun e _ ↦ hc e
      _ = ∑ p ∈ S.map i, d p.1 * d p.2 := by rw [Finset.sum_map]
      _ ≤ ∑ p : V × V, d p.1 * d p.2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ ↦ by positivity)
      _ = (2 * (#G.edgeFinset : ℝ)) ^ 2 := by
        rw [Fintype.sum_prod_type, pow_two, ← hdeg, Finset.sum_mul_sum]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) S (fun _ ↦ 1) c
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hCS
  rw [← hsum]
  exact hCS.trans (by
    calc
      _ ≤ (S.card : ℝ) * (2 * (#G.edgeFinset : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsumSq (by positivity)
      _ = _ := by dsimp [S]; ring)


theorem choose_constant_on_embedding {C : Type*} [Fintype C] [Nonempty C]
    {n m : ℕ} (f : Fin n → C) (h : Fintype.card C * m ≤ n) :
    ∃ g : Fin m ↪ Fin n, ∃ c : C, ∀ i, f (g i) = c := by
  classical
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (f := f) (by simpa using h)
  have hcard : Fintype.card (Fin m) ≤ Fintype.card {i : Fin n // f i = c} := by
    simpa [Fintype.card_subtype] using hc
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨g.trans (Function.Embedding.subtype _), c, fun i ↦ (g i).2⟩

def boxBound (q : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => max (q ^ k * 3) (q ^ (q ^ k * 3) * boxBound q k)

theorem monochromatic_between_parts {C : Type*} [Fintype C] [Nonempty C]
    (k n : ℕ) (h : boxBound (Fintype.card C) k ≤ n)
    (color : Fin k → Fin k → Fin n → Fin n → C) :
    ∃ g : Fin k → Fin 3 ↪ Fin n, ∀ (i j : Fin k), i < j → ∀ a b,
      color i j (g i a) (g j b) = color i j (g i 0) (g j 0) := by
  classical
  induction k generalizing n with
  | zero => exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ k ih =>
    let q := Fintype.card C
    let m := q ^ k * 3
    let b := boxBound q k
    have h' : max m (q ^ m * b) ≤ n := h
    let p : Fin m ↪ Fin n := Fin.castLEEmb ((le_max_left _ _).trans h')
    have hsmall (j : Fin k) :
        ∃ g : Fin b ↪ Fin n, ∃ f : Fin m → C, ∀ t a,
          color 0 j.succ (p a) (g t) = f a := by
      obtain ⟨g, f, hf⟩ := choose_constant_on_embedding
        (fun (t : Fin n) (a : Fin m) ↦ color 0 j.succ (p a) t)
        (m := b) (by simpa [q, Fintype.card_fun] using (le_max_right m (q ^ m * b)).trans h')
      exact ⟨g, f, fun t a ↦ congrFun (hf t) a⟩
    choose l pattern hl using hsmall
    obtain ⟨g', gc, hg'⟩ := choose_constant_on_embedding (fun (a : Fin m) (j : Fin k) ↦ pattern j a)
      (m := 3) (by simp [m, q, Fintype.card_fun])
    obtain ⟨s, hs⟩ := ih b le_rfl (fun i j a t ↦ color i.succ j.succ (l i a) (l j t))
    let g : Fin (k + 1) → Fin 3 ↪ Fin n := Fin.cases (g'.trans p) (fun i ↦ (s i).trans (l i))
    refine ⟨g, fun i j ↦ ?_⟩
    revert i j
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · intro j
      refine Fin.cases (by simp) (fun j _ a t ↦ ?_) j
      change color 0 j.succ (p (g' a)) (l j (s j t)) = color 0 j.succ (p (g' 0)) (l j (s j 0))
      rw [hl, hl, congrFun (hg' a) j, congrFun (hg' 0) j]
    · intro j
      refine Fin.cases (by simp) (fun j hij a t ↦ ?_) j
      exact hs i j (by simpa using hij) a t

noncomputable def paletteGraph (P : Finset E6) (S : Finset ℝ) : SimpleGraph P where
  Adj u v := u ≠ v ∧ dist (u : E6) (v : E6) ∈ S
  symm.symm := by
    intro u v h
    exact ⟨h.1.symm, by rw [_root_.dist_comm]; exact h.2⟩
  loopless.irrefl := fun _ h ↦ h.1 rfl

noncomputable instance (P : Finset E6) (S : Finset ℝ) : DecidableRel (paletteGraph P S).Adj :=
  Classical.decRel _

theorem paletteGraph_free (P : Finset E6) (S : Finset ℝ) (q : ℕ) (hq : S.card + 1 ≤ q) :
    (completeEquipartiteGraph 4 (boxBound q 4)).Free (paletteGraph P S) := by
  classical
  rintro ⟨f⟩
  have hq0 : 0 < q := by omega
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq0
  obtain ⟨label⟩ : Nonempty (Option S ↪ Fin q) := Function.Embedding.nonempty_of_card_le (by simpa)
  let c : ℝ → Fin q := fun r ↦ label (if h : r ∈ S then some ⟨r, h⟩ else none)
  have hcol (r s : ℝ) (hr : r ∈ S) (hs : s ∈ S) (h : c r = c s) : r = s := by
    have hh := label.injective h
    simpa [hr, hs] using hh
  let D (i : Fin 4) (j : Fin (boxBound q 4)) : E6 := (f (i, j) : P).val
  obtain ⟨g, hg⟩ := monochromatic_between_parts (C := Fin q) 4 (boxBound q 4)
    (by simp) (fun i j a b ↦ c (dist (D i a) (D j b)))
  let x (i : Fin 4) (a : Fin 3) : E6 := D i (g i a)
  have hinj : Function.Injective (fun p : Fin 4 × Fin 3 ↦ x p.1 p.2) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hf : f (i, g i a) = f (j, g j b) := Subtype.ext h
    have hpair := f.injective hf
    have hij := congrArg Prod.fst hpair
    dsimp at hij
    subst j
    exact Prod.ext rfl ((g i).injective (congrArg Prod.snd hpair))
  apply no_four_cross_constant_triples hinj (fun i j ↦ dist (x i 0) (x j 0))
  have hmem {i j : Fin 4} (hij : i ≠ j) (a b : Fin 3) : dist (x i a) (x j b) ∈ S :=
    (f.toHom.map_adj (show (completeEquipartiteGraph 4 (boxBound q 4)).Adj
      (i, g i a) (j, g j b) from hij)).2
  have hlt (i j : Fin 4) (hij : i < j) (a b : Fin 3) :
      dist (x i a) (x j b) = dist (x i 0) (x j 0) :=
    hcol _ _ (hmem hij.ne a b) (hmem hij.ne 0 0) (hg i j hij a b)
  intro i j hij a b
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h a b
  · rw [_root_.dist_comm (x i a), _root_.dist_comm (x i 0)]
    exact hlt j i h b a


noncomputable def edgeLength (P : Finset E6) : Sym2 P → ℝ :=
  Sym2.lift ⟨fun u v ↦ dist (u : E6) (v : E6), fun _ _ ↦ _root_.dist_comm _ _⟩

noncomputable def distancePalette (P : Finset E6) : Finset ℝ := by
  classical
  exact (⊤ : SimpleGraph P).edgeFinset.image (edgeLength P)

theorem distanceGraph_edgeFinset (P : Finset E6) (r : ℝ) :
    (distanceGraph P r).edgeFinset = ((⊤ : SimpleGraph P).edgeFinset.filter fun e ↦ edgeLength P e = r) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, mem_filter, SimpleGraph.mem_edgeFinset]
    rfl

theorem paletteGraph_edgeFinset (P : Finset E6) (S : Finset ℝ) :
    (paletteGraph P S).edgeFinset = ((⊤ : SimpleGraph P).edgeFinset.filter fun e ↦ edgeLength P e ∈ S) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, mem_filter, SimpleGraph.mem_edgeFinset]
    rfl

theorem sum_distance_edges (P : Finset E6) (S : Finset ℝ) :
    ∑ r ∈ S, #((distanceGraph P r).edgeFinset) = #((paletteGraph P S).edgeFinset) := by
  classical
  simp only [distanceGraph_edgeFinset, paletteGraph_edgeFinset]
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

theorem all_distance_edges (P : Finset E6) :
    ∑ r ∈ distancePalette P, #((distanceGraph P r).edgeFinset) ≤ P.card ^ 2 := by
  classical
  rw [sum_distance_edges, paletteGraph_edgeFinset]
  exact (Finset.card_filter_le _ _).trans (by
    simpa using ((⊤ : SimpleGraph P).card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)))

theorem clique_side_unique (P : Finset E6) {r s : ℝ} {T : Finset P}
    (hr : (distanceGraph P r).IsNClique 3 T) (hs : (distanceGraph P s).IsNClique 3 T) : r = s := by
  obtain ⟨u, hu, v, hv, hn⟩ := Finset.one_lt_card.mp (by rw [hr.2]; decide)
  exact (hr.1 hu hv hn).2.symm.trans (hs.1 hu hv hn).2

theorem any_size_count_eq_sum (P : Finset E6) :
    anySizeEquilateralTriangleCount 6 P =
      ∑ r ∈ distancePalette P, #((distanceGraph P r).cliqueFinset 3) := by
  classical
  rw [← Finset.card_biUnion (t := fun r ↦ (distanceGraph P r).cliqueFinset 3) (by
    intro r _ s _ hrs
    exact Finset.disjoint_left.mpr fun T hr hs ↦ hrs (clique_side_unique P
      (mem_cliqueFinset_iff.mp hr) (mem_cliqueFinset_iff.mp hs)))]
  unfold anySizeEquilateralTriangleCount
  apply Finset.card_bij (fun T hT ↦ liftFinset P T ((mem_powersetCard.mp (mem_filter.mp hT).1).1))
  · intro T hT
    obtain ⟨_, r, _, hTcard, hdist⟩ := mem_filter.mp hT
    let U := liftFinset P T ((mem_powersetCard.mp (mem_filter.mp hT).1).1)
    have hem : U.map (subtypeEmbedding P) = T := map_liftFinset _ _ _
    have hcard : U.card = 3 := by rw [← Finset.card_map (f := subtypeEmbedding P), hem, hTcard]
    have hcl : (distanceGraph P r).IsNClique 3 U := by
      refine ⟨?_, hcard⟩
      intro u hu v hv huv
      have hua : u.val ∈ T := hem ▸ Finset.mem_map.mpr ⟨u, hu, rfl⟩
      have hva : v.val ∈ T := hem ▸ Finset.mem_map.mpr ⟨v, hv, rfl⟩
      exact ⟨huv, hdist u hua v hva (fun h ↦ huv (Subtype.ext h))⟩
    refine Finset.mem_biUnion.mpr ⟨r, ?_, mem_cliqueFinset_iff.mpr hcl⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < U.card by rw [hcard]; decide)
    exact Finset.mem_image.mpr ⟨s(u, v), by simpa using huv, (hcl.1 hu hv huv).2⟩
  · intro T hT U hU he
    simpa using congrArg (fun R ↦ R.map (subtypeEmbedding P)) he
  · intro U hU
    obtain ⟨r, hr, hcl⟩ := Finset.mem_biUnion.mp hU
    have hc := mem_cliqueFinset_iff.mp hcl
    let T := U.map (subtypeEmbedding P)
    have hcard : T.card = 3 := by simpa [T] using hc.2
    have hTP : T ⊆ P := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
      exact x.2
    have hpos : 0 < r := by
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < U.card by rw [hc.2]; decide)
      rw [← (hc.1 hu hv huv).2]
      exact dist_pos.mpr (fun h ↦ huv (Subtype.ext h))
    have hT : T ∈ (P.powersetCard 3).filter IsAnySizeEquilateralTriangle := by
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hTP, hcard⟩, r, hpos, hcard, ?_⟩
      intro u hu v hv huv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
      exact (hc.1 hx hy (fun h ↦ huv (congrArg Subtype.val h))).2
    refine ⟨T, hT, Finset.map_injective (subtypeEmbedding P) ?_⟩
    simp [T]

theorem light_distance_bound (P : Finset E6) (r : ℝ) {η : ℝ} (hη : 0 < η)
    (hl : (#((distanceGraph P r).edgeFinset) : ℝ) ≤ η ^ 2 * (P.card : ℝ) ^ 2) :
    (#((distanceGraph P r).cliqueFinset 3) : ℝ) ≤ η * P.card * #((distanceGraph P r).edgeFinset) := by
  classical
  let G := distanceGraph P r
  let t : ℝ := #(G.cliqueFinset 3)
  let e : ℝ := #G.edgeFinset
  let n : ℝ := P.card
  change e ≤ η ^ 2 * n ^ 2 at hl
  change t ≤ η * n * e
  have he : 0 ≤ e := by positivity
  have ht : 0 ≤ t := by positivity
  have hn : 0 ≤ η * n * e := by positivity
  have hsq : (3 * t) ^ 2 ≤ 4 * e ^ 3 := graph_triangle_count_sq G
  have he3 : 4 * e ^ 3 ≤ 4 * (η * n * e) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg e)]
  have hh : 3 * t ≤ 2 * (η * n * e) := by
    apply le_of_sq_le_sq _ (by positivity : 0 ≤ 2 * (η * n * e))
    nlinarith [hsq.trans he3]
  linarith

theorem uniform_palette_edge_bound (q : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset E6) (S : Finset ℝ), S.card + 1 ≤ q →
      (#((paletteGraph P S).edgeFinset) : ℝ) ≤ (1 / 3 + η) * (P.card : ℝ) ^ 2 + D := by
  obtain ⟨N, hN⟩ := EdgeExtremal.exists_card_edgeFinset_le_completeEquipartite
    3 (boxBound q 4) (by norm_num) hη
  let c : ℝ := 2 / 3 + η
  let D : ℝ := (N : ℝ) ^ 2 + c ^ 2 / (8 * η)
  refine ⟨D, by dsimp [D]; positivity, fun P S hS ↦ ?_⟩
  have h := hN P (paletteGraph P S) (paletteGraph_free P S q hS)
  let n : ℝ := P.card
  have hyoung : c / 2 * n - η / 2 * n ^ 2 ≤ c ^ 2 / (8 * η) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * η)).2
    nlinarith [sq_nonneg (2 * η * n - c)]
  rw [Fintype.card_coe] at h
  change (#((paletteGraph P S).edgeFinset) : ℝ) ≤ (1 / 3 + η) * n ^ 2 + D
  dsimp [c, D, n] at *
  nlinarith

theorem arbitrary_points_upper {η : ℝ} (hη : 0 < η) (hsmall : η ≤ 1 / 10) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ P : Finset E6,
      (anySizeEquilateralTriangleCount 6 P : ℝ) ≤
        (1 / 27 + 2 * η) * (P.card : ℝ) ^ 3 + B * P.card := by
  classical
  let q : ℕ := ⌈(η ^ 2)⁻¹⌉₊ + 1
  obtain ⟨D, hD, hD_bound⟩ := uniform_palette_edge_bound q hη
  obtain ⟨C, hC, hC_bound⟩ := distanceGraph_triangle_bound hη hsmall
  let B : ℝ := (1 / 9 + η) * D + C * q
  refine ⟨B, by dsimp [B]; positivity, fun P ↦ ?_⟩
  by_cases hP : P.card = 0
  · have hp0 := Finset.card_eq_zero.mp hP
    simp [hp0, anySizeEquilateralTriangleCount]
  let n : ℝ := P.card
  let e (r : ℝ) : ℝ := #((distanceGraph P r).edgeFinset)
  let t (r : ℝ) : ℝ := #((distanceGraph P r).cliqueFinset 3)
  let S := distancePalette P
  let heavy (r : ℝ) : Prop := η ^ 2 * n ^ 2 ≤ e r
  let H : Finset ℝ := S.filter heavy
  let L : Finset ℝ := S.filter fun r ↦ ¬ heavy r
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Nat.pos_of_ne_zero hP
  have htotal : ∑ r ∈ S, e r ≤ n ^ 2 := by
    change ∑ r ∈ distancePalette P, (↑(#((distanceGraph P r).edgeFinset)) : ℝ) ≤ _
    dsimp [n]
    exact_mod_cast all_distance_edges P
  have hsum_heavy : (H.card : ℝ) * (η ^ 2 * n ^ 2) ≤ n ^ 2 := by
    calc
      _ = ∑ r ∈ H, η ^ 2 * n ^ 2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ r ∈ H, e r := sum_le_sum fun r hr ↦ (mem_filter.mp hr).2
      _ ≤ ∑ r ∈ S, e r := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun r _ _ ↦ by positivity)
      _ ≤ _ := htotal
  have hH : H.card + 1 ≤ q := by
    have h : (H.card : ℝ) * η ^ 2 ≤ 1 := by
      apply le_of_mul_le_mul_right _ (sq_pos_of_pos hn)
      simpa only [mul_assoc, one_mul] using hsum_heavy
    have hh : (H.card : ℝ) ≤ (η ^ 2)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ (sq_pos_of_pos hη)]
      exact h
    apply Nat.add_le_add_right
    exact_mod_cast hh.trans (Nat.le_ceil _)
  have hE : ∑ r ∈ H, e r ≤ (1 / 3 + η) * n ^ 2 + D := by
    have hs := hD_bound P H hH
    rw [← sum_distance_edges] at hs
    simpa [e, n] using hs
  have hheavy : ∑ r ∈ H, t r ≤
      ((1 / 9 + η) * (1 / 3 + η)) * n ^ 3 + (1 / 9 + η) * D * n + C * n * q := by
    calc
      _ ≤ ∑ r ∈ H, ((1 / 9 + η) * n * e r + C * n) := sum_le_sum fun r _ ↦ hC_bound P r
      _ = (1 / 9 + η) * n * (∑ r ∈ H, e r) + C * n * H.card := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (H.card : ℝ)]
      _ ≤ (1 / 9 + η) * n * ((1 / 3 + η) * n ^ 2 + D) + C * n * q := by
        have hcast : (H.card : ℝ) ≤ q := by exact_mod_cast (show H.card ≤ q by omega)
        gcongr
      _ = _ := by ring
  have hlight : ∑ r ∈ L, t r ≤ η * n ^ 3 := by
    calc
      _ ≤ ∑ r ∈ L, η * n * e r := sum_le_sum fun r hr ↦
        light_distance_bound P r hη (le_of_not_ge (mem_filter.mp hr).2)
      _ = η * n * (∑ r ∈ L, e r) := by rw [mul_sum]
      _ ≤ η * n * n ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun r _ _ ↦ by positivity)).trans htotal
      _ = _ := by ring
  have hcoef : (1 / 9 + η) * (1 / 3 + η) + η ≤ 1 / 27 + 2 * η := by
    nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hsmall)]
  have hcast : (anySizeEquilateralTriangleCount 6 P : ℝ) = ∑ r ∈ S, t r := by
    rw [any_size_count_eq_sum, Nat.cast_sum]
  rw [hcast, ← sum_filter_add_sum_filter_not S heavy t]
  change ∑ r ∈ H, t r + ∑ r ∈ L, t r ≤ (1 / 27 + 2 * η) * n ^ 3 + B * n
  have hh := add_le_add hheavy hlight
  have hc := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hn.le 3)
  dsimp [B] at ⊢
  linarith only [hh, hc]


noncomputable def circleX (k : ℕ) : ℝ := (k : ℝ) / ((k : ℝ) + 1)

noncomputable def circleY (k : ℕ) : ℝ := Real.sqrt (1 - (circleX k) ^ 2)

theorem circle_coordinates (k : ℕ) : circleX k ^ 2 + circleY k ^ 2 = 1 := by
  have h0 : 0 ≤ circleX k := by unfold circleX; positivity
  have h1 : circleX k ≤ 1 := by
    unfold circleX
    apply (div_le_one (by positivity)).mpr
    linarith
  rw [circleY, Real.sq_sqrt (by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])]
  ring

theorem circleX_injective : Function.Injective circleX := by
  intro k l h
  unfold circleX at h
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hl : (l : ℝ) + 1 ≠ 0 := by positivity
  apply Nat.cast_injective (R := ℝ)
  have hh := (div_eq_div_iff hk hl).mp h
  linarith only [hh]

noncomputable def circlePoint (i : Fin 3) (k : ℕ) : E6 :=
  WithLp.toLp 2 (fun j : Fin 6 ↦
    if j.val = 2 * i.val then circleX k else if j.val = 2 * i.val + 1 then circleY k else 0)

theorem circle_point_norm_sq (i : Fin 3) (k : ℕ) : ‖circlePoint i k‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;> simp [circlePoint, Fin.sum_univ_succ, circle_coordinates]

theorem circle_point_inner (i j : Fin 3) (hij : i ≠ j) (k l : ℕ) :
    inner ℝ (circlePoint i k) (circlePoint j l) = 0 := by
  rw [PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;>
    simp_all [circlePoint, Fin.sum_univ_succ]

theorem circle_point_dist (i j : Fin 3) (hij : i ≠ j) (k l : ℕ) :
    dist (circlePoint i k) (circlePoint j l) = Real.sqrt 2 := by
  rw [dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), norm_sub_sq_real,
    circle_point_norm_sq, circle_point_norm_sq, circle_point_inner i j hij, Real.sq_sqrt (by norm_num)]
  norm_num

theorem circle_point_eq_iff {i j : Fin 3} {k l : ℕ} :
    circlePoint i k = circlePoint j l ↔ i = j ∧ k = l := by
  constructor
  · intro h
    have hij : i = j := by
      by_contra hne
      have hh := circle_point_dist i j hne k l
      rw [h, _root_.dist_self] at hh
      linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    subst j
    refine ⟨rfl, circleX_injective ?_⟩
    let a : Fin 6 := ⟨2 * i.val, by omega⟩
    have hh := congrArg (fun v : E6 ↦ v a) h
    simpa [circlePoint, a] using hh
  · rintro ⟨rfl, rfl⟩
    rfl

noncomputable def circlePointEmbedding (m : ℕ) : Fin 3 × Fin m ↪ E6 :=
  ⟨fun p ↦ circlePoint p.1 p.2.val, fun _ _ h ↦ by
    obtain ⟨hi, hk⟩ := circle_point_eq_iff.mp h
    exact Prod.ext hi (Fin.ext hk)⟩

open scoped Classical in
noncomputable def circleTriangle {m : ℕ} (p : Fin m × Fin m × Fin m) : Finset E6 :=
  {circlePoint 0 p.1.val, circlePoint 1 p.2.1.val, circlePoint 2 p.2.2.val}

theorem circle_triangle_injective (m : ℕ) : Function.Injective (@circleTriangle m) := by
  classical
  intro p q h
  have h0 : circlePoint 0 p.1.val ∈ circleTriangle q := by rw [← h]; simp [circleTriangle]
  have h1 : circlePoint 1 p.2.1.val ∈ circleTriangle q := by rw [← h]; simp [circleTriangle]
  have h2 : circlePoint 2 p.2.2.val ∈ circleTriangle q := by rw [← h]; simp [circleTriangle]
  simp [circleTriangle, circle_point_eq_iff] at h0 h1 h2
  exact Prod.ext (Fin.ext h0) (Prod.ext (Fin.ext h1) (Fin.ext h2))

theorem circle_triangle_card {m : ℕ} (p : Fin m × Fin m × Fin m) : (circleTriangle p).card = 3 := by
  classical
  change ({circlePoint 0 p.1.val, circlePoint 1 p.2.1.val, circlePoint 2 p.2.2.val} : Finset E6).card = 3
  rw [Finset.card_insert_of_notMem (by simp [circle_point_eq_iff]),
    Finset.card_insert_of_notMem (by simp [circle_point_eq_iff]), Finset.card_singleton]

theorem circle_triangle_equi {m : ℕ} (p : Fin m × Fin m × Fin m) :
    IsAnySizeEquilateralTriangle (circleTriangle p) := by
  classical
  refine ⟨Real.sqrt 2, Real.sqrt_pos.mpr (by norm_num), circle_triangle_card p, ?_⟩
  intro x hx y hy hne
  simp only [circleTriangle, mem_insert, mem_singleton] at hx hy
  rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl) <;>
    first | exact False.elim (hne rfl) | exact circle_point_dist _ _ (by decide) _ _

theorem attain_bddAbove (n : ℕ) :
    BddAbove {m : ℕ | ∃ P : Finset E6, P.card = n ∧ anySizeEquilateralTriangleCount 6 P = m} := by
  refine ⟨n.choose 3, ?_⟩
  rintro _ ⟨P, hP, rfl⟩
  classical
  exact (Finset.card_filter_le _ _).trans (by simp [hP])

theorem circles_lower_bound (n : ℕ) : (n / 3) ^ 3 ≤ TAnySize 6 n := by
  classical
  let m := n / 3
  let P : Finset E6 := (Finset.univ : Finset (Fin 3 × Fin m)).map (circlePointEmbedding m)
  have hcard : P.card = 3 * m := by simp [P]
  obtain ⟨Q, hPQ, hQ⟩ := Infinite.exists_superset_card_eq P n (by rw [hcard]; dsimp [m]; omega)
  have hcount : m ^ 3 ≤ anySizeEquilateralTriangleCount 6 Q := by
    let A := (Finset.univ : Finset (Fin m × Fin m × Fin m)).image circleTriangle
    have hA : A.card = m ^ 3 := by
      rw [Finset.card_image_of_injective _ (circle_triangle_injective m)]
      simp [pow_succ, Nat.mul_assoc]
    rw [← hA]
    apply Finset.card_le_card
    intro T hT
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, circle_triangle_card p⟩,
      circle_triangle_equi p⟩
    intro x hx
    apply hPQ
    simp only [circleTriangle, mem_insert, mem_singleton] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact Finset.mem_map.mpr ⟨(0, p.1), Finset.mem_univ _, rfl⟩
    · exact Finset.mem_map.mpr ⟨(1, p.2.1), Finset.mem_univ _, rfl⟩
    · exact Finset.mem_map.mpr ⟨(2, p.2.2), Finset.mem_univ _, rfl⟩
  exact hcount.trans (le_csSup (attain_bddAbove n) ⟨Q, hQ, rfl⟩)


theorem extremal_upper {η : ℝ} (hη : 0 < η) (hsmall : η ≤ 1 / 10) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (TAnySize 6 n : ℝ) ≤
      (1 / 27 + 2 * η) * (n : ℝ) ^ 3 + B * n := by
  obtain ⟨B, hB, hb⟩ := arbitrary_points_upper hη hsmall
  refine ⟨B, hB, fun n ↦ ?_⟩
  obtain ⟨P, hP⟩ := Finset.exists_card_eq (α := E6) n
  have hne : {m : ℕ | ∃ Q : Finset E6, Q.card = n ∧ anySizeEquilateralTriangleCount 6 Q = m}.Nonempty :=
    ⟨anySizeEquilateralTriangleCount 6 P, P, hP, rfl⟩
  obtain ⟨Q, hQ, hcount⟩ := Nat.sSup_mem hne (attain_bddAbove n)
  change anySizeEquilateralTriangleCount 6 Q = TAnySize 6 n at hcount
  rw [← hcount, ← hQ]
  exact hb Q

theorem extremal_lower_polynomial {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ 3 / 27 - (n : ℝ) ^ 2 ≤ (TAnySize 6 n : ℝ) := by
  have hx : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (n : ℝ) / 3 - 1 ≤ ((n / 3 : ℕ) : ℝ) := by
    have hh : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 3 := by
      exact_mod_cast (show n ≤ 3 * (n / 3) + 3 by omega)
    linarith
  have hpow : ((n : ℝ) / 3 - 1) ^ 3 ≤ (((n / 3 : ℕ) : ℝ)) ^ 3 := by
    have : 0 ≤ (n : ℝ) / 3 - 1 := by linarith
    gcongr
  have hcast : (((n / 3 : ℕ) : ℝ)) ^ 3 ≤ (TAnySize 6 n : ℝ) := by
    exact_mod_cast circles_lower_bound n
  exact (show (n : ℝ) ^ 3 / 27 - (n : ℝ) ^ 2 ≤ ((n : ℝ) / 3 - 1) ^ 3 by
    nlinarith [sq_nonneg (n : ℝ)]).trans (hpow.trans hcast)

theorem anysize_asymptotic :
    (fun n : ℕ ↦ (TAnySize 6 n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ (1 / 27 : ℝ) * (n : ℝ) ^ 3) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  change Tendsto (fun n : ℕ ↦ (TAnySize 6 n : ℝ) / ((1 / 27 : ℝ) * (n : ℝ) ^ 3)) atTop (𝓝 1)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · have hpos : 0 < (1 - a) / 27 := by linarith
    have hto : Tendsto (fun n : ℕ ↦ (1 - a) / 27 * (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hpos tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 3, (tendsto_atTop.1 hto) 2] with n hn hxa
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (lt_div_iff₀ (by positivity)).2
    have hlower := extremal_lower_polynomial hn
    have hmul := mul_le_mul_of_nonneg_right hxa (sq_nonneg (n : ℝ))
    nlinarith [sq_pos_of_pos hn0]
  · let η : ℝ := min ((a - 1) / 108) (1 / 10)
    have hη : 0 < η := lt_min (by linarith) (by norm_num)
    have hsmall : η ≤ 1 / 10 := min_le_right _ _
    have heta : 2 * η ≤ (a - 1) / 54 := by
      linarith [min_le_left ((a - 1) / 108) (1 / 10 : ℝ)]
    obtain ⟨B, hB, hupper⟩ := extremal_upper hη hsmall
    have hp : 0 < (a - 1) / 54 := by linarith
    have ht : Tendsto (fun n : ℕ ↦ (a - 1) / 54 * (n : ℝ) ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop hp ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 1, (tendsto_atTop.1 ht) (B + 1)] with n hn hlarge
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_lt_iff₀ (by positivity)).2
    have h := mul_le_mul_of_nonneg_right heta (pow_nonneg hn0.le 3)
    have h' := mul_le_mul_of_nonneg_right hlarge hn0.le
    nlinarith only [hupper n, h, h', hn0]

end Erdos755.AnySize

theorem OMA.solution : type_of% @Erdos755.erdos_755.variants.any_size_cdl := by
  exact Erdos755.AnySize.anysize_asymptotic
