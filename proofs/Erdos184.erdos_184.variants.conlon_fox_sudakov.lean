import FormalConjectures.ErdosProblems.«184»
import Mathlib

/-!
# Cycle and edge decomposition of minimum-degree graphs

Conlon, Fox and Sudakov, *Cycle packing*, Random Structures & Algorithms 45
(2014), 608–626. https://doi.org/10.1002/rsa.20574

The sampling, routing, path-partition, and decomposition lemmas in the first
part are adapted from OpenAI Math's CycleDecomposition development at
adc7f1241b42e322a6451854ab7e4b4c146bf78a, under the Apache License, Version 2.0.
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CycleDecomposition

Here the reservoir probability decreases as D^(-1/200). The resulting
small residue is handled by a longest-cycle argument with a logarithmic
potential. A partition maximizing the sum of within-part edge counts minus a
size penalty yields large parts of positive cut density. The crossing edges
have a bounded-endpoint-load path partition. Splitting the long paths at
balanced crossing edges gives within-part endpoint pairs. Short return paths
close these into trails, which split into cycles. The remaining within-part
graphs retain positive cut density.
-/

-- SPDX-License-Identifier: Apache-2.0
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

-- Upstream module Sampling

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15

section

namespace ErdosGallai.Sampling
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

lemma exp_half_bound : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  nlinarith [exp_one_lt_d9, exp_pos (1 / 2 : ℝ)]

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

theorem bernoulli_sum_upper_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | 2 * p * s.card ≤ ∑ i ∈ s, X i ω} ≤ exp (-p * s.card / 3) := by
  have hInt : Integrable (fun ω => exp ((1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (2 * p * s.card)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(1 / 2 : ℝ) * (2 * p * s.card)) *
        exp ((s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (-p * s.card + (s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

section ProductSamples
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

noncomputable def sampleMeasure (V : Type cycleUniverse5) [Fintype V] (p : unitInterval) : Measure (V → Bool) :=
  Measure.pi (fun _ : V => bernoulliMeasure true false p)

instance sampleMeasure_probability (p : unitInterval) : IsProbabilityMeasure (sampleMeasure V p) := by
  unfold sampleMeasure
  infer_instance

def sampleVertices (ω : V → Bool) : Finset V := Finset.univ.filter (fun v => ω v = true)

def sampleIndicator (v : V) (ω : V → Bool) : ℝ := if ω v then 1 else 0

lemma sampleIndicator_measurable {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) : Measurable (sampleIndicator v) :=
  measurable_of_finite _

lemma sampleIndicator_values {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) (ω : V → Bool) :
    sampleIndicator v ω = 0 ∨ sampleIndicator v ω = 1 := by
  simp only [sampleIndicator]; split <;> simp

lemma sampleIndicator_indep {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) :
    iIndepFun (sampleIndicator (V := V)) (sampleMeasure V p) := by
  exact iIndepFun_pi (X := fun _ : V => fun b : Bool => if b then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma sampleIndicator_integral {V : Type cycleUniverse9} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (v : V) :
    ∫ ω, sampleIndicator v ω ∂sampleMeasure V p = (p : ℝ) := by
  have hl := (measurePreserving_eval (fun _ : V => bernoulliMeasure true false p) v).hasLaw
  have hi := hl.integral_comp (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  simpa [sampleMeasure, sampleIndicator, integral_bernoulliMeasure] using hi

lemma sampleIndicator_sum (S : Finset V) (ω : V → Bool) :
    (∑ v ∈ S, sampleIndicator v ω) = ((S ∩ sampleVertices ω).card : ℝ) := by
  simp only [sampleIndicator,  Finset.sum_boole]
  congr 2
  ext v
  simp [sampleVertices]

lemma sample_card_lower_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | ((S ∩ sampleVertices ω).card : ℝ) ≤ (p : ℝ) * S.card / 2} ≤
      exp (-(p : ℝ) * S.card / 8) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_lower_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_card_upper_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | 2 * (p : ℝ) * S.card ≤ ((S ∩ sampleVertices ω).card : ℝ)} ≤
      exp (-(p : ℝ) * S.card / 3) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_upper_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_miss_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} = (1 - (p : ℝ)) ^ S.card := by
  have heq : {ω | Disjoint S (sampleVertices ω)} =
      Set.univ.pi (fun v : V => if v ∈ S then {false} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.disjoint_left, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · simp only [hv, ↓reduceIte, Set.mem_singleton_iff]
        cases hi : ω v <;> simp_all
      · simp [hv]
    · intro h v hv ht
      have := h v
      simp_all
  rw [heq, Measure.real, sampleMeasure, Measure.pi_pi, ENNReal.toReal_prod]
  have hpv (v : V) :
      ((bernoulliMeasure true false p) (if v ∈ S then {false} else Set.univ)).toReal =
        if v ∈ S then 1 - (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      change (bernoulliMeasure true false p).real {false} = _
      exact bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by simp) (by simp)
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_miss_bound (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} ≤ exp (-(p : ℝ) * S.card) := by
  rw [sample_miss_probability]
  calc
    (1 - (p : ℝ)) ^ S.card ≤ exp (-(p : ℝ)) ^ S.card := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr p.property.2)
      linarith [add_one_le_exp (-(p : ℝ))]
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma sample_contains_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p) {ω | S ⊆ sampleVertices ω} = ENNReal.ofReal (p : ℝ) ^ S.card := by
  have heq : {ω | S ⊆ sampleVertices ω} =
      Set.univ.pi (fun v : V => if v ∈ S then {true} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.subset_iff, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S <;> simp_all
    · intro h v hv
      simpa [hv] using h v
  rw [heq, sampleMeasure, Measure.pi_pi]
  have hpv (v : V) :
      bernoulliMeasure true false p (if v ∈ S then {true} else Set.univ) =
        if v ∈ S then ENNReal.ofReal (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      rw [bernoulliMeasure_apply_of_mem_of_notMem p (by simp) (by simp) (by simp)]
      exact ENNReal.ofReal_coe_nnreal.symm
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_contains_real_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | S ⊆ sampleVertices ω} = (p : ℝ) ^ S.card := by
  rw [Measure.real, sample_contains_probability, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal p.property.1]

lemma sample_blocks_independent {I : Type cycleUniverse10} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepSet (fun i => {ω | S i ⊆ sampleVertices ω}) (sampleMeasure V p) := by
  classical
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro t
  have heq : (⋂ i ∈ t, {ω | S i ⊆ sampleVertices ω}) =
      {ω | t.biUnion S ⊆ sampleVertices ω} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.biUnion_subset]
  rw [heq, sample_contains_probability, Finset.card_biUnion]
  · simp_rw [sample_contains_probability]
    exact (Finset.prod_pow_eq_pow_sum t (fun i => (S i).card) _).symm
  · intro i _ j _ hij
    exact hS hij

noncomputable def blockIndicator (S : Finset V) : (V → Bool) → ℝ :=
  {ω | S ⊆ sampleVertices ω}.indicator (fun _ => 1)

lemma blockIndicator_values (S : Finset V) (ω : V → Bool) :
    blockIndicator S ω = 0 ∨ blockIndicator S ω = 1 := by
  classical
  by_cases h : S ⊆ sampleVertices ω <;> simp [blockIndicator, h]

lemma blockIndicator_integral (p : unitInterval) (S : Finset V) :
    ∫ ω, blockIndicator S ω ∂sampleMeasure V p = (p : ℝ) ^ S.card := by
  rw [blockIndicator, integral_indicator_const _ MeasurableSet.of_discrete,
    sample_contains_real_probability]
  simp

lemma sample_blocks_lower_tail {I : Type cycleUniverse11} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (d : ℕ)
    (hd : ∀ i, (S i).card = d) (t : Finset I) :
    (sampleMeasure V p).real {ω | (∑ i ∈ t, blockIndicator (S i) ω) ≤
      (p : ℝ) ^ d * t.card / 2} ≤ exp (-(p : ℝ) ^ d * t.card / 8) := by
  apply bernoulli_sum_lower_tail t (fun _ => measurable_of_finite _)
    (sample_blocks_independent p S hS).iIndepFun_indicator
    (fun i => blockIndicator_values (S i)) ((p : ℝ) ^ d) (pow_nonneg p.property.1 _)
  intro i
  change (∫ ω, blockIndicator (S i) ω ∂sampleMeasure V p) = _
  rw [blockIndicator_integral, hd]

lemma sample_weight_sum (A : Finset V) (w : V → ℝ) (ω : V → Bool) :
    (∑ v ∈ A ∩ sampleVertices ω, w v) = ∑ v ∈ A, w v * sampleIndicator v ω := by
  rw [← Finset.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro v _
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and, sampleIndicator]
  split <;> simp_all

lemma sample_weight_integral (p : unitInterval) (A : Finset V) (w : V → ℝ) :
    ∫ ω, (∑ v ∈ A ∩ sampleVertices ω, w v) ∂sampleMeasure V p =
      (p : ℝ) * ∑ v ∈ A, w v := by
  simp_rw [sample_weight_sum]
  rw [integral_finsetSum A (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul, sampleIndicator_integral]
  rw [← Finset.sum_mul, mul_comm]

lemma nonnegative_markov_quarter {Ω : Type cycleUniverse12} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hi : Integrable X μ) (hn : ∀ ω, 0 ≤ X ω) {B : ℝ} (hB : 0 < B)
    (he : ∫ ω, X ω ∂μ ≤ B) : μ.real {ω | 4 * B < X ω} ≤ 1 / 4 := by
  have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hn) hi (4 * B)
  have hm : μ.real {ω | 4 * B < X ω} ≤ μ.real {ω | 4 * B ≤ X ω} :=
    measureReal_mono (fun ω (h : 4 * B < X ω) => h.le)
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * B)]

lemma sample_weight_markov (p : unitInterval) (hp : 0 < (p : ℝ))
    (A : Finset V) (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v)
    {B : ℝ} (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B) :
    (sampleMeasure V p).real {ω | 4 * (p : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v} ≤
      1 / 4 := by
  have ht := nonnegative_markov_quarter (μ := sampleMeasure V p)
    (X := fun ω => ∑ v ∈ A ∩ sampleVertices ω, w v) Integrable.of_finite
    (fun ω => Finset.sum_nonneg (fun v hv => hw v (Finset.mem_inter.mp hv).1))
    (mul_pos hp hB) (by rw [sample_weight_integral]; exact mul_le_mul_of_nonneg_left hs hp.le)
  simpa only [mul_assoc] using ht

theorem exists_small_weighted_hitting_set {I : Type cycleUniverse13} (A : Finset V) (hA : A.Nonempty)
    (good : Finset I) (K : I → Finset V) (hKA : ∀ i ∈ good, K i ⊆ A)
    (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v) {B d : ℝ}
    (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B)
    (hd : ∀ i ∈ good, d ≤ (K i).card)
    (q : unitInterval) (hq : 0 < (q : ℝ))
    (hmiss : (good.card : ℝ) * exp (-(q : ℝ) * d) < 1 / 2) :
    ∃ S : Finset V, S ⊆ A ∧ (S.card : ℝ) ≤ 4 * (q : ℝ) * A.card ∧
      (∑ v ∈ S, w v) ≤ 4 * (q : ℝ) * B ∧ ∀ i ∈ good, ¬Disjoint (K i) S := by
  classical
  let μ := sampleMeasure V q
  let E₁ : Set (V → Bool) := {ω | 4 * (q : ℝ) * A.card < ((A ∩ sampleVertices ω).card : ℝ)}
  let E₂ : Set (V → Bool) := {ω | 4 * (q : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v}
  let E₃ : Set (V → Bool) := ⋃ i ∈ good, {ω | Disjoint (K i) (sampleVertices ω)}
  have h₁ : μ.real E₁ ≤ 1 / 4 := by
    have ht := sample_weight_markov q hq A (fun _ => (1 : ℝ)) (by simp)
      (show (0 : ℝ) < A.card by exact_mod_cast hA.card_pos) (by simp)
    simpa [μ, E₁] using ht
  have h₂ : μ.real E₂ ≤ 1 / 4 := sample_weight_markov q hq A w hw hB hs
  have h₃ : μ.real E₃ < 1 / 2 := by
    calc
      μ.real E₃ ≤ ∑ i ∈ good, μ.real {ω | Disjoint (K i) (sampleVertices ω)} :=
        measureReal_biUnion_finset_le good _
      _ ≤ ∑ i ∈ good, exp (-(q : ℝ) * d) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sample_miss_bound q (K i)).trans (exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left (hd i hi) (neg_nonpos.mpr hq.le)))
      _ = (good.card : ℝ) * exp (-(q : ℝ) * d) := by simp
      _ < _ := hmiss
  have hf : μ.real (E₁ ∪ E₂ ∪ E₃) < 1 := by
    have ha := measureReal_union_le (μ := μ) (E₁ ∪ E₂) E₃
    have hb := measureReal_union_le (μ := μ) E₁ E₂
    linarith
  have hne : E₁ ∪ E₂ ∪ E₃ ≠ Set.univ := by
    intro h
    rw [h] at hf
    have hu : μ.real Set.univ = 1 := by simp [μ, Measure.real]
    linarith
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hn := hω
  simp only [Set.mem_union, not_or] at hn
  refine ⟨A ∩ sampleVertices ω, Finset.inter_subset_left, le_of_not_gt hn.1.1,
    le_of_not_gt hn.1.2, ?_⟩
  intro i hi hdj
  apply hn.2
  simp only [E₃, Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨i, hi, ?_⟩
  apply Finset.disjoint_left.mpr
  intro v hv hvs
  exact Finset.disjoint_left.mp hdj hv (Finset.mem_inter.mpr ⟨hKA i hi hv, hvs⟩)

end ProductSamples

section FiniteUnion
variable {Ω : Type cycleUniverse14} {I : Type cycleUniverse15} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exists_avoiding_finite_events (s : Finset I) (E : I → Set Ω)
    (h : ∑ i ∈ s, μ.real (E i) < 1) : ∃ ω, ∀ i ∈ s, ω ∉ E i := by
  by_contra hn
  push Not at hn
  have cover : (⋃ i ∈ s, E i) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi, he⟩ := hn ω
    exact ⟨i, hi, he⟩
  have hu := measureReal_biUnion_finset_le (μ := μ) s E
  rw [cover] at hu
  have : μ.real Set.univ = 1 := by simp [Measure.real]
  rw [this] at hu
  linarith

end FiniteUnion
end ErdosGallai.Sampling
end

end OAI


-- Upstream module SamplingCuts

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7

section
namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory Real
open scoped symmDiff
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

noncomputable def cutColor (e : V × V) : ℕ :=
  (Fintype.equivFin V e.1).val + (Fintype.equivFin V e.2).val

lemma cutColor_lt {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (e : V × V) : cutColor e < 2 * Fintype.card V := by
  have h₁ := (Fintype.equivFin V e.1).isLt
  have h₂ := (Fintype.equivFin V e.2).isLt
  dsimp [cutColor]
  omega

lemma same_cutColor_blocks_disjoint (A B : Finset V) (hAB : Disjoint A B)
    {e f : V × V} (he₁ : e.1 ∈ A) (he₂ : e.2 ∈ B)
    (hf₁ : f.1 ∈ A) (hf₂ : f.2 ∈ B) (hc : cutColor e = cutColor f) (hef : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset V) {f.1, f.2} := by
  have h₁ : e.1 ≠ f.1 := by
    intro h
    have ht : e.2 = f.2 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext h ht)
  have h₂ : e.2 ≠ f.2 := by
    intro h
    have ht : e.1 = f.1 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext ht h)
  have h₃ : e.1 ≠ f.2 := fun h => Finset.disjoint_left.mp hAB he₁ (h ▸ hf₂)
  have h₄ : e.2 ≠ f.1 := fun h => Finset.disjoint_left.mp hAB hf₁ (h ▸ he₂)
  simp [Finset.disjoint_left, h₁, h₂, h₃, h₄]

lemma blockIndicator_sum_card (E : Finset (V × V)) (ω : V → Bool) :
    (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
  classical
  simp only [blockIndicator, Set.indicator_apply, Set.mem_ofPred_eq,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact Finset.sum_boole _ _

lemma sampled_matching_lower_tail (p : unitInterval) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B)
    (c : ℕ) (hc : ∀ e ∈ E, cutColor e = c) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) ≤
        (p : ℝ) ^ 2 * E.card / 2} ≤ exp (-(p : ℝ) ^ 2 * E.card / 8) := by
  classical
  let S : E → Finset V := fun e => {e.val.1, e.val.2}
  have hS : Pairwise fun e f : E => Disjoint (S e) (S f) := by
    intro e f hef
    exact same_cutColor_blocks_disjoint A B hAB (hE e e.property).1 (hE e e.property).2
      (hE f f.property).1 (hE f f.property).2 ((hc e e.property).trans (hc f f.property).symm)
      (fun h => hef (Subtype.ext h))
  have hd : ∀ e : E, (S e).card = 2 := by
    intro e
    apply Finset.card_pair
    intro h
    exact Finset.disjoint_left.mp hAB (hE e e.property).1 (h ▸ (hE e e.property).2)
  have ht := sample_blocks_lower_tail p S hS 2 hd Finset.univ
  have heq (ω : V → Bool) : (∑ e : E, blockIndicator (S e) ω) =
      (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) := by
    exact Finset.sum_attach E (fun e => blockIndicator ({e.1, e.2} : Finset V) ω)
  simp_rw [heq, blockIndicator_sum_card] at ht
  simpa using ht

lemma sum_cutColor_class_card (E : Finset (V × V)) :
    (∑ i ∈ Finset.range (2 * Fintype.card V), (E.filter (fun e => cutColor e = i)).card) =
      E.card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_true_of_mem
  intro e _
  exact Finset.mem_range.mpr (cutColor_lt e)

theorem sampled_bipartite_cut_lower_tail (p : unitInterval)
    (hr : 0 < Fintype.card V) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * Fintype.card V)) := by
  classical
  let r : ℝ := Fintype.card V
  have hrR : 0 < r := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast hr
  let colors := Finset.range (2 * Fintype.card V)
  let C (i : ℕ) := E.filter (fun e => cutColor e = i)
  let m (i : ℕ) : ℝ := (C i).card
  let L := colors.filter (fun i => (E.card : ℝ) / (4 * r) ≤ m i)
  let retained (i : ℕ) (ω : V → Bool) : ℝ :=
    ((C i |>.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ)
  have hsum : ∑ i ∈ colors, m i = (E.card : ℝ) := by
    dsimp [colors, m, C]
    exact_mod_cast sum_cutColor_class_card E
  have hretain (ω : V → Bool) : ∑ i ∈ colors, retained i ω =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
    have ht := sum_cutColor_class_card
      (E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω))
    simpa only [retained, C, colors, Finset.filter_filter, and_comm, Nat.cast_sum] using
      (show (∑ i ∈ Finset.range (2 * Fintype.card V),
        (((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).filter
          (fun e => cutColor e = i)).card : ℝ)) = _ by exact_mod_cast ht)
  have hlarge : (E.card : ℝ) / 2 ≤ ∑ i ∈ L, m i := by
    have hb : ∑ i ∈ colors, m i ≤
        ∑ i ∈ colors, ((if i ∈ L then m i else 0) + (E.card : ℝ) / (4 * r)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiL : i ∈ L
      · simp only [hiL, ↓reduceIte]
        have : 0 ≤ (E.card : ℝ) / (4 * r) := by positivity
        linarith
      · have hiM : m i < (E.card : ℝ) / (4 * r) := by
          simpa only [L, Finset.mem_filter, hi, true_and, not_le] using hiL
        simp only [hiL, ↓reduceIte, zero_add]
        exact hiM.le
    rw [hsum, Finset.sum_add_distrib, Finset.sum_ite_mem] at hb
    have hsub : colors ∩ L = L := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hsub] at hb
    have hconst : ∑ _i ∈ colors, (E.card : ℝ) / (4 * r) = (E.card : ℝ) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, colors, Finset.card_range, Nat.cast_mul,
        Nat.cast_ofNat]
      dsimp [r] at *
      field_simp
      ; ring
    rw [hconst] at hb
    linarith
  let Bad (i : ℕ) : Set (V → Bool) :=
    {ω | retained i ω ≤ (p : ℝ) ^ 2 * m i / 2}
  have hcover : {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ⊆ ⋃ i ∈ L, Bad i := by
    intro ω hfail
    by_contra hnot
    have hiok : ∀ i ∈ L, (p : ℝ) ^ 2 * m i / 2 ≤ retained i ω := by
      intro i hi
      have hn : ω ∉ Bad i := fun h => hnot (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨hi, h⟩⟩)
      exact (lt_of_not_ge hn).le
    have hs₁ : (p : ℝ) ^ 2 / 2 * (∑ i ∈ L, m i) ≤ ∑ i ∈ L, retained i ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = (p : ℝ) ^ 2 * m i / 2 := by ring
        _ ≤ retained i ω := hiok i hi
    have hs₂ : (∑ i ∈ L, retained i ω) ≤ ∑ i ∈ colors, retained i ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Nat.cast_nonneg _)
    rw [hretain] at hs₂
    have hs₃ := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (p : ℝ) ^ 2 / 2)
    change ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
      (p : ℝ) ^ 2 * E.card / 4 at hfail
    nlinarith
  have hbad (i : ℕ) (hi : i ∈ L) : (sampleMeasure V p).real (Bad i) ≤
      exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
    have ht := sampled_matching_lower_tail p A B hAB (C i)
      (fun e he => hE e (Finset.mem_filter.mp he).1) i
      (fun e he => (Finset.mem_filter.mp he).2)
    have hm : (E.card : ℝ) / (4 * r) ≤ m i := (Finset.mem_filter.mp hi).2
    have he : -(p : ℝ) ^ 2 * m i / 8 ≤ -(p : ℝ) ^ 2 * E.card / (32 * r) := by
      have ht := mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr (sq_nonneg (p : ℝ)))
      calc
        _ ≤ (-(p : ℝ) ^ 2 * ((E.card : ℝ) / (4 * r))) / 8 := by linarith
        _ = _ := by ring
    exact ht.trans (exp_le_exp.mpr he)
  calc
    _ ≤ (sampleMeasure V p).real (⋃ i ∈ L, Bad i) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ i ∈ L, (sampleMeasure V p).real (Bad i) := measureReal_biUnion_finset_le L Bad
    _ ≤ ∑ i ∈ L, exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := Finset.sum_le_sum hbad
    _ = (L.card : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by simp
    _ ≤ 2 * r * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      have ht := Finset.card_le_card (Finset.filter_subset (fun i => (E.card : ℝ) / (4 * r) ≤ m i) colors)
      have ht' : L.card ≤ 2 * Fintype.card V := by
        simpa only [colors, Finset.card_range] using ht
      change (L.card : ℝ) ≤ 2 * (Fintype.card V : ℝ)
      exact_mod_cast ht'

def neighborsIn (P : SimpleGraph V) [DecidableRel P.Adj] (v : V) (A : Finset V) :=
  A.filter (P.Adj v)

lemma card_interedges_eq_sum_neighborsIn {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) : (P.interedges A B).card = ∑ v ∈ A, (neighborsIn P v B).card := by
  simp only [SimpleGraph.interedges, Rel.interedges, neighborsIn, Finset.card_filter]
  rw [Finset.sum_product]

lemma neighborsIn_partition_card {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (v : V) (A W : Finset V) (hAW : A ⊆ W) :
    (neighborsIn P v W).card = (neighborsIn P v A).card + (neighborsIn P v (W \ A)).card := by
  have hu : neighborsIn P v W = neighborsIn P v A ∪ neighborsIn P v (W \ A) := by
    ext x; simp only [neighborsIn, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro ⟨hx, ha⟩
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, ha⟩
      · exact Or.inr ⟨⟨hx, hxA⟩, ha⟩
    · rintro (⟨hx, ha⟩ | ⟨⟨hx, _⟩, ha⟩)
      · exact ⟨hAW hx, ha⟩
      · exact ⟨hx, ha⟩
  rw [hu, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).1

lemma interedges_sym2_injective {V : Type cycleUniverse5} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) (hAB : Disjoint A B) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges A B : Set (V × V)) := by
  intro e he f hf hef
  rcases Sym2.mk_eq_mk_iff.mp hef with h | h
  · exact h
  · exact False.elim <| Finset.disjoint_left.mp hAB (P.mem_interedges_iff.mp he).1
      ((congrArg Prod.fst h).symm ▸ (P.mem_interedges_iff.mp hf).2.1)

lemma cut_perturbation_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A T : Finset V) (_hAW : A ⊆ W) (_hTW : T ⊆ W) :
    (P.interedges T (W \ T)).card ≤ (P.interedges A (W \ A)).card +
      Fintype.card V * (A ∆ T).card := by
  classical
  let f := fun e : V × V => s(e.1, e.2)
  let E := (P.interedges A (W \ A)).image f
  let D := (((A ∆ T) ×ˢ (Finset.univ : Finset V)).image f)
  have hinj := interedges_sym2_injective P T (W \ T) (Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx))
  have hsub : (P.interedges T (W \ T)).image f ⊆ E ∪ D := by
    intro e he
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
    rcases P.mem_interedges_iff.mp hxy with ⟨hxT, hyWT, hxy⟩
    obtain ⟨hyW, hyT⟩ := Finset.mem_sdiff.mp hyWT
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(y,x), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · exact Finset.mem_symmDiff.mpr (Or.inl ⟨hyA, hyT⟩)
        · exact Sym2.eq_swap
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(x,y), P.mem_interedges_iff.mpr
          ⟨hxA, Finset.mem_sdiff.mpr ⟨hyW, hyA⟩, hxy⟩, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr
        ⟨Finset.mem_symmDiff.mpr (Or.inr ⟨hxT, hxA⟩), Finset.mem_univ _⟩, rfl⟩
  calc
    _ = ((P.interedges T (W \ T)).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (E ∪ D).card := Finset.card_le_card hsub
    _ ≤ E.card + D.card := Finset.card_union_le _ _
    _ ≤ (P.interedges A (W \ A)).card + (((A ∆ T) ×ˢ (Finset.univ : Finset V))).card :=
      Nat.add_le_add (Finset.card_image_le) Finset.card_image_le
    _ = _ := by simp [mul_comm]

lemma card_le_add_symmDiff {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (A T : Finset V) : A.card ≤ T.card + (A ∆ T).card := by
  have hs : A ⊆ T ∪ (A ∆ T) := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_left _ hxT
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inl ⟨hx,hxT⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma sdiff_card_le_add_symmDiff {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W A T : Finset V) :
    (W \ A).card ≤ (W \ T).card + (A ∆ T).card := by
  have hs : W \ A ⊆ (W \ T) ∪ (A ∆ T) := by
    intro x hx
    obtain ⟨hxW,hxA⟩ := Finset.mem_sdiff.mp hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hxT,hxA⟩))
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxW,hxT⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma cut_card_lower_of_neighbors (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B Q : Finset V) (hQA : Q ⊆ A) (c : ℝ)
    (hc : ∀ v ∈ Q, c ≤ (neighborsIn P v B).card) :
    c * Q.card ≤ ((P.interedges A B).card : ℝ) := by
  rw [card_interedges_eq_sum_neighborsIn, Nat.cast_sum]
  calc
    _ = ∑ v ∈ Q, c := by simp [mul_comm]
    _ ≤ ∑ v ∈ Q, ((neighborsIn P v B).card : ℝ) := Finset.sum_le_sum hc
    _ ≤ ∑ v ∈ A, ((neighborsIn P v B).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hQA (fun _ _ _ => Nat.cast_nonneg _)

lemma bad_sampled_cut_size_and_exceptional (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (_ha : 0 < (A.card : ℝ))
    {p h τ : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ : τ < p*h/4)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧
      ((A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))).card : ℝ) ≤
        4*τ*A.card/(p*h) := by
  have hpart (v : V) : ((neighborsIn P v W).card : ℝ) =
      ((neighborsIn P v A).card : ℝ) + ((neighborsIn P v (W \ A)).card : ℝ) := by
    exact_mod_cast neighborsIn_partition_card P v A W hAW
  constructor
  · by_contra hn
    have ha' : (A.card : ℝ) ≤ p*h/4 := le_of_not_gt hn
    have hlo : p*h/4 * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) A (Finset.Subset.refl _) (p*h/4)
      intro v _
      have hc : ((neighborsIn P v A).card : ℝ) ≤ A.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (P.Adj v) A)
      have hd := hdeg v
      have he := hpart v
      linarith
    nlinarith
  · let Q := A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
    have hl : p*h/4 * Q.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) Q Finset.sdiff_subset (p*h/4)
      intro v hv
      obtain ⟨hvA,hvG⟩ := Finset.mem_sdiff.mp hv
      have hn : ((neighborsIn P v A).card : ℝ) < p*h/4 := by
        simpa only [Finset.mem_filter, hvA, true_and, not_le] using hvG
      have hd := hdeg v
      have he := hpart v
      linarith
    change (Q.card : ℝ) ≤ _
    apply (le_div_iff₀ (mul_pos hp hh)).mpr
    nlinarith

def neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj] (S : Finset V) : Finset V :=
  S.biUnion (fun v => neighborsIn P v Finset.univ)

lemma neighborhoodUnion_leakage (P : SimpleGraph V) [DecidableRel P.Adj]
    (S W A : Finset V) :
    (((neighborhoodUnion P S ∩ W) \ A).card : ℝ) ≤
      ∑ v ∈ S, ((neighborsIn P v (W \ A)).card : ℝ) := by
  have heq : (neighborhoodUnion P S ∩ W) \ A =
      S.biUnion (fun v => neighborsIn P v (W \ A)) := by
    ext x
    simp only [neighborhoodUnion, neighborsIn, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [heq]
  exact_mod_cast Finset.card_biUnion_le

lemma hitting_neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj]
    (good S A : Finset V) (hhit : ∀ v ∈ good, ¬Disjoint (neighborsIn P v A) S) :
    good ⊆ neighborhoodUnion P S := by
  intro v hv
  obtain ⟨x,hxK,hxS⟩ := Finset.not_disjoint_iff.mp (hhit v hv)
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hxS,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.adj_symm (Finset.mem_filter.mp hxK).2⟩

theorem exists_approximating_witness (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (ha : 0 < (A.card : ℝ))
    {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧ ∃ S : Finset V, S ⊆ A ∧
      (S.card : ℝ) ≤ 4 * A.card * M / h ∧
      ((A ∆ (neighborhoodUnion P S ∩ W)).card : ℝ) ≤
        (4*τ/(p*h) + 4*τ*M/h) * A.card := by
  classical
  obtain ⟨hlarge, hexc⟩ := bad_sampled_cut_size_and_exceptional P W A hAW ha hp hh hτ hdeg hbad
  refine ⟨hlarge, ?_⟩
  let good := A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
  let w : V → ℝ := fun v => ((neighborsIn P v (W \ A)).card : ℝ)
  let q : unitInterval := ⟨M/h, div_nonneg hM.le hh.le, (div_le_one hh).mpr hMh⟩
  have hq : 0 < (q : ℝ) := div_pos hM hh
  have hm : (good.card : ℝ) * exp (-(q : ℝ) * (p*h/4)) < 1/2 := by
    have heq : -(q : ℝ) * (p*h/4) = -p*M/4 := by
      dsimp [q]
      field_simp [hh.ne']
    rw [heq]
    have hg : (good.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ good
    exact (mul_le_mul_of_nonneg_right hg (exp_pos _).le).trans_lt hmiss
  have hsum : ∑ v ∈ A, w v ≤ τ * A.card := by
    dsimp [w]
    rw [← Nat.cast_sum, ← card_interedges_eq_sum_neighborsIn]
    exact hbad.le
  obtain ⟨S,hSA,hSc,hSw,hSh⟩ := exists_small_weighted_hitting_set A
    (Finset.card_pos.mp (by exact_mod_cast ha)) good (fun v => neighborsIn P v A)
    (fun v _ => Finset.filter_subset _ _) w (fun _ _ => Nat.cast_nonneg _)
    (mul_pos hτ0 ha) hsum
    (fun v hv => (Finset.mem_filter.mp hv).2) q hq hm
  refine ⟨S,hSA,?_,?_⟩
  · convert hSc using 1 ; dsimp [q] ; ring
  · let T := neighborhoodUnion P S ∩ W
    have hgood : good ⊆ neighborhoodUnion P S := hitting_neighborhoodUnion P good S A hSh
    have hsub : A ∆ T ⊆ (A \ good) ∪ (T \ A) := by
      intro v hv
      rcases Finset.mem_symmDiff.mp hv with ⟨hvA,hvT⟩ | ⟨hvT,hvA⟩
      · apply Finset.mem_union_left
        apply Finset.mem_sdiff.mpr
        refine ⟨hvA,?_⟩
        intro hvG
        exact hvT (Finset.mem_inter.mpr ⟨hgood hvG, hAW hvA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvT,hvA⟩)
    have hδ : ((A ∆ T).card : ℝ) ≤ ((A \ good).card : ℝ) + ((T \ A).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hleak : ((T \ A).card : ℝ) ≤ 4*(q : ℝ)*(τ*A.card) :=
      (neighborhoodUnion_leakage P S W A).trans hSw
    change ((A ∆ T).card : ℝ) ≤ _
    change ((A \ good).card : ℝ) ≤ _ at hexc
    calc
      _ ≤ 4*τ*A.card/(p*h) + 4*(q : ℝ)*(τ*A.card) := add_le_add hexc hleak |>.trans' hδ
      _ = _ := by dsimp [q]; ring

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

theorem cutExpansionOn_of_witnesses (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hε : 4*τ/(p*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/(p*h) + 4*τ*M/h) ≤ p^2*h/8)
    (hexp : CutExpansion P h)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hwitness : ∀ S : Finset V, (S.card : ℝ) ≤ 4*Fintype.card V*M/h →
      let U := neighborhoodUnion P S
      p*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) →
      (p^2/4) * ((P.interedges U Uᶜ).card : ℝ) ≤
        ((P.interedges (U ∩ W) (W \ (U ∩ W))).card : ℝ)) :
    CutExpansionOn P W τ := by
  classical
  have hsmall (A : Finset V) (hAW : A ⊆ W)
      (hsize : (A.card : ℝ) ≤ (W \ A).card) :
      τ * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
    by_contra hn
    have hbad := lt_of_not_ge hn
    have ha : 0 < (A.card : ℝ) := by
      by_contra hn
      have hz : (A.card : ℝ) = 0 := (le_of_not_gt hn).antisymm (Nat.cast_nonneg _)
      rw [hz, mul_zero] at hbad
      exact (Nat.cast_nonneg _).not_gt hbad
    obtain ⟨hlarge,S,hSA,hSc,hδ⟩ := exists_approximating_witness P W A hAW ha
      hp hh hτ0 hτ hM hMh hmiss hdeg hbad
    let U := neighborhoodUnion P S
    let T := U ∩ W
    let δ : ℝ := (A ∆ T).card
    have hδ' : δ ≤ (A.card : ℝ)/2 := by
      have ht := mul_le_mul_of_nonneg_right hε ha.le
      dsimp [δ,T,U]
      linarith
    have hmin : (A.card : ℝ)/2 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) := by
      apply le_min
      · have ht : (A.card : ℝ) ≤ (T.card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast card_le_add_symmDiff A T
        have hTU : (T.card : ℝ) ≤ U.card := by
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : T ⊆ U)
        linarith
      · have ht : ((W \ A).card : ℝ) ≤ ((W \ T).card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast sdiff_card_le_add_symmDiff W A T
        have hs : W \ T ⊆ Uᶜ := by
          intro v hv
          obtain ⟨hvW,hvT⟩ := Finset.mem_sdiff.mp hv
          apply Finset.mem_compl.mpr
          intro hvU
          exact hvT (Finset.mem_inter.mpr ⟨hvU,hvW⟩)
        have hh' : ((W \ T).card : ℝ) ≤ Uᶜ.card := by exact_mod_cast Finset.card_le_card hs
        linarith
    have hsbound : (S.card : ℝ) ≤ 4*Fintype.card V*M/h := by
      apply hSc.trans
      have hac : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ A
      gcongr
    have hw := hwitness S hsbound (by dsimp [U] at hmin; linarith)
    have he := hexp U
    have hlo : p^2*h*A.card/8 ≤ ((P.interedges T (W \ T)).card : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hmin hh.le
      have ht := mul_le_mul_of_nonneg_left (hm.trans he) (by positivity : 0 ≤ p^2/4)
      change p^2/4 * ((P.interedges U Uᶜ).card : ℝ) ≤ _ at hw
      nlinarith
    have hupper : ((P.interedges T (W \ T)).card : ℝ) ≤
        ((P.interedges A (W \ A)).card : ℝ) + Fintype.card V * δ := by
      dsimp [δ]
      exact_mod_cast cut_perturbation_card P W A T hAW Finset.inter_subset_right
    have hd := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ (Fintype.card V : ℝ))
    have hp' := mul_le_mul_of_nonneg_right hperturb ha.le
    change (Fintype.card V : ℝ) * δ ≤ _ at hd
    nlinarith
  intro A hAW
  by_cases hs : (A.card : ℝ) ≤ (W \ A).card
  · rw [min_eq_left hs]
    exact hsmall A hAW hs
  · have hs' : ((W \ A).card : ℝ) ≤ A.card := (lt_of_not_ge hs).le
    rw [min_eq_right hs']
    have heq : W \ (W \ A) = A := Finset.sdiff_sdiff_eq_self hAW
    have ht := hsmall (W \ A) Finset.sdiff_subset (by simpa only [heq] using hs')
    rw [heq] at ht
    let : Std.Symm P.Adj := P.symm
    have hcomm : (P.interedges (W \ A) A).card = (P.interedges A (W \ A)).card :=
      Rel.card_interedges_comm (W \ A) A
    rwa [hcomm] at ht

lemma cutExpansion_minDegree (P : SimpleGraph V) [DecidableRel P.Adj]
    {h : ℝ} (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) (v : V) :
    h ≤ ((neighborsIn P v Finset.univ).card : ℝ) := by
  have ht := hexp {v}
  have hc : (1 : ℝ) ≤ ((({v} : Finset V)ᶜ).card : ℝ) := by
    have : 1 ≤ (({v} : Finset V)ᶜ).card := by
      rw [Finset.card_compl, Finset.card_singleton]
      omega
    exact_mod_cast this
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hc, mul_one] at ht
  rw [card_interedges_eq_sum_neighborsIn, Finset.sum_singleton] at ht
  have heq : neighborsIn P v ({v} : Finset V)ᶜ = neighborsIn P v Finset.univ := by
    ext x
    simp only [neighborsIn, Finset.mem_filter, Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun he => P.irrefl (he ▸ h), h⟩⟩
  rwa [heq] at ht

lemma sample_neighbors_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hdeg : ∀ v, h ≤ ((neighborsIn P v Finset.univ).card : ℝ))
    (v : V) :
    (sampleMeasure V p).real {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2} ≤
      exp (-(p : ℝ)*h/8) := by
  have heq (ω : V → Bool) : neighborsIn P v (sampleVertices ω) =
      neighborsIn P v Finset.univ ∩ sampleVertices ω := by
    ext x; simp [neighborsIn, and_comm]
  simp_rw [heq]
  have hs : {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2} ⊆
      {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) ≤
        (p : ℝ)*(neighborsIn P v Finset.univ).card/2} := by
    intro ω hω
    change (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2 at hω
    exact hω.le.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hdeg v) p.property.1) (by norm_num))
  have he : -(p : ℝ)*(neighborsIn P v Finset.univ).card/8 ≤ -(p : ℝ)*h/8 := by
    have ht := mul_le_mul_of_nonneg_left (hdeg v) p.property.1
    linarith
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((sample_card_lower_tail p _).trans (exp_le_exp.mpr he))

lemma card_small_subsets_le (s : ℕ) (hr : 0 < Fintype.card V) :
    (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)).card ≤
      (s+1) * Fintype.card V ^ s := by
  classical
  have heq : (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)) =
      (Finset.range (s+1)).biUnion (fun t => (Finset.univ : Finset V).powersetCard t) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨S.card, by omega, rfl⟩,
      fun ⟨t,ht,he⟩ => by omega⟩
  rw [heq]
  calc
    _ ≤ ∑ t ∈ Finset.range (s+1), ((Finset.univ : Finset V).powersetCard t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.range (s+1), Fintype.card V ^ s := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hr (by simpa using ht))
    _ = _ := by simp [mul_comm]

def witnessFamily (P : SimpleGraph V) [DecidableRel P.Adj] (s : ℕ) : Finset (Finset V) :=
  ((((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s))).image (neighborhoodUnion P)

lemma card_witnessFamily_le (P : SimpleGraph V) [DecidableRel P.Adj]
    (s : ℕ) (hr : 0 < Fintype.card V) :
    (witnessFamily P s).card ≤ (s+1) * Fintype.card V ^ s :=
  Finset.card_image_le.trans (card_small_subsets_le s hr)

lemma sampled_witness_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) (hexp : CutExpansion P h)
    (hr : 0 < Fintype.card V) (U : Finset V)
    (hU : (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ)) :
    (sampleMeasure V p).real {ω |
      ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
        (p : ℝ)^2/4 * (P.interedges U Uᶜ).card} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  have hAB : Disjoint U Uᶜ := Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_compl.mp hy) hx)
  have heq (ω : V → Bool) :
      P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω)) =
        (P.interedges U Uᶜ).filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω) := by
    ext ⟨x,y⟩
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_compl]
    aesop
  have ht := sampled_bipartite_cut_lower_tail p hr U Uᶜ hAB (P.interedges U Uᶜ)
    (fun e he => ⟨(P.mem_interedges_iff.mp he).1, (P.mem_interedges_iff.mp he).2.1⟩)
  have hl : (p : ℝ)*h^2/8 ≤ ((P.interedges U Uᶜ).card : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hU hh
    have hu := hexp U
    nlinarith
  have he : -(p : ℝ)^2 * (P.interedges U Uᶜ).card/(32*Fintype.card V) ≤
      -(p : ℝ)^3*h^2/(256*Fintype.card V) := by
    have hrR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hs := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (p : ℝ)^2)
    nlinarith
  simp_rw [heq]
  have hc : (p : ℝ)^2/4 * (P.interedges U Uᶜ).card = (p : ℝ)^2 * (P.interedges U Uᶜ).card/4 := by ring
  rw [hc]
  exact ht.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by positivity))

def SampleGood (P : SimpleGraph V) [DecidableRel P.Adj] (p h τ : ℝ) (ω : V → Bool) : Prop :=
  ((sampleVertices ω).card : ℝ) ≤ 2*p*Fintype.card V ∧
    (∀ v, p*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ)) ∧
    CutExpansionOn P (sampleVertices ω) τ

theorem vertex_sampling_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h τ M : ℝ} (hp : 0 < (p : ℝ)) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < (p : ℝ)*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hr : 2 ≤ Fintype.card V)
    (hmiss : (Fintype.card V : ℝ) * exp (-(p : ℝ)*M/4) < 1/2)
    (hε : 4*τ/((p : ℝ)*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/((p : ℝ)*h) + 4*τ*M/h) ≤ (p : ℝ)^2*h/8)
    (hexp : CutExpansion P h) :
    (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) h τ ω} ≤
      exp (-(p : ℝ)*Fintype.card V/3) +
      Fintype.card V * exp (-(p : ℝ)*h/8) +
      2*Fintype.card V * ((⌈4*Fintype.card V*M/h⌉₊+1 : ℕ) : ℝ) *
        (Fintype.card V : ℝ)^⌈4*Fintype.card V*M/h⌉₊ *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  classical
  let μ := sampleMeasure V p
  let s := ⌈4*(Fintype.card V : ℝ)*M/h⌉₊
  let large := (witnessFamily P s).filter
    (fun U => (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ))
  let B₀ : Set (V → Bool) := {ω | 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ)}
  let B₁ (v : V) : Set (V → Bool) :=
    {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2}
  let B₂ (U : Finset V) : Set (V → Bool) := {ω |
    ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
      (p : ℝ)^2/4 * (P.interedges U Uᶜ).card}
  have h₀ : μ.real B₀ ≤ exp (-(p : ℝ)*Fintype.card V/3) := by
    have hs : B₀ ⊆ {ω | 2*(p : ℝ)*Fintype.card V ≤ ((sampleVertices ω).card : ℝ)} := by
      intro ω hω
      change 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ) at hω
      exact hω.le
    have ht := sample_card_upper_tail p (Finset.univ : Finset V)
    simp only [Finset.card_univ, Finset.univ_inter] at ht
    exact (measureReal_mono hs (measure_ne_top _ _)).trans ht
  have h₁ : μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) ≤
      Fintype.card V * exp (-(p : ℝ)*h/8) := by
    calc
      _ ≤ ∑ v : V, μ.real (B₁ v) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _v : V, exp (-(p : ℝ)*h/8) := Finset.sum_le_sum (fun v _ =>
        sample_neighbors_lower_tail P p (cutExpansion_minDegree P hexp hr) v)
      _ = _ := by simp
  have h₂ : μ.real (⋃ U ∈ large, B₂ U) ≤
      2*Fintype.card V * ((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
    calc
      _ ≤ ∑ U ∈ large, μ.real (B₂ U) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _U ∈ large, 2*(Fintype.card V : ℝ)*exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
        apply Finset.sum_le_sum
        intro U hU
        exact sampled_witness_cut_lower_tail P p hh.le hexp (by omega) U (Finset.mem_filter.mp hU).2
      _ = (large.card : ℝ) * (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by simp
      _ ≤ (((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s) *
          (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have ht : large.card ≤ (s+1)*Fintype.card V^s :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans
            (card_witnessFamily_le P s (by omega))
        exact_mod_cast ht
      _ = _ := by ring
  have hcover : {ω | ¬SampleGood P (p : ℝ) h τ ω} ⊆
      (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U) := by
    intro ω hω
    by_contra hn
    have hn₀ : ω ∉ B₀ := fun h => hn (Or.inl (Or.inl h))
    have hn₁ (v : V) : ω ∉ B₁ v := fun h => hn (Or.inl (Or.inr
      (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, h⟩⟩)))
    have hn₂ (U : Finset V) (hU : U ∈ large) : ω ∉ B₂ U := fun h => hn (Or.inr
      (Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨hU,h⟩⟩))
    apply hω
    have hd (v : V) : (p : ℝ)*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ) :=
      le_of_not_gt (hn₁ v)
    refine ⟨le_of_not_gt hn₀, hd, ?_⟩
    apply cutExpansionOn_of_witnesses P (sampleVertices ω) hp hh hτ0 hτ hM hMh
      hmiss hε hperturb hexp hd
    intro S hS
    dsimp only
    intro hU
    let U := neighborhoodUnion P S
    have hSc : S.card ≤ s := by
      have ht := hS.trans (Nat.le_ceil (4*(Fintype.card V : ℝ)*M/h))
      dsimp [s]
      exact_mod_cast ht
    have hmem : U ∈ large := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hU⟩
      apply Finset.mem_image.mpr
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hSc⟩, rfl⟩
    exact le_of_not_gt (hn₂ U hmem)
  calc
    _ ≤ μ.real ((B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U)) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ.real (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) + μ.real (⋃ U ∈ large, B₂ U) :=
      measureReal_union_le _ _
    _ ≤ μ.real B₀ + μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) + μ.real (⋃ U ∈ large, B₂ U) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add h₀ h₁) h₂

end ErdosGallai.Sampling

end

end OAI


-- Upstream module ReservoirSampling

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
namespace ErdosGallai.Sampling

lemma eventually_monomial_lt (K c a b : ℝ) (hc : 0 < c) (hab : a < b) :
    ∀ᶠ D : ℝ in atTop, K * D^a < c * D^b := by
  have ht : Tendsto (fun D : ℝ => K * D^(a-b)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul K
    simpa only [neg_sub, mul_zero] using hh
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_lt_const hc] with D hD htD
  have hb : 0 < D^b := Real.rpow_pos_of_pos hD b
  have heq : D^a = D^(a-b) * D^b := by rw [← Real.rpow_add hD]; congr 1; ring
  rw [heq, ← mul_assoc]
  exact mul_lt_mul_of_pos_right htD hb

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

lemma eventually_log_le_small_power : ∀ᶠ D : ℝ in atTop, log D ≤ D^(1/10 : ℝ) := by
  filter_upwards [(isLittleO_log_rpow_atTop (show (0 : ℝ) < 1/10 by norm_num)).eventuallyLE,
    eventually_ge_atTop (1 : ℝ)] with D hD h1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] using hD

def samplingScaleError (c p D : ℝ) : ℝ :=
  exp (-p/3 * D^(9/10 : ℝ)) +
    D^(51/50 : ℝ) * exp (-(p*c/8) * D^(9/10 : ℝ)) +
    (2*(4/c+2)) * (D^(23/20 : ℝ) * exp (-(p^3*c^2/512) * D^(39/50 : ℝ)))

lemma samplingScaleError_tendsto (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    Tendsto (samplingScaleError c p) atTop (𝓝 0) := by
  have h0 := tendsto_monomial_exp_neg_power 0 (9/10) (p/3) (by norm_num) (by positivity)
  have h1 := tendsto_monomial_exp_neg_power (51/50) (9/10) (p*c/8) (by norm_num) (by positivity)
  have h2 := (tendsto_monomial_exp_neg_power (23/20) (39/50) (p^3*c^2/512)
    (by norm_num) (by positivity)).const_mul (2*(4/c+2))
  unfold samplingScaleError
  simpa [neg_div, Real.rpow_zero] using (h0.add h1).add h2

def SamplingScaleReady (c p D : ℝ) (r : ℕ) : Prop :=
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  2 ≤ r ∧ τ < p*h/4 ∧ M ≤ h ∧ (r : ℝ)*exp (-p*M/4) < 1/2 ∧
    4*τ/(p*h)+4*τ*M/h ≤ 1/2 ∧
    τ+r*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8 ∧
    exp (-p*r/3) + r*exp (-p*h/8) +
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) * (r : ℝ)^⌈4*r*M/h⌉₊ *
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D

lemma sampling_witness_error_le (c p D : ℝ) (r : ℕ) (hc : 0 < c) (hp : 0 < p)
    (hD : 1 ≤ D) (hrpos : 0 < (r : ℝ)) (hrhi : (r : ℝ) ≤ D^(51/50 : ℝ))
    (hlog : log D ≤ D^(1/10 : ℝ))
    (hcost : ((51/50)*(4/c+2))*D^(23/100 : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ)) :
    let h := c*D^(9/10 : ℝ)
    let M := D^(1/100 : ℝ)
    2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤
      (2*(4/c+2))*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
  let h := c*D^(9/10 : ℝ)
  let M := D^(1/100 : ℝ)
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hDpos : 0 < D := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have hrNat : 0 < r := by exact_mod_cast hrpos
  have hs : ((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤ K*D^(13/100 : ℝ) := by
    have hnorm : 4*D^(51/50 : ℝ)*M/h = (4/c)*D^(13/100 : ℝ) := by
      dsimp [M,h]
      rw [show (13/100 : ℝ) = (51/50+1/100)-9/10 by norm_num,
        Real.rpow_sub hDpos, Real.rpow_add hDpos]
      field_simp
    calc
      _ ≤ 4*r*M/h+2 := by
        have hs := (Nat.ceil_lt_add_one (show 0 ≤ 4*(r : ℝ)*M/h by positivity)).le
        push_cast
        linarith
      _ ≤ 4*D^(51/50 : ℝ)*M/h+2 := by gcongr
      _ = (4/c)*D^(13/100 : ℝ)+2 := by rw [hnorm]
      _ ≤ K*D^(13/100 : ℝ) := by
        have hd := Real.one_le_rpow hD (show (0 : ℝ) ≤ 13/100 by norm_num)
        dsimp [K]
        nlinarith
  have hln : log (r : ℝ) ≤ (51/50)*log D := by
    simpa only [Real.log_rpow hDpos] using Real.log_le_log hrpos hrhi
  have hecost : (⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ) := by
    have hs' : (⌈4*r*M/h⌉₊ : ℝ) ≤ K*D^(13/100 : ℝ) := by push_cast at hs; linarith
    calc
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*log D) := by
        apply mul_le_mul hs' hln
        · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
        · positivity
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*D^(1/10 : ℝ)) := by gcongr
      _ = ((51/50)*K)*D^(23/100 : ℝ) := by
        have he := Real.rpow_add hDpos (13/100 : ℝ) (1/10)
        norm_num at he
        rw [he]
        ring
      _ ≤ _ := hcost
  have hratio : c^2*D^(39/50 : ℝ) ≤ h^2/(r : ℝ) := by
    have he : c^2*D^(39/50 : ℝ) = h^2/D^(51/50 : ℝ) := by
      dsimp [h]
      rw [show (39/50 : ℝ) = (9/10)*2-51/50 by norm_num,
        Real.rpow_sub hDpos]
      have he2 := Real.rpow_mul_natCast hDpos.le (9/10 : ℝ) 2
      norm_num only [Nat.cast_ofNat] at he2
      rw [show (9/10 : ℝ)*2=9/5 by norm_num, he2]
      ring
    rw [he]
    exact div_le_div_of_nonneg_left (sq_nonneg h) hrpos hrhi
  have hexpcost : exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) - p^3*h^2/(256*r)) ≤
      exp (-(p^3*c^2/512)*D^(39/50 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left hratio (show 0 ≤ p^3/256 by positivity)
    have hid : (p^3/256)*(h^2/(r : ℝ)) =p^3*h^2/(256*r) := by ring
    rw [hid] at hn
    nlinarith
  have hpoly : 2*(r : ℝ)*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤
      2*K*D^(23/20 : ℝ) := by
    calc
      _ ≤ 2*D^(51/50 : ℝ)*(K*D^(13/100 : ℝ)) := by gcongr
      _ = _ := by
        have he := Real.rpow_add hDpos (51/50 : ℝ) (13/100)
        norm_num at he
        rw [he]
        ring
  have hwitness : 2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
      exp (-p^3*h^2/(256*r)) ≤
      (2*K)*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
    have heq : (r : ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r)) =
        exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ)-p^3*h^2/(256*r)) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hrpos]
      simp only [neg_mul,  Real.exp_neg, div_eq_mul_inv]
    rw [mul_assoc (2*(r : ℝ)*_) _ _, heq]
    exact (mul_le_mul hpoly hexpcost (exp_pos _).le (by positivity)).trans_eq (by ring)
  exact hwitness

lemma eventually_samplingScaleReady (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℕ,
      D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) → SamplingScaleReady c p D r := by
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hmiss : Tendsto (fun D : ℝ => D^(51/50 : ℝ) * exp (-p/4*D^(1/100 : ℝ)))
      atTop (𝓝 0) := by
    convert tendsto_monomial_exp_neg_power (51/50) (1/100) (p/4)
      (by norm_num) (by positivity) using 1 ; simp [neg_div]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 9/10 by norm_num)).eventually_ge_atTop 2,
    eventually_monomial_lt 1 (p*c/4) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt 1 c (1/100) (9/10) hc (by norm_num),
    hmiss.eventually_lt_const (show (0 : ℝ) < 1/2 by norm_num),
    eventually_monomial_lt (4/(p*c)) (1/4) (-4/25) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt (4/c) (1/4) (-3/20) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt 1 (p^2*c/24) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/(p*c)) (p^2*c/24) (43/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/c) (p^2*c/24) (87/100) (9/10) (by positivity) (by norm_num),
    eventually_log_le_small_power,
    eventually_monomial_lt ((51/50)*K) (p^3*c^2/512) (23/100) (39/50)
      (by positivity) (by norm_num)] with D hD h2 hτ hM hm hε₁ hε₂ ht₀ ht₁ ht₂ hlog hcost
  intro r hrlo hrhi
  have hDpos : 0 < D := by linarith
  have hr2 : 2 ≤ r := by exact_mod_cast h2.trans hrlo
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hDpos _
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have he₁ : 4*τ/(p*h) = (4/(p*c))*D^(-4/25 : ℝ) := by
    dsimp [τ,h]
    rw [show (-4/25 : ℝ) =37/50-9/10 by norm_num, Real.rpow_sub hDpos]
    field_simp
  have he₂ : 4*τ*M/h = (4/c)*D^(-3/20 : ℝ) := by
    dsimp [τ,M,h]
    rw [show (-3/20 : ℝ) =(37/50+1/100)-9/10 by norm_num,
      Real.rpow_sub hDpos, Real.rpow_add hDpos]
    field_simp
  have hm₁ : D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)) =
      (4/(p*c))*D^(43/50 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  have hm₂ : D^(51/50 : ℝ)*((4/c)*D^(-3/20 : ℝ)) =
      (4/c)*D^(87/100 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  refine ⟨hr2, ?_, (by simpa only [one_mul] using hM.le), ?_, ?_, ?_, ?_⟩
  · change τ < p*h/4
    dsimp [τ,h]
    simpa only [one_mul, div_mul_eq_mul_div, mul_assoc] using hτ
  · change (r : ℝ)*exp (-p*M/4) < 1/2
    calc
      _ ≤ D^(51/50 : ℝ)*exp (-p*M/4) := mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
      _ < _ := by simpa [M, div_mul_eq_mul_div] using hm
  · change 4*τ/(p*h)+4*τ*M/h ≤ 1/2
    rw [he₁, he₂]
    simp only [Real.rpow_zero, mul_one] at hε₁ hε₂
    linarith
  · change τ+(r : ℝ)*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8
    rw [he₁,he₂]
    have ht : (r : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) ≤
        (4/(p*c))*D^(43/50 : ℝ)+(4/c)*D^(87/100 : ℝ) := by
      calc
        _ ≤ D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hrhi; positivity
        _ = _ := by rw [mul_add, hm₁, hm₂]
    dsimp [τ,h]
    nlinarith
  · change exp (-p*r/3)+r*exp (-p*h/8)+
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D
    have hwitness := sampling_witness_error_le c p D r hc hp hD hrpos hrhi hlog hcost.le
    have hsize : exp (-p*r/3) ≤ exp (-p/3*D^(9/10 : ℝ)) := by
      apply exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hrlo hp.le
      nlinarith
    have hdegree : (r : ℝ)*exp (-p*h/8) ≤
        D^(51/50 : ℝ)*exp (-(p*c/8)*D^(9/10 : ℝ)) := by
      have heq : -p*h/8=-(p*c/8)*D^(9/10 : ℝ) := by dsimp [h]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
    exact add_le_add (add_le_add hsize hdegree) hwitness

end ErdosGallai.Sampling

namespace ErdosGallai

open Filter Asymptotics Real
open scoped Topology
noncomputable section

def thinning (D : ℝ) : ℝ := D ^ (-(1 / 200) : ℝ)

lemma thinning_pos {D : ℝ} (hD : 0 < D) : 0 < thinning D :=
  Real.rpow_pos_of_pos hD _

lemma thinning_tendsto : Tendsto thinning atTop (𝓝 0) := by
  change Tendsto (fun D : ℝ => D ^ (-(1 / 200) : ℝ)) atTop (𝓝 0)
  exact tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 200)

lemma thinning_mul_power {D : ℝ} (hD : 0 < D) (a : ℝ) :
    thinning D * D ^ a = D ^ (a - 1 / 200) := by
  unfold thinning
  rw [← Real.rpow_add hD]
  congr 1
  ring

lemma thinning_pow_mul_power {D : ℝ} (hD : 0 < D) (j : ℕ) (a : ℝ) :
    thinning D ^ j * D ^ a = D ^ (a - (j : ℝ) / 200) := by
  unfold thinning
  rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_add hD]
  congr 1
  ring

namespace Sampling

lemma thinningError_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun D : ℝ => samplingScaleError c (thinning D) D) atTop (𝓝 0) := by
  have h₀ := tendsto_monomial_exp_neg_power 0 (179 / 200) (1 / 3)
    (by norm_num) (by norm_num)
  have h₁ := tendsto_monomial_exp_neg_power (51 / 50) (179 / 200) (c / 8)
    (by norm_num) (by positivity)
  have h₂ := (tendsto_monomial_exp_neg_power (23 / 20) (153 / 200) (c ^ 2 / 512)
    (by norm_num) (by positivity)).const_mul (2 * (4 / c + 2))
  have h := (h₀.add h₁).add h₂
  simp only [add_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  simp only [samplingScaleError, Real.rpow_zero, one_mul]
  have hpow : thinning D * D ^ (9 / 10 : ℝ) = D ^ (179 / 200 : ℝ) := by
    rw [thinning_mul_power hD]
    norm_num
  have hcube : thinning D ^ 3 * D ^ (39 / 50 : ℝ) = D ^ (153 / 200 : ℝ) := by
    rw [thinning_pow_mul_power hD]
    norm_num
  rw [show -thinning D / 3 * D ^ (9 / 10 : ℝ) =
      -(1 / 3) * (thinning D * D ^ (9 / 10 : ℝ)) by ring,
    show -(thinning D * c / 8) * D ^ (9 / 10 : ℝ) =
      -(c / 8) * (thinning D * D ^ (9 / 10 : ℝ)) by ring,
    show -(thinning D ^ 3 * c ^ 2 / 512) * D ^ (39 / 50 : ℝ) =
      -(c ^ 2 / 512) * (thinning D ^ 3 * D ^ (39 / 50 : ℝ)) by ring,
    hpow, hcube]

lemma eventually_thinningReady (c : ℝ) (hc : 0 < c) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℕ, D ^ (9 / 10 : ℝ) ≤ r →
      (r : ℝ) ≤ D ^ (51 / 50 : ℝ) → SamplingScaleReady c (thinning D) D r := by
  have hmiss := tendsto_monomial_exp_neg_power (51 / 50) (1 / 200) (1 / 4)
    (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)).eventually_ge_atTop 2,
    eventually_monomial_lt 1 (c / 4) (37 / 50) (179 / 200) (by positivity) (by norm_num),
    eventually_monomial_lt 1 c (1 / 100) (9 / 10) hc (by norm_num),
    hmiss.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_monomial_lt (4 / c) (1 / 4) (-31 / 200) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt (4 / c) (1 / 4) (-3 / 20) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt 1 (c / 24) (37 / 50) (89 / 100) (by positivity) (by norm_num),
    eventually_monomial_lt (4 / c) (c / 24) (173 / 200) (89 / 100) (by positivity) (by norm_num),
    eventually_monomial_lt (4 / c) (c / 24) (87 / 100) (89 / 100) (by positivity) (by norm_num),
    eventually_log_le_small_power,
    eventually_monomial_lt ((51 / 50) * (4 / c + 2)) (c ^ 2 / 512) (23 / 100) (153 / 200)
      (by positivity) (by norm_num)] with D hD h2 hτ hM hm hε₁ hε₂ ht₀ ht₁ ht₂ hlog hcost
  intro r hrlo hrhi
  have hDpos : 0 < D := by linarith
  have hr2 : 2 ≤ r := by exact_mod_cast h2.trans hrlo
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let p := thinning D
  let h := c * D ^ (9 / 10 : ℝ)
  let τ := D ^ (37 / 50 : ℝ)
  let M := D ^ (1 / 100 : ℝ)
  have hp : 0 < p := thinning_pos hDpos
  have hph : p * h = c * D ^ (179 / 200 : ℝ) := by
    dsimp [p, h]
    rw [mul_left_comm, thinning_mul_power hDpos]
    norm_num
  have hpM : p * M = D ^ (1 / 200 : ℝ) := by
    dsimp [p, M]
    rw [thinning_mul_power hDpos]
    norm_num
  have hp2h : p ^ 2 * h = c * D ^ (89 / 100 : ℝ) := by
    dsimp [p, h]
    rw [mul_left_comm, thinning_pow_mul_power hDpos]
    norm_num
  have hp3 : (p ^ 3 * c ^ 2 / 512) * D ^ (39 / 50 : ℝ) =
      (c ^ 2 / 512) * D ^ (153 / 200 : ℝ) := by
    have hp3' : p ^ 3 * D ^ (39 / 50 : ℝ) = D ^ (153 / 200 : ℝ) := by
      dsimp [p]
      rw [thinning_pow_mul_power hDpos]
      norm_num
    rw [show (p ^ 3 * c ^ 2 / 512) * D ^ (39 / 50 : ℝ) =
      (c ^ 2 / 512) * (p ^ 3 * D ^ (39 / 50 : ℝ)) by ring, hp3']
  have he₁ : 4 * τ / (p * h) = (4 / c) * D ^ (-31 / 200 : ℝ) := by
    rw [hph]
    dsimp [τ]
    rw [show (-31 / 200 : ℝ) = 37 / 50 - 179 / 200 by norm_num, Real.rpow_sub hDpos]
    field_simp
  have he₂ : 4 * τ * M / h = (4 / c) * D ^ (-3 / 20 : ℝ) := by
    dsimp [τ, M, h]
    rw [show (-3 / 20 : ℝ) = (37 / 50 + 1 / 100) - 9 / 10 by norm_num,
      Real.rpow_sub hDpos, Real.rpow_add hDpos]
    field_simp
  have hm₁ : D ^ (51 / 50 : ℝ) * ((4 / c) * D ^ (-31 / 200 : ℝ)) =
      (4 / c) * D ^ (173 / 200 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  have hm₂ : D ^ (51 / 50 : ℝ) * ((4 / c) * D ^ (-3 / 20 : ℝ)) =
      (4 / c) * D ^ (87 / 100 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  change 2 ≤ r ∧ τ < p * h / 4 ∧ M ≤ h ∧ _
  refine ⟨hr2, ?_, by simpa only [one_mul] using hM.le, ?_, ?_, ?_, ?_⟩
  · rw [hph]
    dsimp [τ] at ⊢
    simpa only [one_mul, div_mul_eq_mul_div] using hτ
  · change (r : ℝ) * exp (-p * M / 4) < 1 / 2
    rw [neg_mul, hpM]
    refine (mul_le_mul_of_nonneg_right hrhi (exp_pos _).le).trans_lt ?_
    simpa only [neg_div, neg_mul, div_mul_eq_mul_div, one_mul] using hm
  · change 4 * τ / (p * h) + 4 * τ * M / h ≤ 1 / 2
    rw [he₁, he₂]
    simp only [Real.rpow_zero, mul_one] at hε₁ hε₂
    linarith
  · change τ + (r : ℝ) * (4 * τ / (p * h) + 4 * τ * M / h) ≤ p ^ 2 * h / 8
    rw [he₁, he₂, hp2h]
    have ht : (r : ℝ) * ((4 / c) * D ^ (-31 / 200 : ℝ) + (4 / c) * D ^ (-3 / 20 : ℝ)) ≤
        (4 / c) * D ^ (173 / 200 : ℝ) + (4 / c) * D ^ (87 / 100 : ℝ) := by
      calc
        _ ≤ D ^ (51 / 50 : ℝ) * _ := mul_le_mul_of_nonneg_right hrhi (by positivity)
        _ = _ := by rw [mul_add, hm₁, hm₂]
    dsimp [τ]
    nlinarith only [ht, ht₀, ht₁, ht₂]
  · change exp (-p * r / 3) + r * exp (-p * h / 8) + _ ≤ samplingScaleError c p D
    have hwitness := sampling_witness_error_le c p D r hc hp hD hrpos hrhi hlog
      (by rw [hp3]; exact hcost.le)
    have hsize : exp (-p * r / 3) ≤ exp (-p / 3 * D ^ (9 / 10 : ℝ)) := by
      apply exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hrlo hp.le
      nlinarith
    have hdegree : (r : ℝ) * exp (-p * h / 8) ≤
        D ^ (51 / 50 : ℝ) * exp (-(p * c / 8) * D ^ (9 / 10 : ℝ)) := by
      have heq : -p * h / 8 = -(p * c / 8) * D ^ (9 / 10 : ℝ) := by dsimp [h]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
    exact add_le_add (add_le_add hsize hdegree) hwitness

end Sampling

end
end ErdosGallai

namespace ErdosGallai.Sampling
open Filter MeasureTheory Real

universe u

theorem vertex_sampling_uniform (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      CutExpansion P (c*D^(9/10 : ℝ)) →
      ∀ p : unitInterval, (p : ℝ) = thinning D →
      (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω} ≤ ε := by
  have hevent : ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧
      (∀ r : ℕ, D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) →
        SamplingScaleReady c (thinning D) D r) ∧
      samplingScaleError c (thinning D) D ≤ ε := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_thinningReady c hc,
      (thinningError_tendsto c hc).eventually_le_const hε] with D h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hrlo hrhi hexp p hpD
  obtain ⟨h1, hready, herr⟩ := hD₀ D hD
  have hDpos : 0 < D := by linarith
  have hp : 0 < (p : ℝ) := hpD ▸ thinning_pos hDpos
  rw [← hpD] at hready herr
  obtain ⟨hr,hτ,hM,hmiss,he,hperturb,hbound⟩ := hready (Fintype.card V) hrlo hrhi
  exact (vertex_sampling_failure_bound P p hp (by positivity) (by positivity)
    hτ (by positivity) hM hr hmiss he hperturb hexp).trans (hbound.trans herr)

end ErdosGallai.Sampling

open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Sampling

def reservoirLabelPMF (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) : PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if i = 3 then 1-3*(p : ℝ) else (p : ℝ))) (by
    rw [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (2 : Fin 4) ≠ 3 by decide, ↓reduceIte,  ]
    rw [← ENNReal.ofReal_add p.property.1 p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) (by linarith)]
    norm_num [show (p : ℝ)+(p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1 by ring])

def labelIs (i : Fin 3) (j : Fin 4) : Bool := decide (j = i.castSucc)

lemma ofReal_unitInterval (p : unitInterval) :
    ENNReal.ofReal (p : ℝ) = (unitInterval.toNNReal p : ENNReal) := by
  unfold ENNReal.ofReal
  apply congrArg (fun x : NNReal => (x : ENNReal))
  apply Subtype.ext
  exact Real.coe_toNNReal _ p.property.1

lemma labelIs_preserving (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (labelIs i) (reservoirLabelPMF p hp).toMeasure
      (bernoulliMeasure true false p) := by
  have hnon : 0 ≤ (p : ℝ) := p.property.1
  have hnon' : 0 ≤ 1-3*(p : ℝ) := by linarith
  refine ⟨measurable_of_finite _, ?_⟩
  apply Measure.ext_iff_singleton.mpr
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  rw [PMF.toMeasure_apply_fintype]
  simp only [reservoirLabelPMF]
  cases b <;> fin_cases i <;>
    simp [labelIs, Fin.sum_univ_four,  PMF.ofFintype_apply]
  all_goals
    first
    | exact ofReal_unitInterval p
    | rw [← ENNReal.ofReal_add hnon hnon,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (p : ℝ)+(p : ℝ)) hnon']
      convert ofReal_unitInterval (unitInterval.symm p) using 1
      congr 1
      change (p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1-(p : ℝ)
      ring

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory
noncomputable section
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

def reservoirSample (i : Fin 3) (ω : V → Fin 4) : V → Bool := fun v => labelIs i (ω v)

def reservoirMeasure (V : Type cycleUniverse2) [Fintype V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    Measure (V → Fin 4) := Measure.pi (fun _ : V => (reservoirLabelPMF p hp).toMeasure)

instance reservoirMeasure_probability (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    IsProbabilityMeasure (reservoirMeasure V p hp) := by unfold reservoirMeasure; infer_instance

lemma reservoirSample_preserving {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (reservoirSample i) (reservoirMeasure V p hp) (sampleMeasure V p) := by
  exact measurePreserving_pi _ _ (fun _ => labelIs_preserving p hp i)

lemma reservoirSamples_disjoint {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (ω : V → Fin 4) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (sampleVertices (reservoirSample i ω)) (sampleVertices (reservoirSample j ω)) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    reservoirSample, labelIs, decide_eq_true_eq] at hi hj
  exact hij (Fin.castSucc_injective 3 (hi.symm.trans hj))

universe u

theorem three_reservoirs_uniform (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (P i).Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      (∀ i, CutExpansion (P i) (c*D^(9/10 : ℝ))) →
      ∀ p : unitInterval, (p : ℝ) = thinning D → 3*(p : ℝ) ≤ 1 →
      ∃ W : Fin 3 → Finset V,
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*(p : ℝ)*Fintype.card V) ∧
        (∀ i v, (p : ℝ)*(c*D^(9/10 : ℝ))/2 ≤ ((neighborsIn (P i) v (W i)).card : ℝ)) ∧
        (∀ i, CutExpansionOn (P i) (W i) (D^(37/50 : ℝ))) := by
  obtain ⟨D₀,hD₀⟩ := vertex_sampling_uniform.{u} c hc (1/4) (by norm_num)
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hlo hhi hcut p hpD hp3
  let μ := reservoirMeasure V p hp3
  let B : Fin 3 → Set (V → Fin 4) := fun i =>
    {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) (reservoirSample i ω)}
  have hB : ∀ i, μ.real (B i) ≤ 1/4 := by
    intro i
    have hm := (reservoirSample_preserving (V := V) p hp3 i).measure_preimage
      ((Set.Finite.measurableSet (Set.toFinite {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω})).nullMeasurableSet)
    change (μ (B i)).toReal ≤ 1/4
    rw [show μ (B i) = (sampleMeasure V p) {ω | ¬SampleGood (P i) (p : ℝ)
      (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) ω} from hm]
    exact hD₀ D hD V (P i) hlo hhi (hcut i) p hpD
  have hi : ∑ i ∈ (Finset.univ : Finset (Fin 3)), μ.real (B i) < 1 := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), (1/4 : ℝ) := by
        exact Finset.sum_le_sum (fun i _ => hB i)
      _ < 1 := by norm_num
  obtain ⟨ω,hω⟩ := exists_avoiding_finite_events (μ := μ) Finset.univ B hi
  have hgood : ∀ i, SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ))
      (reservoirSample i ω) := by
    intro i
    exact not_not.mp (hω i (Finset.mem_univ i))
  refine ⟨fun i => sampleVertices (reservoirSample i ω), reservoirSamples_disjoint ω,
    fun i => (hgood i).1, fun i => (hgood i).2.1, fun i => (hgood i).2.2⟩

end
end ErdosGallai.Sampling

end
end
end

end OAI


-- Upstream module EdgeSplitting

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Splitting
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

lemma exp_half_bound : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  nlinarith [exp_one_lt_d9, exp_pos (1 / 2 : ℝ)]

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

theorem bernoulli_sum_upper_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | 2 * p * s.card ≤ ∑ i ∈ s, X i ω} ≤ exp (-p * s.card / 3) := by
  have hInt : Integrable (fun ω => exp ((1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (2 * p * s.card)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(1 / 2 : ℝ) * (2 * p * s.card)) *
        exp ((s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (-p * s.card + (s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

def edgeColorMeasure (V : Type cycleUniverse5) [Fintype V] (l : ℕ) [NeZero l] :
    Measure (Sym2 V → Fin l) :=
  Measure.pi (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure)

instance edgeColorMeasure_probability (l : ℕ) [NeZero l] :
    IsProbabilityMeasure (edgeColorMeasure V l) := by
  unfold edgeColorMeasure
  infer_instance

def colorIndicator {l : ℕ} (i : Fin l) (e : Sym2 V) (ω : Sym2 V → Fin l) : ℝ :=
  if ω e = i then 1 else 0

lemma colorIndicator_indep {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) :
    iIndepFun (colorIndicator (V := V) i) (edgeColorMeasure V l) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma colorIndicator_integral {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) (e : Sym2 V) :
    ∫ ω, colorIndicator i e ω ∂edgeColorMeasure V l = 1/(l : ℝ) := by
  have hl := (measurePreserving_eval
    (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
  have hi := hl.integral_comp (f := fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [PMF.integral_eq_sum] at hi
  simpa [edgeColorMeasure, colorIndicator, PMF.uniformOfFintype_apply] using hi

def colorGraph (P : SimpleGraph V) {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    SimpleGraph V where
  Adj x y := P.Adj x y ∧ ω s(x,y) = i
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact P.irrefl h.1⟩

instance colorGraph_decidable (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    DecidableRel (colorGraph P ω i).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma colorGraph_interedges {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S T : Finset V) :
    (colorGraph P ω i).interedges S T =
      (P.interedges S T).filter (fun e => ω s(e.1,e.2) = i) := by
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_filter]
  change (x ∈ S ∧ y ∈ T ∧ (P.Adj x y ∧ ω s(x,y) = i)) ↔ _
  tauto

lemma color_cut_sum (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S : Finset V) :
    (∑ e ∈ (P.interedges S Sᶜ).image (fun e => s(e.1,e.2)), colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
  rw [Finset.sum_image (boundary_sym2_injective P S)]
  simp only [colorIndicator, Finset.sum_boole, colorGraph_interedges]

lemma color_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] (i : Fin l) (S : Finset V) {h : ℝ}
    (hexp : CutExpansion P h) (hS : S.card ≤ Sᶜ.card) :
    (edgeColorMeasure V l).real {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ≤
        exp (-h*S.card/(8*l)) := by
  let E := (P.interedges S Sᶜ).image (fun e => s(e.1,e.2))
  have hcard : E.card = (P.interedges S Sᶜ).card :=
    Finset.card_image_of_injOn (boundary_sym2_injective P S)
  have hl : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  have hcut : h * S.card ≤ (E.card : ℝ) := by
    rw [hcard]
    have he := hexp S
    rwa [min_eq_left (by exact_mod_cast hS)] at he
  have hb := bernoulli_sum_lower_tail (μ := edgeColorMeasure V l) E
    (fun e => measurable_of_finite (colorIndicator i e)) (colorIndicator_indep i)
    (fun e ω => by simp only [colorIndicator]; split <;> simp)
    (1/(l : ℝ)) (by positivity) (colorIndicator_integral i)
  apply (measureReal_mono (show {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ⊆
      {ω | (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2} from ?_)).trans
      (hb.trans ?_)
  · intro ω hω
    change (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2
    rw [show (∑ e ∈ E, colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) from color_cut_sum P ω i S]
    calc
      _ ≤ h*S.card/(2*l) := le_of_lt hω
      _ ≤ (E.card : ℝ)/(2*l) := div_le_div_of_nonneg_right hcut (by positivity)
      _ = _ := by ring
  · apply exp_le_exp.mpr
    have he := div_le_div_of_nonneg_right hcut (show 0 ≤ 8*(l : ℝ) by positivity)
    calc
      _ = -((E.card : ℝ)/(8*l)) := by ring
      _ ≤ -(h*S.card/(8*l)) := neg_le_neg he
      _ = _ := by ring

lemma cutExpansion_of_small_cuts (P : SimpleGraph V) [DecidableRel P.Adj] {h : ℝ}
    (hcut : ∀ S : Finset V, S.Nonempty → S.card ≤ Sᶜ.card →
      h*S.card ≤ ((P.interedges S Sᶜ).card : ℝ)) : CutExpansion P h := by
  intro S
  by_cases he : S = ∅
  · simp [he]
  by_cases hc : Sᶜ = ∅
  · simp [hc]
  by_cases hs : S.card ≤ Sᶜ.card
  · rw [min_eq_left (by exact_mod_cast hs)]
    exact hcut S (Finset.nonempty_iff_ne_empty.mpr he) hs
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
    have hi := hcut Sᶜ (Finset.nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs)
    have hcomm : (P.interedges Sᶜ S).card = (P.interedges S Sᶜ).card := by
      have := P.symm
      exact Rel.card_interedges_comm Sᶜ S
    simpa only [compl_compl, hcomm] using hi

lemma sum_nonempty_subsets_power (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)).erase ∅, q^S.card) =
      (1+q)^(Fintype.card V)-1 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun S : Finset V => q^S.card)
    (Finset.mem_univ (∅ : Finset V))
  have hp := Finset.prod_one_add (s := (Finset.univ : Finset V)) (f := fun _ => q)
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at hp
  simp only [Finset.card_empty, pow_zero] at hs
  linarith

theorem edge_splitting_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h) :
    (edgeColorMeasure V l).real {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ≤
      l * (exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) := by
  let cuts : Finset (Finset V) := Finset.univ.erase ∅
  let B (i : Fin l) (S : Finset V) : Set (Sym2 V → Fin l) :=
    {ω | S.card ≤ Sᶜ.card ∧
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)}
  let q : ℝ := exp (-h/(8*l))
  have cover : {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S := by
    intro ω hω
    rcases hω with ⟨i, hi⟩
    by_contra hn
    apply hi
    apply cutExpansion_of_small_cuts
    intro S hS hs
    have hb : ω ∉ B i S := by
      intro hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hS.ne_empty, Finset.mem_univ _⟩, hm⟩⟩⟩⟩
    have hc : h*S.card/(2*l) ≤ (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
      exact le_of_not_gt (fun hf => hb ⟨hs, hf⟩)
    convert hc using 1 ; ring
  have hbound (i : Fin l) (S : Finset V) :
      (edgeColorMeasure V l).real (B i S) ≤ q^S.card := by
    by_cases hs : S.card ≤ Sᶜ.card
    · calc
        _ ≤ (edgeColorMeasure V l).real {ω |
            (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} :=
          measureReal_mono (fun _ hw => hw.2)
        _ ≤ exp (-h*S.card/(8*l)) := color_cut_lower_tail P i S hexp hs
        _ = q^S.card := by dsimp [q]; rw [← exp_nat_mul]; congr 1; ring
    · have he : B i S = ∅ := by ext ω; simp [B,hs]
      rw [he, measureReal_empty]
      exact pow_nonneg (exp_pos _).le _
  calc
    _ ≤ (edgeColorMeasure V l).real
        (⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S) :=
      measureReal_mono cover (measure_ne_top _ _)
    _ ≤ ∑ i : Fin l, (edgeColorMeasure V l).real (⋃ S ∈ cuts, B i S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i : Fin l, ∑ S ∈ cuts, (edgeColorMeasure V l).real (B i S) :=
      Finset.sum_le_sum (fun _ _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _i : Fin l, ∑ S ∈ cuts, q^S.card := by
      apply Finset.sum_le_sum; intro i _; exact Finset.sum_le_sum (fun S _ => hbound i S)
    _ = (l : ℝ)*((1+q)^(Fintype.card V)-1) := by
      simp only [cuts, sum_nonempty_subsets_power, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ l*(exp ((Fintype.card V : ℝ)*q)-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg l)
      apply sub_le_sub_right
      calc
        _ ≤ (exp q)^(Fintype.card V) :=
          pow_le_pow_left₀ (by dsimp [q]; positivity) (by linarith [add_one_le_exp q]) _
        _ = _ := (exp_nat_mul _ _).symm

theorem edge_splitting_of_error_lt_one (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h)
    (herror : (l : ℝ)*(exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) < 1) :
    ∃ ω : Sym2 V → Fin l,
      (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
      (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
      (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have he := (edge_splitting_failure_bound P hexp).trans_lt herror
  have hh : ∃ ω : Sym2 V → Fin l, ∀ i, CutExpansion (colorGraph P ω i) (h/(2*l)) := by
    by_contra hn
    push Not at hn
    have hall : {ω : Sym2 V → Fin l | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} =
        Set.univ := Set.eq_univ_of_forall hn
    simp only [hall, Measure.real, measure_univ, ENNReal.toReal_one] at he
    exact (lt_irrefl _ he)
  obtain ⟨ω, hω⟩ := hh
  refine ⟨ω, hω, ?_, ?_⟩
  · intro x y
    exact ⟨fun hxy => ⟨ω s(x,y), hxy, rfl⟩, fun ⟨_, hxy, _⟩ => hxy⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with | _ x y =>
      have hi : (colorGraph P ω i).Adj x y := by simpa using hei
      have hj : (colorGraph P ω j).Adj x y := by simpa using hej
      exact hij (hi.2.symm.trans hj.2)

end

open Filter Asymptotics
open scoped Topology

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

noncomputable def edgeSplittingScaleError (c : ℝ) (l : ℕ) (D : ℝ) : ℝ :=
  (l : ℝ) * (Real.exp (D^(51/50 : ℝ) * Real.exp ((-(c / (8*l))) * D^(9/10 : ℝ))) - 1)

lemma edgeSplittingScaleError_tendsto (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    Tendsto (edgeSplittingScaleError c l) atTop (𝓝 0) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have ht := tendsto_monomial_exp_neg_power (51/50) (9/10) (c/(8*l))
    (by norm_num) (by positivity)
  have hh := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l : ℝ)
  unfold edgeSplittingScaleError
  convert hh using 1 <;> norm_num

universe u

theorem edge_splitting_uniform (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ),
      c*D^(9/10 : ℝ) ≤ h → D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) → CutExpansion P h →
      ∃ ω : Sym2 V → Fin l,
        (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
        (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
        (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have : NeZero l := ⟨hl.ne'⟩
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hevent := (edgeSplittingScaleError_tendsto c hc l hl).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ h hh _hrlo hrhi hexp
  apply edge_splitting_of_error_lt_one P hexp
  apply lt_of_le_of_lt _ (hD₀ D hD)
  unfold edgeSplittingScaleError
  apply mul_le_mul_of_nonneg_left _ hlR.le
  apply sub_le_sub_right
  apply exp_le_exp.mpr
  apply mul_le_mul hrhi _ (exp_pos _).le ((Nat.cast_nonneg (Fintype.card V)).trans hrhi)
  apply exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right hh (show 0 ≤ 8*(l : ℝ) by positivity)
  calc
    -h/(8*l) = -(h/(8*l)) := by ring
    _ ≤ -(c*D^(9/10 : ℝ)/(8*l)) := neg_le_neg he
    _ = -(c/(8*l))*D^(9/10 : ℝ) := by ring

end ErdosGallai.Splitting

end
end
end

end OAI


-- Upstream module Representatives

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Representatives
noncomputable section
open Finset
variable {I : Type cycleUniverse1} {V : Type cycleUniverse2} [DecidableEq I] [DecidableEq V] [Nonempty V]

lemma choose_with_mates (A : Finset I) (mate : I → I)
    (hmate : Function.Involutive mate) (hfix : ∀ i, mate i ≠ i)
    (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ A, A.card ≤ ((N i).card - 1) * k) :
    ∃ f : I → V, (∀ i ∈ A, f i ∈ N i) ∧
      (∀ i ∈ A, mate i ∈ A → f i ≠ f (mate i)) ∧
      (∀ v, (A.filter (fun i => f i = v)).card ≤ k) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert i A hi ih =>
    obtain ⟨f,hf,hsep,hcap⟩ := ih (by
      intro j hj
      exact (Finset.card_le_card (Finset.subset_insert i A)).trans (hroom j (by simp [hj])))
    have hlt : A.card < ((N i).erase (f (mate i))).card * k := by
      have h := hroom i (by simp)
      have hcard := Finset.pred_card_le_card_erase (s := N i) (a := f (mate i))
      have hmul := Nat.mul_le_mul_right k hcard
      rw [Finset.card_insert_of_notMem hi] at h
      omega
    obtain ⟨v,hv,hload⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := f) hlt
    have hvN := (Finset.mem_erase.mp hv).2
    have hvne := (Finset.mem_erase.mp hv).1
    let g := Function.update f i v
    have gi : g i = v := by simp [g]
    have gold : ∀ j, j ≠ i → g j = f j := by
      intro j hj
      simp [g, hj]
    refine ⟨g, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [gi] using hvN
      · rw [gold j (ne_of_mem_of_not_mem hj hi)]
        exact hf j hj
    · intro j hj hmj
      by_cases hji : j = i
      · subst j
        rw [gi, gold (mate i) (hfix i)]
        exact hvne
      · rw [gold j hji]
        by_cases hmi : mate j = i
        · rw [hmi, gi]
          have hjm : j = mate i := by rw [← hmi, hmate]
          simpa [hjm] using hvne.symm
        · rw [gold (mate j) hmi]
          exact hsep j (Finset.mem_of_mem_insert_of_ne hj hji)
            (Finset.mem_of_mem_insert_of_ne hmj hmi)
    · intro w
      have hold : A.filter (fun j => g j = w) = A.filter (fun j => f j = w) := by
        apply Finset.filter_congr
        intro j hj
        rw [gold j (ne_of_mem_of_not_mem hj hi)]
      rw [Finset.filter_insert, hold]
      by_cases hvw : v = w
      · simp only [gi, hvw, if_pos]
        rw [Finset.card_insert_of_notMem (fun h => hi (Finset.mem_filter.mp h).1)]
        simpa only [hvw] using Nat.succ_le_of_lt hload
      · simp only [gi, hvw, ite_false]
        exact hcap w

theorem two_distinct_representatives (S : Finset I) (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ S, 2*S.card ≤ ((N i).card-1)*k) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ k) := by
  let mate : I × Fin 2 → I × Fin 2 := fun i => (i.1, 1-i.2)
  have hm : Function.Involutive mate := by
    rintro ⟨i,t⟩
    fin_cases t <;> rfl
  have hfix : ∀ i, mate i ≠ i := by
    rintro ⟨i,t⟩
    fin_cases t <;> (intro h; have hh := congrArg Prod.snd h; norm_num [mate] at hh)
  obtain ⟨f,hf,hsep,hcap⟩ := choose_with_mates (S ×ˢ Finset.univ) mate hm hfix
    (fun i => N i.1) k (by
      intro i hi
      simpa [Finset.card_product, mul_comm] using hroom i.1 (Finset.mem_product.mp hi).1)
  refine ⟨f, ?_, ?_, hcap⟩
  · intro i hi t
    exact hf (i,t) (by simp [hi])
  · intro i hi
    exact hsep (i,0) (by simp [hi]) (by simp [mate, hi])

theorem reservoir_representatives (S : Finset I) (N : I → Finset V)
    (r d : ℝ) (hr : (S.card : ℝ) ≤ r) (hd : 4 ≤ d)
    (hN : ∀ i ∈ S, d/2 ≤ ((N i).card : ℝ)) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ ⌈8*r/d⌉₊) := by
  apply two_distinct_representatives
  intro i hi
  have hd0 : 0 < d := by linarith
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr
  have hNi := hN i hi
  have hNi1 : 1 ≤ (N i).card := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (N i).card)
  have hn : d/4 ≤ (((N i).card - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hNi1]
    push_cast
    linarith
  have hk : 8*r/d ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.le_ceil _
  have hk0 : 0 ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.cast_nonneg _
  have hprod : 2*(S.card : ℝ) ≤ (((N i).card - 1 : ℕ) : ℝ)*(⌈8*r/d⌉₊ : ℝ) := by
    calc
      _ ≤ 2*r := by linarith
      _ = (d/4)*(8*r/d) := by field_simp; ring
      _ ≤ (d/4)*(⌈8*r/d⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hn hk0
  exact_mod_cast hprod

end
end ErdosGallai.Representatives

namespace ErdosGallai
noncomputable section
open Finset Real Filter
local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def reservoirProbability (η : ℝ) : ℝ := min (η/12) (1/12)
noncomputable def reservoirExpansionCoefficient (c : ℝ) : ℝ := min c 1 / 6

universe u

theorem reservoir_preparation (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      Splitting.CutExpansion P (c*D^(9/10 : ℝ)) →
      ∃ (ω : Sym2 V → Fin 3) (W : Fin 3 → Finset V) (f : Fin 3 → V × Fin 2 → V),
        (∀ i, Splitting.colorGraph P ω i ≤ G) ∧
        (∀ i j, i ≠ j → Disjoint (Splitting.colorGraph P ω i).edgeSet
            (Splitting.colorGraph P ω j).edgeSet) ∧
        (∀ i, Splitting.CutExpansion (Splitting.colorGraph P ω i)
          (reservoirExpansionCoefficient c * D^(9/10 : ℝ))) ∧
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, 2 ≤ (W i).card) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*thinning D*Fintype.card V) ∧
        (∀ i, (W i).card < Fintype.card V) ∧
        ((∑ i, (W i).card : ℕ) : ℝ) ≤ 6 * thinning D * Fintype.card V ∧
        (∀ i, Sampling.CutExpansionOn (Splitting.colorGraph P ω i) (W i)
          (D^(37/50 : ℝ))) ∧
        (∀ i v, v ∉ W i → ∀ t, f i (v,t) ∈ W i ∧
          (Splitting.colorGraph P ω i).Adj v (f i (v,t))) ∧
        (∀ i v, v ∉ W i → f i (v,0) ≠ f i (v,1)) ∧
        (∀ i w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f i x = w)).card ≤
          ⌈8*(Fintype.card V : ℝ) /
            (thinning D * (reservoirExpansionCoefficient c * D^(9/10 : ℝ)))⌉₊) := by
  let c₀ := min c 1
  let a := reservoirExpansionCoefficient c
  have hc₀ : 0 < c₀ := lt_min hc (by norm_num)
  have ha : 0 < a := by dsimp [a, reservoirExpansionCoefficient]; positivity
  obtain ⟨D₁,hD₁⟩ := Splitting.edge_splitting_uniform.{u} c₀ hc₀ 3 (by norm_num)
  obtain ⟨D₂,hD₂⟩ := Sampling.three_reservoirs_uniform.{u} a ha
  have hready : ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧ thinning D ≤ 1 / 12 ∧ 4 ≤ a * D ^ (179 / 200 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      thinning_tendsto.eventually_le_const (show (0 : ℝ) < 1 / 12 by norm_num),
      Sampling.eventually_monomial_lt 4 a 0 (179 / 200)
        ha (by norm_num)] with D hD hq hp
    exact ⟨hD, hq, by simpa using hp.le⟩
  obtain ⟨D₃,hD₃⟩ := hready.exists_forall_of_atTop
  refine ⟨max D₁ (max D₂ D₃), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  have hDsplit : D₁ ≤ D := (le_max_left _ _).trans hD
  have hDsample : D₂ ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDpower : D₃ ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  obtain ⟨hD1, hq12, hexponent⟩ := hD₃ D hDpower
  have hDpos : 0 < D := by linarith
  let q := thinning D
  have hq : 0 < q := thinning_pos hDpos
  change q ≤ _ at hq12
  have hq3 : 3*q ≤ 1 := by linarith
  have hq2 : 2*q < 1 := by linarith
  let p : unitInterval := ⟨q, hq.le, by linarith⟩
  have hpow : 0 < D^(9/10 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hd : 4 ≤ q*(a*D^(9/10 : ℝ)) := by
    dsimp [q]
    rw [mul_left_comm, thinning_mul_power hDpos]
    norm_num
    exact hexponent
  have hr : 0 < (Fintype.card V : ℝ) := hpow.trans_le hlo
  have : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast hr)
  have hexp₀ : Splitting.CutExpansion P (c₀*D^(9/10 : ℝ)) := by
    intro U
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c 1) hpow.le)
      (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans (hexp U)
  obtain ⟨ω,hcut,hcover,hdisj⟩ := hD₁ D hDsplit V P
    (c₀*D^(9/10 : ℝ)) le_rfl hlo hhi hexp₀
  have hcut' : ∀ i, Sampling.CutExpansion (Splitting.colorGraph P ω i)
      (a*D^(9/10 : ℝ)) := by
    intro i
    have heq : a*D^(9/10 : ℝ) = c₀*D^(9/10 : ℝ)/(2*(3 : ℝ)) := by
      dsimp [a, reservoirExpansionCoefficient, c₀]
      ring
    rw [heq]
    exact hcut i
  obtain ⟨W,hWdisj,hWsize,hWneigh,hWcut⟩ := hD₂ D hDsample V
    (fun i => Splitting.colorGraph P ω i) hlo hhi hcut' p rfl hq3
  have hWtwo : ∀ i, 2 ≤ (W i).card := by
    intro i
    let v : V := Classical.choice inferInstance
    have hn := hWneigh i v
    have hsub : Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i) ⊆ W i :=
      Finset.filter_subset _ _
    have hh := Finset.card_le_card hsub
    have hn' : (2 : ℝ) ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      change q*(a*D^(9/10 : ℝ))/2 ≤ _ at hn
      linarith
    have hn'' : 2 ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      exact_mod_cast hn'
    omega
  have hWlt : ∀ i, (W i).card < Fintype.card V := by
    intro i
    have hh := (hWsize i).trans_lt (mul_lt_of_lt_one_left hr hq2)
    exact_mod_cast hh
  have hWsum : ((∑ i, (W i).card : ℕ) : ℝ) ≤ 6 * thinning D * Fintype.card V := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hWsize i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    rw [Nat.cast_sum]
    exact hh.trans_eq (by dsimp [p, q]; ring)
  have hrep : ∀ i, ∃ f : V × Fin 2 → V,
      (∀ v ∈ (W i)ᶜ, ∀ t, f (v,t) ∈ Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)) ∧
      (∀ v ∈ (W i)ᶜ, f (v,0) ≠ f (v,1)) ∧
      (∀ w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f x = w)).card ≤
        ⌈8*(Fintype.card V : ℝ)/(q*(a*D^(9/10 : ℝ)))⌉₊) := by
    intro i
    exact Representatives.reservoir_representatives (W i)ᶜ
      (fun v => Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i))
      (Fintype.card V) (q*(a*D^(9/10 : ℝ)))
      (by exact_mod_cast (Finset.card_le_univ ((W i)ᶜ))) hd
      (fun v _ => hWneigh i v)
  choose f hf hsep hcap using hrep
  refine ⟨ω,W,f,?_,hdisj,?_,hWdisj,hWtwo,hWsize,hWlt,hWsum,hWcut,?_,?_,hcap⟩
  · intro i x y hxy
    exact hPG hxy.1
  · exact hcut'
  · intro i v hv t
    exact Finset.mem_filter.mp (hf i v (Finset.mem_compl.mpr hv) t)
  · intro i v hv
    exact hsep i v (Finset.mem_compl.mpr hv)

end
end ErdosGallai

end
end
end

end OAI


-- Upstream module Routing

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

lemma deleted_boundary_card_le (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges U Uᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ F.card := by
  apply Finset.card_le_card_of_injOn (fun e : V × V => s(e.1, e.2))
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · exact (boundary_sym2_injective P U).mono (by
      intro e he
      exact (Finset.mem_filter.mp he).1)

theorem routing_union_growth_step_of_boundary
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤
      h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  let E := P.interedges B Bᶜ
  let Ebad := E.filter (fun e => s(e.1, e.2) ∈ F)
  let Vbad := B.biUnion (fun v => ({v} : Finset V) ×ˢ (W v))
  let Enew := (Finset.univ : Finset V) ×ˢ (Bnext \ B)
  have hcover : E ⊆ Ebad ∪ Vbad ∪ Enew := by
    intro e he
    rcases P.mem_interedges_iff.mp he with ⟨hv, hw, hadj⟩
    have hnw : e.2 ∉ B := Finset.mem_compl.mp hw
    by_cases hdel : s(e.1, e.2) ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hdel⟩))
    by_cases hforbid : e.2 ∈ W e.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨e.1, hv, Finset.mem_product.mpr ⟨by simp, hforbid⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr
        ⟨hextend e.1 hv e.2 hnw hadj hdel hforbid, hnw⟩⟩
  have hcount : E.card ≤ Ebad.card + Vbad.card + Enew.card :=
    (Finset.card_le_card hcover).trans <|
      (Finset.card_union_le _ _).trans <|
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hforbidden : Vbad.card ≤ ∑ v ∈ B, (W v).card := by
    simpa [Vbad, Finset.card_product] using
      (Finset.card_biUnion_le (s := B) (t := fun v => ({v} : Finset V) ×ˢ W v))
  have hnew : Enew.card = Fintype.card V * (Bnext \ B).card := by
    simp [Enew]
  have hraw : E.card ≤ Ebad.card + (∑ v ∈ B, (W v).card) +
      Fintype.card V * (Bnext \ B).card := by omega
  have hsum : (∑ v ∈ B, ((W v).card : ℝ)) ≤ (h / 4) * B.card := by
    calc
      _ ≤ ∑ _v ∈ B, h / 4 := Finset.sum_le_sum hW
      _ = _ := by simp [mul_comm]
  have hcomplN : B.card + Bᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ B)
  have hcompl : (B.card : ℝ) + (Bᶜ.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcomplN
  have hlecompl : (B.card : ℝ) ≤ (Bᶜ.card : ℝ) := by linarith
  have hcut : h * (B.card : ℝ) ≤ (E.card : ℝ) := by
    simpa [min_eq_left hlecompl, E] using hexp B
  have hdiffN : (Bnext \ B).card + B.card = Bnext.card := by
    rw [Finset.card_sdiff_of_subset hmono]
    exact Nat.sub_add_cancel (Finset.card_le_card hmono)
  have hdiff : ((Bnext \ B).card : ℝ) + (B.card : ℝ) = (Bnext.card : ℝ) := by
    exact_mod_cast hdiffN
  have hrawR : (E.card : ℝ) ≤ (Ebad.card : ℝ) +
      (∑ v ∈ B, ((W v).card : ℝ)) +
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    exact_mod_cast hraw
  have hreach : h * (B.card : ℝ) / 2 ≤
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    nlinarith [hcut, hrawR, hF, hsum]
  have hdiv : h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) ≤
      ((Bnext \ B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card V : ℝ))).mpr
    nlinarith [hreach]
  calc
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ)
        = (B.card : ℝ) + h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) := by ring
    _ ≤ (B.card : ℝ) + ((Bnext \ B).card : ℝ) := add_le_add (le_refl _) hdiv
    _ = (Bnext.card : ℝ) := by linarith

theorem routing_union_growth_step
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (F.card : ℝ) ≤ h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  apply routing_union_growth_step_of_boundary P h hexp hr F B Bnext W hmono hsmall
  · have hd : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤ F.card := by
      exact_mod_cast deleted_boundary_card_le P B F
    exact hd.trans hF
  · exact hW
  · exact hextend

def avoidGraph (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    SimpleGraph V where
  Adj v w := P.Adj v w ∧ s(v, w) ∉ F ∧ v ∉ W ∧ w ∉ W
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2.1, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨by intro v h; exact P.irrefl h.1⟩

noncomputable def walkBall (G : SimpleGraph V) (s : V) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : G.Walk s v, p.length ≤ t)

@[simp] lemma mem_walkBall {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (s v : V) (t : ℕ) :
    v ∈ walkBall G s t ↔ ∃ p : G.Walk s v, p.length ≤ t := by
  classical
  simp [walkBall]

lemma root_mem_walkBall (G : SimpleGraph V) (s : V) (t : ℕ) :
    s ∈ walkBall G s t := by
  exact (mem_walkBall G s s t).mpr ⟨.nil, by simp⟩

lemma walkBall_mono (G : SimpleGraph V) (s : V) {t u : ℕ} (htu : t ≤ u) :
    walkBall G s t ⊆ walkBall G s u := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_walkBall G s v t).mp hv
  exact (mem_walkBall G s v u).mpr ⟨p, hp.trans htu⟩

lemma walk_avoids_end {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s v : V} (p : (avoidGraph P F W).Walk s v) (hs : s ∉ W) : v ∉ W := by
  induction p with
  | nil => exact hs
  | cons hadj p ih => exact ih hadj.2.2.2

lemma ball_avoids (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (t : ℕ) : Disjoint (walkBall (avoidGraph P F W) s t) W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨p, _⟩ := (mem_walkBall _ _ _ _).mp hv
  exact walk_avoids_end P F W p hs

lemma walkBall_step (G : SimpleGraph V) (s v w : V) (t : ℕ)
    (hv : v ∈ walkBall G s t) (hadj : G.Adj v w) :
    w ∈ walkBall G s (t + 1) := by
  obtain ⟨p, hp⟩ := (mem_walkBall _ _ _ _).mp hv
  apply (mem_walkBall _ _ _ _).mpr
  exact ⟨p.concat hadj, by simpa using Nat.add_le_add_right hp 1⟩

noncomputable def rootBallUnion (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) (t : ℕ) : Finset V :=
  A.biUnion (fun s => walkBall (avoidGraph P F (W s)) s t)

lemma rootBallUnion_mono_time (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) {t u : ℕ} (htu : t ≤ u) :
    rootBallUnion P F W A t ⊆ rootBallUnion P F W A u :=
  Finset.biUnion_mono (fun s _ => walkBall_mono _ s htu)

lemma roots_subset_rootBallUnion (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) (t : ℕ) : A ⊆ rootBallUnion P F W A t := by
  intro s hs
  exact Finset.mem_biUnion.mpr ⟨s, hs, root_mem_walkBall _ _ _⟩

theorem rootBallUnion_growth_step
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : V → Finset V) (A : Finset V) (t : ℕ)
    (hroots : ∀ s ∈ A, s ∉ W s)
    (hW : ∀ s ∈ A, ((W s).card : ℝ) ≤ h / 4)
    (hsmall : ((rootBallUnion P F W A t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (F.card : ℝ) ≤ h * (rootBallUnion P F W A t).card / 4) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (rootBallUnion P F W A t).card ≤
      ((rootBallUnion P F W A (t + 1)).card : ℝ) := by
  classical
  let B := rootBallUnion P F W A t
  have hchoose : ∀ v ∈ B, ∃ s ∈ A, v ∈ walkBall (avoidGraph P F (W s)) s t := by
    intro v hv
    exact Finset.mem_biUnion.mp hv
  choose s hsA hreach using hchoose
  let forbid : V → Finset V := fun v => if hv : v ∈ B then W (s v hv) else ∅
  apply routing_union_growth_step P h hexp hr F B (rootBallUnion P F W A (t + 1)) forbid
      (rootBallUnion_mono_time P F W A (Nat.le_succ t)) hsmall hF
  · intro v hv
    simpa only [forbid, dif_pos hv] using hW (s v hv) (hsA v hv)
  · intro v hv w _ hadj hdel hforbid
    have hvs : v ∈ walkBall (avoidGraph P F (W (s v hv))) (s v hv) t := hreach v hv
    have hnv : v ∉ W (s v hv) :=
      (Finset.disjoint_left.mp (ball_avoids P F (W (s v hv)) (s v hv)
        (hroots (s v hv) (hsA v hv)) t)) hvs
    have hnw : w ∉ W (s v hv) := by simpa only [forbid, dif_pos hv] using hforbid
    exact Finset.mem_biUnion.mpr ⟨s v hv, hsA v hv,
      walkBall_step _ _ v w t hvs ⟨hadj, hdel, hnv, hnw⟩⟩

theorem rootBallUnion_growth_block
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 ≤ h) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : V → Finset V) (A : Finset V) (t g : ℕ)
    (hroots : ∀ s ∈ A, s ∉ W s)
    (hW : ∀ s ∈ A, ((W s).card : ℝ) ≤ h / 4)
    (hpos : 1 ≤ (rootBallUnion P F W A t).card)
    (hF : (F.card : ℝ) ≤ h * (rootBallUnion P F W A t).card / 4)
    (hg : (Fintype.card V : ℝ) / 2 < (1 + h / (2 * (Fintype.card V : ℝ))) ^ g) :
    (Fintype.card V : ℝ) / 2 < (rootBallUnion P F W A (t + g)).card := by
  by_contra hnot
  have hend := le_of_not_gt hnot
  let b : ℕ → ℝ := fun j => (rootBallUnion P F W A (t + j)).card
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmono : Monotone b := by
    intro j k hjk
    dsimp [b]
    exact_mod_cast Finset.card_le_card
      (rootBallUnion_mono_time P F W A (Nat.add_le_add_left hjk t))
  have hbase : 1 ≤ b 0 := by dsimp [b]; simpa using (Nat.cast_le (α := ℝ)).mpr hpos
  have hstep : ∀ j < g, c * b j ≤ b (j + 1) := by
    intro j hj
    have hsmall : b j ≤ (Fintype.card V : ℝ) / 2 :=
      (hmono (Nat.le_of_lt hj)).trans hend
    have hFj : (F.card : ℝ) ≤ h * (rootBallUnion P F W A (t + j)).card / 4 := by
      have hbj := hmono (Nat.zero_le j)
      dsimp [b] at hbj
      nlinarith
    simpa only [c, b, Nat.add_assoc] using
      rootBallUnion_growth_step P h hexp hr F W A (t + j) hroots hW hsmall hFj
  have hpow : ∀ j ≤ g, c ^ j ≤ b j := by
    intro j
    induction j with
    | zero => intro _; simpa using hbase
    | succ j ih =>
      intro hjg
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * b j := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ b (j + 1) := hstep j (by omega)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma rootBallUnion_halve (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) (t k : ℕ) (u : ℝ)
    (hcard : A.card ≤ 2 * k)
    (hlarge : 2 * u < (rootBallUnion P F W A t).card) :
    ∃ A' ⊆ A, A'.card ≤ k ∧ u < (rootBallUnion P F W A' t).card := by
  obtain ⟨A₁, hsub, hcard₁⟩ := Finset.exists_subset_card_eq (min_le_right k A.card)
  let A₂ := A \ A₁
  have hcard₂ : A₂.card ≤ k := by
    dsimp [A₂]
    rw [Finset.card_sdiff_of_subset hsub, hcard₁]
    omega
  have hcover : A₁ ∪ A₂ = A := Finset.union_sdiff_of_subset hsub
  have hcount : (rootBallUnion P F W A t).card ≤
      (rootBallUnion P F W A₁ t).card + (rootBallUnion P F W A₂ t).card := by
    conv_lhs => rw [← hcover]
    simp only [rootBallUnion, Finset.union_biUnion]
    exact Finset.card_union_le _ _
  by_cases hfirst : u < (rootBallUnion P F W A₁ t).card
  · exact ⟨A₁, hsub, hcard₁ ▸ min_le_left _ _, hfirst⟩
  · refine ⟨A₂, Finset.sdiff_subset, hcard₂, ?_⟩
    have hcR : ((rootBallUnion P F W A t).card : ℝ) ≤
        (rootBallUnion P F W A₁ t).card + (rootBallUnion P F W A₂ t).card := by
      exact_mod_cast hcount
    linarith

theorem rootBallUnion_extract_root
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : V → Finset V) (g N : ℕ)
    (hFglobal : (F.card : ℝ) ≤ h * (Fintype.card V : ℝ) / 16)
    (hg : (Fintype.card V : ℝ) / 2 < (1 + h / (2 * (Fintype.card V : ℝ))) ^ g) :
    ∀ (A : Finset V) (t : ℕ),
      (∀ s ∈ A, s ∉ W s) →
      (∀ s ∈ A, ((W s).card : ℝ) ≤ h / 4) →
      A.card ≤ 2 ^ N →
      (Fintype.card V : ℝ) / 2 < (rootBallUnion P F W A t).card →
      ∃ s ∈ A, (Fintype.card V : ℝ) / 2 <
        (walkBall (avoidGraph P F (W s)) s (t + N * g)).card := by
  induction N with
  | zero =>
    intro A t hroots hW hcard hlarge
    have hne : A.Nonempty := by
      by_contra h
      have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he, rootBallUnion] at hlarge
      linarith
    obtain ⟨s, hs⟩ := hne
    have he : A = {s} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hs, fun v hv => (Finset.card_le_one.mp (by simpa using hcard)) v hv s hs⟩
    refine ⟨s, hs, ?_⟩
    simpa [he, rootBallUnion] using hlarge
  | succ N ih =>
    intro A t hroots hW hcard hlarge
    have hcard' : A.card ≤ 2 * 2 ^ N := by simpa [pow_succ, Nat.mul_comm] using hcard
    obtain ⟨A', hsub, hcard', hlarge'⟩ := rootBallUnion_halve P F W A t (2 ^ N)
      ((Fintype.card V : ℝ) / 4) hcard' (by linarith)
    have hF' : (F.card : ℝ) ≤ h * (rootBallUnion P F W A' t).card / 4 := by
      nlinarith
    have hpos : 1 ≤ (rootBallUnion P F W A' t).card := by
      have : 0 < ((rootBallUnion P F W A' t).card : ℝ) := by linarith
      exact_mod_cast this
    have hroots' : ∀ s ∈ A', s ∉ W s := fun s hs => hroots s (hsub hs)
    have hW' : ∀ s ∈ A', ((W s).card : ℝ) ≤ h / 4 := fun s hs => hW s (hsub hs)
    have hnext := rootBallUnion_growth_block P h hh.le hexp hr F W A' t g
      hroots' hW' hpos hF' hg
    obtain ⟨s, hs, hb⟩ := ih A' (t + g) hroots' hW' hcard' hnext
    refine ⟨s, hsub hs, ?_⟩
    have ht : t + (N + 1) * g = t + g + N * g := by ring
    simpa only [Nat.succ_eq_add_one, ht] using hb

lemma CutExpansion.le_order (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) :
    h ≤ (Fintype.card V : ℝ) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcomplN : 1 ≤ ({v} : Finset V)ᶜ.card := by
    simp only [Finset.card_compl, Finset.card_singleton]
    omega
  have hcompl : (1 : ℝ) ≤ (({v} : Finset V)ᶜ.card : ℝ) := by exact_mod_cast hcomplN
  have hc := hexp {v}
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hcompl, mul_one] at hc
  have hupper := P.card_interedges_le_mul ({v} : Finset V) ({v} : Finset V)ᶜ
  simp only [Finset.card_singleton, one_mul] at hupper
  have hle := (Finset.card_le_univ (({v} : Finset V)ᶜ))
  exact hc.trans (by exact_mod_cast hupper.trans hle)

noncomputable def routingG (r h : ℝ) : ℕ := ⌈8 * (r / h) * Real.logb 2 (2 * r)⌉₊

noncomputable def routingDepth (r : ℝ) : ℕ := ⌈Real.logb 2 r⌉₊

noncomputable def routingLength (r h : ℝ) : ℕ := 2 * routingG r h * (1 + routingDepth r)

lemma routingG_growth (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    r / 2 < (1 + h / (2 * r)) ^ routingG r h := by
  have hr0 : 0 < r := by linarith
  let x := h / (2 * r)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    linarith
  have hlog : h / (4 * r) ≤ Real.log (1 + h / (2 * r)) := by
    have heq : h / (4 * r) = x / 2 := by dsimp [x]; ring
    rw [heq]
    calc
      x / 2 ≤ 2 * x / (x + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxle)]
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    exact htwo
  have hlogpos : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hbase : Real.log (2 * r) ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2pos).mpr
    nlinarith
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) :=
    Nat.le_ceil _
  have hlogpow : 2 * Real.log (2 * r) ≤
      Real.log ((1 + h / (2 * r)) ^ routingG r h) := by
    rw [Real.log_pow]
    calc
      2 * Real.log (2 * r) ≤ 2 * Real.logb 2 (2 * r) := by linarith
      _ = (8 * (r / h) * Real.logb 2 (2 * r)) * (h / (4 * r)) := by
        field_simp
        ; ring
      _ ≤ (routingG r h : ℝ) * (h / (4 * r)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (routingG r h : ℝ) * Real.log (1 + h / (2 * r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsmall : Real.log (r / 2) < 2 * Real.log (2 * r) := by
    have := Real.log_le_log (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 2 * r)
    linarith
  apply (Real.log_lt_log_iff (by positivity : 0 < r / 2) (by positivity)).mp
  exact hsmall.trans_le hlogpow

lemma le_two_pow_routingDepth (r : ℕ) (hr : 0 < r) : r ≤ 2 ^ routingDepth r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hn := Nat.le_ceil (Real.logb 2 (r : ℝ))
  have hp := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hrR).mp hn
  rw [Real.rpow_natCast] at hp
  dsimp [routingDepth]
  exact_mod_cast hp

theorem routing_large_root_ball
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : V → Finset V) (S : Finset V)
    (hne : S.Nonempty)
    (hroots : ∀ s ∈ S, s ∉ W s)
    (hW : ∀ s ∈ S, ((W s).card : ℝ) ≤ h / 4)
    (hFstart : (F.card : ℝ) ≤ h * S.card / 4)
    (hFglobal : (F.card : ℝ) ≤ h * (Fintype.card V : ℝ) / 16) :
    ∃ s ∈ S, (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F (W s)) s
        (routingG (Fintype.card V) h * (1 + routingDepth (Fintype.card V)))).card := by
  have hrpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hg := routingG_growth (Fintype.card V) h (by exact_mod_cast (by omega : 1 ≤ Fintype.card V))
    hh (hexp.le_order P h hr)
  have hsub := roots_subset_rootBallUnion P F W S 0
  have hpos : 1 ≤ (rootBallUnion P F W S 0).card :=
    (Finset.card_pos.mpr hne).trans_le (Finset.card_le_card hsub)
  have hF : (F.card : ℝ) ≤ h * (rootBallUnion P F W S 0).card / 4 := by
    have hc : (S.card : ℝ) ≤ (rootBallUnion P F W S 0).card := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith
  have hb := rootBallUnion_growth_block P h hh.le hexp hrpos F W S 0
    (routingG (Fintype.card V) h) hroots hW hpos hF hg
  have hrootcard : S.card ≤ 2 ^ routingDepth (Fintype.card V) :=
    (Finset.card_le_univ S).trans (le_two_pow_routingDepth _ (by omega))
  obtain ⟨s, hs, hball⟩ := rootBallUnion_extract_root P h hh hexp hrpos F W
    (routingG (Fintype.card V) h) (routingDepth (Fintype.card V))
    hFglobal hg S (routingG (Fintype.card V) h) hroots hW hrootcard (by simpa using hb)
  refine ⟨s, hs, ?_⟩
  have ht : routingG (Fintype.card V) h * (1 + routingDepth (Fintype.card V)) =
      routingG (Fintype.card V) h + routingDepth (Fintype.card V) * routingG (Fintype.card V) h := by ring
  simpa only [ht] using hball

def incidentEdges (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  F.filter (fun e => v ∈ e)

lemma incidentEdges_union {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (F E : Finset (Sym2 V)) (v : V) :
    incidentEdges (F ∪ E) v = incidentEdges F v ∪ incidentEdges E v := by
  simp [incidentEdges, Finset.filter_union]

lemma incidentEdges_union_card_le (F E : Finset (Sym2 V)) (v : V) :
    (incidentEdges (F ∪ E) v).card ≤ (incidentEdges F v).card + (incidentEdges E v).card := by
  rw [incidentEdges_union]
  exact Finset.card_union_le _ _

lemma incidentEdges_sum_le (F : Finset (Sym2 V)) :
    ∑ v : V, (incidentEdges F v).card ≤ 2 * F.card := by
  have heq : ∑ v : V, (incidentEdges F v).card = ∑ e ∈ F, e.toFinset.card := by
    simp only [incidentEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp [← Sym2.mem_toFinset]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e _ => by
      rw [Sym2.card_toFinset]
      split <;> norm_num)
    _ = 2 * F.card := by simp [mul_comm]

lemma incidentEdges_path_start_le_one {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset s).card ≤ 1 := by
  have hsub : incidentEdges p.edges.toFinset s ⊆ {s(s, p.snd)} := by
    intro e he
    obtain ⟨heP, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp hs
    subst e
    have hv := hp.eq_snd_of_mem_edges (List.mem_toFinset.mp heP)
    simp [hv]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma incidentEdges_path_end_le_one (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset t).card ≤ 1 := by
  simpa using incidentEdges_path_start_le_one G p.reverse hp.reverse

lemma incidentEdges_walk_eq_empty_of_not_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t v : V}
    (p : G.Walk s t) (hv : v ∉ p.support) : incidentEdges p.edges.toFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heP, hve⟩ := Finset.mem_filter.mp he
  have hm := p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, List.mem_toFinset.mp heP, hve⟩)
  exact hv hm

lemma incidentEdges_path_le_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) (v : V) :
    (incidentEdges p.edges.toFinset v).card ≤ 2 := by
  by_cases hv : v ∈ p.support
  · have htake := incidentEdges_path_end_le_one G (p.takeUntil v hv) (hp.takeUntil hv)
    have hdrop := incidentEdges_path_start_le_one G (p.dropUntil v hv) (hp.dropUntil hv)
    have heq : p.edges.toFinset = (p.takeUntil v hv).edges.toFinset ∪ (p.dropUntil v hv).edges.toFinset := by
      have he := congrArg (fun q : G.Walk s t => q.edges.toFinset) (p.take_spec hv)
      simpa only [SimpleGraph.Walk.edges_append, List.toFinset_append] using he.symm
    rw [heq]
    exact (incidentEdges_union_card_le _ _ v).trans (by omega)
  · rw [incidentEdges_walk_eq_empty_of_not_mem G p hv]
    simp

lemma deleted_boundary_card_le_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (B : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤
      ∑ v ∈ B, (incidentEdges F v).card := by
  let T := B.biUnion (fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  have hc : ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun e : V × V => (e.1, s(e.1, e.2)))
    · intro e he
      obtain ⟨heP, heF⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨e.1, (P.mem_interedges_iff.mp heP).1, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨heF, by simp⟩
    · intro e he f hf heq
      have hsym := congrArg Prod.snd heq
      exact boundary_sym2_injective P B (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hsym
  have hT : T.card ≤ ∑ v ∈ B, (incidentEdges F v).card := by
    simpa [T] using Finset.card_biUnion_le (s := B)
      (t := fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  exact hc.trans hT

lemma walkBall_growth_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) (t : ℕ)
    (hsmall : ((walkBall (avoidGraph P F W) s t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (walkBall (avoidGraph P F W) s t).card ≤
      ((walkBall (avoidGraph P F W) s (t + 1)).card : ℝ) := by
  classical
  apply routing_union_growth_step_of_boundary P h hexp hr F _ _ (fun _ => W)
      (walkBall_mono _ s (Nat.le_succ t)) hsmall
  · calc
      _ ≤ ∑ v ∈ walkBall (avoidGraph P F W) s t, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P (walkBall (avoidGraph P F W) s t) F
      _ ≤ ∑ _v ∈ walkBall (avoidGraph P F W) s t, h / 4 := Finset.sum_le_sum (fun v _ => hF v)
      _ = _ := by simp; ring
  · exact fun _ _ => hW
  · intro v hv w _ hadj hdel hw
    have hnv := Finset.disjoint_left.mp (ball_avoids P F W s hs t) hv
    exact walkBall_step _ s v w t hv ⟨hadj, hdel, hnv, hw⟩

lemma walkBall_large_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F W) s (routingG (Fintype.card V) h)).card := by
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < Fintype.card V := by linarith
  let g := routingG (Fintype.card V) h
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  by_contra hnot
  have hend := le_of_not_gt hnot
  have hpow : ∀ j ≤ g, c ^ j ≤ (walkBall (avoidGraph P F W) s j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have H := Finset.card_pos.mpr ⟨s, root_mem_walkBall (avoidGraph P F W) s 0⟩
      have H' : 1 ≤ (walkBall (avoidGraph P F W) s 0).card := H
      simpa using (Nat.cast_le (α := ℝ)).mpr H'
    | succ j ih =>
      intro hj
      have hmono : ((walkBall (avoidGraph P F W) s j).card : ℝ) ≤
          (walkBall (avoidGraph P F W) s g).card := by
        exact_mod_cast Finset.card_le_card (walkBall_mono (avoidGraph P F W) s (by omega : j ≤ g))
      have hsmall := hmono.trans hend
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * (walkBall (avoidGraph P F W) s j).card := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ (walkBall (avoidGraph P F W) s (j + 1)).card :=
          walkBall_growth_of_incidents P h hexp hr0 F W s hs hF hW j hsmall
  have hg := routingG_growth (Fintype.card V) h (by linarith) hh (hexp.le_order P h hr)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma exists_short_avoiding_path (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : (avoidGraph P F W).Walk s t, q.IsPath ∧
      q.length ≤ 2 * routingG (Fintype.card V) h := by
  classical
  let g := routingG (Fintype.card V) h
  let B₁ := walkBall (avoidGraph P F W) s g
  let B₂ := walkBall (avoidGraph P F W) t g
  have h₁ := walkBall_large_of_incidents P h hh hexp hr F W s hs hF hW
  have h₂ := walkBall_large_of_incidents P h hh hexp hr F W t ht hF hW
  have hmeet : (B₁ ∩ B₂).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_union_add_card_inter B₁ B₂
    have hu := Finset.card_le_univ (B₁ ∪ B₂)
    have hsum : (Fintype.card V : ℝ) < (B₁.card : ℝ) + (B₂.card : ℝ) := by
      dsimp [B₁, B₂, g]; linarith
    have hsumN : Fintype.card V < B₁.card + B₂.card := by exact_mod_cast hsum
    omega
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨p₁, hp₁⟩ := (mem_walkBall _ s v g).mp (Finset.mem_inter.mp hv).1
  obtain ⟨p₂, hp₂⟩ := (mem_walkBall _ t v g).mp (Finset.mem_inter.mp hv).2
  let w := p₁.append p₂.reverse
  refine ⟨w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans ?_⟩
  dsimp [w]
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

lemma two_routingG_le_length (r h : ℝ) : 2 * routingG r h ≤ routingLength r h := by
  dsimp [routingLength]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma routingLength_bounds (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) :
    1 ≤ routingLength r h ∧ r ≤ (routingLength r h : ℝ) * h := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * r)
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) := Nat.le_ceil _
  have hgh : 8 * r ≤ (routingG r h : ℝ) * h := by
    calc
      8 * r = (8 * (r / h)) * h := by field_simp
      _ ≤ (8 * (r / h) * Real.logb 2 (2 * r)) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (r / h) by positivity)
      _ ≤ (routingG r h : ℝ) * h := mul_le_mul_of_nonneg_right hg hh.le
  have hgpos : 0 < routingG r h := by
    have hgR : (0 : ℝ) < routingG r h := by nlinarith
    exact_mod_cast hgR
  have hgle : routingG r h ≤ routingLength r h := (by omega : routingG r h ≤ 2 * routingG r h).trans (two_routingG_le_length r h)
  refine ⟨by omega, ?_⟩
  have hgleR : (routingG r h : ℝ) ≤ routingLength r h := by exact_mod_cast hgle
  nlinarith

lemma routing_budget (L k b z h r : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hz : 0 ≤ z) (hh : 0 < h) (_hr : 0 ≤ r)
    (hreach : r ≤ L * h) (hbudget : 64 * (L ^ 2 * (k + b) + z) ≤ h) :
    h / 8 + 2 + k ≤ h / 4 ∧ z + b * L ≤ h / 8 ∧ 64 * L * k * r ≤ h ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLLs : L ≤ L ^ 2 := by nlinarith
  have hbig : 64 * (k + b) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : 0 ≤ k + b)]
      _ ≤ _ := hbudget
  have hbL : 64 * (b * L + z) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_left hLLs hb0, mul_nonneg (sq_nonneg L) hk0]
      _ ≤ _ := hbudget
  have hkL : 64 * L ^ 2 * k ≤ h := by nlinarith [mul_nonneg (sq_nonneg L) hb0]
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    64 * L * k * r ≤ 64 * L * k * (L * h) := mul_le_mul_of_nonneg_left hreach (by positivity)
    _ = (64 * L ^ 2 * k) * h := by ring
    _ ≤ h * h := mul_le_mul_of_nonneg_right hkL hh.le
    _ = h ^ 2 := by ring

noncomputable def saturated (F : Finset (Sym2 V)) (h : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => h / 8 ≤ ((incidentEdges F v).card : ℝ))

lemma saturated_card_le (F : Finset (Sym2 V)) (h : ℝ) (hh : 0 < h)
    (hF : 128 * (F.card : ℝ) ≤ h ^ 2) : (saturated F h).card ≤ h / 8 := by
  classical
  have hs : h / 8 * (saturated F h).card ≤ ∑ v : V, ((incidentEdges F v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ saturated F h, h / 8 := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F h, ((incidentEdges F v).card : ℝ) := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsum : (∑ v : V, ((incidentEdges F v).card : ℝ)) ≤ 2 * (F.card : ℝ) := by
    exact_mod_cast incidentEdges_sum_le F
  nlinarith

def pathInterior {P : SimpleGraph V} {s t : V} (q : P.Walk s t) : Finset V :=
  q.support.toFinset \ {s, t}

lemma pathInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : SimpleGraph V} {s t : V} (q : P.Walk s t) :
    (pathInterior q).card ≤ q.length := by
  have hp := List.toFinset_card_le q.support
  rw [q.length_support] at hp
  have hstart : s ∈ q.support.toFinset ∩ ({s, t} : Finset V) := by simp
  have hint := Finset.card_pos.mpr ⟨s, hstart⟩
  have hd := Finset.card_sdiff_add_card_inter q.support.toFinset ({s, t} : Finset V)
  dsimp [pathInterior]
  omega

lemma avoidGraph_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    avoidGraph P F W ≤ P := fun _ _ h => h.1

lemma walk_avoids_support (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) (hs : s ∉ W) :
    Disjoint q.support.toFinset W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  exact walk_avoids_end P F W (q.takeUntil v (List.mem_toFinset.mp hv)) hs

lemma walk_avoids_edges {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) :
    Disjoint q.edges.toFinset F := by
  apply Finset.disjoint_left.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w => exact (q.adj_of_mem_edges (List.mem_toFinset.mp he)).2.1

lemma exists_short_path_with_avoidance (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ routingLength (Fintype.card V) h ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  obtain ⟨q, hp, hl⟩ := exists_short_avoiding_path P h hh hexp hr F W s t hs ht hF hW
  refine ⟨q.mapLe (avoidGraph_le P F W), hp.mapLe _, ?_, ?_, ?_⟩
  · simpa using hl.trans (two_routingG_le_length (Fintype.card V) h)
  · simpa using walk_avoids_edges P F W q
  · simpa using walk_avoids_support P F W q hs

lemma route_degree_update {P : SimpleGraph V} {s t : V} (q : P.Walk s t)
    (hp : q.IsPath) (F : Finset (Sym2 V)) (h : ℝ) (load : V → ℕ)
    (hdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 8 + 2 + load v)
    (havoid : Disjoint q.support.toFinset (saturated F h \ {s, t})) (v : V) :
    ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      h / 8 + 2 + load v + (if v = s ∨ v = t then 1 else 0) := by
  classical
  have hadd : ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      (incidentEdges F v).card + (incidentEdges q.edges.toFinset v).card := by
    exact_mod_cast incidentEdges_union_card_le F q.edges.toFinset v
  by_cases hv : v = s ∨ v = t
  · rw [if_pos hv]
    have hqN : (incidentEdges q.edges.toFinset v).card ≤ 1 := by
      rcases hv with rfl | rfl
      · exact incidentEdges_path_start_le_one P q hp
      · exact incidentEdges_path_end_le_one P q hp
    have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 1 := by exact_mod_cast hqN
    linarith [hdegree v]
  · rw [if_neg hv]
    by_cases hmem : v ∈ q.support
    · have hns : v ∉ saturated F h := by
        intro hsat
        apply Finset.disjoint_left.mp havoid (List.mem_toFinset.mpr hmem)
        exact Finset.mem_sdiff.mpr ⟨hsat, by simpa using hv⟩
      have hsmall : ((incidentEdges F v).card : ℝ) < h / 8 := by
        simpa [saturated] using hns
      have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 2 := by
        exact_mod_cast incidentEdges_path_le_two P q hp v
      have : (0 : ℝ) ≤ load v := by positivity
      linarith
    · rw [incidentEdges_walk_eq_empty_of_not_mem P q hmem] at hadd
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hadd
      linarith [hdegree v]

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

def endpointLoad (A : Finset I) (x y : I → V) (v : V) : ℕ :=
  (A.filter (fun i => x i = v ∨ y i = v)).card

lemma endpointLoad_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {A B : Finset I} (hAB : A ⊆ B) (x y : I → V) (v : V) :
    endpointLoad A x y v ≤ endpointLoad B x y v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

lemma endpointLoad_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (i : I) (hi : i ∉ A) (x y : I → V) (v : V) :
    endpointLoad (insert i A) x y v = endpointLoad A x y v +
      (if v = x i ∨ v = y i then 1 else 0) := by
  classical
  by_cases hv : v = x i ∨ v = y i
  · have hv' : x i = v ∨ y i = v := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv', hi]
  · have hv' : ¬ (x i = v ∨ y i = v) := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv']

lemma endpointLoad_sum {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (x y : I → V) (hxy : ∀ i ∈ A, x i ≠ y i) :
    ∑ v : V, endpointLoad A x y v = 2 * A.card := by
  classical
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have heq : ∀ i ∈ A, (∑ v : V, if x i = v ∨ y i = v then 1 else 0) = 2 := by
    intro i hi
    have hf : (Finset.univ.filter fun v => x i = v ∨ y i = v) = ({x i, y i} : Finset V) := by
      ext v
      simp [eq_comm]
    have hc : ({x i, y i} : Finset V).card = 2 := by simp [hxy i hi]
    rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ _i ∈ A, 2 := Finset.sum_congr rfl heq
    _ = _ := by simp [mul_comm]

noncomputable def usedEdges (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) : Finset (Sym2 V) :=
  A.biUnion (fun i => (q i).edges.toFinset)

lemma usedEdges_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) (L : ℕ)
    (hq : ∀ i ∈ A, (q i).length ≤ L) : (usedEdges A q).card ≤ L * A.card := by
  calc
    _ ≤ ∑ i ∈ A, (q i).edges.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, L := Finset.sum_le_sum (fun i hi => by
      have hc := List.toFinset_card_le (q i).edges
      simpa using hc.trans (by simpa using hq i hi))
    _ = _ := by simp [mul_comm]

lemma usedEdges_update_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (i : I) (hi : i ∉ A)
    (q : ∀ j, P.Walk (x j) (y j)) (p : P.Walk (x i) (y i)) :
    usedEdges (insert i A) (Function.update q i p) = usedEdges A q ∪ p.edges.toFinset := by
  classical
  rw [usedEdges, Finset.biUnion_insert]
  simp only [Function.update_self]
  rw [Finset.union_comm]
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

noncomputable def teamInterior (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) : Finset V :=
  (A.filter (fun j => team j = team i)).biUnion (fun j => pathInterior (q j))

lemma teamInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} {T : Type} [_contextInstance5 : Fintype I] [_contextInstance6 : DecidableEq I] [_contextInstance7 : DecidableEq T] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) (L : ℕ) (b : ℝ)
    (hq : ∀ j ∈ A, (q j).length ≤ L)
    (hb : ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b) :
    ((teamInterior A q team i).card : ℝ) ≤ b * L := by
  have hc : (teamInterior A q team i).card ≤ L * (A.filter (fun j => team j = team i)).card := by
    calc
      _ ≤ ∑ j ∈ A.filter (fun j => team j = team i), (pathInterior (q j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A.filter (fun j => team j = team i), L := Finset.sum_le_sum (fun j hj =>
        (pathInterior_card_le (q j)).trans (hq j (Finset.mem_filter.mp hj).1))
      _ = _ := by simp [mul_comm]
  have hcard : ((A.filter (fun j => team j = team i)).card : ℝ) ≤ b := by
    apply le_trans _ hb
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
  have hcR : ((teamInterior A q team i).card : ℝ) ≤ (L : ℝ) * (A.filter (fun j => team j = team i)).card := by exact_mod_cast hc
  calc
    _ ≤ (L : ℝ) * b := hcR.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = _ := mul_comm _ _

structure PartialRoutes (P : SimpleGraph V) (x y : I → V) (team : I → T)
    (Z : I → Finset V) (L : ℕ) (h : ℝ) (A : Finset I)
    (q : ∀ i, P.Walk (x i) (y i)) : Prop where
  simple : ∀ i ∈ A, (q i).IsPath
  short : ∀ i ∈ A, (q i).length ≤ L
  avoids : ∀ i ∈ A, Disjoint (pathInterior (q i)) (Z i)
  edge_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset
  team_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))
  degree : ∀ v, ((incidentEdges (usedEdges A q) v).card : ℝ) ≤ h / 8 + 2 + endpointLoad A x y v

theorem routing (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ) ^ 2 * (k + b) + z) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let L := routingLength (Fintype.card V) h
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  obtain ⟨hL, hreach⟩ := routingLength_bounds (Fintype.card V) h (by linarith) hh
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hdegBudget, hforbidBudget, hnumBudget⟩ := routing_budget L k b z h (Fintype.card V)
    hLR hk hb hz hh (by positivity) hreach hbudget
  have hloadA : ∀ (A : Finset I) v, (endpointLoad A x y v : ℝ) ≤ k := by
    intro A v
    have hm : (endpointLoad A x y v : ℝ) ≤ endpointLoad Finset.univ x y v := by
      exact_mod_cast endpointLoad_mono (Finset.subset_univ A) x y v
    exact hm.trans (hload v)
  have htotal : 2 * (Fintype.card I : ℝ) ≤ k * Fintype.card V := by
    have heq := endpointLoad_sum Finset.univ x y (fun i _ => hxy i)
    have heqR : (∑ v : V, (endpointLoad Finset.univ x y v : ℝ)) = 2 * Fintype.card I := by
      exact_mod_cast heq
    rw [← heqR]
    calc
      _ ≤ ∑ _v : V, k := Finset.sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [mul_comm]
  have hdefault : ∀ i, ∃ p : P.Walk (x i) (y i), p.IsPath := by
    intro i
    obtain ⟨p, hp, _⟩ := exists_short_path_with_avoidance P h hh hexp hr ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨p, hp⟩
  choose defaultPath hdefaultPath using hdefault
  have hpartial : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i), PartialRoutes P x y team Z L h A q := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultPath, ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [usedEdges, Finset.biUnion_empty, incidentEdges, Finset.filter_empty,
          Finset.card_empty, Nat.cast_zero, endpointLoad, add_zero]
        linarith
    | @insert i A hi ih =>
      obtain ⟨q, hq⟩ := ih
      let F := usedEdges A q
      let S := saturated F h
      let B := teamInterior A q team i
      let W := (S ∪ Z i ∪ B) \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hc : (F.card : ℝ) ≤ (L : ℝ) * A.card := by
          exact_mod_cast usedEdges_card_le A q L hq.short
        have ha : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ A
        have hsize : 2 * (A.card : ℝ) ≤ k * Fintype.card V := by linarith
        have hmult := mul_le_mul_of_nonneg_left hsize (show 0 ≤ (L : ℝ) by positivity)
        nlinarith [hnumBudget]
      have hS : (S.card : ℝ) ≤ h / 8 := saturated_card_le F h hh hFcard
      have hB : (B.card : ℝ) ≤ b * L := teamInterior_card_le A q team i L b hq.short (hteam i)
      have hW : (W.card : ℝ) ≤ h / 4 := by
        have hc : W.card ≤ S.card + (Z i).card + B.card :=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        have hcR : (W.card : ℝ) ≤ (S.card : ℝ) + (Z i).card + B.card := by exact_mod_cast hc
        linarith [hZ i]
      have hFdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        intro v
        have hd := hq.degree v
        have hl := hloadA A v
        dsimp [F]
        linarith
      obtain ⟨p, hp, hpL, hpF, hpW⟩ := exists_short_path_with_avoidance P h hh hexp hr F W (x i) (y i)
        (by simp [W]) (by simp [W]) hFdegree hW
      have hpZ : Disjoint (pathInterior p) (Z i) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvZ
        obtain ⟨hvp, hvends⟩ := Finset.mem_sdiff.mp hv
        apply Finset.disjoint_left.mp hpW hvp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hvZ), hvends⟩
      have hpS : Disjoint p.support.toFinset (saturated F h \ {x i, y i}) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvS
        obtain ⟨hs, he⟩ := Finset.mem_sdiff.mp hvS
        apply Finset.disjoint_left.mp hpW hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hs), he⟩
      have hpEdge : ∀ j ∈ A, Disjoint p.edges.toFinset (q j).edges.toFinset := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro e hep heq
        exact Finset.disjoint_left.mp hpF hep (Finset.mem_biUnion.mpr ⟨j, hj, heq⟩)
      have hpTeam : ∀ j ∈ A, team i = team j → Disjoint (pathInterior p) (pathInterior (q j)) := by
        intro j hj htm
        apply Finset.disjoint_left.mpr
        intro v hvp hvq
        obtain ⟨hvp', hvends⟩ := Finset.mem_sdiff.mp hvp
        apply Finset.disjoint_left.mp hpW hvp'
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ ?_, hvends⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, htm.symm⟩, hvq⟩
      let q' := Function.update q i p
      have hsame : q' i = p := Function.update_self i p q
      have hother : ∀ j ∈ A, q' j = q j := by
        intro j hj
        apply Function.update_of_ne
        intro hji
        exact hi (hji ▸ hj)
      refine ⟨q', ?_⟩
      constructor
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hp
        · simpa only [hother j hj] using hq.simple j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpL
        · simpa only [hother j hj] using hq.short j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpZ
        · simpa only [hother j hj] using hq.avoids j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpEdge k hkA
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpEdge j hjA).symm
          · simpa only [hother j hjA, hother k hkA] using hq.edge_disjoint j hjA k hkA hjk
      · intro j hj k hk hjk htm
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpTeam k hkA htm
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpTeam j hjA htm.symm).symm
          · simpa only [hother j hjA, hother k hkA] using hq.team_disjoint j hjA k hkA hjk htm
      · intro v
        have heq : usedEdges (insert i A) q' = F ∪ p.edges.toFinset := usedEdges_update_insert A i hi q p
        rw [heq]
        have hu := route_degree_update p hp F h (endpointLoad A x y) hq.degree hpS v
        have hloadEq : (endpointLoad (insert i A) x y v : ℝ) =
            endpointLoad A x y v + (if v = x i ∨ v = y i then (1 : ℝ) else 0) := by
          rw [endpointLoad_insert A i hi]
          split_ifs <;> simp
        rw [hloadEq]
        simpa only [add_assoc] using hu
  obtain ⟨q, hq⟩ := hpartial Finset.univ
  exact ⟨q, fun i => ⟨hq.simple i (by simp), hq.short i (by simp), hq.avoids i (by simp)⟩,
    fun i j hij => hq.edge_disjoint i (by simp) j (by simp) hij,
    fun i j hij htm => hq.team_disjoint i (by simp) j (by simp) hij htm⟩

end Families
end ErdosGallai

end
end
end

end OAI


-- Upstream module ReservoirCycles

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Real Filter Asymptotics

lemma routing_length_upper (r h : ℝ) (hr : 2 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    (routingLength r h : ℝ) ≤ 108*(r/h)*(logb 2 r)^2 := by
  have hr0 : 0 < r := by linarith
  have hl : 1 ≤ logb 2 r := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 2) hr
  have hR : 1 ≤ r/h := (le_div_iff₀ hh).mpr (by simpa using hhr)
  have hlog : logb 2 (2*r) = 1 + logb 2 r := by
    rw [Real.logb_mul (by norm_num) hr0.ne']
    norm_num
  have hg := Nat.ceil_lt_add_one (show 0 ≤ 8*(r/h)*logb 2 (2*r) by rw [hlog]; positivity)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ logb 2 r by linarith)
  change (routingG r h : ℝ) < 8*(r/h)*logb 2 (2*r)+1 at hg
  change (routingDepth r : ℝ) < logb 2 r + 1 at hd
  rw [hlog] at hg
  have hprod : 1 ≤ (r/h)*logb 2 r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
  have hg' : (routingG r h : ℝ) ≤ 18*(r/h)*logb 2 r := by nlinarith
  have hd' : (1 + routingDepth r : ℝ) ≤ 3*logb 2 r := by linarith
  have hm := mul_le_mul hg' hd' (by positivity) (by positivity)
  dsimp [routingLength]
  push_cast
  nlinarith

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

theorem eventually_routing_length (c β γ δ : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 2 ≤ r → r ≤ D^β → c*D^γ ≤ r →
      (routingLength r (c*D^γ) : ℝ) ≤ D^(β-γ+δ) := by
  filter_upwards [eventually_logb_le_power (δ/4) (by positivity),
    eventually_constant_le_power (108*β^2/c) (δ/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with D hlog hconst hD r hr hrD hhr
  have hD0 : 0 < D := by linarith
  have hpowγ : 0 < D^γ := Real.rpow_pos_of_pos hD0 _
  have hden : 0 < c*D^γ := mul_pos hc hpowγ
  have hlog0 : 0 ≤ logb 2 r := (Real.logb_pos (by norm_num) (by linarith)).le
  have hlogR : logb 2 r ≤ β*D^(δ/4) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by linarith : 0 < r) hrD
    rw [Real.logb_rpow_eq_mul_logb_of_pos hD0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog hβ.le)
  have hratio : r/(c*D^γ) ≤ D^(β-γ)/c := by
    calc
      _ ≤ D^β/(c*D^γ) := div_le_div_of_nonneg_right hrD hden.le
      _ = _ := by rw [Real.rpow_sub hD0]; ring
  have hsq : (logb 2 r)^2 ≤ β^2*D^(δ/2) := by
    calc
      _ ≤ (β*D^(δ/4))^2 := pow_le_pow_left₀ hlog0 hlogR 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]; congr 2; ring
  calc
    (routingLength r (c*D^γ) : ℝ) ≤ 108*(r/(c*D^γ))*(logb 2 r)^2 :=
      routing_length_upper r (c*D^γ) hr hden hhr
    _ ≤ 108*(D^(β-γ)/c)*(β^2*D^(δ/2)) := by gcongr
    _ = (108*β^2/c)*D^(β-γ+δ/2) := by rw [Real.rpow_add hD0]; ring
    _ ≤ D^(δ/2)*D^(β-γ+δ/2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hD0.le _)
    _ = D^(β-γ+δ) := by rw [← Real.rpow_add hD0]; congr 1; ring

theorem batch_routing_margin : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
    2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
      (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, D^(9/10:ℝ) ≤ r → r ≤ D^(51/50:ℝ) →
      2 ≤ r ∧ 64*((routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ))+2*D^(3/10:ℝ)) ≤ D^(9/10:ℝ)/4 := by
    filter_upwards [eventually_routing_length (1/4) (51/50) (9/10) (2/25)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_const_mul_power_le 1024 (7/10) (9/10) (by norm_num),
      eventually_constant_le_power 2 (9/10) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcost htwo hD r hr hrD
    have hD0 : 0 < D := by linarith
    have hr2 : 2 ≤ r := htwo.trans hr
    have hh : (1/4)*D^(9/10:ℝ) ≤ r := by
      have hh0 := Real.rpow_nonneg hD0.le (9/10:ℝ)
      linarith
    have hL := hlen r hr2 hrD hh
    norm_num at hL
    have hL' : (routingLength r (D^(9/10:ℝ)/4) : ℝ) ≤ D^(1/5:ℝ) := by
      convert hL using 1 ; ring_nf
    have hsmall : D^(1/100:ℝ) ≤ D^(3/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have h37 : D^(3/10:ℝ) ≤ D^(7/10:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
    have hprod : (routingLength r (D^(9/10:ℝ)/4) : ℝ)^2*
        (D^(1/100:ℝ)+D^(3/10:ℝ)) ≤ 2*D^(7/10:ℝ) := by
      calc
        _ ≤ (D^(1/5:ℝ))^2 * (2*D^(3/10:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    refine ⟨hr2, ?_⟩
    nlinarith only [hprod, h37, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

lemma eventually_reservoir_capacity (c : ℝ) (hc : 0 < c) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ D^(51/50:ℝ) →
      (⌈8*r/(thinning D*(c*D^(9/10:ℝ)))⌉₊ : ℝ) ≤ D^(13/100:ℝ) := by
  filter_upwards [eventually_const_mul_power_le (8/c+1) (1/8) (13/100) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with D hbound hD r hr hrD
  have hD0 : 0 < D := by linarith
  have hpa : thinning D * (c * D ^ (9 / 10 : ℝ)) = c * D ^ (179 / 200 : ℝ) := by
    rw [mul_left_comm, thinning_mul_power hD0]
    norm_num
  have hden : 0 < thinning D*(c*D^(9/10:ℝ)) := by rw [hpa]; positivity
  have hone : 1 ≤ D^(1/8:ℝ) := Real.one_le_rpow hD.le (by norm_num)
  have hx : 8*r/(thinning D*(c*D^(9/10:ℝ))) ≤ (8/c)*D^(1/8:ℝ) := by
    calc
      _ ≤ 8*D^(51/50:ℝ)/(thinning D*(c*D^(9/10:ℝ))) := by gcongr
      _ = _ := by
        have heq : D^(1/8:ℝ) = D^(51/50:ℝ)/D^(179/200:ℝ) := by
          rw [← Real.rpow_sub hD0]; norm_num
        rw [heq, hpa]; ring
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 8*r/(thinning D*(c*D^(9/10:ℝ))) by rw [hpa]; positivity)
  nlinarith only [hx, hceil, hone, hbound]

theorem residue_routing_margin (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(thinning D*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(thinning D*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
    filter_upwards [eventually_routing_length 1 (51/50) (37/50) (1/100)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_reservoir_capacity c hc,
      eventually_const_mul_power_le 128 (71/100) (37/50) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcap hcost hD r rᵢ hr hrD hri2 hrir htau
    have hD0 : 0 < D := by linarith
    have hL := hlen rᵢ hri2 (hrir.trans hrD) (by simpa using htau)
    norm_num at hL
    have hk := hcap r hr hrD
    have hone : 1 ≤ D^(13/100:ℝ) := Real.one_le_rpow hD.le (by norm_num)
    have hprod : (routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(thinning D*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1) ≤ 2*D^(71/100:ℝ) := by
      calc
        _ ≤ (D^(29/100:ℝ))^2 * (2*D^(13/100:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    nlinarith only [hprod, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansionOn (P : SimpleGraph V) [DecidableRel P.Adj] (W : Finset V) (h : ℝ) : Prop :=
  ∀ A : Finset V, A ⊆ W → h * min (A.card : ℝ) ((W \ A).card : ℝ) ≤
    ((P.interedges A (W \ A)).card : ℝ)

lemma subtype_image_compl {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W : Finset V) (U : Finset (W : Set V)) :
    Uᶜ.image Subtype.val = W \ U.image Subtype.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx (Subtype.ext he ▸ hy)
  · rintro ⟨hv,hvU⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro hx
    exact hvU ⟨⟨v,hv⟩,hx,rfl⟩

lemma induced_interedges_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (U : Finset (W : Set V)) :
    (((P.induce (W : Set V)).interedges U Uᶜ).card : ℝ) =
      ((P.interedges (U.image Subtype.val) (W \ U.image Subtype.val)).card : ℝ) := by
  classical
  let f : ↥(W : Set V) × ↥(W : Set V) → V × V := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have heq : ((P.induce (W : Set V)).interedges U Uᶜ).image f =
      P.interedges (U.image Subtype.val) (W \ U.image Subtype.val) := by
    rw [← subtype_image_compl W U]
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩
      exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
    · rintro ⟨⟨x,hx,hxe⟩,⟨y,hy,hye⟩,he⟩
      refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext hxe hye⟩
      change P.Adj x.val y.val
      simpa only [hxe,hye] using he
  rw [← heq, Finset.card_image_of_injective _ hf]

lemma cutExpansion_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (hexp : CutExpansionOn P W h) :
    CutExpansion (P.induce (W : Set V)) h := by
  classical
  intro U
  have hsub : U.image Subtype.val ⊆ W := by
    rintro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have h := hexp (U.image Subtype.val) hsub
  have he : W \ U.image Subtype.val = Uᶜ.image Subtype.val :=
    (subtype_image_compl W U).symm
  rw [he] at h
  simp only [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [induced_interedges_card,he]
  exact h

theorem routing_allow_equal {I : Type} [Fintype I]
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) := by
  classical
  let J := {i : I // x i ≠ y i}
  have hjload (v : V) :
      (endpointLoad Finset.univ (fun i : J => x i.val) (fun i : J => y i.val) v : ℝ) ≤ k := by
    apply le_trans _ (hload v)
    exact_mod_cast (show endpointLoad Finset.univ (fun i : J => x i.val)
        (fun i : J => y i.val) v ≤ endpointLoad Finset.univ x y v from by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
      · intro a _ b _ hab
        exact Subtype.ext hab)
  obtain ⟨q,hq,hd,_⟩ := routing P h hh hexp hr
    (fun i : J => x i.val) (fun i : J => y i.val) (fun i => i.property)
    (fun i : J => i) (fun _ => ∅) k 1 0 hk (by norm_num) (by norm_num) hjload
    (by
      intro i
      have he : (univ.filter (fun j : J => j = i)) = {i} := by ext j; simp
      rw [he]; simp) (by intro i; simp) (by simpa only [add_zero] using hbudget)
  let Q : ∀ i, P.Walk (x i) (y i) := fun i =>
    if hi : x i = y i then (SimpleGraph.Walk.nil : P.Walk (x i) (x i)).copy rfl hi
    else q ⟨i,hi⟩
  refine ⟨Q,?_,?_⟩
  · intro i
    by_cases hi : x i = y i
    · simp [Q,hi]
    · simpa only [Q,dif_neg hi] using ⟨(hq ⟨i,hi⟩).1,(hq ⟨i,hi⟩).2.1⟩
  · intro i j hij
    by_cases hi : x i = y i
    · simp [Q,hi]
    by_cases hj : x j = y j
    · simp [Q,hj]
    simp only [Q,dif_neg hi,dif_neg hj]
    exact hd ⟨i,hi⟩ ⟨j,hj⟩ (fun he => hij (congrArg Subtype.val he))

theorem routing_in_reservoir {I : Type} [Fintype I]
    (G P : SimpleGraph V) [DecidableRel P.Adj] (hPG : P ≤ G)
    (W : Finset V) (h : ℝ) (hh : 0 < h)
    (hexp : CutExpansionOn P W h) (hr : 2 ≤ W.card)
    (x y : I → V) (hx : ∀ i, x i ∈ W) (hy : ∀ i, y i ∈ W)
    (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength W.card h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card h ∧
        ∀ v ∈ (q i).support, v ∈ W) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  classical
  let X : I → (W : Set V) := fun i => ⟨x i,hx i⟩
  let Y : I → (W : Set V) := fun i => ⟨y i,hy i⟩
  have hl (v : (W : Set V)) : (endpointLoad univ X Y v : ℝ) ≤ k := by
    simpa only [endpointLoad,X,Y,Subtype.ext_iff] using hload v.val
  obtain ⟨q,hq,hd⟩ := routing_allow_equal (P.induce (W : Set V)) h hh
    (cutExpansion_induce P W h hexp) (by simpa using hr) X Y k hk hl
    (by simpa using hbudget)
  let f : (P.induce (W : Set V)) →g G :=
    { toFun := Subtype.val, map_rel' := fun ha => hPG ha }
  have hf : Function.Injective f := Subtype.val_injective
  have hcard : Fintype.card ↥(W : Set V) = W.card := Fintype.card_coe W
  let Q : ∀ i, G.Walk (x i) (y i) := fun i => (q i).map f
  refine ⟨Q,?_,?_⟩
  · intro i
    refine ⟨(hq i).1.map hf,?_,?_⟩
    · simpa only [Q,SimpleGraph.Walk.length_map, hcard] using (hq i).2
    · intro v hv
      have hv' : v ∈ (q i).support.map f := by simpa only [Q,SimpleGraph.Walk.support_map] using hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv'
      exact a.property
  · intro i j hij
    change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet
    rw [SimpleGraph.Walk.edgeSet_map,SimpleGraph.Walk.edgeSet_map]
    rw [Set.disjoint_image_iff (Sym2.map.injective hf)]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (hd i j hij)
      (by simpa using he) (by simpa using he')

theorem uniform_reservoir_routing (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ∈ W) → (∀ i, y i ∈ W) →
      (∀ v, endpointLoad univ x y v ≤
        ⌈8*(Fintype.card V:ℝ)/(thinning D*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  obtain ⟨D₀,hD₀,hmargin⟩ := residue_routing_margin c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hx hy hl
  have hDpos : 0 < D := lt_trans (by norm_num) (hD₀.trans_le hD)
  have horder : (D^(37/50:ℝ)) ≤ (W.card : ℝ) := by
    simpa using (cutExpansion_induce P W _ hexp).le_order (P.induce (W:Set V)) _
      (by simpa using hW)
  have hWupper : (W.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast W.card_le_univ
  have hrpos : 0 < (Fintype.card V : ℝ) := by
    have hWreal : (2:ℝ) ≤ W.card := by exact_mod_cast hW
    linarith
  have hk : 1 ≤ (⌈8*(Fintype.card V:ℝ)/(thinning D*(c*D^(9/10:ℝ)))⌉₊ : ℝ) := by
    have hceil : 0 < ⌈8*(Fintype.card V:ℝ)/(thinning D*(c*D^(9/10:ℝ)))⌉₊ :=
      Nat.ceil_pos.mpr (by have := thinning_pos hDpos; positivity)
    exact_mod_cast hceil
  apply routing_in_reservoir G P hPG W (D^(37/50:ℝ)) (by positivity) hexp hW
    x y hx hy _ hk (by intro v; exact_mod_cast hl v)
  exact hmargin D hD _ _ hrpos.le hr (by exact_mod_cast hW) hWupper horder

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem occurrence_slots {A : Type cycleUniverse1} {V : Type cycleUniverse2} [Fintype A] (f : A → V) (k : ℕ)
    (h : ∀ v, Fintype.card {a // f a = v} ≤ k) :
    ∃ slot : A → Fin k, Function.Injective (fun a => (f a, slot a)) := by
  classical
  have he : ∀ v, Nonempty ({a // f a = v} ↪ Fin k) := by
    intro v
    exact Function.Embedding.nonempty_of_card_le (by simpa using h v)
  let e := fun v => Classical.choice (he v)
  refine ⟨fun a => e (f a) ⟨a,rfl⟩, ?_⟩
  intro a b hab
  have hf : f a = f b := congrArg Prod.fst hab
  have hs : e (f a) ⟨a,rfl⟩ = e (f b) ⟨b,rfl⟩ := congrArg Prod.snd hab
  have hσ : (⟨f a, e (f a) ⟨a,rfl⟩⟩ : Σ _ : V, Fin k) =
      ⟨f b, e (f b) ⟨b,rfl⟩⟩ := Sigma.ext hf (heq_of_eq hs)
  let E : (Σ v, {a // f a = v}) ↪ (Σ _ : V, Fin k) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl V) e
  have heq : (⟨f a, ⟨a,rfl⟩⟩ : Σ v, {a // f a = v}) = ⟨f b, ⟨b,rfl⟩⟩ :=
    E.injective hσ
  exact congrArg (fun z : Σ v, {a // f a = v} => z.2.val) heq

def endpointOccurrence {I : Type cycleUniverse3} {V : Type cycleUniverse4} (x y : I → V) (a : I × Fin 2) : V :=
  if a.2 = 0 then x a.1 else y a.1

theorem endpoint_occurrence_slots {I : Type cycleUniverse5} {V : Type cycleUniverse6} [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, (univ.filter (fun i => x i = v ∨ y i = v)).card ≤ 2) :
    ∃ slot : I × Fin 2 → Fin 2,
      Function.Injective (fun a => (endpointOccurrence x y a, slot a)) := by
  classical
  apply occurrence_slots
  intro v
  let f : {a : I × Fin 2 // endpointOccurrence x y a = v} →
      {i : I // x i = v ∨ y i = v} := fun a =>
    ⟨a.val.1, by
      by_cases h0 : a.val.2 = 0
      · exact Or.inl (by simpa [endpointOccurrence,h0] using a.property)
      · exact Or.inr (by simpa [endpointOccurrence,h0] using a.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hi : a.val.1 = b.val.1 := congrArg Subtype.val hab
    apply Prod.ext hi
    by_contra ht
    have hcases : (a.val.2 = 0 ∧ b.val.2 ≠ 0) ∨ (a.val.2 ≠ 0 ∧ b.val.2 = 0) := by
      have ha := (a.val.2).isLt
      have hb := (b.val.2).isLt
      have hne : (a.val.2).val ≠ (b.val.2).val := fun h => ht (Fin.ext h)
      simp only [Fin.ext_iff, Fin.val_zero]
      omega
    rcases hcases with h | h
    · have ha : x a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : y b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ (ha.trans (hi ▸ hb).symm)
    · have ha : y a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : x b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ ((hi ▸ hb).trans ha.symm)
  exact (Fintype.card_le_of_injective f hf).trans (by simpa only [Fintype.card_subtype] using hload v)

theorem reserved_edges_injective {A : Type cycleUniverse7} {V : Type cycleUniverse8} (S W : Set V)
    (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (hin : ∀ v ∈ S, ∀ t, r (v,t) ∈ W)
    (hdisj : Disjoint S W) (hr : ∀ v ∈ S, r (v,0) ≠ r (v,1)) :
    Function.Injective (fun a => s(f a,r (f a,slot a))) := by
  intro a b hab
  rcases Sym2.eq_iff.mp hab with he | he
  · have hf : f a = f b := he.1
    have hh : r (f a,slot a) = r (f b,slot b) := he.2
    apply hslots
    apply Prod.ext hf
    have hrinj : Function.Injective (fun t : Fin 2 => r (f a,t)) := by
      intro i j hij
      have h0 := hr (f a) (hout a)
      fin_cases i <;> fin_cases j
      · rfl
      · exact (h0 hij).elim
      · exact (h0 hij.symm).elim
      · rfl
    exact hrinj (by simpa only [hf] using hh)
  · have hf : f a = r (f b,slot b) := he.1
    exact False.elim (Set.disjoint_left.mp hdisj (hout a)
      (hf.symm ▸ hin (f b) (hout b) (slot b)))

theorem assigned_representative_load {A : Type cycleUniverse9} {V : Type cycleUniverse10} [Fintype A] [DecidableEq V]
    (S : Finset V) (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (k : ℕ)
    (hcap : ∀ v, ((S ×ˢ univ).filter (fun a => r a = v)).card ≤ k) :
    ∀ v, (univ.filter (fun a => r (f a,slot a) = v)).card ≤ k := by
  classical
  intro v
  apply le_trans (Finset.card_le_card_of_injOn (fun a => (f a,slot a)) ?_ ?_) (hcap v)
  · intro a ha
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hout a,mem_univ _⟩, (mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact hslots hab

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem choose_reservoir_endpoints {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] (P : SimpleGraph V) (W : Finset V)
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (houtx : ∀ i, x i ∉ W) (houty : ∀ i, y i ∉ W)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2)
    (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t)))
    (hrne : ∀ v, v ∉ W → r (v,0) ≠ r (v,1))
    (k : ℕ) (hcap : ∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤ k) :
    ∃ a b : I → V,
      (∀ i, a i ∈ W ∧ P.Adj (x i) (a i)) ∧
      (∀ i, b i ∈ W ∧ P.Adj (y i) (b i)) ∧
      Function.Injective (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
      (∀ v, endpointLoad univ a b v ≤ k) ∧
      (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  classical
  obtain ⟨slot,hslot⟩ := endpoint_occurrence_slots x y hne (fun v => by
    convert hload v using 1
    congr 1
    ext i
    simp only [ Finset.mem_filter, Finset.mem_univ, true_and])
  let occ := endpointOccurrence x y
  have ho : ∀ z : I × Fin 2, occ z ∉ W := by
    rintro ⟨i,t⟩
    by_cases h : t = 0
    · simpa [occ,endpointOccurrence,h] using houtx i
    · simpa [occ,endpointOccurrence,h] using houty i
  let a := fun i => r (x i,slot (i,0))
  let b := fun i => r (y i,slot (i,1))
  have hsp := reserved_edges_injective (Wᶜ : Finset V) W occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z))
    (fun v hv t => (hr v (Finset.mem_compl.mp hv) t).1)
    (Set.disjoint_left.mpr (fun _ hv hw => (Finset.mem_compl.mp hv) hw))
    (fun v hv => hrne v (Finset.mem_compl.mp hv))
  have hcap' := assigned_representative_load Wᶜ occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z)) k hcap
  refine ⟨a,b,(fun i => hr _ (houtx i) _),(fun i => hr _ (houty i) _),?_,?_,?_,?_⟩
  · have heq : (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) =
        (fun z => s(occ z,r (occ z,slot z))) := by
      funext z
      rcases z with ⟨i,t⟩
      fin_cases t <;> simp [occ,endpointOccurrence,a,b]
    rw [heq]
    exact hsp
  · intro v
    apply le_trans (Finset.card_le_card_of_injOn
      (fun i => (i,if a i = v then (0 : Fin 2) else 1)) ?_ ?_) (hcap' v)
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_cases hi0 : a i = v
      · simp [hi0,occ,endpointOccurrence,a]
      · have hi1 : b i = v := hi'.resolve_left hi0
        simpa [hi0,occ,endpointOccurrence,b] using hi1
    · intro i hi j hj he
      exact congrArg Prod.fst he
  · intro i; exact ⟨slot (i,0),rfl⟩
  · intro i; exact ⟨slot (i,1),rfl⟩

theorem uniform_assigned_reservoir_routing (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ≠ y i) → (∀ i, x i ∉ W) → (∀ i, y i ∉ W) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(thinning D*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i)),
        (∀ i, G.Adj (x i) (a i) ∧ G.Adj (y i) (b i)) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet) := by
  obtain ⟨D₀,hD₀,hroute⟩ := uniform_reservoir_routing c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hne hx hy hl r hrep hrepne hcap
  obtain ⟨a,b,ha,hb,hs,hl',ha',hb'⟩ :=
    choose_reservoir_endpoints P W x y hne hx hy hl r hrep hrepne _ hcap
  obtain ⟨q,hq,hd⟩ := hroute D hD V P P le_rfl W hexp hW hr I a b
    (fun i => (ha i).1) (fun i => (hb i).1) hl'
  let Q : ∀ i, G.Walk (a i) (b i) := fun i => (q i).mapLe hPG
  refine ⟨a,b,Q,(fun i => ⟨hPG (ha i).2,hPG (hb i).2⟩),hs,?_,?_,ha',hb',?_⟩
  · intro i
    refine ⟨(hq i).1.mapLe hPG,?_,?_⟩
    · simpa only [Q, SimpleGraph.Walk.length_mapLe] using (hq i).2.1
    · simpa only [Q, SimpleGraph.Walk.support_mapLe_eq_support] using (hq i).2.2
  · intro i j hij
    simpa only [Q, SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet] using hd hij
  · intro i
    rw [show (Q i).edgeSet = (q i).edgeSet from (q i).edgeSet_mapLe_eq_edgeSet hPG]
    intro e he
    exact (q i).edges_subset_edgeSet he

end
end ErdosGallai

namespace ErdosGallai
open SimpleGraph

variable {V : Type cycleUniverse11} {G : SimpleGraph V} {x y a b : V}

def reservoirReturn (P : G.Walk a b) (hx : G.Adj x a) (hy : G.Adj y b) :
    G.Walk y x := .cons hy (P.reverse.concat hx.symm)

lemma reservoirReturn_isPath (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (reservoirReturn P hx hy).IsPath := by
  have hxy : x ≠ y := by
    intro h
    subst y
    have := hQ.nil_iff_eq.mpr rfl
    have hz : Q.length = 0 := this.length_eq_zero
    omega
  have hxP : x ∉ P.reverse.support := by
    simpa using hdisj Q.start_mem_support
  have hyP : y ∉ P.reverse.support := by
    simpa using hdisj Q.end_mem_support
  exact (hP.reverse.concat hxP hx.symm).cons (by simpa using And.intro hyP hxy.symm)

theorem reservoir_path_closure (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (Q.append (reservoirReturn P hx hy)).IsCycle ∧
    (Q.append (reservoirReturn P hx hy)).edgeSet =
      Q.edgeSet ∪ P.edgeSet ∪ {s(x,a), s(y,b)} ∧
    3 ≤ (Q.append (reservoirReturn P hx hy)).length := by
  have hreturn := reservoirReturn_isPath Q P hQ hQpos hP hdisj hx hy
  have htail : Q.support.tail.Disjoint (reservoirReturn P hx hy).support.tail := by
    rw [List.disjoint_left]
    intro v hv
    have hvQ := List.mem_of_mem_tail hv
    have hvP : v ∉ P.support := hdisj hvQ
    have hvx : v ≠ x := by
      have hn := hQ.support_nodup
      rw [← Q.cons_tail_support, List.nodup_cons] at hn
      exact fun heq => hn.1 (heq ▸ hv)
    simpa [reservoirReturn] using And.intro hvP hvx
  have hcycle := hQ.isCycle_append hreturn htail (Or.inr (by simp [reservoirReturn]))
  refine ⟨hcycle, ?_, ?_⟩
  · ext e
    simp only [Walk.edgeSet_append, reservoirReturn, Walk.edgeSet_cons,
      Walk.edgeSet_concat, Walk.edgeSet_reverse, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [Sym2.eq_swap (a := x) (b := a)]
    tauto
  · simpa [reservoirReturn] using (by omega : 3 ≤ Q.length + (P.length + 1 + 1))

end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma spoke_sets_pairwise {I : Type cycleUniverse12} {E : Type cycleUniverse13} (e : I × Fin 2 → E)
    (he : Function.Injective e) :
    Pairwise (fun i j => Disjoint ({e (i,0), e (i,1)} : Set E) {e (j,0), e (j,1)}) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro a hai haj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hai haj
  rcases hai with hai | hai <;> rcases haj with haj | haj
  all_goals exact hij (congrArg Prod.fst (he (hai.symm.trans haj)))

lemma pairwise_union_three {I : Type cycleUniverse14} {E : Type cycleUniverse15} (A B S : I → Set E)
    (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hAB : ∀ i j, Disjoint (A i) (B j))
    (hAS : ∀ i j, Disjoint (A i) (S j))
    (hBS : ∀ i j, Disjoint (B i) (S j)) :
    Pairwise (fun i j => Disjoint (A i ∪ B i ∪ S i) (A j ∪ B j ∪ S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro e ((ha | hb) | hs) ((ha' | hb') | hs')
  all_goals first
    | exact Set.disjoint_left.mp (hA hij) ha ha'
    | exact Set.disjoint_left.mp (hB hij) hb hb'
    | exact Set.disjoint_left.mp (hS hij) hs hs'
    | exact Set.disjoint_left.mp (hAB i j) ha hb'
    | exact Set.disjoint_left.mp (hAS i j) ha hs'
    | exact Set.disjoint_left.mp (hBS i j) hb hs'
    | exact Set.disjoint_left.mp (hAB j i) ha' hb
    | exact Set.disjoint_left.mp (hAS j i) ha' hs
    | exact Set.disjoint_left.mp (hBS j i) hb' hs

theorem reservoir_cycle_family {V : Type cycleUniverse16} {I : Type cycleUniverse17} {G : SimpleGraph V}
    {x y a b : I → V} (Q : ∀ i, G.Walk (x i) (y i))
    (P : ∀ i, G.Walk (a i) (b i))
    (hx : ∀ i, G.Adj (x i) (a i)) (hy : ∀ i, G.Adj (y i) (b i))
    (hQ : ∀ i, (Q i).IsPath) (hQpos : ∀ i, 0 < (Q i).length)
    (hP : ∀ i, (P i).IsPath)
    (hsep : ∀ i, (Q i).support.Disjoint (P i).support)
    (hQQ : Pairwise fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hspoke : Function.Injective (fun z : I × Fin 2 =>
      if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)))
    (hQP : ∀ i j, Disjoint (Q i).edgeSet (P j).edgeSet)
    (hQS : ∀ i j, Disjoint (Q i).edgeSet {s(x j,a j),s(y j,b j)})
    (hPS : ∀ i j, Disjoint (P i).edgeSet {s(x j,a j),s(y j,b j)}) :
    let C := fun i => (Q i).append (reservoirReturn (P i) (hx i) (hy i))
    (∀ i, (C i).IsCycle) ∧
    Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
    (⋃ i, (C i).edgeSet) =
      (⋃ i, (Q i).edgeSet) ∪ (⋃ i, (P i).edgeSet) ∪
        (⋃ i, ({s(x i,a i),s(y i,b i)} : Set (Sym2 V))) := by
  dsimp only
  have hC := fun i => reservoir_path_closure (Q i) (P i) (hQ i) (hQpos i)
    (hP i) (hsep i) (hx i) (hy i)
  refine ⟨fun i => (hC i).1, ?_, ?_⟩
  · have hSS : Pairwise (fun i j => Disjoint
        ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) {s(x j,a j),s(y j,b j)}) := by
      simpa using spoke_sets_pairwise _ hspoke
    simpa only [fun i => (hC i).2.1] using
      pairwise_union_three (fun i => (Q i).edgeSet) (fun i => (P i).edgeSet)
        (fun i => ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)))
        hQQ hPP hSS hQP hQS hPS
  · simp only [fun i => (hC i).2.1, Set.iUnion_union_distrib]

lemma reservoir_edge_ledger {E : Type cycleUniverse18} {I : Type cycleUniverse19} (G O R : Set E)
    (A B S C : I → Set E)
    (hcover : (⋃ i, A i) ∪ O ∪ R = G)
    (hAO : Disjoint (⋃ i, A i) O) (hAR : Disjoint (⋃ i, A i) R)
    (hOR : Disjoint O R)
    (hB : (⋃ i, B i) ⊆ R) (hS : (⋃ i, S i) ⊆ O)
    (hC : (⋃ i, C i) = (⋃ i, A i) ∪ (⋃ i, B i) ∪ (⋃ i, S i)) :
    let unusedSpokes := O \ (⋃ i, S i)
    let remaining := R \ (⋃ i, B i)
    Disjoint (⋃ i, C i) unusedSpokes ∧
    Disjoint (⋃ i, C i) remaining ∧
    Disjoint unusedSpokes remaining ∧
    (⋃ i, C i) ∪ unusedSpokes ∪ remaining = G := by
  dsimp only
  rw [hC]
  have hBO := hOR.symm.mono_left hB
  have hSR := hOR.mono_left hS
  refine ⟨?_,?_,hOR.mono Set.sdiff_subset Set.sdiff_subset,?_⟩
  · apply Set.disjoint_left.mpr
    rintro e ((he | he) | he) ⟨ho,hs⟩
    · exact Set.disjoint_left.mp hAO he ho
    · exact Set.disjoint_left.mp hBO he ho
    · exact hs he
  · apply Set.disjoint_left.mpr
    rintro e ((he | he) | he) ⟨hr,hb⟩
    · exact Set.disjoint_left.mp hAR he hr
    · exact hb he
    · exact Set.disjoint_left.mp hSR he hr
  · rw [← hcover]
    ext e
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro ((((ha | hb) | hs) | ho) | hr)
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (hB hb)
      · exact Or.inl (Or.inr (hS hs))
      · exact Or.inl (Or.inr ho.1)
      · exact Or.inr hr.1
    · rintro ((ha | ho) | hr)
      · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
      · by_cases hs : e ∈ ⋃ i, S i
        · exact Or.inl (Or.inl (Or.inr hs))
        · exact Or.inl (Or.inr ⟨ho,hs⟩)
      · by_cases hb : e ∈ ⋃ i, B i
        · exact Or.inl (Or.inl (Or.inl (Or.inr hb)))
        · exact Or.inr ⟨hr,hb⟩

end
end ErdosGallai

end
end
end

end OAI


-- Upstream module ReservoirRemainder

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma walks_edges_disjoint_of_support {V : Type cycleUniverse1} {G H : SimpleGraph V}
    {x y a b : V} (p : G.Walk x y) (q : H.Walk a b)
    (h : p.support.Disjoint q.support) : Disjoint p.edgeSet q.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.ind with
  | _ u v =>
    exact h (p.fst_mem_support_of_mem_edges he) (q.fst_mem_support_of_mem_edges he')

lemma walk_edges_disjoint_spokes_of_outside {V : Type cycleUniverse2} {I : Type cycleUniverse3} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∉ W) (ha : ∀ i, a i ∈ W) (hb : ∀ i, b i ∈ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hQ _ (Q.snd_mem_support_of_mem_edges he) (ha i)
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hQ _ (Q.snd_mem_support_of_mem_edges he) (hb i)

lemma walk_edges_disjoint_spokes_of_inside {V : Type cycleUniverse4} {I : Type cycleUniverse5} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∈ W) (hx : ∀ i, x i ∉ W) (hy : ∀ i, y i ∉ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hx i (hQ _ (Q.fst_mem_support_of_mem_edges he))
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hy i (hQ _ (Q.fst_mem_support_of_mem_edges he))

theorem uniform_reservoir_completion (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V) (Q : ∀ i, G.Walk (x i) (y i)),
      (∀ i, (Q i).IsPath) → (∀ i, 0 < (Q i).length) →
      (∀ i v, v ∈ (Q i).support → v ∉ W) →
      Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(thinning D*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i))
        (C : ∀ i, G.Walk (x i) (x i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q i).edgeSet ∪ (q i).edgeSet ∪
          {s(x i,a i),s(y i,b i)}) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  obtain ⟨D₀,hD₀,hrouting⟩ := uniform_assigned_reservoir_routing c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y Q hQ hpos hout hQQ hl r hrep hrepne hcap
  have hne : ∀ i, x i ≠ y i := by
    intro i hi
    have hz := ((hQ i).nil_iff_eq.mpr hi).length_eq_zero
    have := hpos i
    omega
  have hx : ∀ i, x i ∉ W := fun i => hout i _ (Q i).start_mem_support
  have hy : ∀ i, y i ∉ W := fun i => hout i _ (Q i).end_mem_support
  obtain ⟨a,b,q,hab,hsp,hq,hdd,ha',hb',hPedge⟩ :=
    hrouting D hD V G P hPG W hexp hW hr I x y hne hx hy hl r hrep hrepne hcap
  have ha : ∀ i, a i ∈ W := fun i => (hq i).2.2 _ (q i).start_mem_support
  have hb : ∀ i, b i ∈ W := fun i => (hq i).2.2 _ (q i).end_mem_support
  have hdisj : ∀ i j, (Q i).support.Disjoint (q j).support := by
    intro i j
    exact List.disjoint_left.mpr (fun v hv hv' => hout i v hv ((hq j).2.2 v hv'))
  let C := fun i => (Q i).append (reservoirReturn (q i) (hab i).1 (hab i).2)
  have hfamily := reservoir_cycle_family Q q (fun i => (hab i).1) (fun i => (hab i).2)
    hQ hpos (fun i => (hq i).1) (fun i => hdisj i i) hQQ hdd hsp
    (fun i j => walks_edges_disjoint_of_support _ _ (hdisj i j))
    (fun i => walk_edges_disjoint_spokes_of_outside (Q i) W x y a b (hout i) ha hb)
    (fun i => walk_edges_disjoint_spokes_of_inside (q i) W x y a b (hq i).2.2 hx hy)
  refine ⟨a,b,q,C,hfamily.1,hfamily.2.1,?_,?_,hsp,ha',hb'⟩
  · intro i
    exact (reservoir_path_closure (Q i) (q i) (hQ i) (hpos i) (hq i).1
      (hdisj i i) (hab i).1 (hab i).2).2.1
  · intro i
    exact ⟨hPedge i,(hq i).2.2⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma exists_reservoir_avoided {V : Type cycleUniverse6} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (x y : V) :
    ∃ i, x ∉ W i ∧ y ∉ W i := by
  by_contra hno
  have h : ∀ i, x ∈ W i ∨ y ∈ W i := by
    intro i
    by_contra! hi
    exact hno ⟨i,hi⟩
  have h01 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 1 by decide))
  have h02 := Set.disjoint_left.mp (hW (show (0 : Fin 3) ≠ 2 by decide))
  have h12 := Set.disjoint_left.mp (hW (show (1 : Fin 3) ≠ 2 by decide))
  rcases h 0 with hx0 | hy0 <;>
    rcases h 1 with hx1 | hy1 <;>
    rcases h 2 with hx2 | hy2
  all_goals first
    | exact h01 hx0 hx1
    | exact h02 hx0 hx2
    | exact h12 hx1 hx2
    | exact h01 hy0 hy1
    | exact h02 hy0 hy2
    | exact h12 hy1 hy2

lemma exists_edge_reservoir_avoided {V : Type cycleUniverse7} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∃ i, ∀ v ∈ e, v ∉ W i := by
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨i,hx,hy⟩ := exists_reservoir_avoided W hW x y
    refine ⟨i,?_⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hx
    · exact hy

noncomputable def reservoirColor {V : Type cycleUniverse8} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) : Fin 3 :=
  (exists_edge_reservoir_avoided W hW e).choose

lemma reservoirColor_avoids {V : Type cycleUniverse9} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∀ v ∈ e, v ∉ W (reservoirColor W hW e) :=
  (exists_edge_reservoir_avoided W hW e).choose_spec

def complementaryReservoirGraph {V : Type cycleUniverse10} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ reservoirColor W hW s(x,y) = i
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

lemma complementaryReservoirGraph_edges {V : Type cycleUniverse11} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) :
    (complementaryReservoirGraph G W hW i).edgeSet =
      {e | e ∈ G.edgeSet ∧ reservoirColor W hW e = i} := by
  ext e
  induction e using Sym2.ind with
  | _ x y => rfl

theorem complementary_reservoir_graphs {V : Type cycleUniverse12} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j)) :
    (∀ i, complementaryReservoirGraph G W hW i ≤ G) ∧
    (∀ i x y, (complementaryReservoirGraph G W hW i).Adj x y →
      x ∉ W i ∧ y ∉ W i) ∧
    Pairwise (fun i j => Disjoint (complementaryReservoirGraph G W hW i).edgeSet
      (complementaryReservoirGraph G W hW j).edgeSet) ∧
    (⋃ i, (complementaryReservoirGraph G W hW i).edgeSet) = G.edgeSet := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_, ?_⟩
  · intro i x y h
    have hx := reservoirColor_avoids W hW s(x,y) x (Sym2.mem_mk_left x y)
    have hy := reservoirColor_avoids W hW s(x,y) y (Sym2.mem_mk_right x y)
    rw [h.2] at hx hy
    exact ⟨hx,hy⟩
  · intro i j hij
    rw [complementaryReservoirGraph_edges, complementaryReservoirGraph_edges]
    exact Set.disjoint_left.mpr fun _ he hj => hij (he.2.symm.trans hj.2)
  · ext e
    simp only [Set.mem_iUnion, complementaryReservoirGraph_edges, Set.mem_ofPred]
    constructor
    · rintro ⟨i,he,_⟩; exact he
    · intro he; exact ⟨reservoirColor W hW e, he, rfl⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def reservoirInternal {V : Type cycleUniverse13} (P : SimpleGraph V) (W : Set V) : Set (Sym2 V) :=
  {e | e ∈ P.edgeSet ∧ ∀ v ∈ e, v ∈ W}

noncomputable def reservoirSpokes {V : Type cycleUniverse14} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) : Finset (Sym2 V) :=
  (Wᶜ ×ˢ univ).image (fun z => s(z.1,r z))

lemma mem_reservoirSpokes {V : Type cycleUniverse15} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) (e : Sym2 V) :
    e ∈ reservoirSpokes W r ↔ ∃ v ∉ W, ∃ t : Fin 2, e = s(v,r (v,t)) := by
  simp only [reservoirSpokes, Finset.mem_image, Finset.mem_product,
    Finset.mem_compl, Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨v,t,hv,he⟩
    exact ⟨v,hv,t,he.symm⟩
  · rintro ⟨v,hv,t,he⟩
    exact ⟨v,t,hv,he.symm⟩

lemma reservoirSpokes_card_le {V : Type cycleUniverse16} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) :
    (reservoirSpokes W r).card ≤ 2 * Fintype.card V := by
  apply (Finset.card_image_le).trans
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_univ Wᶜ
  omega

lemma reservoirSpokes_subset {V : Type cycleUniverse17} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, P.Adj v (r (v,t))) :
    (reservoirSpokes W r : Set (Sym2 V)) ⊆ P.edgeSet := by
  intro e he
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he
  exact hr v hv t

lemma reservoirInternal_spokes_disjoint {V : Type cycleUniverse18} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V) :
    Disjoint (reservoirInternal P W) (reservoirSpokes W r : Set (Sym2 V)) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he'
  exact hv (he.2 _ (Sym2.mem_mk_left _ _))

theorem reservoir_reservations {V : Type cycleUniverse19} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V) (W : Fin 3 → Finset V)
    (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ i, P i ≤ G)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hr : ∀ i v, v ∉ W i → ∀ t, (P i).Adj v (r i (v,t))) :
    let R := fun i => reservoirInternal (P i) (W i)
    let O := fun i => (reservoirSpokes (W i) (r i) : Set (Sym2 V))
    (∀ i, R i ⊆ G.edgeSet ∧ O i ⊆ G.edgeSet) ∧
    Pairwise (fun i j => Disjoint (R i ∪ O i) (R j ∪ O j)) ∧
    (∀ i, Disjoint (R i) (O i)) ∧
    Disjoint (⋃ i, R i) (⋃ i, O i) ∧
    (∑ i, (reservoirSpokes (W i) (r i)).card) ≤ 6 * Fintype.card V := by
  dsimp only
  have hR : ∀ i, reservoirInternal (P i) (W i) ⊆ (P i).edgeSet := fun _ _ he => he.1
  have hO := fun i => reservoirSpokes_subset (P i) (W i) (r i) (hr i)
  have hU : ∀ i, reservoirInternal (P i) (W i) ∪
      (reservoirSpokes (W i) (r i) : Set (Sym2 V)) ⊆ (P i).edgeSet :=
    fun i => Set.union_subset (hR i) (hO i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨(hR i).trans (SimpleGraph.edgeSet_mono (hPG i)),
      (hO i).trans (SimpleGraph.edgeSet_mono (hPG i))⟩
  · intro i j hij
    exact (hPP hij).mono (hU i) (hU j)
  · exact fun i => reservoirInternal_spokes_disjoint (P i) (W i) (r i)
  · rw [Set.disjoint_iUnion_left]
    intro i
    rw [Set.disjoint_iUnion_right]
    intro j
    by_cases hij : i = j
    · subst j
      exact reservoirInternal_spokes_disjoint (P i) (W i) (r i)
    · exact (hPP hij).mono (hR i) (hO j)
  · calc
      _ ≤ ∑ _i : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun i _ => reservoirSpokes_card_le (W i) (r i))
      _ = _ := by simp; omega

lemma complementary_walk_outside {V : Type cycleUniverse20} {G : SimpleGraph V}
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) {x y : V} (q : (complementaryReservoirGraph G W hW i).Walk x y)
    (hq : 0 < q.length) : ∀ v ∈ q.support, v ∉ W i := by
  have hn : ¬ q.Nil := by
    intro h
    have hz := h.length_eq_zero
    omega
  intro v hv
  obtain ⟨e,he,hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  have heG := q.edges_subset_edgeSet he
  have hecol : reservoirColor W hW e = i := by
    rw [complementaryReservoirGraph_edges] at heG
    exact heG.2
  exact hecol ▸ reservoirColor_avoids W hW e v hve

theorem complementary_reservation_ledger {V : Type cycleUniverse21} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (E : Set (Sym2 V)) (hE : E ⊆ G.edgeSet) :
    let H := G.deleteEdges E
    let K := fun i => complementaryReservoirGraph H W hW i
    Pairwise (fun i j => Disjoint (K i).edgeSet (K j).edgeSet) ∧
    (∀ i, Disjoint (K i).edgeSet E) ∧
    ((⋃ i, (K i).edgeSet) ∪ E = G.edgeSet) := by
  dsimp only
  have hh := complementary_reservoir_graphs (G.deleteEdges E) W hW
  refine ⟨hh.2.2.1,?_,?_⟩
  · intro i
    apply Set.disjoint_left.mpr
    intro e he he'
    have h := SimpleGraph.edgeSet_mono (hh.1 i) he
    rw [SimpleGraph.edgeSet_deleteEdges] at h
    exact h.2 he'
  · rw [hh.2.2.2, SimpleGraph.edgeSet_deleteEdges]
    exact Set.sdiff_union_of_subset hE

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def edgeRestriction {V : Type cycleUniverse22} (G : SimpleGraph V) (E : Set (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ s(x,y) ∈ E
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

lemma edgeRestriction_le {V : Type cycleUniverse23} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    edgeRestriction G E ≤ G := fun _ _ h => h.1

lemma edgeRestriction_edges {V : Type cycleUniverse24} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    (edgeRestriction G E).edgeSet = G.edgeSet ∩ E := by
  ext e
  induction e using Sym2.ind with | _ x y => rfl

lemma edgeRestriction_edges_of_subset {V : Type cycleUniverse25} (G : SimpleGraph V) (E : Set (Sym2 V))
    (hE : E ⊆ G.edgeSet) : (edgeRestriction G E).edgeSet = E := by
  rw [edgeRestriction_edges, Set.inter_eq_right.mpr hE]

def completedEdges {V : Type cycleUniverse26} {I : Type cycleUniverse27} (C : I → Set (Sym2 V)) : Set (Sym2 V) := ⋃ i, C i

def residualInternalGraph {V : Type cycleUniverse28} {B : Type cycleUniverse29} {I : Type cycleUniverse30} (G : SimpleGraph V)
    (R : B → Set (Sym2 V)) (C : I → Set (Sym2 V)) (b : B) : SimpleGraph V :=
  edgeRestriction G (R b \ completedEdges C)

def unusedSpokes {V : Type cycleUniverse31} {I : Type cycleUniverse32} [Fintype V] (S : Set (Sym2 V))
    (C : I → Set (Sym2 V)) : Finset (Sym2 V) := (S \ completedEdges C).toFinset

lemma unusedSpokes_card_le {V : Type cycleUniverse33} {I : Type cycleUniverse34} [Fintype V] (S : Finset (Sym2 V))
    (C : I → Set (Sym2 V)) : (unusedSpokes (↑S) C).card ≤ S.card := by
  apply Finset.card_le_card
  intro e he
  simp only [unusedSpokes, Set.mem_toFinset, Finset.mem_coe, Set.mem_sdiff] at he
  exact he.1

theorem residue_edge_ledger {V : Type cycleUniverse35} {B : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V]
    (G : SimpleGraph V) (R : B → Set (Sym2 V)) (S : Set (Sym2 V))
    (C : I → Set (Sym2 V))
    (hR : ∀ b, R b ⊆ G.edgeSet) (hS : S ⊆ G.edgeSet)
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hRS : ∀ b, Disjoint (R b) S)
    (hC : ∀ i, C i ⊆ G.edgeSet)
    (_hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hcover : G.edgeSet \ ((⋃ b, R b) ∪ S) ⊆ completedEdges C) :
    (∀ b, (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b c => Disjoint (residualInternalGraph G R C b).edgeSet
      (residualInternalGraph G R C c).edgeSet) ∧
    (∀ b i, Disjoint (residualInternalGraph G R C b).edgeSet (C i)) ∧
    (∀ b, Disjoint (residualInternalGraph G R C b).edgeSet (↑(unusedSpokes S C) : Set _)) ∧
    (∀ i, Disjoint (C i) (↑(unusedSpokes S C) : Set _)) ∧
    (completedEdges C ∪ (↑(unusedSpokes S C) : Set _) ∪
      (⋃ b, (residualInternalGraph G R C b).edgeSet)) = G.edgeSet := by
  classical
  have hrem (b : B) : (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C := by
    apply edgeRestriction_edges_of_subset
    exact fun e he => hR b he.1
  have hsingle : (↑(unusedSpokes S C) : Set _) = S \ completedEdges C := by
    simp only [unusedSpokes, Set.coe_toFinset]
  have hsub : completedEdges C ⊆ G.edgeSet := by
    rintro e he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    exact hC i hi
  refine ⟨hrem,?_,?_,?_,?_,?_⟩
  · intro b c hbc
    rw [hrem b,hrem c]
    exact (hRR hbc).mono Set.sdiff_subset Set.sdiff_subset
  · intro b i
    rw [hrem b]
    apply Set.disjoint_left.mpr
    intro e he hi
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · intro b
    rw [hrem b,hsingle]
    exact (hRS b).mono Set.sdiff_subset Set.sdiff_subset
  · intro i
    rw [hsingle]
    apply Set.disjoint_left.mpr
    intro e hi he
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · rw [hsingle]
    ext e
    constructor
    · rintro ((he | he) | he)
      · exact hsub he
      · exact hS he.1
      · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
        rw [hrem b] at hb
        exact hR b hb.1
    · intro he
      by_cases hc : e ∈ completedEdges C
      · exact Or.inl (Or.inl hc)
      by_cases hs : e ∈ S
      · exact Or.inl (Or.inr ⟨hs,hc⟩)
      have hr : e ∈ ⋃ b, R b := by
        by_contra hr
        exact hc (hcover ⟨he,by intro hu; exact hu.elim hr hs⟩)
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hr
      exact Or.inr (Set.mem_iUnion.mpr ⟨b,by rw [hrem b]; exact ⟨hb,hc⟩⟩)

theorem residue_part_count {V : Type cycleUniverse38} {I : Type cycleUniverse39} [Fintype V] [Fintype I]
    (S : Finset (Sym2 V)) (C : I → Set (Sym2 V))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hS : S.card ≤ 6 * Fintype.card V) :
    Fintype.card I + (unusedSpokes (↑S) C).card ≤ 9 * Fintype.card V := by
  have := unusedSpokes_card_le S C
  omega

lemma induce_edge_image_of_support_subset {V : Type cycleUniverse40} (H : SimpleGraph V)
    (W : Set V) (hW : H.support ⊆ W) :
    Sym2.map Subtype.val '' (H.induce W).edgeSet = H.edgeSet := by
  ext e
  constructor
  · rintro ⟨d,hd,rfl⟩
    induction d using Sym2.ind with
    | _ x y => exact hd
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ W := hW ⟨y,he⟩
      have hy : y ∈ W := hW ⟨x,he.symm⟩
      exact ⟨s(⟨x,hx⟩,⟨y,hy⟩),he,rfl⟩

theorem residual_induce_exact {V : Type cycleUniverse41} {B : Type cycleUniverse42} {I : Type cycleUniverse43} (G : SimpleGraph V)
    (R : B → Set (Sym2 V)) (C : I → Set (Sym2 V)) (b : B) (W : Set V)
    (hR : R b ⊆ G.edgeSet) (hinside : ∀ e ∈ R b, ∀ v ∈ e, v ∈ W) :
    Sym2.map Subtype.val '' ((residualInternalGraph G R C b).induce W).edgeSet =
      R b \ completedEdges C := by
  have hsupport : (residualInternalGraph G R C b).support ⊆ W := by
    rintro v ⟨w,hw⟩
    exact hinside s(v,w) hw.2.1 v (by simp)
  rw [induce_edge_image_of_support_subset _ W hsupport]
  exact edgeRestriction_edges_of_subset G _ (fun e he => hR he.1)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma walk_edges_internal {V : Type cycleUniverse44} {G P : SimpleGraph V} {a b : V}
    (W : Set V) (q : G.Walk a b) (he : q.edgeSet ⊆ P.edgeSet)
    (hv : ∀ v ∈ q.support, v ∈ W) :
    q.edgeSet ⊆ reservoirInternal P W := by
  intro e h
  refine ⟨he h,?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    intro v hmem
    rcases (Sym2.mem_iff.mp hmem) with rfl | rfl
    · exact hv _ (q.fst_mem_support_of_mem_edges h)
    · exact hv _ (q.snd_mem_support_of_mem_edges h)

lemma completion_edges_subset {V : Type cycleUniverse45} [Fintype V] [DecidableEq V]
    {G P : SimpleGraph V} (W : Finset V) (r : V × Fin 2 → V)
    {x y a b : V} (Q : G.Walk x y) (q : G.Walk a b) (C : G.Walk x x)
    (K : Set (Sym2 V)) (hQ : Q.edgeSet ⊆ K)
    (hC : C.edgeSet = Q.edgeSet ∪ q.edgeSet ∪ {s(x,a),s(y,b)})
    (hq : q.edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ q.support, v ∈ W)
    (hx : x ∉ W) (hy : y ∉ W)
    (ha : ∃ t, a = r (x,t)) (hb : ∃ t, b = r (y,t)) :
    C.edgeSet ⊆ K ∪ (reservoirInternal P W ∪ (reservoirSpokes W r : Set _)) := by
  rw [hC]
  have hqi := walk_edges_internal (W : Set V) q hq.1 hq.2
  intro e he
  rcases he with (he | he) | he
  · exact Or.inl (hQ he)
  · exact Or.inr (Or.inl (hqi he))
  · apply Or.inr ∘ Or.inr
    rcases (show e = s(x,a) ∨ e = s(y,b) by simpa using he) with rfl | rfl
    · obtain ⟨t,rfl⟩ := ha
      exact (mem_reservoirSpokes W r _).mpr ⟨x,hx,t,rfl⟩
    · obtain ⟨t,rfl⟩ := hb
      exact (mem_reservoirSpokes W r _).mpr ⟨y,hy,t,rfl⟩

lemma completed_subfamilies_disjoint {E : Type cycleUniverse46} {B : Type cycleUniverse47} {I : B → Type cycleUniverse55}
    (K R : B → Set E) (C : ∀ b, I b → Set E)
    (hKK : Pairwise fun b c => Disjoint (K b) (K c))
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hKR : ∀ b c, Disjoint (K b) (R c))
    (hC : ∀ b i, C b i ⊆ K b ∪ R b)
    (hCC : ∀ b, Pairwise fun i j => Disjoint (C b i) (C b j)) :
    Pairwise (fun s t : Sigma I => Disjoint (C s.1 s.2) (C t.1 t.2)) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ hne
  by_cases hbc : b = c
  · subst c
    apply hCC b
    intro hij
    exact hne (by cases hij; rfl)
  · apply Disjoint.mono (hC b i) (hC c j)
    rw [Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
    exact ⟨⟨hKK hbc,hKR b c⟩,⟨(hKR c b).symm,hRR hbc⟩⟩

lemma completed_subfamilies_cover {E : Type cycleUniverse48} {B : Type cycleUniverse49} {I : B → Type cycleUniverse56}
    (K : B → Set E) (Q C : ∀ b, I b → Set E)
    (hQ : ∀ b, (⋃ i, Q b i) = K b)
    (hQC : ∀ b i, Q b i ⊆ C b i) :
    (⋃ b, K b) ⊆ ⋃ s : Sigma I, C s.1 s.2 := by
  intro e he
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
  rw [← hQ b] at hb
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨⟨b,i⟩,hQC b i hi⟩

lemma endpointLoad_family_card {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hs := endpointLoad_sum (univ : Finset I) x y (fun i _ => hne i)
  have hb := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hload v)
  simp only [Finset.card_univ] at hs
  rw [hs] at hb
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hb
  omega

lemma sigma_three_card_le {V : Type} [Fintype V]
    (I : Fin 3 → Type) [∀ b, Fintype (I b)]
    (hI : ∀ b, Fintype.card (I b) ≤ Fintype.card V) :
    Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _b : Fin 3, Fintype.card V := Finset.sum_le_sum (fun b _ => hI b)
    _ = _ := by simp [mul_comm]

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem uniform_three_reservoir_completion (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) (P K : Fin 3 → SimpleGraph V)
        [∀ b, DecidableRel (P b).Adj],
      (∀ b, P b ≤ G) →
      Pairwise (fun b d => Disjoint (P b).edgeSet (P d).edgeSet) →
      ∀ (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V),
      (∀ b, CutExpansionOn (P b) (W b) (D^(37/50:ℝ))) →
      (∀ b, 2 ≤ (W b).card) → (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      (∀ b v, v ∉ W b → ∀ t, r b (v,t) ∈ W b ∧ (P b).Adj v (r b (v,t))) →
      (∀ b v, v ∉ W b → r b (v,0) ≠ r b (v,1)) →
      (∀ b v, (((W b)ᶜ ×ˢ univ).filter (fun z => r b z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(thinning D*(c*D^(9/10:ℝ)))⌉₊) →
      let T := fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set (Sym2 V))
      Pairwise (fun b d => Disjoint (K b).edgeSet (K d).edgeSet) →
      (∀ b d, Disjoint (K b).edgeSet (T d)) →
      ∀ (I : Fin 3 → Type) [∀ b, Fintype (I b)]
        (x y : ∀ b, I b → V) (Q : ∀ b i, G.Walk (x b i) (y b i)),
      (∀ b i, (Q b i).IsPath) → (∀ b i, 0 < (Q b i).length) →
      (∀ b i v, v ∈ (Q b i).support → v ∉ W b) →
      (∀ b, Pairwise fun i j => Disjoint (Q b i).edgeSet (Q b j).edgeSet) →
      (∀ b, (⋃ i, (Q b i).edgeSet) = (K b).edgeSet) →
      (∀ b v, endpointLoad univ (x b) (y b) v ≤ 2) →
      ∃ C : ∀ b i, G.Walk (x b i) (x b i),
        (∀ b i, (C b i).IsCycle) ∧
        Pairwise (fun s t : Sigma I =>
          Disjoint (C s.1 s.2).edgeSet (C t.1 t.2).edgeSet) ∧
        (∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪ T b) ∧
        (⋃ b, (K b).edgeSet) ⊆ (⋃ s : Sigma I, (C s.1 s.2).edgeSet) ∧
        Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨D₀,hD₀,hclose⟩ := uniform_reservoir_completion c hc
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P K _ hPG hPP W r hexp hW hn hr hrne hcap
  dsimp only
  intro hKK hKT I _ x y Q hQ hpos hout hQQ hcover hl
  have hex : ∀ b : Fin 3,
      ∃ (a z : I b → V) (q : ∀ i, G.Walk (a i) (z i))
        (C : ∀ i, G.Walk (x b i) (x b i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q b i).edgeSet ∪ (q i).edgeSet ∪
          {s(x b i,a i),s(y b i,z i)}) ∧
        (∀ i, (q i).edgeSet ⊆ (P b).edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W b) ∧
        Function.Injective (fun z' : I b × Fin 2 =>
          if z'.2 = 0 then s(x b z'.1,a z'.1) else s(y b z'.1,z z'.1)) ∧
        (∀ i, ∃ t, a i = r b (x b i,t)) ∧
        (∀ i, ∃ t, z i = r b (y b i,t)) := by
    intro b
    exact hclose D hD V G (P b) (hPG b) (W b) (hexp b) (hW b) hn
      (I b) (x b) (y b) (Q b) (hQ b) (hpos b) (hout b) (hQQ b) (hl b)
      (r b) (hr b) (hrne b) (hcap b)
  choose a z q C hCy hCC hCe hqe _hsp ha hz using hex
  have hsub : ∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪
      (reservoirInternal (P b) (W b) ∪ (reservoirSpokes (W b) (r b) : Set _)) := by
    intro b i
    apply completion_edges_subset (W b) (r b) (Q b i) (q b i) (C b i)
      (K b).edgeSet _ (hCe b i) (hqe b i)
      (hout b i _ (Q b i).start_mem_support)
      (hout b i _ (Q b i).end_mem_support) (ha b i) (hz b i)
    intro e he
    rw [← hcover b]
    exact Set.mem_iUnion.mpr ⟨i,he⟩
  have hreserv := reservoir_reservations G P W r hPG hPP
    (fun b v hv t => (hr b v hv t).2)
  refine ⟨C,hCy,?_,hsub,?_,?_⟩
  · exact completed_subfamilies_disjoint (fun b => (K b).edgeSet)
      (fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set _))
      (fun b i => (C b i).edgeSet) hKK hreserv.2.1 hKT hsub hCC
  · apply completed_subfamilies_cover (fun b => (K b).edgeSet)
      (fun b i => (Q b i).edgeSet) (fun b i => (C b i).edgeSet) hcover
    intro b i e he
    rw [hCe b i]
    exact Or.inl (Or.inl he)
  · apply sigma_three_card_le I
    intro b
    apply endpointLoad_family_card (x b) (y b) _ (hl b)
    intro i hi
    have hz := ((hQ b i).nil_iff_eq.mpr hi).length_eq_zero
    have hp := hpos b i
    omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def allReservoirSpokes {V : Type cycleUniverse50} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) : Finset (Sym2 V) :=
  univ.biUnion (fun b => reservoirSpokes (W b) (r b))

lemma coe_allReservoirSpokes {V : Type cycleUniverse51} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r : Set (Sym2 V)) =
      ⋃ b, (reservoirSpokes (W b) (r b) : Set (Sym2 V)) := by
  ext e
  simp [allReservoirSpokes]

lemma allReservoirSpokes_card_le {V : Type cycleUniverse52} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r).card ≤ 6 * Fintype.card V := by
  apply (Finset.card_biUnion_le).trans
  calc
    (∑ b : Fin 3, (reservoirSpokes (W b) (r b)).card) ≤
      ∑ _b : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun b _ => reservoirSpokes_card_le (W b) (r b))
    _ = _ := by simp; omega

theorem three_reservoir_remainder {V : Type cycleUniverse53} {I : Type cycleUniverse54} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V)
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ b, P b ≤ G)
    (hPP : Pairwise fun b d => Disjoint (P b).edgeSet (P d).edgeSet)
    (hr : ∀ b v, v ∉ W b → ∀ t, (P b).Adj v (r b (v,t)))
    (C : I → Set (Sym2 V)) (hC : ∀ i, C i ⊆ G.edgeSet)
    (hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hcover : G.edgeSet \ ((⋃ b, reservoirInternal (P b) (W b)) ∪
      (allReservoirSpokes W r : Set _)) ⊆ completedEdges C) :
    let R := fun b => reservoirInternal (P b) (W b)
    let H := residualInternalGraph G R C
    let S := unusedSpokes (↑(allReservoirSpokes W r)) C
    (∀ b, (H b).support ⊆ (W b : Set V)) ∧
    (∀ b, Sym2.map Subtype.val '' ((H b).induce (W b : Set V)).edgeSet = (H b).edgeSet) ∧
    (∀ b, (H b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
    (∀ b i, Disjoint (H b).edgeSet (C i)) ∧
    (∀ b, Disjoint (H b).edgeSet (S : Set _)) ∧
    (∀ i, Disjoint (C i) (S : Set _)) ∧
    (completedEdges C ∪ (S : Set _) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
    Fintype.card I + S.card ≤ 9 * Fintype.card V := by
  classical
  dsimp only
  obtain ⟨hsub,hTT,_hown,hRS,_hcount⟩ := reservoir_reservations G P W r hPG hPP hr
  have hS : (allReservoirSpokes W r : Set (Sym2 V)) ⊆ G.edgeSet := by
    rw [coe_allReservoirSpokes]
    exact Set.iUnion_subset (fun b => (hsub b).2)
  have hRR : Pairwise fun b d =>
      Disjoint (reservoirInternal (P b) (W b)) (reservoirInternal (P d) (W d)) := by
    intro b d hbd
    exact (hTT hbd).mono Set.subset_union_left Set.subset_union_left
  have hRO : ∀ b, Disjoint (reservoirInternal (P b) (W b))
      (allReservoirSpokes W r : Set (Sym2 V)) := by
    intro b
    rw [coe_allReservoirSpokes]
    exact hRS.mono_left (Set.subset_iUnion (fun d => reservoirInternal (P d) (W d)) b)
  let R := fun b => reservoirInternal (P b) (W b)
  let H := residualInternalGraph G R C
  have hledger := residue_edge_ledger G R (↑(allReservoirSpokes W r)) C
    (fun b => (hsub b).1) hS hRR hRO hC hCC hcover
  have hsupp : ∀ b, (H b).support ⊆ (W b : Set V) := by
    intro b v hv
    obtain ⟨w,hw⟩ := (H b).mem_support.mp hv
    have he : s(v,w) ∈ (H b).edgeSet := hw
    rw [hledger.1 b] at he
    exact he.1.2 _ (Sym2.mem_mk_left _ _)
  refine ⟨hsupp,?_,hledger.1,hledger.2.1,hledger.2.2.1,
    hledger.2.2.2.1,hledger.2.2.2.2.1,hledger.2.2.2.2.2,?_⟩
  · intro b
    exact induce_edge_image_of_support_subset (H b) (W b) (hsupp b)
  · exact residue_part_count (allReservoirSpokes W r) C hI (allReservoirSpokes_card_le W r)

end
end ErdosGallai

end
end
end

end OAI


-- Upstream module Lovasz

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64 cycleUniverse65 cycleUniverse66 cycleUniverse67 cycleUniverse68 cycleUniverse69 cycleUniverse70 cycleUniverse71 cycleUniverse72 cycleUniverse73 cycleUniverse74 cycleUniverse75 cycleUniverse76 cycleUniverse77 cycleUniverse78 cycleUniverse79 cycleUniverse80 cycleUniverse81 cycleUniverse82 cycleUniverse83 cycleUniverse84 cycleUniverse85

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Lovasz
universe u
noncomputable section
open SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def StarActive {V : Type cycleUniverse1} (S : Set V) (R : V → V → Prop) (v : V) : Prop :=
  ∃ a ∈ S, Relation.ReflTransGen R a v

lemma starActive_source {V : Type cycleUniverse2} {S : Set V} {R : V → V → Prop}
    {v : V} (hv : v ∈ S) : StarActive S R v :=
  ⟨v, hv, .refl⟩

lemma starActive_step {V : Type cycleUniverse3} {S : Set V} {R : V → V → Prop}
    {v w : V} (hv : StarActive S R v) (h : R v w) : StarActive S R w := by
  obtain ⟨a, ha, hr⟩ := hv
  exact ⟨a, ha, hr.tail h⟩

lemma starActive_iff {V : Type cycleUniverse4} {S : Set V} {R : V → V → Prop} {v : V} :
    StarActive S R v ↔ v ∈ S ∨ ∃ w, StarActive S R w ∧ R w v := by
  constructor
  · rintro ⟨a, ha, hr⟩
    rcases hr.cases_tail with rfl | ⟨w, hw, h⟩
    · exact Or.inl ha
    · exact Or.inr ⟨w, ⟨a, ha, hw⟩, h⟩
  · rintro (h | ⟨w, hw, h⟩)
    · exact starActive_source h
    · exact starActive_step hw h

lemma starActive_original_iff {V : Type cycleUniverse5} {S T : Set V} {R : V → V → Prop}
    (hST : Disjoint S T) {v : V} (hv : v ∈ T) :
    StarActive S R v ↔ ∃ w, StarActive S R w ∧ R w v := by
  rw [starActive_iff]
  have hs : v ∉ S := fun h => Set.disjoint_left.mp hST h hv
  simp [hs]

lemma starActive_subset {V : Type cycleUniverse6} {S T : Set V} {R : V → V → Prop}
    (hS : S ⊆ T) (hR : ∀ a b, R a b → b ∈ T) :
    {v | StarActive S R v} ⊆ T := by
  rintro v ⟨a, ha, hr⟩
  rcases hr.cases_tail with rfl | ⟨w, _, h⟩
  · exact hS ha
  · exact hR w v h

lemma starActive_no_loop {V : Type cycleUniverse7} {S : Set V} {R : V → V → Prop}
    (hinj : ∀ a b c, R a c → R b c → a = b)
    (hsource : ∀ a b, a ∈ S → ¬ R b a)
    {v : V} (hv : StarActive S R v) : ¬ R v v := by
  obtain ⟨a, ha, hr⟩ := hv
  induction hr with
  | refl => exact hsource a a ha
  | @tail b c hab hbc ih =>
    intro hcc
    have he : b = c := hinj b c c hbc hcc
    subst c
    exact ih hbc

lemma star_inj {V : Type cycleUniverse8} {x a b : V} : s(x,a) = s(x,b) ↔ a = b := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, h'⟩)
    · exact h
    · exact h'.trans h
  · intro h; exact Or.inl ⟨rfl, h⟩

structure PathPiece {V : Type cycleUniverse9} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PathPiece.ends_ne {V : Type cycleUniverse10} {G : SimpleGraph V} (P : PathPiece G) :
    P.start ≠ P.finish := by
  intro h
  have hz := (P.isPath.nil_iff_eq.mpr h).length_eq_zero
  have := P.positive
  omega

structure Piece {V : Type cycleUniverse11} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : (walk.IsPath ∧ 0 < walk.length) ∨
    ∃ h : finish = start, (walk.copy rfl h).IsCycle

namespace Piece
variable {V : Type cycleUniverse12} {G : SimpleGraph V}

def ofPath (p : PathPiece G) : Piece G :=
  ⟨p.start, p.finish, p.walk, Or.inl ⟨p.isPath, p.positive⟩⟩

def ofCycle {v : V} (p : G.Walk v v) (h : p.IsCycle) : Piece G :=
  ⟨v, v, p, Or.inr ⟨rfl, h⟩⟩

end Piece

structure Arm {V : Type cycleUniverse13} (G : SimpleGraph V) (x : V) where
  near : V
  far : V
  adj : G.Adj x near
  walk : G.Walk near far
  isPath : walk.IsPath
  avoids : x ∉ walk.support

namespace Arm
variable {V : Type cycleUniverse14} {G : SimpleGraph V} {x : V}

def tip (A : Arm G x) : PathPiece G where
  start := x
  finish := A.far
  walk := .cons A.adj A.walk
  isPath := A.isPath.cons A.avoids
  positive := by simp

def flip (A : Arm G x) (h : G.Adj x A.far) : Arm G x where
  near := A.far
  far := A.near
  adj := h
  walk := A.walk.reverse
  isPath := A.isPath.reverse
  avoids := by simpa using A.avoids

@[simp] lemma flip_edges (A : Arm G x) (h : G.Adj x A.far) :
    (A.flip h).walk.edgeSet = A.walk.edgeSet := by simp [flip]

@[simp] lemma mem_flip_support (A : Arm G x) (h : G.Adj x A.far) (v : V) :
    v ∈ (A.flip h).walk.support ↔ v ∈ A.walk.support := by simp [flip]

lemma two_arms_isPath (A B : Arm G x)
    (hd : A.walk.support.Disjoint B.walk.support) :
    ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).IsPath := by
  apply Walk.IsPath.mk'
  simp only [Walk.support_append, Walk.support_reverse, Walk.support_cons,
    List.tail_cons, List.reverse_cons, List.append_assoc]
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_reverse.mpr A.isPath.support_nodup, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨B.avoids, B.isPath.support_nodup⟩
  · rw [List.disjoint_left]
    intro v hv hq
    have hav : v ∈ A.walk.support := List.mem_reverse.mp hv
    rcases List.mem_cons.mp hq with rfl | hq
    · exact A.avoids hav
    · exact List.disjoint_left.mp hd hav hq

def join (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) : PathPiece G where
  start := A.far
  finish := B.far
  walk := (Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)
  isPath := two_arms_isPath A B hd
  positive := by simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons]; omega

lemma join_edges (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    (A.join B hd).walk.edgeSet =
      A.walk.edgeSet ∪ B.walk.edgeSet ∪ {s(x,A.near), s(x,B.near)} := by
  simp only [join, Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons]
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma near_ne (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    A.near ≠ B.near := by
  intro h
  exact List.disjoint_left.mp hd A.walk.start_mem_support (by simpa only [h] using B.walk.start_mem_support)

lemma far_ne (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    A.far ≠ B.far := (A.join B hd).ends_ne

lemma far_ne_center (A : Arm G x) : A.far ≠ x := by
  intro h
  apply A.avoids
  simpa only [h] using A.walk.end_mem_support

lemma star_not_mem (A : Arm G x) (v : V) : s(x,v) ∉ A.walk.edgeSet := by
  intro he
  exact A.avoids (Walk.mem_support_iff_exists_mem_edges.mpr
    (Or.inr ⟨s(x,v), he, by simp⟩))

lemma flip_disjoint_left (A B : Arm G x) (h : G.Adj x A.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    (A.flip h).walk.support.Disjoint B.walk.support := by
  rw [List.disjoint_left] at hd ⊢
  intro v hv hb
  exact hd ((A.mem_flip_support h v).mp hv) hb

lemma flip_disjoint_right (A B : Arm G x) (h : G.Adj x B.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    A.walk.support.Disjoint (B.flip h).walk.support := by
  exact (flip_disjoint_left B A h hd.symm).symm

def orient (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) : Arm G x :=
  if ha : active then A.flip (h ha) else A

@[simp] lemma orient_edges (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).walk.edgeSet = A.walk.edgeSet := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A.flip (h ha) from dif_pos ha)).trans (A.flip_edges _)
  · exact congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A from dif_neg ha)

@[simp] lemma orient_near (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).near = if active then A.far else A.near := by
  by_cases ha : active <;> simp [orient, flip, ha]

@[simp] lemma mem_orient_support (A : Arm G x) (active : Prop)
    (h : active → G.Adj x A.far) (v : V) :
    v ∈ (A.orient active h).walk.support ↔ v ∈ A.walk.support := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A.flip (h ha) from dif_pos ha)).to_iff.trans
        (A.mem_flip_support _ v)
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A from dif_neg ha)).to_iff

lemma orient_disjoint (A B : Arm G x) (p q : Prop)
    (ha : p → G.Adj x A.far) (hb : q → G.Adj x B.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    (A.orient p ha).walk.support.Disjoint (B.orient q hb).walk.support := by
  rw [List.disjoint_left]
  intro v hv hw
  exact List.disjoint_left.mp hd ((A.mem_orient_support p ha v).mp hv)
    ((B.mem_orient_support q hb v).mp hw)

end Arm

inductive Frame {V : Type cycleUniverse15} (G : SimpleGraph V) (x : V) where
  | away (p : PathPiece G) (avoid : x ∉ p.walk.support)
  | tip (A : Arm G x)
  | through (A B : Arm G x) (disjoint : A.walk.support.Disjoint B.walk.support)

namespace Frame
variable {V : Type cycleUniverse16} {G : SimpleGraph V} {x : V}

def path : Frame G x → PathPiece G
  | .away p _ => p
  | .tip A => A.tip
  | .through A B hd => A.join B hd

def Port : Frame G x → Type
  | .away _ _ => Bool
  | .tip _ => Unit
  | .through _ _ _ => Bool

def endpoint : (F : Frame G x) → F.Port → V
  | .away p _, false => p.start
  | .away p _, true => p.finish
  | .tip A, _ => A.far
  | .through A _ _, false => A.far
  | .through _ B _, true => B.far

def exit : (F : Frame G x) → F.Port → Option V
  | .away _ _, _ => none
  | .tip _, _ => none
  | .through A _ _, false => some A.near
  | .through _ B _, true => some B.near

def inserted (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x, F.endpoint p)}

def removed (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, F.exit p = some v ∧ e = s(x,v)}

lemma endpoint_ne_center (F : Frame G x) (p : F.Port) : F.endpoint p ≠ x := by
  cases F with
  | away P hx =>
    cases p
    · change P.start ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.start_mem_support
    · change P.finish ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.end_mem_support
  | tip A => exact A.far_ne_center
  | through A B hd => cases p <;> exact Arm.far_ne_center _

lemma endpoint_injective (F : Frame G x) : Function.Injective F.endpoint := by
  cases F with
  | away P hx =>
    intro a b hab
    cases a <;> cases b <;> first | rfl | exact False.elim (P.ends_ne hab) |
      exact False.elim (P.ends_ne hab.symm)
  | tip A =>
    change Function.Injective (fun (_ : Unit) => A.far)
    exact fun _ _ _ => Subsingleton.elim _ _
  | through A B hd =>
    intro a b hab
    cases a <;> cases b <;> first | rfl | exact False.elim (A.far_ne B hd hab) |
      exact False.elim (A.far_ne B hd hab.symm)

lemma port_iff_endpoint (F : Frame G x) (v : V) :
    (∃ p : F.Port, F.endpoint p = v) ↔
      (F.path.start = v ∨ F.path.finish = v) ∧ v ≠ x := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨?_, (F.endpoint_ne_center p)⟩
    cases F with
    | away P hx => cases p <;> simp [endpoint, path]
    | tip A => exact Or.inr rfl
    | through A B hd => cases p <;> simp [endpoint, path, Arm.join]
  · rintro ⟨he, hx⟩
    cases F with
    | away P hp =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩
    | tip A =>
      rcases he with he | he
      · exact (hx he.symm).elim
      · exact ⟨(), he⟩
    | through A B hd =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩

lemma exit_edge (F : Frame G x) (p : F.Port) (v : V) (h : F.exit p = some v) :
    s(x,v) ∈ F.path.walk.edgeSet := by
  cases F with
  | away P hx => cases h
  | tip A => cases h
  | through A B hd =>
    cases p
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)

lemma removed_subset (F : Frame G x) (active : F.Port → Prop) :
    F.removed active ⊆ F.path.walk.edgeSet := by
  rintro e ⟨p, hp, v, hv, rfl⟩
  exact F.exit_edge p v hv

@[simp] lemma removed_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).removed active = ∅ := by
  ext e; simp [removed, exit]

@[simp] lemma removed_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).removed active = ∅ := by
  ext e; simp [removed, exit]

lemma inserted_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).inserted active =
      (if active false then {s(x,P.start)} else ∅) ∪
      (if active true then {s(x,P.finish)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma inserted_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).inserted active = if active () then {s(x,A.far)} else ∅ := by
  ext e
  by_cases h : active () <;> simp [inserted, endpoint, Port, h]

lemma inserted_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).inserted active =
      (if active false then {s(x,A.far)} else ∅) ∪
      (if active true then {s(x,B.far)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma removed_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).removed active =
      (if active false then {s(x,A.near)} else ∅) ∪
      (if active true then {s(x,B.near)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [removed, exit, Port, Bool.exists_bool, h0, h1, or_comm]

end Frame

lemma replace_two_attachments {E : Type cycleUniverse17} (B : Set E) (e f a b : E)
    (he : e ∉ B) (hf : f ∉ B) (hne : e ≠ f) (p q : Prop) [Decidable p] [Decidable q] :
    ((B ∪ {e,f}) \ ((if p then {e} else ∅) ∪ (if q then {f} else ∅))) ∪
      ((if p then {a} else ∅) ∪ (if q then {b} else ∅)) =
      B ∪ {if p then a else e, if q then b else f} := by
  classical
  ext z
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp, hq, ↓reduceIte, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false] <;> aesop

namespace Frame
variable {V : Type cycleUniverse18} {G : SimpleGraph V} {x : V}

lemma modify_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.through A B hd).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.through A B hd).path.walk.edgeSet \ (Frame.through A B hd).removed active) ∪
        (Frame.through A B hd).inserted active := by
  have ha : active false → G.Adj x A.far := hadj false
  have hb : active true → G.Adj x B.far := hadj true
  let A' := A.orient (active false) ha
  let B' := B.orient (active true) hb
  have hd' : A'.walk.support.Disjoint B'.walk.support :=
    A.orient_disjoint B _ _ _ _ hd
  refine ⟨Piece.ofPath (A'.join B' hd'), ?_⟩
  have he : s(x,A.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hf : s(x,B.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hne : s(x,A.near) ≠ s(x,B.near) := fun h => A.near_ne B hd (star_inj.mp h)
  change (A'.join B' hd').walk.edgeSet = _
  rw [inserted_through, removed_through]
  change (A'.join B' hd').walk.edgeSet = ((A.join B hd).walk.edgeSet \ _) ∪ _
  rw [Arm.join_edges, Arm.join_edges]
  dsimp only [A', B']
  simp only [Arm.orient_edges, Arm.orient_near]
  have hh := (replace_two_attachments _ _ _ s(x,A.far) s(x,B.far) he hf hne
    (active false) (active true)).symm
  by_cases h0 : active false <;> by_cases h1 : active true
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simp [h0, h1]

lemma modify_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.tip A).endpoint p))
    (hnew : ∀ p, active p → s(x,(Frame.tip A).endpoint p) ∉
      (Frame.tip A).path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.tip A).path.walk.edgeSet \ (Frame.tip A).removed active) ∪
        (Frame.tip A).inserted active := by
  rw [removed_tip, inserted_tip, Set.sdiff_empty]
  by_cases ha : active ()
  · have haG : G.Adj x A.far := hadj () ha
    have he : s(A.far,x) ∉ A.tip.walk.edges := by
      intro he
      exact hnew () ha (Sym2.eq_swap ▸ he)
    let c : G.Walk A.far A.far := Walk.cons haG.symm A.tip.walk
    have hc : c.IsCycle := Path.cons_isCycle ⟨A.tip.walk,A.tip.isPath⟩ _ he
    refine ⟨Piece.ofCycle c hc, ?_⟩
    change c.edgeSet = _
    dsimp only [c, Arm.tip, path]
    simp only [Walk.edgeSet_cons, ha, ↓reduceIte]
    rw [Sym2.eq_swap]
    ext e
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  · refine ⟨Piece.ofPath A.tip, ?_⟩
    simp [Piece.ofPath, path, ha]

lemma modify_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.away P hx).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.away P hx).path.walk.edgeSet \ (Frame.away P hx).removed active) ∪
        (Frame.away P hx).inserted active := by
  rw [removed_away, inserted_away, Set.sdiff_empty]
  change ∃ Q : Piece G, Q.walk.edgeSet = P.walk.edgeSet ∪ _
  by_cases h0 : active false
  · have h0G : G.Adj x P.start := hadj false h0
    let q : G.Walk x P.finish := Walk.cons h0G P.walk
    have hq : q.IsPath := P.isPath.cons hx
    by_cases h1 : active true
    · have he : s(P.finish,x) ∉ q.edges := by
        intro he
        have hh := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
        have hp := P.positive
        simp only [q, Walk.length_cons] at hh
        omega
      have h1G : G.Adj x P.finish := hadj true h1
      let c : G.Walk P.finish P.finish := Walk.cons h1G.symm q
      have hc : c.IsCycle := Path.cons_isCycle ⟨q,hq⟩ _ he
      refine ⟨Piece.ofCycle c hc, ?_⟩
      change c.edgeSet = _
      simp only [c, q, Walk.edgeSet_cons, h0, h1, ↓reduceIte]
      rw [Sym2.eq_swap]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · let Q : PathPiece G := ⟨x, P.finish, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, h0, h1, ↓reduceIte, Set.union_empty]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
  · by_cases h1 : active true
    · have h1G : G.Adj x P.finish := hadj true h1
      let q : G.Walk x P.start := Walk.cons h1G P.walk.reverse
      have hq : q.IsPath := P.isPath.reverse.cons (by simpa using hx)
      let Q : PathPiece G := ⟨x, P.start, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, Walk.edgeSet_reverse, h0, h1, ↓reduceIte,
        Set.empty_union]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · refine ⟨Piece.ofPath P, ?_⟩
      simp [Piece.ofPath, h0, h1]

theorem modify (F : Frame G x) (active : F.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (F.endpoint p))
    (hnew : ∀ p, active p → F.exit p = none → s(x,F.endpoint p) ∉ F.path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet = (F.path.walk.edgeSet \ F.removed active) ∪
      F.inserted active := by
  cases F with
  | away P hx => exact modify_away P hx active hadj
  | through A B hd => exact modify_through A B hd active hadj
  | tip A => exact modify_tip A active hadj (fun p hp => hnew p hp rfl)

end Frame

theorem rewire_partition {E : Type cycleUniverse19} {I : Type cycleUniverse20} (old remove add : I → Set E) (fresh : Set E)
    (hsub : ∀ i, remove i ⊆ old i)
    (hold : Pairwise fun i j => Disjoint (old i) (old j))
    (hadd : Pairwise fun i j => Disjoint (add i) (add j))
    (hfresh : Disjoint fresh (⋃ i, old i))
    (hbalance : (⋃ i, add i) = (⋃ i, remove i) ∪ fresh) :
    Pairwise (fun i j => Disjoint ((old i \ remove i) ∪ add i)
      ((old j \ remove j) ∪ add j)) ∧
    (⋃ i, ((old i \ remove i) ∪ add i)) = (⋃ i, old i) ∪ fresh := by
  have hcross : ∀ i j, Disjoint (old i \ remove i) (add j) := by
    intro i j
    apply Set.disjoint_left.mpr
    rintro e ⟨hei, hnot⟩ hej
    have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
      rw [← hbalance]
      exact Set.mem_iUnion.mpr ⟨j, hej⟩
    rcases hh with hh | hh
    · obtain ⟨l, hel⟩ := Set.mem_iUnion.mp hh
      by_cases hil : i = l
      · subst l; exact hnot hel
      · exact Set.disjoint_left.mp (hold hil) hei (hsub l hel)
    · exact Set.disjoint_left.mp hfresh hh (Set.mem_iUnion.mpr ⟨i, hei⟩)
  constructor
  · intro i j hij
    exact Disjoint.union_left
      (Disjoint.union_right ((hold hij).mono Set.sdiff_subset Set.sdiff_subset) (hcross i j))
      (Disjoint.union_right (hcross j i).symm (hadd hij))
  · ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi.1⟩)
      · have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
          rw [← hbalance]
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        rcases hh with hh | hh
        · obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hh
          exact Or.inl (Set.mem_iUnion.mpr ⟨l, hsub l hl⟩)
        · exact Or.inr hh
    · rintro (he | he)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        by_cases hr : e ∈ remove i
        · have hh : e ∈ ⋃ l, add l := by
            rw [hbalance]
            exact Or.inl (Set.mem_iUnion.mpr ⟨i, hr⟩)
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
          exact Set.mem_iUnion.mpr ⟨j, Or.inr hj⟩
        · exact Set.mem_iUnion.mpr ⟨i, Or.inl ⟨hi, hr⟩⟩
      · have hh : e ∈ ⋃ l, add l := by rw [hbalance]; exact Or.inr he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨i, Or.inr hi⟩

inductive Centered {V : Type cycleUniverse21} (G : SimpleGraph V) (x : V) where
  | path (F : Frame G x)
  | cycle {v : V} (c : G.Walk v v) (hc : c.IsCycle)

namespace Centered
variable {V : Type cycleUniverse22} {G : SimpleGraph V} {x : V}

def piece : Centered G x → Piece G
  | .path F => .ofPath F.path
  | .cycle c hc => .ofCycle c hc

def Port : Centered G x → Type
  | .path F => F.Port
  | .cycle _ _ => Empty

def endpoint : (K : Centered G x) → K.Port → V
  | .path F, p => F.endpoint p
  | .cycle _ _, p => nomatch p

def exit : (K : Centered G x) → K.Port → Option V
  | .path F, p => F.exit p
  | .cycle _ _, p => nomatch p

def inserted (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x,K.endpoint p)}

def removed (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, K.exit p = some v ∧ e = s(x,v)}

lemma exit_edge (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    s(x,v) ∈ K.piece.walk.edgeSet := by
  cases K with
  | path F => exact F.exit_edge p v h
  | cycle c hc => exact p.elim

lemma exit_adj (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    G.Adj x v := by
  exact G.mem_edgeSet.mp (K.piece.walk.edges_subset_edgeSet (K.exit_edge p v h))

lemma exit_none_all (K : Centered G x) (p : K.Port) (h : K.exit p = none) :
    ∀ q, K.exit q = none := by
  cases K with
  | cycle c hc => exact p.elim
  | path F =>
    cases F with
    | away P hx => exact fun _ => rfl
    | tip A => exact fun _ => rfl
    | through A B hd => cases p <;> cases h

lemma removed_subset (K : Centered G x) (active : K.Port → Prop) :
    K.removed active ⊆ K.piece.walk.edgeSet := by
  rintro e ⟨p, hp, v, hv, rfl⟩
  exact K.exit_edge p v hv

lemma modify (K : Centered G x) (active : K.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (K.endpoint p))
    (hnew : ∀ p, active p → K.exit p = none →
      s(x,K.endpoint p) ∉ K.piece.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      (K.piece.walk.edgeSet \ K.removed active) ∪ K.inserted active := by
  cases K with
  | path F => exact F.modify active hadj hnew
  | cycle c hc =>
    refine ⟨.ofCycle c hc, ?_⟩
    have hr : (Centered.cycle c hc).removed active = ∅ := by
      ext e; simp only [removed, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    have hi : (Centered.cycle c hc).inserted active = ∅ := by
      ext e; simp only [inserted, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    simp only [hr, hi, Set.sdiff_empty, Set.union_empty]
    rfl

end Centered

theorem restore_selected {V : Type cycleUniverse23} {I : Type cycleUniverse24} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (selected : Set (Σ i, (K i).Port))
    (hinj : Set.InjOn (fun z : Σ i, (K i).Port => (K z.1).endpoint z.2) selected)
    (hcov : ∀ v, G.Adj x v → ∃ z ∈ selected, (K z.1).endpoint z.2 = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let R : V → V → Prop := fun a b => ∃ z ∈ selected,
    (K z.1).endpoint z.2 = a ∧ (K z.1).exit z.2 = some b
  let active : (i : I) → (K i).Port → Prop := fun i p =>
    (⟨i,p⟩ : Σ j, (K j).Port) ∈ selected ∧ StarActive S R ((K i).endpoint p)
  have hactive_adj : ∀ v, StarActive S R v → G.Adj x v := by
    intro v hv
    exact starActive_subset (T := {v | G.Adj x v}) hS
      (by rintro a b ⟨z, _, _, hz⟩; exact (K z.1).exit_adj z.2 b hz) hv
  have hbalance : (⋃ i, (K i).inserted (active i)) =
      (⋃ i, (K i).removed (active i)) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
    ext e
    constructor
    · intro he
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp he
      rcases (starActive_iff.mp hp.2) with hs | ⟨w, hw, z, hz, hzw, hzv⟩
      · exact Or.inr ⟨_, hs, rfl⟩
      · exact Or.inl (Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzw.symm ▸ hw⟩,
          _, hzv, rfl⟩)
    · rintro (he | ⟨v, hv, rfl⟩)
      · obtain ⟨i, p, hp, v, hpv, rfl⟩ := Set.mem_iUnion.mp he
        have hv : StarActive S R v := starActive_step hp.2 ⟨⟨i,p⟩, hp.1, rfl, hpv⟩
        obtain ⟨z, hz, hzv⟩ := hcov v (hactive_adj v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ hv⟩, congrArg (s(x,·)) hzv.symm⟩
      · obtain ⟨z, hz, hzv⟩ := hcov v (hS v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ starActive_source hv⟩,
          congrArg (s(x,·)) hzv.symm⟩
  have hadd : Pairwise fun i j =>
      Disjoint ((K i).inserted (active i)) ((K j).inserted (active j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    have h : (⟨i,p⟩ : Σ l, (K l).Port) = ⟨j,q⟩ :=
      hinj hp.1 hq.1 (star_inj.mp (he.symm.trans hf))
    exact hij (congrArg Sigma.fst h)
  have hnew : ∀ i p, active i p → (K i).exit p = none →
      s(x,(K i).endpoint p) ∉ (K i).piece.walk.edgeSet := by
    intro i p hp hn he
    have ha : s(x,(K i).endpoint p) ∈ ⋃ j, (K j).inserted (active j) :=
      Set.mem_iUnion.mpr ⟨i, p, hp, rfl⟩
    rw [hbalance] at ha
    rcases ha with ha | ha
    · obtain ⟨j, q, hq, v, hqv, hev⟩ := Set.mem_iUnion.mp ha
      have hej : s(x,(K i).endpoint p) ∈ (K j).piece.walk.edgeSet :=
        hev ▸ (K j).exit_edge q v hqv
      have hij : i = j := by
        by_contra h; exact Set.disjoint_left.mp (hold h) he hej
      subst j
      rw [(K i).exit_none_all p hn q] at hqv
      cases hqv
    · exact Set.disjoint_left.mp hfresh ha (Set.mem_iUnion.mpr ⟨i, he⟩)
  choose Q hQ using fun i => (K i).modify (active i)
    (fun p hp => hactive_adj _ hp.2) (hnew i)
  have hh := rewire_partition (fun i => (K i).piece.walk.edgeSet)
    (fun i => (K i).removed (active i)) (fun i => (K i).inserted (active i))
    {e | ∃ v ∈ S, e = s(x,v)} (fun i => (K i).removed_subset _) hold hadd hfresh hbalance
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hQ] using hh.1
  · simpa only [hQ] using hh.2

theorem restore_star {V : Type cycleUniverse25} {I : Type cycleUniverse26} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (hcov : ∀ v, G.Adj x v → ∃ i p, (K i).endpoint p = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let T := {v // G.Adj x v}
  have hh : ∀ v : T, ∃ z : Σ i, (K i).Port, (K z.1).endpoint z.2 = v.val := by
    intro v
    obtain ⟨i,p,h⟩ := hcov v.val v.property
    exact ⟨⟨i,p⟩,h⟩
  choose f hf using hh
  apply restore_selected G x K S hS hold hfresh (Set.range f)
  · rintro z ⟨v,rfl⟩ w ⟨u,rfl⟩ he
    have hvu : v = u := Subtype.ext ((hf v).symm.trans (he.trans (hf u)))
    exact congrArg f hvu
  · intro v hv
    exact ⟨f ⟨v,hv⟩, ⟨⟨v,hv⟩, rfl⟩, hf ⟨v,hv⟩⟩

namespace Arm
variable {V : Type cycleUniverse27} {G : SimpleGraph V} {x b : V}

def fromWalk (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) : Arm G x :=
  match w with
  | .nil => False.elim (hn .nil)
  | @Walk.cons _ _ _ y _ h q =>
    ⟨y, b, h, q, (Walk.cons_isPath_iff h q).mp hp |>.1,
      (Walk.cons_isPath_iff h q).mp hp |>.2⟩

@[simp] lemma fromWalk_far (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).far = b := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_support (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).walk.support = w.support.tail := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_tip_edges (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).tip.walk.edgeSet = w.edgeSet := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl
end Arm

lemma PathPiece.exists_frame {V : Type cycleUniverse28} {G : SimpleGraph V} (P : PathPiece G) (x : V) :
    ∃ F : Frame G x, F.path.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, (F.path.start = v ∨ F.path.finish = v) ↔ (P.start = v ∨ P.finish = v) := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨q,r,hq,hr,hqr⟩ := P.isPath.mem_support_iff_exists_append.mp hx
    have hp : (q.append r).IsPath := hqr ▸ P.isPath
    by_cases hqn : q.Nil
    · have hx : P.start = x := hqn.eq
      have hrn : ¬r.Nil := by
        intro hn; exact P.ends_ne (hx.trans hn.eq)
      let A := Arm.fromWalk r hr hrn
      refine ⟨.tip A, ?_, ?_⟩
      · change A.tip.walk.edgeSet = P.walk.edgeSet
        rw [Arm.fromWalk_tip_edges]
        rw [hqr, Walk.edgeSet_append]
        simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hqn]
      · intro v
        change (x = v ∨ A.far = v) ↔ _
        simp only [A, Arm.fromWalk_far, hx]
    · by_cases hrn : r.Nil
      · have hx : x = P.finish := hrn.eq
        have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        refine ⟨.tip A, ?_, ?_⟩
        · change A.tip.walk.edgeSet = P.walk.edgeSet
          rw [Arm.fromWalk_tip_edges, Walk.edgeSet_reverse]
          rw [hqr, Walk.edgeSet_append]
          simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hrn]
        · intro v
          change (x = v ∨ A.far = v) ↔ _
          simp only [A, Arm.fromWalk_far, hx, or_comm]
      · have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        let B := Arm.fromWalk r hr hrn
        have hd : A.walk.support.Disjoint B.walk.support := by
          rw [Arm.fromWalk_support, Arm.fromWalk_support]
          have hd := hp.disjoint_support_of_append hrn
          rw [Walk.support_tail_of_not_nil r hrn] at hd
          apply List.disjoint_left.mpr
          intro v hv hw
          exact List.disjoint_left.mp hd
            (by simpa using (List.mem_of_mem_tail hv : v ∈ q.reverse.support)) hw
        refine ⟨.through A B hd, ?_, ?_⟩
        · change ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).edgeSet = _
          rw [Walk.edgeSet_append, Walk.edgeSet_reverse]
          change A.tip.walk.edgeSet ∪ B.tip.walk.edgeSet = _
          rw [Arm.fromWalk_tip_edges, Arm.fromWalk_tip_edges, Walk.edgeSet_reverse,
            hqr, Walk.edgeSet_append]
        · intro v
          change (A.far = v ∨ B.far = v) ↔ _
          simp only [A, B, Arm.fromWalk_far]
  · exact ⟨.away P hx, rfl, fun _ => Iff.rfl⟩

namespace Piece
variable {V : Type cycleUniverse29} {G H : SimpleGraph V}

lemma isTrail (P : Piece G) : P.walk.IsTrail := by
  rcases P.simple with hp | ⟨h,hc⟩
  · exact hp.1.isTrail
  · exact (P.walk.isTrail_copy rfl h).mp hc.isTrail

def mapLe (h : H ≤ G) (P : Piece H) : Piece G := by
  rcases P with ⟨a,b,w,hs⟩
  refine ⟨a,b,w.mapLe h, ?_⟩
  rcases hs with hp | ⟨hb,hc⟩
  · exact Or.inl ⟨hp.1.mapLe h, by simpa using hp.2⟩
  · subst b
    exact Or.inr ⟨rfl, by simpa using hc.mapLe h⟩

@[simp] lemma mapLe_edges (h : H ≤ G) (P : Piece H) :
    (P.mapLe h).walk.edgeSet = P.walk.edgeSet := by
  cases P
  exact Walk.edgeSet_mapLe_eq_edgeSet _ _

@[simp] lemma mapLe_start (h : H ≤ G) (P : Piece H) : (P.mapLe h).start = P.start := by
  cases P; rfl
@[simp] lemma mapLe_finish (h : H ≤ G) (P : Piece H) : (P.mapLe h).finish = P.finish := by
  cases P; rfl

lemma exists_centered (P : Piece G) (x : V) :
    ∃ K : Centered G x, K.piece.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, P.start ≠ P.finish → (P.start = v ∨ P.finish = v) → v ≠ x →
        ∃ p, K.endpoint p = v := by
  rcases P with ⟨a,b,w,hs⟩
  rcases hs with hp | ⟨hb,hc⟩
  · let Q : PathPiece G := ⟨a,b,w,hp.1,hp.2⟩
    obtain ⟨F,he,hv⟩ := Q.exists_frame x
    refine ⟨.path F, he, ?_⟩
    intro v _ he hx
    exact (F.port_iff_endpoint v).mpr ⟨(hv v).mpr he, hx⟩
  · subst b
    refine ⟨.cycle w (by simpa using hc), rfl, ?_⟩
    exact fun _ hn => (hn rfl).elim
end Piece

theorem trail_partition_degree_sum {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse32} {I : Type cycleUniverse33} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

lemma endpoint_of_odd {V : Type cycleUniverse34} {I : Type cycleUniverse35} [Fintype V] [Fintype I]
    (H : SimpleGraph V) (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet)
    (v : V) (hv : Odd (H.degree v)) :
    ∃ i, (P i).start ≠ (P i).finish ∧ ((P i).start = v ∨ (P i).finish = v) := by
  classical
  have ho := (trail_partition_even_degree_iff H (fun i => (P i).walk)
    (fun i => (P i).isTrail) hd hc v).not.mp (Nat.not_even_iff_odd.mpr hv)
  have hp : 0 < (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card := by
    by_contra hn
    have hz : (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card = 0 := by omega
    exact ho (hz ▸ ⟨0, rfl⟩)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, (Finset.mem_filter.mp hi).2.1, by
    simpa only [eq_comm] using (Finset.mem_filter.mp hi).2.2⟩

theorem restore_partition {V : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V] [Fintype I]
    (G H : SimpleGraph V) (hHG : H ≤ G) (x : V) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hedges : G.edgeSet = H.edgeSet ∪ {e | ∃ v ∈ S, e = s(x,v)})
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} H.edgeSet)
    (hodd : ∀ v, G.Adj x v → Odd (H.degree v))
    (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  choose K hk hv using fun i => ((P i).mapLe hHG).exists_centered x
  have he : ∀ i, (K i).piece.walk.edgeSet = (P i).walk.edgeSet := by
    intro i; exact (hk i).trans ((P i).mapLe_edges hHG)
  have hKC : (⋃ i, (K i).piece.walk.edgeSet) = H.edgeSet := by simpa only [he] using hc
  obtain ⟨Q,hQ,hQC⟩ := restore_star G x K S hS
    (by simpa only [he] using hd) (by rwa [hKC]) (by
      intro v hxv
      obtain ⟨i, hi, hiv⟩ := endpoint_of_odd H P hd hc v (hodd v hxv)
      obtain ⟨p,hp⟩ := hv i v (by simpa using hi) (by simpa using hiv) hxv.ne.symm
      exact ⟨i,p,hp⟩)
  exact ⟨Q,hQ,by simpa only [hKC, ← hedges] using hQC⟩

def activeOrder {V : Type cycleUniverse38} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.support.toFinset.card

lemma activeOrder_mono {V : Type cycleUniverse39} [Fintype V] {G H : SimpleGraph V} (h : H ≤ G) :
    activeOrder H ≤ activeOrder G := by
  apply Finset.card_le_card
  intro v hv
  exact Set.mem_toFinset.mpr (SimpleGraph.support_mono h (Set.mem_toFinset.mp hv))

def HasPartition {V : Type cycleUniverse40} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Piece G),
    (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧ 2 * k ≤ activeOrder G

def evenStarVertices {V : Type cycleUniverse41} [Fintype V] (G : SimpleGraph V) (x : V) : Set V :=
  {y | G.Adj x y ∧ Even (G.degree y)}

def evenStarEdges {V : Type cycleUniverse42} [Fintype V] (G : SimpleGraph V) (x : V) : Set (Sym2 V) :=
  {e | ∃ y ∈ evenStarVertices G x, e = s(x,y)}

def deleteEvenStar {V : Type cycleUniverse43} [Fintype V] (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (evenStarEdges G x)

lemma evenStar_subset {V : Type cycleUniverse44} [Fintype V] (G : SimpleGraph V) (x : V) :
    evenStarEdges G x ⊆ G.edgeSet := by
  rintro e ⟨y,hy,rfl⟩; exact hy.1

lemma deleteEvenStar_neighbor_even {V : Type cycleUniverse45} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = (G.neighborFinset v).erase x := by
  classical
  ext w
  rw [Finset.mem_erase, (deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  constructor
  · rintro ⟨hvw, hn⟩
    refine ⟨?_,hvw⟩
    intro hw; subst w
    exact hn ⟨v,⟨hxv,he⟩, Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨hw,hvw⟩
    refine ⟨hvw, ?_⟩
    rintro ⟨y,_,h⟩
    rcases h with ⟨h,_⟩ | ⟨_,h⟩
    · exact hxv.ne h.symm
    · exact hw h

lemma deleteEvenStar_neighbor_odd {V : Type cycleUniverse46} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : ¬Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = G.neighborFinset v := by
  classical
  ext w
  rw [(deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
  rintro ⟨y,hy,h⟩
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  · exact hxv.ne h.symm
  · subst y; exact he hy.2

lemma deleteEvenStar_neighbor_degree {V : Type cycleUniverse47} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) : Odd ((deleteEvenStar G x).degree v) := by
  classical
  by_cases he : Even (G.degree v)
  · have hcard := Finset.card_erase_add_one (s := G.neighborFinset v)
      (a := x) (by simpa using hxv.symm)
    rw [← deleteEvenStar_neighbor_even G x v hxv he,
      G.card_neighborFinset_eq_degree, (deleteEvenStar G x).card_neighborFinset_eq_degree] at hcard
    obtain ⟨k,hk⟩ := he
    exact ⟨k-1, by omega⟩
  · rw [← (deleteEvenStar G x).card_neighborFinset_eq_degree v,
      deleteEvenStar_neighbor_odd G x v hxv he, G.card_neighborFinset_eq_degree]
    exact Nat.not_even_iff_odd.mp he

lemma deleteEvenStar_edges {V : Type cycleUniverse48} [Fintype V] (G : SimpleGraph V) (x : V) :
    G.edgeSet = (deleteEvenStar G x).edgeSet ∪ evenStarEdges G x := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges,
    Set.sdiff_union_of_subset (evenStar_subset G x)]

lemma deleteEvenStar_fresh {V : Type cycleUniverse49} [Fintype V] (G : SimpleGraph V) (x : V) :
    Disjoint (evenStarEdges G x) (deleteEvenStar G x).edgeSet := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges]
  exact Set.disjoint_sdiff_right

lemma deleteEvenStar_lt {V : Type cycleUniverse50} [Fintype V] (G : SimpleGraph V) (x y : V)
    (hxy : G.Adj x y) (he : Even (G.degree y)) :
    (deleteEvenStar G x).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro e he
    exact G.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono
      (show deleteEvenStar G x ≤ G from G.deleteEdges_le _)
      ((deleteEvenStar G x).mem_edgeFinset.mp he))
  · intro h
    have hh : s(x,y) ∈ (deleteEvenStar G x).edgeFinset := h.symm ▸ G.mem_edgeFinset.mpr hxy
    have hf : s(x,y) ∈ evenStarEdges G x := ⟨y,⟨hxy,he⟩,rfl⟩
    exact Set.disjoint_left.mp (deleteEvenStar_fresh G x) hf (SimpleGraph.mem_edgeFinset.mp hh)

theorem even_vertex_step {V : Type cycleUniverse51} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph V, H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (hpos : ∃ y, 0 < G.degree y ∧ Even (G.degree y)) : HasPartition G := by
  classical
  obtain ⟨y,hy,he⟩ := hpos
  obtain ⟨x,hxy⟩ := (G.degree_pos_iff_exists_adj y).mp hy
  let H := deleteEvenStar G x
  obtain ⟨k,P,hd,hc,hk⟩ := hIH H (deleteEvenStar_lt G x y hxy.symm he)
  obtain ⟨Q,hQ,hQC⟩ := restore_partition G H (G.deleteEdges_le _) x
    (evenStarVertices G x) (fun _ h => h.1) (deleteEvenStar_edges G x)
    (deleteEvenStar_fresh G x) (deleteEvenStar_neighbor_degree G x) P hd hc
  exact ⟨k,Q,hQ,hQC,hk.trans (activeOrder_mono (G.deleteEdges_le _))⟩

lemma single_edge_piece {V : Type cycleUniverse52} (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ P : Piece G, P.walk.edgeSet = {e} := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    let P : PathPiece G := ⟨a,b,Walk.cons hab Walk.nil,
      (Walk.IsPath.nil).cons (by simpa using hab.ne), by simp⟩
    exact ⟨.ofPath P, by simp [Piece.ofPath, P]⟩

lemma partition_single_edges {V : Type cycleUniverse53} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Fin G.edgeFinset.card → Piece G,
      (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = G.edgeSet := by
  classical
  choose P hP using fun e : G.edgeSet => single_edge_piece G e.val e.property
  let e : G.edgeSet ≃ Fin G.edgeFinset.card := (Fintype.equivFin G.edgeSet).trans
    (finCongr (G.card_edgeSet))
  refine ⟨fun i => P (e.symm i), ?_, ?_⟩
  · intro i j hij
    rw [hP, hP]
    exact Set.disjoint_singleton.mpr (fun h => hij (e.symm.injective (Subtype.ext h)))
  · ext z
    simp only [Set.mem_iUnion,hP,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩; exact (e.symm i).property
    · intro hz
      exact ⟨e ⟨z,hz⟩, by simp⟩

lemma matching_partition {V : Type cycleUniverse54} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 1) : HasPartition G := by
  classical
  obtain ⟨P,hd,hc⟩ := partition_single_edges G
  refine ⟨_,P,hd,hc,?_⟩
  rw [← G.sum_degrees_support_eq_twice_card_edges]
  simpa [activeOrder] using Finset.sum_le_sum (s := G.support.toFinset)
    (f := fun v => G.degree v) (g := fun _ => 1) (fun v _ => hdeg v)

def subdivision {V : Type cycleUniverse55} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | some a, some b => G.Adj a b ∧ s(a,b) ≠ s(x,y)
    | none, some b => b = x ∨ b = y
    | some a, none => a = x ∨ a = y
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by
    intro a h
    cases a
    · exact h
    · exact G.irrefl h.1⟩

@[simp] lemma subdivision_some {V : Type cycleUniverse56} (G : SimpleGraph V) (x y a b : V) :
    (subdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := Iff.rfl
@[simp] lemma subdivision_none_some {V : Type cycleUniverse57} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj none (some a) ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_some_none {V : Type cycleUniverse58} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj (some a) none ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_none_none {V : Type cycleUniverse59} (G : SimpleGraph V) (x y : V) :
    ¬(subdivision G x y).Adj none none := id

def halfSubdivision {V : Type cycleUniverse60} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) :=
  (subdivision G x y).deleteEdges {s(none,some x)}

@[simp] lemma half_some {V : Type cycleUniverse61} (G : SimpleGraph V) (x y a b : V) :
    (halfSubdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp []

@[simp] lemma half_none_some {V : Type cycleUniverse62} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj none (some a) ↔ a = y := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp only [subdivision_none_some, Set.mem_singleton_iff, star_inj, Option.some.injEq]
  aesop

@[simp] lemma half_some_none {V : Type cycleUniverse63} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj (some a) none ↔ a = y := by
  rw [(halfSubdivision G x y).adj_comm, half_none_some G x y a hxy]

lemma option_degree_some {V : Type cycleUniverse64} [Fintype V] (K : SimpleGraph (Option V)) (v : V) :
    K.degree (some v) = (Finset.univ.filter (fun u : V => K.Adj (some v) (some u))).card +
      if K.Adj (some v) none then 1 else 0 := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  omega

lemma option_degree_none {V : Type cycleUniverse65} [Fintype V] (K : SimpleGraph (Option V)) :
    K.degree none = (Finset.univ.filter (fun u : V => K.Adj none (some u))).card := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp

lemma subdivision_old_neighbors {V : Type cycleUniverse66} [Fintype V] (G : SimpleGraph V)
    (x y v : V) :
    (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) =
      if v = x then (G.neighborFinset v).erase y else
      if v = y then (G.neighborFinset v).erase x else G.neighborFinset v := by
  classical
  ext u
  by_cases hx : v = x
  · subst v
    simp [eq_comm, and_comm]
    aesop
  · by_cases hy : v = y
    · subst v
      simp [hx,  eq_comm, and_comm]
      tauto
    · simp [hx, hy]

lemma subdivision_degree {V : Type cycleUniverse67} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (subdivision G x y).degree (some v) = G.degree v := by
  classical
  rw [option_degree_some, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy]

lemma subdivision_degree_none {V : Type cycleUniverse68} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (subdivision G x y).degree none = 2 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (subdivision G x y).Adj none (some u)) =
      {x,y} := by ext u; simp
  rw [he]
  simp [hxy.ne]

lemma half_degree {V : Type cycleUniverse69} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).degree (some v) + (if v = x then 1 else 0) = G.degree v := by
  classical
  rw [option_degree_some]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj (some v) (some u)) =
      (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) := by
    ext u; simp
  rw [he, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa [hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx, hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy,half_some_none G x y v hxy.ne]

lemma half_degree_none {V : Type cycleUniverse70} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (halfSubdivision G x y).degree none = 1 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj none (some u)) =
      {y} := by ext u; simp [half_none_some G x y u hxy.ne]
  rw [he]
  simp

lemma subdivision_edge_count {V : Type cycleUniverse71} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (subdivision G x y).edgeFinset.card = G.edgeFinset.card + 1 := by
  classical
  have hd := (subdivision G x y).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, subdivision_degree_none G x y hxy] at hd
  simp_rw [subdivision_degree G x y _ hxy] at hd
  rw [G.sum_degrees_eq_twice_card_edges] at hd
  omega

lemma half_edge_count {V : Type cycleUniverse72} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).edgeFinset.card = G.edgeFinset.card := by
  classical
  have he : (halfSubdivision G x y).edgeFinset =
      (subdivision G x y).edgeFinset.erase s(none,some x) := by
    ext e
    rw [(halfSubdivision G x y).mem_edgeFinset, Finset.mem_erase,
      (subdivision G x y).mem_edgeFinset]
    simp [halfSubdivision, SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [he, Finset.card_erase_of_mem, subdivision_edge_count G x y hxy]
  · omega
  · exact (subdivision G x y).mem_edgeFinset.mpr (Or.inl rfl)

lemma subdivision_activeOrder {V : Type cycleUniverse73} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    activeOrder (subdivision G x y) = activeOrder G + 1 := by
  classical
  have he : (subdivision G x y).support.toFinset =
      insert none (G.support.toFinset.image Option.some) := by
    ext v
    cases v with
    | none => simp [← SimpleGraph.degree_pos_iff_mem_support, subdivision_degree_none G x y hxy]
    | some v =>
      simp only [Set.mem_toFinset, Finset.mem_insert, Option.some_ne_none, Finset.mem_image,
        Option.some.injEq, false_or, exists_eq_right]
      rw [← (subdivision G x y).degree_pos_iff_mem_support,
        subdivision_degree G x y v hxy, G.degree_pos_iff_mem_support]
  dsimp [activeOrder]
  rw [he, Finset.card_insert_of_notMem, Finset.card_image_of_injective]
  · exact Option.some_injective V
  · simp

lemma suppress_path {V : Type cycleUniverse74} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    {a b : V} (p : (subdivision G x y).Walk (some a) (some b)) (hp : p.IsPath) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.support = p.support.filterMap id ∧
      ∀ e : Sym2 V, e ∈ q.edgeSet ↔
        e.map Option.some ∈ p.edgeSet ∨ (e = s(x,y) ∧ s(none,some x) ∈ p.edgeSet) := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    cases p with
    | nil =>
      refine ⟨.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | @cons _ v _ h p =>
      have ht : p.IsPath := hp.of_cons
      have ha : some a ∉ p.support := (Walk.cons_isPath_iff _ _ |>.mp hp).2
      cases v with
      | some c =>
        obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht rfl
        have hac : G.Adj a c := (subdivision_some G x y a c).mp h |>.1
        refine ⟨.cons hac q, hq.cons ?_, ?_, ?_⟩
        · intro ha'
          apply ha
          rw [hqs] at ha'
          simpa using ha'
        · simp [hqs]
        · intro e
          have hinj : Function.Injective (Sym2.map (Option.some : V → Option V)) :=
            Sym2.map.injective (Option.some_injective V)
          have he : e.map Option.some = s(some a,some c) ↔ e = s(a,c) :=
            by simpa only [Sym2.map_mk] using (hinj.eq_iff (a := e) (b := s(a,c)))
          have hnedge : s(none,some x) ≠ s(some a,some c) := by simp []
          simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he, hnedge, false_or, hqe]
          tauto
      | none =>
        cases p with
        | @cons _ v _ h' p =>
          cases v with
          | none => exact (h'.ne rfl).elim
          | some c =>
            have hac : a ≠ c := by
              intro he
              apply ha
              simp [he]
            have hae : a = x ∨ a = y := (subdivision_some_none G x y a).mp h
            have hce : c = x ∨ c = y := (subdivision_none_some G x y c).mp h'
            have hexy : s(a,c) = s(x,y) := by
              rcases hae with rfl | rfl <;> rcases hce with rfl | rfl
              · exact (hac rfl).elim
              · rfl
              · exact Sym2.eq_swap
              · exact (hac rfl).elim
            have hacG : G.Adj a c := G.mem_edgeSet.mp (hexy.symm ▸ hxy)
            obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht.of_cons rfl
            refine ⟨.cons hacG q, hq.cons ?_, ?_, ?_⟩
            · intro ha'
              apply ha
              have hh : some a ∈ p.support := by rw [hqs] at ha'; simpa using ha'
              simp [hh]
            · simp [hqs]
            · intro e
              have he1 : e.map Option.some ≠ s(some a,none) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have he2 : e.map Option.some ≠ s(none,some c) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have hn : s(none,some x) = s(some a,none) ∨
                  s(none,some x) = s(none,some c) := by
                rcases hae with rfl | hay
                · exact Or.inl Sym2.eq_swap
                · rcases hce with rfl | hcy
                  · exact Or.inr rfl
                  · exact (hac (hay.trans hcy.symm)).elim
              simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he1, he2, false_or,
                hexy, hqe]
              tauto

lemma tight_partition_endpoints {V : Type cycleUniverse75} {I : Type cycleUniverse76} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (P : I → Piece G) (S : Finset V)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v)) (hk : 2 * Fintype.card I ≤ S.card) :
    ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ∈ S ∧ (P i).finish ∈ S := by
  classical
  let endpoint : I × Bool → V := fun z => if z.2 then (P z.1).start else (P z.1).finish
  have he : ∀ v : S, ∃ z : I × Bool, endpoint z = v := by
    intro v
    obtain ⟨i,_, h | h⟩ := endpoint_of_odd G P hd hc v (ho v v.property)
    · exact ⟨(i,true),h⟩
    · exact ⟨(i,false),h⟩
  choose pick hpick using he
  have hinj : Function.Injective pick := by
    intro v w hvw
    apply Subtype.ext
    exact (hpick v).symm.trans ((congrArg endpoint hvw).trans (hpick w))
  have hsurj : Function.Surjective pick := by
    by_contra hn
    have hh := Fintype.card_lt_of_injective_not_surjective pick hinj hn
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] at hh
    omega
  have hendinj : Function.Injective endpoint := by
    intro z t heq
    obtain ⟨v,rfl⟩ := hsurj z
    obtain ⟨w,rfl⟩ := hsurj t
    have hvw : v = w := Subtype.ext (by simpa only [hpick] using heq)
    exact congrArg pick hvw
  have hmem : ∀ z, endpoint z ∈ S := by
    intro z
    obtain ⟨v,rfl⟩ := hsurj z
    rw [hpick]
    exact v.property
  intro i
  refine ⟨?_, hmem (i,true), hmem (i,false)⟩
  intro heq
  have hh := hendinj (show endpoint (i,true) = endpoint (i,false) from heq)
  have := congrArg Prod.snd hh
  contradiction

def subdivisionRepresentative {V : Type cycleUniverse77} (x y : V) (e : Sym2 V) : Sym2 (Option V) :=
  if e = s(x,y) then s(none,some x) else e.map Option.some

lemma representative_mem {V : Type cycleUniverse78} (G : SimpleGraph V) (x y : V) (_hxy : G.Adj x y)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    subdivisionRepresentative x y e ∈ (subdivision G x y).edgeSet := by
  classical
  by_cases h : e = s(x,y)
  · simp [subdivisionRepresentative, h]
  · rw [subdivisionRepresentative, if_neg h]
    induction e using Sym2.ind with
    | _ a b => exact ⟨he,h⟩

lemma suppress_piece {V : Type cycleUniverse79} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : Piece (subdivision G x y)) (hne : P.start ≠ P.finish)
    (ha : P.start ≠ none) (hb : P.finish ≠ none) :
    ∃ Q : Piece G, ∀ e, e ∈ Q.walk.edgeSet ↔ subdivisionRepresentative x y e ∈ P.walk.edgeSet := by
  classical
  rcases P with ⟨a,b,p,hp⟩
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b =>
      have hab : a ≠ b := fun h => hne (congrArg some h)
      have hpath : p.IsPath := by
        rcases hp with h | ⟨h,_⟩
        · exact h.1
        · exact (hne h.symm).elim
      obtain ⟨q,hq,_,hqe⟩ := suppress_path G x y hxy p hpath
      have hpos : 0 < q.length := by
        by_contra hn
        exact hab (Walk.eq_of_length_eq_zero (by omega : q.length = 0))
      refine ⟨.ofPath ⟨a,b,q,hq,hpos⟩, ?_⟩
      intro e
      change e ∈ q.edgeSet ↔ _
      rw [hqe]
      by_cases he : e = s(x,y)
      · subst e
        have hn : (s(x,y) : Sym2 V).map some ∉ p.edgeSet := by
          intro h
          have hh := p.edges_subset_edgeSet h
          exact hh.2 rfl
        simp only [subdivisionRepresentative, ite_true, hn, false_or, true_and]
      · simp [subdivisionRepresentative, he]

lemma suppress_partition {V : Type cycleUniverse80} {I : Type cycleUniverse81} [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : I → Piece (subdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (subdivision G x y).edgeSet)
    (hp : ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ≠ none ∧ (P i).finish ≠ none) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  classical
  choose Q hQ using fun i => suppress_piece G x y hxy (P i) (hp i).1 (hp i).2.1 (hp i).2.2
  refine ⟨Q, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun e hei hej =>
      Set.disjoint_left.mp (hd hij) ((hQ i e).mp hei) ((hQ j e).mp hej)
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => (Q i).walk.edges_subset_edgeSet
    · intro e he
      have hrep := representative_mem G x y hxy e he
      rw [← hc] at hrep
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hrep
      exact Set.mem_iUnion.mpr ⟨i,(hQ i e).mpr hi⟩

lemma even_activeOrder {V : Type cycleUniverse82} [Fintype V] (G : SimpleGraph V)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) : Even (activeOrder G) := by
  classical
  have he : G.support.toFinset = Finset.univ.filter (fun v => Odd (G.degree v)) := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      ← G.degree_pos_iff_mem_support]
    refine ⟨ho v, ?_⟩
    rintro ⟨k,hk⟩
    omega
  simpa only [activeOrder, he] using G.even_card_odd_degree_vertices

lemma half_restore {V : Type cycleUniverse83} {I : Type cycleUniverse84} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v))
    (P : I → Piece (halfSubdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (halfSubdivision G x y).edgeSet) :
    ∃ Q : I → Piece (subdivision G x y),
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = (subdivision G x y).edgeSet := by
  classical
  have he : {e : Sym2 (Option V) | ∃ v ∈ ({none} : Set (Option V)), e = s(some x,v)} =
      {s(none,some x)} := by
    ext e
    simp [Sym2.eq_swap]
  apply restore_partition (subdivision G x y) (halfSubdivision G x y)
    ((subdivision G x y).deleteEdges_le _) (some x) {none}
    (by intro v hv; rcases hv with rfl; exact Or.inl rfl) ?_ ?_ ?_ P hd hc
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    symm
    apply Set.sdiff_union_of_subset
    intro e he
    rcases he with rfl
    exact Or.inl rfl
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_right
  · intro v hv
    cases v with
    | none => rw [half_degree_none G x y hxy]; exact ⟨0,rfl⟩
    | some v =>
      have hxv : G.Adj x v := hv.1
      have hh := half_degree G x y v hxy
      rw [if_neg hxv.ne.symm, add_zero] at hh
      rw [hh]
      exact ho v ((G.degree_pos_iff_exists_adj v).mpr ⟨x,hxv.symm⟩)

theorem odd_vertex_step {V : Type cycleUniverse85} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph (Option V), H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) (x : V) (hx : 3 ≤ G.degree x) :
    HasPartition G := by
  classical
  obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hp : ∃ v, 0 < (halfSubdivision G x y).degree v ∧
      Even ((halfSubdivision G x y).degree v) := by
    refine ⟨some x, ?_, ?_⟩
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      omega
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      obtain ⟨k,hk⟩ := ho x (by omega)
      exact ⟨k,by omega⟩
  obtain ⟨k,P,hd,hc,hk⟩ := even_vertex_step (halfSubdivision G x y)
    (fun H hh => hIH H (by rwa [half_edge_count G x y hxy] at hh)) hp
  have hbound : 2 * k ≤ activeOrder G + 1 := by
    have hm := activeOrder_mono ((subdivision G x y).deleteEdges_le {s(none,some x)})
    rw [subdivision_activeOrder G x y hxy] at hm
    exact hk.trans hm
  have hk' : 2 * k ≤ activeOrder G := by
    obtain ⟨a,ha⟩ := even_activeOrder G ho
    omega
  obtain ⟨Q,hQ,hQC⟩ := half_restore G x y hxy ho P hd hc
  let S := G.support.toFinset.image Option.some
  have hScard : S.card = activeOrder G := by
    exact Finset.card_image_of_injective _ (Option.some_injective V)
  have hSodd : ∀ v ∈ S, Odd ((subdivision G x y).degree v) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [subdivision_degree G x y w hxy]
    exact ho w ((G.degree_pos_iff_mem_support w).mpr (Set.mem_toFinset.mp hw))
  have hends := tight_partition_endpoints (subdivision G x y) Q S hQ hQC hSodd
    (by simpa only [Fintype.card_fin, hScard] using hk')
  have hnon : ∀ i, (Q i).start ≠ (Q i).finish ∧
      (Q i).start ≠ none ∧ (Q i).finish ≠ none := by
    intro i
    refine ⟨(hends i).1, ?_, ?_⟩
    · intro h
      have hh := (hends i).2.1
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
    · intro h
      have hh := (hends i).2.2
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
  obtain ⟨R,hR,hRC⟩ := suppress_partition G x y hxy Q hQ hQC hnon
  exact ⟨k,R,hR,hRC,hk'⟩

theorem path_cycle_partition {V : Type u} [Fintype V] (G : SimpleGraph V) : HasPartition G := by
  classical
  suffices ∀ (n : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
      H.edgeFinset.card = n → HasPartition H by
    exact this G.edgeFinset.card V G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ H hcount
    by_cases he : ∃ v, 0 < H.degree v ∧ Even (H.degree v)
    · exact even_vertex_step H (fun K hk => ih K.edgeFinset.card (by omega) W K rfl) he
    · have ho : ∀ v, 0 < H.degree v → Odd (H.degree v) := by
        intro v hv
        exact Nat.not_even_iff_odd.mp (fun hev => he ⟨v,hv,hev⟩)
      by_cases hm : ∀ v, H.degree v ≤ 1
      · exact matching_partition H hm
      · push Not at hm
        obtain ⟨x,hx⟩ := hm
        have hx3 : 3 ≤ H.degree x := by
          obtain ⟨k,hk⟩ := ho x (by omega)
          omega
        exact odd_vertex_step H
          (fun K hk => ih K.edgeFinset.card (by omega) (Option W) K rfl) ho x hx3

end
end ErdosGallai.Lovasz

end
end
end

end OAI


-- Upstream module PathDeletion

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure PositiveSimplePath {V : Type cycleUniverse1} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PositiveSimplePath.endpoints_ne {V : Type cycleUniverse2} {G : SimpleGraph V}
    (P : PositiveSimplePath G) : P.start ≠ P.finish := by
  intro he
  have hz := P.isPath.nil_iff_eq.mpr he
  have := hz.length_eq_zero
  have := P.positive
  omega

theorem endpoint_path_count {V : Type cycleUniverse3} {I : Type cycleUniverse4} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hload : ∀ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hsum : (∑ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card) =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heq : ∀ i : I,
        (∑ v : V, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : (Finset.univ.filter fun v =>
          (P i).start = v ∨ (P i).finish = v) = {(P i).start, (P i).finish} := by
        ext v; simp [eq_comm]
      have hc : ({(P i).start, (P i).finish} : Finset V).card = 2 := by
        simp [(P i).endpoints_ne]
      rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hload v)
  rw [hsum] at hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  omega

def EndpointPathPartition {V : Type cycleUniverse5} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → PositiveSimplePath G),
    Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧
    (∀ v : V, (Finset.univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) ∧
    k ≤ Fintype.card V

def MissingEndpointTheorem : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), EndpointPathPartition G

def PathOrCycleEdgeSet {V : Type cycleUniverse6} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ s = p.edgeSet) ∨
  (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ s = p.edgeSet)

def LovaszPathCyclePartition {V : Type cycleUniverse7} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
    (∀ i, PathOrCycleEdgeSet G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V

def MissingLovaszTheorem : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), LovaszPathCyclePartition G

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
open scoped BigOperators

def evenAugmentation {V : Type cycleUniverse8} [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some u, some v => G.Adj u v
    | none, some v => Even (G.degree v)
    | some u, none => Even (G.degree u)
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact G.irrefl h⟩

@[simp] theorem evenAugmentation_some_adj {V : Type cycleUniverse9} [Fintype V]
    (G : SimpleGraph V) (u v : V) :
    (evenAugmentation G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem evenAugmentation_none_adj {V : Type cycleUniverse10} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj none (some v) ↔ Even (G.degree v) := Iff.rfl

@[simp] theorem evenAugmentation_some_none {V : Type cycleUniverse11} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).Adj (some v) none ↔ Even (G.degree v) := Iff.rfl

theorem evenAugmentation_degree {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).degree (some v) =
      G.degree v + if Even (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp only [evenAugmentation_some_adj, evenAugmentation_some_none]
  have he : (∑ u : V, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  omega

theorem evenAugmentation_old_odd {V : Type cycleUniverse13} [Fintype V]
    (G : SimpleGraph V) (v : V) : Odd ((evenAugmentation G).degree (some v)) := by
  rw [evenAugmentation_degree]
  by_cases h : Even (G.degree v)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · simpa [h] using Nat.not_even_iff_odd.mp h

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem trail_partition_degree_sum {V : Type cycleUniverse14} {I : Type cycleUniverse15} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse16} {I : Type cycleUniverse17} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

private theorem odd_load_one {V : Type cycleUniverse18} [DecidableEq V]
    (S : Finset V) (f : V → ℕ) (ho : ∀ v ∈ S, Odd (f v))
    (hs : ∑ v ∈ S, f v ≤ S.card + 1) : ∀ v ∈ S, f v = 1 := by
  intro v hv
  by_contra hn
  have hv3 : 3 ≤ f v := by rcases ho v hv with ⟨k, hk⟩; omega
  have hlow : ∑ x ∈ S, (1 + if x = v then 2 else 0) ≤ ∑ x ∈ S, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = v
    · subst x; simpa using hv3
    · simp only [he, ↓reduceIte, add_zero]
      rcases ho x hx with ⟨k, hk⟩
      omega
  have heq : (∑ x ∈ S, (1 + if x = v then 2 else 0)) = S.card + 2 := by
    simp [Finset.sum_add_distrib, hv]
  omega

theorem tight_odd_trail_partition {V : Type cycleUniverse19} {I : Type cycleUniverse20} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) {a b : I → V}
    (p : ∀ i, G.Walk (a i) (b i)) (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v))
    (hsize : 2 * Fintype.card I ≤ S.card + 1) :
    (∀ i, a i ≠ b i) ∧ (∀ v ∈ S,
      (Finset.univ.filter (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card = 1) := by
  classical
  let load := fun v : V => (Finset.univ.filter
    (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card
  let openParts := Finset.univ.filter (fun i => a i ≠ b i)
  have hlodd : ∀ v ∈ S, Odd (load v) := by
    intro v hv
    rw [← Nat.not_even_iff_odd, ← trail_partition_even_degree_iff G p ht hd hc v]
    exact (Nat.not_even_iff_odd.mpr (ho v hv))
  have htotal : (∑ v : V, load v) = 2 * openParts.card := by
    dsimp [load]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he : ∀ i : I, (∑ v : V, if a i ≠ b i ∧ (v = a i ∨ v = b i) then 1 else 0) =
        if a i ≠ b i then 2 else 0 := by
      intro i
      by_cases h : a i = b i
      · simp [h]
      · have hf : (Finset.univ.filter (fun v => a i ≠ b i ∧ (v = a i ∨ v = b i))) =
            {a i, b i} := by ext v; simp [h]
        have hcard : ({a i, b i} : Finset V).card = 2 := by simp [h]
        rw [if_pos h, ← hcard, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change openParts.card * 2 = 2 * openParts.card
    omega
  have hsub : (∑ v ∈ S, load v) ≤ ∑ v : V, load v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hlow : S.card ≤ ∑ v ∈ S, load v := by
    simpa using Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := load)
      (fun v hv => by rcases hlodd v hv with ⟨k, hk⟩; omega)
  have hcount : openParts.card ≤ Fintype.card I := Finset.card_le_univ _
  have hpoint := odd_load_one S load hlodd (by omega)
  refine ⟨?_, hpoint⟩
  intro i hi
  have hproper : openParts ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hh : i ∈ openParts := heq.symm ▸ Finset.mem_univ i
    simp [openParts, hi] at hh
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

private theorem path_tail_delete_start {V : Type cycleUniverse21} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.tail.edgeSet = {e | e ∈ p.edgeSet ∧ a ∉ e} := by
  cases p with
  | nil => ext e; simp
  | @cons a c b h q =>
    have ha : a ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have hnot : ∀ e ∈ q.edgeSet, a ∉ e := by
      intro e he hae
      exact ha (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e, he, hae⟩))
    ext e
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.mem_edgeSet,
      SimpleGraph.Walk.edges_tail, SimpleGraph.Walk.edges_cons, List.tail_cons, List.mem_cons]
    constructor
    · intro he
      exact ⟨Or.inr he, hnot e he⟩
    · rintro ⟨he | he, hn⟩
      · subst e; exact (hn (by simp)).elim
      · exact he

private theorem path_dropLast_delete_end {V : Type cycleUniverse22} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.dropLast.edgeSet = {e | e ∈ p.edgeSet ∧ b ∉ e} := by
  have he : p.dropLast.edgeSet = p.reverse.tail.edgeSet := by
    calc
      _ = p.dropLast.reverse.edgeSet := (SimpleGraph.Walk.edgeSet_reverse _).symm
      _ = _ := by rw [SimpleGraph.Walk.reverse_dropLast, SimpleGraph.Walk.edgeSet_copy]
  rw [he, path_tail_delete_start p.reverse hp.reverse, SimpleGraph.Walk.edgeSet_reverse]

private theorem positive_avoids_of_no_incidence {V : Type cycleUniverse23} {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hpos : 0 < p.length)
    (he : ∀ e ∈ p.edgeSet, v ∉ e) : v ∉ p.support := by
  have hn : ¬p.Nil := by intro hz; have := hz.length_eq_zero; omega
  intro hv
  obtain ⟨e, he', hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  exact he e he' hve

theorem delete_vertex_from_path {V : Type cycleUniverse24} [DecidableEq V] {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) :
    let q := (p.takeUntil v hv).dropLast
    let r := (p.dropUntil v hv).tail
    q.IsPath ∧ r.IsPath ∧ Disjoint q.edgeSet r.edgeSet ∧
    q.edgeSet ∪ r.edgeSet = {e | e ∈ p.edgeSet ∧ v ∉ e} ∧
    (0 < q.length → v ∉ q.support) ∧
    (0 < r.length → v ∉ r.support) ∧
    (0 < q.length → G.Adj (p.takeUntil v hv).penultimate v) ∧
    (0 < r.length → G.Adj v (p.dropUntil v hv).snd) := by
  dsimp only
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have ht : t.IsPath := hp.takeUntil hv
  have hd : d.IsPath := hp.dropUntil hv
  have heq : t.append d = p := p.take_spec hv
  have hqe : t.dropLast.edgeSet = {e | e ∈ t.edgeSet ∧ v ∉ e} :=
    path_dropLast_delete_end t ht
  have hre : d.tail.edgeSet = {e | e ∈ d.edgeSet ∧ v ∉ e} :=
    path_tail_delete_start d hd
  have hdis : Disjoint t.edgeSet d.edgeSet := by
    have hn := hp.isTrail.edges_nodup
    rw [← heq, SimpleGraph.Walk.edges_append] at hn
    have hn' := (List.nodup_append.mp hn).2.2
    apply Set.disjoint_left.mpr
    intro e het hed
    exact hn' e het e hed rfl
  refine ⟨ht.dropLast, hd.tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqe, hre]
    exact hdis.mono (fun _ h => h.1) (fun _ h => h.1)
  · have he : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    rw [hqe, hre]
    ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rw [← he]
    simp only [Set.mem_union]
    tauto
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hqe ▸ he).2
  · intro hpos
    apply positive_avoids_of_no_incidence _ hpos
    intro e he
    exact (hre ▸ he).2
  · intro hpos
    apply t.adj_penultimate
    intro hn
    have hz := hn.length_eq_zero
    change 0 < t.dropLast.length at hpos
    rw [SimpleGraph.Walk.length_dropLast, hz] at hpos
    omega
  · intro hpos
    apply d.adj_snd
    intro hn
    have hz := hn.length_eq_zero
    change 0 < d.tail.length at hpos
    rw [SimpleGraph.Walk.length_tail, hz] at hpos
    omega

theorem delete_vertex_boundary_edges {V : Type cycleUniverse25} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) :
    (0 < (p.takeUntil v hv).dropLast.length →
      s((p.takeUntil v hv).penultimate, v) ∈ p.edgeSet) ∧
    (0 < (p.dropUntil v hv).tail.length →
      s(v, (p.dropUntil v hv).snd) ∈ p.edgeSet) := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  constructor
  · intro hpos
    have hn : ¬ t.Nil := by
      intro hz
      change 0 < t.dropLast.length at hpos
      rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hpos
      omega
    have hm := t.mk_penultimate_end_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inl hm
  · intro hpos
    have hn : ¬ d.Nil := by
      intro hz
      change 0 < d.tail.length at hpos
      rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hpos
      omega
    have hm := d.mk_start_snd_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inr hm

theorem delete_vertex_new_ends_ne {V : Type cycleUniverse26} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support)
    (hl : 0 < (p.takeUntil v hv).dropLast.length)
    (hr : 0 < (p.dropUntil v hv).tail.length) :
    (p.takeUntil v hv).penultimate ≠ (p.dropUntil v hv).snd := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  have htn : ¬t.Nil := by
    intro hz
    change 0 < t.dropLast.length at hl
    rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hl
    omega
  have hdn : ¬d.Nil := by
    intro hz
    change 0 < d.tail.length at hr
    rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hr
    omega
  have hdj := hp.isTrail.edges_nodup
  rw [← heq, SimpleGraph.Walk.edges_append] at hdj
  have hdis := (List.nodup_append.mp hdj).2.2
  intro hsame
  have ha := t.mk_penultimate_end_mem_edges htn
  have hb := d.mk_start_snd_mem_edges hdn
  apply hdis _ ha _ hb

  rw [show t.penultimate = d.snd from hsame, Sym2.eq_swap]

theorem delete_vertex_new_endpoint_load {V : Type cycleUniverse27} {I : Type cycleUniverse28} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {a b : I → V} {v : V}
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsPath)
    (hv : ∀ i, v ∈ (p i).support)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (x : V) :
    let live := fun z : I × Bool => if z.2 then
      0 < ((p z.1).takeUntil v (hv z.1)).dropLast.length else
      0 < ((p z.1).dropUntil v (hv z.1)).tail.length
    let newEnd := fun z : I × Bool => if z.2 then
      ((p z.1).takeUntil v (hv z.1)).penultimate else
      ((p z.1).dropUntil v (hv z.1)).snd
    (Finset.univ.filter fun z => live z ∧ newEnd z = x).card ≤ 1 := by
  classical
  dsimp only
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨i, bi⟩ := z
  obtain ⟨j, bj⟩ := w
  have hi := (Finset.mem_filter.mp hz).2
  have hj := (Finset.mem_filter.mp hw).2
  have hei : s(v,x) ∈ (p i).edgeSet := by
    cases bi
    · have hx : ((p i).dropUntil v (hv i)).snd = x := hi.2
      simpa only [hx] using (delete_vertex_boundary_edges (p i) (hv i)).2 hi.1
    · have hx : ((p i).takeUntil v (hv i)).penultimate = x := hi.2
      have he := (delete_vertex_boundary_edges (p i) (hv i)).1 hi.1
      simpa only [hx, Sym2.eq_swap] using he
  have hej : s(v,x) ∈ (p j).edgeSet := by
    cases bj
    · have hx : ((p j).dropUntil v (hv j)).snd = x := hj.2
      simpa only [hx] using (delete_vertex_boundary_edges (p j) (hv j)).2 hj.1
    · have hx : ((p j).takeUntil v (hv j)).penultimate = x := hj.2
      have he := (delete_vertex_boundary_edges (p j) (hv j)).1 hj.1
      simpa only [hx, Sym2.eq_swap] using he
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) hei hej
  subst j
  congr 1
  cases bi <;> cases bj
  · rfl
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hj.1 hi.1
    exact (he (hj.2.trans hi.2.symm)).elim
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hi.1 hj.1
    exact (he (hi.2.trans hj.2.symm)).elim
  · rfl

structure SimplePathPiece {V : Type cycleUniverse29} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace SimplePathPiece
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

def Avoiding (p : I → SimplePathPiece G) (v : V) := {i : I // v ∉ (p i).walk.support}
def Meeting (p : I → SimplePathPiece G) (v : V) := {i : I // v ∈ (p i).walk.support}
def DeleteIndex (p : I → SimplePathPiece G) (v : V) :=
  Avoiding p v ⊕ (Meeting p v × Bool)

instance (p : I → SimplePathPiece G) (v : V) : Fintype (Avoiding p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∉ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (Meeting p v) := by
  classical
  exact inferInstanceAs (Fintype {i : I // v ∈ (p i).walk.support})
instance (p : I → SimplePathPiece G) (v : V) : Fintype (DeleteIndex p v) :=
  inferInstanceAs (Fintype (Avoiding p v ⊕ (Meeting p v × Bool)))

def deleted (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → SimplePathPiece G
  | .inl i => p i.val
  | .inr (i,true) => ⟨_,_,((p i.val).walk.takeUntil v i.property).dropLast,
      ((p i.val).isPath.takeUntil i.property).dropLast⟩
  | .inr (i,false) => ⟨_,_,((p i.val).walk.dropUntil v i.property).tail,
      ((p i.val).isPath.dropUntil i.property).tail⟩

def parent (p : I → SimplePathPiece G) (v : V) : DeleteIndex p v → I
  | .inl i => i.val
  | .inr (i,_) => i.val

def oldEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl i => (p i.val).start = x ∨ (p i.val).finish = x
  | .inr (i,true) => (p i.val).start = x
  | .inr (i,false) => (p i.val).finish = x

def newEnd (p : I → SimplePathPiece G) (v x : V) : DeleteIndex p v → Prop
  | .inl _ => False
  | .inr (i,true) => ((p i.val).walk.takeUntil v i.property).penultimate = x
  | .inr (i,false) => ((p i.val).walk.dropUntil v i.property).snd = x

lemma deleted_ends {V : Type cycleUniverse32} {I : Type cycleUniverse33} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v x : V) (j : DeleteIndex p v) :
    (deleted p v j).start = x ∨ (deleted p v j).finish = x ↔
      oldEnd p v x j ∨ newEnd p v x j := by
  rcases j with i | ⟨i,b⟩
  · simp [deleted, oldEnd, newEnd]
  · cases b <;> simp [deleted, oldEnd, newEnd, or_comm]

lemma deleted_edges_subset {V : Type cycleUniverse34} {I : Type cycleUniverse35} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v) :
    (deleted p v j).walk.edgeSet ⊆ (p (parent p v j)).walk.edgeSet := by
  rcases j with i | ⟨i,b⟩
  · exact Set.Subset.rfl
  · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
    cases b
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inr he).1
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inl he).1

lemma deleted_positive_avoids {V : Type cycleUniverse36} {I : Type cycleUniverse37} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v)
    (hpos : 0 < (deleted p v j).walk.length) : v ∉ (deleted p v j).walk.support := by
  rcases j with i | ⟨i,b⟩
  · exact i.property
  · have h := delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property
    cases b
    · exact h.2.2.2.2.2.1 hpos
    · exact h.2.2.2.2.1 hpos

lemma deleted_disjoint (p : I → SimplePathPiece G) (v : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    Pairwise fun j k => Disjoint (deleted p v j).walk.edgeSet (deleted p v k).walk.edgeSet := by
  intro j k hjk
  by_cases he : parent p v j = parent p v k
  · rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
    · exact (hjk (congrArg Sum.inl (Subtype.ext he))).elim
    · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
    · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
    · have hil : i = l := Subtype.ext he
      subst l
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1
      · exact (hjk rfl).elim
  · exact (hd he).mono (deleted_edges_subset p v j) (deleted_edges_subset p v k)

lemma deleted_old_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => oldEnd p v x j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjp : (p (parent p v j)).start = x ∨ (p (parent p v j)).finish = x := by
    have h := (Finset.mem_filter.mp hj).2
    rcases j with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have hkp : (p (parent p v k)).start = x ∨ (p (parent p v k)).finish = x := by
    have h := (Finset.mem_filter.mp hk).2
    rcases k with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have he := Finset.card_le_one.mp hload (parent p v j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjp⟩) (parent p v k)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
  · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
  · have hil : i = l := Subtype.ext he
    subst l
    cases b <;> cases c
    · rfl
    · exact (hne _ (hk'.trans hj'.symm)).elim
    · exact (hne _ (hj'.trans hk'.symm)).elim
    · rfl

lemma deleted_new_load (p : I → SimplePathPiece G) (v x : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧ newEnd p v x j).card ≤ 1 := by
  classical
  have h := delete_vertex_new_endpoint_load
    (fun i : Meeting p v => (p i.val).walk) (fun i => (p i.val).isPath)
    (fun i => i.property)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) x
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩
  · exact False.elim hj'.2
  rcases k with l | ⟨l,c⟩
  · exact False.elim hk'.2
  apply congrArg Sum.inr
  apply Finset.card_le_one.mp h
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases b <;> exact hj'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases c <;> exact hk'

theorem deleted_endpoint_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun j : DeleteIndex p v => oldEnd p v x j)
  let B := Finset.univ.filter (fun j : DeleteIndex p v =>
    0 < (deleted p v j).walk.length ∧ newEnd p v x j)
  have hsub : (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)) ⊆ A ∪ B := by
    intro j hj
    obtain ⟨hpos,hend⟩ := (Finset.mem_filter.mp hj).2
    rcases (deleted_ends p v x j).mp hend with ho | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hn⟩)
  have ha := deleted_old_load p v x hne hload
  have hb := deleted_new_load p v x hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A,B] at hc
  omega

theorem deleted_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : DeleteIndex p v, (deleted p v j).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨⟨parent p v j, deleted_edges_subset p v j hj⟩,?_⟩
    rcases j with i | ⟨i,b⟩
    · intro hv
      exact i.property (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e,hj,hv⟩))
    · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
      cases b
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inr hj).2
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inl hj).2
  · rintro ⟨⟨i,hi⟩,hv⟩
    by_cases hs : v ∈ (p i).walk.support
    · have h := (delete_vertex_from_path (p i).walk (p i).isPath hs).2.2.2.1
      have he : e ∈ ((p i).walk.takeUntil v hs).dropLast.edgeSet ∪
          ((p i).walk.dropUntil v hs).tail.edgeSet := h.symm ▸ ⟨hi,hv⟩
      rcases he with hl | hr
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩

theorem deleted_positive_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length},
      (deleted p v j.val).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  rw [← deleted_union p v]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hp : 0 < (deleted p v j).walk.length := by
      by_contra hn
      have hz : (deleted p v j).walk.length = 0 := by omega
      have hn' := SimpleGraph.Walk.length_eq_zero_iff.mp hz
      have he' := SimpleGraph.Walk.edges_eq_nil.mpr hn'
      have hmem : e ∈ (deleted p v j).walk.edges := hj
      exact List.not_mem_nil (he' ▸ hmem)
    exact Set.mem_iUnion.mpr ⟨⟨j,hp⟩,hj⟩

def deletedInduced (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    SimplePathPiece (G.induce {x | x ≠ v}) := by
  let q := deleted p v j.val
  have havo : ∀ x ∈ q.walk.support, x ∈ ({x | x ≠ v} : Set V) := by
    intro x hx he
    subst x
    exact deleted_positive_avoids p v j.val j.property hx
  exact ⟨_,_, q.walk.induce _ havo, by
    apply SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa using q.isPath⟩

end SimplePathPiece

end
end ErdosGallai
end
end
end

end OAI


-- Upstream module EndpointPartition

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
open scoped BigOperators

theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

def PositiveSimplePath.mapIso {V : Type cycleUniverse3} {W : Type cycleUniverse4} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (P : PositiveSimplePath G) : PositiveSimplePath H :=
  ⟨f P.start,f P.finish,P.walk.map f.toHom,P.isPath.map f.injective,by simpa using P.positive⟩

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_map {V : Type cycleUniverse9} {I : Type cycleUniverse10} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] [_contextInstance4 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    (deletedInduced p v j).walk.map (SimpleGraph.Embedding.induce _).toHom =
      (deleted p v j.val).walk := by
  exact SimpleGraph.Walk.map_induce _ _

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

def deletedPositive (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    PositiveSimplePath (G.induce {x | x ≠ v}) :=
  { deletedInduced p v j with
    positive := by
      have h := congrArg SimpleGraph.Walk.length (deletedInduced_map p v j)
      rw [SimpleGraph.Walk.length_map] at h
      rw [h]
      exact j.property }

theorem endpoint_partition_after_deletion (p : I → SimplePathPiece G) (v : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hc : (⋃ i, (p i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, x ≠ v → (Finset.univ.filter fun i =>
      (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    EndpointPathPartition (G.induce {x | x ≠ v}) := by
  classical
  let A := {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}
  let f : G.induce {x | x ≠ v} →g G := (SimpleGraph.Embedding.induce _).toHom
  have hf : Function.Injective f := Subtype.val_injective
  apply endpoint_partition_of_family (fun j : A => deletedPositive p v j)
  · intro j k hjk
    have hdis := deleted_disjoint p v hd (fun he => hjk (Subtype.ext he))
    apply Set.disjoint_left.mpr
    intro e hej hek
    have he1 : Sym2.map f e ∈ (deleted p v j.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v j]
      exact ⟨e,hej,rfl⟩
    have he2 : Sym2.map f e ∈ (deleted p v k.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v k]
      exact ⟨e,hek,rfl⟩
    exact Set.disjoint_left.mp hdis he1 he2
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact (deletedPositive p v j).walk.edges_subset_edgeSet hj
    · intro e he
      have he' : Sym2.map f e ∈ G.edgeSet ∧ v ∉ Sym2.map f e := by
        induction e using Sym2.inductionOn with | _ a b =>
          refine ⟨he,?_⟩
          change v ∉ s(a.val,b.val)
          simpa only [Sym2.map_mk,Sym2.mem_iff,eq_comm] using not_or.mpr ⟨a.property,b.property⟩
      have hmem : Sym2.map f e ∈ ⋃ j : A, (deleted p v j.val).walk.edgeSet := by
        rw [deleted_positive_union]
        refine ⟨?_,he'.2⟩
        exact Set.mem_iUnion.mp (hc.symm ▸ he'.1)
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hmem
      rw [← deletedInduced_edges p v j] at hj
      obtain ⟨e',he',heq⟩ := hj
      have heq' : e' = e := Sym2.map.injective hf heq
      subst e'
      exact Set.mem_iUnion.mpr ⟨j,he'⟩
  · intro x
    have hb := deleted_endpoint_load p v x.val hne hd (hl x.val x.property)
    have hc' : (Finset.univ.filter fun j : A =>
        (deletedPositive p v j).start = x ∨ (deletedPositive p v j).finish = x).card ≤
        (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
          ((deleted p v j).start = x.val ∨ (deleted p v j).finish = x.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,j.property,?_⟩
        rcases (Finset.mem_filter.mp hj).2 with hs | ht
        · exact Or.inl (congrArg Subtype.val hs)
        · exact Or.inr (congrArg Subtype.val ht)
      · exact fun _ _ _ _ he => Subtype.ext he
    convert hc'.trans hb using 1

    all_goals first
      | rfl
      | exact congrArg Finset.card (Finset.ext fun i => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and])

end SimplePathPiece

def evenAugmentationOldIso {V : Type cycleUniverse11} [Fintype V] (G : SimpleGraph V) :
    G ≃g (evenAugmentation G).induce {x | x ≠ none} where
  toEquiv := Equiv.optionSubtype none ⟨Equiv.refl (Option V),rfl⟩
  map_rel_iff' := Iff.rfl

theorem endpoint_partition_of_augmented_parts {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (hL : LovaszPathCyclePartition (evenAugmentation G)) :
    EndpointPathPartition G := by
  classical
  obtain ⟨k,parts,hparts,hd,hc,hk⟩ := hL
  have hw : ∀ i : Fin k, ∃ (a b : Option V) (p : (evenAugmentation G).Walk a b),
      p.IsTrail ∧ (a ≠ b → p.IsPath) ∧ parts i = p.edgeSet := by
    intro i
    rcases hparts i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
    · exact ⟨a,b,p,hp.isTrail,fun _ => hp,he⟩
    · exact ⟨a,a,p,hp.isTrail,fun h => False.elim (h rfl),he⟩
  choose a b p ht hp he using hw
  have hd' : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet := by
    simpa only [he] using hd
  have hc' : (⋃ i, (p i).edgeSet) = (evenAugmentation G).edgeSet := by
    simpa only [he] using hc
  let S : Finset (Option V) := Finset.univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,Finset.card_image_of_injective _ (Option.some_injective V),Finset.card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact evenAugmentation_old_odd G y
  have hk' : 2 * Fintype.card (Fin k) ≤ S.card + 1 := by
    simpa only [Fintype.card_fin,Fintype.card_option,hS] using hk
  obtain ⟨hopen,hload⟩ := tight_odd_trail_partition (evenAugmentation G) S p ht hd' hc' ho hk'
  let P : Fin k → SimplePathPiece (evenAugmentation G) := fun i =>
    ⟨a i,b i,p i,hp i (hopen i)⟩
  have hload' : ∀ x : Option V, x ≠ none → (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 1 := by
    intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x =>
      have h := hload (some x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      have hpred : (Finset.univ.filter fun i => a i ≠ b i ∧
          (some x = a i ∨ some x = b i)) =
          (Finset.univ.filter fun i => (P i).start = some x ∨ (P i).finish = some x) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,P]
        constructor
        · rintro ⟨_,hi⟩
          exact hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · intro hi
          exact ⟨hopen i,hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
      apply le_of_eq
      calc
        _ = _ := congrArg Finset.card hpred.symm
        _ = 1 := by
          convert h using 1
          congr 1
          ext i
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]

  have hdel := SimplePathPiece.endpoint_partition_after_deletion P none hopen hd' hc' hload'
  exact endpoint_partition_mapIso (evenAugmentationOldIso G).symm hdel

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G := by
  classical
  obtain ⟨k,P,hd,hc,hk⟩ := Lovasz.path_cycle_partition G
  refine ⟨k,fun i => (P i).walk.edgeSet,?_,hd,hc,?_⟩
  · intro i
    rcases (P i).simple with hp | ⟨h,hcy⟩
    · exact Or.inl ⟨(P i).start,(P i).finish,(P i).walk,hp.1,hp.2,rfl⟩
    · exact Or.inr ⟨(P i).start,(P i).walk.copy rfl h,hcy,by simp⟩
  · exact hk.trans (Finset.card_le_univ _)

theorem lovasz_theorem : MissingLovaszTheorem :=
  fun _ G => lovasz_path_cycle_partition G

theorem endpoint_path_partition {V : Type cycleUniverse14} [Fintype V] (G : SimpleGraph V) :
    EndpointPathPartition G :=
  endpoint_partition_of_augmented_parts G (lovasz_path_cycle_partition (evenAugmentation G))

theorem endpoint_theorem : MissingEndpointTheorem :=
  fun _ G => endpoint_path_partition G

end
end ErdosGallai

end
end
end

end OAI


-- Upstream module Decomposition

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

def CycleOrSingleEdge {V : Type} (G : SimpleGraph V)
    (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

def EdgeDecomposition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

noncomputable section
open SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

lemma edgeDecomposition_of_indexed {V I : Type} [Fintype I] (G : SimpleGraph V)
    (parts : I → Set (Sym2 V)) (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hu : (⋃ i, parts i) = G.edgeSet) : EdgeDecomposition G (Fintype.card I) := by
  let e := Fintype.equivFin I
  refine ⟨fun j => parts (e.symm j), fun j => hp _, ?_, ?_⟩
  · intro i j hij
    exact hd (fun he => hij (e.symm.injective he))
  · ext x
    simp only [Set.mem_iUnion]
    rw [← hu]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i, by simpa using hi⟩

theorem edgeDecomposition_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  apply edgeDecomposition_of_indexed G (fun e : G.edgeSet => {e.1})
  · intro e; exact Or.inr ⟨e.1,e.2,rfl⟩
  · intro e d hed
    exact Set.disjoint_singleton.mpr (fun h => hed (Subtype.ext h))
  · ext e; simp

theorem edgeDecomposition_assemble {V I : Type} [Fintype I] (G : SimpleGraph V)
    (W : I → Type) (H : ∀ i, SimpleGraph (W i))
    (f : ∀ i, H i →g G) (hf : ∀ i, Function.Injective (f i))
    (hdisj : Pairwise (fun i j =>
      Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
    (hcover : (⋃ i, Sym2.map (f i) '' (H i).edgeSet) = G.edgeSet)
    (k : I → ℕ) (hparts : ∀ i, EdgeDecomposition (H i) (k i)) :
    EdgeDecomposition G (∑ i, k i) := by
  classical
  choose parts hp hd hu using hparts
  let J := Σ i, Fin (k i)
  let P : J → Set (Sym2 V) := fun j => Sym2.map (f j.1) '' parts j.1 j.2
  have hpart : ∀ j, CycleOrSingleEdge G (P j) := by
    intro j; exact cycleOrSingleEdge_map (f j.1) (hf j.1) (hp j.1 j.2)
  have hsub : ∀ i a, parts i a ⊆ (H i).edgeSet := by
    intro i a; exact cycleOrSingleEdge_subset (hp i a)
  have hdisjP : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases h : i = j
    · subst j
      have hab : a ≠ b := fun he => hij (by cases he; rfl)
      apply Set.disjoint_left.mpr
      rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
      have hxy : x = y := Sym2.map.injective (hf i) (he.trans he'.symm)
      subst y
      exact Set.disjoint_left.mp (hd i hab) hx hy
    · exact (hdisj h).mono (Set.image_mono (hsub i a)) (Set.image_mono (hsub j b))
  have hcoverP : (⋃ j, P j) = G.edgeSet := by
    rw [← hcover]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,a⟩,x,hx,he⟩
      exact ⟨i,x,hsub i a hx,he⟩
    · rintro ⟨i,x,hx,he⟩
      rw [← hu i] at hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i,a⟩,x,ha,he⟩
  have hc : Fintype.card J = ∑ i, k i := by simp [J, Fintype.card_sigma]
  rw [← hc]
  exact edgeDecomposition_of_indexed G P hpart hdisjP hcoverP

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem small_residue (c : ℝ) (hc : 0 < c) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj], P ≤ G →
      D^(9/10:ℝ) ≤ (Fintype.card V:ℝ) →
      (Fintype.card V:ℝ) ≤ D^(51/50:ℝ) →
      Splitting.CutExpansion P (c*D^(9/10:ℝ)) →
      ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V))
        (W : Fin 3 → Finset V) (H : Fin 3 → SimpleGraph V),
        (∀ i, CycleOrSingleEdge G (parts i)) ∧
        Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
        (∀ b, H b ≤ G ∧ (H b).support ⊆ (W b : Set V)) ∧
        (∀ b, (W b).card < Fintype.card V) ∧
        ((∑ b, (W b).card : ℕ):ℝ) ≤ 6 * thinning D * Fintype.card V ∧
        Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
        (∀ b i, Disjoint (H b).edgeSet (parts i)) ∧
        ((⋃ i, parts i) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
        k ≤ 9 * Fintype.card V := by
  classical
  have ha : 0 < reservoirExpansionCoefficient c := by
    unfold reservoirExpansionCoefficient
    exact div_pos (lt_min hc (by norm_num)) (by norm_num)
  obtain ⟨D₁,hprep⟩ := reservoir_preparation c hc
  obtain ⟨D₂,hD₂,hclose⟩ := uniform_three_reservoir_completion
    (reservoirExpansionCoefficient c) ha
  refine ⟨max D₁ D₂, hD₂.trans_le (le_max_right _ _), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  obtain ⟨ω,W,r,hPG',hPP,hPexp,hWW,hW2,hWsize,hWlt,hWsum,hWexp,hr,hrne,hcap⟩ :=
    hprep D ((le_max_left _ _).trans hD) V G P hPG hlo hhi hexp
  let P' := fun b => Splitting.colorGraph P ω b
  have hWW' : Pairwise fun b d => Disjoint (W b : Set V) (W d : Set V) := by
    intro b d hbd
    exact Finset.disjoint_coe.mpr (hWW b d hbd)
  let R := fun b => reservoirInternal (P' b) (W b)
  let T := fun b => R b ∪ (reservoirSpokes (W b) (r b) : Set (Sym2 V))
  let E : Set (Sym2 V) := ⋃ b, T b
  have hres := reservoir_reservations G P' W r hPG' hPP
    (fun b v hv t => (hr b v hv t).2)
  have hE : E ⊆ G.edgeSet := Set.iUnion_subset fun b =>
    Set.union_subset (hres.1 b).1 (hres.1 b).2
  let K := fun b => complementaryReservoirGraph (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW' b
  have hK := complementary_reservoir_graphs (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW'
  have hKG : ∀ b, K b ≤ G := fun b => (hK.1 b).trans (G.deleteEdges_le E)
  have hledger := complementary_reservation_ledger G (fun b => (W b : Set V)) hWW' E hE
  have hKT : ∀ b d, Disjoint (K b).edgeSet (T d) := fun b d =>
    (hledger.2.1 b).mono_right (Set.subset_iUnion T d)
  have hx : ∀ b : Fin 3, EndpointPathPartition (K b) := fun b => endpoint_path_partition (K b)
  choose k Q hQQ hQc hQl hQn using hx
  let x := fun b i => (Q b i).start
  let y := fun b i => (Q b i).finish
  let q : ∀ b i, G.Walk (x b i) (y b i) := fun b i => (Q b i).walk.mapLe (hKG b)
  have hqp : ∀ b i, (q b i).IsPath := fun b i => (Q b i).isPath.mapLe _
  have hql : ∀ b i, 0 < (q b i).length := by
    intro b i
    simpa [q] using (Q b i).positive
  have hqo : ∀ b i v, v ∈ (q b i).support → v ∉ W b := by
    intro b i v hv
    apply complementary_walk_outside (fun b => (W b : Set V)) hWW' b
      (Q b i).walk (Q b i).positive v
    simpa [q] using hv
  have hqd : ∀ b, Pairwise fun i j => Disjoint (q b i).edgeSet (q b j).edgeSet := by
    intro b i j hij
    simpa [q] using hQQ b hij
  have hqc : ∀ b, (⋃ i, (q b i).edgeSet) = (K b).edgeSet := by
    intro b
    simpa [q] using hQc b
  obtain ⟨C,hCy,hCC,hCsub,hcover,hcount⟩ := hclose D ((le_max_right _ _).trans hD)
    V G P' K hPG' hPP W r hWexp hW2 hhi hr hrne hcap
    hledger.1 hKT (fun b => Fin (k b)) x y q hqp hql hqo hqd hqc
      (by
        intro b v
        dsimp only [endpointLoad,x,y]
        convert hQl b v using 2
        ext i
        simp)
  let I := Σ b, Fin (k b)
  let CE : I → Set (Sym2 V) := fun z => (C z.1 z.2).edgeSet
  have hCE : ∀ i, CE i ⊆ G.edgeSet := fun i => (C i.1 i.2).edges_subset_edgeSet
  have hEeq : E = (⋃ b, R b) ∪ (allReservoirSpokes W r : Set _) := by
    simp only [E,T,coe_allReservoirSpokes,Set.iUnion_union_distrib]
  have hcov : G.edgeSet \ ((⋃ b, R b) ∪ (allReservoirSpokes W r : Set _)) ⊆
      completedEdges CE := by
    rw [← hEeq, ← SimpleGraph.edgeSet_deleteEdges, ← hK.2.2.2]
    exact hcover
  obtain ⟨hsupp,hind,hHe,hHH,hHC,hHS,hCS,hu,hnum⟩ :=
    three_reservoir_remainder G P' W r hPG' hPP
      (fun b v hv t => (hr b v hv t).2) CE hCE hCC hcount hcov
  let H := residualInternalGraph G R CE
  let S := unusedSpokes (↑(allReservoirSpokes W r)) CE
  let J := I ⊕ S
  let parts : J → Set (Sym2 V) := Sum.elim CE (fun e => {e.val})
  have hSsub : (S : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    have hh : e ∈ (allReservoirSpokes W r : Set _) := by
      have hh := he
      simp only [Finset.mem_coe,S,unusedSpokes,Set.mem_toFinset,Set.mem_sdiff] at hh
      exact hh.1
    exact hE (by rw [hEeq]; exact Or.inr hh)
  have hpart : ∀ j, CycleOrSingleEdge G (parts j) := by
    intro j
    rcases j with i | e
    · exact Or.inl ⟨x i.1 i.2,C i.1 i.2,hCy i.1 i.2,rfl⟩
    · exact Or.inr ⟨e.val,hSsub e.property,rfl⟩
  have hpd : Pairwise fun i j => Disjoint (parts i) (parts j) := by
    intro i j hij
    rcases i with i | e <;> rcases j with j | f
    · exact hCC (fun h => hij (congrArg Sum.inl h))
    · exact (hCS i).mono_right (Set.singleton_subset_iff.mpr f.property)
    · exact (hCS j).symm.mono_left (Set.singleton_subset_iff.mpr e.property)
    · exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (Subtype.ext h)))
  have hpartU : (⋃ j, parts j) = completedEdges CE ∪ (S : Set (Sym2 V)) := by
    ext e
    simp only [Set.mem_iUnion, Set.mem_union, completedEdges, parts]
    constructor
    · rintro ⟨i,hi⟩
      rcases i with i | f
      · exact Or.inl ⟨i,hi⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hi) ▸ f.property)
    · rintro (⟨i,hi⟩ | he)
      · exact ⟨Sum.inl i,hi⟩
      · exact ⟨Sum.inr ⟨e,he⟩,rfl⟩
  let equiv := Fintype.equivFin J
  refine ⟨Fintype.card J,fun i => parts (equiv.symm i),W,H,?_,?_,?_,hWlt,hWsum,
    hHH,?_,?_,?_⟩
  · exact fun i => hpart _
  · intro i j hij
    exact hpd (fun h => hij (equiv.symm.injective h))
  · intro b
    refine ⟨?_,hsupp b⟩
    exact edgeRestriction_le G _
  · intro b i
    rcases hji : equiv.symm i with j | e
    all_goals simp only [hji, parts, Sum.elim_inl, Sum.elim_inr]
    · exact hHC b j
    · exact (hHS b).mono_right (Set.singleton_subset_iff.mpr e.property)
  · have he : (⋃ i, parts (equiv.symm i)) = ⋃ j, parts j := by
      ext e
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨i,hi⟩ => ⟨equiv.symm i,hi⟩,
        fun ⟨j,hj⟩ => ⟨equiv j,by simpa using hj⟩⟩
    rw [he,hpartU]
    exact hu
  · simpa only [J,Fintype.card_sum,Fintype.card_coe] using hnum

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def decompositionCost {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (show ∃ k, EdgeDecomposition G k from ⟨_,edgeDecomposition_singleEdges G⟩)

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

lemma decompositionCost_singleEdges {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G ≤ Nat.card G.edgeSet := decompositionCost_le (edgeDecomposition_singleEdges G)

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma edgeDecomposition_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f)
    (hu : Sym2.map f '' H.edgeSet = G.edgeSet) {k : ℕ} (hk : EdgeDecomposition H k) :
    EdgeDecomposition G k := by
  have := edgeDecomposition_assemble (I := Unit) G (fun _ : Unit => W) (fun _ => H) (fun _ => f)
    (fun _ => hf) (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
    (by rw [Set.iUnion_const]; exact hu) (fun _ => k) (fun _ => hk)
  simpa using this

lemma decompositionCost_on {V : Type} [Fintype V] (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A) :
    decompositionCost G ≤ decompositionCost (G.induce (A:Set V)) := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  have hu : Sym2.map f '' (G.induce (A:Set V)).edgeSet = G.edgeSet := by
    ext e
    constructor
    · rintro ⟨e,he,rfl⟩
      induction e using Sym2.ind with | _ x y => exact he
    · intro he
      induction e using Sym2.ind with
      | _ x y =>
        exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩
  exact decompositionCost_le (edgeDecomposition_map f Subtype.val_injective hu (decompositionCost_spec _))

lemma edgeDecomposition_on {V : Type} (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A)
    {k : ℕ} (hk : EdgeDecomposition (G.induce (A:Set V)) k) : EdgeDecomposition G k := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  apply edgeDecomposition_map f Subtype.val_injective _ hk
  ext e
  constructor
  · rintro ⟨e,he,rfl⟩
    induction e using Sym2.ind with | _ x y => exact he
  · intro he
    induction e using Sym2.ind with
    | _ x y => exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

lemma decompositionCost_assemble_same {V J : Type} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ ∑ j, decompositionCost (H j) := by
  simpa using decompositionCost_adjoin_same (I := Empty) G Empty.elim (fun i => nomatch i)
    (by intro i; exact i.elim) H hHG hHH (fun _ i => nomatch i) (by simpa using hu)

end
end ErdosGallai


end
end
end
end OAI


namespace OAI.ErdosGallai

open Filter Finset Real SimpleGraph
open scoped Classical Topology
noncomputable section

private theorem cycle_from_large_minimum_degree {V : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (hd : ∀ v, k < G.degree v) : ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ k + 2 ≤ p.length := by
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hOnPath : ∀ v, G.Adj a v → v ∈ p.support := by
    intro v hav
    by_contra! hnot
    have hh := hmax v b (p.cons hav.symm) (hp.cons hnot)
    simp at hh
  have hFar : ∃ i, k < i ∧ i ≤ p.length ∧ G.Adj a (p.getVert i) := by
    by_contra! hnear
    have hn : G.neighborFinset a ⊆ (Finset.Icc 1 k).image p.getVert := by
      intro v hv
      have hadj := G.mem_neighborFinset a v |>.mp hv
      obtain ⟨i, hi, hlen⟩ := p.mem_support_iff_exists_getVert.mp (hOnPath v hadj)
      have hi1 : 1 ≤ i := by
        by_contra! hzero
        have hz : i = 0 := by omega
        exact hadj.ne (by simpa [hz] using hi)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hi1,
        le_of_not_gt fun h => hnear i h hlen (hi.symm ▸ hadj)⟩, hi⟩
    have hCard := (Finset.card_le_card hn).trans Finset.card_image_le
    rw [G.card_neighborFinset_eq_degree, Nat.card_Icc] at hCard
    exact (not_lt_of_ge (by simpa using hCard)) (hd a)
  obtain ⟨i, hi, hlen, ha⟩ := hFar
  let q := (p.take i).cons ha.symm
  have hq : q.length = i + 1 := by simp [q, Walk.take_length, min_eq_left hlen]
  refine ⟨p.getVert i, q, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa [q] using hp.take i
  · omega
  · omega

private theorem long_cycle_from_edge_count (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n → k * n < G.edgeFinset.card →
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ k + 2 ≤ p.length := by
  induction n with
  | zero =>
    intro V _ _ G hV hm
    have hE := G.card_edgeFinset_le_card_choose_two
    have hz : (Fintype.card V).choose 2 = 0 := by simp [hV]
    rw [hz] at hE
    omega
  | succ n ih =>
    intro V _ _ G hV hm
    letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    by_cases hd : ∀ v, k < G.degree v
    · exact cycle_from_large_minimum_degree G k hk hd
    · push Not at hd
      obtain ⟨v, hv⟩ := hd
      let W := ({v} : Set V)ᶜ
      let H := G.induce W
      have hW : Fintype.card W = n := by
        change Fintype.card ↥(({v} : Set V)ᶜ) = n
        rw [Fintype.card_compl_set, Set.card_singleton, hV]
        omega
      have hEdges : H.edgeFinset.card + G.degree v = G.edgeFinset.card := by
        change (G.induce ({v} : Set V)ᶜ).edgeFinset.card + G.degree v = _
        rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet,
          Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]
      have hHN : k * n < H.edgeFinset.card := by
        rw [Nat.mul_succ] at hm
        omega
      obtain ⟨w, p, hp, hlen⟩ := ih H hW hHN
      let f : H →g G := (SimpleGraph.Embedding.induce W).toHom
      exact ⟨f w, p.map f, hp.map Subtype.val_injective, by simpa using hlen⟩

private theorem delete_longest_gain {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hm : Fintype.card V < G.edgeFinset.card) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ G.edgeFinset.card ≤ Fintype.card V * p.length := by
  let n := Fintype.card V
  let m := G.edgeFinset.card
  have hn : 0 < n := by
    by_contra! hz
    have hE := G.card_edgeFinset_le_card_choose_two
    have hZero : n = 0 := by omega
    change m ≤ n.choose 2 at hE
    simp [hZero] at hE
    omega
  let k := (m - 1) / n
  have hk : 1 ≤ k := (Nat.le_div_iff_mul_le hn).mpr (by omega)
  have hLess : k * n < m := by
    dsimp [k]
    have hSum := Nat.div_mul_le_self (m - 1) n
    omega
  obtain ⟨v, p, hp, hLen⟩ := long_cycle_from_edge_count k hk n G rfl hLess
  refine ⟨v, p, hp, ?_⟩
  have hdiv : k * n + (m - 1) % n = m - 1 := by
    simpa only [k, Nat.mul_comm] using Nat.div_add_mod (m - 1) n
  have hmod := Nat.mod_lt (m - 1) hn
  have hStep : m ≤ n * (k + 1) := by
    rw [Nat.mul_succ, Nat.mul_comm n k]
    have hnm : n < m := hm
    omega
  exact hStep.trans (Nat.mul_le_mul_left n (by omega))

private theorem cost_of_removing_cycle {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {x : V} (p : G.Walk x x) (hp : p.IsCycle) :
    decompositionCost G ≤ 1 + decompositionCost (G.deleteEdges p.edgeSet) := by
  let H := fun _ : Unit => G.deleteEdges p.edgeSet
  have hDis : ∀ a b : Unit, Disjoint (H a).edgeSet (p.edgeSet : Set (Sym2 V)) := by
    intro a b
    rw [show (H a).edgeSet = G.edgeSet \ p.edgeSet from G.edgeSet_deleteEdges _]
    exact Set.disjoint_sdiff_left
  have hCover : p.edgeSet ∪ (H ()).edgeSet = G.edgeSet := by
    rw [show (H ()).edgeSet = G.edgeSet \ p.edgeSet from G.edgeSet_deleteEdges _]
    have hs : p.edgeSet ⊆ G.edgeSet := fun e he => p.edges_subset_edgeSet he
    ext e
    constructor
    · rintro (he | ⟨he, -⟩)
      · exact hs he
      · exact he
    · intro he
      exact if h : e ∈ p.edgeSet then Or.inl h else Or.inr ⟨he, h⟩
  have hCost := decompositionCost_adjoin_same G (fun _ : Unit => p.edgeSet)
    (fun _ => Or.inl ⟨x, p, hp, rfl⟩)
    (fun u v h => False.elim (h (Subsingleton.elim _ _))) H (fun _ => G.deleteEdges_le _)
    (fun u v h => False.elim (h (Subsingleton.elim _ _))) hDis (by
      simpa only [H, Set.iUnion_const] using hCover)
  simpa [H] using hCost

private def cyclePotential (n m : ℕ) : ℝ :=
  if m ≤ n then m else n + n * (Real.log m - Real.log n)

private theorem potential_decrease (n m q : ℕ) (hn : 0 < n) (hm : n < m)
    (hq : q ≤ m) (hgain : m ≤ n * q) :
    1 + cyclePotential n (m - q) ≤ cyclePotential n m := by
  have hrn : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrm : (n : ℝ) < m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := hrn.trans hrm
  have hqr : (m : ℝ) ≤ (n : ℝ) * q := by exact_mod_cast hgain
  have hqCast : ((m - q : ℕ) : ℝ) = (m : ℝ) - q := Nat.cast_sub hq
  have hlog (x : ℝ) (hx : 0 < x) : (m - x) / m ≤ Real.log m - Real.log x := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hx hmpos)
    rw [Real.log_div hx.ne' hmpos.ne'] at hh
    rw [sub_div, div_self hmpos.ne']
    linarith
  rw [show cyclePotential n m = n + n * (log m - log n) by
    simp [cyclePotential, Nat.not_le.mpr hm]]
  by_cases hsmall : m - q ≤ n
  · rw [cyclePotential, if_pos hsmall, hqCast]
    have hb : (m : ℝ) - q ≤ n := by simpa only [hqCast] using (show ((m - q : ℕ) : ℝ) ≤ n by exact_mod_cast hsmall)
    have ht := mul_le_mul_of_nonneg_left (hlog n hrn) hrn.le
    have hu : (n : ℝ) / m ≤ 1 := (div_le_one hmpos).mpr hrm.le
    have hScale : ((n : ℝ) - (m - q)) * ((n : ℝ) / m) ≤ n - (m - q) :=
      mul_le_of_le_one_right (by linarith) hu
    have hEnough : (1 : ℝ) ≤ (n : ℝ) * q / m := (le_div_iff₀ hmpos).mpr (by simpa using hqr)
    linarith only [ht, hScale, hEnough,
      show (n : ℝ) * ((m - n) / m) + (n - (m - q)) * (n / m) = n * q / m by ring]
  · rw [cyclePotential, if_neg hsmall]
    have hpos : 0 < ((m - q : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - q by omega)
    have ht := mul_le_mul_of_nonneg_left (hlog _ hpos) hrn.le
    rw [hqCast] at ht ⊢
    have hEnough : (1 : ℝ) ≤ (n : ℝ) * q / m := (le_div_iff₀ hmpos).mpr (by simpa using hqr)
    linarith only [ht, hEnough, hqCast,
      show (n : ℝ) * ((m - (m - q)) / m) = n * q / m by ring]

private theorem cost_le_potential (m : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hm : G.edgeFinset.card = m) :
    (decompositionCost G : ℝ) ≤ cyclePotential (Fintype.card V) m := by
  induction m using Nat.strong_induction_on generalizing G with
  | h m ih =>
    let n := Fintype.card V
    by_cases hSmall : m ≤ n
    · rw [cyclePotential, if_pos hSmall, ← hm]
      have h := decompositionCost_singleEdges G
      rw [Nat.card_eq_fintype_card, G.card_edgeSet] at h
      exact_mod_cast h
    have hDense : n < G.edgeFinset.card := by omega
    obtain ⟨x, p, hp, hLong⟩ := delete_longest_gain G hDense
    let H := G.deleteEdges p.edgeSet
    have hCard : H.edgeFinset.card = m - p.length := by
      have hs : p.edges.toFinset ⊆ G.edgeFinset := by
        intro e he
        rw [List.mem_toFinset] at he
        exact G.mem_edgeFinset.mpr (p.edges_subset_edgeSet he)
      have hset : (p.edges.toFinset : Set (Sym2 V)) = p.edgeSet := by
        ext e
        simp [Walk.mem_edgeSet]
      change (G.deleteEdges p.edgeSet).edgeFinset.card = _
      rw [← hset, edgeFinset_deleteEdges, Finset.card_sdiff_of_subset hs,
        List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges, hm]
    have hplen : p.length ≤ m := by
      have he : p.edges.toFinset ⊆ G.edgeFinset := by
        intro e he
        exact G.mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
      simpa only [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges, hm]
        using Finset.card_le_card he
    have hL : 0 < p.length := by have := hp.three_le_length; omega
    have hn : 0 < n := by
      have hh := G.card_edgeFinset_le_card_choose_two
      by_contra! hz
      have hz' : Fintype.card V = 0 := by omega
      have hchoose : (Fintype.card V).choose 2 = 0 := by simp [hz']
      rw [hchoose] at hh
      omega
    have hPrev := ih (m - p.length) (by omega) H (by
      convert hCard using 2
      ext e
      simp)
    have hBound : (decompositionCost G : ℝ) ≤ 1 + (decompositionCost H : ℝ) := by
      exact_mod_cast cost_of_removing_cycle G p hp
    calc
      _ ≤ 1 + cyclePotential n (m - p.length) := hBound.trans (add_le_add_right hPrev 1)
      _ ≤ _ := potential_decrease n m p.length hn (by omega) hplen (hm ▸ hLong)

theorem greedy_cycle_cost {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (decompositionCost G : ℝ) ≤ Fintype.card V * (1 + log (Fintype.card V)) := by
  let n := Fintype.card V
  let m := G.edgeFinset.card
  have hBound := cost_le_potential m G rfl
  by_cases hn : n = 0
  · have hm : m = 0 := by
      have h := G.card_edgeFinset_le_card_choose_two
      change m ≤ n.choose 2 at h
      simp [hn] at h
      omega
    simpa [cyclePotential, hm, hn, n] using hBound
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hl : 0 ≤ log (n : ℝ) := log_nonneg hnR
  by_cases hSmall : m ≤ n
  · rw [cyclePotential, if_pos hSmall] at hBound
    have hmR : (m : ℝ) ≤ n := by exact_mod_cast hSmall
    have hnR' : 0 ≤ (n : ℝ) := by positivity
    exact hBound.trans (by nlinarith [mul_nonneg hnR' hl])
  · rw [cyclePotential, if_neg hSmall] at hBound
    have hEdges : (m : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hm := G.card_edgeFinset_le_card_choose_two
      have hchoose : n.choose 2 ≤ n ^ 2 := Nat.choose_le_pow _ _
      exact_mod_cast hm.trans hchoose
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hLog : log (m : ℝ) ≤ 2 * log (n : ℝ) := by
      simpa [Real.log_pow] using Real.log_le_log hmpos hEdges
    have hnR' : 0 ≤ (n : ℝ) := by positivity
    exact hBound.trans (by nlinarith [mul_le_mul_of_nonneg_left hLog hnR'])

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Filter Finset Real SimpleGraph
open scoped Classical Topology
noncomputable section

private theorem thinning_log_tendsto :
    Tendsto (fun D : ℝ => 6 * thinning D * (1 + log D)) atTop (𝓝 0) := by
  have hl := (Asymptotics.isLittleO_iff_tendsto'
    (l := (atTop : Filter ℝ))
    (f := log) (g := fun D : ℝ => D ^ (1 / 200 : ℝ))
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
      exact fun h => ((Real.rpow_pos_of_pos hD _).ne' h).elim)).mp
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200))
  have hs : Tendsto (fun D : ℝ => thinning D + log D / D ^ (1 / 200 : ℝ))
      atTop (𝓝 0) := by simpa using thinning_tendsto.add hl
  have ht : Tendsto (fun D : ℝ => 6 *
      (thinning D + log D / D ^ (1 / 200 : ℝ))) atTop (𝓝 0) := by
    have hConst : Tendsto (fun _ : ℝ => (6 : ℝ)) atTop (𝓝 6) := tendsto_const_nhds
    simpa using hConst.mul hs
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  have hEq : log D / D ^ (1 / 200 : ℝ) = thinning D * log D := by
    rw [thinning, Real.rpow_neg hD.le, div_eq_mul_inv, mul_comm]
  rw [hEq]
  ring

theorem linear_cost_cut_dense (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      CutExpansion G (c * Fintype.card V) →
      (decompositionCost G : ℝ) ≤ C * Fintype.card V := by
  obtain ⟨D₀, hD₀, hResidue⟩ := small_residue c hc
  have hEventually : ∀ᶠ D : ℝ in atTop, 6 * thinning D * (1 + log D) ≤ 1 := by
    have h := thinning_log_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact h.mono (fun _ hD => hD.le)
  obtain ⟨D₁, hScale⟩ := eventually_atTop.mp hEventually
  let C := max 10 (max D₀ D₁)
  have hC : (10 : ℝ) ≤ C := le_max_left _ _
  refine ⟨C, by linarith, ?_⟩
  intro V _ _ G _ hExpansion
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := by dsimp [n]; positivity
  by_cases hThreshold : max D₀ D₁ ≤ n
  · have hn₀ : D₀ ≤ n := (le_max_left _ _).trans hThreshold
    have hn₁ : D₁ ≤ n := (le_max_right _ _).trans hThreshold
    have hnLarge : 1 ≤ n := hD₀.le.trans hn₀
    have hLow : n ^ (9 / 10 : ℝ) ≤ n := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hnLarge
        (show (9 / 10 : ℝ) ≤ 1 by norm_num))
    have hHigh : n ≤ n ^ (51 / 50 : ℝ) := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hnLarge
        (show (1 : ℝ) ≤ 51 / 50 by norm_num))
    have hExpand' : Splitting.CutExpansion G (c * n ^ (9 / 10 : ℝ)) := by
      intro S
      apply le_trans _ (hExpansion S)
      gcongr
    obtain ⟨k, parts, W, H, hp, hd, hHG, -, hMass, hHH, hHP, hu, hk⟩ :=
      hResidue n hn₀ V G G le_rfl hLow hHigh hExpand'
    have hcost (b : Fin 3) :
        (decompositionCost (H b) : ℝ) ≤ (W b).card * (1 + log n) := by
      have hSupport : ∀ ⦃v w⦄, (H b).Adj v w → v ∈ W b ∧ w ∈ W b := by
        intro v w h
        exact ⟨(hHG b).2 ⟨w, h⟩, (hHG b).2 ⟨v, h.symm⟩⟩
      calc
        _ ≤ (decompositionCost ((H b).induce (W b : Set V)) : ℝ) :=
          Nat.cast_le.mpr (decompositionCost_on _ _ hSupport)
        _ ≤ (W b).card * (1 + log ((W b).card : ℝ)) := by
          simpa using greedy_cycle_cost ((H b).induce (W b : Set V))
        _ ≤ _ := by
          by_cases hEmpty : (W b).card = 0
          · simp [hEmpty]
          gcongr
          dsimp [n]
          exact_mod_cast (W b).card_le_univ
    have hsum : (∑ b, (decompositionCost (H b) : ℝ)) ≤
        (6 * thinning n * n) * (1 + log n) := by
      calc
        _ ≤ ∑ b : Fin 3, (W b).card * (1 + log n) := Finset.sum_le_sum (fun b _ => hcost b)
        _ = (∑ b : Fin 3, ((W b).card : ℝ)) * (1 + log n) := by rw [Finset.sum_mul]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by linarith [log_nonneg hnLarge])
          exact_mod_cast hMass
    have hK : (k : ℝ) ≤ 9 * n := by dsimp [n]; exact_mod_cast hk
    have hTotal : (decompositionCost G : ℝ) ≤ k + ∑ b, (decompositionCost (H b) : ℝ) := by
      exact_mod_cast (by
        simpa using decompositionCost_adjoin_same G parts hp hd H
          (fun b => (hHG b).1) hHH hHP hu :
        decompositionCost G ≤ k + ∑ b, decompositionCost (H b))
    have hFinal : (6 * thinning n * n) * (1 + log n) ≤ n := by
      calc
        _ = (6 * thinning n * (1 + log n)) * n := by ring
        _ ≤ 1 * n := mul_le_mul_of_nonneg_right (hScale n hn₁) hn
        _ = n := one_mul n
    exact (by linarith only [hTotal, hsum, hK, hFinal] :
      (decompositionCost G : ℝ) ≤ 10 * n).trans (mul_le_mul_of_nonneg_right hC hn)
  · have hnC : n ≤ C := (le_of_not_ge hThreshold).trans (le_max_right _ _)
    have hEdges : (G.edgeFinset.card : ℝ) ≤ n * n := by
      have h := G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)
      rw [pow_two] at h
      dsimp [n]
      exact_mod_cast h
    have hCost : (decompositionCost G : ℝ) ≤ G.edgeFinset.card := by
      have h := decompositionCost_singleEdges G
      rw [Nat.card_eq_fintype_card, G.card_edgeSet] at h
      exact_mod_cast h
    exact (hCost.trans hEdges).trans (mul_le_mul_of_nonneg_right hnC hn)

end
end OAI.ErdosGallai


namespace DenseCycleDecomposition

open SimpleGraph List
open scoped Classical

private theorem path_darts_forward {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) :
    p.darts.Pairwise (fun e f => e.fst ≠ f.snd) := by
  induction p with
  | nil => simp
  | @cons x y z hadj tail ih =>
    rw [Walk.darts_cons, List.pairwise_cons]
    obtain ⟨ht, hx⟩ := (Walk.cons_isPath_iff hadj tail).1 hp
    refine ⟨?_, ih ht⟩
    intro f hf heq
    change x = f.snd at heq
    exact hx (heq.symm ▸ tail.dart_snd_mem_support_of_mem_darts hf)

private theorem cycle_darts_not_sublist_path {V : Type*} {G : SimpleGraph V} {a b x : V}
    (p : G.Walk a b) (hp : p.IsPath) (c : G.Walk x x) (hc : c.IsCycle) :
    ¬ c.darts <+ p.darts := by
  intro hcp
  have hforward := (path_darts_forward p hp).sublist hcp
  cases c with
  | nil => exact hc.not_nil (by simp)
  | @cons x y _ h tail =>
    rw [Walk.darts_cons, List.pairwise_cons] at hforward
    have htn : ¬ tail.Nil := fun ht => h.ne ht.eq.symm
    exact hforward.1 _ (tail.lastDart_mem_darts htn) rfl

private theorem closed_trail_partition {V : Type*} {G : SimpleGraph V}
    (cost : G.Dart → Bool) (n : ℕ) (a : V) (w : G.Walk a a)
    (hw : w.IsTrail) (hlen : w.length = n)
    (hcost : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.darts <+ w.darts →
      0 < c.darts.countP cost) :
    ∃ k : ℕ, ∃ S : Fin k → Set (Sym2 V),
      (∀ i, ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ S i = c.edgeSet) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (⋃ i, S i) = w.edgeSet ∧ k ≤ w.darts.countP cost := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : w.Nil
    · have hnil := Walk.nil_iff_eq_nil.mp hn
      subst w
      exact ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp, by simp⟩
    have hnotpath : ¬ w.IsPath := fun hp => hn (w.isPath_iff_nil.mp hp)
    have hex : ∃ (x : V) (c : G.Walk x x), c.IsSubwalk w ∧ c.IsCycle := by
      by_contra! h
      exact hnotpath (hw.isPath_iff_isSubwalk_imp_not_isCycle.mpr h)
    obtain ⟨x, c, ⟨p, q, rfl⟩, hc⟩ := hex
    let w' := p.append q
    have hsub : w'.darts <+ ((p.append c).append q).darts := by
      simp only [w', Walk.darts_append]
      exact (List.sublist_append_left _ _).append (List.Sublist.refl _)
    have hsubEdges : w'.edges <+ ((p.append c).append q).edges := by
      simp only [w', Walk.edges_append]
      exact (List.sublist_append_left _ _).append (List.Sublist.refl _)
    have hw' : w'.IsTrail := by
      rw [Walk.isTrail_def]
      exact hsubEdges.nodup hw.edges_nodup
    have hn' : w'.length < n := by
      simp only [w', Walk.length_append] at hlen ⊢
      have := hc.three_le_length
      omega
    obtain ⟨k, S, hS, hSd, hSu, hSk⟩ := ih w'.length hn' a w' hw' rfl
      (fun v d hd hsub' => hcost v d hd (hsub'.trans hsub))
    have hdisjPC : p.edges.Disjoint c.edges :=
      ((Walk.isTrail_append p c).mp
        ((Walk.isTrail_append (p.append c) q).mp hw).1).2.2
    have hdisjCQ : c.edges.Disjoint q.edges := by
      apply List.disjoint_left.mpr
      intro e he hq
      exact List.disjoint_left.mp ((Walk.isTrail_append (p.append c) q).mp hw).2.2
        (by simp [Walk.edges_append, he]) hq
    have hcDisj : Disjoint c.edgeSet w'.edgeSet := by
      rw [Set.disjoint_left]
      intro e he he'
      have he'' : e ∈ p.edges ∨ e ∈ q.edges := by
        simpa only [Walk.mem_edgeSet, w', Walk.edges_append, List.mem_append] using he'
      rcases he'' with hp | hq
      · exact List.disjoint_left.mp hdisjPC hp he
      · exact List.disjoint_left.mp hdisjCQ he hq
    refine ⟨k + 1, Fin.cons c.edgeSet S, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact ⟨x, c, hc, rfl⟩
      · exact fun j => hS j
    · intro i j hne
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact False.elim (hne rfl)
        | succ j =>
          exact hcDisj.mono_right (hSu ▸ Set.subset_iUnion S j)
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          exact hcDisj.symm.mono_left (hSu ▸ Set.subset_iUnion S i)
        | succ j => exact hSd (fun e => hne (congrArg Fin.succ e))
    · rw [Set.iUnion_cons]
      simp only [hSu, w', Walk.edgeSet_append]
      exact Set.union_left_comm _ _ _ |>.trans (Set.union_assoc _ _ _).symm
    · have hsubC : c.darts <+ ((p.append c).append q).darts := by
        simp only [Walk.darts_append]
        exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)
      have hq := hcost x c hc hsubC
      simp only [w', Walk.darts_append, List.countP_append] at hSk ⊢
      omega

theorem close_with_short_return {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (q : G.Walk b a) (hp : p.IsPath) (hw : (p.append q).IsTrail) :
    ∃ k : ℕ, ∃ S : Fin k → Set (Sym2 V),
      (∀ i, ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ S i = c.edgeSet) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (⋃ i, S i) = p.edgeSet ∪ q.edgeSet ∧ k ≤ q.length := by
  classical
  let cost (d : G.Dart) : Bool := decide (d ∉ p.darts)
  have hd : p.darts.Disjoint q.darts := by
    rw [List.disjoint_left]
    intro d hdp hdq
    exact List.disjoint_left.mp ((Walk.isTrail_append p q).mp hw).2.2
      (by exact List.mem_map_of_mem hdp)
      (by exact List.mem_map_of_mem hdq)
  have mass : (p.append q).darts.countP cost = q.length := by
    rw [Walk.darts_append, List.countP_append]
    have hp₀ : p.darts.countP cost = 0 := List.countP_eq_zero.2 (by simp [cost])
    have hq₁ : q.darts.countP cost = q.darts.length := List.countP_eq_length.2 (by
      intro d hdq
      simp only [cost, decide_eq_true_eq]
      exact fun hdp => List.disjoint_left.mp hd hdp hdq)
    simp [hp₀, hq₁]
  have hcost : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.darts <+ (p.append q).darts →
      0 < c.darts.countP cost := by
    intro x c hc hcsub
    by_contra! hz
    have hzero : c.darts.countP cost = 0 := by omega
    let keep (d : G.Dart) : Bool := decide (d ∈ p.darts)
    have hkeepC : c.darts.filter keep = c.darts := List.filter_eq_self.2 (by
      intro d hd
      have hh := List.countP_eq_zero.1 hzero d hd
      simpa [keep, cost] using hh)
    have hkeepP : p.darts.filter keep = p.darts := List.filter_eq_self.2 (by simp [keep])
    have hkeepQ : q.darts.filter keep = [] := List.filter_eq_nil_iff.2 (by
      intro d hdq
      simpa [keep] using fun hdp => List.disjoint_left.mp hd hdp hdq)
    have hsub := hcsub.filter keep
    rw [hkeepC, Walk.darts_append, List.filter_append, hkeepP, hkeepQ, List.append_nil] at hsub
    exact cycle_darts_not_sublist_path p hp c hc hsub
  obtain ⟨k, S, hS, hSd, hSu, hSk⟩ :=
    closed_trail_partition cost _ a (p.append q) hw rfl hcost
  exact ⟨k, S, hS, hSd, by rw [← Walk.edgeSet_append, hSu], mass ▸ hSk⟩

end DenseCycleDecomposition

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

theorem decompositionCost_with_short_returns {V I : Type} [Fintype V] [Fintype I]
    (G R : SimpleGraph V) (hR : R ≤ G)
    (a b : I → V) (p : ∀ i, G.Walk (a i) (b i)) (q : ∀ i, G.Walk (b i) (a i))
    (hp : ∀ i, (p i).IsPath) (htrail : ∀ i, ((p i).append (q i)).IsTrail)
    (hpair : Pairwise (fun i j => Disjoint ((p i).edgeSet ∪ (q i).edgeSet)
      ((p j).edgeSet ∪ (q j).edgeSet)))
    (hdisjoint : ∀ i, Disjoint R.edgeSet ((p i).edgeSet ∪ (q i).edgeSet))
    (hunion : (⋃ i, ((p i).edgeSet ∪ (q i).edgeSet)) ∪ R.edgeSet = G.edgeSet) :
    decompositionCost G ≤ (∑ i, (q i).length) + decompositionCost R := by
  have hParts (i : I) := DenseCycleDecomposition.close_with_short_return (p i) (q i)
    (hp i) (htrail i)
  choose k A hA hAD hCover hCount using hParts
  let P : (Σ i : I, Fin (k i)) → Set (Sym2 V) := fun i => A i.1 i.2
  have hSubset (i : Σ i : I, Fin (k i)) :
      P i ⊆ (p i.1).edgeSet ∪ (q i.1).edgeSet :=
    (hCover i.1) ▸ Set.subset_iUnion (A i.1) i.2
  have hSubpieces (i : Σ i : I, Fin (k i)) : CycleOrSingleEdge G (P i) := .inl (hA i.1 i.2)
  have hDisjoint : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i, r⟩ ⟨j, s⟩ h
    by_cases hs : i = j
    · subst j
      exact hAD i (fun he => h (by cases he; rfl))
    · exact (hpair hs).mono (hSubset ⟨i, r⟩) (hSubset ⟨j, s⟩)
  have hCover' : (⋃ i, P i) = ⋃ i, ((p i).edgeSet ∪ (q i).edgeSet) := by
    ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      exact Set.mem_iUnion.mpr ⟨i.1, hSubset i hi⟩
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      rw [← hCover i] at hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, hj⟩
  have hCost := decompositionCost_adjoin_same G P hSubpieces hDisjoint
    (fun _ : Unit => R) (fun _ => hR)
    (fun _ _ h => False.elim (h (Subsingleton.elim _ _)))
    (fun _ i => (hdisjoint i.1).mono_right (hSubset i))
    (by simpa only [hCover', Set.iUnion_const] using hunion)
  rw [Fintype.card_sigma] at hCost
  have hCost' : decompositionCost G ≤ (∑ i : I, k i) + decompositionCost R := by
    simpa using hCost
  exact hCost'.trans (Nat.add_le_add_right (Finset.sum_le_sum (fun i _ => hCount i)) _)

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

private theorem first_ball_large {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ)
    (hexp : CutExpansion P h) (hV : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ((incidentEdges F s).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    h / 2 ≤ ((walkBall (avoidGraph P F W) s 1).card : ℝ) := by
  let N := Sampling.neighborsIn P s Finset.univ
  let excluded := N.filter (fun v => s(s, v) ∈ F)
  have hN : h ≤ (N.card : ℝ) := Sampling.cutExpansion_minDegree P hexp hV s
  have hExcluded : excluded.card ≤ (incidentEdges F s).card := by
    apply Finset.card_le_card_of_injOn (fun v : V => s(s, v))
    · intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, by simp⟩
    · intro u hu v hv heq
      rcases Sym2.eq_iff.mp heq with ⟨-, huv⟩ | ⟨hsv, hus⟩
      · exact huv
      · exact hus.trans hsv
  have hReach : N \ (W ∪ excluded) ⊆ walkBall (avoidGraph P F W) s 1 := by
    intro v hv
    obtain ⟨hvN, hvNot⟩ := Finset.mem_sdiff.mp hv
    have hvNW : v ∉ W := fun hvW => hvNot (Finset.mem_union_left _ hvW)
    have hvNF : s(s, v) ∉ F := fun he => hvNot
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvN, he⟩))
    have hAdj : P.Adj s v := (Finset.mem_filter.mp hvN).2
    have h : (avoidGraph P F W).Adj s v := ⟨hAdj, hvNF, hs, hvNW⟩
    exact (mem_walkBall _ _ _ _).mpr ⟨Walk.cons h .nil, Nat.le_refl _⟩
  have hCount : N.card ≤ (walkBall (avoidGraph P F W) s 1).card +
      W.card + (incidentEdges F s).card := by
    have hsum := Finset.card_sdiff_add_card_inter N (W ∪ excluded)
    have htake := Finset.card_le_card hReach
    have hcut := Finset.card_le_card (Finset.inter_subset_right (s₁ := N) (s₂ := W ∪ excluded))
    have hun := Finset.card_union_le W excluded
    omega
  have hCountR : (N.card : ℝ) ≤ (walkBall (avoidGraph P F W) s 1).card +
      W.card + (incidentEdges F s).card := by exact_mod_cast hCount
  linarith

private theorem dense_balls_intersect {V : Type} [Fintype V] [DecidableEq V]
    (c : ℝ) (hc : 0 < c) (K : ℕ) (hK : 4 / c ^ 2 ≤ (K : ℝ))
    (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ)
    (hh : c * Fintype.card V ≤ h) (hexp : CutExpansion P h)
    (hV : 2 ≤ Fintype.card V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 < (walkBall (avoidGraph P F W) s (K + 1)).card := by
  let n : ℝ := Fintype.card V
  let B := fun j => walkBall (avoidGraph P F W) s j
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (by omega : 0 < Fintype.card V)
  have hhPos : 0 < h := (mul_pos hc hn).trans_le hh
  have h₁ : h / 2 ≤ (B 1).card := first_ball_large P h hexp hV F W s hs (hF s) hW
  change n / 2 < (B (K + 1)).card
  by_contra! hLast
  have hStage (j : ℕ) (hj : j ≤ K) : (j : ℝ) * (c ^ 2 * n / 4) ≤ (B (j + 1)).card := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hSmall : ((B (j + 1)).card : ℝ) ≤ n / 2 := by
        apply le_trans _ hLast
        exact_mod_cast Finset.card_le_card
          (walkBall_mono (avoidGraph P F W) s (by omega : j + 1 ≤ K + 1))
      have hStart : h / 2 ≤ (B (j + 1)).card := h₁.trans (by
        exact_mod_cast Finset.card_le_card
          (walkBall_mono (avoidGraph P F W) s (by omega : 1 ≤ j + 1)))
      have hGrow := walkBall_growth_of_incidents P h hexp hn F W s hs hF hW (j + 1) hSmall
      have hRatio : c / 2 ≤ h / (2 * n) := by
        apply (le_div_iff₀ (by positivity)).mpr
        linarith only [hh]
      have hIncrease : c ^ 2 * n / 4 ≤ (h / (2 * n)) * (B (j + 1)).card := by
        calc
          _ = (c / 2) * (c * n / 2) := by ring
          _ ≤ (h / (2 * n)) * (B (j + 1)).card :=
            mul_le_mul hRatio (by linarith only [hStart, hh])
              (by positivity) (div_nonneg hhPos.le (by positivity))
      have hj' : j ≤ K := by omega
      have hPrev := ih hj'
      change (1 + h / (2 * n)) * (B (j + 1)).card ≤ (B (j + 1 + 1)).card at hGrow
      push_cast
      linarith only [hGrow, hPrev, hIncrease]
  have hTotal : n ≤ (K : ℝ) * (c ^ 2 * n / 4) := by
    have hhK := (div_le_iff₀ (sq_pos_of_pos hc)).mp hK
    nlinarith only [mul_le_mul_of_nonneg_right hhK (div_nonneg hn.le (by norm_num : (0 : ℝ) ≤ 4))]
  linarith only [hStage K le_rfl, hTotal, hLast, hn]

theorem short_dense_route {V : Type} [Fintype V] [DecidableEq V]
    (c : ℝ) (hc : 0 < c) (K : ℕ) (hK : 4 / c ^ 2 ≤ (K : ℝ))
    (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ)
    (hh : c * Fintype.card V ≤ h) (hexp : CutExpansion P h)
    (hV : 2 ≤ Fintype.card V) (F : Finset (Sym2 V)) (W : Finset V)
    (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ 2 * (K + 1) ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  let H := avoidGraph P F W
  let A := walkBall H s (K + 1)
  let B := walkBall H t (K + 1)
  have hA := dense_balls_intersect c hc K hK P h hh hexp hV F W s hs hF hW
  have hB := dense_balls_intersect c hc K hK P h hh hexp hV F W t ht hF hW
  have hMeet : (A ∩ B).Nonempty := by
    apply Finset.card_pos.mp
    have heq := Finset.card_union_add_card_inter A B
    have hUn := Finset.card_le_univ (A ∪ B)
    have hAB : Fintype.card V < A.card + B.card := by
      exact_mod_cast (show (Fintype.card V : ℝ) < (A.card : ℝ) + B.card from by
        dsimp [A, B, H]
        linarith only [hA, hB])
    omega
  obtain ⟨v, hv⟩ := hMeet
  obtain ⟨p, hp⟩ := (mem_walkBall H s v _).mp (Finset.mem_inter.mp hv).1
  obtain ⟨q, hq⟩ := (mem_walkBall H t v _).mp (Finset.mem_inter.mp hv).2
  let walk := (p.append q.reverse).bypass
  let routed := walk.mapLe (avoidGraph_le P F W)
  refine ⟨routed, ((p.append q.reverse).bypass_isPath).mapLe _, ?_, ?_, ?_⟩
  · simp only [routed, Walk.length_mapLe, walk]
    apply (p.append q.reverse).length_bypass_le_length.trans
    simp only [Walk.length_append, Walk.length_reverse]
    omega
  · simpa only [routed, Walk.edges_mapLe_eq_edges] using walk_avoids_edges P F W walk
  · simpa only [routed, Walk.support_mapLe_eq_support] using walk_avoids_support P F W walk hs

theorem dense_route_family {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (c : ℝ) (hc : 0 < c) (K : ℕ) (hK : 4 / c ^ 2 ≤ (K : ℝ))
    (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ)
    (hh : c * Fintype.card V ≤ h) (hexp : CutExpansion P h)
    (hV : 2 ≤ Fintype.card V) (x y : I → V) (k : ℝ)
    (hLoad : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hDegree : h / 8 + 2 + k ≤ h / 4)
    (hTotal : 128 * (2 * ((K : ℝ) + 1) * Fintype.card I) ≤ h ^ 2) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ 2 * (K + 1)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      ∀ v, ((incidentEdges (usedEdges univ q) v).card : ℝ) ≤ h / 4 := by
  have hPositive : 0 < h := lt_of_lt_of_le (by
    have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
    positivity) hh
  have hLoadPartial (A : Finset I) (v : V) : (endpointLoad A x y v : ℝ) ≤ k :=
    (Nat.cast_le.mpr (endpointLoad_mono (Finset.subset_univ A) x y v)).trans (hLoad v)
  have hDefault : ∀ i, ∃ q : P.Walk (x i) (y i), q.IsPath := by
    intro i
    obtain ⟨q, hq, -, -, -⟩ := short_dense_route c hc K hK P h hh hexp hV ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨q, hq⟩
  let defaultRoute (i : I) := Classical.choose (hDefault i)
  have hBuild : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i ∈ A, (q i).IsPath ∧ (q i).length ≤ 2 * (K + 1)) ∧
      (A : Set I).Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      ∀ v, ((incidentEdges (usedEdges A q) v).card : ℝ) ≤ h / 8 + 2 + endpointLoad A x y v := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultRoute, by simp, by simp, ?_⟩
      intro v
      simp [usedEdges, incidentEdges, endpointLoad]
      linarith only [hPositive]
    | @insert i A hi ih =>
      obtain ⟨q, hq, hd, hUsed⟩ := ih
      let F := usedEdges A q
      let W := saturated F h \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hLocal := usedEdges_card_le A q (2 * (K + 1)) (fun j hj => (hq j hj).2)
        have hCombined : F.card ≤ (2 * (K + 1)) * Fintype.card I :=
          hLocal.trans (Nat.mul_le_mul_left _ A.card_le_univ)
        have hCombinedR : (F.card : ℝ) ≤ 2 * ((K : ℝ) + 1) * Fintype.card I := by
          exact_mod_cast hCombined
        linarith only [hCombinedR, hTotal]
      have hWcard : (W.card : ℝ) ≤ h / 4 := by
        have hS := saturated_card_le F h hPositive hFcard
        have hSmall : (W.card : ℝ) ≤ (saturated F h).card := by
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : W ⊆ saturated F h)
        linarith only [hS, hSmall, hPositive]
      have hIncidents (v : V) : ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        linarith only [hUsed v, hLoadPartial A v, hDegree]
      obtain ⟨p, hp, hpLen, hpF, hpW⟩ := short_dense_route c hc K hK P h hh hexp hV
        F W (x i) (y i) (by simp [W]) (by simp [W]) hIncidents hWcard
      have hpDisjoint (j : I) (hj : j ∈ A) : Disjoint p.edgeSet (q j).edgeSet := by
        apply Set.disjoint_left.mpr
        intro e he hj'
        exact Finset.disjoint_left.mp hpF (List.mem_toFinset.mpr he)
          (Finset.mem_biUnion.mpr ⟨j, hj, List.mem_toFinset.mpr hj'⟩)
      let r := Function.update q i p
      have hSelf : r i = p := Function.update_self i p q
      have hOther (j : I) (hj : j ∈ A) : r j = q j :=
        Function.update_of_ne (show j ≠ i from fun he => hi (he ▸ hj)) p q
      refine ⟨r, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hSelf] using And.intro hp hpLen
        · simpa only [hOther j hj] using hq j hj
      · intro j hj l hl hne
        change j ∈ insert i A at hj
        change l ∈ insert i A at hl
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · have hl' := (Finset.mem_insert.mp hl).resolve_left hne.symm
          simpa only [hSelf, hOther l hl'] using hpDisjoint l hl'
        · rcases Finset.mem_insert.mp hl with rfl | hl'
          · simpa only [hSelf, hOther j hj'] using (hpDisjoint j hj').symm
          · simpa only [hOther j hj', hOther l hl'] using hd hj' hl' hne
      · intro v
        rw [usedEdges_update_insert A i hi q p, endpointLoad_insert A i hi]
        simpa only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_assoc] using
          route_degree_update p hp F h (endpointLoad A x y) hUsed hpW v
  obtain ⟨q, hq, hd, hR⟩ := hBuild univ
  refine ⟨q, fun i => hq i (Finset.mem_univ _), fun i j hij =>
    hd (Finset.mem_univ _) (Finset.mem_univ _) hij, ?_⟩
  intro v
  linarith only [hR v, hLoad v, hDegree]

theorem cutExpansion_delete_bounded_edges {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) [DecidableRel P.Adj] (h b : ℝ) (hexp : CutExpansion P h)
    (F : Finset (Sym2 V)) (hInc : ∀ v, ((incidentEdges F v).card : ℝ) ≤ b) :
    CutExpansion (P.deleteEdges (F : Set (Sym2 V))) (h - b) := by
  intro S
  let H := P.deleteEdges (F : Set (Sym2 V))
  let remove (e : V × V) := s(e.1, e.2) ∈ F
  have hNew : H.interedges S Sᶜ = (P.interedges S Sᶜ).filter (fun e => ¬ remove e) := by
    ext e
    simp [remove, H, SimpleGraph.mem_interedges_iff, SimpleGraph.deleteEdges_adj]
    tauto
  have hRemoved : (((P.interedges S Sᶜ).filter remove).card : ℝ) ≤ b * S.card := by
    calc
      _ ≤ ∑ v ∈ S, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P S F
      _ ≤ ∑ _v ∈ S, b := Finset.sum_le_sum (fun v _ => hInc v)
      _ = _ := by simp [mul_comm]
  have hCount : (((P.interedges S Sᶜ).filter remove).card : ℝ) +
      (H.interedges S Sᶜ).card = (P.interedges S Sᶜ).card := by
    rw [hNew]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := P.interedges S Sᶜ) remove
  have hS : (S.card : ℝ) ≤ Sᶜ.card ∨ (Sᶜ.card : ℝ) ≤ S.card := le_total _ _
  rcases hS with hs | hs
  · rw [min_eq_left hs]
    have hOld := hexp S
    rw [min_eq_left hs] at hOld
    change (h - b) * S.card ≤ (H.interedges S Sᶜ).card
    linarith only [hOld, hCount, hRemoved]
  · have hOld := hexp Sᶜ
    rw [compl_compl, min_eq_left hs] at hOld
    have hFlip : (H.interedges Sᶜ S).card = (H.interedges S Sᶜ).card := by
      letI : Std.Symm H.Adj := H.symm
      exact Rel.card_interedges_comm (r := H.Adj) _ _
    have hNew' : H.interedges Sᶜ S = (P.interedges Sᶜ S).filter (fun e => ¬ remove e) := by
      ext e
      simp [remove, H, SimpleGraph.mem_interedges_iff, SimpleGraph.deleteEdges_adj]
      tauto
    have hCount' : (((P.interedges Sᶜ S).filter remove).card : ℝ) +
        (H.interedges Sᶜ S).card = (P.interedges Sᶜ S).card := by
      rw [hNew']
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := P.interedges Sᶜ S) remove
    have hRemoved' : (((P.interedges Sᶜ S).filter remove).card : ℝ) ≤ b * Sᶜ.card := by
      calc
        _ ≤ ∑ v ∈ Sᶜ, ((incidentEdges F v).card : ℝ) := by
          simpa using (show (((P.interedges Sᶜ Sᶜᶜ).filter remove).card : ℝ) ≤
            ∑ v ∈ Sᶜ, ((incidentEdges F v).card : ℝ) by
            exact_mod_cast deleted_boundary_card_le_incidents P Sᶜ F)
        _ ≤ ∑ _v ∈ Sᶜ, b := Finset.sum_le_sum (fun v _ => hInc v)
        _ = _ := by simp [mul_comm]
    rw [min_eq_right hs]
    change (h - b) * (Sᶜ.card : ℝ) ≤ (H.interedges S Sᶜ).card
    rw [← hFlip]
    linarith only [hOld, hCount', hRemoved']

end
end OAI.ErdosGallai


namespace DenseCycleDecomposition

open Finset SimpleGraph
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] {J : Type} [Fintype J]

def fiber (f : V → J) (j : J) : Finset V := univ.filter (fun v => f v = j)

theorem mem_fiber {f : V → J} {j : J} {v : V} : v ∈ fiber f j ↔ f v = j := by
  simp [fiber]

private theorem fiber_disjoint (f : V → J) {i j : J} (h : i ≠ j) :
    Disjoint (fiber f i) (fiber f j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  exact h ((mem_fiber.mp hi).symm.trans (mem_fiber.mp hj))

variable (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ)

private def cutWeight (A B : Finset V) : ℝ :=
  (G.interedges A B).card - δ * (A.card : ℝ) * B.card

private theorem cutWeight_comm (A B : Finset V) :
    cutWeight G δ A B = cutWeight G δ B A := by
  letI : Std.Symm G.Adj := G.symm
  unfold cutWeight SimpleGraph.interedges
  rw [Rel.card_interedges_comm]
  ring

private theorem cutWeight_union [DecidableEq V] (A B C : Finset V) (hd : Disjoint A B) :
    cutWeight G δ (A ∪ B) C = cutWeight G δ A C + cutWeight G δ B C := by
  have h : G.interedges (A ∪ B) C = G.interedges A C ∪ G.interedges B C := by
    ext e
    simp only [G.mem_interedges_iff, Finset.mem_union]
    tauto
  simp only [cutWeight, h, Finset.card_union_of_disjoint hd,
    Finset.card_union_of_disjoint (G.interedges_disjoint_left hd C), Nat.cast_add]
  ring

private theorem cutWeight_square [DecidableEq V] (A B : Finset V) (h : Disjoint A B) :
    cutWeight G δ (A ∪ B) (A ∪ B) =
    cutWeight G δ A A + cutWeight G δ B B + 2 * cutWeight G δ A B := by
  rw [cutWeight_union G δ A B _ h, cutWeight_comm G δ A (A ∪ B),
    cutWeight_comm G δ B (A ∪ B), cutWeight_union G δ A B A h,
    cutWeight_union G δ A B B h, cutWeight_comm G δ B A]
  ring

private def partitionWeight (f : V → J) : ℝ :=
  ∑ j : J, cutWeight G δ (fiber f j) (fiber f j)

private theorem partitionWeight_difference (f g : V → J) {i j : J} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → fiber f k = fiber g k) :
    partitionWeight G δ g - partitionWeight G δ f =
      cutWeight G δ (fiber g i) (fiber g i) + cutWeight G δ (fiber g j) (fiber g j) -
      (cutWeight G δ (fiber f i) (fiber f i) + cutWeight G δ (fiber f j) (fiber f j)) := by
  unfold partitionWeight
  let rf := fun k => cutWeight G δ (fiber f k) (fiber f k)
  let rg := fun k => cutWeight G δ (fiber g k) (fiber g k)
  have hj : j ∈ (univ : Finset J).erase i := Finset.mem_erase.mpr ⟨hij.symm, mem_univ _⟩
  have hsum (r : J → ℝ) : (∑ k : J, r k) =
      r i + r j + ∑ k ∈ (Finset.univ.erase i).erase j, r k := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ _ hj]
    ring
  change (∑ k, rg k) - (∑ k, rf k) = rg i + rg j - (rf i + rf j)
  rw [hsum rg, hsum rf]
  have he : (∑ k ∈ (Finset.univ.erase i).erase j, rg k) =
      ∑ k ∈ (Finset.univ.erase i).erase j, rf k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    dsimp [rg, rf]
    rw [show fiber f k = fiber g k from h k (mem_erase.mp (mem_erase.mp hk).2).1
      (mem_erase.mp hk).1]
  rw [he]
  ring

private theorem upper_cut_of_max [DecidableEq V] (f : V → J)
    (hMax : ∀ g : V → J, partitionWeight G δ g ≤ partitionWeight G δ f)
    {i j : J} (hij : i ≠ j) : cutWeight G δ (fiber f i) (fiber f j) ≤ 0 := by
  let g (v : V) := if f v = j then i else f v
  have hSame (k) (hki : k ≠ i) (hkj : k ≠ j) : fiber f k = fiber g k := by
    ext v
    simp only [mem_fiber, g]
    split_ifs with hv
    · simp [hv, hki.symm, hkj.symm]
    · rfl
  have hi : fiber g i = fiber f i ∪ fiber f j := by
    ext v
    simp only [mem_fiber, g, Finset.mem_union]
    split_ifs with hv <;> simp [hv]
  have hj : fiber g j = ∅ := by
    ext v
    simp only [mem_fiber, g, Finset.notMem_empty, iff_false]
    split_ifs with hv <;> assumption
  have hDiff := partitionWeight_difference G δ f g hij hSame
  rw [hi, hj, cutWeight_square G δ _ _ (fiber_disjoint f hij)] at hDiff
  have hZero : cutWeight G δ ∅ ∅ = 0 := by simp [cutWeight]
  rw [hZero] at hDiff
  linarith [hMax g]

private theorem lower_cut_of_max [DecidableEq V] (f : V → Option V)
    (hMax : ∀ g : V → Option V, partitionWeight G δ g ≤ partitionWeight G δ f)
    (i : Option V) (A : Finset V) (hA : A ⊆ fiber f i) :
    0 ≤ cutWeight G δ A (fiber f i \ A) := by
  by_cases hi : (fiber f i).Nonempty
  · have hunused : ∃ j : Option V, ∀ v, f v ≠ j := by
      have hcard : (Finset.univ.image f).card < Fintype.card (Option V) := by
        simpa [Fintype.card_option] using Nat.lt_succ_of_le
          (Finset.card_image_le (s := (univ : Finset V)) (f := f))
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show (univ.image f).card < (univ : Finset (Option V)).card by simpa using hcard)
      exact ⟨j, fun v hv => hj (mem_image.mpr ⟨v, mem_univ _, hv⟩)⟩
    obtain ⟨j, hEmpty⟩ := hunused
    obtain ⟨v, hv⟩ := hi
    have hij : i ≠ j := fun he => hEmpty v ((mem_fiber.mp hv).trans he)
    let g (v : V) := if v ∈ A then j else f v
    have hSame (k) (hki : k ≠ i) (hkj : k ≠ j) : fiber f k = fiber g k := by
      ext w
      simp only [mem_fiber, g]
      split_ifs with hw
      · simp [mem_fiber.mp (hA hw), hki.symm, hkj.symm]
      · rfl
    have hgi : fiber g i = fiber f i \ A := by
      ext w
      simp only [mem_fiber, g, Finset.mem_sdiff]
      split_ifs with hw <;> simp [hw, hij.symm]
    have hgj : fiber g j = A := by
      ext w
      simp only [mem_fiber, g]
      split_ifs with hw <;> simp [hw, hEmpty]
    have hfj : fiber f j = ∅ := by
      ext w
      simp [mem_fiber, hEmpty]
    have hunion : A ∪ (fiber f i \ A) = fiber f i := Finset.union_sdiff_of_subset hA
    have hd : Disjoint A (fiber f i \ A) := Finset.disjoint_sdiff
    have hDiff := partitionWeight_difference G δ f g hij hSame
    have hs := (congrArg (fun X => cutWeight G δ X X) hunion.symm).trans
      (cutWeight_square G δ A (fiber f i \ A) hd)
    rw [hgi, hgj, hfj, hs] at hDiff
    have hZero : cutWeight G δ ∅ ∅ = 0 := by simp [cutWeight]
    rw [hZero] at hDiff
    linarith [hMax g]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hi
    have hZero : A = ∅ := Finset.subset_empty.mp (he ▸ hA)
    simp [cutWeight, hZero]

theorem exists_cut_density_partition [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ) :
    ∃ f : V → Option V,
      (∀ i j, i ≠ j → ((G.interedges (fiber f i) (fiber f j)).card : ℝ) ≤
        δ * (fiber f i).card * (fiber f j).card) ∧
      (∀ i A, A ⊆ fiber f i → δ * (A.card : ℝ) * (fiber f i \ A).card ≤
        (G.interedges A (fiber f i \ A)).card) := by
  obtain ⟨f, -, h⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Option V))
    (partitionWeight G δ) ⟨fun _ => none, mem_univ _⟩
  have hMax (g : V → Option V) := h g (mem_univ g)
  refine ⟨f, ?_, ?_⟩
  · intro i j hne
    exact sub_nonpos.mp (upper_cut_of_max G δ f hMax hne)
  · intro i A hs
    exact sub_nonneg.mp (lower_cut_of_max G δ f hMax i A hs)

theorem sum_card_fibers (f : V → J) : ∑ j, (fiber f j).card = Fintype.card V := by
  exact (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := f) (fun _ _ => by simp)).symm

private theorem card_interedges_univ_eq_sum_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : (G.interedges A univ).card = ∑ a ∈ A, G.degree a := by
  unfold SimpleGraph.interedges
  rw [Rel.interedges_eq_biUnion, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.card_map, ← G.card_neighborFinset_eq_degree]
    congr 1
    ext b
    simp
  · intro a _ b _ hne
    unfold Function.onFun
    rw [Finset.disjoint_left]
    rintro p hpA hpB
    obtain ⟨a', _, hA⟩ := Finset.mem_map.mp hpA
    obtain ⟨b', _, hB⟩ := Finset.mem_map.mp hpB
    exact hne (congrArg Prod.fst (hA.trans hB.symm))

theorem partition_fiber_size (G : SimpleGraph V) [DecidableRel G.Adj]
    (c δ : ℝ) (hδ : 0 ≤ δ) (hDegree : ∀ v, c * Fintype.card V ≤ (G.degree v : ℝ))
    (f : V → J)
    (hCut : ∀ i j, i ≠ j → ((G.interedges (fiber f i) (fiber f j)).card : ℝ) ≤
      δ * (fiber f i).card * (fiber f j).card)
    (i : J) (hi : (fiber f i).Nonempty) : (c - δ) * Fintype.card V ≤ (fiber f i).card := by
  let A := fiber f i
  have hFibers : (G.interedges A univ).card = ∑ j, (G.interedges A (fiber f j)).card := by
    have hFib (j : J) : (G.interedges A univ).filter (fun e => f e.2 = j) =
        G.interedges A (fiber f j) := by
      ext e
      simp only [Finset.mem_filter, G.mem_interedges_iff, Finset.mem_univ, mem_fiber]
      tauto
    rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := fun e => f e.2)
      (fun _ _ => by simp)]
    simp_rw [hFib]
  have hcount : ((G.interedges A univ).card : ℝ) ≤
      (A.card : ℝ) ^ 2 + δ * A.card * Fintype.card V := by
    rw [hFibers, Nat.cast_sum]
    have hPoint (j : J) :
        ((G.interedges A (fiber f j)).card : ℝ) ≤
          (if j = i then (A.card : ℝ) ^ 2 else 0) + δ * A.card * (fiber f j).card := by
      by_cases hji : j = i
      · subst j
        have hc : ((G.interedges A A).card : ℝ) ≤ (A.card : ℝ) ^ 2 := by
          rw [pow_two]
          exact_mod_cast G.card_interedges_le_mul A A
        simp only [if_true]
        exact hc.trans (le_add_of_nonneg_right (by positivity))
      · simpa [hji, A] using hCut i j (fun h => hji h.symm)
    refine (Finset.sum_le_sum (fun j _ => hPoint j)).trans_eq ?_
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum, ← Nat.cast_sum,
      sum_card_fibers]
  have hDegrees : (A.card : ℝ) * (c * Fintype.card V) ≤ (G.interedges A univ).card := by
    rw [card_interedges_univ_eq_sum_degree G, Nat.cast_sum]
    simpa using Finset.sum_le_sum (s := A) (fun v _ => hDegree v)
  have hA : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hi
  have hFactor : (A.card : ℝ) * ((c - δ) * Fintype.card V) ≤ (A.card : ℝ) * A.card := by
    nlinarith only [hDegrees, hcount]
  exact (mul_le_mul_iff_right₀ hA).mp hFactor

abbrev activeFibers (f : V → J) := {j : J // (fiber f j).Nonempty}

noncomputable instance (f : V → J) : Fintype (activeFibers f) := Fintype.ofFinite _

theorem active_fibers_card (f : V → J) (a : ℝ) (ha : 0 < a)
    (hV : 0 < Fintype.card V)
    (hLower : ∀ j : activeFibers f, a * Fintype.card V ≤ (fiber f j.val).card) :
    (Fintype.card (activeFibers f) : ℝ) ≤ 1 / a := by
  have hSum : (∑ j : activeFibers f, (fiber f j.val).card) ≤ Fintype.card V := by
    calc
      _ = ∑ j ∈ Finset.univ.filter (fun j => (fiber f j).Nonempty), (fiber f j).card :=
        (Finset.sum_subtype (p := fun j : J => (fiber f j).Nonempty) _
          (fun _ => by simp) (fun j => (fiber f j).card)).symm
      _ ≤ ∑ j : J, (fiber f j).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
      _ = _ := sum_card_fibers f
  have hSumR : (∑ j : activeFibers f, ((fiber f j.val).card : ℝ)) ≤ Fintype.card V := by
    exact_mod_cast hSum
  have hLowerSum : (Fintype.card (activeFibers f) : ℝ) * (a * Fintype.card V) ≤
      ∑ j : activeFibers f, ((fiber f j.val).card : ℝ) := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (activeFibers f))) (fun j _ => hLower j)
  have hVR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hV
  apply (le_div_iff₀ ha).mpr
  apply (mul_le_mul_iff_left₀ hVR).mp
  nlinarith only [hSumR, hLowerSum]

end
end DenseCycleDecomposition

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

theorem induced_cutExpansion_of_density {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ S, S ⊆ A → δ * (S.card : ℝ) * (A \ S).card ≤ (G.interedges S (A \ S)).card) :
    CutExpansion (G.induce (A : Set V)) (δ * A.card / 2) := by
  apply cutExpansion_induce G A
  intro S hS
  have hSumN : S.card + (A \ S).card = A.card := by
    rw [Finset.card_sdiff_of_subset hS]
    have hle := Finset.card_le_card hS
    omega
  have hSum : (S.card : ℝ) + (A \ S).card = A.card := by exact_mod_cast hSumN
  rcases le_total (S.card : ℝ) ((A \ S).card : ℝ) with h | h
  · rw [min_eq_left h]
    have hLarge : δ * A.card / 2 ≤ δ * (A \ S).card := by
      have := mul_le_mul_of_nonneg_left (show (A.card : ℝ) / 2 ≤ (A \ S).card by linarith) hδ
      linarith
    calc
      _ ≤ (δ * (A \ S).card) * S.card := mul_le_mul_of_nonneg_right hLarge (by positivity)
      _ = δ * (S.card : ℝ) * (A \ S).card := by ring
      _ ≤ _ := hd S hS
  · rw [min_eq_right h]
    have hLarge : δ * A.card / 2 ≤ δ * S.card := by
      have := mul_le_mul_of_nonneg_left (show (A.card : ℝ) / 2 ≤ S.card by linarith) hδ
      linarith
    exact (mul_le_mul_of_nonneg_right hLarge (by positivity)).trans (hd S hS)

end
end OAI.ErdosGallai


namespace DenseCycleDecomposition

open Finset SimpleGraph
open scoped Classical
noncomputable section

theorem cut_long_alternating_path {V : Type} {G : SimpleGraph V}
    (side : V → Bool) (hCross : ∀ ⦃v w⦄, G.Adj v w → side v ≠ side w)
    (n : ℕ) {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hn : p.length = n) (W : Finset V)
    (hLength : 2 * W.card + 1 < p.length) :
    ∃ (x y : V) (l : G.Walk a x) (h : G.Adj x y) (r : G.Walk y b),
      p = l.append (Walk.cons h r) ∧ side x = side a ∧ x ∉ W ∧ y ∉ W := by
  induction n using Nat.strong_induction_on generalizing a b W with
  | h n ih =>
    cases p with
    | nil => simp at hLength
    | @cons a b c hab p =>
      by_cases hFresh : a ∉ W ∧ b ∉ W
      · exact ⟨a, b, .nil, hab, p, rfl, rfl, hFresh⟩
      cases p with
      | nil => simp at hLength
      | @cons b d c hbd q =>
        let W' := W \ {a, b}
        have hW : W'.card < W.card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩)
          intro h
          by_cases ha : a ∈ W
          · have : a ∈ W' := h.symm ▸ ha
            simp [W'] at this
          · have hb : b ∈ W := by by_contra hb; exact hFresh ⟨ha, hb⟩
            have : b ∈ W' := h.symm ▸ hb
            simp [W'] at this
        have hPath := (Walk.cons_isPath_iff hab _).mp hp
        have hPath' := (Walk.cons_isPath_iff hbd q).mp hPath.1
        have hqLen : 2 * W'.card + 1 < q.length := by
          simp only [Walk.length_cons] at hLength
          omega
        have hParity : side d = side a := by
          have h₁ := hCross hab
          have h₂ := hCross hbd
          cases he : side a <;> cases hf : side b <;> cases hg : side d <;> simp_all
        have hSmall : q.length < n := by
          simp only [Walk.length_cons] at hn
          omega
        obtain ⟨x, y, l, hxy, r, hr, hxSide, hx, hy⟩ :=
          ih q.length hSmall q hPath'.1 rfl W' hqLen
        have hxq : x ∈ q.support := by
          rw [hr]
          exact Walk.dart_fst_mem_support_of_mem_darts _
            (d := ⟨(x, y), hxy⟩) (by simp [Walk.darts_append, Walk.darts_cons])
        have hyq : y ∈ q.support := by
          rw [hr]
          exact Walk.dart_snd_mem_support_of_mem_darts _
            (d := ⟨(x, y), hxy⟩) (by simp [Walk.darts_append, Walk.darts_cons])
        have haNot : a ∉ q.support := fun ha => hPath.2 (List.mem_cons_of_mem _ ha)
        have hbNot : b ∉ q.support := hPath'.2
        have hxW : x ∉ W := by
          intro h
          apply hx
          simp only [W', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨h, fun hs => hs.elim (fun he => haNot (he ▸ hxq)) (fun he => hbNot (he ▸ hxq))⟩
        have hyW : y ∉ W := by
          intro h
          apply hy
          simp only [W', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨h, fun hs => hs.elim (fun he => haNot (he ▸ hyq)) (fun he => hbNot (he ▸ hyq))⟩
        refine ⟨x, y, .cons hab (.cons hbd l), hxy, r, ?_, hxSide.trans hParity, hxW, hyW⟩
        rw [hr]
        rfl

end
end DenseCycleDecomposition

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

theorem bounded_cut_edge_choice {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (side : V → Bool)
    (hCross : ∀ ⦃a b⦄, G.Adj a b → side a ≠ side b)
    (a b : I → V) (p : ∀ i, G.Walk (a i) (b i))
    (hPath : ∀ i, (p i).IsPath) (n B : ℕ) (hB : 0 < B)
    (U : Finset I) (hU : U.card ≤ n)
    (hLong : ∀ i ∈ U, 2 * (2 * n / B) + 1 < (p i).length) :
    ∃ F : Finset (Sym2 V),
      F.card ≤ U.card ∧ (∀ v, (incidentEdges F v).card ≤ B) ∧
      ∀ i ∈ U, ∃ (x y : V) (l : G.Walk (a i) x) (h : G.Adj x y) (r : G.Walk y (b i)),
        p i = l.append (.cons h r) ∧ side x = side (a i) ∧ s(x, y) ∈ F := by
  induction U using Finset.induction_on with
  | empty =>
    refine ⟨∅, by simp, fun v => ?_, by simp⟩
    simp [incidentEdges]
  | @insert i U hi ih =>
    have hSimple : U.card ≤ n := (Finset.card_le_card (Finset.subset_insert i U)).trans hU
    obtain ⟨F, hF, hLoad, hChosen⟩ := ih hSimple
      (fun j hj => hLong j (Finset.mem_insert_of_mem hj))
    let W : Finset V := Finset.univ.filter (fun v => B ≤ (incidentEdges F v).card)
    have hW : W.card ≤ 2 * n / B := by
      apply (Nat.le_div_iff_mul_le hB).mpr
      calc
        _ = ∑ _v ∈ W, B := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ W, (incidentEdges F v).card :=
          Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
        _ ≤ ∑ v : V, (incidentEdges F v).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W) (by intros; positivity)
        _ ≤ 2 * F.card := incidentEdges_sum_le F
        _ ≤ 2 * n := Nat.mul_le_mul_left _ (hF.trans hSimple)
    have hLen : 2 * W.card + 1 < (p i).length := by
      have h := hLong i (Finset.mem_insert_self _ _)
      omega
    obtain ⟨x, y, l, hxy, r, hp, hSide, hx, hy⟩ :=
      DenseCycleDecomposition.cut_long_alternating_path side hCross _ (p i) (hPath i) rfl W hLen
    let E : Finset (Sym2 V) := {s(x, y)}
    have hE : E.card = 1 := by simp [E]
    refine ⟨F ∪ E, ?_, ?_, ?_⟩
    · have hUnion := Finset.card_union_le F E
      rw [Finset.card_insert_of_notMem hi]
      omega
    · intro v
      have hCard := incidentEdges_union_card_le F E v
      by_cases hv : v ∈ s(x, y)
      · have hV : v ∉ W := by
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact hx
          · exact hy
        have hOld : (incidentEdges F v).card < B := by
          by_contra! hn
          exact hV (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
        have hSingleton : (incidentEdges E v).card ≤ 1 :=
          (Finset.card_filter_le _ _).trans hE.le
        omega
      · have hZero : incidentEdges E v = ∅ := by simp [E, incidentEdges, hv]
        rw [incidentEdges_union, hZero, Finset.union_empty]
        exact hLoad v
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact ⟨x, y, l, hxy, r, hp, hSide, Finset.mem_union_right _ (by simp [E])⟩
      · obtain ⟨u, v, s, h, t, hs, hsSide, hEdge⟩ := hChosen j hj'
        exact ⟨u, v, s, h, t, hs, hsSide, Finset.mem_union_left _ hEdge⟩

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

structure SameSidePath {V : Type} (G : SimpleGraph V) (side : V → Bool) where
  start : V
  finish : V
  walk : G.Walk start finish
  path : walk.IsPath
  same : side start = side finish

def SameSidePath.nil {V : Type} (G : SimpleGraph V) (side : V → Bool) (v : V) :
    SameSidePath G side := ⟨v, v, .nil, Walk.IsPath.nil, rfl⟩

def SameSidePath.endpoint {V : Type} {G : SimpleGraph V} {side : V → Bool}
    (p : SameSidePath G side) (v : V) : Prop :=
  0 < p.walk.length ∧ (p.start = v ∨ p.finish = v)

theorem SameSidePath.endpoint_mem_support {V : Type} {G : SimpleGraph V} {side : V → Bool}
    {p : SameSidePath G side} {v : V} (h : p.endpoint v) : v ∈ p.walk.support := by
  rcases h.2 with h | h
  · exact h ▸ p.walk.start_mem_support
  · exact h ▸ p.walk.end_mem_support

structure CrossPathPieces {V : Type} [DecidableEq V] {G : SimpleGraph V} (side : V → Bool)
    (p : PositiveSimplePath G) (F : Finset (Sym2 V)) (T : ℕ) where
  left : SameSidePath G side
  right : SameSidePath G side
  singles : Finset (Sym2 V)
  cover : left.walk.edgeSet ∪ right.walk.edgeSet ∪ (singles : Set (Sym2 V)) = p.walk.edgeSet
  disjoint : Disjoint left.walk.edgeSet right.walk.edgeSet
  singles_disjoint : Disjoint (left.walk.edgeSet ∪ right.walk.edgeSet) (singles : Set (Sym2 V))
  count : singles.card ≤ T
  no_repeated_end (v : V) : left.endpoint v → right.endpoint v → False
  ends (v : V) : left.endpoint v ∨ right.endpoint v →
    p.start = v ∨ p.finish = v ∨ ∃ e ∈ F, e ∈ p.walk.edgeSet ∧ v ∈ e

noncomputable def pieces_of_same_side {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (side : V → Bool) (p : PositiveSimplePath G) (F : Finset (Sym2 V)) (T : ℕ)
    (hs : side p.start = side p.finish) : CrossPathPieces side p F T where
  left := ⟨p.start, p.finish, p.walk, p.isPath, hs⟩
  right := .nil G side p.finish
  singles := ∅
  cover := by simp [SameSidePath.nil]
  disjoint := by simp [SameSidePath.nil]
  singles_disjoint := by simp
  count := by simp
  no_repeated_end v _ hv := by simp [SameSidePath.endpoint, SameSidePath.nil] at hv
  ends v hv := by
    simp only [SameSidePath.endpoint, SameSidePath.nil, Walk.length_nil, lt_irrefl, false_and,
      or_false] at hv
    exact hv.2.imp_right Or.inl

noncomputable def pieces_of_short_path {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (side : V → Bool) (p : PositiveSimplePath G) (F : Finset (Sym2 V)) (T : ℕ)
    (hs : p.walk.length ≤ T) : CrossPathPieces side p F T where
  left := .nil G side p.start
  right := .nil G side p.finish
  singles := p.walk.edges.toFinset
  cover := by
    simp only [SameSidePath.nil, Walk.edgeSet_nil, Set.empty_union]
    ext e
    simp [Walk.mem_edgeSet]
  disjoint := by simp [SameSidePath.nil]
  singles_disjoint := by simp [SameSidePath.nil]
  count := by
    simpa only [Walk.length_edges] using (List.toFinset_card_le p.walk.edges).trans
      (by simpa only [Walk.length_edges] using hs)
  no_repeated_end v hv _ := by simp [SameSidePath.endpoint, SameSidePath.nil] at hv
  ends v hv := by simp [SameSidePath.endpoint, SameSidePath.nil] at hv

noncomputable def pieces_of_cut {V : Type} [DecidableEq V] {G : SimpleGraph V}
    (side : V → Bool) (p : PositiveSimplePath G) (F : Finset (Sym2 V)) (T : ℕ) (hT : 1 ≤ T)
    {x y : V} (l : G.Walk p.start x) (h : G.Adj x y) (r : G.Walk y p.finish)
    (hs : p.walk = l.append (.cons h r)) (hl : side p.start = side x)
    (hr : side y = side p.finish) (he : s(x, y) ∈ F) : CrossPathPieces side p F T := by
  have hPath := hs ▸ p.isPath
  have hTrail := (Walk.isTrail_append l (.cons h r)).mp hPath.isTrail
  have hrPath := (Walk.cons_isPath_iff h r).mp hPath.of_append_right
  have hLDisj : Disjoint l.edgeSet (Walk.cons h r).edgeSet := by
    exact Set.disjoint_left.mpr (List.disjoint_left.mp hTrail.2.2)
  have hCutDisj : s(x, y) ∉ r.edgeSet := (Walk.isTrail_cons h r).mp hTrail.2.1 |>.2
  have hEdge : s(x, y) ∈ p.walk.edgeSet := by
    rw [hs, Walk.edgeSet_append, Walk.edgeSet_cons]
    simp
  refine {
    left := ⟨p.start, x, l, hPath.of_append_left, hl⟩
    right := ⟨y, p.finish, r, hrPath.1, hr⟩
    singles := {s(x, y)}
    cover := ?_
    disjoint := ?_
    singles_disjoint := ?_
    count := by simpa
    no_repeated_end := ?_
    ends := ?_
  }
  · rw [hs, Walk.edgeSet_append, Walk.edgeSet_cons, Finset.coe_singleton]
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  · apply hLDisj.mono_right
    rw [Walk.edgeSet_cons]
    exact Set.subset_insert _ _
  · rw [Finset.coe_singleton, Set.disjoint_left]
    intro e h₁ h₂
    have hei : e = s(x, y) := h₂
    subst e
    rcases h₁ with hl | hr
    · exact Set.disjoint_left.mp hLDisj hl (by simp [Walk.edgeSet_cons])
    · exact hCutDisj hr
  · intro v hv₁ hv₂
    have hd := hPath.disjoint_support_of_append (q := .cons h r) (by simp)
    rw [Walk.tail_cons] at hd
    exact List.disjoint_left.mp hd (SameSidePath.endpoint_mem_support hv₁)
      (by simpa using SameSidePath.endpoint_mem_support hv₂)
  · intro v hv
    change (0 < l.length ∧ (p.start = v ∨ x = v)) ∨
      (0 < r.length ∧ (y = v ∨ p.finish = v)) at hv
    rcases hv with ⟨-, h₁ | h₁⟩ | ⟨-, h₂ | h₂⟩
    · exact Or.inl h₁
    · exact Or.inr (Or.inr ⟨_, he, hEdge, Sym2.mem_iff.mpr (Or.inl h₁.symm)⟩)
    · exact Or.inr (Or.inr ⟨_, he, hEdge, Sym2.mem_iff.mpr (Or.inr h₂.symm)⟩)
    · exact Or.inr (Or.inl h₂)

theorem bounded_crossing_path_pieces {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (side : V → Bool)
    (hCross : ∀ ⦃a b⦄, G.Adj a b → side a ≠ side b)
    (P : I → PositiveSimplePath G) (n B : ℕ) (hB : 0 < B) (hI : Fintype.card I ≤ n) :
    ∃ F : Finset (Sym2 V), (∀ v, (incidentEdges F v).card ≤ B) ∧
      Nonempty (∀ i, CrossPathPieces side (P i) F (2 * (2 * n / B) + 1)) := by
  let T := 2 * (2 * n / B) + 1
  let U : Finset I := univ.filter (fun i => side (P i).start ≠ side (P i).finish ∧ T < (P i).walk.length)
  obtain ⟨F, -, hLoad, hSelect⟩ := bounded_cut_edge_choice G side @hCross
    (fun i => (P i).start) (fun i => (P i).finish) (fun i => (P i).walk) (fun i => (P i).isPath)
    n B hB U (U.card_le_univ.trans hI) (fun i hi => (Finset.mem_filter.mp hi).2.2)
  have hNonempty (i : I) : Nonempty (CrossPathPieces side (P i) F T) := by
    by_cases hside : side (P i).start = side (P i).finish
    · exact ⟨pieces_of_same_side side (P i) F T hside⟩
    by_cases hshort : (P i).walk.length ≤ T
    · exact ⟨pieces_of_short_path side (P i) F T hshort⟩
    have hUi : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hside, lt_of_not_ge hshort⟩
    obtain ⟨x, y, l, h, r, heq, hx, he⟩ := hSelect i hUi
    have hy : side y = side (P i).finish := by
      have hxy := hCross h
      cases hs : side (P i).start <;> cases ht : side (P i).finish <;> cases hy : side y <;> simp_all
    exact ⟨pieces_of_cut side (P i) F T (by omega) l h r heq hx.symm hy he⟩
  exact ⟨F, hLoad, ⟨fun i => Classical.choice (hNonempty i)⟩⟩

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

variable {V I : Type} [DecidableEq V] [Fintype I]
variable {G : SimpleGraph V} {side : V → Bool} {P : I → PositiveSimplePath G}
variable {F : Finset (Sym2 V)} {T : ℕ}

def CrossPathPieces.part (pieces : ∀ i, CrossPathPieces side (P i) F T) (i : I × Bool) :
    SameSidePath G side :=
  if i.2 then (pieces i.1).right else (pieces i.1).left

abbrev CrossDemandIndex (pieces : ∀ i, CrossPathPieces side (P i) F T) :=
    {i : I × Bool // 0 < (CrossPathPieces.part pieces i).walk.length}

theorem crossDemandIndex_card (pieces : ∀ i, CrossPathPieces side (P i) F T) :
    Fintype.card (CrossDemandIndex pieces) ≤ 2 * Fintype.card I := by
  have hs := Fintype.card_le_of_injective
    (fun i : CrossDemandIndex pieces => i.val) Subtype.val_injective
  simpa [Fintype.card_prod, Nat.mul_comm] using hs

theorem crossing_demand_endpoint_load [Fintype V]
    (pieces : ∀ i, CrossPathPieces side (P i) F T)
    (hDisjoint : Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet))
    (hBound : ∀ v, (Finset.univ.filter (fun i : I => (P i).start = v ∨ (P i).finish = v)).card ≤ 2)
    (v : V) :
    (endpointLoad (Finset.univ : Finset (CrossDemandIndex pieces))
      (fun i => (CrossPathPieces.part pieces i.val).start)
      (fun i => (CrossPathPieces.part pieces i.val).finish) v) ≤ 2 + (incidentEdges F v).card := by
  let A : Finset I := univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)
  let C : Finset I := univ.filter (fun i => ∃ e ∈ incidentEdges F v, e ∈ (P i).walk.edgeSet)
  have hC : C.card ≤ (incidentEdges F v).card := by
    have h (i : I) (hi : i ∈ C) : ∃ e ∈ incidentEdges F v, e ∈ (P i).walk.edgeSet :=
      (Finset.mem_filter.mp hi).2
    let chooseEdge (i : I) : Sym2 V :=
      if hi : i ∈ C then Classical.choose (h i hi) else s(v, v)
    have hmem (i : I) (hi : i ∈ C) :
        chooseEdge i ∈ incidentEdges F v ∧ chooseEdge i ∈ (P i).walk.edgeSet := by
      simpa [chooseEdge, hi] using Classical.choose_spec (h i hi)
    apply Finset.card_le_card_of_injOn chooseEdge
    · intro i hi
      exact (hmem i hi).1
    · intro i hi j hj hEq
      by_contra! hne
      exact Set.disjoint_left.mp (hDisjoint hne) (hmem i hi).2 (hEq.symm ▸ (hmem j hj).2)
  let U := (Finset.univ : Finset (CrossDemandIndex pieces)).filter
    (fun i => (CrossPathPieces.part pieces i.val).start = v ∨
      (CrossPathPieces.part pieces i.val).finish = v)
  have hEndpoint (i : CrossDemandIndex pieces) (hi : i ∈ U) :
      (CrossPathPieces.part pieces i.val).endpoint v := ⟨i.property, (Finset.mem_filter.mp hi).2⟩
  have hU : U.card ≤ (A ∪ C).card := by
    apply Finset.card_le_card_of_injOn (fun i : CrossDemandIndex pieces => i.val.1)
    · intro i hi
      have hChoice : (pieces i.val.1).left.endpoint v ∨ (pieces i.val.1).right.endpoint v := by
        have h := hEndpoint i hi
        cases hb : i.val.2 with
        | false => exact Or.inl (by simpa [CrossPathPieces.part, hb] using h)
        | true => exact Or.inr (by simpa [CrossPathPieces.part, hb] using h)
      rcases (pieces i.val.1).ends v hChoice with hs | hf | ⟨e, he, hep, hve⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hf⟩)
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, Finset.mem_filter.mpr ⟨he, hve⟩, hep⟩
    · intro i hi j hj hij
      change i.val.1 = j.val.1 at hij
      apply Subtype.ext
      apply Prod.ext hij
      have h₁ := hEndpoint i hi
      have h₂ := hEndpoint j hj
      cases hi' : i.val.2 <;> cases hj' : j.val.2
      · rfl
      · exact False.elim ((pieces i.val.1).no_repeated_end v
          (by simpa [CrossPathPieces.part, hi'] using h₁)
          (by rw [hij]; simpa [CrossPathPieces.part, hj'] using h₂))
      · exact False.elim ((pieces i.val.1).no_repeated_end v
          (by rw [hij]; simpa [CrossPathPieces.part, hj'] using h₂)
          (by simpa [CrossPathPieces.part, hi'] using h₁))
      · rfl
  have hA : A.card ≤ 2 := hBound v
  have hUnion := Finset.card_union_le A C
  change U.card ≤ _
  omega

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

variable {V J : Type} [DecidableEq V] [LinearOrder J]

def interPartGraph (G : SimpleGraph V) (f : V → J) (i j : J) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ i < j ∧
    ((f a = i ∧ f b = j) ∨ (f a = j ∧ f b = i))
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.1, h.2.2.elim
    (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨by intro a h; exact G.irrefl h.1⟩

theorem interPartGraph_le (G : SimpleGraph V) (f : V → J) (i j : J) :
    interPartGraph G f i j ≤ G := fun _ _ h => h.1

theorem interPartGraph_distinct (G : SimpleGraph V) (f : V → J) (p : J × J) {a b : V}
    (h : (interPartGraph G f p.1 p.2).Adj a b) : f a ≠ f b := by
  rcases h.2.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]; exact h.2.1.ne
  · rw [ha, hb]; exact h.2.1.ne'

theorem interPartGraph_disjoint (G : SimpleGraph V) (f : V → J) :
    Pairwise (fun p q : J × J =>
      Disjoint (interPartGraph G f p.1 p.2).edgeSet (interPartGraph G f q.1 q.2).edgeSet) := by
  intro p q hne
  rw [Set.disjoint_left]
  intro e hp hq
  induction e using Sym2.ind with
  | _ a b =>
    have hp' : (interPartGraph G f p.1 p.2).Adj a b := hp
    have hq' : (interPartGraph G f q.1 q.2).Adj a b := hq
    rcases hp'.2.2 with ⟨hpa, hpb⟩ | ⟨hpa, hpb⟩ <;>
      rcases hq'.2.2 with ⟨hqa, hqb⟩ | ⟨hqa, hqb⟩
    · exact hne (Prod.ext (hpa.symm.trans hqa) (hpb.symm.trans hqb))
    · have h₁ := hp'.2.1
      have h₂ := hq'.2.1
      rw [← hpa, ← hpb] at h₁
      rw [← hqb, ← hqa] at h₂
      exact h₁.not_gt h₂
    · have h₁ := hp'.2.1
      have h₂ := hq'.2.1
      rw [← hpb, ← hpa] at h₁
      rw [← hqa, ← hqb] at h₂
      exact h₁.not_gt h₂
    · exact hne (Prod.ext (hpb.symm.trans hqb) (hpa.symm.trans hqa))

theorem edge_crosses_some_parts (G : SimpleGraph V) (f : V → J) {a b : V}
    (h : G.Adj a b) (hf : f a ≠ f b) :
    ∃ p : J × J, s(a, b) ∈ (interPartGraph G f p.1 p.2).edgeSet := by
  rcases lt_or_gt_of_ne hf with hab | hab
  · exact ⟨(f a, f b), ⟨h, hab, Or.inl ⟨rfl, rfl⟩⟩⟩
  · exact ⟨(f b, f a), ⟨h, hab, Or.inr ⟨rfl, rfl⟩⟩⟩

private def interPartSide (f : V → J) (i : J) (v : V) : Bool := decide (f v = i)

private theorem interPartSide_crossing (G : SimpleGraph V) (f : V → J) (p : J × J) {a b : V}
    (h : (interPartGraph G f p.1 p.2).Adj a b) :
    interPartSide f p.1 a ≠ interPartSide f p.1 b := by
  rcases h.2.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [interPartSide, ha, hb, h.2.1.ne']
  · simp [interPartSide, ha, hb, h.2.1.ne']

theorem interPartWalk_same_color (G : SimpleGraph V) (f : V → J) (p : J × J)
    {a b : V} (q : (interPartGraph G f p.1 p.2).Walk a b)
    (hq : 0 < q.length) (hs : interPartSide f p.1 a = interPartSide f p.1 b) : f a = f b := by
  have hn : ¬ q.Nil := fun he => (Nat.ne_of_gt hq) (Walk.nil_iff_length_eq.mp he)
  have ha := (q.adj_snd hn).2.2
  have hb := (q.adj_penultimate hn).2.2
  have hi : p.1 < p.2 := (q.adj_snd hn).2.1
  rcases ha with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rcases hb with ⟨-, hb⟩ | ⟨-, hb⟩
  · simp [interPartSide, ha, hb, hi.ne'] at hs
  · exact ha.trans hb.symm
  · exact ha.trans hb.symm
  · simp [interPartSide, ha, hb, hi.ne'] at hs

variable [Fintype V]

structure CrossGroup (G : SimpleGraph V) (f : V → J) (p : J × J) (B : ℕ) where
  k : ℕ
  paths : Fin k → PositiveSimplePath (interPartGraph G f p.1 p.2)
  pathDisjoint : Pairwise (fun i j => Disjoint (paths i).walk.edgeSet (paths j).walk.edgeSet)
  pathCover : (⋃ i, (paths i).walk.edgeSet) = (interPartGraph G f p.1 p.2).edgeSet
  oldLoad : ∀ v : V, (univ.filter (fun i => (paths i).start = v ∨ (paths i).finish = v)).card ≤ 2
  numPaths : k ≤ Fintype.card V
  cutEdges : Finset (Sym2 V)
  cutLoad : ∀ v, (incidentEdges cutEdges v).card ≤ B
  fragments : ∀ i, CrossPathPieces (interPartSide f p.1) (paths i) cutEdges
    (2 * (2 * Fintype.card V / B) + 1)

noncomputable def crossGroup (G : SimpleGraph V) (f : V → J) (p : J × J) (B : ℕ)
    (hB : 0 < B) : CrossGroup G f p B := by
  let H := interPartGraph G f p.1 p.2
  let ex := endpoint_path_partition H
  let k := Classical.choose ex
  let paths := Classical.choose (Classical.choose_spec ex)
  have hpaths := Classical.choose_spec (Classical.choose_spec ex)
  let cutPlan := bounded_crossing_path_pieces H (interPartSide f p.1)
    (fun _ _ h => interPartSide_crossing G f p h) paths
    (Fintype.card V) B hB (by simpa using hpaths.2.2.2)
  let F := Classical.choose cutPlan
  have hF := Classical.choose_spec cutPlan
  refine ⟨k, paths, hpaths.1, hpaths.2.1, ?_, hpaths.2.2.2, F, hF.1, Classical.choice hF.2⟩
  intro v
  convert hpaths.2.2.1 v using 2
  ext i
  simp [paths]

abbrev CrossGroup.Demands {G : SimpleGraph V} {f : V → J} {p : J × J} {B : ℕ}
    (C : CrossGroup G f p B) := CrossDemandIndex C.fragments

def CrossGroup.demand {G : SimpleGraph V} {f : V → J} {p : J × J} {B : ℕ}
    (C : CrossGroup G f p B) (i : C.Demands) :=
  CrossPathPieces.part C.fragments i.val

theorem CrossGroup.demand_false {G : SimpleGraph V} {f : V → J} {p : J × J} {B : ℕ}
    (C : CrossGroup G f p B) (i : C.Demands) (hi : i.val.2 = false) :
    C.demand i = (C.fragments i.val.1).left := by
  unfold CrossGroup.demand CrossPathPieces.part
  rw [hi]
  rfl

theorem CrossGroup.demand_true {G : SimpleGraph V} {f : V → J} {p : J × J} {B : ℕ}
    (C : CrossGroup G f p B) (i : C.Demands) (hi : i.val.2 = true) :
    C.demand i = (C.fragments i.val.1).right := by
  unfold CrossGroup.demand CrossPathPieces.part
  rw [hi]
  rfl

theorem CrossGroup.same_color {G : SimpleGraph V} {f : V → J} {p : J × J} {B : ℕ}
    (C : CrossGroup G f p B) (i : C.Demands) : f (C.demand i).start = f (C.demand i).finish :=
  interPartWalk_same_color G f p (C.demand i).walk i.property (C.demand i).same

theorem CrossGroup.demandCount {G : SimpleGraph V} {f : V → J} {p : J × J} {B : ℕ}
    (C : CrossGroup G f p B) : Fintype.card C.Demands ≤ 2 * Fintype.card V :=
  (crossDemandIndex_card C.fragments).trans (Nat.mul_le_mul_left _ (by simpa using C.numPaths))

theorem CrossGroup.demandLoad {G : SimpleGraph V} {f : V → J} {p : J × J} {B : ℕ}
    (C : CrossGroup G f p B) (v : V) :
    endpointLoad univ (fun i : C.Demands => (C.demand i).start)
      (fun i : C.Demands => (C.demand i).finish) v ≤ 2 + B :=
  (crossing_demand_endpoint_load C.fragments C.pathDisjoint C.oldLoad v).trans
    (Nat.add_le_add_left (C.cutLoad v) _)

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph
open scoped Classical
noncomputable section

variable {V J : Type} [Fintype V] [DecidableEq V] [LinearOrder J] [Fintype J]
variable {G : SimpleGraph V} {f : V → J} {B : ℕ}

abbrev CrossGroup.Singles {p : J × J} (C : CrossGroup G f p B) :=
  (i : Fin C.k) × ↥((C.fragments i).singles)

theorem CrossGroup.demand_subset {p : J × J} (C : CrossGroup G f p B) (i : C.Demands) :
    (C.demand i).walk.edgeSet ⊆ (C.paths i.val.1).walk.edgeSet := by
  rw [← (C.fragments i.val.1).cover]
  cases h : i.val.2
  · rw [C.demand_false i h]
    exact fun _ he => Or.inl (Or.inl he)
  · rw [C.demand_true i h]
    exact fun _ he => Or.inl (Or.inr he)

theorem CrossGroup.single_subset {p : J × J} (C : CrossGroup G f p B) (i : C.Singles) :
    i.2.val ∈ (C.paths i.1).walk.edgeSet := by
  rw [← (C.fragments i.1).cover]
  exact Or.inr i.2.property

theorem CrossGroup.singlesCount {p : J × J} (C : CrossGroup G f p B) :
    Fintype.card C.Singles ≤ Fintype.card V * (2 * (2 * Fintype.card V / B) + 1) := by
  let T := 2 * (2 * Fintype.card V / B) + 1
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : Fin C.k, T := Finset.sum_le_sum (fun i _ => by
      simpa [T] using (C.fragments i).count)
    _ = C.k * T := by simp
    _ ≤ _ := Nat.mul_le_mul_right T C.numPaths

theorem CrossGroup.demandsDisjoint {p : J × J} (C : CrossGroup G f p B) :
    Pairwise (fun i j : C.Demands => Disjoint (C.demand i).walk.edgeSet (C.demand j).walk.edgeSet) := by
  intro i j hne
  by_cases hEq : i.val.1 = j.val.1
  · cases hi : i.val.2 <;> cases hj : j.val.2
    · exact False.elim (hne (Subtype.ext (Prod.ext hEq (hi.trans hj.symm))))
    · rw [C.demand_false i hi, C.demand_true j hj, ← hEq]
      exact (C.fragments i.val.1).disjoint
    · rw [C.demand_true i hi, C.demand_false j hj, ← hEq]
      exact (C.fragments i.val.1).disjoint.symm
    · exact False.elim (hne (Subtype.ext (Prod.ext hEq (hi.trans hj.symm))))
  · exact (C.pathDisjoint hEq).mono (C.demand_subset i) (C.demand_subset j)

theorem CrossGroup.single_ne {p : J × J} (C : CrossGroup G f p B) :
    Function.Injective (fun i : C.Singles => i.2.val) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  change x.val = y.val at h
  by_cases hEq : i = j
  · subst j
    have h' : x = y := Subtype.ext h
    subst y
    rfl
  · exact False.elim (Set.disjoint_left.mp (C.pathDisjoint hEq) (C.single_subset ⟨i, x⟩)
      (h.symm ▸ C.single_subset ⟨j, y⟩))

theorem CrossGroup.demand_single_disjoint {p : J × J} (C : CrossGroup G f p B)
    (i : C.Demands) (j : C.Singles) : j.2.val ∉ (C.demand i).walk.edgeSet := by
  intro he
  by_cases hEq : i.val.1 = j.1
  · have hi : j.2.val ∈ (C.fragments j.1).left.walk.edgeSet ∪ (C.fragments j.1).right.walk.edgeSet := by
      cases h : i.val.2
      · rw [C.demand_false i h, hEq] at he
        exact Or.inl he
      · rw [C.demand_true i h, hEq] at he
        exact Or.inr he
    exact Set.disjoint_left.mp (C.fragments j.1).singles_disjoint hi j.2.property
  · exact Set.disjoint_left.mp (C.pathDisjoint hEq) (C.demand_subset i he) (C.single_subset j)

private theorem Walk.length_pos_of_mem_edgeSet {a b : V} {p : G.Walk a b} {e : Sym2 V}
    (he : e ∈ p.edgeSet) : 0 < p.length := by
  cases p with
  | nil => simp at he
  | cons => simp

theorem CrossGroup.cover {p : J × J} (C : CrossGroup G f p B) {e : Sym2 V}
    (he : e ∈ (interPartGraph G f p.1 p.2).edgeSet) :
    (∃ i : C.Demands, e ∈ (C.demand i).walk.edgeSet) ∨ ∃ j : C.Singles, j.2.val = e := by
  rw [← C.pathCover] at he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
  rw [← (C.fragments i).cover] at hi
  rcases hi with (hi | hi) | hi
  · have hp := Walk.length_pos_of_mem_edgeSet hi
    exact Or.inl ⟨⟨(i, false), hp⟩, hi⟩
  · have hp := Walk.length_pos_of_mem_edgeSet hi
    exact Or.inl ⟨⟨(i, true), hp⟩, hi⟩
  · exact Or.inr ⟨⟨i, e, hi⟩, rfl⟩

theorem endpointLoad_sigma {P : Type} [Fintype P] {I : P → Type} [∀ p, Fintype (I p)]
    (x y : (Σ p, I p) → V) (v : V) :
    endpointLoad univ x y v =
    ∑ p, endpointLoad univ (fun i : I p => x ⟨p, i⟩) (fun i : I p => y ⟨p, i⟩) v := by
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Fintype.sum_sigma _

structure CrossingDecomposition (G : SimpleGraph V) (f : V → J) (B : ℕ) where
  Index : Type
  [indexFintype : Fintype Index]
  Sing : Type
  [singFintype : Fintype Sing]
  a : Index → V
  b : Index → V
  p : ∀ i, G.Walk (a i) (b i)
  isPath : ∀ i, (p i).IsPath
  sameColor : ∀ i, f (a i) = f (b i)
  pathCrosses : ∀ i v w, s(v, w) ∈ (p i).edgeSet → f v ≠ f w
  pathDisjoint : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
  single : Sing → Sym2 V
  singleInjective : Function.Injective single
  singleMem : ∀ i, single i ∈ G.edgeSet
  singleCrosses : ∀ i v w, single i = s(v, w) → f v ≠ f w
  singleDisjoint : ∀ i j, single j ∉ (p i).edgeSet
  coverCrossing : ∀ v w, G.Adj v w → f v ≠ f w →
    (∃ i, s(v, w) ∈ (p i).edgeSet) ∨ (∃ j, single j = s(v, w))
  pathCount : Fintype.card Index ≤ (Fintype.card J)^2 * (2 * Fintype.card V)
  singleCount : Fintype.card Sing ≤
    (Fintype.card J)^2 * (Fintype.card V * (2 * (2 * Fintype.card V / B) + 1))
  load : ∀ v, endpointLoad univ a b v ≤ (Fintype.card J)^2 * (2 + B)

instance {G : SimpleGraph V} {f : V → J} {B : ℕ}
    (D : CrossingDecomposition G f B) : Fintype D.Index := D.indexFintype

instance {G : SimpleGraph V} {f : V → J} {B : ℕ}
    (D : CrossingDecomposition G f B) : Fintype D.Sing := D.singFintype

noncomputable def crossingDecomposition (G : SimpleGraph V) (f : V → J) (B : ℕ) (hB : 0 < B) :
    CrossingDecomposition G f B := by
  let C (p : J × J) := crossGroup G f p B hB
  let I := Σ p : J × J, (C p).Demands
  let S := Σ p : J × J, (C p).Singles
  let a (i : I) := ((C i.1).demand i.2).start
  let b (i : I) := ((C i.1).demand i.2).finish
  let p (i : I) : G.Walk (a i) (b i) := ((C i.1).demand i.2).walk.mapLe
    (interPartGraph_le G f _ _)
  let single (i : S) := i.2.2.val
  have hpSet (i : I) : (p i).edgeSet = ((C i.1).demand i.2).walk.edgeSet := by
    ext e
    simp [p, Walk.mem_edgeSet, Walk.edges_mapLe_eq_edges]
  have hpCross (i : I) : (p i).edgeSet ⊆ (interPartGraph G f i.1.1 i.1.2).edgeSet := by
    rw [hpSet]
    exact ((C i.1).demand_subset i.2).trans (fun e he => ((C i.1).paths i.2.val.1).walk.edges_subset_edgeSet he)
  have hsingleCross (i : S) : single i ∈ (interPartGraph G f i.1.1 i.1.2).edgeSet := by
    exact ((C i.1).paths i.2.1).walk.edges_subset_edgeSet ((C i.1).single_subset i.2)
  refine {
    Index := I
    Sing := S
    a := a
    b := b
    p := p
    isPath := fun i => ((C i.1).demand i.2).path.mapLe _
    sameColor := fun i => (C i.1).same_color i.2
    pathCrosses := fun i _ _ h => interPartGraph_distinct G f i.1 (hpCross i h)
    pathDisjoint := ?_
    single := single
    singleInjective := ?_
    singleMem := fun i => (edgeSet_mono (interPartGraph_le G f _ _)) (hsingleCross i)
    singleCrosses := ?_
    singleDisjoint := ?_
    coverCrossing := ?_
    pathCount := ?_
    singleCount := ?_
    load := ?_
  }
  · rintro ⟨i, a⟩ ⟨j, b⟩ hne
    by_cases he : i = j
    · subst j
      rw [hpSet, hpSet]
      exact (C i).demandsDisjoint (fun h => hne (by cases h; rfl))
    · exact (interPartGraph_disjoint G f he).mono (hpCross ⟨i, a⟩) (hpCross ⟨j, b⟩)
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    by_cases hi : i = j
    · subst j
      have h := (C i).single_ne he
      cases h
      rfl
    · exact False.elim (Set.disjoint_left.mp (interPartGraph_disjoint G f hi)
        (hsingleCross ⟨i, a⟩) (he.symm ▸ hsingleCross ⟨j, b⟩))
  · intro i v w h
    have he := hsingleCross i
    rw [h] at he
    exact interPartGraph_distinct G f i.1 he
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    by_cases hEq : i = j
    · subst j
      rw [hpSet] at h
      exact (C i).demand_single_disjoint a b h
    · exact Set.disjoint_left.mp (interPartGraph_disjoint G f hEq)
        (hpCross ⟨i, a⟩ h) (hsingleCross ⟨j, b⟩)
  · intro v w h hvw
    obtain ⟨i, hi⟩ := edge_crosses_some_parts G f h hvw
    rcases (C i).cover hi with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨⟨i, a⟩, (hpSet ⟨i, a⟩) ▸ ha⟩
    · exact Or.inr ⟨⟨i, b⟩, hb⟩
  · change Fintype.card (Σ p : J × J, (C p).Demands) ≤ _
    rw [Fintype.card_sigma]
    exact (Finset.sum_le_sum (fun i _ => (C i).demandCount)).trans_eq
      (by simp [pow_two])
  · change Fintype.card (Σ p : J × J, (C p).Singles) ≤ _
    rw [Fintype.card_sigma]
    exact (Finset.sum_le_sum (fun i _ => (C i).singlesCount)).trans_eq
      (by simp [pow_two])
  · intro v
    rw [endpointLoad_sigma]
    exact (Finset.sum_le_sum (fun i _ => (C i).demandLoad v)).trans_eq
      (by simp [pow_two])

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph DenseCycleDecomposition
open scoped Classical
noncomputable section

theorem fromEdgeSet_of_subset {V : Type} {G : SimpleGraph V} (E : Set (Sym2 V))
    (h : E ⊆ G.edgeSet) : (SimpleGraph.fromEdgeSet E).edgeSet = E := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · exact fun he => ⟨he, G.edgeSet_subset_compl_diagSet (h he)⟩

theorem decompositionCost_map_le {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f) (hCover : Sym2.map f '' H.edgeSet = G.edgeSet) :
    decompositionCost G ≤ decompositionCost H :=
  decompositionCost_le (edgeDecomposition_map f hf hCover (decompositionCost_spec H))

structure InPartReturns {V I J : Type} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (color : V → J) (a b : I → V) (L : ℕ) (C : ℝ) where
  route : ∀ i, G.Walk (b i) (a i)
  routePath : ∀ i, (route i).IsPath
  routeLength : ∀ i, (route i).length ≤ L
  routeDisjoint : Pairwise (fun i j => Disjoint (route i).edgeSet (route j).edgeSet)
  routeColor : ∀ i v w, s(v, w) ∈ (route i).edgeSet → color v = color (a i) ∧ color w = color (a i)
  residue : J → SimpleGraph V
  residueLe : ∀ j, residue j ≤ G
  residueColor : ∀ j v w, (residue j).Adj v w → color v = j ∧ color w = j
  residueDisjoint : ∀ i j, Disjoint (route i).edgeSet (residue j).edgeSet
  coverWithin : ∀ v w, G.Adj v w → color v = color w →
    (∃ i, s(v, w) ∈ (route i).edgeSet) ∨ (residue (color v)).Adj v w
  cost : ∀ j, (decompositionCost (residue j) : ℝ) ≤ C * (fiber color j).card

theorem routes_inside_parts {V I J : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → J) (a b : I → V)
    (hsame : ∀ i, color (a i) = color (b i))
    (d : ℝ) (hd : 0 < d) (K : ℕ) (hK : 4 / d ^ 2 ≤ (K : ℝ))
    (h k : ℝ) (hD : d * Fintype.card V ≤ h)
    (hSizes : ∀ j, 2 ≤ (fiber color j).card)
    (hExp : ∀ j, CutExpansion (G.induce (fiber color j : Set V)) h)
    (hLoad : ∀ v, (endpointLoad Finset.univ a b v : ℝ) ≤ k)
    (hDegree : h / 8 + 2 + k ≤ h / 4)
    (hTotal : 128 * (2 * ((K : ℝ) + 1) * Fintype.card I) ≤ h ^ 2)
    (C : ℝ) (hCostCut : ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], CutExpansion H ((d / 2) * Fintype.card W) →
      (decompositionCost H : ℝ) ≤ C * Fintype.card W) :
    Nonempty (InPartReturns G color a b (2 * (K + 1)) C) := by
  let Vj (j : J) := ↥(fiber color j : Set V)
  let Ij (j : J) := {i : I // color (a i) = j}
  let H (j : J) := G.induce (fiber color j : Set V)
  let X (j : J) (i : Ij j) : Vj j := ⟨b i.val, mem_fiber.mpr ((hsame i.val).symm.trans i.property)⟩
  let Y (j : J) (i : Ij j) : Vj j := ⟨a i.val, mem_fiber.mpr i.property⟩
  have hSizeJ (j : J) : (Fintype.card (Vj j) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Fintype.card_le_of_injective (fun x : Vj j => x.val) Subtype.val_injective)
  have hCardJ (j : J) : (Fintype.card (Ij j) : ℝ) ≤ Fintype.card I := by
    exact_mod_cast (Fintype.card_le_of_injective (fun x : Ij j => x.val) Subtype.val_injective)
  have hRoute (j : J) : ∃ q : ∀ i, (H j).Walk (X j i) (Y j i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ 2 * (K + 1)) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
      ∀ v, ((incidentEdges (usedEdges univ q) v).card : ℝ) ≤ h / 4 := by
    have hL (v : Vj j) : endpointLoad univ (X j) (Y j) v ≤ endpointLoad univ a b v.val := by
      unfold endpointLoad
      apply Finset.card_le_card_of_injOn (fun i : Ij j => i.val)
      · intro i hi
        rcases (Finset.mem_filter.mp hi).2 with ht | ht
        · exact Finset.mem_filter.mpr ⟨mem_univ _, Or.inr (congrArg Subtype.val ht)⟩
        · exact Finset.mem_filter.mpr ⟨mem_univ _, Or.inl (congrArg Subtype.val ht)⟩
      · intro i _ l _ he
        exact Subtype.ext he
    have hExp' : CutExpansion (H j) h := hExp j
    have hN : 2 ≤ Fintype.card (Vj j) := by simpa [Vj] using hSizes j
    have hLocalD : d * Fintype.card (Vj j) ≤ h :=
      (mul_le_mul_of_nonneg_left (hSizeJ j) hd.le).trans hD
    have hLocalTotal : 128 * (2 * ((K : ℝ) + 1) * Fintype.card (Ij j)) ≤ h ^ 2 := by
      apply le_trans _ hTotal
      gcongr
      exact_mod_cast hCardJ j
    exact dense_route_family d hd K hK (H j) h hLocalD hExp' hN (X j) (Y j) k
      (fun v => (Nat.cast_le.mpr (hL v) : (_ : ℝ) ≤ _).trans (hLoad v.val))
      hDegree hLocalTotal
  choose qJ hqJ hdJ hFJ using hRoute
  let m (j : J) : H j →g G := ⟨Subtype.val, fun h => h⟩
  let idx (i : I) : Ij (color (a i)) := ⟨i, rfl⟩
  let q (i : I) : G.Walk (b i) (a i) := (qJ (color (a i)) (idx i)).map (m _)
  let F (j : J) := usedEdges Finset.univ (qJ j)
  let W (j : J) := (H j).deleteEdges (F j : Set (Sym2 (Vj j)))
  let E (j : J) : Set (Sym2 V) := Sym2.map (m j) '' (W j).edgeSet
  let R (j : J) := SimpleGraph.fromEdgeSet (E j)
  have hE (j : J) : E j ⊆ G.edgeSet := by
    rintro _ ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : (W j).Adj x y := he
      exact (H j).deleteEdges_le _ hxy
  have hR (j : J) : (R j).edgeSet = E j := fromEdgeSet_of_subset (E j) (hE j)
  have hF (j : J) (i : Ij j) : (qJ j i).edgeSet ⊆ (F j : Set (Sym2 (Vj j))) := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨i, mem_univ _, List.mem_toFinset.mpr he⟩
  have hQedge (i : I) :
      (q i).edgeSet = Sym2.map (m (color (a i))) '' (qJ (color (a i)) (idx i)).edgeSet :=
    Walk.edgeSet_map _ _
  have hQedgeAt (i : I) (j : J) (hj : color (a i) = j) :
      (q i).edgeSet = Sym2.map (m j) '' (qJ j ⟨i, hj⟩).edgeSet := by
    subst j
    exact hQedge i
  have hColorOfImage (j : J) {E' : Set (Sym2 (Vj j))} {v w : V}
      (he : s(v, w) ∈ Sym2.map (m j) '' E') : color v = j ∧ color w = j := by
    obtain ⟨e, -, he⟩ := he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : color x.val = j := mem_fiber.mp x.property
      have hy : color y.val = j := mem_fiber.mp y.property
      rcases Sym2.eq_iff.mp he with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩
      · exact ⟨he₁ ▸ hx, he₂ ▸ hy⟩
      · exact ⟨he₂ ▸ hy, he₁ ▸ hx⟩
  have hm (j : J) : Function.Injective (Sym2.map (m j)) :=
    Sym2.map.injective Subtype.val_injective
  have hPathColor (i : I) (v w : V) (he : s(v, w) ∈ (q i).edgeSet) :
      color v = color (a i) ∧ color w = color (a i) :=
    hColorOfImage _ ((hQedge i) ▸ he)
  have hRcolor (j : J) (v w : V) (he : (R j).Adj v w) : color v = j ∧ color w = j :=
    hColorOfImage j ((hR j) ▸ (show s(v, w) ∈ (R j).edgeSet from he))
  refine ⟨{
    route := q
    routePath := fun i => ((hqJ _ (idx i)).1.map Subtype.val_injective)
    routeLength := fun i => by simpa [q] using (hqJ _ (idx i)).2
    routeDisjoint := ?_
    routeColor := hPathColor
    residue := R
    residueLe := fun j => edgeSet_subset_edgeSet.mp ((hR j).symm ▸ hE j)
    residueColor := hRcolor
    residueDisjoint := ?_
    coverWithin := ?_
    cost := ?_
  }⟩
  · intro i l hne
    rw [Set.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | _ v w =>
      have hij : color (a i) = color (a l) := (hPathColor i v w he).1.symm.trans (hPathColor l v w he').1
      let j := color (a i)
      have hi : s(v, w) ∈ Sym2.map (m j) '' (qJ j ⟨i, rfl⟩).edgeSet := hQedge i ▸ he
      have hl : s(v, w) ∈ Sym2.map (m j) '' (qJ j ⟨l, hij.symm⟩).edgeSet :=
        hQedgeAt l j hij.symm ▸ he'
      exact Set.disjoint_left.mp ((Set.disjoint_image_iff (hm j)).mpr
        (hdJ j (fun h => hne (congrArg Subtype.val h)))) hi hl
  · intro i j
    rw [Set.disjoint_left]
    intro e he hr
    induction e using Sym2.ind with
    | _ v w =>
      have hij : color (a i) = j := (hPathColor i v w he).1.symm.trans (hRcolor j v w hr).1
      subst j
      have hi := hQedge i ▸ he
      have hj := hR _ ▸ hr
      have hs : Disjoint (qJ _ (idx i)).edgeSet (W _).edgeSet := by
        simp only [W, SimpleGraph.edgeSet_deleteEdges]
        exact Set.disjoint_sdiff_right.mono_left (hF _ _)
      exact Set.disjoint_left.mp ((Set.disjoint_image_iff (hm _)).mpr hs) hi hj
  · intro v w hvw hColor
    let j := color v
    let x : Vj j := ⟨v, mem_fiber.mpr rfl⟩
    let y : Vj j := ⟨w, mem_fiber.mpr hColor.symm⟩
    by_cases hDel : s(x, y) ∈ F j
    · obtain ⟨i, -, he⟩ := Finset.mem_biUnion.mp hDel
      apply Or.inl
      refine ⟨i.val, ?_⟩
      have hx : s(x, y) ∈ (qJ j i).edgeSet := List.mem_toFinset.mp he
      have hmap : s(v, w) ∈ Sym2.map (m j) '' (qJ j i).edgeSet := ⟨s(x, y), hx, rfl⟩
      rw [hQedgeAt i.val j i.property]
      exact hmap
    · apply Or.inr
      have hxy : s(x, y) ∈ (W j).edgeSet := by
        simp only [W, SimpleGraph.edgeSet_deleteEdges]
        exact ⟨hvw, hDel⟩
      change s(v, w) ∈ (R j).edgeSet
      rw [hR]
      exact ⟨s(x, y), hxy, rfl⟩
  · intro j
    have hCut := cutExpansion_delete_bounded_edges (H j) h (h / 4) (hExp j) (F j) (hFJ j)
    have hStrong : CutExpansion (W j) ((d / 2) * Fintype.card (Vj j)) := by
      intro S
      apply le_trans _ (hCut S)
      have hh : (d / 2) * Fintype.card (Vj j) ≤ h - h / 4 := by
        have hs := mul_le_mul_of_nonneg_left (hSizeJ j) hd.le
        have hn : 0 ≤ d * (Fintype.card V : ℝ) := by positivity
        linarith only [hs, hD, hn]
      exact mul_le_mul_of_nonneg_right hh (by positivity)
    let m' : W j →g R j := ⟨Subtype.val, by
      intro v w hvw
      change s(v.val, w.val) ∈ (R j).edgeSet
      rw [hR]
      exact ⟨s(v, w), hvw, rfl⟩⟩
    have ho := decompositionCost_map_le m' Subtype.val_injective (hR j).symm
    have hCost := hCostCut (Vj j) (W j) hStrong
    exact (Nat.cast_le.mpr ho).trans (by simpa [Vj] using hCost)

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph DenseCycleDecomposition
open scoped Classical
noncomputable section

theorem cost_of_crossing_and_within_parts {V J : Type} [Fintype V] [DecidableEq V]
    [Fintype J] [LinearOrder J] {G : SimpleGraph V} {color : V → J} {B L : ℕ} {C : ℝ}
    (D : CrossingDecomposition G color B)
    (Q : InPartReturns G color D.a D.b L C) :
    decompositionCost G ≤ Fintype.card D.Index * L + Fintype.card D.Sing +
      ∑ j, decompositionCost (Q.residue j) := by
  let E := (⋃ j, (Q.residue j).edgeSet) ∪ Set.range D.single
  let R := SimpleGraph.fromEdgeSet E
  have hRG : E ⊆ G.edgeSet := by
    intro e he
    rcases he with hl | ⟨j, rfl⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hl
      exact edgeSet_mono (Q.residueLe j) hj
    · exact D.singleMem j
  have hEdgeR : R.edgeSet = E := fromEdgeSet_of_subset E hRG
  have hRQ (j : J) : Q.residue j ≤ R := by
    apply edgeSet_subset_edgeSet.mp
    rw [hEdgeR]
    exact fun e he => Or.inl (Set.mem_iUnion.mpr ⟨j, he⟩)
  have hRpair : Pairwise fun i j => Disjoint (Q.residue i).edgeSet (Q.residue j).edgeSet := by
    intro i j hne
    rw [Set.disjoint_left]
    intro e he hf
    induction e using Sym2.ind with
    | _ v w => exact hne ((Q.residueColor i v w he).1.symm.trans (Q.residueColor j v w hf).1)
  have hRsingle (j : J) (i : D.Sing) :
      Disjoint (Q.residue j).edgeSet ({D.single i} : Set (Sym2 V)) := by
    rw [Set.disjoint_left]
    intro e he hi
    have hi' : e = D.single i := hi
    induction e using Sym2.ind with
    | _ v w =>
      have hcolor := Q.residueColor j v w he
      exact D.singleCrosses i v w hi'.symm (hcolor.1.trans hcolor.2.symm)
  have hResCover : (⋃ i, ({D.single i} : Set (Sym2 V))) ∪ (⋃ j, (Q.residue j).edgeSet) =
      R.edgeSet := by
    rw [hEdgeR, Set.union_comm]
    congr 1
    ext e
    simp [eq_comm]
  have hCostR : decompositionCost R ≤ Fintype.card D.Sing +
      ∑ j, decompositionCost (Q.residue j) := by
    apply decompositionCost_adjoin_same R (fun i => {D.single i}) _ _ Q.residue hRQ hRpair hRsingle hResCover
    · intro i
      exact Or.inr ⟨D.single i, hEdgeR.symm ▸ Or.inr ⟨i, rfl⟩, rfl⟩
    · intro i j hij
      simpa using fun he => hij (D.singleInjective he)
  have hPQ (i j : D.Index) : Disjoint (D.p i).edgeSet (Q.route j).edgeSet := by
    rw [Set.disjoint_left]
    intro e hi hj
    induction e using Sym2.ind with
    | _ v w =>
      have hColor := Q.routeColor j v w hj
      exact D.pathCrosses i v w hi (hColor.1.trans hColor.2.symm)
  have hRNonCross (i : D.Index) : Disjoint R.edgeSet (D.p i).edgeSet := by
    rw [hEdgeR, Set.disjoint_left]
    intro e he hp
    rcases he with h | ⟨j, rfl⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      induction e using Sym2.ind with
      | _ v w =>
        have hColor := Q.residueColor j v w hj
        exact D.pathCrosses i v w hp (hColor.1.trans hColor.2.symm)
    · exact D.singleDisjoint i j hp
  have hRNonRouting (i : D.Index) : Disjoint R.edgeSet (Q.route i).edgeSet := by
    rw [hEdgeR, Set.disjoint_left]
    intro e he hq
    rcases he with h | ⟨j, hj⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact Set.disjoint_left.mp (Q.residueDisjoint i j) hq hj
    · induction e using Sym2.ind with
      | _ v w =>
        have hColor := Q.routeColor i v w hq
        exact D.singleCrosses j v w hj (hColor.1.trans hColor.2.symm)
  have hTrail (i : D.Index) : ((D.p i).append (Q.route i)).IsTrail := by
    apply (Walk.isTrail_append _ _).mpr
    exact ⟨(D.isPath i).isTrail, (Q.routePath i).isTrail,
      List.disjoint_left.mpr (Set.disjoint_left.mp (hPQ i i))⟩
  have hClosedPair : Pairwise (fun i j : D.Index =>
      Disjoint ((D.p i).edgeSet ∪ (Q.route i).edgeSet)
        ((D.p j).edgeSet ∪ (Q.route j).edgeSet)) := by
    intro i j hne
    simp only [Set.disjoint_union_left, Set.disjoint_union_right]
    exact ⟨⟨D.pathDisjoint hne, (hPQ j i).symm⟩, ⟨hPQ i j, Q.routeDisjoint hne⟩⟩
  have hFullCover : (⋃ i, ((D.p i).edgeSet ∪ (Q.route i).edgeSet)) ∪ R.edgeSet = G.edgeSet := by
    ext e
    constructor
    · rintro (he | he)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        exact hi.elim (fun h => (D.p i).edges_subset_edgeSet h)
          (fun h => (Q.route i).edges_subset_edgeSet h)
      · exact hRG (hEdgeR ▸ he)
    · intro he
      induction e using Sym2.ind with
      | _ v w =>
        by_cases h : color v = color w
        · rcases Q.coverWithin v w he h with ⟨i, hi⟩ | hi
          · exact Or.inl (Set.mem_iUnion.mpr ⟨i, Or.inr hi⟩)
          · exact Or.inr (edgeSet_mono (hRQ _) hi)
        · rcases D.coverCrossing v w he h with ⟨i, hi⟩ | ⟨i, hi⟩
          · exact Or.inl (Set.mem_iUnion.mpr ⟨i, Or.inl hi⟩)
          · exact Or.inr (hEdgeR.symm ▸ Or.inr ⟨i, hi⟩)
  have hWhole := decompositionCost_with_short_returns G R (edgeSet_subset_edgeSet.mp (hEdgeR.symm ▸ hRG))
    D.a D.b D.p Q.route D.isPath hTrail hClosedPair
    (fun i => Set.disjoint_union_right.mpr ⟨hRNonCross i, hRNonRouting i⟩) hFullCover
  have hRoutes : (∑ i, (Q.route i).length) ≤ Fintype.card D.Index * L := by
    exact (Finset.sum_le_sum (fun i _ => Q.routeLength i)).trans_eq (by simp)
  omega

end
end OAI.ErdosGallai

namespace OAI.ErdosGallai

open Finset SimpleGraph DenseCycleDecomposition
open scoped Classical
noncomputable section

theorem linear_cost_of_minimum_degree (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, ε * Fintype.card V ≤ (G.degree v : ℝ)) →
      (decompositionCost G : ℝ) ≤ C * Fintype.card V := by
  let δ := ε / 2
  let d := ε ^ 2 / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨C₀, hC₀, hCut⟩ := linear_cost_cut_dense (d / 2) (by positivity)
  let K := ⌈4 / d ^ 2⌉₊
  have hK : 4 / d ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  let L := 2 * ((K : ℝ) + 1)
  have hL : 0 < L := by dsimp [L]; positivity
  let R := ⌈max 1 (1 / δ)⌉₊
  let M := (R : ℝ) ^ 2
  have hR : 1 ≤ (R : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have hM : 0 < M := by dsimp [M]; positivity
  let α := d / (64 * M)
  have hα : 0 < α := by dsimp [α]; positivity
  let N₀ := max (2 / δ) (max 1 (max (64 * (3 * M + 2) / d) (256 * L * M / d ^ 2)))
  have hNpos : 0 < N₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans (le_max_right _ _))
  let T := 4 / α + 1
  have hT : 0 < T := by dsimp [T]; positivity
  let C := 2 * M * L + M * T + C₀ + N₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ hDegree
  let n := Fintype.card V
  have hn₀ : (0 : ℝ) ≤ n := by positivity
  by_cases hSmall : (n : ℝ) < N₀
  · have hEdges : (G.edgeFinset.card : ℝ) ≤ (n : ℝ) * n := by
      have h := G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)
      rw [pow_two] at h
      exact_mod_cast h
    have hCost : (decompositionCost G : ℝ) ≤ G.edgeFinset.card := by
      have h := decompositionCost_singleEdges G
      rw [Nat.card_eq_fintype_card, G.card_edgeSet] at h
      exact_mod_cast h
    have hcn : (n : ℝ) ≤ C := hSmall.le.trans (by
      have hML : 0 ≤ 2 * M * L := by positivity
      have hMT : 0 ≤ M * T := by positivity
      dsimp [C]
      linarith only [hML, hMT, hC₀])
    exact (hCost.trans hEdges).trans (mul_le_mul_of_nonneg_right hcn hn₀)
  have hn : N₀ ≤ (n : ℝ) := le_of_not_gt hSmall
  have hnpos : (0 : ℝ) < n := hNpos.trans_le hn
  have hnposN : 0 < n := by exact_mod_cast hnpos
  obtain ⟨f, hbetween, hwithin⟩ := exists_cut_density_partition G δ
  let Active := activeFibers f
  have hSize (j : Active) : δ * n ≤ (fiber f j.val).card := by
    simpa only [show ε - δ = δ by dsimp [δ]; ring] using
      partition_fiber_size G ε δ hδ.le hDegree f hbetween j.val j.property
  have hActive : (Fintype.card Active : ℝ) ≤ 1 / δ := active_fibers_card f δ hδ hnposN hSize
  let equiv := Fintype.equivFin Active
  let J := Fin (Fintype.card Active)
  let color (v : V) : J := equiv ⟨f v, ⟨v, mem_fiber.mpr rfl⟩⟩
  have hFiber (j : J) : fiber color j = fiber f (equiv.symm j).val := by
    ext v
    rw [mem_fiber, mem_fiber]
    constructor
    · intro he
      exact congrArg Subtype.val (equiv.apply_eq_iff_eq_symm_apply.mp he)
    · intro he
      apply equiv.apply_eq_iff_eq_symm_apply.mpr
      exact Subtype.ext he
  have hM' : (Fintype.card J : ℝ) ^ 2 ≤ M := by
    have h : (Fintype.card Active : ℝ) ≤ R :=
      hActive.trans ((le_max_right (1 : ℝ) (1 / δ)).trans (Nat.le_ceil (max 1 (1 / δ))))
    have h' : (Fintype.card J : ℝ) ≤ R := by simpa [J] using h
    dsimp [M]
    gcongr
  let h := d * n
  have hFactor : δ * δ / 2 = d := by dsimp [δ, d]; ring
  have hExp (j : J) : CutExpansion (G.induce (fiber color j : Set V)) h := by
    let A := fiber f (equiv.symm j).val
    rw [hFiber j]
    have hE := induced_cutExpansion_of_density G A δ hδ.le (hwithin (equiv.symm j).val)
    have hCard := mul_le_mul_of_nonneg_left (hSize (equiv.symm j)) hδ.le
    have hN : h ≤ δ * A.card / 2 := by
      calc
        h = (δ * δ / 2) * n := by rw [hFactor]
        _ ≤ _ := by dsimp [A]; nlinarith only [hCard]
    intro S
    exact (mul_le_mul_of_nonneg_right hN (by positivity)).trans (hE S)
  have hSizes (j : J) : 2 ≤ (fiber color j).card := by
    have hN : 2 / δ ≤ (n : ℝ) := (le_max_left _ _).trans hn
    have hc := (div_le_iff₀ hδ).mp hN
    have hcard : (2 : ℝ) ≤ (fiber color j).card := by
      rw [hFiber]
      linarith only [hc, hSize (equiv.symm j)]
    exact_mod_cast hcard
  let B := ⌈α * (n : ℝ)⌉₊
  have hB : 0 < B := (Nat.one_le_ceil_iff.mpr (mul_pos hα hnpos))
  let D := crossingDecomposition G color B hB
  have hB_lo : α * (n : ℝ) ≤ B := Nat.le_ceil _
  have hB_hi : (B : ℝ) ≤ α * n + 1 := (Nat.ceil_lt_add_one (mul_nonneg hα.le hn₀)).le
  have hDiv : ((2 * n / B : ℕ) : ℝ) ≤ 2 / α := by
    have hMul := Nat.div_mul_le_self (2 * n) B
    have hMulR : ((2 * n / B : ℕ) : ℝ) * B ≤ 2 * n := by exact_mod_cast hMul
    have hScaled := (mul_le_mul_of_nonneg_left hB_lo
      (show 0 ≤ ((2 * n / B : ℕ) : ℝ) by positivity)).trans hMulR
    apply (le_div_iff₀ hα).mpr
    apply (mul_le_mul_iff_left₀ hnpos).mp
    nlinarith only [hScaled]
  have hDivBound : ((2 * (2 * n / B) + 1 : ℕ) : ℝ) ≤ T := by
    push_cast
    calc
      _ ≤ 2 * (2 / α) + 1 := by gcongr
      _ = T := by dsimp [T]; ring
  have hPathCount : (Fintype.card D.Index : ℝ) ≤ M * (2 * n) := by
    have h := D.pathCount
    have h' : (Fintype.card D.Index : ℝ) ≤ (Fintype.card J : ℝ) ^ 2 * (2 * n) := by
      exact_mod_cast h
    exact h'.trans (mul_le_mul_of_nonneg_right hM' (by positivity))
  have hSingles : (Fintype.card D.Sing : ℝ) ≤ M * (n * T) := by
    have hh := D.singleCount
    have hh' : (Fintype.card D.Sing : ℝ) ≤
        (Fintype.card J : ℝ) ^ 2 * ((n : ℝ) * ((2 * (2 * n / B) + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hh
    exact hh'.trans (mul_le_mul hM' (mul_le_mul_of_nonneg_left hDivBound hn₀)
      (by positivity) hM.le)
  let k := M * (2 + (B : ℝ))
  have hLoad (v : V) : (endpointLoad Finset.univ D.a D.b v : ℝ) ≤ k := by
    have h' : (endpointLoad Finset.univ D.a D.b v : ℝ) ≤
        (Fintype.card J : ℝ) ^ 2 * (2 + (B : ℝ)) := by exact_mod_cast D.load v
    exact h'.trans (mul_le_mul_of_nonneg_right hM' (by positivity))
  have hA : M * α = d / 64 := by
    dsimp [α]
    field_simp
    <;> ring
  have hBudget : 3 * M + 2 ≤ h / 64 := by
    have hN : 64 * (3 * M + 2) / d ≤ (n : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hh := (div_le_iff₀ hd).mp hN
    dsimp [h]
    linarith only [hh]
  have hInc : h / 8 + 2 + k ≤ h / 4 := by
    have hk : k ≤ 3 * M + h / 64 := by
      have hCast := mul_le_mul_of_nonneg_left hB_hi hM.le
      have hEq : M * (α * (n : ℝ)) = h / 64 := by
        rw [← mul_assoc, hA]
        dsimp [h]
        ring
      dsimp [k]
      linarith only [hCast, hEq]
    have hpos : 0 ≤ h := mul_nonneg hd.le hn₀
    linarith only [hBudget, hk, hpos]
  have hTotal : 128 * (L * Fintype.card D.Index) ≤ h ^ 2 := by
    have hN : 256 * L * M / d ^ 2 ≤ (n : ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hQuad := mul_le_mul_of_nonneg_right ((div_le_iff₀ (sq_pos_of_pos hd)).mp hN) hn₀
    have hCnt := mul_le_mul_of_nonneg_left hPathCount (show 0 ≤ 128 * L by positivity)
    dsimp [h]
    nlinarith only [hQuad, hCnt]
  obtain ⟨Q⟩ := routes_inside_parts G color D.a D.b D.sameColor d hd K hK h k
    le_rfl hSizes hExp hLoad hInc hTotal C₀ hCut
  have hResidual : ∑ j, (decompositionCost (Q.residue j) : ℝ) ≤ C₀ * n := by
    refine (Finset.sum_le_sum (fun j _ => Q.cost j)).trans_eq ?_
    rw [← Finset.mul_sum, ← Nat.cast_sum, sum_card_fibers color]
  have hAll := cost_of_crossing_and_within_parts D Q
  have hAllR : (decompositionCost G : ℝ) ≤ (Fintype.card D.Index : ℝ) * L +
      Fintype.card D.Sing + ∑ j, (decompositionCost (Q.residue j) : ℝ) := by
    dsimp [L]
    exact_mod_cast hAll
  have hPaths := mul_le_mul_of_nonneg_right hPathCount hL.le
  have hSlack := mul_nonneg hNpos.le hn₀
  dsimp [C]
  linarith only [hPaths, hSingles, hResidual, hAllR, hSlack]

end
end OAI.ErdosGallai


namespace DenseCycleDecomposition

open Filter SimpleGraph
open scoped Classical

private theorem supportedPiece {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s : Set (Sym2 V))
    (h : (∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ s = w.edgeSet) ∨
      ∃ e ∈ G.edgeSet, s = {e}) :
    ∃ H : G.Subgraph, Erdos184.IsCycleOrEdge H.coe ∧ H.edgeSet = s := by
  classical
  rcases h with ⟨v, w, hw, rfl⟩ | ⟨e, he, rfl⟩
  · refine ⟨w.toSubgraph, Or.inl ⟨w.toSubgraph_connected.coe, ?_⟩,
      w.edgeSet_toSubgraph⟩
    intro x
    rw [Subgraph.coe_degree]
    change Fintype.card (w.toSubgraph.neighborSet (x : V)) = 2
    rw [Set.fintypeCard_eq_ncard]
    exact hw.ncard_neighborSet_toSubgraph_eq_two ((w.mem_verts_toSubgraph).mp x.property)
  · induction e using Sym2.ind with
    | h a b =>
      let H := G.subgraphOfAdj he
      have hH : H.edgeSet = {s(a, b)} := G.edgeSet_subgraphOfAdj he
      refine ⟨H, Or.inr ?_, hH⟩
      have hImage := Set.ncard_image_of_injective H.coe.edgeSet
        (Sym2.map.injective (f := Subtype.val) Subtype.val_injective)
      rw [H.image_coe_edgeSet_coe, hH, Set.ncard_singleton] at hImage
      rw [← Set.ncard_coe_finset, coe_edgeFinset]
      exact hImage.symm

private theorem transportPartition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (A : Fin k → Set (Sym2 (Fin (Fintype.card V))))
    (hpieces : ∀ i, (∃ (v : Fin (Fintype.card V))
      (w : (G.comap (Fintype.equivFin V).symm).Walk v v), w.IsCycle ∧ A i = w.edgeSet) ∨
      ∃ e ∈ (G.comap (Fintype.equivFin V).symm).edgeSet, A i = {e})
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcover : (⋃ i, A i) = (G.comap (Fintype.equivFin V).symm).edgeSet) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, Erdos184.IsCycleOrEdge H.coe) ∧ G.IsDecomposition D ∧ D.card ≤ k := by
  classical
  let f := (Fintype.equivFin V).symm
  let F : (G.comap f) →g G := ⟨f, fun h => h⟩
  have hf : Function.Injective F := f.injective
  have hMappedEdgeSet : Sym2.map F '' (G.comap f).edgeSet = G.edgeSet := by
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      induction e' using Sym2.ind with
      | h a b => exact F.map_adj he'
    · intro he
      induction e using Sym2.ind with
      | h a b =>
        refine ⟨s(f.symm a, f.symm b), ?_, ?_⟩
        · change (G.comap f).Adj (f.symm a) (f.symm b)
          change G.Adj (f (f.symm a)) (f (f.symm b))
          simpa only [Equiv.apply_symm_apply, SimpleGraph.mem_edgeSet] using he
        · simp only [Sym2.map_mk]
          change s(f (f.symm a), f (f.symm b)) = s(a, b)
          simp
  have hWitness (i : Fin k) : ∃ H : G.Subgraph, Erdos184.IsCycleOrEdge H.coe ∧
      H.edgeSet = Sym2.map F '' A i := by
    apply supportedPiece
    rcases hpieces i with ⟨v, w, hw, ha⟩ | ⟨e, he, ha⟩
    · refine Or.inl ⟨F v, w.map F, hw.map hf, ?_⟩
      rw [ha, Walk.edgeSet_map]
    · refine Or.inr ⟨Sym2.map F e, ?_, by simp [ha]⟩
      rw [← hMappedEdgeSet]
      exact ⟨e, he, rfl⟩
  choose H hH hEdge using hWitness
  refine ⟨Finset.univ.image H, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro J hJ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hJ
    exact hH i
  · intro J hJ K hK hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hK
    change Disjoint (H i).edgeSet (H j).edgeSet
    rw [hEdge, hEdge]
    exact (Set.disjoint_image_iff (Sym2.map.injective hf)).2
      (hdisj (fun eq => hne (congrArg H eq)))
  · calc
      (⋃ J ∈ (Finset.univ.image H : Finset G.Subgraph), J.edgeSet) = ⋃ i, (H i).edgeSet := by
        ext e
        simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨J, ⟨i, rfl⟩, he⟩
          exact ⟨i, he⟩
        · rintro ⟨i, he⟩
          exact ⟨H i, ⟨i, rfl⟩, he⟩
      _ = Sym2.map F '' (⋃ i, A i) := by simp_rw [hEdge, Set.image_iUnion]
      _ = G.edgeSet := by rw [hcover, hMappedEdgeSet]
  · simpa using (Finset.card_image_le (s := Finset.univ) (f := H))

end DenseCycleDecomposition

namespace DenseCycleDecomposition

open Filter SimpleGraph
open scoped Classical

private theorem degrees_under_relabeling {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (f : W ≃ V) (w : W) :
    (G.comap f).degree w = G.degree (f w) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  let F : (G.comap f).neighborSet w ≃ G.neighborSet (f w) :=
    { toFun := fun u => ⟨f u.val, u.property⟩
      invFun := fun v => ⟨f.symm v.val, by
        change G.Adj (f w) (f (f.symm v.val))
        rw [f.apply_symm_apply]
        exact v.property⟩
      left_inv := fun u => Subtype.ext (f.symm_apply_apply u.val)
      right_inv := fun v => Subtype.ext (f.apply_symm_apply v.val) }
  exact Fintype.card_congr F

end DenseCycleDecomposition

open scoped Classical in
theorem OMA.solution : type_of% @Erdos184.erdos_184.variants.conlon_fox_sudakov := by
  classical
  intro ε hε
  obtain ⟨C, hC, hCost⟩ := OAI.ErdosGallai.linear_cost_of_minimum_degree ε hε
  refine ⟨fun n => C * n, Asymptotics.IsBigO.of_bound C ?_, ?_⟩
  · filter_upwards [] with n
    simp [norm_mul, Real.norm_eq_abs, abs_of_pos hC]
  · intro V _ _ G hdegree
    let n := Fintype.card V
    let f := (Fintype.equivFin V).symm
    let H := G.comap f
    have hH (v : Fin n) : ε * Fintype.card (Fin n) ≤ (H.degree v : ℝ) := by
      have hd : (G.minDegree : ℝ) ≤ (G.degree (f v) : ℝ) := by
        exact_mod_cast G.minDegree_le_degree (f v)
      rw [DenseCycleDecomposition.degrees_under_relabeling G f v, Fintype.card_fin]
      exact hdegree.trans hd
    have hBound := hCost (Fin n) H hH
    obtain ⟨A, hA, hDisjoint, hCover⟩ := OAI.ErdosGallai.decompositionCost_spec H
    obtain ⟨D, hD, hDecomposition, hCard⟩ :=
      DenseCycleDecomposition.transportPartition G (OAI.ErdosGallai.decompositionCost H)
        A hA hDisjoint hCover
    exact ⟨D, hD, hDecomposition, (Nat.cast_le.mpr hCard).trans (by simpa [n] using hBound)⟩
