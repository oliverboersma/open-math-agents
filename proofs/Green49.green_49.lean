import FormalConjectures.GreensOpenProblems.«49»
import Mathlib

/-!
# The polynomial Freiman–Ruzsa theorem over the field of two elements

For a nonempty finite set A with |A+A| ≤ K|A|, the proof constructs a
subspace of size at most |A| whose translates cover A. At most 2K¹²
translates are required.

The mathematical result is due to W. T. Gowers, Ben Green, Freddie
Manners, and Terence Tao, “On a conjecture of Marton”, Annals of
Mathematics 201 (2025), 515–549. https://doi.org/10.4007/annals.2025.201.2.5

The entropy proof and its prerequisites are adapted from the collaborative
Lean project “Formalization of the Polynomial Freiman-Ruzsa Conjecture of
Marton”, organized by Yaël Dillies and Terence Tao. The source snapshot is
https://github.com/teorth/pfr/tree/7d6404b79b11. Each adapted section
names its original module. The popular-coset calculations also adapt
PFR.Main. Its CITATION.cff credits these contributors.

Aaron Anderson, Mantas Bakšys, Jonas Bayer, Mauricio Collares, Rémy Degenne,
Yaël Dillies, Ben Eltschig, Sébastien Gouëzel, Kalle Kytölä, Rob Lewis, Paul
Lez, Luccioli Lorenzo, Heather Macbeth, Patrick Massot, Arend Mellendijk,
Kyle Miller, Pietro Monticone, Kim Morrison, Oliver Nash, Utensil Song,
Terence Tao, Floris van Doorn, Sky Wilshaw, Lawrence Wu.

This single-file port expands project-specific notation, makes additive
declarations explicit, and selects the lemmas used here. The closing
argument derives both |A| ≤ K¹¹|B| and |W| ≤ K¹¹|B| for a single
coset intersection B. A direct application of Ruzsa covering and a
transversal of a subspace of W retain the exponent 12.

The adapted code is licensed under Apache License 2.0. The full upstream
license follows. https://github.com/teorth/pfr/blob/7d6404b79b11/LICENSE
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

/- PFR.Mathlib.MeasureTheory.Constructions.Pi -/
noncomputable section
open scoped ProbabilityTheory
open Function Set

namespace MeasureTheory.Measure
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

instance : IsProbabilityMeasure (.pi μ) :=
  ⟨by simp_rw [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]
lemma pi_pi_set (t : Set ι) [DecidablePred (· ∈ t)] (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ Finset.univ.filter (· ∈ t), μ i (s i) := by
  classical
  simp (config := {singlePass := true}) only [← pi_univ_ite]
  simp_rw [pi_pi, apply_ite, measure_univ,
    Finset.prod_ite, Finset.prod_const_one, mul_one]

@[simp]
lemma pi_eval_preimage (i : ι) (s : Set (α i)) :
    Measure.pi μ (eval i ⁻¹' s) = μ i s := by
  classical
  simp_rw [eval_preimage, pi_pi, apply_update (fun i ↦ μ i), measure_univ,
    Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_const_one, mul_one]

lemma map_eval_pi (i : ι) : Measure.map (eval i) (Measure.pi μ) = μ i := by
  ext s hs
  simp_rw [Measure.map_apply (measurable_pi_apply i) hs, pi_eval_preimage]

end MeasureTheory.Measure
end

/- PFR.Mathlib.Probability.Independence.Kernel.IndepFun -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory.Kernel
variable {ι α β β' γ γ' Ω : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}

section iIndepFun

variable {β γ : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {mγ : ∀ i, MeasurableSpace (γ i)}
  {f : ∀ i, Ω → β i}

lemma iIndepFun.finsets {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) κ μ := by
  classical
  set F := fun (j : J) ↦ fun a (i : S j) ↦ f i a
  let M (j : J) := pi (m := fun (i : S j) ↦ m i)
  let πβ (j : J) := Set.pi Set.univ '' Set.pi Set.univ fun (i : S j) => { s | MeasurableSet[m i] s }
  apply iIndepSets.iIndep
  · intro j
    rw [← measurable_iff_comap_le, measurable_pi_iff]
    intro ω
    simpa [F] using hf_meas ω
  · exact fun i ↦ IsPiSystem.comap isPiSystem_pi (F i)
  · intro j
    change MeasurableSpace.comap _ (M j) = _
    have : M j = MeasurableSpace.generateFrom (πβ j) := generateFrom_pi.symm
    rewrite [this, MeasurableSpace.comap_generateFrom] ; rfl
  simp only [iIndepSets, Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const,
    Subtype.forall, exists_exists_and_eq_and]
  intro s E hE
  obtain ⟨sets, h_sets⟩ := Classical.axiomOfChoice (fun (j:s) ↦ hE j (Finset.coe_mem j))
  set E' := fun (j:s) (i:S j) ↦ f i ⁻¹' (sets j i)
  have Ej_eq (j : s) : E j = ⋂ (i : S j), E' j i := by rw [← (h_sets j).2]; ext ω; simp [E', F]
  suffices ∀ᵐ a ∂μ, κ a (⋂ j : s, ⋂ (i : S j), E' j i) = ∏ j : s, κ a (⋂ (i : S j), E' j i) by
    convert this with x
    · rw [Set.iInter_subtype]
      congr! with j hj
      exact Ej_eq ⟨j, hj⟩
    rw [Finset.prod_subtype s (p := fun j ↦ j ∈ s)]
    · apply Finset.prod_congr rfl
      intro j _
      rw [Ej_eq j]
    simp only [implies_true]
  set E'' := fun (i:ι) ↦ ⋂ (j:s) (h: i ∈ S j), E' j ⟨i, h⟩
  set h_disjoint' :
      (↑s:Set J).PairwiseDisjoint S := Set.PairwiseDisjoint.subset h_disjoint fun ⦃a⦄ _ ↦ trivial
  set t := Finset.disjiUnion s S h_disjoint'
  have Einter_eq : ⋂ (j:s), ⋂ (i : S j), E' j i = ⋂ i ∈ t, E'' i := by
    ext x
    simp only [Set.mem_iInter, Subtype.forall, E'']
    constructor
    · intro h i _ j hj hi
      exact h j hj i hi
    intro h j hj i hi
    have hit : i ∈ t := by simpa [t] using ⟨j, hj, hi⟩
    exact h i hit j hj hi
  have Ej_mes (j : s) : ∀ᵐ (a : α) ∂μ, (κ a) (⋂ (i : S j), E' j i) = ∏ i : S j, (κ a) (E' j i) := by
    convert Kernel.iIndepFun.meas_biInter hf_Indep (S := S j)
      (s := fun i:ι ↦ if h:i ∈ S j then E' j ⟨i, h⟩ else Set.univ) ?_ with x
    · simp +contextual [Set.iInter_subtype, E']
    · simp [Finset.prod_subtype (S j) (p := fun i ↦ i ∈ S j)]
    · intro i hi
      simp only [hi, ↓reduceDIte, E']
      apply MeasurableSet.preimage ((h_sets j).1 i hi) _
      apply Measurable.of_comap_le le_rfl
  have Einter_mes :
      ∀ᵐ a ∂μ, κ a (⋂ j : s, ⋂ i : S j, E' j i) = ∏ j : s, ∏ i : S j, κ a (E' j i) := by
    rw [Einter_eq]
    convert Kernel.iIndepFun.meas_biInter hf_Indep (S := t) (s := E'') ?_ with x
    · rw [Finset.prod_disjiUnion, Finset.prod_subtype s (p := fun j ↦ j ∈ s)]
      · simp only [Finset.univ_eq_attach, E'']
        apply Finset.prod_congr rfl
        intro i _hi
        rw [← Finset.prod_attach (S i)]
        apply Finset.prod_congr rfl
        intro j _hj
        congr
        have : E' i j = ⋂ i', if i' = i then E' i j else Set.univ := by
          rw [Set.iInter_ite]
          simp
        rw [this]
        apply Set.iInter_congr
        intro i'
        split_ifs with h
        · simp only [h, SetLike.coe_mem, subset_refl, Set.coe_inclusion, Set.iInter_true, E']
          ext x
          constructor
          · intro this
            convert this
          intro this
          convert this
          exact h.symm
        · have empty : IsEmpty ((j:ι) ∈ S i') := by
            rw [IsEmpty.prop_iff]
            contrapose! h
            ext
            exact Set.PairwiseDisjoint.elim_finset (f := S) h_disjoint (by trivial) (by trivial) _
              h j.property
          exact (Set.iInter_of_empty _).symm
      · simp only [implies_true]
      · exact FinsetCoe.fintype s
    · intro i _
      simp only [E'', E']
      apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.iInter
      intro hi
      apply MeasurableSet.preimage ((h_sets j).1 i hi)
      apply Measurable.of_comap_le le_rfl
  rw [← Filter.eventually_all] at Ej_mes
  apply Filter.Eventually.mono (Filter.eventually_and.mpr ⟨Ej_mes, Einter_mes⟩)
  intro x ⟨h1, h2⟩
  rw [h2]
  apply Finset.prod_congr rfl
  intro i _
  rw [h1 i]

lemma iIndepFun.finsets_comp {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i))
    (γ : J → Type*) {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) κ μ :=
  (Kernel.iIndepFun.finsets S h_disjoint hf_Indep hf_meas).comp φ hφ

end ProbabilityTheory.Kernel.iIndepFun
end

/- PFR.Mathlib.Probability.Independence.Basic -/
noncomputable section
open scoped ProbabilityTheory
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal

namespace ProbabilityTheory
variable {Ω ι β β' γ : Type*} {κ : ι → Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β}
  {g : Ω → β'}

lemma IndepFun.measureReal_inter_preimage_eq_mul {_mβ : MeasurableSpace β}
    {_mβ' : MeasurableSpace β'} (h : IndepFun f g μ) {s : Set β} {t : Set β'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ.real (f ⁻¹' s ∩ g ⁻¹' t) = μ.real (f ⁻¹' s) * μ.real (g ⁻¹' t) := by
  rw [measureReal_def, h.measure_inter_preimage_eq_mul _ _ hs ht, ENNReal.toReal_mul]; rfl

end ProbabilityTheory

namespace ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}

section IndepFun
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

section iIndepFun

variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}

variable (i : ι) [Inv (α i)] [MeasurableInv (α i)] [DecidableEq ι] in
lemma iIndepFun.inv (h : iIndepFun f μ) : iIndepFun (update f i (f i)⁻¹) μ := by
  convert h.comp (update (fun _ ↦ id) i (·⁻¹)) _ with j
  · by_cases hj : j = i
    · subst hj; ext x; simp
    · simp [hj]
  intro j
  by_cases hj : j = i
  · subst hj; simp [measurable_inv]
  · simp [hj, measurable_id]

variable (i : ι) [Neg (α i)] [MeasurableNeg (α i)] [DecidableEq ι] in
lemma iIndepFun.neg (h : iIndepFun f μ) : iIndepFun (update f i (-(f i))) μ := by
  convert h.comp (update (fun _ ↦ id) i ((-·))) _ with j
  · by_cases hj : j = i
    · subst hj; ext x; simp
    · simp [hj]
  intro j
  by_cases hj : j = i
  · subst hj; simp [measurable_neg]
  · simp [hj, measurable_id]

lemma iIndepFun.finsets {f : ∀ i, Ω → β i} {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a (i : S j) ↦ f i a) μ :=
  Kernel.iIndepFun.finsets S h_disjoint hf_Indep hf_meas

lemma iIndepFun.finsets_comp {f : ∀ i, Ω → β i} {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    {γ : J → Type*} {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) μ :=
  Kernel.iIndepFun.finsets_comp S h_disjoint hf_Indep hf_meas γ φ hφ

lemma iIndepFun.finsetSum [MeasurableSpace β'] [AddCommMonoid β'] [MeasurableAdd₂ β']
    {f : ι → Ω → β'} {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ ∑ i ∈ S j, f i a) μ := by
  set φ : (j : J) → ((i : S j) → β') → β' := fun j f_j ↦ ∑ i : {i : ι // i ∈ S j}, f_j i with φ_def
  have hφ (j : J) : Measurable (φ j) := by
    rw [φ_def]
    simp only [Finset.univ_eq_attach]
    measurability
  have := iIndepFun.finsets_comp S h_disjoint hf_Indep hf_meas φ hφ
  have φ_simple (j : J) (a : Ω) : (φ j (fun i => f ↑i a)) = ∑ i ∈ S j, f i a := by
    simp only [φ_def, Finset.univ_eq_attach, ←Finset.sum_attach (S j)]
  simpa [φ_simple] using this

lemma IndepFun.finsetSum [m : MeasurableSpace β'] [AddCommMonoid β'] [MeasurableAdd₂ β']
    {f : ι → Ω → β'} {s t : Finset ι} (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    (h_disj : Disjoint s t) : IndepFun (∑ i ∈ s, f i) (∑ i ∈ t, f i) μ := by
  let S : Bool → Finset ι := fun b => if b then s else t
  have h_disjoint : Set.PairwiseDisjoint Set.univ S := by
    intro b _ c _ hbc
    by_cases hb : b
    · by_cases hc : c
      · exfalso; exact hbc (hb ▸ hc.symm)
      · simpa [hb, hc, Function.onFun, S] using h_disj
    · by_cases hc : c
      · simpa [hb, hc, Function.onFun, S] using h_disj.symm
      · exfalso; exact hbc (eq_false_of_ne_true hb ▸ (eq_false_of_ne_true hc).symm)
  have hindep := iIndepFun.finsetSum S h_disjoint hf_Indep hf_meas
  have h_true : S true = s := by simp [S]
  have h_false : S false = t := by simp [S]
  rw [← h_true, ← h_false]
  convert hindep.indepFun Bool.true_eq_false_eq_False
  all_goals simp

universe u

lemma iIndepFun.finsets_comp' {f : ∀ i, Ω → β i} {S S' : Finset ι} (h_disjoint : Disjoint S S')
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    {γ γ' : Type u} {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'}
    {φ : (∀ i : S, β i) → γ} {φ' : (∀ i : S', β i) → γ'} (hφ : Measurable φ) (hφ' : Measurable φ') :
    IndepFun (fun a ↦ φ (fun (i : S) ↦ f i a)) (fun a ↦ φ' (fun (i : S') ↦ f i a)) μ := by
  set S₂ := ![S,S']
  set γ₂ := ![γ,γ']
  set φ₂ : (j:Fin 2) → ((i: S₂ j) → β i) → γ₂ j :=
    fun j =>
      match j with
      | 0 => φ
      | 1 => φ'
  have h_disjoint₂ : Set.PairwiseDisjoint Set.univ S₂ := by
    simp_rw [Set.PairwiseDisjoint, Set.Pairwise, Fin.forall_fin_two, Function.onFun]
    simp [h_disjoint, h_disjoint.symm, S₂]
  set mγ₂ : (j:Fin 2) → MeasurableSpace (γ₂ j) := fun j ↦ match j with
  | 0 => mγ
  | 1 => mγ'
  have hφ₂ (j:Fin 2) : Measurable (φ₂ j) := match j with
  | 0 => hφ
  | 1 => hφ'
  have hneq : (0:Fin 2) ≠ (1:Fin 2) := by simp
  simpa [φ₂, γ₂] using!
    (iIndepFun.finsets_comp S₂ h_disjoint₂ hf_Indep hf_meas φ₂ hφ₂).indepFun hneq

end iIndepFun

variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]

@[simp] lemma indepFun_zero_measure {f : Ω → α} {g : Ω → β} : IndepFun f g (0 : Measure Ω) := by
  simp [IndepFun]

lemma indepFun_const [IsZeroOrProbabilityMeasure μ] (c : α) : IndepFun f (fun _ => c) μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rw [IndepFun_iff, MeasurableSpace.comap_const]
  intro t₁ t₂ _ ht₂
  rcases MeasurableSpace.measurableSet_bot_iff.mp ht₂ with h | h
  all_goals simp [h]

lemma indepFun_fst_snd [IsZeroOrProbabilityMeasure μ] {μ'} [IsZeroOrProbabilityMeasure μ'] :
    IndepFun (Prod.fst : Ω × Ω' → Ω) (Prod.snd : Ω × Ω' → Ω') (μ.prod μ') := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ' with rfl | hμ'
  · simp
  rw [IndepFun_iff]
  rintro _ _ ⟨s, _, rfl⟩ ⟨t, _, rfl⟩
  simp [← Set.prod_univ, ← Set.univ_prod, Set.prod_inter_prod]

variable {f : Ω → α} {g : Ω → β}

lemma IndepFun.comp_right {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) :
    IndepFun (f ∘ i) (g ∘ i) (μ.comap i) := by
  change μ (range i)ᶜ = 0 at hi'
  rw [IndepFun_iff] at hfg ⊢
  rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  rw [preimage_comp, preimage_comp, ← preimage_inter, comap_apply, comap_apply, comap_apply,
    image_preimage_eq_inter_range, image_preimage_eq_inter_range, image_preimage_eq_inter_range,
    measure_inter_conull hi', measure_inter_conull hi', measure_inter_conull hi',
    hfg _ _ ⟨_, hs, rfl⟩ ⟨_, ht, rfl⟩]
  all_goals first
  | exact hi.injective
  | exact hi.measurableSet_image'
  | exact hi.measurable <| hf hs
  | exact hi.measurable <| hg ht
  | exact hi.measurable <| (hf hs).inter <| hg ht

end IndepFun
end ProbabilityTheory

namespace ProbabilityTheory
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i, κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}

variable [Fintype ι] [∀ i, Fintype (κ i)]

variable {ι : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
  {α : ∀ i, κ i → Type*} {f : ∀ i j, Ω → α i j} [m : ∀ i j, MeasurableSpace (α i j)]

lemma iIndepFun.pi
    (f_meas : ∀ i j, Measurable (f i j))
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ω j ↦ f i j ω) μ := by
  have (i : ι) : Fintype (κ i) := .ofFinite _
  let F i ω j := f i j ω
  let M (i : ι):= MeasurableSpace.pi (m := m i)
  let πβ (i : ι) := Set.pi Set.univ '' Set.pi Set.univ fun j => { s | MeasurableSet[m i j] s }
  apply iIndepSets.iIndep
  · exact fun i ↦ measurable_iff_comap_le.mp (measurable_pi_iff.mpr (f_meas i))
  · exact fun i ↦ IsPiSystem.comap isPiSystem_pi (F i)
  · intro k
    change MeasurableSpace.comap _ (M k) = _
    have : M k = MeasurableSpace.generateFrom (πβ k) := generateFrom_pi.symm
    rewrite [this, MeasurableSpace.comap_generateFrom] ; rfl
  rw [iIndepSets_iff]
  intro s E hE
  simp only [mem_image, mem_pi, mem_univ, true_implies, exists_exists_and_eq_and] at hE
  have hE' (k : s) := hE k (Finset.coe_mem k)
  classical
  obtain ⟨sets, h_sets⟩ := Classical.axiomOfChoice hE'
  let sets' (i : ι) (j : κ i) : Set (α i j) := if h : i ∈ s then sets ⟨i, h⟩ j else Set.univ
  have box (i : ι) (hi : i ∈ s) : E i = ⋂ j : κ i, (f i j)⁻¹' (sets' i j) := by
    rw [← (h_sets ⟨i, hi⟩).right]
    simp_rw [sets', hi]
    ext : 1
    rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    exact ⟨fun hj j ↦ mem_preimage.mpr (hj j), fun hj j ↦ mem_preimage.mp (hj j)⟩
  let set (i : ι) (j : κ i) := f i j ⁻¹' sets' i j
  set set_σ := fun (ij : (i : ι) × κ i) ↦ set ij.fst ij.snd with set_σ_def
  let meas i j := μ (set i j)
  let meas_σ ij := μ (set_σ ij)
  suffices μ (⋂ i ∈ s, ⋂ j, set i j) = ∏ i ∈ s, μ (⋂ j, set i j) by
    convert this with k hk k hk ; all_goals { exact box k hk }
  let κ_σ (i : ι) := Finset.sigma {i} fun i ↦ Finset.univ (α := κ i)
  have reindex_prod (i : ι) : ∏ j, meas i j = ∏ ij : κ_σ i, meas_σ ij := by
    rw [Finset.prod_coe_sort, Finset.prod_sigma, Finset.prod_singleton]
  have reindex_inter (i : ι) : ⋂ j, set i j = ⋂ ij ∈ κ_σ i, set_σ ij := by
    rw [set_σ_def, Set.biInter_finsetSigma, Finset.set_biInter_singleton]
    simp
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf
  rw [Set.biInter_finsetSigma_univ', hf, Finset.prod_sigma]
  · apply Finset.prod_congr rfl
    intro i hi
    symm
    rw [reindex_prod, reindex_inter, Finset.prod_coe_sort]
    apply hf (κ_σ i) (sets := fun ij ↦ sets' ij.fst ij.snd)
    intro ij hij
    rw [← Finset.mem_singleton.mp (Finset.mem_sigma.mp hij).left] at hi
    simpa [sets', hi] using (h_sets ⟨ij.fst, hi⟩).left ij.snd
  intros ij hij
  obtain ⟨hi, _⟩ := Finset.mem_sigma.mp hij
  simp_rw [sets', hi]
  exact (h_sets ⟨ij.fst, hi⟩).1 ij.snd

lemma iIndepFun.pi' {f : ∀ ij : (Σ i, κ i), Ω → α ij.1 ij.2 }
    (f_meas : ∀ i, Measurable (f i))
    (hf : iIndepFun f μ) :
    iIndepFun (fun i ω ↦ (fun j ↦ f ⟨i, j⟩ ω)) μ :=
  iIndepFun.pi (fun _ _ ↦ f_meas _) hf

variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}

lemma iIndepFun.prod {hf : ∀ (i : ι), Measurable (f i)} {ST : ι' → Finset ι}
    (hS : Pairwise (Disjoint on ST)) (h : iIndepFun f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by
  let g : (i : ι') × ST i → ι := Subtype.val ∘' (Sigma.snd (α := ι'))
  have hg : Injective g := by
    intro x y hxy
    have : ¬(Disjoint on ST) x.fst y.fst := by
      refine not_forall.mpr ⟨{g y}, ?_⟩
      simp
      grind
    exact Sigma.subtype_ext (not_ne_iff.mp ((@hS x.fst y.fst).mt this)) hxy
  let m (i : ι') (j : ST i) : MeasurableSpace (α j) := n j
  exact iIndepFun.pi' (m := m) (hf ∘' g) (h.precomp hg)

variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem EventuallyEq.finite_iInter {ι : Type*} {α : Type u_2} {l : Filter α} (s : Finset ι)
    {E : ι → Set α} {F : ι → Set α}
    (h : ∀ i ∈ s, E i =ᶠ[l] F i) :
    ⋂ i ∈ s, E i =ᶠ[l] ⋂ i ∈ s, F i := by
  unfold Filter.EventuallyEq Filter.Eventually at h ⊢
  simp only [eq_iff_iff] at h ⊢
  rw [← Filter.biInter_finset_mem] at h
  apply Filter.mem_of_superset h
  intro a ha
  change a ∈ ⋂ i ∈ s, E i ↔ a ∈ ⋂ i ∈ s, F i
  simp only [mem_iInter, mem_ofPred_eq] at ha ⊢
  change ∀ i ∈ s, a ∈ E i ↔ a ∈ F i at ha
  exact forall₂_congr ha

theorem iIndepFun.ae_eq {ι : Type*} {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f g : ∀ i, Ω → β i}
    (hf_Indep : iIndepFun f μ) (hfg : ∀ i, f i =ᵐ[μ] g i) : iIndepFun g μ := by
  rw [iIndepFun_iff_iIndep, iIndep_iff] at hf_Indep ⊢
  intro s E H
  have (i : ι) : ∃ E' : Set Ω, MeasurableSet[MeasurableSpace.comap (f i) (m i)] E' ∧
      (i ∈ s → E' =ᵐ[μ] E i) := by
    by_cases hi : i ∈ s
    · obtain ⟨F, mF, hFE⟩ := H i hi
      refine ⟨(f i) ⁻¹' F, ⟨F, mF, rfl⟩, fun _ => ?_⟩
      rw [← hFE]
      exact Filter.EventuallyEq.preimage (hfg i) F
    · exact ⟨∅, @MeasurableSet.empty Ω (MeasurableSpace.comap (f i) (m i)), fun h => (hi h).elim⟩
  classical
  obtain ⟨E', hE'⟩ := Classical.axiomOfChoice this
  have hE'' : ∀ i ∈ s, MeasurableSet[MeasurableSpace.comap (f i) (m i)] (E' i) :=
    fun i _ => (hE' i).1
  have hE''' : ∀ i ∈ s, E' i =ᵐ[μ] E i := fun i hi => (hE' i).2 hi
  convert hf_Indep s hE'' using 1 with i
  · apply measure_congr
    apply EventuallyEq.finite_iInter
    intro i hi
    exact (hE''' i hi).symm
  apply Finset.prod_congr rfl
  intro i hi
  exact measure_congr (hE''' i hi).symm

end ProbabilityTheory
end

/- PFR.Mathlib.Probability.IdentDistrib -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}

lemma identDistrib_iff (f : α → γ) (g : β → γ) (μ : Measure α) (ν : Measure β) :     IdentDistrib f g μ ν ↔ AEMeasurable f μ ∧ AEMeasurable g ν ∧ μ.map f = ν.map g := ⟨fun h => ⟨h.aemeasurable_fst, h.aemeasurable_snd, h.map_eq⟩, fun ⟨hf,hg,h⟩ => ⟨hf,hg,h⟩⟩

lemma identDistrib_id_left {X : α → β} (hX : AEMeasurable X μ) : IdentDistrib id X (μ.map X) μ where
  aemeasurable_fst := aemeasurable_id
  aemeasurable_snd := hX
  map_eq := by simp

lemma identDistrib_id_right {X : α → β} (hX : AEMeasurable X μ) : IdentDistrib X id μ (μ.map X) :=
  (identDistrib_id_left hX).symm

@[simp] lemma identDistrib_id {μ ν : Measure α} : IdentDistrib id id μ ν ↔ μ = ν := by
  simp [identDistrib_iff id id μ ν, aemeasurable_id]

lemma IdentDistrib.fst_id
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν] :
    IdentDistrib Prod.fst id (μ.prod ν) μ := by
  have : μ = (μ.prod ν).map Prod.fst := by simp
  nth_rewrite 2 [this]
  exact identDistrib_id_right measurable_fst.aemeasurable

lemma IdentDistrib.snd_id
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IdentDistrib Prod.snd id (μ.prod ν) ν := by
  have : ν = (μ.prod ν).map Prod.snd := by simp
  nth_rewrite 2 [this]
  exact identDistrib_id_right measurable_snd.aemeasurable

protected lemma IdentDistrib.cond (hs : MeasurableSet s) (hf' : Measurable f') (hg' : Measurable g')
    (hfg : IdentDistrib (fun a ↦ (f a, f' a)) (fun b ↦ (g b, g' b)) μ ν) :
    IdentDistrib f g (μ[|f' ⁻¹' s]) (ν[|g' ⁻¹' s]) where
  aemeasurable_fst := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_fst).mono_ac
    cond_absolutelyContinuous
  aemeasurable_snd := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_snd).mono_ac
    cond_absolutelyContinuous
  map_eq := by
    ext t ht
    rw [map_apply₀ (by exact
      (hfg.comp measurable_fst).aemeasurable_fst.mono_ac cond_absolutelyContinuous)
      ht.nullMeasurableSet, map_apply₀ (by exact
      (hfg.comp measurable_fst).aemeasurable_snd.mono_ac cond_absolutelyContinuous)
      ht.nullMeasurableSet, cond_apply (hg' hs), cond_apply (hf' hs)]
    congr
    · simpa only [map_apply₀ (hfg.comp measurable_snd).aemeasurable_fst hs.nullMeasurableSet,
        map_apply₀ (hfg.comp measurable_snd).aemeasurable_snd hs.nullMeasurableSet]
        using! congr_fun (congr_arg (⇑) (hfg.comp measurable_snd).map_eq) s
    · rw [inter_comm, inter_comm (g' ⁻¹' _)]
      simpa only [map_apply₀ hfg.aemeasurable_fst (ht.prod hs).nullMeasurableSet,
        map_apply₀ hfg.aemeasurable_snd (ht.prod hs).nullMeasurableSet]
        using! congr_fun (congr_arg (⇑) hfg.map_eq) (t ×ˢ s)

lemma identDistrib_comp_left {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) : IdentDistrib (f ∘ i) f (μ.comap i) μ where
  aemeasurable_fst := (hf.comp hi.measurable).aemeasurable
  aemeasurable_snd := hf.aemeasurable
  map_eq := by rw [← Measure.map_map hf hi.measurable, hi.map_comap, restrict_eq_self_of_ae_mem hi']

lemma identDistrib_comp_right {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) : IdentDistrib f (f ∘ i) μ (μ.comap i) :=
  (identDistrib_comp_left hi hi' hf).symm

lemma IdentDistrib.comp_left {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hfg : IdentDistrib f g μ ν) : IdentDistrib (f ∘ i) g (μ.comap i) ν :=
  (identDistrib_comp_left hi hi' hf).trans hfg

lemma IdentDistrib.comp_right {i : δ → β} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂ν, a ∈ range i)
    (hg : Measurable g) (hfg : IdentDistrib f g μ ν) : IdentDistrib f (g ∘ i) μ (ν.comap i) :=
  hfg.trans <| identDistrib_comp_right hi hi' hg

end ProbabilityTheory

open MeasureTheory ProbabilityTheory Function Set

namespace ProbabilityTheory
section IdentDistrib
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω → β} {f' g' : Ω' → β}

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem IdentDistrib.pfrProdMk (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
    (h : IndepFun f g μ) (h' : IndepFun f' g' ν) :
    IdentDistrib (fun x ↦ (f x, g x)) (fun x ↦ (f' x, g' x)) μ ν where
  aemeasurable_fst := hff'.aemeasurable_fst.prodMk hgg'.aemeasurable_fst
  aemeasurable_snd := hff'.aemeasurable_snd.prodMk hgg'.aemeasurable_snd
  map_eq := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hff'.aemeasurable_fst hgg'.aemeasurable_fst] at h
    rw [indepFun_iff_map_prod_eq_prod_map_map hff'.aemeasurable_snd hgg'.aemeasurable_snd] at h'
    rw [h, h', hff'.map_eq, hgg'.map_eq]

lemma AEMeasurable.piMk {I : Type*} [Countable I] {F : I → Ω → β} (hF : ∀ i, AEMeasurable (F i) μ) :
    AEMeasurable (fun x i => F i x) μ := by
  refine ⟨fun x i => (hF i).mk (F i) x, measurable_pi_lambda _ (fun i => (hF i).measurable_mk), ?_ ⟩
  filter_upwards [eventually_countable_forall.mpr (fun i ↦ (hF i).ae_eq_mk)] with ω hω
  ext i; exact hω i

variable [Mul β] [MeasurableMul₂ β] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem IdentDistrib.mul
    (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
    (h : IndepFun f g μ) (h' : IndepFun f' g' ν) :
    IdentDistrib (f * g) (f' * g') μ ν :=
  hff'.pfrProdMk hgg' h h' |>.comp_of_aemeasurable measurable_mul.aemeasurable

variable [Add β] [MeasurableAdd₂ β] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem IdentDistrib.add
    (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
    (h : IndepFun f g μ) (h' : IndepFun f' g' ν) :
    IdentDistrib (f + g) (f' + g') μ ν :=
  hff'.pfrProdMk hgg' h h' |>.comp_of_aemeasurable measurable_add.aemeasurable

variable [MeasurableSpace α] [MeasurableSpace β]

lemma identDistrib_map {X : Ω → α} (hX : Measurable X) {f : α → β} (hf : Measurable f)
    (μ : Measure Ω) : IdentDistrib f (f ∘ X) (μ.map X) μ where
  aemeasurable_fst := hf.aemeasurable
  aemeasurable_snd := (hf.comp hX).aemeasurable
  map_eq := map_map hf hX

lemma identDistrib_ulift_self {X : Ω → α} (hX : Measurable X) :
    IdentDistrib X (X ∘ ULift.down) μ (μ.comap ULift.down) := by
  have hX' : Measurable (X ∘ ULift.down : ULift Ω → α) := hX.comp measurable_down
  refine ⟨hX.aemeasurable, hX'.aemeasurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (μ := (μ.comap ULift.down)) hX' hs,
    Measure.comap_apply _ ULift.down_injective _ _ (hX' hs), Set.preimage_comp,
    Set.image_preimage_eq _ ULift.down_surjective, Measure.map_apply hX hs]
  intro s hs
  change MeasurableSet (ULift.down ⁻¹' (ULift.down '' s))
  rwa [Set.preimage_image_eq _ ULift.down_injective]

lemma identDistrib_of_sum {X : Ω → α} {Y : Ω' → α} {μ : T → Measure Ω}
    {μ' : T → Measure Ω'} {w : T → ENNReal} (s : Finset T) (hX : Measurable X) (hY : Measurable Y)
    (h_ident : ∀ y, w y ≠ 0 → IdentDistrib X Y (μ y) (μ' y)) :
    IdentDistrib X Y (∑ y ∈ s, (w y) • (μ y)) (∑ y ∈ s, (w y) • (μ' y)) where
  aemeasurable_fst := hX.aemeasurable
  aemeasurable_snd := hY.aemeasurable
  map_eq := by
    rw [← Measure.mapₗ_apply_of_measurable hX, ← Measure.mapₗ_apply_of_measurable hY]
    simp only [_root_.map_sum, map_smul]
    congr with y E _
    rcases eq_or_ne (w y) 0 with hy | hy
    · simp [hy]
    congr 3
    rw [Measure.mapₗ_apply_of_measurable hX, Measure.mapₗ_apply_of_measurable hY]
    exact (h_ident y hy).map_eq

lemma identDistrib_comp_fst {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ'] : IdentDistrib (X ∘ Prod.fst) X (μ.prod μ') μ where
  aemeasurable_fst := (hX.comp measurable_fst).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [← Measure.map_map hX measurable_fst, Measure.map_fst_prod]
    congr
    simp

lemma identDistrib_comp_snd {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) (μ' : Measure Ω')
  [SigmaFinite μ] [IsProbabilityMeasure μ'] : IdentDistrib (X ∘ Prod.snd) X (μ'.prod μ) μ where
  aemeasurable_fst := (hX.comp measurable_snd).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [← Measure.map_map hX measurable_snd, Measure.map_snd_prod]
    congr
    simp

lemma independent_copies {X : Ω → α} {Y : Ω' → β} (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    ∃ ν : Measure (α × β), ∃ X' : α × β → α, ∃ Y' : α × β → β, IsProbabilityMeasure ν
      ∧ Measurable X' ∧ Measurable Y' ∧ IndepFun X' Y' ν
      ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' := by
  have := Measure.isProbabilityMeasure_map hX.aemeasurable (μ := μ)
  have := Measure.isProbabilityMeasure_map hY.aemeasurable (μ := μ')
  exact ⟨(μ.map X).prod (μ'.map Y), _, _, inferInstance, measurable_fst, measurable_snd,
    indepFun_fst_snd, ⟨measurable_fst.aemeasurable, hX.aemeasurable, by simp⟩,
    measurable_snd.aemeasurable, hY.aemeasurable, by simp⟩

lemma independent_copies_two {Ω : Type u} {Ω' : Type v} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')]
    {X : Ω → α} {Y : Ω' → β} (hX : Measurable X) (hY : Measurable Y) :
    ∃ (Ω'' : Type (max u v)) (m'' : MeasureSpace Ω'') (X' : Ω'' → α) (Y' : Ω'' → β),
    IsProbabilityMeasure (ℙ : Measure Ω'') ∧ Measurable X' ∧ Measurable Y' ∧
      IndepFun X' Y' ∧ IdentDistrib X' X ∧ IdentDistrib Y' Y := by
  refine ⟨Ω × Ω', by infer_instance, X ∘ Prod.fst, Y ∘ Prod.snd, by infer_instance,
    hX.comp measurable_fst, hY.comp measurable_snd, ?_, ?_, ?_⟩
  · exact indepFun_fst_snd.comp hX hY
  · refine ⟨(hX.comp measurable_fst).aemeasurable, hX.aemeasurable, ?_⟩
    have : (ℙ : Measure (Ω × Ω')) = (ℙ : Measure Ω).prod (ℙ : Measure Ω') := rfl
    simp [← Measure.map_map hX measurable_fst, this]
  · refine ⟨(hY.comp measurable_snd).aemeasurable, hY.aemeasurable, ?_⟩
    have : (ℙ : Measure (Ω × Ω')) = (ℙ : Measure Ω).prod (ℙ : Measure Ω') := rfl
    simp [← Measure.map_map hY measurable_snd, this]

lemma independent_copies' {I : Type u} [Finite I] {α : I → Type u'}
    [mS : ∀ i : I, MeasurableSpace (α i)] {Ω : I → Type v}
    [mΩ : ∀ i : I, MeasurableSpace (Ω i)] (X : ∀ i : I, Ω i → α i) (hX : ∀ i : I, Measurable (X i))
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ (A : Type (max u v)) (_ : MeasurableSpace A) (μA : Measure A) (X' : ∀ i, A → α i),
    IsProbabilityMeasure μA ∧ iIndepFun X' μA ∧
    ∀ i : I, Measurable (X' i) ∧ IdentDistrib (X' i) (X i) μA (μ i) := by
  cases nonempty_fintype I
  refine ⟨Π i, Ω i, inferInstance, .pi μ, fun i ↦ X i ∘ eval i, inferInstance, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [iIndepFun_iff]
    intro t s hs
    choose! u _ hus using hs
    simp +contextual only [← hus, preimage_comp, pi_eval_preimage]
    simp_rw [← Finset.mem_coe, ← Set.pi_def, pi_pi_finset]
  · exact (hX i).comp (measurable_pi_apply i)
  · refine ⟨(hX i).comp (measurable_pi_apply i) |>.aemeasurable, (hX i).aemeasurable, ?_⟩
    rw [← Measure.map_map (hX i) (measurable_pi_apply i), Measure.map_eval_pi]

lemma independent_copies3_nondep {α : Type u}
    [mS : MeasurableSpace α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃] :
    ∃ (A : Type (max u_1 u_2 u_3)) (_ : MeasurableSpace A) (μA : Measure A) (X₁' X₂' X₃' : A → α),
      IsProbabilityMeasure μA ∧ iIndepFun ![X₁', X₂', X₃'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ := by
  let Ω₁' : Type (max u_1 u_2 u_3) := ULift.{max u_2 u_3} Ω₁
  let Ω₂' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_3} Ω₂
  let Ω₃' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_2} Ω₃
  let Ω : Fin 3 → Type (max u_1 u_2 u_3) := ![Ω₁', Ω₂', Ω₃']
  let mΩ : (i : Fin 3) → MeasurableSpace (Ω i) :=
    Fin.cases (inferInstance : MeasurableSpace Ω₁') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₂') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₃') Fin.rec0
  let X : (i : Fin 3) → Ω i → α := Fin.cases (X₁ ∘ ULift.down) <| Fin.cases (X₂ ∘ ULift.down) <|
    Fin.cases (X₃ ∘ ULift.down) Fin.rec0
  have hX : ∀ (i : Fin 3), @Measurable _ _ (mΩ i) mS (X i) :=
    Fin.cases (hX₁.comp measurable_down) <|
    Fin.cases (hX₂.comp measurable_down) <|
    Fin.cases (hX₃.comp measurable_down) Fin.rec0
  let μ : (i : Fin 3) → @Measure (Ω i) (mΩ i) :=
    Fin.cases (μ₁.comap ULift.down) <|
    Fin.cases (μ₂.comap ULift.down) <|
    Fin.cases (μ₃.comap ULift.down) Fin.rec0
  have hμ : (i : Fin 3) → IsProbabilityMeasure (μ i) :=
    Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down Fin.rec0
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' X hX μ
  refine ⟨A, mA, μA, X' 0, X' 1, X' 2, hμ, ?_,
    (hX' 0).1, (hX' 1).1, (hX' 2).1,
    (hX' 0).2.trans ((identDistrib_ulift_self hX₁).symm),
    (hX' 1).2.trans (identDistrib_ulift_self hX₂).symm,
    (hX' 2).2.trans (identDistrib_ulift_self hX₃).symm⟩
  convert hi; ext i; fin_cases i <;> rfl

lemma independent_copies4_nondep {α : Type u}
    [mS : MeasurableSpace α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3} {Ω₄ : Type u_4}
    [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    [mΩ₃ : MeasurableSpace Ω₃] [mΩ₄ : MeasurableSpace Ω₄]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α} {X₄ : Ω₄ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃) (hX₄ : Measurable X₄)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃) (μ₄ : Measure Ω₄)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂]
    [hμ₃ : IsProbabilityMeasure μ₃] [hμ₄ : IsProbabilityMeasure μ₄] :
    ∃ (A : Type (max u_1 u_2 u_3 u_4)) (_ : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' X₄' : A → α),
    IsProbabilityMeasure μA ∧ iIndepFun ![X₁', X₂', X₃', X₄'] μA ∧
    Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧ Measurable X₄' ∧
    IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧
    IdentDistrib X₃' X₃ μA μ₃ ∧ IdentDistrib X₄' X₄ μA μ₄ := by
  let Ω₁' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_2 u_3 u_4} Ω₁
  let Ω₂' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_1 u_3 u_4} Ω₂
  let Ω₃' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_1 u_2 u_4} Ω₃
  let Ω₄' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_1 u_2 u_3} Ω₄
  let Ω : Fin 4 → Type (max u_1 u_2 u_3 u_4) := ![Ω₁', Ω₂', Ω₃', Ω₄']
  let mΩ : (i : Fin 4) → MeasurableSpace (Ω i) :=
    Fin.cases (inferInstance : MeasurableSpace Ω₁') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₂') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₃') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₄') Fin.rec0
  let X : (i : Fin 4) → Ω i → α :=
    Fin.cases (X₁ ∘ ULift.down) <| Fin.cases (X₂ ∘ ULift.down) <|
    Fin.cases (X₃ ∘ ULift.down) <| Fin.cases (X₄ ∘ ULift.down) Fin.rec0
  have hX : ∀ (i : Fin 4), @Measurable _ _ (mΩ i) mS (X i) :=
    Fin.cases (hX₁.comp measurable_down) <| Fin.cases (hX₂.comp measurable_down) <|
    Fin.cases (hX₃.comp measurable_down) <| Fin.cases (hX₄.comp measurable_down) Fin.rec0
  let μ : (i : Fin 4) → @Measure (Ω i) (mΩ i) :=
    Fin.cases (μ₁.comap ULift.down) <| Fin.cases (μ₂.comap ULift.down) <|
    Fin.cases (μ₃.comap ULift.down) <| Fin.cases (μ₄.comap ULift.down) Fin.rec0
  let hμ : (i : Fin 4) → IsProbabilityMeasure (μ i) :=
    Fin.cases isProbabilityMeasure_comap_down <| Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down <| Fin.cases isProbabilityMeasure_comap_down Fin.rec0
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' X hX μ
  refine ⟨A, mA, μA, X' 0, X' 1, X' 2, X' 3, hμ, ?_,
    (hX' 0).1, (hX' 1).1, (hX' 2).1, (hX' 3).1,
    (hX' 0).2.trans ((identDistrib_ulift_self hX₁).symm),
    (hX' 1).2.trans ((identDistrib_ulift_self hX₂).symm),
    (hX' 2).2.trans ((identDistrib_ulift_self hX₃).symm),
    (hX' 3).2.trans ((identDistrib_ulift_self hX₄).symm)⟩
  convert hi; ext i; fin_cases i <;> rfl

end IdentDistrib
end ProbabilityTheory
end

/- PFR.ForMathlib.FiniteRange.Defs -/
noncomputable section
open scoped ProbabilityTheory
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite

noncomputable abbrev FiniteRange.fintype {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Fintype (Set.range X) := hX.finite.fintype

noncomputable def FiniteRange.toFinset {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] : Finset G :=
    @Set.toFinset _ _ hX.fintype

instance {Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X where
  finite := Set.toFinite (Set.range X)

example {Ω G : Type*} (X : Ω → G) [Fintype G] : FiniteRange X := by infer_instance

lemma finiteRange_of_finset {Ω G : Type*} (f : Ω → G) (A : Finset G) (h : ∀ ω, f ω ∈ A) :
    FiniteRange f := by
  constructor
  apply Set.Finite.subset (Finset.finite_toSet A)
  intro y hy
  simp only [Set.mem_range] at hy
  rcases hy with ⟨ω, rfl⟩
  exact h ω

lemma FiniteRange.range {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Set.range X = FiniteRange.toFinset X := by simp [FiniteRange.toFinset]

lemma FiniteRange.mem {Ω G : Type*} (X : Ω → G) [FiniteRange X] (ω : Ω) :
    X ω ∈ FiniteRange.toFinset X := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range, exists_apply_eq_apply]

@[simp]
lemma FiniteRange.mem_iff {Ω G : Type*} (X : Ω → G) [FiniteRange X] (x : G) :
    x ∈ FiniteRange.toFinset X ↔ ∃ ω, X ω = x := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range]

instance {Ω G : Type*} (c : G) : FiniteRange (fun _ : Ω ↦ c) := by
  apply finiteRange_of_finset _ { c }
  simp

instance {Ω G H : Type*} (X : Ω → G) (f : G → H) [hX : FiniteRange X] : FiniteRange (f ∘ X) where
  finite := (Set.range_comp f X) ▸ Set.Finite.image f hX.finite

instance {Ω Ω' G : Type*} (X : Ω → G) (f : Ω' → Ω) [hX : FiniteRange X] : FiniteRange (X ∘ f) := by
  apply finiteRange_of_finset _ (FiniteRange.toFinset X)
  intro ω
  exact FiniteRange.mem X (f ω)

instance {Ω G H : Type*} (X : Ω → G) (Y : Ω → H) [hX : FiniteRange X] [hY : FiniteRange Y] :
    FiniteRange fun ω ↦ (X ω, Y ω) where
  finite := (hX.finite.prod hY.finite).subset (Set.range_pair_subset ..)

instance FiniteRange.mul {Ω G : Type*} (X Y : Ω → G) [Mul G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange (X * Y) := by
  change FiniteRange ((fun p ↦ p.1 * p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

instance FiniteRange.add {Ω G : Type*} (X Y : Ω → G) [Add G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange (X + Y) := by
  change FiniteRange ((fun p ↦ p.1 + p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

instance FiniteRange.mul' {Ω G : Type*} (X Y : Ω → G) [Mul G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω * Y ω := FiniteRange.mul ..

instance FiniteRange.add' {Ω G : Type*} (X Y : Ω → G) [Add G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω + Y ω := FiniteRange.add ..

instance FiniteRange.div {Ω G : Type*} (X Y : Ω → G) [Div G]
    [hX : FiniteRange X] [hY : FiniteRange Y] : FiniteRange (X/Y) := by
  change FiniteRange ((fun p ↦ p.1 / p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

instance FiniteRange.sub {Ω G : Type*} (X Y : Ω → G) [Sub G]
    [hX : FiniteRange X] [hY : FiniteRange Y] : FiniteRange (X-Y) := by
  change FiniteRange ((fun p ↦ p.1 - p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

instance FiniteRange.div' {Ω G : Type*} (X Y : Ω → G) [Div G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω / Y ω := FiniteRange.div ..

instance FiniteRange.sub' {Ω G : Type*} (X Y : Ω → G) [Sub G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω - Y ω := FiniteRange.sub ..

instance FiniteRange.inv {Ω G : Type*} (X : Ω → G) [Inv G] [hX : FiniteRange X] :
    FiniteRange X⁻¹ := by
  change FiniteRange ((fun p ↦ p⁻¹) ∘ X)
  infer_instance

instance FiniteRange.neg {Ω G : Type*} (X : Ω → G) [Neg G] [hX : FiniteRange X] :
    FiniteRange (-X) := by
  change FiniteRange ((fun p ↦ (-p)) ∘ X)
  infer_instance

instance FiniteRange.inv' {Ω G : Type*} (X : Ω → G) [Inv G] [FiniteRange X] :
    FiniteRange fun ω ↦ (X ω)⁻¹ := FiniteRange.inv _

instance FiniteRange.neg' {Ω G : Type*} (X : Ω → G) [Neg G] [FiniteRange X] :
    FiniteRange fun ω ↦ (-X ω) := FiniteRange.neg _

instance FiniteRange.zpow {Ω G : Type*} (X : Ω → G) [Pow G ℤ] [hX : FiniteRange X] (n : ℤ) :
    FiniteRange (X ^ n) := by
  change FiniteRange ((· ^ n) ∘ X)
  infer_instance

instance FiniteRange.zsmul {Ω G : Type*} (X : Ω → G) [SMul ℤ G] [hX : FiniteRange X] (n : ℤ) :
    FiniteRange (n • X) := by
  change FiniteRange ((n • ·) ∘ X)
  infer_instance

instance FiniteRange.zpow' {Ω G : Type*} (X : Ω → G) [Pow G ℤ] [FiniteRange X] (n : ℤ) :
    FiniteRange fun ω ↦ X ω ^ n := FiniteRange.zpow ..

instance FiniteRange.zsmul' {Ω G : Type*} (X : Ω → G) [SMul ℤ G] [FiniteRange X] (n : ℤ) :
    FiniteRange fun ω ↦ n • X ω := FiniteRange.zsmul ..

instance FiniteRange.finprod {Ω G I : Type*} [CommMonoid G] {s : Finset I} (X : I → Ω → G)
    [∀ i, FiniteRange (X i)] :
    FiniteRange (∏ i ∈ s, X i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    change FiniteRange (fun _ ↦ 1)
    infer_instance
  | @insert k s hk IH =>
    classical
    have h_eq : ∏ j ∈ insert k s, X j = X k * ∏ j ∈ s, X j := Finset.prod_insert hk
    suffices h : FiniteRange (X k * ∏ j ∈ s, X j) from by
      convert h
      exact h_eq
    exact FiniteRange.mul (X k) (∏ j ∈ s, X j)

instance FiniteRange.finsum {Ω G I : Type*} [AddCommMonoid G] {s : Finset I} (X : I → Ω → G)
    [∀ i, FiniteRange (X i)] :
    FiniteRange (∑ i ∈ s, X i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change FiniteRange (fun _ ↦ 0)
    infer_instance
  | @insert k s hk IH =>
    classical
    have h_eq : ∑ j ∈ insert k s, X j = X k + ∑ j ∈ s, X j := Finset.sum_insert hk
    suffices h : FiniteRange (X k + ∑ j ∈ s, X j) from by
      convert h
      exact h_eq
    exact FiniteRange.add (X k) (∑ j ∈ s, X j)

open MeasureTheory

lemma FiniteRange.full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X) (FiniteRange.toFinset X) = μ Set.univ := by
  rw [Measure.map_apply hX (by measurability)]
  congr
  ext ω
  simp

lemma FiniteRange.real_full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X).real (FiniteRange.toFinset X) = μ.real Set.univ := by
  simp [measureReal_def, FiniteRange.full hX]

lemma FiniteRange.null_of_compl {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) [FiniteRange X] :
    (μ.map X) (FiniteRange.toFinset X : Set G)ᶜ = 0 := by
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply₀ hX (by measurability)]
    convert measure_empty (μ := μ)
    ext ω
    simp
  · simp [hX]

lemma FiniteRange.ae_mem_toFinset {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) [FiniteRange X] :
    ∀ᵐ x ∂(μ.map X), x ∈ (FiniteRange.toFinset X : Set G) := FiniteRange.null_of_compl ..
end

/- PFR.ForMathlib.FiniteRange.ConditionalProbability -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory Set

namespace ProbabilityTheory
variable {Ω α : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
 [MeasurableSpace α] [MeasurableSingletonClass α]

lemma sum_meas_smul_cond_fiber' {X : Ω → α} (hX : Measurable X) [finX : FiniteRange X]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∑ x ∈ finX.toFinset, μ (X ⁻¹' {x}) • μ[|X ← x] = μ := by
  ext E hE
  calc
    _ = ∑ x ∈ finX.toFinset, μ (X ⁻¹' {x} ∩ E) := by
      simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (μ _), cond_mul_eq_inter (hX (.singleton _))]
    _ = _ := by
      have : ⋃ x ∈ finX.toFinset, X ⁻¹' {x} ∩ E = E := by ext _; simp
      rw [← measure_biUnion_finset _ fun _ _ ↦ (hX (.singleton _)).inter hE, this]
      aesop (add simp [PairwiseDisjoint, Set.Pairwise, Function.onFun, disjoint_left])

end ProbabilityTheory
end

/- PFR.ForMathlib.Pair -/
noncomputable section
open scoped ProbabilityTheory
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)

@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    ((_root_.prod X Y) : Ω → S × T) ω = (X ω, Y ω) := rfl
end

/- PFR.ForMathlib.ConditionalIndependence -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory Measure Set
open scoped ENNReal

namespace ProbabilityTheory

section

variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}

theorem IndepFun.identDistrib_cond [IsProbabilityMeasure μ]
    (hi : IndepFun A B μ) {s : Set β}
    (hs : MeasurableSet s) (hA : Measurable A) (hB : Measurable B)
    (h : μ (B ⁻¹' s) ≠ 0) :
    IdentDistrib A A μ (μ[|B ⁻¹' s]) := by
  refine ⟨hA.aemeasurable, hA.aemeasurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hA ht, Measure.map_apply hA ht, cond_apply (hB hs), Set.inter_comm,
    hi.measure_inter_preimage_eq_mul _ _ ht hs, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel h (by finiteness), mul_one]

lemma IndepFun.cond_left (hi : IndepFun A B μ) {s : Set α}
    (hs : MeasurableSet s) (hA : Measurable A) :
    IndepFun A B (μ[| A⁻¹' s]) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.2 (fun u v hu hv ↦ ?_)
  have : A ⁻¹' s ∩ (A ⁻¹' u ∩ B ⁻¹' v) = A ⁻¹' (s ∩ u) ∩ B ⁻¹' v := by aesop
  simp only [cond_apply (hA hs), this]
  rcases eq_or_ne (μ (A ⁻¹' s)) ∞ with h|h
  · simp [h]
  rcases eq_or_ne (μ (A ⁻¹' s)) 0 with h'|h'
  · have I : μ (A ⁻¹' (s ∩ u) ∩ B ⁻¹' v) = 0 := by
      apply le_antisymm ((measure_mono _).trans h'.le) bot_le
      exact inter_subset_left.trans (preimage_mono inter_subset_left)
    have J : μ (A ⁻¹' s ∩ B ⁻¹' v) = 0 :=
      le_antisymm ((measure_mono inter_subset_left).trans h'.le) bot_le
    simp only [I, J, mul_zero]
  · rw [hi.measure_inter_preimage_eq_mul _ _ (hs.inter hu) hv, Set.preimage_inter,
      hi.measure_inter_preimage_eq_mul _ _ hs hv, ← mul_assoc (μ (A ⁻¹' s))⁻¹,
      ← mul_assoc (μ (A ⁻¹' s))⁻¹, ENNReal.inv_mul_cancel h' h, one_mul]

lemma IndepFun.cond (hi : IndepFun A B μ) {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hA : Measurable A) (hB : Measurable B) :
    IndepFun A B (μ[| A ⁻¹' s ∩ B ⁻¹' t]) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.2 (fun u v hu hv ↦ ?_)
  have I1 : A ⁻¹' s ∩ B ⁻¹' t ∩ (A ⁻¹' u ∩ B ⁻¹' v) = A ⁻¹' (s ∩ u) ∩ B ⁻¹' (t ∩ v) := by aesop
  have I2 : A ⁻¹' s ∩ B ⁻¹' t ∩ A ⁻¹' u = A ⁻¹' (s ∩ u) ∩ B ⁻¹' t := by aesop
  have I3 : A ⁻¹' s ∩ B ⁻¹' t ∩ B ⁻¹' v = A ⁻¹' s ∩ B ⁻¹' (t ∩ v) := by aesop
  simp only [cond_apply ((hA hs).inter (hB ht)), I1, I2, I3]
  rcases eq_or_ne (μ (A ⁻¹' s ∩ B⁻¹' t)) ∞ with h|h
  · simp [h]
  rcases eq_or_ne (μ (A ⁻¹' s ∩ B⁻¹' t)) 0 with h'|h'
  · have I : μ (A ⁻¹' (s ∩ u) ∩ B ⁻¹' (t ∩ v)) = 0 := by
      apply le_antisymm ((measure_mono _).trans h'.le) bot_le
      exact inter_subset_inter (preimage_mono inter_subset_left)
        (preimage_mono inter_subset_left)
    have J : μ (A ⁻¹' (s ∩ u) ∩ B ⁻¹' t) = 0 := by
      apply le_antisymm ((measure_mono _).trans h'.le) bot_le
      exact inter_subset_inter_left _ (preimage_mono inter_subset_left)
    simp only [I, J, mul_zero, zero_mul]
  · simp only [hi.measure_inter_preimage_eq_mul _ _ hs ht, ne_eq, mul_eq_zero, not_or] at h'
    simp only [hi.measure_inter_preimage_eq_mul _ _ hs ht, ne_eq, ENNReal.mul_eq_top, h'.1,
      not_false_eq_true, true_and, h'.2, and_true, not_or] at h
    rw [mul_assoc]
    congr 1
    rw [hi.measure_inter_preimage_eq_mul _ _ (hs.inter hu) (ht.inter hv),
      hi.measure_inter_preimage_eq_mul _ _ (hs.inter hu) ht,
      hi.measure_inter_preimage_eq_mul _ _ hs ht,
      hi.measure_inter_preimage_eq_mul _ _ hs (ht.inter hv),
      ENNReal.mul_inv (Or.inl h'.1) (Or.inr h'.2), mul_assoc]
    congr 1
    have : μ (B ⁻¹' t) * ((μ (A ⁻¹' s))⁻¹ * (μ (B ⁻¹' t))⁻¹ * (μ (A ⁻¹' s) * μ (B ⁻¹' (t ∩ v))))
      = (μ (B ⁻¹' t) * (μ (B ⁻¹' t))⁻¹) * ((μ (A ⁻¹' s))⁻¹ * μ (A ⁻¹' s)) * μ (B ⁻¹' (t ∩ v)) := by
        ring
    rw [this, ENNReal.inv_mul_cancel h'.1 h.2, ENNReal.mul_inv_cancel h'.2 h.1, one_mul, one_mul]

end

section defs
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {h : Ω → γ}

def PfrCondIndepFun (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z])

lemma pfrCondIndepFun_iff : PfrCondIndepFun f g h μ ↔ ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z]) := by rfl

variable [MeasurableSingletonClass γ]

lemma PfrCondIndepFun.comp_right {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hfg : PfrCondIndepFun f g h μ) :
    PfrCondIndepFun (f ∘ i) (g ∘ i) (h ∘ i) (μ.comap i) := by
  rw [pfrCondIndepFun_iff] at hfg ⊢
  rw [← Measure.map_map hh hi.measurable, hi.map_comap, restrict_eq_self_of_ae_mem hi']
  refine hfg.mono <| fun c hc ↦ ?_
  rw [preimage_comp, ← comap_cond hi hi' <| hh <| .singleton _]
  exact IndepFun.comp_right hi (cond_absolutelyContinuous.ae_le hi') hf hg hc

end defs

section copy
universe u
variable {Ω : Type*} {α β : Type u} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]

variable [Countable β] 

open Function Set Measure

lemma condIndep_copies (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    [finY : FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      PfrCondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib ((_root_.prod X₁ Y')) ((_root_.prod X Y)) ν μ ∧
      IdentDistrib ((_root_.prod X₂ Y')) ((_root_.prod X Y)) ν μ := by
  let m' := fun (y : β) ↦ ((μ[|Y ← y]).map X)
  let m := fun (y : β) ↦ ((m' y).prod (m' y)).prod (Measure.dirac y)
  let ν : Measure ((α × α) × β) := ∑ y ∈ finY.toFinset, ((μ (Y ⁻¹' {y})) • (m y))
  have h3' (y : β) : { ω : Ω | Y ω = y } ∈ ae (μ[|Y ← y]) := by
    rw [mem_ae_iff, ← cond_inter_self]
    · have : (Y ⁻¹' {y}) ∩ { ω : Ω | Y ω = y }ᶜ = ∅ := by
        ext _; simp
      simp [this]
    exact hY <| .singleton y
  have h3 (y : β) : IdentDistrib (fun ω ↦ (X ω, y)) ((_root_.prod X Y)) (μ[|Y ← y]) (μ[|Y ← y]) := by
    apply IdentDistrib.of_ae_eq (hX.prodMk measurable_const).aemeasurable
    apply Filter.eventuallyEq_of_mem (h3' y)
    intro ω; simp only [mem_ofPred_eq, Prod.mk.injEq, true_and]; exact fun a ↦ id a.symm
  have h4 (y : β) : { ω : (α × α) × β| ω.2 = y } ∈ ae (m y) := by
    rw [mem_ae_iff]
    have : { ω : (α × α) × β | ω.2 = y}ᶜ = Prod.snd⁻¹' {y}ᶜ := by
      simp only [preimage_compl, compl_inj_iff]
      rfl
    rw [this, ← Measure.map_apply measurable_snd (MeasurableSet.singleton y).compl]
    simp [m]
  have h5 {y : β} (hy : μ (Y ⁻¹' {y}) ≠ 0) : IsProbabilityMeasure (m' y) := by
    have : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure hy
    exact isProbabilityMeasure_map hX.aemeasurable
  have h1 : ν.map Prod.snd = μ.map Y := by
    rw [← sum_meas_smul_cond_fiber' hY μ, ← Measure.mapₗ_apply_of_measurable measurable_snd,
      ← Measure.mapₗ_apply_of_measurable hY]
    simp only [_root_.map_sum, LinearMapClass.map_smul, ν]
    congr with y
    rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
    · simp [hy]
    have h6 : IsProbabilityMeasure (m' y) := h5 hy
    have h7 : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure hy
    congr 3
    rw [Measure.mapₗ_apply_of_measurable measurable_snd, Measure.mapₗ_apply_of_measurable hY]
    simp only [map_snd_prod, measure_univ, one_smul, m]
    have := (μ[|Y ← y]).map_const y
    simp only [measure_univ, one_smul] at this; rw [← this]
    apply Measure.map_congr
    apply Filter.eventuallyEq_of_mem (h3' y)
    intro ω; simp only [mem_ofPred_eq]; exact fun a ↦ a.symm
  refine ⟨(α × α) × β, by infer_instance, fun ω ↦ ω.1.1, fun ω ↦ ω.1.2, fun ω ↦ ω.2, ν, ?_,
    measurable_fst.comp measurable_fst, measurable_snd.comp measurable_fst,
    measurable_snd, ?_, ?_, ?_⟩
  · constructor
    simp only [coe_finsetSum, Finset.sum_apply, ν]
    have : ∑ y ∈ finY.toFinset, μ (Y ⁻¹' {y}) * 1 = 1 := by
      simp only [mul_one]
      rw [sum_measure_preimage_singleton]
      · rw [← FiniteRange.range Y, preimage_range, measure_univ]
      · exact fun y _ ↦ hY <| .singleton y
    rw [← this]
    congr with y
    rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
    · simp [hy]
    have : IsProbabilityMeasure (m' y) := h5 hy
    simp
  · rw [pfrCondIndepFun_iff, ae_iff_of_countable]
    intro y hy
    have hy' : ν (Prod.snd⁻¹' {y}) = μ (Y ⁻¹' {y}) := by
      rw [← map_apply measurable_snd (by simp), ← map_apply hY <| .singleton y, h1]
    rw [h1] at hy
    have hy'' : μ (Y ⁻¹' {y}) ≠ 0 := by
      convert hy
      exact (map_apply hY .of_discrete).symm
    have h2 : ν[| Prod.snd⁻¹' {y}] = m y := by
      rw [Measure.ext_iff]
      intro E _
      rw [cond_apply (measurable_snd (by simp)), hy']
      have h3 : (m y) ((Prod.snd⁻¹' {y}) ∩ E) = (m y) E := by
        apply measure_congr
        apply inter_ae_eq_right_of_ae_eq_univ
        simp only [ae_eq_univ]
        rw [(show (Prod.snd⁻¹' {y})ᶜ = Prod.snd⁻¹' ({y}ᶜ) by rfl),
          ← map_apply measurable_snd (by simp)]
        simp [m]
      have h3' {x : β} (hx : x ≠ y) : (m x) ((Prod.snd⁻¹' {y}) ∩ E) = 0 := by
        apply measure_inter_null_of_null_left E
        rw [← Measure.map_apply measurable_snd (by simp), MeasureTheory.Measure.map_snd_prod]
        simp only [Measure.smul_apply, MeasurableSet.singleton, dirac_apply', smul_eq_mul,
          mul_eq_zero, measure_univ_eq_zero, indicator_apply_eq_zero, mem_singleton_iff,
          Pi.ofNat_apply, one_ne_zero, imp_false]; right; exact hx
      simp only [coe_finsetSum, coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ν]
      rw [Finset.sum_eq_single_of_mem y ?_]
      · rw [h3, ← mul_assoc, ENNReal.inv_mul_cancel hy'', one_mul]
        finiteness
      · intro _ _ hx
        rw [h3' hx]
        simp
      · simpa using Set.preimage_singleton_nonempty.mp (nonempty_of_measure_ne_zero hy'')
    rw [h2, indepFun_iff_map_prod_eq_prod_map_map]
    · let f : (α × α) × β → α × α := Prod.fst
      change ((m y).map f) = ((m y).map (Prod.fst ∘ f)).prod ((m y).map (Prod.snd ∘ f))
      have : IsProbabilityMeasure (m' y) := h5 hy''
      have : (m y).map f = (m' y).prod (m' y) := by simp [f, m]
      rw [← map_map measurable_fst measurable_fst, ← map_map measurable_snd measurable_fst, this]
      simp
    · exact (measurable_fst.comp measurable_fst).aemeasurable
    exact (measurable_snd.comp measurable_fst).aemeasurable
  · rw [← sum_meas_smul_cond_fiber' hY μ]
    refine identDistrib_of_sum _ ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      (hX.prodMk hY) ?_
    intro y hy
    have h1 : IdentDistrib (fun ω ↦ (ω.1.1, ω.2)) (fun ω ↦ (ω.1.1, y)) (m y) (m y) := by
      refine .of_ae_eq ((measurable_fst.comp measurable_fst).prodMk measurable_snd).aemeasurable ?_
      apply Filter.eventuallyEq_of_mem (h4 y)
      intro _; simp
    have h2 : IdentDistrib (fun ω ↦ (ω.1.1, y)) (fun ω ↦ (X ω, y)) (m y) (μ[|Y ← y]) := by
      apply IdentDistrib.comp _ measurable_prodMk_right
      apply (identDistrib_comp_fst measurable_fst _ _).trans
      have : IsProbabilityMeasure ((μ[|Y ← y]).map X) := h5 hy
      apply (identDistrib_comp_fst measurable_id _ _).trans
      apply identDistrib_map hX measurable_id
    exact (h1.trans h2).trans (h3 y)
  rw [← sum_meas_smul_cond_fiber' hY μ]
  apply identDistrib_of_sum _ ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    (hX.prodMk hY)
  intro y hy
  have h1 : IdentDistrib (fun ω ↦ (ω.1.2, ω.2)) (fun ω ↦ (ω.1.2, y)) (m y) (m y) := by
    refine .of_ae_eq ((measurable_snd.comp measurable_fst).prodMk measurable_snd).aemeasurable ?_
    apply Filter.eventuallyEq_of_mem (h4 y)
    intro _; simp
  have h2 : IdentDistrib (fun ω ↦ (ω.1.2, y)) (fun ω ↦ (X ω, y)) (m y) (μ[|Y ← y]) := by
    apply IdentDistrib.comp _ measurable_prodMk_right
    apply (identDistrib_comp_fst measurable_snd _ _).trans
    have : IsProbabilityMeasure ((μ[|Y ← y]).map X) := h5 hy
    exact (identDistrib_comp_snd measurable_id _ _).trans (identDistrib_map hX measurable_id _)
  exact (h1.trans h2).trans (h3 y)

lemma condIndep_copies' (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : α → β → Prop)
    (hp : Measurable (uncurry p)) (hp' : ∀ᵐ ω ∂μ, p (X ω) (Y ω)) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      PfrCondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib ((_root_.prod X₁ Y')) ((_root_.prod X Y)) ν μ ∧
       IdentDistrib ((_root_.prod X₂ Y')) ((_root_.prod X Y)) ν μ ∧ (∀ ω, p (X₁ ω) (Y' ω)) ∧ (∀ ω, p (X₂ ω) (Y' ω)) := by
  obtain ⟨Ω', _, X₁, X₂, Y', ν, _, hX₁, hX₂, hY', hXY, hXY₁, hXY₂⟩ :=
    condIndep_copies X Y hX hY μ
  let i := Subtype.val (p := fun ω ↦ p (X₁ ω) (Y' ω) ∧ p (X₂ ω) (Y' ω))
  have hi : MeasurableEmbedding i := MeasurableEmbedding.subtype_coe
    ((hp.comp <| hX₁.prodMk hY').and <| hp.comp <| hX₂.prodMk hY').setOf
  have hi' : ∀ᵐ ω ∂ν, ω ∈ range i := by
    simp only [i, mem_ofPred_eq, Subtype.range_coe_subtype, Filter.eventually_and]
    exact ⟨hXY₁.symm.ae_snd (p := uncurry p) hp.setOf hp',
      hXY₂.symm.ae_snd (p := uncurry p) hp.setOf hp'⟩
  refine ⟨{ω // p (X₁ ω) (Y' ω) ∧ p (X₂ ω) (Y' ω)}, inferInstance, X₁ ∘ (↑), X₂ ∘ (↑), Y' ∘ (↑),
    ν.comap (↑), ?_, hX₁.comp measurable_subtype_coe, hX₂.comp measurable_subtype_coe,
    hY'.comp measurable_subtype_coe, ?_, ?_, ?_, fun ω ↦ ω.2.1, fun ω ↦ ω.2.2⟩
  · exact hi.isProbabilityMeasure_comap hi'
  · exact hXY.comp_right hi hi' hX₁ hX₂ hY'
  · exact hXY₁.comp_left hi hi' <| hX₁.prodMk hY'
  · exact hXY₂.comp_left hi hi' <| hX₂.prodMk hY'

end copy
end ProbabilityTheory
end

/- PFR.Mathlib.MeasureTheory.Integral.Lebesgue.Basic -/
noncomputable section
open scoped ProbabilityTheory
open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

lemma lintegral_eq_zero_of_ae_zero {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s, f x = 0)
    (hmes : MeasurableSet s) : ∫⁻ x, f x ∂μ = 0 := by
  rw [← lintegral_add_compl f hmes, setLIntegral_measure_zero sᶜ f hs,
    setLIntegral_congr_fun (f := f) (g := fun _ ↦ 0) hmes hf]
  simp

lemma lintegral_eq_setLIntegral (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]

end MeasureTheory
end

/- PFR.Mathlib.MeasureTheory.Integral.Lebesgue.Countable -/
noncomputable section
open scoped ProbabilityTheory
open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable [MeasurableSingletonClass α]

lemma lintegral_eq_tsum (μ : Measure α) (f : α → ℝ≥0∞) [Countable α] :
    ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  simp_rw [lintegral_countable', mul_comm]

lemma setLIntegral_eq_sum (μ : Measure α) (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x := by
  simp_rw [mul_comm, lintegral_finset]

lemma lintegral_eq_single (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a, f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by
  rw [← lintegral_add_compl f (A := {a}) (MeasurableSet.singleton a), lintegral_singleton,
    setLIntegral_congr_fun (g := fun _ ↦ 0) (MeasurableSet.compl (MeasurableSet.singleton a)),
    lintegral_zero, add_zero]
  simp +contextual [Set.EqOn, ha]

end MeasureTheory
end

/- PFR.Mathlib.Probability.Kernel.Disintegration -/
noncomputable section
open scoped ProbabilityTheory
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]

namespace Kernel

section condKernel

variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]

lemma condKernel_apply (κ : Kernel T (S × U)) [IsFiniteKernel κ] (x : T × S)
    (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) :
    condKernel κ x = (κ x.1).condKernel x.2 := by
  have h := condKernel_apply_eq_condKernel κ x.1
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h
  refine h x.2 ?_
  rwa [fst_apply' _ _ (.singleton _)]

lemma condKernel_apply' (κ : Kernel T (S × U)) [IsFiniteKernel κ]
    (x : T × S) (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) (s : Set U) :
    condKernel κ x s
      = (κ x.1 (Prod.fst ⁻¹' {x.2}))⁻¹ * (κ x.1) ({x.2} ×ˢ s) := by
  rw [condKernel_apply _ _ hx, Measure.condKernel_apply_of_ne_zero,
    Measure.fst_apply (.singleton _)]
  rwa [Measure.fst_apply (.singleton _)]

lemma condKernel_compProd_apply' (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) {s : Set U} (hs : MeasurableSet s) :
    condKernel (κ ⊗ₖ η) x s = η x s := by
  have hx' : (κ ⊗ₖ η) x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    rwa [compProd_preimage_fst (.singleton _)]
  rw [condKernel_apply' _ _ hx', compProd_apply ((measurableSet_singleton _).prod hs),
    Kernel.compProd_apply, lintegral_eq_single _ x.2, lintegral_eq_single _ x.2]
  · simp [Set.preimage_preimage, mul_comm]
    simp [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top (κ x.1) {x.2})]
  · intro b hb
    rw [Set.eq_empty_of_forall_notMem (s := _ ⁻¹' _) (by simp [hb]), measure_empty]
  · intro b hb
    simp [hb, Set.preimage_preimage]
  · measurability

lemma condKernel_compProd_apply (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) :
    condKernel (κ ⊗ₖ η) x = η x := by
  ext s hs
  convert condKernel_compProd_apply' κ η x hx hs

lemma disintegration (κ : Kernel T (S × U)) [IsFiniteKernel κ] :
    κ = (Kernel.fst κ) ⊗ₖ (condKernel κ) := by
  ext x s hs
  rw [compProd_apply hs, lintegral_fst]
  swap; · exact measurable_kernel_prodMk_left' hs x
  rw [lintegral_eq_tsum, ENNReal.tsum_prod']
  change κ x s = ∑' a : S, ∑' b : U, κ x {(a, b)} * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
  simp_rw [ENNReal.tsum_mul_right, ← measure_preimage_fst_singleton_eq_tsum (κ x)]
  have : ∑' a : S, (κ x (Prod.fst ⁻¹' {a})) * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
      = ∑' a : S, κ x (Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s}) := by
    congr with a
    by_cases ha : κ x (Prod.fst ⁻¹' {a}) = 0
    · simp only [ha, zero_mul]
      exact (measure_mono_null Set.inter_subset_left ha).symm
    · rw [condKernel_apply' κ _ ha, ← mul_assoc,
      ENNReal.mul_inv_cancel ha (measure_ne_top _ _), one_mul]
      congr
  simp_rw [this]
  have : ⋃ a, Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s} = s := by ext a; simp
  conv_lhs => rw [← this]
  rw [measure_iUnion]
  · intro a a' haa'
    rw [Function.onFun, Set.disjoint_iff]
    intro su
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, and_imp]
    intro h1 _ h1' _
    exact haa' (h1.symm.trans h1')
  · refine fun _ ↦ (measurable_fst (.singleton _)).inter ?_
    exact measurable_prodMk_left.comp measurable_snd hs

variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]

lemma condKernel_compProd_ae_eq
    (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η] (μ : Measure T) :
    condKernel (κ ⊗ₖ η) =ᵐ[μ ⊗ₘ κ] η := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condKernel_compProd_apply]
  rw [Measure.compProd_apply (.singleton _), lintegral_eq_tsum] at hx
  simp only [ne_eq, ENNReal.summable.tsum_eq_zero_iff, mul_eq_zero, not_forall] at hx
  obtain ⟨y, hy⟩ := hx
  push Not at hy
  classical
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod_right_eq_if] at hy
  simp only [ne_eq, Set.mem_singleton_iff] at hy
  by_cases hyx1 : y = x.1
  · simp only [hyx1, ite_true] at hy
    exact hy.2
  · simp [hyx1] at hy

lemma compProd_swapLeft_prodMkLeft {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    κ ⊗ₖ swapLeft (prodMkLeft β η) = κ ×ₖ η := by
  ext x s hs
  simp [compProd_apply hs, prod_apply' _ _ _ hs]

lemma condKernel_prod_ae_eq (κ : Kernel T S) [IsFiniteKernel κ] {μ}
    (η : Kernel T U) [IsMarkovKernel η] :
    condKernel (κ ×ₖ η) =ᵐ[μ ⊗ₘ κ] prodMkRight S η := by
  simp_rw [← compProd_swapLeft_prodMkLeft]
  exact condKernel_compProd_ae_eq _ _ _

lemma condKernel_map_prodMk_left {V : Type*} [Nonempty V] [MeasurableSpace V]
    [DiscreteMeasurableSpace V] [Countable V]
    (κ : Kernel T (S × U)) [IsMarkovKernel κ] (μ : Measure T)
    (f : S × U → V) :
    condKernel (map κ (fun p ↦ (p.1, f p)))
      =ᵐ[μ ⊗ₘ fst κ] snd ((condKernel κ) ⊗ₖ (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2))
          .of_discrete)) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.compProd_apply (.singleton _), lintegral_eq_tsum] at hx
  simp only [ne_eq, ENNReal.summable.tsum_eq_zero_iff, mul_eq_zero, not_forall, not_or,
    fst_apply' _ _ (measurable_prodMk_left (.singleton _)), Set.mem_preimage, Set.mem_singleton_iff]
    at hx
  obtain ⟨y, hy⟩ := hx
  have hyx1 : y = x.1 := by
    by_contra hy_ne
    refine hy.2 ?_
    rw [← Prod.eta x]
    simp_rw [Prod.mk_inj]
    simp [hy_ne]
  rw [hyx1] at hy
  ext s hs
  rw [snd_apply' _ _ hs, compProd_deterministic_apply _ (measurable_snd hs)]
  have h_ne_zero : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    refine fun h_zero ↦ hy.2 ?_
    refine measure_mono_null ?_ h_zero
    intro p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    conv_lhs => rw [← Prod.eta x, Prod.mk_inj]
    exact fun h ↦ h.2
  have h_preimage : (fun p ↦ (p.1, f p)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = Prod.fst ⁻¹' {x.2} := by
    ext p; simp
  rw [condKernel_apply' _ _ _, condKernel_apply' _ _ h_ne_zero]; swap
  · rw [map_apply' _ .of_discrete _ (measurable_fst (.singleton _)),
      h_preimage]
    exact h_ne_zero
  rw [map_apply' _ .of_discrete _ (measurable_fst (.singleton _)), h_preimage]
  congr
  rw [map_apply' _ .of_discrete _ ((measurableSet_singleton _).prod hs)]
  congr
  ext p
  simp only [Set.singleton_prod, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    exists_eq_right_right, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ⟨p.2, ?_, ?_⟩, fun ⟨p2, h_mem, h_eq⟩ ↦ ?_⟩
  · rw [h.2, Prod.mk.eta]
    exact h.1
  · rw [h.2, Prod.mk.eta]
  · rw [← h_eq]
    simp [h_mem]

end condKernel

end Kernel

section condDistrib

variable [MeasurableSingletonClass T]
variable [Countable U] [DiscreteMeasurableSpace U]

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

lemma condDistrib_apply' [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) {s : Set S} (hs : MeasurableSet s) :
    condDistrib X Y μ x s = (μ (Y ⁻¹' {x}))⁻¹ * μ (Y ⁻¹' {x} ∩ X ⁻¹' s) := by
  rw [condDistrib_apply_of_ne_zero hX]
  · rw [Measure.map_apply hY (.singleton _),
      Measure.map_apply (hY.prodMk hX) ((measurableSet_singleton _).prod hs)]
    congr
  · rwa [Measure.map_apply hY (.singleton _)]

lemma condDistrib_apply [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) :
    condDistrib X Y μ x = (μ[|Y ⁻¹' {x}]).map X := by
  ext s hs
  rw [condDistrib_apply' hX hY μ x hYx hs, Measure.map_apply hX hs,
    cond_apply (hY (.singleton _))]

variable [Countable T]

lemma condDistrib_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    condDistrib X Y μ =ᵐ[μ.map Y] fun x ↦ (μ[|Y ⁻¹' {x}]).map X := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply hY (.singleton _)] at hx
  exact condDistrib_apply hX hY μ x hx

variable [Nonempty T]

lemma condDistrib_fst_of_ne_zero [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) [IsFiniteMeasure μ]
    (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    Kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib X Z μ u := by
  ext A hA
  rw [Kernel.fst_apply' _ _ hA, condDistrib_apply' (hX.prodMk hY) hZ _ _ hu]
  swap; · exact measurable_fst hA
  rw [condDistrib_apply' hX hZ _ _ hu hA]
  rfl

lemma condDistrib_fst_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib X Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_fst_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (.singleton _)] at hx

lemma condDistrib_snd_of_ne_zero [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    Kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib Y Z μ u := by
  ext A hA
  rw [Kernel.snd_apply' _ _ hA, condDistrib_apply' (hX.prodMk hY) hZ _ _ hu]
  swap; · exact measurable_snd hA
  rw [condDistrib_apply' hY hZ _ _ hu hA]
  rfl

lemma condDistrib_snd_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib Y Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_snd_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (.singleton _)] at hx

lemma condKernel_condDistrib_ae_eq [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
  Kernel.condKernel (condDistrib (fun a ↦ (X a, Y a)) Z μ) =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))]
    condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prodMk hX) (.singleton _)] at hx
  ext A hA
  have hx1 : μ (Z ⁻¹' {x.1}) ≠ 0 := by
    refine fun h_null ↦ hx (measure_mono_null ?_ h_null)
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    rw [← Prod.eta x, Prod.mk_inj] at hω
    exact hω.1
  rw [Kernel.condKernel_apply']
  swap
  · rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
    swap
    · exact measurable_fst (.singleton _)
    simp only [ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, measure_ne_top μ, false_or]
    convert hx
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    conv_rhs => rw [← Prod.eta x]
    exact Prod.mk_inj.symm
  rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
  swap
  · exact measurable_fst (.singleton _)
  rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
  swap
  · exact (measurable_fst (.singleton _)).inter (measurable_snd hA)
  rw [condDistrib_apply' hY (hZ.prodMk hX) _ _ hx hA]
  have : (fun a ↦ (X a, Y a)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = X ⁻¹' {x.2} := by rfl
  simp_rw [this]
  have : (fun a ↦ (X a, Y a)) ⁻¹' ({x.2} ×ˢ A) = X ⁻¹' {x.2} ∩ Y ⁻¹' A := by
    ext y;
    simp only [Set.singleton_prod, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
      exists_eq_right_right, Set.mem_inter_iff, Set.mem_singleton_iff]
    tauto
  simp_rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' {x} = Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
    conv_lhs => rw [← Prod.eta x, Prod.mk_inj]
  rw [this, ENNReal.mul_inv (Or.inr (measure_ne_top _ _)), inv_inv]
  swap; · left; simp [hx1]
  calc (μ (Z ⁻¹' {x.1})) * (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ *
      ((μ (Z ⁻¹' {x.1}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ (X ⁻¹' {x.2} ∩ Y ⁻¹' A)))
    = (μ (Z ⁻¹' {x.1})) * (μ (Z ⁻¹' {x.1}))⁻¹ * (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ *
      μ (Z ⁻¹' {x.1} ∩ (X ⁻¹' {x.2} ∩ Y ⁻¹' A)) := by
        ring
  _ = (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2} ∩ Y ⁻¹' A) := by
        rw [ENNReal.mul_inv_cancel hx1 (measure_ne_top _ _), one_mul, Set.inter_assoc]

lemma swap_condDistrib_ae_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.comap (condDistrib Y (fun a ↦ (X a, Z a)) μ) Prod.swap measurable_swap
      =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))] condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  ext A hA
  rw [Kernel.comap_apply']
  have h_swap : (fun a ↦ (X a, Z a)) ⁻¹' {Prod.swap x} = (fun a ↦ (Z a, X a)) ⁻¹' {x} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.swap_prod_mk, Prod.mk_inj, Prod.mk_inj, and_comm]
  rw [condDistrib_apply' hY (hX.prodMk hZ) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prodMk hX) (.singleton _), ← h_swap] at hx
  rw [condDistrib_apply' hY (hZ.prodMk hX) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prodMk hX) (.singleton _)] at hx
  rw [h_swap]

lemma condDistrib_const_unit (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.condKernel (Kernel.const Unit (μ.map (fun ω ↦ (X ω, Y ω))))
      =ᵐ[μ.map (fun ω ↦ ((), X ω))] Kernel.prodMkLeft Unit (condDistrib Y X μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  have : (fun a ↦ ((), X a)) ⁻¹' {x} = X ⁻¹' {x.2} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.mk_inj]
    simp
  rw [Measure.map_apply (measurable_const.prodMk hX) (.singleton _), this] at hx
  ext s hs
  rw [Kernel.condKernel_apply']
  swap
  · rw [Kernel.const_apply,
      Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _))]
    exact hx
  simp_rw [Kernel.const_apply,
    Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _)),
    Measure.map_apply (hX.prodMk hY) ((measurableSet_singleton _).prod hs)]
  rw [Kernel.prodMkLeft_apply', condDistrib_apply' hY hX _ _ hx hs]
  rfl

lemma condDistrib_unit_right [Nonempty S]
    (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    condDistrib X (fun _ ↦ ()) μ = Kernel.const Unit (μ.map X) := by
  ext x s hs
  rw [condDistrib_apply' hX measurable_const _ _ _ hs]
  · simp only [Set.mem_singleton_iff, Set.preimage_const_of_mem, measure_univ, inv_one,
      Set.univ_inter, one_mul]
    rw [Kernel.const_apply, Measure.map_apply hX hs]
  · simp

lemma map_compProd_condDistrib [Nonempty S] (hX : Measurable X) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.map Z ⊗ₘ condDistrib X Z μ = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext A hA
  rw [Measure.map_apply (hZ.prodMk hX) hA, Measure.compProd_apply hA, lintegral_eq_tsum]
  have : ∑' x : U, μ.map Z {x} * condDistrib X Z μ x (Prod.mk x ⁻¹' A)
      = ∑' x : U, μ (Z ⁻¹' {x} ∩ (fun ω ↦ (x, X ω)) ⁻¹' A) := by
    congr 1 with x
    rw [Measure.map_apply hZ (.singleton _)]
    by_cases hx : μ (Z ⁻¹' {x}) = 0
    · simp [hx, measure_mono_null Set.inter_subset_left hx]
    rw [condDistrib_apply' hX hZ _ _ hx]
    swap; · exact (measurable_prodMk_left hA)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]
    congr
  rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' A = ⋃ x, Z ⁻¹' {x} ∩ ((fun a ↦ (x, X a)) ⁻¹' A) := by
    ext ω
    simp
  rw [this, measure_iUnion]
  · intro i j hij
    rw [Function.onFun]
    refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_
    rw [Set.disjoint_iff]
    intro z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      and_imp]
    exact fun hi hj ↦ hij (hi.symm.trans hj)
  intro u
  exact (hZ (.singleton _)).inter (measurable_const.prodMk hX hA)

section Independence

variable {V : Type*} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {W : Ω → V}

lemma condDistrib_eq_prod_of_indepFun [Nonempty S]
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun (fun ω ↦ (X ω, Z ω)) (fun ω ↦ (Y ω, W ω)) μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (Z ω, W ω)) μ
      =ᵐ[μ.map (fun ω ↦ (Z ω, W ω))] Kernel.prodMkRight V (condDistrib X Z μ)
        ×ₖ Kernel.prodMkLeft U (condDistrib Y W μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prodMk hW) (.singleton _)] at hx
  ext s hs
  rw [condDistrib_apply (hX.prodMk hY) (hZ.prodMk hW) _ _ hx, Kernel.prod_apply' _ _ _ hs]
  simp_rw [Kernel.prodMkLeft_apply, Kernel.prodMkRight_apply]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod] at hx
  have hxZ : μ (Z ⁻¹' {x.1}) ≠ 0 := fun h0 ↦ hx (measure_mono_null Set.inter_subset_left h0)
  have hxW : μ (W ⁻¹' {x.2}) ≠ 0 := fun h0 ↦ hx (measure_mono_null Set.inter_subset_right h0)
  simp_rw [lintegral_eq_tsum, condDistrib_apply hX hZ μ _ hxZ,
    condDistrib_apply hY hW μ _ hxW, Measure.map_apply (hX.prodMk hY) hs]
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod,
    cond_apply ((hZ (.singleton _)).inter (hW (.singleton _)))]
  simp_rw [Measure.map_apply hX (.singleton _),
    cond_apply (hZ (.singleton _))]
  change (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      * μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2} ∩ (fun a ↦ (X a, Y a)) ⁻¹' s)
    = ∑' x_1, (μ (Z ⁻¹' {x.1}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x_1})
      * ((μ[|W ⁻¹' {x.2}]).map Y) (Prod.mk x_1 ⁻¹' s)
  simp_rw [Measure.map_apply hY (measurable_prodMk_left hs),
    cond_apply (hW (.singleton _))]
  have hZW : IndepFun Z W μ := by
    have h' := IndepFun.comp h measurable_snd measurable_snd
    exact h'
  have h_indep1 : (μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2}))⁻¹
      = (μ (Z ⁻¹' {x.1}))⁻¹ * (μ (W ⁻¹' {x.2}))⁻¹ := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul.mp hZW _ _ (.singleton _)
      (.singleton _), ENNReal.mul_inv (Or.inl hxZ) (Or.inl (measure_ne_top _ _))]
  rw [h_indep1]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  simp_rw [← mul_assoc, mul_comm _ (μ (W ⁻¹' {x.2}))⁻¹, mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  have h_Union : (fun ω ↦ (X ω, Y ω)) ⁻¹' s = ⋃ a, ((X ⁻¹' {a}) ∩ (Y ⁻¹' (Prod.mk a ⁻¹' s))) := by
    ext1; simp
  rw [h_Union, Set.inter_iUnion, measure_iUnion]
  rotate_left
  · intro i j hij
    rw [Function.onFun, Set.disjoint_iff]
    intro y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      and_imp]
    exact fun _ _ h3 _ _ _ h7 _ ↦ hij (h3.symm.trans h7)
  · intro b
    refine ((hZ (.singleton _)).inter (hW (.singleton _))).inter ?_
    exact (hX (.singleton _)).inter (hY (measurable_prodMk_left hs))
  congr with b
  calc μ (Z ⁻¹' {x.1} ∩ W ⁻¹' {x.2} ∩ (X ⁻¹' {b} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s)))
    = μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {b} ∩ (W ⁻¹' {x.2} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s))) := by
        rw [Set.inter_assoc, ← Set.inter_assoc (W ⁻¹' {x.2}), Set.inter_comm (W ⁻¹' {x.2}),
          ← Set.inter_assoc, ← Set.inter_assoc, ← Set.inter_assoc]
  _ = μ ((fun ω ↦ (X ω, Z ω)) ⁻¹' {(b, x.1)}
      ∩ ((fun ω ↦ (Y ω, W ω)) ⁻¹' ((Prod.mk b ⁻¹' s) ×ˢ {x.2}))) := by
        rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, Set.inter_comm (Z ⁻¹' {x.1}),
          Set.mk_preimage_prod, Set.inter_comm (W ⁻¹' {x.2})]
  _ = μ ((fun ω ↦ (X ω, Z ω)) ⁻¹' {(b, x.1)})
      * μ ((fun ω ↦ (Y ω, W ω)) ⁻¹' ((Prod.mk b ⁻¹' s) ×ˢ {x.2})) := by
        refine indepFun_iff_measure_inter_preimage_eq_mul.mp h _ _ (.singleton _) ?_
        exact (measurable_prodMk_left hs).prod (.singleton _)
  _ = μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {b}) * μ (W ⁻¹' {x.2} ∩ Y ⁻¹' (Prod.mk b ⁻¹' s)) := by
        rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, Set.inter_comm (Z ⁻¹' {x.1}),
          Set.mk_preimage_prod, Set.inter_comm (W ⁻¹' {x.2})]

end Independence

end condDistrib

end ProbabilityTheory

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

lemma _root_.MeasureTheory.Measure.compProd_apply_singleton
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (μ : Measure T) [SFinite μ]
    (κ : Kernel T S) [IsSFiniteKernel κ] (t : T) (s : S) :
    (μ ⊗ₘ κ) {(t, s)} = κ t {s} * μ {t} := by
  rw [Measure.compProd_apply (.singleton _)]
  have : ∀ a, κ a (Prod.mk a ⁻¹' {(t, s)}) = ({t} : Set T).indicator (fun _ ↦ κ t {s}) a := by
    intro a
    by_cases ha : a = t
    · simp only [ha, Set.mem_singleton_iff, Set.indicator_of_mem]
      congr
      ext y
      simp
    · simp only [Set.mem_singleton_iff, ha, not_false_eq_true, Set.indicator_of_notMem]
      suffices Prod.mk a ⁻¹' {(t, s)} = ∅ by simp [this]
      ext y
      simp [ha]
  simp_rw [this]
  rw [lintegral_indicator (.singleton _)]
  simp

lemma _root_.MeasureTheory.Measure.ae_of_compProd_eq_zero {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : (μ ⊗ₘ κ) s = 0) :
    ∀ᵐ a ∂μ, κ a (Prod.mk a ⁻¹' s) = 0 := by
  let t := toMeasurable (μ ⊗ₘ κ) s
  have ht : (μ ⊗ₘ κ) t = 0 := by
    unfold t
    rwa [measure_toMeasurable]
  rw [Measure.compProd_apply (measurableSet_toMeasurable _ _), lintegral_eq_zero_iff] at ht
  swap; · exact measurable_kernel_prodMk_left (measurableSet_toMeasurable _ _)
  filter_upwards [ht] with a ha
  exact measure_mono_null (fun y hy ↦ subset_toMeasurable (μ ⊗ₘ κ) s hy) ha

lemma _root_.MeasureTheory.Measure.ae_of_ae_compProd {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {p : α × β → Prop} (hp : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) := by
  rw [ae_iff] at hp
  have hp' := Measure.ae_of_compProd_eq_zero hp
  filter_upwards [hp'] with a ha
  rwa [ae_iff]

lemma compProd_congr_ae {μ} [SFinite μ] {κ κ' : Kernel T S} [IsSFiniteKernel κ] [IsSFiniteKernel κ']
    {η η' : Kernel (T × S) U} [IsSFiniteKernel η] [IsSFiniteKernel η']
    (hκ : κ =ᵐ[μ] κ') (hη : η =ᵐ[μ ⊗ₘ κ] η') :
    κ ⊗ₖ η =ᵐ[μ] κ' ⊗ₖ η' := by
  have hη' := Measure.ae_of_ae_compProd hη
  filter_upwards [hκ, hη'] with a haκ haη
  ext s hs
  rw [compProd_apply hs, compProd_apply hs, ← haκ]
  refine lintegral_congr_ae ?_
  filter_upwards [haη] with b hb
  rw [hb]

noncomputable def FiniteKernelSupport (κ : Kernel T S) : Prop :=
  ∀ t, ∃ A : Finset S, κ t Aᶜ = 0

noncomputable def AEFiniteKernelSupport (κ : Kernel T S) (μ : Measure T) : Prop :=
  ∀ᵐ t ∂μ, ∃ A : Finset S, κ t Aᶜ = 0

lemma FiniteKernelSupport.aefiniteKernelSupport {κ : Kernel T S} (hκ : FiniteKernelSupport κ)
    (μ : Measure T) :
    AEFiniteKernelSupport κ μ :=
  ae_of_all μ hκ

@[simp] lemma finiteKernelSupport_zero : FiniteKernelSupport (0 : Kernel T S) :=
  fun t ↦ ⟨∅, by simp⟩

@[simp] lemma aefiniteKernelSupport_zero {μ} : AEFiniteKernelSupport (0 : Kernel T S) μ :=
  finiteKernelSupport_zero.aefiniteKernelSupport _

section

variable [Countable T] [MeasurableSingletonClass T] {μ : Measure T}

noncomputable
def AEFiniteKernelSupport.mk {μ} {κ : Kernel T S} (_hκ : AEFiniteKernelSupport κ μ) :
    Kernel T S := by
  classical
  exact if hS : Nonempty S then
    κ.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0}) (by rw [Set.ofPred_exists]; measurability)
       (.const _ <| .dirac hS.some)
  else 0

@[simp] lemma AEFiniteKernelSupport.mk_zero
    {h : AEFiniteKernelSupport (0 : Kernel T S) μ} : h.mk = 0 := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp [mk]
  ext x
  by_cases hx : x ∈ {t | ∃ A : Finset S, (0 : Kernel T S) t Aᶜ = 0} <;>
    simp [AEFiniteKernelSupport.mk, Kernel.piecewise, hS]

@[simp] lemma AEFiniteKernelSupport.mk_eq_zero_of_isEmpty
    [IsEmpty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = 0 := by
  simp [mk]

open Classical in
lemma AEFiniteKernelSupport.mk_eq
    [hS : Nonempty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = κ.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0})
      (by rw [Set.ofPred_exists]; measurability) (.const _ <| .dirac hS.some) := by
  simp [mk, hS]

lemma AEFiniteKernelSupport.finiteKernelSupport_mk [MeasurableSingletonClass S] {κ : Kernel T S}
    (hκ : AEFiniteKernelSupport κ μ) :
    FiniteKernelSupport hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp
  intro t
  classical
  rw [mk_eq, piecewise_apply]
  split_ifs with ht
  · exact ht
  · refine ⟨{hS.some}, ?_⟩
    simp

lemma AEFiniteKernelSupport.ae_eq_mk
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    κ =ᵐ[μ] hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · filter_upwards with x
    ext s
    simp [Set.eq_empty_of_isEmpty s]
  filter_upwards [hκ] with t ht
  classical
  rw [AEFiniteKernelSupport.mk_eq, Kernel.piecewise_apply, if_pos (by exact ht)]

instance AEFiniteKernelSupport.isMarkovKernel_mk
    {κ : Kernel T S} [IsMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsMarkovKernel hκ.mk := by
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨fun x ↦ (IsEmpty.false x).elim⟩
  inhabit T
  have : Nonempty S := (κ default).nonempty_of_neZero
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance

instance AEFiniteKernelSupport.isZeroOrMarkovKernel_mk
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsZeroOrMarkovKernel hκ.mk := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp only [mk_zero]
    infer_instance
  · infer_instance

instance AEFiniteKernelSupport.isSFiniteKernel_mk
    {κ : Kernel T S} [IsSFiniteKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsSFiniteKernel hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [mk_eq_zero_of_isEmpty]; infer_instance
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance

lemma aefiniteKernelSupport_iff [MeasurableSingletonClass S] {κ : Kernel T S} {μ : Measure T} :
    AEFiniteKernelSupport κ μ ↔ ∃ κ' : Kernel T S, FiniteKernelSupport κ' ∧ κ' =ᵐ[μ] κ := by
  refine ⟨fun h ↦ ⟨h.mk, h.finiteKernelSupport_mk, h.ae_eq_mk.symm⟩, fun ⟨κ', hκ', h_eq⟩ ↦ ?_⟩
  filter_upwards [h_eq] with x hx
  rw [← hx]
  exact hκ' x

end

lemma local_support_of_finiteKernelSupport
    {κ : Kernel T S} (h : FiniteKernelSupport κ) (A : Finset T) :
    ∃ B : Finset S, ∀ t ∈ A, ∀ᵐ x ∂(κ t), x ∈ B := by
  classical
  use A.biUnion (fun t ↦ (h t).choose)
  intro t ht
  change κ t (A.biUnion fun t ↦ (h t).choose)ᶜ = 0
  set B := (h t).choose
  refine measure_mono_null ?_ (h t).choose_spec
  intro s
  simp only [Finset.coe_biUnion, SetLike.mem_coe, Set.compl_iUnion, Set.mem_iInter,
    Set.mem_compl_iff]
  contrapose!; intro h
  use t

lemma FiniteKernelSupport.deterministic [Countable S] [Countable T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (f : T × S → U) :
    FiniteKernelSupport (deterministic f .of_discrete) := by
  intro (t, s)
  use {f (t, s)}
  rw [Kernel.deterministic_apply' (by measurability) _ (by measurability)]
  simp

lemma FiniteKernelSupport.map [MeasurableSingletonClass U]
    {κ : Kernel T S} (hκ : FiniteKernelSupport κ) (f : S → U) :
    FiniteKernelSupport (map κ f) := by
  by_cases hf : Measurable f
  · intro t
    rcases hκ t with ⟨A, hA⟩
    classical
    use Finset.image f A
    rw [Kernel.map_apply' _ hf]
    · refine measure_mono_null ?_ hA
      intro s
      simp only [Finset.coe_image, Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_image, SetLike.mem_coe, not_exists, not_and]
      contrapose!; intro hs; use s
    · apply MeasurableSet.compl
      apply Set.Finite.measurableSet
      exact Finset.finite_toSet (Finset.image f A)
  · simp [map_of_not_measurable _ hf]

lemma AEFiniteKernelSupport.map [MeasurableSingletonClass U] {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) {f : S → U} :
    AEFiniteKernelSupport (Kernel.map κ f) μ := by
  by_cases hf : Measurable f
  · filter_upwards [hκ] with t ⟨A, hA⟩
    classical
    use Finset.image f A
    rw [Kernel.map_apply' _ hf]
    · refine measure_mono_null ?_ hA
      intro s
      simp only [Finset.coe_image, Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_image, SetLike.mem_coe, not_exists, not_and]
      contrapose!; intro hs; use s
    · apply MeasurableSet.compl
      apply Set.Finite.measurableSet
      exact Finset.finite_toSet (Finset.image f A)
  · simp [map_of_not_measurable _ hf]

lemma FiniteKernelSupport.comap {κ : Kernel T S} (hκ : FiniteKernelSupport κ)
    {f : U → T} (hf : Measurable f) :
    FiniteKernelSupport (comap κ f hf) := by
  intro u
  rcases hκ (f u) with ⟨A, hA⟩
  use A
  rwa [Kernel.comap_apply]

lemma AEFiniteKernelSupport.comap_equiv [Countable U] [MeasurableSingletonClass U]
  {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (f : U ≃ᵐ T) :
    AEFiniteKernelSupport (Kernel.comap κ f f.measurable) (μ.comap f) := by
  rw [← @MeasurableEquiv.map_symm]
  rw [AEFiniteKernelSupport]
  simp_rw [Kernel.comap_apply]
  rw [ae_map_iff f.symm.measurable.aemeasurable]
  · simp only [MeasurableEquiv.apply_symm_apply]
    exact hκ
  · rw [Set.ofPred_exists]
    measurability

lemma FiniteKernelSupport.fst [MeasurableSingletonClass S]
   {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (fst κ) := by
  rw [fst_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.fst [MeasurableSingletonClass S] {κ : Kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (fst κ) μ := by
  rw [fst_eq]
  apply hκ.map

lemma FiniteKernelSupport.snd [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (snd κ) := by
  rw [snd_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.snd [MeasurableSingletonClass U] {κ : Kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (snd κ) μ := by
  rw [snd_eq]
  apply hκ.map

lemma aefiniteKernelSupport_of_cond {κ : Kernel T (S × U)} [hU : Nonempty U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] [Countable U] [Countable S] [Countable T]
    (μ : Measure T) (hκ : AEFiniteKernelSupport κ μ) [IsFiniteKernel κ] :
    AEFiniteKernelSupport (condKernel κ) (μ ⊗ₘ (Kernel.fst κ)) := by
  rw [AEFiniteKernelSupport, ae_iff_of_countable] at hκ ⊢
  intro (t, s) hts
  simp only [compProd_apply_singleton, ne_eq, mul_eq_zero, not_or] at hts
  push Not at hts
  rcases hκ t hts.2 with ⟨A, hA⟩
  classical
  use Finset.image Prod.snd A
  rw [condKernel_apply']; swap
  · rw [Kernel.fst_apply' _ _ (.singleton _)] at hts
    exact hts.1
  simp only [Finset.coe_image, Set.singleton_prod, mul_eq_zero, ENNReal.inv_eq_zero]
  right
  refine measure_mono_null ?_ hA
  intro x
  simp only [Set.mem_image, Set.mem_compl_iff, Finset.mem_coe, Prod.exists, exists_eq_right,
    not_exists, forall_exists_index, and_imp]
  intro y h hsyx
  rw [← hsyx]
  exact h s

lemma FiniteKernelSupport.swapRight
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (swapRight κ) := by
  rw [swapRight_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.swapRight {κ : Kernel T (S × U)} {μ : Measure T}
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (swapRight κ) μ := by
  rw [swapRight_eq]
  apply hκ.map

lemma FiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ×ₖ η) := by
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases hη t with ⟨B, hB⟩
  use A ×ˢ B
  rw [Kernel.prod_apply' _ _ _ (by measurability)]
  apply lintegral_eq_zero_of_ae_zero hA _ (by measurability)
  intro s hs
  refine measure_mono_null ?_ hB
  intro u; simp; tauto

lemma AEFiniteKernelSupport.prod {κ : Kernel T S} {η : Kernel T U}
    [IsMarkovKernel κ] [IsMarkovKernel η] {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    AEFiniteKernelSupport (κ ×ₖ η) μ := by
  filter_upwards [hκ, hη] with x ⟨A, hκA⟩ ⟨B, hηB⟩
  use A ×ˢ B
  rw [Finset.coe_product, Set.compl_prod_eq_union, prod_apply, measure_union_null_iff,
    Measure.prod_prod, Measure.prod_prod, hκA, hηB, zero_mul, mul_zero, and_self]

lemma FiniteKernelSupport.compProd [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    {κ : Kernel T S} {η : Kernel (T × S) U}
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ⊗ₖ η) := by
  by_cases hκ' : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ']
  by_cases hη' : IsSFiniteKernel η; swap
  · simp [compProd_of_not_isSFiniteKernel_right _ _ hη']
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hη ({t} ×ˢ A)) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Kernel.compProd_apply (by measurability), lintegral_eq_setLIntegral hA,
    setLIntegral_eq_sum]
  apply Finset.sum_eq_zero
  intro s hs
  simp only [Finset.coe_product, Set.preimage_compl, mul_eq_zero]
  right
  refine measure_mono_null ?_ (hB (t, s) (by simp [hs]))
  intro u; simp; tauto

lemma AEFiniteKernelSupport.compProd [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    {κ : Kernel T S} {η : Kernel (T × S) U} {μ : Measure T} [SFinite μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    AEFiniteKernelSupport (κ ⊗ₖ η) μ := by
  by_cases hκ' : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ']
  by_cases hη' : IsSFiniteKernel η; swap
  · simp [compProd_of_not_isSFiniteKernel_right _ _ hη']
  rw [aefiniteKernelSupport_iff]
  refine ⟨hκ.mk ⊗ₖ hη.mk, ?_, ?_⟩
  · exact hκ.finiteKernelSupport_mk.compProd hη.finiteKernelSupport_mk
  · have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
    refine compProd_congr_ae hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm

lemma FiniteKernelSupport.prodMkRight {κ : Kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkRight U κ) :=
  hκ.comap _

protected lemma AEFiniteKernelSupport.prodMkRight [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable U] {μ}
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite ν] :
    AEFiniteKernelSupport (prodMkRight U κ) (μ.prod ν) := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨prodMkRight U hκ.mk, hκ.finiteKernelSupport_mk.prodMkRight, ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ (x : T × U) ∂(μ.prod ν), x ∈ {y | (prodMkRight U (mk hκ)) y = (prodMkRight U κ) y}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hκ.ae_eq_mk] with x hx
    simp [hx]
  · simp only [prodMkRight_apply, measurableSet_setOfPred]
    exact .of_discrete

lemma FiniteKernelSupport.prodMkLeft {κ : Kernel T S} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (prodMkLeft U κ) :=
  hκ.comap _

protected lemma AEFiniteKernelSupport.prodMkLeft [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable U] {μ}
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite μ] :
    AEFiniteKernelSupport (prodMkLeft U κ) (ν.prod μ) := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨prodMkLeft U hκ.mk, hκ.finiteKernelSupport_mk.prodMkLeft , ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ (x : U × T) ∂(ν.prod μ), x ∈ {y | prodMkLeft U (mk hκ) y = prodMkLeft U κ y}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · refine ae_of_all _ fun y ↦ ?_
    filter_upwards [hκ.ae_eq_mk] with x hx
    simp [hx]
  · simpa using .of_discrete

end ProbabilityTheory.Kernel
end

/- PFR.Mathlib.Probability.Kernel.Composition.Comp -/
noncomputable section
open scoped ProbabilityTheory
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

section
variable {α β γ δ ε : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {_ : MeasurableSpace ε}

variable {Ω S T : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace γ]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → β}

lemma map_map (κ : Kernel α β) {f : β → γ} (hf : Measurable f) {g : γ → δ} (hg : Measurable g) :
    map (map κ f) g = map κ (g ∘ f) := by
  ext x s _
  rw [map_apply _ hg, map_apply _ hf, map_apply _ (hg.comp hf), Measure.map_map hg hf]

lemma map_swapRight (κ : Kernel α (β × γ)) {f : (γ × β) → δ} :
    map (swapRight κ) f = map κ (f ∘ Prod.swap) := by
  by_cases hf : Measurable f
  · rw [swapRight_eq, map_map _ measurable_swap hf]
  · have : ¬ Measurable (f ∘ Prod.swap) := by
      contrapose! hf
      exact hf.comp measurable_swap
    simp [map_of_not_measurable _ hf, map_of_not_measurable _ this]

noncomputable
def deleteMiddle (κ : Kernel α (β × γ × δ)) :
    Kernel α (β × δ) :=
  mapOfMeasurable κ (fun p ↦ (p.1, p.2.2))
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

lemma deleteMiddle_eq (κ : Kernel α (β × γ × δ)) :
    deleteMiddle κ = map κ (fun p ↦ (p.1, p.2.2)) := by
  simp [deleteMiddle]

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (deleteMiddle κ) := by
  rw [deleteMiddle_eq]; apply IsMarkovKernel.map _ (by fun_prop)

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (deleteMiddle κ) := by
  rw [deleteMiddle_eq]; infer_instance

@[simp]
lemma fst_deleteMiddle (κ : Kernel α (β × γ × δ)) : fst (deleteMiddle κ) = fst κ := by
  rw [deleteMiddle_eq, fst_map_prod, fst_eq]
  exact measurable_snd.comp measurable_snd

@[simp]
lemma snd_deleteMiddle (κ : Kernel α (β × γ × δ)) : snd (deleteMiddle κ) = snd (snd κ) := by
  rw [deleteMiddle_eq, snd_map_prod, snd_eq, snd_eq, map_map _ measurable_snd measurable_snd]
  · rfl
  · exact measurable_fst

@[simp] lemma deleteMiddle_zero : deleteMiddle (0 : Kernel α (β × γ × δ)) = 0 := by
  simp [deleteMiddle_eq]

@[simp]
lemma deleteMiddle_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hg : Measurable g) :
    deleteMiddle (map κ (fun b ↦ (f b, g b, g' b)))
      = map κ (fun b ↦ (f b, g' b)) := by
  by_cases hfg' : Measurable (fun b ↦ (f b, g' b))
  · have : Measurable f := hfg'.fst
    have : Measurable g' := hfg'.snd
    rw [deleteMiddle_eq, map_map _ (by fun_prop) (by fun_prop)]
    rfl
  · have : ¬ (Measurable (fun b ↦ (f b, g b, g' b))) := by
      contrapose! hfg'
      have T : Measurable g' := hfg'.snd.snd
      have U : Measurable f := hfg'.fst
      exact U.prod T
    simp [map_of_not_measurable _ hfg', map_of_not_measurable _ this]

@[simp]
lemma deleteMiddle_compProd (ξ : Kernel α β) [IsSFiniteKernel ξ]
    (κ : Kernel (α × β) (γ × δ)) [IsSFiniteKernel κ] :
    deleteMiddle (ξ ⊗ₖ κ) = ξ ⊗ₖ snd κ := by
  ext x s hs
  rw [deleteMiddle_eq, map_apply' _ (by fun_prop) _ hs, compProd_apply hs, compProd_apply]
  swap; · exact measurable_fst.prodMk measurable_snd.snd hs
  congr with b
  rw [snd_apply']
  swap; · exact measurable_prodMk_left hs
  congr

noncomputable
def deleteRight (κ : Kernel α (β × γ × δ)) : Kernel α (β × γ) :=
  mapOfMeasurable κ (fun p ↦ (p.1, p.2.1))
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

lemma deleteRight_eq (κ : Kernel α (β × γ × δ)) :
    deleteRight κ = map κ (fun p ↦ (p.1, p.2.1)) := by simp [deleteRight]

@[simp] lemma deleteRight_zero : deleteRight (0 : Kernel α (β × γ × δ)) = 0 := by
  simp [deleteRight_eq]

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (deleteRight κ) := by
  rw [deleteRight_eq]; apply IsMarkovKernel.map _ (by fun_prop)

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (deleteRight κ) := by
  rw [deleteRight_eq]; infer_instance

@[simp]
lemma fst_deleteRight (κ : Kernel α (β × γ × δ)) : fst (deleteRight κ) = fst κ := by
  rw [deleteRight_eq, fst_map_prod, fst_eq]
  exact measurable_fst.comp measurable_snd

@[simp]
lemma snd_deleteRight (κ : Kernel α (β × γ × δ)) : snd (deleteRight κ) = fst (snd κ) := by
  rw [deleteRight_eq, snd_map_prod, snd_eq, fst_eq, map_map _ measurable_snd measurable_fst]
  · rfl
  · exact measurable_fst

@[simp]
lemma deleteRight_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} {g' : β → ε}
    (hg' : Measurable g') :
    deleteRight (map κ (fun b ↦ (f b, g b, g' b)))
      = map κ (fun b ↦ (f b, g b)) := by
  by_cases hfg : Measurable (fun b ↦ (f b, g b))
  · have : Measurable f := hfg.fst
    have : Measurable g := hfg.snd
    rw [deleteRight_eq, map_map _ (by fun_prop) (by fun_prop)]
    rfl
  · have : ¬ (Measurable (fun b ↦ (f b, g b, g' b))) := by
      contrapose! hfg
      have T : Measurable g := hfg.snd.fst
      have U : Measurable f := hfg.fst
      exact U.prod T
    simp [map_of_not_measurable _ hfg, map_of_not_measurable _ this]

noncomputable
def reverse (κ : Kernel α (β × γ × δ)) : Kernel α (δ × γ × β) :=
  mapOfMeasurable κ (fun p ↦ (p.2.2, p.2.1, p.1))
    ((measurable_snd.comp measurable_snd).prodMk
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst))

lemma reverse_eq (κ : Kernel α (β × γ × δ)) : reverse κ = map κ (fun p ↦ (p.2.2, p.2.1, p.1)) := by
  simp [reverse]

@[simp]
lemma reverse_reverse (κ : Kernel α (β × γ × δ)) :
    reverse (reverse κ) = κ := by
  have : ((fun p : δ × γ × β ↦ (p.2.2, p.2.1, p.1)) ∘ fun p ↦ (p.2.2, p.2.1, p.1)) = id := by
    ext1; simp
  rw [reverse_eq, reverse_eq, map_map _ (by fun_prop) (by fun_prop), this, map_id]

instance (κ : Kernel α (β × γ × δ)) [IsMarkovKernel κ] : IsMarkovKernel (reverse κ) := by
  rw [reverse_eq]; apply IsMarkovKernel.map _ (by fun_prop)

instance (κ : Kernel α (β × γ × δ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (reverse κ) := by
  rw [reverse_eq]; infer_instance

@[simp]
lemma swapRight_deleteMiddle_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteMiddle (reverse κ)) = deleteMiddle κ := by
  rw [swapRight_eq, reverse_eq, deleteMiddle_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop), deleteMiddle_eq]
  rfl

@[simp]
lemma swapRight_snd_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (snd (reverse κ)) = deleteRight κ := by
  rw [swapRight_eq, reverse_eq, deleteRight_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop)]
  rfl

@[simp]
lemma swapRight_deleteRight_reverse (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteRight (reverse κ)) = snd κ := by
  rw [swapRight_eq, reverse_eq, deleteRight_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop)]
  rfl

lemma FiniteKernelSupport.reverse
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (α × β × γ)} (hκ : FiniteKernelSupport κ) :
    FiniteKernelSupport (reverse κ) := by
  rw [reverse_eq]
  apply hκ.map

lemma AEFiniteKernelSupport.reverse
    [MeasurableSingletonClass S] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (S × β × γ)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (reverse κ) μ := by
  rw [reverse_eq]
  apply hκ.map

end
end ProbabilityTheory.Kernel
end

/- PFR.Mathlib.MeasureTheory.Measure.Dirac -/
noncomputable section
open scoped ProbabilityTheory
namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

@[simp]
lemma dirac_real_apply' (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by
  by_cases ha : a ∈ s <;> simp [Measure.real, *]

end MeasureTheory.Measure
end

/- PFR.Mathlib.MeasureTheory.Measure.Prod -/
noncomputable section
open scoped ProbabilityTheory
open Function
open scoped ENNReal NNReal

namespace MeasureTheory.Measure
variable {Ω α β γ : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}

lemma map_prod_comap_swap (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext s hs
  rw [Measure.map_apply (hZ.prodMk hX) hs, Measure.comap_apply _ Prod.swap_injective _ _ hs]
  · rw [Measure.map_apply (hX.prodMk hZ)]
    · congr!
      ext ω
      simp only [Set.image_swap_eq_preimage_swap, Set.mem_preimage, Prod.swap_prod_mk]
    · exact MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' hs
  · exact fun t ht ↦ MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' ht

lemma prod_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Measure.prod_prod]

lemma prod_real_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, prod_apply_singleton]

lemma prod_of_full_measure_finset {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
    {A : Finset α} {B : Finset β} (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) :
    (μ.prod ν) (A ×ˢ B : Finset (α × β))ᶜ = 0 := by
  have : (↑(A ×ˢ B) : Set (α × β))ᶜ = ((A : Set α)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set β)ᶜ) := by
    ext ⟨s, t⟩; simp; tauto
  rw [this]
  simp [hA, hB]

end MeasureTheory.Measure

open MeasureTheory

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsZeroOrProbabilityMeasure μ] {ν : Measure β} [IsZeroOrProbabilityMeasure ν] :
    IsZeroOrProbabilityMeasure (μ.prod ν) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp; infer_instance
  rcases eq_zero_or_isProbabilityMeasure ν with rfl | hν
  · simp; infer_instance
  infer_instance
end

/- PFR.Mathlib.MeasureTheory.Measure.Real -/
noncomputable section
open scoped ProbabilityTheory
open Function Set
open scoped ENNReal NNReal

namespace MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}

lemma Measure.ennreal_smul_real_apply (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by simp

lemma Measure.comap_real_apply {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (comap f μ).real s = μ.real (f '' s) := by simp [Measure.real, comap_apply _ hfi hf μ hs]

lemma Measure.prod_real_singleton (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, Measure.prod_apply_singleton]

variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']

end MeasureTheory
end

/- PFR.Mathlib.Data.Set.Basic -/
noncomputable section
open scoped ProbabilityTheory
namespace Set
variable {α : Type*} {s t : Set α}

@[simp] alias ⟨_, inter_eq_left'⟩ := inter_eq_left
@[simp] alias ⟨_, inter_eq_right'⟩ := inter_eq_right

@[simp] lemma ne_empty_iff_nonempty : s ≠ ∅ ↔ s.Nonempty := nonempty_iff_ne_empty.symm

end Set
end

/- PFR.Mathlib.Data.Set.Insert -/
noncomputable section
open scoped ProbabilityTheory
namespace Set
variable {α : Type*} {s t : Set α}

@[simp] alias ⟨_, inter_singleton_eq_empty'⟩ := inter_singleton_eq_empty

@[simp] alias ⟨_, singleton_inter_eq_empty'⟩ := singleton_inter_eq_empty

end Set
end

/- PFR.Mathlib.Data.Set.Card -/
noncomputable section
open scoped ProbabilityTheory
namespace Set
variable {α : Type*}

lemma ncard_inter_singleton (a : α) (s : Set α) [Decidable (a ∈ s)] :
    (s ∩ {a}).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]

end Set
end

/- PFR.Mathlib.Probability.UniformOn -/
noncomputable section
open scoped ProbabilityTheory
open Function MeasureTheory Measure

namespace ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}

lemma uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    uniformOn s {x} = 1 / Nat.card s := by
  have : {x} ∩ s = {x} := by ext y; simp +contextual [hx]
  simp only [uniformOn, cond, Measure.smul_apply, MeasurableSet.singleton, Measure.restrict_apply,
    this, Measure.count_singleton', smul_eq_mul, mul_one, one_div, inv_inj]
  rw [Measure.count_apply_finite _ hs, Nat.card_eq_card_finite_toFinset hs]

lemma uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) : uniformOn s {x} = 0 := by
  simp [uniformOn, cond, hx]

theorem uniformOn_apply_eq_zero (hst : s ∩ t = ∅) : uniformOn s t = 0 := by
  rcases Set.finite_or_infinite s with hs | hs
  · exact (uniformOn_eq_zero_iff hs).mpr hst
  · simp [uniformOn, cond, Measure.count_apply_infinite hs]

lemma uniformOn_of_infinite (hs : s.Infinite) : uniformOn s = 0 := by simp [hs]

lemma uniformOn_apply (hs : s.Finite) (t : Set Ω) :
    uniformOn s t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  rw [uniformOn, cond_apply hs.measurableSet, count_apply_finite _ hs,
    count_apply_finite _ (hs.inter_of_left _), ← Nat.card_eq_card_finite_toFinset,
    ← Nat.card_eq_card_finite_toFinset, ENNReal.div_eq_inv_mul]

lemma uniformOn_real (hs : s.Finite) (t : Set Ω) :
    (uniformOn s).real t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  simp [measureReal_def, uniformOn_apply hs]

instance uniformOn.instIsProbabilityMeasure [Nonempty s] [Finite s] :
    IsProbabilityMeasure (uniformOn s) := isProbabilityMeasure_uniformOn ‹_› .of_subtype

lemma map_uniformOn_apply {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) {t : Set Ω'}
    (ht : MeasurableSet t) :
    (uniformOn s).map f t = uniformOn (f '' s) t := by
  obtain hs | hs := s.infinite_or_finite
  · simp [uniformOn_of_infinite, hs, hs.image hf.injOn]
  · rw [map_apply hmes ht, uniformOn_apply hs, uniformOn_apply (hs.image _),
      Nat.card_image_of_injective hf, ← Nat.card_image_of_injective hf, Set.image_inter_preimage]

end ProbabilityTheory
end

/- PFR.ForMathlib.Entropy.Measure -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory Real Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] 
  [MeasurableSpace T] 
  [MeasurableSpace U] 

section measureEntropy
variable {μ : Measure S}

noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

class FiniteSupport (μ : Measure S := by volume_tac) : Prop where
  finite : ∃ A : Finset S, ∀ᵐ x ∂μ, x ∈ A

noncomputable
def _root_.MeasureTheory.Measure.pfrSupport (μ : Measure S) [hμ : FiniteSupport μ] : Finset S :=
  hμ.finite.choose.filter (μ {·} ≠ 0)

lemma measure_compl_support (μ : Measure S) [hμ : FiniteSupport μ] : μ μ.pfrSupportᶜ = 0 := by
  let A := hμ.finite.choose
  have : (μ.pfrSupport : Set S)ᶜ ⊆ (A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x} := by
    intro z hz
    simp only [Measure.pfrSupport, ne_eq, Finset.coe_filter, mem_compl_iff, mem_ofPred_eq, not_and,
      Decidable.not_not] at hz
    by_cases h'z : z ∈ A
    · simp [hz h'z, h'z]
    · simp [h'z]
  apply le_antisymm ?_ bot_le
  calc μ (μ.pfrSupport : Set S)ᶜ ≤ μ ((A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x}) :=
    measure_mono this
  _ ≤ μ (Aᶜ) + ∑ x ∈ A.filter (μ {·} = 0), μ {x} := by
    apply (measure_union_le _ _).trans
    gcongr
    apply measure_biUnion_finset_le
  _ ≤ 0 + ∑ x ∈ A.filter (μ {·} = 0), 0 := by
    gcongr with x hx
    · exact hμ.finite.choose_spec.le
    · simp only [Finset.mem_filter] at hx
      exact hx.2.le
  _ = 0 := by simp

lemma ae_mem_support (μ : Measure S) [FiniteSupport μ] : ∀ᵐ x ∂μ, x ∈ μ.pfrSupport :=
  measure_compl_support _

@[simp] lemma mem_support {μ : Measure S} [hμ : FiniteSupport μ] {x : S} :
    x ∈ μ.pfrSupport ↔ μ {x} ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Measure.pfrSupport, ne_eq, Finset.mem_filter] at h
    exact h.2
  · contrapose! h
    exact measure_mono_null (by simpa using h) (measure_compl_support μ)

instance finiteSupport_zero : FiniteSupport (0 : Measure S) where
  finite := ⟨(∅ : Finset S), by simp⟩

noncomputable def FiniteEntropy (μ : Measure S := by volume_tac) : Prop :=
  Summable (fun s ↦ negMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal) ∧
  ∃ A : Set S, Countable A ∧ μ Aᶜ = 0

instance finiteSupport_of_fintype {μ : Measure S} [Finite S] : FiniteSupport μ := by
  cases nonempty_fintype S
  use Finset.univ
  simp

instance finiteSupport_of_mul {μ : Measure S} [FiniteSupport μ] (c : ℝ≥0∞) :
    FiniteSupport (c • μ) := ⟨μ.pfrSupport, Measure.ae_smul_measure (ae_mem_support _) _⟩

section

variable [MeasurableSingletonClass S]

instance finiteSupport_of_dirac (x : S) : FiniteSupport (Measure.dirac x) := ⟨{x}, by simp⟩

lemma full_measure_of_finiteRange {μ : Measure Ω} {X : Ω → S}
    (hX : Measurable X) [hX' : FiniteRange X] :
    (μ.map X) hX'.toFinsetᶜ = 0 := by
  rw [Measure.map_apply hX (MeasurableSet.compl (Finset.measurableSet _))]
  convert measure_empty (μ := μ)
  ext x
  simp [FiniteRange.toFinset]

lemma ae_mem_of_finiteRange {μ : Measure Ω} {X : Ω → S} (hX : Measurable X) [hX' : FiniteRange X] :
    ∀ᵐ x ∂μ.map X, x ∈ hX'.toFinset := full_measure_of_finiteRange hX

instance finiteSupport_of_finiteRange {μ : Measure Ω} {X : Ω → S} [hX' : FiniteRange X] :
    FiniteSupport (μ.map X) := by
  use hX'.toFinset
  exact FiniteRange.null_of_compl μ X

instance finiteSupport_of_prod {μ : Measure S} [FiniteSupport μ] {ν : Measure T} [SigmaFinite ν]
    [FiniteSupport ν] :
    FiniteSupport (μ.prod ν) := by
  use μ.pfrSupport ×ˢ ν.pfrSupport
  exact Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support ν)

lemma integrable_of_finiteSupport (μ : Measure S) [FiniteSupport μ]
    {β : Type*} [NormedAddCommGroup β] [IsFiniteMeasure μ] [Countable S]
    {f : S → β} :
    Integrable f μ := by
  let A := μ.pfrSupport
  have hA : μ Aᶜ = 0 := measure_compl_support μ
  by_cases hA' : A = ∅
  · simp only [hA', Finset.coe_empty, compl_empty, Measure.measure_univ_eq_zero] at hA
    rw [hA]
    exact integrable_zero_measure
  have : ∃ s₀, s₀ ∈ A := by
    contrapose! hA'
    ext s
    simpa using hA' s
  rcases this with ⟨s₀, hs₀⟩
  let f' : A → β := fun a ↦ f a
  classical
  let g : S → A := fun s ↦ if h : s ∈ A then ⟨s, h⟩ else ⟨s₀, hs₀⟩
  have : (f' ∘ g) =ᵐ[μ] f := by
    apply Filter.eventuallyEq_of_mem (s := A) hA
    intro a ha
    simp at ha
    simp [f', g, ha]
  apply Integrable.congr _ this
  apply Integrable.comp_measurable .of_finite
  fun_prop

lemma integral_congr_finiteSupport {μ : Measure Ω} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : Ω → G} [FiniteSupport μ]
    (hfg : ∀ x, μ {x} ≠ 0 → f x = g x) : ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  refine integral_congr_ae <| measure_mono_null ?_ <| measure_compl_support μ
  exact fun x hx hx' ↦ hx <| hfg _ <| mem_support.1 hx'

theorem Measure.ext_iff_singleton_finiteSupport
    {μ1 μ2 : Measure S} [FiniteSupport μ1] [FiniteSupport μ2] :
    μ1 = μ2 ↔ ∀ x, μ1 {x} = μ2 {x} := by
  classical
  constructor
  · rintro rfl
    simp
  · let A1 := μ1.pfrSupport
    have hA1 := measure_compl_support μ1
    let A2 := μ2.pfrSupport
    have hA2 := measure_compl_support μ2
    intro h
    ext s
    have h1 : μ1 s = μ1 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_sdiff _ _).symm
      · simp
      refine measure_mono_null ?_ hA1
      intro x
      simp (config := { contextual := true }) [A1]
    have h2 : μ2 s = μ2 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_sdiff _ _).symm
      · simp
      exact measure_mono_null (fun x ↦ by simp (config := { contextual := true }) [A2]) hA2
    rw [h1, h2]
    have hs : Set.Finite (s ∩ (A1 ∪ A2)) := Set.toFinite (s ∩ (↑A1 ∪ ↑A2))
    rw [← hs.coe_toFinset, ← sum_measure_singleton (μ := μ1), ← sum_measure_singleton (μ := μ2)]
    simp_rw [h]

theorem Measure.ext_iff_measureReal_singleton_finiteSupport {μ1 μ2 : Measure S}
    [FiniteSupport μ1] [FiniteSupport μ2] [IsFiniteMeasure μ1] [IsFiniteMeasure μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton_finiteSupport]
  congr! with x
  have h1 : μ1 {x} ≠ ⊤ := by finiteness
  have h2 : μ2 {x} ≠ ⊤ := by finiteness
  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  simp [h1, h2]

end

lemma measureEntropy_eq_sum {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0) :
   (ProbabilityTheory.measureEntropy μ) = ∑ s ∈ A, negMulLog (((μ Set.univ)⁻¹ • μ).real {s}) := by
  unfold measureEntropy
  rw [tsum_eq_sum]
  intro s hs
  suffices μ.real {s} = 0 by simp [this]
  rw [Measure.real, measure_mono_null (by simpa) hA]
  simp

@[simp]
lemma measureEntropy_zero : (ProbabilityTheory.measureEntropy ((0 : Measure S))) = 0 := by simp [measureEntropy]

@[simp]
lemma measureEntropy_dirac [MeasurableSingletonClass S] (x : S) : (ProbabilityTheory.measureEntropy (Measure.dirac x)) = 0 := by
  rw [measureEntropy]
  simp only [MeasurableSet.univ, Measure.dirac_apply', mem_univ, indicator_of_mem, Pi.one_apply,
    inv_one, one_smul]
  rw [tsum_eq_single x]
  · simp only [Measure.real, MeasurableSet.singleton, Measure.dirac_apply', mem_singleton_iff,
    indicator_of_mem, Pi.one_apply, ENNReal.toReal_one, negMulLog_one]
  · simp +contextual [eq_comm]

lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : (ProbabilityTheory.measureEntropy μ) = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    (ProbabilityTheory.measureEntropy μ) = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [measureEntropy]
  · simp [measureEntropy]

lemma measureEntropy_of_isProbabilityMeasure_finite {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    (ProbabilityTheory.measureEntropy μ) = ∑ s ∈ A, negMulLog (μ.real {s}) := by
  rw [measureEntropy_eq_sum hA]
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;> simp

lemma measureEntropy_of_isProbabilityMeasure_finite' {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    (ProbabilityTheory.measureEntropy μ) = ∑ s ∈ A, negMulLog (μ.real {s}) :=
  measureEntropy_of_isProbabilityMeasure_finite hA

lemma measureEntropy_univ_smul : (ProbabilityTheory.measureEntropy ((μ Set.univ)⁻¹ • μ)) = (ProbabilityTheory.measureEntropy μ) := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => simp [measureEntropy]

lemma measureEntropy_nonneg (μ : Measure S) : 0 ≤ (ProbabilityTheory.measureEntropy μ) := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap; · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
  apply tsum_nonneg
  intro s
  apply negMulLog_nonneg (by positivity)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

variable [MeasurableSingletonClass S]

lemma measureEntropy_le_card_aux {μ : Measure S} [IsProbabilityMeasure μ]
    (A : Finset S) (hμ : μ Aᶜ = 0) :
    (ProbabilityTheory.measureEntropy μ) ≤ log A.card := by
  have μA : μ A = 1 := by
    rw [← compl_compl (A : Set S), measure_compl A.measurableSet.compl (measure_ne_top _ _), hμ]
    simp
  let N := A.card
  have N_pos : (0 : ℝ) < N := by
    rcases Finset.eq_empty_or_nonempty A with rfl|hA
    · simp at μA
    · simpa [N] using Finset.card_pos.mpr hA
  simp only [measureEntropy, measure_univ, inv_one, one_smul]
  calc
  ∑' x, negMulLog (μ.real {x})
    = ∑ x ∈ A, negMulLog (μ.real {x}) := by
      apply tsum_eq_sum
      intro i hi
      have : μ {i} = 0 :=
        le_antisymm ((measure_mono (by simpa using hi)).trans (le_of_eq hμ)) bot_le
      simp [Measure.real, this]
  _ = N * ∑ x ∈ A, (N : ℝ)⁻¹ * negMulLog (μ.real {x}) := by
      rw [Finset.mul_sum]
      congr with x
      rw [← mul_assoc, mul_inv_cancel₀, one_mul]
      exact N_pos.ne'
  _ ≤ N * negMulLog (∑ x ∈ A, (N : ℝ)⁻¹ * (μ.real {x})) := by
      gcongr
      exact concaveOn_negMulLog.le_map_sum (by simp) (by simp [mul_inv_cancel₀ N_pos.ne', N])
        (by simp)
  _ = N * negMulLog ((N : ℝ)⁻¹) := by simp [← Finset.mul_sum]; simp [μA, Measure.real]
  _ = log A.card := by simp [negMulLog, ← mul_assoc, mul_inv_cancel₀ N_pos.ne', N]

lemma measureEntropy_eq_card_iff_measureReal_eq_aux [Fintype S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    (ProbabilityTheory.measureEntropy μ) = log (Fintype.card S) ↔ ∀ s, μ.real {s} = (Fintype.card S : ℝ)⁻¹ := by
  cases isEmpty_or_nonempty S
  · simp [Fintype.card_eq_zero, Subsingleton.elim μ 0]
  
  set N := Fintype.card S
  have hN : (N:ℝ)⁻¹ ≠ 0 := by positivity
  rw [← mul_right_inj' hN]
  
  let w (_ : S) := (N:ℝ)⁻¹
  have hw1 : ∀ s ∈ Finset.univ, 0 < w s := by intros; positivity
  have hw2 : ∑ s : S, w s = 1 := by simp [w, Finset.card_univ, N]
  let p (s : S) := μ.real {s}
  have hp : ∀ s ∈ Finset.univ, 0 ≤ p s := by intros; positivity
  rw [measureEntropy, tsum_fintype, eq_comm]
  convert strictConcaveOn_negMulLog.map_sum_eq_iff hw1 hw2 hp using 2
  · simp [w, p, negMulLog, ← Finset.mul_sum]
  · simp [Finset.mul_sum, w, p]
  · simp [p, ← Finset.mul_sum, w, p]

lemma measureEntropy_le_log_card_of_mem
    {A : Finset S} (μ : Measure S) (hμA : μ Aᶜ = 0) :
    (ProbabilityTheory.measureEntropy μ) ≤ log A.card := by
  have h_log_card_nonneg : 0 ≤ log (Nat.card A) := log_natCast_nonneg (Nat.card ↑A)
  rcases eq_zero_or_neZero μ with rfl|hμ
  · simp
    positivity
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureEntropy_univ_smul]
    exact measureEntropy_le_card_aux A <| by simp [hμA]
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    exact log_natCast_nonneg _

lemma measureEntropy_le_log_card [Fintype S] (μ : Measure S) : (ProbabilityTheory.measureEntropy μ) ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card_of_mem (A := (Finset.univ : Finset S)) μ (by simp)

lemma measureEntropy_eq_card_iff_measureReal_eq [Fintype S] [IsFiniteMeasure μ] [NeZero μ] :
    (ProbabilityTheory.measureEntropy μ) = log (Fintype.card S) ↔ ∀ s : S, μ.real {s} = μ.real Set.univ / Fintype.card S := by
  rw [← measureEntropy_univ_smul]
  convert measureEntropy_eq_card_iff_measureReal_eq_aux ((μ Set.univ)⁻¹ • μ) using 2 with s
  simp only [measureReal_ennreal_smul_apply]
  rw [ENNReal.toReal_inv, inv_mul_eq_iff_eq_mul₀ (by exact measureReal_univ_ne_zero),
    div_eq_mul_inv]
  rfl

lemma measureEntropy_eq_card_iff_measure_eq [Fintype S] [IsFiniteMeasure μ] [NeZero μ] :
    (ProbabilityTheory.measureEntropy μ) = log (Fintype.card S) ↔
    (∀ s : S, μ {s} = μ Set.univ / Fintype.card S) := by
  obtain h | h := isEmpty_or_nonempty S
  · have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  rw [div_eq_mul_inv, measureEntropy_eq_card_iff_measureReal_eq]
  congr! with s
  rw [measureReal_def, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ {s})]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  · finiteness

lemma measureEntropy_map_of_injective
    (μ : Measure T) (f : T → S) (hf_m : Measurable f) (hf : Function.Injective f) :
    (ProbabilityTheory.measureEntropy (μ.map f)) = (ProbabilityTheory.measureEntropy μ) := by
  have : μ.map f Set.univ = μ Set.univ := by
      rw [Measure.map_apply hf_m MeasurableSet.univ]
      simp
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    map_measureReal_apply hf_m (.singleton _)]
  rw [this]
  classical
  let F (x : S) : ℝ := negMulLog ((μ Set.univ)⁻¹.toReal • μ.real (f ⁻¹' {x}))
  have : ∑' x : S, F x
      = ∑' x : (f '' Set.univ), F x := by
    apply (tsum_subtype_eq_of_support_subset _).symm
    intro x hx
    contrapose hx
    suffices f ⁻¹' {x} = ∅ by simp [F, this]
    contrapose! hx
    rw [Set.image_univ]
    exact hx
  rw [this, tsum_image _ hf.injOn, tsum_univ fun x ↦ F (f x)]
  congr! with s
  ext s'
  simpa using hf.eq_iff

lemma measureEntropy_comap (μ : Measure T) (f : S → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ) :
    (ProbabilityTheory.measureEntropy (μ.comap f)) = (ProbabilityTheory.measureEntropy μ) := by
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    Measure.comap_real_apply hf.injective hf.measurableSet_image' _ (.singleton _),
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ MeasurableSet.univ]
  simp only [Set.image_univ, Set.image_singleton, smul_eq_mul]
  classical
  rw [← tsum_range (f := fun x ↦ negMulLog ((μ (Set.range f))⁻¹.toReal * μ.real {x})) (g := f)
    hf.injective, measure_congr hf_range ]
  let F (x : T) : ℝ := negMulLog ((μ .univ)⁻¹.toReal * μ.real {x})
  change ∑' x : (Set.range f), F x = ∑' x : T, F x
  apply tsum_subtype_eq_of_support_subset
  intro x hx
  contrapose hx
  suffices μ {x} = 0 by simp [F, Measure.real, this]
  simp only [ae_eq_univ] at hf_range
  exact measure_mono_null (by simp [*]) hf_range

@[simp]
lemma measureEntropy_prod {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableSingletonClass T] :
    (ProbabilityTheory.measureEntropy (μ.prod ν)) = (ProbabilityTheory.measureEntropy μ) + (ProbabilityTheory.measureEntropy ν) := by
  let A := μ.pfrSupport
  have hA := measure_compl_support μ
  let B := ν.pfrSupport
  have hB := measure_compl_support ν
  have hC : (μ.prod ν) (A ×ˢ B : Finset (S × T))ᶜ = 0 := by
    have : ((A ×ˢ B : Finset (S × T)) : Set (S × T))ᶜ
      = ((A : Set S)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set T)ᶜ) := by ext ⟨a, b⟩; simp; tauto
    rw [this]
    simp [hA, hB, A, B]
  have h1 : (ProbabilityTheory.measureEntropy μ) = ∑ p ∈ (A ×ˢ B), (negMulLog (μ.real {p.1})) * (ν.real {p.2}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hA, Finset.sum_product]
    congr with s
    dsimp
    simp only [← Finset.mul_sum, sum_measureReal_singleton]
    suffices ν.real B = ν.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hB, B]
  have h2 : (ProbabilityTheory.measureEntropy ν) = ∑ p ∈ (A ×ˢ B), (negMulLog (ν.real {p.2})) * (μ.real {p.1}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite' hB, Finset.sum_product_right]
    congr with t
    dsimp
    simp only [← Finset.mul_sum, sum_measureReal_singleton]
    suffices μ.real A = μ.real Set.univ by simp at this; simp [this]
    apply measureReal_congr
    simp [hA, A]
  rw [measureEntropy_of_isProbabilityMeasure_finite' hC, h1, h2, ← Finset.sum_add_distrib]
  congr with ⟨s, t⟩
  simp_rw [← Set.singleton_prod_singleton, measureReal_prod_prod, negMulLog_mul]
  ring

end measureEntropy

section measureMutualInfo

noncomputable
def measureMutualInfo (μ : Measure (S × T) := by volume_tac) : ℝ :=
  (ProbabilityTheory.measureEntropy (μ.map Prod.fst)) + (ProbabilityTheory.measureEntropy (μ.map Prod.snd)) - (ProbabilityTheory.measureEntropy μ)

lemma measureMutualInfo_def (μ : Measure (S × T)) :
    (ProbabilityTheory.measureMutualInfo μ) = (ProbabilityTheory.measureEntropy (μ.map Prod.fst)) + (ProbabilityTheory.measureEntropy (μ.map Prod.snd)) - (ProbabilityTheory.measureEntropy μ) := rfl

@[simp]
lemma measureMutualInfo_zero_measure : (ProbabilityTheory.measureMutualInfo ((0 : Measure (S × T)))) = 0 := by
  simp [measureMutualInfo]

lemma measureMutualInfo_of_not_isFiniteMeasure {μ : Measure (S × U)} (h : ¬ IsFiniteMeasure μ) :
    (ProbabilityTheory.measureMutualInfo μ) = 0 := by
  rw [measureMutualInfo_def]
  have h1 : ¬ IsFiniteMeasure (μ.map Prod.fst) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    exact Measure.map_apply measurable_fst MeasurableSet.univ
  have h2 : ¬ IsFiniteMeasure (μ.map Prod.snd) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    exact Measure.map_apply measurable_snd MeasurableSet.univ
  rw [measureEntropy_of_not_isFiniteMeasure h, measureEntropy_of_not_isFiniteMeasure h1,
    measureEntropy_of_not_isFiniteMeasure h2]
  simp

lemma measureMutualInfo_univ_smul (μ : Measure (S × U)) : (ProbabilityTheory.measureMutualInfo ((μ Set.univ)⁻¹ • μ)) = (ProbabilityTheory.measureMutualInfo μ) := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  rcases eq_zero_or_neZero μ with hμ | _
  · simp [hμ]
  rw [measureMutualInfo_def, measureMutualInfo_def]
  congr 1
  · congr 1
    · convert measureEntropy_univ_smul
      simp [Measure.map_smul, Measure.map_apply measurable_fst]
    · convert measureEntropy_univ_smul
      simp [Measure.map_smul, Measure.map_apply measurable_snd]
  convert measureEntropy_univ_smul

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]

@[simp]
lemma measureMutualInfo_prod {μ : Measure S} {ν : Measure T} [FiniteSupport μ] [FiniteSupport ν]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (ProbabilityTheory.measureMutualInfo (μ.prod ν)) = 0 := by
  rw [measureMutualInfo_def, measureEntropy_prod]
  simp

lemma measureMutualInfo_nonneg_aux {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    0 ≤ (ProbabilityTheory.measureMutualInfo μ) ∧
    ((ProbabilityTheory.measureMutualInfo μ) = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have : IsProbabilityMeasure (μ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let E := μ.pfrSupport
  have hE := measure_compl_support μ
  classical
  set E1 : Finset S := Finset.image Prod.fst E
  set E2 : Finset U := Finset.image Prod.snd E
  have hE' : μ (E1 ×ˢ E2 : Finset (S × U))ᶜ = 0 := by
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    contrapose!
    intro h
    simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
      Finset.coe_product, mem_prod, not_and, Classical.not_imp] at h ⊢
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E, E2,
      mem_support]
    constructor
    · use u
    · use s
  have hE1 : (μ.map Prod.fst) E1ᶜ = 0 := by
    rw [Measure.map_apply measurable_fst (MeasurableSet.compl (Finset.measurableSet E1))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E,
      mem_support]
    intro h; use u
  have hE1' : (μ.map Prod.fst).real E1 = 1 := by
    rw [prob_compl_eq_zero_iff E1.measurableSet] at hE1
    unfold Measure.real
    rw [hE1]
    norm_num
  have hE2 : (μ.map Prod.snd) E2ᶜ = 0 := by
    rw [Measure.map_apply measurable_snd (MeasurableSet.compl (Finset.measurableSet E2))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_eq_right, E2, E, mem_support]
    intro h; use s
  have hE2' : (μ.map Prod.snd).real E2 = 1 := by
    rw [prob_compl_eq_zero_iff E2.measurableSet] at hE2
    unfold Measure.real
    rw [hE2]
    norm_num
  have h_fst_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.fst).real {p.1} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_fst (.singleton _)]
    refine fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h_snd_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.snd).real {p.2} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_snd (.singleton _)]
    exact fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h1 y : (μ.map Prod.fst).real {y} = ∑ z ∈ E2, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_fst (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_eq_right, iUnion_exists, mem_iUnion,
          mem_singleton_iff, Prod.mk.injEq, true_and, exists_prop, exists_and_right,
          exists_eq_right', E2, E] at h2 ⊢
        use s
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  have h2 z : (μ.map Prod.snd).real {z} = ∑ y ∈ E1, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_snd (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, iUnion_exists,
          mem_iUnion, mem_singleton_iff, Prod.mk.injEq, and_true, exists_prop, exists_eq_right', E1,
          E] at h2 ⊢
        use u
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  let w (p : S × U) := (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}
  let f (p : S × U) := ((μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2})⁻¹ * μ.real {p}
  have hw1 : ∀ p ∈ (E1 ×ˢ E2), 0 ≤ w p := by intros; positivity
  have hw2 : ∑ p ∈ E1 ×ˢ E2, w p = 1 := by
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum, sum_measureReal_singleton, w]
    rw [← Finset.sum_mul]
    rw [show (1 : ℝ) = 1 * 1 by norm_num]
    congr
    convert hE1'
    simp
  have hf : ∀ p ∈ E1 ×ˢ E2, 0 ≤ f p := by intros; positivity
  have H :=
  calc
    ∑ p ∈ E1 ×ˢ E2, w p * f p
        = ∑ p ∈ E1 ×ˢ E2, μ.real {p} := by
          congr with p
          by_cases hp : μ.real {p} = 0
          · simp [f, hp]
          · simp [w, f]
            field_simp [h_fst_ne_zero p hp, h_snd_ne_zero p hp]
      _ = 1 := by
        simp only [sum_measureReal_singleton, Finset.coe_product]
        rw [show 1 = μ.real Set.univ by simp]
        apply measureReal_congr
        simpa using hE'
  have H1 : -measureMutualInfo (μ := μ) = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := calc
    _ = ∑ p ∈ E1 ×ˢ E2,
          (-(μ.real {p} * log (μ.real {p}))
          + (μ.real {p} * log ((μ.map Prod.snd).real {p.2})
            + μ.real {p} * log ((μ.map Prod.fst).real {p.1}))) := by
        have H0 : (ProbabilityTheory.measureEntropy μ) = -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log (μ.real {p}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE', negMulLog, neg_mul,
            Finset.sum_neg_distrib]
        have H1 : (ProbabilityTheory.measureEntropy (μ.map Prod.fst)) = -∑ p ∈ E1 ×ˢ E2,
            μ.real {p} * log ((μ.map Prod.fst).real {p.1}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE1, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product, ← Finset.sum_mul]
          congr! with s _
          exact h1 s
        have H2 : (ProbabilityTheory.measureEntropy (μ.map Prod.snd)) =
            -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log ((μ.map Prod.snd).real {p.2}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE2, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product_right, ← Finset.sum_mul]
          congr! with s _
          exact h2 s
        simp_rw [measureMutualInfo_def, H0, H1, H2]
        simp [Finset.sum_add_distrib]
    _ = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := by
        congr! 1 with p _
        by_cases hp : μ.real {p} = 0
        · simp [f, hp]
        have := h_fst_ne_zero p hp
        have := h_snd_ne_zero p hp
        simp [negMulLog, log_mul, log_inv, h_fst_ne_zero p hp, h_snd_ne_zero p hp, hp, w, f]
        field_simp
        ring
  have H2 : 0 = negMulLog (∑ s ∈ (E1 ×ˢ E2), w s * f s) := by
    rw [H, negMulLog_one]
  constructor
  · rw [← neg_nonpos, H1, H2]
    exact concaveOn_negMulLog.le_map_sum hw1 hw2 hf
  rw [← neg_eq_zero, H1, H2, eq_comm]
  refine (strictConcaveOn_negMulLog.map_sum_eq_iff' hw1 hw2 hf).trans ?_
  have w0 (p : S × U) (hp: w p = 0) : μ.real {p} = 0 := by
    simp only [mul_eq_zero, w] at hp
    rcases hp with hp | hp
    · contrapose! hp; exact (h_fst_ne_zero p) hp
    · contrapose! hp; exact (h_snd_ne_zero p) hp
  constructor
  · intro hyp p
    by_cases hp1 : p.1 ∈ E1
    · by_cases hp2 : p.2 ∈ E2
      · have hp : p ∈ E1 ×ˢ E2 := Finset.mem_product.mpr ⟨hp1, hp2⟩
        by_cases hw : w p = 0
        · rw [w0 p hw]
          exact hw.symm
        replace hyp := hyp p hp hw
        simp_rw [smul_eq_mul, H] at hyp
        have := eq_of_inv_mul_eq_one hyp
        convert this.symm
      have : {p.2} ⊆ (E2 : Set U)ᶜ := by
        simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp2
      replace : (Measure.map Prod.snd μ).real {p.2} = 0 := by
        rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE2
      have hp : μ.real {p} = 0 := by contrapose! this; exact (h_snd_ne_zero p) this
      simp [hp, this]
    have : {p.1} ⊆ (E1 : Set S)ᶜ := by
      simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]; convert hp1
    replace : (Measure.map Prod.fst μ).real {p.1} = 0 := by
      rw [measureReal_eq_zero_iff]; exact measure_mono_null this hE1
    have hp : μ.real {p} = 0 := by contrapose! this; exact (h_fst_ne_zero p) this
    simp [hp, this]
  intro hyp ⟨s, u⟩ _ hw
  simp_rw [smul_eq_mul, H]
  change (w (s,u))⁻¹ * (μ.real {(s,u)}) = 1
  have : w (s,u) ≠ 0 := by exact hw
  field_simp [this]
  rw [hyp (s,u)]

lemma measureMutualInfo_nonneg {μ : Measure (S × U)} [FiniteSupport μ] :
    0 ≤ (ProbabilityTheory.measureMutualInfo μ) := by
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureMutualInfo_univ_smul μ]
    apply measureMutualInfo_nonneg_aux.1
  rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]

lemma measureMutualInfo_eq_zero_iff {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    (ProbabilityTheory.measureMutualInfo μ) = 0 ↔ ∀ p, μ.real {p} = (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2} :=
  measureMutualInfo_nonneg_aux.2

end measureMutualInfo

end ProbabilityTheory
end

/- PFR.ForMathlib.Entropy.Kernel.Basic -/
noncomputable section
open scoped ProbabilityTheory
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

noncomputable
def entropy (κ : Kernel T S) (μ : Measure T) := μ[fun y ↦ (ProbabilityTheory.measureEntropy (κ y))]

@[simp]
lemma entropy_zero_measure (κ : Kernel T S) : (Kernel.entropy κ ((0 : Measure T))) = 0 := by simp [entropy]

@[simp]
lemma entropy_zero_kernel (μ : Measure T) : (Kernel.entropy ((0 : Kernel T S)) μ) = 0 := by simp [entropy]

lemma entropy_congr {μ} {κ η : Kernel T S} (h : κ =ᵐ[μ] η) : (Kernel.entropy κ μ) = (Kernel.entropy η μ) := by
  simp_rw [entropy]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

lemma entropy_nonneg (κ : Kernel T S) (μ : Measure T) :
    0 ≤ (Kernel.entropy κ μ) := integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

@[simp]
lemma entropy_const (ν : Measure S) (μ : Measure T) :
    (Kernel.entropy (Kernel.const T ν) μ) = (μ Set.univ).toReal * (ProbabilityTheory.measureEntropy ν) := by
  simp [entropy, Measure.real]

lemma finiteKernelSupport_of_const (ν : Measure S) [FiniteSupport ν] :
    FiniteKernelSupport (Kernel.const T ν) := by
  intro t
  use ν.pfrSupport
  simp [measure_compl_support ν]

lemma finiteSupport_of_compProd' [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  let A := μ.pfrSupport
  have hA := measure_compl_support μ
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Measure.ae_compProd_iff (by exact (Finset.finite_toSet _).measurableSet)]
  filter_upwards [ae_mem_support μ] with t ht
  filter_upwards [hB t ht] with s hs
  exact Finset.mk_mem_product ht hs

lemma finiteSupport_of_compProd
    [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  rw [Measure.compProd_congr hκ.ae_eq_mk]
  exact finiteSupport_of_compProd' hκ.finiteKernelSupport_mk

lemma aefiniteKernelSupport_condDistrib
    [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] :
    AEFiniteKernelSupport (condDistrib X Y μ) (μ.map Y) := by
  filter_upwards [condDistrib_ae_eq hX hY μ] with a ha
  rw [ha]
  exact finiteSupport_of_finiteRange.finite

lemma entropy_le_log_card
   [MeasurableSingletonClass S]
   (κ : Kernel T S) (μ : Measure T) [Fintype S] [IsProbabilityMeasure μ] :
    (Kernel.entropy κ μ) ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ measureEntropy_nonneg _)
  · exact ae_of_all _ (fun _ ↦ measureEntropy_le_log_card _)
  · simp

lemma entropy_snd_compProd_deterministic_of_injective [MeasurableSingletonClass U]
    (κ : Kernel T S) [IsMarkovKernel κ]
    (μ : Measure T) {f : T × S → U}
    (hf : ∀ t, Function.Injective (fun x ↦ f (t, x))) (hmes : Measurable f) :
    (Kernel.entropy (snd (κ ⊗ₖ deterministic f hmes)) μ) = (Kernel.entropy κ μ) := by
  have : ∀ t, snd (κ ⊗ₖ deterministic f hmes) t
      = map κ (fun x ↦ f (t, x)) t := by
    intro t
    ext s hs
    rw [snd_apply' _ _ hs, compProd_deterministic_apply, map_apply' _ (by fun_prop) _ hs]
    · rfl
    · exact measurable_snd hs
  simp_rw [entropy]
  congr with y
  convert measureEntropy_map_of_injective (κ y) _ (hmes.comp measurable_prodMk_left) (hf y)
  rw [this y, map_apply _ (by fun_prop)]
  rfl

lemma entropy_map_of_injective [MeasurableSingletonClass U]
    (κ : Kernel T S) (μ : Measure T) {f : S → U} (hf : Function.Injective f) (hmes : Measurable f) :
    (Kernel.entropy (map κ f) μ) = (Kernel.entropy κ μ) := by
  simp_rw [entropy, map_apply _ hmes, measureEntropy_map_of_injective _ _ hmes hf]

lemma entropy_map_swap [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (κ : Kernel T (S × U)) (μ : Measure T) :
    (Kernel.entropy (map κ Prod.swap) μ) = (Kernel.entropy κ μ) :=
  entropy_map_of_injective κ μ Prod.swap_injective measurable_swap

lemma entropy_swapRight [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (κ : Kernel T (S × U)) (μ : Measure T) :
    (Kernel.entropy (swapRight κ) μ) = (Kernel.entropy κ μ) := by
  rw [swapRight_eq, entropy_map_swap]

lemma entropy_comap [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel T S) (μ : Measure T) (f : T' → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure (μ.comap f)] (hfμ : FiniteSupport (μ.comap f)) :
    (Kernel.entropy (comap κ f hf.measurable) (μ.comap f)) = (Kernel.entropy κ μ) := by
  classical
  rcases hfμ with ⟨A, (hA : ∀ᵐ x ∂μ.comap f, x ∈ A)⟩
  have : ∀ᵐ x ∂μ, x ∈ Finset.image f A := by
    change μ (Finset.image f A : Set T)ᶜ = 0
    simp only [Finset.coe_image, hf.injective.compl_image_eq, measure_union_null_iff]
    constructor
    · rwa [← Measure.comap_apply f hf.injective hf.measurableSet_image']
      exact MeasurableSet.compl (Finset.measurableSet A)
    exact ae_eq_univ.mp hf_range
  simp_rw [entropy]
  simp_rw [integral_eq_setIntegral hA, integral_eq_setIntegral this,
    setIntegral_finset _ .finset,
    Measure.comap_real_apply hf.injective hf.measurableSet_image' _ (.singleton _)]
  simp only [Set.image_singleton, smul_eq_mul]
  simp_rw [comap_apply]
  rw [← Finset.sum_image (f := fun x ↦ μ.real {x} * measureEntropy (κ x)) (g := f)]
  intro x _ y _ hxy
  exact hf.injective hxy

lemma FiniteSupport.comap_equiv [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T']
    {μ : Measure T} (f : T' ≃ᵐ T) [FiniteSupport μ] :
    FiniteSupport (μ.comap f) := by
  classical
  let A := μ.pfrSupport
  have hA := measure_compl_support μ
  refine ⟨Finset.image f.symm A, ?_⟩
  change (Measure.comap (⇑f) μ) (A.image f.symm)ᶜ = 0
  rwa [Finset.coe_image, ← Set.image_compl_eq (MeasurableEquiv.bijective f.symm),
    Measure.comap_apply f (MeasurableEquiv.injective f),MeasurableEquiv.image_symm,
    MeasurableEquiv.image_preimage]
  · exact fun _ ↦ (MeasurableEquiv.measurableSet_image f).mpr
  · exact f.symm.measurableSet_image.mpr A.measurableSet.compl

lemma entropy_comap_equiv [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel T S) {μ : Measure T} (f : T' ≃ᵐ T)
    [IsFiniteMeasure μ] [FiniteSupport μ] :
    (Kernel.entropy (comap κ f f.measurable) (μ.comap f)) = (Kernel.entropy κ μ) := by
  simp [entropy_comap, f.measurableEmbedding, FiniteSupport.comap_equiv f]

lemma entropy_comap_swap [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel (T' × T) S) {μ : Measure (T' × T)} [IsFiniteMeasure μ] [FiniteSupport μ] :
    (Kernel.entropy (comap κ Prod.swap measurable_swap) (μ.comap Prod.swap)) = (Kernel.entropy κ μ) :=
  entropy_comap_equiv κ MeasurableEquiv.prodComm

lemma entropy_prodMkLeft_unit [MeasurableSingletonClass T]
    (κ : Kernel T S) {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] :
    (Kernel.entropy (prodMkLeft Unit κ) (μ.map (Prod.mk ()))) = (Kernel.entropy κ μ) := by
  convert entropy_comap_equiv κ (.punitProd) (μ := μ)
  · rfl
  rw [← MeasurableEquiv.map_symm]
  congr

lemma entropy_compProd_aux [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] {μ} [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ] (hκ : FiniteKernelSupport κ)
    (hη : FiniteKernelSupport η) :
    (Kernel.entropy (κ ⊗ₖ η) μ) = (Kernel.entropy κ μ)
      + μ[fun t ↦ (Kernel.entropy (comap η (Prod.mk t) measurable_prodMk_left) ((κ t)))] := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  let A := μ.pfrSupport
  have hsum (F : T → ℝ) : ∫ (t : T), F t ∂μ = ∑ t ∈ A, (μ.real {t}) * (F t) := by
    rw [integral_eq_setIntegral (ae_mem_support μ), setIntegral_finset _ .finset]
    congr with t ht
  simp_rw [entropy, hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← mul_add]
  congr
  obtain ⟨B, hB⟩ := local_support_of_finiteKernelSupport hκ A
  obtain ⟨C, hC⟩ := local_support_of_finiteKernelSupport hη (A ×ˢ B)
  rw [integral_eq_setIntegral (hB t ht)]
  have hκη : ((κ ⊗ₖ η) t) (B ×ˢ C : Finset (S × U))ᶜ = 0 := by
    rw [Kernel.compProd_apply (Finset.measurableSet _).compl,
      lintegral_eq_setLIntegral (ae_iff.1 <| hB t ht), setLIntegral_eq_sum]
    apply Finset.sum_eq_zero
    intro s hs
    simpa using .inr <| measure_mono_null (by simp [*]) (hC (t, s) <| by simp [ht, hs])
  rw [measureEntropy_eq_sum hκη, measureEntropy_eq_sum (hB t ht),
    setIntegral_finset _ .finset,
    ← Finset.sum_add_distrib, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [measure_univ, inv_one, one_smul, coe_comap, Function.comp_apply, smul_eq_mul]
  have hts : (t, s) ∈ A ×ˢ B := by simp [ht, hs]
  rw [measureEntropy_eq_sum (hC (t, s) hts)]
  simp only [measure_univ, inv_one, one_smul]
  have : negMulLog ((κ t).real {s}) = ∑ u ∈ C, negMulLog ((κ t).real {s}) *
      ((comap η (Prod.mk t) measurable_prodMk_left) s).real {u} := by
    rw [← Finset.mul_sum]
    simp only [coe_comap, Function.comp_apply, sum_measureReal_singleton]
    suffices (η (t, s)).real ↑C = (η (t, s)).real Set.univ by simp [this]
    have := hC (t, s) hts
    rw [ae_iff, ← measureReal_eq_zero_iff] at this
    change (η (t, s)).real Cᶜ = 0 at this
    rw [← measureReal_add_measureReal_compl (s := C) _, this, add_zero]
    exact Finset.measurableSet C
  rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr with u
  have : ((κ ⊗ₖ η) t).real {(s, u)} = (κ t).real {s} * (η (t, s)).real {u} := by
    rw [measureReal_def, compProd_apply (.singleton _),
      lintegral_eq_setLIntegral (ae_iff.1 <| hB t ht), setLIntegral_eq_sum,
      Finset.sum_eq_single_of_mem s hs]
    · simp [measureReal_def, Set.preimage]
    intro b _ hbs
    simp [hbs, Set.preimage]
  rw [this, Kernel.comap_apply, negMulLog_mul, negMulLog, negMulLog]
  ring

lemma entropy_compProd' [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass T]
    [Countable T] [MeasurableSingletonClass U] {μ}
    [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    (Kernel.entropy (κ ⊗ₖ η) μ) = (Kernel.entropy κ μ) + (Kernel.entropy η (μ ⊗ₘ κ)) := by
  rw [entropy_compProd_aux hκ hη]
  congr
  rw [entropy, Measure.integral_compProd]
  · simp_rw [entropy]
    congr
  · have := finiteSupport_of_compProd' hκ (μ := μ)
    exact integrable_of_finiteSupport (μ ⊗ₘ κ)

lemma entropy_compProd [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] {μ}
    [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    (Kernel.entropy (κ ⊗ₖ η) μ) = (Kernel.entropy κ μ) + (Kernel.entropy η (μ ⊗ₘ κ)) := by
  have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
  have h_ent1 : (Kernel.entropy (hκ.mk ⊗ₖ hη.mk) μ) = (Kernel.entropy (κ ⊗ₖ η) μ) := by
    refine entropy_congr <| compProd_congr_ae hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm
  have h_ent2 : (Kernel.entropy hκ.mk μ) = (Kernel.entropy κ μ) := entropy_congr hκ.ae_eq_mk.symm
  have h_ent3 : (Kernel.entropy hη.mk (μ ⊗ₘ hκ.mk)) = (Kernel.entropy η (μ ⊗ₘ κ)) := by
    rw [h_meas_eq, entropy_congr hη.ae_eq_mk]
  rw [← h_ent1, ← h_ent2, ← h_ent3,
    entropy_compProd' hκ.finiteKernelSupport_mk hη.finiteKernelSupport_mk]

@[simp]
lemma entropy_deterministic [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] (f : T → S) (μ : Measure T) :
    (Kernel.entropy (deterministic f .of_discrete) μ) = 0 := by
  simp_rw [entropy]
  convert integral_zero T ℝ
  apply measureEntropy_dirac

@[simp]
lemma entropy_compProd_deterministic [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (κ : Kernel T S) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ] (f : T × S → U)
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (κ ⊗ₖ (deterministic f .of_discrete)) μ) = (Kernel.entropy κ μ) := by
  simp [entropy_compProd hκ ((FiniteKernelSupport.deterministic f).aefiniteKernelSupport _)]

lemma nonempty_of_isMarkovKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] [Nonempty α] : Nonempty β :=
  (κ <| Classical.arbitrary _).nonempty_of_neZero

lemma nonempty_of_isProbabilityMeasure_of_isMarkovKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] : Nonempty β := by
  have : Nonempty α := μ.nonempty_of_neZero
  exact nonempty_of_isMarkovKernel κ

lemma chain_rule [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ] [hU : Nonempty U]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy κ μ) = (Kernel.entropy (fst κ) μ) + (Kernel.entropy (condKernel κ) (μ ⊗ₘ (fst κ))) := by
  conv_lhs => rw [disintegration κ]
  rw [entropy_compProd hκ.fst (aefiniteKernelSupport_of_cond _ hκ)]

lemma chain_rule' [Nonempty S] [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy κ μ) = (Kernel.entropy (snd κ) μ) + (Kernel.entropy (condKernel (swapRight κ)) (μ ⊗ₘ (snd κ))) := by
  rw [← entropy_swapRight, chain_rule hκ.swapRight]
  simp

@[simp]
lemma entropy_prodMkRight [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T]
    {κ : Kernel T S} {η : Kernel T U}
    [IsMarkovKernel κ] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (prodMkRight S η) (μ ⊗ₘ κ)) = (Kernel.entropy η μ) := by
  have := finiteSupport_of_compProd hκ (μ := μ)
  simp [entropy, Measure.integral_compProd, integrable_of_finiteSupport]

lemma entropy_prodMkRight' [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T]
    {η : Kernel T U}
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] {ν : Measure S} [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.entropy (prodMkRight S η) (μ.prod ν)) = (Kernel.entropy η μ) := by
  rw [← entropy_prodMkRight (μ := μ) ((finiteKernelSupport_of_const ν).aefiniteKernelSupport _)]
  congr
  ext s hs
  simp_rw [Measure.prod_apply hs, Measure.compProd_apply hs, Kernel.const_apply]

@[simp]
lemma entropy_prodMkLeft [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] {η : Kernel T U}
    {ν : Measure S} [IsProbabilityMeasure ν] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.entropy (prodMkLeft S η) (ν.prod μ)) = (Kernel.entropy η μ) := by
  simp_rw [entropy, prodMkLeft_apply]
  rw [integral_prod]
  swap; · exact integrable_of_finiteSupport (ν.prod μ)
  simp

variable [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]

@[simp]
lemma entropy_prod {κ : Kernel T S} {η : Kernel T U} [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    (Kernel.entropy (κ ×ₖ η) μ) = (Kernel.entropy κ μ) + (Kernel.entropy η μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty U := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ η
  rw [chain_rule (hκ.prod hη), fst_prod,
    entropy_congr (condKernel_prod_ae_eq _ _), entropy_prodMkRight hκ]

lemma entropy_map_le
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    (f : S → U) [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (map κ f) μ) ≤ (Kernel.entropy κ μ) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  have : (Kernel.entropy κ μ) = (Kernel.entropy (map κ (fun x ↦ (x, f x))) μ) := by
    refine (entropy_map_of_injective κ μ (f := fun x ↦ (x, f x)) ?_ (by fun_prop)).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule' hκ.map]
  simp_rw [snd_map_prod κ measurable_id', le_add_iff_nonneg_right]
  exact entropy_nonneg _ _

lemma entropy_of_map_eq_of_map {κ : Kernel T S} {η : Kernel T U}
    [IsZeroOrMarkovKernel κ] [IsZeroOrMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] (f : S → U) (g : U → S)
    (h1 : η = map κ f) (h2 : κ = map η g)
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    (Kernel.entropy κ μ) = (Kernel.entropy η μ) := by
  refine le_antisymm ?_ ?_
  · rw [h2]; exact entropy_map_le g hη
  · rw [h1]; exact entropy_map_le f hκ

end ProbabilityTheory.Kernel
end

/- PFR.ForMathlib.Entropy.Kernel.MutualInfo -/
noncomputable section
open scoped ProbabilityTheory
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}

noncomputable
def mutualInfo (κ : Kernel T (S × U)) (μ : Measure T) : ℝ :=
  (Kernel.entropy (fst κ) μ) + (Kernel.entropy (snd κ) μ) - (Kernel.entropy κ μ)

lemma mutualInfo_def (κ : Kernel T (S × U)) (μ : Measure T) :
    (Kernel.mutualInfo κ μ) = (Kernel.entropy (fst κ) μ) + (Kernel.entropy (snd κ) μ) - (Kernel.entropy κ μ) := rfl

@[simp]
lemma mutualInfo_zero_measure (κ : Kernel T (S × U)) : (Kernel.mutualInfo κ ((0 : Measure T))) = 0 := by
  simp [mutualInfo]

@[simp]
lemma mutualInfo_zero_kernel (μ : Measure T) : (Kernel.mutualInfo ((0 : Kernel T (S × U))) μ) = 0 := by
  simp [mutualInfo]

lemma mutualInfo_congr {κ η : Kernel T (S × U)} {μ : Measure T} (h : κ =ᵐ[μ] η) :
    (Kernel.mutualInfo κ μ) = (Kernel.mutualInfo η μ) := by
  rw [mutualInfo, mutualInfo]
  have h1 : fst κ =ᵐ[μ] fst η := by
    filter_upwards [h] with t ht
    rw [fst_apply, ht, fst_apply]
  have h2 : snd κ =ᵐ[μ] snd η := by
    filter_upwards [h] with t ht
    rw [snd_apply, ht, snd_apply]
  rw [entropy_congr h1, entropy_congr h2, entropy_congr h]

lemma compProd_assoc' (ξ : Kernel T S) [IsSFiniteKernel ξ]
    (κ : Kernel (T × S) U) [IsSFiniteKernel κ] (η : Kernel (T × S × U) V) [IsSFiniteKernel η] :
    map ((ξ ⊗ₖ κ) ⊗ₖ η) MeasurableEquiv.prodAssoc
      = ξ ⊗ₖ (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)) := by
  ext x s hs
  rw [map_apply' _ (by fun_prop) _ hs,
    compProd_apply (MeasurableEquiv.prodAssoc.measurable hs),
    compProd_apply hs, lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' (MeasurableEquiv.prodAssoc.measurable hs) _
  congr with a
  rw [compProd_apply]
  swap; · exact measurable_prodMk_left hs
  congr

lemma Measure.compProd_compProd (μ : Measure T)
    (ξ : Kernel T S) [IsSFiniteKernel ξ] (κ : Kernel (T × S) U) [IsSFiniteKernel κ] :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).map MeasurableEquiv.prodAssoc := by
  by_cases hμ : SFinite μ; swap
  · simp [Measure.compProd_of_not_sfinite _ _ hμ]
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply MeasurableEquiv.prodAssoc.measurable hs,
    Measure.compProd_apply (MeasurableEquiv.prodAssoc.measurable hs),
    Measure.lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left (MeasurableEquiv.prodAssoc.measurable hs)
  congr with a
  rw [compProd_apply (measurable_prodMk_left hs)]
  congr

lemma Measure.compProd_compProd'' (μ : Measure T)
    (ξ : Kernel T S) [IsSFiniteKernel ξ] (κ : Kernel (T × S) U) [IsSFiniteKernel κ] :
    μ ⊗ₘ ξ ⊗ₘ κ = Measure.comap MeasurableEquiv.prodAssoc (μ ⊗ₘ (ξ ⊗ₖ κ)) := by
  rw [Measure.compProd_compProd, ← MeasurableEquiv.map_symm, Measure.map_map]
  · simp
  · exact MeasurableEquiv.prodAssoc.symm.measurable
  · exact MeasurableEquiv.prodAssoc.measurable

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]

@[simp]
lemma mutualInfo_swapRight
    (κ : Kernel T (S × U)) (μ : Measure T) :
    (Kernel.mutualInfo (swapRight κ) μ) = (Kernel.mutualInfo κ μ) := by
  rw [mutualInfo, fst_swapRight, snd_swapRight, entropy_swapRight, add_comm]
  rfl

variable [MeasurableSingletonClass T]

lemma mutualInfo_nonneg' {κ : Kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    0 ≤ (Kernel.mutualInfo κ μ) := by
  simp_rw [mutualInfo, entropy, integral_eq_setIntegral (ae_mem_support μ),
    setIntegral_finset _ .finset, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp_rw [← mul_add, ← mul_sub, fst_apply, snd_apply]
  have (x : T) : FiniteSupport (κ x) := ⟨hκ x⟩
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg measureMutualInfo_nonneg

lemma mutualInfo_nonneg [Countable T] {κ : Kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    0 ≤ (Kernel.mutualInfo κ μ) := by
  rw [mutualInfo_congr hκ.ae_eq_mk]
  exact mutualInfo_nonneg' hκ.finiteKernelSupport_mk

variable [Countable S] [Countable T]

variable [Countable U]

lemma mutualInfo_eq_fst_sub [Nonempty S] {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.mutualInfo κ μ) = (Kernel.entropy (fst κ) μ) - (Kernel.entropy (condKernel (swapRight κ)) (μ ⊗ₘ (snd κ))) := by
  rw [mutualInfo, chain_rule' hκ]
  ring

@[simp]
lemma mutualInfo_prod {κ : Kernel T S} {η : Kernel T U}
    [IsZeroOrMarkovKernel κ] [IsZeroOrMarkovKernel η]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    (Kernel.mutualInfo (κ ×ₖ η) μ) = 0 := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isMarkovKernel η with rfl | hη'
  · simp
  rw [mutualInfo, snd_prod, fst_prod, entropy_prod hκ hη, sub_self]

lemma mutualInfo_eq_snd_sub [Nonempty U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.mutualInfo κ μ) = (Kernel.entropy (snd κ) μ) - (Kernel.entropy (condKernel κ) (μ ⊗ₘ (fst κ))) := by
  rw [mutualInfo, chain_rule hκ]
  ring

lemma entropy_condKernel_le_entropy_snd [Nonempty U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (condKernel κ) (μ ⊗ₘ (fst κ))) ≤ (Kernel.entropy (snd κ) μ) := by
  rw [← sub_nonneg, ← mutualInfo_eq_snd_sub hκ]
  exact mutualInfo_nonneg hκ

lemma entropy_snd_sub_mutualInfo_le_entropy_map_of_injective {V : Type*} [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    (f : S × U → V) (hfi : ∀ x, Injective (fun y ↦ f (x, y))) [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (snd κ) μ) - (Kernel.mutualInfo κ μ) ≤ (Kernel.entropy (map κ f) μ) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ'
  · simp
  have : Nonempty (S × U) := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  inhabit (S × U)
  have : Nonempty U := ⟨(default : S × U).2⟩
  have : Nonempty V := ⟨f default⟩
  rw [mutualInfo_eq_snd_sub hκ]
  have hf : Measurable f := by fun_prop
  ring_nf
  calc
    (Kernel.entropy (condKernel κ) (μ ⊗ₘ fst κ)) = (Kernel.entropy (snd ((condKernel κ) ⊗ₖ
        (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2))
        .of_discrete))) (μ ⊗ₘ fst κ)) := by
      symm
      apply entropy_snd_compProd_deterministic_of_injective _ _ (fun t ↦ hfi t.2)
    _ = (Kernel.entropy (condKernel (map κ (fun p ↦ (p.1, f p)))) (μ ⊗ₘ fst κ))
 := entropy_congr (condKernel_map_prodMk_left κ μ f).symm
    _ = (Kernel.entropy (condKernel (map κ (fun p ↦ (p.1, f p)))) (μ ⊗ₘ fst (map κ (fun p ↦ (p.1, f p)))))
 := by
        congr 2 with x
        rw [fst_map_prod _ hf, fst_apply, map_apply _ measurable_fst]
    _ ≤ (Kernel.entropy (snd (map κ (fun p ↦ (p.1, f p)))) μ) :=
      entropy_condKernel_le_entropy_snd hκ.map
    _ = (Kernel.entropy (map κ f) μ) := by rw [snd_map_prod _ measurable_fst]

end

section

variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]

lemma entropy_reverse {κ : Kernel T (S × U × V)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (reverse κ) μ) = (Kernel.entropy κ μ) := by
  refine le_antisymm ?_ ?_
  · simpa [reverse_eq] using entropy_map_le (fun p ↦ (p.2.2, p.2.1, p.1)) hκ
  · conv_lhs => rw [← reverse_reverse κ]
    simpa [reverse_eq] using entropy_map_le (fun p ↦ (p.2.2, p.2.1, p.1)) hκ.reverse

instance IsZeroOrProbabilityMeasure.compProd
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) [IsZeroOrProbabilityMeasure μ] (κ : Kernel α β)
    [IsZeroOrMarkovKernel κ] : IsZeroOrProbabilityMeasure (μ ⊗ₘ κ) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ
  · simp only [Measure.compProd_zero_right]; infer_instance
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp only [Measure.compProd_zero_left]; infer_instance
  infer_instance

lemma entropy_condKernel_compProd_triple [Nonempty V] (ξ : Kernel T S) [IsZeroOrMarkovKernel ξ]
    (κ : Kernel (T × S) U) [IsMarkovKernel κ] (η : Kernel (T × S × U) V) [IsMarkovKernel η]
    (μ : Measure T) :
    (Kernel.entropy (condKernel (ξ ⊗ₖ κ ⊗ₖ η)) (μ ⊗ₘ (ξ ⊗ₖ κ))) = (Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ))) :=
  entropy_congr (condKernel_compProd_ae_eq (ξ ⊗ₖ κ) η μ)

lemma entropy_submodular_compProd {ξ : Kernel T S} [IsZeroOrMarkovKernel ξ]
    {κ : Kernel (T × S) U} [IsZeroOrMarkovKernel κ] {η : Kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ : AEFiniteKernelSupport ξ μ) :
    (Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ)))
      ≤ (Kernel.entropy (snd (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable))) (μ ⊗ₘ ξ))
 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isMarkovKernel ξ with rfl | hξ'
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ ξ
  have : Nonempty T := μ.nonempty_of_neZero
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  have : Nonempty U := nonempty_of_isMarkovKernel κ
  rcases eq_zero_or_isMarkovKernel η with rfl | hκ'
  · simp
  have : Nonempty V := nonempty_of_isMarkovKernel η
  have h_meas := (MeasurableEquiv.prodAssoc : (T × S) × U ≃ᵐ T × S × U).measurable
  have : FiniteSupport (μ ⊗ₘ ξ) := finiteSupport_of_compProd hξ
  have : FiniteSupport (μ ⊗ₘ (ξ ⊗ₖ κ)) := finiteSupport_of_compProd (hξ.compProd hκ)
  have h := entropy_condKernel_le_entropy_snd
    (κ := κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc h_meas)) (μ := μ ⊗ₘ ξ) ?_
  · simp only [fst_compProd] at h
    have : condKernel (κ ⊗ₖ comap η ↑MeasurableEquiv.prodAssoc h_meas)
        =ᵐ[μ ⊗ₘ ξ ⊗ₘ κ] comap η ↑MeasurableEquiv.prodAssoc h_meas := by
      exact condKernel_compProd_ae_eq κ (comap η _ MeasurableEquiv.prodAssoc.measurable) (μ ⊗ₘ ξ)
    rwa [entropy_congr this, Measure.compProd_compProd'', entropy_comap_equiv] at h
  · refine (hκ.compProd ?_)
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact Measure.compProd_compProd'' _ _ _

lemma entropy_compProd_triple_add_entropy_le {ξ : Kernel T S} [IsZeroOrMarkovKernel ξ]
    {κ : Kernel (T × S) U} [IsMarkovKernel κ]
    {η : Kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ : AEFiniteKernelSupport ξ μ) :
    (Kernel.entropy ((ξ ⊗ₖ κ) ⊗ₖ η) μ) + (Kernel.entropy ξ μ)
      ≤ (Kernel.entropy (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)) μ)
 + (Kernel.entropy (ξ ⊗ₖ κ) μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isMarkovKernel ξ with rfl | hξ'
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ ξ
  have : Nonempty T := μ.nonempty_of_neZero
  have : Nonempty U := nonempty_of_isMarkovKernel κ
  have : Nonempty V := nonempty_of_isMarkovKernel η
  rw [chain_rule, chain_rule (κ := ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc
    MeasurableEquiv.prodAssoc.measurable))]
  · simp only [fst_compProd, entropy_condKernel_compProd_triple]
    calc (Kernel.entropy (ξ ⊗ₖ κ) μ) + (Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ))) + (Kernel.entropy ξ μ)
      = (Kernel.entropy ξ μ) + (Kernel.entropy (ξ ⊗ₖ κ) μ) + (Kernel.entropy η (μ ⊗ₘ (ξ ⊗ₖ κ))) := by abel
    _ ≤ (Kernel.entropy ξ μ) + (Kernel.entropy (ξ ⊗ₖ κ) μ)
      + (Kernel.entropy (condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _))) (μ ⊗ₘ ξ)) := by
        refine add_le_add le_rfl ?_
        refine (entropy_submodular_compProd hκ hη hξ).trans_eq ?_
        refine entropy_congr ?_
        exact (condKernel_compProd_ae_eq _ _ _).symm
    _ = (Kernel.entropy ξ μ) + (Kernel.entropy (condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _))) (μ ⊗ₘ ξ)) +
          (Kernel.entropy (ξ ⊗ₖ κ) μ) := by abel
  · refine hξ.compProd ?_
    refine AEFiniteKernelSupport.snd ?_
    refine hκ.compProd ?_
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact Measure.compProd_compProd'' _ _ _
  · exact (hξ.compProd hκ).compProd hη

lemma entropy_triple_add_entropy_le' {κ : Kernel T (S × U × V)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy κ μ) + (Kernel.entropy (fst κ) μ) ≤ (Kernel.entropy (deleteMiddle κ) μ) + (Kernel.entropy (deleteRight κ) μ) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty (S × U × V) := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  inhabit (S × U × V)
  have : Nonempty U := ⟨(default : S × U × V).2.1⟩
  have : Nonempty V := ⟨(default : S × U × V).2.2⟩
  set κ' := map κ MeasurableEquiv.prodAssoc.symm with hκ'_def
  set ξ := fst (fst κ') with ξ_def
  let κ'' := condKernel (fst κ')
  let η := condKernel κ'
  have hξ_eq : ξ = fst κ := by
    rw [ξ_def, hκ'_def, fst_eq, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
     fst_eq, map_map _ (by fun_prop) (by fun_prop), map_map _ (by fun_prop) (by fun_prop), fst_eq]
    rfl
  have h_compProd_eq : ξ ⊗ₖ κ'' = fst κ' := (disintegration (fst κ')).symm
  have h_compProd_triple_eq : (ξ ⊗ₖ κ'') ⊗ₖ η = κ' := by
    rw [h_compProd_eq]
    exact (disintegration κ').symm
  have h_compProd_triple_eq' :
      ξ ⊗ₖ (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable)
        = κ := by
    rw [← compProd_assoc', h_compProd_triple_eq,hκ'_def, map_map _ (by fun_prop) (by fun_prop)]
    simp
  have h := entropy_compProd_triple_add_entropy_le (ξ := ξ) (κ := κ'') (η := η) (μ := μ) ?_ ?_ ?_
  rotate_left
  · exact aefiniteKernelSupport_of_cond _ hκ.map.fst
  · rw [h_compProd_eq]
    apply aefiniteKernelSupport_of_cond
    exact hκ.map
  · exact hκ.map.fst.fst
  rw [← hξ_eq]
  have h_right : deleteRight κ = fst κ' := by
    rw [hκ'_def, deleteRight_eq, fst_eq, map_map _ (by fun_prop) (by fun_prop)]
    congr
  have h_middle : deleteMiddle κ
      = ξ ⊗ₖ snd
        (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable) := by
    rw [← deleteMiddle_compProd, h_compProd_triple_eq']
  have hκ : (Kernel.entropy κ μ) = (Kernel.entropy κ' μ) := by
    rw [hκ'_def, entropy_map_of_injective _ _ _ (by fun_prop)]
    exact MeasurableEquiv.prodAssoc.symm.injective
  rw [h_right, h_middle, hκ, ← h_compProd_triple_eq, fst_compProd]
  · exact h

lemma entropy_triple_add_entropy_le (κ : Kernel T (S × U × V)) [IsZeroOrMarkovKernel κ]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy κ μ) + (Kernel.entropy (snd (snd κ)) μ) ≤ (Kernel.entropy (deleteMiddle κ) μ) + (Kernel.entropy (snd κ) μ) := by
  have h2 : fst (reverse κ) = snd (snd κ) := by
    rw [fst_eq, reverse_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop), snd_eq,
      map_map _ (by fun_prop) (by fun_prop)]
    congr
  rw [← entropy_reverse hκ, ← h2]
  refine (entropy_triple_add_entropy_le' (κ := reverse κ) (μ:= μ) hκ.reverse).trans ?_
  refine add_le_add ?_ ?_
  · rw [← entropy_swapRight]
    simp
  · rw [← entropy_swapRight]
    simp

end

end ProbabilityTheory.Kernel
end

/- PFR.ForMathlib.Uniform -/
noncomputable section
open scoped ProbabilityTheory
open Function MeasureTheory Measure Set
open scoped ENNReal

namespace ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}

structure IsUniform (H : Set S) (X : Ω → S) (μ : Measure Ω := by volume_tac) : Prop where
  eq_of_mem ⦃x⦄ (hx : x ∈ H) ⦃y⦄ (hy : y ∈ H) : μ (X ⁻¹' {x}) = μ (X ⁻¹' {y})
  measure_preimage_compl : μ (X ⁻¹' Hᶜ) = 0

lemma isUniform_uniformOn [MeasurableSingletonClass Ω] {A : Set Ω} :
    IsUniform A id (uniformOn A) := by
  constructor
  · intro x hx y hy
    have h'x : {x} ∩ A = {x} := by ext y; simp (config := {contextual := true}) [hx]
    have h'y : {y} ∩ A = {y} := by ext y; simp (config := {contextual := true}) [hy]
    simp [uniformOn, cond, h'x, h'y]
  · exact uniformOn_apply_eq_zero (by simp)

lemma exists_isUniform [MeasurableSpace S] [MeasurableSingletonClass S]
    (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (_ : MeasurableSpace Ω) (X : Ω → S) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧ Measurable X ∧ IsUniform H X μ ∧ (∀ ω, X ω ∈ H) ∧ FiniteRange X := by
  refine ⟨H, Subtype.instMeasurableSpace, fun x ↦ x, (Finset.card H : ℝ≥0∞)⁻¹ • ∑ i, .dirac i, ?_,
    measurable_subtype_coe, ⟨?_, ?_⟩, fun x ↦ x.2, ?_⟩
  · constructor
    simp only [Finset.univ_eq_attach, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      measure_univ, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one, smul_eq_mul]
    rw [ENNReal.inv_mul_cancel]
    · simpa using h.ne_empty
    · simp
  · intro x hx y hy
    simp only [Finset.univ_eq_attach, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, Measure.dirac_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ⟨x, hx⟩, Finset.sum_eq_single ⟨y, hy⟩]
    · simp
    · rintro ⟨b, bH⟩ _hb h'b
      simp only [ne_eq, Subtype.mk.injEq] at h'b
      simp [h'b]
    · simp
    · rintro ⟨b, bH⟩ _hb h'b
      simp only [ne_eq, Subtype.mk.injEq] at h'b
      simp [h'b]
    · simp
  · simp
  · apply finiteRange_of_finset _ H _
    simp

lemma IsUniform.comp [DecidableEq T] {H : Finset S} (h : IsUniform H X μ) {f : S → T}
    (hf : Injective f) : IsUniform (Finset.image f H) (f ∘ X) μ where
  eq_of_mem := by
    intro x hx y hy
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hx hy
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    have A z : f ⁻¹' {f z} = {z} := by ext; simp [hf.eq_iff]
    simp [preimage_comp, A, h.eq_of_mem hx hy]
  measure_preimage_compl := by simpa [preimage_comp, hf] using h.measure_preimage_compl

lemma exists_isUniform_measureSpace {S : Type uS} [MeasurableSpace S]
    [MeasurableSingletonClass S] (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧ (∀ ω : Ω, U ω ∈ H) ∧
      FiniteRange U := by
  rcases exists_isUniform H h with ⟨Ω, mΩ, X, μ, hμ, Xmeas, Xunif, Xmem, Xfin⟩
  exact ⟨Ω, ⟨μ⟩, X, hμ, Xmeas, Xunif, Xmem, Xfin⟩

lemma IsUniform.ae_mem (h : IsUniform H X μ) : ∀ᵐ ω ∂μ, X ω ∈ H := h.measure_preimage_compl

lemma IsUniform.measure_preimage_of_nmem (h : IsUniform H X μ) {s : S} (hs : s ∉ H) :
    μ (X ⁻¹' {s}) = 0 := by
  apply le_antisymm ((measure_mono _).trans h.measure_preimage_compl.le) zero_le
  apply preimage_mono
  simpa using hs

lemma IsUniform.measureReal_preimage_of_nmem (h : IsUniform H X μ) {s : S} (hs : s ∉ H) :
    μ.real (X ⁻¹' {s}) = 0 := by
  rw [measureReal_def, h.measure_preimage_of_nmem hs, ENNReal.toReal_zero]

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

lemma IsUniform.measure_preimage_of_mem
    {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    {s : S} (hs : s ∈ H) :
    μ (X ⁻¹' {s}) = μ univ / Nat.card H := by
  have B : μ univ = (Nat.card H) * μ (X ⁻¹' {s}) := calc
    μ univ = μ (X ⁻¹' Hᶜ) + μ (X ⁻¹' H) := by
      rw [← measure_union (disjoint_compl_left.preimage _) (hX .of_discrete)]
      simp
    _ = μ (X ⁻¹' H) := by rw [h.measure_preimage_compl, zero_add]
    _ = ∑ x ∈ H, μ (X ⁻¹' {x}) := by
      have : X ⁻¹' H = ⋃ x ∈ H, X ⁻¹' ({x} : Set S) := by simp
      rw [this, measure_biUnion_finset]
      · intro y _hy z _hz hyz
        apply Disjoint.preimage
        simp [hyz]
      · intro y _hy
        exact hX .of_discrete
    _ = ∑ _x ∈ H, μ (X ⁻¹' {s}) :=
      Finset.sum_congr rfl fun x hx ↦ h.eq_of_mem (by simpa using hx) hs
    _ = H.card * μ (X ⁻¹' {s}) := by simp
    _ = (Nat.card H) * μ (X ⁻¹' {s}) := by
      congr; simp
  rcases Nat.eq_zero_or_pos (Nat.card H) with hH|hH
  · simp only [hH, CharP.cast_eq_zero, zero_mul, Measure.measure_univ_eq_zero] at B
    simp [B]
  · rwa [eq_comm, ← ENNReal.eq_div_iff] at B
    · simpa using Nat.pos_iff_ne_zero.mp hH
    · simp

lemma IsUniform.measureReal_preimage_of_mem {A : Finset S} [IsProbabilityMeasure μ]
    (h : IsUniform A X μ) (hX : Measurable X) {s : S} (hs : s ∈ A) :
    μ.real (X ⁻¹' {s}) = 1 / A.card := by
  simp [measureReal_def, h.measure_preimage_of_mem hX hs]

lemma IsUniform.measureReal_preimage_of_mem' {A : Finset S} [IsProbabilityMeasure μ]
    (h : IsUniform A X μ) (hX : Measurable X) {s : S} (hs : s ∈ A) :
    (μ.map X).real {s} = 1 / A.card := by
  rw [map_measureReal_apply hX (MeasurableSet.singleton s), h.measureReal_preimage_of_mem hX hs]

lemma IsUniform.measure_preimage {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    (H' : Set S) : μ (X ⁻¹' H') = (μ univ) * (Nat.card (H' ∩ H : Set S)) / Nat.card H := calc
  _ = μ (X ⁻¹' (H' ∩ H) ∪ X ⁻¹' (H' \ H)) := by simp
  _ = μ (X ⁻¹' (H' ∩ H)) + μ (X ⁻¹' (H' \ H)) :=
    measure_union (Disjoint.preimage X disjoint_inf_sdiff) (by measurability)
  _ = μ (X ⁻¹' (H' ∩ H).toFinite.toFinset) := by
    simp [Set.sdiff_eq_compl_inter, measure_mono_null inter_subset_left h.measure_preimage_compl,
      -preimage_compl]
  _ = μ univ * ∑ __ ∈ (H' ∩ H).toFinite.toFinset, (1 : ENNReal) / Nat.card H := by
    rewrite [← sum_measure_preimage_singleton _ (by measurability), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ hx ↦ ?_)
    rw [mul_one_div, h.measure_preimage_of_mem hX ((Finite.mem_toFinset _).mp hx).2]
  _ = (μ univ) * (Nat.card (H' ∩ H).Elem) / Nat.card H := by
    rw [Finset.sum_const, Nat.card_eq_card_finite_toFinset, nsmul_eq_mul, ← mul_assoc, mul_one_div]

lemma IsUniform.full_measure (h : IsUniform H X μ) (hX : Measurable X) :
    (μ.map X) H = μ Set.univ := by
    rw [Measure.map_apply hX (by measurability)]
    refine measure_eq_measure_of_null_sdiff (subset_univ _) ?h_nulldiff
    convert h.measure_preimage_compl
    ext ω; simp

lemma IsUniform.of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] (h : IsUniform H X μ)
    {X' : Ω' → S} {μ' : Measure Ω'} (h' : IdentDistrib X X' μ μ') (hH : MeasurableSet (H : Set S)) :
    IsUniform H X' μ' := by
  constructor
  · intro x hx y hy
    rw [← h'.measure_mem_eq (MeasurableSet.singleton x),
      ← h'.measure_mem_eq (MeasurableSet.singleton y)]
    apply h.eq_of_mem hx hy
  · rw [← h'.measure_mem_eq hH.compl]
    exact h.measure_preimage_compl

lemma IsUniform.restrict {H : Set S} (h : IsUniform H X μ) (hX : Measurable X) (H' : Set S) :
    IsUniform (H' ∩ H) X (μ[|X ⁻¹' H']) where
  eq_of_mem := fun x hx y hy ↦ by
    simp only [cond, Measure.smul_apply, smul_eq_mul]
    rw [μ.restrict_eq_self (preimage_mono (singleton_subset_iff.mpr hx.1)),
      μ.restrict_eq_self (preimage_mono (singleton_subset_iff.mpr hy.1)), h.eq_of_mem hx.2 hy.2]
  measure_preimage_compl := by
    rewrite [← nonpos_iff_eq_zero, Set.compl_inter, Set.preimage_union]
    calc
      _ ≤ (μ[|X ⁻¹' H']) (X ⁻¹' H'ᶜ) + (μ[|X ⁻¹' H']) (X ⁻¹' Hᶜ) := measure_union_le _ _
      _ = (μ[|X ⁻¹' H']) (X ⁻¹' H'ᶜ) + 0 := congrArg _ <| by
        simp only [cond, Measure.smul_apply, smul_eq_mul]
        convert mul_zero _
        exact eq_bot_mono (Measure.restrict_apply_le _ _) h.measure_preimage_compl
      _ = 0 := by
        simp only [cond, Measure.smul_apply, smul_eq_mul]
        rw [add_zero, Set.preimage_compl, Measure.restrict_apply <|
          MeasurableSet.compl (measurableSet_preimage hX .of_discrete),
          compl_inter_self, measure_empty, mul_zero]

lemma IdentDistrib.of_isUniform {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Finite H] [Countable S]
    {X : Ω → S} {X' : Ω' → S}
    (hX : Measurable X) (hX' : Measurable X') (hX_unif : IsUniform H X μ)
    (hX'_unif : IsUniform H X' μ') : IdentDistrib X X' μ μ' := by
  refine ⟨hX.aemeasurable, hX'.aemeasurable, ?_⟩
  ext E hE
  rw [← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hE,
    ← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hE]
  congr! 4 with _ x
  rw [Measure.map_apply hX (.singleton x), Measure.map_apply hX' (.singleton x)]
  set Hf := H.toFinite.toFinset
  have hX_unif' : IsUniform Hf X μ := by convert hX_unif; simp [Hf]
  have hX'_unif' : IsUniform Hf X' μ' := by convert hX'_unif; simp [Hf]
  by_cases h : x ∈ Hf
  · rw [IsUniform.measure_preimage_of_mem hX_unif' hX h,
      IsUniform.measure_preimage_of_mem hX'_unif' hX' h]
    simp
  · rw [IsUniform.measure_preimage_of_nmem hX_unif' h,
      IsUniform.measure_preimage_of_nmem hX'_unif' h]

end ProbabilityTheory
end

/- PFR.Mathlib.Probability.ConditionalProbability -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

lemma cond_real_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp [Measure.real, cond_apply hms]

theorem cond_isProbabilityMeasure_of_real {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by
  apply cond_isProbabilityMeasure_of_finite
  · intro h
    simp [measureReal_def, h] at hcs
  · intro h
    simp [measureReal_def, h] at hcs

end ProbabilityTheory
end

/- PFR.ForMathlib.Entropy.Basic -/
noncomputable section
open scoped ProbabilityTheory
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

section entropy

noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := (ProbabilityTheory.measureEntropy (μ.map X))

lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = (ProbabilityTheory.measureEntropy (μ.map X)) := rfl

lemma entropy_eq_kernel_entropy (X : Ω → S) (μ : Measure Ω) :
    (ProbabilityTheory.entropy X μ) = (Kernel.entropy (Kernel.const Unit (μ.map X)) (Measure.dirac ())) := by simp [entropy]

@[simp]
lemma entropy_zero_measure (X : Ω → S) : (ProbabilityTheory.entropy X ((0 : Measure Ω))) = 0 := by simp [entropy]

lemma entropy_congr {X X' : Ω → S} (h : X =ᵐ[μ] X') : (ProbabilityTheory.entropy X μ) = (ProbabilityTheory.entropy X' μ) := by
  rw [entropy_def, Measure.map_congr h, entropy_def]

lemma entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ entropy X μ := measureEntropy_nonneg _

lemma IdentDistrib.entropy_congr {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {X' : Ω' → S}
    (h : IdentDistrib X X' μ μ') : (ProbabilityTheory.entropy X μ) = (ProbabilityTheory.entropy X' μ') := by
  simp [entropy_def, h.map_eq]

lemma entropy_le_log_card [Fintype S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) : (ProbabilityTheory.entropy X μ) ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

lemma entropy_le_log_card_of_mem [DiscreteMeasurableSpace S]
    {A : Finset S} {μ : Measure Ω} {X : Ω → S}
    (hX : Measurable X) (h : ∀ᵐ ω ∂μ, X ω ∈ A) :
    (ProbabilityTheory.entropy X μ) ≤ log A.card :=
  measureEntropy_le_log_card_of_mem _ <| by rwa [Measure.map_apply hX .of_discrete]

lemma entropy_le_log_card_of_mem_finite [DiscreteMeasurableSpace S]
    {A : Set S} {μ : Measure Ω} {X : Ω → S}
    (hA : A.Finite) (hX : Measurable X) (h : ∀ᵐ ω ∂μ, X ω ∈ A) :
    (ProbabilityTheory.entropy X μ) ≤ log (Nat.card A) := by
  lift A to Finset S using hA
  simpa using entropy_le_log_card_of_mem (A := A) hX (μ := μ) (by simpa)

lemma entropy_eq_sum (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    entropy X μ = ∑' x, negMulLog ((μ.map X).real {x}) := by
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]

lemma entropy_eq_sum_finset {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {A : Finset S} (hA : (μ.map X) Aᶜ = 0) :
    entropy X μ = ∑ x ∈ A, negMulLog ((μ.map X).real {x}) := by
  rw [entropy_eq_sum]
  convert tsum_eq_sum ?_
  · exact SummationFilter.instLeAtTopUnconditional S
  intro s hs
  convert negMulLog_zero
  rw [Measure.real]
  convert ENNReal.toReal_zero
  convert measure_mono_null ?_ hA
  simp [hs]

lemma entropy_eq_sum_finset' {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {A : Finset S} (hA : (μ.map X) Aᶜ = 0) :
    entropy X μ = ∑ x ∈ A, negMulLog ((μ.map X).real {x}) :=
  entropy_eq_sum_finset hA

lemma entropy_eq_sum_finiteRange [MeasurableSingletonClass S]
    (hX : Measurable X) {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] [FiniteRange X] :
    entropy X μ = ∑ x ∈ FiniteRange.toFinset X, negMulLog ((μ.map X).real {x}) :=
  entropy_eq_sum_finset (A := FiniteRange.toFinset X) (full_measure_of_finiteRange hX)

lemma entropy_cond_eq_sum (μ : Measure Ω) (y : T) :
    (ProbabilityTheory.entropy X (μ[|Y ← y])) = ∑' x, negMulLog (((μ[|Y ← y]).map X).real {x}) := by
  by_cases hy : μ (Y ⁻¹' {y}) = 0
  · rw [entropy_def, cond_eq_zero_of_meas_eq_zero hy]
    simp
  · rw [entropy_eq_sum]

lemma entropy_cond_eq_sum_finiteRange [MeasurableSingletonClass S]
    (hX : Measurable X) (μ : Measure Ω) (y : T) [FiniteRange X] :
    (ProbabilityTheory.entropy X (μ[|Y ← y])) = ∑ x ∈ FiniteRange.toFinset X, negMulLog (((μ[|Y ← y]).map X).real {x}) := by
  by_cases hy : μ (Y ⁻¹' {y}) = 0
  · rw [entropy_def, cond_eq_zero_of_meas_eq_zero hy]
    simp
  · rw [entropy_eq_sum_finiteRange hX]

lemma entropy_comp_of_injective [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    (ProbabilityTheory.entropy (f ∘ X) μ) = (ProbabilityTheory.entropy X μ) := by
  have hf_m : Measurable f := .of_discrete
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf_m hf,
    entropy_def]

@[simp] lemma entropy_const [MeasurableSingletonClass S] [IsZeroOrProbabilityMeasure μ] (c : S) :
    (ProbabilityTheory.entropy (fun _ ↦ c) μ) = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;>
  simp [entropy, Measure.map_const]

open Set

open Function

lemma IsUniform.entropy_eq [DiscreteMeasurableSpace S] {H : Finset S} {X : Ω → S} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsUniform H X μ) (hX' : Measurable X) :
    (ProbabilityTheory.entropy X μ) = log (Nat.card H) := by
  have (t : S) : negMulLog ((μ.map X).real {t}) = (μ.map X).real {t} * log (Nat.card H) := by
    by_cases ht : t ∈ H
    · simp [negMulLog, IsUniform.measureReal_preimage_of_mem' hX hX' ht]
    · simp [negMulLog, map_measureReal_apply hX' (.singleton t), hX.measureReal_preimage_of_nmem ht]
  rw [entropy_eq_sum_finset' (A := H), Finset.sum_congr rfl (fun t _ ↦ this t), ← Finset.sum_mul,
    sum_measureReal_singleton]
  · simp [Measure.real, IsUniform.full_measure hX hX']
  rw [Measure.map_apply hX' (by measurability)]
  exact hX.measure_preimage_compl

lemma IsUniform.entropy_eq' [DiscreteMeasurableSpace S]
    {A : Set S} (hA : A.Finite) {X : Ω → S} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : IsUniform A X μ) (hX' : Measurable X) : (ProbabilityTheory.entropy X μ) = log A.ncard := by
  have : IsUniform hA.toFinset X μ := by simpa using hX
  simpa using this.entropy_eq hX'

lemma prob_ge_exp_neg_entropy [MeasurableSingletonClass S] (X : Ω → S) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : Measurable X) [hX' : FiniteRange X] :
    ∃ s : S, μ Set.univ * (rexp (- (ProbabilityTheory.entropy X μ))).toNNReal ≤ μ.map X {s} := by
  have : Nonempty Ω := μ.nonempty_of_neZero
  have : Nonempty S := Nonempty.map X (by infer_instance)
  let μS := μ.map X
  let μs s := μS {s}
  rcases finiteSupport_of_finiteRange (X := X) with ⟨A, hA⟩
  let S_nonzero := A.filter (fun s ↦ μs s ≠ 0)
  set norm := μS A with rw_norm
  have h_norm : norm = μ Set.univ := by
    have := measure_add_measure_compl (μ := μS) (s := A) (Finset.measurableSet _)
    change μS (A : Set S)ᶜ = 0 at hA
    rw [hA, add_zero] at this
    simp [norm, μS, this, Measure.map_apply hX MeasurableSet.univ]
  let pdf_nn s := norm⁻¹ * μs s
  let pdf s := (pdf_nn s).toReal
  let neg_log_pdf s := -log (pdf s)
  rcases Finset.eq_empty_or_nonempty S_nonzero with h_empty | h_nonempty
  · have h_norm_zero : μ Set.univ = 0 := by
      have h : ∀ s ∈ A, μs s ≠ 0 → μs s ≠ 0 := fun _ _ h ↦ h
      rw [← h_norm, rw_norm, ← sum_measure_singleton, ← Finset.sum_filter_of_ne h,
        show Finset.filter _ _ = S_nonzero from rfl, h_empty, show Finset.sum ∅ μs = 0 from rfl]
    use Classical.arbitrary (α := S)
    simp [h_norm_zero]
  rcases exists_or_forall_not (fun s ↦ μ.map X {s} = ∞) with h_infty | h_finite
  · obtain ⟨s, h_s⟩ := h_infty
    use s; rw [h_s] ; exact le_top
  rcases eq_zero_or_neZero μ with h_zero_measure | _
  · use Classical.arbitrary (α := S)
    rw [h_zero_measure, show (0 : Measure Ω) _ = 0 from rfl, zero_mul]
    exact zero_le
  have h_norm_pos : 0 < norm := by
    rw [h_norm, Measure.measure_univ_pos]
    exact NeZero.ne μ
  have h_norm_finite : norm < ∞ := by
    rw [rw_norm, ← sum_measure_singleton]
    exact ENNReal.sum_lt_top.2 (fun s _ ↦ Ne.lt_top (h_finite s))
  have h_invinvnorm_finite : norm⁻¹⁻¹ ≠ ∞ := by
    rw [inv_inv]
    exact LT.lt.ne_top h_norm_finite
  have h_invnorm_ne_zero : norm⁻¹ ≠ 0 := ENNReal.inv_ne_top.mp h_invinvnorm_finite
  have h_invnorm_finite : norm⁻¹ ≠ ∞ := by
    rw [← ENNReal.inv_ne_zero, inv_inv]
    exact h_norm_pos.ne'
  have h_pdf_finite : ∀ s, pdf_nn s ≠ ∞ := fun s ↦ ENNReal.mul_ne_top h_invnorm_finite (h_finite s)
  have h_norm_cancel : norm * norm⁻¹ = 1 := ENNReal.mul_inv_cancel h_norm_pos.ne' h_norm_finite.ne
  have h_pdf1 : (∑ s ∈ A, pdf s) = 1 := by
    rw [← ENNReal.toReal_sum (fun s _ ↦ h_pdf_finite s), ← Finset.mul_sum,
      sum_measure_singleton, mul_comm, h_norm_cancel, ENNReal.toReal_one]
  let ⟨s_max, hs, h_min⟩ := Finset.exists_min_image S_nonzero neg_log_pdf h_nonempty
  have h_pdf_s_max_pos : 0 < pdf s_max := by
    rw [Finset.mem_filter] at hs
    have h_nonzero : pdf s_max ≠ 0 := ENNReal.toReal_ne_zero.mpr
      ⟨mul_ne_zero h_invnorm_ne_zero hs.2, ENNReal.mul_ne_top h_invnorm_finite (h_finite s_max)⟩
    exact LE.le.lt_of_ne ENNReal.toReal_nonneg h_nonzero.symm
  use s_max
  rw [← h_norm, ← one_mul (μ.map X _), ← h_norm_cancel, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt h_norm_pos)
  change ENNReal.ofReal (rexp (-(ProbabilityTheory.entropy X μ))) ≤ pdf_nn s_max
  rw [ENNReal.ofReal_le_iff_le_toReal (h_pdf_finite _),
    show (pdf_nn _).toReal = pdf _ from rfl, ← Real.exp_log h_pdf_s_max_pos]
  apply exp_monotone
  rw [neg_le, ← one_mul (-log _), ← h_pdf1, Finset.sum_mul]
  let g_lhs s := pdf s * neg_log_pdf s_max
  let g_rhs s := -pdf s * log (pdf s)
  suffices ∑ s ∈ A, g_lhs s ≤ ∑ s ∈ A, g_rhs s by
    convert! this
    rw [entropy_eq_sum_finset hA]
    congr with s
    simp only [negMulLog, neg_mul, ENNReal.toReal_mul, neg_inj, g_rhs, pdf, pdf_nn]
    simp at h_norm
    simp [h_norm, μs, μS, Measure.real]
  have h_lhs : ∀ s, μs s = 0 → g_lhs s = 0 := by {intros _ h; simp [g_lhs, pdf, pdf_nn, h]}
  have h_rhs : ∀ s, μs s = 0 → g_rhs s = 0 := by {intros _ h; simp [g_rhs, pdf, pdf_nn, h]}
  rw [← Finset.sum_filter_of_ne (fun s _ ↦ (h_lhs s).mt),
    ← Finset.sum_filter_of_ne (fun s _ ↦ (h_rhs s).mt)]
  apply Finset.sum_le_sum
  intros s h_s
  rw [show g_lhs s = _ * _ from rfl, show g_rhs s = _ * _ from rfl, neg_mul_comm]
  exact mul_le_mul_of_nonneg_left (h_min s h_s) ENNReal.toReal_nonneg

lemma prob_ge_exp_neg_entropy' [MeasurableSingletonClass S]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X) [FiniteRange X] :
    ∃ s : S, rexp (- (ProbabilityTheory.entropy X μ)) ≤ μ.real (X ⁻¹' {s}) := by
  obtain ⟨s, hs⟩ := prob_ge_exp_neg_entropy X μ hX
  use s
  rwa [IsProbabilityMeasure.measure_univ, one_mul,
    (show ENNReal.ofNNReal _ = ENNReal.ofReal _ from rfl),
    ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), ← Measure.real,
    map_measureReal_apply hX (MeasurableSet.singleton s)] at hs

variable [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]

@[simp] lemma entropy_prod_comp (hX : Measurable X) (μ : Measure Ω) (f : S → T) :
    (ProbabilityTheory.entropy ((_root_.prod X (f ∘ X))) μ) = (ProbabilityTheory.entropy X μ) :=
  entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) fun _ _ ab ↦ (Prod.ext_iff.1 ab).1

variable [Countable T]

lemma entropy_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) = (ProbabilityTheory.entropy ((_root_.prod Y X)) μ) := by
  change (ProbabilityTheory.entropy (Prod.swap ∘ (_root_.prod Y X)) μ) = (ProbabilityTheory.entropy ((_root_.prod Y X)) μ)
  exact entropy_comp_of_injective μ (hY.prodMk hX) Prod.swap Prod.swap_injective

lemma entropy_assoc (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod X ((_root_.prod Y Z)))) μ) = (ProbabilityTheory.entropy ((_root_.prod ((_root_.prod X Y)) Z)) μ) := by
  change (ProbabilityTheory.entropy (MeasurableEquiv.prodAssoc ∘ (_root_.prod ((_root_.prod X Y)) Z)) μ) = (ProbabilityTheory.entropy ((_root_.prod ((_root_.prod X Y)) Z)) μ)
  exact entropy_comp_of_injective μ ((hX.prodMk hY).prodMk hZ) _ <| Equiv.injective _

end entropy

section condEntropy

variable [MeasurableSpace T]

variable {X : Ω → S} {Y : Ω → T}

noncomputable
def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ (ProbabilityTheory.entropy X (μ[|Y ← y]))]

lemma condEntropy_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    condEntropy X Y μ = (μ.map Y)[fun y ↦ (ProbabilityTheory.entropy X (μ[|Y ← y]))] := rfl

section

variable [MeasurableSingletonClass T]

lemma condEntropy_eq_kernel_entropy [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] [FiniteRange Y] :
    (ProbabilityTheory.condEntropy X Y μ) = (Kernel.entropy (condDistrib X Y μ) (μ.map Y)) := by
  rw [condEntropy_def, Kernel.entropy]
  apply integral_congr_finiteSupport
  intro t ht
  rw [Measure.map_apply hY (.singleton _)] at ht
  simp only [entropy_def]
  congr
  ext s hs
  rw [condDistrib_apply' hX hY _ _ ht hs, Measure.map_apply hX hs,
      cond_apply (hY (.singleton _))]

variable [Countable T] [Nonempty T] [Nonempty S] [MeasurableSingletonClass S] [Countable S]
  [Countable U] [MeasurableSingletonClass U]

lemma condEntropy_two_eq_kernel_entropy (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange Y] [FiniteRange Z] :
    (ProbabilityTheory.condEntropy X ((_root_.prod Y Z)) μ) =
      (Kernel.entropy (Kernel.condKernel (condDistrib (fun a ↦ (Y a, X a)) Z μ)) (Measure.map Z μ ⊗ₘ Kernel.fst (condDistrib (fun a ↦ (Y a, X a)) Z μ)))
 := by
  rw [Measure.compProd_congr (condDistrib_fst_ae_eq hY hX hZ μ),
      map_compProd_condDistrib hY hZ,
      Kernel.entropy_congr (condKernel_condDistrib_ae_eq hY hX hZ μ),
      ← Kernel.entropy_congr (swap_condDistrib_ae_eq hY hX hZ μ)]
  have : μ.map (fun ω ↦ (Z ω, Y ω)) = (μ.map (fun ω ↦ (Y ω, Z ω))).comap Prod.swap := by
    rw [map_prod_comap_swap hY hZ]
  rw [this, condEntropy_eq_kernel_entropy hX (hY.prodMk hZ), Kernel.entropy_comap_swap]

end

@[simp]
lemma condEntropy_zero_measure (X : Ω → S) (Y : Ω → T) : (ProbabilityTheory.condEntropy X Y ((0 : Measure Ω))) = 0 :=
  by simp [condEntropy]

lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ (ProbabilityTheory.condEntropy X Y μ) :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

lemma condEntropy_eq_sum [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY : Measurable Y) [FiniteRange Y] :
    (ProbabilityTheory.condEntropy X Y μ) = ∑ y ∈ FiniteRange.toFinset Y, ((μ.map Y).real {y}) * (ProbabilityTheory.entropy X (μ[|Y ← y])) := by
  rw [condEntropy_def, integral_eq_setIntegral (ae_mem_of_finiteRange hY),
    setIntegral_finset _ .finset]
  simp_rw [smul_eq_mul]

lemma condEntropy_eq_sum_fintype
    [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY : Measurable Y) [Fintype T] :
    (ProbabilityTheory.condEntropy X Y μ) = ∑ y, μ.real (Y ⁻¹' {y}) * (ProbabilityTheory.entropy X (μ[|Y ← y])) := by
  rw [condEntropy_def, integral_fintype .of_finite]
  simp_rw [smul_eq_mul, map_measureReal_apply hY (.singleton _)]

variable [MeasurableSingletonClass T]

lemma condEntropy_prod_eq_sum {X : Ω → S} {Y : Ω → T} {Z : Ω → T'} [MeasurableSpace T']
    [MeasurableSingletonClass T']
    (μ : Measure Ω) (hY : Measurable Y) (hZ : Measurable Z)
    [IsFiniteMeasure μ] [Finite T] [Fintype T'] :
    (ProbabilityTheory.condEntropy X ((_root_.prod Y Z)) μ) = ∑ z, μ.real (Z ⁻¹' {z}) * (ProbabilityTheory.condEntropy X Y (μ[|Z ⁻¹' {z}])) := by
  cases nonempty_fintype T
  simp_rw [condEntropy_eq_sum_fintype _ _ _ (hY.prodMk hZ), condEntropy_eq_sum_fintype _ _ _ hY,
    Fintype.sum_prod_type_right, Finset.mul_sum, ← mul_assoc]
  congr with y
  congr with x
  have A : (fun a ↦ (Y a, Z a)) ⁻¹' {(x, y)} = Z ⁻¹' {y} ∩ Y ⁻¹' {x} := by
    ext p; simp [and_comm]
  congr 2
  · rw [cond_real_apply (hZ (.singleton y)), A]
    obtain hy | hy := eq_or_ne (μ.real (Z ⁻¹' {y})) 0
    · have : μ.real (Z ⁻¹' {y} ∩ Y ⁻¹' {x}) = 0 :=
        measureReal_mono_null Set.inter_subset_left hy (by finiteness)
      simp [this, hy]
    · rw [mul_inv_cancel_left₀ hy]
  · rw [A, cond_cond_eq_cond_inter (hZ (.singleton y)) (hY (.singleton x))]

variable [MeasurableSingletonClass S]

lemma condEntropy_eq_sum_sum (hX : Measurable X) {Y : Ω → T} (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.condEntropy X Y μ)
      = ∑ y ∈ FiniteRange.toFinset Y, ∑ x ∈ FiniteRange.toFinset X,
        ((μ.map Y).real {y}) * negMulLog (((μ[|Y ← y]).map X).real {x}) := by
  rw [condEntropy_eq_sum _ _ _ hY]
  congr with y
  rw [entropy_cond_eq_sum_finiteRange hX, Finset.mul_sum]

omit [MeasurableSingletonClass S] in

lemma condEntropy_eq_sum_sum_fintype {Y : Ω → T} (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype S] [Fintype T] :
    (ProbabilityTheory.condEntropy X Y μ) = ∑ y, ∑ x, (μ.map Y).real {y} * negMulLog (((μ[|Y ← y]).map X).real {x}) := by
  rw [condEntropy_eq_sum_fintype _ _ _ hY]
  congr with y
  rw [entropy_cond_eq_sum, tsum_fintype, Finset.mul_sum, map_measureReal_apply hY (.singleton _)]

variable [Countable S]

lemma condEntropy_of_injective
    [MeasurableSingletonClass U] (μ : Measure Ω) [IsFiniteMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : T → S → U) (hf : ∀ t, Injective (f t)) [FiniteRange Y] :
    (ProbabilityTheory.condEntropy ((fun ω ↦ f (Y ω) (X ω))) Y μ) = (ProbabilityTheory.condEntropy X Y μ) := by
  rw [condEntropy_eq_sum _ _ _ hY, condEntropy_eq_sum _ _ _ hY]
  have : ∀ y, (ProbabilityTheory.entropy (fun ω ↦ f (Y ω) (X ω)) (μ[|Y ← y])) = (ProbabilityTheory.entropy ((f y ∘ X)) (μ[|Y ← y])) := by
    intro y
    refine entropy_congr ?_
    have : ∀ᵐ ω ∂μ[|Y ← y], Y ω = y := by
      rw [ae_iff, cond_apply (hY (.singleton _))]
      have : {a | ¬Y a = y} = (Y ⁻¹' {y})ᶜ := by ext; simp
      rw [this, Set.inter_compl_self, measure_empty, mul_zero]
    filter_upwards [this] with ω hω
    rw [hω]
    simp
  simp_rw [this]
  congr with y
  rw [entropy_comp_of_injective _ hX (f y) (hf y)]

lemma condEntropy_comp_of_injective {Y : Ω → U}
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Injective f) :
    (ProbabilityTheory.condEntropy (f ∘ X) Y μ) = (ProbabilityTheory.condEntropy X Y μ) :=
  integral_congr_ae (ae_of_all _ (fun _ ↦ entropy_comp_of_injective _ hX f hf))

lemma condEntropy_comm [Countable T] {Z : Ω → U}
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.condEntropy ((_root_.prod X Y)) Z μ) = (ProbabilityTheory.condEntropy ((_root_.prod Y X)) Z μ) := by
  change (ProbabilityTheory.condEntropy ((_root_.prod X Y)) Z μ) = (ProbabilityTheory.condEntropy (Prod.swap ∘ (_root_.prod X Y)) Z μ)
  exact (condEntropy_comp_of_injective μ (hX.prodMk hY) Prod.swap Prod.swap_injective).symm

end condEntropy

section pair

variable [MeasurableSpace T]
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]

lemma chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) = (ProbabilityTheory.entropy X μ) + (ProbabilityTheory.condEntropy Y X μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [entropy_eq_kernel_entropy, Kernel.chain_rule]
  · simp_rw [← Kernel.map_const _ (hX.prodMk hY), Kernel.fst_map_prod _ hY, Kernel.map_const _ hX,
      Kernel.map_const _ (hX.prodMk hY)]
    congr 1
    · rw [Kernel.entropy, integral_dirac]
      rfl
    · simp_rw [condEntropy_eq_kernel_entropy hY hX]
      have : Measure.dirac () ⊗ₘ Kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((), X ω)) := by
        ext s _
        rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prodMk_left hX]
        congr
      rw [this, Kernel.entropy_congr (condDistrib_const_unit hX hY μ)]
      have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) := by
        ext s _
        rw [Measure.map_map measurable_prodMk_left hX]
        rfl
      rw [this, Kernel.entropy_prodMkLeft_unit]
  · apply Kernel.FiniteKernelSupport.aefiniteKernelSupport
    exact Kernel.finiteKernelSupport_of_const _

lemma chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) = (ProbabilityTheory.entropy Y μ) + (ProbabilityTheory.condEntropy X Y μ) := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]

lemma chain_rule'' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.condEntropy X Y μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) - (ProbabilityTheory.entropy Y μ) := by
  rw [chain_rule μ hX hY, add_sub_cancel_left]

lemma IdentDistrib.condEntropy_eq {Ω' : Type*} [MeasurableSpace Ω'] {X : Ω → S} {Y : Ω → T}
    {μ' : Measure Ω'} {X' : Ω' → S} {Y' : Ω' → T} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (h : IdentDistrib ((_root_.prod X Y)) ((_root_.prod X' Y')) μ μ') [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [FiniteRange Y'] :
    (ProbabilityTheory.condEntropy X Y μ) = (ProbabilityTheory.condEntropy X' Y' μ') := by
  have : IdentDistrib Y Y' μ μ' := h.comp measurable_snd
  rw [chain_rule'' _ hX hY, chain_rule'' _ hX' hY', h.entropy_congr, this.entropy_congr]

variable [Countable U] [MeasurableSingletonClass U]

lemma condEntropy_of_injective' (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (f : T → U)
    (hf : Injective f)
    (hfY : Measurable (f ∘ Y)) [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.condEntropy X (f ∘ Y) μ) = (ProbabilityTheory.condEntropy X Y μ) := by
  rw [chain_rule'' μ hX hY, chain_rule'' μ hX hfY, chain_rule' μ hX hY, chain_rule' μ hX hfY]
  congr 1
  · congr 1
    exact condEntropy_comp_of_injective μ hY f hf
  exact entropy_comp_of_injective μ hY f hf

lemma condEntropy_comp_self [IsProbabilityMeasure μ] (hX : Measurable X) {f : S → U}
    (hf : Measurable f) [FiniteRange X] : (ProbabilityTheory.condEntropy X (f ∘ X) μ) = (ProbabilityTheory.entropy X μ) - (ProbabilityTheory.entropy (f ∘ X) μ) := by
  rw [chain_rule'' μ hX (hf.comp hX), entropy_prod_comp hX _ f]

lemma cond_chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    (ProbabilityTheory.condEntropy ((_root_.prod X Y)) Z μ) = (ProbabilityTheory.condEntropy X Z μ) + (ProbabilityTheory.condEntropy Y ((_root_.prod X Z)) μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condEntropy_eq_kernel_entropy (hX.prodMk hY) hZ, Kernel.chain_rule]
  · congr 1
    · rw [condEntropy_eq_kernel_entropy hX hZ]
      refine Kernel.entropy_congr ?_
      exact condDistrib_fst_ae_eq hX hY hZ μ
    · rw [condEntropy_two_eq_kernel_entropy hY hX hZ]
  exact Kernel.aefiniteKernelSupport_condDistrib _ _ μ (by measurability) (by measurability)

lemma cond_chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y]
    [FiniteRange Z] :
    (ProbabilityTheory.condEntropy ((_root_.prod X Y)) Z μ) = (ProbabilityTheory.condEntropy Y Z μ) + (ProbabilityTheory.condEntropy X ((_root_.prod Y Z)) μ) := by
  rw [condEntropy_comm hX hY, cond_chain_rule' _ hY hX hZ]

lemma entropy_comp_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (f : S → U) [FiniteRange X] :
    (ProbabilityTheory.entropy (f ∘ X) μ) ≤ (ProbabilityTheory.entropy X μ) := by
  have hfX : Measurable (f ∘ X) := by fun_prop
  have : (ProbabilityTheory.entropy X μ) = (ProbabilityTheory.entropy ((_root_.prod X (f ∘ X))) μ) := by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule _ hX hfX]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

lemma entropy_of_comp_eq_of_comp
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (f : S → T) (g : T → S) (h1 : Y = f ∘ X) (h2 : X = g ∘ Y) [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.entropy X μ) = (ProbabilityTheory.entropy Y μ) := by
  have h3 : (ProbabilityTheory.entropy X μ) ≤ (ProbabilityTheory.entropy Y μ) := by
    rw [h2]; exact entropy_comp_le μ hY _
  have h4 : (ProbabilityTheory.entropy Y μ) ≤ (ProbabilityTheory.entropy X μ) := by
    rw [h1]; exact entropy_comp_le μ hX _
  linarith

end pair

section mutualInfo

variable [MeasurableSpace T]

noncomputable
def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.entropy ((_root_.prod X Y)) μ)

lemma mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) := rfl

lemma entropy_add_entropy_sub_mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    (ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) := sub_sub_self _ _

lemma IdentDistrib.mutualInfo_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} (hXY : IdentDistrib ((_root_.prod X Y)) ((_root_.prod X' Y')) μ μ') :
      (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.mutualInfo X' Y' μ') := by
  have hX : IdentDistrib X X' μ μ' := hXY.comp measurable_fst
  have hY : IdentDistrib Y Y' μ μ' := hXY.comp measurable_snd
  simp_rw [mutualInfo_def,hX.entropy_congr,hY.entropy_congr,hXY.entropy_congr]

noncomputable
def condMutualInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ (ProbabilityTheory.entropy X (μ[|Z ← z])) + (ProbabilityTheory.entropy Y (μ[|Z ← z])) - (ProbabilityTheory.entropy ((_root_.prod X Y)) (μ[|Z ← z]))]

lemma condMutualInfo_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInfo X Y Z μ = (μ.map Z)[fun z ↦
      (ProbabilityTheory.entropy X (μ[|Z ← z])) + (ProbabilityTheory.entropy Y (μ[|Z ← z])) - (ProbabilityTheory.entropy ((_root_.prod X Y)) (μ[|Z ← z]))] := rfl

lemma condMutualInfo_eq_integral_mutualInfo :
    (ProbabilityTheory.condMutualInfo X Y Z μ) = (μ.map Z)[fun z ↦ (ProbabilityTheory.mutualInfo X Y (μ[| Z ⁻¹' {z}]))] := rfl

@[simp] lemma condMutualInfo_zero_measure : (ProbabilityTheory.condMutualInfo X Y Z 0) = 0 := by
  simp [condMutualInfo]

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

lemma mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ (ProbabilityTheory.mutualInfo X Y μ) := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map ((_root_.prod X Y))).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map ((_root_.prod X Y))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg

lemma entropy_pair_le_add (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [FiniteRange X]
    [FiniteRange Y] : (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) ≤ (ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy Y μ) :=
  sub_nonneg.1 <| mutualInfo_nonneg hX hY _

lemma mutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.mutualInfo X Y μ) = 0 ↔ IndepFun X Y μ := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map ((_root_.prod X Y))).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map ((_root_.prod X Y))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd, ← measureMutualInfo.eq_def, measureMutualInfo_eq_zero_iff]
  simp [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.ext_iff_measureReal_singleton_finiteSupport,
    Measure.map_map measurable_fst (hX.prodMk hY),
    Measure.map_map measurable_snd (hX.prodMk hY), ← measureReal_prod_prod, Function.comp_def]

protected alias ⟨_, IndepFun.mutualInfo_eq_zero⟩ := mutualInfo_eq_zero

lemma mutualInfo_const (hX : Measurable X) (c : T)
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] [FiniteRange X] :
    (ProbabilityTheory.mutualInfo X (fun _ ↦ c) μ) = 0 :=
  (indepFun_const c).mutualInfo_eq_zero hX measurable_const

lemma entropy_pair_eq_add (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) = (ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy Y μ) ↔ IndepFun X Y μ := by
  rw [eq_comm, ← sub_eq_zero, ← mutualInfo_eq_zero hX hY]; rfl

protected alias ⟨_, IndepFun.entropy_pair_eq_add⟩ := entropy_pair_eq_add

variable [Countable S] [Countable T]

lemma mutualInfo_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.mutualInfo Y X μ) := by simp_rw [mutualInfo, add_comm, entropy_comm hX hY]

lemma mutualInfo_eq_entropy_sub_condEntropy
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.entropy X μ) - (ProbabilityTheory.condEntropy X Y μ) := by
  rw [mutualInfo_def, chain_rule μ hX hY]
  abel

lemma mutualInfo_eq_entropy_sub_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.condEntropy Y X μ) := by
  rw [mutualInfo_comm hX hY, mutualInfo_eq_entropy_sub_condEntropy hY hX]

lemma entropy_sub_mutualInfo_eq_condEntropy (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.entropy X μ) - (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.condEntropy X Y μ) := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY, sub_sub_self]

lemma entropy_sub_mutualInfo_eq_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.mutualInfo X Y μ) = (ProbabilityTheory.condEntropy Y X μ) := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' hX hY, sub_sub_self]

lemma IndepFun.condEntropy_eq_entropy {μ : Measure Ω} (h : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y) [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.condEntropy X Y μ) = (ProbabilityTheory.entropy X μ) := by
  have := h.mutualInfo_eq_zero hX hY
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY] at this
  linarith

variable [Countable U] [MeasurableSingletonClass U] [Nonempty S] [Nonempty T]

lemma condMutualInfo_eq_kernel_mutualInfo
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange Z] :
    (ProbabilityTheory.condMutualInfo X Y Z μ) = (Kernel.mutualInfo (condDistrib ((_root_.prod X Y)) Z μ) (μ.map Z)) := by
  rcases finiteSupport_of_finiteRange (μ := μ) (X := Z) with ⟨A, hA⟩
  simp_rw [condMutualInfo_def, entropy_def, Kernel.mutualInfo, Kernel.entropy,
    integral_eq_setIntegral hA, setIntegral_finset _ .finset, smul_eq_mul, mul_sub,
    mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr with x
  · have h := condDistrib_fst_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx, Measure.real]
    rw [h hx, condDistrib_apply hX hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx
  · have h := condDistrib_snd_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx, Measure.real]
    rw [h hx, condDistrib_apply hY hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx
  · by_cases hx : (μ.map Z) {x} = 0
    · simp [hx, Measure.real]
    rw [condDistrib_apply (hX.prodMk hY) hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx

end

lemma condMutualInfo_eq_sum [MeasurableSingletonClass U] [IsFiniteMeasure μ]
    (hZ : Measurable Z) [FiniteRange Z] :
    (ProbabilityTheory.condMutualInfo X Y Z μ) = ∑ z ∈ FiniteRange.toFinset Z,
      μ.real (Z ⁻¹' {z}) * (ProbabilityTheory.mutualInfo X Y (μ[|Z ← z])) := by
  rw [condMutualInfo_eq_integral_mutualInfo,
    integral_eq_setIntegral (ae_mem_of_finiteRange hZ),
    setIntegral_finset _ .finset]
  congr 1 with z
  rw [map_measureReal_apply hZ (MeasurableSet.singleton z)]
  rfl

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

lemma condMutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) {Z : Ω → U} {μ : Measure Ω}
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ (ProbabilityTheory.condMutualInfo X Y Z μ) := by
  refine integral_nonneg (fun z ↦ ?_)
  exact mutualInfo_nonneg hX hY _

variable [Countable S] [Countable T]

lemma condMutualInfo_comm
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) :
    (ProbabilityTheory.condMutualInfo X Y Z μ) = (ProbabilityTheory.condMutualInfo Y X Z μ) := by
  simp_rw [condMutualInfo_def, add_comm, entropy_comm hX hY]

variable [MeasurableSingletonClass U]

lemma condMutualInfo_eq [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange Z] :
    (ProbabilityTheory.condMutualInfo X Y Z μ) = (ProbabilityTheory.condEntropy X Z μ) + (ProbabilityTheory.condEntropy Y Z μ) - (ProbabilityTheory.condEntropy ((_root_.prod X Y)) Z μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condMutualInfo_eq_kernel_mutualInfo hX hY hZ, Kernel.mutualInfo,
    Kernel.entropy_congr (condDistrib_fst_ae_eq hX hY hZ _),
    Kernel.entropy_congr (condDistrib_snd_ae_eq hX hY hZ _),
    condEntropy_eq_kernel_entropy hX hZ, condEntropy_eq_kernel_entropy hY hZ,
    condEntropy_eq_kernel_entropy (hX.prodMk hY) hZ]

lemma condMutualInfo_eq' [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    (ProbabilityTheory.condMutualInfo X Y Z μ) = (ProbabilityTheory.condEntropy X Z μ) - (ProbabilityTheory.condEntropy X ((_root_.prod Y Z)) μ) := by
  rw [condMutualInfo_eq hX hY hZ, cond_chain_rule _ hX hY hZ]
  ring

lemma condMutualInfo_of_inj_map [Countable U] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (f : U → S → V) (hf : ∀ t, Function.Injective (f t)) [FiniteRange Z] :
    (ProbabilityTheory.condMutualInfo (fun ω ↦ f (Z ω) (X ω)) Y Z μ) =
    (ProbabilityTheory.condMutualInfo X Y Z μ) := by
  have hM : Measurable (Function.uncurry f ∘ (_root_.prod Z X)) := by fun_prop
  have hM : Measurable fun ω ↦ f (Z ω) (X ω) := hM
  rw [condMutualInfo_eq hM hY hZ, condMutualInfo_eq hX hY hZ]
  let g : U → (S × T) → (V × T) := fun z (x, y) ↦ (f z x, y)
  have hg : ∀ t, Function.Injective (g t) :=
    fun _ _ _ h ↦ Prod.ext_iff.2 ⟨hf _ (Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2⟩
  rw [← condEntropy_of_injective μ (hX.prodMk hY) hZ g hg, ← condEntropy_of_injective μ hX hZ _ hf]

lemma condMutualInfo_of_inj [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    {f : U → V} (hf : Function.Injective f) :
    (ProbabilityTheory.condMutualInfo X Y (f ∘ Z) μ) = (ProbabilityTheory.condMutualInfo X Y Z μ) := by
  have hfZ : Measurable (f ∘ Z) := by fun_prop
  rw [condMutualInfo_eq hX hY hZ, condMutualInfo_eq hX hY hfZ,
    condEntropy_of_injective' _ hX hZ _ hf hfZ, condEntropy_of_injective' _ hY hZ _ hf hfZ,
    condEntropy_of_injective' _ (hX.prodMk hY) hZ _ hf hfZ]

end

section IsProbabilityMeasure

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable U] [MeasurableSingletonClass U]

lemma condMutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    (ProbabilityTheory.condMutualInfo X Y Z μ) = 0 ↔ PfrCondIndepFun X Y Z μ := by
  rw [pfrCondIndepFun_iff, condMutualInfo_eq_integral_mutualInfo, integral_eq_zero_iff_of_nonneg]
  · have : (fun x ↦ (ProbabilityTheory.mutualInfo X Y (μ[| Z ⁻¹' {x}]))) =ᵐ[μ.map Z] 0 ↔
      ∀ᵐ z ∂(μ.map Z), (ProbabilityTheory.mutualInfo X Y (μ[| Z ⁻¹' {z}])) = 0 := by rfl
    rw [this]
    apply Filter.eventually_congr
    rw [ae_iff_of_countable]
    intro z _hz
    exact mutualInfo_eq_zero hX hY
  · intro z
    by_cases hz : μ (Z ⁻¹' {z}) = 0
    · simp [cond_eq_zero_of_meas_eq_zero hz, mutualInfo_def]
    · exact mutualInfo_nonneg hX hY _
  · exact integrable_of_finiteSupport _

variable (μ)
variable [Countable S] [Countable T]

lemma ent_of_cond_indep (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
     (h : PfrCondIndepFun X Y Z μ) [IsZeroOrProbabilityMeasure μ]
     [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
     (ProbabilityTheory.entropy ((_root_.prod X ((_root_.prod Y Z)))) μ) = (ProbabilityTheory.entropy ((_root_.prod X Z)) μ) + (ProbabilityTheory.entropy ((_root_.prod Y Z)) μ) - (ProbabilityTheory.entropy Z μ) := by
  have hI : (ProbabilityTheory.condMutualInfo X Y Z μ) = 0 := (condMutualInfo_eq_zero hX hY).mpr h
  rw [condMutualInfo_eq hX hY hZ] at hI
  rw [entropy_assoc hX hY hZ, chain_rule _ (hX.prodMk hY) hZ, chain_rule _ hX hZ,
    chain_rule _ hY hZ]
  linarith [hI]

variable [IsZeroOrProbabilityMeasure μ]

lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : (ProbabilityTheory.entropy X μ) - (ProbabilityTheory.condEntropy X Y μ) = (ProbabilityTheory.mutualInfo X Y μ) := by
  rw [mutualInfo_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : (ProbabilityTheory.condEntropy X Y μ) ≤ (ProbabilityTheory.entropy X μ) :=
  sub_nonneg.1 <| by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInfo_nonneg hX hY _

lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    (ProbabilityTheory.condEntropy X ((_root_.prod Y Z)) μ) ≤ (ProbabilityTheory.condEntropy X Z μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  refine (Kernel.entropy_condKernel_le_entropy_snd ?_).trans_eq ?_
  · apply Kernel.aefiniteKernelSupport_condDistrib
    all_goals fun_prop
  exact Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ _)

lemma condEntropy_comp_ge
    [FiniteRange X] [FiniteRange Y] (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : S → U) : (ProbabilityTheory.condEntropy Y (f ∘ X) μ) ≥ (ProbabilityTheory.condEntropy Y X μ) := by
  have h_joint : (ProbabilityTheory.entropy ((_root_.prod Y ((_root_.prod X (f ∘ X))))) μ) = (ProbabilityTheory.entropy ((_root_.prod Y X)) μ) := by
    let g : T × S → T × S × U := fun (y, x) ↦ (y, (x, f x))
    change (ProbabilityTheory.entropy (g ∘ (_root_.prod Y X)) μ) = (ProbabilityTheory.entropy ((_root_.prod Y X)) μ)
    refine entropy_comp_of_injective μ (by exact Measurable.prod hY hX) g (fun _ _ h => ?_)
    repeat rewrite [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  have hZ : Measurable (f ∘ X) := by fun_prop
  rewrite [chain_rule'' μ hY hX, ← entropy_prod_comp hX μ f, ← h_joint,
    ← chain_rule'' μ hY (Measurable.prod (by exact hX) (by exact hZ))]
  exact entropy_submodular μ hY hX hZ

lemma entropy_triple_add_entropy_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    (ProbabilityTheory.entropy ((_root_.prod X ((_root_.prod Y Z)))) μ) + (ProbabilityTheory.entropy Z μ) ≤ (ProbabilityTheory.entropy ((_root_.prod X Z)) μ) + (ProbabilityTheory.entropy ((_root_.prod Y Z)) μ) := by
  rw [chain_rule _ hX (hY.prodMk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)

end IsProbabilityMeasure
end mutualInfo
end ProbabilityTheory

section dataProcessing

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

universe uΩ uS uT uU uV uW

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW}
  [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSpace W]
  [Countable S] [Countable T] [Countable V] [Countable W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

lemma mutual_comp_le [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.mutualInfo (f ∘ X) Y μ) ≤ (ProbabilityTheory.mutualInfo X Y μ) := by
  have h_meas : Measurable (f ∘ X) := by fun_prop
  rw [mutualInfo_comm h_meas hY, mutualInfo_comm hX hY,
    mutualInfo_eq_entropy_sub_condEntropy hY h_meas, mutualInfo_eq_entropy_sub_condEntropy hY hX]
  gcongr
  exact condEntropy_comp_ge μ hX hY f

lemma mutual_comp_comp_le [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) (g : T → V) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    (ProbabilityTheory.mutualInfo (f ∘ X) (g ∘ Y) μ) ≤ (ProbabilityTheory.mutualInfo X Y μ) :=
  calc
    _ ≤ (ProbabilityTheory.mutualInfo X (g ∘ Y) μ) := mutual_comp_le μ hX (Measurable.comp hg hY) f
    _ = (ProbabilityTheory.mutualInfo (g ∘ Y) X μ) := mutualInfo_comm hX (Measurable.comp hg hY) μ
    _ ≤ (ProbabilityTheory.mutualInfo Y X μ) := mutual_comp_le μ hY hX g
    _ = (ProbabilityTheory.mutualInfo X Y μ) := mutualInfo_comm hY hX μ

end ProbabilityTheory
end dataProcessing

section MeasureSpace_example

open ProbabilityTheory

variable {Ω S T : Type*} [MeasureSpace Ω] [IsZeroOrProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

example (hX : Measurable X) (hY : Measurable Y) :
  (ProbabilityTheory.entropy ((_root_.prod X Y)) ℙ) = (ProbabilityTheory.entropy Y ℙ) + (ProbabilityTheory.condEntropy X Y ℙ) := chain_rule _ hX hY

end MeasureSpace_example
end

/- PFR.ForMathlib.Entropy.Kernel.Group -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory

variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [MeasurableSpace T]
  [MeasurableSpace G] [MeasurableSingletonClass G] [AddGroup G] [Countable G]
  {κ : Kernel T G} {μ : Measure T}

@[simp]
lemma measureEntropy_neg (μ : Measure G) : (ProbabilityTheory.measureEntropy (μ.map ((-·)))) = (ProbabilityTheory.measureEntropy μ) :=
  measureEntropy_map_of_injective μ _ measurable_neg neg_injective

namespace ProbabilityTheory.Kernel

lemma entropy_neg (κ : Kernel T G) (μ : Measure T) : (Kernel.entropy (map κ ((-·))) μ) = (Kernel.entropy κ μ) :=
  entropy_map_of_injective κ μ neg_injective measurable_neg

lemma entropy_sub_comm (κ : Kernel T (G × G)) (μ : Measure T) :
    (Kernel.entropy (map κ (fun p ↦ p.1 - p.2)) μ)
      = (Kernel.entropy (map κ (fun p ↦ p.2 - p.1)) μ) := by
  rw [← entropy_neg, Kernel.map_map _ (by fun_prop) (by fun_prop)]
  congr with x
  simp

variable [Countable T] [MeasurableSingletonClass T]

lemma entropy_snd_sub_mutualInfo_le_entropy_map_add
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (snd κ) μ) - (Kernel.mutualInfo κ μ) ≤ (Kernel.entropy (map κ (fun p ↦ p.1 + p.2)) μ) :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ add_right_injective hκ

lemma entropy_snd_sub_mutualInfo_le_entropy_map_add'
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (snd κ) μ) - (Kernel.mutualInfo κ μ) ≤ (Kernel.entropy (map κ (fun p ↦ p.2 + p.1)) μ) :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ add_left_injective hκ

lemma entropy_fst_sub_mutualInfo_le_entropy_map_add
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (fst κ) μ) - (Kernel.mutualInfo κ μ) ≤ (Kernel.entropy (map κ (fun p ↦ p.1 + p.2)) μ) := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_add' (swapRight κ) μ hκ.swapRight
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.2 + p.1) ∘ Prod.swap = (fun p ↦ p.1 + p.2) := rfl
    simp_rw [this]

lemma entropy_fst_sub_mutualInfo_le_entropy_map_add'
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (fst κ) μ) - (Kernel.mutualInfo κ μ) ≤ (Kernel.entropy (map κ (fun p ↦ p.2 + p.1)) μ) := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_add (swapRight κ) μ hκ.swapRight
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 + p.2) ∘ Prod.swap = (fun p ↦ p.2 + p.1) := rfl
    simp_rw [this]

lemma entropy_snd_sub_mutualInfo_le_entropy_map_sub
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (snd κ) μ) - (Kernel.mutualInfo κ μ) ≤ (Kernel.entropy (map κ (fun p ↦ p.1 - p.2)) μ) :=
  entropy_snd_sub_mutualInfo_le_entropy_map_of_injective κ μ _ (fun _ ↦ sub_right_injective) hκ

lemma entropy_fst_sub_mutualInfo_le_entropy_map_sub
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    (Kernel.entropy (fst κ) μ) - (Kernel.mutualInfo κ μ) ≤ (Kernel.entropy (map κ (fun p ↦ p.1 - p.2)) μ) := by
    have h := entropy_snd_sub_mutualInfo_le_entropy_map_sub (swapRight κ) μ hκ.swapRight
    simp only [snd_swapRight, mutualInfo_swapRight, map_swapRight] at h
    refine h.trans_eq ?_
    have : (fun p : G × G ↦ p.1 - p.2) ∘ Prod.swap = (fun p ↦ p.2 - p.1) := rfl
    simp_rw [this]
    rw [← entropy_sub_comm]

lemma max_entropy_sub_mutualInfo_le_entropy_add
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    max ((Kernel.entropy (fst κ) μ)) ((Kernel.entropy (snd κ) μ)) - (Kernel.mutualInfo κ μ)
      ≤ (Kernel.entropy (map κ (fun p ↦ p.1 + p.2)) μ) := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_add _ _ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_add _ _ hκ⟩

lemma max_entropy_sub_mutualInfo_le_entropy_add'
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    max ((Kernel.entropy (fst κ) μ)) ((Kernel.entropy (snd κ) μ)) - (Kernel.mutualInfo κ μ)
      ≤ (Kernel.entropy (map κ (fun p ↦ p.2 + p.1)) μ) := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_add' _ _ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_add' _ _ hκ⟩

lemma max_entropy_sub_mutualInfo_le_entropy_sub
    (κ : Kernel T (G × G)) [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    max ((Kernel.entropy (fst κ) μ)) ((Kernel.entropy (snd κ) μ)) - (Kernel.mutualInfo κ μ)
      ≤ (Kernel.entropy (map κ (fun p ↦ p.1 - p.2)) μ) := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_fst_sub_mutualInfo_le_entropy_map_sub _ _ hκ,
    entropy_snd_sub_mutualInfo_le_entropy_map_sub _ _ hκ⟩

lemma max_entropy_le_entropy_sub_prod
    (κ : Kernel T G) [IsMarkovKernel κ] (η : Kernel T G) [IsMarkovKernel η]
    (μ : Measure T) [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    max ((Kernel.entropy κ μ)) ((Kernel.entropy η μ)) ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1 - p.2)) μ) := by
  calc max ((Kernel.entropy κ μ)) ((Kernel.entropy η μ))
    = max ((Kernel.entropy κ μ)) ((Kernel.entropy η μ)) - (Kernel.mutualInfo (κ ×ₖ η) μ) := by
        rw [mutualInfo_prod _ hκ hη, sub_zero]
  _ ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1 - p.2)) μ) := by
        convert max_entropy_sub_mutualInfo_le_entropy_sub (κ ×ₖ η) μ (hκ.prod hη)
        · simp
        · simp

end ProbabilityTheory.Kernel
end

/- PFR.ForMathlib.Entropy.Group -/
noncomputable section
open scoped ProbabilityTheory
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

universe uΩ uS uT uU
variable {Ω : Type uΩ} {G : Type uS} {T : Type uT} {U : Type uU} [mΩ : MeasurableSpace Ω]
  [Countable G] [Countable T] [Countable U]
  [hG : MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass G] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [AddGroup G] {X Y : Ω → G} {μ : Measure Ω}

namespace ProbabilityTheory
section entropy

@[simp]
lemma entropy_add_const (hX : Measurable X) (c : G) :
    (ProbabilityTheory.entropy (X + fun _ ↦ c) μ) = (ProbabilityTheory.entropy X μ) := by
  apply entropy_comp_of_injective μ hX _ <| add_left_injective c

lemma entropy_add_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod X (X + Y))) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) := by
  change (ProbabilityTheory.entropy ((Equiv.refl _).prodShear Equiv.addLeft ∘ (_root_.prod X Y)) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ)
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ <| Equiv.injective _

lemma entropy_add_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod X (Y + X))) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) := by
  change (ProbabilityTheory.entropy ((Equiv.refl _).prodShear Equiv.addRight ∘ (_root_.prod X Y)) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ)
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ <| Equiv.injective _

lemma entropy_add_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod (Y + X) Y)) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) :=
  (entropy_comm (hY.add hX) hY _).trans <| (entropy_add_right hY hX _).trans <| entropy_comm hY hX _

lemma entropy_sub_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod X (X - Y))) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) := by
  change (ProbabilityTheory.entropy ((Equiv.refl _).prodShear Equiv.subLeft ∘ (_root_.prod X Y)) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ)
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)

lemma entropy_sub_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod X (Y - X))) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) := by
  change (ProbabilityTheory.entropy ((Equiv.refl _).prodShear Equiv.subRight ∘ (_root_.prod X Y)) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ)
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)

lemma entropy_sub_left' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    (ProbabilityTheory.entropy ((_root_.prod (X - Y) Y)) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) :=
  (entropy_comm (hX.sub hY) hY _).trans <| (entropy_sub_right' hY hX _).trans <|
    entropy_comm hY hX _

lemma entropy_neg (hX : Measurable X) : (ProbabilityTheory.entropy ((-X)) μ) = (ProbabilityTheory.entropy X μ) :=
  entropy_comp_of_injective μ hX ((-·)) neg_injective

lemma entropy_sub_comm {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.entropy (X - Y) μ) = (ProbabilityTheory.entropy (Y - X) μ) := by rw [← neg_sub]; exact entropy_neg (hY.sub hX)

end entropy

section condEntropy
variable [IsFiniteMeasure μ] [FiniteRange Y]

lemma condEntropy_add_left (hX : Measurable X) (hY : Measurable Y) :
     (ProbabilityTheory.condEntropy (Y + X) Y μ) = (ProbabilityTheory.condEntropy X Y μ) :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y + x) add_right_injective

lemma condEntropy_add_right (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.condEntropy (X + Y) Y μ) = (ProbabilityTheory.condEntropy X Y μ) :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x + y) add_left_injective

lemma condEntropy_sub_left (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.condEntropy (Y - X) Y μ) = (ProbabilityTheory.condEntropy X Y μ) :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y - x) fun _ ↦ sub_right_injective

lemma condEntropy_sub_right (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.condEntropy (X - Y) Y μ) = (ProbabilityTheory.condEntropy X Y μ) :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x - y) fun _ ↦ sub_left_injective

end condEntropy

section mutualInfo

variable [FiniteRange X] [FiniteRange Y]

lemma mutualInfo_add_right (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h : IndepFun X Y μ) :
    (ProbabilityTheory.mutualInfo X (X + Y) μ) = (ProbabilityTheory.entropy (X + Y) μ) - (ProbabilityTheory.entropy Y μ) := by
  rw [mutualInfo_def, entropy_add_right hX hY, h.entropy_pair_eq_add hX hY]
  abel

end mutualInfo

section IsProbabilityMeasure
variable [IsProbabilityMeasure μ] {Y : Ω → G} [FiniteRange X] [FiniteRange Y]

lemma entropy_sub_mutualInfo_le_entropy_add (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.entropy X μ) - (ProbabilityTheory.mutualInfo X Y μ) ≤ (ProbabilityTheory.entropy (X + Y) μ) := by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_add_right hX hY]
  exact condEntropy_le_entropy _ (hX.add hY) hY

lemma entropy_sub_mutualInfo_le_entropy_add' (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.mutualInfo X Y μ) ≤ (ProbabilityTheory.entropy (X + Y) μ) := by
  rw [entropy_sub_mutualInfo_eq_condEntropy' hX hY, ← condEntropy_add_left hY hX]
  exact condEntropy_le_entropy _ (hX.add hY) hX

lemma entropy_sub_mutualInfo_le_entropy_sub (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.entropy X μ) - (ProbabilityTheory.mutualInfo X Y μ) ≤ (ProbabilityTheory.entropy (X - Y) μ) := by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_sub_right hX hY]
  exact condEntropy_le_entropy _ (hX.sub hY) hY

lemma entropy_sub_mutualInfo_le_entropy_sub' (hX : Measurable X) (hY : Measurable Y) :
    (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.mutualInfo X Y μ) ≤ (ProbabilityTheory.entropy (X - Y) μ) := by
  rw [mutualInfo_comm hX hY, entropy_sub_mutualInfo_eq_condEntropy hY hX,
    ← condEntropy_sub_left hY hX]
  exact condEntropy_le_entropy _ (hX.sub hY) hX

lemma max_entropy_sub_mutualInfo_le_entropy_add (hX : Measurable X) (hY : Measurable Y) :
    max (ProbabilityTheory.entropy X μ) (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.mutualInfo X Y μ) ≤ (ProbabilityTheory.entropy (X + Y) μ) := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_add hX hY, entropy_sub_mutualInfo_le_entropy_add' hX hY⟩

lemma max_entropy_sub_mutualInfo_le_entropy_sub (hX : Measurable X) (hY : Measurable Y) :
    max (ProbabilityTheory.entropy X μ) (ProbabilityTheory.entropy Y μ) - (ProbabilityTheory.mutualInfo X Y μ) ≤ (ProbabilityTheory.entropy (X - Y) μ) := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_sub hX hY, entropy_sub_mutualInfo_le_entropy_sub' hX hY⟩

lemma max_entropy_le_entropy_add (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    max (ProbabilityTheory.entropy X μ) (ProbabilityTheory.entropy Y μ) ≤ (ProbabilityTheory.entropy (X + Y) μ) := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_add hX hY (μ := μ)

lemma max_entropy_le_entropy_sub (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    max (ProbabilityTheory.entropy X μ) (ProbabilityTheory.entropy Y μ) ≤ (ProbabilityTheory.entropy (X - Y) μ) := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_sub hX hY (μ := μ)

end IsProbabilityMeasure
end ProbabilityTheory
end

/- PFR.ForMathlib.Entropy.Kernel.RuzsaDist -/
noncomputable section
open scoped ProbabilityTheory
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {T T' T'' G : Type*} [MeasurableSpace T] [MeasurableSpace T'] [MeasurableSpace T'']
  [MeasurableSpace G] [AddCommGroup G]

noncomputable
def rdistm (μ ν : Measure G) : ℝ := (ProbabilityTheory.measureEntropy ((μ.prod ν).map (fun x ↦ x.1 - x.2))) - (ProbabilityTheory.measureEntropy μ)/2 - (ProbabilityTheory.measureEntropy ν)/2

noncomputable
def rdist (κ : Kernel T G) (η : Kernel T' G) (μ : Measure T) (ν : Measure T') : ℝ :=
  (μ.prod ν)[fun p ↦ rdistm (κ p.1) (η p.2)]

@[simp] lemma rdist_zero_right (κ : Kernel T G) (η : Kernel T' G) (μ : Measure T) :
    (Kernel.rdist κ η μ 0) = 0 := by
  simp [rdist]

@[simp] lemma rdist_zero_left (κ : Kernel T G) (η : Kernel T' G) (ν' : Measure T') :
    (Kernel.rdist κ η 0 ν') = 0 := by
  simp [rdist]

section

variable [Countable T] [MeasurableSingletonClass T] [Countable T'] [MeasurableSingletonClass T']

lemma rdist_eq {κ : Kernel T G} {η : Kernel T' G} {μ : Measure T} {ν : Measure T'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.rdist κ η μ ν) = (μ.prod ν)[fun p ↦ (ProbabilityTheory.measureEntropy (((κ p.1).prod (η p.2)).map (fun x ↦ x.1 - x.2)))]
      - (Kernel.entropy κ μ)/2 - (Kernel.entropy η ν)/2 := by
  rw [rdist]
  simp_rw [rdistm]
  rw [integral_sub, integral_sub]
  · simp_rw [div_eq_mul_inv, integral_mul_const, integral_prod _ (integrable_of_finiteSupport _)]
    simp [entropy]
  all_goals { exact integrable_of_finiteSupport _ }

variable [MeasurableSingletonClass G] [Countable G]

lemma rdist_eq'
    {κ : Kernel T G} {η : Kernel T' G} [IsFiniteKernel κ] [IsFiniteKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.rdist κ η μ ν) =
      (Kernel.entropy (map ((prodMkRight T' κ) ×ₖ (prodMkLeft T η)) (fun x ↦ x.1 - x.2)) (μ.prod ν))
      - (Kernel.entropy κ μ)/2 - (Kernel.entropy η ν)/2 := by
  rw [rdist_eq]
  congr with p
  simp only
  rw [map_apply _ (by fun_prop), prod_apply, prodMkLeft_apply, prodMkRight_apply]

lemma rdist_symm {κ : Kernel T G} {η : Kernel T' G} [IsFiniteKernel κ] [IsFiniteKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.rdist κ η μ ν) = (Kernel.rdist η κ ν μ) := by
  rw [rdist_eq', rdist_eq', sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_comap_swap, comap_map_comm _ _ (by fun_prop), entropy_sub_comm, Measure.comap_swap,
    Measure.prod_swap, comap_prod_swap, map_map _ (by fun_prop) (by fun_prop)]
  congr

@[simp] lemma rdist_zero_kernel_right {κ : Kernel T G} [IsFiniteKernel κ]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.rdist κ 0 μ ν) = - (Kernel.entropy κ μ) / 2 := by
  rw [rdist_eq']
  simp only [prodMkLeft_zero, entropy_zero_kernel, zero_div, sub_zero]
  rw [sub_eq_iff_eq_add]
  ring_nf
  have : map (prodMkRight T' κ ×ₖ (0 : Kernel (T × T') G)) (fun x ↦ x.1 - x.2)
      = 0 := by
    ext1 x
    rw [map_apply _ (by fun_prop), prod_apply]
    simp
  rw [this, entropy_zero_kernel]

@[simp] lemma rdist_zero_kernel_left {η : Kernel T' G} [IsFiniteKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.rdist 0 η μ ν) = - (Kernel.entropy η ν) / 2 := by
  rw [rdist_symm, rdist_zero_kernel_right]

@[simp] lemma rdist_dirac_zero_right {κ : Kernel T G} [IsFiniteKernel κ]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.rdist κ (const T' (Measure.dirac 0)) μ ν) = (Kernel.entropy κ μ) / 2 := by
  rw [rdist_eq']
  simp only [entropy_const, measure_univ, ENNReal.toReal_one, measureEntropy_dirac, mul_zero,
    zero_div, sub_zero]
  rw [sub_eq_iff_eq_add]
  ring_nf
  have : map (prodMkRight T' κ ×ₖ prodMkLeft T (const T' (Measure.dirac 0)))
        (fun x ↦ x.1 - x.2)
      = prodMkRight T' κ := by
    ext x s hs
    rw [prodMkRight_apply, map_apply _ (by fun_prop), prod_apply, prodMkLeft_apply, const_apply,
      prodMkRight_apply, Measure.map_apply measurable_sub hs,
      Measure.prod_apply (measurable_sub hs)]
    have (x : G) : Prod.mk x ⁻¹' ((fun p : G × G ↦ p.1 - p.2) ⁻¹' s) = {y | x - y ∈ s} := by
      ext; simp
    simp_rw [this]
    have (x : G) : Set.indicator {y | x - y ∈ s} (1 : G → ℝ≥0∞) 0 = s.indicator (fun _ ↦ 1) x := by
      by_cases hx : x ∈ s <;> simp [hx]
    simp only [Measure.dirac_apply, this]
    rw [lintegral_indicator_const hs, one_mul]
  rw [this, entropy_prodMkRight']

@[simp] lemma rdist_dirac_zero_left {η : Kernel T' G} [IsFiniteKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν] :
    (Kernel.rdist (const T (Measure.dirac 0)) η μ ν) = (Kernel.entropy η ν) / 2 := by
  rw [rdist_symm, rdist_dirac_zero_right]

lemma ruzsa_triangle_aux {T : Type*} [MeasurableSpace T] (κ : Kernel T (G × G)) (η : Kernel T G)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    map (κ ×ₖ η) (fun p ↦ p.2 - p.1.2)
      = map (η ×ₖ snd κ) (fun p ↦ p.1 - p.2) := by
  have : (fun p : G × G ↦ p.1 - p.2) = (fun p ↦ p.2 - p.1) ∘ Prod.swap := by ext1 p; simp
  rw [this, ← map_map _ measurable_swap .of_discrete, map_prod_swap]
  ext x s hs
  rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs,
    prod_apply' _ _ _ .of_discrete, prod_apply' _ _ _ .of_discrete, lintegral_snd _ _ .of_discrete]
  congr

lemma abs_sub_entropy_le_rdist {κ : Kernel T G} {η : Kernel T' G}
    [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η ν) :
    |(Kernel.entropy κ μ) - (Kernel.entropy η ν)| ≤ 2 * (Kernel.rdist κ η μ ν) := by
  have h := max_entropy_le_entropy_sub_prod (prodMkRight T' κ) (prodMkLeft T η) (μ.prod ν)
    (hκ.prodMkRight ν) (hη.prodMkLeft μ)
  rw [entropy_prodMkRight', entropy_prodMkLeft] at h
  rw [rdist_eq', abs_le]
  constructor
  · linarith [le_max_right ((Kernel.entropy κ μ)) ((Kernel.entropy η ν))]
  · linarith [le_max_left ((Kernel.entropy κ μ)) ((Kernel.entropy η ν))]

lemma rdist_nonneg {κ : Kernel T G} {η : Kernel T' G}
    [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} {ν : Measure T'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [FiniteSupport μ] [FiniteSupport ν]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η ν) :
    0 ≤ (Kernel.rdist κ η μ ν) := by
  suffices 0 ≤ 2 * (Kernel.rdist κ η μ ν) by linarith
  calc 0 ≤ |(Kernel.entropy κ μ) - (Kernel.entropy η ν)| := abs_nonneg _
  _ ≤ 2 * (Kernel.rdist κ η μ ν) := abs_sub_entropy_le_rdist hκ hη

lemma ent_of_diff_le (κ : Kernel T (G × G)) (η : Kernel T G) [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) [IsProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    (Kernel.entropy (map κ (fun p : G × G ↦ p.1 - p.2)) μ)
      ≤ (Kernel.entropy (map ((fst κ) ×ₖ η) (fun p : G × G ↦ p.1 - p.2)) μ)
        + (Kernel.entropy (map (η ×ₖ (snd κ)) (fun p : G × G ↦ p.1 - p.2)) μ)
        - (Kernel.entropy η μ) := by
  have hκη := hκ.prod hη
  have h1 : (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2)))) μ)
        + (Kernel.entropy (map κ (fun p ↦ p.1 - p.2)) μ)
      ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2))) μ)
        + (Kernel.entropy (map κ (fun p ↦ (p.2, p.1 - p.2))) μ) := by
    have h := entropy_triple_add_entropy_le
      (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2)))) μ
    simp only [snd_map_prod _ .of_discrete] at h
    rw [deleteMiddle_map_prod _ .of_discrete] at h
    have : map (κ ×ₖ η) (fun x ↦ x.1.1 - x.1.2)
        = map κ (fun p ↦ p.1 - p.2) := by
      have : (fun x : (G × G) × G ↦ x.1.1 - x.1.2)
        = (fun x ↦ x.1 - x.2) ∘ Prod.fst := by ext1 y; simp
      rw [this, ← map_map _ (by fun_prop) (by fun_prop), ← Kernel.fst_eq, fst_prod]
    rw [this] at h
    refine (h ?_).trans_eq ?_
    · apply FiniteKernelSupport.aefiniteKernelSupport
      apply FiniteKernelSupport.map
      exact hκ.prod hη
    congr 2
    have : (fun x : (G × G) × G ↦ (x.1.2, x.1.1 - x.1.2))
      = (fun x ↦ (x.2, x.1 - x.2)) ∘ Prod.fst := by ext1 y; simp
    rw [this, ← map_map _ (by fun_prop) (by fun_prop), ← Kernel.fst_eq, fst_prod]
  have h2 : (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2))) μ)
      ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ)
        + (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ) := by
    calc (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.1 - p.1.2))) μ)
      ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2))) μ) := by
          have : (fun p : (G × G) × G ↦ (p.1.1 - p.2, p.1.1 - p.1.2))
            = (fun p ↦ (p.1, p.1 - p.2)) ∘ (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2)) := by ext1; simp
          rw [this, ← map_map _ (by fun_prop) (by fun_prop)]
          apply entropy_map_le _ _
          apply FiniteKernelSupport.aefiniteKernelSupport
          apply hκη.map
    _ ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ)
        + (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ) := by
          have h : 0 ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ)
              + (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ)
              - (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2))) μ) := by
            have h' := mutualInfo_nonneg (κ := map (κ ×ₖ η)
              (fun p ↦ (p.1.1 - p.2, p.1.2 - p.2))) (μ := μ) ?_
            · rwa [mutualInfo, fst_map_prod _ .of_discrete, snd_map_prod _ .of_discrete] at h'
            apply FiniteKernelSupport.aefiniteKernelSupport
            apply hκη.map
          linarith
  have h3 : (Kernel.entropy (map κ (fun p : G × G ↦ (p.2, p.1 - p.2))) μ)
      ≤ (Kernel.entropy κ μ) := by
    exact entropy_map_le _ (hκ.aefiniteKernelSupport _)
  have h4 : (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2)))) μ)
      = (Kernel.entropy (κ ×ₖ η) μ) := by
    refine entropy_of_map_eq_of_map
      (fun p : G × G × G ↦ ((p.2.2 + p.2.1, p.2.1), -p.1 + p.2.2 + p.2.1))
      (fun p : (G × G) × G ↦ (p.1.1 - p.2, (p.1.2, p.1.1 - p.1.2))) ?_ ?_ ?_
        (hκη.aefiniteKernelSupport _)
    · rw [map_map _ (by fun_prop) (by fun_prop)]
      suffices ((fun p : G × G × G ↦ ((p.2.2 + p.2.1, p.2.1), -p.1 + p.2.2 + p.2.1))
          ∘ fun p ↦ (p.1.1 - p.2, p.1.2, p.1.1 - p.1.2)) = id by
        simp_rw [this, map_id]
      ext1 p
      simp
    · rfl
    apply FiniteKernelSupport.aefiniteKernelSupport
    apply hκη.map
  have h5 : (Kernel.entropy (κ ×ₖ η) μ) = (Kernel.entropy κ μ) + (Kernel.entropy η μ) := by
    rw [entropy_prod (hκ.aefiniteKernelSupport _) (hη.aefiniteKernelSupport _)]
  rw [h4, h5] at h1
  calc (Kernel.entropy (map κ (fun p : G × G ↦ p.1 - p.2)) μ)
    ≤ (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ)
      + (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.2 - p.2)) μ) - (Kernel.entropy η μ) := by
        linarith
  _ = (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.1.1 - p.2)) μ)
      + (Kernel.entropy (map (κ ×ₖ η) (fun p ↦ p.2 - p.1.2)) μ) - (Kernel.entropy η μ) := by
        congr 2
        rw [← entropy_neg, map_map _ (by fun_prop) (by fun_prop)]
        congr with p
        simp
  _ = (Kernel.entropy (map ((fst κ) ×ₖ η) (fun p : G × G ↦ p.1 - p.2)) μ)
      + (Kernel.entropy (map (η ×ₖ (snd κ)) (fun p : G × G ↦ p.1 - p.2)) μ)
      - (Kernel.entropy η μ) := by
        congr 3
        · ext x s hs
          rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs,
            prod_apply', prod_apply', lintegral_fst]
          · congr with x
          · exact .of_discrete
          · exact measurable_sub hs
          · exact .of_discrete
        · exact ruzsa_triangle_aux κ η

end

variable [MeasurableSingletonClass T] [MeasurableSingletonClass T'] [MeasurableSingletonClass T'']
variable [MeasurableSingletonClass G] [Countable G]

lemma rdist_triangle_aux1 (κ : Kernel T G) (η : Kernel T' G)
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (μ : Measure T) (μ' : Measure T') (μ'' : Measure T'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ'']
    [FiniteSupport μ] [FiniteSupport μ'] [FiniteSupport μ''] :
    (Kernel.entropy (map (prodMkRight T' (prodMkRight T'' κ) ×ₖ prodMkLeft (T × T'') η)
          (fun p ↦ p.1 - p.2)) ((μ.prod μ'').prod μ'))
      = (Kernel.entropy (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ'))
 := by
  have hAB : ∀ᵐ x ∂(μ.prod μ'), x ∈ ((μ.pfrSupport ×ˢ μ'.pfrSupport : Finset (T × T')) : Set (T × T')) :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support μ')
  have hAC : (μ.prod μ'') ((μ.pfrSupport ×ˢ μ''.pfrSupport : Finset (T × T'')) : Set (T × T''))ᶜ = 0 :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support μ'')
  have hACB : ∀ᵐ x ∂(μ.prod μ'').prod μ', x ∈
      (((μ.pfrSupport ×ˢ μ''.pfrSupport) ×ˢ μ'.pfrSupport : Finset ((T × T'') × T')) : Set ((T × T'') × T'))
        := Measure.prod_of_full_measure_finset hAC (measure_compl_support μ')
  simp_rw [entropy, integral_eq_setIntegral hAB, integral_eq_setIntegral hACB,
    setIntegral_finset _ .finset, smul_eq_mul, Measure.prod_real_singleton, Finset.sum_product,
    mul_assoc, ← Finset.mul_sum]
  congr with x
  have : ∀ z y, map (prodMkRight T' (prodMkRight T'' κ) ×ₖ prodMkLeft (T × T'') η)
        (fun p ↦ p.1 - p.2) ((x, z), y)
      = map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun p ↦ p.1 - p.2) (x, y) := by
    intro z y
    ext s hs
    rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs, prod_apply, prod_apply]
    simp
  simp_rw [this, ← Finset.sum_mul, sum_measureReal_singleton, Measure.real,
    measure_of_measure_compl_eq_zero (measure_compl_support μ'')]
  simp

lemma rdist_triangle_aux2 (η : Kernel T' G) (ξ : Kernel T'' G)
    [IsMarkovKernel η] [IsMarkovKernel ξ]
    (μ : Measure T) (μ' : Measure T') (μ'' : Measure T'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ'']
    [FiniteSupport μ] [FiniteSupport μ'] [FiniteSupport μ''] :
    (Kernel.entropy (map (prodMkLeft (T × T'') η ×ₖ prodMkRight T' (prodMkLeft T ξ))
      (fun p ↦ p.1 - p.2)) ((μ.prod μ'').prod μ'))
    = (Kernel.entropy (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ'')) := by
  have hBC :
      ∀ᵐ x ∂(μ'.prod μ''), x ∈ ((μ'.pfrSupport ×ˢ μ''.pfrSupport : Finset (T' × T'')):Set (T' × T'')) :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ') (measure_compl_support μ'')
  have hAC: (μ.prod μ'') ((μ.pfrSupport ×ˢ μ''.pfrSupport : Finset (T × T'')):Set (T × T''))ᶜ = 0 :=
    Measure.prod_of_full_measure_finset (measure_compl_support μ) (measure_compl_support μ'')
  have hACB : ∀ᵐ x ∂(μ.prod μ'').prod μ', x ∈
      (((μ.pfrSupport ×ˢ μ''.pfrSupport) ×ˢ μ'.pfrSupport : Finset ((T × T'') × T')) : Set ((T × T'') × T'))
    := Measure.prod_of_full_measure_finset hAC (measure_compl_support μ')
  simp_rw [entropy, integral_eq_setIntegral hACB, integral_eq_setIntegral hBC,
    setIntegral_finset _ .finset, smul_eq_mul, Measure.prod_real_singleton]
  conv_rhs => rw [Finset.sum_product_right]
  conv_lhs => rw [Finset.sum_product, Finset.sum_product_right]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr with z
  have : ∀ x y, map (prodMkLeft (T × T'') η ×ₖ prodMkRight T' (prodMkLeft T ξ))
        (fun p ↦ p.1 - p.2) ((x, z), y)
      = map (prodMkLeft T'' η ×ₖ prodMkRight T' ξ) (fun p ↦ p.1 - p.2) (z, y) := by
    intro x y
    ext s hs
    rw [map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ hs, prod_apply, prod_apply]
    simp
  simp_rw [this, ← Finset.sum_mul, sum_measureReal_singleton, Measure.real,
    measure_of_measure_compl_eq_zero (measure_compl_support μ),
    measure_univ, ENNReal.toReal_one, one_mul, ← mul_assoc, mul_comm _ (μ'' {z}).toReal, mul_assoc,
    ← Finset.mul_sum]
  congr with y
  congr 2 with s _hs
  rw [map_apply _ (by fun_prop), map_apply _ (by fun_prop), prod_apply, prod_apply]
  simp

variable [Countable T] [Countable T'] [Countable T'']

lemma rdist_triangle (κ : Kernel T G) (η : Kernel T' G) (ξ : Kernel T'' G)
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsMarkovKernel ξ]
    (μ : Measure T) (μ' : Measure T') (μ'' : Measure T'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ'']
    [FiniteSupport μ] [FiniteSupport μ'] [FiniteSupport μ'']
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) (hξ : FiniteKernelSupport ξ) :
    (Kernel.rdist κ ξ μ μ'') ≤ (Kernel.rdist κ η μ μ') + (Kernel.rdist η ξ μ' μ'') := by
  rw [rdist_eq', rdist_eq', rdist_eq']
  have h := ent_of_diff_le (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ))
    (prodMkLeft (T × T'') η) ((μ.prod μ'').prod μ') ?_ ?_
  rotate_left
  · apply FiniteKernelSupport.prodMkRight
    apply hκ.prodMkRight.prod hξ.prodMkLeft
  · apply Kernel.FiniteKernelSupport.prodMkLeft hη
  have h1 : (Kernel.entropy (map (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ)) (fun p ↦ p.1 - p.2)) ((μ.prod μ'').prod μ'))

      = (Kernel.entropy (map (prodMkRight T'' κ ×ₖ prodMkLeft T ξ) (fun x ↦ x.1 - x.2)) (μ.prod μ'')) := by
    rw [map_prodMkRight, entropy_prodMkRight']
  have h2 :
      (Kernel.entropy (map (fst (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ)) ×ₖ prodMkLeft (T × T'') η)
          (fun p ↦ p.1 - p.2)) ((μ.prod μ'').prod μ'))
      = (Kernel.entropy (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ')) := by
    rw [fst_prodMkRight, fst_prod]
    exact rdist_triangle_aux1 _ _ _ _ _
  have h3 :
      (Kernel.entropy (map (prodMkLeft (T × T'') η ×ₖ snd (prodMkRight T' (prodMkRight T'' κ ×ₖ prodMkLeft T ξ)))
        (fun p ↦ p.1 - p.2)) ((μ.prod μ'').prod μ'))
      = (Kernel.entropy (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ'')) := by
    rw [snd_prodMkRight, snd_prod]
    exact rdist_triangle_aux2 _ _ _ _ _
  have h4 : (Kernel.entropy (prodMkLeft (T × T'') η) ((μ.prod μ'').prod μ')) = (Kernel.entropy η μ') := entropy_prodMkLeft
  rw [h1, h2, h3, h4] at h
  calc (Kernel.entropy (map (prodMkRight T'' κ ×ₖ prodMkLeft T ξ) (fun x ↦ x.1 - x.2)) (μ.prod μ''))
      - (Kernel.entropy κ μ) / 2 - (Kernel.entropy ξ μ'') / 2
    ≤ (Kernel.entropy (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ'))
      + (Kernel.entropy (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ''))

      - (Kernel.entropy η μ') - (Kernel.entropy κ μ) / 2 - (Kernel.entropy ξ μ'') / 2 := by gcongr
  _ = (Kernel.entropy (map (prodMkRight T' κ ×ₖ prodMkLeft T η) (fun x ↦ x.1 - x.2)) (μ.prod μ'))
      - (Kernel.entropy κ μ) / 2 - (Kernel.entropy η μ') / 2
      + ((Kernel.entropy (map (prodMkRight T'' η ×ₖ prodMkLeft T' ξ) (fun x ↦ x.1 - x.2)) (μ'.prod μ''))
      - (Kernel.entropy η μ') / 2 - (Kernel.entropy ξ μ'') / 2) := by ring

end ProbabilityTheory.Kernel
end

/- PFR.ForMathlib.FiniteRange.IdentDistrib -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal

namespace ProbabilityTheory
section IdentDistrib
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω → β}
  {f' g' : Ω' → β}

lemma identDistrib_of_finiteRange {Ω Ω₀ S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace S] [MeasurableSingletonClass S]
    [hS : Nonempty S] {μ : Measure Ω} {μ₀ : Measure Ω₀} {X₀ : Ω₀ → S} [FiniteRange X₀] {X : Ω → S}
    (hX : Measurable X) (hi : IdentDistrib X₀ X μ₀ μ) :
    ∃ X' : Ω → S, Measurable X' ∧ FiniteRange X' ∧ X' =ᵐ[μ] X := by
  set A := FiniteRange.toFinset X₀
  classical
  let X' (ω : Ω) : S := if (X ω ∈ A) then X ω else hS.some
  refine ⟨X', ?_, ?_, ?_⟩
  · exact .ite (.preimage (Finset.measurableSet A) hX) hX measurable_const
  · apply finiteRange_of_finset X' (A ∪ {hS.some})
    intro ω
    simp [X']
    split <;> simp [*]
  apply Filter.eventuallyEq_of_mem (s := X ⁻¹' A)
  · rw [mem_ae_iff, ← Set.preimage_compl, ← IdentDistrib.measure_preimage_eq hi]
    · convert measure_empty (μ := μ₀)
      ext ω
      simp [A]
    measurability
  intro ω
  simp only [mem_preimage, Finset.mem_coe, ite_eq_left_iff, X']
  tauto

lemma independent_copies_finiteRange {X : Ω → α} {Y : Ω' → β}
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    ∃ ν : Measure (α × β), ∃ X' : α × β → α, ∃
    Y' : α × β → β, IsProbabilityMeasure ν
      ∧ Measurable X' ∧ Measurable Y' ∧ IndepFun X' Y' ν
      ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' ∧ FiniteRange X' ∧ FiniteRange Y' := by
  have : Nonempty α := μ.nonempty_of_neZero.map X
  have : Nonempty β := μ'.nonempty_of_neZero.map Y
  obtain ⟨ν, X', Y', hν, hX', hY', hind, hIdX, hIdY⟩ := independent_copies hX hY μ μ'
  rcases identDistrib_of_finiteRange hX' hIdX.symm with ⟨X'', hX'', hX''_finite, hX''_eq⟩
  rcases identDistrib_of_finiteRange hY' hIdY.symm with ⟨Y'', hY'', hY''_finite, hY''_eq⟩
  use ν, X'', Y''
  refine ⟨hν, hX'', hY'', ?_, ?_, ?_, hX''_finite, hY''_finite⟩
  · exact hind.congr hX''_eq.symm hY''_eq.symm
  · convert IdentDistrib.trans _ hIdX
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX'') hX''_eq
  · convert IdentDistrib.trans _ hIdY
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hY'') hY''_eq

lemma independent_copies3_nondep_finiteRange {α : Type u}
    [mS : MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    [FiniteRange X₁] [FiniteRange X₂] [FiniteRange X₃]
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂]
    [hμ₃ : IsProbabilityMeasure μ₃] :
    ∃ (A : Type (max u_1 u_2 u_3)) (_ : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' : A → α),
    IsProbabilityMeasure μA ∧
    iIndepFun ![X₁', X₂', X₃'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ ∧
      FiniteRange X₁' ∧ FiniteRange X₂' ∧ FiniteRange X₃' := by
    have : Nonempty α := μ₁.nonempty_of_neZero.map X₁
    obtain ⟨A, mA, μA, X₁', X₂', X₃', hμA, hind, hX₁, hX₂, hX₃, hId₁, hId₂, hId₃⟩ :=
      independent_copies3_nondep hX₁ hX₂ hX₃ μ₁ μ₂ μ₃
    rcases identDistrib_of_finiteRange hX₁ hId₁.symm with ⟨X₁'', hX₁'', hX₁''_finite, hX₁''_eq⟩
    rcases identDistrib_of_finiteRange hX₂ hId₂.symm with ⟨X₂'', hX₂'', hX₂''_finite, hX₂''_eq⟩
    rcases identDistrib_of_finiteRange hX₃ hId₃.symm with ⟨X₃'', hX₃'', hX₃''_finite, hX₃''_eq⟩
    use A, mA, μA, X₁'', X₂'', X₃''
    refine ⟨hμA, ?_, hX₁'', hX₂'', hX₃'', ?_, ?_, ?_, hX₁''_finite, hX₂''_finite, hX₃''_finite⟩
    · apply iIndepFun.ae_eq hind
      intro i; fin_cases i
      all_goals simp [hX₁''_eq.symm, hX₂''_eq.symm, hX₃''_eq.symm]
    · convert IdentDistrib.trans _ hId₁
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₁'') hX₁''_eq
    · convert IdentDistrib.trans _ hId₂
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₂'') hX₂''_eq
    convert IdentDistrib.trans _ hId₃
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₃'') hX₃''_eq

end IdentDistrib
end ProbabilityTheory
end

/- PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityMeasure Topology Metric Filter Set ENNReal NNReal
open scoped BoundedContinuousFunction Topology ENNReal NNReal

instance {Y : Type*} [MeasurableSpace Y] :
    CanLift (Measure Y) (ProbabilityMeasure Y) (↑) IsProbabilityMeasure where
  prf μ h := ⟨⟨μ, h⟩, rfl⟩

instance {Y : Type*} [MeasurableSpace Y] :
    CanLift (Measure Y) (FiniteMeasure Y) (↑) IsFiniteMeasure where
  prf μ h := ⟨⟨μ, h⟩, rfl⟩

variable {ι X : Type*} [MeasurableSpace X] [TopologicalSpace X]

lemma continuous_probabilityMeasure_apply_of_isClopen [OpensMeasurableSpace X]
    {s : Set X} (s_clopen : IsClopen s) :
    Continuous fun μ : ProbabilityMeasure X ↦ (μ : Measure X).real s := by
  convert ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.indicator s s_clopen)
  have s_mble : MeasurableSet s := s_clopen.isOpen.measurableSet
  simp [integral_indicator, s_mble, Measure.real]

variable [DiscreteTopology X] [BorelSpace X]

lemma continuous_pmf_apply' (i : X) :
    Continuous fun μ : ProbabilityMeasure X ↦ (μ : Measure X).real {i} :=
  continuous_probabilityMeasure_apply_of_isClopen (s := {i}) <| isClopen_discrete _

lemma continuous_pmf_apply (i : X) : Continuous fun μ : ProbabilityMeasure X ↦ μ {i} := by
  
  convert continuous_real_toNNReal.comp (continuous_pmf_apply' i)
  ext
  simp [Measure.real, Function.comp_apply]
  rfl

open Filter in
lemma tendsto_lintegral_of_forall_of_finite [Finite X] {L : Filter ι} (μs : ι → Measure X)
    (μ : Measure X) (f : X →ᵇ ℝ≥0) (h : ∀ x, Tendsto (fun i ↦ μs i {x}) L (𝓝 (μ {x}))) :
    Tendsto (fun i ↦ ∫⁻ x, f x ∂(μs i)) L (𝓝 (∫⁻ x, f x ∂μ)) := by
  cases nonempty_fintype X
  simp only [lintegral_fintype]
  refine tendsto_finsetSum Finset.univ ?_
  exact fun x _ ↦ ENNReal.Tendsto.const_mul (h x) (Or.inr ENNReal.coe_ne_top)

lemma ProbabilityMeasure.tendsto_iff_forall_apply_tendsto {L : Filter ι} [Finite X]
    (μs : ι → ProbabilityMeasure X) (μ : ProbabilityMeasure X) :
    Tendsto μs L (𝓝 μ) ↔ ∀ a, Tendsto (μs · {a}) L (𝓝 (μ {a})) := by
  constructor <;> intro h
  · exact fun a ↦ ((continuous_pmf_apply a).continuousAt (x := μ)).tendsto.comp h
  · apply ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
    intro f
    apply tendsto_lintegral_of_forall_of_finite
    intro a
    
    convert ENNReal.continuous_coe.continuousAt.tendsto.comp (h a)
    · simp [Function.comp_apply, ennreal_coeFn_eq_coeFn_toMeasure]
    · simp [ennreal_coeFn_eq_coeFn_toMeasure]

end

/- PFR.ForMathlib.Entropy.RuzsaDist -/
noncomputable section
open scoped ProbabilityTheory
open Filter Function MeasureTheory Measure ProbabilityTheory
open scoped Topology

variable {Ω Ω' Ω'' Ω''' G S T : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G]

lemma continuous_measureEntropy_probabilityMeasure {Ω : Type*} [Finite Ω]
    [TopologicalSpace Ω] [DiscreteTopology Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] :
    Continuous (fun (μ : ProbabilityMeasure Ω) ↦ measureEntropy (S := Ω) μ) := by
  cases nonempty_fintype Ω
  unfold measureEntropy
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro ω _
  apply Real.continuous_negMulLog.comp
  simp only [measure_univ, inv_one, one_smul]
  exact continuous_probabilityMeasure_apply_of_isClopen (s := {ω}) <| isClopen_discrete _

variable [AddCommGroup G]
  {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}

noncomputable
def rdist (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  (ProbabilityTheory.entropy (fun x ↦ x.1 - x.2) ((μ.map X).prod (μ'.map Y))) - (ProbabilityTheory.entropy X μ)/2 - (ProbabilityTheory.entropy Y μ')/2

lemma rdist_def (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω) (μ' : Measure Ω') :
    (rdist X Y μ μ')
      = (ProbabilityTheory.entropy (fun x ↦ x.1 - x.2) ((μ.map X).prod (μ'.map Y))) - (ProbabilityTheory.entropy X μ)/2 - (ProbabilityTheory.entropy Y μ')/2 := rfl

lemma rdist_eq_rdistm : (rdist X Y μ μ') = Kernel.rdistm (μ.map X) (μ'.map Y) := rfl

lemma continuous_rdist_restrict_probabilityMeasure [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] :
    Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦
        (rdist id id μ.1.toMeasure μ.2.toMeasure)) := by
  simp [rdist_def]
  have obs₀ : Continuous (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦
      (ProbabilityTheory.entropy (fun x ↦ x.1 - x.2) (μ.1.toMeasure.prod μ.2.toMeasure))) := by
    simp_rw [entropy_def]
    have diff_cts : Continuous (fun (x : G × G) ↦ x.1 - x.2) := by continuity
    have key₁ := ProbabilityMeasure.continuous_prod (α := G) (β := G)
    have key₂ := ProbabilityMeasure.continuous_map diff_cts
    convert! continuous_measureEntropy_probabilityMeasure.comp (key₂.comp key₁)
  have obs₁ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ (ProbabilityTheory.entropy id μ.1.toMeasure)) := by
    convert (continuous_measureEntropy_probabilityMeasure (Ω := G)).comp continuous_fst
    simp [entropy_def]
  have obs₂ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ (ProbabilityTheory.entropy id μ.2.toMeasure)) := by
    convert (continuous_measureEntropy_probabilityMeasure (Ω := G)).comp continuous_snd
    simp [entropy_def]
  continuity

lemma continuous_rdist_restrict_probabilityMeasure₁ [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ (rdist id id (P.map X) μ.toMeasure)) := by
  have obs : IsProbabilityMeasure (P.map X) := by
    refine ⟨by simp [Measure.map_apply X_mble MeasurableSet.univ]⟩
  let ι : ProbabilityMeasure G → ProbabilityMeasure G × ProbabilityMeasure G :=
      fun ν ↦ ⟨⟨P.map X, obs⟩, ν⟩
  have ι_cont : Continuous ι := Continuous.prodMk_right _
  convert! continuous_rdist_restrict_probabilityMeasure.comp ι_cont

lemma rdist_eq_rdist_id_map : (rdist X Y μ μ') = (rdist id id (μ.map X) (μ'.map Y)) := by
  simp only [rdist_def, entropy_def, Measure.map_id]

lemma continuous_rdist_restrict_probabilityMeasure₁' [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ (rdist X id P μ.toMeasure)) := by
  simp only [@rdist_eq_rdist_id_map Ω G G mΩ P hG, Measure.map_id]
  exact continuous_rdist_restrict_probabilityMeasure₁ _ _ X_mble

lemma ProbabilityTheory.IdentDistrib.rdist_congr {X' : Ω'' → G} {Y' : Ω''' → G}
    (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
    (rdist X Y μ μ') = (rdist X' Y' μ'' μ''') := by
  simp [rdist, hX.map_eq, hY.map_eq, hX.entropy_congr, hY.entropy_congr]

lemma ProbabilityTheory.IdentDistrib.rdist_congr_left {X' : Ω'' → G}
    (hY : AEMeasurable Y μ') (hX : IdentDistrib X X' μ μ'') :
    (rdist X Y μ μ') = (rdist X' Y μ'' μ') := hX.rdist_congr <| .refl hY

lemma ProbabilityTheory.IdentDistrib.rdist_congr_right {Y' : Ω''' → G}
    (hX : AEMeasurable X μ) (hY : IdentDistrib Y Y' μ' μ''') :
    (rdist X Y μ μ') = (rdist X Y' μ μ''') := (IdentDistrib.refl hX).rdist_congr hY

section rdist

variable [Countable G] [MeasurableSingletonClass G]

lemma ProbabilityTheory.IndepFun.rdist_eq [IsFiniteMeasure μ]
    {Y : Ω → G} (h : IndepFun X Y μ) (hX : Measurable X) (hY : Measurable Y) :
    (rdist X Y μ μ) = (ProbabilityTheory.entropy (X - Y) μ) - (ProbabilityTheory.entropy X μ)/2 - (ProbabilityTheory.entropy Y μ)/2 := by
  rw [rdist_def]
  congr 2
  have h_prod : (μ.map X).prod (μ.map Y) = μ.map ((_root_.prod X Y)) :=
    ((indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp h).symm
  rw [h_prod, entropy_def, map_map (by fun_prop) (by fun_prop)]
  rfl

lemma rdist_symm [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    (rdist X Y μ μ') = (rdist Y X μ' μ) := by
  rw [rdist_def, rdist_def, sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_neg (by fun_prop)]
  have : (-fun x : G × G ↦ x.1 - x.2) = (fun x ↦ x.1 - x.2) ∘ Prod.swap := by ext ; simp
  rw [this, entropy_def, ← map_map (by fun_prop) measurable_swap, prod_swap]
  rfl

omit [Countable G] in

lemma continuous_rdist_restrict_probabilityMeasure₁_left [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ (rdist id X μ.toMeasure P)) := by
  convert continuous_rdist_restrict_probabilityMeasure₁' X P X_mble using 2
  rw [rdist_symm]

variable [FiniteRange X] [FiniteRange Y]

lemma diff_ent_le_rdist [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) :
    |(ProbabilityTheory.entropy X μ) - (ProbabilityTheory.entropy Y μ')| ≤ 2 * (rdist X Y μ μ') := by
  obtain ⟨ν, X', Y', _, hX', hY', hind, hIdX, hIdY, _, _⟩ :=
    independent_copies_finiteRange hX hY μ μ'
  rw [← hIdX.rdist_congr hIdY, hind.rdist_eq hX' hY', ← hIdX.entropy_congr, ← hIdY.entropy_congr,
    abs_le]
  have := max_entropy_le_entropy_sub hX' hY' hind
  constructor
  · linarith[le_max_right (ProbabilityTheory.entropy X' ν) (ProbabilityTheory.entropy Y' ν)]
  · linarith[le_max_left (ProbabilityTheory.entropy X' ν) (ProbabilityTheory.entropy Y' ν)]

lemma rdist_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) : 0 ≤ (rdist X Y μ μ') := by
  linarith [ge_trans (diff_ent_le_rdist hX hY) (abs_nonneg ((ProbabilityTheory.entropy X μ) - (ProbabilityTheory.entropy Y μ')))]

lemma rdist_add_const [IsZeroOrProbabilityMeasure μ] [IsZeroOrProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) {c} :
    (rdist X (Y + fun _ ↦ c) μ μ') = (rdist X Y μ μ') := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [rdist_def, entropy_add_const hY]
  rcases eq_zero_or_isProbabilityMeasure μ' with rfl | hμ'
  · simp [rdist_def]
  obtain ⟨ν, X', Y', _, hX', hY', hind, hIdX, hIdY, -⟩ := independent_copies_finiteRange hX hY μ μ'
  have A : IdentDistrib (Y' + fun _ ↦ c) (Y + fun _ ↦ c) ν μ' := by
    change IdentDistrib (fun ω ↦ Y' ω + c) (fun ω ↦ Y ω + c) ν μ'
    apply hIdY.comp (measurable_add_const c)
  have B : IndepFun X' (Y' + fun _ ↦ c) ν := by
    change IndepFun X' (fun ω ↦ Y' ω + c) ν
    apply hind.comp measurable_id (measurable_add_const c)
  have C : X' - (Y' + fun _ ↦ c) = (X' - Y') + (fun _ ↦ -c) := by
    ext ω; simp; abel
  rw [← hIdX.rdist_congr hIdY, ← hIdX.rdist_congr A, hind.rdist_eq hX' hY',
    B.rdist_eq hX' (hY'.add_const _), entropy_add_const hY' c, C, entropy_add_const]
  exact hX'.sub hY'

lemma ent_of_diff_le (X : Ω → G) (Y : Ω → G) (Z : Ω → G)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun ((_root_.prod X Y)) Z μ)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    (ProbabilityTheory.entropy (X - Y) μ) ≤ (ProbabilityTheory.entropy (X - Z) μ) + (ProbabilityTheory.entropy (Z - Y) μ) - (ProbabilityTheory.entropy Z μ) := by
  have h1 : (ProbabilityTheory.entropy ((_root_.prod (X - Z) ((_root_.prod Y (X - Y))))) μ) + (ProbabilityTheory.entropy (X - Y) μ) ≤ (ProbabilityTheory.entropy ((_root_.prod (X - Z) (X - Y))) μ) + (ProbabilityTheory.entropy ((_root_.prod Y (X - Y))) μ) :=
    entropy_triple_add_entropy_le μ (hX.sub hZ) hY (hX.sub hY)
  have h2 : (ProbabilityTheory.entropy ((_root_.prod (X - Z) (X - Y))) μ) ≤ (ProbabilityTheory.entropy (X - Z) μ) + (ProbabilityTheory.entropy (Y - Z) μ) := by
    calc (ProbabilityTheory.entropy ((_root_.prod (X - Z) (X - Y))) μ) ≤ (ProbabilityTheory.entropy ((_root_.prod (X - Z) (Y - Z))) μ) := by
          have : (_root_.prod (X - Z) (X - Y)) = (fun p ↦ (p.1, p.1 - p.2)) ∘ (_root_.prod (X - Z) (Y - Z)) := by ext1; simp
          rw [this]
          apply entropy_comp_le μ (by fun_prop)
    _ ≤ (ProbabilityTheory.entropy (X - Z) μ) + (ProbabilityTheory.entropy (Y - Z) μ) := by
          have h : 0 ≤ (ProbabilityTheory.entropy (X - Z) μ) + (ProbabilityTheory.entropy (Y - Z) μ) - (ProbabilityTheory.entropy ((_root_.prod (X - Z) (Y - Z))) μ) := by
            apply mutualInfo_nonneg (by fun_prop) (by fun_prop) μ
          linarith
  have h3 : (ProbabilityTheory.entropy ((_root_.prod Y (X - Y))) μ) ≤ (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) := by
    have : (_root_.prod Y (X - Y)) = (fun p ↦ (p.2, p.1 - p.2)) ∘ (_root_.prod X Y) := by ext1; simp
    rw [this]
    exact entropy_comp_le μ (hX.prodMk hY) _
  have h4 : (ProbabilityTheory.entropy ((_root_.prod (X - Z) ((_root_.prod Y (X - Y))))) μ) = (ProbabilityTheory.entropy ((_root_.prod X ((_root_.prod Y Z)))) μ) := by
    refine entropy_of_comp_eq_of_comp μ ((hX.sub hZ).prodMk (hY.prodMk (hX.sub hY)))
      (hX.prodMk (hY.prodMk hZ))
      (fun p : G × (G × G) ↦ (p.2.2 + p.2.1, p.2.1, -p.1 + p.2.2 + p.2.1))
      (fun p : G × G × G ↦ (p.1 - p.2.2, p.2.1, p.1 - p.2.1)) ?_ ?_
    · ext1; simp
    · ext1; simp
  have h5 : (ProbabilityTheory.entropy ((_root_.prod X ((_root_.prod Y Z)))) μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) + (ProbabilityTheory.entropy Z μ) := by
    rw [entropy_assoc hX hY hZ, entropy_pair_eq_add (hX.prodMk hY) hZ]
    exact h
  rw [h4, h5] at h1
  calc (ProbabilityTheory.entropy (X - Y) μ) ≤ (ProbabilityTheory.entropy (X - Z) μ) + (ProbabilityTheory.entropy (Y - Z) μ) - (ProbabilityTheory.entropy Z μ) := by linarith
  _ = (ProbabilityTheory.entropy (X - Z) μ) + (ProbabilityTheory.entropy (Z - Y) μ) - (ProbabilityTheory.entropy Z μ) := by
    congr 2
    rw [entropy_sub_comm hY hZ]

lemma rdist_triangle {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [hμ : IsProbabilityMeasure μ] [hμ' : IsProbabilityMeasure μ']
    [hμ'' : IsProbabilityMeasure μ''] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    (rdist X Z μ μ'') ≤ (rdist X Y μ μ') + (rdist Y Z μ' μ'') := by
  obtain ⟨A, mA, μA, X', Y', Z', hμA, hInd, hX', hY', hZ', HX, HY, HZ, _, _, _⟩ :=
    independent_copies3_nondep_finiteRange hX hY hZ μ μ' μ''
  suffices (rdist X' Z' μA μA) ≤ (rdist X' Y' μA μA) + (rdist Y' Z' μA μA) by
    rwa [HX.rdist_congr HY, HY.rdist_congr HZ, HX.rdist_congr HZ] at this
  have IndepLem : IndepFun ((_root_.prod X' Z')) Y' μA :=
    iIndepFun.indepFun_prodMk hInd (fun i => by fin_cases i ; all_goals { simpa }) 0 2 1
      (by norm_cast) (by norm_cast)
  calc (rdist X' Z' μA μA) = (ProbabilityTheory.entropy (X' - Z') μA) - ((ProbabilityTheory.entropy X' μA) / 2 + (ProbabilityTheory.entropy Z' μA) / 2) := by
        rw [ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using hInd.indepFun (show 0 ≠ 2 by norm_cast)) hX' hZ'] ; ring
    _ ≤ ((ProbabilityTheory.entropy (X' - Y') μA) + (ProbabilityTheory.entropy (Y' - Z') μA) - (ProbabilityTheory.entropy Y' μA)) - ((ProbabilityTheory.entropy X' μA) / 2 + (ProbabilityTheory.entropy Z' μA) / 2) :=
          sub_le_sub_right (ent_of_diff_le _ _ _ hX' hZ' hY' IndepLem) _
    _ = ((ProbabilityTheory.entropy (X' - Y') μA) - (ProbabilityTheory.entropy X' μA) / 2 - (ProbabilityTheory.entropy Y' μA) / 2) +
          ((ProbabilityTheory.entropy (Y' - Z') μA) - (ProbabilityTheory.entropy Y' μA) / 2 - (ProbabilityTheory.entropy Z' μA) / 2) := by ring
    _ = (rdist X' Y' μA μA) + (rdist Y' Z' μA μA) := by
        rw [ProbabilityTheory.IndepFun.rdist_eq (by simpa using (iIndepFun.indepFun hInd
          (show 0 ≠ 1 by norm_cast))) hX' hY', ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using (iIndepFun.indepFun hInd (show 1 ≠ 2 by norm_cast))) hY' hZ']

end rdist

variable [MeasurableSpace S] [MeasurableSpace T] [Countable G] [MeasurableSingletonClass G]

noncomputable
def condRuzsaDist (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ]
    (μ' : Measure Ω' := by volume_tac) [IsFiniteMeasure μ'] : ℝ :=
  (Kernel.rdist (condDistrib X Z μ) (condDistrib Y W μ') (μ.map Z) (μ'.map W))

lemma condRuzsaDist_def (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω) [IsFiniteMeasure μ] (μ' : Measure Ω') [IsFiniteMeasure μ'] :
    (condRuzsaDist X Z Y W μ μ')
      = (Kernel.rdist (condDistrib X Z μ) (condDistrib Y W μ') (μ.map Z) (μ'.map W)) := rfl

@[simp] lemma condRuszaDist_zero_right (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    (condRuzsaDist X Z Y W μ 0) = 0 := by
  simp only [condRuzsaDist, Measure.map_zero, Kernel.rdist_zero_right]

@[simp] lemma condRuszaDist_zero_left (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ' : Measure Ω') [IsFiniteMeasure μ'] :
    (condRuzsaDist X Z Y W 0 μ') = 0 := by
  simp [condRuzsaDist]

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

lemma condRuzsaDist_eq_sum {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsFiniteMeasure μ] (μ' : Measure Ω') [IsFiniteMeasure μ']
    [FiniteRange Z] [FiniteRange W] :
    (condRuzsaDist X Z Y W μ μ')
      = ∑ z ∈ FiniteRange.toFinset Z, ∑ w ∈ FiniteRange.toFinset W,
        μ.real (Z ⁻¹' {z}) * μ'.real (W ⁻¹' {w})
          * (rdist X Y ((μ[|Z ← z])) ((μ'[|W ← w]))) := by
  have : ∀ᵐ x ∂Measure.prod (μ.map Z) (μ'.map W), x ∈
    ((((FiniteRange.toFinset Z) ×ˢ (FiniteRange.toFinset W)) : Finset (S × T)): Set (S × T)) := by
    apply Measure.prod_of_full_measure_finset
    all_goals {
      rw [Measure.map_apply ‹_›]
      convert measure_empty (μ := μ)
      simp [← FiniteRange.range]
      measurability
    }
  rw [condRuzsaDist_def, Kernel.rdist, integral_eq_setIntegral this, setIntegral_finset _ .finset]
  simp_rw [Measure.prod_real_singleton, smul_eq_mul, Finset.sum_product,
    map_measureReal_apply hZ (.singleton _), map_measureReal_apply hW (.singleton _)]
  congr with z
  congr with w
  by_cases hz : μ.real (Z ⁻¹' {z}) = 0
  · simp only [mul_eq_mul_left_iff, mul_eq_zero]
    refine Or.inr (Or.inl ?_)
    simp [hz]
  by_cases hw : μ'.real (W ⁻¹' {w}) = 0
  · simp only [mul_eq_mul_left_iff, mul_eq_zero]
    refine Or.inr (Or.inr ?_)
    simp [hw]
  congr 1
  simp only [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top μ, or_false,
    measure_ne_top] at hz hw
  rw [rdist_eq_rdistm, condDistrib_apply hX hZ _ _ hz, condDistrib_apply hY hW _ _ hw]

variable [Countable S]

lemma condRuzsaDist_symm [Countable T]
    {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T} (hZ : Measurable Z)
    (hW : Measurable W) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [FiniteRange Z]
    [FiniteRange W] :
    (condRuzsaDist X Z Y W μ μ') = (condRuzsaDist Y W X Z μ' μ) := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ'.map W) := isProbabilityMeasure_map hW.aemeasurable
  rw [condRuzsaDist_def, condRuzsaDist_def, Kernel.rdist_symm]

lemma condRuzsaDist_nonneg [Countable T] {X : Ω → G} (hX : Measurable X) [FiniteRange X]
    {Z : Ω → S} (hZ : Measurable Z) [FiniteRange Z]
    {Y : Ω' → G} (hY : Measurable Y) [FiniteRange Y]
    {W : Ω' → T} (hW : Measurable W) [FiniteRange W]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    0 ≤ (condRuzsaDist X Z Y W μ μ') := by
  rw [condRuzsaDist_def]
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ'.map W) := isProbabilityMeasure_map hW.aemeasurable
  refine Kernel.rdist_nonneg ?_ ?_
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ hX hZ
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ hY hW

noncomputable
def condRuzsaDist' (X : Ω → G) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) [IsFiniteMeasure μ'] : ℝ :=
  (Kernel.rdist (Kernel.const Unit (μ.map X)) (condDistrib Y W μ') (Measure.dirac ()) (μ'.map W))

lemma condRuzsaDist'_def {T : Type*} [MeasurableSpace T]
    (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (μ : Measure Ω) (μ' : Measure Ω')
    [IsFiniteMeasure μ'] :
    (condRuzsaDist' X Y W μ μ') =
      (Kernel.rdist (Kernel.const Unit (μ.map X)) (condDistrib Y W μ') (Measure.dirac ()) (μ'.map W)) :=
  rfl

@[simp] lemma condRuzsaDist'_zero_right {T : Type*} [MeasurableSpace T]
    (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (μ : Measure Ω) :
    (condRuzsaDist' X Y W μ 0) = 0 := by
  simp only [condRuzsaDist'_def, Measure.map_zero, Kernel.rdist_zero_right]

lemma condRuzsaDist'_eq_sum {X : Ω → G} {Y : Ω' → G} {W : Ω' → T} (hY : Measurable Y)
    (hW : Measurable W) (μ : Measure Ω) (μ' : Measure Ω') [IsFiniteMeasure μ'] [FiniteRange W] :
    (condRuzsaDist' X Y W μ μ')
      = ∑ w ∈ FiniteRange.toFinset W, μ'.real (W ⁻¹' {w}) * (rdist X Y μ ((μ'[|W ← w]))) := by
  have : ∀ᵐ x ∂Measure.prod (dirac ()) (μ'.map W), x ∈
    ((Finset.univ (α := Unit) ×ˢ FiniteRange.toFinset W : Finset (Unit × T)) : Set (Unit × T)) := by
    apply Measure.prod_of_full_measure_finset
    · simp
    rw [Measure.map_apply ‹_› (by measurability)]
    convert measure_empty (μ := μ)
    simp [← FiniteRange.range]
  rw [condRuzsaDist'_def, Kernel.rdist, integral_eq_setIntegral this, setIntegral_finset _ .finset]
  simp_rw [Measure.prod_real_singleton, smul_eq_mul, Finset.sum_product]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  simp_rw [map_measureReal_apply hW (.singleton _)]
  congr with w
  by_cases hw : μ'.real (W ⁻¹' {w}) = 0
  · simp [hw]
  rw [rdist_eq_rdistm, condDistrib_apply hY hW _ _]
  · congr
    simp
  · intro h
    simp [h, measureReal_def] at hw

lemma condRuzsaDist'_eq_sum' {X : Ω → G} {Y : Ω' → G} {W : Ω' → T} (hY : Measurable Y)
    (hW : Measurable W) (μ : Measure Ω) (μ' : Measure Ω') [IsFiniteMeasure μ'] [Fintype T] :
    (condRuzsaDist' X Y W μ μ')
      = ∑ w, μ'.real (W ⁻¹' {w}) * (rdist X Y μ ((μ'[|W ← w]))) := by
  rw [condRuzsaDist'_eq_sum hY hW μ μ']
  apply Finset.sum_subset
  · simp
  intro w _ hw
  simp only [FiniteRange.mem_iff, not_exists] at hw
  have : W⁻¹' {w} = ∅ := by
    ext ω; simp [hw ω]
  simp [this]

open scoped ENNReal

lemma condRuzsaDist'_prod_eq_sum {X : Ω → G} {Y : Ω' → G} {W W' : Ω' → T}
    (μ : Measure Ω) (μ' : Measure Ω') (hY : Measurable Y) (hW' : Measurable W') (hW : Measurable W)
    [IsFiniteMeasure μ'] [FiniteRange W] [FiniteRange W'] :
    (condRuzsaDist' X Y ((_root_.prod W' W)) μ μ')
      = ∑ w ∈ FiniteRange.toFinset W, μ'.real (W ⁻¹' {w}) * (condRuzsaDist' X Y W' μ ((μ'[|W ← w]))) := by
  have : (condRuzsaDist' X Y ((_root_.prod W' W)) μ μ') = ∑ w ∈ ((FiniteRange.toFinset W') ×ˢ FiniteRange.toFinset W),
    μ'.real ((fun a => (W' a, W a)) ⁻¹' {w}) * (rdist X Y μ (μ'[|(fun a ↦ (W' a, W a)) ⁻¹' {w}])) := by
    rw [condRuzsaDist'_eq_sum hY (hW'.prodMk hW)]
    apply Finset.sum_subset
    · intro (t, t')
      simp only [FiniteRange.mem_iff, Prod.mk.injEq, Finset.mem_product, forall_exists_index,
        and_imp]
      exact fun ω h1 h2 ↦ ⟨⟨ω, h1⟩, ⟨ω, h2⟩⟩
    intro (t, t') _ ht
    simp only [FiniteRange.mem_iff, Prod.mk.injEq, not_exists, not_and] at ht
    have : (fun a => (W' a, W a)) ⁻¹' {(t, t')} = ∅ := by
      ext ω
      simpa using ht ω
    simp [this]
  rw [this, Finset.sum_product_right]
  congr 1 with w
  rw [condRuzsaDist'_eq_sum hY hW', Finset.mul_sum]
  congr 1 with w'
  rw [← mul_assoc]
  have A : (fun a ↦ (W' a, W a)) ⁻¹' {(w', w)} = W' ⁻¹' {w'} ∩ W⁻¹' {w} := by ext; simp
  congr 1
  · simp only [A, ProbabilityTheory.cond_real_apply (hW (.singleton w))]
    obtain hw | hw := eq_or_ne (μ'.real (W ⁻¹' {w})) 0
    · have : μ'.real (W' ⁻¹' {w'} ∩ W ⁻¹' {w}) = 0 :=
        measureReal_mono_null Set.inter_subset_right hw
      simp [hw, this]
    · rw [mul_inv_cancel_left₀ hw, Set.inter_comm]
  · congr 1
    rw [A, cond_cond_eq_cond_inter' (hW (.singleton _)) (hW' (.singleton _)), Set.inter_comm]
    finiteness

lemma condRuzsaDist'_prod_eq_sum' {X : Ω → G} {Y : Ω' → G} {W W' : Ω' → T}
    (μ : Measure Ω) (μ' : Measure Ω') (hY : Measurable Y) (hW' : Measurable W') (hW : Measurable W)
    [IsFiniteMeasure μ'] [Fintype T] :
    (condRuzsaDist' X Y ((_root_.prod W' W)) μ μ')
      = ∑ w, μ'.real (W ⁻¹' {w}) * (condRuzsaDist' X Y W' μ ((μ'[|W ← w]))) := by
  rw [condRuzsaDist'_prod_eq_sum μ μ' hY hW' hW]
  apply Finset.sum_subset
  · simp
  intro w _ hw
  simp only [FiniteRange.mem_iff, not_exists] at hw
  have : W⁻¹' {w} = ∅ := by
    ext ω; simp [hw ω]
  simp [this]

lemma condRuzsaDist'_eq_integral (X : Ω → G) {Y : Ω' → G} {W : Ω' → T}
    (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) (μ' : Measure Ω') [IsFiniteMeasure μ'] [FiniteRange W] :
    (condRuzsaDist' X Y W μ μ')
      = (μ'.map W)[fun w ↦ (rdist X Y μ ((μ'[|W ← w])))] := by
  rw [condRuzsaDist'_eq_sum hY hW]
  simp_rw [← smul_eq_mul]
  have : ∀ᵐ x ∂(μ'.map W), x ∈ (FiniteRange.toFinset W : Set T) := by
    rw [ae_map_iff (by measurability) (by exact Finset.measurableSet _)]
    simp [← FiniteRange.range]
  rw [integral_eq_setIntegral this,  setIntegral_finset _ .finset]
  simp [map_measureReal_apply hW (MeasurableSet.singleton _),]

section

variable [Countable T]

lemma condRuzsaDist_of_const {X : Ω → G} (hX : Measurable X)
    (Y : Ω' → G) (W : Ω' → T) (c : S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [FiniteRange W] :
    (condRuzsaDist X ((fun _ ↦ c)) Y W μ μ') = (condRuzsaDist' X Y W μ μ') := by
  rw [condRuzsaDist_def, condRuzsaDist'_def, Measure.map_const, measure_univ, one_smul,
    Kernel.rdist, Kernel.rdist, integral_prod _ (integrable_of_finiteSupport _), integral_dirac,
    integral_prod _ (integrable_of_finiteSupport _), integral_dirac]
  congr!
  rw [condDistrib_apply hX measurable_const] <;> simp

lemma condRuzsaDist_of_indep
    {X : Ω → G} {Z : Ω → S} {Y : Ω → G} {W : Ω → T}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun ((_root_.prod X Z)) ((_root_.prod Y W)) μ) [FiniteRange Z] [FiniteRange W] :
    (condRuzsaDist X Z Y W μ μ) = (ProbabilityTheory.condEntropy (X - Y) ((_root_.prod Z W)) μ) - (ProbabilityTheory.condEntropy X Z μ)/2 - (ProbabilityTheory.condEntropy Y W μ)/2 := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  rw [condRuzsaDist_def, Kernel.rdist_eq', condEntropy_eq_kernel_entropy _ (hZ.prodMk hW),
    condEntropy_eq_kernel_entropy hX hZ, condEntropy_eq_kernel_entropy hY hW]
  swap; · exact hX.sub hY
  congr 2
  have hZW : IndepFun Z W μ := h.comp measurable_snd measurable_snd
  have hZW_map : μ.map ((_root_.prod Z W)) = (μ.map Z).prod (μ.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hW.aemeasurable).mp hZW
  rw [← hZW_map]
  refine Kernel.entropy_congr ?_
  have : Kernel.map (condDistrib ((_root_.prod X Y)) ((_root_.prod Z W)) μ) (fun x ↦ x.1 - x.2)
      =ᵐ[μ.map ((_root_.prod Z W))] condDistrib (X - Y) ((_root_.prod Z W)) μ :=
    (condDistrib_comp _ (by fun_prop) (by fun_prop)).symm
  refine (this.symm.trans ?_).symm
  suffices Kernel.prodMkRight T (condDistrib X Z μ)
        ×ₖ Kernel.prodMkLeft S (condDistrib Y W μ)
      =ᵐ[μ.map ((_root_.prod Z W))] condDistrib ((_root_.prod X Y)) ((_root_.prod Z W)) μ by
    filter_upwards [this] with x hx
    rw [Kernel.map_apply _ (by fun_prop), Kernel.map_apply _ (by fun_prop), hx]
  exact (condDistrib_eq_prod_of_indepFun hX hZ hY hW μ h).symm

end

omit [Countable S] in

lemma condRuzsaDist_of_copy {X : Ω → G} (hX : Measurable X) {Z : Ω → S} (hZ : Measurable Z)
    {Y : Ω' → G} (hY : Measurable Y) {W : Ω' → T} (hW : Measurable W)
    {X' : Ω'' → G} (hX' : Measurable X') {Z' : Ω'' → S} (hZ' : Measurable Z')
    {Y' : Ω''' → G} (hY' : Measurable Y') {W' : Ω''' → T} (hW' : Measurable W')
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure μ''] [IsFiniteMeasure μ''']
    (h1 : IdentDistrib ((_root_.prod X Z)) ((_root_.prod X' Z')) μ μ'') (h2 : IdentDistrib ((_root_.prod Y W)) ((_root_.prod Y' W')) μ' μ''')
    [FiniteRange Z] [FiniteRange W] [FiniteRange Z'] [FiniteRange W'] :
    (condRuzsaDist X Z Y W μ μ') = (condRuzsaDist X' Z' Y' W' μ'' μ''') := by
  classical
  set A := (FiniteRange.toFinset Z) ∪ (FiniteRange.toFinset Z')
  set B := (FiniteRange.toFinset W) ∪ (FiniteRange.toFinset W')
  have hfull : ∀ᵐ x ∂Measure.prod (μ.map Z) (μ'.map W), x ∈
      ((A ×ˢ B : Finset (S × T)): Set (S × T)) := by
    simp only [A, B]
    apply Measure.prod_of_full_measure_finset
    all_goals {
      rw [Measure.map_apply ‹_›]
      convert measure_empty (μ := μ)
      simp [← FiniteRange.range]
      measurability
    }
  have hfull' : ∀ᵐ x ∂Measure.prod (μ''.map Z') (μ'''.map W'), x ∈
    ((A ×ˢ B : Finset (S × T)): Set (S × T)) := by
    simp only [A, B]
    apply Measure.prod_of_full_measure_finset
    all_goals {
      rw [Measure.map_apply ‹_›]
      convert measure_empty (μ := μ)
      simp [← FiniteRange.range]
      measurability
    }
  rw [condRuzsaDist_def, condRuzsaDist_def, Kernel.rdist, Kernel.rdist,
    integral_eq_setIntegral hfull, integral_eq_setIntegral hfull', setIntegral_finset _ .finset,
    setIntegral_finset _ .finset]
  have hZZ' : μ.map Z = μ''.map Z' := (h1.comp measurable_snd).map_eq
  have hWW' : μ'.map W = μ'''.map W' := (h2.comp measurable_snd).map_eq
  simp_rw [Measure.prod_real_apply_singleton, ← hZZ', ← hWW',
    map_measureReal_apply hZ (.singleton _), map_measureReal_apply hW (.singleton _)]
  congr with x
  by_cases hz : μ (Z ⁻¹' {x.1}) = 0
  · simp only [smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inl ?_
    simp [Measure.real, hz]
  by_cases hw : μ' (W ⁻¹' {x.2}) = 0
  · simp only [smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inr ?_
    simp [Measure.real, hw]
  congr 2
  · have hZZ'x : μ (Z ⁻¹' {x.1}) = μ'' (Z' ⁻¹' {x.1}) := by
      have : μ.map Z {x.1} = μ''.map Z' {x.1} := by rw [hZZ']
      rwa [Measure.map_apply hZ (.singleton _),
        Measure.map_apply hZ' (.singleton _)] at this
    ext s hs
    rw [condDistrib_apply' hX hZ _ _ hz hs, condDistrib_apply' hX' hZ' _ _ _ hs]
    swap; · rwa [hZZ'x] at hz
    congr
    have : μ.map ((_root_.prod X Z)) (s ×ˢ {x.1}) = μ''.map ((_root_.prod X' Z')) (s ×ˢ {x.1}) := by rw [h1.map_eq]
    rwa [Measure.map_apply (hX.prodMk hZ) (hs.prod (.singleton _)),
      Measure.map_apply (hX'.prodMk hZ') (hs.prod (.singleton _)),
      Set.mk_preimage_prod, Set.mk_preimage_prod, Set.inter_comm,
      Set.inter_comm ((fun a ↦ X' a) ⁻¹' s)] at this
  · have hWW'x : μ' (W ⁻¹' {x.2}) = μ''' (W' ⁻¹' {x.2}) := by
      have : μ'.map W {x.2} = μ'''.map W' {x.2} := by rw [hWW']
      rwa [Measure.map_apply hW (.singleton _),
        Measure.map_apply hW' (.singleton _)] at this
    ext s hs
    rw [condDistrib_apply' hY hW _ _ hw hs, condDistrib_apply' hY' hW' _ _ _ hs]
    swap; · rwa [hWW'x] at hw
    congr
    have : μ'.map ((_root_.prod Y W)) (s ×ˢ {x.2}) = μ'''.map ((_root_.prod Y' W')) (s ×ˢ {x.2}) := by rw [h2.map_eq]
    rwa [Measure.map_apply (hY.prodMk hW) (hs.prod (.singleton _)),
      Measure.map_apply (hY'.prodMk hW') (hs.prod (.singleton _)),
      Set.mk_preimage_prod, Set.mk_preimage_prod, Set.inter_comm,
      Set.inter_comm ((fun a ↦ Y' a) ⁻¹' s)] at this

lemma condRuzsaDist'_of_copy (X : Ω → G) {Y : Ω' → G} (hY : Measurable Y)
    {W : Ω' → T} (hW : Measurable W)
    (X' : Ω'' → G) {Y' : Ω''' → G} (hY' : Measurable Y') {W' : Ω''' → T} (hW' : Measurable W')
    [IsFiniteMeasure μ'] [IsFiniteMeasure μ''']
    (h1 : IdentDistrib X X' μ μ'') (h2 : IdentDistrib ((_root_.prod Y W)) ((_root_.prod Y' W')) μ' μ''')
    [FiniteRange W] [FiniteRange W'] :
    (condRuzsaDist' X Y W μ μ') = (condRuzsaDist' X' Y' W' μ'' μ''') := by
  classical
  set A := (FiniteRange.toFinset W) ∪ (FiniteRange.toFinset W')
  have hfull : ∀ᵐ x ∂Measure.prod (dirac ()) (μ'.map W), x ∈
      ((Finset.univ (α := Unit) ×ˢ A : Finset (Unit × T)) : Set (Unit × T)) := by
    apply Measure.prod_of_full_measure_finset
    · simp
    simp only [A]
    rw [Measure.map_apply ‹_› (by measurability)]
    convert measure_empty (μ := μ)
    simp [← FiniteRange.range]
  have hfull' : ∀ᵐ x ∂Measure.prod (dirac ()) (μ'''.map W'), x ∈
      ((Finset.univ (α := Unit) ×ˢ A : Finset (Unit × T)) : Set (Unit × T)) := by
    apply Measure.prod_of_full_measure_finset
    · simp
    simp only [A]
    rw [Measure.map_apply ‹_› (by measurability)]
    convert measure_empty (μ := μ)
    simp [← FiniteRange.range]
  rw [condRuzsaDist'_def, condRuzsaDist'_def, Kernel.rdist, Kernel.rdist,
    integral_eq_setIntegral hfull, integral_eq_setIntegral hfull', setIntegral_finset _ .finset,
    setIntegral_finset _ .finset]
  have hWW' : μ'.map W = μ'''.map W' := (h2.comp measurable_snd).map_eq
  simp_rw [Measure.prod_real_apply_singleton, ← hWW', map_measureReal_apply hW (.singleton _)]
  congr with x
  by_cases hw : μ' (W ⁻¹' {x.2}) = 0
  · simp only [smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inr ?_
    simp [Measure.real, hw]
  congr 2
  · rw [Kernel.const_apply, Kernel.const_apply, h1.map_eq]
  · have hWW'x : μ' (W ⁻¹' {x.2}) = μ''' (W' ⁻¹' {x.2}) := by
      have : μ'.map W {x.2} = μ'''.map W' {x.2} := by rw [hWW']
      rwa [Measure.map_apply hW (.singleton _),
        Measure.map_apply hW' (.singleton _)] at this
    ext s hs
    rw [condDistrib_apply' hY hW _ _ hw hs, condDistrib_apply' hY' hW' _ _ _ hs]
    swap; · rwa [hWW'x] at hw
    congr
    have : μ'.map ((_root_.prod Y W)) (s ×ˢ {x.2}) = μ'''.map ((_root_.prod Y' W')) (s ×ˢ {x.2}) := by rw [h2.map_eq]
    rwa [Measure.map_apply (hY.prodMk hW) (hs.prod (.singleton _)),
      Measure.map_apply (hY'.prodMk hW') (hs.prod (.singleton _)),
      Set.mk_preimage_prod, Set.mk_preimage_prod, Set.inter_comm,
      Set.inter_comm ((fun a ↦ Y' a) ⁻¹' s)] at this

variable (μ μ') in
lemma condRuzsaDist_comp_right {T' : Type*} [Finite T] [Finite T'] [MeasurableSpace T']
    [MeasurableSingletonClass T'] [IsFiniteMeasure μ']
    (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (e : T → T')
    (hY : Measurable Y) (hW : Measurable W) (he : Measurable e)
    (h'e : Injective e) :
    (condRuzsaDist' X Y (e ∘ W) μ μ') = (condRuzsaDist' X Y W μ μ') := by
  cases nonempty_fintype T
  cases nonempty_fintype T'
  rw [condRuzsaDist'_eq_sum' hY (he.comp hW), condRuzsaDist'_eq_sum' hY hW]
  have A i : e ⁻¹' {e i} = {i} := by ext x; simp [h'e.eq_iff]
  symm
  refine Fintype.sum_of_injective e h'e _ _ (fun i hi ↦ ?_) (by simp [Set.preimage_comp, A])
  suffices e ⁻¹' {i} = ∅ by simp [Set.preimage_comp, this]
  simpa [Set.eq_empty_iff_forall_notMem] using hi

lemma condRuzsaDist_of_inj_map {G' : Type*} [Countable G'] [AddCommGroup G']
  [MeasurableSpace G'] [MeasurableSingletonClass G'] [IsProbabilityMeasure μ]
  (Y : Fin 4 → Ω → G) (h_indep : IndepFun ((_root_.prod (Y 0) (Y 2))) ((_root_.prod (Y 1) (Y 3))) μ)
  (h_meas : ∀ i, Measurable (Y i)) (π : G × G →+ G')
  (hπ : ∀ (h : G), Injective (fun g ↦ π (g, h)))
  [FiniteRange (Y 2)] [FiniteRange (Y 3)] :
    (condRuzsaDist (π ∘ (_root_.prod (Y 0) (Y 2))) (Y 2) (π ∘ (_root_.prod (Y 1) (Y 3))) (Y 3) μ μ) = (condRuzsaDist (Y 0) (Y 2) (Y 1) (Y 3) μ μ) := by
  let f (h : G) (g : G) : G' := π (g, h)
  let f' : G × G → G → G' := fun (h1, h2) ↦ fun g ↦ π (g, h1 - h2)
  have hf' (t : G × G) : Injective (f' t) := fun _ _ h ↦ hπ _ h
  let f'' : G × G → G' × G := fun (g, h) ↦ (π (g, h), h)
  have hf'' : Measurable f'' := .of_discrete
  have hm1 : Measurable (Y 0 - Y 1) := (h_meas 0).sub (h_meas 1)
  have hm2 : Measurable ((_root_.prod (Y 2) (Y 3))) := (h_meas 2).prodMk (h_meas 3)
  rw [condRuzsaDist_of_indep (h_meas 0) (h_meas 2) (h_meas 1) (h_meas 3) μ h_indep,
    condRuzsaDist_of_indep (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) μ
    (by exact h_indep.comp hf'' hf''),
    ← condEntropy_of_injective μ hm1 hm2 f' hf', ← map_comp_sub π,
    ← condEntropy_of_injective μ (h_meas 0) (h_meas 2) f hπ,
    ← condEntropy_of_injective μ (h_meas 1) (h_meas 3) f hπ]
  rfl

lemma condRuzsaDist'_of_inj_map [IsProbabilityMeasure μ] [Module (ZMod 2) G]
  {X B C : Ω → G}
    (hX : Measurable X) (hB : Measurable B) (hC : Measurable C)
    (h_indep : IndepFun X ((_root_.prod B C)) μ) [FiniteRange X] [FiniteRange B] [FiniteRange C] :
    (condRuzsaDist' X B (B + C) μ μ) = (condRuzsaDist' X C (B + C) μ μ) := by
  let π : G × G →+ G :=
  { toFun := fun x ↦ x.2 - x.1
    map_zero' := by simp
    map_add' := fun a b ↦ by simp only [Prod.snd_add, Prod.fst_add, ZModModule.sub_eq_add]; abel }
  let Y : Fin 4 → Ω → G := ![-X, C, fun _ ↦ 0, B + C]
  have _ : FiniteRange (Y 0) := by simp [Y]; infer_instance
  have _ : FiniteRange (Y 1) := by simp [Y]; infer_instance
  have _ : FiniteRange (Y 2) := by simp [Y]; infer_instance
  have _ : FiniteRange (Y 3) := by simp [Y]; infer_instance
  have hY_meas i : Measurable (Y i) := by
    fin_cases i; exacts [hX.neg, hC, measurable_const, hB.add hC]
  calc (condRuzsaDist' X B (B + C) μ μ)
    = (condRuzsaDist X (fun _ : Ω ↦ (0 : G)) B (B + C) μ μ) := by rw [condRuzsaDist_of_const hX]
  _ = (condRuzsaDist (π ∘ (_root_.prod (-X) (fun _ : Ω ↦ (0 : G)))) (fun _ : Ω ↦ (0 : G)) (π ∘ (_root_.prod C (B + C))) (B + C) μ μ) := by
    congr
    · ext1 ω; simp [π]
    · ext1 ω
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, comp_apply, Pi.add_apply, π]
      abel
  _ = (condRuzsaDist (π ∘ (_root_.prod (Y 0) (Y 2))) (Y 2) (π ∘ (_root_.prod (Y 1) (Y 3))) (Y 3) μ μ) := by congr
  _ = (condRuzsaDist (-X) (fun _ : Ω ↦ (0 : G)) C (B + C) μ μ) := by
    rw [condRuzsaDist_of_inj_map _ _ hY_meas π (fun _ ↦ sub_right_injective)]
    · congr
    · have h1 : ((_root_.prod (Y 0) (Y 2))) = (fun x ↦ (-x, 0)) ∘ X := by ext1 ω; simp [Y]
      have h2 : ((_root_.prod (Y 1) (Y 3))) = (fun p ↦ (p.2, p.1 + p.2)) ∘ ((_root_.prod B C)) := by
        ext ω : 1; simp [ZModModule.neg_eq_self, Y]
      rw [h1, h2]
      refine h_indep.comp ?_ ?_
      · exact measurable_neg.prodMk measurable_const
      · exact measurable_snd.prodMk (measurable_fst.add measurable_snd)
  _ = (condRuzsaDist' (-X) C (B + C) μ μ) := by rw [condRuzsaDist_of_const]; exact hX.neg
  _ = (condRuzsaDist' X C (B + C) μ μ) := by simp_rw [ZModModule.neg_eq_self]

lemma condRuzsaDist'_of_inj_map' [Module (ZMod 2) G] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ''] {A : Ω'' → G} {B C : Ω → G} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) [FiniteRange A] [FiniteRange B] [FiniteRange C] :
    (condRuzsaDist' A B (B + C) μ'' μ) = (condRuzsaDist' A C (B + C) μ'' μ) := by

  let Ω' := Ω'' × Ω
  set X₂' : Ω' → G := A ∘ Prod.fst with hX₂'_def
  have hX₂' : Measurable X₂' := hA.comp measurable_fst
  let B' : Ω' → G := B ∘ Prod.snd
  have hB' : Measurable B' := hB.comp measurable_snd
  let C' : Ω' → G := C ∘ Prod.snd
  have hC' : Measurable C' := hC.comp measurable_snd
  let μ' : Measure Ω' := Measure.prod μ'' μ
  have : IsProbabilityMeasure μ' := by infer_instance
  
  have h1 : (condRuzsaDist' A B (B + C) μ'' μ) = (condRuzsaDist' X₂' B' (B' + C') μ' μ') := by
    refine condRuzsaDist'_of_copy A hB (by fun_prop) X₂' hB' (by fun_prop) ?_ ?_
    · constructor
      · exact hA.aemeasurable
      · exact hX₂'.aemeasurable
      · rw [← Measure.map_map hA measurable_fst]
        simp [μ']
    · constructor
      · exact (hB.prodMk (hB.add hC)).aemeasurable
      · exact (hB'.prodMk (hB'.add hC')).aemeasurable
      · have : (_root_.prod B' (B' + C')) = ((_root_.prod B (B + C))) ∘ Prod.snd := by ext1 _; simp [C', B']
        rw [this, ← Measure.map_map _ measurable_snd]
        · simp only [Measure.map_snd_prod, measure_univ, one_smul, μ']
        · exact hB.prodMk (hB.add hC)
  have h2 : (condRuzsaDist' A C (B + C) μ'' μ) = (condRuzsaDist' X₂' C' (B' + C') μ' μ') := by
    apply condRuzsaDist'_of_copy _ hC (by fun_prop) X₂' hC' (by fun_prop) ?_ ?_
    · constructor
      · exact hA.aemeasurable
      · exact hX₂'.aemeasurable
      · rw [← Measure.map_map hA measurable_fst]
        simp [μ']
    · constructor
      · exact (hC.prodMk (hB.add hC)).aemeasurable
      · exact (hC'.prodMk (hB'.add hC')).aemeasurable
      · have : (_root_.prod C' (B' + C')) = ((_root_.prod C (B + C))) ∘ Prod.snd := by ext1 _; simp [B', C']
        rw [this, ← Measure.map_map _ measurable_snd]
        · simp only [Measure.map_snd_prod, measure_univ, one_smul, μ']
        · exact hC.prodMk (hB.add hC)
  rw [h1, h2, condRuzsaDist'_of_inj_map hX₂' hB' hC']
  rw [indepFun_iff_map_prod_eq_prod_map_map hX₂'.aemeasurable (hB'.prodMk hC').aemeasurable]
  have h_prod : (fun ω ↦ (X₂' ω, prod B' C' ω)) = Prod.map A ((_root_.prod B C)) := by
    ext1
    simp only [comp_apply, X₂', B', C']
    rfl
  have h_comp_snd : (fun a ↦ (B' a, C' a)) = ((_root_.prod B C)) ∘ Prod.snd := by ext1; simp [B', C']
  rw [h_prod, h_comp_snd, hX₂'_def, ← Measure.map_map _ measurable_snd,
    ← Measure.map_map _ measurable_fst, Measure.map_prod_map]
  rotate_left
  · exact hA
  · exact hB.prodMk hC
  · exact hA
  · exact hB.prodMk hC
  simp [μ']

lemma kaimanovich_vershik {X Y Z : Ω → G} (h : iIndepFun ![X, Y, Z] μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (ProbabilityTheory.entropy (X + Y + Z) μ) - (ProbabilityTheory.entropy (X + Y) μ) ≤ (ProbabilityTheory.entropy (Y + Z) μ) - (ProbabilityTheory.entropy Y μ) := by
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  suffices ((ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy Y μ) + (ProbabilityTheory.entropy Z μ)) + (ProbabilityTheory.entropy (X + Y + Z) μ)
    ≤ ((ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy (Y + Z) μ)) + ((ProbabilityTheory.entropy Z μ) + (ProbabilityTheory.entropy (X + Y) μ)) by linarith
  have : ∀ (i : Fin 3), Measurable (![X, Y, Z] i) := fun i ↦ by fin_cases i <;> assumption
  convert entropy_triple_add_entropy_le μ hX hZ (show Measurable (X + (Y + Z)) by fun_prop)
    using 2
  · calc
      (ProbabilityTheory.entropy X μ) + (ProbabilityTheory.entropy Y μ) + (ProbabilityTheory.entropy Z μ) = (ProbabilityTheory.entropy ((_root_.prod X Y)) μ) + (ProbabilityTheory.entropy Z μ) := by
        rw [IndepFun.entropy_pair_eq_add hX hY]
        exact h.indepFun (show 0 ≠ 1 by decide)
      _ = (ProbabilityTheory.entropy ((_root_.prod ((_root_.prod X Y)) Z)) μ) := by
        rw [IndepFun.entropy_pair_eq_add (hX.prodMk hY) hZ]
        exact h.indepFun_prodMk this 0 1 2 (by decide) (by decide)
      _ = (ProbabilityTheory.entropy ((_root_.prod X ((_root_.prod Z (X + (Y + Z)))))) μ) := by
        apply entropy_of_comp_eq_of_comp μ (by fun_prop) (by fun_prop)
          (fun ((x, y), z) ↦ (x, z, x + y + z)) (fun (a, b, c) ↦ ((a, c - a - b), b))
        all_goals { funext ω; dsimp [prod]; ext <;> dsimp; abel }
  · rw [add_assoc]
  · symm
    refine (entropy_add_right hX (by fun_prop) _).trans <|
      IndepFun.entropy_pair_eq_add hX (by fun_prop) ?_
    exact h.indepFun_add_right this 0 1 2 (by decide) (by decide)
  · rw [eq_comm, ← add_assoc]
    refine (entropy_add_right' hZ (by fun_prop) _).trans <|
      IndepFun.entropy_pair_eq_add hZ (by fun_prop) ?_
    exact h.indepFun_add_right this 2 0 1 (by decide) (by decide)

lemma kaimanovich_vershik' {X Y Z : Ω → G} (h : iIndepFun ![X, Y, Z] μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (ProbabilityTheory.entropy (X - (Y + Z)) μ) - (ProbabilityTheory.entropy (X - Y) μ) ≤ (ProbabilityTheory.entropy (Y + Z) μ) - (ProbabilityTheory.entropy Y μ) := by
  rw [← entropy_neg (X := Y + Z) (by fun_prop), ← entropy_neg hY]
  simp_rw [sub_eq_add_neg, neg_add, ← add_assoc]
  refine kaimanovich_vershik ?_ hX hY.neg hZ.neg
  convert (h.neg 1).neg 2
  ext i; fin_cases i
  · simp (discharger := decide)
  · simp (discharger := decide)
  · rw [← show ∀ h : 2 < 3, (2 : Fin 3) = ⟨2, h⟩ by intro; rfl]
    simp (discharger := decide)

section BalogSzemerediGowers

lemma ent_bsg [IsProbabilityMeasure μ] {A B : Ω → G} (hA : Measurable A) (hB : Measurable B)
    [Finite G] :
    (μ.map (A + B))[fun z ↦ (rdist A B (μ[|(A + B) ⁻¹' {z}]) (μ[|(A + B) ⁻¹' {z}]))]
      ≤ 3 * (ProbabilityTheory.mutualInfo A B μ) + 2 * (ProbabilityTheory.entropy (A + B) μ) - (ProbabilityTheory.entropy A μ) - (ProbabilityTheory.entropy B μ) := by
  let Z := A + B
  have hZ : Measurable Z := hA.add hB
  obtain ⟨Ω', _, AB₁, AB₂, Z', ν, _, hAB₁, hAB₂, hZ', hABZ, hABZ₁, hABZ₂, hZ₁, hZ₂⟩ :=
    condIndep_copies' ((_root_.prod A B)) Z (hA.prodMk hB) hZ μ (fun (a, b) c ↦ c = a + b)
    .of_discrete (Eventually.of_forall fun _ ↦ rfl)
  let A₁ := fun ω ↦ (AB₁ ω).1
  let B₁ := fun ω ↦ (AB₁ ω).2
  let A₂ := fun ω ↦ (AB₂ ω).1
  let B₂ := fun ω ↦ (AB₂ ω).2
  replace hZ₁ : Z' = A₁ + B₁ := funext hZ₁
  replace hZ₂ : Z' = A₂ + B₂ := funext hZ₂
  have hA₁ : Measurable A₁ := hAB₁.fst
  have hB₁ : Measurable B₁ := hAB₁.snd
  have hA₂ : Measurable A₂ := hAB₂.fst
  have hB₂ : Measurable B₂ := hAB₂.snd
  have hZZ' : IdentDistrib Z' Z ν μ := hABZ₁.comp measurable_snd
  have :=
    calc
      (ProbabilityTheory.entropy ((_root_.prod A₁ ((_root_.prod B₁ (A₁ - B₂))))) ν)
        = (ProbabilityTheory.entropy ((_root_.prod ((_root_.prod A₁ B₁)) ((_root_.prod ((_root_.prod A₂ B₂)) Z')))) ν) := entropy_of_comp_eq_of_comp _
          (hA₁.prodMk <| hB₁.prodMk <| hA₁.sub hB₂) (hAB₁.prodMk <| hAB₂.prodMk hZ')
            (fun (a, b, c) ↦ ((a, b), (b + c, a - c), a + b))
            (fun ((a, b), (_c, d), _e) ↦ (a, b, a - d))
          (by funext; simpa [sub_add_eq_add_sub, Prod.ext_iff, ← hZ₁, hZ₂, two_nsmul,
            ← add_sub_assoc, add_comm, eq_sub_iff_add_eq]
             using congr_fun (hZ₂.symm.trans hZ₁) _) rfl
      _ = (ProbabilityTheory.entropy ((_root_.prod ((_root_.prod A₁ B₁)) Z')) ν) + (ProbabilityTheory.entropy ((_root_.prod ((_root_.prod A₂ B₂)) Z')) ν) - (ProbabilityTheory.entropy Z' ν) :=
        ent_of_cond_indep _ hAB₁ hAB₂ hZ' hABZ
      _ = 2 * (ProbabilityTheory.entropy ((_root_.prod ((_root_.prod A B)) Z)) μ) - (ProbabilityTheory.entropy Z μ) := by
        rw [two_mul]
        congr 1
        congr 1 <;> exact IdentDistrib.entropy_congr ‹_›
        exact hZZ'.entropy_congr
      _ = 2 * (ProbabilityTheory.entropy ((_root_.prod A B)) μ) - (ProbabilityTheory.entropy Z μ) := by
        congr 2
        exact entropy_prod_comp (hA.prodMk hB) _ fun x ↦ x.1 + x.2
  have :=
    calc
      (ProbabilityTheory.entropy ((_root_.prod A₁ (A₁ - B₂))) ν)
        = (ProbabilityTheory.entropy ((_root_.prod A₁ B₂)) ν) := entropy_sub_right hA₁ hB₂ _
      _ ≤ (ProbabilityTheory.entropy A₁ ν) + (ProbabilityTheory.entropy B₂ ν) := entropy_pair_le_add hA₁ hB₂ _
      _ = (ProbabilityTheory.entropy A μ) + (ProbabilityTheory.entropy B μ) := by
        congr 1
        · exact (hABZ₁.comp measurable_fst.fst).entropy_congr
        · exact (hABZ₂.comp measurable_fst.snd).entropy_congr
  have :=
    calc
      (ProbabilityTheory.entropy ((_root_.prod B₁ (A₁ - B₂))) ν)
        = (ProbabilityTheory.entropy ((_root_.prod A₂ B₁)) ν) := by
          rw [entropy_comm hB₁ (show Measurable (A₁ - B₂) from hA₁.sub hB₂),
            ← entropy_sub_left' hA₂ hB₁, sub_eq_sub_iff_add_eq_add.2 <| hZ₁.symm.trans hZ₂]
      _ ≤ (ProbabilityTheory.entropy A₂ ν) + (ProbabilityTheory.entropy B₁ ν) := entropy_pair_le_add hA₂ hB₁ _
      _ = (ProbabilityTheory.entropy A μ) + (ProbabilityTheory.entropy B μ) := by
        congr 1
        · exact (hABZ₂.comp measurable_fst.fst).entropy_congr
        · exact (hABZ₁.comp measurable_fst.snd).entropy_congr
  have :=
    calc
     _ ≤ _ := entropy_triple_add_entropy_le ν hA₁ hB₁ (show Measurable (A₁ - B₂) from hA₁.sub hB₂)
     _ ≤ _ := add_le_add ‹_› ‹_›
  have :=
    calc
      (ProbabilityTheory.condEntropy (A₁ - B₂) Z' ν)
        ≤ (ProbabilityTheory.entropy (A₁ - B₂) ν) := condEntropy_le_entropy _ (hA₁.sub hB₂) hZ'
      _ ≤ _ := le_sub_iff_add_le'.2 ‹_›
      _ = 2 * (ProbabilityTheory.mutualInfo A B μ) + (ProbabilityTheory.entropy Z μ) := by
        rw [‹(ProbabilityTheory.entropy ((_root_.prod A₁ ((_root_.prod B₁ (A₁ - B₂))))) ν) = _›, mutualInfo_def]; ring
  have hA₁Z :=
    calc
      (ProbabilityTheory.condEntropy A₁ Z' ν)
      _ = (ProbabilityTheory.entropy ((_root_.prod A₁ B₁)) ν) - (ProbabilityTheory.entropy Z' ν) := by
        rw [chain_rule'', hZ₁, entropy_add_right, entropy_comm] <;> assumption
      _ = (ProbabilityTheory.entropy ((_root_.prod A B)) μ) - (ProbabilityTheory.entropy Z μ) := by
        congr 1
        · exact (hABZ₁.comp measurable_fst).entropy_congr
        · exact hZZ'.entropy_congr
      _ = (ProbabilityTheory.entropy A μ) + (ProbabilityTheory.entropy B μ) - (ProbabilityTheory.mutualInfo A B μ) - (ProbabilityTheory.entropy Z μ) := by
        rw [← entropy_add_entropy_sub_mutualInfo]
  have hB₂Z :=
    calc
      (ProbabilityTheory.condEntropy B₂ Z' ν)
      _ = (ProbabilityTheory.entropy ((_root_.prod A₂ B₂)) ν) - (ProbabilityTheory.entropy Z' ν) := by
        rw [chain_rule'', hZ₂, entropy_add_right', entropy_comm] <;> assumption
      _ = (ProbabilityTheory.entropy ((_root_.prod A B)) μ) - (ProbabilityTheory.entropy Z μ) := by
        congr 1
        · exact (hABZ₂.comp measurable_fst).entropy_congr
        · exact hZZ'.entropy_congr
      _ = (ProbabilityTheory.entropy A μ) + (ProbabilityTheory.entropy B μ) - (ProbabilityTheory.mutualInfo A B μ) - (ProbabilityTheory.entropy Z μ) := by
        rw [← entropy_add_entropy_sub_mutualInfo]
  calc
    (μ.map Z)[fun z ↦ (rdist A B (μ[|Z ← z]) (μ[|Z ← z]))]
      = (ν.map Z')[fun z ↦ (rdist A₁ B₂ (ν[|Z' ← z]) (ν[|Z' ← z]))] := by
        rw [hZZ'.map_eq]
        refine integral_congr_ae <| Eventually.of_forall fun z ↦ ?_
        have hAA₁ : IdentDistrib A₁ A (ν[|Z' ← z]) (μ[|Z ← z]) :=
          (hABZ₁.comp <| measurable_fst.fst.prodMk measurable_snd).cond
            (.singleton z) hZ' hZ
        have hBB₂ : IdentDistrib B₂ B (ν[|Z' ← z]) (μ[|Z ← z]) :=
          (hABZ₂.comp <| measurable_fst.snd.prodMk measurable_snd).cond
            .of_discrete hZ' hZ
        dsimp (config := {zeta := false}) [rdist]
        rw [← hAA₁.entropy_congr, ← hBB₂.entropy_congr, hAA₁.map_eq, hBB₂.map_eq]
    _ = (ν.map Z')[fun z ↦
          (ProbabilityTheory.entropy (A₁ - B₂) (ν[|Z' ← z])) - (ProbabilityTheory.entropy A₁ (ν[|Z' ← z]))/2 - (ProbabilityTheory.entropy B₂ (ν[|Z' ← z]))/2] := by
        apply integral_congr_ae
        apply hABZ.mono
        intro z hz
        exact (hz.comp measurable_fst measurable_snd).rdist_eq hA₁ hB₂
    _ = (ProbabilityTheory.condEntropy (A₁ - B₂) Z' ν) - (ProbabilityTheory.condEntropy A₁ Z' ν) / 2 - (ProbabilityTheory.condEntropy B₂ Z' ν) / 2 := by
        rw [integral_sub, integral_sub, integral_div, integral_div]
        · rfl
        all_goals exact .of_finite
    _ ≤ 2 * (ProbabilityTheory.mutualInfo A B μ) + (ProbabilityTheory.entropy Z μ) - (ProbabilityTheory.condEntropy A₁ Z' ν) / 2 - (ProbabilityTheory.condEntropy B₂ Z' ν) / 2 :=
        sub_le_sub_right (sub_le_sub_right ‹_› _) _
    _ = _ := by rw [hA₁Z, hB₂Z]; ring

end BalogSzemerediGowers

variable (μ μ') in

lemma condRuzsaDist_le [Countable T] {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] [FiniteRange W] :
      (condRuzsaDist X Z Y W μ μ') ≤ (rdist X Y μ μ') + (ProbabilityTheory.mutualInfo X Z μ)/2 + (ProbabilityTheory.mutualInfo Y W μ')/2 := by
  have hXZ : Measurable ((_root_.prod X Z) : Ω → G × S):= hX.prodMk hZ
  have hYW : Measurable ((_root_.prod Y W) : Ω' → G × T):= hY.prodMk hW
  obtain ⟨ν, XZ', YW', _, hXZ', hYW', hind, hIdXZ, hIdYW, _, _⟩ :=
    independent_copies_finiteRange hXZ hYW μ μ'
  let X' := Prod.fst ∘ XZ'
  let Z' := Prod.snd ∘ XZ'
  let Y' := Prod.fst ∘ YW'
  let W' := Prod.snd ∘ YW'
  have hX' : Measurable X' := hXZ'.fst
  have hZ' : Measurable Z' := hXZ'.snd
  have hY' : Measurable Y' := hYW'.fst
  have hW' : Measurable W' := hYW'.snd
  have : FiniteRange W' := instFiniteRangeComp ..
  have : FiniteRange X' := instFiniteRangeComp ..
  have : FiniteRange Y' := instFiniteRangeComp ..
  have : FiniteRange Z' := instFiniteRangeComp ..
  have hind' : IndepFun X' Y' ν := hind.comp measurable_fst measurable_fst
  rw [show XZ' = (_root_.prod X' Z') by rfl] at hIdXZ hind
  rw [show YW' = (_root_.prod Y' W') by rfl] at hIdYW hind
  rw [← condRuzsaDist_of_copy hX' hZ' hY' hW' hX hZ hY hW hIdXZ hIdYW,
    condRuzsaDist_of_indep hX' hZ' hY' hW' _ hind]
  have hIdX : IdentDistrib X X' μ ν := hIdXZ.symm.comp measurable_fst
  have hIdY : IdentDistrib Y Y' μ' ν := hIdYW.symm.comp measurable_fst
  rw [hIdX.rdist_congr hIdY, hIdXZ.symm.mutualInfo_eq, hIdYW.symm.mutualInfo_eq,
    hind'.rdist_eq hX' hY', mutualInfo_eq_entropy_sub_condEntropy hX' hZ',
    mutualInfo_eq_entropy_sub_condEntropy hY' hW']
  have h := condEntropy_le_entropy ν (X := X' - Y') (hX'.sub hY') (hZ'.prodMk hW')
  linarith [h, entropy_nonneg Z' ν, entropy_nonneg W' ν]

variable (μ μ') in
lemma condRuzsaDist_le' [Countable T] {X : Ω → G} {Y : Ω' → G} {W : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    [FiniteRange X] [FiniteRange Y] [FiniteRange W] :
    (condRuzsaDist' X Y W μ μ') ≤ (rdist X Y μ μ') + (ProbabilityTheory.mutualInfo Y W μ')/2 := by
  rw [← condRuzsaDist_of_const hX _ _ (0 : Fin 1)]
  refine (condRuzsaDist_le μ μ' hX measurable_const hY hW).trans ?_
  simp [mutualInfo_const hX (0 : Fin 1)]

variable (μ μ') in
lemma condRuzsaDist_le'_prod [Countable T] {X : Ω → G} {Y : Ω' → G} {W Z : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange W] [FiniteRange Z] :
    (condRuzsaDist' X Y ((_root_.prod W Z)) μ μ') ≤ (condRuzsaDist' X Y Z μ μ') + (ProbabilityTheory.condMutualInfo Y W Z μ')/2 := by
  rw [condRuzsaDist'_prod_eq_sum _ _ hY hW hZ, condRuzsaDist'_eq_sum hY hZ,
    condMutualInfo_eq_sum hZ, Finset.sum_div, ← Finset.sum_add_distrib]
  gcongr with z
  rw [mul_div_assoc, ← mul_add]
  rcases eq_or_ne (μ' (Z ⁻¹' {z})) 0 with hz | hz
  · simp [measureReal_def, hz]
  · have : IsProbabilityMeasure (μ'[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure hz
    gcongr
    exact condRuzsaDist_le' _ _ hX hY hW

variable (μ) in
lemma comparison_of_ruzsa_distances [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (rdist X (Y+ Z) μ μ') - (rdist X Y μ μ') ≤ ((ProbabilityTheory.entropy (Y + Z) μ') - (ProbabilityTheory.entropy Y μ')) / 2 ∧
    (Module (ZMod 2) G →
      (ProbabilityTheory.entropy (Y + Z) μ') - (ProbabilityTheory.entropy Y μ') = (rdist Y Z μ' μ') + (ProbabilityTheory.entropy Z μ') / 2 - (ProbabilityTheory.entropy Y μ') / 2) := by
  obtain ⟨Ω'', mΩ'', μ'', X', Y', Z', hμ, hi, hX', hY', hZ', h2X', h2Y', h2Z', _, _, _⟩ :=
    independent_copies3_nondep_finiteRange hX hY hZ μ μ' μ'
  have hY'Z' : IndepFun Y' Z' μ'' := hi.indepFun (show (1 : Fin 3) ≠ 2 by decide)
  have h2 : IdentDistrib (Y' + Z') (Y + Z) μ'' μ' := h2Y'.add h2Z' hY'Z' h
  have hm : ∀ (i : Fin 3), Measurable (![X', Y', Z'] i) :=
    fun i ↦ by fin_cases i <;> (dsimp; assumption)
  have hXY' : IndepFun X' Y' μ'' := hi.indepFun (show (0 : Fin 3) ≠ 1 by decide)
  have hYZ' : IndepFun Y' Z' μ'' := hi.indepFun (show (1 : Fin 3) ≠ 2 by decide)
  have hXYZ' : IndepFun X' (Y' + Z') μ'' := by
    symm
    exact hi.indepFun_add_left hm 1 2 0 (by decide) (by decide)
  rw [← h2X'.rdist_congr h2Y', ← h2X'.rdist_congr h2, ← h2Y'.rdist_congr h2Z',
    ← h2.entropy_congr, ← h2Y'.entropy_congr, ← h2Z'.entropy_congr]
  rw [hXY'.rdist_eq hX' hY', hYZ'.rdist_eq hY' hZ', hXYZ'.rdist_eq hX' (hY'.add hZ')]
  constructor
  · linarith [kaimanovich_vershik' hi hX' hY' hZ']
  · intro hG
    rw [ZModModule.sub_eq_add Y' Z']
    ring

variable (μ) in

lemma condRuzsaDist_diff_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (rdist X (Y+ Z) μ μ') - (rdist X Y μ μ') ≤ ((ProbabilityTheory.entropy (Y + Z) μ') - (ProbabilityTheory.entropy Y μ')) / 2 :=
  (comparison_of_ruzsa_distances μ hX hY hZ h).1

variable (μ) [Module (ZMod 2) G] in
lemma entropy_sub_entropy_eq_condRuzsaDist_add [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (ProbabilityTheory.entropy (Y + Z) μ') - (ProbabilityTheory.entropy Y μ') = (rdist Y Z μ' μ') + (ProbabilityTheory.entropy Z μ') / 2 - (ProbabilityTheory.entropy Y μ') / 2 :=
  (comparison_of_ruzsa_distances μ hX hY hZ h).2 ‹_›

variable (μ) [Module (ZMod 2) G] in
lemma condRuzsaDist_diff_le' [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (rdist X (Y + Z) μ μ') - (rdist X Y μ μ') ≤
    (rdist Y Z μ' μ') / 2 + (ProbabilityTheory.entropy Z μ') / 4 - (ProbabilityTheory.entropy Y μ') / 4 := by
  linarith [condRuzsaDist_diff_le μ hX hY hZ h,
    entropy_sub_entropy_eq_condRuzsaDist_add μ hX hY hZ h]

variable (μ) in
lemma condRuzsaDist_diff_le'' [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (condRuzsaDist' X Y (Y+ Z) μ μ') - (rdist X Y μ μ') ≤ ((ProbabilityTheory.entropy (Y+ Z) μ') - (ProbabilityTheory.entropy Z μ'))/2 := by
  rw [← mutualInfo_add_right hY hZ h]
  linarith [condRuzsaDist_le' (W := Y + Z) μ μ' hX hY (by fun_prop)]

variable (μ) [Module (ZMod 2) G] in
lemma condRuzsaDist_diff_le''' [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    (condRuzsaDist' X Y (Y+ Z) μ μ') - (rdist X Y μ μ') ≤
    (rdist Y Z μ' μ')/2 + (ProbabilityTheory.entropy Y μ')/4 - (ProbabilityTheory.entropy Z μ')/4 := by
  linarith [condRuzsaDist_diff_le'' μ hX hY hZ h,
    entropy_sub_entropy_eq_condRuzsaDist_add μ hX hY hZ h]

variable (μ) in
lemma condRuzsaDist_diff_ofsum_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y Z Z' : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hZ' : Measurable Z')
    (h : iIndepFun ![Y, Z, Z'] μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] [FiniteRange Z'] :
    (condRuzsaDist' X (Y + Z) (Y + Z + Z') μ μ') - (rdist X Y μ μ') ≤
    ((ProbabilityTheory.entropy (Y + Z + Z') μ') + (ProbabilityTheory.entropy (Y + Z) μ') - (ProbabilityTheory.entropy Y μ') - (ProbabilityTheory.entropy Z' μ'))/2 := by
  have hadd : IndepFun (Y + Z) Z' μ' :=
    (h.indepFun_add_left (Fin.cases hY <| Fin.cases hZ <| Fin.cases hZ' Fin.rec0) 0 1 2
      (show 0 ≠ 2 by decide) (show 1 ≠ 2 by decide))
  have h1 := condRuzsaDist_diff_le'' μ hX (show Measurable (Y + Z) by fun_prop) hZ' hadd
  have h2 := condRuzsaDist_diff_le μ hX hY hZ (h.indepFun (show 0 ≠ 1 by decide))
  linarith [h1, h2]
end

/- PFR.TauFunctional -/
/-
# The tau functional

Definition of the tau functional and basic facts

## Main definitions:

* `η`: $1/9$
* `τ`: The tau functional $\tau[X_1; X_2] = d[X_1; X_2] + \eta d[X^0_1; X_1] + \eta d[X^0_2; X_2].$

## Main results

* `tau_minimizer_exists`: A pair of random variables minimizing $\tau$ exists.
* `condRuzsaDistance_ge_of_min`: If $X_1,X_2$ is a tau-minimizer with $k = d[X_1;X_2]$,
  then $d[X'_1|Z, X'_2|W]$ is at least
  $$k - \eta (d[X^0_1;X'_1|Z] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2|W] - d[X^0_2;X_2] )$$
  for any $X'_1, Z, X'_2, W$.
-/

noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory
universe uG

variable (Ω₀₁ Ω₀₂ : Type*) [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
variable (G : Type uG) [AddCommGroup G] [Finite G] [MeasurableSpace G]

structure refPackage where
  
  X₀₁ : Ω₀₁ → G
  
  X₀₂ : Ω₀₂ → G
  hmeas1 : Measurable X₀₁
  hmeas2 : Measurable X₀₂

  η : ℝ
  hη : 0 < η
  hη' : 8 * η ≤ 1

variable (p : refPackage Ω₀₁ Ω₀₂ G)
variable {Ω₀₁ Ω₀₂ G}

variable {Ω Ω' Ω₁ Ω₂ Ω'₁ Ω'₂ S T : Type*}

noncomputable def tau {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (X₁ : Ω₁ → G) (X₂ : Ω₂ → G) (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) : ℝ :=
  (rdist X₁ X₂ μ₁ μ₂) + p.η * (rdist p.X₀₁ X₁ ℙ μ₁) + p.η * (rdist p.X₀₂ X₂ ℙ μ₂)

lemma continuous_tau_restrict_probabilityMeasure
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] :
    Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ (tau p id id μ.1 μ.2)) := by
  have obs₁ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ (rdist p.X₀₂ id ℙ μ.2)) :=
    Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas2) continuous_snd
  have obs₂ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ (rdist id id μ.1.toMeasure μ.2)) :=
    continuous_rdist_restrict_probabilityMeasure
  have obs₃ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ (rdist p.X₀₁ id ℙ μ.1)) :=
    Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas1) continuous_fst
  continuity

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
  [Finite G] in

lemma ProbabilityTheory.IdentDistrib.tau_eq [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace Ω'₁] [MeasurableSpace Ω'₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ'₁ : Measure Ω'₁} {μ'₂ : Measure Ω'₂}
    {X₁ : Ω₁ → G} {X₂ : Ω₂ → G} {X₁' : Ω'₁ → G} {X₂' : Ω'₂ → G}
    (h₁ : IdentDistrib X₁ X₁' μ₁ μ'₁) (h₂ : IdentDistrib X₂ X₂' μ₂ μ'₂) :
    (tau p X₁ X₂ μ₁ μ₂) = (tau p X₁' X₂' μ'₁ μ'₂) := by
  simp only [tau]
  rw [h₁.rdist_congr_right p.hmeas1.aemeasurable,
      h₂.rdist_congr_right p.hmeas2.aemeasurable,
      h₁.rdist_congr h₂]

def tau_minimizes {Ω : Type*} [MeasureSpace Ω] (X₁ : Ω → G) (X₂ : Ω → G) : Prop :=
  ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (tau p X₁ X₂ ℙ ℙ) ≤ (tau p id id ν₁ ν₂)

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
  [Finite G] in

lemma ProbabilityTheory.IdentDistrib.tau_minimizes [MeasureSpace Ω]
    [MeasureSpace Ω']
    {X₁ X₂ : Ω → G} {X₁' X₂' : Ω' → G}
    (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂') :
    tau_minimizes p X₁ X₂ ↔ tau_minimizes p X₁' X₂' := by
  simp_rw [_root_.tau_minimizes, h₁.tau_eq p h₂]

lemma tau_min_exists_measure [MeasurableSingletonClass G] :
    ∃ (μ : Measure G × Measure G),
    IsProbabilityMeasure μ.1 ∧ IsProbabilityMeasure μ.2 ∧
    ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (tau p id id μ.1 μ.2) ≤ (tau p id id ν₁ ν₂) := by
  let _i : TopologicalSpace G := (⊥ : TopologicalSpace G) 
  have : DiscreteTopology G := ⟨rfl⟩
  let T : ProbabilityMeasure G × ProbabilityMeasure G → ℝ := 
    fun ⟨μ₁, μ₂⟩ ↦ (tau p id id μ₁ μ₂)
  have T_cont : Continuous T := by apply continuous_tau_restrict_probabilityMeasure
  have : Inhabited G := ⟨0⟩ 
  obtain ⟨μ, _, hμ⟩ := @IsCompact.exists_isMinOn ℝ (ProbabilityMeasure G × ProbabilityMeasure G)
                          _ _ _ _ Set.univ isCompact_univ ⟨default, trivial⟩ T T_cont.continuousOn
  use ⟨μ.1.toMeasure, μ.2.toMeasure⟩
  refine ⟨μ.1.prop, μ.2.prop, ?_⟩
  intro ν₁ ν₂ Pν₁ Pν₂
  rw [isMinOn_univ_iff] at hμ
  let ν : ProbabilityMeasure G × ProbabilityMeasure G := ⟨⟨ν₁, Pν₁⟩, ν₂, Pν₂⟩
  exact hμ ν

lemma tau_minimizer_exists [MeasurableSingletonClass G] :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
    Measurable X₁ ∧ Measurable X₂ ∧ IsProbabilityMeasure (ℙ : Measure Ω) ∧
    tau_minimizes p X₁ X₂ := by
  let μ := (tau_min_exists_measure p).choose
  have : IsProbabilityMeasure μ.1 := (tau_min_exists_measure p).choose_spec.1
  have : IsProbabilityMeasure μ.2 := (tau_min_exists_measure p).choose_spec.2.1
  have P : IsProbabilityMeasure (μ.1.prod μ.2) := by infer_instance
  let M : MeasureSpace (G × G) := ⟨μ.1.prod μ.2⟩
  refine ⟨G × G, M, Prod.fst, Prod.snd, measurable_fst, measurable_snd, P, ?_⟩
  intro ν₁ ν₂ h₁ h₂
  have A : (tau p (@Prod.fst G G) (@Prod.snd G G) ℙ ℙ) = (tau p id id μ.1 μ.2) :=
    ProbabilityTheory.IdentDistrib.tau_eq p IdentDistrib.fst_id IdentDistrib.snd_id
  convert (tau_min_exists_measure p).choose_spec.2.2 ν₁ ν₂ h₁ h₂

variable [MeasureSpace Ω] [hΩ₁ : MeasureSpace Ω'₁] [hΩ₂ : MeasureSpace Ω'₂]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
  [IsProbabilityMeasure (ℙ : Measure Ω'₁)] [IsProbabilityMeasure (ℙ : Measure Ω'₂)]
  {X₁ : Ω → G} {X₂ : Ω → G} {X₁' : Ω'₁ → G} {X₂' : Ω'₂ → G}

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] [Finite G]
  [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma is_tau_min (h : tau_minimizes p X₁ X₂) (h1 : Measurable X₁') (h2 : Measurable X₂') :
    (tau p X₁ X₂ ℙ ℙ) ≤ (tau p X₁' X₂' ℙ ℙ) := by
  let ν₁ := (ℙ : Measure Ω'₁).map X₁'
  let ν₂ := (ℙ : Measure Ω'₂).map X₂'
  have B : (tau p X₁' X₂' ℙ ℙ) = (tau p id id ν₁ ν₂) :=
    (identDistrib_id_right h1.aemeasurable).tau_eq p (identDistrib_id_right h2.aemeasurable)
  convert h ν₁ ν₂ (Measure.isProbabilityMeasure_map h1.aemeasurable)
    (Measure.isProbabilityMeasure_map h2.aemeasurable)

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] [Finite G]
  [IsProbabilityMeasure (ℙ : Measure Ω)] in

lemma distance_ge_of_min (h : tau_minimizes p X₁ X₂) (h1 : Measurable X₁') (h2 : Measurable X₂') :
    (rdist X₁ X₂ ℙ ℙ) - p.η * ((rdist p.X₀₁ X₁' ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ)) - p.η * ((rdist p.X₀₂ X₂' ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))
      ≤ (rdist X₁' X₂' ℙ ℙ) := by
  have Z := is_tau_min p h h1 h2
  simp [tau] at Z
  linarith

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] [Finite G]
  [IsProbabilityMeasure (ℙ : Measure Ω)] in

lemma distance_ge_of_min' {Ω'₁ Ω'₂ : Type*} (h : tau_minimizes p X₁ X₂)
    [MeasurableSpace Ω'₁] [MeasurableSpace Ω'₂] {μ : Measure Ω'₁} {μ' : Measure Ω'₂}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {X₁' : Ω'₁ → G} {X₂' : Ω'₂ → G}
    (h1 : Measurable X₁') (h2 : Measurable X₂') :
    (rdist X₁ X₂ ℙ ℙ) - p.η * ((rdist p.X₀₁ X₁' ℙ μ) - (rdist p.X₀₁ X₁ ℙ ℙ))
      - p.η * ((rdist p.X₀₂ X₂' ℙ μ') - (rdist p.X₀₂ X₂ ℙ ℙ)) ≤ (rdist X₁' X₂' μ μ') := by
  set M1 : MeasureSpace Ω'₁ := { volume := μ }
  set M2 : MeasureSpace Ω'₂ := { volume := μ' }
  exact distance_ge_of_min p h h1 h2

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
  [IsProbabilityMeasure (ℙ : Measure Ω)] in

lemma condRuzsaDistance_ge_of_min [MeasurableSingletonClass G]
    [Finite S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Finite T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (h : tau_minimizes p X₁ X₂) (h1 : Measurable X₁') (h2 : Measurable X₂')
    (Z : Ω'₁ → S) (W : Ω'₂ → T) (hZ : Measurable Z) (hW : Measurable W) :
    (rdist X₁ X₂ ℙ ℙ) - p.η * ((condRuzsaDist' p.X₀₁ X₁' Z ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ))
      - p.η * ((condRuzsaDist' p.X₀₂ X₂' W ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)) ≤ (condRuzsaDist X₁' Z X₂' W ℙ ℙ) := by
  have hz (a : ℝ) : a = ∑ z ∈ FiniteRange.toFinset Z, Measure.real ℙ (Z ⁻¹' {z}) * a := by
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hZ (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    rw [FiniteRange.real_full hZ]
    simp
  have hw (a : ℝ) : a = ∑ w ∈ FiniteRange.toFinset W, Measure.real ℙ (W ⁻¹' {w}) * a := by
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hW (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    rw [FiniteRange.real_full hW]
    simp
  rw [condRuzsaDist_eq_sum h1 hZ h2 hW, condRuzsaDist'_eq_sum h1 hZ, hz (rdist X₁ X₂ ℙ ℙ),
    hz (rdist p.X₀₁ X₁ ℙ ℙ), hz (p.η * ((condRuzsaDist' p.X₀₂ X₂' W ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))),
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [condRuzsaDist'_eq_sum h2 hW, hw (rdist p.X₀₂ X₂ ℙ ℙ),
    hw (Measure.real ℙ (Z ⁻¹' {z}) * (rdist X₁ X₂ ℙ ℙ) - p.η * (Measure.real ℙ (Z ⁻¹' {z}) *
      (rdist p.X₀₁ X₁' ℙ (ℙ[|Z ← z])) - Measure.real ℙ (Z ⁻¹' {z}) * (rdist p.X₀₁ X₁ ℙ ℙ))),
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro w _
  rcases eq_or_ne (Measure.real ℙ (Z ⁻¹' {z})) 0 with hpz | hpz
  · simp [hpz]
  rcases eq_or_ne (Measure.real ℙ (W ⁻¹' {w})) 0 with hpw | hpw
  · simp [hpw]
  set μ := (hΩ₁.volume)[|Z ← z]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_real hpz
  set μ' := ℙ[|W ← w]
  have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure_of_real hpw
  suffices (rdist X₁ X₂ ℙ ℙ) - p.η * ((rdist p.X₀₁ X₁' volume μ) - (rdist p.X₀₁ X₁ ℙ ℙ)) -
    p.η * ((rdist p.X₀₂ X₂' volume μ') - (rdist p.X₀₂ X₂ ℙ ℙ)) ≤ (rdist X₁' X₂' μ μ') by
    replace this := mul_le_mul_of_nonneg_left this
      (show 0 ≤ (Measure.real ℙ (Z ⁻¹' {z})) * (Measure.real ℙ (W ⁻¹' {w})) by positivity)
    convert this using 1
    ring
  exact distance_ge_of_min' p h h1 h2
end

/- PFR.HundredPercent -/
/-
# The 100% version of entropic PFR

Here we show entropic PFR in the case of doubling constant zero.

## Main results

* `exists_isUniform_of_rdist_eq_zero` : If $d[X_1;X_2]=0$, then there exists a subgroup $H \leq G$
such that $d[X_1;U_H] = d[X_2;U_H] = 0$.
-/

noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {G : Type*} [MeasureSpace Ω] [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] {X : Ω → G}

def symmGroup (X : Ω → G) (hX : Measurable X) : AddSubgroup G where
  carrier := {x | IdentDistrib X (fun ω ↦ X ω + x)}
  add_mem' := by
    intro x y hx hy
    let f : G → G := fun g ↦ g + x
    have : IdentDistrib (f ∘ X) (fun ω ↦ f (X ω + y)) := hy.comp <| measurable_add_const _
    have Z := hx.trans this
    dsimp
    convert Z using 1
    ext ω
    simp only [f]
    abel
  zero_mem' := by simpa using IdentDistrib.refl hX.aemeasurable
  neg_mem' := by
    intro x hx
    dsimp at hx ⊢
    let f : G → G := fun g ↦ g - x
    have : IdentDistrib (f ∘ X) (fun ω ↦ f (X ω + x)) := hx.comp <| measurable_sub_const' _
    convert this.symm using 1
    · ext ω
      simp only [f]
      abel
    · ext ω
      simp only [Function.comp_apply, f]
      abel_nf

@[simp] lemma mem_symmGroup (hX : Measurable X) {x : G} :
    x ∈ symmGroup X hX ↔ IdentDistrib X (fun ω ↦ X ω + x) := Iff.rfl

lemma ProbabilityTheory.IdentDistrib.symmGroup_eq {Ω' : Type*} [MeasureSpace Ω'] {X' : Ω' → G}
    (hX : Measurable X) (hX' : Measurable X') (h : IdentDistrib X X') :
    symmGroup X hX = symmGroup X' hX' := by
  ext x
  have A : Measurable (fun a ↦ a + x) := measurable_add_const _
  exact ⟨fun H ↦ h.symm.trans (H.trans (h.comp A)), fun H ↦ h.trans (H.trans (h.symm.comp A))⟩

variable [Finite G] [MeasurableSingletonClass G] [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma sub_mem_symmGroup (hX : Measurable X) (hdist : (rdist X X ℙ ℙ) = 0)
    {x y : G} (hx : ℙ (X ⁻¹' {x}) ≠ 0) (hy : ℙ (X ⁻¹' {y}) ≠ 0) : x - y ∈ symmGroup X hX := by

  rcases ProbabilityTheory.independent_copies_two hX hX with
    ⟨Ω', mΩ', X', Y', hP, hX', hY', h_indep, hidX, hidY⟩
  rw [hidX.symm.symmGroup_eq hX hX']
  have A : (ProbabilityTheory.condEntropy (X' - Y') Y' ℙ) = (ProbabilityTheory.entropy (X' - Y') ℙ) := calc
    (ProbabilityTheory.condEntropy (X' - Y') Y' ℙ) = (ProbabilityTheory.condEntropy X' Y' ℙ) := condEntropy_sub_right hX' hY'
    _ = (ProbabilityTheory.entropy X' ℙ) := h_indep.condEntropy_eq_entropy hX' hY'
    _ = (ProbabilityTheory.entropy (X' - Y') ℙ) := by
      have : (rdist X' Y' ℙ ℙ) = 0 := by rwa [hidX.rdist_congr hidY]
      rw [h_indep.rdist_eq hX' hY', ← (hidX.trans hidY.symm).entropy_congr] at this
      linarith
  have I : IndepFun (X' - Y') Y' := by
    refine (mutualInfo_eq_zero (by fun_prop) hY').1 ?_
    rw [mutualInfo_eq_entropy_sub_condEntropy (by fun_prop) hY', A, sub_self]
  have M : ∀ c, ℙ (Y' ⁻¹' {c}) ≠ 0 → IdentDistrib (fun ω ↦ X' ω - c) (X' - Y') := by
    intro c hc
    let F := fun ω ↦ X' ω - c
    refine ⟨by fun_prop, by fun_prop, ?_⟩
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, Measure.map_apply (by fun_prop) hs]
    have : ℙ (F ⁻¹' s) * ℙ (Y' ⁻¹' {c}) = ℙ ((X' - Y') ⁻¹' s) * ℙ (Y' ⁻¹' {c}) := by calc
      ℙ (F ⁻¹' s) * ℙ (Y' ⁻¹' {c}) = ℙ (F ⁻¹' s ∩ Y' ⁻¹' {c}) := by
        have hFY' : IndepFun F Y' := by
          have : Measurable (fun z ↦ z - c) := measurable_sub_const' c
          apply h_indep.comp this measurable_id
        rw [indepFun_iff_measure_inter_preimage_eq_mul.1 hFY' _ _ hs .of_discrete]
      _ = ℙ ((X' - Y') ⁻¹' s ∩ Y' ⁻¹' {c}) := by
        congr 1; ext z; simp +contextual [F]
      _ = ℙ ((X' - Y') ⁻¹' s) * ℙ (Y' ⁻¹' {c}) := by
        rw [indepFun_iff_measure_inter_preimage_eq_mul.1 I _ _ hs .of_discrete]
    rwa [ENNReal.mul_left_inj hc (measure_ne_top ℙ _)] at this
  have J : IdentDistrib (fun ω ↦ X' ω - x) (fun ω ↦ X' ω - y) := by
    have Px : ℙ (Y' ⁻¹' {x}) ≠ 0 := by
      convert hx; exact hidY.measure_mem_eq .of_discrete
    have Py : ℙ (Y' ⁻¹' {y}) ≠ 0 := by
      convert hy; exact hidY.measure_mem_eq .of_discrete
    exact (M x Px).trans (M y Py).symm
  have : IdentDistrib X' (fun ω ↦ X' ω + (x - y)) := by
    have : Measurable (fun c ↦ c + x) := measurable_add_const x
    convert J.comp this using 1
    · ext ω; simp
    · ext ω; simp; abel
  exact this

lemma isUniform_sub_const_of_rdist_eq_zero (hX : Measurable X) (hdist : (rdist X X ℙ ℙ) = 0) {x₀ : G}
    (hx₀ : ℙ (X ⁻¹' {x₀}) ≠ 0) : IsUniform (symmGroup X hX) (fun ω ↦ X ω - x₀) where
  eq_of_mem := by
    have B c z : (fun ω ↦ X ω - c) ⁻¹' {z} = X ⁻¹' {c + z} := by
      ext w; simp [sub_eq_iff_eq_add']
    have A : ∀ (z : G), z ∈ symmGroup X hX →
        ℙ ((fun ω ↦ X ω - x₀) ⁻¹' {z}) = ℙ ((fun ω ↦ X ω - x₀) ⁻¹' {0}) := by
      intro z hz
      have : X ⁻¹' {x₀ + z} = (fun ω ↦ X ω - z) ⁻¹' {x₀} := by simp [B, add_comm]
      simp_rw [B, add_zero, this]
      have Z := (mem_symmGroup hX).1 (AddSubgroup.neg_mem (symmGroup X hX) hz)
      simp [← sub_eq_add_neg] at Z
      exact Z.symm.measure_mem_eq .of_discrete
    intro x hx y hy
    rw [A x hx, A y hy]
  measure_preimage_compl := by
    apply (measure_preimage_eq_zero_iff_of_countable (Set.to_countable _)).2
    intro x hx
    contrapose! hx
    have B : (fun ω ↦ X ω - x₀) ⁻¹' {x} = X ⁻¹' {x₀ + x} := by
      ext w; simp [sub_eq_iff_eq_add']
    rw [B] at hx
    simpa using sub_mem_symmGroup hX hdist hx hx₀

theorem exists_isUniform_of_rdist_self_eq_zero (hX : Measurable X) (hdist : (rdist X X ℙ ℙ) = 0) :
    ∃ H : AddSubgroup G, ∃ U : Ω → G, Measurable U ∧ IsUniform H U ∧ (rdist X U ℙ ℙ) = 0 := by
  
  obtain ⟨x₀, h₀⟩ : ∃ x₀, ℙ (X ⁻¹' {x₀}) ≠ 0 := by
    by_contra! h
    have A a : (ℙ : Measure Ω).map X {a} = 0 := by
      rw [Measure.map_apply hX .of_discrete]
      exact h _
    have B : (ℙ : Measure Ω).map X = 0 := by
      rw [← Measure.sum_smul_dirac (μ := (ℙ : Measure Ω).map X)]
      simp [A]
    have : IsProbabilityMeasure ((ℙ : Measure Ω).map X) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    exact IsProbabilityMeasure.ne_zero _ B
  refine ⟨symmGroup X hX, fun ω ↦ X ω - x₀, hX.sub_const _,
    isUniform_sub_const_of_rdist_eq_zero hX hdist h₀, ?_⟩
  simp_rw [sub_eq_add_neg, ← Pi.add_def, rdist_add_const hX hX, hdist]

theorem exists_isUniform_of_rdist_eq_zero
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')] {X' : Ω' → G}
    (hX : Measurable X) (hX' : Measurable X') (hdist : (rdist X X' ℙ ℙ) = 0) :
    ∃ H : AddSubgroup G, ∃ U : Ω → G,
      Measurable U ∧ IsUniform H U ∧ (rdist X U ℙ ℙ) = 0 ∧ (rdist X' U ℙ ℙ) = 0 := by
  have h' : (rdist X X ℙ ℙ) = 0 := by
    apply le_antisymm _ (rdist_nonneg hX hX)
    calc
      (rdist X X ℙ ℙ) ≤ (rdist X X' ℙ ℙ) + (rdist X' X ℙ ℙ) := rdist_triangle hX hX' hX
      _ = 0 := by rw [hdist, rdist_symm, hdist, zero_add]
  rcases exists_isUniform_of_rdist_self_eq_zero hX h' with ⟨H, U, hmeas, hunif, hd⟩
  refine ⟨H, U, hmeas, hunif, hd, ?_⟩
  apply le_antisymm _ (rdist_nonneg hX' hmeas)
  calc
    (rdist X' U ℙ ℙ) ≤ (rdist X' X ℙ ℙ) + (rdist X U ℙ ℙ) := rdist_triangle hX' hX hmeas
    _ = 0 := by rw [hd, rdist_symm, hdist, zero_add]
end

/- PFR.Fibring -/
/-
# The fibring identity

The proof of the fibring identity, which is a key component of the proof of PFR.

## Main statement

* `sum_of_rdist_eq`: If $Y_1,Y_2,Y_3,Y_4$ are independent, then $d[Y_1; Y_2] + d[Y_3; Y_4]$ is equal
  to the sum of $$d[Y_1+Y_3; Y_2+Y_4] + d[Y_1|Y_1+Y_3; Y_2|Y_2+Y_4] $$ and
  $$ I[Y_1+Y_2 : Y_2 + Y_4 | Y_1+Y_2+Y_3+Y_4].$$

-/

noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory Function

section GeneralFibring

variable {H : Type*} [AddCommGroup H] [Countable H] [hH : MeasurableSpace H]
  [MeasurableSingletonClass H]
  {H' : Type*} [AddCommGroup H'] [Countable H'] [hH' : MeasurableSpace H']
  [MeasurableSingletonClass H']
  (π : H →+ H')
variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

lemma rdist_of_indep_eq_sum_fibre {Z_1 Z_2 : Ω → H} (h : IndepFun Z_1 Z_2 μ)
    (h1 : Measurable Z_1) (h2 : Measurable Z_2) [FiniteRange Z_1] [FiniteRange Z_2] :
    (rdist Z_1 Z_2 μ μ) = (rdist (π ∘ Z_1) (π ∘ Z_2) μ μ) + (condRuzsaDist Z_1 (π∘Z_1) Z_2 (π∘Z_2) μ μ)
      + (ProbabilityTheory.condMutualInfo (Z_1-Z_2) ((_root_.prod (π∘Z_1) (π∘Z_2))) (π∘(Z_1 - Z_2)) μ) := by
  have hπ : Measurable π := .of_discrete
  have step1 : (rdist Z_1 Z_2 μ μ) = (rdist (π ∘ Z_1) (π ∘ Z_2) μ μ) +
      (ProbabilityTheory.condEntropy ((Z_1 - Z_2)) (π ∘ (Z_1 - Z_2)) μ) - (ProbabilityTheory.condEntropy Z_1 (π ∘ Z_1) μ) / 2 - (ProbabilityTheory.condEntropy Z_2 (π ∘ Z_2) μ) / 2 := by
    have hsub : (ProbabilityTheory.condEntropy ((Z_1 - Z_2)) (π ∘ (Z_1 - Z_2)) μ) = (ProbabilityTheory.entropy ((Z_1 - Z_2)) μ) - (ProbabilityTheory.entropy (π ∘ (Z_1 - Z_2)) μ) :=
      condEntropy_comp_self (by fun_prop) hπ
    rw [h.rdist_eq h1 h2, (h.comp hπ hπ).rdist_eq (hπ.comp h1) (hπ.comp h2),
      condEntropy_comp_self h1 hπ, condEntropy_comp_self h2 hπ, hsub, map_comp_sub π]
    ring_nf
  have m0 : Measurable (fun x ↦ (x, π x)) := .of_discrete
  have h' : IndepFun ((_root_.prod Z_1 (π ∘ Z_1))) ((_root_.prod Z_2 (π ∘ Z_2))) μ := h.comp m0 m0
  have m1 : Measurable (Z_1 - Z_2) := h1.sub h2
  have m2 : Measurable ((_root_.prod (↑π ∘ Z_1) (↑π ∘ Z_2))) := (hπ.comp h1).prodMk (hπ.comp h2)
  have m3 : Measurable (↑π ∘ (Z_1 - Z_2)) := hπ.comp m1
  have entroplem : (ProbabilityTheory.condEntropy (Z_1 - Z_2) ((_root_.prod ((_root_.prod (↑π ∘ Z_1) (↑π ∘ Z_2))) (↑π ∘ (Z_1 - Z_2)))) μ)
      = (ProbabilityTheory.condEntropy (Z_1 - Z_2) ((_root_.prod (↑π ∘ Z_1) (↑π ∘ Z_2))) μ) := by
    rw [map_comp_sub π]
    let f : H' × H' → (H' × H') × H' := fun (x,y) ↦ ((x,y), x - y)
    have hf : Injective f := fun _ _ h ↦ (Prod.ext_iff.1 h).1
    have mf : Measurable f := measurable_id.prodMk measurable_sub
    refine condEntropy_of_injective' μ m1 m2 f hf (mf.comp m2)
  rw [step1, condMutualInfo_eq' m1 m2 m3, entroplem,
    condRuzsaDist_of_indep h1 (hπ.comp h1) h2 (hπ.comp h2) μ h']
  ring_nf

lemma rdist_le_sum_fibre {Z_1 : Ω → H} {Z_2 : Ω' → H}
  (h1 : Measurable Z_1) (h2 : Measurable Z_2) [FiniteRange Z_1] [FiniteRange Z_2] :
  (rdist (π ∘ Z_1) (π ∘ Z_2) μ μ') + (condRuzsaDist Z_1 (π∘Z_1) Z_2 (π∘Z_2) μ μ') ≤ (rdist Z_1 Z_2 μ μ') := by
  obtain ⟨ν, W_1, W_2, hν, m1, m2, hi, hi1, hi2, _, _⟩ := independent_copies_finiteRange h1 h2 μ μ'
  have hπ : Measurable π := .of_discrete
  have hφ : Measurable (fun x ↦ (x, π x)) := .of_discrete
  have hπ1 : IdentDistrib ((_root_.prod Z_1 (π ∘ Z_1))) ((_root_.prod W_1 (π ∘ W_1))) μ ν := hi1.symm.comp hφ
  have hπ2 : IdentDistrib ((_root_.prod Z_2 (π ∘ Z_2))) ((_root_.prod W_2 (π ∘ W_2))) μ' ν := hi2.symm.comp hφ
  rw [← hi1.rdist_congr hi2, ← (hi1.comp hπ).rdist_congr (hi2.comp hπ),
    rdist_of_indep_eq_sum_fibre π hi m1 m2,
    condRuzsaDist_of_copy h1 (hπ.comp h1) h2 (hπ.comp h2) m1 (hπ.comp m1) m2 (hπ.comp m2) hπ1 hπ2]
  exact le_add_of_nonneg_right (condMutualInfo_nonneg (by fun_prop) (by fun_prop))

end GeneralFibring

variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma sum_of_rdist_eq_step_condRuzsaDist {Y : Fin 4 → Ω → G} (h_indep : iIndepFun Y μ)
    (h_meas : ∀ i, Measurable (Y i)) :
    (condRuzsaDist ((_root_.prod (Y 0) (Y 2))) (Y 0 - Y 2) ((_root_.prod (Y 1) (Y 3))) (Y 1 - Y 3) μ μ)
      = (condRuzsaDist (Y 0) (Y 0 - Y 2) (Y 1) (Y 1 - Y 3) μ μ) := by
  let Y' : Fin 4 → Ω → G
    | 0 => Y 0
    | 1 => Y 1
    | 2 => Y 0 - Y 2
    | 3 => Y 1 - Y 3
  let f : (G × G) → (G × G) := fun (g, h) ↦ (g, g - h)
  have hf : Measurable f := .of_discrete
  have h_indep' : IndepFun ((_root_.prod (Y' 0) (Y' 2))) ((_root_.prod (Y' 1) (Y' 3))) μ :=
    (h_indep.indepFun_prodMk_prodMk h_meas 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)).comp hf hf
  have h_meas' : ∀ i, Measurable (Y' i)
    | 0 => h_meas 0
    | 1 => h_meas 1
    | 2 => (h_meas 0).sub (h_meas 2)
    | 3 => (h_meas 1).sub (h_meas 3)
  have h' (i j : Fin 4) : (_root_.prod (Y i) (Y j)) = (_root_.prod (Y i) (Y i - (Y i - Y j))) := by simp only [sub_sub_cancel]
  rw [h' 0 2, h' 1 3]
  exact condRuzsaDist_of_inj_map Y' h_indep' h_meas'
    ((AddMonoidHom.fst G G).prod ((AddMonoidHom.fst G G) - (AddMonoidHom.snd G G)))
    (fun _ _ _ h ↦ (Prod.ext_iff.1 h).1)

lemma sum_of_rdist_eq_step_condMutualInfo {Y : Fin 4 → Ω → G}
    (h_meas : ∀ i, Measurable (Y i)) :
    (ProbabilityTheory.condMutualInfo ((_root_.prod (Y 0 - Y 1) (Y 2 - Y 3))) ((_root_.prod (Y 0 - Y 2) (Y 1 - Y 3))) (Y 0 - Y 1 - (Y 2 - Y 3)) μ) =
    (ProbabilityTheory.condMutualInfo (Y 0 - Y 1) (Y 1 - Y 3) (Y 0 - Y 1 - Y 2 + Y 3) μ) := by
  suffices (ProbabilityTheory.condMutualInfo ((_root_.prod (Y 0 - Y 1) (Y 2 - Y 3))) ((_root_.prod (Y 0 - Y 2) (Y 1 - Y 3))) (Y 0 - Y 1 - (Y 2 - Y 3)) μ) =
    (ProbabilityTheory.condMutualInfo (Y 0 - Y 1) (Y 1 - Y 3) (Y 0 - Y 1 - (Y 2 - Y 3)) μ) by convert this using 2; abel
  symm
  have hm (f : G → G → G × G) {a b i j k l : Fin 4} :
    Measurable (uncurry f ∘ (_root_.prod (Y i - Y j - (Y k - Y l)) (Y a - Y b))) := by fun_prop
  have hmf : Measurable fun ω ↦ ((Y 0 - Y 1) ω, (Y 0 - Y 1) ω - (Y 0 - Y 1 - (Y 2 - Y 3)) ω) :=
    hm (fun z x ↦ (x, x - z))
  have hmg : Measurable fun ω ↦ ((Y 1 - Y 3) ω + (Y 0 - Y 1 - (Y 2 - Y 3)) ω, (Y 1 - Y 3) ω) :=
    hm (fun z x ↦ (x + z, x))
  have hmij {i j : Fin 4} : Measurable (Y i - Y j) := (h_meas _).sub (h_meas _)
  have hm0123 {i j k l : Fin 4} : Measurable (Y i - Y j - (Y k - Y l)) :=
    ((h_meas _).sub (h_meas _)).sub ((h_meas _).sub (h_meas _))
  rw [← condMutualInfo_of_inj_map hmij hmij hm0123 (fun z x ↦ (x, x - z)),
    condMutualInfo_comm hmf hmij,
    ← condMutualInfo_of_inj_map hmij hmf hm0123 (fun z x ↦ (x + z, x)),
    condMutualInfo_comm hmg hmf]
  · congr! 3 with ω
    · simp
    · rw [sub_sub, add_sub_left_comm, ← sub_sub]
      simp
  · exact fun _ _ _ h ↦ (Prod.ext_iff.1 h).2
  exact fun _ _ _ h ↦ (Prod.ext_iff.1 h).1

lemma sum_of_rdist_eq (Y : Fin 4 → Ω → G) (h_indep : iIndepFun Y μ)
  (h_meas : ∀ i, Measurable (Y i)) :
    (rdist (Y 0) (Y 1) μ μ) + (rdist (Y 2) (Y 3) μ μ)
      = (rdist ((Y 0) - (Y 2)) ((Y 1) - (Y 3)) μ μ)
        + (condRuzsaDist (Y 0) ((Y 0) - (Y 2)) (Y 1) ((Y 1) - (Y 3)) μ μ)
        + (ProbabilityTheory.condMutualInfo ((Y 0) - (Y 1)) ((Y 1) - (Y 3)) ((Y 0) - (Y 1) - (Y 2) + (Y 3)) μ) := by
  let π : G × G →+ G := (AddMonoidHom.fst G G) - (AddMonoidHom.snd G G)
  have hπ {W_1 W_2 : Ω → G} : π ∘ (_root_.prod W_1 W_2) = W_1 - W_2 := rfl
  let Z_1 : Ω → G × G := (_root_.prod (Y 0) (Y 2))
  let Z_2 : Ω → G × G := (_root_.prod (Y 1) (Y 3))
  have hZ : Z_1 - Z_2 = (_root_.prod (Y 0 - Y 1) (Y 2 - Y 3)) := rfl
  have m1 : Measurable Z_1 := (h_meas 0).prodMk (h_meas 2)
  have m2 : Measurable Z_2 := (h_meas 1).prodMk (h_meas 3)
  have h_indep_0 : IndepFun (Y 0) (Y 1) μ := h_indep.indepFun (by decide)
  have h_indep_2 : IndepFun (Y 2) (Y 3) μ := h_indep.indepFun (by decide)
  have h_indep_Z : IndepFun Z_1 Z_2 μ := h_indep.indepFun_prodMk_prodMk h_meas
    0 2 1 3 (by decide) (by decide) (by decide) (by decide)
  have h_indep_sub : IndepFun (Y 0 - Y 1) (Y 2 - Y 3) μ :=
    h_indep.indepFun_sub_sub h_meas 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
  have msub (i j : Fin 4) : Measurable (Y i - Y j) := (h_meas i).sub (h_meas j)
  have h_add : (rdist Z_1 Z_2 μ μ) = (rdist (Y 0) (Y 1) μ μ) + (rdist (Y 2) (Y 3) μ μ) := by
    rw [h_indep_0.rdist_eq (h_meas 0) (h_meas 1), h_indep_2.rdist_eq (h_meas 2) (h_meas 3),
      h_indep_Z.rdist_eq m1 m2, hZ,
      (entropy_pair_eq_add (h_meas 0) (h_meas 2)).2 (h_indep.indepFun (by decide)),
      (entropy_pair_eq_add (h_meas 1) (h_meas 3)).2 (h_indep.indepFun (by decide)),
      (entropy_pair_eq_add (msub 0 1) (msub 2 3)).2 h_indep_sub]
    ring_nf
  rw [← h_add, rdist_of_indep_eq_sum_fibre π h_indep_Z m1 m2]
  simp only [hπ, hZ]
  rw [sum_of_rdist_eq_step_condRuzsaDist h_indep h_meas,
    sum_of_rdist_eq_step_condMutualInfo h_meas]

lemma sum_of_rdist_eq_char_2
  [Module (ZMod 2) G] (Y : Fin 4 → Ω → G) (h_indep : iIndepFun Y μ)
  (h_meas : ∀ i, Measurable (Y i)) :
    (rdist (Y 0) (Y 1) μ μ) + (rdist (Y 2) (Y 3) μ μ)
      = (rdist ((Y 0) + (Y 2)) ((Y 1) + (Y 3)) μ μ)
        + (condRuzsaDist (Y 0) ((Y 0) + (Y 2)) (Y 1) ((Y 1) + (Y 3)) μ μ)
        + (ProbabilityTheory.condMutualInfo ((Y 0) + (Y 1)) ((Y 1) + (Y 3)) ((Y 0) + (Y 1) + (Y 2) + (Y 3)) μ) := by
  simpa [ZModModule.sub_eq_add] using sum_of_rdist_eq Y h_indep h_meas

end

/- PFR.FirstEstimate -/
/-
# First estimate

The first estimate on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ are independent random variables, with $X_1,\tilde X_1$ copies
  of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $k := d[X_1;X_2]$
* $I_1 := I [X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2]$

## Main results

* `first_estimate` : $I_1 ≤ 2 η k$
* `ent_ofsum_le` : $H[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} H[X_1]+\tfrac{1}{2} H[X_2] +
  (2 + \eta) k - I_1.$
-/

noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory

variable {G : Type*} [addgroup : AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')
variable (h_indep : iIndepFun ![X₁, X₂, X₂', X₁'])
variable (h_min : tau_minimizes p X₁ X₂)

include h_indep hX₁ hX₂ hX₁' hX₂' h₁ h₂ in

lemma rdist_add_rdist_add_condMutual_eq [Module (ZMod 2) G] :
    (rdist (X₁ + X₂') (X₂ + X₁') ℙ ℙ) + (condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') ℙ ℙ)
      + (ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ) = 2 * ((rdist X₁ X₂ ℙ ℙ)) := by
  cases nonempty_fintype G
  have h0 : ![X₁, X₂, X₂', X₁'] 0 = X₁ := rfl
  have h1 : ![X₁, X₂, X₂', X₁'] 1 = X₂ := rfl
  have h2 : ![X₁, X₂, X₂', X₁'] 2 = X₂' := rfl
  have h3 : ![X₁, X₂, X₂', X₁'] 3 = X₁' := rfl
  have h := sum_of_rdist_eq_char_2 ![X₁, X₂, X₂', X₁'] h_indep
    (fun i => by fin_cases i <;> assumption)
  rw [h0, h1, h2, h3] at h
  have heq : (rdist X₂' X₁' ℙ ℙ) = ((rdist X₁ X₂ ℙ ℙ)) := by
    rw [rdist_symm]
    apply h₁.symm.rdist_congr h₂.symm
  rw [heq] at h
  convert h.symm using 1
  · congr 2 <;> abel
  · ring

include h_min hX₁ hX₂ hX₁' hX₂' in

lemma rdist_of_sums_ge :
    (rdist (X₁ + X₂') (X₂ + X₁') ℙ ℙ) ≥
      ((rdist X₁ X₂ ℙ ℙ)) - p.η * ((rdist p.X₀₁ (X₁ + X₂') ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ))
        - p.η * ((rdist p.X₀₂ (X₂ + X₁') ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)) :=
  distance_ge_of_min _ h_min (hX₁.add hX₂') (hX₂.add hX₁')

include h_min hX₁ hX₂ hX₁' hX₂' in

lemma condRuzsaDist_of_sums_ge :
    (condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') ℙ ℙ) ≥
      ((rdist X₁ X₂ ℙ ℙ)) - p.η * ((condRuzsaDist' p.X₀₁ X₁ (X₁ + X₂') ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ))
        - p.η * ((condRuzsaDist' p.X₀₂ X₂ (X₂ + X₁') ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)) :=
  condRuzsaDistance_ge_of_min _ h_min hX₁ hX₂ _ _ (by fun_prop) (by fun_prop)

variable [Module (ZMod 2) G]

include hX₁ hX₂' h_indep h₂ in

lemma diff_rdist_le_1 [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] :
    (rdist p.X₀₁ (X₁ + X₂') ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) ≤ ((rdist X₁ X₂ ℙ ℙ))/2 + (ProbabilityTheory.entropy X₂ ℙ)/4 - (ProbabilityTheory.entropy X₁ ℙ)/4 := by
  have h : IndepFun X₁ X₂' := by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide)
  convert condRuzsaDist_diff_le' ℙ p.hmeas1 hX₁ hX₂' h using 4
  · exact h₂.rdist_congr_right hX₁.aemeasurable
  · exact h₂.entropy_congr

include hX₁' hX₂ h_indep h₁ in

lemma diff_rdist_le_2 [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    (rdist p.X₀₂ (X₂ + X₁') ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ) ≤ ((rdist X₁ X₂ ℙ ℙ))/2 + (ProbabilityTheory.entropy X₁ ℙ)/4 - (ProbabilityTheory.entropy X₂ ℙ)/4 := by
  have h : IndepFun X₂ X₁' := by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide)
  convert condRuzsaDist_diff_le' ℙ p.hmeas2 hX₂ hX₁' h using 4
  · rw [rdist_symm]
    exact h₁.rdist_congr_right hX₂.aemeasurable
  · exact h₁.entropy_congr

include h_indep hX₁ hX₂' h₂ in

lemma diff_rdist_le_3 [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] :
    (condRuzsaDist' p.X₀₁ X₁ (X₁ + X₂') ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) ≤ ((rdist X₁ X₂ ℙ ℙ))/2 + (ProbabilityTheory.entropy X₁ ℙ)/4 - (ProbabilityTheory.entropy X₂ ℙ)/4 := by
  have h : IndepFun X₁ X₂' := by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide)
  convert condRuzsaDist_diff_le''' ℙ p.hmeas1 hX₁ hX₂' h using 3
  · rw [h₂.rdist_congr_right hX₁.aemeasurable]
  · apply h₂.entropy_congr

include h_indep hX₂ hX₁' h₁

lemma diff_rdist_le_4 [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    (condRuzsaDist' p.X₀₂ X₂ (X₂ + X₁') ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ) ≤ ((rdist X₁ X₂ ℙ ℙ))/2 + (ProbabilityTheory.entropy X₂ ℙ)/4 - (ProbabilityTheory.entropy X₁ ℙ)/4 := by
  have h : IndepFun X₂ X₁' := by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide)
  convert condRuzsaDist_diff_le''' ℙ p.hmeas2 hX₂ hX₁' h using 3
  · rw [rdist_symm, h₁.rdist_congr_right hX₂.aemeasurable]
  · apply h₁.entropy_congr

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in

lemma first_estimate
    [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ)) ≤ 2 * p.η * ((rdist X₁ X₂ ℙ ℙ)) := by
  have v1 := rdist_add_rdist_add_condMutual_eq X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  have v2 := rdist_of_sums_ge p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_› ‹_›
  have v3 := condRuzsaDist_of_sums_ge p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› (by fun_prop) (by aesop)
  have v4 := mul_le_mul_of_nonneg_left (diff_rdist_le_1 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  have v5 := mul_le_mul_of_nonneg_left (diff_rdist_le_2 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  have v6 := mul_le_mul_of_nonneg_left (diff_rdist_le_3 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  have v7 := mul_le_mul_of_nonneg_left (diff_rdist_le_4 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  linarith [v1, v2, v3, v4, v5, v6, v7]

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in

lemma ent_ofsum_le
    [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    (ProbabilityTheory.entropy (X₁ + X₂ + X₁' + X₂') ℙ) ≤ (ProbabilityTheory.entropy X₁ ℙ)/2 + (ProbabilityTheory.entropy X₂ ℙ)/2 + (2+p.η)*((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ)) := by
  let D := (rdist (X₁ + X₂') (X₂ + X₁') ℙ ℙ)
  let Dcc := (condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') ℙ ℙ)
  let D1 := (rdist p.X₀₁ X₁ ℙ ℙ)
  let Dc1 := (condRuzsaDist' p.X₀₁ X₁ (X₁ + X₂') ℙ ℙ)
  let D2 := (rdist p.X₀₂ X₂ ℙ ℙ)
  let Dc2 := (condRuzsaDist' p.X₀₂ X₂ (X₂ + X₁') ℙ ℙ)
  have lem68 : D + Dcc + ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ)) = 2 * ((rdist X₁ X₂ ℙ ℙ)) :=
    rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep
  have lem610 : Dcc ≥ ((rdist X₁ X₂ ℙ ℙ)) - p.η * (Dc1 - D1) - p.η * (Dc2 - D2) :=
    condRuzsaDist_of_sums_ge p X₁ X₂ X₁' X₂' hX₁ hX₂ (by fun_prop) (by aesop) h_min
  have lem611c : Dc1 - D1 ≤ ((rdist X₁ X₂ ℙ ℙ)) / 2 + (ProbabilityTheory.entropy X₁ ℙ) / 4 - (ProbabilityTheory.entropy X₂ ℙ) / 4 :=
    diff_rdist_le_3 p X₁ X₂ X₁' X₂' hX₁ hX₂' h₂ h_indep
  have lem611d : Dc2 - D2 ≤ ((rdist X₁ X₂ ℙ ℙ)) / 2 + (ProbabilityTheory.entropy X₂ ℙ) / 4 - (ProbabilityTheory.entropy X₁ ℙ) / 4 :=
    diff_rdist_le_4 p X₁ X₂ X₁' X₂' hX₂ hX₁' h₁ h_indep
  have aux : D + ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ)) ≤ (1 + p.η) * ((rdist X₁ X₂ ℙ ℙ)) := by
    calc D + ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ))
       ≤ ((rdist X₁ X₂ ℙ ℙ)) + p.η * (Dc1 - D1) + p.η * (Dc2 - D2) := ?_
     _ ≤ ((rdist X₁ X₂ ℙ ℙ)) + p.η * (((rdist X₁ X₂ ℙ ℙ)) / 2 + (ProbabilityTheory.entropy X₁ ℙ) / 4 - (ProbabilityTheory.entropy X₂ ℙ) / 4) + p.η * (((rdist X₁ X₂ ℙ ℙ)) / 2 + (ProbabilityTheory.entropy X₂ ℙ) / 4 - (ProbabilityTheory.entropy X₁ ℙ) / 4) := ?_
     _ = (1 + p.η) * ((rdist X₁ X₂ ℙ ℙ)) := by ring
    · linarith
    · gcongr <;> exact p.hη.le
  have ent_sub_eq_ent_add : (ProbabilityTheory.entropy (X₁ + X₂' - (X₂ + X₁')) ℙ) = (ProbabilityTheory.entropy (X₁ + X₂' + (X₂ + X₁')) ℙ) := by
    simp [ZModModule.sub_eq_add]
  have rw₁ : X₁ + X₂' + (X₂ + X₁') = X₁ + X₂ + X₁' + X₂' := by abel
  have ind_aux : IndepFun (X₁ + X₂') (X₂ + X₁') := by
    exact iIndepFun.indepFun_add_add h_indep (fun i ↦ by fin_cases i <;> assumption) 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
  have ind : D = (ProbabilityTheory.entropy (X₁ + X₂' - (X₂ + X₁')) ℙ) - (ProbabilityTheory.entropy (X₁ + X₂') ℙ) / 2 - (ProbabilityTheory.entropy (X₂ + X₁') ℙ) / 2 :=
    ind_aux.rdist_eq (by fun_prop) (by fun_prop)
  rw [ind, ent_sub_eq_ent_add, rw₁] at aux
  have obs : (ProbabilityTheory.entropy (X₁ + X₂ + X₁' + X₂') ℙ) ≤ (ProbabilityTheory.entropy (X₁ + X₂') ℙ) / 2 + (ProbabilityTheory.entropy (X₂ + X₁') ℙ) / 2 + (1 + p.η) * ((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ)) := by
    linarith
  have rw₂ : (ProbabilityTheory.entropy (X₁ + X₂') ℙ) = ((rdist X₁ X₂ ℙ ℙ)) + (ProbabilityTheory.entropy X₁ ℙ)/2 + (ProbabilityTheory.entropy X₂ ℙ)/2 := by
    have HX₂_eq : (ProbabilityTheory.entropy X₂ ℙ) = (ProbabilityTheory.entropy X₂' ℙ) :=
      congr_arg (fun (μ : Measure G) ↦ measureEntropy (μ := μ)) h₂.map_eq
    have k_eq : ((rdist X₁ X₂ ℙ ℙ)) = (ProbabilityTheory.entropy (X₁ - X₂') ℙ) - (ProbabilityTheory.entropy X₁ ℙ) / 2 - (ProbabilityTheory.entropy X₂' ℙ) / 2 := by
      have k_eq_aux : ((rdist X₁ X₂ ℙ ℙ)) = (rdist X₁ X₂' ℙ ℙ) := h₂.rdist_congr_right hX₁.aemeasurable
      rw [k_eq_aux]
      exact (h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide)).rdist_eq hX₁ hX₂'
    rw [k_eq, ← ZModModule.sub_eq_add, ← HX₂_eq]
    ring
  have rw₃ : (ProbabilityTheory.entropy (X₂ + X₁') ℙ) = ((rdist X₁ X₂ ℙ ℙ)) + (ProbabilityTheory.entropy X₁ ℙ)/2 + (ProbabilityTheory.entropy X₂ ℙ)/2 := by
    have HX₁_eq : (ProbabilityTheory.entropy X₁ ℙ) = (ProbabilityTheory.entropy X₁' ℙ) :=
      congr_arg (fun (μ : Measure G) ↦ measureEntropy (μ := μ)) h₁.map_eq
    have k_eq' : ((rdist X₁ X₂ ℙ ℙ)) = (ProbabilityTheory.entropy (X₁' - X₂) ℙ) - (ProbabilityTheory.entropy X₁' ℙ) / 2 - (ProbabilityTheory.entropy X₂ ℙ) / 2 := by
      have k_eq_aux : ((rdist X₁ X₂ ℙ ℙ)) = (rdist X₁' X₂ ℙ ℙ) := h₁.rdist_congr_left hX₂.aemeasurable
      rw [k_eq_aux]
      exact (h_indep.indepFun (show (3 : Fin 4) ≠ 1 by decide)).rdist_eq hX₁' hX₂
    rw [add_comm X₂ X₁', k_eq', ← ZModModule.sub_eq_add, ← HX₁_eq]
    ring
  calc (ProbabilityTheory.entropy (X₁ + X₂ + X₁' + X₂') ℙ)
      ≤ (ProbabilityTheory.entropy (X₁ + X₂') ℙ) / 2 + (ProbabilityTheory.entropy (X₂ + X₁') ℙ) / 2 + (1 + p.η) * ((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ))  := obs
    _ = (((rdist X₁ X₂ ℙ ℙ)) + (ProbabilityTheory.entropy X₁ ℙ) / 2 + (ProbabilityTheory.entropy X₂ ℙ) / 2) / 2
        + (((rdist X₁ X₂ ℙ ℙ)) + (ProbabilityTheory.entropy X₁ ℙ) / 2 + (ProbabilityTheory.entropy X₂ ℙ) / 2) / 2 + (1 + p.η) * ((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ))  := by rw [rw₂, rw₃]
    _ = (ProbabilityTheory.entropy X₁ ℙ) / 2 + (ProbabilityTheory.entropy X₂ ℙ) / 2 + (2 + p.η) * ((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ))              := by ring
end

/- PFR.ForMathlib.FourVariables -/
noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} [MeasureSpace Ω]
  {G : Type*} [hG : MeasurableSpace G]

variable {Z₁ Z₂ Z₃ Z₄ : Ω → G} (h_indep : iIndepFun ![Z₁, Z₂, Z₃, Z₄])

include h_indep

lemma reindex_four_abdc :
    iIndepFun ![Z₁, Z₂, Z₄, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 1, 3, 2]
    invFun := ![0, 1, 3, 2]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_acbd :
    iIndepFun ![Z₁, Z₃, Z₂, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 2, 1, 3]
    invFun := ![0, 2, 1, 3]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bacd :
    iIndepFun ![Z₂, Z₁, Z₃, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 0, 2, 3]
    invFun := ![1, 0, 2, 3]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_badc :
    iIndepFun ![Z₂, Z₁, Z₄, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 0, 3, 2]
    invFun := ![1, 0, 3, 2]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bcad :
    iIndepFun ![Z₂, Z₃, Z₁, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 2, 0, 3]
    invFun := ![2, 0, 1, 3]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bdca :
    iIndepFun ![Z₂, Z₄, Z₃, Z₁] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 3, 2, 0]
    invFun := ![3, 0, 2, 1]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_cbad :
    iIndepFun ![Z₃, Z₂, Z₁, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![2, 1, 0, 3]
    invFun := ![2, 1, 0, 3]
    left_inv i := by fin_cases i <;> rfl
    right_inv i := by fin_cases i <;> rfl }
  refine .of_precomp σ.symm.surjective ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

private abbrev κ : Fin 3 → Type
  | 0 | 1 => Fin 1
  | 2   => Fin 2

private def κ_equiv : (Σ i, κ i) ≃ Fin 4 where
  toFun := fun x ↦ match x with
    | Sigma.mk 0 _ => 0
    | Sigma.mk 1 _ => 1
    | Sigma.mk 2 ⟨0, _⟩ => 2
    | Sigma.mk 2 ⟨1, _⟩ => 3
  invFun := ![Sigma.mk 0 ⟨0, zero_lt_one⟩, Sigma.mk 1 ⟨0, zero_lt_one⟩,
    Sigma.mk 2 ⟨0, zero_lt_two⟩, Sigma.mk 2 ⟨1, one_lt_two⟩]
  left_inv := by rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance fintype_kappa : ∀ (i : Fin 3), Fintype (κ i)
  | 0 | 1 | 2 => inferInstanceAs (Fintype (Fin _))

lemma apply_two_last
    (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) (hZ₄ : Measurable Z₄)
    {phi : G → G → G} (hphi : Measurable phi.uncurry) :
    iIndepFun ![Z₁, Z₂, (fun ω ↦ phi (Z₃ ω) (Z₄ ω))] := by
  
  have T := (h_indep.precomp κ_equiv.injective).pi' (m := fun _ _ ↦ hG) ?_; swap
  · rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> assumption

  let phi_third : ∀ (i : Fin 3), (κ i → G) → G
    | 0 | 1 => (fun f ↦ f ⟨0, zero_lt_one⟩)
    | 2   => (fun f ↦ phi (f ⟨0, zero_lt_two⟩) (f ⟨1, one_lt_two⟩))
  convert T.comp phi_third ?_ with i
  · fin_cases i <;> rfl
  · intro i
    match i with
    | 0 | 1 => exact measurable_pi_apply _
    | 2 =>
      have : Measurable (fun (p : Fin 2 → G) ↦ (p 0, p 1)) := by fun_prop
      exact hphi.comp this

end ProbabilityTheory.iIndepFun
end

/- PFR.SecondEstimate -/
/-
# Second estimate

The second estimate on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies
  of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $I_1 := I_1 [X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2]$
* $I_2 := I[X_1+X_2 : X_1 + \tilde X_1 | X_1+X_2+\tilde X_1+\tilde X_2]$

## Main results

* `second_estimate` : $$ I_2 \leq 2 \eta k + \frac{2 \eta (2 \eta k - I_1)}{1 - \eta}.$$
-/

noncomputable section
open scoped ProbabilityTheory
open MeasureTheory Module ProbabilityTheory

variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [Module (ZMod 2) G] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun ![X₁, X₂, X₁', X₂'])

variable (h_min : tau_minimizes p X₁ X₂)

include h_min hX₁ hX₁' hX₂ hX₂' h_indep h₁ h₂ in

lemma rdist_of_sums_ge' : (rdist (X₁ + X₁') (X₂ + X₂') ℙ ℙ) ≥ ((rdist X₁ X₂ ℙ ℙ)) - p.η * ((rdist X₁ X₁ ℙ ℙ) + (rdist X₂ X₂ ℙ ℙ)) / 2 := by
  refine LE.le.ge (LE.le.trans ?_ (distance_ge_of_min p h_min (hX₁.add hX₁') (hX₂.add hX₂')))
  rw [sub_sub, sub_le_sub_iff_left ((rdist X₁ X₂ ℙ ℙ)), ← mul_add,mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [p.hη])
  have h₁' := condRuzsaDist_diff_le' ℙ p.hmeas1 hX₁ hX₁' (h_indep.indepFun (show 0 ≠ 2 by decide))
  have h₂' := condRuzsaDist_diff_le' ℙ p.hmeas2 hX₂ hX₂' (h_indep.indepFun (show 1 ≠ 3 by decide))
  rw [h₁.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₁.aemeasurable).rdist_congr h₁] at h₁'
  rw [h₂.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₂.aemeasurable).rdist_congr h₂] at h₂'
  linarith

include h_min hX₁ hX₁' hX₂ hX₂' h_indep h₁ h₂ in
lemma second_estimate_aux :
    (rdist X₁ X₁ ℙ ℙ) + (rdist X₂ X₂ ℙ ℙ) ≤ 2 * (((rdist X₁ X₂ ℙ ℙ)) + (2 * p.η * ((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ))) / (1 - p.η)) := by
  have hX₁_indep : IndepFun X₁ X₁' (μ := ℙ) := h_indep.indepFun (show 0 ≠ 2 by decide)
  have hX₂_indep : IndepFun X₂ X₂' (μ := ℙ) := h_indep.indepFun (show 1 ≠ 3 by decide)
  have hX_indep : IndepFun (X₁ + X₁') (X₂ + X₂') := by
    exact h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption) 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
  have h : (rdist (X₁ + X₁') (X₂+ X₂') ℙ ℙ) ≤ (2 + p.η) * ((rdist X₁ X₂ ℙ ℙ)) - ((rdist X₁ X₁ ℙ ℙ) + (rdist X₂ X₂ ℙ ℙ)) / 2 - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ)) := by
    have h := hX_indep.rdist_eq (hX₁.add hX₁') (hX₂.add hX₂')
    rw [ZModModule.sub_eq_add (X₁ + X₁') (X₂ + X₂'), ← ZModModule.sub_eq_add X₁ X₁',
      ← ZModModule.sub_eq_add X₂ X₂',
      sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp (hX₁_indep.rdist_eq hX₁ hX₁').symm),
      sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp (hX₂_indep.rdist_eq hX₂ hX₂').symm),
      ← h₁.entropy_congr, ← h₂.entropy_congr, add_assoc, add_assoc, add_halves, add_halves,
      ← (IdentDistrib.refl hX₁.aemeasurable).rdist_congr h₁,
      ← (IdentDistrib.refl hX₂.aemeasurable).rdist_congr h₂,
      ZModModule.sub_eq_add X₁ X₁', ZModModule.sub_eq_add X₂ X₂', ← add_assoc, add_right_comm _ X₁']
        at h
    have h_indep' : iIndepFun ![X₁, X₂, X₂', X₁'] :=
      by exact h_indep.reindex_four_abdc
    have h' := ent_ofsum_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
    convert (h.symm ▸ (sub_le_sub_right (sub_le_sub_right h' _) _)) using 1; ring
  have h' := (rdist_of_sums_ge' p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min).le.trans h
  rw [← div_le_iff₀' two_pos, ← sub_le_iff_le_add', le_div_iff₀ (by linarith [p.hη'])]
  linarith

include h_min hX₁ hX₁' hX₂ hX₂' h_indep h₁ h₂ in

lemma second_estimate : ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') ℙ)) ≤ 2 * p.η * ((rdist X₁ X₂ ℙ ℙ)) + (2 * p.η * (2 * p.η * ((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') ℙ)))) / (1 - p.η) := by
  have hX₁_indep : IndepFun X₁ X₁' (μ := ℙ) := h_indep.indepFun (show 0 ≠ 2 by decide)
  have hX₂_indep : IndepFun X₂ X₂' (μ := ℙ) := h_indep.indepFun (show 1 ≠ 3 by decide)
  let Y : Fin 4 → Ω → G := ![X₂, X₁, X₂', X₁']
  have hY : ∀ i, Measurable (Y i) := fun i => by fin_cases i <;> assumption
  have hY_indep : iIndepFun Y := by exact h_indep.reindex_four_badc
  have h := sum_of_rdist_eq_char_2 Y hY_indep hY
  rw [show Y 0 = X₂ by rfl, show Y 1 = X₁ by rfl, show Y 2 = X₂' by rfl, show Y 3 = X₁' by rfl] at h
  rw [← h₂.rdist_congr h₁, rdist_symm, rdist_symm (X := X₂ + X₂'),
    condRuzsaDist_symm (Z := X₂ + X₂') (W := X₁ + X₁') (hX₂.add hX₂') (hX₁.add hX₁'),
    ← two_mul] at h
  replace h : 2 * ((rdist X₁ X₂ ℙ ℙ)) = (rdist (X₁ + X₁') (X₂ + X₂') ℙ ℙ) + (condRuzsaDist X₁ (X₁ + X₁') X₂ (X₂ + X₂') ℙ ℙ)
      + (ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁ + X₁') (X₁ + X₂ + X₁' + X₂') ℙ) := by
    convert h using 3 <;> abel
  have h' := condRuzsaDistance_ge_of_min p h_min hX₁ hX₂ (X₁ + X₁') (X₂ + X₂') (hX₁.add hX₁')
    (hX₂.add hX₂')
  have h₁' := condRuzsaDist_diff_le''' ℙ p.hmeas1 hX₁ hX₁' hX₁_indep
  have h₂' := condRuzsaDist_diff_le''' ℙ p.hmeas2 hX₂ hX₂' hX₂_indep
  rw [h₁.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₁.aemeasurable).rdist_congr h₁] at h₁'
  rw [h₂.entropy_congr, add_sub_cancel_right,
    ← (IdentDistrib.refl hX₂.aemeasurable).rdist_congr h₂] at h₂'
  have h'' : ((ProbabilityTheory.condMutualInfo (X₁ + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') ℙ)) ≤ p.η * ((rdist X₁ X₁ ℙ ℙ) + (rdist X₂ X₂ ℙ ℙ)) := by
    simp_rw [← add_comm X₁ X₁']
    have h₁'' := mul_le_mul_of_nonneg_left h₁' (show 0 ≤ p.η by linarith [p.hη])
    have h₂'' := mul_le_mul_of_nonneg_left h₂' (show 0 ≤ p.η by linarith [p.hη])
    have := rdist_of_sums_ge' p _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
    linarith
  nth_rewrite 1 [mul_div_assoc, ← mul_add, mul_assoc, mul_left_comm]
  refine h''.trans (mul_le_mul_of_nonneg_left ?_ (show 0 ≤ p.η by linarith [p.hη]))
  exact second_estimate_aux p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
end

/- PFR.Endgame -/
/-
# Endgame

The endgame on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies
    of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $U := X_1 + X_2$
* $V := \tilde X_1 + X_2$
* $W := X_1 + \tilde X_1$
* $S := X_1 + X_2 + \tilde X_1 + \tilde X_2$.
* $I_1 := I[U : V | S]$
* $I_2 := I[U : W | S]$
* $I_3 := I[V : W | S]$ (not explicitly defined in Lean)

# Main results:

* `sum_condMutual_le` : An upper bound on the total conditional mutual information $I_1+I_2+I_3$.
* `sum_dist_diff_le`: A sum of the "costs" of $U$, $V$, $W$.
* `construct_good`: A construction of two random variables with small Ruzsa distance between them
  given some random variables with control on total cost, as well as total mutual information.
-/

noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory

variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [mΩ : MeasureSpace Ω]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun ![X₁, X₂, X₁', X₂'])

variable (h_min : tau_minimizes p X₁ X₂)

private lemma hmeas2 {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
    [MeasurableSingletonClass G] :
    Measurable fun p : Fin 4 → G => ((p 0 + p 1, p 0 + p 2), p 0 + p 1 + p 2 + p 3) := by
  fun_prop

include h_indep hX₁ hX₂ hX₁' hX₂' h₁ in

lemma I₃_eq [IsProbabilityMeasure (ℙ : Measure Ω)] : (ProbabilityTheory.condMutualInfo ((X₁' + X₂)) ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ) = ((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ)) := by
  have h_indep2 : iIndepFun ![X₁', X₂, X₁, X₂'] := by
    exact h_indep.reindex_four_cbad
  have hident : IdentDistrib (fun a (i : Fin 4) => ![X₁, X₂, X₁', X₂'] i a)
    (fun a (j : Fin 4) => ![X₁', X₂, X₁, X₂'] j a) := by
    exact { aemeasurable_fst := by
              apply Measurable.aemeasurable
              rw [measurable_pi_iff]
              intro x
              fin_cases x;
              all_goals aesop
            aemeasurable_snd := by
              apply Measurable.aemeasurable
              rw [measurable_pi_iff]
              intro x
              fin_cases x;
              all_goals aesop
            map_eq := by
              rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
                (Fin.cases hX₁.aemeasurable <| Fin.cases hX₂.aemeasurable <|
                Fin.cases hX₁'.aemeasurable <| Fin.cases hX₂'.aemeasurable Fin.rec0)).mp h_indep,
                (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
                (Fin.cases hX₁'.aemeasurable <| Fin.cases hX₂.aemeasurable <|
                Fin.cases hX₁.aemeasurable <| Fin.cases hX₂'.aemeasurable Fin.rec0)).mp h_indep2]
              congr
              ext i
              fin_cases i
              all_goals simp [h₁.map_eq] }
  have hmeas1 : Measurable (fun p : Fin 4 → G => (p 0 + p 1, p 0 + p 1 + p 2 + p 3)) := by
    fun_prop
  have hUVS : IdentDistrib (prod (X₁ + X₂) (X₁ + X₂ + X₁' + X₂')) (prod (X₁' + X₂) (X₁ + X₂ + X₁' + X₂')) := by
    convert! hident.comp hmeas1; simp; abel
  have hUVWS : IdentDistrib (prod (prod (X₁ + X₂) (X₁' + X₁)) (X₁ + X₂ + X₁' + X₂')) (prod (prod (X₁' + X₂) (X₁' + X₁)) (X₁ + X₂ + X₁' + X₂')) := by
    convert (hident.comp hmeas2) <;> simp <;> abel
  have hU : Measurable (X₁ + X₂) := Measurable.add hX₁ hX₂
  have hV : Measurable (X₁' + X₂) := Measurable.add hX₁' hX₂
  have hW : Measurable (X₁' + X₁) := Measurable.add hX₁' hX₁
  have hS : Measurable (X₁ + X₂ + X₁' + X₂') := by fun_prop
  rw [condMutualInfo_eq hV hW hS, condMutualInfo_eq hU hW hS, chain_rule'' ℙ hU hS,
    chain_rule'' ℙ hV hS, chain_rule'' ℙ hW hS, chain_rule'' ℙ _ hS, chain_rule'' ℙ _ hS,
    hUVS.entropy_congr, hUVWS.entropy_congr]
  · exact Measurable.prod hU hW
  · exact Measurable.prod hV hW

include h_indep hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in

lemma sum_condMutual_le [Module (ZMod 2) G] [IsProbabilityMeasure (ℙ : Measure Ω)] :
    (ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.condMutualInfo ((X₁' + X₂)) ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.condMutualInfo ((X₁' + X₁)) ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ)
      ≤ 6 * p.η * ((rdist X₁ X₂ ℙ ℙ)) - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * ((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ))) := by
  have : (ProbabilityTheory.condMutualInfo ((X₁' + X₁)) ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ) = ((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ)) := condMutualInfo_comm (by fun_prop) (by fun_prop) ..
  rw [I₃_eq, this]
  any_goals simpa
  have h₂ := second_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have : 0 < 1 - p.η := by linarith [p.hη']
  field_simp at h₂ ⊢
  linarith

include h_indep h₁ h₂ in
lemma hU [IsProbabilityMeasure (ℙ : Measure Ω)] : (ProbabilityTheory.entropy ((X₁ + X₂)) ℙ) = (ProbabilityTheory.entropy (X₁' + X₂') ℙ) :=
  IdentDistrib.entropy_congr (h₁.add h₂
    (h_indep.indepFun (show (0 : Fin 4) ≠ 1 by norm_cast))
     (h_indep.indepFun (show (2 : Fin 4) ≠ 3 by norm_cast)))

variable {X₁ X₂ X₁' X₂'} in
include h_indep hX₁ hX₂ hX₁' hX₂' in
lemma independenceCondition1 :
    iIndepFun ![X₁, X₂, X₁' + X₂'] :=
  h_indep.apply_two_last hX₁ hX₂ hX₁' hX₂' measurable_add

include h₁ h₂ h_indep in
lemma hV [IsProbabilityMeasure (ℙ : Measure Ω)] : (ProbabilityTheory.entropy ((X₁' + X₂)) ℙ) = (ProbabilityTheory.entropy (X₁ + X₂') ℙ) :=
  IdentDistrib.entropy_congr (h₁.symm.add h₂
    (h_indep.indepFun (show (2 : Fin 4) ≠ 1 by norm_cast))
    (h_indep.indepFun (show (0 : Fin 4) ≠ 3 by norm_cast)))

include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition2 :
    iIndepFun ![X₂, X₁, X₁' + X₂'] :=
  independenceCondition1 hX₂ hX₁ hX₁' hX₂' h_indep.reindex_four_bacd

include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition3 :
    iIndepFun ![X₁', X₂, X₁ + X₂'] :=
  independenceCondition1 hX₁' hX₂ hX₁ hX₂' h_indep.reindex_four_cbad

include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition4 :
    iIndepFun ![X₂, X₁', X₁ + X₂'] :=
  independenceCondition1 hX₂ hX₁' hX₁ hX₂' h_indep.reindex_four_bcad

include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition5 :
    iIndepFun ![X₁, X₁', X₂ + X₂'] :=
  independenceCondition1 hX₁ hX₁' hX₂ hX₂' h_indep.reindex_four_acbd

include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition6 :
    iIndepFun ![X₂, X₂', X₁' + X₁] :=
  independenceCondition1 hX₂ hX₂' hX₁' hX₁ h_indep.reindex_four_bdca

include h_indep hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in

lemma sum_dist_diff_le [IsProbabilityMeasure (ℙ : Measure Ω)] [Module (ZMod 2) G] :
    ((condRuzsaDist' p.X₀₁ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) ≤ (6 - 3 * p.η)*((rdist X₁ X₂ ℙ ℙ)) + 3 * (2*p.η*((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ))) := by
  let X₀₁ := p.X₀₁
  let X₀₂ := p.X₀₂
  have ineq1 : (condRuzsaDist' X₀₁ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₁ X₁ ℙ ℙ) ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₁ ℙ))/2 := by
    have aux1 : (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁ + X₂)) ℙ) - (ProbabilityTheory.entropy X₁ ℙ) - (ProbabilityTheory.entropy (X₁' + X₂') ℙ) = (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₁ ℙ) := by
      rw [hU X₁ X₂ X₁' X₂' h₁ h₂ h_indep]; ring
    have aux2 : (condRuzsaDist' X₀₁ ((X₁ + X₂)) ((X₁ + X₂) + (X₁' + X₂')) ℙ ℙ) - (rdist X₀₁ X₁ ℙ ℙ)
            ≤ ((ProbabilityTheory.entropy ((X₁ + X₂) + (X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁ + X₂)) ℙ) - (ProbabilityTheory.entropy X₁ ℙ) - (ProbabilityTheory.entropy (X₁' + X₂') ℙ)) / 2 :=
      condRuzsaDist_diff_ofsum_le ℙ (hX := p.hmeas1) (hY := hX₁) (hZ := hX₂)
      (Measurable.add hX₁' hX₂') (independenceCondition1 hX₁ hX₂ hX₁' hX₂' h_indep)
    rw [← add_assoc, aux1] at aux2
    linarith [aux2]
  have ineq2 : (condRuzsaDist' X₀₂ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₂ X₂ ℙ ℙ) ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₂ ℙ))/2 := by
    have aux1 : (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁ + X₂)) ℙ) - (ProbabilityTheory.entropy X₂ ℙ) - (ProbabilityTheory.entropy (X₁' + X₂') ℙ) = (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₂ ℙ) := by
      rw [hU X₁ X₂ X₁' X₂' h₁ h₂ h_indep] ; ring
    have aux2 : (condRuzsaDist' X₀₂ ((X₁ + X₂)) ((X₁ + X₂) + (X₁' + X₂')) ℙ ℙ) - (rdist X₀₂ X₂ ℙ ℙ)
            ≤ ((ProbabilityTheory.entropy ((X₁ + X₂) + (X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁ + X₂)) ℙ) - (ProbabilityTheory.entropy X₂ ℙ) - (ProbabilityTheory.entropy (X₁' + X₂') ℙ)) / 2 := by
      rw [(show (X₁ + X₂) = X₂ + X₁ from add_comm _ _)]
      apply condRuzsaDist_diff_ofsum_le ℙ (p.hmeas2) (hX₂) (hX₁)
        (Measurable.add hX₁' hX₂') (independenceCondition2 hX₁ hX₂ hX₁' hX₂' h_indep)
    rw [← add_assoc, aux1] at aux2
    linarith [aux2]
  have V_add_eq : (X₁' + X₂) + (X₁ + X₂') = (X₁ + X₂ + X₁' + X₂') := by abel
  have ineq3 : (condRuzsaDist' X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₁ X₁ ℙ ℙ) ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₁ ℙ))/2 := by
    have aux2 : (condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁' + X₂) + (X₁ + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁' ℙ ℙ)
            ≤ ((ProbabilityTheory.entropy ((X₁' + X₂) + (X₁ + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁' + X₂)) ℙ) - (ProbabilityTheory.entropy X₁' ℙ) - (ProbabilityTheory.entropy (X₁ + X₂') ℙ)) / 2 :=
      condRuzsaDist_diff_ofsum_le ℙ (p.hmeas1) (hX₁') (hX₂) (Measurable.add hX₁ hX₂')
      (independenceCondition3 hX₁ hX₂ hX₁' hX₂' h_indep)
    have aux1 : (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁' + X₂)) ℙ) - (ProbabilityTheory.entropy X₁' ℙ) - (ProbabilityTheory.entropy (X₁ + X₂') ℙ) = (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₁ ℙ) := by
      rw [hV X₁ X₂ X₁' X₂' h₁ h₂ h_indep, h₁.entropy_congr]; ring
    rw [← h₁.rdist_congr_right p.hmeas1.aemeasurable, V_add_eq, aux1] at aux2
    linarith [aux2]
  have ineq4 : (condRuzsaDist' X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₂ X₂ ℙ ℙ) ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₂ ℙ))/2 := by
    have aux2 : (condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁' + X₂) + (X₁ + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)
            ≤ ((ProbabilityTheory.entropy ((X₁' + X₂) + (X₁ + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁' + X₂)) ℙ) - (ProbabilityTheory.entropy X₂ ℙ) - (ProbabilityTheory.entropy (X₁ + X₂') ℙ)) / 2 := by
      rw [(show (X₁' + X₂) = X₂ + X₁' from add_comm _ _)]
      apply condRuzsaDist_diff_ofsum_le ℙ (p.hmeas2) (hX₂) (hX₁') (Measurable.add hX₁ hX₂')
        (independenceCondition4 hX₁ hX₂ hX₁' hX₂' h_indep)
    have aux1 : (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁' + X₂)) ℙ) - (ProbabilityTheory.entropy X₂ ℙ) - (ProbabilityTheory.entropy (X₁ + X₂') ℙ) = (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₂ ℙ) := by
      rw [hV X₁ X₂ X₁' X₂' h₁ h₂ h_indep]; ring
    rw [V_add_eq, aux1] at aux2
    linarith [aux2]
  let W' := X₂ + X₂'
  have ineq5 : (condRuzsaDist' X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₁ X₁ ℙ ℙ) ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁' + X₁)) ℙ) - (ProbabilityTheory.entropy X₁ ℙ) - (ProbabilityTheory.entropy W' ℙ))/2 := by
    have := condRuzsaDist_diff_ofsum_le ℙ p.hmeas1 hX₁ hX₁' (Measurable.add hX₂ hX₂')
      (independenceCondition5 hX₁ hX₂ hX₁' hX₂' h_indep)
    grind
  have ineq6 : (condRuzsaDist' X₀₂ W' ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₂ X₂ ℙ ℙ) ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy W' ℙ) - (ProbabilityTheory.entropy X₂ ℙ) - (ProbabilityTheory.entropy ((X₁' + X₁)) ℙ))/2 := by
    have := condRuzsaDist_diff_ofsum_le ℙ p.hmeas2 hX₂ hX₂' (Measurable.add hX₁' hX₁)
      (independenceCondition6 hX₁ hX₂ hX₁' hX₂' h_indep)
    grind
  have dist_eq : (condRuzsaDist' X₀₂ W' ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) = (condRuzsaDist' X₀₂ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) := by
    have S_eq : (X₁ + X₂ + X₁' + X₂') = (X₂ + X₂') + (X₁' + X₁) := by
      rw [add_comm X₁' X₁, add_assoc _ X₂', add_comm X₂', ← add_assoc X₂, ← add_assoc X₂,
        add_comm X₂]
    rw [S_eq]
    apply condRuzsaDist'_of_inj_map' p.hmeas2 (hX₂.add hX₂') (hX₁'.add hX₁)
  
  have ineq7 : ((condRuzsaDist' p.X₀₁ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) ≤
    3 * (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - 3/2 * (ProbabilityTheory.entropy X₁ ℙ) -3/2 * (ProbabilityTheory.entropy X₂ ℙ) := by
    have step₁ : ((condRuzsaDist' p.X₀₁ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) ≤ (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2 :=
      calc
        _ = ((condRuzsaDist' p.X₀₁ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ)) + ((condRuzsaDist' p.X₀₂ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)) := by ring
        _ ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₁ ℙ))/2 + ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₂ ℙ))/2 := add_le_add ineq1 ineq2
        _ = (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2 := by ring
    have step₂ : ((condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) ≤ (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2 :=
      calc  ((condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)))
        _ = (condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)) := by ring
        _ ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₁ ℙ))/2 + ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (ProbabilityTheory.entropy X₂ ℙ))/2 := add_le_add ineq3 ineq4
        _ = (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2 := by ring
    have step₃ : ((condRuzsaDist' p.X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) ≤ (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2 :=
      calc ((condRuzsaDist' p.X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) = ((condRuzsaDist' X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₁ X₁ ℙ ℙ)) + ((condRuzsaDist' X₀₂ W' ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist X₀₂ X₂ ℙ ℙ)) :=
          by rw [dist_eq]
        _ ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy ((X₁' + X₁)) ℙ) - (ProbabilityTheory.entropy X₁ ℙ) - (ProbabilityTheory.entropy W' ℙ))/2
          + ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) + (ProbabilityTheory.entropy W' ℙ) - (ProbabilityTheory.entropy X₂ ℙ) - (ProbabilityTheory.entropy ((X₁' + X₁)) ℙ))/2 := add_le_add ineq5 ineq6
        _ = (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2 := by ring
    calc ((condRuzsaDist' p.X₀₁ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) ≤ ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2) +
      ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2) + ((ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))/2) :=
        add_le_add (add_le_add step₁ step₂) step₃
    _ = 3 * (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - 3/2 * (ProbabilityTheory.entropy X₁ ℙ) -3/2 * (ProbabilityTheory.entropy X₂ ℙ) := by ring
  have h_indep' : iIndepFun ![X₁, X₂, X₂', X₁'] := by
    refine .of_precomp (Equiv.swap (2 : Fin 4) 3).surjective ?_
    convert h_indep using 1
    ext x
    fin_cases x ; all_goals { aesop }
  have ineq8 : 3 * (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) ≤ 3/2 * ((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ)) + 3*(2+p.η)*((rdist X₁ X₂ ℙ ℙ)) - 3*((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ)) :=
    calc 3 * (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) ≤ 3 * ((ProbabilityTheory.entropy X₁ ℙ) / 2 + (ProbabilityTheory.entropy X₂ ℙ) / 2 + (2+p.η)*((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ))) := by
          gcongr
          exact ent_ofsum_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
      _ = 3/2 * ( (ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ)) + 3*(2+p.η)*((rdist X₁ X₂ ℙ ℙ)) - 3*((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ)) := by ring
  
  calc
        ((condRuzsaDist' p.X₀₁ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁ + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ ((X₁' + X₁)) ((X₁ + X₂ + X₁' + X₂')) ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)))
    _ ≤ 3 * (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - 3/2 * (ProbabilityTheory.entropy X₁ ℙ) -3/2 * (ProbabilityTheory.entropy X₂ ℙ) := ineq7
    _ = 3 * (ProbabilityTheory.entropy ((X₁ + X₂ + X₁' + X₂')) ℙ) - (3/2 *((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))) := by ring
    _ ≤ (3/2 * ( (ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ)) + 3*(2+p.η)*((rdist X₁ X₂ ℙ ℙ)) - 3*((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ))) - (3/2 *((ProbabilityTheory.entropy X₁ ℙ) + (ProbabilityTheory.entropy X₂ ℙ))) :=
      sub_le_sub_right ineq8 _
    _ = (6 - 3 * p.η)*((rdist X₁ X₂ ℙ ℙ)) + 3 * (2*p.η*((rdist X₁ X₂ ℙ ℙ)) - ((ProbabilityTheory.condMutualInfo ((X₁ + X₂)) ((X₁' + X₂)) ((X₁ + X₂ + X₁' + X₂')) ℙ))) := by ring

omit [Finite G] hG [MeasurableSingletonClass G] mΩ in

lemma sum_uvw_eq_zero [Module (ZMod 2) G] : (X₁ + X₂) + (X₁' + X₂) + (X₁' + X₁) = 0 := by
  simp [add_assoc, ← ZModModule.sub_eq_add X₁', ZModModule.add_self]

section construct_good
variable {Ω' : Type*} [MeasureSpace Ω']

omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] in
lemma cond_c_eq_integral [IsProbabilityMeasure (ℙ : Measure Ω')]
    {Y Z : Ω' → G} (hY : Measurable Y) (hZ : Measurable Z) : ((condRuzsaDist' p.X₀₁ Y Z ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ Y Z ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) =
    (Measure.map Z ℙ)[fun z => ((rdist p.X₀₁ Y ℙ (ℙ[|Z ← z])) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ Y ℙ (ℙ[|Z ← z])) - (rdist p.X₀₂ X₂ ℙ ℙ)))] := by
  cases nonempty_fintype G
  simp only [integral_fintype .of_finite, smul_sub, smul_add, smul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  simp_rw [← integral_fintype .of_finite]
  rw [← condRuzsaDist'_eq_integral _ hY hZ, ← condRuzsaDist'_eq_integral _ hY hZ, integral_const,
    integral_const]
  have : IsProbabilityMeasure (Measure.map Z ℙ) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  simp

variable {T₁ T₂ T₃ : Ω' → G} (hT : T₁ + T₂ + T₃ = 0)
variable (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)
  [IsProbabilityMeasure (ℙ : Measure Ω')] [Module (ZMod 2) G]

include hT₁ hT₂ hT₃ hT h_min in

lemma construct_good_prelim :
    ((rdist X₁ X₂ ℙ ℙ)) ≤ ((ProbabilityTheory.mutualInfo T₁ T₂ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ) + (ProbabilityTheory.mutualInfo T₃ T₁ ℙ)) + p.η * ((rdist p.X₀₁ T₁ ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₂ ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + p.η * ((ProbabilityTheory.mutualInfo T₁ T₃ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ))/2 := by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ (rdist T₁ T₂ (ℙ[|T₃ ⁻¹' {t}]) (ℙ[|T₃ ⁻¹' {t}]))]
  let sum2 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ (rdist p.X₀₁ T₁ ℙ (ℙ[|T₃ ⁻¹' {t}])) - (rdist p.X₀₁ X₁ ℙ ℙ)]
  let sum3 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ (rdist p.X₀₂ T₂ ℙ (ℙ[|T₃ ⁻¹' {t}])) - (rdist p.X₀₂ X₂ ℙ ℙ)]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ((rdist T₁ T₂ (ℙ[|T₃ ⁻¹' {t}]) (ℙ[|T₃ ⁻¹' {t}])) + p.η * ((rdist p.X₀₁ T₁ ℙ (ℙ[|T₃ ⁻¹' {t}])) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₂ ℙ (ℙ[|T₃ ⁻¹' {t}])) - (rdist p.X₀₂ X₂ ℙ ℙ))))]
  have hp.η : 0 ≤ p.η := by linarith [p.hη]
  have hP : IsProbabilityMeasure (Measure.map T₃ ℙ) :=
    Measure.isProbabilityMeasure_map hT₃.aemeasurable
  have h2T₃ : T₃ = T₁ + T₂ :=
    calc T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hT, zero_sub]; simp [ZModModule.neg_eq_self]
      _ = T₁ + T₂ := by rw [add_sub_cancel_right]
  have h2T₁ : T₁ = T₂ + T₃ := by simp [h2T₃, add_left_comm, ZModModule.add_self]
  have h2T₂ : T₂ = T₃ + T₁ := by simp [h2T₁, add_left_comm, ZModModule.add_self]
  have h1 : sum1 ≤ ((ProbabilityTheory.mutualInfo T₁ T₂ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ) + (ProbabilityTheory.mutualInfo T₃ T₁ ℙ)) := by
    have h1 : sum1 ≤ 3 * (ProbabilityTheory.mutualInfo T₁ T₂ ℙ) + 2 * (ProbabilityTheory.entropy T₃ ℙ) - (ProbabilityTheory.entropy T₁ ℙ) - (ProbabilityTheory.entropy T₂ ℙ) := by
      subst h2T₃; exact ent_bsg hT₁ hT₂
    have h2 : (ProbabilityTheory.entropy ((_root_.prod T₂ T₃)) ℙ) = (ProbabilityTheory.entropy ((_root_.prod T₁ T₂)) ℙ) := by
      rw [h2T₃, entropy_add_right', entropy_comm] <;> assumption
    have h3 : (ProbabilityTheory.entropy ((_root_.prod T₁ T₂)) ℙ) = (ProbabilityTheory.entropy ((_root_.prod T₃ T₁)) ℙ) := by
      rw [h2T₃, entropy_add_left, entropy_comm] <;> assumption
    simp_rw [mutualInfo_def] at h1 ⊢; linarith
  have h2 : p.η * sum2 ≤ p.η * ((rdist p.X₀₁ T₁ ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + (ProbabilityTheory.mutualInfo T₁ T₃ ℙ) / 2) := by
    have : sum2 = (condRuzsaDist' p.X₀₁ T₁ T₃ ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) := by
      simp only [integral_sub .of_finite .of_finite, integral_const, smul_eq_mul, sum2]
      simp [condRuzsaDist'_eq_sum hT₁ hT₃, integral_eq_setIntegral
        (FiniteRange.ae_mem_toFinset _ T₃), setIntegral_finset _ .finset,
        map_measureReal_apply hT₃ (.singleton _)]
    gcongr
    linarith [condRuzsaDist_le' ℙ ℙ p.hmeas1 hT₁ hT₃]
  have h3 : p.η * sum3 ≤ p.η * ((rdist p.X₀₂ T₂ ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ) / 2) := by
    have : sum3 = (condRuzsaDist' p.X₀₂ T₂ T₃ ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ) := by
      simp only [integral_sub .of_finite .of_finite, integral_const, smul_eq_mul, sum3]
      simp [condRuzsaDist'_eq_sum hT₂ hT₃,
        integral_eq_setIntegral (FiniteRange.ae_mem_toFinset _ T₃),
         setIntegral_finset _ .finset,
        map_measureReal_apply hT₃ (.singleton _)]
    gcongr
    linarith [condRuzsaDist_le' ℙ ℙ p.hmeas2 hT₂ hT₃]
  have h4 : sum4 ≤ ((ProbabilityTheory.mutualInfo T₁ T₂ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ) + (ProbabilityTheory.mutualInfo T₃ T₁ ℙ)) + p.η * ((rdist p.X₀₁ T₁ ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₂ ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + p.η * ((ProbabilityTheory.mutualInfo T₁ T₃ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ)) / 2 := by
    suffices sum4 = sum1 + p.η * (sum2 + sum3) by linarith
    simp only [sum1, sum2, sum3, sum4, integral_add .of_finite .of_finite, integral_const_mul]
  have hk : ((rdist X₁ X₂ ℙ ℙ)) ≤ sum4 := by
    suffices (Measure.map T₃ ℙ)[fun _ ↦ ((rdist X₁ X₂ ℙ ℙ))] ≤ sum4 by simpa using this
    refine integral_mono_ae .of_finite .of_finite <| ae_iff_of_countable.2 fun t ht ↦ ?_
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' {t}]) :=
      cond_isProbabilityMeasure (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' {t}]) (μ' := ℙ[|T₃ ⁻¹' {t}]) p h_min hT₁ hT₂]
  exact hk.trans h4

include hT₁ hT₂ hT₃ hT h_min in

lemma construct_good :
    ((rdist X₁ X₂ ℙ ℙ)) ≤ ((ProbabilityTheory.mutualInfo T₁ T₂ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ) + (ProbabilityTheory.mutualInfo T₃ T₁ ℙ)) + (p.η/3) * (((ProbabilityTheory.mutualInfo T₁ T₂ ℙ) + (ProbabilityTheory.mutualInfo T₂ T₃ ℙ) + (ProbabilityTheory.mutualInfo T₃ T₁ ℙ)) + ((rdist p.X₀₁ T₁ ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₁ ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((rdist p.X₀₁ T₂ ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₂ ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((rdist p.X₀₁ T₃ ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₃ ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)))) := by
  have v2 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₁ hT₃ hT₂
  have v3 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₂ hT₁ hT₃
  have v6 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₃ hT₂ hT₁
  simp only [mutualInfo, entropy_comm hT₂ hT₁, entropy_comm hT₃ hT₁, entropy_comm hT₃ hT₂]
    at *
  linarith

include hT₁ hT₂ hT₃ hT h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω')] in
lemma construct_good' (μ : Measure Ω') [IsProbabilityMeasure μ] :
    ((rdist X₁ X₂ ℙ ℙ)) ≤ ((ProbabilityTheory.mutualInfo T₁ T₂ μ) + (ProbabilityTheory.mutualInfo T₂ T₃ μ) + (ProbabilityTheory.mutualInfo T₃ T₁ μ)) + (p.η/3) * (((ProbabilityTheory.mutualInfo T₁ T₂ μ) + (ProbabilityTheory.mutualInfo T₂ T₃ μ) + (ProbabilityTheory.mutualInfo T₃ T₁ μ)) + ((rdist p.X₀₁ T₁ ℙ μ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₁ ℙ μ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((rdist p.X₀₁ T₂ ℙ μ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₂ ℙ μ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((rdist p.X₀₁ T₃ ℙ μ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((rdist p.X₀₂ T₃ ℙ μ) - (rdist p.X₀₂ X₂ ℙ ℙ)))) := by
  let _ : MeasureSpace Ω' := ⟨μ⟩
  apply construct_good p X₁ X₂ h_min hT hT₁ hT₂ hT₃

variable {R : Ω' → G} (hR : Measurable R)

omit [AddCommGroup G] in
lemma delta'_eq_integral :
    ((ProbabilityTheory.condMutualInfo T₁ T₂ R ℙ) + (ProbabilityTheory.condMutualInfo T₂ T₃ R ℙ) + (ProbabilityTheory.condMutualInfo T₃ T₁ R ℙ)) = (Measure.map R ℙ)[fun r => ((ProbabilityTheory.mutualInfo T₁ T₂ (ℙ[|R⁻¹' {r}])) + (ProbabilityTheory.mutualInfo T₂ T₃ (ℙ[|R⁻¹' {r}])) + (ProbabilityTheory.mutualInfo T₃ T₁ (ℙ[|R⁻¹' {r}])))] := by
  cases nonempty_fintype G
  simp_rw [condMutualInfo_eq_integral_mutualInfo, integral_fintype .of_finite, smul_add,
    Finset.sum_add_distrib]

include hT₁ hT₂ hT₃ hT h_min hR in
lemma cond_construct_good :
    ((rdist X₁ X₂ ℙ ℙ)) ≤ ((ProbabilityTheory.condMutualInfo T₁ T₂ R ℙ) + (ProbabilityTheory.condMutualInfo T₂ T₃ R ℙ) + (ProbabilityTheory.condMutualInfo T₃ T₁ R ℙ)) + (p.η/3) * (((ProbabilityTheory.condMutualInfo T₁ T₂ R ℙ) + (ProbabilityTheory.condMutualInfo T₂ T₃ R ℙ) + (ProbabilityTheory.condMutualInfo T₃ T₁ R ℙ)) + ((condRuzsaDist' p.X₀₁ T₁ R ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ T₁ R ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ T₂ R ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ T₂ R ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ))) + ((condRuzsaDist' p.X₀₁ T₃ R ℙ ℙ) - (rdist p.X₀₁ X₁ ℙ ℙ) + ((condRuzsaDist' p.X₀₂ T₃ R ℙ ℙ) - (rdist p.X₀₂ X₂ ℙ ℙ)))) := by
  cases nonempty_fintype G
  rw [delta'_eq_integral, cond_c_eq_integral _ _ _ hT₁ hR, cond_c_eq_integral _ _ _ hT₂ hR,
    cond_c_eq_integral _ _ _ hT₃ hR]
  simp_rw [integral_fintype .of_finite, ← Finset.sum_add_distrib, ← smul_add, Finset.mul_sum,
    mul_smul_comm, ← Finset.sum_add_distrib, ← smul_add]
  simp_rw [← integral_fintype .of_finite]
  have : IsProbabilityMeasure (Measure.map R ℙ) := Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    ((rdist X₁ X₂ ℙ ℙ)) = (Measure.map R ℙ)[fun _r => ((rdist X₁ X₂ ℙ ℙ))] := by
      rw [integral_const]; simp
    _ ≤ _ := ?_
  simp_rw [integral_fintype .of_finite]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : ℙ (R⁻¹' {r}) = 0
  · simp [Measure.real, Measure.map_apply hR (.singleton r), hr]
  simp_rw [smul_eq_mul]
  gcongr
  have : IsProbabilityMeasure (ℙ[|R ⁻¹' {r}]) := cond_isProbabilityMeasure hr
  apply construct_good' p X₁ X₂ h_min hT hT₁ hT₂ hT₃

end construct_good

include hX₁ hX₂ h_min h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂' in

theorem tau_strictly_decreases_aux [IsProbabilityMeasure (ℙ : Measure Ω)] [Module (ZMod 2) G]
    (hpη : p.η = 1 / 9) : (rdist X₁ X₂ ℙ ℙ) = 0 := by
  have h0 := cond_construct_good p X₁ X₂ h_min (sum_uvw_eq_zero ..)
    (show Measurable (X₁ + X₂) by fun_prop) (show Measurable (X₁' + X₂) by fun_prop)
    (show Measurable (X₁' + X₁) by fun_prop) (show Measurable (X₁ + X₂ + X₁' + X₂') by fun_prop)
  have h1 := sum_condMutual_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h2 := sum_dist_diff_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h_indep' : iIndepFun ![X₁, X₂, X₂', X₁'] := by
    let σ : Fin 4 ≃ Fin 4 :=
    { toFun := ![0, 1, 3, 2]
      invFun := ![0, 1, 3, 2]
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
    refine .of_precomp σ.symm.surjective ?_
    convert h_indep using 1
    ext i; fin_cases i <;> rfl
  have h3 := first_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
  have hk : 0 ≤ ((rdist X₁ X₂ ℙ ℙ)) := rdist_nonneg hX₁ hX₂
  rw [hpη] at *
  linarith only [hk, h0, h1, h2, h3]
end

/- PFR.EntropyPFR -/
/-
# Entropic version of polynomial Freiman-Ruzsa conjecture

Here we prove the entropic version of the polynomial Freiman-Ruzsa conjecture.

## Main results

* `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some
  subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$.

-/

noncomputable section
open scoped ProbabilityTheory
open MeasureTheory ProbabilityTheory
universe uG

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]

variable {Ω Ω' : Type*} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {G : Type uG} [AddCommGroup G] [Module (ZMod 2) G] [Finite G] [MeasurableSpace G]
  [MeasurableSingletonClass G]
variable (p : refPackage Ω₀₁ Ω₀₂ G) {X₁ : Ω → G} {X₂ : Ω → G} (hX₁ : Measurable X₁)
  (hX₂ : Measurable X₂)

include hX₁ hX₂ in

theorem tau_strictly_decreases (h_min : tau_minimizes p X₁ X₂) (hpη : p.η = 1 / 9) :
    (rdist X₁ X₂ ℙ ℙ) = 0 := by
  cases nonempty_fintype G
  let ⟨A, mA, μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩
    := independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_congr h_id2]
  let _ : MeasureSpace A := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure A) := hμ
  rw [← h_id1.tau_minimizes p h_id2] at h_min
  apply tau_strictly_decreases_aux p Y₁ Y₂ Y₁' Y₂' hY₁ hY₂ hY₁' hY₂' (h_id1.trans h_id1'.symm)
    (h_id2.trans h_id2'.symm) h_indep h_min hpη

theorem entropic_PFR_conjecture (hpη : p.η = 1 / 9) :
    ∃ H : Submodule (ZMod 2) G, ∃ Ω : Type uG, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ (rdist p.X₀₁ U ℙ ℙ) + (rdist p.X₀₂ U ℙ ℙ) ≤ 11 * (rdist p.X₀₁ p.X₀₂ ℙ ℙ) := by
  cases nonempty_fintype G
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, _, htau_min⟩ := tau_minimizer_exists p
  have hdist : (rdist X₁ X₂ ℙ ℙ) = 0 := tau_strictly_decreases p hX₁ hX₂ htau_min hpη
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  refine ⟨AddSubgroup.toZModSubmodule _ H, Ω', inferInstance, U, inferInstance, hU, hH_unif , ?_⟩
  have h : (tau p X₁ X₂ ℙ ℙ) ≤ (tau p p.X₀₂ p.X₀₁ ℙ ℙ) := is_tau_min p htau_min p.hmeas2 p.hmeas1
  rw [tau, tau, hpη] at h
  norm_num at h
  have : (rdist p.X₀₁ p.X₀₂ ℙ ℙ) = (rdist p.X₀₂ p.X₀₁ ℙ ℙ) := rdist_symm
  have : (rdist p.X₀₁ U ℙ ℙ) ≤ (rdist p.X₀₁ X₁ ℙ ℙ) + (rdist X₁ U ℙ ℙ) := rdist_triangle p.hmeas1 hX₁ hU
  have : (rdist p.X₀₂ U ℙ ℙ) ≤ (rdist p.X₀₂ X₂ ℙ ℙ) + (rdist X₂ U ℙ ℙ) := rdist_triangle p.hmeas2 hX₂ hU
  linarith

end


/- Popular cosets -/
noncomputable section
open scoped ProbabilityTheory
open ProbabilityTheory MeasureTheory Real Set Fintype Function
open scoped Pointwise

universe u

namespace ProbabilityTheory
variable {G Ω : Type*} [AddCommGroup G] [Finite G]
    [MeasurableSpace G] [MeasurableSingletonClass G] {A B : Finset G}
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U V : Ω → G}

lemma IsUniform.measureReal_preimage_sub_zero [DecidableEq G] (Uunif : IsUniform A U)
    (Umeas : Measurable U) (Vunif : IsUniform B V) (Vmeas : Measurable V) (h_indep : IndepFun U V) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {0})
      = (A ∩ B).card / (A.card * B.card) := by
  cases nonempty_fintype G
  have : (U - V) ⁻¹' {0} = ⋃ (g : G), (U ⁻¹' {g} ∩ V⁻¹' {g}) := by
    ext ω; simp [sub_eq_zero, eq_comm]
  rw [this, measureReal_iUnion_fintype _ (fun i ↦ (Umeas .of_discrete).inter <| Vmeas .of_discrete)]
  swap
  · intro g g' hgg'
    apply Set.disjoint_iff_inter_eq_empty.2
    ext a
    simp (config := {contextual := True}) [hgg']
  let W : Finset G := A ∩ B
  calc
    ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p} ∩ V ⁻¹' {p})
      = ∑ p, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply sum_congr _ _ (fun g ↦ ?_)
        rw [h_indep.measureReal_inter_preimage_eq_mul .of_discrete .of_discrete]
    _ = ∑ p ∈ W, (ℙ : Measure Ω).real (U ⁻¹' {p}) * (ℙ : Measure Ω).real (V ⁻¹' {p}) := by
        apply (Finset.sum_subset W.subset_univ _).symm
        intro i _ hi
        obtain hi | hi : i ∉ A ∨ i ∉ B := by simpa [or_iff_not_imp_left, W] using hi
        · simp [Uunif.measureReal_preimage_of_nmem hi]
        · simp [Vunif.measureReal_preimage_of_nmem hi]
    _ = ∑ p ∈ W, (1 / A.card : ℝ) * (1 / B.card) := by
        congr! 1 with i hi
        replace hi : i ∈ A ∧ i ∈ B := by simpa [W] using hi
        rw [Uunif.measureReal_preimage_of_mem (by trivial) hi.1,
            Vunif.measureReal_preimage_of_mem (by trivial) hi.2]
    _ = (W.card : ℝ) / (A.card * B.card) := by simp [div_eq_inv_mul]; ring

lemma IsUniform.measureReal_preimage_sub [DecidableEq G] (Uunif : IsUniform A U)
    (Umeas : Measurable U) (Vunif : IsUniform B V) (Vmeas : Measurable V) (h_indep : IndepFun U V)
    (x : G) :
    (ℙ : Measure Ω).real ((U - V) ⁻¹' {x}) = (A ∩ (B + {x})).card / (A.card * B.card) := by
  classical
  let W := fun ω ↦ V ω + x
  have Wunif : IsUniform (B + {x} : Set G) W := by
    simpa [W, Function.comp_def] using Vunif.comp (add_left_injective x)
  have Wmeas : Measurable W := Vmeas.add_const _
  have UWindep : IndepFun U W := by
    have : Measurable (fun g ↦ g + x) := measurable_add_const x
    exact h_indep.comp measurable_id this
  have : (U - V) ⁻¹' {x} = (U - W) ⁻¹' {0} := by
    ext ω
    simp [W, ← sub_eq_zero (b := x)]
    abel_nf
  have h : (B : Set G)+{x} = (B+{x}:Finset G) := by simp
  rw [h] at Wunif
  simp [this, Uunif.measureReal_preimage_sub_zero Umeas Wunif Wmeas UWindep]

end ProbabilityTheory

lemma PFR_conjecture_pos_aux {G : Type*} [AddCommGroup G] {A : Set G} (hA : A.Finite) {K : ℝ}
    (hA₀ : A.Nonempty) (hAK : (A - A).ncard ≤ K * A.ncard) :
    (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A - A).ncard ∧ 0 < K := by
  have card_AA_pos : (0 : ℝ) < (A - A).ncard := by simpa [Set.ncard_pos (hA.sub hA)]
  have KA_pos : 0 < K ∧ (0 : ℝ) < A.ncard := by
    have I : ¬ (A.ncard : ℝ) < 0 := by simp
    simpa [Nat.cast_pos, I, and_false, or_false] using mul_pos_iff.1 (card_AA_pos.trans_le hAK)
  exact ⟨KA_pos.2, card_AA_pos, KA_pos.1⟩

variable {G : Type*} [AddCommGroup G] {A : Set G} {K : ℝ} [Countable G]

theorem rdist_le_of_isUniform_of_card_add_le [A_fin : Finite A] [MeasurableSpace G]
    [MeasurableSingletonClass G]
    (hA₀ : A.Nonempty) (hA : (A - A).ncard ≤ K * A.ncard)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U₀ : Ω → G}
    (U₀unif : IsUniform A U₀) (U₀meas : Measurable U₀) : (rdist (U₀) (U₀) volume volume) ≤ log K := by
  obtain ⟨A_pos, AA_pos, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A - A).ncard ∧ 0 < K :=
    PFR_conjecture_pos_aux A.toFinite hA₀ hA
  rcases independent_copies_two U₀meas U₀meas with ⟨Ω, mΩ, U, U', hP, hU, hU', UU'_indep, idU, idU'⟩
  have Uunif : IsUniform A U := U₀unif.of_identDistrib idU.symm .of_discrete
  have U'unif : IsUniform A U' := U₀unif.of_identDistrib idU'.symm .of_discrete
  have IU : (rdist (U) (U') volume volume) ≤ log K := by
    have I : (ProbabilityTheory.entropy (U - U') volume) ≤ log (A - A).ncard := by
      apply entropy_le_log_card_of_mem_finite (Set.Finite.sub A_fin A_fin) (hU.sub hU')
      filter_upwards [Uunif.ae_mem, U'unif.ae_mem] with ω h1 h2
      exact Set.sub_mem_sub h1 h2
    have J : log (A - A).ncard ≤ log K + log A.ncard := by
      rw [← log_mul K_pos.ne' A_pos.ne']; gcongr
    rw [UU'_indep.rdist_eq hU hU', Uunif.entropy_eq' A_fin hU, U'unif.entropy_eq' A_fin hU']
    linarith
  rwa [idU.rdist_congr idU'] at IU

variable [Module (ZMod 2) G] [Finite G]

lemma sumset_eq_sub {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] (A : Set G) :
    A + A = A - A := by
  rw [← Set.image2_add, ← Set.image2_sub]
  congr! 1 with a _ b _
  show a + b = a - b
  simp [ZModModule.sub_eq_add]

lemma green49_popular_sharp (hA₀ : A.Nonempty) (hA : (A + A).ncard ≤ K * A.ncard) :
    ∃ (W : Submodule (ZMod 2) G) (B : Set G), B.Nonempty ∧ B ⊆ A ∧ B-B ⊆ W ∧
      (A.ncard : ℝ) ≤ K^11*B.ncard ∧ (Nat.card W : ℝ) ≤ K^11*B.ncard := by
  cases nonempty_fintype G
  classical
  have A_fin : Finite A := by infer_instance
  let _mG : MeasurableSpace G := ⊤
  rw [sumset_eq_sub] at hA
  have : MeasurableSingletonClass G := ⟨fun _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < (A - A).ncard ∧ 0 < K :=
    PFR_conjecture_pos_aux A.toFinite hA₀ hA
  let A' := A.toFinite.toFinset
  have hA₀' : Finset.Nonempty A' := by simpa [Finset.Nonempty, Set.Nonempty, A'] using hA₀
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' hA₀' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -, -⟩
  rw [hAA'] at UAunif
  have : (rdist (UA) (UA) volume volume) ≤ log K := rdist_le_of_isUniform_of_card_add_le hA₀ hA UAunif UAmeas
  rw [← sumset_eq_sub] at hA
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas, 1/9, (by norm_num), (by norm_num)⟩
  
  rcases entropic_PFR_conjecture p (by norm_num) with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  have H_fin : (H : Set G).Finite := (H : Set G).toFinite
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm .of_discrete
  have VA'unif := VAunif
  rw [← hAA'] at VA'unif
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm .of_discrete
  let H' := (H : Set G).toFinite.toFinset
  have hHH' : H' = (H : Set G) := (toFinite (H : Set G)).coe_toFinset
  have VH'unif := VHunif
  rw [← hHH'] at VH'unif
  have : (rdist (VA) (VH) volume volume) ≤ 11/2 * log K := by rw [idVA.rdist_congr idVH]; linarith
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos
    positivity
  have VA_ent : (ProbabilityTheory.entropy (VA) volume) = log A.ncard := VAunif.entropy_eq' A_fin VAmeas
  have VH_ent : (ProbabilityTheory.entropy (VH) volume) = log (H : Set G).ncard := VHunif.entropy_eq' H_fin VHmeas
  have Icard : |log A.ncard - log (H : Set G).ncard| ≤ 11 * log K := by
    rw [← VA_ent, ← VH_ent]
    apply (diff_ent_le_rdist VAmeas VHmeas).trans
    linarith
  
  have I : log K * (-11/2) + log A.ncard * (-1/2) + log (H : Set G).ncard * (-1/2)
      ≤ - (ProbabilityTheory.entropy (VA - VH) volume) := by
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    linarith
  
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- (ProbabilityTheory.entropy (VA - VH) volume)) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
  let B := A ∩ ((H : Set G) + {x₀})
  rw [VA'unif.measureReal_preimage_sub VAmeas VH'unif VHmeas Vindep] at h₀
  have hAA'_card : A'.card = A.ncard := by simp [← hAA']
  have hHH'_card : H'.card = (H : Set G).ncard := by simp [← hHH']
  rw [hAA'_card,hHH'_card,le_div_iff₀ (by positivity)] at h₀
  have prob : exp (-(ProbabilityTheory.entropy (VA - VH) volume)) * ((A.ncard : ℝ) * (H : Set G).ncard) ≤ B.ncard := by
    simpa [B,← Set.ncard_coe_finset,hAA',hHH',-add_singleton] using h₀
  have lk : exp (11 * log K) = K^11 := by
    calc
      exp (11 * log K) = exp (log (K^11)) := by rw [log_pow]; norm_num
      _ = K^11 := exp_log (by positivity)
  have ll : 0 ≤ 11*log K + (-(ProbabilityTheory.entropy (VA - VH) volume)) + log (H : Set G).ncard := by
    linarith [(le_abs_self _).trans Icard]
  have e := exp_monotone ll
  rw [Real.exp_zero,exp_add,exp_add,lk,exp_log H_pos] at e
  have large : (A.ncard : ℝ) ≤ K^11 * B.ncard := calc
    (A.ncard : ℝ) = 1*A.ncard := (one_mul _).symm
    _ ≤ (K^11*exp (-(ProbabilityTheory.entropy (VA - VH) volume))*(H : Set G).ncard)*A.ncard := by gcongr
    _ = K^11*(exp (-(ProbabilityTheory.entropy (VA - VH) volume)) * ((A.ncard : ℝ)*(H : Set G).ncard)) := by ring
    _ ≤ K^11*B.ncard := by gcongr
  have lr : 0 ≤ 11*log K + (-(ProbabilityTheory.entropy (VA - VH) volume)) + log A.ncard := by
    linarith [(neg_le_abs _).trans Icard]
  have g := exp_monotone lr
  rw [Real.exp_zero,exp_add,exp_add,lk,exp_log A_pos] at g
  have largeH : ((H : Set G).ncard : ℝ) ≤ K^11 * B.ncard := calc
    ((H : Set G).ncard : ℝ) = 1*(H : Set G).ncard := (one_mul _).symm
    _ ≤ (K^11*exp (-(ProbabilityTheory.entropy (VA - VH) volume))*A.ncard)*(H : Set G).ncard := by gcongr
    _ = K^11*(exp (-(ProbabilityTheory.entropy (VA - VH) volume)) * ((A.ncard : ℝ)*(H : Set G).ncard)) := by ring
    _ ≤ K^11*B.ncard := by gcongr
  have bn : B.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h,Set.ncard_empty,Nat.cast_zero,mul_zero] at large
    exact A_pos.not_ge large
  refine ⟨H,B,bn,inter_subset_left,?_,large,largeH⟩
  rintro _ ⟨a,ha,b,hb,rfl⟩
  obtain ⟨x,hx,y,hy,e⟩ := ha.2
  obtain ⟨z,hz,t,ht,f⟩ := hb.2
  obtain rfl : y=x₀ := hy
  obtain rfl : t=y := ht
  rw [← e,← f]
  change x+t-(z+t) ∈ H
  simpa using H.sub_mem hx hz
end

open Finset
open scoped Pointwise

/-- A popular coset whose density is high on both sides yields the exponent 12. -/
theorem Green49Sharp.cover (popular : ∀ n (A : Finset (𝔽₂ n)), A.Nonempty → ∀ K : ℝ, 1 ≤ K →
    ((A+A).card : ℝ) ≤ K*A.card →
    ∃ (W : Submodule (ZMod 2) (𝔽₂ n)) (B : Finset (𝔽₂ n)),
      B.Nonempty ∧ B ⊆ A ∧ ((B-B : Finset _) : Set (𝔽₂ n)) ⊆ W ∧
      (A.card : ℝ) ≤ K^11*B.card ∧ (Nat.card W : ℝ) ≤ K^11*B.card) :
    type_of% @Green49.green_49 := by
  classical
  refine ⟨(12 : ℕ), by norm_num, ?_⟩
  intro n A ne K k1 doubling
  obtain ⟨W,B,bne,ba,sub,mass,size⟩ := popular n A ne K k1 doubling
  have kpos : 0 < K := by linarith
  have bpos : 0 < (B.card : ℝ) := by exact_mod_cast bne.card_pos
  have mono : A+B ⊆ A+A := by gcongr
  have bnd : ((A+B).card : ℝ) ≤ (K*A.card/B.card)*B.card := by
    rw [div_mul_cancel₀ _ bpos.ne']
    exact (show ((A+B).card : ℝ) ≤ (A+A).card by exact_mod_cast card_le_card mono).trans doubling
  obtain ⟨F,_,bound,hcov⟩ := ruzsa_covering_add bne bnd
  have fmass : (F.card : ℝ)*B.card ≤ K*A.card := (le_div_iff₀ bpos).mp bound
  have cov : (A : Set (𝔽₂ n)) ⊆ F+W := by
    intro a ha
    obtain ⟨x,hx,y,hy,e⟩ := mem_add.mp (hcov ha)
    exact Set.mem_add.mpr ⟨x,hx,y,sub hy,e⟩
  by_cases small : Nat.card W ≤ A.card
  · refine ⟨W,F,small,?_,cov⟩
    have smallF : (F.card : ℝ) ≤ K^12 := by
      apply le_of_mul_le_mul_right (a := (B.card : ℝ)) _ bpos
      calc
        (F.card : ℝ)*B.card ≤ K*A.card := fmass
        _ ≤ K*(K^11*B.card) := by gcongr
        _ = K^12*B.card := by ring
    linarith [show 0 ≤ K^12 by positivity]
  obtain ⟨V,va,av,vw⟩ := ZModModule.exists_submodule_subset_card_le Nat.prime_two W
    (le_of_not_ge small) ne.card_pos.ne'
  obtain ⟨S,hs,cs⟩ := V.toAddSubgroup.exists_left_transversal_of_le (H:=W.toAddSubgroup) vw
  change S + (V : Set (𝔽₂ n)) = (W : Set (𝔽₂ n)) at hs
  change Nat.card S * Nat.card V = Nat.card W at cs
  let T := S.toFinite.toFinset
  have et : (T : Set (𝔽₂ n))=S := S.toFinite.coe_toFinset
  have ct : T.card=Nat.card S := by simp [T]
  have vp : 0 < (Nat.card V : ℝ) := by exact_mod_cast (Nat.card_pos : 0 < Nat.card V)
  have hv : (A.card : ℝ) ≤ 2*Nat.card V := by exact_mod_cast av.le
  have tv : (T.card : ℝ)*Nat.card V = Nat.card W := by rw [ct,← Nat.cast_mul,cs]
  refine ⟨V,F+T,va,?_,?_⟩
  · refine (show ((F+T).card : ℝ) ≤ (F.card : ℝ)*T.card by exact_mod_cast card_add_le).trans ?_
    apply le_of_mul_le_mul_right (a := (B.card : ℝ)*Nat.card V) _ (mul_pos bpos vp)
    calc
      (F.card : ℝ)*T.card*(B.card*Nat.card V) = ((F.card : ℝ)*B.card)*(T.card*Nat.card V) := by ring
      _ = ((F.card : ℝ)*B.card)*Nat.card W := by rw [tv]
      _ ≤ (K*A.card)*(K^11*B.card) := by gcongr
      _ ≤ (K*(2*Nat.card V))*(K^11*B.card) := by gcongr
      _ = 2*K^12*(B.card*Nat.card V) := by ring
  · rw [Finset.coe_add,et,add_assoc,hs]
    exact cov


theorem Green49Sharp.concentrate : ∀ n (A : Finset (𝔽₂ n)), A.Nonempty → ∀ K : ℝ, 1 ≤ K →
    ((A+A).card : ℝ) ≤ K*A.card →
    ∃ (W : Submodule (ZMod 2) (𝔽₂ n)) (B : Finset (𝔽₂ n)),
      B.Nonempty ∧ B ⊆ A ∧ ((B-B : Finset _) : Set (𝔽₂ n)) ⊆ W ∧
      (A.card : ℝ) ≤ K^11*B.card ∧ (Nat.card W : ℝ) ≤ K^11*B.card := by
  intro n A ha K k1 doubling
  classical
  obtain ⟨W,B,bne,ba,diff,mass,small⟩ := green49_popular_sharp (A:=(A : Set (𝔽₂ n)))
    (K:=K) ha.to_set (by simpa only [← Finset.coe_add,Set.ncard_coe_finset] using doubling)
  let S := B.toFinite.toFinset
  have e : (S : Set (𝔽₂ n)) = B := B.toFinite.coe_toFinset
  have c : S.card = B.ncard := by rw [← e, Set.ncard_coe_finset]
  refine ⟨W,S,?_,?_,?_,?_,?_⟩
  · exact Finset.coe_nonempty.mp (e ▸ bne)
  · intro x hx
    exact ba (e ▸ (show x∈(S : Set _) from hx))
  · rwa [Finset.coe_sub,e]
  · simpa only [c, Set.ncard_coe_finset] using mass
  · simpa only [c] using small

theorem OMA.solution : type_of% @Green49.green_49 :=
  Green49Sharp.cover Green49Sharp.concentrate
