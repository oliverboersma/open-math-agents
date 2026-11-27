import FormalConjectures.GreensOpenProblems.«32»
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finset.Density
import Mathlib.Data.Finset.Sort
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-
Credit: @LDJAI for the application to Green's Problem 32.
The finite Szemerédi proof below is adapted from Gabriel Dahia's DensityHalesJewett,
commit 27e0e647664afe404fd3fef9425920819ca48b3e, Apache-2.0.
Copyright (c) 2026 Gabriel Dahia. See https://github.com/gdahia/DensityHalesJewett .
Adaptations combine the required modules into this file for the registry checker.
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

/-! From DensityHalesJewett.Word by Gabriel Dahia. -/

open Finset
open scoped BigOperators

namespace DensityHalesJewett

/-- The fiber of a word family above a fixed prefix.  Words on a sum of coordinate types are
concatenations `Sum.elim x y` of their two parts. -/
def fiber {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) (x : ι → α) : Finset (κ → α) :=
  Finset.univ.filter fun y ↦ Sum.elim x y ∈ A

@[simp]
lemma mem_fiber {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {A : Finset (ι ⊕ κ → α)} {x : ι → α} {y : κ → α} :
    y ∈ fiber A x ↔ Sum.elim x y ∈ A := by
  simp [fiber]

/-- Uniform density is the average of the uniform densities of the fibers. -/
lemma average_density_fiber {α ι κ : Type*} [Fintype (ι → α)] [Fintype (κ → α)]
    [Fintype (ι ⊕ κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (A : Finset (ι ⊕ κ → α)) :
    (𝔼 x : ι → α, ((fiber A x).dens : ℝ)) = (A.dens : ℝ) := by
  classical
  simp_rw [← Finset.expect_indicator_one]
  rw [← Finset.expect_product']
  apply Finset.expect_equiv (Equiv.sumArrowEquivProdArrow ι κ α).symm
  · simp
  · rintro ⟨x, y⟩ -
    simp [Set.indicator_apply, Equiv.sumArrowEquivProdArrow]

/-- A bounded function with large average exceeds a lower threshold on a quantitatively large
set. -/
lemma density_ge_threshold {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (a b : ℝ) (hf₁ : ∀ x, f x ≤ 1)
    (hba : b < a) (havg : a ≤ 𝔼 x : X, f x) :
    (a - b) / (1 - b) ≤
      ((Finset.univ.filter fun x ↦ b ≤ f x).dens : ℝ) := by
  classical
  let H := Finset.univ.filter fun x ↦ b ≤ f x
  change (a - b) / (1 - b) ≤ (H.dens : ℝ)
  have h1b : 0 < 1 - b := by
    rw [sub_pos]
    exact hba.trans_le <| havg.trans <|
      Finset.expect_le Finset.univ_nonempty fun x _ ↦ hf₁ x
  rw [div_le_iff₀ h1b, sub_le_iff_le_add]
  apply havg.trans
  convert Finset.expect_le_expect (s := Finset.univ) (f := f)
    (g := fun x ↦ b + (1 - b) * Set.indicator (H : Set X) 1 x) ?_ using 1
  · symm
    rw [Finset.expect_add_distrib]
    simp only [Fintype.expect_const, ← Finset.mul_expect, Finset.expect_indicator_one]
    ring
  · intro x _
    by_cases hx : b ≤ f x <;> simp [H, hx] <;> linarith [hf₁ x]

end DensityHalesJewett

end

section

/-! From DensityHalesJewett.Subspace by Gabriel Dahia. -/

open Finset Function
open Combinatorics

namespace DensityHalesJewett
namespace Subspace

variable {η α ι : Type*}

/-- Evaluation by a fixed combinatorial subspace is injective. -/
lemma injective (V : Combinatorics.Subspace η α ι) :
    Function.Injective V := by
  intro x y hxy
  funext e
  obtain ⟨i, hi⟩ := V.proper e
  simpa only [V.apply_inr hi] using congrFun hxy i

/-- The finite range of a combinatorial subspace. -/
def range [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) : Finset (ι → α) :=
  Finset.univ.image V

@[simp]
lemma mem_range [Fintype (η → α)] [DecidableEq (ι → α)]
    {V : Combinatorics.Subspace η α ι} {w : ι → α} :
    w ∈ range V ↔ ∃ x, V x = w := by
  simp [range]

/-- A subspace is contained in a finite word family when all its evaluations belong to it. -/
def IsContained (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : Prop :=
  ∀ x, V x ∈ A

/-- Compose a parameter subspace with an ambient subspace. -/
def compose (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η) :
    Combinatorics.Subspace θ α ι where
  idxFun i := (V.idxFun i).elim Sum.inl W.idxFun
  proper e := by
    obtain ⟨j, hj⟩ := W.proper e
    obtain ⟨i, hi⟩ := V.proper j
    refine ⟨i, ?_⟩
    simp only [hi, Sum.elim_inr, hj]

@[simp]
lemma compose_apply (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η)
    (x : θ → α) : compose V W x = V (W x) := by
  funext i
  cases hi : V.idxFun i <;> simp [compose, Combinatorics.Subspace.coe_apply, hi]

/-- Repeat the first `m` parameter directions to fill a larger `M`-coordinate cube. -/
def repeatInitial {m M : ℕ} (α : Type*) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Combinatorics.Subspace (Fin m) α (Fin M) where
  idxFun i := Sum.inr <|
    if hi : i.val < m then ⟨i.val, hi⟩ else ⟨0, Nat.zero_lt_of_lt hm⟩
  proper e := by
    refine ⟨Fin.castLE hmM e, ?_⟩
    simp only [Fin.castLE, e.isLt, ↓reduceDIte]

@[simp]
lemma repeatInitial_map {β : Type*} {m M : ℕ} (α : Type*) (hm : 1 ≤ m) (hmM : m ≤ M)
    (f : β → α) (x : Fin m → β) :
    repeatInitial α hm hmM (f ∘ x) = f ∘ repeatInitial β hm hmM x := by
  funext i
  simp only [Function.comp_apply, (repeatInitial α hm hmM).apply_inr rfl,
    (repeatInitial β hm hmM).apply_inr rfl]

/-- Concatenate subspaces on disjoint coordinate blocks. -/
def concat (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α κ) :
    Combinatorics.Subspace (η ⊕ θ) α (ι ⊕ κ) where
  idxFun := Sum.elim
    (fun i ↦ (V.idxFun i).elim Sum.inl (fun e ↦ Sum.inr <| Sum.inl e))
    (fun i ↦ (W.idxFun i).elim Sum.inl (fun e ↦ Sum.inr <| Sum.inr e))
  proper e := by
    cases e with
    | inl e =>
      obtain ⟨i, hi⟩ := V.proper e
      refine ⟨Sum.inl i, ?_⟩
      simp only [hi, Sum.elim_inl, Sum.elim_inr]
    | inr e =>
      obtain ⟨i, hi⟩ := W.proper e
      refine ⟨Sum.inr i, ?_⟩
      simp only [hi, Sum.elim_inr]

@[simp]
lemma concat_apply (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α κ)
    (x : η → α) (y : θ → α) : concat V W (Sum.elim x y) =
      Sum.elim (V x) (W y) := by
  funext i
  cases i with
  | inl i => cases hi : V.idxFun i <;> simp [concat, Combinatorics.Subspace.coe_apply, hi]
  | inr i => cases hi : W.idxFun i <;> simp [concat, Combinatorics.Subspace.coe_apply, hi]

/-- Regard a line as a one-dimensional subspace parameterized by `Fin 1`. -/
def lineToSubspaceFinOne (l : Combinatorics.Line α ι) :
    Combinatorics.Subspace (Fin 1) α ι :=
  l.toSubspaceUnit.reindex finOneEquiv.symm (Equiv.refl _) (Equiv.refl _)

@[simp]
lemma lineToSubspaceFinOne_apply (l : Combinatorics.Line α ι) (x : Fin 1 → α) :
    lineToSubspaceFinOne l x = l (x 0) := by
  funext i
  simp [lineToSubspaceFinOne, Fin.eq_zero]

/-- Relative density on a subspace, defined on its parameter cube. -/
def relativeDensity [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℚ≥0 :=
  (Finset.univ.filter fun x ↦ V x ∈ A).dens

/-- Ambient line structures whose evaluations are contained in a subspace. -/
def Lines [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) :=
  {l : Combinatorics.Line α ι // ∀ a, l a ∈ range V}

/-- Compose a parameter-cube line with a combinatorial subspace. -/
def composeLine (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := by
    obtain ⟨e, he⟩ := l.proper
    obtain ⟨i, hi⟩ := V.proper e
    refine ⟨i, ?_⟩
    simp only [hi, Sum.elim_inr, he]

@[simp]
lemma composeLine_apply (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η)
    (a : α) : composeLine V l a = V (l a) := by
  funext i
  cases hi : V.idxFun i <;>
    simp [composeLine, Combinatorics.Line.coe_apply, Combinatorics.Subspace.coe_apply, hi]

/-- Regard the composite of a parameter line with a subspace as a line in that subspace. -/
def composeLineToLines [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) : Lines V :=
  ⟨composeLine V l, fun a ↦ mem_range.mpr ⟨l a, (composeLine_apply V l a).symm⟩⟩

/-- The canonical parameter word representing a point of a line contained in a subspace. -/
noncomputable def parameterWord [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) : η → α :=
  Classical.choose <| mem_range.mp (q.2 a)

lemma parameterWord_apply [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) :
    V (parameterWord V q a) = q.1 a :=
  Classical.choose_spec <| mem_range.mp (q.2 a)

/-- A chosen coordinate on which a subspace realizes a given parameter direction. -/
noncomputable def properCoordinate (V : Combinatorics.Subspace η α ι) (e : η) : ι :=
  Classical.choose <| V.proper e

lemma properCoordinate_spec (V : Combinatorics.Subspace η α ι) (e : η) :
    V.idxFun (properCoordinate V e) = Sum.inr e :=
  Classical.choose_spec <| V.proper e

/-- Recover the parameter-cube line underlying an ambient line contained in a subspace. -/
noncomputable def uncomposeLine [Fintype (η → α)] [DecidableEq (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) : Combinatorics.Line α η where
  idxFun e := q.1.idxFun (properCoordinate V e)
  proper := by
    obtain ⟨j, hj⟩ := q.1.proper
    cases hVj : V.idxFun j with
    | inl b =>
      obtain ⟨a, hab⟩ := exists_ne b
      refine absurd ?_ hab
      rw [← q.1.apply_none a j hj, ← parameterWord_apply V q a]
      exact V.apply_inl hVj
    | inr e =>
      cases hq : q.1.idxFun (properCoordinate V e) with
      | none => exact ⟨e, hq⟩
      | some c =>
        obtain ⟨a, hac⟩ := exists_ne c
        exact absurd (by rw [← q.1.apply_none a j hj, ← q.1.apply_some hq,
          ← parameterWord_apply V q a, V.apply_inr (properCoordinate_spec V e),
          V.apply_inr hVj]) hac

lemma uncomposeLine_apply [Fintype (η → α)] [DecidableEq (ι → α)] [Nontrivial α]
    (V : Combinatorics.Subspace η α ι) (q : Lines V) (a : α) :
    V (uncomposeLine V q a) = q.1 a := by
  funext i
  cases hi : V.idxFun i with
  | inl b => rw [V.apply_inl hi, ← parameterWord_apply V q a, V.apply_inl hi]
  | inr e =>
    rw [V.apply_inr hi]
    change q.1 a (properCoordinate V e) = q.1 a i
    rw [← parameterWord_apply V q a, V.apply_inr (properCoordinate_spec V e), V.apply_inr hi]

/-- Composition with a subspace identifies parameter-cube lines with ambient lines contained in
the subspace. -/
noncomputable def linesEquiv [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) :
    Combinatorics.Line α η ≃ Lines V where
  toFun := composeLineToLines V
  invFun := uncomposeLine V
  left_inv := by
    intro l
    apply Combinatorics.Line.coe_injective
    funext a
    apply injective V
    rw [uncomposeLine_apply]
    exact composeLine_apply V l a
  right_inv := by
    intro q
    apply Subtype.ext
    change composeLine V (uncomposeLine V q) = q.1
    apply Combinatorics.Line.coe_injective
    funext a
    rw [composeLine_apply]
    exact uncomposeLine_apply V q a

/-- Map a parameter-cube line to the corresponding ambient line in a subspace. -/
noncomputable def mapLine [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    Combinatorics.Line α ι :=
  (linesEquiv V l).1

lemma mapLine_eq_composeLine [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    mapLine V l = composeLine V l :=
  rfl

@[simp]
lemma mapLine_apply [Fintype (η → α)] [DecidableEq (ι → α)]
    [Nontrivial α] (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η)
    (a : α) : mapLine V l a = V (l a) :=
  composeLine_apply V l a

/-- Restrict the variable letters of a subspace along an alphabet embedding. -/
def restrictAlphabet {β : Type*} [Fintype (η → β)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (e : β ↪ α) : Finset (ι → α) :=
  Finset.univ.image fun x ↦ V (e ∘ x)

end Subspace
end DensityHalesJewett

end

section

/-! From DensityHalesJewett.Canonization by Gabriel Dahia. -/

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Two words over `Option α` have the same support when their variable positions agree. -/
def SameSupport {α ι : Type*} (x y : ι → Option α) : Prop := ∀ i, x i = none ↔ y i = none

namespace Line

variable {α ι : Type*}

/-- The word obtained from a line by substituting a letter, or the variable itself, at its
variable positions. -/
def fillOption (l : Combinatorics.Line α ι) (v : Option α) : ι → Option α :=
  fun i ↦ (l.idxFun i).elim v some

@[simp]
lemma fillOption_some (l : Combinatorics.Line α ι) (a : α) :
    fillOption l (some a) = some ∘ l a := by
  funext i
  cases h : l.idxFun i <;> simp [fillOption, Combinatorics.Line.coe_apply, h]

end Line

namespace Subspace

variable {α η θ ι : Type*}

/-- Substitute a word over `Option α` into a combinatorial subspace, marking variable positions
of the parameter word by `none`. -/
def wordMap (V : Combinatorics.Subspace η α ι) (x : η → Option α) : ι → Option α :=
  fun i ↦ Sum.elim some x (V.idxFun i)

lemma wordMap_compose (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace θ α η)
    (x : θ → Option α) : wordMap (compose V W) x = wordMap V (wordMap W x) := by
  funext i
  cases h : V.idxFun i <;> simp [wordMap, compose, h]

lemma composeLine_idxFun (V : Combinatorics.Subspace η α ι) (l : Combinatorics.Line α η) :
    (composeLine V l).idxFun = wordMap V l.idxFun :=
  rfl

/-- Prepend a new variable direction, realized by a line on a fresh block of coordinates, to the
directions of a subspace. -/
def consLine {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') : Combinatorics.Subspace (Fin (ℓ + 1)) α (B ⊕ B') where
  idxFun := Sum.elim (fun b ↦ (V.idxFun b).map id Fin.succ)
    fun i ↦ (l.idxFun i).elim (Sum.inr 0) Sum.inl
  proper e := by
    induction e using Fin.cases with
    | zero =>
      obtain ⟨i, hi⟩ := l.proper
      exact ⟨Sum.inr i, by simp [hi]⟩
    | succ j =>
      obtain ⟨b, hb⟩ := V.proper j
      exact ⟨Sum.inl b, by simp [hb]⟩

lemma wordMap_consLine {ℓ : ℕ} {B B' : Type*} (V : Combinatorics.Subspace (Fin ℓ) α B)
    (l : Combinatorics.Line α B') (x : Fin (ℓ + 1) → Option α) :
    wordMap (consLine V l) x
      = Sum.elim (wordMap V fun i ↦ x i.succ) (Line.fillOption l (x 0)) := by
  funext i
  cases i with
  | inl b => cases h : V.idxFun b <;> simp [wordMap, consLine, h]
  | inr i => cases h : l.idxFun i <;> simp [wordMap, consLine, Line.fillOption, h]

/-- Embed the first `N` coordinates of a cube into a larger one, filling the remaining
coordinates with a fixed letter. -/
noncomputable def padInitial (α : Type*) [Nonempty α] {N n : ℕ} (h : N ≤ n) :
    Combinatorics.Subspace (Fin N) α (Fin n) where
  idxFun i := if hi : i.val < N then Sum.inr ⟨i.val, hi⟩ else Sum.inl (Classical.arbitrary α)
  proper e := ⟨Fin.castLE h e, by simp [Fin.castLE, e.isLt]⟩

end Subspace

namespace Canonization

variable {α : Type*}

open Subspace

/-- The inductive form of support canonization: for any block of positions preceding the
variables and any block of variable slots following them, there is a block of positions carrying
`ℓ` variables on which every colouring becomes a function of the support alone. -/
private lemma exists_canonical_aux (α : Type*) [Finite α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∀ (P S : Type) [Finite P] [Finite S], ∃ (B : Type) (_ : Finite B),
      ∀ χ : (P → Option α) → (B → Option α) → (S → Option α) → C,
        ∃ V : Combinatorics.Subspace (Fin ℓ) α B,
          ∀ (p : P → Option α) (s : S → Option α) (x y : Fin ℓ → Option α),
            SameSupport x y → χ p (wordMap V x) s = χ p (wordMap V y) s := by
  induction ℓ with
  | zero =>
    intro P S _ _
    refine ⟨PEmpty, inferInstance, ?_⟩
    intro χ
    refine ⟨⟨PEmpty.elim, ?_⟩, ?_⟩
    · intro e
      exact e.elim0
    · intro p s _ _ _
      exact congrArg (fun w ↦ χ p w s) (funext fun i ↦ i.elim)
  | succ ℓ ih =>
    intro P S _ _
    obtain ⟨B, _, hB⟩ := ih P (Unit ⊕ S)
    obtain ⟨B', _, hB'⟩ := Combinatorics.Line.exists_mono_in_high_dimension α
      ((P → Option α) → (B → Option α) → (S → Option α) → C)
    refine ⟨B ⊕ B', inferInstance, ?_⟩
    intro χ
    obtain ⟨l, prof, hprof⟩ := hB' fun u p b s ↦ χ p (Sum.elim b (some ∘ u)) s
    have hprof' : ∀ (a : α) (p : P → Option α) (b : B → Option α) (s : S → Option α),
        χ p (Sum.elim b (some ∘ l a)) s = prof p b s :=
      fun a p b s ↦ congrFun (congrFun (congrFun (hprof a) p) b) s
    obtain ⟨V, hV⟩ := hB fun p b q ↦
      χ p (Sum.elim b (Line.fillOption l (q (Sum.inl ())))) fun s ↦ q (Sum.inr s)
    refine ⟨consLine V l, ?_⟩
    intro p s x y hxy
    rw [wordMap_consLine, wordMap_consLine]
    apply Eq.trans (hV p (Sum.elim (fun _ ↦ x 0) s) (fun i ↦ x i.succ) (fun i ↦ y i.succ)
      fun i ↦ hxy i.succ)
    simp only [Sum.elim_inl, Sum.elim_inr]
    cases hx : x 0 with
    | none => rw [(hxy 0).1 hx]
    | some a =>
      cases hy : y 0 with
      | none => simp [(hxy 0).2 hy] at hx
      | some b =>
        rw [Line.fillOption_some, Line.fillOption_some, hprof' a, hprof' b]

/-- **Support canonization**: in a large enough cube every colouring of words over `Option α`
admits an `ℓ`-dimensional subspace on which the colour of a substituted word depends only on its
support. -/
lemma exists_canonical (α : Type*) [Finite α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∃ N : ℕ, ∀ χ : (Fin N → Option α) → C,
      ∃ V : Combinatorics.Subspace (Fin ℓ) α (Fin N),
        ∀ x y : Fin ℓ → Option α, SameSupport x y → χ (wordMap V x) = χ (wordMap V y) := by
  obtain ⟨B, _, hB⟩ := exists_canonical_aux α C ℓ PEmpty PEmpty
  have := Fintype.ofFinite B
  refine ⟨Fintype.card B, ?_⟩
  intro χ
  obtain ⟨V, hV⟩ := hB fun _ w _ ↦ χ (w ∘ (Fintype.equivFin B).symm)
  have hw (z : Fin ℓ → Option α) :
      wordMap (V.reindex (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin B)) z
        = wordMap V z ∘ (Fintype.equivFin B).symm := by
    funext i
    cases h : V.idxFun ((Fintype.equivFin B).symm i) <;>
      simp [wordMap, Combinatorics.Subspace.reindex, h]
  refine ⟨V.reindex (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin B), ?_⟩
  intro x y hxy
  rw [hw x, hw y]
  exact hV PEmpty.elim PEmpty.elim x y hxy

/-- Support canonization holds in every ambient dimension beyond the one it produces. -/
lemma exists_canonical_of_le (α : Type*) [Finite α] [Nonempty α] (C : Type*) [Finite C] (ℓ : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ χ : (Fin n → Option α) → C,
      ∃ V : Combinatorics.Subspace (Fin ℓ) α (Fin n),
        ∀ x y : Fin ℓ → Option α, SameSupport x y → χ (wordMap V x) = χ (wordMap V y) := by
  obtain ⟨N, hN⟩ := exists_canonical α C ℓ
  refine ⟨N, ?_⟩
  intro n hn χ
  obtain ⟨V, hV⟩ := hN fun w ↦ χ (wordMap (padInitial α hn) w)
  refine ⟨compose (padInitial α hn) V, ?_⟩
  intro x y hxy
  rw [wordMap_compose, wordMap_compose]
  exact hV x y hxy

end Canonization
end DensityHalesJewett

end

section

/-! From DensityHalesJewett.FiniteUnions by Gabriel Dahia. -/

open Finset
open Combinatorics

namespace DensityHalesJewett
namespace FiniteUnions

/-- A translated combinatorial cube of sets: a base block `E` and wildcard blocks `G` such that
every union of `E` with a subfamily of the `G` has the same colour. -/
lemma exists_translatedCube (C : Type*) [Finite C] (n : ℕ) :
    ∃ M : ℕ, ∀ d : Finset (Fin M) → C,
      ∃ (E : Finset (Fin M)) (G : Fin n → Finset (Fin M)),
        E.Nonempty ∧ (∀ i, (G i).Nonempty) ∧ (∀ i, Disjoint E (G i)) ∧
          (∀ i j, i ≠ j → Disjoint (G i) (G j)) ∧
          ∃ c, ∀ I : Finset (Fin n), d (E ∪ I.biUnion G) = c := by
  classical
  obtain ⟨M, hM⟩ := Combinatorics.Subspace.exists_mono_in_high_dimension_fin Bool C (Fin (n + 1))
  refine ⟨M, ?_⟩
  intro d
  obtain ⟨W, c, hc⟩ := hM fun x ↦ d {i | x i}
  set S : Finset (Fin M) := {i | W.idxFun i = Sum.inl true} with hS
  set X : Fin (n + 1) → Finset (Fin M) := fun j ↦ {i | W.idxFun i = Sum.inr j} with hX
  have hXne : ∀ j, (X j).Nonempty := by
    intro j
    obtain ⟨i, hi⟩ := W.proper j
    exact ⟨i, by simp [hX, hi]⟩
  have hXX : ∀ j j', j ≠ j' → Disjoint (X j) (X j') := by
    simp only [Finset.disjoint_left, hX, Finset.mem_filter, Finset.mem_univ, true_and]
    grind
  have hSX : ∀ j, Disjoint S (X j) := by
    simp only [Finset.disjoint_left, hS, hX, Finset.mem_filter, Finset.mem_univ, true_and]
    grind
  have key : ∀ J : Finset (Fin (n + 1)), d (S ∪ J.biUnion X) = c := by
    intro J
    rw [← hc fun j ↦ decide (j ∈ J)]
    congr 1
    ext i
    simp only [hS, hX, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_biUnion]
    rw [Combinatorics.Subspace.coe_apply]
    cases h : W.idxFun i with
    | inl b => cases b <;> simp
    | inr j => simp
  refine ⟨S ∪ X 0, fun i ↦ X i.succ, (hXne 0).mono Finset.subset_union_right,
    fun i ↦ hXne _, ?_, fun i j hij ↦ hXX _ _ fun h ↦ hij (Fin.succ_injective _ h),
    c, ?_⟩
  · intro i
    exact Finset.disjoint_union_left.2 ⟨hSX _, hXX _ _ (Fin.succ_ne_zero i).symm⟩
  · intro I
    convert key (insert 0 (I.image Fin.succ)) using 2
    ext i
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image]
    grind

/-- Iterating the translated cube canonizes the colour of a union of blocks in terms of the least
block that it contains. -/
lemma exists_minCanonical (C : Type*) [Finite C] (t : ℕ) :
    ∃ D : ℕ, ∀ d : Finset (Fin D) → C, ∃ E : Fin t → Finset (Fin D),
      (∀ i, (E i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        ∃ f : Fin t → C, ∀ (J : Finset (Fin t)) (hJ : J.Nonempty),
          d (J.biUnion E) = f (J.min' hJ) := by
  classical
  induction t with
  | zero =>
    refine ⟨0, ?_⟩
    intro d
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, Fin.elim0, ?_⟩
    intro J hJ
    simp [Finset.eq_empty_of_isEmpty J] at hJ
  | succ t ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨M, hM⟩ := exists_translatedCube C D
    refine ⟨M, ?_⟩
    intro d
    obtain ⟨E₀, G, hE₀, hG, hE₀G, hGG, c, hc⟩ := hM d
    obtain ⟨I, hI, hII, f, hf⟩ := hD fun K ↦ d (K.biUnion G)
    refine ⟨Fin.cons E₀ fun j ↦ (I j).biUnion G, ?_, ?_, Fin.cons c f, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hE₀
      | succ j => simpa using (hI j).biUnion fun g _ ↦ hG g
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simpa using (Finset.disjoint_biUnion_right _ _ _).2 fun g _ ↦ hE₀G g
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simpa using
            (Finset.disjoint_biUnion_left _ _ _).2 fun g _ ↦ (hE₀G g).symm
        | succ j =>
          simp only [Fin.cons_succ, Finset.disjoint_biUnion_left, Finset.disjoint_biUnion_right]
          intro g hg g' hg'
          apply hGG g' g
          intro hgg'
          refine (hII i j ?_).notMem_of_mem_left_finset hg' (hgg' ▸ hg)
          intro h
          exact hij (congrArg Fin.succ h)
    · intro J hJ
      set K : Finset (Fin t) := {j | j.succ ∈ J} with hK
      have himage : J.erase 0 = K.image Fin.succ := by
        ext i
        induction i using Fin.cases with
        | zero => simp
        | succ j => simp [hK, Fin.succ_ne_zero]
      have hbiUnion : (J.erase 0).biUnion (Fin.cons E₀ fun j ↦ (I j).biUnion G)
          = (K.biUnion I).biUnion G := by
        simp [himage, Finset.image_biUnion, Finset.biUnion_biUnion]
      by_cases h0 : (0 : Fin (t + 1)) ∈ J
      · have hmin : J.min' hJ = 0 := le_antisymm (Finset.min'_le _ _ h0) (Fin.zero_le _)
        rw [hmin, ← Finset.insert_erase h0, Finset.biUnion_insert, hbiUnion]
        simpa using hc _
      · have hKne : K.Nonempty := by
          obtain ⟨i, hi⟩ := hJ
          induction i using Fin.cases with
          | zero => exact absurd hi h0
          | succ j => exact ⟨j, by simpa [hK] using hi⟩
        have hJK : J = K.image Fin.succ := by rw [← himage, Finset.erase_eq_of_notMem h0]
        have hmin : J.min' hJ = (K.min' hKne).succ := by
          simp_rw [hJK]
          exact Finset.min'_image (fun _ _ h ↦ Fin.succ_le_succ_iff.2 h) K _
        rw [hmin, ← Finset.erase_eq_of_notMem h0, hbiUnion]
        simpa using hf K hKne

/-- The finite disjoint unions theorem: for every colouring of the subsets of a large enough
finite index set there are `m` pairwise disjoint nonempty blocks all of whose nonempty unions
receive the same colour. -/
lemma exists_monochromaticUnions (C : Type*) [Finite C] (m : ℕ) :
    ∃ D : ℕ, ∀ d : Finset (Fin D) → C, ∃ E : Fin m → Finset (Fin D),
      (∀ i, (E i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        ∃ c, ∀ J : Finset (Fin m), J.Nonempty → d (J.biUnion E) = c := by
  classical
  let _ := Fintype.ofFinite C
  obtain ⟨D, hD⟩ := exists_minCanonical C ((m - 1) * Fintype.card C + 1)
  refine ⟨D, ?_⟩
  intro d
  obtain ⟨E, hE, hEE, f, hf⟩ := hD d
  obtain ⟨c, -, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := Finset.univ)
      (t := (Finset.univ : Finset C)) (f := f) (n := m - 1) (fun a _ ↦ Finset.mem_univ _) (by
        simp only [Finset.card_univ, Fintype.card_fin]
        rw [Nat.mul_comm]
        omega)
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := {i | f i = c}) (n := m) (by omega)
  refine ⟨fun j ↦ E (T.orderEmbOfFin hTcard j), fun j ↦ hE _,
    fun i j hij ↦ hEE _ _ fun h ↦ hij ((T.orderEmbOfFin hTcard).injective h), c, ?_⟩
  intro J hJ
  rw [← Finset.image_biUnion, hf _ (hJ.image _)]
  obtain ⟨j, -, hj⟩ :=
    Finset.mem_image.1 (Finset.min'_mem _ (hJ.image (T.orderEmbOfFin hTcard)))
  rw [← hj]
  simpa using hTsub (T.orderEmbOfFin_mem hTcard j)

end FiniteUnions
end DensityHalesJewett

end

section

/-! From DensityHalesJewett.GrahamRothschild by Gabriel Dahia. -/

open Finset
open Combinatorics

namespace DensityHalesJewett

namespace GrahamRothschild

open Subspace

variable {α ι C : Type*} [DecidableEq ι] {m n : ℕ}

/-- The subspace whose variable directions are pairwise disjoint nonempty blocks of coordinates,
all remaining coordinates carrying a fixed letter. -/
noncomputable def ofBlocks (a₀ : α) (E : Fin m → Finset ι) (hE : ∀ j, (E j).Nonempty)
    (hEE : ∀ i j, i ≠ j → Disjoint (E i) (E j)) : Combinatorics.Subspace (Fin m) α ι where
  idxFun i := if h : ∃ j, i ∈ E j then Sum.inr h.choose else Sum.inl a₀
  proper e := by
    obtain ⟨i, hi⟩ := hE e
    refine ⟨i, ?_⟩
    rw [dif_pos ⟨e, hi⟩]
    apply congrArg Sum.inr
    by_contra hne
    exact Finset.disjoint_left.1 (hEE _ _ hne) (Exists.choose_spec (⟨e, hi⟩ : ∃ j, i ∈ E j)) hi

variable {a₀ : α} {E : Fin m → Finset ι} {hE : ∀ j, (E j).Nonempty}
  {hEE : ∀ i j, i ≠ j → Disjoint (E i) (E j)}

lemma ofBlocks_idxFun_of_mem {i : ι} {j : Fin m} (hij : i ∈ E j) :
    (ofBlocks a₀ E hE hEE).idxFun i = Sum.inr j := by
  simp only [ofBlocks]
  rw [dif_pos ⟨j, hij⟩]
  apply congrArg Sum.inr
  by_contra hne
  exact Finset.disjoint_left.1 (hEE _ _ hne) (Exists.choose_spec (⟨j, hij⟩ : ∃ j, i ∈ E j)) hij

lemma ofBlocks_idxFun_of_notMem {i : ι} (hi : ∀ j, i ∉ E j) :
    (ofBlocks a₀ E hE hEE).idxFun i = Sum.inl a₀ := by
  simp only [ofBlocks]
  rw [dif_neg (by simpa using hi)]

/-- The support of a word substituted into `ofBlocks` is the union of the blocks indexed by the
support of that word. -/
lemma sameSupport_wordMap_ofBlocks (x : Fin m → Option α) (J : Finset (Fin m))
    (hJ : ∀ j, j ∈ J ↔ x j = none) :
    SameSupport (wordMap (ofBlocks a₀ E hE hEE) x)
      fun i ↦ if i ∈ J.biUnion E then none else some a₀ := by
  have hite : ∀ i : ι, ((if i ∈ J.biUnion E then none else some a₀ : Option α) = none)
      ↔ i ∈ J.biUnion E := by
    intro i
    split <;> simp [*]
  intro i
  rw [wordMap]
  by_cases h : ∃ j, i ∈ E j
  · obtain ⟨j, hj⟩ := h
    rw [ofBlocks_idxFun_of_mem hj, Sum.elim_inr, ← hJ j, hite i, Finset.mem_biUnion]
    constructor
    · intro hjJ
      exact ⟨j, hjJ, hj⟩
    · rintro ⟨j', hj'J, hij'⟩
      by_contra hne
      refine Finset.disjoint_left.1 (hEE j j' ?_) hj hij'
      intro hjj'
      apply hne
      rw [hjj']
      exact hj'J
  · rw [not_exists] at h
    rw [ofBlocks_idxFun_of_notMem h, Sum.elim_inl, hite i]
    simp [Finset.mem_biUnion, h]

/-- Extend a colouring of the lines of a cube to a colouring of all words over `Option α`. -/
private noncomputable def extend [Nonempty C] (χ : Combinatorics.Line α (Fin n) → C)
    (w : Fin n → Option α) : C :=
  if h : ∃ i, w i = none then χ ⟨w, h⟩ else Classical.arbitrary C

private lemma extend_idxFun [Nonempty C] (χ : Combinatorics.Line α (Fin n) → C)
    (l : Combinatorics.Line α (Fin n)) : extend χ l.idxFun = χ l :=
  dif_pos l.proper

/-- **Graham--Rothschild for lines**: beyond a dimension depending only on the alphabet, the
number of colours and `m`, every colouring of the lines of a cube is constant on the lines of some
`m`-dimensional combinatorial subspace. -/
lemma exists_lines (α : Type*) [Finite α] [Nonempty α] (C : Type*) [Finite C] [Nonempty C]
    (m : ℕ) : ∃ N : ℕ, ∀ n, N ≤ n → ∀ χ : Combinatorics.Line α (Fin n) → C,
      ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
        ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (composeLine V l) = c := by
  classical
  obtain ⟨L, hL⟩ := FiniteUnions.exists_monochromaticUnions C m
  obtain ⟨N, hN⟩ := Canonization.exists_canonical_of_le α C L
  refine ⟨N, ?_⟩
  intro n hn χ
  obtain ⟨V, hV⟩ := hN n hn (extend χ)
  obtain ⟨E, hE, hEE, c, hc⟩ := hL fun I ↦
    extend χ (wordMap V fun i ↦ if i ∈ I then none else some (Classical.arbitrary α))
  refine ⟨compose V (ofBlocks (Classical.arbitrary α) E hE hEE), c, ?_⟩
  intro l
  rw [← extend_idxFun χ, composeLine_idxFun, wordMap_compose,
    hV _ _ (sameSupport_wordMap_ofBlocks l.idxFun {j | l.idxFun j = none} fun j ↦ by simp)]
  apply hc
  obtain ⟨j, hj⟩ := l.proper
  exact ⟨j, by simpa using hj⟩

/-- The Graham--Rothschild property for `k` letters, `r` colours and dimension `m`, in a cube of
dimension `N`. -/
def IsLineBound (k r m N : ℕ) : Prop :=
  ∀ χ : Combinatorics.Line (Fin k) (Fin N) → Fin r,
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin N),
      ∃ c, ∀ l : Combinatorics.Line (Fin k) (Fin m), χ (composeLine V l) = c

/-- A Graham--Rothschild dimension for colorings of combinatorial lines. -/
noncomputable def bound (alphabet colors dimension : ℕ) : ℕ :=
  sInf {N | ∀ n, N ≤ n → IsLineBound alphabet colors dimension n}

private lemma isLineBound_of_bound_le {k r m : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r) (n : ℕ)
    (hn : bound k r m ≤ n) : IsLineBound k r m n := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact Nat.sInf_mem (exists_lines (Fin k) (Fin r) m) n hn

/-- Transporting a subspace along an alphabet equivalence transports the lines it carries. -/
private lemma composeLine_reindex {β : Type*} (e : α ≃ β)
    (V : Combinatorics.Subspace (Fin m) β (Fin n)) (l : Combinatorics.Line α (Fin m)) :
    composeLine (V.reindex (Equiv.refl _) e.symm (Equiv.refl _)) l
      = Combinatorics.Line.map e.symm (composeLine V (l.map e)) := by
  apply Combinatorics.Line.ext
  funext i
  cases h : V.idxFun i <;>
    simp [composeLine, Combinatorics.Subspace.reindex, Combinatorics.Line.map, h]

/-- The line case of the Graham--Rothschild theorem. -/
lemma lines (α C : Type*) [Fintype α] [Nontrivial α] [Fintype C] [Nonempty C]
    [DecidableEq α] (m n : ℕ)
    (hn : bound (Fintype.card α) (Fintype.card C) m ≤ n)
    (χ : Combinatorics.Line α (Fin n) → C) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      ∃ c, ∀ l : Combinatorics.Line α (Fin m), χ (Subspace.mapLine V l) = c := by
  obtain ⟨V, c, hc⟩ :=
    isLineBound_of_bound_le (k := Fintype.card α) (r := Fintype.card C) (m := m)
      (le_trans one_le_two Fintype.one_lt_card) Fintype.card_pos n hn
      fun l ↦ Fintype.equivFin C (χ (l.map (Fintype.equivFin α).symm))
  refine ⟨V.reindex (Equiv.refl _) (Fintype.equivFin α).symm (Equiv.refl _),
    (Fintype.equivFin C).symm c, ?_⟩
  intro l
  rw [Subspace.mapLine_eq_composeLine, composeLine_reindex, ← hc (l.map (Fintype.equivFin α)),
    Equiv.symm_apply_apply]

/-- The two-color form of Graham--Rothschild used by the density argument. -/
lemma lines_twoColor (α : Type*) [Fintype α] [Nontrivial α] [DecidableEq α]
    (m n : ℕ)
    (hn : bound (Fintype.card α) 2 m ≤ n)
    (L : Finset (Combinatorics.Line α (Fin n))) :
    ∃ V : Combinatorics.Subspace (Fin m) α (Fin n),
      (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∈ L) ∨
        (∀ l : Combinatorics.Line α (Fin m), Subspace.mapLine V l ∉ L) := by
  classical
  obtain ⟨V, c, hc⟩ :=
    lines α (Fin 2) m n hn fun l ↦ if l ∈ L then 0 else 1
  obtain rfl | ⟨c, rfl⟩ := c.eq_zero_or_eq_succ
  · refine ⟨V, ?_⟩
    left
    intro l
    by_contra h
    simpa [h] using hc l
  · refine ⟨V, ?_⟩
    right
    rw [Fin.eq_zero c] at hc
    intro l h
    simpa [h] using hc l

end GrahamRothschild
end DensityHalesJewett

end

section

/-! From DensityHalesJewett.UniformFibers by Gabriel Dahia. -/

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- The density Hales--Jewett assertion for the alphabet `Fin k`. -/
def HasDensityHJ (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
    δ * (k : ℝ) ^ n ≤ #A → ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A

namespace Subspace

/-- A one-dimensional density Hales--Jewett threshold selected from `HasDensityHJ`. -/
noncomputable def densityOneBound (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.find (h.2 δ h.1)
  else 0

lemma densityOneBound_spec {k : ℕ} (hDHJ : HasDensityHJ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityOneBound k δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ a, l a ∈ A := by
  classical
  rw [densityOneBound, dif_pos ⟨hδ, hDHJ⟩] at hn
  exact Nat.find_spec (hDHJ δ hδ) n hn A hA

/-- The one-dimensional case of multidimensional density Hales--Jewett. -/
lemma exists_one_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : densityOneBound k δ ≤ n)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin 1) (Fin k) (Fin n), IsContained V A := by
  obtain ⟨l, hl⟩ := densityOneBound_spec hDHJ δ hδ n hn A hA
  refine ⟨lineToSubspaceFinOne l, ?_⟩
  intro x
  rw [lineToSubspaceFinOne_apply]
  exact hl _

/-- A line is equivalently an `Option`-valued index word with at least one variable
coordinate. -/
private noncomputable def lineIndexEquiv (α ι : Type*) :
    Combinatorics.Line α ι ≃
      {f : ι → Option α // ¬ ∀ i, f i ≠ none} where
  toFun l := by
    refine ⟨l.idxFun, ?_⟩
    intro h
    apply l.proper.elim
    intro i hi
    exact h i hi
  invFun f := ⟨f, by simpa using f.property⟩
  left_inv l := by cases l; rfl
  right_inv _ := Subtype.ext rfl

/-- An index word with no variable coordinate is equivalently an ordinary alphabet word. -/
private noncomputable def fixedIndexWordEquiv (α ι : Type*) [Nonempty α] :
    {f : ι → Option α // ∀ i, f i ≠ none} ≃ (ι → α) where
  toFun f i := (f.1 i).getD (Classical.arbitrary α)
  invFun x := by
    refine ⟨some ∘ x, ?_⟩
    intro i
    exact Option.some_ne_none (x i)
  left_inv f := by
    refine Subtype.ext (funext ?_)
    intro i
    cases hi : f.1 i with
    | none => exact (f.2 i hi).elim
    | some b => simp [hi]
  right_inv x := by simp

/-- The exact number of combinatorial line structures in a nonempty finite-alphabet word cube. -/
lemma card_line (k m : ℕ) (hk : 0 < k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))] :
    Fintype.card (Combinatorics.Line (Fin k) (Fin m)) = (k + 1) ^ m - k ^ m := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [Fintype.card_congr (lineIndexEquiv (Fin k) (Fin m)),
    Fintype.card_subtype_compl (fun f : Fin m → Option (Fin k) ↦ ∀ i, f i ≠ none),
    Fintype.card_pi_const, Fintype.card_option, Fintype.card_fin,
    Fintype.card_congr (fixedIndexWordEquiv (Fin k) (Fin m)),
    Fintype.card_pi_const, Fintype.card_fin]

/-- The finite enumeration of line structures induced by their index words. -/
noncomputable abbrev lineFintype (k m : ℕ) : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
  Fintype.ofInjective (fun l ↦ l.idxFun) fun l₁ l₂ h ↦ by
    cases l₁
    cases l₂
    cases h
    rfl

/-- A subspace over the empty alphabet, obtained by repeating parameter coordinates. -/
def emptyAlphabetSubspace {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Combinatorics.Subspace (Fin m) (Fin 0) (Fin n) where
  idxFun i := Sum.inr ⟨i.val % m, Nat.mod_lt _ (Nat.zero_lt_of_lt hm)⟩
  proper e := ⟨Fin.castLE hmn e, by simp [Nat.mod_eq_of_lt e.isLt]⟩

/-- Every empty-alphabet subspace is contained in every word family. -/
lemma emptyAlphabetSubspace_isContained {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (A : Finset (Fin n → Fin 0)) : IsContained (emptyAlphabetSubspace hm hmn) A := by
  intro x
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)

/-- Convert the cardinal density hypothesis to the normalized finite-set density inequality. -/
lemma density_le_of_card_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ * (k : ℝ) ^ n ≤ #A) :
    δ ≤ (A.dens : ℝ) := by
  rw [Finset.nnratCast_dens]
  refine (le_div_iff₀ ?_).mpr ?_
  · simp only [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  · simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using hA

/-- Convert a normalized density lower bound back to the cardinal form used by the
density Hales--Jewett assertion. -/
lemma card_le_of_density_le {k n : ℕ} (hk : 0 < k) (δ : ℝ)
    (A : Finset (Fin n → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ * (k : ℝ) ^ n ≤ #A := by
  rw [Finset.nnratCast_dens] at hA
  have hpos : 0 < (Fintype.card (Fin n → Fin k) : ℝ) := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
    exact_mod_cast pow_pos hk n
  simpa only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow] using
    (le_div_iff₀ hpos).mp hA

/-- One fiber of a map to a finite nonempty type has at least the average relative density. -/
lemma exists_fiber_density {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (s : Finset X) (f : X → Y) :
    ∃ y, (s.filter fun x ↦ f x = y).dens ≥ (s.dens : ℝ) / Fintype.card Y := by
  classical
  let b : ℝ := #s / Fintype.card Y
  have hb : (#(Finset.univ : Finset Y) : ℕ) • b ≤ ∑ _x ∈ s, (1 : ℝ) := by
    simp only [Finset.card_univ, nsmul_eq_mul, b]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, mul_div_cancel₀]
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨y, _, hy⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (s := s) (t := Finset.univ)
      (f := f) (w := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ Finset.mem_univ _)
      Finset.univ_nonempty hb
  refine ⟨y, ?_⟩
  rw [Finset.nnratCast_dens, Finset.nnratCast_dens]
  change (#s : ℝ) / Fintype.card Y ≤ ∑ x ∈ s with f x = y, (1 : ℝ) at hy
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hy
  rw [ge_iff_le]
  simpa only [div_div, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_one] using
    div_le_div_of_nonneg_right hy (by positivity : 0 ≤ (Fintype.card X : ℝ))

/-- At least half the ambient density lies on prefixes with fiber density at least half as large. -/
lemma half_density_prefixes {k p q : ℕ} (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    δ / 2 ≤
      ((Finset.univ.filter fun x : Fin p → Fin k ↦ δ / 2 ≤ ((fiber A x).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let : Nonempty (Fin p → Fin k) := Pi.instNonempty
  have hδ₁ : δ ≤ 1 := hA.trans (by exact_mod_cast Finset.dens_le_one (s := A))
  have hthreshold := density_ge_threshold (fun x : Fin p → Fin k ↦ ((fiber A x).dens : ℝ))
    δ (δ / 2)
    (fun x ↦ by exact_mod_cast Finset.dens_le_one (s := fiber A x))
    (by linarith) (by simpa only [average_density_fiber] using hA)
  refine le_trans ?_ hthreshold
  refine (le_div_iff₀ ?_).mpr ?_
  · linarith
  · nlinarith

/-- A dense suffix fiber contains a line whose points remain in the ambient family. -/
lemma exists_line_of_fiber_density {k p q : ℕ} (hk : 0 < k) (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : densityOneBound k δ ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (x : Fin p → Fin k)
    (hx : δ ≤ ((fiber A x).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin q), ∀ a, Sum.elim x (l a) ∈ A := by
  obtain ⟨l, hl⟩ :=
    densityOneBound_spec hDHJ δ hδ q hq (fiber A x)
      (card_le_of_density_le hk δ (fiber A x) hx)
  refine ⟨l, ?_⟩
  intro a
  exact mem_fiber.mp (hl a)

/-- One suffix line is complete above a positive-density family of prefixes. -/
lemma exists_common_dense_line {k p q : ℕ} (hk : 0 < k) (hDHJ : HasDensityHJ k)
    (δ : ℝ) (hδ : 0 < δ) (hq : densityOneBound k (δ / 2) ≤ q)
    (A : Finset (Fin p ⊕ Fin q → Fin k)) (hA : δ ≤ (A.dens : ℝ)) :
    letI := lineFintype k q
    ∃ l : Combinatorics.Line (Fin k) (Fin q),
      δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q))) ≤
        ((Finset.univ.filter fun x : Fin p → Fin k ↦
          ∀ a, Sum.elim x (l a) ∈ A).dens : ℝ) := by
  classical
  let := lineFintype k q
  let B := Finset.univ.filter fun x : Fin p → Fin k ↦
    δ / 2 ≤ ((fiber A x).dens : ℝ)
  have hB : δ / 2 ≤ (B.dens : ℝ) := half_density_prefixes hk δ hδ A hA
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.dens_empty] at hB
    simp only [NNRat.cast_zero] at hB
    linarith
  have existsLine (x : {x // x ∈ B}) : ∃ l : Combinatorics.Line (Fin k) (Fin q),
      ∀ a, Sum.elim x (l a) ∈ A :=
    exists_line_of_fiber_density hk hDHJ (δ / 2) (by linarith) hq A x
      (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using x.2)
  choose lineAt hlineAt using existsLine
  let l₀ := lineAt ⟨hBne.choose, hBne.choose_spec⟩
  let : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let f : (Fin p → Fin k) → Combinatorics.Line (Fin k) (Fin q) := fun x ↦
    if hx : x ∈ B then lineAt ⟨x, hx⟩ else l₀
  obtain ⟨l, hl⟩ := exists_fiber_density B f
  refine ⟨l, le_trans ?_ (le_trans hl ?_)⟩
  · simpa only [div_div] using
      div_le_div_of_nonneg_right hB
        (by positivity : 0 ≤ (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ))
  · exact_mod_cast Finset.dens_le_dens <| by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hfl : lineAt ⟨x, hx.1⟩ = l := by
        simpa only [f, dif_pos hx.1] using hx.2
      intro a
      rw [← hfl]
      exact hlineAt ⟨x, hx.1⟩ a

/-- Every positive target density eventually forces a subspace of any fixed positive
dimension. -/
lemma exists_eventually_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n hmn A _
    exact ⟨emptyAlphabetSubspace hm hmn, emptyAlphabetSubspace_isContained hm hmn A⟩
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  induction m, hm using Nat.le_induction generalizing δ with
  | base =>
      exact ⟨densityOneBound k δ, fun n hn A hA ↦
        exists_one_of_density hDHJ δ hδ n hn A hA⟩
  | succ m hm ih =>
      let q := max 1 (densityOneBound k (δ / 2))
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      have hq : densityOneBound k (δ / 2) ≤ q := le_max_right _ _
      let : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
      let := lineFintype k q
      let ε := δ / (2 * Fintype.card (Combinatorics.Line (Fin k) (Fin q)))
      have hε : 0 < ε := by
        have hlinecard : 0 < Fintype.card (Combinatorics.Line (Fin k) (Fin q)) :=
          Fintype.card_pos
        dsimp only [ε]
        exact div_pos hδ (by exact_mod_cast mul_pos (by norm_num : 0 < (2 : ℕ)) hlinecard)
      obtain ⟨P, hP⟩ := ih ε hε
      refine ⟨P + q, ?_⟩
      intro n hn A hA
      let p := n - q
      have hqn : q ≤ n := by omega
      have hpq : p + q = n := Nat.sub_add_cancel hqn
      have hPp : P ≤ p := by omega
      let e : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hpq)
      let wordEquiv : (Fin p ⊕ Fin q → Fin k) ≃ (Fin n → Fin k) :=
        e.arrowCongr (Equiv.refl _)
      let A' := A.map wordEquiv.symm.toEmbedding
      have hA' : δ ≤ (A'.dens : ℝ) := by
        simpa only [A', Finset.dens_map_equiv] using density_le_of_card_le hk δ A hA
      obtain ⟨l, hl⟩ := exists_common_dense_line hk hDHJ δ hδ hq A' hA'
      let C := Finset.univ.filter fun x : Fin p → Fin k ↦
        ∀ a, Sum.elim x (l a) ∈ A'
      have hC : ε ≤ (C.dens : ℝ) := by
        simpa only [ε, C] using hl
      obtain ⟨V, hV⟩ := hP p hPp C (card_le_of_density_le hk ε C hC)
      let W₀ : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin p ⊕ Fin q) :=
        (Subspace.concat V (lineToSubspaceFinOne l)).reindex finSumFinEquiv
          (Equiv.refl _) (Equiv.refl _)
      let W : Combinatorics.Subspace (Fin (m + 1)) (Fin k) (Fin n) :=
        W₀.reindex (Equiv.refl _) (Equiv.refl _) e
      refine ⟨W, ?_⟩
      intro z
      let x : Fin m → Fin k := fun i ↦ z (finSumFinEquiv (Sum.inl i))
      let a : Fin k := z (finSumFinEquiv (Sum.inr 0))
      have hx : Sum.elim (V x) (l a) ∈ A' := by
        have hxC : ∀ b, Sum.elim (V x) (l b) ∈ A' := by
          simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hV x
        exact hxC a
      rw [Finset.mem_map_equiv] at hx
      simp only [Equiv.symm_symm] at hx
      convert hx using 1
      funext i
      simp only [W, W₀, Combinatorics.Subspace.reindex_apply, Equiv.refl_apply,
        Equiv.refl_symm]
      change (Subspace.concat V (lineToSubspaceFinOne l)) (z ∘ finSumFinEquiv) (e.symm i) =
        wordEquiv (Sum.elim (V x) (l a)) i
      have hz : z ∘ finSumFinEquiv =
          Sum.elim x (fun _ : Fin 1 ↦ a) := by
        funext j
        cases j with
        | inl j => rfl
        | inr j => exact congrArg z (congrArg finSumFinEquiv (congrArg Sum.inr (Fin.eq_zero j)))
      rw [hz, Subspace.concat_apply, lineToSubspaceFinOne_apply]
      rfl

/-- A bound for multidimensional density Hales--Jewett. -/
noncomputable def densityBound (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ HasDensityHJ k then
    Nat.find (exists_eventually_of_density h.2.2 m h.1 δ h.2.1)
  else 0

lemma densityBound_spec {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityBound k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A := by
  classical
  rw [densityBound, dif_pos ⟨hm, hδ, hDHJ⟩] at hn
  exact Nat.find_spec (exists_eventually_of_density hDHJ m hm δ hδ) n hn A hA

/-- Multidimensional density Hales--Jewett follows from the one-dimensional assertion. -/
lemma exists_of_density {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityBound k m δ ≤ n) (A : Finset (Fin n → Fin k))
    (hA : δ * (k : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin k) (Fin n), IsContained V A :=
  densityBound_spec hDHJ m hm δ hδ n hn A hA

/-- Split the coordinates of a word family into a prefix and a suffix along a cut equivalence. -/
def splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : Finset (Fin p ⊕ Fin q → Fin alphabet) :=
  A.map (e.arrowCongr (Equiv.refl (Fin alphabet))).symm.toEmbedding

@[simp]
lemma mem_splitWords {alphabet p q n : ℕ} {e : Fin p ⊕ Fin q ≃ Fin n}
    {A : Finset (Fin n → Fin alphabet)} {w : Fin p ⊕ Fin q → Fin alphabet} :
    w ∈ splitWords e A ↔ w ∘ e.symm ∈ A := by
  rw [splitWords, Finset.mem_map_equiv, Equiv.symm_symm]
  rfl

@[simp]
lemma dens_splitWords {alphabet p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Finset (Fin n → Fin alphabet)) : (splitWords e A).dens = A.dens := by
  rw [splitWords, Finset.dens_map_equiv]

/-- The canonical cut equivalence associated with a decomposition of the ambient dimension. -/
def cutEquiv {p q n : ℕ} (h : p + q = n) : Fin p ⊕ Fin q ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

/-- The subspace of a coordinate block whose parameter directions are all of its coordinates. -/
def blockSubspace (α : Type*) (m : ℕ) : Combinatorics.Subspace (Fin m) α (Fin m) where
  idxFun i := Sum.inr i
  proper e := ⟨e, rfl⟩

@[simp]
lemma blockSubspace_apply {α : Type*} {m : ℕ} (x : Fin m → α) : blockSubspace α m x = x := by
  funext i
  exact (blockSubspace α m).apply_inr rfl

/-- Prepend a fixed block of letters to the coordinates of a subspace. -/
def prependFixed {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) : Combinatorics.Subspace η α (Fin (m + p)) where
  idxFun i :=
    match finSumFinEquiv.symm i with
    | Sum.inl j => Sum.inl (u j)
    | Sum.inr j => V.idxFun j
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨finSumFinEquiv (Sum.inr i), by simp only [Equiv.symm_apply_apply, hi]⟩

@[simp]
lemma prependFixed_apply {α η : Type*} {m p : ℕ} (u : Fin m → α)
    (V : Combinatorics.Subspace η α (Fin p)) (x : η → α) :
    prependFixed u V x = Sum.elim u (V x) ∘ finSumFinEquiv.symm := by
  funext i
  simp only [Function.comp_apply, Combinatorics.Subspace.coe_apply, prependFixed]
  cases hi : finSumFinEquiv.symm i <;> simp [Combinatorics.Subspace.coe_apply]

/-- Regroup a cut of the coordinates following a fixed block. -/
def prependCoords {m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin m ⊕ Fin r :=
  ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin q))).trans
      (Equiv.sumAssoc (Fin m) (Fin p) (Fin q))).trans ((Equiv.refl (Fin m)).sumCongr e)

/-- Prepend a fixed coordinate block to a cut of the remaining coordinates. -/
def prependCut {m p q r n : ℕ} (h : m + r = n) (e : Fin p ⊕ Fin q ≃ Fin r) :
    Fin (m + p) ⊕ Fin q ≃ Fin n :=
  (prependCoords e).trans (cutEquiv h)

/-- Regrouping the coordinates identifies a prepended word with the concatenation of the fixed
block and the cut word. -/
lemma concat_prependFixed {alphabet η m p q r : ℕ} (e : Fin p ⊕ Fin q ≃ Fin r)
    (u : Fin m → Fin alphabet) (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (prependFixed u V x) y ∘ (prependCoords e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) := by
  funext s
  cases s with
  | inl a => simp [prependCoords]
  | inr b =>
      cases hb : e.symm b <;> simp [prependCoords, hb]

/-- The same identification stated for the cut of the ambient coordinates. -/
lemma concat_prependFixed_cut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p))
    (x : Fin η → Fin alphabet) (y : Fin q → Fin alphabet) :
    Sum.elim (prependFixed u V x) y ∘ (prependCut h e).symm =
      Sum.elim u (Sum.elim (V x) y ∘ e.symm) ∘
        (cutEquiv h).symm := by
  rw [← concat_prependFixed e u V x y]
  rfl

/-- The suffix fibers of a prepended cut are the suffix fibers of the family already restricted
to the fixed prefix block. -/
lemma fiber_splitWords_prependCut {alphabet η m p q r n : ℕ} (h : m + r = n)
    (e : Fin p ⊕ Fin q ≃ Fin r) (A : Finset (Fin n → Fin alphabet)) (u : Fin m → Fin alphabet)
    (V : Combinatorics.Subspace (Fin η) (Fin alphabet) (Fin p)) (x : Fin η → Fin alphabet) :
    fiber (splitWords (prependCut h e) A) (prependFixed u V x) =
      fiber (splitWords e (fiber (splitWords (cutEquiv h) A) u)) (V x) := by
  ext y
  simp only [mem_fiber, mem_splitWords]
  rw [concat_prependFixed_cut]

/-- A prefix fiber sparser than the ambient density by `ε` forces another prefix fiber denser
than the ambient density by a fixed amount. -/
lemma exists_denser_fiber {alphabet m q : ℕ} (halphabet : 0 < alphabet) {ε : ℝ} (hε : 0 < ε)
    (A : Finset (Fin m ⊕ Fin q → Fin alphabet)) (u₀ : Fin m → Fin alphabet)
    (hu₀ : ((fiber A u₀).dens : ℝ) < (A.dens : ℝ) - ε) :
    ∃ u, (A.dens : ℝ) + ε / (alphabet : ℝ) ^ m ≤ ((fiber A u).dens : ℝ) := by
  classical
  by_contra! hcon
  have halphabetR : (0 : ℝ) < (alphabet : ℝ) := by exact_mod_cast halphabet
  have hpow : (0 : ℝ) < (alphabet : ℝ) ^ m := pow_pos halphabetR m
  have hcard : (Fintype.card (Fin m → Fin alphabet) : ℝ) = (alphabet : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have hsum : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) =
      (alphabet : ℝ) ^ m * (A.dens : ℝ) := by
    rw [← average_density_fiber A, ← hcard, ← Finset.card_univ, Finset.card_mul_expect]
  have hle : ∑ u : Fin m → Fin alphabet, ((fiber A u).dens : ℝ) ≤
      ∑ u : Fin m → Fin alphabet, (((A.dens : ℝ) + ε / (alphabet : ℝ) ^ m) +
        if u = u₀ then -(ε + ε / (alphabet : ℝ) ^ m) else 0) := by
    apply Finset.sum_le_sum
    intro u _
    by_cases hu : u = u₀
    · rw [hu, if_pos rfl]
      linarith
    · rw [if_neg hu, add_zero]
      linarith [hcon u]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq' Finset.univ u₀,
    if_pos (Finset.mem_univ u₀), Finset.card_univ, nsmul_eq_mul, hcard, hsum, mul_add,
    mul_div_cancel₀ ε hpow.ne'] at hle
  linarith [div_pos hε hpow]

/-- Every ambient dimension admits a cut into a prefix carrying a subspace and a nonempty suffix
above which all fibers are almost as dense as the whole family. -/
def VariableCutFibersSufficient (alphabet dimension : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n → Fin alphabet),
    ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
      ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
        ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ)

/-- The block density-increment argument: one coordinate block either uniformizes all suffix
fibers or increases the working density by a fixed amount, and the density upper bound bounds the
number of increments. -/
private lemma exists_variableCut_of_fuel (alphabet dimension : ℕ) (halphabet : 0 < alphabet)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t n : ℕ, dimension * (t + 1) < n → ∀ A : Finset (Fin n → Fin alphabet),
      1 ≤ (A.dens : ℝ) + t * (ε / (alphabet : ℝ) ^ dimension) →
      ∃ p q : ℕ, ∃ e : Fin p ⊕ Fin q ≃ Fin n, 0 < q ∧
        ∃ V : Combinatorics.Subspace (Fin dimension) (Fin alphabet) (Fin p),
          ∀ x, (A.dens : ℝ) - ε ≤ ((fiber (splitWords e A) (V x)).dens : ℝ) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      intro n hn A hfuel
      have hblock : dimension ≤ dimension * (t + 1) :=
        Nat.le_mul_of_pos_right dimension (Nat.succ_pos t)
      have hd : dimension + (n - dimension) = n := by omega
      have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension :=
        div_pos hε (pow_pos (by exact_mod_cast halphabet) dimension)
      by_cases hsucc :
          ∀ u, (A.dens : ℝ) - ε ≤ ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ)
      · exact ⟨dimension, n - dimension, cutEquiv hd, by omega,
          blockSubspace (Fin alphabet) dimension, by simpa only [blockSubspace_apply] using hsucc⟩
      push Not at hsucc
      obtain ⟨u₀, hu₀⟩ := hsucc
      obtain ⟨u, hu⟩ := exists_denser_fiber halphabet hε (splitWords (cutEquiv hd) A) u₀
        (by rwa [dens_splitWords])
      rw [dens_splitWords] at hu
      have hu₁ : ((fiber (splitWords (cutEquiv hd) A) u).dens : ℝ) ≤ 1 := by
        exact_mod_cast Finset.dens_le_one (s := fiber (splitWords (cutEquiv hd) A) u)
      have htR : (1 : ℝ) ≤ (t : ℝ) := by
        nlinarith [mul_pos hεpos hεpos]
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by
        have : 1 ≤ t := by exact_mod_cast htR
        omega⟩
      have hstep : dimension * (s + 1 + 1) = dimension * (s + 1) + dimension := by ring
      obtain ⟨p, q, e, hq, V, hV⟩ := ih s (by omega) (n - dimension) (by omega)
        (fiber (splitWords (cutEquiv hd) A) u)
        (by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hfuel; linarith)
      refine ⟨dimension + p, q, prependCut hd e, hq, prependFixed u V, ?_⟩
      intro x
      rw [fiber_splitWords_prependCut]
      linarith [hV x]

/-- Every sufficiently large ambient dimension is sufficient for variable-cut uniform fibers. -/
lemma exists_eventually_variableCutFibersSufficient (alphabet dimension : ℕ)
    (hdimension : 1 ≤ dimension) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, VariableCutFibersSufficient alphabet dimension ε n := by
  classical
  by_cases halphabet : alphabet = 0
  · subst alphabet
    refine ⟨dimension + 1, ?_⟩
    intro n hn A
    refine ⟨dimension, n - dimension, cutEquiv (by omega), by omega,
      emptyAlphabetSubspace hdimension le_rfl, ?_⟩
    intro x
    exact Fin.elim0 (x ⟨0, hdimension⟩)
  have halphabet₀ : 0 < alphabet := Nat.pos_of_ne_zero halphabet
  have hεpos : 0 < ε / (alphabet : ℝ) ^ dimension :=
    div_pos hε (pow_pos (by exact_mod_cast halphabet₀) dimension)
  obtain ⟨t, ht⟩ := exists_nat_gt (1 / (ε / (alphabet : ℝ) ^ dimension))
  refine ⟨dimension * (t + 1) + 1, ?_⟩
  intro n hn A
  apply exists_variableCut_of_fuel alphabet dimension halphabet₀ hε t n (by omega) A
  rw [div_lt_iff₀ hεpos] at ht
  linarith [NNRat.cast_nonneg (α := ℝ) A.dens]

/-- A sufficient ambient dimension for the variable-cut uniform-fibers lemma. -/
noncomputable def variableCutFibersBound (alphabet dimension : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ dimension ∧ 0 < ε then
    Nat.find (exists_eventually_variableCutFibersSufficient alphabet dimension h.1 h.2)
  else 0

/-- The selected variable-cut bound is sufficient in every larger ambient dimension. -/
lemma variableCutFibersBound_spec (alphabet dimension n : ℕ) (hdimension : 1 ≤ dimension)
    {ε : ℝ} (hε : 0 < ε) (hn : variableCutFibersBound alphabet dimension ε ≤ n) :
    VariableCutFibersSufficient alphabet dimension ε n := by
  classical
  rw [variableCutFibersBound, dif_pos ⟨hdimension, hε⟩] at hn
  exact Nat.find_spec
    (exists_eventually_variableCutFibersSufficient alphabet dimension hdimension hε) n hn

/-- Averaging restricted-parameter slice densities over suffixes equals averaging their ambient
fiber densities over restricted parameter words. -/
lemma average_restrictedParameterSlice {k M : ℕ}
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) :
    Finset.expect Finset.univ (fun y : κ → Fin (k + 1) ↦
      ((Finset.univ.filter fun x : Fin M → Fin k ↦
        Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) =
      Finset.expect Finset.univ (fun x : Fin M → Fin k ↦
        ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) := by
  simp_rw [← Finset.expect_indicator_one]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro y _
  by_cases h : Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A <;> simp [h]

/-- Averaging a pointwise-dense family of suffix fibers produces one suffix above which the
restricted parameter family is dense. -/
lemma exists_dense_suffix_of_restricted_fibers {k M : ℕ} (hk : 0 < k) (δ : ℝ)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hW : ∀ x : Fin M → Fin k,
      δ / 2 ≤ ((fiber A (W (Fin.castSucc ∘ x))).dens : ℝ)) :
    ∃ y : κ → Fin (k + 1),
      δ / 2 ≤
        ((Finset.univ.filter fun x : Fin M → Fin k ↦
          Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have havg : δ / 2 ≤
      Finset.expect Finset.univ (fun y : κ → Fin (k + 1) ↦
        ((Finset.univ.filter fun x : Fin M → Fin k ↦
          Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)) := by
    rw [average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty fun x _ ↦ hW x
  by_contra! h
  apply (not_lt_of_ge havg)
  apply Finset.expect_lt
  · intro y _
    exact (h y).le
  · exact ⟨fun _ ↦ 0, Finset.mem_univ _, h (fun _ ↦ 0)⟩

/-- Extend a restricted parameter subspace to the full alphabet, attach a fixed suffix, and
transport the resulting subspace along an equivalence of ambient coordinates. -/
lemma extend_restricted_subspace {k m M : ℕ} {ι κ ζ : Type*}
    [DecidableEq (ζ → Fin (k + 1))] (e : ι ⊕ κ ≃ ζ)
    (A : Finset (ζ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι) (y : κ → Fin (k + 1))
    (S : Combinatorics.Subspace (Fin m) (Fin k) (Fin M))
    (hS : ∀ x, (Sum.elim (W (Fin.castSucc ∘ S x)) y) ∘ e.symm ∈ A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ,
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  let lift_S : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M) :=
    { idxFun := fun i ↦ (S.idxFun i).map (Fin.castSuccEmb : Fin k → Fin (k + 1)) id
      proper := fun e ↦ by
        obtain ⟨i, hi⟩ := S.proper e
        refine ⟨i, ?_⟩
        simp [hi] }
  have h_lift_eval (x : Fin m → Fin k) : lift_S (Fin.castSuccEmb ∘ x) = Fin.castSucc ∘ S x := by
    ext i
    cases hi : S.idxFun i <;> simp [lift_S, Combinatorics.Subspace.coe_apply, hi]
  let concat_suffix : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ζ :=
    { idxFun := fun c ↦
        match e.symm c with
        | Sum.inl i => W.idxFun i
        | Sum.inr j => Sum.inl (y j)
      proper := fun e' ↦ by
        obtain ⟨i, hi⟩ := W.proper e'
        refine ⟨e (Sum.inl i), ?_⟩
        simp [hi] }
  have h_concat_suffix_eval (z : Fin M → Fin (k + 1)) :
      concat_suffix z = (Sum.elim (W z) y) ∘ e.symm := by
    ext c
    simp only [Subspace.coe_apply, Function.comp_apply, concat_suffix]
    cases e.symm c <;> simp [Combinatorics.Subspace.coe_apply]
  let V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ζ :=
    compose concat_suffix lift_S
  refine ⟨V, ?_⟩
  intro w hw
  rw [restrictAlphabet, Finset.mem_image] at hw
  rcases hw with ⟨x, _, rfl⟩
  rw [compose_apply, h_lift_eval x, h_concat_suffix_eval (Fin.castSucc ∘ S x)]
  exact hS x

/-- For the empty restricted alphabet, the restricted range is empty as soon as the parameter
dimension is positive. -/
lemma exists_empty_restrictAlphabet_subset {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (A : Finset (Fin n → Fin 1)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  let V : Combinatorics.Subspace (Fin m) (Fin 1) (Fin n) :=
    { idxFun := fun i ↦ if hi : i.val < m then Sum.inr ⟨i.val, hi⟩ else Sum.inl 0
      proper := fun e ↦ by
        refine ⟨Fin.castLE hmn e, ?_⟩
        simp only [Fin.castLE, e.isLt, ↓reduceDIte] }
  refine ⟨V, ?_⟩
  intro w hw
  simp only [restrictAlphabet, Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨x, _⟩ := hw
  exact Fin.elim0 (x ⟨0, Nat.zero_lt_of_lt hm⟩)

/-- The restricted-alphabet conclusion holds in every sufficiently large dimension. -/
lemma exists_eventually_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → ∀ A : Finset (Fin n → Fin (k + 1)),
      δ * (k + 1 : ℝ) ^ n ≤ #A →
        ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
          restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  classical
  by_cases hk₀ : k = 0
  · subst k
    refine ⟨m, ?_⟩
    intro n hmn A _
    exact exists_empty_restrictAlphabet_subset hm hmn A
  have hk : 0 < k := Nat.pos_of_ne_zero hk₀
  let M := max 1 (densityBound k m (δ / 2))
  refine ⟨variableCutFibersBound (k + 1) M (δ / 2), ?_⟩
  intro n hn A hA
  have hM : 1 ≤ M := le_max_left _ _
  have hA' : δ ≤ (A.dens : ℝ) := by
    apply density_le_of_card_le (Nat.zero_lt_succ k) δ A
    convert hA using 1
    norm_num
  obtain ⟨p, q, e, _hq, W, hW⟩ :=
    variableCutFibersBound_spec (k + 1) M n hM (by linarith) hn A
  obtain ⟨y, hy⟩ :=
    exists_dense_suffix_of_restricted_fibers hk δ (splitWords e A) W fun x ↦ by
      linarith [hW (Fin.castSucc ∘ x)]
  let B := Finset.univ.filter fun x : Fin M → Fin k ↦
    Sum.elim (W (Fin.castSucc ∘ x)) y ∈ splitWords e A
  obtain ⟨S, hS⟩ :=
    exists_of_density hDHJ m hm (δ / 2) (by linarith) M (le_max_right _ _) B
      (card_le_of_density_le hk (δ / 2) B (by simpa only [B] using hy))
  apply extend_restricted_subspace e A W y S
  intro x
  rw [← mem_splitWords]
  simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hS x

/-- A bound for the restricted-alphabet subspace lemma. -/
noncomputable def restrictAlphabetBound (k m : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 1 ≤ m ∧ 0 < δ ∧ HasDensityHJ k then
    Nat.find (exists_eventually_restrictAlphabet_subset h.2.2 m h.1 δ h.2.1)
  else 0

lemma restrictAlphabetBound_spec {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A := by
  classical
  rw [restrictAlphabetBound, dif_pos ⟨hm, hδ, hDHJ⟩] at hn
  exact Nat.find_spec (exists_eventually_restrictAlphabet_subset hDHJ m hm δ hδ) n hn A hA

/-- A dense family over `Fin (k+1)` contains the `Fin k` restriction of a subspace. -/
lemma exists_restrictAlphabet_subset {k : ℕ} (hDHJ : HasDensityHJ k)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : restrictAlphabetBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1)))
    (hA : δ * (k + 1 : ℝ) ^ n ≤ #A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      restrictAlphabet V Fin.castSuccEmb ⊆ A :=
  restrictAlphabetBound_spec hDHJ m hm δ hδ n hn A hA

end Subspace
end DensityHalesJewett

end

section

/-! From DensityHalesJewett.DensityIncrement.Parameters by Gabriel Dahia. -/

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

namespace Parameters

/-- A positive dimension selected from the density Hales--Jewett assertion when available. -/
noncomputable def m₀ (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 0 < δ ∧ HasDensityHJ k then
    Nat.succ <| Nat.find <| h.2 (δ / 4) (by linarith)
  else 1

lemma m₀_pos (k : ℕ) (δ : ℝ) : 0 < m₀ k δ := by
  classical
  unfold m₀
  split <;> simp

/-- The selected dimension is antitone in the density threshold. -/
lemma m₀_antitone {k : ℕ} (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : m₀ k ρ ≤ m₀ k δ := by
  classical
  rw [m₀, dif_pos ⟨hδ.trans_le hδρ, hDHJ⟩, m₀, dif_pos ⟨hδ, hDHJ⟩]
  apply Nat.succ_le_succ
  apply Nat.find_min'
  intro n hn A hA
  exact Nat.find_spec (hDHJ (δ / 4) (by linarith)) n hn A (le_trans (by gcongr) hA)

/-- The denominator in the parameter definition grows with the selected dimension. -/
lemma power_difference_mono (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m ≤
      ((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    apply ih.trans
    rw [Nat.cast_add, Nat.cast_one]
    suffices 0 ≤ (k : ℝ) * (((k + 1 : ℕ) : ℝ) ^ n - (k : ℝ) ^ n) by
      rw [Nat.cast_add, Nat.cast_one] at this
      nlinarith [pow_nonneg (by positivity : 0 ≤ (k : ℝ)) n]
    apply mul_nonneg
    · positivity
    · apply sub_nonneg.mpr
      apply pow_le_pow_left₀
      · positivity
      · exact_mod_cast Nat.le_succ k

/-- The denominator defining `θ` is positive for every admissible alphabet and density. -/
lemma θ_denominator_pos {k : ℕ} (hk : 2 ≤ k) (δ : ℝ) :
    0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
  apply sub_pos.mpr
  apply pow_lt_pow_left₀
  · exact_mod_cast Nat.lt_succ_self k
  · positivity
  · exact Nat.ne_of_gt <| m₀_pos k δ

/-- The correlated-fibers threshold attached to an alphabet size and density. -/
noncomputable def θ (k : ℕ) (δ : ℝ) : ℝ :=
  (δ / 4) /
    (((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ)

/-- The threshold is monotone in the density parameter. -/
lemma θ_mono_of_dhj {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  unfold θ
  refine div_le_div₀ ?_ (by linarith) (θ_denominator_pos hk ρ) ?_
  · exact div_nonneg (hδ.trans_le hδρ).le (by norm_num)
  · exact power_difference_mono k <| m₀_antitone hDHJ hδ hδρ

/-- The threshold is monotone even when the density Hales--Jewett assertion is unavailable. -/
lemma θ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : θ k δ ≤ θ k ρ := by
  classical
  by_cases hDHJ : HasDensityHJ k
  · exact θ_mono_of_dhj hk hDHJ hδ hδρ
  · unfold θ
    rw [m₀, dif_neg (fun h ↦ hDHJ h.2), m₀, dif_neg (fun h ↦ hDHJ h.2)]
    apply div_le_div_of_nonneg_right
    · linarith
    · rw [pow_one, pow_one, Nat.cast_add, Nat.cast_one]
      linarith

lemma θ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < θ k δ := by
  unfold θ
  exact div_pos (by positivity) (θ_denominator_pos hk δ)

/-- The error tolerance attached to an alphabet size and density. -/
noncomputable def η (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))

/-- The error tolerance is monotone in the density parameter. -/
lemma η_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : η k δ ≤ η k ρ := by
  unfold η
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hδρ (θ_mono hk hδ hδρ) (θ_pos hk hδ).le
        (hδ.trans_le hδρ).le
    · norm_num
  · exact div_le_div_of_nonneg_right (θ_mono hk hδ hδρ) (by norm_num)
  · exact div_le_div_of_nonneg_right hδρ (by norm_num)

lemma η_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < η k δ := by
  unfold η
  apply lt_min
  · positivity [θ_pos hk hδ]
  · apply lt_min
    · positivity [θ_pos hk hδ]
    · positivity

/-- The density increment attached to an alphabet size and density. -/
noncomputable def γ (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ * η k δ ^ 2 / k) (min (η k δ ^ 2 / 2) (3 * η k δ))

/-- The increment is monotone in the density parameter. -/
lemma γ_mono {k : ℕ} (hk : 2 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) : γ k δ ≤ γ k ρ := by
  unfold γ
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · apply mul_le_mul hδρ
      · exact (sq_le_sq₀ (η_pos hk hδ).le
          (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
      · positivity
      · exact (hδ.trans_le hδρ).le
    · positivity
  · apply div_le_div_of_nonneg_right
    · exact (sq_le_sq₀ (η_pos hk hδ).le
        (η_pos hk (hδ.trans_le hδρ)).le).mpr (η_mono hk hδ hδρ)
    · norm_num
  · exact mul_le_mul_of_nonneg_left (η_mono hk hδ hδρ) (by norm_num)

lemma γ_pos {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < γ k δ := by
  unfold γ
  positivity [η_pos hk hδ]

lemma η_lt_θ_div_two {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    η k δ < θ k δ / 2 := by
  unfold η
  apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
  linarith [θ_pos hk hδ]

lemma η_le_δ_div_six (k : ℕ) (δ : ℝ) : η k δ ≤ δ / 6 := by
  unfold η
  exact (min_le_right _ _).trans (min_le_right _ _)

lemma γ_le_η_sq_div_two (k : ℕ) (δ : ℝ) : γ k δ ≤ η k δ ^ 2 / 2 := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_left _ _)

lemma γ_le_three_mul_η (k : ℕ) (δ : ℝ) : γ k δ ≤ 3 * η k δ := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The increment parameters can be chosen uniformly above a fixed positive density floor. -/
lemma γ_mono_lowerBound {k : ℕ} (hk : 2 ≤ k) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    0 < γ k δ₀ ∧ ∀ ρ, δ₀ ≤ ρ → γ k δ₀ ≤ γ k ρ := by
  constructor
  · exact γ_pos hk hδ₀
  · intro ρ hδρ
    exact γ_mono hk hδ₀ hδρ

/-- The correlated-fiber threshold is at most one in the admissible parameter range. -/
lemma θ_le_one {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ₁ : δ ≤ 1) :
    θ k δ ≤ 1 := by
  unfold θ
  have hden_pos : 0 < ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ :=
    θ_denominator_pos hk δ
  have h_one_le_diff : 1 ≤ ((k + 1 : ℕ) : ℝ) ^ m₀ k δ - (k : ℝ) ^ m₀ k δ := by
    have h1 : ((k + 1 : ℕ) : ℝ) ^ 1 - (k : ℝ) ^ 1 = (1 : ℝ) := by norm_num
    simpa [h1] using power_difference_mono k (Nat.succ_le_of_lt (m₀_pos k δ))
  apply (div_le_one hden_pos).mpr
  linarith [hδ₁, h_one_le_diff]

/-- The numerical parameters turn the absolute density left outside a large intersection into
the required relative density gain. -/
lemma large_intersection_complement_gain {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    (δ + 6 * η k δ) * (1 - θ k δ / 4) ≤ δ - 3 * η k δ := by
  have hη : η k δ ≤ δ * θ k δ / 48 :=
    min_le_left (δ * θ k δ / 48) (min (θ k δ / 4) (δ / 6))
  nlinarith [hη, θ_pos hk hδ₀, η_pos hk hδ₀,
    mul_nonneg hδ₀.le (θ_pos hk hδ₀).le,
    mul_nonneg (η_pos hk hδ₀).le (θ_pos hk hδ₀).le]

end Parameters

end DensityHalesJewett

end

section

/-! From DensityHalesJewett.Insensitive by Gabriel Dahia. -/

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- Two words are equivalent after freely interchanging the letters `i` and `j`. -/
def InsensitiveEquiv {α ι : Type*} (i j : α) (x y : ι → α) : Prop :=
  ∀ a, a ≠ i → a ≠ j → ∀ c, (x c = a ↔ y c = a)

/-- Membership in an `(i,j)`-insensitive family is constant on insensitive-equivalence classes. -/
def IsInsensitive {α ι : Type*} (i j : α) (D : Finset (ι → α)) : Prop :=
  ∀ ⦃x y⦄, InsensitiveEquiv i j x y → (x ∈ D ↔ y ∈ D)

/-- Transport a word family along an equivalence of coordinate types. -/
def transportWords {α ι ι' : Type*}
    (e : ι ≃ ι') (D : Finset (ι → α)) : Finset (ι' → α) :=
  D.map ((e.arrowCongr (Equiv.refl α)).toEmbedding)

@[simp]
lemma mem_transportWords {α ι ι' : Type*}
    {e : ι ≃ ι'} {D : Finset (ι → α)} {w : ι' → α} :
    w ∈ transportWords e D ↔ w ∘ e ∈ D := by
  rw [transportWords, Finset.mem_map_equiv]
  rfl

@[simp]
lemma dens_transportWords {α ι ι' : Type*} [Fintype (ι → α)] [Fintype (ι' → α)]
    (e : ι ≃ ι') (D : Finset (ι → α)) : (transportWords e D).dens = D.dens := by
  rw [transportWords, Finset.dens_map_equiv]

/-- Fix the coordinates outside a designated block, keeping a subspace on the block. -/
def transportSubspace {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) : Combinatorics.Subspace η α ι where
  idxFun c := Sum.elim (fun a ↦ Sum.inl (z a)) V.idxFun (e c)
  proper x := by
    obtain ⟨c, hc⟩ := V.proper x
    exact ⟨e.symm (Sum.inr c), by simp only [Equiv.apply_symm_apply, Sum.elim_inr, hc]⟩

@[simp]
lemma transportSubspace_apply {α η ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (z : ω → α)
    (V : Combinatorics.Subspace η α ν) (x : η → α) :
    transportSubspace e z V x = Sum.elim z (V x) ∘ e := by
  funext c
  simp only [Combinatorics.Subspace.coe_apply, transportSubspace, Function.comp_apply]
  cases e c <;> simp only [Sum.elim_inl, Sum.elim_inr, id_eq, Combinatorics.Subspace.coe_apply]

namespace IsInsensitive

/-- Reindexing coordinates preserves insensitivity. -/
lemma reindex {α ι ι' : Type*}
    {i j : α} {D : Finset (ι → α)} (e : ι ≃ ι') (hD : IsInsensitive i j D) :
    IsInsensitive i j (DensityHalesJewett.transportWords e D) := by
  intro x y hxy
  simp only [mem_transportWords]
  apply hD
  intro a hai haj c
  exact hxy a hai haj (e c)

/-- Fixing a prefix of coordinates preserves insensitivity of the remaining section. -/
lemma fiberSection {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : IsInsensitive i j D) (v : ι → α) :
    IsInsensitive i j (DensityHalesJewett.fiber D v) := by
  intro x y hxy
  simp only [mem_fiber]
  apply hD
  intro a hai haj c
  cases c with
  | inl c => simp only [Sum.elim_inl]
  | inr c => exact hxy a hai haj c

/-- Complements preserve insensitivity. -/
lemma compl {α ι : Type*} [Fintype (ι → α)] [DecidableEq (ι → α)]
    {i j : α} {D : Finset (ι → α)} (hD : IsInsensitive i j D) :
    IsInsensitive i j Dᶜ := by
  intro x y hxy
  simp only [mem_compl, hD hxy]

/-- The part of `D` left uncovered by a set of subspaces. -/
noncomputable def uncovered {η α ι : Type*} [Fintype (η → α)]
    [DecidableEq (ι → α)] (D : Finset (ι → α))
    (𝒱 : Set (Combinatorics.Subspace η α ι)) : Finset (ι → α) := by
  classical
  exact D.filter fun w ↦ ∀ V ∈ 𝒱, w ∉ Subspace.range V

/-- The intersection of a finite indexed family of finite sets. -/
noncomputable def intersection {r : ℕ} {X : Type*} [Fintype X]
    (D : Fin r → Finset X) : Finset X := by
  classical
  exact Finset.univ.inf D

@[simp]
lemma mem_intersection {r : ℕ} {X : Type*} [Fintype X]
    {D : Fin r → Finset X} {x : X} :
    x ∈ intersection D ↔ ∀ i, x ∈ D i := by
  simp [intersection, ← Finset.singleton_subset_iff, Finset.le_inf_iff]

/-- An ambient dimension is sufficient for tiling every dense one-pair insensitive family. -/
def TilingSufficient (k m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ i : Fin k, ∀ D : Finset (Fin n → Fin (k + 1)),
    IsInsensitive i.castSucc (Fin.last k) D →
    2 * β ≤ (D.dens : ℝ) →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V D) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered D 𝒱).dens : ℝ) < 2 * β

/-- Differences preserve insensitivity. -/
lemma sdiff {α ι : Type*} [DecidableEq (ι → α)]
    {i j : α} {D E : Finset (ι → α)} (hD : IsInsensitive i j D)
    (hE : IsInsensitive i j E) : IsInsensitive i j (D \ E) := by
  intro x y hxy
  simp [hD hxy, hE hxy]

/-- Insensitive-equivalent prefixes have the same section. -/
lemma fiber_congr {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : IsInsensitive i j D) {v w : ι → α}
    (hvw : InsensitiveEquiv i j v w) :
    DensityHalesJewett.fiber D v = DensityHalesJewett.fiber D w := by
  ext y
  simp only [mem_fiber]
  apply hD
  intro a hai haj c
  cases c with
  | inl c => exact hvw a hai haj c
  | inr c => simp only [Sum.elim_inr]

end IsInsensitive

/-- Regrouping the coordinates of a word with a fixed prefix and a split tail. -/
private lemma concat_comp_regroup {α ω ν ν₁ ν₂ : Type*} (s : ν ≃ ν₁ ⊕ ν₂)
    (u : ω → α) (r : ν₁ → α) (x : ν₂ → α) :
    Sum.elim (Sum.elim u r) x ∘
        (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm) =
      Sum.elim u (Sum.elim r x ∘ s) := by
  funext c
  cases c with
  | inl a => simp [Equiv.sumAssoc]
  | inr n => cases hn : s n <;> simp [Equiv.sumAssoc, hn]

/-- The same regrouping stated after a coordinate splitting of the ambient type. -/
private lemma concat_comp_regroup_trans {α ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν)
    (s : ν ≃ ν₁ ⊕ ν₂) (u : ω → α) (r : ν₁ → α) (x : ν₂ → α) :
    Sum.elim (Sum.elim u r) x ∘
        (e.trans (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm)) =
      Sum.elim u (Sum.elim r x ∘ s) ∘ e := by
  rw [← concat_comp_regroup s u r x]
  rfl

/-- Sections over the last block of a split tail are sections of sections. -/
private lemma fiber_transportWords_regroup {α ι ω ν ν₁ ν₂ : Type*}
    [Fintype α] [DecidableEq α] [Fintype ω]
    [Fintype ν] [DecidableEq ν] [Fintype ν₁] [Fintype ν₂] [DecidableEq ν₂]
    (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂) (U : Finset (ι → α)) (u : ω → α) (r : ν₁ → α) :
    DensityHalesJewett.fiber
        (transportWords (e.trans (((Equiv.refl ω).sumCongr s).trans
          (Equiv.sumAssoc ω ν₁ ν₂).symm)) U) (Sum.elim u r) =
      DensityHalesJewett.fiber
        (transportWords s (DensityHalesJewett.fiber (transportWords e U) u)) r := by
  ext x
  simp only [mem_fiber, mem_transportWords, concat_comp_regroup_trans]

/-- A word is the concatenation of its parts along a coordinate splitting. -/
private lemma eq_concat_parts {α ι ω ν : Type*} (e : ι ≃ ω ⊕ ν) (w : ι → α) :
    Sum.elim (fun a ↦ w (e.symm (Sum.inl a)))
        (fun n ↦ w (e.symm (Sum.inr n))) ∘ e = w := by
  simpa [Function.comp_def] using congrArg (· ∘ e) (Sum.elim_comp_inl_inr (w ∘ e.symm))

/-- Sections commute with set difference. -/
private lemma fiber_transportWords_sdiff {α ι ω ν : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [Fintype ω]
    [Fintype ν] [DecidableEq ν]
    (e : ι ≃ ω ⊕ ν) (A B : Finset (ι → α)) (v : ω → α) :
    DensityHalesJewett.fiber (transportWords e (A \ B)) v =
      DensityHalesJewett.fiber (transportWords e A) v \
        DensityHalesJewett.fiber (transportWords e B) v := by
  ext y
  simp only [Finset.mem_sdiff, mem_fiber, mem_transportWords]

/-- Removing a subset from a family subtracts its density. -/
private lemma dens_sdiff_of_subset {X : Type*} [Fintype X] [DecidableEq X] {A B : Finset X}
    (h : B ⊆ A) : (((A \ B).dens : ℝ)) = (A.dens : ℝ) - (B.dens : ℝ) := by
  push_cast [← Finset.dens_sdiff_add_dens_eq_dens h]
  ring

/-- A nonempty family occupies at least one point of the ambient cube. -/
private lemma one_div_card_le_dens {X : Type*} [Fintype X] {A : Finset X} (h : A.Nonempty) :
    1 / (Fintype.card X : ℝ) ≤ (A.dens : ℝ) := by
  rw [Finset.nnratCast_dens]
  gcongr
  exact_mod_cast h.card_pos

/-- An insensitive family that is dense in a large enough block contains a full subspace: the
restricted-alphabet subspace lemma supplies the `Fin k`-restricted range, and insensitivity
upgrades containment to the whole parameter cube. -/
lemma exists_isContained_of_insensitive {k m b : ℕ} (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    (i : Fin k) {β : ℝ} (hβ : 0 < β) (hb : Subspace.restrictAlphabetBound k m β ≤ b)
    (E : Finset (Fin b → Fin (k + 1)))
    (hE : IsInsensitive i.castSucc (Fin.last k) E) (hdens : β ≤ (E.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b), Subspace.IsContained V E := by
  obtain ⟨V, hV⟩ :=
    Subspace.exists_restrictAlphabet_subset hDHJ m hm β hβ b hb E
      (by exact_mod_cast Subspace.card_le_of_density_le (k := k + 1) (Nat.succ_pos k) β E hdens)
  refine ⟨V, ?_⟩
  intro x
  refine (hE ?_).mpr
    (hV (Finset.mem_image.mpr ⟨fun e ↦ if h : x e = Fin.last k then i else (x e).castPred h,
      Finset.mem_univ _, rfl⟩))
  intro a hai hal c
  cases hc : V.idxFun c with
  | inl t => simp only [V.apply_inl hc]
  | inr e =>
      simp only [V.apply_inr hc, Function.comp_apply]
      by_cases hx : x e = Fin.last k
      · rw [dif_pos hx, hx, Fin.castSuccEmb_apply]
        apply iff_of_false
        · intro h
          exact hal h.symm
        · intro h
          exact hai h.symm
      · rw [dif_neg hx, Fin.castSuccEmb_apply, Fin.castSucc_castPred]

/-- The two block orders describe the same ambient word. -/
private lemma concat_comp_swap {α ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂)
    (u : ω → α) (y : ν₁ → α) (x : ν₂ → α) :
    Sum.elim (Sum.elim u y) x ∘
        (e.trans (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm)) =
      Sum.elim (Sum.elim u x) y ∘
        (e.trans (((Equiv.refl ω).sumCongr (s.trans (Equiv.sumComm ν₁ ν₂))).trans
          (Equiv.sumAssoc ω ν₂ ν₁).symm)) := by
  rw [concat_comp_regroup_trans, concat_comp_regroup_trans]
  refine congrArg (· ∘ e) (congrArg (Sum.elim u) ?_)
  funext n
  cases hn : s n <;> simp [hn]

/-- A canonical subspace contained in a family, depending on nothing but the family. -/
noncomputable def pickSubspace {k m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (E : Finset (Fin b → Fin (k + 1))) :
    Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b) := by
  classical
  exact if h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.IsContained V E then Classical.choose h
    else Subspace.repeatInitial (Fin (k + 1)) hm hmb

lemma pickSubspace_isContained {k m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    {E : Finset (Fin b → Fin (k + 1))}
    (h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.IsContained V E) :
    Subspace.IsContained (pickSubspace hm hmb E) E := by
  classical
  rw [pickSubspace, dif_pos h]
  exact Classical.choose_spec h

namespace IsInsensitive

/-- Nothing is covered by an empty family of subspaces. -/
@[simp]
private lemma uncovered_empty {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (D : Finset (ι → α)) :
    uncovered D (∅ : Set (Combinatorics.Subspace η α ι)) = D := by
  simp only [uncovered, Set.mem_empty_iff_false, false_implies, implies_true,
    Finset.filter_true_of_mem]

/-- Fix an initial coordinate block and place a subspace on the remaining coordinates. -/
private def padExtraSubspace {α η : Type*} {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin N)) :
    Combinatorics.Subspace η α (Fin n) where
  idxFun i :=
    match e.symm i with
    | Sum.inl j => Sum.inl (z j)
    | Sum.inr j => V.idxFun j
  proper a := by
    obtain ⟨i, hi⟩ := V.proper a
    refine ⟨e (Sum.inr i), ?_⟩
    simp only [Equiv.symm_apply_apply, hi]

@[simp]
private lemma padExtraSubspace_apply {α η : Type*} {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (z : Fin r → α)
    (V : Combinatorics.Subspace η α (Fin N)) (x : η → α) :
    padExtraSubspace e z V x =
      Sum.elim z (V x) ∘ e.symm := by
  funext i
  cases hi : e.symm i <;>
    simp [padExtraSubspace, Combinatorics.Subspace.coe_apply, hi, Sum.elim, Function.comp_apply]

/-- Fiberwise tiles remain finite, contained, and disjoint after their fixed prefixes are padded
back into the ambient cube. -/
private lemma padded_tiles_facts {α η : Type*} [Fintype α] [Fintype (η → α)]
    [DecidableEq α] {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (D : Finset (Fin n → α))
    (tiles : (Fin r → α) → Set (Combinatorics.Subspace η α (Fin N)))
    (hfinite : ∀ z, (tiles z).Finite)
    (hcontained : ∀ z V, V ∈ tiles z →
      Subspace.IsContained V (fiber (D.map
        (e.arrowCongr (Equiv.refl α)).symm.toEmbedding) z))
    (hpairwise : ∀ z, (tiles z).PairwiseDisjoint fun V ↦
      (Subspace.range V : Set (Fin N → α))) :
    let global : Set (Combinatorics.Subspace η α (Fin n)) :=
      ⋃ z, padExtraSubspace e z '' tiles z
    global.Finite ∧
      (∀ V ∈ global, Subspace.IsContained V D) ∧
      (global.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → α))) := by
  classical
  dsimp only
  refine ⟨Set.finite_iUnion fun z ↦ (hfinite z).image (padExtraSubspace e z), ?_, ?_⟩
  · intro U hU x
    simp only [Set.mem_iUnion, Set.mem_image] at hU
    obtain ⟨z, V, hV, rfl⟩ := hU
    have hx := hcontained z V hV x
    simp only [mem_fiber, Finset.mem_map_equiv, Equiv.symm_symm] at hx
    simpa [padExtraSubspace_apply, Equiv.arrowCongr] using hx
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' hU' hcommon
    simp only [Set.mem_iUnion, Set.mem_image] at hU hU'
    obtain ⟨z, V, hV, rfl⟩ := hU
    obtain ⟨z', V', hV', rfl⟩ := hU'
    obtain ⟨w, hw, hw'⟩ := hcommon
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
    have hzx : Sum.elim z (V x) = Sum.elim z' (V' x') := by
      funext c
      simpa only [padExtraSubspace_apply, Function.comp_apply, Equiv.symm_apply_apply] using
        congrFun (hx.trans hx'.symm) (e c)
    have hzz : z = z' := funext fun j ↦ congrFun hzx (Sum.inl j)
    subst z'
    apply congrArg (padExtraSubspace e z)
    apply Set.pairwiseDisjoint_iff.mp (hpairwise z) hV hV'
    refine ⟨V x, Subspace.mem_range.mpr ⟨x, rfl⟩,
      Subspace.mem_range.mpr ⟨x', ?_⟩⟩
    exact funext fun j ↦ (congrFun hzx (Sum.inr j)).symm

/-- After padding fiberwise tiles, the uncovered part of each fiber is exactly the uncovered part
of the corresponding local family. -/
private lemma fiber_uncovered_padded {α η : Type*} [Fintype α] [Fintype (η → α)]
    [DecidableEq α] {r N n : ℕ}
    (e : Fin r ⊕ Fin N ≃ Fin n) (D : Finset (Fin n → α))
    (tiles : (Fin r → α) → Set (Combinatorics.Subspace η α (Fin N)))
    (z : Fin r → α) :
    let wordEquiv := e.arrowCongr (Equiv.refl α)
    let global : Set (Combinatorics.Subspace η α (Fin n)) :=
      ⋃ z, padExtraSubspace e z '' tiles z
    fiber ((uncovered D global).map wordEquiv.symm.toEmbedding) z =
      uncovered (fiber (D.map wordEquiv.symm.toEmbedding) z) (tiles z) := by
  classical
  dsimp only
  ext y
  simp only [mem_fiber, Finset.mem_map_equiv, uncovered, Finset.mem_filter]
  constructor
  · rintro ⟨hyD, hyfree⟩
    refine ⟨hyD, ?_⟩
    intro V hV hyV
    apply hyfree (padExtraSubspace e z V)
    · exact Set.mem_iUnion_of_mem z <| Set.mem_image_of_mem _ hV
    · obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyV
      exact Subspace.mem_range.mpr ⟨x, by
        simp [padExtraSubspace_apply, Equiv.arrowCongr, hx]⟩
  · rintro ⟨hyD, hyfree⟩
    refine ⟨hyD, ?_⟩
    intro U hU hyU
    simp only [Set.mem_iUnion, Set.mem_image] at hU
    obtain ⟨z', V, hV, rfl⟩ := hU
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hyU
    have hconcat : Sum.elim z y = Sum.elim z' (V x) := by
      apply (e.arrowCongr (Equiv.refl α)).injective
      simpa [padExtraSubspace_apply, Equiv.arrowCongr] using hx.symm
    have hzz : z = z' := funext fun j ↦ congrFun hconcat (Sum.inl j)
    subst z'
    apply hyfree V hV
    refine Subspace.mem_range.mpr ⟨x, funext ?_⟩
    intro j 
    exact (congrFun hconcat (Sum.inr j)).symm

/-- Merge the tiles removed at one packing stage with a recursive tiling of the remainder. -/
private lemma combine_tiling_stage {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k m S : ℕ} {β c : ℝ}
    (U R : Finset (ι → Fin (k + 1)))
    (newTiles oldTiles : Set
      (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι))
    (hnewfinite : newTiles.Finite) (holdfinite : oldTiles.Finite)
    (hRU : R ⊆ U)
    (hnewcontained : ∀ V ∈ newTiles, Subspace.IsContained V R)
    (hRcovered : ∀ w ∈ R, ∃ V ∈ newTiles, w ∈ Subspace.range V)
    (hnewdisjoint : newTiles.PairwiseDisjoint fun V ↦
      (Subspace.range V : Set (ι → Fin (k + 1))))
    (holdcontained : ∀ V ∈ oldTiles, Subspace.IsContained V (U \ R))
    (holddisjoint : oldTiles.PairwiseDisjoint fun V ↦
      (Subspace.range V : Set (ι → Fin (k + 1))))
    (hRdens : c ≤ (R.dens : ℝ))
    (holdconclusion : ((uncovered (U \ R) oldTiles).dens : ℝ) < 2 * β ∨
      ((uncovered (U \ R) oldTiles).dens : ℝ) + S * c ≤ ((U \ R).dens : ℝ)) :
    let allTiles := newTiles ∪ oldTiles
    allTiles.Finite ∧
      (∀ V ∈ allTiles, Subspace.IsContained V U) ∧
      (allTiles.PairwiseDisjoint fun V ↦
        (Subspace.range V : Set (ι → Fin (k + 1)))) ∧
      (((uncovered U allTiles).dens : ℝ) < 2 * β ∨
        ((uncovered U allTiles).dens : ℝ) + (S + 1) * c ≤ (U.dens : ℝ)) := by
  classical
  dsimp only
  refine ⟨hnewfinite.union holdfinite, ?_, ?_, ?_⟩
  · intro V hV
    rcases hV with hV | hV
    · intro x
      exact hRU (hnewcontained V hV x)
    · intro x
      exact (Finset.mem_sdiff.mp (holdcontained V hV x)).1
  · apply Set.PairwiseDisjoint.union hnewdisjoint holddisjoint
    intro V hV V' hV' _
    rw [Set.disjoint_left]
    intro w hw hw'
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
    exact (Finset.mem_sdiff.mp (hx' ▸ holdcontained V' hV' x')).2
      (hx ▸ hnewcontained V hV x)
  · have huncovered : uncovered U (newTiles ∪ oldTiles) =
        uncovered (U \ R) oldTiles := by
      ext w
      simp only [uncovered, Finset.mem_filter, Finset.mem_sdiff, Set.mem_union]
      grind [Subspace.mem_range, Subspace.IsContained]
    rw [huncovered]
    rcases holdconclusion with hlt | hle
    · left
      exact hlt
    · right
      rw [dens_sdiff_of_subset hRU] at hle
      nlinarith

/-- The canonical tile in each good fiber lies in the filtered region, and these tiles cover that
region. -/
private lemma canonical_tiles_cover {k m b : ℕ} {ι ζ : Type*}
    [Fintype ι] [Fintype ζ]
    [DecidableEq (ζ → Fin (k + 1))]
    (hm : 1 ≤ m) (hmb : m ≤ b) (e : ι ≃ ζ ⊕ Fin b)
    (U : Finset (ι → Fin (k + 1)))
    (B : (ζ → Fin (k + 1)) → Finset (Fin b → Fin (k + 1)))
    (hB : B = fun z ↦ fiber (transportWords e U) z)
    (good : Finset (ζ → Fin (k + 1)))
    (tile : (ζ → Fin (k + 1)) →
      Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (htile : tile = fun z ↦ transportSubspace e z (pickSubspace hm hmb (B z)))
    (hpick : ∀ z ∈ good, Subspace.IsContained (pickSubspace hm hmb (B z)) (B z))
    (R : Finset (ι → Fin (k + 1)))
    (hR : R = U.filter fun w ↦
      (fun a ↦ w (e.symm (Sum.inl a))) ∈ good ∧
        (fun j ↦ w (e.symm (Sum.inr j))) ∈
          Subspace.range (pickSubspace hm hmb (B (fun a ↦ w (e.symm (Sum.inl a)))))) :
    (∀ z ∈ good, Subspace.IsContained (tile z) R) ∧
      (∀ w ∈ R, ∃ z ∈ good, w ∈ Subspace.range (tile z)) := by
  classical
  subst B
  constructor
  · intro z hz x
    have hmemU : tile z x ∈ U := by
      simpa only [htile, transportSubspace_apply, mem_fiber, mem_transportWords] using
        hpick z hz x
    have hparts : (fun a ↦ tile z x (e.symm (Sum.inl a))) = z := by
      funext a
      simp only [htile, transportSubspace_apply, Function.comp_apply,
        Equiv.apply_symm_apply, Sum.elim_inl]
    rw [hR, Finset.mem_filter]
    refine ⟨hmemU, hparts.symm ▸ hz, ?_⟩
    rw [hparts]
    refine Subspace.mem_range.mpr ⟨x, ?_⟩
    funext j
    simp only [htile, transportSubspace_apply, Function.comp_apply,
      Equiv.apply_symm_apply, Sum.elim_inr]
  · intro w hw
    rw [hR, Finset.mem_filter] at hw
    obtain ⟨_, hz, hrange⟩ := hw
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hrange
    refine ⟨_, hz, Subspace.mem_range.mpr ⟨x, ?_⟩⟩
    rw [htile, transportSubspace_apply, hx]
    exact eq_concat_parts e w

/-- A positive-density set of nonempty fibers gives a proportional ambient density lower bound. -/
private lemma density_of_nonempty_fibers {k b : ℕ} {ι ζ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ζ]
    [Fintype (ζ → Fin (k + 1))]
    (e : ι ≃ ζ ⊕ Fin b) (R : Finset (ι → Fin (k + 1)))
    (good : Finset (ζ → Fin (k + 1))) {β : ℝ}
    (hgood : β ≤ (good.dens : ℝ))
    (hnonempty : ∀ z ∈ good, (fiber (transportWords e R) z).Nonempty) :
    β / ((k : ℝ) + 1) ^ b ≤ (R.dens : ℝ) := by
  classical
  have hcard : (Fintype.card (Fin b → Fin (k + 1)) : ℝ) = ((k : ℝ) + 1) ^ b := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one]
  have hfiber (z : ζ → Fin (k + 1)) (hz : z ∈ good) :
      1 / ((k : ℝ) + 1) ^ b ≤ ((fiber (transportWords e R) z).dens : ℝ) := by
    rw [← hcard]
    exact one_div_card_le_dens (hnonempty z hz)
  have haverage : (R.dens : ℝ) =
      𝔼 z : (ζ → Fin (k + 1)), ((fiber (transportWords e R) z).dens : ℝ) := by
    rw [average_density_fiber, dens_transportWords]
  rw [haverage, div_eq_mul_inv, mul_comm β (((k : ℝ) + 1) ^ b)⁻¹, ← one_div]
  apply le_trans (mul_le_mul_of_nonneg_left hgood (by positivity))
  rw [← Finset.expect_indicator_one (s := good), Finset.mul_expect]
  apply Finset.expect_le_expect
  intro z _
  by_cases hz : z ∈ good
  · rw [Set.indicator_of_mem (by simpa using hz)]
    simpa only [Pi.one_apply, mul_one] using hfiber z hz
  · rw [Set.indicator_of_notMem (by simpa using hz), mul_zero]
    positivity

/-- Removing the canonical tiles chosen in one fresh block preserves insensitivity in every
section over the blocks that remain. -/
private lemma canonical_remainder_sections_insensitive {k m S b : ℕ} (i : Fin k)
    {ι ω : Type*} [Fintype ι] [Fintype ω]
    (hm : 1 ≤ m) (hmb : m ≤ b)
    (e₁ : ι ≃ (ω ⊕ Fin (S * b)) ⊕ Fin b)
    (e₂ : ι ≃ (ω ⊕ Fin b) ⊕ Fin (S * b))
    (U : Finset (ι → Fin (k + 1)))
    (B : (ω ⊕ Fin (S * b) → Fin (k + 1)) → Finset (Fin b → Fin (k + 1)))
    (good : Finset (ω ⊕ Fin (S * b) → Fin (k + 1)))
    (R : Finset (ι → Fin (k + 1)))
    (hR : R = U.filter fun w ↦
      (fun a ↦ w (e₁.symm (Sum.inl a))) ∈ good ∧
        (fun j ↦ w (e₁.symm (Sum.inr j))) ∈
          Subspace.range (pickSubspace hm hmb (B (fun a ↦ w (e₁.symm (Sum.inl a))))))
    (hU : ∀ v, IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e₂ U) v))
    (hBcongr : ∀ u y y', InsensitiveEquiv i.castSucc (Fin.last k) y y' →
      B (Sum.elim u y) = B (Sum.elim u y'))
    (hgood : ∀ u y y', B (Sum.elim u y) = B (Sum.elim u y') →
      (Sum.elim u y ∈ good ↔ Sum.elim u y' ∈ good))
    (hswap : ∀ (v : ω ⊕ Fin b → Fin (k + 1)) y,
      Sum.elim v y ∘ e₂ =
        Sum.elim (Sum.elim (fun a ↦ v (Sum.inl a)) y)
          (fun j ↦ v (Sum.inr j)) ∘ e₁) :
    ∀ v, IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e₂ (U \ R)) v) := by
  classical
  intro v
  rw [fiber_transportWords_sdiff]
  let u : ω → Fin (k + 1) := fun a ↦ v (Sum.inl a)
  let x : Fin b → Fin (k + 1) := fun j ↦ v (Sum.inr j)
  have hv : v = Sum.elim u x := (Sum.elim_comp_inl_inr v).symm
  have hword (y : Fin (S * b) → Fin (k + 1)) :
      Sum.elim v y ∘ e₂ = Sum.elim (Sum.elim u y) x ∘ e₁ := by
    simpa only [u, x] using hswap v y
  have hUpart := hU v
  apply sdiff hUpart
  intro y y' hyy'
  have hsection : B (Sum.elim u y) = B (Sum.elim u y') := hBcongr u y y' hyy'
  have hmemU : Sum.elim v y ∘ e₂ ∈ U ↔ Sum.elim v y' ∘ e₂ ∈ U := by
    simpa only [mem_fiber, mem_transportWords] using hUpart (x := y) (y := y') hyy'
  have hout (z : Fin (S * b) → Fin (k + 1)) :
      (fun a ↦ (Sum.elim v z ∘ e₂) (e₁.symm (Sum.inl a))) = Sum.elim u z := by
    rw [hword z]
    funext a
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inl]
  have hblock (z : Fin (S * b) → Fin (k + 1)) :
      (fun j ↦ (Sum.elim v z ∘ e₂) (e₁.symm (Sum.inr j))) = x := by
    rw [hword z]
    funext j
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Sum.elim_inr]
  have hmemR (z : Fin (S * b) → Fin (k + 1)) :
      z ∈ fiber (transportWords e₂ R) v ↔
        Sum.elim v z ∘ e₂ ∈ U ∧ Sum.elim u z ∈ good ∧
          x ∈ Subspace.range (pickSubspace hm hmb (B (Sum.elim u z))) := by
    rw [mem_fiber, mem_transportWords, hR, Finset.mem_filter, hout z, hblock z]
  rw [hmemR y, hmemR y', hsection, hmemU, hgood u y y' hsection]

/-- The block density-increment tiling of paper Lemma 12.

The coordinates are split into an already consumed part `ω` and `T` fresh blocks of size `b`. The
invariant is that all sections of the working family over the fresh blocks stay insensitive; each
stage either has already reached uncovered density below `2 * β` or removes disjoint tiles of total
density at least `β / (k + 1) ^ b`, and choosing the local subspace canonically from the section
keeps the invariant for the later blocks. -/
private lemma exists_tiling_of_insensitive_sections {k : ℕ} (i : Fin k) (hDHJ : HasDensityHJ k)
    {m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hb : Subspace.restrictAlphabetBound k m β ≤ b) :
    ∀ T : ℕ, ∀ ι ω : Type, ∀ [Fintype ι] [DecidableEq ι] [Fintype ω],
      ∀ e : ι ≃ ω ⊕ Fin (T * b), ∀ U : Finset (ι → Fin (k + 1)),
        (∀ v : ω → Fin (k + 1),
          IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e U) v)) →
        ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι),
          𝒱.Finite ∧ (∀ V ∈ 𝒱, Subspace.IsContained V U) ∧
          (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (ι → Fin (k + 1)))) ∧
          (((uncovered U 𝒱).dens : ℝ) < 2 * β ∨
            ((uncovered U 𝒱).dens : ℝ) + T * (β / ((k : ℝ) + 1) ^ b) ≤ (U.dens : ℝ)) := by
  classical
  intro T
  induction T with
  | zero =>
      intro ι ω _ _ _ e U _
      refine ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty, ?_⟩
      right
      simp only [uncovered_empty, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ S ih =>
      intro ι ω _ _ _ e U hins
      by_cases hU : (U.dens : ℝ) < 2 * β
      · exact ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty, Or.inl (by simpa using hU)⟩
      push Not at hU
      have hsplit : S * b + b = (S + 1) * b := by ring
      set s : Fin ((S + 1) * b) ≃ Fin (S * b) ⊕ Fin b :=
        (finSumFinEquiv.trans (finCongr hsplit)).symm with hs
      set e₁ : ι ≃ (ω ⊕ Fin (S * b)) ⊕ Fin b :=
        e.trans (((Equiv.refl ω).sumCongr s).trans
          (Equiv.sumAssoc ω (Fin (S * b)) (Fin b)).symm) with he₁
      set e₂ : ι ≃ (ω ⊕ Fin b) ⊕ Fin (S * b) :=
        e.trans (((Equiv.refl ω).sumCongr (s.trans (Equiv.sumComm (Fin (S * b)) (Fin b)))).trans
          (Equiv.sumAssoc ω (Fin b) (Fin (S * b))).symm) with he₂
      set B : (ω ⊕ Fin (S * b) → Fin (k + 1)) → Finset (Fin b → Fin (k + 1)) :=
        fun z ↦ fiber (transportWords e₁ U) z with hBdef
      have hB (u : ω → Fin (k + 1)) (r : Fin (S * b) → Fin (k + 1)) :
          B (Sum.elim u r) = fiber (transportWords s (fiber (transportWords e U) u)) r :=
        fiber_transportWords_regroup e s U u r
      have hBins (z : ω ⊕ Fin (S * b) → Fin (k + 1)) :
          IsInsensitive i.castSucc (Fin.last k) (B z) := by
        rw [← Sum.elim_comp_inl_inr z, hB]
        exact fiberSection (reindex s (hins _)) _
      have havg : (𝔼 z : (ω ⊕ Fin (S * b) → Fin (k + 1)), ((B z).dens : ℝ)) = (U.dens : ℝ) := by
        simp only [hBdef]
        rw [average_density_fiber, dens_transportWords]
      have hgood :
          β ≤ ((Finset.univ.filter fun z : ω ⊕ Fin (S * b) → Fin (k + 1) ↦
            β ≤ ((B z).dens : ℝ)).dens : ℝ) := by
        refine le_trans ?_ (density_ge_threshold (fun z ↦ ((B z).dens : ℝ)) (2 * β) β
          (fun z ↦ by exact_mod_cast Finset.dens_le_one (s := B z))
          (by linarith) (by rw [havg]; exact hU))
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      set good : Finset (ω ⊕ Fin (S * b) → Fin (k + 1)) :=
        Finset.univ.filter fun z ↦ β ≤ ((B z).dens : ℝ) with hgooddef
      set tile : (ω ⊕ Fin (S * b) → Fin (k + 1)) →
          Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι :=
        fun z ↦ transportSubspace e₁ z (pickSubspace hm hmb (B z)) with htiledef
      have hpick (z : ω ⊕ Fin (S * b) → Fin (k + 1)) (hz : z ∈ good) :
          Subspace.IsContained (pickSubspace hm hmb (B z)) (B z) :=
        pickSubspace_isContained hm hmb
          (exists_isContained_of_insensitive hDHJ hm i hβ₀ hb (B z) (hBins z)
            (by simpa only [hgooddef, Finset.mem_filter, Finset.mem_univ, true_and] using hz))
      set R : Finset (ι → Fin (k + 1)) := U.filter (fun w ↦
        (fun a ↦ w (e₁.symm (Sum.inl a))) ∈ good ∧
          (fun j ↦ w (e₁.symm (Sum.inr j))) ∈
            Subspace.range (pickSubspace hm hmb (B (fun a ↦ w (e₁.symm (Sum.inl a))))))
        with hRdef
      have hRU : R ⊆ U := Finset.filter_subset _ _
      obtain ⟨htileR, hRtile⟩ :=
        canonical_tiles_cover hm hmb e₁ U B hBdef good tile htiledef hpick R hRdef
      have hdensR : β / ((k : ℝ) + 1) ^ b ≤ (R.dens : ℝ) := by
        apply density_of_nonempty_fibers e₁ R good
          (by simpa only [hgooddef] using hgood)
        intro z hz
        refine ⟨pickSubspace hm hmb (B z) (fun _ ↦ 0), ?_⟩
        rw [mem_fiber, mem_transportWords]
        simpa only [htiledef, transportSubspace_apply] using htileR z hz (fun _ ↦ 0)
      have hins' : ∀ v : ω ⊕ Fin b → Fin (k + 1),
          IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e₂ (U \ R)) v) := by
        apply canonical_remainder_sections_insensitive i hm hmb e₁ e₂ U B good R hRdef
        · intro v
          let u : ω → Fin (k + 1) := fun a ↦ v (Sum.inl a)
          let x : Fin b → Fin (k + 1) := fun j ↦ v (Sum.inr j)
          have hv : v = Sum.elim u x := (Sum.elim_comp_inl_inr v).symm
          rw [hv, he₂,
            fiber_transportWords_regroup e
              (s.trans (Equiv.sumComm (Fin (S * b)) (Fin b))) U u x]
          exact fiberSection (reindex _ (hins _)) _
        · intro u y y' hyy'
          rw [hB, hB]
          exact fiber_congr (reindex s (hins u)) hyy'
        · intro u y y' hsection
          simp only [hgooddef, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hsection]
        · intro v y
          let u : ω → Fin (k + 1) := fun a ↦ v (Sum.inl a)
          let x : Fin b → Fin (k + 1) := fun j ↦ v (Sum.inr j)
          have hv : v = Sum.elim u x := (Sum.elim_comp_inl_inr v).symm
          rw [hv, he₁, he₂]
          exact (concat_comp_swap e s u y x).symm
      obtain ⟨𝒲, hfin', hcont', hdisj', hdens'⟩ := ih ι (ω ⊕ Fin b) e₂ (U \ R) hins'
      let newTiles := tile '' (good : Set (ω ⊕ Fin (S * b) → Fin (k + 1)))
      have hnewdisjoint : newTiles.PairwiseDisjoint fun V ↦
          (Subspace.range V : Set (ι → Fin (k + 1))) := by
        rw [Set.pairwiseDisjoint_iff]
        intro V hV V' hV' hmeet
        obtain ⟨z, hz, rfl⟩ := hV
        obtain ⟨z', hz', rfl⟩ := hV'
        obtain ⟨w, hw, hw'⟩ := hmeet
        obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
        obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
        have hzz : z = z' := by
          funext a
          simpa only [htiledef, transportSubspace_apply, Function.comp_apply,
            Equiv.apply_symm_apply, Sum.elim_inl] using
            congrFun (hx.trans hx'.symm) (e₁.symm (Sum.inl a))
        rw [hzz]
      obtain ⟨hfinite, hcontained, hdisjoint, hdensity⟩ :=
        combine_tiling_stage U R newTiles 𝒲
          (good.finite_toSet.image tile) hfin' hRU
          (fun _ hV ↦ by obtain ⟨z, hz, rfl⟩ := hV; exact htileR z hz)
          (fun w hw ↦ by
            obtain ⟨z, hz, hmem⟩ := hRtile w hw
            exact ⟨tile z, ⟨z, hz, rfl⟩, hmem⟩)
          hnewdisjoint hcont' hdisj' hdensR hdens'
      refine ⟨newTiles ∪ 𝒲, hfinite, hcontained, hdisjoint, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hdensity

/-- Finite-stage block packing gives one exact sufficient dimension for one-family tiling. -/
lemma exists_tilingSufficient_dimension (k m : ℕ) (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, TilingSufficient k m β N := by
  by_cases hβ : β < 1
  · set b := max m (Subspace.restrictAlphabetBound k m β) with hbdef
    have hc : 0 < β / ((k : ℝ) + 1) ^ b := by positivity
    obtain ⟨T, hT⟩ := exists_nat_gt (1 / (β / ((k : ℝ) + 1) ^ b))
    rw [div_lt_iff₀ hc] at hT
    refine ⟨T * b, ?_⟩
    intro i D hD hDβ
    have hsections : ∀ v : Fin 0 → Fin (k + 1),
        IsInsensitive i.castSucc (Fin.last k)
          (fiber (transportWords (Equiv.emptySum (Fin 0) (Fin (T * b))).symm D) v) := by
      intro v x y hxy
      simp only [mem_fiber, mem_transportWords]
      apply hD
      intro a hai hal c
      simpa only [Function.comp_apply, Equiv.emptySum_symm_apply, Sum.elim_inr] using
        hxy a hai hal c
    obtain ⟨𝒱, hfinite, hcontained, hpairwise, hconclusion⟩ :=
      exists_tiling_of_insensitive_sections i hDHJ hm (le_max_left _ _) hβ₀ hβ
        (le_max_right _ _) T (Fin (T * b)) (Fin 0)
        (Equiv.emptySum (Fin 0) (Fin (T * b))).symm D hsections
    refine ⟨𝒱, hfinite, hcontained, hpairwise, ?_⟩
    rcases hconclusion with hlt | hle
    · exact hlt
    · exfalso
      have hD₁ : (D.dens : ℝ) ≤ 1 := by exact_mod_cast Finset.dens_le_one (s := D)
      have hnonneg : (0 : ℝ) ≤ ((uncovered D 𝒱).dens : ℝ) := by positivity
      linarith
  · refine ⟨m, ?_⟩
    intro _i D _hD hDβ
    have hD₁ : (D.dens : ℝ) ≤ 1 := by exact_mod_cast Finset.dens_le_one (s := D)
    linarith

/-- A tiling in every fixed extra-coordinate section combines to a tiling of the full cube. -/
private lemma tilingSufficient_mono {k m N n : ℕ} {β : ℝ}
    (hN : TilingSufficient k m β N) (hNn : N ≤ n) :
    TilingSufficient k m β n := by
  classical
  intro i D hD hDβ
  let r := n - N
  have hNr : N + r = n := Nat.add_sub_of_le hNn
  let e : Fin r ⊕ Fin N ≃ Fin n :=
    (Equiv.sumComm (Fin r) (Fin N)).trans <| finSumFinEquiv.trans (finCongr hNr)
  let wordEquiv :=
    e.arrowCongr (Equiv.refl (Fin (k + 1)))
  let D' := D.map wordEquiv.symm.toEmbedding
  let slice := fun z : Fin r → Fin (k + 1) ↦ fiber D' z
  have hslice (z : Fin r → Fin (k + 1)) :
      IsInsensitive i.castSucc (Fin.last k) (slice z) := by
    intro x y hxy
    simp only [slice, mem_fiber, D', Finset.mem_map_equiv]
    apply hD
    intro a hai hal c
    cases hc : e.symm c with
    | inl j => simp [wordEquiv, Equiv.arrowCongr, hc]
    | inr j => simpa [wordEquiv, Equiv.arrowCongr, hc] using hxy a hai hal j
  have existsLocal (z : Fin r → Fin (k + 1)) :
      ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N)),
        𝒱.Finite ∧
        (∀ V ∈ 𝒱, Subspace.IsContained V (slice z)) ∧
        (𝒱.PairwiseDisjoint fun V ↦
          (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
        ((uncovered (slice z) 𝒱).dens : ℝ) < 2 * β := by
    by_cases hz : 2 * β ≤ ((slice z).dens : ℝ)
    · exact hN i (slice z) (hslice z) hz
    · exact ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty,
        by simpa using lt_of_not_ge hz⟩
  choose tiles hlocalFinite hlocalContained hlocalDisjoint hlocalDensity using existsLocal
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ z, padExtraSubspace e z '' tiles z
  obtain ⟨hglobalFinite, hglobalContained, hglobalDisjoint⟩ := padded_tiles_facts e D tiles
    hlocalFinite
    (fun z V hV ↦ by simpa only [slice, D'] using hlocalContained z V hV)
    hlocalDisjoint
  refine ⟨global, hglobalFinite, hglobalContained, hglobalDisjoint, ?_⟩
  · let E := (uncovered D global).map wordEquiv.symm.toEmbedding
    have hfiber (z : Fin r → Fin (k + 1)) :
        fiber E z = uncovered (slice z) (tiles z) := by
      simpa only [E, global, slice, D', wordEquiv] using
        fiber_uncovered_padded e D tiles z
    have hEdens :
        (E.dens : ℝ) = ((uncovered D global).dens : ℝ) := by
      simp only [E, Finset.dens_map_equiv]
    rw [← hEdens, ← average_density_fiber]
    apply Finset.expect_lt
    · intro z _
      rw [hfiber]
      exact (hlocalDensity z).le
    · let z : Fin r → Fin (k + 1) := fun _ ↦ 0
      refine ⟨z, Finset.mem_univ z, ?_⟩
      rw [hfiber]
      exact hlocalDensity z

/-- One-family tiling sufficiency is upward closed after padding with unused final coordinates. -/
lemma exists_eventually_tilingSufficient (k m : ℕ) (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, ∀ n ≥ N, TilingSufficient k m β n := by
  obtain ⟨N, hN⟩ := exists_tilingSufficient_dimension k m hDHJ hm hβ₀
  refine ⟨N, ?_⟩
  intro _n hn
  exact tilingSufficient_mono hN hn

/-- A sufficient ambient dimension for tiling one insensitive family.  The tiling argument needs
density Hales--Jewett for the smaller alphabet, so the witness is selected under
`HasDensityHJ k`. -/
noncomputable def tilingBound (k m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : HasDensityHJ k ∧ 1 ≤ m ∧ 0 < β then
    Nat.find (exists_eventually_tilingSufficient k m h.1 h.2.1 h.2.2)
  else 0

/-- The selected one-family tiling bound satisfies the tiling predicate in every larger
dimension. -/
lemma tilingBound_spec (k m n : ℕ) (hDHJ : HasDensityHJ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β)
    (hn : tilingBound k m β ≤ n) : TilingSufficient k m β n := by
  classical
  rw [tilingBound, dif_pos ⟨hDHJ, hm, hβ₀⟩] at hn
  exact Nat.find_spec (exists_eventually_tilingSufficient k m hDHJ hm hβ₀) n hn

/-- The preimage of a word family in a subspace parameter cube. -/
noncomputable def parameterPreimage {η α ι : Type*} [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι) (D : Finset (ι → α)) : Finset (η → α) := by
  classical
  apply Finset.univ.filter
  intro x
  exact V x ∈ D

/-- Pulling an insensitive family back through a subspace preserves its sensitivity pair. -/
lemma parameterPreimage_isInsensitive {α η ι : Type*}
    [Fintype (η → α)] {a b : α} (V : Combinatorics.Subspace η α ι) (D : Finset (ι → α))
    (hD : IsInsensitive a b D) : IsInsensitive a b (parameterPreimage V D) := by
  classical
  intro x y hxy
  simp only [parameterPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  apply hD
  intro c hca hcb i
  cases hi : V.idxFun i with
  | inl d => rw [V.apply_inl hi, V.apply_inl hi]
  | inr e =>
    rw [V.apply_inr hi, V.apply_inr hi]
    exact hxy c hca hcb e

/-- Composing a finite disjoint family of inner tiles with one outer tile preserves finiteness,
containment, and pairwise-disjointness. -/
lemma composed_inner_tiles_facts {k d M n : ℕ}
    (D : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n))
    (𝒲 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin M)))
    (h𝒲 : 𝒲.Finite)
    (hcontained : ∀ W ∈ 𝒲, Subspace.IsContained W (parameterPreimage V D))
    (hpairwise : 𝒲.PairwiseDisjoint fun W ↦
      (Subspace.range W : Set (Fin M → Fin (k + 1)))) :
    let 𝒰 := Subspace.compose V '' 𝒲
    𝒰.Finite ∧
      (∀ U ∈ 𝒰, Subspace.IsContained U D) ∧
      (𝒰.PairwiseDisjoint fun U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) := by
  classical
  refine ⟨h𝒲.image (Subspace.compose V), ?_, ?_⟩
  · intro U hU x
    obtain ⟨W, hW, rfl⟩ := hU
    simp only [Subspace.compose_apply]
    simpa only [parameterPreimage, Finset.mem_filter, Finset.mem_univ, true_and] using
      hcontained W hW x
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' hU' hcommon
    obtain ⟨W, hW, rfl⟩ := hU
    obtain ⟨W', hW', rfl⟩ := hU'
    apply congrArg (Subspace.compose V)
    apply Set.pairwiseDisjoint_iff.mp hpairwise hW hW'
    obtain ⟨z, hz, hz'⟩ := hcommon
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hz
    obtain ⟨y, hy⟩ := Subspace.mem_range.mp hz'
    refine ⟨W x, Subspace.mem_range.mpr ⟨x, rfl⟩,
      Subspace.mem_range.mpr ⟨y, ?_⟩⟩
    apply Subspace.injective V
    simpa only [Subspace.compose_apply] using hy.trans hx.symm

/-- Mapping a parameter-cube family into a subspace scales its ambient density by the density of
the whole subspace range. -/
private lemma dens_map_subspace_eq_mul_range {α η ι : Type*}
    [Fintype (η → α)] [Fintype (ι → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (η → α)) :
    ((A.map ⟨V, Subspace.injective V⟩).dens : ℝ) =
      (A.dens : ℝ) * ((Subspace.range V).dens : ℝ) := by
  simp only [Finset.nnratCast_dens, Subspace.range, Finset.card_map]
  rw [Finset.card_image_iff.mpr (Subspace.injective V).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · let : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hA : A = ∅ := Subsingleton.elim _ _
    rw [hA]
    simp
  · field_simp
    simp only [Finset.card_univ]

/-- An ambient dimension is sufficient for tiling every dense intersection of `r` insensitive
families. -/
def IntersectionTilingSufficient (k r m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ (_ : 1 ≤ r), ∀ hrk : r ≤ k,
    ∀ D : Fin r → Finset (Fin n → Fin (k + 1)),
    (∀ i, IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (D i)) →
    2 * r * β ≤ ((intersection D).dens : ℝ) →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V (intersection D)) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered (intersection D) 𝒱).dens : ℝ) < 2 * r * β

/-- One indexed insensitive family is exactly the one-family tiling statement. -/
private lemma intersectionTilingSufficient_one {k m n : ℕ} {β : ℝ}
    (h : TilingSufficient k m β n) :
    IntersectionTilingSufficient k 1 m β n := by
  intro _ hrk D hD hDβ
  have hintersection : intersection D = D 0 := by
    ext x
    simp [Fin.forall_fin_one]
  obtain ⟨𝒱, hfinite, hcontained, hpairwise, huncovered⟩ :=
    h (Fin.castLE hrk 0) (D 0) (hD 0) (by
      rw [hintersection] at hDβ
      norm_num at hDβ ⊢
      exact hDβ)
  refine ⟨𝒱, hfinite, ?_, hpairwise, ?_⟩
  · simpa only [hintersection] using hcontained
  · rw [hintersection]
    norm_num
    exact huncovered

/-- Errors inside pairwise-disjoint outer tiles have total ambient density at most their common
relative-density bound. -/
private lemma mapped_inner_errors_density_le {k M n : ℕ} {β : ℝ} (hβ₀ : 0 < β)
    (𝒱 : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)))
    (hfinite : 𝒱.Finite)
    (hpairwise : 𝒱.PairwiseDisjoint fun V ↦
      (Subspace.range V : Set (Fin n → Fin (k + 1))))
    (localError : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) →
      Finset (Fin M → Fin (k + 1)))
    (hlocal : ∀ V, ((localError V).dens : ℝ) ≤ 2 * β) :
    let outer := hfinite.toFinset
    let errors := outer.biUnion fun V ↦
      (localError V).map ⟨V, Subspace.injective V⟩
    (errors.dens : ℝ) ≤ 2 * β := by
  classical
  dsimp only
  let outer := hfinite.toFinset
  let innerError := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    (localError V).map ⟨V, Subspace.injective V⟩
  have herror_pairwise : (outer : Set _).PairwiseDisjoint innerError := by
    intro V hV V' hV' hVV
    change Disjoint (innerError V) (innerError V')
    rw [Finset.disjoint_left]
    intro w hw hw'
    apply Set.disjoint_left.mp (hpairwise
      (by simpa [outer] using hV) (by simpa [outer] using hV') hVV)
    · obtain ⟨x, _hx, hxw⟩ := Finset.mem_map.mp hw
      exact Subspace.mem_range.mpr ⟨x, hxw⟩
    · obtain ⟨x', _hx', hx'w⟩ := Finset.mem_map.mp hw'
      exact Subspace.mem_range.mpr ⟨x', hx'w⟩
  rw [Finset.dens_biUnion herror_pairwise]
  change (NNRat.castHom ℝ) (∑ V ∈ outer, (innerError V).dens) ≤ 2 * β
  rw [map_sum (NNRat.castHom ℝ)]
  have hsummand (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      ((innerError V).dens : ℝ) ≤ 2 * β * ((Subspace.range V).dens : ℝ) := by
    dsimp only [innerError]
    rw [dens_map_subspace_eq_mul_range]
    exact mul_le_mul_of_nonneg_right (hlocal V) (by positivity)
  apply (Finset.sum_le_sum fun V _ ↦ hsummand V).trans
  rw [← Finset.mul_sum]
  have hranges_pairwise : (outer : Set _).PairwiseDisjoint
      (fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
        Subspace.range V) := by
    intro V hV V' hV' hVV
    change Disjoint (Subspace.range V) (Subspace.range V')
    rw [Finset.disjoint_left]
    intro w hw hw'
    exact Set.disjoint_left.mp (hpairwise
      (by simpa [outer] using hV) (by simpa [outer] using hV') hVV) hw hw'
  have hsum : (∑ V ∈ outer, ((Subspace.range V).dens : ℝ)) ≤ 1 := by
    have hdens_ranges : (((outer.biUnion Subspace.range).dens : ℚ≥0) : ℝ) =
        ∑ V ∈ outer, ((Subspace.range V).dens : ℝ) := by
      rw [Finset.dens_biUnion hranges_pairwise]
      change (NNRat.castHom ℝ) (∑ V ∈ outer, (Subspace.range V).dens) = _
      rw [map_sum (NNRat.castHom ℝ)]
      rfl
    rw [← hdens_ranges]
    exact_mod_cast Finset.dens_le_one (s := outer.biUnion Subspace.range)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hβ₀.le)

/-- A point missed by all composed tiles is either missed by all outer tiles, or belongs to the
uncovered inner error inside the unique outer tile containing it. -/
private lemma uncovered_composed_tiles_subset {k r m M n : ℕ}
    (D : Fin r.succ → Finset (Fin n → Fin (k + 1)))
    (D₀ : Fin r → Finset (Fin n → Fin (k + 1)))
    (hsubset : intersection D ⊆ intersection D₀)
    (𝒱 : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)))
    (hfinite : 𝒱.Finite)
    (tiles : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) →
      Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M))) :
    let pullback := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
      parameterPreimage V (D (Fin.last r))
    let global := ⋃ V : 𝒱, Subspace.compose V.val '' tiles V
    let errors := hfinite.toFinset.biUnion fun V ↦
      (uncovered (pullback V) (tiles V)).map ⟨V, Subspace.injective V⟩
    uncovered (intersection D) global ⊆ uncovered (intersection D₀) 𝒱 ∪ errors := by
  classical
  dsimp only
  intro w hw
  simp only [uncovered, Finset.mem_filter] at hw
  simp only [uncovered, Finset.mem_filter, Finset.mem_union]
  by_cases hparent : ∃ V ∈ 𝒱, w ∈ Subspace.range V
  · right
    obtain ⟨V, hV, hwV⟩ := hparent
    obtain ⟨x, hx⟩ := Subspace.mem_range.mp hwV
    refine Finset.mem_biUnion.mpr ⟨V, by simpa using hV, ?_⟩
    apply Finset.mem_map.mpr
    refine ⟨x, ?_, hx⟩
    simp only [Finset.mem_filter]
    constructor
    · simp only [parameterPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx ▸ (mem_intersection.mp hw.1 (Fin.last r))
    · intro W hW hxW
      apply hw.2 (Subspace.compose V W)
      · exact Set.mem_iUnion_of_mem ⟨V, hV⟩ <|
          Set.mem_image_of_mem (Subspace.compose V) hW
      · obtain ⟨y, hy⟩ := Subspace.mem_range.mp hxW
        exact Subspace.mem_range.mpr ⟨y, by rw [Subspace.compose_apply, hy, hx]⟩
  · left
    refine ⟨hsubset hw.1, ?_⟩
    intro V hV hwV
    exact hparent ⟨V, hV, hwV⟩

/-- Composing the inner tilings with a disjoint outer tiling preserves all packing properties and
adds the final insensitive family to the containment statement. -/
private lemma composed_outer_tiles_facts {k r m M n : ℕ}
    (D : Fin (r + 1) → Finset (Fin n → Fin (k + 1)))
    (D₀ : Fin r → Finset (Fin n → Fin (k + 1)))
    (hD₀ : ∀ i, D₀ i = D (Fin.castSucc i))
    (𝒱 : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)))
    (hfinite : 𝒱.Finite)
    (hcontained : ∀ V ∈ 𝒱, Subspace.IsContained V (intersection D₀))
    (hpairwise : 𝒱.PairwiseDisjoint fun V ↦
      (Subspace.range V : Set (Fin n → Fin (k + 1))))
    (tiles : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) →
      Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M)))
    (hinner : ∀ V,
      (Subspace.compose V '' tiles V).Finite ∧
      (∀ U ∈ Subspace.compose V '' tiles V,
        Subspace.IsContained U (D (Fin.last r))) ∧
      ((Subspace.compose V '' tiles V).PairwiseDisjoint fun U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1))))) :
    let global := ⋃ V : 𝒱, Subspace.compose V.val '' tiles V
    global.Finite ∧
      (∀ U ∈ global, Subspace.IsContained U (intersection D)) ∧
      (global.PairwiseDisjoint fun U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) := by
  classical
  let : Finite 𝒱 := hfinite
  dsimp only
  refine ⟨Set.finite_iUnion fun V ↦ (hinner V).1, ?_, ?_⟩
  · intro U hU x
    simp only [Set.mem_iUnion] at hU
    obtain ⟨V, W, hW, rfl⟩ := hU
    rw [mem_intersection]
    intro i
    refine Fin.lastCases ?_ ?_ i
    · exact (hinner V).2.1 (Subspace.compose V W)
        (Set.mem_image_of_mem (Subspace.compose V.val) hW) x
    · intro j
      simpa only [Subspace.compose_apply, hD₀ j] using
        mem_intersection.mp (hcontained V V.prop (W x)) j
  · rw [Set.pairwiseDisjoint_iff]
    intro U hU U' hU' hcommon
    simp only [Set.mem_iUnion] at hU hU'
    obtain ⟨V, hU⟩ := hU
    obtain ⟨V', hU'⟩ := hU'
    have hVV : V = V' := by
      refine Subtype.ext (Set.pairwiseDisjoint_iff.mp hpairwise V.prop V'.prop ?_)
      obtain ⟨w, hw, hw'⟩ := hcommon
      obtain ⟨x, hx⟩ := Subspace.mem_range.mp hw
      obtain ⟨x', hx'⟩ := Subspace.mem_range.mp hw'
      obtain ⟨W, hW, rfl⟩ := hU
      obtain ⟨W', hW', rfl⟩ := hU'
      refine ⟨V.val (W x), Subspace.mem_range.mpr ⟨W x, rfl⟩,
        Subspace.mem_range.mpr ⟨W' x', ?_⟩⟩
      simpa only [Subspace.compose_apply] using hx'.trans hx.symm
    subst V'
    exact Set.pairwiseDisjoint_iff.mp (hinner V).2.2 hU hU' hcommon

/-- The two-stage outer/inner packing step for adding one insensitive family. -/
private lemma extend_intersection_tiling {k r m M n : ℕ}
    (hr₀ : 1 ≤ r) (hrk : r + 1 ≤ k) {β : ℝ} (hβ₀ : 0 < β)
    (houter : IntersectionTilingSufficient k r M β n)
    (hinner : TilingSufficient k m β M) :
    IntersectionTilingSufficient k (r + 1) m β n := by
  intro _ hrk' D hD hDβ
  let D₀ : Fin r → Finset (Fin n → Fin (k + 1)) := fun i ↦
    D (Fin.castSucc i)
  have hsubset : intersection D ⊆ intersection D₀ := by grind [mem_intersection]
  have hD₀ (i : Fin r) :
      IsInsensitive (Fin.castLE (by omega) i).castSucc (Fin.last k) (D₀ i) := by
    have hindex : Fin.castLE hrk' (Fin.castSucc i) = Fin.castLE (by omega) i := Fin.ext rfl
    rw [← hindex]
    simpa only [D₀] using hD (Fin.castSucc i)
  obtain ⟨𝒱, hfinite, hcontained, hpairwise, huncovered⟩ :=
    houter hr₀ (by omega) D₀ hD₀ (by
        apply le_trans (b := 2 * ((r : ℝ) + 1) * β)
        · nlinarith
        · have hdens : ((intersection D).dens : ℝ) ≤ ((intersection D₀).dens : ℝ) := by
            exact_mod_cast Finset.dens_mono hsubset
          convert hDβ.trans hdens using 1
          norm_num)
  let iLast : Fin k := ⟨r, by omega⟩
  let DLast := D (Fin.last r)
  have hLast : IsInsensitive iLast.castSucc (Fin.last k) DLast := by
    convert hD (Fin.last r) using 1
    simp only [iLast, Fin.castLE, Fin.last, Fin.castSucc]
  let pullback := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    parameterPreimage V DLast
  have hPullback (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      IsInsensitive iLast.castSucc (Fin.last k) (pullback V) :=
    parameterPreimage_isInsensitive V DLast hLast
  have existsInner (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      ∃ 𝒲 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M)),
        𝒲.Finite ∧
        (∀ W ∈ 𝒲, Subspace.IsContained W (pullback V)) ∧
        (𝒲.PairwiseDisjoint fun W ↦
          (Subspace.range W : Set (Fin M → Fin (k + 1)))) ∧
        ((uncovered (pullback V) 𝒲).dens : ℝ) < 2 * β := by
    by_cases hV : 2 * β ≤ ((pullback V).dens : ℝ)
    · exact hinner iLast (pullback V) (hPullback V) hV
    · exact ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty,
        by simpa using lt_of_not_ge hV⟩
  choose tiles htilesFinite htilesContained htilesDisjoint htilesDensity using existsInner
  let composed := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    Subspace.compose V '' tiles V
  have hcomposed (V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n)) :
      (composed V).Finite ∧
      (∀ U ∈ composed V, Subspace.IsContained U DLast) ∧
      ((composed V).PairwiseDisjoint fun U ↦
        (Subspace.range U : Set (Fin n → Fin (k + 1)))) :=
    composed_inner_tiles_facts DLast V (tiles V)
      (htilesFinite V) (htilesContained V) (htilesDisjoint V)
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ V : 𝒱, composed V
  obtain ⟨hglobalFinite, hglobalContained, hglobalDisjoint⟩ :=
    composed_outer_tiles_facts D D₀ (fun _ ↦ rfl) 𝒱 hfinite
      hcontained hpairwise tiles (fun V ↦ by simpa only [composed] using hcomposed V)
  refine ⟨global, ?_, ?_, ?_, ?_⟩
  · simpa only [global, composed] using hglobalFinite
  · simpa only [global, composed] using hglobalContained
  · simpa only [global, composed] using hglobalDisjoint
  · let outer := hfinite.toFinset
    let innerError := fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
      (uncovered (pullback V) (tiles V)).map ⟨V, Subspace.injective V⟩
    let errors := outer.biUnion innerError
    have herrors : (errors.dens : ℝ) ≤ 2 * β := by
      simpa only [errors, outer, innerError] using
        mapped_inner_errors_density_le hβ₀ 𝒱 hfinite hpairwise
          (fun V ↦ uncovered (pullback V) (tiles V))
          (fun V ↦ (htilesDensity V).le)
    have huncovered_subset :
        uncovered (intersection D) global ⊆
          uncovered (intersection D₀) 𝒱 ∪ errors := by
      simpa only [global, composed, errors, outer, innerError, pullback, DLast] using
        uncovered_composed_tiles_subset D D₀ hsubset 𝒱 hfinite tiles
    have hdens :
        ((uncovered (intersection D) global).dens : ℝ) ≤
          ((uncovered (intersection D₀) 𝒱 ∪ errors).dens : ℝ) := by
      exact_mod_cast Finset.dens_mono huncovered_subset
    have hdens_union :
        ((uncovered (intersection D₀) 𝒱 ∪ errors).dens : ℝ) ≤
          ((uncovered (intersection D₀) 𝒱).dens : ℝ) + (errors.dens : ℝ) := by
      exact_mod_cast Finset.dens_union_le (uncovered (intersection D₀) 𝒱) errors
    refine hdens.trans_lt (hdens_union.trans_lt ?_)
    convert add_lt_add_of_lt_of_le huncovered herrors using 1
    push_cast
    ring

/-- Induction on the number of insensitive families gives one exact sufficient intersection-tiling
dimension. -/
lemma exists_intersectionTilingSufficient_dimension (k r m : ℕ) (hDHJ : HasDensityHJ k)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, IntersectionTilingSufficient k r m β N := by
  induction r using Nat.strong_induction_on generalizing m with
  | h r ih =>
      obtain rfl | hr := r
      · omega
      obtain rfl | s := hr
      · obtain ⟨N, hN⟩ := exists_tilingSufficient_dimension k m hDHJ hm hβ₀
        exact ⟨N, intersectionTilingSufficient_one hN⟩
      · let M := max 1 (tilingBound k m β)
        have hM : 1 ≤ M := le_max_left _ _
        obtain ⟨N, houter⟩ :=
          ih (s + 1) (by omega) M (by omega) (by omega) hM
        have hinner : TilingSufficient k m β M :=
          tilingBound_spec k m M hDHJ hm hβ₀ (le_max_right _ _)
        exact ⟨N, extend_intersection_tiling (by omega) (by omega) hβ₀ houter hinner⟩

/-- Exact intersection-tiling sufficiency transports to every larger coordinate dimension. -/
private lemma intersectionTilingSufficient_mono {k r m N n : ℕ} {β : ℝ}
    (hN : IntersectionTilingSufficient k r m β N) (hNn : N ≤ n) :
    IntersectionTilingSufficient k r m β n := by
  classical
  intro hr₀ hrk D hD hDβ
  let q := n - N
  have hNq : N + q = n := Nat.add_sub_of_le hNn
  let e : Fin q ⊕ Fin N ≃ Fin n :=
    (Equiv.sumComm (Fin q) (Fin N)).trans <| finSumFinEquiv.trans (finCongr hNq)
  let wordEquiv := e.arrowCongr (Equiv.refl (Fin (k + 1)))
  let D' := fun i ↦ (D i).map wordEquiv.symm.toEmbedding
  let slice := fun z : Fin q → Fin (k + 1) ↦ fun i ↦ fiber (D' i) z
  have hslice (z : Fin q → Fin (k + 1)) (i : Fin r) :
      IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (slice z i) := by
    intro x y hxy
    simp only [slice, mem_fiber, D', Finset.mem_map_equiv]
    apply hD i
    intro a hai hal c
    cases hc : e.symm c with
    | inl j => simp [wordEquiv, Equiv.arrowCongr, hc]
    | inr j => simpa [wordEquiv, Equiv.arrowCongr, hc] using hxy a hai hal j
  let I := intersection D
  let I' := I.map wordEquiv.symm.toEmbedding
  have hIdens : (I'.dens : ℝ) = (I.dens : ℝ) := by
    simp only [I', Finset.dens_map_equiv]
  have hfiberI (z : Fin q → Fin (k + 1)) :
      fiber I' z = intersection (slice z) := by
    ext y
    simp only [mem_fiber, Finset.mem_map_equiv, I', I, mem_intersection, slice, D',
      Equiv.symm_symm]
  have existsLocal (z : Fin q → Fin (k + 1)) :
      ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin N)),
        𝒱.Finite ∧
        (∀ V ∈ 𝒱, Subspace.IsContained V (intersection (slice z))) ∧
        (𝒱.PairwiseDisjoint fun V ↦
          (Subspace.range V : Set (Fin N → Fin (k + 1)))) ∧
        ((uncovered (intersection (slice z)) 𝒱).dens : ℝ) < 2 * r * β := by
    by_cases hz : 2 * r * β ≤ ((intersection (slice z)).dens : ℝ)
    · exact hN hr₀ hrk (slice z) (hslice z) hz
    · exact ⟨∅, Set.finite_empty, by simp, Set.pairwiseDisjoint_empty,
        by simpa using lt_of_not_ge hz⟩
  choose tiles hlocalFinite hlocalContained hlocalDisjoint hlocalDensity using existsLocal
  let global : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) :=
    ⋃ z, padExtraSubspace e z '' tiles z
  obtain ⟨hglobalFinite, hglobalContained, hglobalDisjoint⟩ := padded_tiles_facts e I tiles
    hlocalFinite
    (fun z V hV ↦ by simpa only [I', ← hfiberI z] using hlocalContained z V hV)
    hlocalDisjoint
  refine ⟨global, hglobalFinite, ?_, hglobalDisjoint, ?_⟩
  · simpa only [I, mem_intersection] using hglobalContained
  · let E := (uncovered I global).map wordEquiv.symm.toEmbedding
    have hfiber (z : Fin q → Fin (k + 1)) :
        fiber E z = uncovered (intersection (slice z)) (tiles z) := by
      rw [← hfiberI z]
      simpa only [E, global, I', wordEquiv] using fiber_uncovered_padded e I tiles z
    have hEdens :
        (E.dens : ℝ) = ((uncovered I global).dens : ℝ) := by
      simp only [E, Finset.dens_map_equiv]
    rw [← hEdens, ← average_density_fiber]
    apply Finset.expect_lt
    · intro z _
      rw [hfiber]
      exact (hlocalDensity z).le
    · let z : Fin q → Fin (k + 1) := fun _ ↦ 0
      refine ⟨z, Finset.mem_univ z, ?_⟩
      rw [hfiber]
      exact hlocalDensity z

/-- Intersection-tiling sufficiency is upward closed after padding with unused final
coordinates. -/
lemma exists_eventually_intersectionTilingSufficient (k r m : ℕ) (hDHJ : HasDensityHJ k)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) :
    ∃ N, ∀ n ≥ N, IntersectionTilingSufficient k r m β n := by
  obtain ⟨N, hN⟩ :=
    exists_intersectionTilingSufficient_dimension k r m hDHJ hr₀ hrk hm hβ₀
  exact ⟨N, fun _n hn ↦ intersectionTilingSufficient_mono hN hn⟩

/-- A sufficient ambient dimension for tiling an intersection of insensitive families, again
selected under `HasDensityHJ k`. -/
noncomputable def intersectionTilingBound (k r m : ℕ) (β : ℝ) : ℕ := by
  classical
  exact if h : HasDensityHJ k ∧ 1 ≤ r ∧ r ≤ k ∧ 1 ≤ m ∧ 0 < β then
    Nat.find (exists_eventually_intersectionTilingSufficient
      k r m h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 0

/-- The selected intersection-tiling bound satisfies the tiling predicate in every larger
dimension. -/
lemma intersectionTilingBound_spec (k r m n : ℕ) (hDHJ : HasDensityHJ k)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β)
    (hn : intersectionTilingBound k r m β ≤ n) :
    IntersectionTilingSufficient k r m β n := by
  classical
  rw [intersectionTilingBound,
    dif_pos ⟨hDHJ, hr₀, hrk, hm, hβ₀⟩] at hn
  exact Nat.find_spec
    (exists_eventually_intersectionTilingSufficient k r m hDHJ hr₀ hrk hm hβ₀) n hn

/-- An intersection of insensitive families can be tiled by disjoint subspaces. -/
lemma exists_disjoint_subspaces_iInter {k : ℕ} (r m n : ℕ) (hDHJ : HasDensityHJ k)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m)
    (β : ℝ) (hβ₀ : 0 < β)
    (hn : intersectionTilingBound k r m β ≤ n)
    (D : Fin r → Finset (Fin n → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (D i))
    (hDβ : 2 * r * β ≤ ((intersection D).dens : ℝ)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      𝒱.Finite ∧
      (∀ V ∈ 𝒱, Subspace.IsContained V (intersection D)) ∧
      (𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (Fin n → Fin (k + 1)))) ∧
      ((uncovered (intersection D) 𝒱).dens : ℝ) < 2 * r * β :=
  intersectionTilingBound_spec k r m n hDHJ hr₀ hrk hm hβ₀ hn hr₀ hrk D hD hDβ

end IsInsensitive
end DensityHalesJewett

end

section

/-! From DensityHalesJewett.DensityIncrement.CorrelatedFibers by Gabriel Dahia. -/

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- A finite word family contains no complete combinatorial line. -/
def IsLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ∃ a, l a ∉ A

/-- Pull a word family back to the parameter cube of a subspace. -/
def pullback {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι → α)) : Finset (η → α) :=
  Finset.univ.filter fun x ↦ V x ∈ A

/-- The working parameter dimension of the correlated-fibers lemma. -/
noncomputable def correlatedFibersParameters (k m : ℕ) (δ : ℝ) : ℕ :=
  max m (Parameters.m₀ k δ)

/-- The line-canonization dimension of the correlated-fibers lemma. -/
noncomputable def correlatedFibersLines (k m : ℕ) (δ : ℝ) : ℕ :=
  max 1 (GrahamRothschild.bound (k + 1) 2 (correlatedFibersParameters k m δ))

/-- A bound for the correlated-fibers lemma.  Uniformization now returns its own coordinate cut,
so the bound constrains the total ambient dimension. -/
noncomputable def correlatedFibersBound (k m : ℕ) (δ : ℝ) : ℕ :=
  Subspace.variableCutFibersBound (k + 1) (correlatedFibersLines k m δ)
    (Parameters.η k δ ^ 2 / 2)

/-- Uniformization followed by line canonization produces a large subspace on which every
restricted-alphabet line is uniformly good or uniformly sparse. -/
lemma exists_uniform_fibers_and_homogeneous_lines {k M L : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ)
    {ι κ : Type*} [Finite ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (huniform : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
      ((∀ l : Combinatorics.Line (Fin k) (Fin M),
          Parameters.θ k δ ≤
            ((Finset.univ.filter fun y ↦
              ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
        (∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ)) := by
  let : Nontrivial (Fin (k + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  let ε := Parameters.η k δ ^ 2 / 2
  have hε₀ : 0 < ε := by positivity [Parameters.η_pos hk hδ₀]
  by_cases hM : 1 ≤ M
  · have hL : 1 ≤ L := by
      by_contra hL
      obtain rfl : L = 0 := by omega
      obtain ⟨R, _⟩ :=
        GrahamRothschild.lines_twoColor (Fin (k + 1)) M 0
          (by simpa only [Fintype.card_fin] using hGR) ∅
      obtain ⟨i, _⟩ := R.proper ⟨0, hM⟩
      exact Fin.elim0 i
    obtain ⟨U, hU⟩ := huniform hL
    let : Fintype (Combinatorics.Line (Fin (k + 1)) (Fin L)) :=
      Subspace.lineFintype (k + 1) L
    let goodLines :=
      Finset.univ.filter fun q : Combinatorics.Line (Fin (k + 1)) (Fin L) ↦
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a : Fin k, Sum.elim (U (q a.castSucc)) y ∈ A).dens : ℝ)
    obtain ⟨R, hgood | hbad⟩ :=
      GrahamRothschild.lines_twoColor (Fin (k + 1)) M L
        (by simpa only [Fintype.card_fin] using hGR) goodLines
    · refine ⟨Subspace.compose U R, ?_, ?_⟩
      · intro x
        rw [Subspace.compose_apply]
        have hx := hU (R x)
        linarith
      · left
        intro l
        have hl := hgood (l.map Fin.castSucc)
        simpa only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply,
          Subspace.compose_apply] using hl
    · refine ⟨Subspace.compose U R, ?_, ?_⟩
      · intro x
        rw [Subspace.compose_apply]
        have hx := hU (R x)
        linarith
      · right
        intro l
        have hl := hbad (l.map Fin.castSucc)
        simp only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply] at hl
        simpa only [Subspace.compose_apply] using lt_of_not_ge hl
  · have hM₀ : M = 0 := by omega
    subst M
    let : Fintype (ι → Fin (k + 1)) := Fintype.ofFinite _
    have havg :
        δ ≤ 𝔼 x : ι → Fin (k + 1), ((fiber A x).dens : ℝ) := by
      simpa only [average_density_fiber] using hA
    obtain ⟨x, _, hx⟩ :=
      Finset.exists_le_of_le_expect Finset.univ_nonempty havg
    let W : Combinatorics.Subspace (Fin 0) (Fin (k + 1)) ι := {
      idxFun := fun i ↦ Sum.inl (x i)
      proper := fun e ↦ Fin.elim0 e
    }
    refine ⟨W, ?_, ?_⟩
    · intro z
      have hW : W z = x := by
        funext i
        simp only [W, Combinatorics.Subspace.coe_apply, Sum.elim_inl, id_eq]
      rw [hW]
      dsimp only [ε] at hε₀
      linarith
    · left
      intro l
      exact Fin.elim0 l.proper.choose

/-- Restricting the parameter directions of a good correlated-fibers subspace preserves its
uniform fiber and common-line-fiber estimates. -/
lemma restrict_correlated_fibers_subspace {k m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M)
    {δ : ℝ} {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  let R := Subspace.repeatInitial (Fin (k + 1)) hm hmM
  let V := Subspace.compose W R
  refine ⟨V, ?_, ?_⟩
  · intro x
    simpa only [V, Subspace.compose_apply] using hfibers (R x)
  · intro l
    let Rk := Subspace.repeatInitial (Fin k) hm hmM
    simpa only [V, R, Rk, Subspace.compose_apply, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using
        hlines (Subspace.composeLine Rk l)

/-- Uniformize the fibers and canonize their line-density coloring.

The working parameter dimension is chosen large enough both for the requested `m`-dimensional
output and for the density Hales--Jewett argument at dimension `Parameters.m₀ k δ`.  In the
monochromatic good case, restrict the working subspace to `m` parameters.  In the bad case, retain
the larger subspace as a certificate whose every restricted-alphabet line has common-suffix density
strictly below `Parameters.θ k δ`. -/
lemma exists_correlated_fibers_or_sparse_certificate {k M L : ℕ} (hk : 2 ≤ k)
    (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ)
    {ι κ : Type*} [Finite ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hmM : m ≤ M) (hm₀M : Parameters.m₀ k δ ≤ M)
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ))
    (huniform : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
      ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
        ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
          (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin M),
            ((Finset.univ.filter fun y ↦
              ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
                Parameters.θ k δ := by
  obtain ⟨W, hfibers, hgood | hsparse⟩ :=
    exists_uniform_fibers_and_homogeneous_lines hk hδ₀ hGR A hA huniform
  · exact .inl <|
      restrict_correlated_fibers_subspace hm hmM A W hfibers hgood
  · right
    exact ⟨M, hm₀M, W, hfibers, hsparse⟩

/-- Uniformly dense fibers force a positive-density set of suffixes whose restricted parameter
slice has density at least `δ / 4`. -/
lemma dense_suffixes_of_uniform_fibers {k M : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    δ / 4 ≤
      ((Finset.univ.filter fun y : κ → Fin (k + 1) ↦
        δ / 4 ≤
          ((Finset.univ.filter fun x : Fin M → Fin k ↦
            Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let f := fun y : κ → Fin (k + 1) ↦
    ((Finset.univ.filter fun x : Fin M → Fin k ↦
      Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hη₀ := Parameters.η_pos hk hδ₀
  have hηδ := Parameters.η_le_δ_div_six k δ
  have havg : δ - Parameters.η k δ ^ 2 / 2 ≤
      Finset.expect Finset.univ f := by
    rw [Subspace.average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty fun x _ ↦ hfibers (Fin.castSucc ∘ x)
  have hthreshold := density_ge_threshold f
    (δ - Parameters.η k δ ^ 2 / 2) (δ / 4)
    (fun y ↦ by
      dsimp only [f]
      exact_mod_cast Finset.dens_le_one)
    (by nlinarith [sq_nonneg δ]) havg
  refine (le_div_iff₀ (by linarith : 0 < 1 - δ / 4)).mpr ?_ |>.trans hthreshold
  nlinarith [sq_nonneg δ]

/-- Density Hales--Jewett in every dense suffix slice, followed by finite pigeonhole, produces
one parameter line shared by at least a `θ`-density set of suffixes. -/
lemma exists_popular_line_of_dense_suffixes {k M : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hM : Parameters.m₀ k δ ≤ M)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  classical
  let q := Parameters.m₀ k δ
  have hq₀ : 0 < q := Parameters.m₀_pos k δ
  let R := Subspace.repeatInitial (Fin (k + 1)) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  let W₀ := Subspace.compose W R
  have hW₀ : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W₀ x)).dens : ℝ) := by
    intro x
    simpa only [W₀, Subspace.compose_apply] using hfibers (R x)
  have hdense := dense_suffixes_of_uniform_fibers hk hδ₀ hδ₁ A W₀ hW₀
  let := Subspace.lineFintype k q
  let B := Finset.univ.filter fun y : κ → Fin (k + 1) ↦
    δ / 4 ≤
      ((Finset.univ.filter fun x : Fin q → Fin k ↦
        Sum.elim (W₀ (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hB : δ / 4 ≤ (B.dens : ℝ) := by
    simpa only [B] using hdense
  have hBne : B.Nonempty :=
    Finset.dens_pos.mp (by exact_mod_cast lt_of_lt_of_le (by linarith : 0 < δ / 4) hB)
  have hbound : Subspace.densityOneBound k (δ / 4) ≤ q := by
    dsimp only [q]
    rw [Subspace.densityOneBound, dif_pos ⟨by linarith, hDHJ⟩,
      Parameters.m₀, dif_pos ⟨hδ₀, hDHJ⟩]
    omega
  have existsLine (y : κ → Fin (k + 1)) (hy : y ∈ B) :
      ∃ l : Combinatorics.Line (Fin k) (Fin q),
        ∀ a, Sum.elim (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    let S := Finset.univ.filter fun x : Fin q → Fin k ↦
      Sum.elim (W₀ (Fin.castSucc ∘ x)) y ∈ A
    obtain ⟨l, hl⟩ :=
      Subspace.densityOneBound_spec hDHJ (δ / 4) (by linarith) q hbound S <|
        Subspace.card_le_of_density_le (by omega) (δ / 4) S
          (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, S] using hy)
    exact ⟨l, fun a ↦ by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hl a⟩
  choose lineAt hlineAt using fun y : {y // y ∈ B} ↦ existsLine y y.2
  let l₀ := lineAt ⟨hBne.choose, hBne.choose_spec⟩
  let : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let f : (κ → Fin (k + 1)) → Combinatorics.Line (Fin k) (Fin q) := fun y ↦
    if hy : y ∈ B then lineAt ⟨y, hy⟩ else l₀
  obtain ⟨l, hl⟩ := Subspace.exists_fiber_density B f
  have hcommon :
      (B.filter fun y ↦ f y = l) ⊆
        Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hline : lineAt ⟨y, hy.1⟩ = l := by
      simpa only [f, dif_pos hy.1] using hy.2
    intro a
    rw [← hline]
    exact hlineAt ⟨y, hy.1⟩ a
  have hcard :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ q - (k : ℝ) ^ q := by
    rw [Subspace.card_line k q (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) q
  have hθ :
      Parameters.θ k δ ≤
        (B.dens : ℝ) / Fintype.card (Combinatorics.Line (Fin k) (Fin q)) := by
    unfold Parameters.θ
    rw [← hcard]
    exact div_le_div_of_nonneg_right hB (by positivity)
  let Rk := Subspace.repeatInitial (Fin k) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  refine ⟨Subspace.composeLine Rk l, hθ.trans (hl.trans ?_)⟩
  exact_mod_cast Finset.dens_le_dens <| by
    simpa only [W₀, R, Rk, Subspace.compose_apply, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using hcommon

/-- The uniformly sparse certificate is impossible.

Average the dense fibers over suffixes, find many suffix slices of density at least `δ / 4`, and
apply `hDHJ` on an embedded `Parameters.m₀ k δ`-dimensional parameter cube in each such slice.
Pigeonholing the resulting lines gives one line with common-suffix density at least
`Parameters.θ k δ`, contradicting the certificate. -/
lemma not_exists_sparse_correlated_fibers_certificate {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    ¬ ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
      ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
        (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
        ∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ := by
  rintro ⟨M, hM, W, hfibers, hsparse⟩
  obtain ⟨l, hl⟩ :=
    exists_popular_line_of_dense_suffixes hk hDHJ hδ₀ hδ₁ hM A W hfibers
  exact (not_lt_of_ge hl) (hsparse l)

/-- Every parameter-cube line in a suitable subspace has a dense common fiber. -/
lemma exists_subspace_correlated_fibers {k M L : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Finite ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hmM : m ≤ M) (hm₀M : Parameters.m₀ k δ ≤ M)
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ))
    (huniform : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) :=
  (exists_correlated_fibers_or_sparse_certificate hk m hm δ hδ₀ hmM hm₀M hGR A hA
    huniform).resolve_right (not_exists_sparse_correlated_fibers_certificate hk hDHJ δ hδ₀ hδ₁ A)

/-- The pullback of a word family to a subspace after fixing the suffix coordinates. -/
def suffixPullback {α η ι κ : Type*} [Fintype (η → α)]
    [DecidableEq (ι ⊕ κ → α)] (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι ⊕ κ → α)) (y : κ → α) : Finset (η → α) :=
  Finset.univ.filter fun x ↦ Sum.elim (V x) y ∈ A

/-- The parameter lines whose first-`k` points belong to a word family at a fixed suffix. -/
def suffixLines {k m : ℕ} {ι κ : Type*}
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (y : κ → Fin (k + 1)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  Finset.univ.filter fun l ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A

/-- Fix suffix coordinates of a subspace. -/
def Subspace.fixSuffix {α η ι κ : Type*} (V : Combinatorics.Subspace η α ι)
    (y : κ → α) : Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun := Sum.elim V.idxFun (Sum.inl ∘ y)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩

/-- Fix suffix coordinates and transport the ambient coordinates along an equivalence. -/
def Subspace.fixSuffixReindex {α η ι κ ζ : Type*} (e : ι ⊕ κ ≃ ζ)
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α ζ :=
  (Subspace.fixSuffix V y).reindex (Equiv.refl _) (Equiv.refl _) e

/-- Pointwise fiber lower bounds imply the corresponding average lower bound for fixed-suffix
pullbacks.  This is a finite double-counting argument. -/
lemma average_suffixPullback_lower {α η ι κ : Type*} [Nonempty α] [Fintype (η → α)]
    [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) (r : ℝ)
    (hV : ∀ x, r ≤ ((fiber A (V x)).dens : ℝ)) :
    r ≤ 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) =
      𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
    calc
      𝔼 x : η → α, ((fiber A (V x)).dens : ℝ)
          = 𝔼 x : η → α, 𝔼 y : κ → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        simp
      _ = 𝔼 y : κ → α, 𝔼 x : η → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (η → α)) (Finset.univ : Finset (κ → α))]
      _ = 𝔼 y : κ → α, 𝔼 x : η → α,
          (Set.indicator (suffixPullback V A y) (1 : (η → α) → ℝ) x : ℝ) := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro x _
        by_cases h : Sum.elim (V x) y ∈ A <;> simp [fiber, suffixPullback, h]
      _ = 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
        simp
  have h_r_le_expect : r ≤ 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := η → α)) fun x _ => hV x
  exact h_r_le_expect.trans h_expect_eq.le

/-- If a function has average at least `δ - η²/2` but never reaches `δ + η²/2`, then it is at
least `δ - 2η` on all but an `η`-fraction of its domain. -/
lemma density_near_average {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (δ η : ℝ) (hη₀ : 0 < η)
    (havg : δ - η ^ 2 / 2 ≤ 𝔼 x : X, f x)
    (hupper : ∀ x, f x < δ + η ^ 2 / 2) :
    1 - η ≤ ((Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x).dens : ℝ) := by
  set H := Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x
  by_cases hH : 1 - η ≤ (H.dens : ℝ)
  · exact hH
  · exfalso
    have hfg : ∀ x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η)
        * (Set.indicator H (1 : X → ℝ) x : ℝ) := by
      intro x
      by_cases hxH : x ∈ H
      · rw [Set.indicator_of_mem (by simpa using hxH), Pi.one_apply, mul_one]
        linarith [hupper x]
      · rw [Set.indicator_of_notMem (by simpa using hxH), mul_zero, add_zero]
        have : ¬(δ - 2 * η ≤ f x) := by simpa [H] using hxH
        linarith
    have hexpect : 𝔼 x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) := by
      apply (Finset.expect_le_expect fun x _ ↦ hfg x).trans_eq
      rw [Finset.expect_add_distrib, Finset.expect_const univ_nonempty, ← Finset.mul_expect]
      simp
    linarith [havg, hexpect,
      mul_le_mul_of_nonneg_left (not_le.mp hH).le (by positivity : (0 : ℝ) ≤ η ^ 2 / 2 + 2 * η),
      mul_pos hη₀ hη₀, pow_pos hη₀ 3]

/-- Dense common suffix fibers for every line give the same lower bound for the average
fixed-suffix line density.  This is the second finite double-counting step. -/
lemma average_suffixLines_lower {k m : ℕ} {ι κ : Type*}
    [Fintype (κ → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (θ : ℝ)
    (hV : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      θ ≤ ((Finset.univ.filter fun y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    θ ≤ 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) =
      𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
    calc
      𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)
          = 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
            𝔼 y : κ → Fin (k + 1),
            (Set.indicator (Finset.univ.filter fun y ↦
              ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A)
              (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        apply Finset.expect_congr rfl
        intro l _
        rw [← Finset.expect_indicator_one]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A)
            (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (Combinatorics.Line (Fin k) (Fin m)))
          (Finset.univ : Finset (κ → Fin (k + 1)))]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (suffixLines V A y)
            (1 : Combinatorics.Line (Fin k) (Fin m) → ℝ) l : ℝ) := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro l _
        dsimp [suffixLines]
        by_cases h : ∀ a : Fin k, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A <;> simp [h]
      _ = 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
        simp
  have h_θ_le_expect : θ ≤ 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := Combinatorics.Line (Fin k) (Fin m)))
      fun l _ => hV l
  exact h_θ_le_expect.trans h_expect_eq.le

/-- A function bounded above by one with average at least `θ` exceeds `θ/2` on a set of
density at least `θ/2`. -/
lemma density_half_threshold {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hf₁ : ∀ x, f x ≤ 1) (havg : θ ≤ 𝔼 x : X, f x) :
    θ / 2 ≤ ((Finset.univ.filter fun x ↦ θ / 2 ≤ f x).dens : ℝ) := by
  refine le_trans ?_
    (density_ge_threshold f θ (θ / 2) hf₁ (by linarith) havg)
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - θ / 2)]
  nlinarith [sq_nonneg (θ / 2)]

/-- Two subsets of densities at least `1-η` and `θ/2` intersect when `η < θ/2`. -/
lemma exists_mem_inter_of_large_density {X : Type*} [Fintype X]
    (S T : Finset X) (η θ : ℝ)
    (hS : 1 - η ≤ (S.dens : ℝ)) (hT : θ / 2 ≤ (T.dens : ℝ))
    (hηθ : η < θ / 2) : ∃ x, x ∈ S ∧ x ∈ T := by
  classical
  by_contra h
  have hunion : ((S ∪ T).dens : ℝ) = (S.dens : ℝ) + (T.dens : ℝ) := by
    exact_mod_cast Finset.dens_union_of_disjoint
      (Finset.disjoint_left.mpr fun x hxS hxT ↦ h ⟨x, hxS, hxT⟩)
  have hle : ((S ∪ T).dens : ℝ) ≤ 1 := by
    exact_mod_cast Finset.dens_le_one (s := S ∪ T)
  linarith [hunion, hle]

/-- Correlated fibers yield either a dense fixed suffix or a fixed suffix supporting many
complete parameter lines. -/
lemma exists_suffix_many_lines {k m : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (Fin m → Fin (k + 1))]
    [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (hfiber : ∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    (∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤
      ((suffixPullback V A y).dens : ℝ)) ∨
    ∃ y, δ - 2 * Parameters.η k δ ≤ ((suffixPullback V A y).dens : ℝ) ∧
      Parameters.θ k δ / 2 ≤ ((suffixLines V A y).dens : ℝ) := by
  classical
  let f := fun y : κ → Fin (k + 1) ↦ ((suffixPullback V A y).dens : ℝ)
  let g := fun y : κ → Fin (k + 1) ↦ ((suffixLines V A y).dens : ℝ)
  by_cases hinc : ∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤ f y
  · exact .inl hinc
  right
  have hη₀ : 0 < Parameters.η k δ := Parameters.η_pos hk hδ₀
  have hη₁ : Parameters.η k δ ≤ 1 :=
    (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  have havgf : δ - Parameters.η k δ ^ 2 / 2 ≤ 𝔼 y, f y :=
    average_suffixPullback_lower V A _ hfiber
  have hupper : ∀ y, f y < δ + Parameters.η k δ ^ 2 / 2 := by
    intro y
    exact lt_of_not_ge fun hy ↦ hinc ⟨y, hy⟩
  have hmostly : 1 - Parameters.η k δ ≤
      ((Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y).dens : ℝ) :=
    density_near_average f δ (Parameters.η k δ) hη₀ havgf hupper
  have havgg : Parameters.θ k δ ≤ 𝔼 y, g y :=
    average_suffixLines_lower V A (Parameters.θ k δ) hlines
  have hmany : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y).dens : ℝ) := by
    refine density_half_threshold g (Parameters.θ k δ) (Parameters.θ_pos hk hδ₀)
      (Parameters.θ_le_one hk hδ₁) ?_ havgg
    intro y
    dsimp only [g]
    exact_mod_cast Finset.dens_le_one (s := suffixLines V A y)
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_inter_of_large_density
    (Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y)
    (Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y)
    (Parameters.η k δ) (Parameters.θ k δ) hmostly hmany
    (Parameters.η_lt_θ_div_two hk hδ₀)
  refine ⟨y, ?_, ?_⟩
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f] using hy₁
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g] using hy₂

/-- Fixing a suffix and reindexing preserves the relative-density and complete-line statistics.
The proof is coordinate bookkeeping using `Subspace.reindex_apply` and `Finset.mem_map_equiv`. -/
lemma Subspace.fixSuffixReindex_statistics {k m : ℕ} {ι κ ζ : Type*}
    [Fintype (Fin m → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ζ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (e : ι ⊕ κ ≃ ζ) (A : Finset (ζ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (y : κ → Fin (k + 1)) :
    let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
    (Subspace.relativeDensity (Subspace.fixSuffixReindex e V y) A : ℝ) =
        ((suffixPullback V A' y).dens : ℝ) ∧
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, Subspace.fixSuffixReindex e V y (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) =
        ((suffixLines V A' y).dens : ℝ) := by
  intro A'
  have h_fixSuffix_eval (x : Fin m → Fin (k + 1)) :
      (Subspace.fixSuffix V y : (Fin m → Fin (k + 1)) → (ι ⊕ κ → Fin (k + 1))) x
        = Sum.elim (V x) y := by
    ext j
    cases j <;> simp [Subspace.fixSuffix, Combinatorics.Subspace.coe_apply]
  have h_eval (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x = Sum.elim (V x) y ∘ e.symm := by
    calc
      Subspace.fixSuffixReindex e V y x
          = (Subspace.fixSuffix V y) x ∘ e.symm := by
        ext i
        simp [Subspace.fixSuffixReindex, Combinatorics.Subspace.reindex_apply]
      _ = Sum.elim (V x) y ∘ e.symm := by rw [h_fixSuffix_eval x]
  have h_mem_map (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x ∈ A ↔ Sum.elim (V x) y ∈ A' := by
    rw [h_eval x]
    dsimp [A']
    simp [Finset.mem_map_equiv, Equiv.arrowCongr]
  constructor
  · dsimp [Subspace.relativeDensity, suffixPullback]
    congr
    ext x
    simp [h_mem_map x]
  · dsimp [suffixLines]
    congr
    ext l
    exact forall_congr' fun a ↦ h_mem_map (Fin.castSucc ∘ l a)

/-- A bound for the many-lines lemma. -/
noncomputable def manyLinesBound (k m : ℕ) (δ : ℝ) : ℕ :=
  correlatedFibersBound k m δ

/-- Either density has already increased on an `m`-subspace, or a dense slice contains a positive
proportion of all parameter-cube lines. -/
lemma exists_subspace_many_lines {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (m : ℕ) [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (hm : 1 ≤ m) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)) ∨
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ - 2 * Parameters.η k δ ≤ (Subspace.relativeDensity V A : ℝ) ∧
      Parameters.θ k δ / 2 ≤
        ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
          ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) := by
  classical
  have hε₀ : 0 < Parameters.η k δ ^ 2 / 2 := by
    positivity [Parameters.η_pos hk hδ₀]
  obtain ⟨p, q, e, _hq, U, hU⟩ :=
    Subspace.variableCutFibersBound_spec (k + 1) (correlatedFibersLines k m δ) n
      (le_max_left _ _) hε₀ (by simpa only [manyLinesBound, correlatedFibersBound] using hn) A
  let A' := Subspace.splitWords e A
  have hA' : δ ≤ (A'.dens : ℝ) := by
    simpa only [A', Subspace.dens_splitWords] using hA
  obtain ⟨W, hWfiber, hWlines⟩ :=
    exists_subspace_correlated_fibers hk hDHJ m hm δ hδ₀ hδ₁
      (ι := Fin p) (κ := Fin q) (M := correlatedFibersParameters k m δ)
      (L := correlatedFibersLines k m δ) (le_max_left _ _) (le_max_right _ _)
      (le_max_right _ _) A' hA' (fun _ ↦ ⟨U, fun x ↦ by
        simpa only [A', Subspace.dens_splitWords] using hU x⟩)
  obtain ⟨y, hy⟩ | ⟨y, hy, hylines⟩ :=
    exists_suffix_many_lines hk δ hδ₀ hδ₁ A' W hWfiber hWlines
  · left
    use Subspace.fixSuffixReindex e W y
    rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
    simpa only [A', Subspace.splitWords] using hy
  · right
    refine ⟨Subspace.fixSuffixReindex e W y, ?_, ?_⟩
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
      simpa only [A', Subspace.splitWords] using hy
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).2]
      simpa only [A', Subspace.splitWords] using hylines

end DensityHalesJewett

end

section

/-! From DensityHalesJewett.DensityIncrement.StructuredCorrelation by Gabriel Dahia. -/

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- A power of the restricted-alphabet proportion eventually falls below the error tolerance. -/
lemma exists_restrictedParameterWords_decay {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) :
    ∃ m : ℕ, ((k : ℝ) / (k + 1)) ^ m < Parameters.η k δ := by
  apply exists_pow_lt_of_lt_one (Parameters.η_pos hk hδ₀)
  apply (div_lt_one (by positivity : 0 < (k + 1 : ℝ))).mpr
  norm_num

/-- A parameter-cube dimension sufficient for the insensitive-intersection construction. -/
noncomputable def insensitiveIntersectionDimension (k : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact if h : 2 ≤ k ∧ 0 < δ then
    Nat.find (exists_restrictedParameterWords_decay h.1 h.2)
  else 0

/-- Above the selected dimension, the restricted-alphabet proportion is at most the error
tolerance. -/
lemma insensitiveIntersectionDimension_spec {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hm : insensitiveIntersectionDimension k δ ≤ m) :
    ((k : ℝ) / (k + 1)) ^ m ≤ Parameters.η k δ := by
  classical
  rw [insensitiveIntersectionDimension, dif_pos ⟨hk, hδ₀⟩] at hm
  refine (pow_le_pow_of_le_one (by positivity) ?_ hm).trans ?_
  · exact (div_le_one (by positivity : 0 < (k + 1 : ℝ))).mpr (by norm_num)
  · exact (Nat.find_spec (exists_restrictedParameterWords_decay hk hδ₀)).le

/-- Replace every occurrence of the final alphabet letter by a fixed restricted-alphabet
letter. -/
def replaceLastLetter {k m : ℕ} (i : Fin k) (x : Fin m → Fin (k + 1)) :
    Fin m → Fin (k + 1) :=
  fun c ↦ if x c = Fin.last k then i.castSucc else x c

/-- The endpoint family associated with one restricted-alphabet letter. -/
def endpointFamily {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (i : Fin k) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter fun x ↦ V (replaceLastLetter i x) ∈ A

/-- Parameter words which avoid the final alphabet letter. -/
def restrictedParameterWords (k m : ℕ) : Finset (Fin m → Fin (k + 1)) :=
  Finset.univ.filter fun x ↦ ∀ c, x c ≠ Fin.last k

/-- The restricted parameter words are exactly the pointwise images of `Fin k`-valued words. -/
lemma restrictedParameterWords_eq_map (k m : ℕ) :
    restrictedParameterWords k m =
      Finset.univ.map (Function.Embedding.piCongrRight fun _ : Fin m ↦
        (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) := by
  classical
  ext x
  simp only [restrictedParameterWords, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · intro hx
    let y : Fin m → Fin k := fun c ↦ (x c).castPred (hx c)
    refine ⟨y, ?_⟩
    funext c
    exact Fin.castSucc_castPred (x c) (hx c)
  · rintro ⟨y, rfl⟩ c
    exact Fin.castSucc_ne_last (y c)

/-- The density of restricted parameter words is the expected power of the alphabet ratio. -/
lemma restrictedParameterWords_density (k m : ℕ) :
    ((restrictedParameterWords k m).dens : ℝ) = ((k : ℝ) / (k + 1)) ^ m := by
  rw [restrictedParameterWords_eq_map, Finset.nnratCast_dens, Finset.card_map,
    Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
    Fintype.card_pi_const, Fintype.card_fin]
  rw [div_pow]
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- Each endpoint family is insensitive to interchanging its selected letter with the final
letter. -/
lemma endpointFamily_isInsensitive {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k) :
    IsInsensitive i.castSucc (Fin.last k) (endpointFamily A V i) := by
  intro x y hxy
  have hreplace : replaceLastLetter i x = replaceLastLetter i y := by
    funext c
    by_cases hxi : x c = i.castSucc <;> by_cases hyi : y c = i.castSucc <;>
      grind [replaceLastLetter, hxy (x c), hxy (y c)]
  simp only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hreplace]

/-- Encode a restricted-alphabet line by the word using the final letter on its wildcard
coordinates. -/
private def lineEndpoint {k m : ℕ} (l : Combinatorics.Line (Fin k) (Fin m)) :
    Fin m → Fin (k + 1) :=
  fun c ↦
    match l.idxFun c with
    | none => Fin.last k
    | some a => a.castSucc

/-- The endpoint word remembers every fixed letter and every wildcard coordinate of a line. -/
private lemma lineEndpoint_injective {k m : ℕ} :
    Function.Injective (lineEndpoint : Combinatorics.Line (Fin k) (Fin m) →
      (Fin m → Fin (k + 1))) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ hll
  congr
  funext c
  have hc := congrFun hll c
  cases hfc : f c <;> cases hgc : g c <;>
    simp_all [lineEndpoint, Fin.castSucc_ne_last, eq_comm (a := Fin.last k)]

/-- Complete restricted-alphabet parameter lines inject into the intersection of the endpoint
families, giving the required density lower bound. -/
lemma endpointFamily_intersection_dense {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    {δ : ℝ} (hδ₀ : 0 < δ)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hrestricted : ((restrictedParameterWords k m).dens : ℝ) ≤ 1 / 2)
    (hlines : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    Parameters.θ k δ / 4 ≤
      ((IsInsensitive.intersection (endpointFamily A V)).dens : ℝ) := by
  classical
  let good := Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
    ∀ a, V (Fin.castSucc ∘ l a) ∈ A
  let endpointEmbedding :
      Combinatorics.Line (Fin k) (Fin m) ↪ (Fin m → Fin (k + 1)) :=
    ⟨lineEndpoint, lineEndpoint_injective⟩
  have hsubset :
      good.map endpointEmbedding ⊆ IsInsensitive.intersection (endpointFamily A V) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hx
    apply IsInsensitive.mem_intersection.mpr
    intro i
    simp only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and]
    have hgood :
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A := by
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    have heval :
        replaceLastLetter i (lineEndpoint l) = Fin.castSucc ∘ l i := by
      funext c
      cases hc : l.idxFun c with
      | none =>
          simp [lineEndpoint, replaceLastLetter, Combinatorics.Line.coe_apply, hc]
      | some a =>
          simp [lineEndpoint, replaceLastLetter, Combinatorics.Line.coe_apply, hc,
            Fin.castSucc_ne_last]
    change V (replaceLastLetter i (lineEndpoint l)) ∈ A
    rw [heval]
    exact hgood i
  have hmono :
      ((good.map endpointEmbedding).dens : ℝ) ≤
        ((IsInsensitive.intersection (endpointFamily A V)).dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens hsubset
  refine (le_trans ?_ hmono)
  have hgood :
      Parameters.θ k δ / 2 ≤ (good.dens : ℝ) := by
    simpa only [good] using hlines
  have hlinepos :
      0 < (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) := by
    have hgoodpos : 0 < (good.dens : ℝ) :=
      (div_pos (Parameters.θ_pos hk hδ₀) (by norm_num)).trans_le hgood
    have hgne : good.Nonempty := Finset.dens_pos.mp (by exact_mod_cast hgoodpos)
    let : Nonempty (Combinatorics.Line (Fin k) (Fin m)) := ⟨hgne.choose⟩
    exact_mod_cast Fintype.card_pos
  rw [Finset.nnratCast_dens, Finset.card_map]
  rw [Finset.nnratCast_dens] at hgood hrestricted
  have hlinecard :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin m)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    rw [Subspace.card_line k m (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) m
  have hwordcard :
      (Fintype.card (Fin m → Fin (k + 1)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ m := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow]
  have hrestrictedcard :
      (restrictedParameterWords k m).card = k ^ m := by
    rw [restrictedParameterWords_eq_map, Finset.card_map, Finset.card_univ,
      Fintype.card_pi_const, Fintype.card_fin]
  rw [hlinecard] at hgood hlinepos
  rw [hwordcard] at ⊢
  rw [hrestrictedcard, Nat.cast_pow, hwordcard] at hrestricted
  have hwordpos : 0 < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hhalf :
      ((k + 1 : ℕ) : ℝ) ^ m / 2 ≤
        ((k + 1 : ℕ) : ℝ) ^ m - (k : ℝ) ^ m := by
    apply (div_le_iff₀ hwordpos).mp at hrestricted
    nlinarith
  rw [le_div_iff₀ hlinepos] at hgood
  rw [le_div_iff₀ hwordpos]
  nlinarith [hhalf, hgood, Parameters.θ_pos hk hδ₀]

/-- In a line-free ambient family, a word lying both in its pullback and in every endpoint family
cannot use the final alphabet letter. -/
lemma pullback_inter_endpointFamily_subset_restricted {k m n : ℕ}
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A) :
    pullback V A ∩ IsInsensitive.intersection (endpointFamily A V) ⊆
      restrictedParameterWords k m := by
  intro x hx
  obtain ⟨hxpull, hxinter⟩ := Finset.mem_inter.mp hx
  simp only [restrictedParameterWords, Finset.mem_filter, Finset.mem_univ, true_and]
  intro c hc
  let p : Combinatorics.Line (Fin (k + 1)) (Fin m) := {
    idxFun := fun i ↦ if x i = Fin.last k then none else some (x i)
    proper := ⟨c, if_pos hc⟩
  }
  have hp_last : p (Fin.last k) = x := by
    funext i
    by_cases hi : x i = Fin.last k <;>
      simp only [p, Combinatorics.Line.coe_apply, hi, ↓reduceIte, Option.getD_none,
        Option.getD_some]
  have hp_cast (i : Fin k) : p i.castSucc = replaceLastLetter i x := by
    funext j
    by_cases hj : x j = Fin.last k <;>
      simp only [p, replaceLastLetter, Combinatorics.Line.coe_apply, hj, ↓reduceIte,
        Option.getD_none, Option.getD_some]
  obtain ⟨a, ha⟩ := hfree (Subspace.composeLine V p)
  apply ha
  rw [Subspace.composeLine_apply]
  obtain ⟨i, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
  · rw [hp_cast]
    have hi := IsInsensitive.mem_intersection.mp hxinter i
    simpa only [endpointFamily, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · rw [hp_last]
    simpa only [pullback, Finset.mem_filter, Finset.mem_univ, true_and] using hxpull

/-- In a sufficiently large parameter cube, words avoiding the final letter have density at most
`η`. -/
lemma restrictedParameterWords_density_le_eta {k m : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m) :
    ((restrictedParameterWords k m).dens : ℝ) ≤ Parameters.η k δ := by
  rw [restrictedParameterWords_density]
  exact insensitiveIntersectionDimension_spec hk hδ₀ hm_large

/-- Many complete restricted-alphabet lines yield a large insensitive intersection whose part
inside a line-free family is small.  This packages the endpoint construction, its injective
line count, the identification of the intersection, and the geometric-decay estimate. -/
lemma exists_endpoint_insensitive_intersection {k m n : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hfree : IsLineFree A)
    (hlines : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ)) :
    ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
      Parameters.θ k δ / 4 ≤ ((IsInsensitive.intersection C).dens : ℝ) ∧
      ((pullback V A ∩ IsInsensitive.intersection C).dens : ℝ) ≤
        Parameters.η k δ := by
  refine ⟨endpointFamily A V, endpointFamily_isInsensitive A V, ?_, ?_⟩
  · refine endpointFamily_intersection_dense hk hδ₀ A V ?_ hlines
    apply (restrictedParameterWords_density_le_eta hk hδ₀ hm_large).trans
    exact (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  · refine le_trans ?_ <|
      restrictedParameterWords_density_le_eta hk hδ₀ hm_large
    exact_mod_cast Finset.dens_mono <|
      pullback_inter_endpointFamily_subset_restricted A V hfree

/-- Removing an intersection of density at least `θ / 4`, while losing at most `η` of a family
of density `δ - 2η`, gives the two complement estimates used below. -/
lemma density_complement_bounds {X : Type*} [Fintype X] [Nonempty X]
    [DecidableEq X] (A C : Finset X) (δ η θ : ℝ)
    (hδ₀ : 0 ≤ δ) (hη₀ : 0 ≤ η) (hA : δ - 2 * η ≤ (A.dens : ℝ))
    (hC : θ / 4 ≤ (C.dens : ℝ))
    (hAC : ((A ∩ C).dens : ℝ) ≤ η)
    (hgain : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η) :
    (δ + 6 * η) * ((Cᶜ).dens : ℝ) ≤ ((A ∩ Cᶜ).dens : ℝ) ∧
      δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
  have hsplitA : ((A ∩ C).dens : ℝ) + ((A ∩ Cᶜ).dens : ℝ) = (A.dens : ℝ) := by
    norm_cast
    simpa only [sdiff_eq_inter_compl] using Finset.dens_inter_add_dens_sdiff A C
  have hsplitC : ((Cᶜ).dens : ℝ) + (C.dens : ℝ) = 1 := by
    norm_cast
    simpa only [← compl_eq_univ_sdiff, Finset.dens_univ] using
      Finset.dens_sdiff_add_dens_eq_dens C.subset_univ
  have houtside : δ - 3 * η ≤ ((A ∩ Cᶜ).dens : ℝ) := by
    linarith [hsplitA, hA, hAC]
  constructor
  · refine (mul_le_mul_of_nonneg_left ?_ ?_).trans (hgain.trans houtside)
    · linarith [hsplitC, hC]
    · linarith [hδ₀, hη₀]
  · exact houtside

/-- An intersection of insensitive families with a density gain on its complement. -/
lemma exists_large_insensitive_intersection {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A)
    (hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (Subspace.relativeDensity V A : ℝ) < δ + Parameters.η k δ ^ 2 / 2) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ C : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) ∧
        (δ + 6 * Parameters.η k δ) *
            ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
        δ - 3 * Parameters.η k δ ≤
          ((pullback V A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  classical
  let : Fintype (Combinatorics.Line (Fin k) (Fin m)) :=
    Fintype.ofInjective (fun l ↦ l.idxFun) fun _ _ h ↦ Combinatorics.Line.ext h
  obtain ⟨V, hV⟩ | ⟨V, hV, hlines⟩ :=
    exists_subspace_many_lines hk hDHJ m hm δ hδ₀ hδ₁ n hn A hA
  · exact ((not_lt_of_ge hV) (hsmall V)).elim
  obtain ⟨C, hC, hCdense, hAC⟩ :=
    exists_endpoint_insensitive_intersection hk δ hδ₀ hδ₁ hm_large A V hfree hlines
  refine ⟨V, C, hC, ?_⟩
  apply density_complement_bounds
  · exact hδ₀.le
  · exact (Parameters.η_pos hk hδ₀).le
  · simpa only [Subspace.relativeDensity, pullback] using hV
  · exact hCdense
  · exact hAC
  · exact Parameters.large_intersection_complement_gain hk hδ₀

/-- The part of the complement of an indexed intersection at which membership first fails. -/
def firstFailurePiece {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Finset X :=
  (C i)ᶜ ∩ Finset.univ.filter fun x ↦ ∀ j, j < i → x ∈ C j

/-- Replace the first failed set by its complement, retain the preceding sets, and make all
subsequent constraints vacuous. -/
def firstFailureFamily {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) : Fin k → Finset X :=
  fun j ↦ if j < i then C j else if j = i then (C j)ᶜ else Finset.univ

/-- Every member of the first-failure family has the required sensitivity pair. -/
lemma firstFailureFamily_isInsensitive {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    ∀ j, IsInsensitive j.castSucc (Fin.last k) (firstFailureFamily C i j) := by
  intro j
  dsimp [firstFailureFamily]
  by_cases hij : j < i
  · simp [hij, hC j]
  · by_cases hej : j = i
    · rw [hej]
      simpa using (hC i).compl
    · simp [hij, hej, IsInsensitive]

/-- Intersecting the first-failure family recovers its selected piece. -/
lemma firstFailureFamily_intersection {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) (i : Fin k) :
    IsInsensitive.intersection (firstFailureFamily C i) = firstFailurePiece C i := by
  ext x
  simp only [IsInsensitive.mem_intersection, firstFailureFamily, firstFailurePiece,
    Finset.mem_inter, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    constructor
    · have hxi := hx i
      simp only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] at hxi
      exact hxi
    · intro j hij
      simpa only [if_pos hij] using hx j
  · rintro ⟨hnot, hbefore⟩ j
    by_cases hij : j < i
    · simpa only [if_pos hij] using hbefore j hij
    · by_cases hji : j = i
      · subst j
        simpa only [lt_self_iff_false, ↓reduceIte, Finset.mem_compl] using hnot
      · simp only [if_neg hij, if_neg hji, Finset.mem_univ]

/-- The first-failure pieces cover the complement of the original intersection. -/
lemma firstFailurePiece_biUnion {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    Finset.univ.biUnion (firstFailurePiece C) = (IsInsensitive.intersection C)ᶜ := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    rw [firstFailurePiece, Finset.mem_inter, Finset.mem_compl] at hi
    rw [Finset.mem_compl]
    intro hinter
    exact hi.1 (IsInsensitive.mem_intersection.mp hinter i)
  · rw [Finset.mem_compl]
    intro hx
    have hfailed : ∃ i, x ∉ C i := by
      by_contra! h
      exact hx <| IsInsensitive.mem_intersection.mpr h
    let I := Finset.univ.filter fun i : Fin k ↦ x ∉ C i
    have hI : I.Nonempty := by
      obtain ⟨i, hi⟩ := hfailed
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i := I.min' hI
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [firstFailurePiece, Finset.mem_inter, Finset.mem_compl]
    constructor
    · exact (Finset.mem_filter.mp (I.min'_mem hI)).2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hij
      by_contra hj
      have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      exact (not_lt_of_ge (I.min'_le j hjI)) hij

/-- A first-failure piece is disjoint from every piece at a later index. -/
lemma firstFailurePiece_disjoint_of_lt {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) {i j : Fin k} (hij : i < j) :
    Disjoint (firstFailurePiece C i : Set X) (firstFailurePiece C j : Set X) := by
  dsimp only [Disjoint]
  intro x hxi hxj
  simp only [firstFailurePiece, coe_inter, coe_compl, coe_filter, mem_univ, true_and,
    Set.subset_inter_iff] at *
  simp only [Set.bot_eq_empty, Set.subset_empty_iff]
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  exact (hxi.1 hy) (hxj.2 hy i hij)

/-- Distinct first-failure pieces are pairwise disjoint. -/
lemma firstFailurePiece_pairwiseDisjoint {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (C : Fin k → Finset X) :
    (Set.univ : Set (Fin k)).PairwiseDisjoint fun i ↦ (firstFailurePiece C i : Set X) := by
  intro i _ j _ hij
  obtain hij | hji := lt_or_gt_of_ne hij
  · exact firstFailurePiece_disjoint_of_lt C hij
  · exact (firstFailurePiece_disjoint_of_lt C hji).symm

/-- The first-failure partition converts the densities of its pieces, and of their intersections
with `A`, into sums. -/
lemma firstFailurePiece_density_sums {k : ℕ}
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X) :
    (∑ i, ((firstFailurePiece C i).dens : ℝ)) =
        (((IsInsensitive.intersection C)ᶜ).dens : ℝ) ∧
      (∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ)) =
        ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ) := by
  constructor
  · have h := Finset.dens_biUnion (s := Finset.univ) (t := firstFailurePiece C) <|
      Finset.pairwiseDisjoint_coe.mp <| by
        simpa only [Finset.coe_univ] using firstFailurePiece_pairwiseDisjoint C
    rw [firstFailurePiece_biUnion] at h
    rw [← NNRat.cast_sum]
    exact congrArg (fun q : ℚ≥0 ↦ (q : ℝ)) h.symm
  · have hpairwise :
        (Set.univ : Set (Fin k)).PairwiseDisjoint fun i ↦
          (A ∩ firstFailurePiece C i : Set X) :=
      (firstFailurePiece_pairwiseDisjoint C).mono_on fun _ _ ↦
        Set.inter_subset_right
    have h := Finset.dens_biUnion (s := Finset.univ)
      (t := fun i ↦ A ∩ firstFailurePiece C i) <|
        Finset.pairwiseDisjoint_coe.mp <| by
          simpa only [Finset.coe_univ, Finset.coe_inter] using hpairwise
    rw [← Finset.inter_biUnion, firstFailurePiece_biUnion] at h
    rw [← NNRat.cast_sum]
    exact congrArg (fun q : ℚ≥0 ↦ (q : ℝ)) h.symm

/-- The quantitative hypotheses and the first-failure density sums force one piece to be both
large and relatively dense in `A`. -/
lemma exists_dense_firstFailurePiece_of_density_sums {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X)
    (hweighted : (δ + 6 * Parameters.η k δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hsumPieces : (∑ i, ((firstFailurePiece C i).dens : ℝ)) =
      (((IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hsumIntersections : (∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ)) =
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((firstFailurePiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((firstFailurePiece C i).dens : ℝ) ≤
        ((A ∩ firstFailurePiece C i).dens : ℝ) := by
  by_contra! h
  let g := Parameters.γ k δ
  let e := Parameters.η k δ
  let c := (((IsInsensitive.intersection C)ᶜ).dens : ℝ)
  let a := ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)
  let : Nonempty (Fin k) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hk⟩⟩
  have hg₀ : 0 < g := Parameters.γ_pos hk hδ₀
  have he₀ : 0 < e := Parameters.η_pos hk hδ₀
  have hsum_lt :
      ∑ i, ((A ∩ firstFailurePiece C i).dens : ℝ) <
        ∑ i, ((δ + g) * ((firstFailurePiece C i).dens : ℝ) + g) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    by_cases hi : g ≤ ((firstFailurePiece C i).dens : ℝ)
    · linarith [h i (by simpa only [g] using hi)]
    · have hinter :
          ((A ∩ firstFailurePiece C i).dens : ℝ) ≤ ((firstFailurePiece C i).dens : ℝ) := by
        exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
      have hcoefficient : 0 ≤ δ + g := by linarith
      nlinarith [mul_nonneg hcoefficient
        (by positivity : 0 ≤ ((firstFailurePiece C i).dens : ℝ))]
  have hupper : a < (δ + g) * c + (k : ℝ) * g := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_lt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum_lt
    rwa [hsumPieces, hsumIntersections] at hsum_lt
  have hac : a ≤ c := by
    dsimp only [a, c]
    exact_mod_cast Finset.dens_le_dens Finset.inter_subset_right
  have hc : δ / 2 ≤ c := by
    dsimp only [a, c] at hlarge hac
    linarith [Parameters.η_le_δ_div_six k δ]
  have hcoef : 3 * e ≤ 6 * e - g := by
    dsimp only [e, g]
    linarith [Parameters.γ_le_three_mul_η k δ]
  have hleft :
      3 * e * (δ / 2) ≤ (6 * e - g) * c :=
    mul_le_mul hcoef hc (by positivity) (by linarith)
  have hk_real : 0 < (k : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two hk
  have hright : (k : ℝ) * g ≤ δ * e ^ 2 := by
    have hdiv : g ≤ δ * e ^ 2 / (k : ℝ) := by
      dsimp only [g, e]
      unfold Parameters.γ
      exact min_le_left _ _
    simpa only [mul_comm] using (le_div_iff₀ hk_real).mp hdiv
  have hstrict : δ * e ^ 2 < 3 * e * (δ / 2) := by
    dsimp only [e]
    nlinarith [Parameters.η_le_δ_div_six k δ]
  have hgap : (6 * e - g) * c < (k : ℝ) * g := by
    dsimp only [a, c, e, g] at hweighted hupper
    nlinarith
  exact (not_lt_of_ge hleft) (hgap.trans_le hright |>.trans hstrict)

/-- The first-failure partition and its quantitative weighted averaging.

The complement of `intersection C` is partitioned by `firstFailurePiece C i`.  The two global
density estimates ensure that one piece is both large enough and has the required relative
`A`-density. -/
lemma exists_dense_firstFailurePiece {k : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Finset X) (C : Fin k → Finset X)
    (hweighted : (δ + 6 * Parameters.η k δ) *
        ((IsInsensitive.intersection C)ᶜ.dens : ℝ) ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ))
    (hlarge : δ - 3 * Parameters.η k δ ≤
      ((A ∩ (IsInsensitive.intersection C)ᶜ).dens : ℝ)) :
    ∃ i : Fin k,
      Parameters.γ k δ ≤ ((firstFailurePiece C i).dens : ℝ) ∧
      (δ + Parameters.γ k δ) * ((firstFailurePiece C i).dens : ℝ) ≤
        ((A ∩ firstFailurePiece C i).dens : ℝ) := by
  obtain ⟨hsumPieces, hsumIntersections⟩ :=
    firstFailurePiece_density_sums A C
  exact exists_dense_firstFailurePiece_of_density_sums hk hδ₀ hδ₁ A C hweighted
    hlarge hsumPieces hsumIntersections

/-- The Boolean reconstruction of a first-failure piece as an insensitive intersection.

Complement closure preserves the sensitivity pair at the failure index, while the universal
sets after that index impose no constraints. -/
lemma firstFailureFamily_facts {k : ℕ} {ι : Type*}
    [Fintype (ι → Fin (k + 1))] [DecidableEq (ι → Fin (k + 1))]
    (C : Fin k → Finset (ι → Fin (k + 1)))
    (hC : ∀ i, IsInsensitive i.castSucc (Fin.last k) (C i)) (i : Fin k) :
    (∀ j, IsInsensitive j.castSucc (Fin.last k) (firstFailureFamily C i j)) ∧
      IsInsensitive.intersection (firstFailureFamily C i) = firstFailurePiece C i ∧
      Finset.univ.biUnion (firstFailurePiece C) = (IsInsensitive.intersection C)ᶜ ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint fun j ↦
        (firstFailurePiece C j : Set (ι → Fin (k + 1))) :=
  ⟨firstFailureFamily_isInsensitive C hC i,
    firstFailureFamily_intersection C i, firstFailurePiece_biUnion C,
    firstFailurePiece_pairwiseDisjoint C⟩

/-- Correlation with a positive-density intersection of insensitive families. -/
lemma exists_structured_correlation {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m n : ℕ) (hm : 1 ≤ m)
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_large : insensitiveIntersectionDimension k δ ≤ m)
    (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (hfree : IsLineFree A) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
        (∀ i, IsInsensitive i.castSucc (Fin.last k) (D i)) ∧
        Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ) ∧
        (δ + Parameters.γ k δ) * ((IsInsensitive.intersection D).dens : ℝ) ≤
          ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ) := by
  classical
  by_cases hlarge : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)
  · obtain ⟨V, hV⟩ := hlarge
    let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    let : DecidableEq (Fin m → Fin (k + 1)) := Classical.decEq _
    let D := fun _ : Fin k ↦ (Finset.univ : Finset (Fin m → Fin (k + 1)))
    have hD : IsInsensitive.intersection D = Finset.univ := by
      simpa only [IsInsensitive.intersection, D] using
        (Finset.inf_const (s := (Finset.univ : Finset (Fin k))) Finset.univ_nonempty
          (Finset.univ : Finset (Fin m → Fin (k + 1))))
    refine ⟨V, D, ?_, ?_, ?_⟩
    · intro i x y _
      simp only [D, Finset.mem_univ]
    · rw [hD]
      norm_num
      nlinarith [Parameters.η_le_δ_div_six k δ,
        Parameters.γ_le_η_sq_div_two k δ, Parameters.η_pos hk hδ₀,
        sq_nonneg (1 - Parameters.η k δ)]
    · rw [hD]
      norm_num
      change δ + Parameters.γ k δ ≤ (Subspace.relativeDensity V A : ℝ)
      linarith [Parameters.γ_le_η_sq_div_two k δ]
  · have hsmall : ∀ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        (Subspace.relativeDensity V A : ℝ) < δ + Parameters.η k δ ^ 2 / 2 := by
      intro V
      exact lt_of_not_ge fun hV ↦ hlarge ⟨V, hV⟩
    obtain ⟨V, C, hC, hweighted, houtside⟩ :=
      exists_large_insensitive_intersection hk hDHJ m n hm δ hδ₀ hδ₁ hm_large hn A hA
        hfree hsmall
    obtain ⟨i, hidense, hicorrelation⟩ :=
      exists_dense_firstFailurePiece hk hδ₀ hδ₁ (pullback V A) C hweighted
        houtside
    obtain ⟨hD, hintersection, _, _⟩ := firstFailureFamily_facts C hC i
    refine ⟨V, firstFailureFamily C i, hD, ?_, ?_⟩
    · rw [hintersection]
      exact hidense
    · rw [hintersection]
      exact hicorrelation

end DensityHalesJewett

end

section

/-! From DensityHalesJewett.DensityIncrement by Gabriel Dahia. -/

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- An ambient dimension supports all working dimensions needed by the density-increment
dichotomy. -/
def IncrementBoundSufficient (k d : ℕ) (δ : ℝ) (n : ℕ) : Prop :=
  ∀ (_ : 2 ≤ k), HasDensityHJ k → 1 ≤ d → 0 < δ → δ ≤ 1 →
    ∃ m, 1 ≤ m ∧
      insensitiveIntersectionDimension k δ ≤ m ∧
      manyLinesBound k m δ ≤ n ∧
      IsInsensitive.intersectionTilingBound k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m

/-- Sufficient ambient dimensions for the density-increment dichotomy occur eventually. -/
lemma exists_eventually_incrementBoundSufficient (k d : ℕ) (δ : ℝ) :
    ∃ N, ∀ n ≥ N, IncrementBoundSufficient k d δ n := by
  let m := max (max 1 (insensitiveIntersectionDimension k δ))
    (IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))))
  refine ⟨manyLinesBound k m δ, ?_⟩
  intro n hn _ _ _ _ _
  refine ⟨m, ?_, ?_, hn, ?_⟩ <;>
    dsimp only [m] <;> omega

/-- A sufficient ambient dimension for the density-increment dichotomy. -/
noncomputable def incrementBound (k d : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_eventually_incrementBoundSufficient k d δ)

/-- Select one working dimension supporting both structured correlation and the final tiling
argument.

The bound simultaneously leaves enough ambient coordinates for the many-lines construction and
makes the resulting parameter cube large enough for the insensitive-intersection construction and
for tiling that intersection by `d`-subspaces. -/
lemma incrementBound_spec {k d : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) (hd : 1 ≤ d)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {n : ℕ} (hn : incrementBound k d δ ≤ n) :
    ∃ m, 1 ≤ m ∧
      insensitiveIntersectionDimension k δ ≤ m ∧
      manyLinesBound k m δ ≤ n ∧
      IsInsensitive.intersectionTilingBound k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m := by
  classical
  unfold incrementBound at hn
  exact Nat.find_spec (exists_eventually_incrementBoundSufficient k d δ) n hn
    hk hDHJ hd hδ₀ hδ₁

/-- The insensitive-intersection tiling theorem supplies a nonempty finite family of disjoint
`d`-subspaces with small uncovered part. -/
lemma exists_finite_structured_tiling {k d m : ℕ}
    (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_tiling : IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive i.castSucc (Fin.last k) (D i))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ)) :
    ∃ 𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)),
      𝒱.Nonempty ∧
      (∀ W ∈ 𝒱, Subspace.IsContained W (IsInsensitive.intersection D)) ∧
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint fun W ↦
        (Subspace.range W : Set (Fin m → Fin (k + 1)))) ∧
      ((IsInsensitive.uncovered (η := Fin d)
        (IsInsensitive.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2 := by
  classical
  let β := Parameters.γ k δ ^ 2 / (4 * (k : ℝ))
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have hγ₁ : Parameters.γ k δ ≤ 1 := by
    linarith [Parameters.γ_le_three_mul_η k δ, Parameters.η_le_δ_div_six k δ]
  have hβ₀ : 0 < β := by positivity
  have hβ_simplify :
      2 * (k : ℝ) * β = Parameters.γ k δ ^ 2 / 2 := by
    dsimp only [β]
    field_simp
    ring
  have hDβ :
      2 * (k : ℝ) * β ≤ ((IsInsensitive.intersection D).dens : ℝ) := by
    rw [hβ_simplify]
    nlinarith
  obtain ⟨𝒱, h𝒱finite, hcontained, hpairwise, huncovered⟩ :=
    IsInsensitive.exists_disjoint_subspaces_iInter (k := k) k d m hDHJ (by omega) le_rfl hd
      β hβ₀ hm_tiling D (by
        simpa only [Fin.castLE_rfl, id_eq] using hD) hDβ
  have h𝒱nonempty : 𝒱.Nonempty := by
    by_contra h𝒱
    rw [Set.not_nonempty_iff_eq_empty.mp h𝒱] at huncovered
    have hempty :
        IsInsensitive.uncovered (η := Fin d)
          (IsInsensitive.intersection D) (∅ : Set _) =
            IsInsensitive.intersection D := by
      ext x
      simp [IsInsensitive.uncovered]
    rw [hempty, hβ_simplify] at huncovered
    nlinarith
  refine ⟨h𝒱finite.toFinset, h𝒱finite.toFinset_nonempty.mpr h𝒱nonempty, ?_, ?_, ?_⟩
  · intro W hW
    exact hcontained W (h𝒱finite.mem_toFinset.mp hW)
  · simpa only [h𝒱finite.coe_toFinset] using hpairwise
  · simpa only [h𝒱finite.coe_toFinset, hβ_simplify] using huncovered

/-- The structured correlation and the small uncovered part give an aggregate density gain over
the disjoint tile family. -/
lemma structured_tiling_density_sum {k d m n : ℕ}
    (hk : 2 ≤ k) {δ : ℝ} (hδ₀ : 0 < δ)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ))
    (hcorrelation : (δ + Parameters.γ k δ) *
        ((IsInsensitive.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (hcontained : ∀ W ∈ 𝒱, Subspace.IsContained W (IsInsensitive.intersection D))
    (hpairwise :
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint fun W ↦
      (Subspace.range W : Set (Fin m → Fin (k + 1)))))
    (huncovered :
      ((IsInsensitive.uncovered (η := Fin d)
        (IsInsensitive.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2) :
    (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ) := by
  classical
  let C := IsInsensitive.intersection D
  let P := pullback V A
  let T := 𝒱.biUnion Subspace.range
  have hTsub : T ⊆ C := by
    intro x hx
    simp only [T, Finset.mem_biUnion] at hx
    obtain ⟨W, hW, hxW⟩ := hx
    obtain ⟨z, rfl⟩ := Subspace.mem_range.mp hxW
    exact hcontained W hW z
  have hpairwise_fin :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        Subspace.range := by
    intro W hW W' hW' hne
    apply Finset.disjoint_left.mpr
    intro x hxW hxW'
    exact Set.disjoint_left.mp (hpairwise hW hW' hne) hxW hxW'
  have hsumT :
      ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) = (T.dens : ℝ) := by
    exact_mod_cast (Finset.dens_biUnion hpairwise_fin).symm
  have hpairwise_inter :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        (fun W ↦ P ∩ Subspace.range W) := by
    intro W hW W' hW' hne
    exact (hpairwise_fin hW hW' hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hinterT :
      𝒱.biUnion (fun W ↦ P ∩ Subspace.range W) = P ∩ T := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, T]
    aesop
  have hsumPT :
      ∑ W ∈ 𝒱, ((P ∩ Subspace.range W).dens : ℝ) = ((P ∩ T).dens : ℝ) := by
    rw [← hinterT]
    exact_mod_cast (Finset.dens_biUnion hpairwise_inter).symm
  have huncovered_eq : IsInsensitive.uncovered (η := Fin d) C (𝒱 : Set _) = C \ T := by
    ext x
    simp [IsInsensitive.uncovered, T]
  have hPT_eq : (P ∩ C) ∩ T = P ∩ T := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hTsub]
  have hremainder_real :
      (((P ∩ C) \ T).dens : ℝ) ≤ ((C \ T).dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens
      (Finset.sdiff_subset_sdiff Finset.inter_subset_right (subset_refl T))
  have hdecomp :
      ((P ∩ T).dens : ℝ) + (((P ∩ C) \ T).dens : ℝ) =
        ((P ∩ C).dens : ℝ) := by
    norm_cast
    simpa only [hPT_eq] using Finset.dens_inter_add_dens_sdiff (P ∩ C) T
  have hTdens : (T.dens : ℝ) ≤ (C.dens : ℝ) := by exact_mod_cast Finset.dens_le_dens hTsub
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have hcoefficient : 0 ≤ δ + Parameters.γ k δ / 2 := by linarith
  rw [hsumT, hsumPT]
  apply (mul_le_mul_of_nonneg_left hTdens hcoefficient).trans
  rw [huncovered_eq] at huncovered
  dsimp only [C, P] at hDdense hcorrelation huncovered hdecomp hremainder_real hTdens ⊢
  nlinarith

/-- Intersecting a family with a subspace range factors its ambient density into relative density
and range density. -/
lemma Subspace.dens_inter_range_eq_relativeDensity_mul_range
    {η α ι : Type*} [Fintype (η → α)] [Fintype (ι → α)]
    [DecidableEq (ι → α)]
    (W : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    ((A ∩ range W).dens : ℝ) =
      (relativeDensity W A : ℝ) * ((range W).dens : ℝ) := by
  classical
  let B := Finset.univ.filter fun x : η → α ↦ W x ∈ A
  have hAB : A ∩ range W = B.image W := by
    ext w
    simp only [B, range, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    grind
  rw [hAB]
  simp only [Finset.nnratCast_dens, relativeDensity, range, B]
  rw [Finset.card_image_iff.mpr (Subspace.injective W).injOn,
    Finset.card_image_iff.mpr (Subspace.injective W).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · let : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hB : (Finset.univ.filter fun x : η → α ↦ W x ∈ A) = ∅ :=
      Subsingleton.elim _ _
    rw [hB]
    simp
  · field_simp
    simp only [Finset.card_univ]

/-- Finite weighted averaging selects a tile whose pullback density realizes the aggregate
gain. -/
lemma exists_dense_tile_of_density_sum {k d m n : ℕ}
    {δ : ℝ} (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (h𝒱 : 𝒱.Nonempty)
    (hsum : (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) :
    ∃ W ∈ 𝒱,
      δ + Parameters.γ k δ / 2 ≤
        (Subspace.relativeDensity W (pullback V A) : ℝ) := by
  by_contra! h
  apply (not_lt_of_ge hsum)
  calc
    (∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) <
        ∑ W ∈ 𝒱, (δ + Parameters.γ k δ / 2) *
          ((Subspace.range W).dens : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty h𝒱
      intro W hW
      rw [Subspace.dens_inter_range_eq_relativeDensity_mul_range]
      apply mul_lt_mul_of_pos_right (h W hW)
      exact_mod_cast Finset.dens_pos.mpr
        ⟨W (fun _ ↦ 0), Subspace.mem_range.mpr ⟨fun _ ↦ 0, rfl⟩⟩
    _ = (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) := by
      rw [Finset.mul_sum]

/-- Relative density in a composite subspace is relative density in the inner subspace of the
outer pullback. -/
lemma Subspace.relativeDensity_compose {α η ζ ι : Type*}
    [Fintype (η → α)] [Fintype (ζ → α)] [DecidableEq (η → α)]
    [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    (relativeDensity (compose V W) A : ℝ) =
      (relativeDensity W (pullback V A) : ℝ) := by
  simp only [relativeDensity, pullback, Finset.mem_filter, Finset.mem_univ, true_and,
    compose_apply]

/-- Tile a structured insensitive intersection and extract a dense tile.

Apply `IsInsensitive.exists_disjoint_subspaces_iInter` with error
`γ² / (4k)`.  Pairwise disjointness turns the densities on the tile ranges into finite sums, and
the uncovered-density estimate preserves half of the correlation gain.  Finite averaging then
selects one `d`-tile of relative `A`-density at least `δ + γ/2`; composing that tile with `V`
gives the required ambient subspace. -/
lemma exists_density_increment_subspace_of_structured_correlation {k d m n : ℕ}
    (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_tiling : IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive i.castSucc (Fin.last k) (D i))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ))
    (hcorrelation : (δ + Parameters.γ k δ) *
        ((IsInsensitive.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
      δ + Parameters.γ k δ / 2 ≤ (Subspace.relativeDensity W A : ℝ) := by
  obtain ⟨𝒱, h𝒱, hcontained, hpairwise, huncovered⟩ :=
    exists_finite_structured_tiling hk hDHJ hd hδ₀ hδ₁ hm_tiling D hD hDdense
  obtain ⟨W, _, hW⟩ :=
    exists_dense_tile_of_density_sum A V 𝒱 h𝒱 <|
      structured_tiling_density_sum hk hδ₀ A V D hDdense hcorrelation 𝒱
        hcontained hpairwise huncovered
  refine ⟨Subspace.compose V W, ?_⟩
  rwa [Subspace.relativeDensity_compose]

/-- A dense word family either contains a line or has increased density on a prescribed-dimensional
subspace. -/
lemma density_increment {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : incrementBound k d δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        δ + Parameters.γ k δ / 2 ≤ (Subspace.relativeDensity V A : ℝ) := by
  classical
  by_cases hfree : IsLineFree A
  · obtain ⟨m, hm, hm_large, hmn, hm_tiling⟩ :=
      incrementBound_spec hk hDHJ hd hδ₀ hδ₁ hn
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let : Nonempty (Combinatorics.Line (Fin k) (Fin m)) :=
      ⟨Combinatorics.Line.diagonal (Fin k) (Fin m)⟩
    obtain ⟨V, D, hD, hDdense, hcorrelation⟩ :=
      exists_structured_correlation hk hDHJ m n hm δ hδ₀ hδ₁ hm_large hmn A hA hfree
    exact Or.inr <|
      exists_density_increment_subspace_of_structured_correlation hk hDHJ hd hδ₀ hδ₁ hm_tiling
        A V D hD hDdense hcorrelation
  · rw [IsLineFree] at hfree
    push Not at hfree
    left
    exact hfree

end DensityHalesJewett

end

section

/-! From DensityHalesJewett.Main by Gabriel Dahia. -/

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Identify a binary word with the coordinates on which it equals `1`. -/
def binarySupport {ι : Type*} [Fintype ι] (w : ι → Fin 2) : Finset ι :=
  Finset.univ.filter fun i ↦ w i = 1

/-- Two binary words are the ordered points of a combinatorial line exactly when their supports
are strictly comparable. -/
lemma binary_line_iff_ssubset {ι : Type*} [Fintype ι] (x y : ι → Fin 2) :
    (∃ l : Combinatorics.Line (Fin 2) ι, l 0 = x ∧ l 1 = y) ↔
      binarySupport x ⊂ binarySupport y := by
  have hmem : ∀ (w : ι → Fin 2) (j : ι), j ∈ binarySupport w ↔ w j = 1 := by simp [binarySupport]
  constructor
  · rintro ⟨l, rfl, rfl⟩
    obtain ⟨i, hi⟩ := l.proper
    refine (ssubset_iff_of_subset ?_).2 ⟨i, by simp [hmem, hi], by simp [hmem, hi]⟩
    intro j hj
    cases hj' : l.idxFun j <;> simp_all
  · intro h
    obtain ⟨i, hiy, hix⟩ := exists_of_ssubset h
    have hsub : ∀ j, x j = 1 → y j = 1 := by
      intro j hj
      exact (hmem y j).1 (h.1 ((hmem x j).2 hj))
    refine ⟨⟨fun j ↦ if x j = y j then some (x j) else none, i, by grind⟩, ?_, ?_⟩ <;>
      funext j <;> grind [Combinatorics.Line.coe_apply]

/-- Binary support faithfully records a binary word. -/
lemma binarySupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (binarySupport : (ι → Fin 2) → Finset ι) := by
  intro x y hxy
  funext i
  apply Fin.ext
  have hi : x i = 1 ↔ y i = 1 := by
    simpa only [binarySupport, mem_filter, mem_univ, true_and] using Finset.ext_iff.mp hxy i
  grind

/-- A squared elementary upper bound for the normalized central binomial coefficient. -/
lemma centralBinom_ratio_sq_mul_le (m : ℕ) :
    ((Nat.centralBinom m : ℝ) / 4 ^ m) ^ 2 * (3 * m + 1) ≤ 1 := by
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec : ((m + 1 : ℕ) : ℝ) * Nat.centralBinom (m + 1) =
          2 * (2 * m + 1) * Nat.centralBinom m := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ m
      have hratio : (Nat.centralBinom (m + 1) : ℝ) / 4 ^ (m + 1) =
          ((Nat.centralBinom m : ℝ) / 4 ^ m) *
            ((2 * m + 1 : ℝ) / (2 * (m + 1))) := by
        rw [pow_succ]
        field_simp
        push_cast at hrec ⊢
        linear_combination 2 * hrec
      rw [hratio, mul_pow, mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) ih
      rw [div_pow, div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity))).mpr
      push_cast
      ring_nf
      nlinarith

/-- The middle binomial coefficient is at most the reciprocal square-root proportion of the
Boolean cube. -/
lemma centralBinom_ratio_le_inv_sqrt (m : ℕ) :
    (Nat.centralBinom m : ℝ) / 4 ^ m ≤ (√(3 * m + 1))⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (Real.sqrt_pos.2 (by positivity)),
    ← sq_le_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  simpa only [one_pow] using centralBinom_ratio_sq_mul_le m

/-- The two normalizations of the binomial denominator, one per half-dimension and one per
dimension, agree. -/
private lemma two_pow_two_mul (m : ℕ) : (2 : ℝ) ^ (2 * m) = 4 ^ m := by
  rw [pow_mul]
  norm_num

/-- Reduce the normalized middle binomial coefficient in any dimension to the central coefficient
in half that dimension. -/
lemma middleBinomial_ratio_le_central (n : ℕ) :
    (n.choose (n / 2) : ℝ) / 2 ^ n ≤
      (Nat.centralBinom (n / 2) : ℝ) / 4 ^ (n / 2) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    have hdiv : 2 * m / 2 = m := by grind
    rw [hdiv, Nat.centralBinom, two_pow_two_mul]
  · subst n
    have hdiv : (2 * m + 1) / 2 = m := by grind
    rw [hdiv, Nat.centralBinom]
    cases m with
    | zero => norm_num
    | succ m =>
      have hchoose : (2 * (m + 1) + 1).choose (m + 1) ≤
          2 * Nat.centralBinom (m + 1) := by
        rw [Nat.choose_succ_left (2 * (m + 1)) (m + 1) (by grind)]
        simpa only [Nat.add_sub_cancel, two_mul] using
          add_le_add (Nat.choose_le_centralBinom m (m + 1))
            (Nat.choose_le_centralBinom (m + 1) (m + 1))
      rw [pow_succ, two_pow_two_mul, mul_comm (4 ^ (m + 1) : ℝ) 2]
      apply le_trans (b := (2 * Nat.centralBinom (m + 1) : ℝ) /
        (2 * 4 ^ (m + 1)))
      · exact (div_le_div_iff_of_pos_right
          (by positivity : (0 : ℝ) < 2 * 4 ^ (m + 1))).mpr <| by
            exact_mod_cast hchoose
      · field_simp
        rfl

/-- Eventually the middle layer occupies less than any prescribed positive proportion of the
Boolean cube. -/
lemma exists_middleBinomial_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → (n.choose (n / 2) : ℝ) < δ * 2 ^ n := by
  have ht : Filter.Tendsto (fun m : ℕ ↦ (√(3 * (m : ℝ) + 1))⁻¹)
      Filter.atTop (nhds 0) := by
    apply tendsto_inv_atTop_zero.comp
    apply Real.tendsto_sqrt_atTop.comp
    simpa only [add_comm] using
      tendsto_const_nhds.add_atTop
        ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ))
          Filter.atTop Filter.atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hδ)
  refine ⟨2 * M, ?_⟩
  intro n hn
  have hMn : M ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by grind)
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp
  apply (middleBinomial_ratio_le_central n).trans_lt
  apply (centralBinom_ratio_le_inv_sqrt (n / 2)).trans_lt
  exact hM (n / 2) hMn

/-- Density Hales--Jewett for the binary alphabet. -/
lemma dhj_two : HasDensityHJ 2 := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_middleBinomial_lt δ hδ
  refine ⟨N, ?_⟩
  intro n hn A hA
  by_contra hline
  let B := A.image binarySupport
  have hB : IsAntichain (· ⊆ ·) (B : Set (Finset (Fin n))) := by
    intro s hs t ht hst hsub
    change s ∈ B at hs
    change t ∈ B at ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    apply hline
    obtain ⟨l, hlx, hly⟩ := (binary_line_iff_ssubset x y).2 <|
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, hst⟩
    refine ⟨l, ?_⟩
    intro a
    obtain rfl | ⟨i, rfl⟩ := a.eq_zero_or_eq_succ
    · rw [hlx]
      exact hx
    · simp only [Fin.eq_zero i]
      change l 1 ∈ A
      rwa [hly]
  have hcard : #A ≤ n.choose (n / 2) := by
    rw [← Finset.card_image_of_injective A binarySupport_injective]
    simpa only [B, Fintype.card_fin] using hB.sperner
  exact (not_lt_of_ge (hA.trans <| by exact_mod_cast hcard)) (hN n hn)

/-- A positive uniform increment eventually raises the density floor above one. -/
lemma exists_density_increment_steps {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 1 < δ + (R : ℝ) * (Parameters.γ k δ / 2) := by
  refine ⟨⌈2 / (Parameters.γ k δ)⌉₊ + 1, ?_⟩
  refine lt_trans (?_) (lt_add_of_pos_left _ hδ)
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ zero_lt_two).2
  simp only [one_mul]
  apply (div_lt_iff₀ (Parameters.γ_pos hk hδ)).1
  apply lt_of_le_of_lt (Nat.ceil_le.mp le_rfl) (by grind)

/-- Choose the dimensions for a finite density-increment iteration backwards.

The last parameter cube has dimension one.  At stage `j`, the preceding dimension is large enough
to apply `density_increment` with density floor `δ + j * (γ k δ / 2)` and target dimension
`d (j + 1)`. -/
lemma exists_density_increment_schedule (k R : ℕ) (δ : ℝ) :
    ∃ d : ℕ → ℕ,
      d R = 1 ∧
      (∀ j, j ≤ R → 1 ≤ d j) ∧
      ∀ j, j < R →
        incrementBound k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j := by
  let γ := Parameters.γ k δ
  let d_aux : ℕ → ℕ :=
    Nat.rec 1 (fun t d_t => max 1 (incrementBound k d_t (δ + ((R - (t + 1) : ℕ) : ℝ) * (γ / 2))))
  let d : ℕ → ℕ := fun j => d_aux (R - j)
  have h_aux_succ (t : ℕ) : d_aux (t + 1) =
      max 1 (incrementBound k (d_aux t) (δ + ((R - (t + 1) : ℕ) : ℝ) * (γ / 2))) := rfl
  have h_aux_one (t : ℕ) : 1 ≤ d_aux t := by
    induction t with
    | zero => simp [d_aux]
    | succ t ih => rw [h_aux_succ t]; exact le_max_left _ _
  have h_d_R : d R = 1 := by
    dsimp [d, d_aux]
    simp
  have h_d_one (j : ℕ) (hj : j ≤ R) : 1 ≤ d j := by
    dsimp [d]
    exact h_aux_one (R - j)
  have h_d_step (j : ℕ) (hj : j < R) :
      incrementBound k (d (j + 1)) (δ + (j : ℝ) * (γ / 2)) ≤ d j := by
    have h_sub : R - j = (R - (j + 1)) + 1 := by omega
    have h_index : (R - ((R - (j + 1) : ℕ) + 1) : ℕ) = j := by omega
    dsimp [d]
    rw [h_sub, h_aux_succ (R - (j + 1)), h_index]
    exact le_max_right _ _
  exact ⟨d, h_d_R, h_d_one, h_d_step⟩

/-- Split the first `m` coordinates from the remaining coordinates of `Fin n`. -/
def prefixCoordinateEquiv {m n : ℕ} (hmn : m ≤ n) : Fin m ⊕ Fin (n - m) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hmn))

/-- Assemble a word from its first `m` coordinates and a fixed remaining suffix. -/
def prefixCoordinateWord {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (x : Fin m → α) (y : Fin (n - m) → α) : Fin n → α :=
  Sum.elim x y ∘ (prefixCoordinateEquiv hmn).symm

/-- The coordinate subspace obtained by fixing every coordinate after the first `m`. -/
def prefixCoordinateSubspace {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (y : Fin (n - m) → α) : Combinatorics.Subspace (Fin m) α (Fin n) where
  idxFun i := ((prefixCoordinateEquiv hmn).symm i).elim Sum.inr (Sum.inl ∘ y)
  proper e := by
    refine ⟨prefixCoordinateEquiv hmn (Sum.inl e), ?_⟩
    simp only [Equiv.symm_apply_apply, Sum.elim_inl]

@[simp]
lemma prefixCoordinateSubspace_apply {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (y : Fin (n - m) → α) (x : Fin m → α) :
    prefixCoordinateSubspace hmn y x = prefixCoordinateWord hmn x y := by
  funext i
  change (((prefixCoordinateEquiv hmn).symm i).elim Sum.inr (Sum.inl ∘ y)).elim id x =
    Sum.elim x y ((prefixCoordinateEquiv hmn).symm i)
  cases (prefixCoordinateEquiv hmn).symm i <;> rfl

/-- Some fixed suffix leaves a first-coordinate fiber at least as dense as the ambient family. -/
lemma exists_dense_prefixCoordinateWord {k m n : ℕ} (hmn : m ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) :
    ∃ y : Fin (n - m) → Fin (k + 1),
      (A.dens : ℝ) ≤
        ((Finset.univ.filter fun x : Fin m → Fin (k + 1) ↦
          prefixCoordinateWord hmn x y ∈ A).dens : ℝ) := by
  let eCoord := (Equiv.sumComm (Fin (n - m)) (Fin m)).trans (prefixCoordinateEquiv hmn)
  let eWord := eCoord.arrowCongr (Equiv.refl (Fin (k + 1)))
  let A' := A.map eWord.symm.toEmbedding
  have hA' : (A'.dens : ℝ) = (A.dens : ℝ) := by
    simp only [A', Finset.dens_map_equiv]
  have havg :
      (A.dens : ℝ) ≤ Finset.expect Finset.univ (fun y : Fin (n - m) → Fin (k + 1) ↦
        ((fiber A' y).dens : ℝ)) := by
    rw [average_density_fiber, hA']
  obtain ⟨y, _, hy⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty havg
  refine ⟨y, ?_⟩
  have hword (x : Fin m → Fin (k + 1)) :
      eWord (Sum.elim y x) = prefixCoordinateWord hmn x y := by
    funext i
    cases h : (prefixCoordinateEquiv hmn).symm i <;>
      simp [eWord, eCoord, prefixCoordinateWord, Equiv.arrowCongr, Sum.elim, h,
        Function.comp_apply]
  have hfiber : fiber A' y = Finset.univ.filter fun x : Fin m → Fin (k + 1) ↦
      prefixCoordinateWord hmn x y ∈ A := by
    ext x
    simp only [mem_fiber, Finset.mem_filter, Finset.mem_univ, true_and, A',
      Finset.mem_map_equiv, Equiv.symm_symm]
    rw [hword]
  rwa [← hfiber]

/-- A coordinate fiber of any prescribed smaller dimension has relative density at least the
ambient density. -/
lemma exists_density_preserving_subspace_of_le {k m n : ℕ} (hmn : m ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (A.dens : ℝ) ≤ (Subspace.relativeDensity V A : ℝ) := by
  obtain ⟨y, hy⟩ := exists_dense_prefixCoordinateWord hmn A
  refine ⟨prefixCoordinateSubspace hmn y, ?_⟩
  simpa only [Subspace.relativeDensity, prefixCoordinateSubspace_apply] using hy

/-- One scheduled density-increment stage either produces an ambient line or advances the nested
subspace while preserving the quantitative density invariant. -/
lemma density_increment_chain_step {k R n j : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) {δ : ℝ} (hδ : 0 < δ)
    (d : ℕ → ℕ) (hd : ∀ t, t ≤ R → 1 ≤ d t)
    (hstep : ∀ t, t < R →
      incrementBound k (d (t + 1))
        (δ + (t : ℝ) * (Parameters.γ k δ / 2)) ≤ d t)
    (hj : j < R) (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n))
    (hV : δ + (j : ℝ) * (Parameters.γ k δ / 2) ≤
      (Subspace.relativeDensity V A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ W : Combinatorics.Subspace (Fin (d (j + 1))) (Fin (k + 1)) (Fin n),
        δ + ((j + 1 : ℕ) : ℝ) * (Parameters.γ k δ / 2) ≤
          (Subspace.relativeDensity W A : ℝ) := by
  let : Nontrivial (Fin (k + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  let ρ := δ + (j : ℝ) * (Parameters.γ k δ / 2)
  have hγ := Parameters.γ_mono_lowerBound hk hδ
  have hρ₀ : 0 < ρ := by
    dsimp only [ρ]
    nlinarith [hγ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  have hρ₁ : ρ ≤ 1 := hV.trans (by exact_mod_cast Finset.dens_le_one (s := pullback V A))
  have hinc := density_increment hk hDHJ (d (j + 1))
    (hd (j + 1) (Nat.succ_le_of_lt hj)) ρ hρ₀ hρ₁ (d j) (hstep j hj)
      (pullback V A) (by
        simpa only [ρ, Subspace.relativeDensity, pullback] using hV)
  obtain ⟨l, hl⟩ | ⟨U, hU⟩ := hinc
  · left
    use Subspace.mapLine V l
    intro a
    simpa only [Subspace.mapLine_apply, pullback, Finset.mem_filter, Finset.mem_univ,
      true_and] using hl a
  · right
    use Subspace.compose V U
    rw [Subspace.relativeDensity_compose]
    dsimp only [ρ] at hU
    have hδρ : δ ≤ δ + (j : ℝ) * (Parameters.γ k δ / 2) := by
      nlinarith [hγ.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
    norm_num [Nat.cast_add, Nat.cast_one]
    linarith [hγ.2 _ hδρ]

/-- Iterating the one-step lemma along the schedule either finds a line or reaches the last
scheduled subspace with the accumulated density lower bound. -/
lemma line_or_density_increment_chain {k R n : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) {δ : ℝ} (hδ : 0 < δ)
    (d : ℕ → ℕ) (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (hstep : ∀ j, j < R →
      incrementBound k (d (j + 1))
        (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j)
    (A : Finset (Fin n → Fin (k + 1)))
    (V₀ : Combinatorics.Subspace (Fin (d 0)) (Fin (k + 1)) (Fin n))
    (hV₀ : δ ≤ (Subspace.relativeDensity V₀ A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin (d R)) (Fin (k + 1)) (Fin n),
        δ + (R : ℝ) * (Parameters.γ k δ / 2) ≤
          (Subspace.relativeDensity V A : ℝ) := by
  suffices ∀ j, j ≤ R →
      (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
        ∃ V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n),
          δ + (j : ℝ) * (Parameters.γ k δ / 2) ≤
            (Subspace.relativeDensity V A : ℝ) by
    exact this R le_rfl
  intro j hj
  induction j with
  | zero =>
      right
      exact ⟨V₀, by simpa only [Nat.cast_zero, zero_mul, add_zero] using hV₀⟩
  | succ j ih =>
      obtain hline | ⟨V, hV⟩ := ih (Nat.le_of_succ_le hj)
      · left
        exact hline
      · exact density_increment_chain_step hk hDHJ hδ d hd hstep
          (Nat.lt_of_succ_le hj) A V hV

/-- Iterate the density-increment dichotomy along a backward dimension schedule.

Pull back the family after each increment and compose the resulting nested subspaces.  A line in
any parameter cube gives a line in the original family.  Otherwise monotonicity of `Parameters.γ`
raises the density by at least `Parameters.γ k δ / 2` at every stage, and the final relative
density is at most one. -/
lemma line_or_iterated_density_le_one {k R n : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    {δ : ℝ} (hδ : 0 < δ) (d : ℕ → ℕ)
    (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (hstep : ∀ j, j < R →
      incrementBound k (d (j + 1)) (δ + (j : ℝ) * (Parameters.γ k δ / 2)) ≤ d j)
    (hn : d 0 ≤ n) (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      δ + (R : ℝ) * (Parameters.γ k δ / 2) ≤ 1 := by
  obtain ⟨V₀, hV₀⟩ :=
    exists_density_preserving_subspace_of_le hn A
  obtain hline | ⟨V, hV⟩ :=
    line_or_density_increment_chain hk hDHJ hδ d hd hstep A V₀ (hA.trans hV₀)
  · left
    exact hline
  · right
    exact hV.trans (mod_cast Finset.dens_le_one (s := pullback V A))

/-- Density Hales--Jewett for every finite alphabet of cardinality at least two. -/
lemma density_hales_jewett_fin (k : ℕ) (hk : 2 ≤ k) : HasDensityHJ k := by
  induction k, hk using Nat.le_induction with
  | base => exact dhj_two
  | succ k hk hDHJ =>
      intro δ hδ
      obtain ⟨R, hR⟩ := exists_density_increment_steps hk hδ
      obtain ⟨d, _, hd, hstep⟩ := exists_density_increment_schedule k R δ
      refine ⟨d 0, ?_⟩
      intro n hn A hA
      refine (line_or_iterated_density_le_one hk hDHJ hδ d hd hstep hn A ?_).resolve_right ?_
      · exact Subspace.density_le_of_card_le (Nat.zero_lt_succ k) δ A hA
      · exact not_le_of_gt hR

end DensityHalesJewett

namespace Combinatorics.Line

/-- A threshold for the density Hales--Jewett theorem over an alphabet of size `k`. -/
noncomputable def densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ :=
  if 2 ≤ k then DensityHalesJewett.Subspace.densityOneBound k δ else 1

/-- The density theorem for alphabets with at most one letter. -/
lemma exists_of_density_card_le_one (α : Type*) [Fintype α]
    (hα : Fintype.card α ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : 1 ≤ n) (A : Finset (Fin n → α))
    (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hα
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨Line.diagonal α (Fin n), ?_⟩
  intro x
  have hcard : Fintype.card α = 1 :=
    Fintype.card_eq_one_of_forall_eq fun y ↦ Subsingleton.elim y x
  rw [hcard] at hAδ
  norm_num at hAδ
  obtain ⟨w, hw⟩ : A.Nonempty := Finset.card_pos.mp <| by
    exact_mod_cast hδ.trans_le hAδ
  simpa only [Subsingleton.elim (Line.diagonal α (Fin n) x) w] using hw

/-- Transport the finite-alphabet density theorem across the canonical alphabet equivalence. -/
lemma exists_of_density_card_ge_two (α : Type*) [Fintype α]
    (hα : 2 ≤ Fintype.card α) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : DensityHalesJewett.Subspace.densityOneBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  classical
  let e := Fintype.equivFin α
  let wordEquiv : (Fin n → α) ≃ (Fin n → Fin (Fintype.card α)) :=
    (Equiv.refl (Fin n)).arrowCongr e
  let B := A.map wordEquiv.toEmbedding
  have hB : δ * (Fintype.card α : ℝ) ^ n ≤ #B := by
    simpa only [B, Finset.card_map] using hAδ
  obtain ⟨l, hl⟩ := DensityHalesJewett.Subspace.densityOneBound_spec
    (DensityHalesJewett.density_hales_jewett_fin (Fintype.card α) hα)
    δ hδ n hn B hB
  refine ⟨l.map e.symm, ?_⟩
  intro x
  specialize hl (e x)
  rw [Finset.mem_map_equiv] at hl
  change (e.symm ∘ l (e x)) ∈ A at hl
  rwa [← e.symm_apply_apply x, Combinatorics.Line.map_apply]

lemma densityTheoremBound_spec (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  by_cases hα : 2 ≤ Fintype.card α
  · refine exists_of_density_card_ge_two α hα δ hδ n ?_ A hAδ
    simpa only [densityTheoremBound, if_pos hα] using hn
  · refine exists_of_density_card_le_one α (by grind) δ hδ n ?_ A hAδ
    simpa only [densityTheoremBound, if_neg hα] using hn

theorem exists_of_density (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound (Fintype.card α) δ ≤ n)
    (A : Finset (Fin n → α)) (hAδ : δ * (Fintype.card α : ℝ) ^ n ≤ #A) :
    ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A :=
  densityTheoremBound_spec α δ hδ n hn A hAδ

end Combinatorics.Line

end

section

/-! From DensityHalesJewett.Szemeredi by Gabriel Dahia. -/

open Finset
open Combinatorics

namespace Combinatorics

/-- A nonconstant arithmetic progression of length `k` in an additive monoid. -/
structure ArithmeticProgression (α : Type*) [AddMonoid α] (k : ℕ) where
  /-- The initial term of the arithmetic progression. -/
  start : α
  /-- The common difference of the arithmetic progression. -/
  diff : α
  diff_ne_zero : diff ≠ 0

namespace ArithmeticProgression

/-- The term of `P` indexed by `i`. -/
def term {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (i : Fin k) : α :=
  P.start + (i : ℕ) • P.diff

/-- The proposition that every term of `P` belongs to `s`. -/
def IsSubset {α : Type*} [AddMonoid α] {k : ℕ} (P : ArithmeticProgression α k)
    (s : Set α) : Prop :=
  ∀ i, P.term i ∈ s

end ArithmeticProgression
end Combinatorics

namespace DensityHalesJewett

namespace Line

/-- A base-encoded combinatorial line is a nonconstant arithmetic progression.  The encoding is
mathlib's `finFunctionFinEquiv`, which reads a word as the base-`k` digits of a natural number. -/
lemma baseEncode_isArithmeticProgression {k m : ℕ} (hk : 1 ≤ k)
    (l : Combinatorics.Line (Fin k) (Fin m)) :
    ∃ P : Combinatorics.ArithmeticProgression ℕ k,
      ∀ a, P.term a = (finFunctionFinEquiv (l a) : ℕ) := by
  let d := ∑ i : Fin m, if l.idxFun i = none then k ^ (i : ℕ) else 0
  refine ⟨
    { start := (finFunctionFinEquiv (l ⟨0, hk⟩) : ℕ)
      diff := d
      diff_ne_zero := ?_ }, ?_⟩
  · refine Nat.ne_of_gt (Finset.sum_pos' ?_ ?_)
    · intro i _
      exact Nat.zero_le _
    · obtain ⟨i, hi⟩ := l.proper
      exact ⟨i, Finset.mem_univ i, by simp [hi, Nat.zero_lt_of_lt hk]⟩
  · intro a
    change (finFunctionFinEquiv (l ⟨0, hk⟩) : ℕ) + (a : ℕ) • d
      = (finFunctionFinEquiv (l a) : ℕ)
    simp only [finFunctionFinEquiv_apply]
    rw [nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hli : l.idxFun i <;> simp [Combinatorics.Line.coe_apply, hli]

end Line

/-- A sufficiently dense initial interval has a complete digit block with at least half the
ambient density. -/
lemma exists_dense_digitBlock {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 2 * K / δ ≤ N) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : δ * N ≤ #A) :
    ∃ q : ℕ, (q + 1) * K ≤ N ∧
      δ / 2 * K ≤ #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
  let Q := N / K
  let S := A ∩ Finset.range (Q * K)
  have htail : (#(A \ Finset.range (Q * K)) : ℝ) < K := by
    norm_cast
    refine (Finset.card_le_card (t := Finset.Ico (Q * K) N) ?_).trans_lt ?_
    · intro x hx
      rw [Finset.mem_Ico]
      rw [Finset.mem_sdiff, Finset.mem_range] at hx
      exact ⟨Nat.le_of_not_gt hx.2, Finset.mem_range.mp (hAN hx.1)⟩
    · rw [Nat.card_Ico]
      simpa only [Q, Nat.mod_eq_sub_mul_div, Nat.mul_comm] using
        Nat.mod_lt N (Nat.zero_lt_of_lt hK)
  have hS : δ / 2 * N ≤ (#S : ℝ) := by
    rw [← Finset.card_inter_add_card_sdiff A (Finset.range (Q * K))] at hA
    push_cast at hA
    dsimp only [S]
    nlinarith [htail, (div_le_iff₀ hδ).mp hN]
  have hmap : ∀ x ∈ S, x / K ∈ Finset.range Q := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_range] at hx
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).2 hx.2)
  obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ Finset.range Q,
      δ / 2 * K ≤ ∑ x ∈ S with x / K = q, (1 : ℝ) := by
    apply Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (M := ℝ) (s := S) (t := Finset.range Q) (f := fun x ↦ x / K)
      (w := fun _ ↦ 1) (b := δ / 2 * K) hmap
    · obtain ⟨x, hx⟩ : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hSempty
        rw [hSempty, Finset.card_empty, Nat.cast_zero] at hS
        exact not_lt_of_ge hS (mul_pos (by positivity) (lt_of_lt_of_le (by positivity) hN))
      exact ⟨x / K, hmap x hx⟩
    · simp only [Finset.card_range, nsmul_eq_mul, Finset.sum_const, mul_one]
      refine le_trans ?_ hS
      rw [← mul_assoc, mul_comm (Q : ℝ) (δ / 2), mul_assoc]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.div_mul_le_self N K) (by positivity)
  refine ⟨q, ?_, ?_⟩
  · exact (Nat.mul_le_mul_right K (Nat.succ_le_iff.mp (Finset.mem_range.mp hqQ))).trans
      (Nat.div_mul_le_self N K)
  · convert hq using 1
    norm_cast
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    ext x
    dsimp only [S]
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hxA, hxlo, hxhi⟩
      refine ⟨⟨hxA, hxhi.trans_le ?_⟩, ?_⟩
      · exact Nat.mul_le_mul_right K
          (Nat.succ_le_iff.mp (Finset.mem_range.mp hqQ))
      · apply Nat.le_antisymm
        · exact Nat.lt_succ_iff.mp
            ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).2 hxhi)
        · exact (Nat.le_div_iff_mul_le (Nat.zero_lt_of_lt hK)).2 hxlo
    · rintro ⟨⟨hxA, _⟩, hxq⟩
      refine ⟨hxA, ?_, ?_⟩
      · rw [← hxq]
        simpa [Nat.mul_comm] using Nat.mul_div_le x K
      · rw [← hxq]
        exact (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hK)).mp (Nat.lt_succ_self _)

end DensityHalesJewett

namespace Combinatorics.ArithmeticProgression

/-- A threshold for the density theorem for arithmetic progressions of length `k`. -/
noncomputable def densityTheoremBound (k : ℕ) (δ : ℝ) : ℕ :=
  ⌈2 * (k ^ Combinatorics.Line.densityTheoremBound k (δ / 2) : ℕ) / δ⌉₊

theorem exists_of_density_nat (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : densityTheoremBound k δ ≤ n) (A : Finset ℕ)
    (hAn : A ⊆ range n) (hAδ : δ * n ≤ #A) :
    ∃ P : ArithmeticProgression ℕ k, P.IsSubset (A : Set ℕ) := by
  classical
  have hk_one : 1 ≤ k := by grind
  let m := Combinatorics.Line.densityTheoremBound k (δ / 2)
  let K := k ^ m
  obtain ⟨q, _, hqA⟩ : ∃ q : ℕ, (q + 1) * K ≤ n ∧
      δ / 2 * K ≤ #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
    refine DensityHalesJewett.exists_dense_digitBlock (one_le_pow₀ hk_one) hδ ?_ A hAn hAδ
    · apply Nat.le_of_ceil_le
      simpa only [densityTheoremBound, m, K] using hn
  let encode (x : Fin m → Fin k) := q * K + (finFunctionFinEquiv x : ℕ)
  let B := Finset.univ.filter fun x : Fin m → Fin k ↦ encode x ∈ A
  let encodeOnB (x : Fin m → Fin k) (_ : x ∈ B) := encode x
  have hBcard : #B = #(A ∩ Finset.Ico (q * K) ((q + 1) * K)) := by
    apply Finset.card_bij encodeOnB
    · intro x hx
      dsimp only [encodeOnB, encode]
      rw [Finset.mem_filter] at hx
      refine Finset.mem_inter.mpr ⟨hx.2, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, ?_⟩⟩
      rw [add_mul, one_mul]
      apply Nat.add_lt_add_left
      exact (finFunctionFinEquiv x).isLt
    · intro x _ y _ hxy
      dsimp only [encodeOnB, encode] at hxy
      exact finFunctionFinEquiv.injective (Fin.ext (Nat.add_left_cancel hxy))
    · intro y hy
      rw [Finset.mem_inter, Finset.mem_Ico] at hy
      have hz : y - q * K < K := by
        rw [Nat.sub_lt_iff_lt_add hy.2.1]
        simpa only [add_mul, one_mul, Nat.add_comm] using hy.2.2
      let z : Fin K := ⟨y - q * K, hz⟩
      let x := finFunctionFinEquiv.symm z
      have hxencode : (finFunctionFinEquiv x : ℕ) = y - q * K :=
        congrArg Fin.val (Equiv.apply_symm_apply finFunctionFinEquiv z)
      dsimp only [encodeOnB, encode]
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · dsimp only [encode]
        rw [hxencode, Nat.add_sub_of_le hy.2.1]
        exact hy.1
      · rw [hxencode, Nat.add_sub_of_le hy.2.1]
  obtain ⟨l, hl⟩ : ∃ l : Combinatorics.Line (Fin k) (Fin m), ∀ x : Fin k, l x ∈ B := by
    apply Combinatorics.Line.exists_of_density (Fin k) (δ / 2)
    · positivity
    · simp [m]
    · rw [Fintype.card_fin, hBcard]
      simpa only [K, Nat.cast_pow] using hqA
  obtain ⟨P, hP⟩ := DensityHalesJewett.Line.baseEncode_isArithmeticProgression hk_one l
  refine ⟨
    { start := q * K + P.start
      diff := P.diff
      diff_ne_zero := P.diff_ne_zero }, ?_⟩
  intro a
  change (q * K + P.start) + (a : ℕ) • P.diff ∈ A
  rw [add_assoc]
  change q * K + P.term a ∈ A
  rw [hP]
  exact (Finset.mem_filter.mp (hl a)).2

end Combinatorics.ArithmeticProgression

end

section

/-! From DensityHalesJewett.Challenge by Gabriel Dahia. -/

open Filter Finset
open Combinatorics

namespace Combinatorics.Line

/-- **Density Hales--Jewett theorem**: for a positive density `δ`, every sufficiently long word
length `n` has the property that any set of at least a `δ` fraction of the words of length `n`
over `α` contains a combinatorial line. -/
theorem exists_of_density_atTop (α : Type*) [Fintype α] (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset (Fin n → α), δ * (Fintype.card α : ℝ) ^ n ≤ #A →
      ∃ l : Line α (Fin n), ∀ x : α, l x ∈ A := by
  refine eventually_atTop.2 ⟨densityTheoremBound (Fintype.card α) δ, ?_⟩
  intro n hn A hAδ
  exact exists_of_density α δ hδ n hn A hAδ

end Combinatorics.Line

/-- **Szemeredi's theorem**: for a positive density `δ`, every sufficiently large `n` has the
property that any subset of `range n` of size at least `δ * n` contains an arithmetic progression
of length `k`, i.e. `k` terms `a, a + d, a + 2 * d, …` with `d ≠ 0`. -/
theorem exists_of_density_nat_atTop (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ A : Finset ℕ, A ⊆ range n → δ * n ≤ #A →
      ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A := by
  refine eventually_atTop.2 ⟨Combinatorics.ArithmeticProgression.densityTheoremBound k δ, ?_⟩
  intro n hn A hAn hAδ
  obtain ⟨P, hP⟩ :=
    Combinatorics.ArithmeticProgression.exists_of_density_nat k hk δ hδ n hn A hAn hAδ
  refine ⟨P.start, P.diff, P.diff_ne_zero, ?_⟩
  intro i
  simpa [Combinatorics.ArithmeticProgression.term, nsmul_eq_mul] using hP i

end

open Filter Asymptotics
open scoped Pointwise Topology

namespace GreenGap

/-- A positive-density set of missing representatives contains a progression. Its
step lies strictly between zero and the prime, so its inverse straightens the
progression into an interval in the dilated complement. -/
private theorem gap_of_dense_complement {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k)
    {δ : ℝ}
    (hsz : ∀ S : Finset ℕ, S ⊆ Finset.range p → δ * p ≤ S.card →
      ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ S)
    (A : Finset (ZMod p)) (hden : δ * p ≤ (p : ℝ) - A.card)
    {L : ℕ} (hL : L ≤ k) :
    ∃ u : (ZMod p)ˣ, Green32.HasGap (u • A) L := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let S := Aᶜ.map ⟨ZMod.val, ZMod.val_injective p⟩
  have hS : ∀ n ∈ S, n < p ∧ (n : ZMod p) ∉ A := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
    exact ⟨ZMod.val_lt x, by simpa using hx⟩
  have hcard : S.card + A.card = p := by
    simpa [S, ZMod.card] using A.card_compl_add_card
  have hcardR : (S.card : ℝ) + A.card = p := by exact_mod_cast hcard
  obtain ⟨a, d, hd, hAP⟩ := hsz S
    (fun n hn ↦ Finset.mem_range.mpr (hS n hn).1) (by linarith)
  have hstep : a + d < p := by
    simpa using (hS _ (hAP ⟨1, by omega⟩)).1
  have hunit : (d : ZMod p) ≠ 0 := by
    intro h
    have hpd := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) ((ZMod.natCast_eq_zero_iff d p).mp h)
    omega
  let u : (ZMod p)ˣ := Units.mk0 (d : ZMod p) hunit
  refine ⟨u⁻¹, u⁻¹ • (a : ZMod p), ?_⟩
  intro i hi hmem
  have hmiss := (hS _ (hAP ⟨i, hi.trans_le hL⟩)).2
  apply hmiss
  have h := Finset.mem_inv_smul_finset_iff.mp hmem
  rw [smul_add, smul_inv_smul] at h
  simpa [u, Units.smul_def, Nat.cast_add, Nat.cast_mul, mul_comm] using h

end GreenGap

/-- Apply finite Szemerédi to the missing fraction (1-c)/2. For sufficiently
large p the target gap is at most 200/c, uniformly in p. -/
theorem OMA.solution : type_of% @Green32.green_32.variants.szemeredi_regime := by
  intro c hc ω hω
  obtain ⟨hc0, hc1⟩ := hc
  let δ := (1 - c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let k := max 3 ⌈200 / c⌉₊
  have hk : 3 ≤ k := le_max_left _ _
  obtain ⟨φ, hφ, heq⟩ := hω.exists_eq_mul
  have hr : Tendsto (fun n ↦ φ n * c) atTop (𝓝 c) := by
    simpa using hφ.mul_const c
  have hlo := hr.eventually_const_lt (show c / 2 < c by linarith)
  have hhi := hr.eventually_lt_const (show c < (1 + c) / 2 by linarith)
  have hg : Tendsto ω atTop atTop :=
    hω.symm.tendsto_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hc0)
  unfold Green32.HasLargeGapDilate
  filter_upwards [exists_of_density_nat_atTop k hk δ hδ, heq, hlo, hhi,
    hg.eventually (eventually_gt_atTop (100 : ℝ))] with p hsz hpEq hl hu h100
  intro hp
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  change ω p = φ p * (c * (p : ℝ)) at hpEq
  have hlow : c / 2 * (p : ℝ) ≤ ω p := by
    rw [hpEq, ← mul_assoc]
    exact (mul_lt_mul_of_pos_right hl hpR).le
  have hupp : ω p < (1 + c) / 2 * (p : ℝ) := by
    rw [hpEq, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hu hpR
  have hwp : ω p < (p : ℝ) := hupp.trans <| by
    simpa using mul_lt_mul_of_pos_right (show (1 + c) / 2 < 1 by linarith) hpR
  refine ⟨h100, hwp, ?_⟩
  intro A hA
  have homega : 0 < ω p := by linarith
  have hcard : (A.card : ℝ) ≤ ω p := by rw [hA]; exact Nat.floor_le homega.le
  have hlen : ⌊100 * (p : ℝ) / ω p⌋₊ ≤ k := by
    apply le_trans (Nat.floor_mono (b := 200 / c) ?_) ((Nat.floor_le_ceil _).trans (le_max_right _ _))
    apply (div_le_div_iff₀ homega hc0).mpr
    nlinarith
  exact GreenGap.gap_of_dense_complement hp hk hsz A (by dsimp [δ]; linarith) hlen
