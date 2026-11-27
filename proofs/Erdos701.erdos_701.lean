import FormalConjectures.ErdosProblems.«701»
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.UpperLower.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-
Chvátal's conjecture (Erdős problem 701).
Mathematical proof: Fan Chang, Hong Liu and Miao Liu, arXiv:2609.19123.
Lean formalisation: Chvatal formalization contributors, boonsuan/chvatal
(MIT; see upstream commit and permission notice below).
Port source: LeanPool/lean-pool @ 701389c04bdd56aabf8dbb9ad729165fdba772b5 (Apache-2.0).
Modified: adapted to formal-conjectures' pinned Mathlib and inlined into one
file for Left to Solve.

Applicable Lean Pool NOTICE attribution:

Lean Pool
=========

Copyright the Lean Pool contributors and the respective project authors.

Lean Pool is licensed under the Apache License, Version 2.0. See the LICENSE
file for the full license text.

Lean Pool is an aggregation of third-party Lean 4 formalizations. Each project
under LeanPool/ is the work of its original authors, who retain copyright as
recorded in the per-file headers and in the project registry. This NOTICE file
records, for every pooled project, the upstream repository it was imported from
and the license under which it was originally published.

--------------------------------------------------------------------------------
Projects originally licensed under the MIT License
--------------------------------------------------------------------------------

These projects were imported from repositories licensed under the MIT License.
The MIT License grants the right to sublicense, so these projects are
redistributed here under the Apache License, Version 2.0. As the MIT License
requires, the original copyright notices are preserved below, together with the
MIT permission notice that follows them.

  LeanPool/Chvatal                   https://github.com/boonsuan/chvatal

Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Apache License, Version 2.0 (Lean Pool LICENSE):
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      “License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      “Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      “Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      “control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      “You” (or “Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      “Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      “Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      “Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      “Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      “Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, “submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as “Not a Contribution.”

      “Contributor” shall mean Licensor and any individual or Legal Entity
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

      (d) If the Work includes a “NOTICE” text file as part of its
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
      Contributor provides its Contributions) on an “AS IS” BASIS,
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
      boilerplate notice, with the fields enclosed by brackets “[]”
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same “printed page” as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the “License”);
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an “AS IS” BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

-- LeanPool/Chvatal/Family.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/


/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Finite set families and maximal intersection

This file formalizes the set-family language used in Sections 1 and 4 of
*A proof of Chvátal's conjecture via a sharp correlation inequality*.
In particular, `Family.isMaximalIntersecting_iff` and
`Family.IsMaximalIntersecting.card_eq` give Proposition 4.1. We use mathlib's
`Set.Intersecting`, `IsUpperSet`, and `IsLowerSet`, so intersection includes a
member paired with itself: the empty set cannot belong to an intersecting family.

The dimension-zero exception is explicit. The empty family is maximal
intersecting on an empty ground type, but is not antipodal. Accordingly,
Proposition 4.1 is stated for a nonempty ground type.
-/


namespace Chvatal

/-- A family of subsets of a finite ground type, representing `𝒜 ⊆ 2^[n]`
throughout the paper. -/
abbrev Family (ι : Type*) := Finset (Finset ι)

namespace Family

variable {ι : Type*} [DecidableEq ι]

/-- The hereditary (decreasing) families of Section 1: taking a subset preserves
membership. This is mathlib's lower-set predicate. -/
abbrev IsHereditary (D : Family ι) : Prop := IsLowerSet (D : Set (Finset ι))

/-- The increasing families of Sections 1–4: taking a superset preserves
membership. This is mathlib's upper-set predicate. -/
abbrev IsIncreasing (B : Family ι) : Prop := IsUpperSet (B : Set (Finset ι))

/-- The intersecting families of Sections 1 and 4: any two members, including a
member with itself, have nonempty intersection. -/
abbrev IsIntersecting (B : Family ι) : Prop := (B : Set (Finset ι)).Intersecting

/-- A maximal intersecting family as defined immediately before Proposition 4.1.
Maximality is taken among all families on the given ground type. -/
def IsMaximalIntersecting (B : Family ι) : Prop :=
  B.IsIntersecting ∧ ∀ C : Family ι, C.IsIntersecting → B ⊆ C → B = C

/-- The star `D_i = {S ∈ D : i ∈ S}` appearing in Chvátal's conjecture
(Theorem 1.1 and Section 4). -/
def star (D : Family ι) (i : ι) : Family ι := D.filter (i ∈ ·)

/-- Membership in the star from Theorem 1.1. -/
@[simp] theorem mem_star {D : Family ι} {i : ι} {S : Finset ι} :
    S ∈ D.star i ↔ S ∈ D ∧ i ∈ S := by
  simp [star]

/-- A star is a subfamily of its ambient family, as used in Theorem 1.1. -/
theorem star_subset (D : Family ι) (i : ι) : D.star i ⊆ D :=
  Finset.filter_subset _ _

/-- Every star is intersecting; this is the last observation in the proof of
Proposition 5.3, and explains why stars are competitors in Chvátal's conjecture. -/
theorem star_isIntersecting (D : Family ι) (i : ι) : (D.star i).IsIntersecting := by
  intro S hS T hT hdisj
  exact Finset.disjoint_left.mp hdisj (mem_star.mp hS).2 (mem_star.mp hT).2

/-- Intersecting families cannot contain the empty set (Section 4's convention). -/
theorem IsIntersecting.empty_not_mem {B : Family ι} (hB : B.IsIntersecting) : ∅ ∉ B :=
  hB.bot_notMem

/-- Membership in an intersecting family guarantees that the member is nonempty,
including when the two members in the definition coincide. -/
theorem IsIntersecting.nonempty {B : Family ι} (hB : B.IsIntersecting)
    {S : Finset ι} (hS : S ∈ B) : S.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (hB.ne_bot hS)

/-- An intersecting subfamily remains intersecting; this is used when restricting
a maximal intersecting family to a hereditary family in Section 4. -/
theorem IsIntersecting.mono {B C : Family ι} (hC : C.IsIntersecting)
    (hBC : B ⊆ C) : B.IsIntersecting := Set.Intersecting.mono hBC hC

/-- Every intersecting family has a maximal intersecting extension, as used at
the end of Section 4 and in the proof of Proposition 5.3. This also holds in dimension
zero. -/
theorem IsIntersecting.exists_maximal_extension [Finite ι] {B : Family ι}
    (hB : B.IsIntersecting) : ∃ C : Family ι, B ⊆ C ∧ C.IsMaximalIntersecting := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨C, hBC, hC, hmax⟩ := Finite.exists_le_maximal (p := IsIntersecting) hB
  exact ⟨C, hBC, hC, fun D hD hCD => Finset.Subset.antisymm hCD (hmax hD hCD)⟩

/-- The first assertion in the proof of Proposition 4.1: adjoining supersets
preserves intersection, so every maximal intersecting family is increasing. -/
theorem IsMaximalIntersecting.isIncreasing {B : Family ι}
    (hB : B.IsMaximalIntersecting) : B.IsIncreasing :=
  hB.1.isUpperSet' hB.2

variable [Fintype ι]

/-- The dual family `B* = {S : Sᶜ ∉ B}` from Section 3.1. -/
def dual (B : Family ι) : Family ι := Finset.univ.filter (fun S => Sᶜ ∉ B)

/-- Membership in the dual family, matching the convention in Section 3.1. -/
@[simp] theorem mem_dual {B : Family ι} {S : Finset ι} :
    S ∈ B.dual ↔ Sᶜ ∉ B := by
  simp [dual]

/-- Family duality is an involution, as is the Boolean-function duality in
Sections 1–3. -/
@[simp] theorem dual_dual (B : Family ι) : B.dual.dual = B := by
  ext S
  simp

/-- A family is antipodal when exactly one of each complementary pair belongs to
it, as defined immediately before Proposition 4.1. -/
def IsAntipodal (B : Family ι) : Prop := ∀ S : Finset ι, S ∈ B ↔ Sᶜ ∉ B

/-- Antipodality is the self-duality condition used in Section 4. -/
theorem isAntipodal_iff_dual_eq (B : Family ι) : B.IsAntipodal ↔ B.dual = B := by
  simp only [IsAntipodal, Finset.ext_iff, mem_dual]
  exact forall_congr' fun S => iff_comm

/-- Duality preserves increasing families, as used for `𝒢*` in Section 3. -/
theorem IsIncreasing.dual {B : Family ι} (hB : B.IsIncreasing) : B.dual.IsIncreasing := by
  intro S T hST hS
  simp only [Finset.mem_coe, mem_dual] at hS ⊢
  exact fun hTc => hS (hB (compl_le_compl hST) hTc)

/-- Complementing membership in a hereditary family gives an increasing family;
this is the family underlying `f = 1 - 𝟙_D` in Section 4. -/
theorem IsHereditary.isIncreasing_compl {D : Family ι} (hD : D.IsHereditary) :
    Dᶜ.IsIncreasing := by
  intro S T hST hS
  simp only [Finset.mem_coe, Finset.mem_compl] at hS ⊢
  exact fun hT => hS (hD hST hT)

/-- The cardinality bound for intersecting families used by Proposition 4.1,
written without division so it remains valid in dimension zero. -/
theorem IsIntersecting.two_mul_card_le {B : Family ι} (hB : B.IsIntersecting) :
    2 * B.card ≤ 2 ^ Fintype.card ι := by
  simpa only [Fintype.card_finset] using hB.card_le

/-- The equality case in Proposition 4.1, in the division-free form
`2 |B| = 2^n`. The ground type must be nonempty. -/
theorem IsMaximalIntersecting.two_mul_card_eq [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) : 2 * B.card = 2 ^ Fintype.card ι := by
  simpa only [Fintype.card_finset] using hB.1.is_max_iff_card_eq.mp hB.2

/-- Proposition 4.1: a maximal intersecting family occupies half the cube. -/
theorem IsMaximalIntersecting.card_eq [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) : B.card = 2 ^ (Fintype.card ι - 1) := by
  have hpos := Fintype.card_pos (α := ι)
  have hcard := hB.two_mul_card_eq
  have hsucc : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  rw [hsucc, pow_succ] at hcard
  omega

/-- The antipodality conclusion of Proposition 4.1, obtained by counting the
disjoint family and its image under complementation. -/
theorem IsMaximalIntersecting.isAntipodal [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) : B.IsAntipodal := by
  let C := B.map ⟨compl, compl_injective⟩
  have hdisj : Disjoint B C := hB.1.disjoint_map_compl
  have hunion : B ∪ C = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, ← Nat.two_mul]
    exact hB.1.is_max_iff_card_eq.mp hB.2
  intro S
  constructor
  · exact hB.1.compl_notMem
  · intro hSc
    have hmem : S ∈ B ∪ C := by rw [hunion]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hmem with hS | hS
    · exact hS
    · obtain ⟨T, hT, hTS⟩ := Finset.mem_map.mp hS
      apply False.elim (hSc _)
      simpa only [← hTS, Function.Embedding.coeFn_mk, compl_compl] using hT

/-- The converse direction of Proposition 4.1: increasing antipodal families
are intersecting. -/
theorem IsIncreasing.isIntersecting_of_isAntipodal {B : Family ι}
    (hinc : B.IsIncreasing) (hanti : B.IsAntipodal) : B.IsIntersecting := by
  intro S hS T hT hdisj
  exact (hanti S).mp hS (hinc hdisj.le_compl_left hT)

/-- The converse maximality assertion of Proposition 4.1: any newly adjoined
member has its complement already in the original family. -/
theorem IsIncreasing.isMaximalIntersecting_of_isAntipodal {B : Family ι}
    (hinc : B.IsIncreasing) (hanti : B.IsAntipodal) : B.IsMaximalIntersecting := by
  refine ⟨hinc.isIntersecting_of_isAntipodal hanti, ?_⟩
  intro C hC hBC
  apply Finset.Subset.antisymm hBC
  intro S hS
  by_contra hSB
  have hScB : Sᶜ ∈ B := by
    by_contra hScB
    exact hSB ((hanti S).mpr hScB)
  exact hC.compl_notMem hS (hBC hScB)

/-- Proposition 4.1: on a nonempty ground type, maximal intersecting families
are exactly the increasing antipodal families. -/
theorem isMaximalIntersecting_iff [Nonempty ι] (B : Family ι) :
    B.IsMaximalIntersecting ↔ B.IsIncreasing ∧ B.IsAntipodal :=
  ⟨fun hB => ⟨hB.isIncreasing, hB.isAntipodal⟩,
    fun hB => hB.1.isMaximalIntersecting_of_isAntipodal hB.2⟩

/-- A full-cube star is increasing, as used among the examples in Section 5. -/
theorem univ_star_isIncreasing (i : ι) :
    (star (Finset.univ : Family ι) i).IsIncreasing := by
  intro S T hST hS
  exact mem_star.mpr ⟨Finset.mem_univ _, hST (mem_star.mp hS).2⟩

/-- A full-cube star selects exactly one member of each complementary pair;
this is the simplest antipodal family in Proposition 4.1. -/
theorem univ_star_isAntipodal (i : ι) :
    (star (Finset.univ : Family ι) i).IsAntipodal := by
  intro S
  simp

/-- Full-cube stars are maximal intersecting, the basic extremal examples in
Sections 4 and 5. -/
theorem univ_star_isMaximalIntersecting (i : ι) :
    (star (Finset.univ : Family ι) i).IsMaximalIntersecting :=
  (univ_star_isIncreasing i).isMaximalIntersecting_of_isAntipodal
    (univ_star_isAntipodal i)

/-- The last reduction in Section 4: to prove the star bound inside `D`, it
suffices to bound `D ∩ B` for each maximal intersecting family `B`. This lemma
isolates the purely combinatorial reduction from the correlation inequality. -/
theorem exists_star_bound_of_maximal [Finite ι] {D : Family ι}
    (hmax : ∀ B : Family ι, B.IsMaximalIntersecting →
      ∃ i : ι, (D ∩ B).card ≤ (D.star i).card)
    {A : Family ι} (hAD : A ⊆ D) (hA : A.IsIntersecting) :
    ∃ i : ι, A.card ≤ (D.star i).card := by
  obtain ⟨B, hAB, hB⟩ := hA.exists_maximal_extension
  obtain ⟨i, hi⟩ := hmax B hB
  exact ⟨i, (Finset.card_le_card (Finset.subset_inter hAD hAB)).trans hi⟩

end Family
end Chvatal

end

-- LeanPool/Chvatal/Fourier.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Fourier–Walsh analysis on the finite Boolean cube

This file develops the normalized Fourier–Walsh conventions used in Section 2 of
arXiv:2609.19123. A point of the cube is its set of coordinates equal to one.
-/


open scoped BigOperators symmDiff


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Uniform expectation on the Boolean cube, as in the preliminaries of the paper. -/
noncomputable def cubeMean (f : Finset ι → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card (Finset ι)

/-- The Walsh character indexed by `S`, denoted `χ_S` in the paper. -/
noncomputable def walsh (S x : Finset ι) : ℝ := (-1 : ℝ) ^ (S ∩ x).card

/-- The normalized Fourier coefficient `f̂(S)` of Section 2. -/
noncomputable def fourier (f : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  cubeMean (fun x => f x * walsh S x)

/-- Covariance with respect to uniform measure, as used in the main theorem. -/
noncomputable def covariance (f g : Finset ι → ℝ) : ℝ :=
  cubeMean (fun x => f x * g x) - cubeMean f * cubeMean g

/-- The dual Boolean function `f*(x) = 1 - f(1-x)` in the paper. -/
noncomputable def dual (f : Finset ι → ℝ) (x : Finset ι) : ℝ := 1 - f xᶜ

/-- The cube has positive cardinality, including when its coordinate set is empty. -/
theorem cube_card_pos : (0 : ℝ) < Fintype.card (Finset ι) := by
  exact_mod_cast Fintype.card_pos

/-- Uniform expectation preserves constants; this fixes the normalization in Section 2. -/
@[simp] theorem cubeMean_const (c : ℝ) : cubeMean (fun _ : Finset ι => c) = c := by
  simp [cubeMean]

/-- Additivity of the expectation used throughout the Fourier calculations. -/
theorem cubeMean_add (f g : Finset ι → ℝ) :
    cubeMean (fun x => f x + g x) = cubeMean f + cubeMean g := by
  simp [cubeMean, Finset.sum_add_distrib, add_div]

/-- Subtractivity of the expectation used throughout the Fourier calculations. -/
theorem cubeMean_sub (f g : Finset ι → ℝ) :
    cubeMean (fun x => f x - g x) = cubeMean f - cubeMean g := by
  simp [cubeMean, Finset.sum_sub_distrib, sub_div]

/-- Scalar linearity of expectation, used for the Fourier identities in Section 2. -/
theorem cubeMean_mul_left (c : ℝ) (f : Finset ι → ℝ) :
    cubeMean (fun x => c * f x) = c * cubeMean f := by
  simp [cubeMean, ← Finset.mul_sum, mul_div_assoc]

/-- Right scalar linearity of expectation, a companion to `cubeMean_mul_left`. -/
theorem cubeMean_mul_right (f : Finset ι → ℝ) (c : ℝ) :
    cubeMean (fun x => f x * c) = cubeMean f * c := by
  simpa [mul_comm] using cubeMean_mul_left c f

/-- Negation commutes with expectation, as used in Fourier coefficient calculations. -/
@[simp] theorem cubeMean_neg (f : Finset ι → ℝ) :
    cubeMean (fun x => -f x) = -cubeMean f := by
  simpa using cubeMean_mul_left (-1) f

/-- Expectation commutes with finite sums; this is used in Fourier inversion. -/
theorem cubeMean_sum {κ : Type*} (s : Finset κ) (f : κ → Finset ι → ℝ) :
    cubeMean (fun x => ∑ k ∈ s, f k x) = ∑ k ∈ s, cubeMean (f k) := by
  simp only [cubeMean, Finset.sum_div]
  exact Finset.sum_comm

/-- The uniform cube distribution is invariant under translation by symmetric difference. -/
theorem cubeMean_symmDiff (f : Finset ι → ℝ) (S : Finset ι) :
    cubeMean (fun x => f (x ∆ S)) = cubeMean f := by
  unfold cubeMean
  congr 1
  apply Function.Bijective.sum_comp
  exact (show Function.Involutive (fun x : Finset ι => x ∆ S) from
    fun x => symmDiff_symmDiff_cancel_right S x).bijective

/-- Complementation preserves uniform expectation; used in the duality identities. -/
theorem cubeMean_compl (f : Finset ι → ℝ) :
    cubeMean (fun x => f xᶜ) = cubeMean f := by
  unfold cubeMean
  congr 1
  exact (show Function.Involutive (fun x : Finset ι => xᶜ) from compl_compl).bijective.sum_comp f

/-- The mean of the dual function, recorded in the paper's preliminaries. -/
@[simp] theorem cubeMean_dual (f : Finset ι → ℝ) :
    cubeMean (dual f) = 1 - cubeMean f := by
  unfold dual
  rw [cubeMean_sub, cubeMean_const, cubeMean_compl]

/-- The empty Walsh character is the constant one function (Section 2). -/
@[simp] theorem walsh_empty (x : Finset ι) : walsh ∅ x = 1 := by simp [walsh]

/-- Evaluating a character at the origin gives one (Section 2). -/
@[simp] theorem walsh_apply_empty (S : Finset ι) : walsh S ∅ = 1 := by simp [walsh]

/-- The symmetry of the Walsh kernel allows inversion to use the same transform. -/
theorem walsh_comm (S x : Finset ι) : walsh S x = walsh x S := by
  simp [walsh, Finset.inter_comm]

/-- The empty Fourier coefficient is the uniform mean, in the convention of Section 2. -/
@[simp] theorem fourier_empty (f : Finset ι → ℝ) : fourier f ∅ = cubeMean f := by
  simp [fourier]

/-- Inserting a coordinate multiplies a Walsh character by that coordinate's sign. -/
theorem walsh_insert {i : ι} {S : Finset ι} (hi : i ∉ S) (x : Finset ι) :
    walsh (insert i S) x = (if i ∈ x then -1 else 1) * walsh S x := by
  by_cases hx : i ∈ x
  · simp [walsh, Finset.insert_inter_of_mem hx, Finset.card_insert_of_notMem,
      hi, hx, pow_succ, mul_comm]
  · simp [walsh, Finset.insert_inter_of_notMem hx, hx]

/-- The character multiplication law in the cube variable, used in Section 2. -/
theorem walsh_symmDiff_right (S x y : Finset ι) :
    walsh S (x ∆ y) = walsh S x * walsh S y := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [walsh_insert hi, walsh_insert hi, walsh_insert hi, ih]
    by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;>
      simp [Finset.mem_symmDiff, hx, hy]

/-- The product of characters is indexed by symmetric difference, as in Section 2. -/
theorem walsh_symmDiff_left (S T x : Finset ι) :
    walsh (S ∆ T) x = walsh S x * walsh T x := by
  simpa only [walsh_comm] using walsh_symmDiff_right x S T

/-- Every Walsh character has square one, as needed for Parseval's identity. -/
@[simp] theorem walsh_sq (S x : Finset ι) : walsh S x ^ 2 = 1 := by
  rw [pow_two, ← walsh_symmDiff_left]
  simp

/-- A singleton character is the sign of its single cube coordinate. -/
theorem walsh_singleton (i : ι) (x : Finset ι) :
    walsh {i} x = if i ∈ x then -1 else 1 := by
  simpa using walsh_insert (S := ∅) (by simp) x

/-- Toggling a coordinate in a character's support reverses its sign. -/
theorem walsh_toggle {S : Finset ι} {i : ι} (hi : i ∈ S) (x : Finset ι) :
    walsh S (x ∆ {i}) = -walsh S x := by
  rw [walsh_symmDiff_right, walsh_comm S {i}, walsh_singleton]
  simp [hi]

/-- Every nonconstant Walsh character has mean zero, the orthogonality input of Section 2. -/
theorem cubeMean_walsh_of_nonempty {S : Finset ι} (hS : S.Nonempty) :
    cubeMean (walsh S) = 0 := by
  obtain ⟨i, hi⟩ := hS
  have h := cubeMean_symmDiff (walsh S) {i}
  simp only [walsh_toggle hi, cubeMean_neg] at h
  linarith

/-- The uniform mean of a Walsh character is the Kronecker delta at the empty set. -/
theorem cubeMean_walsh (S : Finset ι) :
    cubeMean (walsh S) = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst S; simp [cubeMean, walsh]
  · simp [hS, cubeMean_walsh_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hS)]

/-- Orthogonality of the Walsh basis, stated in the paper's normalized inner product. -/
theorem walsh_orthogonality (S T : Finset ι) :
    cubeMean (fun x => walsh S x * walsh T x) = if S = T then 1 else 0 := by
  simp_rw [← walsh_symmDiff_left]
  rw [cubeMean_walsh]
  have h : S ∆ T = ∅ ↔ S = T := symmDiff_eq_bot
  simp only [h]

/-- Multiplying by a character shifts the Fourier index, as used in Lemma 2.2. -/
theorem fourier_mul_walsh (f : Finset ι → ℝ) (S T : Finset ι) :
    fourier (fun x => f x * walsh T x) S = fourier f (S ∆ T) := by
  unfold fourier
  congr 1
  funext x
  rw [walsh_symmDiff_left]
  ring

/-- A function independent of coordinate `i` has no Fourier coefficient containing `i`.
This is the support argument for the monomials in Lemma 2.2. -/
theorem fourier_eq_zero_of_invariant (f : Finset ι → ℝ) {S : Finset ι} {i : ι}
    (hi : i ∈ S) (hf : ∀ x, f (x ∆ {i}) = f x) : fourier f S = 0 := by
  have h := cubeMean_symmDiff (fun x => f x * walsh S x) {i}
  simp only [hf, walsh_toggle hi, mul_neg, cubeMean_neg] at h
  unfold fourier
  linarith

/-- Summing the Walsh kernel gives a scaled Kronecker delta, the inversion kernel. -/
theorem sum_walsh_kernel (x y : Finset ι) :
    (∑ S, walsh S x * walsh S y) =
      if x = y then (Fintype.card (Finset ι) : ℝ) else 0 := by
  have h := walsh_orthogonality x y
  unfold cubeMean at h
  rw [div_eq_iff (ne_of_gt (cube_card_pos (ι := ι)))] at h
  simpa only [walsh_comm, ite_mul, one_mul, zero_mul] using h

/-- Fourier inversion on the Boolean cube, the expansion used throughout Section 2. -/
theorem fourier_inversion (f : Finset ι → ℝ) (x : Finset ι) :
    (∑ S, fourier f S * walsh S x) = f x := by
  calc
    (∑ S, fourier f S * walsh S x) =
        (∑ y, f y * ∑ S, walsh S y * walsh S x) /
          Fintype.card (Finset ι) := by
      simp only [fourier, cubeMean, div_mul_eq_mul_div, Finset.sum_div,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = f x := by
      simp_rw [sum_walsh_kernel]
      simp [mul_ite]

/-- Parseval's identity for two real cube functions, as recalled in Section 2. -/
theorem parseval_inner (f g : Finset ι → ℝ) :
    cubeMean (fun x => f x * g x) = ∑ S, fourier f S * fourier g S := by
  calc
    cubeMean (fun x => f x * g x) =
        cubeMean (fun x => ∑ S, fourier g S * (f x * walsh S x)) := by
      congr 1
      funext x
      rw [← fourier_inversion g x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = ∑ S, fourier f S * fourier g S := by
      rw [cubeMean_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [cubeMean_mul_left]
      exact mul_comm (fourier g S) (fourier f S)

/-- The sum-of-squares form of Parseval's identity in Section 2. -/
theorem parseval (f : Finset ι → ℝ) :
    cubeMean (fun x => f x ^ 2) = ∑ S, fourier f S ^ 2 := by
  simpa only [pow_two] using parseval_inner f f

/-- The transform preserves addition, used in the constant-coefficient adjustment. -/
theorem fourier_add (f g : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f x + g x) S = fourier f S + fourier g S := by
  simp only [fourier, add_mul, cubeMean_add]

/-- The transform preserves subtraction, used in the constant-coefficient adjustment. -/
theorem fourier_sub (f g : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f x - g x) S = fourier f S - fourier g S := by
  simp only [fourier, sub_mul, cubeMean_sub]

/-- A constant has only its empty Fourier coefficient, as in the Section 2 convention. -/
theorem fourier_const (c : ℝ) (S : Finset ι) :
    fourier (fun _ : Finset ι => c) S = if S = ∅ then c else 0 := by
  rw [fourier, cubeMean_mul_left, cubeMean_walsh]
  split_ifs <;> simp

/-- Subtracting the mean removes exactly the constant Fourier coefficient. -/
theorem fourier_sub_mean (f : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f x - cubeMean f) S =
      if S = ∅ then 0 else fourier f S := by
  rw [fourier_sub, fourier_const]
  split_ifs with h
  · subst S; simp
  · simp

/-- The Fourier transform is injective, a direct consequence of the inversion formula. -/
theorem fourier_injective : Function.Injective (fourier (ι := ι)) := by
  intro f g h
  funext x
  rw [← fourier_inversion f x, ← fourier_inversion g x, h]

/-- Complementation multiplies a Walsh character by the parity of its index. -/
theorem walsh_compl (S x : Finset ι) :
    walsh S xᶜ = (-1 : ℝ) ^ S.card * walsh S x := by
  have hx : xᶜ = x ∆ Finset.univ := by
    ext i
    simp [Finset.mem_symmDiff]
  rw [hx, walsh_symmDiff_right]
  simp [walsh, mul_comm]

/-- Complementing the argument multiplies Fourier coefficients by index parity. -/
theorem fourier_compl (f : Finset ι → ℝ) (S : Finset ι) :
    fourier (fun x => f xᶜ) S = (-1 : ℝ) ^ S.card * fourier f S := by
  have h := cubeMean_compl (fun x => f x * walsh S xᶜ)
  simp only [compl_compl] at h
  unfold fourier
  rw [h]
  simp_rw [walsh_compl, ← mul_assoc, mul_comm (f _), mul_assoc]
  rw [cubeMean_mul_left]
  simp [mul_comm]

/-- The nonconstant Fourier coefficients of the dual, recalled in Section 2. -/
theorem fourier_dual_of_nonempty (f : Finset ι → ℝ) {S : Finset ι}
    (hS : S.Nonempty) :
    fourier (dual f) S = -((-1 : ℝ) ^ S.card * fourier f S) := by
  unfold dual
  rw [fourier_sub, fourier_const, fourier_compl]
  simp [hS.ne_empty]

/-- Covariance is the sum of the products of the nonconstant Fourier coefficients. -/
theorem covariance_fourier (f g : Finset ι → ℝ) :
    covariance f g = ∑ S ∈ Finset.univ.erase ∅, fourier f S * fourier g S := by
  rw [covariance, parseval_inner]
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset ι)))
    (fun S => fourier f S * fourier g S) (by simp : (∅ : Finset ι) ∈ Finset.univ)
  simp only [fourier_empty] at h
  linarith

/-- The alternating Fourier expression for covariance with the dual, used in Theorem 1.2. -/
theorem covariance_dual_fourier (f : Finset ι → ℝ) :
    covariance f (dual f) = ∑ S ∈ Finset.univ.erase ∅,
      -(-1 : ℝ) ^ S.card * fourier f S ^ 2 := by
  rw [covariance_fourier]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourier_dual_of_nonempty f
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)]
  ring

/-- Pointwise nonnegativity implies nonnegative uniform expectation. -/
theorem cubeMean_nonneg {f : Finset ι → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeMean f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x)
    (le_of_lt (cube_card_pos (ι := ι)))

/-- Pointwise comparison implies comparison of uniform expectations. -/
theorem cubeMean_mono {f g : Finset ι → ℝ} (h : ∀ x, f x ≤ g x) :
    cubeMean f ≤ cubeMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x)
    (le_of_lt (cube_card_pos (ι := ι)))

/-- Translating a cube function multiplies each Fourier coefficient by the character
of the translation vector; this is the spectral step in equation (10). -/
theorem fourier_symmDiff (f : Finset ι → ℝ) (S T : Finset ι) :
    fourier (fun x => f (x ∆ T)) S = walsh S T * fourier f S := by
  have h := cubeMean_symmDiff (fun x => f x * walsh S (x ∆ T)) T
  simp only [symmDiff_symmDiff_cancel_right] at h
  unfold fourier
  rw [h]
  simp_rw [walsh_symmDiff_right, ← mul_assoc]
  rw [cubeMean_mul_right]
  ring

/-- Equation (10), first equality: the energy of a simultaneous coordinate flip
is the Fourier energy weighted by the squared character difference. -/
theorem flip_energy_fourier (f : Finset ι → ℝ) (T : Finset ι) :
    cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) =
      ∑ S, (1 - walsh S T) ^ 2 * fourier f S ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourier_sub, fourier_symmDiff]
  ring

/-- The elementary parity computation behind equation (10). -/
theorem walsh_flip_factor (S T : Finset ι) :
    (1 - walsh S T) ^ 2 = if Odd (S ∩ T).card then 4 else 0 := by
  unfold walsh
  by_cases h : Odd (S ∩ T).card
  · norm_num [h, h.neg_one_pow]
  · have he : Even (S ∩ T).card := Nat.not_odd_iff_even.mp h
    simp [h, he.neg_one_pow]

/-- Equation (10), second equality: only Fourier sets meeting the flipped set
in an odd number of coordinates contribute to the flip energy. -/
theorem flip_energy_odd (f : Finset ι → ℝ) (T : Finset ι) :
    cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) =
      4 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
        fourier f S ^ 2 := by
  rw [flip_energy_fourier, Finset.mul_sum]
  simp_rw [walsh_flip_factor, Finset.sum_filter, ite_mul, zero_mul]

/-- The change of variables `y = x ∆ T` in equation (11), before specializing
`f` to an indicator. Both sides retain the paper's factor of one half. -/
theorem weighted_flip_energy (f g : Finset ι → ℝ) :
    (1 / 2 : ℝ) * ∑ T, fourier g T ^ 2 *
      cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) =
    (1 / 2 : ℝ) * cubeMean (fun x =>
      ∑ y, (f x - f y) ^ 2 * fourier g (x ∆ y) ^ 2) := by
  congr 1
  simp_rw [← cubeMean_mul_left]
  rw [← cubeMean_sum]
  congr 1
  funext x
  calc
    (∑ T, fourier g T ^ 2 * (f x - f (x ∆ T)) ^ 2) =
        ∑ T, (f x - f (x ∆ T)) ^ 2 * fourier g (x ∆ (x ∆ T)) ^ 2 := by
      simp only [symmDiff_symmDiff_cancel_left, mul_comm]
    _ = ∑ y, (f x - f y) ^ 2 * fourier g (x ∆ y) ^ 2 := by
      exact (show Function.Involutive (fun y : Finset ι => x ∆ y) from
        fun y => symmDiff_symmDiff_cancel_left x y).bijective.sum_comp
        (fun y => (f x - f y) ^ 2 * fourier g (x ∆ y) ^ 2)

end Chvatal

end

-- LeanPool/Chvatal/Bessel.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/




/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Normalized finite-dimensional Hilbert spaces

Theorem 2.1 uses the uniform probability inner product, rather than the counting
inner product on Euclidean space. This file transfers mathlib's Bessel inequality
and Gram–Schmidt theorem through the explicit normalization by `√|Ω|`.
-/


namespace Chvatal


open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The uniform probability inner product in Section 2, generalized to any nonempty
finite sample space. -/
noncomputable def uniformInner (f g : Ω → ℝ) : ℝ := (∑ x, f x * g x) / Fintype.card Ω

/-- The normalization which identifies the paper's probability inner product with
mathlib's Euclidean inner product. -/
noncomputable def uniformEuclidean : (Ω → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ Ω :=
  (LinearEquiv.smulOfNeZero ℝ (Ω → ℝ) (Real.sqrt (Fintype.card Ω))⁻¹
    (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast Fintype.card_pos)))).trans
      (WithLp.linearEquiv 2 ℝ (Ω → ℝ)).symm

/-- Coordinate formula for the normalization used in Theorem 2.1. -/
@[simp] theorem uniformEuclidean_apply (f : Ω → ℝ) (x : Ω) :
    uniformEuclidean f x = (Real.sqrt (Fintype.card Ω))⁻¹ * f x := rfl

/-- The normalization preserves exactly the probability inner product of Section 2. -/
theorem inner_uniformEuclidean (f g : Ω → ℝ) :
    inner ℝ (uniformEuclidean f) (uniformEuclidean g) = uniformInner f g := by
  rw [PiLp.inner_apply, uniformInner, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Real.inner_apply, uniformEuclidean_apply]
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hs := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (Fintype.card Ω) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  field_simp
  rw [hs]
  ring

/-- Orthonormality with respect to uniform probability, as in Theorem 2.1 and
Corollary 3.2. The index type may be empty. -/
noncomputable def UniformOrthonormal {κ : Type*} (u : κ → Ω → ℝ) : Prop := by
  classical
  exact ∀ i j, uniformInner (u i) (u j) = if i = j then 1 else 0

/-- Uniform orthonormality is ordinary orthonormality after normalization. -/
theorem uniformOrthonormal_iff {κ : Type*} (u : κ → Ω → ℝ) :
    UniformOrthonormal u ↔ Orthonormal ℝ (fun i => uniformEuclidean (u i)) := by
  classical
  rw [orthonormal_iff_ite]
  simp only [UniformOrthonormal, inner_uniformEuclidean]

/-- Theorem 2.1 (Bessel's inequality), with the paper's normalized inner product. -/
theorem bessel_inequality {κ : Type*} [Fintype κ] (u : κ → Ω → ℝ)
    (hu : UniformOrthonormal u) (h : Ω → ℝ) :
    ∑ i, (uniformInner (u i) h) ^ 2 ≤ uniformInner h h := by
  classical
  have hB := ((uniformOrthonormal_iff u).mp hu).sum_inner_products_le
    (s := Finset.univ) (uniformEuclidean h)
  simpa only [inner_uniformEuclidean, ← real_inner_self_eq_norm_sq,
    inner_uniformEuclidean, Real.norm_eq_abs, sq_abs] using hB

/-- The linear algebra step in Corollary 3.2: a finite independent family contained
in a subspace can be orthonormalized inside that same subspace. Thus simultaneous
physical and Fourier support restrictions, which define subspaces, are preserved. -/
theorem exists_uniformOrthonormal_in_submodule {κ : Type*} [Finite κ]
    (W : Submodule ℝ (Ω → ℝ)) (f : κ → Ω → ℝ)
    (hli : LinearIndependent ℝ f) (hf : ∀ i, f i ∈ W) :
    ∃ u : κ → Ω → ℝ, UniformOrthonormal u ∧ ∀ i, u i ∈ W := by
  classical
  let _ := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let v : Fin (Fintype.card κ) → EuclideanSpace ℝ Ω :=
    fun i => uniformEuclidean (f (e.symm i))
  have hv : LinearIndependent ℝ v :=
    (hli.comp e.symm e.symm.injective).map'
      uniformEuclidean.toLinearMap (LinearMap.ker_eq_bot.mpr uniformEuclidean.injective)
  let w := InnerProductSpace.gramSchmidtNormed ℝ v
  have hw : Orthonormal ℝ w := InnerProductSpace.gramSchmidtNormed_orthonormal hv
  let L := W.map uniformEuclidean.toLinearMap
  have hspan : Submodule.span ℝ (Set.range v) ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨f (e.symm i), hf _, rfl⟩
  have hwmem (i) : w i ∈ L := by
    apply hspan
    rw [← InnerProductSpace.span_gramSchmidt ℝ v,
      ← InnerProductSpace.span_gramSchmidtNormed_range]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨fun i => uniformEuclidean.symm (w (e i)), ?_, ?_⟩
  · rw [uniformOrthonormal_iff]
    simpa only [LinearEquiv.apply_symm_apply, Function.comp_def] using hw.comp e e.injective
  · intro i
    obtain ⟨g, hg, hgeq⟩ := Submodule.mem_map.mp (hwmem (e i))
    change uniformEuclidean.symm (w (e i)) ∈ W
    rw [← hgeq]
    simpa using hg

end Chvatal

end

-- LeanPool/Chvatal/Auxiliary.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Auxiliary monomials

The Boolean monomials in Section 3.1 of the paper are represented as indicators
of principal upper sets. This file proves their exact Fourier expansion (9),
all four assertions of Lemma 3.1, and the orthonormal auxiliary families of
Corollary 3.2. The independence proof uses subset induction and needs no
arbitrary ordering of the monomials.
-/


namespace Chvatal

open Finset
open scoped symmDiff

variable {ι : Type*} [DecidableEq ι]

/-- The Boolean monomial `M_S` of Section 3.1, equal to `1` exactly on supersets of `S`. -/
def monomial (S x : Finset ι) : ℝ := if S ⊆ x then 1 else 0

/-- The physical support calculation immediately preceding Lemma 3.1. -/
@[simp] theorem monomial_ne_zero_iff (S x : Finset ι) :
    monomial S x ≠ 0 ↔ S ⊆ x := by
  simp [monomial]

/-- Each monomial is one at its own index, the diagonal entry in the triangular
independence argument of Lemma 3.1(iii). -/
@[simp] theorem monomial_self (S : Finset ι) : monomial S S = 1 := by
  simp [monomial]

variable [Fintype ι]

/-- Evaluating a zero linear combination at successive subsets forces every
coefficient to vanish. This is the triangular argument in Lemma 3.1(iii). -/
theorem monomial_coefficients_eq_zero (c : Finset ι → ℝ)
    (h : ∑ S, c S • monomial S = 0) : ∀ S, c S = 0 := by
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  have heval := congrFun h S
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
  have hsum : ∑ T : Finset ι, c T * monomial T S = c S := by
      rw [Finset.sum_eq_single S]
      · simp
      · intro T _ hTS
        by_cases hsub : T ⊆ S
        · rw [ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hTS⟩)]
          simp
        · simp [monomial, hsub]
      · simp
  exact hsum.symm.trans heval

/-- Lemma 3.1(iii): the entire Boolean monomial family is linearly independent.
Consequently every family obtained by restricting the index set is independent. -/
theorem linearIndependent_monomial [Finite ι] :
    LinearIndependent ℝ (monomial (ι := ι)) := by
  let _ := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  exact monomial_coefficients_eq_zero

/-- Lemma 3.1(iii) for any specified subfamily of monomials. -/
theorem linearIndependent_monomial_subfamily [Finite ι] (A : Set (Finset ι)) :
    LinearIndependent ℝ (fun S : A => monomial S.1) :=
  linearIndependent_monomial.comp Subtype.val Subtype.val_injective

/-- A monomial is unchanged when a coordinate outside its index is toggled.
This gives its Fourier support in the discussion preceding Lemma 3.1. -/
theorem monomial_toggle {S : Finset ι} {i : ι} (hi : i ∉ S) (x : Finset ι) :
    monomial S (x ∆ {i}) = monomial S x := by
  have hsub : S ⊆ x ∆ {i} ↔ S ⊆ x := by
    constructor <;> intro h j hj
    · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
      simpa [Finset.mem_symmDiff, hji] using h hj
    · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
      simpa [Finset.mem_symmDiff, hji] using h hj
  simp [monomial, hsub]

/-- The Fourier support inclusion for monomials preceding Lemma 3.1:
only subsets of the monomial's index can have a nonzero coefficient. -/
theorem fourier_monomial_eq_zero {S T : Finset ι} (hTS : ¬T ⊆ S) :
    fourier (monomial S) T = 0 := by
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
  exact fourier_eq_zero_of_invariant _ hiT (monomial_toggle hiS)

/-- Multiplication by the full Walsh character, used to construct the second
auxiliary family in Lemma 3.1. It is a linear involution. -/
noncomputable def fullWalshMultiplier : (Finset ι → ℝ) ≃ₗ[ℝ] (Finset ι → ℝ) where
  toFun f x := f x * walsh Finset.univ x
  invFun f x := f x * walsh Finset.univ x
  left_inv f := by
    funext x
    change (f x * walsh Finset.univ x) * walsh Finset.univ x = f x
    rw [mul_assoc, ← pow_two, walsh_sq, mul_one]
  right_inv f := by
    funext x
    change (f x * walsh Finset.univ x) * walsh Finset.univ x = f x
    rw [mul_assoc, ← pow_two, walsh_sq, mul_one]
  map_add' f g := by ext x; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The functions `χ_[n] M_S` in the second auxiliary family of Lemma 3.1. -/
noncomputable def twistedMonomial (S : Finset ι) : Finset ι → ℝ :=
  fullWalshMultiplier (monomial S)

/-- Coordinate description of the twisted monomials of Lemma 3.1. -/
@[simp] theorem twistedMonomial_apply (S x : Finset ι) :
    twistedMonomial S x = monomial S x * walsh Finset.univ x := rfl

/-- Lemma 3.1(iii) for the second family: the full character is an invertible
multiplier, so independence of the monomials is preserved. -/
theorem linearIndependent_twistedMonomial :
    LinearIndependent ℝ (twistedMonomial (ι := ι)) :=
  linearIndependent_monomial.map' fullWalshMultiplier.toLinearMap
    (LinearMap.ker_eq_bot.mpr fullWalshMultiplier.injective)

/-- Fourier support of the second family in Lemma 3.1: a nonzero coefficient
must contain the complement of the monomial's index. -/
theorem fourier_twistedMonomial_eq_zero {S T : Finset ι} (hST : ¬Sᶜ ⊆ T) :
    fourier (twistedMonomial S) T = 0 := by
  have hTS : ¬Tᶜ ⊆ S := by
    intro h
    exact hST (by simpa using compl_le_compl h)
  change fourier (fun x => monomial S x * walsh Finset.univ x) T = 0
  rw [fourier_mul_walsh]
  have hcomp : T ∆ Finset.univ = Tᶜ := by
    ext i
    simp [Finset.mem_symmDiff]
  rw [hcomp]
  exact fourier_monomial_eq_zero hTS

/-- Lemma 3.1(i), physical support: increasing families contain the entire
support of every monomial indexed by one of their members. -/
theorem monomial_eq_zero_of_not_mem {F : Family ι} (hF : F.IsIncreasing)
    {S : Finset ι} (hS : S ∈ F) {x : Finset ι} (hx : x ∉ F) :
    monomial S x = 0 := by
  have hsub : ¬S ⊆ x := fun h => hx (hF h hS)
  simp [monomial, hsub]

/-- Lemma 3.1(i), Fourier support: a monomial whose index lies outside an
increasing family has zero Fourier coefficients on that family. -/
theorem fourier_monomial_eq_zero_of_mem {G : Family ι} (hG : G.IsIncreasing)
    {S T : Finset ι} (hS : S ∉ G) (hT : T ∈ G) :
    fourier (monomial S) T = 0 :=
  fourier_monomial_eq_zero (fun hTS => hS (hG hTS hT))

/-- Lemma 3.1(ii), physical support of the twisted monomials. -/
theorem twistedMonomial_eq_zero_of_not_mem {F : Family ι} (hF : F.IsIncreasing)
    {S : Finset ι} (hS : S ∈ F) {x : Finset ι} (hx : x ∉ F) :
    twistedMonomial S x = 0 := by
  simp [monomial_eq_zero_of_not_mem hF hS hx]

/-- Lemma 3.1(ii), Fourier support of the twisted monomials: when the complement
of the index belongs to an increasing family, all coefficients outside it vanish. -/
theorem fourier_twistedMonomial_eq_zero_of_not_mem {G : Family ι}
    (hG : G.IsIncreasing) {S T : Finset ι} (hS : Sᶜ ∈ G) (hT : T ∉ G) :
    fourier (twistedMonomial S) T = 0 :=
  fourier_twistedMonomial_eq_zero (fun hST => hT (hG hST hS))

/-- The multiplicative recursion for the Boolean monomials in Section 3.1. -/
theorem monomial_insert (i : ι) (S x : Finset ι) :
    monomial (insert i S) x = if i ∈ x then monomial S x else 0 := by
  simp only [monomial, Finset.insert_subset_iff]
  split_ifs <;> simp_all

/-- Equation (9), multiplied by `2^|S|`: the finite Walsh expansion of a
Boolean monomial. This proof follows the coordinate product expansion. -/
theorem monomial_expansion_scaled (S x : Finset ι) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * walsh T x) =
      (2 : ℝ) ^ S.card * monomial S x := by
  induction S using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i S hi ih =>
    rw [Finset.sum_powerset_insert hi]
    have hsum :
        (∑ T ∈ S.powerset, (-1 : ℝ) ^ (insert i T).card * walsh (insert i T) x) =
          -(if i ∈ x then (-1 : ℝ) else 1) *
            (∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * walsh T x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      have hiT : i ∉ T := fun h => hi ((Finset.mem_powerset.mp hT) h)
      rw [Finset.card_insert_of_notMem hiT, walsh_insert hiT, pow_succ]
      ring
    rw [hsum, ih, Finset.card_insert_of_notMem hi, pow_succ, monomial_insert]
    by_cases hix : i ∈ x <;> simp [hix]
    ring

/-- Equation (9): the normalized Fourier–Walsh expansion of `M_S`. -/
theorem monomial_expansion (S x : Finset ι) :
    monomial S x = ((2 : ℝ) ^ S.card)⁻¹ *
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * walsh T x := by
  rw [monomial_expansion_scaled]
  simp

/-- Scalar linearity of the Fourier transform, used when preserving support
under the Gram–Schmidt process in Corollary 3.2. -/
theorem fourier_smul_function (c : ℝ) (f : Finset ι → ℝ) (S : Finset ι) :
    fourier (c • f) S = c * fourier f S := by
  simp only [fourier, Pi.smul_apply, smul_eq_mul, mul_assoc, cubeMean_mul_left]

/-- The functions satisfying both support restrictions of Corollary 3.2 form a
linear subspace: physical support lies in `F`, and Fourier support lies in `K`. -/
def supportSubspace (F K : Family ι) : Submodule ℝ (Finset ι → ℝ) where
  carrier := {f | (∀ x, x ∉ F → f x = 0) ∧ (∀ S, S ∉ K → fourier f S = 0)}
  zero_mem' := by
    constructor
    · intro x _; rfl
    · intro S _; simp [fourier, cubeMean]
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx; simp [hf.1 x hx, hg.1 x hx]
    · intro S hS
      change fourier (fun x => f x + g x) S = 0
      rw [fourier_add, hf.2 S hS, hg.2 S hS, add_zero]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x hx; simp [hf.1 x hx]
    · intro S hS; rw [fourier_smul_function, hf.2 S hS, mul_zero]

/-- Expanded membership criterion for the support-preserving subspace used in
Corollary 3.2. -/
@[simp] theorem mem_supportSubspace (F K : Family ι) (f : Finset ι → ℝ) :
    f ∈ supportSubspace F K ↔
      (∀ x, x ∉ F → f x = 0) ∧ (∀ S, S ∉ K → fourier f S = 0) := Iff.rfl

/-- The probability inner product of Theorem 2.1 is the cube expectation used in
all Fourier identities in Section 2. -/
theorem uniformInner_eq_cubeMean (f g : Finset ι → ℝ) :
    uniformInner f g = cubeMean (fun x => f x * g x) := rfl

/-- Lemma 3.1(iv): disjoint Fourier supports imply orthogonality by Parseval. -/
theorem uniformInner_eq_zero_of_fourier_support (G : Family ι)
    {f g : Finset ι → ℝ} (hf : ∀ S, S ∈ G → fourier f S = 0)
    (hg : ∀ S, S ∉ G → fourier g S = 0) : uniformInner f g = 0 := by
  rw [uniformInner_eq_cubeMean, parseval_inner]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S ∈ G
  · rw [hf S hS, zero_mul]
  · rw [hg S hS, mul_zero]

/-- Symmetry of the real probability inner product, used for the two mixed
orders in the combined orthonormal family of Corollary 3.2. -/
theorem uniformInner_comm (f g : Finset ι → ℝ) : uniformInner f g = uniformInner g f := by
  simp only [uniformInner, mul_comm]

/-- Lemma 3.1(iv) for the particular two monomial families in the paper. -/
theorem monomial_twistedMonomial_orthogonal {G : Family ι} (hG : G.IsIncreasing)
    {S T : Finset ι} (hS : S ∉ G) (hT : Tᶜ ∈ G) :
    uniformInner (monomial S) (twistedMonomial T) = 0 :=
  uniformInner_eq_zero_of_fourier_support G
    (fun _ h => fourier_monomial_eq_zero_of_mem hG hS h)
    (fun _ h => fourier_twistedMonomial_eq_zero_of_not_mem hG hT h)

/-- Corollary 3.2: orthonormal auxiliary families with the paper's exact index
sets and both required support conditions. The sum type joins the two families
into a single orthonormal system, including when either index set is empty. -/
theorem auxiliary_orthonormal_system (F G : Family ι)
    (hF : F.IsIncreasing) (hG : G.IsIncreasing) :
    ∃ (u : ↥(F \ G) → Finset ι → ℝ) (v : ↥(F \ G.dual) → Finset ι → ℝ),
      UniformOrthonormal (Sum.elim u v) ∧
      (∀ i, u i ∈ supportSubspace F Gᶜ) ∧
      (∀ i, v i ∈ supportSubspace F G) := by
  classical
  have hmono : ∀ i : ↥(F \ G), monomial i.1 ∈ supportSubspace F Gᶜ := by
    intro i
    constructor
    · intro x hx
      exact monomial_eq_zero_of_not_mem hF (Finset.mem_sdiff.mp i.2).1 hx
    · intro S hS
      exact fourier_monomial_eq_zero_of_mem hG (Finset.mem_sdiff.mp i.2).2
        (by simpa using hS)
  have htwist : ∀ i : ↥(F \ G.dual), twistedMonomial i.1 ∈ supportSubspace F G := by
    intro i
    constructor
    · intro x hx
      exact twistedMonomial_eq_zero_of_not_mem hF (Finset.mem_sdiff.mp i.2).1 hx
    · intro S hS
      apply fourier_twistedMonomial_eq_zero_of_not_mem hG _ hS
      simpa only [Family.mem_dual, not_not] using (Finset.mem_sdiff.mp i.2).2
  obtain ⟨u, hu, humem⟩ := exists_uniformOrthonormal_in_submodule
    (supportSubspace F Gᶜ) (fun i : ↥(F \ G) => monomial i.1)
      (linearIndependent_monomial.comp Subtype.val Subtype.val_injective) hmono
  obtain ⟨v, hv, hvmem⟩ := exists_uniformOrthonormal_in_submodule
    (supportSubspace F G) (fun i : ↥(F \ G.dual) => twistedMonomial i.1)
      (linearIndependent_twistedMonomial.comp Subtype.val Subtype.val_injective) htwist
  have huv (i j) : uniformInner (u i) (v j) = 0 := by
    apply uniformInner_eq_zero_of_fourier_support G
    · intro S hS
      exact (humem i).2 S (by simpa using hS)
    · exact (hvmem j).2
  refine ⟨u, v, ?_, humem, hvmem⟩
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i = j <;> simpa [hij] using hu i j
    | inr j => simpa using huv i j
  | inr i =>
    cases j with
    | inl j => simpa [uniformInner_comm] using huv j i
    | inr j =>
      by_cases hij : i = j <;> simpa [hij] using hv i j

/-- The exact coefficient formula from equation (9). In particular, every subset
of `S` occurs with a nonzero Fourier coefficient. -/
theorem fourier_monomial (S T : Finset ι) :
    fourier (monomial S) T =
      if T ⊆ S then ((2 : ℝ) ^ S.card)⁻¹ * (-1 : ℝ) ^ T.card else 0 := by
  unfold fourier
  simp_rw [monomial_expansion S]
  simp_rw [mul_assoc, Finset.sum_mul, mul_assoc]
  rw [cubeMean_mul_left, cubeMean_sum]
  simp_rw [cubeMean_mul_left, walsh_orthogonality]
  by_cases hTS : T ⊆ S <;> simp [hTS, mul_ite]

/-- The exact Fourier support calculation for the first family preceding Lemma 3.1. -/
theorem fourier_monomial_ne_zero_iff (S T : Finset ι) :
    fourier (monomial S) T ≠ 0 ↔ T ⊆ S := by
  rw [fourier_monomial]
  split_ifs with h <;> simp [h]

/-- The exact coefficients of the second auxiliary family, obtained by
complementing Fourier indices as in the discussion preceding Lemma 3.1. -/
theorem fourier_twistedMonomial (S T : Finset ι) :
    fourier (twistedMonomial S) T =
      if Sᶜ ⊆ T then ((2 : ℝ) ^ S.card)⁻¹ * (-1 : ℝ) ^ Tᶜ.card else 0 := by
  change fourier (fun x => monomial S x * walsh Finset.univ x) T = _
  rw [fourier_mul_walsh]
  have hcomp : T ∆ Finset.univ = Tᶜ := by ext i; simp [Finset.mem_symmDiff]
  rw [hcomp, fourier_monomial]
  have hsub : Tᶜ ⊆ S ↔ Sᶜ ⊆ T := by
    constructor <;> intro h <;> simpa using compl_le_compl h
  simp only [hsub]

/-- The exact Fourier support calculation for the second family preceding
Lemma 3.1: its support is the upper interval above the complementary index. -/
theorem fourier_twistedMonomial_ne_zero_iff (S T : Finset ι) :
    fourier (twistedMonomial S) T ≠ 0 ↔ Sᶜ ⊆ T := by
  rw [fourier_twistedMonomial]
  split_ifs with h <;> simp [h]

/-- The physical support equality for monomials stated before Lemma 3.1. -/
theorem support_monomial (S : Finset ι) :
    Function.support (monomial S) = {x | S ⊆ x} := by
  ext x; simp [Function.mem_support]

/-- The Fourier support equality for monomials stated before Lemma 3.1. -/
theorem support_fourier_monomial (S : Finset ι) :
    Function.support (fourier (monomial S)) = {T | T ⊆ S} := by
  ext T; simp [Function.mem_support, fourier_monomial_ne_zero_iff]

/-- Multiplication by the full character does not change physical support,
as stated before Lemma 3.1. -/
theorem support_twistedMonomial (S : Finset ι) :
    Function.support (twistedMonomial S) = {x | S ⊆ x} := by
  ext x
  have hw : walsh Finset.univ x ≠ 0 := by
    intro h
    have hsq := walsh_sq Finset.univ x
    simp [h] at hsq
  simp [Function.mem_support, hw]

/-- The Fourier support equality for twisted monomials stated before Lemma 3.1. -/
theorem support_fourier_twistedMonomial (S : Finset ι) :
    Function.support (fourier (twistedMonomial S)) = {T | Sᶜ ⊆ T} := by
  ext T; simp [Function.mem_support, fourier_twistedMonomial_ne_zero_iff]

end Chvatal

end

-- LeanPool/Chvatal/Boolean.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Boolean functions and coordinate influences

This file formalizes the influence convention in Section 2, equation (6), and the
influence comparison of Lemma 3.3 of Chang–Liu–Liu, arXiv:2609.19123v1.
Boolean functions are real-valued functions with an explicit `IsBoolean` hypothesis;
this makes their Fourier transforms ordinary real-valued transforms. Increasing
functions use mathlib's `Monotone` predicate on finite subsets ordered by inclusion.
-/


open scoped BigOperators symmDiff


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Section 2: a real-valued cube function is Boolean when every value is zero or one. -/
noncomputable def IsBoolean (f : Finset ι → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

/-- The sign `2xᵢ - 1` used in the influence identity (6). -/
noncomputable def coordinateSign (i : ι) (x : Finset ι) : ℝ := if i ∈ x then 1 else -1

/-- Section 2: influence, written as mean squared change under a single-coordinate flip.
For Boolean functions this is the probability that the value changes; see
`influence_eq_mean_indicator`. -/
noncomputable def influence (f : Finset ι → ℝ) (i : ι) : ℝ :=
  cubeMean (fun x => (f x - f (x ∆ {i})) ^ 2)

/-- The Boolean duality operation of Section 2 preserves Boolean values. -/
theorem IsBoolean.dual {f : Finset ι → ℝ} (hf : IsBoolean f) : IsBoolean (dual f) := by
  intro x
  rcases hf xᶜ with h | h
  · right; simp [Chvatal.dual, h]
  · left; simp [Chvatal.dual, h]

/-- The duality operation of Section 2 preserves monotonicity. -/
theorem monotone_dual {f : Finset ι → ℝ} (hf : Monotone f) : Monotone (dual f) := by
  intro x y hxy
  exact sub_le_sub_left (hf (compl_le_compl hxy)) 1

/-- Boolean values lie in the unit interval; used in the pointwise estimates of Section 3. -/
theorem IsBoolean.nonneg {f : Finset ι → ℝ} (hf : IsBoolean f) (x : Finset ι) :
    0 ≤ f x := by rcases hf x with h | h <;> simp [h]

/-- Squaring a Boolean value leaves it unchanged, as used in Parseval's variance formula. -/
theorem IsBoolean.sq {f : Finset ι → ℝ} (hf : IsBoolean f) (x : Finset ι) :
    f x ^ 2 = f x := by rcases hf x with h | h <;> simp [h]

/-- For Boolean functions the squared-change definition equals the probability definition
of influence in Section 2. -/
theorem influence_eq_mean_indicator {f : Finset ι → ℝ} (hf : IsBoolean f) (i : ι) :
    influence f i = cubeMean (fun x => if f x ≠ f (x ∆ {i}) then 1 else 0) := by
  unfold influence
  congr 1
  funext x
  rcases hf x with h | h <;> rcases hf (x ∆ {i}) with k | k <;> simp [h, k]

/-- Influences are nonnegative, including in the degenerate cases of Theorem 1.2. -/
theorem influence_nonneg (f : Finset ι → ℝ) (i : ι) : 0 ≤ influence f i :=
  cubeMean_nonneg fun _ => sq_nonneg _

/-- Flipping a set containing `i` reverses `2xᵢ - 1`, as in the proof of Lemma 3.3. -/
theorem coordinateSign_symmDiff {T : Finset ι} {i : ι} (hi : i ∈ T) (x : Finset ι) :
    coordinateSign i (x ∆ T) = -coordinateSign i x := by
  by_cases hx : i ∈ x <;> simp [coordinateSign, Finset.mem_symmDiff, hi, hx]

/-- The change of variables in the proof of Lemma 3.3 negates the signed mean. -/
theorem signed_mean_flip {T : Finset ι} {i : ι} (hi : i ∈ T) (f : Finset ι → ℝ) :
    cubeMean (fun x => coordinateSign i x * f (x ∆ T)) =
      -cubeMean (fun x => coordinateSign i x * f x) := by
  calc
    _ = cubeMean (fun x => coordinateSign i (x ∆ T) * f ((x ∆ T) ∆ T)) :=
      (cubeMean_symmDiff (fun x => coordinateSign i x * f (x ∆ T)) T).symm
    _ = -cubeMean (fun x => coordinateSign i x * f x) := by
      simp_rw [coordinateSign_symmDiff hi, symmDiff_symmDiff_cancel_right, neg_mul]
      exact cubeMean_neg _

/-- The signed difference formula in the proof of Lemma 3.3, before using Boolean values. -/
theorem signed_mean_difference {T : Finset ι} {i : ι} (hi : i ∈ T)
    (f : Finset ι → ℝ) :
    cubeMean (fun x => coordinateSign i x * (f x - f (x ∆ T))) =
      2 * cubeMean (fun x => coordinateSign i x * f x) := by
  simp_rw [mul_sub]
  rw [cubeMean_sub, signed_mean_flip hi]
  ring

/-- Equation (6), pointwise form: monotonicity fixes the sign of a single-coordinate change. -/
theorem flip_sq_eq_signed_difference {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (i : ι) (x : Finset ι) :
    (f x - f (x ∆ {i})) ^ 2 = coordinateSign i x * (f x - f (x ∆ {i})) := by
  by_cases hi : i ∈ x
  · have hs : x ∆ {i} ⊆ x := by
      intro j hj
      simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hj
      rcases hj with h | h
      · exact h.1
      · exact h.1 ▸ hi
    have hle := hm hs
    rcases hf x with h | h <;> rcases hf (x ∆ {i}) with k | k <;>
      simp_all [coordinateSign]
    linarith
  · have hs : x ⊆ x ∆ {i} := by
      intro j hj
      simp only [Finset.mem_symmDiff, Finset.mem_singleton]
      exact Or.inl ⟨hj, fun h => hi (h ▸ hj)⟩
    have hle := hm hs
    rcases hf x with h | h <;> rcases hf (x ∆ {i}) with k | k <;>
      simp_all [coordinateSign]
    linarith

/-- Equation (6): influence of an increasing Boolean function equals twice its signed mean. -/
theorem influence_eq_signed_mean {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (i : ι) :
    influence f i = 2 * cubeMean (fun x => coordinateSign i x * f x) := by
  unfold influence
  simp_rw [flip_sq_eq_signed_difference hf hm]
  exact signed_mean_difference (Finset.mem_singleton_self i) f

/-- The pointwise Boolean estimate in Lemma 3.3: a signed change is at most its square. -/
theorem signed_difference_le_sq {f : Finset ι → ℝ} (hf : IsBoolean f)
    (i : ι) (x y : Finset ι) :
    coordinateSign i x * (f x - f y) ≤ (f x - f y) ^ 2 := by
  rcases hf x with h | h <;> rcases hf y with k | k <;>
    by_cases hi : i ∈ x <;> simp [coordinateSign, h, k, hi]

/-- Lemma 3.3, inequality in (15), for each coordinate in the flipped set.
Taking the maximum over these coordinates gives exactly the paper's formulation. -/
theorem influence_le_flip_energy {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) {T : Finset ι} {i : ι} (hi : i ∈ T) :
    influence f i ≤ cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) := by
  rw [influence_eq_signed_mean hf hm, ← signed_mean_difference hi]
  exact cubeMean_mono fun x => signed_difference_le_sq hf i x _

/-- Corollary 1.3: an antipodal Boolean function has mean one half. -/
theorem mean_eq_half_of_antipodal {g : Finset ι → ℝ} (hg : dual g = g) :
    cubeMean g = 1 / 2 := by
  have h := cubeMean_dual g
  rw [hg] at h
  linarith

/-- Corollary 1.3: an antipodal Boolean function has variance one quarter. -/
theorem variance_eq_quarter_of_antipodal {g : Finset ι → ℝ} (hb : IsBoolean g)
    (hg : dual g = g) : covariance g g = 1 / 4 := by
  have hs : (fun x => g x * g x) = g := by
    funext x
    simpa [pow_two] using hb.sq x
  rw [covariance, hs, mean_eq_half_of_antipodal hg]
  norm_num

end Chvatal

end

-- LeanPool/Chvatal/Counting.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The counting reduction in Section 4

The indicator-function identities in this file translate between set families
and the cube's uniform probability measure. They are the elementary counting
steps in Section 4 of arXiv:2609.19123.
-/


open scoped BigOperators


namespace Chvatal
namespace Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real-valued indicator `𝟙_B` of a family, used in Section 4. -/
noncomputable def indicator (B : Family ι) (x : Finset ι) : ℝ := if x ∈ B then 1 else 0

/-- Evaluating the Section 4 indicator at a member of its family. -/
@[simp] theorem indicator_of_mem {B : Family ι} {x : Finset ι} (hx : x ∈ B) :
    B.indicator x = 1 := by simp [indicator, hx]

/-- Evaluating the Section 4 indicator outside its family. -/
@[simp] theorem indicator_of_not_mem {B : Family ι} {x : Finset ι} (hx : x ∉ B) :
    B.indicator x = 0 := by simp [indicator, hx]

/-- The expectation of a family indicator is its density in the Boolean cube,
the normalization used in both counting formulas in Section 4. -/
theorem cubeMean_indicator (B : Family ι) :
    cubeMean B.indicator = B.card / (Fintype.card (Finset ι) : ℝ) := by
  simp [cubeMean, indicator]

/-- The pointwise product of two family indicators counts their intersection,
as used in the covariance calculation in Section 4. -/
theorem indicator_inter (D B : Family ι) :
    (D ∩ B).indicator = fun x => D.indicator x * B.indicator x := by
  funext x
  by_cases hD : x ∈ D <;> by_cases hB : x ∈ B <;> simp [indicator, hD, hB]

/-- Complementing family membership gives the function `1 - 𝟙_D` of Section 4. -/
theorem indicator_compl (D : Family ι) :
    Dᶜ.indicator = fun x => 1 - D.indicator x := by
  funext x
  by_cases hx : x ∈ D <;> simp [indicator, hx]

/-- An increasing family has an increasing indicator, as used for `g = 𝟙_B`
in Section 4. -/
theorem IsIncreasing.monotone_indicator {B : Family ι} (hB : B.IsIncreasing) :
    Monotone B.indicator := by
  intro x y hxy
  by_cases hx : x ∈ B
  · have hy : y ∈ B := hB hxy hx
    simp [indicator, hx, hy]
  · simp only [indicator, if_neg hx]
    split_ifs <;> norm_num

/-- For a hereditary family, the function `f = 1 - 𝟙_D` in Section 4 is
increasing. -/
theorem IsHereditary.monotone_one_sub_indicator {D : Family ι}
    (hD : D.IsHereditary) : Monotone (fun x => 1 - D.indicator x) := by
  intro x y hxy
  by_cases hy : y ∈ D
  · have hx : x ∈ D := hD hxy hy
    simp [indicator, hx, hy]
  · by_cases hx : x ∈ D <;> simp [indicator, hx, hy]

/-- The indicator of an antipodal family is self-dual, giving the antipodality
hypothesis for `g` in the application of Corollary 1.3. -/
theorem IsAntipodal.dual_indicator {B : Family ι} (hB : B.IsAntipodal) :
    Chvatal.dual B.indicator = B.indicator := by
  funext x
  by_cases hx : x ∈ B
  · simp [Chvatal.dual, indicator, hx, (hB x).mp hx]
  · have hxc : xᶜ ∈ B := by
      by_contra hxc
      exact hx ((hB x).mpr hxc)
    simp [Chvatal.dual, indicator, hx, hxc]

/-- Family duality and Boolean-function duality agree under indicators, as
used when translating the families in Sections 3 and 4. -/
theorem indicator_dual (B : Family ι) :
    B.dual.indicator = Chvatal.dual B.indicator := by
  funext x
  by_cases hx : xᶜ ∈ B <;> simp [indicator, Chvatal.dual, hx]

/-- An antipodal family has uniform density one half, the input to Section 4's
covariance calculation. -/
theorem IsAntipodal.cubeMean_indicator {B : Family ι} (hB : B.IsAntipodal) :
    cubeMean B.indicator = 1 / 2 := by
  have hmean := cubeMean_dual B.indicator
  rw [hB.dual_indicator] at hmean
  linarith

/-- The first counting identity in Section 4: for `f = 1 - 𝟙_D` and
`g = 𝟙_B`, with `B` antipodal, covariance is
`(|D| / 2 - |D ∩ B|) / 2^n`. Heredity is unnecessary for this identity. -/
theorem covariance_one_sub_indicator {D B : Family ι} (hB : B.IsAntipodal) :
    covariance (fun x => 1 - D.indicator x) B.indicator =
      ((D.card : ℝ) / 2 - (D ∩ B).card) / Fintype.card (Finset ι) := by
  have hprod : (fun x => (1 - D.indicator x) * B.indicator x) =
      fun x => B.indicator x - (D ∩ B).indicator x := by
    rw [indicator_inter]
    funext x
    ring
  rw [covariance, hprod, cubeMean_sub, cubeMean_sub, cubeMean_const,
    hB.cubeMean_indicator, cubeMean_indicator, cubeMean_indicator]
  ring

/-- The converse indicator bridge in Section 4: a self-dual family indicator
comes from an antipodal family. -/
theorem isAntipodal_iff_dual_indicator (B : Family ι) :
    B.IsAntipodal ↔ Chvatal.dual B.indicator = B.indicator := by
  refine ⟨IsAntipodal.dual_indicator, ?_⟩
  intro h x
  have hx := congrFun h x
  by_cases hmem : x ∈ B <;> by_cases hcomp : xᶜ ∈ B <;>
    simp_all [Chvatal.dual, indicator]

/-- The support of the value one, used in Section 4 to pass from increasing
Boolean functions back to set families. -/
noncomputable def oneSupport (f : Finset ι → ℝ) : Family ι := by
  classical
  exact Finset.univ.filter (fun x => f x = 1)

/-- Membership in the support used in Section 4's converse implication. -/
@[simp] theorem mem_oneSupport {f : Finset ι → ℝ} {x : Finset ι} :
    x ∈ oneSupport f ↔ f x = 1 := by
  classical
  simp [oneSupport]

/-- Taking the indicator of a Boolean function's support recovers the function,
as required in Section 4's converse construction. -/
theorem indicator_oneSupport {f : Finset ι → ℝ}
    (hf : ∀ x, f x = 0 ∨ f x = 1) : (oneSupport f).indicator = f := by
  funext x
  rcases hf x with hx | hx <;> simp [indicator, hx]

/-- The support of an increasing Boolean function is an increasing family,
the first family construction in Section 4's converse. -/
theorem isIncreasing_oneSupport {f : Finset ι → ℝ}
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hm : Monotone f) :
    (oneSupport f).IsIncreasing := by
  intro x y hxy hx
  have hx' : f x = 1 := mem_oneSupport.mp hx
  rcases hf y with hy | hy
  · have := hm hxy
    rw [hx', hy] at this
    norm_num at this
  · exact mem_oneSupport.mpr hy

/-- The complement of an increasing family is hereditary, used for
`D = supp (1 - f)` in Section 4's converse. -/
theorem IsIncreasing.isHereditary_compl {B : Family ι} (hB : B.IsIncreasing) :
    Bᶜ.IsHereditary := by
  intro x y hxy hy
  simp only [Finset.mem_coe, Finset.mem_compl] at hy ⊢
  exact fun hx => hy (hB hxy hx)

/-- A family indicator is Boolean-valued, as required when invoking
Corollary 1.3 in Section 4. -/
theorem isBoolean_indicator (B : Family ι) : IsBoolean B.indicator := by
  intro x
  by_cases hx : x ∈ B <;> simp [indicator, hx]

/-- The complement indicator `1 - 𝟙_D` used in Section 4 is Boolean-valued. -/
theorem isBoolean_one_sub_indicator (D : Family ι) :
    IsBoolean (fun x => 1 - D.indicator x) := by
  intro x
  by_cases hx : x ∈ D <;> simp [indicator, hx]

/-- Each coordinate sign has uniform mean zero, the cancellation used to count
influences in Section 4. -/
theorem cubeMean_coordinateSign (i : ι) : cubeMean (coordinateSign i) = 0 := by
  have heq : coordinateSign i = fun x => -walsh {i} x := by
    funext x
    rw [walsh_singleton]
    by_cases hx : i ∈ x <;> simp [coordinateSign, hx]
  rw [heq, cubeMean_neg, cubeMean_walsh_of_nonempty (Finset.singleton_nonempty i), neg_zero]

/-- The second counting identity in Section 4: the influence of `1 - 𝟙_D`
is twice the number of boundary edges in coordinate `i`, divided by `2^n`.
The numerator is `|D| - 2 |D_i|`. -/
theorem influence_one_sub_indicator {D : Family ι} (hD : D.IsHereditary) (i : ι) :
    influence (fun x => 1 - D.indicator x) i =
      2 * ((D.card : ℝ) - 2 * (D.star i).card) / Fintype.card (Finset ι) := by
  rw [influence_eq_signed_mean (isBoolean_one_sub_indicator D)
    hD.monotone_one_sub_indicator]
  have heq : (fun x => coordinateSign i x * (1 - D.indicator x)) =
      fun x => coordinateSign i x - (2 * (D.star i).indicator x - D.indicator x) := by
    funext x
    by_cases hmem : x ∈ D <;> by_cases hi : i ∈ x <;>
      norm_num [coordinateSign, indicator, mem_star, hmem, hi]
  rw [heq, cubeMean_sub, cubeMean_coordinateSign, cubeMean_sub,
    cubeMean_mul_left, cubeMean_indicator, cubeMean_indicator]
  ring

/-- The coordinatewise form of equation (17) in Section 4. Taking the minimum
influence and the maximum star size yields the displayed equation in the paper. -/
theorem covariance_sub_quarter_influence {D B : Family ι}
    (hD : D.IsHereditary) (hB : B.IsAntipodal) (i : ι) :
    covariance (fun x => 1 - D.indicator x) B.indicator -
      influence (fun x => 1 - D.indicator x) i / 4 =
      ((D.star i).card - (D ∩ B).card : ℝ) / Fintype.card (Finset ι) := by
  rw [covariance_one_sub_indicator hB, influence_one_sub_indicator hD]
  ring

/-- Equation (17) of Section 4, with its finite minimum of influences and
maximum of star cardinalities. A nonempty coordinate type makes the minimum
well-defined. -/
theorem covariance_sub_quarter_min_influence [Nonempty ι] {D B : Family ι}
    (hD : D.IsHereditary) (hB : B.IsAntipodal) :
    covariance (fun x => 1 - D.indicator x) B.indicator -
      (Finset.univ.inf' Finset.univ_nonempty (influence (fun x => 1 - D.indicator x))) / 4 =
      (((Finset.univ.sup fun i => (D.star i).card : ℕ) : ℝ) - (D ∩ B).card) /
        Fintype.card (Finset ι) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : ι => (D.star i).card) Finset.univ_nonempty
  have hmax : (Finset.univ.sup fun j => (D.star j).card) = (D.star i).card := by
    exact le_antisymm (Finset.sup_le hi) (Finset.le_sup (f := fun j => (D.star j).card)
      (Finset.mem_univ i))
  have hmin : Finset.univ.inf' Finset.univ_nonempty
      (influence (fun x => 1 - D.indicator x)) =
      influence (fun x => 1 - D.indicator x) i := by
    apply le_antisymm (Finset.inf'_le _ (Finset.mem_univ i))
    apply Finset.le_inf'
    intro j hj
    rw [influence_one_sub_indicator hD, influence_one_sub_indicator hD]
    apply div_le_div_of_nonneg_right _ (cube_card_pos (ι := ι)).le
    have hij : ((D.star j).card : ℝ) ≤ (D.star i).card := by exact_mod_cast hi j hj
    linarith
  rw [hmax, hmin]
  exact covariance_sub_quarter_influence hD hB i

/-- Equation (17) turns a coordinate's influence bound into the corresponding
star bound, in either direction. -/
theorem influence_le_four_covariance_iff {D B : Family ι}
    (hD : D.IsHereditary) (hB : B.IsAntipodal) (i : ι) :
    influence (fun x => 1 - D.indicator x) i ≤
        4 * covariance (fun x => 1 - D.indicator x) B.indicator ↔
      (D ∩ B).card ≤ (D.star i).card := by
  have heq := covariance_sub_quarter_influence hD hB i
  constructor
  · intro h
    have hdiv : 0 ≤ ((D.star i).card - (D ∩ B).card : ℝ) /
        Fintype.card (Finset ι) := by rw [← heq]; linarith
    have hnum := (le_div_iff₀ (cube_card_pos (ι := ι))).mp hdiv
    simp only [zero_mul] at hnum
    exact_mod_cast sub_nonneg.mp hnum
  · intro h
    have hreal : ((D ∩ B).card : ℝ) ≤ (D.star i).card := by exact_mod_cast h
    have hdiv := div_nonneg (sub_nonneg.mpr hreal) (le_of_lt (cube_card_pos (ι := ι)))
    rw [← heq] at hdiv
    linarith

/-- The star property asserted for each hereditary family in Theorem 1.1:
every intersecting subfamily is no larger than some star. -/
noncomputable def HasStarProperty (D : Family ι) : Prop :=
  ∀ A : Family ι, A ⊆ D → A.IsIntersecting → ∃ i : ι, A.card ≤ (D.star i).card

end Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The antipodal correlation assertion of Corollary 1.3, expressed with a
coordinate attaining a bound instead of a finite minimum. On a nonempty ground
type this is exactly `Cov(f,g) ≥ (1/4) min_i Inf_i[f]`. This is a proposition,
not an assumption introduced into the logical environment. -/
noncomputable def AntipodalCorrelationBound (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ f g : Finset ι → ℝ, IsBoolean f → Monotone f → IsBoolean g → Monotone g →
    dual g = g → ∃ i : ι, influence f i ≤ 4 * covariance f g

/-- Theorem 1.1 deduced from Corollary 1.3, exactly as in Section 4. The analytic
correlation theorem is an explicit hypothesis: this declaration does not claim
to prove that analytic assertion. -/
theorem chvatal_of_antipodal_correlation [Nonempty ι]
    (hcorr : AntipodalCorrelationBound ι) {D : Family ι} (hD : D.IsHereditary) :
    D.HasStarProperty := by
  intro A hAD hA
  apply Family.exists_star_bound_of_maximal (D := D) (A := A) ?_ hAD hA
  intro B hB
  obtain ⟨i, hi⟩ := hcorr (fun x => 1 - D.indicator x) B.indicator
    (Family.isBoolean_one_sub_indicator D) hD.monotone_one_sub_indicator
    (Family.isBoolean_indicator B) hB.isIncreasing.monotone_indicator
    hB.isAntipodal.dual_indicator
  exact ⟨i, (Family.influence_le_four_covariance_iff hD hB.isAntipodal i).mp hi⟩

/-- Section 4's converse: a star bound for every hereditary family implies the
antipodal correlation bound, using `D = supp(1-f)` and `B = supp(g)`. -/
theorem antipodal_correlation_of_chvatal
    (hstar : ∀ D : Family ι, D.IsHereditary → D.HasStarProperty) :
    AntipodalCorrelationBound ι := by
  intro f g hf hfm hg hgm hdual
  let D : Family ι := (Family.oneSupport f)ᶜ
  let B : Family ι := Family.oneSupport g
  have hD : D.IsHereditary :=
    (Family.isIncreasing_oneSupport hf hfm).isHereditary_compl
  have hfD : (fun x => 1 - D.indicator x) = f := by
    dsimp [D]
    rw [Family.indicator_compl, Family.indicator_oneSupport hf]
    funext x
    ring
  have hgB : B.indicator = g := Family.indicator_oneSupport hg
  have hincB : B.IsIncreasing := Family.isIncreasing_oneSupport hg hgm
  have hantiB : B.IsAntipodal := by
    rw [Family.isAntipodal_iff_dual_indicator, hgB]
    exact hdual
  have hint : (D ∩ B).IsIntersecting :=
    (hincB.isIntersecting_of_isAntipodal hantiB).mono Finset.inter_subset_right
  obtain ⟨i, hi⟩ := hstar D hD (D ∩ B) Finset.inter_subset_left hint
  have hbound := (Family.influence_le_four_covariance_iff hD hantiB i).mpr hi
  rw [hfD, hgB] at hbound
  exact ⟨i, hbound⟩

/-- The equivalence recalled in Section 4 between Chvátal's star assertion and
Corollary 1.3's antipodal correlation assertion. Both sides remain explicit
propositions; no direction relies on an unproved result. -/
theorem chvatal_iff_antipodal_correlation [Nonempty ι] :
    (∀ D : Family ι, D.IsHereditary → D.HasStarProperty) ↔
      AntipodalCorrelationBound ι :=
  ⟨antipodal_correlation_of_chvatal,
    fun h _ hD => chvatal_of_antipodal_correlation h hD⟩

end Chvatal

end

-- LeanPool/Chvatal/Kernel.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The auxiliary kernel and Bessel lower bound

This file proves the kernel calculation (8) and the lower bound (14) in the proof
of Theorem 1.4. All sums are finite and the normalization is made explicit.
-/


open scoped BigOperators symmDiff


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The function `H_y` from Section 3.1, with a general spectral multiplier `q`.
The paper takes `q = g - t`. -/
noncomputable def auxiliaryKernel (F : Family ι) (q : Finset ι → ℝ) (y x : Finset ι) : ℝ :=
  if x ∈ F then (Fintype.card (Finset ι) : ℝ) * fourier q (x ∆ y) else 0

/-- The convolution calculation preceding equation (8), before imposing the
physical support condition on the auxiliary function. -/
theorem sum_mul_fourier_translate (h q : Finset ι → ℝ) (y : Finset ι) :
    (∑ x, h x * fourier q (x ∆ y)) =
      ∑ S, q S * fourier h S * walsh S y := by
  simp only [fourier, cubeMean, mul_div_assoc, Finset.mul_sum, Finset.sum_div,
    Finset.sum_mul, walsh_symmDiff_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro x _
  rw [walsh_comm x S, walsh_comm y S]
  ring

/-- The physical support restriction cancels the indicator and the normalization
in the inner product with `H_y`, as in the first line preceding equation (8). -/
theorem auxiliaryKernel_inner_sum (F : Family ι) (q h : Finset ι → ℝ)
    (y : Finset ι) (hh : ∀ x, x ∉ F → h x = 0) :
    uniformInner h (auxiliaryKernel F q y) = ∑ x, h x * fourier q (x ∆ y) := by
  have heq (x : Finset ι) :
      h x * auxiliaryKernel F q y x =
        (Fintype.card (Finset ι) : ℝ) * (h x * fourier q (x ∆ y)) := by
    by_cases hx : x ∈ F
    · simp only [auxiliaryKernel, if_pos hx]; ring
    · simp [auxiliaryKernel, hx, hh x hx]
  simp only [uniformInner, heq, ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (ne_of_gt (cube_card_pos (ι := ι)))

/-- The spectral form of the inner product calculation in Section 3.1. -/
theorem auxiliaryKernel_inner_fourier (F : Family ι) (q h : Finset ι → ℝ)
    (y : Finset ι) (hh : ∀ x, x ∉ F → h x = 0) :
    uniformInner h (auxiliaryKernel F q y) =
      ∑ S, q S * fourier h S * walsh S y := by
  rw [auxiliaryKernel_inner_sum F q h y hh, sum_mul_fourier_translate]

/-- Equation (8) in its general form: a constant spectral multiplier on the
Fourier support of `h` makes `h` an eigenfunction of the kernel. -/
theorem auxiliaryKernel_inner_eigenvalue (F : Family ι) (q h : Finset ι → ℝ)
    (y : Finset ι) (hh : ∀ x, x ∉ F → h x = 0) (c : ℝ)
    (hc : ∀ S, q S * fourier h S = c * fourier h S) :
    uniformInner h (auxiliaryKernel F q y) = c * h y := by
  rw [auxiliaryKernel_inner_fourier F q h y hh]
  simp_rw [hc, mul_assoc]
  rw [← Finset.mul_sum, fourier_inversion]

/-- Equation (8), first case: Fourier support outside `G` gives eigenvalue `-t`. -/
theorem auxiliaryKernel_inner_outside (F G : Family ι) (h : Finset ι → ℝ)
    (y : Finset ι) (t : ℝ) (hh : h ∈ supportSubspace F Gᶜ) :
    uniformInner h (auxiliaryKernel F (fun S => G.indicator S - t) y) = -t * h y := by
  apply auxiliaryKernel_inner_eigenvalue F _ h y hh.1 (-t)
  intro S
  by_cases hS : S ∈ G
  · rw [hh.2 S (by simpa using hS), mul_zero, mul_zero]
  · simp [Family.indicator, hS]

/-- Equation (8), second case: Fourier support inside `G` gives eigenvalue `1-t`. -/
theorem auxiliaryKernel_inner_inside (F G : Family ι) (h : Finset ι → ℝ)
    (y : Finset ι) (t : ℝ) (hh : h ∈ supportSubspace F G) :
    uniformInner h (auxiliaryKernel F (fun S => G.indicator S - t) y) =
      (1 - t) * h y := by
  apply auxiliaryKernel_inner_eigenvalue F _ h y hh.1 (1 - t)
  intro S
  by_cases hS : S ∈ G
  · simp [Family.indicator, hS]
  · rw [hh.2 S hS, mul_zero, mul_zero]

/-- Equation (7), pointwise norm calculation for the auxiliary kernel. -/
theorem auxiliaryKernel_norm_sq (F : Family ι) (q : Finset ι → ℝ) (y : Finset ι) :
    uniformInner (auxiliaryKernel F q y) (auxiliaryKernel F q y) =
      (Fintype.card (Finset ι) : ℝ) * ∑ x ∈ F, (fourier q (x ∆ y)) ^ 2 := by
  have heq (x : Finset ι) :
      auxiliaryKernel F q y x * auxiliaryKernel F q y x =
        (Fintype.card (Finset ι) : ℝ) ^ 2 *
          (if x ∈ F then (fourier q (x ∆ y)) ^ 2 else 0) := by
    by_cases hx : x ∈ F <;> simp [auxiliaryKernel, hx]
    ring
  simp only [uniformInner, heq, ← Finset.mul_sum]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  rw [pow_two, mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt (cube_card_pos (ι := ι)))]

/-- Equation (7): the squared Fourier kernel on `F × F` is the average,
with factor `2^{-n}`, of the squared norms of the auxiliary kernels. -/
theorem auxiliaryKernel_energy_identity (F : Family ι) (q : Finset ι → ℝ) :
    (∑ x ∈ F, ∑ y ∈ F, fourier q (x ∆ y) ^ 2) =
      (∑ y ∈ F, uniformInner (auxiliaryKernel F q y) (auxiliaryKernel F q y)) /
        Fintype.card (Finset ι) := by
  simp_rw [auxiliaryKernel_norm_sq]
  rw [← Finset.mul_sum,
    mul_div_cancel_left₀ _ (ne_of_gt (cube_card_pos (ι := ι))), Finset.sum_comm]

/-- A probability-unit function supported on `F` has unnormalized squared sum
`2^n` on `F`, as used immediately before equation (14). -/
theorem sum_sq_of_supported_unit (F : Family ι) (h : Finset ι → ℝ)
    (hh : ∀ x, x ∉ F → h x = 0) (hunit : uniformInner h h = 1) :
    ∑ x ∈ F, h x ^ 2 = (Fintype.card (Finset ι) : ℝ) := by
  have hsum : (∑ x ∈ F, h x ^ 2) = ∑ x, h x ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ F)
    intro x _ hx
    simp [hh x hx]
  rw [hsum]
  simp only [uniformInner, ← pow_two] at hunit
  exact (div_eq_one_iff_eq (ne_of_gt (cube_card_pos (ι := ι)))).mp hunit

/-- Equation (14): Bessel's inequality applied to the two auxiliary families
gives the sharp lower bound on the squared Fourier kernel restricted to `F × F`.
No positivity assumptions on `t` or nonemptiness assumptions on the families
are needed. -/
theorem auxiliaryKernel_bessel_bound (F G : Family ι)
    (hF : F.IsIncreasing) (hG : G.IsIncreasing) (t : ℝ) :
    t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card ≤
      ∑ x ∈ F, ∑ y ∈ F, (fourier (fun S => G.indicator S - t) (x ∆ y)) ^ 2 := by
  classical
  obtain ⟨u, v, huv, humem, hvmem⟩ := auxiliary_orthonormal_system F G hF hG
  have huunit (i) : uniformInner (u i) (u i) = 1 := by
    simpa using huv (Sum.inl i) (Sum.inl i)
  have hvunit (j) : uniformInner (v j) (v j) = 1 := by
    simpa using huv (Sum.inr j) (Sum.inr j)
  have hu_sq (i) : ∑ y ∈ F, u i y ^ 2 = (Fintype.card (Finset ι) : ℝ) :=
    sum_sq_of_supported_unit F _ (humem i).1 (huunit i)
  have hv_sq (j) : ∑ y ∈ F, v j y ^ 2 = (Fintype.card (Finset ι) : ℝ) :=
    sum_sq_of_supported_unit F _ (hvmem j).1 (hvunit j)
  have hpoint (y : Finset ι) :
      t ^ 2 * (∑ i, u i y ^ 2) + (1 - t) ^ 2 * (∑ j, v j y ^ 2) ≤
        (Fintype.card (Finset ι) : ℝ) *
          ∑ x ∈ F, (fourier (fun S => G.indicator S - t) (x ∆ y)) ^ 2 := by
    have hb := bessel_inequality (Sum.elim u v) huv
      (auxiliaryKernel F (fun S => G.indicator S - t) y)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      auxiliaryKernel_inner_outside F G _ y t (humem _),
      auxiliaryKernel_inner_inside F G _ y t (hvmem _),
      mul_pow, neg_sq, ← Finset.mul_sum, auxiliaryKernel_norm_sq] at hb
    exact hb
  have hsum := Finset.sum_le_sum (fun y (_hy : y ∈ F) => hpoint y)
  have hleft :
      (∑ y ∈ F, (t ^ 2 * (∑ i, u i y ^ 2) + (1 - t) ^ 2 * (∑ j, v j y ^ 2))) =
        (Fintype.card (Finset ι) : ℝ) *
          (t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_comm (s := F), Finset.sum_comm (s := F)]
    simp only [hu_sq, hv_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul]
    ring
  rw [hleft, ← Finset.mul_sum, Finset.sum_comm (s := F)] at hsum
  exact le_of_mul_le_mul_left hsum (cube_card_pos (ι := ι))

end Chvatal

end

-- LeanPool/Chvatal/Correlation.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The quadratic correlation inequality

This file follows Section 3.2 of arXiv:2609.19123: spectral flip energy is written
as a boundary sum, a constant is subtracted from the second function, and the
auxiliary orthonormal system bounds the resulting interior sum.
-/


open scoped BigOperators symmDiff


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Summing against a family indicator restricts a sum to that family, as in (11). -/
theorem sum_indicator_mul (F : Family ι) (h : Finset ι → ℝ) :
    (∑ x, F.indicator x * h x) = ∑ x ∈ F, h x := by
  simp [Family.indicator, ite_mul]

/-- Summing a symmetric kernel against the squared change of an indicator counts
each boundary pair twice. This is the Boolean step in equation (11). -/
theorem indicator_boundary_sum (F : Family ι) (k : Finset ι → Finset ι → ℝ)
    (hk : ∀ x y, k x y = k y x) :
    (∑ x, ∑ y, (F.indicator x - F.indicator y) ^ 2 * k x y) =
      2 * ∑ x ∈ F, ∑ y ∈ Fᶜ, k x y := by
  have hpoint (x y : Finset ι) :
      (F.indicator x - F.indicator y) ^ 2 * k x y =
        F.indicator x * Fᶜ.indicator y * k x y +
          F.indicator y * Fᶜ.indicator x * k y x := by
    rw [hk y x]
    by_cases hx : x ∈ F <;> by_cases hy : y ∈ F <;>
      simp [Family.indicator, hx, hy]
  have hcross : (∑ x, ∑ y, F.indicator x * Fᶜ.indicator y * k x y) =
      ∑ x ∈ F, ∑ y ∈ Fᶜ, k x y := by
    simp_rw [mul_assoc, ← Finset.mul_sum, sum_indicator_mul]
  have hcross' : (∑ x, ∑ y, F.indicator y * Fᶜ.indicator x * k y x) =
      ∑ x ∈ F, ∑ y ∈ Fᶜ, k x y := by
    rw [Finset.sum_comm]
    exact hcross
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [hcross, hcross']
  ring

/-- Equation (11), its first equality: the odd-intersection spectral sum is one
half of the Fourier-weighted flip energy. -/
theorem two_spectral_eq_weighted_flip (f g : Finset ι → ℝ) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier f S ^ 2 * fourier g T ^ 2) =
      (1 / 2 : ℝ) * ∑ T, fourier g T ^ 2 *
        cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) := by
  simp_rw [flip_energy_odd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro S hS
  ring

/-- Equation (11), the boundary formula for a family indicator. -/
theorem two_spectral_eq_boundary (F : Family ι) (g : Finset ι → ℝ) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier F.indicator S ^ 2 * fourier g T ^ 2) =
      (∑ x ∈ F, ∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) /
        Fintype.card (Finset ι) := by
  rw [two_spectral_eq_weighted_flip, weighted_flip_energy, cubeMean,
    indicator_boundary_sum F (fun x y => fourier g (x ∆ y) ^ 2)
      (fun x y => by rw [symmDiff_comm])]
  ring

/-- Equation (12): the Fourier kernel across a family boundary is unchanged
when a constant is subtracted from the function. -/
theorem boundary_sub_const (F : Family ι) (g : Finset ι → ℝ) (t : ℝ) :
    (∑ x ∈ F, ∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) =
      ∑ x ∈ F, ∑ y ∈ Fᶜ, fourier (fun z => g z - t) (x ∆ y) ^ 2 := by
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hne : x ∆ y ≠ ∅ := by
    intro h
    have hxy : x = y := (show x ∆ y = ∅ ↔ x = y from symmDiff_eq_bot).mp h
    subst y
    exact (Finset.mem_compl.mp hy) hx
  rw [fourier_sub, fourier_const, if_neg hne, sub_zero]

/-- Reindexing the squared Fourier kernel gives the Parseval norm, the first
step in equation (13). -/
theorem sum_fourier_kernel_sq (g : Finset ι → ℝ) (x : Finset ι) :
    (∑ y, fourier g (x ∆ y) ^ 2) = cubeMean (fun z => g z ^ 2) := by
  rw [parseval]
  exact (show Function.Involutive (fun y : Finset ι => x ∆ y) from
    fun y => symmDiff_symmDiff_cancel_left x y).bijective.sum_comp
      (fun y => fourier g y ^ 2)

/-- Equation (13): boundary energy equals total energy minus interior energy. -/
theorem boundary_eq_total_sub_interior (F : Family ι) (g : Finset ι → ℝ) :
    (∑ x ∈ F, ∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) =
      F.card * cubeMean (fun z => g z ^ 2) -
        ∑ x ∈ F, ∑ y ∈ F, fourier g (x ∆ y) ^ 2 := by
  have hsplit (x : Finset ι) :
      (∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) +
        (∑ y ∈ F, fourier g (x ∆ y) ^ 2) = cubeMean (fun z => g z ^ 2) := by
    rw [Finset.sum_compl_add_sum, sum_fourier_kernel_sq]
  have h := congrArg (fun h : Finset ι → ℝ => ∑ x ∈ F, h x) (funext hsplit)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h
  linarith

/-- A shifted Boolean function's squared norm, used after equation (14). -/
theorem boolean_sub_const_norm {g : Finset ι → ℝ} (hg : IsBoolean g) (t : ℝ) :
    cubeMean (fun z => (g z - t) ^ 2) =
      (1 - t) ^ 2 * cubeMean g + t ^ 2 * (1 - cubeMean g) := by
  have hp (z : Finset ι) : (g z - t) ^ 2 =
      (1 - t) ^ 2 * g z + t ^ 2 * (1 - g z) := by
    rcases hg z with hz | hz <;> rw [hz] <;> ring
  simp_rw [hp]
  rw [cubeMean_add, cubeMean_mul_left, cubeMean_mul_left, cubeMean_sub, cubeMean_const]

/-- The density of a family difference is the difference of the corresponding
indicator means, used to convert equation (14) into covariance. -/
theorem card_sdiff_div_cube (F G : Family ι) :
    ((F \ G).card : ℝ) / Fintype.card (Finset ι) =
      cubeMean F.indicator - cubeMean (fun x => F.indicator x * G.indicator x) := by
  rw [← Family.indicator_inter, Family.cubeMean_indicator, Family.cubeMean_indicator,
    ← sub_div]
  congr 1
  have h : ((F \ G).card : ℝ) + (F ∩ G).card = F.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter F G
  linarith

/-- The final algebra in Section 3.2: the total shifted norm minus the two
auxiliary-family dimensions equals a quadratic combination of covariances. -/
theorem shifted_dimension_covariance (F G : Family ι) (t : ℝ) :
    (F.card * cubeMean (fun z => (G.indicator z - t) ^ 2) -
      (t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card)) /
        Fintype.card (Finset ι) =
      t ^ 2 * covariance F.indicator G.indicator +
        (1 - t) ^ 2 * covariance F.indicator (dual G.indicator) := by
  rw [boolean_sub_const_norm (Family.isBoolean_indicator G)]
  simp only [sub_div, add_div]
  simp_rw [mul_div_assoc]
  rw [card_sdiff_div_cube, card_sdiff_div_cube, Family.indicator_dual]
  have he (a : ℝ) : (F.card : ℝ) * (a / Fintype.card (Finset ι)) =
      cubeMean F.indicator * a := by
    rw [Family.cubeMean_indicator]
    ring
  rw [he]
  unfold covariance
  rw [cubeMean_dual]
  ring

/-- The last step of Section 3.2, isolating how the interior-kernel estimate (14)
combines with the boundary identities (11)–(13). -/
theorem two_spectral_le_of_interior_bound (F G : Family ι) (t : ℝ)
    (hinterior : t ^ 2 * (F \ G).card + (1 - t) ^ 2 * (F \ G.dual).card ≤
      ∑ x ∈ F, ∑ y ∈ F, fourier (fun z => G.indicator z - t) (x ∆ y) ^ 2) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier F.indicator S ^ 2 * fourier G.indicator T ^ 2) ≤
      t ^ 2 * covariance F.indicator G.indicator +
        (1 - t) ^ 2 * covariance F.indicator (dual G.indicator) := by
  rw [two_spectral_eq_boundary, boundary_sub_const F G.indicator t,
    boundary_eq_total_sub_interior, ← shifted_dimension_covariance]
  exact div_le_div_of_nonneg_right (sub_le_sub_left hinterior _)
    (le_of_lt (cube_card_pos (ι := ι)))

/-- Theorem 1.4, equation (3): for every real `t`, twice the odd-intersection
Fourier energy is bounded by the indicated quadratic combination of covariances.
The proof includes empty supports and an empty coordinate type. -/
theorem two_spectral_le_quadratic_covariance {f g : Finset ι → ℝ}
    (hf : IsBoolean f) (hmf : Monotone f) (hg : IsBoolean g) (hmg : Monotone g)
    (t : ℝ) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier f S ^ 2 * fourier g T ^ 2) ≤
      t ^ 2 * covariance f g + (1 - t) ^ 2 * covariance f (dual g) := by
  have h := two_spectral_le_of_interior_bound (Family.oneSupport f) (Family.oneSupport g) t
    (auxiliaryKernel_bessel_bound (Family.oneSupport f) (Family.oneSupport g)
      (Family.isIncreasing_oneSupport hf hmf) (Family.isIncreasing_oneSupport hg hmg) t)
  simpa only [Family.indicator_oneSupport hf, Family.indicator_oneSupport hg] using h

end Chvatal

end

-- LeanPool/Chvatal/Optimization.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The one-variable optimization in Section 3.3

These elementary real inequalities isolate the optimization used to deduce Theorem 1.2
from Theorem 1.4 of Chang–Liu–Liu, arXiv:2609.19123v1. Real division in Lean assigns
`0 / 0 = 0`, agreeing with the convention in the footnote to Theorem 1.2.
-/


namespace Chvatal

/-- Section 3.3: completing the square in the parameter of Theorem 1.4. -/
theorem quadratic_covariance_identity (a b t : ℝ) (hab : a + b ≠ 0) :
    t ^ 2 * a + (1 - t) ^ 2 * b =
      a * b / (a + b) + (a + b) * (t - b / (a + b)) ^ 2 := by
  field_simp
  ring

/-- Section 3.3: the optimal parameter is `b / (a + b)` when the denominator is nonzero. -/
theorem quadratic_covariance_minimizer (a b : ℝ) (hab : a + b ≠ 0) :
    (b / (a + b)) ^ 2 * a + (1 - b / (a + b)) ^ 2 * b = a * b / (a + b) := by
  rw [quadratic_covariance_identity a b _ hab]
  ring

/-- Section 3.3: optimize the bound for every parameter, including the zero-denominator case.

In the application, `a` and `b` are the two covariances and `c` is twice the sum over
pairs of Fourier indices with odd intersection in Theorem 1.4. -/
theorem le_harmonic_half_of_quadratic_bound {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, c ≤ t ^ 2 * a + (1 - t) ^ 2 * b) :
    c ≤ a * b / (a + b) := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simpa [ha0, hb0] using h 0
  · simpa [quadratic_covariance_minimizer a b hab] using h (b / (a + b))

/-- The algebraic last step of Theorem 1.2: combine (16) with the optimized Theorem 1.4. -/
theorem le_harmonic_of_spectral_bound {a b c w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : w ≤ 2 * c) (h : ∀ t : ℝ, c ≤ t ^ 2 * a + (1 - t) ^ 2 * b) :
    w ≤ 2 * a * b / (a + b) := by
  have hc := le_harmonic_half_of_quadratic_bound ha hb h
  calc
    w ≤ 2 * c := hw
    _ ≤ 2 * (a * b / (a + b)) := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = 2 * a * b / (a + b) := by ring

/-- Corollary 1.3: the harmonic mean of two equal nonnegative covariances is that covariance. -/
theorem harmonic_self (a : ℝ) : 2 * a * a / (a + a) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · field_simp
    ring

end Chvatal

end

-- LeanPool/Chvatal/Spectral.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Ordered influence weights in the sharp correlation inequality

This file defines the left-hand side `𝒲(f,g)` of Theorem 1.2 and proves the
comparison (16) from Lemma 3.3. It also records the variance argument in
Corollary 1.3. The parameter optimization is in `Chvatal.Optimization`.
-/


open scoped BigOperators symmDiff


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The largest influence over a Fourier index, as in Theorem 1.2.
The empty index is assigned zero so that sums can run over the entire cube. -/
noncomputable def maxInfluence (f : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  if h : S.Nonempty then S.sup' h (influence f) else 0

/-- The empty Fourier index makes no contribution to Theorem 1.2. -/
@[simp] theorem maxInfluence_empty (f : Finset ι → ℝ) : maxInfluence f ∅ = 0 := by
  simp [maxInfluence]

/-- On a nonempty index, the influence weight is the ordinary finite maximum. -/
theorem maxInfluence_of_nonempty (f : Finset ι → ℝ) {S : Finset ι} (hS : S.Nonempty) :
    maxInfluence f S = S.sup' hS (influence f) := by simp [maxInfluence, hS]

/-- Every coordinate in an index is bounded by its maximum influence. -/
theorem influence_le_maxInfluence (f : Finset ι → ℝ) {S : Finset ι} {i : ι}
    (hi : i ∈ S) : influence f i ≤ maxInfluence f S := by
  rw [maxInfluence_of_nonempty f ⟨i, hi⟩]
  exact Finset.le_sup' (influence f) hi

/-- The spectral weights in Theorem 1.2 are nonnegative. -/
theorem maxInfluence_nonneg (f : Finset ι → ℝ) (S : Finset ι) : 0 ≤ maxInfluence f S := by
  by_cases hS : S.Nonempty
  · obtain ⟨i, hi⟩ := hS
    exact (influence_nonneg f i).trans (influence_le_maxInfluence f hi)
  · simp [maxInfluence, hS]

/-- Lemma 3.3 in its stated maximum-over-coordinates form. -/
theorem maxInfluence_le_flip_energy {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (T : Finset ι) :
    maxInfluence f T ≤ cubeMean (fun x => (f x - f (x ∆ T)) ^ 2) := by
  by_cases hT : T.Nonempty
  · rw [maxInfluence_of_nonempty f hT, Finset.sup'_le_iff]
    intro i hi
    exact influence_le_flip_energy hf hm hi
  · rw [maxInfluence, dif_neg hT]
    exact cubeMean_nonneg fun _ => sq_nonneg _

/-- Lemma 3.3, equation (15): maximum influence is bounded by the odd-intersection
Fourier energy. The formula also holds for the empty index under our zero convention. -/
theorem maxInfluence_le_odd_spectral {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (T : Finset ι) :
    maxInfluence f T ≤ 4 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier f S ^ 2 := by
  rw [← flip_energy_odd]
  exact maxInfluence_le_flip_energy hf hm T

/-- The spectral expression `𝒲(f,g)` in Theorem 1.2 and Section 5.
Its empty-index term vanishes by `maxInfluence_empty`. -/
noncomputable def spectralWeight (f g : Finset ι → ℝ) : ℝ :=
  ∑ S, fourier g S ^ 2 * maxInfluence f S

/-- The expression `spectralWeight` agrees with the paper's sum over nonempty indices. -/
theorem spectralWeight_eq_sum_nonempty (f g : Finset ι → ℝ) :
    spectralWeight f g = ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
      fourier g S ^ 2 * maxInfluence f S := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Finset ι))
    (fun S => fourier g S ^ 2 * maxInfluence f S) (Finset.mem_univ (∅ : Finset ι))
  simp only [maxInfluence_empty, mul_zero, add_zero] at h
  exact h.symm

/-- Nonnegativity of the left side of Theorem 1.2, used when a covariance vanishes. -/
theorem spectralWeight_nonneg (f g : Finset ι → ℝ) : 0 ≤ spectralWeight f g := by
  exact Finset.sum_nonneg fun S _ => mul_nonneg (sq_nonneg _) (maxInfluence_nonneg f S)

/-- Equation (16): multiply Lemma 3.3 by the squared Fourier coefficient and sum. -/
theorem spectralWeight_le_four_spectral {f : Finset ι → ℝ} (hf : IsBoolean f)
    (hm : Monotone f) (g : Finset ι → ℝ) :
    spectralWeight f g ≤ 4 * ∑ T,
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
        fourier f S ^ 2 * fourier g T ^ 2 := by
  unfold spectralWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  calc
    fourier g T ^ 2 * maxInfluence f T ≤
        fourier g T ^ 2 * (4 * ∑ S ∈ Finset.univ.filter
          (fun S : Finset ι => Odd (S ∩ T).card), fourier f S ^ 2) :=
      mul_le_mul_of_nonneg_left (maxInfluence_le_odd_spectral hf hm T) (sq_nonneg _)
    _ = 4 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
        fourier f S ^ 2 * fourier g T ^ 2 := by
      rw [← Finset.sum_mul]
      ring

/-- The Parseval computation in Corollary 1.3: nonconstant Fourier coefficients
of an antipodal Boolean function have total squared mass one quarter. -/
theorem fourier_mass_of_antipodal {g : Finset ι → ℝ} (hb : IsBoolean g)
    (hg : dual g = g) :
    (∑ S ∈ Finset.univ.erase (∅ : Finset ι), fourier g S ^ 2) = 1 / 4 := by
  simpa [covariance_fourier, pow_two] using variance_eq_quarter_of_antipodal hb hg

/-- The lower bound on `𝒲(f,g)` used in Corollary 1.3. Any common lower bound
on the coordinate influences is weighted by the variance `1/4`. -/
theorem quarter_le_spectralWeight {f g : Finset ι → ℝ} {m : ℝ}
    (hb : IsBoolean g) (hg : dual g = g) (hm : ∀ i, m ≤ influence f i) :
    m / 4 ≤ spectralWeight f g := by
  calc
    m / 4 = (∑ S ∈ Finset.univ.erase (∅ : Finset ι), fourier g S ^ 2) * m := by
      rw [fourier_mass_of_antipodal hb hg]
      ring
    _ = ∑ S ∈ Finset.univ.erase (∅ : Finset ι), fourier g S ^ 2 * m :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
        fourier g S ^ 2 * maxInfluence f S := by
      apply Finset.sum_le_sum
      intro S hS
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
      exact mul_le_mul_of_nonneg_left ((hm i).trans (influence_le_maxInfluence f hi))
        (sq_nonneg _)
    _ = spectralWeight f g := (spectralWeight_eq_sum_nonempty f g).symm

end Chvatal

end

-- LeanPool/Chvatal/Main.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Chvátal's conjecture and the sharp correlation inequality

The main results of Chang–Liu–Liu, arXiv:2609.19123v1:

* `sharp_correlation`: Theorem 1.2, the sharp harmonic-mean bound.
* `antipodal_correlation`: Corollary 1.3, the minimum-influence bound.
* `chvatal`: Theorem 1.1, the star bound for hereditary families.

Theorem 1.4 is `two_spectral_le_quadratic_covariance` in `Chvatal.Correlation`.
The analytic statements allow an empty coordinate type. Statements involving a
minimum coordinate or a star center explicitly require a nonempty coordinate type.
-/


open scoped BigOperators


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonnegativity of covariance for increasing Boolean functions, recalled after
Theorem 1.2. Here it follows directly by setting `t = 1` in Theorem 1.4. -/
theorem covariance_nonneg {f g : Finset ι → ℝ} (hf : IsBoolean f) (hmf : Monotone f)
    (hg : IsBoolean g) (hmg : Monotone g) : 0 ≤ covariance f g := by
  classical
  have hs : 0 ≤ 2 * (∑ T, ∑ S ∈ Finset.univ.filter
      (fun S : Finset ι => Odd (S ∩ T).card), fourier f S ^ 2 * fourier g T ^ 2) := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun T _ =>
      Finset.sum_nonneg fun S _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have h := two_spectral_le_quadratic_covariance hf hmf hg hmg 1
  norm_num at h
  exact hs.trans h

/-- Theorem 1.2, equation (1): the sharp correlation inequality.
The denominator-zero convention in the paper agrees with Lean's real division. -/
theorem sharp_correlation {f g : Finset ι → ℝ} (hf : IsBoolean f) (hmf : Monotone f)
    (hg : IsBoolean g) (hmg : Monotone g) :
    spectralWeight f g ≤
      2 * covariance f g * covariance f (dual g) /
        (covariance f g + covariance f (dual g)) := by
  apply le_harmonic_of_spectral_bound
    (covariance_nonneg hf hmf hg hmg)
    (covariance_nonneg hf hmf hg.dual (monotone_dual hmg))
    (c := 2 * ∑ T, ∑ S ∈ Finset.univ.filter
      (fun S : Finset ι => Odd (S ∩ T).card), fourier f S ^ 2 * fourier g T ^ 2)
  · have h := spectralWeight_le_four_spectral hf hmf g
    linarith
  · exact two_spectral_le_quadratic_covariance hf hmf hg hmg

/-- The antipodal specialization of Theorem 1.2 used in Corollary 1.3 and Proposition 5.3. -/
theorem antipodal_spectral_bound {f g : Finset ι → ℝ} (hf : IsBoolean f)
    (hmf : Monotone f) (hg : IsBoolean g) (hmg : Monotone g) (hdual : dual g = g) :
    spectralWeight f g ≤ covariance f g := by
  have h := sharp_correlation hf hmf hg hmg
  rwa [hdual, harmonic_self] at h

/-- The minimum coordinate influence appearing in Corollary 1.3.
A nonempty coordinate type is required to choose a minimum. -/
noncomputable def minInfluence [Nonempty ι] (f : Finset ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (influence f)

/-- The minimum influence is no larger than any coordinate influence. -/
theorem minInfluence_le [Nonempty ι] (f : Finset ι → ℝ) (i : ι) :
    minInfluence f ≤ influence f i :=
  Finset.inf'_le (influence f) (Finset.mem_univ i)

/-- Corollary 1.3, equation (2): the Friedgut–Kahn–Kalai–Keller correlation bound. -/
theorem antipodal_correlation [Nonempty ι] {f g : Finset ι → ℝ} (hf : IsBoolean f)
    (hmf : Monotone f) (hg : IsBoolean g) (hmg : Monotone g) (hdual : dual g = g) :
    minInfluence f / 4 ≤ covariance f g :=
  (quarter_le_spectralWeight hg hdual (minInfluence_le f)).trans
    (antipodal_spectral_bound hf hmf hg hmg hdual)

/-- Corollary 1.3 in the existential coordinate form used by the Section 4 counting reduction. -/
theorem antipodal_correlation_bound [Nonempty ι] : AntipodalCorrelationBound ι := by
  intro f g hf hmf hg hmg hdual
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (influence f) Finset.univ_nonempty
  have h := (quarter_le_spectralWeight hg hdual (fun j => hi j (Finset.mem_univ j))).trans
    (antipodal_spectral_bound hf hmf hg hmg hdual)
  exact ⟨i, by linarith⟩

/-- Theorem 1.1: every intersecting subfamily of a hereditary family is bounded
in cardinality by a star of that hereditary family. -/
theorem chvatal [Finite ι] [Nonempty ι] {D A : Family ι} (hD : D.IsHereditary)
    (hAD : A ⊆ D) (hA : A.IsIntersecting) :
    ∃ i : ι, A.card ≤ (D.star i).card := by
  let : Fintype ι := Fintype.ofFinite ι
  exact chvatal_of_antipodal_correlation antipodal_correlation_bound hD A hAD hA

/-- The abstract's formulation of Theorem 1.1: a single star is a largest
intersecting subfamily of the given hereditary family. -/
theorem exists_largest_intersecting_star [Finite ι] [Nonempty ι] {D : Family ι}
    (hD : D.IsHereditary) :
    ∃ i : ι, (D.star i).IsIntersecting ∧
      ∀ A : Family ι, A ⊆ D → A.IsIntersecting → A.card ≤ (D.star i).card := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : ι => (D.star i).card) Finset.univ_nonempty
  refine ⟨i, Family.star_isIntersecting D i, ?_⟩
  intro A hAD hA
  obtain ⟨j, hj⟩ := chvatal hD hAD hA
  exact hj.trans (hi j (Finset.mem_univ j))

end Chvatal

end

-- LeanPool/Chvatal/Sharpness.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Sharpness and the two-coordinate counterexample

This file formalizes Proposition 5.1 and Remark 5.2 of arXiv:2609.19123.
The AND function is the indicator of the top cube point; OR is its dual.
-/


open scoped BigOperators symmDiff


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The function `AND_n` in Section 5: all coordinates must equal one. -/
noncomputable def andFunction (x : Finset ι) : ℝ := if x = Finset.univ then 1 else 0

/-- The function `OR_n` in Section 5, defined as the dual of `AND_n`. -/
noncomputable def orFunction : Finset ι → ℝ := dual andFunction

/-- AND is Boolean, as required for the sharpness examples in Section 5. -/
theorem isBoolean_andFunction : IsBoolean (andFunction (ι := ι)) := by
  intro x
  simp only [andFunction]
  split_ifs <;> simp

/-- AND is increasing, as required for Proposition 5.1. -/
theorem monotone_andFunction : Monotone (andFunction (ι := ι)) := by
  intro x y hxy
  by_cases hx : x = Finset.univ
  · subst x
    have hy : y = Finset.univ := Finset.univ_subset_iff.mp hxy
    simp [hy, andFunction]
  · simp only [andFunction, if_neg hx]
    split_ifs <;> norm_num

/-- OR is Boolean, as required for Remark 5.2. -/
theorem isBoolean_orFunction : IsBoolean (orFunction (ι := ι)) :=
  isBoolean_andFunction.dual

/-- OR is increasing, as required for Remark 5.2. -/
theorem monotone_orFunction : Monotone (orFunction (ι := ι)) :=
  monotone_dual monotone_andFunction

/-- Integrating against AND evaluates at the top point, the counting calculation
in Proposition 5.1. -/
theorem cubeMean_andFunction_mul (g : Finset ι → ℝ) :
    cubeMean (fun x => andFunction x * g x) =
      g Finset.univ / Fintype.card (Finset ι) := by
  simp [cubeMean, andFunction, ite_mul]

/-- The quantity `a = 2^{-n}` in Proposition 5.1 is the mean of AND. -/
theorem cubeMean_andFunction :
    cubeMean (andFunction (ι := ι)) = 1 / Fintype.card (Finset ι) := by
  simp [cubeMean, andFunction]

/-- Every coordinate of AND has influence `2a`, as computed in Proposition 5.1. -/
theorem influence_andFunction (i : ι) :
    influence andFunction i = 2 / Fintype.card (Finset ι) := by
  have ht : (Finset.univ : Finset ι) ∆ {i} ≠ Finset.univ := by
    intro h
    have hi : i ∈ (Finset.univ : Finset ι) ∆ {i} := h.symm ▸ Finset.mem_univ i
    simp [Finset.mem_symmDiff] at hi
  have hp (x : Finset ι) : (andFunction x - andFunction (x ∆ {i})) ^ 2 =
      andFunction x + andFunction (x ∆ {i}) := by
    by_cases hx : x = Finset.univ
    · subst x
      simp [andFunction, ht]
    · simp only [andFunction, if_neg hx]
      split_ifs <;> norm_num
  unfold influence
  simp_rw [hp]
  rw [cubeMean_add, cubeMean_symmDiff, cubeMean_andFunction]
  ring

/-- AND has the same maximum influence on every nonempty Fourier index. -/
theorem maxInfluence_andFunction {S : Finset ι} (hS : S.Nonempty) :
    maxInfluence andFunction S = 2 / Fintype.card (Finset ι) := by
  rw [maxInfluence_of_nonempty _ hS]
  simp_rw [influence_andFunction]
  exact Finset.sup'_const hS (2 / (Fintype.card (Finset ι) : ℝ))

/-- Proposition 5.1: the AND spectral weight is `2a` times the variance of `g`. -/
theorem spectralWeight_andFunction (g : Finset ι → ℝ) :
    spectralWeight andFunction g =
      (2 / Fintype.card (Finset ι)) * covariance g g := by
  rw [spectralWeight_eq_sum_nonempty, covariance_fourier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [maxInfluence_andFunction
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)]
  ring

/-- The variance of a Boolean function is `b(1-b)`, the Parseval calculation
used in Proposition 5.1. -/
theorem covariance_self_boolean {g : Finset ι → ℝ} (hg : IsBoolean g) :
    covariance g g = cubeMean g * (1 - cubeMean g) := by
  have hsq : (fun x => g x * g x) = g := by
    funext x
    simpa [pow_two] using hg.sq x
  rw [covariance, hsq]
  ring

/-- The covariance of AND with any function, prior to using the endpoint values
in Proposition 5.1. -/
theorem covariance_andFunction (g : Finset ι → ℝ) :
    covariance andFunction g =
      (1 / Fintype.card (Finset ι)) * (g Finset.univ - cubeMean g) := by
  rw [covariance, cubeMean_andFunction_mul, cubeMean_andFunction]
  ring

/-- The covariance of AND with the dual, in the endpoint form used by
Proposition 5.1. -/
theorem covariance_andFunction_dual (g : Finset ι → ℝ) :
    covariance andFunction (dual g) =
      (1 / Fintype.card (Finset ι)) * (cubeMean g - g ∅) := by
  rw [covariance_andFunction, cubeMean_dual]
  simp only [dual, Finset.compl_univ]
  ring

/-- An increasing Boolean function is constant or has the two endpoint values
used in the nonconstant case of Proposition 5.1. -/
theorem monotone_boolean_endpoints {g : Finset ι → ℝ} (hg : IsBoolean g)
    (hm : Monotone g) :
    g = (fun _ => 0) ∨ g = (fun _ => 1) ∨ (g ∅ = 0 ∧ g Finset.univ = 1) := by
  rcases hg Finset.univ with htop | htop
  · left
    funext x
    have hle := hm (Finset.subset_univ x)
    have hnonneg := hg.nonneg x
    simp only [htop] at hle
    linarith
  · rcases hg ∅ with hbot | hbot
    · exact Or.inr (Or.inr ⟨hbot, htop⟩)
    · right; left
      funext x
      have hle := hm (Finset.empty_subset x)
      rcases hg x with hx | hx
      · rw [hbot, hx] at hle
        norm_num at hle
      · exact hx

/-- Proposition 5.1: AND attains equality in the harmonic correlation bound
for every increasing Boolean second function, including constant functions. -/
theorem andFunction_sharp {g : Finset ι → ℝ} (hg : IsBoolean g) (hm : Monotone g) :
    spectralWeight andFunction g =
      2 * covariance andFunction g * covariance andFunction (dual g) /
        (covariance andFunction g + covariance andFunction (dual g)) := by
  rw [spectralWeight_andFunction, covariance_self_boolean hg,
    covariance_andFunction, covariance_andFunction_dual]
  rcases monotone_boolean_endpoints hg hm with h | h | ⟨hbot, htop⟩
  · subst g
    simp
  · subst g
    simp
  · rw [hbot, htop]
    have hN : (Fintype.card (Finset ι) : ℝ) ≠ 0 := ne_of_gt cube_card_pos
    have hsum : (1 / (Fintype.card (Finset ι) : ℝ)) * (1 - cubeMean g) +
        (1 / (Fintype.card (Finset ι) : ℝ)) * (cubeMean g - 0) =
        1 / Fintype.card (Finset ι) := by ring
    rw [hsum]
    field_simp
    ring

/-- The mean of OR is `1 - 2^{-n}`, used in Remark 5.2. -/
theorem cubeMean_orFunction :
    cubeMean (orFunction (ι := ι)) = 1 - 1 / Fintype.card (Finset ι) := by
  rw [orFunction, cubeMean_dual, cubeMean_andFunction]

/-- OR vanishes at the bottom cube point, including in dimension zero. -/
@[simp] theorem orFunction_empty : orFunction (∅ : Finset ι) = 0 := by
  simp [orFunction, dual, andFunction]

/-- OR is one at the top when there is at least one coordinate. -/
@[simp] theorem orFunction_univ [Nonempty ι] :
    orFunction (Finset.univ : Finset ι) = 1 := by
  simp [orFunction, dual, andFunction, Finset.univ_nonempty.ne_empty.symm]

/-- Remark 5.2: the exact two-coordinate AND/OR counterexample. The spectral
weight exceeds covariance, so removing antipodality from the stronger bound fails. -/
theorem and_or_two_example :
    covariance (andFunction (ι := Fin 2)) orFunction = 1 / 16 ∧
    covariance (andFunction (ι := Fin 2)) (dual orFunction) = 3 / 16 ∧
    spectralWeight (andFunction (ι := Fin 2)) orFunction = 3 / 32 ∧
    covariance (andFunction (ι := Fin 2)) orFunction <
      spectralWeight (andFunction (ι := Fin 2)) orFunction := by
  norm_num [covariance_andFunction, covariance_andFunction_dual,
    spectralWeight_andFunction, covariance_self_boolean isBoolean_orFunction,
    cubeMean_orFunction, Fintype.card_finset]
  norm_num [dual]

/-- On a single coordinate AND is antipodal, providing the extremizer for the
optimal constant asserted in Proposition 5.1. -/
theorem andFunction_one_antipodal :
    dual (andFunction (ι := Fin 1)) = andFunction := by
  have heq (x : Finset (Fin 1)) : x = Finset.univ ↔ (0 : Fin 1) ∈ x := by
    constructor
    · intro h; simp [h]
    · intro h
      apply Finset.eq_univ_of_forall
      intro i
      simpa only [Subsingleton.elim i 0] using h
  funext x
  simp only [dual, andFunction, heq, Finset.mem_compl]
  by_cases hx : (0 : Fin 1) ∈ x <;> simp [hx]

/-- The one-coordinate extremizer has covariance one quarter and influence one,
so the coefficient in Corollary 1.3 cannot be increased. -/
theorem andFunction_one_values :
    covariance (andFunction (ι := Fin 1)) andFunction = 1 / 4 ∧
      influence (andFunction (ι := Fin 1)) 0 = 1 := by
  rw [covariance_self_boolean isBoolean_andFunction, cubeMean_andFunction,
    influence_andFunction]
  norm_num [Fintype.card_finset]

/-- Proposition 5.1, antipodal case: AND attains the factor one quarter for
every coordinate and every increasing antipodal Boolean second function. -/
theorem andFunction_antipodal_sharp {g : Finset ι → ℝ} (hg : IsBoolean g)
    (hm : Monotone g) (hdual : dual g = g) (i : ι) :
    covariance andFunction g = influence andFunction i / 4 := by
  have h := andFunction_sharp hg hm
  rw [hdual, harmonic_self] at h
  rw [← h, spectralWeight_andFunction, variance_eq_quarter_of_antipodal hg hdual,
    influence_andFunction]
  ring

/-- Proposition 5.1, optimality: a coefficient valid for all increasing Boolean
pairs with an antipodal second function, even just on the one-coordinate cube,
cannot exceed `1/4`. The finite infimum is the minimum influence from (2). -/
theorem quarter_coefficient_optimal (c : ℝ)
    (hc : ∀ (f g : Finset (Fin 1) → ℝ), IsBoolean f → Monotone f →
      IsBoolean g → Monotone g → dual g = g →
        c * Finset.univ.inf' Finset.univ_nonempty (influence f) ≤ covariance f g) :
    c ≤ 1 / 4 := by
  have h := hc andFunction andFunction isBoolean_andFunction monotone_andFunction
    isBoolean_andFunction monotone_andFunction andFunction_one_antipodal
  rw [andFunction_one_values.1] at h
  simp_rw [influence_andFunction] at h
  norm_num [Fintype.card_finset] at h
  exact h

end Chvatal

end

-- LeanPool/Chvatal/LayerCake.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/


/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Finite layer-cake decomposition

Section 5 lifts inequalities for hereditary families to inequalities for
nonnegative decreasing weights by layer cake. On a finite space, integration can
be replaced by repeatedly subtracting the smallest positive weight from its
support. The support is a lower set, and each step strictly shrinks it.
-/


open scoped BigOperators

namespace Chvatal

variable {α : Type*} [Fintype α] [Preorder α]

/-- The finite layer-cake principle used in Section 5 (Proposition 5.3): if a
signed function has nonnegative sum on every lower set, then its scalar product
with every nonnegative antitone weight is nonnegative. This also covers an empty
underlying type. -/
theorem sum_mul_antitone_nonneg_of_lowerSets (c : α → ℝ)
    (hc : ∀ D : Finset α, IsLowerSet (D : Set α) → 0 ≤ ∑ x ∈ D, c x)
    (ω : α → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    0 ≤ ∑ x, c x * ω x := by
  classical
  suffices hmain : ∀ n (w : α → ℝ),
      (Finset.univ.filter (fun x => 0 < w x)).card = n →
      (∀ x, 0 ≤ w x) → Antitone w → 0 ≤ ∑ x, c x * w x by
    exact hmain _ ω rfl hω hanti
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn hw hwanti
    let D := Finset.univ.filter (fun x => 0 < w x)
    have hDlower : IsLowerSet (D : Set α) := by
      intro x y hxy hy
      simp only [D, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact lt_of_lt_of_le hy (hwanti hxy)
    by_cases hD : D.Nonempty
    · obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image D w hD
      have ha_pos : 0 < w a := (Finset.mem_filter.mp ha).2
      let w' : α → ℝ := fun x => max (w x - w a) 0
      have hw' : ∀ x, 0 ≤ w' x := fun x => le_max_right _ _
      have hw'anti : Antitone w' := by
        intro x y hxy
        exact max_le_max (sub_le_sub_right (hwanti hxy) (w a)) le_rfl
      have hw'le (x) : w' x ≤ w x :=
        max_le (sub_le_self _ ha_pos.le) (hw x)
      have hsmaller : (Finset.univ.filter (fun x => 0 < w' x)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact lt_of_lt_of_le hx (hw'le x)
        · intro heq
          have ha' : a ∈ Finset.univ.filter (fun x => 0 < w' x) := by
            rw [heq]
            exact ha
          simpa [w'] using (Finset.mem_filter.mp ha').2
      have hrec : 0 ≤ ∑ x, c x * w' x := ih _ hsmaller w' rfl hw' hw'anti
      have hdecomp (x) : w x = w' x + if x ∈ D then w a else 0 := by
        by_cases hx : x ∈ D
        · have hax : w a ≤ w x := hamin x hx
          simp only [w', max_eq_left (sub_nonneg.mpr hax), if_pos hx]
          ring
        · have hxzero : w x = 0 := by
            have hxle : w x ≤ 0 := by simpa [D] using hx
            exact le_antisymm hxle (hw x)
          simp [w', hx, hxzero, ha_pos.le]
      have hsum : (∑ x, c x * w x) =
          (∑ x, c x * w' x) + w a * ∑ x ∈ D, c x := by
        have hpoint (x) : c x * w x =
            c x * w' x + c x * (if x ∈ D then w a else 0) := by
          rw [hdecomp x, mul_add]
        simp_rw [hpoint]
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [hsum]
      exact add_nonneg hrec (mul_nonneg ha_pos.le (hc D hDlower))
    · have hwzero (x) : w x = 0 := by
        have hx : ¬0 < w x := by
          intro hx
          exact hD ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        exact le_antisymm (le_of_not_gt hx) (hw x)
      simp [hwzero]

end Chvatal

end

-- LeanPool/Chvatal/Weighted.lean
section

/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The spectral coefficients in the weighted star inequality

This file formalizes Proposition 5.3 of arXiv:2609.19123. The paper assigns each
nonempty Fourier set to its largest coordinate in a fixed total order. The
arguments below allow any fixed selector belonging to that set, a slightly
stronger formulation which includes the paper's choice.
-/


open scoped BigOperators


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Proposition 5.3's coefficients `λ_i`: four times the nonconstant Fourier
mass assigned to coordinate `i`. The selector is fixed independently of the
weight or hereditary family under consideration. -/
noncomputable def spectralWeights (g : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) : ℝ :=
  4 * ∑ S ∈ Finset.univ.erase ∅, if select S = i then fourier g S ^ 2 else 0

/-- Nonnegativity of every coefficient in Proposition 5.3. -/
theorem spectralWeights_nonneg (g : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) :
    0 ≤ spectralWeights g select i := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

/-- Regrouping Fourier sets according to their selected coordinate, the
partition-of-mass step in Proposition 5.3. -/
theorem sum_spectralWeights_mul (g : Finset ι → ℝ) (select : Finset ι → ι)
    (a : ι → ℝ) :
    (∑ i, spectralWeights g select i * a i) =
      4 * ∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2 * a (select S) := by
  simp only [spectralWeights, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp [mul_assoc, mul_ite, ite_mul]

/-- The coefficients in Proposition 5.3 sum to one, by Parseval and the
variance-one-quarter identity for an antipodal Boolean function. -/
theorem sum_spectralWeights {g : Finset ι → ℝ} (hg : IsBoolean g)
    (hdual : dual g = g) (select : Finset ι → ι) :
    ∑ i, spectralWeights g select i = 1 := by
  have hsum := sum_spectralWeights_mul g select (fun _ => 1)
  simp only [mul_one] at hsum
  have hmass : (∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2) = covariance g g := by
    rw [covariance_fourier]
    simp only [pow_two]
  rw [hmass, variance_eq_quarter_of_antipodal hg hdual] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- A fixed total order gives the selector `max_≺ S` used in Proposition 5.3.
The value at the empty set is irrelevant because the coefficients omit it. -/
noncomputable def orderedSelector [LinearOrder ι] [Nonempty ι] (S : Finset ι) : ι :=
  if hS : S.Nonempty then S.max' hS else Classical.choice inferInstance

/-- The ordered selector lies in each nonempty set, the property of the
paper's `max_≺` used in the weighted argument. -/
theorem orderedSelector_mem [LinearOrder ι] [Nonempty ι] {S : Finset ι}
    (hS : S.Nonempty) : orderedSelector S ∈ S := by
  simp only [orderedSelector, dif_pos hS]
  exact Finset.max'_mem _ _

/-- The hereditary-family inequality in the proof of Proposition 5.3, deduced
from the selected-coordinate spectral lower bound. This hypothesis is explicit
so the counting reduction is independent of the analytic proof. -/
theorem hereditary_bound_of_selected_correlation {g : Finset ι → ℝ}
    (hg : IsBoolean g) (hdual : dual g = g) (select : Finset ι → ι)
    (hcor : ∀ f : Finset ι → ℝ, IsBoolean f → Monotone f →
      (∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2 * influence f (select S)) ≤
        covariance f g)
    {D : Family ι} (hD : D.IsHereditary) :
    ((D ∩ Family.oneSupport g).card : ℝ) ≤
      ∑ i, spectralWeights g select i * (D.star i).card := by
  let B := Family.oneSupport g
  have hgB : B.indicator = g := Family.indicator_oneSupport hg
  have hanti : B.IsAntipodal := by
    rw [Family.isAntipodal_iff_dual_indicator, hgB]
    exact hdual
  have hsum := sum_spectralWeights hg hdual select
  have hbound := hcor (fun x => 1 - D.indicator x)
    (Family.isBoolean_one_sub_indicator D) hD.monotone_one_sub_indicator
  have hweighted : (∑ i, spectralWeights g select i *
      influence (fun x => 1 - D.indicator x) i) ≤
      4 * covariance (fun x => 1 - D.indicator x) g := by
    rw [sum_spectralWeights_mul]
    linarith
  have hcount : (∑ i, spectralWeights g select i *
      influence (fun x => 1 - D.indicator x) i) =
      (2 * (D.card : ℝ) - 4 * ∑ i, spectralWeights g select i * (D.star i).card) /
        Fintype.card (Finset ι) := by
    calc
      _ = (∑ i, ((2 * (D.card : ℝ)) * spectralWeights g select i -
          4 * (spectralWeights g select i * (D.star i).card))) /
          Fintype.card (Finset ι) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Family.influence_one_sub_indicator hD]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
        ring
  have hcov := Family.covariance_one_sub_indicator (D := D) hanti
  rw [hgB] at hcov
  rw [hcount, hcov] at hweighted
  have hN := cube_card_pos (ι := ι)
  have hnum := (div_le_div_iff_of_pos_right hN).mp
    (show (2 * (D.card : ℝ) - 4 * ∑ i, spectralWeights g select i * (D.star i).card) /
        Fintype.card (Finset ι) ≤
      (4 * ((D.card : ℝ) / 2 - (D ∩ B).card)) / Fintype.card (Finset ι) by
      simpa only [mul_div_assoc] using hweighted)
  dsimp [B] at hnum
  linarith

/-- The fractional star function `q(x) = ∑_i λ_i x_i` from the proof of
Proposition 5.3. -/
noncomputable def starMixture (weights : ι → ℝ) (x : Finset ι) : ℝ :=
  ∑ i, if i ∈ x then weights i else 0

/-- Counting the fractional star function on a family gives the corresponding
weighted combination of its star cardinalities (Proposition 5.3). -/
theorem sum_starMixture (weights : ι → ℝ) (D : Family ι) :
    (∑ x ∈ D, starMixture weights x) =
      ∑ i, weights i * (D.star i).card := by
  unfold starMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Family.star, ← Finset.sum_filter, mul_comm]

/-- Summing a family indicator over another family counts their intersection,
the second counting step for the defect in Proposition 5.3. -/
theorem sum_indicator_on_family (B D : Family ι) :
    (∑ x ∈ D, B.indicator x) = ((D ∩ B).card : ℝ) := by
  simp [Family.indicator]

/-- The mean-zero defect in Proposition 5.3, summed on a hereditary family.
The identity itself holds for every family. -/
theorem sum_starMixture_sub_indicator (weights : ι → ℝ) (B D : Family ι) :
    (∑ x ∈ D, (starMixture weights x - B.indicator x)) =
      (∑ i, weights i * (D.star i).card) - (D ∩ B).card := by
  rw [Finset.sum_sub_distrib, sum_starMixture, sum_indicator_on_family]

/-- The weighted form of the same defect, obtained by interchanging finite
sums. This is the finite counterpart of the layer-cake calculation in (18). -/
theorem sum_defect_mul (weights : ι → ℝ) (B : Family ι) (ω : Finset ι → ℝ) :
    (∑ x, (starMixture weights x - B.indicator x) * ω x) =
      (∑ i, weights i * ∑ x ∈ Family.star Finset.univ i, ω x) - ∑ x ∈ B, ω x := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  · unfold starMixture
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Family.star, Finset.sum_filter, Finset.mul_sum, ite_mul]
  · simp [Family.indicator, ite_mul]

/-- Finite layer-cake lifting in Proposition 5.3: domination on every
hereditary family implies domination for every nonnegative decreasing weight. -/
theorem weighted_bound_of_hereditary_bound (weights : ι → ℝ) (B : Family ι)
    (hbound : ∀ D : Family ι, D.IsHereditary →
      ((D ∩ B).card : ℝ) ≤ ∑ i, weights i * (D.star i).card)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∑ x ∈ B, ω x) ≤ ∑ i, weights i * ∑ x ∈ Family.star Finset.univ i, ω x := by
  have h := sum_mul_antitone_nonneg_of_lowerSets
    (fun x => starMixture weights x - B.indicator x)
    (fun D hD => by
      rw [sum_starMixture_sub_indicator]
      exact sub_nonneg.mpr (hbound D hD)) ω hω hanti
  rw [sum_defect_mul] at h
  exact sub_nonneg.mp h

/-- The selected-coordinate expression in Proposition 5.3 is bounded by the
spectral expression in Theorem 1.2, because the selector belongs to its set. -/
theorem selected_spectral_le (f g : Finset ι → ℝ) (select : Finset ι → ι)
    (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S) :
    (∑ S ∈ Finset.univ.erase ∅, fourier g S ^ 2 * influence f (select S)) ≤
      spectralWeight f g := by
  rw [spectralWeight_eq_sum_nonempty]
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (influence_le_maxInfluence f
    (hselect S (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)))
    (sq_nonneg _)

/-- The first inequality of Proposition 5.3 deduced from the antipodal spectral
bound, keeping the analytic dependency explicit. -/
theorem weighted_bound_of_spectral_bound [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) (select : Finset ι → ι)
    (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S)
    (hspectral : ∀ f : Finset ι → ℝ, IsBoolean f → Monotone f →
      spectralWeight f B.indicator ≤ covariance f B.indicator)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∑ x ∈ B, ω x) ≤
      ∑ i, spectralWeights B.indicator select i * ∑ x ∈ Family.star Finset.univ i, ω x := by
  apply weighted_bound_of_hereditary_bound _ B ?_ ω hω hanti
  intro D hD
  have hsupport : Family.oneSupport B.indicator = B := by
    ext x
    by_cases hx : x ∈ B <;> simp [Family.indicator, hx]
  have h := hereditary_bound_of_selected_correlation (Family.isBoolean_indicator B)
    hB.isAntipodal.dual_indicator select
    (fun f hf hm => (selected_spectral_le f B.indicator select hselect).trans
      (hspectral f hf hm)) hD
  simpa only [hsupport] using h

/-- Proposition 5.3's first inequality, proved from the antipodal case of
Theorem 1.2. It holds for any fixed selector belonging to each nonempty index. -/
theorem weighted_star_mixture_bound [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) (select : Finset ι → ι)
    (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∑ x ∈ B, ω x) ≤
      ∑ i, spectralWeights B.indicator select i * ∑ x ∈ Family.star Finset.univ i, ω x :=
  weighted_bound_of_spectral_bound hB select hselect
    (fun _ hf hmf => antipodal_spectral_bound hf hmf (Family.isBoolean_indicator B)
      hB.isIncreasing.monotone_indicator hB.isAntipodal.dual_indicator) ω hω hanti

/-- A convex combination of star weights is at most their maximum, the second
inequality in equation (18). -/
theorem star_mixture_le_max [Nonempty ι] (weights : ι → ℝ)
    (hweights : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (ω : Finset ι → ℝ) :
    (∑ i, weights i * ∑ x ∈ Family.star Finset.univ i, ω x) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) := by
  let M := Finset.univ.sup' Finset.univ_nonempty
    (fun i => ∑ x ∈ Family.star Finset.univ i, ω x)
  calc
    _ ≤ ∑ i, weights i * M := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hweights i)
      exact Finset.le_sup' (fun j : ι => ∑ x ∈ Family.star Finset.univ j, ω x)
        (Finset.mem_univ i)
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Proposition 5.3 in the paper's exact ordered-selector formulation: the
spectral coefficients are nonnegative, sum to one, and satisfy both inequalities
in equation (18). The total order represents the paper's fixed permutation. -/
theorem kleitman_weighted_bound [LinearOrder ι] [Nonempty ι] {B : Family ι}
    (hB : B.IsMaximalIntersecting) (ω : Finset ι → ℝ)
    (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    (∀ i, 0 ≤ spectralWeights B.indicator orderedSelector i) ∧
    (∑ i, spectralWeights B.indicator orderedSelector i) = 1 ∧
    (∑ x ∈ B, ω x) ≤
      (∑ i, spectralWeights B.indicator orderedSelector i *
        ∑ x ∈ Family.star Finset.univ i, ω x) ∧
    (∑ i, spectralWeights B.indicator orderedSelector i *
        ∑ x ∈ Family.star Finset.univ i, ω x) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) := by
  have hweights := spectralWeights_nonneg B.indicator orderedSelector
  have hsum := sum_spectralWeights (Family.isBoolean_indicator B)
    hB.isAntipodal.dual_indicator orderedSelector
  exact ⟨hweights, hsum,
    weighted_star_mixture_bound hB orderedSelector (fun _ => orderedSelector_mem) ω hω hanti,
    star_mixture_le_max _ hweights hsum ω⟩

/-- The final conclusion of Proposition 5.3 for one intersecting family:
its total nonnegative decreasing weight is bounded by some full-cube star. -/
theorem exists_weighted_star_bound [Nonempty ι] {A : Family ι}
    (hA : A.IsIntersecting) (ω : Finset ι → ℝ)
    (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    ∃ i : ι, (∑ x ∈ A, ω x) ≤ ∑ x ∈ Family.star Finset.univ i, ω x := by
  classical
  obtain ⟨B, hAB, hB⟩ := hA.exists_maximal_extension
  let select : Finset ι → ι := fun S =>
    if hS : S.Nonempty then hS.choose else Classical.choice inferInstance
  have hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S := by
    intro S hS
    simp only [select, dif_pos hS]
    exact hS.choose_spec
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc
    (∑ x ∈ A, ω x) ≤ ∑ x ∈ B, ω x :=
      Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hω x)
    _ ≤ ∑ j, spectralWeights B.indicator select j *
        ∑ x ∈ Family.star Finset.univ j, ω x :=
      weighted_star_mixture_bound hB select hselect ω hω hanti
    _ ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun j => ∑ x ∈ Family.star Finset.univ j, ω x) :=
      star_mixture_le_max _ (spectralWeights_nonneg _ _)
        (sum_spectralWeights (Family.isBoolean_indicator B) hB.isAntipodal.dual_indicator
          select) ω
    _ ≤ ∑ x ∈ Family.star Finset.univ i, ω x := Finset.sup'_le _ _ hi

/-- The final maximum-attainment statement of Proposition 5.3: one star
simultaneously dominates every intersecting family for a fixed nonnegative
decreasing weight, and that star is itself intersecting. -/
theorem exists_largest_weighted_intersecting_star [Nonempty ι]
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hanti : Antitone ω) :
    ∃ i : ι, (Family.star (Finset.univ : Family ι) i).IsIntersecting ∧
      ∀ A : Family ι, A.IsIntersecting →
        (∑ x ∈ A, ω x) ≤ ∑ x ∈ Family.star Finset.univ i, ω x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => ∑ x ∈ Family.star Finset.univ i, ω x) Finset.univ_nonempty
  refine ⟨i, Family.star_isIntersecting Finset.univ i, ?_⟩
  intro A hA
  obtain ⟨j, hj⟩ := exists_weighted_star_bound hA ω hω hanti
  exact hj.trans (hi j (Finset.mem_univ j))

end Chvatal

end

-- LeanPool/Chvatal/Signed.lean
section

/-
Copyright (c) 2026 Chvátal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/



/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The signed Boolean formulation

The final paragraph of Section 5 of arXiv:2609.19123 changes conventions from
`{0,1}`-valued functions to `{-1,1}`-valued functions by `h = 2g - 1`.
This file verifies that conversion, the positive-part and Fourier identities,
and the resulting signed version of the weighted star inequality.
-/


open scoped BigOperators


namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A signed Boolean function, with values in `{-1,1}`, as in Section 5's
comparison with Friedgut–Kahn–Kalai–Keller. -/
noncomputable def IsSignedBoolean (h : Finset ι → ℝ) : Prop := ∀ x, h x = -1 ∨ h x = 1

/-- The convention change `h = 2g - 1` in the final paragraph of Section 5. -/
noncomputable def signLift (g : Finset ι → ℝ) (x : Finset ι) : ℝ := 2 * g x - 1

/-- The inverse convention change `g = (h + 1) / 2` in Section 5. -/
noncomputable def booleanPart (h : Finset ι → ℝ) (x : Finset ι) : ℝ := (h x + 1) / 2

/-- The signed lift followed by the Boolean conversion is the identity. -/
@[simp] theorem booleanPart_signLift (g : Finset ι → ℝ) : booleanPart (signLift g) = g := by
  funext x
  simp only [booleanPart, signLift]
  ring

/-- The Boolean conversion followed by the signed lift is the identity. -/
@[simp] theorem signLift_booleanPart (h : Finset ι → ℝ) : signLift (booleanPart h) = h := by
  funext x
  simp only [booleanPart, signLift]
  ring

/-- Section 5: a Boolean function becomes a `{-1,1}`-valued function. -/
theorem IsBoolean.signLift {g : Finset ι → ℝ} (hg : IsBoolean g) :
    IsSignedBoolean (signLift g) := by
  intro x
  rcases hg x with hx | hx <;> norm_num [Chvatal.signLift, hx]

/-- Conversely every signed Boolean function gives an ordinary Boolean function,
so the closing signed formulation has the same scope as the Boolean one. -/
theorem IsSignedBoolean.booleanPart {h : Finset ι → ℝ} (hh : IsSignedBoolean h) :
    IsBoolean (booleanPart h) := by
  intro x
  rcases hh x with hx | hx <;> simp [Chvatal.booleanPart, hx]

/-- The convention change in Section 5 preserves increasing functions. -/
theorem monotone_signLift {g : Finset ι → ℝ} (hg : Monotone g) :
    Monotone (signLift g) := by
  intro x y hxy
  dsimp [signLift]
  linarith [hg hxy]

/-- The inverse convention change also preserves increasing functions. -/
theorem monotone_booleanPart {h : Finset ι → ℝ} (hh : Monotone h) :
    Monotone (booleanPart h) := by
  intro x y hxy
  dsimp [booleanPart]
  linarith [hh hxy]

/-- Section 5: a self-dual Boolean function lifts to an odd function under
antipodal complementation, `h(xᶜ) = -h(x)`. -/
theorem signLift_compl {g : Finset ι → ℝ} (hg : dual g = g) (x : Finset ι) :
    signLift g xᶜ = -signLift g x := by
  have hx := congrFun hg x
  dsimp [dual] at hx
  dsimp [signLift]
  linarith

/-- The inverse of the preceding antipodality conversion. -/
theorem dual_booleanPart {h : Finset ι → ℝ} (hh : ∀ x, h xᶜ = -h x) :
    dual (booleanPart h) = booleanPart h := by
  funext x
  simp only [dual, booleanPart, hh]
  ring

/-- The identity `h_+² = g` explicitly stated in the final paragraph of Section 5. -/
theorem signLift_positivePart_sq {g : Finset ι → ℝ} (hg : IsBoolean g) (x : Finset ι) :
    max (signLift g x) 0 ^ 2 = g x := by
  rcases hg x with hx | hx <;> norm_num [signLift, hx]

/-- The positive-part identity for an arbitrary signed Boolean function. -/
theorem IsSignedBoolean.positivePart_sq {h : Finset ι → ℝ} (hh : IsSignedBoolean h)
    (x : Finset ι) : max (h x) 0 ^ 2 = Chvatal.booleanPart h x := by
  rcases hh x with hx | hx <;> norm_num [Chvatal.booleanPart, hx]

/-- Fourier coefficients under the affine convention change of Section 5,
including the exceptional constant coefficient. -/
theorem fourier_signLift (g : Finset ι → ℝ) (S : Finset ι) :
    fourier (signLift g) S = 2 * fourier g S - if S = ∅ then 1 else 0 := by
  change fourier (fun x => 2 * g x - 1) S = _
  rw [fourier_sub, fourier_const]
  congr 1
  simp only [fourier, mul_assoc, cubeMean_mul_left]

/-- Section 5's formula `ĥ(S) = 2ĝ(S)` for every nonempty Fourier index. -/
theorem fourier_signLift_of_nonempty (g : Finset ι → ℝ) {S : Finset ι}
    (hS : S.Nonempty) : fourier (signLift g) S = 2 * fourier g S := by
  simp [fourier_signLift, hS.ne_empty]

/-- The coefficients in the final displayed equation of Section 5, in the
signed Boolean convention. Choosing `orderedSelector` gives the paper's order. -/
noncomputable def signedSpectralWeights (h : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) : ℝ :=
  ∑ S ∈ Finset.univ.erase ∅, if select S = i then fourier h S ^ 2 else 0

/-- Section 5: the signed Fourier formula gives exactly the same coefficients
`λ_i` as Proposition 5.3, with its factor of four absorbed by the convention change. -/
theorem spectralWeights_eq_signed (g : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) :
    spectralWeights g select i = signedSpectralWeights (signLift g) select i := by
  rw [spectralWeights, signedSpectralWeights, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourier_signLift_of_nonempty g
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)]
  split_ifs <;> ring

/-- Nonnegativity of the signed coefficients in the closing Section 5 formulation. -/
theorem signedSpectralWeights_nonneg (h : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) :
    0 ≤ signedSpectralWeights h select i := by
  exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

/-- The signed coefficients sum to one for every antipodal signed Boolean function. -/
theorem sum_signedSpectralWeights {h : Finset ι → ℝ} (hh : IsSignedBoolean h)
    (hanti : ∀ x, h xᶜ = -h x) (select : Finset ι → ι) :
    (∑ i, signedSpectralWeights h select i) = 1 := by
  have hsum := sum_spectralWeights hh.booleanPart (dual_booleanPart hanti) select
  simpa only [spectralWeights_eq_signed, signLift_booleanPart] using hsum

/-- The weighted star inequality in the signed Boolean convention of Section 5's
closing paragraph. Its left side uses exactly the stated positive-part square,
and its coefficients use the stated squared signed Fourier coefficients. -/
theorem signed_weighted_star_bound [Nonempty ι] {h : Finset ι → ℝ}
    (hh : IsSignedBoolean h) (hm : Monotone h) (hanti : ∀ x, h xᶜ = -h x)
    (select : Finset ι → ι) (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hωanti : Antitone ω) :
    (∑ x, max (h x) 0 ^ 2 * ω x) ≤
      ∑ i, signedSpectralWeights h select i * ∑ x ∈ Family.star Finset.univ i, ω x := by
  let B := Family.oneSupport (booleanPart h)
  have hBindicator : B.indicator = booleanPart h := Family.indicator_oneSupport hh.booleanPart
  have hBmono : B.IsIncreasing := Family.isIncreasing_oneSupport hh.booleanPart
    (monotone_booleanPart hm)
  have hBanti : B.IsAntipodal := by
    rw [Family.isAntipodal_iff_dual_indicator, hBindicator]
    exact dual_booleanPart hanti
  have hbound := weighted_star_mixture_bound
    (hBmono.isMaximalIntersecting_of_isAntipodal hBanti) select hselect ω hω hωanti
  rw [hBindicator] at hbound
  simp only [spectralWeights_eq_signed, signLift_booleanPart] at hbound
  have hsum : (∑ x, max (h x) 0 ^ 2 * ω x) = ∑ x ∈ B, ω x := by
    simp_rw [hh.positivePart_sq]
    rw [← hBindicator, sum_indicator_mul]
  rw [hsum]
  exact hbound

end Chvatal

end

namespace Chvatal

section

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Represent a family of subsets as a finite family of finite subsets. -/
noncomputable def ofSetFamily (F : Set (Set X)) : Family X := by
  classical
  exact Finset.univ.filter (fun s : Finset X => (s : Set X) ∈ F)

@[simp] theorem mem_ofSetFamily {F : Set (Set X)} {s : Finset X} :
    s ∈ ofSetFamily F ↔ (s : Set X) ∈ F := by
  classical
  simp [ofSetFamily]

/-- The representation preserves the cardinality of the family. -/
theorem mk_ofSetFamily (F : Set (Set X)) :
    Cardinal.mk F = ((ofSetFamily F).card : Cardinal) := by
  classical
  have e : ↥(ofSetFamily F) ≃ F :=
    Fintype.finsetEquivSet.subtypeEquiv fun s => mem_ofSetFamily
  rw [← Cardinal.mk_congr e, Cardinal.mk_fintype, Fintype.card_coe]

end

end Chvatal

theorem OMA.solution : type_of% @Erdos701.erdos_701 := by
  classical
  intro X _ _ F hF
  have hD : (Chvatal.ofSetFamily F).IsHereditary := by
    intro s t hst ht
    exact Chvatal.mem_ofSetFamily.mpr
      (hF (Finset.coe_subset.mpr hst) (Chvatal.mem_ofSetFamily.mp ht))
  obtain ⟨i, _, hi⟩ := Chvatal.exists_largest_intersecting_star hD
  refine ⟨i, ?_⟩
  intro G hGF hG
  have hsub : Chvatal.ofSetFamily G ⊆ Chvatal.ofSetFamily F := by
    intro s hs
    exact Chvatal.mem_ofSetFamily.mpr (hGF (Chvatal.mem_ofSetFamily.mp hs))
  have hinter : (Chvatal.ofSetFamily G).IsIntersecting := by
    intro s hs t ht hst
    exact hG (Chvatal.mem_ofSetFamily.mp hs) (Chvatal.mem_ofSetFamily.mp ht)
      (Finset.disjoint_coe.mpr hst)
  have hstar : Chvatal.ofSetFamily {A : Set X | A ∈ F ∧ i ∈ A} =
      (Chvatal.ofSetFamily F).star i := by
    ext s
    simp only [Chvatal.mem_ofSetFamily, Chvatal.Family.mem_star, Set.mem_setOf_eq, Finset.mem_coe]
  rw [Chvatal.mk_ofSetFamily, Chvatal.mk_ofSetFamily, hstar]
  exact_mod_cast hi _ hsub hinter
