import FormalConjectures.ErdosProblems.«676»
import Mathlib

/-!
Port of the disproof by Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer.
https://github.com/Ghuffy1/erdos676/tree/3cc60a9fa3b811c10732dcc435f7fe21e0d54cab

The port assembles the Lean modules and their dependencies in a single file.
Blueprint annotations and module headers are removed. The result uses a
dyadic sieve and moment estimates to produce arbitrarily large exceptions.

Erdős 676 / JSP-000549 proof project
Copyright 2026 Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer.
Original project code is distributed under Apache License 2.0.
The paper and original prose are distributed under CC BY 4.0, as specified in LICENSE-PAPER.

Third-party sources retain their original licenses and notices.

Erdos676/Basic.lean adapts the public Formal Conjectures development,
Copyright 2026 The Formal Conjectures Authors, Apache License 2.0.
Source commit e754a78c74a3f2bbc38e4f2063b5f6eed51bde39.

vendor/Architect and vendor/Architect.lean are copied without mathematical changes
from hanwenzhu/LeanArchitect commit 468e8f58fb4ad6e6ad672a08da6d0d0531e95a97.
See vendor/LICENSE-LeanArchitect and provenance/vendor.json.

vendor/PrimeNumberTheoremAnd contains the required Mertens development and its
Euler--Maclaurin dependency from AlexKontorovich/PrimeNumberTheoremAnd commit
c39a751132c88b6e8080b74c74023fd95b3d8be0.
See vendor/LICENSE-PrimeNumberTheoremAnd and provenance/vendor.json.

mathlib and its transitive dependencies are fetched at the revisions in
lake-manifest.json. Their copyright and license notices remain with those projects.

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
The modular equivalence proof follows the public Formal Conjectures development,
Copyright 2026 The Formal Conjectures Authors, Apache License 2.0.
Source commit e754a78c74a3f2bbc38e4f2063b5f6eed51bde39.
-/


namespace Erdos676

def Representable (n : ℕ) : Prop :=
  ∃ a p b : ℕ, p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b

def Exceptional (n : ℕ) : Prop := ¬ Representable n

def EventualRepresentation : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, Representable n

def UnboundedExceptions : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Exceptional n

theorem representable_iff_mod (n : ℕ) :
    Representable n ↔ ∃ p : ℕ, p.Prime ∧ p ^ 2 ≤ n ∧ n % p ^ 2 < p := by
  constructor
  · rintro ⟨a, p, b, hp, ha, hb, rfl⟩
    refine ⟨p, hp, ?_, ?_⟩
    · nlinarith
    · have hb' : b < p ^ 2 := by
        have := hp.two_le
        nlinarith
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb'] using hb
  · rintro ⟨p, hp, hn, hr⟩
    refine ⟨n / p ^ 2, p, n % p ^ 2, hp, ?_, hr, ?_⟩
    · exact Nat.div_pos hn (pow_pos hp.pos _)
    · simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n (p ^ 2)).symm

theorem exceptional_iff_mod (n : ℕ) :
    Exceptional n ↔ ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ≤ n % p ^ 2 := by
  simp only [Exceptional, representable_iff_mod, not_exists, not_and, not_lt]

theorem not_eventual_iff_unbounded :
    ¬ EventualRepresentation ↔ UnboundedExceptions := by
  simp only [EventualRepresentation, Filter.eventually_atTop, UnboundedExceptions,
    Exceptional, not_exists, not_forall, exists_prop]

theorem unbounded_iff_infinite :
    UnboundedExceptions ↔ Set.Infinite {n : ℕ | Exceptional n} := by
  constructor
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro m
    obtain ⟨n, hn, he⟩ := h (m + 1)
    exact ⟨n, he, by omega⟩
  · intro h N
    obtain ⟨n, hn, hnN⟩ := h.exists_gt N
    exact ⟨n, le_of_lt hnN, hn⟩

noncomputable def dyadicExceptions (X : ℕ) : Finset ℕ :=
  @Finset.filter ℕ Exceptional (Classical.decPred Exceptional) (Finset.Ioc X (2 * X))

theorem mem_dyadicExceptions (X n : ℕ) :
    n ∈ dyadicExceptions X ↔ X < n ∧ n ≤ 2 * X ∧ Exceptional n := by
  simp [dyadicExceptions, and_assoc]

theorem unbounded_of_eventually_dyadic_nonempty
    (h : ∀ᶠ X : ℕ in Filter.atTop, (dyadicExceptions X).Nonempty) :
    UnboundedExceptions := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp h
  intro N
  obtain ⟨n, hn⟩ := hX₀ (max X₀ N) (le_max_left _ _)
  obtain ⟨hl, _, he⟩ := (mem_dyadicExceptions _ _).mp hn
  exact ⟨n, le_trans (le_max_right _ _) hl.le, he⟩

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676


theorem restricted_mass_lower_bound {ι : Type*} [DecidableEq ι]
    (I U : Finset ι) (f : ι → ℝ) (hUI : U ⊆ I)
    (hf : ∀ x ∈ I, 0 ≤ f x) :
    (∑ x ∈ I, f x) -
        Real.sqrt ((I \ U).card * ∑ x ∈ I, (f x) ^ 2) ≤
      ∑ x ∈ U, f x := by
  have hsplit : (∑ x ∈ I \ U, f x) + (∑ x ∈ U, f x) = ∑ x ∈ I, f x :=
    Finset.sum_sdiff hUI
  have hcs := sq_sum_le_card_mul_sum_sq (s := I \ U) (f := f)
  have hsquares : (∑ x ∈ I \ U, (f x) ^ 2) ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ => sq_nonneg (f x))
  have hcard : (0 : ℝ) ≤ (I \ U).card := Nat.cast_nonneg _
  have hnonneg : 0 ≤ ((I \ U).card : ℝ) * ∑ x ∈ I, (f x) ^ 2 :=
    mul_nonneg hcard (Finset.sum_nonneg (fun x _ => sq_nonneg (f x)))
  have hbound : (∑ x ∈ I \ U, f x) ≤
      Real.sqrt ((I \ U).card * ∑ x ∈ I, (f x) ^ 2) := by
    apply (Real.le_sqrt (Finset.sum_nonneg (fun x hx => hf x (Finset.mem_sdiff.mp hx).1))
      hnonneg).mpr
    exact hcs.trans (mul_le_mul_of_nonneg_left hsquares hcard)
  linarith


theorem mass_le_card {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀ x ∈ S, f x ≤ 1) : ∑ x ∈ S, f x ≤ S.card := by
  simpa using Finset.sum_le_sum h


theorem positive_restricted_mass_of_moment_gap {ι : Type*} [DecidableEq ι]
    (I U : Finset ι) (f : ι → ℝ) (hUI : U ⊆ I)
    (hf : ∀ x ∈ I, 0 ≤ f x)
    (hfirst : 0 < ∑ x ∈ I, f x)
    (hgap : ((I \ U).card : ℝ) * (∑ x ∈ I, (f x) ^ 2) <
      (∑ x ∈ I, f x) ^ 2) :
    0 < ∑ x ∈ U, f x := by
  have hsplit := Finset.sum_sdiff (f := f) hUI
  have hcs := sq_sum_le_card_mul_sum_sq (s := I \ U) (f := f)
  have hsq : (∑ x ∈ I \ U, (f x) ^ 2) ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ => sq_nonneg (f x))
  have hupper := hcs.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
  have hnonneg : 0 ≤ ∑ x ∈ I \ U, f x :=
    Finset.sum_nonneg fun x hx => hf x (Finset.mem_sdiff.mp hx).1
  by_contra h
  have hu : (∑ x ∈ U, f x) ≤ 0 := le_of_not_gt h
  nlinarith


theorem scalar_moment_gap {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hsmall : 3 * e < d) :
    (1 - d) * (1 + e) < (1 - e) ^ 2 := by
  have : 0 ≤ d * e := mul_nonneg hd he
  nlinarith [sq_nonneg e]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676


theorem symmetric_row_sum_bound {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ)
    (r : ι → ℝ) (C : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, K i j) ≤ C) :
    (∑ i ∈ s, ∑ j ∈ s, K i j * r i * r j) ≤ C * ∑ i ∈ s, (r i) ^ 2 := by
  have hfirst : (∑ i ∈ s, ∑ j ∈ s, K i j * (r i) ^ 2) =
      ∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    ring
  have hsecond : (∑ i ∈ s, ∑ j ∈ s, K i j * (r j) ^ 2) =
      ∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
    ring
  have htwice : 2 * (∑ i ∈ s, ∑ j ∈ s, K i j * r i * r j) ≤
      2 * (∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j)) := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, K i j * (2 * r i * r j) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, K i j * ((r i) ^ 2 + (r j) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (hK i hi j hj)
        nlinarith [sq_nonneg (r i - r j)]
      _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [hfirst, hsecond]
        ring
  have htotal : (∑ i ∈ s, (r i) ^ 2 * (∑ j ∈ s, K i j)) ≤
      C * ∑ i ∈ s, (r i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg (r i))
    nlinarith
  linarith

end Erdos676
end

section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Erdos676

theorem complex_gram_row_bound {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset P) (v : P → E) (c : P → ℂ) (C : ℝ)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, ‖⟪v i, v j⟫_ℂ‖) ≤ C) :
    ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hexpand : ‖∑ i ∈ s, c i • v i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (star (c i) * (c j * ⟪v i, v j⟫_ℂ)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    have hcomplex : ⟪∑ i ∈ s, c i • v i, ∑ i ∈ s, c i • v i⟫_ℂ =
        ∑ i ∈ s, ∑ j ∈ s, star (c i) * (c j * ⟪v i, v j⟫_ℂ) := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [starRingEnd_apply]
      ring
    rw [hcomplex]
    change Complex.reCLM (∑ i ∈ s, ∑ j ∈ s, star (c i) * (c j * ⟪v i, v j⟫_ℂ)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact map_sum Complex.reCLM _ _
  rw [hexpand]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖⟪v i, v j⟫_ℂ‖ * ‖c i‖ * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have h := Complex.re_le_norm (star (c i) * (c j * ⟪v i, v j⟫_ℂ))
      simpa only [norm_mul, norm_star, mul_comm, mul_left_comm, mul_assoc] using h
    _ ≤ _ := symmetric_row_sum_bound s (fun i j => ‖⟪v i, v j⟫_ℂ‖) (fun i => ‖c i‖) C
      (fun _ _ _ _ => norm_nonneg _) (fun i _ j _ => norm_inner_symm _ _) hrow

end Erdos676
end

section
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Erdos676

theorem sampling_gram_bound {P T : Type*} [Fintype T]
    (s : Finset P) (f : P → T → ℂ) (c : P → ℂ) (C : ℝ)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, ‖∑ t : T, star (f i t) * f j t‖) ≤ C) :
    (∑ t : T, ‖∑ i ∈ s, c i * f i t‖ ^ 2) ≤ C * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  let v (i : P) : EuclideanSpace ℂ T := WithLp.toLp 2 (f i)
  have hinner (i j : P) : ⟪v i, v j⟫_ℂ = ∑ t : T, star (f i t) * f j t := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro t ht
    change f j t * star (f i t) = star (f i t) * f j t
    exact mul_comm _ _
  have h := complex_gram_row_bound s v c C (by simpa only [hinner] using hrow)
  rw [EuclideanSpace.norm_sq_eq] at h
  have heval (t : T) : (∑ i ∈ s, c i • v i) t = ∑ i ∈ s, c i * f i t := by
    have hmap := map_sum (PiLp.projₗ (𝕜 := ℂ) (β := fun _ : T => ℂ) 2 t)
      (fun i => c i • v i) s
    simpa only [PiLp.projₗ_apply, PiLp.smul_apply, v, PiLp.toLp_apply, smul_eq_mul] using hmap
  simpa only [heval] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

section FiniteGroup

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]


def overlap (A : Finset G) (k : G) : ℕ :=
  ∑ x ∈ A, if x + k ∈ A then 1 else 0

omit [Fintype G] in
theorem overlap_le_card (A : Finset G) (k : G) : overlap A k ≤ A.card := by
  unfold overlap
  calc
    _ ≤ ∑ _x ∈ A, 1 := Finset.sum_le_sum fun x hx => by split_ifs <;> omega
    _ = A.card := by simp

omit [Fintype G] in
theorem overlap_zero (A : Finset G) : overlap A 0 = A.card := by
  simp [overlap]


theorem sum_overlap (A : Finset G) : ∑ k : G, overlap A k = A.card ^ 2 := by
  classical
  unfold overlap
  rw [Finset.sum_comm]
  have htranslate (x : G) :
      (∑ k : G, if x + k ∈ A then 1 else 0) = A.card := by
    calc
      _ = ∑ y : G, if y ∈ A then 1 else 0 :=
        Equiv.sum_comp (Equiv.addLeft x) (fun y => if y ∈ A then 1 else 0)
      _ = A.card := by simp
  simp_rw [htranslate]
  simp [pow_two]

end FiniteGroup

end Erdos676
end

section
namespace Erdos676

theorem periodic_count_mul (p : ℕ → Prop) [DecidablePred p] (m k : ℕ)
    (hp : Function.Periodic p m) :
    Nat.count p (k * m) = k * Nat.count p m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.count_add, ih]
      have hshift : (fun j => p (k * m + j)) = p := by
        funext j
        simpa [Nat.add_comm] using (hp.nat_mul k) j
      simp [hshift, Nat.add_mul]

theorem periodic_count_decomposition (p : ℕ → Prop) [DecidablePred p] (m N : ℕ)
    (hp : Function.Periodic p m) :
    Nat.count p N = (N / m) * Nat.count p m + Nat.count p (N % m) := by
  conv_lhs => rw [← Nat.div_add_mod N m]
  rw [Nat.count_add, Nat.mul_comm m (N / m), periodic_count_mul p m (N / m) hp]
  have hshift : (fun j => p (N / m * m + j)) = p := by
    funext j
    simpa [Nat.add_comm] using (hp.nat_mul (N / m)) j
  simp [hshift]

theorem periodic_count_bounds (p : ℕ → Prop) [DecidablePred p] (m N : ℕ)
    (hm : 0 < m) (hp : Function.Periodic p m) :
    (N / m) * Nat.count p m ≤ Nat.count p N ∧
      Nat.count p N ≤ (N / m + 1) * Nat.count p m := by
  have hr : Nat.count p (N % m) ≤ Nat.count p m :=
    Nat.count_monotone p (Nat.mod_lt N hm).le
  rw [periodic_count_decomposition p m N hp]
  constructor <;> nlinarith


theorem periodic_count_scaled_error (p : ℕ → Prop) [DecidablePred p] (m N : ℕ)
    (hm : 0 < m) (hp : Function.Periodic p m) :
    |(m : ℤ) * Nat.count p N - (N : ℤ) * Nat.count p m| ≤
      (m : ℤ) * Nat.count p m := by
  have hrem : (N % m : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Nat.mod_lt N hm).le
  have hcount : (Nat.count p (N % m) : ℤ) ≤ Nat.count p m := by
    exact_mod_cast Nat.count_monotone p (Nat.mod_lt N hm).le
  have hm0 : (0 : ℤ) ≤ m := by omega
  have hrho : (0 : ℤ) ≤ Nat.count p m := by omega
  have hc0 : (0 : ℤ) ≤ Nat.count p (N % m) := by omega
  have hr0 : (0 : ℤ) ≤ N % m := by omega
  have hprod1 := mul_le_mul_of_nonneg_left hcount hm0
  have hprod2 := mul_le_mul_of_nonneg_right hrem hrho
  have hprod3 := mul_nonneg hm0 hc0
  have hprod4 := mul_nonneg hr0 hrho
  have hN : (N : ℤ) = (N / m : ℤ) * m + (N % m : ℤ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod N m).symm)
  have hNmul := congrArg (fun t : ℤ => t * (Nat.count p m : ℤ)) hN
  rw [periodic_count_decomposition p m N hp]
  push_cast
  apply abs_le.mpr
  constructor <;> nlinarith

theorem periodic_count_shift_period (p : ℕ → Prop) [DecidablePred p] (m S : ℕ)
    (hp : Function.Periodic p m) :
    Nat.count (fun j => p (S + j)) m = Nat.count p m := by
  have hshift : (fun j => p (m + j)) = p := by
    funext j
    simpa [Nat.add_comm] using hp j
  have h := congrArg (Nat.count p) (Nat.add_comm S m)
  simp only [Nat.count_add, hshift] at h
  omega

theorem periodic_interval_count_scaled_error (p : ℕ → Prop) [DecidablePred p]
    (m S N : ℕ) (hm : 0 < m) (hp : Function.Periodic p m) :
    |(m : ℤ) * Nat.count (fun j => p (S + j)) N - (N : ℤ) * Nat.count p m| ≤
      (m : ℤ) * Nat.count p m := by
  have hsp : Function.Periodic (fun j => p (S + j)) m := by
    intro j
    simpa [Nat.add_assoc] using hp (S + j)
  simpa only [periodic_count_shift_period p m S hp] using
    periodic_count_scaled_error (fun j => p (S + j)) m N hm hsp

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

def residueCondition {ι : Type*} (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i)))
    (n : ℕ) : Prop := ∀ i, (n : ZMod (m i)) ∈ A i

theorem residueCondition_periodic {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i))) :
    Function.Periodic (residueCondition m A) (∏ i, m i) := by
  intro n
  unfold residueCondition
  apply propext
  apply forall_congr'
  intro i
  have hz : ((∏ j, m j : ℕ) : ZMod (m i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
  simp only [Nat.cast_add, hz, add_zero]


theorem residueCondition_count_period {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i)))
    (hm : ∀ i, 0 < m i) (hc : Pairwise (fun i j => (m i).Coprime (m j))) :
    @Nat.count (residueCondition m A) (Classical.decPred _) (∏ i, m i) =
      ∏ i, (A i).card := by
  classical
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  let : NeZero M := ⟨ne_of_gt hM⟩
  let : Fintype {n : ℕ // n < M ∧ residueCondition m A n} :=
    Fintype.ofFinset ((Finset.range M).filter (residueCondition m A)) (by
      intro n
      simp only [Finset.mem_filter, Finset.mem_range]
      rfl)
  let f (r : ZMod M) (i : ι) : ZMod (m i) :=
    ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r
  let e₁ : {n : ℕ // n < M ∧ residueCondition m A n} ≃
      {r : ZMod M // ∀ i, f r i ∈ A i} := {
    toFun := fun n => ⟨n.val, by
      intro i
      change ZMod.castHom _ _ (n.val : ZMod M) ∈ A i
      rw [map_natCast]
      exact n.property.2 i⟩
    invFun := fun r => ⟨r.val.val, ZMod.val_lt r.val, by
      have hcast : (r.val.val : ZMod M) = r.val := ZMod.natCast_zmod_val r.val
      have hh : ∀ i, f (r.val.val : ZMod M) i ∈ A i := by
        rw [hcast]
        exact r.property
      intro i
      have hh' := hh i
      change ZMod.castHom _ _ (r.val.val : ZMod M) ∈ A i at hh'
      rwa [map_natCast] at hh'⟩
    left_inv := fun n => Subtype.ext (ZMod.val_natCast_of_lt n.property.1)
    right_inv := fun r => Subtype.ext (ZMod.natCast_zmod_val r.val)
  }
  let e₂ : {r : ZMod M // ∀ i, f r i ∈ A i} ≃
      {r : ∀ i, ZMod (m i) // ∀ i, r i ∈ A i} :=
    (ZMod.prodEquivPi m hc).toEquiv.subtypeEquiv (by
      intro r
      change (∀ i, f r i ∈ A i) ↔ ∀ i, ZMod.prodEquivPi m hc r i ∈ A i
      simp only [ZMod.prodEquivPi_apply]
      rfl)
  rw [Nat.count_eq_card_fintype]
  calc
    _ = Fintype.card (∀ i, {r : ZMod (m i) // r ∈ A i}) :=
      Fintype.card_congr ((e₁.trans e₂).trans Equiv.subtypePiEquivPi)
    _ = ∏ i, (A i).card := by simp

theorem residueCondition_interval_error {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (A : ∀ i, Finset (ZMod (m i)))
    (hm : ∀ i, 0 < m i) (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (S N : ℕ) :
    |(@Nat.count (fun j => residueCondition m A (S + j)) (Classical.decPred _) N : ℝ) -
      (N : ℝ) / (∏ i, m i : ℕ) * (∏ i, (A i).card : ℕ)| ≤
      (∏ i, (A i).card : ℕ) := by
  classical
  let M := ∏ i, m i
  let ρ := ∏ i, (A i).card
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  have hi := periodic_interval_count_scaled_error (residueCondition m A) M S N hM
    (residueCondition_periodic m A)
  rw [residueCondition_count_period m A hm hc] at hi
  have hr : |(M : ℝ) * Nat.count (fun j => residueCondition m A (S + j)) N -
      (N : ℝ) * ρ| ≤ (M : ℝ) * ρ := by exact_mod_cast hi
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : (M : ℝ) * ((N : ℝ) / M * ρ) = (N : ℝ) * ρ := by
    field_simp
  rw [abs_le] at hr ⊢
  constructor <;> nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

def smallResidues (p : ℕ) : Finset (ZMod (p ^ 2)) :=
  (Finset.range p).image (fun r : ℕ => (r : ZMod (p ^ 2)))

theorem smallResidues_card (p : ℕ) (hp : 1 ≤ p) : (smallResidues p).card = p := by
  have hsq : p ≤ p ^ 2 := by nlinarith
  unfold smallResidues
  rw [Finset.card_image_iff.mpr, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < p ^ 2 := lt_of_lt_of_le (Finset.mem_range.mp ha) hsq
  have hb' : b < p ^ 2 := lt_of_lt_of_le (Finset.mem_range.mp hb) hsq
  have hval := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hval

theorem mem_smallResidues (p n : ℕ) (hp : 1 ≤ p) :
    (n : ZMod (p ^ 2)) ∈ smallResidues p ↔ n % p ^ 2 < p := by
  have hsq : p ≤ p ^ 2 := by nlinarith
  constructor
  · intro hn
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hn
    have hr' : r < p ^ 2 := lt_of_lt_of_le (Finset.mem_range.mp hr) hsq
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt hr', ZMod.val_natCast] at hv
    exact hv ▸ Finset.mem_range.mp hr
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨n % p ^ 2, Finset.mem_range.mpr hn, ?_⟩
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_mod _ _)

theorem prime_square_condition_count_period (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    @Nat.count (fun n => ∀ p ∈ s, n % p ^ 2 < p) (Classical.decPred _)
      ((∏ p ∈ s, p) ^ 2) = ∏ p ∈ s, p := by
  classical
  let m (p : s) := (p.val) ^ 2
  let A (p : s) := smallResidues p.val
  have hm : ∀ p : s, 0 < m p := fun p => pow_pos (hs p p.property).pos _
  have hc : Pairwise (fun p q : s => (m p).Coprime (m q)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hs p p.property) (hs q q.property)).mpr
      (Subtype.coe_ne_coe.mpr hpq)).pow 2 2
  have hpredicate : residueCondition m A = (fun n => ∀ p ∈ s, n % p ^ 2 < p) := by
    funext n
    apply propext
    constructor
    · intro hn p hp
      exact (mem_smallResidues p n (hs p hp).one_lt.le).mp (hn ⟨p, hp⟩)
    · intro hn p
      exact (mem_smallResidues p n (hs p p.property).one_lt.le).mpr (hn p p.property)
  have h := residueCondition_count_period m A hm hc
  rw [hpredicate] at h
  have hcard : ∀ p : s, (A p).card = p.val := fun p =>
    smallResidues_card p (hs p p.property).one_lt.le
  simp only [hcard, m, Finset.prod_pow] at h
  have hprod : (∏ p : s, (p : ℕ)) = ∏ p ∈ s, p :=
    Finset.prod_coe_sort s (fun p : ℕ => p)
  rwa [hprod] at h

theorem prime_square_condition_periodic (s : Finset ℕ) :
    Function.Periodic (fun n => ∀ p ∈ s, n % p ^ 2 < p) ((∏ p ∈ s, p) ^ 2) := by
  intro n
  apply propext
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  have hd : p ^ 2 ∣ (∏ q ∈ s, q) ^ 2 :=
    pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp) 2
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero, Nat.mod_mod]


theorem prime_square_interval_scaled_error (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (S N : ℕ) :
    |(((∏ p ∈ s, p) ^ 2 : ℕ) : ℤ) *
        @Nat.count (fun j => ∀ p ∈ s, (S + j) % p ^ 2 < p) (Classical.decPred _) N -
      (N : ℤ) * (∏ p ∈ s, p : ℕ)| ≤
      (((∏ p ∈ s, p) ^ 2 : ℕ) : ℤ) * (∏ p ∈ s, p : ℕ) := by
  classical
  have hm : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hs p hp).pos)
  have h := periodic_interval_count_scaled_error
    (fun n => ∀ p ∈ s, n % p ^ 2 < p) ((∏ p ∈ s, p) ^ 2) S N
    (pow_pos hm _) (prime_square_condition_periodic s)
  have hcount : Nat.count (fun n => ∀ p ∈ s, n % p ^ 2 < p)
      ((∏ p ∈ s, p) ^ 2) = ∏ p ∈ s, p := by
    convert prime_square_condition_count_period s hs using 1
    exact congrArg (fun D : DecidablePred _ => @Nat.count _ D _)
      (Subsingleton.elim _ _)
  rw [hcount] at h
  convert h using 1
  congr 2
  congr 2
  exact congrArg (fun D : DecidablePred _ => @Nat.count _ D _)
    (Subsingleton.elim _ _)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def normalizedFactor (p a : ℝ) : ℝ := 1 + (a - 1) / (p - 1) ^ 2

theorem normalizedFactor_formula (p a : ℝ) (hp : 2 ≤ p) :
    normalizedFactor p a = (1 - 2 / p + a / p ^ 2) / (1 - 1 / p) ^ 2 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hi : 1 - 1 / p ≠ 0 := by
    intro h
    have := (div_eq_one_iff_eq hp0).mp (by linarith : 1 / p = 1)
    linarith
  unfold normalizedFactor
  field_simp [hp0, hp1, hi]
  <;> ring

theorem normalizedFactor_nonneg {p a : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a) :
    0 ≤ normalizedFactor p a := by
  have hden : 0 < (p - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hp1 : p - 1 ≠ 0 := by linarith
  have hnum : 0 ≤ (p - 1) ^ 2 + a - 1 := by nlinarith
  have hid : normalizedFactor p a = ((p - 1) ^ 2 + a - 1) / (p - 1) ^ 2 := by
    unfold normalizedFactor
    field_simp [hp1]
    <;> ring
  rw [hid]
  exact div_nonneg hnum hden.le

theorem normalizedFactor_le {p a : ℝ} (hp : 2 ≤ p) (ha : a ≤ p) :
    normalizedFactor p a ≤ p / (p - 1) := by
  have hden : 0 < (p - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hp1 : p - 1 ≠ 0 := by linarith
  have hid : normalizedFactor p a = ((p - 1) ^ 2 + a - 1) / (p - 1) ^ 2 := by
    unfold normalizedFactor
    field_simp [hp1]
    <;> ring
  rw [hid]
  calc
    _ ≤ (p * (p - 1)) / (p - 1) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith
    _ = p / (p - 1) := by field_simp [hp1]


theorem sum_normalizedFactor {ι : Type*} (S : Finset ι) (p : ℝ) (a : ι → ℝ)
    (ha : ∑ i ∈ S, a i = S.card) :
    ∑ i ∈ S, normalizedFactor p (a i) = S.card := by
  simp only [normalizedFactor, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [ha]
  simp

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

section AddGroup

variable {G : Type*} [AddGroup G] [DecidableEq G]

noncomputable def translatedBack (A : Finset G) (k : G) : Finset G :=
  A.map (Equiv.addRight k).symm.toEmbedding

omit [DecidableEq G] in
theorem mem_translatedBack (A : Finset G) (k x : G) :
    x ∈ translatedBack A k ↔ x + k ∈ A := by
  rw [translatedBack, Finset.mem_map_equiv, Equiv.symm_symm]
  rfl

omit [DecidableEq G] in
theorem translatedBack_card (A : Finset G) (k : G) :
    (translatedBack A k).card = A.card := by
  exact Finset.card_map _

theorem overlap_eq_card_inter (A : Finset G) (k : G) :
    overlap A k = (A ∩ translatedBack A k).card := by
  have hset : A ∩ translatedBack A k = A.filter (fun x => x + k ∈ A) := by
    ext x
    simp [mem_translatedBack]
  rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem two_position_card (A : Finset G) (k : G) :
    (A ∪ translatedBack A k).card + overlap A k = 2 * A.card := by
  rw [overlap_eq_card_inter, Finset.card_union_add_card_inter, translatedBack_card]
  omega

end AddGroup

noncomputable def twoPositionResidues (p : ℕ) (k : ZMod (p ^ 2)) :
    Finset (ZMod (p ^ 2)) := smallResidues p ∪ translatedBack (smallResidues p) k

theorem mem_twoPositionResidues (p : ℕ) (hp : 1 ≤ p) (k n : ℕ) :
    (n : ZMod (p ^ 2)) ∈ twoPositionResidues p (k : ZMod (p ^ 2)) ↔
      n % p ^ 2 < p ∨ (n + k) % p ^ 2 < p := by
  simp only [twoPositionResidues, Finset.mem_union, mem_translatedBack,
    mem_smallResidues p n hp, ← Nat.cast_add, mem_smallResidues p (n + k) hp]

theorem twoPositionResidues_card (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    (twoPositionResidues p k).card + overlap (smallResidues p) k = 2 * p := by
  rw [twoPositionResidues, two_position_card, smallResidues_card p hp]

noncomputable def twoPositionDensity (p : ℕ) (k : ZMod (p ^ 2)) : ℝ :=
  (twoPositionResidues p k).card / (p : ℝ) ^ 2

theorem twoPositionDensity_formula (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    twoPositionDensity p k = 2 / p - (overlap (smallResidues p) k : ℝ) / (p : ℝ) ^ 2 := by
  have hcard := twoPositionResidues_card p hp k
  have hc : ((twoPositionResidues p k).card : ℝ) + overlap (smallResidues p) k = 2 * p := by
    exact_mod_cast hcard
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  unfold twoPositionDensity
  field_simp
  nlinarith

theorem twoPositionDensity_bounds (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    0 ≤ twoPositionDensity p k ∧ twoPositionDensity p k ≤ 2 / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  constructor
  · unfold twoPositionDensity
    positivity
  · rw [twoPositionDensity_formula p hp k]
    have h : (0 : ℝ) ≤ overlap (smallResidues p) k := Nat.cast_nonneg _
    have := div_nonneg h (sq_nonneg (p : ℝ))
    linarith

theorem twoPositionDensity_le_one (p : ℕ) (hp : 1 ≤ p) (k : ZMod (p ^ 2)) :
    twoPositionDensity p k ≤ 1 := by
  let : NeZero p := ⟨by omega⟩
  have hc : (twoPositionResidues p k).card ≤ p ^ 2 := by
    simpa only [Finset.card_univ, ZMod.card] using
      Finset.card_le_card (Finset.subset_univ (twoPositionResidues p k))
  have hcr : ((twoPositionResidues p k).card : ℝ) ≤ (p : ℝ) ^ 2 := by
    exact_mod_cast hc
  exact (div_le_one (sq_pos_of_pos (by exact_mod_cast (by omega : 0 < p)))).mpr hcr

theorem normalized_overlap_sum (p : ℕ) [NeZero p] (hp : 1 ≤ p) :
    (∑ k : ZMod (p ^ 2), normalizedFactor p (overlap (smallResidues p) k)) =
      (p : ℝ) ^ 2 := by
  have ho : (∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ)) = (p : ℝ) ^ 2 := by
    exact_mod_cast (by simpa only [smallResidues_card p hp] using sum_overlap (smallResidues p))
  have hmean : (∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ)) =
      (Finset.univ : Finset (ZMod (p ^ 2))).card := by
    simpa only [Finset.card_univ, ZMod.card, Nat.cast_pow] using ho
  simpa only [Finset.card_univ, ZMod.card, Nat.cast_pow] using
    sum_normalizedFactor (Finset.univ : Finset (ZMod (p ^ 2))) p
      (fun k => (overlap (smallResidues p) k : ℝ)) hmean

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def residueIndicator {m : ℕ} (A : Finset (ZMod m)) (x : ZMod m) : ℂ :=
  if x ∈ A then 1 else 0

noncomputable def residueFourier {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (k : ZMod m) : ℂ :=
  ZMod.dft (residueIndicator A) k / (m : ℂ)

theorem norm_stdAddChar {m : ℕ} [NeZero m] (x : ZMod m) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem residue_dft_sum {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (k : ZMod m) :
    ZMod.dft (residueIndicator A) k = ∑ x ∈ A, ZMod.stdAddChar (-(x * k)) := by
  classical
  rw [ZMod.dft_apply]
  simp only [residueIndicator, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem residueFourier_zero {m : ℕ} [NeZero m] (A : Finset (ZMod m)) :
    residueFourier A 0 = (A.card : ℂ) / (m : ℂ) := by
  unfold residueFourier
  rw [residue_dft_sum]
  simp

theorem residueFourier_norm_le {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (k : ZMod m) :
    ‖residueFourier A k‖ ≤ (A.card : ℝ) / (m : ℝ) := by
  unfold residueFourier
  rw [norm_div, Complex.norm_natCast, residue_dft_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  calc
    _ ≤ ∑ x ∈ A, ‖ZMod.stdAddChar (-(x * k))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_stdAddChar, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem residueFourier_inversion {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (n : ZMod m) :
    residueIndicator A n =
      ∑ k : ZMod m, residueFourier A k * ZMod.stdAddChar (k * n) := by
  have h := congrArg (fun f : ZMod m → ℂ => f n) (ZMod.dft.symm_apply_apply (residueIndicator A))
  rw [ZMod.invDFT_apply] at h
  rw [← h]
  simp only [residueFourier, smul_eq_mul, Finset.mul_sum, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem smallResidues_fourier_zero (p : ℕ) (hp : 1 ≤ p) :
    letI : NeZero p := ⟨by omega⟩
    residueFourier (smallResidues p) 0 = 1 / (p : ℂ) := by
  letI : NeZero p := ⟨by omega⟩
  rw [residueFourier_zero, smallResidues_card p hp, Nat.cast_pow]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem smallResidues_fourier_norm_le (p : ℕ) (hp : 1 ≤ p) :
    letI : NeZero p := ⟨by omega⟩
    ∀ k : ZMod (p ^ 2), ‖residueFourier (smallResidues p) k‖ ≤ 1 / (p : ℝ) := by
  letI : NeZero p := ⟨by omega⟩
  intro k
  have h := residueFourier_norm_le (smallResidues p) k
  rw [smallResidues_card p hp, Nat.cast_pow] at h
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have heq : (p : ℝ) / (p : ℝ) ^ 2 = 1 / p := by field_simp
  rwa [heq] at h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def boxMean (H : ℕ) (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  (∑ h ∈ Finset.range H, f (n + h)) / (H : ℂ)

noncomputable def boxMultiplier (H : ℕ) (χ : AddChar ℤ ℂ) : ℂ :=
  (∑ h ∈ Finset.range H, χ h) / (H : ℂ)

noncomputable def boxSmooth (H : ℕ) : ℕ → (ℤ → ℂ) → (ℤ → ℂ)
  | 0, f => f
  | J + 1, f => boxMean H (boxSmooth H J f)

theorem boxMean_add (H : ℕ) (f g : ℤ → ℂ) (n : ℤ) :
    boxMean H (fun k => f k + g k) n = boxMean H f n + boxMean H g n := by
  simp only [boxMean, Finset.sum_add_distrib, add_div]

theorem boxMean_const_mul (H : ℕ) (c : ℂ) (f : ℤ → ℂ) (n : ℤ) :
    boxMean H (fun k => c * f k) n = c * boxMean H f n := by
  simp only [boxMean, ← Finset.mul_sum]
  ring

theorem boxMean_character (H : ℕ) (χ : AddChar ℤ ℂ) (n : ℤ) :
    boxMean H χ n = boxMultiplier H χ * χ n := by
  simp only [boxMean, boxMultiplier, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  ring

theorem boxSmooth_character (H J : ℕ) (χ : AddChar ℤ ℂ) (n : ℤ) :
    boxSmooth H J χ n = (boxMultiplier H χ) ^ J * χ n := by
  induction J generalizing n with
  | zero => simp only [boxSmooth, pow_zero, one_mul]
  | succ J ih =>
      change boxMean H (boxSmooth H J χ) n = _
      have hfun : boxSmooth H J χ = fun k => (boxMultiplier H χ) ^ J * χ k := funext ih
      rw [hfun, boxMean_const_mul, boxMean_character, pow_succ]
      ring

theorem norm_boxMultiplier_le_one (H : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) : ‖boxMultiplier H χ‖ ≤ 1 := by
  unfold boxMultiplier
  rw [norm_div, Complex.norm_natCast]
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_one hHreal).mpr
  calc
    _ ≤ ∑ h ∈ Finset.range H, ‖χ h‖ := norm_sum_le _ _
    _ = _ := by simp only [hχ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem norm_boxMultiplier_decay (H : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) :
    ‖boxMultiplier H χ‖ ≤ 2 / ((H : ℝ) * ‖χ 1 - 1‖) := by
  have hpow (h : ℕ) : χ (h : ℤ) = (χ 1) ^ h := by
    simpa only [nsmul_eq_mul, mul_one] using χ.map_nsmul_eq_pow h (1 : ℤ)
  have hgeom : (∑ h ∈ Finset.range H, χ (h : ℤ)) = ((χ 1) ^ H - 1) / (χ 1 - 1) := by
    simp_rw [hpow]
    exact geom_sum_eq hχ1 H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hdiff : 0 < ‖χ 1 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hχ1)
  have hnum : ‖(χ 1) ^ H - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(χ 1) ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hχ, norm_one, one_pow]; norm_num
  unfold boxMultiplier
  rw [hgeom, norm_div, norm_div, Complex.norm_natCast, div_div]
  simpa only [mul_comm] using div_le_div_of_nonneg_right hnum (mul_pos hdiff hHreal).le

theorem norm_boxSmooth_character_le (H J : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (n : ℤ) : ‖boxSmooth H J χ n‖ ≤ 1 := by
  rw [boxSmooth_character, norm_mul, norm_pow, hχ, mul_one]
  exact pow_le_one₀ (norm_nonneg _) (norm_boxMultiplier_le_one H hH χ hχ)

theorem norm_boxSmooth_character_decay (H J : ℕ) (hH : 0 < H) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) (n : ℤ) :
    ‖boxSmooth H J χ n‖ ≤ (2 / ((H : ℝ) * ‖χ 1 - 1‖)) ^ J := by
  rw [boxSmooth_character, norm_mul, norm_pow, hχ, mul_one]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_boxMultiplier_decay H hH χ hχ hχ1) J

end Erdos676
end

section
namespace Erdos676

noncomputable def residueFrequency {m : ℕ} [NeZero m] (k : ZMod m) : ℝ :=
  (k.valMinAbs : ℝ) / (m : ℝ)

noncomputable def residueCharacter {m : ℕ} [NeZero m] (k : ZMod m) : AddChar ℤ ℂ where
  toFun n := ZMod.stdAddChar (k * (n : ZMod m))
  map_zero_eq_one' := by simp [AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by rw [Int.cast_add, mul_add, AddChar.map_add_eq_mul]

theorem residueCharacter_norm {m : ℕ} [NeZero m] (k : ZMod m) (n : ℤ) :
    ‖residueCharacter k n‖ = 1 := norm_stdAddChar _

theorem residueCharacter_one {m : ℕ} [NeZero m] (k : ZMod m) :
    residueCharacter k 1 = ZMod.stdAddChar k := by simp [residueCharacter]

theorem abs_residueFrequency_le_half {m : ℕ} [NeZero m] (k : ZMod m) :
    |residueFrequency k| ≤ 1 / 2 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hlo : -(m : ℝ) < (k.valMinAbs : ℝ) * 2 := by exact_mod_cast k.valMinAbs_mem_Ioc.1
  have hhi : (k.valMinAbs : ℝ) * 2 ≤ m := by exact_mod_cast k.valMinAbs_mem_Ioc.2
  unfold residueFrequency
  rw [abs_div, abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  exact (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem residueFrequency_ne_zero {m : ℕ} [NeZero m] {k : ZMod m} (hk : k ≠ 0) :
    residueFrequency k ≠ 0 := by
  apply div_ne_zero
  · exact Int.cast_ne_zero.mpr (fun h => hk ((ZMod.valMinAbs_eq_zero k).mp h))
  · exact Nat.cast_ne_zero.mpr (NeZero.ne m)

theorem stdAddChar_frequency {m : ℕ} [NeZero m] (k : ZMod m) :
    ZMod.stdAddChar k = Complex.exp (Complex.I * ((2 * Real.pi * residueFrequency k : ℝ) : ℂ)) := by
  calc
    _ = ZMod.stdAddChar (k.valMinAbs : ZMod m) := congrArg ZMod.stdAddChar k.coe_valMinAbs.symm
    _ = Complex.exp (2 * Real.pi * Complex.I * k.valMinAbs / m) := ZMod.stdAddChar_coe _
    _ = _ := by congr 1; unfold residueFrequency; push_cast; ring

theorem stdAddChar_sub_one_lower {m : ℕ} [NeZero m] (k : ZMod m) :
    4 * |residueFrequency k| ≤ ‖ZMod.stdAddChar k - 1‖ := by
  have hfreq := abs_residueFrequency_le_half k
  have harg : |Real.pi * residueFrequency k| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hfreq Real.pi_pos.le
      _ = _ := by ring
  have hsin := Real.mul_abs_le_abs_sin harg
  have hcancel : 2 / Real.pi * |Real.pi * residueFrequency k| = 2 * |residueFrequency k| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hcancel] at hsin
  rw [stdAddChar_frequency, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have harg' : 2 * Real.pi * residueFrequency k / 2 = Real.pi * residueFrequency k := by ring
  rw [harg', abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem residue_boxMultiplier_decay {m : ℕ} [NeZero m] (k : ZMod m) (hk : k ≠ 0)
    (H : ℕ) (hH : 0 < H) :
    ‖boxMultiplier H (residueCharacter k)‖ ≤ 1 / ((H : ℝ) * |residueFrequency k|) := by
  have hk1 : ZMod.stdAddChar k ≠ 1 := by
    intro h
    apply hk
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using h
  have hc1 : residueCharacter k 1 ≠ 1 := by rwa [residueCharacter_one]
  have h := norm_boxMultiplier_decay H hH (residueCharacter k) (residueCharacter_norm k) hc1
  rw [residueCharacter_one] at h
  have hf : 0 < |residueFrequency k| := abs_pos.mpr (residueFrequency_ne_zero hk)
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hnorm : 0 < ‖ZMod.stdAddChar k - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hk1)
  have hgap := stdAddChar_sub_one_lower k
  apply h.trans
  apply (div_le_div_iff₀ (mul_pos hHreal hnorm) (mul_pos hHreal hf)).mpr
  nlinarith

end Erdos676
end

section
open scoped BigOperators ComplexConjugate

namespace Erdos676

theorem character_sum_norm_le (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ n ∈ Finset.range L, χ n‖ ≤ L := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, ‖χ n‖ := norm_sum_le _ _
    _ = _ := by simp only [hχ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem character_sum_decay (L : ℕ) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) :
    ‖∑ n ∈ Finset.range L, χ n‖ ≤ 2 / ‖χ 1 - 1‖ := by
  have hpow (n : ℕ) : χ (n : ℤ) = (χ 1) ^ n := by
    simpa only [nsmul_eq_mul, mul_one] using χ.map_nsmul_eq_pow n (1 : ℤ)
  simp_rw [hpow]
  rw [geom_sum_eq hχ1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ‖(χ 1) ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hχ, norm_one, one_pow]; norm_num

theorem pair_character_sum (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)) =
      (∑ a ∈ Finset.range L, χ a) * star (∑ b ∈ Finset.range L, χ b) := by
  have hstar : star (∑ b ∈ Finset.range L, χ (b : ℤ)) =
      ∑ b ∈ Finset.range L, star (χ (b : ℤ)) := map_sum (starRingEnd ℂ) _ _
  simp only [AddChar.map_sub_eq_div, div_eq_mul_inv, Complex.inv_eq_conj (hχ _),
    hstar, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  rw [Finset.sum_comm]

theorem pair_character_sum_norm (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)‖ =
      ‖∑ a ∈ Finset.range L, χ a‖ ^ 2 := by
  rw [pair_character_sum L χ hχ, norm_mul, norm_star, pow_two]

theorem pair_character_sum_norm_le (L : ℕ) (χ : AddChar ℤ ℂ) (hχ : ∀ n, ‖χ n‖ = 1) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)‖ ≤ (L : ℝ) ^ 2 := by
  rw [pair_character_sum_norm L χ hχ]
  exact pow_le_pow_left₀ (norm_nonneg _) (character_sum_norm_le L χ hχ) 2

theorem pair_character_sum_decay (L : ℕ) (χ : AddChar ℤ ℂ)
    (hχ : ∀ n, ‖χ n‖ = 1) (hχ1 : χ 1 ≠ 1) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, χ ((a : ℤ) - b)‖ ≤
      (2 / ‖χ 1 - 1‖) ^ 2 := by
  rw [pair_character_sum_norm L χ hχ]
  exact pow_le_pow_left₀ (norm_nonneg _) (character_sum_decay L χ hχ hχ1) 2

end Erdos676
end

section
namespace Erdos676

noncomputable def realCharacter (θ : ℝ) : AddChar ℤ ℂ where
  toFun n := Complex.exp (Complex.I * ((2 * Real.pi * θ * (n : ℝ) : ℝ) : ℂ))
  map_zero_eq_one' := by simp
  map_add_eq_mul' n k := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem realCharacter_norm (θ : ℝ) (n : ℤ) : ‖realCharacter θ n‖ = 1 := by
  simp [realCharacter, Complex.norm_exp, Complex.mul_re]

theorem realCharacter_one (θ : ℝ) :
    realCharacter θ 1 = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
  simp [realCharacter]

theorem realCharacter_gap (θ : ℝ) (hθ : |θ| ≤ 1 / 2) :
    4 * |θ| ≤ ‖realCharacter θ 1 - 1‖ := by
  have harg : |Real.pi * θ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    calc
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hθ Real.pi_pos.le
      _ = _ := by ring
  have hsin := Real.mul_abs_le_abs_sin harg
  have hcancel : 2 / Real.pi * |Real.pi * θ| = 2 * |θ| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hcancel] at hsin
  rw [realCharacter_one, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  rw [show 2 * Real.pi * θ / 2 = Real.pi * θ by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem realCharacter_difference (θ φ : ℝ) (n : ℤ) :
    star (realCharacter θ n) * realCharacter φ n = realCharacter (φ - θ) n := by
  have hinv := Complex.inv_eq_conj (realCharacter_norm θ n)
  rw [starRingEnd_apply] at hinv
  rw [← hinv, mul_comm, ← div_eq_mul_inv]
  change Complex.exp _ / Complex.exp _ = Complex.exp _
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem residueCharacter_eq_realCharacter {m : ℕ} [NeZero m] (k : ZMod m) :
    residueCharacter k = realCharacter (residueFrequency k) := by
  apply AddChar.ext
  intro n
  have hleft : residueCharacter k n = (residueCharacter k 1) ^ n := by
    simpa using (residueCharacter k).map_zsmul_eq_zpow n (1 : ℤ)
  have hright : realCharacter (residueFrequency k) n = (realCharacter (residueFrequency k) 1) ^ n := by
    simpa using (realCharacter (residueFrequency k)).map_zsmul_eq_zpow n (1 : ℤ)
  rw [hleft, hright, residueCharacter_one, realCharacter_one, stdAddChar_frequency]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem kernel_envelope (L t K : ℝ) (hL : 0 < L) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hbase : K ≤ L ^ 2) (htail : K * t ^ 2 ≤ 1) :
    K ≤ 4 * L ^ 2 / (1 + L * t) ^ 2 := by
  have hden : 0 < 1 + L * t := by positivity
  apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
  by_cases hsmall : L * t ≤ 1
  · have hsquare := pow_le_pow_left₀ hden.le (show 1 + L * t ≤ 2 by linarith) 2
    have hscaled := mul_le_mul_of_nonneg_left hsquare hK
    nlinarith
  · have hlarge : 1 ≤ L * t := (lt_of_not_ge hsmall).le
    have hsquare := pow_le_pow_left₀ hden.le (show 1 + L * t ≤ 2 * L * t by linarith) 2
    have hscaled := mul_le_mul_of_nonneg_left hsquare hK
    have hlast := mul_le_mul_of_nonneg_left htail (show 0 ≤ 4 * L ^ 2 by positivity)
    nlinarith

theorem real_pair_kernel_bound (L : ℕ) (hL : 0 < L) (θ : ℝ) (hθ : |θ| ≤ 1 / 2) :
    ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, realCharacter θ ((a : ℤ) - b)‖ ≤
      4 * (L : ℝ) ^ 2 / (1 + L * |θ|) ^ 2 := by
  let K := ‖∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, realCharacter θ ((a : ℤ) - b)‖
  have hbase : K ≤ (L : ℝ) ^ 2 := pair_character_sum_norm_le L _ (realCharacter_norm θ)
  have htail : K * |θ| ^ 2 ≤ 1 := by
    by_cases hz : θ = 0
    · simp [hz]
    · have hpos : 0 < |θ| := abs_pos.mpr hz
      have hgap := realCharacter_gap θ hθ
      have hne : realCharacter θ 1 ≠ 1 := by
        intro heq
        rw [heq, sub_self, norm_zero] at hgap
        linarith
      have hsum := character_sum_decay L (realCharacter θ) (realCharacter_norm θ) hne
      have hnorm : 0 < ‖realCharacter θ 1 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hrecip : 2 / ‖realCharacter θ 1 - 1‖ ≤ 1 / |θ| := by
        apply (div_le_div_iff₀ hnorm hpos).mpr
        linarith
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) (hsum.trans hrecip) 2
      have heq : (1 / |θ|) ^ 2 * |θ| ^ 2 = 1 := by field_simp
      have hscaled := mul_le_mul_of_nonneg_right hsquare (sq_nonneg |θ|)
      rw [← pair_character_sum_norm L (realCharacter θ) (realCharacter_norm θ)] at hscaled
      exact hscaled.trans_eq heq
  exact kernel_envelope L |θ| K (by exact_mod_cast hL) (abs_nonneg _) (norm_nonneg _) hbase htail

end Erdos676
end

section
open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp)
    (RCLike.continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_B1) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end

section
theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl

namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

section Issue1584
open MeasureTheory Set Filter Topology


private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep


private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]


private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  have hf1 : f 1 = 0 := by simp [hf_def]
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    have hinj : InjOn f (Ici 1) := hmono.injOn
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      rw [Real.log_mul hs1ne hlogne]
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens


open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - ⌊x⌋₊ - 1 / 2) * log x - x + 1 + ∫ t in 1..x, (t - ⌊t⌋₊ - 1 / 2) / t := by
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  have : 1 = ⌊(1 : ℝ)⌋₊ := by simp
  nth_rw 1 [this]
  rw [sum_eq_integral_add_integral_deriv (by norm_num) hx (fun _ _ ↦ (by fun_prop (disch := grind)))]
  · simp only [log_one, B1, Nat.floor_one, Nat.cast_one, sub_self, zero_sub,
    RCLike.ofReal_real_eq_id, id_eq, mul_neg, zero_mul, neg_zero, integral_log, mul_zero, sub_zero,
    deriv_log']
    ring_nf
    congr
    ext
    ring
  · simp only [deriv_log', Set.uIcc_of_le hx]
    fun_prop (disch := grind)

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop

theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! E₁Λ.bounded using 1

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩

theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

-- Helpers for `log_zeta_eq_integ` (#1583): Abel summation / sum-integral interchange.
namespace LogZetaInteg


private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)


private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]


private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity


private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop


private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log


private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb


theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

-- Integrability helpers for the integral splitting in `log_zeta_eq` (#1319).
-- Each summand of `(log (log x) + γ + E₂Λ x) * x^(-s)` is separately integrable on `Ioi 1`.


private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]


private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith


private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ


private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  rw [log_zeta_eq_integ s hs]
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

-- Helpers for `deriv_gamma_add_γ_eq_zero` (#1320): take `s → 1⁺` in `log_zeta_eq`.
section
open MeasureTheory Set


private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop


private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp


private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith


private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)


private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo


private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1


private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]

theorem sum_mangoldt_div_log_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)| ≤ C := by
    use (log 4 + 6)/log 2 + |eulerMascheroniConstant|
    intro x hx
    rw [sum_mangoldt_div_log_eq]
    calc
      _ = |E₂Λ x + eulerMascheroniConstant| := by ring_nf
      _ ≤ (log 4 + 6)/log x + |eulerMascheroniConstant| := by grw [abs_add_le, E₂Λ.abs_le hx]
      _ ≤ _ := by gcongr

theorem sum_mangoldt_div_log_eq_log_log' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2

theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_mangoldt_div_log_eq_log_log' using 1

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]

theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2

theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_prime_div_eq_log_log' using 1

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'


noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le

theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]

theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]

theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one

theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp ((isLittleO_one_iff ℝ).mp E₃.bound')) using 2 with x
     · simp
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind

theorem E₃.bound''' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p) - exp (-eulerMascheroniConstant) / log x) =O[atTop] (fun x ↦ 1 / (log x)^2) := by
  obtain ⟨c, hc⟩ := E₃.abs_le
  rw [isBigO_iff]
  refine ⟨exp (-eulerMascheroniConstant) * 2 * c, ?_⟩
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop c.exp] with x hx hx2
  rw [prod_one_minus_div_prime_eq (by linarith)]
  specialize hc x hx
  rw [norm_eq_abs, norm_eq_abs]
  calc
  _ = |exp (-eulerMascheroniConstant) / log x * (exp (E₃ x) - 1)| := by ring_nf
  _ = |exp (-eulerMascheroniConstant) / log x| * |exp (E₃ x) - 1| := by rw [abs_mul]
  _ ≤ _ := by
    have : |E₃ x| ≤ 1 := by
      apply hc.trans
      have := log_le_log (exp_pos _) hx2
      rw [log_exp] at this
      apply div_le_one_iff.mpr <| Or.inl ⟨log_pos (by linarith), this⟩
    grw [abs_exp_sub_one_le this, hc]
    apply le_of_eq
    rw [abs_div, abs_div, abs_one, abs_of_nonneg (exp_nonneg _), abs_of_nonneg (log_nonneg (by linarith)), abs_of_nonneg (sq_nonneg _)]
    ring

end Mertens
end

section
open scoped BigOperators
open Filter Asymptotics

namespace Erdos676

noncomputable def primesUpToReal (x : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime

noncomputable def primeReciprocalSum (x : ℝ) : ℝ :=
  ∑ p ∈ primesUpToReal x, (1 : ℝ) / p

noncomputable def survivalProduct (x : ℝ) : ℝ :=
  ∏ p ∈ primesUpToReal x, (1 - (1 : ℝ) / p)

theorem prime_reciprocal_error :
    ∃ B C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum x - Real.log (Real.log x) - B| ≤ C / Real.log x := by
  refine ⟨Mertens.M, Real.log 4 + 6 + Mertens.E₁, ?_, ?_⟩
  · have hE := Mertens.E₁.nonneg
    have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  · intro x hx
    simpa only [primeReciprocalSum, primesUpToReal, Mertens.E₂p, one_div]
      using Mertens.E₂p.abs_le hx

theorem survivalProduct_asymptotic :
    survivalProduct ~[atTop]
      (fun x : ℝ => Real.exp (-Real.eulerMascheroniConstant) / Real.log x) := by
  exact Mertens.E₃.bound''

theorem survivalProduct_pos (x : ℝ) : 0 < survivalProduct x := by
  unfold survivalProduct
  apply Finset.prod_pos
  intro p hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact sub_pos.mpr ((div_lt_one hp0).mpr hp1)

theorem survivalProduct_formula {x : ℝ} (hx : 1 < x) :
    survivalProduct x = Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Mertens.E₃ x) / Real.log x := by
  exact Mertens.prod_one_minus_div_prime_eq hx

end Erdos676
end

section
namespace Erdos676


theorem moment_gap_from_bounds {A Q K N V d e : ℝ}
    (hN : 0 < N) (hV : 0 < V) (hQ : 0 ≤ Q)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (he1 : e < 1)
    (hsmall : 3 * e < d)
    (hfirst : (1 - e) * N * V ≤ A)
    (hsecond : Q ≤ (1 + e) * N * V ^ 2)
    (hcomplement : K ≤ (1 - d) * N) :
    0 < A ∧ K * Q < A ^ 2 := by
  have hpositive : 0 < (1 - e) * N * V :=
    mul_pos (mul_pos (sub_pos.mpr he1) hN) hV
  have hA : 0 < A := lt_of_lt_of_le hpositive hfirst
  refine ⟨hA, ?_⟩
  have hcompare := scalar_moment_gap hd he hsmall
  have hscale : 0 < N ^ 2 * V ^ 2 := mul_pos (sq_pos_of_pos hN) (sq_pos_of_pos hV)
  have hscaled := mul_lt_mul_of_pos_right hcompare hscale
  calc
    K * Q ≤ ((1 - d) * N) * ((1 + e) * N * V ^ 2) :=
      mul_le_mul hcomplement hsecond hQ (mul_nonneg (sub_nonneg.mpr hd1) hN.le)
    _ < ((1 - e) * N * V) ^ 2 := by nlinarith [hscaled]
    _ ≤ A ^ 2 := by nlinarith


theorem exists_linear_quadratic_margin {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ α : ℝ, 0 < α ∧ c * α ≤ 1 ∧ 0 ≤ C * α ^ 2 ∧ C * α ^ 2 < 1 ∧
      3 * (C * α ^ 2) < c * α := by
  let α := min (1 / (2 * c)) (c / (6 * C))
  have hα : 0 < α := lt_min (div_pos (by norm_num) (by positivity))
    (div_pos hc (by positivity))
  have hleft : α * (2 * c) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * c)).mp (min_le_left _ _)
  have hright : α * (6 * C) ≤ c :=
    (le_div_iff₀ (by positivity : 0 < 6 * C)).mp (min_le_right _ _)
  have hpos : 0 < 3 * C * α := by positivity
  have hfirst : 3 * C * α < c := by nlinarith
  have hgap : 3 * (C * α ^ 2) < c * α := by
    have := mul_lt_mul_of_pos_right hfirst hα
    nlinarith
  refine ⟨α, hα, ?_, mul_nonneg hC.le (sq_nonneg α), ?_, hgap⟩ <;> nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def bracketLoss {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (lower upper : ι → ℝ) : ℝ :=
  ∑ j ∈ s, (upper j - lower j) * ∏ i ∈ s.erase j, upper i

theorem bracketLoss_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (j : ι) (hj : j ∉ s) (lower upper : ι → ℝ) :
    bracketLoss (insert j s) lower upper =
      (upper j - lower j) * (∏ i ∈ s, upper i) + upper j * bracketLoss s lower upper := by
  unfold bracketLoss
  rw [Finset.sum_insert hj, Finset.erase_insert hj, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hji : j ≠ i := by
    intro h
    subst i
    exact hj hi
  rw [Finset.erase_insert_of_ne hji, Finset.prod_insert]
  · ring
  · exact fun h => hj (Finset.mem_of_mem_erase h)


theorem product_lower_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (actual lower upper : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ actual i)
    (hl : ∀ i ∈ s, lower i ≤ actual i)
    (hu : ∀ i ∈ s, actual i ≤ upper i) :
    (∏ i ∈ s, upper i) - bracketLoss s lower upper ≤ ∏ i ∈ s, actual i := by
  induction s using Finset.induction_on with
  | empty => simp [bracketLoss]
  | @insert j s hj ih =>
      have haS : ∀ i ∈ s, 0 ≤ actual i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hlS : ∀ i ∈ s, lower i ≤ actual i := fun i hi => hl i (Finset.mem_insert_of_mem hi)
      have huS : ∀ i ∈ s, actual i ≤ upper i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have haj := ha j (Finset.mem_insert_self j s)
      have hlj := hl j (Finset.mem_insert_self j s)
      have huj := hu j (Finset.mem_insert_self j s)
      have hup : ∀ i ∈ s, 0 ≤ upper i := fun i hi => (haS i hi).trans (huS i hi)
      have hp : 0 ≤ ∏ i ∈ s, upper i := Finset.prod_nonneg hup
      have hL : 0 ≤ bracketLoss s lower upper := by
        unfold bracketLoss
        apply Finset.sum_nonneg
        intro i hi
        exact mul_nonneg (sub_nonneg.mpr ((hlS i hi).trans (huS i hi)))
          (Finset.prod_nonneg fun k hk => hup k (Finset.mem_of_mem_erase hk))
      have hscaled := mul_le_mul_of_nonneg_left (ih haS hlS huS) haj
      have hterm1 := mul_nonneg (sub_nonneg.mpr hlj) hp
      have hterm2 := mul_nonneg (sub_nonneg.mpr huj) hL
      rw [Finset.prod_insert hj, Finset.prod_insert hj, bracketLoss_insert s j hj]
      nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def bernoulliWeight {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) : ℝ :=
  (∏ i ∈ t, g i) * ∏ i ∈ s \ t, (1 - g i)

theorem sum_bernoulliWeight {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) :
    ∑ t ∈ s.powerset, bernoulliWeight s t g = 1 := by
  have h := Finset.prod_add g (fun i => 1 - g i) s
  simpa [bernoulliWeight] using h.symm

theorem bernoulliWeight_nonneg {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (ht : t ⊆ s)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    0 ≤ bernoulliWeight s t g := by
  unfold bernoulliWeight
  exact mul_nonneg (Finset.prod_nonneg fun i hi => hg0 i (ht hi))
    (Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hg1 i (Finset.mem_sdiff.mp hi).1))


theorem weighted_square_tail_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w value : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s with R < value i, w i) * R ^ 2 ≤
      ∑ i ∈ s, w i * (value i) ^ 2 := by
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i ∈ s with R < value i, w i * (value i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hlarge⟩ := Finset.mem_filter.mp hi
      apply mul_le_mul_of_nonneg_left _ (hw i his)
      nlinarith
    _ ≤ ∑ i ∈ s, w i * (value i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi _ => mul_nonneg (hw i hi) (sq_nonneg _))

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bernoulliWeight_factorization {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (ht : t ⊆ s)
    (hg : ∀ i ∈ s, g i ≠ 1) :
    bernoulliWeight s t g =
      (∏ i ∈ s, (1 - g i)) * ∏ i ∈ t, (g i / (1 - g i)) := by
  have ht0 : (∏ i ∈ t, (1 - g i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (Ne.symm (hg i (ht hi)))
  rw [Finset.prod_div_distrib, ← Finset.prod_sdiff ht]
  unfold bernoulliWeight
  field_simp


theorem truncated_sieve_normalization {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (keep : Finset ι → Prop) [DecidablePred keep]
    (hg : ∀ i ∈ s, g i ≠ 1) :
    (∑ t ∈ s.powerset with keep t, ∏ i ∈ t, g i / (1 - g i)) *
        (∏ i ∈ s, (1 - g i)) =
      ∑ t ∈ s.powerset with keep t, bernoulliWeight s t g := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [bernoulliWeight_factorization s t g
    (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1) hg]
  ring


theorem bernoulli_truncation_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (value : Finset ι → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i ≤ 1) :
    (1 - ∑ t ∈ s.powerset with value t ≤ R, bernoulliWeight s t g) * R ^ 2 ≤
      ∑ t ∈ s.powerset, bernoulliWeight s t g * (value t) ^ 2 := by
  classical
  have htotal := Finset.sum_filter_add_sum_filter_not s.powerset
    (fun t => value t ≤ R) (fun t => bernoulliWeight s t g)
  rw [sum_bernoulliWeight] at htotal
  simp only [not_le] at htotal
  have ht := weighted_square_tail_bound s.powerset (fun t => bernoulliWeight s t g)
    value R hR (fun t ht => bernoulliWeight_nonneg s t g
      (Finset.mem_powerset.mp ht) hg0 hg1)
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bernoulliWeight_insert_absent {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (i : ι) (hi : i ∉ s) (ht : t ⊆ s) :
    bernoulliWeight (insert i s) t g = (1 - g i) * bernoulliWeight s t g := by
  have hit : i ∉ t := fun h => hi (ht h)
  have hisdiff : i ∉ s \ t := fun h => hi (Finset.mem_sdiff.mp h).1
  unfold bernoulliWeight
  rw [Finset.insert_sdiff_of_notMem _ hit, Finset.prod_insert hisdiff]
  ring

theorem bernoulliWeight_insert_present {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (g : ι → ℝ) (i : ι) (hi : i ∉ s) (ht : t ⊆ s) :
    bernoulliWeight (insert i s) (insert i t) g = g i * bernoulliWeight s t g := by
  have hit : i ∉ t := fun h => hi (ht h)
  simp only [bernoulliWeight, Finset.insert_sdiff_insert,
    Finset.sdiff_insert_of_notMem hi, Finset.prod_insert hit]
  ring

theorem bernoulli_expectation_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (F : Finset ι → ℝ) (i : ι) (hi : i ∉ s) :
    (∑ t ∈ (insert i s).powerset, bernoulliWeight (insert i s) t g * F t) =
      (1 - g i) * (∑ t ∈ s.powerset, bernoulliWeight s t g * F t) +
      g i * (∑ t ∈ s.powerset, bernoulliWeight s t g * F (insert i t)) := by
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [bernoulliWeight_insert_absent s t g i hi (Finset.mem_powerset.mp ht)]
    ring
  · apply Finset.sum_congr rfl
    intro t ht
    rw [bernoulliWeight_insert_present s t g i hi (Finset.mem_powerset.mp ht)]
    ring

theorem bernoulli_first_moment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ i ∈ t, f i)) =
      ∑ i ∈ s, g i * f i := by
  induction s using Finset.induction_on with
  | empty => simp [bernoulliWeight]
  | @insert i s hi ih =>
      rw [bernoulli_expectation_insert s g _ i hi]
      have hshift : (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ j ∈ insert i t, f j)) =
          f i + (∑ j ∈ s, g j * f j) := by
        calc
          _ = ∑ t ∈ s.powerset, bernoulliWeight s t g *
              (f i + ∑ j ∈ t, f j) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.sum_insert (fun h => hi (Finset.mem_powerset.mp ht h))]
          _ = f i + (∑ j ∈ s, g j * f j) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
              sum_bernoulliWeight, one_mul, ih]
      rw [ih, hshift, Finset.sum_insert hi]
      ring

theorem bernoulli_second_moment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ i ∈ t, f i) ^ 2) =
      (∑ i ∈ s, g i * f i) ^ 2 + ∑ i ∈ s, g i * (1 - g i) * (f i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp [bernoulliWeight]
  | @insert i s hi ih =>
      rw [bernoulli_expectation_insert s g _ i hi]
      have hshift : (∑ t ∈ s.powerset, bernoulliWeight s t g *
          (∑ j ∈ insert i t, f j) ^ 2) =
          (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ j ∈ t, f j) ^ 2) +
          2 * f i * (∑ j ∈ s, g j * f j) + (f i) ^ 2 := by
        calc
          _ = ∑ t ∈ s.powerset,
              (bernoulliWeight s t g * (∑ j ∈ t, f j) ^ 2 +
              (2 * f i) * (bernoulliWeight s t g * (∑ j ∈ t, f j)) +
              bernoulliWeight s t g * (f i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.sum_insert (fun h => hi (Finset.mem_powerset.mp ht h))]
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
              sum_bernoulliWeight, one_mul, bernoulli_first_moment]
      rw [hshift, ih, Finset.sum_insert hi, Finset.sum_insert hi]
      ring

theorem bernoulli_second_moment_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g * (∑ i ∈ t, f i) ^ 2) ≤
      (∑ i ∈ s, g i * f i) ^ 2 + ∑ i ∈ s, g i * (f i) ^ 2 := by
  rw [bernoulli_second_moment]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i hi
  have h : g i * (1 - g i) ≤ g i := by nlinarith [sq_nonneg (g i)]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)


theorem truncated_sieve_second_moment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g f : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hg1 : ∀ i ∈ s, g i < 1) :
    (1 - (∑ t ∈ s.powerset with (∑ i ∈ t, f i) ≤ R,
        ∏ i ∈ t, g i / (1 - g i)) * (∏ i ∈ s, (1 - g i))) * R ^ 2 ≤
      (∑ i ∈ s, g i * f i) ^ 2 + ∑ i ∈ s, g i * (f i) ^ 2 := by
  classical
  rw [truncated_sieve_normalization s g _ (fun i hi => ne_of_lt (hg1 i hi))]
  exact (bernoulli_truncation_bound s g (fun t => ∑ i ∈ t, f i) R hR hg0
    (fun i hi => (hg1 i hi).le)).trans
      (bernoulli_second_moment_le s g f)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_log_reciprocal_upper {z : ℝ} (hz : 1 ≤ z) :
    (∑ p ∈ primesUpToReal z, Real.log p / p) ≤ Real.log z + (Real.log 4 + 4) := by
  have h := (abs_le.mp (Mertens.sum_log_prime_div_eq_log hz)).2
  change (∑ p ∈ primesUpToReal z, Real.log p / p) - Real.log z ≤ Real.log 4 + 4 at h
  linarith

theorem prime_log_moments {z : ℝ} (hz : 2 ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ primesUpToReal z, 0 ≤ g p)
    (hg : ∀ p ∈ primesUpToReal z, g p ≤ 2 / p) :
    (∑ p ∈ primesUpToReal z, g p * Real.log p) ≤ 4 * Real.log z ∧
      (∑ p ∈ primesUpToReal z, g p * (Real.log p) ^ 2) ≤ 4 * (Real.log z) ^ 2 := by
  have hL : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hfirst : (∑ p ∈ primesUpToReal z, g p * Real.log p) ≤ 4 * Real.log z := by
    calc
      _ ≤ ∑ p ∈ primesUpToReal z, (2 / p) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (hg p hp) (Real.log_natCast_nonneg p)
      _ = 2 * (∑ p ∈ primesUpToReal z, Real.log p / p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 2 * (Real.log z + (Real.log 4 + 4)) := by
        exact mul_le_mul_of_nonneg_left (prime_log_reciprocal_upper (by linarith)) (by norm_num)
      _ ≤ 4 * Real.log z := by linarith
  refine ⟨hfirst, ?_⟩
  calc
    _ ≤ ∑ p ∈ primesUpToReal z, Real.log z * (g p * Real.log p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpz : (p : ℝ) ≤ z := by
        have hp' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
        exact (Nat.cast_le.mpr hp').trans (Nat.floor_le (by linarith))
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (Finset.mem_filter.mp hp).2.pos
      have hlog := Real.log_le_log hp0 hpz
      have hnonneg := mul_nonneg (hg0 p hp) (Real.log_natCast_nonneg p)
      have h := mul_le_mul_of_nonneg_right hlog hnonneg
      nlinarith
    _ = Real.log z * (∑ p ∈ primesUpToReal z, g p * Real.log p) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log z * (4 * Real.log z) := mul_le_mul_of_nonneg_left hfirst hL
    _ = 4 * (Real.log z) ^ 2 := by ring

theorem bernoulli_prime_log_second_moment {z : ℝ} (hz : 2 ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ primesUpToReal z, 0 ≤ g p)
    (hg : ∀ p ∈ primesUpToReal z, g p ≤ 2 / p) :
    (∑ t ∈ (primesUpToReal z).powerset, bernoulliWeight (primesUpToReal z) t g *
      (∑ p ∈ t, Real.log p) ^ 2) ≤ 20 * (Real.log z) ^ 2 := by
  have h := prime_log_moments hz hlarge g hg0 hg
  have hfirst0 : 0 ≤ ∑ p ∈ primesUpToReal z, g p * Real.log p :=
    Finset.sum_nonneg fun p hp => mul_nonneg (hg0 p hp) (Real.log_natCast_nonneg p)
  have hsq : (∑ p ∈ primesUpToReal z, g p * Real.log p) ^ 2 ≤
      (4 * Real.log z) ^ 2 := by nlinarith [h.1]
  have hbound := bernoulli_second_moment_le (primesUpToReal z) g (fun p => Real.log p)
  nlinarith [h.2]

theorem prime_sieve_normalizer_tail {z R : ℝ} (hz : 2 ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (hR : 0 ≤ R) (g : ℕ → ℝ)
    (hg0 : ∀ p ∈ primesUpToReal z, 0 ≤ g p)
    (hg : ∀ p ∈ primesUpToReal z, g p ≤ 2 / p)
    (hg1 : ∀ p ∈ primesUpToReal z, g p < 1) :
    (1 - (∑ t ∈ (primesUpToReal z).powerset with (∑ p ∈ (t : Finset ℕ), Real.log p) ≤ R,
        ∏ p ∈ t, g p / (1 - g p)) * (∏ p ∈ primesUpToReal z, (1 - g p))) * R ^ 2 ≤
      20 * (Real.log z) ^ 2 := by
  classical
  rw [truncated_sieve_normalization (primesUpToReal z) g _
    (fun p hp => ne_of_lt (hg1 p hp))]
  exact (bernoulli_truncation_bound (primesUpToReal z) g
    (fun t => ∑ p ∈ t, Real.log p) R hR hg0 (fun p hp => (hg1 p hp).le)).trans
      (bernoulli_prime_log_second_moment hz hlarge g hg0 hg)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_index_log_sum_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {z : ℝ} (hz : 1 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z) :
    (∑ p : P, Real.log (a p) / a p) ≤ Real.log z + (Real.log 4 + 4) := by
  have hsub : Finset.univ.image a ⊆ primesUpToReal z := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(hprime p).pos, Nat.le_floor (hle p)⟩, hprime p⟩
  calc
    _ = ∑ q ∈ Finset.univ.image a, Real.log q / q := by
      symm
      rw [Finset.sum_image]
      intro p hp q hq h
      exact hinj h
    _ ≤ ∑ q ∈ primesUpToReal z, Real.log q / q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => div_nonneg (Real.log_natCast_nonneg q) (Nat.cast_nonneg q))
    _ ≤ _ := prime_log_reciprocal_upper hz

theorem prime_index_log_moments {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {z : ℝ} (hz : 2 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z)
    (hlarge : Real.log 4 + 4 ≤ Real.log z) (g : P → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg : ∀ p, g p ≤ 2 / a p) :
    (∑ p : P, g p * Real.log (a p)) ^ 2 +
      (∑ p : P, g p * (Real.log (a p)) ^ 2) ≤ 20 * (Real.log z) ^ 2 := by
  have hL : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hfirst : (∑ p : P, g p * Real.log (a p)) ≤ 4 * Real.log z := by
    calc
      _ ≤ ∑ p : P, (2 / a p) * Real.log (a p) :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right (hg p)
          (Real.log_natCast_nonneg (a p)))
      _ = 2 * (∑ p : P, Real.log (a p) / a p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 2 * (Real.log z + (Real.log 4 + 4)) :=
        mul_le_mul_of_nonneg_left (prime_index_log_sum_le a hinj hprime (by linarith) hle) (by norm_num)
      _ ≤ 4 * Real.log z := by linarith
  have hfirst0 : 0 ≤ ∑ p : P, g p * Real.log (a p) :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (hg0 p) (Real.log_natCast_nonneg (a p)))
  have hsecond : (∑ p : P, g p * (Real.log (a p)) ^ 2) ≤ 4 * (Real.log z) ^ 2 := by
    calc
      _ ≤ ∑ p : P, Real.log z * (g p * Real.log (a p)) := by
        apply Finset.sum_le_sum
        intro p _
        have hlog := Real.log_le_log (by exact_mod_cast (hprime p).pos) (hle p)
        have hnonneg := mul_nonneg (hg0 p) (Real.log_natCast_nonneg (a p))
        have h := mul_le_mul_of_nonneg_right hlog hnonneg
        nlinarith
      _ = Real.log z * (∑ p : P, g p * Real.log (a p)) := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.log z * (4 * Real.log z) := mul_le_mul_of_nonneg_left hfirst hL
      _ = 4 * (Real.log z) ^ 2 := by ring
  have hsq : (∑ p : P, g p * Real.log (a p)) ^ 2 ≤ (4 * Real.log z) ^ 2 := by
    nlinarith
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def eventProduct {P N : Type*} (E : P → N → Prop)
    (t : Finset P) (n : N) : ℝ := by
  classical
  exact if ∀ p ∈ t, E p n then 1 else 0

theorem eventProduct_union {P N : Type*} [DecidableEq P]
    (E : P → N → Prop) (t u : Finset P) (n : N) :
    eventProduct E (t ∪ u) n = eventProduct E t n * eventProduct E u n := by
  classical
  simp only [eventProduct, Finset.forall_mem_union]
  split_ifs <;> simp_all

noncomputable def sieveSquareRoot {P N : Type*}
    (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop) (n : N) : ℝ :=
  ∑ t ∈ T, weights t * eventProduct E t n

theorem sieveSquareRoot_of_avoids {P N : Type*} [DecidableEq P]
    (s : Finset P) (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1)
    (n : N) (hn : ∀ p ∈ s, ¬ E p n) :
    sieveSquareRoot T weights E n = 1 := by
  classical
  unfold sieveSquareRoot
  rw [Finset.sum_eq_single ∅]
  · simp [eventProduct, hweights]
  · intro t ht htne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr htne
    have hfalse : ¬ ∀ q ∈ t, E q n := fun h => hn p (hT t ht hp) (h p hp)
    simp [eventProduct, hfalse]
  · exact fun h => (h hEmpty).elim

theorem avoidance_le_sieveSquare {P N : Type*} [DecidableEq P]
    (s : Finset P) (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1) (n : N) :
    eventProduct (fun p n => ¬ E p n) s n ≤ (sieveSquareRoot T weights E n) ^ 2 := by
  classical
  unfold eventProduct
  split_ifs with hn
  · rw [sieveSquareRoot_of_avoids s T weights E hT hEmpty hweights n hn]
    norm_num
  · exact sq_nonneg _

theorem sieveSquare_expansion {P N : Type*} [DecidableEq P]
    (T : Finset (Finset P)) (weights : Finset P → ℝ) (E : P → N → Prop) (n : N) :
    (sieveSquareRoot T weights E n) ^ 2 =
      ∑ t ∈ T, ∑ u ∈ T, weights t * weights u * eventProduct E (t ∪ u) n := by
  unfold sieveSquareRoot
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [eventProduct_union]
  ring

theorem avoidance_sum_le_sieveSquare {P N : Type*} [DecidableEq P]
    (I : Finset N) (s : Finset P) (T : Finset (Finset P))
    (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) s n) ≤
      ∑ t ∈ T, ∑ u ∈ T, weights t * weights u * (∑ n ∈ I, eventProduct E (t ∪ u) n) := by
  classical
  calc
    _ ≤ ∑ n ∈ I, (sieveSquareRoot T weights E n) ^ 2 :=
      Finset.sum_le_sum fun n _ => avoidance_le_sieveSquare s T weights E hT hEmpty hweights n
    _ = _ := by
      simp_rw [sieveSquare_expansion]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      exact (Finset.mul_sum _ _ _).symm

theorem selberg_square_upper_bound {P N : Type*} [DecidableEq P]
    (I : Finset N) (s : Finset P) (T : Finset (Finset P))
    (weights : Finset P → ℝ) (E : P → N → Prop)
    (hT : ∀ t ∈ T, t ⊆ s) (hEmpty : ∅ ∈ T) (hweights : weights ∅ = 1)
    (mass : ℝ) (density : Finset P → ℝ) (error : Finset P → Finset P → ℝ)
    (happrox : ∀ t ∈ T, ∀ u ∈ T,
      |(∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)| ≤ error t u) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) s n) ≤
      mass * (∑ t ∈ T, ∑ u ∈ T, weights t * weights u * density (t ∪ u)) +
        ∑ t ∈ T, ∑ u ∈ T, |weights t * weights u| * error t u := by
  classical
  have hterm (t : Finset P) (ht : t ∈ T) (u : Finset P) (hu : u ∈ T) :
      weights t * weights u * (∑ n ∈ I, eventProduct E (t ∪ u) n) ≤
        mass * (weights t * weights u * density (t ∪ u)) +
          |weights t * weights u| * error t u := by
    have hscaled := mul_le_mul_of_nonneg_left (happrox t ht u hu)
      (abs_nonneg (weights t * weights u))
    have habs : weights t * weights u *
        ((∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)) ≤
        |weights t * weights u| *
          |(∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)| := by
      simpa only [abs_mul] using le_abs_self (weights t * weights u *
        ((∑ n ∈ I, eventProduct E (t ∪ u) n) - mass * density (t ∪ u)))
    nlinarith
  calc
    _ ≤ ∑ t ∈ T, ∑ u ∈ T,
        weights t * weights u * (∑ n ∈ I, eventProduct E (t ∪ u) n) :=
      avoidance_sum_le_sieveSquare I s T weights E hT hEmpty hweights
    _ ≤ ∑ t ∈ T, ∑ u ∈ T,
        (mass * (weights t * weights u * density (t ∪ u)) +
          |weights t * weights u| * error t u) := by
      exact Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun u hu => hterm t ht u hu
    _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bernoulli_product_split {P : Type*} [DecidableEq P]
    (s t : Finset P) (a b : P → ℝ) (ht : t ⊆ s) :
    (∏ p ∈ s, if p ∈ t then a p else b p) =
      (∏ p ∈ t, a p) * ∏ p ∈ s \ t, b p := by
  let f (p : P) := if p ∈ t then a p else b p
  have hleft : (∏ p ∈ s \ t, f p) = ∏ p ∈ s \ t, b p := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [f, (Finset.mem_sdiff.mp hp).2]
  have hright : (∏ p ∈ t, f p) = ∏ p ∈ t, a p := by
    apply Finset.prod_congr rfl
    intro p hp
    simp [f, hp]
  change (∏ p ∈ s, f p) = _
  rw [← Finset.prod_sdiff ht, hleft, hright]
  ring

theorem bernoulli_product_expectation {P : Type*} [DecidableEq P]
    (s : Finset P) (g a b : P → ℝ) :
    (∑ t ∈ s.powerset, bernoulliWeight s t g *
      (∏ p ∈ s, if p ∈ t then a p else b p)) =
      ∏ p ∈ s, (g p * a p + (1 - g p) * b p) := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t ht
  rw [bernoulli_product_split s t a b (Finset.mem_powerset.mp ht)]
  simp only [bernoulliWeight, Finset.prod_mul_distrib]
  ring

noncomputable def bernoulliBasis {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r t : Finset P) : ℝ :=
  ∏ p : P, if p ∈ t then (if p ∈ r then 1 - 1 / g p else 1) else 1

theorem bernoulliBasis_empty {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r : Finset P) : bernoulliBasis g r ∅ = 1 := by
  simp [bernoulliBasis]

theorem bernoulliBasis_product_expectation {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r u : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g * bernoulliBasis g r t *
      bernoulliBasis g u t) =
      ∏ p : P, (g p * ((if p ∈ r then 1 - 1 / g p else 1) *
        (if p ∈ u then 1 - 1 / g p else 1)) + (1 - g p)) := by
  have hprod (t : Finset P) : bernoulliBasis g r t * bernoulliBasis g u t =
      ∏ p : P, if p ∈ t then ((if p ∈ r then 1 - 1 / g p else 1) *
        (if p ∈ u then 1 - 1 / g p else 1)) else 1 := by
    unfold bernoulliBasis
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p ∈ t <;> simp [hp]
  calc
    _ = ∑ t : Finset P, bernoulliWeight Finset.univ t g *
        (∏ p : P, if p ∈ t then ((if p ∈ r then 1 - 1 / g p else 1) *
          (if p ∈ u then 1 - 1 / g p else 1)) else 1) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← hprod]
      ring
    _ = _ := by
      simpa only [Finset.powerset_univ, mul_one] using
        bernoulli_product_expectation Finset.univ g
          (fun p => (if p ∈ r then 1 - 1 / g p else 1) *
            (if p ∈ u then 1 - 1 / g p else 1)) (fun _ => 1)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bernoulliBasis_orthogonal {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (hg : ∀ p, g p ≠ 0) (r u : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g * bernoulliBasis g r t *
      bernoulliBasis g u t) =
      if r = u then ∏ p ∈ r, (1 - g p) / g p else 0 := by
  rw [bernoulliBasis_product_expectation]
  by_cases hru : r = u
  · subst u
    simp only [ite_true]
    calc
      _ = ∏ p : P, if p ∈ r then (1 - g p) / g p else 1 := by
        apply Finset.prod_congr rfl
        intro p _
        by_cases hp : p ∈ r
        · simp only [hp, ite_true]
          field_simp [hg p]
          ring
        · simp [hp]
      _ = _ := Finset.prod_ite_mem_eq r (fun p => (1 - g p) / g p)
  · simp only [hru, ite_false]
    obtain ⟨p, hp⟩ : ∃ p, (p ∈ r ∧ p ∉ u) ∨ (p ∉ r ∧ p ∈ u) := by
      by_contra! h
      apply hru
      ext p
      have hmem := h p
      tauto
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    rcases hp with ⟨hr, hu⟩ | ⟨hr, hu⟩
    · simp only [hr, hu, ite_true, ite_false, mul_one]
      field_simp [hg p]
      ring
    · simp only [hr, hu, ite_true, ite_false, one_mul]
      field_simp [hg p]
      ring

theorem weighted_square_expansion {A B : Type*}
    (S : Finset A) (T : Finset B) (weight : B → ℝ) (basis : A → B → ℝ)
    (coefficient : A → ℝ) :
    (∑ t ∈ T, weight t * (∑ a ∈ S, coefficient a * basis a t) ^ 2) =
      ∑ a ∈ S, ∑ b ∈ S, coefficient a * coefficient b *
        (∑ t ∈ T, weight t * basis a t * basis b t) := by
  calc
    _ = ∑ t ∈ T, ∑ a ∈ S, ∑ b ∈ S,
        coefficient a * coefficient b * (weight t * basis a t * basis b t) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [pow_two, Finset.mul_sum]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a ∈ S, ∑ b ∈ S, coefficient a * coefficient b *
        (∑ t ∈ T, weight t * basis a t * basis b t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact (Finset.mul_sum _ _ _).symm

theorem weighted_orthogonal_square {A B : Type*} [DecidableEq A]
    (S : Finset A) (T : Finset B) (weight : B → ℝ) (basis : A → B → ℝ)
    (coefficient norm : A → ℝ)
    (horth : ∀ a ∈ S, ∀ b ∈ S,
      (∑ t ∈ T, weight t * basis a t * basis b t) = if a = b then norm a else 0) :
    (∑ t ∈ T, weight t * (∑ a ∈ S, coefficient a * basis a t) ^ 2) =
      ∑ a ∈ S, (coefficient a) ^ 2 * norm a := by
  rw [weighted_square_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single a]
  · rw [horth a ha a ha]
    simp [pow_two]
  · intro b hb hba
    rw [horth a ha b hb]
    simp [Ne.symm hba]
  · exact fun h => (h ha).elim

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def selbergQ {P : Type*} (g : P → ℝ) (r : Finset P) : ℝ :=
  ∏ p ∈ r, g p / (1 - g p)

noncomputable def selbergNormalizer {P : Type*}
    (T : Finset (Finset P)) (g : P → ℝ) : ℝ := ∑ r ∈ T, selbergQ g r

noncomputable def selbergMixture {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ) (t : Finset P) : ℝ :=
  ∑ r ∈ T, (selbergQ g r / selbergNormalizer T g) * bernoulliBasis g r t

theorem selbergQ_nonneg {P : Type*} (g : P → ℝ) (r : Finset P)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) : 0 ≤ selbergQ g r := by
  exact Finset.prod_nonneg (fun p _ => div_nonneg (hg0 p) (sub_nonneg.mpr (hg1 p)))

theorem selbergNormalizer_pos {P : Type*} [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ) (hEmpty : ∅ ∈ T)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    0 < selbergNormalizer T g := by
  have h := Finset.single_le_sum (fun r (_ : r ∈ T) => selbergQ_nonneg g r hg0 hg1) hEmpty
  have hone : (1 : ℝ) ≤ selbergNormalizer T g := by
    simpa only [selbergQ, Finset.prod_empty, selbergNormalizer] using h
  linarith

theorem selbergQ_mul_norm {P : Type*} (g : P → ℝ)
    (hg0 : ∀ p, g p ≠ 0) (hg1 : ∀ p, g p ≠ 1) (r : Finset P) :
    selbergQ g r * (∏ p ∈ r, (1 - g p) / g p) = 1 := by
  unfold selbergQ
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p _
  field_simp [hg0 p, sub_ne_zero.mpr (Ne.symm (hg1 p))]

theorem selbergMixture_empty {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ) (hG : selbergNormalizer T g ≠ 0) :
    selbergMixture T g ∅ = 1 := by
  simp only [selbergMixture, bernoulliBasis_empty, mul_one, ← Finset.sum_div]
  exact div_self hG

theorem selbergMixture_second_moment {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ)
    (hg0 : ∀ p, g p ≠ 0) (hg1 : ∀ p, g p ≠ 1)
    (hG : selbergNormalizer T g ≠ 0) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g * (selbergMixture T g t) ^ 2) =
      1 / selbergNormalizer T g := by
  unfold selbergMixture
  rw [weighted_orthogonal_square T Finset.univ
    (fun t => bernoulliWeight Finset.univ t g) (bernoulliBasis g)
    (fun r => selbergQ g r / selbergNormalizer T g)
    (fun r => ∏ p ∈ r, (1 - g p) / g p)
    (fun r _ u _ => bernoulliBasis_orthogonal g hg0 r u)]
  calc
    _ = ∑ r ∈ T, selbergQ g r / (selbergNormalizer T g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      have hnorm := selbergQ_mul_norm g hg0 hg1 r
      field_simp
      nlinarith [congrArg (fun x => selbergQ g r * x) hnorm]
    _ = 1 / selbergNormalizer T g := by
      rw [← Finset.sum_div]
      change selbergNormalizer T g / (selbergNormalizer T g) ^ 2 = _
      field_simp

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def eventBasis {P N : Type*} (g : P → ℝ) (r : Finset P)
    (E : P → N → Prop) (n : N) : ℝ := by
  classical
  exact ∏ p ∈ r, (1 - (if E p n then 1 else 0) / g p)

noncomputable def basisCoefficient {P : Type*} (g : P → ℝ) (d : Finset P) : ℝ :=
  ∏ p ∈ d, (-1 / g p)

theorem eventBasis_expansion {P N : Type*} [DecidableEq P]
    (g : P → ℝ) (r : Finset P) (E : P → N → Prop) (n : N) :
    eventBasis g r E n = ∑ d ∈ r.powerset, basisCoefficient g d * eventProduct E d n := by
  classical
  unfold eventBasis
  have hfactor (p : P) : 1 - (if E p n then 1 else 0) / g p =
      (-1 / g p) * (if E p n then 1 else 0) + 1 := by ring
  simp_rw [hfactor]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib]
  rw [Finset.prod_boole]
  rfl

theorem eventBasis_pattern {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (r t : Finset P) :
    eventBasis g r (fun p u => p ∈ u) t = bernoulliBasis g r t := by
  classical
  have hext : bernoulliBasis g r t =
      ∏ p : P, if p ∈ r then (if p ∈ t then 1 - 1 / g p else 1) else 1 := by
    unfold bernoulliBasis
    apply Finset.prod_congr rfl
    intro p _
    by_cases hr : p ∈ r <;> by_cases ht : p ∈ t <;> simp [hr, ht]
  rw [hext, Finset.prod_ite_mem_eq]
  unfold eventBasis
  apply Finset.prod_congr rfl
  intro p _
  by_cases ht : p ∈ t <;> simp [ht]

theorem basisCoefficient_abs_sum {P : Type*} [DecidableEq P]
    (g : P → ℝ) (r : Finset P) :
    (∑ d ∈ r.powerset, |basisCoefficient g d|) = ∏ p ∈ r, (1 + |1 / g p|) := by
  have h := Finset.prod_add (fun p => |(-1 : ℝ) / g p|) (fun _ => (1 : ℝ)) r
  simpa only [basisCoefficient, Finset.abs_prod, Finset.prod_const_one, mul_one,
    abs_div, abs_neg, abs_one, add_comm] using h.symm

theorem basisCoefficient_abs_sum_le {P : Type*} [DecidableEq P]
    (g size : P → ℝ) (r : Finset P)
    (hsize : ∀ p ∈ r, 2 ≤ size p) (hrecip : ∀ p ∈ r, |1 / g p| ≤ size p) :
    (∑ d ∈ r.powerset, |basisCoefficient g d|) ≤ (∏ p ∈ r, size p) ^ 2 := by
  rw [basisCoefficient_abs_sum, ← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hs := hsize p hp
    have hg := hrecip p hp
    nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bernoulli_event_mean {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (d : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g *
      eventProduct (fun p u => p ∈ u) d t) = ∏ p ∈ d, g p := by
  classical
  have hproduct (t : Finset P) :
      (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) =
      eventProduct (fun p u => p ∈ u) d t := by
    by_cases hd : d ⊆ t
    · have hleft : (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) = 1 := by
        apply Finset.prod_eq_one
        intro p _
        by_cases hp : p ∈ t
        · simp [hp]
        · have hpd : p ∉ d := fun h => hp (hd h)
          simp [hp, hpd]
      rw [hleft]
      have hall : ∀ p ∈ d, p ∈ t := hd
      simpa [eventProduct] using hall
    · obtain ⟨p, hpd, hpt⟩ := Finset.not_subset.mp hd
      have hleft : (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ p)
        simp [hpt, hpd]
      rw [hleft]
      have hnot : ¬ ∀ p ∈ d, p ∈ t := fun h => hpt (h p hpd)
      simp [eventProduct, hnot]
  calc
    _ = ∑ t : Finset P, bernoulliWeight Finset.univ t g *
        (∏ p : P, if p ∈ t then (1 : ℝ) else (if p ∈ d then 0 else 1)) := by
      simp_rw [hproduct]
    _ = ∏ p : P, (g p * 1 + (1 - g p) * (if p ∈ d then 0 else 1)) := by
      simpa only [Finset.powerset_univ] using
        bernoulli_product_expectation Finset.univ g (fun _ => 1) (fun p => if p ∈ d then 0 else 1)
    _ = ∏ p ∈ d, g p := by
      conv_rhs => rw [← Finset.prod_ite_mem_eq]
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p ∈ d <;> simp [hp]

theorem eventBasis_inner_expansion {P N : Type*} [DecidableEq P]
    (I : Finset N) (g : P → ℝ) (r u : Finset P) (E : P → N → Prop) (w : N → ℝ) :
    (∑ n ∈ I, w n * eventBasis g r E n * eventBasis g u E n) =
      ∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
        basisCoefficient g d * basisCoefficient g e *
          (∑ n ∈ I, w n * eventProduct E (d ∪ e) n) := by
  calc
    _ = ∑ n ∈ I, ∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
        basisCoefficient g d * basisCoefficient g e *
          (w n * eventProduct E (d ∪ e) n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [eventBasis_expansion, eventBasis_expansion, Finset.mul_sum]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      rw [eventProduct_union]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      exact (Finset.mul_sum _ _ _).symm

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem double_sum_error_bound {A B : Type*} (S : Finset A) (T : Finset B)
    (a : A → ℝ) (b : B → ℝ) (C D : A → B → ℝ) (K : ℝ)
    (h : ∀ i ∈ S, ∀ j ∈ T, |C i j - D i j| ≤ K) :
    |(∑ i ∈ S, ∑ j ∈ T, a i * b j * C i j) -
      (∑ i ∈ S, ∑ j ∈ T, a i * b j * D i j)| ≤
      (∑ i ∈ S, |a i|) * (∑ j ∈ T, |b j|) * K := by
  have heq : (∑ i ∈ S, ∑ j ∈ T, a i * b j * C i j) -
      (∑ i ∈ S, ∑ j ∈ T, a i * b j * D i j) =
      ∑ i ∈ S, ∑ j ∈ T, a i * b j * (C i j - D i j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, |∑ j ∈ T, a i * b j * (C i j - D i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, |a i * b j * (C i j - D i j)| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, |a i| * |b j| * K := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (h i hi j hj) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]

theorem eventBasis_inner_error {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (g : P → ℝ) (hg : ∀ p, g p ≠ 0)
    (r u : Finset P) (E : P → N → Prop) (M K : ℝ)
    (happrox : ∀ d ∈ r.powerset, ∀ e ∈ u.powerset,
      |(∑ n ∈ I, eventProduct E (d ∪ e) n) - M * (∏ p ∈ d ∪ e, g p)| ≤ K) :
    |(∑ n ∈ I, eventBasis g r E n * eventBasis g u E n) -
      M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)| ≤
      (∑ d ∈ r.powerset, |basisCoefficient g d|) *
        (∑ e ∈ u.powerset, |basisCoefficient g e|) * K := by
  have hmodel := eventBasis_inner_expansion Finset.univ g r u
    (fun p t => p ∈ t) (fun t => bernoulliWeight Finset.univ t g)
  simp only [eventBasis_pattern] at hmodel
  rw [bernoulliBasis_orthogonal g hg r u] at hmodel
  simp_rw [bernoulli_event_mean] at hmodel
  have hactual := eventBasis_inner_expansion I g r u E (fun _ => 1)
  simp only [one_mul] at hactual
  rw [hactual, hmodel]
  have hscale : M * (∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
      basisCoefficient g d * basisCoefficient g e * (∏ p ∈ d ∪ e, g p)) =
      ∑ d ∈ r.powerset, ∑ e ∈ u.powerset,
        basisCoefficient g d * basisCoefficient g e * (M * ∏ p ∈ d ∪ e, g p) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hscale]
  exact double_sum_error_bound r.powerset u.powerset (basisCoefficient g) (basisCoefficient g)
    (fun d e => ∑ n ∈ I, eventProduct E (d ∪ e) n)
    (fun d e => M * ∏ p ∈ d ∪ e, g p) K happrox

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def eventMixture {P N : Type*}
    (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop) (n : N) : ℝ :=
  ∑ r ∈ T, (selbergQ g r / selbergNormalizer T g) * eventBasis g r E n

theorem selberg_coefficient_sum {P : Type*} (T : Finset (Finset P)) (g : P → ℝ)
    (hG : selbergNormalizer T g ≠ 0) :
    (∑ r ∈ T, selbergQ g r / selbergNormalizer T g) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hG

theorem eventMixture_of_avoids {P N : Type*}
    (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop) (n : N)
    (hG : selbergNormalizer T g ≠ 0) (hn : ∀ p, ¬ E p n) : eventMixture T g E n = 1 := by
  have hb (r : Finset P) : eventBasis g r E n = 1 := by
    simp [eventBasis, hn]
  simp only [eventMixture, hb, mul_one]
  exact selberg_coefficient_sum T g hG

theorem selberg_model_quadratic {P : Type*} [Fintype P] [DecidableEq P]
    (T : Finset (Finset P)) (g : P → ℝ)
    (hg0 : ∀ p, g p ≠ 0) (hg1 : ∀ p, g p ≠ 1) (hG : selbergNormalizer T g ≠ 0) :
    (∑ r ∈ T, ∑ u ∈ T, (selbergQ g r / selbergNormalizer T g) *
      (selbergQ g u / selbergNormalizer T g) *
        (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)) = 1 / selbergNormalizer T g := by
  have h := weighted_square_expansion T Finset.univ
    (fun t => bernoulliWeight Finset.univ t g) (bernoulliBasis g)
    (fun r => selbergQ g r / selbergNormalizer T g)
  simp_rw [bernoulliBasis_orthogonal g hg0] at h
  exact h.symm.trans (selbergMixture_second_moment T g hg0 hg1 hG)

theorem eventMixture_second_moment_upper {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop)
    (hEmpty : ∅ ∈ T) (hg0 : ∀ p, 0 < g p) (hg1 : ∀ p, g p < 1) (M D : ℝ)
    (happrox : ∀ r ∈ T, ∀ u ∈ T,
      |(∑ n ∈ I, eventBasis g r E n * eventBasis g u E n) -
        M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)| ≤ D) :
    (∑ n ∈ I, (eventMixture T g E n) ^ 2) ≤ M / selbergNormalizer T g + D := by
  have hG : 0 < selbergNormalizer T g := selbergNormalizer_pos T g hEmpty
    (fun p => (hg0 p).le) (fun p => (hg1 p).le)
  let c (r : Finset P) := selbergQ g r / selbergNormalizer T g
  have hc (r : Finset P) : 0 ≤ c r :=
    div_nonneg (selbergQ_nonneg g r (fun p => (hg0 p).le) (fun p => (hg1 p).le)) hG.le
  have hcsum : (∑ r ∈ T, |c r|) = 1 := by
    simp_rw [abs_of_nonneg (hc _)]
    exact selberg_coefficient_sum T g (ne_of_gt hG)
  have herror := double_sum_error_bound T T c c
    (fun r u => ∑ n ∈ I, eventBasis g r E n * eventBasis g u E n)
    (fun r u => M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)) D happrox
  rw [hcsum, one_mul, one_mul] at herror
  have hmodel : (∑ r ∈ T, ∑ u ∈ T, c r * c u *
      (M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0))) =
        M / selbergNormalizer T g := by
    calc
      _ = M * (∑ r ∈ T, ∑ u ∈ T, c r * c u *
          (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by
        rw [selberg_model_quadratic T g (fun p => ne_of_gt (hg0 p))
          (fun p => ne_of_lt (hg1 p)) (ne_of_gt hG)]
        ring
  rw [hmodel] at herror
  have hactual := weighted_square_expansion T I (fun _ => 1)
    (fun r n => eventBasis g r E n) c
  simp only [one_mul] at hactual
  change (∑ n ∈ I, (∑ r ∈ T, c r * eventBasis g r E n) ^ 2) ≤ _
  rw [hactual]
  linarith [(abs_le.mp herror).2]

theorem selberg_avoidance_upper_from_inner {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop)
    (hEmpty : ∅ ∈ T) (hg0 : ∀ p, 0 < g p) (hg1 : ∀ p, g p < 1) (M D : ℝ)
    (happrox : ∀ r ∈ T, ∀ u ∈ T,
      |(∑ n ∈ I, eventBasis g r E n * eventBasis g u E n) -
        M * (if r = u then ∏ p ∈ r, (1 - g p) / g p else 0)| ≤ D) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) Finset.univ n) ≤
      M / selbergNormalizer T g + D := by
  classical
  have hG := selbergNormalizer_pos T g hEmpty (fun p => (hg0 p).le) (fun p => (hg1 p).le)
  calc
    _ ≤ ∑ n ∈ I, (eventMixture T g E n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      unfold eventProduct
      split_ifs with hn
      · have hn' : ∀ p, ¬ E p n := fun p => hn p (Finset.mem_univ p)
        rw [eventMixture_of_avoids T g E n (ne_of_gt hG) hn']
        norm_num
      · exact sq_nonneg _
    _ ≤ _ := eventMixture_second_moment_upper I T g E hEmpty hg0 hg1 M D happrox

theorem selberg_avoidance_upper_from_counts {P N : Type*} [Fintype P] [DecidableEq P]
    (I : Finset N) (T : Finset (Finset P)) (g : P → ℝ) (E : P → N → Prop)
    (hEmpty : ∅ ∈ T) (hg0 : ∀ p, 0 < g p) (hg1 : ∀ p, g p < 1)
    (M K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hcoefficient : ∀ r ∈ T, (∑ d ∈ r.powerset, |basisCoefficient g d|) ≤ L)
    (hcounts : ∀ r ∈ T, ∀ u ∈ T, ∀ d ∈ r.powerset, ∀ e ∈ u.powerset,
      |(∑ n ∈ I, eventProduct E (d ∪ e) n) - M * (∏ p ∈ d ∪ e, g p)| ≤ K) :
    (∑ n ∈ I, eventProduct (fun p n => ¬ E p n) Finset.univ n) ≤
      M / selbergNormalizer T g + L ^ 2 * K := by
  apply selberg_avoidance_upper_from_inner I T g E hEmpty hg0 hg1 M (L ^ 2 * K)
  intro r hr u hu
  have h := eventBasis_inner_error I g (fun p => ne_of_gt (hg0 p)) r u E M K
    (hcounts r hr u hu)
  have hprod := mul_le_mul (hcoefficient r hr) (hcoefficient u hu)
    (Finset.sum_nonneg (fun d _ => abs_nonneg (basisCoefficient g d))) hL
  have hscaled := mul_le_mul_of_nonneg_right hprod hK
  exact h.trans (by simpa only [pow_two] using hscaled)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem nat_prod_union_le {P : Type*} [DecidableEq P]
    (a : P → ℕ) (ha : ∀ p, 1 ≤ a p) (r u : Finset P) :
    (∏ p ∈ r ∪ u, a p) ≤ (∏ p ∈ r, a p) * (∏ p ∈ u, a p) := by
  have h := Finset.prod_union_inter (f := a) (s₁ := r) (s₂ := u)
  have hinter : 1 ≤ ∏ p ∈ r ∩ u, a p := Finset.one_le_prod (fun p _ => ha p)
  simpa only [mul_one] using
    (Nat.mul_le_mul_left (∏ p ∈ r ∪ u, a p) hinter).trans_eq h

theorem nat_prod_subsets_union_le {P : Type*} [DecidableEq P]
    (a : P → ℕ) (ha : ∀ p, 1 ≤ a p) (r u d e : Finset P) (R : ℕ)
    (hd : d ⊆ r) (he : e ⊆ u)
    (hr : (∏ p ∈ r, a p) ≤ R) (hu : (∏ p ∈ u, a p) ≤ R) :
    (∏ p ∈ d ∪ e, a p) ≤ R ^ 2 := by
  have hdprod : (∏ p ∈ d, a p) ≤ ∏ p ∈ r, a p :=
    Finset.prod_le_prod_of_subset_of_one_le' hd (fun p _ _ => ha p)
  have heprod : (∏ p ∈ e, a p) ≤ ∏ p ∈ u, a p :=
    Finset.prod_le_prod_of_subset_of_one_le' he (fun p _ _ => ha p)
  have hunion := nat_prod_union_le a ha d e
  have hmul := Nat.mul_le_mul (hdprod.trans hr) (heprod.trans hu)
  simpa only [pow_two] using hunion.trans hmul

theorem prime_size_coefficient_bound {P : Type*} [DecidableEq P]
    (a : P → ℕ) (g : P → ℝ) (r : Finset P) (R : ℕ)
    (ha : ∀ p, 2 ≤ a p) (hg : ∀ p, |1 / g p| ≤ a p)
    (hr : (∏ p ∈ r, a p) ≤ R) :
    (∑ d ∈ r.powerset, |basisCoefficient g d|) ≤ (R : ℝ) ^ 2 := by
  have h := basisCoefficient_abs_sum_le g (fun p => (a p : ℝ)) r
    (fun p _ => by exact_mod_cast ha p) (fun p _ => hg p)
  have hprod : (∏ p ∈ r, (a p : ℝ)) ≤ R := by exact_mod_cast hr
  have hprod0 : 0 ≤ ∏ p ∈ r, (a p : ℝ) := Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _)
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def residueDensity {P : Type*} (a : P → ℕ)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2))) (p : P) : ℝ :=
  (A p).card / (a p : ℝ) ^ 2

def residueEvent {P : Type*} (a : P → ℕ)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2))) (S : ℕ) (p : P) (n : ℕ) : Prop :=
  ((S + n : ℕ) : ZMod ((a p) ^ 2)) ∈ A p

theorem residueDensity_bounds {P : Type*} (a : P → ℕ)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2))) (p : P)
    (ha : 0 < a p) (hmin : a p ≤ (A p).card) (hmax : (A p).card < (a p) ^ 2) :
    0 < residueDensity a A p ∧ residueDensity a A p < 1 ∧
      |1 / residueDensity a A p| ≤ a p := by
  have ha' : (0 : ℝ) < a p := by exact_mod_cast ha
  have hc : (0 : ℝ) < (A p).card := by exact_mod_cast lt_of_lt_of_le ha hmin
  have hmin' : (a p : ℝ) ≤ (A p).card := by exact_mod_cast hmin
  have hmax' : ((A p).card : ℝ) < (a p : ℝ) ^ 2 := by exact_mod_cast hmax
  have hsq := sq_pos_of_pos ha'
  refine ⟨div_pos hc hsq, (div_lt_one hsq).mpr hmax', ?_⟩
  unfold residueDensity
  rw [one_div, inv_div, abs_of_nonneg (div_nonneg (sq_nonneg _) hc.le)]
  apply (div_le_iff₀ hc).mpr
  nlinarith

theorem residueEvent_count_error {P : Type*} [DecidableEq P]
    (a : P → ℕ) (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (ha : ∀ p, 0 < a p) (hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)))
    (d : Finset P) (S N : ℕ) :
    |(∑ n ∈ Finset.range N, eventProduct (residueEvent a A S) d n) -
      (N : ℝ) * (∏ p ∈ d, residueDensity a A p)| ≤ ∏ p ∈ d, ((A p).card : ℝ) := by
  classical
  let m (p : d) := (a p) ^ 2
  let B (p : d) := A p
  have hm : ∀ p : d, 0 < m p := fun p => pow_pos (ha p) 2
  have hd : Pairwise (fun p q : d => (m p).Coprime (m q)) := by
    intro p q hpq
    exact hc (Subtype.coe_ne_coe.mpr hpq)
  have h := residueCondition_interval_error m B hm hd S N
  have hp (n : ℕ) : residueCondition m B (S + n) ↔
      ∀ p ∈ d, residueEvent a A S p n := by
    constructor
    · intro hn p hpd
      exact hn ⟨p, hpd⟩
    · intro hn p
      exact hn p p.property
  have hsum : (@Nat.count (fun n => residueCondition m B (S + n)) (Classical.decPred _) N : ℝ) =
      ∑ n ∈ Finset.range N, eventProduct (residueEvent a A S) d n := by
    rw [Nat.count_eq_card_filter_range]
    simp only [eventProduct, ← hp]
    simp
  rw [hsum] at h
  have hmod : ((∏ p : d, m p : ℕ) : ℝ) = ∏ p ∈ d, (a p : ℝ) ^ 2 := by
    simp only [m, Nat.cast_prod, Nat.cast_pow]
    exact Finset.prod_coe_sort d (fun p => (a p : ℝ) ^ 2)
  have hcard : ((∏ p : d, (B p).card : ℕ) : ℝ) = ∏ p ∈ d, ((A p).card : ℝ) := by
    simp only [B, Nat.cast_prod]
    exact Finset.prod_coe_sort d (fun p => ((A p).card : ℝ))
  rw [hmod, hcard] at h
  have hdensity : (∏ p ∈ d, residueDensity a A p) =
      (∏ p ∈ d, ((A p).card : ℝ)) / (∏ p ∈ d, (a p : ℝ) ^ 2) := by
    simp only [residueDensity, Finset.prod_div_distrib]
  rw [hdensity]
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using h

noncomputable def sieveSubsets {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (R : ℕ) : Finset (Finset P) :=
  Finset.univ.filter (fun r => (∏ p ∈ r, a p) ≤ R)


theorem square_residue_sieve_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (ha : ∀ p, 2 ≤ a p) (hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hmax : ∀ p, (A p).card < (a p) ^ 2)
    (R S N : ℕ) (hR : 1 ≤ R) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (N : ℝ) / selbergNormalizer (sieveSubsets a R) (residueDensity a A) + (R : ℝ) ^ 8 := by
  have hb (p : P) := residueDensity_bounds a A p (by have := ha p; omega) (hmin p) (hmax p)
  have hEmpty : ∅ ∈ sieveSubsets a R := by simp [sieveSubsets, hR]
  have hcoef : ∀ r ∈ sieveSubsets a R,
      (∑ d ∈ r.powerset, |basisCoefficient (residueDensity a A) d|) ≤ (R : ℝ) ^ 2 := by
    intro r hr
    exact prime_size_coefficient_bound a (residueDensity a A) r R ha (fun p => (hb p).2.2)
      (Finset.mem_filter.mp hr).2
  have hcounts : ∀ r ∈ sieveSubsets a R, ∀ u ∈ sieveSubsets a R,
      ∀ d ∈ r.powerset, ∀ e ∈ u.powerset,
      |(∑ n ∈ Finset.range N, eventProduct (residueEvent a A S) (d ∪ e) n) -
        (N : ℝ) * (∏ p ∈ d ∪ e, residueDensity a A p)| ≤ (R : ℝ) ^ 4 := by
    intro r hr u hu d hd e he
    have hprod := nat_prod_subsets_union_le a (fun p => by have := ha p; omega) r u d e R
      (Finset.mem_powerset.mp hd) (Finset.mem_powerset.mp he)
      (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hu).2
    have hcard : (∏ p ∈ d ∪ e, (A p).card) ≤ R ^ 4 := by
      calc
        _ ≤ ∏ p ∈ d ∪ e, (a p) ^ 2 :=
          Finset.prod_le_prod' (fun p _ => (hmax p).le)
        _ = (∏ p ∈ d ∪ e, a p) ^ 2 := Finset.prod_pow _ _ _
        _ ≤ (R ^ 2) ^ 2 := Nat.pow_le_pow_left hprod 2
        _ = R ^ 4 := by ring
    have hcard' : (∏ p ∈ d ∪ e, ((A p).card : ℝ)) ≤ (R : ℝ) ^ 4 := by exact_mod_cast hcard
    exact (residueEvent_count_error a A (fun p => by have := ha p; omega) hc (d ∪ e) S N).trans hcard'
  have h := selberg_avoidance_upper_from_counts (Finset.range N) (sieveSubsets a R)
    (residueDensity a A) (residueEvent a A S) hEmpty (fun p => (hb p).1)
    (fun p => (hb p).2.1) (N : ℝ) ((R : ℝ) ^ 4) ((R : ℝ) ^ 2)
    (by positivity) (sq_nonneg _) hcoef hcounts
  convert h using 1 <;> ring

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem reciprocal_bound_of_relative_loss {G V e : ℝ}
    (hG : 0 < G) (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hbound : 1 - e ≤ G * V) :
    1 / G ≤ (1 + 2 * e) * V := by
  apply (div_le_iff₀ hG).mpr
  have hprod := mul_le_mul_of_nonneg_left hbound (by linarith : 0 ≤ 1 + 2 * e)
  have hs : 0 ≤ e * (1 - 2 * e) := mul_nonneg he (by linarith)
  nlinarith


theorem inverse_normalizer_bound {G V R L : ℝ}
    (hG : 0 < G) (hR : 0 < R)
    (hsmall : 20 * L ^ 2 ≤ R ^ 2 / 2)
    (htail : (1 - G * V) * R ^ 2 ≤ 20 * L ^ 2) :
    1 / G ≤ (1 + 40 * (L / R) ^ 2) * V := by
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hratio : 20 * (L / R) ^ 2 = (20 * L ^ 2) / R ^ 2 := by ring
  have he0 : 0 ≤ 20 * (L / R) ^ 2 := by positivity
  have hehalf : 20 * (L / R) ^ 2 ≤ 1 / 2 := by
    rw [hratio]
    exact (div_le_iff₀ hR2).mpr (by linarith)
  have hbound : 1 - 20 * (L / R) ^ 2 ≤ G * V := by
    have hdiv := (le_div_iff₀ hR2).mpr htail
    rw [← hratio] at hdiv
    linarith
  have h := reciprocal_bound_of_relative_loss hG he0 hehalf hbound
  convert h using 1 <;> first | rfl | ring

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem log_nat_product {P : Type*} (a : P → ℕ) (ha : ∀ p, 0 < a p) (r : Finset P) :
    Real.log ((∏ p ∈ r, a p : ℕ) : ℝ) = ∑ p ∈ r, Real.log (a p) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p _ => by exact_mod_cast (ne_of_gt (ha p)))

theorem product_le_iff_sum_log_le {P : Type*} (a : P → ℕ) (ha : ∀ p, 0 < a p)
    (r : Finset P) {R : ℕ} (hR : 0 < R) :
    (∏ p ∈ r, a p) ≤ R ↔ (∑ p ∈ r, Real.log (a p)) ≤ Real.log R := by
  have hp : (0 : ℝ) < (∏ p ∈ r, a p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p _ => ha p)
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  rw [← log_nat_product a ha r, Real.log_le_log_iff hp hR', Nat.cast_le]

theorem selbergNormalizer_bernoulli_probability {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (R : ℕ) (g : P → ℝ) (hg : ∀ p, g p ≠ 1) :
    selbergNormalizer (sieveSubsets a R) g * (∏ p : P, (1 - g p)) =
      ∑ r ∈ sieveSubsets a R, bernoulliWeight Finset.univ r g := by
  have h := truncated_sieve_normalization (Finset.univ : Finset P) g
    (fun r => (∏ p ∈ r, a p) ≤ R) (fun p _ => hg p)
  simpa only [Finset.powerset_univ, selbergNormalizer, sieveSubsets, selbergQ] using h

theorem selbergNormalizer_log_tail {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (ha : ∀ p, 0 < a p) (R : ℕ) (hR : 1 ≤ R) (g : P → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p < 1) :
    (1 - selbergNormalizer (sieveSubsets a R) g * (∏ p : P, (1 - g p))) * (Real.log R) ^ 2 ≤
      (∑ p : P, g p * Real.log (a p)) ^ 2 + ∑ p : P, g p * (Real.log (a p)) ^ 2 := by
  classical
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  have htail := bernoulli_truncation_bound (Finset.univ : Finset P) g
    (fun r => ∑ p ∈ r, Real.log (a p)) (Real.log R) hlogR
    (fun p _ => hg0 p) (fun p _ => (hg1 p).le)
  have hfilter : ((Finset.univ : Finset P).powerset.filter
      (fun r => (∑ p ∈ r, Real.log (a p)) ≤ Real.log R)) = sieveSubsets a R := by
    ext r
    simp only [Finset.powerset_univ, sieveSubsets, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (product_le_iff_sum_log_le a ha r (by omega)).symm
  rw [hfilter, ← selbergNormalizer_bernoulli_probability a R g (fun p => ne_of_lt (hg1 p))] at htail
  exact htail.trans (bernoulli_second_moment_le Finset.univ g (fun p => Real.log (a p)))

theorem square_residue_sieve_moment_bound {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (ha : ∀ p, 2 ≤ a p) (hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hmax : ∀ p, (A p).card < (a p) ^ 2)
    (R S N : ℕ) (hR : 2 ≤ R) (L : ℝ)
    (hmoment : (∑ p : P, residueDensity a A p * Real.log (a p)) ^ 2 +
      (∑ p : P, residueDensity a A p * (Real.log (a p)) ^ 2) ≤ 20 * L ^ 2)
    (hsmall : 20 * L ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (1 + 40 * (L / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - residueDensity a A p)) + (R : ℝ) ^ 8 := by
  have hb (p : P) := residueDensity_bounds a A p (by have := ha p; omega) (hmin p) (hmax p)
  have hEmpty : ∅ ∈ sieveSubsets a R := by simp [sieveSubsets]; omega
  have hG := selbergNormalizer_pos (sieveSubsets a R) (residueDensity a A) hEmpty
    (fun p => (hb p).1.le) (fun p => (hb p).2.1.le)
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have htail := selbergNormalizer_log_tail a (fun p => by have := ha p; omega) R
    (by omega) (residueDensity a A) (fun p => (hb p).1.le) (fun p => (hb p).2.1)
  have hinverse := inverse_normalizer_bound hG hlogR hsmall (htail.trans hmoment)
  have hmain := mul_le_mul_of_nonneg_left hinverse (Nat.cast_nonneg N)
  have hsieve := square_residue_sieve_upper a A ha hc hmin hmax R S N (by omega)
  calc
    _ ≤ (N : ℝ) / selbergNormalizer (sieveSubsets a R) (residueDensity a A) + (R : ℝ) ^ 8 := hsieve
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      calc
        (N : ℝ) / selbergNormalizer (sieveSubsets a R) (residueDensity a A) =
            (N : ℝ) * (1 / selbergNormalizer (sieveSubsets a R) (residueDensity a A)) := by ring
        _ ≤ _ := hmain
        _ = _ := by ring

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_square_sieve_upper_strict {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hmax : ∀ p, (A p).card < (a p) ^ 2)
    (hcard : ∀ p, (A p).card ≤ 2 * a p)
    (R S N : ℕ) (hR : 2 ≤ R) (z : ℝ) (hz : 2 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - residueDensity a A p)) + (R : ℝ) ^ 8 := by
  have hb (p : P) := residueDensity_bounds a A p (hprime p).pos (hmin p) (hmax p)
  have hg (p : P) : residueDensity a A p ≤ 2 / a p := by
    have hap : (0 : ℝ) < a p := by exact_mod_cast (hprime p).pos
    have hcard' : ((A p).card : ℝ) ≤ 2 * a p := by exact_mod_cast hcard p
    unfold residueDensity
    calc
      _ ≤ (2 * a p) / (a p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcard' (sq_nonneg _)
      _ = 2 / a p := by field_simp
  have hmoment := prime_index_log_moments a hinj hprime hz hle hlarge
    (residueDensity a A) (fun p => (hb p).1.le) hg
  have hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hprime p) (hprime q)).mpr
      (fun heq => hpq (hinj heq))).pow 2 2
  exact square_residue_sieve_moment_bound a A (fun p => (hprime p).two_le) hc
    hmin hmax R S N hR (Real.log z) hmoment hsmall


theorem prime_square_sieve_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (A : ∀ p, Finset (ZMod ((a p) ^ 2)))
    (hmin : ∀ p, a p ≤ (A p).card) (hcard : ∀ p, (A p).card ≤ 2 * a p)
    (R S N : ℕ) (hR : 2 ≤ R) (z : ℝ) (hz : 2 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N, eventProduct (fun p n => ¬ residueEvent a A S p n) Finset.univ n) ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - residueDensity a A p)) + (R : ℝ) ^ 8 := by
  classical
  by_cases hstrict : ∀ p, (A p).card < (a p) ^ 2
  · exact prime_square_sieve_upper_strict a hinj hprime A hmin hstrict hcard
      R S N hR z hz hle hlarge hsmall
  · obtain ⟨p, hp⟩ := not_forall.mp hstrict
    let : NeZero (a p) := ⟨(hprime p).ne_zero⟩
    have hcap : (A p).card ≤ (a p) ^ 2 := by
      simpa only [ZMod.card] using (A p).card_le_univ
    have heq : (A p).card = (a p) ^ 2 := le_antisymm hcap (Nat.le_of_not_gt hp)
    have hfull : A p = Finset.univ := Finset.eq_univ_of_card _ (by simpa only [ZMod.card] using heq)
    have hevent (n : ℕ) : residueEvent a A S p n := by simp [residueEvent, hfull]
    have hleft : (∑ n ∈ Finset.range N,
        eventProduct (fun q n => ¬ residueEvent a A S q n) Finset.univ n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simpa [eventProduct] using (show ∃ q, residueEvent a A S q n from ⟨p, hevent n⟩)
    have hdensity : residueDensity a A p = 1 := by
      unfold residueDensity
      rw [heq]
      push_cast
      exact div_self (pow_ne_zero 2 (by exact_mod_cast (hprime p).ne_zero))
    have hprod : (∏ q : P, (1 - residueDensity a A q)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      rw [hdensity]
      ring
    rw [hleft, hprod]
    simp

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676


theorem two_shift_sieve_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (k : ℤ) (R S N : ℕ) (hR : 2 ≤ R) (z : ℝ) (hz : 2 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    (∑ n ∈ Finset.range N,
      eventProduct (fun p n => ¬ residueEvent a
        (fun p => twoPositionResidues (a p) (k : ZMod ((a p) ^ 2))) S p n) Finset.univ n) ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N *
        (∏ p : P, (1 - twoPositionDensity (a p) (k : ZMod ((a p) ^ 2)))) + (R : ℝ) ^ 8 := by
  let A (p : P) := twoPositionResidues (a p) (k : ZMod ((a p) ^ 2))
  have hmin (p : P) : a p ≤ (A p).card := by
    have h : (smallResidues (a p)).card ≤ (A p).card :=
      Finset.card_le_card Finset.subset_union_left
    rwa [smallResidues_card (a p) (hprime p).one_lt.le] at h
  have hcard (p : P) : (A p).card ≤ 2 * a p := by
    have h := twoPositionResidues_card (a p) (hprime p).one_lt.le (k : ZMod ((a p) ^ 2))
    dsimp [A]
    omega
  have h := prime_square_sieve_upper a hinj hprime A hmin hcard R S N hR z hz hle hlarge hsmall
  simpa only [A, residueDensity, twoPositionDensity] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

def alternatingChoose (K m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (m + 1), (-1) ^ i * (K.choose i : ℤ)

theorem alternatingChoose_succ (K m : ℕ) :
    alternatingChoose (K + 1) m = (-1) ^ m * (K.choose m : ℤ) := by
  exact Int.alternating_sum_range_choose_eq_choose

theorem alternatingChoose_zero (m : ℕ) : alternatingChoose 0 m = 1 := by
  induction m with
  | zero => simp [alternatingChoose]
  | succ m ih =>
      unfold alternatingChoose at *
      rw [Finset.sum_range_succ]
      simp [ih]

theorem alternatingChoose_even_upper (K m : ℕ) (hm : Even m) :
    (if K = 0 then (1 : ℤ) else 0) ≤ alternatingChoose K m := by
  cases K with
  | zero => simp [alternatingChoose_zero]
  | succ K =>
      rw [alternatingChoose_succ, hm.neg_one_pow]
      simp

theorem alternatingChoose_odd_lower (K m : ℕ) (hm : Odd m) :
    alternatingChoose K m ≤ (if K = 0 then (1 : ℤ) else 0) := by
  cases K with
  | zero => simp [alternatingChoose_zero]
  | succ K =>
      rw [alternatingChoose_succ, hm.neg_one_pow]
      simp

theorem alternatingChoose_nonneg (K m : ℕ) (hm : Even m) :
    0 ≤ alternatingChoose K m := by
  have h := alternatingChoose_even_upper K m hm
  split_ifs at h <;> omega

theorem alternatingChoose_successor_gap (K m : ℕ) (hm : Even (m + 1)) :
    alternatingChoose K (m + 1) - alternatingChoose K m = (K.choose (m + 1) : ℤ) := by
  unfold alternatingChoose
  rw [Finset.sum_range_succ, hm.neg_one_pow]
  ring

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem event_choose_count {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) :
    (∑ d ∈ s.powersetCard k, eventProduct E d n) =
      ((@Finset.filter P (fun p => E p n) (Classical.decPred _) s).card.choose k : ℝ) := by
  classical
  have hset : (s.filter (fun p => E p n)).powersetCard k =
      (s.powersetCard k).filter (fun d => ∀ p ∈ d, E p n) := by
    ext d
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hk⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hd hp)).1, hk⟩,
        fun p hp => (Finset.mem_filter.mp (hd hp)).2⟩
    · rintro ⟨⟨hd, hk⟩, he⟩
      exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hd hp, he p hp⟩, hk⟩
  simp only [eventProduct, Finset.sum_boole]
  rw [← hset, Finset.card_powersetCard]

noncomputable def bonferroniEvent {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j *
    (∑ d ∈ s.powersetCard j, eventProduct E d n)

theorem bonferroniEvent_eq_alternatingChoose {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) :
    bonferroniEvent s k E n =
      (alternatingChoose ((@Finset.filter P (fun p => E p n) (Classical.decPred _) s).card) k : ℝ) := by
  classical
  simp only [bonferroniEvent, event_choose_count, alternatingChoose]
  push_cast
  rfl

theorem eventAvoidance_eq_zero_count {P N : Type*} [DecidableEq P]
    (s : Finset P) (E : P → N → Prop) (n : N) :
    eventProduct (fun p n => ¬ E p n) s n =
      if (@Finset.filter P (fun p => E p n) (Classical.decPred _) s).card = 0 then (1 : ℝ) else 0 := by
  classical
  have hz : (s.filter (fun p => E p n)).card = 0 ↔ ∀ p ∈ s, ¬ E p n := by
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  unfold eventProduct
  congr 1
  exact propext hz.symm

theorem bonferroniEvent_even_upper {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) (hk : Even k) :
    eventProduct (fun p n => ¬ E p n) s n ≤ bonferroniEvent s k E n := by
  classical
  rw [eventAvoidance_eq_zero_count, bonferroniEvent_eq_alternatingChoose]
  exact_mod_cast alternatingChoose_even_upper ((s.filter (fun p => E p n)).card) k hk

theorem bonferroniEvent_odd_lower {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) (hk : Odd k) :
    bonferroniEvent s k E n ≤ eventProduct (fun p n => ¬ E p n) s n := by
  classical
  rw [eventAvoidance_eq_zero_count, bonferroniEvent_eq_alternatingChoose]
  exact_mod_cast alternatingChoose_odd_lower ((s.filter (fun p => E p n)).card) k hk

theorem bonferroniEvent_gap {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) (hk : Even (k + 1)) :
    bonferroniEvent s (k + 1) E n - bonferroniEvent s k E n =
      ∑ d ∈ s.powersetCard (k + 1), eventProduct E d n := by
  classical
  simp only [bonferroniEvent_eq_alternatingChoose, event_choose_count]
  exact_mod_cast alternatingChoose_successor_gap ((s.filter (fun p => E p n)).card) k hk

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem weighted_sum_linearCombination {A B : Type*}
    (S : Finset A) (T : Finset B) (weight : B → ℝ) (coefficient : A → ℝ) (f : A → B → ℝ) :
    (∑ t ∈ T, weight t * (∑ a ∈ S, coefficient a * f a t)) =
      ∑ a ∈ S, coefficient a * (∑ t ∈ T, weight t * f a t) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem bernoulli_avoidance_mean {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g *
      eventProduct (fun p u => p ∉ u) s t) = ∏ p ∈ s, (1 - g p) := by
  classical
  have hproduct (t : Finset P) :
      (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) =
      eventProduct (fun p u => p ∉ u) s t := by
    by_cases hs : ∀ p ∈ s, p ∉ t
    · have hleft : (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro p _
        by_cases ht : p ∈ t
        · have hps : p ∉ s := fun h => hs p h ht
          simp [ht, hps]
        · simp [ht]
      rw [hleft]
      simpa [eventProduct] using hs
    · push Not at hs
      obtain ⟨p, hps, hpt⟩ := hs
      have hleft : (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ p)
        simp [hps, hpt]
      rw [hleft]
      have hnot : ¬ ∀ p ∈ s, p ∉ t := fun h => h p hps hpt
      simp [eventProduct, hnot]
  calc
    _ = ∑ t : Finset P, bernoulliWeight Finset.univ t g *
        (∏ p : P, if p ∈ t then (if p ∈ s then (0 : ℝ) else 1) else 1) := by simp_rw [hproduct]
    _ = ∏ p : P, (g p * (if p ∈ s then (0 : ℝ) else 1) + (1 - g p) * 1) := by
      simpa only [Finset.powerset_univ] using
        bernoulli_product_expectation Finset.univ g (fun p => if p ∈ s then 0 else 1) (fun _ => 1)
    _ = ∏ p ∈ s, (1 - g p) := by
      conv_rhs => rw [← Finset.prod_ite_mem_eq]
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p ∈ s <;> simp [hp]

noncomputable def bonferroniModel {P : Type*} (s : Finset P) (k : ℕ) (g : P → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (∑ d ∈ s.powersetCard j, ∏ p ∈ d, g p)

theorem bonferroni_model_expectation {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) :
    (∑ t : Finset P, bernoulliWeight Finset.univ t g *
      bonferroniEvent s k (fun p u => p ∈ u) t) = bonferroniModel s k g := by
  unfold bonferroniEvent bonferroniModel
  rw [weighted_sum_linearCombination]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact bernoulli_event_mean g d

theorem bonferroniModel_even_upper {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) (hk : Even k)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    (∏ p ∈ s, (1 - g p)) ≤ bonferroniModel s k g := by
  rw [← bernoulli_avoidance_mean, ← bonferroni_model_expectation]
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (bonferroniEvent_even_upper s k (fun p u => p ∈ u) t hk)
    (bernoulliWeight_nonneg Finset.univ t g (Finset.subset_univ _)
      (fun p _ => hg0 p) (fun p _ => hg1 p))

theorem bonferroniModel_odd_lower {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) (hk : Odd k)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    bonferroniModel s k g ≤ ∏ p ∈ s, (1 - g p) := by
  rw [← bernoulli_avoidance_mean, ← bonferroni_model_expectation]
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (bonferroniEvent_odd_lower s k (fun p u => p ∈ u) t hk)
    (bernoulliWeight_nonneg Finset.univ t g (Finset.subset_univ _)
      (fun p _ => hg0 p) (fun p _ => hg1 p))

theorem bonferroniModel_gap {P : Type*} (g : P → ℝ) (s : Finset P) (k : ℕ)
    (hk : Even (k + 1)) :
    bonferroniModel s (k + 1) g - bonferroniModel s k g =
      ∑ d ∈ s.powersetCard (k + 1), ∏ p ∈ d, g p := by
  unfold bonferroniModel
  rw [Finset.sum_range_succ, hk.neg_one_pow]
  ring

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

def bonferroniSupport {P : Type*} (s : Finset P) (k : ℕ) : Finset (Finset P) :=
  s.powerset.filter (fun d => d.card ≤ k)

theorem truncated_card_sum {P R : Type*} [Semiring R] (s : Finset P) (k : ℕ)
    (c : ℕ → R) (f : Finset P → R) :
    (∑ j ∈ Finset.range (k + 1), c j * (∑ d ∈ s.powersetCard j, f d)) =
      ∑ d ∈ bonferroniSupport s k, c d.card * f d := by
  classical
  simp only [Finset.powersetCard_eq_filter, Finset.sum_filter, Finset.mul_sum,
    mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff,
    bonferroniSupport, Finset.sum_filter]

theorem bonferroniEvent_expansion {P N : Type*} [DecidableEq P]
    (s : Finset P) (k : ℕ) (E : P → N → Prop) (n : N) :
    bonferroniEvent s k E n =
      ∑ d ∈ bonferroniSupport s k, (-1 : ℝ) ^ d.card * eventProduct E d n :=
  truncated_card_sum s k (fun j => (-1 : ℝ) ^ j) (fun d => eventProduct E d n)

theorem bonferroniModel_expansion {P : Type*} (s : Finset P) (k : ℕ) (g : P → ℝ) :
    bonferroniModel s k g =
      ∑ d ∈ bonferroniSupport s k, (-1 : ℝ) ^ d.card * (∏ p ∈ d, g p) :=
  truncated_card_sum s k (fun j => (-1 : ℝ) ^ j) (fun d => ∏ p ∈ d, g p)

theorem eventProduct_biUnion {J P N : Type*} [DecidableEq J] [DecidableEq P]
    (s : Finset J) (d : J → Finset P) (E : P → N → Prop) (n : N) :
    eventProduct E (s.biUnion d) n = ∏ j ∈ s, eventProduct E (d j) n := by
  induction s using Finset.induction_on with
  | empty => simp [eventProduct]
  | @insert j s hj ih =>
      rw [Finset.biUnion_insert, eventProduct_union, Finset.prod_insert hj, ih]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem disjoint_polynomial_transfer {J P N : Type*} [Fintype J] [DecidableEq J] [DecidableEq P]
    (I : Finset N) (T : J → Finset (Finset P)) (c : J → Finset P → ℝ)
    (E : P → N → Prop) (g a : P → ℝ) (M : ℝ)
    (hdisjoint : ∀ i j, i ≠ j → ∀ d ∈ T i, ∀ e ∈ T j, Disjoint d e)
    (hcount : ∀ b ∈ Fintype.piFinset T,
      |(∑ n ∈ I, eventProduct E (Finset.univ.biUnion b) n) -
        M * (∏ p ∈ Finset.univ.biUnion b, g p)| ≤ ∏ p ∈ Finset.univ.biUnion b, a p) :
    |(∑ n ∈ I, ∏ j : J, ∑ d ∈ T j, c j d * eventProduct E d n) -
      M * (∏ j : J, ∑ d ∈ T j, c j d * (∏ p ∈ d, g p))| ≤
      ∏ j : J, ∑ d ∈ T j, |c j d| * (∏ p ∈ d, a p) := by
  classical
  let U (b : J → Finset P) := Finset.univ.biUnion b
  let w (b : J → Finset P) := ∏ j : J, c j (b j)
  have hpair (b : J → Finset P) (hb : b ∈ Fintype.piFinset T) :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset J)) b := by
    intro i hi j hj hij
    exact hdisjoint i j hij (b i) (Fintype.mem_piFinset.mp hb i)
      (b j) (Fintype.mem_piFinset.mp hb j)
  have hactual (n : N) : (∏ j : J, ∑ d ∈ T j, c j d * eventProduct E d n) =
      ∑ b ∈ Fintype.piFinset T, w b * eventProduct E (U b) n := by
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.prod_mul_distrib]
    rw [eventProduct_biUnion]
  have hmodel : (∏ j : J, ∑ d ∈ T j, c j d * (∏ p ∈ d, g p)) =
      ∑ b ∈ Fintype.piFinset T, w b * (∏ p ∈ U b, g p) := by
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.prod_mul_distrib, Finset.prod_biUnion (hpair b hb)]
  have hexpand : (∑ n ∈ I, ∏ j : J, ∑ d ∈ T j, c j d * eventProduct E d n) =
      ∑ b ∈ Fintype.piFinset T, w b * (∑ n ∈ I, eventProduct E (U b) n) := by
    simp_rw [hactual]
    have h := weighted_sum_linearCombination (Fintype.piFinset T) I (fun _ => 1) w
      (fun b n => eventProduct E (U b) n)
    simpa only [one_mul] using h
  rw [hexpand, hmodel]
  have hdiff : (∑ b ∈ Fintype.piFinset T, w b * (∑ n ∈ I, eventProduct E (U b) n)) -
      M * (∑ b ∈ Fintype.piFinset T, w b * (∏ p ∈ U b, g p)) =
      ∑ b ∈ Fintype.piFinset T, w b *
        ((∑ n ∈ I, eventProduct E (U b) n) - M * (∏ p ∈ U b, g p)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hdiff]
  calc
    _ ≤ ∑ b ∈ Fintype.piFinset T, |w b *
        ((∑ n ∈ I, eventProduct E (U b) n) - M * (∏ p ∈ U b, g p))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Fintype.piFinset T, |w b| * (∏ p ∈ U b, a p) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcount b hb) (abs_nonneg _)
    _ = ∑ b ∈ Fintype.piFinset T, ∏ j : J, |c j (b j)| * (∏ p ∈ b j, a p) := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [w, Finset.abs_prod]
      rw [Finset.prod_biUnion (hpair b hb), Finset.prod_mul_distrib]
    _ = _ := (Finset.prod_univ_sum T (fun j d => |c j d| * (∏ p ∈ d, a p))).symm

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bonferroni_product_count_error {J P N : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq P]
    (I : Finset N) (blocks : J → Finset P) (k : J → ℕ)
    (E : P → N → Prop) (g a : P → ℝ) (M : ℝ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hcount : ∀ d : Finset P,
      |(∑ n ∈ I, eventProduct E d n) - M * (∏ p ∈ d, g p)| ≤ ∏ p ∈ d, a p) :
    |(∑ n ∈ I, ∏ j : J, bonferroniEvent (blocks j) (k j) E n) -
      M * (∏ j : J, bonferroniModel (blocks j) (k j) g)| ≤
      ∏ j : J, ∑ d ∈ bonferroniSupport (blocks j) (k j), ∏ p ∈ d, a p := by
  let T (j : J) := bonferroniSupport (blocks j) (k j)
  let c (_ : J) (d : Finset P) : ℝ := (-1) ^ d.card
  have hpair : ∀ i j, i ≠ j → ∀ d ∈ T i, ∀ e ∈ T j, Disjoint d e := by
    intro i j hij d hd e he
    have hd' : d ⊆ blocks i := Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
    have he' : e ⊆ blocks j := Finset.mem_powerset.mp (Finset.mem_filter.mp he).1
    exact (hdisjoint hij).mono hd' he'
  have h := disjoint_polynomial_transfer I T c E g a M hpair (fun b _ => hcount _)
  simpa only [bonferroniEvent_expansion, bonferroniModel_expansion, T, c,
    abs_pow, abs_neg, abs_one, one_pow, one_mul] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem one_shift_prime_count_error {P : Type*} [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (d : Finset P) (S N : ℕ) :
    |(∑ n ∈ Finset.range N,
      eventProduct (residueEvent a (fun p => smallResidues (a p)) S) d n) -
      (N : ℝ) * (∏ p ∈ d, (1 : ℝ) / a p)| ≤ ∏ p ∈ d, (a p : ℝ) := by
  let A (p : P) := smallResidues (a p)
  have hcard (p : P) : (A p).card = a p := smallResidues_card (a p) (hprime p).one_lt.le
  have hdensity (p : P) : residueDensity a A p = (1 : ℝ) / a p := by
    unfold residueDensity
    rw [hcard]
    have hp0 : (a p : ℝ) ≠ 0 := by exact_mod_cast (hprime p).ne_zero
    field_simp
  have hcoprime : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hprime p) (hprime q)).mpr
      (fun h => hpq (hinj h))).pow 2 2
  have h := residueEvent_count_error a A (fun p => (hprime p).pos) hcoprime d S N
  simpa only [hcard, hdensity, A] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem sum_powers_le_add_pow (n k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), n ^ i) ≤ (1 + n) ^ k := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), n ^ i * k.choose i := by
      apply Finset.sum_le_sum
      intro i hi
      have hpos := Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      simpa using Nat.mul_le_mul_left (n ^ i) hpos
    _ = (n + 1) ^ k := by rw [add_pow]; simp
    _ = (1 + n) ^ k := by rw [Nat.add_comm n 1]

theorem bounded_elementary_sum {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (B k : ℕ) (ha : ∀ p ∈ s, a p ≤ B) :
    (∑ d ∈ s.powersetCard k, ∏ p ∈ d, a p) ≤ s.card.choose k * B ^ k := by
  calc
    _ ≤ ∑ _d ∈ s.powersetCard k, B ^ k := by
      apply Finset.sum_le_sum
      intro d hd
      have hprod : (∏ p ∈ d, a p) ≤ ∏ _p ∈ d, B :=
        Finset.prod_le_prod' (fun p hp => ha p ((Finset.mem_powersetCard.mp hd).1 hp))
      simpa only [Finset.prod_const, (Finset.mem_powersetCard.mp hd).2] using hprod
    _ = s.card.choose k * B ^ k := by simp

theorem truncated_block_weight_bound {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (B k : ℕ) (ha : ∀ p ∈ s, a p ≤ B) :
    (∑ d ∈ bonferroniSupport s k, ∏ p ∈ d, a p) ≤ (1 + s.card * B) ^ k := by
  have hsum := truncated_card_sum s k (fun _ => (1 : ℕ)) (fun d => ∏ p ∈ d, a p)
  simp only [one_mul] at hsum
  rw [← hsum]
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), s.card.choose i * B ^ i :=
      Finset.sum_le_sum (fun i _ => bounded_elementary_sum s a B i ha)
    _ ≤ ∑ i ∈ Finset.range (k + 1), (s.card * B) ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := Nat.mul_le_mul_right (B ^ i) (Nat.choose_le_pow s.card i)
      simpa only [mul_pow] using h
    _ ≤ _ := sum_powers_le_add_pow (s.card * B) k

theorem block_weight_power_bound {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (B k : ℕ) (hB : 1 ≤ B)
    (ha : ∀ p ∈ s, a p ≤ B) (hcard : s.card + 1 ≤ B) :
    (∑ d ∈ bonferroniSupport s k, ∏ p ∈ d, a p) ≤ B ^ (2 * k) := by
  have hbase : 1 + s.card * B ≤ B ^ 2 := by nlinarith
  calc
    _ ≤ (1 + s.card * B) ^ k := truncated_block_weight_bound s a B k ha
    _ ≤ (B ^ 2) ^ k := Nat.pow_le_pow_left hbase k
    _ = B ^ (2 * k) := (pow_mul B 2 k).symm

theorem bounded_block_card {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (hinj : Set.InjOn a s) (B : ℕ) (hB : 1 ≤ B)
    (hmin : ∀ p ∈ s, 2 ≤ a p) (hmax : ∀ p ∈ s, a p ≤ B) : s.card + 1 ≤ B := by
  have hsubset : s.image a ⊆ Finset.Icc 2 B := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨hmin p hp, hmax p hp⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_iff.mpr hinj, Nat.card_Icc] at hcard
  omega

theorem bounded_block_coefficient_sum {P : Type*} [DecidableEq P]
    (s : Finset P) (a : P → ℕ) (hinj : Set.InjOn a s) (B k : ℕ) (hB : 1 ≤ B)
    (hmin : ∀ p ∈ s, 2 ≤ a p) (hmax : ∀ p ∈ s, a p ≤ B) :
    (∑ d ∈ bonferroniSupport s k, ∏ p ∈ d, a p) ≤ B ^ (2 * k) :=
  block_weight_power_bound s a B k hB hmax (bounded_block_card s a hinj B hB hmin hmax)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bounded_block_product_count_error {J P : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (blocks : J → Finset P) (k B : J → ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hB : ∀ j, 1 ≤ B j) (hmax : ∀ j, ∀ p ∈ blocks j, a p ≤ B j)
    (S N : ℕ) :
    |(∑ n ∈ Finset.range N, ∏ j : J, bonferroniEvent (blocks j) (k j)
        (residueEvent a (fun p => smallResidues (a p)) S) n) -
      (N : ℝ) * (∏ j : J, bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p))| ≤
      ∏ j : J, (B j : ℝ) ^ (2 * k j) := by
  have h := bonferroni_product_count_error (Finset.range N) blocks k
    (residueEvent a (fun p => smallResidues (a p)) S)
    (fun p => (1 : ℝ) / a p) (fun p => (a p : ℝ)) N hdisjoint
    (fun d => one_shift_prime_count_error a hinj hprime d S N)
  apply h.trans
  apply Finset.prod_le_prod
  · intro j hj
    exact Finset.sum_nonneg (fun d hd => Finset.prod_nonneg (fun p hp => Nat.cast_nonneg (a p)))
  · intro j hj
    have hNat := bounded_block_coefficient_sum (blocks j) a hinj.injOn (B j) (k j) (hB j)
      (fun p hp => (hprime p).two_le) (hmax j)
    exact_mod_cast hNat

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bracketLoss_replacements {J : Type*} [DecidableEq J]
    (s : Finset J) (lower upper : J → ℝ) :
    bracketLoss s lower upper = ∑ j ∈ s,
      ((∏ i ∈ s, upper i) - ∏ i ∈ s, Function.update upper j (lower j) i) := by
  unfold bracketLoss
  apply Finset.sum_congr rfl
  intro j hj
  have hU := Finset.mul_prod_erase s upper hj
  have hL : (∏ i ∈ s, Function.update upper j (lower j) i) =
      lower j * ∏ i ∈ s.erase j, upper i := by
    simpa only [Finset.sdiff_singleton_eq_erase] using Finset.prod_update_of_mem hj upper (lower j)
  rw [hL, ← hU]
  ring

theorem scalar_bracket_transfer {J : Type*} (s : Finset J)
    (A a E : ℝ) (B b : J → ℝ) (hA : |A - a| ≤ E)
    (hB : ∀ j ∈ s, |B j - b j| ≤ E) :
    (a - ∑ j ∈ s, (a - b j)) - (2 * (s.card : ℝ) + 1) * E ≤
      A - ∑ j ∈ s, (A - B j) := by
  have hAlow := (abs_le.mp hA).1
  have hAup := (abs_le.mp hA).2
  have hsum : (∑ j ∈ s, (A - B j)) ≤ ∑ j ∈ s, ((a - b j) + 2 * E) := by
    apply Finset.sum_le_sum
    intro j hj
    have hBlow := (abs_le.mp (hB j hj)).1
    linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

theorem product_bracket_transfer {J N : Type*} [DecidableEq J]
    (s : Finset J) (I : Finset N) (upper lower : J → N → ℝ)
    (u l : J → ℝ) (M E : ℝ)
    (hU : |(∑ n ∈ I, ∏ j ∈ s, upper j n) - M * (∏ j ∈ s, u j)| ≤ E)
    (hL : ∀ j ∈ s,
      |(∑ n ∈ I, ∏ i ∈ s, Function.update (fun i => upper i n) j (lower j n) i) -
        M * (∏ i ∈ s, Function.update u j (l j) i)| ≤ E) :
    M * ((∏ j ∈ s, u j) - bracketLoss s l u) - (2 * (s.card : ℝ) + 1) * E ≤
      ∑ n ∈ I, ((∏ j ∈ s, upper j n) - bracketLoss s (fun j => lower j n) (fun j => upper j n)) := by
  have h := scalar_bracket_transfer s
    (∑ n ∈ I, ∏ j ∈ s, upper j n) (M * (∏ j ∈ s, u j)) E
    (fun j => ∑ n ∈ I, ∏ i ∈ s, Function.update (fun i => upper i n) j (lower j n) i)
    (fun j => M * (∏ i ∈ s, Function.update u j (l j) i)) hU hL
  have hmodel : M * ((∏ j ∈ s, u j) - bracketLoss s l u) =
      M * (∏ j ∈ s, u j) -
        ∑ j ∈ s, (M * (∏ i ∈ s, u i) - M * (∏ i ∈ s, Function.update u j (l j) i)) := by
    rw [bracketLoss_replacements]
    simp only [mul_sub, Finset.mul_sum]
  have hactual : (∑ n ∈ I, ((∏ j ∈ s, upper j n) -
      bracketLoss s (fun j => lower j n) (fun j => upper j n))) =
      (∑ n ∈ I, ∏ j ∈ s, upper j n) - ∑ j ∈ s,
        ((∑ n ∈ I, ∏ i ∈ s, upper i n) -
          ∑ n ∈ I, ∏ i ∈ s, Function.update (fun i => upper i n) j (lower j n) i) := by
    simp_rw [bracketLoss_replacements]
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  rw [hmodel, hactual]
  exact h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem grouped_first_moment_lower {J P : Type*}
    [Fintype J] [DecidableEq J] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (blocks : J → Finset P) (k B : J → ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hB : ∀ j, 1 ≤ B j) (hmax : ∀ j, ∀ p ∈ blocks j, a p ≤ B j)
    (hk : ∀ j, Even (k j)) (hkpos : ∀ j, 1 ≤ k j) (S N : ℕ) :
    (N : ℝ) * ((∏ j : J, bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p)) -
        bracketLoss Finset.univ
          (fun j => bonferroniModel (blocks j) (k j - 1) (fun p => (1 : ℝ) / a p))
          (fun j => bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p))) -
      (2 * (Fintype.card J : ℝ) + 1) * (∏ j : J, (B j : ℝ) ^ (2 * k j)) ≤
      ∑ n ∈ Finset.range N, eventProduct
        (fun p n => ¬ residueEvent a (fun p => smallResidues (a p)) S p n)
        (Finset.univ.biUnion blocks) n := by
  let ev := residueEvent a (fun p => smallResidues (a p)) S
  let upper (j : J) (n : ℕ) := bonferroniEvent (blocks j) (k j) ev n
  let lower (j : J) (n : ℕ) := bonferroniEvent (blocks j) (k j - 1) ev n
  let u (j : J) := bonferroniModel (blocks j) (k j) (fun p => (1 : ℝ) / a p)
  let l (j : J) := bonferroniModel (blocks j) (k j - 1) (fun p => (1 : ℝ) / a p)
  let error : ℝ := ∏ j : J, (B j : ℝ) ^ (2 * k j)
  have hU : |(∑ n ∈ Finset.range N, ∏ j : J, upper j n) - N * (∏ j : J, u j)| ≤ error :=
    bounded_block_product_count_error a hinj hprime blocks k B hdisjoint hB hmax S N
  have hL : ∀ j : J, j ∈ (Finset.univ : Finset J) →
      |(∑ n ∈ Finset.range N, ∏ i : J, Function.update (fun i => upper i n) j (lower j n) i) -
        N * (∏ i : J, Function.update u j (l j) i)| ≤ error := by
    intro j hj
    let k' := Function.update k j (k j - 1)
    have hsmall (i : J) : k' i ≤ k i := by
      by_cases hi : i = j <;> simp [k', hi]
    have herror : (∏ i : J, (B i : ℝ) ^ (2 * k' i)) ≤ error := by
      apply Finset.prod_le_prod
      · intro i hi
        exact pow_nonneg (Nat.cast_nonneg _) _
      · intro i hi
        exact pow_le_pow_right₀ (by exact_mod_cast hB i) (Nat.mul_le_mul_left 2 (hsmall i))
    have h := (bounded_block_product_count_error a hinj hprime blocks k' B hdisjoint hB hmax S N).trans herror
    have hactual (i : J) (n : ℕ) : bonferroniEvent (blocks i) (k' i) ev n =
        Function.update (fun i => upper i n) j (lower j n) i := by
      by_cases hi : i = j <;> simp [k', upper, lower, hi]
    have hmodel (i : J) : bonferroniModel (blocks i) (k' i) (fun p => (1 : ℝ) / a p) =
        Function.update u j (l j) i := by
      by_cases hi : i = j <;> simp [k', u, l, hi]
    change |(∑ n ∈ Finset.range N, ∏ i : J, bonferroniEvent (blocks i) (k' i) ev n) -
      (N : ℝ) * (∏ i : J, bonferroniModel (blocks i) (k' i) (fun p => (1 : ℝ) / a p))| ≤ error at h
    simpa only [hactual, hmodel] using h
  have htransfer := product_bracket_transfer (Finset.univ : Finset J) (Finset.range N)
    upper lower u l (N : ℝ) error hU hL
  have hodd (j : J) : Odd (k j - 1) := by
    obtain ⟨m, hm⟩ := hk j
    refine ⟨m - 1, ?_⟩
    have := hkpos j
    omega
  have hpointwise (n : ℕ) : (∏ j : J, upper j n) -
      bracketLoss Finset.univ (fun j => lower j n) (fun j => upper j n) ≤
        eventProduct (fun p n => ¬ ev p n) (Finset.univ.biUnion blocks) n := by
    have h := product_lower_bound (Finset.univ : Finset J)
      (fun j => eventProduct (fun p n => ¬ ev p n) (blocks j) n)
      (fun j => lower j n) (fun j => upper j n) (by
        intro j hj
        unfold eventProduct
        split_ifs <;> norm_num)
      (fun j hj => bonferroniEvent_odd_lower (blocks j) (k j - 1) ev n (hodd j))
      (fun j hj => bonferroniEvent_even_upper (blocks j) (k j) ev n (hk j))
    rwa [← eventProduct_biUnion] at h
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hpointwise n)
  simpa only [Finset.card_univ] using htransfer.trans hsum

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem scaled_elementary_sum_le {P : Type*} [DecidableEq P]
    (s : Finset P) (g : P → ℝ) (k : ℕ) (hg : ∀ p ∈ s, 0 ≤ g p) :
    (2 : ℝ) ^ k * (∑ d ∈ s.powersetCard k, ∏ p ∈ d, g p) ≤
      ∏ p ∈ s, (1 + 2 * g p) := by
  calc
    _ = ∑ d ∈ s.powersetCard k, ∏ p ∈ d, (2 * g p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hd).2]
    _ ≤ ∑ d ∈ s.powerset, ∏ p ∈ d, (2 * g p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hd).1
      · intro d hd _
        exact Finset.prod_nonneg (fun p hp => mul_nonneg (by norm_num)
          (hg p (Finset.mem_powerset.mp hd hp)))
    _ = ∏ p ∈ s, (1 + 2 * g p) := by
      simpa only [Finset.prod_const_one, mul_one, add_comm] using
        (Finset.prod_add (fun p => 2 * g p) (fun _ => (1 : ℝ)) s).symm

theorem elementary_sum_geometric_bound {P : Type*} [DecidableEq P]
    (s : Finset P) (g : P → ℝ) (k : ℕ) (C : ℝ)
    (hg : ∀ p ∈ s, 0 ≤ g p) (hC : (∑ p ∈ s, g p) ≤ C) :
    (∑ d ∈ s.powersetCard k, ∏ p ∈ d, g p) ≤ Real.exp (2 * C) / (2 : ℝ) ^ k := by
  have hprod : (∏ p ∈ s, (1 + 2 * g p)) ≤ Real.exp (2 * C) := by
    calc
      _ ≤ ∏ p ∈ s, Real.exp (2 * g p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact add_nonneg (by norm_num) (mul_nonneg (by norm_num) (hg p hp))
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (2 * g p)
      _ = Real.exp (∑ p ∈ s, 2 * g p) := (Real.exp_sum _ _).symm
      _ = Real.exp (2 * ∑ p ∈ s, g p) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (2 * C) := Real.exp_le_exp.mpr (by linarith)
  have h := (scaled_elementary_sum_le s g k hg).trans hprod
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).mpr
  simpa only [mul_comm] using h

theorem exp_neg_two_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have he : -2 * x ≤ Real.log (1 - x) := by linarith
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr he

theorem survival_product_lower {P : Type*} (s : Finset P) (g : P → ℝ) (C : ℝ)
    (hg0 : ∀ p ∈ s, 0 ≤ g p) (hg1 : ∀ p ∈ s, g p ≤ 1 / 2)
    (hC : (∑ p ∈ s, g p) ≤ C) :
    Real.exp (-2 * C) ≤ ∏ p ∈ s, (1 - g p) := by
  calc
    _ ≤ Real.exp (-2 * ∑ p ∈ s, g p) := Real.exp_le_exp.mpr (by linarith)
    _ = ∏ p ∈ s, Real.exp (-2 * g p) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le)
      (fun p hp => exp_neg_two_le_one_sub (hg0 p hp) (hg1 p hp))

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem bonferroniModel_relative_gap {P : Type*} [Fintype P] [DecidableEq P]
    (g : P → ℝ) (s : Finset P) (k : ℕ) (hk : Even (k + 1)) (C : ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1 / 2)
    (hC : (∑ p ∈ s, g p) ≤ C) :
    bonferroniModel s (k + 1) g - bonferroniModel s k g ≤
      (Real.exp (4 * C) / (2 : ℝ) ^ (k + 1)) * bonferroniModel s (k + 1) g := by
  have hV := survival_product_lower s g C (fun p _ => hg0 p) (fun p _ => hg1 p) hC
  have hcoef : 0 ≤ Real.exp (4 * C) / (2 : ℝ) ^ (k + 1) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hV hcoef
  have hexp : Real.exp (4 * C) * Real.exp (-2 * C) = Real.exp (2 * C) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : (Real.exp (4 * C) / (2 : ℝ) ^ (k + 1)) * Real.exp (-2 * C) =
      Real.exp (2 * C) / (2 : ℝ) ^ (k + 1) := by
    rw [div_mul_eq_mul_div, hexp]
  rw [hid] at hscaled
  have hupper := bonferroniModel_even_upper g s (k + 1) hk hg0 (fun p => by have := hg1 p; linarith)
  calc
    _ = ∑ d ∈ s.powersetCard (k + 1), ∏ p ∈ d, g p := bonferroniModel_gap g s k hk
    _ ≤ Real.exp (2 * C) / (2 : ℝ) ^ (k + 1) :=
      elementary_sum_geometric_bound s g (k + 1) C (fun p _ => hg0 p) hC
    _ ≤ (Real.exp (4 * C) / (2 : ℝ) ^ (k + 1)) * (∏ p ∈ s, (1 - g p)) := hscaled
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper hcoef

theorem product_bracket_relative_lower {J : Type*} [DecidableEq J]
    (s : Finset J) (V lower upper error : J → ℝ)
    (hV : ∀ j ∈ s, 0 ≤ V j) (hupper : ∀ j ∈ s, V j ≤ upper j)
    (hgap : ∀ j ∈ s, upper j - lower j ≤ error j * upper j)
    (herror : (∑ j ∈ s, error j) ≤ 1) :
    (1 - ∑ j ∈ s, error j) * (∏ j ∈ s, V j) ≤
      (∏ j ∈ s, upper j) - bracketLoss s lower upper := by
  have hU : ∀ j ∈ s, 0 ≤ upper j := fun j hj => (hV j hj).trans (hupper j hj)
  have hprod : (∏ j ∈ s, V j) ≤ ∏ j ∈ s, upper j := Finset.prod_le_prod hV hupper
  have hloss : bracketLoss s lower upper ≤ (∑ j ∈ s, error j) * (∏ j ∈ s, upper j) := by
    unfold bracketLoss
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hnonneg : 0 ≤ ∏ i ∈ s.erase j, upper i :=
      Finset.prod_nonneg (fun i hi => hU i (Finset.mem_of_mem_erase hi))
    calc
      _ ≤ (error j * upper j) * (∏ i ∈ s.erase j, upper i) :=
        mul_le_mul_of_nonneg_right (hgap j hj) hnonneg
      _ = error j * (∏ i ∈ s, upper i) := by
        rw [mul_assoc, Finset.mul_prod_erase s upper hj]
  have hscaled := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr herror)
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem sum_nat_div_two_pow (J : ℕ) :
    (∑ j ∈ Finset.range J, (j : ℝ) / 2 ^ j) = 2 - (2 * J + 2) / (2 : ℝ) ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring

theorem sum_nat_div_two_pow_le (J : ℕ) :
    (∑ j ∈ Finset.range J, (j : ℝ) / 2 ^ j) ≤ 2 := by
  rw [sum_nat_div_two_pow]
  have h : 0 ≤ (2 * (J : ℝ) + 2) / (2 : ℝ) ^ J := by positivity
  linarith

theorem block_degree_budget (L J : ℕ) :
    (∑ j ∈ Finset.range J, (2 * (L + j) : ℝ) / 2 ^ j) ≤ 4 * L + 4 := by
  have hgeometric : (∑ j ∈ Finset.range J, (1 : ℝ) / 2 ^ j) ≤ 2 := by
    simpa only [one_div_pow] using sum_geometric_two_le J
  have hweighted := sum_nat_div_two_pow_le J
  have heq : (∑ j ∈ Finset.range J, (2 * (L + j) : ℝ) / 2 ^ j) =
      2 * L * (∑ j ∈ Finset.range J, (1 : ℝ) / 2 ^ j) +
        2 * (∑ j ∈ Finset.range J, (j : ℝ) / 2 ^ j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  have hscale := mul_le_mul_of_nonneg_left hgeometric (by positivity : 0 ≤ 2 * (L : ℝ))
  linarith

theorem block_error_sum (C : ℝ) (L J : ℕ) :
    (∑ j ∈ Finset.range J, Real.exp (4 * C) / (2 : ℝ) ^ (2 * (L + j))) ≤
      2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) := by
  have hsplit (j : ℕ) : Real.exp (4 * C) / (2 : ℝ) ^ (2 * (L + j)) =
      (Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * (1 / 4 : ℝ) ^ j := by
    rw [Nat.mul_add, pow_add]
    have hp : (2 : ℝ) ^ (2 * j) = 4 ^ j := by rw [pow_mul]; norm_num
    rw [hp, one_div_pow]
    ring
  simp only [hsplit, ← Finset.mul_sum]
  have hsum : (∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j) ≤ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j _
        gcongr <;> norm_num
      _ ≤ 2 := sum_geometric_two_le J
  have h := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ Real.exp (4 * C) / (2 : ℝ) ^ (2 * L))
  convert h using 1 <;> first | rfl | ring

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_block_first_moment_lower {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (J L : ℕ) (hL : 1 ≤ L) (blocks : Fin J → Finset P) (B : Fin J → ℕ)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hB : ∀ j, 1 ≤ B j) (hmax : ∀ j, ∀ p ∈ blocks j, a p ≤ B j)
    (C : ℝ) (hC : ∀ j, (∑ p ∈ blocks j, (1 : ℝ) / a p) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) (S N : ℕ) :
    (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N *
        (∏ p ∈ Finset.univ.biUnion blocks, (1 - (1 : ℝ) / a p)) -
      (2 * (J : ℝ) + 1) * (∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val))) ≤
      ∑ n ∈ Finset.range N, eventProduct
        (fun p n => ¬ residueEvent a (fun p => smallResidues (a p)) S p n)
        (Finset.univ.biUnion blocks) n := by
  let g (p : P) : ℝ := 1 / a p
  let k (j : Fin J) := 2 * (L + j.val)
  let error (j : Fin J) : ℝ := Real.exp (4 * C) / (2 : ℝ) ^ k j
  let u (j : Fin J) := bonferroniModel (blocks j) (k j) g
  let l (j : Fin J) := bonferroniModel (blocks j) (k j - 1) g
  let V (j : Fin J) := ∏ p ∈ blocks j, (1 - g p)
  have hg0 (p : P) : 0 ≤ g p := by dsimp [g]; positivity
  have hg1 (p : P) : g p ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < a p := by exact_mod_cast (hprime p).pos
    have hp2 : (2 : ℝ) ≤ a p := by exact_mod_cast (hprime p).two_le
    apply (div_le_iff₀ hp0).mpr
    linarith
  have hk (j : Fin J) : Even (k j) := ⟨L + j.val, by dsimp [k]; omega⟩
  have hkpos (j : Fin J) : 1 ≤ k j := by dsimp [k]; omega
  have hV : ∀ j ∈ (Finset.univ : Finset (Fin J)), 0 ≤ V j := by
    intro j hj
    apply Finset.prod_nonneg
    intro p hp
    have := hg1 p
    linarith
  have hupper : ∀ j ∈ (Finset.univ : Finset (Fin J)), V j ≤ u j := by
    intro j hj
    exact bonferroniModel_even_upper g (blocks j) (k j) (hk j) hg0 (fun p => by have := hg1 p; linarith)
  have hgap : ∀ j ∈ (Finset.univ : Finset (Fin J)), u j - l j ≤ error j * u j := by
    intro j hj
    have hsub : k j - 1 + 1 = k j := Nat.sub_add_cancel (hkpos j)
    have heven : Even (k j - 1 + 1) := by rw [hsub]; exact hk j
    have h := bonferroniModel_relative_gap g (blocks j) (k j - 1) heven C hg0 hg1 (hC j)
    simpa only [hsub, u, l, error] using h
  have hsum : (∑ j : Fin J, error j) ≤ 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) := by
    have h := block_error_sum C L J
    simpa only [Finset.sum_range, error, k] using h
  have hmodel := product_bracket_relative_lower (Finset.univ : Finset (Fin J))
    V l u error hV hupper hgap (hsum.trans hsmall)
  have hVprod : 0 ≤ ∏ j : Fin J, V j := Finset.prod_nonneg hV
  have hcompare := mul_le_mul_of_nonneg_right (sub_le_sub_left hsum 1) hVprod
  have hmodel' := hcompare.trans hmodel
  have hscaled := mul_le_mul_of_nonneg_left hmodel' (Nat.cast_nonneg N)
  have hactual := grouped_first_moment_lower a hinj hprime blocks k B hdisjoint hB hmax hk hkpos S N
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin J))) blocks :=
    fun i hi j hj hij => hdisjoint hij
  have hVeq : (∏ p ∈ Finset.univ.biUnion blocks, (1 - g p)) = ∏ j : Fin J, V j :=
    Finset.prod_biUnion hpair
  have hpower : (∏ j : Fin J, (B j : ℝ) ^ (2 * k j)) =
      ∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val)) := by
    apply Finset.prod_congr rfl
    intro j hj
    dsimp [k]
    congr 1
    omega
  change (N : ℝ) * ((∏ j : Fin J, u j) - bracketLoss Finset.univ l u) -
    (2 * (Fintype.card (Fin J) : ℝ) + 1) * (∏ j : Fin J, (B j : ℝ) ^ (2 * k j)) ≤ _ at hactual
  rw [Fintype.card_fin, hpower] at hactual
  change (1 - _) * (N : ℝ) * (∏ p ∈ Finset.univ.biUnion blocks, (1 - g p)) - _ ≤ _
  rw [hVeq]
  nlinarith

end Erdos676
end

section
open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem primeReciprocalSum_eq (x : ℝ) :
    primeReciprocalSum x = Real.log (Real.log x) + Mertens.M + Mertens.E₂p x := by
  exact Mertens.sum_prime_div_eq x


theorem prime_power_band_limit (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun X : ℝ => primeReciprocalSum (X ^ b) - primeReciprocalSum (X ^ a))
      atTop (nhds (Real.log b - Real.log a)) := by
  have herror : Tendsto Mertens.E₂p atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have hea := herror.comp (tendsto_rpow_atTop ha)
  have heb := herror.comp (tendsto_rpow_atTop hb)
  have hlimit : Tendsto
      (fun X : ℝ => Real.log b - Real.log a + (Mertens.E₂p (X ^ b) - Mertens.E₂p (X ^ a)))
      atTop (nhds (Real.log b - Real.log a)) := by
    simpa using tendsto_const_nhds.add (heb.sub hea)
  refine Filter.Tendsto.congr' ?_ hlimit
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [primeReciprocalSum_eq, primeReciprocalSum_eq,
    Real.log_rpow hX0 b, Real.log_rpow hX0 a,
    Real.log_mul (ne_of_gt hb) (ne_of_gt hlog),
    Real.log_mul (ne_of_gt ha) (ne_of_gt hlog)]
  ring

end Erdos676
end

section
open scoped BigOperators Topology
open Filter

namespace Erdos676

theorem mem_primesUpToReal (x : ℝ) (p : ℕ) :
    p ∈ primesUpToReal x ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  constructor
  · intro hp
    obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
    refine ⟨hprime, ?_⟩
    exact (Nat.le_floor_iff' hprime.ne_zero).mp (Finset.mem_Ioc.mp hinterval).2
  · rintro ⟨hprime, hx⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hprime.pos, Nat.le_floor hx⟩, hprime⟩

theorem primesUpToReal_subset {x y : ℝ} (hxy : x ≤ y) : primesUpToReal x ⊆ primesUpToReal y := by
  intro p hp
  obtain ⟨hprime, hpx⟩ := (mem_primesUpToReal x p).mp hp
  exact (mem_primesUpToReal y p).mpr ⟨hprime, hpx.trans hxy⟩

theorem primeReciprocalSum_nonneg (x : ℝ) : 0 ≤ primeReciprocalSum x :=
  Finset.sum_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))

theorem primeReciprocalSum_mono : Monotone primeReciprocalSum := by
  intro x y hxy
  exact Finset.sum_le_sum_of_subset_of_nonneg (primesUpToReal_subset hxy)
    (fun p _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))

theorem exists_half_power_prime_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C := by
  have hlimit := prime_power_band_limit (1 / 2 : ℝ) 1 (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hlimit
  let limit := Real.log 1 - Real.log (1 / 2 : ℝ)
  have hevent : ∀ᶠ x : ℝ in atTop,
      primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) < limit + 1 :=
    (tendsto_order.mp hlimit).2 _ (by dsimp [limit]; linarith)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hevent
  let T := max 2 X₀
  let C := 1 + |primeReciprocalSum T| + |limit|
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x
  by_cases hTx : T ≤ x
  · have h := hX₀ x ((le_max_right 2 X₀).trans hTx)
    have hlim := le_abs_self limit
    have hmass := abs_nonneg (primeReciprocalSum T)
    dsimp [C]
    linarith
  · have hxT : x ≤ T := (lt_of_not_ge hTx).le
    have hmono := primeReciprocalSum_mono hxT
    have hnonneg := primeReciprocalSum_nonneg (x ^ (1 / 2 : ℝ))
    have habs := le_abs_self (primeReciprocalSum T)
    have hlim := abs_nonneg limit
    dsimp [C]
    linarith

theorem prime_interval_mass_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {x y : ℝ} (hyx : y ≤ x) (hmin : ∀ p, y < (a p : ℝ)) (hmax : ∀ p, (a p : ℝ) ≤ x) :
    (∑ p : P, (1 : ℝ) / a p) ≤ primeReciprocalSum x - primeReciprocalSum y := by
  have himage : Finset.univ.image a ⊆ primesUpToReal x \ primesUpToReal y := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_primesUpToReal x (a p)).mpr ⟨hprime p, hmax p⟩, ?_⟩
    intro hbad
    have hle := ((mem_primesUpToReal y (a p)).mp hbad).2
    exact (not_le_of_gt (hmin p)) hle
  have hsum : (∑ p : P, (1 : ℝ) / a p) =
      ∑ q ∈ Finset.univ.image a, (1 : ℝ) / q := by
    symm
    rw [Finset.sum_image]
    intro p hp q hq h
    exact hinj h
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg himage
    (fun p _ _ => div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg p))
  have hsplit : (∑ p ∈ primesUpToReal x \ primesUpToReal y, (1 : ℝ) / p) +
      primeReciprocalSum y = primeReciprocalSum x :=
    Finset.sum_sdiff (primesUpToReal_subset hyx)
  rw [hsum]
  linarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def dyadicCutoff (z : ℝ) : ℕ → ℝ
  | 0 => z
  | j + 1 => dyadicCutoff z j ^ (1 / 2 : ℝ)

theorem one_le_dyadicCutoff {z : ℝ} (hz : 1 ≤ z) (j : ℕ) : 1 ≤ dyadicCutoff z j := by
  induction j with
  | zero => exact hz
  | succ j ih => exact Real.one_le_rpow ih (by norm_num)

theorem dyadicCutoff_antitone {z : ℝ} (hz : 1 ≤ z) : Antitone (dyadicCutoff z) := by
  apply antitone_nat_of_succ_le
  intro j
  exact Real.rpow_le_self_of_one_le (one_le_dyadicCutoff hz j) (by norm_num)

theorem log_dyadicCutoff {z : ℝ} (hz : 1 ≤ z) (j : ℕ) :
    Real.log (dyadicCutoff z j) = (1 / 2 : ℝ) ^ j * Real.log z := by
  induction j with
  | zero => simp [dyadicCutoff]
  | succ j ih =>
      have hp : 0 < dyadicCutoff z j := lt_of_lt_of_le zero_lt_one (one_le_dyadicCutoff hz j)
      rw [dyadicCutoff, Real.log_rpow hp, ih, pow_succ]
      ring

theorem exists_cutoff_interval (cutoff : ℕ → ℝ) (J : ℕ) (x : ℝ)
    (hfirst : x ≤ cutoff 0) (hlast : cutoff J < x) :
    ∃ j < J, cutoff (j + 1) < x ∧ x ≤ cutoff j := by
  induction J generalizing x with
  | zero => linarith
  | succ J ih =>
      by_cases hj : cutoff J < x
      · obtain ⟨j, hjJ, hlow, hupp⟩ := ih x hfirst hj
        exact ⟨j, Nat.lt_trans hjJ (Nat.lt_succ_self J), hlow, hupp⟩
      · exact ⟨J, Nat.lt_succ_self J, hlast, le_of_not_gt hj⟩

noncomputable def dyadicPrimeBlock {P : Type*} [Fintype P]
    (a : P → ℕ) (z : ℝ) (j : ℕ) : Finset P := by
  classical
  exact Finset.univ.filter (fun p => dyadicCutoff z (j + 1) < (a p : ℝ) ∧ (a p : ℝ) ≤ dyadicCutoff z j)

theorem mem_dyadicPrimeBlock {P : Type*} [Fintype P]
    (a : P → ℕ) (z : ℝ) (j : ℕ) (p : P) :
    p ∈ dyadicPrimeBlock a z j ↔
      dyadicCutoff z (j + 1) < (a p : ℝ) ∧ (a p : ℝ) ≤ dyadicCutoff z j := by
  classical
  simp [dyadicPrimeBlock]

theorem dyadicPrimeBlocks_disjoint {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) {z : ℝ} (hz : 1 ≤ z) :
    Pairwise (fun i j => Disjoint (dyadicPrimeBlock a z i) (dyadicPrimeBlock a z j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hi := (mem_dyadicPrimeBlock a z i p).mp hpi
  have hj := (mem_dyadicPrimeBlock a z j p).mp hpj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hcut := dyadicCutoff_antitone hz (Nat.succ_le_of_lt hlt)
    linarith
  · have hcut := dyadicCutoff_antitone hz (Nat.succ_le_of_lt hgt)
    linarith

theorem dyadicPrimeBlocks_cover {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hprime : ∀ p, (a p).Prime) (z : ℝ) (hmax : ∀ p, (a p : ℝ) ≤ z)
    (J : ℕ) (hlast : dyadicCutoff z J < 2) :
    Finset.univ.biUnion (fun j : Fin J => dyadicPrimeBlock a z j.val) = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro p
  have hp2 : (2 : ℝ) ≤ a p := by exact_mod_cast (hprime p).two_le
  obtain ⟨j, hj, hlow, hupp⟩ := exists_cutoff_interval (dyadicCutoff z) J (a p)
    (hmax p) (hlast.trans_le hp2)
  exact Finset.mem_biUnion.mpr
    ⟨⟨j, hj⟩, Finset.mem_univ _, (mem_dyadicPrimeBlock a z j p).mpr ⟨hlow, hupp⟩⟩

theorem dyadicPrimeBlock_mass_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    {z : ℝ} (hz : 1 ≤ z) (C : ℝ)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (j : ℕ) : (∑ p ∈ dyadicPrimeBlock a z j, (1 : ℝ) / a p) ≤ C := by
  let block := dyadicPrimeBlock a z j
  have hlow (p : block) : dyadicCutoff z (j + 1) < (a p : ℝ) :=
    ((mem_dyadicPrimeBlock a z j p).mp p.property).1
  have hupp (p : block) : (a p : ℝ) ≤ dyadicCutoff z j :=
    ((mem_dyadicPrimeBlock a z j p).mp p.property).2
  have h := prime_interval_mass_le (fun p : block => a p)
    (fun p q hpq => Subtype.ext (hinj hpq)) (fun p => hprime p)
    (dyadicCutoff_antitone hz (Nat.le_succ j)) hlow hupp
  have hbound := h.trans (hC (dyadicCutoff z j))
  have hsum : (∑ p : block, (1 : ℝ) / a p) = ∑ p ∈ block, (1 : ℝ) / a p :=
    Finset.sum_coe_sort block (fun p => (1 : ℝ) / a p)
  rw [hsum] at hbound
  exact hbound

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem floor_dyadicCutoff_pos {z : ℝ} (hz : 1 ≤ z) (j : ℕ) :
    1 ≤ ⌊dyadicCutoff z j⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using one_le_dyadicCutoff hz j)

theorem log_floor_dyadicCutoff_le {z : ℝ} (hz : 1 ≤ z) (j : ℕ) :
    Real.log (⌊dyadicCutoff z j⌋₊ : ℝ) ≤ (1 / 2 : ℝ) ^ j * Real.log z := by
  have hfloor : (0 : ℝ) < ⌊dyadicCutoff z j⌋₊ := by
    exact_mod_cast (by have := floor_dyadicCutoff_pos hz j; omega : 0 < ⌊dyadicCutoff z j⌋₊)
  have hle := Real.log_le_log hfloor (Nat.floor_le (by have := one_le_dyadicCutoff hz j; linarith))
  simpa only [log_dyadicCutoff hz j] using hle


theorem dyadic_error_product_le {z : ℝ} (hz : 1 ≤ z) (L J : ℕ) :
    (∏ j : Fin J, (⌊dyadicCutoff z j.val⌋₊ : ℝ) ^ (4 * (L + j.val))) ≤
      z ^ (8 * L + 8) := by
  have hbasepos (j : Fin J) : (0 : ℝ) < ⌊dyadicCutoff z j.val⌋₊ := by
    exact_mod_cast (by have := floor_dyadicCutoff_pos hz j.val; omega : 0 < ⌊dyadicCutoff z j.val⌋₊)
  have hprodpos : 0 < ∏ j : Fin J, (⌊dyadicCutoff z j.val⌋₊ : ℝ) ^ (4 * (L + j.val)) :=
    Finset.prod_pos (fun j _ => pow_pos (hbasepos j) _)
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hzlog : 0 ≤ Real.log z := Real.log_nonneg hz
  apply (Real.log_le_log_iff hprodpos (pow_pos hzpos _)).mp
  rw [Real.log_prod (fun j _ => ne_of_gt (pow_pos (hbasepos j) _)), Real.log_pow]
  have hbudget : (∑ j : Fin J, (2 * (L + j.val) : ℝ) / 2 ^ j.val) ≤ 4 * L + 4 := by
    simpa only [Finset.sum_range] using block_degree_budget L J
  calc
    _ = ∑ j : Fin J, (4 * (L + j.val) : ℝ) * Real.log (⌊dyadicCutoff z j.val⌋₊ : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_pow]
      push_cast
      rfl
    _ ≤ ∑ j : Fin J, (4 * (L + j.val) : ℝ) * ((1 / 2 : ℝ) ^ j.val * Real.log z) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (log_floor_dyadicCutoff_le hz j.val) (by positivity)
    _ = 2 * (∑ j : Fin J, (2 * (L + j.val) : ℝ) / 2 ^ j.val) * Real.log z := by
      simp only [Finset.mul_sum, Finset.sum_mul, one_div_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * (4 * L + 4) * Real.log z := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (by norm_num)) hzlog
    _ = (8 * L + 8 : ℕ) * Real.log z := by push_cast; ring

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem dyadic_first_moment_lower {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hz : 1 ≤ z) (hmax : ∀ p, (a p : ℝ) ≤ z)
    (J L : ℕ) (hL : 1 ≤ L) (hcover : dyadicCutoff z J < 2)
    (C : ℝ)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1)
    (S N : ℕ) :
    (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N *
        (∏ p : P, (1 - (1 : ℝ) / a p)) -
      (2 * (J : ℝ) + 1) * z ^ (8 * L + 8) ≤
      ∑ n ∈ Finset.range N, eventProduct
        (fun p n => ¬ residueEvent a (fun p => smallResidues (a p)) S p n) Finset.univ n := by
  let blocks (j : Fin J) := dyadicPrimeBlock a z j.val
  let B (j : Fin J) := ⌊dyadicCutoff z j.val⌋₊
  have hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)) := by
    intro i j hij
    exact dyadicPrimeBlocks_disjoint a hz (fun h => hij (Fin.ext h))
  have hB (j : Fin J) : 1 ≤ B j := floor_dyadicCutoff_pos hz j.val
  have hbound (j : Fin J) (p : P) (hp : p ∈ blocks j) : a p ≤ B j :=
    Nat.le_floor ((mem_dyadicPrimeBlock a z j.val p).mp hp).2
  have hmass (j : Fin J) : (∑ p ∈ blocks j, (1 : ℝ) / a p) ≤ C :=
    dyadicPrimeBlock_mass_le a hinj hprime hz C hC j.val
  have h := prime_block_first_moment_lower a hinj hprime J L hL blocks B
    hdisjoint hB hbound C hmass hsmall S N
  have hcover' : Finset.univ.biUnion blocks = Finset.univ :=
    dyadicPrimeBlocks_cover a hprime z hmax J hcover
  rw [hcover'] at h
  have herror : (∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val))) ≤ z ^ (8 * L + 8) :=
    dyadic_error_product_le hz L J
  have hscaled := mul_le_mul_of_nonneg_left herror
    (by positivity : 0 ≤ 2 * (J : ℝ) + 1)
  calc
    _ ≤ (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N *
        (∏ p : P, (1 - (1 : ℝ) / a p)) -
      (2 * (J : ℝ) + 1) * (∏ j : Fin J, (B j : ℝ) ^ (4 * (L + j.val))) :=
      sub_le_sub_left hscaled _
    _ ≤ _ := h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676


theorem translated_count_le (U E : Finset ℕ) (j : ℕ) :
    (U.filter fun n => n + j ∈ E).card ≤ E.card := by
  apply Finset.card_le_card_of_injOn (fun n => n + j)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n _ m _ h
    exact Nat.add_right_cancel h


theorem translated_sum_le (U E : Finset ℕ) (H : ℕ) :
    (∑ n ∈ U, ∑ j ∈ Finset.range H, if n + j ∈ E then 1 else 0) ≤ H * E.card := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ j ∈ Finset.range H, (U.filter fun n => n + j ∈ E).card := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ ≤ ∑ _j ∈ Finset.range H, E.card :=
      Finset.sum_le_sum fun j _ => translated_count_le U E j
    _ = H * E.card := by simp

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

def SmallAvoidance (z n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ z → p ≤ n % p ^ 2

def LargeAvoidance (z n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → z < p → p ^ 2 ≤ n → p ≤ n % p ^ 2

theorem exceptional_of_small_large {z n : ℕ}
    (hs : SmallAvoidance z n) (hl : LargeAvoidance z n) : Exceptional n := by
  apply (exceptional_iff_mod n).mpr
  intro p hp hpn
  rcases le_or_gt p z with h | h
  · exact hs p hp h
  · exact hl p hp h hpn

noncomputable def smallAverage (z H n : ℕ) : ℝ := by
  classical
  exact (∑ j ∈ Finset.range H, if SmallAvoidance z (n + j) then 1 else 0) / (H : ℝ)

theorem smallAverage_nonneg (z H n : ℕ) : 0 ≤ smallAverage z H n := by
  classical
  unfold smallAverage
  exact div_nonneg (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num)
    (Nat.cast_nonneg _)


theorem smallAverage_mass_le_exceptions (U E : Finset ℕ) (z H : ℕ) (hH : 0 < H)
    (hlarge : ∀ n ∈ U, ∀ j < H, LargeAvoidance z (n + j))
    (hmem : ∀ n ∈ U, ∀ j < H, Exceptional (n + j) → n + j ∈ E) :
    (∑ n ∈ U, smallAverage z H n) ≤ E.card := by
  classical
  have hsupport :
      (∑ n ∈ U, ∑ j ∈ Finset.range H,
        if SmallAvoidance z (n + j) then (1 : ℕ) else 0) ≤ H * E.card := by
    apply le_trans ?_ (translated_sum_le U E H)
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro j hj
    by_cases hs : SmallAvoidance z (n + j)
    · have he := hmem n hn j (Finset.mem_range.mp hj)
        (exceptional_of_small_large hs (hlarge n hn j (Finset.mem_range.mp hj)))
      simp [hs, he]
    · simp [hs]
  have hcast :
      (∑ n ∈ U, ∑ j ∈ Finset.range H,
        if SmallAvoidance z (n + j) then (1 : ℝ) else 0) ≤ (H : ℝ) * E.card := by
    exact_mod_cast hsupport
  have hHreal : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  simp only [smallAverage, ← Finset.sum_div]
  exact (div_le_iff₀ hHreal).mpr (by simpa [mul_comm] using hcast)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def smallPrimeCount (z S N : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.range N, if SmallAvoidance z (S + n) then 1 else 0

theorem smallAvoidance_iff_prime_family (z : ℝ) (n : ℕ) :
    SmallAvoidance ⌊z⌋₊ n ↔
      ∀ p : primesUpToReal z, ¬ (n : ZMod (p.val ^ 2)) ∈ smallResidues p.val := by
  constructor
  · intro hs p hmem
    have hp := (Finset.mem_filter.mp p.property).2
    have hple := (Finset.mem_Ioc.mp (Finset.mem_filter.mp p.property).1).2
    have hlarge := hs p hp hple
    exact (Nat.not_lt.mpr hlarge) ((mem_smallResidues p n hp.one_lt.le).mp hmem)
  · intro hs p hp hple
    have hmem : p ∈ primesUpToReal z :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, hple⟩, hp⟩
    apply Nat.le_of_not_gt
    intro hsmall
    exact hs ⟨p, hmem⟩ ((mem_smallResidues p n hp.one_lt.le).mpr hsmall)

theorem smallPrimeCount_eq_family (z : ℝ) (S N : ℕ) :
    smallPrimeCount ⌊z⌋₊ S N =
      ∑ n ∈ Finset.range N, eventProduct
        (fun (p : primesUpToReal z) n => ¬ residueEvent (fun p => p.val)
          (fun p => smallResidues p.val) S p n) Finset.univ n := by
  classical
  unfold smallPrimeCount
  apply Finset.sum_congr rfl
  intro n hn
  have hiff : (∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
      ¬ residueEvent (fun p => p.val) (fun p => smallResidues p.val) S p n) ↔
        SmallAvoidance ⌊z⌋₊ (S + n) := by
    simp only [Finset.mem_univ, forall_true_left, residueEvent]
    exact (smallAvoidance_iff_prime_family z (S + n)).symm
  by_cases hs : SmallAvoidance ⌊z⌋₊ (S + n)
  · have hq := hiff.mpr hs
    simpa [eventProduct, hs] using hq
  · have hq : ¬ ∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
        ¬ residueEvent (fun p => p.val) (fun p => smallResidues p.val) S p n :=
      fun h => hs (hiff.mp h)
    simpa [eventProduct, hs] using hq

theorem smallPrimeCount_finite_lower (z : ℝ) (hz : 1 ≤ z)
    (J L : ℕ) (hL : 1 ≤ L) (hcover : dyadicCutoff z J < 2)
    (C : ℝ)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) (S N : ℕ) :
    (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N * survivalProduct z -
      (2 * (J : ℝ) + 1) * z ^ (8 * L + 8) ≤ smallPrimeCount ⌊z⌋₊ S N := by
  let P := primesUpToReal z
  have hprime (p : P) : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hmax (p : P) : (p.val : ℝ) ≤ z := ((mem_primesUpToReal z p.val).mp p.property).2
  have h := dyadic_first_moment_lower (fun p : P => p.val) Subtype.val_injective hprime
    z hz hmax J L hL hcover C hC hsmall S N
  have hprod : (∏ p : P, (1 - (1 : ℝ) / p.val)) = survivalProduct z :=
    Finset.prod_coe_sort P (fun p : ℕ => 1 - (1 : ℝ) / p)
  rw [hprod, ← smallPrimeCount_eq_family] at h
  exact h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def smallPairCount (z S N i j : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.range N,
    if SmallAvoidance z (S + n + i) ∧ SmallAvoidance z (S + n + j) then 1 else 0

noncomputable def pairSurvivalProduct (z : ℝ) (k : ℤ) : ℝ :=
  ∏ p ∈ primesUpToReal z, (1 - twoPositionDensity p (k : ZMod (p ^ 2)))

theorem pair_residue_membership (p S n i j : ℕ) :
    (((S + i + n : ℕ) : ZMod (p ^ 2)) ∈
      twoPositionResidues p (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p ^ 2))) ↔
        ((S + n + i : ℕ) : ZMod (p ^ 2)) ∈ smallResidues p ∨
        ((S + n + j : ℕ) : ZMod (p ^ 2)) ∈ smallResidues p := by
  have hfirst : ((S + i + n : ℕ) : ZMod (p ^ 2)) = ((S + n + i : ℕ) : ZMod (p ^ 2)) := by
    congr 1
    omega
  have hsecond : ((S + i + n : ℕ) : ZMod (p ^ 2)) + (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p ^ 2)) =
      ((S + n + j : ℕ) : ZMod (p ^ 2)) := by
    push_cast
    ring
  rw [twoPositionResidues, Finset.mem_union, mem_translatedBack, hsecond, hfirst]

theorem smallPairCount_eq_family (z : ℝ) (S N i j : ℕ) :
    smallPairCount ⌊z⌋₊ S N i j =
      ∑ n ∈ Finset.range N, eventProduct
        (fun (p : primesUpToReal z) n => ¬ residueEvent (fun p => p.val)
          (fun p => twoPositionResidues p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2)))
          (S + i) p n) Finset.univ n := by
  classical
  unfold smallPairCount
  apply Finset.sum_congr rfl
  intro n hn
  have hiff : (∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
      ¬ residueEvent (fun p => p.val)
        (fun p => twoPositionResidues p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2))) (S + i) p n) ↔
      SmallAvoidance ⌊z⌋₊ (S + n + i) ∧ SmallAvoidance ⌊z⌋₊ (S + n + j) := by
    simp only [Finset.mem_univ, forall_true_left, residueEvent, pair_residue_membership, not_or]
    rw [forall_and]
    exact and_congr (smallAvoidance_iff_prime_family z (S + n + i)).symm
      (smallAvoidance_iff_prime_family z (S + n + j)).symm
  by_cases hs : SmallAvoidance ⌊z⌋₊ (S + n + i) ∧ SmallAvoidance ⌊z⌋₊ (S + n + j)
  · have hq := hiff.mpr hs
    simpa [eventProduct, hs] using hq
  · have hq : ¬ ∀ p ∈ (Finset.univ : Finset (primesUpToReal z)),
        ¬ residueEvent (fun p => p.val)
          (fun p => twoPositionResidues p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2))) (S + i) p n :=
      fun h => hs (hiff.mp h)
    simpa [eventProduct, hs] using hq

theorem smallPairCount_sieve_bound (z : ℝ) (hz : 2 ≤ z) (R S N i j : ℕ)
    (hR : 2 ≤ R) (hlarge : Real.log 4 + 4 ≤ Real.log z)
    (hsmall : 20 * (Real.log z) ^ 2 ≤ (Real.log R) ^ 2 / 2) :
    smallPairCount ⌊z⌋₊ S N i j ≤
      (1 + 40 * (Real.log z / Real.log R) ^ 2) * N * pairSurvivalProduct z ((j : ℤ) - i) +
        (R : ℝ) ^ 8 := by
  let P := primesUpToReal z
  have hprime (p : P) : p.val.Prime := (Finset.mem_filter.mp p.property).2
  have hmax (p : P) : (p.val : ℝ) ≤ z := ((mem_primesUpToReal z p.val).mp p.property).2
  have h := two_shift_sieve_upper (fun p : P => p.val) Subtype.val_injective hprime
    ((j : ℤ) - i) R (S + i) N hR z hz hmax hlarge hsmall
  have hprod : (∏ p : P, (1 - twoPositionDensity p.val (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p.val ^ 2)))) =
      pairSurvivalProduct z ((j : ℤ) - i) := by
    unfold pairSurvivalProduct
    exact Finset.prod_coe_sort P (fun p : ℕ => 1 - twoPositionDensity p (Int.cast ((j : ℤ) - (i : ℤ)) : ZMod (p ^ 2)))
  rw [hprod, ← smallPairCount_eq_family] at h
  exact h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def localSingularFactor (p : ℕ) (k : ZMod (p ^ 2)) : ℝ :=
  normalizedFactor p (overlap (smallResidues p) k)

noncomputable def localSingularExcess (p : ℕ) (k : ZMod (p ^ 2)) : ℝ :=
  max (localSingularFactor p k - 1) 0

noncomputable def singularFactorProduct (z : ℝ) (k : ℤ) : ℝ :=
  ∏ p ∈ primesUpToReal z, localSingularFactor p (k : ZMod (p ^ 2))

theorem localSingularFactor_nonneg (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    0 ≤ localSingularFactor p k :=
  normalizedFactor_nonneg (by exact_mod_cast hp) (Nat.cast_nonneg _)

theorem localSingularFactor_le (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    localSingularFactor p k ≤ (p : ℝ) / (p - 1) := by
  apply normalizedFactor_le (by exact_mod_cast hp)
  have h := overlap_le_card (smallResidues p) k
  rw [smallResidues_card p (by omega)] at h
  exact_mod_cast h

theorem localSingularExcess_le_overlap (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    localSingularExcess p k ≤ (overlap (smallResidues p) k : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  unfold localSingularExcess localSingularFactor normalizedFactor
  apply max_le
  · have h := div_le_div_of_nonneg_right
      (by linarith : (overlap (smallResidues p) k : ℝ) - 1 ≤ overlap (smallResidues p) k) hden.le
    linarith
  · exact div_nonneg (Nat.cast_nonneg _) hden.le

theorem one_add_localSingularExcess_le (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    1 + localSingularExcess p k ≤ (p : ℝ) / (p - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hone : (1 : ℝ) ≤ (p : ℝ) / (p - 1) := (le_div_iff₀ hp1).mpr (by linarith)
  have hfactor := localSingularFactor_le p hp k
  unfold localSingularExcess
  rw [add_max]
  apply max_le <;> linarith

theorem localSingularFactor_identity (p : ℕ) (hp : 2 ≤ p) (k : ZMod (p ^ 2)) :
    1 - twoPositionDensity p k = (1 - (1 : ℝ) / p) ^ 2 * localSingularFactor p k := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [twoPositionDensity_formula p (by omega)]
  unfold localSingularFactor normalizedFactor
  field_simp
  ring

theorem pairSurvivalProduct_factorization (z : ℝ) (k : ℤ) :
    pairSurvivalProduct z k = (survivalProduct z) ^ 2 * singularFactorProduct z k := by
  unfold pairSurvivalProduct survivalProduct singularFactorProduct
  calc
    _ = ∏ p ∈ primesUpToReal z, (1 - (1 : ℝ) / p) ^ 2 * localSingularFactor p (k : ZMod (p ^ 2)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact localSingularFactor_identity p (Finset.mem_filter.mp hp).2.two_le _
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow]

theorem localSingularExcess_sum_le (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    (∑ k : ZMod (p ^ 2), localSingularExcess p k) ≤ (p : ℝ) ^ 2 / ((p : ℝ) - 1) ^ 2 := by
  calc
    _ ≤ ∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ) / ((p : ℝ) - 1) ^ 2 :=
      Finset.sum_le_sum (fun k _ => localSingularExcess_le_overlap p hp k)
    _ = _ := by
      rw [← Finset.sum_div]
      have hsum : (∑ k : ZMod (p ^ 2), (overlap (smallResidues p) k : ℝ)) = (p : ℝ) ^ 2 := by
        exact_mod_cast (by simpa only [smallResidues_card p (by omega)] using sum_overlap (smallResidues p))
      rw [hsum]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem shifted_reciprocal_square_le (p : ℕ) (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ^ 2 ≤ 4 * ((p : ℝ) ^ 2)⁻¹ := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (sq_pos_of_pos hp1) (sq_pos_of_pos hp0)).mpr
  nlinarith

theorem shifted_reciprocal_square_tail (s : Finset ℕ) (m n : ℕ)
    (hm : 1 ≤ m) (hn : m ≤ n) (hs : s ⊆ Finset.Ioc m n) :
    (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤ (4 : ℝ) / (m : ℝ) := by
  have hsum : (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤
      4 * ∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    exact shifted_reciprocal_square_le p (by have := (Finset.mem_Ioc.mp (hs hp)).1; omega)
  have hsub : (∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹) ≤ ∑ p ∈ Finset.Ioc m n, ((p : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0) hn
  have hinv : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hupper : (∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by linarith
  simpa only [div_eq_mul_inv] using hsum.trans (mul_le_mul_of_nonneg_left hupper (by norm_num))

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem nat_shifted_square_kernel_sum (s : Finset ℕ) :
    (∑ n ∈ s, ((1 + (n : ℝ)) ^ 2)⁻¹) ≤ 2 := by
  classical
  let N := s.sup id + 2
  have hsub : s.image Nat.succ ⊆ Finset.Ioo 0 N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hle : k ≤ s.sup id := Finset.le_sup (f := id) hk
    exact Finset.mem_Ioo.mpr ⟨by omega, by dsimp [N]; omega⟩
  have hsum : (∑ n ∈ s, ((1 + (n : ℝ)) ^ 2)⁻¹) =
      ∑ n ∈ s.image Nat.succ, ((n : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      simp only [Nat.cast_succ, add_comm]
    · intro a ha b hb hab
      exact Nat.succ_injective hab
  rw [hsum]
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => by positivity : ∀ n, n ∈ Finset.Ioo 0 N → n ∉ s.image Nat.succ → 0 ≤ ((n : ℝ) ^ 2)⁻¹)
  have htail := sum_Ioo_inv_sq_le (α := ℝ) 0 N
  norm_num only [Nat.cast_zero, zero_add, div_one] at htail
  exact hbound.trans htail

theorem signed_square_kernel_sum (s : Finset ℤ)
    (hs : (∀ n ∈ s, 0 ≤ n) ∨ (∀ n ∈ s, n ≤ 0)) :
    (∑ n ∈ s, ((1 + |(n : ℝ)|) ^ 2)⁻¹) ≤ 2 := by
  classical
  have hinj : Set.InjOn Int.natAbs (s : Set ℤ) := by
    intro a ha b hb heq
    rcases Int.natAbs_eq_natAbs_iff.mp heq with h | h
    · exact h
    · rcases hs with hs | hs <;> have ha' := hs a ha <;> have hb' := hs b hb <;> omega
  have hsum : (∑ n ∈ s, ((1 + |(n : ℝ)|) ^ 2)⁻¹) =
      ∑ n ∈ s.image Int.natAbs, ((1 + (n : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hsum]
  exact nat_shifted_square_kernel_sum _

theorem integer_square_kernel_sum (s : Finset ℤ) :
    (∑ n ∈ s, ((1 + |(n : ℝ)|) ^ 2)⁻¹) ≤ 4 := by
  classical
  have hpos := signed_square_kernel_sum (s.filter (fun n => 0 ≤ n))
    (Or.inl (fun n hn => (Finset.mem_filter.mp hn).2))
  have hneg := signed_square_kernel_sum (s.filter (fun n => ¬0 ≤ n))
    (Or.inr (fun n hn => (le_of_not_ge (Finset.mem_filter.mp hn).2)))
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun n : ℤ => 0 ≤ n)
    (fun n => ((1 + |(n : ℝ)|) ^ 2)⁻¹)
  linarith

theorem indexed_integer_kernel_sum {P : Type*} (s : Finset P) (g : P → ℤ)
    (hinj : Set.InjOn g (s : Set P)) :
    (∑ i ∈ s, ((1 + |(g i : ℝ)|) ^ 2)⁻¹) ≤ 4 := by
  classical
  have heq : (∑ n ∈ s.image g, ((1 + |(n : ℝ)|) ^ 2)⁻¹) =
      ∑ i ∈ s, ((1 + |(g i : ℝ)|) ^ 2)⁻¹ := Finset.sum_image hinj
  rw [← heq]
  exact integer_square_kernel_sum _

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem floor_abs_le_abs_add_one (x : ℝ) : |(⌊x⌋ : ℝ)| ≤ |x| + 1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  exact abs_le.mpr ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

theorem inverse_square_floor_kernel (x : ℝ) :
    ((1 + |x|) ^ 2)⁻¹ ≤ 4 * ((1 + |(⌊x⌋ : ℝ)|) ^ 2)⁻¹ := by
  have hx : 0 < 1 + |x| := by positivity
  have hm : 0 < 1 + |(⌊x⌋ : ℝ)| := by positivity
  have hle : 1 + |(⌊x⌋ : ℝ)| ≤ 2 * (1 + |x|) := by
    linarith [floor_abs_le_abs_add_one x, abs_nonneg x]
  have hsq := pow_le_pow_left₀ hm.le hle 2
  simp only [← one_div, mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hx) (sq_pos_of_pos hm)).mpr
  nlinarith

theorem separated_floor_injective {P : Type*} (s : Finset P) (θ : P → ℝ) (L base : ℝ)
    (hL : 0 < L) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ L * |θ i - θ j|) :
    Set.InjOn (fun i => (⌊L * (θ i - base)⌋ : ℤ)) (s : Set P) := by
  intro i hi j hj heq
  change (⌊L * (θ i - base)⌋ : ℤ) = ⌊L * (θ j - base)⌋ at heq
  by_contra hij
  have hsep' := hsep i hi j hj hij
  have hlowi := Int.floor_le (L * (θ i - base))
  have hlowj := Int.floor_le (L * (θ j - base))
  have hupi := Int.lt_floor_add_one (L * (θ i - base))
  have hupj := Int.lt_floor_add_one (L * (θ j - base))
  rw [heq] at hlowi hupi
  have habs : |L * (θ i - θ j)| < 1 := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  rw [abs_mul, abs_of_pos hL] at habs
  linarith

theorem separated_square_kernel_sum {P : Type*} (s : Finset P) (θ : P → ℝ) (L base : ℝ)
    (hL : 0 < L) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ L * |θ i - θ j|) :
    (∑ i ∈ s, ((1 + L * |θ i - base|) ^ 2)⁻¹) ≤ 16 := by
  have hinj := separated_floor_injective s θ L base hL hsep
  have hsum := indexed_integer_kernel_sum s (fun i => (⌊L * (θ i - base)⌋ : ℤ)) hinj
  have hpoint (i : P) : ((1 + L * |θ i - base|) ^ 2)⁻¹ ≤
      4 * ((1 + |((⌊L * (θ i - base)⌋ : ℤ) : ℝ)|) ^ 2)⁻¹ := by
    have h := inverse_square_floor_kernel (L * (θ i - base))
    simpa only [abs_mul, abs_of_pos hL] using h
  have hbound := Finset.sum_le_sum (fun i (_ : i ∈ s) => hpoint i)
  rw [← Finset.mul_sum] at hbound
  linarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem pair_sample_sum {R : Type*} [AddCommMonoid R] (L : ℕ) (F : ℤ → R) :
    (∑ t : Fin L × Fin L, F ((t.1.val : ℤ) - t.2.val)) =
      ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, F ((a : ℤ) - b) := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ a : Fin L, ∑ b ∈ Finset.range L, F ((a.val : ℤ) - b) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Finset.sum_range (fun b => F ((a.val : ℤ) - b))).symm
    _ = _ := (Finset.sum_range (fun a => ∑ b ∈ Finset.range L, F ((a : ℤ) - b))).symm

theorem separated_pair_sampling_bound {P : Type*} (s : Finset P) (θ : P → ℝ)
    (c : P → ℂ) (L : ℕ) (hL : 0 < L)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (L : ℝ) * |θ i - θ j|)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2) :
    (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
      ‖∑ i ∈ s, c i * realCharacter (θ i) ((a : ℤ) - b)‖ ^ 2) ≤
        64 * (L : ℝ) ^ 2 * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  let f (i : P) (t : Fin L × Fin L) := realCharacter (θ i) ((t.1.val : ℤ) - t.2.val)
  have hpair (i j : P) : (∑ t : Fin L × Fin L, star (f i t) * f j t) =
      ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
        realCharacter (θ j - θ i) ((a : ℤ) - b) := by
    simp only [f, realCharacter_difference]
    exact pair_sample_sum L _
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hrow : ∀ i ∈ s, (∑ j ∈ s, ‖∑ t : Fin L × Fin L, star (f i t) * f j t‖) ≤
      64 * (L : ℝ) ^ 2 := by
    intro i hi
    have hsum := separated_square_kernel_sum s θ L (θ i) hLreal hsep
    have hbound : (∑ j ∈ s, ‖∑ t : Fin L × Fin L, star (f i t) * f j t‖) ≤
        4 * (L : ℝ) ^ 2 * ∑ j ∈ s, ((1 + L * |θ j - θ i|) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [hpair]
      simpa only [div_eq_mul_inv] using real_pair_kernel_bound L hL (θ j - θ i) (hdiam j hj i hi)
    have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * (L : ℝ) ^ 2 by positivity)
    nlinarith
  have h := sampling_gram_bound s f c (64 * (L : ℝ) ^ 2) hrow
  have htotal := pair_sample_sum L (fun n => ‖∑ i ∈ s, c i * realCharacter (θ i) n‖ ^ 2)
  change (∑ t : Fin L × Fin L, ‖∑ i ∈ s, c i * realCharacter (θ i) ((t.1.val : ℤ) - t.2.val)‖ ^ 2) ≤ _ at h
  rwa [htotal] at h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem interval_sum_le_pair_sum (N : ℕ) (F : ℤ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (N : ℝ) * (∑ n ∈ Finset.range N, F n) ≤
      ∑ a ∈ Finset.range (2 * N), ∑ b ∈ Finset.range (2 * N), F ((a : ℤ) - b) := by
  classical
  let small := (Finset.range N).product (Finset.range N)
  let large := (Finset.range (2 * N)).product (Finset.range (2 * N))
  let embed (t : ℕ × ℕ) : ℕ × ℕ := (t.1 + t.2, t.2)
  have hinj : Function.Injective embed := by
    intro a b h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    dsimp [embed] at hfst hsnd
    apply Prod.ext <;> omega
  have hsub : small.image embed ⊆ large := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hu1, hu2⟩ := Finset.mem_product.mp hu
    have h1 := Finset.mem_range.mp hu1
    have h2 := Finset.mem_range.mp hu2
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [embed]; omega),
      Finset.mem_range.mpr (by dsimp [embed]; omega)⟩
  calc
    _ = ∑ t ∈ small, F (t.1 : ℤ) := by
      dsimp [small]
      rw [Finset.sum_product]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.mul_sum]
    _ = ∑ t ∈ small, F (((embed t).1 : ℤ) - (embed t).2) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [embed, Nat.cast_add, add_sub_cancel_right]
    _ = ∑ t ∈ small.image embed, F ((t.1 : ℤ) - t.2) :=
      by
        symm
        exact Finset.sum_image (fun a ha b hb h => hinj h)
    _ ≤ ∑ t ∈ large, F ((t.1 : ℤ) - t.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => hF _)
    _ = _ := by dsimp [large]; rw [Finset.sum_product]

theorem separated_interval_sampling_bound {P : Type*} (s : Finset P) (θ : P → ℝ)
    (c : P → ℂ) (N : ℕ) (hN : 0 < N)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (2 * N : ℕ) * |θ i - θ j|)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2) :
    (∑ n ∈ Finset.range N, ‖∑ i ∈ s, c i * realCharacter (θ i) n‖ ^ 2) ≤
      256 * N * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hpair := separated_pair_sampling_bound s θ c (2 * N) (by omega) hsep hdiam
  have hmajor := interval_sum_le_pair_sum N
    (fun n => ‖∑ i ∈ s, c i * realCharacter (θ i) n‖ ^ 2) (fun n => sq_nonneg _)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound := hmajor.trans hpair
  push_cast at hbound
  nlinarith

theorem separated_translated_sampling_bound {P : Type*} (s : Finset P) (θ : P → ℝ)
    (c : P → ℂ) (S : ℤ) (N : ℕ) (hN : 0 < N)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (2 * N : ℕ) * |θ i - θ j|)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2) :
    (∑ n ∈ Finset.range N, ‖∑ i ∈ s, c i * realCharacter (θ i) (S + n)‖ ^ 2) ≤
      256 * N * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have h := separated_interval_sampling_bound s θ (fun i => c i * realCharacter (θ i) S) N hN hsep hdiam
  have hfun (n : ℕ) : (∑ i ∈ s, c i * realCharacter (θ i) (S + n)) =
      ∑ i ∈ s, (c i * realCharacter (θ i) S) * realCharacter (θ i) n := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [AddChar.map_add_eq_mul]
    ring
  simpa only [hfun, norm_mul, realCharacter_norm, mul_one] using h

end Erdos676
end

section
namespace Erdos676

theorem prime_frequency_cross_ne (p q : ℕ) (a b : ℤ)
    (hp : p.Prime) (hq : q.Prime) (ha : a ≠ 0) (habound : a.natAbs < p)
    (hpair : ¬(p = q ∧ a = b)) : a * (q : ℤ) ^ 2 ≠ b * (p : ℤ) ^ 2 := by
  intro heq
  by_cases hpq : p = q
  · subst q
    have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne_zero)
    exact hpair ⟨rfl, mul_right_cancel₀ hp0 heq⟩
  · have hdiv : (p : ℤ) ∣ a * (q : ℤ) ^ 2 := by
      rw [heq]
      refine ⟨b * p, ?_⟩
      ring
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdiv with hpa | hpqdiv
    · have ha0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hpa
        (by simpa only [Int.natAbs_natCast] using habound)
      exact ha ha0
    · have hpqdiv' : (p : ℤ) ∣ (q : ℤ) := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpqdiv
      have hpqN : p ∣ q := Int.natCast_dvd_natCast.mp hpqdiv'
      rcases (Nat.dvd_prime hq).mp hpqN with hp1 | hpq'
      · exact hp.ne_one hp1
      · exact hpq hpq'

theorem integer_fraction_separation (p q : ℕ) (a b : ℤ)
    (hp : 0 < p) (hq : 0 < q)
    (hcross : a * (q : ℤ) ^ 2 ≠ b * (p : ℤ) ^ 2) :
    1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) ≤
      |(a : ℝ) / (p : ℝ) ^ 2 - (b : ℝ) / (q : ℝ) ^ 2| := by
  let d : ℤ := a * (q : ℤ) ^ 2 - b * (p : ℤ) ^ 2
  have hd : d ≠ 0 := sub_ne_zero.mpr hcross
  have hnat : 1 ≤ d.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hd)
  have habsInt : (1 : ℤ) ≤ |d| := by
    simpa only [Int.natCast_natAbs] using (show (1 : ℤ) ≤ d.natAbs by exact_mod_cast hnat)
  have habs : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast habsInt
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hden : 0 < (p : ℝ) ^ 2 * (q : ℝ) ^ 2 := mul_pos (sq_pos_of_ne_zero hp0) (sq_pos_of_ne_zero hq0)
  have hid : (a : ℝ) / (p : ℝ) ^ 2 - (b : ℝ) / (q : ℝ) ^ 2 =
      (d : ℝ) / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
    dsimp [d]
    push_cast
    field_simp
    <;> ring
  rw [hid, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right habs hden.le

theorem prime_frequency_separation (p q : ℕ) (a b : ℤ)
    (hp : p.Prime) (hq : q.Prime) (ha : a ≠ 0) (habound : a.natAbs < p)
    (hpair : ¬(p = q ∧ a = b)) :
    1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) ≤
      |(a : ℝ) / (p : ℝ) ^ 2 - (b : ℝ) / (q : ℝ) ^ 2| :=
  integer_fraction_separation p q a b hp.pos hq.pos
    (prime_frequency_cross_ne p q a b hp hq ha habound hpair)

theorem prime_frequency_abs_le_quarter (p : ℕ) (a : ℤ) (hp : 2 ≤ p) (ha : a.natAbs < p) :
    |(a : ℝ) / (p : ℝ) ^ 2| ≤ 1 / 4 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hboundInt : |a| ≤ (p : ℤ) - 1 := by
    have h := (show (a.natAbs : ℤ) < p by exact_mod_cast ha)
    rw [Int.natCast_natAbs] at h
    omega
  have hbound : |(a : ℝ)| ≤ (p : ℝ) - 1 := by exact_mod_cast hboundInt
  have hpos : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos (by linarith)
  rw [abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_frequency_sampling_bound {P : Type*} (s : Finset P)
    (p : P → ℕ) (k : P → ℤ) (c : P → ℂ) (S : ℤ) (N : ℕ) (hN : 0 < N)
    (hprime : ∀ i ∈ s, (p i).Prime) (hnonzero : ∀ i ∈ s, k i ≠ 0)
    (hsmall : ∀ i ∈ s, (k i).natAbs < p i)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, p i = p j → k i = k j → i = j)
    (hsize : ∀ i ∈ s, ∀ j ∈ s, (p i : ℝ) ^ 2 * (p j : ℝ) ^ 2 ≤ 2 * N) :
    (∑ n ∈ Finset.range N,
      ‖∑ i ∈ s, c i * realCharacter ((k i : ℝ) / (p i : ℝ) ^ 2) (S + n)‖ ^ 2) ≤
        256 * N * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  let θ (i : P) := (k i : ℝ) / (p i : ℝ) ^ 2
  have hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ (2 * N : ℕ) * |θ i - θ j| := by
    intro i hi j hj hij
    have hpair : ¬(p i = p j ∧ k i = k j) := fun h => hij (hinj i hi j hj h.1 h.2)
    have h := prime_frequency_separation (p i) (p j) (k i) (k j)
      (hprime i hi) (hprime j hj) (hnonzero i hi) (hsmall i hi) hpair
    have hden : 0 < (p i : ℝ) ^ 2 * (p j : ℝ) ^ 2 := by
      have hi' : (0 : ℝ) < p i := by exact_mod_cast (hprime i hi).pos
      have hj' : (0 : ℝ) < p j := by exact_mod_cast (hprime j hj).pos
      positivity
    have hmul := (div_le_iff₀ hden).mp h
    have hscaled := mul_le_mul_of_nonneg_right (hsize i hi j hj) (abs_nonneg (θ i - θ j))
    change 1 ≤ ((2 * N : ℕ) : ℝ) * |θ i - θ j|
    push_cast
    dsimp [θ] at hscaled ⊢
    nlinarith
  have hdiam : ∀ i ∈ s, ∀ j ∈ s, |θ i - θ j| ≤ 1 / 2 := by
    intro i hi j hj
    have hi' := prime_frequency_abs_le_quarter (p i) (k i) (hprime i hi).two_le (hsmall i hi)
    have hj' := prime_frequency_abs_le_quarter (p j) (k j) (hprime j hj).two_le (hsmall j hj)
    have h := abs_sub_le (θ i) 0 (θ j)
    simp only [sub_zero, zero_sub, abs_neg] at h
    dsimp [θ] at h
    linarith
  exact separated_translated_sampling_bound s θ c S N hN hsep hdiam

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def retainedFrequencies (m : ℕ) [NeZero m] (D : ℝ) : Finset (ZMod m) :=
  Finset.univ.filter (fun k => k ≠ 0 ∧ |residueFrequency k| ≤ D)

theorem retained_frequency_abs_bound {m : ℕ} [NeZero m] {D : ℝ} (hD : 0 ≤ D)
    {k : ZMod m} (hk : k ∈ retainedFrequencies m D) : k.valMinAbs.natAbs ≤ ⌊(m : ℝ) * D⌋₊ := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hfreq := (Finset.mem_filter.mp hk).2.2
  unfold residueFrequency at hfreq
  rw [abs_div, abs_of_pos hm] at hfreq
  have hmul := (div_le_iff₀ hm).mp hfreq
  apply Nat.le_floor
  have habs : (k.valMinAbs.natAbs : ℝ) = |(k.valMinAbs : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  nlinarith

theorem retainedFrequencies_card_le (m : ℕ) [NeZero m] (D : ℝ) (hD : 0 ≤ D) :
    (retainedFrequencies m D).card ≤ 2 * ⌊(m : ℝ) * D⌋₊ := by
  classical
  let M := ⌊(m : ℝ) * D⌋₊
  let target : Finset ℤ := (Finset.Icc (-(M : ℤ)) M).erase 0
  have hsub : (retainedFrequencies m D).image ZMod.valMinAbs ⊆ target := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have habs := retained_frequency_abs_bound hD hk
    have habs' : |k.valMinAbs| ≤ (M : ℤ) := by
      simpa only [Int.natCast_natAbs] using (show (k.valMinAbs.natAbs : ℤ) ≤ M by exact_mod_cast habs)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_Icc.mpr (abs_le.mp habs')⟩
    exact fun h => (Finset.mem_filter.mp hk).2.1 ((ZMod.valMinAbs_eq_zero k).mp h)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ ZMod.injective_valMinAbs] at hcard
  have htarget : target.card = 2 * M := by
    have hzero : (0 : ℤ) ∈ Finset.Icc (-(M : ℤ)) M := by simp
    rw [show target = (Finset.Icc (-(M : ℤ)) M).erase 0 from rfl,
      Finset.card_erase_of_mem hzero, Int.card_Icc]
    omega
  rwa [htarget] at hcard

theorem retainedFrequencies_card_real_le (m : ℕ) [NeZero m] (D : ℝ) (hD : 0 ≤ D) :
    ((retainedFrequencies m D).card : ℝ) ≤ 2 * m * D := by
  have hcard : ((retainedFrequencies m D).card : ℝ) ≤ 2 * (⌊(m : ℝ) * D⌋₊ : ℝ) :=
    by exact_mod_cast retainedFrequencies_card_le m D hD
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) hD)
  nlinarith

theorem retained_prime_fourier_mass (p : ℕ) (hp : 1 ≤ p) (D : ℝ) (hD : 0 ≤ D) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k ∈ retainedFrequencies (p ^ 2) D, ‖residueFourier (smallResidues p) k‖ ^ 2) ≤ 2 * D := by
  letI : NeZero p := ⟨by omega⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hbound : (∑ k ∈ retainedFrequencies (p ^ 2) D, ‖residueFourier (smallResidues p) k‖ ^ 2) ≤
      ((retainedFrequencies (p ^ 2) D).card : ℝ) * (1 / (p : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ k ∈ retainedFrequencies (p ^ 2) D, (1 / (p : ℝ)) ^ 2 :=
        Finset.sum_le_sum (fun k hk => pow_le_pow_left₀ (norm_nonneg _) (smallResidues_fourier_norm_le p hp k) 2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hcount := retainedFrequencies_card_real_le (p ^ 2) D hD
  rw [Nat.cast_pow] at hcount
  have hscaled := mul_le_mul_of_nonneg_right hcount (sq_nonneg (1 / (p : ℝ)))
  have heq : (2 * (p : ℝ) ^ 2 * D) * (1 / (p : ℝ)) ^ 2 = 2 * D := by field_simp
  exact hbound.trans (by rwa [heq] at hscaled)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem boxMean_sum {P : Type*} (H : ℕ) (s : Finset P) (f : P → ℤ → ℂ) (n : ℤ) :
    boxMean H (fun k => ∑ p ∈ s, f p k) n = ∑ p ∈ s, boxMean H (f p) n := by
  simp only [boxMean, Finset.sum_div]
  rw [Finset.sum_comm]

theorem boxSmooth_const_mul (H J : ℕ) (c : ℂ) (f : ℤ → ℂ) (n : ℤ) :
    boxSmooth H J (fun k => c * f k) n = c * boxSmooth H J f n := by
  induction J generalizing n with
  | zero => rfl
  | succ J ih =>
      change boxMean H (boxSmooth H J (fun k => c * f k)) n = _
      rw [show boxSmooth H J (fun k => c * f k) = (fun k => c * boxSmooth H J f k) from funext ih]
      exact boxMean_const_mul H c _ n

theorem boxSmooth_sum {P : Type*} (H J : ℕ) (s : Finset P) (f : P → ℤ → ℂ) (n : ℤ) :
    boxSmooth H J (fun k => ∑ p ∈ s, f p k) n = ∑ p ∈ s, boxSmooth H J (f p) n := by
  induction J generalizing n with
  | zero => rfl
  | succ J ih =>
      change boxMean H (boxSmooth H J (fun k => ∑ p ∈ s, f p k)) n = _
      rw [show boxSmooth H J (fun k => ∑ p ∈ s, f p k) =
        (fun k => ∑ p ∈ s, boxSmooth H J (f p) k) from funext ih]
      exact boxMean_sum H s _ n

noncomputable def residueFourierPart {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) (n : ℤ) : ℂ :=
  ∑ k ∈ s, residueFourier A k * residueCharacter k n

theorem residueIndicator_fourier {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (n : ℤ) :
    residueIndicator A (n : ZMod m) = residueFourierPart A Finset.univ n :=
  residueFourier_inversion A (n : ZMod m)

theorem smoothed_residueFourierPart {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) (H J : ℕ) (n : ℤ) :
    boxSmooth H J (residueFourierPart A s) n =
      ∑ k ∈ s, residueFourier A k * (boxMultiplier H (residueCharacter k)) ^ J * residueCharacter k n := by
  unfold residueFourierPart
  rw [boxSmooth_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [boxSmooth_const_mul, boxSmooth_character]
  ring

theorem residueFourier_mass_le {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) : (∑ k ∈ s, ‖residueFourier A k‖) ≤ A.card := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hc : (s.card : ℝ) ≤ m := by
    exact_mod_cast (show s.card ≤ m by simpa only [ZMod.card] using Finset.card_le_univ s)
  calc
    _ ≤ ∑ k ∈ s, (A.card : ℝ) / m := Finset.sum_le_sum (fun k hk => residueFourier_norm_le A k)
    _ = (s.card : ℝ) * ((A.card : ℝ) / m) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * ((A.card : ℝ) / m) :=
      mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg _) hm.le)
    _ = _ := by field_simp

theorem smoothed_fourier_tail_bound {m : ℕ} [NeZero m]
    (A s : Finset (ZMod m)) (H J : ℕ) (hH : 0 < H) (D : ℝ) (hD : 0 < D)
    (hs : ∀ k ∈ s, k ≠ 0 ∧ D ≤ |residueFrequency k|) (n : ℤ) :
    ‖boxSmooth H J (residueFourierPart A s) n‖ ≤
      A.card * (1 / ((H : ℝ) * D)) ^ J := by
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hdecay (k : ZMod m) (hk : k ∈ s) :
      ‖boxMultiplier H (residueCharacter k)‖ ^ J ≤ (1 / ((H : ℝ) * D)) ^ J := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (residue_boxMultiplier_decay k (hs k hk).1 H hH).trans
      (one_div_le_one_div_of_le (mul_pos hHreal hD)
        (mul_le_mul_of_nonneg_left (hs k hk).2 hHreal.le))
  rw [smoothed_residueFourierPart]
  calc
    _ ≤ ∑ k ∈ s, ‖residueFourier A k * (boxMultiplier H (residueCharacter k)) ^ J * residueCharacter k n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ s, ‖residueFourier A k‖ * (1 / ((H : ℝ) * D)) ^ J := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, norm_mul, norm_pow, residueCharacter_norm, mul_one]
      exact mul_le_mul_of_nonneg_left (hdecay k hk) (norm_nonneg _)
    _ = (∑ k ∈ s, ‖residueFourier A k‖) * (1 / ((H : ℝ) * D)) ^ J := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (residueFourier_mass_le A s) (by positivity)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem retained_prime_band_energy {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime)
    (hinj : Function.Injective a) (D : ℝ) (hD : 0 ≤ D)
    (hsmall : ∀ p, D * a p < 1) (H J N : ℕ) (hH : 0 < H) (hN : 0 < N) (S : ℤ)
    (hsize : ∀ p q, (a p : ℝ) ^ 2 * (a q : ℝ) ^ 2 ≤ 2 * N) :
    (∑ n ∈ Finset.range N, ‖∑ p : P, ∑ k ∈ retainedFrequencies ((a p) ^ 2) D,
      residueFourier (smallResidues (a p)) k * (boxMultiplier H (residueCharacter k)) ^ J *
        residueCharacter k (S + n)‖ ^ 2) ≤ 512 * N * Fintype.card P * D := by
  classical
  let Q := Σ p : P, retainedFrequencies ((a p) ^ 2) D
  let prime (q : Q) := a q.1
  let label (q : Q) := q.2.val.valMinAbs
  let coeff (q : Q) := residueFourier (smallResidues (a q.1)) q.2.val *
    (boxMultiplier H (residueCharacter q.2.val)) ^ J
  have hpQ (q : Q) : (prime q).Prime := hprime q.1
  have hnQ (q : Q) : label q ≠ 0 := by
    intro h
    have hk := (Finset.mem_filter.mp q.2.property).2.1
    exact hk ((ZMod.valMinAbs_eq_zero q.2.val).mp h)
  have hsQ (q : Q) : (label q).natAbs < prime q := by
    have hp0 : (0 : ℝ) < a q.1 := by exact_mod_cast (hprime q.1).pos
    have hfreq := (Finset.mem_filter.mp q.2.property).2.2
    unfold residueFrequency at hfreq
    rw [abs_div, Nat.cast_pow, abs_of_pos (sq_pos_of_pos hp0)] at hfreq
    have habs := (div_le_iff₀ (sq_pos_of_pos hp0)).mp hfreq
    have hcut := mul_lt_mul_of_pos_left (hsmall q.1) hp0
    have hreal : |(label q : ℝ)| < (prime q : ℝ) := by
      dsimp [label, prime]
      nlinarith
    have hreal' : ((label q).natAbs : ℝ) < (prime q : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hreal
    exact_mod_cast hreal'
  have hinjQ : ∀ i j : Q, prime i = prime j → label i = label j → i = j := by
    rintro ⟨p, k⟩ ⟨q, l⟩ hpq hkl
    have hpq' : p = q := hinj hpq
    subst q
    have hfreq : k.val = l.val := ZMod.valMinAbs_inj.mp hkl
    have hkl' : k = l := Subtype.ext hfreq
    subst l
    rfl
  have henergy := prime_frequency_sampling_bound (Finset.univ : Finset Q) prime label coeff S N hN
    (fun q _ => hpQ q) (fun q _ => hnQ q) (fun q _ => hsQ q)
    (fun i _ j _ => hinjQ i j) (fun i _ j _ => hsize i.1 j.1)
  have hmass : (∑ q : Q, ‖coeff q‖ ^ 2) ≤ (Fintype.card P : ℝ) * (2 * D) := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ p : P, ∑ k : retainedFrequencies ((a p) ^ 2) D,
          ‖residueFourier (smallResidues (a p)) k.val‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro k hk
        have hm := norm_boxMultiplier_le_one H hH (residueCharacter k.val) (residueCharacter_norm k.val)
        have hpow := pow_le_one₀ (norm_nonneg _) hm (n := J)
        have hmul := mul_le_mul_of_nonneg_left hpow (norm_nonneg (residueFourier (smallResidues (a p)) k.val))
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [coeff, norm_mul, norm_pow, mul_one] using hmul
      _ ≤ ∑ p : P, (2 * D) := by
        apply Finset.sum_le_sum
        intro p hp
        have heq := Finset.sum_coe_sort (retainedFrequencies ((a p) ^ 2) D)
          (fun k => ‖residueFourier (smallResidues (a p)) k‖ ^ 2)
        rw [heq]
        exact retained_prime_fourier_mass (a p) (hprime p).one_lt.le D hD
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hseries (n : ℕ) : (∑ q : Q, coeff q * realCharacter ((label q : ℝ) / (prime q : ℝ) ^ 2) (S + n)) =
      ∑ p : P, ∑ k ∈ retainedFrequencies ((a p) ^ 2) D,
        residueFourier (smallResidues (a p)) k * (boxMultiplier H (residueCharacter k)) ^ J *
          residueCharacter k (S + n) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    have heq := Finset.sum_coe_sort (retainedFrequencies ((a p) ^ 2) D)
      (fun k => residueFourier (smallResidues (a p)) k * (boxMultiplier H (residueCharacter k)) ^ J *
        residueCharacter k (S + n))
    rw [← heq]
    apply Finset.sum_congr rfl
    intro k hk
    have hfreq : (label ⟨p, k⟩ : ℝ) / (prime ⟨p, k⟩ : ℝ) ^ 2 = residueFrequency k.val := by
      simp only [label, prime, residueFrequency, Nat.cast_pow]
    rw [hfreq, ← residueCharacter_eq_realCharacter]
  simp only [hseries] at henergy
  have hscaled := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 256 * (N : ℝ) by positivity)
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def discardedFrequencies (m : ℕ) [NeZero m] (D : ℝ) : Finset (ZMod m) :=
  Finset.univ \ insert 0 (retainedFrequencies m D)

theorem zero_not_mem_retained (m : ℕ) [NeZero m] (D : ℝ) :
    (0 : ZMod m) ∉ retainedFrequencies m D := by
  simp [retainedFrequencies]

theorem discarded_frequency_lower {m : ℕ} [NeZero m] {D : ℝ}
    {k : ZMod m} (hk : k ∈ discardedFrequencies m D) :
    k ≠ 0 ∧ D < |residueFrequency k| := by
  have hnot := (Finset.mem_sdiff.mp hk).2
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    exact hnot (Finset.mem_insert_self 0 _)
  refine ⟨hk0, lt_of_not_ge ?_⟩
  intro hle
  apply hnot
  exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0, hle⟩)

theorem frequency_sum_decomposition {m : ℕ} [NeZero m] (D : ℝ) (F : ZMod m → ℂ) :
    (∑ k : ZMod m, F k) = F 0 + (∑ k ∈ retainedFrequencies m D, F k) +
      ∑ k ∈ discardedFrequencies m D, F k := by
  classical
  have h := Finset.sum_sdiff (Finset.subset_univ (insert 0 (retainedFrequencies m D))) (f := F)
  rw [Finset.sum_insert (zero_not_mem_retained m D)] at h
  change (∑ k ∈ discardedFrequencies m D, F k) + (F 0 + ∑ k ∈ retainedFrequencies m D, F k) = _ at h
  rw [← h]
  ring

theorem residueCharacter_zero {m : ℕ} [NeZero m] (n : ℤ) :
    residueCharacter (0 : ZMod m) n = 1 := by simp [residueCharacter, AddChar.map_zero_eq_one]

theorem boxMultiplier_zero {m : ℕ} [NeZero m] (H : ℕ) (hH : 0 < H) :
    boxMultiplier H (residueCharacter (0 : ZMod m)) = 1 := by
  have hH0 : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hH)
  simp [boxMultiplier, residueCharacter_zero, hH0]

theorem smoothed_indicator_decomposition {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (D : ℝ) (H J : ℕ) (hH : 0 < H) (n : ℤ) :
    boxSmooth H J (fun k : ℤ => residueIndicator A (k : ZMod m)) n = residueFourier A 0 +
      boxSmooth H J (residueFourierPart A (retainedFrequencies m D)) n +
      boxSmooth H J (residueFourierPart A (discardedFrequencies m D)) n := by
  have hfun : (fun k : ℤ => residueIndicator A (k : ZMod m)) = residueFourierPart A Finset.univ :=
    funext (residueIndicator_fourier A)
  rw [hfun, smoothed_residueFourierPart, smoothed_residueFourierPart, smoothed_residueFourierPart,
    frequency_sum_decomposition D]
  simp only [boxMultiplier_zero H hH, one_pow, residueCharacter_zero, mul_one]

theorem smoothed_discarded_bound {m : ℕ} [NeZero m]
    (A : Finset (ZMod m)) (D : ℝ) (hD : 0 < D) (H J : ℕ) (hH : 0 < H) (n : ℤ) :
    ‖boxSmooth H J (residueFourierPart A (discardedFrequencies m D)) n‖ ≤
      A.card * (1 / ((H : ℝ) * D)) ^ J :=
  smoothed_fourier_tail_bound A _ H J hH D hD
    (fun k hk => ⟨(discarded_frequency_lower hk).1, (discarded_frequency_lower hk).2.le⟩) n

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def primeBandSignal {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (n : ℤ) : ℂ :=
  ∑ p : P, residueIndicator (smallResidues (a p)) (n : ZMod ((a p) ^ 2))

noncomputable def retainedPrimeBand {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (H J : ℕ) (D : ℝ) (n : ℤ) : ℂ :=
  ∑ p : P, boxSmooth H J
    (residueFourierPart (smallResidues (a p)) (retainedFrequencies ((a p) ^ 2) D)) n

noncomputable def discardedPrimeBand {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (H J : ℕ) (D : ℝ) (n : ℤ) : ℂ :=
  ∑ p : P, boxSmooth H J
    (residueFourierPart (smallResidues (a p)) (discardedFrequencies ((a p) ^ 2) D)) n

theorem smoothed_prime_band_split {P : Type*} [Fintype P] (a : P → ℕ) [∀ p, NeZero (a p)]
    (hprime : ∀ p, (a p).Prime) (H J : ℕ) (hH : 0 < H) (D : ℝ) (n : ℤ) :
    boxSmooth H J (primeBandSignal a) n - (∑ p : P, 1 / (a p : ℂ)) =
      retainedPrimeBand a H J D n + discardedPrimeBand a H J D n := by
  unfold primeBandSignal
  rw [boxSmooth_sum]
  have hterm (p : P) := smoothed_indicator_decomposition (smallResidues (a p)) D H J hH n
  simp only [smallResidues_fourier_zero (a _) (hprime _).one_lt.le] at hterm
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun p hp => hterm p)
  simp only [Finset.sum_add_distrib] at hsum
  unfold retainedPrimeBand discardedPrimeBand
  rw [hsum]
  ring

theorem discardedPrimeBand_bound {P : Type*} [Fintype P] (a : P → ℕ) [∀ p, NeZero (a p)]
    (hprime : ∀ p, (a p).Prime) (H J : ℕ) (hH : 0 < H) (D : ℝ) (hD : 0 < D) (n : ℤ) :
    ‖discardedPrimeBand a H J D n‖ ≤ (∑ p : P, (a p : ℝ)) * (1 / ((H : ℝ) * D)) ^ J := by
  unfold discardedPrimeBand
  calc
    _ ≤ ∑ p : P, ‖boxSmooth H J
        (residueFourierPart (smallResidues (a p)) (discardedFrequencies ((a p) ^ 2) D)) n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p : P, (a p : ℝ) * (1 / ((H : ℝ) * D)) ^ J := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [smallResidues_card (a p) (hprime p).one_lt.le] using
        smoothed_discarded_bound (smallResidues (a p)) D hD H J hH n
    _ = _ := by rw [Finset.sum_mul]

theorem smoothed_prime_band_energy {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (D : ℝ) (hD : 0 < D) (hsmall : ∀ p, D * a p < 1)
    (H J N : ℕ) (hH : 0 < H) (hN : 0 < N) (S : ℤ)
    (hsize : ∀ p q, (a p : ℝ) ^ 2 * (a q : ℝ) ^ 2 ≤ 2 * N) :
    (∑ n ∈ Finset.range N,
      ‖boxSmooth H J (primeBandSignal a) (S + n) - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2) ≤
      1024 * N * Fintype.card P * D +
        2 * N * (∑ p : P, (a p : ℝ)) ^ 2 * (1 / ((H : ℝ) * D)) ^ (2 * J) := by
  have hret := retained_prime_band_energy a hprime hinj D hD.le hsmall H J N hH hN S hsize
  have hret' : (∑ n ∈ Finset.range N, ‖retainedPrimeBand a H J D (S + n)‖ ^ 2) ≤
      512 * N * Fintype.card P * D := by
    simpa only [retainedPrimeBand, smoothed_residueFourierPart] using hret
  have hpoint (n : ℕ) :
      ‖boxSmooth H J (primeBandSignal a) (S + n) - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2 ≤
      2 * ‖retainedPrimeBand a H J D (S + n)‖ ^ 2 +
        2 * ((∑ p : P, (a p : ℝ)) * (1 / ((H : ℝ) * D)) ^ J) ^ 2 := by
    rw [smoothed_prime_band_split a hprime H J hH D]
    have htriangle := norm_add_le (retainedPrimeBand a H J D (S + n)) (discardedPrimeBand a H J D (S + n))
    have htail := discardedPrimeBand_bound a hprime H J hH D hD (S + n)
    have hn1 := norm_nonneg (retainedPrimeBand a H J D (S + n))
    have hn2 := norm_nonneg (discardedPrimeBand a H J D (S + n))
    have hn3 := norm_nonneg (retainedPrimeBand a H J D (S + n) + discardedPrimeBand a H J D (S + n))
    have hb : 0 ≤ (∑ p : P, (a p : ℝ)) * (1 / ((H : ℝ) * D)) ^ J := by positivity
    nlinarith [sq_nonneg (‖retainedPrimeBand a H J D (S + n)‖ - ‖discardedPrimeBand a H J D (S + n)‖)]
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hpoint n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hpow : ((1 / ((H : ℝ) * D)) ^ J) ^ 2 = (1 / ((H : ℝ) * D)) ^ (2 * J) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [mul_pow, hpow] at hsum
  nlinarith

end Erdos676
end

section
open Filter Asymptotics
open scoped Topology

namespace Erdos676

noncomputable def powerFloor (r x : ℝ) : ℕ := ⌊x ^ r⌋₊

theorem floor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

theorem log_floor_ge_half_log {x : ℝ} (hx : 4 ≤ x) :
    Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hhalf := floor_ge_half (by linarith : 2 ≤ x)
  have hfloorpos : (0 : ℝ) < ⌊x⌋₊ := lt_of_lt_of_le (by positivity : 0 < x / 2) hhalf
  have hlog := Real.log_le_log (by positivity : 0 < x / 2) hhalf
  rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  have hfour : Real.log (4 : ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlogfour] at hfour
  linarith

theorem half_pow_le_inv_succ (j : ℕ) :
    (1 / 2 : ℝ) ^ j ≤ 1 / ((j : ℝ) + 1) := by
  have hj : j + 1 ≤ 2 ^ j := j.lt_two_pow_self
  have hj' : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by exact_mod_cast hj
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hj'

theorem eventually_log_le_power {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hnorm : Real.log x ≤ ‖Real.log x‖ := le_abs_self _
  have hpow : ‖x ^ r‖ = x ^ r := Real.norm_of_nonneg (Real.rpow_pos_of_pos hxpos r).le
  exact hnorm.trans (by simpa only [hpow] using hx)

theorem eventually_powerFloor_half {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, x ^ r / 2 ≤ (powerFloor r x : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop hr).eventually_ge_atTop 2] with x hx
  exact floor_ge_half hx

theorem eventually_log_powerFloor_lower {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, (r / 2) * Real.log x ≤ Real.log (powerFloor r x : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop hr).eventually_ge_atTop 4,
    eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have h := log_floor_ge_half_log hx
  rw [Real.log_rpow hxpos r] at h
  simpa only [powerFloor, div_mul_eq_mul_div] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_family_card_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hz : 0 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z) :
    (Fintype.card P : ℝ) ≤ z := by
  have hsub : Finset.univ.image a ⊆ Finset.Ioc 0 ⌊z⌋₊ := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_Ioc.mpr ⟨(hprime p).pos, Nat.le_floor (hle p)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show (Fintype.card P : ℝ) ≤ ⌊z⌋₊ by exact_mod_cast hcard).trans (Nat.floor_le hz)

theorem prime_family_sum_le_square {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hz : 0 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z) :
    (∑ p : P, (a p : ℝ)) ≤ z ^ 2 := by
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) => hle p)
  have hcard := mul_le_mul_of_nonneg_right (prime_family_card_le a hinj hprime z hz hle) hz
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  nlinarith

theorem smoothed_prime_band_energy_size {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (z D : ℝ) (hz : 0 ≤ z) (hD : 0 < D) (hle : ∀ p, (a p : ℝ) ≤ z)
    (hcut : D * z < 1) (H J N : ℕ) (hH : 0 < H) (hN : 0 < N) (S : ℤ)
    (hsize : z ^ 4 ≤ 2 * N) :
    (∑ n ∈ Finset.range N,
      ‖boxSmooth H J (primeBandSignal a) (S + n) - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2) ≤
      1024 * N * z * D + 2 * N * z ^ 4 * (1 / ((H : ℝ) * D)) ^ (2 * J) := by
  have hsmall (p : P) : D * a p < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle p) hD.le) hcut
  have hpair (p q : P) : (a p : ℝ) ^ 2 * (a q : ℝ) ^ 2 ≤ 2 * N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (a p)) (hle p) 2
    have hq := pow_le_pow_left₀ (Nat.cast_nonneg (a q)) (hle q) 2
    have h := mul_le_mul hp hq (sq_nonneg _) (sq_nonneg z)
    nlinarith
  have h := smoothed_prime_band_energy a hprime hinj D hD hsmall H J N hH hN S hpair
  have hcard := prime_family_card_le a hinj hprime z hz hle
  have hsum := prime_family_sum_le_square a hinj hprime z hz hle
  have hsum0 : 0 ≤ ∑ p : P, (a p : ℝ) := Finset.sum_nonneg (fun p hp => Nat.cast_nonneg _)
  have hsum2 := pow_le_pow_left₀ hsum0 hsum 2
  have hterm1 := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 1024 * (N : ℝ) * D by positivity)
  have hterm2 := mul_le_mul_of_nonneg_left hsum2
    (show 0 ≤ 2 * (N : ℝ) * (1 / ((H : ℝ) * D)) ^ (2 * J) by positivity)
  nlinarith

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem growing_dyadic_covers {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, dyadicCutoff (x ^ α) (powerFloor δ x) < 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / (4 * α) := div_pos hlog2 (by positivity)
  have hlog := eventually_log_le_power hδ hc
  have hfloor := eventually_powerFloor_half hδ
  filter_upwards [hlog, hfloor, eventually_ge_atTop (1 : ℝ)] with x hxlog hxfloor hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hz : 1 ≤ x ^ α := Real.one_le_rpow hx hα.le
  have hnonneg : 0 ≤ α * Real.log x := mul_nonneg hα.le (Real.log_nonneg hx)
  have hden : 0 < (powerFloor δ x : ℝ) + 1 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hxlog hα.le
  have hcancel : α * (Real.log 2 / (4 * α)) = Real.log 2 / 4 := by
    field_simp
  have hsmall : α * Real.log x ≤ (Real.log 2 / 4) * x ^ δ := by
    nlinarith [hscaled]
  have hcut : Real.log (dyadicCutoff (x ^ α) (powerFloor δ x)) ≤
      (α * Real.log x) / ((powerFloor δ x : ℝ) + 1) := by
    rw [log_dyadicCutoff hz, Real.log_rpow hxpos α]
    have h := mul_le_mul_of_nonneg_right (half_pow_le_inv_succ (powerFloor δ x)) hnonneg
    convert h using 1 <;> first | rfl | ring
  have hratio : (α * Real.log x) / ((powerFloor δ x : ℝ) + 1) ≤ Real.log 2 / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [hsmall, hxfloor]
  have hstrict : Real.log (dyadicCutoff (x ^ α) (powerFloor δ x)) < Real.log 2 := by
    linarith
  exact (Real.log_lt_log_iff
    (lt_of_lt_of_le zero_lt_one (one_le_dyadicCutoff hz _)) (by norm_num)).mp hstrict

theorem powerFloor_power_le {x : ℝ} (hx : 0 ≤ x) (r : ℝ) (m : ℕ) :
    (powerFloor r x : ℝ) ^ m ≤ x ^ (r * m) := by
  have hfloor : (powerFloor r x : ℝ) ≤ x ^ r := Nat.floor_le (Real.rpow_nonneg hx r)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (powerFloor r x)) hfloor m
  calc
    _ ≤ (x ^ r) ^ m := hpow
    _ = x ^ (r * m) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem growing_first_error_bound {x α δ : ℝ} (hx : 1 ≤ x) (hδ : 0 ≤ δ) (m : ℕ) :
    (2 * (powerFloor δ x : ℝ) + 1) * (x ^ α) ^ m ≤ 3 * x ^ (δ + α * m) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hfloor : (powerFloor δ x : ℝ) ≤ x ^ δ := Nat.floor_le (Real.rpow_nonneg hx0 δ)
  have hone : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ
  have hp : 0 ≤ (x ^ α) ^ m := pow_nonneg (Real.rpow_nonneg hx0 α) m
  have hbound : 2 * (powerFloor δ x : ℝ) + 1 ≤ 3 * x ^ δ := by linarith
  calc
    _ ≤ (3 * x ^ δ) * (x ^ α) ^ m := mul_le_mul_of_nonneg_right hbound hp
    _ = 3 * x ^ (δ + α * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, Real.rpow_add (lt_of_lt_of_le zero_lt_one hx)]
      ring

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

noncomputable def fourierThreshold (η ε x : ℝ) : ℝ := x ^ ε / (powerFloor η x : ℝ)

theorem fourier_first_term_bound {x H β ε η : ℝ} (hx : 0 < x)
    (hH : x ^ η / 2 ≤ H) :
    1024 * (4 * x) * x ^ β * (x ^ ε / H) ≤ 8192 * x ^ (1 + β + ε - η) := by
  have hp : 0 < x ^ η / 2 := by positivity
  have hden := div_le_div_of_nonneg_left
    (show 0 ≤ 4096 * x * x ^ β * x ^ ε by positivity) hp hH
  have hproduct : x * x ^ β * x ^ ε = x ^ (1 + β + ε) := by
    rw [Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
  calc
    _ = (4096 * x * x ^ β * x ^ ε) / H := by ring
    _ ≤ (4096 * x * x ^ β * x ^ ε) / (x ^ η / 2) := hden
    _ = 8192 * (x * x ^ β * x ^ ε / x ^ η) := by ring
    _ = _ := by rw [hproduct, ← Real.rpow_sub hx]

theorem fourier_tail_term_identity {x H β ε : ℝ} (hx : 0 < x) (hH : H ≠ 0) (J : ℕ) :
    2 * (4 * x) * (x ^ β) ^ 4 * (1 / (H * (x ^ ε / H))) ^ (2 * J) =
      8 * x ^ (1 + 4 * β - ε * (2 * J : ℕ)) := by
  have hcancel : H * (x ^ ε / H) = x ^ ε := by field_simp
  have hp : (1 / x ^ ε) ^ (2 * J) = x ^ (-ε * (2 * J : ℕ)) := by
    calc
      _ = (x ^ (-ε)) ^ (2 * J) := by rw [Real.rpow_neg hx.le, one_div]
      _ = (x ^ (-ε)) ^ ((2 * J : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = _ := (Real.rpow_mul hx.le _ _).symm
  have hfour : (x ^ β) ^ 4 = x ^ (4 * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    norm_num
    ring
  rw [hcancel, hp, hfour]
  have hproduct : x * x ^ (4 * β) * x ^ (-ε * (2 * J : ℕ)) =
      x ^ (1 + 4 * β - ε * (2 * J : ℕ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
    congr 1
    ring
  calc
    _ = 8 * (x * x ^ (4 * β) * x ^ (-ε * (2 * J : ℕ))) := by ring
    _ = _ := by rw [hproduct]

theorem fourier_error_bound {x H β ε η : ℝ} (hx : 1 ≤ x)
    (hH : x ^ η / 2 ≤ H) (hrelation : η = β + 2 * ε)
    (J : ℕ) (hJ : 4 * β + ε ≤ ε * (2 * J : ℕ)) :
    1024 * (4 * x) * x ^ β * (x ^ ε / H) +
      2 * (4 * x) * (x ^ β) ^ 4 * (1 / (H * (x ^ ε / H))) ^ (2 * J) ≤
        8200 * x ^ (1 - ε) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity : 0 < x ^ η / 2) hH
  have hfirst := fourier_first_term_bound hx0 hH (β := β) (ε := ε)
  have hexponent : 1 + β + ε - η = 1 - ε := by linarith
  rw [hexponent] at hfirst
  rw [fourier_tail_term_identity hx0 hH0.ne' J]
  have hpower := Real.rpow_le_rpow_of_exponent_le hx
    (show 1 + 4 * β - ε * (2 * J : ℕ) ≤ 1 - ε by linarith)
  linarith

end Erdos676
end

section
open Filter
open scoped Topology BigOperators

namespace Erdos676

theorem fourier_threshold_product_le {x β ε η : ℝ} (hx : 0 < x)
    (hH : x ^ η / 2 ≤ (powerFloor η x : ℝ)) (hrelation : η = β + 2 * ε) :
    fourierThreshold η ε x * x ^ β ≤ 2 * x ^ (-ε) := by
  have h := div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le ε)
    (show 0 < x ^ η / 2 by positivity) hH
  have hscaled := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx.le β)
  have heq : (x ^ ε / (x ^ η / 2)) * x ^ β = 2 * x ^ (-ε) := by
    calc
      _ = 2 * ((x ^ β * x ^ ε) / x ^ η) := by ring
      _ = 2 * x ^ (β + ε - η) := by rw [← Real.rpow_add hx, ← Real.rpow_sub hx]
      _ = _ := by congr 1; congr 1; linarith
  exact hscaled.trans_eq heq

theorem growing_fourier_cutoffs {β ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hrelation : η = β + 2 * ε) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 0 < powerFloor η x ∧
      x ^ η / 2 ≤ (powerFloor η x : ℝ) ∧ 0 < fourierThreshold η ε x ∧
      fourierThreshold η ε x * x ^ β < 1 := by
  have hlimit := (tendsto_rpow_neg_atTop hε).const_mul (2 : ℝ)
  have hsmall : ∀ᶠ x : ℝ in atTop, 2 * x ^ (-ε) < 1 :=
    (tendsto_order.mp (by simpa only [mul_zero] using hlimit)).2 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_powerFloor_half hη, hsmall]
    with x hx hhalf htail
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hHreal : (0 : ℝ) < powerFloor η x := lt_of_lt_of_le (by positivity : 0 < x ^ η / 2) hhalf
  have hHnat : 0 < powerFloor η x := by exact_mod_cast hHreal
  refine ⟨hx, hHnat, hhalf, div_pos (Real.rpow_pos_of_pos hx0 ε) hHreal, ?_⟩
  exact (fourier_threshold_product_le hx0 hhalf hrelation).trans_lt htail

universe u

theorem growing_prime_band_energy {β ε η : ℝ} (hβ : 0 < β) (hβsmall : β ≤ 1 / 4)
    (hε : 0 < ε) (hrelation : η = β + 2 * ε) :
    ∃ J : ℕ, ∀ᶠ X : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (a : P → ℕ) [∀ p, NeZero (a p)],
        (∀ p, (a p).Prime) → Function.Injective a → (∀ p, (a p : ℝ) ≤ (X : ℝ) ^ β) →
        ∀ S : ℤ,
          (∑ n ∈ Finset.range (4 * X),
            ‖boxSmooth (powerFloor η X) J (primeBandSignal a) (S + n) -
              (∑ p : P, 1 / (a p : ℂ))‖ ^ 2) ≤ 8200 * (X : ℝ) ^ (1 - ε) := by
  have hη : 0 < η := by linarith
  obtain ⟨J, hJ⟩ := exists_nat_gt ((4 * β + ε) / (2 * ε))
  have hJ' : 4 * β + ε ≤ ε * (2 * J : ℕ) := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * ε)).mp hJ
    push_cast
    nlinarith
  refine ⟨J, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (growing_fourier_cutoffs hε hη hrelation)] with X hX
  obtain ⟨hx, hH, hhalf, hD, hcut⟩ := hX
  intro P instF instD a instN hprime hinj hle S
  have hx0 : (0 : ℝ) < X := zero_lt_one.trans_le hx
  have hXN : 0 < X := by exact_mod_cast hx0
  have hsize : ((X : ℝ) ^ β) ^ 4 ≤ (X : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]
    have hpow := Real.rpow_le_rpow_of_exponent_le hx (show β * (4 : ℝ) ≤ 1 by linarith)
    simpa only [Real.rpow_one, Nat.cast_ofNat] using hpow
  have h := smoothed_prime_band_energy_size a hprime hinj ((X : ℝ) ^ β)
    (fourierThreshold η ε X) (Real.rpow_nonneg (Nat.cast_nonneg X) β) hD hle hcut
    (powerFloor η X) J (4 * X) hH (by omega) S (by push_cast; nlinarith)
  have herr := fourier_error_bound hx hhalf hrelation J hJ'
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  exact h.trans herr

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

def boxPathShift {H J : ℕ} (p : Fin J → Fin H) : ℤ := ∑ j : Fin J, (p j : ℤ)

theorem boxPathShift_nonneg {H J : ℕ} (p : Fin J → Fin H) : 0 ≤ boxPathShift p :=
  Finset.sum_nonneg (fun j hj => Int.natCast_nonneg _)

theorem boxPathShift_le {H J : ℕ} (p : Fin J → Fin H) :
    boxPathShift p ≤ (J : ℤ) * H := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin J))) =>
    (show (p j : ℤ) ≤ H by exact_mod_cast (p j).isLt.le))
  simpa only [boxPathShift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

theorem boxPathShift_cons {H J : ℕ} (a : Fin H) (p : Fin J → Fin H) :
    boxPathShift (Fin.cons a p) = (a : ℤ) + boxPathShift p := by
  simp only [boxPathShift, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem box_path_sum_succ (H J : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    (∑ p : Fin (J + 1) → Fin H, f (n + boxPathShift p)) =
      ∑ a : Fin H, ∑ p : Fin J → Fin H, f ((n + a) + boxPathShift p) := by
  have h := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (J + 1) => Fin H))
    (fun p => f (n + boxPathShift p))
  rw [Fintype.sum_prod_type] at h
  symm
  convert h using 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro p hp
  change f ((n + a) + boxPathShift p) = f (n + boxPathShift (Fin.cons a p))
  rw [boxPathShift_cons, add_assoc]

theorem boxSmooth_path_formula (H J : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    boxSmooth H J f n =
      (∑ p : Fin J → Fin H, f (n + boxPathShift p)) / (H : ℂ) ^ J := by
  induction J generalizing n with
  | zero => simp [boxSmooth, boxPathShift]
  | succ J ih =>
      change (∑ a ∈ Finset.range H, boxSmooth H J f (n + a)) / (H : ℂ) = _
      simp_rw [ih]
      rw [← Finset.sum_div, div_div, pow_succ, box_path_sum_succ, Finset.sum_range]

theorem boxSmooth_const (H J : ℕ) (hH : 0 < H) (c : ℂ) (n : ℤ) :
    boxSmooth H J (fun _ => c) n = c := by
  have hH0 : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hH)
  induction J generalizing n with
  | zero => rfl
  | succ J ih =>
      change (∑ a ∈ Finset.range H, boxSmooth H J (fun _ => c) (n + a)) / (H : ℂ) = c
      simp only [ih, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def realBoxSmooth (H J : ℕ) (f : ℤ → ℝ) (n : ℤ) : ℝ :=
  (∑ p : Fin J → Fin H, f (n + boxPathShift p)) / (H : ℝ) ^ J

theorem coe_realBoxSmooth (H J : ℕ) (f : ℤ → ℝ) (n : ℤ) :
    (realBoxSmooth H J f n : ℂ) = boxSmooth H J (fun k => (f k : ℂ)) n := by
  rw [boxSmooth_path_formula]
  simp only [realBoxSmooth, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem realBoxSmooth_const (H J : ℕ) (hH : 0 < H) (c : ℝ) (n : ℤ) :
    realBoxSmooth H J (fun _ => c) n = c := by
  have h := boxSmooth_const H J hH (c : ℂ) n
  rw [← coe_realBoxSmooth] at h
  exact_mod_cast h

theorem realBoxSmooth_nonneg (H J : ℕ) (f : ℤ → ℝ) (hf : ∀ k, 0 ≤ f k) (n : ℤ) :
    0 ≤ realBoxSmooth H J f n := by
  exact div_nonneg (Finset.sum_nonneg (fun p hp => hf _)) (pow_nonneg (Nat.cast_nonneg H) J)

theorem realBoxSmooth_le_of_local (H J : ℕ) (hH : 0 < H) (f : ℤ → ℝ) (n : ℤ) (c : ℝ)
    (hf : ∀ k : ℤ, n ≤ k → k ≤ n + (J : ℤ) * H → f k ≤ c) :
    realBoxSmooth H J f n ≤ c := by
  have hsum : (∑ p : Fin J → Fin H, f (n + boxPathShift p)) ≤
      ∑ _p : Fin J → Fin H, c := by
    apply Finset.sum_le_sum
    intro p hp
    exact hf _ (by linarith [boxPathShift_nonneg p]) (by linarith [boxPathShift_le p])
  have h := div_le_div_of_nonneg_right hsum (pow_nonneg (Nat.cast_nonneg H) J)
  exact h.trans_eq (realBoxSmooth_const H J hH c n)

theorem realBoxSmooth_ge_of_local (H J : ℕ) (hH : 0 < H) (f : ℤ → ℝ) (n : ℤ) (c : ℝ)
    (hf : ∀ k : ℤ, n ≤ k → k ≤ n + (J : ℤ) * H → c ≤ f k) :
    c ≤ realBoxSmooth H J f n := by
  have hsum : (∑ _p : Fin J → Fin H, c) ≤ ∑ p : Fin J → Fin H, f (n + boxPathShift p) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hf _ (by linarith [boxPathShift_nonneg p]) (by linarith [boxPathShift_le p])
  have h := div_le_div_of_nonneg_right hsum (pow_nonneg (Nat.cast_nonneg H) J)
  exact (realBoxSmooth_const H J hH c n).symm.trans_le h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem shifted_sum_lower (L U : Finset ℤ) (G : ℤ → ℝ) (t : ℤ)
    (hG : ∀ n, 0 ≤ G n) (hLU : ∀ n ∈ L, n + t ∈ U) :
    (∑ n ∈ L, G (n + t)) ≤ ∑ n ∈ U, G n := by
  classical
  have hsub : L.image (fun n => n + t) ⊆ U := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact hLU n hn
  have heq : (∑ m ∈ L.image (fun n => n + t), G m) = ∑ n ∈ L, G (n + t) :=
    Finset.sum_image (fun a ha b hb h => add_right_cancel h)
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => hG n)

theorem shifted_sum_upper (U V : Finset ℤ) (G : ℤ → ℝ) (t : ℤ)
    (hG : ∀ n, 0 ≤ G n) (hUV : ∀ n ∈ U, n - t ∈ V) :
    (∑ n ∈ U, G n) ≤ ∑ n ∈ V, G (n + t) := by
  have h := shifted_sum_lower U V (fun n => G (n + t)) (-t)
    (fun n => hG _) (by simpa only [sub_eq_add_neg] using hUV)
  simpa only [add_assoc, neg_add_cancel, add_zero] using h

theorem smoothing_sandwich (L U V : Finset ℤ) (G : ℤ → ℝ) (H J : ℕ) (hH : 0 < H)
    (hG : ∀ n, 0 ≤ G n)
    (hLU : ∀ t : ℤ, 0 ≤ t → t ≤ (J : ℤ) * H → ∀ n ∈ L, n + t ∈ U)
    (hUV : ∀ t : ℤ, 0 ≤ t → t ≤ (J : ℤ) * H → ∀ n ∈ U, n - t ∈ V) :
    (∑ n ∈ L, realBoxSmooth H J G n) ≤ (∑ n ∈ U, G n) ∧
      (∑ n ∈ U, G n) ≤ ∑ n ∈ V, realBoxSmooth H J G n := by
  have hlower (p : Fin J → Fin H) := shifted_sum_lower L U G (boxPathShift p) hG
    (hLU _ (boxPathShift_nonneg p) (boxPathShift_le p))
  have hupper (p : Fin J → Fin H) := shifted_sum_upper U V G (boxPathShift p) hG
    (hUV _ (boxPathShift_nonneg p) (boxPathShift_le p))
  have hconst : (∑ _p : Fin J → Fin H, ∑ n ∈ U, G n) / (H : ℝ) ^ J = ∑ n ∈ U, G n :=
    realBoxSmooth_const H J hH _ 0
  have hlo := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.univ) (fun (p : Fin J → Fin H) hp => hlower p))
    (pow_nonneg (Nat.cast_nonneg H) J)
  have hhi := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.univ) (fun (p : Fin J → Fin H) hp => hupper p))
    (pow_nonneg (Nat.cast_nonneg H) J)
  rw [hconst] at hlo hhi
  have heq (W : Finset ℤ) : (∑ n ∈ W, realBoxSmooth H J G n) =
      (∑ p : Fin J → Fin H, ∑ n ∈ W, G (n + boxPathShift p)) / (H : ℝ) ^ J := by
    unfold realBoxSmooth
    rw [← Finset.sum_div, Finset.sum_comm]
  constructor
  · rw [heq]
    exact hlo
  · rw [heq]
    exact hhi

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem sum_deviation_bound {I : Type*} (W : Finset I) (F : I → ℝ) (μ E : ℝ)
    (hE : ∑ n ∈ W, (F n - μ) ^ 2 ≤ E) :
    |(∑ n ∈ W, F n) - μ * W.card| ≤ Real.sqrt (W.card * E) := by
  have hE0 : 0 ≤ E := (Finset.sum_nonneg (fun n hn => sq_nonneg (F n - μ))).trans hE
  have hcs := sq_sum_le_card_mul_sum_sq (s := W) (f := fun n => F n - μ)
  have hscaled := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg W.card)
  have hsum : (∑ n ∈ W, (F n - μ)) = (∑ n ∈ W, F n) - μ * W.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum] at hcs
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hE0)).mpr
  simpa only [sq_abs] using hcs.trans hscaled

theorem correlation_from_smoothing_bounds (L U V : Finset ℤ) (G F : ℤ → ℝ) (μ E M B : ℝ)
    (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (hlower : (∑ n ∈ L, F n) ≤ ∑ n ∈ U, G n)
    (hupper : (∑ n ∈ U, G n) ≤ ∑ n ∈ V, F n)
    (hEL : ∑ n ∈ L, (F n - μ) ^ 2 ≤ E)
    (hEV : ∑ n ∈ V, (F n - μ) ^ 2 ≤ E)
    (hLM : (L.card : ℝ) ≤ M) (hVM : (V.card : ℝ) ≤ M)
    (hLU : (U.card : ℝ) ≤ L.card + B) (hUV : (V.card : ℝ) ≤ U.card + B) :
    |(∑ n ∈ U, G n) - μ * U.card| ≤ Real.sqrt (M * E) + μ * B := by
  have hdl := sum_deviation_bound L F μ E hEL
  have hdv := sum_deviation_bound V F μ E hEV
  have hrootL := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hLM hE)
  have hrootV := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hVM hE)
  have hcl := mul_le_mul_of_nonneg_left hLU hμ
  have hcv := mul_le_mul_of_nonneg_left hUV hμ
  obtain ⟨hdl1, hdl2⟩ := abs_le.mp hdl
  obtain ⟨hdv1, hdv2⟩ := abs_le.mp hdv
  apply abs_le.mpr
  constructor <;> nlinarith

end Erdos676
end

section
namespace Erdos676

def initialResidues (m p : ℕ) : Finset (ZMod m) :=
  (Finset.range p).image (fun k : ℕ => (k : ZMod m))

def expandedResidues (m p R : ℕ) : Finset (ZMod m) :=
  (Finset.range (p + R)).image (fun k : ℕ => (k : ZMod m) - R)

def contractedResidues (m p R : ℕ) : Finset (ZMod m) := initialResidues m (p - R)

def boundaryResidues (m p R : ℕ) : Finset (ZMod m) :=
  expandedResidues m p R \ contractedResidues m p R

theorem contracted_subset_initial (m p R : ℕ) : contractedResidues m p R ⊆ initialResidues m p := by
  apply Finset.image_subset_image
  exact Finset.range_mono (Nat.sub_le p R)

theorem initial_subset_expanded (m p R : ℕ) : initialResidues m p ⊆ expandedResidues m p R := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨k + R, Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), ?_⟩
  simp only [Nat.cast_add, add_sub_cancel_right]

theorem contracted_shift_initial (m p R h : ℕ) (hh : h ≤ R) (n : ZMod m)
    (hn : n ∈ contractedResidues m p R) : n + h ∈ initialResidues m p := by
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨k + h, Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), ?_⟩
  rw [Nat.cast_add, heq]

theorem initial_shift_expanded (m p R h : ℕ) (hh : h ≤ R) (n : ZMod m)
    (hn : n + h ∈ initialResidues m p) : n ∈ expandedResidues m p R := by
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hn
  refine Finset.mem_image.mpr ⟨k + (R - h),
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), ?_⟩
  rw [Nat.cast_add, Nat.cast_sub hh, heq]
  ring

theorem initialResidues_card (m p : ℕ) (hp : p ≤ m) : (initialResidues m p).card = p := by
  unfold initialResidues
  rw [Finset.card_image_iff.mpr, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < m := (Finset.mem_range.mp ha).trans_le hp
  have hb' : b < m := (Finset.mem_range.mp hb).trans_le hp
  have hval := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hval

theorem boundaryResidues_card_le (m p R : ℕ) (hp : p ≤ m) :
    (boundaryResidues m p R).card ≤ 2 * R := by
  have hsub := (contracted_subset_initial m p R).trans (initial_subset_expanded m p R)
  have hcon : (contractedResidues m p R).card = p - R := initialResidues_card m (p - R)
    ((Nat.sub_le p R).trans hp)
  have hexp : (expandedResidues m p R).card ≤ p + R := by
    exact (Finset.card_image_le).trans_eq (Finset.card_range (p + R))
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  change (boundaryResidues m p R).card + (contractedResidues m p R).card =
    (expandedResidues m p R).card at hcard
  omega

theorem outside_boundary_shift (m p R h : ℕ) (hh : h ≤ R) (n : ZMod m)
    (hn : n ∉ boundaryResidues m p R) :
    n + h ∈ initialResidues m p ↔ n ∈ initialResidues m p := by
  have hcon (he : n ∈ expandedResidues m p R) : n ∈ contractedResidues m p R := by
    by_contra hc
    exact hn (Finset.mem_sdiff.mpr ⟨he, hc⟩)
  constructor
  · intro hmem
    exact contracted_subset_initial m p R (hcon (initial_shift_expanded m p R h hh n hmem))
  · intro hmem
    exact contracted_shift_initial m p R h hh n (hcon (initial_subset_expanded m p R hmem))

theorem initial_prime_square (p : ℕ) : initialResidues (p ^ 2) p = smallResidues p := rfl

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def originalAvoidSet {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc A B).filter (fun n => ∀ p, (n : ZMod ((a p) ^ 2)) ∉ initialResidues ((a p) ^ 2) (a p))

noncomputable def lowerAvoidSet {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc A (B - R)).filter
    (fun n => ∀ p, (n : ZMod ((a p) ^ 2)) ∉ expandedResidues ((a p) ^ 2) (a p) R)

noncomputable def upperAvoidSet {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (A - R) B).filter
    (fun n => ∀ p, (n : ZMod ((a p) ^ 2)) ∉ contractedResidues ((a p) ^ 2) (a p) R)

theorem lowerAvoidSet_subset {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    lowerAvoidSet a A B R ⊆ originalAvoidSet a A B := by
  classical
  intro n hn
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, by have := (Finset.mem_Icc.mp hnI).2; omega⟩, ?_⟩
  intro p hp
  exact hnA p (initial_subset_expanded _ _ _ hp)

theorem originalAvoidSet_subset {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    originalAvoidSet a A B ⊆ upperAvoidSet a A B R := by
  classical
  intro n hn
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnI).1; omega, (Finset.mem_Icc.mp hnI).2⟩, ?_⟩
  intro p hp
  exact hnA p (contracted_subset_initial _ _ _ hp)

theorem lowerAvoidSet_shift {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ)
    (t : ℤ) (ht0 : 0 ≤ t) (htR : t ≤ R) (n : ℤ) (hn : n ∈ lowerAvoidSet a A B R) :
    n + t ∈ originalAvoidSet a A B := by
  classical
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
  have htNat : t.toNat ≤ R := by exact_mod_cast (show (t.toNat : ℤ) ≤ R by rwa [htcast])
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnI).1; omega,
    by have := (Finset.mem_Icc.mp hnI).2; omega⟩, ?_⟩
  intro p hp
  have htmod : (t.toNat : ZMod ((a p) ^ 2)) = (t : ZMod ((a p) ^ 2)) := by
    rw [← Int.cast_natCast, htcast]
  have hp' : (n : ZMod ((a p) ^ 2)) + t.toNat ∈ initialResidues ((a p) ^ 2) (a p) := by
    simpa only [Int.cast_add, htmod] using hp
  exact hnA p (initial_shift_expanded _ _ _ _ htNat _ hp')

theorem upperAvoidSet_shift {P : Type*} [Fintype P] (a : P → ℕ) (A B : ℤ) (R : ℕ)
    (t : ℤ) (ht0 : 0 ≤ t) (htR : t ≤ R) (n : ℤ) (hn : n ∈ originalAvoidSet a A B) :
    n - t ∈ upperAvoidSet a A B R := by
  classical
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
  have htNat : t.toNat ≤ R := by exact_mod_cast (show (t.toNat : ℤ) ≤ R by rwa [htcast])
  obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hnI).1; omega,
    by have := (Finset.mem_Icc.mp hnI).2; omega⟩, ?_⟩
  intro p hp
  have htmod : (t.toNat : ZMod ((a p) ^ 2)) = (t : ZMod ((a p) ^ 2)) := by
    rw [← Int.cast_natCast, htcast]
  have hbad := contracted_shift_initial _ _ _ _ htNat (Int.cast (n - t) : ZMod ((a p) ^ 2)) hp
  apply hnA p
  simpa only [htmod, ← Int.cast_add, sub_add_cancel] using hbad

theorem avoidance_smoothing_sandwich {P : Type*} [Fintype P] (a : P → ℕ)
    (A B : ℤ) (H J : ℕ) (hH : 0 < H) (G : ℤ → ℝ) (hG : ∀ n, 0 ≤ G n) :
    (∑ n ∈ lowerAvoidSet a A B (J * H), realBoxSmooth H J G n) ≤
      (∑ n ∈ originalAvoidSet a A B, G n) ∧
    (∑ n ∈ originalAvoidSet a A B, G n) ≤
      ∑ n ∈ upperAvoidSet a A B (J * H), realBoxSmooth H J G n := by
  apply smoothing_sandwich _ _ _ G H J hH hG
  · intro t ht0 htR n hn
    exact lowerAvoidSet_shift a A B (J * H) t ht0 (by exact_mod_cast htR) n hn
  · intro t ht0 htR n hn
    exact upperAvoidSet_shift a A B (J * H) t ht0 (by exact_mod_cast htR) n hn

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem periodic_sum_mul (f : ℕ → ℝ) (m k : ℕ) (hf : Function.Periodic f m) :
    (∑ i ∈ Finset.range (k * m), f i) = k * ∑ i ∈ Finset.range m, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift : (fun j => f (k * m + j)) = f := by
        funext j
        simpa [Nat.add_comm] using (hf.nat_mul k) j
      simp only [hshift, Nat.cast_add, Nat.cast_one]
      ring

theorem periodic_sum_decomposition (f : ℕ → ℝ) (m N : ℕ)
    (hf : Function.Periodic f m) :
    (∑ i ∈ Finset.range N, f i) =
      (N / m : ℕ) * (∑ i ∈ Finset.range m, f i) + ∑ i ∈ Finset.range (N % m), f i := by
  conv_lhs => rw [← Nat.div_add_mod N m]
  rw [Nat.mul_comm m (N / m), Finset.sum_range_add, periodic_sum_mul f m (N / m) hf]
  have hshift : (fun j => f (N / m * m + j)) = f := by
    funext j
    simpa [Nat.add_comm] using (hf.nat_mul (N / m)) j
  simp only [hshift]

theorem periodic_sum_error (f : ℕ → ℝ) (m N : ℕ) (hm : 0 < m)
    (hf : Function.Periodic f m) (hf0 : ∀ i, 0 ≤ f i) :
    |(∑ i ∈ Finset.range N, f i) -
        (N : ℝ) / m * (∑ i ∈ Finset.range m, f i)| ≤
      ∑ i ∈ Finset.range m, f i := by
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range m, f i := Finset.sum_nonneg (fun i _ => hf0 i)
  have hrem0 : 0 ≤ ∑ i ∈ Finset.range (N % m), f i :=
    Finset.sum_nonneg (fun i _ => hf0 i)
  have hrem : (∑ i ∈ Finset.range (N % m), f i) ≤ ∑ i ∈ Finset.range m, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.mod_lt N hm).le) (fun i _ _ => hf0 i)
  have hmod0 : (0 : ℝ) ≤ ((N % m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmod : ((N % m : ℕ) : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt N hm).le
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (N : ℝ) = (N / m : ℕ) * m + (N % m : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod N m).symm)
  have hratio : (N : ℝ) / m = (N / m : ℕ) + ((N % m : ℕ) : ℝ) / m := by
    apply (div_eq_iff (ne_of_gt hmreal)).mpr
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hmreal)]
    exact hN
  have hfract0 : 0 ≤ ((N % m : ℕ) : ℝ) / m := div_nonneg hmod0 hmreal.le
  have hfract1 : ((N % m : ℕ) : ℝ) / m ≤ 1 := (div_le_one hmreal).mpr hmod
  have hfracsum0 := mul_nonneg hfract0 hsum0
  have hfracsum1 := mul_le_mul_of_nonneg_right hfract1 hsum0
  rw [periodic_sum_decomposition f m N hf, hratio, abs_le]
  constructor <;> nlinarith

theorem periodic_sum_shift_period (f : ℕ → ℝ) (m S : ℕ)
    (hf : Function.Periodic f m) :
    (∑ i ∈ Finset.range m, f (S + i)) = ∑ i ∈ Finset.range m, f i := by
  have hshift : (fun i => f (m + i)) = f := by
    funext i
    simpa [Nat.add_comm] using hf i
  have h := congrArg (fun n => ∑ i ∈ Finset.range n, f i) (Nat.add_comm S m)
  simp only [Finset.sum_range_add, hshift] at h
  linarith


theorem periodic_double_average_upper (f : ℕ → ℝ) (m H : ℕ) (shift : ℕ → ℕ)
    (hm : 0 < m) (hH : 0 < H) (hf : Function.Periodic f m)
    (hf0 : ∀ i, 0 ≤ f i) (hmean : (∑ i ∈ Finset.range m, f i) = m) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H, f (shift j + i)) / (H : ℝ) ^ 2 ≤
      1 + (m : ℝ) / H := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hinner (j : ℕ) : (∑ i ∈ Finset.range H, f (shift j + i)) ≤ (H : ℝ) + m := by
    have hp : Function.Periodic (fun i => f (shift j + i)) m := by
      intro i
      simpa only [Nat.add_assoc] using hf (shift j + i)
    have h := (abs_le.mp (periodic_sum_error (fun i => f (shift j + i)) m H hm hp
      (fun i => hf0 _))).2
    rw [periodic_sum_shift_period f m (shift j) hf, hmean] at h
    rw [div_mul_cancel₀ _ (ne_of_gt hmreal)] at h
    linarith
  have htotal : (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H, f (shift j + i)) ≤
      (H : ℝ) * ((H : ℝ) + m) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.range H) => hinner j)
  apply (div_le_iff₀ (sq_pos_of_pos hHreal)).mpr
  have hid : (1 + (m : ℝ) / H) * (H : ℝ) ^ 2 = (H : ℝ) * ((H : ℝ) + m) := by
    field_simp
  rwa [hid]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem sum_range_zmod (m : ℕ) [NeZero m] (f : ZMod m → ℝ) :
    (∑ n ∈ Finset.range m, f (n : ZMod m)) = ∑ r : ZMod m, f r := by
  have he (i : Fin m) : ZMod.finEquiv m i = (i.val : ZMod m) := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt i.isLt]
    cases m with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ m => rfl
  rw [Finset.sum_range]
  have h := Equiv.sum_comp (ZMod.finEquiv m).toEquiv f
  change (∑ i : Fin m, f (ZMod.finEquiv m i)) = _ at h
  simpa only [he] using h

theorem crt_sum_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ r : ZMod (∏ i, m i), ∏ i,
      f i (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r)) =
      ∏ i, ∑ r : ZMod (m i), f i r := by
  calc
    _ = ∑ r : ∀ i, ZMod (m i), ∏ i, f i (r i) := by
      have h := Equiv.sum_comp (ZMod.prodEquivPi m hc).toEquiv (fun r => ∏ i, f i (r i))
      change (∑ r : ZMod (∏ i, m i), ∏ i, f i (ZMod.prodEquivPi m hc r i)) = _ at h
      simpa only [ZMod.prodEquivPi_apply] using h
    _ = _ := (Fintype.prod_sum f).symm

theorem crt_product_mean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ)
    (hf : ∀ i, (∑ r : ZMod (m i), f i r) = m i) :
    (∑ r : ZMod (∏ i, m i), ∏ i,
      f i (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r)) =
      (∏ i, m i : ℕ) := by
  rw [crt_sum_product m hc f]
  simp only [hf, Nat.cast_prod]

theorem crt_natural_sum_mean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ)
    (hf : ∀ i, (∑ r : ZMod (m i), f i r) = m i) :
    (∑ n ∈ Finset.range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) =
      (∏ i, m i : ℕ) := by
  have h := sum_range_zmod (∏ i, m i)
    (fun r => ∏ i, f i (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) _ r))
  simp only [map_natCast] at h
  rw [h]
  exact crt_product_mean_one m hc f hf

theorem crt_product_periodic {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (f : ∀ i, ZMod (m i) → ℝ) :
    Function.Periodic (fun n : ℕ => ∏ i, f i (n : ZMod (m i))) (∏ i, m i) := by
  intro n
  apply Finset.prod_congr rfl
  intro i _
  have hz : ((∏ j, m j : ℕ) : ZMod (m i)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
  rw [Nat.cast_add, hz, add_zero]

theorem crt_double_average_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ)
    (hf : ∀ i, (∑ r : ZMod (m i), f i r) = m i)
    (hf0 : ∀ i r, 0 ≤ f i r) (H : ℕ) (hH : 0 < H) (shift : ℕ → ℕ) :
    (∑ j ∈ Finset.range H, ∑ n ∈ Finset.range H,
      ∏ i, f i ((shift j + n : ℕ) : ZMod (m i))) / (H : ℝ) ^ 2 ≤
      1 + (∏ i, m i : ℕ) / (H : ℝ) := by
  exact periodic_double_average_upper (fun n => ∏ i, f i (n : ZMod (m i)))
    (∏ i, m i) H shift (Nat.pos_of_ne_zero (NeZero.ne _)) hH
    (crt_product_periodic m f) (fun _ => Finset.prod_nonneg (fun i _ => hf0 i _))
    (crt_natural_sum_mean_one m hc f hf)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem periodic_sum_upper_mean (f : ℕ → ℝ) (m H : ℕ) (μ : ℝ)
    (hm : 0 < m) (hf : Function.Periodic f m) (hf0 : ∀ i, 0 ≤ f i)
    (hmean : (∑ i ∈ Finset.range m, f i) ≤ (m : ℝ) * μ) :
    (∑ i ∈ Finset.range H, f i) ≤ ((H : ℝ) + m) * μ := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (abs_le.mp (periodic_sum_error f m H hm hf hf0)).2
  have hfactor : 0 ≤ (H : ℝ) / m + 1 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmean hfactor
  have hid : ((H : ℝ) / m + 1) * ((m : ℝ) * μ) = ((H : ℝ) + m) * μ := by
    field_simp
  rw [hid] at hscaled
  nlinarith

theorem zmod_double_average_upper (m H : ℕ) [NeZero m]
    (f : ZMod m → ℝ) (μ : ℝ) (hH : 0 < H) (hf0 : ∀ r, 0 ≤ f r)
    (hmean : (∑ r : ZMod m, f r) ≤ (m : ℝ) * μ) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      f ((i : ZMod m) - (j : ZMod m))) / (H : ℝ) ^ 2 ≤
        (1 + (m : ℝ) / H) * μ := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne _)
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hinner (j : ℕ) : (∑ i ∈ Finset.range H, f ((i : ZMod m) - (j : ZMod m))) ≤
      ((H : ℝ) + m) * μ := by
    have hp : Function.Periodic (fun i : ℕ => f ((i : ZMod m) - (j : ZMod m))) m := by
      intro i
      simp
    have hsum : (∑ i ∈ Finset.range m, f ((i : ZMod m) - (j : ZMod m))) = ∑ r : ZMod m, f r := by
      rw [sum_range_zmod m (fun r => f (r - (j : ZMod m)))]
      have h := Equiv.sum_comp (Equiv.addRight (-(j : ZMod m))) f
      change (∑ r : ZMod m, f (r + -(j : ZMod m))) = _ at h
      simpa only [sub_eq_add_neg] using h
    apply periodic_sum_upper_mean _ m H μ hm hp (fun i => hf0 _)
    rwa [hsum]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range H) => hinner j)
  have hsum' : (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      f ((i : ZMod m) - (j : ZMod m))) ≤ (H : ℝ) * (((H : ℝ) + m) * μ) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply (div_le_iff₀ (sq_pos_of_pos hHreal)).mpr
  have hid : ((1 + (m : ℝ) / H) * μ) * (H : ℝ) ^ 2 =
      (H : ℝ) * (((H : ℝ) + m) * μ) := by
    field_simp
  rwa [hid]

theorem crt_pair_average_upper {J : Type*} [Fintype J] [DecidableEq J]
    (m : J → ℕ) [∀ j, NeZero (m j)] [NeZero (∏ j, m j)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ j, ZMod (m j) → ℝ) (μ : J → ℝ)
    (hf0 : ∀ j r, 0 ≤ f j r)
    (hmean : ∀ j, (∑ r : ZMod (m j), f j r) ≤ (m j : ℝ) * μ j)
    (H : ℕ) (hH : 0 < H) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      ∏ t : J, f t ((i : ZMod (m t)) - (j : ZMod (m t)))) / (H : ℝ) ^ 2 ≤
        (1 + (∏ t, m t : ℕ) / (H : ℝ)) * (∏ t : J, μ t) := by
  let F (r : ZMod (∏ t, m t)) :=
    ∏ t : J, f t (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ t)) _ r)
  have hF0 : ∀ r, 0 ≤ F r := fun r => Finset.prod_nonneg (fun t _ => hf0 t _)
  have hFmean : (∑ r : ZMod (∏ t, m t), F r) ≤ (∏ t, m t : ℕ) * (∏ t : J, μ t) := by
    rw [crt_sum_product m hc f]
    calc
      _ ≤ ∏ t : J, (m t : ℝ) * μ t :=
        Finset.prod_le_prod (fun t _ => Finset.sum_nonneg (fun r _ => hf0 t r)) (fun t _ => hmean t)
      _ = _ := by rw [Finset.prod_mul_distrib, Nat.cast_prod]
  have h := zmod_double_average_upper (∏ t, m t) H F (∏ t : J, μ t) hH hF0 hFmean
  simpa only [F, map_sub, map_natCast] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem modular_interval_upper (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (S : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N, if (S + (n : ℤ) : ZMod m) ∈ A then (1 : ℝ) else 0) ≤
      ((N : ℝ) / m + 1) * A.card := by
  classical
  let F (r : ZMod m) : ℝ := if (S : ZMod m) + r ∈ A then 1 else 0
  have hperm := Equiv.sum_comp (Equiv.addLeft (S : ZMod m))
    (fun r : ZMod m => if r ∈ A then (1 : ℝ) else 0)
  change (∑ r : ZMod m, F r) = (∑ r : ZMod m, if r ∈ A then (1 : ℝ) else 0) at hperm
  have hsum : (∑ n ∈ Finset.range m, F (n : ZMod m)) = (A.card : ℝ) := by
    rw [sum_range_zmod m F, hperm]
    simp
  have hperiod : Function.Periodic (fun n : ℕ => F (n : ZMod m)) m := by
    intro n
    simp
  have hnonneg : ∀ n : ℕ, 0 ≤ F (n : ZMod m) := by intro n; dsimp [F]; split_ifs <;> norm_num
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hmean : (∑ n ∈ Finset.range m, F (n : ZMod m)) ≤ (m : ℝ) * (A.card / (m : ℝ)) := by
    rw [hsum]
    field_simp
    rfl
  have h := periodic_sum_upper_mean (fun n : ℕ => F (n : ZMod m)) m N (A.card / (m : ℝ))
    (Nat.pos_of_ne_zero (NeZero.ne m)) hperiod hnonneg hmean
  have hid : ((N : ℝ) + m) * (A.card / (m : ℝ)) = ((N : ℝ) / m + 1) * A.card := by
    field_simp
    <;> ring
  rw [hid] at h
  simpa only [F, Int.cast_add, Int.cast_natCast] using h

theorem prime_boundary_interval_upper (p R N : ℕ) (hp : p.Prime) (S : ℤ) :
    (∑ n ∈ Finset.range N, if (S + (n : ℤ) : ZMod (p ^ 2)) ∈ boundaryResidues (p ^ 2) p R
      then (1 : ℝ) else 0) ≤ 2 * R * ((N : ℝ) / (p : ℝ) ^ 2 + 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := modular_interval_upper (p ^ 2) (boundaryResidues (p ^ 2) p R) S N
  have hcard : ((boundaryResidues (p ^ 2) p R).card : ℝ) ≤ 2 * R := by
    exact_mod_cast boundaryResidues_card_le (p ^ 2) p R (by nlinarith [hp.two_le])
  have hmul := mul_le_mul_of_nonneg_left hcard
    (show 0 ≤ (N : ℝ) / (p : ℝ) ^ 2 + 1 by positivity)
  rw [Nat.cast_pow] at h
  nlinarith

theorem finite_union_indicator_le {P : Type*} [Fintype P] (B : P → Prop) [DecidablePred B] :
    (if ∃ p, B p then (1 : ℝ) else 0) ≤ ∑ p : P, if B p then 1 else 0 := by
  classical
  by_cases h : ∃ p, B p
  · obtain ⟨p, hp⟩ := h
    have hex : ∃ p, B p := ⟨p, hp⟩
    have hsingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun p => if B p then (1 : ℝ) else 0)
      (fun p hp => by split_ifs <;> norm_num) (Finset.mem_univ p)
    simpa only [hp, ite_true, hex] using hsingle
  · simp only [h, ite_false]
    exact Finset.sum_nonneg (fun p hp => by split_ifs <;> norm_num)

theorem family_boundary_interval_upper {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (R N : ℕ) (S : ℤ) :
    (∑ n ∈ Finset.range N, if ∃ p : P,
      (S + (n : ℤ) : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R
      then (1 : ℝ) else 0) ≤
      2 * R * ((N : ℝ) * (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) + Fintype.card P) := by
  classical
  have hpoint := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) =>
    finite_union_indicator_le (fun p : P =>
      (S + (n : ℤ) : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R))
  rw [Finset.sum_comm] at hpoint
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
    prime_boundary_interval_upper (a p) R N (hprime p) S)
  have hid : (∑ p : P, 2 * R * ((N : ℝ) / (a p : ℝ) ^ 2 + 1)) =
      2 * R * ((N : ℝ) * (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) + Fintype.card P) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, div_eq_mul_inv,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hid] at hsum
  exact hpoint.trans hsum

end Erdos676
end

section
namespace Erdos676

noncomputable def avoidanceBoundarySet {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc A B).filter (fun n => ∃ p,
    (n : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R)

theorem lower_avoidance_difference_bound {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    (originalAvoidSet a A B \ lowerAvoidSet a A B R).card ≤
      R + (avoidanceBoundarySet a A B R).card := by
  classical
  have hsub : originalAvoidSet a A B \ lowerAvoidSet a A B R ⊆
      Finset.Icc (B - R + 1) B ∪ avoidanceBoundarySet a A B R := by
    intro n hn
    obtain ⟨hnU, hnL⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hnU
    by_cases hcut : n ≤ B - R
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hnI, ?_⟩
      by_contra hnone
      push Not at hnone
      apply hnL
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, hcut⟩, ?_⟩
      intro p hp
      apply hnone p
      exact Finset.mem_sdiff.mpr ⟨hp, fun hc => hnA p (contracted_subset_initial _ _ _ hc)⟩
    · apply Finset.mem_union_left
      exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hnI).2⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hlayer : (Finset.Icc (B - R + 1) B).card = R := by rw [Int.card_Icc]; omega
  rwa [hlayer] at hcard

theorem upper_avoidance_difference_bound {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    (upperAvoidSet a A B R \ originalAvoidSet a A B).card ≤
      R + (avoidanceBoundarySet a A B R).card := by
  classical
  have hsub : upperAvoidSet a A B R \ originalAvoidSet a A B ⊆
      Finset.Icc (A - R) (A - 1) ∪ avoidanceBoundarySet a A B R := by
    intro n hn
    obtain ⟨hnV, hnU⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hnV
    by_cases hcut : A ≤ n
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hcut, (Finset.mem_Icc.mp hnI).2⟩, ?_⟩
      by_contra hnone
      push Not at hnone
      apply hnU
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hcut, (Finset.mem_Icc.mp hnI).2⟩, ?_⟩
      intro p hp
      exact hnone p (Finset.mem_sdiff.mpr ⟨initial_subset_expanded _ _ _ hp, hnA p⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1, by omega⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hlayer : (Finset.Icc (A - R) (A - 1)).card = R := by rw [Int.card_Icc]; omega
  rwa [hlayer] at hcard

theorem avoidance_card_bounds {P : Type*} [Fintype P]
    (a : P → ℕ) (A B : ℤ) (R : ℕ) :
    (originalAvoidSet a A B).card ≤ (lowerAvoidSet a A B R).card + R + (avoidanceBoundarySet a A B R).card ∧
    (upperAvoidSet a A B R).card ≤ (originalAvoidSet a A B).card + R + (avoidanceBoundarySet a A B R).card := by
  have hlo := lower_avoidance_difference_bound a A B R
  have hhi := upper_avoidance_difference_bound a A B R
  have hsplitL := Finset.card_sdiff_add_card_eq_card (lowerAvoidSet_subset a A B R)
  have hsplitV := Finset.card_sdiff_add_card_eq_card (originalAvoidSet_subset a A B R)
  omega

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem card_filter_real {I : Type*} (s : Finset I) (P : I → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ) = ∑ n ∈ s, if P n then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hPa : P a <;> simp [ha, hPa, ih]

theorem int_interval_image (S : ℤ) (N : ℕ) :
    (Finset.range N).image (fun n : ℕ => S + (n : ℤ)) = Finset.Icc S (S + N - 1) := by
  ext m
  constructor
  · intro hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hn' := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hnat : (((m - S).toNat : ℕ) : ℤ) = m - S := Int.toNat_of_nonneg (by omega)
    exact Finset.mem_image.mpr ⟨(m - S).toNat, Finset.mem_range.mpr (by omega), by omega⟩

theorem sum_int_interval {T : Type*} [AddCommMonoid T] (S : ℤ) (N : ℕ) (f : ℤ → T) :
    (∑ n ∈ Finset.Icc S (S + N - 1), f n) = ∑ n ∈ Finset.range N, f (S + n) := by
  rw [← int_interval_image S N]
  apply Finset.sum_image
  intro a ha b hb h
  exact_mod_cast (add_left_cancel h)

theorem int_enlarged_interval_card (S : ℤ) (N R : ℕ) :
    (Finset.Icc (S - R) (S + N - 1)).card = N + R := by
  rw [Int.card_Icc]
  omega

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem family_reciprocal_square_tail {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (m : ℕ) (hm : 0 < m)
    (hlo : ∀ p, m < a p) : (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by
  let s := Finset.univ.image a
  let N := max m (s.sup id)
  have hsub : s ⊆ Finset.Ioc m N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr ⟨hlo p, (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hsum : (∑ p : P, ((a p : ℝ) ^ 2)⁻¹) = ∑ n ∈ s, ((n : ℝ) ^ 2)⁻¹ := by
    symm
    apply Finset.sum_image
    intro p hp q hq h
    exact hinj h
  rw [hsum]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n hn hnot => by positivity : ∀ n, n ∈ Finset.Ioc m N → n ∉ s → 0 ≤ ((n : ℝ) ^ 2)⁻¹)
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (Nat.ne_of_gt hm) (le_max_left m (s.sup id))
  have hN0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
  linarith

theorem avoidance_boundary_card_bound {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (m : ℕ) (hm : 0 < m) (hlo : ∀ p, m < a p) (z : ℝ) (hz : 0 ≤ z)
    (hle : ∀ p, (a p : ℝ) ≤ z) (S : ℤ) (N R : ℕ) :
    ((avoidanceBoundarySet a S (S + N - 1) R).card : ℝ) ≤
      2 * R * ((N : ℝ) / m + z) := by
  classical
  have hcount := family_boundary_interval_upper a hprime R N S
  have htail := family_reciprocal_square_tail a hinj m hm hlo
  have hcard := prime_family_card_le a hinj hprime z hz hle
  have hinner := add_le_add (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg N)) hcard
  have hscaled := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * (R : ℝ) by positivity)
  have hsum : ((avoidanceBoundarySet a S (S + N - 1) R).card : ℝ) =
      ∑ n ∈ Finset.range N, if ∃ p : P,
        (S + (n : ℤ) : ZMod ((a p) ^ 2)) ∈ boundaryResidues ((a p) ^ 2) (a p) R then 1 else 0 := by
    unfold avoidanceBoundarySet
    rw [card_filter_real, sum_int_interval]
    simp only [Int.cast_add]
  rw [hsum]
  have h := hcount.trans hscaled
  simpa only [div_eq_mul_inv] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem avoidance_correlation_bound {P : Type*} [Fintype P] (a : P → ℕ)
    (A B : ℤ) (H J : ℕ) (hH : 0 < H) (G : ℤ → ℝ) (hG : ∀ n, 0 ≤ G n)
    (μ E : ℝ) (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (henergy : ∑ n ∈ Finset.Icc (A - (J * H : ℕ)) B,
      (realBoxSmooth H J G n - μ) ^ 2 ≤ E) :
    |(∑ n ∈ originalAvoidSet a A B, G n) - μ * (originalAvoidSet a A B).card| ≤
      Real.sqrt ((Finset.Icc (A - (J * H : ℕ)) B).card * E) +
        μ * ((J * H : ℕ) + (avoidanceBoundarySet a A B (J * H)).card) := by
  let R := J * H
  let W := Finset.Icc (A - (R : ℤ)) B
  have hVW : upperAvoidSet a A B R ⊆ W := Finset.filter_subset _ _
  have hLW : lowerAvoidSet a A B R ⊆ W :=
    (lowerAvoidSet_subset a A B R).trans ((originalAvoidSet_subset a A B R).trans hVW)
  have henergyL : ∑ n ∈ lowerAvoidSet a A B R, (realBoxSmooth H J G n - μ) ^ 2 ≤ E :=
    (Finset.sum_le_sum_of_subset_of_nonneg hLW (fun n hn hnot => sq_nonneg _)).trans henergy
  have henergyV : ∑ n ∈ upperAvoidSet a A B R, (realBoxSmooth H J G n - μ) ^ 2 ≤ E :=
    (Finset.sum_le_sum_of_subset_of_nonneg hVW (fun n hn hnot => sq_nonneg _)).trans henergy
  have hLM : ((lowerAvoidSet a A B R).card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hLW
  have hVM : ((upperAvoidSet a A B R).card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hVW
  have hcards := avoidance_card_bounds a A B R
  have hLU : ((originalAvoidSet a A B).card : ℝ) ≤ (lowerAvoidSet a A B R).card +
      ((R : ℝ) + (avoidanceBoundarySet a A B R).card) := by
    exact_mod_cast (by simpa only [Nat.add_assoc] using hcards.1)
  have hUV : ((upperAvoidSet a A B R).card : ℝ) ≤ (originalAvoidSet a A B).card +
      ((R : ℝ) + (avoidanceBoundarySet a A B R).card) := by
    exact_mod_cast (by simpa only [Nat.add_assoc] using hcards.2)
  have hsand := avoidance_smoothing_sandwich a A B H J hH G hG
  exact correlation_from_smoothing_bounds _ _ _ G (realBoxSmooth H J G) μ E W.card
    ((R : ℝ) + (avoidanceBoundarySet a A B R).card) hμ hE hsand.1 hsand.2 henergyL henergyV hLM hVM hLU hUV

theorem avoidance_correlation_explicit {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (hinj : Function.Injective a)
    (m : ℕ) (hm : 0 < m) (hlo : ∀ p, m < a p) (z : ℝ) (hz : 0 ≤ z) (hle : ∀ p, (a p : ℝ) ≤ z)
    (S : ℤ) (N H J : ℕ) (hH : 0 < H) (G : ℤ → ℝ) (hG : ∀ n, 0 ≤ G n)
    (μ E : ℝ) (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (henergy : ∑ n ∈ Finset.Icc (S - (J * H : ℕ)) (S + N - 1),
      (realBoxSmooth H J G n - μ) ^ 2 ≤ E) :
    |(∑ n ∈ originalAvoidSet a S (S + N - 1), G n) - μ * (originalAvoidSet a S (S + N - 1)).card| ≤
      Real.sqrt (((N : ℝ) + J * H) * E) + μ * ((J * H : ℕ) + 2 * (J * H : ℕ) * ((N : ℝ) / m + z)) := by
  have h := avoidance_correlation_bound a S (S + N - 1) H J hH G hG μ E hμ hE henergy
  have hb := avoidance_boundary_card_bound a hprime hinj m hm hlo z hz hle S N (J * H)
  rw [int_enlarged_interval_card, Nat.cast_add, Nat.cast_mul] at h
  have hscaled := mul_le_mul_of_nonneg_left hb hμ
  simp only [Nat.cast_mul] at hscaled ⊢
  nlinarith

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem eventually_box_radius_le {η : ℝ} (hη : η < 1) (J : ℕ) :
    ∀ᶠ x : ℝ in atTop, (J : ℝ) * (powerFloor η x : ℝ) ≤ x := by
  filter_upwards [(tendsto_rpow_atTop (by linarith : 0 < 1 - η)).eventually_ge_atTop (J : ℝ),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hfloor : (powerFloor η x : ℝ) ≤ x ^ η := Nat.floor_le (Real.rpow_nonneg hx0.le η)
  calc
    _ ≤ (J : ℝ) * x ^ η := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg J)
    _ ≤ x ^ (1 - η) * x ^ η := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le η)
    _ = x := by rw [← Real.rpow_add hx0, show 1 - η + η = 1 by ring, Real.rpow_one]

theorem boundary_ratio_bound {x c : ℝ} (hx : 1 ≤ x) (hc : c ≤ 1 / 2) (hlarge : 4 ≤ x ^ c) :
    x / (⌊x ^ c / 2⌋₊ : ℝ) + 2 * x ^ (1 / 2 : ℝ) ≤ 6 * x ^ (1 - c) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hfloor : x ^ c / 4 ≤ (⌊x ^ c / 2⌋₊ : ℝ) := by
    have h := floor_ge_half (show 2 ≤ x ^ c / 2 by linarith)
    nlinarith
  have hden : 0 < x ^ c / 4 := by positivity
  have hdiv := div_le_div_of_nonneg_left hx0.le hden hfloor
  have heq : x / (x ^ c / 4) = 4 * x ^ (1 - c) := by
    rw [Real.rpow_sub hx0, Real.rpow_one]
    ring
  rw [heq] at hdiv
  have hpow := Real.rpow_le_rpow_of_exponent_le hx (show (1 / 2 : ℝ) ≤ 1 - c by linarith)
  linarith

theorem boundary_error_power_bound {x R c η : ℝ} (hx : 1 ≤ x) (hc : c ≤ 1 / 2)
    (hlarge : 4 ≤ x ^ c) (hR : 0 ≤ R) (J : ℕ) (hRupper : R ≤ J * x ^ η) :
    R + 2 * R * (x / (⌊x ^ c / 2⌋₊ : ℝ) + 2 * x ^ (1 / 2 : ℝ)) ≤
      13 * J * x ^ (1 + η - c) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hratio := boundary_ratio_bound hx hc hlarge
  have hp : 1 ≤ x ^ (1 - c) := Real.one_le_rpow hx (by linarith)
  have hterm := mul_le_mul_of_nonneg_left hratio (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hR)
  have hbase := mul_le_mul_of_nonneg_left hp hR
  have hrhs := mul_le_mul_of_nonneg_right hRupper (show 0 ≤ 13 * x ^ (1 - c) by positivity)
  have hprod : x ^ η * x ^ (1 - c) = x ^ (1 + η - c) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [mul_assoc (J : ℝ) (x ^ η) (13 * x ^ (1 - c))] at hrhs
  have hconvert : (J : ℝ) * (x ^ η * (13 * x ^ (1 - c))) = 13 * J * x ^ (1 + η - c) := by
    rw [mul_left_comm (x ^ η) 13, hprod]
    ring
  rw [hconvert] at hrhs
  nlinarith

theorem correlation_sqrt_power_bound {x R ε : ℝ} (hx : 0 < x) (hR : R ≤ x) :
    Real.sqrt ((x + R) * (8200 * x ^ (1 - ε))) ≤ 200 * x ^ (1 - ε / 2) := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right (show x + R ≤ 2 * x by linarith)
    (show 0 ≤ 8200 * x ^ (1 - ε) by positivity)
  have hpow : (x ^ (1 - ε / 2)) ^ 2 = x * x ^ (1 - ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num only [Nat.cast_ofNat]
    have heq : (1 - ε / 2) * (2 : ℝ) = 1 + (1 - ε) := by ring
    rw [heq, Real.rpow_add hx, Real.rpow_one]
  rw [mul_pow, hpow]
  nlinarith

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem prime_family_reciprocal_band_le {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (y z : ℝ) (hyz : y ≤ z) (hlo : ∀ p, y < a p) (hhi : ∀ p, (a p : ℝ) ≤ z) :
    (∑ p : P, 1 / (a p : ℝ)) ≤ primeReciprocalSum z - primeReciprocalSum y := by
  have hsub : Finset.univ.image a ⊆ primesUpToReal z \ primesUpToReal y := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_primesUpToReal z (a p)).mpr ⟨hprime p, hhi p⟩, ?_⟩
    intro hmem
    exact (not_le_of_gt (hlo p)) ((mem_primesUpToReal y (a p)).mp hmem).2
  have himage : (∑ p : P, 1 / (a p : ℝ)) = ∑ q ∈ Finset.univ.image a, 1 / (q : ℝ) := by
    symm
    apply Finset.sum_image
    intro p hp q hq h
    exact hinj h
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p hp hnot => by positivity : ∀ p, p ∈ primesUpToReal z \ primesUpToReal y →
      p ∉ Finset.univ.image a → 0 ≤ 1 / (p : ℝ))
  have hsplit := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) (primesUpToReal_subset hyz)
  rw [himage]
  change (∑ q ∈ primesUpToReal z \ primesUpToReal y, 1 / (q : ℝ)) + primeReciprocalSum y =
    primeReciprocalSum z at hsplit
  linarith

universe u

theorem exists_prime_band_reciprocal_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (p : P → ℕ),
        Function.Injective p → (∀ i, (p i).Prime) → (∀ i, X ^ a ≤ (p i : ℝ)) →
        (∀ i, (p i : ℝ) ≤ X ^ b) → (∑ i : P, 1 / (p i : ℝ)) ≤ C := by
  let limit := Real.log b - Real.log (a / 2)
  have hb : 0 < b := ha.trans_le hab
  have hlimit := prime_power_band_limit (a / 2) b (by positivity) hb
  have hnear : ∀ᶠ X : ℝ in atTop, primeReciprocalSum (X ^ b) - primeReciprocalSum (X ^ (a / 2)) < limit + 1 :=
    (tendsto_order.mp hlimit).2 _ (by dsimp [limit]; linarith)
  refine ⟨|limit| + 2, by positivity, ?_⟩
  filter_upwards [hnear, eventually_gt_atTop (1 : ℝ)] with X hX hx
  intro P instF instD p hinj hprime hlo hhi
  have hstrict : X ^ (a / 2) < X ^ a := Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)
  have horder : X ^ (a / 2) ≤ X ^ b := hstrict.le.trans (Real.rpow_le_rpow_of_exponent_le hx.le hab)
  have h := prime_family_reciprocal_band_le p hinj hprime _ _ horder
    (fun i => hstrict.trans_le (hlo i)) hhi
  linarith [le_abs_self limit]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def primeBandCount {P : Type*} [Fintype P] (a : P → ℕ) (n : ℤ) : ℝ := by
  classical
  exact ∑ p : P, if (n : ZMod ((a p) ^ 2)) ∈ smallResidues (a p) then 1 else 0

theorem primeBandCount_nonneg {P : Type*} [Fintype P] (a : P → ℕ) (n : ℤ) :
    0 ≤ primeBandCount a n := by
  classical
  unfold primeBandCount
  exact Finset.sum_nonneg (fun p hp => by split_ifs <;> norm_num)

theorem coe_primeBandCount {P : Type*} [Fintype P] (a : P → ℕ) [∀ p, NeZero (a p)] (n : ℤ) :
    (primeBandCount a n : ℂ) = primeBandSignal a n := by
  classical
  unfold primeBandCount primeBandSignal
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with h <;> simp [residueIndicator, h]

theorem primeBandCount_energy_identity {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (H J : ℕ) (n : ℤ) :
    (realBoxSmooth H J (primeBandCount a) n - (∑ p : P, 1 / (a p : ℝ))) ^ 2 =
      ‖boxSmooth H J (primeBandSignal a) n - (∑ p : P, 1 / (a p : ℂ))‖ ^ 2 := by
  have hfun : (fun k => (primeBandCount a k : ℂ)) = primeBandSignal a := funext (coe_primeBandCount a)
  have hcoe : ((realBoxSmooth H J (primeBandCount a) n - (∑ p : P, 1 / (a p : ℝ)) : ℝ) : ℂ) =
      boxSmooth H J (primeBandSignal a) n - (∑ p : P, 1 / (a p : ℂ)) := by
    rw [Complex.ofReal_sub, coe_realBoxSmooth, hfun]
    simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [← hcoe, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

universe u v

theorem high_prime_averaging {a b η c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 4) (hbη : b < η) (hηc : η < c) (hc : c ≤ 1 / 2) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (p : P → ℕ) [∀ i, NeZero (p i)],
        (∀ i, (p i).Prime) → Function.Injective p → (∀ i, (X : ℝ) ^ a ≤ p i) →
        (∀ i, (p i : ℝ) ≤ (X : ℝ) ^ b) →
      ∀ (Q : Type v) [Fintype Q] [DecidableEq Q] (q : Q → ℕ) [∀ i, NeZero (q i)],
        (∀ i, (q i).Prime) → Function.Injective q → (∀ i, (X : ℝ) ^ c ≤ q i) →
        (∀ i, (q i : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) →
        |(∑ n ∈ originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ)), primeBandCount p n) -
          (∑ i : P, 1 / (p i : ℝ)) * (originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ))).card| ≤
            K * (X : ℝ) ^ (1 - δ) := by
  let ε := (η - b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hb0 : 0 < b := ha.trans_le hab
  have hη0 : 0 < η := hb0.trans hbη
  have hc0 : 0 < c := hη0.trans hηc
  have hrelation : η = b + 2 * ε := by dsimp [ε]; ring
  obtain ⟨J, henergy⟩ := growing_prime_band_energy hb0 hb hε hrelation
  obtain ⟨C, hC, hreciprocal⟩ := exists_prime_band_reciprocal_bound ha hab
  let δ := min (ε / 2) (c - η)
  let K := 200 + 13 * J * C
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, δ, hK, hδ, ?_⟩
  filter_upwards [henergy,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreciprocal,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (growing_fourier_cutoffs hε hη0 hrelation),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_box_radius_le (by linarith : η < 1) J),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually ((tendsto_rpow_atTop hc0).eventually_ge_atTop 4)]
    with X henergyX hrecX hcutX hradius hcX
  intro P instP instDP p instNP hp hinjp hlop hhip Q instQ instDQ q instNQ hq hinjq hloq hhiq
  obtain ⟨hx, hH, hhalf, hD, hsmall⟩ := hcutX
  have hx0 : (0 : ℝ) < X := zero_lt_one.trans_le hx
  have hXnat : 0 < X := by exact_mod_cast hx0
  let H := powerFloor η X
  let R := J * H
  let m := ⌊(X : ℝ) ^ c / 2⌋₊
  let μ := ∑ i : P, 1 / (p i : ℝ)
  let E := 8200 * (X : ℝ) ^ (1 - ε)
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun i hi => by positivity)
  have hμC : μ ≤ C := hrecX P p hinjp hp hlop hhip
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hRreal : (R : ℝ) ≤ X := by simpa only [R, H, Nat.cast_mul] using hradius
  have hRnat : R ≤ X := by exact_mod_cast hRreal
  have hm1 : 1 ≤ m := Nat.le_floor (by norm_num only [Nat.cast_one]; linarith)
  have hm : 0 < m := by omega
  have hmlow : (m : ℝ) ≤ (X : ℝ) ^ c / 2 := Nat.floor_le (by positivity)
  have hmq (i : Q) : m < q i := by
    have hi := hloq i
    have hpow : 0 < (X : ℝ) ^ c := Real.rpow_pos_of_pos hx0 c
    exact_mod_cast (show (m : ℝ) < (q i : ℝ) by linarith)
  have henergy0 := henergyX P p hp hinjp hhip 0
  have hframe : Finset.Icc ((X : ℤ) + 1 - R) (2 * (X : ℤ)) ⊆
      Finset.Icc 0 ((4 * X : ℕ) - 1 : ℤ) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have henergyAll : (∑ n ∈ Finset.Icc 0 ((4 * X : ℕ) - 1 : ℤ),
      (realBoxSmooth H J (primeBandCount p) n - μ) ^ 2) ≤ E := by
    rw [show ((4 * X : ℕ) - 1 : ℤ) = (0 : ℤ) + (4 * X : ℕ) - 1 by omega,
      sum_int_interval]
    dsimp only [μ]
    simp_rw [primeBandCount_energy_identity]
    simpa only [zero_add] using henergy0
  have henergyFrame := (Finset.sum_le_sum_of_subset_of_nonneg hframe
    (fun n hn hnot => sq_nonneg (realBoxSmooth H J (primeBandCount p) n - μ))).trans henergyAll
  have hend : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  have hcorr := avoidance_correlation_explicit q hq hinjq m hm hmq
    (2 * (X : ℝ) ^ (1 / 2 : ℝ)) (by positivity) hhiq ((X : ℤ) + 1) X H J hH
    (primeBandCount p) (primeBandCount_nonneg p) μ E hμ hE (by simpa only [hend] using henergyFrame)
  rw [hend] at hcorr
  have hsqrt := correlation_sqrt_power_bound hx0 hRreal (ε := ε)
  have hRupper : (R : ℝ) ≤ J * (X : ℝ) ^ η :=
    by simpa only [R, H, powerFloor, Nat.cast_mul] using
      (mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hx0.le η)) (Nat.cast_nonneg J))
  have hboundary := boundary_error_power_bound hx hc hcX (Nat.cast_nonneg R) J hRupper
  have hboundary0 : 0 ≤ (R : ℝ) + 2 * R * ((X : ℝ) / m + 2 * (X : ℝ) ^ (1 / 2 : ℝ)) := by positivity
  have hμbound := mul_le_mul_of_nonneg_left hboundary hμ
  have hCbound := mul_le_mul_of_nonneg_right hμC (show 0 ≤ 13 * J * (X : ℝ) ^ (1 + η - c) by positivity)
  have hpow1 := Real.rpow_le_rpow_of_exponent_le hx (show 1 - ε / 2 ≤ 1 - δ by dsimp [δ]; have := min_le_left (ε / 2) (c - η); linarith)
  have hpow2 := Real.rpow_le_rpow_of_exponent_le hx (show 1 + η - c ≤ 1 - δ by dsimp [δ]; have := min_le_right (ε / 2) (c - η); linarith)
  have hp1 := mul_le_mul_of_nonneg_left hpow1 (by norm_num : (0 : ℝ) ≤ 200)
  have hp2 := mul_le_mul_of_nonneg_left hpow2 (show 0 ≤ 13 * J * C by positivity)
  change |(∑ n ∈ originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ)), primeBandCount p n) -
    μ * (originalAvoidSet q ((X : ℤ) + 1) (2 * (X : ℤ))).card| ≤ K * (X : ℝ) ^ (1 - δ)
  dsimp only [E] at hcorr
  dsimp only [R, H, m] at hsqrt hμbound
  simp only [Nat.cast_mul] at hcorr hsqrt hμbound
  dsimp only [K]
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem avoid_indicator_lower {P : Type*} [Fintype P] (B : P → Prop) [DecidablePred B] :
    1 - (∑ p : P, if B p then (1 : ℝ) else 0) ≤ if ∀ p, ¬B p then 1 else 0 := by
  classical
  have h := finite_union_indicator_le B
  by_cases hall : ∀ p, ¬B p
  · simp [hall]
  · have hex : ∃ p, B p := by simpa only [not_forall, not_not] using hall
    simp only [hall, hex, ite_true, ite_false] at h ⊢
    linarith

theorem avoid_filter_card_lower {I P : Type*} [Fintype P] (U : Finset I)
    (B : P → I → Prop) [∀ p, DecidablePred (B p)] :
    letI : DecidablePred (fun n => ∀ p, ¬B p n) := Classical.decPred _
    (U.card : ℝ) - (∑ n ∈ U, ∑ p : P, if B p n then (1 : ℝ) else 0) ≤
      (U.filter (fun n => ∀ p, ¬B p n)).card := by
  classical
  have h := Finset.sum_le_sum (fun n (_ : n ∈ U) => avoid_indicator_lower (fun p => B p n))
  have hcard : ((U.filter (fun n => ∀ p, ¬B p n)).card : ℝ) =
      ∑ n ∈ U, if ∀ p, ¬B p n then (1 : ℝ) else 0 := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert n U hn ih => by_cases hcond : ∀ p, ¬B p n <;> simp [hn, hcond, ih]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [← hcard] at h
  convert! h using 2 <;> apply congrArg <;> ext n <;> simp

theorem avoidance_block_lower {I P : Type*} [Fintype P] (U : Finset I)
    (B : P → I → Prop) [∀ p, DecidablePred (B p)] (mass error : ℝ)
    (hcount : (∑ n ∈ U, ∑ p : P, if B p n then (1 : ℝ) else 0) ≤ mass * U.card + error) :
    letI : DecidablePred (fun n => ∀ p, ¬B p n) := Classical.decPred _
    (1 - mass) * U.card - error ≤ (U.filter (fun n => ∀ p, ¬B p n)).card := by
  have h := avoid_filter_card_lower U B
  nlinarith

theorem finite_affine_iteration_lower (y : ℕ → ℝ) (d e : ℝ) (N : ℕ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e)
    (hstep : ∀ n < N, d * y n - e ≤ y (n + 1)) :
    d ^ N * y 0 - N * e ≤ y N := by
  have haux : ∀ n ≤ N, d ^ n * y 0 - n * e ≤ y n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hprev := ih (by omega)
        have hrec := hstep n (by omega)
        have hscaled := mul_le_mul_of_nonneg_left hprev hd0
        have herror := mul_le_mul_of_nonneg_right hd1 (show 0 ≤ (n : ℝ) * e by positivity)
        rw [pow_succ]
        push_cast
        nlinarith
  exact haux N le_rfl

end Erdos676
end

section
open scoped BigOperators
open Filter
open scoped Topology

namespace Erdos676

noncomputable def primeAvoidSet (s : Finset ℕ) (A B : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Icc A B).filter (fun n => ∀ p ∈ s,
    (n : ZMod (p ^ 2)) ∉ initialResidues (p ^ 2) p)

noncomputable def primeWitnessCount (s : Finset ℕ) (n : ℤ) : ℝ := by
  classical
  exact ∑ p ∈ s, if (n : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then 1 else 0

noncomputable def primeMass (s : Finset ℕ) : ℝ := ∑ p ∈ s, 1 / (p : ℝ)

theorem primeAvoidSet_subtype (s : Finset ℕ) (A B : ℤ) :
    originalAvoidSet (fun p : s => (p : ℕ)) A B = primeAvoidSet s A B := by
  classical
  ext n
  simp [originalAvoidSet, primeAvoidSet]

theorem primeBandCount_subtype (s : Finset ℕ) (n : ℤ) :
    primeBandCount (fun p : s => (p : ℕ)) n = primeWitnessCount s n := by
  classical
  unfold primeBandCount primeWitnessCount
  have h := Finset.sum_coe_sort s (fun p : ℕ =>
    if (n : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then (1 : ℝ) else 0)
  exact h

theorem primeMass_subtype (s : Finset ℕ) :
    (∑ p : s, (1 : ℝ) / (p : ℕ)) = primeMass s := by
  exact Finset.sum_coe_sort s (fun p : ℕ => 1 / (p : ℝ))

theorem primeAvoidSet_mono {s t : Finset ℕ} (hst : s ⊆ t) (A B : ℤ) :
    primeAvoidSet t A B ⊆ primeAvoidSet s A B := by
  classical
  intro n hn
  obtain ⟨hnI, hnP⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hnI, fun p hp => hnP p (hst hp)⟩

theorem primeAvoidSet_union (s t : Finset ℕ) (A B : ℤ) :
    primeAvoidSet (s ∪ t) A B = (primeAvoidSet s A B).filter
      (fun n => ∀ p ∈ t, (n : ZMod (p ^ 2)) ∉ initialResidues (p ^ 2) p) := by
  classical
  ext n
  simp only [primeAvoidSet, Finset.mem_filter, Finset.mem_union]
  aesop

theorem prime_avoidance_step (s t : Finset ℕ) (A B : ℤ) (mass error : ℝ)
    (hcount : (∑ n ∈ primeAvoidSet s A B, primeWitnessCount t n) ≤
      mass * (primeAvoidSet s A B).card + error) :
    (1 - mass) * (primeAvoidSet s A B).card - error ≤ (primeAvoidSet (s ∪ t) A B).card := by
  classical
  have hsum : (∑ n ∈ primeAvoidSet s A B, ∑ p : t,
      if (n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p then (1 : ℝ) else 0) ≤
      mass * (primeAvoidSet s A B).card + error := by
    have heq (n : ℤ) : (∑ p : t,
        if (n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p then (1 : ℝ) else 0) =
        primeWitnessCount t n :=
      Finset.sum_coe_sort t (fun p : ℕ =>
        if (n : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then (1 : ℝ) else 0)
    simpa only [heq] using hcount
  have h := avoidance_block_lower (primeAvoidSet s A B)
    (fun (p : t) n => (n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p) mass error hsum
  have hset : (primeAvoidSet s A B).filter
      (fun n => ∀ p : t, ¬(n : ZMod ((p : ℕ) ^ 2)) ∈ initialResidues ((p : ℕ) ^ 2) p) =
      primeAvoidSet (s ∪ t) A B := by
    ext n
    simp only [primeAvoidSet, Finset.mem_filter, Finset.mem_union]
    aesop
  convert h using 1
  apply congrArg (fun z : Finset ℤ => (z.card : ℝ))
  ext n
  simp only [primeAvoidSet, Finset.mem_filter, Finset.mem_union]
  aesop

theorem prime_set_high_averaging {a b η c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 4) (hbη : b < η) (hηc : η < c) (hc : c ≤ 1 / 2) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      ∀ s t : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ t, p.Prime) →
        (∀ p ∈ s, (X : ℝ) ^ c ≤ p) → (∀ p ∈ s, (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) →
        (∀ p ∈ t, (X : ℝ) ^ a ≤ p) → (∀ p ∈ t, (p : ℝ) ≤ (X : ℝ) ^ b) →
        |(∑ n ∈ primeAvoidSet s ((X : ℤ) + 1) (2 * X), primeWitnessCount t n) -
          primeMass t * (primeAvoidSet s ((X : ℤ) + 1) (2 * X)).card| ≤ K * (X : ℝ) ^ (1 - δ) := by
  obtain ⟨K, δ, hK, hδ, h⟩ := high_prime_averaging ha hab hb hbη hηc hc
  refine ⟨K, δ, hK, hδ, ?_⟩
  filter_upwards [h] with X hX
  intro s t hs ht hslo hshi htlo hthi
  letI (p : s) : NeZero (p : ℕ) := ⟨(hs p p.property).ne_zero⟩
  letI (p : t) : NeZero (p : ℕ) := ⟨(ht p p.property).ne_zero⟩
  have hbound := hX t (fun p : t => (p : ℕ)) (fun p => ht p p.property) Subtype.val_injective
    (fun p => htlo p p.property) (fun p => hthi p p.property)
    s (fun p : s => (p : ℕ)) (fun p => hs p p.property) Subtype.val_injective
    (fun p => hslo p p.property) (fun p => hshi p p.property)
  simpa only [primeAvoidSet_subtype, primeBandCount_subtype, primeMass_subtype] using hbound

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

noncomputable def discreteCutoff (L : ℕ) : ℝ := (1 / 2 : ℝ) ^ L

theorem discreteCutoff_pos (L : ℕ) : 0 < discreteCutoff L := by
  unfold discreteCutoff
  positivity

theorem discreteCutoff_tendsto : Tendsto discreteCutoff atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem discreteCutoff_degree_tendsto :
    Tendsto (fun L : ℕ => discreteCutoff L * (8 * L + 8 : ℕ)) atTop (nhds (0 : ℝ)) := by
  have hlinear := tendsto_self_mul_const_pow_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have h := (hlinear.const_mul 8).add (discreteCutoff_tendsto.const_mul 8)
  convert h using 1
  · ext L
    simp only [discreteCutoff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · norm_num

theorem truncation_loss_discrete (C : ℝ) (L : ℕ) :
    2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) =
      (2 * Real.exp (4 * C)) * (discreteCutoff L) ^ 2 := by
  unfold discreteCutoff
  rw [← pow_mul, Nat.mul_comm L 2, one_div_pow]
  ring

theorem exists_discrete_cutoff_parameters {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ L : ℕ, 1 ≤ L ∧ discreteCutoff L < 1 / 4 ∧
      discreteCutoff L * (8 * L + 8 : ℕ) ≤ 1 / 2 ∧
      C * (discreteCutoff L) ^ 2 < (c / 8) * discreteCutoff L := by
  have hsmall : ∀ᶠ L in atTop, discreteCutoff L < min (1 / 4) (c / (8 * C)) :=
    (tendsto_order.mp discreteCutoff_tendsto).2 _ (lt_min (by norm_num) (by positivity))
  have hdegree : ∀ᶠ L in atTop, discreteCutoff L * (8 * L + 8 : ℕ) < (1 / 2 : ℝ) :=
    (tendsto_order.mp discreteCutoff_degree_tendsto).2 _ (by norm_num)
  obtain ⟨L, hL, hs, hd⟩ := ((eventually_ge_atTop 1).and (hsmall.and hdegree)).exists
  refine ⟨L, hL, lt_of_lt_of_le hs (min_le_left _ _), hd.le, ?_⟩
  have hratio := lt_of_lt_of_le hs (min_le_right _ _)
  have hprod := (lt_div_iff₀ (by positivity : 0 < 8 * C)).mp hratio
  have hscaled := mul_lt_mul_of_pos_right hprod (discreteCutoff_pos L)
  nlinarith

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

noncomputable def dyadicRetention : ℝ := 1 - Real.log 2

theorem log_two_lt_three_fourths : Real.log 2 < 3 / 4 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
  norm_num at h
  linarith

theorem dyadicRetention_bounds : (1 / 4 : ℝ) < dyadicRetention ∧ dyadicRetention < 1 := by
  have hlogpos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  dsimp [dyadicRetention]
  constructor <;> linarith [log_two_lt_three_fourths]

theorem discreteCutoff_sq (L : ℕ) : (discreteCutoff L) ^ 2 = (1 / 4 : ℝ) ^ L := by
  unfold discreteCutoff
  rw [pow_two, ← mul_pow]
  norm_num

theorem exists_dyadic_retention_margin {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ L : ℕ, 3 ≤ L ∧ discreteCutoff L ≤ 1 / 200 ∧
      discreteCutoff L * (8 * L + 8 : ℕ) ≤ 1 / 2 ∧
      C * (discreteCutoff L) ^ 2 < c * dyadicRetention ^ L := by
  have hd : 0 < dyadicRetention := lt_trans (by norm_num) dyadicRetention_bounds.1
  let r := (1 / 4 : ℝ) / dyadicRetention
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := (div_lt_one hd).mpr dyadicRetention_bounds.1
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  have hsmall : ∀ᶠ L : ℕ in atTop, C * r ^ L < c := by
    exact (tendsto_order.mp (by simpa only [mul_zero] using hlim)).2 c hc
  have hcut : ∀ᶠ L : ℕ in atTop, discreteCutoff L < 1 / 200 :=
    (tendsto_order.mp discreteCutoff_tendsto).2 _ (by norm_num)
  have hdegree : ∀ᶠ L : ℕ in atTop, discreteCutoff L * (8 * L + 8 : ℕ) < 1 / 2 :=
    (tendsto_order.mp discreteCutoff_degree_tendsto).2 _ (by norm_num)
  obtain ⟨L, hL, hsmallL, hcutL, hdegreeL⟩ :=
    ((eventually_ge_atTop 3).and (hsmall.and (hcut.and hdegree))).exists
  refine ⟨L, hL, hcutL.le, hdegreeL.le, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hsmallL (pow_pos hd L)
  have hid : r ^ L * dyadicRetention ^ L = (discreteCutoff L) ^ 2 := by
    rw [← mul_pow, discreteCutoff_sq]
    dsimp [r]
    rw [div_mul_cancel₀ _ hd.ne']
  nlinarith [hid]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def highPrimeLevel (j : ℕ) : ℝ := (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j
noncomputable def highPrimeBlockUpper (τ : ℝ) (j : ℕ) : ℝ := (1 - τ) * highPrimeLevel j

theorem highPrimeLevel_pos (j : ℕ) : 0 < highPrimeLevel j := by unfold highPrimeLevel; positivity

theorem highPrimeLevel_zero : highPrimeLevel 0 = 1 / 4 := by simp [highPrimeLevel]

theorem highPrimeLevel_succ (j : ℕ) : highPrimeLevel (j + 1) = highPrimeLevel j / 2 := by
  simp only [highPrimeLevel, pow_succ]
  ring

theorem highPrimeLevel_le_quarter (j : ℕ) : highPrimeLevel j ≤ 1 / 4 := by
  have h : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold highPrimeLevel
  linarith

theorem highPrimeLevel_discrete (j : ℕ) : highPrimeLevel j = discreteCutoff (j + 2) := by
  simp only [highPrimeLevel, discreteCutoff, pow_add]
  norm_num
  ring

theorem highPrimeBlock_bounds {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    0 < highPrimeLevel (j + 1) ∧ highPrimeLevel (j + 1) < highPrimeBlockUpper τ j ∧
      highPrimeBlockUpper τ j < highPrimeLevel j ∧ highPrimeLevel j ≤ 1 / 4 := by
  have hj := highPrimeLevel_pos j
  rw [highPrimeLevel_succ]
  dsimp only [highPrimeBlockUpper]
  refine ⟨by positivity, ?_, ?_, highPrimeLevel_le_quarter j⟩ <;> nlinarith

theorem highPrimeBlock_log_mass {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    Real.log (highPrimeBlockUpper τ j) - Real.log (highPrimeLevel (j + 1)) < Real.log 2 := by
  have hj := highPrimeLevel_pos j
  have hone : 0 < 1 - τ := by linarith
  have hden : highPrimeLevel (j + 1) ≠ 0 := (highPrimeLevel_pos (j + 1)).ne'
  have hnum : highPrimeBlockUpper τ j ≠ 0 := mul_ne_zero hone.ne' hj.ne'
  have hratio : highPrimeBlockUpper τ j / highPrimeLevel (j + 1) = 2 * (1 - τ) := by
    rw [highPrimeLevel_succ]
    unfold highPrimeBlockUpper
    field_simp
  rw [← Real.log_div hnum hden, hratio]
  apply Real.log_lt_log (by positivity)
  linarith

theorem highPrimeGap_log_mass {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1) (j : ℕ) :
    Real.log (highPrimeLevel j) - Real.log (highPrimeBlockUpper τ j) = -Real.log (1 - τ) := by
  rw [highPrimeBlockUpper, Real.log_mul (by positivity : 1 - τ ≠ 0) (highPrimeLevel_pos j).ne']
  ring

theorem highPrimeGap_loss_le {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) :
    -Real.log (1 - τ) ≤ 2 * τ := by
  have hpos : 0 < 1 - τ := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos zero_lt_one hpos)
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hpos.ne', Real.log_one, zero_sub] at h
  have hdiv : 1 / (1 - τ) ≤ 2 * τ + 1 := by
    apply (div_le_iff₀ hpos).mpr
    have hprod := mul_nonneg hτ0 (show 0 ≤ 1 - 2 * τ by linarith)
    nlinarith
  linarith

theorem exists_small_highPrimeGap (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 2 ∧ (N : ℝ) * (-Real.log (1 - τ)) < ε := by
  let τ := min (1 / 4 : ℝ) (ε / (4 * (N + 1)))
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτq : τ ≤ 1 / 4 := min_le_left _ _
  have hτ : τ < 1 / 2 := by linarith
  have hτe : τ ≤ ε / (4 * (N + 1)) := min_le_right _ _
  have hscaled := (le_div_iff₀ (by positivity : 0 < 4 * ((N : ℝ) + 1))).mp hτe
  have hgap := mul_le_mul_of_nonneg_left (highPrimeGap_loss_le hτ0.le hτ.le) (Nat.cast_nonneg N)
  refine ⟨τ, hτ0, hτ, ?_⟩
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_witness_interval_upper (p N : ℕ) (hp : p.Prime) (S : ℤ) :
    (∑ n ∈ Finset.range N,
      if (S + (n : ℤ) : ZMod (p ^ 2)) ∈ initialResidues (p ^ 2) p then (1 : ℝ) else 0) ≤
      (N : ℝ) / p + p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := modular_interval_upper (p ^ 2) (initialResidues (p ^ 2) p) S N
  rw [initialResidues_card _ _ (by nlinarith [hp.two_le]), Nat.cast_pow] at h
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have heq : ((N : ℝ) / (p : ℝ) ^ 2 + 1) * p = (N : ℝ) / p + p := by field_simp
  rwa [heq] at h

theorem initial_avoidance_card_lower {P : Type*} [Fintype P]
    (a : P → ℕ) [∀ p, NeZero (a p)] (hprime : ∀ p, (a p).Prime) (S : ℤ) (N : ℕ) :
    (N : ℝ) - N * (∑ p : P, 1 / (a p : ℝ)) - (∑ p : P, (a p : ℝ)) ≤
      (originalAvoidSet a S (S + N - 1)).card := by
  classical
  have hcount := avoid_filter_card_lower (Finset.Icc S (S + N - 1))
    (fun p n => (n : ZMod ((a p) ^ 2)) ∈ initialResidues ((a p) ^ 2) (a p))
  have hcount' : ((Finset.Icc S (S + N - 1)).card : ℝ) -
      (∑ n ∈ Finset.Icc S (S + N - 1), ∑ p : P,
        if (n : ZMod ((a p) ^ 2)) ∈ initialResidues ((a p) ^ 2) (a p) then (1 : ℝ) else 0) ≤
      (originalAvoidSet a S (S + N - 1)).card := by
    convert hcount using 1
    apply congrArg (fun s : Finset ℤ => (s.card : ℝ))
    ext n
    simp [originalAvoidSet]
  have hcard : (Finset.Icc S (S + N - 1)).card = N := by rw [Int.card_Icc]; omega
  rw [hcard] at hcount'
  have hsum : (∑ n ∈ Finset.Icc S (S + N - 1), ∑ p : P,
      if (n : ZMod ((a p) ^ 2)) ∈ initialResidues ((a p) ^ 2) (a p) then (1 : ℝ) else 0) ≤
      N * (∑ p : P, 1 / (a p : ℝ)) + (∑ p : P, (a p : ℝ)) := by
    rw [sum_int_interval, Finset.sum_comm]
    have h := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
      prime_witness_interval_upper (a p) N (hprime p) S)
    simpa only [Finset.sum_add_distrib, div_eq_mul_inv, one_mul, Finset.mul_sum, Int.cast_add] using h
  nlinarith

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem prime_family_card_le_count {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (z : ℝ) (hle : ∀ p, (a p : ℝ) ≤ z) :
    Fintype.card P ≤ Nat.primeCounting ⌊z⌋₊ := by
  have hsub : Finset.univ.image a ⊆ Nat.primesLE ⌊z⌋₊ := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hle p), hprime p⟩
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Nat.primesLE_card_eq_primeCounting] using hcard

universe u

theorem prime_endpoint_sum_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (a : P → ℕ),
        Function.Injective a → (∀ p, (a p).Prime) →
        (∀ p, (a p : ℝ) ≤ 2 * X ^ (1 / 2 : ℝ)) →
        (∑ p : P, (a p : ℝ)) ≤ ε * X := by
  let C := Real.log 4 + 1
  have hC : 0 < C := by dsimp [C]; have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith
  have hz : Tendsto (fun X : ℝ => 2 * X ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_atTop (by norm_num)
  have hpi := hz.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  have hlog := (Real.tendsto_log_atTop.comp hz).eventually_ge_atTop (max 1 (4 * C / ε))
  filter_upwards [hpi, hlog, eventually_gt_atTop (0 : ℝ)] with X hπ hl hx
  intro P instF instD a hinj hprime hle
  let z := 2 * X ^ (1 / 2 : ℝ)
  change max 1 (4 * C / ε) ≤ Real.log z at hl
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hlogpos : 0 < Real.log z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hl)
  have hratio : 4 * C / Real.log z ≤ ε := by
    apply (div_le_iff₀ hlogpos).mpr
    have h := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hl)
    nlinarith
  have hsum : (∑ p : P, (a p : ℝ)) ≤ (Nat.primeCounting ⌊z⌋₊ : ℝ) * z := by
    have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) => hle p)
    have hc : (Fintype.card P : ℝ) ≤ Nat.primeCounting ⌊z⌋₊ := by
      exact_mod_cast prime_family_card_le_count a hinj hprime z hle
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right hc hz0.le)
  have hsquare : z ^ 2 = 4 * X := by
    have hp : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    dsimp [z]
    rw [mul_pow, hp]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_right hπ hz0.le
  have heq : C * z / Real.log z * z = (4 * C / Real.log z) * X := by
    have h := hsquare
    field_simp
    nlinarith
  change (Nat.primeCounting ⌊z⌋₊ : ℝ) * z ≤ C * z / Real.log z * z at hscaled
  rw [heq] at hscaled
  exact hsum.trans (hscaled.trans (mul_le_mul_of_nonneg_right hratio hx.le))

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem log_five_halves_lt_one : Real.log (5 / 2 : ℝ) < 1 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 5 / 2)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem initial_prime_cutoff_bounds :
    ∀ᶠ X : ℝ in atTop, X ^ (6 / 25 : ℝ) < X ^ (1 / 4 : ℝ) ∧
      2 * X ^ (1 / 2 : ℝ) ≤ X ^ (3 / 5 : ℝ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop 2] with X hX hpow
  refine ⟨Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num), ?_⟩
  have h := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith : 0 ≤ X) (1 / 2 : ℝ))
  have heq : X ^ (1 / 2 : ℝ) * X ^ (1 / 10 : ℝ) = X ^ (3 / 5 : ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < X)]
    norm_num
  rw [heq] at h
  simpa only [mul_comm] using h

universe u

theorem initial_large_prime_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P : Type u) [Fintype P] [DecidableEq P] (a : P → ℕ) [∀ p, NeZero (a p)],
        (∀ p, (a p).Prime) → Function.Injective a →
        (∀ p, (X : ℝ) ^ (1 / 4 : ℝ) ≤ a p) →
        (∀ p, (a p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) →
        d * X ≤ (originalAvoidSet a ((X : ℤ) + 1) (2 * (X : ℤ))).card := by
  let d₀ := 1 - Real.log (5 / 2 : ℝ)
  have hd₀ : 0 < d₀ := by dsimp [d₀]; linarith [log_five_halves_lt_one]
  have hlimit := prime_power_band_limit (6 / 25 : ℝ) (3 / 5 : ℝ) (by norm_num) (by norm_num)
  have hlog : Real.log (3 / 5 : ℝ) - Real.log (6 / 25 : ℝ) = Real.log (5 / 2 : ℝ) := by
    rw [← Real.log_div (by norm_num : (3 / 5 : ℝ) ≠ 0) (by norm_num : (6 / 25 : ℝ) ≠ 0)]
    norm_num
  rw [hlog] at hlimit
  have hnear : ∀ᶠ X : ℝ in atTop, primeReciprocalSum (X ^ (3 / 5 : ℝ)) -
      primeReciprocalSum (X ^ (6 / 25 : ℝ)) < Real.log (5 / 2 : ℝ) + d₀ / 4 :=
    (tendsto_order.mp hlimit).2 _ (by linarith)
  refine ⟨d₀ / 2, by positivity, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hnear,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually initial_prime_cutoff_bounds,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (prime_endpoint_sum_small (by positivity : 0 < d₀ / 4)),
    eventually_ge_atTop (1 : ℕ)] with X hX hcuts hend hpos
  intro P instF instD a instN hprime hinj hlo hhi
  have horder' : (X : ℝ) ^ (6 / 25 : ℝ) ≤ (X : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) (by norm_num)
  have hmass := prime_family_reciprocal_band_le a hinj hprime _ _ horder'
    (fun p => hcuts.1.trans_le (hlo p)) (fun p => (hhi p).trans hcuts.2)
  have hsum := hend P a hinj hprime hhi
  have hlow := initial_avoidance_card_lower a hprime ((X : ℤ) + 1) X
  have heq : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  rw [heq] at hlow
  have hscaled := mul_le_mul_of_nonneg_left (hmass.trans hX.le) (Nat.cast_nonneg X)
  dsimp only [d₀] at *
  nlinarith

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

noncomputable def primeBandSet (x a b : ℝ) : Finset ℕ :=
  primesUpToReal (x ^ b) \ primesUpToReal (x ^ a)

theorem mem_primeBandSet (x a b : ℝ) (p : ℕ) :
    p ∈ primeBandSet x a b ↔ p.Prime ∧ x ^ a < p ∧ (p : ℝ) ≤ x ^ b := by
  simp only [primeBandSet, Finset.mem_sdiff, mem_primesUpToReal]
  aesop

theorem primeBandSet_mass {x a b : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) :
    primeMass (primeBandSet x a b) = primeReciprocalSum (x ^ b) - primeReciprocalSum (x ^ a) := by
  have hsub := primesUpToReal_subset (Real.rpow_le_rpow_of_exponent_le hx hab)
  have h := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) hsub
  change primeMass (primeBandSet x a b) + primeReciprocalSum (x ^ a) =
    primeReciprocalSum (x ^ b) at h
  linarith

noncomputable def initialHighPrimeSet (X : ℕ) : Finset ℕ :=
  primesUpToReal (2 * (X : ℝ) ^ (1 / 2 : ℝ)) \ primesUpToReal ((X : ℝ) ^ (1 / 4 : ℝ))

noncomputable def selectedHighPrimes (X : ℕ) (τ : ℝ) : ℕ → Finset ℕ
  | 0 => initialHighPrimeSet X
  | j + 1 => selectedHighPrimes X τ j ∪ primeBandSet X (highPrimeLevel (j + 1)) (highPrimeBlockUpper τ j)

theorem initialHighPrimeSet_bounds {X p : ℕ} (hp : p ∈ initialHighPrimeSet X) :
    p.Prime ∧ (X : ℝ) ^ (1 / 4 : ℝ) < p ∧ (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  simp only [initialHighPrimeSet, Finset.mem_sdiff, mem_primesUpToReal] at hp
  aesop

theorem selectedHighPrimes_bounds {X : ℕ} (hX : 1 ≤ X) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    ∀ p ∈ selectedHighPrimes X τ j,
      p.Prime ∧ (X : ℝ) ^ highPrimeLevel j < p ∧
        (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  induction j with
  | zero =>
      intro p hp
      simpa only [highPrimeLevel_zero] using initialHighPrimeSet_bounds hp
  | succ j ih =>
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨hprime, hlo, hhi⟩ := ih p hp
        refine ⟨hprime, ?_, hhi⟩
        exact (Real.rpow_le_rpow_of_exponent_le hx (by
          rw [highPrimeLevel_succ]; linarith [highPrimeLevel_pos j])).trans_lt hlo
      · obtain ⟨hprime, hlo, hhi⟩ := (mem_primeBandSet _ _ _ p).mp hp
        refine ⟨hprime, hlo, hhi.trans ?_⟩
        have hbound := highPrimeBlock_bounds hτ0 hτ j
        have hpowers := Real.rpow_le_rpow_of_exponent_le hx (show highPrimeBlockUpper τ j ≤ 1 / 2 by linarith)
        have hpos := Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2 : ℝ)
        linarith

theorem highPrimeBlock_mass_eventually {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      primeMass (primeBandSet X (highPrimeLevel (j + 1)) (highPrimeBlockUpper τ j)) ≤ Real.log 2 := by
  have hb := highPrimeBlock_bounds hτ0 hτ j
  have hlim := (prime_power_band_limit _ _ hb.1 (hb.1.trans hb.2.1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hnear := (tendsto_order.mp hlim).2 (Real.log 2) (highPrimeBlock_log_mass hτ0 hτ j)
  filter_upwards [hnear, eventually_ge_atTop (1 : ℕ)] with X hX hx
  rw [primeBandSet_mass (by exact_mod_cast hx) hb.2.1.le]
  exact hX.le

theorem initialHighPrimeSet_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℕ in atTop,
      d * X ≤ (primeAvoidSet (initialHighPrimeSet X) ((X : ℤ) + 1) (2 * X)).card := by
  obtain ⟨d, hd, hevent⟩ := initial_large_prime_avoidance.{0}
  refine ⟨d, hd, ?_⟩
  filter_upwards [hevent] with X hX
  let s := initialHighPrimeSet X
  letI (p : s) : NeZero (p : ℕ) := ⟨(initialHighPrimeSet_bounds p.property).1.ne_zero⟩
  have h := hX s (fun p : s => (p : ℕ))
    (fun p => (initialHighPrimeSet_bounds p.property).1) Subtype.val_injective
    (fun p => (initialHighPrimeSet_bounds p.property).2.1.le)
    (fun p => (initialHighPrimeSet_bounds p.property).2.2)
  simpa only [primeAvoidSet_subtype] using h

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem power_saving_eventually {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (K : ℝ) :
    ∀ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (1 - δ) ≤ ε * X := by
  have hlim := ((tendsto_rpow_neg_atTop hδ).const_mul K).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hnear : ∀ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (-δ) < ε :=
    (tendsto_order.mp (by simpa only [mul_zero, Function.comp_def] using hlim)).2 ε hε
  filter_upwards [hnear, eventually_ge_atTop (1 : ℕ)] with X hX hx
  have hx0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have h := mul_le_mul_of_nonneg_right hX.le hx0.le
  have heq : (X : ℝ) ^ (-δ) * X = (X : ℝ) ^ (1 - δ) := by
    calc
      (X : ℝ) ^ (-δ) * X = (X : ℝ) ^ (-δ) * (X : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (X : ℝ) ^ (-δ + 1) := (Real.rpow_add hx0 _ _).symm
      _ = (X : ℝ) ^ (1 - δ) := by congr 1; ring
  simpa only [mul_assoc, heq] using h

theorem highPrimeStep_eventually {τ ε : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2)
    (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      dyadicRetention * (primeAvoidSet (selectedHighPrimes X τ j) ((X : ℤ) + 1) (2 * X)).card - ε * X ≤
        (primeAvoidSet (selectedHighPrimes X τ (j + 1)) ((X : ℤ) + 1) (2 * X)).card := by
  have hb := highPrimeBlock_bounds hτ0 hτ j
  let η := (highPrimeBlockUpper τ j + highPrimeLevel j) / 2
  obtain ⟨K, δ, hK, hδ, havg⟩ := prime_set_high_averaging hb.1 hb.2.1.le
    (hb.2.2.1.le.trans hb.2.2.2)
    (show highPrimeBlockUpper τ j < η by dsimp [η]; linarith [hb.2.2.1])
    (show η < highPrimeLevel j by dsimp [η]; linarith [hb.2.2.1])
    (show highPrimeLevel j ≤ 1 / 2 by linarith [hb.2.2.2])
  filter_upwards [havg, power_saving_eventually hδ hε K,
    highPrimeBlock_mass_eventually hτ0 hτ j, eventually_ge_atTop (1 : ℕ)] with X hX herr hmass hx
  let s := selectedHighPrimes X τ j
  let t := primeBandSet X (highPrimeLevel (j + 1)) (highPrimeBlockUpper τ j)
  have hs := selectedHighPrimes_bounds hx hτ0 hτ j
  have ht (p : ℕ) (hp : p ∈ t) := (mem_primeBandSet _ _ _ p).mp hp
  have hbound := hX s t (fun p hp => (hs p hp).1) (fun p hp => (ht p hp).1)
    (fun p hp => (hs p hp).2.1.le) (fun p hp => (hs p hp).2.2)
    (fun p hp => (ht p hp).2.1.le) (fun p hp => (ht p hp).2.2)
  have hcount : (∑ n ∈ primeAvoidSet s ((X : ℤ) + 1) (2 * X), primeWitnessCount t n) ≤
      Real.log 2 * (primeAvoidSet s ((X : ℤ) + 1) (2 * X)).card + ε * X := by
    have hupper := (le_abs_self _).trans hbound
    have hscaled := mul_le_mul_of_nonneg_right hmass
      (Nat.cast_nonneg (primeAvoidSet s ((X : ℤ) + 1) (2 * X)).card)
    linarith
  exact prime_avoidance_step s t _ _ (Real.log 2) (ε * X) hcount

theorem selectedHighPrimes_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ (τ : ℝ), 0 < τ → τ < 1 / 2 → ∀ (j : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ X : ℕ in atTop,
        (d * dyadicRetention ^ j - ε) * X ≤
          (primeAvoidSet (selectedHighPrimes X τ j) ((X : ℤ) + 1) (2 * X)).card := by
  obtain ⟨d, hd, hinit⟩ := initialHighPrimeSet_avoidance
  refine ⟨d, hd, ?_⟩
  intro τ hτ0 hτ j
  induction j with
  | zero =>
      intro ε hε
      filter_upwards [hinit] with X hX
      simp only [pow_zero, mul_one, selectedHighPrimes]
      have hεX : 0 ≤ ε * (X : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg X)
      linarith
  | succ j ih =>
      intro ε hε
      have hε2 : 0 < ε / 2 := by positivity
      filter_upwards [ih (ε / 2) hε2, highPrimeStep_eventually hτ0 hτ hε2 j] with X hprev hstep
      have hd0 : 0 ≤ dyadicRetention := by linarith [dyadicRetention_bounds.1]
      have hscaled := mul_le_mul_of_nonneg_left hprev hd0
      have he := mul_le_mul_of_nonneg_right dyadicRetention_bounds.2.le
        (show 0 ≤ ε / 2 * (X : ℝ) by positivity)
      rw [pow_succ]
      nlinarith

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem primeMass_union_le (s t : Finset ℕ) : primeMass (s ∪ t) ≤ primeMass s + primeMass t := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := fun p : ℕ => 1 / (p : ℝ))
  have hpos : 0 ≤ primeMass (s ∩ t) := Finset.sum_nonneg (fun p hp => by positivity)
  change primeMass (s ∪ t) + primeMass (s ∩ t) = primeMass s + primeMass t at h
  linarith

noncomputable def omittedHighPrimes (X : ℕ) (τ : ℝ) : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => omittedHighPrimes X τ j ∪ primeBandSet X (highPrimeBlockUpper τ j) (highPrimeLevel j)

theorem highPrime_covered (X : ℕ) (τ : ℝ) (j p : ℕ) (hp : p.Prime)
    (hlo : (X : ℝ) ^ highPrimeLevel j < p)
    (hhi : (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ)) :
    p ∈ selectedHighPrimes X τ j ∨ p ∈ omittedHighPrimes X τ j := by
  induction j with
  | zero =>
      left
      simp only [selectedHighPrimes, initialHighPrimeSet, Finset.mem_sdiff, mem_primesUpToReal]
      rw [highPrimeLevel_zero] at hlo
      exact ⟨⟨hp, hhi⟩, fun h => (not_le_of_gt hlo) h.2⟩
  | succ j ih =>
      by_cases hold : (X : ℝ) ^ highPrimeLevel j < p
      · rcases ih hold with hs | hg
        · exact Or.inl (Finset.mem_union_left _ hs)
        · exact Or.inr (Finset.mem_union_left _ hg)
      · have hle : (p : ℝ) ≤ (X : ℝ) ^ highPrimeLevel j := le_of_not_gt hold
        by_cases hblock : (p : ℝ) ≤ (X : ℝ) ^ highPrimeBlockUpper τ j
        · left
          exact Finset.mem_union_right _ ((mem_primeBandSet _ _ _ p).mpr ⟨hp, hlo, hblock⟩)
        · right
          exact Finset.mem_union_right _ ((mem_primeBandSet _ _ _ p).mpr ⟨hp, lt_of_not_ge hblock, hle⟩)

theorem omittedHighPrimes_bounds {X : ℕ} (hX : 1 ≤ X) (τ : ℝ) (j : ℕ) :
    ∀ p ∈ omittedHighPrimes X τ j, p.Prime ∧ (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  induction j with
  | zero => simp [omittedHighPrimes]
  | succ j ih =>
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ih p hp
      · obtain ⟨hprime, hlo, hhi⟩ := (mem_primeBandSet _ _ _ p).mp hp
        refine ⟨hprime, hhi.trans ?_⟩
        have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
        have hpow := Real.rpow_le_rpow_of_exponent_le hx
          (show highPrimeLevel j ≤ 1 / 2 by linarith [highPrimeLevel_le_quarter j])
        have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2 : ℝ)
        linarith

theorem highPrimeGap_mass_eventually {τ ε : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2)
    (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      primeMass (primeBandSet X (highPrimeBlockUpper τ j) (highPrimeLevel j)) ≤
        -Real.log (1 - τ) + ε := by
  have hb := highPrimeBlock_bounds hτ0 hτ j
  have hlim := (prime_power_band_limit _ _ (hb.1.trans hb.2.1) (highPrimeLevel_pos j)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [highPrimeGap_log_mass hτ0.le (by linarith)] at hlim
  have hnear := (tendsto_order.mp hlim).2 (-Real.log (1 - τ) + ε) (by linarith)
  filter_upwards [hnear, eventually_ge_atTop (1 : ℕ)] with X hX hx
  rw [primeBandSet_mass (by exact_mod_cast hx) hb.2.2.1.le]
  exact hX.le

theorem omittedHighPrimes_mass_eventually {τ ε : ℝ} (hτ0 : 0 < τ) (hτ : τ < 1 / 2)
    (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop, primeMass (omittedHighPrimes X τ j) ≤
      j * (-Real.log (1 - τ)) + ε := by
  induction j generalizing ε with
  | zero =>
      filter_upwards [] with X
      simpa [omittedHighPrimes, primeMass] using hε.le
  | succ j ih =>
      have hε2 : 0 < ε / 2 := by positivity
      filter_upwards [ih hε2, highPrimeGap_mass_eventually hτ0 hτ hε2 j] with X hprev hgap
      have hsum := primeMass_union_le (omittedHighPrimes X τ j)
        (primeBandSet X (highPrimeBlockUpper τ j) (highPrimeLevel j))
      change primeMass (omittedHighPrimes X τ (j + 1)) ≤ _ at hsum
      push_cast
      linarith

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem primeWitnessCount_nonneg (s : Finset ℕ) (n : ℤ) : 0 ≤ primeWitnessCount s n := by
  classical
  unfold primeWitnessCount
  exact Finset.sum_nonneg (fun p hp => by split_ifs <;> norm_num)

theorem prime_witness_sum_upper (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (S : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc S (S + N - 1), primeWitnessCount s n) ≤
      N * primeMass s + ∑ p ∈ s, (p : ℝ) := by
  classical
  unfold primeWitnessCount
  rw [sum_int_interval, Finset.sum_comm]
  have h := Finset.sum_le_sum (fun p (hp : p ∈ s) => prime_witness_interval_upper p N (hs p hp) S)
  simpa only [primeMass, Finset.sum_add_distrib, div_eq_mul_inv, one_mul,
    Finset.mul_sum, Int.cast_add] using h

theorem prime_avoidance_gap_lower (s t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (S : ℤ) (N : ℕ) :
    (primeAvoidSet s S (S + N - 1)).card -
      (N * primeMass t + ∑ p ∈ t, (p : ℝ)) ≤
        (primeAvoidSet (s ∪ t) S (S + N - 1)).card := by
  have hsub : primeAvoidSet s S (S + N - 1) ⊆ Finset.Icc S (S + N - 1) := by
    classical
    exact Finset.filter_subset _ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => primeWitnessCount_nonneg t n)
  have hbound := hsum.trans (prime_witness_sum_upper t ht S N)
  have h := prime_avoidance_step s t S (S + N - 1) 0
    (N * primeMass t + ∑ p ∈ t, (p : ℝ)) (by simpa only [zero_mul, zero_add] using hbound)
  simpa only [sub_zero, one_mul] using h

noncomputable def allHighPrimes (X j : ℕ) : Finset ℕ :=
  primesUpToReal (2 * (X : ℝ) ^ (1 / 2 : ℝ)) \ primesUpToReal ((X : ℝ) ^ highPrimeLevel j)

theorem allHighPrimes_covered (X j : ℕ) (τ : ℝ) :
    allHighPrimes X j ⊆ selectedHighPrimes X τ j ∪ omittedHighPrimes X τ j := by
  intro p hp
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hprime, hupper⟩ := (mem_primesUpToReal _ p).mp hhi
  have hlower : (X : ℝ) ^ highPrimeLevel j < p := by
    by_contra h
    exact hlo ((mem_primesUpToReal _ p).mpr ⟨hprime, le_of_not_gt h⟩)
  exact Finset.mem_union.mpr (highPrime_covered X τ j p hprime hlower hupper)

theorem omittedHighPrimes_endpoint_sum {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (j : ℕ) :
    ∀ᶠ X : ℕ in atTop, (∑ p ∈ omittedHighPrimes X τ j, (p : ℝ)) ≤ ε * X := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (prime_endpoint_sum_small.{0} hε), eventually_ge_atTop (1 : ℕ)] with X hX hx
  let s := omittedHighPrimes X τ j
  have hb := omittedHighPrimes_bounds hx τ j
  have h := hX s (fun p : s => (p : ℕ)) Subtype.val_injective
    (fun p => (hb p p.property).1) (fun p => (hb p p.property).2)
  simpa only [Finset.sum_coe_sort] using h

theorem allHighPrimes_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ j : ℕ, ∀ᶠ X : ℕ in atTop,
      d * dyadicRetention ^ j * X ≤
        (primeAvoidSet (allHighPrimes X j) ((X : ℤ) + 1) (2 * X)).card := by
  obtain ⟨d, hd, hselected⟩ := selectedHighPrimes_avoidance
  refine ⟨d / 2, by positivity, ?_⟩
  intro j
  let g := d * dyadicRetention ^ j
  have hg : 0 < g := mul_pos hd (pow_pos (by linarith [dyadicRetention_bounds.1]) j)
  have he : 0 < g / 8 := by positivity
  obtain ⟨τ, hτ0, hτ, hgap⟩ := exists_small_highPrimeGap j he
  filter_upwards [hselected τ hτ0 hτ j (g / 8) he,
    omittedHighPrimes_mass_eventually hτ0 hτ he j,
    omittedHighPrimes_endpoint_sum he τ j, eventually_ge_atTop (1 : ℕ)] with X hsel hmass hend hx
  have hb := omittedHighPrimes_bounds hx τ j
  have hlower := prime_avoidance_gap_lower (selectedHighPrimes X τ j) (omittedHighPrimes X τ j)
    (fun p hp => (hb p hp).1) ((X : ℤ) + 1) X
  have heq : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  rw [heq] at hlower
  have hcard : ((primeAvoidSet (selectedHighPrimes X τ j ∪ omittedHighPrimes X τ j)
      ((X : ℤ) + 1) (2 * X)).card : ℝ) ≤
      (primeAvoidSet (allHighPrimes X j) ((X : ℤ) + 1) (2 * X)).card := by
    exact_mod_cast Finset.card_le_card (primeAvoidSet_mono (allHighPrimes_covered X j τ) _ _)
  have hmassX := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg X)
  have hgapX := mul_le_mul_of_nonneg_right hgap.le (Nat.cast_nonneg X)
  dsimp only [g] at *
  nlinarith

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem allHighPrimes_bounds {X j p : ℕ} (hp : p ∈ allHighPrimes X j) :
    p.Prime ∧ (X : ℝ) ^ highPrimeLevel j < p ∧
      (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
  simp only [allHighPrimes, Finset.mem_sdiff, mem_primesUpToReal] at hp
  aesop

noncomputable def stableHighSet (X j : ℕ) (η : ℝ) : Finset ℤ :=
  lowerAvoidSet (fun p : allHighPrimes X j => (p : ℕ))
    ((X : ℤ) + 1) (2 * X) (powerFloor η X)

theorem stable_high_avoidance :
    ∃ d : ℝ, 0 < d ∧ ∀ (j : ℕ) (η : ℝ), η < highPrimeLevel j →
      ∀ᶠ X : ℕ in atTop, d * dyadicRetention ^ j * X ≤ (stableHighSet X j η).card := by
  obtain ⟨d, hd, hfull⟩ := allHighPrimes_avoidance
  refine ⟨d / 2, by positivity, ?_⟩
  intro j η hη
  let c := highPrimeLevel j
  have hc0 : 0 < c := highPrimeLevel_pos j
  have hc : c ≤ 1 / 2 := by dsimp [c]; linarith [highPrimeLevel_le_quarter j]
  let g := d * dyadicRetention ^ j
  have hg : 0 < g := mul_pos hd (pow_pos (by linarith [dyadicRetention_bounds.1]) j)
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((tendsto_rpow_atTop hc0).eventually_ge_atTop 4)
  have herror := power_saving_eventually (show 0 < c - η by dsimp [c]; linarith)
    (show 0 < g / 2 by positivity) 13
  filter_upwards [hfull j, hlarge, herror, eventually_ge_atTop (1 : ℕ)] with X hcount hlargeX herr hx
  let s := allHighPrimes X j
  let a : s → ℕ := fun p => (p : ℕ)
  let m := ⌊(X : ℝ) ^ c / 2⌋₊
  let H := powerFloor η X
  have hs (p : s) := allHighPrimes_bounds p.property
  letI (p : s) : NeZero (a p) := ⟨(hs p).1.ne_zero⟩
  have hxreal : (1 : ℝ) ≤ X := by exact_mod_cast hx
  have hmreal : 0 < (m : ℝ) := by
    have hhalf := floor_ge_half (show 2 ≤ (X : ℝ) ^ c / 2 by linarith)
    dsimp [m]
    linarith
  have hm : 0 < m := by exact_mod_cast hmreal
  have hfloor : (m : ℝ) ≤ (X : ℝ) ^ c / 2 := Nat.floor_le (by positivity)
  have hlo (p : s) : m < a p := by
    have hp := (hs p).2.1
    dsimp only [c] at hfloor hlargeX
    have hreal : (m : ℝ) < (a p : ℝ) := by dsimp [a]; linarith
    exact_mod_cast hreal
  have hb := avoidance_boundary_card_bound a (fun p => (hs p).1) Subtype.val_injective
    m hm hlo (2 * (X : ℝ) ^ (1 / 2 : ℝ)) (by positivity)
    (fun p => (hs p).2.2) ((X : ℤ) + 1) X H
  have heq : (X : ℤ) + 1 + X - 1 = 2 * X := by ring
  rw [heq] at hb
  have hcards := (avoidance_card_bounds a ((X : ℤ) + 1) (2 * X) H).1
  have hcardsR : ((originalAvoidSet a ((X : ℤ) + 1) (2 * X)).card : ℝ) ≤
      (lowerAvoidSet a ((X : ℤ) + 1) (2 * X) H).card + H +
        (avoidanceBoundarySet a ((X : ℤ) + 1) (2 * X) H).card := by exact_mod_cast hcards
  have hpower := boundary_error_power_bound hxreal hc (by simpa only [c] using hlargeX)
    (Nat.cast_nonneg H) 1 (show (H : ℝ) ≤ (1 : ℕ) * (X : ℝ) ^ η by
      simpa only [H, powerFloor, Nat.cast_one, one_mul] using Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) η))
  have hpowe : 1 + η - c = 1 - (c - η) := by ring
  simp only [Nat.cast_one, mul_one, hpowe] at hpower
  have hcount' : g * X ≤ (originalAvoidSet a ((X : ℤ) + 1) (2 * X)).card := by
    simpa only [a, s, g, primeAvoidSet_subtype] using hcount
  change d / 2 * dyadicRetention ^ j * X ≤ (lowerAvoidSet a ((X : ℤ) + 1) (2 * X) H).card
  dsimp only [g] at herr hcount'
  dsimp only [m] at hb
  nlinarith

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

noncomputable def stableNaturalCenters (X j : ℕ) (η : ℝ) : Finset ℕ :=
  (stableHighSet X j η).image Int.toNat

theorem stableHighSet_interval {X j : ℕ} {η : ℝ} {n : ℤ} (hn : n ∈ stableHighSet X j η) :
    (X : ℤ) + 1 ≤ n ∧ n ≤ 2 * X - powerFloor η X := by
  classical
  exact Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1

theorem stableNaturalCenters_card (X j : ℕ) (η : ℝ) :
    (stableNaturalCenters X j η).card = (stableHighSet X j η).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  have ha0 : 0 ≤ a := by have := (stableHighSet_interval ha).1; omega
  have hb0 : 0 ≤ b := by have := (stableHighSet_interval hb).1; omega
  have h := congrArg (fun n : ℕ => (n : ℤ)) hab
  simpa only [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] using h

theorem stableNaturalCenters_shifts {X j : ℕ} {η : ℝ} {n k : ℕ}
    (hn : n ∈ stableNaturalCenters X j η) (hk : k < powerFloor η X) :
    X < n + k ∧ n + k ≤ 2 * X := by
  classical
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hmlo, hmhi⟩ := stableHighSet_interval hm
  have hm0 : 0 ≤ m := by omega
  have hcast := Int.toNat_of_nonneg hm0
  omega

theorem stableNaturalCenters_subset (X j : ℕ) (η : ℝ) :
    stableNaturalCenters X j η ⊆ Finset.Ioc X (2 * X) := by
  classical
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hmlo, hmhi⟩ := stableHighSet_interval hm
  have hm0 : 0 ≤ m := by omega
  have hcast := Int.toNat_of_nonneg hm0
  exact Finset.mem_Ioc.mpr (by omega)

theorem stableNaturalCenters_large_avoidance {X j : ℕ} {η : ℝ} {n k : ℕ}
    (hn : n ∈ stableNaturalCenters X j η) (hk : k < powerFloor η X) :
    LargeAvoidance ⌊(X : ℝ) ^ highPrimeLevel j⌋₊ (n + k) := by
  classical
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  have hm0 : 0 ≤ m := by have := (stableHighSet_interval hm).1; omega
  have hcast := Int.toNat_of_nonneg hm0
  have hshift := lowerAvoidSet_shift (fun p : allHighPrimes X j => (p : ℕ))
    ((X : ℤ) + 1) (2 * X) (powerFloor η X) (k : ℤ) (by omega) (by omega) m hm
  have hres := (Finset.mem_filter.mp hshift).2
  intro p hp hcut hpn
  have hlow : (X : ℝ) ^ highPrimeLevel j < (p : ℝ) :=
    (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg X) _)).mp hcut
  have hupper : (p : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
    have hinterval := Finset.mem_Icc.mp (Finset.mem_filter.mp hshift).1
    have hnat : m.toNat + k ≤ 2 * X := by omega
    have hp2 : (p : ℝ) ^ 2 ≤ 2 * X := by exact_mod_cast hpn.trans hnat
    have hsquare : ((X : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]
      norm_num
    have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 2 : ℝ)
    nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hmem : p ∈ allHighPrimes X j := by
    apply Finset.mem_sdiff.mpr
    exact ⟨(mem_primesUpToReal _ p).mpr ⟨hp, hupper⟩,
      fun h => (not_le_of_gt hlow) ((mem_primesUpToReal _ p).mp h).2⟩
  have havoid := hres ⟨p, hmem⟩
  have heqm : ((m.toNat : ℕ) : ZMod (p ^ 2)) = (m : ZMod (p ^ 2)) := by
    rw [← Int.cast_natCast, hcast]
  have havoidNat : ((m.toNat + k : ℕ) : ZMod (p ^ 2)) ∉ smallResidues p := by
    simpa only [Nat.cast_add, heqm, Int.cast_add, Int.cast_natCast, initial_prime_square] using havoid
  exact Nat.le_of_not_gt (fun hsmall => havoidNat ((mem_smallResidues p _ hp.one_lt.le).mpr hsmall))

theorem stable_natural_centers :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ (j : ℕ) (η : ℝ), η < highPrimeLevel j →
      ∀ᶠ X : ℕ in atTop, d * dyadicRetention ^ j * X ≤ (stableNaturalCenters X j η).card := by
  obtain ⟨d, hd, hstable⟩ := stable_high_avoidance
  refine ⟨min d 1, lt_min hd zero_lt_one, min_le_right _ _, ?_⟩
  intro j η hη
  filter_upwards [hstable j η hη] with X hX
  rw [stableNaturalCenters_card]
  have h := mul_le_mul_of_nonneg_right (min_le_left d 1)
    (show 0 ≤ dyadicRetention ^ j * (X : ℝ) by
      apply mul_nonneg (pow_nonneg (by linarith [dyadicRetention_bounds.1]) _) (Nat.cast_nonneg X))
  nlinarith

end Erdos676
end

section
open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem exists_eventual_survival_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, c / Real.log x ≤ survivalProduct x := by
  let c := Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-1)
  have hlimit : Tendsto Mertens.E₃ atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hevent : ∀ᶠ x : ℝ in atTop, (-1 : ℝ) < Mertens.E₃ x :=
    (tendsto_order.mp hlimit).1 _ (by norm_num)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [hevent, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [survivalProduct_formula hx1]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx1).le
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.le) (Real.exp_pos _).le

theorem eventually_power_error_absorbed {α β C η : ℝ}
    (hα : 0 < α) (hβ : β < 1) (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, C * x ^ β ≤ η * x * survivalProduct (x ^ α) := by
  obtain ⟨c, hc, hsurvival⟩ := exists_eventual_survival_lower
  have hlog := eventually_log_le_power (by linarith : 0 < 1 - β)
    (div_pos (mul_pos hη hc) (mul_pos hC hα))
  have hsurvival' := (tendsto_rpow_atTop hα).eventually hsurvival
  filter_upwards [hlog, hsurvival', eventually_gt_atTop (1 : ℝ)] with x hxlog hxV hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hden : 0 < α * Real.log x := mul_pos hα (Real.log_pos hx1)
  rw [Real.log_rpow hx0 α] at hxV
  have hpower : x ^ β * x ^ (1 - β) = x := by
    rw [← Real.rpow_add hx0, show β + (1 - β) = 1 by ring, Real.rpow_one]
  have hcancel : (C * α) * (η * c / (C * α)) = η * c := by
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hxlog
    (by positivity : 0 ≤ C * α * x ^ β)
  have hrhs : (C * α * x ^ β) * (η * c / (C * α) * x ^ (1 - β)) = η * c * x := by
    calc
      _ = ((C * α) * (η * c / (C * α))) * (x ^ β * x ^ (1 - β)) := by ring
      _ = _ := by rw [hcancel, hpower]
  rw [hrhs] at hscaled
  have hfirst : C * x ^ β ≤ η * c * x / (α * Real.log x) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hscaled]
  calc
    _ ≤ η * c * x / (α * Real.log x) := hfirst
    _ = (η * x) * (c / (α * Real.log x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hxV (mul_nonneg hη.le hx0.le)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem smallAverage_sum_eq_counts (z H S N : ℕ) :
    (∑ n ∈ Finset.range N, smallAverage z H (S + n)) =
      (∑ j ∈ Finset.range H, smallPrimeCount z (S + j) N) / (H : ℝ) := by
  classical
  simp only [smallAverage, smallPrimeCount, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.add_right_comm]

theorem smallAverage_sum_lower (z H S N : ℕ) (hH : 0 < H) (B : ℝ)
    (hcount : ∀ T : ℕ, B ≤ smallPrimeCount z T N) :
    B ≤ ∑ n ∈ Finset.range N, smallAverage z H (S + n) := by
  rw [smallAverage_sum_eq_counts]
  apply (le_div_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)).mpr
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range H) => hcount (S + j))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using h

theorem sum_dyadic_interval_eq_range (X : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc X (2 * X), f n) = ∑ n ∈ Finset.range X, f (X + 1 + n) := by
  have hset : Finset.Ioc X (2 * X) = Finset.Ico (X + 1) (2 * X + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hlength : 2 * X + 1 - (X + 1) = X := by omega
  rw [hlength]

theorem smallAverage_dyadic_lower (z H X : ℕ) (hH : 0 < H) (B : ℝ)
    (hcount : ∀ T : ℕ, B ≤ smallPrimeCount z T X) :
    B ≤ ∑ n ∈ Finset.Ioc X (2 * X), smallAverage z H n := by
  rw [sum_dyadic_interval_eq_range]
  exact smallAverage_sum_lower z H (X + 1) X hH B hcount

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem smallPrimeCount_first_moment {α C η : ℝ} (L : ℕ)
    (hα : 0 < α) (hL : 1 ≤ L) (hη : 0 < η)
    (hdegree : α * (8 * L + 8 : ℕ) ≤ 1 / 2)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ S : ℕ,
      (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) - η) * N *
          survivalProduct ((N : ℝ) ^ α) ≤ smallPrimeCount ⌊(N : ℝ) ^ α⌋₊ S N := by
  have hcover := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (growing_dyadic_covers hα (by norm_num : (0 : ℝ) < 1 / 4))
  have habsorb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_power_error_absorbed hα (by norm_num : (3 / 4 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 3) hη)
  filter_upwards [hcover, habsorb, eventually_ge_atTop (1 : ℕ)] with N hcov habs hN
  intro S
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 1 ≤ (N : ℝ) ^ α := Real.one_le_rpow hNreal hα.le
  have hfinite := smallPrimeCount_finite_lower ((N : ℝ) ^ α) hz
    (powerFloor (1 / 4) N) L hL hcov C hC hsmall S N
  have herror := growing_first_error_bound (α := α) hNreal (by norm_num : (0 : ℝ) ≤ 1 / 4) (8 * L + 8)
  have hexponent : (1 / 4 : ℝ) + α * (8 * L + 8 : ℕ) ≤ 3 / 4 := by linarith
  have hpower := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
  have herror' : (2 * (powerFloor (1 / 4) N : ℝ) + 1) * ((N : ℝ) ^ α) ^ (8 * L + 8) ≤
      3 * (N : ℝ) ^ (3 / 4 : ℝ) :=
    herror.trans (mul_le_mul_of_nonneg_left hpower (by norm_num))
  have hnegligible := herror'.trans habs
  calc
    _ = (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N * survivalProduct ((N : ℝ) ^ α) -
        η * N * survivalProduct ((N : ℝ) ^ α) := by ring
    _ ≤ (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L)) * N * survivalProduct ((N : ℝ) ^ α) -
        (2 * (powerFloor (1 / 4) N : ℝ) + 1) * ((N : ℝ) ^ α) ^ (8 * L + 8) :=
      sub_le_sub_left hnegligible _
    _ ≤ _ := hfinite

theorem smallAverage_first_moment {α C η : ℝ} (L : ℕ)
    (hα : 0 < α) (hL : 1 ≤ L) (hη : 0 < η)
    (hdegree : α * (8 * L + 8 : ℕ) ≤ 1 / 2)
    (hC : ∀ x : ℝ, primeReciprocalSum x - primeReciprocalSum (x ^ (1 / 2 : ℝ)) ≤ C)
    (hsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ, 0 < H →
      (1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) - η) * N *
        survivalProduct ((N : ℝ) ^ α) ≤
          ∑ n ∈ Finset.Ioc N (2 * N), smallAverage ⌊(N : ℝ) ^ α⌋₊ H n := by
  filter_upwards [smallPrimeCount_first_moment L hα hL hη hdegree hC hsmall] with N hN
  intro H hH
  exact smallAverage_dyadic_lower _ H N hH _ hN

end Erdos676
end

section
namespace Erdos676

theorem first_moment_loss_dyadic (C : ℝ) (L : ℕ) :
    2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) =
      (2 * Real.exp (4 * C)) * (discreteCutoff L) ^ 2 := by
  rw [discreteCutoff_sq]
  simp only [pow_mul, div_pow, one_pow]
  norm_num
  ring

theorem final_parameter_choice {d : ℝ} (hd : 0 < d) (C : ℝ) :
    ∃ L : ℕ, 3 ≤ L ∧ discreteCutoff L ≤ 1 / 200 ∧
      discreteCutoff L * (8 * L + 8 : ℕ) ≤ 1 / 2 ∧
      16 * (2 * Real.exp (4 * C) + 40000) * (discreteCutoff L) ^ 2 < d * dyadicRetention ^ L := by
  exact exists_dyadic_retention_margin hd (by positivity)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def pairMean (H : ℕ) (f : ℤ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H, f ((i : ℤ) - j)) / (H : ℝ) ^ 2

theorem pairMean_mono (H : ℕ) {f g : ℤ → ℝ} (hfg : ∀ k, f k ≤ g k) :
    pairMean H f ≤ pairMean H g := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hfg _))

theorem pairMean_nonneg (H : ℕ) {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    0 ≤ pairMean H f := by
  apply div_nonneg _ (sq_nonneg _)
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => hf _))

theorem pairMean_const (H : ℕ) (hH : 0 < H) (c : ℝ) :
    pairMean H (fun _ => c) = c := by
  have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hH)
  simp only [pairMean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem pairMean_add (H : ℕ) (f g : ℤ → ℝ) :
    pairMean H (fun k => f k + g k) = pairMean H f + pairMean H g := by
  simp only [pairMean, Finset.sum_add_distrib, add_div]

theorem pairMean_mul_const (H : ℕ) (c : ℝ) (f : ℤ → ℝ) :
    pairMean H (fun k => c * f k) = c * pairMean H f := by
  simp only [pairMean, ← Finset.mul_sum]
  ring

theorem pairMean_sum {P : Type*} (H : ℕ) (s : Finset P) (f : P → ℤ → ℝ) :
    pairMean H (fun k => ∑ p ∈ s, f p k) = ∑ p ∈ s, pairMean H (f p) := by
  unfold pairMean
  simp_rw [Finset.sum_comm (s := Finset.range H) (t := s)]
  rw [Finset.sum_div]

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem localSingularFactor_sum (p : ℕ) [NeZero p] (hp : 1 ≤ p) :
    (∑ k : ZMod (p ^ 2), localSingularFactor p k) = (p : ℝ) ^ 2 :=
  normalized_overlap_sum p hp

theorem singular_mixed_average_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (s : Finset P) (H : ℕ) (hH : 0 < H) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      ∏ p : P, if p ∈ s then
        localSingularExcess (a p) ((i : ZMod ((a p) ^ 2)) - j)
      else localSingularFactor (a p) ((i : ZMod ((a p) ^ 2)) - j)) / (H : ℝ) ^ 2 ≤
      (1 + (∏ p : P, (a p) ^ 2 : ℕ) / (H : ℝ)) *
        (∏ p : P, if p ∈ s then 1 / ((a p : ℝ) - 1) ^ 2 else 1) := by
  classical
  letI (p : P) : NeZero (a p) := ⟨(hprime p).ne_zero⟩
  letI : NeZero (∏ p : P, (a p) ^ 2) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero 2 (hprime p).ne_zero)⟩
  have hc : Pairwise (fun p q => ((a p) ^ 2).Coprime ((a q) ^ 2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hprime p) (hprime q)).mpr
      (fun heq => hpq (hinj heq))).pow 2 2
  apply crt_pair_average_upper (fun p => (a p) ^ 2) hc
    (fun p k => if p ∈ s then localSingularExcess (a p) k else localSingularFactor (a p) k)
    (fun p => if p ∈ s then 1 / ((a p : ℝ) - 1) ^ 2 else 1) _ _ H hH
  · intro p k
    split_ifs
    · exact le_max_right _ _
    · exact localSingularFactor_nonneg _ (hprime p).two_le _
  · intro p
    by_cases hp : p ∈ s
    · simp only [hp, if_true, Nat.cast_pow]
      simpa only [div_eq_mul_inv, one_mul] using
        localSingularExcess_sum_le (a p) (hprime p).two_le
    · simp only [hp, if_false, mul_one, Nat.cast_pow]
      exact (localSingularFactor_sum (a p) (hprime p).one_lt.le).le

theorem singular_product_average_upper {P : Type*} [Fintype P] [DecidableEq P]
    (a : P → ℕ) (hinj : Function.Injective a) (hprime : ∀ p, (a p).Prime)
    (H : ℕ) (hH : 0 < H) :
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range H,
      ∏ p : P, localSingularFactor (a p) ((i : ZMod ((a p) ^ 2)) - j)) /
        (H : ℝ) ^ 2 ≤ 1 + (∏ p : P, (a p) ^ 2 : ℕ) / (H : ℝ) := by
  simpa only [Finset.notMem_empty, if_false, Finset.prod_const_one, mul_one] using
    singular_mixed_average_upper a hinj hprime ∅ H hH

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem product_increment_upper {P : Type*} [LinearOrder P]
    (s : Finset P) (v c : P → ℝ)
    (hv : ∀ p ∈ s, 0 ≤ v p) (hc : ∀ p ∈ s, 1 + v p ≤ c p) :
    (∏ p ∈ s, (1 + v p)) ≤ 1 + (∏ p ∈ s, c p) * ∑ p ∈ s, v p := by
  rw [Finset.prod_one_add_ordered, Finset.mul_sum]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro p hp
  have hprefix : (∏ q ∈ s with q < p, (1 + v q)) ≤ ∏ q ∈ s, c q := by
    calc
      _ ≤ ∏ q ∈ s with q < p, c q :=
        Finset.prod_le_prod
          (fun q hq => by linarith [hv q (Finset.mem_filter.mp hq).1])
          (fun q hq => hc q (Finset.mem_filter.mp hq).1)
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le
        (Finset.filter_subset _ _) (fun q hq => by
          linarith [hv q (Finset.mem_filter.mp hq).1, hc q (Finset.mem_filter.mp hq).1])
        (fun q hq _ => by linarith [hv q hq, hc q hq])
  calc
    _ ≤ v p * (∏ q ∈ s, c q) := mul_le_mul_of_nonneg_left hprefix (hv p hp)
    _ = _ := mul_comm _ _

theorem singular_tail_increment_upper (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p)
    (k : ℤ) :
    (∏ p ∈ s, localSingularFactor p (k : ZMod (p ^ 2))) ≤
      1 + (∏ p ∈ s, (p : ℝ) / (p - 1)) *
        ∑ p ∈ s, localSingularExcess p (k : ZMod (p ^ 2)) := by
  calc
    _ ≤ ∏ p ∈ s, (1 + localSingularExcess p (k : ZMod (p ^ 2))) :=
      Finset.prod_le_prod (fun p hp => localSingularFactor_nonneg p (hs p hp) _)
        (fun p _ => by
          have h := le_max_left (localSingularFactor p (k : ZMod (p ^ 2)) - 1) 0
          change _ ≤ 1 + max _ _
          linarith)
    _ ≤ _ := product_increment_upper s _ _
      (fun _ _ => le_max_right _ _)
      (fun p hp => one_add_localSingularExcess_le p (hs p hp) _)

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def singularProductOn (s : Finset ℕ) (k : ℤ) : ℝ :=
  ∏ p ∈ s, localSingularFactor p (k : ZMod (p ^ 2))

noncomputable def singularExcessAt (p : ℕ) (k : ℤ) : ℝ :=
  localSingularExcess p (k : ZMod (p ^ 2))

noncomputable def singularMajorant (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, (p : ℝ) / (p - 1)

theorem singularProductOn_nonneg (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (k : ℤ) :
    0 ≤ singularProductOn s k :=
  Finset.prod_nonneg (fun p hp => localSingularFactor_nonneg p (hs p hp).two_le _)

theorem singular_mixed_finset_mean (s u : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (H : ℕ) (hH : 0 < H) :
    pairMean H (fun k => ∏ p ∈ s, if p ∈ u then singularExcessAt p k
      else localSingularFactor p (k : ZMod (p ^ 2))) ≤
      (1 + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) *
        ∏ p ∈ s, if p ∈ u then 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  classical
  have h := singular_mixed_average_upper (fun p : s => (p : ℕ)) Subtype.val_injective
    (fun p => hs p p.property) (Finset.univ.filter (fun p : s => (p : ℕ) ∈ u)) H hH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  have hvalue (i j : ℕ) :
      (∏ p : s, if (p : ℕ) ∈ u then
        localSingularExcess p ((i : ZMod ((p : ℕ) ^ 2)) - j)
      else localSingularFactor p ((i : ZMod ((p : ℕ) ^ 2)) - j)) =
      ∏ p ∈ s, if p ∈ u then localSingularExcess p ((i : ZMod (p ^ 2)) - j)
        else localSingularFactor p ((i : ZMod (p ^ 2)) - j) :=
    Finset.prod_coe_sort s (fun p => if p ∈ u then
      localSingularExcess p ((i : ZMod (p ^ 2)) - j)
      else localSingularFactor p ((i : ZMod (p ^ 2)) - j))
  have hmodulus := Finset.prod_coe_sort s (fun p => p ^ 2)
  have hmean := Finset.prod_coe_sort s (fun p => if p ∈ u then 1 / ((p : ℝ) - 1) ^ 2 else 1)
  simp_rw [hvalue] at h
  rw [hmodulus, hmean] at h
  simpa only [pairMean, singularExcessAt, Int.cast_sub, Int.cast_natCast] using h

theorem singularProductOn_mean (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (H : ℕ) (hH : 0 < H) :
    pairMean H (singularProductOn s) ≤ 1 + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ) := by
  change pairMean H (fun k => ∏ p ∈ s, localSingularFactor p (k : ZMod (p ^ 2))) ≤ _
  simpa only [Finset.notMem_empty, ite_false,
    Finset.prod_const_one, mul_one] using singular_mixed_finset_mean s ∅ hs H hH

theorem singularProductOn_excess_mean (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (q : ℕ) (hq : q.Prime) (hqs : q ∉ s) (H : ℕ) (hH : 0 < H) :
    pairMean H (fun k => singularProductOn s k * singularExcessAt q k) ≤
      (1 + ((q ^ 2 * ∏ p ∈ s, p ^ 2 : ℕ) : ℝ) / H) /
        ((q : ℝ) - 1) ^ 2 := by
  classical
  have hs' : ∀ p ∈ insert q s, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq
    · exact hs p hp
  have h := singular_mixed_finset_mean (insert q s) {q} hs' H hH
  have hfun : (fun k : ℤ => ∏ p ∈ insert q s, if p ∈ ({q} : Finset ℕ)
      then singularExcessAt p k else localSingularFactor p (k : ZMod (p ^ 2))) =
      (fun k => singularProductOn s k * singularExcessAt q k) := by
    funext k
    rw [Finset.prod_insert hqs]
    simp only [Finset.mem_singleton, ite_true]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hpq : p ≠ q := fun heq => hqs (heq ▸ hp)
    simp only [hpq, ite_false]
  have hprod : (∏ p ∈ insert q s, if p ∈ ({q} : Finset ℕ)
      then 1 / ((p : ℝ) - 1) ^ 2 else 1) = 1 / ((q : ℝ) - 1) ^ 2 := by
    rw [Finset.prod_insert hqs]
    simp only [Finset.mem_singleton, ite_true]
    have heq : (∏ p ∈ s, if p = q then 1 / ((p : ℝ) - 1) ^ 2 else 1) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hpq : p ≠ q := fun heq => hqs (heq ▸ hp)
      simp only [hpq, ite_false]
    rw [heq, mul_one]
  rw [hfun, hprod, Finset.prod_insert hqs] at h
  simpa only [div_eq_mul_inv, one_mul] using h

theorem singularProductOn_union (s t : Finset ℕ) (hst : Disjoint s t) (k : ℤ) :
    singularProductOn (s ∪ t) k = singularProductOn s k * singularProductOn t k :=
  Finset.prod_union hst

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem singularMajorant_nonneg (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    0 ≤ singularMajorant s := by
  apply Finset.prod_nonneg
  intro p hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
  exact div_nonneg (by positivity) (by linarith)

theorem singularProductOn_le_majorant (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (k : ℤ) :
    singularProductOn s k ≤ singularMajorant s :=
  Finset.prod_le_prod (fun p hp => localSingularFactor_nonneg p (hs p hp).two_le _)
    (fun p hp => localSingularFactor_le p (hs p hp).two_le _)

theorem singular_range_mean_increment (s t : Finset ℕ) (hst : Disjoint s t)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime) (H : ℕ) :
    pairMean H (singularProductOn (s ∪ t)) ≤ pairMean H (singularProductOn s) +
      singularMajorant t * ∑ p ∈ t,
        pairMean H (fun k => singularProductOn s k * singularExcessAt p k) := by
  have hpoint (k : ℤ) : singularProductOn (s ∪ t) k ≤ singularProductOn s k +
      singularMajorant t * ∑ p ∈ t, singularProductOn s k * singularExcessAt p k := by
    have htail := singular_tail_increment_upper t (fun p hp => (ht p hp).two_le) k
    change singularProductOn t k ≤ 1 + singularMajorant t * ∑ p ∈ t, singularExcessAt p k at htail
    have h := mul_le_mul_of_nonneg_left htail (singularProductOn_nonneg s hs k)
    rw [singularProductOn_union s t hst]
    calc
      _ ≤ singularProductOn s k * (1 + singularMajorant t * ∑ p ∈ t, singularExcessAt p k) := h
      _ = _ := by
        simp only [Finset.mul_sum, mul_add, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have h := pairMean_mono H hpoint
  simpa only [pairMean_add, pairMean_mul_const, pairMean_sum] using h

theorem singular_excess_mean_bound (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (q : ℕ) (hq : q.Prime) (hqs : q ∉ s) (H : ℕ) (hH : 0 < H) :
    pairMean H (fun k => singularProductOn s k * singularExcessAt q k) ≤
      4 * (((q : ℝ) ^ 2)⁻¹ + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
  have h := singularProductOn_excess_mean s hs q hq hqs H hH
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hH0 : 0 < (H : ℝ) := by exact_mod_cast hH
  have hnonneg : 0 ≤ 1 + (q : ℝ) ^ 2 * (∏ p ∈ s, p ^ 2 : ℕ) / H := by positivity
  have hbound := mul_le_mul_of_nonneg_left (shifted_reciprocal_square_le q hq.two_le) hnonneg
  have heq : (1 + (q : ℝ) ^ 2 * (∏ p ∈ s, p ^ 2 : ℕ) / H) *
      (4 * ((q : ℝ) ^ 2)⁻¹) =
      4 * (((q : ℝ) ^ 2)⁻¹ + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
    field_simp
  rw [heq] at hbound
  apply h.trans
  simpa only [Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv, one_mul] using hbound

theorem singular_range_mean_bound (s t : Finset ℕ) (hst : Disjoint s t)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (H m n : ℕ) (hH : 0 < H) (hm : 1 ≤ m) (hn : m ≤ n)
    (htail : t ⊆ Finset.Ioc m n) :
    pairMean H (singularProductOn (s ∪ t)) ≤ pairMean H (singularProductOn s) +
      4 * singularMajorant t * ((m : ℝ)⁻¹ +
        t.card * (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
  have hinc := singular_range_mean_increment s t hst hs ht H
  have hsum : (∑ p ∈ t, pairMean H (fun k => singularProductOn s k * singularExcessAt p k)) ≤
      4 * ((m : ℝ)⁻¹ + t.card * (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) := by
    have heach := Finset.sum_le_sum (fun p hp => singular_excess_mean_bound s hs p (ht p hp)
      (fun hps => (Finset.disjoint_left.mp hst hps) hp) H hH)
    have htail' : (∑ p ∈ t, ((p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg htail
        (fun p _ _ => by positivity : ∀ p, p ∈ Finset.Ioc m n → p ∉ t → 0 ≤ ((p : ℝ) ^ 2)⁻¹)
      have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0) hn
      have hn0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
      linarith
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul] at heach
    simp only [div_eq_mul_inv] at heach ⊢
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (singularMajorant_nonneg t ht)
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem singularExcessAt_mean (q H : ℕ) (hq : q.Prime) (hH : 0 < H) :
    pairMean H (singularExcessAt q) ≤ 4 * (((q : ℝ) ^ 2)⁻¹ + 1 / (H : ℝ)) := by
  change pairMean H (fun k => singularExcessAt q k) ≤ _
  simpa only [singularProductOn, Finset.prod_empty, Nat.cast_one, one_mul] using
    singular_excess_mean_bound ∅ (by simp) q hq (by simp) H hH

theorem singular_excess_mean_coarse (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (q H : ℕ) (hq : q.Prime) (hH : 0 < H) :
    pairMean H (fun k => singularProductOn s k * singularExcessAt q k) ≤
      4 * singularMajorant s * (((q : ℝ) ^ 2)⁻¹ + 1 / (H : ℝ)) := by
  have hpoint (k : ℤ) : singularProductOn s k * singularExcessAt q k ≤
      singularMajorant s * singularExcessAt q k :=
    mul_le_mul_of_nonneg_right (singularProductOn_le_majorant s hs k) (le_max_right _ _)
  have h := pairMean_mono H hpoint
  rw [pairMean_mul_const] at h
  have hbound := mul_le_mul_of_nonneg_left (singularExcessAt_mean q H hq hH)
    (singularMajorant_nonneg s hs)
  nlinarith

theorem singular_range_mean_bound_coarse (s t : Finset ℕ) (hst : Disjoint s t)
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (H m n : ℕ) (hH : 0 < H) (hm : 1 ≤ m) (hn : m ≤ n)
    (htail : t ⊆ Finset.Ioc m n) :
    pairMean H (singularProductOn (s ∪ t)) ≤ pairMean H (singularProductOn s) +
      4 * singularMajorant s * singularMajorant t *
        ((m : ℝ)⁻¹ + t.card / (H : ℝ)) := by
  have hinc := singular_range_mean_increment s t hst hs ht H
  have hsum : (∑ p ∈ t, pairMean H (fun k => singularProductOn s k * singularExcessAt p k)) ≤
      4 * singularMajorant s * ((m : ℝ)⁻¹ + t.card / (H : ℝ)) := by
    have heach := Finset.sum_le_sum (fun p hp => singular_excess_mean_coarse s hs p H (ht p hp) hH)
    have htail' : (∑ p ∈ t, ((p : ℝ) ^ 2)⁻¹) ≤ (m : ℝ)⁻¹ := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg htail
        (fun p _ _ => by positivity : ∀ p, p ∈ Finset.Ioc m n → p ∉ t → 0 ≤ ((p : ℝ) ^ 2)⁻¹)
      have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0) hn
      have hn0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
      linarith
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at heach
    have hfactor : 0 ≤ 4 * singularMajorant s := mul_nonneg (by norm_num) (singularMajorant_nonneg s hs)
    have hscaled := mul_le_mul_of_nonneg_left htail' hfactor
    simp only [div_eq_mul_inv, one_mul] at heach ⊢
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (singularMajorant_nonneg t ht)
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem singularMajorant_union (s t : Finset ℕ) (hst : Disjoint s t) :
    singularMajorant (s ∪ t) = singularMajorant s * singularMajorant t :=
  Finset.prod_union hst

theorem singular_three_ranges_mean_bound (s t u : Finset ℕ)
    (hst : s ⊆ t) (htu : t ⊆ u) (hu : ∀ p ∈ u, p.Prime)
    (H m n r : ℕ) (hH : 0 < H) (hm : 1 ≤ m) (hmn : m ≤ n) (hnr : n ≤ r)
    (hfirst : t \ s ⊆ Finset.Ioc m n) (hsecond : u \ t ⊆ Finset.Ioc n r) :
    pairMean H (singularProductOn u) ≤
      1 + (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ) +
      4 * singularMajorant (t \ s) *
        ((m : ℝ)⁻¹ + (t \ s).card * (∏ p ∈ s, p ^ 2 : ℕ) / (H : ℝ)) +
      4 * singularMajorant u * ((n : ℝ)⁻¹ + (u \ t).card / (H : ℝ)) := by
  have ht : ∀ p ∈ t, p.Prime := fun p hp => hu p (htu hp)
  have hs : ∀ p ∈ s, p.Prime := fun p hp => ht p (hst hp)
  have hst' : Disjoint s (t \ s) := Finset.disjoint_left.mpr
    (fun p hp hdiff => (Finset.mem_sdiff.mp hdiff).2 hp)
  have htu' : Disjoint t (u \ t) := Finset.disjoint_left.mpr
    (fun p hp hdiff => (Finset.mem_sdiff.mp hdiff).2 hp)
  have hsplit1 : s ∪ (t \ s) = t := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hst]
  have hsplit2 : t ∪ (u \ t) = u := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset htu]
  have hlow := singularProductOn_mean s hs H hH
  have hmiddle := singular_range_mean_bound s (t \ s) hst' hs
    (fun p hp => ht p (Finset.mem_sdiff.mp hp).1) H m n hH hm hmn hfirst
  have hupper := singular_range_mean_bound_coarse t (u \ t) htu' ht
    (fun p hp => hu p (Finset.mem_sdiff.mp hp).1) H n r hH (hm.trans hmn) hnr hsecond
  rw [hsplit1] at hmiddle
  rw [hsplit2] at hupper
  have hprod := singularMajorant_union t (u \ t) htu'
  rw [hsplit2] at hprod
  rw [mul_assoc 4 (singularMajorant t), ← hprod] at hupper
  linarith

theorem singular_mean_extension (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ p ∈ t, p.Prime) (H : ℕ) :
    pairMean H (singularProductOn t) ≤ singularMajorant (t \ s) *
      pairMean H (singularProductOn s) := by
  have hs : ∀ p ∈ s, p.Prime := fun p hp => ht p (hst hp)
  have hdisj : Disjoint s (t \ s) := Finset.disjoint_left.mpr
    (fun p hp hdiff => (Finset.mem_sdiff.mp hdiff).2 hp)
  have hsplit : s ∪ (t \ s) = t := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hst]
  have hpoint (k : ℤ) : singularProductOn t k ≤
      singularMajorant (t \ s) * singularProductOn s k := by
    conv_lhs => rw [← hsplit, singularProductOn_union s (t \ s) hdisj]
    have h := mul_le_mul_of_nonneg_left
      (singularProductOn_le_majorant (t \ s) (fun p hp => ht p (Finset.mem_sdiff.mp hp).1) k)
      (singularProductOn_nonneg s hs k)
    simpa only [mul_comm] using h
  simpa only [pairMean_mul_const] using pairMean_mono H hpoint

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem prime_band_subset_Ioc {x y : ℝ} :
    primesUpToReal y \ primesUpToReal x ⊆ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
  intro p hp
  obtain ⟨hpy, hpx⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hprime, hpy⟩ := (mem_primesUpToReal y p).mp hpy
  have hpx' : x < (p : ℝ) := by
    by_contra h
    exact hpx ((mem_primesUpToReal x p).mpr ⟨hprime, le_of_not_gt h⟩)
  have hlower : ⌊x⌋₊ < p := Nat.lt_of_not_ge (fun h =>
    (not_le_of_gt hpx') ((Nat.le_floor_iff' hprime.ne_zero).mp h))
  exact Finset.mem_Ioc.mpr ⟨hlower, Nat.le_floor hpy⟩

theorem prime_band_card_le {x y : ℝ} :
    (primesUpToReal y \ primesUpToReal x).card ≤ ⌊y⌋₊ := by
  have h := Finset.card_le_card (prime_band_subset_Ioc (x := x) (y := y))
  rw [Nat.card_Ioc] at h
  omega

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

noncomputable def primeSquarePeriod (y : ℝ) : ℕ :=
  ∏ p ∈ primesUpToReal y, p ^ 2

theorem primeSquarePeriod_pos (y : ℝ) : 0 < primeSquarePeriod y := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos ((mem_primesUpToReal y p).mp hp).1.pos 2

theorem log_primeSquarePeriod (y : ℝ) :
    Real.log (primeSquarePeriod y : ℝ) = 2 * Chebyshev.theta y := by
  unfold primeSquarePeriod
  rw [Nat.cast_prod, Real.log_prod]
  · simp_rw [Nat.cast_pow, Real.log_pow]
    change (∑ p ∈ primesUpToReal y, (2 : ℝ) * Real.log p) =
      2 * ∑ p ∈ primesUpToReal y, Real.log p
    rw [Finset.mul_sum]
  · intro p hp
    exact_mod_cast (pow_ne_zero 2 ((mem_primesUpToReal y p).mp hp).1.ne_zero)

theorem primeSquarePeriod_le_exp {y : ℝ} (hy : 0 ≤ y) :
    (primeSquarePeriod y : ℝ) ≤ Real.exp (2 * Real.log 4 * y) := by
  have hp : 0 < (primeSquarePeriod y : ℝ) := by exact_mod_cast primeSquarePeriod_pos y
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  rw [log_primeSquarePeriod]
  nlinarith [Chebyshev.theta_le_log4_mul_x hy]

theorem logarithmic_primeSquarePeriod_le {H : ℝ} (hH : 1 ≤ H) :
    (primeSquarePeriod (Real.log H / (8 * Real.log 4)) : ℝ) ≤ H ^ (1 / 4 : ℝ) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hbound := primeSquarePeriod_le_exp
    (div_nonneg (Real.log_nonneg hH) (by positivity : 0 ≤ 8 * Real.log 4))
  have heq : 2 * Real.log 4 * (Real.log H / (8 * Real.log 4)) = Real.log H * (1 / 4) := by
    field_simp
    ring
  rw [heq, ← Real.rpow_def_of_pos hH0] at hbound
  exact hbound

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem singular_cutoff_mean_bound (y₀ y₁ y₂ : ℝ) (H : ℕ)
    (h01 : y₀ ≤ y₁) (h12 : y₁ ≤ y₂) (hfloor : 1 ≤ ⌊y₀⌋₊) (hH : 0 < H) :
    pairMean H (singularFactorProduct y₂) ≤
      1 + (primeSquarePeriod y₀ : ℝ) / H +
      4 * singularMajorant (primesUpToReal y₁ \ primesUpToReal y₀) *
        ((⌊y₀⌋₊ : ℝ)⁻¹ + ⌊y₁⌋₊ * (primeSquarePeriod y₀ : ℝ) / H) +
      4 * singularMajorant (primesUpToReal y₂) *
        ((⌊y₁⌋₊ : ℝ)⁻¹ + (⌊y₂⌋₊ : ℝ) / H) := by
  have hprime (y : ℝ) : ∀ p ∈ primesUpToReal y, p.Prime :=
    fun p hp => ((mem_primesUpToReal y p).mp hp).1
  have h := singular_three_ranges_mean_bound (primesUpToReal y₀) (primesUpToReal y₁)
    (primesUpToReal y₂) (primesUpToReal_subset h01) (primesUpToReal_subset h12)
    (hprime y₂) H ⌊y₀⌋₊ ⌊y₁⌋₊ ⌊y₂⌋₊ hH hfloor (Nat.floor_mono h01) (Nat.floor_mono h12)
    prime_band_subset_Ioc prime_band_subset_Ioc
  have hc1 : ((primesUpToReal y₁ \ primesUpToReal y₀).card : ℝ) ≤ ⌊y₁⌋₊ :=
    by exact_mod_cast (prime_band_card_le (x := y₀) (y := y₁))
  have hc2 : ((primesUpToReal y₂ \ primesUpToReal y₁).card : ℝ) ≤ ⌊y₂⌋₊ :=
    by exact_mod_cast (prime_band_card_le (x := y₁) (y := y₂))
  have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
  have hterm1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg (primeSquarePeriod y₀))) hH0
  have hterm2 := div_le_div_of_nonneg_right hc2 hH0
  have hmajor1 : 0 ≤ singularMajorant (primesUpToReal y₁ \ primesUpToReal y₀) :=
    singularMajorant_nonneg _ (fun p hp => hprime y₁ p (Finset.mem_sdiff.mp hp).1)
  have hmajor2 := singularMajorant_nonneg _ (hprime y₂)
  have hscaled1 := mul_le_mul_of_nonneg_left hterm1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmajor1)
  have hscaled2 := mul_le_mul_of_nonneg_left hterm2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmajor2)
  change pairMean H (singularProductOn (primesUpToReal y₂)) ≤ _
  change pairMean H (singularProductOn (primesUpToReal y₂)) ≤
    1 + (primeSquarePeriod y₀ : ℝ) / H + _ + _ at h
  have hM : (∏ p ∈ primesUpToReal y₀, p ^ 2) = primeSquarePeriod y₀ := rfl
  rw [hM] at h
  nlinarith

end Erdos676
end

section
open Filter Asymptotics
open scoped Topology BigOperators

namespace Erdos676

theorem singularMajorant_primes (y : ℝ) :
    singularMajorant (primesUpToReal y) = (survivalProduct y)⁻¹ := by
  unfold singularMajorant survivalProduct
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast ((mem_primesUpToReal y p).mp hp).1.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem singularMajorant_band {y z : ℝ} (hyz : y ≤ z) :
    singularMajorant (primesUpToReal z \ primesUpToReal y) =
      survivalProduct y / survivalProduct z := by
  have h := Finset.prod_sdiff (f := fun p : ℕ => (p : ℝ) / (p - 1))
    (primesUpToReal_subset hyz)
  change singularMajorant (primesUpToReal z \ primesUpToReal y) *
    singularMajorant (primesUpToReal y) = singularMajorant (primesUpToReal z) at h
  rw [singularMajorant_primes, singularMajorant_primes] at h
  have hy := (survivalProduct_pos y).ne'
  have hz := (survivalProduct_pos z).ne'
  field_simp at h ⊢
  nlinarith

theorem survival_ratio_formula {y z : ℝ} (hy : 1 < y) (hz : 1 < z) :
    survivalProduct y / survivalProduct z =
      Real.exp (Mertens.E₃ y - Mertens.E₃ z) * (Real.log z / Real.log y) := by
  rw [survivalProduct_formula hy, survivalProduct_formula hz, Real.exp_sub]
  have hylog := (Real.log_pos hy).ne'
  have hzlog := (Real.log_pos hz).ne'
  have he := Real.exp_ne_zero (-Real.eulerMascheroniConstant)
  have hez := Real.exp_ne_zero (Mertens.E₃ z)
  field_simp

theorem survival_ratio_limit {f g : ℝ → ℝ} {L : ℝ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop)
    (hlog : Tendsto (fun x => Real.log (g x) / Real.log (f x)) atTop (nhds L)) :
    Tendsto (fun x => survivalProduct (f x) / survivalProduct (g x)) atTop (nhds L) := by
  have hE : Tendsto Mertens.E₃ atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hexp : Tendsto (fun x => Real.exp (Mertens.E₃ (f x) - Mertens.E₃ (g x)))
      atTop (nhds (1 : ℝ)) := by
    simpa only [sub_self, Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp ((hE.comp hf).sub (hE.comp hg))
  have hprod := hexp.mul hlog
  simp only [one_mul] at hprod
  apply Filter.Tendsto.congr' _ hprod
  filter_upwards [hf.eventually (eventually_gt_atTop (1 : ℝ)),
    hg.eventually (eventually_gt_atTop (1 : ℝ))] with x hfx hgx
  exact (survival_ratio_formula hfx hgx).symm

end Erdos676
end

section
open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem exists_survival_ratio_log_bound :
    ∃ T : ℝ, 1 < T ∧ ∀ y z : ℝ, T ≤ y → T ≤ z →
      survivalProduct y / survivalProduct z ≤
        Real.exp 2 * (Real.log z / Real.log y) := by
  have hE : Tendsto Mertens.E₃ atTop (nhds (0 : ℝ)) :=
    (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hlo : ∀ᶠ y in atTop, (-1 : ℝ) < Mertens.E₃ y :=
    (tendsto_order.mp hE).1 _ (by norm_num)
  have hhi : ∀ᶠ y in atTop, Mertens.E₃ y < (1 : ℝ) :=
    (tendsto_order.mp hE).2 _ (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlo.and hhi)
  refine ⟨max 2 T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro y z hy hz
  have hy1 : 1 < y := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hy)
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hz)
  have hyE := hT y ((le_max_right _ _).trans hy)
  have hzE := hT z ((le_max_right _ _).trans hz)
  rw [survival_ratio_formula hy1 hz1]
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (Real.log_pos hz1).le (Real.log_pos hy1).le)
  exact Real.exp_le_exp.mpr (by linarith)

theorem exists_singularMajorant_log_bound :
    ∃ C T : ℝ, 0 < C ∧ 1 < T ∧ ∀ y : ℝ, T ≤ y →
      singularMajorant (primesUpToReal y) ≤ C * Real.log y := by
  obtain ⟨c, hc, hevent⟩ := exists_eventual_survival_lower
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨c⁻¹, max 2 T, inv_pos.mpr hc,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro y hy
  have hy1 : 1 < y := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hy)
  have hV := hT y ((le_max_right _ _).trans hy)
  have hproduct := (div_le_iff₀ (Real.log_pos hy1)).mp hV
  rw [singularMajorant_primes]
  apply (inv_le_iff_one_le_mul₀ (survivalProduct_pos y)).mpr
  have hscaled := mul_le_mul_of_nonneg_left hproduct (inv_nonneg.mpr hc.le)
  simpa only [inv_mul_cancel₀ hc.ne', mul_comm, mul_left_comm, mul_assoc] using hscaled

end Erdos676
end

section
open Filter Asymptotics
open scoped Topology

namespace Erdos676

noncomputable def logarithmicCutoff (x : ℝ) : ℝ := Real.log x / (8 * Real.log 4)

theorem logarithmicCutoff_tendsto : Tendsto logarithmicCutoff atTop atTop := by
  exact Real.tendsto_log_atTop.atTop_div_const
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

theorem logarithmicCutoff_eventually_le_power {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, logarithmicCutoff x ≤ x ^ b := by
  have h := eventually_log_le_power hb
    (mul_pos (by norm_num : (0 : ℝ) < 8) (Real.log_pos (by norm_num : (1 : ℝ) < 4)))
  filter_upwards [h] with x hx
  exact (div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos (by norm_num)))).mpr
    (by simpa only [mul_comm] using hx)

theorem inverse_floor_le_twice_inverse {x : ℝ} (hx : 2 ≤ x) :
    (⌊x⌋₊ : ℝ)⁻¹ ≤ 2 / x := by
  have hx0 : 0 < x := by linarith
  have hfloor := floor_ge_half hx
  have hhalf : 0 < x / 2 := by positivity
  have h := one_div_le_one_div_of_le hhalf hfloor
  simpa only [one_div, inv_div] using h

noncomputable def singularCoreError (C b x : ℝ) : ℝ :=
  x ^ (-(3 / 4 : ℝ)) +
  (64 * Real.log 4 * Real.exp 2) / Real.log (logarithmicCutoff x) +
  (4 * Real.exp 2) * (Real.log x / x ^ (1 / 2 : ℝ)) +
  (8 * C * b) * (Real.log x / x ^ (1 / 4 : ℝ)) +
  (4 * C * b) * (Real.log x / x ^ (1 - b))

theorem singularCoreError_tendsto (C : ℝ) {b : ℝ} (hb : b < 1) :
    Tendsto (singularCoreError C b) atTop (nhds 0) := by
  change Tendsto (fun x => singularCoreError C b x) atTop (nhds 0)
  have hzero := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)
  have hlog := (Real.tendsto_log_atTop.comp logarithmicCutoff_tendsto).inv_tendsto_atTop
  have hhalf := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hquarter := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hlast := (isLittleO_log_rpow_atTop (by linarith : 0 < 1 - b)).tendsto_div_nhds_zero
  have h := (((hzero.add (hlog.const_mul (64 * Real.log 4 * Real.exp 2))).add
    (hhalf.const_mul (4 * Real.exp 2))).add (hquarter.const_mul (8 * C * b))).add
    (hlast.const_mul (4 * C * b))
  simpa only [singularCoreError, div_eq_mul_inv, mul_zero, add_zero,
    Pi.inv_apply, Function.comp_apply] using h

end Erdos676
end

section
namespace Erdos676

theorem rpow_div_self {x : ℝ} (hx : 0 < x) (r : ℝ) :
    x ^ r / x = 1 / x ^ (1 - r) := by
  rw [Real.rpow_sub hx 1 r, Real.rpow_one, one_div_div]

theorem first_range_error_bound {x A B : ℝ} (hx : 1 < x)
    (hlogY : 1 ≤ Real.log (logarithmicCutoff x)) (hB0 : 0 ≤ B)
    (hA : A ≤ Real.exp 2 * Real.log x / Real.log (logarithmicCutoff x))
    (hB : B ≤ 2 / logarithmicCutoff x + 1 / x ^ (1 / 2 : ℝ)) :
    4 * A * B ≤ (64 * Real.log 4 * Real.exp 2) / Real.log (logarithmicCutoff x) +
      (4 * Real.exp 2) * (Real.log x / x ^ (1 / 2 : ℝ)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hly : 0 < Real.log (logarithmicCutoff x) := by linarith
  have hupper0 : 0 ≤ Real.exp 2 * Real.log x / Real.log (logarithmicCutoff x) := by positivity
  have hmul := mul_le_mul hA hB hB0 hupper0
  have hscale := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 4)
  have hratio : Real.log x / Real.log (logarithmicCutoff x) ≤ Real.log x :=
    div_le_self hlx.le hlogY
  have hterm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * Real.exp 2))
    (Real.rpow_nonneg hx0.le (1 / 2 : ℝ))
  calc
    4 * A * B ≤ 4 * (Real.exp 2 * Real.log x / Real.log (logarithmicCutoff x)) *
        (2 / logarithmicCutoff x + 1 / x ^ (1 / 2 : ℝ)) := by nlinarith [hscale]
    _ = (64 * Real.log 4 * Real.exp 2) / Real.log (logarithmicCutoff x) +
        (4 * Real.exp 2) * (Real.log x / Real.log (logarithmicCutoff x)) /
          x ^ (1 / 2 : ℝ) := by
      unfold logarithmicCutoff
      field_simp
      <;> ring
    _ ≤ _ := add_le_add le_rfl (by simpa only [mul_div_assoc] using hterm)

theorem second_range_error_bound {x A B C b : ℝ} (_hx : 0 < x)
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hlog : 0 ≤ Real.log x) (hB0 : 0 ≤ B)
    (hA : A ≤ C * b * Real.log x)
    (hB : B ≤ 2 / x ^ (1 / 4 : ℝ) + 1 / x ^ (1 - b)) :
    4 * A * B ≤ (8 * C * b) * (Real.log x / x ^ (1 / 4 : ℝ)) +
      (4 * C * b) * (Real.log x / x ^ (1 - b)) := by
  have hmul := mul_le_mul hA hB hB0 (mul_nonneg (mul_nonneg hC hb) hlog)
  have hscale := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 4)
  calc
    4 * A * B = 4 * (A * B) := by ring
    _ ≤ _ := hscale
    _ = _ := by ring

end Erdos676
end

section
namespace Erdos676

theorem singular_core_bound (H : ℕ) (C b : ℝ) (hH : 1 < (H : ℝ))
    (hC : 0 ≤ C) (hb : (1 / 4 : ℝ) ≤ b)
    (hy : 2 ≤ logarithmicCutoff H) (hlogy : 1 ≤ Real.log (logarithmicCutoff H))
    (hyquarter : logarithmicCutoff H ≤ (H : ℝ) ^ (1 / 4 : ℝ))
    (hmajor1 : singularMajorant (primesUpToReal ((H : ℝ) ^ (1 / 4 : ℝ)) \
        primesUpToReal (logarithmicCutoff H)) ≤
      Real.exp 2 * Real.log H / Real.log (logarithmicCutoff H))
    (hmajor2 : singularMajorant (primesUpToReal ((H : ℝ) ^ b)) ≤ C * b * Real.log H) :
    pairMean H (singularFactorProduct ((H : ℝ) ^ b)) ≤ 1 + singularCoreError C b H := by
  let x : ℝ := H
  let y : ℝ := logarithmicCutoff x
  have hx : 1 < x := hH
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hHnat : 0 < H := by exact_mod_cast (lt_trans zero_lt_one hH)
  have hq : 2 ≤ x ^ (1 / 4 : ℝ) := hy.trans hyquarter
  have hy1 : (1 : ℝ) ≤ y := by dsimp [y, x]; linarith
  have hfloor : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hy1)
  have horder := Real.rpow_le_rpow_of_exponent_le hx.le hb
  have h := singular_cutoff_mean_bound y (x ^ (1 / 4 : ℝ)) (x ^ b) H hyquarter horder hfloor hHnat
  have hM : (primeSquarePeriod y : ℝ) ≤ x ^ (1 / 4 : ℝ) := logarithmic_primeSquarePeriod_le hx.le
  have hbase : (primeSquarePeriod y : ℝ) / x ≤ x ^ (-(3 / 4 : ℝ)) := by
    have hdiv := div_le_div_of_nonneg_right hM hx0.le
    have heq : x ^ (1 / 4 : ℝ) / x = x ^ (-(3 / 4 : ℝ)) := by
      rw [rpow_div_self hx0, Real.rpow_neg hx0.le]
      norm_num
    rwa [heq] at hdiv
  have hinv0 : (⌊y⌋₊ : ℝ)⁻¹ ≤ 2 / y := inverse_floor_le_twice_inverse hy
  have hinv1 : (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ)⁻¹ ≤ 2 / x ^ (1 / 4 : ℝ) :=
    inverse_floor_le_twice_inverse hq
  have hfloor1 : (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hfloor2 : (⌊x ^ b⌋₊ : ℝ) ≤ x ^ b := Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hproduct : (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ) * (primeSquarePeriod y : ℝ) / x ≤
      1 / x ^ (1 / 2 : ℝ) := by
    have hmul := mul_le_mul hfloor1 hM (Nat.cast_nonneg (primeSquarePeriod y))
      (Real.rpow_nonneg hx0.le (1 / 4 : ℝ))
    have hdiv := div_le_div_of_nonneg_right hmul hx0.le
    have heq : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) / x = 1 / x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
      rw [rpow_div_self hx0]
      norm_num
    rwa [heq] at hdiv
  have hlast : (⌊x ^ b⌋₊ : ℝ) / x ≤ 1 / x ^ (1 - b) := by
    have hdiv := div_le_div_of_nonneg_right hfloor2 hx0.le
    rwa [rpow_div_self hx0] at hdiv
  have herr1 := first_range_error_bound hx hlogy
    (by positivity : 0 ≤ (⌊y⌋₊ : ℝ)⁻¹ + (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ) * (primeSquarePeriod y : ℝ) / x)
    hmajor1 (add_le_add hinv0 hproduct)
  have herr2 := second_range_error_bound hx0 hC (by linarith : 0 ≤ b) (Real.log_pos hx).le
    (by positivity : 0 ≤ (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ)⁻¹ + (⌊x ^ b⌋₊ : ℝ) / x)
    hmajor2 (add_le_add hinv1 hlast)
  change pairMean H (singularFactorProduct (x ^ b)) ≤ 1 + singularCoreError C b x
  unfold singularCoreError
  nlinarith

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem exists_singular_core_error_bound {b : ℝ} (hb : (1 / 4 : ℝ) ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℕ in atTop,
      pairMean H (singularFactorProduct ((H : ℝ) ^ b)) ≤ 1 + singularCoreError C b H := by
  obtain ⟨T₁, hT₁, hratio⟩ := exists_survival_ratio_log_bound
  obtain ⟨C, T₂, hC, hT₂, hmajor⟩ := exists_singularMajorant_log_bound
  refine ⟨C, hC, ?_⟩
  have hevent : ∀ᶠ x : ℝ in atTop, 1 < x ∧ 2 ≤ logarithmicCutoff x ∧
      Real.exp 1 ≤ logarithmicCutoff x ∧ T₁ ≤ logarithmicCutoff x ∧
      T₂ ≤ logarithmicCutoff x ∧ logarithmicCutoff x ≤ x ^ (1 / 4 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), logarithmicCutoff_tendsto.eventually_ge_atTop 2,
      logarithmicCutoff_tendsto.eventually_ge_atTop (Real.exp 1),
      logarithmicCutoff_tendsto.eventually_ge_atTop T₁,
      logarithmicCutoff_tendsto.eventually_ge_atTop T₂,
      logarithmicCutoff_eventually_le_power (by norm_num : (0 : ℝ) < 1 / 4)]
      with x hx hy hexp h₁ h₂ hpower
    exact ⟨hx, hy, hexp, h₁, h₂, hpower⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hevent] with H hH
  obtain ⟨hx, hy, hexp, h₁, h₂, hpower⟩ := hH
  have hx0 : 0 < (H : ℝ) := lt_trans zero_lt_one hx
  have hlogy : 1 ≤ Real.log (logarithmicCutoff H) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  have horder : (H : ℝ) ^ (1 / 4 : ℝ) ≤ (H : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hx.le hb
  have hmajor1 : singularMajorant (primesUpToReal ((H : ℝ) ^ (1 / 4 : ℝ)) \
      primesUpToReal (logarithmicCutoff H)) ≤
      Real.exp 2 * Real.log H / Real.log (logarithmicCutoff H) := by
    rw [singularMajorant_band hpower]
    have hfirst := hratio (logarithmicCutoff H) ((H : ℝ) ^ (1 / 4 : ℝ)) h₁ (h₁.trans hpower)
    have hlogpower : Real.log ((H : ℝ) ^ (1 / 4 : ℝ)) ≤ Real.log H := by
      rw [Real.log_rpow hx0]
      nlinarith [Real.log_pos hx]
    have hsecond := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hlogpower (by linarith : 0 ≤ Real.log (logarithmicCutoff H)))
      (Real.exp_pos 2).le
    exact hfirst.trans (by simpa only [mul_div_assoc] using hsecond)
  have hmajor2 : singularMajorant (primesUpToReal ((H : ℝ) ^ b)) ≤ C * b * Real.log H := by
    have h := hmajor ((H : ℝ) ^ b) (h₂.trans (hpower.trans horder))
    rw [Real.log_rpow hx0] at h
    simpa only [mul_assoc] using h
  exact singular_core_bound H C b hx hC.le hb hy hlogy hpower hmajor1 hmajor2

theorem singular_core_average_eventually {b ε : ℝ} (hb : (1 / 4 : ℝ) ≤ b)
    (hb1 : b < 1) (hε : 0 < ε) :
    ∀ᶠ H : ℕ in atTop,
      pairMean H (singularFactorProduct ((H : ℝ) ^ b)) ≤ 1 + ε := by
  obtain ⟨C, hC, hbound⟩ := exists_singular_core_error_bound hb
  have hlimit := (singularCoreError_tendsto C hb1).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have herr : ∀ᶠ H : ℕ in atTop, singularCoreError C b H < ε :=
    (tendsto_order.mp hlimit).2 ε hε
  filter_upwards [hbound, herr] with H hH hE
  linarith

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem powerFloor_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (powerFloor η) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [(tendsto_rpow_atTop hη).eventually_ge_atTop (n : ℝ)] with x hx
  exact Nat.le_floor hx

theorem log_powerFloor_ratio_bounds {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      η - Real.log 2 / Real.log x ≤ Real.log (powerFloor η x : ℝ) / Real.log x ∧
      Real.log (powerFloor η x : ℝ) / Real.log x ≤ η := by
  filter_upwards [(tendsto_rpow_atTop hη).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with x hp hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hpow0 : 0 < x ^ η := Real.rpow_pos_of_pos hx0 η
  have hhalf := floor_ge_half hp
  have hfloor0 : 0 < (powerFloor η x : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < x ^ η / 2) hhalf
  have hlo := Real.log_le_log (by positivity : 0 < x ^ η / 2) hhalf
  have hhi := Real.log_le_log hfloor0 (Nat.floor_le hpow0.le)
  rw [Real.log_div hpow0.ne' (by norm_num), Real.log_rpow hx0 η] at hlo
  rw [Real.log_rpow hx0 η] at hhi
  constructor
  · apply (le_div_iff₀ (Real.log_pos hx)).mpr
    have heq : (η - Real.log 2 / Real.log x) * Real.log x = η * Real.log x - Real.log 2 := by
      field_simp [(Real.log_pos hx).ne']
      <;> ring
    rwa [heq]
  · exact (div_le_iff₀ (Real.log_pos hx)).mpr hhi

theorem log_powerFloor_ratio_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ => Real.log (powerFloor η x : ℝ) / Real.log x) atTop (nhds η) := by
  have hsmall : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hlo : Tendsto (fun x : ℝ => η - Real.log 2 / Real.log x) atTop (nhds η) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    ((log_powerFloor_ratio_bounds hη).mono (fun _ h => h.1))
    ((log_powerFloor_ratio_bounds hη).mono (fun _ h => h.2))

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem cast_powerFloor_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ => (powerFloor η x : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).comp (powerFloor_tendsto hη)

theorem floor_power_cutoff_le {x η b α : ℝ} (hx : 1 ≤ x) (_hη : 0 < η)
    (hb : 0 < b) (hα : η * b ≤ α) :
    (powerFloor η x : ℝ) ^ b ≤ x ^ α := by
  calc
    _ ≤ (x ^ η) ^ b := Real.rpow_le_rpow (Nat.cast_nonneg _)
      (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hx) η)) hb.le
    _ = x ^ (η * b) := (Real.rpow_mul (zero_le_one.trans hx) η b).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx hα

theorem floor_survival_ratio_limit {η b α : ℝ}
    (hη : 0 < η) (hb : 0 < b) (hα : 0 < α) :
    Tendsto (fun x : ℝ => survivalProduct ((powerFloor η x : ℝ) ^ b) /
      survivalProduct (x ^ α)) atTop (nhds (α / (b * η))) := by
  apply survival_ratio_limit ((tendsto_rpow_atTop hb).comp (cast_powerFloor_tendsto hη))
    (tendsto_rpow_atTop hα)
  change Tendsto (fun x : ℝ => Real.log (x ^ α) / Real.log ((powerFloor η x : ℝ) ^ b))
    atTop (nhds (α / (b * η)))
  have hlim : Tendsto (fun x : ℝ => α / (b * (Real.log (powerFloor η x : ℝ) / Real.log x)))
      atTop (nhds (α / (b * η))) :=
    tendsto_const_nhds.div ((log_powerFloor_ratio_tendsto hη).const_mul b) (mul_pos hb hη).ne'
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ), (cast_powerFloor_tendsto hη).eventually_gt_atTop 1]
    with x hx hfloor
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hfloor0 : 0 < (powerFloor η x : ℝ) := lt_trans zero_lt_one hfloor
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlogfloor : Real.log (powerFloor η x : ℝ) ≠ 0 := (Real.log_pos hfloor).ne'
  rw [Real.log_rpow hx0 α, Real.log_rpow hfloor0 b]
  field_simp
  <;> ring

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem growing_singular_average {η b α ε : ℝ}
    (hη : 0 < η) (hb : (1 / 4 : ℝ) ≤ b) (hb1 : b < 1)
    (hα : 0 < α) (hcut : η * b ≤ α) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      pairMean (powerFloor η x) (singularFactorProduct (x ^ α)) ≤ α / (b * η) + ε := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  obtain ⟨C, hC, hcore⟩ := exists_singular_core_error_bound hb
  have herr := (singularCoreError_tendsto C hb1).comp (cast_powerFloor_tendsto hη)
  have hratio := floor_survival_ratio_limit hη hb0 hα
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlimit : Tendsto (fun x : ℝ =>
      (survivalProduct ((powerFloor η x : ℝ) ^ b) / survivalProduct (x ^ α)) *
        (1 + singularCoreError C b (powerFloor η x))) atTop (nhds (α / (b * η))) := by
    simpa only [add_zero, mul_one, Function.comp_apply] using hratio.mul (hone.add herr)
  have hsmall := (tendsto_order.mp hlimit).2 (α / (b * η) + ε) (by linarith)
  filter_upwards [(powerFloor_tendsto hη).eventually hcore,
    eventually_ge_atTop (1 : ℝ), hsmall] with x hxcore hx hxsmall
  have hcuts := floor_power_cutoff_le hx hη hb0 hcut
  have hext := singular_mean_extension (primesUpToReal ((powerFloor η x : ℝ) ^ b))
    (primesUpToReal (x ^ α)) (primesUpToReal_subset hcuts)
    (fun p hp => ((mem_primesUpToReal (x ^ α) p).mp hp).1) (powerFloor η x)
  change pairMean (powerFloor η x) (singularFactorProduct (x ^ α)) ≤
    singularMajorant (primesUpToReal (x ^ α) \ primesUpToReal ((powerFloor η x : ℝ) ^ b)) *
      pairMean (powerFloor η x) (singularFactorProduct ((powerFloor η x : ℝ) ^ b)) at hext
  rw [singularMajorant_band hcuts] at hext
  have hnonneg : 0 ≤ survivalProduct ((powerFloor η x : ℝ) ^ b) / survivalProduct (x ^ α) :=
    div_nonneg (survivalProduct_pos _).le (survivalProduct_pos _).le
  have hscale := mul_le_mul_of_nonneg_left hxcore hnonneg
  exact (hext.trans hscale).trans hxsmall.le

theorem original_singular_average {α ε : ℝ} (hα : 0 < α) (hsmall : α < 1 / 2)
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      pairMean (powerFloor (α * (1 - α ^ 2)) N) (singularFactorProduct ((N : ℝ) ^ α)) ≤
        1 / (1 - α ^ 2) ^ 2 + ε := by
  have hsq : 0 ≤ α ^ 2 := sq_nonneg α
  have hsqsmall : α ^ 2 < 1 / 4 := by nlinarith
  have hb : (1 / 4 : ℝ) ≤ 1 - α ^ 2 := by linarith
  have hb0 : 0 < 1 - α ^ 2 := by linarith
  have hb1 : 1 - α ^ 2 < 1 := by nlinarith
  have hη : 0 < α * (1 - α ^ 2) := mul_pos hα hb0
  have hcut : (α * (1 - α ^ 2)) * (1 - α ^ 2) ≤ α := by
    have hprod := mul_le_mul_of_nonneg_left (show (1 - α ^ 2) ^ 2 ≤ 1 by nlinarith) hα.le
    nlinarith
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (growing_singular_average hη hb hb1 hα hcut hε)
  have heq : α / ((1 - α ^ 2) * (α * (1 - α ^ 2))) = 1 / (1 - α ^ 2) ^ 2 := by
    field_simp
  simpa only [heq] using h

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem smallAverage_square_sum_eq_pairs (z H S N : ℕ) :
    (∑ n ∈ Finset.range N, (smallAverage z H (S + n)) ^ 2) =
      (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, smallPairCount z S N i j) / (H : ℝ) ^ 2 := by
  classical
  simp only [smallAverage, div_pow, ← Finset.sum_div]
  congr 1
  have h := weighted_square_expansion (Finset.range H) (Finset.range N) (fun _ => (1 : ℝ))
    (fun i n => if SmallAvoidance z (S + n + i) then (1 : ℝ) else 0) (fun _ => (1 : ℝ))
  simp only [one_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold smallPairCount
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hi' : SmallAvoidance z (S + n + i) <;>
    by_cases hj' : SmallAvoidance z (S + n + j) <;> simp [hi', hj']

theorem smallAverage_dyadic_square_sum_eq_pairs (z H X : ℕ) :
    (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage z H n) ^ 2) =
      (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, smallPairCount z (X + 1) X i j) / (H : ℝ) ^ 2 := by
  rw [sum_dyadic_interval_eq_range]
  exact smallAverage_square_sum_eq_pairs z H (X + 1) X

theorem smallAverage_second_upper (z H S N : ℕ) (hH : 0 < H)
    (V : ℕ → ℕ → ℝ) (B E : ℝ)
    (hpairs : ∀ i < H, ∀ j < H, smallPairCount z S N i j ≤ B * V i j + E) :
    (∑ n ∈ Finset.range N, (smallAverage z H (S + n)) ^ 2) ≤
      B * ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, V i j) / (H : ℝ) ^ 2) + E := by
  have hsum : (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, smallPairCount z S N i j) ≤
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, (B * V i j + E) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hpairs i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  rw [smallAverage_square_sum_eq_pairs]
  calc
    _ ≤ (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, (B * V i j + E)) / (H : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      have hHne : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hH)
      field_simp

end Erdos676
end

section
open Filter
open scoped Topology

namespace Erdos676

theorem pairSurvivalProduct_nonneg (z : ℝ) (k : ℤ) : 0 ≤ pairSurvivalProduct z k := by
  unfold pairSurvivalProduct
  apply Finset.prod_nonneg
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  exact sub_nonneg.mpr (twoPositionDensity_le_one p hprime.one_lt.le _)

theorem eventually_pair_cutoff_conditions {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hsmall : 20 * α ≤ ρ) :
    ∀ᶠ x : ℝ in atTop,
      2 ≤ x ^ α ∧ 2 ≤ powerFloor ρ x ∧ Real.log 4 + 4 ≤ Real.log (x ^ α) ∧
      20 * (Real.log (x ^ α)) ^ 2 ≤ (Real.log (powerFloor ρ x : ℝ)) ^ 2 / 2 ∧
      1 + 40 * (Real.log (x ^ α) / Real.log (powerFloor ρ x : ℝ)) ^ 2 ≤
        1 + 160 * (α / ρ) ^ 2 := by
  have hz := (tendsto_rpow_atTop hα).eventually_ge_atTop 2
  have hR := (tendsto_rpow_atTop hρ).eventually_ge_atTop 3
  have hlogz := (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hα)).eventually_ge_atTop (Real.log 4 + 4)
  filter_upwards [hz, hR, hlogz, eventually_log_powerFloor_lower hρ,
    eventually_gt_atTop (1 : ℝ)] with x hxz hxR hxlogz hxlogR hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hxlog : 0 < Real.log x := Real.log_pos hx1
  have hR2 : 2 ≤ powerFloor ρ x := Nat.le_floor (by linarith : (2 : ℝ) ≤ x ^ ρ)
  have hlogRpos : 0 < Real.log (powerFloor ρ x : ℝ) :=
    lt_of_lt_of_le (mul_pos (div_pos hρ (by norm_num)) hxlog) hxlogR
  have hlogzpos : 0 ≤ Real.log (x ^ α) := by rw [Real.log_rpow hx0 α]; positivity
  have hten : 10 * Real.log (x ^ α) ≤ Real.log (powerFloor ρ x : ℝ) := by
    have hs := mul_le_mul_of_nonneg_right hsmall hxlog.le
    rw [Real.log_rpow hx0 α]
    nlinarith
  have hsq : 20 * (Real.log (x ^ α)) ^ 2 ≤ (Real.log (powerFloor ρ x : ℝ)) ^ 2 / 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hten)
      (by linarith : 0 ≤ Real.log (powerFloor ρ x : ℝ) + 10 * Real.log (x ^ α))
    nlinarith [sq_nonneg (Real.log (x ^ α))]
  have hratio : Real.log (x ^ α) / Real.log (powerFloor ρ x : ℝ) ≤ 2 * α / ρ := by
    apply (div_le_div_iff₀ hlogRpos hρ).mpr
    have hs := mul_le_mul_of_nonneg_left hxlogR (by positivity : 0 ≤ 2 * α)
    rw [Real.log_rpow hx0 α]
    nlinarith
  have hratio0 : 0 ≤ Real.log (x ^ α) / Real.log (powerFloor ρ x : ℝ) :=
    div_nonneg hlogzpos hlogRpos.le
  have hratio2 : 0 ≤ 2 * α / ρ := by positivity
  have hsquare := mul_nonneg (sub_nonneg.mpr hratio) (add_nonneg hratio2 hratio0)
  refine ⟨hxz, hR2, hxlogz, hsq, ?_⟩
  have hnormalize : (2 * α / ρ) ^ 2 = 4 * (α / ρ) ^ 2 := by ring
  nlinarith [hnormalize]

theorem smallPairCount_growing_upper {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hsmall : 20 * α ≤ ρ) :
    ∀ᶠ N : ℕ in atTop, ∀ S i j : ℕ,
      smallPairCount ⌊(N : ℝ) ^ α⌋₊ S N i j ≤
        (1 + 160 * (α / ρ) ^ 2) * N * pairSurvivalProduct ((N : ℝ) ^ α) ((j : ℤ) - i) +
          (N : ℝ) ^ (8 * ρ) := by
  have hconditions := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_pair_cutoff_conditions hα hρ hsmall)
  filter_upwards [hconditions] with N hN
  intro S i j
  obtain ⟨hz, hR, hlarge, hsize, hcoef⟩ := hN
  have h := smallPairCount_sieve_bound ((N : ℝ) ^ α) hz (powerFloor ρ N) S N i j
    hR hlarge hsize
  have hV := pairSurvivalProduct_nonneg ((N : ℝ) ^ α) ((j : ℤ) - i)
  have hscaled := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Nat.cast_nonneg N) hV)
  have herror := powerFloor_power_le (Nat.cast_nonneg N) ρ 8
  have herror' : (powerFloor ρ N : ℝ) ^ 8 ≤ (N : ℝ) ^ (8 * ρ) := by
    simpa only [Nat.cast_ofNat, mul_comm] using herror
  nlinarith

theorem smallAverage_second_moment_reduction {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hsmall : 20 * α ≤ ρ) :
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ, 0 < H →
      (∑ n ∈ Finset.Ioc N (2 * N), (smallAverage ⌊(N : ℝ) ^ α⌋₊ H n) ^ 2) ≤
        (1 + 160 * (α / ρ) ^ 2) * N *
          ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
            pairSurvivalProduct ((N : ℝ) ^ α) ((j : ℤ) - i)) / (H : ℝ) ^ 2) +
          (N : ℝ) ^ (8 * ρ) := by
  filter_upwards [smallPairCount_growing_upper hα hρ hsmall] with N hN
  intro H hH
  rw [sum_dyadic_interval_eq_range]
  exact smallAverage_second_upper _ H (N + 1) N hH
    (fun i j => pairSurvivalProduct ((N : ℝ) ^ α) ((j : ℤ) - i))
    ((1 + 160 * (α / ρ) ^ 2) * N) ((N : ℝ) ^ (8 * ρ))
    (fun i hi j hj => hN (N + 1) i j)

end Erdos676
end

section
open Filter Asymptotics
open scoped Topology

namespace Erdos676

theorem eventually_log_pow_le_power (q : ℕ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ q ≤ c * x ^ r := by
  have h : (fun x : ℝ => (Real.log x) ^ q) =o[atTop] (fun x => x ^ r) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (q : ℝ) hr
  filter_upwards [h.bound hc, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog0 : 0 ≤ (Real.log x) ^ q := pow_nonneg (Real.log_pos hx1).le q
  have hpow0 : 0 ≤ x ^ r := (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx1) r).le
  simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hpow0] using hx

theorem eventually_power_error_absorbed_by_survival_pow (q : ℕ) {α β C η : ℝ}
    (hα : 0 < α) (hβ : β < 1) (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, C * x ^ β ≤ η * x * (survivalProduct (x ^ α)) ^ q := by
  obtain ⟨c, hc, hsurvival⟩ := exists_eventual_survival_lower
  have hlog := eventually_log_pow_le_power q (by linarith : 0 < 1 - β)
    (div_pos (mul_pos hη (pow_pos hc q)) (mul_pos hC (pow_pos hα q)))
  have hsurvival' := (tendsto_rpow_atTop hα).eventually hsurvival
  filter_upwards [hlog, hsurvival', eventually_gt_atTop (1 : ℝ)] with x hxlog hxV hx1
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hden0 : 0 < α * Real.log x := mul_pos hα (Real.log_pos hx1)
  have hden : 0 < (α * Real.log x) ^ q := pow_pos hden0 q
  rw [Real.log_rpow hx0 α] at hxV
  have hpower : x ^ β * x ^ (1 - β) = x := by
    rw [← Real.rpow_add hx0, show β + (1 - β) = 1 by ring, Real.rpow_one]
  have hcancel : (C * α ^ q) * (η * c ^ q / (C * α ^ q)) = η * c ^ q := by
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hxlog
    (by positivity : 0 ≤ C * α ^ q * x ^ β)
  have hrhs : (C * α ^ q * x ^ β) * (η * c ^ q / (C * α ^ q) * x ^ (1 - β)) =
      η * c ^ q * x := by
    calc
      _ = ((C * α ^ q) * (η * c ^ q / (C * α ^ q))) * (x ^ β * x ^ (1 - β)) := by ring
      _ = _ := by rw [hcancel, hpower]
  rw [hrhs] at hscaled
  have hfirst : C * x ^ β ≤ η * c ^ q * x / (α * Real.log x) ^ q := by
    apply (le_div_iff₀ hden).mpr
    rw [mul_pow]
    nlinarith [hscaled]
  have hVpow := pow_le_pow_left₀ (div_nonneg hc.le hden0.le) hxV q
  calc
    _ ≤ η * c ^ q * x / (α * Real.log x) ^ q := hfirst
    _ = (η * x) * (c / (α * Real.log x)) ^ q := by rw [div_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hVpow (mul_nonneg hη.le hx0.le)

end Erdos676
end

section
open Filter
open scoped Topology BigOperators

namespace Erdos676

theorem pairSurvival_average_factorization (z : ℝ) (H : ℕ) :
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
      pairSurvivalProduct z ((j : ℤ) - i)) / (H : ℝ) ^ 2 =
    (survivalProduct z) ^ 2 *
      ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        singularFactorProduct z ((j : ℤ) - i)) / (H : ℝ) ^ 2) := by
  simp_rw [pairSurvivalProduct_factorization, ← Finset.mul_sum]
  ring

theorem second_moment_bound_of_singular_mean {α ρ K ε : ℝ}
    (hα : 0 < α) (hρ : 0 < ρ) (hsmall : 20 * α ≤ ρ)
    (hρ8 : 8 * ρ < 1) (hε : 0 < ε) (H : ℕ → ℕ)
    (hH : ∀ᶠ N : ℕ in atTop, 0 < H N)
    (hmean : ∀ᶠ N : ℕ in atTop,
      (∑ i ∈ Finset.range (H N), ∑ j ∈ Finset.range (H N),
        singularFactorProduct ((N : ℝ) ^ α) ((j : ℤ) - i)) / (H N : ℝ) ^ 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ioc N (2 * N), (smallAverage ⌊(N : ℝ) ^ α⌋₊ (H N) n) ^ 2) ≤
        ((1 + 160 * (α / ρ) ^ 2) * K + ε) * N *
          (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
  have herr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_power_error_absorbed_by_survival_pow 2 hα hρ8 zero_lt_one hε)
  filter_upwards [smallAverage_second_moment_reduction hα hρ hsmall, hH, hmean, herr]
    with N hred hHN hMN hEN
  have hc : 0 ≤ (1 + 160 * (α / ρ) ^ 2) * (N : ℝ) *
      (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hMN hc
  have h := hred (H N) hHN
  rw [pairSurvival_average_factorization] at h
  have hEN' : (N : ℝ) ^ (8 * ρ) ≤ ε * N * (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
    simpa only [one_mul] using hEN
  nlinarith

end Erdos676
end

section
open Filter
open scoped Topology BigOperators

namespace Erdos676

theorem original_second_moment {α ρ ε : ℝ} (hα : 0 < α) (hsmall : α < 1 / 2)
    (hρ : 0 < ρ) (hcut : 20 * α ≤ ρ) (hρ8 : 8 * ρ < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ioc N (2 * N),
        (smallAverage ⌊(N : ℝ) ^ α⌋₊ (powerFloor (α * (1 - α ^ 2)) N) n) ^ 2) ≤
      ((1 + 160 * (α / ρ) ^ 2) * (1 / (1 - α ^ 2) ^ 2 + ε) + ε) * N *
        (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
  have hb : 0 < 1 - α ^ 2 := by nlinarith
  have hη : 0 < α * (1 - α ^ 2) := mul_pos hα hb
  have hH : ∀ᶠ N : ℕ in atTop, 0 < powerFloor (α * (1 - α ^ 2)) N :=
    ((powerFloor_tendsto hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 0
  have hmean := original_singular_average hα hsmall hε
  apply second_moment_bound_of_singular_mean hα hρ hcut hρ8 hε
    (fun N => powerFloor (α * (1 - α ^ 2)) N) hH
  simpa only [pairMean] using hmean

theorem original_second_moment_quadratic {α ε : ℝ} (hα : 0 < α)
    (hsmall : α ≤ 1 / 200) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ioc N (2 * N),
        (smallAverage ⌊(N : ℝ) ^ α⌋₊ (powerFloor (α * (1 - α ^ 2)) N) n) ^ 2) ≤
      (1 + 40000 * α ^ 2 + ε) * N * (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by
  let A := 1 + 160 * (α / (1 / 10 : ℝ)) ^ 2
  let δ := ε / (A + 1)
  have hA : 0 < A + 1 := by dsimp [A]; positivity
  have hδ : 0 < δ := div_pos hε hA
  have hhalf : α < 1 / 2 := by linarith
  have h := original_second_moment hα hhalf (by norm_num : (0 : ℝ) < 1 / 10)
    (by linarith : 20 * α ≤ (1 / 10 : ℝ)) (by norm_num : 8 * (1 / 10 : ℝ) < 1) hδ
  have hb : 0 < 1 - α ^ 2 := by nlinarith
  have hu : 0 ≤ α ^ 2 := sq_nonneg α
  have huupper : α ^ 2 ≤ 1 / 4 := by nlinarith
  have hu2 : (α ^ 2) ^ 2 ≤ (α ^ 2) / 4 := by nlinarith
  have hrecip : 1 / (1 - α ^ 2) ^ 2 ≤ 1 + 4 * α ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    have hu3 : 0 ≤ (α ^ 2) ^ 3 := pow_nonneg hu 3
    nlinarith
  have hAeq : A = 1 + 16000 * α ^ 2 := by dsimp [A]; ring
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hrecipA := mul_le_mul_of_nonneg_left hrecip hA0
  have hcoef : A * (1 / (1 - α ^ 2) ^ 2) ≤ 1 + 40000 * α ^ 2 := by
    rw [hAeq] at hrecipA
    nlinarith
  have hδeq : A * δ + δ = ε := by dsimp [δ]; field_simp
  filter_upwards [h] with N hN
  have hweight : 0 ≤ (N : ℝ) * (survivalProduct ((N : ℝ) ^ α)) ^ 2 := by positivity
  have hcoef' : A * (1 / (1 - α ^ 2) ^ 2 + δ) + δ ≤ 1 + 40000 * α ^ 2 + ε := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hcoef' hweight
  dsimp only [A] at hscaled
  nlinarith

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676


structure SieveData (X : ℕ) where
  cutoff : ℕ
  window : ℕ
  centers : Finset ℕ
  window_pos : 0 < window
  centers_subset : centers ⊆ Finset.Ioc X (2 * X)
  first_pos : 0 < ∑ n ∈ Finset.Ioc X (2 * X), smallAverage cutoff window n
  moment_gap :
    (((Finset.Ioc X (2 * X)) \ centers).card : ℝ) *
        (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage cutoff window n) ^ 2) <
      (∑ n ∈ Finset.Ioc X (2 * X), smallAverage cutoff window n) ^ 2
  large_avoidance :
    ∀ n ∈ centers, ∀ j < window, LargeAvoidance cutoff (n + j)
  shifts_stay_in_interval :
    ∀ n ∈ centers, ∀ j < window, X < n + j ∧ n + j ≤ 2 * X


theorem SieveData.exception_exists {X : ℕ} (D : SieveData X) :
    (dyadicExceptions X).Nonempty := by
  have hpositive : 0 < ∑ n ∈ D.centers, smallAverage D.cutoff D.window n :=
    positive_restricted_mass_of_moment_gap (Finset.Ioc X (2 * X)) D.centers
      (smallAverage D.cutoff D.window) D.centers_subset
      (fun n _ => smallAverage_nonneg _ _ n) D.first_pos D.moment_gap
  have hcard := smallAverage_mass_le_exceptions D.centers (dyadicExceptions X)
    D.cutoff D.window D.window_pos D.large_avoidance (by
      intro n hn j hj he
      exact (mem_dyadicExceptions X (n + j)).mpr
        ⟨(D.shifts_stay_in_interval n hn j hj).1,
          (D.shifts_stay_in_interval n hn j hj).2, he⟩)
  have : 0 < (dyadicExceptions X).card := by
    exact_mod_cast (lt_of_lt_of_le hpositive hcard)
  exact Finset.card_pos.mp this


theorem disproof_of_eventual_sieve_data
    (h : ∀ᶠ X : ℕ in Filter.atTop, Nonempty (SieveData X)) :
    ¬ EventualRepresentation := by
  apply not_eventual_iff_unbounded.mpr
  apply unbounded_of_eventually_dyadic_nonempty
  filter_upwards [h] with X hX
  obtain ⟨D⟩ := hX
  exact D.exception_exists

end Erdos676
end

section
namespace Erdos676


def QuantitativeDisproof : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
    c * X / Real.log X ≤ (dyadicExceptions X).card

theorem quantitativeDisproof_implies_disproof (h : QuantitativeDisproof) :
    ¬ EventualRepresentation := by
  obtain ⟨c, hc, hcount⟩ := h
  apply not_eventual_iff_unbounded.mpr
  apply unbounded_of_eventually_dyadic_nonempty
  filter_upwards [hcount, Filter.eventually_ge_atTop 2] with X hX hX2
  have hXreal : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hpositive : 0 < c * X / Real.log X :=
    div_pos (mul_pos hc (lt_trans zero_lt_one hXreal)) (Real.log_pos hXreal)
  have hcard : 0 < (dyadicExceptions X).card := by
    exact_mod_cast lt_of_lt_of_le hpositive hX
  exact Finset.card_pos.mp hcard

end Erdos676
end

section
open scoped BigOperators

namespace Erdos676

theorem quantitative_restricted_mass {ι : Type*} [DecidableEq ι]
    (I U : Finset ι) (f : ι → ℝ) (hUI : U ⊆ I) {N V d e : ℝ}
    (hN : 0 ≤ N) (hV : 0 ≤ V) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (he : 0 ≤ e) (heSmall : e ≤ d / 8)
    (hfirst : (1 - e) * N * V ≤ ∑ x ∈ I, f x)
    (hsecond : (∑ x ∈ I, (f x) ^ 2) ≤ (1 + e) * N * V ^ 2)
    (hcomplement : ((I \ U).card : ℝ) ≤ (1 - d) * N) :
    (d / 8) * N * V ≤ ∑ x ∈ U, f x := by
  have hsplit := Finset.sum_sdiff (f := f) hUI
  have hcs := sq_sum_le_card_mul_sum_sq (s := I \ U) (f := f)
  have hsquares : (∑ x ∈ I \ U, (f x) ^ 2) ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ => sq_nonneg (f x))
  have hQ0 : 0 ≤ ∑ x ∈ I, (f x) ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg (f x)
  have hupper := hcs.trans (mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg _))
  have hproduct := mul_le_mul hcomplement hsecond hQ0
    (mul_nonneg (sub_nonneg.mpr hd1) hN)
  have hcoef : (1 - d) * (1 + e) ≤ (1 - d / 4) ^ 2 := by
    nlinarith [mul_nonneg hd he, sq_nonneg d]
  have hscaled := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg N) (sq_nonneg V))
  have hcap0 : 0 ≤ (1 - d / 4) * N * V := by
    apply mul_nonneg _ hV
    apply mul_nonneg _ hN
    linarith
  have hcap : (∑ x ∈ I \ U, f x) ≤ (1 - d / 4) * N * V := by
    nlinarith
  have hsmall := mul_le_mul_of_nonneg_right heSmall (mul_nonneg hN hV)
  nlinarith


theorem quantitative_dyadic_count (X z H : ℕ) (U : Finset ℕ)
    (hH : 0 < H) (hU : U ⊆ Finset.Ioc X (2 * X)) {V d e : ℝ}
    (hV : 0 ≤ V) (hd : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (heSmall : e ≤ d / 8)
    (hfirst : (1 - e) * X * V ≤
      ∑ n ∈ Finset.Ioc X (2 * X), smallAverage z H n)
    (hsecond : (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage z H n) ^ 2) ≤
      (1 + e) * X * V ^ 2)
    (hcomplement : (((Finset.Ioc X (2 * X)) \ U).card : ℝ) ≤ (1 - d) * X)
    (hlarge : ∀ n ∈ U, ∀ j < H, LargeAvoidance z (n + j))
    (hshift : ∀ n ∈ U, ∀ j < H, X < n + j ∧ n + j ≤ 2 * X) :
    (d / 8) * X * V ≤ (dyadicExceptions X).card := by
  have hmass := quantitative_restricted_mass (Finset.Ioc X (2 * X)) U
    (smallAverage z H) hU
    (Nat.cast_nonneg X) hV hd hd1 he heSmall hfirst hsecond hcomplement
  have hcount := smallAverage_mass_le_exceptions U (dyadicExceptions X) z H hH hlarge (by
    intro n hn j hj hexc
    exact (mem_dyadicExceptions X (n + j)).mpr
      ⟨(hshift n hn j hj).1, (hshift n hn j hj).2, hexc⟩)
  exact hmass.trans hcount

end Erdos676
end

section
open Filter
open scoped BigOperators Topology

namespace Erdos676

theorem eventual_exception_survival_lower :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * X * survivalProduct ((X : ℝ) ^ α) ≤ (dyadicExceptions X).card := by
  obtain ⟨d, hd, hd1, hcenters⟩ := stable_natural_centers
  obtain ⟨C, hC0, hC⟩ := exists_half_power_prime_mass_bound
  obtain ⟨L, hL, hsmall, hdegree, hmargin⟩ := final_parameter_choice hd C
  let α := discreteCutoff L
  let j := L - 2
  let γ := d * dyadicRetention ^ L
  let η := α * (1 - α ^ 2)
  have hα : 0 < α := discreteCutoff_pos L
  have hαsmall : α ≤ 1 / 200 := hsmall
  have hret0 : 0 < dyadicRetention := by linarith [dyadicRetention_bounds.1]
  have hγ : 0 < γ := mul_pos hd (pow_pos hret0 L)
  have hγ1 : γ ≤ 1 := by
    have hpow := pow_le_one₀ hret0.le dyadicRetention_bounds.2.le (n := L)
    dsimp [γ]
    nlinarith
  have hη : 0 < η := mul_pos hα (by dsimp [α] at hαsmall ⊢; nlinarith [sq_nonneg (discreteCutoff L)])
  have hηα : η < α := by
    dsimp [η]
    nlinarith [sq_pos_of_pos hα]
  have hlevel : highPrimeLevel j = α := by
    rw [highPrimeLevel_discrete]
    have hj : j + 2 = L := by dsimp [j]; omega
    rw [hj]
  have hηlevel : η < highPrimeLevel j := by rwa [hlevel]
  have hpow : dyadicRetention ^ L ≤ dyadicRetention ^ j :=
    pow_le_pow_of_le_one hret0.le dyadicRetention_bounds.2.le (by dsimp [j]; omega)
  have hfirstloss : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) < γ / 16 := by
    rw [truncation_loss_discrete]
    dsimp only [γ, α] at *
    have hs : 0 ≤ 40000 * (discreteCutoff L) ^ 2 := by positivity
    nlinarith
  have hsecondloss : 40000 * α ^ 2 < γ / 16 := by
    have hs : 0 ≤ (2 * Real.exp (4 * C)) * α ^ 2 := by positivity
    change 16 * (2 * Real.exp (4 * C) + 40000) * α ^ 2 < γ at hmargin
    nlinarith
  have hfirstsmall : 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) ≤ 1 := by linarith
  have hfirst := smallAverage_first_moment L hα (by omega) (show 0 < γ / 16 by positivity)
    hdegree hC hfirstsmall
  have hsecond := original_second_moment_quadratic hα hαsmall (show 0 < γ / 16 by positivity)
  have hH : ∀ᶠ X : ℕ in atTop, 0 < powerFloor η X :=
    ((powerFloor_tendsto hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 0
  refine ⟨α, γ / 8, hα, by positivity, ?_⟩
  filter_upwards [hcenters j η hηlevel, hfirst, hsecond, hH] with X hU hfirstX hsecondX hHX
  let U := stableNaturalCenters X j η
  let H := powerFloor η X
  let V := survivalProduct ((X : ℝ) ^ α)
  have hV : 0 ≤ V := (survivalProduct_pos _).le
  have hUsub : U ⊆ Finset.Ioc X (2 * X) := stableNaturalCenters_subset X j η
  have hsize : γ * X ≤ (U.card : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hpow hd.le
    have hscaledX := mul_le_mul_of_nonneg_right hscaled (Nat.cast_nonneg X)
    exact hscaledX.trans hU
  have hcomp : (((Finset.Ioc X (2 * X)) \ U).card : ℝ) ≤ (1 - γ) * X := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hUsub
    have hI : (Finset.Ioc X (2 * X)).card = X := by rw [Nat.card_Ioc]; omega
    rw [hI] at hsplit
    have hsplitR : (((Finset.Ioc X (2 * X)) \ U).card : ℝ) + U.card = X := by exact_mod_cast hsplit
    nlinarith
  have hfirstBound : (1 - γ / 8) * X * V ≤
      ∑ n ∈ Finset.Ioc X (2 * X), smallAverage ⌊(X : ℝ) ^ α⌋₊ H n := by
    have hcoef : 1 - γ / 8 ≤ 1 - 2 * Real.exp (4 * C) / (2 : ℝ) ^ (2 * L) - γ / 16 := by linarith
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg X)) hV).trans
      (hfirstX H hHX)
  have hsecondBound : (∑ n ∈ Finset.Ioc X (2 * X), (smallAverage ⌊(X : ℝ) ^ α⌋₊ H n) ^ 2) ≤
      (1 + γ / 8) * X * V ^ 2 := by
    have hcoef : 1 + 40000 * α ^ 2 + γ / 16 ≤ 1 + γ / 8 := by linarith
    exact hsecondX.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg X)) (sq_nonneg V))
  apply quantitative_dyadic_count X ⌊(X : ℝ) ^ α⌋₊ H U hHX hUsub hV hγ.le hγ1
    (show 0 ≤ γ / 8 by positivity) le_rfl hfirstBound hsecondBound hcomp
  · intro n hn k hk
    have h := stableNaturalCenters_large_avoidance hn hk
    rwa [hlevel] at h
  · exact fun n hn k hk => stableNaturalCenters_shifts hn hk

theorem full_quantitative_disproof : QuantitativeDisproof := by
  obtain ⟨α, c, hα, hc, hcount⟩ := eventual_exception_survival_lower
  obtain ⟨v, hv, hsurvival⟩ := exists_eventual_survival_lower
  refine ⟨c * v / α, by positivity, ?_⟩
  have hsurvival' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((tendsto_rpow_atTop hα).eventually hsurvival)
  filter_upwards [hcount, hsurvival', eventually_ge_atTop (2 : ℕ)] with X hX hV hx
  have hx1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  rw [Real.log_rpow (zero_lt_one.trans hx1) α] at hV
  have hscaled := mul_le_mul_of_nonneg_left hV (show 0 ≤ c * (X : ℝ) by positivity)
  have heq : c * X * (v / (α * Real.log X)) = (c * v / α) * X / Real.log X := by ring
  rw [heq] at hscaled
  exact hscaled.trans hX

theorem full_disproof : ¬ EventualRepresentation :=
  quantitativeDisproof_implies_disproof full_quantitative_disproof

theorem full_unbounded_exceptions : UnboundedExceptions :=
  not_eventual_iff_unbounded.mp full_disproof

end Erdos676
end

section
open Filter

namespace Erdos676

theorem erdos676_negative :
    ¬ (∀ᶠ n : ℕ in atTop, ∃ a p b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b) :=
  full_disproof

theorem erdos676_infinite_exceptions :
    Set.Infinite {n : ℕ | ¬ ∃ a p b : ℕ,
      p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b} :=
  unbounded_iff_infinite.mp full_unbounded_exceptions

end Erdos676
end

theorem OMA.disproof : ¬ (type_of% @Erdos676.erdos_676) :=
  Erdos676.erdos676_negative
