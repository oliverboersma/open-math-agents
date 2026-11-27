import FormalConjectures.Arxiv.«2104.00502».BarkerSequence

/-
The odd-length result is due to Schmidt–Willms; it and the even-length
matrix construction are adapted from JD Jones, JD-Jones-ASES/ob-lean at
7826a8c0249678cfcb4c606e88d9fb978b316989 (MIT). Indexed correlations,
the even-length bridge, and the circulant Hadamard order reduction and
exclusion also use OpenAI, openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a
and 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
Copyright OpenAI for the openai/math material.
Modified: dependency modules inlined, with list-to-indexed bridges and
parity cases combined; ported from Sunstead to the Left to Solve statement and toolchain.

MIT License

Copyright (c) 2026 JD Jones

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

Original ob-lean NOTICE (paths refer to its upstream repository):

ob-lean is licensed under the MIT License (see LICENSE).

Portions derive from openai/math (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, 2026-10-06), Copyright OpenAI (the upstream repository
names no other holder), licensed under the Apache License, Version 2.0. A copy of that license is in
LICENSES/Apache-2.0.txt; it is also available at http://www.apache.org/licenses/LICENSE-2.0. The
upstream repository carries no NOTICE file.

What is derived:

1. The definitions IsSign, aperiodic and IsBarker in Challenge.lean and OB/Defs.lean are restated
   character for character, with the namespace changed, from the upstream file
   lean/ComparatorChallenges/EvenBarker.lean; the definitions RealMatrix, IsCirculant,
   IsSignHadamard and ExistsRealCirculantHadamard in the same two files are restated character for
   character, with the namespace changed, from lean/ComparatorChallenges/CirculantHadamard.lean.
2. scripts/EvenBarker-oai.txt and scripts/CirculantHadamard-oai.txt are copies of those two upstream
   files; they are reference data for scripts/check_definitions.py and are not built.
3. The definition `periodic` and the lemmas of OB/Hadamard.lean whose docstrings say “adapts ... of
   openai/math ...” are modified from the upstream tree lean/OAI/LinearAlgebra/Barker/ (the files
   named in each docstring). Those docstrings are the modification notices.

No other part of openai/math is included. Unless required by applicable law or agreed to in writing,
the derived portions are distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
KIND, either express or implied, as the Apache License states.

scripts/core_notation_audit.lean is a copy of scripts/core_notation_audit.lean of
https://github.com/PalomarRegistry/PalomarSubmission, Copyright (c) 2026 Kim Morrison, MIT License (the
permission notice is in LICENSES/PalomarSubmission-MIT.txt); the only change is a three-line provenance
comment at its head. It is used locally to check the statement surface and is not built.

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

open Arxiv.«2104.00502»

namespace OddBarker

universe u

/-- `x` is `1` or `-1`. -/
def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

open scoped BigOperators

/-- The aperiodic autocorrelation of `h` at shift `k`: `∑_{j < n - k} h j * h (j + k)`. -/
def aperiodic {n : ℕ} (h : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ j : Fin (n - k), h ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n k)⟩ *
    h ⟨j.val + k, Nat.add_lt_of_lt_sub j.isLt⟩

/-- Every entry is a sign and every nontrivial aperiodic autocorrelation has absolute value at
most one. -/
def IsBarker {n : ℕ} (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧ ∀ k : ℕ, 0 < k → k < n → |aperiodic h k| ≤ 1


end OddBarker

open Finset

namespace OddBarker

/-- The sequence read on `ℕ`, zero outside `[0, n)`. -/
def seq {n : ℕ} (h : Fin n → ℤ) (i : ℕ) : ℤ := if hi : i < n then h ⟨i, hi⟩ else 0

theorem seq_eq {n : ℕ} (h : Fin n → ℤ) {i : ℕ} (hi : i < n) : seq h i = h ⟨i, hi⟩ := by
  simp [seq, hi]

theorem seq_of_le {n : ℕ} (h : Fin n → ℤ) {i : ℕ} (hi : n ≤ i) : seq h i = 0 := by
  simp [seq, not_lt.mpr hi]

theorem aperiodic_eq_sum {n : ℕ} (h : Fin n → ℤ) (k : ℕ) :
    aperiodic h k = ∑ j ∈ range (n - k), seq h j * seq h (j + k) := by
  unfold aperiodic
  rw [← Fin.sum_univ_eq_sum_range (fun j => seq h j * seq h (j + k)) (n - k)]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : j.val < n := by omega
  have h2 : j.val + k < n := by omega
  simp [seq, h1, h2]

/-- A product of signs is `1 - ((card - sum) % 4)`, and `card - sum` is even. -/
theorem prod_signs (s : Finset ℕ) (x : ℕ → ℤ) (hx : ∀ i ∈ s, x i = 1 ∨ x i = -1) :
    ∏ i ∈ s, x i = 1 - (((s.card : ℤ) - ∑ i ∈ s, x i) % 4) ∧
      ((s.card : ℤ) - ∑ i ∈ s, x i) % 2 = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih1]
    rcases hx a (Finset.mem_insert_self a s) with h | h <;> rw [h] <;> push_cast <;> omega

theorem seq_sign {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {i : ℕ} (hi : i < n) :
    seq h i = 1 ∨ seq h i = -1 := by
  simpa [seq, hi, IsSign] using hs ⟨i, hi⟩

theorem seq_mul_self {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {i : ℕ} (hi : i < n) :
    seq h i * seq h i = 1 := by
  rcases seq_sign hs hi with h1 | h1 <;> rw [h1] <;> norm_num

/-- `2 ∣ C(k) - (n - k)` for a sign sequence (each term is `±1`). -/
theorem aperiodic_parity {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {k : ℕ} (hk : k ≤ n) :
    (2 : ℤ) ∣ aperiodic h k - ((n - k : ℕ) : ℤ) := by
  have hdvd : (2 : ℤ) ∣ ∑ j ∈ range (n - k), (seq h j * seq h (j + k) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j < n := by simp at hj; omega
    have hj2 : j + k < n := by simp at hj; omega
    rcases seq_sign hs hj1 with h1 | h1 <;> rcases seq_sign hs hj2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [Finset.sum_sub_distrib, ← aperiodic_eq_sum] at hdvd
  simpa using hdvd

theorem odd_shift_zero {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (k : ℕ)
    (hk : Odd k) (hk0 : 0 < k) (hkn : k < n) : aperiodic h k = 0 := by
  have hdvd : (2 : ℤ) ∣ ∑ j ∈ range (n - k), (seq h j * seq h (j + k) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j < n := by simp at hj; omega
    have hj2 : j + k < n := by simp at hj; omega
    rcases seq_sign hb.1 hj1 with h1 | h1 <;> rcases seq_sign hb.1 hj2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [Finset.sum_sub_distrib, ← aperiodic_eq_sum] at hdvd
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hdvd
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ := hdvd
  have hc : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by push_cast [hkn.le]; ring
  rw [hc] at hd
  subst hu hv
  push_cast at hd
  omega

end OddBarker

open Finset

namespace OddBarker

/-- The folded sum `∑_{k ≤ w} (-1)^k a k a (w - k)`. -/
def T0 (a : ℕ → ℤ) (w : ℕ) : ℤ :=
  ∑ k ∈ range (w + 1), (-1) ^ k * a k * a (w - k)

theorem neg_one_pow_sub {N k : ℕ} (hk : k ≤ N) :
    (-1 : ℤ) ^ (N - k) = (-1) ^ N * (-1) ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add]
  have h : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨k, by ring⟩
  linear_combination (-(-1 : ℤ) ^ d) * h

/-- At odd arguments the folded sum vanishes identically. -/
theorem T0_odd (a : ℕ → ℤ) {w : ℕ} (hw : Even w) : T0 a (w + 1) = 0 := by
  unfold T0
  have h := Finset.sum_range_reflect (fun k => (-1 : ℤ) ^ k * a k * a (w + 1 - k)) (w + 2)
  have hneg : ∑ j ∈ range (w + 2), (fun k => (-1 : ℤ) ^ k * a k * a (w + 1 - k)) (w + 2 - 1 - j)
      = -∑ j ∈ range (w + 2), (-1 : ℤ) ^ j * a j * a (w + 1 - j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ w + 1 := by simp at hj; omega
    have e1 : w + 2 - 1 - j = w + 1 - j := by omega
    have e2 : w + 1 - (w + 1 - j) = j := by omega
    simp only [e1, e2]
    rw [neg_one_pow_sub hj', pow_succ, hw.neg_one_pow]
    ring
  linarith [h, hneg]

/-- The step identity. -/
theorem T0_step (a : ℕ → ℤ) {w : ℕ} (hw : Even w) :
    T0 a (w + 2) - T0 a w = 2 * a 0 * (a (w + 2) - a (w + 1)) -
      ∑ t ∈ range (w + 1), (-1) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t)) := by
  set S1 := ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * a (t + 1) * a (w - t + 1) with hS1
  set S2 := ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * a (t + 1) * a (w - t) with hS2
  set S3 := ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * a t * a (w - t + 1) with hS3
  have hsplit : ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t))
      = S1 - S2 - S3 + T0 a w := by
    unfold T0
    rw [hS1, hS2, hS3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have h1 : T0 a (w + 2) = -S1 + 2 * a 0 * a (w + 2) := by
    unfold T0
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hS1, ← Finset.sum_neg_distrib]
    have hmid : ∑ i ∈ range (w + 1), (-1 : ℤ) ^ (i + 1) * a (i + 1) * a (w + 2 - (i + 1))
        = ∑ i ∈ range (w + 1), -((-1 : ℤ) ^ i * a (i + 1) * a (w - i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ w := by simp at hi; omega
      have e : w + 2 - (i + 1) = w - i + 1 := by omega
      rw [e, pow_succ]
      ring
    rw [hmid]
    have e2 : w + 2 - (w + 1 + 1) = 0 := by omega
    rw [e2, Nat.sub_zero, pow_succ, pow_succ, hw.neg_one_pow]
    ring
  have h2 : S2 = a 0 * a (w + 1) := by
    have h := T0_odd a hw
    unfold T0 at h
    rw [Finset.sum_range_succ'] at h
    have hmid : ∑ i ∈ range (w + 1), (-1 : ℤ) ^ (i + 1) * a (i + 1) * a (w + 1 - (i + 1))
        = -S2 := by
      rw [hS2, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have e : w + 1 - (i + 1) = w - i := by omega
      rw [e, pow_succ]
      ring
    rw [hmid] at h
    simp at h
    linarith
  have h3 : S3 = S2 := by
    rw [hS3, hS2, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ w := by simp at hj; omega
    have e1 : w + 1 - 1 - j = w - j := by omega
    have e2 : w - (w - j) + 1 = j + 1 := by omega
    rw [e1, e2, neg_one_pow_sub hj', hw.neg_one_pow]
    ring
  rw [hsplit, h1, h3, h2]
  ring

end OddBarker

open Finset

namespace OddBarker

theorem key_bound (a : ℕ → ℤ) (p q : ℕ)
    (hs : ∀ i, i ≤ p + q → a i = 1 ∨ a i = -1)
    (hp2 : 2 ≤ p) (hpq : p < q)
    (hpb : a p ≠ a (p - 1)) (hpmin : ∀ s, 1 ≤ s → s < p → a s = a (s - 1))
    (hqb : a q ≠ a (q - 1)) (hndvd : ¬ p ∣ q)
    (hqmin : ∀ s, 1 ≤ s → s < q → a s ≠ a (s - 1) → p ∣ s)
    (hpodd : Odd p) (hqodd : Odd q)
    (hT0 : T0 a (p + q - 2) = 1) (hT2 : T0 a (p + q) = 1) : False := by
  have hw : Even (p + q - 2) := by
    obtain ⟨u, hu⟩ := hpodd
    obtain ⟨v, hv⟩ := hqodd
    exact ⟨u + v, by omega⟩
  have hstep := T0_step a hw
  have e : p + q - 2 + 2 = p + q := by omega
  rw [e, hT0, hT2] at hstep
  set w := p + q - 2 with hwdef
  set f : ℕ → ℤ := fun t => (-1) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t)) with hf
  have hzero : ∀ t ∈ range (w + 1), t ≠ p - 1 → t ≠ q - 1 → f t = 0 := by
    intro t ht h1 h2
    simp only [Finset.mem_range] at ht
    by_cases hA : a (t + 1) = a t
    · simp [hf, hA]
    by_cases hB : a (w - t + 1) = a (w - t)
    · simp [hf, hB]
    exfalso
    have hs1 : p ≤ t + 1 := by
      by_contra hlt
      exact hA (by simpa using hpmin (t + 1) (by omega) (by omega))
    have hs2 : p ≤ w - t + 1 := by
      by_contra hlt
      have := hpmin (w - t + 1) (by omega) (by omega)
      exact hB (by simpa using this)
    have hq1 : t + 1 < q := by omega
    have hq2 : w - t + 1 < q := by omega
    have d1 := hqmin (t + 1) (by omega) hq1 (by simpa using hA)
    have d2 := hqmin (w - t + 1) (by omega) hq2 (by simpa using hB)
    have hdv : p ∣ (t + 1) + (w - t + 1) := Nat.dvd_add d1 d2
    have e3 : (t + 1) + (w - t + 1) = p + q := by omega
    rw [e3] at hdv
    exact hndvd ((Nat.dvd_add_right (dvd_refl p)).mp hdv)
  have hmemp : p - 1 ∈ range (w + 1) := by simp; omega
  have hmemq : q - 1 ∈ range (w + 1) := by simp; omega
  have hne : p - 1 ≠ q - 1 := by omega
  have hsum : ∑ t ∈ range (w + 1), f t = f (p - 1) + f (q - 1) :=
    Finset.sum_eq_add_of_mem (p - 1) (q - 1) hmemp hmemq hne
      (fun c hc hcc => hzero c hc hcc.1 hcc.2)
  have hp1 : Even (p - 1) := by
    obtain ⟨u, hu⟩ := hpodd
    exact ⟨u, by omega⟩
  have hq1 : Even (q - 1) := by
    obtain ⟨u, hu⟩ := hqodd
    exact ⟨u, by omega⟩
  have ep1 : p - 1 + 1 = p := by omega
  have eq1 : q - 1 + 1 = q := by omega
  have ew1 : w - (p - 1) = q - 1 := by omega
  have ew2 : w - (q - 1) = p - 1 := by omega
  have hfp : f (p - 1) = (a p - a (p - 1)) * (a q - a (q - 1)) := by
    simp only [hf, ep1, ew1, eq1, hp1.neg_one_pow, one_mul]
  have hfq : f (q - 1) = (a q - a (q - 1)) * (a p - a (p - 1)) := by
    simp only [hf, ep1, ew2, eq1, hq1.neg_one_pow, one_mul]
  have hsum' : ∑ t ∈ range (w + 1), (-1 : ℤ) ^ t * (a (t + 1) - a t) * (a (w - t + 1) - a (w - t))
      = (a p - a (p - 1)) * (a q - a (q - 1)) + (a q - a (q - 1)) * (a p - a (p - 1)) := by
    rw [← hfp, ← hfq, ← hsum]
  rw [hsum'] at hstep
  have ew1' : w + 1 = p + q - 1 := by omega
  have ew2' : w + 2 = p + q := by omega
  rw [ew1'] at hstep
  have hap := hs p (by omega)
  have hap1 := hs (p - 1) (by omega)
  have haq := hs q (by omega)
  have haq1 := hs (q - 1) (by omega)
  have ha0 := hs 0 (by omega)
  have haw1 := hs (p + q - 1) (by omega)
  have haw2 := hs (p + q) (by omega)
  rcases hap with h1 | h1 <;> rcases hap1 with h2 | h2 <;> rcases haq with h3 | h3 <;>
    rcases haq1 with h4 | h4 <;> rcases ha0 with h5 | h5 <;> rcases haw1 with h6 | h6 <;>
    rcases haw2 with h7 | h7 <;> simp only [h1, h2, h3, h4, h5, h6, h7, ne_eq, not_true_eq_false] at hstep hpb hqb <;>
    (try norm_num at hstep)

end OddBarker

open Finset

namespace OddBarker

/-- Split a range sum at `a`, with the tail indexed as `i + a`. -/
theorem pa_split (f : ℕ → ℤ) (a b : ℕ) :
    ∑ j ∈ range (a + b), f j = ∑ j ∈ range a, f j + ∑ i ∈ range b, f (i + a) := by
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm]

/-- `C(u) + C(n - u) ≡ n (mod 4)` for a sign sequence and `0 < u < n`. -/
theorem aperiodic_add_aperiodic_sub_mod_four {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j))
    {u : ℕ} (hu0 : 0 < u) (hun : u < n) :
    (4 : ℤ) ∣ aperiodic h u + aperiodic h (n - u) - n := by
  obtain ⟨v, hv⟩ : ∃ v, v = n - u := ⟨_, rfl⟩
  have hvu : n - v = u := by omega
  rw [← hv, aperiodic_eq_sum h u, aperiodic_eq_sum h v, ← hv, hvu]
  have h1 : (4 : ℤ) ∣ ∑ j ∈ range v,
      (seq h j * seq h (j + u) - seq h j + seq h (j + u) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_range] at hj
    rcases seq_sign hs (show j < n by omega) with e1 | e1 <;>
      rcases seq_sign hs (show j + u < n by omega) with e2 | e2 <;>
      rw [e1, e2] <;> norm_num
  have h2 : (4 : ℤ) ∣ ∑ i ∈ range u,
      (seq h i * seq h (i + v) - seq h (i + v) + seq h i - 1) := by
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rcases seq_sign hs (show i < n by omega) with e1 | e1 <;>
      rcases seq_sign hs (show i + v < n by omega) with e2 | e2 <;>
      rw [e1, e2] <;> norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h1 h2
  have e1 := pa_split (seq h) v u
  have e2 := pa_split (seq h) u v
  rw [show v + u = n by omega] at e1
  rw [show u + v = n by omega] at e2
  omega

/-- For odd `n` and a Barker sequence, every even nontrivial shift has autocorrelation
`(-1)^((n-1)/2)`. -/
theorem even_shift_eq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = (-1) ^ ((n - 1) / 2) := by
  have hv : Odd (n - k) := by
    obtain ⟨a, ha⟩ := hn
    obtain ⟨b, hb2⟩ := hk
    exact ⟨a - b, by omega⟩
  have hz := odd_shift_zero hb hn (n - k) hv (by omega) (by omega)
  have hd := aperiodic_add_aperiodic_sub_mod_four hb.1 hk0 hkn
  rw [hz] at hd
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨m, hm⟩ := hn
  have hm2 : (n - 1) / 2 = m := by omega
  rw [hm2]
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow]
    obtain ⟨t, ht⟩ := he
    omega
  · rw [ho.neg_one_pow]
    obtain ⟨t, ht⟩ := ho
    omega

/-- The Challenge's `aperiodic_eq`. -/
theorem aperiodic_eq_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0 := by
  split_ifs with he
  · exact even_shift_eq hb hn he hk0 hkn
  · exact odd_shift_zero hb hn k (Nat.not_even_iff_odd.mp he) hk0 hkn

/-- For even `n` and a Barker sequence, every even nontrivial shift has autocorrelation `0`
(parity: `C(k) ≡ n - k ≡ 0 (mod 2)` and `|C(k)| ≤ 1`). -/
theorem even_shift_zero_of_even {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = 0 := by
  have hp := aperiodic_parity hb.1 hkn.le
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb2⟩ := hk
  omega

end OddBarker

open Finset

namespace OddBarker

/-- The product of the terms of `C(u)` is `1 - (((n - u) - C(u)) % 4)`. -/
theorem prod_shift_eq {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {u : ℕ} (hun : u ≤ n) :
    ∏ j ∈ range (n - u), seq h j * seq h (j + u)
      = 1 - ((((n - u : ℕ) : ℤ) - aperiodic h u) % 4) := by
  have hx : ∀ i ∈ range (n - u),
      seq h i * seq h (i + u) = 1 ∨ seq h i * seq h (i + u) = -1 := by
    intro i hi
    have hi1 : i < n := by simp at hi; omega
    have hi2 : i + u < n := by simp at hi; omega
    rcases seq_sign hs hi1 with h1 | h1 <;> rcases seq_sign hs hi2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [(prod_signs (range (n - u)) (fun j => seq h j * seq h (j + u)) hx).1, card_range,
    ← aperiodic_eq_sum]

/-- Consecutive shifts share all factors but two. -/
theorem sk_prod_split {n : ℕ} (h : Fin n → ℤ) {u : ℕ} (hu : u + 1 ≤ n) :
    ∏ j ∈ range (n - u), seq h j * seq h (j + u)
      = (∏ j ∈ range (n - (u + 1)), seq h j * seq h (j + (u + 1)))
          * (seq h (n - 1 - u) * seq h u) := by
  have he : n - u = (n - (u + 1)) + 1 := by omega
  have h1 : n - (u + 1) = n - 1 - u := by omega
  have hA : ∏ j ∈ range (n - u), seq h j
      = (∏ j ∈ range (n - (u + 1)), seq h j) * seq h (n - 1 - u) := by
    rw [he, prod_range_succ, h1]
  have hB : ∏ j ∈ range (n - u), seq h (j + u)
      = (∏ j ∈ range (n - (u + 1)), seq h (j + (u + 1))) * seq h u := by
    rw [he, prod_range_succ']
    simp only [zero_add]
    congr 1
    apply prod_congr rfl
    intro j _
    congr 1
    omega
  rw [prod_mul_distrib, prod_mul_distrib, hA, hB]
  ring

theorem sk_neg_one_pow (x : ℕ) :
    ((-1 : ℤ) ^ x = 1 ∧ x % 2 = 0) ∨ ((-1 : ℤ) ^ x = -1 ∧ x % 2 = 1) := by
  rcases Nat.even_or_odd x with hx | hx
  · exact Or.inl ⟨hx.neg_one_pow, Nat.even_iff.mp hx⟩
  · exact Or.inr ⟨hx.neg_one_pow, Nat.odd_iff.mp hx⟩

/-- Skew-symmetry away from the last index. -/
theorem sk_skew_lt {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ}
    (hk : k + 1 < n) :
    seq h k * seq h (n - 1 - k) = (-1) ^ ((n - 1) / 2 + k) := by
  have hsplit := sk_prod_split h (u := k) (by omega)
  have hP1 := prod_shift_eq hb.1 (u := k + 1) (by omega)
  have hC1 := aperiodic_eq_internal h hn hb (k + 1) (by omega) (by omega)
  have hsg : seq h (n - 1 - k) * seq h k = 1 ∨ seq h (n - 1 - k) * seq h k = -1 := by
    rcases seq_sign hb.1 (i := n - 1 - k) (by omega) with h1 | h1 <;>
      rcases seq_sign hb.1 (i := k) (by omega) with h2 | h2 <;> rw [h1, h2] <;> norm_num
  rw [hP1] at hsplit
  rw [mul_comm]
  obtain ⟨q0, hP0, hq0⟩ : ∃ q, ∏ j ∈ range (n - k), seq h j * seq h (j + k) = q ∧
      ((k = 0 ∧ q = 1) ∨ (0 < k ∧ q = 1 - ((((n - k : ℕ) : ℤ) - aperiodic h k) % 4) ∧
        aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0)) := by
    rcases Nat.eq_zero_or_pos k with h0 | hk0
    · subst h0
      refine ⟨1, ?_, Or.inl ⟨rfl, rfl⟩⟩
      apply prod_eq_one
      intro j hj
      simp at hj
      simpa using seq_mul_self hb.1 hj
    · exact ⟨_, prod_shift_eq hb.1 (by omega), Or.inr ⟨hk0, rfl,
        aperiodic_eq_internal h hn hb k hk0 (by omega)⟩⟩
  rw [hP0] at hsplit
  generalize seq h (n - 1 - k) * seq h k = s at hsplit hsg ⊢
  generalize aperiodic h k = c0 at hq0
  generalize aperiodic h (k + 1) = c1 at hsplit hC1
  obtain ⟨t, rfl⟩ := hn
  have ht2 : (2 * t + 1 - 1) / 2 = t := by omega
  rw [ht2] at hq0 hC1 ⊢
  simp only [Nat.even_iff] at hq0 hC1
  rcases sk_neg_one_pow t with ⟨e1, p1⟩ | ⟨e1, p1⟩ <;>
  rcases sk_neg_one_pow (t + k) with ⟨e2, p2⟩ | ⟨e2, p2⟩ <;>
  rw [e1] at hq0 hC1 <;> rw [e2] <;>
  split_ifs at hq0 hC1 <;> rcases hsg with rfl | rfl <;> omega

/-- Skew-symmetry on `ℕ`: for odd `n`, a Barker sequence and `k < n`,
`a k * a (n - 1 - k) = (-1)^((n - 1)/2 + k)`. -/
theorem skew_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ} (hk : k < n) :
    seq h k * seq h (n - 1 - k) = (-1) ^ ((n - 1) / 2 + k) := by
  rcases Nat.lt_or_ge (k + 1) n with hk1 | hk1
  · exact sk_skew_lt hb hn hk1
  · have hkn : k = n - 1 := by omega
    rcases Nat.eq_zero_or_pos k with h0 | hk0
    · subst h0
      have hn1 : n = 1 := by omega
      subst hn1
      show seq h 0 * seq h 0 = (-1) ^ 0
      rw [pow_zero]
      exact seq_mul_self hb.1 (by norm_num)
    · have h0 := sk_skew_lt hb hn (k := 0) (by omega)
      have e : n - 1 - k = 0 := by omega
      rw [e, mul_comm]
      have e' : n - 1 - 0 = k := by omega
      rw [e'] at h0
      rw [h0]
      obtain ⟨t, rfl⟩ := hn
      rw [pow_add, pow_add, pow_zero, (show Even k from ⟨t, by omega⟩).neg_one_pow]

/-- The Challenge's `skew`. -/
theorem skew_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : Fin n) :
    h k * h (Fin.rev k) = (-1) ^ ((n - 1) / 2 + k.val) := by
  have h1 : h k = seq h k.val := by rw [seq_eq h k.isLt]
  have h2 : h (Fin.rev k) = seq h (n - 1 - k.val) := by
    rw [seq_eq h (by omega)]
    congr 1
    ext
    simp only [Fin.val_rev]
    omega
  rw [h1, h2]
  exact skew_seq hb hn k.isLt

/-- Sign changes mirror with a flip: for `1 ≤ s ≤ n - 1`,
`a (s - 1) * a s = -(a (n - s - 1) * a (n - s))`. -/
theorem skew_pair {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s + 1 ≤ n) :
    seq h (s - 1) * seq h s = -(seq h (n - s - 1) * seq h (n - s)) := by
  have e1 := skew_seq hb hn (k := s - 1) (by omega)
  have e2 := skew_seq hb hn (k := s) (by omega)
  have r1 : n - 1 - (s - 1) = n - s := by omega
  have r2 : n - 1 - s = n - s - 1 := by omega
  rw [r1] at e1
  rw [r2] at e2
  have hp : (-1 : ℤ) ^ ((n - 1) / 2 + s) = -(-1) ^ ((n - 1) / 2 + (s - 1)) := by
    have : (n - 1) / 2 + s = (n - 1) / 2 + (s - 1) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [hp, ← e1] at e2
  rcases seq_sign hb.1 (i := s - 1) (by omega) with h1 | h1 <;>
  rcases seq_sign hb.1 (i := s) (by omega) with h2 | h2 <;>
  rcases seq_sign hb.1 (i := n - s - 1) (by omega) with h3 | h3 <;>
  rcases seq_sign hb.1 (i := n - s) (by omega) with h4 | h4 <;>
  rw [h1, h2, h3, h4] at e2 <;> rw [h1, h2, h3, h4] <;>
    (revert e2; norm_num)

end OddBarker

open Finset

namespace OddBarker

/-- Cancelling a sign: `E * S = E` with `E * E = 1` gives `S = 1`. -/
theorem fo_cancel (E S : ℤ) (hE : E * E = 1) (h : E * S = E) : S = 1 := by
  linear_combination E * h + (1 - S) * hE

/-- `∏_{k < j} (-1)^k` read off `j mod 4`. -/
theorem fo_prod_neg_one_pow (j : ℕ) :
    ∏ k ∈ range j, (-1 : ℤ) ^ k = if j % 4 = 0 ∨ j % 4 = 1 then 1 else -1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, ih]
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow]
      obtain ⟨r, hr⟩ := he
      split_ifs <;> omega
    · rw [ho.neg_one_pow]
      obtain ⟨r, hr⟩ := ho
      split_ifs <;> omega

/-- The folded identity on `ℕ`: `T0 (seq h) w = 1` for even `w ≤ n - 3`. -/
theorem fold_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {w : ℕ} (hw : Even w)
    (hwn : w + 3 ≤ n) : T0 (seq h) w = 1 := by
  have hN : aperiodic h (n - 1 - w) = (-1) ^ ((n - 1) / 2) := by
    apply even_shift_eq hb hn
    · obtain ⟨r, hr⟩ := hn
      obtain ⟨s, hs⟩ := hw
      exact ⟨r - s, by omega⟩
    · omega
    · omega
  rw [aperiodic_eq_sum, show n - (n - 1 - w) = w + 1 by omega] at hN
  have hterm : ∀ j ∈ range (w + 1), seq h j * seq h (j + (n - 1 - w))
      = (-1) ^ ((n - 1) / 2) * ((-1) ^ j * seq h j * seq h (w - j)) := by
    intro j hj
    have hj' : j ≤ w := by have := Finset.mem_range.mp hj; omega
    have hk : w - j < n := by omega
    have hsk := skew_seq hb hn hk
    rw [show n - 1 - (w - j) = j + (n - 1 - w) by omega] at hsk
    have hpow : (-1 : ℤ) ^ ((n - 1) / 2 + (w - j)) = (-1) ^ ((n - 1) / 2) * (-1) ^ j := by
      rw [pow_add, neg_one_pow_sub hj', hw.neg_one_pow, one_mul]
    rw [hpow] at hsk
    have hsq := seq_mul_self hb.1 hk
    linear_combination (seq h j * seq h (w - j)) * hsk - (seq h j * seq h (j + (n - 1 - w))) * hsq
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hN
  unfold T0
  exact fo_cancel _ _ (by rw [← mul_pow]; norm_num) hN

/-- The Challenge's `fold`. -/
theorem fold_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (w : ℕ) (hw : Even w)
    (hwn : w + 3 ≤ n) :
    ∑ k : Fin (w + 1), (-1) ^ k.val * h ⟨k.val, by omega⟩ * h ⟨w - k.val, by omega⟩ = 1 := by
  have hT := fold_seq hb hn hw hwn
  unfold T0 at hT
  rw [← Fin.sum_univ_eq_sum_range (fun k => (-1 : ℤ) ^ k * seq h k * seq h (w - k)) (w + 1)] at hT
  refine Eq.trans ?_ hT
  apply Finset.sum_congr rfl
  intro k _
  have hk1 : k.val < n := by omega
  have hk2 : w - k.val < n := by omega
  simp only [seq_eq h hk1, seq_eq h hk2]

/-- `∏_{i ≤ 2j} a i = a j` for `2j ≤ n - 3`. -/
theorem prod_prefix {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {j : ℕ}
    (hj : 2 * j + 3 ≤ n) :
    ∏ i ∈ range (2 * j + 1), seq h i = seq h j := by
  have hT := fold_seq hb hn (w := 2 * j) ⟨j, by ring⟩ hj
  unfold T0 at hT
  have hsplit : ∑ k ∈ range (2 * j + 1), (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)
      = 2 * ∑ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k) + (-1) ^ j := by
    rw [show 2 * j + 1 = (j + 1) + j by omega, Finset.sum_range_add, Finset.sum_range_succ]
    have hmid : (-1 : ℤ) ^ j * seq h j * seq h (2 * j - j) = (-1) ^ j := by
      rw [show 2 * j - j = j by omega, mul_assoc, seq_mul_self hb.1 (by omega), mul_one]
    have hup : ∑ x ∈ range j, (-1 : ℤ) ^ (j + 1 + x) * seq h (j + 1 + x) * seq h (2 * j - (j + 1 + x))
        = ∑ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k) := by
      rw [← Finset.sum_range_reflect (fun k => (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)) j]
      apply Finset.sum_congr rfl
      intro x hx
      have hx' : x < j := Finset.mem_range.mp hx
      show (-1 : ℤ) ^ (j + 1 + x) * seq h (j + 1 + x) * seq h (2 * j - (j + 1 + x))
        = (-1 : ℤ) ^ (j - 1 - x) * seq h (j - 1 - x) * seq h (2 * j - (j - 1 - x))
      have hp : (-1 : ℤ) ^ (j + 1 + x) = (-1) ^ (j - 1 - x) := by
        rw [show j + 1 + x = (j - 1 - x) + 2 * (x + 1) by omega, pow_add,
          (even_two_mul (x + 1)).neg_one_pow, mul_one]
      rw [hp, show 2 * j - (j + 1 + x) = j - 1 - x by omega,
        show 2 * j - (j - 1 - x) = j + 1 + x by omega]
      ring
    rw [hmid, hup]
    ring
  have hL : 2 * ∑ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k) = 1 - (-1) ^ j := by
    rw [hsplit] at hT
    linarith
  obtain ⟨hps, -⟩ := prod_signs (range j) (fun k => (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)) (by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rcases neg_one_pow_eq_or ℤ k with h1 | h1 <;>
    rcases seq_sign hb.1 (show k < n by omega) with h2 | h2 <;>
    rcases seq_sign hb.1 (show 2 * j - k < n by omega) with h3 | h3 <;>
    simp only [h1, h2, h3] <;> norm_num)
  simp only [Finset.card_range] at hps
  have hE := fo_prod_neg_one_pow j
  have hPE : ∏ k ∈ range j, (-1 : ℤ) ^ k * seq h k * seq h (2 * j - k)
      = ∏ k ∈ range j, (-1 : ℤ) ^ k := by
    rw [hps, hE]
    rcases Nat.even_or_odd j with he | ho
    · rw [he.neg_one_pow] at hL
      obtain ⟨r, hr⟩ := he
      split_ifs <;> omega
    · rw [ho.neg_one_pow] at hL
      obtain ⟨r, hr⟩ := ho
      split_ifs <;> omega
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_assoc] at hPE
  have hAB := fo_cancel _ _ (by rw [hE]; split_ifs <;> norm_num) hPE
  have hrefl : ∏ x ∈ range j, seq h (j + 1 + x) = ∏ k ∈ range j, seq h (2 * j - k) := by
    rw [← Finset.prod_range_reflect (fun x => seq h (j + 1 + x)) j]
    apply Finset.prod_congr rfl
    intro x hx
    have hx' : x < j := Finset.mem_range.mp hx
    show seq h (j + 1 + (j - 1 - x)) = seq h (2 * j - x)
    rw [show j + 1 + (j - 1 - x) = 2 * j - x by omega]
  rw [show 2 * j + 1 = (j + 1) + j by omega, Finset.prod_range_add, Finset.prod_range_succ, hrefl]
  linear_combination seq h j * hAB

/-- The doubling law on `ℕ`: `a (u - 1) a u = a (2u - 1) a (2u)` for `1 ≤ u`, `2u + 3 ≤ n`. -/
theorem doubling_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {u : ℕ} (hu : 1 ≤ u)
    (hun : 2 * u + 3 ≤ n) :
    seq h (u - 1) * seq h u = seq h (2 * u - 1) * seq h (2 * u) := by
  have h1 := prod_prefix hb hn (j := u) hun
  have h2 := prod_prefix hb hn (j := u - 1) (by omega)
  rw [show 2 * u + 1 = (2 * (u - 1) + 1) + 1 + 1 by omega, Finset.prod_range_succ,
    Finset.prod_range_succ, h2, show 2 * (u - 1) + 1 + 1 = 2 * u by omega,
    show 2 * (u - 1) + 1 = 2 * u - 1 by omega] at h1
  have hsq := seq_mul_self hb.1 (show u - 1 < n by omega)
  linear_combination (-seq h (u - 1)) * h1 + (seq h (2 * u - 1) * seq h (2 * u)) * hsq

/-- The Challenge's `doubling`. -/
theorem doubling_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (u : ℕ)
    (hu : 1 ≤ u) (hun : 2 * u + 3 ≤ n) :
    h ⟨u - 1, by omega⟩ * h ⟨u, by omega⟩ = h ⟨2 * u - 1, by omega⟩ * h ⟨2 * u, by omega⟩ := by
  have hd := doubling_seq hb hn hu hun
  rwa [seq_eq h (show u - 1 < n by omega), seq_eq h (show u < n by omega),
    seq_eq h (show 2 * u - 1 < n by omega), seq_eq h (show 2 * u < n by omega)] at hd

end OddBarker

open Finset

namespace OddBarker

/-- Four signs with `x y = -(z w)`: `y ≠ x ↔ w = z`. -/
theorem ru_sign4 {x y z w : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hz : z = 1 ∨ z = -1) (hw : w = 1 ∨ w = -1) (he : x * y = -(z * w)) : (y ≠ x ↔ w = z) := by
  revert he
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    rcases hw with rfl | rfl <;> norm_num

/-- Four signs with `x y = z w`: `y ≠ x ↔ w ≠ z`. -/
theorem ru_sign4' {x y z w : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hz : z = 1 ∨ z = -1) (hw : w = 1 ∨ w = -1) (he : x * y = z * w) : (y ≠ x ↔ w ≠ z) := by
  revert he
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    rcases hw with rfl | rfl <;> norm_num

/-- The mirror: `s` is a sign change iff `n - s` is not. -/
theorem ru_mirror {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h s ≠ seq h (s - 1) ↔ seq h (n - s) = seq h (n - s - 1) :=
  ru_sign4 (seq_sign hb.1 (by omega : s - 1 < n)) (seq_sign hb.1 hsn)
    (seq_sign hb.1 (by omega : n - s - 1 < n)) (seq_sign hb.1 (by omega : n - s < n))
    (skew_pair hb hn hs1 (by omega))

/-- The mirror, other form: `s` is not a sign change iff `n - s` is. -/
theorem ru_mirror' {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h s = seq h (s - 1) ↔ seq h (n - s) ≠ seq h (n - s - 1) := by
  have := ru_mirror hb hn hs1 hsn
  tauto

/-- Doubling: `u` is a sign change iff `2u` is. -/
theorem ru_double {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {u : ℕ} (hu : 1 ≤ u)
    (hun : 2 * u + 3 ≤ n) : seq h u ≠ seq h (u - 1) ↔ seq h (2 * u) ≠ seq h (2 * u - 1) :=
  ru_sign4' (seq_sign hb.1 (by omega : u - 1 < n)) (seq_sign hb.1 (by omega : u < n))
    (seq_sign hb.1 (by omega : 2 * u - 1 < n)) (seq_sign hb.1 (by omega : 2 * u < n))
    (doubling_seq hb hn hu hun)

/-- Two multiples of `p ≥ 3` at distance `1` or `2` cannot exist. -/
theorem ru_dvd_close {p a b : ℕ} (hp : 3 ≤ p) (ha : p ∣ a) (hb : p ∣ b) (hab : a < b)
    (hba : b ≤ a + 2) : False := by
  have h1 := Nat.dvd_sub hb ha
  have h2 := Nat.le_of_dvd (by omega) h1
  omega

theorem two_le_p {n : ℕ} {h : Fin n → ℤ} (h01 : seq h 0 = seq h 1) {p : ℕ}
    (hpB : seq h p ≠ seq h (p - 1)) : 2 ≤ p := by
  by_contra hlt
  interval_cases p
  · exact hpB rfl
  · exact hpB h01.symm

theorem two_mul_p_le {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) :
    2 * p ≤ n + 1 := by
  by_contra hlt
  have h1 := (ru_mirror' hb hn (s := p - 1) (by omega) (by omega)).mp
    (hpmin (p - 1) (by omega) (by omega))
  have e1 : n - (p - 1) = n - p + 1 := by omega
  rw [e1] at h1
  exact h1 (hpmin (n - p + 1) (by omega) (by omega))

theorem p_odd {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) :
    Odd p := by
  have hp := two_mul_p_le hb hn h7 hpn hpB hpmin hp2
  rcases Nat.even_or_odd p with ⟨u, hu⟩ | ho
  · exfalso
    have e : 2 * u = p := by omega
    have hd := (ru_double hb hn (u := u) (by omega) (by omega)).mpr (by rw [e]; exact hpB)
    exact hd (hpmin u (by omega) (by omega))
  · exact ho

/-- A sign change not divisible by `p` exists (`n - 1` or `n - 2`). -/
theorem exists_q {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p) :
    ∃ s, 0 < s ∧ s < n ∧ seq h s ≠ seq h (s - 1) ∧ ¬ p ∣ s := by
  have c1 := (ru_mirror' hb hn (s := 1) (by omega) (by omega)).mp (hpmin 1 (by omega) (by omega))
  have c2 := (ru_mirror' hb hn (s := 2) (by omega) (by omega)).mp (hpmin 2 (by omega) (by omega))
  by_cases hd : p ∣ n - 1
  · refine ⟨n - 2, by omega, by omega, c2, ?_⟩
    intro hd2
    exact ru_dvd_close hp3 hd2 hd (by omega) (by omega)
  · exact ⟨n - 1, by omega, by omega, c1, hd⟩

theorem p_lt_q {n : ℕ} {h : Fin n → ℤ} {p q : ℕ}
    (hpB : seq h p ≠ seq h (p - 1)) (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q) (hp2 : 2 ≤ p) : p < q := by
  rcases Nat.lt_or_ge p q with hlt | hge
  · exact hlt
  · exfalso
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · exact hpq (heq ▸ dvd_refl p)
    · rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; exact hqB rfl
      · exact hqB (hpmin q h0 hlt)

/-- For `t` and `n - t` both in `[1, q)`: `p` divides one of them. -/
theorem ru_either {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {p q t : ℕ}
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s)
    (ht1 : 1 ≤ t) (htq : t < q) (htn : t < n) (hmq : n - t < q) : p ∣ t ∨ p ∣ n - t := by
  by_cases hc : seq h t ≠ seq h (t - 1)
  · exact Or.inl (hqmin t (by omega) htq hc)
  · have hm := (ru_mirror' hb hn ht1 htn).mp (not_not.mp hc)
    exact Or.inr (hqmin (n - t) (by omega) hmq hm)

theorem two_mul_q_le {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    2 * q ≤ n + 3 := by
  have hplq := p_lt_q hpB hpmin hqB hpq (by omega)
  by_contra hlt
  have H1 := ru_either hb hn hqmin (t := n - q + 1) (by omega) (by omega) (by omega) (by omega)
  have H2 := ru_either hb hn hqmin (t := n - q + 2) (by omega) (by omega) (by omega) (by omega)
  have H3 := ru_either hb hn hqmin (t := n - q + 3) (by omega) (by omega) (by omega) (by omega)
  rcases H1 with H1 | H1 <;> rcases H2 with H2 | H2 <;> rcases H3 with H3 | H3 <;>
    first
    | exact ru_dvd_close hp3 H1 H2 (by omega) (by omega)
    | exact ru_dvd_close hp3 H2 H1 (by omega) (by omega)
    | exact ru_dvd_close hp3 H1 H3 (by omega) (by omega)
    | exact ru_dvd_close hp3 H3 H1 (by omega) (by omega)
    | exact ru_dvd_close hp3 H2 H3 (by omega) (by omega)
    | exact ru_dvd_close hp3 H3 H2 (by omega) (by omega)

theorem q_odd {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp3 : 3 ≤ p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) (hq : 2 * q ≤ n + 3) :
    Odd q := by
  have hplq := p_lt_q hpB hpmin hqB hpq (by omega)
  rcases Nat.even_or_odd q with ⟨u, hu⟩ | ho
  · exfalso
    obtain ⟨k, hk⟩ := hn
    have e : 2 * u = q := by omega
    have hd := (ru_double hb ⟨k, hk⟩ (u := u) (by omega) (by omega)).mpr (by rw [e]; exact hqB)
    have hdu := hqmin u (by omega) (by omega) hd
    exact hpq (e ▸ Dvd.dvd.mul_left hdu 2)
  · exact ho

/-- Lemma 4: `n ≤ p + q + 1`. -/
theorem n_le_p_add_q_add_one {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1)) (hp2 : 2 ≤ p) (hpodd : Odd p)
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) (hqodd : Odd q) (hplq : p < q) :
    n ≤ p + q + 1 := by
  by_contra hlt
  have hle : p + q + 3 ≤ n := by
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb'⟩ := hqodd
    obtain ⟨c, hc⟩ := hn
    omega
  have hw0 : Even (p + q - 2) := by
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb'⟩ := hqodd
    exact ⟨a + b, by omega⟩
  have hw2 : Even (p + q) := by
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb'⟩ := hqodd
    exact ⟨a + b + 1, by omega⟩
  have hT0 := fold_seq hb hn hw0 (by omega)
  have hT2 := fold_seq hb hn hw2 (by omega)
  exact key_bound (seq h) p q (fun i hi => seq_sign hb.1 (by omega)) hp2 hplq hpB
    (fun s hs1 hsp => hpmin s (by omega) hsp) hqB hpq
    (fun s hs1 hsq hc => hqmin s (by omega) hsq hc) hpodd hqodd hT0 hT2

/-- The run bounds on `ℕ`. -/
theorem run_bounds_seq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    (h01 : seq h 0 = seq h 1) {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 := by
  have hp2 := two_le_p h01 hpB
  have hpodd := p_odd hb hn h7 hpn hpB hpmin hp2
  have hp3 : 3 ≤ p := by
    obtain ⟨a, ha⟩ := hpodd
    omega
  have hplq := p_lt_q hpB hpmin hqB hpq hp2
  have hq := two_mul_q_le hb hn h7 hpn hpB hpmin hp3 hqn hqB hpq hqmin
  have hqodd := q_odd hb hn h7 hpn hpB hpmin hp3 hqn hqB hpq hqmin hq
  exact ⟨hpodd, hqodd, hq,
    n_le_p_add_q_add_one hb hn h7 hpn hpB hpmin hp2 hpodd hqn hqB hpq hqmin hqodd hplq⟩

/-- The Challenge's `run_bounds`. -/
theorem run_bounds_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (h7 : 7 ≤ n)
    (h01 : h ⟨0, by omega⟩ = h ⟨1, by omega⟩) (p q : ℕ)
    (hpn : p < n) (hpB : h ⟨p, hpn⟩ ≠ h ⟨p - 1, by omega⟩)
    (hpmin : ∀ s (hs0 : 0 < s) (hsp : s < p), h ⟨s, by omega⟩ = h ⟨s - 1, by omega⟩)
    (hqn : q < n) (hqB : h ⟨q, hqn⟩ ≠ h ⟨q - 1, by omega⟩) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s (hs0 : 0 < s) (hsq : s < q), h ⟨s, by omega⟩ ≠ h ⟨s - 1, by omega⟩ → p ∣ s) :
    Odd p ∧ Odd q ∧ 2 * q ≤ n + 3 ∧ n ≤ p + q + 1 := by
  refine run_bounds_seq hb hn h7 ?_ hpn ?_ ?_ hqn ?_ hpq ?_
  · rw [seq_eq h (by omega : 0 < n), seq_eq h (by omega : 1 < n)]
    exact h01
  · rw [seq_eq h hpn, seq_eq h (by omega : p - 1 < n)]
    exact hpB
  · intro s hs0 hsp
    rw [seq_eq h (by omega : s < n), seq_eq h (by omega : s - 1 < n)]
    exact hpmin s hs0 hsp
  · rw [seq_eq h hqn, seq_eq h (by omega : q - 1 < n)]
    exact hqB
  · intro s hs0 hsq hc
    rw [seq_eq h (by omega : s < n), seq_eq h (by omega : s - 1 < n)] at hc
    exact hqmin s hs0 hsq hc

end OddBarker

open Finset

namespace OddBarker

/-- For `1 ≤ s < n`: `s` is a sign change iff `d s = -1`. -/
theorem en_change_iff {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h s ≠ seq h (s - 1) ↔ seq h (s - 1) * seq h s = -1 := by
  rcases seq_sign hb.1 (show s - 1 < n by omega) with h1 | h1 <;>
    rcases seq_sign hb.1 hsn with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- For `1 ≤ s < n`: `d s = 1 ∨ d s = -1`. -/
theorem en_d_sign {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) {s : ℕ} (hs1 : 1 ≤ s)
    (hsn : s < n) : seq h (s - 1) * seq h s = 1 ∨ seq h (s - 1) * seq h s = -1 := by
  rcases seq_sign hb.1 (show s - 1 < n by omega) with h1 | h1 <;>
    rcases seq_sign hb.1 hsn with h2 | h2 <;> rw [h1, h2] <;> norm_num

theorem endgame {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (h7 : 7 ≤ n)
    (h01 : seq h 0 = seq h 1) {p q : ℕ} (hpn : p < n) (hpB : seq h p ≠ seq h (p - 1))
    (hpmin : ∀ s, 0 < s → s < p → seq h s = seq h (s - 1))
    (hqn : q < n) (hqB : seq h q ≠ seq h (q - 1)) (hpq : ¬ p ∣ q)
    (hqmin : ∀ s, 0 < s → s < q → seq h s ≠ seq h (s - 1) → p ∣ s) :
    n = 7 ∨ n = 11 ∨ n = 13 := by
  obtain ⟨hpo, hqo, hq2, hnpq⟩ :=
    run_bounds_seq hb hn h7 h01 hpn hpB hpmin hqn hqB hpq hqmin
  have hp2 := two_le_p h01 hpB
  have hplq := p_lt_q hpB hpmin hqB hpq hp2
  have hn' := hn
  obtain ⟨a, ha⟩ := hpo
  obtain ⟨b, hb'⟩ := hqo
  obtain ⟨c, hc⟩ := hn'
  have hp3 : 3 ≤ p := by omega
  have hcase : (q = p + 2 ∧ (n = 2 * p + 1 ∨ n = 2 * p + 3)) ∨ (q = p + 4 ∧ n = 2 * p + 5) := by
    omega
  rcases hcase with ⟨hq, hn2⟩ | ⟨hq, hn2⟩
  · -- `q = p + 2`: position `2p - 2` is not a change, so `n - 2p + 2` is.
    have hdbl := doubling_seq hb hn (u := p - 1) (by omega) (by omega)
    have hsk := skew_pair hb hn (s := 2 * (p - 1)) (by omega) (by omega)
    have hpm := hpmin (p - 1) (by omega) (by omega)
    rw [hpm, seq_mul_self hb.1 (by omega)] at hdbl
    have hd : seq h (n - 2 * (p - 1) - 1) * seq h (n - 2 * (p - 1)) = -1 := by linarith
    have hch := (en_change_iff hb (s := n - 2 * (p - 1)) (by omega) (by omega)).mpr hd
    rcases hn2 with hn2 | hn2
    · have hdv := hqmin _ (by omega) (by omega) hch
      rw [show n - 2 * (p - 1) = 3 by omega] at hdv
      have := Nat.le_of_dvd (by norm_num) hdv
      omega
    · by_cases hp5 : p = 3
      · exfalso
        subst hp5
        have hdb3 := doubling_seq hb hn (u := 3) (by norm_num) (by omega)
        have hsk3 := skew_pair hb hn (s := 3) (by norm_num) (by omega)
        rw [show n - 3 - 1 = 2 * 3 - 1 by omega, show n - 3 = 2 * 3 by omega] at hsk3
        have hz : seq h (2 * 3 - 1) * seq h (2 * 3) = 0 := by linarith
        rcases seq_sign hb.1 (show 2 * 3 - 1 < n by omega) with e1 | e1 <;>
          rcases seq_sign hb.1 (show 2 * 3 < n by omega) with e2 | e2 <;>
          rw [e1, e2] at hz <;> norm_num at hz
      · have hdv := hqmin _ (by omega) (by omega) hch
        rw [show n - 2 * (p - 1) = 5 by omega] at hdv
        have := Nat.le_of_dvd (by norm_num) hdv
        omega
  · -- `q = p + 4`, `n = 2p + 5`: one of `p + 2`, `p + 3` is a change.
    have hsk := skew_pair hb hn (s := p + 3) (by omega) (by omega)
    rw [show n - (p + 3) - 1 = p + 2 - 1 by omega, show n - (p + 3) = p + 2 by omega] at hsk
    rcases en_d_sign hb (s := p + 2) (by omega) (by omega) with hd | hd
    · have hd3 : seq h (p + 3 - 1) * seq h (p + 3) = -1 := by rw [hsk, hd]
      have hch := (en_change_iff hb (s := p + 3) (by omega) (by omega)).mpr hd3
      have hdv := hqmin _ (by omega) (by omega) hch
      have h3 := (Nat.dvd_add_right (dvd_refl p)).mp hdv
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have hch := (en_change_iff hb (s := p + 2) (by omega) (by omega)).mpr hd
      have hdv := hqmin _ (by omega) (by omega) hch
      have h2 := (Nat.dvd_add_right (dvd_refl p)).mp hdv
      have := Nat.le_of_dvd (by norm_num) h2
      omega

/-- The alternation `j ↦ (-1)^j h j`. -/
def alt {n : ℕ} (h : Fin n → ℤ) : Fin n → ℤ := fun j => (-1) ^ j.val * h j

theorem en_seq_alt {n : ℕ} (h : Fin n → ℤ) (i : ℕ) : seq (alt h) i = (-1) ^ i * seq h i := by
  unfold seq
  split_ifs with hi
  · simp [alt]
  · simp

theorem aperiodic_alt {n : ℕ} (h : Fin n → ℤ) (k : ℕ) :
    aperiodic (alt h) k = (-1) ^ k * aperiodic h k := by
  rw [aperiodic_eq_sum, aperiodic_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [en_seq_alt, en_seq_alt, pow_add]
  have h2 : ((-1 : ℤ) ^ j) * (-1) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (seq h j * seq h (j + k) * (-1) ^ k) * h2

theorem isBarker_alt {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) : IsBarker (alt h) := by
  refine ⟨fun j => ?_, fun k hk0 hkn => ?_⟩
  · rcases hb.1 j with h1 | h1 <;> rcases neg_one_pow_eq_or ℤ j.val with h2 | h2 <;>
      simp [alt, IsSign, h1, h2]
  · rw [aperiodic_alt, abs_mul, abs_neg_one_pow, one_mul]
    exact hb.2 k hk0 hkn

/-- The endgame from `seq g 0 = seq g 1`, with `p`, `q` found by `Nat.find`. -/
theorem en_of_h01 {n : ℕ} (g : Fin n → ℤ) (hn : Odd n) (hg : IsBarker g) (h7 : 7 ≤ n)
    (h01 : seq g 0 = seq g 1) : n = 7 ∨ n = 11 ∨ n = 13 := by
  have hex : ∃ s, 0 < s ∧ s < n ∧ seq g s ≠ seq g (s - 1) := by
    refine ⟨n - 1, by omega, by omega, ?_⟩
    have hs := skew_pair hg hn (s := 1) le_rfl (by omega)
    rw [show (1 : ℕ) - 1 = 0 from rfl, h01, seq_mul_self hg.1 (show 1 < n by omega)] at hs
    exact (en_change_iff hg (s := n - 1) (by omega) (by omega)).mpr (by linarith)
  obtain ⟨p, ⟨hp0, hpn, hpB⟩, hpm⟩ :
      ∃ p, (0 < p ∧ p < n ∧ seq g p ≠ seq g (p - 1)) ∧
        ∀ m, m < p → ¬ (0 < m ∧ m < n ∧ seq g m ≠ seq g (m - 1)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hpmin : ∀ s, 0 < s → s < p → seq g s = seq g (s - 1) := by
    intro s hs0 hsp
    by_contra hne
    exact hpm s hsp ⟨hs0, by omega, hne⟩
  have hp2 := two_le_p h01 hpB
  have hpo := p_odd hg hn h7 hpn hpB hpmin hp2
  have hp3 : 3 ≤ p := by obtain ⟨c, hc⟩ := hpo; omega
  have hexq := exists_q hg hn h7 hpn hpB hpmin hp3
  obtain ⟨q, ⟨hq0, hqn, hqB, hpq⟩, hqm⟩ :
      ∃ q, (0 < q ∧ q < n ∧ seq g q ≠ seq g (q - 1) ∧ ¬ p ∣ q) ∧
        ∀ m, m < q → ¬ (0 < m ∧ m < n ∧ seq g m ≠ seq g (m - 1) ∧ ¬ p ∣ m) :=
    ⟨Nat.find hexq, Nat.find_spec hexq, fun m hm => Nat.find_min hexq hm⟩
  have hqmin : ∀ s, 0 < s → s < q → seq g s ≠ seq g (s - 1) → p ∣ s := by
    intro s hs0 hsq hne
    by_contra hnd
    exact hqm s hsq ⟨hs0, by omega, hne, hnd⟩
  exact endgame hg hn h7 h01 hpn hpB hpmin hqn hqB hpq hqmin

/-- The Challenge's `odd_length_mem`. -/
theorem odd_length_mem_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 := by
  by_cases h7 : n < 7
  · obtain ⟨c, hc⟩ := hn
    omega
  push Not at h7
  have hor : seq h 0 = seq h 1 ∨ seq (alt h) 0 = seq (alt h) 1 := by
    rw [en_seq_alt, en_seq_alt]
    rcases seq_sign hb.1 (show 0 < n by omega) with e0 | e0 <;>
      rcases seq_sign hb.1 (show 1 < n by omega) with e1 | e1 <;> rw [e0, e1] <;> norm_num
  have key : n = 7 ∨ n = 11 ∨ n = 13 := by
    rcases hor with e | e
    · exact en_of_h01 h hn hb h7 e
    · exact en_of_h01 (alt h) hn (isBarker_alt hb) h7 e
  rcases key with e | e | e <;> omega

end OddBarker
namespace BarkerList

/-- Convert the list specification into the indexed autocorrelation used by Schmidt and Willms. -/
theorem aperiodic_eq_fin (a : List ℤ) (k : ℕ) :
    aperiodicAutocorrelation a k = OddBarker.aperiodic a.get k := by
  have h : a.zipWith (· * ·) (a.drop k) = List.ofFn (fun j : Fin (a.length - k) =>
      a[j.val]'(Nat.lt_of_lt_of_le j.isLt (Nat.sub_le _ _)) *
      a[j.val+k]'(Nat.add_lt_of_lt_sub j.isLt)) := by
    apply List.ext_getElem
    · simp [Nat.min_eq_right (Nat.sub_le a.length k)]
    · intro i hi hj
      simp [List.getElem_zipWith, List.getElem_drop, Nat.add_comm]
  simp only [aperiodicAutocorrelation, h, List.sum_ofFn, OddBarker.aperiodic, List.get_eq_getElem]

theorem indexed_barker (a : List ℤ) (ha : IsBarkerSequence a) : OddBarker.IsBarker a.get := by
  refine ⟨fun j => ha.1 _ (List.get_mem a j), fun k hk hkl => ?_⟩
  rw [← aperiodic_eq_fin]
  exact ha.2 k hk hkl

end BarkerList

namespace BarkerList

theorem odd_length_bound (a : List ℤ) (ha : IsBarkerSequence a) (ho : Odd a.length) : a.length ≤ 13 := by
  have h := OddBarker.odd_length_mem_internal a.get ho (indexed_barker a ha)
  omega

end BarkerList

namespace BarkerEven

namespace OddBarker

universe u

/-- `x` is `1` or `-1`. -/
def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

open scoped BigOperators

/-- The aperiodic autocorrelation of `h` at shift `k`: `∑_{j < n - k} h j * h (j + k)`. -/
def aperiodic {n : ℕ} (h : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ j : Fin (n - k), h ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n k)⟩ *
    h ⟨j.val + k, Nat.add_lt_of_lt_sub j.isLt⟩

/-- Every entry is a sign and every nontrivial aperiodic autocorrelation has absolute value at
most one. -/
def IsBarker {n : ℕ} (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧ ∀ k : ℕ, 0 < k → k < n → |aperiodic h k| ≤ 1

/-- Real `n × n` matrices. -/
abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- `H` is circulant: `H i j` depends only on `j - i` in `Fin n`. -/
def IsCirculant {n : ℕ} (H : RealMatrix n) : Prop :=
  ∃ h : Fin n → ℝ, ∀ i j, H i j = h (j - i)

/-- `H` is a `±1` matrix with `H Hᵀ = n I`. -/
def IsSignHadamard {n : ℕ} (H : RealMatrix n) : Prop :=
  (∀ i j, IsSign (H i j)) ∧
    H * H.transpose = (n : ℝ) • (1 : RealMatrix n)

/-- A real circulant Hadamard matrix of order `n` exists. -/
def ExistsRealCirculantHadamard (n : ℕ) : Prop :=
  ∃ H : RealMatrix n, IsCirculant H ∧ IsSignHadamard H


end OddBarker

open Finset

namespace OddBarker

/-- The sequence read on `ℕ`, zero outside `[0, n)`. -/
def seq {n : ℕ} (h : Fin n → ℤ) (i : ℕ) : ℤ := if hi : i < n then h ⟨i, hi⟩ else 0

theorem seq_eq {n : ℕ} (h : Fin n → ℤ) {i : ℕ} (hi : i < n) : seq h i = h ⟨i, hi⟩ := by
  simp [seq, hi]

theorem seq_of_le {n : ℕ} (h : Fin n → ℤ) {i : ℕ} (hi : n ≤ i) : seq h i = 0 := by
  simp [seq, not_lt.mpr hi]

theorem aperiodic_eq_sum {n : ℕ} (h : Fin n → ℤ) (k : ℕ) :
    aperiodic h k = ∑ j ∈ range (n - k), seq h j * seq h (j + k) := by
  unfold aperiodic
  rw [← Fin.sum_univ_eq_sum_range (fun j => seq h j * seq h (j + k)) (n - k)]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : j.val < n := by omega
  have h2 : j.val + k < n := by omega
  simp [seq, h1, h2]

/-- A product of signs is `1 - ((card - sum) % 4)`, and `card - sum` is even. -/
theorem prod_signs (s : Finset ℕ) (x : ℕ → ℤ) (hx : ∀ i ∈ s, x i = 1 ∨ x i = -1) :
    ∏ i ∈ s, x i = 1 - (((s.card : ℤ) - ∑ i ∈ s, x i) % 4) ∧
      ((s.card : ℤ) - ∑ i ∈ s, x i) % 2 = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih1]
    rcases hx a (Finset.mem_insert_self a s) with h | h <;> rw [h] <;> push_cast <;> omega

theorem seq_sign {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {i : ℕ} (hi : i < n) :
    seq h i = 1 ∨ seq h i = -1 := by
  simpa [seq, hi, IsSign] using hs ⟨i, hi⟩

theorem seq_mul_self {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {i : ℕ} (hi : i < n) :
    seq h i * seq h i = 1 := by
  rcases seq_sign hs hi with h1 | h1 <;> rw [h1] <;> norm_num

/-- `2 ∣ C(k) - (n - k)` for a sign sequence (each term is `±1`). -/
theorem aperiodic_parity {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) {k : ℕ} (hk : k ≤ n) :
    (2 : ℤ) ∣ aperiodic h k - ((n - k : ℕ) : ℤ) := by
  have hdvd : (2 : ℤ) ∣ ∑ j ∈ range (n - k), (seq h j * seq h (j + k) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j < n := by simp at hj; omega
    have hj2 : j + k < n := by simp at hj; omega
    rcases seq_sign hs hj1 with h1 | h1 <;> rcases seq_sign hs hj2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [Finset.sum_sub_distrib, ← aperiodic_eq_sum] at hdvd
  simpa using hdvd

theorem odd_shift_zero {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) (k : ℕ)
    (hk : Odd k) (hk0 : 0 < k) (hkn : k < n) : aperiodic h k = 0 := by
  have hdvd : (2 : ℤ) ∣ ∑ j ∈ range (n - k), (seq h j * seq h (j + k) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j < n := by simp at hj; omega
    have hj2 : j + k < n := by simp at hj; omega
    rcases seq_sign hb.1 hj1 with h1 | h1 <;> rcases seq_sign hb.1 hj2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [Finset.sum_sub_distrib, ← aperiodic_eq_sum] at hdvd
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hdvd
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ := hdvd
  have hc : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by push_cast [hkn.le]; ring
  rw [hc] at hd
  subst hu hv
  push_cast at hd
  omega

end OddBarker

open Finset

namespace OddBarker

/-- Split a range sum at `a`, with the tail indexed as `i + a`. -/
theorem pa_split (f : ℕ → ℤ) (a b : ℕ) :
    ∑ j ∈ range (a + b), f j = ∑ j ∈ range a, f j + ∑ i ∈ range b, f (i + a) := by
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm]

/-- `C(u) + C(n - u) ≡ n (mod 4)` for a sign sequence and `0 < u < n`. -/
theorem aperiodic_add_aperiodic_sub_mod_four {n : ℕ} {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j))
    {u : ℕ} (hu0 : 0 < u) (hun : u < n) :
    (4 : ℤ) ∣ aperiodic h u + aperiodic h (n - u) - n := by
  obtain ⟨v, hv⟩ : ∃ v, v = n - u := ⟨_, rfl⟩
  have hvu : n - v = u := by omega
  rw [← hv, aperiodic_eq_sum h u, aperiodic_eq_sum h v, ← hv, hvu]
  have h1 : (4 : ℤ) ∣ ∑ j ∈ range v,
      (seq h j * seq h (j + u) - seq h j + seq h (j + u) - 1) := by
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_range] at hj
    rcases seq_sign hs (show j < n by omega) with e1 | e1 <;>
      rcases seq_sign hs (show j + u < n by omega) with e2 | e2 <;>
      rw [e1, e2] <;> norm_num
  have h2 : (4 : ℤ) ∣ ∑ i ∈ range u,
      (seq h i * seq h (i + v) - seq h (i + v) + seq h i - 1) := by
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rcases seq_sign hs (show i < n by omega) with e1 | e1 <;>
      rcases seq_sign hs (show i + v < n by omega) with e2 | e2 <;>
      rw [e1, e2] <;> norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h1 h2
  have e1 := pa_split (seq h) v u
  have e2 := pa_split (seq h) u v
  rw [show v + u = n by omega] at e1
  rw [show u + v = n by omega] at e2
  omega

/-- For odd `n` and a Barker sequence, every even nontrivial shift has autocorrelation
`(-1)^((n-1)/2)`. -/
theorem even_shift_eq {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Odd n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = (-1) ^ ((n - 1) / 2) := by
  have hv : Odd (n - k) := by
    obtain ⟨a, ha⟩ := hn
    obtain ⟨b, hb2⟩ := hk
    exact ⟨a - b, by omega⟩
  have hz := odd_shift_zero hb hn (n - k) hv (by omega) (by omega)
  have hd := aperiodic_add_aperiodic_sub_mod_four hb.1 hk0 hkn
  rw [hz] at hd
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨m, hm⟩ := hn
  have hm2 : (n - 1) / 2 = m := by omega
  rw [hm2]
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow]
    obtain ⟨t, ht⟩ := he
    omega
  · rw [ho.neg_one_pow]
    obtain ⟨t, ht⟩ := ho
    omega

/-- The Challenge's `aperiodic_eq`. -/
theorem aperiodic_eq_internal {n : ℕ} (h : Fin n → ℤ) (hn : Odd n) (hb : IsBarker h) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = if Even k then (-1) ^ ((n - 1) / 2) else 0 := by
  split_ifs with he
  · exact even_shift_eq hb hn he hk0 hkn
  · exact odd_shift_zero hb hn k (Nat.not_even_iff_odd.mp he) hk0 hkn

/-- For even `n` and a Barker sequence, every even nontrivial shift has autocorrelation `0`
(parity: `C(k) ≡ n - k ≡ 0 (mod 2)` and `|C(k)| ≤ 1`). -/
theorem even_shift_zero_of_even {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n) {k : ℕ}
    (hk : Even k) (hk0 : 0 < k) (hkn : k < n) :
    aperiodic h k = 0 := by
  have hp := aperiodic_parity hb.1 hkn.le
  have hb' := abs_le.mp (hb.2 k hk0 hkn)
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb2⟩ := hk
  omega

end OddBarker

open Finset

namespace OddBarker

/-- The Challenge's `four_dvd_of_even`. -/
theorem four_dvd_of_even_internal {n : ℕ} (h : Fin n → ℤ) (hn : Even n) (h2 : 2 < n)
    (hb : IsBarker h) : 4 ∣ n := by
  have hk2 : aperiodic h 2 = 0 :=
    even_shift_zero_of_even hb hn (k := 2) even_two (by omega) h2
  have hev : Even (n - 2) := by
    obtain ⟨u, hu⟩ := hn
    exact ⟨u - 1, by omega⟩
  have hkn : aperiodic h (n - 2) = 0 :=
    even_shift_zero_of_even hb hn (k := n - 2) hev (by omega) (by omega)
  have hd := aperiodic_add_aperiodic_sub_mod_four hb.1 (u := 2) (by omega) h2
  rw [hk2, hkn, add_zero, zero_sub, dvd_neg] at hd
  exact_mod_cast hd

/-- The periodic autocorrelation at shift `a` (the definition of `openai/math`'s `Barker/Model.lean`,
adapted). -/
def periodic {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) : ℤ :=
  ∑ j : Fin n, h j * h (j - a)

theorem periodic_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ} (hs : ∀ j, IsSign (h j)) :
    periodic h 0 = n := by
  unfold periodic
  have : ∀ j : Fin n, h j * h j = 1 := by
    intro j
    rcases hs j with h1 | h1 <;> rw [h1] <;> norm_num
  simp only [sub_zero, this]
  simp

/-- `periodic h a = C(a) + C(n - a)` for `a ≠ 0` (the wraparound split). Adapts
`periodic_eq_aperiodic_add` of openai/math lean/OAI/LinearAlgebra/Barker/Wraparound.lean. -/
theorem periodic_eq_aperiodic_add {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) (ha : a ≠ 0) :
    periodic h a = aperiodic h a.val + aperiodic h (n - a.val) := by
  have ha_le : a.val ≤ n := Nat.le_of_lt a.isLt
  have hn : a.val + (n - a.val) = n := Nat.add_sub_of_le ha_le
  let f : Fin n → ℤ := fun j => h j * h (j - a)
  have split := Fin.sum_univ_add
    (fun j : Fin (a.val + (n - a.val)) => f (j.cast hn))
  rw [Fin.sum_congr' f hn] at split
  have low :
      (∑ j : Fin a.val, f ((Fin.castAdd (n - a.val) j).cast hn)) =
        aperiodic h (n - a.val) := by
    have hc : n - (n - a.val) = a.val := by omega
    have reindex : aperiodic h (n - a.val) =
        ∑ j : Fin a.val,
          h ⟨j.val, by omega⟩ * h ⟨j.val + (n - a.val), by omega⟩ := by
      unfold aperiodic
      apply Fintype.sum_equiv (finCongr hc)
      intro j
      rfl
    rw [reindex]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : ((Fin.castAdd (n - a.val) j).cast hn - a) =
        (⟨j.val + (n - a.val), by omega⟩ : Fin n) := by
      apply Fin.ext
      have hlt : (Fin.castAdd (n - a.val) j).cast hn < a := by
        change j.val < a.val
        exact j.isLt
      rw [Fin.coe_sub_iff_lt.mpr hlt]
      dsimp only [Fin.val_cast, Fin.val_castAdd]
      omega
    change h ((Fin.castAdd (n - a.val) j).cast hn) *
        h ((Fin.castAdd (n - a.val) j).cast hn - a) = _
    rw [hsub]
    rfl
  have high :
      (∑ j : Fin (n - a.val), f ((Fin.natAdd a.val j).cast hn)) =
        aperiodic h a.val := by
    unfold aperiodic
    apply Finset.sum_congr rfl
    intro j _
    have hsub : ((Fin.natAdd a.val j).cast hn - a) =
        (⟨j.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      have hle : a ≤ (Fin.natAdd a.val j).cast hn := by
        change a.val ≤ a.val + j.val
        omega
      rw [Fin.sub_val_of_le hle]
      dsimp only [Fin.val_cast, Fin.val_natAdd]
      omega
    change h ((Fin.natAdd a.val j).cast hn) *
        h ((Fin.natAdd a.val j).cast hn - a) = _
    rw [hsub, mul_comm]
    congr 1
    apply congrArg h
    apply Fin.ext
    change a.val + j.val = j.val + a.val
    omega
  change (∑ j : Fin n, f j) = _
  rw [split, low, high, add_comm]

/-- The periodic autocorrelation vanishes off the peak for an even Barker sequence of length `> 2`. Adapts
`periodic_offpeak_zero` of openai/math lean/OAI/LinearAlgebra/Barker/Main.lean. -/
theorem periodic_offpeak_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n)
    (h2 : 2 < n) (a : Fin n) (ha : a ≠ 0) : periodic h a = 0 := by
  have ha0 : 0 < a.val := by
    by_contra hnot
    apply ha
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hab := abs_le.mp (hb.2 a.val ha0 a.isLt)
  have hac := abs_le.mp (hb.2 (n - a.val) (by omega) (by omega))
  have hp := periodic_eq_aperiodic_add h a ha
  obtain ⟨u, hu⟩ := aperiodic_add_aperiodic_sub_mod_four hb.1 ha0 a.isLt
  obtain ⟨v, hv⟩ := four_dvd_of_even_internal h hn h2 hb
  have hv' : (n : ℤ) = 4 * v := by exact_mod_cast hv
  omega

/-- The circulant matrix of `h`: `circ h i j = h (j - i)`. -/
def circ {n : ℕ} (h : Fin n → ℤ) : RealMatrix n := fun i j => (h (j - i) : ℝ)

theorem circ_isCirculant {n : ℕ} (h : Fin n → ℤ) : IsCirculant (circ h) := by
  exact ⟨fun x => (h x : ℝ), fun i j => rfl⟩

theorem circ_isSignHadamard {n : ℕ} {h : Fin n → ℤ} (hb : IsBarker h) (hn : Even n) (h2 : 2 < n) :
    IsSignHadamard (circ h) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · intro i j
    rcases hb.1 (j - i) with h1 | h1 <;> simp [circ, h1, IsSign]
  · ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, circ]
    have key : ∑ k, (h (k - i) : ℝ) * (h (k - j) : ℝ) = ((periodic h (j - i) : ℤ) : ℝ) := by
      unfold periodic
      push_cast
      apply Fintype.sum_equiv (Equiv.subRight i)
      intro k
      simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]
    rw [key]
    by_cases hij : i = j
    · subst hij
      simp [periodic_zero hb.1]
    · have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
      simp [periodic_offpeak_zero hb hn h2 _ hji, hij]

/-- The Challenge's `existsRealCirculantHadamard_of_even`. -/
theorem existsRealCirculantHadamard_of_even_internal {n : ℕ} (h : Fin n → ℤ) (hn : Even n)
    (h2 : 2 < n) (hb : IsBarker h) : ExistsRealCirculantHadamard n := by
  exact ⟨circ h, circ_isCirculant h, circ_isSignHadamard hb hn h2⟩


end OddBarker
namespace BarkerList

/-- Convert the list specification into the indexed autocorrelation used by Schmidt and Willms. -/
theorem aperiodic_eq_fin (a : List ℤ) (k : ℕ) :
    aperiodicAutocorrelation a k = OddBarker.aperiodic a.get k := by
  have h : a.zipWith (· * ·) (a.drop k) = List.ofFn (fun j : Fin (a.length - k) =>
      a[j.val]'(Nat.lt_of_lt_of_le j.isLt (Nat.sub_le _ _)) *
      a[j.val+k]'(Nat.add_lt_of_lt_sub j.isLt)) := by
    apply List.ext_getElem
    · simp [Nat.min_eq_right (Nat.sub_le a.length k)]
    · intro i hi hj
      simp [List.getElem_zipWith, List.getElem_drop, Nat.add_comm]
  simp only [aperiodicAutocorrelation, h, List.sum_ofFn, OddBarker.aperiodic, List.get_eq_getElem]

theorem indexed_barker (a : List ℤ) (ha : IsBarkerSequence a) : OddBarker.IsBarker a.get := by
  refine ⟨fun j => ha.1 _ (List.get_mem a j), fun k hk hkl => ?_⟩
  rw [← aperiodic_eq_fin]
  exact ha.2 k hk hkl

end BarkerList

end BarkerEven

-- OAI.LinearAlgebra.CirculantHadamard.Model
section
namespace BarkerOrderPort

namespace CirculantHadamard

universe u

def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def IsCirculant {n : ℕ} (H : RealMatrix n) : Prop :=
  ∃ h : Fin n → ℝ, ∀ i j, H i j = h (j - i)

def IsSignHadamard {n : ℕ} (H : RealMatrix n) : Prop :=
  (∀ i j, IsSign (H i j)) ∧
    H * H.transpose = (n : ℝ) • (1 : RealMatrix n)

def ExistsRealCirculantHadamard (n : ℕ) : Prop :=
  ∃ H : RealMatrix n, IsCirculant H ∧ IsSignHadamard H

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.Basic
section
namespace BarkerOrderPort

universe uR

namespace CirculantHadamard

def rowCirculant {n : ℕ} {R : Type uR} (h : Fin n → R) :
    Matrix (Fin n) (Fin n) R := fun i j => h (j - i)

@[simp] theorem rowCirculant_apply {n : ℕ} {R : Type uR}
    (h : Fin n → R) (i j : Fin n) : rowCirculant h i j = h (j - i) := rfl

theorem rowCirculant_isCirculant {n : ℕ} (h : Fin n → ℝ) :
    IsCirculant (rowCirculant h) := ⟨h, fun _ _ => rfl⟩

@[simp] theorem rowCirculant_zero_row {n : ℕ} [NeZero n]
    {R : Type uR} (h : Fin n → R) (j : Fin n) : rowCirculant h 0 j = h j := by
  simp [rowCirculant]

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.MatrixBridge
section
namespace BarkerOrderPort

universe uR


namespace CirculantHadamard

open scoped BigOperators

variable {n : ℕ}

/-- An integer sign row with the full Hadamard Gram equation. -/
def IsIntegerSignRow (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧
    rowCirculant h * (rowCirculant h).transpose =
      (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- The Gram entry at `(i,a)` is the cyclic autocorrelation at `a-i`. -/
theorem rowCirculant_gram_apply [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by
  classical
  let e : Fin n ≃ Fin n :=
    { toFun := fun j => j - i
      invFun := fun j => j + i
      left_inv := fun j => sub_add_cancel j i
      right_inv := fun j => add_sub_cancel_right j i }
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant_apply]
  apply Fintype.sum_equiv e
  intro j
  change h (j - i) * h (j - a) = h (j - i) * h ((j - i) - (a - i))
  simp only [sub_sub_sub_cancel_right]

/-- The full Gram equation is exactly the cyclic autocorrelation system. -/
theorem gram_eq_iff_autocorrelation [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) :
    rowCirculant h * (rowCirculant h).transpose =
        (n : R) • (1 : Matrix (Fin n) (Fin n) R) ↔
      ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : R) else 0 := by
  classical
  constructor
  · intro hGram a
    have ha := congrArg (fun M : Matrix (Fin n) (Fin n) R => M 0 a) hGram
    rw [rowCirculant_gram_apply] at ha
    simpa [Matrix.smul_apply, Matrix.one_apply, eq_comm] using ha
  · intro hCorr
    ext i a
    rw [rowCirculant_gram_apply, hCorr]
    by_cases hia : i = a
    · subst a
      simp
    · have hai : a - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hia)
      simp [hia, hai, Matrix.smul_apply]

/-- Casting the integer Gram matrix agrees entry by entry with taking the
Gram matrix after casting the row. -/
theorem intCast_gram_apply (h : Fin n → ℤ) (i j : Fin n) :
    ((rowCirculant h * (rowCirculant h).transpose) i j : ℝ) =
      (rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose) i j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant, Int.cast_sum,
    Int.cast_mul]

private theorem MatrixBridge_intCast_scaled_identity_apply (i j : Fin n) :
    (((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℝ) =
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
  by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]

/-- The real coefficient embedding preserves and reflects the entire Gram
identity, including the diagonal value. -/
theorem gram_intCast_iff (h : Fin n → ℤ) :
    rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose =
        (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  constructor
  · intro hGram
    ext i j
    apply Int.cast_injective (α := ℝ)
    rw [intCast_gram_apply, MatrixBridge_intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hGram
  · intro hGram
    ext i j
    rw [← intCast_gram_apply, ← MatrixBridge_intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hGram

/-- Every integer sign row gives the actual real circulant Hadamard matrix. -/
theorem IsIntegerSignRow.exists_real {h : Fin n → ℤ} (hh : IsIntegerSignRow h) :
    ExistsRealCirculantHadamard n := by
  refine ⟨rowCirculant (fun a => (h a : ℝ)), rowCirculant_isCirculant _, ?_,
    (gram_intCast_iff h).mpr hh.2⟩
  intro i j
  rcases hh.1 (j - i) with hpos | hneg
  · left
    simp only [rowCirculant_apply, hpos, Int.cast_one]
  · right
    simp only [rowCirculant_apply, hneg, Int.cast_neg, Int.cast_one]

/-- A real sign matrix determines an integer sign row without approximation. -/
theorem ExistsRealCirculantHadamard.exists_integerSignRow [NeZero n]
    (hH : ExistsRealCirculantHadamard n) : ∃ h : Fin n → ℤ, IsIntegerSignRow h := by
  classical
  rcases hH with ⟨H, ⟨h, hrow⟩, hsign, hGram⟩
  have hsignRow : ∀ j, IsSign (h j) := by
    intro j
    simpa only [hrow, sub_zero] using hsign 0 j
  let z : Fin n → ℤ := fun j => if h j = 1 then 1 else -1
  have hzcast : ∀ j, (z j : ℝ) = h j := by
    intro j
    by_cases hj : h j = 1
    · simp [z, hj]
    · have hneg := (hsignRow j).resolve_left hj
      simp only [z, if_neg hj, Int.cast_neg, Int.cast_one, hneg]
  have hzsign : ∀ j, IsSign (z j) := by
    intro j
    dsimp [z, IsSign]
    split_ifs <;> simp
  have hzH : rowCirculant (fun j => (z j : ℝ)) = H := by
    ext i j
    rw [rowCirculant_apply, hzcast, hrow]
  refine ⟨z, hzsign, (gram_intCast_iff z).mp ?_⟩
  simpa only [hzH] using hGram

/-- Equivalence between the public real matrix problem and integer sign rows. -/
theorem integerSignRow_iff_real [NeZero n] :
    (∃ h : Fin n → ℤ, IsIntegerSignRow h) ↔ ExistsRealCirculantHadamard n := by
  constructor
  · rintro ⟨h, hh⟩
    exact hh.exists_real
  · exact ExistsRealCirculantHadamard.exists_integerSignRow

/-- A direct integer autocorrelation presentation of the real matrix problem. -/
theorem existsReal_iff_integer_autocorrelation [NeZero n] :
    ExistsRealCirculantHadamard n ↔
      ∃ h : Fin n → ℤ, (∀ j, IsSign (h j)) ∧
        ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : ℤ) else 0 := by
  rw [← integerSignRow_iff_real]
  simp only [IsIntegerSignRow, gram_eq_iff_autocorrelation]

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicRing
section
namespace BarkerOrderPort

universe uR uG

/-! The finite cyclic group ring, with coefficient conjugation and index reversal. -/

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

abbrev Elem (R : Type uR) [Semiring R] (n : ℕ) := AddMonoidAlgebra R (ZMod n)

noncomputable def groupStar {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) : AddMonoidAlgebra R G :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun a => star (f.coeff (-a)))

@[simp] theorem groupStar_apply {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) (a : G) :
    (groupStar f).coeff a = star (f.coeff (-a)) := rfl

@[simp] theorem groupStar_groupStar {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) :
    groupStar (groupStar f) = f := by
  ext a
  simp

@[simp] theorem groupStar_single {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (a : G) (r : R) :
    groupStar (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) (star r) := by
  classical
  ext b
  change star (Finsupp.single a r (-b)) = Finsupp.single (-a) (star r) b
  by_cases hb : b = -a
  · subst b
    simp
  · have hab : a ≠ -b := by
      intro h
      apply hb
      simpa using (congrArg (fun x : G => -x) h).symm
    simp [hab, Ne.symm hb]

noncomputable def ofCoeffs {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (c : ZMod n → R) : Elem R n :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)

@[simp] theorem ofCoeffs_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (c : ZMod n → R) (a : ZMod n) : (ofCoeffs c).coeff a = c a := rfl

@[simp] theorem ofCoeffs_coeffs {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f : Elem R n) : ofCoeffs (fun a => f.coeff a) = f := by
  exact AddMonoidAlgebra.coeff_injective (Finsupp.ext fun _ => rfl)

noncomputable def scalar {R : Type uR} [Semiring R] (n : ℕ) (r : R) : Elem R n :=
  AddMonoidAlgebra.single 0 r

@[simp] theorem scalar_apply {R : Type uR} [Semiring R] {n : ℕ}
    (r : R) (a : ZMod n) : (scalar n r).coeff a = if a = 0 then r else 0 := by
  classical
  simp [scalar, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

@[simp] theorem scalar_natCast {R : Type uR} [Semiring R] (n m : ℕ) :
    scalar n (m : R) = (m : Elem R n) := rfl

noncomputable def ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : Elem R n :=
  ofCoeffs fun a => star (f.coeff (-a))

@[simp] theorem ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (ringStar f).coeff a = star (f.coeff (-a)) := rfl

theorem ringStar_eq_groupStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStar f = groupStar f := rfl

@[simp] theorem ringStar_single {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (a : ZMod n) (r : R) :
    ringStar (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) (star r) :=
  groupStar_single a r

section Convolution

variable {R : Type uR} {G : Type uG} [Semiring R] [AddCommGroup G] [Fintype G]

theorem group_mul_apply (f g : AddMonoidAlgebra R G) (a : G) :
    (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) := by
  classical
  calc
    (f * g).coeff a = f.coeff.sum (fun j r => r * g.coeff (-j + a)) :=
      AddMonoidAlgebra.coeff_mul_apply_left f g a
    _ = ∑ j, f.coeff j * g.coeff (-j + a) := Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
    _ = _ := by simp only [sub_eq_add_neg, add_comm]

theorem group_mul_apply_right (f g : AddMonoidAlgebra R G) (a : G) :
    (f * g).coeff a = ∑ j, f.coeff (a - j) * g.coeff j := by
  classical
  calc
    (f * g).coeff a = g.coeff.sum (fun j r => f.coeff (a - j) * r) := by
      simpa only [sub_eq_add_neg] using AddMonoidAlgebra.coeff_mul_apply_right f g a
    _ = _ := Finsupp.sum_fintype _ _ (fun _ => mul_zero _)

@[simp] theorem groupStar_zero [StarRing R] :
    groupStar (0 : AddMonoidAlgebra R G) = 0 := by
  ext a
  simp

@[simp] theorem groupStar_add [StarRing R] (f g : AddMonoidAlgebra R G) :
    groupStar (f + g) = groupStar f + groupStar g := by
  ext a
  change star (f.coeff (-a) + g.coeff (-a)) = star (f.coeff (-a)) + star (g.coeff (-a))
  exact star_add _ _

@[simp] theorem groupStar_one [StarRing R] :
    groupStar (1 : AddMonoidAlgebra R G) = 1 := by
  classical
  ext a
  simp [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem groupStar_mul [StarRing R] (f g : AddMonoidAlgebra R G) :
    groupStar (f * g) = groupStar g * groupStar f := by
  ext a
  rw [groupStar_apply, group_mul_apply_right, star_sum, group_mul_apply]
  apply Fintype.sum_equiv (Equiv.neg G)
  intro j
  simp only [star_mul, groupStar_apply, Equiv.neg_apply, neg_neg]
  congr 2
  congr 1
  abel

end Convolution

theorem mul_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f g : Elem R n) (a : ZMod n) : (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) :=
  group_mul_apply f g a

theorem mul_apply_right {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f g : Elem R n) (a : ZMod n) : (f * g).coeff a = ∑ j, f.coeff (a - j) * g.coeff j :=
  group_mul_apply_right f g a

@[simp] theorem ringStar_ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStar (ringStar f) = f :=
  groupStar_groupStar f

@[simp] theorem ringStar_zero {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] : ringStar (0 : Elem R n) = 0 := groupStar_zero

@[simp] theorem ringStar_add {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f g : Elem R n) : ringStar (f + g) = ringStar f + ringStar g :=
  groupStar_add f g

@[simp] theorem ringStar_one {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] : ringStar (1 : Elem R n) = 1 := groupStar_one

theorem ringStar_mul {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f g : Elem R n) :
    ringStar (f * g) = ringStar g * ringStar f := groupStar_mul f g

@[simp] theorem ringStar_scalar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (r : R) : ringStar (scalar n r) = scalar n (star r) := by
  classical
  ext a
  by_cases ha : a = 0 <;> simp [scalar_apply, ha]

theorem mul_ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (f * ringStar f).coeff a = ∑ j, f.coeff j * star (f.coeff (j - a)) := by
  simp only [mul_apply, ringStar_apply, neg_sub]

noncomputable def groupStarRingHom {R : Type uR} {G : Type uG} [CommSemiring R] [StarRing R]
    [AddCommGroup G] [Fintype G] : AddMonoidAlgebra R G →+* AddMonoidAlgebra R G where
  toFun := groupStar
  map_zero' := groupStar_zero
  map_one' := groupStar_one
  map_add' := groupStar_add
  map_mul' f g := by rw [groupStar_mul, mul_comm]

noncomputable def ringStarRingHom {R : Type uR} [CommSemiring R] [StarRing R]
    (n : ℕ) [NeZero n] : Elem R n →+* Elem R n := groupStarRingHom

@[simp] theorem ringStarRingHom_apply {R : Type uR} [CommSemiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStarRingHom n f = ringStar f := rfl

noncomputable def augmentation {R : Type uR} [Semiring R] (n : ℕ) : Elem R n →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R) 1 (fun _ _ => Commute.one_right _)

theorem augmentation_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f : Elem R n) : augmentation n f = ∑ a, f.coeff a := by
  change f.coeff.sum (fun _ r => r * 1) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp

@[simp] theorem augmentation_scalar {R : Type uR} [Semiring R] (n : ℕ) (r : R) :
    augmentation n (scalar n r) = r := by
  change AddMonoidAlgebra.liftNC (RingHom.id R).toAddMonoidHom
    (1 : Multiplicative (ZMod n) →* R) (AddMonoidAlgebra.single 0 r) = r
  simp

theorem augmentation_ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) :
    augmentation n (ringStar f) = star (augmentation n f) := by
  simp only [augmentation_apply, ringStar_apply, star_sum]
  exact Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun _ => rfl)

theorem augmentation_norm_star {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (r : R)
    (h : f * ringStar f = scalar n r) :
    augmentation n f * star (augmentation n f) = r := by
  have he := congrArg (augmentation n) h
  simpa only [map_mul, augmentation_ringStar, augmentation_scalar] using he

theorem augmentation_norm {n : ℕ} [NeZero n] (f : Elem ℤ n) (r : ℤ)
    (h : f * ringStar f = scalar n r) : (augmentation n f) ^ 2 = r := by
  simpa only [star_trivial, pow_two] using augmentation_norm_star f r h

end CirculantHadamard.CyclicRing

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicNorm
section
namespace BarkerOrderPort

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every literal integer coefficient is a sign. -/
def CyclicSignRow {n : ℕ} (f : CyclicRing.Elem ℤ n) : Prop :=
  ∀ a, IsSign (f.coeff a)

section PositiveOrder

variable {n : ℕ} [NeZero n]

/-- The cyclic group-ring element whose coefficients are the given first row. -/
def cyclicRow (h : Fin n → ℤ) : CyclicRing.Elem ℤ n :=
  CyclicRing.ofCoeffs (fun a => h ((ZMod.finEquiv n).symm a))

/-- Recover the integer first row without changing the cyclic orientation. -/
def integerRow (f : CyclicRing.Elem ℤ n) : Fin n → ℤ :=
  fun j => f.coeff (ZMod.finEquiv n j)

@[simp] theorem cyclicRow_apply (h : Fin n → ℤ) (a : ZMod n) :
    (cyclicRow h).coeff a = h ((ZMod.finEquiv n).symm a) := by
  simp [cyclicRow]

@[simp] theorem integerRow_apply (f : CyclicRing.Elem ℤ n) (j : Fin n) :
    integerRow f j = f.coeff (ZMod.finEquiv n j) := rfl

@[simp] theorem cyclicRow_integerRow (f : CyclicRing.Elem ℤ n) :
    cyclicRow (integerRow f) = f := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  simp [integerRow]

@[simp] theorem integerRow_cyclicRow (h : Fin n → ℤ) :
    integerRow (cyclicRow h) = h := by
  funext j
  simp [integerRow]

theorem sum_cyclicRow (h : Fin n → ℤ) :
    (∑ a : ZMod n, (cyclicRow h).coeff a) = ∑ j : Fin n, h j := by
  simpa only [cyclicRow_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    RingEquiv.symm_apply_apply] using
    ((ZMod.finEquiv n).toEquiv.sum_comp (fun a : ZMod n => (cyclicRow h).coeff a)).symm

theorem cyclicSignRow_cyclicRow_iff (h : Fin n → ℤ) :
    CyclicSignRow (cyclicRow h) ↔ ∀ j, IsSign (h j) := by
  constructor
  · intro hf j
    simpa using hf (ZMod.finEquiv n j)
  · intro hh a
    simpa using hh ((ZMod.finEquiv n).symm a)

/-- The norm coefficient uses the same `j - a` orientation as the row Gram. -/
theorem cyclicRow_norm_apply (h : Fin n → ℤ) (a : Fin n) :
    (cyclicRow h * CyclicRing.ringStar (cyclicRow h)).coeff (ZMod.finEquiv n a) =
      ∑ j : Fin n, h j * h (j - a) := by
  rw [CyclicRing.mul_ringStar_apply]
  simpa only [cyclicRow_apply, map_sub, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply, star_trivial] using
    ((ZMod.finEquiv n).toEquiv.sum_comp
      (fun j : ZMod n =>
        (cyclicRow h).coeff j * star ((cyclicRow h).coeff (j - ZMod.finEquiv n a)))).symm

theorem cyclicRow_norm_iff_autocorrelation (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      ∀ a : Fin n, (∑ j : Fin n, h j * h (j - a)) =
        if a = 0 then (n : ℤ) else 0 := by
  constructor
  · intro hn a
    have ha := congrArg
      (fun f : CyclicRing.Elem ℤ n => f.coeff (ZMod.finEquiv n a)) hn
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using ha
  · intro hh
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro x
    obtain ⟨a, rfl⟩ := (ZMod.finEquiv n).surjective x
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using hh a

theorem cyclicRow_norm_iff_gram (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) :=
  (cyclicRow_norm_iff_autocorrelation h).trans (gram_eq_iff_autocorrelation h).symm

theorem integerSignRow_iff_cyclicSignNorm (h : Fin n → ℤ) :
    IsIntegerSignRow h ↔
      CyclicSignRow (cyclicRow h) ∧
        cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
          CyclicRing.scalar n (n : ℤ) := by
  exact and_congr (cyclicSignRow_cyclicRow_iff h).symm (cyclicRow_norm_iff_gram h).symm

/-- The literal sign norm equation is equivalent to the public real-matrix
existence predicate.  Neither direction assumes a mathematical bridge. -/
theorem exists_cyclicSignRow_iff_real :
    (∃ f : CyclicRing.Elem ℤ n,
      CyclicSignRow f ∧ f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) ↔
      ExistsRealCirculantHadamard n := by
  rw [← integerSignRow_iff_real]
  constructor
  · rintro ⟨f, hf, hn⟩
    refine ⟨integerRow f, (integerSignRow_iff_cyclicSignNorm _).2 ?_⟩
    simpa only [cyclicRow_integerRow] using And.intro hf hn
  · rintro ⟨h, hh⟩
    exact ⟨cyclicRow h, (integerSignRow_iff_cyclicSignNorm h).1 hh⟩

/-- The identity coefficient is the sum of the actual coefficient squares. -/
theorem cyclicNorm_identity_coeff (f : CyclicRing.Elem ℤ n) :
    (f * CyclicRing.ringStar f).coeff 0 = ∑ a : ZMod n, f.coeff a ^ 2 := by
  simp [CyclicRing.mul_ringStar_apply, pow_two]

theorem cyclicSignRow_identity_coeff (f : CyclicRing.Elem ℤ n)
    (hf : CyclicSignRow f) : (f * CyclicRing.ringStar f).coeff 0 = (n : ℤ) := by
  rw [cyclicNorm_identity_coeff]
  calc
    (∑ a : ZMod n, f.coeff a ^ 2) = ∑ _a : ZMod n, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      rcases hf a with ha | ha <;> simp [ha]
    _ = (n : ℤ) := by simp

/-- Evaluating the actual cyclic norm at the trivial character gives the
square of the coefficient sum. -/
theorem augmentation_sum_sq_of_norm (f : CyclicRing.Elem ℤ n)
    (hf : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    (∑ a : ZMod n, f.coeff a) ^ 2 = (n : ℤ) := by
  simpa only [CyclicRing.augmentation_apply] using
    CyclicRing.augmentation_norm f (n : ℤ) hf

end PositiveOrder

end CirculantHadamard

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.OrderSquareEven
section
namespace BarkerOrderPort

universe uIota


namespace CirculantHadamard

open scoped BigOperators

private theorem OrderSquareEven_positive_nat_square_of_int_square {n : ℕ} (hn : 0 < n)
    (z : ℤ) (hz : z ^ 2 = (n : ℤ)) :
    ∃ m : ℕ, 0 < m ∧ n = m ^ 2 := by
  have hsq : z.natAbs ^ 2 = n := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using congrArg Int.natAbs hz
  have hm : z.natAbs ≠ 0 := by
    intro hm
    have hzero : n = 0 := by simpa only [hm, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hsq.symm
    exact (Nat.ne_of_gt hn) hzero
  exact ⟨z.natAbs, Nat.pos_of_ne_zero hm, hsq.symm⟩

private theorem OrderSquareEven_even_card_of_sign_sum_zero {ι : Type uIota} [Fintype ι]
    (f : ι → ℤ) (hsign : ∀ i, IsSign (f i)) (hsum : ∑ i, f i = 0) :
    Even (Fintype.card ι) := by
  classical
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hcast (i : ι) : φ (f i) = 1 := by
    rcases hsign i with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
      exact ZMod.neg_eq_self_mod_two (1 : ZMod 2)
  have hcard : (Fintype.card ι : ZMod 2) = 0 := by
    have h := congrArg φ hsum
    simpa only [map_sum, hcast, map_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using h
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hcard)

/-- A nonidentity norm coefficient is a zero sum of exactly `n` signs. -/
theorem order_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    Even n := by
  classical
  let : Fact (1 < n) := ⟨hn⟩
  have hcorr : (∑ a : ZMod n, f.coeff a * f.coeff (a - 1)) = 0 := by
    have h := congrArg (fun g : CyclicRing.Elem ℤ n => g.coeff 1) hnorm
    simpa only [CyclicRing.mul_ringStar_apply, star_trivial, CyclicRing.scalar_apply,
      if_neg (one_ne_zero : (1 : ZMod n) ≠ 0)] using h
  have heven := OrderSquareEven_even_card_of_sign_sum_zero (fun a : ZMod n => f.coeff a * f.coeff (a - 1))
    (fun a => by
      rcases hsign a with ha | ha <;> rcases hsign (a - 1) with hb | hb <;>
        simp [IsSign, ha, hb]) hcorr
  simpa only [ZMod.card] using heven

/-- Square and even order from the actual integer sign norm equation. -/
theorem order_square_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    (∃ m : ℕ, 0 < m ∧ n = m ^ 2) ∧ Even n := by
  constructor
  · exact OrderSquareEven_positive_nat_square_of_int_square (lt_trans Nat.zero_lt_one hn)
      (CyclicRing.augmentation n f) (CyclicRing.augmentation_norm f (n : ℤ) hnorm)
  · exact order_even_of_sign_norm hn f hsign hnorm

/-- A nontrivial actual real circulant sign Hadamard matrix has positive
square order and even order. The integer row and its norm identity are
obtained from the proved matrix correspondence. -/
theorem order_square_even {n : ℕ} (hn : 1 < n)
    (h : ExistsRealCirculantHadamard n) :
    (∃ m : ℕ, 0 < m ∧ n = m ^ 2) ∧ Even n := by
  let : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  obtain ⟨f, hsign, hnorm⟩ := exists_cyclicSignRow_iff_real.mpr h
  exact order_square_even_of_sign_norm hn f hsign hnorm

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.TwoAdicDecomposition
section
namespace BarkerOrderPort


namespace CirculantHadamard

/-- Extract the two-adic part from a specified positive square root. -/
theorem exists_two_adic_square_decomposition_of_eq_sq {n m : ℕ}
    (hm : 0 < m) (hnm : n = m ^ 2) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by
  obtain ⟨s, u, hu, hroot⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  have hmEven : Even m := (Nat.even_pow.mp (hnm ▸ heven)).1
  have hs : s ≠ 0 := by
    intro hs0
    have hmu : m = u := by simpa only [hs0, pow_zero, one_mul] using hroot
    exact (Nat.not_even_iff_odd.mpr hu) (hmu ▸ hmEven)
  have huPos : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro hu0
    have hm0 : m = 0 := by simpa only [hu0, mul_zero] using hroot
    exact hm.ne' hm0
  refine ⟨s, u, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs), huPos, hu, ?_⟩
  rw [hnm, hroot, mul_pow, ← pow_mul, Nat.mul_comm s 2]

/-- Every positive even natural square has a positive odd part and a
nonzero, even power of two. -/
theorem exists_two_adic_square_decomposition {n : ℕ}
    (hn : 0 < n) (hsquare : IsSquare n) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by
  obtain ⟨m, hnm⟩ := hsquare.exists_sq
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm0
    have hn0 : n = 0 := by simpa only [hm0, zero_pow (by decide : 2 ≠ 0)] using hnm
    exact hn.ne' hn0
  exact exists_two_adic_square_decomposition_of_eq_sq hm hnm heven

/-- Interface for an order theorem that already supplies its positive root. -/
theorem exists_two_adic_square_decomposition_of_positive_square {n : ℕ}
    (hsquare : ∃ m : ℕ, 0 < m ∧ n = m ^ 2) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by
  obtain ⟨m, hm, hnm⟩ := hsquare
  exact exists_two_adic_square_decomposition_of_eq_sq hm hnm heven

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicProjection
section
namespace BarkerOrderPort

universe uR uS


noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [Semiring R] {m n l : ℕ}

/-- The quotient of cyclic group rings induced by reduction of indices. -/
def cyclicProjection (h : m ∣ n) : Elem R n →+* Elem R m :=
  AddMonoidAlgebra.mapDomainRingHom R (ZMod.castHom h (ZMod m)).toAddMonoidHom

variable {R}

theorem cyclicProjection_apply (h : m ∣ n) (F : Elem R n) :
    cyclicProjection R h F = AddMonoidAlgebra.mapDomain (ZMod.castHom h (ZMod m)) F := rfl

@[simp] theorem cyclicProjection_single (h : m ∣ n) (a : ZMod n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single (ZMod.castHom h (ZMod m) a) r :=
  AddMonoidAlgebra.mapDomain_single

@[simp] theorem cyclicProjection_single_zero (h : m ∣ n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r := by
  simp

@[simp] theorem cyclicProjection_scalar (h : m ∣ n) (r : R) :
    cyclicProjection R h (scalar n r) = scalar m r := by
  exact cyclicProjection_single_zero h r

@[simp] theorem cyclicProjection_generator (h : m ∣ n) :
    cyclicProjection R h (AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1 := by
  simp only [cyclicProjection_single, map_one]

@[simp] theorem cyclicProjection_single_natCast (h : m ∣ n) (a : ℕ) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single (a : ZMod n) r) =
      AddMonoidAlgebra.single (a : ZMod m) r := by
  simp

@[simp] theorem cyclicProjection_self (F : Elem R n) :
    cyclicProjection R (dvd_refl n) F = F := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (ZMod.castHom (dvd_refl n) (ZMod n)) F.coeff = F.coeff
  simp [ZMod.castHom_self]

theorem cyclicProjection_comp (h₁ : l ∣ m) (h₂ : m ∣ n) (F : Elem R n) :
    cyclicProjection R h₁ (cyclicProjection R h₂ F) =
      cyclicProjection R (dvd_trans h₁ h₂) F := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (ZMod.castHom h₁ (ZMod l))
      (Finsupp.mapDomain (ZMod.castHom h₂ (ZMod m)) F.coeff) =
    Finsupp.mapDomain (ZMod.castHom (dvd_trans h₁ h₂) (ZMod l)) F.coeff
  rw [← Finsupp.mapDomain_comp]
  have hcomp : (ZMod.castHom h₁ (ZMod l) : ZMod m → ZMod l) ∘
      (ZMod.castHom h₂ (ZMod m) : ZMod n → ZMod m) =
      (ZMod.castHom (dvd_trans h₁ h₂) (ZMod l) : ZMod n → ZMod l) :=
    congrArg (fun f : ZMod n →+* ZMod l => (f : ZMod n → ZMod l))
      (ZMod.castHom_comp h₁ h₂)
  rw [hcomp]

/-- Any additive coefficient evaluation factors through the quotient exactly
when its index function is pulled back along reduction. -/
theorem sum_cyclicProjection {S : Type uS} [AddCommMonoid S]
    (h : m ∣ n) (F : Elem R n) (v : ZMod m → R →+ S) :
    (cyclicProjection R h F).coeff.sum (fun a r => v a r) =
      F.coeff.sum (fun a r => v (ZMod.castHom h (ZMod m) a) r) :=
  Finsupp.sum_mapDomain_index_addMonoidHom v

/-- Evaluation at the trivial character is unchanged by the cyclic quotient. -/
@[simp] theorem augmentation_cyclicProjection (h : m ∣ n) (F : Elem R n) :
    augmentation m (cyclicProjection R h F) = augmentation n F := by
  change (cyclicProjection R h F).coeff.sum (fun _ r => r * 1) =
    F.coeff.sum (fun _ r => r * 1)
  simp only [mul_one]
  exact sum_cyclicProjection h F (fun _ => AddMonoidHom.id R)

section Star

variable [StarRing R] [NeZero m] [NeZero n]

/-- Quotienting the indices commutes with conjugation and index reversal. -/
@[simp] theorem cyclicProjection_ringStar (h : m ∣ n) (F : Elem R n) :
    cyclicProjection R h (ringStar F) = ringStar (cyclicProjection R h F) := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change cyclicProjection R h (ringStar ((F : Elem R n) + G)) =
      ringStar (cyclicProjection R h ((F : Elem R n) + G))
    calc
      _ = cyclicProjection R h (ringStar F + ringStar G) :=
        congrArg (cyclicProjection R h) (ringStar_add F G)
      _ = cyclicProjection R h (ringStar F) + cyclicProjection R h (ringStar G) :=
        (cyclicProjection R h).map_add _ _
      _ = ringStar (cyclicProjection R h F) + ringStar (cyclicProjection R h G) :=
        congrArg₂ (· + ·) hF hG
      _ = ringStar (cyclicProjection R h F + cyclicProjection R h G) :=
        (ringStar_add _ _).symm
      _ = _ := congrArg ringStar ((cyclicProjection R h).map_add F G).symm
  · intro a r
    simp only [ringStar_single, cyclicProjection_single, map_neg]

/-- A scalar convolution norm descends to the quotient cyclic group. -/
theorem cyclicProjection_norm (h : m ∣ n) {F : Elem R n} {r : R}
    (hnorm : F * ringStar F = scalar n r) :
    cyclicProjection R h F * ringStar (cyclicProjection R h F) = scalar m r := by
  have hq := congrArg (cyclicProjection R h) hnorm
  simpa only [map_mul, cyclicProjection_ringStar, cyclicProjection_scalar] using hq

end Star

end CirculantHadamard

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.ProjectionPairFiber
section
namespace BarkerOrderPort


namespace CirculantHadamard

/-- The fiber of reduction modulo `m` consists of its two canonical lifts. -/
theorem zmod_double_cast_eq_iff {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (x : ZMod (2 * m)) (j : ZMod m) :
    ZMod.castHom h (ZMod m) x = j ↔
      x = (j.val : ZMod (2 * m)) ∨ x = ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero (2 * m) := ⟨by omega⟩
  have hxlt : x.val < 2 * m := ZMod.val_lt x
  have hjlt : j.val < m := ZMod.val_lt j
  constructor
  · intro hx
    have hmod : x.val % m = j.val := by
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] using
        congrArg ZMod.val hx
    by_cases hsmall : x.val < m
    · left
      have hval : x.val = j.val := by
        simpa only [Nat.mod_eq_of_lt hsmall] using hmod
      rw [← hval, ZMod.natCast_zmod_val]
    · right
      have hmle : m ≤ x.val := by omega
      have hsub : x.val - m < m := by omega
      rw [Nat.mod_eq_sub_mod hmle, Nat.mod_eq_of_lt hsub] at hmod
      have hval : x.val = j.val + m := by omega
      rw [← hval, ZMod.natCast_zmod_val]
  · rintro (rfl | rfl)
    · simp only [map_natCast, ZMod.natCast_zmod_val]
    · rw [map_natCast]
      simp only [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]

/-- The two canonical lifts into the group of twice the order are distinct. -/
theorem zmod_double_lifts_ne {m : ℕ} (hm : 0 < m) (j : ZMod m) :
    (j.val : ZMod (2 * m)) ≠ ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  have hjlt : j.val < m := ZMod.val_lt j
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show j.val < 2 * m by omega),
    Nat.mod_eq_of_lt (show j.val + m < 2 * m by omega)] at hv
  omega

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.ProjectionCoefficients
section
namespace BarkerOrderPort

universe uA uB uR


namespace CirculantHadamard

open scoped BigOperators

section Fiber

variable {A : Type uA} {B : Type uB} {R : Type uR} [Fintype A] [DecidableEq B] [AddCommMonoid R]

/-- Mapping the domain adds precisely the coefficients in a quotient fiber. -/
theorem mapDomain_apply_sum (q : A → B) (f : A →₀ R) (b : B) :
    Finsupp.mapDomain q f b = ∑ a ∈ Finset.univ.filter (fun a => q a = b), f a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.single_apply, Finset.sum_filter]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hzero : f a = 0 := Finsupp.notMem_support_iff.mp ha
  simp [hzero]

/-- The same coefficient formula, indexed by the subtype of the fiber. -/
theorem mapDomain_apply_fiber (q : A → B) (f : A →₀ R) (b : B) :
    Finsupp.mapDomain q f b = ∑ a : {a : A // q a = b}, f a.val := by
  classical
  rw [mapDomain_apply_sum]
  exact Finset.sum_subtype _ (by intro a; simp) _

end Fiber

section Cyclic

variable {R : Type uR} [Semiring R]

/-- Coefficients of the actual cyclic group-ring quotient as a finite filter sum. -/
theorem cyclicProjection_apply_sum {m n : ℕ} [NeZero n] (h : m ∣ n)
    (f : CyclicRing.Elem R n) (a : ZMod m) :
    (cyclicProjection R h f).coeff a =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod n =>
        ZMod.castHom h (ZMod m) x = a), f.coeff x := by
  change Finsupp.mapDomain (ZMod.castHom h (ZMod m)) f.coeff a = _
  exact mapDomain_apply_sum _ _ _

/-- Coefficients of the actual cyclic group-ring quotient as a fiber subtype sum. -/
theorem cyclicProjection_apply_fiber {m n : ℕ} [NeZero n] (h : m ∣ n)
    (f : CyclicRing.Elem R n) (a : ZMod m) :
    (cyclicProjection R h f).coeff a =
      ∑ x : {x : ZMod n // ZMod.castHom h (ZMod m) x = a}, f.coeff x.val := by
  change Finsupp.mapDomain (ZMod.castHom h (ZMod m)) f.coeff a = _
  exact mapDomain_apply_fiber _ _ _

/-- A quotient by the subgroup of order two adds opposite coefficients. -/
theorem cyclicProjection_double_apply {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (f : CyclicRing.Elem R (2 * m)) (j : ZMod m) :
    (cyclicProjection R h f).coeff j =
      f.coeff (j.val : ZMod (2 * m)) + f.coeff ((j.val + m : ℕ) : ZMod (2 * m)) := by
  classical
  let : NeZero (2 * m) := ⟨(Nat.mul_pos (by decide) hm).ne'⟩
  rw [cyclicProjection_apply_sum]
  refine Finset.sum_eq_add_of_mem _ _ ?_ ?_ (zmod_double_lifts_ne hm j) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (zmod_double_cast_eq_iff hm h _ j).mpr (Or.inl rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (zmod_double_cast_eq_iff hm h _ j).mpr (Or.inr rfl)
  · intro x hx hne
    have hx' := (Finset.mem_filter.mp hx).2
    rcases (zmod_double_cast_eq_iff hm h x j).mp hx' with hxj | hxj
    · exact (hne.1 hxj).elim
    · exact (hne.2 hxj).elim

end Cyclic

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.OrderProjection
section
namespace BarkerOrderPort

universe uα


noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every fiber of reduction modulo a divisor has the exact quotient size. -/
theorem cyclic_reduction_fiber_card {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (a : ZMod m) :
    Fintype.card {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a} = d := by
  classical
  let q : ZMod n →+ ZMod m := (ZMod.castHom hdiv (ZMod m)).toAddMonoidHom
  have hsurj : Function.Surjective q := by
    intro b
    refine ⟨(b.val : ZMod n), ?_⟩
    change ZMod.castHom hdiv (ZMod m) (b.val : ZMod n) = b
    simp only [map_natCast, ZMod.natCast_zmod_val]
  have hcards (b : ZMod m) :
      (Finset.univ.filter (fun x : ZMod n => q x = b)).card =
        (Finset.univ.filter (fun x : ZMod n => q x = a)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range q (hsurj b) (hsurj a)
  have htotal : n = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
    calc
      n = (Finset.univ : Finset (ZMod n)).card := by simp
      _ = ∑ b : ZMod m, (Finset.univ.filter (fun x : ZMod n => q x = b)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
        simp only [hcards, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  rw [Fintype.card_subtype]
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos m) (htotal.symm.trans hn)

/-- An odd finite family of actual integer signs has odd sum. -/
theorem odd_sum_of_signs {α : Type uα} [Fintype α] (f : α → ℤ)
    (hf : ∀ x, IsSign (f x)) (hcard : Odd (Fintype.card α)) :
    Odd (∑ x, f x) := by
  classical
  apply Int.odd_iff.mpr
  have hmod (x : α) : f x % 2 = 1 := by
    rcases hf x with hx | hx <;> norm_num [hx]
  calc
    (∑ x, f x) % 2 = (∑ _x : α, (1 : ℤ)) % 2 := by
      rw [Finset.sum_int_mod]
      simp only [hmod]
    _ = (Fintype.card α : ℤ) % 2 := by simp
    _ = 1 := Int.odd_iff.mp ((Int.odd_coe_nat _).mpr hcard)

/-- The actual quotient coefficient is odd because its fiber consists of
exactly the specified odd number of original signs. -/
theorem cyclicProjection_odd_coefficients {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (hd : Odd d)
    (f : CyclicRing.Elem ℤ n) (hf : CyclicSignRow f) (a : ZMod m) :
    Odd ((cyclicProjection ℤ hdiv f).coeff a) := by
  classical
  rw [cyclicProjection_apply_fiber]
  apply odd_sum_of_signs
    (α := {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a})
    (fun x => f.coeff x.val) (fun x => hf x.val)
  rw [cyclic_reduction_fiber_card hdiv hn a]
  exact hd

/-- First projection in the order reduction: every coefficient is odd and
the scalar on the right of the norm equation remains the original order. -/
theorem exists_odd_cyclic_projection {n s u : ℕ} [NeZero n]
    (hu : Odd u) (heq : n = 2 ^ (2 * s) * u ^ 2)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    ∃ T : CyclicRing.Elem ℤ (2 ^ (2 * s)),
      (∀ a, Odd (T.coeff a)) ∧
        T * CyclicRing.ringStar T =
          CyclicRing.scalar _ ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ) := by
  let : NeZero (2 ^ (2 * s)) := ⟨pow_ne_zero _ (by decide)⟩
  have hdiv : 2 ^ (2 * s) ∣ n := ⟨u ^ 2, heq⟩
  refine ⟨cyclicProjection ℤ hdiv f, ?_, ?_⟩
  · exact cyclicProjection_odd_coefficients hdiv heq hu.pow f hsign
  · calc
      _ = CyclicRing.scalar _ (n : ℤ) := cyclicProjection_norm hdiv hnorm
      _ = CyclicRing.scalar _ ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ) := by rw [heq]

end CirculantHadamard

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.IntegerLocalDivisibility
section
namespace BarkerOrderPort

universe uA


namespace CirculantHadamard

/-- Divisibility by a rational prime power in its actual integer localization
implies the same divisibility in the integers. -/
theorem integer_prime_pow_dvd_of_localization
    {A : Type uA} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) (hx : (p : A) ^ t ∣ algebraMap ℤ A x) :
    (p : ℤ) ^ t ∣ x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl y
  have hinj : Function.Injective (algebraMap ℤ A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  have hclear : x * (s : ℤ) = (p : ℤ) ^ t * a := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_natCast, hy, mul_assoc, hs]
  have hsprime : ¬ (p : ℤ) ∣ (s : ℤ) := by
    intro hdiv
    have hmem : (s : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
      Ideal.mem_span_singleton.mpr hdiv
    exact s.property (hP.symm ▸ hmem)
  exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right t hsprime
    ⟨a, hclear⟩

/-- Prime-power divisibility of integer coefficients is unchanged by
localization at that prime. -/
theorem integer_prime_pow_dvd_localization_iff
    {A : Type uA} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) :
    (p : A) ^ t ∣ algebraMap ℤ A x ↔ (p : ℤ) ^ t ∣ x := by
  constructor
  · exact integer_prime_pow_dvd_of_localization hp hP t x
  · intro hx
    simpa only [map_pow, map_natCast] using map_dvd (algebraMap ℤ A) hx

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.LocalDVR
section
namespace BarkerOrderPort

universe uR


noncomputable section

namespace CirculantHadamard.LocalDVR

open IsLocalRing IsDiscreteValuationRing

section PrincipalMaximalIdeal

variable {R : Type uR} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

/-- A nonzero generator of the maximal ideal of a Noetherian local domain
proves that the ring is a DVR. -/
theorem isDiscreteValuationRing_of_maximalIdeal_eq_span {π : R}
    (hπ : π ≠ 0) (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    IsDiscreteValuationRing R := by
  have hmax : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro hzero
    apply hπ
    exact Ideal.span_singleton_eq_bot.mp (hspan.symm.trans hzero)
  have hfield : ¬ IsField R := isField_iff_maximalIdeal_eq.not.mpr hmax
  have hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal := ⟨⟨π, hspan⟩⟩
  exact ((IsDiscreteValuationRing.TFAE R hfield).out 4 0).mp hprincipal

/-- The actual chosen generator factors every nonzero element into a unit
times a natural power. -/
theorem eq_unit_mul_pow_of_maximalIdeal_eq_span {π x : R}
    (hπ : π ≠ 0) (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), x = (u : R) * π ^ n := by
  let : IsDiscreteValuationRing R :=
    isDiscreteValuationRing_of_maximalIdeal_eq_span hπ hspan
  exact eq_unit_mul_pow_irreducible hx ((irreducible_iff_uniformizer π).mpr hspan)

end PrincipalMaximalIdeal

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Normalize the additive valuation using the concrete uniformizer relation. -/
theorem addVal_eq_of_unit_mul_uniformizer_pow {π p : R} {u : Rˣ} {D : ℕ}
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hp : p = (u : R) * π ^ D) :
    addVal R p = (D : ℕ∞) :=
  addVal_def p u ((irreducible_iff_uniformizer π).mpr hspan) D hp

/-- Right-unit version, convenient for the factorization of a rational prime. -/
theorem addVal_eq_of_uniformizer_pow_mul_unit {π p b : R} {D : ℕ}
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hb : IsUnit b)
    (hp : p = π ^ D * b) : addVal R p = (D : ℕ∞) := by
  obtain ⟨u, rfl⟩ := hb
  exact addVal_eq_of_unit_mul_uniformizer_pow hspan (hp.trans (mul_comm _ _))

private theorem LocalDVR_finite_add_eq {a b : ℕ∞} {N : ℕ} (h : a + b = (N : ℕ∞)) :
    ∃ m n : ℕ, a = (m : ℕ∞) ∧ b = (n : ℕ∞) ∧ m + n = N := by
  have ha : a ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_right zero_le
  have hb : b ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_left zero_le
  obtain ⟨m, hm, _⟩ := ENat.le_natCast_iff.mp ha
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp hb
  refine ⟨m, n, hm, hn, ?_⟩
  rw [hm, hn, ← Nat.cast_add] at h
  exact_mod_cast h

/-- If the valuation of a product is at least twice that of `p`, one factor
is divisible by `p`. The value of `p` is allowed to be ramified. -/
theorem dvd_or_dvd_of_mul_eq_pow_mul_unit {p x y b : R} {D e : ℕ}
    (_hp : p ≠ 0) (_hD : 0 < D) (hpval : addVal R p = (D : ℕ∞))
    (he : 2 ≤ e) (hb : IsUnit b) (hxy : x * y = p ^ e * b) :
    p ∣ x ∨ p ∣ y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, addVal_pow, hpval,
    addVal_eq_zero_iff.mpr hb, add_zero] at hv
  have hv' : addVal R x + addVal R y = ((e * D : ℕ) : ℕ∞) := by
    simpa only [nsmul_eq_mul, Nat.cast_mul] using hv
  obtain ⟨m, n, hm, hn, hmn⟩ := LocalDVR_finite_add_eq hv'
  have heD : 2 * D ≤ e * D := Nat.mul_le_mul_right D he
  have hsplit : D ≤ m ∨ D ≤ n := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_le_iff_dvd.mp
    rw [hpval, hm]
    exact_mod_cast hx
  · right
    apply addVal_le_iff_dvd.mp
    rw [hpval, hn]
    exact_mod_cast hy

/-- A product with valuation one has a unit factor. This is the unramified
base case of the integral division argument. -/
theorem isUnit_or_isUnit_of_mul_eq_uniformizer_mul_unit {p x y b : R}
    (hpval : addVal R p = 1) (hb : IsUnit b) (hxy : x * y = p * b) :
    IsUnit x ∨ IsUnit y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, hpval, addVal_eq_zero_iff.mpr hb, add_zero] at hv
  obtain ⟨m, n, hm, hn, hmn⟩ := LocalDVR_finite_add_eq (N := 1) hv
  have hsplit : m = 0 ∨ n = 0 := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_eq_zero_iff.mp
    simpa only [hx, Nat.cast_zero] using hm
  · right
    apply addVal_eq_zero_iff.mp
    simpa only [hy, Nat.cast_zero] using hn

end Valuation

end CirculantHadamard.LocalDVR

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.IntegerTwoLocal
section
namespace BarkerOrderPort


noncomputable section

namespace CirculantHadamard.IntegerTwoLocal

/-- The prime ideal `(2)` in the integers. -/
def ideal : Ideal ℤ := Ideal.span {(2 : ℤ)}

instance ideal_isPrime : ideal.IsPrime := by
  apply (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
  exact Nat.prime_iff_prime_int.mp Nat.prime_two

/-- The actual ring `ℤ_(2)`. -/
abbrev Ring := Localization.AtPrime ideal

/-- The localization has no zero divisors. -/
theorem isDomain : IsDomain Ring := inferInstance

/-- The complement-of-prime localization is local. -/
theorem isLocalRing : IsLocalRing Ring := inferInstance

/-- Integer coefficients embed faithfully in the concrete localization. -/
theorem algebraMap_injective : Function.Injective (algebraMap ℤ Ring) :=
  IsLocalization.injective Ring ideal.primeCompl_le_nonZeroDivisors

instance charZero : CharZero Ring :=
  charZero_of_injective_algebraMap algebraMap_injective

/-- Noetherianity is inherited from the integer ring by localization. -/
instance isNoetherianRing : IsNoetherianRing Ring :=
  IsLocalization.isNoetherianRing ideal.primeCompl Ring
    (inferInstance : IsNoetherianRing ℤ)

/-- The maximal ideal is exactly the principal ideal generated by two. -/
theorem maximalIdeal_eq_span :
    IsLocalRing.maximalIdeal Ring = Ideal.span {(2 : Ring)} := by
  calc
    IsLocalRing.maximalIdeal Ring = Ideal.map (algebraMap ℤ Ring) ideal :=
      (Localization.AtPrime.map_eq_maximalIdeal (I := ideal)).symm
    _ = Ideal.span {(2 : Ring)} := by
      simp only [ideal, Ideal.map_span, Set.image_singleton, map_ofNat]

theorem two_ne_zero : (2 : Ring) ≠ 0 := by norm_num

theorem two_not_isUnit : ¬ IsUnit (2 : Ring) := by
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, maximalIdeal_eq_span]
  exact Ideal.mem_span_singleton_self _

/-- The concrete localization is a discrete valuation ring with uniformizer
(two); this conclusion is obtained from its proved principal maximal ideal. -/
instance isDiscreteValuationRing : IsDiscreteValuationRing Ring :=
  LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span two_ne_zero
    maximalIdeal_eq_span

@[simp] theorem mem_ideal_iff_even (z : ℤ) : z ∈ ideal ↔ Even z := by
  simp only [ideal, Ideal.mem_span_singleton, even_iff_two_dvd]

/-- Exactly the odd integers become units. -/
theorem isUnit_algebraMap_iff_odd (z : ℤ) :
    IsUnit (algebraMap ℤ Ring z) ↔ Odd z := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff Ring ideal z]
  change z ∉ ideal ↔ Odd z
  rw [mem_ideal_iff_even, Int.not_even_iff_odd]

theorem isUnit_intCast_of_odd (z : ℤ) (hz : Odd z) : IsUnit (z : Ring) := by
  simpa using (isUnit_algebraMap_iff_odd z).mpr hz

theorem isUnit_natCast_of_odd (u : ℕ) (hu : Odd u) : IsUnit (u : Ring) := by
  simpa only [Int.cast_natCast] using
    isUnit_intCast_of_odd (u : ℤ) ((Int.odd_coe_nat u).mpr hu)

end CirculantHadamard.IntegerTwoLocal

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluation
section
namespace BarkerOrderPort

universe uR uS uT uA


noncomputable section

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]
variable {n : ℕ}

/-- Evaluation at a multiplicative character of the additive cyclic group. -/
def evaluate (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) : Elem R n →+* S :=
  AddMonoidAlgebra.liftNCRingHom φ χ (fun _ _ => Commute.all _ _)

@[simp] theorem evaluate_single (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (a : ZMod n) (r : R) :
    evaluate φ χ (AddMonoidAlgebra.single a r) = φ r * χ (Multiplicative.ofAdd a) :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

@[simp] theorem evaluate_scalar (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (r : R) :
    evaluate φ χ (scalar n r) = φ r := by
  simp only [scalar, evaluate_single]
  change φ r * χ 1 = φ r
  simp

/-- The full finite sum, rather than a sum over an unspecified support. -/
theorem evaluate_apply [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (f : Elem R n) :
    evaluate φ χ f = ∑ a : ZMod n, φ (f.coeff a) * χ (Multiplicative.ofAdd a) := by
  change f.coeff.sum (fun a r => φ r * χ (Multiplicative.ofAdd a)) = _
  exact Finsupp.sum_fintype f.coeff _ (fun _ => by simp)

@[simp] theorem evaluate_ofCoeffs [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (c : ZMod n → R) :
    evaluate φ χ (ofCoeffs c) = ∑ a : ZMod n, φ (c a) * χ (Multiplicative.ofAdd a) :=
  evaluate_apply φ χ (ofCoeffs c)

/-- The trivial character recovers augmentation followed by the coefficient map. -/
theorem evaluate_trivial_eq_augmentation [NeZero n] (φ : R →+* S)
    (f : Elem R n) :
    evaluate φ (1 : Multiplicative (ZMod n) →* S) f = φ (augmentation n f) := by
  simp [evaluate_apply, augmentation_apply, map_sum]

/-- Evaluation commutes with a change of target coefficient ring. -/
theorem map_evaluate [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (ψ : S →+* T) (f : Elem R n) :
    ψ (evaluate φ χ f) = evaluate (ψ.comp φ) (ψ.toMonoidHom.comp χ) f := by
  rw [evaluate_apply, evaluate_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact map_mul ψ (φ (f.coeff a)) (χ (Multiplicative.ofAdd a))

/-- Bundled naturality of character evaluation. -/
theorem map_evaluate_hom [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (ψ : S →+* T) :
    ψ.comp (evaluate φ χ) = evaluate (ψ.comp φ) (ψ.toMonoidHom.comp χ) := by
  apply RingHom.ext
  intro f
  exact map_evaluate φ χ ψ f

/-- A target endomorphism intertwines evaluation and the full group-ring star
when it intertwines the coefficient involution and character inversion. -/
theorem evaluate_ringStar_intertwining [StarRing R] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) (τ : S →+* S)
    (hφ : ∀ r, φ (star r) = τ (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = τ (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = τ (evaluate φ χ f) := by
  rw [evaluate_apply, evaluate_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ ?_
  intro a
  simp only [ringStar_apply, Equiv.neg_apply, map_mul, hφ]
  rw [← hχ]
  simp only [neg_neg]

/-- Character evaluation carries the full group-ring involution to target star. -/
theorem evaluate_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = star (evaluate φ χ f) :=
  evaluate_ringStar_intertwining φ χ (starRingEnd S) hφ hχ f

/-- The group-ring norm product becomes the usual star norm product. -/
theorem evaluate_mul_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (f * ringStar f) = evaluate φ χ f * star (evaluate φ χ f) := by
  rw [map_mul, evaluate_ringStar φ χ hφ hχ]

/-- A proved scalar group-ring norm equation transfers to every compatible
character; the norm equation is not built into the evaluation definition. -/
theorem evaluate_norm_eq [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) (r : R) (hf : f * ringStar f = scalar n r) :
    evaluate φ χ f * star (evaluate φ χ f) = φ r := by
  rw [← evaluate_mul_ringStar φ χ hφ hχ, hf, evaluate_scalar]

/-- For integer coefficients, coefficient-star compatibility is automatic. -/
theorem evaluate_int_ringStar {A : Type uA} [CommRing A] [StarRing A] [NeZero n]
    (χ : Multiplicative (ZMod n) →* A)
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem ℤ n) :
    evaluate (Int.castRingHom A) χ (ringStar f) =
      star (evaluate (Int.castRingHom A) χ f) := by
  exact evaluate_ringStar (Int.castRingHom A) χ (fun r => by simp) hχ f

end CirculantHadamard.CyclicRing

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial
section
namespace BarkerOrderPort

universe uR uA


noncomputable section

namespace CirculantHadamard.CyclicPolynomial

open Polynomial

variable (R : Type uR) [CommRing R] (n : ℕ)

/-- The defining polynomial of the cyclic group algebra. -/
def relation : R[X] := X ^ n - 1

/-- The basis element at the distinguished generator of the cyclic group. -/
def generator : AddMonoidAlgebra R (ZMod n) := AddMonoidAlgebra.single 1 1

theorem generator_pow : generator R n ^ n = 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul,
    AddMonoidAlgebra.one_def]

theorem root_pow : AdjoinRoot.root (relation R n) ^ n = 1 := by
  have h : AdjoinRoot.mk (relation R n) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_self (f := relation R n)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h

variable {R}

/-- A genuine cyclic character associated to an element whose `n`th power is one. -/
def powerCharacter {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) : Multiplicative (ZMod n) →* A where
  toFun a := x ^ a.toAdd.val
  map_one' := by
    change x ^ (0 : ZMod n).val = 1
    simp
  map_mul' a b := by
    change x ^ (a.toAdd + b.toAdd).val =
      x ^ a.toAdd.val * x ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

@[simp]
theorem powerCharacter_apply {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) (i : ZMod n) :
    powerCharacter n x hx (Multiplicative.ofAdd i) = x ^ i.val := rfl

@[simp]
theorem powerCharacter_generator {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) :
    powerCharacter n x hx (Multiplicative.ofAdd 1) = x := by
  change x ^ (1 : ZMod n).val = x
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]

variable (R)

/-- Send the cyclic basis element at `i` to the `i.val`th power of the root. -/
def toPolynomial [NeZero n] :
    AddMonoidAlgebra R (ZMod n) →ₐ[R] AdjoinRoot (relation R n) :=
  AddMonoidAlgebra.lift R (AdjoinRoot (relation R n)) (ZMod n)
    (powerCharacter n (AdjoinRoot.root (relation R n)) (root_pow R n))

@[simp]
theorem toPolynomial_single [NeZero n] (i : ZMod n) (r : R) :
    toPolynomial R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val := by
  simp [toPolynomial, Algebra.smul_def]

@[simp]
theorem toPolynomial_generator [NeZero n] :
    toPolynomial R n (generator R n) = AdjoinRoot.root (relation R n) := by
  simp only [generator, toPolynomial, AddMonoidAlgebra.lift_single,
    powerCharacter_generator, one_smul]

theorem generator_isRoot : aeval (generator R n) (relation R n) = 0 := by
  simp [relation, generator_pow]

/-- Evaluate the polynomial quotient at the actual cyclic group-ring generator. -/
def fromPolynomial :
    AdjoinRoot (relation R n) →ₐ[R] AddMonoidAlgebra R (ZMod n) :=
  AdjoinRoot.liftAlgHom (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_root :
    fromPolynomial R n (AdjoinRoot.root (relation R n)) = generator R n := by
  exact AdjoinRoot.liftAlgHom_root (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_mk (p : R[X]) :
    fromPolynomial R n (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p := by
  exact AdjoinRoot.liftAlgHom_mk (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n) p

theorem generator_pow_val [NeZero n] (i : ZMod n) :
    generator R n ^ i.val = AddMonoidAlgebra.single i 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul]

theorem toPolynomial_comp_fromPolynomial [NeZero n] :
    (toPolynomial R n).comp (fromPolynomial R n) =
      AlgHom.id R (AdjoinRoot (relation R n)) := by
  apply AdjoinRoot.algHom_ext
  simp

theorem fromPolynomial_comp_toPolynomial [NeZero n] :
    (fromPolynomial R n).comp (toPolynomial R n) =
      AlgHom.id R (AddMonoidAlgebra R (ZMod n)) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    simp [generator_pow_val]
  · exact Subsingleton.elim _ _

/-- The actual cyclic group algebra is the polynomial quotient by `X ^ n - 1`. -/
def cyclicEquiv [NeZero n] :
    AddMonoidAlgebra R (ZMod n) ≃ₐ[R] AdjoinRoot (relation R n) :=
  AlgEquiv.ofAlgHom (toPolynomial R n) (fromPolynomial R n)
    (toPolynomial_comp_fromPolynomial R n) (fromPolynomial_comp_toPolynomial R n)

@[simp]
theorem cyclicEquiv_single [NeZero n] (i : ZMod n) (r : R) :
    cyclicEquiv R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val :=
  toPolynomial_single R n i r

@[simp]
theorem cyclicEquiv_generator [NeZero n] :
    cyclicEquiv R n (generator R n) = AdjoinRoot.root (relation R n) :=
  toPolynomial_generator R n

@[simp]
theorem cyclicEquiv_symm_root [NeZero n] :
    (cyclicEquiv R n).symm (AdjoinRoot.root (relation R n)) = generator R n :=
  fromPolynomial_root R n

@[simp]
theorem cyclicEquiv_symm_mk [NeZero n] (p : R[X]) :
    (cyclicEquiv R n).symm (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p :=
  fromPolynomial_mk R n p

@[simp]
theorem cyclicEquiv_aeval [NeZero n] (p : R[X]) :
    cyclicEquiv R n (aeval (generator R n) p) =
      AdjoinRoot.mk (relation R n) p := by
  rw [← Polynomial.aeval_algHom_apply, cyclicEquiv_generator,
    AdjoinRoot.aeval_eq]

end CirculantHadamard.CyclicPolynomial

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.RamifiedConjugation
section
namespace BarkerOrderPort

universe uR uA


noncomputable section

namespace CirculantHadamard.RamifiedConjugation

open Polynomial IsDiscreteValuationRing

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Ring automorphisms of a DVR preserve its integer-valued order. -/
theorem addVal_ringEquiv (e : R ≃+* R) (x : R) :
    addVal R (e x) = addVal R x := by
  by_cases hx : x = 0
  · simp only [hx, map_zero]
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ
  have heπ : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have heu : e x = (Units.map e.toMonoidHom u : R) * (e π) ^ m := by
    simpa only [map_mul, map_pow, Units.coe_map,
      show e.toMonoidHom (u : R) = e (u : R) from rfl] using congrArg e hu
  rw [addVal_def x u hπ m hu,
    addVal_def (e x) (Units.map e.toMonoidHom u) heπ m heu]

private theorem RamifiedConjugation_enat_add_self_injective {a b : ℕ∞} (h : a + a = b + b) : a = b := by
  cases a using ENat.recTopCoe with
  | top =>
      cases b using ENat.recTopCoe with
      | top => rfl
      | coe b => simp only [← ENat.natCast_add, top_add, ENat.top_ne_natCast] at h
  | coe a =>
      cases b using ENat.recTopCoe with
      | top => simp only [← ENat.natCast_add, top_add, ENat.natCast_ne_top] at h
      | coe b =>
          have hab : a + a = b + b := ENat.natCast_inj.mp h
          have : a = b := by omega
          exact congrArg (fun n : ℕ => (n : ℕ∞)) this

/-- A norm with an even scalar exponent gives divisibility by half that
power. The statement includes zero and needs no normalization assumption
on the scalar's valuation. -/
theorem pow_dvd_of_norm_eq (e : R ≃+* R) (a x b : R) (t : ℕ)
    (hb : IsUnit b) (h : x * e x = a ^ (2 * t) * b) : a ^ t ∣ x := by
  have hsq : x * e x = (a ^ t * a ^ t) * b := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm t 2]
    exact h
  have hv := congrArg (addVal R) hsq
  have hbval : addVal R b = 0 := addVal_eq_zero_iff.mpr hb
  simp only [addVal_mul, addVal_ringEquiv, hbval, add_zero] at hv
  exact addVal_le_iff_dvd.mp (RamifiedConjugation_enat_add_self_injective hv).symm.le

end Valuation

section Cyclotomic

variable (A : Type uA) [CommRing A] (n : ℕ)

/-- The actual cyclotomic quotient used by the ramified construction. -/
abbrev CyclotomicRing := AdjoinRoot (cyclotomic n A)

/-- The adjoined root satisfies the stated order relation even before
domainhood or characteristic zero has been established. -/
theorem root_pow_order : AdjoinRoot.root (cyclotomic n A) ^ n = 1 := by
  have h : AdjoinRoot.mk (cyclotomic n A) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one n A)
  simpa only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] using h

variable [domain : IsDomain (CyclotomicRing A n)] [charZero : CharZero (CyclotomicRing A n)]


/-- The quotient root is a primitive root of the exact specified order. -/
theorem root_isPrimitiveRoot (hn : 0 < n) :
    IsPrimitiveRoot (AdjoinRoot.root (cyclotomic n A)) n := by
  apply (isRoot_cyclotomic_iff_charZero hn).mp
  simpa only [map_cyclotomic] using AdjoinRoot.isRoot_root (cyclotomic n A)

theorem root_pow_pred_mul_root (hn : 0 < n) :
    AdjoinRoot.root (cyclotomic n A) ^ (n - 1) *
      AdjoinRoot.root (cyclotomic n A) = 1 := by
  rw [← pow_succ, Nat.sub_add_cancel hn, root_pow_order]

private theorem RamifiedConjugation_inverse_root_aeval (hn : 0 < n) :
    aeval (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (cyclotomic n A) = 0 := by
  have hcoprime : (n - 1).Coprime n :=
    (Nat.coprime_self_sub_left hn).mpr (Nat.coprime_one_left n)
  have hroot :=
    ((root_isPrimitiveRoot A n hn).pow_of_coprime (n - 1) hcoprime).isRoot_cyclotomic hn
  rw [aeval_def, ← eval_map, map_cyclotomic]
  exact hroot

/-- The root-inverting endomorphism fixes the coefficient algebra. -/
def conjugationHom (hn : 0 < n) : CyclotomicRing A n →ₐ[A] CyclotomicRing A n :=
  AdjoinRoot.liftAlgHom (cyclotomic n A)
    (Algebra.ofId A (CyclotomicRing A n))
    (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (RamifiedConjugation_inverse_root_aeval A n hn)

@[simp] theorem conjugationHom_root (hn : 0 < n) :
    conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A)) =
      AdjoinRoot.root (cyclotomic n A) ^ (n - 1) := by
  exact AdjoinRoot.liftAlgHom_root (cyclotomic n A)
    (Algebra.ofId A (CyclotomicRing A n))
    (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (RamifiedConjugation_inverse_root_aeval A n hn)

theorem conjugationHom_comp_self (hn : 0 < n) :
    (conjugationHom A n hn).comp (conjugationHom A n hn) =
      AlgHom.id A (CyclotomicRing A n) := by
  apply AdjoinRoot.algHom_ext
  change conjugationHom A n hn
    (conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A))) =
      AdjoinRoot.root (cyclotomic n A)
  rw [conjugationHom_root]
  have hzero : AdjoinRoot.root (cyclotomic n A) ≠ 0 :=
    ((root_isPrimitiveRoot A n hn).isUnit (ne_of_gt hn)).ne_zero
  apply mul_right_cancel₀ (pow_ne_zero (n - 1) hzero)
  calc
    conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) *
        AdjoinRoot.root (cyclotomic n A) ^ (n - 1) =
      conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A) ^ (n - 1) *
        AdjoinRoot.root (cyclotomic n A)) := by rw [map_mul, conjugationHom_root]
    _ = 1 := by rw [root_pow_pred_mul_root A n hn, map_one]
    _ = AdjoinRoot.root (cyclotomic n A) *
        AdjoinRoot.root (cyclotomic n A) ^ (n - 1) := by
      simpa only [mul_comm] using (root_pow_pred_mul_root A n hn).symm

/-- The actual involutive algebra automorphism inverting the cyclotomic root. -/
def cyclotomicConjugation (hn : 0 < n) : CyclotomicRing A n ≃ₐ[A] CyclotomicRing A n :=
  AlgEquiv.ofAlgHom (conjugationHom A n hn) (conjugationHom A n hn)
    (conjugationHom_comp_self A n hn) (conjugationHom_comp_self A n hn)

@[simp] theorem cyclotomicConjugation_root (hn : 0 < n) :
    cyclotomicConjugation A n hn (AdjoinRoot.root (cyclotomic n A)) =
      AdjoinRoot.root (cyclotomic n A) ^ (n - 1) :=
  conjugationHom_root A n hn

theorem cyclotomicConjugation_involutive (hn : 0 < n) :
    Function.Involutive (cyclotomicConjugation A n hn) := by
  intro x
  exact DFunLike.congr_fun (conjugationHom_comp_self A n hn) x

variable [IsDiscreteValuationRing (CyclotomicRing A n)]

@[simp] theorem cyclotomicConjugation_addVal (hn : 0 < n) (x : CyclotomicRing A n) :
    addVal (CyclotomicRing A n) (cyclotomicConjugation A n hn x) =
      addVal (CyclotomicRing A n) x :=
  addVal_ringEquiv (cyclotomicConjugation A n hn).toRingEquiv x

theorem cyclotomic_pow_dvd_of_norm_eq (hn : 0 < n) (a x b : CyclotomicRing A n) (t : ℕ)
    (hb : IsUnit b)
    (h : x * cyclotomicConjugation A n hn x = a ^ (2 * t) * b) : a ^ t ∣ x :=
  pow_dvd_of_norm_eq (cyclotomicConjugation A n hn).toRingEquiv a x b t hb h

end Cyclotomic

end CirculantHadamard.RamifiedConjugation

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicIntegerEvaluation
section
namespace BarkerOrderPort

universe uA


noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]

/-- Integer cyclic group-ring evaluation in the actual cyclotomic quotient. -/
def integerCyclotomicEvaluation :
    CyclicRing.Elem ℤ n →+* AdjoinRoot (cyclotomic n A) :=
  CyclicRing.evaluate (Int.castRingHom (AdjoinRoot (cyclotomic n A)))
    (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
      (RamifiedConjugation.root_pow_order A n))

theorem integerCyclotomicEvaluation_apply (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      ∑ a : ZMod n, (T.coeff a : AdjoinRoot (cyclotomic n A)) *
        AdjoinRoot.root (cyclotomic n A) ^ a.val := by
  rw [integerCyclotomicEvaluation, CyclicRing.evaluate_apply]
  rfl

@[simp] theorem integerCyclotomicEvaluation_scalar (a : ℤ) :
    integerCyclotomicEvaluation A n (CyclicRing.scalar n a) =
      (a : AdjoinRoot (cyclotomic n A)) :=
  CyclicRing.evaluate_scalar _ _ a

variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]

/-- The actual character intertwines negation of its index and the proved
cyclotomic conjugation. -/
theorem cyclotomicPowerCharacter_neg (a : ZMod n) :
    CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
        (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd (-a)) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
          (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd a)) := by
  let χ := CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
    (RamifiedConjugation.root_pow_order A n)
  have hnonzero : χ (Multiplicative.ofAdd a) ≠ 0 :=
    pow_ne_zero a.val
      ((RamifiedConjugation.root_isPrimitiveRoot A n hn).isUnit (ne_of_gt hn)).ne_zero
  apply mul_right_cancel₀ hnonzero
  have hleft : χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) = 1 := by
    rw [← map_mul]
    change χ (Multiplicative.ofAdd (-a + a)) = 1
    simp
  change χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) =
    RamifiedConjugation.cyclotomicConjugation A n hn
      (χ (Multiplicative.ofAdd a)) * χ (Multiplicative.ofAdd a)
  rw [hleft]
  symm
  change RamifiedConjugation.cyclotomicConjugation A n hn
      (AdjoinRoot.root (cyclotomic n A) ^ a.val) *
    AdjoinRoot.root (cyclotomic n A) ^ a.val = 1
  rw [map_pow, RamifiedConjugation.cyclotomicConjugation_root, ← mul_pow,
    RamifiedConjugation.root_pow_pred_mul_root A n hn, one_pow]

/-- Evaluating the integer cyclic involution is exactly the cyclotomic
conjugate of the evaluated element. -/
theorem integerCyclotomicEvaluation_ringStar (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n (CyclicRing.ringStar T) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (integerCyclotomicEvaluation A n T) := by
  apply CyclicRing.evaluate_ringStar_intertwining
    (Int.castRingHom (AdjoinRoot (cyclotomic n A)))
    (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
      (RamifiedConjugation.root_pow_order A n))
    (RamifiedConjugation.cyclotomicConjugation A n hn).toRingHom
  · intro r
    simp
  · exact cyclotomicPowerCharacter_neg A n hn

/-- A proved scalar norm equation in the integer group ring transfers to
the actual cyclotomic norm equation. -/
theorem integerCyclotomicEvaluation_norm (T : CyclicRing.Elem ℤ n) (a : ℤ)
    (hT : T * CyclicRing.ringStar T = CyclicRing.scalar n a) :
    integerCyclotomicEvaluation A n T *
      RamifiedConjugation.cyclotomicConjugation A n hn
        (integerCyclotomicEvaluation A n T) =
      (a : AdjoinRoot (cyclotomic n A)) := by
  rw [← integerCyclotomicEvaluation_ringStar A n hn, ← map_mul, hT,
    integerCyclotomicEvaluation_scalar]

end CirculantHadamard

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicRemainder
section
namespace BarkerOrderPort

universe uR uS


noncomputable section

namespace CirculantHadamard.CyclotomicRemainder

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S] {f : R[X]}

/-- Scalar divisibility in a monic root extension gives a constant-polynomial
factor of the canonical remainder. -/
theorem C_dvd_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) :
    C a ∣ F %ₘ f := by
  obtain ⟨x, hx⟩ := hdiv
  refine ⟨h.modByMonicHom x, ?_⟩
  calc
    F %ₘ f = h.modByMonicHom (h.map F) := (h.modByMonicHom_map F).symm
    _ = h.modByMonicHom (a • x) := by rw [hx, Algebra.smul_def]
    _ = a • h.modByMonicHom x := h.modByMonicHom.map_smul a x
    _ = C a * h.modByMonicHom x := Polynomial.smul_eq_C_mul a

/-- A constant factor of the canonical remainder gives scalar divisibility
after passing to the monic root extension. -/
theorem dvd_map_of_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : C a ∣ F %ₘ f) :
    algebraMap R S a ∣ h.map F := by
  obtain ⟨G, hG⟩ := hdiv
  refine ⟨h.map G, ?_⟩
  calc
    h.map F = h.map (F %ₘ f) := (h.map_modByMonic F).symm
    _ = h.map (C a * G) := congrArg h.map hG
    _ = algebraMap R S a * h.map G := by rw [map_mul, ← h.algebraMap_apply]

/-- Exact divisibility equivalence for a monic root extension. -/
theorem map_dvd_iff_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ C a ∣ F %ₘ f :=
  ⟨C_dvd_modByMonic_of_dvd_map h a F, dvd_map_of_C_dvd_modByMonic h a F⟩

/-- Scalar divisibility is equivalent to divisibility of every coefficient
of the canonical remainder. -/
theorem map_dvd_iff_dvd_coeff_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ ∀ i, a ∣ (F %ₘ f).coeff i :=
  (map_dvd_iff_C_dvd_modByMonic h a F).trans (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Coefficient form of the forward divisibility bridge. -/
theorem dvd_coeff_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (map_dvd_iff_dvd_coeff_modByMonic h a F).mp hdiv i

/-- The actual quotient by a monic polynomial satisfies the constant-factor
criterion, using its concrete `IsAdjoinRootMonic` constructor. -/
theorem adjoinRoot_dvd_iff_C_dvd_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔ C a ∣ F %ₘ f := by
  simpa only [AdjoinRoot.isAdjoinRootMonic_toAdjoinRoot,
    AdjoinRoot.isAdjoinRoot_map_eq_mkₐ, AdjoinRoot.coe_mkₐ] using
    map_dvd_iff_C_dvd_modByMonic (AdjoinRoot.isAdjoinRootMonic f hf) a F

/-- The concrete monic quotient has scalar divisibility exactly when all
coefficients of the monic remainder have that scalar factor. -/
theorem adjoinRoot_dvd_iff_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔
      ∀ i, a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_C_dvd_modByMonic f hf a F).trans
    (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Scalar divisibility in a monic quotient implies coefficientwise
divisibility of the remainder. -/
theorem adjoinRoot_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X])
    (hdiv : algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_dvd_coeff_modByMonic f hf a F).mp hdiv i

end CirculantHadamard.CyclotomicRemainder

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.DyadicRemainder
section
namespace BarkerOrderPort

universe uR


noncomputable section

namespace CirculantHadamard.DyadicRemainder

open Polynomial Finset

variable {R : Type uR} [CommRing R]

/-- The polynomial with the first `n` entries of a coefficient function. -/
def coefficientPolynomial (n : ℕ) (c : ℕ → R) : R[X] :=
  ∑ i ∈ range n, monomial i (c i)

/-- The difference between coefficient blocks at distance `m`. -/
def remainder (m : ℕ) (c : ℕ → R) : R[X] :=
  coefficientPolynomial m (fun i => c i - c (i + m))

@[simp]
theorem coefficientPolynomial_coeff (n : ℕ) (c : ℕ → R) (j : ℕ) :
    (coefficientPolynomial n c).coeff j = if j < n then c j else 0 := by
  classical
  simp [coefficientPolynomial, coeff_monomial, Finsupp.single_apply]

theorem degree_coefficientPolynomial_lt (n : ℕ) (c : ℕ → R) :
    (coefficientPolynomial n c).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  simp only [coefficientPolynomial_coeff, if_neg (not_lt.mpr hj)]

theorem natDegree_coefficientPolynomial_lt {n : ℕ} (hn : 0 < n) (c : ℕ → R) :
    (coefficientPolynomial n c).natDegree < n := by
  by_cases hzero : coefficientPolynomial n c = 0
  · simpa only [hzero, natDegree_zero] using hn
  · exact (natDegree_lt_iff_degree_lt hzero).mpr (degree_coefficientPolynomial_lt n c)

@[simp]
theorem remainder_coeff (m : ℕ) (c : ℕ → R) (j : ℕ) (hj : j < m) :
    (remainder m c).coeff j = c j - c (j + m) := by
  simp only [remainder, coefficientPolynomial_coeff, if_pos hj]

theorem remainder_coeff_eq_zero (m : ℕ) (c : ℕ → R) (j : ℕ) (hj : m ≤ j) :
    (remainder m c).coeff j = 0 := by
  simp only [remainder, coefficientPolynomial_coeff, if_neg (not_lt.mpr hj)]

theorem degree_remainder_lt (m : ℕ) (c : ℕ → R) :
    (remainder m c).degree < (m : WithBot ℕ) :=
  degree_coefficientPolynomial_lt m _

theorem natDegree_remainder_lt {m : ℕ} (hm : 0 < m) (c : ℕ → R) :
    (remainder m c).natDegree < m :=
  natDegree_coefficientPolynomial_lt hm _

theorem remainder_eq_sub (m : ℕ) (c : ℕ → R) :
    remainder m c = coefficientPolynomial m c -
      coefficientPolynomial m (fun i => c (i + m)) := by
  simp only [remainder, coefficientPolynomial, monomial_sub, sum_sub_distrib]

/-- Split the coefficient polynomial into its lower and upper blocks. -/
theorem coefficientPolynomial_two_mul (m : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
      X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
  classical
  calc
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
        ∑ i ∈ range m, monomial (m + i) (c (m + i)) := by
      rw [two_mul]
      exact sum_range_add (fun i => monomial i (c i)) m m
    _ = coefficientPolynomial m c +
        X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
      congr 1
      simp only [coefficientPolynomial, mul_sum, X_pow_mul_monomial]
      apply sum_congr rfl
      intro i _
      rw [Nat.add_comm m i]

/-- The explicit quotient/remainder equation before applying monic division. -/
theorem remainder_add_mul (m : ℕ) (c : ℕ → R) :
    remainder m c + (X ^ m + 1) *
      coefficientPolynomial m (fun i => c (i + m)) = coefficientPolynomial (2 * m) c := by
  rw [remainder_eq_sub, add_mul, one_mul,
    add_comm (X ^ m * coefficientPolynomial m (fun i => c (i + m)))
      (coefficientPolynomial m (fun i => c (i + m))),
    ← add_assoc, sub_add_cancel]
  exact (coefficientPolynomial_two_mul m c).symm

/-- The canonical monic remainder is exactly the paired coefficient difference. -/
theorem coefficientPolynomial_modByMonic {m : ℕ} (hm : 0 < m) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c %ₘ (X ^ m + 1) = remainder m c := by
  nontriviality R
  have hmonic : (X ^ m + (1 : R[X])).Monic := by
    simpa only [C_1] using (monic_X_pow_add_C (1 : R) hm.ne')
  apply (div_modByMonic_unique
    (coefficientPolynomial m (fun i => c (i + m))) (remainder m c) hmonic ?_).2
  refine ⟨remainder_add_mul m c, ?_⟩
  have hdegree : (X ^ m + (1 : R[X])).degree = (m : WithBot ℕ) := by
    simpa only [C_1] using (degree_X_pow_add_C hm (1 : R))
  rw [hdegree]
  exact degree_remainder_lt m c

/-- Coefficients below the half-length in the canonical monic remainder. -/
theorem coefficientPolynomial_modByMonic_coeff {m : ℕ} (hm : 0 < m)
    (c : ℕ → R) (j : ℕ) (hj : j < m) :
    (coefficientPolynomial (2 * m) c %ₘ (X ^ m + 1)).coeff j = c j - c (j + m) := by
  rw [coefficientPolynomial_modByMonic hm, remainder_coeff m c j hj]

/-- The dyadic cyclotomic polynomial has the expected two terms. -/
theorem cyclotomic_two_pow_succ (R : Type uR) [CommRing R] (k : ℕ) :
    cyclotomic (2 ^ (k + 1)) R = (X : R[X]) ^ (2 ^ k) + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two, geom_sum_two]

/-- The remainder statement specialized to the dyadic cyclotomic polynomial. -/
theorem coefficientPolynomial_modByMonic_cyclotomic (k : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 ^ (k + 1)) c %ₘ cyclotomic (2 ^ (k + 1)) R =
      remainder (2 ^ k) c := by
  rw [cyclotomic_two_pow_succ, pow_succ, Nat.mul_comm (2 ^ k) 2]
  exact coefficientPolynomial_modByMonic (pow_pos (by decide : 0 < (2 : ℕ)) k) c

end CirculantHadamard.DyadicRemainder

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.RamifiedEisenstein
section
namespace BarkerOrderPort

universe uA uB


noncomputable section

namespace CirculantHadamard.RamifiedEisenstein

open Polynomial

/-- The prime-power cyclotomic polynomial translated to put the root at `ξ - 1`. -/
def shifted (A : Type uA) [CommRing A] (p k : ℕ) : A[X] :=
  (cyclotomic (p ^ (k + 1)) A).comp (X + 1)

theorem shifted_monic (A : Type uA) [CommRing A] (p k : ℕ) :
    (shifted A p k).Monic := by
  simpa only [shifted, C_1] using
    (cyclotomic.monic (p ^ (k + 1)) A).comp_X_add_C (1 : A)

theorem shifted_natDegree (A : Type uA) [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).natDegree = (p - 1) * p ^ k := by
  rw [shifted, natDegree_comp, show (X + 1 : A[X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one, natDegree_cyclotomic,
    Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem cyclotomic_natDegree (A : Type uA) [CommRing A] [Nontrivial A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (cyclotomic (p ^ (k + 1)) A).natDegree = (p - 1) * p ^ k := by
  rw [natDegree_cyclotomic, Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem shifted_coeff_zero (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).coeff 0 = (p : A) := by
  rw [shifted, coeff_zero_eq_eval_zero, eval_comp,
    cyclotomic_prime_pow_eq_geom_sum hp, eval_add, eval_X, eval_one, zero_add,
    eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range,
    Nat.smul_one_eq_cast]

theorem shifted_isWeaklyEisensteinAt (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).IsWeaklyEisensteinAt (Ideal.span {(p : A)}) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k).isWeaklyEisensteinAt.map
    (Int.castRingHom A)
  simpa [shifted, Ideal.submodule_span_eq, Ideal.map_span, Polynomial.map_comp] using h

section Local

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A] [IsLocalRing A]
  {p : ℕ}

theorem shifted_isEisensteinAt (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    (shifted A p k).IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpu : ¬ IsUnit (p : A) :=
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (p : A) hp0 hmax).not_isUnit
  apply (shifted_monic A p k).isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top inferInstance)
  · intro i hi
    rw [hmax]
    exact (shifted_isWeaklyEisensteinAt A hp k).mem hi
  · rw [shifted_coeff_zero A hp k, hmax, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro h
    have h21 : (2 : ℕ) ≤ 1 := (pow_dvd_pow_iff hp0 hpu).mp (by simpa using h)
    exact (by decide : ¬ (2 : ℕ) ≤ 1) h21

theorem shifted_irreducible (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : Irreducible (shifted A p k) := by
  apply (shifted_isEisensteinAt A hp k hmax).irreducible inferInstance
    (shifted_monic A p k).isPrimitive
  rw [shifted_natDegree A hp k]
  exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)

theorem cyclotomic_irreducible (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : Irreducible (cyclotomic (p ^ (k + 1)) A) := by
  apply (MulEquiv.irreducible_iff (Polynomial.algEquivAevalXAddC (1 : A))).mp
  change Irreducible ((cyclotomic (p ^ (k + 1)) A).comp (X + C (1 : A)))
  simpa only [shifted, C_1] using shifted_irreducible A hp k hmax

/-- Modulo the maximal ideal, the translated polynomial is exactly a pure power. -/
theorem mod_maximal_shifted (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    (shifted A p k).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) =
      (X : (A ⧸ IsLocalRing.maximalIdeal A)[X]) ^ ((p - 1) * p ^ k) := by
  ext i
  rw [coeff_map, coeff_X_pow]
  by_cases hi : i = (p - 1) * p ^ k
  · subst i
    rw [if_pos rfl, ← shifted_natDegree A hp k,
      (shifted_monic A p k).coeff_natDegree, map_one]
  · rw [if_neg hi]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (shifted_isEisensteinAt A hp k hmax).coeff_mem
    simpa only [shifted_natDegree A hp k] using hi

end Local

section DVR

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ}

theorem cyclotomic_prime (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : Prime (cyclotomic (p ^ (k + 1)) A) :=
  irreducible_iff_prime.mp (cyclotomic_irreducible A hp k hmax)

theorem cyclotomic_adjoinRoot_isDomain (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    IsDomain (AdjoinRoot (cyclotomic (p ^ (k + 1)) A)) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic_prime A hp k hmax)

/-- The minimal polynomial equality is for the actual primitive root in a
faithful domain extension, not merely for the formal quotient root. -/
theorem cyclotomic_eq_minpoly (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) {B : Type uB} [CommRing B] [IsDomain B]
    [Algebra A B] [NoZeroSMulDivisors A B] {ξ : B}
    (hξ : IsPrimitiveRoot ξ (p ^ (k + 1))) :
    cyclotomic (p ^ (k + 1)) A = minpoly A ξ := by
  have hroot : aeval ξ (cyclotomic (p ^ (k + 1)) A) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def]
    exact hξ.isRoot_cyclotomic (pow_pos hp.pos (k + 1))
  have hi : IsIntegral A ξ := ⟨_, cyclotomic.monic _ A, hroot⟩
  have hd : minpoly A ξ ∣ cyclotomic (p ^ (k + 1)) A :=
    minpoly.isIntegrallyClosed_dvd hi hroot
  exact Polynomial.eq_of_monic_of_associated (cyclotomic.monic _ A) (minpoly.monic hi)
    ((minpoly.irreducible hi).associated_of_dvd
      (cyclotomic_irreducible A hp k hmax) hd).symm

end DVR

end CirculantHadamard.RamifiedEisenstein

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.RamifiedUnit
section
namespace BarkerOrderPort

universe uR uS


noncomputable section

namespace CirculantHadamard.RamifiedUnit

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [IsDomain R]

/-- The polynomial form of the unit factor in an Eisenstein relation. -/
theorem exists_polynomial_unit_factor (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by
  have hdvd : C a ∣ f.eraseLead := by
    apply (C_dvd_iff_dvd_coeff _ _).2
    intro i
    by_cases hi : i = f.natDegree
    · simp [eraseLead_coeff, hi]
    · rw [eraseLead_coeff_of_ne _ hi]
      by_cases hilt : i < f.natDegree
      · exact hcoeff i hilt
      · rw [coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_ne (Nat.le_of_not_gt hilt) (Ne.symm hi))]
        exact dvd_zero a
  obtain ⟨q, hq⟩ := hdvd
  have hqzero : q.coeff 0 = 1 := by
    apply mul_left_cancel₀ ha
    have hh := congrArg (fun g : R[X] => g.coeff 0) hq
    simpa [eraseLead_coeff_of_ne _ (Nat.ne_of_lt hdeg), hzero] using hh.symm
  have hqrepr : 1 + X * q.divX = q := by
    simpa [hqzero, add_comm] using X_mul_divX_add q
  refine ⟨q.divX, ?_⟩
  calc
    f = f.eraseLead + X ^ f.natDegree := by
      simpa [hf] using (eraseLead_add_C_mul_X_pow f).symm
    _ = X ^ f.natDegree + C a * (1 + X * q.divX) := by
      rw [hq, hqrepr]
      exact add_comm _ _

variable [CommRing S] [Algebra R S] [IsLocalRing S]

/-- A root in the maximal ideal turns the normalized polynomial factor into
a unit, and therefore expresses the constant coefficient as a unit times
the ramified power. -/
theorem exists_unit_mul_root_pow (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by
  obtain ⟨q, hq⟩ := exists_polynomial_unit_factor f a ha hf hdeg hzero hcoeff
  have hrel : z ^ f.natDegree + algebraMap R S a * (1 + z * aeval z q) = 0 := by
    rw [hq] at hroot
    simpa only [map_add, map_mul, map_pow, aeval_X, map_one, aeval_C] using hroot
  have hn : -(z * aeval z q) ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.maximalIdeal S).neg_mem
      ((IsLocalRing.maximalIdeal S).mul_mem_right _ hz)
  have hu : IsUnit (1 + z * aeval z q) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(z * aeval z q)) hn
  obtain ⟨v, hv⟩ := hu
  have hpow : z ^ f.natDegree = -(algebraMap R S a * (v : S)) := by
    rw [← hv] at hrel
    exact eq_neg_of_add_eq_zero_left hrel
  refine ⟨-v⁻¹, ?_⟩
  rw [Units.val_neg, hpow, neg_mul_neg]
  calc
    algebraMap R S a = algebraMap R S a * ((v : S) * ↑v⁻¹) := by simp
    _ = ↑v⁻¹ * (algebraMap R S a * (v : S)) := by ac_rfl

end CirculantHadamard.RamifiedUnit

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.RamifiedLocal
section
namespace BarkerOrderPort

universe uA


noncomputable section

namespace CirculantHadamard.RamifiedLocal

open Polynomial

/-- The genuine monic cyclotomic quotient, with no additional ring-data premise. -/
abbrev Extension (A : Type uA) [CommRing A] (p k : ℕ) :=
  AdjoinRoot (cyclotomic (p ^ (k + 1)) A)

/-- The actual ramified parameter in the cyclotomic quotient. -/
def uniformizer (A : Type uA) [CommRing A] (p k : ℕ) : Extension A p k :=
  AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A) - 1

instance extensionFinite (A : Type uA) [CommRing A] (p k : ℕ) :
    Module.Finite A (Extension A p k) :=
  (cyclotomic.monic (p ^ (k + 1)) A).finite_adjoinRoot

theorem uniformizer_aeval_shifted (A : Type uA) [CommRing A] (p k : ℕ) :
    aeval (uniformizer A p k) (RamifiedEisenstein.shifted A p k) = 0 := by
  simp only [RamifiedEisenstein.shifted, aeval_comp, map_add, aeval_X, map_one,
    uniformizer, sub_add_cancel, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- Every element is a scalar modulo the actual root-minus-one parameter. -/
theorem exists_scalar_add_uniformizer_mul (A : Type uA) [CommRing A] (p k : ℕ)
    (x : Extension A p k) :
    ∃ a : A, ∃ b : Extension A p k,
      x = algebraMap A (Extension A p k) a + uniformizer A p k * b := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  have hroot : (q.map (algebraMap A (Extension A p k))).eval
      (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) =
      AdjoinRoot.mk (cyclotomic (p ^ (k + 1)) A) q := by
    rw [eval_map, ← aeval_def, AdjoinRoot.aeval_eq]
  have hone : (q.map (algebraMap A (Extension A p k))).eval 1 =
      algebraMap A (Extension A p k) (q.eval 1) := by
    rw [eval_map, eval₂_at_one]
  have hdiv := sub_dvd_eval_sub
    (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) (1 : Extension A p k)
    (q.map (algebraMap A (Extension A p k)))
  rw [hroot, hone] at hdiv
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨q.eval 1, b, ?_⟩
  change _ = _ + (AdjoinRoot.root _ - 1) * b
  rw [← hb]
  simp

theorem prime_mem_span_uniformizer (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p : Extension A p k) ∈ Ideal.span {uniformizer A p k} := by
  let : Fact p.Prime := ⟨hp⟩
  have hdiv := sub_dvd_eval_sub
    (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) (1 : Extension A p k)
    ((cyclotomic (p ^ (k + 1)) A).map (algebraMap A (Extension A p k)))
  have hdiv' : uniformizer A p k ∣ -(p : Extension A p k) := by
    simpa only [uniformizer, eval_map, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, eval₂_one_cyclotomic_prime_pow, zero_sub] using hdiv
  exact (Ideal.neg_mem_iff (Ideal.span {uniformizer A p k})).mp
    (Ideal.mem_span_singleton.mpr hdiv')

section LocalBase

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ}

theorem isDomain (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : IsDomain (Extension A p k) :=
  RamifiedEisenstein.cyclotomic_adjoinRoot_isDomain A hp k hmax

/-- Every maximal ideal of the genuine quotient is the same principal ideal. -/
theorem maximal_eq_span_uniformizer (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) (M : Ideal (Extension A p k)) [M.IsMaximal] :
    M = Ideal.span {uniformizer A p k} := by
  have hcomap : M.comap (algebraMap A (Extension A p k)) = Ideal.span {(p : A)} :=
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) M)).trans hmax
  have hmap : (Ideal.span {(p : A)}).map (algebraMap A (Extension A p k)) ≤ M := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [hcomap]
  have hpow := Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
      (RamifiedEisenstein.shifted_isWeaklyEisensteinAt A hp k)
      (uniformizer_aeval_shifted A p k) (RamifiedEisenstein.shifted_monic A p k)
      _ (le_refl _)
  have hpi : uniformizer A p k ∈ M :=
    (inferInstance : M.IsPrime).mem_of_pow_mem _ (hmap hpow)
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, hxform⟩ := exists_scalar_add_uniformizer_mul A p k x
    have haM : algebraMap A (Extension A p k) a ∈ M := by
      have hh := M.sub_mem hx (Ideal.mul_mem_right b M hpi)
      simpa [hxform] using hh
    have ha : a ∈ Ideal.span {(p : A)} := by
      rw [← hcomap]
      exact haM
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    have hap : algebraMap A (Extension A p k) a ∈
        Ideal.span {uniformizer A p k} := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ (prime_mem_span_uniformizer A hp k)
    rw [hxform]
    exact (Ideal.span {uniformizer A p k}).add_mem hap
      (Ideal.mul_mem_right b _ (Ideal.subset_span (Set.mem_singleton _)))
  · exact (Ideal.span_singleton_le_iff_mem M).mpr hpi

theorem isLocalRing (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : IsLocalRing (Extension A p k) := by
  let : IsDomain (Extension A p k) := isDomain A hp k hmax
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Extension A p k)
  let : M.IsMaximal := hM
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M, hM, ?_⟩
  intro N hN
  let : N.IsMaximal := hN
  exact (maximal_eq_span_uniformizer A hp k hmax N).trans
    (maximal_eq_span_uniformizer A hp k hmax M).symm

theorem maximalIdeal_eq_span (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] :
    IsLocalRing.maximalIdeal (Extension A p k) = Ideal.span {uniformizer A p k} :=
  maximal_eq_span_uniformizer A hp k hmax _

theorem root_residue_eq_one (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Extension A p k))
      (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Extension A p k))),
    ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change uniformizer A p k ∈ IsLocalRing.maximalIdeal (Extension A p k)
  rw [maximalIdeal_eq_span A hp k hmax]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem exists_unit_mul_uniformizer_pow (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] :
    ∃ u : (Extension A p k)ˣ,
      (p : Extension A p k) = (u : Extension A p k) *
        uniformizer A p k ^ ((p - 1) * p ^ k) := by
  have hd : 0 < (RamifiedEisenstein.shifted A p k).natDegree := by
    rw [RamifiedEisenstein.shifted_natDegree A hp k]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)
  have hcoeff : ∀ i < (RamifiedEisenstein.shifted A p k).natDegree,
      (p : A) ∣ (RamifiedEisenstein.shifted A p k).coeff i := by
    intro i hi
    exact Ideal.mem_span_singleton.mp
      ((RamifiedEisenstein.shifted_isWeaklyEisensteinAt A hp k).mem hi)
  have hpi : uniformizer A p k ∈ IsLocalRing.maximalIdeal (Extension A p k) := by
    rw [maximalIdeal_eq_span A hp k hmax]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨u, hu⟩ := RamifiedUnit.exists_unit_mul_root_pow
    (RamifiedEisenstein.shifted A p k) (p : A) (Nat.cast_ne_zero.mpr hp.ne_zero)
    (RamifiedEisenstein.shifted_monic A p k) hd
    (RamifiedEisenstein.shifted_coeff_zero A hp k) hcoeff
    (uniformizer A p k) hpi (uniformizer_aeval_shifted A p k)
  exact ⟨u, by simpa only [map_natCast, RamifiedEisenstein.shifted_natDegree A hp k] using hu⟩

theorem algebraMap_injective (hp : p.Prime) (k : ℕ) [IsLocalRing (Extension A p k)] : Function.Injective (algebraMap A (Extension A p k)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  apply Polynomial.degree_ne_of_natDegree_ne
  rw [RamifiedEisenstein.cyclotomic_natDegree A hp k]
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))

theorem charZero (hp : p.Prime) (k : ℕ) [IsLocalRing (Extension A p k)] : CharZero (Extension A p k) where
  cast_injective m n h :=
    Nat.cast_injective (algebraMap_injective A hp k (by simpa only [map_natCast] using h))

theorem uniformizer_ne_zero (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] : uniformizer A p k ≠ 0 := by
  intro hzero
  have hpS : (p : Extension A p k) ≠ 0 := by
    intro hpzero
    have : algebraMap A (Extension A p k) (p : A) =
        algebraMap A (Extension A p k) 0 := by simpa using hpzero
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : A) ≠ 0)
      (algebraMap_injective A hp k this)
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  have hd : (p - 1) * p ^ k ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))
  exact hpS (by simpa only [hzero, zero_pow hd, mul_zero] using hu)

theorem isDiscreteValuationRing (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] [IsDomain (Extension A p k)] : IsDiscreteValuationRing (Extension A p k) :=
  LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (uniformizer_ne_zero A hp k hmax) (maximalIdeal_eq_span A hp k hmax)

theorem addVal_prime (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsDomain (Extension A p k)] [IsDiscreteValuationRing (Extension A p k)] :
    IsDiscreteValuationRing.addVal (Extension A p k) (p : Extension A p k) =
      (((p - 1) * p ^ k : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  exact LocalDVR.addVal_eq_of_unit_mul_uniformizer_pow
    (maximalIdeal_eq_span A hp k hmax) hu

end LocalBase

end CirculantHadamard.RamifiedLocal

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.OrderCyclotomicDivisibility
section
namespace BarkerOrderPort

universe uA


noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

/-- The canonical polynomial with the literal integer coefficients of a cyclic
element evaluates to the same element in the cyclotomic quotient. -/
theorem integerCyclotomicEvaluation_coefficientPolynomial
    (A : Type uA) [CommRing A] (n : ℕ) [NeZero n] (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      AdjoinRoot.mk (cyclotomic n A)
        (DyadicRemainder.coefficientPolynomial n
          (fun i => algebraMap ℤ A (T.coeff (i : ZMod n)))) := by
  classical
  rw [integerCyclotomicEvaluation_apply]
  simp only [DyadicRemainder.coefficientPolynomial, map_sum,
    ← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
    algebraMap_int_eq, Int.coe_castRingHom, map_intCast]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ a : Fin (n + 1), (T.coeff a : AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val) =
        ∑ a : Fin (n + 1), (T.coeff (Fin.ofNat (n + 1) a.val) :
          AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val
      simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]

/-- A scalar norm of the stated dyadic size forces each opposite coefficient
difference to be divisible by its square-root dyadic factor. No condition on
the parity of the coefficients, or separate positivity of `u`, is required. -/
theorem dyadic_difference_dvd (k t u : ℕ)
    (T : CyclicRing.Elem ℤ (2 ^ (k + 1))) (hu : Odd u)
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∀ j : ZMod (2 ^ k), (2 : ℤ) ^ t ∣
      T.coeff (j.val : ZMod (2 ^ (k + 1))) -
        T.coeff ((j.val + 2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
  let A := IntegerTwoLocal.Ring
  let S := RamifiedLocal.Extension A 2 k
  let : IsDomain S := RamifiedLocal.isDomain A Nat.prime_two k
    IntegerTwoLocal.maximalIdeal_eq_span
  let : IsLocalRing S := RamifiedLocal.isLocalRing A Nat.prime_two k
    IntegerTwoLocal.maximalIdeal_eq_span
  let : IsDiscreteValuationRing S := RamifiedLocal.isDiscreteValuationRing A
    Nat.prime_two k IntegerTwoLocal.maximalIdeal_eq_span
  let : CharZero S := charZero_of_injective_algebraMap
    (RamifiedLocal.algebraMap_injective A Nat.prime_two k)
  have hn : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
  let : NeZero (2 ^ (k + 1)) := ⟨hn.ne'⟩
  let x : S := integerCyclotomicEvaluation A (2 ^ (k + 1)) T
  have huS : IsUnit ((u : S) ^ 2) := by
    have hunit := (IntegerTwoLocal.isUnit_natCast_of_odd u hu).map
      (algebraMap A S)
    have huS' : IsUnit (u : S) := by simpa only [map_natCast] using hunit
    exact huS'.pow 2
  have hnormS : x * RamifiedConjugation.cyclotomicConjugation A (2 ^ (k + 1)) hn x =
      (2 : S) ^ (2 * t) * (u : S) ^ 2 := by
    have hcast : (((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) : S) =
        (2 : S) ^ (2 * t) * (u : S) ^ 2 := by
      exact (Int.cast_natCast (R := S) (2 ^ (2 * t) * u ^ 2)).trans
        (show ((2 ^ (2 * t) * u ^ 2 : ℕ) : S) =
            (2 : S) ^ (2 * t) * (u : S) ^ 2 by
          exact (Nat.cast_mul (α := S) (2 ^ (2 * t)) (u ^ 2)).trans
            (congrArg₂ (fun a b : S => a * b)
              ((Nat.cast_pow (α := S) 2 (2 * t)).trans
                (congrArg (fun a : S => a ^ (2 * t)) (Nat.cast_two (R := S))))
              (Nat.cast_pow (α := S) u 2)))
    exact (integerCyclotomicEvaluation_norm A (2 ^ (k + 1)) hn T
      ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) hnorm).trans hcast
  have hdiv : (2 : S) ^ t ∣ x :=
    RamifiedConjugation.cyclotomic_pow_dvd_of_norm_eq A (2 ^ (k + 1)) hn
      2 x ((u : S) ^ 2) t huS hnormS
  let c : ℕ → A := fun i => algebraMap ℤ A (T.coeff (i : ZMod (2 ^ (k + 1))))
  have hpoly : algebraMap A S ((2 : A) ^ t) ∣
      AdjoinRoot.mk (cyclotomic (2 ^ (k + 1)) A)
        (DyadicRemainder.coefficientPolynomial (2 ^ (k + 1)) c) := by
    simpa only [x, map_pow, map_ofNat,
      integerCyclotomicEvaluation_coefficientPolynomial, c,
      eq_intCast] using hdiv
  intro j
  have hcoeff := CyclotomicRemainder.adjoinRoot_dvd_coeff_modByMonic
    (cyclotomic (2 ^ (k + 1)) A) (cyclotomic.monic _ _) ((2 : A) ^ t)
    (DyadicRemainder.coefficientPolynomial (2 ^ (k + 1)) c) hpoly j.val
  rw [DyadicRemainder.coefficientPolynomial_modByMonic_cyclotomic,
    DyadicRemainder.remainder_coeff _ _ _ j.val_lt] at hcoeff
  apply integer_prime_pow_dvd_of_localization (A := A) (P := IntegerTwoLocal.ideal)
    Nat.prime_two rfl t
  simpa only [c, map_sub, Nat.cast_ofNat] using hcoeff

end CirculantHadamard

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.OrderHalving
section
namespace BarkerOrderPort


namespace CirculantHadamard

open CyclicRing

/-- The coefficient obtained by projecting a pair and dividing by two. -/
def pairAverage (a b : ℤ) : ℤ := (a + b) / 2

theorem two_mul_pairAverage {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    2 * pairAverage a b = a + b := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  dsimp [pairAverage]
  omega

/-- Congruent odd coefficients modulo four have an odd integral average. -/
theorem odd_pairAverage {a b : ℤ} (hb : Odd b) (hab : (4 : ℤ) ∣ a - b) :
    Odd (pairAverage a b) := by
  obtain ⟨r, hr⟩ := hb
  obtain ⟨s, hs⟩ := hab
  refine ⟨r + s, ?_⟩
  dsimp [pairAverage]
  omega

theorem odd_pairAverage_of_two_pow_dvd {a b : ℤ} {t : ℕ}
    (hb : Odd b) (ht : 2 ≤ t) (hab : (2 : ℤ) ^ t ∣ a - b) :
    Odd (pairAverage a b) := by
  apply odd_pairAverage hb
  have hpow : (2 : ℤ) ^ 2 ∣ (2 : ℤ) ^ t := pow_dvd_pow 2 ht
  exact (show (4 : ℤ) ∣ (2 : ℤ) ^ t from hpow).trans hab

theorem normScalar_halving (u : ℤ) {t : ℕ} (ht : 1 ≤ t) :
    (2 : ℤ) ^ (2 * t) * u ^ 2 =
      4 * ((2 : ℤ) ^ (2 * (t - 1)) * u ^ 2) := by
  have hexp : 2 * t = 2 * (t - 1) + 2 := by omega
  rw [hexp, pow_add]
  ring

/-- Literal paired coefficients on the quotient of a cyclic group of even
order. Integer divisibility is proved separately before this is used. -/
noncomputable def halvePairs {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m)) : Elem ℤ m :=
  ofCoeffs fun j => pairAverage (T.coeff (j.val : ZMod (2 * m)))
    (T.coeff ((j.val + m : ℕ) : ZMod (2 * m)))

@[simp] theorem halvePairs_apply {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m))
    (j : ZMod m) :
    (halvePairs T).coeff j = pairAverage (T.coeff (j.val : ZMod (2 * m)))
      (T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) := rfl

theorem halvePairs_odd {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m))
    (hodd : ∀ j, Odd (T.coeff j))
    (hpair : ∀ j : ZMod m, (4 : ℤ) ∣
      T.coeff (j.val : ZMod (2 * m)) - T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) :
    ∀ j, Odd ((halvePairs T).coeff j) := by
  intro j
  exact odd_pairAverage (hodd _) (hpair j)

/-- Cancellation takes place in each integer coefficient. A cyclic group
ring has zero divisors, which are irrelevant to this scalar cancellation. -/
theorem four_smul_cancel {m : ℕ} {S T : Elem ℤ m}
    (h : (4 : ℤ) • S = (4 : ℤ) • T) : S = T := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  have hj := congrArg (fun f : Elem ℤ m => f.coeff j) h
  change 4 * S.coeff j = 4 * T.coeff j at hj
  omega

theorem norm_of_double_norm {m : ℕ} [NeZero m] (T : Elem ℤ m) (c : ℤ)
    (h : ((2 : ℤ) • T) * ringStar ((2 : ℤ) • T) = scalar m (4 * c)) :
    T * ringStar T = scalar m c := by
  have hstar : ringStar ((2 : ℤ) • T) = (2 : ℤ) • ringStar T := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro j
    change star ((2 : ℤ) * T.coeff (-j)) = (2 : ℤ) * star (T.coeff (-j))
    simp only [star_trivial]
  have hfour : ((2 : ℤ) • T) * ringStar ((2 : ℤ) • T) =
      (4 : ℤ) • (T * ringStar T) := by
    rw [hstar, smul_mul_assoc, mul_smul_comm, smul_smul]
    rfl
  have hscalar : scalar m (4 * c) = (4 : ℤ) • scalar m c := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro j
    change (scalar m (4 * c)).coeff j = (4 : ℤ) * (scalar m c).coeff j
    by_cases hj : j = 0 <;> simp [scalar_apply, hj]
  apply four_smul_cancel
  rw [← hfour, h, hscalar]

/-- Odd coefficients make the literal projected fiber sums exactly twice the
integer averages. This is an identity for the actual cyclic quotient map. -/
theorem cyclicProjection_eq_two_smul_halvePairs {m : ℕ} [NeZero m]
    (h : m ∣ 2 * m) (T : Elem ℤ (2 * m)) (hodd : ∀ j, Odd (T.coeff j)) :
    cyclicProjection ℤ h T = (2 : ℤ) • halvePairs T := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  rw [cyclicProjection_double_apply (NeZero.pos m) h]
  change _ = 2 * pairAverage _ _
  exact (two_mul_pairAverage (hodd _) (hodd _)).symm

/-- Projecting and dividing by two divides the scalar norm by four. All
coefficient and star identities are consequences of the actual quotient. -/
theorem halvePairs_norm {m : ℕ} [NeZero m] [NeZero (2 * m)]
    (T : Elem ℤ (2 * m)) (c : ℤ) (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T = scalar (2 * m) (4 * c)) :
    halvePairs T * ringStar (halvePairs T) = scalar m c := by
  have hdiv : m ∣ 2 * m := ⟨2, Nat.mul_comm 2 m⟩
  have hproj := cyclicProjection_norm hdiv hnorm
  rw [cyclicProjection_eq_two_smul_halvePairs hdiv T hodd] at hproj
  exact norm_of_double_norm (halvePairs T) c hproj

/-- Algebraic halving with paired divisibility. In the dyadic case, cyclotomic
evaluation supplies this divisibility from the norm equation. -/
theorem halvePairs_odd_norm_of_pair_divisibility {m : ℕ} [NeZero m] [NeZero (2 * m)]
    (t u : ℕ) (T : Elem ℤ (2 * m)) (ht : 2 ≤ t)
    (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T = scalar (2 * m) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ))
    (hpair : ∀ j : ZMod m, (2 : ℤ) ^ t ∣
      T.coeff (j.val : ZMod (2 * m)) - T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) :
    (∀ j, Odd ((halvePairs T).coeff j)) ∧
      halvePairs T * ringStar (halvePairs T) =
        scalar m ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
  constructor
  · intro j
    exact odd_pairAverage_of_two_pow_dvd (hodd _) ht (hpair j)
  · apply halvePairs_norm T _ hodd
    have hs : ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) =
        4 * ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        normScalar_halving (u : ℤ) (show 1 ≤ t by omega)
    rw [← hs]
    exact hnorm

/-- The actual dyadic order-halving step. The paired divisibility is supplied
by cyclotomic evaluation and localization, not assumed in this statement.
The constructed witness is the literal paired average `halvePairs`. -/
theorem exists_odd_halving (k t u : ℕ) (T : Elem ℤ (2 ^ (k + 1)))
    (ht : 2 ≤ t) (hu : Odd u) (hodd : ∀ j, Odd (T.coeff j))
    (hnorm : T * ringStar T =
      scalar (2 ^ (k + 1)) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    ∃ U : Elem ℤ (2 ^ k), (∀ j, Odd (U.coeff j)) ∧
      U * ringStar U = scalar (2 ^ k) ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
  have hstep (n : ℕ) [NeZero n] (hn : n = 2 * 2 ^ k) (S : Elem ℤ n)
      (hS : ∀ j, Odd (S.coeff j))
      (hnormS : S * ringStar S = scalar n ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ))
      (hpair : ∀ j : ZMod (2 ^ k), (2 : ℤ) ^ t ∣
        S.coeff (j.val : ZMod n) - S.coeff ((j.val + 2 ^ k : ℕ) : ZMod n)) :
      ∃ U : Elem ℤ (2 ^ k), (∀ j, Odd (U.coeff j)) ∧
        U * ringStar U = scalar (2 ^ k) ((2 ^ (2 * (t - 1)) * u ^ 2 : ℕ) : ℤ) := by
    subst n
    exact ⟨halvePairs S,
      halvePairs_odd_norm_of_pair_divisibility t u S ht hS hnormS hpair⟩
  exact hstep (2 ^ (k + 1)) (pow_succ' 2 k) T hodd hnorm
    (dyadic_difference_dvd k t u T hu hnorm)

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.ModEight
section
namespace BarkerOrderPort

universe uIota


namespace CirculantHadamard

open scoped BigOperators

/-- Every odd integer square is congruent to one modulo eight. -/
theorem odd_sq_mod_eight {a : ℤ} (ha : Odd a) :
    Int.ModEq 8 (a ^ 2) 1 := by
  rcases ha with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  rw [Int.modEq_iff_dvd]
  refine ⟨-m, ?_⟩
  nlinarith [hm]

/-- A finite sum of odd integer squares is congruent to the number of terms. -/
theorem sum_odd_sq_mod_eight {ι : Type uIota} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, Odd (a i)) :
    Int.ModEq 8 (∑ i ∈ s, a i ^ 2) (s.card : ℤ) := by
  classical
  revert ha
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [Int.ModEq]
  · intro i s hi ih ha
    have hiOdd : Odd (a i) := ha i (Finset.mem_insert_self i s)
    have hsOdd : ∀ j ∈ s, Odd (a j) :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one, add_comm (s.card : ℤ) 1] using
      (odd_sq_mod_eight hiOdd).add (ih hsOdd)

/-- The same congruence for all members of a finite type. -/
theorem sum_univ_odd_sq_mod_eight {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) :
    Int.ModEq 8 (∑ i, a i ^ 2) (Fintype.card ι : ℤ) := by
  simpa using sum_odd_sq_mod_eight Finset.univ a (fun i _ => ha i)

/-- A multiple of eight odd squares cannot sum to four times an odd square. -/
theorem odd_sq_sum_ne_four_mul_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℤ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ 4 * u ^ 2 := by
  have hc : (8 : ℤ) ∣ (Fintype.card ι : ℤ) :=
    Int.natCast_dvd_natCast.mpr hcard
  have hzero : Int.ModEq 8 (∑ i, a i ^ 2) 0 :=
    (sum_univ_odd_sq_mod_eight a ha).trans (Int.modEq_zero_iff_dvd.mpr hc)
  have hfour : Int.ModEq 8 (4 * u ^ 2) 4 := by
    simpa using (odd_sq_mod_eight hu).mul_left 4
  intro hsum
  rw [hsum] at hzero
  have hbad : Int.ModEq 8 (0 : ℤ) 4 := hzero.symm.trans hfour
  norm_num [Int.ModEq] at hbad

/-- Natural norm parameters are cast only after forming the literal scalar. -/
theorem odd_sq_sum_ne_four_mul_nat_sq {ι : Type uIota} [Fintype ι] (a : ι → ℤ)
    (ha : ∀ i, Odd (a i)) (hcard : 8 ∣ Fintype.card ι)
    {u : ℕ} (hu : Odd u) : (∑ i, a i ^ 2) ≠ ((4 * u ^ 2 : ℕ) : ℤ) := by
  simpa using odd_sq_sum_ne_four_mul_sq a ha hcard ((Int.odd_coe_nat u).mpr hu)

/-- The actual cyclic norm equation is impossible for an all-odd row when
the cyclic order is divisible by eight and the norm parameter is odd. -/
theorem odd_norm_four_impossible {n u : ℕ} [NeZero n]
    (hcard : 8 ∣ n) (hu : Odd u) (T : CyclicRing.Elem ℤ n)
    (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar n ((4 * u ^ 2 : ℕ) : ℤ)) : False := by
  have hsum : (∑ a : ZMod n, T.coeff a ^ 2) = ((4 * u ^ 2 : ℕ) : ℤ) := by
    rw [← cyclicNorm_identity_coeff T, hnorm]
    simp
  exact odd_sq_sum_ne_four_mul_nat_sq (fun a : ZMod n => T.coeff a) hodd
    (by simpa using hcard) hu hsum

/-- For `k ≥ 3`, the order `2^k` meets the exact modulo-eight obstruction. -/
theorem odd_norm_four_impossible_two_pow {k u : ℕ} [NeZero (2 ^ k)]
    (hk : 3 ≤ k) (hu : Odd u) (T : CyclicRing.Elem ℤ (2 ^ k))
    (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * CyclicRing.ringStar T =
      CyclicRing.scalar (2 ^ k) ((4 * u ^ 2 : ℕ) : ℤ)) : False := by
  apply odd_norm_four_impossible (u := u) ?_ hu T hodd hnorm
  exact (show 8 ∣ 2 ^ k from pow_dvd_pow 2 hk)

end CirculantHadamard

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.OrderDescent
section
namespace BarkerOrderPort


noncomputable section

namespace CirculantHadamard

open CyclicRing

/-- An odd-coefficient dyadic cyclic norm cannot have two more group
exponents than norm half-exponents. No halving is performed when `t = 1`. -/
theorem odd_norm_impossible {k t u : ℕ}
    (ht : 1 ≤ t) (hkt : t + 2 ≤ k) (hu : Odd u)
    (T : Elem ℤ (2 ^ k)) (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    False := by
  suffices main : ∀ t k : ℕ, 1 ≤ t → t + 2 ≤ k →
      ∀ T : Elem ℤ (2 ^ k), (∀ a, Odd (T.coeff a)) →
        T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) →
          False by
    exact main t k ht hkt T hodd hnorm
  intro t
  induction t with
  | zero =>
      intro k ht
      omega
  | succ t ih =>
      intro k ht hkt T hodd hnorm
      cases t with
      | zero =>
          have hcard : 8 ∣ 2 ^ k := by
            have hpow : (2 : ℕ) ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
            norm_num at hpow
            exact hpow
          apply odd_norm_four_impossible hcard hu T hodd
          simpa only [Nat.zero_add, Nat.mul_one, Nat.reducePow] using hnorm
      | succ t =>
          cases k with
          | zero => omega
          | succ k =>
              obtain ⟨U, hUodd, hUnorm⟩ := exists_odd_halving
                k (t + 1 + 1) u T (by omega) hu hodd hnorm
              apply ih k (by omega) (by omega) U hUodd
              simpa only [Nat.add_sub_cancel] using hUnorm

theorem initial_even_power_norm_impossible {s u : ℕ} (hs : 2 ≤ s) (hu : Odd u)
    (T : Elem ℤ (2 ^ (2 * s))) (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * ringStar T =
      scalar (2 ^ (2 * s)) ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ)) : False :=
  odd_norm_impossible (by omega) (by omega) hu T hodd hnorm

end CirculantHadamard

end

end BarkerOrderPort
end

-- OAI.LinearAlgebra.CirculantHadamard.OrderReduction
section
namespace BarkerOrderPort


namespace CirculantHadamard

/-- Every nontrivial actual real circulant sign Hadamard matrix has order
`4 * u^2` for a positive odd natural number `u`. -/
theorem order_reduction {n : ℕ} (hn : 1 < n)
    (h : ExistsRealCirculantHadamard n) :
    ∃ u : ℕ, 0 < u ∧ Odd u ∧ n = 4 * u ^ 2 := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨hsquare, heven⟩ := order_square_even hn h
  obtain ⟨s, u, hs, huPos, hu, horder⟩ :=
    exists_two_adic_square_decomposition_of_positive_square hsquare heven
  obtain ⟨f, hf, hnorm⟩ := (exists_cyclicSignRow_iff_real (n := n)).2 h
  have hsOne : s = 1 := by
    by_contra hsOne
    have hsTwo : 2 ≤ s := by omega
    obtain ⟨T, hodd, hTnorm⟩ :=
      exists_odd_cyclic_projection hu horder f hf hnorm
    exact odd_norm_impossible (by omega : 1 ≤ s) (by omega : s + 2 ≤ 2 * s)
      hu T hodd hTnorm
  refine ⟨u, huPos, hu, ?_⟩
  simpa [hsOne] using horder

/-- The order restriction stated directly for the supplied real matrix. -/
theorem order_reduction_of_matrix {n : ℕ} (hn : 1 < n) (H : RealMatrix n)
    (hc : IsCirculant H) (hh : IsSignHadamard H) :
    ∃ u : ℕ, 0 < u ∧ Odd u ∧ n = 4 * u ^ 2 :=
  order_reduction hn ⟨H, hc, hh⟩

end CirculantHadamard

end BarkerOrderPort
end

namespace BarkerOddSquarePort

-- OAI.LinearAlgebra.CirculantHadamard.Model
section
namespace OAI

namespace CirculantHadamard

universe u

def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def IsCirculant {n : ℕ} (H : RealMatrix n) : Prop :=
  ∃ h : Fin n → ℝ, ∀ i j, H i j = h (j - i)

def IsSignHadamard {n : ℕ} (H : RealMatrix n) : Prop :=
  (∀ i j, IsSign (H i j)) ∧
    H * H.transpose = (n : ℝ) • (1 : RealMatrix n)

def ExistsRealCirculantHadamard (n : ℕ) : Prop :=
  ∃ H : RealMatrix n, IsCirculant H ∧ IsSignHadamard H

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.Basic
section
namespace OAI

universe uR

namespace CirculantHadamard

def rowCirculant {n : ℕ} {R : Type uR} (h : Fin n → R) :
    Matrix (Fin n) (Fin n) R := fun i j => h (j - i)

@[simp] theorem rowCirculant_apply {n : ℕ} {R : Type uR}
    (h : Fin n → R) (i j : Fin n) : rowCirculant h i j = h (j - i) := rfl

theorem rowCirculant_isCirculant {n : ℕ} (h : Fin n → ℝ) :
    IsCirculant (rowCirculant h) := ⟨h, fun _ _ => rfl⟩

@[simp] theorem rowCirculant_zero_row {n : ℕ} [NeZero n]
    {R : Type uR} (h : Fin n → R) (j : Fin n) : rowCirculant h 0 j = h j := by
  simp [rowCirculant]

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.MatrixBridge
section
namespace OAI

universe uR


namespace CirculantHadamard

open scoped BigOperators

variable {n : ℕ}

/-- An integer sign row with the full Hadamard Gram equation. -/
def IsIntegerSignRow (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧
    rowCirculant h * (rowCirculant h).transpose =
      (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- The Gram entry at `(i,a)` is the cyclic autocorrelation at `a-i`. -/
theorem rowCirculant_gram_apply [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by
  classical
  let e : Fin n ≃ Fin n :=
    { toFun := fun j => j - i
      invFun := fun j => j + i
      left_inv := fun j => sub_add_cancel j i
      right_inv := fun j => add_sub_cancel_right j i }
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant_apply]
  apply Fintype.sum_equiv e
  intro j
  change h (j - i) * h (j - a) = h (j - i) * h ((j - i) - (a - i))
  simp only [sub_sub_sub_cancel_right]

/-- The full Gram equation is exactly the cyclic autocorrelation system. -/
theorem gram_eq_iff_autocorrelation [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) :
    rowCirculant h * (rowCirculant h).transpose =
        (n : R) • (1 : Matrix (Fin n) (Fin n) R) ↔
      ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : R) else 0 := by
  classical
  constructor
  · intro hGram a
    have ha := congrArg (fun M : Matrix (Fin n) (Fin n) R => M 0 a) hGram
    rw [rowCirculant_gram_apply] at ha
    simpa [Matrix.smul_apply, Matrix.one_apply, eq_comm] using ha
  · intro hCorr
    ext i a
    rw [rowCirculant_gram_apply, hCorr]
    by_cases hia : i = a
    · subst a
      simp
    · have hai : a - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hia)
      simp [hia, hai, Matrix.smul_apply]

/-- Casting the integer Gram matrix agrees entry by entry with taking the
Gram matrix after casting the row. -/
theorem intCast_gram_apply (h : Fin n → ℤ) (i j : Fin n) :
    ((rowCirculant h * (rowCirculant h).transpose) i j : ℝ) =
      (rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose) i j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant, Int.cast_sum,
    Int.cast_mul]

private theorem intCast_scaled_identity_apply (i j : Fin n) :
    (((n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℝ) =
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
  by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]

/-- The real coefficient embedding preserves and reflects the entire Gram
identity, including the diagonal value. -/
theorem gram_intCast_iff (h : Fin n → ℤ) :
    rowCirculant (fun a => (h a : ℝ)) *
        (rowCirculant (fun a => (h a : ℝ))).transpose =
        (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  constructor
  · intro hGram
    ext i j
    apply Int.cast_injective (α := ℝ)
    rw [intCast_gram_apply, intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hGram
  · intro hGram
    ext i j
    rw [← intCast_gram_apply, ← intCast_scaled_identity_apply]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => (M i j : ℝ)) hGram

/-- Every integer sign row gives the actual real circulant Hadamard matrix. -/
theorem IsIntegerSignRow.exists_real {h : Fin n → ℤ} (hh : IsIntegerSignRow h) :
    ExistsRealCirculantHadamard n := by
  refine ⟨rowCirculant (fun a => (h a : ℝ)), rowCirculant_isCirculant _, ?_,
    (gram_intCast_iff h).mpr hh.2⟩
  intro i j
  rcases hh.1 (j - i) with hpos | hneg
  · left
    simp only [rowCirculant_apply, hpos, Int.cast_one]
  · right
    simp only [rowCirculant_apply, hneg, Int.cast_neg, Int.cast_one]

/-- A real sign matrix determines an integer sign row without approximation. -/
theorem ExistsRealCirculantHadamard.exists_integerSignRow [NeZero n]
    (hH : ExistsRealCirculantHadamard n) : ∃ h : Fin n → ℤ, IsIntegerSignRow h := by
  classical
  rcases hH with ⟨H, ⟨h, hrow⟩, hsign, hGram⟩
  have hsignRow : ∀ j, IsSign (h j) := by
    intro j
    simpa only [hrow, sub_zero] using hsign 0 j
  let z : Fin n → ℤ := fun j => if h j = 1 then 1 else -1
  have hzcast : ∀ j, (z j : ℝ) = h j := by
    intro j
    by_cases hj : h j = 1
    · simp [z, hj]
    · have hneg := (hsignRow j).resolve_left hj
      simp only [z, if_neg hj, Int.cast_neg, Int.cast_one, hneg]
  have hzsign : ∀ j, IsSign (z j) := by
    intro j
    dsimp [z, IsSign]
    split_ifs <;> simp
  have hzH : rowCirculant (fun j => (z j : ℝ)) = H := by
    ext i j
    rw [rowCirculant_apply, hzcast, hrow]
  refine ⟨z, hzsign, (gram_intCast_iff z).mp ?_⟩
  simpa only [hzH] using hGram

/-- Equivalence between the public real matrix problem and integer sign rows. -/
theorem integerSignRow_iff_real [NeZero n] :
    (∃ h : Fin n → ℤ, IsIntegerSignRow h) ↔ ExistsRealCirculantHadamard n := by
  constructor
  · rintro ⟨h, hh⟩
    exact hh.exists_real
  · exact ExistsRealCirculantHadamard.exists_integerSignRow

/-- A direct integer autocorrelation presentation of the real matrix problem. -/
theorem existsReal_iff_integer_autocorrelation [NeZero n] :
    ExistsRealCirculantHadamard n ↔
      ∃ h : Fin n → ℤ, (∀ j, IsSign (h j)) ∧
        ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : ℤ) else 0 := by
  rw [← integerSignRow_iff_real]
  simp only [IsIntegerSignRow, gram_eq_iff_autocorrelation]

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicRing
section
namespace OAI

universe uR uG

/-! The finite cyclic group ring, with coefficient conjugation and index reversal. -/

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

abbrev Elem (R : Type uR) [Semiring R] (n : ℕ) := AddMonoidAlgebra R (ZMod n)

noncomputable def groupStar {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) : AddMonoidAlgebra R G :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun a => star (f.coeff (-a)))

@[simp] theorem groupStar_apply {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) (a : G) :
    (groupStar f).coeff a = star (f.coeff (-a)) := rfl

@[simp] theorem groupStar_groupStar {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) :
    groupStar (groupStar f) = f := by
  ext a
  simp

@[simp] theorem groupStar_single {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (a : G) (r : R) :
    groupStar (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) (star r) := by
  classical
  ext b
  change star (Finsupp.single a r (-b)) = Finsupp.single (-a) (star r) b
  by_cases hb : b = -a
  · subst b
    simp
  · have hab : a ≠ -b := by
      intro h
      apply hb
      simpa using (congrArg (fun x : G => -x) h).symm
    simp [hab, Ne.symm hb]

noncomputable def ofCoeffs {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (c : ZMod n → R) : Elem R n :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)

@[simp] theorem ofCoeffs_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (c : ZMod n → R) (a : ZMod n) : (ofCoeffs c).coeff a = c a := rfl

@[simp] theorem ofCoeffs_coeffs {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f : Elem R n) : ofCoeffs (fun a => f.coeff a) = f := by
  exact AddMonoidAlgebra.coeff_injective (Finsupp.ext fun _ => rfl)

noncomputable def scalar {R : Type uR} [Semiring R] (n : ℕ) (r : R) : Elem R n :=
  AddMonoidAlgebra.single 0 r

@[simp] theorem scalar_apply {R : Type uR} [Semiring R] {n : ℕ}
    (r : R) (a : ZMod n) : (scalar n r).coeff a = if a = 0 then r else 0 := by
  classical
  simp [scalar, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

@[simp] theorem scalar_natCast {R : Type uR} [Semiring R] (n m : ℕ) :
    scalar n (m : R) = (m : Elem R n) := rfl

noncomputable def ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : Elem R n :=
  ofCoeffs fun a => star (f.coeff (-a))

@[simp] theorem ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (ringStar f).coeff a = star (f.coeff (-a)) := rfl

theorem ringStar_eq_groupStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStar f = groupStar f := rfl

@[simp] theorem ringStar_single {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (a : ZMod n) (r : R) :
    ringStar (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) (star r) :=
  groupStar_single a r

section Convolution

variable {R : Type uR} {G : Type uG} [Semiring R] [AddCommGroup G] [Fintype G]

theorem group_mul_apply (f g : AddMonoidAlgebra R G) (a : G) :
    (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) := by
  classical
  calc
    (f * g).coeff a = f.coeff.sum (fun j r => r * g.coeff (-j + a)) :=
      AddMonoidAlgebra.coeff_mul_apply_left f g a
    _ = ∑ j, f.coeff j * g.coeff (-j + a) := Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
    _ = _ := by simp only [sub_eq_add_neg, add_comm]

theorem group_mul_apply_right (f g : AddMonoidAlgebra R G) (a : G) :
    (f * g).coeff a = ∑ j, f.coeff (a - j) * g.coeff j := by
  classical
  calc
    (f * g).coeff a = g.coeff.sum (fun j r => f.coeff (a - j) * r) := by
      simpa only [sub_eq_add_neg] using AddMonoidAlgebra.coeff_mul_apply_right f g a
    _ = _ := Finsupp.sum_fintype _ _ (fun _ => mul_zero _)

@[simp] theorem groupStar_zero [StarRing R] :
    groupStar (0 : AddMonoidAlgebra R G) = 0 := by
  ext a
  simp

@[simp] theorem groupStar_add [StarRing R] (f g : AddMonoidAlgebra R G) :
    groupStar (f + g) = groupStar f + groupStar g := by
  ext a
  change star (f.coeff (-a) + g.coeff (-a)) = star (f.coeff (-a)) + star (g.coeff (-a))
  exact star_add _ _

@[simp] theorem groupStar_one [StarRing R] :
    groupStar (1 : AddMonoidAlgebra R G) = 1 := by
  classical
  ext a
  simp [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem groupStar_mul [StarRing R] (f g : AddMonoidAlgebra R G) :
    groupStar (f * g) = groupStar g * groupStar f := by
  ext a
  rw [groupStar_apply, group_mul_apply_right, star_sum, group_mul_apply]
  apply Fintype.sum_equiv (Equiv.neg G)
  intro j
  simp only [star_mul, groupStar_apply, Equiv.neg_apply, neg_neg]
  congr 2
  congr 1
  abel

end Convolution

theorem mul_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f g : Elem R n) (a : ZMod n) : (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) :=
  group_mul_apply f g a

theorem mul_apply_right {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f g : Elem R n) (a : ZMod n) : (f * g).coeff a = ∑ j, f.coeff (a - j) * g.coeff j :=
  group_mul_apply_right f g a

@[simp] theorem ringStar_ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStar (ringStar f) = f :=
  groupStar_groupStar f

@[simp] theorem ringStar_zero {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] : ringStar (0 : Elem R n) = 0 := groupStar_zero

@[simp] theorem ringStar_add {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f g : Elem R n) : ringStar (f + g) = ringStar f + ringStar g :=
  groupStar_add f g

@[simp] theorem ringStar_one {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] : ringStar (1 : Elem R n) = 1 := groupStar_one

theorem ringStar_mul {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f g : Elem R n) :
    ringStar (f * g) = ringStar g * ringStar f := groupStar_mul f g

@[simp] theorem ringStar_scalar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (r : R) : ringStar (scalar n r) = scalar n (star r) := by
  classical
  ext a
  by_cases ha : a = 0 <;> simp [scalar_apply, ha]

theorem mul_ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (f * ringStar f).coeff a = ∑ j, f.coeff j * star (f.coeff (j - a)) := by
  simp only [mul_apply, ringStar_apply, neg_sub]

noncomputable def groupStarRingHom {R : Type uR} {G : Type uG} [CommSemiring R] [StarRing R]
    [AddCommGroup G] [Fintype G] : AddMonoidAlgebra R G →+* AddMonoidAlgebra R G where
  toFun := groupStar
  map_zero' := groupStar_zero
  map_one' := groupStar_one
  map_add' := groupStar_add
  map_mul' f g := by rw [groupStar_mul, mul_comm]

noncomputable def ringStarRingHom {R : Type uR} [CommSemiring R] [StarRing R]
    (n : ℕ) [NeZero n] : Elem R n →+* Elem R n := groupStarRingHom

@[simp] theorem ringStarRingHom_apply {R : Type uR} [CommSemiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStarRingHom n f = ringStar f := rfl

noncomputable def augmentation {R : Type uR} [Semiring R] (n : ℕ) : Elem R n →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R) 1 (fun _ _ => Commute.one_right _)

theorem augmentation_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f : Elem R n) : augmentation n f = ∑ a, f.coeff a := by
  change f.coeff.sum (fun _ r => r * 1) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp

@[simp] theorem augmentation_scalar {R : Type uR} [Semiring R] (n : ℕ) (r : R) :
    augmentation n (scalar n r) = r := by
  change AddMonoidAlgebra.liftNC (RingHom.id R).toAddMonoidHom
    (1 : Multiplicative (ZMod n) →* R) (AddMonoidAlgebra.single 0 r) = r
  simp

theorem augmentation_ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) :
    augmentation n (ringStar f) = star (augmentation n f) := by
  simp only [augmentation_apply, ringStar_apply, star_sum]
  exact Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun _ => rfl)

theorem augmentation_norm_star {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (r : R)
    (h : f * ringStar f = scalar n r) :
    augmentation n f * star (augmentation n f) = r := by
  have he := congrArg (augmentation n) h
  simpa only [map_mul, augmentation_ringStar, augmentation_scalar] using he

theorem augmentation_norm {n : ℕ} [NeZero n] (f : Elem ℤ n) (r : ℤ)
    (h : f * ringStar f = scalar n r) : (augmentation n f) ^ 2 = r := by
  simpa only [star_trivial, pow_two] using augmentation_norm_star f r h

end CirculantHadamard.CyclicRing

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicNorm
section
namespace OAI

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every literal integer coefficient is a sign. -/
def CyclicSignRow {n : ℕ} (f : CyclicRing.Elem ℤ n) : Prop :=
  ∀ a, IsSign (f.coeff a)

section PositiveOrder

variable {n : ℕ} [NeZero n]

/-- The cyclic group-ring element whose coefficients are the given first row. -/
def cyclicRow (h : Fin n → ℤ) : CyclicRing.Elem ℤ n :=
  CyclicRing.ofCoeffs (fun a => h ((ZMod.finEquiv n).symm a))

/-- Recover the integer first row without changing the cyclic orientation. -/
def integerRow (f : CyclicRing.Elem ℤ n) : Fin n → ℤ :=
  fun j => f.coeff (ZMod.finEquiv n j)

@[simp] theorem cyclicRow_apply (h : Fin n → ℤ) (a : ZMod n) :
    (cyclicRow h).coeff a = h ((ZMod.finEquiv n).symm a) := by
  simp [cyclicRow]

@[simp] theorem integerRow_apply (f : CyclicRing.Elem ℤ n) (j : Fin n) :
    integerRow f j = f.coeff (ZMod.finEquiv n j) := rfl

@[simp] theorem cyclicRow_integerRow (f : CyclicRing.Elem ℤ n) :
    cyclicRow (integerRow f) = f := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  simp [integerRow]

@[simp] theorem integerRow_cyclicRow (h : Fin n → ℤ) :
    integerRow (cyclicRow h) = h := by
  funext j
  simp [integerRow]

theorem sum_cyclicRow (h : Fin n → ℤ) :
    (∑ a : ZMod n, (cyclicRow h).coeff a) = ∑ j : Fin n, h j := by
  simpa only [cyclicRow_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    RingEquiv.symm_apply_apply] using
    ((ZMod.finEquiv n).toEquiv.sum_comp (fun a : ZMod n => (cyclicRow h).coeff a)).symm

theorem cyclicSignRow_cyclicRow_iff (h : Fin n → ℤ) :
    CyclicSignRow (cyclicRow h) ↔ ∀ j, IsSign (h j) := by
  constructor
  · intro hf j
    simpa using hf (ZMod.finEquiv n j)
  · intro hh a
    simpa using hh ((ZMod.finEquiv n).symm a)

/-- The norm coefficient uses the same `j - a` orientation as the row Gram. -/
theorem cyclicRow_norm_apply (h : Fin n → ℤ) (a : Fin n) :
    (cyclicRow h * CyclicRing.ringStar (cyclicRow h)).coeff (ZMod.finEquiv n a) =
      ∑ j : Fin n, h j * h (j - a) := by
  rw [CyclicRing.mul_ringStar_apply]
  simpa only [cyclicRow_apply, map_sub, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply, star_trivial] using
    ((ZMod.finEquiv n).toEquiv.sum_comp
      (fun j : ZMod n =>
        (cyclicRow h).coeff j * star ((cyclicRow h).coeff (j - ZMod.finEquiv n a)))).symm

theorem cyclicRow_norm_iff_autocorrelation (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      ∀ a : Fin n, (∑ j : Fin n, h j * h (j - a)) =
        if a = 0 then (n : ℤ) else 0 := by
  constructor
  · intro hn a
    have ha := congrArg
      (fun f : CyclicRing.Elem ℤ n => f.coeff (ZMod.finEquiv n a)) hn
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using ha
  · intro hh
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro x
    obtain ⟨a, rfl⟩ := (ZMod.finEquiv n).surjective x
    simpa only [cyclicRow_norm_apply, CyclicRing.scalar_apply,
      RingEquiv.map_eq_zero_iff] using hh a

theorem cyclicRow_norm_iff_gram (h : Fin n → ℤ) :
    cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
        CyclicRing.scalar n (n : ℤ) ↔
      rowCirculant h * (rowCirculant h).transpose =
        (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) :=
  (cyclicRow_norm_iff_autocorrelation h).trans (gram_eq_iff_autocorrelation h).symm

theorem integerSignRow_iff_cyclicSignNorm (h : Fin n → ℤ) :
    IsIntegerSignRow h ↔
      CyclicSignRow (cyclicRow h) ∧
        cyclicRow h * CyclicRing.ringStar (cyclicRow h) =
          CyclicRing.scalar n (n : ℤ) := by
  exact and_congr (cyclicSignRow_cyclicRow_iff h).symm (cyclicRow_norm_iff_gram h).symm

/-- The literal sign norm equation is equivalent to the public real-matrix
existence predicate.  Neither direction assumes a mathematical bridge. -/
theorem exists_cyclicSignRow_iff_real :
    (∃ f : CyclicRing.Elem ℤ n,
      CyclicSignRow f ∧ f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) ↔
      ExistsRealCirculantHadamard n := by
  rw [← integerSignRow_iff_real]
  constructor
  · rintro ⟨f, hf, hn⟩
    refine ⟨integerRow f, (integerSignRow_iff_cyclicSignNorm _).2 ?_⟩
    simpa only [cyclicRow_integerRow] using And.intro hf hn
  · rintro ⟨h, hh⟩
    exact ⟨cyclicRow h, (integerSignRow_iff_cyclicSignNorm h).1 hh⟩

/-- The identity coefficient is the sum of the actual coefficient squares. -/
theorem cyclicNorm_identity_coeff (f : CyclicRing.Elem ℤ n) :
    (f * CyclicRing.ringStar f).coeff 0 = ∑ a : ZMod n, f.coeff a ^ 2 := by
  simp [CyclicRing.mul_ringStar_apply, pow_two]

theorem cyclicSignRow_identity_coeff (f : CyclicRing.Elem ℤ n)
    (hf : CyclicSignRow f) : (f * CyclicRing.ringStar f).coeff 0 = (n : ℤ) := by
  rw [cyclicNorm_identity_coeff]
  calc
    (∑ a : ZMod n, f.coeff a ^ 2) = ∑ _a : ZMod n, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      rcases hf a with ha | ha <;> simp [ha]
    _ = (n : ℤ) := by simp

/-- Evaluating the actual cyclic norm at the trivial character gives the
square of the coefficient sum. -/
theorem augmentation_sum_sq_of_norm (f : CyclicRing.Elem ℤ n)
    (hf : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    (∑ a : ZMod n, f.coeff a) ^ 2 = (n : ℤ) := by
  simpa only [CyclicRing.augmentation_apply] using
    CyclicRing.augmentation_norm f (n : ℤ) hf

end PositiveOrder

end CirculantHadamard

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial
section
namespace OAI

universe uR uA


noncomputable section

namespace CirculantHadamard.CyclicPolynomial

open Polynomial

variable (R : Type uR) [CommRing R] (n : ℕ)

/-- The defining polynomial of the cyclic group algebra. -/
def relation : R[X] := X ^ n - 1

/-- The basis element at the distinguished generator of the cyclic group. -/
def generator : AddMonoidAlgebra R (ZMod n) := AddMonoidAlgebra.single 1 1

theorem generator_pow : generator R n ^ n = 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul,
    AddMonoidAlgebra.one_def]

theorem root_pow : AdjoinRoot.root (relation R n) ^ n = 1 := by
  have h : AdjoinRoot.mk (relation R n) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_self (f := relation R n)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h

variable {R}

/-- A genuine cyclic character associated to an element whose `n`th power is one. -/
def powerCharacter {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) : Multiplicative (ZMod n) →* A where
  toFun a := x ^ a.toAdd.val
  map_one' := by
    change x ^ (0 : ZMod n).val = 1
    simp
  map_mul' a b := by
    change x ^ (a.toAdd + b.toAdd).val =
      x ^ a.toAdd.val * x ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

@[simp]
theorem powerCharacter_apply {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) (i : ZMod n) :
    powerCharacter n x hx (Multiplicative.ofAdd i) = x ^ i.val := rfl

@[simp]
theorem powerCharacter_generator {A : Type uA} [Monoid A] [NeZero n]
    (x : A) (hx : x ^ n = 1) :
    powerCharacter n x hx (Multiplicative.ofAdd 1) = x := by
  change x ^ (1 : ZMod n).val = x
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]

variable (R)

/-- Send the cyclic basis element at `i` to the `i.val`th power of the root. -/
def toPolynomial [NeZero n] :
    AddMonoidAlgebra R (ZMod n) →ₐ[R] AdjoinRoot (relation R n) :=
  AddMonoidAlgebra.lift R (AdjoinRoot (relation R n)) (ZMod n)
    (powerCharacter n (AdjoinRoot.root (relation R n)) (root_pow R n))

@[simp]
theorem toPolynomial_single [NeZero n] (i : ZMod n) (r : R) :
    toPolynomial R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val := by
  simp [toPolynomial, Algebra.smul_def]

@[simp]
theorem toPolynomial_generator [NeZero n] :
    toPolynomial R n (generator R n) = AdjoinRoot.root (relation R n) := by
  simp only [generator, toPolynomial, AddMonoidAlgebra.lift_single,
    powerCharacter_generator, one_smul]

theorem generator_isRoot : aeval (generator R n) (relation R n) = 0 := by
  simp [relation, generator_pow]

/-- Evaluate the polynomial quotient at the actual cyclic group-ring generator. -/
def fromPolynomial :
    AdjoinRoot (relation R n) →ₐ[R] AddMonoidAlgebra R (ZMod n) :=
  AdjoinRoot.liftAlgHom (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_root :
    fromPolynomial R n (AdjoinRoot.root (relation R n)) = generator R n := by
  exact AdjoinRoot.liftAlgHom_root (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n)

@[simp]
theorem fromPolynomial_mk (p : R[X]) :
    fromPolynomial R n (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p := by
  exact AdjoinRoot.liftAlgHom_mk (relation R n)
    (Algebra.ofId R (AddMonoidAlgebra R (ZMod n)))
    (generator R n) (generator_isRoot R n) p

theorem generator_pow_val [NeZero n] (i : ZMod n) :
    generator R n ^ i.val = AddMonoidAlgebra.single i 1 := by
  simp [generator, AddMonoidAlgebra.single_pow, nsmul_eq_mul]

theorem toPolynomial_comp_fromPolynomial [NeZero n] :
    (toPolynomial R n).comp (fromPolynomial R n) =
      AlgHom.id R (AdjoinRoot (relation R n)) := by
  apply AdjoinRoot.algHom_ext
  simp

theorem fromPolynomial_comp_toPolynomial [NeZero n] :
    (fromPolynomial R n).comp (toPolynomial R n) =
      AlgHom.id R (AddMonoidAlgebra R (ZMod n)) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    simp [generator_pow_val]
  · exact Subsingleton.elim _ _

/-- The actual cyclic group algebra is the polynomial quotient by `X ^ n - 1`. -/
def cyclicEquiv [NeZero n] :
    AddMonoidAlgebra R (ZMod n) ≃ₐ[R] AdjoinRoot (relation R n) :=
  AlgEquiv.ofAlgHom (toPolynomial R n) (fromPolynomial R n)
    (toPolynomial_comp_fromPolynomial R n) (fromPolynomial_comp_toPolynomial R n)

@[simp]
theorem cyclicEquiv_single [NeZero n] (i : ZMod n) (r : R) :
    cyclicEquiv R n (AddMonoidAlgebra.single i r) =
      algebraMap R (AdjoinRoot (relation R n)) r *
        AdjoinRoot.root (relation R n) ^ i.val :=
  toPolynomial_single R n i r

@[simp]
theorem cyclicEquiv_generator [NeZero n] :
    cyclicEquiv R n (generator R n) = AdjoinRoot.root (relation R n) :=
  toPolynomial_generator R n

@[simp]
theorem cyclicEquiv_symm_root [NeZero n] :
    (cyclicEquiv R n).symm (AdjoinRoot.root (relation R n)) = generator R n :=
  fromPolynomial_root R n

@[simp]
theorem cyclicEquiv_symm_mk [NeZero n] (p : R[X]) :
    (cyclicEquiv R n).symm (AdjoinRoot.mk (relation R n) p) =
      aeval (generator R n) p :=
  fromPolynomial_mk R n p

@[simp]
theorem cyclicEquiv_aeval [NeZero n] (p : R[X]) :
    cyclicEquiv R n (aeval (generator R n) p) =
      AdjoinRoot.mk (relation R n) p := by
  rw [← Polynomial.aeval_algHom_apply, cyclicEquiv_generator,
    AdjoinRoot.aeval_eq]

end CirculantHadamard.CyclicPolynomial

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryBlocks
section
namespace OAI

universe uR uS


noncomputable section

namespace CirculantHadamard.BinaryBlocks

open CyclicRing
open scoped BigOperators

abbrev ProductElem (R : Type uR) [Semiring R] (m : ℕ) :=
  AddMonoidAlgebra R (ZMod 4 × ZMod m)

theorem four_coprime_sq {u : ℕ} (hu : Odd u) : Nat.Coprime 4 (u ^ 2) := by
  simpa using (hu.coprime_two_left.pow_left 2).pow_right 2

/-- The concrete CRT map on the exponent group. -/
def crtIndex (u : ℕ) (hu : Odd u) :
    ZMod (4 * u ^ 2) ≃+ ZMod 4 × ZMod (u ^ 2) :=
  (ZMod.chineseRemainder (four_coprime_sq hu)).toAddEquiv

/-- The resulting algebra equivalence preserves the actual convolution. -/
def crt (R : Type uR) [CommRing R] (u : ℕ) (hu : Odd u) :
    Elem R (4 * u ^ 2) ≃ₐ[R] ProductElem R (u ^ 2) :=
  AddMonoidAlgebra.domCongr R R (crtIndex u hu)

@[simp] theorem crt_apply {R : Type uR} [CommRing R] {u : ℕ} (hu : Odd u)
    (f : Elem R (4 * u ^ 2)) (a : ZMod 4 × ZMod (u ^ 2)) :
    (crt R u hu f).coeff a = f.coeff ((crtIndex u hu).symm a) := by
  exact AddMonoidAlgebra.coeff_domCongr (R := R) (A := R) (crtIndex u hu) f a

theorem crt_ringStar {R : Type uR} [CommRing R] [StarRing R]
    {u : ℕ} [NeZero u] (hu : Odd u) (f : Elem R (4 * u ^ 2)) :
    crt R u hu (ringStar f) = groupStar (crt R u hu f) := by
  ext a
  simp only [crt_apply, ringStar_apply, groupStar_apply, map_neg]

theorem crt_norm {R : Type uR} [CommRing R] [StarRing R]
    {u : ℕ} [NeZero u] (hu : Odd u) (f : Elem R (4 * u ^ 2)) (N : ℕ)
    (hnorm : f * ringStar f = (N : Elem R (4 * u ^ 2))) :
    crt R u hu f * groupStar (crt R u hu f) = (N : ProductElem R (u ^ 2)) := by
  rw [← crt_ringStar hu, ← map_mul, hnorm, map_natCast]

def block {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : ZMod 4) : Elem R m :=
  ofCoeffs fun b => f.coeff (j, b)

@[simp] theorem block_apply {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : ZMod 4) (b : ZMod m) : (block f j).coeff b = f.coeff (j, b) := rfl

/-- Fin-four indexing agrees with the coefficient arithmetic used by the halves. -/
def blocks {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) : Fin 4 → Elem R m := fun j => block f j

@[simp] theorem blocks_apply {R : Type uR} [Semiring R] {m : ℕ} [NeZero m]
    (f : ProductElem R m) (j : Fin 4) (b : ZMod m) : (blocks f j).coeff b = f.coeff (j, b) := rfl

theorem blocks_signs {m : ℕ} [NeZero m] (f : ProductElem ℤ m)
    (hf : ∀ a, IsSign (f.coeff a)) : ∀ j b, IsSign ((blocks f j).coeff b) :=
  fun j b => hf (j, b)

theorem crt_blocks_signs {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hf : ∀ a, IsSign (f.coeff a)) :
    ∀ j b, IsSign ((blocks (crt ℤ u hu f) j).coeff b) := by
  intro j b
  rw [blocks_apply, crt_apply]
  exact hf ((crtIndex u hu).symm (j, b))

section Evaluation

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (m : ℕ)

/-- A fourth-root character on the first factor, retaining the second factor. -/
def partialCharacter (z : S) (hz : z ^ 4 = 1) :
    Multiplicative (ZMod 4 × ZMod m) →* Elem S m where
  toFun a := AddMonoidAlgebra.single a.toAdd.2
    (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd a.toAdd.1))
  map_one' := by
    change AddMonoidAlgebra.single 0
      (CyclicPolynomial.powerCharacter 4 z hz 1) = 1
    rw [map_one]
    rfl
  map_mul' a b := by
    change AddMonoidAlgebra.single (a.toAdd.2 + b.toAdd.2)
      (CyclicPolynomial.powerCharacter 4 z hz
        (Multiplicative.ofAdd a.toAdd.1 * Multiplicative.ofAdd b.toAdd.1)) =
      AddMonoidAlgebra.single a.toAdd.2
        (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd a.toAdd.1)) *
      AddMonoidAlgebra.single b.toAdd.2
        (CyclicPolynomial.powerCharacter 4 z hz (Multiplicative.ofAdd b.toAdd.1))
    rw [map_mul, AddMonoidAlgebra.single_mul_single]

/-- Actual partial evaluation, allowing the integer-to-complex coefficient map. -/
def partialEval (φ : R →+* S) (z : S) (hz : z ^ 4 = 1) :
    ProductElem R m →+* Elem S m :=
  AddMonoidAlgebra.liftNCRingHom
    (AddMonoidAlgebra.singleZeroRingHom.comp φ) (partialCharacter m z hz)
    (fun _ _ => Commute.all _ _)

@[simp] theorem partialEval_single (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (a : ZMod 4 × ZMod m) (r : R) :
    partialEval m φ z hz (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a.2 (φ r * z ^ a.1.val) := by
  simp [partialEval, AddMonoidAlgebra.liftNCRingHom,
    AddMonoidAlgebra.liftNC_single, partialCharacter,
    AddMonoidAlgebra.single_mul_single]

variable [NeZero m]

/-- The four coefficients are summed, with no loss of the second coordinate. -/
theorem partialEval_apply (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) (b : ZMod m) :
    (partialEval m φ z hz f).coeff b =
      ∑ j : ZMod 4, φ (f.coeff (j, b)) * z ^ j.val := by
  classical
  have hexp : f = ∑ a : ZMod 4 × ZMod m, AddMonoidAlgebra.single a (f.coeff a) := by
    simpa only [AddMonoidAlgebra.sum_coeff_single] using
      (Finsupp.sum_fintype f.coeff AddMonoidAlgebra.single
        (fun a => AddMonoidAlgebra.single_zero a))
  calc
    (partialEval m φ z hz f).coeff b =
        (partialEval m φ z hz (∑ a : ZMod 4 × ZMod m,
          AddMonoidAlgebra.single a (f.coeff a))).coeff b :=
            congrArg (fun g => (partialEval m φ z hz g).coeff b) hexp
    _ = ∑ a : ZMod 4 × ZMod m,
        (AddMonoidAlgebra.single a.2 (φ (f.coeff a) * z ^ a.1.val)).coeff b := by
      rw [map_sum]
      simp only [partialEval_single, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

def mappedBlock (φ : R →+* S) (f : ProductElem R m) (j : ZMod 4) : Elem S m :=
  ofCoeffs fun b => φ (f.coeff (j, b))

@[simp] theorem mappedBlock_apply (φ : R →+* S) (f : ProductElem R m)
    (j : ZMod 4) (b : ZMod m) : (mappedBlock m φ f j).coeff b = φ (f.coeff (j, b)) := rfl

theorem partialEval_four (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) :
    partialEval m φ z hz f = mappedBlock m φ f 0 + z • mappedBlock m φ f 1 +
      z ^ 2 • mappedBlock m φ f 2 + z ^ 3 • mappedBlock m φ f 3 := by
  ext b
  rw [partialEval_apply]
  change (∑ j : Fin 4, φ (f.coeff (j, b)) * z ^ j.val) =
    φ (f.coeff (0, b)) + z * φ (f.coeff (1, b)) +
      z ^ 2 * φ (f.coeff (2, b)) + z ^ 3 * φ (f.coeff (3, b))
  rw [Fin.sum_univ_four]
  change φ (f.coeff (0, b)) * z ^ 0 + φ (f.coeff (1, b)) * z ^ 1 +
    φ (f.coeff (2, b)) * z ^ 2 + φ (f.coeff (3, b)) * z ^ 3 = _
  simp only [pow_zero, pow_one, one_mul, mul_comm]

theorem partialEval_one (φ : R →+* S) (f : ProductElem R m) :
    partialEval m φ 1 (by simp) f = mappedBlock m φ f 0 + mappedBlock m φ f 1 +
      mappedBlock m φ f 2 + mappedBlock m φ f 3 := by
  simpa using partialEval_four m φ 1 (by simp) f

theorem partialEval_neg_one (φ : R →+* S) (f : ProductElem R m) :
    partialEval m φ (-1) (by norm_num) f = mappedBlock m φ f 0 - mappedBlock m φ f 1 +
      mappedBlock m φ f 2 - mappedBlock m φ f 3 := by
  have hn2 : (-1 : S) ^ 2 = 1 := by norm_num
  have hn3 : (-1 : S) ^ 3 = -1 := by norm_num
  simpa only [hn2, hn3, one_smul, neg_one_smul, sub_eq_add_neg]
    using partialEval_four m φ (-1) (by norm_num) f

theorem fourthRoot_pow_four (i : S) (hi : i ^ 2 = -1) : i ^ 4 = 1 := by
  calc
    i ^ 4 = (i ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hi]; norm_num

/-- The Gaussian coefficient ring can use its actual imaginary unit directly. -/
theorem partialEval_fourthRoot (φ : R →+* S) (i : S) (hi : i ^ 2 = -1)
    (f : ProductElem R m) :
    partialEval m φ i (fourthRoot_pow_four i hi) f =
      mappedBlock m φ f 0 + i • mappedBlock m φ f 1 -
        mappedBlock m φ f 2 - i • mappedBlock m φ f 3 := by
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  simpa only [hi, hi3, neg_one_smul, neg_smul, one_smul, sub_eq_add_neg]
    using partialEval_four m φ i (fourthRoot_pow_four i hi) f

end Evaluation

theorem partialEval_I {R : Type uR} [CommRing R] (m : ℕ) [NeZero m]
    (φ : R →+* ℂ) (f : ProductElem R m) :
    partialEval m φ Complex.I (by norm_num [pow_succ, Complex.I_sq]) f =
      mappedBlock m φ f 0 + Complex.I • mappedBlock m φ f 1 -
        mappedBlock m φ f 2 - Complex.I • mappedBlock m φ f 3 := by
  exact partialEval_fourthRoot m φ Complex.I Complex.I_sq f

section Star

variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]

/-- Intertwining is proved on the actual ring maps, with both parts of the star. -/
theorem partialEval_groupStar (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hchar : ∀ a : ZMod 4, z ^ (-a).val = star (z ^ a.val))
    (f : ProductElem R m) :
    partialEval m φ z hz (groupStar f) = ringStar (partialEval m φ z hz f) := by
  have hs (a : ZMod 4 × ZMod m) (r : R) :
      partialEval m φ z hz (groupStar (AddMonoidAlgebra.single a r)) =
        ringStar (partialEval m φ z hz (AddMonoidAlgebra.single a r)) := by
    rw [groupStar_single, partialEval_single, partialEval_single, ringStar_single]
    change AddMonoidAlgebra.single (-a.2) (φ (star r) * z ^ (-a.1).val) =
      AddMonoidAlgebra.single (-a.2) (star (φ r * z ^ a.1.val))
    rw [hφ, hchar, star_mul, mul_comm]
  have he : (partialEval m φ z hz).comp groupStarRingHom =
      (ringStarRingHom m).comp (partialEval m φ z hz) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      exact hs 0 r
    · intro a
      exact hs a 1
  exact RingHom.congr_fun he f

theorem one_character_star : ∀ a : ZMod 4, (1 : S) ^ (-a).val = star ((1 : S) ^ a.val) := by
  intro a
  simp

theorem neg_one_character_star :
    ∀ a : ZMod 4, (-1 : S) ^ (-a).val = star ((-1 : S) ^ a.val) := by
  intro a
  fin_cases a
  · change (-1 : S) ^ 0 = star ((-1 : S) ^ 0)
    simp
  · change (-1 : S) ^ 3 = star ((-1 : S) ^ 1)
    norm_num
  · change (-1 : S) ^ 2 = star ((-1 : S) ^ 2)
    norm_num
  · change (-1 : S) ^ 1 = star ((-1 : S) ^ 3)
    norm_num

theorem fourthRoot_character_star (i : S) (hi : i ^ 2 = -1) (hstar : star i = -i) :
    ∀ a : ZMod 4, i ^ (-a).val = star (i ^ a.val) := by
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  intro a
  fin_cases a
  · change i ^ 0 = star (i ^ 0)
    simp
  · change i ^ 3 = star (i ^ 1)
    simp [hi3, hstar]
  · change i ^ 2 = star (i ^ 2)
    rw [hi]
    simp
  · change i ^ 1 = star (i ^ 3)
    simp [hi3, hstar]

end Star

theorem I_character_star :
    ∀ a : ZMod 4, Complex.I ^ (-a).val = star (Complex.I ^ a.val) := by
  exact fourthRoot_character_star Complex.I Complex.I_sq (by simp)

end CirculantHadamard.BinaryBlocks

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryCoefficients
section
namespace OAI

universe uG uR

namespace CirculantHadamard
namespace BinaryCoefficients

def halfSum (x y : ℤ) : ℤ := (x + y) / 2

def halfDiff (x y : ℤ) : ℤ := (x - y) / 2

def signOffset (x : ℤ) : ℤ := (x - 1) / 2

theorem two_halfSum {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    2 * halfSum x y = x + y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [halfSum]

theorem two_halfDiff {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    2 * halfDiff x y = x - y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [halfDiff]

theorem halfDiff_eq {x y : ℤ} (hx : IsSign x) (hy : IsSign y) :
    halfDiff x y = halfSum x y - y := by
  linarith [two_halfSum hx hy, two_halfDiff hx hy]

theorem two_signOffset {x : ℤ} (hx : IsSign x) :
    2 * signOffset x = x - 1 := by
  rcases hx with rfl | rfl <;> norm_num [signOffset]

theorem sign_eq_one_add {x : ℤ} (hx : IsSign x) :
    x = 1 + 2 * signOffset x := by
  linarith [two_signOffset hx]

variable {G : Type uG}

/-- The canonical coefficient map, with no change to the index. -/
noncomputable def castCoeffs {R : Type uR} [Ring R] (f : G →₀ ℤ) : G →₀ R :=
  Finsupp.mapRange (fun z : ℤ => (z : R)) (by simp) f

@[simp] theorem castCoeffs_apply {R : Type uR} [Ring R] (f : G →₀ ℤ) (x : G) :
    castCoeffs (R := R) f x = (f x : R) := rfl

noncomputable def complexify (f : G →₀ ℤ) : G →₀ ℂ := castCoeffs f

@[simp] theorem complexify_apply (f : G →₀ ℤ) (x : G) :
    complexify f x = (f x : ℂ) := rfl

theorem complexify_add (f h : G →₀ ℤ) :
    complexify (f + h) = complexify f + complexify h := by
  ext x
  simp

theorem complexify_sub (f h : G →₀ ℤ) :
    complexify (f - h) = complexify f - complexify h := by
  ext x
  simp

theorem complexify_int_smul (z : ℤ) (f : G →₀ ℤ) :
    complexify (z • f) = (z : ℂ) • complexify f := by
  ext x
  simp [Finsupp.smul_apply, smul_eq_mul]

/-- Integer real and imaginary parts interpreted in any coefficient ring.
The linear identities do not require an equation such as `i^2 = -1`. -/
noncomputable def liftPair {R : Type uR} [CommRing R] (i : R) (f h : G →₀ ℤ) : G →₀ R :=
  castCoeffs f + i • castCoeffs h

variable [Finite G]

noncomputable def ofCoeffs {R : Type uR} [Zero R] (f : G → R) : G →₀ R :=
  Finsupp.equivFunOnFinite.symm f

@[simp] theorem ofCoeffs_apply {R : Type uR} [Zero R] (f : G → R) (x : G) :
    ofCoeffs f x = f x := rfl

/-- Literal sign hypotheses for the four blocks, without a norm premise. -/
def Signs (H : Fin 4 → (G →₀ ℤ)) : Prop := ∀ j x, IsSign (H j x)

noncomputable def a (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfSum (H 0 x) (H 2 x)

noncomputable def b (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfSum (H 1 x) (H 3 x)

noncomputable def c (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ := a H + b H

noncomputable def d (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ := a H - b H

noncomputable def gReal (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfDiff (H 0 x) (H 2 x)

noncomputable def gImag (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfDiff (H 1 x) (H 3 x)

noncomputable def gOver {R : Type uR} [CommRing R] (i : R)
    (H : Fin 4 → (G →₀ ℤ)) : G →₀ R := liftPair i (gReal H) (gImag H)

noncomputable def g (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℂ := gOver Complex.I H

noncomputable def UReal (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => signOffset (H 2 x)

noncomputable def UImag (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => signOffset (H 3 x)

noncomputable def UOver {R : Type uR} [CommRing R] (i : R)
    (H : Fin 4 → (G →₀ ℤ)) : G →₀ R := liftPair i (UReal H) (UImag H)

noncomputable def U (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℂ := UOver Complex.I H

/-- This is the sum of all group elements (every coefficient is one),
not the scalar one in a convolution ring. -/
noncomputable def JOver (R : Type uR) [CommRing R] : G →₀ R := ofCoeffs fun _ => 1

@[simp] theorem JOver_apply {R : Type uR} [CommRing R] (x : G) :
    (JOver R : G →₀ R) x = 1 := rfl

noncomputable def J : G →₀ ℂ := JOver ℂ

@[simp] theorem J_apply (x : G) : (J : G →₀ ℂ) x = 1 := rfl

theorem two_a {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • a H = H 0 + H 2 := by
  ext x
  change 2 * halfSum (H 0 x) (H 2 x) = H 0 x + H 2 x
  exact two_halfSum (hH 0 x) (hH 2 x)

theorem two_b {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • b H = H 1 + H 3 := by
  ext x
  change 2 * halfSum (H 1 x) (H 3 x) = H 1 x + H 3 x
  exact two_halfSum (hH 1 x) (hH 3 x)

theorem two_c {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • c H = H 0 + H 1 + H 2 + H 3 := by
  rw [c, smul_add, two_a hH, two_b hH]
  abel

theorem two_d {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℤ) • d H = H 0 - H 1 + H 2 - H 3 := by
  rw [d, smul_sub, two_a hH, two_b hH]
  abel

theorem gOver_eq_ab {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    gOver i H = castCoeffs (a H) + i • castCoeffs (b H) -
      castCoeffs (H 2) - i • castCoeffs (H 3) := by
  ext x
  simp only [gOver, liftPair, gReal, gImag, a, b, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, castCoeffs_apply, ofCoeffs_apply, smul_eq_mul]
  rw [halfDiff_eq (hH 0 x) (hH 2 x), halfDiff_eq (hH 1 x) (hH 3 x)]
  push_cast
  ring

theorem two_gOver {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : R) • gOver i H = castCoeffs (H 0) + i • castCoeffs (H 1) -
      castCoeffs (H 2) - i • castCoeffs (H 3) := by
  ext x
  have h0 := congrArg (fun z : ℤ => (z : R)) (two_halfDiff (hH 0 x) (hH 2 x))
  have h1 := congrArg (fun z : ℤ => (z : R)) (two_halfDiff (hH 1 x) (hH 3 x))
  push_cast at h0 h1
  simp only [gOver, liftPair, gReal, gImag, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, castCoeffs_apply, ofCoeffs_apply, smul_eq_mul]
  calc
    _ = 2 * (halfDiff (H 0 x) (H 2 x) : R) +
        i * (2 * (halfDiff (H 1 x) (H 3 x) : R)) := by ring
    _ = _ := by rw [h0, h1]; ring

/-- The binary identity with an explicitly constructed integral-pair `U`. -/
theorem binary_identity_over {R : Type uR} [CommRing R] (i : R)
    {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    castCoeffs (H 2) + i • castCoeffs (H 3) =
      (1 + i) • (JOver R : G →₀ R) + (2 : R) • UOver i H := by
  ext x
  have h2 := congrArg (fun z : ℤ => (z : R)) (sign_eq_one_add (hH 2 x))
  have h3 := congrArg (fun z : ℤ => (z : R)) (sign_eq_one_add (hH 3 x))
  push_cast at h2 h3
  simp only [UOver, liftPair, UReal, UImag, Finsupp.add_apply, Finsupp.smul_apply,
    castCoeffs_apply, ofCoeffs_apply, JOver_apply, smul_eq_mul]
  rw [h2, h3]
  ring

theorem g_eq_ab {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    g H = complexify (a H) + Complex.I • complexify (b H) -
      complexify (H 2) - Complex.I • complexify (H 3) :=
  gOver_eq_ab Complex.I hH

theorem two_g {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    (2 : ℂ) • g H = complexify (H 0) + Complex.I • complexify (H 1) -
      complexify (H 2) - Complex.I • complexify (H 3) :=
  two_gOver Complex.I hH

theorem binary_identity {H : Fin 4 → (G →₀ ℤ)} (hH : Signs H) :
    complexify (H 2) + Complex.I • complexify (H 3) =
      (1 + Complex.I) • (J : G →₀ ℂ) + (2 : ℂ) • U H :=
  binary_identity_over Complex.I hH

end BinaryCoefficients
end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicRings
section
namespace OAI


noncomputable section

namespace CirculantHadamard.CyclotomicRings

open scoped BigOperators

/-- The fixed primitive root used in the `p`-direction. -/
def rho (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem rho_isPrimitiveRoot (p : ℕ) (hp : p ≠ 0) : IsPrimitiveRoot (rho p) p :=
  Complex.isPrimitiveRoot_exp p hp

@[simp] theorem rho_zero : rho 0 = 1 := by simp [rho]

theorem rho_pow (p : ℕ) (hp : p ≠ 0) : rho p ^ p = 1 :=
  (rho_isPrimitiveRoot p hp).pow_eq_one

theorem I_isPrimitiveRoot : IsPrimitiveRoot Complex.I 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by norm_num) Complex.I_pow_four
  intro j hj0 hj4
  interval_cases j <;>
    norm_num [pow_one, Complex.I_sq, Complex.I_pow_three, Complex.ext_iff]

/-- Conjugation of a complex root is an explicit nonnegative power. -/
theorem star_eq_pow_pred_of_pow_eq_one {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) : star z = z ^ (n - 1) := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h, hn] at hz
  have hnorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hn
  have hs : star z * z = 1 := by
    change (starRingEnd ℂ) z * z = 1
    rw [Complex.conj_mul', hnorm]
    norm_num
  have hp : z ^ (n - 1) * z = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn), hz]
  exact mul_right_cancel₀ hz0 (hs.trans hp.symm)

theorem star_rho (p : ℕ) (hp : p ≠ 0) : star (rho p) = rho p ^ (p - 1) :=
  star_eq_pow_pred_of_pow_eq_one hp (rho_pow p hp)

theorem rho_mul_star (p : ℕ) : rho p * star (rho p) = 1 := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [star_rho p hp, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)]
    exact rho_pow p hp

def GaussianRing : Subalgebra ℤ ℂ := Algebra.adjoin ℤ ({Complex.I} : Set ℂ)

def gaussianI : GaussianRing := ⟨Complex.I, Algebra.subset_adjoin (by simp)⟩

@[simp] theorem coe_gaussianI : (gaussianI : ℂ) = Complex.I := rfl

theorem gaussianI_sq : gaussianI ^ 2 = -1 :=
  Subtype.ext Complex.I_sq

/-- A finite list of prime directions, keeping `i` in the coefficient ring. -/
def rootRing (s : Finset ℕ) : Subalgebra ℤ ℂ :=
  Algebra.adjoin ℤ (({Complex.I} : Set ℂ) ∪ rho '' (s : Set ℕ))

/-- The literal global ring in the alternating products. -/
abbrev B (u : ℕ) : Subalgebra ℤ ℂ := rootRing u.primeFactors

/-- The literal coefficient ring with the `p`-direction omitted. -/
abbrev awayRing (u p : ℕ) : Subalgebra ℤ ℂ := rootRing (u.primeFactors.erase p)

theorem I_mem_rootRing (s : Finset ℕ) : Complex.I ∈ rootRing s :=
  Algebra.subset_adjoin (Or.inl (by simp))

theorem rho_mem_rootRing (s : Finset ℕ) (p : ℕ) (hp : p ∈ s) : rho p ∈ rootRing s :=
  Algebra.subset_adjoin (Or.inr ⟨p, hp, rfl⟩)

theorem I_mem_B (u : ℕ) : Complex.I ∈ B u := I_mem_rootRing _

theorem rho_mem_B (u p : ℕ) (hp : p ∈ u.primeFactors) : rho p ∈ B u :=
  rho_mem_rootRing _ _ hp

theorem I_mem_awayRing (u p : ℕ) : Complex.I ∈ awayRing u p := I_mem_rootRing _

theorem rho_mem_awayRing (u p q : ℕ) (hq : q ∈ u.primeFactors) (hne : q ≠ p) :
    rho q ∈ awayRing u p :=
  rho_mem_rootRing _ _ (Finset.mem_erase.mpr ⟨hne, hq⟩)

theorem rootRing_mono {s t : Finset ℕ} (hst : s ⊆ t) : rootRing s ≤ rootRing t := by
  apply Algebra.adjoin_mono
  exact Set.union_subset_union_right _ (Set.image_mono hst)

theorem GaussianRing_le_rootRing (s : Finset ℕ) : GaussianRing ≤ rootRing s :=
  Algebra.adjoin_mono Set.subset_union_left

theorem awayRing_le_B (u p : ℕ) : awayRing u p ≤ B u :=
  rootRing_mono (Finset.erase_subset _ _)

def awayInclusion (u p : ℕ) : awayRing u p →ₐ[ℤ] B u :=
  Subalgebra.inclusion (awayRing_le_B u p)

def gaussianToB (u : ℕ) : GaussianRing →ₐ[ℤ] B u :=
  Subalgebra.inclusion (GaussianRing_le_rootRing _)

def gaussianToAway (u p : ℕ) : GaussianRing →ₐ[ℤ] awayRing u p :=
  Subalgebra.inclusion (GaussianRing_le_rootRing _)

@[simp] theorem coe_awayInclusion (u p : ℕ) (x : awayRing u p) :
    (awayInclusion u p x).val = x.val := by
  exact Subalgebra.coe_inclusion (R := ℤ) (A := ℂ)
    (S := awayRing u p) (T := B u) (awayRing_le_B u p) x

@[simp] theorem coe_gaussianToB (u : ℕ) (x : GaussianRing) :
    (gaussianToB u x).val = x.val := by
  exact Subalgebra.coe_inclusion (R := ℤ) (A := ℂ)
    (S := GaussianRing) (T := B u) (GaussianRing_le_rootRing _) x

@[simp] theorem coe_gaussianToAway (u p : ℕ) (x : GaussianRing) :
    (gaussianToAway u p x).val = x.val := by
  exact Subalgebra.coe_inclusion (R := ℤ) (A := ℂ)
    (S := GaussianRing) (T := awayRing u p) (GaussianRing_le_rootRing _) x

theorem gaussian_mem (s : Finset ℕ) (a b : ℤ) :
    (a : ℂ) + (b : ℂ) * Complex.I ∈ rootRing s :=
  (rootRing s).add_mem ((rootRing s).algebraMap_mem a)
    ((rootRing s).mul_mem ((rootRing s).algebraMap_mem b) (I_mem_rootRing s))

private theorem star_mem_adjoin {S : Set ℂ}
    (hS : ∀ z ∈ S, star z ∈ Algebra.adjoin ℤ S) {z : ℂ}
    (hz : z ∈ Algebra.adjoin ℤ S) : star z ∈ Algebra.adjoin ℤ S := by
  refine Algebra.adjoin_induction (p := fun z _ => star z ∈ Algebra.adjoin ℤ S)
    hS ?_ ?_ ?_ hz
  · intro a
    simp
  · intro x y _ _ hx hy
    simpa only [star_add] using (Algebra.adjoin ℤ S).add_mem hx hy
  · intro x y _ _ hx hy
    simpa only [star_mul] using (Algebra.adjoin ℤ S).mul_mem hy hx

theorem star_mem_GaussianRing {z : ℂ} (hz : z ∈ GaussianRing) :
    star z ∈ GaussianRing := by
  apply star_mem_adjoin (S := ({Complex.I} : Set ℂ)) ?_ hz
  rintro z (rfl : z = Complex.I)
  simp

theorem star_mem_rootRing (s : Finset ℕ) {z : ℂ} (hz : z ∈ rootRing s) :
    star z ∈ rootRing s := by
  apply star_mem_adjoin ?_ hz
  rintro z (hI | ⟨p, hp, rfl⟩)
  · rcases hI with rfl
    simpa [rootRing] using (rootRing s).neg_mem (I_mem_rootRing s)
  · by_cases hp0 : p = 0
    · simpa only [hp0, rho_zero, star_one, rootRing] using (rootRing s).one_mem
    · rw [star_rho p hp0]
      exact (rootRing s).pow_mem (rho_mem_rootRing s p hp) _

instance GaussianRingStarRing : StarRing GaussianRing where
  star x := ⟨star (x : ℂ), star_mem_GaussianRing x.property⟩
  star_involutive x := Subtype.ext (star_star (x : ℂ))
  star_mul x y := Subtype.ext (star_mul (x : ℂ) (y : ℂ))
  star_add x y := Subtype.ext (star_add (x : ℂ) (y : ℂ))

instance rootRingStarRing (s : Finset ℕ) : StarRing (rootRing s) where
  star x := ⟨star (x : ℂ), star_mem_rootRing s x.property⟩
  star_involutive x := Subtype.ext (star_star (x : ℂ))
  star_mul x y := Subtype.ext (star_mul (x : ℂ) (y : ℂ))
  star_add x y := Subtype.ext (star_add (x : ℂ) (y : ℂ))

@[simp] theorem coe_star_GaussianRing (x : GaussianRing) :
    ((star x : GaussianRing) : ℂ) = star (x : ℂ) := rfl

@[simp] theorem coe_star_rootRing (s : Finset ℕ) (x : rootRing s) :
    ((star x : rootRing s) : ℂ) = star (x : ℂ) := rfl

@[simp] theorem gaussianToB_star (u : ℕ) (x : GaussianRing) :
    gaussianToB u (star x) = star (gaussianToB u x) := by
  apply Subtype.ext
  exact (coe_gaussianToB u (star x)).trans
    ((coe_star_GaussianRing x).trans
      ((congrArg (star : ℂ → ℂ) (coe_gaussianToB u x).symm).trans
        (coe_star_rootRing u.primeFactors (gaussianToB u x)).symm))

@[simp] theorem gaussianToAway_star (u p : ℕ) (x : GaussianRing) :
    gaussianToAway u p (star x) = star (gaussianToAway u p x) := by
  apply Subtype.ext
  exact (coe_gaussianToAway u p (star x)).trans
    ((coe_star_GaussianRing x).trans
      ((congrArg (star : ℂ → ℂ) (coe_gaussianToAway u p x).symm).trans
        (coe_star_rootRing (u.primeFactors.erase p) (gaussianToAway u p x)).symm))

private theorem rho_finite_order (p : ℕ) : ∃ n : ℕ, n ≠ 0 ∧ rho p ^ n = 1 := by
  by_cases hp : p = 0
  · exact ⟨1, by decide, by simp [hp]⟩
  · exact ⟨p, hp, rho_pow p hp⟩

private theorem map_star_of_pow_eq_one (S : Subalgebra ℤ ℂ) [StarRing S]
    (hstar : ∀ x : S, ((star x : S) : ℂ) = star (x : ℂ))
    (σ : S →+* ℂ) (x : S) (n : ℕ) (hn : n ≠ 0) (hx : (x : ℂ) ^ n = 1) :
    σ (star x) = star (σ x) := by
  have hxS : x ^ n = 1 := Subtype.ext hx
  have hsource : star x = x ^ (n - 1) := by
    apply Subtype.ext
    simpa only [hstar, Subalgebra.coe_pow] using star_eq_pow_pred_of_pow_eq_one hn hx
  have htarget : σ x ^ n = 1 := by rw [← map_pow, hxS, map_one]
  rw [hsource, map_pow, star_eq_pow_pred_of_pow_eq_one hn htarget]

private theorem map_star_adjoin (S : Set ℂ) [StarRing (Algebra.adjoin ℤ S)]
    (hstar : ∀ x : Algebra.adjoin ℤ S, ((star x : Algebra.adjoin ℤ S) : ℂ) = star (x : ℂ))
    (hS : ∀ z ∈ S, ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 1)
    (σ : Algebra.adjoin ℤ S →+* ℂ) (x : Algebra.adjoin ℤ S) :
    σ (star x) = star (σ x) := by
  rcases x with ⟨x, hx⟩
  refine Algebra.adjoin_induction
    (p := fun z hz => σ (star (⟨z, hz⟩ : Algebra.adjoin ℤ S)) =
      star (σ (⟨z, hz⟩ : Algebra.adjoin ℤ S))) ?_ ?_ ?_ ?_ hx
  · intro z hz
    obtain ⟨n, hn, hzn⟩ := hS z hz
    exact map_star_of_pow_eq_one _ hstar σ ⟨z, Algebra.subset_adjoin hz⟩ n hn hzn
  · intro a
    change σ (star (a : Algebra.adjoin ℤ S)) = star (σ (a : Algebra.adjoin ℤ S))
    simp
  · intro z w hz hw hzp hwp
    change σ (star ((⟨z, hz⟩ : Algebra.adjoin ℤ S) + ⟨w, hw⟩)) =
      star (σ ((⟨z, hz⟩ : Algebra.adjoin ℤ S) + ⟨w, hw⟩))
    simpa only [star_add, map_add] using congrArg₂ (· + ·) hzp hwp
  · intro z w hz hw hzp hwp
    change σ (star ((⟨z, hz⟩ : Algebra.adjoin ℤ S) * ⟨w, hw⟩)) =
      star (σ ((⟨z, hz⟩ : Algebra.adjoin ℤ S) * ⟨w, hw⟩))
    simpa only [star_mul, map_mul] using congrArg₂ (· * ·) hwp hzp

/-- Every complex-valued ring map respects the actual conjugation. -/
theorem map_star_rootRing (s : Finset ℕ) (σ : rootRing s →+* ℂ) (x : rootRing s) :
    σ (star x) = star (σ x) := by
  apply @map_star_adjoin (({Complex.I} : Set ℂ) ∪ rho '' (s : Set ℕ))
    (rootRingStarRing s) (coe_star_rootRing s) ?_ σ x
  rintro z (hI | ⟨p, _, rfl⟩)
  · rcases hI with rfl
    exact ⟨4, by decide, Complex.I_pow_four⟩
  · exact rho_finite_order p

theorem map_star_B (u : ℕ) (σ : B u →+* ℂ) (x : B u) :
    σ (star x) = star (σ x) := map_star_rootRing _ σ x

theorem map_star_awayRing (u p : ℕ) (σ : awayRing u p →+* ℂ) (x : awayRing u p) :
    σ (star x) = star (σ x) := map_star_rootRing _ σ x

theorem map_star_GaussianRing (σ : GaussianRing →+* ℂ) (x : GaussianRing) :
    σ (star x) = star (σ x) := by
  apply @map_star_adjoin ({Complex.I} : Set ℂ) GaussianRingStarRing
    coe_star_GaussianRing ?_ σ x
  rintro z (rfl : z = Complex.I)
  exact ⟨4, by decide, Complex.I_pow_four⟩

private theorem integral_of_finite_order {z : ℂ} (h : ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 1) :
    IsIntegral ℤ z := by
  obtain ⟨n, hn, hz⟩ := h
  apply IsIntegral.of_pow (Nat.pos_of_ne_zero hn)
  rw [hz]
  exact isIntegral_one

instance rootRing_finite (s : Finset ℕ) : Module.Finite ℤ (rootRing s) := by
  apply Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_singleton Complex.I).union (s.finite_toSet.image rho))
  rintro z (hI | ⟨p, _, rfl⟩)
  · rcases hI with rfl
    exact integral_of_finite_order ⟨4, by decide, Complex.I_pow_four⟩
  · exact integral_of_finite_order (rho_finite_order p)

instance GaussianRing_finite : Module.Finite ℤ GaussianRing :=
  Algebra.finite_adjoin_simple_of_isIntegral
    (integral_of_finite_order ⟨4, by decide, Complex.I_pow_four⟩)

private theorem primitive_mul {z w : ℂ} {m n : ℕ}
    (hz : IsPrimitiveRoot z m) (hw : IsPrimitiveRoot w n) (hcop : m.Coprime n) :
    IsPrimitiveRoot (z * w) (m * n) := by
  have horder := (Commute.all z w).orderOf_mul_eq_mul_orderOf_of_coprime
    (by simpa only [← hz.eq_orderOf, ← hw.eq_orderOf] using hcop)
  rw [← hz.eq_orderOf, ← hw.eq_orderOf] at horder
  rw [← horder]
  exact IsPrimitiveRoot.orderOf _

theorem prime_roots_prod_primitive (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    IsPrimitiveRoot (∏ p ∈ s, rho p) (∏ p ∈ s, p) := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert p s hp ih =>
      intro hs
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, Nat.Prime q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      apply primitive_mul (rho_isPrimitiveRoot p hpp.ne_zero) (ih hsp)
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hpp (hsp q hq)).mpr
      intro heq
      exact hp (heq.symm ▸ hq)

/-- The single generator of a finite prime-root ring. -/
def etaOf (s : Finset ℕ) : ℂ := Complex.I * ∏ q ∈ s, rho q

def orderOfSet (s : Finset ℕ) : ℕ := 4 * ∏ q ∈ s, q

theorem etaOf_isPrimitiveRoot (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    IsPrimitiveRoot (etaOf s) (orderOfSet s) := by
  apply primitive_mul I_isPrimitiveRoot (prime_roots_prod_primitive s hs)
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  simpa using ((hodd p hp).coprime_two_left.pow_left 2)

theorem orderOfSet_pos (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    0 < orderOfSet s :=
  Nat.mul_pos (by decide) (Finset.prod_pos (fun p hp => (hs p hp).pos))

theorem rootRing_eq_singleton (s : Finset ℕ)
    (hs : ∀ p ∈ s, Nat.Prime p) (hodd : ∀ p ∈ s, Odd p) :
    rootRing s = Algebra.adjoin ℤ ({etaOf s} : Set ℂ) := by
  classical
  have hη := etaOf_isPrimitiveRoot s hs hodd
  let : NeZero (orderOfSet s) := ⟨(orderOfSet_pos s hs).ne'⟩
  have hηmem : etaOf s ∈ rootRing s :=
    (rootRing s).mul_mem (I_mem_rootRing s)
      ((rootRing s).prod_mem (fun q hq => rho_mem_rootRing s q hq))
  have hpower {z : ℂ} (hz : z ^ orderOfSet s = 1) :
      z ∈ Algebra.adjoin ℤ ({etaOf s} : Set ℂ) := by
    obtain ⟨j, _, hj⟩ := hη.eq_pow_of_pow_eq_one hz
    rw [← hj]
    exact (Algebra.adjoin ℤ ({etaOf s} : Set ℂ)).pow_mem
      (Algebra.subset_adjoin (by simp)) j
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro z (hI | ⟨q, hq, rfl⟩)
    · rcases hI with rfl
      apply hpower
      exact (I_isPrimitiveRoot.pow_eq_one_iff_dvd _).mpr (dvd_mul_right 4 _)
    · apply hpower
      apply ((rho_isPrimitiveRoot q (hs q hq).ne_zero).pow_eq_one_iff_dvd _).mpr
      exact (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq).trans (dvd_mul_left _ 4)
  · apply Algebra.adjoin_le
    simpa using hηmem

def eta (u p : ℕ) : ℂ := etaOf (u.primeFactors.erase p)

def awayOrder (u p : ℕ) : ℕ := orderOfSet (u.primeFactors.erase p)

theorem eta_isPrimitiveRoot (u p : ℕ) (hu : Odd u) :
    IsPrimitiveRoot (eta u p) (awayOrder u p) := by
  apply etaOf_isPrimitiveRoot
  · intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  · intro q hq
    exact hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))

theorem awayOrder_pos (u p : ℕ) : 0 < awayOrder u p :=
  orderOfSet_pos _ (fun _q hq => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))

theorem awayRing_eq_singleton (u p : ℕ) (hu : Odd u) :
    awayRing u p = Algebra.adjoin ℤ ({eta u p} : Set ℂ) := by
  apply rootRing_eq_singleton
  · intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  · intro q hq
    exact hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))

theorem prime_not_dvd_awayOrder (u p : ℕ) (hu : Odd u) (hp : p ∈ u.primeFactors) :
    ¬p ∣ awayOrder u p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  apply hpp.coprime_iff_not_dvd.mp
  change p.Coprime (4 * ∏ q ∈ u.primeFactors.erase p, q)
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · have hodd := hu.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    simpa using hodd.coprime_two_right.pow_right 2
  · apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply (Nat.coprime_primes hpp
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))).mpr
    exact (Finset.ne_of_mem_erase hq).symm

theorem B_eq_adjoin_away (u p : ℕ) (hp : p ∈ u.primeFactors) :
    B u = (Algebra.adjoin (awayRing u p) ({rho p} : Set ℂ)).restrictScalars ℤ := by
  change Algebra.adjoin ℤ (({Complex.I} : Set ℂ) ∪ rho '' (u.primeFactors : Set ℕ)) =
    (Algebra.adjoin
      (Algebra.adjoin ℤ (({Complex.I} : Set ℂ) ∪ rho '' ((u.primeFactors.erase p : Finset ℕ) : Set ℕ)))
      ({rho p} : Set ℂ)).restrictScalars ℤ
  rw [← Algebra.adjoin_union_eq_adjoin_adjoin]
  congr 1
  ext z
  constructor
  · rintro (hI | ⟨q, hq, rfl⟩)
    · exact Or.inl (Or.inl hI)
    · by_cases heq : q = p
      · exact Or.inr (by simp [heq])
      · exact Or.inl (Or.inr ⟨q, Finset.mem_erase.mpr ⟨heq, hq⟩, rfl⟩)
  · rintro ((hI | ⟨q, hq, rfl⟩) | heq)
    · exact Or.inl hI
    · exact Or.inr ⟨q, Finset.mem_of_mem_erase hq, rfl⟩
    · exact Or.inr ⟨p, hp, (Set.mem_singleton_iff.mp heq).symm⟩

end CirculantHadamard.CyclotomicRings

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryNorms
section
namespace OAI

universe uR uA


noncomputable section

namespace CirculantHadamard.BinaryNorms

open CyclicRing

section CoefficientCancellation

variable {R : Type uR} [CommRing R] [IsDomain R] [CharZero R]
variable {n : ℕ}

/-- Cancel four coefficientwise, without any domain assumption on the group
algebra. -/
theorem four_nsmul_cancel {f g : Elem R n}
    (h : (4 : ℕ) • f = (4 : ℕ) • g) : f = g := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  let coeff : Elem R n →+ R :=
    { toFun := fun p => p.coeff a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have ha := congrArg coeff h
  rw [map_nsmul, map_nsmul] at ha
  have hc : (4 : R) * f.coeff a = (4 : R) * g.coeff a := by
    simp only [coeff, nsmul_eq_mul, Nat.cast_ofNat] at ha
    convert ha using 1 <;> rfl
  exact mul_left_cancel₀ (by norm_num : (4 : R) ≠ 0) hc

end CoefficientCancellation

section NormCancellation

variable {R : Type uR} [CommRing R] [StarRing R]
variable {n : ℕ} [NeZero n]

/-- Coefficient conjugation fixes natural scalar multiples. -/
theorem ringStar_nsmul (k : ℕ) (x : Elem R n) :
    ringStar (k • x) = k • ringStar x := by
  exact map_nsmul (ringStarRingHom n) k x

/-- The exact factor four before cancellation; this is valid even when the
coefficient ring itself has zero divisors. -/
theorem two_nsmul_norm (x : Elem R n) :
    ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) =
      (4 : ℕ) • (x * ringStar x) := by
  rw [ringStar_nsmul]
  simp only [nsmul_eq_mul]
  ring

variable [IsDomain R] [CharZero R]

theorem norm_of_two_nsmul (u : ℕ) (x : Elem R n)
    (h : ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) =
      ((4 * u ^ 2 : ℕ) : Elem R n)) :
    x * ringStar x = scalar n ((u ^ 2 : ℕ) : R) := by
  rw [scalar_natCast]
  apply four_nsmul_cancel
  calc
    (4 : ℕ) • (x * ringStar x) =
        ((2 : ℕ) • x) * ringStar ((2 : ℕ) • x) :=
      (two_nsmul_norm x).symm
    _ = ((4 * u ^ 2 : ℕ) : Elem R n) := h
    _ = (4 : ℕ) • ((u ^ 2 : ℕ) : Elem R n) := by
      simp only [Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat]

theorem norm_of_evaluation
    {A : Type uA} [CommRing A] (sigma : A → A)
    (eval : A →+* Elem R n) (u : ℕ) (h : A) (x : Elem R n)
    (hnorm : h * sigma h = ((4 * u ^ 2 : ℕ) : A))
    (hstar : eval (sigma h) = ringStar (eval h))
    (hvalue : eval h = (2 : ℕ) • x) :
    x * ringStar x = scalar n ((u ^ 2 : ℕ) : R) := by
  apply norm_of_two_nsmul u x
  rw [← hvalue, ← hstar, ← map_mul, hnorm, map_natCast]

end NormCancellation

section ActualBinaryElements

open BinaryBlocks BinaryCoefficients

variable {m : ℕ} [NeZero m]

/-- The partial evaluation uses the same literal coefficient cast as the
constructed Gaussian element. -/
theorem mappedBlock_intCast {R : Type uR} [CommRing R]
    (f : ProductElem ℤ m) (j : ZMod 4) :
    mappedBlock m (Int.castRingHom R) f j =
      AddMonoidAlgebra.ofCoeff (castCoeffs (block f j).coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  rfl

/-- The value at one is twice the actual integral `c`, not a freely chosen
element with a prescribed evaluation. -/
theorem evaluation_one_eq_two_c (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (RingHom.id ℤ) 1 (by simp) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff)) := by
  rw [partialEval_one]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_c (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, two_smul, mappedBlock, blocks, block,
    RingHom.id_apply] at hv ⊢
  convert hv using 1 <;> rfl

/-- The value at minus one is twice the actual integral `d`. -/
theorem evaluation_neg_one_eq_two_d (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (RingHom.id ℤ) (-1) (by norm_num) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff)) := by
  rw [partialEval_neg_one]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_d (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    two_smul, mappedBlock, blocks, block, RingHom.id_apply] at hv ⊢
  convert hv using 1 <;> rfl

/-- The fourth-root evaluation is twice the constructed Gaussian pair.
The coefficient ring is arbitrary, including the actual Gaussian ring,
without assuming a group-algebra domain. -/
theorem evaluation_fourthRoot_eq_two_gOver {R : Type uR} [CommRing R]
    (i : R) (hi : i ^ 2 = -1) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a)) :
    partialEval m (Int.castRingHom R) i (fourthRoot_pow_four i hi) f =
      (2 : ℕ) • AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff)) := by
  rw [partialEval_fourthRoot m (Int.castRingHom R) i hi f]
  simp only [mappedBlock_intCast]
  apply AddMonoidAlgebra.coeff_injective
  have hv := (two_gOver i (H := fun j => (blocks f j).coeff) (blocks_signs f hsign)).symm
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_smul, two_smul, blocks] at hv ⊢
  convert hv using 1 <;> rfl

theorem c_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℤ m) (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℤ) := by
  exact norm_of_evaluation groupStar
    (partialEval m (RingHom.id ℤ) 1 (by simp)) u f (AddMonoidAlgebra.ofCoeff (c (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (RingHom.id ℤ) 1 (by simp)
      (fun _ => by simp) one_character_star f)
    (evaluation_one_eq_two_c f hsign)

/-- The second norm uses the real fourth root `-1` and its genuine star law. -/
theorem d_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℤ m) (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℤ) := by
  exact norm_of_evaluation groupStar
    (partialEval m (RingHom.id ℤ) (-1) (by norm_num)) u f (AddMonoidAlgebra.ofCoeff (d (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (RingHom.id ℤ) (-1) (by norm_num)
      (fun _ => by simp) neg_one_character_star f)
    (evaluation_neg_one_eq_two_d f hsign)

/-- The third norm uses conjugation of the fourth root, not exponent reversal
alone. Both the square equation and the conjugation equation are explicit. -/
theorem gOver_norm_of_product_norm {R : Type uR} [CommRing R] [StarRing R]
    [IsDomain R] [CharZero R] (i : R) (hi : i ^ 2 = -1) (hstar : star i = -i)
    (u : ℕ) (f : ProductElem ℤ m) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem R m) (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : R) := by
  exact norm_of_evaluation groupStar
    (partialEval m (Int.castRingHom R) i (fourthRoot_pow_four i hi))
    u f (AddMonoidAlgebra.ofCoeff (gOver i (fun j => (blocks f j).coeff))) hnorm
    (partialEval_groupStar m (Int.castRingHom R) i (fourthRoot_pow_four i hi)
      (fun _ => by simp) (fourthRoot_character_star i hi hstar) f)
    (evaluation_fourthRoot_eq_two_gOver i hi f hsign)

/-- The same cancellation is valid in `ℂ[C_m]`, despite that ring having zero
divisors. This specializes the actual coefficient construction `g`. -/
theorem g_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem ℂ m) (AddMonoidAlgebra.ofCoeff (g (fun j => (blocks f j).coeff))) (ringStar (AddMonoidAlgebra.ofCoeff (g (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : ℂ) :=
  gOver_norm_of_product_norm Complex.I Complex.I_sq (by simp) u f hsign hnorm

/-- Conjugation negates the imaginary unit in the actual Gaussian subring. -/
theorem star_gaussianI : star CyclotomicRings.gaussianI = -CyclotomicRings.gaussianI := by
  apply Subtype.ext
  change star Complex.I = -Complex.I
  simp

/-- The integral Gaussian norm, before any character evaluation or localization. -/
theorem gaussian_g_norm_of_product_norm (u : ℕ) (f : ProductElem ℤ m)
    (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * groupStar f = ((4 * u ^ 2 : ℕ) : ProductElem ℤ m)) :
    Mul.mul (α := Elem CyclotomicRings.GaussianRing m)
        (AddMonoidAlgebra.ofCoeff (gOver CyclotomicRings.gaussianI (fun j => (blocks f j).coeff)))
        (ringStar (AddMonoidAlgebra.ofCoeff (gOver CyclotomicRings.gaussianI (fun j => (blocks f j).coeff)))) =
      scalar m ((u ^ 2 : ℕ) : CyclotomicRings.GaussianRing) :=
  gOver_norm_of_product_norm CyclotomicRings.gaussianI CyclotomicRings.gaussianI_sq
    star_gaussianI u f hsign hnorm

end ActualBinaryElements

/-- The complete binary norm step starts from the original cyclic sign row.
The CRT transport, block signs, doubled evaluation values, full-star
compatibility, and scalar cancellation are all proved in the construction.
No separate norm premise for `c`, `d`, or `g` is accepted. -/
theorem binary_norms_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    Mul.mul (α := Elem ℤ (u ^ 2)) (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.c (fun j => (H j).coeff)))
        (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.c (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : ℤ) ∧
      Mul.mul (α := Elem ℤ (u ^ 2)) (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.d (fun j => (H j).coeff)))
          (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.d (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : ℤ) ∧
      Mul.mul (α := Elem CyclotomicRings.GaussianRing (u ^ 2))
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.gOver CyclotomicRings.gaussianI (fun j => (H j).coeff)))
          (ringStar (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.gOver CyclotomicRings.gaussianI (fun j => (H j).coeff)))) =
        scalar (u ^ 2) ((u ^ 2 : ℕ) : CyclotomicRings.GaussianRing) := by
  let F := BinaryBlocks.crt ℤ u hu f
  have hs : ∀ a, IsSign (F.coeff a) := by
    intro a
    simpa only [F, BinaryBlocks.crt_apply] using
      hsign ((BinaryBlocks.crtIndex u hu).symm a)
  have hn : F * groupStar F = ((4 * u ^ 2 : ℕ) : BinaryBlocks.ProductElem ℤ (u ^ 2)) :=
    BinaryBlocks.crt_norm hu f (4 * u ^ 2) (by simpa only [scalar_natCast] using hnorm)
  exact ⟨c_norm_of_product_norm u F hs hn, d_norm_of_product_norm u F hs hn,
    gaussian_g_norm_of_product_norm u F hs hn⟩

end CirculantHadamard.BinaryNorms

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluation
section
namespace OAI

universe uR uS uT uA


noncomputable section

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]
variable {n : ℕ}

/-- Evaluation at a multiplicative character of the additive cyclic group. -/
def evaluate (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) : Elem R n →+* S :=
  AddMonoidAlgebra.liftNCRingHom φ χ (fun _ _ => Commute.all _ _)

@[simp] theorem evaluate_single (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (a : ZMod n) (r : R) :
    evaluate φ χ (AddMonoidAlgebra.single a r) = φ r * χ (Multiplicative.ofAdd a) :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

@[simp] theorem evaluate_scalar (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (r : R) :
    evaluate φ χ (scalar n r) = φ r := by
  simp only [scalar, evaluate_single]
  change φ r * χ 1 = φ r
  simp

/-- The full finite sum, rather than a sum over an unspecified support. -/
theorem evaluate_apply [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (f : Elem R n) :
    evaluate φ χ f = ∑ a : ZMod n, φ (f.coeff a) * χ (Multiplicative.ofAdd a) := by
  change f.coeff.sum (fun a r => φ r * χ (Multiplicative.ofAdd a)) = _
  exact Finsupp.sum_fintype f.coeff _ (fun _ => by simp)

@[simp] theorem evaluate_ofCoeffs [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (c : ZMod n → R) :
    evaluate φ χ (ofCoeffs c) = ∑ a : ZMod n, φ (c a) * χ (Multiplicative.ofAdd a) :=
  evaluate_apply φ χ (ofCoeffs c)

/-- The trivial character recovers augmentation followed by the coefficient map. -/
theorem evaluate_trivial_eq_augmentation [NeZero n] (φ : R →+* S)
    (f : Elem R n) :
    evaluate φ (1 : Multiplicative (ZMod n) →* S) f = φ (augmentation n f) := by
  simp [evaluate_apply, augmentation_apply, map_sum]

/-- Evaluation commutes with a change of target coefficient ring. -/
theorem map_evaluate [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (ψ : S →+* T) (f : Elem R n) :
    ψ (evaluate φ χ f) = evaluate (ψ.comp φ) (ψ.toMonoidHom.comp χ) f := by
  rw [evaluate_apply, evaluate_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact map_mul ψ (φ (f.coeff a)) (χ (Multiplicative.ofAdd a))

/-- Bundled naturality of character evaluation. -/
theorem map_evaluate_hom [NeZero n] (φ : R →+* S)
    (χ : Multiplicative (ZMod n) →* S) (ψ : S →+* T) :
    ψ.comp (evaluate φ χ) = evaluate (ψ.comp φ) (ψ.toMonoidHom.comp χ) := by
  apply RingHom.ext
  intro f
  exact map_evaluate φ χ ψ f

/-- A target endomorphism intertwines evaluation and the full group-ring star
when it intertwines the coefficient involution and character inversion. -/
theorem evaluate_ringStar_intertwining [StarRing R] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S) (τ : S →+* S)
    (hφ : ∀ r, φ (star r) = τ (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = τ (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = τ (evaluate φ χ f) := by
  rw [evaluate_apply, evaluate_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ ?_
  intro a
  simp only [ringStar_apply, Equiv.neg_apply, map_mul, hφ]
  rw [← hχ]
  simp only [neg_neg]

/-- Character evaluation carries the full group-ring involution to target star. -/
theorem evaluate_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (ringStar f) = star (evaluate φ χ f) :=
  evaluate_ringStar_intertwining φ χ (starRingEnd S) hφ hχ f

/-- The group-ring norm product becomes the usual star norm product. -/
theorem evaluate_mul_ringStar [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) :
    evaluate φ χ (f * ringStar f) = evaluate φ χ f * star (evaluate φ χ f) := by
  rw [map_mul, evaluate_ringStar φ χ hφ hχ]

/-- A proved scalar group-ring norm equation transfers to every compatible
character; the norm equation is not built into the evaluation definition. -/
theorem evaluate_norm_eq [StarRing R] [StarRing S] [NeZero n]
    (φ : R →+* S) (χ : Multiplicative (ZMod n) →* S)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem R n) (r : R) (hf : f * ringStar f = scalar n r) :
    evaluate φ χ f * star (evaluate φ χ f) = φ r := by
  rw [← evaluate_mul_ringStar φ χ hφ hχ, hf, evaluate_scalar]

/-- For integer coefficients, coefficient-star compatibility is automatic. -/
theorem evaluate_int_ringStar {A : Type uA} [CommRing A] [StarRing A] [NeZero n]
    (χ : Multiplicative (ZMod n) →* A)
    (hχ : ∀ a : ZMod n,
      χ (Multiplicative.ofAdd (-a)) = star (χ (Multiplicative.ofAdd a)))
    (f : Elem ℤ n) :
    evaluate (Int.castRingHom A) χ (ringStar f) =
      star (evaluate (Int.castRingHom A) χ f) := by
  exact evaluate_ringStar (Int.castRingHom A) χ (fun r => by simp) hχ f

end CirculantHadamard.CyclicRing

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.PrimeComponents
section
namespace OAI


noncomputable section

namespace CirculantHadamard.PrimeComponents

open scoped BigOperators

def primes (u : ℕ) : Finset ℕ := u.primeFactors

abbrev PrimeIndex (u : ℕ) := {p : ℕ // p ∈ primes u}

def exponent (u p : ℕ) : ℕ := (u ^ 2).factorization p

def order (u p : ℕ) : ℕ := p ^ exponent u p

abbrev Component (u : ℕ) (p : PrimeIndex u) := ZMod (order u p.val)

abbrev PrimaryProduct (u : ℕ) := (p : PrimeIndex u) → Component u p

theorem mem_primes {u p : ℕ} : p ∈ primes u ↔ p.Prime ∧ p ∣ u ∧ u ≠ 0 :=
  Nat.mem_primeFactors

theorem prime_of_mem {u p : ℕ} (hp : p ∈ primes u) : p.Prime :=
  (mem_primes.mp hp).1

theorem dvd_of_mem {u p : ℕ} (hp : p ∈ primes u) : p ∣ u :=
  (mem_primes.mp hp).2.1

theorem primes_nonempty {u : ℕ} (hu : 1 < u) : (primes u).Nonempty :=
  Nat.nonempty_primeFactors.mpr hu

theorem prime_ne_two_of_odd {u p : ℕ} (hu : Odd u) (hp : p ∈ primes u) : p ≠ 2 := by
  intro h
  apply hu.not_two_dvd_nat
  simpa only [h] using dvd_of_mem hp

theorem odd_of_mem {u p : ℕ} (hu : Odd u) (hp : p ∈ primes u) : Odd p :=
  (prime_of_mem hp).odd_of_ne_two (prime_ne_two_of_odd hu hp)

/-- The scalar exponent in local comparison is the exponent in u². -/
theorem exponent_eq_two_mul (u p : ℕ) : exponent u p = 2 * u.factorization p := by
  simp only [exponent, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem exponent_pos {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    0 < exponent u p := by
  apply (prime_of_mem hp).factorization_pos_of_dvd (pow_ne_zero 2 hu.ne')
  exact (dvd_of_mem hp).trans (dvd_pow_self u (by decide : 2 ≠ 0))

theorem order_pos {u p : ℕ} (hp : p ∈ primes u) : 0 < order u p :=
  pow_pos (prime_of_mem hp).pos _

instance componentOrder_neZero (u : ℕ) (p : PrimeIndex u) : NeZero (order u p.val) :=
  ⟨(order_pos p.property).ne'⟩

theorem prime_dvd_order {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    p ∣ order u p := dvd_pow_self p (exponent_pos hu hp).ne'

theorem order_dvd_square (u p : ℕ) : order u p ∣ u ^ 2 :=
  Nat.ordProj_dvd (u ^ 2) p

/-- This is the full primary factor: the next power does not divide u². -/
theorem next_power_not_dvd {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    ¬p ^ (exponent u p + 1) ∣ u ^ 2 :=
  Nat.pow_succ_factorization_not_dvd (pow_ne_zero 2 hu.ne') (prime_of_mem hp)

def cofactor (u p : ℕ) : ℕ := u ^ 2 / order u p

theorem order_mul_cofactor (u p : ℕ) : order u p * cofactor u p = u ^ 2 := by
  exact Nat.mul_div_cancel' (order_dvd_square u p)

theorem cofactor_not_dvd {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    ¬p ∣ cofactor u p :=
  Nat.not_dvd_ordCompl (prime_of_mem hp) (pow_ne_zero 2 hu.ne')

theorem cofactor_coprime {u p : ℕ} (hu : 0 < u) (hp : p ∈ primes u) :
    Nat.Coprime p (cofactor u p) :=
  Nat.coprime_ordCompl (prime_of_mem hp) (pow_ne_zero 2 hu.ne')

theorem prod_order_finset (u : ℕ) (hu : 0 < u) :
    (∏ p ∈ primes u, order u p) = u ^ 2 := by
  have h := Nat.prod_factorization_pow_eq_self (pow_ne_zero 2 hu.ne')
  simpa only [Nat.prod_factorization_eq_prod_primeFactors,
    Nat.primeFactors_pow u (by decide : 2 ≠ 0), primes, order, exponent] using h

theorem prod_order (u : ℕ) (hu : 0 < u) :
    (∏ p : PrimeIndex u, order u p.val) = u ^ 2 := by
  change (∏ p : (primes u), order u p.val) = u ^ 2
  rw [Finset.prod_coe_sort]
  exact prod_order_finset u hu

theorem pairwise_coprime (u : ℕ) :
    Pairwise (fun p q : PrimeIndex u => Nat.Coprime (order u p.val) (order u q.val)) := by
  intro p q hpq
  exact Nat.coprime_pow_primes _ _ (prime_of_mem p.property) (prime_of_mem q.property)
    (fun h => hpq (Subtype.ext h))

/-- The actual finite Chinese remainder equivalence, with no chosen-map premise. -/
def crtRing (u : ℕ) (hu : 0 < u) : ZMod (u ^ 2) ≃+* PrimaryProduct u :=
  (ZMod.ringEquivCongr (prod_order u hu).symm).trans
    (ZMod.prodEquivPi (fun p : PrimeIndex u => order u p.val) (pairwise_coprime u))

def crt (u : ℕ) (hu : 0 < u) : ZMod (u ^ 2) ≃+ PrimaryProduct u :=
  (crtRing u hu).toAddEquiv

@[simp] theorem crt_intCast (u : ℕ) (hu : 0 < u) (z : ℤ) (p : PrimeIndex u) :
    crt u hu (z : ZMod (u ^ 2)) p = (z : Component u p) := by
  change (crtRing u hu (z : ZMod (u ^ 2))) p = _
  exact congrArg (fun y : PrimaryProduct u => y p) (map_intCast (crtRing u hu) z)

@[simp] theorem crt_natCast (u : ℕ) (hu : 0 < u) (z : ℕ) (p : PrimeIndex u) :
    crt u hu (z : ZMod (u ^ 2)) p = (z : Component u p) := by
  change (crtRing u hu (z : ZMod (u ^ 2))) p = _
  exact congrArg (fun y : PrimaryProduct u => y p) (map_natCast (crtRing u hu) z)

/-- Every CRT coordinate is literal reduction from ZMod(u²) to the full p-power. -/
theorem crt_apply (u : ℕ) (hu : 0 < u) (x : ZMod (u ^ 2)) (p : PrimeIndex u) :
    crt u hu x p = (ZMod.cast x : Component u p) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [crt_intCast, ZMod.cast_intCast (order_dvd_square u p.val)]

def primaryGenerator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) : ZMod (u ^ 2) :=
  (crt u hu).symm (Pi.single p (1 : Component u p))

@[simp] theorem crt_primaryGenerator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    crt u hu (primaryGenerator u hu p) = Pi.single p (1 : Component u p) :=
  (crt u hu).apply_symm_apply _

@[simp] theorem crt_primaryGenerator_same (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    crt u hu (primaryGenerator u hu p) p = 1 := by
  rw [crt_primaryGenerator, Pi.single_eq_same]

@[simp] theorem crt_primaryGenerator_ne (u : ℕ) (hu : 0 < u)
    (p q : PrimeIndex u) (hqp : q ≠ p) :
    crt u hu (primaryGenerator u hu p) q = 0 := by
  rw [crt_primaryGenerator, Pi.single_eq_of_ne hqp]

/-- The chosen primary generator has exactly the full primary order. -/
theorem primaryGenerator_addOrderOf (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    addOrderOf (primaryGenerator u hu p) = order u p.val := by
  rw [primaryGenerator, AddEquiv.addOrderOf_eq]
  have h := addOrderOf_injective (AddMonoidHom.single (Component u) p)
    (Pi.single_injective p) (1 : Component u p)
  exact h.trans (ZMod.addOrderOf_one (order u p.val))

end CirculantHadamard.PrimeComponents

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.PrimeCharacterEvaluations
section
namespace OAI

universe uR uS uT uA


noncomputable section

namespace CirculantHadamard.PrimeCharacterEvaluations

open scoped BigOperators
open CyclicRing

section WeightedProjection

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]
variable {n m : ℕ}

/-- A character with values in the actual residual cyclic group algebra. -/
def weightedCharacter (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) :
    Multiplicative (ZMod n) →* Elem S m where
  toFun g := AddMonoidAlgebra.single (f g.toAdd) (χ g)
  map_one' := by
    change AddMonoidAlgebra.single (f 0) (χ 1) = 1
    simp only [map_zero, map_one, AddMonoidAlgebra.one_def]
  map_mul' g h := by
    change AddMonoidAlgebra.single (f (g.toAdd + h.toAdd)) (χ (g * h)) = _
    simp only [map_add, map_mul, AddMonoidAlgebra.single_mul_single]

@[simp] theorem weightedCharacter_apply (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) (g : ZMod n) :
    weightedCharacter f χ (Multiplicative.ofAdd g) =
      AddMonoidAlgebra.single (f g) (χ (Multiplicative.ofAdd g)) := rfl

/-- Coefficients are mapped by `φ`, the coordinate `f` is kept as a variable,
and all other character values become coefficients. -/
def weightedProjection (φ : R →+* S) (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) : Elem R n →+* Elem S m :=
  evaluate (AddMonoidAlgebra.singleZeroRingHom.comp φ) (weightedCharacter f χ)

@[simp] theorem weightedProjection_single (φ : R →+* S)
    (f : ZMod n →+ ZMod m) (χ : Multiplicative (ZMod n) →* S)
    (g : ZMod n) (r : R) :
    weightedProjection φ f χ (AddMonoidAlgebra.single g r) =
      AddMonoidAlgebra.single (f g) (φ r * χ (Multiplicative.ofAdd g)) := by
  simp only [weightedProjection, evaluate_single, RingHom.comp_apply,
    AddMonoidAlgebra.singleZeroRingHom_apply, AddMonoidAlgebra.singleAddHom,
    weightedCharacter_apply,
    AddMonoidAlgebra.single_mul_single, zero_add]

@[simp] theorem weightedProjection_scalar (φ : R →+* S)
    (f : ZMod n →+ ZMod m) (χ : Multiplicative (ZMod n) →* S) (r : R) :
    weightedProjection φ f χ (scalar n r) = scalar m (φ r) := by
  rw [scalar, weightedProjection_single, map_zero]
  change AddMonoidAlgebra.single 0 (φ r * χ 1) = _
  simp only [map_one, mul_one, scalar]

private theorem toMultiplicative_apply (f : ZMod n →+ ZMod m) (a : ZMod n) :
    f.toMultiplicative (Multiplicative.ofAdd a) = Multiplicative.ofAdd (f a) := rfl

/-- Subsequent evaluation is exactly the product of the evaluated coefficients
and the character of the retained coordinate. -/
theorem evaluate_weightedProjection (φ : R →+* S) (ψ : S →+* T)
    (f : ZMod n →+ ZMod m) (χ : Multiplicative (ZMod n) →* S)
    (θ : Multiplicative (ZMod m) →* T) :
    (evaluate ψ θ).comp (weightedProjection φ f χ) =
      evaluate (ψ.comp φ)
        ((ψ.toMonoidHom.comp χ) * (θ.comp f.toMultiplicative)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, weightedProjection_single, evaluate_single,
      map_zero, map_mul, MonoidHom.mul_apply, MonoidHom.comp_apply,
      toMultiplicative_apply, RingHom.toMonoidHom_eq_coe]
    simp
  · intro g
    simp only [RingHom.comp_apply, weightedProjection_single, evaluate_single,
      map_one, one_mul, MonoidHom.mul_apply, MonoidHom.comp_apply,
      toMultiplicative_apply, RingHom.toMonoidHom_eq_coe]
    rfl

/-- Norm preservation is a consequence of the constructed ring homomorphism.
In particular it does not require the residual group algebra to be a domain. -/
theorem weightedProjection_product (φ : R →+* S) (f : ZMod n →+ ZMod m)
    (χ : Multiplicative (ZMod n) →* S) (x y : Elem R n) (r : R)
    (hxy : x * y = scalar n r) :
    weightedProjection φ f χ x * weightedProjection φ f χ y = scalar m (φ r) := by
  rw [← map_mul, hxy, weightedProjection_scalar]

end WeightedProjection

open PrimeComponents CyclotomicRings

/-- The actual CRT coordinate, without a chosen-decomposition hypothesis. -/
def coordinate (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    ZMod (u ^ 2) →+ Component u p where
  toFun a := crt u hu a p
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem coordinate_generator (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    coordinate u hu p (primaryGenerator u hu p) = 1 :=
  crt_primaryGenerator_same u hu p

@[simp] theorem coordinate_generator_ne (u : ℕ) (hu : 0 < u)
    (p q : PrimeIndex u) (h : q ≠ p) :
    coordinate u hu q (primaryGenerator u hu p) = 0 :=
  crt_primaryGenerator_ne u hu p q h

section RootCharacters
variable {A : Type uA} [CommMonoid A]

theorem root_order_pow (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (r : A) (hr : r ^ p.val = 1) : r ^ order u p.val = 1 := by
  obtain ⟨t, ht⟩ := prime_dvd_order hu p.property
  rw [ht, pow_mul, hr, one_pow]

def componentCharacter (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (r : A) (hr : r ^ p.val = 1) : Multiplicative (ZMod (u ^ 2)) →* A :=
  (CyclicPolynomial.powerCharacter (order u p.val) r (root_order_pow u hu p r hr)).comp
    (coordinate u hu p).toMultiplicative

@[simp] theorem componentCharacter_apply (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (r : A) (hr : r ^ p.val = 1) (a : ZMod (u ^ 2)) :
    componentCharacter u hu p r hr (Multiplicative.ofAdd a) =
      r ^ (coordinate u hu p a).val := rfl

@[simp] theorem componentCharacter_generator (u : ℕ) (hu : 0 < u)
    (p : PrimeIndex u) (r : A) (hr : r ^ p.val = 1) :
    componentCharacter u hu p r hr (Multiplicative.ofAdd (primaryGenerator u hu p)) = r := by
  change CyclicPolynomial.powerCharacter (order u p.val) r (root_order_pow u hu p r hr) (Multiplicative.ofAdd
    (coordinate u hu p (primaryGenerator u hu p))) = r
  rw [coordinate_generator, CyclicPolynomial.powerCharacter_generator]

@[simp] theorem componentCharacter_generator_ne (u : ℕ) (hu : 0 < u)
    (p q : PrimeIndex u) (h : q ≠ p) (r : A) (hr : r ^ q.val = 1) :
    componentCharacter u hu q r hr (Multiplicative.ofAdd (primaryGenerator u hu p)) = 1 := by
  rw [componentCharacter_apply, coordinate_generator_ne u hu p q h]
  simp

/-- A finite product of the actual primary-coordinate characters. -/
def rootsCharacter (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) (S : Finset (PrimeIndex u)) :
    Multiplicative (ZMod (u ^ 2)) →* A :=
  ∏ p ∈ S, componentCharacter u hu p (r p) (hr p)

@[simp] theorem rootsCharacter_apply (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) (S : Finset (PrimeIndex u)) (a : ZMod (u ^ 2)) :
    rootsCharacter u hu r hr S (Multiplicative.ofAdd a) =
      ∏ p ∈ S, r p ^ (coordinate u hu p a).val := by
  simp [rootsCharacter]

@[simp] theorem rootsCharacter_empty (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) : rootsCharacter u hu r hr ∅ = 1 := by
  simp [rootsCharacter]

theorem rootsCharacter_generator (u : ℕ) (hu : 0 < u) (r : PrimeIndex u → A)
    (hr : ∀ p, r p ^ p.val = 1) (S : Finset (PrimeIndex u)) (p : PrimeIndex u) :
    rootsCharacter u hu r hr S (Multiplicative.ofAdd (primaryGenerator u hu p)) =
      if p ∈ S then r p else 1 := by
  classical
  simp only [rootsCharacter, MonoidHom.finsetProd_apply]
  have heq : ∀ q ∈ S, componentCharacter u hu q (r q) (hr q)
      (Multiplicative.ofAdd (primaryGenerator u hu p)) = if q = p then r p else 1 := by
    intro q _
    by_cases h : q = p
    · subst q
      simp only [componentCharacter_generator, ite_true]
    · simp [h, componentCharacter_generator_ne u hu p q h]
  rw [Finset.prod_congr rfl heq]
  simp

end RootCharacters

/-- The chosen primitive prime root in the literal global coefficient ring. -/
def rhoB (u : ℕ) (p : PrimeIndex u) : B u :=
  ⟨rho p.val, rho_mem_B u p.val p.property⟩

@[simp] theorem coe_rhoB (u : ℕ) (p : PrimeIndex u) :
    (rhoB u p : ℂ) = rho p.val := rfl

theorem rhoB_pow (u : ℕ) (p : PrimeIndex u) : rhoB u p ^ p.val = 1 :=
  Subtype.ext (rho_pow p.val (prime_of_mem p.property).ne_zero)

theorem rhoB_ne_one (u : ℕ) (p : PrimeIndex u) : rhoB u p ≠ 1 := by
  intro h
  exact (rho_isPrimitiveRoot p.val (prime_of_mem p.property).ne_zero).ne_one
    (prime_of_mem p.property).one_lt (congrArg Subtype.val h)

def subsetCharacter (u : ℕ) (hu : 0 < u) (S : Finset (PrimeIndex u)) :
    Multiplicative (ZMod (u ^ 2)) →* B u :=
  rootsCharacter u hu (rhoB u) (rhoB_pow u) S

@[simp] theorem subsetCharacter_empty (u : ℕ) (hu : 0 < u) :
    subsetCharacter u hu ∅ = 1 := rootsCharacter_empty _ _ _ _

theorem subsetCharacter_generator (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (p : PrimeIndex u) :
    subsetCharacter u hu S (Multiplicative.ofAdd (primaryGenerator u hu p)) =
      if p ∈ S then rhoB u p else 1 := rootsCharacter_generator _ _ _ _ _ _

theorem subsetCharacter_nonempty (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    ∃ a : ZMod (u ^ 2), subsetCharacter u hu S (Multiplicative.ofAdd a) ≠ 1 := by
  obtain ⟨p, hp⟩ := hS
  refine ⟨primaryGenerator u hu p, ?_⟩
  rw [subsetCharacter_generator, if_pos hp]
  exact rhoB_ne_one u p

def subsetEvaluation (u : ℕ) (hu : 0 < u) (S : Finset (PrimeIndex u)) :
    Elem GaussianRing (u ^ 2) →+* B u :=
  evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S)

/-- The omitted root is replaced by one; all remaining roots lie in the actual away ring. -/
def rhoAway (u : ℕ) (p q : PrimeIndex u) : awayRing u p.val := by
  classical
  exact if h : q = p then 1 else
    ⟨rho q.val, rho_mem_awayRing u p.val q.val q.property
      (fun he => h (Subtype.ext he))⟩

theorem rhoAway_pow (u : ℕ) (p q : PrimeIndex u) : rhoAway u p q ^ q.val = 1 := by
  classical
  by_cases h : q = p
  · simp [rhoAway, h]
  · apply Subtype.ext
    simpa [rhoAway, h] using rho_pow q.val (prime_of_mem q.property).ne_zero

def awayCharacter (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) : Multiplicative (ZMod (u ^ 2)) →* awayRing u p.val :=
  rootsCharacter u hu (rhoAway u p) (rhoAway_pow u p) (S.erase p)

/-- Leave precisely the full p-primary cyclic coordinate unevaluated. -/
def partialEvaluation (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    Elem GaussianRing (u ^ 2) →+* Elem (awayRing u p.val) (order u p.val) :=
  weightedProjection (gaussianToAway u p.val).toRingHom (coordinate u hu p)
    (awayCharacter u hu p S)

theorem partialEvaluation_product (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (x y : Elem GaussianRing (u ^ 2))
    (hxy : x * y = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    partialEvaluation u hu p S x * partialEvaluation u hu p S y =
      scalar (order u p.val) ((u ^ 2 : ℕ) : awayRing u p.val) := by
  unfold partialEvaluation
  simpa only [map_natCast] using weightedProjection_product
    (gaussianToAway u p.val).toRingHom (coordinate u hu p) (awayCharacter u hu p S)
    x y ((u ^ 2 : ℕ) : GaussianRing) hxy

theorem awayCharacter_map (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    (awayInclusion u p.val).toMonoidHom.comp (awayCharacter u hu p S) =
      subsetCharacter u hu (S.erase p) := by
  classical
  apply MonoidHom.ext
  intro a
  change awayInclusion u p.val
    (rootsCharacter u hu (rhoAway u p) (rhoAway_pow u p) (S.erase p)
      (Multiplicative.ofAdd a.toAdd)) =
    rootsCharacter u hu (rhoB u) (rhoB_pow u) (S.erase p)
      (Multiplicative.ofAdd a.toAdd)
  simp only [rootsCharacter_apply, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro q hq
  have hqp := (Finset.mem_erase.mp hq).1
  congr 1
  apply Subtype.ext
  simp [rhoAway, hqp, rhoB]

theorem subsetCharacter_insert (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    subsetCharacter u hu (insert p S) =
      subsetCharacter u hu (S.erase p) * componentCharacter u hu p (rhoB u p) (rhoB_pow u p) := by
  classical
  have hi : insert p (S.erase p) = insert p S := by
    ext q
    by_cases h : q = p <;> simp [h]
  calc
    subsetCharacter u hu (insert p S) = subsetCharacter u hu (insert p (S.erase p)) :=
      congrArg (subsetCharacter u hu) hi.symm
    _ = _ := by
      simp only [subsetCharacter, rootsCharacter, Finset.prod_insert (Finset.notMem_erase p S),
        mul_comm]

/-- Evaluate the remaining p-primary variable at one. -/
def partialAtOne (u : ℕ) (p : PrimeIndex u) :
    Elem (awayRing u p.val) (order u p.val) →+* B u :=
  evaluate (awayInclusion u p.val).toRingHom 1

/-- Evaluate the remaining full p-primary variable at the selected pth root. -/
def partialAtRoot (u : ℕ) (hu : 0 < u) (p : PrimeIndex u) :
    Elem (awayRing u p.val) (order u p.val) →+* B u :=
  evaluate (awayInclusion u p.val).toRingHom
    (CyclicPolynomial.powerCharacter (order u p.val) (rhoB u p)
      (root_order_pow u hu p (rhoB u p) (rhoB_pow u p)))

private theorem gaussian_away_comp (u p : ℕ) :
    (awayInclusion u p).toRingHom.comp (gaussianToAway u p).toRingHom =
      (gaussianToB u).toRingHom := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  exact (coe_awayInclusion u p (gaussianToAway u p r)).trans
    ((coe_gaussianToAway u p r).trans (coe_gaussianToB u r).symm)

theorem partialEvaluation_at_one (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    (partialAtOne u p).comp (partialEvaluation u hu p S) =
      subsetEvaluation u hu (S.erase p) := by
  unfold partialAtOne partialEvaluation
  rw [evaluate_weightedProjection]
  rw [gaussian_away_comp]
  have ht : (1 : Multiplicative (Component u p) →* B u).comp
      (coordinate u hu p).toMultiplicative = 1 := by ext; rfl
  rw [ht, mul_one]
  exact congrArg (evaluate (gaussianToB u).toRingHom) (awayCharacter_map u hu p S)

theorem partialEvaluation_at_root (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) :
    (partialAtRoot u hu p).comp (partialEvaluation u hu p S) =
      subsetEvaluation u hu (insert p S) := by
  unfold partialAtRoot partialEvaluation
  rw [evaluate_weightedProjection]
  rw [gaussian_away_comp]
  change evaluate (gaussianToB u).toRingHom
    (((awayInclusion u p.val).toMonoidHom.comp (awayCharacter u hu p S)) *
      componentCharacter u hu p (rhoB u p) (rhoB_pow u p)) = _
  rw [awayCharacter_map, ← subsetCharacter_insert]
  rfl

@[simp] theorem partialEvaluation_at_one_apply (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (hp : p ∉ S) (x : Elem GaussianRing (u ^ 2)) :
    partialAtOne u p (partialEvaluation u hu p S x) = subsetEvaluation u hu S x := by
  have h := congrArg (fun f : Elem GaussianRing (u ^ 2) →+* B u => f x)
    (partialEvaluation_at_one u hu p S)
  simpa only [RingHom.comp_apply, Finset.erase_eq_of_notMem hp] using h

@[simp] theorem partialEvaluation_at_root_apply (u : ℕ) (hu : 0 < u) (p : PrimeIndex u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2)) :
    partialAtRoot u hu p (partialEvaluation u hu p S x) =
      subsetEvaluation u hu (insert p S) x :=
  congrArg (fun f : Elem GaussianRing (u ^ 2) →+* B u => f x)
    (partialEvaluation_at_root u hu p S)

theorem rhoB_mul_star (u : ℕ) (p : PrimeIndex u) : rhoB u p * star (rhoB u p) = 1 :=
  Subtype.ext (rho_mul_star p.val)

theorem subsetCharacter_mul_star (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (a : ZMod (u ^ 2)) :
    subsetCharacter u hu S (Multiplicative.ofAdd a) *
      star (subsetCharacter u hu S (Multiplicative.ofAdd a)) = 1 := by
  unfold subsetCharacter
  rw [rootsCharacter_apply, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p _
  rw [star_pow, ← mul_pow, rhoB_mul_star, one_pow]

theorem subsetCharacter_neg (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (a : ZMod (u ^ 2)) :
    subsetCharacter u hu S (Multiplicative.ofAdd (-a)) =
      star (subsetCharacter u hu S (Multiplicative.ofAdd a)) := by
  let χ := subsetCharacter u hu S
  have hi : χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) = 1 := by
    rw [← map_mul]
    change χ (Multiplicative.ofAdd (-a + a)) = 1
    simp
  have hs := subsetCharacter_mul_star u hu S a
  change χ (Multiplicative.ofAdd a) * star (χ (Multiplicative.ofAdd a)) = 1 at hs
  calc
    χ (Multiplicative.ofAdd (-a)) = χ (Multiplicative.ofAdd (-a)) * 1 := (mul_one _).symm
    _ = χ (Multiplicative.ofAdd (-a)) *
        (χ (Multiplicative.ofAdd a) * star (χ (Multiplicative.ofAdd a))) := by rw [hs]
    _ = star (χ (Multiplicative.ofAdd a)) := by rw [← mul_assoc, hi, one_mul]

theorem subsetEvaluation_star (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2)) :
    subsetEvaluation u hu S (ringStar x) = star (subsetEvaluation u hu S x) := by
  exact evaluate_ringStar (gaussianToB u).toRingHom (subsetCharacter u hu S)
    (gaussianToB_star u) (subsetCharacter_neg u hu S) x

theorem subsetEvaluation_norm (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    subsetEvaluation u hu S x * star (subsetEvaluation u hu S x) = ((u ^ 2 : ℕ) : B u) := by
  simpa only [subsetEvaluation, map_natCast] using evaluate_norm_eq
    (gaussianToB u).toRingHom (subsetCharacter u hu S)
    (gaussianToB_star u) (subsetCharacter_neg u hu S) x ((u ^ 2 : ℕ) : GaussianRing) hx

theorem subsetEvaluation_ne_zero (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    subsetEvaluation u hu S x ≠ 0 := by
  intro h
  have hn := subsetEvaluation_norm u hu S x hx
  rw [h, zero_mul] at hn
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero 2 hu.ne')) hn.symm

/-- Every complex embedding has the required norm. Compatibility with conjugation
is derived from the actual adjoined roots in `map_star_B`. -/
theorem subsetEvaluation_map_norm (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (σ : B u →+* ℂ) : ‖σ (subsetEvaluation u hu S x)‖ = (u : ℝ) := by
  have hn := congrArg (fun z : B u => ‖σ z‖) (subsetEvaluation_norm u hu S x hx)
  simp only [map_mul, map_star_B, norm_mul, norm_star, map_natCast] at hn
  rw [RCLike.norm_natCast, Nat.cast_pow] at hn
  nlinarith [norm_nonneg (σ (subsetEvaluation u hu S x)), (show (0 : ℝ) ≤ (u : ℝ) from Nat.cast_nonneg u)]

end CirculantHadamard.PrimeCharacterEvaluations

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryEvaluation
section
namespace OAI

universe uR


noncomputable section

namespace CirculantHadamard.BinaryEvaluation

open scoped BigOperators
open CyclicRing BinaryCoefficients CyclotomicRings PrimeComponents
open PrimeCharacterEvaluations

/- Select the canonical multiplication action directly. This avoids searching
through the concrete subalgebra's unrelated inherited scalar actions. -/
local instance gaussianSelfScalar : SMulZeroClass GaussianRing GaussianRing where
  smul r x := r * x
  smul_zero := mul_zero

local instance gaussianCoeffScalar (n : ℕ) :
    SMulZeroClass GaussianRing (ZMod n →₀ GaussianRing) := Finsupp.smulZeroClass

/-- The canonical coefficient action, with its group-algebra result type fixed. -/
def gaussianScale {n : ℕ} (r : GaussianRing) (x : Elem GaussianRing n) :
    Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff
    (@SMul.smul GaussianRing (ZMod n →₀ GaussianRing)
      (gaussianCoeffScalar n).toSMul r x.coeff)

@[simp] theorem gaussianScale_apply {n : ℕ} (r : GaussianRing)
    (x : Elem GaussianRing n) (a : ZMod n) : (gaussianScale r x).coeff a = r * x.coeff a := rfl

section CoefficientCast

variable {R : Type uR} [CommRing R] {n : ℕ} [NeZero n]

theorem castCoeffs_add [NeZero n] (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f + g).coeff) =
      AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff) +
        AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  change ((f.coeff x + g.coeff x : ℤ) : R) = (f.coeff x : R) + (g.coeff x : R)
  exact Int.cast_add _ _

theorem castCoeffs_sub [NeZero n] (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f - g).coeff) =
      AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff) -
        AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  change ((f.coeff x - g.coeff x : ℤ) : R) = (f.coeff x : R) - (g.coeff x : R)
  exact Int.cast_sub _ _

theorem castCoeffs_mul (f g : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (f * g).coeff) =
      Mul.mul (α := Elem R n) (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))
        (AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff)) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  calc
    (((f * g).coeff x : ℤ) : R) = ∑ j, (f.coeff j : R) * (g.coeff (x - j) : R) := by
      rw [CyclicRing.mul_apply]
      simp only [Int.cast_sum, Int.cast_mul]
    _ = _ := (CyclicRing.mul_apply (AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) f.coeff))
      (AddMonoidAlgebra.ofCoeff (castCoeffs g.coeff)) x).symm

theorem castCoeffs_ringStar [StarRing R] (f : Elem ℤ n) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (ringStar f).coeff) =
      ringStar (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff)) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  simp

theorem castCoeffs_scalar [NeZero n] (r : ℤ) :
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) (scalar n r).coeff) =
      scalar n (r : R) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro x
  simp [scalar_apply]

/-- Coefficient maps preserve the norm equation. -/
theorem castCoeffs_norm [StarRing R] (f : Elem ℤ n) (r : ℕ)
    (hf : f * ringStar f = scalar n (r : ℤ)) :
    Mul.mul (α := Elem R n) (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))
      (ringStar (AddMonoidAlgebra.ofCoeff (castCoeffs f.coeff))) = scalar n (r : R) := by
  have h := congrArg (fun z : Elem ℤ n =>
    AddMonoidAlgebra.ofCoeff (castCoeffs (R := R) z.coeff)) hf
  simpa only [castCoeffs_mul, castCoeffs_ringStar, castCoeffs_scalar,
    Int.cast_natCast] using h

end CoefficientCast

section GaussianBlocks

variable {n : ℕ} [NeZero n]

def aG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (a (fun j => (H j).coeff)))
def bG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (b (fun j => (H j).coeff)))
def cG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (c (fun j => (H j).coeff)))
def dG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (d (fun j => (H j).coeff)))
def gG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (gOver gaussianI (fun j => (H j).coeff))
def UG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (UOver gaussianI (fun j => (H j).coeff))
def JG : Elem GaussianRing n := AddMonoidAlgebra.ofCoeff (JOver GaussianRing)

theorem cG_eq (H : Fin 4 → Elem ℤ n) : cG H = aG H + bG H :=
  castCoeffs_add (AddMonoidAlgebra.ofCoeff (a (fun j => (H j).coeff)))
    (AddMonoidAlgebra.ofCoeff (b (fun j => (H j).coeff)))

theorem dG_eq (H : Fin 4 → Elem ℤ n) : dG H = aG H - bG H :=
  castCoeffs_sub (AddMonoidAlgebra.ofCoeff (a (fun j => (H j).coeff)))
    (AddMonoidAlgebra.ofCoeff (b (fun j => (H j).coeff)))

theorem gG_eq {H : Fin 4 → Elem ℤ n} (hH : Signs (fun j => (H j).coeff)) :
    gG H = aG H + gaussianScale gaussianI (bG H) -
      (gaussianScale (1 + gaussianI) JG + gaussianScale 2 (UG H)) := by
  calc
    gG H = aG H + gaussianScale gaussianI (bG H) -
        Add.add (α := Elem GaussianRing n)
          (AddMonoidAlgebra.ofCoeff (castCoeffs (H 2).coeff))
          (gaussianScale gaussianI (AddMonoidAlgebra.ofCoeff (castCoeffs (H 3).coeff))) := by
      apply AddMonoidAlgebra.coeff_injective
      have h := gOver_eq_ab gaussianI hH
      rw [sub_sub] at h
      simp only [gG, aG, bG, gaussianScale, AddMonoidAlgebra.coeff_sub,
        AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_ofCoeff]
      convert h using 1; rfl
    _ = _ := by
      apply congrArg
        (fun z : Elem GaussianRing n => aG H + gaussianScale gaussianI (bG H) - z)
      apply AddMonoidAlgebra.coeff_injective
      have h := binary_identity_over gaussianI hH
      simp only [gaussianScale, JG, UG, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_ofCoeff]
      convert h using 1 <;> rfl

theorem cG_norm (H : Fin 4 → Elem ℤ n) (r : ℕ)
    (hc : Mul.mul (α := Elem ℤ n)
      (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff)))
      (ringStar (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff)))) =
      scalar n (r : ℤ)) :
    cG H * ringStar (cG H) = scalar n (r : GaussianRing) :=
  castCoeffs_norm (AddMonoidAlgebra.ofCoeff (c (fun j => (H j).coeff))) r hc

theorem dG_norm (H : Fin 4 → Elem ℤ n) (r : ℕ)
    (hd : Mul.mul (α := Elem ℤ n)
      (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff)))
      (ringStar (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff)))) =
      scalar n (r : ℤ)) :
    dG H * ringStar (dG H) = scalar n (r : GaussianRing) :=
  castCoeffs_norm (AddMonoidAlgebra.ofCoeff (d (fun j => (H j).coeff))) r hd

end GaussianBlocks

section Values

variable (u : ℕ) [NeZero u] (hu : 0 < u)

def iB : B u := gaussianToB u gaussianI

def aValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (aG H)
def bValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (bG H)
def cValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (cG H)
def dValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (dG H)
def gValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (gG H)
def UValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (UG H)
def JValue (S : Finset (PrimeIndex u)) : B u := subsetEvaluation u hu S JG

theorem subsetEvaluation_smul (S : Finset (PrimeIndex u)) (r : GaussianRing)
    (x : Elem GaussianRing (u ^ 2)) :
    subsetEvaluation u hu S (gaussianScale r x) =
      gaussianToB u r * subsetEvaluation u hu S x := by
  change evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S) _ =
    gaussianToB u r * evaluate (gaussianToB u).toRingHom (subsetCharacter u hu S) x
  rw [evaluate_apply, evaluate_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change gaussianToB u (r * x.coeff a) * subsetCharacter u hu S (Multiplicative.ofAdd a) =
    gaussianToB u r *
      (gaussianToB u (x.coeff a) * subsetCharacter u hu S (Multiplicative.ofAdd a))
  rw [map_mul, mul_assoc]

theorem cValue_eq (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) :
    cValue u hu H S = aValue u hu H S + bValue u hu H S := by
  exact congrArg (subsetEvaluation u hu S) (cG_eq H) |>.trans (map_add _ _ _)

theorem dValue_eq (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) :
    dValue u hu H S = aValue u hu H S - bValue u hu H S := by
  exact congrArg (subsetEvaluation u hu S) (dG_eq H) |>.trans (map_sub _ _ _)

theorem gValue_eq {H : Fin 4 → Elem ℤ (u ^ 2)} (hH : Signs (fun j => (H j).coeff))
    (S : Finset (PrimeIndex u)) :
    gValue u hu H S = aValue u hu H S + iB u * bValue u hu H S -
      ((1 + iB u) * JValue u hu S + 2 * UValue u hu H S) := by
  have h := congrArg (subsetEvaluation u hu S) (gG_eq hH)
  simpa [map_add, map_sub, map_ofNat, subsetEvaluation_smul, iB, gValue, aValue, bValue,
    JValue, UValue] using h

theorem evaluated_norms (H : Fin 4 → Elem ℤ (u ^ 2))
    (hc : cG H * ringStar (cG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hd : dG H * ringStar (dG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hg : gG H * ringStar (gG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (S : Finset (PrimeIndex u)) :
    cValue u hu H S * star (cValue u hu H S) = ((u ^ 2 : ℕ) : B u) ∧
      dValue u hu H S * star (dValue u hu H S) = ((u ^ 2 : ℕ) : B u) ∧
      gValue u hu H S * star (gValue u hu H S) = ((u ^ 2 : ℕ) : B u) :=
  ⟨subsetEvaluation_norm u hu S (cG H) hc,
    subsetEvaluation_norm u hu S (dG H) hd,
    subsetEvaluation_norm u hu S (gG H) hg⟩

end Values

/-- All three Gaussian norm equations come from the original cyclic sign row. -/
theorem gaussian_norms_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    cG H * ringStar (cG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) ∧
      dG H * ringStar (dG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) ∧
      gG H * ringStar (gG H) = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) := by
  obtain ⟨hc, hd, hg⟩ := BinaryNorms.binary_norms_of_cyclic_norm hu f hsign hnorm
  exact ⟨cG_norm _ (u ^ 2) hc, dG_norm _ (u ^ 2) hd, hg⟩

/-- Actual subset evaluations of `c,d,g` all have star norm `u²`,
without independent binary-element norm assumptions. -/
theorem binary_evaluation_of_cyclic_norm {u : ℕ} [NeZero u] (hu : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ))
    (S : Finset (PrimeIndex u)) :
    let hp : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
    let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hu f)
    cValue u hp H S * star (cValue u hp H S) = ((u ^ 2 : ℕ) : B u) ∧
      dValue u hp H S * star (dValue u hp H S) = ((u ^ 2 : ℕ) : B u) ∧
      gValue u hp H S * star (gValue u hp H S) = ((u ^ 2 : ℕ) : B u) := by
  obtain ⟨hc, hd, hg⟩ := gaussian_norms_of_cyclic_norm hu f hsign hnorm
  exact evaluated_norms u (Nat.pos_of_ne_zero (NeZero.ne u)) _ hc hd hg S

end CirculantHadamard.BinaryEvaluation

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.LocalizationMaps
section
namespace OAI

universe uA uB


namespace CirculantHadamard

section LocalizationMap

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]

/-- The actual map from the localization at a contracted prime ideal. -/
noncomputable def localizationAtComapMap (f : A →+* B) (m : Ideal B) [m.IsPrime] :
    Localization.AtPrime (m.comap f) →+* Localization.AtPrime m :=
  Localization.localRingHom (m.comap f) m f rfl

/-- The induced map agrees with the original ring map on coefficients. -/
@[simp] theorem localizationAtComapMap_algebraMap (f : A →+* B)
    (m : Ideal B) [m.IsPrime] (a : A) :
    localizationAtComapMap f m (algebraMap A (Localization.AtPrime (m.comap f)) a) =
      algebraMap B (Localization.AtPrime m) (f a) :=
  Localization.localRingHom_to_map (m.comap f) m f rfl a

/-- Both numerator and denominator follow the coefficient inclusion. -/
theorem localizationAtComapMap_mk' (f : A →+* B) (m : Ideal B) [m.IsPrime]
    (a : A) (s : (m.comap f).primeCompl) :
    localizationAtComapMap f m (IsLocalization.mk' (Localization.AtPrime (m.comap f)) a s) =
      IsLocalization.mk' (Localization.AtPrime m) (f a)
        (⟨f s, s.2⟩ : m.primeCompl) :=
  Localization.localRingHom_mk' (m.comap f) m f rfl a s

/-- An inclusion into a domain remains injective after the two prime
localizations, even though the target inverts additional denominators. -/
theorem localizationAtComapMap_injective [IsDomain B] (f : A →+* B)
    (hf : Function.Injective f) (m : Ideal B) [m.IsPrime] :
    Function.Injective (localizationAtComapMap f m) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := (m.comap f).primeCompl) (Localization.AtPrime (m.comap f))
    (localizationAtComapMap f m)
  intro a ha
  rw [localizationAtComapMap_algebraMap] at ha
  have hB : Function.Injective (algebraMap B (Localization.AtPrime m)) :=
    IsLocalization.injective (Localization.AtPrime m) m.primeCompl_le_nonZeroDivisors
  have hfa : f a = 0 := hB (by simpa only [map_zero] using ha)
  have haz : a = 0 := hf (by simpa only [map_zero] using hfa)
  rw [haz, map_zero]

/-- Units used by the local comparison remain units in the larger
coefficient localization. -/
theorem localizationAtComapMap_isUnit (f : A →+* B) (m : Ideal B) [m.IsPrime]
    {x : Localization.AtPrime (m.comap f)} (hx : IsUnit x) :
    IsUnit (localizationAtComapMap f m x) :=
  hx.map (localizationAtComapMap f m)

/-- Integral coefficient extensions preserve maximality on contraction. -/
theorem maximal_comap_of_integral (f : A →+* B) (hf : f.IsIntegral)
    (m : Ideal B) [m.IsMaximal] : (m.comap f).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf m

end LocalizationMap

/-- Every rational prime has a maximal ideal above it in an integral
integer algebra with injective integer map. The conclusion retains the exact
contraction as well as membership of the prime in the maximal ideal. -/
theorem exists_maximal_ideal_over_nat_prime (B : Type uB) [CommRing B]
    [Algebra ℤ B] [Algebra.IsIntegral ℤ B]
    (hB : Function.Injective (algebraMap ℤ B)) {p : ℕ} (hp : p.Prime) :
    ∃ m : Ideal B, m.IsMaximal ∧
      m.comap (algebraMap ℤ B) = Ideal.span ({(p : ℤ)} : Set ℤ) ∧ (p : B) ∈ m := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hB
  obtain ⟨m, hm, hcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) P
      (by rw [hker]; exact bot_le)
  refine ⟨m, hm, hcomap, ?_⟩
  have hpP : (p : ℤ) ∈ P := Ideal.subset_span (Set.mem_singleton _)
  have hpcomap : (p : ℤ) ∈ m.comap (algebraMap ℤ B) := by
    rwa [hcomap]
  have hpm := Ideal.mem_comap.mp hpcomap
  simpa only [map_natCast] using hpm

/-- Characteristic zero supplies the injective integer map automatically. -/
theorem exists_maximal_ideal_over_nat_prime_of_charZero (B : Type uB) [CommRing B]
    [CharZero B] [Algebra ℤ B] [Algebra.IsIntegral ℤ B] {p : ℕ} (hp : p.Prime) :
    ∃ m : Ideal B, m.IsMaximal ∧
      m.comap (algebraMap ℤ B) = Ideal.span ({(p : ℤ)} : Set ℤ) ∧ (p : B) ∈ m :=
  exists_maximal_ideal_over_nat_prime B (algebraMap ℤ B).injective_int hp

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryLocalization
section
namespace OAI

universe uB uO uk uF


namespace CirculantHadamard.BinaryLocalization

/-- A finite characteristic-zero integer algebra has a maximal ideal over two. -/
theorem exists_maximal_two_mem (B : Type uB) [CommRing B] [CharZero B]
    [Module.Finite ℤ B] :
    ∃ m : Ideal B, m.IsMaximal ∧ (2 : B) ∈ m := by
  let : Algebra.IsIntegral ℤ B := Algebra.IsIntegral.of_finite ℤ B
  obtain ⟨m, hm, _, htwo⟩ :=
    exists_maximal_ideal_over_nat_prime_of_charZero B Nat.prime_two
  exact ⟨m, hm, htwo⟩

/-- The one residue field used by both first-order maps has characteristic two. -/
theorem residue_char_two {B : Type uB} [CommRing B] (m : Ideal B) [m.IsPrime]
    (htwo : (2 : B) ∈ m) :
    CharP (IsLocalRing.ResidueField (Localization.AtPrime m)) 2 := by
  let O := Localization.AtPrime m
  apply CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
  have hmem : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    simpa only [map_ofNat] using
      (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (2 : B)).mpr htwo
  have hz := (IsLocalRing.residue_eq_zero_iff (2 : O)).mpr hmem
  simpa only [map_ofNat] using hz

/-- A square root of minus one reduces to one in a field of characteristic two. -/
theorem map_i_eq_one {O : Type uO} {k : Type uk} [CommRing O] [Field k] [CharP k 2]
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) : φ i = 1 := by
  have htwo : (2 : k) = 0 := CharTwo.two_eq_zero
  have hsquare : (φ i) ^ 2 = -1 := by
    simpa using congrArg φ hi
  have hsq : (φ i - 1) ^ 2 = 0 := by
    calc
      (φ i - 1) ^ 2 = (φ i) ^ 2 - 2 * φ i + 1 := by ring
      _ = 0 := by rw [hsquare, htwo]; ring
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq)

/-- An odd scalar is one in the common characteristic-two residue field. -/
theorem map_odd_nat_eq_one {O : Type uO} {k : Type uk} [CommRing O] [Field k] [CharP k 2]
    (φ : O →+* k) {u : ℕ} (hu : Odd u) : φ (u : O) = 1 := by
  rw [map_natCast]
  exact natCast_eq_one_of_odd_of_two_eq_zero hu CharTwo.two_eq_zero

/-- The odd norm supplies a unit without requiring the second factor to be a
conjugation operation on the local ring. -/
theorem isUnit_of_mul_eq_odd_square {O : Type uO} [CommRing O] [IsLocalRing O]
    [CharP (IsLocalRing.ResidueField O) 2] {x y : O} {u : ℕ}
    (hu : Odd u) (hxy : x * y = (u : O) ^ 2) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  intro hx
  have h := congrArg (IsLocalRing.residue O) hxy
  have hu' := map_odd_nat_eq_one (IsLocalRing.residue O) hu
  have hbad : (0 : IsLocalRing.ResidueField O) = 1 := by
    simpa only [map_mul, map_pow, hx, zero_mul, hu', one_pow] using h
  exact zero_ne_one hbad

/-- A faithful ring embedding reflects the odd-power witness for an actual unit. -/
theorem odd_power_of_map {O : Type uO} {F : Type uF} [CommRing O] [CommRing F]
    (f : O →+* F) (hf : Function.Injective f) (u : Oˣ)
    (h : ∃ m : ℕ, 0 < m ∧ Odd m ∧ (f (u : O)) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ u ^ m = 1 := by
  obtain ⟨m, hm, hodd, hpow⟩ := h
  refine ⟨m, hm, hodd, ?_⟩
  apply Units.ext
  apply hf
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using hpow

end CirculantHadamard.BinaryLocalization

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryLocalRing
section
namespace OAI


noncomputable section

namespace CirculantHadamard.BinaryLocalRing

open CyclotomicRings

def twoIdeal (u : ℕ) : Ideal (B u) :=
  Classical.choose (BinaryLocalization.exists_maximal_two_mem (B u))

instance twoIdeal_isMaximal (u : ℕ) : (twoIdeal u).IsMaximal :=
  (Classical.choose_spec (BinaryLocalization.exists_maximal_two_mem (B u))).1

theorem two_mem (u : ℕ) : (2 : B u) ∈ twoIdeal u :=
  (Classical.choose_spec (BinaryLocalization.exists_maximal_two_mem (B u))).2

abbrev O (u : ℕ) := Localization.AtPrime (twoIdeal u)

/- Name the canonical localization algebra directly. This avoids searching
through iterated-localization algebra instances for these concrete carriers. -/
instance local_algebra (u : ℕ) : Algebra (B u) (O u) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := (twoIdeal u).primeCompl)

instance fraction_algebra (u : ℕ) : Algebra (B u) (FractionRing (B u)) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := nonZeroDivisors (B u))

abbrev k (u : ℕ) := IsLocalRing.ResidueField (O u)

def toLocal (u : ℕ) : B u →+* O u := algebraMap (B u) (O u)

theorem toLocal_injective (u : ℕ) : Function.Injective (toLocal u) :=
  IsLocalization.injective (O u) (twoIdeal u).primeCompl_le_nonZeroDivisors

/-- The same localization embeds into the fraction field used for the
alternating products. -/
def toFraction (u : ℕ) : O u →ₐ[B u] FractionRing (B u) :=
  Localization.mapToFractionRing (FractionRing (B u)) (twoIdeal u).primeCompl
    (O u) (twoIdeal u).primeCompl_le_nonZeroDivisors

@[simp] theorem toFraction_toLocal (u : ℕ) (x : B u) :
    toFraction u (toLocal u x) = algebraMap (B u) (FractionRing (B u)) x :=
  (toFraction u).commutes x

theorem toFraction_injective (u : ℕ) : Function.Injective (toFraction u) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (twoIdeal u).primeCompl (toFraction u).toRingHom).2
  intro a b
  change toLocal u a = toLocal u b ↔
    toFraction u (toLocal u a) = toFraction u (toLocal u b)
  rw [toFraction_toLocal, toFraction_toLocal]
  constructor
  · intro h
    exact congrArg (algebraMap (B u) (FractionRing (B u))) (toLocal_injective u h)
  · intro h
    exact congrArg (toLocal u) (IsFractionRing.injective (B u) (FractionRing (B u)) h)

instance local_charZero (u : ℕ) : CharZero (O u) where
  cast_injective a b hab := by
    apply (Nat.cast_injective (R := B u))
    apply toLocal_injective u
    simpa only [map_natCast] using hab

instance residue_charTwo (u : ℕ) : CharP (k u) 2 :=
  BinaryLocalization.residue_char_two (twoIdeal u) (two_mem u)

def residue (u : ℕ) : O u →+* k u := IsLocalRing.residue (O u)

def gaussianToLocal (u : ℕ) : GaussianRing →+* O u :=
  (toLocal u).comp (gaussianToB u).toRingHom

def imaginary (u : ℕ) : O u := gaussianToLocal u gaussianI

theorem imaginary_sq (u : ℕ) : imaginary u ^ 2 = -1 := by
  unfold imaginary
  rw [← map_pow, gaussianI_sq, map_neg, map_one]

theorem residue_imaginary (u : ℕ) : residue u (imaginary u) = 1 :=
  BinaryLocalization.map_i_eq_one (residue u) (imaginary u) (imaginary_sq u)

theorem two_ne_zero (u : ℕ) : (2 : O u) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

/-- Every one of the actual character norms supplies its own local unit. -/
theorem norm_isUnit (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) : IsUnit (toLocal u x) := by
  apply BinaryLocalization.isUnit_of_mul_eq_odd_square hu
    (y := toLocal u y)
  have h := congrArg (toLocal u) hxy
  simpa only [map_mul, map_pow, map_natCast] using h

/-- The unit value is the localized character value, not an unrelated witness. -/
def normUnit (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) : (O u)ˣ :=
  (norm_isUnit u hu x y hxy).unit

@[simp] theorem normUnit_val (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) :
    (normUnit u hu x y hxy : O u) = toLocal u x :=
  (norm_isUnit u hu x y hxy).unit_spec

end CirculantHadamard.BinaryLocalRing

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.AlternatingProducts
section
namespace OAI

universe uI uG uH


namespace CirculantHadamard

open scoped BigOperators

variable {I : Type uI}

def subsetSign (S : Finset I) : ℤ := (-1) ^ S.card

@[simp] theorem subsetSign_empty : subsetSign (∅ : Finset I) = 1 := by
  simp [subsetSign]

theorem subsetSign_of_even (S : Finset I) (h : Even S.card) : subsetSign S = 1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = 1)

theorem subsetSign_of_odd (S : Finset I) (h : Odd S.card) : subsetSign S = -1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = -1)

theorem subsetSign_insert [DecidableEq I] (p : I) (S : Finset I) (hp : p ∉ S) :
    subsetSign (insert p S) = -subsetSign S := by
  simp only [subsetSign, Finset.card_insert_of_notMem hp, pow_succ, mul_neg_one]

/-- The signed subset count vanishes by pairing along an actual element of `t`. -/
theorem sum_subsetSign_eq_zero (t : Finset I) (ht : t.Nonempty) :
    ∑ S ∈ t.powerset, subsetSign S = 0 := by
  classical
  obtain ⟨p, hp⟩ := ht
  have hpaired :
      (∑ S ∈ (t.erase p).powerset, subsetSign (insert p S)) =
        -(∑ S ∈ (t.erase p).powerset, subsetSign S) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    exact subsetSign_insert p S
      (fun h => (Finset.notMem_erase p t) ((Finset.mem_powerset.mp hS) h))
  calc
    _ = ∑ S ∈ (insert p (t.erase p)).powerset, subsetSign S := by
      rw [Finset.insert_erase hp]
    _ = (∑ S ∈ (t.erase p).powerset, subsetSign S) +
        ∑ S ∈ (t.erase p).powerset, subsetSign (insert p S) :=
      Finset.sum_powerset_insert (Finset.notMem_erase p t) subsetSign
    _ = 0 := by rw [hpaired, add_neg_cancel]

/-- The even-cardinality and odd-cardinality subset filters have equal size. -/
theorem card_even_subsets_eq_card_odd_subsets (t : Finset I) (ht : t.Nonempty) :
    (t.powerset.filter (fun S => Even S.card)).card =
      (t.powerset.filter (fun S => Odd S.card)).card := by
  classical
  have heven : (∑ S ∈ t.powerset.filter (fun S => Even S.card), subsetSign S) =
      ((t.powerset.filter (fun S => Even S.card)).card : ℤ) := by
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Even S.card), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_even S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hodd : (∑ S ∈ t.powerset.filter (fun S => ¬ Even S.card), subsetSign S) =
      -((t.powerset.filter (fun S => Odd S.card)).card : ℤ) := by
    have hfilter : t.powerset.filter (fun S => ¬ Even S.card) =
        t.powerset.filter (fun S => Odd S.card) := by
      ext S
      simp only [Finset.mem_filter, Nat.not_even_iff_odd]
    rw [hfilter]
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Odd S.card), (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_odd S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hsum := Finset.sum_filter_add_sum_filter_not t.powerset
    (fun S : Finset I => Even S.card) subsetSign
  rw [heven, hodd, sum_subsetSign_eq_zero t ht] at hsum
  exact Int.natCast_inj.mp (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hsum))

/-- Numerator before introducing any inverse, available in a coefficient ring. -/
def evenSubsetProduct {G : Type uG} [CommMonoid G] (t : Finset I)
    (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset.filter (fun S => Even S.card), x S

/-- Denominator before introducing any inverse, available in a coefficient ring. -/
def oddSubsetProduct {G : Type uG} [CommMonoid G] (t : Finset I)
    (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset.filter (fun S => Odd S.card), x S

theorem map_evenSubsetProduct {G : Type uG} {H : Type uH} [CommMonoid G] [CommMonoid H]
    (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (evenSubsetProduct t x) = evenSubsetProduct t (fun S => f (x S)) := by
  simp only [evenSubsetProduct, map_prod]

theorem map_oddSubsetProduct {G : Type uG} {H : Type uH} [CommMonoid G] [CommMonoid H]
    (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (oddSubsetProduct t x) = oddSubsetProduct t (fun S => f (x S)) := by
  simp only [oddSubsetProduct, map_prod]

section DivisionCommMonoid

variable {G : Type uG} [DivisionCommMonoid G]

/-- The alternating product of the actual family indexed by subsets of `t`. -/
def alternatingProduct (t : Finset I) (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset, (x S) ^ subsetSign S

@[simp] theorem alternatingProduct_empty (x : Finset I → G) :
    alternatingProduct ∅ x = x ∅ := by
  simp [alternatingProduct]

@[simp] theorem alternatingProduct_one (t : Finset I) :
    alternatingProduct t (fun _ => (1 : G)) = 1 := by
  simp [alternatingProduct]

theorem alternatingProduct_congr (t : Finset I) (x y : Finset I → G)
    (h : ∀ S ⊆ t, x S = y S) :
    alternatingProduct t x = alternatingProduct t y := by
  apply Finset.prod_congr rfl
  intro S hS
  rw [h S (Finset.mem_powerset.mp hS)]

theorem alternatingProduct_mul (t : Finset I) (x y : Finset I → G) :
    alternatingProduct t (fun S => x S * y S) =
      alternatingProduct t x * alternatingProduct t y := by
  simp only [alternatingProduct, mul_zpow, Finset.prod_mul_distrib]

theorem alternatingProduct_inv (t : Finset I) (x : Finset I → G) :
    alternatingProduct t (fun S => (x S)⁻¹) = (alternatingProduct t x)⁻¹ := by
  simp only [alternatingProduct, inv_zpow, Finset.prod_inv_distrib]

theorem alternatingProduct_div (t : Finset I) (x y : Finset I → G) :
    alternatingProduct t (fun S => x S / y S) =
      alternatingProduct t x / alternatingProduct t y := by
  simp only [alternatingProduct, div_zpow, Finset.prod_div_distrib]

/-- A single direction pairs each omitted-`p` subset with its insertion.
The exponent at the inserted subset is the negative of the original one. -/
theorem alternatingProduct_insert [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∉ t) :
    alternatingProduct (insert p t) x =
      ∏ S ∈ t.powerset, (x S / x (insert p S)) ^ subsetSign S := by
  unfold alternatingProduct
  rw [Finset.prod_powerset_insert hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  have hpS : p ∉ S := fun h => hp ((Finset.mem_powerset.mp hS) h)
  rw [subsetSign_insert p S hpS, zpow_neg, div_zpow, div_eq_mul_inv]

theorem alternatingProduct_pair [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∈ t) :
    alternatingProduct t x =
      ∏ S ∈ (t.erase p).powerset, (x S / x (insert p S)) ^ subsetSign S := by
  calc
    alternatingProduct t x = alternatingProduct (insert p (t.erase p)) x := by
      rw [Finset.insert_erase hp]
    _ = _ := alternatingProduct_insert (t.erase p) x p (Finset.notMem_erase p t)

/-- Even subsets contribute the value itself; odd subsets contribute its inverse. -/
theorem alternatingProduct_eq_parity (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x =
      ∏ S ∈ t.powerset, if Even S.card then x S else (x S)⁻¹ := by
  classical
  apply Finset.prod_congr rfl
  intro S _
  by_cases h : Even S.card
  · simp only [subsetSign_of_even S h, zpow_one, if_pos h]
  · have ho : Odd S.card := Nat.not_even_iff_odd.mp h
    simp only [subsetSign_of_odd S ho, zpow_neg_one, if_neg h]

/-- Collect the signed powers as a quotient of two ordinary products.
Both products themselves make sense before passing to a fraction field. -/
theorem alternatingProduct_eq_even_div_odd (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x = evenSubsetProduct t x / oddSubsetProduct t x := by
  classical
  rw [alternatingProduct_eq_parity, evenSubsetProduct, oddSubsetProduct,
    Finset.prod_filter, Finset.prod_filter, div_eq_mul_inv,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S _
  by_cases h : Even S.card
  · simp [h, Nat.not_odd_iff_even.mpr h]
  · simp [h, Nat.not_even_iff_odd.mp h]

end DivisionCommMonoid

section CommGroup

variable {G : Type uG} {H : Type uH} [CommGroup G] [DivisionCommMonoid H]

/-- In particular this applies to the homomorphism from local units to the
fraction field, retaining the single fixed alternating product. -/
theorem map_alternatingProduct (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (alternatingProduct t x) = alternatingProduct t (fun S => f (x S)) := by
  simp only [alternatingProduct, map_prod, map_zpow]

/-- A nonempty index set cancels every constant family, by actual subset pairing. -/
theorem alternatingProduct_const (t : Finset I) (ht : t.Nonempty) (c : G) :
    alternatingProduct t (fun _ => c) = 1 := by
  classical
  obtain ⟨p, hp⟩ := ht
  rw [alternatingProduct_pair t (fun _ => c) p hp]
  simp

/-- Clearing the odd-subset denominator inside the group of units.
Mapping this equality into the fraction field gives the polynomial identity
needed before applying a homomorphism defined only on the coefficient ring. -/
theorem alternatingProduct_mul_oddSubsetProduct (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x * oddSubsetProduct t x = evenSubsetProduct t x := by
  rw [alternatingProduct_eq_even_div_odd, div_mul_cancel]

end CommGroup

section FiniteUniverse

variable [Fintype I] {G : Type uG} [DivisionCommMonoid G]

/-- The full prime-index product, using all subsets of the finite index type. -/
def fullAlternatingProduct (x : Finset I → G) : G :=
  alternatingProduct Finset.univ x

theorem fullAlternatingProduct_pair [DecidableEq I] (x : Finset I → G) (p : I) :
    fullAlternatingProduct x =
      ∏ S ∈ ((Finset.univ : Finset I).erase p).powerset,
        (x S / x (insert p S)) ^ subsetSign S :=
  alternatingProduct_pair Finset.univ x p (Finset.mem_univ p)

end FiniteUniverse

theorem fullAlternatingProduct_const [Fintype I] [Nonempty I]
    {G : Type uG} [CommGroup G] (c : G) :
    fullAlternatingProduct (fun _ : Finset I => c) = 1 :=
  alternatingProduct_const Finset.univ Finset.univ_nonempty c

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryProductTransport
section
namespace OAI

universe uG uI


noncomputable section

namespace CirculantHadamard.BinaryProductTransport

open CyclotomicRings BinaryLocalRing

/-- Odd-power torsion is closed under taking a quotient in a commutative
group. The product of the two supplied exponents is an explicit witness. -/
theorem odd_power_mul_inv {G : Type uG} [CommGroup G] (x y : G)
    (hx : ∃ m : ℕ, 0 < m ∧ Odd m ∧ x ^ m = 1)
    (hy : ∃ n : ℕ, 0 < n ∧ Odd n ∧ y ^ n = 1) :
    ∃ r : ℕ, 0 < r ∧ Odd r ∧ (x * y⁻¹) ^ r = 1 := by
  obtain ⟨m, hm, hmOdd, hxm⟩ := hx
  obtain ⟨n, hn, hnOdd, hyn⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, hmOdd.mul hnOdd, ?_⟩
  have hxmn : x ^ (m * n) = 1 := by rw [pow_mul, hxm, one_pow]
  have hymn : y ^ (m * n) = 1 := by rw [Nat.mul_comm m n, pow_mul, hyn, one_pow]
  simp only [mul_pow, inv_pow, hxmn, hymn, inv_one, mul_one]

/-- The actual map from local units to the fraction field of `B u`. -/
def localUnitToFraction (u : ℕ) : (O u)ˣ →* FractionRing (B u) :=
  (toFraction u).toRingHom.toMonoidHom.comp (Units.coeHom (O u))

@[simp] theorem localUnitToFraction_apply (u : ℕ) (X : (O u)ˣ) :
    localUnitToFraction u X = toFraction u (X : O u) := rfl

theorem localUnitToFraction_injective (u : ℕ) :
    Function.Injective (localUnitToFraction u) := by
  intro X Y h
  apply Units.ext
  exact toFraction_injective u h

/-- Transport of the literal signed subset product, using the supplied
value equality only for subsets that occur in the product. -/
theorem local_alternatingProduct_toFraction {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S)) :
    localUnitToFraction u (alternatingProduct t X) =
      alternatingProduct t (fun S => algebraMap (B u) (FractionRing (B u)) (x S)) := by
  rw [map_alternatingProduct]
  apply alternatingProduct_congr
  intro S hS
  change toFraction u (X S : O u) = _
  rw [hX S hS, toFraction_toLocal]

/-- An exact fraction-field power identity holds for the actual local
alternating product with precisely the same exponent. -/
theorem local_alternatingProduct_pow_eq_one {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S)) (m : ℕ)
    (hpow : (alternatingProduct t
      (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1) :
    (alternatingProduct t X) ^ m = 1 := by
  apply localUnitToFraction_injective u
  rw [map_pow, map_one, local_alternatingProduct_toFraction u t x X hX]
  exact hpow

theorem local_alternatingProduct_has_odd_power {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S))
    (hodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ (alternatingProduct t X) ^ m = 1 := by
  obtain ⟨m, hm, hmOdd, hpow⟩ := hodd
  exact ⟨m, hm, hmOdd, local_alternatingProduct_pow_eq_one u t x X hX m hpow⟩

/-- The two concrete unit families produce an odd-power quotient family.
No torsion of individual factors is assumed or inferred. -/
theorem local_alternatingProduct_ratio_has_odd_power {I : Type uI}
    (u : ℕ) (t : Finset I) (x y : Finset I → B u)
    (X Y : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S))
    (hY : ∀ S ⊆ t, (Y S : O u) = toLocal u (y S))
    (hx : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1)
    (hy : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (y S))) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t (fun S => X S * (Y S)⁻¹)) ^ m = 1 := by
  simpa only [alternatingProduct_mul, alternatingProduct_inv] using
    odd_power_mul_inv (alternatingProduct t X) (alternatingProduct t Y)
      (local_alternatingProduct_has_odd_power u t x X hX hx)
      (local_alternatingProduct_has_odd_power u t y Y hY hy)

end CirculantHadamard.BinaryProductTransport

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryCharacterSum
section
namespace OAI

universe uG uR uA uI uT uK uk uB


namespace CirculantHadamard.BinaryCharacterSum

open scoped BigOperators

section CharacterSum

variable {G : Type uG} {R : Type uR} [Group G] [Fintype G] [CommRing R]

/-- A nontrivial value of a character forces its finite sum to vanish.
The proof uses the permutation of `G` given by left translation. -/
theorem character_sum_eq_zero [IsDomain R] (χ : G →* R)
    (hχ : ∃ g : G, χ g ≠ 1) : (∑ g : G, χ g) = 0 := by
  classical
  obtain ⟨g, hg⟩ := hχ
  apply eq_zero_of_mul_eq_self_left hg
  simpa only [Finset.mul_sum, ← map_mul] using
    (Group.mulLeft_bijective g).sum_comp (fun h : G => χ h)

/-- The trivial character sums to the cardinality of the group. -/
theorem character_sum_trivial (χ : G →* R) (hχ : ∀ g : G, χ g = 1) :
    (∑ g : G, χ g) = (Fintype.card G : R) := by
  simp [hχ]

end CharacterSum

section ActualGroupRing

variable {A : Type uA} {R : Type uR} [CommRing A] [CommRing R] {n : ℕ} [NeZero n]

/-- The coefficientwise all-ones element is literally the sum of the basis
elements, with coefficient one at each group element. -/
theorem JOver_eq_sum_single {G : Type uG} [Fintype G] :
    (BinaryCoefficients.JOver A : G →₀ A) = ∑ g : G, Finsupp.single g 1 := by
  classical
  ext g
  simp

/-- Evaluation of the actual all-ones group-ring element is the complete
character sum. `JOver` is not the scalar unit of the group ring. -/
theorem evaluate_J_eq_sum (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) =
      ∑ g : Multiplicative (ZMod n), χ g := by
  rw [CyclicRing.evaluate_apply]
  simp only [BinaryCoefficients.JOver_apply, map_one, one_mul]
  exact (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n)).sum_comp _

/-- A witnessed nontrivial character annihilates the actual group-ring `J`. -/
theorem evaluate_J_eq_zero [IsDomain R] (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R)
    (hχ : ∃ g : Multiplicative (ZMod n), χ g ≠ 1) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = 0 := by
  rw [evaluate_J_eq_sum]
  exact character_sum_eq_zero χ hχ

/-- At the trivial character, the actual group-ring `J` evaluates to `n`. -/
theorem evaluate_J_trivial (φ : A →+* R) :
    CyclicRing.evaluate φ (1 : Multiplicative (ZMod n) →* R)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = (n : R) := by
  rw [CyclicRing.evaluate_apply]
  simp

end ActualGroupRing

/-- Collapse written directly with evaluations of the actual group-ring `J`.
Only character witnesses for nonempty subsets are used. -/
theorem subset_evaluate_J_mul
    {I : Type uI} {A : Type uA} {R : Type uR} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    (φ : A →+* R) (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → R) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d S) =
      (n : R) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * CyclicRing.evaluate φ (χ S)
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d S) =
        ε ∅ * CyclicRing.evaluate φ (χ ∅)
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [evaluate_J_eq_zero φ (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (n : R) * d ∅ := by
      rw [hε, one_mul, htrivial, evaluate_J_trivial]

/-- First prove the character sum in its domain, then change coefficient
rings. This does not assume nontriviality of the reduced characters and also
allows the coefficients `d S` to lie in a localization of the original ring. -/
theorem subset_map_evaluate_J_mul
    {I : Type uI} {A : Type uA} {R : Type uR} {T : Type uT} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] [CommRing T] {n : ℕ} [NeZero n]
    (φ : A →+* R) (ψ : R →+* T)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → T) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
      (n : T) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
        ε ∅ * ψ (CyclicRing.evaluate φ (χ ∅)
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [evaluate_J_eq_zero φ (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (n : T) * d ∅ := by
      rw [hε, one_mul, htrivial, evaluate_J_trivial, map_natCast]

section SubsetSum

variable {I : Type uI} {G : Type uG} {R : Type uR} [Fintype I] [DecidableEq I]
    [Group G] [Fintype G] [CommRing R] [IsDomain R]

/-- Only the empty subset survives. The coefficients `d S` are arbitrary;
in particular they may be inverses of specified units. -/
theorem subset_character_sum_mul [DecidableEq I]
    (χ : Finset I → G →* R) (ε d : Finset I → R)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1) :
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) * d S) =
      (Fintype.card G : R) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) * d S) =
        ε ∅ * (∑ g : G, χ ∅ g) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [character_sum_eq_zero (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (Fintype.card G : R) * d ∅ := by
      rw [hε, one_mul, character_sum_trivial (χ ∅) htrivial]

/-- Ring-valued version of the quotient by each specified denominator unit. -/
theorem subset_character_sum_mul_unit_inv
    (χ : Finset I → G →* R) (ε : Finset I → R) (c : Finset I → Rˣ)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1) :
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) * ↑((c S)⁻¹)) =
      (Fintype.card G : R) * ↑((c ∅)⁻¹) :=
  subset_character_sum_mul χ ε (fun S => ↑((c S)⁻¹)) hε htrivial hnonempty

end SubsetSum

/-- In a field, the same collapse is expressed using division. No
nonvanishing assumption on nonempty-subset denominators is needed. -/
theorem subset_character_sum_div
    {I : Type uI} {G : Type uG} {K : Type uK} [Fintype I] [DecidableEq I] [Group G] [Fintype G] [Field K]
    (χ : Finset I → G →* K) (ε c : Finset I → K)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1) :
    (∑ S : Finset I, ε S * (∑ g : G, χ S g) / c S) =
      (Fintype.card G : K) / c ∅ := by
  simpa only [div_eq_mul_inv] using
    subset_character_sum_mul χ ε (fun S => (c S)⁻¹) hε htrivial hnonempty

section Residue

variable {R : Type uR} {k : Type uk} [CommRing R] [CommRing k] [Nontrivial k] [CharP k 2]

/-- An odd cardinal times the inverse of a unit stays nonzero in any
nontrivial characteristic-two residue ring. -/
theorem residue_odd_mul_unit_inv_ne_zero (φ : R →+* k) {n : ℕ}
    (hn : Odd n) (c : Rˣ) : φ ((n : R) * ↑(c⁻¹)) ≠ 0 := by
  rw [map_mul, map_natCast,
    natCast_eq_one_of_odd_of_two_eq_zero hn (CharTwo.two_eq_zero (R := k)), one_mul]
  exact (IsUnit.map φ (c⁻¹).isUnit).ne_zero

/-- The weighted sum is nonzero after reduction when the finite group has
odd order and the empty-subset denominator is the specified unit. -/
theorem residue_subset_character_sum_ne_zero
    {I : Type uI} {G : Type uG} [Fintype I] [DecidableEq I] [Group G] [Fintype G] [IsDomain R]
    (φ : R →+* k) (χ : Finset I → G →* R)
    (ε : Finset I → R) (c : Finset I → Rˣ)
    (hε : ε ∅ = 1) (htrivial : ∀ g : G, χ ∅ g = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty → ∃ g : G, χ S g ≠ 1)
    (hodd : Odd (Fintype.card G)) :
    φ (∑ S : Finset I, ε S * (∑ g : G, χ S g) * ↑((c S)⁻¹)) ≠ 0 := by
  rw [subset_character_sum_mul_unit_inv χ ε c hε htrivial hnonempty]
  exact residue_odd_mul_unit_inv_ne_zero φ hodd (c ∅)

/-- The residue of the actual `J` expression is nonzero. Only the denominator
at the surviving empty subset needs to be a unit; the other coefficients are
arbitrary because their character evaluations vanish. -/
theorem residue_subset_evaluate_J_ne_zero
    {I : Type uI} {A : Type uA} [Fintype I] [DecidableEq I] [CommRing A] [IsDomain R]
    {n : ℕ} [NeZero n] (φ : A →+* R) (residue : R →+* k)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → R) (c₀ : Rˣ)
    (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1)
    (hd : d ∅ = ↑(c₀⁻¹)) (hodd : Odd n) :
    residue (∑ S : Finset I, ε S * CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) * d S) ≠ 0 := by
  rw [subset_evaluate_J_mul φ χ ε d hε htrivial hnonempty, hd]
  exact residue_odd_mul_unit_inv_ne_zero residue hodd c₀

/-- Localization and residue reduction may follow the domain-valued
character-sum proof. Only the empty-subset coefficient is constrained. -/
theorem residue_subset_map_evaluate_J_ne_zero
    {I : Type uI} {A : Type uA} {B : Type uB} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing B] [IsDomain B] {n : ℕ} [NeZero n]
    (φ : A →+* B) (ψ : B →+* R) (residue : R →+* k)
    (χ : Finset I → Multiplicative (ZMod n) →* B)
    (ε d : Finset I → R) (c₀ : Rˣ)
    (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1)
    (hd : d ∅ = ↑(c₀⁻¹)) (hodd : Odd n) :
    residue (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) ≠ 0 := by
  rw [subset_map_evaluate_J_mul φ ψ χ ε d hε htrivial hnonempty, hd]
  exact residue_odd_mul_unit_inv_ne_zero residue hodd c₀

end Residue

section ActualSubsetCharacters

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations

/-- The witness is the actual CRT generator of a prime in the nonempty
subset. Its value is the corresponding primitive prime root, hence not one. -/
theorem actual_subsetCharacter_nontrivial (u : ℕ) (hu : 0 < u)
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    ∃ g : Multiplicative (ZMod (u ^ 2)), subsetCharacter u hu S g ≠ 1 := by
  obtain ⟨a, ha⟩ := subsetCharacter_nonempty u hu S hS
  exact ⟨Multiplicative.ofAdd a, ha⟩

variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)

/-- The actual empty-subset evaluation of `J` is the order `u²`. -/
theorem actual_subsetEvaluation_J_empty :
    subsetEvaluation u hu ∅
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2)) =
      (u ^ 2 : ℕ) := by
  simp only [subsetEvaluation, subsetCharacter_empty, evaluate_J_trivial]

/-- Every actual nonempty-subset evaluation of `J` vanishes. No
nontrivial-character hypothesis is an input to this theorem. -/
theorem actual_subsetEvaluation_J_nonempty
    (S : Finset (PrimeIndex u)) (hS : S.Nonempty) :
    subsetEvaluation u hu S
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2)) = 0 := by
  exact evaluate_J_eq_zero (gaussianToB u).toRingHom (subsetCharacter u hu S)
    (actual_subsetCharacter_nontrivial u hu S hS)

/-- The actual prime-subset sum, with the literal parity signs. The target
may be a localization: its coefficients need not belong to the original `B`. -/
theorem actual_subset_J_sum
    {T : Type uT} [CommRing T] (ψ : B u →+* T)
    (d : Finset (PrimeIndex u) → T) :
    (∑ S : Finset (PrimeIndex u), (subsetSign S : T) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) *
      d S) = ((u ^ 2 : ℕ) : T) * d ∅ := by
  exact subset_map_evaluate_J_mul (gaussianToB u).toRingHom ψ
    (subsetCharacter u hu) (fun S => (subsetSign S : T)) d (by simp)
    (subsetCharacter_empty u hu) (actual_subsetCharacter_nontrivial u hu)

/-- In a field the concrete sum is exactly `|P| / c_empty`, with
`|P| = u²`. Values at every nonempty subset were proved zero using its
actual primitive primary component. -/
theorem actual_subset_J_sum_div
    {K : Type uK} [Field K] (ψ : B u →+* K)
    (c : Finset (PrimeIndex u) → K) :
    (∑ S : Finset (PrimeIndex u), (subsetSign S : K) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) /
      c S) = ((u ^ 2 : ℕ) : K) / c ∅ := by
  simpa only [div_eq_mul_inv] using actual_subset_J_sum u hu ψ (fun S => (c S)⁻¹)

/-- The concrete prime-character sum has nonzero characteristic-two residue.
Oddness comes from the actual `u`; only the surviving denominator must be a
unit. There is no assumption on reduced-character nontriviality. -/
theorem actual_subset_J_residue_ne_zero
    {T : Type uT} {k : Type uk} [CommRing T] [CommRing k] [Nontrivial k] [CharP k 2]
    (ψ : B u →+* T) (residue : T →+* k)
    (d : Finset (PrimeIndex u) → T) (c₀ : Tˣ)
    (hd : d ∅ = ↑(c₀⁻¹)) (hodd : Odd u) :
    residue (∑ S : Finset (PrimeIndex u), (subsetSign S : T) *
      ψ (subsetEvaluation u hu S
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing) : CyclicRing.Elem GaussianRing (u ^ 2))) *
      d S) ≠ 0 := by
  rw [actual_subset_J_sum u hu ψ d, hd]
  exact residue_odd_mul_unit_inv_ne_zero residue hodd.pow c₀

end ActualSubsetCharacters

end CirculantHadamard.BinaryCharacterSum

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.FirstOrderResidue
section
namespace OAI

universe uO uK uIota


namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

/-- Units whose difference from one is a multiple of the specified element. -/
def principalUnits (t : O) : Subgroup Oˣ where
  carrier := {u | ∃ a : O, (u : O) = 1 + t * a}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b + t * a * b, ?_⟩
    change (u : O) * (v : O) = _
    rw [ha, hb]
    ring
  inv_mem' := by
    rintro u ⟨a, ha⟩
    refine ⟨-a * (↑u⁻¹ : O), ?_⟩
    have h := u.mul_inv
    rw [ha] at h
    linear_combination h

@[simp]
theorem mem_principalUnits (t : O) (u : Oˣ) :
    u ∈ principalUnits t ↔ ∃ a : O, (u : O) = 1 + t * a :=
  Iff.rfl

/-- The coefficient of a principal unit. Its uniqueness is proved separately
using the domain assumption and `t ≠ 0`. -/
noncomputable def principalUnitCoeff (t : O) (u : principalUnits t) : O :=
  Classical.choose u.property

theorem principalUnitCoeff_spec (t : O) (u : principalUnits t) :
    ((u : Oˣ) : O) = 1 + t * principalUnitCoeff t u :=
  Classical.choose_spec u.property

section Domain

variable [IsDomain O]

theorem principalUnitCoeff_eq (t : O) (ht : t ≠ 0) (u : principalUnits t)
    {a : O} (ha : ((u : Oˣ) : O) = 1 + t * a) :
    principalUnitCoeff t u = a := by
  apply mul_left_cancel₀ ht
  exact add_left_cancel ((principalUnitCoeff_spec t u).symm.trans ha)

theorem principalUnitCoeff_mul (t : O) (ht : t ≠ 0)
    (u v : principalUnits t) :
    principalUnitCoeff t (u * v) =
      principalUnitCoeff t u + principalUnitCoeff t v +
        t * principalUnitCoeff t u * principalUnitCoeff t v := by
  apply principalUnitCoeff_eq t ht
  change ((u : Oˣ) : O) * ((v : Oˣ) : O) = _
  rw [principalUnitCoeff_spec, principalUnitCoeff_spec]
  ring

variable {K : Type uK} [Field K]

/-- The actual first-order homomorphism associated with a nonzero element
killed by the given residue map. `Multiplicative K` uses addition in `K`. -/
noncomputable def actualFirstOrder (φ : O →+* K) (t : O) (ht : t ≠ 0)
    (hφt : φ t = 0) : principalUnits t →* Multiplicative K where
  toFun u := Multiplicative.ofAdd (φ (principalUnitCoeff t u))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change φ (principalUnitCoeff t 1) = 0
    rw [principalUnitCoeff_eq t ht 1 (a := 0) (by simp), map_zero]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change φ (principalUnitCoeff t (u * v)) =
      φ (principalUnitCoeff t u) + φ (principalUnitCoeff t v)
    rw [principalUnitCoeff_mul t ht]
    simp [hφt]

theorem actualFirstOrder_apply_of_eq (φ : O →+* K) (t : O) (ht : t ≠ 0)
    (hφt : φ t = 0) (u : principalUnits t) {a : O}
    (ha : ((u : Oˣ) : O) = 1 + t * a) :
    (actualFirstOrder φ t ht hφt u).toAdd = φ a := by
  change φ (principalUnitCoeff t u) = φ a
  rw [principalUnitCoeff_eq t ht u ha]

/-- An exact signed product identity among principal units gives a vanishing
sum of their first-order residues. Representations are required only on `s`. -/
theorem first_order_sum_eq_zero_of_prod_eq_one {ι : Type uIota}
    (φ : O →+* K) (t : O) (ht : t ≠ 0) (hφt : φ t = 0)
    (s : Finset ι) (u : ι → Oˣ) (L : ι → O) (ε : ι → ℤ)
    (hrep : ∀ i ∈ s, (u i : O) = 1 + t * L i)
    (hprod : (∏ i ∈ s, (u i) ^ (ε i)) = 1) :
    ∑ i ∈ s, (ε i : K) * φ (L i) = 0 := by
  classical
  let v : ι → principalUnits t := fun i =>
    if hi : i ∈ s then ⟨u i, ⟨L i, hrep i hi⟩⟩ else 1
  have hv (i : ι) (hi : i ∈ s) : (v i : Oˣ) = u i := by
    simp only [v, dif_pos hi]
  have hp : (∏ i ∈ s, (v i) ^ (ε i)) = 1 := by
    apply Subtype.ext
    change (principalUnits t).subtype (∏ i ∈ s, (v i) ^ (ε i)) =
      (principalUnits t).subtype 1
    rw [map_prod, map_one]
    calc
      (∏ i ∈ s, (principalUnits t).subtype ((v i) ^ (ε i))) =
          ∏ i ∈ s, (u i) ^ (ε i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [map_zpow]
        change (v i : Oˣ) ^ (ε i) = (u i) ^ (ε i)
        rw [hv i hi]
      _ = 1 := hprod
  have hmap := congrArg
    (fun z : principalUnits t => (actualFirstOrder φ t ht hφt z).toAdd) hp
  have hsum :
      (∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd) = 0 := by
    simpa only [map_prod, map_zpow, toAdd_prod,
      toAdd_zpow, map_one, toAdd_one] using hmap
  calc
    (∑ i ∈ s, (ε i : K) * φ (L i)) =
        ∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd := by
      apply Finset.sum_congr rfl
      intro i hi
      have hvi : ((v i : Oˣ) : O) = 1 + t * L i := by
        rw [hv i hi]
        exact hrep i hi
      rw [actualFirstOrder_apply_of_eq φ t ht hφt (v i) hvi, zsmul_eq_mul]
    _ = 0 := hsum

end Domain

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.ResidueTorsion
section
namespace OAI

universe uR uK


namespace CirculantHadamard

open scoped BigOperators

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]

/-- A root whose image is one is trivial if one of its torsion exponents
is not divisible by the target characteristic. -/
theorem eq_one_of_residue_one_of_not_dvd {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hmap : f z = 1) (hpow : z ^ m = 1)
    (hm : ¬ p ∣ m) : z = 1 := by
  by_contra hne
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have hsum : (∑ i ∈ Finset.range m, z ^ i) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne)
  have hcast : (m : K) = 0 := by
    have h := congrArg f hsum
    simpa only [map_sum, map_pow, hmap, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
  exact hm ((CharP.cast_eq_zero_iff K p m).mp hcast)

/-- Coprime-order torsion in the residue-one subgroup is trivial. The
exponent need not be the exact order. -/
theorem eq_one_of_residue_one_of_coprime {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hpow : z ^ m = 1) (hcop : m.Coprime p) : z = 1 := by
  exact eq_one_of_residue_one_of_not_dvd f z hmap hpow
    (hp.coprime_iff_not_dvd.mp hcop.symm)

theorem exists_prime_power_of_residue_one {p : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hfinite : ∃ N : ℕ, 0 < N ∧ z ^ N = 1) :
    ∃ a : ℕ, z ^ (p ^ a) = 1 := by
  obtain ⟨N, hN, hpow⟩ := hfinite
  obtain ⟨a, m, hm, hNm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  refine ⟨a, eq_one_of_residue_one_of_not_dvd f (z ^ (p ^ a)) ?_ ?_ hm⟩
  · rw [map_pow, hmap, one_pow]
  · rw [← pow_mul, ← hNm]
    exact hpow

/-- The exact order is a power of the residue characteristic, including
the zeroth power for the identity element. -/
theorem orderOf_eq_prime_power_of_residue_one {p : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hfinite : IsOfFinOrder z) : ∃ a : ℕ, orderOf z = p ^ a := by
  obtain ⟨a, ha⟩ := exists_prime_power_of_residue_one f z hp hmap
    hfinite.exists_pow_eq_one
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one ha)
  exact ⟨b, hb⟩

/-- The characteristic-two consequence needed for the two alternating
products: a unit of odd torsion exponent and residue one equals one. -/
theorem units_eq_one_of_residue_one_of_odd [CharP K 2]
    (f : R →+* K) (u : Rˣ) (hmap : f (u : R) = 1)
    (hfinite : ∃ m : ℕ, 0 < m ∧ Odd m ∧ u ^ m = 1) : u = 1 := by
  obtain ⟨m, _, hm, hu⟩ := hfinite
  have hpow : (u : R) ^ m = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun v : Rˣ => (v : R)) hu
  apply Units.ext
  exact eq_one_of_residue_one_of_coprime f (u : R) Nat.prime_two hmap hpow
    hm.coprime_two_right

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryResidue
section
namespace OAI

universe uO uk uIota

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

/-- The coefficient of the ratio `d / c` along `2`. Division by `c` means
multiplication by the inverse of the supplied unit. -/
def binaryLr (c : Oˣ) (b : O) : O :=
  -b * (↑(c⁻¹) : O)

/-- The coefficient of the ratio `g / c` along `1 + i`. -/
def binaryLw (c : Oˣ) (i b J U : O) : O :=
  i * b * (↑(c⁻¹) : O) - J * (↑(c⁻¹) : O) -
    (1 - i) * U * (↑(c⁻¹) : O)

theorem binary_ratio_r (c d : Oˣ) (a b : O)
    (hc : (c : O) = a + b) (hd : (d : O) = a - b) :
    ((d * c⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr c b := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  calc
    ((d * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + 2 * (-b * (↑(c⁻¹) : O)) := by
      change (d : O) * (↑(c⁻¹) : O) = _
      rw [hd]
      ring
    _ = 1 + (2 : O) * binaryLr c b := by rw [hc']; rfl

theorem binary_ratio_w (c g : Oˣ) (a b J U i : O)
    (hc : (c : O) = a + b)
    (hg : (g : O) = a + i * b - ((1 + i) * J + 2 * U))
    (hi : i ^ 2 = -1) :
    ((g * c⁻¹ : Oˣ) : O) = 1 + (1 + i) * binaryLw c i b J U := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  calc
    ((g * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + (1 + i) * binaryLw c i b J U -
          (i * i + 1) * (b + U) * (↑(c⁻¹) : O) := by
      change (g : O) * (↑(c⁻¹) : O) = _
      rw [hg]
      unfold binaryLw
      ring
    _ = 1 + (1 + i) * binaryLw c i b J U := by rw [hc', hi']; ring

/-- This identity is exact before applying the residue map. -/
theorem binaryLr_add_binaryLw (c : Oˣ) (i b J U : O) :
    binaryLr c b + binaryLw c i b J U =
      -J * (↑(c⁻¹) : O) - (1 - i) * (b + U) * (↑(c⁻¹) : O) := by
  unfold binaryLr binaryLw
  ring

/-- Nonvanishing of `2` also makes the second first-order parameter nonzero. -/
theorem binary_one_add_i_ne_zero (i : O) (hi : i ^ 2 = -1)
    (h2 : (2 : O) ≠ 0) : 1 + i ≠ 0 := by
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  have hfactor : (1 + i) * (1 - i) = (2 : O) := by
    calc
      (1 + i) * (1 - i) = 1 - i * i := by ring
      _ = 2 := by rw [hi']; ring
  intro hzero
  apply h2
  rw [← hfactor, hzero, zero_mul]

section Domain

variable [IsDomain O]

/-- The displayed coefficient is the unique coefficient along `2`. -/
theorem binaryLr_unique (c d : Oˣ) (a b L : O)
    (hc : (c : O) = a + b) (hd : (d : O) = a - b)
    (h2 : (2 : O) ≠ 0)
    (hL : ((d * c⁻¹ : Oˣ) : O) = 1 + (2 : O) * L) :
    L = binaryLr c b := by
  apply mul_left_cancel₀ h2
  exact add_left_cancel (hL.symm.trans (binary_ratio_r c d a b hc hd))

/-- The displayed coefficient is the unique coefficient along `1 + i`. -/
theorem binaryLw_unique (c g : Oˣ) (a b J U i L : O)
    (hc : (c : O) = a + b)
    (hg : (g : O) = a + i * b - ((1 + i) * J + 2 * U))
    (hi : i ^ 2 = -1) (h2 : (2 : O) ≠ 0)
    (hL : ((g * c⁻¹ : Oˣ) : O) = 1 + (1 + i) * L) :
    L = binaryLw c i b J U := by
  apply mul_left_cancel₀ (binary_one_add_i_ne_zero i hi h2)
  exact add_left_cancel (hL.symm.trans (binary_ratio_w c g a b J U i hc hg hi))

end Domain

section Residue

variable {k : Type uk} [Field k] [charTwo : CharP k 2]

/-- The two coefficients have residues summing to the residue of `J / c`. -/
theorem binary_residue_sum (φ : O →+* k) (c : Oˣ) (i b J U : O)
    (hi : φ i = 1) :
    φ (binaryLr c b) + φ (binaryLw c i b J U) =
      φ (J * (↑(c⁻¹) : O)) := by
  rw [← map_add, binaryLr_add_binaryLw]
  simp [hi, CharTwo.neg_eq]

/-- A signed product of units with residue one again has residue one.
The powers are formed in the unit group, including for negative exponents. -/
theorem binary_signed_product_residue_one [CharP k 2] {ι : Type uIota}
    (φ : O →+* k) (s : Finset ι) (u : ι → Oˣ) (ε : ι → ℤ)
    (hu : ∀ j ∈ s, φ (u j : O) = 1) :
    φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 := by
  let f : Oˣ →* kˣ := Units.map φ.toMonoidHom
  have hf (j : ι) (hj : j ∈ s) : f (u j) = 1 := by
    apply Units.ext
    change φ (u j : O) = 1
    exact hu j hj
  have hp : f (∏ j ∈ s, (u j) ^ (ε j)) = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro j hj
    rw [map_zpow, hf j hj, one_zpow]
  have hval := congrArg (fun z : kˣ => (z : k)) hp
  change φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 at hval
  exact hval

variable [IsDomain O]

/-- The same-residue-field contradiction for a finite signed family of
binary decompositions. All arithmetic input to the concrete application is
explicit: unit decompositions, a square root of `-1`, odd torsion of both
signed products, and a nonzero signed `J / c` residue sum. -/
theorem binary_residue_contradiction {ι : Type uIota}
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) (hφi : φ i = 1)
    (h2 : (2 : O) ≠ 0) (s : Finset ι) (ε : ι → ℤ)
    (c d g : ι → Oˣ) (a b J U : ι → O)
    (hc : ∀ j ∈ s, (c j : O) = a j + b j)
    (hd : ∀ j ∈ s, (d j : O) = a j - b j)
    (hg : ∀ j ∈ s,
      (g j : O) = a j + i * b j - ((1 + i) * J j + 2 * U j))
    (hrOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hwOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hnonzero : (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) ≠ 0) :
    False := by
  have hφ2 : φ (2 : O) = 0 := by
    calc
      φ (2 : O) = φ (1 + 1) := by congr 1; ring
      _ = (1 : k) + 1 := by simp only [map_add, map_one]
      _ = 0 := CharTwo.add_self_eq_zero 1
  have hφpi : φ (1 + i) = 0 := by
    rw [map_add, map_one, hφi]
    exact CharTwo.add_self_eq_zero 1
  have hr (j : ι) (hj : j ∈ s) :
      ((d j * (c j)⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr (c j) (b j) :=
    binary_ratio_r (c j) (d j) (a j) (b j) (hc j hj) (hd j hj)
  have hw (j : ι) (hj : j ∈ s) :
      ((g j * (c j)⁻¹ : Oˣ) : O) =
        1 + (1 + i) * binaryLw (c j) i (b j) (J j) (U j) :=
    binary_ratio_w (c j) (g j) (a j) (b j) (J j) (U j) i (hc j hj) (hg j hj) hi
  have hrMap (j : ι) (hj : j ∈ s) : φ ((d j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hr j hj, map_add, map_one, map_mul, hφ2, zero_mul, add_zero]
  have hwMap (j : ι) (hj : j ∈ s) : φ ((g j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hw j hj, map_add, map_one, map_mul, hφpi, zero_mul, add_zero]
  have hrOne : (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => d j * (c j)⁻¹) ε hrMap) hrOdd
  have hwOne : (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => g j * (c j)⁻¹) ε hwMap) hwOdd
  have hrSum := first_order_sum_eq_zero_of_prod_eq_one φ (2 : O) h2 hφ2 s
    (fun j => d j * (c j)⁻¹) (fun j => binaryLr (c j) (b j)) ε hr hrOne
  have hwSum := first_order_sum_eq_zero_of_prod_eq_one φ (1 + i)
    (binary_one_add_i_ne_zero i hi h2) hφpi s
    (fun j => g j * (c j)⁻¹) (fun j => binaryLw (c j) i (b j) (J j) (U j)) ε hw hwOne
  apply hnonzero
  calc
    (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) =
        ∑ j ∈ s, ((ε j : k) * φ (binaryLr (c j) (b j)) +
          (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_add, binary_residue_sum φ (c j) i (b j) (J j) (U j) hφi]
    _ = (∑ j ∈ s, (ε j : k) * φ (binaryLr (c j) (b j))) +
        ∑ j ∈ s, (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j)) :=
      Finset.sum_add_distrib
    _ = 0 := by rw [hrSum, hwSum, add_zero]

end Residue

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryLocalFamily
section
namespace OAI

noncomputable section

namespace CirculantHadamard.BinaryLocalFamily

open scoped BigOperators
open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing
open BinaryLocalRing BinaryProductTransport

variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u) (hodd : Odd u)

/-- The actual local unit attached to one evaluated Gaussian norm element. -/
def evaluationUnit (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (S : Finset (PrimeIndex u)) : (O u)ˣ :=
  normUnit u hodd (subsetEvaluation u hu S x) (star (subsetEvaluation u hu S x))
    (by simpa only [Nat.cast_pow] using subsetEvaluation_norm u hu S x hx)

@[simp] theorem evaluationUnit_val (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (S : Finset (PrimeIndex u)) :
    (evaluationUnit u hu hodd x hx S : O u) = toLocal u (subsetEvaluation u hu S x) :=
  normUnit_val _ _ _ _ _

/-- The concrete local argument. In particular, neither local units nor a
nonzero residue sum are assumptions of this theorem. -/
theorem contradiction_of_evaluated_data (hodd : Odd u)
    (C D G : Elem GaussianRing (u ^ 2))
    (hC : C * ringStar C = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hD : D * ringStar D = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hG : G * ringStar G = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (a b U : Finset (PrimeIndex u) → B u)
    (hc : ∀ S, subsetEvaluation u hu S C = a S + b S)
    (hd : ∀ S, subsetEvaluation u hu S D = a S - b S)
    (hg : ∀ S, subsetEvaluation u hu S G =
      a S + gaussianToB u gaussianI * b S -
        ((1 + gaussianToB u gaussianI) *
          subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing)) + 2 * U S))
    (hCodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S C))) ^ m = 1)
    (hDodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S D))) ^ m = 1)
    (hGodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S G))) ^ m = 1) :
    False := by
  classical
  let c := evaluationUnit u hu hodd C hC
  let d := evaluationUnit u hu hodd D hD
  let g := evaluationUnit u hu hodd G hG
  have cval (S) : (c S : O u) = toLocal u (subsetEvaluation u hu S C) :=
    evaluationUnit_val u hu hodd C hC S
  have dval (S) : (d S : O u) = toLocal u (subsetEvaluation u hu S D) :=
    evaluationUnit_val u hu hodd D hD S
  have gval (S) : (g S : O u) = toLocal u (subsetEvaluation u hu S G) :=
    evaluationUnit_val u hu hodd G hG S
  have hr := local_alternatingProduct_ratio_has_odd_power u Finset.univ
    (fun S => subsetEvaluation u hu S D) (fun S => subsetEvaluation u hu S C)
    d c (fun S _ => dval S) (fun S _ => cval S) hDodd hCodd
  have hw := local_alternatingProduct_ratio_has_odd_power u Finset.univ
    (fun S => subsetEvaluation u hu S G) (fun S => subsetEvaluation u hu S C)
    g c (fun S _ => gval S) (fun S _ => cval S) hGodd hCodd
  apply binary_residue_contradiction (residue u) (imaginary u)
    (imaginary_sq u) (residue_imaginary u) (two_ne_zero u)
    (Finset.univ : Finset (Finset (PrimeIndex u))) subsetSign c d g
    (fun S => toLocal u (a S)) (fun S => toLocal u (b S))
    (fun S => toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))))
    (fun S => toLocal u (U S))
  · intro S _
    rw [cval, hc, map_add]
  · intro S _
    rw [dval, hd, map_sub]
  · intro S _
    rw [gval, hg]
    have hi_local : toLocal u (gaussianToB u gaussianI) = imaginary u := by
      change toLocal u ((gaussianToB u).toRingHom gaussianI) =
        ((toLocal u).comp (gaussianToB u).toRingHom) gaussianI
      exact (RingHom.comp_apply _ _ _).symm
    simp only [map_sub, map_add, map_mul, map_one, map_ofNat, hi_local]
  · simpa only [alternatingProduct, Finset.powerset_univ] using hr
  · simpa only [alternatingProduct, Finset.powerset_univ] using hw
  · have hnonzero := BinaryCharacterSum.actual_subset_J_residue_ne_zero u hu
      (toLocal u) (residue u) (fun S => (↑((c S)⁻¹) : O u)) (c ∅) rfl hodd
    have hsum : (residue u)
        (∑ S : Finset (PrimeIndex u), (subsetSign S : O u) *
          toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))) *
            (↑((c S)⁻¹) : O u)) =
        ∑ S : Finset (PrimeIndex u), (residue u)
          ((subsetSign S : O u) *
            toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))) *
              (↑((c S)⁻¹) : O u)) :=
      map_sum (residue u).toAddMonoidHom _ _
    rw [hsum] at hnonzero
    simpa only [map_mul, map_intCast, mul_assoc] using hnonzero

end CirculantHadamard.BinaryLocalFamily

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.AlternatingNorm
section
namespace OAI

universe uR uIota


namespace CirculantHadamard.AlternatingNorm

open scoped BigOperators

theorem norm_map_prod_of_const {R : Type uR} {ι : Type uIota} [CommRing R]
    (σ : R →+* ℂ) (x : ι → R) (s : Finset ι) (c : ℝ)
    (hx : ∀ i ∈ s, ‖σ (x i)‖ = c) :
    ‖σ (∏ i ∈ s, x i)‖ = c ^ s.card := by
  classical
  rw [map_prod, norm_prod]
  calc
    (∏ i ∈ s, ‖σ (x i)‖) = ∏ _i ∈ s, c := Finset.prod_congr rfl hx
    _ = c ^ s.card := by simp

/-- The numerator and denominator have equally many character factors.
Only a genuine cleared identity in `R` is required; there is no assumed norm
bound on `z`, no injectivity assumption on `σ`, and no fraction-field extension.
-/
theorem norm_eq_one_of_balanced_products {R : Type uR} {ι : Type uIota} [CommRing R]
    (σ : R →+* ℂ) (x : ι → R) (numerator denominator : Finset ι)
    (z : R) (c : ℝ) (hc : 0 < c)
    (hcard : numerator.card = denominator.card)
    (hnumerator : ∀ i ∈ numerator, ‖σ (x i)‖ = c)
    (hdenominator : ∀ i ∈ denominator, ‖σ (x i)‖ = c)
    (hclear : z * (∏ i ∈ denominator, x i) = ∏ i ∈ numerator, x i) :
    ‖σ z‖ = 1 := by
  have hmap := congrArg σ hclear
  rw [map_mul] at hmap
  have hnorm := congrArg norm hmap
  rw [norm_mul,
    norm_map_prod_of_const σ x denominator c hdenominator,
    norm_map_prod_of_const σ x numerator c hnumerator,
    hcard] at hnorm
  have hpositive : 0 < c ^ denominator.card := pow_pos hc _
  nlinarith

end CirculantHadamard.AlternatingNorm

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.AlternatingField
section
namespace OAI

universe uI uK uR


namespace CirculantHadamard

open scoped BigOperators

theorem oddSubsetProduct_ne_zero {I : Type uI} {K : Type uK} [Field K]
    (t : Finset I) (x : Finset I → K)
    (hx : ∀ S ⊆ t, x S ≠ 0) : oddSubsetProduct t x ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro S hS
  exact hx S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)

/-- An equality in the fraction field genuinely clears to the coefficient
ring. The field embedding is used only to reflect this polynomial identity. -/
theorem cleared_alternatingProduct_identity {I : Type uI} {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (t : Finset I) (x : Finset I → R) (z : R)
    (hx : ∀ S ⊆ t, f (x S) ≠ 0)
    (hz : f z = alternatingProduct t (fun S => f (x S))) :
    z * oddSubsetProduct t x = evenSubsetProduct t x := by
  have hodd : f (oddSubsetProduct t x) =
      oddSubsetProduct t (fun S => f (x S)) :=
    map_oddSubsetProduct f.toMonoidHom t x
  have heven : f (evenSubsetProduct t x) =
      evenSubsetProduct t (fun S => f (x S)) :=
    map_evenSubsetProduct f.toMonoidHom t x
  apply hf
  rw [map_mul, hodd, heven, hz, alternatingProduct_eq_even_div_odd]
  exact div_mul_cancel₀ _ (oddSubsetProduct_ne_zero t (fun S => f (x S)) hx)

/-- Once the actual alternating fraction belongs to the coefficient ring,
every complex homomorphism has modulus one if each character value has the
same positive modulus. Subset parity supplies the equal factor counts. -/
theorem norm_hom_integral_alternatingProduct {I : Type uI} {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (t : Finset I) (ht : t.Nonempty) (x : Finset I → R) (z : R)
    (hx : ∀ S ⊆ t, f (x S) ≠ 0)
    (hz : f z = alternatingProduct t (fun S => f (x S)))
    (σ : R →+* ℂ) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ S ⊆ t, ‖σ (x S)‖ = c) : ‖σ z‖ = 1 := by
  classical
  apply AlternatingNorm.norm_eq_one_of_balanced_products σ x
    (t.powerset.filter (fun S => Even S.card))
    (t.powerset.filter (fun S => Odd S.card)) z c hc
    (card_even_subsets_eq_card_odd_subsets t ht)
  · intro S hS
    exact hnorm S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  · intro S hS
    exact hnorm S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  · exact cleared_alternatingProduct_identity f hf t x z hx hz

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.LocalizationIntersection
section
namespace OAI

universe uR uK


namespace CirculantHadamard

/-- If every maximal ideal admits a denominator outside it taking `z` into the
base ring's image, then `z` itself lies in that image. -/
theorem exists_base_of_local_denominators
    {R : Type uR} {K : Type uK} [CommRing R] [CommRing K] [Algebra R K]
    (z : K)
    (hz : ∀ m : MaximalSpectrum R, ∃ a s : R,
      s ∉ m.asIdeal ∧ algebraMap R K s * z = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = z := by
  classical
  by_contra h
  let denom : Ideal R :=
    (1 : Submodule R K).comap (LinearMap.toSpanSingleton R K z)
  have hdenom : (1 : R) ∉ denom := by
    simpa [denom] using h
  obtain ⟨m, hm, hle⟩ :=
    denom.exists_le_maximal (denom.ne_top_iff_one.mpr hdenom)
  obtain ⟨a, s, hs, hsa⟩ := hz ⟨m, hm⟩
  apply hs
  apply hle
  change s • z ∈ (1 : Submodule R K)
  apply Submodule.mem_one.mpr
  exact ⟨a, by simpa only [Algebra.smul_def] using hsa.symm⟩

section FractionField

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Membership in every maximal localization, realized inside a common fraction
field, gives a base-ring representative. -/
theorem exists_base_of_mem_all_maximal_localizations
    {z : K}
    (hz : ∀ m : MaximalSpectrum R,
      z ∈ Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :
    ∃ r : R, algebraMap R K r = z := by
  have hzall : z ∈ (⨅ m : MaximalSpectrum R,
      Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :=
    Algebra.mem_iInf.mpr hz
  rw [MaximalSpectrum.iInf_localization_eq_bot R K] at hzall
  exact Algebra.mem_bot.mp hzall

/-- A fraction-field element represented by an actual element of each maximal
local ring is the image of a base-ring element. -/
theorem exists_base_of_localization_images
    {z : K}
    (hz : ∀ m : MaximalSpectrum R, ∃ y : Localization.AtPrime m.asIdeal,
      Localization.mapToFractionRing K m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal)
        m.asIdeal.primeCompl_le_nonZeroDivisors y = z) :
    ∃ r : R, algebraMap R K r = z := by
  apply exists_base_of_mem_all_maximal_localizations
  intro m
  obtain ⟨y, hy⟩ := hz m
  change ∃ (a s : R) (_ : s ∈ m.asIdeal.primeCompl),
    z = algebraMap R K a * (algebraMap R K s)⁻¹
  exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
    K m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors
    (Localization.AtPrime m.asIdeal) z).mp ⟨y, hy⟩

end FractionField

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.ResidueOneAssociation
section
namespace OAI

universe uS uk


namespace CirculantHadamard.LocalComparison

variable {S : Type uS} {k : Type uk} [CommRing S] [CommRing k]

/-- `x` differs from `y` by multiplication by a unit whose residue is one. -/
def ResidueOneAssociated (residue : S →+* k) (x y : S) : Prop :=
  ∃ u : Sˣ, x = (u : S) * y ∧ residue (u : S) = 1

theorem residue_inv_eq_one (residue : S →+* k) {u : Sˣ}
    (hu : residue (u : S) = 1) : residue (↑u⁻¹ : S) = 1 := by
  have h : residue (u : S) * residue (↑u⁻¹ : S) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simpa only [hu, one_mul] using h

namespace ResidueOneAssociated

variable {residue : S →+* k} {x y z c x' y' : S}

theorem refl (residue : S →+* k) (x : S) :
    ResidueOneAssociated residue x x := by
  exact ⟨1, by simp, by simp⟩

theorem symm (h : ResidueOneAssociated residue x y) :
    ResidueOneAssociated residue y x := by
  obtain ⟨u, hxy, hu⟩ := h
  refine ⟨u⁻¹, ?_, residue_inv_eq_one residue hu⟩
  rw [hxy, Units.inv_mul_cancel_left]

theorem trans (hxy : ResidueOneAssociated residue x y)
    (hyz : ResidueOneAssociated residue y z) : ResidueOneAssociated residue x z := by
  obtain ⟨u, hxy, hu⟩ := hxy
  obtain ⟨v, hyz, hv⟩ := hyz
  refine ⟨u * v, ?_, ?_⟩
  · simp only [Units.val_mul, hxy, hyz, mul_assoc]
  · simp only [Units.val_mul, map_mul, hu, hv, one_mul]

theorem residue_eq (h : ResidueOneAssociated residue x y) : residue x = residue y := by
  obtain ⟨u, hxy, hu⟩ := h
  rw [hxy, map_mul, hu, one_mul]

theorem mul_left (h : ResidueOneAssociated residue x y) (c : S) :
    ResidueOneAssociated residue (c * x) (c * y) := by
  obtain ⟨u, hxy, hu⟩ := h
  refine ⟨u, ?_, hu⟩
  rw [hxy]
  ac_rfl

/-- A common regular scalar can be cancelled even if the ambient ring has
zero divisors. This is the form used when comparing scalar-divided factors. -/
theorem mul_left_iff (residue : S →+* k) (hc : IsLeftRegular c) :
    ResidueOneAssociated residue (c * x) (c * y) ↔
      ResidueOneAssociated residue x y := by
  constructor
  · rintro ⟨u, hxy, hu⟩
    refine ⟨u, hc ?_, hu⟩
    calc
      c * x = (u : S) * (c * y) := hxy
      _ = c * ((u : S) * y) := by ac_rfl
  · exact fun h => h.mul_left c

theorem mul (h : ResidueOneAssociated residue x y)
    (h' : ResidueOneAssociated residue x' y') :
    ResidueOneAssociated residue (x * x') (y * y') := by
  obtain ⟨u, hxy, hu⟩ := h
  obtain ⟨v, hxy', hv⟩ := h'
  refine ⟨u * v, ?_, ?_⟩
  · rw [hxy, hxy', Units.val_mul]
    ac_rfl
  · simp only [Units.val_mul, map_mul, hu, hv, one_mul]

/-- With equal nonzero products, a comparison for one factor gives the inverse
unit as comparison for the other factor. Only regularity of `y` is needed. -/
theorem product_complement_of_regular (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hy : IsLeftRegular y) :
    ResidueOneAssociated residue x' y' := by
  obtain ⟨u, hxy, hu⟩ := h
  have hcancel : (u : S) * x' = y' := by
    apply hy
    calc
      y * ((u : S) * x') = ((u : S) * y) * x' := by ac_rfl
      _ = x * x' := by rw [← hxy]
      _ = y * y' := hprod
  refine ⟨u⁻¹, ?_, residue_inv_eq_one residue hu⟩
  rw [← hcancel, Units.inv_mul_cancel_left]

/-- The two-factor step used in the character-comparison base case. -/
theorem product_complement [IsDomain S] (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hne : y * y' ≠ 0) :
    ResidueOneAssociated residue x' y' := by
  have hy : y ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
  exact h.product_complement_of_regular hprod (fun _ _ h => mul_left_cancel₀ hy h)

theorem mul_left_iff_of_ne_zero [IsDomain S] (residue : S →+* k) (hc : c ≠ 0) :
    ResidueOneAssociated residue (c * x) (c * y) ↔
      ResidueOneAssociated residue x y :=
  mul_left_iff residue (fun _ _ h => mul_left_cancel₀ hc h)

/-- Two units with the same residue differ by a unit with residue one. -/
theorem of_isUnit_of_residue_eq (residue : S →+* k)
    (hx : IsUnit x) (hy : IsUnit y) (hres : residue x = residue y) :
    ResidueOneAssociated residue x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨u * v⁻¹, ?_, ?_⟩
  · simp only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rw [Units.val_mul, map_mul, hres, ← map_mul, Units.mul_inv, map_one]

end ResidueOneAssociated

section ActualResidueField

variable [IsLocalRing S] {x y : S}

/-- Equality to the residue of a unit forces an element of a local ring to be
a unit. The residue map is the actual quotient by the maximal ideal. -/
theorem isUnit_of_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  rw [hres]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit y).mpr hy

/-- Concrete local-ring base case: an augmentation unit and agreement in the
residue field suffice to construct the comparison unit. -/
theorem residueOneAssociated_of_isUnit_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) :
    ResidueOneAssociated (IsLocalRing.residue S) x y :=
  ResidueOneAssociated.of_isUnit_of_residue_eq (IsLocalRing.residue S)
    (isUnit_of_residue_eq hy hres) hy hres

end ActualResidueField

end CirculantHadamard.LocalComparison

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.LocalDVR
section
namespace OAI

universe uR


noncomputable section

namespace CirculantHadamard.LocalDVR

open IsLocalRing IsDiscreteValuationRing

section PrincipalMaximalIdeal

variable {R : Type uR} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

/-- A nonzero generator of the maximal ideal of a Noetherian local domain
proves that the ring is a DVR. -/
theorem isDiscreteValuationRing_of_maximalIdeal_eq_span {π : R}
    (hπ : π ≠ 0) (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    IsDiscreteValuationRing R := by
  have hmax : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro hzero
    apply hπ
    exact Ideal.span_singleton_eq_bot.mp (hspan.symm.trans hzero)
  have hfield : ¬ IsField R := isField_iff_maximalIdeal_eq.not.mpr hmax
  have hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal := ⟨⟨π, hspan⟩⟩
  exact ((IsDiscreteValuationRing.TFAE R hfield).out 4 0).mp hprincipal

/-- The actual chosen generator factors every nonzero element into a unit
times a natural power. -/
theorem eq_unit_mul_pow_of_maximalIdeal_eq_span {π x : R}
    (hπ : π ≠ 0) (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), x = (u : R) * π ^ n := by
  let : IsDiscreteValuationRing R :=
    isDiscreteValuationRing_of_maximalIdeal_eq_span hπ hspan
  exact eq_unit_mul_pow_irreducible hx ((irreducible_iff_uniformizer π).mpr hspan)

end PrincipalMaximalIdeal

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Normalize the additive valuation using the concrete uniformizer relation. -/
theorem addVal_eq_of_unit_mul_uniformizer_pow {π p : R} {u : Rˣ} {D : ℕ}
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hp : p = (u : R) * π ^ D) :
    addVal R p = (D : ℕ∞) :=
  addVal_def p u ((irreducible_iff_uniformizer π).mpr hspan) D hp

/-- Right-unit version, convenient for the factorization of a rational prime. -/
theorem addVal_eq_of_uniformizer_pow_mul_unit {π p b : R} {D : ℕ}
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hb : IsUnit b)
    (hp : p = π ^ D * b) : addVal R p = (D : ℕ∞) := by
  obtain ⟨u, rfl⟩ := hb
  exact addVal_eq_of_unit_mul_uniformizer_pow hspan (hp.trans (mul_comm _ _))

private theorem finite_add_eq {a b : ℕ∞} {N : ℕ} (h : a + b = (N : ℕ∞)) :
    ∃ m n : ℕ, a = (m : ℕ∞) ∧ b = (n : ℕ∞) ∧ m + n = N := by
  have ha : a ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_right zero_le
  have hb : b ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_left zero_le
  obtain ⟨m, hm, _⟩ := ENat.le_natCast_iff.mp ha
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp hb
  refine ⟨m, n, hm, hn, ?_⟩
  rw [hm, hn, ← Nat.cast_add] at h
  exact_mod_cast h

/-- If the valuation of a product is at least twice that of `p`, one factor
is divisible by `p`. The value of `p` is allowed to be ramified. -/
theorem dvd_or_dvd_of_mul_eq_pow_mul_unit {p x y b : R} {D e : ℕ}
    (_hp : p ≠ 0) (_hD : 0 < D) (hpval : addVal R p = (D : ℕ∞))
    (he : 2 ≤ e) (hb : IsUnit b) (hxy : x * y = p ^ e * b) :
    p ∣ x ∨ p ∣ y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, addVal_pow, hpval,
    addVal_eq_zero_iff.mpr hb, add_zero] at hv
  have hv' : addVal R x + addVal R y = ((e * D : ℕ) : ℕ∞) := by
    simpa only [nsmul_eq_mul, Nat.cast_mul] using hv
  obtain ⟨m, n, hm, hn, hmn⟩ := finite_add_eq hv'
  have heD : 2 * D ≤ e * D := Nat.mul_le_mul_right D he
  have hsplit : D ≤ m ∨ D ≤ n := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_le_iff_dvd.mp
    rw [hpval, hm]
    exact_mod_cast hx
  · right
    apply addVal_le_iff_dvd.mp
    rw [hpval, hn]
    exact_mod_cast hy

/-- A product with valuation one has a unit factor. This is the unramified
base case of the integral division argument. -/
theorem isUnit_or_isUnit_of_mul_eq_uniformizer_mul_unit {p x y b : R}
    (hpval : addVal R p = 1) (hb : IsUnit b) (hxy : x * y = p * b) :
    IsUnit x ∨ IsUnit y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, hpval, addVal_eq_zero_iff.mpr hb, add_zero] at hv
  obtain ⟨m, n, hm, hn, hmn⟩ := finite_add_eq (N := 1) hv
  have hsplit : m = 0 ∨ n = 0 := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_eq_zero_iff.mp
    simpa only [hx, Nat.cast_zero] using hm
  · right
    apply addVal_eq_zero_iff.mp
    simpa only [hy, Nat.cast_zero] using hn

end Valuation

end CirculantHadamard.LocalDVR

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicLocalBase
section
namespace OAI

universe uK uR uA


noncomputable section

namespace CirculantHadamard.CyclotomicLocalBase

open IsLocalRing

/-- The cyclotomic order as an actual subalgebra of the complex numbers. -/
abbrev Order (eta : ℂ) := Algebra.adjoin ℤ ({eta} : Set ℂ)

/-- The distinguished root in its integral order. -/
def generator (eta : ℂ) : Order eta :=
  ⟨eta, Algebra.subset_adjoin (Set.mem_singleton eta)⟩

/-- Localization of the actual cyclotomic order at the chosen prime ideal. -/
abbrev Local (eta : ℂ) (m : Ideal (Order eta)) [m.IsPrime] :=
  Localization.AtPrime m

variable {eta : ℂ} {L p : ℕ}

theorem order_pos (hpL : ¬ p ∣ L) : 0 < L := by
  apply Nat.pos_of_ne_zero
  intro h
  apply hpL
  rw [h]
  exact dvd_zero p

/-- The genuine finite integral power basis of `ℤ[eta]`. -/
def powerBasis (hη : IsPrimitiveRoot eta L) (hL : 0 < L) :
    PowerBasis ℤ (Order eta) :=
  Algebra.adjoin.powerBasis' (hη.isIntegral hL)

@[simp] theorem powerBasis_gen (hη : IsPrimitiveRoot eta L) (hL : 0 < L) :
    (powerBasis hη hL).gen = generator eta := by
  simp [powerBasis, generator]

theorem order_finite (hη : IsPrimitiveRoot eta L) (hL : 0 < L) :
    Module.Finite ℤ (Order eta) := (powerBasis hη hL).finite

theorem order_free (hη : IsPrimitiveRoot eta L) (hL : 0 < L) :
    Module.Free ℤ (Order eta) := Module.Free.of_basis (powerBasis hη hL).basis

theorem order_noetherian (hη : IsPrimitiveRoot eta L) (hL : 0 < L) :
    IsNoetherianRing (Order eta) := by
  let := order_finite hη hL
  exact IsNoetherianRing.of_finite ℤ (Order eta)

theorem generator_pow (hη : IsPrimitiveRoot eta L) :
    generator eta ^ L = 1 := by
  apply Subtype.ext
  exact hη.pow_eq_one

theorem local_noetherian (hη : IsPrimitiveRoot eta L) (hL : 0 < L)
    (m : Ideal (Order eta)) [m.IsPrime] : IsNoetherianRing (Local eta m) :=
  IsLocalization.isNoetherianRing m.primeCompl (Local eta m) (order_noetherian hη hL)

instance local_charZero (m : Ideal (Order eta)) [m.IsPrime] : CharZero (Local eta m) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective (Local eta m) m.primeCompl_le_nonZeroDivisors)

theorem prime_ne_zero (hp : p.Prime) (m : Ideal (Order eta)) [m.IsPrime] :
    (p : Local eta m) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

theorem order_not_mem (hp : p.Prime) (hpL : ¬ p ∣ L)
    (m : Ideal (Order eta)) [hm : m.IsMaximal] (hpm : (p : Order eta) ∈ m) :
    (L : Order eta) ∉ m := by
  intro hLm
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd.mpr hpL).cast (R := Order eta)
  have hone : (1 : Order eta) ∈ m := by
    rw [← hab]
    exact m.add_mem (m.mul_mem_left a hpm) (m.mul_mem_left b hLm)
  exact hm.ne_top (m.eq_top_iff_one.mpr hone)

theorem order_isUnit (hp : p.Prime) (hpL : ¬ p ∣ L)
    (m : Ideal (Order eta)) [m.IsMaximal] (hpm : (p : Order eta) ∈ m) :
    IsUnit (L : Local eta m) := by
  simpa only [map_natCast] using
    (IsLocalization.AtPrime.isUnit_to_map_iff (Local eta m) m (L : Order eta)).mpr
      (order_not_mem hp hpL m hpm)

private theorem formallyUnramified_of_powerBasis
    {K : Type uK} {R : Type uR} {A : Type uA} [CommRing K] [CommRing R] [CommRing A] [Algebra K R] [Algebra K A]
    [Algebra R A] [IsScalarTower K R A] (M : Submonoid R) [IsLocalization M A]
    (pb : PowerBasis K R) {L : ℕ} (hL : 0 < L) (hroot : pb.gen ^ L = 1)
    (hLu : IsUnit (L : A)) : Algebra.FormallyUnramified K A := by
  let z : A := algebraMap R A pb.gen
  let D : Derivation K A (KaehlerDifferential K A) := KaehlerDifferential.D K A
  have hzpow : z ^ L = 1 := by
    dsimp [z]
    rw [← map_pow, hroot, map_one]
  have hzunit : IsUnit z := by
    apply IsUnit.of_mul_eq_one (z ^ (L - 1))
    rw [← pow_succ', Nat.sub_add_cancel hL, hzpow]
  have hDroot : D z = 0 := by
    have hpow := congrArg D hzpow
    have hzero : (L : A) • (z ^ (L - 1) • D z : KaehlerDifferential K A) =
        (0 : KaehlerDifferential K A) := by
      simpa only [Derivation.leibniz_pow, Derivation.map_one_eq_zero,
        Nat.cast_smul_eq_nsmul A] using hpow
    have hcancel : z ^ (L - 1) • D z = (0 : KaehlerDifferential K A) :=
      hLu.smul_eq_zero.mp hzero
    exact (hzunit.pow (L - 1)).smul_eq_zero.mp hcancel
  have hDorder (a : R) : D (algebraMap R A a) = 0 := by
    obtain ⟨f, hf⟩ := pb.exists_eq_aeval' a
    rw [hf]
    change D ((IsScalarTower.toAlgHom K R A) (Polynomial.aeval pb.gen f)) = 0
    rw [← Polynomial.aeval_algHom_apply, Derivation.map_aeval]
    change Polynomial.aeval z (Polynomial.derivative f) • D z = 0
    rw [hDroot, smul_zero]
  have hD (x : A) : D x = 0 := by
    obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj M x
    have hd := congrArg D hxs
    rw [Derivation.leibniz, hDorder, hDorder, smul_zero, zero_add] at hd
    exact (IsLocalization.map_units A s).smul_eq_zero.mp hd
  have hspan : Submodule.span A (Set.range D) = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro x ⟨y, rfl⟩
    exact hD y
  have htop : (⊤ : Submodule A (KaehlerDifferential K A)) = ⊥ :=
    (KaehlerDifferential.span_range_derivation K A).symm.trans hspan
  have hall (x : KaehlerDifferential K A) : x = 0 := by
    have hx : x ∈ (⊤ : Submodule A (KaehlerDifferential K A)) := trivial
    rw [htop, Submodule.mem_bot] at hx
    exact hx
  exact ⟨⟨fun x y => (hall x).trans (hall y).symm⟩⟩

/-- Every absolute differential vanishes: the root has invertible derivative,
and the same vanishing extends across the localization denominators. -/
theorem formallyUnramified (hη : IsPrimitiveRoot eta L) (hp : p.Prime)
    (hpL : ¬ p ∣ L) (m : Ideal (Order eta)) [m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) : Algebra.FormallyUnramified ℤ (Local eta m) := by
  let : Algebra (Order eta) (Local eta m) :=
    OreLocalization.instAlgebra (R := Order eta) (S := m.primeCompl) (R₀ := Order eta)
  let : SMul (Order eta) (Local eta m) :=
    (inferInstance : Algebra (Order eta) (Local eta m)).toSMul
  let : Module (Order eta) (Local eta m) := Algebra.toModule
  let : IsScalarTower ℤ (Order eta) (Local eta m) :=
    AddCommGroup.intIsScalarTower
  apply formallyUnramified_of_powerBasis m.primeCompl
    (powerBasis hη (order_pos hpL)) (order_pos hpL)
  · simpa only [powerBasis_gen] using generator_pow hη
  · exact order_isUnit hp hpL m hpm

/-- The rational prime ideal lies under the chosen maximal ideal. -/
theorem liesOver_prime (hp : p.Prime) (m : Ideal (Order eta)) [hm : m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) : m.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  constructor
  apply hmax.eq_of_le
  · apply (Ideal.ne_top_iff_one _).mpr
    change algebraMap ℤ (Order eta) 1 ∉ m
    simpa only [map_one] using (m.ne_top_iff_one.mp hm.ne_top)
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change algebraMap ℤ (Order eta) (p : ℤ) ∈ m
    simpa only [Ideal.mem_under, map_natCast, map_intCast, Int.cast_natCast] using hpm

/-- The maximal ideal is generated by the actual rational prime. -/
theorem maximalIdeal_eq_span (hη : IsPrimitiveRoot eta L) (hp : p.Prime)
    (hpL : ¬ p ∣ L) (m : Ideal (Order eta)) [m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) :
    maximalIdeal (Local eta m) = Ideal.span {(p : Local eta m)} := by
  let := order_finite hη (order_pos hpL)
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : P.IsPrime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  let : m.LiesOver P := liesOver_prime hp m hpm
  let := Localization.AtPrime.algebraOfLiesOver P m
  have hU : Algebra.IsUnramifiedAt ℤ m := formallyUnramified hη hp hpL m hpm
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq ℤ P m).mp hU).2
  simpa only [P, Ideal.map_span, Set.image_singleton, map_natCast, map_intCast,
    Int.cast_natCast] using
    hmap.symm

theorem prime_not_isUnit (m : Ideal (Order eta)) [m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) : ¬ IsUnit (p : Local eta m) := by
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Local eta m) m
    (p : Order eta)).mpr hpm
  simpa only [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmem

/-- The concrete unramified localization is a discrete valuation ring. -/
theorem isDiscreteValuationRing (hη : IsPrimitiveRoot eta L) (hp : p.Prime)
    (hpL : ¬ p ∣ L) (m : Ideal (Order eta)) [m.IsMaximal]
    (hpm : (p : Order eta) ∈ m) : IsDiscreteValuationRing (Local eta m) := by
  let := local_noetherian hη (order_pos hpL) m
  exact LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (prime_ne_zero hp m) (maximalIdeal_eq_span hη hp hpL m hpm)

end CirculantHadamard.CyclotomicLocalBase

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicAwayLocal
section
namespace OAI

universe uR uS


noncomputable section

namespace CirculantHadamard.CyclotomicAwayLocal

open CyclotomicRings IsLocalRing

/-- The actual prime ideal on the coefficient ring with one direction omitted. -/
abbrev awayPrime (u p : ℕ) (m : Ideal (B u)) : Ideal (awayRing u p) :=
  m.comap (awayInclusion u p).toRingHom

/-- The coefficient localization used in the prime-direction comparison. -/
abbrev AwayLocal (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :=
  Localization.AtPrime (awayPrime u p m)

instance awayLocal_algebra (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :
    Algebra (awayRing u p) (AwayLocal u p m) :=
  OreLocalization.instAlgebra (R := awayRing u p) (R₀ := awayRing u p)
    (S := (awayPrime u p m).primeCompl)

/-- Integrality follows from the genuine finite integer module structure of
the global root ring, through the coefficient inclusion. -/
theorem awayInclusion_isIntegral (u p : ℕ) :
    (awayInclusion u p).toRingHom.IsIntegral := by
  apply RingHom.IsIntegral.tower_top (algebraMap ℤ (awayRing u p))
    (awayInclusion u p).toRingHom
  rw [show (awayInclusion u p).toRingHom.comp (algebraMap ℤ (awayRing u p)) =
    algebraMap ℤ (B u) from Subsingleton.elim _ _]
  exact Algebra.IsIntegral.isIntegral

theorem awayMaximal (u p : ℕ) (m : Ideal (B u)) [m.IsMaximal] :
    (awayPrime u p m).IsMaximal :=
  maximal_comap_of_integral (awayInclusion u p).toRingHom
    (awayInclusion_isIntegral u p) m

private theorem natCast_mem_comap_of_mem {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal S) (p : ℕ) (h : (p : S) ∈ m) :
    (p : R) ∈ m.comap f := by
  change f (p : R) ∈ m
  simpa only [map_natCast] using h

theorem prime_mem_awayPrime (u p : ℕ) (m : Ideal (B u))
    (hpm : (p : B u) ∈ m) : (p : awayRing u p) ∈ awayPrime u p m :=
  natCast_mem_comap_of_mem (awayInclusion u p).toRingHom m p hpm

instance awayLocal_charZero (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :
    CharZero (AwayLocal u p m) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective (AwayLocal u p m)
      (awayPrime u p m).primeCompl_le_nonZeroDivisors)

instance awayLocal_noetherian (u p : ℕ) (m : Ideal (B u)) [m.IsPrime] :
    IsNoetherianRing (AwayLocal u p m) :=
  IsLocalization.isNoetherianRing (awayPrime u p m).primeCompl (AwayLocal u p m)
    (IsNoetherianRing.of_finite ℤ (awayRing u p))

private theorem maximalIdeal_eq_span_of_eq (S : Subalgebra ℤ ℂ) {z : ℂ} {L p : ℕ}
    (hS : S = CyclotomicLocalBase.Order z) (hz : IsPrimitiveRoot z L)
    (hp : p.Prime) (hpL : ¬ p ∣ L) (m : Ideal S) [m.IsMaximal]
    (hpm : (p : S) ∈ m) :
    maximalIdeal (Localization.AtPrime m) = Ideal.span {(p : Localization.AtPrime m)} := by
  subst S
  exact CyclotomicLocalBase.maximalIdeal_eq_span hz hp hpL m hpm

/-- The maximal ideal of the exact contracted localization is generated by
the rational prime; no ring-property premise is assumed. -/
theorem awayLocal_maximalIdeal_eq_span (u p : ℕ) (hu : Odd u)
    (hp : p ∈ u.primeFactors) (m : Ideal (B u)) [m.IsMaximal]
    (hpm : (p : B u) ∈ m) :
    maximalIdeal (AwayLocal u p m) = Ideal.span {(p : AwayLocal u p m)} := by
  let := awayMaximal u p m
  exact maximalIdeal_eq_span_of_eq (awayRing u p) (awayRing_eq_singleton u p hu)
    (eta_isPrimitiveRoot u p hu) (Nat.prime_of_mem_primeFactors hp)
    (prime_not_dvd_awayOrder u p hu hp) (awayPrime u p m)
    (prime_mem_awayPrime u p m hpm)

theorem awayLocal_prime_ne_zero (u p : ℕ) (hp : p ∈ u.primeFactors)
    (m : Ideal (B u)) [m.IsPrime] : (p : AwayLocal u p m) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem awayLocal_prime_not_isUnit (u p : ℕ) (m : Ideal (B u)) [m.IsMaximal]
    (hpm : (p : B u) ∈ m) : ¬ IsUnit (p : AwayLocal u p m) := by
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff (AwayLocal u p m)
    (awayPrime u p m) (p : awayRing u p)).mpr (prime_mem_awayPrime u p m hpm)
  simpa only [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmem

theorem awayLocal_isDiscreteValuationRing (u p : ℕ) (hu : Odd u)
    (hp : p ∈ u.primeFactors) (m : Ideal (B u)) [m.IsMaximal]
    (hpm : (p : B u) ∈ m) : IsDiscreteValuationRing (AwayLocal u p m) :=
  LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (awayLocal_prime_ne_zero u p hp m)
    (awayLocal_maximalIdeal_eq_span u p hu hp m hpm)

end CirculantHadamard.CyclotomicAwayLocal

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicProjection
section
namespace OAI

universe uR uS


noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [Semiring R] {m n l : ℕ}

/-- The quotient of cyclic group rings induced by reduction of indices. -/
def cyclicProjection (h : m ∣ n) : Elem R n →+* Elem R m :=
  AddMonoidAlgebra.mapDomainRingHom R (ZMod.castHom h (ZMod m)).toAddMonoidHom

variable {R}

theorem cyclicProjection_apply (h : m ∣ n) (F : Elem R n) :
    cyclicProjection R h F = AddMonoidAlgebra.mapDomain (ZMod.castHom h (ZMod m)) F := rfl

@[simp] theorem cyclicProjection_single (h : m ∣ n) (a : ZMod n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single (ZMod.castHom h (ZMod m) a) r :=
  AddMonoidAlgebra.mapDomain_single

@[simp] theorem cyclicProjection_single_zero (h : m ∣ n) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r := by
  simp

@[simp] theorem cyclicProjection_scalar (h : m ∣ n) (r : R) :
    cyclicProjection R h (scalar n r) = scalar m r := by
  exact cyclicProjection_single_zero h r

@[simp] theorem cyclicProjection_generator (h : m ∣ n) :
    cyclicProjection R h (AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1 := by
  simp only [cyclicProjection_single, map_one]

@[simp] theorem cyclicProjection_single_natCast (h : m ∣ n) (a : ℕ) (r : R) :
    cyclicProjection R h (AddMonoidAlgebra.single (a : ZMod n) r) =
      AddMonoidAlgebra.single (a : ZMod m) r := by
  simp

@[simp] theorem cyclicProjection_self (F : Elem R n) :
    cyclicProjection R (dvd_refl n) F = F := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (ZMod.castHom (dvd_refl n) (ZMod n)) F.coeff = F.coeff
  simp [ZMod.castHom_self]

theorem cyclicProjection_comp (h₁ : l ∣ m) (h₂ : m ∣ n) (F : Elem R n) :
    cyclicProjection R h₁ (cyclicProjection R h₂ F) =
      cyclicProjection R (dvd_trans h₁ h₂) F := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (ZMod.castHom h₁ (ZMod l))
      (Finsupp.mapDomain (ZMod.castHom h₂ (ZMod m)) F.coeff) =
    Finsupp.mapDomain (ZMod.castHom (dvd_trans h₁ h₂) (ZMod l)) F.coeff
  rw [← Finsupp.mapDomain_comp]
  have hcomp : (ZMod.castHom h₁ (ZMod l) : ZMod m → ZMod l) ∘
      (ZMod.castHom h₂ (ZMod m) : ZMod n → ZMod m) =
      (ZMod.castHom (dvd_trans h₁ h₂) (ZMod l) : ZMod n → ZMod l) :=
    congrArg (fun f : ZMod n →+* ZMod l => (f : ZMod n → ZMod l))
      (ZMod.castHom_comp h₁ h₂)
  rw [hcomp]

/-- Any additive coefficient evaluation factors through the quotient exactly
when its index function is pulled back along reduction. -/
theorem sum_cyclicProjection {S : Type uS} [AddCommMonoid S]
    (h : m ∣ n) (F : Elem R n) (v : ZMod m → R →+ S) :
    (cyclicProjection R h F).coeff.sum (fun a r => v a r) =
      F.coeff.sum (fun a r => v (ZMod.castHom h (ZMod m) a) r) :=
  Finsupp.sum_mapDomain_index_addMonoidHom v

/-- Evaluation at the trivial character is unchanged by the cyclic quotient. -/
@[simp] theorem augmentation_cyclicProjection (h : m ∣ n) (F : Elem R n) :
    augmentation m (cyclicProjection R h F) = augmentation n F := by
  change (cyclicProjection R h F).coeff.sum (fun _ r => r * 1) =
    F.coeff.sum (fun _ r => r * 1)
  simp only [mul_one]
  exact sum_cyclicProjection h F (fun _ => AddMonoidHom.id R)

section Star

variable [StarRing R] [NeZero m] [NeZero n]

/-- Quotienting the indices commutes with conjugation and index reversal. -/
@[simp] theorem cyclicProjection_ringStar (h : m ∣ n) (F : Elem R n) :
    cyclicProjection R h (ringStar F) = ringStar (cyclicProjection R h F) := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change cyclicProjection R h (ringStar ((F : Elem R n) + G)) =
      ringStar (cyclicProjection R h ((F : Elem R n) + G))
    calc
      _ = cyclicProjection R h (ringStar F + ringStar G) :=
        congrArg (cyclicProjection R h) (ringStar_add F G)
      _ = cyclicProjection R h (ringStar F) + cyclicProjection R h (ringStar G) :=
        (cyclicProjection R h).map_add _ _
      _ = ringStar (cyclicProjection R h F) + ringStar (cyclicProjection R h G) :=
        congrArg₂ (· + ·) hF hG
      _ = ringStar (cyclicProjection R h F + cyclicProjection R h G) :=
        (ringStar_add _ _).symm
      _ = _ := congrArg ringStar ((cyclicProjection R h).map_add F G).symm
  · intro a r
    simp only [ringStar_single, cyclicProjection_single, map_neg]

/-- A scalar convolution norm descends to the quotient cyclic group. -/
theorem cyclicProjection_norm (h : m ∣ n) {F : Elem R n} {r : R}
    (hnorm : F * ringStar F = scalar n r) :
    cyclicProjection R h F * ringStar (cyclicProjection R h F) = scalar m r := by
  have hq := congrArg (cyclicProjection R h) hnorm
  simpa only [map_mul, cyclicProjection_ringStar, cyclicProjection_scalar] using hq

end Star

end CirculantHadamard

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicScalarDivision
section
namespace OAI

universe uR uG uH


noncomputable section

namespace CirculantHadamard

section DivisionExists

variable {R : Type uR} {G : Type uG} [CommRing R] [AddMonoid G] [finiteG : Finite G]

/-- Coefficientwise divisibility produces an actual element of the finite
group algebra whose scalar multiple is the original element. -/
theorem scalar_division_exists (p : R) (F : AddMonoidAlgebra R G)
    (hF : ∀ g, p ∣ F.coeff g) :
    ∃ F' : AddMonoidAlgebra R G, F = AddMonoidAlgebra.single (0 : G) p * F' := by
  classical
  let d : G → R := fun g => Classical.choose (hF g)
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm d), ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  exact Classical.choose_spec (hF g)

/-- Multiplication by a scalar makes every coefficient divisible by that scalar. -/
theorem scalar_division_coefficients [Finite G] (p : R) (F : AddMonoidAlgebra R G) :
    ∀ g, p ∣ (AddMonoidAlgebra.single (0 : G) p * F).coeff g := by
  intro g
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  exact dvd_mul_right p (F.coeff g)

theorem scalar_division_iff (p : R) (F : AddMonoidAlgebra R G) :
    (∀ g, p ∣ F.coeff g) ↔
      ∃ F' : AddMonoidAlgebra R G, F = AddMonoidAlgebra.single (0 : G) p * F' := by
  constructor
  · exact scalar_division_exists p F
  · rintro ⟨F', rfl⟩
    exact scalar_division_coefficients p F'

end DivisionExists

section Cancellation

variable {R : Type uR} {G : Type uG} [CommRing R] [IsDomain R] [AddMonoid G]

/-- A scalar is cancellable because its action at each coefficient is
injective. No domain structure is asserted for the group algebra. -/
theorem scalar_mul_left_cancel (p : R) (hp : p ≠ 0)
    {F K : AddMonoidAlgebra R G}
    (h : AddMonoidAlgebra.single (0 : G) p * F =
      AddMonoidAlgebra.single (0 : G) p * K) : F = K := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  apply mul_left_cancel₀ hp
  simpa only [AddMonoidAlgebra.coeff_single_zero_mul] using
    congrArg (fun H : AddMonoidAlgebra R G => H.coeff g) h

theorem scalar_mul_left_injective (p : R) (hp : p ≠ 0) :
    Function.Injective
      (fun F : AddMonoidAlgebra R G => AddMonoidAlgebra.single (0 : G) p * F) :=
  fun _ _ h => scalar_mul_left_cancel p hp h

/-- The element obtained by coefficientwise division is unique. -/
theorem scalar_division_unique (p : R) (hp : p ≠ 0)
    {F F₁ F₂ : AddMonoidAlgebra R G}
    (h₁ : F = AddMonoidAlgebra.single (0 : G) p * F₁)
    (h₂ : F = AddMonoidAlgebra.single (0 : G) p * F₂) : F₁ = F₂ :=
  scalar_mul_left_cancel p hp (h₁.symm.trans h₂)

/-- Cancelling one regular scalar lowers the exponent of the norm equation
by exactly one. This is valid although the group algebra has zero divisors. -/
theorem scalar_mul_norm_division (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G)
    (h : (AddMonoidAlgebra.single (0 : G) p * F) * K =
      AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) :
    F * K = AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
  apply scalar_mul_left_cancel p hp
  calc
    AddMonoidAlgebra.single (0 : G) p * (F * K) =
        (AddMonoidAlgebra.single (0 : G) p * F) * K := (mul_assoc _ _ _).symm
    _ = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b) := h
    _ = AddMonoidAlgebra.single (0 : G) p *
        AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
      rw [pow_succ', mul_assoc]

end Cancellation

section Quotient

variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R] [IsDomain R]
  [AddMonoid G] [AddMonoid H]

/-- Project the norm equation along a genuine ring homomorphism and then
divide the chosen projected factor by one coefficient scalar. -/
theorem quotient_scalar_norm_division
    (q : AddMonoidAlgebra R G →+* AddMonoidAlgebra R H)
    (hscalar : ∀ r : R, q (AddMonoidAlgebra.single (0 : G) r) =
      AddMonoidAlgebra.single (0 : H) r)
    (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G) (F' : AddMonoidAlgebra R H)
    (hFK : F * K = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b))
    (hF : q F = AddMonoidAlgebra.single (0 : H) p * F') :
    F' * q K = AddMonoidAlgebra.single (0 : H) (p ^ e * b) := by
  apply scalar_mul_norm_division p hp e b F' (q K)
  calc
    (AddMonoidAlgebra.single (0 : H) p * F') * q K = q F * q K := by rw [hF]
    _ = q (F * K) := (q.map_mul F K).symm
    _ = q (AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) := congrArg q hFK
    _ = AddMonoidAlgebra.single (0 : H) (p ^ (e + 1) * b) := hscalar _

end Quotient

end CirculantHadamard

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.LocalComparisonInduction
section
namespace OAI

universe uA uS

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing

variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

/-- If the product has exactly one prime factor up to a unit, at least one
factor is a unit. This elementary base step does not use a valuation. -/
theorem isUnit_or_isUnit_of_mul_prime_unit {p x y : A} (hp : Prime p)
    (b : Aˣ) (hxy : x * y = p * (b : A)) : IsUnit x ∨ IsUnit y := by
  have hdvd : p ∣ x * y := ⟨(b : A), hxy⟩
  rcases hp.dvd_or_dvd hdvd with hx | hy
  · obtain ⟨z, hz⟩ := hx
    have hzy : z * y = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (z * y) = (p * z) * y := (mul_assoc _ _ _).symm
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inr (isUnit_of_mul_isUnit_right (hzy.symm ▸ b.isUnit))
  · obtain ⟨z, hz⟩ := hy
    have hxz : x * z = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (x * z) = x * (p * z) := by ac_rfl
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inl (isUnit_of_mul_isUnit_left (hxz.symm ▸ b.isUnit))

/-- Both augmentations in the comparison theorem are nonzero. -/
theorem augmentation_ne_zero_of_scalar_product {p : ℕ} {e : ℕ}
    (hp : (p : A) ≠ 0) (b : Aˣ) (F K : Elem A (p ^ e))
    (hFK : F * K = scalar (p ^ e) ((p : A) ^ e * (b : A))) :
    augmentation (p ^ e) F ≠ 0 ∧ augmentation (p ^ e) K ≠ 0 := by
  have haug : augmentation (p ^ e) F * augmentation (p ^ e) K =
      (p : A) ^ e * (b : A) := by
    simpa only [map_mul, augmentation_scalar] using
      congrArg (augmentation (p ^ e)) hFK
  have hne : augmentation (p ^ e) F * augmentation (p ^ e) K ≠ 0 := by
    rw [haug]
    exact mul_ne_zero (pow_ne_zero _ hp) b.ne_zero
  exact mul_ne_zero_iff.mp hne

/-- The exponent-one base case, using the actual residue field of `S`. -/
theorem comparison_base (n p : ℕ) (φ : A →+* S) (hp : Prime (p : A))
    (hpS : φ (p : A) ≠ 0)
    (v : Elem A n →+* S)
    (vscalar : ∀ a : A, v (scalar n a) = φ a)
    (vres : ∀ F : Elem A n,
      IsLocalRing.residue S (v F) =
        IsLocalRing.residue S (φ (augmentation n F)))
    (b : Aˣ) (F K : Elem A n)
    (hFK : F * K = scalar n ((p : A) * (b : A))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v F) (φ (augmentation n F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v K) (φ (augmentation n K)) := by
  have haug : augmentation n F * augmentation n K = (p : A) * (b : A) := by
    simpa only [map_mul, augmentation_scalar] using congrArg (augmentation n) hFK
  have hv : v F * v K = φ ((p : A) * (b : A)) := by
    simpa only [map_mul, vscalar] using congrArg v hFK
  have hprod : v F * v K = φ (augmentation n F) * φ (augmentation n K) := by
    calc
      v F * v K = φ ((p : A) * (b : A)) := hv
      _ = φ (augmentation n F * augmentation n K) := congrArg φ haug.symm
      _ = φ (augmentation n F) * φ (augmentation n K) := φ.map_mul _ _
  have hne : φ (augmentation n F) * φ (augmentation n K) ≠ 0 := by
    rw [← map_mul, haug, map_mul]
    exact mul_ne_zero hpS (b.isUnit.map φ).ne_zero
  rcases isUnit_or_isUnit_of_mul_prime_unit hp b haug with hF | hK
  · have h := residueOneAssociated_of_isUnit_residue_eq (hF.map φ) (vres F)
    exact ⟨h, h.product_complement hprod hne⟩
  · have h := residueOneAssociated_of_isUnit_residue_eq (hK.map φ) (vres K)
    have hprod' : v K * v F = φ (augmentation n K) * φ (augmentation n F) := by
      simpa only [mul_comm] using hprod
    have hne' : φ (augmentation n K) * φ (augmentation n F) ≠ 0 := by
      simpa only [mul_comm] using hne
    exact ⟨h.product_complement hprod' hne', h⟩

/-- Induction step when the first projected factor is divisible by `p`.
The other factor is left intact. The two output associations are both
transported, so the next step may divide either factor. -/
theorem comparison_step_left [IsDomain S] (p e : ℕ) (φ : A →+* S)
    (hp : (p : A) ≠ 0)
    (v : Elem A (p ^ (e + 1)) →+* S)
    (v' : Elem A (p ^ (e + 2)) →+* S)
    (vscalar : ∀ a : A, v (scalar (p ^ (e + 1)) a) = φ a)
    (vq : ∀ F : Elem A (p ^ (e + 2)),
      v (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v' F)
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)))
    (F' : Elem A (p ^ (e + 1)))
    (hF : cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F')
    (ih : ∀ U V : Elem A (p ^ (e + 1)),
      U * V = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
        ResidueOneAssociated (IsLocalRing.residue S) (v U)
          (φ (augmentation (p ^ (e + 1)) U)) ∧
        ResidueOneAssociated (IsLocalRing.residue S) (v V)
          (φ (augmentation (p ^ (e + 1)) V))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v' F)
      (φ (augmentation (p ^ (e + 2)) F)) ∧
    ResidueOneAssociated (IsLocalRing.residue S) (v' K)
      (φ (augmentation (p ^ (e + 2)) K)) := by
  let q := cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1)))
  have hdiv : F' * q K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) :=
    quotient_scalar_norm_division q (fun a => cyclicProjection_single_zero _ a)
      (p : A) hp (e + 1) (b : A) F K F' hFK hF
  obtain ⟨hiF, hiK⟩ := ih F' (q K) hdiv
  have heval : v' F = φ (p : A) * v F' := by
    rw [← vq F, hF, map_mul, vscalar]
  have haug : augmentation (p ^ (e + 2)) F =
      (p : A) * augmentation (p ^ (e + 1)) F' := by
    rw [← augmentation_cyclicProjection (pow_dvd_pow p (Nat.le_succ (e + 1))) F,
      hF, map_mul, augmentation_scalar]
  constructor
  · rw [heval, haug, map_mul]
    exact hiF.mul_left (φ (p : A))
  · simpa only [q, vq, augmentation_cyclicProjection] using hiK

/-- The integral induction with its projection-divisibility input exposed.
The concrete cyclotomic theorem discharges `hdivide`; it is not a definition
of the comparison conclusion. -/
theorem comparison_induction (p : ℕ) (φ : A →+* S)
    (hp : Prime (p : A)) (hpS : φ (p : A) ≠ 0)
    (v : (e : ℕ) → Elem A (p ^ (e + 1)) →+* S)
    (vscalar : ∀ e a, v e (scalar (p ^ (e + 1)) a) = φ a)
    (vres : ∀ F : Elem A (p ^ 1),
      IsLocalRing.residue S (v 0 F) =
        IsLocalRing.residue S (φ (augmentation (p ^ 1) F)))
    (vq : ∀ e F,
      v e (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v (e + 1) F)
    (hdivide : ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 2))),
      F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)) →
      (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
        scalar (p ^ (e + 1)) (p : A) * F') ∨
      (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
        scalar (p ^ (e + 1)) (p : A) * K')) :
    ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 1))),
      F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
      ResidueOneAssociated (IsLocalRing.residue S) (v e F)
        (φ (augmentation (p ^ (e + 1)) F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v e K)
        (φ (augmentation (p ^ (e + 1)) K)) := by
  intro e
  induction e with
  | zero =>
      intro b F K hFK
      exact comparison_base (p ^ (0 + 1)) p φ hp hpS (v 0) (vscalar 0) vres
        b F K (by simpa only [Nat.zero_add, pow_one] using hFK)
  | succ e ih =>
      intro b F K hFK
      rcases hdivide e b F K hFK with ⟨F', hF⟩ | ⟨K', hK⟩
      · exact comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b F K hFK F' hF (ih b)
      · have hKF : K * F = scalar (p ^ (e + 2))
            ((p : A) ^ (e + 2) * (b : A)) := by
          simpa only [mul_comm] using hFK
        exact (comparison_step_left p e φ hp.ne_zero (v e) (v (e + 1))
          (vscalar e) (vq e) b K F hKF K' hK (ih b)).symm

end CirculantHadamard.LocalComparison

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicProjectionPolynomial
section
namespace OAI

universe uR

/-! Polynomial evaluation commutes with the concrete cyclic quotient map. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [CommRing R] {m n : ℕ}

/-- The cyclic quotient also preserves the coefficient algebra structure. -/
def cyclicProjectionAlgHom (h : m ∣ n) : Elem R n →ₐ[R] Elem R m :=
  { cyclicProjection R h with
    commutes' := fun r => cyclicProjection_scalar h r }

@[simp] theorem cyclicProjectionAlgHom_apply (h : m ∣ n) (F : Elem R n) :
    cyclicProjectionAlgHom R h F = cyclicProjection R h F := rfl

/-- Polynomial evaluation at the generator commutes with the cyclic quotient. -/
theorem cyclicProjection_aeval (h : m ∣ n) (F : Polynomial R) :
    cyclicProjection R h (Polynomial.aeval (CyclicPolynomial.generator R n) F) =
      Polynomial.aeval (CyclicPolynomial.generator R m) F := by
  change cyclicProjectionAlgHom R h
    (Polynomial.aeval (CyclicPolynomial.generator R n) F) = _
  have hgen : cyclicProjectionAlgHom R h (CyclicPolynomial.generator R n) =
      CyclicPolynomial.generator R m := cyclicProjection_generator (R := R) h
  rw [← Polynomial.aeval_algHom_apply, hgen]

end CirculantHadamard

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluationAt
section
namespace OAI

universe uA uS uT


noncomputable section

namespace CirculantHadamard.CyclicRing

open Polynomial
open scoped BigOperators

variable {A : Type uA} {S : Type uS} {T : Type uT} [CommRing A] [CommRing S] [CommRing T]
variable [Algebra A S] [Algebra A T]

/-- Evaluate the polynomial quotient at a proved `n`th root of unity. -/
def evaluateAt (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) : Elem A n →ₐ[A] S :=
  (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx])).comp
      (CyclicPolynomial.cyclicEquiv A n).toAlgHom

@[simp] theorem evaluateAt_single (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (a : ZMod n) (r : A) :
    evaluateAt n x hx (AddMonoidAlgebra.single a r) = algebraMap A S r * x ^ a.val := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (AddMonoidAlgebra.single a r)) = _
  rw [CyclicPolynomial.cyclicEquiv_single, map_mul, map_pow, AlgHom.commutes,
    AdjoinRoot.liftAlgHom_root (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
      (by simp [CyclicPolynomial.relation, hx])]

@[simp] theorem evaluateAt_scalar (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (r : A) : evaluateAt n x hx (scalar n r) = algebraMap A S r := by
  simp [scalar]

@[simp] theorem evaluateAt_generator (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) :
    evaluateAt (A := A) n x hx (CyclicPolynomial.generator A n) = x := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (CyclicPolynomial.generator A n)) = x
  rw [CyclicPolynomial.cyclicEquiv_generator]
  exact AdjoinRoot.liftAlgHom_root (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx])

/-- Evaluation agrees with evaluation of every polynomial in the cyclic generator. -/
@[simp] theorem evaluateAt_aeval (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (p : A[X]) :
    evaluateAt n x hx (aeval (CyclicPolynomial.generator A n) p) = aeval x p := by
  change (AdjoinRoot.liftAlgHom (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]))
      (CyclicPolynomial.cyclicEquiv A n (aeval (CyclicPolynomial.generator A n) p)) = _
  rw [CyclicPolynomial.cyclicEquiv_aeval]
  exact AdjoinRoot.liftAlgHom_mk (CyclicPolynomial.relation A n) (Algebra.ofId A S) x
    (by simp [CyclicPolynomial.relation, hx]) p

/-- The quotient construction and the finite-character construction are the same
ring homomorphism. -/
theorem evaluateAt_eq_evaluate (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1) :
    (evaluateAt (A := A) n x hx).toRingHom =
      evaluate (algebraMap A S) (CyclicPolynomial.powerCharacter n x hx) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp [evaluateAt_single]
  · intro a
    simp [evaluateAt_single, CyclicPolynomial.powerCharacter_apply]

theorem evaluateAt_apply (n : ℕ) [NeZero n] (x : S) (hx : x ^ n = 1)
    (f : Elem A n) :
    evaluateAt n x hx f = ∑ a : ZMod n, algebraMap A S (f.coeff a) * x ^ a.val := by
  change (evaluateAt n x hx).toRingHom f = _
  rw [evaluateAt_eq_evaluate, evaluate_apply]
  rfl

/-- Evaluation at one is the actual augmentation followed by the coefficient map. -/
@[simp] theorem evaluateAt_one (n : ℕ) [NeZero n] (f : Elem A n) :
    evaluateAt n (1 : S) (one_pow n) f = algebraMap A S (augmentation n f) := by
  simp [evaluateAt_apply, augmentation_apply, map_sum]

/-- Naturality under an algebra homomorphism that sends the chosen root to the
chosen target root.  Both root equations remain explicit proved hypotheses. -/
theorem map_evaluateAt_hom (n : ℕ) [NeZero n]
    (x : S) (hx : x ^ n = 1) (y : T) (hy : y ^ n = 1)
    (ψ : S →ₐ[A] T) (hxy : ψ x = y) :
    ψ.comp (evaluateAt n x hx) = evaluateAt n y hy := by
  apply AddMonoidAlgebra.algHom_ext
  · intro a
    simp [AlgHom.comp_apply, evaluateAt_single, hxy]
  · exact Subsingleton.elim _ _

theorem map_evaluateAt (n : ℕ) [NeZero n]
    (x : S) (hx : x ^ n = 1) (y : T) (hy : y ^ n = 1)
    (ψ : S →ₐ[A] T) (hxy : ψ x = y) (f : Elem A n) :
    ψ (evaluateAt n x hx f) = evaluateAt n y hy f :=
  DFunLike.congr_fun (map_evaluateAt_hom n x hx y hy ψ hxy) f

/-- In particular, a residue map sending the root to one sends evaluation to
the residue of augmentation. -/
theorem map_evaluateAt_of_map_eq_one (n : ℕ) [NeZero n]
    (x : S) (hx : x ^ n = 1) (ψ : S →ₐ[A] T) (hx1 : ψ x = 1) (f : Elem A n) :
    ψ (evaluateAt n x hx f) = algebraMap A T (augmentation n f) := by
  rw [map_evaluateAt n x hx 1 (one_pow n) ψ hx1, evaluateAt_one]

end CirculantHadamard.CyclicRing

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicRemainder
section
namespace OAI

universe uR uS


noncomputable section

namespace CirculantHadamard.CyclotomicRemainder

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S] {f : R[X]}

/-- Scalar divisibility in a monic root extension gives a constant-polynomial
factor of the canonical remainder. -/
theorem C_dvd_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) :
    C a ∣ F %ₘ f := by
  obtain ⟨x, hx⟩ := hdiv
  refine ⟨h.modByMonicHom x, ?_⟩
  calc
    F %ₘ f = h.modByMonicHom (h.map F) := (h.modByMonicHom_map F).symm
    _ = h.modByMonicHom (a • x) := by rw [hx, Algebra.smul_def]
    _ = a • h.modByMonicHom x := h.modByMonicHom.map_smul a x
    _ = C a * h.modByMonicHom x := Polynomial.smul_eq_C_mul a

/-- A constant factor of the canonical remainder gives scalar divisibility
after passing to the monic root extension. -/
theorem dvd_map_of_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : C a ∣ F %ₘ f) :
    algebraMap R S a ∣ h.map F := by
  obtain ⟨G, hG⟩ := hdiv
  refine ⟨h.map G, ?_⟩
  calc
    h.map F = h.map (F %ₘ f) := (h.map_modByMonic F).symm
    _ = h.map (C a * G) := congrArg h.map hG
    _ = algebraMap R S a * h.map G := by rw [map_mul, ← h.algebraMap_apply]

/-- Exact divisibility equivalence for a monic root extension. -/
theorem map_dvd_iff_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ C a ∣ F %ₘ f :=
  ⟨C_dvd_modByMonic_of_dvd_map h a F, dvd_map_of_C_dvd_modByMonic h a F⟩

/-- Scalar divisibility is equivalent to divisibility of every coefficient
of the canonical remainder. -/
theorem map_dvd_iff_dvd_coeff_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ ∀ i, a ∣ (F %ₘ f).coeff i :=
  (map_dvd_iff_C_dvd_modByMonic h a F).trans (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Coefficient form of the forward divisibility bridge. -/
theorem dvd_coeff_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (map_dvd_iff_dvd_coeff_modByMonic h a F).mp hdiv i

/-- The actual quotient by a monic polynomial satisfies the constant-factor
criterion, using its concrete `IsAdjoinRootMonic` constructor. -/
theorem adjoinRoot_dvd_iff_C_dvd_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔ C a ∣ F %ₘ f := by
  simpa only [AdjoinRoot.isAdjoinRootMonic_toAdjoinRoot,
    AdjoinRoot.isAdjoinRoot_map_eq_mkₐ, AdjoinRoot.coe_mkₐ] using
    map_dvd_iff_C_dvd_modByMonic (AdjoinRoot.isAdjoinRootMonic f hf) a F

/-- The concrete monic quotient has scalar divisibility exactly when all
coefficients of the monic remainder have that scalar factor. -/
theorem adjoinRoot_dvd_iff_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔
      ∀ i, a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_C_dvd_modByMonic f hf a F).trans
    (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Scalar divisibility in a monic quotient implies coefficientwise
divisibility of the remainder. -/
theorem adjoinRoot_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X])
    (hdiv : algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_dvd_coeff_modByMonic f hf a F).mp hdiv i

end CirculantHadamard.CyclotomicRemainder

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicProjection
section
namespace OAI

universe uR uS


noncomputable section

namespace CirculantHadamard

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- Every actual cyclic group-ring element has a polynomial representative. -/
theorem exists_cyclic_polynomial (n : ℕ) [NeZero n]
    (F : AddMonoidAlgebra R (ZMod n)) :
    ∃ P : R[X], aeval (CyclicPolynomial.generator R n) P = F := by
  obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective (CyclicPolynomial.cyclicEquiv R n F)
  refine ⟨P, ?_⟩
  apply (CyclicPolynomial.cyclicEquiv R n).injective
  rw [CyclicPolynomial.cyclicEquiv_aeval, hP]

/-- The actual root in the cyclotomic quotient satisfies its `n`th-power
relation, directly because the cyclotomic polynomial divides `X ^ n - 1`. -/
theorem cyclotomicAdjoinRoot_pow (n : ℕ) :
    AdjoinRoot.root (cyclotomic n R) ^ n = 1 := by
  have h : AdjoinRoot.mk (cyclotomic n R) ((X : R[X]) ^ n - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one n R)
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] using h

/-- Evaluation of the actual cyclic group ring at the root in its cyclotomic
quotient, using the root's proved power relation. -/
def cyclicCyclotomicEvaluation (R : Type uR) [CommRing R] (n : ℕ) [NeZero n] :
    AddMonoidAlgebra R (ZMod n) →ₐ[R] AdjoinRoot (cyclotomic n R) :=
  CyclicRing.evaluateAt n (AdjoinRoot.root (cyclotomic n R))
    (cyclotomicAdjoinRoot_pow n)

@[simp]
theorem cyclicCyclotomicEvaluation_aeval (n : ℕ) [NeZero n] (P : R[X]) :
    cyclicCyclotomicEvaluation R n (aeval (CyclicPolynomial.generator R n) P) =
      AdjoinRoot.mk (cyclotomic n R) P := by
  rw [cyclicCyclotomicEvaluation, CyclicRing.evaluateAt_aeval, AdjoinRoot.aeval_eq]

/-- A prime-power cyclotomic polynomial becomes `p` at every element whose
`p ^ e`th power is one. -/
theorem aeval_cyclotomic_prime_pow_of_pow_eq_one {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) :
    aeval x (cyclotomic (p ^ (e + 1)) R) = (p : S) := by
  rw [cyclotomic_prime_pow_eq_geom_sum hp]
  simp [hx]

/-- Evaluating a monic division identity preserves integral divisibility if
both the divisor's evaluation and the remainder have the stated scalar factor. -/
theorem aeval_divisible_of_modByMonic_coeff (x : S) (F Q : R[X]) (a : R)
    (_hQ : Q.Monic) (hQx : aeval x Q = algebraMap R S a)
    (hcoeff : ∀ i, a ∣ (F %ₘ Q).coeff i) :
    ∃ G : S, aeval x F = algebraMap R S a * G := by
  obtain ⟨T, hT⟩ := (C_dvd_iff_dvd_coeff a (F %ₘ Q)).2 hcoeff
  refine ⟨aeval x T + aeval x (F /ₘ Q), ?_⟩
  calc
    aeval x F = aeval x (F %ₘ Q) + aeval x Q * aeval x (F /ₘ Q) := by
      rw [← map_mul, ← map_add, modByMonic_add_div F Q]
    _ = algebraMap R S a * (aeval x T + aeval x (F /ₘ Q)) := by
      rw [hT, map_mul, aeval_C, hQx, mul_add]

/-- Integral divisibility at a `p ^ e`th root follows from coefficientwise
divisibility of the remainder modulo the next cyclotomic polynomial. -/
theorem aeval_divisible_of_cyclotomic_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : S, aeval x F = (p : S) * G := by
  have hQx : aeval x (cyclotomic (p ^ (e + 1)) R) =
      algebraMap R S (p : R) := by
    simpa only [map_natCast] using aeval_cyclotomic_prime_pow_of_pow_eq_one hp x hx
  simpa only [map_natCast] using aeval_divisible_of_modByMonic_coeff x F
    (cyclotomic (p ^ (e + 1)) R) (p : R) (cyclotomic.monic _ _) hQx hcoeff

/-- The concrete `p`-division step in the cyclic group algebra: project from
order `p ^ (e + 1)` to order `p ^ e`, then divide integrally by `p`. -/
theorem cyclicProjection_divisible_of_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e))
          (aeval (CyclicPolynomial.generator R (p ^ (e + 1))) F) =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  rw [cyclicProjection_aeval]
  exact aeval_divisible_of_cyclotomic_remainder_coeff hp
    (CyclicPolynomial.generator R (p ^ e)) (CyclicPolynomial.generator_pow R (p ^ e))
    F hcoeff

/-- Divisibility at the actual primitive-root quotient forces integral
divisibility after projecting the actual cyclic group-ring element.

The concrete monic quotient's linear remainder map supplies coefficientwise
divisibility of the remainder. -/
theorem cyclicProjection_divisible_of_cyclotomicEvaluation {p e : ℕ}
    [NeZero p] (hp : p.Prime) (F : AddMonoidAlgebra R (ZMod (p ^ (e + 1))))
    (hdiv : (p : AdjoinRoot (cyclotomic (p ^ (e + 1)) R)) ∣
      cyclicCyclotomicEvaluation R (p ^ (e + 1)) F) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e)) F =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  obtain ⟨P, rfl⟩ := exists_cyclic_polynomial (p ^ (e + 1)) F
  rw [cyclicCyclotomicEvaluation_aeval] at hdiv
  apply cyclicProjection_divisible_of_remainder_coeff hp P
  intro i
  exact CyclotomicRemainder.adjoinRoot_dvd_coeff_modByMonic
    (cyclotomic (p ^ (e + 1)) R) (cyclotomic.monic _ _) (p : R) P
    (by simpa only [map_natCast] using hdiv) i

end CirculantHadamard

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicFactorDivision
section
namespace OAI

universe uA


noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial IsDiscreteValuationRing

variable {A : Type uA} [CommRing A]

/-- The ramified DVR and its value of `p` imply the concrete choice of a
divisible projected factor. These are local-ring properties, independent of
the input factors. The scalar and group exponents are both `e + 2`. -/
theorem projected_factor_divisible {p e D : ℕ} [NeZero p] (hp : p.Prime)
    [IsDomain (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    [IsDiscreteValuationRing (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    (hpS : (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ≠ 0)
    (hD : 0 < D)
    (hpval : addVal (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) = (D : ℕ∞))
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A))) :
    (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F') ∨
    (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
      scalar (p ^ (e + 1)) (p : A) * K') := by
  let v := cyclicCyclotomicEvaluation A (p ^ (e + 2))
  have hscalar : ∀ a : A, v (scalar (p ^ (e + 2)) a) =
      algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) a := by
    intro a
    exact v.commutes a
  have hv : v F * v K =
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ^ (e + 2) *
        algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) (b : A) := by
    have h := congrArg v hFK
    simpa only [map_mul, hscalar, map_pow, map_natCast] using h
  have hb : IsUnit (algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (b : A)) := b.isUnit.map _
  have hchoose := LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit
    hpS hD hpval (Nat.le_add_left 2 e) hb hv
  rcases hchoose with hF | hK
  · left
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp F hF
  · right
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp K hK

end CirculantHadamard.LocalComparison

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluationProjection
section
namespace OAI

universe uR uS

/-! Evaluation at a root of smaller order factors through the cyclic quotient. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable {m n : ℕ} [NeZero m] [NeZero n]

/-- The actual root evaluation is unchanged after reducing the cyclic index.
Both root equations are stated explicitly to match the two evaluation maps. -/
theorem evaluateAt_cyclicProjection (h : m ∣ n)
    (x : S) (hm : x ^ m = 1) (hn : x ^ n = 1) (F : Elem R n) :
    evaluateAt m x hm (cyclicProjection R h F) = evaluateAt n x hn F := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change evaluateAt m x hm (cyclicProjection R h ((F : Elem R n) + G)) =
      evaluateAt n x hn ((F : Elem R n) + G)
    simp only [map_add, hF, hG]
  · intro a r
    simp only [cyclicProjection_single, evaluateAt_single]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [← pow_eq_pow_mod _ hm]

end CirculantHadamard

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.RamifiedEisenstein
section
namespace OAI

universe uA uB


noncomputable section

namespace CirculantHadamard.RamifiedEisenstein

open Polynomial

/-- The prime-power cyclotomic polynomial translated to put the root at `ξ - 1`. -/
def shifted (A : Type uA) [CommRing A] (p k : ℕ) : A[X] :=
  (cyclotomic (p ^ (k + 1)) A).comp (X + 1)

theorem shifted_monic (A : Type uA) [CommRing A] (p k : ℕ) :
    (shifted A p k).Monic := by
  simpa only [shifted, C_1] using
    (cyclotomic.monic (p ^ (k + 1)) A).comp_X_add_C (1 : A)

theorem shifted_natDegree (A : Type uA) [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).natDegree = (p - 1) * p ^ k := by
  rw [shifted, natDegree_comp, show (X + 1 : A[X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one, natDegree_cyclotomic,
    Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem cyclotomic_natDegree (A : Type uA) [CommRing A] [Nontrivial A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (cyclotomic (p ^ (k + 1)) A).natDegree = (p - 1) * p ^ k := by
  rw [natDegree_cyclotomic, Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem shifted_coeff_zero (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).coeff 0 = (p : A) := by
  rw [shifted, coeff_zero_eq_eval_zero, eval_comp,
    cyclotomic_prime_pow_eq_geom_sum hp, eval_add, eval_X, eval_one, zero_add,
    eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range,
    Nat.smul_one_eq_cast]

theorem shifted_isWeaklyEisensteinAt (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).IsWeaklyEisensteinAt (Ideal.span {(p : A)}) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k).isWeaklyEisensteinAt.map
    (Int.castRingHom A)
  simpa [shifted, Ideal.submodule_span_eq, Ideal.map_span, Polynomial.map_comp] using h

section Local

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A] [IsLocalRing A]
  {p : ℕ}

theorem shifted_isEisensteinAt (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    (shifted A p k).IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpu : ¬ IsUnit (p : A) :=
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (p : A) hp0 hmax).not_isUnit
  apply (shifted_monic A p k).isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top inferInstance)
  · intro i hi
    rw [hmax]
    exact (shifted_isWeaklyEisensteinAt A hp k).mem hi
  · rw [shifted_coeff_zero A hp k, hmax, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro h
    have h21 : (2 : ℕ) ≤ 1 := (pow_dvd_pow_iff hp0 hpu).mp (by simpa using h)
    exact (by decide : ¬ (2 : ℕ) ≤ 1) h21

theorem shifted_irreducible (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : Irreducible (shifted A p k) := by
  apply (shifted_isEisensteinAt A hp k hmax).irreducible inferInstance
    (shifted_monic A p k).isPrimitive
  rw [shifted_natDegree A hp k]
  exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)

theorem cyclotomic_irreducible (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : Irreducible (cyclotomic (p ^ (k + 1)) A) := by
  apply (MulEquiv.irreducible_iff (Polynomial.algEquivAevalXAddC (1 : A))).mp
  change Irreducible ((cyclotomic (p ^ (k + 1)) A).comp (X + C (1 : A)))
  simpa only [shifted, C_1] using shifted_irreducible A hp k hmax

/-- Modulo the maximal ideal, the translated polynomial is exactly a pure power. -/
theorem mod_maximal_shifted (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    (shifted A p k).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) =
      (X : (A ⧸ IsLocalRing.maximalIdeal A)[X]) ^ ((p - 1) * p ^ k) := by
  ext i
  rw [coeff_map, coeff_X_pow]
  by_cases hi : i = (p - 1) * p ^ k
  · subst i
    rw [if_pos rfl, ← shifted_natDegree A hp k,
      (shifted_monic A p k).coeff_natDegree, map_one]
  · rw [if_neg hi]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (shifted_isEisensteinAt A hp k hmax).coeff_mem
    simpa only [shifted_natDegree A hp k] using hi

end Local

section DVR

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ}

theorem cyclotomic_prime (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : Prime (cyclotomic (p ^ (k + 1)) A) :=
  irreducible_iff_prime.mp (cyclotomic_irreducible A hp k hmax)

theorem cyclotomic_adjoinRoot_isDomain (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    IsDomain (AdjoinRoot (cyclotomic (p ^ (k + 1)) A)) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic_prime A hp k hmax)

/-- The minimal polynomial equality is for the actual primitive root in a
faithful domain extension, not merely for the formal quotient root. -/
theorem cyclotomic_eq_minpoly (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) {B : Type uB} [CommRing B] [IsDomain B]
    [Algebra A B] [NoZeroSMulDivisors A B] {ξ : B}
    (hξ : IsPrimitiveRoot ξ (p ^ (k + 1))) :
    cyclotomic (p ^ (k + 1)) A = minpoly A ξ := by
  have hroot : aeval ξ (cyclotomic (p ^ (k + 1)) A) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def]
    exact hξ.isRoot_cyclotomic (pow_pos hp.pos (k + 1))
  have hi : IsIntegral A ξ := ⟨_, cyclotomic.monic _ A, hroot⟩
  have hd : minpoly A ξ ∣ cyclotomic (p ^ (k + 1)) A :=
    minpoly.isIntegrallyClosed_dvd hi hroot
  exact Polynomial.eq_of_monic_of_associated (cyclotomic.monic _ A) (minpoly.monic hi)
    ((minpoly.irreducible hi).associated_of_dvd
      (cyclotomic_irreducible A hp k hmax) hd).symm

end DVR

end CirculantHadamard.RamifiedEisenstein

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.RamifiedUnit
section
namespace OAI

universe uR uS


noncomputable section

namespace CirculantHadamard.RamifiedUnit

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [IsDomain R]

/-- The polynomial form of the unit factor in an Eisenstein relation. -/
theorem exists_polynomial_unit_factor (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by
  have hdvd : C a ∣ f.eraseLead := by
    apply (C_dvd_iff_dvd_coeff _ _).2
    intro i
    by_cases hi : i = f.natDegree
    · simp [eraseLead_coeff, hi]
    · rw [eraseLead_coeff_of_ne _ hi]
      by_cases hilt : i < f.natDegree
      · exact hcoeff i hilt
      · rw [coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_ne (Nat.le_of_not_gt hilt) (Ne.symm hi))]
        exact dvd_zero a
  obtain ⟨q, hq⟩ := hdvd
  have hqzero : q.coeff 0 = 1 := by
    apply mul_left_cancel₀ ha
    have hh := congrArg (fun g : R[X] => g.coeff 0) hq
    simpa [eraseLead_coeff_of_ne _ (Nat.ne_of_lt hdeg), hzero] using hh.symm
  have hqrepr : 1 + X * q.divX = q := by
    simpa [hqzero, add_comm] using X_mul_divX_add q
  refine ⟨q.divX, ?_⟩
  calc
    f = f.eraseLead + X ^ f.natDegree := by
      simpa [hf] using (eraseLead_add_C_mul_X_pow f).symm
    _ = X ^ f.natDegree + C a * (1 + X * q.divX) := by
      rw [hq, hqrepr]
      exact add_comm _ _

variable [CommRing S] [Algebra R S] [IsLocalRing S]

/-- A root in the maximal ideal turns the normalized polynomial factor into
a unit, and therefore expresses the constant coefficient as a unit times
the ramified power. -/
theorem exists_unit_mul_root_pow (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by
  obtain ⟨q, hq⟩ := exists_polynomial_unit_factor f a ha hf hdeg hzero hcoeff
  have hrel : z ^ f.natDegree + algebraMap R S a * (1 + z * aeval z q) = 0 := by
    rw [hq] at hroot
    simpa only [map_add, map_mul, map_pow, aeval_X, map_one, aeval_C] using hroot
  have hn : -(z * aeval z q) ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.maximalIdeal S).neg_mem
      ((IsLocalRing.maximalIdeal S).mul_mem_right _ hz)
  have hu : IsUnit (1 + z * aeval z q) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(z * aeval z q)) hn
  obtain ⟨v, hv⟩ := hu
  have hpow : z ^ f.natDegree = -(algebraMap R S a * (v : S)) := by
    rw [← hv] at hrel
    exact eq_neg_of_add_eq_zero_left hrel
  refine ⟨-v⁻¹, ?_⟩
  rw [Units.val_neg, hpow, neg_mul_neg]
  calc
    algebraMap R S a = algebraMap R S a * ((v : S) * ↑v⁻¹) := by simp
    _ = ↑v⁻¹ * (algebraMap R S a * (v : S)) := by ac_rfl

end CirculantHadamard.RamifiedUnit

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.RamifiedLocal
section
namespace OAI

universe uA


noncomputable section

namespace CirculantHadamard.RamifiedLocal

open Polynomial

/-- The genuine monic cyclotomic quotient, with no additional ring-data premise. -/
abbrev Extension (A : Type uA) [CommRing A] (p k : ℕ) :=
  AdjoinRoot (cyclotomic (p ^ (k + 1)) A)

/-- The actual ramified parameter in the cyclotomic quotient. -/
def uniformizer (A : Type uA) [CommRing A] (p k : ℕ) : Extension A p k :=
  AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A) - 1

instance extensionFinite (A : Type uA) [CommRing A] (p k : ℕ) :
    Module.Finite A (Extension A p k) :=
  (cyclotomic.monic (p ^ (k + 1)) A).finite_adjoinRoot

theorem uniformizer_aeval_shifted (A : Type uA) [CommRing A] (p k : ℕ) :
    aeval (uniformizer A p k) (RamifiedEisenstein.shifted A p k) = 0 := by
  simp only [RamifiedEisenstein.shifted, aeval_comp, map_add, aeval_X, map_one,
    uniformizer, sub_add_cancel, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- Every element is a scalar modulo the actual root-minus-one parameter. -/
theorem exists_scalar_add_uniformizer_mul (A : Type uA) [CommRing A] (p k : ℕ)
    (x : Extension A p k) :
    ∃ a : A, ∃ b : Extension A p k,
      x = algebraMap A (Extension A p k) a + uniformizer A p k * b := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  have hroot : (q.map (algebraMap A (Extension A p k))).eval
      (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) =
      AdjoinRoot.mk (cyclotomic (p ^ (k + 1)) A) q := by
    rw [eval_map, ← aeval_def, AdjoinRoot.aeval_eq]
  have hone : (q.map (algebraMap A (Extension A p k))).eval 1 =
      algebraMap A (Extension A p k) (q.eval 1) := by
    rw [eval_map, eval₂_at_one]
  have hdiv := sub_dvd_eval_sub
    (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) (1 : Extension A p k)
    (q.map (algebraMap A (Extension A p k)))
  rw [hroot, hone] at hdiv
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨q.eval 1, b, ?_⟩
  change _ = _ + (AdjoinRoot.root _ - 1) * b
  rw [← hb]
  simp

theorem prime_mem_span_uniformizer (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p : Extension A p k) ∈ Ideal.span {uniformizer A p k} := by
  let : Fact p.Prime := ⟨hp⟩
  have hdiv := sub_dvd_eval_sub
    (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) (1 : Extension A p k)
    ((cyclotomic (p ^ (k + 1)) A).map (algebraMap A (Extension A p k)))
  have hdiv' : uniformizer A p k ∣ -(p : Extension A p k) := by
    simpa only [uniformizer, eval_map, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, eval₂_one_cyclotomic_prime_pow, zero_sub] using hdiv
  exact (Ideal.neg_mem_iff (Ideal.span {uniformizer A p k})).mp
    (Ideal.mem_span_singleton.mpr hdiv')

section LocalBase

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ}

theorem isDomain (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : IsDomain (Extension A p k) :=
  RamifiedEisenstein.cyclotomic_adjoinRoot_isDomain A hp k hmax

/-- Every maximal ideal of the genuine quotient is the same principal ideal. -/
theorem maximal_eq_span_uniformizer (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) (M : Ideal (Extension A p k)) [M.IsMaximal] :
    M = Ideal.span {uniformizer A p k} := by
  have hcomap : M.comap (algebraMap A (Extension A p k)) = Ideal.span {(p : A)} :=
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) M)).trans hmax
  have hmap : (Ideal.span {(p : A)}).map (algebraMap A (Extension A p k)) ≤ M := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [hcomap]
  have hpow := Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
      (RamifiedEisenstein.shifted_isWeaklyEisensteinAt A hp k)
      (uniformizer_aeval_shifted A p k) (RamifiedEisenstein.shifted_monic A p k)
      _ (le_refl _)
  have hpi : uniformizer A p k ∈ M :=
    (inferInstance : M.IsPrime).mem_of_pow_mem _ (hmap hpow)
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, hxform⟩ := exists_scalar_add_uniformizer_mul A p k x
    have haM : algebraMap A (Extension A p k) a ∈ M := by
      have hh := M.sub_mem hx (Ideal.mul_mem_right b M hpi)
      simpa [hxform] using hh
    have ha : a ∈ Ideal.span {(p : A)} := by
      rw [← hcomap]
      exact haM
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    have hap : algebraMap A (Extension A p k) a ∈
        Ideal.span {uniformizer A p k} := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ (prime_mem_span_uniformizer A hp k)
    rw [hxform]
    exact (Ideal.span {uniformizer A p k}).add_mem hap
      (Ideal.mul_mem_right b _ (Ideal.subset_span (Set.mem_singleton _)))
  · exact (Ideal.span_singleton_le_iff_mem M).mpr hpi

theorem isLocalRing (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) : IsLocalRing (Extension A p k) := by
  let : IsDomain (Extension A p k) := isDomain A hp k hmax
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Extension A p k)
  let : M.IsMaximal := hM
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M, hM, ?_⟩
  intro N hN
  let : N.IsMaximal := hN
  exact (maximal_eq_span_uniformizer A hp k hmax N).trans
    (maximal_eq_span_uniformizer A hp k hmax M).symm

theorem maximalIdeal_eq_span (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] :
    IsLocalRing.maximalIdeal (Extension A p k) = Ideal.span {uniformizer A p k} :=
  maximal_eq_span_uniformizer A hp k hmax _

theorem root_residue_eq_one (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Extension A p k))
      (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Extension A p k))),
    ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change uniformizer A p k ∈ IsLocalRing.maximalIdeal (Extension A p k)
  rw [maximalIdeal_eq_span A hp k hmax]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem exists_unit_mul_uniformizer_pow (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] :
    ∃ u : (Extension A p k)ˣ,
      (p : Extension A p k) = (u : Extension A p k) *
        uniformizer A p k ^ ((p - 1) * p ^ k) := by
  have hd : 0 < (RamifiedEisenstein.shifted A p k).natDegree := by
    rw [RamifiedEisenstein.shifted_natDegree A hp k]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)
  have hcoeff : ∀ i < (RamifiedEisenstein.shifted A p k).natDegree,
      (p : A) ∣ (RamifiedEisenstein.shifted A p k).coeff i := by
    intro i hi
    exact Ideal.mem_span_singleton.mp
      ((RamifiedEisenstein.shifted_isWeaklyEisensteinAt A hp k).mem hi)
  have hpi : uniformizer A p k ∈ IsLocalRing.maximalIdeal (Extension A p k) := by
    rw [maximalIdeal_eq_span A hp k hmax]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨u, hu⟩ := RamifiedUnit.exists_unit_mul_root_pow
    (RamifiedEisenstein.shifted A p k) (p : A) (Nat.cast_ne_zero.mpr hp.ne_zero)
    (RamifiedEisenstein.shifted_monic A p k) hd
    (RamifiedEisenstein.shifted_coeff_zero A hp k) hcoeff
    (uniformizer A p k) hpi (uniformizer_aeval_shifted A p k)
  exact ⟨u, by simpa only [map_natCast, RamifiedEisenstein.shifted_natDegree A hp k] using hu⟩

theorem algebraMap_injective (hp : p.Prime) (k : ℕ) [IsLocalRing (Extension A p k)] : Function.Injective (algebraMap A (Extension A p k)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  apply Polynomial.degree_ne_of_natDegree_ne
  rw [RamifiedEisenstein.cyclotomic_natDegree A hp k]
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))

theorem charZero (hp : p.Prime) (k : ℕ) [IsLocalRing (Extension A p k)] : CharZero (Extension A p k) where
  cast_injective m n h :=
    Nat.cast_injective (algebraMap_injective A hp k (by simpa only [map_natCast] using h))

theorem uniformizer_ne_zero (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] : uniformizer A p k ≠ 0 := by
  intro hzero
  have hpS : (p : Extension A p k) ≠ 0 := by
    intro hpzero
    have : algebraMap A (Extension A p k) (p : A) =
        algebraMap A (Extension A p k) 0 := by simpa using hpzero
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : A) ≠ 0)
      (algebraMap_injective A hp k this)
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  have hd : (p - 1) * p ^ k ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))
  exact hpS (by simpa only [hzero, zero_pow hd, mul_zero] using hu)

theorem isDiscreteValuationRing (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsLocalRing (Extension A p k)] [IsDomain (Extension A p k)] : IsDiscreteValuationRing (Extension A p k) :=
  LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (uniformizer_ne_zero A hp k hmax) (maximalIdeal_eq_span A hp k hmax)

theorem addVal_prime (hp : p.Prime) (k : ℕ)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    [IsDomain (Extension A p k)] [IsDiscreteValuationRing (Extension A p k)] :
    IsDiscreteValuationRing.addVal (Extension A p k) (p : Extension A p k) =
      (((p - 1) * p ^ k : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  exact LocalDVR.addVal_eq_of_unit_mul_uniformizer_pow
    (maximalIdeal_eq_span A hp k hmax) hu

end LocalBase

end CirculantHadamard.RamifiedLocal

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.LocalComparison
section
namespace OAI

universe uA


noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial

variable (A : Type uA) [CommRing A]

/-- The fixed primitive-order-`p` root used at every induction level. -/
def orderPRoot (p : ℕ) : RamifiedLocal.Extension A p 0 :=
  AdjoinRoot.root (cyclotomic (p ^ (0 + 1)) A)

theorem orderPRoot_pow (p : ℕ) : orderPRoot A p ^ p = 1 := by
  calc
    orderPRoot A p ^ p = orderPRoot A p ^ (p ^ (0 + 1)) :=
      congrArg (fun n : ℕ => orderPRoot A p ^ n) (by simp)
    _ = 1 := cyclotomicAdjoinRoot_pow (R := A) (p ^ (0 + 1))

theorem orderPRoot_pow_level (p e : ℕ) : orderPRoot A p ^ (p ^ (e + 1)) = 1 := by
  calc
    orderPRoot A p ^ (p ^ (e + 1)) = orderPRoot A p ^ (p * p ^ e) :=
      congrArg (fun n : ℕ => orderPRoot A p ^ n) (pow_succ' p e)
    _ = (orderPRoot A p ^ p) ^ (p ^ e) := pow_mul _ _ _
    _ = 1 := by rw [orderPRoot_pow, one_pow]

/-- Actual order-`p` evaluation of an element of the cyclic group ring of
order `p ^ (e + 1)`. -/
def orderPValue (p e : ℕ) [NeZero p] :
    Elem A (p ^ (e + 1)) →ₐ[A] RamifiedLocal.Extension A p 0 :=
  evaluateAt (p ^ (e + 1)) (orderPRoot A p) (orderPRoot_pow_level A p e)

@[simp] theorem orderPValue_scalar (p e : ℕ) [NeZero p] (a : A) :
    orderPValue A p e (scalar (p ^ (e + 1)) a) =
      algebraMap A (RamifiedLocal.Extension A p 0) a :=
  (orderPValue A p e).commutes a

theorem orderPValue_projection (p e : ℕ) [NeZero p]
    (F : Elem A (p ^ (e + 2))) :
    orderPValue A p e
        (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) =
      orderPValue A p (e + 1) F :=
  evaluateAt_cyclicProjection _ _ _ _ F

/-- The conclusion of comparison, expressed by an actual unit and membership
in the actual ramified maximal ideal. -/
def OrderPCompared (p e : ℕ) [NeZero p] (F : Elem A (p ^ (e + 1))) : Prop :=
  ∃ u : (RamifiedLocal.Extension A p 0)ˣ,
    orderPValue A p e F = (u : RamifiedLocal.Extension A p 0) *
      algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ (e + 1)) F) ∧
    (u : RamifiedLocal.Extension A p 0) - 1 ∈
      Ideal.span {RamifiedLocal.uniformizer A p 0}

section DVR

variable [IsDomain A] [CharZero A] [IsDiscreteValuationRing A]

/-- Character comparison with every ramified extension constructed from the
input DVR. Both factors are compared, with matching group/scalar exponents. -/
theorem local_character_comparison (p : ℕ) [NeZero p] (hp : p.Prime)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    (e : ℕ) (b : Aˣ) (F K : Elem A (p ^ (e + 1)))
    (hFK : F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A))) :
    OrderPCompared A p e F ∧ OrderPCompared A p e K := by
  let : IsDomain (RamifiedLocal.Extension A p 0) :=
    RamifiedLocal.isDomain A hp 0 hmax
  let : IsLocalRing (RamifiedLocal.Extension A p 0) :=
    RamifiedLocal.isLocalRing A hp 0 hmax
  have hpA : Prime (p : A) :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer (p : A)).mpr hmax).prime
  have hpS : algebraMap A (RamifiedLocal.Extension A p 0) (p : A) ≠ 0 := by
    intro h
    exact hpA.ne_zero (RamifiedLocal.algebraMap_injective A hp 0
      (by simpa only [map_zero] using h))
  have hroot : IsLocalRing.residue (RamifiedLocal.Extension A p 0) (orderPRoot A p) = 1 := by
    have hpi : RamifiedLocal.uniformizer A p 0 ∈
        IsLocalRing.maximalIdeal (RamifiedLocal.Extension A p 0) := by
      rw [RamifiedLocal.maximalIdeal_eq_span A hp 0 hmax]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hpi
    simpa only [RamifiedLocal.uniformizer, orderPRoot, map_sub, map_one, sub_eq_zero] using hz
  have hc := comparison_induction p (algebraMap A (RamifiedLocal.Extension A p 0))
    hpA hpS (fun k => (orderPValue A p k).toRingHom)
    (fun k a => orderPValue_scalar A p k a)
    (by
      intro U
      change IsLocalRing.residue (RamifiedLocal.Extension A p 0) (orderPValue A p 0 U) =
        IsLocalRing.residue (RamifiedLocal.Extension A p 0)
          (algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ 1) U))
      simp only [orderPValue, evaluateAt_apply,
        augmentation_apply, map_sum, map_mul, map_pow, hroot, one_pow, mul_one])
    (fun k U => orderPValue_projection A p k U)
    (by
      intro k c U V hUV
      let : IsDomain (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isDomain A hp (k + 1) hmax
      let : IsLocalRing (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isLocalRing A hp (k + 1) hmax
      let : IsDiscreteValuationRing (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isDiscreteValuationRing A hp (k + 1) hmax
      have hpR : (p : RamifiedLocal.Extension A p (k + 1)) ≠ 0 := by
        intro h
        apply hpA.ne_zero
        apply RamifiedLocal.algebraMap_injective A hp (k + 1)
        simpa only [map_natCast, map_zero] using h
      exact projected_factor_divisible hp hpR
        (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos (k + 1)))
        (RamifiedLocal.addVal_prime A hp (k + 1) hmax) c U V hUV)
    e b F K hFK
  have toCompared {U : Elem A (p ^ (e + 1))}
      (hU : ResidueOneAssociated (IsLocalRing.residue (RamifiedLocal.Extension A p 0))
        (orderPValue A p e U)
        (algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ (e + 1)) U))) :
      OrderPCompared A p e U := by
    obtain ⟨u, hu, hres⟩ := hU
    refine ⟨u, hu, ?_⟩
    rw [← RamifiedLocal.maximalIdeal_eq_span A hp 0 hmax]
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, hres, map_one, sub_self]
  exact ⟨toCompared hc.1, toCompared hc.2⟩

/-- The augmentation denominators used in the corresponding ratio statement
are nonzero in the coefficient DVR. -/
theorem local_character_comparison_denominators [IsDiscreteValuationRing A] (p : ℕ) (hp : p.Prime)
    (e : ℕ) (b : Aˣ) (F K : Elem A (p ^ (e + 1)))
    (hFK : F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A))) :
    augmentation (p ^ (e + 1)) F ≠ 0 ∧ augmentation (p ^ (e + 1)) K ≠ 0 :=
  augmentation_ne_zero_of_scalar_product (Nat.cast_ne_zero.mpr hp.ne_zero) b F K hFK

end DVR

end CirculantHadamard.LocalComparison

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CoefficientEvaluation
section
namespace OAI

universe uR uS uT


noncomputable section

namespace CirculantHadamard.CyclicRing

open PrimeCharacterEvaluations

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]

/-- Map coefficients and retain the same cyclic basis. -/
def coefficientMap (φ : R →+* S) (n : ℕ) : Elem R n →+* Elem S n :=
  weightedProjection φ (AddMonoidHom.id (ZMod n)) 1

@[simp] theorem coefficientMap_single (φ : R →+* S) (n : ℕ)
    (a : ZMod n) (r : R) :
    coefficientMap φ n (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a (φ r) := by
  simp [coefficientMap, weightedProjection_single]

@[simp] theorem coefficientMap_scalar (φ : R →+* S) (n : ℕ) (r : R) :
    coefficientMap φ n (scalar n r) = scalar n (φ r) :=
  weightedProjection_scalar φ (AddMonoidHom.id (ZMod n)) 1 r

/-- Bundled naturality; no root-of-unity or nonzero-modulus premise is needed. -/
theorem evaluate_coefficientMap_hom (φ : R →+* S) (ψ : S →+* T) (n : ℕ)
    (χ : Multiplicative (ZMod n) →* T) :
    (evaluate ψ χ).comp (coefficientMap φ n) = evaluate (ψ.comp φ) χ := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, coefficientMap_single, evaluate_single]
  · intro a
    simp only [RingHom.comp_apply, coefficientMap_single, evaluate_single]

theorem evaluate_coefficientMap (φ : R →+* S) (ψ : S →+* T) {n : ℕ}
    (χ : Multiplicative (ZMod n) →* T) (F : Elem R n) :
    evaluate ψ χ (coefficientMap φ n F) = evaluate (ψ.comp φ) χ F :=
  congrArg (fun f : Elem R n →+* T => f F) (evaluate_coefficientMap_hom φ ψ n χ)

@[simp] theorem augmentation_coefficientMap (φ : R →+* S) (n : ℕ) [NeZero n]
    (F : Elem R n) :
    augmentation n (coefficientMap φ n F) = φ (augmentation n F) := by
  calc
    augmentation n (coefficientMap φ n F) =
        evaluate (RingHom.id S) (1 : Multiplicative (ZMod n) →* S)
          (coefficientMap φ n F) := by
            simpa only [RingHom.id_apply] using
              (evaluate_trivial_eq_augmentation (R := S) (S := S) (n := n)
                (RingHom.id S) (coefficientMap φ n F)).symm
    _ = evaluate ((RingHom.id S).comp φ) (1 : Multiplicative (ZMod n) →* S) F :=
      evaluate_coefficientMap φ (RingHom.id S) 1 F
    _ = φ (augmentation n F) := by
      simpa only [RingHom.id_comp] using evaluate_trivial_eq_augmentation φ F

end CirculantHadamard.CyclicRing

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.AlternatingLocalization
section
namespace OAI

universe uR uK uAZero uS uL uI uk


noncomputable section

namespace CirculantHadamard.AlternatingLocalization

open scoped BigOperators

abbrev AtMaximal (R : Type uR) [CommRing R] (m : MaximalSpectrum R) :=
  Localization.AtPrime m.asIdeal

def toFraction {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) : AtMaximal R m →ₐ[R] K :=
  Localization.mapToFractionRing K m.asIdeal.primeCompl (AtMaximal R m)
    m.asIdeal.primeCompl_le_nonZeroDivisors

theorem toFraction_injective {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) : Function.Injective (toFraction K m) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := m.asIdeal.primeCompl) (AtMaximal R m) (toFraction K m).toRingHom
  intro a ha
  change toFraction K m (algebraMap R (AtMaximal R m) a) = 0 at ha
  rw [AlgHom.commutes] at ha
  have ha0 : a = 0 := IsFractionRing.injective R K (by simpa only [map_zero] using ha)
  rw [ha0, map_zero]

/-- The integral representative and a local representative of the same fixed
fraction agree under the actual coefficient localization map. -/
theorem local_representative_eq {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) (b : R) (v : AtMaximal R m)
    (h : algebraMap R K b = toFraction K m v) :
    algebraMap R (AtMaximal R m) b = v := by
  apply toFraction_injective K m
  simpa only [AlgHom.commutes] using h

section ActualComparisonMap

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- The actual coefficient localization at the contracted prime. Maximality
of the contraction is a separate input to the local comparison theorem, not
an assumption needed to construct this map. -/
abbrev AtComap (f : A₀ →+* R) (m : MaximalSpectrum R) :=
  Localization.AtPrime (m.asIdeal.comap f)

def baseToLocal (f : A₀ →+* R) (m : MaximalSpectrum R) :
    AtComap f m →+* AtMaximal R m :=
  localizationAtComapMap f m.asIdeal

@[simp] theorem baseToLocal_algebraMap (f : A₀ →+* R) (m : MaximalSpectrum R)
    (a : A₀) :
    baseToLocal f m (algebraMap A₀ (AtComap f m) a) =
      algebraMap R (AtMaximal R m) (f a) :=
  localizationAtComapMap_algebraMap f m.asIdeal a

/-- The comparison algebra is mapped by the universal property of its actual
cyclotomic quotient, rather than by assuming an arbitrary extension map. -/
def comparisonToLocal (f : A₀ →+* R) (m : MaximalSpectrum R) (p : ℕ) (rho : R)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0) :
    AdjoinRoot (Polynomial.cyclotomic p (AtComap f m)) →+* AtMaximal R m :=
  AdjoinRoot.lift (baseToLocal f m) (algebraMap R (AtMaximal R m) rho) (by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
      Polynomial.cyclotomic.eval_apply, hroot, map_zero])

@[simp] theorem comparisonToLocal_root (f : A₀ →+* R) (m : MaximalSpectrum R)
    (p : ℕ) (rho : R) (hroot : (Polynomial.cyclotomic p R).eval rho = 0) :
    comparisonToLocal f m p rho hroot
        (AdjoinRoot.root (Polynomial.cyclotomic p (AtComap f m))) =
      algebraMap R (AtMaximal R m) rho :=
  AdjoinRoot.lift_root _

@[simp] theorem comparisonToLocal_of (f : A₀ →+* R) (m : MaximalSpectrum R)
    (p : ℕ) (rho : R) (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (a : AtComap f m) :
    comparisonToLocal f m p rho hroot
        (AdjoinRoot.of (Polynomial.cyclotomic p (AtComap f m)) a) =
      baseToLocal f m a :=
  AdjoinRoot.lift_of _

/-- Residue characteristic is derived from membership of the rational prime,
not assumed as an independent property of the chosen maximal ideal. -/
theorem residue_charP (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) :
    CharP (IsLocalRing.ResidueField (AtMaximal R m)) p := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  have hpzero : (p : k) = 0 := by
    have hm : algebraMap R (AtMaximal R m) (p : R) ∈
        IsLocalRing.maximalIdeal (AtMaximal R m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (AtMaximal R m) m.asIdeal _).mpr hpm
    simpa only [map_natCast] using (IsLocalRing.residue_eq_zero_iff _).mpr hm
  exact (CharP.charP_iff_prime_eq_zero hp).mpr hpzero

/-- A p-th root has residue one at every maximal ideal containing p. -/
theorem residue_root_eq_one (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) (rho : R) (hrho : rho ^ p = 1) :
    IsLocalRing.residue (AtMaximal R m) (algebraMap R (AtMaximal R m) rho) = 1 := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  let : Fact p.Prime := ⟨hp⟩
  let : CharP k p := residue_charP m p hp hpm
  let r : k := IsLocalRing.residue (AtMaximal R m)
    (algebraMap R (AtMaximal R m) rho)
  have hpow : r ^ p = 1 := by
    dsimp [r]
    rw [← map_pow, ← map_pow, hrho, map_one, map_one]
  have hnil : (r - 1) ^ p = 0 := by rw [sub_pow_char, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hnil)

theorem residue_unit_eq_one_of_span {S : Type uS} {L : Type uL} [CommRing S] [CommRing L]
    [IsLocalRing L] (f : S →+* L) (rho : S) (v : Sˣ)
    (hv : (v : S) - 1 ∈ Ideal.span ({rho - 1} : Set S))
    (hrho : IsLocalRing.residue L (f rho) = 1) :
    IsLocalRing.residue L ((Units.map f.toMonoidHom v : Lˣ) : L) = 1 := by
  let g : S →+* IsLocalRing.ResidueField L := (IsLocalRing.residue L).comp f
  have hspan : Ideal.span ({rho - 1} : Set S) ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a = rho - 1 := Set.mem_singleton_iff.mp ha
    subst a
    change g (rho - 1) = 0
    simp only [map_sub, map_one, RingHom.comp_apply, g, hrho, sub_self]
  have hz := hspan hv
  change g ((v : S) - 1) = 0 at hz
  have hval : g (v : S) = 1 := sub_eq_zero.mp (by simpa only [map_sub, map_one] using hz)
  exact hval

theorem map_residueOneAssociated {S : Type uS} {L : Type uL} [CommRing S] [CommRing L]
    [IsLocalRing S] [IsLocalRing L] (f : S →+* L) (rho : S)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span ({rho - 1} : Set S))
    (hrho : IsLocalRing.residue L (f rho) = 1) {a b : S}
    (hab : LocalComparison.ResidueOneAssociated (IsLocalRing.residue S) a b) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue L) (f a) (f b) := by
  obtain ⟨v, hv, hres⟩ := hab
  have hspan : (v : S) - 1 ∈ Ideal.span ({rho - 1} : Set S) := by
    rw [← hmax]
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, map_one, hres, sub_self]
  refine ⟨Units.map f.toMonoidHom v, ?_,
    residue_unit_eq_one_of_span f rho v hspan hrho⟩
  change f a = f (v : S) * f b
  simpa only [map_mul, Units.coe_map] using congrArg f hv

end ActualComparisonMap

/-- The local association is converted to the actual fraction-field quotient
only after the augmentation image is known to be nonzero. -/
theorem local_edge_of_associated {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (m : MaximalSpectrum R)
    (a b : R) (hb : algebraMap R K b ≠ 0)
    (h : LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m) a) (algebraMap R (AtMaximal R m) b)) :
    ∃ v : (AtMaximal R m)ˣ,
      toFraction K m (v : AtMaximal R m) = algebraMap R K a / algebraMap R K b ∧
      IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1 := by
  obtain ⟨v, hv, hres⟩ := h
  refine ⟨v, ?_, hres⟩
  apply (eq_div_iff hb).mpr
  have hmap := congrArg (toFraction K m) hv
  simpa only [map_mul, AlgHom.commutes] using hmap.symm

/-- A finite prime factorization supplies the away-from-u unit, including u=1. -/
theorem natCast_isUnit_of_primeFactors {R : Type uR} [CommRing R]
    (u : ℕ) (hu : u ≠ 0) (hprime : ∀ p ∈ u.primeFactors, IsUnit (p : R)) :
    IsUnit (u : R) := by
  rw [← Nat.prod_primeFactorsList hu, Nat.cast_list_prod]
  apply List.prod_isUnit
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact hprime p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)

theorem local_norm_factor_isUnit {R : Type uR} [CommRing R]
    (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal)
    (x y : R) (hnorm : x * y = (u : R) ^ 2) :
    IsUnit (algebraMap R (AtMaximal R m) x) := by
  have huunit : IsUnit (u : AtMaximal R m) :=
    natCast_isUnit_of_primeFactors u hu (fun p hp => by
      have h := (IsLocalization.AtPrime.isUnit_to_map_iff
        (AtMaximal R m) m.asIdeal (p : R)).mpr (havoid p hp)
      simpa only [map_natCast] using h)
  apply isUnit_of_mul_isUnit_left (y := algebraMap R (AtMaximal R m) y)
  rw [← map_mul, hnorm, map_pow, map_natCast]
  exact huunit.pow 2

section AlternatingUnits

variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]

theorem exists_unit_of_edges (f : R →+* K) (res : R →+* k)
    (t : Finset I) (p : I) (hp : p ∈ t) (x : Finset I → K)
    (hedge : ∀ S ∈ (t.erase p).powerset, ∃ v : Rˣ,
      f (v : R) = x (insert p S) / x S ∧ res (v : R) = 1) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t x ∧ res (v : R) = 1 := by
  classical
  let edge : Finset I → Rˣ := fun S =>
    if hS : S ∈ (t.erase p).powerset then Classical.choose (hedge S hS) else 1
  have hedge' : ∀ S ∈ (t.erase p).powerset,
      f (edge S : R) = x (insert p S) / x S ∧ res (edge S : R) = 1 := by
    intro S hS
    simpa only [edge, dif_pos hS] using Classical.choose_spec (hedge S hS)
  let v : Rˣ := ∏ S ∈ (t.erase p).powerset, (edge S)⁻¹ ^ subsetSign S
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  let tok : Rˣ →* k := res.toMonoidHom.comp (Units.coeHom R)
  refine ⟨v, ?_, ?_⟩
  · change toK v = alternatingProduct t x
    rw [alternatingProduct_pair t x p hp]
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_congr rfl
    intro S hS
    change (f (edge S : R))⁻¹ ^ subsetSign S = _
    rw [(hedge' S hS).1, inv_div]
  · change tok v = 1
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_eq_one
    intro S hS
    change (res (edge S : R))⁻¹ ^ subsetSign S = 1
    rw [(hedge' S hS).2, inv_one, one_zpow]

/-- Ordinary local units give an actual local unit representative of the fixed
field product. The representatives are not independently chosen field values. -/
theorem exists_unit_of_factor_units (f : R →+* K) (t : Finset I)
    (x : Finset I → R) (hx : ∀ S ⊆ t, IsUnit (x S)) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t (fun S => f (x S)) := by
  classical
  let units : Finset I → Rˣ := fun S => if hS : S ⊆ t then (hx S hS).unit else 1
  have hval : ∀ S ⊆ t, (units S : R) = x S := by
    intro S hS
    simp only [units, dif_pos hS, IsUnit.unit_spec]
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  refine ⟨alternatingProduct t units, ?_⟩
  change toK (alternatingProduct t units) = _
  rw [map_alternatingProduct]
  apply alternatingProduct_congr
  intro S hS
  change f (units S : R) = f (x S)
  rw [hval S hS]

end AlternatingUnits

section MaximalCover

variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The away-from-u case uses only the evaluated norm identity and avoidance
of the actual rational prime factors of u. -/
theorem exists_local_unit_away (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (x y : Finset I → R)
    (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal) :
    ∃ v : (AtMaximal R m)ˣ,
      toFraction K m (v : AtMaximal R m) =
        alternatingProduct t (fun S => algebraMap R K (x S)) := by
  obtain ⟨v, hv⟩ := exists_unit_of_factor_units (toFraction K m).toRingHom t
    (fun S => algebraMap R (AtMaximal R m) (x S))
    (fun S hS => local_norm_factor_isUnit m u hu havoid (x S) (y S) (hnorm S hS))
  refine ⟨v, ?_⟩
  change toFraction K m (v : AtMaximal R m) = alternatingProduct t
    (fun S => toFraction K m (algebraMap R (AtMaximal R m) (x S))) at hv
  simpa only [AlgHom.commutes] using hv

/-- Every maximal ideal is covered either by a genuine prime-direction edge
comparison or by the norm argument. Local character comparison supplies the
edge hypotheses, without assuming that the product belongs to the base ring. -/
theorem exists_base_of_edges_and_norm (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (prime : I → ℕ)
    (hcover : ∀ p ∈ u.primeFactors, ∃ i ∈ t, prime i = p)
    (x y : Finset I → R) (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (hedge : ∀ m : MaximalSpectrum R, ∀ i ∈ t, (prime i : R) ∈ m.asIdeal →
      ∀ S ∈ (t.erase i).powerset, ∃ v : (AtMaximal R m)ˣ,
        toFraction K m (v : AtMaximal R m) =
          algebraMap R K (x (insert i S)) / algebraMap R K (x S) ∧
        IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1) :
    ∃ b : R, algebraMap R K b =
      alternatingProduct t (fun S => algebraMap R K (x S)) := by
  classical
  apply exists_base_of_localization_images
  intro m
  by_cases hm : ∃ p ∈ u.primeFactors, (p : R) ∈ m.asIdeal
  · obtain ⟨p, hp, hpm⟩ := hm
    obtain ⟨i, hi, hpi⟩ := hcover p hp
    have him : (prime i : R) ∈ m.asIdeal := by rw [hpi]; exact hpm
    obtain ⟨v, hv, _⟩ := exists_unit_of_edges (toFraction K m).toRingHom
      (IsLocalRing.residue (AtMaximal R m)) t i hi
      (fun S => algebraMap R K (x S)) (hedge m i hi him)
    exact ⟨v, hv⟩
  · have havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal := by
      intro p hp hpm
      exact hm ⟨p, hp, hpm⟩
    obtain ⟨v, hv⟩ := exists_local_unit_away (K := K) m u hu t x y hnorm havoid
    exact ⟨v, hv⟩

end MaximalCover

section ConcreteComparison

open CyclicRing

/-- Bezout makes the complementary integer factor a unit in the actual
localization at any prime containing `p`. -/
theorem coprime_natCast_isUnit {R : Type uR} [CommRing R]
    (I : Ideal R) [I.IsPrime] (p c : ℕ) (hpc : Nat.Coprime p c)
    (hpI : (p : R) ∈ I) : IsUnit (c : Localization.AtPrime I) := by
  have hcI : (c : R) ∉ I := by
    intro hc
    obtain ⟨a, b, hab⟩ := hpc.cast (R := R)
    have hone : (1 : R) ∈ I := by
      rw [← hab]
      exact I.add_mem (I.mul_mem_left a hpI) (I.mul_mem_left b hc)
    exact (inferInstance : I.IsPrime).ne_top (I.eq_top_iff_one.mpr hone)
  simpa only [map_natCast] using
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime I) I (c : R)).mpr hcI

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- Apply the proved DVR comparison after coefficient localization and map its
actual unit through the cyclotomic quotient into the target maximal localization.
The group order and scalar prime exponent are the same `p ^ (e + 1)`. -/
theorem actual_local_character_association
    (f : A₀ →+* R) (m : MaximalSpectrum R)
    [IsDomain (AtComap f m)] [CharZero (AtComap f m)]
    [IsDiscreteValuationRing (AtComap f m)]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpm : (p : R) ∈ m.asIdeal)
    (hmax : IsLocalRing.maximalIdeal (AtComap f m) =
      Ideal.span {(p : AtComap f m)})
    (rho : R) (hrho : rho ^ p = 1)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (n e c : ℕ) [NeZero n] (hn : n = p ^ (e + 1))
    (hrhon : rho ^ n = 1) (hc : IsUnit (c : AtComap f m))
    (F K : Elem A₀ n)
    (hFK : F * K = scalar n ((p : A₀) ^ (e + 1) * (c : A₀))) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m)
        (evaluate f (CyclicPolynomial.powerCharacter n rho hrhon) F))
      (algebraMap R (AtMaximal R m) (evaluate f 1 F)) := by
  subst n
  let A := AtComap f m
  let L := AtMaximal R m
  let φ : A₀ →+* A := algebraMap A₀ A
  let FA := coefficientMap φ (p ^ (e + 1)) F
  let KA := coefficientMap φ (p ^ (e + 1)) K
  have hFA : FA * KA = scalar (p ^ (e + 1))
      ((p : A) ^ (e + 1) * (hc.unit : A)) := by
    dsimp [FA, KA]
    rw [← map_mul, hFK, coefficientMap_scalar, map_mul, map_pow,
      map_natCast, map_natCast]
  obtain ⟨v, hv, hvspan⟩ :=
    (LocalComparison.local_character_comparison A p hp hmax e hc.unit FA KA hFA).1
  let j : RamifiedLocal.Extension A p 0 →+* L :=
    comparisonToLocal f m (p ^ (0 + 1)) rho (by simpa only [Nat.zero_add, pow_one] using hroot)
  have jroot : j (LocalComparison.orderPRoot A p) = algebraMap R L rho := by
    exact comparisonToLocal_root f m _ rho _
  have jcoeff (a : A) : j (algebraMap A (RamifiedLocal.Extension A p 0) a) =
      baseToLocal f m a := by
    exact comparisonToLocal_of f m _ rho _ a
  have evalRoot :
      (j.comp (LocalComparison.orderPValue A p e).toRingHom).comp
          (coefficientMap φ (p ^ (e + 1))) =
        (algebraMap R L).comp
          (evaluate f (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single 0 r))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single 0 r))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ (0 : ZMod (p ^ (e + 1))).val)
        (baseToLocal_algebraMap f m r)
    · intro a
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single a 1))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single a 1))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ a.val)
        (baseToLocal_algebraMap f m (1 : A₀))
  have evalOne : j (algebraMap A (RamifiedLocal.Extension A p 0)
      (augmentation (p ^ (e + 1)) FA)) =
        algebraMap R L (evaluate f 1 F) := by
    rw [jcoeff]
    dsimp [FA]
    rw [augmentation_coefficientMap, baseToLocal_algebraMap,
      evaluate_trivial_eq_augmentation]
  have hres : IsLocalRing.residue L
      ((Units.map j.toMonoidHom v : Lˣ) : L) = 1 := by
    apply residue_unit_eq_one_of_span j (LocalComparison.orderPRoot A p) v
    · exact hvspan
    · rw [jroot]
      exact residue_root_eq_one m p hp hpm rho hrho
  refine ⟨Units.map j.toMonoidHom v, ?_, hres⟩
  have heval := DFunLike.congr_fun evalRoot F
  change j (LocalComparison.orderPValue A p e FA) =
    algebraMap R L (evaluate f
      (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon) F) at heval
  rw [← heval]
  change j (LocalComparison.orderPValue A p e FA) =
    j (v : RamifiedLocal.Extension A p 0) * algebraMap R L (evaluate f 1 F)
  simpa only [map_mul, evalOne, Units.coe_map] using congrArg j hv

end ConcreteComparison

section ActualAlternatingProduct

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing

/-- Name the canonical algebra structures directly to avoid searching through
iterated-localization algebra instances for the concrete coefficient ring. -/
instance B_local_algebra (u : ℕ) (m : MaximalSpectrum (B u)) :
    Algebra (B u) (AtMaximal (B u) m) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := m.asIdeal.primeCompl)

instance B_fraction_algebra (u : ℕ) : Algebra (B u) (FractionRing (B u)) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := nonZeroDivisors (B u))

/-- The selected element of B satisfies the actual cyclotomic relation. -/
theorem rhoB_cyclotomic_root (u : ℕ) (p : PrimeIndex u) :
    (Polynomial.cyclotomic p.val (B u)).eval (rhoB u p) = 0 := by
  have hp := prime_of_mem p.property
  apply Subtype.val_injective
  change (B u).val ((Polynomial.cyclotomic p.val (B u)).eval (rhoB u p)) =
    (B u).val (0 : B u)
  rw [map_zero]
  change (B u).val.toRingHom
    ((Polynomial.cyclotomic p.val (B u)).eval (rhoB u p)) = 0
  rw [← Polynomial.cyclotomic.eval_apply]
  exact (rho_isPrimitiveRoot p.val hp.ne_zero).isRoot_cyclotomic hp.pos

theorem subset_evaluations_local_associated (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal)
    (S : Finset (PrimeIndex u)) (hpS : p ∉ S) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal (B u) m))
      (algebraMap (B u) (AtMaximal (B u) m) (subsetEvaluation u hu (insert p S) x))
      (algebraMap (B u) (AtMaximal (B u) m) (subsetEvaluation u hu S x)) := by
  let f := (awayInclusion u p.val).toRingHom
  let A := AtComap f m
  let : NeZero p.val := ⟨(prime_of_mem p.property).ne_zero⟩
  let : CharZero A := CyclotomicAwayLocal.awayLocal_charZero u p.val m.asIdeal
  let : IsDiscreteValuationRing A :=
    CyclotomicAwayLocal.awayLocal_isDiscreteValuationRing u p.val huodd p.property m.asIdeal hpm
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p.val : A)} :=
    CyclotomicAwayLocal.awayLocal_maximalIdeal_eq_span u p.val huodd p.property m.asIdeal hpm
  let e := exponent u p.val - 1
  have he : exponent u p.val = e + 1 := by
    dsimp [e]
    have hpos := exponent_pos hu p.property
    omega
  have hn : order u p.val = p.val ^ (e + 1) := by rw [order, he]
  have hc : IsUnit (cofactor u p.val : A) :=
    coprime_natCast_isUnit (m.asIdeal.comap f) p.val (cofactor u p.val)
      (cofactor_coprime hu p.property)
      (CyclotomicAwayLocal.prime_mem_awayPrime u p.val m.asIdeal hpm)
  let F := partialEvaluation u hu p S x
  let K := partialEvaluation u hu p S (ringStar x)
  have hnum : u ^ 2 = p.val ^ (e + 1) * cofactor u p.val := by
    rw [← hn]
    exact (order_mul_cofactor u p.val).symm
  have hFK : F * K = scalar (order u p.val)
      ((p.val : awayRing u p.val) ^ (e + 1) * (cofactor u p.val : awayRing u p.val)) := by
    dsimp [F, K]
    rw [partialEvaluation_product u hu p S x (ringStar x) hx]
    apply congrArg (scalar (order u p.val))
    exact_mod_cast hnum
  have h := actual_local_character_association f m p.val (prime_of_mem p.property)
    hpm hmax (rhoB u p) (rhoB_pow u p) (rhoB_cyclotomic_root u p)
    (order u p.val) e (cofactor u p.val) hn
    (root_order_pow u hu p (rhoB u p) (rhoB_pow u p)) hc F K hFK
  change LocalComparison.ResidueOneAssociated _
    (algebraMap (B u) (AtMaximal (B u) m) (partialAtRoot u hu p F))
    (algebraMap (B u) (AtMaximal (B u) m) (partialAtOne u p F)) at h
  simpa only [F, partialEvaluation_at_root_apply,
    partialEvaluation_at_one_apply u hu p S hpS x] using h

/-- The denominator is nonzero because it is an actual evaluated norm factor. -/
theorem exists_local_edge_unit (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal)
    (S : Finset (PrimeIndex u)) (hpS : p ∉ S) :
    ∃ v : (AtMaximal (B u) m)ˣ,
      toFraction (FractionRing (B u)) m (v : AtMaximal (B u) m) =
        algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu (insert p S) x) /
          algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x) ∧
      IsLocalRing.residue (AtMaximal (B u) m) (v : AtMaximal (B u) m) = 1 := by
  apply local_edge_of_associated m _ _
  · intro hz
    apply subsetEvaluation_ne_zero u hu S x hx
    apply IsFractionRing.injective (B u) (FractionRing (B u))
    simpa only [map_zero] using hz
  · exact subset_evaluations_local_associated u hu huodd x hx p m hpm S hpS

/-- At every maximal ideal over p, the one fixed global alternating product
is the image of a unit with residue one. No edge comparison is an input. -/
theorem exists_local_unit_alternatingProduct (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal) :
    ∃ v : (AtMaximal (B u) m)ˣ,
      toFraction (FractionRing (B u)) m (v : AtMaximal (B u) m) =
        alternatingProduct (Finset.univ : Finset (PrimeIndex u))
          (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x)) ∧
      IsLocalRing.residue (AtMaximal (B u) m) (v : AtMaximal (B u) m) = 1 := by
  classical
  apply exists_unit_of_edges (toFraction (FractionRing (B u)) m).toRingHom
    (IsLocalRing.residue (AtMaximal (B u) m)) Finset.univ p (Finset.mem_univ p)
  intro S hS
  have hpS : p ∉ S := fun hp =>
    (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hp)).1 rfl
  exact exists_local_edge_unit u hu huodd x hx p m hpm S hpS

/-- Integrality of the actual subset-character alternating product. The
maximal ideals over prime divisors use the proved local comparison; every
other maximal ideal uses the actual norm identity. -/
theorem exists_integral_alternatingProduct (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    ∃ z : B u, algebraMap (B u) (FractionRing (B u)) z =
      alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x)) := by
  classical
  refine exists_base_of_edges_and_norm u hu.ne' Finset.univ
    (fun p : PrimeIndex u => p.val) ?_
    (fun S => subsetEvaluation u hu S x) (fun S => star (subsetEvaluation u hu S x)) ?_ ?_
  · intro p hp
    exact ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    simpa only [Nat.cast_pow] using subsetEvaluation_norm u hu S x hx
  · intro m p _ hpm S hS
    have hpS : p ∉ S := fun hp =>
      (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hp)).1 rfl
    exact exists_local_edge_unit u hu huodd x hx p m hpm S hpS

end ActualAlternatingProduct

end CirculantHadamard.AlternatingLocalization

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicAdjoin
section
namespace OAI

universe uR


noncomputable section

namespace CirculantHadamard.CyclotomicAdjoin

/-- The actual integer algebra generated by `s`. -/
abbrev Ring (s : Set ℂ) : Type := Algebra.adjoin ℤ s

/-- The actual intermediate field generated over the rationals by `s`. -/
abbrev Field (s : Set ℂ) : Type := IntermediateField.adjoin ℚ s

/-- Each generator's positive power relation is a monic integral relation
over both the integers and the rationals. -/
theorem root_integral (R : Type uR) [CommRing R] [Algebra R ℂ] {ζ : ℂ}
    (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) : IsIntegral R ζ := by
  obtain ⟨n, hn, hpow⟩ := hζ
  apply IsIntegral.of_pow hn
  rw [hpow]
  exact isIntegral_one

/-- Containment of the integer algebra in the rationally generated field,
with the latter viewed as an integer subalgebra of `ℂ`. -/
theorem ring_le_field (s : Set ℂ) :
    Algebra.adjoin ℤ s ≤
      (IntermediateField.adjoin ℚ s).toSubalgebra.restrictScalars ℤ := by
  apply Algebra.adjoin_le
  intro ζ hζ
  exact IntermediateField.subset_adjoin ℚ s hζ

/-- The concrete inclusion preserves the underlying complex number. -/
def inclusion (s : Set ℂ) : Ring s →+* Field s where
  toFun z := ⟨(z : ℂ), ring_le_field s z.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem inclusion_coe (s : Set ℂ) (z : Ring s) :
    ((inclusion s z : Field s) : ℂ) = (z : ℂ) := rfl

theorem inclusion_injective (s : Set ℂ) : Function.Injective (inclusion s) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : Field s => (z : ℂ)) hxy

/-- Every element of the integer algebra is integral over the integers.
Finiteness of the generator set is not needed for this conclusion. -/
theorem integral {s : Set ℂ}
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (z : Ring s) : IsIntegral ℤ z := by
  have hA : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ s) :=
    Algebra.IsIntegral.adjoin (fun ζ hζ => root_integral ℤ (hroots ζ hζ))
  exact Algebra.isIntegral_def.mp hA z

/-- In particular the corresponding actual complex number is integral. -/
theorem integral_coe {s : Set ℂ}
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (z : Ring s) : IsIntegral ℤ (z : ℂ) :=
  map_isIntegral_int (Algebra.adjoin ℤ s).val (integral hroots z)

/-- Integrality of the element after its literal inclusion into the field. -/
theorem inclusion_integral {s : Set ℂ}
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (z : Ring s) : IsIntegral ℤ (inclusion s z) :=
  map_isIntegral_int (inclusion s) (integral hroots z)

/-- A finite set of roots of unity generates a finite-dimensional extension
of `ℚ`. -/
theorem finiteDimensional {s : Set ℂ} (hs : s.Finite)
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) :
    FiniteDimensional ℚ (Field s) := by
  classical
  let : Fintype s := hs.fintype
  exact IntermediateField.finiteDimensional_adjoin
    (fun ζ hζ => root_integral ℚ (hroots ζ hζ))

/-- The number-field structure for the concrete rational adjoin follows
from its finite dimension. -/
theorem numberField {s : Set ℂ} (hs : s.Finite)
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) :
    NumberField (Field s) := by
  let : FiniteDimensional ℚ (Field s) := finiteDimensional hs hroots
  exact NumberField.of_module_finite ℚ (Field s)

end CirculantHadamard.CyclotomicAdjoin

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.Kronecker
section
namespace OAI

universe uK


namespace CirculantHadamard

/-- An algebraic integer in a number field with all embedding norms equal to
one is a root of unity, with a positive exponent. -/
theorem root_of_unity_of_norm_embeddings (K : Type uK) [Field K] [NumberField K]
    {z : K} (hzi : IsIntegral ℤ z)
    (hz : ∀ σ : K →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hzi hz
  exact ⟨n, hn, hpow⟩

theorem finite_adjoin_root_of_unity (s : Set ℂ) (hs : s.Finite)
    (hroots : ∀ ζ ∈ s, ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (z : Algebra.adjoin ℤ s)
    (hz : ∀ σ : Algebra.adjoin ℤ s →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  let : NumberField (CyclotomicAdjoin.Field s) :=
    CyclotomicAdjoin.numberField hs hroots
  have hnorm (σ : CyclotomicAdjoin.Field s →+* ℂ) :
      ‖σ (CyclotomicAdjoin.inclusion s z)‖ = 1 :=
    hz (σ.comp (CyclotomicAdjoin.inclusion s))
  obtain ⟨n, hn, hpow⟩ := root_of_unity_of_norm_embeddings
    (CyclotomicAdjoin.Field s) (CyclotomicAdjoin.inclusion_integral hroots z) hnorm
  refine ⟨n, hn, CyclotomicAdjoin.inclusion_injective s ?_⟩
  simpa only [map_pow, map_one] using hpow

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.CyclotomicTorsion
section
namespace OAI


namespace CirculantHadamard

theorem B_root_of_unity (u : ℕ) (z : CyclotomicRings.B u)
    (hz : ∀ σ : CyclotomicRings.B u →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  apply finite_adjoin_root_of_unity
    (({Complex.I} : Set ℂ) ∪ CyclotomicRings.rho '' (u.primeFactors : Set ℕ))
    ((Set.finite_singleton Complex.I).union
      (u.primeFactors.finite_toSet.image CyclotomicRings.rho)) ?_ z hz
  intro ζ hζ
  rcases hζ with hI | ⟨p, hp, rfl⟩
  · have hζI : ζ = Complex.I := Set.mem_singleton_iff.mp hI
    subst ζ
    exact ⟨4, by decide, CyclotomicRings.I_isPrimitiveRoot.pow_eq_one⟩
  · have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    exact ⟨p, hprime.pos, CyclotomicRings.rho_pow p hprime.ne_zero⟩

end CirculantHadamard

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.AlternatingTorsion
section
namespace OAI


noncomputable section

namespace CirculantHadamard

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations
open AlternatingLocalization

/-- The single fixed field element used for every prime-direction comparison. -/
abbrev alternatingValue (u : ℕ) (hu : 0 < u)
    (x : CyclicRing.Elem GaussianRing (u ^ 2)) : FractionRing (B u) :=
  alternatingProduct (Finset.univ : Finset (PrimeIndex u))
    (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x))

/-- Denominator removal and all complex homomorphisms are discharged for the
actual character values before invoking Kronecker's criterion. -/
theorem exists_integral_alternating_root_of_unity (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    ∃ z : B u,
      algebraMap (B u) (FractionRing (B u)) z =
        alternatingValue u (lt_trans Nat.zero_lt_one hu) x ∧
      ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  classical
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  obtain ⟨z, hz⟩ := exists_integral_alternatingProduct u hu0 huodd x hx
  refine ⟨z, hz, B_root_of_unity u z ?_⟩
  intro σ
  have ht : (Finset.univ : Finset (PrimeIndex u)).Nonempty := by
    obtain ⟨p, hp⟩ := primes_nonempty hu
    exact ⟨⟨p, hp⟩, Finset.mem_univ _⟩
  have hne : ∀ S ⊆ (Finset.univ : Finset (PrimeIndex u)),
      algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu0 S x) ≠ 0 := by
    intro S _ hS
    apply subsetEvaluation_ne_zero u hu0 S x hx
    apply IsFractionRing.injective (B u) (FractionRing (B u))
    simpa only [map_zero] using hS
  exact norm_hom_integral_alternatingProduct
    (algebraMap (B u) (FractionRing (B u)))
    (IsFractionRing.injective (B u) (FractionRing (B u)))
    Finset.univ ht (fun S => subsetEvaluation u hu0 S x) z hne hz σ (u : ℝ)
    (by exact_mod_cast hu0) (fun S _ => subsetEvaluation_map_norm u hu0 S x hx σ)

/-- The same alternating product is killed by a power of every actual prime
dividing u. The maximal ideal and characteristic-p residue field are built
from the concrete integral coefficient ring. -/
theorem alternatingProduct_prime_power_torsion (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) :
    ∃ a : ℕ, (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ^ (p.val ^ a) = 1 := by
  classical
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  obtain ⟨z, hz, hfinite⟩ := exists_integral_alternating_root_of_unity u hu huodd x hx
  have hp : p.val.Prime := prime_of_mem p.property
  obtain ⟨m, hm, _, hpm⟩ := exists_maximal_ideal_over_nat_prime_of_charZero (B u) hp
  let M : MaximalSpectrum (B u) := ⟨m, hm⟩
  let : Algebra (B u) (AtMaximal (B u) M) := B_local_algebra u M
  obtain ⟨v, hv, hvres⟩ :=
    exists_local_unit_alternatingProduct u hu0 huodd x hx p M hpm
  have hlocal : algebraMap (B u) (AtMaximal (B u) M) z =
      (v : AtMaximal (B u) M) :=
    local_representative_eq (FractionRing (B u)) M z v (hz.trans hv.symm)
  let : CharP (IsLocalRing.ResidueField (AtMaximal (B u) M)) p.val :=
    residue_charP M p.val hp hpm
  let f : B u →+* IsLocalRing.ResidueField (AtMaximal (B u) M) :=
    (IsLocalRing.residue (AtMaximal (B u) M)).comp
      (algebraMap (B u) (AtMaximal (B u) M))
  have hres : f z = 1 := by
    change IsLocalRing.residue (AtMaximal (B u) M)
      (algebraMap (B u) (AtMaximal (B u) M) z) = 1
    rw [hlocal]
    exact hvres
  obtain ⟨a, ha⟩ := exists_prime_power_of_residue_one f z hp hres hfinite
  refine ⟨a, ?_⟩
  have h := congrArg (algebraMap (B u) (FractionRing (B u))) ha
  simpa only [map_pow, map_one, hz] using h

/-- The actual subset-character product has a positive odd torsion exponent. -/
theorem alternatingProduct_odd_torsion (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u : GaussianRing) ^ 2)) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ^ m = 1 := by
  classical
  have hx' : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing) := by
    simpa only [Nat.cast_pow] using hx
  obtain ⟨p, hp⟩ := primes_nonempty hu
  obtain ⟨a, ha⟩ := alternatingProduct_prime_power_torsion u hu huodd x hx' ⟨p, hp⟩
  exact ⟨p ^ a, pow_pos (prime_of_mem hp).pos _, (odd_of_mem huodd hp).pow, ha⟩

/-- With two distinct prime directions the single fixed product is one. -/
theorem alternatingProduct_eq_one_of_two_primes (u : ℕ) [NeZero (u ^ 2)]
    (hu : 1 < u) (huodd : Odd u) (x : CyclicRing.Elem GaussianRing (u ^ 2))
    (hx : x * CyclicRing.ringStar x =
      CyclicRing.scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p q : PrimeIndex u) (hpq : p ≠ q) :
    alternatingValue u (lt_trans Nat.zero_lt_one hu) x = 1 := by
  obtain ⟨a, ha⟩ := alternatingProduct_prime_power_torsion u hu huodd x hx p
  obtain ⟨b, hb⟩ := alternatingProduct_prime_power_torsion u hu huodd x hx q
  have hcop : Nat.Coprime (p.val ^ a) (q.val ^ b) :=
    Nat.coprime_pow_primes a b (prime_of_mem p.property) (prime_of_mem q.property)
      (fun h => hpq (Subtype.ext h))
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb)
  have hd1 : orderOf (alternatingValue u (lt_trans Nat.zero_lt_one hu) x) ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

end CirculantHadamard

end

end OAI
end

-- OAI.LinearAlgebra.CirculantHadamard.BinaryContradiction
section
namespace OAI

noncomputable section

namespace CirculantHadamard

open CyclicRing BinaryEvaluation

/-- The binary contradiction starts with the original integer sign row and
its full cyclic norm equation. -/
theorem binary_sign_norm_impossible {u : ℕ} [NeZero u]
    (hu : 1 < u) (hodd : Odd u)
    (f : Elem ℤ (4 * u ^ 2)) (hsign : ∀ a, IsSign (f.coeff a))
    (hnorm : f * ringStar f = scalar (4 * u ^ 2) ((4 * u ^ 2 : ℕ) : ℤ)) :
    False := by
  let hu0 : 0 < u := lt_trans Nat.zero_lt_one hu
  let H := BinaryBlocks.blocks (BinaryBlocks.crt ℤ u hodd f)
  have hH : BinaryCoefficients.Signs (fun j => (H j).coeff) :=
    BinaryBlocks.crt_blocks_signs hodd f hsign
  obtain ⟨hc, hd, hg⟩ := gaussian_norms_of_cyclic_norm hodd f hsign hnorm
  apply BinaryLocalFamily.contradiction_of_evaluated_data u hu0 hodd
    (cG H) (dG H) (gG H) hc hd hg
    (aValue u hu0 H) (bValue u hu0 H) (UValue u hu0 H)
  · exact fun S => cValue_eq u hu0 H S
  · exact fun S => dValue_eq u hu0 H S
  · exact fun S => gValue_eq u hu0 hH S
  · exact alternatingProduct_odd_torsion u hu hodd (cG H)
      (by simpa only [Nat.cast_pow] using hc)
  · exact alternatingProduct_odd_torsion u hu hodd (dG H)
      (by simpa only [Nat.cast_pow] using hd)
  · exact alternatingProduct_odd_torsion u hu hodd (gG H)
      (by simpa only [Nat.cast_pow] using hg)

/-- No real circulant sign Hadamard matrix has order `4u²` for odd `u > 1`.
The original real-matrix predicate is converted by the proved integer-row
equivalence; every subsequent construction is made from that actual row. -/
theorem not_exists_four_mul_odd_square {u : ℕ}
    (hu : 1 < u) (hodd : Odd u) :
    ¬ ExistsRealCirculantHadamard (4 * u ^ 2) := by
  let : NeZero u := ⟨(lt_trans Nat.zero_lt_one hu).ne'⟩
  intro hH
  obtain ⟨f, hsign, hnorm⟩ :=
    (exists_cyclicSignRow_iff_real (n := 4 * u ^ 2)).mpr hH
  exact binary_sign_norm_impossible hu hodd f hsign hnorm

end CirculantHadamard

end

end OAI
end

end BarkerOddSquarePort

theorem OMA.solution : type_of% @Arxiv.«2104.00502».barker_conjecture := by
  intro a ha
  rcases Nat.even_or_odd a.length with he | ho
  · by_cases hsmall : a.length ≤ 2
    · omega
    have hmatrix := BarkerEven.OddBarker.existsRealCirculantHadamard_of_even_internal
      a.get he (by omega) (BarkerEven.BarkerList.indexed_barker a ha)
    obtain ⟨u, hu, huo, hn⟩ :=
      BarkerOrderPort.CirculantHadamard.order_reduction (by omega) hmatrix
    by_cases hlarge : 1 < u
    · exact (BarkerOddSquarePort.OAI.CirculantHadamard.not_exists_four_mul_odd_square
        hlarge huo (hn ▸ hmatrix)).elim
    have hu_one : u = 1 := by omega
    simp [hu_one] at hn
    omega
  · exact BarkerList.odd_length_bound a ha ho
