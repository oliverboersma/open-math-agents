import FormalConjectures.ErdosProblems.«782»

/-! # Dietmann and Elsholtz's bound on Hilbert cubes in the squares

The proof follows R. Dietmann and C. Elsholtz, *Hilbert cubes in progression-free sets and in the set of squares II* (2012), and proves the needed square-sumset estimate of K. Gyarmati by quadratic-character orthogonality and the larger sieve. The Fermat descent is adapted with attribution and license below.
-/

/-!
Fermat's descent, adapted from Michael Piscitelli, Erdos672/NoFourSquaresInAP.lean,
https://github.com/herakles-dev/erdos672-four-squares-lean at be8bcb6ddb9f8c3dc43e3535a34b0d4f3075c6ed.
Only the dependency closure of no_four_squares_in_ap is retained; namespace changed.
SPDX-License-Identifier: Apache-2.0
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

   Copyright 2026 D. Michael Piscitelli

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

namespace OMA.Fermat782

private theorem eq_zero_of_sq_eq_two_mul_sq_nat :
    ∀ b : ℕ, ∀ a : ℕ, a ^ 2 = 2 * b ^ 2 → b = 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact hb
    · exfalso
      rcases Nat.even_or_odd a with hae | hao
      · obtain ⟨k, hk⟩ := hae
        have hb2 : b ^ 2 = 2 * k ^ 2 := by subst hk; nlinarith
        have hkb : k < b := by nlinarith [hb2, sq_nonneg k, hb]
        have hk0 := ih k hkb b hb2
        subst hk0; simp at hb2; omega
      · obtain ⟨k, hk⟩ := hao
        subst hk
        have hexp : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
        rw [hexp] at hab; omega

private theorem eq_zero_of_sq_eq_two_mul_sq (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : b = 0 := by
  have hnat : a.natAbs ^ 2 = 2 * b.natAbs ^ 2 := by
    have h1 : (a.natAbs : ℤ) ^ 2 = 2 * (b.natAbs : ℤ) ^ 2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]; exact h
    exact_mod_cast h1
  have := eq_zero_of_sq_eq_two_mul_sq_nat b.natAbs a.natAbs hnat
  simpa using this

private theorem fsap_three_dvd_of_sq_add_sq (a b : ℤ) (h : (3 : ℤ) ∣ a ^ 2 + b ^ 2) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b := by
  have key : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  have hz : ((a ^ 2 + b ^ 2 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  push_cast at hz
  obtain ⟨ha, hb⟩ := key _ _ hz
  constructor
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb

private theorem fsap_descent_core (x y a b : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : IsCoprime x y) (hab : IsCoprime a b) (hy2 : 2 ∣ y)
    (h1 : x ^ 2 - y ^ 2 = a ^ 2 - b ^ 2) (h2 : x * y = 2 * (a * b)) :
    ∃ X Y : ℤ, X ≠ 0 ∧ Y ≠ 0 ∧ IsCoprime X Y ∧ (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) ∧
      (∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) ∧ X.natAbs * Y.natAbs * 2 ≤ x.natAbs * y.natAbs := by
  obtain ⟨y', rfl⟩ := hy2
  have hy' : y' ≠ 0 := by rintro rfl; simp at hy
  have h2' : x * y' = a * b := by
    have : 2 * (x * y') = 2 * (a * b) := by linear_combination h2
    exact mul_left_cancel₀ two_ne_zero this
  have hxab : x ∣ a * b := Dvd.intro y' h2'
  obtain ⟨x₁, x₂, hx₁a, hx₂b, hx12⟩ := exists_dvd_and_dvd_of_dvd_mul hxab
  obtain ⟨y₁, hy₁⟩ := hx₁a
  obtain ⟨y₂, hy₂⟩ := hx₂b
  have hx₁ : x₁ ≠ 0 := by rintro rfl; simp at hx12; exact hx hx12
  have hx₂ : x₂ ≠ 0 := by rintro rfl; simp at hx12; exact hx hx12
  have hy12 : y' = y₁ * y₂ := by
    have : x₁ * x₂ * y' = x₁ * x₂ * (y₁ * y₂) := by
      rw [← hx12, h2', hy₁, hy₂, hx12]; ring
    exact mul_left_cancel₀ (mul_ne_zero hx₁ hx₂) this
  have hy₁ne : y₁ ≠ 0 := by rintro rfl; simp at hy12; exact hy' hy12
  have hy₂ne : y₂ ≠ 0 := by rintro rfl; simp at hy12; exact hy' hy12
  subst hx12 hy₁ hy₂ hy12
  have hkey : x₂ ^ 2 * (x₁ ^ 2 + y₂ ^ 2) = y₁ ^ 2 * (x₁ ^ 2 + 4 * y₂ ^ 2) := by
    linear_combination h1
  have hc21 : IsCoprime x₂ y₁ :=
    hxy.mono ⟨x₁, by ring⟩ ⟨2 * y₂, by ring⟩
  have hc12 : IsCoprime x₁ y₂ :=
    hab.mono ⟨y₁, by ring⟩ ⟨x₂, by ring⟩
  have hdvd : y₁ ^ 2 ∣ x₁ ^ 2 + y₂ ^ 2 :=
    (hc21.symm.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left (Dvd.intro _ hkey.symm)
  obtain ⟨k, hk⟩ := hdvd
  have hk' : x₁ ^ 2 + 4 * y₂ ^ 2 = x₂ ^ 2 * k := by
    have : y₁ ^ 2 * (x₁ ^ 2 + 4 * y₂ ^ 2) = y₁ ^ 2 * (x₂ ^ 2 * k) := by
      rw [← hkey, hk]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hy₁ne) this
  have hkpos : 0 < k := by
    have h1pos : 0 < x₁ ^ 2 + y₂ ^ 2 := by positivity
    by_contra hneg
    have : y₁ ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (not_lt.mp hneg)
    linarith
  have hk3 : k ∣ 3 := by
    obtain ⟨u, v, huv⟩ := hc12.pow (m := 2) (n := 2)
    exact ⟨u * (4 * y₁ ^ 2 - x₂ ^ 2) + v * (x₂ ^ 2 - y₁ ^ 2), by
      linear_combination (-3) * huv + (4 * u - v) * hk + (v - u) * hk'⟩
  have hkle : k ≤ 3 := Int.le_of_dvd (by norm_num) hk3
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  · refine ⟨x₁, y₂, hx₁, hy₂ne, hc12, ⟨y₁, by rw [hk]; ring⟩, ⟨x₂, by rw [hk']; ring⟩, ?_⟩
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
    have h2n : (2 : ℤ).natAbs = 2 := rfl
    rw [h2n]
    have hx₂p : 0 < x₂.natAbs := Int.natAbs_pos.mpr hx₂
    have hy₁p : 0 < y₁.natAbs := Int.natAbs_pos.mpr hy₁ne
    have e : x₁.natAbs * x₂.natAbs * (2 * (y₁.natAbs * y₂.natAbs)) =
        x₁.natAbs * y₂.natAbs * 2 * (x₂.natAbs * y₁.natAbs) := by ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hx₂p hy₁p)
  · exact absurd hk3 (by norm_num)
  · exfalso
    have h3 : (3 : ℤ) ∣ x₁ ^ 2 + y₂ ^ 2 := ⟨y₁ ^ 2, by rw [hk]; ring⟩
    obtain ⟨h3a, h3b⟩ := fsap_three_dvd_of_sq_add_sq x₁ y₂ h3
    have hu := hc12.isUnit_of_dvd' h3a h3b
    rw [Int.isUnit_iff] at hu
    omega

private theorem fsap_concordant_descent_odd (X Y : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXY : IsCoprime X Y) (hXodd : X % 2 = 1)
    (hZ : ∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) (hW : ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) :
    ∃ X' Y' : ℤ, X' ≠ 0 ∧ Y' ≠ 0 ∧ IsCoprime X' Y' ∧ (∃ Z, X' ^ 2 + Y' ^ 2 = Z ^ 2) ∧
      (∃ W, X' ^ 2 + 4 * Y' ^ 2 = W ^ 2) ∧ X'.natAbs * Y'.natAbs < X.natAbs * Y.natAbs := by
  obtain ⟨Z, hZ⟩ := hZ
  obtain ⟨W, hW⟩ := hW
  have hX2 : 0 < X ^ 2 := by positivity
  have hZpos : 0 < |Z| := by
    rw [abs_pos]; rintro rfl; nlinarith [sq_nonneg Y]
  have hPT1 : PythagoreanTriple X Y |Z| := by
    show X * X + Y * Y = |Z| * |Z|
    have : |Z| * |Z| = Z ^ 2 := by rw [← sq, sq_abs]
    rw [this, ← hZ]; ring
  obtain ⟨m, n, hXmn, hYmn, hZmn, hmn, hpar, hm0⟩ :=
    PythagoreanTriple.coprime_classification' hPT1 (Int.isCoprime_iff_gcd_eq_one.mp hXY) hXodd hZpos
  have hm : m ≠ 0 := by rintro rfl; simp at hYmn; exact hY hYmn
  have hn : n ≠ 0 := by rintro rfl; simp at hYmn; exact hY hYmn
  have hcmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have hWpos : 0 < |W| := by
    rw [abs_pos]; rintro rfl; nlinarith [sq_nonneg Y]
  have hPT2 : PythagoreanTriple (m ^ 2 - n ^ 2) (4 * m * n) |W| := by
    show (m ^ 2 - n ^ 2) * (m ^ 2 - n ^ 2) + (4 * m * n) * (4 * m * n) = |W| * |W|
    have : |W| * |W| = W ^ 2 := by rw [← sq, sq_abs]
    rw [this, ← hW, hXmn, hYmn]; ring
  have hX2' : IsCoprime X 2 := by
    obtain ⟨k, hk⟩ := Int.odd_iff.mpr hXodd
    exact ⟨1, -k, by rw [hk]; ring⟩
  have hcop2 : Int.gcd (m ^ 2 - n ^ 2) (4 * m * n) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    have hc4 : IsCoprime (m ^ 2 - n ^ 2) 4 := by
      rw [← hXmn]
      have := hX2'.pow_right (n := 2)
      norm_num at this
      exact this
    have hc1 : IsCoprime (m ^ 2 - n ^ 2) m := by
      have e : m ^ 2 - n ^ 2 = -n ^ 2 + m * m := by ring
      rw [e]; exact (hcmn.symm.pow_left (m := 2)).neg_left.add_mul_left_left m
    have hc2 : IsCoprime (m ^ 2 - n ^ 2) n := by
      have e : m ^ 2 - n ^ 2 = m ^ 2 + n * (-n) := by ring
      rw [e]; exact (hcmn.pow_left (m := 2)).add_mul_left_left (-n)
    exact (hc4.mul_right hc1).mul_right hc2
  have hpar2 : (m ^ 2 - n ^ 2) % 2 = 1 := by rw [← hXmn]; exact hXodd
  obtain ⟨a, b, hab1, hab2, hWab, hgab, hpar', ha0⟩ :=
    PythagoreanTriple.coprime_classification' hPT2 hcop2 hpar2 hWpos
  have hab : a * b = 2 * (m * n) := by linarith
  have hcab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hgab
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  have hab0 : a * b ≠ 0 := by rw [hab]; exact mul_ne_zero two_ne_zero hmn0
  have ha : a ≠ 0 := left_ne_zero_of_mul hab0
  have hb : b ≠ 0 := right_ne_zero_of_mul hab0
  have hcore : ∃ X' Y' : ℤ, X' ≠ 0 ∧ Y' ≠ 0 ∧ IsCoprime X' Y' ∧ (∃ Z, X' ^ 2 + Y' ^ 2 = Z ^ 2) ∧
      (∃ W, X' ^ 2 + 4 * Y' ^ 2 = W ^ 2) ∧ X'.natAbs * Y'.natAbs * 2 ≤ a.natAbs * b.natAbs := by
    rcases hpar' with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
    · obtain ⟨X', Y', h1, h2, h3, h4, h5, h6⟩ := fsap_descent_core b a n m hb ha hcab.symm
        hcmn.symm (Int.dvd_of_emod_eq_zero ha2) (by linear_combination hab1)
        (by linear_combination hab)
      exact ⟨X', Y', h1, h2, h3, h4, h5, by rw [mul_comm a.natAbs]; exact h6⟩
    · exact fsap_descent_core a b m n ha hb hcab hcmn (Int.dvd_of_emod_eq_zero hb2) hab1.symm hab
  obtain ⟨X', Y', h1, h2, h3, h4, h5, h6⟩ := hcore
  refine ⟨X', Y', h1, h2, h3, h4, h5, ?_⟩
  have habn : a.natAbs * b.natAbs = 2 * (m.natAbs * n.natAbs) := by
    have := congrArg Int.natAbs hab
    simpa [Int.natAbs_mul] using this
  have hYn : Y.natAbs = 2 * (m.natAbs * n.natAbs) := by
    rw [hYmn, Int.natAbs_mul, Int.natAbs_mul, mul_assoc]; rfl
  have hXpos : 0 < X.natAbs := Int.natAbs_pos.mpr hX
  have hmnpos : 0 < m.natAbs * n.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hm) (Int.natAbs_pos.mpr hn)
  rw [hYn]
  have : 2 * (m.natAbs * n.natAbs) ≤ X.natAbs * (2 * (m.natAbs * n.natAbs)) :=
    Nat.le_mul_of_pos_left _ hXpos
  omega

private theorem fsap_concordant_descent (X Y : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXY : IsCoprime X Y)
    (hZ : ∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) (hW : ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) :
    ∃ X' Y' : ℤ, X' ≠ 0 ∧ Y' ≠ 0 ∧ IsCoprime X' Y' ∧ (∃ Z, X' ^ 2 + Y' ^ 2 = Z ^ 2) ∧
      (∃ W, X' ^ 2 + 4 * Y' ^ 2 = W ^ 2) ∧ X'.natAbs * Y'.natAbs < X.natAbs * Y.natAbs := by
  rcases Int.even_or_odd X with hXe | hXo
  · obtain ⟨X₀, hX₀⟩ := hXe
    obtain ⟨Z, hZ⟩ := hZ
    obtain ⟨W, hW⟩ := hW
    have hX₀ne : X₀ ≠ 0 := by rintro rfl; simp at hX₀; exact hX hX₀
    have h2X : (2 : ℤ) ∣ X := ⟨X₀, by rw [hX₀]; ring⟩
    have hYo : Y % 2 = 1 := by
      rcases Int.even_or_odd Y with hYe | hYo
      · exfalso
        have hu := hXY.isUnit_of_dvd' h2X hYe.two_dvd
        rw [Int.isUnit_iff] at hu
        omega
      · exact Int.odd_iff.mp hYo
    have hWe : Even W := by
      have : Even (W ^ 2) := ⟨2 * X₀ ^ 2 + 2 * Y ^ 2, by rw [← hW, hX₀]; ring⟩
      exact (Int.even_pow' two_ne_zero).mp this
    obtain ⟨W₀, hW₀⟩ := hWe
    have hcop : IsCoprime Y X₀ := hXY.symm.of_isCoprime_of_dvd_right ⟨2, by rw [hX₀]; ring⟩
    have hZ' : ∃ Z, Y ^ 2 + X₀ ^ 2 = Z ^ 2 := by
      refine ⟨W₀, ?_⟩
      have h4 : 4 * (Y ^ 2 + X₀ ^ 2) = 4 * W₀ ^ 2 := by
        rw [hX₀, hW₀] at hW; linear_combination hW
      exact mul_left_cancel₀ (by norm_num) h4
    have hW' : ∃ W, Y ^ 2 + 4 * X₀ ^ 2 = W ^ 2 := ⟨Z, by rw [hX₀] at hZ; linear_combination hZ⟩
    obtain ⟨X', Y', h1, h2, h3, h4, h5, h6⟩ :=
      fsap_concordant_descent_odd Y X₀ hY hX₀ne hcop hYo hZ' hW'
    refine ⟨X', Y', h1, h2, h3, h4, h5, ?_⟩
    have hXn : X.natAbs = 2 * X₀.natAbs := by rw [hX₀]; omega
    rw [hXn]
    have e : 2 * X₀.natAbs * Y.natAbs = 2 * (Y.natAbs * X₀.natAbs) := by ring
    rw [e]; omega
  · exact fsap_concordant_descent_odd X Y hX hY hXY (Int.odd_iff.mp hXo) hZ hW

private theorem fsap_no_concordant_pair : ∀ N : ℕ, ∀ X Y : ℤ, X.natAbs * Y.natAbs = N →
    X ≠ 0 → Y ≠ 0 → IsCoprime X Y → (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) →
    (∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2) → False := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro X Y hN hX hY hXY hZ hW
    obtain ⟨X', Y', hX', hY', hXY', hZ', hW', hlt⟩ := fsap_concordant_descent X Y hX hY hXY hZ hW
    exact ih _ (hN ▸ hlt) X' Y' rfl hX' hY' hXY' hZ' hW'

private theorem fsap_four_ap_all_odd (r s t u : ℤ) (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2)
    (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) (hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1) :
    Odd r ∧ Odd s ∧ Odd t ∧ Odd u := by
  have hro : Odd r := by
    by_contra hre
    rw [Int.not_odd_iff_even] at hre
    obtain ⟨k, hk⟩ := hre
    have hr4 : r ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
    have ht2 : t ^ 2 % 2 = 0 := by omega
    have hte : Even t := (Int.even_pow' two_ne_zero).mp (Int.even_iff.mpr ht2)
    obtain ⟨l, hl⟩ := hte
    have ht4 : t ^ 2 = 4 * l ^ 2 := by rw [hl]; ring
    have hs2 : s ^ 2 % 2 = 0 := by omega
    have hse : Even s := (Int.even_pow' two_ne_zero).mp (Int.even_iff.mpr hs2)
    obtain ⟨j, hj⟩ := hse
    have hs4 : s ^ 2 = 4 * j ^ 2 := by rw [hj]; ring
    have hu2 : u ^ 2 % 2 = 0 := by omega
    have hue : Even u := (Int.even_pow' two_ne_zero).mp (Int.even_iff.mpr hu2)
    have h2r : (2 : ℤ) ∣ r := ⟨k, by rw [hk]; ring⟩
    have h2t : (2 : ℤ) ∣ t := ⟨l, by rw [hl]; ring⟩
    have h2s : (2 : ℤ) ∣ s := ⟨j, by rw [hj]; ring⟩
    have h2u : (2 : ℤ) ∣ u := hue.two_dvd
    have hg1 : (2 : ℕ) ∣ Int.gcd r s := Int.dvd_gcd (by exact_mod_cast h2r) (by exact_mod_cast h2s)
    have hg2 : (2 : ℕ) ∣ Int.gcd t u := Int.dvd_gcd (by exact_mod_cast h2t) (by exact_mod_cast h2u)
    have hg : (2 : ℕ) ∣ Int.gcd (Int.gcd r s : ℤ) (Int.gcd t u : ℤ) :=
      Int.dvd_gcd (Int.natCast_dvd_natCast.mpr hg1) (Int.natCast_dvd_natCast.mpr hg2)
    rw [hprim] at hg
    omega
  have hr2 : r ^ 2 % 2 = 1 := Int.odd_iff.mp hro.pow
  have hto : Odd t := by
    have : t ^ 2 % 2 = 1 := by omega
    exact (Int.odd_pow' two_ne_zero).mp (Int.odd_iff.mpr this)
  have hr4 : r ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hro
  have ht4 : t ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hto
  have hso : Odd s := by
    have : s ^ 2 % 2 = 1 := by omega
    exact (Int.odd_pow' two_ne_zero).mp (Int.odd_iff.mpr this)
  have hs2 : s ^ 2 % 2 = 1 := Int.odd_iff.mp hso.pow
  have huo : Odd u := by
    have : u ^ 2 % 2 = 1 := by omega
    exact (Int.odd_pow' two_ne_zero).mp (Int.odd_iff.mpr this)
  exact ⟨hro, hso, hto, huo⟩

private theorem fsap_four_ap_coprime (r s t u : ℤ) (hro : Odd r) (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2)
    (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) (hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1) :
    IsCoprime r t := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set d := Int.gcd r t with hd
  have hdr : (d : ℤ) ∣ r := Int.gcd_dvd_left r t
  have hdt : (d : ℤ) ∣ t := Int.gcd_dvd_right r t
  have hdo : Odd (d : ℤ) := by
    by_contra hde
    rw [Int.not_odd_iff_even] at hde
    have : Even r := even_iff_two_dvd.mpr (hde.two_dvd.trans hdr)
    exact (Int.not_even_iff_odd.mpr hro) this
  have hd2 : IsCoprime ((d : ℤ) ^ 2) 2 := by
    obtain ⟨k, hk⟩ := hdo
    have hd1 : IsCoprime (d : ℤ) 2 := ⟨1, -k, by rw [hk]; ring⟩
    exact hd1.pow_left
  have hd_s : (d : ℤ) ∣ s := by
    have h2s : (d : ℤ) ^ 2 ∣ 2 * s ^ 2 := by
      rw [← h1]; exact dvd_add (pow_dvd_pow_of_dvd hdr 2) (pow_dvd_pow_of_dvd hdt 2)
    have : (d : ℤ) ^ 2 ∣ s ^ 2 := hd2.dvd_of_dvd_mul_left h2s
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp this
  have hd_u : (d : ℤ) ∣ u := by
    have hu2 : u ^ 2 = 2 * t ^ 2 - s ^ 2 := by linarith
    have : (d : ℤ) ^ 2 ∣ u ^ 2 := by
      rw [hu2]
      exact dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdt 2) 2) (pow_dvd_pow_of_dvd hd_s 2)
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp this
  have hg1 : d ∣ Int.gcd r s := Int.dvd_gcd hdr hd_s
  have hg2 : d ∣ Int.gcd t u := Int.dvd_gcd hdt hd_u
  have hg : d ∣ Int.gcd (Int.gcd r s : ℤ) (Int.gcd t u : ℤ) :=
    Int.dvd_gcd (Int.natCast_dvd_natCast.mpr hg1) (Int.natCast_dvd_natCast.mpr hg2)
  rw [hprim] at hg
  exact Nat.dvd_one.mp hg

private theorem fsap_four_way_factor (P Q P' Q' : ℤ) (hP : P ≠ 0)
    (hPQ : IsCoprime P Q) (hP'Q' : IsCoprime P' Q') (h : P * Q = P' * Q') :
    ∃ g h p q : ℤ, P = g * p ∧ Q = h * q ∧ P' = g * q ∧ Q' = h * p ∧
      IsCoprime g h ∧ IsCoprime p q ∧ IsCoprime g p ∧ IsCoprime g q ∧
      IsCoprime h p ∧ IsCoprime h q := by
  have hdvd : P ∣ P' * Q' := Dvd.intro Q h
  obtain ⟨g, p, hgP', hpQ', hPgp⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
  obtain ⟨q, hq⟩ := hgP'
  obtain ⟨h', hh'⟩ := hpQ'
  have hg : g ≠ 0 := by rintro rfl; simp at hPgp; exact hP hPgp
  have hp : p ≠ 0 := by rintro rfl; simp at hPgp; exact hP hPgp
  have hQ' : Q = h' * q := by
    have : g * p * Q = g * p * (h' * q) := by rw [← hPgp, h, hq, hh', hPgp]; ring
    exact mul_left_cancel₀ (mul_ne_zero hg hp) this
  subst hPgp hq hh' hQ'
  refine ⟨g, h', p, q, rfl, rfl, rfl, by ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPQ.of_mul_left_left.of_mul_right_left
  · exact hPQ.of_mul_left_right.of_mul_right_right
  · exact hP'Q'.of_mul_left_left.of_mul_right_left
  · exact hPQ.of_mul_left_left.of_mul_right_right
  · exact hPQ.of_mul_left_right.of_mul_right_left.symm
  · exact hP'Q'.of_mul_left_right.of_mul_right_right.symm

private theorem fsap_concordant_of_params (X Y p q g h : ℤ) (hXsq : X ^ 2 = (g * h) ^ 2)
    (hYsq : Y ^ 2 = (p * q) ^ 2) (hA : (q ^ 2 - p ^ 2) ^ 2 = X ^ 2)
    (hB : (g ^ 2 - h ^ 2) ^ 2 = 4 * Y ^ 2) (heven : Even (g ^ 2 - h ^ 2)) :
    (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) ∧ ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2 := by
  obtain ⟨c, hc⟩ := heven
  have hZ : g ^ 2 + h ^ 2 = 2 * (c + h ^ 2) := by linarith
  refine ⟨⟨c + h ^ 2, ?_⟩, ⟨q ^ 2 + p ^ 2, ?_⟩⟩
  · have h4 : 4 * (X ^ 2 + Y ^ 2) = 4 * (c + h ^ 2) ^ 2 := by
      linear_combination 4 * hXsq - hB + (g ^ 2 + h ^ 2 + 2 * (c + h ^ 2)) * hZ
    exact mul_left_cancel₀ (by norm_num) h4
  · linear_combination -hA + 4 * hYsq

private theorem fsap_concordant_of_four_params (g h p q : ℤ) (hg : g ≠ 0) (hh : h ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hgh : IsCoprime g h) (hpq : IsCoprime p q) (hgp : IsCoprime g p) (hgq : IsCoprime g q)
    (hhp : IsCoprime h p) (hhq : IsCoprime h q)
    (key : 2 * (g * h * p * q) = (g ^ 2 - h ^ 2) * (q ^ 2 - p ^ 2)) :
    ∃ X Y : ℤ, X ≠ 0 ∧ Y ≠ 0 ∧ IsCoprime X Y ∧ (∃ Z, X ^ 2 + Y ^ 2 = Z ^ 2) ∧
      ∃ W, X ^ 2 + 4 * Y ^ 2 = W ^ 2 := by
  have hc1 : IsCoprime (g * h) (g ^ 2 - h ^ 2) := by
    have e : g ^ 2 - h ^ 2 = -h ^ 2 + g * g := by ring
    have e' : g ^ 2 - h ^ 2 = g ^ 2 + h * (-h) := by ring
    apply IsCoprime.mul_left
    · rw [e]; exact (hgh.pow_right (n := 2)).neg_right.add_mul_left_right g
    · rw [e']; exact (hgh.symm.pow_right (n := 2)).add_mul_left_right (-h)
  have hc2 : IsCoprime (p * q) (q ^ 2 - p ^ 2) := by
    have e : q ^ 2 - p ^ 2 = q ^ 2 + p * (-p) := by ring
    have e' : q ^ 2 - p ^ 2 = -p ^ 2 + q * q := by ring
    apply IsCoprime.mul_left
    · rw [e]; exact (hpq.pow_right (n := 2)).add_mul_left_right (-p)
    · rw [e']; exact (hpq.symm.pow_right (n := 2)).neg_right.add_mul_left_right q
  have hd1 : g * h ∣ q ^ 2 - p ^ 2 :=
    hc1.dvd_of_dvd_mul_left (Dvd.intro (2 * (p * q)) (by linear_combination key))
  have hd2 : p * q ∣ g ^ 2 - h ^ 2 :=
    hc2.dvd_of_dvd_mul_left (Dvd.intro (2 * (g * h)) (by linear_combination key))
  obtain ⟨A, hA⟩ := hd1
  obtain ⟨B, hB⟩ := hd2
  have hne : g * h * p * q ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hg hh) hp) hq
  have hAB : A * B = 2 := by
    have : g * h * p * q * (A * B) = g * h * p * q * 2 := by
      rw [hA, hB] at key; linear_combination -key
    exact mul_left_cancel₀ hne this
  have hABn : A.natAbs * B.natAbs = 2 := by
    have := congrArg Int.natAbs hAB
    rwa [Int.natAbs_mul] at this
  have hAn : A.natAbs = 1 ∨ A.natAbs = 2 := by
    have hdv : A.natAbs ∣ 2 := Dvd.intro _ hABn
    have h2 := Nat.le_of_dvd (by norm_num) hdv
    have h0 : A.natAbs ≠ 0 := by intro h0; rw [h0] at hABn; simp at hABn
    omega
  have hA2 : A ^ 2 = (A.natAbs : ℤ) ^ 2 := (Int.natAbs_sq A).symm
  have hB2 : B ^ 2 = (B.natAbs : ℤ) ^ 2 := (Int.natAbs_sq B).symm
  have hXY : IsCoprime (g * h) (p * q) := (hgp.mul_right hgq).mul_left (hhp.mul_right hhq)
  rcases hAn with hA1 | hA1
  · have hB1 : B.natAbs = 2 := by rw [hA1] at hABn; omega
    have hA2' : A ^ 2 = 1 := by rw [hA2, hA1]; norm_num
    have hB2' : B ^ 2 = 4 := by rw [hB2, hB1]; norm_num
    have hBeven : Even (g ^ 2 - h ^ 2) := by
      have : B = 2 ∨ B = -2 := by omega
      rcases this with rfl | rfl
      · exact ⟨p * q, by rw [hB]; ring⟩
      · exact ⟨-(p * q), by rw [hB]; ring⟩
    refine ⟨g * h, p * q, mul_ne_zero hg hh, mul_ne_zero hp hq, hXY, ?_⟩
    exact fsap_concordant_of_params (g * h) (p * q) p q g h rfl rfl
      (by rw [hA]; linear_combination (g * h) ^ 2 * hA2')
      (by rw [hB]; linear_combination (p * q) ^ 2 * hB2') hBeven
  · have hB1 : B.natAbs = 1 := by rw [hA1] at hABn; omega
    have hA2' : A ^ 2 = 4 := by rw [hA2, hA1]; norm_num
    have hB2' : B ^ 2 = 1 := by rw [hB2, hB1]; norm_num
    have hAeven : Even (q ^ 2 - p ^ 2) := by
      have : A = 2 ∨ A = -2 := by omega
      rcases this with rfl | rfl
      · exact ⟨g * h, by rw [hA]; ring⟩
      · exact ⟨-(g * h), by rw [hA]; ring⟩
    refine ⟨p * q, g * h, mul_ne_zero hp hq, mul_ne_zero hg hh, hXY.symm, ?_⟩
    exact fsap_concordant_of_params (p * q) (g * h) h g q p (by ring) (by ring)
      (by rw [hB]; linear_combination (p * q) ^ 2 * hB2')
      (by rw [hA]; linear_combination (g * h) ^ 2 * hA2') hAeven

private theorem four_squares_ap_descent_step_primitive (r s t u : ℤ)
    (hr : 0 < r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2) (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2)
    (hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1) :
    ∃ r' s' t' u' : ℤ, 0 < r' ∧ r' < s' ∧ s' < t' ∧ t' < u' ∧
      r' ^ 2 + t' ^ 2 = 2 * s' ^ 2 ∧ s' ^ 2 + u' ^ 2 = 2 * t' ^ 2 ∧
      u'.natAbs < u.natAbs := by
  exfalso
  obtain ⟨hro, hso, hto, huo⟩ := fsap_four_ap_all_odd r s t u h1 h2 hprim
  have hcrt : IsCoprime r t := fsap_four_ap_coprime r s t u hro h1 h2 hprim
  have hcsu : IsCoprime s u := by
    have hprim' : Int.gcd (Int.gcd u t) (Int.gcd s r) = 1 := by
      rw [Int.gcd_comm u t, Int.gcd_comm s r, Int.gcd_comm]; exact hprim
    exact (fsap_four_ap_coprime u t s r huo (by linear_combination h2) (by linear_combination h1)
      hprim').symm
  obtain ⟨P, hP⟩ : Even (t + r) := hto.add_odd hro
  obtain ⟨Q, hQ⟩ : Even (t - r) := hto.sub_odd hro
  obtain ⟨P', hP'⟩ : Even (u + s) := huo.add_odd hso
  obtain ⟨Q', hQ'⟩ : Even (u - s) := huo.sub_odd hso
  have ht : t = P + Q := by linarith
  have hrPQ : r = P - Q := by linarith
  have hu : u = P' + Q' := by linarith
  have hs : s = P' - Q' := by linarith
  subst ht hrPQ hu hs
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hP'pos : 0 < P' := by linarith
  have hQ'pos : 0 < Q' := by linarith
  have hcPQ : IsCoprime P Q := by
    obtain ⟨a, b, hab⟩ := hcrt
    exact ⟨a + b, b - a, by linear_combination hab⟩
  have hcP'Q' : IsCoprime P' Q' := by
    obtain ⟨a, b, hab⟩ := hcsu
    exact ⟨a + b, b - a, by linear_combination hab⟩
  have hprod : P * Q = P' * Q' := by
    have : 4 * (P * Q) = 4 * (P' * Q') := by linear_combination -h1 - h2
    exact mul_left_cancel₀ (by norm_num) this
  obtain ⟨g, h, p, q, hPg, hQh, hP'g, hQ'h, hgh, hpq, hgp, hgq, hhp, hhq⟩ :=
    fsap_four_way_factor P Q P' Q' hPpos.ne' hcPQ hcP'Q' hprod
  have hg : g ≠ 0 := by rintro rfl; simp at hPg; exact hPpos.ne' hPg
  have hp : p ≠ 0 := by rintro rfl; simp at hPg; exact hPpos.ne' hPg
  have hh : h ≠ 0 := by rintro rfl; simp at hQh; exact hQpos.ne' hQh
  have hq : q ≠ 0 := by rintro rfl; simp at hQh; exact hQpos.ne' hQh
  have key : 2 * (g * h * p * q) = (g ^ 2 - h ^ 2) * (q ^ 2 - p ^ 2) := by
    subst hPg hQh hP'g hQ'h
    have : 2 * (2 * (g * h * p * q)) = 2 * ((g ^ 2 - h ^ 2) * (q ^ 2 - p ^ 2)) := by
      linear_combination -h2
    exact mul_left_cancel₀ two_ne_zero this
  obtain ⟨X, Y, hX, hY, hXY, hZ, hW⟩ :=
    fsap_concordant_of_four_params g h p q hg hh hp hq hgh hpq hgp hgq hhp hhq key
  exact fsap_no_concordant_pair _ X Y rfl hX hY hXY hZ hW

private theorem four_squares_ap_descent_step (r s t u : ℤ)
    (hr : 0 < r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2) (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) :
    ∃ r' s' t' u' : ℤ, 0 < r' ∧ r' < s' ∧ s' < t' ∧ t' < u' ∧
      r' ^ 2 + t' ^ 2 = 2 * s' ^ 2 ∧ s' ^ 2 + u' ^ 2 = 2 * t' ^ 2 ∧
      u'.natAbs < u.natAbs := by
  by_cases hprim : Int.gcd (Int.gcd r s) (Int.gcd t u) = 1
  · -- Primitive configuration: the genuine Fermat descent.
    exact four_squares_ap_descent_step_primitive r s t u hr hrs hst htu h1 h2 hprim
  · -- Non-primitive: divide out `g := gcd (gcd r s) (gcd t u) ≥ 2`. The two relations are
    -- homogeneous of degree 2, so they persist; ordering and positivity persist; and the largest
    -- root strictly shrinks.
    have hrs_ne : Int.gcd r s ≠ 0 := by
      intro h; rw [Int.gcd_eq_zero_iff] at h; exact (ne_of_gt hr) h.1
    have hg_ne : Int.gcd (Int.gcd r s) (Int.gcd t u) ≠ 0 := by
      intro h; rw [Int.gcd_eq_zero_iff] at h; exact hrs_ne (by exact_mod_cast h.1)
    have hg_ge2 : 2 ≤ Int.gcd (Int.gcd r s) (Int.gcd t u) := by omega
    have hgz_pos : (0 : ℤ) < (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) := by
      exact_mod_cast (by omega : 0 < Int.gcd (Int.gcd r s) (Int.gcd t u))
    have hgz_ge2 : (2 : ℤ) ≤ (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) := by exact_mod_cast hg_ge2
    -- Divisibility of all four by `g`.
    have hdvd_r : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ r :=
      (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left r s)
    have hdvd_s : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ s :=
      (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right r s)
    have hdvd_t : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ t :=
      (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left t u)
    have hdvd_u : (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) ∣ u :=
      (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right t u)
    obtain ⟨r0, hr0⟩ := hdvd_r
    obtain ⟨s0, hs0⟩ := hdvd_s
    obtain ⟨t0, ht0⟩ := hdvd_t
    obtain ⟨u0, hu0⟩ := hdvd_u
    set g : ℤ := (Int.gcd (Int.gcd r s) (Int.gcd t u) : ℤ) with hg_def
    -- Positivity of the reduced roots.
    have hr0pos : 0 < r0 := by
      rcases mul_pos_iff.mp (hr0 ▸ hr : 0 < g * r0) with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h (not_lt.mpr (le_of_lt hgz_pos))
    -- Ordering of the reduced roots.
    have hr0s0 : r0 < s0 :=
      lt_of_mul_lt_mul_left (by rw [← hr0, ← hs0]; exact hrs) (le_of_lt hgz_pos)
    have hs0t0 : s0 < t0 :=
      lt_of_mul_lt_mul_left (by rw [← hs0, ← ht0]; exact hst) (le_of_lt hgz_pos)
    have ht0u0 : t0 < u0 :=
      lt_of_mul_lt_mul_left (by rw [← ht0, ← hu0]; exact htu) (le_of_lt hgz_pos)
    -- The two relations persist (cancel `g²`).
    have hgsq_ne : g ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hgz_pos)
    have h1' : r0 ^ 2 + t0 ^ 2 = 2 * s0 ^ 2 := by
      have hsub : (g * r0) ^ 2 + (g * t0) ^ 2 = 2 * (g * s0) ^ 2 := by
        rw [← hr0, ← ht0, ← hs0]; exact h1
      have hg2 : g ^ 2 * (r0 ^ 2 + t0 ^ 2) = g ^ 2 * (2 * s0 ^ 2) := by linear_combination hsub
      exact mul_left_cancel₀ hgsq_ne hg2
    have h2' : s0 ^ 2 + u0 ^ 2 = 2 * t0 ^ 2 := by
      have hsub : (g * s0) ^ 2 + (g * u0) ^ 2 = 2 * (g * t0) ^ 2 := by
        rw [← hs0, ← hu0, ← ht0]; exact h2
      have hg2 : g ^ 2 * (s0 ^ 2 + u0 ^ 2) = g ^ 2 * (2 * t0 ^ 2) := by linear_combination hsub
      exact mul_left_cancel₀ hgsq_ne hg2
    -- The largest root strictly shrinks.
    have hu0pos : 0 < u0 := lt_trans hr0pos (lt_trans hr0s0 (lt_trans hs0t0 ht0u0))
    have hu0_lt_u : u0 < u := by
      rw [hu0]; nlinarith [hgz_ge2, hu0pos, mul_le_mul_of_nonneg_right hgz_ge2 (le_of_lt hu0pos)]
    have hshrink : u0.natAbs < u.natAbs := by
      rw [Int.natAbs_lt_iff_sq_lt]; nlinarith [hu0pos, hu0_lt_u]
    exact ⟨r0, s0, t0, u0, hr0pos, hr0s0, hs0t0, ht0u0, h1', h2', hshrink⟩

theorem four_squares_ap_descent (r s t u : ℤ)
    (hr : 0 < r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (h1 : r ^ 2 + t ^ 2 = 2 * s ^ 2) (h2 : s ^ 2 + u ^ 2 = 2 * t ^ 2) : False := by
  suffices H : ∀ N : ℕ, ∀ r s t u : ℤ, u.natAbs = N →
      0 < r → r < s → s < t → t < u →
      r ^ 2 + t ^ 2 = 2 * s ^ 2 → s ^ 2 + u ^ 2 = 2 * t ^ 2 → False by
    exact H u.natAbs r s t u rfl hr hrs hst htu h1 h2
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro r s t u hN hr hrs hst htu h1 h2
    obtain ⟨r', s', t', u', hr', hrs', hst', htu', h1', h2', hlt⟩ :=
      four_squares_ap_descent_step r s t u hr hrs hst htu h1 h2
    exact ih u'.natAbs (hN ▸ hlt) r' s' t' u' rfl hr' hrs' hst' htu' h1' h2'

private theorem no_four_squares_in_ap_pos (r s t u D : ℤ) (hD : 0 < D)
    (h1 : s ^ 2 = r ^ 2 + D) (h2 : t ^ 2 = s ^ 2 + D) (h3 : u ^ 2 = t ^ 2 + D) : False := by
  have c1 : r ^ 2 + t ^ 2 = 2 * s ^ 2 := by linarith
  have c2 : s ^ 2 + u ^ 2 = 2 * t ^ 2 := by linarith
  have hsq_rs : r ^ 2 < s ^ 2 := by linarith
  have hsq_st : s ^ 2 < t ^ 2 := by linarith
  have hsq_tu : t ^ 2 < u ^ 2 := by linarith
  set R := (r.natAbs : ℤ) with hRdef
  set S := (s.natAbs : ℤ) with hSdef
  set T := (t.natAbs : ℤ) with hTdef
  set U := (u.natAbs : ℤ) with hUdef
  have hRsq : R ^ 2 = r ^ 2 := by rw [hRdef, Int.natAbs_sq]
  have hSsq : S ^ 2 = s ^ 2 := by rw [hSdef, Int.natAbs_sq]
  have hTsq : T ^ 2 = t ^ 2 := by rw [hTdef, Int.natAbs_sq]
  have hUsq : U ^ 2 = u ^ 2 := by rw [hUdef, Int.natAbs_sq]
  have hRnn : 0 ≤ R := by positivity
  have hSnn : 0 ≤ S := by positivity
  have hTnn : 0 ≤ T := by positivity
  have hUnn : 0 ≤ U := by positivity
  have hRS : R < S := by nlinarith [hRsq, hSsq, hsq_rs, hRnn, hSnn]
  have hST : S < T := by nlinarith [hSsq, hTsq, hsq_st, hSnn, hTnn]
  have hTU : T < U := by nlinarith [hTsq, hUsq, hsq_tu, hTnn, hUnn]
  have hRpos : 0 < R := by
    rcases lt_or_eq_of_le hRnn with h | h
    · exact h
    · exfalso
      have hr0 : r ^ 2 = 0 := by rw [← hRsq, ← h]; ring
      have hs2 : s ^ 2 = D := by linarith
      have ht2 : t ^ 2 = 2 * s ^ 2 := by linarith
      have hs0 := eq_zero_of_sq_eq_two_mul_sq t s ht2
      rw [hs0] at hs2; simp at hs2; omega
  have c1' : R ^ 2 + T ^ 2 = 2 * S ^ 2 := by rw [hRsq, hTsq, hSsq]; exact c1
  have c2' : S ^ 2 + U ^ 2 = 2 * T ^ 2 := by rw [hSsq, hUsq, hTsq]; exact c2
  exact four_squares_ap_descent R S T U hRpos hRS hST hTU c1' c2'

theorem no_four_squares_in_ap (r s t u D : ℤ) (hD : D ≠ 0)
    (h1 : s ^ 2 = r ^ 2 + D) (h2 : t ^ 2 = s ^ 2 + D) (h3 : u ^ 2 = t ^ 2 + D) : False := by
  rcases lt_trichotomy D 0 with hneg | hzero | hpos
  · -- `D < 0`: `u², t², s², r²` is an AP with positive common difference `-D`.
    exact no_four_squares_in_ap_pos u t s r (-D) (by linarith)
      (by linarith) (by linarith) (by linarith)
  · exact hD hzero
  · exact no_four_squares_in_ap_pos r s t u D hpos h1 h2 h3

end OMA.Fermat782

open Finset
namespace OMA.Quadratic782

variable {p : ℕ} [Fact p.Prime]

/-- Distinct translates of the quadratic character have inner product -1. -/
theorem cross (hp : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    ∑ x : ZMod p, (quadraticChar (ZMod p)) (x+a) * (quadraticChar (ZMod p)) (x+b) = -1 := by
  classical
  let e := (((Equiv.addRight b).trans (Equiv.inv (ZMod p))).trans
      (Equiv.mulLeft₀ (a-b) (sub_ne_zero.mpr hab))).trans (Equiv.addLeft 1)
  have hprod (x : ZMod p) :
      (quadraticChar (ZMod p)) (e x) = (quadraticChar (ZMod p)) (x+a) * (quadraticChar (ZMod p)) (x+b) + (if x = -b then 1 else 0) := by
    change (quadraticChar (ZMod p)) (1 + (a-b) * (x+b)⁻¹) = _
    by_cases h : x = -b
    · subst x; simp
    · rw [if_neg h, add_zero]
      have hn : x+b ≠ 0 := fun h' => h (eq_neg_of_add_eq_zero_left h')
      have he : 1+(a-b)*(x+b)⁻¹ = (x+a)*(x+b)⁻¹ := by
        field_simp; ring
      rw [he, map_mul]
      congr 1
      have hi := map_mul (quadraticChar (ZMod p)) (x+b)⁻¹ (x+b)
      rw [inv_mul_cancel₀ hn, map_one] at hi
      have hs := quadraticChar_sq_one hn
      rcases sq_eq_one_iff.mp hs with h1 | h1 <;> rw [h1] at hi ⊢ <;> linarith
  have he := e.sum_comp (fun z => (quadraticChar (ZMod p)) z)
  simp_rw [hprod] at he
  rw [sum_add_distrib, quadraticChar_sum_zero (by rwa [ZMod.ringChar_zmod_n])] at he
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  omega

theorem diag (a : ZMod p) : ∑ x : ZMod p, (quadraticChar (ZMod p)) (x+a)*(quadraticChar (ZMod p)) (x+a) ≤ p := by
  classical
  calc
    _ ≤ ∑ _x : ZMod p, (1:ℤ) := sum_le_sum fun x _ => by
      by_cases h : x+a = 0
      · simp [h]
      · rw [← sq, quadraticChar_sq_one h]
    _ = _ := by simp [ZMod.card]

/-- Orthogonality of the translates bounds the second moment for any finite set. -/
theorem energy (hp : p ≠ 2) (B : Finset (ZMod p)) :
    (∑ x : ZMod p, (∑ b ∈ B, (quadraticChar (ZMod p)) (x+b))^2) ≤ (p:ℤ) * B.card := by
  classical
  calc
    _ = ∑ a ∈ B, ∑ b ∈ B, ∑ x : ZMod p, (quadraticChar (ZMod p)) (x+a)*(quadraticChar (ZMod p)) (x+b) := by
      simp_rw [pow_two, sum_mul, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ ≤ ∑ a ∈ B, ∑ b ∈ B, (if a = b then (p:ℤ) else 0) := by
      apply sum_le_sum; intro a _
      apply sum_le_sum; intro b _
      split_ifs with h
      · subst b; exact diag a
      · rw [cross hp h]; decide
    _ = _ := by simp [mul_comm]

theorem row (B : Finset (ZMod p)) (x : ZMod p) (hs : ∀ b ∈ B, IsSquare (x+b)) :
    (B.card:ℤ) - 1 ≤ ∑ b ∈ B, (quadraticChar (ZMod p)) (x+b) := by
  classical
  have he (b : ZMod p) (hb : b ∈ B) :
      (quadraticChar (ZMod p)) (x+b) = 1 - (if -x = b then 1 else 0) := by
    split_ifs with h
    · subst b; simp
    · have hn : x+b ≠ 0 := fun h' => h (neg_eq_of_add_eq_zero_left (add_comm x b ▸ h'))
      simpa using (quadraticChar_one_iff_isSquare hn).mpr (hs b hb)
  rw [sum_congr rfl he, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one, sum_ite_eq]
  split_ifs <;> omega

theorem field_bound (A B : Finset (ZMod p)) (hs : ∀ a ∈ A, ∀ b ∈ B, IsSquare (a+b))
    (q : ℕ) (hq : 2 ≤ q) (hp : p ≠ 2) (hpq : p ≤ q^2) :
    min A.card B.card ≤ 2*q := by
  classical
  by_contra! hn
  obtain ⟨C,hCA,hC⟩ := exists_subset_card_eq (show 2*q+1 ≤ A.card by omega)
  obtain ⟨D,hDB,hD⟩ := exists_subset_card_eq (show 2*q+1 ≤ B.card by omega)
  have lower : ∑ _x ∈ C, ((2*q:ℤ)^2) ≤ ∑ x ∈ C, (∑ b ∈ D, (quadraticChar (ZMod p)) (x+b))^2 := by
    apply sum_le_sum; intro x hx
    have hr := row D x (fun b hb => hs x (hCA hx) b (hDB hb))
    rw [hD] at hr; push_cast at hr
    nlinarith
  have hsub : (∑ x ∈ C, (∑ b ∈ D, (quadraticChar (ZMod p)) (x+b))^2) ≤ ∑ x : ZMod p, (∑ b ∈ D, (quadraticChar (ZMod p)) (x+b))^2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => sq_nonneg _)
  have hh := lower.trans (hsub.trans (energy hp D))
  simp [hC,hD] at hh
  have hq' : (2:ℤ) ≤ q := by exact_mod_cast hq
  have hpq' : (p:ℤ) ≤ (q:ℤ)^2 := by exact_mod_cast hpq
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq') (show (0:ℤ) ≤ 2*q+1 by positivity),
             mul_nonneg (sq_nonneg (q:ℤ)) (show (0:ℤ) ≤ q by positivity)]

theorem residues (A B : Finset ℕ) (hs : ∀ a ∈ A, ∀ b ∈ B, IsSquare (a+b))
    (q p : ℕ) (hq : 2 ≤ q) (hp : p.Prime) (ho : p ≠ 2) (hpq : p ≤ q^2) :
    min (A.image (· % p)).card (B.image (· % p)).card ≤ 2*q := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let project (S : Finset ℕ) := S.image (fun n : ℕ => (n : ZMod p))
  have card (S : Finset ℕ) : (S.image (· % p)).card = (project S).card := by
    change _ = (S.image (fun n : ℕ => (n : ZMod p))).card
    rw [← card_image_of_injective (S.image (fun n : ℕ => (n : ZMod p))) (ZMod.val_injective p),
      Finset.image_image]
    simp [Function.comp_def, ZMod.val_natCast]
  rw [card, card]
  apply field_bound (project A) (project B) _ q hq ho hpq
  rintro x hx y hy
  change x ∈ A.image (fun n : ℕ => (n:ZMod p)) at hx
  change y ∈ B.image (fun n : ℕ => (n:ZMod p)) at hy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨c,hc⟩ := hs a ha b hb
  exact ⟨(c:ZMod p), by exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) hc⟩

end OMA.Quadratic782

/-! Growth and bisection of a Hilbert cube in the squares, following Dietmann–Elsholtz.
At a new generator of size t the preceding cube has no three consecutive terms of a
t-progression; otherwise its union with its translate would have all four. -/
namespace OMA.Growth782
open Finset Filter

def shifts (X : Finset ℤ) (t : ℤ) := X.image (· + t)

private lemma mem_shift {X : Finset ℤ} {t z : ℤ} : z ∈ shifts X t ↔ z-t ∈ X := by
  constructor
  · rintro h; obtain ⟨a,ha,rfl⟩ := mem_image.mp h; simpa using ha
  · intro h; exact mem_image.mpr ⟨z-t,h,by omega⟩

private lemma card_shift (X : Finset ℤ) (t : ℤ) : (shifts X t).card = X.card :=
  card_image_of_injective _ (fun _ _ h => add_right_cancel h)

private def Free (X : Finset ℤ) : Prop := ∀ z t : ℤ, 0<t →
  z∈X → z+t∈X → z+2*t∈X → z+3*t∈X → False

private lemma grow (X : Finset ℤ) (t : ℤ) (ht : 0<t) (h : Free (X ∪ shifts X t)) :
    3*X.card ≤ 2*(X ∪ shifts X t).card := by
  let I := X ∩ shifts X t
  have subset : I ∪ shifts I (-t) ⊆ X := by
    intro a ha
    rcases mem_union.mp ha with ha|ha
    · exact (mem_inter.mp ha).1
    · have hb := (mem_inter.mp (mem_shift.mp ha)).2
      exact (show a- -t-t = a by omega) ▸ mem_shift.mp hb
  have dis : Disjoint I (shifts I (-t)) := by
    apply disjoint_left.mpr
    intro a ha hb
    have a0 := mem_shift.mp (mem_inter.mp ha).2
    have a1 := (mem_inter.mp ha).1
    have a2 : a+t ∈ X := by simpa using (mem_inter.mp (mem_shift.mp hb)).1
    apply h (a-t) t ht (mem_union_left _ a0)
      (mem_union_left _ (by convert a1 using 1; omega))
      (mem_union_left _ (by convert a2 using 1; omega))
    exact mem_union_right _ (mem_shift.mpr (by convert a2 using 1; omega))
  have size := card_le_card subset
  rw [card_union_of_disjoint dis,card_shift] at size
  have comb := card_union_add_card_inter X (shifts X t)
  rw [card_shift] at comb
  dsimp only [I] at size
  omega

def cube {ι : Type*} [DecidableEq ι] (I : Finset ι) (a : ℤ) (b : ι → ℤ) : Finset ℤ :=
  I.powerset.image (fun J => a + ∑ i ∈ J, b i)

private lemma mem_cube {ι : Type*} [DecidableEq ι] {I : Finset ι} {a z : ℤ} {b : ι → ℤ} :
    z ∈ cube I a b ↔ ∃ J ⊆ I, z = a + ∑ i ∈ J, b i := by
  simp [cube,eq_comm]

private lemma cube_insert {ι : Type*} [DecidableEq ι] (I : Finset ι) (j : ι)
    (hj : j∉I) (a : ℤ) (b : ι → ℤ) :
    cube (insert j I) a b = cube I a b ∪ shifts (cube I a b) (b j) := by
  ext z
  rw [mem_union,mem_shift,mem_cube,mem_cube,mem_cube]
  constructor
  · rintro ⟨J,hJ,rfl⟩
    by_cases h : j∈J
    · right
      refine ⟨J.erase j, ?_, ?_⟩
      · intro i hi
        exact (mem_insert.mp (hJ (mem_of_mem_erase hi))).resolve_left (ne_of_mem_erase hi)
      · have hh := sum_erase_add J b h
        omega
    · left
      refine ⟨J,?_,rfl⟩
      intro i hi
      exact (mem_insert.mp (hJ hi)).resolve_left (fun e => h (e ▸ hi))
  · rintro (⟨J,hJ,rfl⟩|⟨J,hJ,e⟩)
    · exact ⟨J,hJ.trans (subset_insert ..),rfl⟩
    · refine ⟨insert j J, insert_subset_insert _ hJ, ?_⟩
      rw [sum_insert (fun hj' => hj (hJ hj'))]
      omega

private theorem exponential {ι : Type*} [DecidableEq ι] (I : Finset ι) (a : ℤ)
    (b : ι → ℤ) (hb : ∀ i,0<b i) (hf : Free (cube I a b)) :
    (3/2 : ℝ)^I.card ≤ (cube I a b).card := by
  induction I using Finset.induction_on with
  | empty => simp [cube]
  | insert j I hj ih =>
    rw [cube_insert _ _ hj] at hf ⊢
    have old : Free (cube I a b) := fun z t ht h0 h1 h2 h3 =>
      hf z t ht (mem_union_left _ h0) (mem_union_left _ h1) (mem_union_left _ h2) (mem_union_left _ h3)
    have hh := ih old
    have bound : 3*((cube I a b).card:ℝ) ≤ 2*((cube I a b ∪ shifts (cube I a b) (b j)).card:ℝ) := by
      exact_mod_cast grow (cube I a b) (b j) (hb j) hf
    rw [card_insert_of_notMem hj,pow_succ]
    linarith

def NoFour : Prop := ∀ x t : ℤ, 0<t → IsSquare x → IsSquare (x+t) →
  IsSquare (x+2*t) → IsSquare (x+3*t) → False

theorem noFour_of_catalogue (f : Set.IsAPOfLengthFree {n : ℕ | IsSquare n} 4) : NoFour := by
  intro x t ht h0 h1 h2 h3
  have hx : 0≤x := by obtain ⟨w,rfl⟩ := h0; exact mul_self_nonneg _
  lift x to ℕ using hx
  lift t to ℕ using ht.le
  have pos : 0<t := by exact_mod_cast ht
  let u (i : ℕ) := x+i*t
  have sqs (i : ℕ) (hi : i<4) : IsSquare (u i) := by
    interval_cases i
    · simpa [u] using (show IsSquare x by exact_mod_cast h0)
    · simpa [u] using (show IsSquare (x+t) by exact_mod_cast h1)
    · exact_mod_cast h2
    · exact_mod_cast h3
  have inj : Function.Injective u := fun i j e => Nat.eq_of_mul_eq_mul_right pos (Nat.add_left_cancel e)
  let S := (range 4).image u
  have hcard : S.card = 4 := by simp [S,card_image_of_injective _ inj]
  have square : (↑S : Set ℕ) ⊆ {n : ℕ | IsSquare n} := by
    intros z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    exact sqs i (mem_range.mp hi)
  have ap : (↑S : Set ℕ).IsAPOfLength 4 := by
    refine ⟨x,t,?_,?_⟩
    · simpa using congrArg (fun a : ℕ => (a:ℕ∞)) hcard
    · ext z
      constructor
      · intro hz
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
        exact ⟨i,by exact_mod_cast mem_range.mp hi,rfl⟩
      · rintro ⟨i,hi,rfl⟩
        exact mem_image.mpr ⟨i,mem_range.mpr (by exact_mod_cast hi),rfl⟩
  exact (by decide : ¬ (4:ℕ∞)≤1) (f _ square ap)

def LogBound : Prop := ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ A B : Finset ℕ,
  (∀ a∈A,a≤N) → (∀ b∈B,b≤N) → (∀ a∈A,∀ b∈B, IsSquare (a+b)) →
  ((min A.card B.card : ℕ):ℝ) ≤ C*Real.log N

theorem upper_nat (no4 : NoFour) (hbnd : LogBound) :
    type_of% @Erdos782.erdos_782.variants.dietmann_elsholtz := by
  obtain ⟨C,hC,hN⟩ := hbnd
  have tend : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have big := tend.eventually_ge_atTop (6*Real.log C+1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.1 ((hN.and big).and (eventually_ge_atTop 2))
  refine ⟨N₀,?_⟩
  intro N hn d a b ha _ pos full
  obtain ⟨⟨bound,large⟩,hn2⟩ := hN₀ N hn
  obtain ⟨S,hsub,hs⟩ := exists_subset_card_eq (s := (univ : Finset (Fin d)))
    (n := d/2) (by simp; omega)
  let T := univ \ S
  have ht : T.card = d-d/2 := by simp [T,card_sdiff_of_subset hsub,hs]
  have dis : Disjoint S T := disjoint_left.mpr fun _ hx hy => (mem_sdiff.mp hy).2 hx
  let A := cube S a b
  let B := cube T 0 b
  have sums : ∀ x∈A,∀ y∈B, IsSquare (x+y) ∧ 1≤x+y ∧ x+y≤N := by
    intro x hx y hy
    obtain ⟨I,hI,ex⟩ := mem_cube.mp hx
    obtain ⟨J,hJ,ey⟩ := mem_cube.mp hy
    apply full
    refine ⟨I∪J,?_⟩
    rw [sum_union (dis.mono hI hJ),ex,ey]; ring
  have zeroB : 0∈B := mem_cube.mpr ⟨∅,empty_subset _,by simp⟩
  have baseA : a∈A := mem_cube.mpr ⟨∅,empty_subset _,by simp⟩
  have Apos (x : ℤ) (hx : x∈A) : 0≤x := by have := (sums x hx 0 zeroB).2.1; omega
  have Bpos (x : ℤ) (hx : x∈B) : 0≤x := by
    obtain ⟨J,_,rfl⟩ := mem_cube.mp hx
    exact add_nonneg le_rfl (sum_nonneg fun i _ => (pos i).le)
  have inj {S : Finset ℤ} (nn : ∀ x∈S,0≤x) : (S.image Int.toNat).card = S.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    simpa [Int.toNat_of_nonneg (nn x hx),Int.toNat_of_nonneg (nn y hy)]
      using congrArg (fun i : ℕ => (i:ℤ)) e
  have size := bound (A.image Int.toNat) (B.image Int.toNat) (by
    intro x h; obtain ⟨u,hu,rfl⟩ := mem_image.mp h
    have := (sums u hu 0 zeroB).2.2; omega) (by
    intro x h; obtain ⟨u,hu,rfl⟩ := mem_image.mp h
    have := (sums a baseA u hu).2.2; omega) (by
    intro x hx y hy
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
    apply Int.isSquare_natCast_iff.mp
    push_cast
    simpa [Int.toNat_of_nonneg (Apos u hu),Int.toNat_of_nonneg (Bpos v hv)] using (sums u hu v hv).1)
  rw [inj Apos,inj Bpos] at size
  have freeA : Free A := by
    intro x t h h0 h1 h2 h3
    apply no4 x t h <;> first
      | simpa using (sums _ h0 _ zeroB).1
      | simpa using (sums _ h1 _ zeroB).1
      | simpa using (sums _ h2 _ zeroB).1
      | simpa using (sums _ h3 _ zeroB).1
  have freeB : Free B := by
    intro x t h h0 h1 h2 h3
    apply no4 (a+x) t h (sums _ baseA _ h0).1
    · simpa only [add_assoc] using (sums _ baseA _ h1).1
    · simpa only [add_assoc] using (sums _ baseA _ h2).1
    · simpa only [add_assoc] using (sums _ baseA _ h3).1
  have front := exponential S a b pos freeA
  have back := exponential T 0 b pos freeB
  rw [hs] at front
  rw [ht] at back
  have hpow : (3/2:ℝ)^(d/2) ≤ C*Real.log N := by
    apply le_trans _ size
    rw [Nat.cast_min,le_min_iff]
    exact ⟨front,(pow_le_pow_right₀ (by norm_num) (show d/2 ≤ d-d/2 by omega)).trans back⟩
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_mul hC.ne' (Real.log_pos (by exact_mod_cast (show 1<N by omega))).ne'] at hlog
  have lb : (1/3:ℝ) ≤ Real.log (3/2) := by
    convert Real.one_sub_inv_le_log_of_pos (show 0<(3/2:ℝ) by norm_num) using 1
    norm_num
  have half : (d:ℝ) ≤ 2*((d/2:ℕ):ℝ)+1 := by exact_mod_cast (show d≤2*(d/2)+1 by omega)
  nlinarith [mul_le_mul_of_nonneg_left lb (show (0:ℝ)≤(d/2:ℕ) by positivity)]

end OMA.Growth782

/-! A two-set larger sieve. For a prime with at most 2q occupied classes, the
4q elements of one summand supply at least 2q distinct colliding pairs. The
primes dividing the difference of a fixed pair have total logarithmic weight
at most log N. -/
namespace OMA.Sieve782
open Finset Real Filter

def Projected : Prop := ∀ A B : Finset ℕ, (∀ a∈A,∀ b∈B,IsSquare (a+b)) →
  ∀ q p : ℕ, 2≤q → p.Prime → p≠2 → p≤q^2 →
  min (A.image (· % p)).card (B.image (· % p)).card ≤ 2*q

private def pairs (A : Finset ℕ) := (A ×ˢ A).filter (fun z => z.2<z.1)
private def hits (A : Finset ℕ) (p : ℕ) := (pairs A).filter (fun z => z.1%p=z.2%p)
private def primes (q : ℕ) := (Nat.primesLE (q^2)).erase 2

private lemma collisions (A : Finset ℕ) (p : ℕ) :
    A.card ≤ (A.image (·%p)).card + (hits A p).card := by
  let seen := (hits A p).image Prod.fst
  have later (x y : ℕ) (hx : x∈A) (hy : y∈A) (lt : y<x) (eqn : x%p=y%p) : x∈seen :=
    mem_image.mpr ⟨(x,y),mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,lt⟩,eqn⟩,rfl⟩
  have rest : (A\seen).card ≤ (A.image (·%p)).card := by
    apply card_le_card_of_injOn (fun n => n%p)
    · intro x hx; exact mem_image_of_mem _ (mem_sdiff.mp hx).1
    · intro x hx y hy e
      obtain ⟨xA,xn⟩ := mem_sdiff.mp hx
      obtain ⟨yA,yn⟩ := mem_sdiff.mp hy
      rcases lt_trichotomy x y with h|h|h
      · exact (yn (later y x yA xA h e.symm)).elim
      · exact h
      · exact (xn (later x y xA yA h e)).elim
  exact card_le_card_sdiff_add_card.trans (Nat.add_le_add rest card_image_le)

private lemma one_pair {N q : ℕ} (A : Finset ℕ) (hs : ∀ x∈A,x≤N)
    (z : ℕ × ℕ) (hz : z∈pairs A) :
    (∑ p ∈ primes q, if z.1%p=z.2%p then Real.log p else 0) ≤ Real.log N := by
  obtain ⟨both,lt⟩ := mem_filter.mp hz
  let d := z.1-z.2
  have hd : 0<d := Nat.sub_pos_of_lt lt
  have small : d≤N := (Nat.sub_le ..).trans (hs _ (mem_product.mp both).1)
  let U := (primes q).filter (fun p => z.1%p=z.2%p)
  have sub : U ⊆ d.primeFactors := by
    intro p hp
    obtain ⟨prime,eqn⟩ := mem_filter.mp hp
    have pr := (Nat.mem_primesLE.mp (mem_of_mem_erase prime)).2
    exact Nat.mem_primeFactors.mpr ⟨pr,(Nat.modEq_iff_dvd' lt.le).mp eqn.symm,hd.ne'⟩
  have dvd : (∏ p ∈ U,p) ∣ d :=
    (prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) sub).trans (Nat.prod_primeFactors_dvd d)
  have po : 0<∏ p ∈ U,p := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (sub hp)).pos
  rw [← sum_filter]
  calc
    (∑ p ∈ U, Real.log p) = Real.log ((∏ p ∈ U,p : ℕ):ℝ) := by
      rw [Nat.cast_prod,Real.log_prod]
      exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors (sub hp)).ne_zero
    _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast po) (by exact_mod_cast (Nat.le_of_dvd hd dvd).trans small)

private lemma weighted {N q : ℕ} (hN : 1≤N) (A : Finset ℕ) (hs : ∀ x∈A,x≤N) :
    (∑ p ∈ primes q, ((hits A p).card:ℝ)*Real.log p) ≤ (A.card:ℝ)^2*Real.log N := by
  have eqn (p : ℕ) : ((hits A p).card:ℝ) * Real.log p =
      ∑ z ∈ pairs A, if z.1%p=z.2%p then Real.log p else 0 := by
    rw [← sum_filter]; simp [hits]
  simp_rw [eqn]
  rw [sum_comm]
  have hc : (pairs A).card ≤ A.card^2 := by simpa [pairs,sq] using (card_filter_le (s:=A ×ˢ A) (p:=fun z => z.2<z.1))
  calc
    _ ≤ ∑ _z ∈ pairs A, Real.log N := sum_le_sum fun z hz => one_pair A hs z hz
    _ = ((pairs A).card:ℝ) * Real.log N := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.log_nonneg (by exact_mod_cast hN))

private lemma log_sqrt {x : ℝ} (hx : 0≤x) : Real.log x ≤ 2*√x := by
  have hh := Real.log_le_rpow_div hx (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at hh
  linarith

private lemma prime_mass {q : ℕ} (hq : 65536≤q) :
    (q:ℝ)^2/4 ≤ ∑ p ∈ primes q, Real.log p := by
  have big : (65536:ℝ)≤q := by exact_mod_cast hq
  have hq' : (0:ℝ)≤q := Nat.cast_nonneg _
  have rt : (256:ℝ) ≤ √q := by rw [Real.le_sqrt (by norm_num) hq']; norm_num; exact hq
  have logq : Real.log q ≤ q/128 := by
    nlinarith [log_sqrt hq',Real.sq_sqrt hq',mul_nonneg (Real.sqrt_nonneg (q:ℝ)) (sub_nonneg.mpr rt)]
  have rt2 : Real.sqrt ((q:ℝ)^2+1) ≤ q+1 := by
    rw [Real.sqrt_le_iff]; constructor <;> nlinarith
  have lognext := log_sqrt (x := (q:ℝ)^2+1) (by positivity)
  have h := Chebyshev.theta_ge (q^2)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h
  push_cast at h
  rw [Real.sqrt_sq hq',Real.log_pow] at h
  have mem : 2∈Nat.primesLE (q^2) := Nat.mem_primesLE.mpr ⟨by nlinarith, Nat.prime_two⟩
  rw [← sum_erase_add _ _ mem] at h
  norm_num only [Nat.cast_ofNat] at h
  dsimp [primes]
  nlinarith [Real.log_two_gt_d9,Real.log_two_lt_d9,
    mul_le_mul_of_nonneg_left logq hq', mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (sq_nonneg (q:ℝ)),
    mul_nonneg hq' (sub_nonneg.mpr big)]

theorem logBound (localBound : Projected) : Growth782.LogBound := by
  refine ⟨300000,by norm_num,?_⟩
  filter_upwards [eventually_ge_atTop 4] with N hn
  intro A B hA hB square
  let m := min A.card B.card
  let q := m/4
  have m_le : m ≤ 4*q+3 := by dsimp [q]; omega
  have hlog : 1 ≤ Real.log N := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<2^2) (show (2:ℝ)^2≤N by exact_mod_cast hn)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_gt_d9]
  change (m:ℝ) ≤ _
  by_cases big : 65536 ≤ q
  · have h4 : 4*q ≤ m := by dsimp [q]; omega
    obtain ⟨U,uA,uc⟩ := exists_subset_card_eq (s:=A) (n:=4*q) (h4.trans (min_le_left ..))
    obtain ⟨V,vB,vc⟩ := exists_subset_card_eq (s:=B) (n:=4*q) (h4.trans (min_le_right ..))
    have proj := localBound U V (fun a ha b hb => square a (uA ha) b (vB hb)) q
    have each (p : ℕ) (hp : p∈primes q) : 2*q ≤ (hits U p).card + (hits V p).card := by
      obtain ⟨pne,pin⟩ := mem_erase.mp hp
      obtain ⟨pl,pr⟩ := Nat.mem_primesLE.mp pin
      have hh := proj p (by omega) pr pne pl
      have aa := collisions U p
      have bb := collisions V p
      omega
    have low : 2*(q:ℝ) * (∑ p ∈ primes q,Real.log p) ≤
        (∑ p ∈ primes q,((hits U p).card:ℝ)*Real.log p) +
        ∑ p ∈ primes q,((hits V p).card:ℝ)*Real.log p := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_le_sum
      intro p hp
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast each p hp)
        (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp (mem_of_mem_erase hp)).2.one_le))
    have up := add_le_add (weighted (N:=N) (q:=q) (by omega) U (fun x hx => hA x (uA hx)))
      (weighted (N:=N) (q:=q) (by omega) V (fun x hx => hB x (vB hx)))
    rw [uc,vc] at up
    push_cast at up
    have mass := mul_le_mul_of_nonneg_left (prime_mass big) (by positivity : (0:ℝ)≤2*q)
    have pos : (0:ℝ)<(q:ℝ)^2 := by
      have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
      positivity
    have qb : (q:ℝ) ≤ 64*Real.log N := by
      apply le_of_mul_le_mul_right (a:= (q:ℝ)^2) _ pos
      nlinarith only [mass.trans (low.trans up)]
    have mm : (m:ℝ)≤4*(q:ℝ)+3 := by exact_mod_cast m_le
    linarith
  · have sm : m ≤ 262143 := by omega
    have : (m:ℝ)≤262143 := by exact_mod_cast sm
    linarith

end OMA.Sieve782

namespace OMA

theorem noFour782 : Growth782.NoFour := by
  rintro x d hd ⟨r,hr⟩ ⟨s,hs⟩ ⟨t,ht⟩ ⟨u,hu⟩
  apply Fermat782.no_four_squares_in_ap r s t u d (ne_of_gt hd) <;> nlinarith

theorem dietmannElsholtz782 : type_of% @Erdos782.erdos_782.variants.dietmann_elsholtz :=
  Growth782.upper_nat noFour782 (Sieve782.logBound Quadratic782.residues)

end OMA

theorem OMA.solution : type_of% @Erdos782.erdos_782.variants.dietmann_elsholtz := OMA.dietmannElsholtz782
