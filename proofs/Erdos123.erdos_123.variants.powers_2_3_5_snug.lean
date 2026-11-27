import FormalConjectures.ErdosProblems.«123»
import Mathlib

/-!
# Short-band sums of 2–3–5 smooth numbers

This file adapts the proof of `erdos123_dcomplete_real` from
Antosha Shashakov and Principia Math, `Principia-Math-Solutions`,
commit ea33fd0a7482f2d19d0cf2ae1745f1e4d22cb076, path
`erdos123/Erdos123Complete.lean`. The original proof is licensed under Apache-2.0.
The adaptation extracts the relevant modules, modifies their code for the pinned toolchain
and checker, and translates the final theorem to the Formal Conjectures definitions.

https://github.com/antoshashakov/Principia-Math-Solutions/tree/ea33fd0a7482f2d19d0cf2ae1745f1e4d22cb076/erdos123
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

section Module_Band

namespace Erdos123Band

set_option maxHeartbeats 4000000 in
def Smooth3 (a b c : ℕ) : Set ℕ :=
  {x | ∃ k l m : ℕ, x = a ^ k * b ^ l * c ^ m}

set_option maxHeartbeats 4000000 in
def IsPrimitive (s : Finset ℕ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬x ∣ y

set_option maxHeartbeats 4000000 in
def IsDComplete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ, (∀ x ∈ s, x ∈ A) ∧ IsPrimitive s ∧ s.sum id = n

set_option maxHeartbeats 4000000 in
def PairwiseCoprime3 (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c

set_option maxHeartbeats 4000000 in
noncomputable def Band (a b c x : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ 2 * s < 3 * x)
  (Finset.range (2 * x)).filter (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ 2 * s < 3 * x)

set_option maxHeartbeats 4000000 in
noncomputable def S1 (a b c x : ℕ) : ℕ := (Band a b c x).sum id

set_option maxHeartbeats 4000000 in
noncomputable def S2 (a b c x : ℕ) : ℕ := (Band a b c x).sum (fun s => s ^ 2)

set_option maxHeartbeats 4000000 in
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

set_option maxHeartbeats 4000000 in
theorem coprime_pow_inj {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    {k l k' l' : ℕ} (h : a ^ k * b ^ l = a ^ k' * b ^ l') : k = k' ∧ l = l' := by
  have key : ∀ {k l k' l' : ℕ}, a ^ k * b ^ l = a ^ k' * b ^ l' → k ≤ k' →
      k = k' ∧ l = l' := by
    intro k l k' l' h hkk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
    rw [pow_add, mul_assoc] at h
    have hpos : 0 < a ^ k := pow_pos (by omega) k
    have h2 : b ^ l = a ^ d * b ^ l' := Nat.eq_of_mul_eq_mul_left hpos h
    have hdvd : a ^ d ∣ b ^ l := ⟨b ^ l', by rw [h2]⟩
    have hcop : Nat.Coprime (a ^ d) (b ^ l) := hab.pow d l
    have had1 : a ^ d = 1 := (Nat.gcd_eq_left hdvd).symm.trans hcop
    have hd0 : d = 0 := by
      rcases Nat.pow_eq_one.mp had1 with h1 | h1
      · omega
      · exact h1
    subst hd0
    refine ⟨by omega, ?_⟩
    rw [pow_zero, one_mul] at h2
    exact Nat.pow_right_injective hb h2
  rcases le_total k k' with hkk | hkk
  · exact key h hkk
  · obtain ⟨hk, hl⟩ := key h.symm hkk
    exact ⟨hk.symm, hl.symm⟩

set_option maxHeartbeats 4000000 in
theorem coprime_pow_ne {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    {p q : ℕ} (hp : 1 ≤ p) : a ^ p ≠ b ^ q := by
  intro h
  have h' : a ^ p * b ^ 0 = a ^ 0 * b ^ q := by simpa using h
  obtain ⟨hp0, _⟩ := coprime_pow_inj hab ha hb h'
  omega

set_option maxHeartbeats 4000000 in
theorem log_ratio_irrational {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Irrational (Real.log b / Real.log a) := by
  have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  rw [Irrational]
  rintro ⟨r, hr⟩
  have hrpos : 0 < (r : ℝ) := by rw [hr]; positivity
  have hrpos' : 0 < r := by exact_mod_cast hrpos
  have hden : 0 < r.den := r.pos
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos'
  have hrq : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by rw [← Rat.cast_def]
  have heq : (r.den : ℝ) * Real.log b = (r.num : ℝ) * Real.log a := by
    have : Real.log b = (r : ℝ) * Real.log a := by rw [hr]; field_simp
    rw [this, hrq]; field_simp
  set p : ℕ := r.num.toNat with hp
  have hpnum : (r.num : ℝ) = (p : ℝ) := by
    rw [hp]; exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm
  have heq2 : (r.den : ℝ) * Real.log b = (p : ℝ) * Real.log a := by rw [heq, hpnum]
  have hlog : Real.log ((b : ℝ) ^ r.den) = Real.log ((a : ℝ) ^ p) := by
    rw [Real.log_pow, Real.log_pow]; exact_mod_cast heq2
  have hbq : (b : ℝ) ^ r.den = (a : ℝ) ^ p :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog
  have hbqn : b ^ r.den = a ^ p := by exact_mod_cast hbq
  have hp1 : 1 ≤ p := by rw [hp]; omega
  exact coprime_pow_ne hab ha hb hp1 hbqn.symm

set_option maxHeartbeats 4000000 in
theorem exists_small_combo {u v : ℕ} (huv : Nat.Coprime u v) (hu : 2 ≤ u) (hv : 2 ≤ v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℤ, 0 < (m : ℝ) * Real.log u + (n : ℝ) * Real.log v ∧
      (m : ℝ) * Real.log u + (n : ℝ) * Real.log v < ε := by
  have hirr : Irrational (Real.log u / Real.log v) := log_ratio_irrational huv.symm hv hu
  have hdense : Dense (AddSubgroup.closure {Real.log u, Real.log v} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  obtain ⟨z, hz1, hz2⟩ :=
    (dense_iff_inter_open.mp hdense) (Set.Ioo 0 ε) isOpen_Ioo (Set.nonempty_Ioo.mpr hε)
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hz2
  rw [zsmul_eq_mul, zsmul_eq_mul] at hmn
  exact ⟨m, n, by rw [hmn]; exact hz1.1, by rw [hmn]; exact hz1.2⟩

set_option maxHeartbeats 4000000 in
theorem exists_int_step {a b : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ w z p q : ℕ, 2 ≤ w ∧ 2 ≤ z ∧ Nat.Coprime w z ∧
      (w = a ∧ z = b ∨ w = b ∧ z = a) ∧ 1 ≤ p ∧ 1 ≤ q ∧
      z ^ p < w ^ q ∧ 2 * (w ^ q) ^ K < 3 * (z ^ p) ^ K := by
  have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set ε : ℝ := Real.log (3 / 2) / K with hεdef
  have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hεpos : 0 < ε := div_pos hlog32 hKR
  have hε_le : ε ≤ Real.log (3 / 2) := by
    rw [hεdef, div_le_iff₀ hKR]; nlinarith [hlog32, hK1R]
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h32a : Real.log (3 / 2) < Real.log a := Real.log_lt_log (by norm_num) (by linarith)
  have h32b : Real.log (3 / 2) < Real.log b := Real.log_lt_log (by norm_num) (by linarith)
  have hεa : ε < Real.log a := lt_of_le_of_lt hε_le h32a
  have hεb : ε < Real.log b := lt_of_le_of_lt hε_le h32b
  obtain ⟨m, n, hpos, hlt⟩ := exists_small_combo hab ha hb hεpos
  have hcase : (1 ≤ m ∧ n ≤ -1) ∨ (m ≤ -1 ∧ 1 ≤ n) := by
    have hnotpp : ¬ (0 ≤ m ∧ 0 ≤ n) := by
      rintro ⟨hm, hn⟩
      have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
      have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hn
      rcases eq_or_lt_of_le hm with hm0 | hm1
      · rcases eq_or_lt_of_le hn with hn0 | hn1
        · rw [← hm0, ← hn0] at hpos; norm_num at hpos
        · have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          nlinarith [hlt, hεb, mul_nonneg hmR hla.le]
      · have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        nlinarith [hlt, hεa, mul_nonneg hnR hlb.le]
    have hnotnn : ¬ (m ≤ 0 ∧ n ≤ 0) := by
      rintro ⟨hm, hn⟩
      have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hn
      nlinarith [hpos, mul_nonpos_of_nonpos_of_nonneg hmR hla.le,
        mul_nonpos_of_nonpos_of_nonneg hnR hlb.le]
    rcases lt_trichotomy m 0 with hm | hm | hm
    · right; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn; exact hnotnn ⟨by omega, by omega⟩
    · exfalso
      rcases le_or_gt n 0 with hn | hn
      · exact hnotnn ⟨by omega, hn⟩
      · exact hnotpp ⟨by omega, by omega⟩
    · left; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn; exact hnotpp ⟨by omega, by omega⟩
  have key : ∀ (w z P Q : ℕ), 2 ≤ w → 2 ≤ z → 1 ≤ P → 1 ≤ Q →
      0 < (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z →
      (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z < ε →
      z ^ P < w ^ Q ∧ 2 * (w ^ Q) ^ K < 3 * (z ^ P) ^ K := by
    intro w z P Q hw hz hP hQ hgt hlt2
    have hzw : (z : ℝ) ^ P < (w : ℝ) ^ Q := by
      have hl : Real.log ((z : ℝ) ^ P) < Real.log ((w : ℝ) ^ Q) := by
        simp only [Real.log_pow]; linarith
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hl
    refine ⟨by exact_mod_cast hzw, ?_⟩
    have hstep := mul_lt_mul_of_pos_left hlt2 hKR
    have hKε : (K : ℝ) * ε = Real.log (3 / 2) := by rw [hεdef]; field_simp
    rw [hKε, mul_sub] at hstep
    have hreal : 2 * ((w : ℝ) ^ Q) ^ K < 3 * ((z : ℝ) ^ P) ^ K := by
      have hloglt : Real.log (((w : ℝ) ^ Q) ^ K) < Real.log ((3 / 2) * ((z : ℝ) ^ P) ^ K) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        simp only [Real.log_pow]
        linarith [hstep]
      have hlt3 : ((w : ℝ) ^ Q) ^ K < (3 / 2) * ((z : ℝ) ^ P) ^ K :=
        (Real.log_lt_log_iff (by positivity) (by positivity)).mp hloglt
      linarith
    have hcast : (2 * (w ^ Q) ^ K : ℝ) < (3 * (z ^ P) ^ K : ℝ) := by
      push_cast; push_cast at hreal; linarith
    exact_mod_cast hcast
  rcases hcase with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · have e1 : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ m)
    have e2 : ((-n).toNat : ℝ) = -(n : ℝ) := by
      have : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨a, b, (-n).toNat, m.toNat, ha, hb, hab, Or.inl ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key a b (-n).toNat m.toNat ha hb (by omega) (by omega) hgt hlt2
  · have e1 : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ n)
    have e2 : ((-m).toNat : ℝ) = -(m : ℝ) := by
      have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨b, a, (-m).toNat, n.toNat, hb, ha, hab.symm, Or.inr ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key b a (-m).toNat n.toNat hb ha (by omega) (by omega) hgt hlt2

set_option maxHeartbeats 4000000 in
theorem cell_quadratic {ι : Type*} (B : Finset ι) (s z : ι → ℝ)
    (hσ : (∑ i ∈ B, s i ^ 2) ≠ 0) (t : ℝ) :
    (∑ i ∈ B, (s i * t - z i) ^ 2)
      = (∑ i ∈ B, s i ^ 2) * (t - (∑ i ∈ B, s i * z i) / (∑ i ∈ B, s i ^ 2)) ^ 2
        + ((∑ i ∈ B, z i ^ 2) - (∑ i ∈ B, s i * z i) ^ 2 / (∑ i ∈ B, s i ^ 2)) := by
  have expand :
      (∑ i ∈ B, (s i * t - z i) ^ 2)
        = (∑ i ∈ B, s i ^ 2) * t ^ 2 - 2 * t * (∑ i ∈ B, s i * z i)
          + (∑ i ∈ B, z i ^ 2) := by
    rw [Finset.sum_congr rfl
      (fun i _ => show (s i * t - z i) ^ 2
        = s i ^ 2 * t ^ 2 - 2 * t * (s i * z i) + z i ^ 2 from by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
  rw [expand]; field_simp; ring

set_option maxHeartbeats 4000000 in
theorem cell_A_nonneg {ι : Type*} (B : Finset ι) (s z : ι → ℝ)
    (hσ : 0 < ∑ i ∈ B, s i ^ 2) :
    0 ≤ (∑ i ∈ B, z i ^ 2) - (∑ i ∈ B, s i * z i) ^ 2 / (∑ i ∈ B, s i ^ 2) := by
  have hcs : (∑ i ∈ B, s i * z i) ^ 2 ≤ (∑ i ∈ B, s i ^ 2) * (∑ i ∈ B, z i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq B s z
  rw [sub_nonneg, div_le_iff₀ hσ]
  nlinarith [hcs]

section Bricks

variable {a b c : ℕ}

set_option maxHeartbeats 4000000 in
theorem mem_Band {x s : ℕ} :
    s ∈ Band a b c x ↔ s ∈ Smooth3 a b c ∧ x ≤ s ∧ 2 * s < 3 * x := by
  unfold Band
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨by omega, h⟩

set_option maxHeartbeats 4000000 in
theorem band_primitive (x : ℕ) : IsPrimitive (Band a b c x) := by
  intro u hu v hv hne hdvd
  obtain ⟨-, hux, hu3⟩ := mem_Band.mp hu
  obtain ⟨-, hvx, hv3⟩ := mem_Band.mp hv
  obtain ⟨q, rfl⟩ := hdvd
  have hq2 : 2 ≤ q := by
    rcases q with _ | _ | q
    · simp only [Nat.mul_zero] at hvx hv3
      omega
    · exact absurd (Nat.mul_one u).symm hne
    · omega
  have hmul : u * 2 ≤ u * q := Nat.mul_le_mul_left u hq2
  linarith [hmul, hvx, hv3, hux, hu3]

set_option maxHeartbeats 4000000 in
theorem IsPrimitive.subset {s t : Finset ℕ} (h : IsPrimitive t) (hst : s ⊆ t) :
    IsPrimitive s :=
  fun _ hx _ hy hne => h (hst hx) (hst hy) hne

set_option maxHeartbeats 4000000 in
theorem pow_succ_le_pow {s r : ℕ} (hs : 2 ≤ s) (hsr : s + 1 ≤ r) {t : ℕ} (ht : s * s ≤ t) :
    s ^ (t + 1) ≤ r ^ t := by
  have hsp : (0 : ℝ) < s := by positivity
  have hB : (1 : ℝ) + (t : ℝ) * (1 / s) ≤ (1 + 1 / s) ^ t :=
    one_add_mul_le_pow (le_trans (by norm_num : (-2:ℝ) ≤ 0) (by positivity)) t
  have hst : (0 : ℝ) < (s : ℝ) ^ t := by positivity
  have hts : (s : ℝ) * ((s : ℝ) - 1) ≤ (t : ℝ) := by
    have : ((s * s : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    push_cast at this; nlinarith [this]
  have hLHS : (s : ℝ) ^ (t + 1) ≤ (s : ℝ) ^ t * (1 + t * (1 / s)) := by
    rw [pow_succ]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hst)
    rw [mul_one_div]
    have hd : (s : ℝ) - 1 ≤ (t : ℝ) / s := by rw [le_div_iff₀ hsp]; nlinarith [hts]
    linarith
  have hRHS : (s : ℝ) ^ t * (1 + 1 / s) ^ t = ((s : ℝ) + 1) ^ t := by
    rw [← mul_pow]; congr 1; field_simp
  have hmul : (s : ℝ) ^ t * (1 + t * (1 / s)) ≤ (s : ℝ) ^ t * (1 + 1 / s) ^ t :=
    mul_le_mul_of_nonneg_left hB (le_of_lt hst)
  have hchain : (s : ℝ) ^ (t + 1) ≤ ((s : ℝ) + 1) ^ t := by rw [← hRHS]; linarith
  have hfin : ((s : ℝ) + 1) ^ t ≤ (r : ℝ) ^ t := by
    have hsr' : (s : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hsr
    exact pow_le_pow_left₀ (by positivity) hsr' t
  have : (s : ℝ) ^ (t + 1) ≤ (r : ℝ) ^ t := le_trans hchain hfin
  exact_mod_cast this

set_option maxHeartbeats 4000000 in
theorem ladder_count {w z p q K : ℕ}
    (hz : 2 ≤ z) (hp : 1 ≤ p) (hq : 1 ≤ q) (hK : 1 ≤ K)
    (hlt : z ^ p < w ^ q) (hratio : 2 * (w ^ q) ^ K < 3 * (z ^ p) ^ K)
    (hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (Band a b c x).card := by
  set r : ℕ := w ^ q with hrdef
  set s : ℕ := z ^ p with hsdef
  have hs2 : 2 ≤ s := le_trans hz (by rw [hsdef]; exact Nat.le_self_pow (by omega) z)
  have hsr : s < r := hlt
  have hsr1 : s + 1 ≤ r := hsr
  have hs0 : 0 < s := by omega
  have hr0 : 0 < r := by omega
  set E : ℕ → ℕ → ℕ := fun N j => r ^ j * s ^ (N - j) with hEdef
  have hEpos : ∀ N j, 0 < E N j := fun N j => by simp only [hEdef]; positivity
  have hEmem : ∀ N j, E N j ∈ Smooth3 a b c := by
    intro N j
    simp only [hEdef, hrdef, hsdef, ← pow_mul]
    exact hmem (q * j) (p * (N - j))
  have hIter : ∀ N j i, j + i ≤ N → E N j * r ^ i = E N (j + i) * s ^ i := by
    intro N j i hji
    simp only [hEdef]
    rw [mul_right_comm, ← pow_add, mul_assoc, ← pow_add]
    congr 2 <;> omega
  have hMono : ∀ N j, j + 1 ≤ N → E N j < E N (j + 1) := by
    intro N j hj
    have hrec : E N j * r = E N (j + 1) * s := by
      have := hIter N j 1 (by omega); simpa using this
    have h1 : E N j * s < E N (j + 1) * s := by
      calc E N j * s < E N j * r := mul_lt_mul_of_pos_left hsr (hEpos N j)
        _ = E N (j + 1) * s := hrec
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le s)
  have hMono' : ∀ N j j', j ≤ j' → j' ≤ N → E N j ≤ E N j' := by
    intro N j j' hjj hj'
    induction j' with
    | zero => exact le_of_eq (by rw [Nat.le_zero.mp hjj])
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hMono N k (by omega)))
      · have : j = k + 1 := by omega
        rw [this]
  have hStrict : ∀ N j j', j < j' → j' ≤ N → E N j < E N j' := by
    intro N j j' hjj hj'
    calc E N j < E N (j + 1) := hMono N j (by omega)
      _ ≤ E N j' := hMono' N (j + 1) j' (by omega) hj'
  set m2 : ℕ := s * s with hm2
  refine ⟨s ^ (2 * m2 + K), fun x hxX0 => ?_⟩
  have hx1 : 1 ≤ x := le_trans (Nat.one_le_two_pow.trans (by
    exact Nat.pow_le_pow_left (by omega) _)) hxX0
  have hx0 : 0 < x := hx1
  set N : ℕ := Nat.log s x with hNdef
  have hsN : s ^ N ≤ x := Nat.pow_log_le_self s (by omega)
  have hxlt : x < s ^ (N + 1) := Nat.lt_pow_succ_log_self (by omega) x
  have hNbig : 2 * m2 + K ≤ N := Nat.le_log_of_pow_le (by omega) hxX0
  have hKN : K ≤ N := by omega
  have htbig : s * s ≤ N - K + 1 := by rw [← hm2]; omega
  have hbigmid : x ≤ E N (N - K + 1) := by
    have hchain : s ^ (N + 1) ≤ E N (N - K + 1) := by
      have hEval : E N (N - K + 1) = r ^ (N - K + 1) * s ^ (K - 1) := by
        simp only [hEdef]; congr 2; omega
      rw [hEval]
      have hsplit : s ^ (N + 1) = s ^ (N - K + 1 + 1) * s ^ (K - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      exact Nat.mul_le_mul_right _ (pow_succ_le_pow hs2 hsr1 htbig)
    omega
  have hex : ∃ j, x ≤ E N j := ⟨N - K + 1, hbigmid⟩
  classical
  set J : ℕ := Nat.find hex with hJdef
  have hJspec : x ≤ E N J := Nat.find_spec hex
  have hJle : J ≤ N - K + 1 := Nat.find_le hbigmid
  have hJmin : ∀ j, j < J → E N j < x := by
    intro j hj; have := Nat.find_min hex hj; omega
  have hJsr : E N J * s < x * r := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · have hE0 : E N J = s ^ N := by rw [hJ0]; simp only [hEdef]; simp
      rw [hE0]
      calc s ^ N * s ≤ x * s := Nat.mul_le_mul_right _ hsN
        _ < x * r := mul_lt_mul_of_pos_left hsr hx0
    · have hjm1 : E N (J - 1) < x := hJmin (J - 1) (by omega)
      have hrec : E N (J - 1) * r = E N J * s := by
        have := hIter N (J - 1) 1 (by omega)
        rw [show J - 1 + 1 = J by omega] at this; simpa using this
      calc E N J * s = E N (J - 1) * r := hrec.symm
        _ ≤ (x - 1) * r := Nat.mul_le_mul_right _ (by omega)
        _ < x * r := mul_lt_mul_of_pos_right (by omega) hr0
  have hsK : s ^ K = s ^ (K - 1) * s := by rw [← pow_succ]; congr 1; omega
  have hrK : r ^ K = r ^ (K - 1) * r := by rw [← pow_succ]; congr 1; omega
  have fA : E N (J + K - 1) * s ^ (K - 1) = E N J * r ^ (K - 1) := by
    have hI := hIter N J (K - 1) (by omega)
    rw [show J + (K - 1) = J + K - 1 by omega] at hI
    exact hI.symm
  have hbig : 2 * E N (J + K - 1) * s ^ K < 3 * x * s ^ K := by
    calc 2 * E N (J + K - 1) * s ^ K
        = 2 * (E N (J + K - 1) * s ^ (K - 1)) * s := by rw [hsK]; ring
      _ = 2 * (E N J * r ^ (K - 1)) * s := by rw [fA]
      _ = (E N J * s) * (2 * r ^ (K - 1)) := by ring
      _ < (x * r) * (2 * r ^ (K - 1)) := mul_lt_mul_of_pos_right hJsr (by positivity)
      _ = x * (2 * r ^ K) := by rw [hrK]; ring
      _ < x * (3 * s ^ K) := mul_lt_mul_of_pos_left hratio hx0
      _ = 3 * x * s ^ K := by ring
  have hupper : 2 * E N (J + K - 1) < 3 * x :=
    lt_of_mul_lt_mul_right hbig (Nat.zero_le _)
  have hmaps : ∀ i ∈ Finset.range K, E N (J + i) ∈ Band a b c x := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [mem_Band]
    refine ⟨hEmem N (J + i), le_trans hJspec (hMono' N J (J + i) (by omega) (by omega)), ?_⟩
    have hle : E N (J + i) ≤ E N (J + K - 1) := hMono' N (J + i) (J + K - 1) (by omega) (by omega)
    omega
  have hinj : Set.InjOn (fun i => E N (J + i)) (Finset.range K) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd heq (ne_of_lt (hStrict N (J + i) (J + i') (by omega) (by omega)))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hStrict N (J + i') (J + i) (by omega) (by omega)))
  have hcard := Finset.card_le_card_of_injOn (fun i => E N (J + i)) hmaps hinj
  rwa [Finset.card_range] at hcard

set_option maxHeartbeats 4000000 in
theorem band_card_eventually_ge (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (K : ℕ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (Band a b c x).card := by
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · exact ⟨0, fun x _ => by rw [hK0]; exact Nat.zero_le _⟩
  obtain ⟨w, z, p, q, hw, hz, hwz, horient, hp, hq, hlt, hratio⟩ :=
    exists_int_step hco.1 (by omega) (by omega) K hK
  have hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c := by
    intro i j
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨i, j, 0, by simp⟩
    · exact ⟨j, i, 0, by ring⟩
  exact ladder_count hz hp hq hK hlt hratio hmem

set_option maxHeartbeats 4000000 in
lemma one_add_e_norm (α : ℝ) : ‖1 + e α‖ = 2 * |Real.cos (Real.pi * α)| := by
  have harg : e α = Complex.exp ((↑(2 * Real.pi * α) : ℂ) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hre : (e α).re = Real.cos (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_re _
  have him : (e α).im = Real.sin (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_im _
  have e1 : Real.cos (2 * Real.pi * α) = 2 * Real.cos (Real.pi * α) ^ 2 - 1 := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.cos_two_mul _
  have e2 : Real.sin (2 * Real.pi * α)
      = 2 * Real.sin (Real.pi * α) * Real.cos (Real.pi * α) := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.sin_two_mul _
  have hnn : (0 : ℝ) ≤ 2 * |Real.cos (Real.pi * α)| := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (1 + e α)), ← Real.sqrt_sq hnn]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hre, him]
  rw [e1, e2, mul_pow, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * α)]

set_option maxHeartbeats 4000000 in
lemma one_add_e_eq (α : ℝ) :
    1 + e α = 2 * (Real.cos (Real.pi * α) : ℂ) * e (α / 2) := by
  have h1 : e (α / 2) = Complex.exp (↑(Real.pi * α) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hcos : (Real.cos (Real.pi * α) : ℂ)
      = (Complex.exp (↑(Real.pi * α) * Complex.I)
          + Complex.exp (-(↑(Real.pi * α) * Complex.I))) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]; ring_nf
  have hsq : Complex.exp (↑(Real.pi * α) * Complex.I)
      * Complex.exp (↑(Real.pi * α) * Complex.I) = e α := by
    rw [← Complex.exp_add, e]; congr 1; push_cast; ring
  have hcancel : Complex.exp (-(↑(Real.pi * α) * Complex.I))
      * Complex.exp (↑(Real.pi * α) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [hcos, h1,
    show (2 : ℂ) * ((Complex.exp (↑(Real.pi * α) * Complex.I)
          + Complex.exp (-(↑(Real.pi * α) * Complex.I))) / 2)
        * Complex.exp (↑(Real.pi * α) * Complex.I)
      = Complex.exp (↑(Real.pi * α) * Complex.I) * Complex.exp (↑(Real.pi * α) * Complex.I)
        + Complex.exp (-(↑(Real.pi * α) * Complex.I)) * Complex.exp (↑(Real.pi * α) * Complex.I) by
      ring]
  rw [hsq, hcancel]; ring

set_option maxHeartbeats 4000000 in
lemma sin_sq_half_ge (u : ℝ) (hu : |u| ≤ 1 / 2) :
    u ^ 2 ≤ Real.sin (Real.pi * (u / 2)) ^ 2 := by
  have h1 : |u| ≤ Real.sin (Real.pi / 2 * |u|) :=
    Real.le_sin_mul (abs_nonneg u) (by linarith)
  have h2 : Real.sin (Real.pi / 2 * |u|) ^ 2 = Real.sin (Real.pi * (u / 2)) ^ 2 := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, show Real.pi / 2 * u = Real.pi * (u / 2) by ring]
    · rw [h, show Real.pi / 2 * -u = -(Real.pi * (u / 2)) by ring, Real.sin_neg]
      ring
  calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    _ ≤ Real.sin (Real.pi / 2 * |u|) ^ 2 := by nlinarith [abs_nonneg u]
    _ = Real.sin (Real.pi * (u / 2)) ^ 2 := h2

set_option maxHeartbeats 4000000 in
lemma abs_cos_le_exp (y : ℝ) :
    |Real.cos (Real.pi * y)| ≤ Real.exp (-(2 * (y - round y) ^ 2)) := by
  set m : ℤ := round y with hm
  set u : ℝ := y - (m : ℝ) with hu
  have huabs : |u| ≤ 1 / 2 := by rw [hu, hm]; exact abs_sub_round y
  have hsplit : Real.pi * y = Real.pi * u + (m : ℝ) * Real.pi := by rw [hu]; ring
  have hper : |Real.cos (Real.pi * y)| = |Real.cos (Real.pi * u)| := by
    rw [hsplit, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one,
      one_zpow, one_mul]
  have hhalf : Real.cos (Real.pi * u) = 1 - 2 * Real.sin (Real.pi * (u / 2)) ^ 2 := by
    have hd : Real.cos (2 * (Real.pi * (u / 2)))
        = 2 * Real.cos (Real.pi * (u / 2)) ^ 2 - 1 := Real.cos_two_mul _
    have harg : Real.pi * u = 2 * (Real.pi * (u / 2)) := by ring
    rw [harg, hd]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (u / 2))]
  have hnn : 0 ≤ Real.cos (Real.pi * u) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos, (abs_le.mp huabs).1]
    · nlinarith [Real.pi_pos, (abs_le.mp huabs).2]
  have hsin := sin_sq_half_ge u huabs
  have hchain : |Real.cos (Real.pi * u)| ≤ 1 - 2 * u ^ 2 := by
    rw [abs_of_nonneg hnn, hhalf]
    linarith
  have hexp : 1 - 2 * u ^ 2 ≤ Real.exp (-(2 * u ^ 2)) := by
    have := Real.add_one_le_exp (-(2 * u ^ 2))
    linarith
  rw [hper]
  exact le_trans hchain hexp

set_option maxHeartbeats 4000000 in
noncomputable def Qenergy (a b c x : ℕ) (t : ℝ) : ℝ :=
  ∑ s ∈ Band a b c x, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2

set_option maxHeartbeats 4000000 in
noncomputable def chiBand (a b c x : ℕ) (t : ℝ) : ℝ :=
  ∏ s ∈ Band a b c x, |Real.cos (Real.pi * ((s : ℝ) * t))|

set_option maxHeartbeats 4000000 in
lemma Qenergy_nonneg (a b c x : ℕ) (t : ℝ) : 0 ≤ Qenergy a b c x t :=
  Finset.sum_nonneg (fun s _ => sq_nonneg _)

set_option maxHeartbeats 4000000 in
lemma chiBand_nonneg (a b c x : ℕ) (t : ℝ) : 0 ≤ chiBand a b c x t :=
  Finset.prod_nonneg (fun s _ => abs_nonneg _)

set_option maxHeartbeats 4000000 in
lemma measurable_round_real : Measurable (round : ℝ → ℤ) := by
  have h : (round : ℝ → ℤ) = fun x => ⌊x + 1 / 2⌋ := funext round_eq
  rw [h]
  exact Int.measurable_floor.comp (measurable_id.add measurable_const)

set_option maxHeartbeats 4000000 in
lemma Qenergy_measurable (a b c x : ℕ) : Measurable (Qenergy a b c x) := by
  unfold Qenergy
  refine Finset.measurable_sum _ (fun s _ => ?_)
  have hst : Measurable (fun t : ℝ => (s : ℝ) * t) := measurable_const.mul measurable_id
  have hround : Measurable (fun t : ℝ => ((round ((s : ℝ) * t) : ℤ) : ℝ)) :=
    (measurable_of_countable _).comp (measurable_round_real.comp hst)
  exact (hst.sub hround).pow_const 2

set_option maxHeartbeats 4000000 in
lemma exp_neg_two_Q_intervalIntegrable (a b c x : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      MeasureTheory.volume u v := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((Real.measurable_exp.comp
      ((Qenergy_measurable a b c x).const_mul 2).neg)).aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc Real.exp (-(2 * Qenergy a b c x t))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [Qenergy_nonneg a b c x t])
    _ = 1 := Real.exp_zero

set_option maxHeartbeats 4000000 in
lemma chi_le_exp_neg_two_Q (a b c x : ℕ) (t : ℝ) :
    chiBand a b c x t ≤ Real.exp (-(2 * Qenergy a b c x t)) := by
  have hle : chiBand a b c x t
      ≤ ∏ s ∈ Band a b c x, Real.exp (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2)) :=
    Finset.prod_le_prod (fun s _ => abs_nonneg _)
      (fun s _ => abs_cos_le_exp ((s : ℝ) * t))
  refine hle.trans (le_of_eq ?_)
  rw [← Real.exp_sum]
  congr 1
  have hpt : ∀ s ∈ Band a b c x,
      (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2))
        = (-2 : ℝ) * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := fun s _ => by ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Qenergy]
  ring

set_option maxHeartbeats 4000000 in
lemma chiBand_continuous (a b c x : ℕ) : Continuous (chiBand a b c x) := by
  unfold chiBand; fun_prop

set_option maxHeartbeats 4000000 in
lemma chiBand_intervalIntegrable (a b c x : ℕ) (u v : ℝ) :
    IntervalIntegrable (chiBand a b c x) MeasureTheory.volume u v :=
  (chiBand_continuous a b c x).intervalIntegrable u v

set_option maxHeartbeats 4000000 in
lemma prod_abs_one_add_e (a b c x : ℕ) (t : ℝ) :
    (∏ s ∈ Band a b c x, ‖1 + e ((s : ℝ) * t)‖)
      = 2 ^ (Band a b c x).card * chiBand a b c x t := by
  rw [chiBand, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun s _ => one_add_e_norm ((s : ℝ) * t))

set_option maxHeartbeats 4000000 in
lemma continuous_e : Continuous e := by
  unfold e; exact Complex.continuous_exp.comp (by fun_prop)

set_option maxHeartbeats 4000000 in
lemma e_norm (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  rw [hre, Real.exp_zero]

set_option maxHeartbeats 4000000 in
lemma norm_setIntegral_prod_le (a b c x n : ℕ) (S : Set ℝ) :
    ‖∫ t in S, (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ 2 ^ (Band a b c x).card * ∫ t in S, chiBand a b c x t := by
  calc ‖∫ t in S, (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ ∫ t in S, ‖(∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in S, 2 ^ (Band a b c x).card * chiBand a b c x t := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        dsimp only
        rw [norm_mul, e_norm, mul_one, norm_prod, prod_abs_one_add_e]
    _ = 2 ^ (Band a b c x).card * ∫ t in S, chiBand a b c x t :=
        MeasureTheory.integral_const_mul _ _

set_option maxHeartbeats 4000000 in
def MajorArc (x : ℕ) : Set ℝ :=
  {t | t ∈ Set.Ioc (0 : ℝ) 1 ∧ (t ≤ 1 / (8 * (x : ℝ)) ∨ 1 - 1 / (8 * (x : ℝ)) ≤ t)}

set_option maxHeartbeats 4000000 in
def MinorArc (x : ℕ) : Set ℝ := Set.Ioc (0 : ℝ) 1 \ MajorArc x

set_option maxHeartbeats 4000000 in
lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e]; rw [← Complex.exp_add]; congr 1; push_cast; ring

set_option maxHeartbeats 4000000 in
lemma integral_e (k : ℤ) :
    ∫ t in (0:ℝ)..1, e ((k : ℝ) * t) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have hcong : ∀ t ∈ Set.uIcc (0:ℝ) 1, e (((0 : ℤ) : ℝ) * t) = 1 := by
      intro t _; simp only [Int.cast_zero, zero_mul]; simp [e]
    rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const]; norm_num
  · rw [if_neg hk]
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) with hc
    have hcne : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
    have hexpc : Complex.exp c = 1 := by
      rw [hc, Complex.exp_eq_one_iff]; exact ⟨k, by ring⟩
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun t : ℝ => Complex.exp (c * ↑t) / c) (e ((k : ℝ) * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => c * (↑t : ℂ)) c t := by
        simpa using (Complex.ofRealCLM.hasDerivAt).const_mul c
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * ↑t)) (Complex.exp (c * ↑t) * c) t := h1.cexp
      have h3 := h2.div_const c
      rw [mul_div_assoc, div_self hcne, mul_one] at h3
      have hval : e ((k : ℝ) * t) = Complex.exp (c * ↑t) := by rw [e, hc]; push_cast; ring_nf
      rw [hval]; exact h3
    have hcont : IntervalIntegrable (fun t : ℝ => e ((k : ℝ) * t)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; unfold e; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, hexpc]; ring

set_option maxHeartbeats 4000000 in
lemma prod_e (T : Finset ℕ) (t : ℝ) :
    (∏ s ∈ T, e ((s : ℝ) * t)) = e (((∑ s ∈ T, s : ℕ) : ℝ) * t) := by
  induction T using Finset.induction with
  | empty => simp [e]
  | @insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← e_add]
    congr 1; push_cast; ring

set_option maxHeartbeats 4000000 in
theorem subsetSum_fourier (B : Finset ℕ) (n : ℕ) :
    (∫ t in (0:ℝ)..1, (∏ s ∈ B, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      = ((B.powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℂ) := by
  have hintegrand : ∀ t : ℝ,
      (∏ s ∈ B, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))
        = ∑ T ∈ B.powerset, e ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℝ) * t) := by
    intro t
    have hprod : (∏ s ∈ B, (1 + e ((s : ℝ) * t)))
        = ∑ T ∈ B.powerset, e (((∑ s ∈ T, s : ℕ) : ℝ) * t) := by
      have hcomm : (∏ s ∈ B, (1 + e ((s : ℝ) * t))) = ∏ s ∈ B, (e ((s : ℝ) * t) + 1) := by
        simp only [add_comm]
      rw [hcomm, Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.prod_const_one, mul_one, prod_e]
    rw [hprod, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    rw [← e_add]; congr 1; push_cast; ring
  rw [intervalIntegral.integral_congr (fun t _ => hintegrand t)]
  rw [intervalIntegral.integral_finset_sum]
  · have hterm : ∀ T ∈ B.powerset,
        (∫ t in (0:ℝ)..1, e ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℝ) * t))
          = if (∑ s ∈ T, s) = n then (1 : ℂ) else 0 := by
      intro T _
      have h := integral_e (((∑ s ∈ T, s : ℕ) : ℤ) - n)
      rw [show ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℝ)) = ((((∑ s ∈ T, s : ℕ) : ℤ) - n : ℤ) : ℝ) by
        push_cast; ring] at *
      rw [h]
      congr 1
      simp only [eq_iff_iff]
      constructor <;> intro hh <;> omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  · intro T _
    apply Continuous.intervalIntegrable; unfold e; fun_prop

set_option maxHeartbeats 4000000 in
lemma measurableSet_MajorArc (x : ℕ) : MeasurableSet (MajorArc x) := by
  have heq : MajorArc x = Set.Ioc (0 : ℝ) 1 ∩
      (Set.Iic (1 / (8 * (x : ℝ))) ∪ Set.Ici (1 - 1 / (8 * (x : ℝ)))) := by
    ext t; simp only [MajorArc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union,
      Set.mem_Iic, Set.mem_Ici]
  rw [heq]; exact measurableSet_Ioc.inter (measurableSet_Iic.union measurableSet_Ici)

set_option maxHeartbeats 4000000 in
lemma measurableSet_MinorArc (x : ℕ) : MeasurableSet (MinorArc x) :=
  measurableSet_Ioc.diff (measurableSet_MajorArc x)

set_option maxHeartbeats 4000000 in
lemma integral_chi_le_exp_on_minor (a b c x : ℕ) :
    (∫ t in MinorArc x, chiBand a b c x t)
      ≤ ∫ t in MinorArc x, Real.exp (-(2 * Qenergy a b c x t)) := by
  have hmm : MinorArc x ⊆ Set.Ioc (0 : ℝ) 1 := Set.diff_subset
  have hχ : MeasureTheory.IntegrableOn (chiBand a b c x) (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (chiBand_intervalIntegrable a b c x 0 1))).mono_set hmm
  have hexp : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (exp_neg_two_Q_intervalIntegrable a b c x 0 1))).mono_set hmm
  exact MeasureTheory.setIntegral_mono_on hχ hexp (measurableSet_MinorArc x)
    (fun t _ => chi_le_exp_neg_two_Q a b c x t)

set_option maxHeartbeats 4000000 in
lemma exp_layercake_on_minor (a b c x : ℕ) :
    (∫ t in MinorArc x, Real.exp (-(2 * Qenergy a b c x t)))
      = ∫ level in Set.Ioc (0 : ℝ) 1,
          (MeasureTheory.volume.restrict (MinorArc x)).real
            {t | level ≤ Real.exp (-(2 * Qenergy a b c x t))} := by
  have hint : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (exp_neg_two_Q_intervalIntegrable a b c x 0 1))).mono_set Set.diff_subset
  exact hint.integral_eq_integral_Ioc_meas_le
    (MeasureTheory.ae_of_all _ (fun t => Real.exp_nonneg _))
    (MeasureTheory.ae_of_all _ (fun t => by
      calc Real.exp (-(2 * Qenergy a b c x t)) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (by nlinarith [Qenergy_nonneg a b c x t])
        _ = 1 := Real.exp_zero))

set_option maxHeartbeats 4000000 in
lemma band_card_upper (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (x : ℕ) :
    (Band a b c x).card ≤ (Nat.log 2 (2 * x) + 1) ^ 3 := by
  set K := Nat.log 2 (2 * x) with hK
  have hsub : Band a b c x ⊆
      Finset.image (fun p : ℕ × ℕ × ℕ => a ^ p.1 * b ^ p.2.1 * c ^ p.2.2)
        (Finset.range (K + 1) ×ˢ Finset.range (K + 1) ×ˢ Finset.range (K + 1)) := by
    intro s hs
    obtain ⟨⟨k, l, m, hklm⟩, hxs, h2s⟩ := mem_Band.mp hs
    have hs2x : s < 2 * x := by omega
    have hbpos : 0 < b ^ l := pow_pos (by omega) l
    have hcpos : 0 < c ^ m := pow_pos (by omega) m
    have hapos : 0 < a ^ k := pow_pos (by omega) k
    have hak : a ^ k ≤ s := by
      rw [hklm, mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hbpos hcpos)
    have hbl : b ^ l ≤ s := by
      rw [hklm]; calc b ^ l ≤ a ^ k * b ^ l := Nat.le_mul_of_pos_left _ hapos
        _ ≤ a ^ k * b ^ l * c ^ m := Nat.le_mul_of_pos_right _ hcpos
    have hcm : c ^ m ≤ s := by
      rw [hklm]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hapos hbpos)
    have hbound : ∀ d e : ℕ, 2 ≤ d → d ^ e ≤ s → e ≤ K := by
      intro d e hd hde
      rw [hK]
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ e ≤ d ^ e := Nat.pow_le_pow_left hd e
        _ ≤ s := hde
        _ ≤ 2 * x := by omega
    refine Finset.mem_image.mpr ⟨(k, l, m), ?_, hklm.symm⟩
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound a k ha hak),
      Nat.lt_succ_of_le (hbound b l hb hbl), Nat.lt_succ_of_le (hbound c m hc hcm)⟩
  calc (Band a b c x).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.range (K + 1) ×ˢ Finset.range (K + 1) ×ˢ Finset.range (K + 1)).card :=
        Finset.card_image_le
    _ = (K + 1) ^ 3 := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range]; ring

set_option maxHeartbeats 4000000 in
lemma S2_upper (x : ℕ) : S2 a b c x ≤ (Band a b c x).card * (2 * x) ^ 2 := by
  unfold S2
  calc (Band a b c x).sum (fun s => s ^ 2)
      ≤ (Band a b c x).sum (fun _ => (2 * x) ^ 2) := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        obtain ⟨_, _, h2s⟩ := mem_Band.mp hs
        exact Nat.pow_le_pow_left (by omega) 2
    _ = (Band a b c x).card * (2 * x) ^ 2 := by rw [Finset.sum_const, smul_eq_mul]

set_option maxHeartbeats 4000000 in
lemma minor_meas_le {x : ℕ} {z M : ℝ}
    (hz : MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z}
            ≤ ENNReal.ofReal M) :
    MeasureTheory.volume {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ z} ≤ ENNReal.ofReal M := by
  have hsub : {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ z}
      ⊆ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z} ∪ ({1} : Set ℝ) := by
    rintro t ⟨htm, htq⟩
    have htioc : t ∈ Set.Ioc (0 : ℝ) 1 := htm.1
    rcases eq_or_lt_of_le htioc.2 with h1 | h1
    · exact Or.inr h1
    · exact Or.inl ⟨⟨le_of_lt htioc.1, h1⟩, htq⟩
  calc MeasureTheory.volume {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ z}
      ≤ MeasureTheory.volume
          ({t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z} ∪ ({1} : Set ℝ)) :=
        MeasureTheory.measure_mono hsub
    _ ≤ MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ z}
          + MeasureTheory.volume ({1} : Set ℝ) := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal M := by rw [Real.volume_singleton, add_zero]; exact hz

set_option maxHeartbeats 4000000 in
lemma level_set_eq (a b c x : ℕ) {level : ℝ} (hlevel : 0 < level) :
    {t : ℝ | level ≤ Real.exp (-(2 * Qenergy a b c x t))}
      = {t : ℝ | Qenergy a b c x t ≤ -Real.log level / 2} := by
  ext t
  simp only [Set.mem_setOf_eq]
  rw [← Real.log_le_iff_le_exp hlevel]
  constructor <;> intro h <;> linarith

set_option maxHeartbeats 4000000 in
lemma minor_exp_integral_le (a b c x : ℕ) {κ₀ Mbound : ℝ}
    (hfloor : ∀ t ∈ MinorArc x, κ₀ * Real.log x ≤ Qenergy a b c x t)
    (hmeas : (MeasureTheory.volume
        {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ Real.log x}).toReal ≤ Mbound) :
    (∫ t in MinorArc x, Real.exp (-(2 * Qenergy a b c x t)))
      ≤ Real.exp (-(2 * κ₀ * Real.log x)) * Mbound + Real.exp (-(2 * Real.log x)) := by
  have hmeas𝔪 : MeasurableSet (MinorArc x) := measurableSet_MinorArc x
  have hmeasQ : MeasurableSet {t : ℝ | Qenergy a b c x t ≤ Real.log x} :=
    measurableSet_le (Qenergy_measurable a b c x) measurable_const
  have hInt : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * Qenergy a b c x t)))
      (MinorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (exp_neg_two_Q_intervalIntegrable a b c x 0 1))).mono_set Set.diff_subset
  have hvolIoc : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; simp
  have hfin : ∀ S : Set ℝ, S ⊆ MinorArc x → MeasureTheory.volume S < ⊤ := fun S hS =>
    lt_of_le_of_lt (MeasureTheory.measure_mono (hS.trans Set.diff_subset)) hvolIoc
  rw [← MeasureTheory.integral_inter_add_sdiff hmeasQ hInt]
  refine add_le_add ?_ ?_
  ·
    have hsetle : (∫ t in MinorArc x ∩ {t | Qenergy a b c x t ≤ Real.log x},
          Real.exp (-(2 * Qenergy a b c x t)))
        ≤ ∫ _t in MinorArc x ∩ {t | Qenergy a b c x t ≤ Real.log x},
            Real.exp (-(2 * κ₀ * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.inter_subset_left)
        (MeasureTheory.integrableOn_const (hfin _ Set.inter_subset_left).ne)
        (hmeas𝔪.inter hmeasQ) (fun t ht => ?_)
      exact Real.exp_le_exp.mpr (by linarith [hfloor t ht.1])
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    rw [show MinorArc x ∩ {t | Qenergy a b c x t ≤ Real.log x}
        = {t : ℝ | t ∈ MinorArc x ∧ Qenergy a b c x t ≤ Real.log x} from by
      ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]]
    exact hmeas
  ·
    have hsetle : (∫ t in MinorArc x \ {t | Qenergy a b c x t ≤ Real.log x},
          Real.exp (-(2 * Qenergy a b c x t)))
        ≤ ∫ _t in MinorArc x \ {t | Qenergy a b c x t ≤ Real.log x},
            Real.exp (-(2 * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.diff_subset)
        (MeasureTheory.integrableOn_const (hfin _ Set.diff_subset).ne)
        (hmeas𝔪.diff hmeasQ) (fun t ht => ?_)
      have hQ : Real.log x < Qenergy a b c x t := by
        have h2 := ht.2; simp only [Set.mem_setOf_eq, not_le] at h2; exact h2
      exact Real.exp_le_exp.mpr (by linarith)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)).trans (le_of_eq (mul_one _))
    calc (MeasureTheory.volume (MinorArc x \ {t | Qenergy a b c x t ≤ Real.log x})).toReal
        ≤ (MeasureTheory.volume (Set.Ioc (0 : ℝ) 1)).toReal :=
          ENNReal.toReal_mono hvolIoc.ne
            (MeasureTheory.measure_mono (Set.diff_subset.trans Set.diff_subset))
      _ = 1 := by rw [Real.volume_Ioc]; simp

set_option maxHeartbeats 4000000 in
lemma poly_log_rpow_tendsto {p q : ℝ} (hq : 0 < q) :
    Filter.Tendsto (fun x : ℝ => Real.log x ^ p * x ^ (-q)) Filter.atTop (nhds 0) := by
  have h : (fun x : ℝ => Real.log x ^ p) =o[Filter.atTop] (fun x => x ^ q) :=
    isLittleO_log_rpow_rpow_atTop p hq
  refine (h.tendsto_div_nhds_zero).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

set_option maxHeartbeats 4000000 in
lemma natLog_two_le_realLog (x : ℕ) (hx : 1 ≤ x) :
    (Nat.log 2 (2 * x) : ℝ) ≤ Real.log (2 * x) / Real.log 2 := by
  have hpow : (2 : ℝ) ^ Nat.log 2 (2 * x) ≤ (2 * x : ℝ) := by
    have := Nat.pow_log_le_self 2 (show 2 * x ≠ 0 by omega)
    calc (2 : ℝ) ^ Nat.log 2 (2 * x) = ((2 ^ Nat.log 2 (2 * x) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * x : ℕ) : ℝ) := by exact_mod_cast this
      _ = (2 * x : ℝ) := by push_cast; ring
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  calc (Nat.log 2 (2 * x) : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ Nat.log 2 (2 * x)) := by
        rw [Real.log_pow]
    _ ≤ Real.log (2 * x) := Real.log_le_log (by positivity) hpow

set_option maxHeartbeats 4000000 in
lemma prod_one_add_e_eq (a b c x : ℕ) (t : ℝ) :
    (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t)))
      = 2 ^ (Band a b c x).card
        * ((∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ)
        * e ((S1 a b c x : ℝ) * t / 2) := by
  simp only [one_add_e_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Complex.ofReal_prod]
  congr 1
  rw [show (∏ s ∈ Band a b c x, e ((s : ℝ) * t / 2))
      = ∏ s ∈ Band a b c x, e ((s : ℝ) * (t / 2)) from by
    refine Finset.prod_congr rfl (fun s _ => ?_); rw [mul_div_assoc], prod_e]
  congr 1
  rw [S1]
  simp only [id_eq]
  ring

set_option maxHeartbeats 4000000 in
lemma integrand_re (a b c x n : ℕ) (t : ℝ) :
    ((∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = 2 ^ (Band a b c x).card * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hre : ∀ β : ℝ, (e β).re = Real.cos (2 * Real.pi * β) := by
    intro β
    have hb : e β = Complex.exp ((↑(2 * Real.pi * β) : ℂ) * Complex.I) := by
      rw [e]; congr 1; push_cast; ring
    rw [hb, Complex.exp_ofReal_mul_I_re]
  rw [prod_one_add_e_eq, mul_assoc, ← e_add,
    show ((2 : ℂ) ^ (Band a b c x).card
          * ((∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ))
        = (((2 : ℝ) ^ (Band a b c x).card
            * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t))) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, hre]
  congr 1
  rw [show 2 * Real.pi * ((S1 a b c x : ℝ) * t / 2 + -((n : ℝ) * t))
      = Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t) by ring]

set_option maxHeartbeats 4000000 in
lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j t hj IH =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have haj0 : 0 ≤ a j := ha j (Finset.mem_insert_self j t)
    have hIH : 1 - ∑ i ∈ t, a i ≤ ∏ i ∈ t, (1 - a i) :=
      IH (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    have hsum0 : 0 ≤ ∑ i ∈ t, a i :=
      Finset.sum_nonneg (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have h1 : (1 - a j) * (1 - ∑ i ∈ t, a i) ≤ (1 - a j) * ∏ i ∈ t, (1 - a i) :=
      mul_le_mul_of_nonneg_left hIH (by linarith [ha1 j (Finset.mem_insert_self j t)])
    nlinarith [h1, haj0, hsum0, mul_nonneg haj0 hsum0]

set_option maxHeartbeats 4000000 in
lemma prod_cos_ge (a b c x : ℕ) (t : ℝ)
    (ht : ∀ s ∈ Band a b c x, (Real.pi * ((s : ℝ) * t)) ^ 2 ≤ 2) :
    1 - Real.pi ^ 2 * (S2 a b c x : ℝ) * t ^ 2 / 2
      ≤ ∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) := by
  have hstep1 : (∏ s ∈ Band a b c x, (1 - (Real.pi * ((s : ℝ) * t)) ^ 2 / 2))
      ≤ ∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)) := by
    refine Finset.prod_le_prod (fun s hs => ?_) (fun s _ => Real.one_sub_sq_div_two_le_cos)
    have := ht s hs; nlinarith [this]
  refine le_trans ?_ hstep1
  have hweier := prod_one_sub_ge (Band a b c x) (fun s => (Real.pi * ((s : ℝ) * t)) ^ 2 / 2)
    (fun s _ => by positivity) (fun s hs => by have := ht s hs; linarith)
  have hL : Real.pi ^ 2 * (S2 a b c x : ℝ) * t ^ 2 / 2
      = ∑ s ∈ Band a b c x, (Real.pi * ((s : ℝ) * t)) ^ 2 / 2 := by
    rw [S2]; push_cast; rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  exact le_trans (le_of_eq (by rw [hL])) hweier

set_option maxHeartbeats 4000000 in
lemma major_arc_re_eq (a b c x n : ℕ) :
    (∫ t in MajorArc x,
        (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in MajorArc x, 2 ^ (Band a b c x).card
          * (∏ s ∈ Band a b c x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((S1 a b c x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hInt : MeasureTheory.IntegrableOn
      (fun t => (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      (MajorArc x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((by unfold e; fun_prop : Continuous
        (fun t => (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))).intervalIntegrable
        0 1))).mono_set (fun t ht => ht.1)
  have hre_int : (∫ t in MajorArc x,
        (∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in MajorArc x,
          ((∏ s ∈ Band a b c x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re := by
    simpa using (Complex.reCLM.integral_comp_comm hInt).symm
  rw [hre_int]
  exact MeasureTheory.setIntegral_congr_fun (measurableSet_MajorArc x)
    (fun t _ => integrand_re a b c x n t)

set_option maxHeartbeats 4000000 in
lemma le_S1_of_card_pos {x : ℕ} (h : 1 ≤ (Band a b c x).card) : x ≤ S1 a b c x := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp h
  calc x ≤ s := (mem_Band.mp hs).2.1
    _ = id s := rfl
    _ ≤ S1 a b c x := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hs

set_option maxHeartbeats 4000000 in
lemma S2_lower {x : ℕ} (h : 25 ≤ (Band a b c x).card) : 25 * x ^ 2 ≤ S2 a b c x := by
  have hstep : (Band a b c x).card • (x ^ 2) ≤ (Band a b c x).sum (fun s => s ^ 2) := by
    apply Finset.card_nsmul_le_sum
    intro s hs
    exact Nat.pow_le_pow_left (mem_Band.mp hs).2.1 2
  have hmul : 25 * x ^ 2 ≤ (Band a b c x).card * x ^ 2 := Nat.mul_le_mul_right _ h
  calc 25 * x ^ 2 ≤ (Band a b c x).card * x ^ 2 := hmul
    _ = (Band a b c x).card • (x ^ 2) := (smul_eq_mul _ _).symm
    _ ≤ S2 a b c x := hstep

set_option maxHeartbeats 4000000 in
lemma S1_step_upper (x : ℕ) : S1 a b c (x + 1) ≤ S1 a b c x + (3 * x + 3) := by
  classical
  have hsplit :
      ((Band a b c (x + 1)) \ (Band a b c x)).sum id
        + ((Band a b c (x + 1)) ∩ (Band a b c x)).sum id
      = S1 a b c (x + 1) := by
    rw [← Finset.sdiff_inter_self_left (Band a b c (x + 1)) (Band a b c x)]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have h1 : ((Band a b c (x + 1)) ∩ (Band a b c x)).sum id ≤ S1 a b c x :=
    Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have hsub : (Band a b c (x + 1)) \ (Band a b c x)
      ⊆ Finset.Icc ((3 * x) / 2) ((3 * x) / 2 + 1) := by
    intro s hs
    obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hS, hge, hlt⟩ := mem_Band.mp hmem
    have hxle : x ≤ s := by omega
    have h2s : 3 * x ≤ 2 * s := by
      by_contra hcon
      exact hnot (mem_Band.mpr ⟨hS, hxle, by omega⟩)
    rw [Finset.mem_Icc]
    omega
  have h2 : ((Band a b c (x + 1)) \ (Band a b c x)).sum id ≤ 3 * x + 3 := by
    calc ((Band a b c (x + 1)) \ (Band a b c x)).sum id
        ≤ (Finset.Icc ((3 * x) / 2) ((3 * x) / 2 + 1)).sum id :=
          Finset.sum_le_sum_of_subset hsub
      _ = (3 * x) / 2 + ((3 * x) / 2 + 1) := by
          rw [show Finset.Icc ((3 * x) / 2) ((3 * x) / 2 + 1)
              = {(3 * x) / 2, (3 * x) / 2 + 1} by
            ext y
            simp [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
            omega]
          rw [Finset.sum_insert (by simp)]
          simp
      _ ≤ 3 * x + 3 := by omega
  omega

set_option maxHeartbeats 4000000 in
theorem sweep (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (X₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ x : ℕ, X₀ ≤ x ∧
      (2 * (n : ℤ) - (S1 a b c x : ℤ)) ^ 2 ≤ (S2 a b c x : ℤ) := by
  classical
  obtain ⟨X₁, hX₁⟩ := band_card_eventually_ge ha hb hc hco 25
  set X₂ : ℕ := max (max X₀ X₁) 2 with hX₂def
  have hX₂card : ∀ x : ℕ, X₂ ≤ x → 25 ≤ (Band a b c x).card := fun x hx =>
    hX₁ x (le_trans (le_trans (le_max_right X₀ X₁) (le_max_left _ 2)) hx)
  refine ⟨S1 a b c X₂ + 1, fun n hn => ?_⟩
  set Q : ℕ → Prop := fun x' => X₂ ≤ x' ∧ S1 a b c x' ≤ 2 * n with hQdef
  have hQ_le : ∀ x', Q x' → x' ≤ 2 * n := by
    intro x' ⟨hx', hs1⟩
    exact le_trans (le_S1_of_card_pos (le_trans (by norm_num) (hX₂card x' hx'))) hs1
  have hQX₂ : Q X₂ := ⟨le_refl _, by omega⟩
  have hX₂le : X₂ ≤ 2 * n + 1 := le_trans (hQ_le X₂ hQX₂) (by omega)
  set x : ℕ := Nat.findGreatest Q (2 * n + 1) with hxdef
  have hspec : Q x := Nat.findGreatest_spec hX₂le hQX₂
  have hxle : x ≤ 2 * n := hQ_le x hspec
  have hnot : ¬Q (x + 1) :=
    Nat.findGreatest_is_greatest (P := Q) (n := 2 * n + 1) (k := x + 1)
      (by omega) (by omega)
  have hnext : 2 * n < S1 a b c (x + 1) := by
    by_contra hcon
    exact hnot ⟨le_trans hspec.1 (by omega), by omega⟩
  have hstep := S1_step_upper (a := a) (b := b) (c := c) x
  have hS2 := S2_lower (hX₂card x hspec.1)
  have hx2 : 2 ≤ x := le_trans (le_max_right _ 2) hspec.1
  refine ⟨x, le_trans (le_trans (le_max_left X₀ X₁) (le_max_left _ 2)) hspec.1, ?_⟩
  have h1 : (S1 a b c x : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hspec.2
  have h2 : 2 * (n : ℤ) - (S1 a b c x : ℤ) ≤ 3 * (x : ℤ) + 3 := by
    have hz : (2 * n : ℤ) < (S1 a b c (x + 1) : ℤ) := by exact_mod_cast hnext
    have hcast : (S1 a b c (x + 1) : ℤ) ≤ (S1 a b c x : ℤ) + (3 * (x : ℤ) + 3) := by
      exact_mod_cast hstep
    omega
  have h3 : (25 : ℤ) * (x : ℤ) ^ 2 ≤ (S2 a b c x : ℤ) := by exact_mod_cast hS2
  have hx2' : (2 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx2
  nlinarith [sq_nonneg (2 * (n : ℤ) - (S1 a b c x : ℤ))]

end Bricks

end Erdos123Band
end Module_Band

section Module_Slab

namespace Erdos123Band

open Real

set_option maxHeartbeats 1000000 in
theorem exists_small_theta {θ : ℝ} (hθ : Irrational θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℤ, 0 < (m : ℝ) * θ + (n : ℝ) ∧ (m : ℝ) * θ + (n : ℝ) < ε := by
  have hirr : Irrational (θ / 1) := by rwa [div_one]
  have hdense : Dense (AddSubgroup.closure {θ, (1 : ℝ)} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  obtain ⟨z, hz1, hz2⟩ :=
    (dense_iff_inter_open.mp hdense) (Set.Ioo 0 ε) isOpen_Ioo (Set.nonempty_Ioo.mpr hε)
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hz2
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hmn
  exact ⟨m, n, by rw [hmn]; exact hz1.1, by rw [hmn]; exact hz1.2⟩

set_option maxHeartbeats 1000000 in
theorem finite_net {θ : ℝ} (hθ : Irrational θ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : ℝ, ∃ r N : ℤ, |(r : ℝ)| ≤ R ∧ |y - r * θ - N| < δ := by
  obtain ⟨m, n₀, hωpos, hωlt⟩ := exists_small_theta hθ hδ
  set ω : ℝ := (m : ℝ) * θ + (n₀ : ℝ) with hωdef
  refine ⟨(|(m : ℝ)| + 1) / ω, by positivity, fun y => ?_⟩

  set y' : ℝ := y - (⌊y⌋ : ℝ) with hy'def
  have hy'0 : 0 ≤ y' := by
    have := Int.floor_le y
    simp only [hy'def]; linarith
  have hy'1 : y' < 1 := by
    have := Int.lt_floor_add_one y
    simp only [hy'def]; linarith

  set j : ℤ := ⌊y' / ω⌋ with hjdef
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (div_nonneg hy'0 hωpos.le)
  have hj0R : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
  have hjle : (j : ℝ) * ω ≤ y' := by
    have h1 : (j : ℝ) ≤ y' / ω := Int.floor_le _
    calc (j : ℝ) * ω ≤ (y' / ω) * ω := mul_le_mul_of_nonneg_right h1 hωpos.le
      _ = y' := div_mul_cancel₀ _ hωpos.ne'
  have hjlt : y' < ((j : ℝ) + 1) * ω := by
    have h1 : y' / ω < (j : ℝ) + 1 := Int.lt_floor_add_one _
    calc y' = (y' / ω) * ω := (div_mul_cancel₀ _ hωpos.ne').symm
      _ < ((j : ℝ) + 1) * ω := mul_lt_mul_of_pos_right h1 hωpos

  have hjbound : (j : ℝ) * ω < 1 := lt_of_le_of_lt hjle hy'1
  have hjltinv : (j : ℝ) < 1 / ω := (lt_div_iff₀ hωpos).mpr hjbound
  refine ⟨j * m, ⌊y⌋ + j * n₀, ?_, ?_⟩
  ·
    have h1 : |((j * m : ℤ) : ℝ)| = (j : ℝ) * |(m : ℝ)| := by
      push_cast
      rw [abs_mul, abs_of_nonneg hj0R]
    rw [h1]
    have h2 : (j : ℝ) * |(m : ℝ)| ≤ (1 / ω) * |(m : ℝ)| :=
      mul_le_mul_of_nonneg_right hjltinv.le (abs_nonneg _)
    have h3 : (1 / ω) * |(m : ℝ)| ≤ (|(m : ℝ)| + 1) / ω := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hωpos hωpos]
      nlinarith [abs_nonneg (m : ℝ), hωpos]
    linarith [h2, h3]
  ·
    have hkey : y - ((j * m : ℤ) : ℝ) * θ - ((⌊y⌋ + j * n₀ : ℤ) : ℝ) = y' - (j : ℝ) * ω := by
      simp only [hy'def, hωdef]
      push_cast
      ring
    rw [hkey, abs_of_nonneg (by linarith)]
    linarith

set_option maxHeartbeats 1000000 in
theorem two_rounding {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hirr : Irrational (u / v))
    {η : ℝ} (hη : 0 < η) (hηv : η < v) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ A X Y : ℝ, R ≤ X → R ≤ Y → u * X + v * Y = A + η / 2 →
      ∃ p q : ℤ, 0 ≤ p ∧ 0 ≤ q ∧ A ≤ u * p + v * q ∧ u * p + v * q < A + η ∧
        |(p : ℝ) - X| ≤ R ∧ |(q : ℝ) - Y| ≤ R := by
  set θ : ℝ := u / v with hθdef
  set lam : ℝ := η / v with hlamdef
  have hlam0 : 0 < lam := div_pos hη hv
  have hlam1 : lam < 1 := (div_lt_one hv).mpr hηv
  obtain ⟨R₁, hR₁0, hnet⟩ := finite_net hirr (show (0 : ℝ) < lam / 8 by positivity)

  set C₂ : ℝ := 1 + (u * (1 + R₁) + η / 2) / v with hC₂def
  set R : ℝ := max (R₁ + 2) (C₂ + 1) with hRdef
  have hR1 : 1 ≤ R := le_trans (by linarith) (le_max_left _ _)
  refine ⟨R, hR1, fun A X Y hX hY hplane => ?_⟩
  set p₀ : ℤ := ⌊X⌋ with hp₀def
  have hp₀le : (p₀ : ℝ) ≤ X := Int.floor_le X
  have hp₀gt : X - 1 < (p₀ : ℝ) := by
    have := Int.lt_floor_add_one X
    linarith
  set y₀ : ℝ := (A - u * p₀) / v with hy₀def
  obtain ⟨r, N, hrR, hdist⟩ := hnet (y₀ - (1 - lam / 2))
  set p : ℤ := p₀ + r with hpdef
  set q : ℤ := N + 1 with hqdef
  set w : ℝ := y₀ - (r : ℝ) * θ with hwdef
  have hvne : v ≠ 0 := hv.ne'

  have hvw : v * w = A - u * p := by
    simp only [hwdef, hy₀def, hθdef, hpdef]
    push_cast
    field_simp
    ring

  have hq_cast : (q : ℝ) = (N : ℝ) + 1 := by
    simp only [hqdef]; push_cast; ring
  have habs := abs_lt.mp hdist
  have hwin1 : 3 * lam / 8 < (q : ℝ) - w := by
    rw [hq_cast]
    simp only [hwdef]
    linarith [habs.2]
  have hwin2 : (q : ℝ) - w < 5 * lam / 8 := by
    rw [hq_cast]
    simp only [hwdef]
    linarith [habs.1]

  have hstrip : u * p + v * q - A = v * ((q : ℝ) - w) := by
    have : v * ((q : ℝ) - w) = v * q - v * w := by ring
    rw [this, hvw]; ring
  have hvlam : v * lam = η := by
    simp only [hlamdef]; field_simp
  have hstrip1 : A < u * p + v * q := by
    have h1 : 0 < v * ((q : ℝ) - w) := by
      have : (0 : ℝ) < 3 * lam / 8 := by positivity
      exact mul_pos hv (by linarith)
    linarith [hstrip]
  have hstrip2 : u * p + v * q < A + η := by
    have h1 : v * ((q : ℝ) - w) < v * (5 * lam / 8) := mul_lt_mul_of_pos_left hwin2 hv
    have h2 : v * (5 * lam / 8) = 5 * η / 8 := by
      rw [show v * (5 * lam / 8) = (v * lam) * 5 / 8 by ring, hvlam]; ring
    have h3 : 5 * η / 8 < η := by linarith
    linarith [hstrip]

  have hpX : |(p : ℝ) - X| ≤ 1 + R₁ := by
    simp only [hpdef]
    push_cast
    have h1 : |(p₀ : ℝ) + (r : ℝ) - X| ≤ |(p₀ : ℝ) - X| + |(r : ℝ)| := by
      calc |(p₀ : ℝ) + (r : ℝ) - X| = |((p₀ : ℝ) - X) + (r : ℝ)| := by ring_nf
        _ ≤ |(p₀ : ℝ) - X| + |(r : ℝ)| := abs_add_le _ _
    have h2 : |(p₀ : ℝ) - X| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    linarith [h1, h2, hrR]

  have hwY : |w - Y| ≤ (u * (1 + R₁) + η / 2) / v := by
    have hA : A = u * X + v * Y - η / 2 := by linarith [hplane]
    have hw2 : w = (u * (X - (p : ℝ)) - η / 2) / v + Y := by
      have h1 : v * w = A - u * p := hvw
      rw [hA] at h1
      field_simp
      linarith [h1]
    rw [hw2]
    have h3 : |(u * (X - (p : ℝ)) - η / 2) / v + Y - Y| = |u * (X - (p : ℝ)) - η / 2| / v := by
      rw [add_sub_cancel_right, abs_div, abs_of_pos hv]
    rw [h3, div_le_div_iff₀ hv hv]
    have h4 : |u * (X - (p : ℝ))| = u * |X - (p : ℝ)| := by
      rw [abs_mul, abs_of_pos hu]
    have h5 : |X - (p : ℝ)| ≤ 1 + R₁ := by rwa [abs_sub_comm]
    have hnum : |u * (X - (p : ℝ)) - η / 2| ≤ u * (1 + R₁) + η / 2 := by
      calc |u * (X - (p : ℝ)) - η / 2|
          = |u * (X - (p : ℝ)) + -(η / 2)| := by ring_nf
        _ ≤ |u * (X - (p : ℝ))| + |-(η / 2)| := abs_add_le _ _
        _ = u * |X - (p : ℝ)| + η / 2 := by
            rw [h4, abs_neg, abs_of_pos (by positivity : (0:ℝ) < η / 2)]
        _ ≤ u * (1 + R₁) + η / 2 := by
            have := mul_le_mul_of_nonneg_left h5 hu.le
            linarith
    nlinarith [hnum, hv]
  have hqw : |(q : ℝ) - w| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hwin1, hlam0]
    · linarith [hwin2, hlam1]
  have hqY : |(q : ℝ) - Y| ≤ C₂ := by
    have h1 : |(q : ℝ) - Y| ≤ |(q : ℝ) - w| + |w - Y| := abs_sub_le _ _ _
    simp only [hC₂def]
    linarith [hqw, hwY]

  have hRp : R₁ + 2 ≤ R := le_max_left _ _
  have hRq : C₂ + 1 ≤ R := le_max_right _ _
  have hp0 : 0 ≤ p := by
    have h1 : X - (1 + R₁) ≤ (p : ℝ) := by
      have := abs_le.mp hpX
      linarith [this.1]
    have h2 : (1 : ℝ) ≤ (p : ℝ) := by linarith [hX, hRp]
    exact_mod_cast le_trans (by norm_num : (0:ℝ) ≤ 1) h2
  have hq0 : 0 ≤ q := by
    have h1 : Y - C₂ ≤ (q : ℝ) := by
      have := abs_le.mp hqY
      linarith [this.1]
    have h2 : (1 : ℝ) ≤ (q : ℝ) := by linarith [hY, hRq]
    exact_mod_cast le_trans (by norm_num : (0:ℝ) ≤ 1) h2
  exact ⟨p, q, hp0, hq0, hstrip1.le, hstrip2, hpX.trans (by linarith),
    hqY.trans (by linarith)⟩

section Logs

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
lemma eta_pos : (0 : ℝ) < Real.log (3 / 2) := Real.log_pos (by norm_num)

set_option maxHeartbeats 1000000 in
lemma eta_lt_log {d : ℕ} (hd : 2 ≤ d) : Real.log (3 / 2) < Real.log d := by
  apply Real.log_lt_log (by norm_num)
  have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

set_option maxHeartbeats 1000000 in
lemma log_base_pos {d : ℕ} (hd : 2 ≤ d) : (0 : ℝ) < Real.log d := by
  apply Real.log_pos
  exact_mod_cast hd

end Logs

section ThreeRounding

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
theorem three_rounding (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L X Y Z : ℝ, 0 ≤ X → 0 ≤ Y → 0 ≤ Z →
      ¬(X = 0 ∧ Y = 0) → ¬(X = 0 ∧ Z = 0) → ¬(Y = 0 ∧ Z = 0) →
      (X = 0 ∨ 2 * R₀ ≤ X) → (Y = 0 ∨ 2 * R₀ ≤ Y) → (Z = 0 ∨ 2 * R₀ ≤ Z) →
      X * Real.log a + Y * Real.log b + Z * Real.log c = L + Real.log (3 / 2) / 2 →
      ∃ k l m : ℕ,
        (L ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
          k * Real.log a + l * Real.log b + m * Real.log c < L + Real.log (3 / 2)) ∧
        |(k : ℝ) - X| ≤ R₀ ∧ |(l : ℝ) - Y| ≤ R₀ ∧ |(m : ℝ) - Z| ≤ R₀ ∧
        (X = 0 → k = 0) ∧ (Y = 0 → l = 0) ∧ (Z = 0 → m = 0) := by
  obtain ⟨hab, hac, hbc⟩ := hco
  set α : ℝ := Real.log a with hαdef
  set β : ℝ := Real.log b with hβdef
  set γ : ℝ := Real.log c with hγdef
  set η : ℝ := Real.log (3 / 2) with hηdef
  have hα : 0 < α := log_base_pos ha
  have hβ : 0 < β := log_base_pos hb
  have hγ : 0 < γ := log_base_pos hc
  have hη : 0 < η := eta_pos
  have hηα : η < α := eta_lt_log ha
  have hηβ : η < β := eta_lt_log hb
  have hηγ : η < γ := eta_lt_log hc

  have hirr_ac : Irrational (α / γ) := by
    simpa [hαdef, hγdef] using log_ratio_irrational hac.symm hc ha
  have hirr_bc : Irrational (β / γ) := by
    simpa [hβdef, hγdef] using log_ratio_irrational hbc.symm hc hb
  have hirr_ab : Irrational (α / β) := by
    simpa [hαdef, hβdef] using log_ratio_irrational hab.symm hb ha
  obtain ⟨Rac, hRac1, hRac⟩ := two_rounding hα hγ hirr_ac hη hηγ
  obtain ⟨Rbc, hRbc1, hRbc⟩ := two_rounding hβ hγ hirr_bc hη hηγ
  obtain ⟨Rab, hRab1, hRab⟩ := two_rounding hα hβ hirr_ab hη hηβ
  set R₀ : ℝ := 1 + Rac + Rbc + Rab + β / (2 * γ) with hR₀def
  have hβγ0 : 0 < β / (2 * γ) := by positivity
  have hR₀1 : 1 ≤ R₀ := by simp only [hR₀def]; linarith
  refine ⟨R₀, hR₀1, fun L X Y Z hX0 hY0 hZ0 hXY hXZ hYZ hXalt hYalt hZalt hplane => ?_⟩
  by_cases hX : X = 0
  ·
    have hY' : 2 * R₀ ≤ Y := by
      rcases hYalt with h | h
      · exact absurd ⟨hX, h⟩ hXY
      · exact h
    have hZ' : 2 * R₀ ≤ Z := by
      rcases hZalt with h | h
      · exact absurd ⟨hX, h⟩ hXZ
      · exact h
    have hplane' : β * Y + γ * Z = L + η / 2 := by
      rw [hX] at hplane; linarith [hplane]
    have hYR : Rbc ≤ Y := by linarith [hR₀1, hRbc1, hβγ0, hRac1, hRab1]
    have hZR : Rbc ≤ Z := by linarith [hR₀1, hRbc1, hβγ0, hRac1, hRab1]
    obtain ⟨p, q, hp0, hq0, hlo, hhi, hpY, hqZ⟩ := hRbc L Y Z hYR hZR hplane'
    refine ⟨0, p.toNat, q.toNat, ?_, ?_, ?_, ?_, fun _ => rfl, ?_, ?_⟩
    · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hp0
      have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hq0
      constructor
      · push_cast
        rw [hpcast, hqcast]
        linarith [hlo]
      · push_cast
        rw [hpcast, hqcast]
        linarith [hhi]
    · rw [hX]
      simp only [Nat.cast_zero, sub_zero, abs_zero]
      linarith
    · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hp0
      rw [hpcast]
      linarith [hpY, hR₀1, hRac1, hRab1, hβγ0]
    · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hq0
      rw [hqcast]
      linarith [hqZ, hR₀1, hRac1, hRab1, hβγ0]
    · intro hY'0
      exfalso
      rw [hY'0] at hY'
      linarith [hR₀1]
    · intro hZ'0
      exfalso
      rw [hZ'0] at hZ'
      linarith [hR₀1]
  · by_cases hY : Y = 0
    ·
      have hX' : 2 * R₀ ≤ X := by
        rcases hXalt with h | h
        · exact absurd h hX
        · exact h
      have hZ' : 2 * R₀ ≤ Z := by
        rcases hZalt with h | h
        · exact absurd ⟨hY, h⟩ hYZ
        · exact h
      have hplane' : α * X + γ * Z = L + η / 2 := by
        rw [hY] at hplane; linarith [hplane]
      have hXR : Rac ≤ X := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
      have hZR : Rac ≤ Z := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
      obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqZ⟩ := hRac L X Z hXR hZR hplane'
      refine ⟨p.toNat, 0, q.toNat, ?_, ?_, ?_, ?_, ?_, fun _ => rfl, ?_⟩
      · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hp0
        have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hq0
        constructor
        · push_cast
          rw [hpcast, hqcast]
          linarith [hlo]
        · push_cast
          rw [hpcast, hqcast]
          linarith [hhi]
      · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hp0
        rw [hpcast]
        linarith [hpX, hR₀1, hRbc1, hRab1, hβγ0]
      · rw [hY]
        simp only [Nat.cast_zero, sub_zero, abs_zero]
        linarith
      · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hq0
        rw [hqcast]
        linarith [hqZ, hR₀1, hRbc1, hRab1, hβγ0]
      · intro hX'0; exact absurd hX'0 hX
      · intro hZ'0
        exfalso
        rw [hZ'0] at hZ'
        linarith [hR₀1]
    · by_cases hZ : Z = 0
      ·
        have hX' : 2 * R₀ ≤ X := by
          rcases hXalt with h | h
          · exact absurd h hX
          · exact h
        have hY' : 2 * R₀ ≤ Y := by
          rcases hYalt with h | h
          · exact absurd h hY
          · exact h
        have hplane' : α * X + β * Y = L + η / 2 := by
          rw [hZ] at hplane; linarith [hplane]
        have hXR : Rab ≤ X := by linarith [hR₀1, hRab1, hβγ0, hRbc1, hRac1]
        have hYR : Rab ≤ Y := by linarith [hR₀1, hRab1, hβγ0, hRbc1, hRac1]
        obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqY⟩ := hRab L X Y hXR hYR hplane'
        refine ⟨p.toNat, q.toNat, 0, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          constructor
          · push_cast
            rw [hpcast, hqcast]
            linarith [hlo]
          · push_cast
            rw [hpcast, hqcast]
            linarith [hhi]
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          rw [hpcast]
          linarith [hpX, hR₀1, hRbc1, hRac1, hβγ0]
        · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          rw [hqcast]
          linarith [hqY, hR₀1, hRbc1, hRac1, hβγ0]
        · rw [hZ]
          simp only [Nat.cast_zero, sub_zero, abs_zero]
          linarith
        · intro hX'0; exact absurd hX'0 hX
        · intro hY'0; exact absurd hY'0 hY
      ·
        have hX' : 2 * R₀ ≤ X := by
          rcases hXalt with h | h
          · exact absurd h hX
          · exact h
        have hY' : 2 * R₀ ≤ Y := by
          rcases hYalt with h | h
          · exact absurd h hY
          · exact h
        have hZ' : 2 * R₀ ≤ Z := by
          rcases hZalt with h | h
          · exact absurd h hZ
          · exact h
        set l₀ : ℤ := round Y with hl₀def
        have hl₀Y : |(l₀ : ℝ) - Y| ≤ 1 / 2 := by
          rw [abs_sub_comm]
          exact abs_sub_round Y
        have hl₀pos : (1 : ℝ) ≤ (l₀ : ℝ) := by
          have h1 := abs_le.mp hl₀Y
          linarith [hY', hR₀1, h1.1]
        have hl₀0 : 0 ≤ l₀ := by exact_mod_cast le_trans (by norm_num : (0:ℝ) ≤ 1) hl₀pos
        set Z' : ℝ := Z + (β / γ) * (Y - (l₀ : ℝ)) with hZ'def
        have hZ'Z : |Z' - Z| ≤ β / (2 * γ) := by
          simp only [hZ'def, add_sub_cancel_left]
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < β / γ), abs_sub_comm]
          calc (β / γ) * |(l₀ : ℝ) - Y| ≤ (β / γ) * (1 / 2) :=
                mul_le_mul_of_nonneg_left hl₀Y (by positivity)
            _ = β / (2 * γ) := by ring
        have hplane' : α * X + γ * Z' = (L - β * l₀) + η / 2 := by
          have hexp : γ * (β / γ * (Y - (l₀ : ℝ))) = β * (Y - (l₀ : ℝ)) := by
            have hγne : γ ≠ 0 := hγ.ne'
            field_simp
          calc α * X + γ * Z'
              = α * X + γ * Z + γ * (β / γ * (Y - (l₀ : ℝ))) := by
                rw [hZ'def]; ring
            _ = α * X + γ * Z + β * (Y - (l₀ : ℝ)) := by rw [hexp]
            _ = (L - β * l₀) + η / 2 := by linarith [hplane]
        have hXR : Rac ≤ X := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
        have hZ'R : Rac ≤ Z' := by
          have h1 := abs_le.mp hZ'Z
          have h2 : Z - β / (2 * γ) ≤ Z' := by linarith [h1.1]
          simp only [hR₀def] at hZ'
          linarith [hZ', hRbc1, hRab1]
        obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqZ'⟩ :=
          hRac (L - β * l₀) X Z' hXR hZ'R hplane'
        refine ⟨p.toNat, l₀.toNat, q.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          have hlcast : ((l₀.toNat : ℕ) : ℝ) = (l₀ : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hl₀0
          constructor
          · push_cast
            rw [hpcast, hqcast, hlcast]
            linarith [hlo]
          · push_cast
            rw [hpcast, hqcast, hlcast]
            linarith [hhi]
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          rw [hpcast]
          linarith [hpX, hR₀1, hRbc1, hRab1, hβγ0]
        · have hlcast : ((l₀.toNat : ℕ) : ℝ) = (l₀ : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hl₀0
          rw [hlcast]
          calc |(l₀ : ℝ) - Y| ≤ 1 / 2 := hl₀Y
            _ ≤ R₀ := by linarith [hR₀1]
        · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          rw [hqcast]
          have h1 : |(q : ℝ) - Z| ≤ |(q : ℝ) - Z'| + |Z' - Z| := abs_sub_le _ _ _
          simp only [hR₀def]
          linarith [hqZ', hZ'Z, hRbc1, hRab1]
        · intro hX'0; exact absurd hX'0 hX
        · intro hY'0; exact absurd hY'0 hY
        · intro hZ'0; exact absurd hZ'0 hZ

end ThreeRounding

section UniqueFactorization

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
theorem coprime3_pow_inj (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) {k l m k' l' m' : ℕ}
    (h : a ^ k * b ^ l * c ^ m = a ^ k' * b ^ l' * c ^ m') :
    k = k' ∧ l = l' ∧ m = m' := by
  obtain ⟨hab, hac, hbc⟩ := hco
  have key : ∀ {k l m k' l' m' : ℕ}, a ^ k * b ^ l * c ^ m = a ^ k' * b ^ l' * c ^ m' →
      k ≤ k' → k = k' := by
    intro k l m k' l' m' h hkk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
    have hpos : 0 < a ^ k := pow_pos (by omega) k
    have h2 : b ^ l * c ^ m = a ^ d * (b ^ l' * c ^ m') := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc a ^ k * (b ^ l * c ^ m) = a ^ k * b ^ l * c ^ m := by ring
        _ = a ^ (k + d) * b ^ l' * c ^ m' := h
        _ = a ^ k * (a ^ d * (b ^ l' * c ^ m')) := by rw [pow_add]; ring
    have hdvd : a ^ d ∣ b ^ l * c ^ m := ⟨b ^ l' * c ^ m', h2⟩
    have hcop : Nat.Coprime (a ^ d) (b ^ l * c ^ m) :=
      Nat.Coprime.mul_right (hab.pow d l) (hac.pow d m)
    have had1 : a ^ d = 1 := (Nat.gcd_eq_left hdvd).symm.trans hcop
    have hd0 : d = 0 := by
      rcases Nat.pow_eq_one.mp had1 with h1 | h1
      · omega
      · exact h1
    omega
  have hk : k = k' := by
    rcases le_total k k' with h' | h'
    · exact key h h'
    · exact (key h.symm h').symm
  subst hk
  have hpos : 0 < a ^ k := pow_pos (by omega) k
  have h2 : b ^ l * c ^ m = b ^ l' * c ^ m' := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc a ^ k * (b ^ l * c ^ m) = a ^ k * b ^ l * c ^ m := by ring
      _ = a ^ k * b ^ l' * c ^ m' := h
      _ = a ^ k * (b ^ l' * c ^ m') := by ring
  obtain ⟨hl, hm⟩ := coprime_pow_inj hbc hb hc h2
  exact ⟨rfl, hl, hm⟩

set_option maxHeartbeats 1000000 in
noncomputable def expTriple (a b c s : ℕ) : ℕ × ℕ × ℕ :=
  letI := Classical.dec (s ∈ Smooth3 a b c)
  if h : s ∈ Smooth3 a b c then
    (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else (0, 0, 0)

set_option maxHeartbeats 1000000 in
lemma expTriple_spec {s : ℕ} (h : s ∈ Smooth3 a b c) :
    s = a ^ (expTriple a b c s).1 * b ^ (expTriple a b c s).2.1
      * c ^ (expTriple a b c s).2.2 := by
  classical
  unfold expTriple
  rw [dif_pos h]
  exact h.choose_spec.choose_spec.choose_spec

end UniqueFactorization

section BandCount

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
theorem band_card_le_sq (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) (x : ℕ) :
    (Band a b c x).card ≤ (Nat.log 2 (2 * x) + 1) ^ 2 := by
  classical
  set K := Nat.log 2 (2 * x) with hK
  set f : ℕ → ℕ × ℕ := fun s => ((expTriple a b c s).1, (expTriple a b c s).2.1) with hf
  have hmaps : ∀ s ∈ Band a b c x, f s ∈ Finset.range (K + 1) ×ˢ Finset.range (K + 1) := by
    intro s hs
    obtain ⟨hS, hxs, h2s⟩ := mem_Band.mp hs
    have hspos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · exfalso; omega
      · exact h0
    have hs2x : s < 2 * x := by omega
    have hspec := expTriple_spec (a := a) (b := b) (c := c) hS
    set k := (expTriple a b c s).1
    set l := (expTriple a b c s).2.1
    set m := (expTriple a b c s).2.2
    have hbpos : 0 < b ^ l := pow_pos (by omega) l
    have hcpos : 0 < c ^ m := pow_pos (by omega) m
    have hapos : 0 < a ^ k := pow_pos (by omega) k
    have hak : a ^ k ≤ s := by
      rw [hspec, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hbpos hcpos)
    have hbl : b ^ l ≤ s := by
      rw [hspec]
      calc b ^ l ≤ a ^ k * b ^ l := Nat.le_mul_of_pos_left _ hapos
        _ ≤ a ^ k * b ^ l * c ^ m := Nat.le_mul_of_pos_right _ hcpos
    have hbound : ∀ d e : ℕ, 2 ≤ d → d ^ e ≤ s → e ≤ K := by
      intro d e hd hde
      rw [hK]
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ e ≤ d ^ e := Nat.pow_le_pow_left hd e
        _ ≤ s := hde
        _ ≤ 2 * x := by omega
    simp only [hf, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound a k ha hak), Nat.lt_succ_of_le (hbound b l hb hbl)⟩
  have hinj : Set.InjOn f (Band a b c x) := by
    intro s hs s' hs' heq
    obtain ⟨hS, hxs, h2s⟩ := mem_Band.mp hs
    obtain ⟨hS', hxs', h2s'⟩ := mem_Band.mp hs'
    have hspec := expTriple_spec (a := a) (b := b) (c := c) hS
    have hspec' := expTriple_spec (a := a) (b := b) (c := c) hS'
    have hkk : (expTriple a b c s).1 = (expTriple a b c s').1 := by
      have := congrArg Prod.fst heq; simpa [hf] using this
    have hll : (expTriple a b c s).2.1 = (expTriple a b c s').2.1 := by
      have := congrArg Prod.snd heq; simpa [hf] using this
    set k := (expTriple a b c s).1
    set l := (expTriple a b c s).2.1
    set m := (expTriple a b c s).2.2
    set m' := (expTriple a b c s').2.2
    rw [← hkk, ← hll] at hspec'

    have hmm : m = m' := by
      by_contra hne

      rcases Nat.lt_or_ge m m' with hlt | hge
      ·
        have hdiv : s' = s * c ^ (m' - m) := by
          have hpow : c ^ m * c ^ (m' - m) = c ^ m' := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : 2 ≤ c ^ (m' - m) := by
          calc 2 ≤ c := hc
            _ = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m' - m) := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 * s ≤ s' := by
          calc 2 * s = s * 2 := by ring
            _ ≤ s * c ^ (m' - m) := Nat.mul_le_mul_left s hcge
            _ = s' := hdiv.symm
        omega
      · have hlt : m' < m := by omega
        have hdiv : s = s' * c ^ (m - m') := by
          have hpow : c ^ m' * c ^ (m - m') = c ^ m := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : 2 ≤ c ^ (m - m') := by
          calc 2 ≤ c := hc
            _ = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m - m') := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 * s' ≤ s := by
          calc 2 * s' = s' * 2 := by ring
            _ ≤ s' * c ^ (m - m') := Nat.mul_le_mul_left s' hcge
            _ = s := hdiv.symm
        omega
    rw [hspec, hspec', hmm]
  calc (Band a b c x).card
      ≤ (Finset.range (K + 1) ×ˢ Finset.range (K + 1)).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = (K + 1) ^ 2 := by
        rw [Finset.card_product, Finset.card_range]; ring

end BandCount

section Dictionary

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
theorem mem_Band_iff_slab (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    {x : ℕ} (hx : 1 ≤ x) (k l m : ℕ) :
    a ^ k * b ^ l * c ^ m ∈ Band a b c x ↔
      (Real.log x ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
        k * Real.log a + l * Real.log b + m * Real.log c
          < Real.log x + Real.log (3 / 2)) := by
  set s : ℕ := a ^ k * b ^ l * c ^ m with hsdef
  have hapos : (0 : ℝ) < (a : ℝ) := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    have : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    linarith
  have hspos : 0 < s := by
    simp only [hsdef]
    positivity
  have hsposR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have hxposR : (0 : ℝ) < (x : ℝ) := by
    have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hlogs : Real.log s = k * Real.log a + l * Real.log b + m * Real.log c := by
    have hcast : (s : ℝ) = (a : ℝ) ^ k * (b : ℝ) ^ l * (c : ℝ) ^ m := by
      simp only [hsdef]; push_cast; ring
    rw [hcast, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  have hmemS : s ∈ Smooth3 a b c := ⟨k, l, m, rfl⟩
  rw [mem_Band]
  constructor
  · rintro ⟨-, hxs, h2s⟩
    constructor
    · rw [← hlogs]
      apply Real.log_le_log hxposR
      exact_mod_cast hxs
    · rw [← hlogs]
      have h1 : (s : ℝ) < 3 / 2 * (x : ℝ) := by
        have : (2 * s : ℝ) < (3 * x : ℝ) := by exact_mod_cast h2s
        linarith
      have h2 : Real.log s < Real.log (3 / 2 * (x : ℝ)) :=
        Real.log_lt_log hsposR h1
      rw [Real.log_mul (by norm_num) hxposR.ne'] at h2
      linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨hmemS, ?_, ?_⟩
    · rw [← hlogs] at hlo
      have h1 : (x : ℝ) ≤ (s : ℝ) := by
        have := Real.log_le_log_iff hxposR hsposR
        exact this.mp hlo
      exact_mod_cast h1
    · rw [← hlogs] at hhi
      have h1 : Real.log s < Real.log (3 / 2 * (x : ℝ)) := by
        rw [Real.log_mul (by norm_num) hxposR.ne']
        linarith
      have h2 : (s : ℝ) < 3 / 2 * (x : ℝ) :=
        (Real.log_lt_log_iff hsposR (by positivity)).mp h1
      have h3 : (2 * s : ℝ) < (3 * x : ℝ) := by linarith
      exact_mod_cast h3

end Dictionary

end Erdos123Band
end Module_Slab

section Module_Grid

namespace Erdos123Band

set_option maxHeartbeats 1000000 in
def wt (a b c : ℕ) (v : ℕ × ℕ × ℕ) : ℕ := a ^ v.1 * b ^ v.2.1 * c ^ v.2.2

set_option maxHeartbeats 1000000 in
def Tri (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {v | v.1 + v.2.1 + v.2.2 = n ∧ v ≠ (n, 0, 0) ∧ v ≠ (0, n, 0) ∧ v ≠ (0, 0, n)}

set_option maxHeartbeats 1000000 in
lemma Tri_sum {n : ℕ} {v : ℕ × ℕ × ℕ} (hv : v ∈ Tri n) : v.1 + v.2.1 + v.2.2 = n := hv.1

set_option maxHeartbeats 1000000 in
lemma Tri_at_most_one_zero {n : ℕ} {v : ℕ × ℕ × ℕ} (hv : v ∈ Tri n) :
    ¬(v.1 = 0 ∧ v.2.1 = 0) ∧ ¬(v.1 = 0 ∧ v.2.2 = 0) ∧ ¬(v.2.1 = 0 ∧ v.2.2 = 0) := by
  obtain ⟨hsum, hc1, hc2, hc3⟩ := hv
  obtain ⟨i, j, r⟩ := v
  have hsum' : i + j + r = n := hsum
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    have h1' : i = 0 := h1
    have h2' : j = 0 := h2
    exact hc3 (by simp only [Prod.mk.injEq]; omega)
  · rintro ⟨h1, h2⟩
    have h1' : i = 0 := h1
    have h2' : r = 0 := h2
    exact hc2 (by simp only [Prod.mk.injEq]; omega)
  · rintro ⟨h1, h2⟩
    have h1' : j = 0 := h1
    have h2' : r = 0 := h2
    exact hc1 (by simp only [Prod.mk.injEq]; omega)

section GridEmbedding

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
theorem grid_embedding (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ c₀ C₀ : ℝ, ∃ D : ℕ, 0 < c₀ ∧ 0 < C₀ ∧ 1 ≤ D ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
      ∃ n : ℕ, ∃ Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ,
        (c₀ * Real.log x ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * Real.log x) ∧
        (∀ v ∈ Tri n, wt a b c (Φ v) ∈ Band a b c x) ∧
        (∀ v ∈ Tri n, ∀ w ∈ Tri n, wt a b c (Φ v) = wt a b c (Φ w) → v = w) ∧
        (∀ v ∈ Tri n,
          (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
          (v.2.2 = 0 → (Φ v).2.2 = 0)) ∧
        (∀ v ∈ Tri n, ∀ w ∈ Tri n,
          (v.1 ≤ w.1 + 1 ∧ w.1 ≤ v.1 + 1 ∧ v.2.1 ≤ w.2.1 + 1 ∧ w.2.1 ≤ v.2.1 + 1 ∧
            v.2.2 ≤ w.2.2 + 1 ∧ w.2.2 ≤ v.2.2 + 1) →
          ((Φ v).1 ≤ (Φ w).1 + D ∧ (Φ w).1 ≤ (Φ v).1 + D ∧
            (Φ v).2.1 ≤ (Φ w).2.1 + D ∧ (Φ w).2.1 ≤ (Φ v).2.1 + D ∧
            (Φ v).2.2 ≤ (Φ w).2.2 + D ∧ (Φ w).2.2 ≤ (Φ v).2.2 + D)) := by
  classical
  obtain ⟨R₀, hR₀1, hround⟩ := three_rounding ha hb hc hco
  set α : ℝ := Real.log a with hαdef
  set β : ℝ := Real.log b with hβdef
  set γ : ℝ := Real.log c with hγdef
  set η : ℝ := Real.log (3 / 2) with hηdef
  have hα : 0 < α := log_base_pos ha
  have hβ : 0 < β := log_base_pos hb
  have hγ : 0 < γ := log_base_pos hc
  have hη : 0 < η := eta_pos
  have hη1 : η ≤ 1 := by
    have h1 : Real.log (3 / 2) < Real.log 2 := by
      apply Real.log_lt_log (by norm_num) (by norm_num)
    have h2 := Real.log_two_lt_d9
    simp only [hηdef]
    linarith
  set M₀ : ℝ := max α (max β γ) with hM₀def
  set m₀ : ℝ := min α (min β γ) with hm₀def
  have hM₀ : 0 < M₀ := lt_of_lt_of_le hα (le_max_left _ _)
  have hm₀ : 0 < m₀ := by
    simp only [hm₀def, lt_min_iff]
    exact ⟨hα, hβ, hγ⟩
  have hαM : α ≤ M₀ := le_max_left _ _
  have hβM : β ≤ M₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hγM : γ ≤ M₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmα : m₀ ≤ α := min_le_left _ _
  have hmβ : m₀ ≤ β := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmγ : m₀ ≤ γ := le_trans (min_le_right _ _) (min_le_right _ _)
  set τ₀ : ℝ := (4 * R₀ + 1) * M₀ with hτ₀def
  have hτ₀ : 0 < τ₀ := by
    apply mul_pos ?_ hM₀
    linarith
  have hτ₀M : τ₀ / M₀ = 4 * R₀ + 1 := by
    rw [hτ₀def, mul_div_assoc, div_self hM₀.ne', mul_one]

  set Dr : ℝ := 2 * R₀ + 2 * τ₀ / m₀ with hDrdef
  have hDrpos : 0 < Dr := by positivity
  set D : ℕ := ⌈Dr⌉₊ with hDdef
  have hDrD : Dr ≤ (D : ℝ) := Nat.le_ceil Dr
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    apply Nat.one_le_ceil_iff.mpr hDrpos

  set T : ℝ := 4 * τ₀ + 2 with hTdef
  set X₀ : ℕ := max 2 ⌈Real.exp T⌉₊ with hX₀def
  refine ⟨1 / (2 * τ₀), 2 / τ₀, D, by positivity, by positivity, hD1, X₀,
    le_max_left _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := by omega
  set L : ℝ := Real.log x with hLdef
  have hLT : T ≤ L := by
    have hxT : Real.exp T ≤ (x : ℝ) := by
      calc Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hx
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos T) hxT
  have hL0 : 0 < L := by
    have hT0 : (0 : ℝ) < T := by simp only [hTdef]; positivity
    linarith
  set Λ : ℝ := L + η / 2 with hΛdef
  have hΛ0 : 0 < Λ := by positivity
  have hLΛ : L ≤ Λ := by simp only [hΛdef]; linarith
  have hΛ2L : Λ ≤ 2 * L := by
    simp only [hΛdef]
    have : η / 2 ≤ L := by nlinarith [hLT, hη1]
    linarith
  set n : ℕ := ⌊Λ / τ₀⌋₊ with hndef
  have hn1 : 1 ≤ n := by
    rw [hndef]
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hτ₀, one_mul]
    simp only [hΛdef, hTdef] at hLT ⊢
    nlinarith [hη]
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  set τ : ℝ := Λ / n with hτdef
  have hτpos : 0 < τ := div_pos hΛ0 hn0R
  have hτlow : τ₀ ≤ τ := by
    rw [hτdef, le_div_iff₀ hn0R]
    have h1 : (n : ℝ) ≤ Λ / τ₀ := Nat.floor_le (by positivity)
    calc τ₀ * (n : ℝ) = (n : ℝ) * τ₀ := by ring
      _ ≤ (Λ / τ₀) * τ₀ := mul_le_mul_of_nonneg_right h1 hτ₀.le
      _ = Λ := div_mul_cancel₀ _ hτ₀.ne'
  have hτhigh : τ ≤ 2 * τ₀ := by
    rw [hτdef, div_le_iff₀ hn0R]
    have h1 : Λ / τ₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Λ < ((n : ℝ) + 1) * τ₀ := by
      calc Λ = (Λ / τ₀) * τ₀ := (div_mul_cancel₀ _ hτ₀.ne').symm
        _ < ((n : ℝ) + 1) * τ₀ := mul_lt_mul_of_pos_right h1 hτ₀
    nlinarith [hτ₀, hn1R]
  have hτn : τ * (n : ℝ) = Λ := by
    rw [hτdef]
    field_simp

  have hnlow : 1 / (2 * τ₀) * L ≤ (n : ℝ) := by
    have h1 : Λ / τ₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Λ < ((n : ℝ) + 1) * τ₀ := by
      calc Λ = (Λ / τ₀) * τ₀ := (div_mul_cancel₀ _ hτ₀.ne').symm
        _ < ((n : ℝ) + 1) * τ₀ := mul_lt_mul_of_pos_right h1 hτ₀
    have h3 : L < ((n : ℝ) + 1) * τ₀ := lt_of_le_of_lt hLΛ h2
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < 2 * τ₀)]
    nlinarith [hn1R, hτ₀]
  have hnhigh : (n : ℝ) ≤ 2 / τ₀ * L := by
    have h1 : (n : ℝ) ≤ Λ / τ₀ := Nat.floor_le (by positivity)
    have h2 : Λ / τ₀ ≤ (2 * L) / τ₀ := by gcongr
    calc (n : ℝ) ≤ Λ / τ₀ := h1
      _ ≤ (2 * L) / τ₀ := h2
      _ = 2 / τ₀ * L := by ring

  set Xc : ℕ → ℝ := fun i => τ * i / α with hXcdef
  set Yc : ℕ → ℝ := fun j => τ * j / β with hYcdef
  set Zc : ℕ → ℝ := fun r => τ * r / γ with hZcdef

  have coord_pos : ∀ (p : ℕ) (u : ℝ), 0 < u → u ≤ M₀ → 1 ≤ p →
      4 * R₀ + 1 ≤ τ * p / u := by
    intro p u hu huM hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    rw [le_div_iff₀ hu]
    have h1 : τ₀ ≤ τ * p := by
      calc τ₀ = τ₀ * 1 := (mul_one _).symm
        _ ≤ τ * (p : ℝ) := by
            apply mul_le_mul hτlow hp1 (by norm_num) hτpos.le
    calc (4 * R₀ + 1) * u ≤ (4 * R₀ + 1) * M₀ := by
          apply mul_le_mul_of_nonneg_left huM (by linarith)
      _ = τ₀ := hτ₀def.symm
      _ ≤ τ * p := h1
  have coord_sep : ∀ (p q : ℕ) (u : ℝ), 0 < u → u ≤ M₀ → p ≠ q →
      4 * R₀ + 1 ≤ |τ * p / u - τ * q / u| := by
    intro p q u hu huM hpq
    have h1 : |τ * p / u - τ * q / u| = (τ / u) * |(p : ℝ) - (q : ℝ)| := by
      rw [show τ * p / u - τ * q / u = (τ / u) * ((p : ℝ) - (q : ℝ)) by ring, abs_mul,
        abs_of_pos (div_pos hτpos hu)]
    have h2 : (1 : ℝ) ≤ |(p : ℝ) - (q : ℝ)| := by
      have h3 : ((p : ℤ) : ℝ) - ((q : ℤ) : ℝ) = (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) := by push_cast; ring
      have h4 : (p : ℤ) ≠ (q : ℤ) := by exact_mod_cast hpq
      have h5 : 1 ≤ |(p : ℤ) - (q : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr h4)
      have h6 : (1 : ℝ) ≤ |(((p : ℤ) - (q : ℤ) : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast h5
      calc (1 : ℝ) ≤ |(((p : ℤ) - (q : ℤ) : ℤ) : ℝ)| := h6
        _ = |(p : ℝ) - (q : ℝ)| := by rw [← h3]; push_cast; ring_nf
    have h7 : τ₀ / M₀ ≤ τ / u := by
      rw [div_le_div_iff₀ hM₀ hu]
      nlinarith [hτlow, huM, hτ₀, hu]
    rw [h1]
    calc 4 * R₀ + 1 = τ₀ / M₀ := hτ₀M.symm
      _ = (τ₀ / M₀) * 1 := (mul_one _).symm
      _ ≤ (τ / u) * |(p : ℝ) - (q : ℝ)| := by
          apply mul_le_mul h7 h2 (by norm_num) (div_pos hτpos hu).le
  have coord_close : ∀ (p q : ℕ) (u : ℝ), 0 < u → m₀ ≤ u → p ≤ q + 1 → q ≤ p + 1 →
      |τ * p / u - τ * q / u| ≤ 2 * τ₀ / m₀ := by
    intro p q u hu hum hpq hqp
    have h1 : |τ * p / u - τ * q / u| = (τ / u) * |(p : ℝ) - (q : ℝ)| := by
      rw [show τ * p / u - τ * q / u = (τ / u) * ((p : ℝ) - (q : ℝ)) by ring, abs_mul,
        abs_of_pos (div_pos hτpos hu)]
    have h2 : |(p : ℝ) - (q : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor
      · have : (q : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hqp
        linarith
      · have : (p : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hpq
        linarith
    have h3 : τ / u ≤ 2 * τ₀ / m₀ := by
      rw [div_le_div_iff₀ hu hm₀]
      nlinarith [hτhigh, hum, hm₀, hτpos]
    rw [h1]
    calc (τ / u) * |(p : ℝ) - (q : ℝ)| ≤ (τ / u) * 1 := by
          apply mul_le_mul_of_nonneg_left h2 (div_pos hτpos hu).le
      _ = τ / u := mul_one _
      _ ≤ 2 * τ₀ / m₀ := h3

  have hex : ∀ v : ℕ × ℕ × ℕ, v ∈ Tri n →
      ∃ klm : ℕ × ℕ × ℕ,
        (L ≤ klm.1 * α + klm.2.1 * β + klm.2.2 * γ ∧
          klm.1 * α + klm.2.1 * β + klm.2.2 * γ < L + η) ∧
        |(klm.1 : ℝ) - Xc v.1| ≤ R₀ ∧ |(klm.2.1 : ℝ) - Yc v.2.1| ≤ R₀ ∧
        |(klm.2.2 : ℝ) - Zc v.2.2| ≤ R₀ ∧
        (v.1 = 0 → klm.1 = 0) ∧ (v.2.1 = 0 → klm.2.1 = 0) ∧
        (v.2.2 = 0 → klm.2.2 = 0) := by
    intro v hv
    obtain ⟨i, j, r⟩ := v
    obtain ⟨hz1, hz2, hz3⟩ := Tri_at_most_one_zero hv
    simp only at hz1 hz2 hz3
    have hsum : i + j + r = n := Tri_sum hv
    have hX0 : (0 : ℝ) ≤ Xc i := by
      simp only [hXcdef]; positivity
    have hY0 : (0 : ℝ) ≤ Yc j := by
      simp only [hYcdef]; positivity
    have hZ0 : (0 : ℝ) ≤ Zc r := by
      simp only [hZcdef]; positivity
    have hXzero : Xc i = 0 ↔ i = 0 := by
      simp only [hXcdef]
      constructor
      · intro h
        by_contra hi
        have hi1 : 1 ≤ i := by omega
        have := coord_pos i α hα hαM hi1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hYzero : Yc j = 0 ↔ j = 0 := by
      simp only [hYcdef]
      constructor
      · intro h
        by_contra hj
        have hj1 : 1 ≤ j := by omega
        have := coord_pos j β hβ hβM hj1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hZzero : Zc r = 0 ↔ r = 0 := by
      simp only [hZcdef]
      constructor
      · intro h
        by_contra hr
        have hr1 : 1 ≤ r := by omega
        have := coord_pos r γ hγ hγM hr1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hXalt : Xc i = 0 ∨ 2 * R₀ ≤ Xc i := by
      by_cases hi : i = 0
      · left; exact hXzero.mpr hi
      · right
        have := coord_pos i α hα hαM (by omega)
        linarith [hR₀1]
    have hYalt : Yc j = 0 ∨ 2 * R₀ ≤ Yc j := by
      by_cases hj : j = 0
      · left; exact hYzero.mpr hj
      · right
        have := coord_pos j β hβ hβM (by omega)
        linarith [hR₀1]
    have hZalt : Zc r = 0 ∨ 2 * R₀ ≤ Zc r := by
      by_cases hr : r = 0
      · left; exact hZzero.mpr hr
      · right
        have := coord_pos r γ hγ hγM (by omega)
        linarith [hR₀1]
    have hplane : Xc i * α + Yc j * β + Zc r * γ = L + η / 2 := by
      simp only [hXcdef, hYcdef, hZcdef]
      have h1 : τ * i / α * α + τ * j / β * β + τ * r / γ * γ
          = τ * ((i : ℝ) + (j : ℝ) + (r : ℝ)) := by
        field_simp
      rw [h1]
      have h2 : (i : ℝ) + (j : ℝ) + (r : ℝ) = (n : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hsum
      rw [h2, hτn]
    have hXYz : ¬(Xc i = 0 ∧ Yc j = 0) := by
      rintro ⟨h1, h2⟩
      exact hz1 ⟨hXzero.mp h1, hYzero.mp h2⟩
    have hXZz : ¬(Xc i = 0 ∧ Zc r = 0) := by
      rintro ⟨h1, h2⟩
      exact hz2 ⟨hXzero.mp h1, hZzero.mp h2⟩
    have hYZz : ¬(Yc j = 0 ∧ Zc r = 0) := by
      rintro ⟨h1, h2⟩
      exact hz3 ⟨hYzero.mp h1, hZzero.mp h2⟩
    obtain ⟨k, l, m, hslab, hk, hl, hm, hkz, hlz, hmz⟩ :=
      hround L (Xc i) (Yc j) (Zc r) hX0 hY0 hZ0 hXYz hXZz hYZz hXalt hYalt hZalt hplane
    exact ⟨(k, l, m), hslab, hk, hl, hm,
      fun h => hkz (hXzero.mpr h), fun h => hlz (hYzero.mpr h), fun h => hmz (hZzero.mpr h)⟩

  set Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ :=
    fun v => if h : v ∈ Tri n then (hex v h).choose else (0, 0, 0) with hΦdef
  have hΦspec : ∀ v (hv : v ∈ Tri n),
      (L ≤ (Φ v).1 * α + (Φ v).2.1 * β + (Φ v).2.2 * γ ∧
        (Φ v).1 * α + (Φ v).2.1 * β + (Φ v).2.2 * γ < L + η) ∧
      |((Φ v).1 : ℝ) - Xc v.1| ≤ R₀ ∧ |((Φ v).2.1 : ℝ) - Yc v.2.1| ≤ R₀ ∧
      |((Φ v).2.2 : ℝ) - Zc v.2.2| ≤ R₀ ∧
      (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
      (v.2.2 = 0 → (Φ v).2.2 = 0) := by
    intro v hv
    simp only [hΦdef, dif_pos hv]
    exact (hex v hv).choose_spec
  refine ⟨n, Φ, ⟨hnlow, hnhigh⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    obtain ⟨⟨hlo, hhi⟩, -⟩ := hΦspec v hv
    have := (mem_Band_iff_slab ha hb hc hx1 (Φ v).1 (Φ v).2.1 (Φ v).2.2).mpr
      ⟨by rw [← hLdef, ← hαdef, ← hβdef, ← hγdef]; linarith,
        by rw [← hLdef, ← hαdef, ← hβdef, ← hγdef, ← hηdef]; linarith⟩
    exact this
  ·
    intro v hv w hw hwt
    obtain ⟨-, hkv, hlv, hmv, -⟩ := hΦspec v hv
    obtain ⟨-, hkw, hlw, hmw, -⟩ := hΦspec w hw
    obtain ⟨hkk, hll, hmm⟩ := coprime3_pow_inj ha hb hc hco hwt
    by_contra hvw

    obtain ⟨i, j, r⟩ := v
    obtain ⟨i', j', r'⟩ := w
    simp only [Prod.mk.injEq, not_and] at hvw
    have hdiff : i ≠ i' ∨ j ≠ j' ∨ r ≠ r' := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hcon.2.2) (hvw hcon.1 hcon.2.1)
    simp only at hkv hlv hmv hkw hlw hmw hkk hll hmm
    rcases hdiff with h | h | h
    · have hsep := coord_sep i i' α hα hαM h
      have h2 : ((Φ (i, j, r)).1 : ℝ) = ((Φ (i', j', r')).1 : ℝ) := by
        exact_mod_cast hkk
      have e1 : |Xc i - ((Φ (i, j, r)).1 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hkv
      have e2 : |((Φ (i, j, r)).1 : ℝ) - Xc i'| ≤ R₀ := by
        rw [h2]
        exact hkw
      have h1 : |Xc i - Xc i'| ≤ 2 * R₀ := by
        calc |Xc i - Xc i'|
            ≤ |Xc i - ((Φ (i, j, r)).1 : ℝ)| + |((Φ (i, j, r)).1 : ℝ) - Xc i'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hXcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
    · have hsep := coord_sep j j' β hβ hβM h
      have h2 : ((Φ (i, j, r)).2.1 : ℝ) = ((Φ (i', j', r')).2.1 : ℝ) := by
        exact_mod_cast hll
      have e1 : |Yc j - ((Φ (i, j, r)).2.1 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hlv
      have e2 : |((Φ (i, j, r)).2.1 : ℝ) - Yc j'| ≤ R₀ := by
        rw [h2]
        exact hlw
      have h1 : |Yc j - Yc j'| ≤ 2 * R₀ := by
        calc |Yc j - Yc j'|
            ≤ |Yc j - ((Φ (i, j, r)).2.1 : ℝ)| + |((Φ (i, j, r)).2.1 : ℝ) - Yc j'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hYcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
    · have hsep := coord_sep r r' γ hγ hγM h
      have h2 : ((Φ (i, j, r)).2.2 : ℝ) = ((Φ (i', j', r')).2.2 : ℝ) := by
        exact_mod_cast hmm
      have e1 : |Zc r - ((Φ (i, j, r)).2.2 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hmv
      have e2 : |((Φ (i, j, r)).2.2 : ℝ) - Zc r'| ≤ R₀ := by
        rw [h2]
        exact hmw
      have h1 : |Zc r - Zc r'| ≤ 2 * R₀ := by
        calc |Zc r - Zc r'|
            ≤ |Zc r - ((Φ (i, j, r)).2.2 : ℝ)| + |((Φ (i, j, r)).2.2 : ℝ) - Zc r'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hZcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
  ·
    intro v hv
    obtain ⟨-, -, -, -, h1, h2, h3⟩ := hΦspec v hv
    exact ⟨h1, h2, h3⟩
  ·
    intro v hv w hw hclose
    obtain ⟨-, hkv, hlv, hmv, -⟩ := hΦspec v hv
    obtain ⟨-, hkw, hlw, hmw, -⟩ := hΦspec w hw
    obtain ⟨h11, h12, h21, h22, h31, h32⟩ := hclose
    have hboundk : |((Φ v).1 : ℝ) - ((Φ w).1 : ℝ)| ≤ Dr := by
      have hc := coord_close v.1 w.1 α hα hmα h11 h12
      calc |((Φ v).1 : ℝ) - ((Φ w).1 : ℝ)|
          ≤ |((Φ v).1 : ℝ) - Xc v.1| + |Xc v.1 - ((Φ w).1 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Xc v.1 - Xc w.1| + |Xc w.1 - ((Φ w).1 : ℝ)|) := by
            apply add_le_add hkv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hXcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have hboundl : |((Φ v).2.1 : ℝ) - ((Φ w).2.1 : ℝ)| ≤ Dr := by
      have hc := coord_close v.2.1 w.2.1 β hβ hmβ h21 h22
      calc |((Φ v).2.1 : ℝ) - ((Φ w).2.1 : ℝ)|
          ≤ |((Φ v).2.1 : ℝ) - Yc v.2.1| + |Yc v.2.1 - ((Φ w).2.1 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Yc v.2.1 - Yc w.2.1| + |Yc w.2.1 - ((Φ w).2.1 : ℝ)|) := by
            apply add_le_add hlv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hYcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have hboundm : |((Φ v).2.2 : ℝ) - ((Φ w).2.2 : ℝ)| ≤ Dr := by
      have hc := coord_close v.2.2 w.2.2 γ hγ hmγ h31 h32
      calc |((Φ v).2.2 : ℝ) - ((Φ w).2.2 : ℝ)|
          ≤ |((Φ v).2.2 : ℝ) - Zc v.2.2| + |Zc v.2.2 - ((Φ w).2.2 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Zc v.2.2 - Zc w.2.2| + |Zc w.2.2 - ((Φ w).2.2 : ℝ)|) := by
            apply add_le_add hmv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hZcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have conv : ∀ p q : ℕ, |(p : ℝ) - (q : ℝ)| ≤ Dr → p ≤ q + D ∧ q ≤ p + D := by
      intro p q hpq
      have h1 := abs_le.mp hpq
      constructor
      · have h2 : (p : ℝ) ≤ (q : ℝ) + (D : ℝ) := by linarith [h1.2, hDrD]
        exact_mod_cast h2
      · have h2 : (q : ℝ) ≤ (p : ℝ) + (D : ℝ) := by linarith [h1.1, hDrD]
        exact_mod_cast h2
    obtain ⟨e1, e2⟩ := conv _ _ hboundk
    obtain ⟨e3, e4⟩ := conv _ _ hboundl
    obtain ⟨e5, e6⟩ := conv _ _ hboundm
    exact ⟨e1, e2, e3, e4, e5, e6⟩

end GridEmbedding

end Erdos123Band
end Module_Grid

section Module_Routing

namespace Erdos123Band

set_option maxHeartbeats 1000000 in
def rowV (n q i : ℕ) : ℕ × ℕ × ℕ := (i, q - i, n - q)

set_option maxHeartbeats 1000000 in
def pathV (n q j s : ℕ) : ℕ × ℕ × ℕ := (q - j + s, j, n - q - s)

set_option maxHeartbeats 1000000 in
def midQ (n : ℕ) : Finset ℕ := Finset.Icc ((n + 2) / 3) ((2 * n) / 3)

set_option maxHeartbeats 1000000 in
def midJ (q : ℕ) : Finset ℕ := Finset.Icc ((q + 3) / 4) ((3 * q) / 4)

set_option maxHeartbeats 1000000 in
lemma midQ_card {n : ℕ} (hn : 48 ≤ n) : n ≤ 4 * (midQ n).card := by
  rw [midQ, Nat.card_Icc]
  omega

set_option maxHeartbeats 1000000 in
lemma midJ_card {n q : ℕ} (hn : 48 ≤ n) (hq : q ∈ midQ n) : n ≤ 7 * (midJ q).card := by
  rw [midQ, Finset.mem_Icc] at hq
  rw [midJ, Nat.card_Icc]
  omega

set_option maxHeartbeats 1000000 in
lemma midQ_bounds {n q : ℕ} (hq : q ∈ midQ n) : (n + 2) / 3 ≤ q ∧ q ≤ (2 * n) / 3 := by
  rwa [midQ, Finset.mem_Icc] at hq

set_option maxHeartbeats 1000000 in
lemma midJ_bounds {q j : ℕ} (hj : j ∈ midJ q) : (q + 3) / 4 ≤ j ∧ j ≤ (3 * q) / 4 := by
  rwa [midJ, Finset.mem_Icc] at hj

set_option maxHeartbeats 1000000 in
lemma rowV_mem_Tri {n q i : ℕ} (hn : 48 ≤ n) (hq : q ∈ midQ n) (hi : i ≤ q) :
    rowV n q i ∈ Tri n := by
  obtain ⟨hq1, hq2⟩ := midQ_bounds hq
  refine ⟨by show i + (q - i) + (n - q) = n; omega, ?_, ?_, ?_⟩
  all_goals
    simp only [rowV, ne_eq, Prod.mk.injEq, not_and]
    omega

set_option maxHeartbeats 1000000 in
lemma pathV_mem_Tri {n q j s : ℕ} (hn : 48 ≤ n) (hq : q ∈ midQ n) (hj : j ∈ midJ q)
    (hs : s ≤ n - q) :
    pathV n q j s ∈ Tri n := by
  obtain ⟨hq1, hq2⟩ := midQ_bounds hq
  obtain ⟨hj1, hj2⟩ := midJ_bounds hj
  refine ⟨by show q - j + s + j + (n - q - s) = n; omega, ?_, ?_, ?_⟩
  all_goals
    simp only [pathV, ne_eq, Prod.mk.injEq, not_and]
    omega

set_option maxHeartbeats 1000000 in
lemma pathV_zero {n q j : ℕ} (hj : j ≤ q) : pathV n q j 0 = rowV n q (q - j) := by
  simp only [pathV, rowV, Prod.mk.injEq]
  omega

set_option maxHeartbeats 1000000 in
lemma rowV_adjacent {n q i : ℕ} (hi : i + 1 ≤ q) :
    (rowV n q i).1 ≤ (rowV n q (i + 1)).1 + 1 ∧
    (rowV n q (i + 1)).1 ≤ (rowV n q i).1 + 1 ∧
    (rowV n q i).2.1 ≤ (rowV n q (i + 1)).2.1 + 1 ∧
    (rowV n q (i + 1)).2.1 ≤ (rowV n q i).2.1 + 1 ∧
    (rowV n q i).2.2 ≤ (rowV n q (i + 1)).2.2 + 1 ∧
    (rowV n q (i + 1)).2.2 ≤ (rowV n q i).2.2 + 1 := by
  simp only [rowV]
  omega

set_option maxHeartbeats 1000000 in
lemma pathV_adjacent {n q j s : ℕ} (hj : j ≤ q) (hs : s + 1 ≤ n - q) :
    (pathV n q j s).1 ≤ (pathV n q j (s + 1)).1 + 1 ∧
    (pathV n q j (s + 1)).1 ≤ (pathV n q j s).1 + 1 ∧
    (pathV n q j s).2.1 ≤ (pathV n q j (s + 1)).2.1 + 1 ∧
    (pathV n q j (s + 1)).2.1 ≤ (pathV n q j s).2.1 + 1 ∧
    (pathV n q j s).2.2 ≤ (pathV n q j (s + 1)).2.2 + 1 ∧
    (pathV n q j (s + 1)).2.2 ≤ (pathV n q j s).2.2 + 1 := by
  simp only [pathV]
  omega

section Selection

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
noncomputable def rowBad (Bad : ℕ × ℕ × ℕ → Prop) (n q : ℕ) : Finset ℕ :=
  letI := Classical.decPred Bad
  (Finset.range (q + 1)).filter (fun i => Bad (rowV n q i))

set_option maxHeartbeats 1000000 in
noncomputable def pathBad (Bad : ℕ × ℕ × ℕ → Prop) (n q j : ℕ) : Finset ℕ :=
  letI := Classical.decPred Bad
  (Finset.range (n - q + 1)).filter (fun s => Bad (pathV n q j s))

set_option maxHeartbeats 1000000 in
theorem exists_sparse_row_and_path (hn : 48 ≤ n)
    (Bad : ℕ × ℕ × ℕ → Prop) (H : ℕ)
    (hH : ∀ F : Finset (ℕ × ℕ × ℕ), (∀ v ∈ F, v ∈ Tri n ∧ Bad v) → F.card ≤ H) :
    ∃ q ∈ midQ n, ∃ j ∈ midJ q,
      n * (rowBad Bad n q).card ≤ 4 * H ∧
      n * (pathBad Bad n q j).card ≤ 7 * H := by
  classical

  have hrow_sum : ∑ q ∈ midQ n, (rowBad Bad n q).card ≤ H := by

    set F : Finset (ℕ × ℕ × ℕ) := (midQ n).biUnion (fun q => (rowBad Bad n q).image (rowV n q))
      with hFdef
    have hFsub : ∀ v ∈ F, v ∈ Tri n ∧ Bad v := by
      intro v hv
      simp only [hFdef, Finset.mem_biUnion, Finset.mem_image] at hv
      obtain ⟨q, hq, i, hi, rfl⟩ := hv
      rw [rowBad, Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨rowV_mem_Tri hn hq (by omega), hi.2⟩
    have hFcard : F.card = ∑ q ∈ midQ n, (rowBad Bad n q).card := by
      rw [hFdef, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro q hq
        apply Finset.card_image_of_injOn
        intro i _ i' _ hii
        have h1 := congrArg (fun v : ℕ × ℕ × ℕ => v.1) hii
        simpa only [rowV] using h1
      · intro q hq q' hq' hqq
        apply Finset.disjoint_left.mpr
        intro v hv hv'
        simp only [Finset.mem_image] at hv hv'
        obtain ⟨i, hi, rfl⟩ := hv
        obtain ⟨i', hi', heq⟩ := hv'
        rw [rowBad, Finset.mem_filter, Finset.mem_range] at hi hi'
        obtain ⟨hq1, hq2⟩ := midQ_bounds hq
        obtain ⟨hq1', hq2'⟩ := midQ_bounds hq'

        have h3 : n - q' = n - q := by
          have h := congrArg (fun v : ℕ × ℕ × ℕ => v.2.2) heq
          simpa only [rowV] using h
        have h4 : q = q' := by omega
        exact hqq h4
    rw [← hFcard]
    exact hH F hFsub
  have hrow_min : ∃ q ∈ midQ n, (midQ n).card * (rowBad Bad n q).card ≤ H := by
    have hne : (midQ n).Nonempty := by
      rw [← Finset.card_pos]
      have := midQ_card hn
      omega
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (midQ n)
      (fun q => (rowBad Bad n q).card) hne
    refine ⟨q, hq, ?_⟩
    calc (midQ n).card * (rowBad Bad n q).card
        = ∑ _q' ∈ midQ n, (rowBad Bad n q).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ q' ∈ midQ n, (rowBad Bad n q').card :=
          Finset.sum_le_sum (fun q' hq' => hmin q' hq')
      _ ≤ H := hrow_sum
  obtain ⟨q, hq, hrowq⟩ := hrow_min

  have hpath_sum : ∑ j ∈ midJ q, (pathBad Bad n q j).card ≤ H := by
    set F : Finset (ℕ × ℕ × ℕ) :=
      (midJ q).biUnion (fun j => (pathBad Bad n q j).image (pathV n q j)) with hFdef
    have hFsub : ∀ v ∈ F, v ∈ Tri n ∧ Bad v := by
      intro v hv
      simp only [hFdef, Finset.mem_biUnion, Finset.mem_image] at hv
      obtain ⟨j, hj, s, hs, rfl⟩ := hv
      rw [pathBad, Finset.mem_filter, Finset.mem_range] at hs
      exact ⟨pathV_mem_Tri hn hq hj (by omega), hs.2⟩
    have hFcard : F.card = ∑ j ∈ midJ q, (pathBad Bad n q j).card := by
      rw [hFdef, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro j hj
        apply Finset.card_image_of_injOn
        intro s hs s' hs' hss
        rw [Finset.mem_coe, pathBad, Finset.mem_filter, Finset.mem_range] at hs hs'
        have h3 := congrArg (fun v : ℕ × ℕ × ℕ => v.2.2) hss
        simp only [pathV] at h3
        obtain ⟨hq1, hq2⟩ := midQ_bounds hq
        omega
      · intro j hj j' hj' hjj
        apply Finset.disjoint_left.mpr
        intro v hv hv'
        simp only [Finset.mem_image] at hv hv'
        obtain ⟨s, hs, rfl⟩ := hv
        obtain ⟨s', hs', heq⟩ := hv'
        have h2 := congrArg (fun v : ℕ × ℕ × ℕ => v.2.1) heq
        simp only [pathV] at h2
        exact hjj h2.symm
    rw [← hFcard]
    exact hH F hFsub
  have hpath_min : ∃ j ∈ midJ q, (midJ q).card * (pathBad Bad n q j).card ≤ H := by
    have hne : (midJ q).Nonempty := by
      rw [← Finset.card_pos]
      have := midJ_card hn hq
      omega
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (midJ q)
      (fun j => (pathBad Bad n q j).card) hne
    refine ⟨j, hj, ?_⟩
    calc (midJ q).card * (pathBad Bad n q j).card
        = ∑ _j' ∈ midJ q, (pathBad Bad n q j).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ j' ∈ midJ q, (pathBad Bad n q j').card :=
          Finset.sum_le_sum (fun j' hj' => hmin j' hj')
      _ ≤ H := hpath_sum
  obtain ⟨j, hj, hpathj⟩ := hpath_min
  refine ⟨q, hq, j, hj, ?_, ?_⟩
  · calc n * (rowBad Bad n q).card ≤ 4 * (midQ n).card * (rowBad Bad n q).card := by
          have := midQ_card hn
          exact Nat.mul_le_mul_right _ this
      _ = 4 * ((midQ n).card * (rowBad Bad n q).card) := by ring
      _ ≤ 4 * H := Nat.mul_le_mul_left _ hrowq
  · calc n * (pathBad Bad n q j).card ≤ 7 * (midJ q).card * (pathBad Bad n q j).card := by
          have := midJ_card hn hq
          exact Nat.mul_le_mul_right _ this
      _ = 7 * ((midJ q).card * (pathBad Bad n q j).card) := by ring
      _ ≤ 7 * H := Nat.mul_le_mul_left _ hpathj

end Selection

set_option maxHeartbeats 1000000 in
theorem seq_propagation {M : ℕ} (s : ℕ → ℕ) (d : ℕ → ℤ) (A B : ℕ → ℕ)
    (hs : ∀ i, i ≤ M → 0 < s i)
    (hB : ∀ i, i < M → 0 < B i)
    (hrel : ∀ i, i < M → A i * s i = B i * s (i + 1))
    (hd : ∀ i, i < M → (B i : ℤ) * d (i + 1) = (A i : ℤ) * d i) :
    ∀ i, i ≤ M → ∀ j, j ≤ M → d i * (s j : ℤ) = d j * (s i : ℤ) := by

  have hstep : ∀ i, i < M → d i * (s (i + 1) : ℤ) = d (i + 1) * (s i : ℤ) := by
    intro i hi
    have h1 : (A i : ℤ) * (s i : ℤ) = (B i : ℤ) * (s (i + 1) : ℤ) := by
      exact_mod_cast hrel i hi
    have h2 := hd i hi
    have hBpos : (0 : ℤ) < (B i : ℤ) := by exact_mod_cast hB i hi

    have h3 : (B i : ℤ) * (d i * (s (i + 1) : ℤ)) = (B i : ℤ) * (d (i + 1) * (s i : ℤ)) := by
      calc (B i : ℤ) * (d i * (s (i + 1) : ℤ))
          = d i * ((B i : ℤ) * (s (i + 1) : ℤ)) := by ring
        _ = d i * ((A i : ℤ) * (s i : ℤ)) := by rw [← h1]
        _ = ((B i : ℤ) * d (i + 1)) * (s i : ℤ) := by rw [h2]; ring
        _ = (B i : ℤ) * (d (i + 1) * (s i : ℤ)) := by ring
    exact mul_left_cancel₀ hBpos.ne' h3

  have hzero : ∀ i, i ≤ M → d 0 * (s i : ℤ) = d i * (s 0 : ℤ) := by
    intro i
    induction i with
    | zero => intro _; ring
    | succ k ih =>
      intro hk
      have hk' : k ≤ M := by omega
      have hkM : k < M := by omega
      have h1 := ih hk'
      have h2 := hstep k hkM
      have hskpos : (0 : ℤ) < (s k : ℤ) := by exact_mod_cast hs k hk'

      have h3 : (d 0 * (s (k + 1) : ℤ)) * (s k : ℤ) = (d (k + 1) * (s 0 : ℤ)) * (s k : ℤ) := by
        calc (d 0 * (s (k + 1) : ℤ)) * (s k : ℤ)
            = (d 0 * (s k : ℤ)) * (s (k + 1) : ℤ) := by ring
          _ = (d k * (s 0 : ℤ)) * (s (k + 1) : ℤ) := by rw [h1]
          _ = (s 0 : ℤ) * (d k * (s (k + 1) : ℤ)) := by ring
          _ = (s 0 : ℤ) * (d (k + 1) * (s k : ℤ)) := by rw [h2]
          _ = (d (k + 1) * (s 0 : ℤ)) * (s k : ℤ) := by ring
      exact mul_right_cancel₀ hskpos.ne' h3
  intro i hi j hj
  have h1 := hzero i hi
  have h2 := hzero j hj
  have hs0pos : (0 : ℤ) < (s 0 : ℤ) := by exact_mod_cast hs 0 (by omega)
  have h3 : (d i * (s j : ℤ)) * (s 0 : ℤ) = (d j * (s i : ℤ)) * (s 0 : ℤ) := by
    calc (d i * (s j : ℤ)) * (s 0 : ℤ)
        = (d i * (s 0 : ℤ)) * (s j : ℤ) := by ring
      _ = (d 0 * (s i : ℤ)) * (s j : ℤ) := by rw [← h1]
      _ = (d 0 * (s j : ℤ)) * (s i : ℤ) := by ring
      _ = (d j * (s 0 : ℤ)) * (s i : ℤ) := by rw [h2]
      _ = (d j * (s i : ℤ)) * (s 0 : ℤ) := by ring
  exact mul_right_cancel₀ hs0pos.ne' h3

set_option maxHeartbeats 1000000 in
theorem dvd_of_cross {s₀ s₁ s₂ s₃ : ℕ} {d₀ d₁ d₂ d₃ : ℤ}
    (hgcd : Nat.gcd (Nat.gcd s₁ s₂) s₃ = 1)
    (h1 : d₀ * (s₁ : ℤ) = d₁ * (s₀ : ℤ))
    (h2 : d₀ * (s₂ : ℤ) = d₂ * (s₀ : ℤ))
    (h3 : d₀ * (s₃ : ℤ) = d₃ * (s₀ : ℤ)) :
    (s₀ : ℤ) ∣ d₀ := by

  have hb1 : (Nat.gcd s₁ s₂ : ℤ) = s₁ * Nat.gcdA s₁ s₂ + s₂ * Nat.gcdB s₁ s₂ :=
    Nat.gcd_eq_gcd_ab s₁ s₂
  have hb2 : (Nat.gcd (Nat.gcd s₁ s₂) s₃ : ℤ)
      = (Nat.gcd s₁ s₂ : ℤ) * Nat.gcdA (Nat.gcd s₁ s₂) s₃
        + s₃ * Nat.gcdB (Nat.gcd s₁ s₂) s₃ :=
    Nat.gcd_eq_gcd_ab (Nat.gcd s₁ s₂) s₃
  set u : ℤ := Nat.gcdA s₁ s₂ * Nat.gcdA (Nat.gcd s₁ s₂) s₃ with hu
  set v : ℤ := Nat.gcdB s₁ s₂ * Nat.gcdA (Nat.gcd s₁ s₂) s₃ with hv
  set w : ℤ := Nat.gcdB (Nat.gcd s₁ s₂) s₃ with hw
  have hone : (1 : ℤ) = (s₁ : ℤ) * u + (s₂ : ℤ) * v + (s₃ : ℤ) * w := by
    have hcast : ((Nat.gcd (Nat.gcd s₁ s₂) s₃ : ℕ) : ℤ) = 1 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hgcd
    calc (1 : ℤ) = (Nat.gcd (Nat.gcd s₁ s₂) s₃ : ℤ) := hcast.symm
      _ = (Nat.gcd s₁ s₂ : ℤ) * Nat.gcdA (Nat.gcd s₁ s₂) s₃
            + s₃ * Nat.gcdB (Nat.gcd s₁ s₂) s₃ := hb2
      _ = (s₁ * Nat.gcdA s₁ s₂ + s₂ * Nat.gcdB s₁ s₂) * Nat.gcdA (Nat.gcd s₁ s₂) s₃
            + s₃ * Nat.gcdB (Nat.gcd s₁ s₂) s₃ := by rw [← hb1]
      _ = (s₁ : ℤ) * u + (s₂ : ℤ) * v + (s₃ : ℤ) * w := by
          simp only [hu, hv, hw]; ring
  refine ⟨d₁ * u + d₂ * v + d₃ * w, ?_⟩
  calc d₀ = d₀ * 1 := (mul_one d₀).symm
    _ = d₀ * ((s₁ : ℤ) * u + (s₂ : ℤ) * v + (s₃ : ℤ) * w) := by rw [← hone]
    _ = (d₀ * (s₁ : ℤ)) * u + (d₀ * (s₂ : ℤ)) * v + (d₀ * (s₃ : ℤ)) * w := by ring
    _ = (d₁ * (s₀ : ℤ)) * u + (d₂ * (s₀ : ℤ)) * v + (d₃ * (s₀ : ℤ)) * w := by
        rw [h1, h2, h3]
    _ = (s₀ : ℤ) * (d₁ * u + d₂ * v + d₃ * w) := by ring

set_option maxHeartbeats 1000000 in
theorem chain_dvd {q P : ℕ} (rS pS : ℕ → ℕ) (rd pd : ℕ → ℤ)
    (rA rB pA pB : ℕ → ℕ)
    (hrs : ∀ i, i ≤ q → 0 < rS i) (hps : ∀ s, s ≤ P → 0 < pS s)
    (hrB : ∀ i, i < q → 0 < rB i) (hpB : ∀ s, s < P → 0 < pB s)
    (hrrel : ∀ i, i < q → rA i * rS i = rB i * rS (i + 1))
    (hprel : ∀ s, s < P → pA s * pS s = pB s * pS (s + 1))
    (hrd : ∀ i, i < q → (rB i : ℤ) * rd (i + 1) = (rA i : ℤ) * rd i)
    (hpd : ∀ s, s < P → (pB s : ℤ) * pd (s + 1) = (pA s : ℤ) * pd s)
    (j : ℕ) (hj : j ≤ q)
    (hjunc_s : pS 0 = rS j) (hjunc_d : pd 0 = rd j)
    (hgcd : Nat.gcd (Nat.gcd (rS 0) (rS q)) (pS P) = 1) :
    (rS 0 : ℤ) ∣ rd 0 := by
  have hrow := seq_propagation rS rd rA rB hrs hrB hrrel hrd
  have hpath := seq_propagation pS pd pA pB hps hpB hprel hpd

  have hcross2 : rd 0 * (rS q : ℤ) = rd q * (rS 0 : ℤ) :=
    hrow 0 (by omega) q (by omega)

  have hpj : pd 0 * (pS P : ℤ) = pd P * (pS 0 : ℤ) :=
    hpath 0 (by omega) P (by omega)
  have hrj : rd 0 * (rS j : ℤ) = rd j * (rS 0 : ℤ) :=
    hrow 0 (by omega) j hj
  have hsjpos : (0 : ℤ) < (rS j : ℤ) := by exact_mod_cast hrs j hj
  have hcross3 : rd 0 * (pS P : ℤ) = pd P * (rS 0 : ℤ) := by
    have h1 : (rd 0 * (pS P : ℤ)) * (rS j : ℤ) = (pd P * (rS 0 : ℤ)) * (rS j : ℤ) := by
      calc (rd 0 * (pS P : ℤ)) * (rS j : ℤ)
          = (rd 0 * (rS j : ℤ)) * (pS P : ℤ) := by ring
        _ = (rd j * (rS 0 : ℤ)) * (pS P : ℤ) := by rw [hrj]
        _ = (rS 0 : ℤ) * (rd j * (pS P : ℤ)) := by ring
        _ = (rS 0 : ℤ) * (pd 0 * (pS P : ℤ)) := by rw [hjunc_d]
        _ = (rS 0 : ℤ) * (pd P * (pS 0 : ℤ)) := by rw [hpj]
        _ = (rS 0 : ℤ) * (pd P * (rS j : ℤ)) := by rw [hjunc_s]
        _ = (pd P * (rS 0 : ℤ)) * (rS j : ℤ) := by ring
    exact mul_right_cancel₀ hsjpos.ne' h1
  exact dvd_of_cross hgcd (by ring) hcross2 hcross3

section CornerGcd

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
theorem corner_gcd_eq_one (hco : PairwiseCoprime3 a b c)
    (l₁ m₁ k₂ m₂ k₃ l₃ : ℕ) :
    Nat.gcd (Nat.gcd (b ^ l₁ * c ^ m₁) (a ^ k₂ * c ^ m₂)) (a ^ k₃ * b ^ l₃) = 1 := by
  obtain ⟨hab, hac, hbc⟩ := hco
  have hcop : Nat.Coprime (Nat.gcd (b ^ l₁ * c ^ m₁) (a ^ k₂ * c ^ m₂)) (a ^ k₃ * b ^ l₃) := by
    apply Nat.Coprime.mul_right
    ·
      apply Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      exact Nat.Coprime.mul (hab.symm.pow l₁ k₃) (hac.symm.pow m₁ k₃)
    ·
      apply Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
      exact Nat.Coprime.mul (hab.pow k₂ l₃) (hbc.symm.pow m₂ l₃)
  exact hcop

end CornerGcd

section EdgeCoeffs

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
def edgeA (a b c : ℕ) (e e' : ℕ × ℕ × ℕ) : ℕ :=
  a ^ (e'.1 - e.1) * b ^ (e'.2.1 - e.2.1) * c ^ (e'.2.2 - e.2.2)

set_option maxHeartbeats 1000000 in
lemma edgeA_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (e e' : ℕ × ℕ × ℕ) :
    0 < edgeA a b c e e' := by
  unfold edgeA
  positivity

set_option maxHeartbeats 1000000 in
lemma edgeA_mul_wt (a b c : ℕ) (e e' : ℕ × ℕ × ℕ) :
    edgeA a b c e e' * wt a b c e = edgeA a b c e' e * wt a b c e' := by
  unfold edgeA wt
  have h1 : e'.1 - e.1 + e.1 = e.1 - e'.1 + e'.1 := by omega
  have h2 : e'.2.1 - e.2.1 + e.2.1 = e.2.1 - e'.2.1 + e'.2.1 := by omega
  have h3 : e'.2.2 - e.2.2 + e.2.2 = e.2.2 - e'.2.2 + e'.2.2 := by omega
  calc a ^ (e'.1 - e.1) * b ^ (e'.2.1 - e.2.1) * c ^ (e'.2.2 - e.2.2)
        * (a ^ e.1 * b ^ e.2.1 * c ^ e.2.2)
      = a ^ (e'.1 - e.1 + e.1) * b ^ (e'.2.1 - e.2.1 + e.2.1)
          * c ^ (e'.2.2 - e.2.2 + e.2.2) := by
        rw [pow_add, pow_add, pow_add]; ring
    _ = a ^ (e.1 - e'.1 + e'.1) * b ^ (e.2.1 - e'.2.1 + e'.2.1)
          * c ^ (e.2.2 - e'.2.2 + e'.2.2) := by rw [h1, h2, h3]
    _ = a ^ (e.1 - e'.1) * b ^ (e.2.1 - e'.2.1) * c ^ (e.2.2 - e'.2.2)
          * (a ^ e'.1 * b ^ e'.2.1 * c ^ e'.2.2) := by
        rw [pow_add, pow_add, pow_add]; ring

set_option maxHeartbeats 1000000 in
lemma edgeA_le (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) {D : ℕ} {e e' : ℕ × ℕ × ℕ}
    (h1 : e'.1 ≤ e.1 + D) (h2 : e'.2.1 ≤ e.2.1 + D) (h3 : e'.2.2 ≤ e.2.2 + D) :
    edgeA a b c e e' ≤ (a * b * c) ^ D := by
  unfold edgeA
  have e1 : a ^ (e'.1 - e.1) ≤ a ^ D := Nat.pow_le_pow_right ha (by omega)
  have e2 : b ^ (e'.2.1 - e.2.1) ≤ b ^ D := Nat.pow_le_pow_right hb (by omega)
  have e3 : c ^ (e'.2.2 - e.2.2) ≤ c ^ D := Nat.pow_le_pow_right hc (by omega)
  calc a ^ (e'.1 - e.1) * b ^ (e'.2.1 - e.2.1) * c ^ (e'.2.2 - e.2.2)
      ≤ a ^ D * b ^ D * c ^ D := by
        apply Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
    _ = (a * b * c) ^ D := by rw [mul_pow, mul_pow]

end EdgeCoeffs

end Erdos123Band
end Module_Routing

section Module_Rigidity

namespace Erdos123Band

set_option maxHeartbeats 1000000 in
noncomputable def TriF (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  letI := Classical.decPred (fun v : ℕ × ℕ × ℕ => v ∈ Tri n)
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun v => v ∈ Tri n)

set_option maxHeartbeats 1000000 in
lemma mem_TriF {n : ℕ} {v : ℕ × ℕ × ℕ} : v ∈ TriF n ↔ v ∈ Tri n := by
  unfold TriF
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    have hs := Tri_sum h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

set_option maxHeartbeats 1000000 in
lemma badF_card_le (a b c x n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (t δ : ℝ) (hδ : 0 < δ)
    (hband : ∀ v ∈ Tri n, wt a b c (Φ v) ∈ Band a b c x)
    (hinj : ∀ v ∈ Tri n, ∀ w ∈ Tri n, wt a b c (Φ v) = wt a b c (Φ w) → v = w) :
    (((TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|)).card : ℝ) * δ ^ 2 ≤ Qenergy a b c x t := by
  classical
  set F : Finset (ℕ × ℕ × ℕ) := (TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) with hFdef
  have hFT : ∀ v ∈ F, v ∈ Tri n := fun v hv => mem_TriF.mp (Finset.mem_filter.mp hv).1
  have hFbad : ∀ v ∈ F, δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| :=
    fun v hv => (Finset.mem_filter.mp hv).2
  set G : Finset ℕ := F.image (fun v => wt a b c (Φ v)) with hGdef
  have hGcard : G.card = F.card := by
    rw [hGdef]
    apply Finset.card_image_of_injOn
    intro v hv w hw hvw
    exact hinj v (hFT v hv) w (hFT w hw) hvw
  have hGsub : G ⊆ Band a b c x := by
    intro s hs
    rw [hGdef] at hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    exact hband v (hFT v hv)
  have hGterm : ∀ s ∈ G, δ ^ 2 ≤ ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := by
    intro s hs
    rw [hGdef] at hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    have h1 := hFbad v hv
    calc δ ^ 2
        ≤ |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| ^ 2 :=
          pow_le_pow_left₀ hδ.le h1.le 2
      _ = ((wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)) ^ 2 := sq_abs _
  have h1 : (G.card : ℝ) * δ ^ 2 ≤ ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := by
    have h := Finset.card_nsmul_le_sum G
      (fun s => ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2) (δ ^ 2) hGterm
    rwa [nsmul_eq_mul] at h
  have h2 : ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 ≤ Qenergy a b c x t := by
    unfold Qenergy
    exact Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun s _ _ => sq_nonneg _)
  calc (F.card : ℝ) * δ ^ 2
      = (G.card : ℝ) * δ ^ 2 := by rw [hGcard]
    _ ≤ ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := h1
    _ ≤ Qenergy a b c x t := h2

set_option maxHeartbeats 1000000 in
lemma edge_defect_zero {K : ℕ} {t δ : ℝ} (hδ : 0 < δ) (hKδ : (K : ℝ) * δ ≤ 1 / 4)
    {A B S S' : ℕ} (hrel : A * S = B * S') (hAK : A ≤ K) (hBK : B ≤ K)
    (hS : |(S : ℝ) * t - round ((S : ℝ) * t)| ≤ δ)
    (hS' : |(S' : ℝ) * t - round ((S' : ℝ) * t)| ≤ δ) :
    (B : ℤ) * round ((S' : ℝ) * t) = (A : ℤ) * round ((S : ℝ) * t) := by
  set d : ℤ := round ((S : ℝ) * t) with hd
  set d' : ℤ := round ((S' : ℝ) * t) with hd'
  have hAR : (A : ℝ) ≤ (K : ℝ) := by exact_mod_cast hAK
  have hBR : (B : ℝ) ≤ (K : ℝ) := by exact_mod_cast hBK
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hrelR : (A : ℝ) * (S : ℝ) = (B : ℝ) * (S' : ℝ) := by exact_mod_cast hrel
  set E : ℤ := B * d' - A * d with hE
  have hid : (E : ℝ)
      = (B : ℝ) * ((d' : ℝ) - (S' : ℝ) * t) - (A : ℝ) * ((d : ℝ) - (S : ℝ) * t) := by
    have hexp : (E : ℝ) = (B : ℝ) * (d' : ℝ) - (A : ℝ) * (d : ℝ) := by
      rw [hE]; push_cast; ring
    have h2 : (B : ℝ) * ((S' : ℝ) * t) = (A : ℝ) * ((S : ℝ) * t) := by
      rw [← mul_assoc, ← mul_assoc, ← hrelR]
    rw [hexp]; linarith [h2]
  have hSd : |(d : ℝ) - (S : ℝ) * t| ≤ δ := by rw [abs_sub_comm]; exact hS
  have hSd' : |(d' : ℝ) - (S' : ℝ) * t| ≤ δ := by rw [abs_sub_comm]; exact hS'
  have hu := abs_le.mp hSd
  have hu' := abs_le.mp hSd'
  have hB1 : (B : ℝ) * ((d' : ℝ) - (S' : ℝ) * t) ≤ (B : ℝ) * δ :=
    mul_le_mul_of_nonneg_left hu'.2 hB0
  have hB2 : (B : ℝ) * (-δ) ≤ (B : ℝ) * ((d' : ℝ) - (S' : ℝ) * t) :=
    mul_le_mul_of_nonneg_left hu'.1 hB0
  have hA1 : (A : ℝ) * ((d : ℝ) - (S : ℝ) * t) ≤ (A : ℝ) * δ :=
    mul_le_mul_of_nonneg_left hu.2 hA0
  have hA2 : (A : ℝ) * (-δ) ≤ (A : ℝ) * ((d : ℝ) - (S : ℝ) * t) :=
    mul_le_mul_of_nonneg_left hu.1 hA0
  have hBδ : (B : ℝ) * δ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_right hBR hδ.le
  have hAδ : (A : ℝ) * δ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_right hAR hδ.le
  have hEbound : |(E : ℝ)| ≤ 1 / 2 := by
    rw [hid, abs_le]
    constructor
    · linarith [hB2, hA1, hBδ, hAδ, hKδ]
    · linarith [hB1, hA2, hBδ, hAδ, hKδ]
  have hE1 : |(E : ℝ)| < 1 := lt_of_le_of_lt hEbound (by norm_num)
  have hE1' : ((|E| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hE1
  have hE1'' : |E| < 1 := by exact_mod_cast hE1'
  have hE0 : E = 0 := by
    have h := abs_lt.mp hE1''
    omega
  have hfin : (B : ℤ) * d' - (A : ℤ) * d = 0 := by rw [← hE]; exact hE0
  linarith [hfin]

set_option maxHeartbeats 1000000 in
theorem lemma_5_2' (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ κ₀ : ℝ, ∃ X₅ : ℕ, 0 < κ₀ ∧ ∀ x : ℕ, X₅ ≤ x → ∀ t : ℝ,
      t ∈ MinorArc x → κ₀ * Real.log x ≤ Qenergy a b c x t := by
  classical
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  obtain ⟨c₀, C₀, D, hc₀, -, hD1, X₀g, -, hgrid⟩ :=
    grid_embedding (a := a) (b := b) (c := c) (by omega) (by omega) (by omega) hco

  set K : ℕ := (a * b * c) ^ D with hKdef
  have habc8 : 8 ≤ a * b * c := by
    calc 8 = 2 * 2 * 2 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hK8 : 8 ≤ K := by
    rw [hKdef]
    calc 8 ≤ a * b * c := habc8
      _ = (a * b * c) ^ 1 := (pow_one _).symm
      _ ≤ (a * b * c) ^ D := Nat.pow_le_pow_right (le_trans (by norm_num) habc8) hD1
  have hKR : (8 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK8
  have hK0R : (0 : ℝ) < (K : ℝ) := by linarith
  have h4K0 : (0 : ℝ) < 4 * (K : ℝ) := by linarith
  set δ : ℝ := 1 / (4 * (K : ℝ)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos h4K0
  have hδ32 : δ ≤ 1 / 32 := by
    rw [hδdef, div_le_div_iff₀ h4K0 (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hKδeq : (K : ℝ) * δ = 1 / 4 := by
    rw [hδdef, mul_one_div, div_eq_div_iff h4K0.ne' (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  have hKδ : (K : ℝ) * δ ≤ 1 / 4 := le_of_eq hKδeq
  set κ₀ : ℝ := c₀ * δ ^ 2 / 9 with hκdef
  have hκpos : 0 < κ₀ := by
    rw [hκdef]
    exact div_pos (mul_pos hc₀ (pow_pos hδpos 2)) (by norm_num)
  refine ⟨κ₀, max X₀g (max 3 ⌈Real.exp (96 / c₀)⌉₊), hκpos, fun x hx t ht => ?_⟩

  have hxX₀g : X₀g ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_left 3 _) (le_max_right X₀g _)) hx
  have hx0 : 0 < x := by omega
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hxceil : ⌈Real.exp (96 / c₀)⌉₊ ≤ x :=
    le_trans (le_trans (le_max_right 3 _) (le_max_right X₀g _)) hx
  have hxceilR : Real.exp (96 / c₀) ≤ (x : ℝ) := by
    calc Real.exp (96 / c₀) ≤ (⌈Real.exp (96 / c₀)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := by exact_mod_cast hxceil
  have hL96 : 96 / c₀ ≤ Real.log x := by
    calc 96 / c₀ = Real.log (Real.exp (96 / c₀)) := (Real.log_exp _).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxceilR
  have h96 : (96 : ℝ) ≤ c₀ * Real.log x := by
    have h1 := (div_le_iff₀ hc₀).mp hL96
    linarith

  by_contra hcon
  push_neg at hcon

  obtain ⟨n, Φ, ⟨hnlo, -⟩, hband, hinj, hface, hjump⟩ := hgrid x hxX₀g
  have hn96R : (96 : ℝ) ≤ (n : ℝ) := le_trans h96 hnlo
  have hn96 : 96 ≤ n := by exact_mod_cast hn96R
  have hn48 : 48 ≤ n := by omega

  have hQb := badF_card_le a b c x n Φ t δ hδpos hband hinj
  set H : ℕ := ((TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|)).card with hHdef
  rw [hκdef] at hcon
  have hδsq : (0 : ℝ) < δ ^ 2 := pow_pos hδpos 2
  have hH9R : (H : ℝ) * 9 < (n : ℝ) := by
    have h1 : (H : ℝ) * δ ^ 2 < c₀ * δ ^ 2 / 9 * Real.log x := lt_of_le_of_lt hQb hcon
    have h2 : ((H : ℝ) * 9) * δ ^ 2 < (c₀ * Real.log x) * δ ^ 2 := by nlinarith [h1]
    have h3 : (H : ℝ) * 9 < c₀ * Real.log x := lt_of_mul_lt_mul_right h2 hδsq.le
    linarith [hnlo]
  have hH9 : 9 * H < n := by
    have h3 : ((9 * H : ℕ) : ℝ) < (n : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hH8 : 8 * H < n := by omega

  have hHbound : ∀ F : Finset (ℕ × ℕ × ℕ),
      (∀ v ∈ F, v ∈ Tri n ∧ δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) → F.card ≤ H := by
    intro F hF
    rw [hHdef]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvT, hvB⟩ := hF v hv
    exact Finset.mem_filter.mpr ⟨mem_TriF.mpr hvT, hvB⟩
  obtain ⟨q, hq, j, hj, hrow4, hpath7⟩ :=
    exists_sparse_row_and_path hn48
      (fun v => δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)|)
      H hHbound
  have hjq : j ≤ q := by
    have h := (midJ_bounds hj).2
    omega

  have hrow0 : (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) n q).card = 0 := by
    by_contra hne
    have h1 : 1 ≤ (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q).card := Nat.pos_of_ne_zero hne
    have h2 : n ≤ 4 * H := by
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
            - round ((wt a b c (Φ v) : ℝ) * t)|) n q).card := Nat.mul_le_mul_left n h1
        _ ≤ 4 * H := hrow4
    omega
  have hpath0 : (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) n q j).card = 0 := by
    by_contra hne
    have h1 : 1 ≤ (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q j).card := Nat.pos_of_ne_zero hne
    have h2 : n ≤ 7 * H := by
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
            - round ((wt a b c (Φ v) : ℝ) * t)|) n q j).card := Nat.mul_le_mul_left n h1
        _ ≤ 7 * H := hpath7
    omega

  have hrowGood : ∀ i, i ≤ q →
      |(wt a b c (Φ (rowV n q i)) : ℝ) * t
        - round ((wt a b c (Φ (rowV n q i)) : ℝ) * t)| ≤ δ := by
    intro i hi
    by_contra hbad
    push_neg at hbad
    have hmem : i ∈ rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q := by
      simp only [rowBad, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hbad⟩
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  have hpathGood : ∀ s, s ≤ n - q →
      |(wt a b c (Φ (pathV n q j s)) : ℝ) * t
        - round ((wt a b c (Φ (pathV n q j s)) : ℝ) * t)| ≤ δ := by
    intro s hs
    by_contra hbad
    push_neg at hbad
    have hmem : s ∈ pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q j := by
      simp only [pathBad, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hbad⟩
    have hpos := Finset.card_pos.mpr ⟨s, hmem⟩
    omega

  have hrS_ge : ∀ i, i ≤ q → x ≤ wt a b c (Φ (rowV n q i)) := fun i hi =>
    (mem_Band.mp (hband _ (rowV_mem_Tri hn48 hq hi))).2.1
  have hrs : ∀ i, i ≤ q → 0 < wt a b c (Φ (rowV n q i)) := fun i hi =>
    lt_of_lt_of_le hx0 (hrS_ge i hi)
  have hpS_ge : ∀ s, s ≤ n - q → x ≤ wt a b c (Φ (pathV n q j s)) := fun s hs =>
    (mem_Band.mp (hband _ (pathV_mem_Tri hn48 hq hj hs))).2.1
  have hps : ∀ s, s ≤ n - q → 0 < wt a b c (Φ (pathV n q j s)) := fun s hs =>
    lt_of_lt_of_le hx0 (hpS_ge s hs)

  have hrB : ∀ i, i < q → 0 < edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i)) :=
    fun i _ => edgeA_pos (by omega) (by omega) (by omega) _ _
  have hpB : ∀ s, s < n - q → 0 < edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s)) :=
    fun s _ => edgeA_pos (by omega) (by omega) (by omega) _ _
  have hrrel : ∀ i, i < q →
      edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))) * wt a b c (Φ (rowV n q i))
        = edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i))
          * wt a b c (Φ (rowV n q (i + 1))) :=
    fun i _ => edgeA_mul_wt a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1)))
  have hprel : ∀ s, s < n - q →
      edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))) * wt a b c (Φ (pathV n q j s))
        = edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s))
          * wt a b c (Φ (pathV n q j (s + 1))) :=
    fun s _ => edgeA_mul_wt a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1)))

  have hrd : ∀ i, i < q →
      (edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i)) : ℤ)
          * round ((wt a b c (Φ (rowV n q (i + 1))) : ℝ) * t)
        = (edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))) : ℤ)
          * round ((wt a b c (Φ (rowV n q i)) : ℝ) * t) := by
    intro i hi
    have hm1 : rowV n q i ∈ Tri n := rowV_mem_Tri hn48 hq (by omega)
    have hm2 : rowV n q (i + 1) ∈ Tri n := rowV_mem_Tri hn48 hq (by omega)
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjump _ hm1 _ hm2 (rowV_adjacent (by omega))
    exact edge_defect_zero hδpos hKδ
      (edgeA_mul_wt a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))))
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j2 j4 j6)
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j1 j3 j5)
      (hrowGood i (by omega)) (hrowGood (i + 1) (by omega))
  have hpd : ∀ s, s < n - q →
      (edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s)) : ℤ)
          * round ((wt a b c (Φ (pathV n q j (s + 1))) : ℝ) * t)
        = (edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))) : ℤ)
          * round ((wt a b c (Φ (pathV n q j s)) : ℝ) * t) := by
    intro s hs
    have hm1 : pathV n q j s ∈ Tri n := pathV_mem_Tri hn48 hq hj (by omega)
    have hm2 : pathV n q j (s + 1) ∈ Tri n := pathV_mem_Tri hn48 hq hj (by omega)
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjump _ hm1 _ hm2 (pathV_adjacent hjq (by omega))
    exact edge_defect_zero hδpos hKδ
      (edgeA_mul_wt a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))))
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j2 j4 j6)
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j1 j3 j5)
      (hpathGood s (by omega)) (hpathGood (s + 1) (by omega))

  have hjunc_s : wt a b c (Φ (pathV n q j 0)) = wt a b c (Φ (rowV n q (q - j))) := by
    rw [pathV_zero hjq]
  have hjunc_d : round ((wt a b c (Φ (pathV n q j 0)) : ℝ) * t)
      = round ((wt a b c (Φ (rowV n q (q - j))) : ℝ) * t) := by
    rw [hjunc_s]

  have hmem0 : rowV n q 0 ∈ Tri n := rowV_mem_Tri hn48 hq (Nat.zero_le q)
  have hmemq : rowV n q q ∈ Tri n := rowV_mem_Tri hn48 hq (le_refl q)
  have hmemP : pathV n q j (n - q) ∈ Tri n := pathV_mem_Tri hn48 hq hj (le_refl (n - q))
  have hk0 : (Φ (rowV n q 0)).1 = 0 := (hface _ hmem0).1 (by simp [rowV])
  have hl0 : (Φ (rowV n q q)).2.1 = 0 := (hface _ hmemq).2.1 (by simp [rowV])
  have hm0 : (Φ (pathV n q j (n - q))).2.2 = 0 := (hface _ hmemP).2.2 (by simp [pathV])
  have hw0 : wt a b c (Φ (rowV n q 0))
      = b ^ (Φ (rowV n q 0)).2.1 * c ^ (Φ (rowV n q 0)).2.2 := by
    rw [wt, hk0, pow_zero, one_mul]
  have hwq : wt a b c (Φ (rowV n q q))
      = a ^ (Φ (rowV n q q)).1 * c ^ (Φ (rowV n q q)).2.2 := by
    rw [wt, hl0, pow_zero, mul_one]
  have hwP : wt a b c (Φ (pathV n q j (n - q)))
      = a ^ (Φ (pathV n q j (n - q))).1 * b ^ (Φ (pathV n q j (n - q))).2.1 := by
    rw [wt, hm0, pow_zero, mul_one]
  have hgcd : Nat.gcd (Nat.gcd (wt a b c (Φ (rowV n q 0))) (wt a b c (Φ (rowV n q q))))
      (wt a b c (Φ (pathV n q j (n - q)))) = 1 := by
    rw [hw0, hwq, hwP]
    exact corner_gcd_eq_one hco _ _ _ _ _ _

  have hdvd : (wt a b c (Φ (rowV n q 0)) : ℤ)
      ∣ round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t) :=
    chain_dvd (q := q) (P := n - q)
      (fun i => wt a b c (Φ (rowV n q i)))
      (fun s => wt a b c (Φ (pathV n q j s)))
      (fun i => round ((wt a b c (Φ (rowV n q i)) : ℝ) * t))
      (fun s => round ((wt a b c (Φ (pathV n q j s)) : ℝ) * t))
      (fun i => edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1))))
      (fun i => edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i)))
      (fun s => edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1))))
      (fun s => edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s)))
      hrs hps hrB hpB hrrel hprel hrd hpd
      (q - j) (Nat.sub_le q j) hjunc_s hjunc_d hgcd
  obtain ⟨r, hr⟩ := hdvd

  have hgood0 : |(wt a b c (Φ (rowV n q 0)) : ℝ) * t
      - round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t)| ≤ δ := hrowGood 0 (Nat.zero_le q)
  have hSxN : x ≤ wt a b c (Φ (rowV n q 0)) := hrS_ge 0 (Nat.zero_le q)
  have hSx : (x : ℝ) ≤ (wt a b c (Φ (rowV n q 0)) : ℝ) := by exact_mod_cast hSxN
  have hS₀pos : (0 : ℝ) < (wt a b c (Φ (rowV n q 0)) : ℝ) := lt_of_lt_of_le hxR hSx
  have hkey : |t - (r : ℝ)| ≤ δ / (x : ℝ) := by
    have hfac : (wt a b c (Φ (rowV n q 0)) : ℝ) * t
        - ((round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t) : ℤ) : ℝ)
        = (wt a b c (Φ (rowV n q 0)) : ℝ) * (t - (r : ℝ)) := by
      rw [hr]; push_cast; ring
    have h1 : (wt a b c (Φ (rowV n q 0)) : ℝ) * |t - (r : ℝ)| ≤ δ := by
      calc (wt a b c (Φ (rowV n q 0)) : ℝ) * |t - (r : ℝ)|
          = |(wt a b c (Φ (rowV n q 0)) : ℝ) * (t - (r : ℝ))| := by
            rw [abs_mul, abs_of_pos hS₀pos]
        _ = |(wt a b c (Φ (rowV n q 0)) : ℝ) * t
              - ((round ((wt a b c (Φ (rowV n q 0)) : ℝ) * t) : ℤ) : ℝ)| := by rw [hfac]
        _ ≤ δ := hgood0
    rw [le_div_iff₀ hxR]
    calc |t - (r : ℝ)| * (x : ℝ)
        ≤ |t - (r : ℝ)| * (wt a b c (Φ (rowV n q 0)) : ℝ) :=
          mul_le_mul_of_nonneg_left hSx (abs_nonneg _)
      _ = (wt a b c (Φ (rowV n q 0)) : ℝ) * |t - (r : ℝ)| := mul_comm _ _
      _ ≤ δ := h1

  simp only [MinorArc, Set.mem_diff] at ht
  obtain ⟨htIoc, htmaj⟩ := ht
  simp only [MajorArc, Set.mem_setOf_eq, not_and, not_or, not_le] at htmaj
  obtain ⟨h1t, h2t⟩ := htmaj htIoc
  have hδx : δ / (x : ℝ) < 1 / (8 * (x : ℝ)) := by
    have h8x : (0 : ℝ) < 8 * (x : ℝ) := by linarith
    rw [div_lt_div_iff₀ hxR h8x]
    have h1 : δ * (8 * (x : ℝ)) ≤ 1 / 32 * (8 * (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hδ32 h8x.le
    linarith
  have habs := abs_le.mp hkey
  rcases le_or_gt r 0 with hr0 | hr1
  · have hrR : (r : ℝ) ≤ 0 := by exact_mod_cast hr0
    linarith [habs.2, h1t, hδx, hrR]
  · have h1r : (1 : ℤ) ≤ r := by omega
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1r
    linarith [habs.1, h2t, hδx, hrR]

end Erdos123Band

end Module_Rigidity

section Module_LowEnergy

open scoped ENNReal

namespace Erdos123Band

set_option maxHeartbeats 1600000 in
lemma round_nonneg_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ round y := by
  rw [round_eq]
  exact Int.floor_nonneg.mpr (by linarith)

set_option maxHeartbeats 1600000 in
lemma round_le_nat {s : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y < (s : ℝ)) : round y ≤ (s : ℤ) := by
  rw [round_eq]
  have h1 : y + 1 / 2 < (s : ℝ) + 1 / 2 := by linarith
  have h2 : ⌊y + 1 / 2⌋ ≤ ⌊(1 : ℝ) / 2 + (s : ℕ)⌋ := by
    apply Int.floor_mono
    push_cast
    linarith
  have h3 : ⌊(1 : ℝ) / 2 + (s : ℕ)⌋ = (s : ℤ) := by
    rw [Int.floor_add_natCast]
    norm_num
  omega

set_option maxHeartbeats 1600000 in
lemma abs_sub_le_abs_add_abs (u v : ℝ) : |u - v| ≤ |u| + |v| := by
  calc |u - v| = |u + -v| := by ring_nf
    _ ≤ |u| + |-v| := abs_add_le _ _
    _ = |u| + |v| := by rw [abs_neg]

set_option maxHeartbeats 1600000 in
lemma choose_le_succ_pow (n : ℕ) : ∀ k, Nat.choose n k ≤ (n + 1) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    have hid : Nat.choose n (m + 1) * (m + 1) = Nat.choose n m * (n - m) :=
      Nat.choose_succ_right_eq n m
    have h1 : Nat.choose n (m + 1) ≤ Nat.choose n (m + 1) * (m + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    calc Nat.choose n (m + 1) ≤ Nat.choose n m * (n - m) := by omega
      _ ≤ (n + 1) ^ m * (n + 1) := by
          apply Nat.mul_le_mul ih (by omega)
      _ = (n + 1) ^ (m + 1) := (pow_succ _ _).symm

section LowEnergy

variable {a b c : ℕ}

set_option maxHeartbeats 1600000 in
def rwS (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) : ℕ → ℕ :=
  fun i => wt a b c (Φ (rowV n q i))

set_option maxHeartbeats 1600000 in
def pwS (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) : ℕ → ℕ :=
  fun s => wt a b c (Φ (pathV n q j s))

set_option maxHeartbeats 1600000 in
def rwA (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) : ℕ → ℕ :=
  fun i => edgeA a b c (Φ (rowV n q i)) (Φ (rowV n q (i + 1)))

set_option maxHeartbeats 1600000 in
def rwB (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) : ℕ → ℕ :=
  fun i => edgeA a b c (Φ (rowV n q (i + 1))) (Φ (rowV n q i))

set_option maxHeartbeats 1600000 in
def pwA (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) : ℕ → ℕ :=
  fun s => edgeA a b c (Φ (pathV n q j s)) (Φ (pathV n q j (s + 1)))

set_option maxHeartbeats 1600000 in
def pwB (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) : ℕ → ℕ :=
  fun s => edgeA a b c (Φ (pathV n q j (s + 1))) (Φ (pathV n q j s))

set_option maxHeartbeats 1600000 in
noncomputable def rdv (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun i => round ((rwS a b c n Φ q i : ℝ) * t)

set_option maxHeartbeats 1600000 in
noncomputable def pdv (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun s => round ((pwS a b c n Φ q j s : ℝ) * t)

set_option maxHeartbeats 1600000 in
noncomputable def rdef (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun i => (rwB a b c n Φ q i : ℤ) * rdv a b c n Φ q t (i + 1)
    - (rwA a b c n Φ q i : ℤ) * rdv a b c n Φ q t i

set_option maxHeartbeats 1600000 in
noncomputable def pdef (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) (t : ℝ) : ℕ → ℤ :=
  fun s => (pwB a b c n Φ q j s : ℤ) * pdv a b c n Φ q j t (s + 1)
    - (pwA a b c n Φ q j s : ℤ) * pdv a b c n Φ q j t s

set_option maxHeartbeats 1600000 in
theorem chain_diff_dvd (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c)
    {x n : ℕ} (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (hband : ∀ v ∈ Tri n, wt a b c (Φ v) ∈ Band a b c x)
    (hface : ∀ v ∈ Tri n,
      (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
      (v.2.2 = 0 → (Φ v).2.2 = 0))
    (hx1 : 1 ≤ x) (hn : 48 ≤ n) {q j : ℕ} (hq : q ∈ midQ n) (hj : j ∈ midJ q)
    (t t' : ℝ)
    (hrd : ∀ i, i < q → rdef a b c n Φ q t i = rdef a b c n Φ q t' i)
    (hpd : ∀ s, s < n - q → pdef a b c n Φ q j t s = pdef a b c n Φ q j t' s) :
    (rwS a b c n Φ q 0 : ℤ) ∣ (rdv a b c n Φ q t 0 - rdv a b c n Φ q t' 0) := by
  obtain ⟨hq1, hq2⟩ := midQ_bounds hq
  obtain ⟨hj1, hj2⟩ := midJ_bounds hj
  have hjq : j ≤ q := by omega
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega

  have hrs : ∀ i, i ≤ q → 0 < rwS a b c n Φ q i := by
    intro i hi
    have hmem := hband _ (rowV_mem_Tri hn hq hi)
    have h1 := (mem_Band.mp hmem).2.1
    show 0 < wt a b c (Φ (rowV n q i))
    omega
  have hps : ∀ s, s ≤ n - q → 0 < pwS a b c n Φ q j s := by
    intro s hs
    have hmem := hband _ (pathV_mem_Tri hn hq hj hs)
    have h1 := (mem_Band.mp hmem).2.1
    show 0 < wt a b c (Φ (pathV n q j s))
    omega

  have hrB : ∀ i, i < q → 0 < rwB a b c n Φ q i := by
    intro i _
    exact edgeA_pos ha0 hb0 hc0 _ _
  have hpB : ∀ s, s < n - q → 0 < pwB a b c n Φ q j s := by
    intro s _
    exact edgeA_pos ha0 hb0 hc0 _ _

  have hrrel : ∀ i, i < q →
      rwA a b c n Φ q i * rwS a b c n Φ q i
        = rwB a b c n Φ q i * rwS a b c n Φ q (i + 1) := by
    intro i _
    exact edgeA_mul_wt a b c _ _
  have hprel : ∀ s, s < n - q →
      pwA a b c n Φ q j s * pwS a b c n Φ q j s
        = pwB a b c n Φ q j s * pwS a b c n Φ q j (s + 1) := by
    intro s _
    exact edgeA_mul_wt a b c _ _

  set Δr : ℕ → ℤ := fun i => rdv a b c n Φ q t i - rdv a b c n Φ q t' i with hΔr
  set Δp : ℕ → ℤ := fun s => pdv a b c n Φ q j t s - pdv a b c n Φ q j t' s with hΔp
  have hrdΔ : ∀ i, i < q →
      (rwB a b c n Φ q i : ℤ) * Δr (i + 1) = (rwA a b c n Φ q i : ℤ) * Δr i := by
    intro i hi
    have h := hrd i hi
    simp only [rdef] at h
    simp only [hΔr]
    linear_combination h
  have hpdΔ : ∀ s, s < n - q →
      (pwB a b c n Φ q j s : ℤ) * Δp (s + 1) = (pwA a b c n Φ q j s : ℤ) * Δp s := by
    intro s hs
    have h := hpd s hs
    simp only [pdef] at h
    simp only [hΔp]
    linear_combination h

  have hjuncV : pathV n q j 0 = rowV n q (q - j) := pathV_zero hjq
  have hjunc_s : pwS a b c n Φ q j 0 = rwS a b c n Φ q (q - j) := by
    simp only [pwS, rwS, hjuncV]
  have hjunc_d : Δp 0 = Δr (q - j) := by
    simp only [hΔp, hΔr, pdv, rdv, pwS, rwS, hjuncV]

  have hrow0 : rowV n q 0 = ((0 : ℕ), q, n - q) := by
    simp only [rowV, Nat.sub_zero]
  have hrowq : rowV n q q = (q, (0 : ℕ), n - q) := by
    simp only [rowV, Nat.sub_self]
  have hpathP : pathV n q j (n - q) = (q - j + (n - q), j, (0 : ℕ)) := by
    simp only [pathV, Nat.sub_self]
  have hmem0 : rowV n q 0 ∈ Tri n := rowV_mem_Tri hn hq (by omega)
  have hmemq : rowV n q q ∈ Tri n := rowV_mem_Tri hn hq (le_refl q)
  have hmemP : pathV n q j (n - q) ∈ Tri n := pathV_mem_Tri hn hq hj (le_refl _)
  have hface0 := (hface _ hmem0).1
  have hfaceq := (hface _ hmemq).2.1
  have hfaceP := (hface _ hmemP).2.2
  have hk0 : (Φ (rowV n q 0)).1 = 0 := by
    apply hface0
    rw [hrow0]
  have hl0 : (Φ (rowV n q q)).2.1 = 0 := by
    apply hfaceq
    rw [hrowq]
  have hm0 : (Φ (pathV n q j (n - q))).2.2 = 0 := by
    apply hfaceP
    rw [hpathP]
  have hw0 : rwS a b c n Φ q 0
      = b ^ (Φ (rowV n q 0)).2.1 * c ^ (Φ (rowV n q 0)).2.2 := by
    simp only [rwS, wt, hk0, pow_zero, one_mul]
  have hwq : rwS a b c n Φ q q
      = a ^ (Φ (rowV n q q)).1 * c ^ (Φ (rowV n q q)).2.2 := by
    simp only [rwS, wt, hl0, pow_zero, mul_one]
  have hwP : pwS a b c n Φ q j (n - q)
      = a ^ (Φ (pathV n q j (n - q))).1 * b ^ (Φ (pathV n q j (n - q))).2.1 := by
    simp only [pwS, wt, hm0, pow_zero, mul_one]
  have hgcd : Nat.gcd (Nat.gcd (rwS a b c n Φ q 0) (rwS a b c n Φ q q))
      (pwS a b c n Φ q j (n - q)) = 1 := by
    rw [hw0, hwq, hwP]
    exact corner_gcd_eq_one hco _ _ _ _ _ _
  exact chain_dvd (rwS a b c n Φ q) (pwS a b c n Φ q j) Δr Δp
    (rwA a b c n Φ q) (rwB a b c n Φ q) (pwA a b c n Φ q j) (pwB a b c n Φ q j)
    hrs hps hrB hpB hrrel hprel hrdΔ hpdΔ (q - j) (by omega) hjunc_s hjunc_d hgcd

abbrev CodeT := ℕ × ℕ × Finset (ℕ × ℤ) × Finset (ℕ × ℤ)

set_option maxHeartbeats 1600000 in
noncomputable def DefCodes (n K B : ℕ) : Finset (Finset (ℕ × ℤ)) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.Icc (-(K : ℤ)) (K : ℤ))).powerset.filter
    (fun S => S.card ≤ B)

set_option maxHeartbeats 1600000 in
noncomputable def Codes (n K B : ℕ) : Finset CodeT :=
  (Finset.range (n + 1)) ×ˢ ((Finset.range (n + 1)) ×ˢ
    ((DefCodes n K B) ×ˢ (DefCodes n K B)))

set_option maxHeartbeats 1600000 in
lemma DefCodes_card_le (n K B : ℕ) :
    (DefCodes n K B).card ≤ (B + 1) * ((n + 1) * (2 * K + 2)) ^ B := by
  classical
  set P : Finset (ℕ × ℤ) := (Finset.range (n + 1)) ×ˢ (Finset.Icc (-(K : ℤ)) (K : ℤ))
    with hP
  have hPcard : P.card = (n + 1) * (2 * K + 1) := by
    rw [hP, Finset.card_product, Finset.card_range, Int.card_Icc]
    congr 1
    omega
  have hsub : DefCodes n K B ⊆
      (Finset.range (B + 1)).biUnion (fun k => Finset.powersetCard k P) := by
    intro S hS
    rw [DefCodes, Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.mem_biUnion]
    exact ⟨S.card, by rw [Finset.mem_range]; omega,
      Finset.mem_powersetCard.mpr ⟨hS.1, rfl⟩⟩
  calc (DefCodes n K B).card
      ≤ ((Finset.range (B + 1)).biUnion (fun k => Finset.powersetCard k P)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (B + 1), (Finset.powersetCard k P).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (B + 1), ((n + 1) * (2 * K + 2)) ^ B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        rw [Finset.card_powersetCard, hPcard]
        calc Nat.choose ((n + 1) * (2 * K + 1)) k
            ≤ ((n + 1) * (2 * K + 1) + 1) ^ k := choose_le_succ_pow _ k
          _ ≤ ((n + 1) * (2 * K + 2)) ^ k := by
              apply Nat.pow_le_pow_left
              nlinarith [Nat.zero_le n, Nat.zero_le K]
          _ ≤ ((n + 1) * (2 * K + 2)) ^ B := by
              apply Nat.pow_le_pow_right (by positivity) (by omega)
    _ = (B + 1) * ((n + 1) * (2 * K + 2)) ^ B := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

set_option maxHeartbeats 1600000 in
lemma Codes_card_le (n K B : ℕ) :
    (Codes n K B).card ≤ (B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) := by
  have h1 : (Codes n K B).card
      = (n + 1) * ((n + 1) * ((DefCodes n K B).card * (DefCodes n K B).card)) := by
    rw [Codes, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_range]
  rw [h1]
  have h2 := DefCodes_card_le n K B
  have h3 : (DefCodes n K B).card * (DefCodes n K B).card
      ≤ ((B + 1) * ((n + 1) * (2 * K + 2)) ^ B) * ((B + 1) * ((n + 1) * (2 * K + 2)) ^ B) :=
    Nat.mul_le_mul h2 h2
  calc (n + 1) * ((n + 1) * ((DefCodes n K B).card * (DefCodes n K B).card))
      ≤ (n + 1) * ((n + 1) * (((B + 1) * ((n + 1) * (2 * K + 2)) ^ B)
          * ((B + 1) * ((n + 1) * (2 * K + 2)) ^ B))) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        exact h3
    _ = (B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) := by
        rw [mul_pow]
        ring

set_option maxHeartbeats 1600000 in
def SCode (a b c n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (cd : CodeT) : Set ℝ :=
  {t | (∀ p ∈ cd.2.2.1, rdef a b c n Φ cd.1 t p.1 = p.2) ∧
       (∀ i, i < cd.1 → i ∉ cd.2.2.1.image Prod.fst → rdef a b c n Φ cd.1 t i = 0) ∧
       (∀ p ∈ cd.2.2.2, pdef a b c n Φ cd.1 cd.2.1 t p.1 = p.2) ∧
       (∀ s, s < n - cd.1 → s ∉ cd.2.2.2.image Prod.fst →
         pdef a b c n Φ cd.1 cd.2.1 t s = 0)}

set_option maxHeartbeats 1600000 in
lemma SCode_defects_eq {n : ℕ} {Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ} {cd : CodeT} {t t' : ℝ}
    (ht : t ∈ SCode a b c n Φ cd) (ht' : t' ∈ SCode a b c n Φ cd) :
    (∀ i, i < cd.1 → rdef a b c n Φ cd.1 t i = rdef a b c n Φ cd.1 t' i) ∧
    (∀ s, s < n - cd.1 →
      pdef a b c n Φ cd.1 cd.2.1 t s = pdef a b c n Φ cd.1 cd.2.1 t' s) := by
  classical
  obtain ⟨hr1, hr2, hp1, hp2⟩ := ht
  obtain ⟨hr1', hr2', hp1', hp2'⟩ := ht'
  constructor
  · intro i hi
    by_cases hmem : i ∈ cd.2.2.1.image Prod.fst
    · rw [Finset.mem_image] at hmem
      obtain ⟨p, hp, hpi⟩ := hmem
      rw [← hpi]
      rw [hr1 p hp, hr1' p hp]
    · rw [hr2 i hi hmem, hr2' i hi hmem]
  · intro s hs
    by_cases hmem : s ∈ cd.2.2.2.image Prod.fst
    · rw [Finset.mem_image] at hmem
      obtain ⟨p, hp, hpi⟩ := hmem
      rw [← hpi]
      rw [hp1 p hp, hp1' p hp]
    · rw [hp2 s hs hmem, hp2' s hs hmem]

set_option maxHeartbeats 1600000 in
def arc3 (s₀ : ℕ) (ν : ℤ) (x : ℕ) : Set ℝ :=
  Set.Icc (((ν : ℝ) - s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) - s₀) / s₀ + 1 / (2 * x)) ∪
  (Set.Icc ((ν : ℝ) / s₀ - 1 / (2 * x)) ((ν : ℝ) / s₀ + 1 / (2 * x)) ∪
    Set.Icc (((ν : ℝ) + s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) + s₀) / s₀ + 1 / (2 * x)))

set_option maxHeartbeats 1600000 in
lemma arc3_volume (s₀ : ℕ) (ν : ℤ) (x : ℕ) :
    MeasureTheory.volume (arc3 s₀ ν x) ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
  have hIcc : ∀ z : ℝ, MeasureTheory.volume
      (Set.Icc (z - 1 / (2 * (x : ℝ))) (z + 1 / (2 * (x : ℝ)))) = ENNReal.ofReal (1 / x) := by
    intro z
    rw [Real.volume_Icc]
    congr 1
    ring
  calc MeasureTheory.volume (arc3 s₀ ν x)
      ≤ MeasureTheory.volume
          (Set.Icc (((ν : ℝ) - s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) - s₀) / s₀ + 1 / (2 * x)))
        + (MeasureTheory.volume
            (Set.Icc ((ν : ℝ) / s₀ - 1 / (2 * x)) ((ν : ℝ) / s₀ + 1 / (2 * x)))
          + MeasureTheory.volume
            (Set.Icc (((ν : ℝ) + s₀) / s₀ - 1 / (2 * x)) (((ν : ℝ) + s₀) / s₀ + 1 / (2 * x)))) := by
        refine le_trans
          (MeasureTheory.measure_union_le (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            _ _) ?_
        exact add_le_add le_rfl
          (MeasureTheory.measure_union_le (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            _ _)
    _ = ENNReal.ofReal (1 / x) + (ENNReal.ofReal (1 / x) + ENNReal.ofReal (1 / x)) := by
        rw [hIcc, hIcc, hIcc]
    _ ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        apply le_of_eq
        ring

set_option maxHeartbeats 1600000 in
lemma mem_arc3 {s₀ x : ℕ} {ν ν' : ℤ} {t : ℝ} (hxs : x ≤ s₀) (hx : 1 ≤ x)
    (hnear : |(s₀ : ℝ) * t - (ν' : ℝ)| ≤ 1 / 2)
    (hcong : ν' = ν - s₀ ∨ ν' = ν ∨ ν' = ν + s₀) :
    t ∈ arc3 s₀ ν x := by
  have hs₀ : (0 : ℝ) < (s₀ : ℝ) := by
    have : 0 < s₀ := by omega
    exact_mod_cast this
  have hxR : (0 : ℝ) < (x : ℝ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hxs' : (x : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hxs
  have hdist : |t - (ν' : ℝ) / s₀| ≤ 1 / (2 * x) := by
    have h1 : |t - (ν' : ℝ) / s₀| = |(s₀ : ℝ) * t - ν'| / s₀ := by
      rw [show t - (ν' : ℝ) / s₀ = ((s₀ : ℝ) * t - ν') / s₀ by field_simp, abs_div,
        abs_of_pos hs₀]
    rw [h1]
    have e1 : |(s₀ : ℝ) * t - (ν' : ℝ)| / s₀ ≤ (1 / 2) / s₀ := by
      rw [div_le_div_iff₀ hs₀ hs₀]
      nlinarith [hnear, hs₀]
    have e2 : (1 / 2 : ℝ) / s₀ ≤ (1 / 2) / x := by
      rw [div_le_div_iff₀ hs₀ hxR]
      nlinarith [hxs']
    calc |(s₀ : ℝ) * t - (ν' : ℝ)| / s₀ ≤ (1 / 2) / s₀ := e1
      _ ≤ (1 / 2) / x := e2
      _ = 1 / (2 * x) := by ring
  have hmem : t ∈ Set.Icc ((ν' : ℝ) / s₀ - 1 / (2 * x)) ((ν' : ℝ) / s₀ + 1 / (2 * x)) := by
    rw [Set.mem_Icc]
    have := abs_le.mp hdist
    constructor <;> linarith [this.1, this.2]
  rcases hcong with h | h | h
  · left
    have hcast : (ν' : ℝ) = (ν : ℝ) - s₀ := by rw [h]; push_cast; ring
    rwa [hcast] at hmem
  · right; left
    have hcast : (ν' : ℝ) = (ν : ℝ) := by rw [h]
    rwa [hcast] at hmem
  · right; right
    have hcast : (ν' : ℝ) = (ν : ℝ) + s₀ := by rw [h]; push_cast; ring
    rwa [hcast] at hmem

set_option maxHeartbeats 1600000 in
lemma rdef_cast {n : ℕ} (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q : ℕ) (t : ℝ) (i : ℕ) :
    ((rdef a b c n Φ q t i : ℤ) : ℝ)
      = (rwB a b c n Φ q i : ℝ)
          * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)
        - (rwA a b c n Φ q i : ℝ)
          * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t) := by
  have hrel : rwA a b c n Φ q i * rwS a b c n Φ q i
      = rwB a b c n Φ q i * rwS a b c n Φ q (i + 1) := edgeA_mul_wt a b c _ _
  have hrelR : (rwA a b c n Φ q i : ℝ) * (rwS a b c n Φ q i : ℝ)
      = (rwB a b c n Φ q i : ℝ) * (rwS a b c n Φ q (i + 1) : ℝ) := by exact_mod_cast hrel
  simp only [rdef]
  push_cast
  linear_combination (-t) * hrelR

set_option maxHeartbeats 1600000 in
lemma pdef_cast {n : ℕ} (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (q j : ℕ) (t : ℝ) (s : ℕ) :
    ((pdef a b c n Φ q j t s : ℤ) : ℝ)
      = (pwB a b c n Φ q j s : ℝ)
          * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)
        - (pwA a b c n Φ q j s : ℝ)
          * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t) := by
  have hrel : pwA a b c n Φ q j s * pwS a b c n Φ q j s
      = pwB a b c n Φ q j s * pwS a b c n Φ q j (s + 1) := edgeA_mul_wt a b c _ _
  have hrelR : (pwA a b c n Φ q j s : ℝ) * (pwS a b c n Φ q j s : ℝ)
      = (pwB a b c n Φ q j s : ℝ) * (pwS a b c n Φ q j (s + 1) : ℝ) := by exact_mod_cast hrel
  simp only [pdef]
  push_cast
  linear_combination (-t) * hrelR

set_option maxHeartbeats 1600000 in
theorem low_energy_measure (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) :
    ∃ C₄ : ℕ, 1 ≤ C₄ ∧ ∃ X₂ : ℕ, ∀ x : ℕ, X₂ ≤ x →
      MeasureTheory.volume
          {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ Real.log x}
        ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄) := by
  classical
  have ha2 : 2 ≤ a := ha
  have hb2 : 2 ≤ b := hb
  have hc2 : 2 ≤ c := hc
  obtain ⟨c₀, C₀, D, hc₀, hC₀, hD1, X₀g, hX₀g2, hgrid⟩ := grid_embedding ha2 hb2 hc2 hco
  set K : ℕ := (a * b * c) ^ D with hKdef
  have habc8 : 8 ≤ a * b * c := by
    calc 8 = 2 * 2 * 2 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hK8 : 8 ≤ K := by
    rw [hKdef]
    calc 8 ≤ a * b * c := habc8
      _ = (a * b * c) ^ 1 := (pow_one _).symm
      _ ≤ (a * b * c) ^ D := Nat.pow_le_pow_right (le_trans (by norm_num) habc8) hD1
  have hKR : (8 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK8
  set δ : ℝ := 1 / (4 * K) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    positivity
  set B1 : ℕ := ⌈4 / (c₀ * δ ^ 2)⌉₊ with hB1def
  set B2 : ℕ := ⌈7 / (c₀ * δ ^ 2)⌉₊ with hB2def
  set B : ℕ := 2 * (B1 + B2 + 2) with hBdef
  set C₄ : ℕ := 2 * B + 3 with hC₄def
  set CCn : ℕ := (B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) with hCCndef
  set T₃ : ℝ := 3 * (CCn : ℝ) * (2 * C₀) ^ (2 * B + 2) + 1 with hT₃def
  set X₂ : ℕ := max X₀g (max 3 (max ⌈Real.exp (96 / c₀)⌉₊
    (max ⌈Real.exp T₃⌉₊ ⌈Real.exp (1 / C₀)⌉₊))) with hX₂def
  refine ⟨C₄, by omega, X₂, fun x hx => ?_⟩
  simp only [hX₂def, max_le_iff] at hx
  obtain ⟨hxX₀g, hx3, hxc₀, hxT₃, hxC₀⟩ := hx
  have hx1 : 1 ≤ x := by omega
  have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  set L : ℝ := Real.log x with hLdef
  have hthresh : ∀ T : ℝ, ⌈Real.exp T⌉₊ ≤ x → T ≤ L := by
    intro T hT
    have h1 : Real.exp T ≤ (x : ℝ) := by
      calc Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast hT
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos T) h1
  have hL96 : 96 / c₀ ≤ L := hthresh _ hxc₀
  have hLT₃ : T₃ ≤ L := hthresh _ hxT₃
  have hLC₀ : 1 / C₀ ≤ L := hthresh _ hxC₀
  have hL0 : 0 < L := by
    have h96 : (0 : ℝ) < 96 / c₀ := by positivity
    linarith
  obtain ⟨n, Φ, ⟨hnlow, hnhigh⟩, hband, hinj, hface, hjump⟩ := hgrid x hxX₀g
  have hc₀L96 : (96 : ℝ) ≤ c₀ * L := by
    have h1 : c₀ * (96 / c₀) ≤ c₀ * L := mul_le_mul_of_nonneg_left hL96 hc₀.le
    rw [mul_div_cancel₀ _ hc₀.ne'] at h1
    linarith
  have hn96 : 96 ≤ n := by
    have h1 : (96 : ℝ) ≤ (n : ℝ) := by
      calc (96 : ℝ) ≤ c₀ * L := hc₀L96
        _ = c₀ * Real.log x := by rw [hLdef]
        _ ≤ (n : ℝ) := hnlow
    exact_mod_cast h1
  have hn48 : 48 ≤ n := by omega
  set E : Set ℝ := {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ Qenergy a b c x t ≤ Real.log x}
    with hEdef

  set Amap : CodeT → Set ℝ := fun cd =>
    if h : (E ∩ SCode a b c n Φ cd).Nonempty then
      arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x
    else ∅ with hAmapdef

  have hcover : ∀ t ∈ E, ∃ cd ∈ Codes n K B, t ∈ Amap cd := by
    intro t htE
    obtain ⟨ht01, htQ⟩ := htE
    obtain ⟨ht0, ht1⟩ := ht01

    set Bad : ℕ × ℕ × ℕ → Prop := fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| with hBaddef
    set H : ℕ := ((TriF n).filter (fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)|)).card with hHdef
    have hHQ : (H : ℝ) * δ ^ 2 ≤ Qenergy a b c x t :=
      badF_card_le a b c x n Φ t δ hδ0 hband hinj
    have hHδL : (H : ℝ) * δ ^ 2 ≤ L := by
      calc (H : ℝ) * δ ^ 2 ≤ Qenergy a b c x t := hHQ
        _ ≤ Real.log x := htQ
        _ = L := by rw [hLdef]

    have hHhyp : ∀ F : Finset (ℕ × ℕ × ℕ), (∀ v ∈ F, v ∈ Tri n ∧ Bad v) → F.card ≤ H := by
      intro F hF
      rw [hHdef]
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hv1, hv2⟩ := hF v hv
      rw [Finset.mem_filter]
      exact ⟨mem_TriF.mpr hv1, hv2⟩
    obtain ⟨q, hq, j, hj, hrowH, hpathH⟩ := exists_sparse_row_and_path hn48 Bad H hHhyp
    obtain ⟨hq1, hq2⟩ := midQ_bounds hq
    obtain ⟨hj1, hj2⟩ := midJ_bounds hj
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hc₀L_le_n : c₀ * L ≤ (n : ℝ) := by
      calc c₀ * L = c₀ * Real.log x := by rw [hLdef]
        _ ≤ (n : ℝ) := hnlow

    have hkey : ∀ m k : ℕ, n * m ≤ k * H → (m : ℝ) * (c₀ * δ ^ 2) ≤ (k : ℝ) := by
      intro m k hmk
      have hnm : (n : ℝ) * m ≤ (k : ℝ) * H := by exact_mod_cast hmk
      have e1 : c₀ * L * ((m : ℝ) * δ ^ 2) ≤ (n : ℝ) * ((m : ℝ) * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hc₀L_le_n (by positivity)
      have e2 : (n : ℝ) * m * δ ^ 2 ≤ (k : ℝ) * H * δ ^ 2 :=
        mul_le_mul_of_nonneg_right hnm (by positivity)
      have e3 : (k : ℝ) * ((H : ℝ) * δ ^ 2) ≤ (k : ℝ) * L :=
        mul_le_mul_of_nonneg_left hHδL (by positivity)
      have h1 : (m : ℝ) * (c₀ * δ ^ 2) * L ≤ (k : ℝ) * L := by nlinarith [e1, e2, e3]
      exact le_of_mul_le_mul_right h1 hL0
    have hrow_le : (rowBad Bad n q).card ≤ B1 := by
      have h2 : ((rowBad Bad n q).card : ℝ) ≤ 4 / (c₀ * δ ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have h := hkey _ 4 hrowH
        calc ((rowBad Bad n q).card : ℝ) * (c₀ * δ ^ 2) ≤ ((4 : ℕ) : ℝ) := h
          _ = 4 := by norm_num
      calc (rowBad Bad n q).card = ⌈((rowBad Bad n q).card : ℝ)⌉₊ :=
            (Nat.ceil_natCast _).symm
        _ ≤ ⌈(4 : ℝ) / (c₀ * δ ^ 2)⌉₊ := Nat.ceil_mono h2
        _ ≤ B1 := by rw [hB1def]
    have hpath_le : (pathBad Bad n q j).card ≤ B2 := by
      have h2 : ((pathBad Bad n q j).card : ℝ) ≤ 7 / (c₀ * δ ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have h := hkey _ 7 hpathH
        calc ((pathBad Bad n q j).card : ℝ) * (c₀ * δ ^ 2) ≤ ((7 : ℕ) : ℝ) := h
          _ = 7 := by norm_num
      calc (pathBad Bad n q j).card = ⌈((pathBad Bad n q j).card : ℝ)⌉₊ :=
            (Nat.ceil_natCast _).symm
        _ ≤ ⌈(7 : ℝ) / (c₀ * δ ^ 2)⌉₊ := Nat.ceil_mono h2
        _ ≤ B2 := by rw [hB2def]

    have hrow_coeff : ∀ i, i < q → rwA a b c n Φ q i ≤ K ∧ rwB a b c n Φ q i ≤ K := by
      intro i hi
      have hv := rowV_mem_Tri (n := n) hn48 hq (by omega : i ≤ q)
      have hw := rowV_mem_Tri (n := n) hn48 hq (by omega : i + 1 ≤ q)
      have hadj := rowV_adjacent (n := n) (q := q) (i := i) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      constructor
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.2.1
          hj6.2.2.2.1 hj6.2.2.2.2.2 |>.trans_eq hKdef.symm
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.1
          hj6.2.2.1 hj6.2.2.2.2.1 |>.trans_eq hKdef.symm
    have hpath_coeff : ∀ s, s < n - q →
        pwA a b c n Φ q j s ≤ K ∧ pwB a b c n Φ q j s ≤ K := by
      intro s hs
      have hv := pathV_mem_Tri (n := n) hn48 hq hj (by omega : s ≤ n - q)
      have hw := pathV_mem_Tri (n := n) hn48 hq hj (by omega : s + 1 ≤ n - q)
      have hadj := pathV_adjacent (n := n) (q := q) (j := j) (s := s) (by omega) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      constructor
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.2.1
          hj6.2.2.2.1 hj6.2.2.2.2.2 |>.trans_eq hKdef.symm
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.1
          hj6.2.2.1 hj6.2.2.2.2.1 |>.trans_eq hKdef.symm

    have hrdef_le : ∀ i, i < q → rdef a b c n Φ q t i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro i hi
      obtain ⟨hA, hB⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ q t i
      have h1 : |(rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (rwA a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have habs : |((rdef a b c n Φ q t i : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ q i : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ q i : ℝ) := by positivity
        calc |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)
            - (rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)|
            ≤ |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ q i : ℝ) * (1 / 2) + (rwA a b c n Φ q i : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    have hpdef_le : ∀ s, s < n - q →
        pdef a b c n Φ q j t s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro s hs
      obtain ⟨hA, hB⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ q j t s
      have h1 : |(pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (pwA a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have habs : |((pdef a b c n Φ q j t s : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ q j s : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ q j s : ℝ) := by positivity
        calc |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ q j s : ℝ) * (1 / 2) + (pwA a b c n Φ q j s : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2

    have hgood_of_notbad : ∀ v, ¬Bad v →
        |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| ≤ δ := by
      intro v hv
      rw [hBaddef] at hv
      push_neg at hv
      exact hv
    have h2Kδ : 2 * (K : ℝ) * δ < 1 := by
      rw [hδdef]
      have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
      rw [show 2 * (K : ℝ) * (1 / (4 * K)) = 1 / 2 by field_simp; ring]
      norm_num
    have hrdef_zero : ∀ i, i < q → ¬Bad (rowV n q i) → ¬Bad (rowV n q (i + 1)) →
        rdef a b c n Φ q t i = 0 := by
      intro i hi hg1 hg2
      obtain ⟨hA, hB⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ q t i
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (rwA a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ q i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ q i : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ q i : ℝ) := by positivity
      have habs : |((rdef a b c n Φ q t i : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)
            - (rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)|
            ≤ |(rwB a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t (i + 1) : ℝ) - (rwS a b c n Φ q (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ q i : ℝ)
              * ((rdv a b c n Φ q t i : ℝ) - (rwS a b c n Φ q i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ q i : ℝ) * δ + (rwA a b c n Φ q i : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |rdef a b c n Φ q t i| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega
    have hpdef_zero : ∀ s, s < n - q → ¬Bad (pathV n q j s) → ¬Bad (pathV n q j (s + 1)) →
        pdef a b c n Φ q j t s = 0 := by
      intro s hs hg1 hg2
      obtain ⟨hA, hB⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ q j t s
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t|
          ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (pwA a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ q j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ q j s : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ q j s : ℝ) := by positivity
      have habs : |((pdef a b c n Φ q j t s : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t (s + 1) : ℝ) - (pwS a b c n Φ q j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ q j s : ℝ)
              * ((pdv a b c n Φ q j t s : ℝ) - (pwS a b c n Φ q j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ q j s : ℝ) * δ + (pwA a b c n Φ q j s : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |pdef a b c n Φ q j t s| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega

    set rdfF : Finset ℕ := (Finset.range q).filter (fun i => rdef a b c n Φ q t i ≠ 0)
      with hrdfFdef
    set pdfF : Finset ℕ :=
      (Finset.range (n - q)).filter (fun s => pdef a b c n Φ q j t s ≠ 0) with hpdfFdef
    set rdf : Finset (ℕ × ℤ) := rdfF.image (fun i => (i, rdef a b c n Φ q t i)) with hrdfdef
    set pdf : Finset (ℕ × ℤ) := pdfF.image (fun s => (s, pdef a b c n Φ q j t s))
      with hpdfdef

    have hrdfF_sub : rdfF ⊆ (rowBad Bad n q) ∪ (rowBad Bad n q).image (fun i => i - 1) := by
      intro i hi
      rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hiq, hine⟩ := hi
      by_cases hb1 : Bad (rowV n q i)
      · apply Finset.mem_union_left
        rw [rowBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hb1⟩
      · by_cases hb2 : Bad (rowV n q (i + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨i + 1, ?_, by omega⟩
          rw [rowBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hb2⟩
        · exact absurd (hrdef_zero i hiq hb1 hb2) hine
    have hpdfF_sub : pdfF ⊆ (pathBad Bad n q j) ∪ (pathBad Bad n q j).image (fun s => s - 1) := by
      intro s hs
      rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨hsq, hsne⟩ := hs
      by_cases hb1 : Bad (pathV n q j s)
      · apply Finset.mem_union_left
        rw [pathBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hb1⟩
      · by_cases hb2 : Bad (pathV n q j (s + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨s + 1, ?_, by omega⟩
          rw [pathBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hb2⟩
        · exact absurd (hpdef_zero s hsq hb1 hb2) hsne
    have hrdf_card : rdf.card ≤ B := by
      calc rdf.card ≤ rdfF.card := Finset.card_image_le
        _ ≤ ((rowBad Bad n q) ∪ (rowBad Bad n q).image (fun i => i - 1)).card :=
            Finset.card_le_card hrdfF_sub
        _ ≤ (rowBad Bad n q).card + ((rowBad Bad n q).image (fun i => i - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ (rowBad Bad n q).card + (rowBad Bad n q).card := by
            have := Finset.card_image_le (s := rowBad Bad n q) (f := fun i => i - 1)
            omega
        _ ≤ B1 + B1 := by
            have := hrow_le
            omega
        _ ≤ B := by
            rw [hBdef]
            omega
    have hpdf_card : pdf.card ≤ B := by
      calc pdf.card ≤ pdfF.card := Finset.card_image_le
        _ ≤ ((pathBad Bad n q j) ∪ (pathBad Bad n q j).image (fun s => s - 1)).card :=
            Finset.card_le_card hpdfF_sub
        _ ≤ (pathBad Bad n q j).card + ((pathBad Bad n q j).image (fun s => s - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ (pathBad Bad n q j).card + (pathBad Bad n q j).card := by
            have := Finset.card_image_le (s := pathBad Bad n q j) (f := fun s => s - 1)
            omega
        _ ≤ B2 + B2 := by
            have := hpath_le
            omega
        _ ≤ B := by
            rw [hBdef]
            omega

    have hcdmem : ((q, j, rdf, pdf) : CodeT) ∈ Codes n K B := by
      rw [Codes]
      simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro p hp
          rw [hrdfdef, Finset.mem_image] at hp
          obtain ⟨i, hi, rfl⟩ := hp
          rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hrdef_le i hi.1⟩
        · exact hrdf_card
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro p hp
          rw [hpdfdef, Finset.mem_image] at hp
          obtain ⟨s, hs, rfl⟩ := hp
          rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hpdef_le s hs.1⟩
        · exact hpdf_card

    have hrdf_fst : rdf.image Prod.fst = rdfF := by
      rw [hrdfdef, Finset.image_image]
      exact Finset.image_id'
    have hpdf_fst : pdf.image Prod.fst = pdfF := by
      rw [hpdfdef, Finset.image_image]
      exact Finset.image_id'
    have htS : t ∈ SCode a b c n Φ (q, j, rdf, pdf) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [hrdfdef, Finset.mem_image] at hp
        obtain ⟨i, _, rfl⟩ := hp
        rfl
      · intro i hi hnot
        rw [show ((q, j, rdf, pdf) : CodeT).2.2.1 = rdf from rfl, hrdf_fst, hrdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hi, hne⟩)
      · intro p hp
        rw [hpdfdef, Finset.mem_image] at hp
        obtain ⟨s, _, rfl⟩ := hp
        rfl
      · intro s hs hnot
        rw [show ((q, j, rdf, pdf) : CodeT).2.2.2 = pdf from rfl, hpdf_fst, hpdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hs, hne⟩)

    have hne : (E ∩ SCode a b c n Φ (q, j, rdf, pdf)).Nonempty :=
      ⟨t, ⟨⟨ht0, ht1⟩, htQ⟩, htS⟩
    refine ⟨(q, j, rdf, pdf), hcdmem, ?_⟩
    have hAeq : Amap (q, j, rdf, pdf)
        = arc3 (rwS a b c n Φ q 0) (rdv a b c n Φ q hne.choose 0) x := by
      rw [hAmapdef]
      exact dif_pos hne
    rw [hAeq]
    obtain ⟨ht'E, ht'S⟩ := hne.choose_spec
    obtain ⟨⟨ht'0, ht'1⟩, _⟩ := ht'E

    obtain ⟨hdefr, hdefp⟩ := SCode_defects_eq (a := a) (b := b) (c := c) htS ht'S
    have hdvd := chain_diff_dvd ha2 hb2 hc2 hco Φ hband hface hx1 hn48 hq hj
      t hne.choose hdefr hdefp
    obtain ⟨r, hr⟩ := hdvd

    have hs₀mem := hband _ (rowV_mem_Tri hn48 hq (by omega : 0 ≤ q))
    have hs₀x : x ≤ rwS a b c n Φ q 0 := by
      have h1 := (mem_Band.mp hs₀mem).2.1
      exact h1
    have hs₀0 : 0 < rwS a b c n Φ q 0 := by omega
    have hs₀R : (0 : ℝ) < (rwS a b c n Φ q 0 : ℝ) := by exact_mod_cast hs₀0
    have hbound : ∀ u : ℝ, 0 ≤ u → u < 1 →
        0 ≤ rdv a b c n Φ q u 0 ∧ rdv a b c n Φ q u 0 ≤ (rwS a b c n Φ q 0 : ℤ) := by
      intro u hu0 hu1
      constructor
      · apply round_nonneg_of_nonneg
        positivity
      · apply round_le_nat (by positivity)
        calc (rwS a b c n Φ q 0 : ℝ) * u < (rwS a b c n Φ q 0 : ℝ) * 1 :=
              mul_lt_mul_of_pos_left hu1 hs₀R
          _ = (rwS a b c n Φ q 0 : ℝ) := mul_one _
    obtain ⟨hb1, hb2⟩ := hbound t ht0 ht1
    obtain ⟨hb1', hb2'⟩ := hbound hne.choose ht'0 ht'1
    have hs₀Z : (0 : ℤ) < (rwS a b c n Φ q 0 : ℤ) := by exact_mod_cast hs₀0
    have hprodlo : -((rwS a b c n Φ q 0 : ℕ) : ℤ) ≤ ((rwS a b c n Φ q 0 : ℕ) : ℤ) * r := by
      rw [← hr]
      omega
    have hprodhi : ((rwS a b c n Φ q 0 : ℕ) : ℤ) * r ≤ ((rwS a b c n Φ q 0 : ℕ) : ℤ) := by
      rw [← hr]
      omega
    have hrlo : -1 ≤ r := by nlinarith [hprodlo, hs₀Z]
    have hrhi : r ≤ 1 := by nlinarith [hprodhi, hs₀Z]
    have hcong : rdv a b c n Φ q t 0 = rdv a b c n Φ q hne.choose 0 - rwS a b c n Φ q 0
        ∨ rdv a b c n Φ q t 0 = rdv a b c n Φ q hne.choose 0
        ∨ rdv a b c n Φ q t 0 = rdv a b c n Φ q hne.choose 0 + rwS a b c n Φ q 0 := by
      interval_cases r
      · left; omega
      · right; left; omega
      · right; right; omega
    have hnear : |(rwS a b c n Φ q 0 : ℝ) * t - (rdv a b c n Φ q t 0 : ℝ)| ≤ 1 / 2 :=
      abs_sub_round _
    exact mem_arc3 hs₀x hx1 hnear hcong

  have hsubset : E ⊆ ⋃ cd ∈ Codes n K B, Amap cd := by
    intro t ht
    obtain ⟨cd, hcd, hmem⟩ := hcover t ht
    exact Set.mem_biUnion hcd hmem
  have hvol_arc : ∀ cd ∈ Codes n K B,
      MeasureTheory.volume (Amap cd) ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
    intro cd _
    by_cases h : (E ∩ SCode a b c n Φ cd).Nonempty
    · have hAeq : Amap cd
          = arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x := by
        rw [hAmapdef]
        exact dif_pos h
      rw [hAeq]
      exact arc3_volume _ _ _
    · have hAeq : Amap cd = ∅ := by
        rw [hAmapdef]
        exact dif_neg h
      rw [hAeq]
      simp
  calc MeasureTheory.volume E
      ≤ MeasureTheory.volume (⋃ cd ∈ Codes n K B, Amap cd) :=
        MeasureTheory.measure_mono hsubset
    _ ≤ ∑ cd ∈ Codes n K B, MeasureTheory.volume (Amap cd) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Codes n K B, ENNReal.ofReal (3 / (x : ℝ)) :=
        Finset.sum_le_sum hvol_arc
    _ = ((Codes n K B).card : ℝ≥0∞) * ENNReal.ofReal (3 / (x : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal

        have hcards : ((Codes n K B).card : ℝ)
            ≤ (CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2) := by
          have h1 := Codes_card_le n K B
          have h2 : ((Codes n K B).card : ℝ)
              ≤ (((B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) : ℕ) : ℝ) := by
            exact_mod_cast h1
          calc ((Codes n K B).card : ℝ)
              ≤ (((B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) : ℕ) : ℝ) := h2
            _ = (CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2) := by
                rw [hCCndef]
                push_cast
                ring
        have hn1 : ((n : ℝ) + 1) ≤ 2 * C₀ * L := by
          have h1 : (n : ℝ) ≤ C₀ * L := by
            calc (n : ℝ) ≤ C₀ * Real.log x := hnhigh
              _ = C₀ * L := by rw [hLdef]
          have h2 : (1 : ℝ) ≤ C₀ * L := by
            have h3 : C₀ * (1 / C₀) ≤ C₀ * L := mul_le_mul_of_nonneg_left hLC₀ hC₀.le
            rw [mul_div_cancel₀ _ hC₀.ne'] at h3
            linarith
          linarith
        have hCCn0 : (0 : ℝ) ≤ (CCn : ℝ) := by positivity
        have hL2B : (0 : ℝ) ≤ L ^ (2 * B + 2) := by positivity
        have hfinal : 3 * ((Codes n K B).card : ℝ) ≤ L ^ C₄ := by
          calc 3 * ((Codes n K B).card : ℝ)
              ≤ 3 * ((CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2)) := by linarith [hcards]
            _ ≤ 3 * ((CCn : ℝ) * (2 * C₀ * L) ^ (2 * B + 2)) := by
                apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
                apply mul_le_mul_of_nonneg_left ?_ hCCn0
                apply pow_le_pow_left₀ (by positivity) hn1
            _ = (3 * (CCn : ℝ) * (2 * C₀) ^ (2 * B + 2)) * L ^ (2 * B + 2) := by
                rw [mul_pow]
                ring
            _ ≤ L * L ^ (2 * B + 2) := by
                apply mul_le_mul_of_nonneg_right ?_ hL2B
                rw [hT₃def] at hLT₃
                linarith
            _ = L ^ (2 * B + 3) := by
                rw [← pow_succ']
            _ = L ^ C₄ := by rw [hC₄def]
        calc ((Codes n K B).card : ℝ) * (3 / (x : ℝ))
            = (3 * ((Codes n K B).card : ℝ)) / (x : ℝ) := by ring
          _ ≤ L ^ C₄ / (x : ℝ) := by
              have hmul := mul_le_mul_of_nonneg_right hfinal hx0R.le
              rw [div_le_div_iff₀ hx0R hx0R]
              linarith [hmul]
          _ = 1 / (x : ℝ) * Real.log x ^ C₄ := by
              rw [hLdef]
              ring

end LowEnergy

end Erdos123Band

end Module_LowEnergy

namespace Erdos123Band

lemma e_int (k : ℤ) : e (k : ℝ) = 1 := by
  rw [e, show (2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  rw [e, e, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul]
  simp only [Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

lemma one_le_log {x : ℕ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (x : ℝ))]
  linarith [Real.exp_one_lt_d9]

end Erdos123Band

section Module_GBand

namespace Erdos123Band

set_option maxHeartbeats 1000000 in
noncomputable def GBand (a b c p q x : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x)
  (Finset.range (2 * p * x)).filter (fun s => s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x)

set_option maxHeartbeats 1000000 in
noncomputable def GS1 (a b c p q x : ℕ) : ℕ := (GBand a b c p q x).sum id

set_option maxHeartbeats 1000000 in
noncomputable def GS2 (a b c p q x : ℕ) : ℕ := (GBand a b c p q x).sum (fun s => s ^ 2)

set_option maxHeartbeats 1000000 in
theorem of_mem_GBand {a b c p q x s : ℕ} (h : s ∈ GBand a b c p q x) :
    s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x := by
  unfold GBand at h
  simp only [Finset.mem_filter, Finset.mem_range] at h
  exact h.2

set_option maxHeartbeats 1000000 in
theorem mem_GBand {a b c p q : ℕ} (hq : 0 < q) {x s : ℕ} :
    s ∈ GBand a b c p q x ↔ s ∈ Smooth3 a b c ∧ x ≤ s ∧ q * s < p * x := by
  unfold GBand
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    have hs : s ≤ q * s := Nat.le_mul_of_pos_left s hq
    have h1 : s < p * x := lt_of_le_of_lt hs h.2.2
    have h2 : p * x ≤ 2 * p * x := by
      have hp2 : p ≤ 2 * p := by omega
      exact Nat.mul_le_mul_right x hp2
    exact lt_of_lt_of_le h1 h2

set_option maxHeartbeats 1000000 in
lemma gband_le {a b c p q x s : ℕ} (hq : 0 < q) (h : s ∈ GBand a b c p q x) :
    s ≤ p * x := by
  obtain ⟨-, -, hw⟩ := of_mem_GBand h
  have hs : s ≤ q * s := Nat.le_mul_of_pos_left s hq
  exact le_of_lt (lt_of_le_of_lt hs hw)

set_option maxHeartbeats 1000000 in
theorem smooth3_dvd_exponents {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) {k1 l1 m1 k2 l2 m2 : ℕ}
    (h : a ^ k1 * b ^ l1 * c ^ m1 ∣ a ^ k2 * b ^ l2 * c ^ m2) :
    k1 ≤ k2 ∧ l1 ≤ l2 ∧ m1 ≤ m2 := by
  obtain ⟨hab, hac, hbc⟩ := hco
  have key : ∀ u v w : ℕ, 2 ≤ u → Nat.Coprime u v → Nat.Coprime u w →
      ∀ e1 e2 f2 g2 : ℕ, u ^ e1 ∣ u ^ e2 * v ^ f2 * w ^ g2 → e1 ≤ e2 := by
    intro u v w hu huv huw e1 e2 f2 g2 hdvd
    have hdvd' : u ^ e1 ∣ u ^ e2 * (v ^ f2 * w ^ g2) := by
      rwa [← mul_assoc]
    have hcop : Nat.Coprime (u ^ e1) (v ^ f2 * w ^ g2) :=
      Nat.Coprime.mul_right (huv.pow e1 f2) (huw.pow e1 g2)
    have h2 : u ^ e1 ∣ u ^ e2 := by
      rcases hdvd' with ⟨d, hd⟩
      have h3 : u ^ e1 ∣ (v ^ f2 * w ^ g2) * u ^ e2 := ⟨d, by rw [← hd]; ring⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop) h3
    by_contra hlt
    push_neg at hlt
    have h4 : u ^ e1 ≤ u ^ e2 := Nat.le_of_dvd (pow_pos (by omega) _) h2
    have h5 : u ^ e2 < u ^ e1 := Nat.pow_lt_pow_right (by omega) (by omega)
    exact absurd h4 (not_le.mpr h5)
  refine ⟨?_, ?_, ?_⟩
  · exact key a b c ha hab hac k1 k2 l2 m2 (dvd_trans ⟨b ^ l1 * c ^ m1, by ring⟩ h)
  · exact key b a c hb hab.symm hbc l1 l2 k2 m2
      (dvd_trans ⟨a ^ k1 * c ^ m1, by ring⟩ (h.trans ⟨1, by ring⟩))
  · exact key c a b hc hac.symm hbc.symm m1 m2 k2 l2
      (dvd_trans ⟨a ^ k1 * b ^ l1, by ring⟩ (h.trans ⟨1, by ring⟩))

set_option maxHeartbeats 1000000 in
theorem gband_primitive {a b c p q : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q)
    (hpd : p < q * min a (min b c)) (x : ℕ) :
    IsPrimitive (GBand a b c p q x) := by
  intro u hu v hv hne hdvd
  obtain ⟨huS, hux, huw⟩ := of_mem_GBand hu
  obtain ⟨hvS, hvx, hvw⟩ := of_mem_GBand hv
  obtain ⟨k1, l1, m1, hu'⟩ := huS
  obtain ⟨k2, l2, m2, hv'⟩ := hvS
  subst hu' hv'
  obtain ⟨hk, hl, hm⟩ :=
    smooth3_dvd_exponents (by omega) (by omega) (by omega) hco hdvd
  set W : ℕ := a ^ (k2 - k1) * (b ^ (l2 - l1) * c ^ (m2 - m1)) with hW
  have hfact : a ^ k2 * b ^ l2 * c ^ m2 = a ^ k1 * b ^ l1 * c ^ m1 * W := by
    rw [hW]
    have e1 : a ^ k2 = a ^ k1 * a ^ (k2 - k1) := by rw [← pow_add]; congr 1; omega
    have e2 : b ^ l2 = b ^ l1 * b ^ (l2 - l1) := by rw [← pow_add]; congr 1; omega
    have e3 : c ^ m2 = c ^ m1 * c ^ (m2 - m1) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, e3]; ring

  have hgap : k1 < k2 ∨ l1 < l2 ∨ m1 < m2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hk' : k1 = k2 := by omega
    have hl' : l1 = l2 := by omega
    have hm' : m1 = m2 := by omega
    exact hne (by rw [hk', hl', hm'])
  set d : ℕ := min a (min b c) with hd
  have hda : d ≤ a := min_le_left _ _
  have hdb : d ≤ b := le_trans (min_le_right _ _) (min_le_left _ _)
  have hdc : d ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)

  have hdW : d ≤ W := by
    rcases hgap with hg | hg | hg
    · have h1 : a ≤ a ^ (k2 - k1) := by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ (k2 - k1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc d ≤ a := hda
        _ ≤ a ^ (k2 - k1) := h1
        _ ≤ W := by
            rw [hW]
            exact Nat.le_mul_of_pos_right _
              (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
    · have h1 : b ≤ b ^ (l2 - l1) := by
        calc b = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (l2 - l1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc d ≤ b := hdb
        _ ≤ b ^ (l2 - l1) := h1
        _ ≤ W := by
            rw [hW, ← mul_assoc, mul_comm (a ^ (k2 - k1)) (b ^ (l2 - l1)), mul_assoc]
            exact Nat.le_mul_of_pos_right _
              (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
    · have h1 : c ≤ c ^ (m2 - m1) := by
        calc c = c ^ 1 := (pow_one c).symm
          _ ≤ c ^ (m2 - m1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc d ≤ c := hdc
        _ ≤ c ^ (m2 - m1) := h1
        _ ≤ W := by
            rw [hW, show a ^ (k2 - k1) * (b ^ (l2 - l1) * c ^ (m2 - m1))
              = c ^ (m2 - m1) * (a ^ (k2 - k1) * b ^ (l2 - l1)) by ring]
            exact Nat.le_mul_of_pos_right _
              (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))

  set u : ℕ := a ^ k1 * b ^ l1 * c ^ m1 with hu'
  set v : ℕ := a ^ k2 * b ^ l2 * c ^ m2 with hv'
  have hupos : 0 < u := by
    rw [hu']
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
      (pow_pos (by omega) _)
  have h1 : p * x ≤ p * u := Nat.mul_le_mul_left p hux
  have h2 : p * u < q * d * u := by
    have hqd : p < q * d := by rw [hd]; exact hpd
    exact (Nat.mul_lt_mul_right hupos).mpr hqd
  have h3 : q * d * u ≤ q * v := by
    have h4 : d * u ≤ W * u := Nat.mul_le_mul_right u hdW
    have h5 : W * u = v := by rw [hfact]; ring
    calc q * d * u = q * (d * u) := by ring
      _ ≤ q * (W * u) := Nat.mul_le_mul_left q h4
      _ = q * v := by rw [h5]
  exact absurd (calc q * v < p * x := hvw
    _ ≤ p * u := h1
    _ < q * d * u := h2
    _ ≤ q * v := h3) (lt_irrefl _)

set_option maxHeartbeats 1000000 in
lemma geta_pos {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    (0 : ℝ) < Real.log p - Real.log q := by
  have h : Real.log q < Real.log p :=
    Real.log_lt_log (by exact_mod_cast hq) (by exact_mod_cast hqp)
  linarith

set_option maxHeartbeats 1000000 in
lemma geta_lt_log {p q d : ℕ} (hq : 0 < q) (hp : 0 < p) (hpd : p < q * d) :
    Real.log p - Real.log q < Real.log d := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, Nat.mul_zero] at hpd; omega
    · exact h0
  have h1 : Real.log p < Real.log (q * d) :=
    Real.log_lt_log (by exact_mod_cast hp) (by exact_mod_cast hpd)
  have h2 : Real.log ((q : ℝ) * (d : ℝ)) = Real.log q + Real.log d :=
    Real.log_mul (by exact_mod_cast hq.ne') (by exact_mod_cast hd.ne')
  rw [h2] at h1
  linarith

set_option maxHeartbeats 1000000 in
theorem gexists_int_step {a b p q : ℕ} (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hq : 0 < q) (hqp : q < p) (hpa : p < q * a) (hpb : p < q * b)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ w z P Q : ℕ, 2 ≤ w ∧ 2 ≤ z ∧ Nat.Coprime w z ∧
      (w = a ∧ z = b ∨ w = b ∧ z = a) ∧ 1 ≤ P ∧ 1 ≤ Q ∧
      z ^ P < w ^ Q ∧ q * (w ^ Q) ^ K < p * (z ^ P) ^ K := by
  have hp0 : 0 < p := by omega
  have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set η : ℝ := Real.log p - Real.log q with hηdef
  have hη : 0 < η := geta_pos hq hqp
  set ε : ℝ := η / K with hεdef
  have hεpos : 0 < ε := div_pos hη hKR
  have hε_le : ε ≤ η := by
    rw [hεdef, div_le_iff₀ hKR]; nlinarith [hη, hK1R]
  have hηa : η < Real.log a := geta_lt_log hq hp0 hpa
  have hηb : η < Real.log b := geta_lt_log hq hp0 hpb
  have hεa : ε < Real.log a := lt_of_le_of_lt hε_le hηa
  have hεb : ε < Real.log b := lt_of_le_of_lt hε_le hηb
  obtain ⟨m, n, hpos, hlt⟩ := exists_small_combo hab ha hb hεpos
  have hcase : (1 ≤ m ∧ n ≤ -1) ∨ (m ≤ -1 ∧ 1 ≤ n) := by
    have hnotpp : ¬ (0 ≤ m ∧ 0 ≤ n) := by
      rintro ⟨hm, hn⟩
      have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm
      have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hn
      rcases eq_or_lt_of_le hm with hm0 | hm1
      · rcases eq_or_lt_of_le hn with hn0 | hn1
        · rw [← hm0, ← hn0] at hpos; norm_num at hpos
        · have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          nlinarith [hlt, hεb, mul_nonneg hmR hla.le]
      · have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        nlinarith [hlt, hεa, mul_nonneg hnR hlb.le]
    have hnotnn : ¬ (m ≤ 0 ∧ n ≤ 0) := by
      rintro ⟨hm, hn⟩
      have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hn
      nlinarith [hpos, mul_nonpos_of_nonpos_of_nonneg hmR hla.le,
        mul_nonpos_of_nonpos_of_nonneg hnR hlb.le]
    rcases lt_trichotomy m 0 with hm | hm | hm
    · right; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn
      exact hnotnn ⟨by omega, by omega⟩
    · exfalso
      rcases le_or_gt n 0 with hn | hn
      · exact hnotnn ⟨by omega, hn⟩
      · exact hnotpp ⟨by omega, by omega⟩
    · left; refine ⟨by omega, ?_⟩; by_contra hn; push_neg at hn
      exact hnotpp ⟨by omega, by omega⟩
  have key : ∀ (w z P Q : ℕ), 2 ≤ w → 2 ≤ z → 1 ≤ P → 1 ≤ Q →
      0 < (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z →
      (Q : ℝ) * Real.log w - (P : ℝ) * Real.log z < ε →
      z ^ P < w ^ Q ∧ q * (w ^ Q) ^ K < p * (z ^ P) ^ K := by
    intro w z P Q hw hz hP hQ hgt hlt2
    have hzw : (z : ℝ) ^ P < (w : ℝ) ^ Q := by
      have hl : Real.log ((z : ℝ) ^ P) < Real.log ((w : ℝ) ^ Q) := by
        simp only [Real.log_pow]; linarith
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hl
    refine ⟨by exact_mod_cast hzw, ?_⟩
    have hstep := mul_lt_mul_of_pos_left hlt2 hKR
    have hKε : (K : ℝ) * ε = η := by rw [hεdef]; field_simp
    rw [hKε, mul_sub, hηdef] at hstep
    have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have hreal : (q : ℝ) * ((w : ℝ) ^ Q) ^ K < (p : ℝ) * ((z : ℝ) ^ P) ^ K := by
      have hloglt : Real.log ((q : ℝ) * ((w : ℝ) ^ Q) ^ K)
          < Real.log ((p : ℝ) * ((z : ℝ) ^ P) ^ K) := by
        rw [Real.log_mul hq0R.ne' (by positivity), Real.log_mul hp0R.ne' (by positivity)]
        simp only [Real.log_pow]
        linarith [hstep]
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hloglt
    have hcast : ((q * (w ^ Q) ^ K : ℕ) : ℝ) < ((p * (z ^ P) ^ K : ℕ) : ℝ) := by
      push_cast; push_cast at hreal; linarith
    exact_mod_cast hcast
  rcases hcase with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · have e1 : (m.toNat : ℝ) = (m : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ m)
    have e2 : ((-n).toNat : ℝ) = -(n : ℝ) := by
      have : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨a, b, (-n).toNat, m.toNat, ha, hb, hab, Or.inl ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (m.toNat : ℝ) * Real.log a - ((-n).toNat : ℝ) * Real.log b < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key a b (-n).toNat m.toNat ha hb (by omega) (by omega) hgt hlt2
  · have e1 : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ n)
    have e2 : ((-m).toNat : ℝ) = -(m : ℝ) := by
      have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    refine ⟨b, a, (-m).toNat, n.toNat, hb, ha, hab.symm, Or.inr ⟨rfl, rfl⟩, by omega, by omega, ?_⟩
    have hgt : 0 < (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a := by
      rw [e1, e2]; nlinarith [hpos]
    have hlt2 : (n.toNat : ℝ) * Real.log b - ((-m).toNat : ℝ) * Real.log a < ε := by
      rw [e1, e2]; nlinarith [hlt]
    exact key b a (-m).toNat n.toNat hb ha (by omega) (by omega) hgt hlt2

set_option maxHeartbeats 1000000 in
theorem gladder_count {a b c p q w z P Q K : ℕ}
    (hz : 2 ≤ z) (hq : 0 < q) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hK : 1 ≤ K)
    (hlt : z ^ P < w ^ Q) (hratio : q * (w ^ Q) ^ K < p * (z ^ P) ^ K)
    (hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (GBand a b c p q x).card := by
  set r : ℕ := w ^ Q with hrdef
  set s : ℕ := z ^ P with hsdef
  have hs2 : 2 ≤ s := le_trans hz (by rw [hsdef]; exact Nat.le_self_pow (by omega) z)
  have hsr : s < r := hlt
  have hsr1 : s + 1 ≤ r := hsr
  have hs0 : 0 < s := by omega
  have hr0 : 0 < r := by omega
  set E : ℕ → ℕ → ℕ := fun N j => r ^ j * s ^ (N - j) with hEdef
  have hEpos : ∀ N j, 0 < E N j := fun N j => by
    simp only [hEdef]
    exact Nat.mul_pos (pow_pos hr0 _) (pow_pos hs0 _)
  have hEmem : ∀ N j, E N j ∈ Smooth3 a b c := by
    intro N j
    simp only [hEdef, hrdef, hsdef, ← pow_mul]
    exact hmem (Q * j) (P * (N - j))
  have hIter : ∀ N j i, j + i ≤ N → E N j * r ^ i = E N (j + i) * s ^ i := by
    intro N j i hji
    simp only [hEdef]
    rw [mul_right_comm, ← pow_add, mul_assoc, ← pow_add]
    congr 2 <;> omega
  have hMono : ∀ N j, j + 1 ≤ N → E N j < E N (j + 1) := by
    intro N j hj
    have hrec : E N j * r = E N (j + 1) * s := by
      have := hIter N j 1 (by omega); simpa using this
    have h1 : E N j * s < E N (j + 1) * s := by
      calc E N j * s < E N j * r := mul_lt_mul_of_pos_left hsr (hEpos N j)
        _ = E N (j + 1) * s := hrec
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le s)
  have hMono' : ∀ N j j', j ≤ j' → j' ≤ N → E N j ≤ E N j' := by
    intro N j j' hjj hj'
    induction j' with
    | zero => exact le_of_eq (by rw [Nat.le_zero.mp hjj])
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hMono N k (by omega)))
      · have : j = k + 1 := by omega
        rw [this]
  have hStrict : ∀ N j j', j < j' → j' ≤ N → E N j < E N j' := by
    intro N j j' hjj hj'
    calc E N j < E N (j + 1) := hMono N j (by omega)
      _ ≤ E N j' := hMono' N (j + 1) j' (by omega) hj'
  set m2 : ℕ := s * s with hm2
  refine ⟨s ^ (2 * m2 + K), fun x hxX0 => ?_⟩
  have hx1 : 1 ≤ x := le_trans (Nat.one_le_two_pow.trans (by
    exact Nat.pow_le_pow_left (by omega) _)) hxX0
  have hx0 : 0 < x := hx1
  set N : ℕ := Nat.log s x with hNdef
  have hsN : s ^ N ≤ x := Nat.pow_log_le_self s (by omega)
  have hxlt : x < s ^ (N + 1) := Nat.lt_pow_succ_log_self (by omega) x
  have hNbig : 2 * m2 + K ≤ N := Nat.le_log_of_pow_le (by omega) hxX0
  have hKN : K ≤ N := by omega
  have htbig : s * s ≤ N - K + 1 := by rw [← hm2]; omega
  have hbigmid : x ≤ E N (N - K + 1) := by
    have hchain : s ^ (N + 1) ≤ E N (N - K + 1) := by
      have hEval : E N (N - K + 1) = r ^ (N - K + 1) * s ^ (K - 1) := by
        simp only [hEdef]; congr 2; omega
      rw [hEval]
      have hsplit : s ^ (N + 1) = s ^ (N - K + 1 + 1) * s ^ (K - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      exact Nat.mul_le_mul_right _ (pow_succ_le_pow hs2 hsr1 htbig)
    omega
  have hex : ∃ j, x ≤ E N j := ⟨N - K + 1, hbigmid⟩
  classical
  set J : ℕ := Nat.find hex with hJdef
  have hJspec : x ≤ E N J := Nat.find_spec hex
  have hJle : J ≤ N - K + 1 := Nat.find_le hbigmid
  have hJmin : ∀ j, j < J → E N j < x := by
    intro j hj; have := Nat.find_min hex hj; omega
  have hJsr : E N J * s < x * r := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · have hE0 : E N J = s ^ N := by rw [hJ0]; simp only [hEdef]; simp
      rw [hE0]
      calc s ^ N * s ≤ x * s := Nat.mul_le_mul_right _ hsN
        _ < x * r := mul_lt_mul_of_pos_left hsr hx0
    · have hjm1 : E N (J - 1) < x := hJmin (J - 1) (by omega)
      have hrec : E N (J - 1) * r = E N J * s := by
        have := hIter N (J - 1) 1 (by omega)
        rw [show J - 1 + 1 = J by omega] at this; simpa using this
      calc E N J * s = E N (J - 1) * r := hrec.symm
        _ ≤ (x - 1) * r := Nat.mul_le_mul_right _ (by omega)
        _ < x * r := mul_lt_mul_of_pos_right (by omega) hr0
  have hsK : s ^ K = s ^ (K - 1) * s := by rw [← pow_succ]; congr 1; omega
  have hrK : r ^ K = r ^ (K - 1) * r := by rw [← pow_succ]; congr 1; omega
  have fA : E N (J + K - 1) * s ^ (K - 1) = E N J * r ^ (K - 1) := by
    have hI := hIter N J (K - 1) (by omega)
    rw [show J + (K - 1) = J + K - 1 by omega] at hI
    exact hI.symm
  have hbig : q * E N (J + K - 1) * s ^ K < p * x * s ^ K := by
    calc q * E N (J + K - 1) * s ^ K
        = q * (E N (J + K - 1) * s ^ (K - 1)) * s := by rw [hsK]; ring
      _ = q * (E N J * r ^ (K - 1)) * s := by rw [fA]
      _ = (E N J * s) * (q * r ^ (K - 1)) := by ring
      _ < (x * r) * (q * r ^ (K - 1)) :=
          mul_lt_mul_of_pos_right hJsr (Nat.mul_pos hq (pow_pos hr0 _))
      _ = x * (q * r ^ K) := by rw [hrK]; ring
      _ < x * (p * s ^ K) := mul_lt_mul_of_pos_left hratio hx0
      _ = p * x * s ^ K := by ring
  have hupper : q * E N (J + K - 1) < p * x :=
    lt_of_mul_lt_mul_right hbig (Nat.zero_le _)
  have hmaps : ∀ i ∈ Finset.range K, E N (J + i) ∈ GBand a b c p q x := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [mem_GBand hq]
    refine ⟨hEmem N (J + i), le_trans hJspec (hMono' N J (J + i) (by omega) (by omega)), ?_⟩
    have hle : E N (J + i) ≤ E N (J + K - 1) :=
      hMono' N (J + i) (J + K - 1) (by omega) (by omega)
    calc q * E N (J + i) ≤ q * E N (J + K - 1) := Nat.mul_le_mul_left q hle
      _ < p * x := hupper
  have hinj : Set.InjOn (fun i => E N (J + i)) (Finset.range K) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd heq (ne_of_lt (hStrict N (J + i) (J + i') (by omega) (by omega)))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hStrict N (J + i') (J + i) (by omega) (by omega)))
  have hcard := Finset.card_le_card_of_injOn (fun i => E N (J + i)) hmaps hinj
  rwa [Finset.card_range] at hcard

set_option maxHeartbeats 1000000 in
theorem gband_card_eventually_ge {a b c p q : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) (K : ℕ) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → K ≤ (GBand a b c p q x).card := by
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · exact ⟨0, fun x _ => by rw [hK0]; exact Nat.zero_le _⟩
  have hpa : p < q * a :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q (min_le_left _ _))
  have hpb : p < q * b :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  obtain ⟨w, z, P, Q, hw, hz, hwz, horient, hP, hQ, hlt, hratio⟩ :=
    gexists_int_step hco.1 (by omega) (by omega) hq hqp hpa hpb K hK
  have hmem : ∀ i j : ℕ, w ^ i * z ^ j ∈ Smooth3 a b c := by
    intro i j
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨i, j, 0, by simp⟩
    · exact ⟨j, i, 0, by ring⟩
  exact gladder_count hz hq hP hQ hK hlt hratio hmem

set_option maxHeartbeats 1000000 in
noncomputable def GQenergy (a b c p q x : ℕ) (t : ℝ) : ℝ :=
  ∑ s ∈ GBand a b c p q x, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2

set_option maxHeartbeats 1000000 in
noncomputable def GchiBand (a b c p q x : ℕ) (t : ℝ) : ℝ :=
  ∏ s ∈ GBand a b c p q x, |Real.cos (Real.pi * ((s : ℝ) * t))|

set_option maxHeartbeats 1000000 in
lemma GQenergy_nonneg (a b c p q x : ℕ) (t : ℝ) : 0 ≤ GQenergy a b c p q x t :=
  Finset.sum_nonneg (fun s _ => sq_nonneg _)

set_option maxHeartbeats 1000000 in
lemma GchiBand_nonneg (a b c p q x : ℕ) (t : ℝ) : 0 ≤ GchiBand a b c p q x t :=
  Finset.prod_nonneg (fun s _ => abs_nonneg _)

set_option maxHeartbeats 1000000 in
lemma GQenergy_measurable (a b c p q x : ℕ) : Measurable (GQenergy a b c p q x) := by
  unfold GQenergy
  refine Finset.measurable_sum _ (fun s _ => ?_)
  have hst : Measurable (fun t : ℝ => (s : ℝ) * t) := measurable_const.mul measurable_id
  have hround : Measurable (fun t : ℝ => ((round ((s : ℝ) * t) : ℤ) : ℝ)) :=
    (measurable_of_countable _).comp (measurable_round_real.comp hst)
  exact (hst.sub hround).pow_const 2

set_option maxHeartbeats 1000000 in
lemma gexp_neg_two_Q_intervalIntegrable (a b c p q x : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t => Real.exp (-(2 * GQenergy a b c p q x t)))
      MeasureTheory.volume u v := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((Real.measurable_exp.comp
      ((GQenergy_measurable a b c p q x).const_mul 2).neg)).aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc Real.exp (-(2 * GQenergy a b c p q x t))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [GQenergy_nonneg a b c p q x t])
    _ = 1 := Real.exp_zero

set_option maxHeartbeats 1000000 in
lemma gchi_le_exp_neg_two_Q (a b c p q x : ℕ) (t : ℝ) :
    GchiBand a b c p q x t ≤ Real.exp (-(2 * GQenergy a b c p q x t)) := by
  have hle : GchiBand a b c p q x t
      ≤ ∏ s ∈ GBand a b c p q x, Real.exp (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2)) :=
    Finset.prod_le_prod (fun s _ => abs_nonneg _)
      (fun s _ => abs_cos_le_exp ((s : ℝ) * t))
  refine hle.trans (le_of_eq ?_)
  rw [← Real.exp_sum]
  congr 1
  have hpt : ∀ s ∈ GBand a b c p q x,
      (-(2 * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2))
        = (-2 : ℝ) * ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := fun s _ => by ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, GQenergy]
  ring

set_option maxHeartbeats 1000000 in
lemma GchiBand_continuous (a b c p q x : ℕ) : Continuous (GchiBand a b c p q x) := by
  unfold GchiBand; fun_prop

set_option maxHeartbeats 1000000 in
lemma GchiBand_intervalIntegrable (a b c p q x : ℕ) (u v : ℝ) :
    IntervalIntegrable (GchiBand a b c p q x) MeasureTheory.volume u v :=
  (GchiBand_continuous a b c p q x).intervalIntegrable u v

set_option maxHeartbeats 1000000 in
lemma gprod_abs_one_add_e (a b c p q x : ℕ) (t : ℝ) :
    (∏ s ∈ GBand a b c p q x, ‖1 + e ((s : ℝ) * t)‖)
      = 2 ^ (GBand a b c p q x).card * GchiBand a b c p q x t := by
  rw [GchiBand, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun s _ => one_add_e_norm ((s : ℝ) * t))

set_option maxHeartbeats 1000000 in
lemma gnorm_setIntegral_prod_le (a b c p q x n : ℕ) (S : Set ℝ) :
    ‖∫ t in S, (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ 2 ^ (GBand a b c p q x).card * ∫ t in S, GchiBand a b c p q x t := by
  calc ‖∫ t in S, (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖
      ≤ ∫ t in S, ‖(∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in S, 2 ^ (GBand a b c p q x).card * GchiBand a b c p q x t := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        dsimp only
        rw [norm_mul, e_norm, mul_one, norm_prod, gprod_abs_one_add_e]
    _ = 2 ^ (GBand a b c p q x).card * ∫ t in S, GchiBand a b c p q x t :=
        MeasureTheory.integral_const_mul _ _

set_option maxHeartbeats 1000000 in
def GMajorArc (p q x : ℕ) : Set ℝ :=
  {t | t ∈ Set.Ioc (0 : ℝ) 1 ∧
    (t ≤ (q : ℝ) / (8 * (p : ℝ) * (x : ℝ)) ∨ 1 - (q : ℝ) / (8 * (p : ℝ) * (x : ℝ)) ≤ t)}

set_option maxHeartbeats 1000000 in
def GMinorArc (p q x : ℕ) : Set ℝ := Set.Ioc (0 : ℝ) 1 \ GMajorArc p q x

set_option maxHeartbeats 1000000 in
lemma gmeasurableSet_MajorArc (p q x : ℕ) : MeasurableSet (GMajorArc p q x) := by
  have heq : GMajorArc p q x = Set.Ioc (0 : ℝ) 1 ∩
      (Set.Iic ((q : ℝ) / (8 * (p : ℝ) * (x : ℝ)))
        ∪ Set.Ici (1 - (q : ℝ) / (8 * (p : ℝ) * (x : ℝ)))) := by
    ext t; simp only [GMajorArc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union,
      Set.mem_Iic, Set.mem_Ici]
  rw [heq]; exact measurableSet_Ioc.inter (measurableSet_Iic.union measurableSet_Ici)

set_option maxHeartbeats 1000000 in
lemma gmeasurableSet_MinorArc (p q x : ℕ) : MeasurableSet (GMinorArc p q x) :=
  measurableSet_Ioc.diff (gmeasurableSet_MajorArc p q x)

set_option maxHeartbeats 1000000 in
lemma gintegral_chi_le_exp_on_minor (a b c p q x : ℕ) :
    (∫ t in GMinorArc p q x, GchiBand a b c p q x t)
      ≤ ∫ t in GMinorArc p q x, Real.exp (-(2 * GQenergy a b c p q x t)) := by
  have hmm : GMinorArc p q x ⊆ Set.Ioc (0 : ℝ) 1 := Set.diff_subset
  have hχ : MeasureTheory.IntegrableOn (GchiBand a b c p q x) (GMinorArc p q x)
      MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (GchiBand_intervalIntegrable a b c p q x 0 1))).mono_set hmm
  have hexp : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * GQenergy a b c p q x t)))
      (GMinorArc p q x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (gexp_neg_two_Q_intervalIntegrable a b c p q x 0 1))).mono_set hmm
  exact MeasureTheory.setIntegral_mono_on hχ hexp (gmeasurableSet_MinorArc p q x)
    (fun t _ => gchi_le_exp_neg_two_Q a b c p q x t)

set_option maxHeartbeats 1000000 in
lemma gminor_meas_le {a b c p q x : ℕ} {z M : ℝ}
    (hz : MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
            ≤ ENNReal.ofReal M) :
    MeasureTheory.volume {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ z}
      ≤ ENNReal.ofReal M := by
  have hsub : {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ z}
      ⊆ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z} ∪ ({1} : Set ℝ) := by
    rintro t ⟨htm, htq⟩
    have htioc : t ∈ Set.Ioc (0 : ℝ) 1 := htm.1
    rcases eq_or_lt_of_le htioc.2 with h1 | h1
    · exact Or.inr h1
    · exact Or.inl ⟨⟨le_of_lt htioc.1, h1⟩, htq⟩
  calc MeasureTheory.volume {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ z}
      ≤ MeasureTheory.volume
          ({t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z} ∪ ({1} : Set ℝ)) :=
        MeasureTheory.measure_mono hsub
    _ ≤ MeasureTheory.volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ z}
          + MeasureTheory.volume ({1} : Set ℝ) := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal M := by rw [Real.volume_singleton, add_zero]; exact hz

set_option maxHeartbeats 1000000 in
lemma gminor_exp_integral_le (a b c p q x : ℕ) {κ₀ Mbound : ℝ}
    (hfloor : ∀ t ∈ GMinorArc p q x, κ₀ * Real.log x ≤ GQenergy a b c p q x t)
    (hmeas : (MeasureTheory.volume
        {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ Real.log x}).toReal ≤ Mbound) :
    (∫ t in GMinorArc p q x, Real.exp (-(2 * GQenergy a b c p q x t)))
      ≤ Real.exp (-(2 * κ₀ * Real.log x)) * Mbound + Real.exp (-(2 * Real.log x)) := by
  have hmeas𝔪 : MeasurableSet (GMinorArc p q x) := gmeasurableSet_MinorArc p q x
  have hmeasQ : MeasurableSet {t : ℝ | GQenergy a b c p q x t ≤ Real.log x} :=
    measurableSet_le (GQenergy_measurable a b c p q x) measurable_const
  have hInt : MeasureTheory.IntegrableOn (fun t => Real.exp (-(2 * GQenergy a b c p q x t)))
      (GMinorArc p q x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (gexp_neg_two_Q_intervalIntegrable a b c p q x 0 1))).mono_set Set.diff_subset
  have hvolIoc : MeasureTheory.volume (Set.Ioc (0 : ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; simp
  have hfin : ∀ S : Set ℝ, S ⊆ GMinorArc p q x → MeasureTheory.volume S < ⊤ := fun S hS =>
    lt_of_le_of_lt (MeasureTheory.measure_mono (hS.trans Set.diff_subset)) hvolIoc
  rw [← MeasureTheory.integral_inter_add_sdiff hmeasQ hInt]
  refine add_le_add ?_ ?_
  · have hsetle : (∫ t in GMinorArc p q x ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in GMinorArc p q x ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * κ₀ * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.inter_subset_left)
        (MeasureTheory.integrableOn_const (hfin _ Set.inter_subset_left).ne)
        (hmeas𝔪.inter hmeasQ) (fun t ht => ?_)
      exact Real.exp_le_exp.mpr (by linarith [hfloor t ht.1])
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    rw [show GMinorArc p q x ∩ {t | GQenergy a b c p q x t ≤ Real.log x}
        = {t : ℝ | t ∈ GMinorArc p q x ∧ GQenergy a b c p q x t ≤ Real.log x} from by
      ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]]
    exact hmeas
  · have hsetle : (∫ t in GMinorArc p q x \ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in GMinorArc p q x \ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.diff_subset)
        (MeasureTheory.integrableOn_const (hfin _ Set.diff_subset).ne)
        (hmeas𝔪.diff hmeasQ) (fun t ht => ?_)
      have hQ : Real.log x < GQenergy a b c p q x t := by
        have h2 := ht.2; simp only [Set.mem_setOf_eq, not_le] at h2; exact h2
      exact Real.exp_le_exp.mpr (by linarith)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)).trans (le_of_eq (mul_one _))
    calc (MeasureTheory.volume
          (GMinorArc p q x \ {t | GQenergy a b c p q x t ≤ Real.log x})).toReal
        ≤ (MeasureTheory.volume (Set.Ioc (0 : ℝ) 1)).toReal :=
          ENNReal.toReal_mono hvolIoc.ne
            (MeasureTheory.measure_mono (Set.diff_subset.trans Set.diff_subset))
      _ = 1 := by rw [Real.volume_Ioc]; simp

set_option maxHeartbeats 1000000 in
lemma gprod_one_add_e_eq (a b c p q x : ℕ) (t : ℝ) :
    (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t)))
      = 2 ^ (GBand a b c p q x).card
        * ((∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ)
        * e ((GS1 a b c p q x : ℝ) * t / 2) := by
  simp only [one_add_e_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Complex.ofReal_prod]
  congr 1
  rw [show (∏ s ∈ GBand a b c p q x, e ((s : ℝ) * t / 2))
      = ∏ s ∈ GBand a b c p q x, e ((s : ℝ) * (t / 2)) from by
    refine Finset.prod_congr rfl (fun s _ => ?_); rw [mul_div_assoc], prod_e]
  congr 1
  rw [GS1]
  simp only [id_eq]
  ring

set_option maxHeartbeats 1000000 in
lemma gintegrand_re (a b c p q x n : ℕ) (t : ℝ) :
    ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = 2 ^ (GBand a b c p q x).card
        * (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hre : ∀ β : ℝ, (e β).re = Real.cos (2 * Real.pi * β) := by
    intro β
    have hb : e β = Complex.exp ((↑(2 * Real.pi * β) : ℂ) * Complex.I) := by
      rw [e]; congr 1; push_cast; ring
    rw [hb, Complex.exp_ofReal_mul_I_re]
  rw [gprod_one_add_e_eq, mul_assoc, ← e_add,
    show ((2 : ℂ) ^ (GBand a b c p q x).card
          * ((∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)) : ℝ) : ℂ))
        = (((2 : ℝ) ^ (GBand a b c p q x).card
            * (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t))) : ℝ) : ℂ) by
      push_cast; ring,
    Complex.re_ofReal_mul, hre]
  congr 1
  rw [show 2 * Real.pi * ((GS1 a b c p q x : ℝ) * t / 2 + -((n : ℝ) * t))
      = Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t) by ring]

set_option maxHeartbeats 1000000 in
lemma gmajor_arc_re_eq (a b c p q x n : ℕ) :
    (∫ t in GMajorArc p q x,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in GMajorArc p q x, 2 ^ (GBand a b c p q x).card
          * (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  have hInt : MeasureTheory.IntegrableOn
      (fun t => (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      (GMajorArc p q x) MeasureTheory.volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((by unfold e; fun_prop : Continuous
        (fun t => (∏ s ∈ GBand a b c p q x,
          (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))).intervalIntegrable
        0 1))).mono_set (fun t ht => ht.1)
  have hre_int : (∫ t in GMajorArc p q x,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in GMajorArc p q x,
          ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re := by
    simpa using (Complex.reCLM.integral_comp_comm hInt).symm
  rw [hre_int]
  exact MeasureTheory.setIntegral_congr_fun (gmeasurableSet_MajorArc p q x)
    (fun t _ => gintegrand_re a b c p q x n t)

set_option maxHeartbeats 1000000 in
lemma gle_S1_of_card_pos {a b c p q x : ℕ} (h : 1 ≤ (GBand a b c p q x).card) :
    x ≤ GS1 a b c p q x := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp h
  calc x ≤ s := (of_mem_GBand hs).2.1
    _ = id s := rfl
    _ ≤ GS1 a b c p q x := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hs

set_option maxHeartbeats 1000000 in
lemma gS2_ge_card_sq (a b c p q x : ℕ) :
    (GBand a b c p q x).card * x ^ 2 ≤ GS2 a b c p q x := by
  have hstep : (GBand a b c p q x).card • (x ^ 2)
      ≤ (GBand a b c p q x).sum (fun s => s ^ 2) := by
    apply Finset.card_nsmul_le_sum
    intro s hs
    exact Nat.pow_le_pow_left (of_mem_GBand hs).2.1 2
  simpa [smul_eq_mul, GS2] using hstep

set_option maxHeartbeats 1000000 in
lemma gS2_upper {a b c p q : ℕ} (hq : 0 < q) (x : ℕ) :
    GS2 a b c p q x ≤ (GBand a b c p q x).card * (p * x) ^ 2 := by
  unfold GS2
  calc (GBand a b c p q x).sum (fun s => s ^ 2)
      ≤ (GBand a b c p q x).sum (fun _ => (p * x) ^ 2) := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        exact Nat.pow_le_pow_left (gband_le hq hs) 2
    _ = (GBand a b c p q x).card * (p * x) ^ 2 := by rw [Finset.sum_const, smul_eq_mul]

set_option maxHeartbeats 1000000 in
lemma gS1_step_upper {a b c p q : ℕ} (hq : 0 < q) (x : ℕ) :
    GS1 a b c p q (x + 1) ≤ GS1 a b c p q x + p * p * (x + 1) := by
  classical
  have hsplit :
      ((GBand a b c p q (x + 1)) \ (GBand a b c p q x)).sum id
        + ((GBand a b c p q (x + 1)) ∩ (GBand a b c p q x)).sum id
      = GS1 a b c p q (x + 1) := by
    rw [← Finset.sdiff_inter_self_left (GBand a b c p q (x + 1)) (GBand a b c p q x)]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have h1 : ((GBand a b c p q (x + 1)) ∩ (GBand a b c p q x)).sum id ≤ GS1 a b c p q x :=
    Finset.sum_le_sum_of_subset Finset.inter_subset_right
  set E : Finset ℕ := (GBand a b c p q (x + 1)) \ (GBand a b c p q x) with hE
  have hEprop : ∀ s ∈ E, p * x ≤ q * s ∧ q * s < p * (x + 1) := by
    intro s hs
    obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hS, hge, hlt⟩ := of_mem_GBand hmem
    refine ⟨?_, hlt⟩
    by_contra hcon
    push_neg at hcon
    exact hnot ((mem_GBand hq).mpr ⟨hS, by omega, hcon⟩)
  have hcard : E.card ≤ p := by
    have hmaps : ∀ s ∈ E, q * s ∈ Finset.Ico (p * x) (p * x + p) := by
      intro s hs
      obtain ⟨h2, h3⟩ := hEprop s hs
      rw [Finset.mem_Ico]
      refine ⟨h2, ?_⟩
      have : p * (x + 1) = p * x + p := by ring
      omega
    have hinj : Set.InjOn (fun s => q * s) E := by
      intro s hs t ht hst
      exact Nat.eq_of_mul_eq_mul_left hq hst
    have h4 := Finset.card_le_card_of_injOn (fun s => q * s) hmaps hinj
    rwa [Nat.card_Ico, Nat.add_sub_cancel_left] at h4
  have helem : ∀ s ∈ E, id s ≤ p * (x + 1) := by
    intro s hs
    obtain ⟨-, h3⟩ := hEprop s hs
    have hle : s ≤ q * s := Nat.le_mul_of_pos_left s hq
    exact le_of_lt (lt_of_le_of_lt hle h3)
  have h2 : E.sum id ≤ p * p * (x + 1) := by
    calc E.sum id ≤ E.card • (p * (x + 1)) := Finset.sum_le_card_nsmul E id _ helem
      _ = E.card * (p * (x + 1)) := smul_eq_mul _ _
      _ ≤ p * (p * (x + 1)) := Nat.mul_le_mul_right _ hcard
      _ = p * p * (x + 1) := by ring
  omega

end Erdos123Band
end Module_GBand

section Module_GSlab

namespace Erdos123Band

open Real

section ThreeRounding

variable {a b c : ℕ}

set_option maxHeartbeats 1000000 in
theorem gthree_rounding (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) {η : ℝ} (hη : 0 < η)
    (hηα : η < Real.log a) (hηβ : η < Real.log b) (hηγ : η < Real.log c) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L X Y Z : ℝ, 0 ≤ X → 0 ≤ Y → 0 ≤ Z →
      ¬(X = 0 ∧ Y = 0) → ¬(X = 0 ∧ Z = 0) → ¬(Y = 0 ∧ Z = 0) →
      (X = 0 ∨ 2 * R₀ ≤ X) → (Y = 0 ∨ 2 * R₀ ≤ Y) → (Z = 0 ∨ 2 * R₀ ≤ Z) →
      X * Real.log a + Y * Real.log b + Z * Real.log c = L + η / 2 →
      ∃ k l m : ℕ,
        (L ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
          k * Real.log a + l * Real.log b + m * Real.log c < L + η) ∧
        |(k : ℝ) - X| ≤ R₀ ∧ |(l : ℝ) - Y| ≤ R₀ ∧ |(m : ℝ) - Z| ≤ R₀ ∧
        (X = 0 → k = 0) ∧ (Y = 0 → l = 0) ∧ (Z = 0 → m = 0) := by
  obtain ⟨hab, hac, hbc⟩ := hco
  set α : ℝ := Real.log a with hαdef
  set β : ℝ := Real.log b with hβdef
  set γ : ℝ := Real.log c with hγdef
  have hα : 0 < α := log_base_pos ha
  have hβ : 0 < β := log_base_pos hb
  have hγ : 0 < γ := log_base_pos hc

  have hirr_ac : Irrational (α / γ) := by
    simpa [hαdef, hγdef] using log_ratio_irrational hac.symm hc ha
  have hirr_bc : Irrational (β / γ) := by
    simpa [hβdef, hγdef] using log_ratio_irrational hbc.symm hc hb
  have hirr_ab : Irrational (α / β) := by
    simpa [hαdef, hβdef] using log_ratio_irrational hab.symm hb ha
  obtain ⟨Rac, hRac1, hRac⟩ := two_rounding hα hγ hirr_ac hη hηγ
  obtain ⟨Rbc, hRbc1, hRbc⟩ := two_rounding hβ hγ hirr_bc hη hηγ
  obtain ⟨Rab, hRab1, hRab⟩ := two_rounding hα hβ hirr_ab hη hηβ
  set R₀ : ℝ := 1 + Rac + Rbc + Rab + β / (2 * γ) with hR₀def
  have hβγ0 : 0 < β / (2 * γ) := by positivity
  have hR₀1 : 1 ≤ R₀ := by simp only [hR₀def]; linarith
  refine ⟨R₀, hR₀1, fun L X Y Z hX0 hY0 hZ0 hXY hXZ hYZ hXalt hYalt hZalt hplane => ?_⟩
  by_cases hX : X = 0
  ·
    have hY' : 2 * R₀ ≤ Y := by
      rcases hYalt with h | h
      · exact absurd ⟨hX, h⟩ hXY
      · exact h
    have hZ' : 2 * R₀ ≤ Z := by
      rcases hZalt with h | h
      · exact absurd ⟨hX, h⟩ hXZ
      · exact h
    have hplane' : β * Y + γ * Z = L + η / 2 := by
      rw [hX] at hplane; linarith [hplane]
    have hYR : Rbc ≤ Y := by linarith [hR₀1, hRbc1, hβγ0, hRac1, hRab1]
    have hZR : Rbc ≤ Z := by linarith [hR₀1, hRbc1, hβγ0, hRac1, hRab1]
    obtain ⟨p, q, hp0, hq0, hlo, hhi, hpY, hqZ⟩ := hRbc L Y Z hYR hZR hplane'
    refine ⟨0, p.toNat, q.toNat, ?_, ?_, ?_, ?_, fun _ => rfl, ?_, ?_⟩
    · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hp0
      have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hq0
      constructor
      · push_cast
        rw [hpcast, hqcast]
        linarith [hlo]
      · push_cast
        rw [hpcast, hqcast]
        linarith [hhi]
    · rw [hX]
      simp only [Nat.cast_zero, sub_zero, abs_zero]
      linarith
    · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hp0
      rw [hpcast]
      linarith [hpY, hR₀1, hRac1, hRab1, hβγ0]
    · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hq0
      rw [hqcast]
      linarith [hqZ, hR₀1, hRac1, hRab1, hβγ0]
    · intro hY'0
      exfalso
      rw [hY'0] at hY'
      linarith [hR₀1]
    · intro hZ'0
      exfalso
      rw [hZ'0] at hZ'
      linarith [hR₀1]
  · by_cases hY : Y = 0
    ·
      have hX' : 2 * R₀ ≤ X := by
        rcases hXalt with h | h
        · exact absurd h hX
        · exact h
      have hZ' : 2 * R₀ ≤ Z := by
        rcases hZalt with h | h
        · exact absurd ⟨hY, h⟩ hYZ
        · exact h
      have hplane' : α * X + γ * Z = L + η / 2 := by
        rw [hY] at hplane; linarith [hplane]
      have hXR : Rac ≤ X := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
      have hZR : Rac ≤ Z := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
      obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqZ⟩ := hRac L X Z hXR hZR hplane'
      refine ⟨p.toNat, 0, q.toNat, ?_, ?_, ?_, ?_, ?_, fun _ => rfl, ?_⟩
      · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hp0
        have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hq0
        constructor
        · push_cast
          rw [hpcast, hqcast]
          linarith [hlo]
        · push_cast
          rw [hpcast, hqcast]
          linarith [hhi]
      · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hp0
        rw [hpcast]
        linarith [hpX, hR₀1, hRbc1, hRab1, hβγ0]
      · rw [hY]
        simp only [Nat.cast_zero, sub_zero, abs_zero]
        linarith
      · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hq0
        rw [hqcast]
        linarith [hqZ, hR₀1, hRbc1, hRab1, hβγ0]
      · intro hX'0; exact absurd hX'0 hX
      · intro hZ'0
        exfalso
        rw [hZ'0] at hZ'
        linarith [hR₀1]
    · by_cases hZ : Z = 0
      ·
        have hX' : 2 * R₀ ≤ X := by
          rcases hXalt with h | h
          · exact absurd h hX
          · exact h
        have hY' : 2 * R₀ ≤ Y := by
          rcases hYalt with h | h
          · exact absurd h hY
          · exact h
        have hplane' : α * X + β * Y = L + η / 2 := by
          rw [hZ] at hplane; linarith [hplane]
        have hXR : Rab ≤ X := by linarith [hR₀1, hRab1, hβγ0, hRbc1, hRac1]
        have hYR : Rab ≤ Y := by linarith [hR₀1, hRab1, hβγ0, hRbc1, hRac1]
        obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqY⟩ := hRab L X Y hXR hYR hplane'
        refine ⟨p.toNat, q.toNat, 0, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          constructor
          · push_cast
            rw [hpcast, hqcast]
            linarith [hlo]
          · push_cast
            rw [hpcast, hqcast]
            linarith [hhi]
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          rw [hpcast]
          linarith [hpX, hR₀1, hRbc1, hRac1, hβγ0]
        · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          rw [hqcast]
          linarith [hqY, hR₀1, hRbc1, hRac1, hβγ0]
        · rw [hZ]
          simp only [Nat.cast_zero, sub_zero, abs_zero]
          linarith
        · intro hX'0; exact absurd hX'0 hX
        · intro hY'0; exact absurd hY'0 hY
      ·
        have hX' : 2 * R₀ ≤ X := by
          rcases hXalt with h | h
          · exact absurd h hX
          · exact h
        have hY' : 2 * R₀ ≤ Y := by
          rcases hYalt with h | h
          · exact absurd h hY
          · exact h
        have hZ' : 2 * R₀ ≤ Z := by
          rcases hZalt with h | h
          · exact absurd h hZ
          · exact h
        set l₀ : ℤ := round Y with hl₀def
        have hl₀Y : |(l₀ : ℝ) - Y| ≤ 1 / 2 := by
          rw [abs_sub_comm]
          exact abs_sub_round Y
        have hl₀pos : (1 : ℝ) ≤ (l₀ : ℝ) := by
          have h1 := abs_le.mp hl₀Y
          linarith [hY', hR₀1, h1.1]
        have hl₀0 : 0 ≤ l₀ := by exact_mod_cast le_trans (by norm_num : (0:ℝ) ≤ 1) hl₀pos
        set Z' : ℝ := Z + (β / γ) * (Y - (l₀ : ℝ)) with hZ'def
        have hZ'Z : |Z' - Z| ≤ β / (2 * γ) := by
          simp only [hZ'def, add_sub_cancel_left]
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < β / γ), abs_sub_comm]
          calc (β / γ) * |(l₀ : ℝ) - Y| ≤ (β / γ) * (1 / 2) :=
                mul_le_mul_of_nonneg_left hl₀Y (by positivity)
            _ = β / (2 * γ) := by ring
        have hplane' : α * X + γ * Z' = (L - β * l₀) + η / 2 := by
          have hexp : γ * (β / γ * (Y - (l₀ : ℝ))) = β * (Y - (l₀ : ℝ)) := by
            have hγne : γ ≠ 0 := hγ.ne'
            field_simp
          calc α * X + γ * Z'
              = α * X + γ * Z + γ * (β / γ * (Y - (l₀ : ℝ))) := by
                rw [hZ'def]; ring
            _ = α * X + γ * Z + β * (Y - (l₀ : ℝ)) := by rw [hexp]
            _ = (L - β * l₀) + η / 2 := by linarith [hplane]
        have hXR : Rac ≤ X := by linarith [hR₀1, hRac1, hβγ0, hRbc1, hRab1]
        have hZ'R : Rac ≤ Z' := by
          have h1 := abs_le.mp hZ'Z
          have h2 : Z - β / (2 * γ) ≤ Z' := by linarith [h1.1]
          simp only [hR₀def] at hZ'
          linarith [hZ', hRbc1, hRab1]
        obtain ⟨p, q, hp0, hq0, hlo, hhi, hpX, hqZ'⟩ :=
          hRac (L - β * l₀) X Z' hXR hZ'R hplane'
        refine ⟨p.toNat, l₀.toNat, q.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          have hlcast : ((l₀.toNat : ℕ) : ℝ) = (l₀ : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hl₀0
          constructor
          · push_cast
            rw [hpcast, hqcast, hlcast]
            linarith [hlo]
          · push_cast
            rw [hpcast, hqcast, hlcast]
            linarith [hhi]
        · have hpcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hp0
          rw [hpcast]
          linarith [hpX, hR₀1, hRbc1, hRab1, hβγ0]
        · have hlcast : ((l₀.toNat : ℕ) : ℝ) = (l₀ : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hl₀0
          rw [hlcast]
          calc |(l₀ : ℝ) - Y| ≤ 1 / 2 := hl₀Y
            _ ≤ R₀ := by linarith [hR₀1]
        · have hqcast : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
            exact_mod_cast Int.toNat_of_nonneg hq0
          rw [hqcast]
          have h1 : |(q : ℝ) - Z| ≤ |(q : ℝ) - Z'| + |Z' - Z| := abs_sub_le _ _ _
          simp only [hR₀def]
          linarith [hqZ', hZ'Z, hRbc1, hRab1]
        · intro hX'0; exact absurd hX'0 hX
        · intro hY'0; exact absurd hY'0 hY
        · intro hZ'0; exact absurd hZ'0 hZ

end ThreeRounding

section Dictionary

variable {a b c p q : ℕ}

set_option maxHeartbeats 1000000 in
theorem mem_GBand_iff_slab (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hq : 0 < q) (hp : 0 < p) {x : ℕ} (hx : 1 ≤ x) (k l m : ℕ) :
    a ^ k * b ^ l * c ^ m ∈ GBand a b c p q x ↔
      (Real.log x ≤ k * Real.log a + l * Real.log b + m * Real.log c ∧
        k * Real.log a + l * Real.log b + m * Real.log c
          < Real.log x + (Real.log p - Real.log q)) := by
  set s : ℕ := a ^ k * b ^ l * c ^ m with hsdef
  have hapos : (0 : ℝ) < (a : ℝ) := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    have : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    linarith
  have hspos : 0 < s := by
    simp only [hsdef]
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
      (pow_pos (by omega) _)
  have hsposR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have hxposR : (0 : ℝ) < (x : ℝ) := by
    have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpposR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogs : Real.log s = k * Real.log a + l * Real.log b + m * Real.log c := by
    have hcast : (s : ℝ) = (a : ℝ) ^ k * (b : ℝ) ^ l * (c : ℝ) ^ m := by
      simp only [hsdef]; push_cast; ring
    rw [hcast, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  have hmemS : s ∈ Smooth3 a b c := ⟨k, l, m, rfl⟩
  rw [mem_GBand hq]
  constructor
  · rintro ⟨-, hxs, h2s⟩
    constructor
    · rw [← hlogs]
      apply Real.log_le_log hxposR
      exact_mod_cast hxs
    · rw [← hlogs]
      have h1 : (q : ℝ) * (s : ℝ) < (p : ℝ) * (x : ℝ) := by exact_mod_cast h2s
      have h2 : Real.log ((q : ℝ) * (s : ℝ)) < Real.log ((p : ℝ) * (x : ℝ)) :=
        Real.log_lt_log (by positivity) h1
      rw [Real.log_mul hqposR.ne' hsposR.ne', Real.log_mul hpposR.ne' hxposR.ne'] at h2
      linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨hmemS, ?_, ?_⟩
    · rw [← hlogs] at hlo
      have h1 : (x : ℝ) ≤ (s : ℝ) := by
        have := Real.log_le_log_iff hxposR hsposR
        exact this.mp hlo
      exact_mod_cast h1
    · rw [← hlogs] at hhi
      have h1 : Real.log ((q : ℝ) * (s : ℝ)) < Real.log ((p : ℝ) * (x : ℝ)) := by
        rw [Real.log_mul hqposR.ne' hsposR.ne', Real.log_mul hpposR.ne' hxposR.ne']
        linarith
      have h2 : (q : ℝ) * (s : ℝ) < (p : ℝ) * (x : ℝ) :=
        (Real.log_lt_log_iff (by positivity) (by positivity)).mp h1
      exact_mod_cast h2

end Dictionary

section BandCount

variable {a b c p q : ℕ}

set_option maxHeartbeats 1000000 in
theorem gband_card_le_sq (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hpc : p < q * c) (x : ℕ) :
    (GBand a b c p q x).card ≤ (Nat.log 2 (2 * p * x) + 1) ^ 2 := by
  classical
  set K := Nat.log 2 (2 * p * x) with hK
  set f : ℕ → ℕ × ℕ := fun s => ((expTriple a b c s).1, (expTriple a b c s).2.1) with hf
  have hle2px : ∀ s ∈ GBand a b c p q x, s ≤ 2 * p * x := by
    intro s hs
    have h1 : s ≤ p * x := gband_le hq hs
    have h2 : p * x ≤ 2 * p * x := Nat.mul_le_mul_right x (by omega)
    omega
  have hmaps : ∀ s ∈ GBand a b c p q x,
      f s ∈ Finset.range (K + 1) ×ˢ Finset.range (K + 1) := by
    intro s hs
    obtain ⟨hS, hxs, h2s⟩ := of_mem_GBand hs
    have hspos : 0 < s := by
      obtain ⟨k, l, m, hklm⟩ := hS
      rw [hklm]
      exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
        (pow_pos (by omega) _)
    have hs2x : s ≤ 2 * p * x := hle2px s hs
    have hspec := expTriple_spec (a := a) (b := b) (c := c) hS
    set k := (expTriple a b c s).1
    set l := (expTriple a b c s).2.1
    set m := (expTriple a b c s).2.2
    have hbpos : 0 < b ^ l := pow_pos (by omega) l
    have hcpos : 0 < c ^ m := pow_pos (by omega) m
    have hapos : 0 < a ^ k := pow_pos (by omega) k
    have hak : a ^ k ≤ s := by
      rw [hspec, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hbpos hcpos)
    have hbl : b ^ l ≤ s := by
      rw [hspec]
      calc b ^ l ≤ a ^ k * b ^ l := Nat.le_mul_of_pos_left _ hapos
        _ ≤ a ^ k * b ^ l * c ^ m := Nat.le_mul_of_pos_right _ hcpos
    have hbound : ∀ d e : ℕ, 2 ≤ d → d ^ e ≤ s → e ≤ K := by
      intro d e hd hde
      rw [hK]
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ e ≤ d ^ e := Nat.pow_le_pow_left hd e
        _ ≤ s := hde
        _ ≤ 2 * p * x := hs2x
    simp only [hf, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound a k ha hak), Nat.lt_succ_of_le (hbound b l hb hbl)⟩
  have hinj : Set.InjOn f (GBand a b c p q x) := by
    intro s hs s' hs' heq
    obtain ⟨hS, hxs, h2s⟩ := of_mem_GBand hs
    obtain ⟨hS', hxs', h2s'⟩ := of_mem_GBand hs'
    have hspec := expTriple_spec (a := a) (b := b) (c := c) hS
    have hspec' := expTriple_spec (a := a) (b := b) (c := c) hS'
    have hkk : (expTriple a b c s).1 = (expTriple a b c s').1 := by
      have := congrArg Prod.fst heq; simpa [hf] using this
    have hll : (expTriple a b c s).2.1 = (expTriple a b c s').2.1 := by
      have := congrArg Prod.snd heq; simpa [hf] using this
    set k := (expTriple a b c s).1
    set l := (expTriple a b c s).2.1
    set m := (expTriple a b c s).2.2
    set m' := (expTriple a b c s').2.2
    rw [← hkk, ← hll] at hspec'

    have hmm : m = m' := by
      by_contra hne
      rcases Nat.lt_or_ge m m' with hlt | hge
      ·
        have hdiv : s' = s * c ^ (m' - m) := by
          have hpow : c ^ m * c ^ (m' - m) = c ^ m' := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : c ≤ c ^ (m' - m) := by
          calc c = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m' - m) := Nat.pow_le_pow_right (by omega) (by omega)
        have hspos : 0 < s := by
          rw [hspec]
          exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
            (pow_pos (by omega) _)
        have h6 : q * c * s ≤ q * s' := by
          rw [hdiv]
          calc q * c * s = q * (c * s) := by ring
            _ ≤ q * (c ^ (m' - m) * s) :=
                Nat.mul_le_mul_left q (Nat.mul_le_mul_right s hcge)
            _ = q * (s * c ^ (m' - m)) := by ring
        have h7 : p * x ≤ p * s := Nat.mul_le_mul_left p hxs
        have h8 : p * s < q * c * s := (Nat.mul_lt_mul_right hspos).mpr hpc
        exact absurd (calc q * s' < p * x := h2s'
          _ ≤ p * s := h7
          _ < q * c * s := h8
          _ ≤ q * s' := h6) (lt_irrefl _)
      · have hlt : m' < m := by omega
        have hdiv : s = s' * c ^ (m - m') := by
          have hpow : c ^ m' * c ^ (m - m') = c ^ m := by
            rw [← pow_add]
            congr 1
            omega
          rw [hspec, hspec', ← hpow]
          ring
        have hcge : c ≤ c ^ (m - m') := by
          calc c = c ^ 1 := (pow_one c).symm
            _ ≤ c ^ (m - m') := Nat.pow_le_pow_right (by omega) (by omega)
        have hspos' : 0 < s' := by
          rw [hspec']
          exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
            (pow_pos (by omega) _)
        have h6 : q * c * s' ≤ q * s := by
          rw [hdiv]
          calc q * c * s' = q * (c * s') := by ring
            _ ≤ q * (c ^ (m - m') * s') :=
                Nat.mul_le_mul_left q (Nat.mul_le_mul_right s' hcge)
            _ = q * (s' * c ^ (m - m')) := by ring
        have h7 : p * x ≤ p * s' := Nat.mul_le_mul_left p hxs'
        have h8 : p * s' < q * c * s' := (Nat.mul_lt_mul_right hspos').mpr hpc
        exact absurd (calc q * s < p * x := h2s
          _ ≤ p * s' := h7
          _ < q * c * s' := h8
          _ ≤ q * s := h6) (lt_irrefl _)
    rw [hspec, hspec', hmm]
  calc (GBand a b c p q x).card
      ≤ (Finset.range (K + 1) ×ˢ Finset.range (K + 1)).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = (K + 1) ^ 2 := by
        rw [Finset.card_product, Finset.card_range]; ring

end BandCount

end Erdos123Band
end Module_GSlab

section Module_GGrid

namespace Erdos123Band

section GGridEmbedding

set_option maxHeartbeats 1000000 in
theorem ggrid_embedding {a b c p q : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ c₀ C₀ : ℝ, ∃ D : ℕ, 0 < c₀ ∧ 0 < C₀ ∧ 1 ≤ D ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
      ∃ n : ℕ, ∃ Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ,
        (c₀ * Real.log x ≤ (n : ℝ) ∧ (n : ℝ) ≤ C₀ * Real.log x) ∧
        (∀ v ∈ Tri n, wt a b c (Φ v) ∈ GBand a b c p q x) ∧
        (∀ v ∈ Tri n, ∀ w ∈ Tri n, wt a b c (Φ v) = wt a b c (Φ w) → v = w) ∧
        (∀ v ∈ Tri n,
          (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
          (v.2.2 = 0 → (Φ v).2.2 = 0)) ∧
        (∀ v ∈ Tri n, ∀ w ∈ Tri n,
          (v.1 ≤ w.1 + 1 ∧ w.1 ≤ v.1 + 1 ∧ v.2.1 ≤ w.2.1 + 1 ∧ w.2.1 ≤ v.2.1 + 1 ∧
            v.2.2 ≤ w.2.2 + 1 ∧ w.2.2 ≤ v.2.2 + 1) →
          ((Φ v).1 ≤ (Φ w).1 + D ∧ (Φ w).1 ≤ (Φ v).1 + D ∧
            (Φ v).2.1 ≤ (Φ w).2.1 + D ∧ (Φ w).2.1 ≤ (Φ v).2.1 + D ∧
            (Φ v).2.2 ≤ (Φ w).2.2 + D ∧ (Φ w).2.2 ≤ (Φ v).2.2 + D)) := by
  classical
  have hp0 : 0 < p := by omega
  have hpa : p < q * a :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q (min_le_left _ _))
  have hpb : p < q * b :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hpc : p < q * c :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  set α : ℝ := Real.log a with hαdef
  set β : ℝ := Real.log b with hβdef
  set γ : ℝ := Real.log c with hγdef
  set η : ℝ := Real.log p - Real.log q with hηdef
  have hα : 0 < α := log_base_pos ha
  have hβ : 0 < β := log_base_pos hb
  have hγ : 0 < γ := log_base_pos hc
  have hη : 0 < η := geta_pos hq hqp
  have hηα : η < α := geta_lt_log hq hp0 hpa
  have hηβ : η < β := geta_lt_log hq hp0 hpb
  have hηγ : η < γ := geta_lt_log hq hp0 hpc
  obtain ⟨R₀, hR₀1, hround⟩ := gthree_rounding ha hb hc hco hη hηα hηβ hηγ
  set M₀ : ℝ := max α (max β γ) with hM₀def
  set m₀ : ℝ := min α (min β γ) with hm₀def
  have hM₀ : 0 < M₀ := lt_of_lt_of_le hα (le_max_left _ _)
  have hm₀ : 0 < m₀ := by
    simp only [hm₀def, lt_min_iff]
    exact ⟨hα, hβ, hγ⟩
  have hαM : α ≤ M₀ := le_max_left _ _
  have hβM : β ≤ M₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hγM : γ ≤ M₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmα : m₀ ≤ α := min_le_left _ _
  have hmβ : m₀ ≤ β := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmγ : m₀ ≤ γ := le_trans (min_le_right _ _) (min_le_right _ _)
  set τ₀ : ℝ := (4 * R₀ + 1) * M₀ with hτ₀def
  have hτ₀ : 0 < τ₀ := by
    apply mul_pos ?_ hM₀
    linarith
  have hτ₀M : τ₀ / M₀ = 4 * R₀ + 1 := by
    rw [hτ₀def, mul_div_assoc, div_self hM₀.ne', mul_one]

  set Dr : ℝ := 2 * R₀ + 2 * τ₀ / m₀ with hDrdef
  have hDrpos : 0 < Dr := by positivity
  set D : ℕ := ⌈Dr⌉₊ with hDdef
  have hDrD : Dr ≤ (D : ℝ) := Nat.le_ceil Dr
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    apply Nat.one_le_ceil_iff.mpr hDrpos

  set T : ℝ := 4 * τ₀ + 2 with hTdef
  set X₀ : ℕ := max 2 ⌈Real.exp T⌉₊ with hX₀def
  refine ⟨1 / (2 * τ₀), 2 / τ₀, D, by positivity, by positivity, hD1, X₀,
    le_max_left _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := by omega
  set L : ℝ := Real.log x with hLdef
  have hLT : T ≤ L := by
    have hxT : Real.exp T ≤ (x : ℝ) := by
      calc Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hx
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos T) hxT
  have hL0 : 0 < L := by
    have hT0 : (0 : ℝ) < T := by simp only [hTdef]; positivity
    linarith
  set Λ : ℝ := L + η / 2 with hΛdef
  have hΛ0 : 0 < Λ := by positivity
  have hLΛ : L ≤ Λ := by simp only [hΛdef]; linarith
  have hητ₀ : η < τ₀ := by
    have h1 : η < M₀ := lt_of_lt_of_le hηα hαM
    have h2 : M₀ ≤ τ₀ := by
      rw [hτ₀def]
      nlinarith [hR₀1, hM₀]
    linarith
  have hΛ2L : Λ ≤ 2 * L := by
    simp only [hΛdef]
    have hη2L : η / 2 ≤ L := by
      simp only [hTdef] at hLT
      linarith [hτ₀, hητ₀]
    linarith
  set n : ℕ := ⌊Λ / τ₀⌋₊ with hndef
  have hn1 : 1 ≤ n := by
    rw [hndef]
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hτ₀, one_mul]
    simp only [hΛdef, hTdef] at hLT ⊢
    nlinarith [hη]
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  set τ : ℝ := Λ / n with hτdef
  have hτpos : 0 < τ := div_pos hΛ0 hn0R
  have hτlow : τ₀ ≤ τ := by
    rw [hτdef, le_div_iff₀ hn0R]
    have h1 : (n : ℝ) ≤ Λ / τ₀ := Nat.floor_le (by positivity)
    calc τ₀ * (n : ℝ) = (n : ℝ) * τ₀ := by ring
      _ ≤ (Λ / τ₀) * τ₀ := mul_le_mul_of_nonneg_right h1 hτ₀.le
      _ = Λ := div_mul_cancel₀ _ hτ₀.ne'
  have hτhigh : τ ≤ 2 * τ₀ := by
    rw [hτdef, div_le_iff₀ hn0R]
    have h1 : Λ / τ₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Λ < ((n : ℝ) + 1) * τ₀ := by
      calc Λ = (Λ / τ₀) * τ₀ := (div_mul_cancel₀ _ hτ₀.ne').symm
        _ < ((n : ℝ) + 1) * τ₀ := mul_lt_mul_of_pos_right h1 hτ₀
    nlinarith [hτ₀, hn1R]
  have hτn : τ * (n : ℝ) = Λ := by
    rw [hτdef]
    field_simp

  have hnlow : 1 / (2 * τ₀) * L ≤ (n : ℝ) := by
    have h1 : Λ / τ₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Λ < ((n : ℝ) + 1) * τ₀ := by
      calc Λ = (Λ / τ₀) * τ₀ := (div_mul_cancel₀ _ hτ₀.ne').symm
        _ < ((n : ℝ) + 1) * τ₀ := mul_lt_mul_of_pos_right h1 hτ₀
    have h3 : L < ((n : ℝ) + 1) * τ₀ := lt_of_le_of_lt hLΛ h2
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < 2 * τ₀)]
    nlinarith [hn1R, hτ₀]
  have hnhigh : (n : ℝ) ≤ 2 / τ₀ * L := by
    have h1 : (n : ℝ) ≤ Λ / τ₀ := Nat.floor_le (by positivity)
    have h2 : Λ / τ₀ ≤ (2 * L) / τ₀ := by gcongr
    calc (n : ℝ) ≤ Λ / τ₀ := h1
      _ ≤ (2 * L) / τ₀ := h2
      _ = 2 / τ₀ * L := by ring

  set Xc : ℕ → ℝ := fun i => τ * i / α with hXcdef
  set Yc : ℕ → ℝ := fun j => τ * j / β with hYcdef
  set Zc : ℕ → ℝ := fun r => τ * r / γ with hZcdef

  have coord_pos : ∀ (p : ℕ) (u : ℝ), 0 < u → u ≤ M₀ → 1 ≤ p →
      4 * R₀ + 1 ≤ τ * p / u := by
    intro p u hu huM hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    rw [le_div_iff₀ hu]
    have h1 : τ₀ ≤ τ * p := by
      calc τ₀ = τ₀ * 1 := (mul_one _).symm
        _ ≤ τ * (p : ℝ) := by
            apply mul_le_mul hτlow hp1 (by norm_num) hτpos.le
    calc (4 * R₀ + 1) * u ≤ (4 * R₀ + 1) * M₀ := by
          apply mul_le_mul_of_nonneg_left huM (by linarith)
      _ = τ₀ := hτ₀def.symm
      _ ≤ τ * p := h1
  have coord_sep : ∀ (p q : ℕ) (u : ℝ), 0 < u → u ≤ M₀ → p ≠ q →
      4 * R₀ + 1 ≤ |τ * p / u - τ * q / u| := by
    intro p q u hu huM hpq
    have h1 : |τ * p / u - τ * q / u| = (τ / u) * |(p : ℝ) - (q : ℝ)| := by
      rw [show τ * p / u - τ * q / u = (τ / u) * ((p : ℝ) - (q : ℝ)) by ring, abs_mul,
        abs_of_pos (div_pos hτpos hu)]
    have h2 : (1 : ℝ) ≤ |(p : ℝ) - (q : ℝ)| := by
      have h3 : ((p : ℤ) : ℝ) - ((q : ℤ) : ℝ) = (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) := by push_cast; ring
      have h4 : (p : ℤ) ≠ (q : ℤ) := by exact_mod_cast hpq
      have h5 : 1 ≤ |(p : ℤ) - (q : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr h4)
      have h6 : (1 : ℝ) ≤ |(((p : ℤ) - (q : ℤ) : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast h5
      calc (1 : ℝ) ≤ |(((p : ℤ) - (q : ℤ) : ℤ) : ℝ)| := h6
        _ = |(p : ℝ) - (q : ℝ)| := by rw [← h3]; push_cast; ring_nf
    have h7 : τ₀ / M₀ ≤ τ / u := by
      rw [div_le_div_iff₀ hM₀ hu]
      nlinarith [hτlow, huM, hτ₀, hu]
    rw [h1]
    calc 4 * R₀ + 1 = τ₀ / M₀ := hτ₀M.symm
      _ = (τ₀ / M₀) * 1 := (mul_one _).symm
      _ ≤ (τ / u) * |(p : ℝ) - (q : ℝ)| := by
          apply mul_le_mul h7 h2 (by norm_num) (div_pos hτpos hu).le
  have coord_close : ∀ (p q : ℕ) (u : ℝ), 0 < u → m₀ ≤ u → p ≤ q + 1 → q ≤ p + 1 →
      |τ * p / u - τ * q / u| ≤ 2 * τ₀ / m₀ := by
    intro p q u hu hum hpq hqp
    have h1 : |τ * p / u - τ * q / u| = (τ / u) * |(p : ℝ) - (q : ℝ)| := by
      rw [show τ * p / u - τ * q / u = (τ / u) * ((p : ℝ) - (q : ℝ)) by ring, abs_mul,
        abs_of_pos (div_pos hτpos hu)]
    have h2 : |(p : ℝ) - (q : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor
      · have : (q : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hqp
        linarith
      · have : (p : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hpq
        linarith
    have h3 : τ / u ≤ 2 * τ₀ / m₀ := by
      rw [div_le_div_iff₀ hu hm₀]
      nlinarith [hτhigh, hum, hm₀, hτpos]
    rw [h1]
    calc (τ / u) * |(p : ℝ) - (q : ℝ)| ≤ (τ / u) * 1 := by
          apply mul_le_mul_of_nonneg_left h2 (div_pos hτpos hu).le
      _ = τ / u := mul_one _
      _ ≤ 2 * τ₀ / m₀ := h3

  have hex : ∀ v : ℕ × ℕ × ℕ, v ∈ Tri n →
      ∃ klm : ℕ × ℕ × ℕ,
        (L ≤ klm.1 * α + klm.2.1 * β + klm.2.2 * γ ∧
          klm.1 * α + klm.2.1 * β + klm.2.2 * γ < L + η) ∧
        |(klm.1 : ℝ) - Xc v.1| ≤ R₀ ∧ |(klm.2.1 : ℝ) - Yc v.2.1| ≤ R₀ ∧
        |(klm.2.2 : ℝ) - Zc v.2.2| ≤ R₀ ∧
        (v.1 = 0 → klm.1 = 0) ∧ (v.2.1 = 0 → klm.2.1 = 0) ∧
        (v.2.2 = 0 → klm.2.2 = 0) := by
    intro v hv
    obtain ⟨i, j, r⟩ := v
    obtain ⟨hz1, hz2, hz3⟩ := Tri_at_most_one_zero hv
    simp only at hz1 hz2 hz3
    have hsum : i + j + r = n := Tri_sum hv
    have hX0 : (0 : ℝ) ≤ Xc i := by
      simp only [hXcdef]; positivity
    have hY0 : (0 : ℝ) ≤ Yc j := by
      simp only [hYcdef]; positivity
    have hZ0 : (0 : ℝ) ≤ Zc r := by
      simp only [hZcdef]; positivity
    have hXzero : Xc i = 0 ↔ i = 0 := by
      simp only [hXcdef]
      constructor
      · intro h
        by_contra hi
        have hi1 : 1 ≤ i := by omega
        have := coord_pos i α hα hαM hi1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hYzero : Yc j = 0 ↔ j = 0 := by
      simp only [hYcdef]
      constructor
      · intro h
        by_contra hj
        have hj1 : 1 ≤ j := by omega
        have := coord_pos j β hβ hβM hj1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hZzero : Zc r = 0 ↔ r = 0 := by
      simp only [hZcdef]
      constructor
      · intro h
        by_contra hr
        have hr1 : 1 ≤ r := by omega
        have := coord_pos r γ hγ hγM hr1
        rw [h] at this
        linarith [hR₀1]
      · intro h
        rw [h]
        simp
    have hXalt : Xc i = 0 ∨ 2 * R₀ ≤ Xc i := by
      by_cases hi : i = 0
      · left; exact hXzero.mpr hi
      · right
        have := coord_pos i α hα hαM (by omega)
        linarith [hR₀1]
    have hYalt : Yc j = 0 ∨ 2 * R₀ ≤ Yc j := by
      by_cases hj : j = 0
      · left; exact hYzero.mpr hj
      · right
        have := coord_pos j β hβ hβM (by omega)
        linarith [hR₀1]
    have hZalt : Zc r = 0 ∨ 2 * R₀ ≤ Zc r := by
      by_cases hr : r = 0
      · left; exact hZzero.mpr hr
      · right
        have := coord_pos r γ hγ hγM (by omega)
        linarith [hR₀1]
    have hplane : Xc i * α + Yc j * β + Zc r * γ = L + η / 2 := by
      simp only [hXcdef, hYcdef, hZcdef]
      have h1 : τ * i / α * α + τ * j / β * β + τ * r / γ * γ
          = τ * ((i : ℝ) + (j : ℝ) + (r : ℝ)) := by
        field_simp
      rw [h1]
      have h2 : (i : ℝ) + (j : ℝ) + (r : ℝ) = (n : ℝ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hsum
      rw [h2, hτn]
    have hXYz : ¬(Xc i = 0 ∧ Yc j = 0) := by
      rintro ⟨h1, h2⟩
      exact hz1 ⟨hXzero.mp h1, hYzero.mp h2⟩
    have hXZz : ¬(Xc i = 0 ∧ Zc r = 0) := by
      rintro ⟨h1, h2⟩
      exact hz2 ⟨hXzero.mp h1, hZzero.mp h2⟩
    have hYZz : ¬(Yc j = 0 ∧ Zc r = 0) := by
      rintro ⟨h1, h2⟩
      exact hz3 ⟨hYzero.mp h1, hZzero.mp h2⟩
    obtain ⟨k, l, m, hslab, hk, hl, hm, hkz, hlz, hmz⟩ :=
      hround L (Xc i) (Yc j) (Zc r) hX0 hY0 hZ0 hXYz hXZz hYZz hXalt hYalt hZalt hplane
    exact ⟨(k, l, m), hslab, hk, hl, hm,
      fun h => hkz (hXzero.mpr h), fun h => hlz (hYzero.mpr h), fun h => hmz (hZzero.mpr h)⟩

  set Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ :=
    fun v => if h : v ∈ Tri n then (hex v h).choose else (0, 0, 0) with hΦdef
  have hΦspec : ∀ v (hv : v ∈ Tri n),
      (L ≤ (Φ v).1 * α + (Φ v).2.1 * β + (Φ v).2.2 * γ ∧
        (Φ v).1 * α + (Φ v).2.1 * β + (Φ v).2.2 * γ < L + η) ∧
      |((Φ v).1 : ℝ) - Xc v.1| ≤ R₀ ∧ |((Φ v).2.1 : ℝ) - Yc v.2.1| ≤ R₀ ∧
      |((Φ v).2.2 : ℝ) - Zc v.2.2| ≤ R₀ ∧
      (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
      (v.2.2 = 0 → (Φ v).2.2 = 0) := by
    intro v hv
    simp only [hΦdef, dif_pos hv]
    exact (hex v hv).choose_spec
  refine ⟨n, Φ, ⟨hnlow, hnhigh⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    obtain ⟨⟨hlo, hhi⟩, -⟩ := hΦspec v hv
    have := (mem_GBand_iff_slab ha hb hc hq hp0 hx1 (Φ v).1 (Φ v).2.1 (Φ v).2.2).mpr
      ⟨by rw [← hLdef, ← hαdef, ← hβdef, ← hγdef]; linarith,
        by rw [← hLdef, ← hαdef, ← hβdef, ← hγdef, ← hηdef]; linarith⟩
    exact this
  ·
    intro v hv w hw hwt
    obtain ⟨-, hkv, hlv, hmv, -⟩ := hΦspec v hv
    obtain ⟨-, hkw, hlw, hmw, -⟩ := hΦspec w hw
    obtain ⟨hkk, hll, hmm⟩ := coprime3_pow_inj ha hb hc hco hwt
    by_contra hvw

    obtain ⟨i, j, r⟩ := v
    obtain ⟨i', j', r'⟩ := w
    simp only [Prod.mk.injEq, not_and] at hvw
    have hdiff : i ≠ i' ∨ j ≠ j' ∨ r ≠ r' := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hcon.2.2) (hvw hcon.1 hcon.2.1)
    simp only at hkv hlv hmv hkw hlw hmw hkk hll hmm
    rcases hdiff with h | h | h
    · have hsep := coord_sep i i' α hα hαM h
      have h2 : ((Φ (i, j, r)).1 : ℝ) = ((Φ (i', j', r')).1 : ℝ) := by
        exact_mod_cast hkk
      have e1 : |Xc i - ((Φ (i, j, r)).1 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hkv
      have e2 : |((Φ (i, j, r)).1 : ℝ) - Xc i'| ≤ R₀ := by
        rw [h2]
        exact hkw
      have h1 : |Xc i - Xc i'| ≤ 2 * R₀ := by
        calc |Xc i - Xc i'|
            ≤ |Xc i - ((Φ (i, j, r)).1 : ℝ)| + |((Φ (i, j, r)).1 : ℝ) - Xc i'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hXcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
    · have hsep := coord_sep j j' β hβ hβM h
      have h2 : ((Φ (i, j, r)).2.1 : ℝ) = ((Φ (i', j', r')).2.1 : ℝ) := by
        exact_mod_cast hll
      have e1 : |Yc j - ((Φ (i, j, r)).2.1 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hlv
      have e2 : |((Φ (i, j, r)).2.1 : ℝ) - Yc j'| ≤ R₀ := by
        rw [h2]
        exact hlw
      have h1 : |Yc j - Yc j'| ≤ 2 * R₀ := by
        calc |Yc j - Yc j'|
            ≤ |Yc j - ((Φ (i, j, r)).2.1 : ℝ)| + |((Φ (i, j, r)).2.1 : ℝ) - Yc j'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hYcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
    · have hsep := coord_sep r r' γ hγ hγM h
      have h2 : ((Φ (i, j, r)).2.2 : ℝ) = ((Φ (i', j', r')).2.2 : ℝ) := by
        exact_mod_cast hmm
      have e1 : |Zc r - ((Φ (i, j, r)).2.2 : ℝ)| ≤ R₀ := by
        rw [abs_sub_comm]
        exact hmv
      have e2 : |((Φ (i, j, r)).2.2 : ℝ) - Zc r'| ≤ R₀ := by
        rw [h2]
        exact hmw
      have h1 : |Zc r - Zc r'| ≤ 2 * R₀ := by
        calc |Zc r - Zc r'|
            ≤ |Zc r - ((Φ (i, j, r)).2.2 : ℝ)| + |((Φ (i, j, r)).2.2 : ℝ) - Zc r'| :=
              abs_sub_le _ _ _
          _ ≤ R₀ + R₀ := add_le_add e1 e2
          _ = 2 * R₀ := by ring
      simp only [hZcdef] at h1 hsep
      linarith [hsep, h1, hR₀1]
  ·
    intro v hv
    obtain ⟨-, -, -, -, h1, h2, h3⟩ := hΦspec v hv
    exact ⟨h1, h2, h3⟩
  ·
    intro v hv w hw hclose
    obtain ⟨-, hkv, hlv, hmv, -⟩ := hΦspec v hv
    obtain ⟨-, hkw, hlw, hmw, -⟩ := hΦspec w hw
    obtain ⟨h11, h12, h21, h22, h31, h32⟩ := hclose
    have hboundk : |((Φ v).1 : ℝ) - ((Φ w).1 : ℝ)| ≤ Dr := by
      have hc := coord_close v.1 w.1 α hα hmα h11 h12
      calc |((Φ v).1 : ℝ) - ((Φ w).1 : ℝ)|
          ≤ |((Φ v).1 : ℝ) - Xc v.1| + |Xc v.1 - ((Φ w).1 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Xc v.1 - Xc w.1| + |Xc w.1 - ((Φ w).1 : ℝ)|) := by
            apply add_le_add hkv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hXcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have hboundl : |((Φ v).2.1 : ℝ) - ((Φ w).2.1 : ℝ)| ≤ Dr := by
      have hc := coord_close v.2.1 w.2.1 β hβ hmβ h21 h22
      calc |((Φ v).2.1 : ℝ) - ((Φ w).2.1 : ℝ)|
          ≤ |((Φ v).2.1 : ℝ) - Yc v.2.1| + |Yc v.2.1 - ((Φ w).2.1 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Yc v.2.1 - Yc w.2.1| + |Yc w.2.1 - ((Φ w).2.1 : ℝ)|) := by
            apply add_le_add hlv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hYcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have hboundm : |((Φ v).2.2 : ℝ) - ((Φ w).2.2 : ℝ)| ≤ Dr := by
      have hc := coord_close v.2.2 w.2.2 γ hγ hmγ h31 h32
      calc |((Φ v).2.2 : ℝ) - ((Φ w).2.2 : ℝ)|
          ≤ |((Φ v).2.2 : ℝ) - Zc v.2.2| + |Zc v.2.2 - ((Φ w).2.2 : ℝ)| := abs_sub_le _ _ _
        _ ≤ R₀ + (|Zc v.2.2 - Zc w.2.2| + |Zc w.2.2 - ((Φ w).2.2 : ℝ)|) := by
            apply add_le_add hmv (abs_sub_le _ _ _)
        _ ≤ R₀ + (2 * τ₀ / m₀ + R₀) := by
            apply add_le_add le_rfl
            apply add_le_add
            · simpa [hZcdef] using hc
            · rwa [abs_sub_comm]
        _ = Dr := by rw [hDrdef]; ring
    have conv : ∀ p q : ℕ, |(p : ℝ) - (q : ℝ)| ≤ Dr → p ≤ q + D ∧ q ≤ p + D := by
      intro p q hpq
      have h1 := abs_le.mp hpq
      constructor
      · have h2 : (p : ℝ) ≤ (q : ℝ) + (D : ℝ) := by linarith [h1.2, hDrD]
        exact_mod_cast h2
      · have h2 : (q : ℝ) ≤ (p : ℝ) + (D : ℝ) := by linarith [h1.1, hDrD]
        exact_mod_cast h2
    obtain ⟨e1, e2⟩ := conv _ _ hboundk
    obtain ⟨e3, e4⟩ := conv _ _ hboundl
    obtain ⟨e5, e6⟩ := conv _ _ hboundm
    exact ⟨e1, e2, e3, e4, e5, e6⟩

end GGridEmbedding

set_option maxHeartbeats 1000000 in
theorem gband_card_ge_sq (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      c₁ * Real.log x ^ 2 ≤ ((GBand a b c p q x).card : ℝ) := by
  classical
  obtain ⟨c₀, C₀, D, hc₀, hC₀, hD1, X₀g, hX₀g2, hgrid⟩ :=
    ggrid_embedding (a := a) (b := b) (c := c) (p := p) (q := q)
      (by omega) (by omega) (by omega) hco hq hqp hpd
  refine ⟨c₀ ^ 2 / 36, div_pos (pow_pos hc₀ 2) (by norm_num),
    max X₀g ⌈Real.exp (96 / c₀)⌉₊, fun x hx => ?_⟩
  have hxg : X₀g ≤ x := le_trans (le_max_left _ _) hx
  have hlog96 : 96 / c₀ ≤ Real.log x := by
    have h1 : Real.exp (96 / c₀) ≤ (x : ℝ) := by
      calc Real.exp (96 / c₀) ≤ (⌈Real.exp (96 / c₀)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hx
    calc 96 / c₀ = Real.log (Real.exp (96 / c₀)) := (Real.log_exp _).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) h1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (div_pos (by norm_num) hc₀) hlog96
  have h96 : (96 : ℝ) ≤ c₀ * Real.log x := by
    have h2 := (div_le_iff₀ hc₀).mp hlog96
    linarith [h2]
  obtain ⟨n, Φ, ⟨hnlo, -⟩, hband, hinj, -, -⟩ := hgrid x hxg
  have hn96R : (96 : ℝ) ≤ (n : ℝ) := le_trans h96 hnlo
  have hn96 : 96 ≤ n := by exact_mod_cast hn96R

  have hmemTri : ∀ i j : ℕ, 1 ≤ i → i ≤ n / 5 → 1 ≤ j → j ≤ n / 5 →
      (i, j, n - i - j) ∈ Tri n := by
    intro i j hi1 him hj1 hjm
    have h5 : 5 * (n / 5) ≤ n := by omega
    have hAnd : i + j + (n - i - j) = n ∧ (i, j, n - i - j) ≠ (n, 0, 0) ∧
        (i, j, n - i - j) ≠ (0, n, 0) ∧ (i, j, n - i - j) ≠ (0, 0, n) := by
      refine ⟨by omega, fun hcon => ?_, fun hcon => ?_, fun hcon => ?_⟩ <;>
        (simp only [Prod.mk.injEq] at hcon; omega)
    exact hAnd
  set F : Finset (ℕ × ℕ) := Finset.Icc 1 (n / 5) ×ˢ Finset.Icc 1 (n / 5) with hFdef
  set g : ℕ × ℕ → ℕ := fun ij => wt a b c (Φ (ij.1, ij.2, n - ij.1 - ij.2)) with hgdef
  have hmaps : ∀ ij ∈ F, g ij ∈ GBand a b c p q x := by
    intro ij hij
    simp only [hFdef, Finset.mem_product, Finset.mem_Icc] at hij
    simp only [hgdef]
    exact hband _ (hmemTri ij.1 ij.2 hij.1.1 hij.1.2 hij.2.1 hij.2.2)
  have hinjF : Set.InjOn g (F : Set (ℕ × ℕ)) := by
    intro ij hij ij' hij' hgg
    have hij2 : ij ∈ F := Finset.mem_coe.mp hij
    have hij2' : ij' ∈ F := Finset.mem_coe.mp hij'
    simp only [hFdef, Finset.mem_product, Finset.mem_Icc] at hij2 hij2'
    simp only [hgdef] at hgg
    have h1 := hinj _ (hmemTri ij.1 ij.2 hij2.1.1 hij2.1.2 hij2.2.1 hij2.2.2)
      _ (hmemTri ij'.1 ij'.2 hij2'.1.1 hij2'.1.2 hij2'.2.1 hij2'.2.2) hgg
    have hfst : ij.1 = ij'.1 := congrArg (fun t : ℕ × ℕ × ℕ => t.1) h1
    have hsnd : ij.2 = ij'.2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h1
    calc ij = (ij.1, ij.2) := rfl
      _ = (ij'.1, ij'.2) := by rw [hfst, hsnd]
      _ = ij' := rfl
  have hcard : F.card ≤ (GBand a b c p q x).card :=
    Finset.card_le_card_of_injOn g hmaps hinjF
  have hFcard : F.card = (n / 5) * (n / 5) := by
    simp only [hFdef, Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
  have hcards : (n / 5) * (n / 5) ≤ (GBand a b c p q x).card := by
    rw [← hFcard]
    exact hcard

  have hmR : ((n : ℝ) - 4) / 5 ≤ ((n / 5 : ℕ) : ℝ) := by
    have h1 : n ≤ 5 * (n / 5) + 4 := by omega
    have h2 : (n : ℝ) ≤ 5 * ((n / 5 : ℕ) : ℝ) + 4 := by exact_mod_cast h1
    linarith
  have hn6 : (n : ℝ) / 6 ≤ ((n : ℝ) - 4) / 5 := by linarith [hn96R]
  have hm6 : (n : ℝ) / 6 ≤ ((n / 5 : ℕ) : ℝ) := le_trans hn6 hmR
  have hmsq : ((n : ℝ) / 6) * ((n : ℝ) / 6) ≤ ((n / 5 : ℕ) : ℝ) * ((n / 5 : ℕ) : ℝ) :=
    mul_le_mul hm6 hm6 (by positivity) (Nat.cast_nonneg _)
  have hsq : (c₀ * Real.log x) * (c₀ * Real.log x) ≤ (n : ℝ) * (n : ℝ) :=
    mul_le_mul hnlo hnlo (mul_nonneg hc₀.le hL0.le) (Nat.cast_nonneg _)
  calc c₀ ^ 2 / 36 * Real.log x ^ 2
      = (c₀ * Real.log x) * (c₀ * Real.log x) / 36 := by ring
    _ ≤ (n : ℝ) * (n : ℝ) / 36 := by linarith
    _ = ((n : ℝ) / 6) * ((n : ℝ) / 6) := by ring
    _ ≤ ((n / 5 : ℕ) : ℝ) * ((n / 5 : ℕ) : ℝ) := hmsq
    _ ≤ ((GBand a b c p q x).card : ℝ) := by exact_mod_cast hcards

end Erdos123Band
end Module_GGrid

section Module_GRigidity

namespace Erdos123Band

set_option maxHeartbeats 1000000 in
lemma gbadF_card_le (a b c p q x n : ℕ) (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (t δ : ℝ)
    (hδ : 0 < δ)
    (hband : ∀ v ∈ Tri n, wt a b c (Φ v) ∈ GBand a b c p q x)
    (hinj : ∀ v ∈ Tri n, ∀ w ∈ Tri n, wt a b c (Φ v) = wt a b c (Φ w) → v = w) :
    (((TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|)).card : ℝ) * δ ^ 2
      ≤ GQenergy a b c p q x t := by
  classical
  set F : Finset (ℕ × ℕ × ℕ) := (TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) with hFdef
  have hFT : ∀ v ∈ F, v ∈ Tri n := fun v hv => mem_TriF.mp (Finset.mem_filter.mp hv).1
  have hFbad : ∀ v ∈ F, δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| :=
    fun v hv => (Finset.mem_filter.mp hv).2
  set G : Finset ℕ := F.image (fun v => wt a b c (Φ v)) with hGdef
  have hGcard : G.card = F.card := by
    rw [hGdef]
    apply Finset.card_image_of_injOn
    intro v hv w hw hvw
    exact hinj v (hFT v hv) w (hFT w hw) hvw
  have hGsub : G ⊆ GBand a b c p q x := by
    intro s hs
    rw [hGdef] at hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    exact hband v (hFT v hv)
  have hGterm : ∀ s ∈ G, δ ^ 2 ≤ ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := by
    intro s hs
    rw [hGdef] at hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    have h1 := hFbad v hv
    calc δ ^ 2
        ≤ |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| ^ 2 :=
          pow_le_pow_left₀ hδ.le h1.le 2
      _ = ((wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)) ^ 2 := sq_abs _
  have h1 : (G.card : ℝ) * δ ^ 2 ≤ ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := by
    have h := Finset.card_nsmul_le_sum G
      (fun s => ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2) (δ ^ 2) hGterm
    rwa [nsmul_eq_mul] at h
  have h2 : ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 ≤ GQenergy a b c p q x t := by
    unfold GQenergy
    exact Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun s _ _ => sq_nonneg _)
  calc (F.card : ℝ) * δ ^ 2
      = (G.card : ℝ) * δ ^ 2 := by rw [hGcard]
    _ ≤ ∑ s ∈ G, ((s : ℝ) * t - round ((s : ℝ) * t)) ^ 2 := h1
    _ ≤ GQenergy a b c p q x t := h2

set_option maxHeartbeats 1000000 in
theorem gvery_low (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ κ₀ δ : ℝ, ∃ X₅ : ℕ, 0 < κ₀ ∧ 0 < δ ∧ δ ≤ 1 / 32 ∧ ∀ x : ℕ, X₅ ≤ x → ∀ t : ℝ,
      GQenergy a b c p q x t < κ₀ * Real.log x → ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ) := by
  classical
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  obtain ⟨c₀, C₀, D, hc₀, -, hD1, X₀g, -, hgrid⟩ :=
    ggrid_embedding (a := a) (b := b) (c := c) (p := p) (q := q)
      (by omega) (by omega) (by omega) hco hq hqp hpd

  set K : ℕ := (a * b * c) ^ D with hKdef
  have habc8 : 8 ≤ a * b * c := by
    calc 8 = 2 * 2 * 2 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hK8 : 8 ≤ K := by
    rw [hKdef]
    calc 8 ≤ a * b * c := habc8
      _ = (a * b * c) ^ 1 := (pow_one _).symm
      _ ≤ (a * b * c) ^ D := Nat.pow_le_pow_right (le_trans (by norm_num) habc8) hD1
  have hKR : (8 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK8
  have hK0R : (0 : ℝ) < (K : ℝ) := by linarith
  have h4K0 : (0 : ℝ) < 4 * (K : ℝ) := by linarith
  set δ : ℝ := 1 / (4 * (K : ℝ)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos h4K0
  have hδ32 : δ ≤ 1 / 32 := by
    rw [hδdef, div_le_div_iff₀ h4K0 (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hKδeq : (K : ℝ) * δ = 1 / 4 := by
    rw [hδdef, mul_one_div, div_eq_div_iff h4K0.ne' (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  have hKδ : (K : ℝ) * δ ≤ 1 / 4 := le_of_eq hKδeq
  set κ₀ : ℝ := c₀ * δ ^ 2 / 9 with hκdef
  have hκpos : 0 < κ₀ := by
    rw [hκdef]
    exact div_pos (mul_pos hc₀ (pow_pos hδpos 2)) (by norm_num)
  refine ⟨κ₀, δ, max X₀g (max 3 ⌈Real.exp (96 / c₀)⌉₊), hκpos, hδpos, hδ32,
    fun x hx t hcon => ?_⟩

  have hxX₀g : X₀g ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_left 3 _) (le_max_right X₀g _)) hx
  have hx0 : 0 < x := by omega
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hxceil : ⌈Real.exp (96 / c₀)⌉₊ ≤ x :=
    le_trans (le_trans (le_max_right 3 _) (le_max_right X₀g _)) hx
  have hxceilR : Real.exp (96 / c₀) ≤ (x : ℝ) := by
    calc Real.exp (96 / c₀) ≤ (⌈Real.exp (96 / c₀)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := by exact_mod_cast hxceil
  have hL96 : 96 / c₀ ≤ Real.log x := by
    calc 96 / c₀ = Real.log (Real.exp (96 / c₀)) := (Real.log_exp _).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxceilR
  have h96 : (96 : ℝ) ≤ c₀ * Real.log x := by
    have h1 := (div_le_iff₀ hc₀).mp hL96
    linarith

  obtain ⟨n, Φ, ⟨hnlo, -⟩, hband, hinj, hface, hjump⟩ := hgrid x hxX₀g
  have hn96R : (96 : ℝ) ≤ (n : ℝ) := le_trans h96 hnlo
  have hn96 : 96 ≤ n := by exact_mod_cast hn96R
  have hn48 : 48 ≤ n := by omega

  have hQb := gbadF_card_le a b c p q x n Φ t δ hδpos hband hinj
  set H : ℕ := ((TriF n).filter (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|)).card with hHdef
  rw [hκdef] at hcon
  have hδsq : (0 : ℝ) < δ ^ 2 := pow_pos hδpos 2
  have hH9R : (H : ℝ) * 9 < (n : ℝ) := by
    have h1 : (H : ℝ) * δ ^ 2 < c₀ * δ ^ 2 / 9 * Real.log x := lt_of_le_of_lt hQb hcon
    have h2 : ((H : ℝ) * 9) * δ ^ 2 < (c₀ * Real.log x) * δ ^ 2 := by nlinarith [h1]
    have h3 : (H : ℝ) * 9 < c₀ * Real.log x := lt_of_mul_lt_mul_right h2 hδsq.le
    linarith [hnlo]
  have hH9 : 9 * H < n := by
    have h3 : ((9 * H : ℕ) : ℝ) < (n : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hH8 : 8 * H < n := by omega

  have hHbound : ∀ F : Finset (ℕ × ℕ × ℕ),
      (∀ v ∈ F, v ∈ Tri n ∧ δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) → F.card ≤ H := by
    intro F hF
    rw [hHdef]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvT, hvB⟩ := hF v hv
    exact Finset.mem_filter.mpr ⟨mem_TriF.mpr hvT, hvB⟩
  obtain ⟨q', hq', j, hj, hrow4, hpath7⟩ :=
    exists_sparse_row_and_path hn48
      (fun v => δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)|)
      H hHbound
  have hjq : j ≤ q' := by
    have h := (midJ_bounds hj).2
    omega

  have hrow0 : (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) n q').card = 0 := by
    by_contra hne
    have h1 : 1 ≤ (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q').card := Nat.pos_of_ne_zero hne
    have h2 : n ≤ 4 * H := by
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
            - round ((wt a b c (Φ v) : ℝ) * t)|) n q').card := Nat.mul_le_mul_left n h1
        _ ≤ 4 * H := hrow4
    omega
  have hpath0 : (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
      - round ((wt a b c (Φ v) : ℝ) * t)|) n q' j).card = 0 := by
    by_contra hne
    have h1 : 1 ≤ (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q' j).card := Nat.pos_of_ne_zero hne
    have h2 : n ≤ 7 * H := by
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
            - round ((wt a b c (Φ v) : ℝ) * t)|) n q' j).card := Nat.mul_le_mul_left n h1
        _ ≤ 7 * H := hpath7
    omega

  have hrowGood : ∀ i, i ≤ q' →
      |(wt a b c (Φ (rowV n q' i)) : ℝ) * t
        - round ((wt a b c (Φ (rowV n q' i)) : ℝ) * t)| ≤ δ := by
    intro i hi
    by_contra hbad
    push_neg at hbad
    have hmem : i ∈ rowBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q' := by
      simp only [rowBad, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hbad⟩
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  have hpathGood : ∀ s, s ≤ n - q' →
      |(wt a b c (Φ (pathV n q' j s)) : ℝ) * t
        - round ((wt a b c (Φ (pathV n q' j s)) : ℝ) * t)| ≤ δ := by
    intro s hs
    by_contra hbad
    push_neg at hbad
    have hmem : s ∈ pathBad (fun v => δ < |(wt a b c (Φ v) : ℝ) * t
        - round ((wt a b c (Φ v) : ℝ) * t)|) n q' j := by
      simp only [pathBad, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hbad⟩
    have hpos := Finset.card_pos.mpr ⟨s, hmem⟩
    omega

  have hrS_ge : ∀ i, i ≤ q' → x ≤ wt a b c (Φ (rowV n q' i)) := fun i hi =>
    (of_mem_GBand (hband _ (rowV_mem_Tri hn48 hq' hi))).2.1
  have hrs : ∀ i, i ≤ q' → 0 < wt a b c (Φ (rowV n q' i)) := fun i hi =>
    lt_of_lt_of_le hx0 (hrS_ge i hi)
  have hpS_ge : ∀ s, s ≤ n - q' → x ≤ wt a b c (Φ (pathV n q' j s)) := fun s hs =>
    (of_mem_GBand (hband _ (pathV_mem_Tri hn48 hq' hj hs))).2.1
  have hps : ∀ s, s ≤ n - q' → 0 < wt a b c (Φ (pathV n q' j s)) := fun s hs =>
    lt_of_lt_of_le hx0 (hpS_ge s hs)

  have hrB : ∀ i, i < q' → 0 < edgeA a b c (Φ (rowV n q' (i + 1))) (Φ (rowV n q' i)) :=
    fun i _ => edgeA_pos (by omega) (by omega) (by omega) _ _
  have hpB : ∀ s, s < n - q' →
      0 < edgeA a b c (Φ (pathV n q' j (s + 1))) (Φ (pathV n q' j s)) :=
    fun s _ => edgeA_pos (by omega) (by omega) (by omega) _ _
  have hrrel : ∀ i, i < q' →
      edgeA a b c (Φ (rowV n q' i)) (Φ (rowV n q' (i + 1))) * wt a b c (Φ (rowV n q' i))
        = edgeA a b c (Φ (rowV n q' (i + 1))) (Φ (rowV n q' i))
          * wt a b c (Φ (rowV n q' (i + 1))) :=
    fun i _ => edgeA_mul_wt a b c (Φ (rowV n q' i)) (Φ (rowV n q' (i + 1)))
  have hprel : ∀ s, s < n - q' →
      edgeA a b c (Φ (pathV n q' j s)) (Φ (pathV n q' j (s + 1)))
          * wt a b c (Φ (pathV n q' j s))
        = edgeA a b c (Φ (pathV n q' j (s + 1))) (Φ (pathV n q' j s))
          * wt a b c (Φ (pathV n q' j (s + 1))) :=
    fun s _ => edgeA_mul_wt a b c (Φ (pathV n q' j s)) (Φ (pathV n q' j (s + 1)))

  have hrd : ∀ i, i < q' →
      (edgeA a b c (Φ (rowV n q' (i + 1))) (Φ (rowV n q' i)) : ℤ)
          * round ((wt a b c (Φ (rowV n q' (i + 1))) : ℝ) * t)
        = (edgeA a b c (Φ (rowV n q' i)) (Φ (rowV n q' (i + 1))) : ℤ)
          * round ((wt a b c (Φ (rowV n q' i)) : ℝ) * t) := by
    intro i hi
    have hm1 : rowV n q' i ∈ Tri n := rowV_mem_Tri hn48 hq' (by omega)
    have hm2 : rowV n q' (i + 1) ∈ Tri n := rowV_mem_Tri hn48 hq' (by omega)
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjump _ hm1 _ hm2 (rowV_adjacent (by omega))
    exact edge_defect_zero hδpos hKδ
      (edgeA_mul_wt a b c (Φ (rowV n q' i)) (Φ (rowV n q' (i + 1))))
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j2 j4 j6)
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j1 j3 j5)
      (hrowGood i (by omega)) (hrowGood (i + 1) (by omega))
  have hpd' : ∀ s, s < n - q' →
      (edgeA a b c (Φ (pathV n q' j (s + 1))) (Φ (pathV n q' j s)) : ℤ)
          * round ((wt a b c (Φ (pathV n q' j (s + 1))) : ℝ) * t)
        = (edgeA a b c (Φ (pathV n q' j s)) (Φ (pathV n q' j (s + 1))) : ℤ)
          * round ((wt a b c (Φ (pathV n q' j s)) : ℝ) * t) := by
    intro s hs
    have hm1 : pathV n q' j s ∈ Tri n := pathV_mem_Tri hn48 hq' hj (by omega)
    have hm2 : pathV n q' j (s + 1) ∈ Tri n := pathV_mem_Tri hn48 hq' hj (by omega)
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hjump _ hm1 _ hm2 (pathV_adjacent hjq (by omega))
    exact edge_defect_zero hδpos hKδ
      (edgeA_mul_wt a b c (Φ (pathV n q' j s)) (Φ (pathV n q' j (s + 1))))
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j2 j4 j6)
      (by rw [hKdef]; exact edgeA_le ha1 hb1 hc1 j1 j3 j5)
      (hpathGood s (by omega)) (hpathGood (s + 1) (by omega))

  have hjunc_s : wt a b c (Φ (pathV n q' j 0)) = wt a b c (Φ (rowV n q' (q' - j))) := by
    rw [pathV_zero hjq]
  have hjunc_d : round ((wt a b c (Φ (pathV n q' j 0)) : ℝ) * t)
      = round ((wt a b c (Φ (rowV n q' (q' - j))) : ℝ) * t) := by
    rw [hjunc_s]

  have hmem0 : rowV n q' 0 ∈ Tri n := rowV_mem_Tri hn48 hq' (Nat.zero_le q')
  have hmemq : rowV n q' q' ∈ Tri n := rowV_mem_Tri hn48 hq' (le_refl q')
  have hmemP : pathV n q' j (n - q') ∈ Tri n := pathV_mem_Tri hn48 hq' hj (le_refl (n - q'))
  have hk0 : (Φ (rowV n q' 0)).1 = 0 := (hface _ hmem0).1 (by simp [rowV])
  have hl0 : (Φ (rowV n q' q')).2.1 = 0 := (hface _ hmemq).2.1 (by simp [rowV])
  have hm0 : (Φ (pathV n q' j (n - q'))).2.2 = 0 := (hface _ hmemP).2.2 (by simp [pathV])
  have hw0 : wt a b c (Φ (rowV n q' 0))
      = b ^ (Φ (rowV n q' 0)).2.1 * c ^ (Φ (rowV n q' 0)).2.2 := by
    rw [wt, hk0, pow_zero, one_mul]
  have hwq : wt a b c (Φ (rowV n q' q'))
      = a ^ (Φ (rowV n q' q')).1 * c ^ (Φ (rowV n q' q')).2.2 := by
    rw [wt, hl0, pow_zero, mul_one]
  have hwP : wt a b c (Φ (pathV n q' j (n - q')))
      = a ^ (Φ (pathV n q' j (n - q'))).1 * b ^ (Φ (pathV n q' j (n - q'))).2.1 := by
    rw [wt, hm0, pow_zero, mul_one]
  have hgcd : Nat.gcd (Nat.gcd (wt a b c (Φ (rowV n q' 0))) (wt a b c (Φ (rowV n q' q'))))
      (wt a b c (Φ (pathV n q' j (n - q')))) = 1 := by
    rw [hw0, hwq, hwP]
    exact corner_gcd_eq_one hco _ _ _ _ _ _

  have hdvd : (wt a b c (Φ (rowV n q' 0)) : ℤ)
      ∣ round ((wt a b c (Φ (rowV n q' 0)) : ℝ) * t) :=
    chain_dvd (q := q') (P := n - q')
      (fun i => wt a b c (Φ (rowV n q' i)))
      (fun s => wt a b c (Φ (pathV n q' j s)))
      (fun i => round ((wt a b c (Φ (rowV n q' i)) : ℝ) * t))
      (fun s => round ((wt a b c (Φ (pathV n q' j s)) : ℝ) * t))
      (fun i => edgeA a b c (Φ (rowV n q' i)) (Φ (rowV n q' (i + 1))))
      (fun i => edgeA a b c (Φ (rowV n q' (i + 1))) (Φ (rowV n q' i)))
      (fun s => edgeA a b c (Φ (pathV n q' j s)) (Φ (pathV n q' j (s + 1))))
      (fun s => edgeA a b c (Φ (pathV n q' j (s + 1))) (Φ (pathV n q' j s)))
      hrs hps hrB hpB hrrel hprel hrd hpd'
      (q' - j) (Nat.sub_le q' j) hjunc_s hjunc_d hgcd
  obtain ⟨r, hr⟩ := hdvd

  have hgood0 : |(wt a b c (Φ (rowV n q' 0)) : ℝ) * t
      - round ((wt a b c (Φ (rowV n q' 0)) : ℝ) * t)| ≤ δ := hrowGood 0 (Nat.zero_le q')
  have hSxN : x ≤ wt a b c (Φ (rowV n q' 0)) := hrS_ge 0 (Nat.zero_le q')
  have hSx : (x : ℝ) ≤ (wt a b c (Φ (rowV n q' 0)) : ℝ) := by exact_mod_cast hSxN
  have hS₀pos : (0 : ℝ) < (wt a b c (Φ (rowV n q' 0)) : ℝ) := lt_of_lt_of_le hxR hSx
  refine ⟨r, ?_⟩
  have hfac : (wt a b c (Φ (rowV n q' 0)) : ℝ) * t
      - ((round ((wt a b c (Φ (rowV n q' 0)) : ℝ) * t) : ℤ) : ℝ)
      = (wt a b c (Φ (rowV n q' 0)) : ℝ) * (t - (r : ℝ)) := by
    rw [hr]; push_cast; ring
  have h1 : (wt a b c (Φ (rowV n q' 0)) : ℝ) * |t - (r : ℝ)| ≤ δ := by
    calc (wt a b c (Φ (rowV n q' 0)) : ℝ) * |t - (r : ℝ)|
        = |(wt a b c (Φ (rowV n q' 0)) : ℝ) * (t - (r : ℝ))| := by
          rw [abs_mul, abs_of_pos hS₀pos]
      _ = |(wt a b c (Φ (rowV n q' 0)) : ℝ) * t
            - ((round ((wt a b c (Φ (rowV n q' 0)) : ℝ) * t) : ℤ) : ℝ)| := by rw [hfac]
      _ ≤ δ := hgood0
  rw [le_div_iff₀ hxR]
  calc |t - (r : ℝ)| * (x : ℝ)
      ≤ |t - (r : ℝ)| * (wt a b c (Φ (rowV n q' 0)) : ℝ) :=
        mul_le_mul_of_nonneg_left hSx (abs_nonneg _)
    _ = (wt a b c (Φ (rowV n q' 0)) : ℝ) * |t - (r : ℝ)| := mul_comm _ _
    _ ≤ δ := h1

end Erdos123Band

end Module_GRigidity

section Module_GBandAux

namespace Erdos123Band

open Real MeasureTheory

set_option maxHeartbeats 1000000 in
theorem gS4_le {a b c p q : ℕ} (hq : 0 < q) (x : ℕ) :
    (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4) ≤ ((p : ℝ) * (x : ℝ)) ^ 2 * (GS2 a b c p q x : ℝ) := by
  have hGS2 : (GS2 a b c p q x : ℝ) = ∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 2 := by
    rw [GS2, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun s _ => by push_cast; ring)
  rw [hGS2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsle : (s : ℝ) ≤ (p : ℝ) * (x : ℝ) := by
    have := gband_le hq hs
    have : ((s : ℕ) : ℝ) ≤ ((p * x : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hsq : (s : ℝ) ^ 2 ≤ ((p : ℝ) * (x : ℝ)) ^ 2 := by nlinarith
  calc (s : ℝ) ^ 4 = (s : ℝ) ^ 2 * (s : ℝ) ^ 2 := by ring
    _ ≤ ((p : ℝ) * (x : ℝ)) ^ 2 * (s : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

set_option maxHeartbeats 1000000 in
theorem gsum_sq_band (a b c p q x : ℕ) (t : ℝ) :
    (∑ s ∈ GBand a b c p q x, ((s : ℝ) * t) ^ 2) = (GS2 a b c p q x : ℝ) * t ^ 2 := by
  rw [GS2, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun s _ => by push_cast; ring)

set_option maxHeartbeats 1000000 in
lemma gintegrand_reflect (a b c p q x n : ℕ) (u : ℝ) :
    (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * (1 - u)))) * e (-((n : ℝ) * (1 - u)))
      = (starRingEnd ℂ)
          ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * u))) * e (-((n : ℝ) * u))) := by
  rw [map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [map_add, map_one, e_conj]
    congr 1
    rw [show (s : ℝ) * (1 - u) = ((s : ℤ) : ℝ) + -((s : ℝ) * u) by push_cast; ring,
      e_add, e_int, one_mul]
  · rw [e_conj]
    rw [show -((n : ℝ) * (1 - u)) = ((-(n : ℤ) : ℤ) : ℝ) + (n : ℝ) * u by push_cast; ring,
      e_add, e_int, one_mul, neg_neg]

set_option maxHeartbeats 1000000 in
theorem gintegrand_re_reflect (a b c p q x n : ℕ) (u : ℝ) :
    (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * (1 - u))))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * (1 - u)))
      = (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * u)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * u)) := by
  have hkey : ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * (1 - u))))
        * e (-((n : ℝ) * (1 - u)))).re
      = ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * u))) * e (-((n : ℝ) * u))).re := by
    rw [gintegrand_reflect, Complex.conj_re]
  rw [gintegrand_re a b c p q x n (1 - u), gintegrand_re a b c p q x n u] at hkey
  have hpow : (0 : ℝ) < 2 ^ (GBand a b c p q x).card := by positivity
  rw [mul_assoc, mul_assoc] at hkey
  exact mul_left_cancel₀ (ne_of_gt hpow) hkey

set_option maxHeartbeats 1000000 in
lemma gfold_half (F : ℝ → ℝ) (hcont : Continuous F) (hsymm : ∀ u : ℝ, F (1 - u) = F u) :
    (∫ t in (0:ℝ)..1, F t) = 2 * ∫ t in (0:ℝ)..(1/2), F t := by
  have hsplit : (∫ t in (0:ℝ)..1, F t)
      = (∫ t in (0:ℝ)..(1/2), F t) + ∫ t in (1/2:ℝ)..1, F t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 (1/2)) (hcont.intervalIntegrable (1/2) 1)).symm
  have hmirror : (∫ t in (1/2:ℝ)..1, F t) = ∫ t in (0:ℝ)..(1/2), F t := by
    have hsub : (∫ t in (0:ℝ)..(1/2 : ℝ), F (1 - t))
        = ∫ t in (1 - 1/2 : ℝ)..(1 - 0 : ℝ), F t :=
      intervalIntegral.integral_comp_sub_left F 1
    rw [show (1 - 1/2 : ℝ) = 1/2 by norm_num, sub_zero] at hsub
    rw [← hsub]
    exact intervalIntegral.integral_congr (fun u _ => hsymm u)
  rw [hsplit, hmirror]; ring

set_option maxHeartbeats 1000000 in
theorem gsplit_half (a b c p q x n : ℕ) :
    (∫ t in (0:ℝ)..1, (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
      = 2 * ∫ t in (0:ℝ)..(1/2),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) :=
  gfold_half
    (fun t => (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
      * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
    (by fun_prop)
    (gintegrand_re_reflect a b c p q x n)

set_option maxHeartbeats 1000000 in
lemma gnatLog2_le_real (m : ℕ) (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
    have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    calc (2 : ℝ) ^ Nat.log 2 m = ((2 ^ Nat.log 2 m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (m : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 m) ≤ Real.log m :=
    Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  linarith

set_option maxHeartbeats 1000000 in
theorem gV_upper (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ CV : ℝ, 0 < CV ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      Real.sqrt (GS2 a b c p q x) ≤ CV * (x : ℝ) * Real.log x := by
  have hp : 0 < p := lt_trans hq hqp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpc : p < q * c :=
    lt_of_lt_of_le hpd (Nat.mul_le_mul_left q (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨4 * (p : ℝ), by linarith, max 3 (2 * p), fun x hx => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hx2p : 2 * p ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log hx3
  have h2p : (0 : ℝ) < ((2 * p : ℕ) : ℝ) := by
    have h : 0 < 2 * p := by omega
    exact_mod_cast h
  have hm1 : 1 ≤ 2 * p * x := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hKR0 : (0 : ℝ) ≤ ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hKle : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ)
      ≤ Real.log ((2 * p * x : ℕ) : ℝ) / Real.log 2 :=
    gnatLog2_le_real (2 * p * x) hm1
  have hsplit : Real.log ((2 * p * x : ℕ) : ℝ)
      = Real.log ((2 * p : ℕ) : ℝ) + Real.log x := by
    rw [show ((2 * p * x : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) * (x : ℝ) by push_cast; ring,
      Real.log_mul h2p.ne' hxpos.ne']
  have hlog2p : Real.log ((2 * p : ℕ) : ℝ) ≤ Real.log x :=
    Real.log_le_log h2p (by exact_mod_cast hx2p)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hKmul : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log x := by
    have h := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hKle
    rw [hsplit] at h
    linarith
  have hprod : 0 ≤ ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) * (Real.log 2 - 0.6931471803) :=
    mul_nonneg hKR0 (by linarith)
  have hK4 : ((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1 ≤ 4 * Real.log x := by nlinarith

  have hcard := gband_card_le_sq (a := a) (b := b) (c := c) (p := p) (q := q)
    (by omega) (by omega) (by omega) hco hq hpc x
  have hS2 := gS2_upper (a := a) (b := b) (c := c) (p := p) (q := q) hq x
  have hchain : GS2 a b c p q x ≤ (Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) ^ 2 :=
    le_trans hS2 (Nat.mul_le_mul_right _ hcard)
  have hchainR : (GS2 a b c p q x : ℝ)
      ≤ ((((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ))) ^ 2 := by
    have hc2 : ((GS2 a b c p q x : ℕ) : ℝ)
        ≤ (((Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hchain
    calc (GS2 a b c p q x : ℝ)
        ≤ (((Nat.log 2 (2 * p * x) + 1) ^ 2 * (p * x) ^ 2 : ℕ) : ℝ) := hc2
      _ = ((((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ))) ^ 2 := by
          push_cast; ring
  have hnn : (0 : ℝ) ≤ (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ)) := by
    positivity
  calc Real.sqrt (GS2 a b c p q x)
      ≤ Real.sqrt (((((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ))) ^ 2) :=
        Real.sqrt_le_sqrt hchainR
    _ = (((Nat.log 2 (2 * p * x) : ℕ) : ℝ) + 1) * ((p : ℝ) * (x : ℝ)) := Real.sqrt_sq hnn
    _ ≤ (4 * Real.log x) * ((p : ℝ) * (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hK4 (by positivity)
    _ = 4 * (p : ℝ) * (x : ℝ) * Real.log x := by ring

set_option maxHeartbeats 1000000 in
theorem gV_lower (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ cV : ℝ, 0 < cV ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      cV * (x : ℝ) * Real.log x ≤ Real.sqrt (GS2 a b c p q x) := by
  obtain ⟨c₁, hc₁, X₁, hX₁⟩ := gband_card_ge_sq a b c p q ha hb hc hco hq hqp hpd
  refine ⟨Real.sqrt c₁, Real.sqrt_pos.mpr hc₁, max X₁ 3, fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log hx3
  have hcard : c₁ * Real.log x ^ 2 ≤ ((GBand a b c p q x).card : ℝ) := hX₁ x hx1
  have hS2 : ((GBand a b c p q x).card : ℝ) * (x : ℝ) ^ 2 ≤ (GS2 a b c p q x : ℝ) := by
    have h := gS2_ge_card_sq a b c p q x
    have h2 : (((GBand a b c p q x).card * x ^ 2 : ℕ) : ℝ) ≤ ((GS2 a b c p q x : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h2
    linarith
  have hkey : c₁ * ((x : ℝ) * Real.log x) ^ 2 ≤ (GS2 a b c p q x : ℝ) := by
    have h2 : c₁ * Real.log x ^ 2 * (x : ℝ) ^ 2
        ≤ ((GBand a b c p q x).card : ℝ) * (x : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    calc c₁ * ((x : ℝ) * Real.log x) ^ 2 = c₁ * Real.log x ^ 2 * (x : ℝ) ^ 2 := by ring
      _ ≤ ((GBand a b c p q x).card : ℝ) * (x : ℝ) ^ 2 := h2
      _ ≤ (GS2 a b c p q x : ℝ) := hS2
  have hnn : (0 : ℝ) ≤ (x : ℝ) * Real.log x := mul_nonneg hxpos.le (by linarith)
  calc Real.sqrt c₁ * (x : ℝ) * Real.log x
      = Real.sqrt c₁ * Real.sqrt (((x : ℝ) * Real.log x) ^ 2) := by
        rw [Real.sqrt_sq hnn]; ring
    _ = Real.sqrt (c₁ * ((x : ℝ) * Real.log x) ^ 2) := (Real.sqrt_mul hc₁.le _).symm
    _ ≤ Real.sqrt (GS2 a b c p q x) := Real.sqrt_le_sqrt hkey

end Erdos123Band
end Module_GBandAux

section Module_GLowEnergy

open scoped ENNReal

namespace Erdos123Band

section GLowEnergy

variable {a b c : ℕ}

set_option maxHeartbeats 4000000 in
theorem gchain_diff_dvd (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hco : PairwiseCoprime3 a b c)
    {n : ℕ} (Φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (hwt : ∀ v ∈ Tri n, 0 < wt a b c (Φ v))
    (hface : ∀ v ∈ Tri n,
      (v.1 = 0 → (Φ v).1 = 0) ∧ (v.2.1 = 0 → (Φ v).2.1 = 0) ∧
      (v.2.2 = 0 → (Φ v).2.2 = 0))
    (hn : 48 ≤ n) {q j : ℕ} (hq : q ∈ midQ n) (hj : j ∈ midJ q)
    (t t' : ℝ)
    (hrd : ∀ i, i < q → rdef a b c n Φ q t i = rdef a b c n Φ q t' i)
    (hpd : ∀ s, s < n - q → pdef a b c n Φ q j t s = pdef a b c n Φ q j t' s) :
    (rwS a b c n Φ q 0 : ℤ) ∣ (rdv a b c n Φ q t 0 - rdv a b c n Φ q t' 0) := by
  obtain ⟨hq1, hq2⟩ := midQ_bounds hq
  obtain ⟨hj1, hj2⟩ := midJ_bounds hj
  have hjq : j ≤ q := by omega
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega

  have hrs : ∀ i, i ≤ q → 0 < rwS a b c n Φ q i := by
    intro i hi
    show 0 < wt a b c (Φ (rowV n q i))
    exact hwt _ (rowV_mem_Tri hn hq hi)
  have hps : ∀ s, s ≤ n - q → 0 < pwS a b c n Φ q j s := by
    intro s hs
    show 0 < wt a b c (Φ (pathV n q j s))
    exact hwt _ (pathV_mem_Tri hn hq hj hs)

  have hrB : ∀ i, i < q → 0 < rwB a b c n Φ q i := by
    intro i _
    exact edgeA_pos ha0 hb0 hc0 _ _
  have hpB : ∀ s, s < n - q → 0 < pwB a b c n Φ q j s := by
    intro s _
    exact edgeA_pos ha0 hb0 hc0 _ _

  have hrrel : ∀ i, i < q →
      rwA a b c n Φ q i * rwS a b c n Φ q i
        = rwB a b c n Φ q i * rwS a b c n Φ q (i + 1) := by
    intro i _
    exact edgeA_mul_wt a b c _ _
  have hprel : ∀ s, s < n - q →
      pwA a b c n Φ q j s * pwS a b c n Φ q j s
        = pwB a b c n Φ q j s * pwS a b c n Φ q j (s + 1) := by
    intro s _
    exact edgeA_mul_wt a b c _ _

  set Δr : ℕ → ℤ := fun i => rdv a b c n Φ q t i - rdv a b c n Φ q t' i with hΔr
  set Δp : ℕ → ℤ := fun s => pdv a b c n Φ q j t s - pdv a b c n Φ q j t' s with hΔp
  have hrdΔ : ∀ i, i < q →
      (rwB a b c n Φ q i : ℤ) * Δr (i + 1) = (rwA a b c n Φ q i : ℤ) * Δr i := by
    intro i hi
    have h := hrd i hi
    simp only [rdef] at h
    simp only [hΔr]
    linear_combination h
  have hpdΔ : ∀ s, s < n - q →
      (pwB a b c n Φ q j s : ℤ) * Δp (s + 1) = (pwA a b c n Φ q j s : ℤ) * Δp s := by
    intro s hs
    have h := hpd s hs
    simp only [pdef] at h
    simp only [hΔp]
    linear_combination h

  have hjuncV : pathV n q j 0 = rowV n q (q - j) := pathV_zero hjq
  have hjunc_s : pwS a b c n Φ q j 0 = rwS a b c n Φ q (q - j) := by
    simp only [pwS, rwS, hjuncV]
  have hjunc_d : Δp 0 = Δr (q - j) := by
    simp only [hΔp, hΔr, pdv, rdv, pwS, rwS, hjuncV]

  have hrow0 : rowV n q 0 = ((0 : ℕ), q, n - q) := by
    simp only [rowV, Nat.sub_zero]
  have hrowq : rowV n q q = (q, (0 : ℕ), n - q) := by
    simp only [rowV, Nat.sub_self]
  have hpathP : pathV n q j (n - q) = (q - j + (n - q), j, (0 : ℕ)) := by
    simp only [pathV, Nat.sub_self]
  have hmem0 : rowV n q 0 ∈ Tri n := rowV_mem_Tri hn hq (by omega)
  have hmemq : rowV n q q ∈ Tri n := rowV_mem_Tri hn hq (le_refl q)
  have hmemP : pathV n q j (n - q) ∈ Tri n := pathV_mem_Tri hn hq hj (le_refl _)
  have hface0 := (hface _ hmem0).1
  have hfaceq := (hface _ hmemq).2.1
  have hfaceP := (hface _ hmemP).2.2
  have hk0 : (Φ (rowV n q 0)).1 = 0 := by
    apply hface0
    rw [hrow0]
  have hl0 : (Φ (rowV n q q)).2.1 = 0 := by
    apply hfaceq
    rw [hrowq]
  have hm0 : (Φ (pathV n q j (n - q))).2.2 = 0 := by
    apply hfaceP
    rw [hpathP]
  have hw0 : rwS a b c n Φ q 0
      = b ^ (Φ (rowV n q 0)).2.1 * c ^ (Φ (rowV n q 0)).2.2 := by
    simp only [rwS, wt, hk0, pow_zero, one_mul]
  have hwq : rwS a b c n Φ q q
      = a ^ (Φ (rowV n q q)).1 * c ^ (Φ (rowV n q q)).2.2 := by
    simp only [rwS, wt, hl0, pow_zero, mul_one]
  have hwP : pwS a b c n Φ q j (n - q)
      = a ^ (Φ (pathV n q j (n - q))).1 * b ^ (Φ (pathV n q j (n - q))).2.1 := by
    simp only [pwS, wt, hm0, pow_zero, mul_one]
  have hgcd : Nat.gcd (Nat.gcd (rwS a b c n Φ q 0) (rwS a b c n Φ q q))
      (pwS a b c n Φ q j (n - q)) = 1 := by
    rw [hw0, hwq, hwP]
    exact corner_gcd_eq_one hco _ _ _ _ _ _
  exact chain_dvd (rwS a b c n Φ q) (pwS a b c n Φ q j) Δr Δp
    (rwA a b c n Φ q) (rwB a b c n Φ q) (pwA a b c n Φ q j) (pwB a b c n Φ q j)
    hrs hps hrB hpB hrrel hprel hrdΔ hpdΔ (q - j) (by omega) hjunc_s hjunc_d hgcd

end GLowEnergy

section GLowEnergyMeasure

set_option maxHeartbeats 4000000 in
theorem glow_energy_measure (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ C₄ : ℕ, 1 ≤ C₄ ∧ ∃ X₂ : ℕ, ∀ x : ℕ, X₂ ≤ x →
      MeasureTheory.volume
          {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x}
        ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄) := by
  classical
  have ha2 : 2 ≤ a := ha
  have hb2 : 2 ≤ b := hb
  have hc2 : 2 ≤ c := hc
  obtain ⟨c₀, C₀, D, hc₀, hC₀, hD1, X₀g, hX₀g2, hgrid⟩ :=
    ggrid_embedding (a := a) (b := b) (c := c) (p := p) (q := q) ha2 hb2 hc2 hco hq hqp hpd
  set K : ℕ := (a * b * c) ^ D with hKdef
  have habc8 : 8 ≤ a * b * c := by
    calc 8 = 2 * 2 * 2 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hK8 : 8 ≤ K := by
    rw [hKdef]
    calc 8 ≤ a * b * c := habc8
      _ = (a * b * c) ^ 1 := (pow_one _).symm
      _ ≤ (a * b * c) ^ D := Nat.pow_le_pow_right (le_trans (by norm_num) habc8) hD1
  have hKR : (8 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK8
  set δ : ℝ := 1 / (4 * K) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    positivity
  set B1 : ℕ := ⌈4 / (c₀ * δ ^ 2)⌉₊ with hB1def
  set B2 : ℕ := ⌈7 / (c₀ * δ ^ 2)⌉₊ with hB2def
  set B : ℕ := 2 * (B1 + B2 + 2) with hBdef
  set C₄ : ℕ := 2 * B + 3 with hC₄def
  set CCn : ℕ := (B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) with hCCndef
  set T₃ : ℝ := 3 * (CCn : ℝ) * (2 * C₀) ^ (2 * B + 2) + 1 with hT₃def
  set X₂ : ℕ := max X₀g (max 3 (max ⌈Real.exp (96 / c₀)⌉₊
    (max ⌈Real.exp T₃⌉₊ ⌈Real.exp (1 / C₀)⌉₊))) with hX₂def
  refine ⟨C₄, by omega, X₂, fun x hx => ?_⟩
  simp only [hX₂def, max_le_iff] at hx
  obtain ⟨hxX₀g, hx3, hxc₀, hxT₃, hxC₀⟩ := hx
  have hx1 : 1 ≤ x := by omega
  have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  set L : ℝ := Real.log x with hLdef
  have hthresh : ∀ T : ℝ, ⌈Real.exp T⌉₊ ≤ x → T ≤ L := by
    intro T hT
    have h1 : Real.exp T ≤ (x : ℝ) := by
      calc Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (x : ℝ) := by exact_mod_cast hT
    calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
      _ ≤ L := Real.log_le_log (Real.exp_pos T) h1
  have hL96 : 96 / c₀ ≤ L := hthresh _ hxc₀
  have hLT₃ : T₃ ≤ L := hthresh _ hxT₃
  have hLC₀ : 1 / C₀ ≤ L := hthresh _ hxC₀
  have hL0 : 0 < L := by
    have h96 : (0 : ℝ) < 96 / c₀ := by positivity
    linarith
  obtain ⟨n, Φ, ⟨hnlow, hnhigh⟩, hband, hinj, hface, hjump⟩ := hgrid x hxX₀g
  have hwtpos : ∀ v ∈ Tri n, 0 < wt a b c (Φ v) := by
    intro v hv
    have h1 := ((mem_GBand hq).mp (hband v hv)).2.1
    omega
  have hc₀L96 : (96 : ℝ) ≤ c₀ * L := by
    have h1 : c₀ * (96 / c₀) ≤ c₀ * L := mul_le_mul_of_nonneg_left hL96 hc₀.le
    rw [mul_div_cancel₀ _ hc₀.ne'] at h1
    linarith
  have hn96 : 96 ≤ n := by
    have h1 : (96 : ℝ) ≤ (n : ℝ) := by
      calc (96 : ℝ) ≤ c₀ * L := hc₀L96
        _ = c₀ * Real.log x := by rw [hLdef]
        _ ≤ (n : ℝ) := hnlow
    exact_mod_cast h1
  have hn48 : 48 ≤ n := by omega
  set E : Set ℝ := {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x}
    with hEdef

  set Amap : CodeT → Set ℝ := fun cd =>
    if h : (E ∩ SCode a b c n Φ cd).Nonempty then
      arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x
    else ∅ with hAmapdef

  have hcover : ∀ t ∈ E, ∃ cd ∈ Codes n K B, t ∈ Amap cd := by
    intro t htE
    obtain ⟨ht01, htQ⟩ := htE
    obtain ⟨ht0, ht1⟩ := ht01

    set Bad : ℕ × ℕ × ℕ → Prop := fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| with hBaddef
    set H : ℕ := ((TriF n).filter (fun v =>
      δ < |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)|)).card with hHdef
    have hHQ : (H : ℝ) * δ ^ 2 ≤ GQenergy a b c p q x t :=
      gbadF_card_le a b c p q x n Φ t δ hδ0 hband hinj
    have hHδL : (H : ℝ) * δ ^ 2 ≤ L := by
      calc (H : ℝ) * δ ^ 2 ≤ GQenergy a b c p q x t := hHQ
        _ ≤ Real.log x := htQ
        _ = L := by rw [hLdef]

    have hHhyp : ∀ F : Finset (ℕ × ℕ × ℕ), (∀ v ∈ F, v ∈ Tri n ∧ Bad v) → F.card ≤ H := by
      intro F hF
      rw [hHdef]
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hv1, hv2⟩ := hF v hv
      rw [Finset.mem_filter]
      exact ⟨mem_TriF.mpr hv1, hv2⟩
    obtain ⟨u, hu, j, hj, hrowH, hpathH⟩ := exists_sparse_row_and_path hn48 Bad H hHhyp
    obtain ⟨hu1, hu2⟩ := midQ_bounds hu
    obtain ⟨hj1, hj2⟩ := midJ_bounds hj
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hc₀L_le_n : c₀ * L ≤ (n : ℝ) := by
      calc c₀ * L = c₀ * Real.log x := by rw [hLdef]
        _ ≤ (n : ℝ) := hnlow

    have hkey : ∀ m k : ℕ, n * m ≤ k * H → (m : ℝ) * (c₀ * δ ^ 2) ≤ (k : ℝ) := by
      intro m k hmk
      have hnm : (n : ℝ) * m ≤ (k : ℝ) * H := by exact_mod_cast hmk
      have e1 : c₀ * L * ((m : ℝ) * δ ^ 2) ≤ (n : ℝ) * ((m : ℝ) * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hc₀L_le_n (by positivity)
      have e2 : (n : ℝ) * m * δ ^ 2 ≤ (k : ℝ) * H * δ ^ 2 :=
        mul_le_mul_of_nonneg_right hnm (by positivity)
      have e3 : (k : ℝ) * ((H : ℝ) * δ ^ 2) ≤ (k : ℝ) * L :=
        mul_le_mul_of_nonneg_left hHδL (by positivity)
      have h1 : (m : ℝ) * (c₀ * δ ^ 2) * L ≤ (k : ℝ) * L := by nlinarith [e1, e2, e3]
      exact le_of_mul_le_mul_right h1 hL0
    have hrow_le : (rowBad Bad n u).card ≤ B1 := by
      have h2 : ((rowBad Bad n u).card : ℝ) ≤ 4 / (c₀ * δ ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have h := hkey _ 4 hrowH
        calc ((rowBad Bad n u).card : ℝ) * (c₀ * δ ^ 2) ≤ ((4 : ℕ) : ℝ) := h
          _ = 4 := by norm_num
      calc (rowBad Bad n u).card = ⌈((rowBad Bad n u).card : ℝ)⌉₊ :=
            (Nat.ceil_natCast _).symm
        _ ≤ ⌈(4 : ℝ) / (c₀ * δ ^ 2)⌉₊ := Nat.ceil_mono h2
        _ ≤ B1 := by rw [hB1def]
    have hpath_le : (pathBad Bad n u j).card ≤ B2 := by
      have h2 : ((pathBad Bad n u j).card : ℝ) ≤ 7 / (c₀ * δ ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have h := hkey _ 7 hpathH
        calc ((pathBad Bad n u j).card : ℝ) * (c₀ * δ ^ 2) ≤ ((7 : ℕ) : ℝ) := h
          _ = 7 := by norm_num
      calc (pathBad Bad n u j).card = ⌈((pathBad Bad n u j).card : ℝ)⌉₊ :=
            (Nat.ceil_natCast _).symm
        _ ≤ ⌈(7 : ℝ) / (c₀ * δ ^ 2)⌉₊ := Nat.ceil_mono h2
        _ ≤ B2 := by rw [hB2def]

    have hrow_coeff : ∀ i, i < u → rwA a b c n Φ u i ≤ K ∧ rwB a b c n Φ u i ≤ K := by
      intro i hi
      have hv := rowV_mem_Tri (n := n) hn48 hu (by omega : i ≤ u)
      have hw := rowV_mem_Tri (n := n) hn48 hu (by omega : i + 1 ≤ u)
      have hadj := rowV_adjacent (n := n) (q := u) (i := i) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      constructor
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.2.1
          hj6.2.2.2.1 hj6.2.2.2.2.2 |>.trans_eq hKdef.symm
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.1
          hj6.2.2.1 hj6.2.2.2.2.1 |>.trans_eq hKdef.symm
    have hpath_coeff : ∀ s, s < n - u →
        pwA a b c n Φ u j s ≤ K ∧ pwB a b c n Φ u j s ≤ K := by
      intro s hs
      have hv := pathV_mem_Tri (n := n) hn48 hu hj (by omega : s ≤ n - u)
      have hw := pathV_mem_Tri (n := n) hn48 hu hj (by omega : s + 1 ≤ n - u)
      have hadj := pathV_adjacent (n := n) (q := u) (j := j) (s := s) (by omega) (by omega)
      have hj6 := hjump _ hv _ hw hadj
      constructor
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.2.1
          hj6.2.2.2.1 hj6.2.2.2.2.2 |>.trans_eq hKdef.symm
      · exact edgeA_le (by omega) (by omega) (by omega) hj6.1
          hj6.2.2.1 hj6.2.2.2.2.1 |>.trans_eq hKdef.symm

    have hrdef_le : ∀ i, i < u → rdef a b c n Φ u t i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro i hi
      obtain ⟨hA, hB⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ u t i
      have h1 : |(rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (rwA a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have habs : |((rdef a b c n Φ u t i : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ u i : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ u i : ℝ) := by positivity
        calc |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)
            - (rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)|
            ≤ |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ u i : ℝ) * (1 / 2) + (rwA a b c n Φ u i : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    have hpdef_le : ∀ s, s < n - u →
        pdef a b c n Φ u j t s ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      intro s hs
      obtain ⟨hA, hB⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ u j t s
      have h1 : |(pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t|
          ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have h2 : |(pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_sub_comm]
        exact abs_sub_round _
      have hAR : (pwA a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have habs : |((pdef a b c n Φ u j t s : ℤ) : ℝ)| ≤ (K : ℝ) := by
        rw [hid]
        have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ u j s : ℝ) := by positivity
        have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ u j s : ℝ) := by positivity
        calc |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ u j s : ℝ) * (1 / 2) + (pwA a b c n Φ u j s : ℝ) * (1 / 2) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1 hB0
              · exact mul_le_mul_of_nonneg_left h2 hA0
          _ ≤ (K : ℝ) * (1 / 2) + (K : ℝ) * (1 / 2) := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right hBR (by norm_num)
              · apply mul_le_mul_of_nonneg_right hAR (by norm_num)
          _ = (K : ℝ) := by ring
      rw [Finset.mem_Icc]
      have := abs_le.mp habs
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2

    have hgood_of_notbad : ∀ v, ¬Bad v →
        |(wt a b c (Φ v) : ℝ) * t - round ((wt a b c (Φ v) : ℝ) * t)| ≤ δ := by
      intro v hv
      rw [hBaddef] at hv
      push_neg at hv
      exact hv
    have h2Kδ : 2 * (K : ℝ) * δ < 1 := by
      rw [hδdef]
      have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
      rw [show 2 * (K : ℝ) * (1 / (4 * K)) = 1 / 2 by field_simp; ring]
      norm_num
    have hrdef_zero : ∀ i, i < u → ¬Bad (rowV n u i) → ¬Bad (rowV n u (i + 1)) →
        rdef a b c n Φ u t i = 0 := by
      intro i hi hg1 hg2
      obtain ⟨hA, hB⟩ := hrow_coeff i hi
      have hid := rdef_cast (a := a) (b := b) (c := c) (n := n) Φ u t i
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (rwA a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (rwB a b c n Φ u i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have hA0 : (0 : ℝ) ≤ (rwA a b c n Φ u i : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (rwB a b c n Φ u i : ℝ) := by positivity
      have habs : |((rdef a b c n Φ u t i : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)
            - (rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)|
            ≤ |(rwB a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t (i + 1) : ℝ) - (rwS a b c n Φ u (i + 1) : ℝ) * t)|
              + |(rwA a b c n Φ u i : ℝ)
              * ((rdv a b c n Φ u t i : ℝ) - (rwS a b c n Φ u i : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (rwB a b c n Φ u i : ℝ) * δ + (rwA a b c n Φ u i : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |rdef a b c n Φ u t i| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega
    have hpdef_zero : ∀ s, s < n - u → ¬Bad (pathV n u j s) → ¬Bad (pathV n u j (s + 1)) →
        pdef a b c n Φ u j t s = 0 := by
      intro s hs hg1 hg2
      obtain ⟨hA, hB⟩ := hpath_coeff s hs
      have hid := pdef_cast (a := a) (b := b) (c := c) (n := n) Φ u j t s
      have h1 := hgood_of_notbad _ hg2
      have h2 := hgood_of_notbad _ hg1
      have h1' : |(pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t|
          ≤ δ := by
        rw [abs_sub_comm]
        exact h1
      have h2' : |(pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t| ≤ δ := by
        rw [abs_sub_comm]
        exact h2
      have hAR : (pwA a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hA
      have hBR : (pwB a b c n Φ u j s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hB
      have hA0 : (0 : ℝ) ≤ (pwA a b c n Φ u j s : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (pwB a b c n Φ u j s : ℝ) := by positivity
      have habs : |((pdef a b c n Φ u j t s : ℤ) : ℝ)| < 1 := by
        rw [hid]
        calc |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)
            - (pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)|
            ≤ |(pwB a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t (s + 1) : ℝ) - (pwS a b c n Φ u j (s + 1) : ℝ) * t)|
              + |(pwA a b c n Φ u j s : ℝ)
              * ((pdv a b c n Φ u j t s : ℝ) - (pwS a b c n Φ u j s : ℝ) * t)| := by
              exact abs_sub_le_abs_add_abs _ _
          _ ≤ (pwB a b c n Φ u j s : ℝ) * δ + (pwA a b c n Φ u j s : ℝ) * δ := by
              rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hA0]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left h1' hB0
              · exact mul_le_mul_of_nonneg_left h2' hA0
          _ ≤ (K : ℝ) * δ + (K : ℝ) * δ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hBR hδ0.le
              · exact mul_le_mul_of_nonneg_right hAR hδ0.le
          _ = 2 * (K : ℝ) * δ := by ring
          _ < 1 := h2Kδ
      have h3 : |pdef a b c n Φ u j t s| < 1 := by exact_mod_cast habs
      rw [abs_lt] at h3
      omega

    set rdfF : Finset ℕ := (Finset.range u).filter (fun i => rdef a b c n Φ u t i ≠ 0)
      with hrdfFdef
    set pdfF : Finset ℕ :=
      (Finset.range (n - u)).filter (fun s => pdef a b c n Φ u j t s ≠ 0) with hpdfFdef
    set rdf : Finset (ℕ × ℤ) := rdfF.image (fun i => (i, rdef a b c n Φ u t i)) with hrdfdef
    set pdf : Finset (ℕ × ℤ) := pdfF.image (fun s => (s, pdef a b c n Φ u j t s))
      with hpdfdef

    have hrdfF_sub : rdfF ⊆ (rowBad Bad n u) ∪ (rowBad Bad n u).image (fun i => i - 1) := by
      intro i hi
      rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hiq, hine⟩ := hi
      by_cases hbb1 : Bad (rowV n u i)
      · apply Finset.mem_union_left
        rw [rowBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hbb1⟩
      · by_cases hbb2 : Bad (rowV n u (i + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨i + 1, ?_, by omega⟩
          rw [rowBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hbb2⟩
        · exact absurd (hrdef_zero i hiq hbb1 hbb2) hine
    have hpdfF_sub : pdfF ⊆ (pathBad Bad n u j) ∪ (pathBad Bad n u j).image (fun s => s - 1) := by
      intro s hs
      rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨hsq, hsne⟩ := hs
      by_cases hbb1 : Bad (pathV n u j s)
      · apply Finset.mem_union_left
        rw [pathBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hbb1⟩
      · by_cases hbb2 : Bad (pathV n u j (s + 1))
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨s + 1, ?_, by omega⟩
          rw [pathBad, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hbb2⟩
        · exact absurd (hpdef_zero s hsq hbb1 hbb2) hsne
    have hrdf_card : rdf.card ≤ B := by
      calc rdf.card ≤ rdfF.card := Finset.card_image_le
        _ ≤ ((rowBad Bad n u) ∪ (rowBad Bad n u).image (fun i => i - 1)).card :=
            Finset.card_le_card hrdfF_sub
        _ ≤ (rowBad Bad n u).card + ((rowBad Bad n u).image (fun i => i - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ (rowBad Bad n u).card + (rowBad Bad n u).card := by
            have := Finset.card_image_le (s := rowBad Bad n u) (f := fun i => i - 1)
            omega
        _ ≤ B1 + B1 := by
            have := hrow_le
            omega
        _ ≤ B := by
            rw [hBdef]
            omega
    have hpdf_card : pdf.card ≤ B := by
      calc pdf.card ≤ pdfF.card := Finset.card_image_le
        _ ≤ ((pathBad Bad n u j) ∪ (pathBad Bad n u j).image (fun s => s - 1)).card :=
            Finset.card_le_card hpdfF_sub
        _ ≤ (pathBad Bad n u j).card + ((pathBad Bad n u j).image (fun s => s - 1)).card :=
            Finset.card_union_le _ _
        _ ≤ (pathBad Bad n u j).card + (pathBad Bad n u j).card := by
            have := Finset.card_image_le (s := pathBad Bad n u j) (f := fun s => s - 1)
            omega
        _ ≤ B2 + B2 := by
            have := hpath_le
            omega
        _ ≤ B := by
            rw [hBdef]
            omega

    have hcdmem : ((u, j, rdf, pdf) : CodeT) ∈ Codes n K B := by
      rw [Codes]
      simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro pt hpt
          rw [hrdfdef, Finset.mem_image] at hpt
          obtain ⟨i, hi, rfl⟩ := hpt
          rw [hrdfFdef, Finset.mem_filter, Finset.mem_range] at hi
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hrdef_le i hi.1⟩
        · exact hrdf_card
      · rw [DefCodes, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro pt hpt
          rw [hpdfdef, Finset.mem_image] at hpt
          obtain ⟨s, hs, rfl⟩ := hpt
          rw [hpdfFdef, Finset.mem_filter, Finset.mem_range] at hs
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hpdef_le s hs.1⟩
        · exact hpdf_card

    have hrdf_fst : rdf.image Prod.fst = rdfF := by
      rw [hrdfdef, Finset.image_image]
      exact Finset.image_id'
    have hpdf_fst : pdf.image Prod.fst = pdfF := by
      rw [hpdfdef, Finset.image_image]
      exact Finset.image_id'
    have htS : t ∈ SCode a b c n Φ (u, j, rdf, pdf) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro pt hpt
        rw [hrdfdef, Finset.mem_image] at hpt
        obtain ⟨i, _, rfl⟩ := hpt
        rfl
      · intro i hi hnot
        rw [show ((u, j, rdf, pdf) : CodeT).2.2.1 = rdf from rfl, hrdf_fst, hrdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hi, hne⟩)
      · intro pt hpt
        rw [hpdfdef, Finset.mem_image] at hpt
        obtain ⟨s, _, rfl⟩ := hpt
        rfl
      · intro s hs hnot
        rw [show ((u, j, rdf, pdf) : CodeT).2.2.2 = pdf from rfl, hpdf_fst, hpdfFdef] at hnot
        by_contra hne
        exact hnot (by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hs, hne⟩)

    have hne : (E ∩ SCode a b c n Φ (u, j, rdf, pdf)).Nonempty :=
      ⟨t, ⟨⟨ht0, ht1⟩, htQ⟩, htS⟩
    refine ⟨(u, j, rdf, pdf), hcdmem, ?_⟩
    have hAeq : Amap (u, j, rdf, pdf)
        = arc3 (rwS a b c n Φ u 0) (rdv a b c n Φ u hne.choose 0) x := by
      rw [hAmapdef]
      exact dif_pos hne
    rw [hAeq]
    obtain ⟨ht'E, ht'S⟩ := hne.choose_spec
    obtain ⟨⟨ht'0, ht'1⟩, _⟩ := ht'E

    obtain ⟨hdefr, hdefp⟩ := SCode_defects_eq (a := a) (b := b) (c := c) htS ht'S
    have hdvd := gchain_diff_dvd ha2 hb2 hc2 hco Φ hwtpos hface hn48 hu hj
      t hne.choose hdefr hdefp
    obtain ⟨r, hr⟩ := hdvd

    have hs₀mem := hband _ (rowV_mem_Tri hn48 hu (by omega : 0 ≤ u))
    have hs₀x : x ≤ rwS a b c n Φ u 0 := ((mem_GBand hq).mp hs₀mem).2.1
    have hs₀0 : 0 < rwS a b c n Φ u 0 := by omega
    have hs₀R : (0 : ℝ) < (rwS a b c n Φ u 0 : ℝ) := by exact_mod_cast hs₀0
    have hbound : ∀ v : ℝ, 0 ≤ v → v < 1 →
        0 ≤ rdv a b c n Φ u v 0 ∧ rdv a b c n Φ u v 0 ≤ (rwS a b c n Φ u 0 : ℤ) := by
      intro v hv0 hv1
      constructor
      · apply round_nonneg_of_nonneg
        positivity
      · apply round_le_nat (by positivity)
        calc (rwS a b c n Φ u 0 : ℝ) * v < (rwS a b c n Φ u 0 : ℝ) * 1 :=
              mul_lt_mul_of_pos_left hv1 hs₀R
          _ = (rwS a b c n Φ u 0 : ℝ) := mul_one _
    obtain ⟨hbd1, hbd2⟩ := hbound t ht0 ht1
    obtain ⟨hbd1', hbd2'⟩ := hbound hne.choose ht'0 ht'1
    have hs₀Z : (0 : ℤ) < (rwS a b c n Φ u 0 : ℤ) := by exact_mod_cast hs₀0
    have hprodlo : -((rwS a b c n Φ u 0 : ℕ) : ℤ) ≤ ((rwS a b c n Φ u 0 : ℕ) : ℤ) * r := by
      rw [← hr]
      omega
    have hprodhi : ((rwS a b c n Φ u 0 : ℕ) : ℤ) * r ≤ ((rwS a b c n Φ u 0 : ℕ) : ℤ) := by
      rw [← hr]
      omega
    have hrlo : -1 ≤ r := by nlinarith [hprodlo, hs₀Z]
    have hrhi : r ≤ 1 := by nlinarith [hprodhi, hs₀Z]
    have hcong : rdv a b c n Φ u t 0 = rdv a b c n Φ u hne.choose 0 - rwS a b c n Φ u 0
        ∨ rdv a b c n Φ u t 0 = rdv a b c n Φ u hne.choose 0
        ∨ rdv a b c n Φ u t 0 = rdv a b c n Φ u hne.choose 0 + rwS a b c n Φ u 0 := by
      interval_cases r
      · left; omega
      · right; left; omega
      · right; right; omega
    have hnear : |(rwS a b c n Φ u 0 : ℝ) * t - (rdv a b c n Φ u t 0 : ℝ)| ≤ 1 / 2 :=
      abs_sub_round _
    exact mem_arc3 hs₀x hx1 hnear hcong

  have hsubset : E ⊆ ⋃ cd ∈ Codes n K B, Amap cd := by
    intro t ht
    obtain ⟨cd, hcd, hmem⟩ := hcover t ht
    exact Set.mem_biUnion hcd hmem
  have hvol_arc : ∀ cd ∈ Codes n K B,
      MeasureTheory.volume (Amap cd) ≤ ENNReal.ofReal (3 / (x : ℝ)) := by
    intro cd _
    by_cases h : (E ∩ SCode a b c n Φ cd).Nonempty
    · have hAeq : Amap cd
          = arc3 (rwS a b c n Φ cd.1 0) (rdv a b c n Φ cd.1 h.choose 0) x := by
        rw [hAmapdef]
        exact dif_pos h
      rw [hAeq]
      exact arc3_volume _ _ _
    · have hAeq : Amap cd = ∅ := by
        rw [hAmapdef]
        exact dif_neg h
      rw [hAeq]
      simp
  calc MeasureTheory.volume E
      ≤ MeasureTheory.volume (⋃ cd ∈ Codes n K B, Amap cd) :=
        MeasureTheory.measure_mono hsubset
    _ ≤ ∑ cd ∈ Codes n K B, MeasureTheory.volume (Amap cd) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Codes n K B, ENNReal.ofReal (3 / (x : ℝ)) :=
        Finset.sum_le_sum hvol_arc
    _ = ((Codes n K B).card : ℝ≥0∞) * ENNReal.ofReal (3 / (x : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal

        have hcards : ((Codes n K B).card : ℝ)
            ≤ (CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2) := by
          have h1 := Codes_card_le n K B
          have h2 : ((Codes n K B).card : ℝ)
              ≤ (((B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) : ℕ) : ℝ) := by
            exact_mod_cast h1
          calc ((Codes n K B).card : ℝ)
              ≤ (((B + 1) ^ 2 * (2 * K + 2) ^ (2 * B) * (n + 1) ^ (2 * B + 2) : ℕ) : ℝ) := h2
            _ = (CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2) := by
                rw [hCCndef]
                push_cast
                ring
        have hn1 : ((n : ℝ) + 1) ≤ 2 * C₀ * L := by
          have h1 : (n : ℝ) ≤ C₀ * L := by
            calc (n : ℝ) ≤ C₀ * Real.log x := hnhigh
              _ = C₀ * L := by rw [hLdef]
          have h2 : (1 : ℝ) ≤ C₀ * L := by
            have h3 : C₀ * (1 / C₀) ≤ C₀ * L := mul_le_mul_of_nonneg_left hLC₀ hC₀.le
            rw [mul_div_cancel₀ _ hC₀.ne'] at h3
            linarith
          linarith
        have hCCn0 : (0 : ℝ) ≤ (CCn : ℝ) := by positivity
        have hL2B : (0 : ℝ) ≤ L ^ (2 * B + 2) := by positivity
        have hfinal : 3 * ((Codes n K B).card : ℝ) ≤ L ^ C₄ := by
          calc 3 * ((Codes n K B).card : ℝ)
              ≤ 3 * ((CCn : ℝ) * ((n : ℝ) + 1) ^ (2 * B + 2)) := by linarith [hcards]
            _ ≤ 3 * ((CCn : ℝ) * (2 * C₀ * L) ^ (2 * B + 2)) := by
                apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
                apply mul_le_mul_of_nonneg_left ?_ hCCn0
                apply pow_le_pow_left₀ (by positivity) hn1
            _ = (3 * (CCn : ℝ) * (2 * C₀) ^ (2 * B + 2)) * L ^ (2 * B + 2) := by
                rw [mul_pow]
                ring
            _ ≤ L * L ^ (2 * B + 2) := by
                apply mul_le_mul_of_nonneg_right ?_ hL2B
                rw [hT₃def] at hLT₃
                linarith
            _ = L ^ (2 * B + 3) := by
                rw [← pow_succ']
            _ = L ^ C₄ := by rw [hC₄def]
        calc ((Codes n K B).card : ℝ) * (3 / (x : ℝ))
            = (3 * ((Codes n K B).card : ℝ)) / (x : ℝ) := by ring
          _ ≤ L ^ C₄ / (x : ℝ) := by
              have hmul := mul_le_mul_of_nonneg_right hfinal hx0R.le
              rw [div_le_div_iff₀ hx0R hx0R]
              linarith [hmul]
          _ = 1 / (x : ℝ) * Real.log x ^ C₄ := by
              rw [hLdef]
              ring

end GLowEnergyMeasure

end Erdos123Band

end Module_GLowEnergy

section Module_GCosApprox

namespace Erdos123Band

open Finset

theorem cos_sub_exp_le {u : ℝ} (hu : |u| ≤ 1) :
    |Real.cos u - Real.exp (-(u ^ 2 / 2))| ≤ u ^ 4 := by
  have hu2 : u ^ 2 ≤ 1 := by
    have := abs_nonneg u
    nlinarith [sq_abs u]
  have hx : |(-(u ^ 2 / 2) : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 2 / 2)]
    linarith
  have h1 : |Real.cos u - (1 - u ^ 2 / 2)| ≤ |u| ^ 4 * (5 / 96) := Real.cos_bound hu
  have h2 : |Real.exp (-(u ^ 2 / 2)) - 1 - (-(u ^ 2 / 2))| ≤ (-(u ^ 2 / 2)) ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le hx
  have h2' : |(1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))| ≤ u ^ 4 / 4 := by
    have hrw : (1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))
        = -(Real.exp (-(u ^ 2 / 2)) - 1 - (-(u ^ 2 / 2))) := by ring
    rw [hrw, abs_neg]
    calc |Real.exp (-(u ^ 2 / 2)) - 1 - (-(u ^ 2 / 2))| ≤ (-(u ^ 2 / 2)) ^ 2 := h2
      _ = u ^ 4 / 4 := by ring
  have habs : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 4)]
  have htri : |Real.cos u - Real.exp (-(u ^ 2 / 2))|
      ≤ |Real.cos u - (1 - u ^ 2 / 2)| + |(1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))| := by
    have : Real.cos u - Real.exp (-(u ^ 2 / 2))
        = (Real.cos u - (1 - u ^ 2 / 2)) + ((1 - u ^ 2 / 2) - Real.exp (-(u ^ 2 / 2))) := by ring
    rw [this]
    exact abs_add_le _ _
  have h4 : (0:ℝ) ≤ u ^ 4 := by positivity
  rw [habs] at h1
  linarith

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have hf' : ∀ i ∈ t, |f i| ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hg' : ∀ i ∈ t, |g i| ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hfa : |f a| ≤ 1 := hf a (Finset.mem_insert_self a t)
      have hIH := ih hf' hg'
      have hQ : |∏ i ∈ t, g i| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun i _ => abs_nonneg _) hg'
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      set P := ∏ i ∈ t, f i with hP
      set Q := ∏ i ∈ t, g i with hQdef
      have key : f a * P - g a * Q = f a * (P - Q) + (f a - g a) * Q := by ring
      calc |f a * P - g a * Q| = |f a * (P - Q) + (f a - g a) * Q| := by rw [key]
        _ ≤ |f a * (P - Q)| + |(f a - g a) * Q| := abs_add_le _ _
        _ = |f a| * |P - Q| + |f a - g a| * |Q| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * |P - Q| + |f a - g a| * 1 := by
              have h1 : |f a| * |P - Q| ≤ 1 * |P - Q| :=
                mul_le_mul_of_nonneg_right hfa (abs_nonneg _)
              have h2 : |f a - g a| * |Q| ≤ |f a - g a| * 1 :=
                mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
              linarith
        _ = |P - Q| + |f a - g a| := by ring
        _ ≤ (∑ i ∈ t, |f i - g i|) + |f a - g a| := by linarith
        _ = |f a - g a| + ∑ i ∈ t, |f i - g i| := by ring

theorem abs_prod_cos_sub_exp_le {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, |c i| ≤ 1) :
    |(∏ i ∈ s, Real.cos (c i)) - Real.exp (-((∑ i ∈ s, c i ^ 2) / 2))|
      ≤ ∑ i ∈ s, c i ^ 4 := by
  have hexp : Real.exp (-((∑ i ∈ s, c i ^ 2) / 2)) = ∏ i ∈ s, Real.exp (-(c i ^ 2 / 2)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  rw [hexp]
  have hf : ∀ i ∈ s, |Real.cos (c i)| ≤ 1 := fun i _ => Real.abs_cos_le_one _
  have hg : ∀ i ∈ s, |Real.exp (-(c i ^ 2 / 2))| ≤ 1 := by
    intro i _
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (c i)])
  calc |(∏ i ∈ s, Real.cos (c i)) - ∏ i ∈ s, Real.exp (-(c i ^ 2 / 2))|
      ≤ ∑ i ∈ s, |Real.cos (c i) - Real.exp (-(c i ^ 2 / 2))| :=
        abs_prod_sub_prod_le s _ _ hf hg
    _ ≤ ∑ i ∈ s, c i ^ 4 :=
        Finset.sum_le_sum (fun i hi => cos_sub_exp_le (hc i hi))

end Erdos123Band
end Module_GCosApprox

section Module_GaussFT

open scoped Real
open MeasureTheory

namespace Erdos123Band

noncomputable section

set_option maxHeartbeats 4000000 in
lemma cpow_half_inv_two_pi :
    ((Real.pi : ℂ) / (2 * (Real.pi : ℂ) ^ 2)) ^ (1 / 2 : ℂ)
      = (1 / Real.sqrt (2 * Real.pi) : ℝ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hval : (Real.pi : ℂ) / (2 * (Real.pi : ℂ) ^ 2) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hval]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, ← one_div]

set_option maxHeartbeats 4000000 in
lemma gaussian_ft_complex (y : ℝ) :
    (∫ u : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u)))
      = (1 / Real.sqrt (2 * Real.pi) : ℝ) * Complex.exp (-((y : ℂ) ^ 2 / 2)) := by
  have hbre : (0 : ℝ) < (2 * (Real.pi : ℂ) ^ 2).re := by
    have : (2 * (Real.pi : ℂ) ^ 2) = ((2 * Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]; positivity
  have hint : ∀ u : ℝ,
      Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))
        = Complex.exp (Complex.I * ((-(2 * Real.pi * y) : ℝ) : ℂ) * u)
          * Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) := by
    intro u
    rw [mul_comm]
    congr 2
    rw [e]
    congr 1
    push_cast
    ring
  simp_rw [hint]
  rw [fourierIntegral_gaussian hbre ((-(2 * Real.pi * y) : ℝ) : ℂ)]
  rw [cpow_half_inv_two_pi]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  congr 2
  push_cast
  field_simp
  ring

set_option maxHeartbeats 4000000 in
lemma gauss_integrable (y : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))) := by
  have hbre : (0 : ℝ) < (2 * (Real.pi : ℂ) ^ 2).re := by
    have : (2 * (Real.pi : ℂ) ^ 2) = ((2 * Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]; positivity
  have hfun : (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u)))
      = (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * (u : ℂ) ^ 2
          + (-(2 * Real.pi * Complex.I * y)) * u + 0)) := by
    funext u
    rw [e, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact integrable_cexp_quadratic hbre _ 0

set_option maxHeartbeats 4000000 in
lemma gaussian_ft_real (y : ℝ) :
    (∫ u : ℝ, Real.cos (2 * Real.pi * y * u) * Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)))
      = (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y ^ 2 / 2)) := by
  have hcpx := gaussian_ft_complex y
  have hintg := gauss_integrable y
  have hpt : ∀ u : ℝ,
      (Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))).re
        = Real.cos (2 * Real.pi * y * u) * Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)) := by
    intro u
    have hAreal : Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * (u : ℂ) ^ 2)
        = ((Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)) : ℝ) : ℂ) := by
      rw [show -(2 * (Real.pi : ℂ) ^ 2) * (u : ℂ) ^ 2
            = ((-(2 * Real.pi ^ 2 * u ^ 2) : ℝ) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_exp]
    have here : (e (-(y * u))).re = Real.cos (2 * Real.pi * y * u) := by
      have hb : e (-(y * u)) = Complex.exp ((↑(2 * Real.pi * (-(y * u))) : ℂ) * Complex.I) := by
        rw [e]; congr 1; push_cast; ring
      rw [hb, Complex.exp_ofReal_mul_I_re]
      rw [show 2 * Real.pi * (-(y * u)) = -(2 * Real.pi * y * u) by ring, Real.cos_neg]
    rw [hAreal, Complex.re_ofReal_mul, here, mul_comm]
  have hlhs : (∫ u : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) ^ 2) * u ^ 2) * e (-(y * u))).re
      = ∫ u : ℝ, Real.cos (2 * Real.pi * y * u) * Real.exp (-(2 * Real.pi ^ 2 * u ^ 2)) := by
    have hre := _root_.integral_re (𝕜 := ℂ) hintg
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [← hlhs, hcpx, Complex.re_ofReal_mul,
    show -((y : ℂ) ^ 2 / 2) = ((-(y ^ 2 / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    Complex.ofReal_re]

set_option maxHeartbeats 4000000 in
theorem gaussian_integrable_scaled {A : ℝ} (hA : 0 < A) (y : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (y * u)) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
    have h := _root_.integrable_exp_neg_mul_sq hA
    simpa only [neg_mul] using h
  refine hg.mul_bdd (c := 1) ?_ ?_
  · fun_prop
  · refine Filter.Eventually.of_forall (fun u => ?_)
    simpa using Real.abs_cos_le_one (y * u)

set_option maxHeartbeats 4000000 in
theorem gaussian_ft_scaled {A : ℝ} (hA : 0 < A) (y : ℝ) :
    (∫ u : ℝ, Real.exp (-(A * u ^ 2)) * Real.cos (y * u))
      = Real.sqrt (Real.pi / A) * Real.exp (-(y ^ 2 / (4 * A))) := by
  have hbre : (0 : ℝ) < ((A : ℂ)).re := by simpa using hA
  have hFT := fourierIntegral_gaussian (b := (A : ℂ)) hbre ((y : ℝ) : ℂ)

  have hintg : Integrable
      (fun u : ℝ => Complex.exp (Complex.I * (y : ℂ) * u) * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)) := by
    have hfun : (fun u : ℝ => Complex.exp (Complex.I * (y : ℂ) * u)
          * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2))
        = (fun u : ℝ => Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2
            + (Complex.I * (y : ℂ)) * u + 0)) := by
      funext u
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hfun]
    exact integrable_cexp_quadratic hbre _ 0
  have hpt : ∀ u : ℝ,
      (Complex.exp (Complex.I * (y : ℂ) * u) * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)).re
        = Real.exp (-(A * u ^ 2)) * Real.cos (y * u) := by
    intro u
    have hAreal : Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)
        = ((Real.exp (-(A * u ^ 2)) : ℝ) : ℂ) := by
      rw [show -(A : ℂ) * (u : ℂ) ^ 2 = ((-(A * u ^ 2) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
    have here : (Complex.exp (Complex.I * (y : ℂ) * u)).re = Real.cos (y * u) := by
      rw [show Complex.I * (y : ℂ) * (u : ℂ) = ((y * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_re _
    rw [hAreal, mul_comm, Complex.re_ofReal_mul, here]
  have hlhs : (∫ u : ℝ, Complex.exp (Complex.I * (y : ℂ) * u)
        * Complex.exp (-(A : ℂ) * (u : ℂ) ^ 2)).re
      = ∫ u : ℝ, Real.exp (-(A * u ^ 2)) * Real.cos (y * u) := by
    have hre := _root_.integral_re (𝕜 := ℂ) hintg
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hrhs : ((Real.pi : ℂ) / (A : ℂ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(y : ℂ) ^ 2 / (4 * (A : ℂ)))
      = ((Real.sqrt (Real.pi / A) * Real.exp (-(y ^ 2 / (4 * A))) : ℝ) : ℂ) := by
    have hA' : (A : ℂ) ≠ 0 := by
      simpa using hA.ne'
    have h1 : ((Real.pi : ℂ) / (A : ℂ)) = ((Real.pi / A : ℝ) : ℂ) := by push_cast; ring
    have h2 : (-(y : ℂ) ^ 2 / (4 * (A : ℂ))) = ((-(y ^ 2 / (4 * A)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1, h2, ← Complex.ofReal_exp, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul, ← Real.sqrt_eq_rpow]
  rw [← hlhs, hFT, hrhs, Complex.ofReal_re]

set_option maxHeartbeats 4000000 in
theorem gaussian_ft_scaled_zero {A : ℝ} (hA : 0 < A) :
    (∫ u : ℝ, Real.exp (-A * u ^ 2)) = Real.sqrt (Real.pi / A) := by
  have h := gaussian_ft_scaled hA 0
  simp only [zero_mul, Real.cos_zero, mul_one] at h
  simp only [neg_mul]
  rw [h]
  norm_num

example {A : ℝ} (hA : 0 < A) : True := by
  have h1 : (∫ u : ℝ, Real.exp (-A * u ^ 2)) = Real.sqrt (Real.pi / A) :=
    gaussian_ft_scaled_zero hA
  have h2 : (∫ u : ℝ, Real.exp (-A * u ^ 2)) = Real.sqrt (Real.pi / A) :=
    _root_.integral_gaussian A
  trivial

set_option maxHeartbeats 4000000 in
theorem gauss_tail_Ioi {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    (∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2))) ≤ Real.exp (-(A * T ^ 2)) / (A * T) := by
  have hAT : -(A * T) < 0 := by nlinarith
  have hint1 : IntegrableOn (fun u : ℝ => Real.exp (-(A * u ^ 2))) (Set.Ioi T) := by
    have h := _root_.integrable_exp_neg_mul_sq hA
    have h' : Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
      simpa only [neg_mul] using h
    exact h'.integrableOn
  have hint2 : IntegrableOn (fun u : ℝ => Real.exp (-(A * T) * u)) (Set.Ioi T) :=
    integrableOn_exp_mul_Ioi hAT T
  have hmono : (∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)))
      ≤ ∫ u in Set.Ioi T, Real.exp (-(A * T) * u) := by
    refine MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Ioi ?_
    intro u hu
    have hu' : T < u := hu
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (mul_nonneg hA.le (hT.trans hu').le) (sub_nonneg.mpr hu'.le)]
  rw [integral_exp_mul_Ioi hAT T] at hmono
  refine hmono.trans_eq ?_
  rw [show -(A * T) * T = -(A * T ^ 2) by ring, neg_div_neg_eq]

set_option maxHeartbeats 4000000 in
theorem gauss_osc_tail_Ioi {A T : ℝ} (hA : 0 < A) (hT : 0 < T) (y : ℝ) :
    |∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)) * Real.cos (y * u)|
      ≤ Real.exp (-(A * T ^ 2)) / (A * T) := by
  have hint : IntegrableOn
      (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (y * u)) (Set.Ioi T) :=
    (gaussian_integrable_scaled hA y).integrableOn
  have hint1 : IntegrableOn (fun u : ℝ => Real.exp (-(A * u ^ 2))) (Set.Ioi T) := by
    have h := _root_.integrable_exp_neg_mul_sq hA
    have h' : Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
      simpa only [neg_mul] using h
    exact h'.integrableOn
  calc |∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)) * Real.cos (y * u)|
      ≤ ∫ u in Set.Ioi T, |Real.exp (-(A * u ^ 2)) * Real.cos (y * u)| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Ioi T, Real.exp (-(A * u ^ 2)) := by
        refine MeasureTheory.setIntegral_mono_on hint.abs hint1 measurableSet_Ioi ?_
        intro u _
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        calc Real.exp (-(A * u ^ 2)) * |Real.cos (y * u)|
            ≤ Real.exp (-(A * u ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
          _ = Real.exp (-(A * u ^ 2)) := mul_one _
    _ ≤ Real.exp (-(A * T ^ 2)) / (A * T) := gauss_tail_Ioi hA hT

end

end Erdos123Band
end Module_GaussFT

section Module_GPrincipal

open MeasureTheory

namespace Erdos123Band

noncomputable section

set_option maxHeartbeats 1000000 in
noncomputable def gT (x : ℕ) : ℝ := Real.sqrt (Real.sqrt (Real.log x))

set_option maxHeartbeats 1000000 in
noncomputable def gt₁ (a b c p q x : ℕ) : ℝ := gT x / Real.sqrt (GS2 a b c p q x)

set_option maxHeartbeats 1000000 in
lemma gauss_half_line {A : ℝ} (hA : 0 < A) (y : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (y * u))
      = Real.sqrt (Real.pi / A) * Real.exp (-(y ^ 2 / (4 * A))) / 2 := by
  have heven : ∀ u : ℝ,
      (fun v : ℝ => Real.exp (-(A * v ^ 2)) * Real.cos (y * v)) |u|
        = Real.exp (-(A * u ^ 2)) * Real.cos (y * u) := by
    intro u
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h]
      show Real.exp (-(A * (-u) ^ 2)) * Real.cos (y * (-u))
        = Real.exp (-(A * u ^ 2)) * Real.cos (y * u)
      rw [show (-u) ^ 2 = u ^ 2 by ring, show y * -u = -(y * u) by ring, Real.cos_neg]
  have hcomp := integral_comp_abs
    (f := fun v : ℝ => Real.exp (-(A * v ^ 2)) * Real.cos (y * v))
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall heven),
    gaussian_ft_scaled hA y] at hcomp
  linarith

set_option maxHeartbeats 1000000 in
lemma gprincipal_abstract {φ : ℝ → ℝ} {V θ T E : ℝ}
    (hφ : Continuous φ) (hV : 0 < V) (hT : 0 < T) (hθ : θ ^ 2 ≤ V ^ 2) (hE : 0 ≤ E)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) (T / V),
      |φ t - Real.exp (-(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2))| ≤ E) :
    Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
        - (T / V) * E
        - 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T)
      ≤ ∫ t in (0 : ℝ)..(T / V), φ t * Real.cos (Real.pi * θ * t) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := hpi.ne'
  have hVne : V ≠ 0 := hV.ne'
  have hTne : T ≠ 0 := hT.ne'
  set A : ℝ := Real.pi ^ 2 * V ^ 2 / 2 with hAdef
  have hA : 0 < A := by
    rw [hAdef]; exact div_pos (mul_pos (pow_pos hpi 2) (pow_pos hV 2)) two_pos
  set t₁ : ℝ := T / V with ht₁def
  have ht₁ : 0 < t₁ := div_pos hT hV
  have hcosC : Continuous (fun t : ℝ => Real.cos (Real.pi * θ * t)) := by fun_prop
  have hexpC : Continuous (fun t : ℝ => Real.exp (-(A * t ^ 2))) := by fun_prop
  have hgint : Integrable
      (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u)) :=
    gaussian_integrable_scaled hA (Real.pi * θ)

  have hb2 : (∫ t in (0 : ℝ)..t₁, Real.exp (-(A * t ^ 2)) * Real.cos (Real.pi * θ * t))
      = (∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u))
        - ∫ u in Set.Ioi t₁, Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u) :=
    (intervalIntegral.integral_Ioi_sub_Ioi hgint.integrableOn ht₁.le).symm

  have hsqrt : Real.sqrt (Real.pi / A) = Real.sqrt (2 / Real.pi) / V := by
    have hnn : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) / V := div_nonneg (Real.sqrt_nonneg _) hV.le
    have hkey : Real.pi / A = (Real.sqrt (2 / Real.pi) / V) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity), hAdef]
      field_simp
    rw [hkey, Real.sqrt_sq hnn]
  have hexpge : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-((Real.pi * θ) ^ 2 / (4 * A))) := by
    refine Real.exp_le_exp.mpr ?_
    have hq : (Real.pi * θ) ^ 2 / (4 * A) = θ ^ 2 / (2 * V ^ 2) := by
      rw [hAdef]; field_simp; ring
    rw [hq]
    have h2 : θ ^ 2 / (2 * V ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hθ]
    linarith
  have hmain : Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u) := by
    rw [gauss_half_line hA (Real.pi * θ), hsqrt]
    have hc : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) / V / 2 :=
      div_nonneg (div_nonneg (Real.sqrt_nonneg _) hV.le) (by norm_num)
    calc Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
        = Real.sqrt (2 / Real.pi) / V / 2 * Real.exp (-(1 / 2)) := by field_simp
      _ ≤ Real.sqrt (2 / Real.pi) / V / 2 * Real.exp (-((Real.pi * θ) ^ 2 / (4 * A))) :=
          mul_le_mul_of_nonneg_left hexpge hc
      _ = Real.sqrt (2 / Real.pi) / V * Real.exp (-((Real.pi * θ) ^ 2 / (4 * A))) / 2 := by
          ring

  have htail : |∫ u in Set.Ioi t₁, Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u)|
      ≤ 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T) := by
    have h := gauss_osc_tail_Ioi (A := A) (T := t₁) hA ht₁ (Real.pi * θ)
    have e1 : A * t₁ ^ 2 = Real.pi ^ 2 * T ^ 2 / 2 := by
      rw [hAdef, ht₁def]; field_simp
    have e2 : A * t₁ = Real.pi ^ 2 * V * T / 2 := by
      rw [hAdef, ht₁def]; field_simp
    rw [e1, e2] at h
    refine h.trans (le_of_eq ?_)
    field_simp

  have hIg : IntervalIntegrable
      (fun u : ℝ => Real.exp (-(A * u ^ 2)) * Real.cos (Real.pi * θ * u)) volume 0 t₁ :=
    (hexpC.mul hcosC).intervalIntegrable _ _
  have hIF : IntervalIntegrable
      (fun t => (φ t - Real.exp (-(A * t ^ 2))) * Real.cos (Real.pi * θ * t))
      volume 0 t₁ := ((hφ.sub hexpC).mul hcosC).intervalIntegrable _ _
  have hsplit : (∫ t in (0 : ℝ)..t₁, φ t * Real.cos (Real.pi * θ * t))
      = (∫ t in (0 : ℝ)..t₁, Real.exp (-(A * t ^ 2)) * Real.cos (Real.pi * θ * t))
        + ∫ t in (0 : ℝ)..t₁, (φ t - Real.exp (-(A * t ^ 2))) * Real.cos (Real.pi * θ * t) := by
    rw [← intervalIntegral.integral_add hIg hIF]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have herr : |∫ t in (0 : ℝ)..t₁, (φ t - Real.exp (-(A * t ^ 2)))
      * Real.cos (Real.pi * θ * t)| ≤ t₁ * E := by
    have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := fun t => (φ t - Real.exp (-(A * t ^ 2))) * Real.cos (Real.pi * θ * t)) ht₁.le
    have h2 : (∫ t in (0 : ℝ)..t₁, |(φ t - Real.exp (-(A * t ^ 2)))
        * Real.cos (Real.pi * θ * t)|) ≤ ∫ _t in (0 : ℝ)..t₁, E := by
      refine intervalIntegral.integral_mono_on ht₁.le hIF.abs
        intervalIntegrable_const (fun t ht => ?_)
      rw [abs_mul]
      have hc : |Real.cos (Real.pi * θ * t)| ≤ 1 := Real.abs_cos_le_one _
      have hd : |φ t - Real.exp (-(A * t ^ 2))| ≤ E := hb t ⟨ht.1, ht.2⟩
      nlinarith [abs_nonneg (φ t - Real.exp (-(A * t ^ 2))),
        abs_nonneg (Real.cos (Real.pi * θ * t))]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h2
    linarith
  rw [hsplit, hb2]
  have hA1 := abs_le.mp herr
  have hA2 := abs_le.mp htail
  linarith [hmain, hA1.1, hA2.2]

set_option maxHeartbeats 1000000 in
lemma gT_nonneg (x : ℕ) : 0 ≤ gT x := Real.sqrt_nonneg _

set_option maxHeartbeats 1000000 in
lemma gT_pow_four {x : ℕ} (hx : 1 ≤ x) : gT x ^ 4 = Real.log x := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  simp only [gT]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt hL]

set_option maxHeartbeats 1000000 in
lemma gT_eventually_ge (M : ℝ) : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → M ≤ gT x := by
  by_cases hM : M ≤ 0
  · exact ⟨0, fun x _ => hM.trans (gT_nonneg x)⟩
  push_neg at hM
  refine ⟨Nat.ceil (Real.exp (M ^ 4)) + 1, fun x hx => ?_⟩
  have hxR : Real.exp (M ^ 4) ≤ (x : ℝ) := by
    have h1 : (Nat.ceil (Real.exp (M ^ 4)) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (M ^ 4)) ≤ x)
    exact le_trans (Nat.le_ceil _) h1
  have hlog : M ^ 4 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (M ^ 4)) hxR
    rwa [Real.log_exp] at h
  have h1 : M ^ 2 ≤ Real.sqrt (Real.log x) := by
    have he : Real.sqrt (M ^ 4) = M ^ 2 := by
      rw [show M ^ 4 = (M ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc M ^ 2 = Real.sqrt (M ^ 4) := he.symm
      _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hlog
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM.le).symm
    _ ≤ Real.sqrt (Real.sqrt (Real.log x)) := Real.sqrt_le_sqrt h1

set_option maxHeartbeats 1000000 in
lemma gauss_const_ge : (23 / 100 : ℝ) ≤ Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / 2 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hs : (79 / 100 : ℝ) ≤ Real.sqrt (2 / Real.pi) := by
    have hrw : Real.sqrt ((79 / 100 : ℝ) ^ 2) = (79 / 100 : ℝ) := Real.sqrt_sq (by norm_num)
    calc (79 / 100 : ℝ) = Real.sqrt ((79 / 100 : ℝ) ^ 2) := hrw.symm
      _ ≤ Real.sqrt (2 / Real.pi) := by
          refine Real.sqrt_le_sqrt ?_
          rw [le_div_iff₀ Real.pi_pos]
          nlinarith [hpi]
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hehalf : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
    nlinarith [hsq, Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
  have hmul : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  have he : (3 / 5 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    nlinarith [hmul, hehalf, Real.exp_pos (1 / 2 : ℝ), Real.exp_pos (-(1 / 2 : ℝ))]
  have hprod : (79 / 100 : ℝ) * (3 / 5 : ℝ)
      ≤ Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) :=
    mul_le_mul hs he (by norm_num) (Real.sqrt_nonneg _)
  linarith

set_option maxHeartbeats 1000000 in
lemma exp_neg_four_le : Real.exp (-4 : ℝ) ≤ 1 / 16 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have e2 : Real.exp (1 : ℝ) * Real.exp (1 : ℝ) = Real.exp 2 := by
    rw [← Real.exp_add]; norm_num
  have e4 : Real.exp (2 : ℝ) * Real.exp (2 : ℝ) = Real.exp 4 := by
    rw [← Real.exp_add]; norm_num
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by nlinarith [h1, e2]
  have h4 : (16 : ℝ) ≤ Real.exp 4 := by nlinarith [h2, e4]
  have hmul : Real.exp (-4 : ℝ) * Real.exp (4 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [hmul, h4, Real.exp_pos (-4 : ℝ), Real.exp_pos (4 : ℝ)]

set_option maxHeartbeats 1000000 in
theorem gprincipal_lower (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) →
        1 / (5 * Real.sqrt (GS2 a b c p q x))
          ≤ ∫ t in (0 : ℝ)..(gt₁ a b c p q x),
              (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
                * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
  obtain ⟨cV, hcV, X₁, hX₁⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  set M : ℝ := 5 + Real.pi * p / cV + 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 / cV ^ 2 with hMdef
  obtain ⟨X₂, hX₂⟩ := gT_eventually_ge M
  refine ⟨max (max X₁ X₂) 2, fun x hx n hn => ?_⟩
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  set T : ℝ := gT x with hTdef
  set V : ℝ := Real.sqrt (GS2 a b c p q x) with hVdef
  set L : ℝ := Real.log x with hLdef
  have hTM : M ≤ T := hX₂ x hxX₂
  have hMnn1 : (0 : ℝ) ≤ Real.pi * p / cV := div_nonneg (by positivity) hcV.le
  have hMnn2 : (0 : ℝ) ≤ 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 / cV ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg cV)
  have hT5 : (5 : ℝ) ≤ T := by rw [hMdef] at hTM; linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := hTpos.ne'
  have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < L := by
    rw [hLdef]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hxR
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hT4 : T ^ 4 = L := gT_pow_four (by omega)
  have hVlow : cV * (x : ℝ) * L ≤ V := hX₁ x hxX₁
  have hWpos : (0 : ℝ) < cV * (x : ℝ) * L := mul_pos (mul_pos hcV hxpos) hLpos
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le hWpos hVlow
  have hVne : V ≠ 0 := hVpos.ne'
  have hS2eq : ((GS2 a b c p q x : ℕ) : ℝ) = V ^ 2 := by
    rw [hVdef, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hT3 : T ≤ T ^ 3 := by
    have h1 : (1 : ℝ) ≤ T := by linarith
    have h2 : (1 : ℝ) ≤ T ^ 2 := by nlinarith [h1]
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * T ^ 2 := mul_le_mul_of_nonneg_left h2 hTpos.le
      _ = T ^ 3 := by ring

  have hcube1 : Real.pi * (p : ℝ) ≤ cV * T ^ 3 := by
    have h1 : Real.pi * (p : ℝ) / cV ≤ T := by rw [hMdef] at hTM; linarith
    have h2 : Real.pi * (p : ℝ) ≤ cV * T := by rw [div_le_iff₀ hcV] at h1; linarith
    calc Real.pi * (p : ℝ) ≤ cV * T := h2
      _ ≤ cV * T ^ 3 := mul_le_mul_of_nonneg_left hT3 hcV.le

  have hcube2 : 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ cV ^ 2 * T ^ 3 := by
    have h1 : 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 / cV ^ 2 ≤ T := by
      rw [hMdef] at hTM; linarith
    have h2 : 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ cV ^ 2 * T := by
      rw [div_le_iff₀ (pow_pos hcV 2)] at h1; linarith
    calc 100 * Real.pi ^ 4 * (p : ℝ) ^ 2 ≤ cV ^ 2 * T := h2
      _ ≤ cV ^ 2 * T ^ 3 := mul_le_mul_of_nonneg_left hT3 (pow_pos hcV 2).le
  have hπT : (45 : ℝ) ≤ Real.pi ^ 2 * T := by nlinarith [hpi9, hT5]

  have hθ : ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) ^ 2 ≤ V ^ 2 := by
    have hcast : (2 * (n : ℝ) - (GS1 a b c p q x : ℝ)) ^ 2
        ≤ ((GS2 a b c p q x : ℕ) : ℝ) := by exact_mod_cast hn
    rw [hS2eq] at hcast
    calc ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) ^ 2
        = (2 * (n : ℝ) - (GS1 a b c p q x : ℝ)) ^ 2 := by ring
      _ ≤ V ^ 2 := hcast

  have hsmall : ∀ t : ℝ, 0 ≤ t → t ≤ T / V → ∀ s ∈ GBand a b c p q x,
      |Real.pi * ((s : ℝ) * t)| ≤ 1 := by
    intro t ht0 htt s hs
    have hsle : (s : ℝ) ≤ (p : ℝ) * (x : ℝ) := by exact_mod_cast gband_le hq hs
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    rw [abs_of_nonneg (mul_nonneg hpi.le (mul_nonneg hs0 ht0))]
    have hkey : Real.pi * ((p : ℝ) * (x : ℝ)) * T ≤ V := by
      have h1 : Real.pi * ((p : ℝ) * (x : ℝ)) * T ≤ cV * (x : ℝ) * L := by
        rw [← hT4]
        nlinarith [mul_le_mul_of_nonneg_right hcube1
          (mul_nonneg hxpos.le hTpos.le)]
      linarith
    have h3 : Real.pi * ((p : ℝ) * (x : ℝ)) * (T / V) ≤ 1 := by
      rw [show Real.pi * ((p : ℝ) * (x : ℝ)) * (T / V)
          = (Real.pi * ((p : ℝ) * (x : ℝ)) * T) / V by ring, div_le_one hVpos]
      exact hkey
    have h2 : (s : ℝ) * t ≤ ((p : ℝ) * (x : ℝ)) * (T / V) :=
      mul_le_mul hsle htt ht0 (by positivity)
    calc Real.pi * ((s : ℝ) * t)
        ≤ Real.pi * (((p : ℝ) * (x : ℝ)) * (T / V)) :=
          mul_le_mul_of_nonneg_left h2 hpi.le
      _ ≤ 1 := by linarith [h3]

  set E : ℝ := Real.pi ^ 4 * (T / V) ^ 4
      * (((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ)) with hEdef
  have hEnn : (0 : ℝ) ≤ E := by rw [hEdef]; positivity
  have hbnd : ∀ t ∈ Set.Icc (0 : ℝ) (T / V),
      |(∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        - Real.exp (-(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2))| ≤ E := by
    intro t ht
    obtain ⟨ht0, htt⟩ := ht

    have happ : |(∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          - Real.exp (-((∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 2) / 2))|
        ≤ ∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 4 :=
      abs_prod_cos_sub_exp_le (GBand a b c p q x)
        (fun s => Real.pi * ((s : ℝ) * t)) (fun s hs => hsmall t ht0 htt s hs)
    have hsum2 : (∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 2)
        = Real.pi ^ 2 * (((GS2 a b c p q x : ℕ) : ℝ) * t ^ 2) := by
      rw [← gsum_sq_band a b c p q x t, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hexpeq : -((∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 2) / 2)
        = -(Real.pi ^ 2 * V ^ 2 / 2 * t ^ 2) := by rw [hsum2, hS2eq]; ring
    rw [hexpeq] at happ
    refine happ.trans ?_
    have hsum4 : (∑ s ∈ GBand a b c p q x, (Real.pi * ((s : ℝ) * t)) ^ 4)
        = Real.pi ^ 4 * t ^ 4 * (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have h4 : (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4)
        ≤ ((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ) := gS4_le hq x
    have ht4 : t ^ 4 ≤ (T / V) ^ 4 := pow_le_pow_left₀ ht0 htt 4
    rw [hsum4, hEdef]
    calc Real.pi ^ 4 * t ^ 4 * (∑ s ∈ GBand a b c p q x, (s : ℝ) ^ 4)
        ≤ Real.pi ^ 4 * t ^ 4 * (((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ Real.pi ^ 4 * (T / V) ^ 4
            * (((p : ℝ) * (x : ℝ)) ^ 2 * ((GS2 a b c p q x : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ht4 (by positivity)) (by positivity)

  have hkey2 : 100 * (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2) ≤ V ^ 2 := by
    calc 100 * (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2)
        = (100 * Real.pi ^ 4 * (p : ℝ) ^ 2) * (T ^ 5 * (x : ℝ) ^ 2) := by ring
      _ ≤ (cV ^ 2 * T ^ 3) * (T ^ 5 * (x : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcube2
            (mul_nonneg (pow_nonneg hTpos.le 5) (sq_nonneg _))
      _ = cV ^ 2 * (x : ℝ) ^ 2 * T ^ 8 := by ring
      _ = (cV * (x : ℝ) * L) ^ 2 := by rw [← hT4]; ring
      _ ≤ V ^ 2 := pow_le_pow_left₀ hWpos.le hVlow 2
  have hDerr : (T / V) * E ≤ (1 / 100) * (1 / V) := by
    have hE' : (T / V) * E = (Real.pi ^ 4 * T ^ 5 * ((p : ℝ) * (x : ℝ)) ^ 2) / V ^ 3 := by
      rw [hEdef, hS2eq]; field_simp; try ring
    rw [hE', div_le_iff₀ (pow_pos hVpos 3)]
    have hrw : (1 / 100 : ℝ) * (1 / V) * V ^ 3 = V ^ 2 / 100 := by field_simp; try ring
    rw [hrw]
    linarith [hkey2]

  have hTail : 2 * Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) / (Real.pi ^ 2 * V * T)
      ≤ (1 / 100) * (1 / V) := by
    have h1 : Real.exp (-(Real.pi ^ 2 * T ^ 2 / 2)) ≤ 1 / 16 := by
      refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_four_le
      nlinarith [hpi9, hT5]
    rw [div_le_iff₀ (mul_pos (mul_pos (pow_pos hpi 2) hVpos) hTpos)]
    have hrw : (1 / 100 : ℝ) * (1 / V) * (Real.pi ^ 2 * V * T) = Real.pi ^ 2 * T / 100 := by
      field_simp; try ring
    rw [hrw]
    linarith [h1, hπT]

  have habs := gprincipal_abstract
    (φ := fun t => ∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
    (V := V) (θ := (GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) (T := T) (E := E)
    (by fun_prop) hVpos hTpos hθ hEnn hbnd
  have hgt : gt₁ a b c p q x = T / V := by simp only [gt₁, hTdef, hVdef]
  have hgoal_eq : (∫ t in (0 : ℝ)..(gt₁ a b c p q x),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
      = ∫ t in (0 : ℝ)..(T / V),
        (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
          * Real.cos (Real.pi * ((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t) := by
    rw [hgt]
    exact intervalIntegral.integral_congr (fun t _ => by rw [mul_assoc])
  rw [hgoal_eq]
  refine le_trans ?_ habs
  have hconst : (23 / 100 : ℝ) * (1 / V)
      ≤ Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V) := by
    rw [show Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / (2 * V)
        = (Real.sqrt (2 / Real.pi) * Real.exp (-(1 / 2)) / 2) * (1 / V) by ring]
    exact mul_le_mul_of_nonneg_right gauss_const_ge (one_div_nonneg.mpr hVpos.le)
  have hfin : (1 : ℝ) / (5 * V) = (1 / 5) * (1 / V) := by field_simp; try ring
  rw [hfin]
  linarith [hconst, hDerr, hTail, one_div_pos.mpr hVpos]

end

end Erdos123Band
end Module_GPrincipal

section Module_GTail

open MeasureTheory

namespace Erdos123Band

noncomputable section

set_option maxHeartbeats 1000000 in
lemma gnarrow_ratio {a b c p q : ℕ} (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) (hd2 : 2 ≤ min a (min b c)) :
    ∃ p' q' : ℕ, 0 < q' ∧ q' < p' ∧ p' < q' * min a (min b c) ∧ 2 * p' ≤ 3 * q' ∧
      ∀ x : ℕ, GBand a b c p' q' x ⊆ GBand a b c p q x := by
  by_cases h : 2 * p ≤ 3 * q
  · exact ⟨p, q, hq, hqp, hpd, h, fun x => Finset.Subset.refl _⟩
  · push_neg at h
    refine ⟨3, 2, by norm_num, by norm_num, ?_, by norm_num, fun x s hs => ?_⟩
    · omega
    · obtain ⟨hS, hx, hw⟩ := of_mem_GBand hs
      refine (mem_GBand hq).mpr ⟨hS, hx, ?_⟩
      have hx0 : 0 < x := by omega
      have h1 : 2 * (q * s) < 3 * (q * x) := by
        calc 2 * (q * s) = q * (2 * s) := by ring
          _ < q * (3 * x) := mul_lt_mul_of_pos_left hw hq
          _ = 3 * (q * x) := by ring
      have h2 : 3 * (q * x) < 2 * (p * x) := by
        calc 3 * (q * x) = 3 * q * x := by ring
          _ < 2 * p * x := mul_lt_mul_of_pos_right h hx0
          _ = 2 * (p * x) := by ring
      omega

set_option maxHeartbeats 1000000 in
lemma gband_lt_two_mul {a b c p' q' x s : ℕ} (hq' : 0 < q') (hnarrow : 2 * p' ≤ 3 * q')
    (hs : s ∈ GBand a b c p' q' x) : 2 * s < 3 * x := by
  obtain ⟨-, -, hw⟩ := of_mem_GBand hs
  have h1 : q' * (2 * s) < q' * (3 * x) := by
    calc q' * (2 * s) = 2 * (q' * s) := by ring
      _ < 2 * (p' * x) := by omega
      _ = 2 * p' * x := by ring
      _ ≤ 3 * q' * x := Nat.mul_le_mul_right x hnarrow
      _ = q' * (3 * x) := by ring
  exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)

set_option maxHeartbeats 1000000 in
lemma gband_lt_d_mul {a b c p q x s : ℕ} (hq : 0 < q) (hpd : p < q * min a (min b c))
    (hs : s ∈ GBand a b c p q x) : s < min a (min b c) * x := by
  obtain ⟨-, -, hw⟩ := of_mem_GBand hs
  have h1 : q * s < q * (min a (min b c) * x) := by
    calc q * s < p * x := hw
      _ ≤ q * min a (min b c) * x := Nat.mul_le_mul_right x (le_of_lt hpd)
      _ = q * (min a (min b c) * x) := by ring
  exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)

set_option maxHeartbeats 1000000 in
theorem gvery_low_sharp (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ κ₀ δ : ℝ, ∃ X₅ : ℕ, 0 < κ₀ ∧ 0 < δ ∧
      δ * ((min a (min b c) : ℕ) : ℝ) ≤ 1 / 8 ∧ ∀ x : ℕ, X₅ ≤ x → ∀ t : ℝ,
        GQenergy a b c p q x t < κ₀ * Real.log x → ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ) := by
  classical
  have hd2 : 2 ≤ min a (min b c) := by simp only [le_min_iff]; omega
  obtain ⟨p', q', hq', hq'p', hp'd, hnarrow, hsub⟩ := gnarrow_ratio hq hqp hpd hd2
  obtain ⟨κ₀, δ₀, X₅, hκ₀, hδ₀, hδ₀32, hvl⟩ := gvery_low a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨c₁, hc₁, X₁, hcard⟩ := gband_card_ge_sq a b c p' q' ha hb hc hco hq' hq'p' hp'd
  set d : ℕ := min a (min b c) with hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  set δ : ℝ := min (1 / 32) (1 / (8 * (d : ℝ))) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδd : δ * (d : ℝ) ≤ 1 / 8 := by
    have h1 : δ ≤ 1 / (8 * (d : ℝ)) := min_le_right _ _
    have h2 : δ * (d : ℝ) ≤ (1 / (8 * (d : ℝ))) * (d : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hdR.le
    calc δ * (d : ℝ) ≤ (1 / (8 * (d : ℝ))) * (d : ℝ) := h2
      _ = 1 / 8 := by field_simp

  have hlogtop : Filter.Tendsto (fun x : ℕ => Real.log x) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₃, hX₃⟩ := Filter.eventually_atTop.mp
    (hlogtop.eventually_ge_atTop (max (κ₀ / (c₁ * δ ^ 2)) 1))
  refine ⟨κ₀, δ, max (max X₅ X₁) (max X₃ 2), hκ₀, hδpos, hδd, fun x hx t hQ => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxX₅, hxX₁⟩, hxX₃, hx2⟩ := hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hLbig := hX₃ x hxX₃
  rw [max_le_iff] at hLbig
  obtain ⟨hLratio, hL1⟩ := hLbig
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  obtain ⟨r, hr⟩ := hvl x hxX₅ t hQ
  refine ⟨r, ?_⟩
  set u : ℝ := t - (r : ℝ) with hu

  have hshift : ∀ s : ℕ, (s : ℝ) * t - (round ((s : ℝ) * t) : ℝ)
      = (s : ℝ) * u - (round ((s : ℝ) * u) : ℝ) := by
    intro s
    have he : (s : ℝ) * t = (s : ℝ) * u + ((s * r : ℤ) : ℝ) := by
      rw [hu]; push_cast; ring
    rw [he, round_add_intCast]
    push_cast; ring
  have hQu : GQenergy a b c p q x t
      = ∑ s ∈ GBand a b c p q x, ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2 := by
    unfold GQenergy
    exact Finset.sum_congr rfl (fun s _ => by rw [hshift s])
  have hu32 : |u| ≤ (1 / 32) / (x : ℝ) := hr.trans (by gcongr)

  have hkey : ∀ s ∈ GBand a b c p' q' x,
      ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2 = ((s : ℝ) * u) ^ 2 := by
    intro s hs
    have h2s : 2 * s < 3 * x := gband_lt_two_mul hq' hnarrow hs
    have hsR : (s : ℝ) ≤ 2 * (x : ℝ) := by
      have : s ≤ 2 * x := by omega
      exact_mod_cast this
    have hsu : |(s : ℝ) * u| < 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ))]
      have h1 : (s : ℝ) * |u| ≤ (2 * (x : ℝ)) * ((1 / 32) / (x : ℝ)) :=
        mul_le_mul hsR hu32 (abs_nonneg _) (by positivity)
      have h2 : (2 * (x : ℝ)) * ((1 / 32) / (x : ℝ)) = 1 / 16 := by field_simp; ring
      linarith [h1, h2.le, h2.ge]
    have hround : round ((s : ℝ) * u) = 0 := by
      rw [round_eq_zero_iff, Set.mem_Ico]
      constructor
      · linarith [neg_abs_le ((s : ℝ) * u)]
      · linarith [le_abs_self ((s : ℝ) * u)]
    rw [hround]
    push_cast; ring

  have hbig : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2) ≤ GQenergy a b c p q x t := by
    have hstep1 : ∑ s ∈ GBand a b c p' q' x,
          ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2
        ≤ GQenergy a b c p q x t := by
      rw [hQu]
      exact Finset.sum_le_sum_of_subset_of_nonneg (hsub x) (fun s _ _ => sq_nonneg _)
    have hstep2 : ((GBand a b c p' q' x).card : ℝ) * ((x : ℝ) ^ 2 * u ^ 2)
        ≤ ∑ s ∈ GBand a b c p' q' x, ((s : ℝ) * u - (round ((s : ℝ) * u) : ℝ)) ^ 2 := by
      rw [Finset.sum_congr rfl hkey]
      calc ((GBand a b c p' q' x).card : ℝ) * ((x : ℝ) ^ 2 * u ^ 2)
          = ∑ _s ∈ GBand a b c p' q' x, ((x : ℝ) ^ 2 * u ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ s ∈ GBand a b c p' q' x, ((s : ℝ) * u) ^ 2 := by
            refine Finset.sum_le_sum (fun s hs => ?_)
            have hxs : (x : ℝ) ≤ (s : ℝ) := by exact_mod_cast (of_mem_GBand hs).2.1
            have hsq : (x : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by nlinarith [hxpos.le]
            nlinarith [sq_nonneg u]
    have hstep3 : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2)
        ≤ ((GBand a b c p' q' x).card : ℝ) * ((x : ℝ) ^ 2 * u ^ 2) := by
      refine mul_le_mul_of_nonneg_right (hcard x hxX₁) (by positivity)
    linarith

  have hu2 : u ^ 2 ≤ (δ / (x : ℝ)) ^ 2 := by
    have h1 : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2) < κ₀ * Real.log x := by linarith
    have h2 : κ₀ ≤ c₁ * δ ^ 2 * Real.log x := by
      rw [div_le_iff₀ (by positivity)] at hLratio
      linarith
    have h3 : c₁ * Real.log x ^ 2 * ((x : ℝ) ^ 2 * u ^ 2)
        < c₁ * δ ^ 2 * Real.log x * Real.log x := by nlinarith
    have h4 : (x : ℝ) ^ 2 * u ^ 2 ≤ δ ^ 2 := by
      nlinarith [hLpos, hc₁, mul_pos hc₁ (pow_pos hLpos 2)]
    rw [div_pow]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rcases abs_cases u with ⟨he, hnn⟩ | ⟨he, hnn⟩
  · rw [he]; nlinarith [hu2, div_pos hδpos hxpos]
  · rw [he]; nlinarith [hu2, div_pos hδpos hxpos]

set_option maxHeartbeats 1000000 in
lemma gexp_integral_le_on (a b c p q x : ℕ) {κ₀ Mbound : ℝ} {S : Set ℝ}
    (hSm : MeasurableSet S) (hSsub : S ⊆ Set.Ioc (0 : ℝ) 1)
    (hfloor : ∀ t ∈ S, κ₀ * Real.log x ≤ GQenergy a b c p q x t)
    (hmeas : (volume {t : ℝ | t ∈ S ∧ GQenergy a b c p q x t ≤ Real.log x}).toReal ≤ Mbound) :
    (∫ t in S, Real.exp (-(2 * GQenergy a b c p q x t)))
      ≤ Real.exp (-(2 * κ₀ * Real.log x)) * Mbound + Real.exp (-(2 * Real.log x)) := by
  have hmeasQ : MeasurableSet {t : ℝ | GQenergy a b c p q x t ≤ Real.log x} :=
    measurableSet_le (GQenergy_measurable a b c p q x) measurable_const
  have hInt : IntegrableOn (fun t => Real.exp (-(2 * GQenergy a b c p q x t))) S volume :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (gexp_neg_two_Q_intervalIntegrable a b c p q x 0 1))).mono_set hSsub
  have hvolIoc : volume (Set.Ioc (0 : ℝ) 1) < ⊤ := by rw [Real.volume_Ioc]; simp
  have hfin : ∀ U : Set ℝ, U ⊆ S → volume U < ⊤ := fun U hU =>
    lt_of_le_of_lt (measure_mono (hU.trans hSsub)) hvolIoc
  rw [← MeasureTheory.integral_inter_add_sdiff hmeasQ hInt]
  refine add_le_add ?_ ?_
  · have hsetle : (∫ t in S ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in S ∩ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * κ₀ * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.inter_subset_left)
        (MeasureTheory.integrableOn_const (hfin _ Set.inter_subset_left).ne)
        (hSm.inter hmeasQ) (fun t ht => ?_)
      exact Real.exp_le_exp.mpr (by linarith [hfloor t ht.1])
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    rw [show S ∩ {t | GQenergy a b c p q x t ≤ Real.log x}
        = {t : ℝ | t ∈ S ∧ GQenergy a b c p q x t ≤ Real.log x} from by
      ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]]
    exact hmeas
  · have hsetle : (∫ t in S \ {t | GQenergy a b c p q x t ≤ Real.log x},
          Real.exp (-(2 * GQenergy a b c p q x t)))
        ≤ ∫ _t in S \ {t | GQenergy a b c p q x t ≤ Real.log x},
            Real.exp (-(2 * Real.log x)) := by
      refine MeasureTheory.setIntegral_mono_on (hInt.mono_set Set.diff_subset)
        (MeasureTheory.integrableOn_const (hfin _ Set.diff_subset).ne)
        (hSm.diff hmeasQ) (fun t ht => ?_)
      have hQ : Real.log x < GQenergy a b c p q x t := by
        have h2 := ht.2; simp only [Set.mem_setOf_eq, not_le] at h2; exact h2
      exact Real.exp_le_exp.mpr (by linarith)
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hsetle
    refine hsetle.trans ?_
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)).trans (le_of_eq (mul_one _))
    calc (volume (S \ {t | GQenergy a b c p q x t ≤ Real.log x})).toReal
        ≤ (volume (Set.Ioc (0 : ℝ) 1)).toReal :=
          ENNReal.toReal_mono hvolIoc.ne (measure_mono (Set.diff_subset.trans hSsub))
      _ = 1 := by rw [Real.volume_Ioc]; simp

set_option maxHeartbeats 1000000 in
lemma gQenergy_eq_of_small {a b c p q x : ℕ} (hq : 0 < q) (hpd : p < q * min a (min b c))
    {t : ℝ} (ht0 : 0 ≤ t) (hsmall : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t ≤ 1 / 4) :
    GQenergy a b c p q x t = (GS2 a b c p q x : ℝ) * t ^ 2 := by
  rw [GQenergy, ← gsum_sq_band a b c p q x t]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hslt : (s : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) := by
    have := gband_lt_d_mul hq hpd hs
    have h2 : (s : ℝ) ≤ ((min a (min b c) * x : ℕ) : ℝ) := by exact_mod_cast this.le
    rwa [Nat.cast_mul] at h2
  have hst : 0 ≤ (s : ℝ) * t := mul_nonneg (by positivity) ht0
  have hst2 : (s : ℝ) * t ≤ 1 / 4 := by
    refine le_trans (mul_le_mul_of_nonneg_right hslt ht0) ?_
    linarith [hsmall]
  have hround : round ((s : ℝ) * t) = 0 := by
    rw [round_eq_zero_iff, Set.mem_Ico]
    constructor <;> linarith
  rw [hround]
  push_cast; ring

set_option maxHeartbeats 1000000 in
lemma gintegrand_abs_le (a b c p q x n : ℕ) (t : ℝ) :
    |(∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))|
      ≤ Real.exp (-(2 * GQenergy a b c p q x t)) := by
  refine le_trans ?_ (gchi_le_exp_neg_two_Q a b c p q x t)
  rw [GchiBand, ← Finset.abs_prod, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

set_option maxHeartbeats 1000000 in
lemma gintegrand_continuous (a b c p q x n : ℕ) :
    Continuous (fun t : ℝ => (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
      * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))) := by
  fun_prop

set_option maxHeartbeats 1000000 in
lemma gintermediate_upper (a b c p q : ℕ) (hq : 0 < q) (hpd : p < q * min a (min b c))
    {δ : ℝ} (hδ : 0 < δ) (hδd : δ * ((min a (min b c) : ℕ) : ℝ) ≤ 1 / 8)
    (x : ℕ) (hx : 0 < x) {F : ℝ → ℝ} (hFcont : Continuous F)
    (hFabs : ∀ t : ℝ, |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)))
    (hVpos : 0 < Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
    (hT2 : (2 : ℝ) ≤ gT x)
    (h12 : gt₁ a b c p q x ≤ 2 * δ / (x : ℝ)) :
    |∫ t in (gt₁ a b c p q x)..(2 * δ / (x : ℝ)), F t|
      ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  set V : ℝ := Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) with hVdef
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hV2 : V ^ 2 = ((GS2 a b c p q x : ℕ) : ℝ) := by
    rw [hVdef]; exact Real.sq_sqrt (by positivity)
  set T : ℝ := gT x with hTdef
  have hTpos : (0 : ℝ) < T := by linarith
  set t₁ : ℝ := gt₁ a b c p q x with ht₁def
  have ht₁eq : t₁ = T / V := by rw [ht₁def, hTdef, hVdef, gt₁]
  have ht₁pos : 0 < t₁ := by rw [ht₁eq]; positivity
  set t₂ : ℝ := 2 * δ / (x : ℝ) with ht₂def
  have hFabsInt : ∀ u v : ℝ, IntervalIntegrable (fun t => |F t|) volume u v :=
    fun u v => (hFcont.abs).intervalIntegrable u v
  set A : ℝ := 2 * ((GS2 a b c p q x : ℕ) : ℝ) with hAdef
  have hApos : 0 < A := by rw [hAdef]; nlinarith [hV2, hVpos]
  have hgi : MeasureTheory.Integrable (fun u : ℝ => Real.exp (-(A * u ^ 2))) := by
    have := gaussian_integrable_scaled hApos 0
    simpa using this
  have hstep1 : |∫ t in t₁..t₂, F t| ≤ ∫ t in t₁..t₂, |F t| := by
    have := intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := volume) h12
    simpa only [Real.norm_eq_abs] using this
  have hstep2 : (∫ t in t₁..t₂, |F t|) ≤ ∫ t in t₁..t₂, Real.exp (-(A * t ^ 2)) := by
    refine intervalIntegral.integral_mono_on h12 (hFabsInt t₁ t₂)
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(A * t ^ 2))).intervalIntegrable _ _)
      (fun t ht => ?_)
    have htpos : 0 ≤ t := le_trans ht₁pos.le ht.1
    have hQ : GQenergy a b c p q x t = ((GS2 a b c p q x : ℕ) : ℝ) * t ^ 2 := by
      refine gQenergy_eq_of_small hq hpd htpos ?_
      have hdx0 : (0 : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) := by positivity
      have h1 : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t
          ≤ ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t₂ := by nlinarith [ht.2]
      have h2 : ((min a (min b c) : ℕ) : ℝ) * (x : ℝ) * t₂
          = ((min a (min b c) : ℕ) : ℝ) * (2 * δ) := by
        rw [ht₂def]; field_simp
      nlinarith [h1, h2, hδd]
    calc |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)) := hFabs t
      _ = Real.exp (-(A * t ^ 2)) := by rw [hQ, hAdef]; congr 1; ring
  have hstep3 : (∫ t in t₁..t₂, Real.exp (-(A * t ^ 2)))
      ≤ ∫ t in Set.Ioi t₁, Real.exp (-(A * t ^ 2)) := by
    rw [intervalIntegral.integral_of_le h12]
    refine MeasureTheory.setIntegral_mono_set hgi.integrableOn ?_
      (HasSubset.Subset.eventuallyLE Set.Ioc_subset_Ioi_self)
    filter_upwards with t using Real.exp_nonneg _
  have hstep4 := gauss_tail_Ioi hApos ht₁pos
  have hAt1 : A * t₁ ^ 2 = 2 * T ^ 2 := by rw [hAdef, ht₁eq, ← hV2]; field_simp
  have hAt1' : A * t₁ = 2 * V * T := by rw [hAdef, ht₁eq, ← hV2]; field_simp
  have hfin : Real.exp (-(A * t₁ ^ 2)) / (A * t₁) ≤ 1 / (20 * V) := by
    rw [hAt1, hAt1']
    have h1 : 2 * T ^ 2 ≤ Real.exp (2 * T ^ 2) := by
      linarith [Real.add_one_le_exp (2 * T ^ 2)]
    have h2 : (2 * T ^ 2) * Real.exp (-(2 * T ^ 2)) ≤ 1 := by
      have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-(2 * T ^ 2)))
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
    have hT3 : (8 : ℝ) ≤ T ^ 3 := by
      nlinarith [hT2, hTpos, sq_nonneg (T - 2), sq_nonneg T]
    have h5 : 10 * Real.exp (-(2 * T ^ 2)) ≤ T := by
      have hT2pos : (0 : ℝ) < 2 * T ^ 2 := by positivity
      rw [← sub_nonneg]
      have h6 : T - 10 * Real.exp (-(2 * T ^ 2))
          = (T * (2 * T ^ 2) - 10 * ((2 * T ^ 2) * Real.exp (-(2 * T ^ 2)))) / (2 * T ^ 2) := by
        field_simp
      rw [h6]
      refine div_nonneg ?_ hT2pos.le
      nlinarith [h2, hT3]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 2 * V by linarith)]
  linarith [hstep1, hstep2, hstep3, hstep4, hfin]

set_option maxHeartbeats 1000000 in
lemma gminor_upper (a b c p q : ℕ) {κ₀ δ : ℝ} {C₄ : ℕ} (x : ℕ) (hx1 : 1 ≤ x)
    (hδ : 0 < δ) (hδ16 : δ ≤ 1 / 16) (hL1 : (1 : ℝ) ≤ Real.log x)
    {F : ℝ → ℝ} (hFcont : Continuous F)
    (hFabs : ∀ t : ℝ, |F t| ≤ Real.exp (-(2 * GQenergy a b c p q x t)))
    (hvl : ∀ t : ℝ, GQenergy a b c p q x t < κ₀ * Real.log x →
      ∃ r : ℤ, |t - (r : ℝ)| ≤ δ / (x : ℝ))
    (hmeasx : volume {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x}
      ≤ ENNReal.ofReal (1 / (x : ℝ) * Real.log x ^ C₄))
    (hnum : Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
        + Real.exp (-(2 * Real.log x)) ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))) :
    |∫ t in (2 * δ / (x : ℝ))..(1 / 2), F t|
      ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  set t₂ : ℝ := 2 * δ / (x : ℝ) with ht₂def
  have ht₂pos : 0 < t₂ := by rw [ht₂def]; positivity
  have ht₂half : t₂ ≤ 1 / 2 := by
    rw [ht₂def, div_le_iff₀ hxpos]; nlinarith [hδ16, hx1R]
  have hstep1 : |∫ t in t₂..(1 / 2), F t| ≤ ∫ t in t₂..(1 / 2), |F t| := by
    have := intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := volume) ht₂half
    simpa only [Real.norm_eq_abs] using this
  have hstep2 : (∫ t in t₂..(1 / 2), |F t|)
      ≤ ∫ t in t₂..(1 / 2), Real.exp (-(2 * GQenergy a b c p q x t)) :=
    intervalIntegral.integral_mono_on ht₂half ((hFcont.abs).intervalIntegrable _ _)
      (gexp_neg_two_Q_intervalIntegrable a b c p q x t₂ (1 / 2)) (fun t _ => hFabs t)
  have hdx : δ / (x : ℝ) ≤ 1 / 16 := by
    rw [div_le_iff₀ hxpos]; nlinarith [hδ16, hx1R]
  have hfloor : ∀ t ∈ Set.Ioc t₂ (1 / 2 : ℝ), κ₀ * Real.log x ≤ GQenergy a b c p q x t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr⟩ := hvl t hcon
    have htpos : 0 < t := lt_trans ht₂pos ht.1
    have hhalf : δ / (x : ℝ) < t₂ := by
      have heq : t₂ - δ / (x : ℝ) = δ / (x : ℝ) := by rw [ht₂def]; field_simp; norm_num
      have hpos : 0 < δ / (x : ℝ) := div_pos hδ hxpos
      linarith
    have hcontr : δ / (x : ℝ) < |t - (r : ℝ)| := by
      rcases le_or_gt 1 r with h | h
      · have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.2, hdx]
      · rcases le_or_gt r (-1) with h' | h'
        · have hrR : ((r : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h'
          rw [abs_of_nonneg (by linarith)]
          linarith [hdx]
        · have hr0 : r = 0 := by omega
          subst hr0
          rw [Int.cast_zero, sub_zero, abs_of_pos htpos]
          linarith [ht.1, hhalf]
    linarith [hr, hcontr]
  have hSsub : Set.Ioc t₂ (1 / 2 : ℝ) ⊆ Set.Ioc (0 : ℝ) 1 :=
    fun t ht => ⟨lt_trans ht₂pos ht.1, by linarith [ht.2]⟩
  have hmeasS : (volume {t : ℝ | t ∈ Set.Ioc t₂ (1 / 2 : ℝ) ∧
      GQenergy a b c p q x t ≤ Real.log x}).toReal ≤ 1 / (x : ℝ) * Real.log x ^ C₄ := by
    have hsub : {t : ℝ | t ∈ Set.Ioc t₂ (1 / 2 : ℝ) ∧ GQenergy a b c p q x t ≤ Real.log x}
        ⊆ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ GQenergy a b c p q x t ≤ Real.log x} := by
      rintro t ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith [ht₂pos], by linarith⟩, h3⟩
    have hle := (measure_mono hsub).trans hmeasx
    have hnn : (0 : ℝ) ≤ 1 / (x : ℝ) * Real.log x ^ C₄ :=
      mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal hnn)
  have hmain := gexp_integral_le_on a b c p q x measurableSet_Ioc hSsub hfloor hmeasS
  rw [← intervalIntegral.integral_of_le ht₂half] at hmain
  linarith [hstep1, hstep2, hmain, hnum]

set_option maxHeartbeats 1000000 in
theorem gtail_upper (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |∫ t in (gt₁ a b c p q x)..(1 / 2),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))|
        ≤ 1 / (10 * Real.sqrt (GS2 a b c p q x)) := by
  classical
  obtain ⟨κ₀, δ, X₅, hκ₀, hδ, hδd, hvl⟩ := gvery_low_sharp a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨C₄, hC₄, X₂, hmeasx⟩ := glow_energy_measure a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨CV, hCV, X₆, hVup⟩ := gV_upper a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨cV, hcV, X₇, hVlow⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  have hd2 : 2 ≤ min a (min b c) := by simp only [le_min_iff]; omega
  have hdR2 : (2 : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) := by exact_mod_cast hd2
  have hδ16 : δ ≤ 1 / 16 := by nlinarith [hδd, hdR2, hδ]

  have hlogtop : Filter.Tendsto (fun x : ℕ => Real.log x) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Xa, hXa⟩ := Filter.eventually_atTop.mp
    (hlogtop.eventually_ge_atTop (max 16 ((1 / (2 * δ * cV)) ^ 2)))
  have hgrow : Filter.Tendsto
      (fun y : ℝ => 20 * CV * Real.log y ^ ((1 : ℝ) + (C₄ : ℝ)) * y ^ (-(2 * κ₀))
        + 20 * CV * Real.log y * y ^ (-(1 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 := poly_log_rpow_tendsto (p := (1 : ℝ) + (C₄ : ℝ)) (q := 2 * κ₀) (by linarith)
    have h2 := poly_log_rpow_tendsto (p := (1 : ℝ)) (q := (1 : ℝ)) (by norm_num)
    have hsum := (h1.const_mul (20 * CV)).add (h2.const_mul (20 * CV))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr (fun y => ?_)
    rw [Real.rpow_one]
    ring
  obtain ⟨Xb, hXb⟩ := Filter.eventually_atTop.mp
    ((hgrow.comp tendsto_natCast_atTop_atTop).eventually_lt_const (show (0 : ℝ) < 1 by norm_num))
  refine ⟨max (max (max X₅ X₂) (max X₆ X₇)) (max (max Xa Xb) 2), fun x hx n => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hxX₅, hxX₂⟩, hxX₆, hxX₇⟩, ⟨hxXa, hxXb⟩, hx2⟩ := hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hLbig := hXa x hxXa
  rw [max_le_iff] at hLbig
  obtain ⟨hL16, hLB⟩ := hLbig
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith

  have hVge : cV * (x : ℝ) * Real.log x ≤ Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) :=
    hVlow x hxX₇
  have hVpos : 0 < Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos hcV hxpos) hLpos) hVge
  have hVle : Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) ≤ CV * (x : ℝ) * Real.log x :=
    hVup x hxX₆
  have h20V : (0 : ℝ) < 20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) := by linarith

  have hsq16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsL4 : (4 : ℝ) ≤ Real.sqrt (Real.log x) := by
    have h := Real.sqrt_le_sqrt hL16; rwa [hsq16] at h
  have hT2 : (2 : ℝ) ≤ gT x := by
    unfold gT
    have h := Real.sqrt_le_sqrt hsL4; rwa [hsq4] at h
  have hTle : gT x ≤ Real.sqrt (Real.log x) := by
    unfold gT
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (Real.log x)),
      Real.sqrt_nonneg (Real.sqrt (Real.log x)), hsL4,
      sq_nonneg (Real.sqrt (Real.sqrt (Real.log x)) - 2)]

  have h12 : gt₁ a b c p q x ≤ 2 * δ / (x : ℝ) := by
    have hp : (0 : ℝ) < 2 * δ * cV := by positivity
    have hkey : 1 / (2 * δ * cV) ≤ Real.sqrt (Real.log x) := by
      have h := Real.sqrt_le_sqrt hLB
      rwa [Real.sqrt_sq (by positivity)] at h
    have h3 : 1 ≤ 2 * δ * cV * Real.sqrt (Real.log x) := by
      rw [div_le_iff₀ hp] at hkey; linarith
    have hself : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt hLpos.le
    have h4 : Real.sqrt (Real.log x) ≤ 2 * δ * cV * Real.log x := by
      nlinarith [h3, Real.sqrt_nonneg (Real.log x), hself]
    unfold gt₁
    rw [div_le_div_iff₀ hVpos hxpos]
    nlinarith [mul_le_mul_of_nonneg_right (hTle.trans h4) hxpos.le,
      mul_le_mul_of_nonneg_left hVge (show (0 : ℝ) ≤ 2 * δ by linarith)]

  have hnum : Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
      + Real.exp (-(2 * Real.log x))
      ≤ 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
    have hEnn : (0 : ℝ) ≤ Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
        + Real.exp (-(2 * Real.log x)) :=
      add_nonneg (mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))) (Real.exp_nonneg _)
    have hc1 : Real.exp (-(2 * κ₀ * Real.log x)) = (x : ℝ) ^ (-(2 * κ₀)) := by
      rw [Real.rpow_def_of_pos hxpos]; ring_nf
    have hc3 : Real.exp (-(2 * Real.log x)) = (x : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hxpos]; ring_nf
    have hLpow : Real.log (x : ℝ) ^ ((1 : ℝ) + (C₄ : ℝ))
        = Real.log (x : ℝ) ^ C₄ * Real.log x := by
      rw [show ((1 : ℝ) + (C₄ : ℝ)) = ((C₄ + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_succ]
    have hkey := hXb x hxXb
    simp only [Function.comp_apply] at hkey
    rw [le_div_iff₀ h20V]
    have heq : (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (20 * CV * (x : ℝ) * Real.log x)
        = 20 * CV * Real.log (x : ℝ) ^ ((1 : ℝ) + (C₄ : ℝ)) * (x : ℝ) ^ (-(2 * κ₀))
          + 20 * CV * Real.log (x : ℝ) * (x : ℝ) ^ (-(1 : ℝ)) := by
      rw [hc1, hc3, hLpow,
        show (-(1 : ℝ)) = -(2 : ℝ) + 1 by ring, Real.rpow_add hxpos, Real.rpow_one]
      field_simp
    have hmono : (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
        ≤ (Real.exp (-(2 * κ₀ * Real.log x)) * (1 / (x : ℝ) * Real.log x ^ C₄)
          + Real.exp (-(2 * Real.log x))) * (20 * CV * (x : ℝ) * Real.log x) := by
      refine mul_le_mul_of_nonneg_left ?_ hEnn
      linarith
    rw [heq] at hmono
    linarith [hmono, hkey]

  have hA := gintermediate_upper a b c p q hq hpd hδ hδd x (by omega)
    (gintegrand_continuous a b c p q x n) (gintegrand_abs_le a b c p q x n) hVpos hT2 h12
  have hB := gminor_upper a b c p q x (by omega) hδ hδ16 hL1
    (gintegrand_continuous a b c p q x n) (gintegrand_abs_le a b c p q x n)
    (hvl x hxX₅) (hmeasx x hxX₂) hnum
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
      (gt₁ a b c p q x) (2 * δ / (x : ℝ)))
    ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume) (2 * δ / (x : ℝ)) (1 / 2))
  rw [← hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hSne : Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ) ≠ 0 := ne_of_gt hVpos
  have hsum : 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
      + 1 / (20 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ))
      = 1 / (10 * Real.sqrt ((GS2 a b c p q x : ℕ) : ℝ)) := by
    field_simp
    ring
  linarith [hA, hB, hsum]

example : ∀ (a b c p q : ℕ), 1 < a → 1 < b → 1 < c →
    PairwiseCoprime3 a b c → 0 < q → q < p →
    p < q * min a (min b c) →
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      |∫ t in (gt₁ a b c p q x)..(1 / 2),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))|
        ≤ 1 / (10 * Real.sqrt (GS2 a b c p q x)) := @gtail_upper

end

end Erdos123Band
end Module_GTail

section Module_GLCLT

namespace Erdos123Band

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem gcount_eq_integral (a b c p q x n : ℕ) :
    ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℝ)
      = 2 ^ (GBand a b c p q x).card
        * ∫ t in (0:ℝ)..1,
            (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
              * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
  classical
  have hcont : Continuous
      (fun t : ℝ => (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))) := by
    unfold e
    fun_prop
  have hIoc : IntegrableOn
      (fun t : ℝ => (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      (Set.Ioc (0:ℝ) 1) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hcont.intervalIntegrable 0 1
  have hfourier : (∫ t in (0:ℝ)..1,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t)))
      = ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℂ) :=
    subsetSum_fourier (GBand a b c p q x) n
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at hfourier
  have h2 := congrArg Complex.re hfourier
  simp only [Complex.natCast_re] at h2
  have hre : (∫ t in Set.Ioc (0:ℝ) 1,
        (∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re
      = ∫ t in Set.Ioc (0:ℝ) 1,
          ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re := by
    simpa using (Complex.reCLM.integral_comp_comm hIoc).symm
  have hcongr : (∫ t in Set.Ioc (0:ℝ) 1,
        ((∏ s ∈ GBand a b c p q x, (1 + e ((s : ℝ) * t))) * e (-((n : ℝ) * t))).re)
      = ∫ t in Set.Ioc (0:ℝ) 1, 2 ^ (GBand a b c p q x).card *
          ((∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [gintegrand_re a b c p q x n t, mul_assoc]
  rw [hre, hcongr, MeasureTheory.integral_const_mul] at h2
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact h2.symm

set_option maxHeartbeats 1000000 in
theorem glclt_coverage (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ n : ℕ,
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) →
      ∃ T : Finset ℕ, T ⊆ GBand a b c p q x ∧ T.sum id = n := by
  classical
  obtain ⟨X₁, hprin⟩ := gprincipal_lower a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨X₂, htail⟩ := gtail_upper a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨cV, hcV, X₃, hVlow⟩ := gV_lower a b c p q ha hb hc hco hq hqp hpd
  refine ⟨max (max X₁ X₂) (max X₃ 3), fun x hx n hn => ?_⟩
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₃ : X₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxR : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
  have hlog : (1:ℝ) ≤ Real.log x := one_le_log hx3
  have hVpos : (0:ℝ) < Real.sqrt (GS2 a b c p q x) := by
    have hpos : (0:ℝ) < cV * (x:ℝ) * Real.log x :=
      mul_pos (mul_pos hcV (by linarith)) (by linarith)
    linarith [hVlow x hxX₃]
  have hP := hprin x hxX₁ n hn
  have hTl := abs_le.mp (htail x hxX₂ n)

  have hsplit :
      (∫ t in (0:ℝ)..(gt₁ a b c p q x),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
        + (∫ t in (gt₁ a b c p q x)..(1/2 : ℝ),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)))
      = ∫ t in (0:ℝ)..(1/2 : ℝ),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) :=
    intervalIntegral.integral_add_adjacent_intervals
      ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
        0 (gt₁ a b c p q x))
      ((gintegrand_continuous a b c p q x n).intervalIntegrable (μ := volume)
        (gt₁ a b c p q x) (1/2 : ℝ))
  have hid : (1:ℝ) / (5 * Real.sqrt (GS2 a b c p q x))
      = 2 * (1 / (10 * Real.sqrt (GS2 a b c p q x))) := by
    have hne : Real.sqrt (GS2 a b c p q x) ≠ 0 := ne_of_gt hVpos
    first
      | (field_simp; ring)
      | field_simp
  have hhalf : 1 / (10 * Real.sqrt (GS2 a b c p q x))
      ≤ ∫ t in (0:ℝ)..(1/2 : ℝ),
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
    rw [← hsplit]; linarith [hP, hTl.1]
  have hfull : 1 / (5 * Real.sqrt (GS2 a b c p q x))
      ≤ ∫ t in (0:ℝ)..1,
          (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
            * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) := by
    rw [gsplit_half a b c p q x n]; linarith [hhalf]
  have hIpos : (0:ℝ) < ∫ t in (0:ℝ)..1,
      (∏ s ∈ GBand a b c p q x, Real.cos (Real.pi * ((s : ℝ) * t)))
        * Real.cos (Real.pi * (((GS1 a b c p q x : ℝ) - 2 * (n : ℝ)) * t)) :=
    lt_of_lt_of_le (div_pos one_pos (by linarith)) hfull
  have hcnt : (0:ℝ)
      < ((((GBand a b c p q x).powerset.filter (fun T => ∑ s ∈ T, s = n)).card : ℕ) : ℝ) := by
    rw [gcount_eq_integral]
    exact mul_pos (by positivity) hIpos
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (by exact_mod_cast hcnt)
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  exact ⟨T, hT.1, by simpa using hT.2⟩

end Erdos123Band
end Module_GLCLT

section Module_GMain

namespace Erdos123Band

set_option maxHeartbeats 1000000 in
theorem gsweep {a b c p q : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) (X₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ x : ℕ, X₀ ≤ x ∧
      (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2 ≤ (GS2 a b c p q x : ℤ) := by
  classical
  obtain ⟨X₁, hX₁⟩ := gband_card_eventually_ge ha hb hc hco hq hqp hpd (4 * p ^ 4)
  set X₂ : ℕ := max (max X₀ X₁) 2 with hX₂def
  have hX₂card : ∀ x : ℕ, X₂ ≤ x → 4 * p ^ 4 ≤ (GBand a b c p q x).card := fun x hx =>
    hX₁ x (le_trans (le_trans (le_max_right X₀ X₁) (le_max_left _ 2)) hx)
  have hp1 : 1 ≤ p := by omega
  have hp4 : 1 ≤ 4 * p ^ 4 := by
    have h1 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hS2of : ∀ x : ℕ, X₂ ≤ x → 4 * p ^ 4 * x ^ 2 ≤ GS2 a b c p q x := by
    intro x hx
    calc 4 * p ^ 4 * x ^ 2 ≤ (GBand a b c p q x).card * x ^ 2 :=
          Nat.mul_le_mul_right _ (hX₂card x hx)
      _ ≤ GS2 a b c p q x := gS2_ge_card_sq a b c p q x
  refine ⟨GS1 a b c p q X₂ + 1, fun n hn => ?_⟩
  set Q : ℕ → Prop := fun x' => X₂ ≤ x' ∧ GS1 a b c p q x' ≤ 2 * n with hQdef
  have hQ_le : ∀ x', Q x' → x' ≤ 2 * n := by
    intro x' ⟨hx', hs1⟩
    have hcard : 1 ≤ (GBand a b c p q x').card := le_trans hp4 (hX₂card x' hx')
    exact le_trans (gle_S1_of_card_pos hcard) hs1
  have hQX₂ : Q X₂ := ⟨le_refl _, by omega⟩
  have hX₂le : X₂ ≤ 2 * n + 1 := le_trans (hQ_le X₂ hQX₂) (by omega)
  set x : ℕ := Nat.findGreatest Q (2 * n + 1) with hxdef
  have hspec : Q x := Nat.findGreatest_spec hX₂le hQX₂
  have hxle : x ≤ 2 * n := hQ_le x hspec
  have hnot : ¬Q (x + 1) :=
    Nat.findGreatest_is_greatest (P := Q) (n := 2 * n + 1) (k := x + 1)
      (by omega) (by omega)
  have hnext : 2 * n < GS1 a b c p q (x + 1) := by
    by_contra hcon
    exact hnot ⟨le_trans hspec.1 (by omega), by omega⟩
  have hstep := gS1_step_upper (a := a) (b := b) (c := c) (p := p) hq x
  have hS2 := hS2of x hspec.1
  have hx2 : 2 ≤ x := le_trans (le_max_right _ 2) hspec.1
  refine ⟨x, le_trans (le_trans (le_max_left X₀ X₁) (le_max_left _ 2)) hspec.1, ?_⟩
  have h1 : (GS1 a b c p q x : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hspec.2
  have h2 : 2 * (n : ℤ) - (GS1 a b c p q x : ℤ) ≤ (p : ℤ) * p * ((x : ℤ) + 1) := by
    have hz : (2 * n : ℤ) < (GS1 a b c p q (x + 1) : ℤ) := by exact_mod_cast hnext
    have hcast : (GS1 a b c p q (x + 1) : ℤ)
        ≤ (GS1 a b c p q x : ℤ) + (p : ℤ) * p * ((x : ℤ) + 1) := by
      exact_mod_cast hstep
    linarith
  have h3 : (4 : ℤ) * (p : ℤ) ^ 4 * (x : ℤ) ^ 2 ≤ (GS2 a b c p q x : ℤ) := by
    exact_mod_cast hS2
  have hx2' : (2 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx2
  have hP0 : (0 : ℤ) ≤ (p : ℤ) * p := by positivity
  have hA0 : 0 ≤ 2 * (n : ℤ) - (GS1 a b c p q x : ℤ) := by linarith
  have h4 : (p : ℤ) * p * ((x : ℤ) + 1) ≤ 2 * ((p : ℤ) * p) * (x : ℤ) := by
    nlinarith [hx2', hP0]
  have hAB : 2 * (n : ℤ) - (GS1 a b c p q x : ℤ) ≤ 2 * ((p : ℤ) * p) * (x : ℤ) :=
    le_trans h2 h4
  have h5 : (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2
      ≤ (2 * ((p : ℤ) * p) * (x : ℤ)) ^ 2 := by
    nlinarith [hA0, hAB]
  calc (2 * (n : ℤ) - (GS1 a b c p q x : ℤ)) ^ 2
      ≤ (2 * ((p : ℤ) * p) * (x : ℤ)) ^ 2 := h5
    _ = 4 * (p : ℤ) ^ 4 * (x : ℤ) ^ 2 := by ring
    _ ≤ (GS2 a b c p q x : ℤ) := h3

set_option maxHeartbeats 1000000 in
theorem erdos123_dcomplete_general (a b c p q : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hq : 0 < q) (hqp : q < p)
    (hpd : p < q * min a (min b c)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ x : ℕ, ∃ T : Finset ℕ, T ⊆ GBand a b c p q x ∧ (∀ s ∈ T, s ∈ Smooth3 a b c) ∧
        IsPrimitive T ∧ T.sum id = n := by
  obtain ⟨X₀, hcov⟩ := glclt_coverage a b c p q ha hb hc hco hq hqp hpd
  obtain ⟨N₀, hsweep⟩ := gsweep ha hb hc hco hq hqp hpd X₀
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, hwin⟩ := hsweep n hn
  obtain ⟨T, hsub, hsum⟩ := hcov x hx n hwin
  exact ⟨x, T, hsub, fun s hs => (of_mem_GBand (hsub hs)).1,
    (gband_primitive ha hb hc hco hq hpd x).subset hsub, hsum⟩

set_option maxHeartbeats 1000000 in
theorem erdos123_dcomplete_real (a b c : ℕ) (ρ : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hco : PairwiseCoprime3 a b c) (hρ1 : 1 < ρ) (hρd : ρ < min a (min b c)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ x : ℕ, ∃ T : Finset ℕ,
        (∀ s ∈ T, s ∈ Smooth3 a b c ∧ (x : ℝ) ≤ s ∧ (s : ℝ) < ρ * x) ∧
        IsPrimitive T ∧ T.sum id = n := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hρ1
  set p : ℕ := r.num.toNat with hpdef
  set q : ℕ := r.den with hqdef
  have hq0 : 0 < q := r.pos
  have hr0 : (0 : ℚ) < r := by
    have h1 : (0 : ℝ) < (r : ℝ) := lt_trans one_pos hr1
    exact_mod_cast h1
  have hnum0 : 0 < r.num := Rat.num_pos.mpr hr0
  have hpn : ((p : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum0.le
  have hp0 : 0 < p := by
    have h1 : (0 : ℤ) < ((p : ℕ) : ℤ) := by rw [hpn]; exact hnum0
    exact_mod_cast h1
  have hpR : ((p : ℕ) : ℝ) = ((r.num : ℤ) : ℝ) := by exact_mod_cast hpn
  have hrcast : (r : ℝ) = (p : ℝ) / (q : ℝ) := by
    rw [Rat.cast_def, hpR, hqdef]
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hqp : q < p := by
    have h1 : (q : ℝ) < (p : ℝ) := by
      have h2 : (1 : ℝ) < (p : ℝ) / (q : ℝ) := by rw [← hrcast]; exact hr1
      rw [lt_div_iff₀ hqR] at h2
      linarith
    exact_mod_cast h1
  have hpd : p < q * min a (min b c) := by
    have hminR : ((min a (min b c) : ℕ) : ℝ) = min (a : ℝ) (min (b : ℝ) (c : ℝ)) := by
      push_cast
      rfl
    have h1 : (p : ℝ) / (q : ℝ) < min (a : ℝ) (min (b : ℝ) (c : ℝ)) := by
      rw [← hrcast, ← hminR]; exact lt_trans hr2 hρd
    have h2 : (p : ℝ) < (q : ℝ) * ((min a (min b c) : ℕ) : ℝ) := by
      rw [hminR]
      rw [div_lt_iff₀ hqR] at h1
      linarith
    have h3 : (p : ℝ) < ((q * min a (min b c) : ℕ) : ℝ) := by
      push_cast
      push_cast at h2
      linarith
    exact_mod_cast h3
  obtain ⟨N₀, hgen⟩ := erdos123_dcomplete_general a b c p q ha hb hc hco hq0 hqp hpd
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  obtain ⟨x, T, hsub, hsmooth, hprim, hsum⟩ := hgen n (le_trans (le_max_left _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hTne : T.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hsum
    omega
  obtain ⟨s₀, hs₀⟩ := hTne
  have hx0 : 0 < x := by
    obtain ⟨-, -, hw⟩ := of_mem_GBand (hsub hs₀)
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [h0, Nat.mul_zero] at hw
      exact absurd hw (Nat.not_lt_zero _)
    · exact h0
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  refine ⟨x, T, fun s hs => ?_, hprim, hsum⟩
  obtain ⟨hS, hxs, hw⟩ := of_mem_GBand (hsub hs)
  refine ⟨hS, by exact_mod_cast hxs, ?_⟩
  have hcast : (q : ℝ) * (s : ℝ) < (p : ℝ) * (x : ℝ) := by exact_mod_cast hw
  have h1 : (s : ℝ) < (p : ℝ) / (q : ℝ) * (x : ℝ) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hqR]
    nlinarith [hcast]
  have h2 : (p : ℝ) / (q : ℝ) * (x : ℝ) < ρ * (x : ℝ) := by
    apply mul_lt_mul_of_pos_right _ hxR
    rw [← hrcast]
    exact hr2
  linarith

end Erdos123Band

end Module_GMain

open Filter
open scoped Pointwise

theorem OMA.solution : type_of% @Erdos123.erdos_123.variants.powers_2_3_5_snug := by
  intro ε hε
  let δ := min ε (1 / 2 : ℝ)
  let ρ := 1 + δ
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hρ : 1 < ρ := by dsimp [ρ]; linarith
  have hρsmall : ρ < ((min (2 : ℕ) (min 3 5) : ℕ) : ℝ) := by
    norm_num
    dsimp [ρ]
    linarith
  obtain ⟨N, hN⟩ := Erdos123Band.erdos123_dcomplete_real 2 3 5 ρ
    (by decide) (by decide) (by decide)
    (by norm_num [Erdos123Band.PairwiseCoprime3]) hρ hρsmall
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  obtain ⟨x, T, hT, -, hSum⟩ := hN n ((le_max_left N 1).trans hn)
  have hNonempty : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hSum
    omega
  refine ⟨T, ?_, ⟨hNonempty, ?_⟩, hSum⟩
  · intro a ha
    obtain ⟨k, l, m, rfl⟩ := (hT a ha).1
    have hpow (p r : ℕ) : p ^ r ∈ Submonoid.powers p :=
      Submonoid.pow_mem _ (Submonoid.mem_powers p) r
    exact Set.mem_mul.2 ⟨2 ^ k * 3 ^ l, Set.mem_mul.2 ⟨2 ^ k, hpow 2 k, 3 ^ l,
      hpow 3 l, rfl⟩, 5 ^ m, hpow 5 m, rfl⟩
  · intro a ha
    have hx := (hT (T.min' hNonempty) (T.min'_mem hNonempty)).2.1
    refine (hT a ha).2.2.trans_le ?_
    calc
      ρ * (x : ℝ) ≤ (1 + ε) * (x : ℝ) :=
        mul_le_mul_of_nonneg_right (by dsimp [ρ]; linarith) (Nat.cast_nonneg _)
      _ ≤ (1 + ε) * (T.min' hNonempty : ℝ) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
