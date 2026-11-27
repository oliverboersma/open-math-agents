import FormalConjectures.ErdosProblems.«710»
import Mathlib

/-!
Formalization of the stronger lower estimate by Will Howe, Grant Huffman,
Jensen Kohlmeyer, and Liam Kruer, with a comparison of the two asymptotic scales.
https://github.com/Ghuffy1/erdos710-lean/tree/ee0440a8f58b07bcdc89c8b12606052cb84aac91

This repository contains an attributed subset of the Apache-2.0 licensed
AlexKontorovich/PrimeNumberTheoremAnd project, pinned to
c39a751132c88b6e8080b74c74023fd95b3d8be0. Original authorship and copyright
headers are retained. The source selection, removed unused material, and
checksums are recorded in vendor/pnt-slice-manifest.json.

The exact problem-definition bridge reproduces the mathematical definitions
from google-deepmind/formal-conjectures, Copyright 2026 The Formal Conjectures
Authors, licensed under Apache 2.0. The examined blobs are identified in
Erdos710/CanonicalBridge.lean and docs/STATEMENT.md. No unanswered theorem from
that repository is imported.

The mathematical statement was publicly announced earlier by David Turturean.
See docs/ATTRIBUTION.md and docs/PRIORITY.md. This repository makes no claim of
first mathematical discovery or organizer-confirmed formalization priority.

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
namespace MatchingEstimate710

def HasMatching (n h : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ i, n < a i ∧ a i < n + h ∧ (i.val + 1) ∣ a i

def neighbors (n h : ℕ) (i : Fin n) : Finset ℕ :=
  (Finset.Ioo n (n + h)).filter (fun m => (i.val + 1) ∣ m)

def HallCondition (n h : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ (S.biUnion (neighbors n h)).card

theorem hall_iff_hasMatching (n h : ℕ) : HallCondition n h ↔ HasMatching n h := by
  classical
  rw [HallCondition, HasMatching]
  rw [Finset.all_card_le_biUnion_card_iff_existsInjective']
  simp only [neighbors, Finset.mem_filter, Finset.mem_Ioo, and_assoc]

theorem hasMatching_mono (n : ℕ) {h H : ℕ} (hh : h ≤ H)
    (hm : HasMatching n h) : HasMatching n H := by
  obtain ⟨a, ha, hb⟩ := hm
  refine ⟨a, ha, fun i => ?_⟩
  exact ⟨(hb i).1, lt_of_lt_of_le (hb i).2.1 (Nat.add_le_add_left hh n), (hb i).2.2⟩

theorem hasMatching_quadratic (n : ℕ) : HasMatching n (n * n + 1) := by
  refine ⟨fun i => (i.val + 1) * (n + 1), ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    have h' : i.val + 1 = j.val + 1 := Nat.eq_of_mul_eq_mul_right (by omega) h
    omega
  · intro i
    have hi : 1 ≤ i.val + 1 := by omega
    have hn : i.val + 1 ≤ n := i.isLt
    have hlo := Nat.mul_le_mul_right (n + 1) hi
    have hhi := Nat.mul_le_mul_right (n + 1) hn
    refine ⟨?_, ?_, dvd_mul_right _ _⟩ <;> nlinarith

theorem matching_exists (n : ℕ) : ∃ h, HasMatching n h :=
  ⟨n * n + 1, hasMatching_quadratic n⟩

noncomputable def f (n : ℕ) : ℕ := by
  classical
  exact Nat.find (matching_exists n)

theorem f_spec (n : ℕ) : HasMatching n (f n) := by
  classical
  exact Nat.find_spec (matching_exists n)

theorem f_le {n h : ℕ} (hh : HasMatching n h) : f n ≤ h := by
  classical
  exact Nat.find_min' (matching_exists n) hh

theorem f_le_quadratic (n : ℕ) : f n ≤ n * n + 1 :=
  f_le (hasMatching_quadratic n)

theorem hasMatching_lower {n h : ℕ} (hn : 0 < n) (hm : HasMatching n h) :
    n + 1 ≤ h := by
  obtain ⟨a, hinj, ha⟩ := hm
  let b : Fin n → Fin (h - 1) := fun i => ⟨a i - (n + 1), by
    have hi := ha i
    omega⟩
  have hb : Function.Injective b := by
    intro i j hij
    apply hinj
    have heq := congrArg Fin.val hij
    change a i - (n + 1) = a j - (n + 1) at heq
    have hi := ha i
    have hj := ha j
    omega
  have hc : n ≤ h - 1 := by simpa using Fintype.card_le_of_injective b hb
  omega

theorem f_ge_linear {n : ℕ} (hn : 0 < n) : n + 1 ≤ f n :=
  hasMatching_lower hn (f_spec n)

theorem f_zero : f 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply f_le
  refine ⟨Fin.elim0, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem f_one : f 1 = 2 := by
  have hlo := f_ge_linear (n := 1) (by omega)
  have hhi := f_le_quadratic 1
  omega

def HasEndpointMatching (n M : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ i, n < a i ∧ a i ≤ M ∧ (i.val + 1) ∣ a i

theorem endpoint_iff_length {n M : ℕ} (hnM : n ≤ M) :
    HasEndpointMatching n M ↔ HasMatching n (M - n + 1) := by
  constructor <;> rintro ⟨a, hinj, ha⟩ <;> refine ⟨a, hinj, fun i => ?_⟩
  · obtain ⟨hl, hu, hd⟩ := ha i
    exact ⟨hl, by omega, hd⟩
  · obtain ⟨hl, hu, hd⟩ := ha i
    exact ⟨hl, by omega, hd⟩

theorem f_le_of_endpoint {n M : ℕ} (hnM : n ≤ M)
    (hm : HasEndpointMatching n M) : f n ≤ M - n + 1 :=
  f_le ((endpoint_iff_length hnM).mp hm)

theorem no_endpoint_of_length_lt_f {n M : ℕ} (hnM : n ≤ M)
    (h : M - n + 1 < f n) : ¬ HasEndpointMatching n M := by
  intro hm
  exact (Nat.not_lt_of_ge (f_le_of_endpoint hnM hm)) h

end MatchingEstimate710
end

section
open Filter Asymptotics
open scoped Topology

namespace MatchingEstimate710

noncomputable def sharpConstant : ℝ := Real.sqrt 2 / Real.exp 1

noncomputable def scale (n : ℕ) : ℝ := (n : ℝ) * Real.sqrt (Real.log (n : ℝ))

def AsymptoticFormula : Prop :=
  (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => sharpConstant * scale n)

def LowerEstimate : Prop :=
  ∀ c : ℝ, c < sharpConstant → ∀ᶠ n : ℕ in atTop, c * scale n ≤ (f n : ℝ)

def UpperEstimate : Prop :=
  ∀ c : ℝ, sharpConstant < c → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ c * scale n

theorem sharpConstant_pos : 0 < sharpConstant := by
  unfold sharpConstant
  positivity

theorem scale_pos {n : ℕ} (hn : 2 ≤ n) : 0 < scale n := by
  have hnr : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  unfold scale
  exact mul_pos (by linarith) (Real.sqrt_pos.2 (Real.log_pos hnr))

theorem eventually_scale_pos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact scale_pos hn

theorem ratio_tendsto_of_estimates (hl : LowerEstimate) (hu : UpperEstimate) :
    Tendsto (fun n : ℕ => (f n : ℝ) / scale n) atTop (𝓝 sharpConstant) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hc : (a + sharpConstant) / 2 < sharpConstant := by linarith
    filter_upwards [hl _ hc, eventually_scale_pos] with n hn hs
    have hr := (le_div_iff₀ hs).2 hn
    linarith
  · intro a ha
    have hc : sharpConstant < (a + sharpConstant) / 2 := by linarith
    filter_upwards [hu _ hc, eventually_scale_pos] with n hn hs
    have hr := (div_le_iff₀ hs).2 hn
    linarith


theorem asymptoticFormula_of_estimates (hl : LowerEstimate) (hu : UpperEstimate) :
    AsymptoticFormula := by
  apply isEquivalent_of_tendsto_one
  change Tendsto (fun n : ℕ => (f n : ℝ) / (sharpConstant * scale n)) atTop (𝓝 1)
  have hr := (ratio_tendsto_of_estimates hl hu).div_const sharpConstant
  have hK : sharpConstant ≠ 0 := ne_of_gt sharpConstant_pos
  simpa only [Pi.div_apply, div_div, mul_comm, div_self hK] using hr

end MatchingEstimate710
end

section
open Filter Asymptotics
open scoped Topology


namespace MatchingEstimate710

theorem log_div_id_tendsto_zero :
    Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
  simpa only [Real.rpow_one] using
    (isLittleO_log_rpow_atTop (r := 1) zero_lt_one).tendsto_div_nhds_zero

theorem log_sq_div_id_tendsto_zero :
    Tendsto (fun L : ℝ => (Real.log L) ^ 2 / L) atTop (𝓝 0) := by
  simpa using (isLittleO_log_rpow_rpow_atTop (s := 1) 2 zero_lt_one).tendsto_div_nhds_zero

theorem sqrt_exponential_tail_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ => L * Real.exp (-c * Real.sqrt L)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp Real.tendsto_sqrt_atTop
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  simp only [Function.comp_apply, Real.rpow_two, Real.sq_sqrt hL]

theorem eventually_le_mul_of_div_tendsto_zero {f : ℝ → ℝ}
    (hf : Tendsto (fun L => f L / L) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, f L ≤ ε * L := by
  have he := hf.eventually (eventually_lt_nhds hε)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with L hh hL
  exact (div_le_iff₀ hL).mp hh.le

theorem logarithmic_window_small (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, C * Real.log L ≤ a * L := by
  have hh := log_div_id_tendsto_zero.const_mul C
  simp only [mul_zero] at hh
  apply eventually_le_mul_of_div_tendsto_zero _ ha
  simpa only [mul_div_assoc] using hh

theorem lattice_polynomial_window_tendsto (C : ℝ) :
    Tendsto (fun L : ℝ =>
      (((C * Real.log L) ^ 2 + (Real.log 2 + Real.log 3) * (C * Real.log L)) /
        (2 * Real.log 2 * Real.log 3)) / L) atTop (𝓝 0) := by
  have h₁ := log_sq_div_id_tendsto_zero.const_mul (C ^ 2 / (2 * Real.log 2 * Real.log 3))
  have h₂ := log_div_id_tendsto_zero.const_mul
    ((Real.log 2 + Real.log 3) * C / (2 * Real.log 2 * Real.log 3))
  have hh := h₁.add h₂
  simp only [mul_zero, add_zero] at hh
  apply hh.congr
  intro L
  ring

theorem lattice_tail_window_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun L : ℝ =>
      (2 * ((1 + 2 / Real.log 2) * (1 + 2 / Real.log 3)) * L ^ 2 *
        Real.exp (-c * Real.sqrt L)) / L) atTop (𝓝 0) := by
  have hh := (sqrt_exponential_tail_tendsto hc).const_mul
    (2 * ((1 + 2 / Real.log 2) * (1 + 2 / Real.log 3)))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp

end MatchingEstimate710
end

section
open Filter
open scoped Topology


namespace MatchingEstimate710

noncomputable def lowerEndpoint (κ : ℝ) (n : ℕ) : ℕ := ⌊κ * scale n⌋₊

noncomputable def upperWindow (κ : ℝ) (n : ℕ) : ℝ := Real.log ((lowerEndpoint κ n : ℝ) / n)
noncomputable def lowerWindow (β κ : ℝ) (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) * (β * Real.log n) / lowerEndpoint κ n)

theorem log_nat_tendsto_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem sqrt_log_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log n)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp log_nat_tendsto_atTop

theorem log_log_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto_atTop

theorem scale_tendsto_atTop : Tendsto scale atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ sqrt_log_nat_tendsto_atTop

theorem lowerEndpoint_ratio_tendsto {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun n : ℕ => (lowerEndpoint κ n : ℝ) / scale n) atTop (𝓝 κ) := by
  simpa only [Function.comp_def, lowerEndpoint] using
    (tendsto_nat_floor_mul_div_atTop hκ).comp scale_tendsto_atTop

theorem lowerEndpoint_tendsto_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (lowerEndpoint κ) atTop atTop :=
  tendsto_nat_floor_atTop.comp (scale_tendsto_atTop.const_mul_atTop hκ)

theorem lowerEndpoint_div_nat_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (lowerEndpoint κ n : ℝ) / n) atTop atTop := by
  have hh := (lowerEndpoint_ratio_tendsto hκ.le).pos_mul_atTop hκ sqrt_log_nat_tendsto_atTop
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs : Real.sqrt (Real.log n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  dsimp [scale]
  field_simp

theorem lowerEndpoint_log_ratio_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => Real.log ((lowerEndpoint κ n : ℝ) / scale n)) atTop (𝓝 (Real.log κ)) :=
  (Real.continuousAt_log hκ.ne').tendsto.comp (lowerEndpoint_ratio_tendsto hκ.le)

theorem upperWindow_identity {κ : ℝ} {n : ℕ} (hn : 2 ≤ n) (hT : 0 < lowerEndpoint κ n) :
    upperWindow κ n = Real.log ((lowerEndpoint κ n : ℝ) / scale n) + Real.log (Real.log n) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hT0 : (0 : ℝ) < lowerEndpoint κ n := by exact_mod_cast hT
  have hs : Real.sqrt (Real.log n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hr : 0 < (lowerEndpoint κ n : ℝ) / scale n := div_pos hT0 (scale_pos hn)
  have he : (lowerEndpoint κ n : ℝ) / n =
      ((lowerEndpoint κ n : ℝ) / scale n) * Real.sqrt (Real.log n) := by
    unfold scale
    field_simp
  rw [upperWindow, he, Real.log_mul hr.ne' hs, Real.log_sqrt hL.le]

theorem lowerWindow_identity {β κ : ℝ} (hβ : 0 < β) {n : ℕ}
    (hn : 2 ≤ n) (hT : 0 < lowerEndpoint κ n) :
    lowerWindow β κ n = Real.log β - Real.log ((lowerEndpoint κ n : ℝ) / scale n) +
      Real.log (Real.log n) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hT0 : (0 : ℝ) < lowerEndpoint κ n := by exact_mod_cast hT
  have hs : Real.sqrt (Real.log n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hr : (0 : ℝ) < (lowerEndpoint κ n : ℝ) / scale n := div_pos hT0 (scale_pos hn)
  have he : (n : ℝ) * (β * Real.log n) / lowerEndpoint κ n =
      (β / ((lowerEndpoint κ n : ℝ) / scale n)) * Real.sqrt (Real.log n) := by
    unfold scale
    have hsq := Real.sq_sqrt hL.le
    field_simp
    nlinarith [hsq]
  rw [lowerWindow, he, Real.log_mul (by positivity) hs, Real.log_div hβ.ne' hr.ne', Real.log_sqrt hL.le]

theorem window_difference_tendsto {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => lowerWindow β κ n - upperWindow κ n) atTop
      (𝓝 (Real.log (β / κ ^ 2))) := by
  have hc : Tendsto (fun _ : ℕ => Real.log β) atTop (𝓝 (Real.log β)) := tendsto_const_nhds
  have hh := hc.sub ((lowerEndpoint_log_ratio_tendsto hκ).const_mul 2)
  have he : Real.log β - 2 * Real.log κ = Real.log (β / κ ^ 2) := by
    rw [Real.log_div hβ.ne' (pow_ne_zero 2 hκ.ne'), Real.log_pow]
    ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), (lowerEndpoint_tendsto_atTop hκ).eventually (eventually_gt_atTop 0)]
    with n hn hT
  rw [lowerWindow_identity hβ hn hT, upperWindow_identity hn hT]
  ring

theorem upperWindow_ratio_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => upperWindow κ n / Real.log (Real.log n)) atTop (𝓝 (1 / 2)) := by
  have hz := (lowerEndpoint_log_ratio_tendsto hκ).div_atTop log_log_nat_tendsto_atTop
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) := tendsto_const_nhds
  have hh := hz.add hc
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), (lowerEndpoint_tendsto_atTop hκ).eventually (eventually_gt_atTop 0),
    log_log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hT hll
  rw [upperWindow_identity hn hT]
  field_simp

theorem lowerWindow_ratio_tendsto {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => lowerWindow β κ n / Real.log (Real.log n)) atTop (𝓝 (1 / 2)) := by
  have hc : Tendsto (fun _ : ℕ => Real.log β) atTop (𝓝 (Real.log β)) := tendsto_const_nhds
  have hz := (hc.sub (lowerEndpoint_log_ratio_tendsto hκ)).div_atTop log_log_nat_tendsto_atTop
  have hh := hz.add (tendsto_const_nhds (x := (1 / 2 : ℝ)))
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), (lowerEndpoint_tendsto_atTop hκ).eventually (eventually_gt_atTop 0),
    log_log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hT hll
  rw [lowerWindow_identity hβ hn hT]
  field_simp

theorem log_window_bounds {g : ℕ → ℝ}
    (hg : Tendsto (fun n => g n / Real.log (Real.log n)) atTop (𝓝 (1 / 2))) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ g n ∧ g n ≤ Real.log (Real.log n) := by
  have hl := hg.eventually (eventually_gt_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))
  have hu := hg.eventually (eventually_lt_nhds (by norm_num : (1 / 2 : ℝ) < 3 / 4))
  filter_upwards [hl, hu, log_log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hlow hupp hp
  have h₁ := (lt_div_iff₀ hp).mp hlow
  have h₂ := (div_lt_iff₀ hp).mp hupp
  constructor <;> nlinarith

theorem endpoint_window_bounds {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop,
      (0 ≤ upperWindow κ n ∧ upperWindow κ n ≤ Real.log (Real.log n)) ∧
      (0 ≤ lowerWindow β κ n ∧ lowerWindow β κ n ≤ Real.log (Real.log n)) :=
  (log_window_bounds (upperWindow_ratio_tendsto hκ)).and
    (log_window_bounds (lowerWindow_ratio_tendsto hβ hκ))

theorem nat_ratio_scale_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) / scale n) atTop (𝓝 0) := by
  have hh := tendsto_inv_atTop_zero.comp sqrt_log_nat_tendsto_atTop
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs : Real.sqrt (Real.log n) ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  simp only [Function.comp_apply, scale]
  field_simp

noncomputable def endpointLength (κ : ℝ) (n : ℕ) : ℕ := lowerEndpoint κ n - n + 1

theorem endpointLength_ratio_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (endpointLength κ n : ℝ) / scale n) atTop (𝓝 κ) := by
  have hi := scale_tendsto_atTop.const_div_atTop (1 : ℝ)
  have hh := ((lowerEndpoint_ratio_tendsto hκ.le).sub nat_ratio_scale_tendsto_zero).add hi
  simp only [sub_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    (lowerEndpoint_div_nat_tendsto hκ).eventually (eventually_ge_atTop (1 : ℝ))] with n hn hratio
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnT : n ≤ lowerEndpoint κ n := by
    exact_mod_cast (one_le_div hn0).mp hratio
  rw [endpointLength, Nat.cast_add, Nat.cast_sub hnT, Nat.cast_one]
  ring

end MatchingEstimate710
end

section
open MeasureTheory ProbabilityTheory
open scoped unitInterval


namespace MatchingEstimate710

theorem geometric_parameter_pos {p : unitInterval} (hp : p ≠ 0) : 0 < (p : ℝ) := by
  have hne : (p : ℝ) ≠ 0 := by
    intro h
    apply hp
    exact Subtype.ext h
  exact lt_of_le_of_ne p.property.1 hne.symm

theorem geometric_ratio_lt_one {p : unitInterval} (hp : p ≠ 0) :
    ‖1 - (p : ℝ)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [p.property.2])]
  linarith [geometric_parameter_pos hp]

theorem geometric_mean_hasSum {p : unitInterval} (hp : p ≠ 0) :
    HasSum (fun n : ℕ => ((1 - (p : ℝ)) ^ n * (p : ℝ)) * (n : ℝ))
      ((1 - (p : ℝ)) / (p : ℝ)) := by
  let r : ℝ := 1 - (p : ℝ)
  let f : ℕ → ℝ := fun n => r ^ n * (p : ℝ) * n
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (geometric_parameter_pos hp)
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (geometric_ratio_lt_one hp)).mul_left (r * (p : ℝ))
  have hshift : HasSum (fun n => f (n + 1)) (r * (p : ℝ) * (1 / (1 - r) ^ 2)) := by
    apply h.congr_fun
    intro n
    simp only [f, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have hsum := (hasSum_nat_add_iff (f := f) 1).mp hshift
  have hval : r * (p : ℝ) * (1 / (1 - r) ^ 2) + ∑ i ∈ Finset.range 1, f i =
      (1 - (p : ℝ)) / (p : ℝ) := by
    simp [f, r]
    field_simp
  rw [hval] at hsum
  exact hsum

theorem geometric_mean {p : unitInterval} (hp : p ≠ 0) :
    (∫ n : ℕ, (n : ℝ) ∂geometricMeasure p) = (1 - (p : ℝ)) / (p : ℝ) := by
  rw [integral_geometricMeasure hp]
  simpa only [smul_eq_mul] using (geometric_mean_hasSum hp).tsum_eq

theorem geometric_exp_hasSum {p : unitInterval} {s : ℝ}
    (hs : (1 - (p : ℝ)) * Real.exp s < 1) :
    HasSum (fun n : ℕ => ((1 - (p : ℝ)) ^ n * (p : ℝ)) * Real.exp (s * (n : ℝ)))
      ((p : ℝ) / (1 - (1 - (p : ℝ)) * Real.exp s)) := by
  have hnonneg : 0 ≤ (1 - (p : ℝ)) * Real.exp s :=
    mul_nonneg (by linarith [p.property.2]) (Real.exp_nonneg _)
  have hh := (hasSum_geometric_of_lt_one hnonneg hs).mul_left (p : ℝ)
  rw [div_eq_mul_inv]
  apply hh.congr_fun
  intro n
  rw [mul_comm s, Real.exp_nat_mul, mul_pow]
  ring

theorem geometric_exponential_moment {p : unitInterval} (hp : p ≠ 0) {s : ℝ}
    (hs : (1 - (p : ℝ)) * Real.exp s < 1) :
    (∫ n : ℕ, Real.exp (s * (n : ℝ)) ∂geometricMeasure p) =
      (p : ℝ) / (1 - (1 - (p : ℝ)) * Real.exp s) := by
  rw [integral_geometricMeasure hp]
  simpa only [smul_eq_mul] using (geometric_exp_hasSum hs).tsum_eq

end MatchingEstimate710
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators


namespace MatchingEstimate710

theorem geometric_natCast_integrable {p : unitInterval} (hp : p ≠ 0) :
    Integrable (fun n : ℕ => (n : ℝ)) (geometricMeasure p) := by
  apply (integrable_geometricMeasure_iff hp).mpr
  apply (geometric_mean_hasSum hp).summable.congr
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]

theorem geometric_exp_integrable {p : unitInterval} (hp : p ≠ 0) {s : ℝ}
    (hs : (1 - (p : ℝ)) * Real.exp s < 1) :
    Integrable (fun n : ℕ => Real.exp (s * (n : ℝ))) (geometricMeasure p) := by
  apply (integrable_geometricMeasure_iff hp).mpr
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (geometric_exp_hasSum hs).summable

variable {ι : Type*} [Fintype ι]

noncomputable def geometricProduct (p : ι → unitInterval) : Measure (ι → ℕ) :=
  Measure.pi (fun i => geometricMeasure (p i))

instance geometricProduct_probability (p : ι → unitInterval) :
    IsProbabilityMeasure (geometricProduct p) := by
  unfold geometricProduct
  infer_instance

noncomputable def weightedExponent (v : ι → ℝ) (z : ι → ℕ) : ℝ :=
  ∑ i, v i * (z i : ℝ)

theorem weightedExponent_integrable (p : ι → unitInterval) (hp : ∀ i, p i ≠ 0)
    (v : ι → ℝ) : Integrable (weightedExponent v) (geometricProduct p) := by
  classical
  apply integrable_finsetSum
  intro i _
  exact (integrable_comp_eval (μ := fun i => geometricMeasure (p i))
    (geometric_natCast_integrable (hp i))).const_mul (v i)

theorem weightedExponent_mean (p : ι → unitInterval) (hp : ∀ i, p i ≠ 0)
    (v : ι → ℝ) :
    (∫ z, weightedExponent v z ∂geometricProduct p) =
      ∑ i, v i * ((1 - (p i : ℝ)) / (p i : ℝ)) := by
  classical
  unfold weightedExponent geometricProduct
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_comp_eval
      (geometric_natCast_integrable (hp i)).aestronglyMeasurable, geometric_mean (hp i)]
  · intro i _
    exact (integrable_comp_eval (geometric_natCast_integrable (hp i))).const_mul (v i)

theorem exp_weightedExponent (v : ι → ℝ) (s : ℝ) (z : ι → ℕ) :
    Real.exp (s * weightedExponent v z) = ∏ i, Real.exp ((s * v i) * (z i : ℝ)) := by
  classical
  unfold weightedExponent
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_assoc]

theorem geometricProduct_exp_integrable (p : ι → unitInterval) (hp : ∀ i, p i ≠ 0)
    (v : ι → ℝ) {s : ℝ} (hs : ∀ i, (1 - (p i : ℝ)) * Real.exp (s * v i) < 1) :
    Integrable (fun z => Real.exp (s * weightedExponent v z)) (geometricProduct p) := by
  simp_rw [exp_weightedExponent]
  exact Integrable.fintype_prod (fun i => geometric_exp_integrable (hp i) (hs i))

theorem geometricProduct_exponential_moment (p : ι → unitInterval) (hp : ∀ i, p i ≠ 0)
    (v : ι → ℝ) {s : ℝ} (hs : ∀ i, (1 - (p i : ℝ)) * Real.exp (s * v i) < 1) :
    (∫ z, Real.exp (s * weightedExponent v z) ∂geometricProduct p) =
      ∏ i, (p i : ℝ) / (1 - (1 - (p i : ℝ)) * Real.exp (s * v i)) := by
  simp_rw [exp_weightedExponent]
  rw [geometricProduct, integral_fintype_prod_eq_prod
    (fun i (n : ℕ) => Real.exp ((s * v i) * (n : ℝ)))]
  apply Finset.prod_congr rfl
  intro i _
  exact geometric_exponential_moment (hp i) (hs i)

theorem geometricProduct_exponential_tail (p : ι → unitInterval) (hp : ∀ i, p i ≠ 0)
    (v : ι → ℝ) {s : ℝ} (hs0 : 0 < s)
    (hs : ∀ i, (1 - (p i : ℝ)) * Real.exp (s * v i) < 1) (T : ℝ) :
    (geometricProduct p).real {z | T ≤ weightedExponent v z} ≤
      Real.exp (-(s * T)) *
        ∏ i, (p i : ℝ) / (1 - (1 - (p i : ℝ)) * Real.exp (s * v i)) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := geometricProduct p) (Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le))
    (geometricProduct_exp_integrable p hp v hs) (Real.exp (s * T))
  have he : {z : ι → ℕ | Real.exp (s * T) ≤ Real.exp (s * weightedExponent v z)} =
      {z | T ≤ weightedExponent v z} := by
    ext z
    simp only [Set.mem_ofPred_eq, Real.exp_le_exp, mul_le_mul_iff_right₀ hs0]
  rw [he, geometricProduct_exponential_moment p hp v hs] at hm
  have h : (geometricProduct p).real {z | T ≤ weightedExponent v z} ≤
      (∏ i, (p i : ℝ) / (1 - (1 - (p i : ℝ)) * Real.exp (s * v i))) /
        Real.exp (s * T) := by
    apply (le_div_iff₀ (Real.exp_pos (s * T))).mpr
    rw [mul_comm]
    exact hm
  simpa only [div_eq_mul_inv, Real.exp_neg, mul_comm] using h

end MatchingEstimate710
end

section
open MeasureTheory
open scoped BigOperators


namespace MatchingEstimate710

noncomputable def tiltFactor (δ : ℝ) : ℝ := (1 + δ) / (1 - δ * (1 + δ))

theorem exp_sub_one_le_small {t δ : ℝ} (ht : 0 ≤ t) (htδ : t ≤ δ) (hδ : δ ≤ 1) :
    Real.exp t - 1 ≤ (1 + δ) * t := by
  have hn : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht]; exact htδ.trans hδ
  have h := Real.norm_exp_sub_one_sub_id_le hn
  simp only [Real.norm_eq_abs, abs_of_nonneg ht] at h
  have h' := (le_abs_self (Real.exp t - 1 - t)).trans h
  have ht2 : t ^ 2 ≤ δ * t := by nlinarith
  nlinarith

theorem geometric_small_exponent {b t δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ht0 : 0 ≤ t) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδ : δ * (1 + δ) < 1) (ht : t ≤ δ * (1 - b)) :
    b * Real.exp t < 1 ∧
      (1 - b) / (1 - b * Real.exp t) ≤
        Real.exp (tiltFactor δ * (b / (1 - b)) * t) := by
  have hh : 0 < 1 - b := sub_pos.mpr hb1
  have hq : 0 < 1 - δ * (1 + δ) := sub_pos.mpr hδ
  have htδ : t ≤ δ := ht.trans (by nlinarith)
  have he : Real.exp t - 1 ≤ (1 + δ) * t := exp_sub_one_le_small ht0 htδ hδ1
  have he0 : 0 ≤ Real.exp t - 1 := by linarith [Real.one_le_exp_iff.mpr ht0]
  have hbe : b * (Real.exp t - 1) ≤ Real.exp t - 1 := by nlinarith
  have hd : (1 - b) * (1 - δ * (1 + δ)) ≤ 1 - b * Real.exp t := by
    calc
      _ = (1 - b) - (1 + δ) * (δ * (1 - b)) := by ring
      _ ≤ (1 - b) - (1 + δ) * t := by nlinarith
      _ ≤ (1 - b) - (Real.exp t - 1) := by linarith
      _ ≤ 1 - b * Real.exp t := by nlinarith
  have hd0 : 0 < 1 - b * Real.exp t := (mul_pos hh hq).trans_le hd
  refine ⟨by linarith, ?_⟩
  have hratio : 0 < (1 - b) / (1 - b * Real.exp t) := div_pos hh hd0
  have hlog : Real.log ((1 - b) / (1 - b * Real.exp t)) ≤
      tiltFactor δ * (b / (1 - b)) * t := by
    calc
      _ ≤ (1 - b) / (1 - b * Real.exp t) - 1 := Real.log_le_sub_one_of_pos hratio
      _ = b * (Real.exp t - 1) / (1 - b * Real.exp t) := by field_simp; ring
      _ ≤ b * ((1 + δ) * t) / (1 - b * Real.exp t) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hb0) hd0.le
      _ ≤ b * ((1 + δ) * t) / ((1 - b) * (1 - δ * (1 + δ))) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hh hq) hd
      _ = _ := by unfold tiltFactor; field_simp
  simpa only [Real.exp_log hratio] using Real.exp_le_exp.mpr hlog

theorem exists_small_tilt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ * (1 + δ) < 1 ∧ tiltFactor δ ≤ 1 + ε := by
  let δ := min (1 / 4 : ℝ) (ε / 8)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδε : δ ≤ ε / 8 := min_le_right _ _
  have hδsq : δ ^ 2 ≤ δ / 4 := by nlinarith
  have hq : 0 < 1 - δ * (1 + δ) := by nlinarith
  refine ⟨δ, hδ0, by linarith, by linarith, ?_⟩
  unfold tiltFactor
  apply (div_le_iff₀ hq).mpr
  have hlow : (1 / 2 : ℝ) ≤ 1 - δ * (1 + δ) := by nlinarith
  have hprod : ε / 2 ≤ ε * (1 - δ * (1 + δ)) :=
    by nlinarith [mul_le_mul_of_nonneg_left hlow hε.le]
  nlinarith

variable {ι : Type*} [Fintype ι]

theorem geometricProduct_small_tilt (p : ι → unitInterval) (hp : ∀ i, p i ≠ 0)
    (v : ι → ℝ) {s δ : ℝ} (hs0 : 0 < s) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδ : δ * (1 + δ) < 1)
    (ht0 : ∀ i, 0 ≤ s * v i) (ht : ∀ i, s * v i ≤ δ * (p i : ℝ)) (T : ℝ) :
    (geometricProduct p).real {z | T ≤ weightedExponent v z} ≤
      Real.exp (-s * (T - tiltFactor δ *
        ∑ i, v i * ((1 - (p i : ℝ)) / (p i : ℝ)))) := by
  classical
  have hb (i : ι) := geometric_small_exponent
    (by linarith [(p i).property.2] : 0 ≤ 1 - (p i : ℝ))
    (by linarith [geometric_parameter_pos (hp i)] : 1 - (p i : ℝ) < 1)
    (ht0 i) hδ0 hδ1 hδ (by simpa using ht i)
  have hbound : (∏ i, (p i : ℝ) / (1 - (1 - (p i : ℝ)) * Real.exp (s * v i))) ≤
      Real.exp (s * tiltFactor δ * ∑ i, v i * ((1 - (p i : ℝ)) / (p i : ℝ))) := by
    calc
      _ ≤ ∏ i, Real.exp (tiltFactor δ * ((1 - (p i : ℝ)) / (p i : ℝ)) * (s * v i)) := by
        apply Finset.prod_le_prod
        · intro i _
          exact div_nonneg (p i).property.1 (by linarith [(hb i).1])
        · intro i _
          simpa only [sub_sub_cancel] using (hb i).2
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have htail := geometricProduct_exponential_tail p hp v hs0 (fun i => (hb i).1) T
  calc
    _ ≤ Real.exp (-(s * T)) *
        Real.exp (s * tiltFactor δ * ∑ i, v i * ((1 - (p i : ℝ)) / (p i : ℝ))) :=
      htail.trans (mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _))
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end MatchingEstimate710
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean.
Original blob 1fa2d2b6a88a2b891dc7674914e8e3fa7d19472c.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

open Filter Real


theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean.
Original blob dc51688f7332e0caf3bd4d1b50c1d0052d304103.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/Sobolev.lean.
Original blob 1f98bcbccc7ba3b9c9ee02ec95404731085368f9.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

lemma ext_fun {f g : CS n E} (h : ∀ x, f x = g x) : f = g := by
  cases f with | mk f hf hs =>
    cases g with | mk g hg ht =>
      have hfg : f = g := funext h
      subst g
      rfl

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  apply ext_fun
  intro x
  exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  apply ext_fun
  intro v
  by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/Fourier.lean.
Original blob 99e15a0237162df31161745e8e9e98a891c44a51.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (Circle.norm_coe z)

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _ -- `scomp` introduces ℝ-smul on ℂ, which we undo
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv


lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)


lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K


lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)


lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]


lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean.
Original blob 13d3575b14d663481b15e0099f75c42739668f40.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/SmoothExistence.lean.
Original blob b33edf879b1117ae0912512529051f0ba77b7d9e.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/Wiener.lean.
Original blob 59fd5069a7eca51a8bc5005b5c43e31a5cbb38ac.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

 

noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

-- TODO - add to mathlib

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

                        
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp


lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      cexp (↑(-2 * π * a * (u / (2 * π))) * I) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    simp only [smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun u ↦ ‖cexp (-(↑u * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a ↦ ‖ψ a‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      rw [hasFiniteIntegral_iff_enorm]
      simp only [Function.uncurry, smul_eq_mul, enorm_mul, Complex.enorm_exp_ofReal_mul_I, one_mul]
      simpa only [ofReal_exp, ofReal_mul, ofReal_neg, ofReal_sub, ofReal_one, neg_mul, f1, f2] using this
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

                        
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq_integral_exp_smul, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul, ← mul_assoc, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * b * ψ t * d = (a * b * d) * ψ t by ring]
  congr 1
  have hint : (fun u : ℝ => (↑(Real.exp (-u * (σ' - 1))) : ℂ) *
      cexp (↑(-2 * π * t * (u / (2 * π))) * I)) =
      (fun u : ℝ => cexp ((1 - ↑σ' - ↑t * I) * ↑u)) := by
    funext u
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hπ]
    <;> ring
  rw [hint]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx

 

lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)
                      
theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

theorem decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0] ; gcongr
                        
lemma decay_bounds (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_bounds_W21 ψ hA hA' u

lemma decay_bounds_cor_aux (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg (one_add_sq_pos u).le] at hC
  rwa [le_div_iff₀' (one_add_sq_pos _)]

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    exact ((continuous_FourierIntegral ψ).comp (continuous_id.div_const c)).aestronglyMeasurable
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)

lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

lemma nnabla_cast (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  ext n ; simp [nnabla]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg (fun n _ ↦ ha n)) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right₀ l1 h

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)



theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr e1),
      abs_of_pos (inv_pos.mpr e2)] using inv_anti₀ e1 e3

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])
                        
lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)

lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  have hEq (x : ℝ) : (∫ t, f t * exp (log x * t * I)) =
      𝓕 f (-Real.log x / (2 * π)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    dsimp only
    rw [smul_eq_mul, mul_comm (f t)]
    have ht : -2 * π * t * (-Real.log x / (2 * π)) = Real.log x * t := by
      field_simp [Real.pi_ne_zero]
      <;> ring
    rw [ht, ofReal_mul]
  simp only [hEq]

  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)
                            
lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm
                        
lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩

noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg (fun n _ ↦ hf n)) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg (fun n _ ↦ hf n)

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  convert! cancel_aux' hf hg hf' hg' n using 1
  match n with
  | n + 2 => simp only [cumsum_succ] ; push_cast ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    intro ε hε
    obtain ⟨δ, hδ, hk⟩ := k2 ε hε
    refine ⟨δ, hδ, fun {x} hx hdist => ?_⟩
    rcases eq_or_lt_of_le (show 0 ≤ x from hx) with he | hpos
    · subst x
      simpa using hε
    · exact hk hpos hdist

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · exact (((continuous_FourierIntegral ψ).comp (continuous_id.div_const (2 * π))).norm).aestronglyMeasurable
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring

lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)
                        
lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'

-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead
                        
lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f

noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]
                            
lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4

lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩


theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this

 
                              
lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith

lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1
                            
theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith

 

-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)
                                                                    
theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_ofPred_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

-- #print axioms WeakPNT
end

section
/-
Adapted from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
Commit c39a751132c88b6e8080b74c74023fd95b3d8be0; original file PrimeNumberTheoremAnd/Consequences.lean.
Original blob d9283ccaac007eed83e131577df256bcecdd150f.
Copyright the PrimeNumberTheoremAnd contributors. Apache-2.0; see vendor/PNT-LICENSE.
Modified locally: removed blueprint-only metadata and selected the proved PNT dependency slice.
Further toolchain-compatibility edits, if required, are recorded in the local sources.
-/

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  intro z hz
  have hz' := Set.Ico_subset_Icc_self.trans h hz
  have hcd : c ≤ d := by
    contrapose! hz'
    rw [Icc_eq_empty_of_lt hz']
    exact notMem_empty _
  simp only [mem_Ico, mem_Icc] at *
  refine ⟨hz'.1, hz'.2.eq_or_lt.resolve_left ?_⟩
  rintro rfl
  apply hz.2.not_ge
  have := h <| right_mem_Icc.mpr (hz.1.trans hz.2.le)
  simp only [mem_Icc] at this
  exact this.2

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
                        
lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R}
    (x : ℝ) : ∑ᶠ (n : ℕ) (_ : n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero

lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_le_two]
  exact one_lt_two


theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← add_sub_cancel u w]
  exact add_isLittleO huv hwu


theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop


theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'


lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this


lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  rwa [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx a; simp only [_root_.id] at a; linarith)] at h'


lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm


lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩


lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega
      
theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2
end

section
open Filter Asymptotics
open scoped Topology

namespace MatchingEstimate710

theorem theta_asymptotic :
    (fun x : ℝ => Chebyshev.theta x) ~[atTop] (fun x : ℝ => x) :=
  chebyshev_asymptotic

theorem theta_ratio_tendsto :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have hne : ∀ᶠ x : ℝ in atTop, x ≠ 0 :=
    (eventually_gt_atTop 0).mono (fun _ hx => hx.ne')
  exact (isEquivalent_iff_tendsto_one hne).mp theta_asymptotic

theorem theta_scaled_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Chebyshev.theta (a * x) / x) atTop (𝓝 a) := by
  have ht := theta_ratio_tendsto.comp (tendsto_id.const_mul_atTop ha)
  have hh := ht.mul_const a
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_apply, id_eq]
  field_simp


theorem prime_bin_theta_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (Chebyshev.theta (b * x) - Chebyshev.theta (a * x)) / x)
      atTop (𝓝 (b - a)) := by
  simpa only [sub_div] using (theta_scaled_tendsto hb).sub (theta_scaled_tendsto ha)

end MatchingEstimate710
end

section
open Filter MeasureTheory Set
open scoped Topology


namespace MatchingEstimate710

theorem weighted_integral_average_tendsto {f w : ℝ → ℝ} {a c : ℝ}
    (hf : ∀ b, a ≤ b → IntervalIntegrable f volume a b)
    (hw : ∀ b, a ≤ b → IntervalIntegrable w volume a b)
    (hw0 : ∀ t, a ≤ t → 0 ≤ w t)
    (hdiv : Tendsto (fun b => ∫ t in a..b, w t) atTop atTop)
    (hlim : ∀ ε > 0, ∀ᶠ t : ℝ in atTop, |f t - c * w t| ≤ ε * w t) :
    Tendsto (fun b => (∫ t in a..b, f t) / (∫ t in a..b, w t)) atTop (𝓝 c) := by
  let e : ℝ → ℝ := fun t => f t - c * w t
  have he : ∀ b, a ≤ b → IntervalIntegrable e volume a b :=
    fun b hb => (hf b hb).sub ((hw b hb).const_mul c)
  have hz : Tendsto (fun b => (∫ t in a..b, e t) / (∫ t in a..b, w t))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp (hlim (ε / 2) (by positivity))
    let T := max a R
    have haT : a ≤ T := le_max_left _ _
    have hRT : R ≤ T := le_max_right _ _
    have hsmall : Tendsto
        (fun b => |∫ t in a..T, e t| / (∫ t in a..b, w t)) atTop (𝓝 0) := by
      have hi := tendsto_inv_atTop_zero.comp hdiv
      have hh := hi.const_mul |∫ t in a..T, e t|
      simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using hh
    have hsmall' := Metric.tendsto_nhds.mp hsmall (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop T, hdiv.eventually (eventually_gt_atTop 0),
      hsmall'] with b hTb hW hb
    have hab : a ≤ b := haT.trans hTb
    have heTb : IntervalIntegrable e volume T b := (he T haT).symm.trans (he b hab)
    have hwTb : IntervalIntegrable w volume T b := (hw T haT).symm.trans (hw b hab)
    have htail : |∫ t in T..b, e t| ≤ (ε / 2) * (∫ t in T..b, w t) := by
      calc
        _ ≤ ∫ t in T..b, |e t| := intervalIntegral.abs_integral_le_integral_abs hTb
        _ ≤ ∫ t in T..b, (ε / 2) * w t := by
          apply intervalIntegral.integral_mono_on hTb heTb.abs (hwTb.const_mul _)
          intro t ht
          exact hR t (hRT.trans ht.1)
        _ = _ := intervalIntegral.integral_const_mul _ _
    have hwinitial : 0 ≤ ∫ t in a..T, w t :=
      intervalIntegral.integral_nonneg haT (fun t ht => hw0 t ht.1)
    have hwle : (∫ t in T..b, w t) ≤ ∫ t in a..b, w t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hw T haT) hwTb]
      linarith
    have hnum : |∫ t in a..b, e t| ≤
        |∫ t in a..T, e t| + (ε / 2) * (∫ t in a..b, w t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (he T haT) heTb]
      exact (abs_add_le _ _).trans (add_le_add_right
        (htail.trans (mul_le_mul_of_nonneg_left hwle (by positivity))) _)
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hW]
    have hb' : |∫ t in a..T, e t| / (∫ t in a..b, w t) < ε / 2 := by
      simpa only [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (abs_nonneg _) hW.le)] using hb
    calc
      _ ≤ (|∫ t in a..T, e t| + (ε / 2) * (∫ t in a..b, w t)) /
          (∫ t in a..b, w t) := div_le_div_of_nonneg_right hnum hW.le
      _ = |∫ t in a..T, e t| / (∫ t in a..b, w t) + ε / 2 := by field_simp
      _ < ε := by linarith
  have hc : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hh := hz.add hc
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hdiv.eventually (eventually_gt_atTop 0), eventually_ge_atTop a] with b hb hab
  dsimp only [e]
  rw [intervalIntegral.integral_sub (hf b hab) ((hw b hab).const_mul c),
    intervalIntegral.integral_const_mul]
  field_simp
  ring

end MatchingEstimate710
end

section
open Filter MeasureTheory Set
open scoped Topology BigOperators


namespace MatchingEstimate710

noncomputable def primeRootSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
    Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))

theorem primeRootSum_abel {x : ℝ} (hx : 2 ≤ x) :
    primeRootSum x = Chebyshev.theta x * x ^ (-(1 / 2 : ℝ)) +
      (1 / 2 : ℝ) * ∫ t in 2..x, Chebyshev.theta t * t ^ (-(3 / 2 : ℝ)) := by
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n => Real.log n)
  have hdiff : ∀ t ∈ Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt
  have hint : IntegrableOn (deriv (fun t : ℝ => t ^ (-(1 / 2 : ℝ)))) (Icc 2 x) := by
    rw [Real.deriv_rpow_const']
    refine ContinuousOn.integrableOn_Icc ?_
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact continuousAt_const.mul ((Real.hasDerivAt_rpow_const (Or.inl ht0)).continuousAt)
  have hs : primeRootSum x =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) ^ (-(1 / 2 : ℝ)) * a n := by
    unfold primeRootSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n.Prime <;> simp [a, hn, mul_comm]
  rw [hs, sum_mul_eq_sub_integral_mul₁ a (by simp [a]) (by simp [a]) x hdiff hint,
    ← intervalIntegral.integral_of_le hx]
  have ha : ∀ t : ℝ, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n) = Chebyshev.theta t := by
    intro t
    simp only [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, a,
      Set.indicator_apply, Set.mem_ofPred_eq]
  simp_rw [ha, Real.deriv_rpow_const]
  have hpow : -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) := by norm_num
  rw [hpow]
  have hi : (∫ t in 2..x, -(1 / 2 : ℝ) * t ^ (-(3 / 2 : ℝ)) * Chebyshev.theta t) =
      -(1 / 2 : ℝ) * ∫ t in 2..x, Chebyshev.theta t * t ^ (-(3 / 2 : ℝ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hi]
  ring

theorem rootKernel_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have ht0 : t ≠ 0 := by linarith [ht.1]
  exact (Real.hasDerivAt_rpow_const (Or.inl ht0)).continuousAt

theorem thetaRootKernel_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t * t ^ (-(3 / 2 : ℝ)))
      volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  let a : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have hg : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Icc 2 x) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (Real.hasDerivAt_rpow_const (Or.inl ht0)).continuousAt
  have hh := integrableOn_mul_sum_Icc a (m := 0) (by norm_num : (0 : ℝ) ≤ 2) hg
  convert hh using 1 <;> try rfl
  funext t
  simp [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, a, mul_comm]

theorem rootKernel_integral (x : ℝ) :
    (∫ t in (2 : ℝ)..x, t ^ (-(1 / 2 : ℝ))) =
      2 * (Real.sqrt x - Real.sqrt 2) := by
  have h := integral_rpow (a := (2 : ℝ)) (b := x) (r := -(1 / 2 : ℝ))
    (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ)))
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
  rw [h, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  ring

theorem rootKernel_integral_tendsto :
    Tendsto (fun x : ℝ => ∫ t in (2 : ℝ)..x, t ^ (-(1 / 2 : ℝ))) atTop atTop := by
  have h := (tendsto_atTop_add_const_right atTop (-Real.sqrt 2)
    Real.tendsto_sqrt_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  simpa only [rootKernel_integral, sub_eq_add_neg] using h

theorem rootKernel_integral_ratio_tendsto :
    Tendsto (fun x : ℝ => (∫ t in (2 : ℝ)..x, t ^ (-(1 / 2 : ℝ))) / Real.sqrt x)
      atTop (𝓝 2) := by
  have hz := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul
    (2 * Real.sqrt 2)
  have hc : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hh := hc.sub hz
  simp only [mul_zero, sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [rootKernel_integral]
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  field_simp

theorem thetaRootKernel_average_tendsto :
    Tendsto (fun x : ℝ =>
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t * t ^ (-(3 / 2 : ℝ))) /
        (∫ t in (2 : ℝ)..x, t ^ (-(1 / 2 : ℝ)))) atTop (𝓝 1) := by
  apply weighted_integral_average_tendsto
    (fun _ hx => thetaRootKernel_integrable hx)
    (fun _ hx => rootKernel_integrable hx)
    (fun t ht => Real.rpow_nonneg (by linarith) _)
    rootKernel_integral_tendsto
  intro ε hε
  have hh := Metric.tendsto_nhds.mp theta_ratio_tendsto ε hε
  filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  rw [Real.dist_eq] at ht
  have hp : t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) / t := by
    convert Real.rpow_sub_one ht0.ne' (-(1 / 2 : ℝ)) using 1
    norm_num
  have he : Chebyshev.theta t * t ^ (-(3 / 2 : ℝ)) - 1 * t ^ (-(1 / 2 : ℝ)) =
      (Chebyshev.theta t / t - 1) * t ^ (-(1 / 2 : ℝ)) := by rw [hp]; ring
  rw [he, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  exact mul_le_mul_of_nonneg_right ht.le (Real.rpow_nonneg ht0.le _)

theorem thetaRootKernel_ratio_tendsto :
    Tendsto (fun x : ℝ =>
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t * t ^ (-(3 / 2 : ℝ))) / Real.sqrt x)
      atTop (𝓝 2) := by
  have hh := thetaRootKernel_average_tendsto.mul rootKernel_integral_ratio_tendsto
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [rootKernel_integral_tendsto.eventually (eventually_gt_atTop 0)] with x hx
  field_simp


theorem primeRootSum_ratio_tendsto :
    Tendsto (fun x : ℝ => primeRootSum x / Real.sqrt x) atTop (𝓝 2) := by
  have hh := theta_ratio_tendsto.add (thetaRootKernel_ratio_tendsto.const_mul (1 / 2 : ℝ))
  norm_num only at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [primeRootSum_abel hx]
  have hp : Chebyshev.theta x * x ^ (-(1 / 2 : ℝ)) / Real.sqrt x =
      Chebyshev.theta x / x := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
    calc
      _ = Chebyshev.theta x / (Real.sqrt x * Real.sqrt x) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hx0.le]
  rw [add_div, hp]
  ring

end MatchingEstimate710
end

section
namespace MatchingEstimate710

noncomputable def cofactorProfile (x : ℝ) : ℝ := (1 - x) / (1 + x)

theorem cofactorProfile_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ cofactorProfile x := div_nonneg (sub_nonneg.mpr hx1) (by linarith)

theorem cofactorProfile_le_one {x : ℝ} (hx : 0 ≤ x) : cofactorProfile x ≤ 1 := by
  unfold cofactorProfile
  apply (div_le_iff₀ (by linarith : 0 < 1 + x)).mpr
  linarith

theorem cofactorProfile_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    cofactorProfile b ≤ cofactorProfile a := by
  unfold cofactorProfile
  apply (div_le_div_iff₀ (by linarith : 0 < 1 + b) (by linarith : 0 < 1 + a)).mpr
  nlinarith

theorem cofactorProfile_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cofactorProfile (a + b) ≤ cofactorProfile a * cofactorProfile b := by
  unfold cofactorProfile
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + (a + b))
    (by positivity : 0 < (1 + a) * (1 + b))).mpr
  nlinarith [mul_nonneg (mul_nonneg ha hb) (add_nonneg ha hb)]

theorem add_le_mul_of_two_le {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    a + b ≤ a * b := by
  nlinarith [mul_nonneg (show 0 ≤ a - 2 by linarith) (show 0 ≤ b - 2 by linarith)]

theorem one_sub_mul_exp_le_one (d : ℝ) : (1 - d) * Real.exp d ≤ 1 := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-d))
    (Real.exp_nonneg d)
  simpa only [sub_eq_add_neg, ← Real.exp_add, neg_add_cancel,
    add_neg_cancel, Real.exp_zero, add_comm] using h


theorem scalar_envelope_parametric {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    1 - x ≤ (1 + z) * cofactorProfile
      (Real.sqrt ((z * Real.exp (1 - z)) * (x * Real.exp (x - 1)))) := by
  let d := (x - z) / 2
  have hxz : 0 ≤ x * z := mul_nonneg hx hz
  have hs : 0 ≤ Real.sqrt (x * z) := Real.sqrt_nonneg _
  have he : 0 ≤ Real.exp d := Real.exp_nonneg _
  have ha : 0 ≤ Real.sqrt (x * z) * Real.exp d := mul_nonneg hs he
  have hsq : (z * Real.exp (1 - z)) * (x * Real.exp (x - 1)) =
      (Real.sqrt (x * z) * Real.exp d) ^ 2 := by
    calc
      _ = (x * z) * (Real.exp (1 - z) * Real.exp (x - 1)) := by ring
      _ = (x * z) * Real.exp (x - z) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt hxz, pow_two, ← Real.exp_add]
        congr 2
        dsimp [d]
        ring
  have haeq : Real.sqrt ((z * Real.exp (1 - z)) * (x * Real.exp (x - 1))) =
      Real.sqrt (x * z) * Real.exp d := by
    rw [hsq, Real.sqrt_sq ha]
  have hcoeff : (2 + z - x) * Real.exp d ≤ 2 := by
    have h := one_sub_mul_exp_le_one d
    dsimp [d] at h ⊢
    nlinarith
  have hmid : (2 + z - x) * (Real.sqrt (x * z) * Real.exp d) ≤
      2 * Real.sqrt (x * z) := by
    nlinarith [mul_le_mul_of_nonneg_left hcoeff hs]
  have hamgm : 2 * Real.sqrt (x * z) ≤ x + z := by
    nlinarith [sq_nonneg (x - z), Real.sq_sqrt hxz]
  rw [haeq, cofactorProfile, ← mul_div_assoc]
  apply (le_div_iff₀ (by linarith : 0 < 1 + Real.sqrt (x * z) * Real.exp d)).mpr
  nlinarith


theorem envelope_pointwise_bound {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v) :
    x / ((1 + 2 * x) * v) ≤
      x / 2 + (max (Real.sqrt 2 - Real.sqrt v) 0) ^ 2 / (4 * v) := by
  have hd : 0 < (1 + 2 * x) * v := by positivity
  have hv_sq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv.le
  have h2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases h : Real.sqrt 2 ≤ Real.sqrt v
  · rw [max_eq_right (sub_nonpos.mpr h)]
    simp only [zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
    have hv2 : 2 ≤ v := by
      nlinarith [Real.sqrt_nonneg v, Real.sqrt_nonneg 2]
    have hd2 : 2 ≤ (1 + 2 * x) * v := by
      nlinarith [mul_nonneg hx hv.le]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ x / 2 by positivity) (sub_nonneg.mpr hd2)]
  · rw [max_eq_left (by linarith : 0 ≤ Real.sqrt 2 - Real.sqrt v)]
    apply (div_le_iff₀ hd).mpr
    have hsq : 0 ≤ ((2 * x + 1) * Real.sqrt v - Real.sqrt 2) ^ 2 := sq_nonneg _
    have hsx : (Real.sqrt 2) ^ 2 * x = 2 * x := by rw [h2_sq]
    have hvx : (Real.sqrt v) ^ 2 * x = v * x := by rw [hv_sq]
    have hvxx : (Real.sqrt v) ^ 2 * x ^ 2 = v * x ^ 2 := by rw [hv_sq]
    field_simp
    nlinarith

end MatchingEstimate710
end

section
namespace MatchingEstimate710

theorem list_sum_le_prod_of_two_le (l : List ℝ) (hl : ∀ a ∈ l, 2 ≤ a) :
    l.sum ≤ l.prod ∧ (l ≠ [] → 2 ≤ l.prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 2 ≤ a := hl a (by simp)
    have htail : ∀ b ∈ l, 2 ≤ b := fun b hb => hl b (by simp [hb])
    have hh := ih htail
    by_cases he : l = []
    · subst l
      simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
        List.prod_nil, mul_one, ne_eq, List.cons_ne_self, not_false_eq_true, true_implies]
      exact ⟨le_rfl, ha⟩
    · have hp : 2 ≤ l.prod := hh.2 he
      constructor
      · simp only [List.sum_cons, List.prod_cons]
        calc
          a + l.sum ≤ a + l.prod := by linarith [hh.1]
          _ ≤ a * l.prod := add_le_mul_of_two_le ha hp
      · intro _
        simp only [List.prod_cons]
        nlinarith

theorem cofactorProfile_list (l : List ℝ) (hl : ∀ a ∈ l, 0 ≤ a) (hs : l.sum ≤ 1) :
    cofactorProfile l.sum ≤ (l.map cofactorProfile).prod := by
  induction l with
  | nil => simp [cofactorProfile]
  | cons a l ih =>
    have ha : 0 ≤ a := hl a (by simp)
    have htail : ∀ b ∈ l, 0 ≤ b := fun b hb => hl b (by simp [hb])
    have hsum : 0 ≤ l.sum := List.sum_nonneg htail
    have hs' : a + l.sum ≤ 1 := by simpa only [List.sum_cons] using hs
    have ha1 : a ≤ 1 := by linarith
    have htail1 : l.sum ≤ 1 := by linarith
    have hh := ih htail htail1
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    exact (cofactorProfile_mul ha hsum).trans
      (mul_le_mul_of_nonneg_left hh (cofactorProfile_nonneg ha ha1))

def largeFactors (n : ℕ) : List ℕ := n.primeFactorsList.filter (fun p => 3 < p)

noncomputable def factorWeight (y : ℝ) (p : ℕ) : ℝ :=
  max 0 (cofactorProfile (Real.sqrt ((p : ℝ) / y)))

noncomputable def rho (y : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ((largeFactors n).map (factorWeight y)).prod

theorem factorWeight_nonneg (y : ℝ) (p : ℕ) : 0 ≤ factorWeight y p := le_max_left _ _

theorem factorWeight_le_one (y : ℝ) (p : ℕ) : factorWeight y p ≤ 1 :=
  max_le (by norm_num) (cofactorProfile_le_one (Real.sqrt_nonneg _))

theorem rho_one (y : ℝ) : rho y 1 = 1 := by simp [rho, largeFactors]

theorem rho_two (y : ℝ) : rho y 2 = 1 := by simp [rho, largeFactors]

theorem rho_three (y : ℝ) : rho y 3 = 1 := by
  simp [rho, largeFactors, Nat.primeFactorsList_prime Nat.prime_three]

theorem rho_mul (y : ℝ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    rho y (a * b) = rho y a * rho y b := by
  have hp := ((Nat.perm_primeFactorsList_mul ha hb).filter (fun p => 3 < p)).map
    (factorWeight y)
  simpa [rho, ha, hb, mul_ne_zero ha hb, largeFactors, List.filter_append,
    List.map_append, List.prod_append] using hp.prod_eq

theorem rho_nonneg (y : ℝ) (n : ℕ) : 0 ≤ rho y n := by
  unfold rho
  split_ifs
  · exact le_rfl
  · apply List.prod_nonneg
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    exact factorWeight_nonneg y p

theorem rho_pow (y : ℝ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    rho y (n ^ k) = (rho y n) ^ k := by
  induction k with
  | zero => simp [rho_one]
  | succ k ih => rw [pow_succ, rho_mul y (pow_ne_zero k hn) hn, ih, pow_succ]

theorem rho_two_pow_three_pow (y : ℝ) (a b : ℕ) :
    rho y (2 ^ a * 3 ^ b) = 1 := by
  rw [rho_mul y (pow_ne_zero a (by decide)) (pow_ne_zero b (by decide)),
    rho_pow y (by decide), rho_pow y (by decide), rho_two, rho_three]
  simp

theorem rho_small_prime_part (y : ℝ) (a b : ℕ) {r : ℕ} (hr : r ≠ 0) :
    rho y ((2 ^ a * 3 ^ b) * r) = rho y r := by
  rw [rho_mul y (mul_ne_zero (pow_ne_zero a (by decide)) (pow_ne_zero b (by decide))) hr,
    rho_two_pow_three_pow, one_mul]

theorem list_prod_sqrt (l : List ℕ) :
    (l.map (fun p : ℕ => Real.sqrt (p : ℝ))).prod = Real.sqrt (l.prod : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih,
      Real.sqrt_mul (Nat.cast_nonneg a)]

theorem largeFactors_prod_le {n : ℕ} (hn : n ≠ 0) : (largeFactors n).prod ≤ n := by
  have h := (show List.Sublist (largeFactors n) n.primeFactorsList from List.filter_sublist).prod_le_prod'
    (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).one_lt.le)
  simpa only [largeFactors, Nat.prod_primeFactorsList hn] using h

theorem list_sum_sqrt_div (l : List ℕ) (y : ℝ) :
    (l.map (fun p : ℕ => Real.sqrt ((p : ℝ) / y))).sum =
      (l.map (fun p : ℕ => Real.sqrt (p : ℝ))).sum / Real.sqrt y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, Real.sqrt_div (Nat.cast_nonneg a), add_div]


theorem cofactor_domination {q : ℕ} (hq : q ≠ 0) {y : ℝ}
    (hy : 0 < y) (hqy : (q : ℝ) < y) :
    cofactorProfile (Real.sqrt ((q : ℝ) / y)) ≤ rho y q := by
  let l := largeFactors q
  have htwo : ∀ a ∈ l.map (fun p : ℕ => Real.sqrt (p : ℝ)), 2 ≤ a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    have hp' : p ∈ q.primeFactorsList ∧ 3 < p := by simpa [l, largeFactors] using hp
    apply Real.le_sqrt_of_sq_le
    have hp4 : 4 ≤ p := by omega
    exact_mod_cast hp4
  have hsum : (l.map (fun p : ℕ => Real.sqrt ((p : ℝ) / y))).sum ≤
      Real.sqrt ((q : ℝ) / y) := by
    rw [list_sum_sqrt_div]
    calc
      _ ≤ (l.map (fun p : ℕ => Real.sqrt (p : ℝ))).prod / Real.sqrt y :=
        div_le_div_of_nonneg_right (list_sum_le_prod_of_two_le _ htwo).1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (l.prod : ℝ) / Real.sqrt y := by rw [list_prod_sqrt]
      _ ≤ Real.sqrt (q : ℝ) / Real.sqrt y := div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by exact_mod_cast largeFactors_prod_le hq)) (Real.sqrt_nonneg _)
      _ = _ := (Real.sqrt_div (Nat.cast_nonneg q) y).symm
  have ht : Real.sqrt ((q : ℝ) / y) ≤ 1 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by simpa using (div_le_one hy).mpr hqy.le)
  have hnonneg : ∀ a ∈ l.map (fun p : ℕ => Real.sqrt ((p : ℝ) / y)), 0 ≤ a := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    exact Real.sqrt_nonneg _
  have hprofile := cofactorProfile_list _ hnonneg (hsum.trans ht)
  have hmono := cofactorProfile_antitone (List.sum_nonneg hnonneg) hsum
  have heq : l.map (factorWeight y) =
      l.map (fun p : ℕ => cofactorProfile (Real.sqrt ((p : ℝ) / y))) := by
    apply List.map_congr_left
    intro p hp
    have hp' : p ∈ q.primeFactorsList ∧ 3 < p := by simpa [l, largeFactors] using hp
    have hpq : (p : ℝ) ≤ q := by exact_mod_cast Nat.le_of_mem_primeFactorsList hp'.1
    have hroot : Real.sqrt ((p : ℝ) / y) ≤ 1 :=
      (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
        (by simpa using (div_le_one hy).mpr (hpq.trans hqy.le))
    exact max_eq_right (cofactorProfile_nonneg (Real.sqrt_nonneg _) hroot)
  have hh := hmono.trans hprofile
  simpa only [rho, if_neg hq, List.map_map, Function.comp_def, ← heq] using hh

end MatchingEstimate710
end

section
namespace MatchingEstimate710

theorem factorWeight_lt_one {y : ℝ} (hy : 0 < y) {p : ℕ} (hp : 0 < p) :
    factorWeight y p < 1 := by
  have hs : 0 < Real.sqrt ((p : ℝ) / y) := Real.sqrt_pos.mpr (div_pos (by exact_mod_cast hp) hy)
  apply max_lt_iff.mpr
  refine ⟨zero_lt_one, ?_⟩
  unfold cofactorProfile
  apply (div_lt_iff₀ (by linarith : 0 < 1 + Real.sqrt ((p : ℝ) / y))).mpr
  linarith

theorem factorWeight_eq_profile {y : ℝ} (hy : 0 < y) {p : ℕ} (hp : (p : ℝ) ≤ y) :
    factorWeight y p = cofactorProfile (Real.sqrt ((p : ℝ) / y)) := by
  have hs : Real.sqrt ((p : ℝ) / y) ≤ 1 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by simpa using (div_le_one hy).mpr hp)
  exact max_eq_right (cofactorProfile_nonneg (Real.sqrt_nonneg _) hs)

theorem factorWeight_eq_zero_of_ge {y : ℝ} (hy : 0 < y) {p : ℕ} (hp : y ≤ (p : ℝ)) :
    factorWeight y p = 0 := by
  have hs : 1 ≤ Real.sqrt ((p : ℝ) / y) := Real.le_sqrt_of_sq_le
    (by simpa using (le_div_iff₀ hy).mpr (by simpa using hp))
  apply max_eq_left
  unfold cofactorProfile
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem one_sub_factorWeight {y : ℝ} (hy : 0 < y) {p : ℕ} (hp : (p : ℝ) ≤ y) :
    1 - factorWeight y p =
      2 * Real.sqrt ((p : ℝ) / y) / (1 + Real.sqrt ((p : ℝ) / y)) := by
  rw [factorWeight_eq_profile hy hp, cofactorProfile]
  have hs : 1 + Real.sqrt ((p : ℝ) / y) ≠ 0 := by positivity
  field_simp
  ring

theorem factorWeight_odds {y : ℝ} (hy : 0 < y) {p : ℕ}
    (hp0 : 0 < p) (hpy : (p : ℝ) ≤ y) :
    factorWeight y p / (1 - factorWeight y p) = (Real.sqrt (y / (p : ℝ)) - 1) / 2 := by
  have hs : 0 < Real.sqrt ((p : ℝ) / y) :=
    Real.sqrt_pos.mpr (div_pos (by exact_mod_cast hp0) hy)
  have hinv : Real.sqrt (y / (p : ℝ)) = (Real.sqrt ((p : ℝ) / y))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  rw [one_sub_factorWeight hy hpy, factorWeight_eq_profile hy hpy, cofactorProfile, hinv]
  field_simp

end MatchingEstimate710
end

section
open Filter
open scoped Topology BigOperators


namespace MatchingEstimate710

noncomputable def largePrimeRange (y : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊y⌋₊).filter (fun p => 3 < p)

theorem mem_largePrimeRange {y : ℝ} {p : ℕ} :
    p ∈ largePrimeRange y ↔ p ≤ ⌊y⌋₊ ∧ p.Prime ∧ 3 < p := by
  simp only [largePrimeRange, Finset.mem_filter, Nat.mem_primesLE, and_assoc]

theorem sum_largePrimeRange (g : ℕ → ℝ) {y : ℝ} (hy : 3 ≤ y) :
    (∑ p ∈ largePrimeRange y, g p) = (∑ p ∈ Nat.primesLE ⌊y⌋₊, g p) - g 2 - g 3 := by
  classical
  have hp2 : 2 ∈ Nat.primesLE ⌊y⌋₊ :=
    Nat.mem_primesLE.mpr ⟨Nat.le_floor (by norm_num only [Nat.cast_ofNat]; linarith), Nat.prime_two⟩
  have hp3 : 3 ∈ Nat.primesLE ⌊y⌋₊ :=
    Nat.mem_primesLE.mpr ⟨Nat.le_floor hy, Nat.prime_three⟩
  have hs : Nat.primesLE ⌊y⌋₊ = {2, 3} ∪ largePrimeRange y := by
    ext p
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, mem_largePrimeRange]
    constructor
    · intro hp
      have h := Nat.mem_primesLE.mp hp
      by_cases hp3 : 3 < p
      · exact Or.inr ⟨h.1, h.2, hp3⟩
      · have h2 := h.2.two_le
        omega
    · rintro ((rfl | rfl) | h)
      · exact hp2
      · exact hp3
      · exact Nat.mem_primesLE.mpr ⟨h.1, h.2.1⟩
  have hd : Disjoint ({2, 3} : Finset ℕ) (largePrimeRange y) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hh := (mem_largePrimeRange.mp hq).2.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  rw [hs, Finset.sum_union hd]
  simp only [Finset.sum_insert (by norm_num : (2 : ℕ) ∉ ({3} : Finset ℕ)),
    Finset.sum_singleton]
  ring

noncomputable def primeLogMean (y : ℝ) : ℝ :=
  ∑ p ∈ largePrimeRange y,
    Real.log p * (factorWeight y p / (1 - factorWeight y p))

theorem primeLogMean_identity {y : ℝ} (hy : 3 ≤ y) :
    primeLogMean y = (Real.sqrt y / 2) *
      (primeRootSum y - Real.log 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) -
        Real.log 3 * (3 : ℝ) ^ (-(1 / 2 : ℝ))) -
      (1 / 2 : ℝ) * (Chebyshev.theta y - Real.log 2 - Real.log 3) := by
  have hy0 : 0 < y := by linarith
  have hs : primeLogMean y = ∑ p ∈ largePrimeRange y,
      ((Real.sqrt y / 2) * (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))) -
        (1 / 2 : ℝ) * Real.log p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have h := mem_largePrimeRange.mp hp
    have hpy : (p : ℝ) ≤ y := (Nat.cast_le.mpr h.1).trans (Nat.floor_le hy0.le)
    rw [factorWeight_odds hy0 h.2.1.pos hpy, Real.sqrt_div hy0.le,
      Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow]
    ring
  rw [hs, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_largePrimeRange _ hy, sum_largePrimeRange _ hy]
  rw [← Chebyshev.theta_eq_sum_primesLE]
  have hroot : (∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))) =
      primeRootSum y := by simp only [primeRootSum, Nat.primesLE_eq_filter_Icc_zero]
  rw [hroot]
  norm_num only [Nat.cast_ofNat]


theorem primeLogMean_ratio_tendsto :
    Tendsto (fun y : ℝ => primeLogMean y / y) atTop (𝓝 (1 / 2)) := by
  let C := Real.log 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) +
    Real.log 3 * (3 : ℝ) ^ (-(1 / 2 : ℝ))
  let D := Real.log 2 + Real.log 3
  have hC := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul (C / 2)
  have hD := (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).const_mul (D / 2)
  have hh := ((primeRootSum_ratio_tendsto.const_mul (1 / 2 : ℝ)).sub hC).sub
    (theta_ratio_tendsto.const_mul (1 / 2 : ℝ))
  have hh' := hh.add hD
  norm_num only [mul_zero, sub_zero, add_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with y hy
  simp only [Function.comp_apply]
  rw [primeLogMean_identity hy]
  have hy0 : 0 < y := by linarith
  have hs : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy0)
  have hsq := Real.mul_self_sqrt hy0.le
  dsimp [C, D]
  field_simp
  linear_combination -(primeRootSum y -
    (Real.log 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) +
      Real.log 3 * (3 : ℝ) ^ (-(1 / 2 : ℝ)))) * hsq

end MatchingEstimate710
end

section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators


namespace MatchingEstimate710

abbrev PrimeIndex (y : ℝ) := ↥(largePrimeRange y)

noncomputable def primeParameter (y : ℝ) (p : ℕ) : unitInterval :=
  ⟨1 - factorWeight y p,
    ⟨sub_nonneg.mpr (factorWeight_le_one y p), by linarith [factorWeight_nonneg y p]⟩⟩

theorem primeParameter_ne_zero {y : ℝ} (hy : 0 < y) (p : PrimeIndex y) :
    primeParameter y p ≠ 0 := by
  have hp := (mem_largePrimeRange.mp p.property).2.1.pos
  have hh := factorWeight_lt_one hy hp
  intro he
  have hc := congrArg (fun q : unitInterval => (q : ℝ)) he
  change 1 - factorWeight y p = 0 at hc
  linarith

noncomputable def primeDistribution (y : ℝ) : Measure (PrimeIndex y → ℕ) :=
  geometricProduct (fun p => primeParameter y p)

noncomputable def primeLogValue (y : ℝ) : (PrimeIndex y → ℕ) → ℝ :=
  weightedExponent (fun p => Real.log (p : ℕ))

instance primeDistribution_probability (y : ℝ) : IsProbabilityMeasure (primeDistribution y) := by
  unfold primeDistribution
  infer_instance

theorem primeLogValue_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (primeLogValue y) (primeDistribution y) :=
  weightedExponent_integrable _ (primeParameter_ne_zero hy) _

theorem primeLogValue_mean {y : ℝ} (hy : 0 < y) :
    (∫ z, primeLogValue y z ∂primeDistribution y) = primeLogMean y := by
  rw [primeLogValue, primeDistribution, weightedExponent_mean _ (primeParameter_ne_zero hy)]
  simp only [primeParameter, sub_sub_cancel, primeLogMean]
  exact (largePrimeRange y).sum_coe_sort
    (fun p : ℕ => Real.log p * (factorWeight y p / (1 - factorWeight y p)))

theorem sqrt_ratio_le_primeParameter {y : ℝ} (hy : 0 < y) {p : ℕ} (hpy : (p : ℝ) ≤ y) :
    Real.sqrt ((p : ℝ) / y) ≤ (primeParameter y p : ℝ) := by
  change Real.sqrt ((p : ℝ) / y) ≤ 1 - factorWeight y p
  rw [one_sub_factorWeight hy hpy]
  have hs0 := Real.sqrt_nonneg ((p : ℝ) / y)
  have hs1 : Real.sqrt ((p : ℝ) / y) ≤ 1 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by simpa using (div_le_one hy).mpr hpy)
  apply (le_div_iff₀ (by positivity : 0 < 1 + Real.sqrt ((p : ℝ) / y))).mpr
  nlinarith

theorem prime_tilt_exponent_bound {y δ : ℝ} (hy : 0 < y) (hδ : 0 ≤ δ) (p : PrimeIndex y) :
    0 ≤ (δ / (2 * Real.sqrt y)) * Real.log (p : ℕ) ∧
      (δ / (2 * Real.sqrt y)) * Real.log (p : ℕ) ≤ δ * (primeParameter y p : ℝ) := by
  have hm := mem_largePrimeRange.mp p.property
  have hpy : (p : ℝ) ≤ y := (Nat.cast_le.mpr hm.1).trans (Nat.floor_le hy.le)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hm.2.1.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hm.2.1.one_le
  constructor
  · exact mul_nonneg (by positivity) (Real.log_nonneg hp1)
  · have hlog : Real.log (p : ℕ) ≤ 2 * Real.sqrt (p : ℕ) := by
      have h := Real.log_le_rpow_div (le_of_lt hp0) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    calc
      _ ≤ (δ / (2 * Real.sqrt y)) * (2 * Real.sqrt (p : ℕ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = δ * Real.sqrt ((p : ℝ) / y) := by
        rw [Real.sqrt_div (le_of_lt hp0)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_ratio_le_primeParameter hy hpy) hδ

theorem primeDistribution_tilt_bound {y δ : ℝ} (hy : 0 < y) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : δ * (1 + δ) < 1) (T : ℝ) :
    (primeDistribution y).real {z | T ≤ primeLogValue y z} ≤
      Real.exp (-(δ / (2 * Real.sqrt y)) * (T - tiltFactor δ * primeLogMean y)) := by
  have hh := geometricProduct_small_tilt (fun p : PrimeIndex y => primeParameter y p)
    (primeParameter_ne_zero hy) (fun p => Real.log (p : ℕ))
    (by positivity : 0 < δ / (2 * Real.sqrt y)) hδ0.le hδ1 hδ
    (fun p => (prime_tilt_exponent_bound hy hδ0.le p).1)
    (fun p => (prime_tilt_exponent_bound hy hδ0.le p).2) T
  have hsum : (∑ p : PrimeIndex y,
      Real.log (p : ℕ) * (factorWeight y p / (1 - factorWeight y p))) = primeLogMean y :=
    (largePrimeRange y).sum_coe_sort
      (fun p : ℕ => Real.log p * (factorWeight y p / (1 - factorWeight y p)))
  simpa only [primeDistribution, primeLogValue, primeParameter, sub_sub_cancel, hsum] using hh

theorem primeLogMean_scaled_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun L : ℝ => primeLogMean (β * L) / L) atTop (𝓝 (β / 2)) := by
  have hh := (primeLogMean_ratio_tendsto.comp (tendsto_id.const_mul_atTop hβ)).mul_const β
  have hlimit : (1 / 2 : ℝ) * β = β / 2 := by ring
  rw [hlimit] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  dsimp only [Function.comp_apply, id_eq]
  field_simp


theorem primeDistribution_exponential_concentration {β θ : ℝ} (hβ : 0 < β)
    (hθ : β / 2 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℝ in atTop,
      (primeDistribution (β * L)).real {z | θ * L ≤ primeLogValue (β * L) z} ≤
        Real.exp (-c * Real.sqrt L) := by
  let ε := (θ - β / 2) / β
  have hε : 0 < ε := div_pos (by linarith) hβ
  obtain ⟨δ, hδ0, hδ1, hδ, hK⟩ := exists_small_tilt hε
  have hK0 : 0 < tiltFactor δ := by
    unfold tiltFactor
    exact div_pos (by linarith) (by linarith)
  have hKθ : tiltFactor δ * (β / 2) < θ := by
    have hh := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ β / 2)
    dsimp [ε] at hh
    have hb0 : β ≠ 0 := hβ.ne'
    field_simp at hh
    nlinarith
  let α := (θ - tiltFactor δ * (β / 2)) / 2
  have hα : 0 < α := by dsimp [α]; linarith
  have hlim : Tendsto (fun L : ℝ => θ - tiltFactor δ * (primeLogMean (β * L) / L))
      atTop (𝓝 (θ - tiltFactor δ * (β / 2))) :=
    tendsto_const_nhds.sub ((primeLogMean_scaled_tendsto hβ).const_mul (tiltFactor δ))
  have hg : ∀ᶠ L : ℝ in atTop, α < θ - tiltFactor δ * (primeLogMean (β * L) / L) :=
    hlim.eventually (eventually_gt_nhds (by dsimp [α]; linarith))
  let c := δ * α / (2 * Real.sqrt β)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [hg, eventually_gt_atTop (0 : ℝ)] with L hgap hL
  have hy : 0 < β * L := mul_pos hβ hL
  have hgap' : α * L ≤ θ * L - tiltFactor δ * primeLogMean (β * L) := by
    have hh := mul_le_mul_of_nonneg_right hgap.le hL.le
    rwa [sub_mul, mul_assoc, div_mul_cancel₀ _ hL.ne'] at hh
  calc
    _ ≤ Real.exp (-(δ / (2 * Real.sqrt (β * L))) *
        (θ * L - tiltFactor δ * primeLogMean (β * L))) :=
      primeDistribution_tilt_bound hy hδ0 hδ1 hδ (θ * L)
    _ ≤ Real.exp (-(δ / (2 * Real.sqrt (β * L))) * (α * L)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hgap'
        (neg_nonpos.mpr (by positivity : 0 ≤ δ / (2 * Real.sqrt (β * L))))
    _ = _ := by
      congr 1
      rw [Real.sqrt_mul hβ.le]
      dsimp [c]
      have hsβ : Real.sqrt β ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hβ)
      have hsL : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
      have hsq := Real.mul_self_sqrt hL.le
      field_simp
      nlinarith [hsq]

end MatchingEstimate710
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators


namespace MatchingEstimate710

noncomputable def rhoHom (y : ℝ) : ℕ →* ℝ where
  toFun := rho y
  map_one' := rho_one y
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha, rho]
    by_cases hb : b = 0
    · simp [hb, rho]
    exact rho_mul y ha hb

theorem rho_prime {y : ℝ} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    rho y p = factorWeight y p := by
  simp [rho, largeFactors, Nat.primeFactorsList_prime hp, hp3, hp.ne_zero]

noncomputable def primeInteger (y : ℝ) (z : PrimeIndex y → ℕ) : ℕ :=
  ∏ p : PrimeIndex y, (p : ℕ) ^ z p

theorem primeInteger_pos (y : ℝ) (z : PrimeIndex y → ℕ) : 0 < primeInteger y z := by
  classical
  unfold primeInteger
  apply Finset.prod_pos
  intro p _
  exact pow_pos (mem_largePrimeRange.mp p.property).2.1.pos _

theorem rho_primeInteger (y : ℝ) (z : PrimeIndex y → ℕ) :
    rho y (primeInteger y z) = ∏ p : PrimeIndex y, factorWeight y p ^ z p := by
  classical
  change rhoHom y (∏ p : PrimeIndex y, (p : ℕ) ^ z p) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p _
  rw [map_pow]
  change rho y (p : ℕ) ^ z p = _
  rw [rho_prime (mem_largePrimeRange.mp p.property).2.1
    (mem_largePrimeRange.mp p.property).2.2]

theorem primeInteger_factorization (y : ℝ) (z : PrimeIndex y → ℕ) (q : PrimeIndex y) :
    (primeInteger y z).factorization q = z q := by
  classical
  unfold primeInteger
  rw [Nat.factorization_prod (fun p _ =>
    pow_ne_zero _ (mem_largePrimeRange.mp p.property).2.1.ne_zero)]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single q]
  · rw [(mem_largePrimeRange.mp q.property).2.1.factorization_pow,
      Finsupp.single_eq_same]
  · intro p _ hpq
    rw [(mem_largePrimeRange.mp p.property).2.1.factorization_pow,
      Finsupp.single_eq_of_ne (fun h => hpq (Subtype.ext h.symm))]
  · simp

theorem primeInteger_injective (y : ℝ) : Function.Injective (primeInteger y) := by
  intro z w h
  funext p
  have hh := congrArg (fun n : ℕ => n.factorization p) h
  simpa only [primeInteger_factorization] using hh

theorem log_primeInteger (y : ℝ) (z : PrimeIndex y → ℕ) :
    Real.log (primeInteger y z : ℝ) = primeLogValue y z := by
  classical
  unfold primeInteger primeLogValue weightedExponent
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
    ring
  · intro p _
    have hp := (mem_largePrimeRange.mp p.property).2.1.pos
    positivity

noncomputable def primeMassNormalizer (y : ℝ) : ℝ :=
  (∏ p : PrimeIndex y, (1 - factorWeight y p))⁻¹

theorem primeMassNormalizer_pos {y : ℝ} (hy : 0 < y) : 0 < primeMassNormalizer y := by
  classical
  unfold primeMassNormalizer
  apply inv_pos.mpr
  apply Finset.prod_pos
  intro p _
  exact sub_pos.mpr (factorWeight_lt_one hy (mem_largePrimeRange.mp p.property).2.1.pos)

theorem primeDistribution_singleton {y : ℝ} (hy : 0 < y) (z : PrimeIndex y → ℕ) :
    (primeDistribution y).real {z} = rho y (primeInteger y z) / primeMassNormalizer y := by
  classical
  change (Measure.pi (fun p : PrimeIndex y => geometricMeasure (primeParameter y p))).real {z} = _
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  have he (p : PrimeIndex y) :
      (geometricMeasure (primeParameter y p) {z p}).toReal =
        factorWeight y p ^ z p * (1 - factorWeight y p) := by
    change (geometricMeasure (primeParameter y p)).real {z p} = _
    rw [geometricMeasure_real_singleton (primeParameter_ne_zero hy p)]
    simp only [primeParameter, sub_sub_cancel]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, rho_primeInteger]
  simp only [primeMassNormalizer, div_eq_mul_inv, inv_inv]

end MatchingEstimate710
end

section
open scoped BigOperators


namespace MatchingEstimate710

theorem primeInteger_factorization_outside (y : ℝ) (z : PrimeIndex y → ℕ) {q : ℕ}
    (hq : q ∉ largePrimeRange y) : (primeInteger y z).factorization q = 0 := by
  classical
  unfold primeInteger
  rw [Nat.factorization_prod (fun p _ =>
    pow_ne_zero _ (mem_largePrimeRange.mp p.property).2.1.ne_zero), Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro p _
  rw [(mem_largePrimeRange.mp p.property).2.1.factorization_pow]
  apply Finsupp.single_eq_of_ne
  intro he
  exact hq (he ▸ p.property)

theorem primeInteger_not_dvd_two (y : ℝ) (z : PrimeIndex y → ℕ) :
    ¬2 ∣ primeInteger y z := by
  rw [Nat.prime_two.dvd_iff_one_le_factorization (primeInteger_pos y z).ne',
    primeInteger_factorization_outside y z]
  · omega
  · intro h
    have hh := (mem_largePrimeRange.mp h).2.2
    omega

theorem primeInteger_not_dvd_three (y : ℝ) (z : PrimeIndex y → ℕ) :
    ¬3 ∣ primeInteger y z := by
  rw [Nat.prime_three.dvd_iff_one_le_factorization (primeInteger_pos y z).ne',
    primeInteger_factorization_outside y z]
  · omega
  · intro h
    have hh := (mem_largePrimeRange.mp h).2.2
    omega

theorem rho_eq_zero_of_large_prime_dvd {y : ℝ} (hy : 0 < y) {p m : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpy : y ≤ (p : ℝ)) (hpm : p ∣ m) :
    rho y m = 0 := by
  obtain ⟨k, rfl⟩ := hpm
  change rhoHom y (p * k) = 0
  rw [map_mul]
  change rho y p * rho y k = 0
  rw [rho_prime hp hp3, factorWeight_eq_zero_of_ge hy hpy, zero_mul]

noncomputable def primeExponents (y : ℝ) (m : ℕ) (p : PrimeIndex y) : ℕ :=
  m.factorization p

theorem primeInteger_of_support_subset {y : ℝ} {m : ℕ} (hm : m ≠ 0)
    (hs : m.factorization.support ⊆ largePrimeRange y) :
    primeInteger y (primeExponents y m) = m := by
  classical
  unfold primeInteger primeExponents
  calc
    _ = ∏ p ∈ largePrimeRange y, p ^ m.factorization p :=
      (largePrimeRange y).prod_coe_sort (fun p : ℕ => p ^ m.factorization p)
    _ = ∏ p ∈ m.factorization.support, p ^ m.factorization p := by
      symm
      apply Finset.prod_subset hs
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]
    _ = m := Nat.prod_factorization_pow_eq_self hm

theorem prime_support_of_rho_ne_zero {y : ℝ} (hy : 0 < y) {m : ℕ}
    (h2 : ¬2 ∣ m) (h3 : ¬3 ∣ m) (hr : rho y m ≠ 0) :
    m.factorization.support ⊆ largePrimeRange y := by
  intro p hp
  have hpf : p ∈ m.primeFactors := hp
  have hprime := Nat.prime_of_mem_primeFactors hpf
  have hpm := Nat.dvd_of_mem_primeFactors hpf
  have hp3 : 3 < p := by
    have hp2 := hprime.two_le
    have hne2 : p ≠ 2 := by rintro rfl; exact h2 hpm
    have hne3 : p ≠ 3 := by rintro rfl; exact h3 hpm
    omega
  have hpy : (p : ℝ) < y := by
    by_contra h
    exact hr (rho_eq_zero_of_large_prime_dvd hy hprime hp3 (le_of_not_gt h) hpm)
  exact mem_largePrimeRange.mpr ⟨Nat.le_floor hpy.le, hprime, hp3⟩

theorem primeInteger_reconstructs_nonzero_weight {y : ℝ} (hy : 0 < y) {m : ℕ}
    (hm : m ≠ 0) (h2 : ¬2 ∣ m) (h3 : ¬3 ∣ m) (hr : rho y m ≠ 0) :
    primeInteger y (primeExponents y m) = m :=
  primeInteger_of_support_subset hm (prime_support_of_rho_ne_zero hy h2 h3 hr)

def core23 (m : ℕ) : ℕ := ordCompl[3] (ordCompl[2] m)

theorem core23_pos {m : ℕ} (hm : m ≠ 0) : 0 < core23 m :=
  Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 hm).ne'

theorem core23_not_dvd_two {m : ℕ} (hm : m ≠ 0) : ¬2 ∣ core23 m := by
  intro h
  exact Nat.not_dvd_ordCompl Nat.prime_two hm (h.trans (Nat.ordCompl_dvd _ 3))

theorem core23_not_dvd_three {m : ℕ} (hm : m ≠ 0) : ¬3 ∣ core23 m :=
  Nat.not_dvd_ordCompl Nat.prime_three (Nat.ordCompl_pos 2 hm).ne'

theorem core23_decomposition (m : ℕ) :
    (2 ^ m.factorization 2 * 3 ^ (ordCompl[2] m).factorization 3) * core23 m = m := by
  unfold core23
  rw [mul_assoc, Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]

theorem rho_core23 (y : ℝ) {m : ℕ} (hm : m ≠ 0) : rho y (core23 m) = rho y m := by
  have h := rho_small_prime_part y (m.factorization 2) ((ordCompl[2] m).factorization 3)
    (core23_pos hm).ne'
  rw [core23_decomposition] at h
  exact h.symm

theorem core23_le (m : ℕ) : core23 m ≤ m :=
  (Nat.ordCompl_le _ 3).trans (Nat.ordCompl_le _ 2)

end MatchingEstimate710
end

section
open MeasureTheory Set


namespace MatchingEstimate710

theorem primeInteger_measurable (y : ℝ) : Measurable (primeInteger y) :=
  measurable_of_countable _

noncomputable def arithmeticPrimeMeasure (y : ℝ) : Measure ℕ :=
  (primeDistribution y).map (primeInteger y)

instance arithmeticPrimeMeasure_probability (y : ℝ) :
    IsProbabilityMeasure (arithmeticPrimeMeasure y) := by
  unfold arithmeticPrimeMeasure
  exact Measure.isProbabilityMeasure_map (primeInteger_measurable y).aemeasurable

theorem arithmeticPrimeMeasure_singleton {y : ℝ} (hy : 0 < y) {m : ℕ}
    (hm : m ≠ 0) (h2 : ¬2 ∣ m) (h3 : ¬3 ∣ m) :
    (arithmeticPrimeMeasure y).real {m} = rho y m / primeMassNormalizer y := by
  classical
  rw [arithmeticPrimeMeasure, measureReal_def,
    Measure.map_apply (primeInteger_measurable y) (measurableSet_singleton m)]
  by_cases hex : ∃ z, primeInteger y z = m
  · obtain ⟨z, rfl⟩ := hex
    have hp : (primeInteger y) ⁻¹' {primeInteger y z} = {z} := by
      ext w
      simp only [mem_preimage, mem_singleton_iff]
      exact (primeInteger_injective y).eq_iff
    rw [hp]
    exact primeDistribution_singleton hy z
  · have hr : rho y m = 0 := by
      by_contra hr
      exact hex ⟨primeExponents y m, primeInteger_reconstructs_nonzero_weight hy hm h2 h3 hr⟩
    have hp : (primeInteger y) ⁻¹' {m} = ∅ := by
      ext z
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hz
      exact hex ⟨z, hz⟩
    rw [hp, measure_empty, ENNReal.toReal_zero, hr, zero_div]

theorem arithmeticPrimeMeasure_small_factor_zero (y : ℝ) {m : ℕ}
    (h : 2 ∣ m ∨ 3 ∣ m) : (arithmeticPrimeMeasure y) {m} = 0 := by
  rw [arithmeticPrimeMeasure,
    Measure.map_apply (primeInteger_measurable y) (measurableSet_singleton m)]
  have hp : (primeInteger y) ⁻¹' {m} = ∅ := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro hz
    rcases h with h2 | h3
    · exact primeInteger_not_dvd_two y z (hz ▸ h2)
    · exact primeInteger_not_dvd_three y z (hz ▸ h3)
  rw [hp, measure_empty]

end MatchingEstimate710
end

section
namespace MatchingEstimate710

theorem log_two_div_log_three_irrational :
    Irrational (Real.log 2 / Real.log 3) := by
  rintro ⟨r, hr⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrpos : (0 : ℚ) < r := by
    have h : (0 : ℝ) < (r : ℝ) := by rw [hr]; exact div_pos hlog2 hlog3
    exact_mod_cast h
  have hnum : 0 ≤ r.num := (Rat.num_pos.mpr hrpos).le
  have hnumcast : (r.num : ℝ) = (r.num.natAbs : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnum)
    simpa only [Int.cast_natCast] using h.symm
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.pos.ne'
  have hcross : (r.num.natAbs : ℝ) * Real.log 3 = Real.log 2 * (r.den : ℝ) := by
    have h := (div_eq_div_iff hden hlog3.ne').mp
      (show (r.num : ℝ) / (r.den : ℝ) = Real.log 2 / Real.log 3 by
        simpa only [Rat.cast_def] using hr)
    simpa only [hnumcast] using h
  have hpowers : (2 : ℝ) ^ r.den = (3 : ℝ) ^ r.num.natAbs := by
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
    rw [Real.log_pow, Real.log_pow]
    nlinarith [hcross]
  have hpowers_nat : (2 : ℕ) ^ r.den = (3 : ℕ) ^ r.num.natAbs := by
    exact_mod_cast hpowers
  have htwo : (2 : ℕ) ∣ (3 : ℕ) ^ r.num.natAbs :=
    hpowers_nat ▸ dvd_pow_self 2 r.pos.ne'
  have hbad := Nat.prime_two.dvd_of_dvd_pow htwo
  norm_num at hbad

end MatchingEstimate710
end

section
open Filter MeasureTheory
open scoped Topology BigOperators


namespace MatchingEstimate710

theorem tendsto_zero_of_dense_span
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (B : ℕ → E →L[𝕜] F) (S : Set E) (C : ℝ)
    (hB : ∀ n, ‖B n‖ ≤ C)
    (hS : (Submodule.span 𝕜 S).topologicalClosure = ⊤)
    (hgen : ∀ x ∈ S, Tendsto (fun n => B n x) atTop (𝓝 0)) :
    ∀ x, Tendsto (fun n => B n x) atTop (𝓝 0) := by
  have hequi : Equicontinuous (fun n x => B n x) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun d => C * d)
      (by
        have hc : Continuous (fun d : ℝ => C * d) := continuous_const.mul continuous_id
        simpa using hc.tendsto (0 : ℝ))
    intro x y n
    calc
      dist (B n x) (B n y) = ‖B n (x - y)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖B n‖ * ‖x - y‖ := (B n).le_opNorm _
      _ ≤ C * dist x y := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _)
  let M : Submodule 𝕜 E :=
    { carrier := {x | Tendsto (fun n => B n x) atTop (𝓝 0)}
      zero_mem' := by
        change Tendsto (fun n => B n 0) atTop (𝓝 0)
        simp
      add_mem' := by
        intro x y hx hy
        change Tendsto (fun n => B n (x + y)) atTop (𝓝 0)
        simpa only [map_add, add_zero] using hx.add hy
      smul_mem' := by
        intro c x hx
        change Tendsto (fun n => B n (c • x)) atTop (𝓝 0)
        simpa only [map_smul, smul_zero] using hx.const_smul c }
  have hclosed : IsClosed (M : Set E) :=
    hequi.isClosed_setOfPred_tendsto continuous_const
  have hspan : Submodule.span 𝕜 S ≤ M := Submodule.span_le.mpr hgen
  have hh := (Submodule.span 𝕜 S).topologicalClosure_minimal hspan hclosed
  rw [hS] at hh
  intro x
  exact hh (Submodule.mem_top)

abbrev RotationCircle := AddCircle (1 : ℝ)

noncomputable def circleShift (a : RotationCircle) (i : ℕ) : C(RotationCircle, RotationCircle) :=
  ⟨fun x => x + i • a, continuous_id.add continuous_const⟩

noncomputable def circlePull (a : RotationCircle) (i : ℕ) :
    C(RotationCircle, ℂ) →L[ℂ] C(RotationCircle, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (circleShift a i)

noncomputable def circleAverage (a : RotationCircle) (n : ℕ) :
    C(RotationCircle, ℂ) →L[ℂ] C(RotationCircle, ℂ) :=
  ((n + 1 : ℂ)⁻¹) • ∑ i ∈ Finset.range (n + 1), circlePull a i

theorem circleAverage_apply (a : RotationCircle) (n : ℕ)
    (f : C(RotationCircle, ℂ)) (x : RotationCircle) :
    circleAverage a n f x = (n + 1 : ℂ)⁻¹ *
      ∑ i ∈ Finset.range (n + 1), f (x + i • a) := by
  simp [circleAverage, circlePull, circleShift]

theorem circleAverage_norm_le (a : RotationCircle) (n : ℕ) :
    ‖circleAverage a n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  rw [circleAverage_apply, norm_mul]
  calc
    _ ≤ ‖(n + 1 : ℂ)⁻¹‖ * ∑ i ∈ Finset.range (n + 1), ‖f (x + i • a)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(n + 1 : ℂ)⁻¹‖ * ((n + 1 : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (Finset.sum_le_sum (fun i _ => f.norm_coe_le_norm (x + i • a))).trans_eq (by simp)
    _ = ‖f‖ := by
      have hn : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
        rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
      rw [norm_inv, hn, inv_mul_cancel_left₀ (by positivity : (n + 1 : ℝ) ≠ 0)]

theorem circle_map_integrable (f : C(RotationCircle, ℂ)) :
    Integrable f AddCircle.haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

noncomputable def circleIntegral : C(RotationCircle, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂AddCircle.haarAddCircle
      map_add' := fun f g => integral_add (circle_map_integrable f) (circle_map_integrable g)
      map_smul' := fun c f => integral_smul c f }
    1 (fun f => by
      simpa using (norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure RotationCircle))
        (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))))

theorem circleIntegral_apply (f : C(RotationCircle, ℂ)) :
    circleIntegral f = ∫ x, f x ∂AddCircle.haarAddCircle := rfl

theorem circleIntegral_norm_le : ‖circleIntegral‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa [circleIntegral_apply] using
    (norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure RotationCircle))
      (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x)))

noncomputable def circleMean :
    C(RotationCircle, ℂ) →L[ℂ] C(RotationCircle, ℂ) :=
  (ContinuousLinearMap.const ℂ RotationCircle).comp circleIntegral

theorem circleMean_apply (f : C(RotationCircle, ℂ)) (x : RotationCircle) :
    circleMean f x = ∫ y, f y ∂AddCircle.haarAddCircle := rfl

theorem circleMean_norm_le : ‖circleMean‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  rw [circleMean_apply]
  simpa using (norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure RotationCircle))
    (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm y)))

noncomputable def circleError (a : RotationCircle) (n : ℕ) :
    C(RotationCircle, ℂ) →L[ℂ] C(RotationCircle, ℂ) :=
  circleAverage a n - circleMean

theorem circleError_norm_le (a : RotationCircle) (n : ℕ) :
    ‖circleError a n‖ ≤ 2 := by
  change ‖circleAverage a n - circleMean‖ ≤ 2
  have hh : ‖circleAverage a n - circleMean‖ ≤ ‖circleAverage a n‖ + ‖circleMean‖ :=
    norm_sub_le (circleAverage a n) circleMean
  linarith [circleAverage_norm_le a n, circleMean_norm_le]

theorem character_add (k : ℤ) (x y : RotationCircle) :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem character_nsmul (k : ℤ) (a : RotationCircle) (n : ℕ) :
    fourier k (n • a) = (fourier k a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, character_add, ih, pow_succ]

theorem circleAverage_character (a : RotationCircle) (n : ℕ) (k : ℤ) :
    circleAverage a n (fourier k) =
      ((n + 1 : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), (fourier k a) ^ i) • fourier k := by
  ext x
  rw [circleAverage_apply]
  simp only [character_add, character_nsmul, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem circleIntegral_character (k : ℤ) :
    circleIntegral (fourier k) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa [circleIntegral_apply, fourierCoeff, Pi.single_apply, eq_comm] using h

theorem circleMean_character (k : ℤ) :
    circleMean (fourier k) = if k = 0 then fourier 0 else 0 := by
  ext x
  simp only [circleMean_apply, ← circleIntegral_apply, circleIntegral_character]
  split_ifs <;> simp

private theorem complex_nat_succ_norm (n : ℕ) :
    ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
  rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]

theorem geometric_average_tendsto {q : ℂ} (hq : q ≠ 1) (hqn : ‖q‖ = 1) :
    Tendsto (fun n : ℕ => (n + 1 : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), q ^ i)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      ‖(n + 1 : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1), q ^ i‖ ≤
        (n + 1 : ℝ)⁻¹ * (2 / ‖q - 1‖) := by
    rw [geom_sum_eq hq, norm_mul, norm_inv, norm_div, complex_nat_succ_norm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖q ^ (n + 1) - 1‖ ≤ ‖q ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow, hqn]; norm_num
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  simpa using (tendsto_inv_atTop_zero.comp hn).mul_const (2 / ‖q - 1‖)

theorem circleError_character_tendsto (a : RotationCircle)
    (ha : ∀ k : ℤ, k ≠ 0 → fourier k a ≠ 1) (k : ℤ) :
    Tendsto (fun n => circleError a n (fourier k)) atTop (𝓝 0) := by
  by_cases hk : k = 0
  · subst k
    have hz (n : ℕ) : circleError a n (fourier 0) = 0 := by
      rw [circleError, sub_apply, circleAverage_character,
        circleMean_character]
      have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      simp [hn]
    simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : C(RotationCircle, ℂ))) atTop (𝓝 0))
  · have hh := (geometric_average_tendsto (ha k hk)
        (by rw [fourier_apply]; exact Circle.norm_coe _ : ‖fourier k a‖ = 1)).smul_const (fourier (T := (1 : ℝ)) k)
    have hz : (0 : ℂ) • (fourier (T := (1 : ℝ)) k) = 0 := by
      ext x
      simp
    rw [hz] at hh
    simpa [circleError, sub_apply, circleAverage_character, circleMean_character, hk] using hh

theorem circleError_tendsto (a : RotationCircle)
    (ha : ∀ k : ℤ, k ≠ 0 → fourier k a ≠ 1) (f : C(RotationCircle, ℂ)) :
    Tendsto (fun n => circleError a n f) atTop (𝓝 0) := by
  apply tendsto_zero_of_dense_span (circleError a) (Set.range (fourier (T := (1 : ℝ)))) 2
    (circleError_norm_le a) (span_fourier_closure_eq_top (T := (1 : ℝ)))
  rintro g ⟨k, rfl⟩
  exact circleError_character_tendsto a ha k

theorem character_ne_one_of_irrational {α : ℝ} (hα : Irrational α)
    {k : ℤ} (hk : k ≠ 0) : fourier k (α : RotationCircle) ≠ 1 := by
  intro he
  have hz : k • (α : RotationCircle) = 0 := by
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
    apply Subtype.ext
    simpa [fourier_apply] using he
  have hf : IsOfFinAddOrder (α : RotationCircle) :=
    isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨k, hk, hz⟩
  obtain ⟨r, hr⟩ := AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div.mp hf
  apply hα
  exact ⟨r, by simpa using hr⟩


theorem irrational_rotation_average {α : ℝ} (hα : Irrational α)
    (f : C(RotationCircle, ℂ)) :
    Tendsto (fun n => circleAverage (α : RotationCircle) n f - circleMean f)
      atTop (𝓝 0) :=
  circleError_tendsto _ (fun _ hk => character_ne_one_of_irrational hα hk) f

end MatchingEstimate710
end

section
open Filter MeasureTheory Set
open scoped Topology BigOperators


namespace MatchingEstimate710

noncomputable def realOrbitAverage (a : RotationCircle) (n : ℕ)
    (f : RotationCircle → ℝ) (x : RotationCircle) : ℝ :=
  (n + 1 : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x + i • a)

noncomputable def complexifyCircle (f : C(RotationCircle, ℝ)) : C(RotationCircle, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

theorem complexify_average_error (f : C(RotationCircle, ℝ)) (a : RotationCircle)
    (n : ℕ) (x : RotationCircle) :
    (circleAverage a n (complexifyCircle f) - circleMean (complexifyCircle f)) x =
      ((realOrbitAverage a n f x - ∫ y, f y ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
  simp [circleAverage_apply, circleMean_apply, complexifyCircle, realOrbitAverage,
    integral_complex_ofReal]

theorem real_continuous_rotation_uniform {α : ℝ} (hα : Irrational α)
    (f : C(RotationCircle, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : RotationCircle,
      |realOrbitAverage (α : RotationCircle) n f x -
        ∫ y, f y ∂AddCircle.haarAddCircle| < ε := by
  have h := irrational_rotation_average hα (complexifyCircle f)
  have hn : ∀ᶠ n in atTop, ‖circleAverage (α : RotationCircle) n (complexifyCircle f) -
      circleMean (complexifyCircle f)‖ < ε := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp h ε hε)
  filter_upwards [hn] with n hn
  intro x
  have hb := (circleAverage (α : RotationCircle) n (complexifyCircle f) -
    circleMean (complexifyCircle f)).norm_coe_le_norm x
  rw [complexify_average_error] at hb
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hb.trans_lt hn

theorem realOrbitAverage_mono (a : RotationCircle) (n : ℕ)
    {f g : RotationCircle → ℝ} (h : ∀ x, f x ≤ g x) (x : RotationCircle) :
    realOrbitAverage a n f x ≤ realOrbitAverage a n g x := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun i _ => h (x + i • a))

noncomputable def lowerTent (δ t : ℝ) : ℝ := min t ((1 - t) / δ)
noncomputable def upperTent (δ t : ℝ) : ℝ := 1 - lowerTent δ (1 - t)

theorem lowerTent_continuous (δ : ℝ) : Continuous (lowerTent δ) :=
  continuous_id.min ((continuous_const.sub continuous_id).div_const δ)

theorem upperTent_continuous (δ : ℝ) : Continuous (upperTent δ) :=
  continuous_const.sub ((lowerTent_continuous δ).comp (continuous_const.sub continuous_id))

theorem lowerTent_bounds {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ lowerTent δ t ∧ lowerTent δ t ≤ t := by
  exact ⟨le_min ht.1 (div_nonneg (by linarith [ht.2]) hδ.le), min_le_left _ _⟩

theorem upperTent_bounds {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc (0 : ℝ) 1) :
    t ≤ upperTent δ t ∧ upperTent δ t ≤ 1 := by
  have h := lowerTent_bounds hδ (t := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  unfold upperTent
  constructor <;> linarith

theorem lowerTent_eq {δ t : ℝ} (hδ : 0 < δ)
    (h : t ≤ 1 - δ) : lowerTent δ t = t := by
  apply min_eq_left
  apply (le_div_iff₀ hδ).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1 - t by linarith) hδ.le]

theorem upperTent_eq {δ t : ℝ} (hδ : 0 < δ)
    (h : δ ≤ t) : upperTent δ t = t := by
  rw [upperTent, lowerTent_eq hδ (by linarith)]
  ring

theorem lowerTent_zero {δ : ℝ} (hδ : 0 < δ) : lowerTent δ 0 = 0 := by
  exact min_eq_left (by positivity)

theorem lowerTent_one (δ : ℝ) : lowerTent δ 1 = 0 := by simp [lowerTent]

noncomputable def lowerCircle (δ : ℝ) (hδ : 0 < δ) : C(RotationCircle, ℝ) :=
  ⟨AddCircle.liftIco 1 0 (lowerTent δ),
    AddCircle.liftIco_zero_continuous
      (by rw [lowerTent_zero hδ, lowerTent_one]) (lowerTent_continuous δ).continuousOn⟩

noncomputable def upperCircle (δ : ℝ) (hδ : 0 < δ) : C(RotationCircle, ℝ) :=
  ⟨AddCircle.liftIco 1 0 (upperTent δ),
    AddCircle.liftIco_zero_continuous
      (by simp [upperTent, lowerTent_zero hδ, lowerTent_one])
      (upperTent_continuous δ).continuousOn⟩

noncomputable def circleFraction (x : RotationCircle) : ℝ :=
  AddCircle.equivIco 1 0 x

theorem circleFraction_bounds (x : RotationCircle) :
    circleFraction x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨(AddCircle.equivIco 1 0 x).property.1, ?_⟩
  simpa only [circleFraction, zero_add] using (AddCircle.equivIco 1 0 x).property.2.le

theorem circleFraction_sandwich {δ : ℝ} (hδ : 0 < δ) (x : RotationCircle) :
    lowerCircle δ hδ x ≤ circleFraction x ∧ circleFraction x ≤ upperCircle δ hδ x := by
  exact ⟨(lowerTent_bounds hδ (circleFraction_bounds x)).2,
    (upperTent_bounds hδ (circleFraction_bounds x)).1⟩

theorem integral_liftIco_unit (f : ℝ → ℝ) :
    (∫ x : RotationCircle, AddCircle.liftIco 1 0 f x ∂AddCircle.haarAddCircle) =
      ∫ t in (0 : ℝ)..1, f t := by
  have hv : (volume : Measure RotationCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hv, ← UnitAddCircle.intervalIntegral_preimage 0]
  simp only [zero_add]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  exact AddCircle.liftIco_zero_coe_apply ⟨ht.1.le, ht.2⟩

theorem lowerTent_integral_ge {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 / 2 - δ ≤ ∫ t in (0 : ℝ)..1, lowerTent δ t := by
  have hi₁ := (lowerTent_continuous δ).intervalIntegrable (μ := volume) (0 : ℝ) (1 - δ)
  have hi₂ := (lowerTent_continuous δ).intervalIntegrable (μ := volume) (1 - δ) (1 : ℝ)
  have hs := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have he : (∫ t in (0 : ℝ)..(1 - δ), lowerTent δ t) = (1 - δ) ^ 2 / 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..(1 - δ), t := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        exact lowerTent_eq hδ ht.2.le
      _ = _ := by rw [integral_id]; norm_num
  have hn : 0 ≤ ∫ t in (1 - δ)..(1 : ℝ), lowerTent δ t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t ht =>
      (lowerTent_bounds hδ ⟨by linarith [ht.1], ht.2⟩).1)
  rw [he] at hs
  nlinarith [sq_nonneg δ]

theorem upperTent_integral_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ t in (0 : ℝ)..1, upperTent δ t) ≤ 1 / 2 + δ := by
  have hi₁ := (upperTent_continuous δ).intervalIntegrable (μ := volume) (0 : ℝ) δ
  have hi₂ := (upperTent_continuous δ).intervalIntegrable (μ := volume) δ (1 : ℝ)
  have hs := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have he : (∫ t in δ..(1 : ℝ), upperTent δ t) = (1 - δ ^ 2) / 2 := by
    calc
      _ = ∫ t in δ..(1 : ℝ), t := by
        apply intervalIntegral.integral_congr_Ioo_of_le hδ1
        intro t ht
        exact upperTent_eq hδ ht.1.le
      _ = _ := by rw [integral_id]; norm_num
  have hb : (∫ t in (0 : ℝ)..δ, upperTent δ t) ≤ δ := by
    have h := intervalIntegral.integral_mono_on hδ.le hi₁
      (continuous_const.intervalIntegrable (0 : ℝ) δ)
      (fun t ht => (upperTent_bounds hδ ⟨ht.1, ht.2.trans hδ1⟩).2)
    simpa using h
  rw [he] at hs
  nlinarith [sq_nonneg δ]

theorem lowerCircle_integral_ge {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 / 2 - δ ≤ ∫ x, lowerCircle δ hδ x ∂AddCircle.haarAddCircle := by
  rw [show (fun x => lowerCircle δ hδ x) = AddCircle.liftIco 1 0 (lowerTent δ) from rfl,
    integral_liftIco_unit]
  exact lowerTent_integral_ge hδ hδ1

theorem upperCircle_integral_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ x, upperCircle δ hδ x ∂AddCircle.haarAddCircle) ≤ 1 / 2 + δ := by
  rw [show (fun x => upperCircle δ hδ x) = AddCircle.liftIco 1 0 (upperTent δ) from rfl,
    integral_liftIco_unit]
  exact upperTent_integral_le hδ hδ1

theorem circleFraction_average_uniform {α : ℝ} (hα : Irrational α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : RotationCircle,
      |realOrbitAverage (α : RotationCircle) n circleFraction x - 1 / 2| < ε := by
  let δ := min (ε / 4) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hl := real_continuous_rotation_uniform hα (lowerCircle δ hδ)
    (by positivity : 0 < ε / 4)
  have hu := real_continuous_rotation_uniform hα (upperCircle δ hδ)
    (by positivity : 0 < ε / 4)
  filter_upwards [hl, hu] with n hln hun
  intro x
  have hlx := (abs_lt.mp (hln x)).1
  have hux := (abs_lt.mp (hun x)).2
  have hli := lowerCircle_integral_ge hδ hδ1
  have hui := upperCircle_integral_le hδ hδ1
  have hlow := realOrbitAverage_mono (α : RotationCircle) n
    (fun z => (circleFraction_sandwich hδ z).1) x
  have hupp := realOrbitAverage_mono (α : RotationCircle) n
    (fun z => (circleFraction_sandwich hδ z).2) x
  apply abs_lt.mpr
  constructor <;> linarith

theorem circleFraction_coe (x : ℝ) : circleFraction (x : RotationCircle) = Int.fract x := by
  simpa only [circleFraction, div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) x)

theorem fractional_average_uniform {α : ℝ} (hα : Irrational α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ ζ : ℝ,
      |(n + 1 : ℝ)⁻¹ * (∑ i ∈ Finset.range (n + 1), Int.fract (ζ + (i : ℝ) * α)) -
        1 / 2| < ε := by
  filter_upwards [circleFraction_average_uniform hα hε] with n hn
  intro ζ
  have h := hn (ζ : RotationCircle)
  simpa only [realOrbitAverage, ← AddCircle.coe_add, ← AddCircle.coe_nsmul,
    nsmul_eq_mul, circleFraction_coe] using h

end MatchingEstimate710
end

section
open Filter Set
open scoped Topology BigOperators


namespace MatchingEstimate710

noncomputable def latticeN (A u : ℝ) : ℕ := ⌊u / A⌋₊

noncomputable def latticeCount (A D u : ℝ) : ℕ :=
  (Finset.range (latticeN A u + 1)).sum (fun a : ℕ => ⌊(u - (a : ℝ) * A) / D⌋₊ + 1)

noncomputable def latticeFracMean (A D u : ℝ) : ℝ :=
  (latticeN A u + 1 : ℝ)⁻¹ *
    (Finset.range (latticeN A u + 1)).sum
      (fun a : ℕ => Int.fract (u / D + (a : ℝ) * (-A / D)))

noncomputable def latticeRemainder (A u : ℝ) : ℝ := u / A - latticeN A u

theorem sum_natCast_range_succ (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1), (a : ℝ)) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem latticeRemainder_bounds {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    0 ≤ latticeRemainder A u ∧ latticeRemainder A u < 1 := by
  have h₁ := Nat.floor_le (div_nonneg hu hA.le)
  have h₂ := Nat.lt_floor_add_one (u / A)
  dsimp [latticeRemainder, latticeN]
  constructor <;> linarith

theorem lattice_summand_cast {A D u : ℝ} (hA : 0 < A) (hD : 0 < D) (hu : 0 ≤ u)
    {a : ℕ} (ha : a ∈ Finset.range (latticeN A u + 1)) :
    ((⌊(u - (a : ℝ) * A) / D⌋₊ + 1 : ℕ) : ℝ) =
      u / D + 1 - ((A / D) * a + Int.fract (u / D + (a : ℝ) * (-A / D))) := by
  have haN : a ≤ latticeN A u := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using ha
  have haU : (a : ℝ) ≤ u / A :=
    (Nat.cast_le.mpr haN).trans (Nat.floor_le (div_nonneg hu hA.le))
  have hnonneg : 0 ≤ (u - (a : ℝ) * A) / D := by
    apply div_nonneg _ hD.le
    have hh := (le_div_iff₀ hA).mp haU
    linarith
  rw [Nat.cast_add, Nat.cast_one, natCast_floor_eq_intCast_floor hnonneg, ← Int.self_sub_fract]
  have harg : (u - (a : ℝ) * A) / D = u / D + (a : ℝ) * (-A / D) := by ring
  rw [harg]
  ring

theorem latticeCount_cast {A D u : ℝ} (hA : 0 < A) (hD : 0 < D) (hu : 0 ≤ u) :
    (latticeCount A D u : ℝ) =
      (latticeN A u + 1 : ℝ) * (u / D + 1) -
        (A / D) * ((latticeN A u : ℝ) * (latticeN A u + 1) / 2) -
        (latticeN A u + 1 : ℝ) * latticeFracMean A D u := by
  unfold latticeCount
  rw [Nat.cast_sum (R := ℝ) (Finset.range (latticeN A u + 1))
    (fun a => ⌊(u - (a : ℝ) * A) / D⌋₊ + 1)]
  calc
    _ = ∑ a ∈ Finset.range (latticeN A u + 1),
        (u / D + 1 - ((A / D) * a + Int.fract (u / D + (a : ℝ) * (-A / D)))) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact lattice_summand_cast hA hD hu ha
    _ = (latticeN A u + 1 : ℝ) * (u / D + 1) -
        ((A / D) * (∑ a ∈ Finset.range (latticeN A u + 1), (a : ℝ)) +
          ∑ a ∈ Finset.range (latticeN A u + 1), Int.fract (u / D + (a : ℝ) * (-A / D))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ = _ := by
      rw [sum_natCast_range_succ]
      dsimp [latticeFracMean]
      have hN : (latticeN A u + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring

theorem latticeCount_remainder_identity {A D u : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hu : 0 ≤ u) :
    (latticeCount A D u : ℝ) - u ^ 2 / (2 * A * D) - (A + D) * u / (2 * A * D) =
      A * (latticeRemainder A u - (latticeRemainder A u) ^ 2) / (2 * D) +
      (1 - latticeRemainder A u) / 2 +
      (latticeN A u + 1 : ℝ) * (1 / 2 - latticeFracMean A D u) := by
  rw [latticeCount_cast hA hD hu]
  dsimp [latticeRemainder]
  field_simp
  ring

theorem latticeN_tendsto {A : ℝ} (hA : 0 < A) : Tendsto (latticeN A) atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  simpa only [div_eq_mul_inv, mul_comm, id_eq] using
    (tendsto_id.const_mul_atTop (inv_pos.mpr hA))

theorem latticeFracMean_tendsto {A D : ℝ} (hA : 0 < A) (hAD : Irrational (A / D)) :
    Tendsto (latticeFracMean A D) atTop (𝓝 (1 / 2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (latticeN_tendsto hA).eventually (fractional_average_uniform hAD.neg hε)
  filter_upwards [h] with u hu
  have hh := hu (u / D)
  simpa only [latticeFracMean, neg_div, Real.dist_eq] using hh

theorem latticeN_ratio_identity {A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    (latticeN A u + 1 : ℝ) / u = 1 / A + (1 - latticeRemainder A u) / u := by
  dsimp [latticeRemainder]
  field_simp
  ring

theorem remainder_ratio_tendsto {A : ℝ} (hA : 0 < A) :
    Tendsto (fun u : ℝ => (1 - latticeRemainder A u) / u) atTop (𝓝 0) := by
  have hlo : ∀ᶠ u : ℝ in atTop, 0 ≤ (1 - latticeRemainder A u) / u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hr := latticeRemainder_bounds hA hu.le
    exact div_nonneg (by linarith [hr.2]) hu.le
  have hhi : ∀ᶠ u : ℝ in atTop, (1 - latticeRemainder A u) / u ≤ 1 / u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hr := latticeRemainder_bounds hA hu.le
    exact div_le_div_of_nonneg_right (by linarith [hr.1]) hu.le
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0))
  exact squeeze_zero' hlo hhi (hi.congr (fun u => (one_div u).symm))

theorem latticeN_ratio_tendsto {A : ℝ} (hA : 0 < A) :
    Tendsto (fun u : ℝ => (latticeN A u + 1 : ℝ) / u) atTop (𝓝 (1 / A)) := by
  have hc : Tendsto (fun _ : ℝ => 1 / A) atTop (𝓝 (1 / A)) := tendsto_const_nhds
  have hh := hc.add (remainder_ratio_tendsto hA)
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  exact (latticeN_ratio_identity hA hu).symm

noncomputable def boundedLatticeError (A D u : ℝ) : ℝ :=
  A * (latticeRemainder A u - (latticeRemainder A u) ^ 2) / (2 * D) +
    (1 - latticeRemainder A u) / 2

theorem boundedLatticeError_bounds {A D u : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hu : 0 ≤ u) : 0 ≤ boundedLatticeError A D u ∧
      boundedLatticeError A D u ≤ A / (2 * D) + 1 / 2 := by
  have hr := latticeRemainder_bounds hA hu
  have hrsq : 0 ≤ latticeRemainder A u - (latticeRemainder A u) ^ 2 := by
    nlinarith [mul_nonneg hr.1 (show 0 ≤ 1 - latticeRemainder A u by linarith [hr.2])]
  have hrupper : latticeRemainder A u - (latticeRemainder A u) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (latticeRemainder A u)]
  constructor
  · unfold boundedLatticeError
    exact add_nonneg (div_nonneg (mul_nonneg hA.le hrsq) (by positivity))
      (div_nonneg (by linarith [hr.2]) (by norm_num))
  · have ht₁ : A * (latticeRemainder A u - (latticeRemainder A u) ^ 2) / (2 * D) ≤
        A / (2 * D) := by
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have ht₂ : (1 - latticeRemainder A u) / 2 ≤ (1 : ℝ) / 2 := by linarith [hr.1]
    exact add_le_add ht₁ ht₂

theorem boundedLatticeError_ratio_tendsto {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    Tendsto (fun u : ℝ => boundedLatticeError A D u / u) atTop (𝓝 0) := by
  have hlo : ∀ᶠ u : ℝ in atTop, 0 ≤ boundedLatticeError A D u / u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact div_nonneg (boundedLatticeError_bounds hA hD hu.le).1 hu.le
  have hhi : ∀ᶠ u : ℝ in atTop,
      boundedLatticeError A D u / u ≤ (A / (2 * D) + 1 / 2) / u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact div_le_div_of_nonneg_right (boundedLatticeError_bounds hA hD hu.le).2 hu.le
  apply squeeze_zero' hlo hhi
  have hh := (tendsto_inv_atTop_zero : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0)).const_mul
    (A / (2 * D) + 1 / 2)
  simp only [mul_zero] at hh
  exact hh.congr (fun u => (div_eq_mul_inv _ _).symm)


theorem latticeCount_asymptotic {A D : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hAD : Irrational (A / D)) :
    Tendsto (fun u : ℝ => ((latticeCount A D u : ℝ) - u ^ 2 / (2 * A * D) -
      (A + D) * u / (2 * A * D)) / u) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds
  have hfrac := hc.sub (latticeFracMean_tendsto hA hAD)
  have hprod := (latticeN_ratio_tendsto hA).mul hfrac
  have htotal := (boundedLatticeError_ratio_tendsto hA hD).add hprod
  simp only [sub_self, mul_zero, add_zero] at htotal
  apply htotal.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [latticeCount_remainder_identity hA hD hu.le]
  dsimp [boundedLatticeError]
  ring

theorem two_three_lattice_asymptotic :
    Tendsto (fun u : ℝ =>
      ((latticeCount (Real.log 2) (Real.log 3) u : ℝ) -
        u ^ 2 / (2 * Real.log 2 * Real.log 3) -
        (Real.log 2 + Real.log 3) * u / (2 * Real.log 2 * Real.log 3)) / u)
      atTop (𝓝 0) :=
  latticeCount_asymptotic (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
    log_two_div_log_three_irrational

theorem latticeCount_uniform_scaled_error {A D c₁ c₂ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hAD : Irrational (A / D))
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ u ∈ Icc (c₁ * L) (c₂ * L),
      |(latticeCount A D u : ℝ) - u ^ 2 / (2 * A * D) -
        (A + D) * u / (2 * A * D)| ≤ ε * L := by
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  have he := Metric.tendsto_nhds.mp (latticeCount_asymptotic hA hD hAD)
    (ε / c₂) (div_pos hε hc₂)
  obtain ⟨R, hR⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop (max (1 : ℝ) (R / c₁))] with L hL
  intro u hu
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hL)
  have hRL : R ≤ c₁ * L := by
    have h := (le_max_right (1 : ℝ) (R / c₁)).trans hL
    simpa only [mul_comm] using (div_le_iff₀ hc₁).mp h
  have hu0 : 0 < u := (mul_pos hc₁ hLpos).trans_le hu.1
  have hh := hR u (hRL.trans hu.1)
  rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hu0] at hh
  have hb := (div_lt_iff₀ hu0).mp hh
  have ht : (ε / c₂) * u ≤ ε * L := by
    calc
      _ ≤ (ε / c₂) * (c₂ * L) := mul_le_mul_of_nonneg_left hu.2 (by positivity)
      _ = _ := by field_simp
  exact hb.le.trans ht

end MatchingEstimate710
end

section
open scoped BigOperators


namespace MatchingEstimate710

noncomputable def latticeExponentPairs (A D u : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (latticeN A u + 1)).biUnion fun a =>
    (Finset.range (⌊(u - (a : ℝ) * A) / D⌋₊ + 1)).image fun b => (a, b)

theorem card_latticeExponentPairs (A D u : ℝ) :
    (latticeExponentPairs A D u).card = latticeCount A D u := by
  classical
  unfold latticeExponentPairs latticeCount
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro b c h
      exact congrArg Prod.snd h
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro z ha hb
    obtain ⟨a', _, hza⟩ := Finset.mem_image.mp ha
    obtain ⟨b', _, hzb⟩ := Finset.mem_image.mp hb
    exact hab (congrArg Prod.fst (hza.trans hzb.symm))

theorem mem_latticeExponentPairs {A D u : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hu : 0 ≤ u) (a b : ℕ) :
    (a, b) ∈ latticeExponentPairs A D u ↔ (a : ℝ) * A + (b : ℝ) * D ≤ u := by
  classical
  have hmem : (a, b) ∈ latticeExponentPairs A D u ↔
      a ≤ latticeN A u ∧ b ≤ ⌊(u - (a : ℝ) * A) / D⌋₊ := by
    simp [latticeExponentPairs, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
  rw [hmem]
  constructor
  · intro ⟨ha, hb⟩
    have haU : (a : ℝ) ≤ u / A :=
      (Nat.cast_le.mpr ha).trans (Nat.floor_le (div_nonneg hu hA.le))
    have hau : (a : ℝ) * A ≤ u := (le_div_iff₀ hA).mp haU
    have hnonneg : 0 ≤ (u - (a : ℝ) * A) / D := div_nonneg (by linarith) hD.le
    have hbU : (b : ℝ) ≤ (u - (a : ℝ) * A) / D :=
      (Nat.cast_le.mpr hb).trans (Nat.floor_le hnonneg)
    have hbu := (le_div_iff₀ hD).mp hbU
    linarith
  · intro h
    have hau : (a : ℝ) * A ≤ u := by
      have hb0 : 0 ≤ (b : ℝ) * D := mul_nonneg (Nat.cast_nonneg _) hD.le
      linarith
    constructor
    · exact Nat.le_floor ((le_div_iff₀ hA).mpr hau)
    · exact Nat.le_floor ((le_div_iff₀ hD).mpr (by linarith))

theorem two_three_powers_injective :
    Function.Injective (fun ab : ℕ × ℕ => 2 ^ ab.1 * 3 ^ ab.2) := by
  intro ab cd h
  have htwo := congrArg (fun n : ℕ => n.factorization 2) h
  have hthree := congrArg (fun n : ℕ => n.factorization 3) h
  have hfac (a b : ℕ) : (2 ^ a * 3 ^ b).factorization =
      Finsupp.single 2 a + Finsupp.single 3 b := by
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
  simp only [hfac, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by norm_num : (3 : ℕ) ≠ 2),
    Finsupp.single_eq_of_ne (by norm_num : (2 : ℕ) ≠ 3), add_zero, zero_add] at htwo hthree
  exact Prod.ext htwo hthree

noncomputable def smooth23Below (x : ℝ) : Finset ℕ :=
  if 1 ≤ x then
    (latticeExponentPairs (Real.log 2) (Real.log 3) (Real.log x)).image
      (fun ab : ℕ × ℕ => 2 ^ ab.1 * 3 ^ ab.2)
  else ∅

theorem card_smooth23Below {x : ℝ} (hx : 1 ≤ x) :
    (smooth23Below x).card = latticeCount (Real.log 2) (Real.log 3) (Real.log x) := by
  rw [smooth23Below, if_pos hx, Finset.card_image_of_injective _ two_three_powers_injective,
    card_latticeExponentPairs]

theorem mem_smooth23Below {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    m ∈ smooth23Below x ↔ ∃ a b : ℕ, m = 2 ^ a * 3 ^ b ∧ (m : ℝ) ≤ x := by
  classical
  rw [smooth23Below, if_pos hx]
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hA : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbound (a b : ℕ) : (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 ≤ Real.log x ↔
      ((2 ^ a * 3 ^ b : ℕ) : ℝ) ≤ x := by
    have hp : (0 : ℝ) < ((2 ^ a * 3 ^ b : ℕ) : ℝ) := by positivity
    rw [← Real.log_le_log_iff hp hx0]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  constructor
  · intro hm
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨a, b, rfl, (hbound a b).mp ((mem_latticeExponentPairs hA hD hlog a b).mp hab)⟩
  · rintro ⟨a, b, rfl, hab⟩
    apply Finset.mem_image.mpr
    exact ⟨(a, b), (mem_latticeExponentPairs hA hD hlog a b).mpr ((hbound a b).mpr hab), rfl⟩

noncomputable def smooth23CountLog (u : ℝ) : ℝ :=
  if 0 ≤ u then (latticeCount (Real.log 2) (Real.log 3) u : ℝ) else 0

theorem smooth23CountLog_eq_card (u : ℝ) :
    smooth23CountLog u = ((smooth23Below (Real.exp u)).card : ℝ) := by
  by_cases hu : 0 ≤ u
  · rw [smooth23CountLog, if_pos hu, card_smooth23Below (Real.one_le_exp_iff.mpr hu),
      Real.log_exp]
  · simp [smooth23CountLog, hu, smooth23Below, Real.one_le_exp_iff]

end MatchingEstimate710
end

section
open Filter Set
open scoped Topology BigOperators


namespace MatchingEstimate710

theorem latticeCount_global_bound {A D u : ℝ} (hA : 0 < A) (hD : 0 < D) (hu : 0 ≤ u) :
    (latticeCount A D u : ℝ) ≤ (1 + u / A) * (1 + u / D) := by
  have hn : latticeCount A D u ≤ (latticeN A u + 1) * (⌊u / D⌋₊ + 1) := by
    unfold latticeCount
    calc
      _ ≤ ∑ _a ∈ Finset.range (latticeN A u + 1), (⌊u / D⌋₊ + 1) := by
        apply Finset.sum_le_sum
        intro a _
        apply Nat.add_le_add_right
        apply Nat.floor_mono
        apply div_le_div_of_nonneg_right _ hD.le
        have ha0 : 0 ≤ (a : ℝ) * A := mul_nonneg (Nat.cast_nonneg _) hA.le
        linarith
      _ = _ := by simp
  have hcast : (latticeCount A D u : ℝ) ≤
      (latticeN A u + 1 : ℝ) * (⌊u / D⌋₊ + 1 : ℝ) := by exact_mod_cast hn
  have hN : (latticeN A u + 1 : ℝ) ≤ 1 + u / A := by
    have h := Nat.floor_le (div_nonneg hu hA.le)
    dsimp [latticeN]
    linarith
  have hM : (⌊u / D⌋₊ + 1 : ℝ) ≤ 1 + u / D := by
    have h := Nat.floor_le (div_nonneg hu hD.le)
    linarith
  exact hcast.trans (mul_le_mul hN hM (by positivity) (by positivity))

noncomputable def latticeError (A D u : ℝ) : ℝ :=
  (latticeCount A D u : ℝ) - u ^ 2 / (2 * A * D) - (A + D) * u / (2 * A * D)

theorem lattice_increment_identity (A D u v : ℝ) :
    (latticeCount A D (u + v) : ℝ) - (latticeCount A D u : ℝ) -
      u * v / (A * D) - (v ^ 2 + (A + D) * v) / (2 * A * D) =
        latticeError A D (u + v) - latticeError A D u := by
  unfold latticeError
  ring

theorem lattice_uniform_increment_error {A D c₁ c₂ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hAD : Irrational (A / D))
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ u ∈ Icc (c₁ * L) (c₂ * L), ∀ v : ℝ,
      |v| ≤ (c₁ / 2) * L →
      |(latticeCount A D (u + v) : ℝ) - (latticeCount A D u : ℝ) -
        u * v / (A * D) - (v ^ 2 + (A + D) * v) / (2 * A * D)| ≤ ε * L := by
  have hc : c₁ / 2 ≤ c₂ + c₁ / 2 := by linarith
  have he := latticeCount_uniform_scaled_error hA hD hAD
    (show 0 < c₁ / 2 by linarith) hc (show 0 < ε / 2 by positivity)
  filter_upwards [he, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro u hu v hv
  have hv' := abs_le.mp hv
  have hu' : u ∈ Icc ((c₁ / 2) * L) ((c₂ + c₁ / 2) * L) := by
    constructor <;> nlinarith [hu.1, hu.2]
  have huv : u + v ∈ Icc ((c₁ / 2) * L) ((c₂ + c₁ / 2) * L) := by
    constructor <;> nlinarith [hu.1, hu.2, hv'.1, hv'.2]
  rw [lattice_increment_identity]
  exact (abs_sub _ _).trans (by
    have h₁ := hL u hu'
    have h₂ := hL (u + v) huv
    change |latticeError A D (u + v)| ≤ (ε / 2) * L at h₂
    change |latticeError A D u| ≤ (ε / 2) * L at h₁
    linarith)

end MatchingEstimate710
end

section
open MeasureTheory Set
open scoped BigOperators


namespace MatchingEstimate710

theorem mem_smooth23Below_iff (x : ℝ) (m : ℕ) :
    m ∈ smooth23Below x ↔ ∃ a b : ℕ, m = 2 ^ a * 3 ^ b ∧ (m : ℝ) ≤ x := by
  by_cases hx : 1 ≤ x
  · exact mem_smooth23Below hx m
  · simp only [smooth23Below, if_neg hx, Finset.notMem_empty, false_iff, not_exists,
      not_and]
    intro a b hm hab
    have hpos : 1 ≤ 2 ^ a * 3 ^ b := by
      have hp : 0 < 2 ^ a * 3 ^ b := by positivity
      omega
    have hp : (1 : ℝ) ≤ m := by exact_mod_cast (hm ▸ hpos)
    exact hx (hp.trans hab)

theorem smooth23CountLog_nonneg (u : ℝ) : 0 ≤ smooth23CountLog u := by
  rw [smooth23CountLog_eq_card]
  positivity

theorem smooth23CountLog_monotone : Monotone smooth23CountLog := by
  intro u v huv
  rw [smooth23CountLog_eq_card, smooth23CountLog_eq_card]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro m hm
  rw [mem_smooth23Below_iff] at hm ⊢
  obtain ⟨a, b, h, hx⟩ := hm
  exact ⟨a, b, h, hx.trans (Real.exp_le_exp.mpr huv)⟩

theorem smooth23CountLog_le {u L : ℝ} (hL : 0 ≤ L) (hu : u ≤ L) :
    smooth23CountLog u ≤ (1 + L / Real.log 2) * (1 + L / Real.log 3) := by
  apply (smooth23CountLog_monotone hu).trans
  rw [smooth23CountLog, if_pos hL]
  exact latticeCount_global_bound (Real.log_pos (by norm_num))
    (Real.log_pos (by norm_num)) hL

theorem primeLogValue_nonneg (y : ℝ) (z : PrimeIndex y → ℕ) : 0 ≤ primeLogValue y z := by
  unfold primeLogValue weightedExponent
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg _ (Nat.cast_nonneg _)
  apply Real.log_nonneg
  exact_mod_cast (mem_largePrimeRange.mp p.property).2.1.one_le

theorem weightedLattice_integrable (y x : ℝ) :
    Integrable (fun z => smooth23CountLog (x - primeLogValue y z)) (primeDistribution y) := by
  let B := (1 + max 0 x / Real.log 2) * (1 + max 0 x / Real.log 3)
  have hm : AEStronglyMeasurable (fun z => smooth23CountLog (x - primeLogValue y z))
      (primeDistribution y) := (measurable_of_countable _).aestronglyMeasurable
  apply Integrable.mono' (integrable_const B) hm
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (smooth23CountLog_nonneg _)]
  apply smooth23CountLog_le (le_max_left _ _)
  have hz := primeLogValue_nonneg y z
  linarith [le_max_right (0 : ℝ) x]

noncomputable def weightedLatticeCount (y x : ℝ) : ℝ :=
  ∫ z, smooth23CountLog (x - primeLogValue y z) ∂primeDistribution y

theorem weightedLatticeCount_nonneg (y x : ℝ) : 0 ≤ weightedLatticeCount y x :=
  integral_nonneg (fun _ => smooth23CountLog_nonneg _)

end MatchingEstimate710
end

section
open scoped BigOperators


namespace MatchingEstimate710

noncomputable def weightedSum (y X : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, rho y m

noncomputable def roughCores (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun r => ¬2 ∣ r ∧ ¬3 ∣ r)

noncomputable def coreFiber (X : ℝ) (r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun m => core23 m = r)

theorem core23_mul_smooth (a b r : ℕ) (h2 : ¬2 ∣ r) (h3 : ¬3 ∣ r) :
    core23 ((2 ^ a * 3 ^ b) * r) = r := by
  have hnot : ¬2 ∣ 3 ^ b * r := by
    intro h
    rcases Nat.prime_two.dvd_mul.mp h with hp | hp
    · have hh := Nat.prime_two.dvd_of_dvd_pow hp
      norm_num at hh
    · exact h2 hp
  unfold core23
  rw [mul_assoc, Nat.ordCompl_pow_mul_of_not_dvd a Nat.prime_two hnot,
    Nat.ordCompl_pow_mul_of_not_dvd b Nat.prime_three h3]

theorem coreFiber_eq_image {X : ℝ} (hX : 0 ≤ X) {r : ℕ}
    (hr : 0 < r) (h2 : ¬2 ∣ r) (h3 : ¬3 ∣ r) :
    coreFiber X r = (smooth23Below (X / r)).image (fun k => k * r) := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  ext m
  constructor
  · intro hm
    obtain ⟨hm, hcore⟩ := Finset.mem_filter.mp hm
    have hmX : (m : ℝ) ≤ X :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le hX)
    let a := m.factorization 2
    let b := (ordCompl[2] m).factorization 3
    have he : (2 ^ a * 3 ^ b) * r = m := by
      simpa only [a, b, hcore] using core23_decomposition m
    apply Finset.mem_image.mpr
    refine ⟨2 ^ a * 3 ^ b, ?_, he⟩
    rw [mem_smooth23Below_iff]
    refine ⟨a, b, rfl, (le_div_iff₀ hrR).mpr ?_⟩
    rw [← Nat.cast_mul, he]
    exact hmX
  · intro hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨a, b, rfl, hk⟩ := (mem_smooth23Below_iff _ _).mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, core23_mul_smooth a b r h2 h3⟩
    · have hp : 0 < (2 ^ a * 3 ^ b) * r := by positivity
      omega
    · apply Nat.le_floor
      rw [Nat.cast_mul]
      exact (le_div_iff₀ hrR).mp hk

theorem card_coreFiber {X : ℝ} (hX : 0 ≤ X) {r : ℕ}
    (hr : 0 < r) (h2 : ¬2 ∣ r) (h3 : ¬3 ∣ r) :
    (coreFiber X r).card = (smooth23Below (X / r)).card := by
  rw [coreFiber_eq_image hX hr h2 h3]
  apply Finset.card_image_of_injective
  intro a b h
  exact mul_right_cancel₀ hr.ne' h

theorem sum_coreFiber (y X : ℝ) (r : ℕ) :
    (∑ m ∈ coreFiber X r, rho y m) = rho y r * (coreFiber X r).card := by
  have hc : ∀ m ∈ coreFiber X r, rho y m = rho y r := by
    intro m hm
    obtain ⟨hm, hcore⟩ := Finset.mem_filter.mp hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    rw [← rho_core23 y hm0, hcore]
  rw [Finset.sum_congr rfl hc]
  simp [mul_comm]

theorem weightedSum_convolution {X : ℝ} (hX : 0 ≤ X) (y : ℝ) :
    weightedSum y X = ∑ r ∈ roughCores X, rho y r * ((smooth23Below (X / r)).card : ℝ) := by
  classical
  have hmap : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, core23 m ∈ roughCores X := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by have := core23_pos hm0; omega,
      (core23_le m).trans (Finset.mem_Icc.mp hm).2⟩,
      core23_not_dvd_two hm0, core23_not_dvd_three hm0⟩
  calc
    _ = ∑ r ∈ roughCores X, ∑ m ∈ coreFiber X r, rho y m :=
      (Finset.sum_fiberwise_of_maps_to hmap (rho y)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      obtain ⟨hr, h2, h3⟩ := Finset.mem_filter.mp hr
      have hr0 : 0 < r := by have := (Finset.mem_Icc.mp hr).1; omega
      rw [sum_coreFiber, card_coreFiber hX hr0 h2 h3]

end MatchingEstimate710
end

section
open MeasureTheory Set
open scoped BigOperators


namespace MatchingEstimate710

noncomputable def arithLatticeCount (X : ℝ) (r : ℕ) : ℝ :=
  (smooth23Below (X / (r : ℝ))).card

theorem arithLatticeCount_log {X : ℝ} (hX : 0 < X) {r : ℕ} (hr : 0 < r) :
    arithLatticeCount X r = smooth23CountLog (Real.log X - Real.log (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [smooth23CountLog_eq_card, Real.exp_sub, Real.exp_log hX, Real.exp_log hrR]
  rfl

theorem arithLatticeCount_comp {X : ℝ} (hX : 0 < X) (y : ℝ) (z : PrimeIndex y → ℕ) :
    arithLatticeCount X (primeInteger y z) = smooth23CountLog (Real.log X - primeLogValue y z) := by
  rw [arithLatticeCount_log hX (primeInteger_pos y z), log_primeInteger]

theorem arithLatticeCount_off_interval (X : ℝ) {r : ℕ} (hr : r ∉ Finset.Icc 1 ⌊X⌋₊) :
    arithLatticeCount X r = 0 := by
  by_cases hr0 : r = 0
  · subst r
    simp [arithLatticeCount, smooth23Below]
  · have hrR : (0 : ℝ) < r := by exact_mod_cast (Nat.pos_of_ne_zero hr0)
    have hn : ¬1 ≤ X / (r : ℝ) := by
      intro h
      have hle : (r : ℝ) ≤ X := by simpa using (le_div_iff₀ hrR).mp h
      exact hr (Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hle⟩)
    simp [arithLatticeCount, smooth23Below, hn]

theorem arithLatticeCount_integral_finite (y X : ℝ) :
    (∫ r, arithLatticeCount X r ∂arithmeticPrimeMeasure y) =
      ∑ r ∈ Finset.Icc 1 ⌊X⌋₊,
        (arithmeticPrimeMeasure y).real {r} * arithLatticeCount X r := by
  classical
  let S := Finset.Icc 1 ⌊X⌋₊
  have he : arithLatticeCount X = (S : Set ℕ).indicator (arithLatticeCount X) := by
    funext r
    by_cases hr : r ∈ S
    · rw [indicator_of_mem hr]
    · rw [indicator_of_notMem hr]
      exact arithLatticeCount_off_interval X hr
  calc
    _ = ∫ r, (S : Set ℕ).indicator (arithLatticeCount X) r ∂arithmeticPrimeMeasure y := by rw [← he]
    _ = ∫ r in (S : Set ℕ), arithLatticeCount X r ∂arithmeticPrimeMeasure y :=
      integral_indicator S.measurableSet
    _ = _ := by
      rw [setIntegral_finset S IntegrableOn.finset]
      simp only [smul_eq_mul, S]

theorem arithLatticeCount_integral_weights {y X : ℝ} (hy : 0 < y) (hX : 0 ≤ X) :
    (∫ r, arithLatticeCount X r ∂arithmeticPrimeMeasure y) = weightedSum y X / primeMassNormalizer y := by
  classical
  rw [arithLatticeCount_integral_finite]
  have hsub : roughCores X ⊆ Finset.Icc 1 ⌊X⌋₊ := Finset.filter_subset _ _
  calc
    _ = ∑ r ∈ roughCores X, (arithmeticPrimeMeasure y).real {r} * arithLatticeCount X r := by
      symm
      apply Finset.sum_subset hsub
      intro r hr hnot
      have hsmall : 2 ∣ r ∨ 3 ∣ r := by
        by_cases h2 : 2 ∣ r
        · exact Or.inl h2
        by_cases h3 : 3 ∣ r
        · exact Or.inr h3
        exact False.elim (hnot (Finset.mem_filter.mpr ⟨hr, h2, h3⟩))
      have hz := arithmeticPrimeMeasure_small_factor_zero y hsmall
      simp only [measureReal_def, hz, ENNReal.toReal_zero, zero_mul]
    _ = ∑ r ∈ roughCores X, (rho y r / primeMassNormalizer y) * arithLatticeCount X r := by
      apply Finset.sum_congr rfl
      intro r hr
      obtain ⟨hr, h2, h3⟩ := Finset.mem_filter.mp hr
      have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
      rw [arithmeticPrimeMeasure_singleton hy hr0 h2 h3]
    _ = (∑ r ∈ roughCores X, rho y r * arithLatticeCount X r) / primeMassNormalizer y := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [weightedSum_convolution hX]; rfl

theorem arithLatticeCount_integral_map {X : ℝ} (hX : 0 < X) (y : ℝ) :
    (∫ r, arithLatticeCount X r ∂arithmeticPrimeMeasure y) = weightedLatticeCount y (Real.log X) := by
  rw [arithmeticPrimeMeasure, integral_map_of_stronglyMeasurable (primeInteger_measurable y)
    (measurable_of_countable (arithLatticeCount X)).stronglyMeasurable]
  simp_rw [arithLatticeCount_comp hX]
  rfl


theorem weightedSum_eq_convolution {y X : ℝ} (hy : 0 < y) (hX : 0 < X) :
    weightedSum y X = primeMassNormalizer y * weightedLatticeCount y (Real.log X) := by
  have hh := (arithLatticeCount_integral_weights hy hX.le).symm.trans (arithLatticeCount_integral_map hX y)
  have hZ := (primeMassNormalizer_pos hy).ne'
  exact (div_eq_iff hZ).mp hh |>.trans (mul_comm _ _)

end MatchingEstimate710
end

section
open MeasureTheory Set

namespace MatchingEstimate710

theorem integral_error_with_exception {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f g : α → ℝ} {S : Set α}
    (hf : Integrable f μ) (hg : Integrable g μ) (hS : MeasurableSet S)
    (c d : ℝ) (hbound : ∀ x, |f x - g x| ≤ c + d * S.indicator (fun _ => (1 : ℝ)) x) :
    |(∫ x, f x ∂μ) - (∫ x, g x ∂μ)| ≤ c + d * μ.real S := by
  have hb : Integrable (fun x => c + d * S.indicator (fun _ => (1 : ℝ)) x) μ :=
    (integrable_const c).add (((integrable_const (1 : ℝ)).indicator hS).const_mul d)
  rw [← integral_sub hf hg]
  calc
    _ ≤ ∫ x, |f x - g x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x - g x)
    _ ≤ ∫ x, c + d * S.indicator (fun _ => (1 : ℝ)) x ∂μ :=
      integral_mono (hf.sub hg).abs hb hbound
    _ = _ := by
      rw [integral_add (integrable_const c) (((integrable_const (1 : ℝ)).indicator hS).const_mul d),
        integral_const_mul, integral_indicator_const (1 : ℝ) hS]
      simp

end MatchingEstimate710
end

section
open MeasureTheory Set Filter
open scoped Topology


namespace MatchingEstimate710

def primeCore (y L θ : ℝ) : Set (PrimeIndex y → ℕ) :=
  {z | primeLogValue y z ≤ θ * L}

noncomputable def truncatedGap (y L θ : ℝ) (z : PrimeIndex y → ℕ) : ℝ :=
  (primeCore y L θ).indicator (fun z => L - primeLogValue y z) z

theorem primeCore_measurable (y L θ : ℝ) : MeasurableSet (primeCore y L θ) :=
  measurableSet_le (measurable_of_countable _) measurable_const

theorem truncatedGap_bounds (y : ℝ) {L θ : ℝ} (hL : 0 ≤ L) (hθ : θ ≤ 1)
    (z : PrimeIndex y → ℕ) : 0 ≤ truncatedGap y L θ z ∧ truncatedGap y L θ z ≤ L := by
  by_cases hz : z ∈ primeCore y L θ
  · rw [truncatedGap, indicator_of_mem hz]
    have hU : primeLogValue y z ≤ θ * L := hz
    have hU0 := primeLogValue_nonneg y z
    constructor <;> nlinarith
  · rw [truncatedGap, indicator_of_notMem hz]
    exact ⟨le_rfl, hL⟩

theorem truncatedGap_integrable (y : ℝ) {L θ : ℝ} (hL : 0 ≤ L) (hθ : θ ≤ 1) :
    Integrable (truncatedGap y L θ) (primeDistribution y) := by
  apply Integrable.mono' (integrable_const L) (measurable_of_countable _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (truncatedGap_bounds y hL hθ z).1]
  exact (truncatedGap_bounds y hL hθ z).2

theorem truncatedGap_integral_bounds (y : ℝ) {L θ : ℝ} (hL : 0 ≤ L) (hθ : θ ≤ 1) :
    (1 - θ) * L * (primeDistribution y).real (primeCore y L θ) ≤
        (∫ z, truncatedGap y L θ z ∂primeDistribution y) ∧
      (∫ z, truncatedGap y L θ z ∂primeDistribution y) ≤ L := by
  have hi := truncatedGap_integrable y hL hθ
  constructor
  · have hj : Integrable (fun z => ((1 - θ) * L) *
        (primeCore y L θ).indicator (fun _ => (1 : ℝ)) z) (primeDistribution y) :=
      ((integrable_const (1 : ℝ)).indicator (primeCore_measurable y L θ)).const_mul _
    have hb : ∀ z, ((1 - θ) * L) * (primeCore y L θ).indicator (fun _ => (1 : ℝ)) z ≤
        truncatedGap y L θ z := by
      intro z
      by_cases hz : z ∈ primeCore y L θ
      · rw [truncatedGap, indicator_of_mem hz, indicator_of_mem hz]
        have hU : primeLogValue y z ≤ θ * L := hz
        nlinarith
      · rw [truncatedGap, indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]
    have hh := integral_mono hj hi hb
    simpa only [integral_const_mul, integral_indicator_const (1 : ℝ) (primeCore_measurable y L θ),
      smul_eq_mul, mul_one] using hh
  · have hh := integral_mono hi (integrable_const L)
      (fun z => (truncatedGap_bounds y hL hθ z).2)
    simpa using hh

theorem weightedLattice_local_error (y : ℝ) {L θ v ε : ℝ}
    (hL : 0 ≤ L) (hθ : θ < 1) (hε : 0 ≤ ε)
    (hv : |v| ≤ ((1 - θ) / 2) * L)
    (hlocal : ∀ u ∈ Icc ((1 - θ) * L) L,
      |(latticeCount (Real.log 2) (Real.log 3) (u + v) : ℝ) -
          (latticeCount (Real.log 2) (Real.log 3) u : ℝ) -
        u * v / (Real.log 2 * Real.log 3) -
        (v ^ 2 + (Real.log 2 + Real.log 3) * v) / (2 * Real.log 2 * Real.log 3)| ≤ ε * L) :
    |weightedLatticeCount y (L + v) - weightedLatticeCount y L -
        (v / (Real.log 2 * Real.log 3)) * (∫ z, truncatedGap y L θ z ∂primeDistribution y)| ≤
      ε * L + |(v ^ 2 + (Real.log 2 + Real.log 3) * v) / (2 * Real.log 2 * Real.log 3)| +
      (2 * ((1 + (L + |v|) / Real.log 2) * (1 + (L + |v|) / Real.log 3))) *
        (primeDistribution y).real (primeCore y L θ)ᶜ := by
  let P := (v ^ 2 + (Real.log 2 + Real.log 3) * v) / (2 * Real.log 2 * Real.log 3)
  let B := (1 + (L + |v|) / Real.log 2) * (1 + (L + |v|) / Real.log 3)
  let f := fun z => smooth23CountLog ((L + v) - primeLogValue y z) -
    smooth23CountLog (L - primeLogValue y z)
  let g := fun z => (v / (Real.log 2 * Real.log 3)) * truncatedGap y L θ z
  have hf : Integrable f (primeDistribution y) :=
    (weightedLattice_integrable y (L + v)).sub (weightedLattice_integrable y L)
  have hg : Integrable g (primeDistribution y) := (truncatedGap_integrable y hL hθ.le).const_mul _
  have hc : 0 ≤ ε * L + |P| := add_nonneg (mul_nonneg hε hL) (abs_nonneg _)
  have hb1 (z : PrimeIndex y → ℕ) : smooth23CountLog ((L + v) - primeLogValue y z) ≤ B := by
    apply smooth23CountLog_le (by positivity)
    linarith [primeLogValue_nonneg y z, le_abs_self v]
  have hb0 (z : PrimeIndex y → ℕ) : smooth23CountLog (L - primeLogValue y z) ≤ B := by
    apply smooth23CountLog_le (by positivity)
    linarith [primeLogValue_nonneg y z, abs_nonneg v]
  have he := integral_error_with_exception hf hg (primeCore_measurable y L θ).compl
    (ε * L + |P|) (2 * B) (by
      intro z
      by_cases hz : z ∈ primeCore y L θ
      · have hU : primeLogValue y z ≤ θ * L := hz
        have hU0 := primeLogValue_nonneg y z
        have hu : L - primeLogValue y z ∈ Icc ((1 - θ) * L) L := by
          constructor <;> nlinarith
        have hu0 : 0 ≤ L - primeLogValue y z := by nlinarith
        have huv0 : 0 ≤ (L - primeLogValue y z) + v := by
          have hv' := (abs_le.mp hv).1
          nlinarith
        have hrel : (L + v) - primeLogValue y z = (L - primeLogValue y z) + v := by ring
        have hh := hlocal (L - primeLogValue y z) hu
        have heq : f z - g z =
            ((latticeCount (Real.log 2) (Real.log 3) ((L - primeLogValue y z) + v) : ℝ) -
              (latticeCount (Real.log 2) (Real.log 3) (L - primeLogValue y z) : ℝ) -
              (L - primeLogValue y z) * v / (Real.log 2 * Real.log 3) - P) + P := by
          dsimp [f, g, truncatedGap]
          rw [indicator_of_mem hz, hrel, smooth23CountLog, smooth23CountLog,
            if_pos huv0, if_pos hu0]
          ring
        rw [indicator_of_notMem (show z ∉ (primeCore y L θ)ᶜ from fun h => h hz), mul_zero, add_zero, heq]
        exact (abs_add_le _ _).trans (add_le_add hh (le_refl _))
      · rw [indicator_of_mem (show z ∈ (primeCore y L θ)ᶜ from hz), mul_one]
        have hg0 : g z = 0 := by simp [g, truncatedGap, indicator_of_notMem hz]
        rw [hg0, sub_zero]
        have hh : |f z| ≤ 2 * B := by
          dsimp [f]
          exact (abs_sub _ _).trans (by
            rw [abs_of_nonneg (smooth23CountLog_nonneg _), abs_of_nonneg (smooth23CountLog_nonneg _)]
            linarith [hb1 z, hb0 z])
        exact hh.trans (by linarith))
  simpa only [f, g, weightedLatticeCount, integral_sub (weightedLattice_integrable y (L + v))
      (weightedLattice_integrable y L), integral_const_mul, P, B] using he

end MatchingEstimate710
end

section
open Filter Set MeasureTheory
open scoped Topology


namespace MatchingEstimate710

noncomputable def latticeMainWeight (y L θ : ℝ) : ℝ :=
  (∫ z, truncatedGap y L θ z ∂primeDistribution y) / (Real.log 2 * Real.log 3)

theorem lattice_window_global_bound {L v : ℝ} (hL : 1 ≤ L) (hv : |v| ≤ L) :
    (1 + (L + |v|) / Real.log 2) * (1 + (L + |v|) / Real.log 3) ≤
      ((1 + 2 / Real.log 2) * (1 + 2 / Real.log 3)) * L ^ 2 := by
  have hA : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha : 1 + (L + |v|) / Real.log 2 ≤ (1 + 2 / Real.log 2) * L := by
    have hh := div_le_div_of_nonneg_right (show L + |v| ≤ 2 * L by linarith) hA.le
    have he : (1 + 2 / Real.log 2) * L = L + (2 * L) / Real.log 2 := by ring
    rw [he]
    linarith
  have hd : 1 + (L + |v|) / Real.log 3 ≤ (1 + 2 / Real.log 3) * L := by
    have hh := div_le_div_of_nonneg_right (show L + |v| ≤ 2 * L by linarith) hD.le
    have he : (1 + 2 / Real.log 3) * L = L + (2 * L) / Real.log 3 := by ring
    rw [he]
    linarith
  calc
    _ ≤ ((1 + 2 / Real.log 2) * L) * ((1 + 2 / Real.log 3) * L) :=
      mul_le_mul ha hd (by positivity) (by positivity)
    _ = _ := by ring

theorem lattice_window_polynomial_bound {C L v : ℝ} (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hv : |v| ≤ C * Real.log L) :
    |(v ^ 2 + (Real.log 2 + Real.log 3) * v) / (2 * Real.log 2 * Real.log 3)| ≤
      ((C * Real.log L) ^ 2 + (Real.log 2 + Real.log 3) * (C * Real.log L)) /
        (2 * Real.log 2 * Real.log 3) := by
  have hA : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hM : 0 ≤ C * Real.log L := mul_nonneg hC (Real.log_nonneg hL)
  have hv2 : v ^ 2 ≤ (C * Real.log L) ^ 2 := by
    have hh := abs_le.mp hv
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith : 0 ≤ C * Real.log L + v)]
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.log 2 * Real.log 3)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ |v ^ 2| + |(Real.log 2 + Real.log 3) * v| := abs_add_le _ _
    _ = v ^ 2 + (Real.log 2 + Real.log 3) * |v| := by
      rw [abs_of_nonneg (sq_nonneg v), abs_mul, abs_of_pos (add_pos hA hD)]
    _ ≤ _ := add_le_add hv2 (mul_le_mul_of_nonneg_left hv (add_pos hA hD).le)

theorem primeCore_tail_bound {β θ : ℝ} (hβ : 0 < β) (hθ : β / 2 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℝ in atTop,
      (primeDistribution (β * L)).real (primeCore (β * L) L θ)ᶜ ≤
        Real.exp (-c * Real.sqrt L) := by
  obtain ⟨c, hc, hh⟩ := primeDistribution_exponential_concentration hβ hθ
  refine ⟨c, hc, hh.mono (fun L hL => ?_)⟩
  apply (measureReal_mono (show (primeCore (β * L) L θ)ᶜ ⊆
    {z | θ * L ≤ primeLogValue (β * L) z} from ?_)).trans hL
  intro z hz
  change ¬primeLogValue (β * L) z ≤ θ * L at hz
  exact (le_of_lt (lt_of_not_ge hz))

theorem weightedLattice_uniform_error {β θ C : ℝ} (hβ : 0 < β)
    (hθlo : β / 2 < θ) (hθhi : θ < 1) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ v : ℝ, |v| ≤ C * Real.log L →
      |weightedLatticeCount (β * L) (L + v) - weightedLatticeCount (β * L) L -
        v * latticeMainWeight (β * L) L θ| ≤ ε * L := by
  have hA : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hθ0 : 0 < θ := lt_trans (by positivity : 0 < β / 2) hθlo
  have h₁ : 0 < 1 - θ := sub_pos.mpr hθhi
  obtain ⟨c, hc, htail⟩ := primeCore_tail_bound hβ hθlo
  have hlocal := lattice_uniform_increment_error hA hD log_two_div_log_three_irrational
    h₁ (show 1 - θ ≤ (1 : ℝ) by linarith) (show 0 < ε / 3 by positivity)
  have hwindow := logarithmic_window_small C
    (lt_min (by norm_num : (0 : ℝ) < 1) (show 0 < (1 - θ) / 2 by linarith))
  have hp := eventually_le_mul_of_div_tendsto_zero (lattice_polynomial_window_tendsto C)
    (show 0 < ε / 3 by positivity)
  have ht := eventually_le_mul_of_div_tendsto_zero (lattice_tail_window_tendsto hc)
    (show 0 < ε / 3 by positivity)
  filter_upwards [hlocal, hwindow, hp, ht, htail, eventually_ge_atTop (1 : ℝ)]
    with L hlocalL hwindowL hpL htL htailL hL
  intro v hv
  have hL0 : 0 ≤ L := by linarith
  have hvL : |v| ≤ L := hv.trans (hwindowL.trans (by nlinarith [min_le_left (1 : ℝ) ((1 - θ) / 2)]))
  have hvs : |v| ≤ ((1 - θ) / 2) * L :=
    hv.trans (hwindowL.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL0))
  have hh := weightedLattice_local_error (β * L) hL0 hθhi
    (show 0 ≤ ε / 3 by positivity) hvs (fun u hu => by
      exact hlocalL u (by simpa only [one_mul] using hu) v hvs)
  have hb := lattice_window_global_bound hL hvL
  have hbn : 0 ≤ 2 * ((1 + (L + |v|) / Real.log 2) * (1 + (L + |v|) / Real.log 3)) := by positivity
  have htail' :
      (2 * ((1 + (L + |v|) / Real.log 2) * (1 + (L + |v|) / Real.log 3))) *
          (primeDistribution (β * L)).real (primeCore (β * L) L θ)ᶜ ≤
        2 * ((1 + 2 / Real.log 2) * (1 + 2 / Real.log 3)) * L ^ 2 *
          Real.exp (-c * Real.sqrt L) := by
    calc
      _ ≤ (2 * ((1 + (L + |v|) / Real.log 2) * (1 + (L + |v|) / Real.log 3))) *
          Real.exp (-c * Real.sqrt L) := mul_le_mul_of_nonneg_left htailL hbn
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        nlinarith [hb]
  have hp' := lattice_window_polynomial_bound hC hL hv
  have hcoeff : v * latticeMainWeight (β * L) L θ =
      (v / (Real.log 2 * Real.log 3)) *
        (∫ z, truncatedGap (β * L) L θ z ∂primeDistribution (β * L)) := by
    unfold latticeMainWeight
    ring
  rw [hcoeff]
  exact hh.trans (by linarith)

theorem latticeMainWeight_bounds {β θ : ℝ} (hβ : 0 < β)
    (hθlo : β / 2 < θ) (hθhi : θ < 1) :
    ∀ᶠ L : ℝ in atTop,
      (1 - θ) / (2 * Real.log 2 * Real.log 3) * L ≤ latticeMainWeight (β * L) L θ ∧
      latticeMainWeight (β * L) L θ ≤ L / (Real.log 2 * Real.log 3) := by
  have hA : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨c, hc, htail⟩ := primeCore_tail_bound hβ hθlo
  have he : Tendsto (fun L : ℝ => Real.exp (-c * Real.sqrt L)) atTop (𝓝 0) := by
    have hh := (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hc)).mpr Real.tendsto_sqrt_atTop
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hh
  have he' := he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [htail, he', eventually_ge_atTop (0 : ℝ)] with L ht heL hL
  have hm := probReal_add_probReal_compl (μ := primeDistribution (β * L))
    (primeCore_measurable (β * L) L θ)
  have hmass : (1 / 2 : ℝ) ≤ (primeDistribution (β * L)).real (primeCore (β * L) L θ) := by
    linarith
  have hg := truncatedGap_integral_bounds (β * L) hL hθhi.le
  have hlo : (1 - θ) * L / 2 ≤ ∫ z, truncatedGap (β * L) L θ z ∂primeDistribution (β * L) := by
    have hh := mul_le_mul_of_nonneg_left hmass (mul_nonneg (sub_pos.mpr hθhi).le hL)
    linarith [hg.1]
  constructor
  · unfold latticeMainWeight
    apply (le_div_iff₀ (mul_pos hA hD)).mpr
    convert hlo using 1 <;> first | rfl | field_simp
  · exact div_le_div_of_nonneg_right hg.2 (mul_pos hA hD).le


theorem weightedLattice_uniform_relative_error {β θ C : ℝ} (hβ : 0 < β)
    (hθlo : β / 2 < θ) (hθhi : θ < 1) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ v : ℝ, |v| ≤ C * Real.log L →
      |weightedLatticeCount (β * L) (L + v) - weightedLatticeCount (β * L) L -
        v * latticeMainWeight (β * L) L θ| ≤ ε * latticeMainWeight (β * L) L θ := by
  let k := (1 - θ) / (2 * Real.log 2 * Real.log 3)
  have hk : 0 < k := by
    dsimp [k]
    exact div_pos (sub_pos.mpr hθhi) (mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
      (Real.log_pos (by norm_num)))
  have he := weightedLattice_uniform_error hβ hθlo hθhi hC (mul_pos hε hk)
  filter_upwards [he, latticeMainWeight_bounds hβ hθlo hθhi] with L hL hw
  intro v hv
  have hh := hL v hv
  have hh' := mul_le_mul_of_nonneg_left hw.1 hε.le
  dsimp [k] at hh
  exact hh.trans (by convert hh' using 1; ring)

end MatchingEstimate710
end

section
open Filter
open scoped Topology


namespace MatchingEstimate710

noncomputable def arithmeticMainWeight (β θ L : ℝ) : ℝ :=
  primeMassNormalizer (β * L) * latticeMainWeight (β * L) L θ

theorem arithmeticMainWeight_bounds {β θ : ℝ} (hβ : 0 < β)
    (hθlo : β / 2 < θ) (hθhi : θ < 1) :
    ∀ᶠ L : ℝ in atTop,
      0 < arithmeticMainWeight β θ L ∧
      (1 - θ) / (2 * Real.log 2 * Real.log 3) * primeMassNormalizer (β * L) * L ≤
        arithmeticMainWeight β θ L ∧
      arithmeticMainWeight β θ L ≤ primeMassNormalizer (β * L) * L / (Real.log 2 * Real.log 3) := by
  filter_upwards [latticeMainWeight_bounds hβ hθlo hθhi, eventually_gt_atTop (0 : ℝ)]
    with L hW hL
  have hZ := primeMassNormalizer_pos (mul_pos hβ hL)
  have hk : 0 < (1 - θ) / (2 * Real.log 2 * Real.log 3) := by
    exact div_pos (sub_pos.mpr hθhi) (mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
      (Real.log_pos (by norm_num)))
  have hW0 : 0 < latticeMainWeight (β * L) L θ := (mul_pos hk hL).trans_le hW.1
  refine ⟨mul_pos hZ hW0, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hW.1 hZ.le
    simpa only [arithmeticMainWeight, mul_assoc, mul_left_comm, mul_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left hW.2 hZ.le
    simpa only [arithmeticMainWeight, mul_div_assoc] using hh

theorem weightedSum_uniform_log_error {β θ C : ℝ} (hβ : 0 < β)
    (hθlo : β / 2 < θ) (hθhi : θ < 1) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ v : ℝ, |v| ≤ C * Real.log L →
      |weightedSum (β * L) (Real.exp (L + v)) - weightedSum (β * L) (Real.exp L) -
        v * arithmeticMainWeight β θ L| ≤ ε * arithmeticMainWeight β θ L := by
  filter_upwards [weightedLattice_uniform_relative_error hβ hθlo hθhi hC hε,
    eventually_gt_atTop (0 : ℝ)] with L hL hL0
  intro v hv
  have hy := mul_pos hβ hL0
  have hZ := primeMassNormalizer_pos hy
  have hh := mul_le_mul_of_nonneg_left (hL v hv) hZ.le
  rw [weightedSum_eq_convolution hy (Real.exp_pos _),
    weightedSum_eq_convolution hy (Real.exp_pos _), Real.log_exp, Real.log_exp]
  have he : primeMassNormalizer (β * L) * weightedLatticeCount (β * L) (L + v) -
      primeMassNormalizer (β * L) * weightedLatticeCount (β * L) L -
      v * arithmeticMainWeight β θ L = primeMassNormalizer (β * L) *
        (weightedLatticeCount (β * L) (L + v) - weightedLatticeCount (β * L) L -
          v * latticeMainWeight (β * L) L θ) := by
    unfold arithmeticMainWeight
    ring
  rw [he, abs_mul, abs_of_pos hZ]
  simpa only [arithmeticMainWeight, mul_assoc, mul_left_comm, mul_comm] using hh


theorem weightedSum_uniform_integer_error {β θ C : ℝ} (hβ : 0 < β)
    (hθlo : β / 2 < θ) (hθhi : θ < 1) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ v : ℝ, |v| ≤ C * Real.log (Real.log n) →
      |weightedSum (β * Real.log n) ((n : ℝ) * Real.exp v) - weightedSum (β * Real.log n) n -
        v * arithmeticMainWeight β θ (Real.log n)| ≤ ε * arithmeticMainWeight β θ (Real.log n) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (weightedSum_uniform_log_error hβ hθlo hθhi hC hε),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro v hv
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hh := hn v hv
  simpa only [Real.exp_add, Real.exp_log hnR] using hh

end MatchingEstimate710
end

section
open MeasureTheory Set
open scoped BigOperators Classical


namespace MatchingEstimate710

noncomputable def weightedLogAtom (y : ℝ) (n m : ℕ) : Measure ℝ :=
  ENNReal.ofReal (rho y m) • Measure.dirac (Real.log ((m : ℝ) / n))

instance weightedLogAtom_finite (y : ℝ) (n m : ℕ) : IsFiniteMeasure (weightedLogAtom y n m) :=
  (Measure.dirac _).smul_finite (by simp)

noncomputable def finiteLogMeasure (y : ℝ) (n N : ℕ) : Measure ℝ :=
  ∑ m ∈ Finset.Icc 1 N, weightedLogAtom y n m

instance finiteLogMeasure_finite (y : ℝ) (n N : ℕ) : IsFiniteMeasure (finiteLogMeasure y n N) := by
  unfold finiteLogMeasure
  infer_instance

theorem finiteLogMeasure_apply (y : ℝ) (n N : ℕ) (S : Set ℝ) :
    (finiteLogMeasure y n N).real S =
      (Finset.Icc 1 N).sum (fun m : ℕ =>
        if Real.log ((m : ℝ) / n) ∈ S then rho y m else 0) := by
  classical
  rw [finiteLogMeasure, measureReal_def, Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun m _ => measure_ne_top (weightedLogAtom y n m) S)]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : Real.log ((m : ℝ) / n) ∈ S <;>
    simp [weightedLogAtom, Measure.smul_apply, Measure.dirac_apply, Set.indicator, hm, rho_nonneg]

theorem finiteLogMeasure_integral (y : ℝ) (n N : ℕ) (f : ℝ → ℝ) :
    (∫ v, f v ∂finiteLogMeasure y n N) =
      ∑ m ∈ Finset.Icc 1 N, rho y m * f (Real.log ((m : ℝ) / n)) := by
  classical
  rw [finiteLogMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro m _
    rw [weightedLogAtom, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (rho_nonneg y m), smul_eq_mul]
  · intro m _
    exact (integrable_dirac (by finiteness)).smul_measure (by simp)

theorem finiteLogMeasure_setIntegral (y : ℝ) (n N : ℕ) (f : ℝ → ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ v in S, f v ∂finiteLogMeasure y n N) =
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => Real.log ((m : ℝ) / n) ∈ S),
        rho y m * f (Real.log ((m : ℝ) / n)) := by
  classical
  rw [← integral_indicator hS, finiteLogMeasure_integral, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : Real.log ((m : ℝ) / n) ∈ S <;> simp [Set.indicator, hm]

theorem log_ratio_mem_Ioc {n m a b : ℝ} (hn : 0 < n) (hm : 0 < m) :
    Real.log (m / n) ∈ Ioc a b ↔ n * Real.exp a < m ∧ m ≤ n * Real.exp b := by
  rw [mem_Ioc, ← Real.exp_lt_exp, ← Real.exp_le_exp, Real.exp_log (div_pos hm hn),
    lt_div_iff₀ hn, div_le_iff₀ hn]
  simp only [mul_comm]

theorem weighted_sum_interval {A B : ℝ} {N : ℕ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hBN : B ≤ (N : ℝ)) (y : ℝ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => A < (m : ℝ) ∧ (m : ℝ) ≤ B), rho y m) =
      weightedSum y B - weightedSum y A := by
  have hB : 0 ≤ B := hA.trans hAB
  have hfloor : ⌊B⌋₊ ≤ N := by
    simpa only [Nat.floor_natCast] using Nat.floor_mono hBN
  have hsets : (Finset.Icc 1 N).filter (fun m : ℕ => A < (m : ℝ) ∧ (m : ℝ) ≤ B) =
      Finset.Icc 1 ⌊B⌋₊ \ Finset.Icc 1 ⌊A⌋₊ := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    rw [← Nat.floor_lt hA, ← Nat.le_floor_iff hB]
    omega
  have hsub : Finset.Icc 1 ⌊A⌋₊ ⊆ Finset.Icc 1 ⌊B⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hAB)
  rw [hsets, Finset.sum_sdiff_eq_sub hsub]
  rfl

theorem finiteLogMeasure_Ioc (y : ℝ) {n N : ℕ} (hn : 0 < n) {a b : ℝ}
    (hab : a ≤ b) (hbN : (n : ℝ) * Real.exp b ≤ N) :
    (finiteLogMeasure y n N).real (Ioc a b) =
      weightedSum y ((n : ℝ) * Real.exp b) - weightedSum y ((n : ℝ) * Real.exp a) := by
  classical
  rw [finiteLogMeasure_apply]
  trans ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => Real.log ((m : ℝ) / n) ∈ Ioc a b), rho y m
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : Real.log ((m : ℝ) / n) ∈ Ioc a b <;> simp [h]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (Finset.Icc 1 N).filter (fun m : ℕ => Real.log ((m : ℝ) / n) ∈ Ioc a b) =
      (Finset.Icc 1 N).filter (fun m : ℕ => (n : ℝ) * Real.exp a < m ∧ (m : ℝ) ≤ (n : ℝ) * Real.exp b) := by
    apply Finset.filter_congr
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
    exact log_ratio_mem_Ioc hnR hmR
  rw [hs]
  apply weighted_sum_interval (mul_nonneg hnR.le (Real.exp_nonneg _)) _ hbN
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab) hnR.le

end MatchingEstimate710
end

section
open scoped BigOperators

namespace MatchingEstimate710


theorem hall_of_fractional_weights {I J : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq J] (t : I → Finset J) (w : I → J → ℝ)
    (hpos : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, 1 ≤ ∑ j ∈ t i, w i j)
    (hcol : ∀ j, ∑ i, w i j ≤ 1) :
    ∀ S : Finset I, S.card ≤ (S.biUnion t).card := by
  intro S
  have hrow' : ∀ i ∈ S, 1 ≤ ∑ j ∈ S.biUnion t, w i j := by
    intro i hi
    exact (hrow i).trans
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_biUnion_of_mem t hi) (fun j _ _ => hpos i j))
  have hcol' : ∀ j, ∑ i ∈ S, w i j ≤ 1 := by
    intro j
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun i _ _ => hpos i j)).trans (hcol j)
  have hc : (S.card : ℝ) ≤ ((S.biUnion t).card : ℝ) := by
    calc
      (S.card : ℝ) = ∑ i ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ S, ∑ j ∈ S.biUnion t, w i j := Finset.sum_le_sum hrow'
      _ = ∑ j ∈ S.biUnion t, ∑ i ∈ S, w i j := Finset.sum_comm
      _ ≤ ∑ j ∈ S.biUnion t, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hcol' j)
      _ = ((S.biUnion t).card : ℝ) := by simp
  exact_mod_cast hc

theorem hasMatching_of_fractional_weights (n h : ℕ) (w : Fin n → ℕ → ℝ)
    (hpos : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, 1 ≤ ∑ j ∈ neighbors n h i, w i j)
    (hcol : ∀ j, ∑ i, w i j ≤ 1) : HasMatching n h := by
  classical
  exact (hall_iff_hasMatching n h).mp
    (hall_of_fractional_weights (neighbors n h) w hpos hrow hcol)


theorem weighted_matching_sum_le {I J : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq J] (T : Finset J) (a : I → J) (ha : Function.Injective a)
    (haT : ∀ i, a i ∈ T) (u : I → ℝ) (v : J → ℝ)
    (hv : ∀ j ∈ T, 0 ≤ v j) (hdom : ∀ i, u i ≤ v (a i)) :
    ∑ i, u i ≤ ∑ j ∈ T, v j := by
  calc
    ∑ i, u i ≤ ∑ i, v (a i) := Finset.sum_le_sum (fun i _ => hdom i)
    _ = ∑ j ∈ Finset.univ.image a, v j :=
      (Finset.sum_image (fun i _ j _ h => ha h)).symm
    _ ≤ ∑ j ∈ T, v j := Finset.sum_le_sum_of_subset_of_nonneg
      (by simpa only [Finset.image_subset_iff, Finset.mem_univ, forall_true_left] using haT)
      (fun j hj _ => hv j hj)


theorem no_matching_of_weighted_obstruction (n h : ℕ)
    (u : Fin n → ℝ) (v : ℕ → ℝ)
    (hv : ∀ j ∈ Finset.Ioo n (n + h), 0 ≤ v j)
    (hdom : ∀ i j, n < j → j < n + h → (i.val + 1) ∣ j → u i ≤ v j)
    (hgap : (∑ j ∈ Finset.Ioo n (n + h), v j) < ∑ i, u i) :
    ¬ HasMatching n h := by
  classical
  rintro ⟨a, ha, had⟩
  have hle := weighted_matching_sum_le (Finset.Ioo n (n + h)) a ha
    (fun i => Finset.mem_Ioo.mpr ⟨(had i).1, (had i).2.1⟩) u v hv
    (fun i => hdom i (a i) (had i).1 (had i).2.1 (had i).2.2)
  exact hgap.not_ge hle

theorem length_lt_f_of_no_matching {n h : ℕ} (hn : ¬ HasMatching n h) : h < f n := by
  by_contra hc
  exact hn (hasMatching_mono n (by omega) (f_spec n))

end MatchingEstimate710
end

section
open Set

namespace MatchingEstimate710

noncomputable def leftParameterMap (x : ℝ) : ℝ := x * Real.exp (x - 1)
noncomputable def rightParameterMap (x : ℝ) : ℝ := x * Real.exp (1 - x)

theorem leftParameterMap_continuous : Continuous leftParameterMap :=
  continuous_id.mul (Real.continuous_exp.comp (continuous_id.sub continuous_const))

theorem rightParameterMap_continuous : Continuous rightParameterMap :=
  continuous_id.mul (Real.continuous_exp.comp (continuous_const.sub continuous_id))

theorem leftParameter_exists {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1, leftParameterMap x = t := by
  apply intermediate_value_Icc (a := (0 : ℝ)) (b := 1) zero_le_one
    leftParameterMap_continuous.continuousOn
  simpa [leftParameterMap] using ht

theorem rightParameter_exists {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1, rightParameterMap x = t := by
  apply intermediate_value_Icc (a := (0 : ℝ)) (b := 1) zero_le_one
    rightParameterMap_continuous.continuousOn
  simpa [rightParameterMap] using ht

noncomputable def leftParameter (t : ℝ) : ℝ :=
  if ht : t ∈ Icc (0 : ℝ) 1 then (leftParameter_exists ht).choose else 0

noncomputable def rightParameter (t : ℝ) : ℝ :=
  if ht : t ∈ Icc (0 : ℝ) 1 then (rightParameter_exists ht).choose else 0

theorem leftParameter_spec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    leftParameter t ∈ Icc (0 : ℝ) 1 ∧ leftParameterMap (leftParameter t) = t := by
  simpa only [leftParameter, dif_pos ht] using (leftParameter_exists ht).choose_spec

theorem rightParameter_spec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rightParameter t ∈ Icc (0 : ℝ) 1 ∧ rightParameterMap (rightParameter t) = t := by
  simpa only [rightParameter, dif_pos ht] using (rightParameter_exists ht).choose_spec

noncomputable def Phi (t : ℝ) : ℝ := 1 - leftParameter t
noncomputable def H (t : ℝ) : ℝ := 1 + rightParameter t

theorem Phi_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ Phi t ∧ Phi t ≤ 1 := by
  have hh := (leftParameter_spec ht).1
  unfold Phi
  constructor <;> linarith [hh.1, hh.2]

theorem H_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 ≤ H t ∧ H t ≤ 2 := by
  have hh := (rightParameter_spec ht).1
  unfold H
  constructor <;> linarith [hh.1, hh.2]

theorem scalar_envelope {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Phi t ≤ H r * cofactorProfile (Real.sqrt (r * t)) := by
  have hx := leftParameter_spec ht
  have hz := rightParameter_spec hr
  have hh := scalar_envelope_parametric hx.1.1 hz.1.1
  change 1 - leftParameter t ≤ (1 + rightParameter r) *
    cofactorProfile (Real.sqrt (r * t))
  change 1 - leftParameter t ≤ (1 + rightParameter r) *
    cofactorProfile (Real.sqrt
      (rightParameterMap (rightParameter r) * leftParameterMap (leftParameter t))) at hh
  simpa only [hx.2, hz.2] using hh

noncomputable def lowerSourceWeight (y : ℝ) (T i : ℕ) : ℝ :=
  if (T : ℝ) / y < (i : ℝ) then rho y i * Phi ((T : ℝ) / (y * (i : ℝ))) else 0

noncomputable def lowerTargetWeight (y : ℝ) (T m : ℕ) : ℝ :=
  rho y m * H ((m : ℝ) / (T : ℝ))

theorem lowerTargetWeight_nonneg {y : ℝ} {T m : ℕ} (hm : 0 < m) (hmT : m ≤ T) :
    0 ≤ lowerTargetWeight y T m := by
  have hT : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le hm hmT
  have hr : (m : ℝ) / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hT.le, (div_le_one hT).mpr (by exact_mod_cast hmT)⟩
  exact mul_nonneg (rho_nonneg y m) (by linarith [(H_bounds hr).1])


theorem lower_edge_domination {y : ℝ} (hy : 0 < y) {T i m : ℕ}
    (hi : 0 < i) (hm : 0 < m) (hmT : m ≤ T) (hdvd : i ∣ m) :
    lowerSourceWeight y T i ≤ lowerTargetWeight y T m := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hT : (0 : ℝ) < T := by exact_mod_cast lt_of_lt_of_le hm hmT
  have hmTR : (m : ℝ) ≤ T := by exact_mod_cast hmT
  unfold lowerSourceWeight
  split_ifs with hcut
  · obtain ⟨q, hq⟩ := hdvd
    have hq0 : q ≠ 0 := by intro h; simp [h] at hq; omega
    have hqR : (q : ℝ) < y := by
      have heq : (m : ℝ) = (i : ℝ) * (q : ℝ) := by exact_mod_cast hq
      have hTi : (T : ℝ) < (i : ℝ) * y := (div_lt_iff₀ hy).mp hcut
      by_contra hc
      have hqq := mul_le_mul_of_nonneg_left (le_of_not_gt hc) hiR.le
      linarith
    have ht : (T : ℝ) / (y * (i : ℝ)) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one (mul_pos hy hiR)).mpr
        have hh := (div_lt_iff₀ hy).mp hcut
        nlinarith
    have hr : (m : ℝ) / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hmR.le hT.le, (div_le_one hT).mpr hmTR⟩
    have hrt : ((m : ℝ) / T) * ((T : ℝ) / (y * (i : ℝ))) = (q : ℝ) / y := by
      have heq : (m : ℝ) = (i : ℝ) * (q : ℝ) := by exact_mod_cast hq
      rw [heq]
      field_simp [ne_of_gt hT, ne_of_gt hiR, ne_of_gt hy]
    have he := scalar_envelope hr ht
    rw [hrt] at he
    have hc := cofactor_domination hq0 hy hqR
    have hH : 0 ≤ H ((m : ℝ) / T) := by linarith [(H_bounds hr).1]
    have hh := he.trans (mul_le_mul_of_nonneg_left hc hH)
    have hfinal := mul_le_mul_of_nonneg_left hh (rho_nonneg y i)
    simpa only [lowerTargetWeight, hq, rho_mul y (Nat.ne_of_gt hi) hq0,
      mul_assoc, mul_comm, mul_left_comm] using hfinal
  · exact lowerTargetWeight_nonneg hm hmT


theorem f_gt_of_lower_weight_gap (n h : ℕ) {y : ℝ} (hy : 0 < y)
    (hgap : (∑ m ∈ Finset.Ioo n (n + h), lowerTargetWeight y (n + h - 1) m) <
      ∑ i : Fin n, lowerSourceWeight y (n + h - 1) (i.val + 1)) :
    h < f n := by
  apply length_lt_f_of_no_matching
  apply no_matching_of_weighted_obstruction n h
    (fun i => lowerSourceWeight y (n + h - 1) (i.val + 1))
    (lowerTargetWeight y (n + h - 1))
  · intro m hm
    have hh := Finset.mem_Ioo.mp hm
    exact lowerTargetWeight_nonneg (by omega) (by omega)
  · intro i m hlo hhi hd
    exact lower_edge_domination hy (by omega) (by omega) (by omega) hd
  · exact hgap

end MatchingEstimate710
end

section
open Set

namespace MatchingEstimate710

theorem leftParameterMap_deriv (x : ℝ) :
    HasDerivAt leftParameterMap ((1 + x) * Real.exp (x - 1)) x := by
  convert (hasDerivAt_id x).mul (((hasDerivAt_id x).sub_const 1).exp) using 1 <;> try rfl
  dsimp
  ring

theorem rightParameterMap_deriv (x : ℝ) :
    HasDerivAt rightParameterMap ((1 - x) * Real.exp (1 - x)) x := by
  convert (hasDerivAt_id x).mul (((hasDerivAt_id x).const_sub 1).exp) using 1 <;> try rfl
  dsimp
  ring

theorem leftParameterMap_strictMono : StrictMonoOn leftParameterMap (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) leftParameterMap_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(leftParameterMap_deriv x).deriv]
  exact mul_pos (by linarith [hx.1]) (Real.exp_pos _)

theorem rightParameterMap_strictMono : StrictMonoOn rightParameterMap (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) rightParameterMap_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(rightParameterMap_deriv x).deriv]
  exact mul_pos (by linarith [hx.2]) (Real.exp_pos _)

private theorem map_Icc {f : ℝ → ℝ} (hf : StrictMonoOn f (Icc (0 : ℝ) 1))
    (h0 : f 0 = 0) (h1 : f 1 = 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← h0]
    exact hf.monotoneOn ⟨le_rfl, zero_le_one⟩ hx hx.1
  · rw [← h1]
    exact hf.monotoneOn hx ⟨zero_le_one, le_rfl⟩ hx.2

private noncomputable def inverseOrderIso (f g : ℝ → ℝ)
    (hf : StrictMonoOn f (Icc (0 : ℝ) 1)) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ Icc (0 : ℝ) 1 ∧ f (g t) = t) :
    Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 where
  toFun x := ⟨f x, map_Icc hf h0 h1 x.property⟩
  invFun t := ⟨g t, (hg t t.property).1⟩
  left_inv x := by
    apply Subtype.ext
    exact hf.injOn (hg (f x) (map_Icc hf h0 h1 x.property)).1 x.property
      (hg (f x) (map_Icc hf h0 h1 x.property)).2
  right_inv t := Subtype.ext (hg t t.property).2
  map_rel_iff' := by
    intro x y
    exact hf.le_iff_le x.property y.property

private theorem inverse_continuousOn (f g : ℝ → ℝ)
    (hf : StrictMonoOn f (Icc (0 : ℝ) 1)) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ Icc (0 : ℝ) 1 ∧ f (g t) = t) :
    ContinuousOn g (Icc (0 : ℝ) 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_subtype_val.comp (inverseOrderIso f g hf h0 h1 hg).symm.continuous

theorem leftParameter_continuousOn : ContinuousOn leftParameter (Icc (0 : ℝ) 1) :=
  inverse_continuousOn leftParameterMap leftParameter leftParameterMap_strictMono
    (by simp [leftParameterMap]) (by simp [leftParameterMap]) (fun _ ht => leftParameter_spec ht)

theorem rightParameter_continuousOn : ContinuousOn rightParameter (Icc (0 : ℝ) 1) :=
  inverse_continuousOn rightParameterMap rightParameter rightParameterMap_strictMono
    (by simp [rightParameterMap]) (by simp [rightParameterMap]) (fun _ ht => rightParameter_spec ht)

theorem Phi_continuousOn : ContinuousOn Phi (Icc (0 : ℝ) 1) :=
  continuousOn_const.sub leftParameter_continuousOn

theorem H_continuousOn : ContinuousOn H (Icc (0 : ℝ) 1) :=
  continuousOn_const.add rightParameter_continuousOn

theorem leftParameter_monotoneOn : MonotoneOn leftParameter (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply (leftParameterMap_strictMono.le_iff_le (leftParameter_spec hx).1
    (leftParameter_spec hy).1).mp
  simpa only [(leftParameter_spec hx).2, (leftParameter_spec hy).2] using hxy

theorem rightParameter_monotoneOn : MonotoneOn rightParameter (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply (rightParameterMap_strictMono.le_iff_le (rightParameter_spec hx).1
    (rightParameter_spec hy).1).mp
  simpa only [(rightParameter_spec hx).2, (rightParameter_spec hy).2] using hxy

theorem Phi_antitoneOn : AntitoneOn Phi (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hh := leftParameter_monotoneOn hx hy hxy
  dsimp [Phi]
  linarith

theorem H_monotoneOn : MonotoneOn H (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hh := rightParameter_monotoneOn hx hy hxy
  dsimp [H]
  linarith

end MatchingEstimate710
end

section
open Set Filter MeasureTheory
open scoped Topology


namespace MatchingEstimate710

noncomputable def leftLogCoordinate (x : ℝ) : ℝ := -Real.log x + 1 - x
noncomputable def rightLogCoordinate (x : ℝ) : ℝ := -Real.log x - 1 + x

theorem leftParameter_map {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    leftParameter (leftParameterMap x) = x := by
  have ht : leftParameterMap x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have hh := leftParameterMap_strictMono.monotoneOn ⟨le_rfl, zero_le_one⟩ hx hx.1
      simpa [leftParameterMap] using hh
    · have hh := leftParameterMap_strictMono.monotoneOn hx ⟨zero_le_one, le_rfl⟩ hx.2
      simpa [leftParameterMap] using hh
  exact leftParameterMap_strictMono.injOn (leftParameter_spec ht).1 hx (leftParameter_spec ht).2

theorem rightParameter_map {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    rightParameter (rightParameterMap x) = x := by
  have ht : rightParameterMap x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have hh := rightParameterMap_strictMono.monotoneOn ⟨le_rfl, zero_le_one⟩ hx hx.1
      simpa [rightParameterMap] using hh
    · have hh := rightParameterMap_strictMono.monotoneOn hx ⟨zero_le_one, le_rfl⟩ hx.2
      simpa [rightParameterMap] using hh
  exact rightParameterMap_strictMono.injOn (rightParameter_spec ht).1 hx (rightParameter_spec ht).2

theorem exp_neg_leftLogCoordinate {x : ℝ} (hx : 0 < x) :
    Real.exp (-leftLogCoordinate x) = leftParameterMap x := by
  have he : -leftLogCoordinate x = Real.log x + (x - 1) := by unfold leftLogCoordinate; ring
  rw [he, Real.exp_add, Real.exp_log hx, leftParameterMap]

theorem exp_neg_rightLogCoordinate {x : ℝ} (hx : 0 < x) :
    Real.exp (-rightLogCoordinate x) = rightParameterMap x := by
  have he : -rightLogCoordinate x = Real.log x + (1 - x) := by unfold rightLogCoordinate; ring
  rw [he, Real.exp_add, Real.exp_log hx, rightParameterMap]

theorem leftLogCoordinate_nonneg {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ leftLogCoordinate x := by
  have hh := Real.log_nonpos hx.le hx1
  unfold leftLogCoordinate
  linarith

theorem rightLogCoordinate_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ rightLogCoordinate x := by
  have hh := Real.log_le_sub_one_of_pos hx
  unfold rightLogCoordinate
  linarith

theorem leftLogCoordinate_deriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt leftLogCoordinate (-x⁻¹ - 1) x := by
  convert ((Real.hasDerivAt_log hx).neg.add_const 1).sub (hasDerivAt_id x) using 1 <;> rfl

theorem rightLogCoordinate_deriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt rightLogCoordinate (-x⁻¹ + 1) x := by
  convert ((Real.hasDerivAt_log hx).neg.sub_const 1).add (hasDerivAt_id x) using 1 <;> rfl

theorem leftLoss_continuousOn :
    ContinuousOn (fun s : ℝ => leftParameter (Real.exp (-s))) (Ici 0) := by
  apply leftParameter_continuousOn.comp (Real.continuous_exp.comp continuous_neg).continuousOn
  intro s hs
  exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)⟩

theorem rightLoss_continuousOn :
    ContinuousOn (fun s : ℝ => rightParameter (Real.exp (-s))) (Ici 0) := by
  apply rightParameter_continuousOn.comp (Real.continuous_exp.comp continuous_neg).continuousOn
  intro s hs
  exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)⟩

theorem leftLoss_coordinate_integral {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (∫ s in 0..leftLogCoordinate x, leftParameter (Real.exp (-s))) =
      3 / 2 - x - x ^ 2 / 2 := by
  have hd : ∀ t ∈ uIcc x 1, HasDerivAt leftLogCoordinate (-t⁻¹ - 1) t := by
    rw [uIcc_of_le hx1]
    intro t ht
    exact leftLogCoordinate_deriv (ne_of_gt (hx.trans_le ht.1))
  have hc : ContinuousOn (fun t : ℝ => -t⁻¹ - 1) (uIcc x 1) := by
    rw [uIcc_of_le hx1]
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hx.trans_le ht.1)
    fun_prop
  have hg : ContinuousOn (fun s : ℝ => leftParameter (Real.exp (-s)))
      (leftLogCoordinate '' uIcc x 1) := by
    apply leftLoss_continuousOn.mono
    rintro s ⟨t, ht, rfl⟩
    rw [uIcc_of_le hx1] at ht
    exact leftLogCoordinate_nonneg (hx.trans_le ht.1) ht.2
  have hi := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  have hcoord1 : leftLogCoordinate 1 = 0 := by simp [leftLogCoordinate]
  rw [hcoord1, intervalIntegral.integral_symm (a := 0) (b := leftLogCoordinate x)] at hi
  have he : (∫ t in x..1,
      ((fun s : ℝ => leftParameter (Real.exp (-s))) ∘ leftLogCoordinate) t * (-t⁻¹ - 1)) =
        -(∫ t in x..1, (1 + t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx1] at ht
    have ht0 : 0 < t := hx.trans_le ht.1
    simp only [Function.comp_apply, exp_neg_leftLogCoordinate ht0, leftParameter_map ⟨ht0.le, ht.2⟩]
    field_simp
    ring
  rw [he] at hi
  have hf : (∫ t in x..1, (1 + t)) = 3 / 2 - x - x ^ 2 / 2 := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  linarith

theorem rightLoss_coordinate_integral {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (∫ s in 0..rightLogCoordinate x, rightParameter (Real.exp (-s))) =
      1 / 2 - x + x ^ 2 / 2 := by
  have hd : ∀ t ∈ uIcc x 1, HasDerivAt rightLogCoordinate (-t⁻¹ + 1) t := by
    rw [uIcc_of_le hx1]
    intro t ht
    exact rightLogCoordinate_deriv (ne_of_gt (hx.trans_le ht.1))
  have hc : ContinuousOn (fun t : ℝ => -t⁻¹ + 1) (uIcc x 1) := by
    rw [uIcc_of_le hx1]
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hx.trans_le ht.1)
    fun_prop
  have hg : ContinuousOn (fun s : ℝ => rightParameter (Real.exp (-s)))
      (rightLogCoordinate '' uIcc x 1) := by
    apply rightLoss_continuousOn.mono
    rintro s ⟨t, ht, rfl⟩
    rw [uIcc_of_le hx1] at ht
    exact rightLogCoordinate_nonneg (hx.trans_le ht.1)
  have hi := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  have hcoord1 : rightLogCoordinate 1 = 0 := by simp [rightLogCoordinate]
  rw [hcoord1, intervalIntegral.integral_symm (a := 0) (b := rightLogCoordinate x)] at hi
  have he : (∫ t in x..1,
      ((fun s : ℝ => rightParameter (Real.exp (-s))) ∘ rightLogCoordinate) t * (-t⁻¹ + 1)) =
        -(∫ t in x..1, (1 - t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx1] at ht
    have ht0 : 0 < t := hx.trans_le ht.1
    simp only [Function.comp_apply, exp_neg_rightLogCoordinate ht0, rightParameter_map ⟨ht0.le, ht.2⟩]
    field_simp
    ring
  rw [he] at hi
  have hf : (∫ t in x..1, (1 - t)) = 1 / 2 - x + x ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  linarith

theorem exp_neg_mem_unit {b : ℝ} (hb : 0 ≤ b) : Real.exp (-b) ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb)⟩

theorem leftLoss_integral {b : ℝ} (hb : 0 ≤ b) :
    (∫ s in 0..b, leftParameter (Real.exp (-s))) =
      3 / 2 - leftParameter (Real.exp (-b)) - (leftParameter (Real.exp (-b))) ^ 2 / 2 := by
  have hs := leftParameter_spec (exp_neg_mem_unit hb)
  have hp : 0 < leftParameter (Real.exp (-b)) := by
    have hv : 0 < leftParameterMap (leftParameter (Real.exp (-b))) := by
      rw [hs.2]
      exact Real.exp_pos _
    unfold leftParameterMap at hv
    exact pos_of_mul_pos_left hv (Real.exp_nonneg _)
  have hc : leftLogCoordinate (leftParameter (Real.exp (-b))) = b := by
    have he := (exp_neg_leftLogCoordinate hp).trans hs.2
    exact neg_inj.mp (Real.exp_injective he)
  simpa only [hc] using leftLoss_coordinate_integral hp hs.1.2

theorem rightLoss_integral {b : ℝ} (hb : 0 ≤ b) :
    (∫ s in 0..b, rightParameter (Real.exp (-s))) =
      1 / 2 - rightParameter (Real.exp (-b)) + (rightParameter (Real.exp (-b))) ^ 2 / 2 := by
  have hs := rightParameter_spec (exp_neg_mem_unit hb)
  have hp : 0 < rightParameter (Real.exp (-b)) := by
    have hv : 0 < rightParameterMap (rightParameter (Real.exp (-b))) := by
      rw [hs.2]
      exact Real.exp_pos _
    unfold rightParameterMap at hv
    exact pos_of_mul_pos_left hv (Real.exp_nonneg _)
  have hc : rightLogCoordinate (rightParameter (Real.exp (-b))) = b := by
    have he := (exp_neg_rightLogCoordinate hp).trans hs.2
    exact neg_inj.mp (Real.exp_injective he)
  simpa only [hc] using rightLoss_coordinate_integral hp hs.1.2

theorem exp_neg_tendsto_unit_zero :
    Tendsto (fun b : ℝ => Real.exp (-b)) atTop (nhdsWithin 0 (Icc (0 : ℝ) 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  exact exp_neg_mem_unit hb

theorem leftLoss_parameter_tendsto :
    Tendsto (fun b : ℝ => leftParameter (Real.exp (-b))) atTop (𝓝 0) := by
  have hf := leftParameter_continuousOn 0 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  have hz : leftParameter 0 = 0 := by
    simpa [leftParameterMap] using leftParameter_map (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  simpa only [hz, Function.comp_def] using hf.tendsto.comp exp_neg_tendsto_unit_zero

theorem rightLoss_parameter_tendsto :
    Tendsto (fun b : ℝ => rightParameter (Real.exp (-b))) atTop (𝓝 0) := by
  have hf := rightParameter_continuousOn 0 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  have hz : rightParameter 0 = 0 := by
    simpa [rightParameterMap] using rightParameter_map (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  simpa only [hz, Function.comp_def] using hf.tendsto.comp exp_neg_tendsto_unit_zero

theorem leftLoss_integral_tendsto :
    Tendsto (fun b : ℝ => ∫ s in 0..b, 1 - Phi (Real.exp (-s))) atTop (𝓝 (3 / 2)) := by
  have hc : Tendsto (fun _ : ℝ => (3 / 2 : ℝ)) atTop (𝓝 (3 / 2)) := tendsto_const_nhds
  have hh := (hc.sub leftLoss_parameter_tendsto).sub ((leftLoss_parameter_tendsto.pow 2).div_const 2)
  norm_num only [zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  simp only [Phi, sub_sub_cancel]
  exact (leftLoss_integral hb).symm

theorem rightLoss_integral_tendsto :
    Tendsto (fun b : ℝ => ∫ s in 0..b, H (Real.exp (-s)) - 1) atTop (𝓝 (1 / 2)) := by
  have hc : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) := tendsto_const_nhds
  have hh := (hc.sub rightLoss_parameter_tendsto).add ((rightLoss_parameter_tendsto.pow 2).div_const 2)
  norm_num only [zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  simp only [H, add_sub_cancel_left]
  exact (rightLoss_integral hb).symm

end MatchingEstimate710
end

section
open Set MeasureTheory


namespace MatchingEstimate710

theorem leftParameter_strictMonoOn : StrictMonoOn leftParameter (Icc (0 : ℝ) 1) := by
  intro t ht u hu htu
  apply (leftParameterMap_strictMono.lt_iff_lt (leftParameter_spec ht).1 (leftParameter_spec hu).1).mp
  simpa only [(leftParameter_spec ht).2, (leftParameter_spec hu).2] using htu

theorem rightParameter_strictMonoOn : StrictMonoOn rightParameter (Icc (0 : ℝ) 1) := by
  intro t ht u hu htu
  apply (rightParameterMap_strictMono.lt_iff_lt (rightParameter_spec ht).1 (rightParameter_spec hu).1).mp
  simpa only [(rightParameter_spec ht).2, (rightParameter_spec hu).2] using htu

theorem Phi_strictAntiOn : StrictAntiOn Phi (Icc (0 : ℝ) 1) := by
  intro t ht u hu htu
  have hh := leftParameter_strictMonoOn ht hu htu
  dsimp [Phi]
  linarith

theorem H_strictMonoOn : StrictMonoOn H (Icc (0 : ℝ) 1) := by
  intro t ht u hu htu
  have hh := rightParameter_strictMonoOn ht hu htu
  dsimp [H]
  linarith

noncomputable def sourceLogProfile (b v : ℝ) : ℝ := Phi (Real.exp (-b - v))
noncomputable def targetLogProfile (a v : ℝ) : ℝ := H (Real.exp (v - a))

theorem sourceLogProfile_argument {b v : ℝ} (hv : -b ≤ v) :
    Real.exp (-b - v) ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

theorem targetLogProfile_argument {a v : ℝ} (hv : v ≤ a) :
    Real.exp (v - a) ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

theorem sourceLogProfile_continuousOn (b : ℝ) :
    ContinuousOn (sourceLogProfile b) (Icc (-b) 0) := by
  apply Phi_continuousOn.comp (by fun_prop)
  intro v hv
  exact sourceLogProfile_argument hv.1

theorem targetLogProfile_continuousOn (a : ℝ) :
    ContinuousOn (targetLogProfile a) (Icc 0 a) := by
  apply H_continuousOn.comp (by fun_prop)
  intro v hv
  exact targetLogProfile_argument hv.2

theorem sourceLogProfile_strictMonoOn (b : ℝ) :
    StrictMonoOn (sourceLogProfile b) (Icc (-b) 0) := by
  intro u hu v hv huv
  apply Phi_strictAntiOn (sourceLogProfile_argument hv.1) (sourceLogProfile_argument hu.1)
  exact Real.exp_lt_exp.mpr (by linarith)

theorem targetLogProfile_strictMonoOn (a : ℝ) :
    StrictMonoOn (targetLogProfile a) (Icc 0 a) := by
  intro u hu v hv huv
  apply H_strictMonoOn (targetLogProfile_argument hu.2) (targetLogProfile_argument hv.2)
  exact Real.exp_lt_exp.mpr (by linarith)

theorem sourceLogProfile_bounds {b v : ℝ} (hv : v ∈ Icc (-b) 0) :
    0 ≤ sourceLogProfile b v ∧ sourceLogProfile b v ≤ 1 :=
  Phi_bounds (sourceLogProfile_argument hv.1)

theorem targetLogProfile_bounds {a v : ℝ} (hv : v ∈ Icc 0 a) :
    0 ≤ targetLogProfile a v ∧ targetLogProfile a v ≤ 2 := by
  have hh := H_bounds (targetLogProfile_argument hv.2)
  change 0 ≤ H (Real.exp (v - a)) ∧ H (Real.exp (v - a)) ≤ 2
  exact ⟨by linarith [hh.1], hh.2⟩

theorem sourceLogProfile_integral {b : ℝ} (hb : 0 ≤ b) :
    (∫ v in (-b)..0, sourceLogProfile b v) =
      b - 3 / 2 + leftParameter (Real.exp (-b)) + (leftParameter (Real.exp (-b))) ^ 2 / 2 := by
  have harg (v : ℝ) : -b - v = -(b + v) := by ring
  simp_rw [sourceLogProfile, harg]
  rw [intervalIntegral.integral_comp_add_left (fun s => Phi (Real.exp (-s))) b]
  simp only [add_neg_cancel, add_zero]
  have hi : IntervalIntegrable (fun s : ℝ => leftParameter (Real.exp (-s))) volume 0 b :=
    (leftLoss_continuousOn.mono (by intro s hs; exact hs.1)).intervalIntegrable_of_Icc hb
  rw [show (fun s : ℝ => Phi (Real.exp (-s))) =
    (fun s : ℝ => 1 - leftParameter (Real.exp (-s))) from rfl,
    intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const,
    leftLoss_integral hb]
  simp only [smul_eq_mul]
  ring

theorem targetLogProfile_integral {a : ℝ} (ha : 0 ≤ a) :
    (∫ v in 0..a, targetLogProfile a v) =
      a + 1 / 2 - rightParameter (Real.exp (-a)) + (rightParameter (Real.exp (-a))) ^ 2 / 2 := by
  have harg (v : ℝ) : v - a = -(a - v) := by ring
  simp_rw [targetLogProfile, harg]
  rw [intervalIntegral.integral_comp_sub_left (fun s => H (Real.exp (-s))) a]
  simp only [sub_self, sub_zero]
  have hi : IntervalIntegrable (fun s : ℝ => rightParameter (Real.exp (-s))) volume 0 a :=
    (rightLoss_continuousOn.mono (by intro s hs; exact hs.1)).intervalIntegrable_of_Icc ha
  rw [show (fun s : ℝ => H (Real.exp (-s))) =
    (fun s : ℝ => 1 + rightParameter (Real.exp (-s))) from rfl,
    intervalIntegral.integral_add intervalIntegrable_const hi, intervalIntegral.integral_const,
    rightLoss_integral ha]
  simp only [smul_eq_mul]
  ring

end MatchingEstimate710
end

section
open MeasureTheory Set Filter


namespace MatchingEstimate710

theorem integral_eq_bounded_layercake_lt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {M : ℝ} (hf : Integrable f μ)
    (hn : 0 ≤ᵐ[μ] f) (hb : f ≤ᵐ[μ] (fun _ => M)) :
    (∫ x, f x ∂μ) = ∫ t in Ioc 0 M, μ.real {x | t < f x} := by
  rw [hf.integral_eq_integral_Ioc_meas_le hn hb]
  apply integral_congr_ae
  filter_upwards [meas_le_ae_eq_meas_lt μ (volume.restrict (Ioc 0 M)) f] with t ht
  exact congrArg ENNReal.toReal ht

theorem monotone_superlevel_interval {φ : ℝ → ℝ} {a b t : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) (hm : StrictMonoOn φ (Icc a b)) :
    ∃ c ∈ Icc a b, (Ioc a b ∩ {x | t < φ x}) = Ioc c b := by
  by_cases hta : t < φ a
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
    ext x
    constructor
    · exact fun h => h.1
    · intro hx
      refine ⟨hx, ?_⟩
      exact hta.trans_le (hm.monotoneOn ⟨le_rfl, hab⟩ (Ioc_subset_Icc_self hx) hx.1.le)
  by_cases hbt : φ b ≤ t
  · refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
    rw [Ioc_self]
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxt⟩
    have hxφ := hm.monotoneOn (Ioc_subset_Icc_self hx) ⟨hab, le_rfl⟩ hx.2
    exact (not_lt_of_ge (hxφ.trans hbt)) hxt
  obtain ⟨c, hcI, hct⟩ := intermediate_value_Icc hab hc
    (show t ∈ Icc (φ a) (φ b) from ⟨le_of_not_gt hta, (lt_of_not_ge hbt).le⟩)
  refine ⟨c, hcI, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, htx⟩
    change t < φ x at htx
    have hcx : c < x := (hm.lt_iff_lt hcI (Ioc_subset_Icc_self hx)).mp (by simpa only [hct] using htx)
    exact ⟨hcx, hx.2⟩
  · intro hx
    have hax : a < x := hcI.1.trans_lt hx.1
    refine ⟨⟨hax, hx.2⟩, ?_⟩
    change t < φ x
    have hφ := hm hcI ⟨hax.le, hx.2⟩ hx.1
    simpa only [hct] using hφ

theorem monotone_profile_integral_error {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : ℝ → ℝ} {a b M δ : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hc : ContinuousOn φ (Icc a b)) (hm : StrictMonoOn φ (Icc a b))
    (hφ : ∀ x ∈ Icc a b, 0 ≤ φ x ∧ φ x ≤ M)
    (htail : ∀ c ∈ Icc a b, |μ.real (Ioc c b) - ν.real (Ioc c b)| ≤ δ) :
    |(∫ x in Ioc a b, φ x ∂μ) - (∫ x in Ioc a b, φ x ∂ν)| ≤ M * δ := by
  let μ' := μ.restrict (Ioc a b)
  let ν' := ν.restrict (Ioc a b)
  have hfi (ξ : Measure ℝ) [IsFiniteMeasure ξ] : Integrable φ (ξ.restrict (Ioc a b)) :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hfn (ξ : Measure ℝ) : 0 ≤ᵐ[ξ.restrict (Ioc a b)] φ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (hφ x (Ioc_subset_Icc_self hx)).1
  have hfb (ξ : Measure ℝ) : φ ≤ᵐ[ξ.restrict (Ioc a b)] (fun _ => M) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (hφ x (Ioc_subset_Icc_self hx)).2
  have hanti (ξ : Measure ℝ) [IsFiniteMeasure ξ] :
      Antitone (fun t : ℝ => ξ.real {x | t < φ x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans_lt hx)
  have hiμ : IntervalIntegrable (fun t : ℝ => μ'.real {x | t < φ x}) volume 0 M :=
    (hanti μ').intervalIntegrable
  have hiν : IntervalIntegrable (fun t : ℝ => ν'.real {x | t < φ x}) volume 0 M :=
    (hanti ν').intervalIntegrable
  have hlev (t : ℝ) : |μ'.real {x | t < φ x} - ν'.real {x | t < φ x}| ≤ δ := by
    obtain ⟨c, hcI, hset⟩ := monotone_superlevel_interval (t := t) hab hc hm
    have he (ξ : Measure ℝ) : (ξ.restrict (Ioc a b)).real {x | t < φ x} = ξ.real (Ioc c b) := by
      simp only [measureReal_def, Measure.restrict_apply' measurableSet_Ioc, inter_comm,
        hset]
    change |(μ.restrict (Ioc a b)).real {x | t < φ x} -
      (ν.restrict (Ioc a b)).real {x | t < φ x}| ≤ δ
    rw [he μ, he ν]
    exact htail c hcI
  change |(∫ x, φ x ∂μ') - (∫ x, φ x ∂ν')| ≤ M * δ
  rw [integral_eq_bounded_layercake_lt (hfi μ) (hfn μ) (hfb μ),
    integral_eq_bounded_layercake_lt (hfi ν) (hfn ν) (hfb ν),
    ← intervalIntegral.integral_of_le hM, ← intervalIntegral.integral_of_le hM,
    ← intervalIntegral.integral_sub hiμ hiν]
  calc
    _ ≤ ∫ t in 0..M, |μ'.real {x | t < φ x} - ν'.real {x | t < φ x}| :=
      intervalIntegral.abs_integral_le_integral_abs hM
    _ ≤ ∫ _t in (0 : ℝ)..M, δ :=
      intervalIntegral.integral_mono_on hM (hiμ.sub hiν).abs intervalIntegrable_const
        (fun t _ => hlev t)
    _ = _ := by simp

end MatchingEstimate710
end

section
open Set MeasureTheory


namespace MatchingEstimate710

theorem interval_measure_subtract (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    μ.real (Ioc c b) = μ.real (Ioc a b) - μ.real (Ioc a c) := by
  have hs : Ioc a b \ Ioc a c = Ioc c b := by
    ext x
    simp only [mem_sdiff, mem_Ioc]
    constructor
    · rintro ⟨⟨hax, hxb⟩, hn⟩
      exact ⟨lt_of_not_ge (fun hxc => hn ⟨hax, hxc⟩), hxb⟩
    · rintro ⟨hcx, hxb⟩
      exact ⟨⟨hac.trans_lt hcx, hxb⟩, fun h => (not_le_of_gt hcx) h.2⟩
  rw [← hs, measureReal_sdiff (Ioc_subset_Ioc_right hcb) measurableSet_Ioc]

theorem cumulative_error_tail {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b δ : ℝ} (hab : a ≤ b)
    (hcdf : ∀ x ∈ Icc a b, |μ.real (Ioc a x) - ν.real (Ioc a x)| ≤ δ) :
    ∀ c ∈ Icc a b, |μ.real (Ioc c b) - ν.real (Ioc c b)| ≤ 2 * δ := by
  intro c hc
  rw [interval_measure_subtract μ hc.1 hc.2, interval_measure_subtract ν hc.1 hc.2]
  calc
    _ = |(μ.real (Ioc a b) - ν.real (Ioc a b)) -
        (μ.real (Ioc a c) - ν.real (Ioc a c))| := by congr 1; ring
    _ ≤ |μ.real (Ioc a b) - ν.real (Ioc a b)| + |μ.real (Ioc a c) - ν.real (Ioc a c)| := abs_sub _ _
    _ ≤ δ + δ := add_le_add (hcdf b ⟨hab, le_rfl⟩) (hcdf c hc)
    _ = _ := by ring

theorem monotone_profile_cumulative_error {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : ℝ → ℝ} {a b M δ : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hc : ContinuousOn φ (Icc a b)) (hm : StrictMonoOn φ (Icc a b))
    (hφ : ∀ x ∈ Icc a b, 0 ≤ φ x ∧ φ x ≤ M)
    (hcdf : ∀ x ∈ Icc a b, |μ.real (Ioc a x) - ν.real (Ioc a x)| ≤ δ) :
    |(∫ x in Ioc a b, φ x ∂μ) - (∫ x in Ioc a b, φ x ∂ν)| ≤ 2 * M * δ := by
  have hh := monotone_profile_integral_error hab hM hc hm hφ (cumulative_error_tail hab hcdf)
  convert hh using 1
  ring

noncomputable def flatIntervalMeasure (W a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal W • volume.restrict (Ioc a b)

instance flatIntervalMeasure_finite (W a b : ℝ) : IsFiniteMeasure (flatIntervalMeasure W a b) := by
  constructor
  simp [flatIntervalMeasure, Measure.smul_apply]
  exact ENNReal.mul_lt_top (by simp) (by simp)

theorem flatIntervalMeasure_Ioc {W a b c d : ℝ} (hW : 0 ≤ W)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (flatIntervalMeasure W a b).real (Ioc c d) = W * (d - c) := by
  have hs : Ioc c d ⊆ Ioc a b := Ioc_subset_Ioc hac hdb
  simp only [flatIntervalMeasure, measureReal_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hW, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_self_of_subset_left hs, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)]

theorem flatIntervalMeasure_integral {W a b : ℝ} (hW : 0 ≤ W) (φ : ℝ → ℝ) :
    (∫ x in Ioc a b, φ x ∂flatIntervalMeasure W a b) = W * ∫ x in Ioc a b, φ x := by
  simp only [flatIntervalMeasure, Measure.restrict_smul, Measure.restrict_restrict measurableSet_Ioc,
    inter_self, integral_smul_measure, ENNReal.toReal_ofReal hW, smul_eq_mul]

theorem profile_error_from_cumulative {μ : Measure ℝ} [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} {a b M W δ : ℝ} (hab : a ≤ b) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hc : ContinuousOn φ (Icc a b)) (hm : StrictMonoOn φ (Icc a b))
    (hφ : ∀ x ∈ Icc a b, 0 ≤ φ x ∧ φ x ≤ M)
    (hcdf : ∀ x ∈ Icc a b, |μ.real (Ioc a x) - W * (x - a)| ≤ δ) :
    |(∫ x in Ioc a b, φ x ∂μ) - W * (∫ x in a..b, φ x)| ≤ 2 * M * δ := by
  have hcf : ∀ x ∈ Icc a b, |μ.real (Ioc a x) -
      (flatIntervalMeasure W a b).real (Ioc a x)| ≤ δ := by
    intro x hx
    rw [flatIntervalMeasure_Ioc hW le_rfl hx.1 hx.2]
    exact hcdf x hx
  have hh := monotone_profile_cumulative_error hab hM hc hm hφ hcf
  rw [flatIntervalMeasure_integral hW] at hh
  simpa only [intervalIntegral.integral_of_le hab] using hh

end MatchingEstimate710
end

section
open MeasureTheory Set
open scoped BigOperators


namespace MatchingEstimate710

noncomputable def lowerSourceTotal (y : ℝ) (T n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n, lowerSourceWeight y T m

noncomputable def lowerTargetTotal (y : ℝ) (T n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc n T, lowerTargetWeight y T m

theorem source_left_endpoint {y : ℝ} (hy : 0 < y) {T n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    (n : ℝ) * Real.exp (-Real.log ((n : ℝ) * y / T)) = (T : ℝ) / y := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Real.exp_neg, Real.exp_log (div_pos (mul_pos hnR hy) hTR)]
  field_simp

theorem target_right_endpoint {T n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    (n : ℝ) * Real.exp (Real.log ((T : ℝ) / n)) = T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  rw [Real.exp_log (div_pos hTR hnR)]
  field_simp

theorem source_profile_at_log {y : ℝ} (hy : 0 < y) {T n m : ℕ}
    (hT : 0 < T) (hn : 0 < n) (hm : 0 < m) :
    sourceLogProfile (Real.log ((n : ℝ) * y / T)) (Real.log ((m : ℝ) / n)) =
      Phi ((T : ℝ) / (y * m)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  unfold sourceLogProfile
  congr 1
  rw [Real.exp_sub, Real.exp_neg, Real.exp_log (div_pos (mul_pos hnR hy) hTR),
    Real.exp_log (div_pos hmR hnR)]
  field_simp

theorem target_profile_at_log {T n m : ℕ} (hT : 0 < T) (hn : 0 < n) (hm : 0 < m) :
    targetLogProfile (Real.log ((T : ℝ) / n)) (Real.log ((m : ℝ) / n)) = H ((m : ℝ) / T) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  unfold targetLogProfile
  congr 1
  rw [Real.exp_sub, Real.exp_log (div_pos hTR hnR), Real.exp_log (div_pos hmR hnR)]
  field_simp

theorem source_profile_integral_eq_total {y : ℝ} (hy : 0 < y) {T n : ℕ}
    (hn : 0 < n) (hnT : n ≤ T) :
    (∫ v in Ioc (-Real.log ((n : ℝ) * y / T)) 0,
      sourceLogProfile (Real.log ((n : ℝ) * y / T)) v ∂finiteLogMeasure y n T) =
        lowerSourceTotal y T n := by
  classical
  have hT : 0 < T := hn.trans_le hnT
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [finiteLogMeasure_setIntegral _ _ _ _ measurableSet_Ioc]
  have hs : (Finset.Icc 1 T).filter (fun m : ℕ => Real.log ((m : ℝ) / n) ∈
      Ioc (-Real.log ((n : ℝ) * y / T)) 0) =
        (Finset.Icc 1 n).filter (fun m : ℕ => (T : ℝ) / y < m) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm, hlog⟩ := Finset.mem_filter.mp hm
      have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
      have hbounds := (log_ratio_mem_Ioc hnR (show (0 : ℝ) < m by exact_mod_cast hm0)).mp hlog
      rw [source_left_endpoint hy hT hn, Real.exp_zero, mul_one] at hbounds
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, by exact_mod_cast hbounds.2⟩, hbounds.1⟩
    · intro hm
      obtain ⟨hm, hcut⟩ := Finset.mem_filter.mp hm
      have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hnT⟩, ?_⟩
      apply (log_ratio_mem_Ioc hnR (show (0 : ℝ) < m by exact_mod_cast hm0)).mpr
      rw [source_left_endpoint hy hT hn, Real.exp_zero, mul_one]
      exact ⟨hcut, by exact_mod_cast (Finset.mem_Icc.mp hm).2⟩
  trans ∑ m ∈ (Finset.Icc 1 n).filter (fun m : ℕ => (T : ℝ) / y < m),
    rho y m * sourceLogProfile (Real.log ((n : ℝ) * y / T)) (Real.log ((m : ℝ) / n))
  · apply Finset.sum_congr
    · apply Finset.ext
      intro m
      have hh := Finset.ext_iff.mp hs m
      simpa only [Finset.mem_filter] using hh
    · intro m _
      rfl
  rw [Finset.sum_filter]
  unfold lowerSourceTotal
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
  rw [source_profile_at_log hy hT hn hm0]
  rfl

theorem target_profile_integral_eq_total {y : ℝ} {T n : ℕ}
    (hn : 0 < n) (hnT : n ≤ T) :
    (∫ v in Ioc 0 (Real.log ((T : ℝ) / n)), targetLogProfile (Real.log ((T : ℝ) / n)) v
      ∂finiteLogMeasure y n T) = lowerTargetTotal y T n := by
  classical
  have hT : 0 < T := hn.trans_le hnT
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [finiteLogMeasure_setIntegral _ _ _ _ measurableSet_Ioc]
  have hs : (Finset.Icc 1 T).filter (fun m : ℕ => Real.log ((m : ℝ) / n) ∈
      Ioc 0 (Real.log ((T : ℝ) / n))) = Finset.Ioc n T := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm, hlog⟩ := Finset.mem_filter.mp hm
      have hm0 : 0 < m := by have := (Finset.mem_Icc.mp hm).1; omega
      have hbounds := (log_ratio_mem_Ioc hnR (show (0 : ℝ) < m by exact_mod_cast hm0)).mp hlog
      rw [Real.exp_zero, mul_one, target_right_endpoint hT hn] at hbounds
      exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hbounds.1, by exact_mod_cast hbounds.2⟩
    · intro hm
      have hbounds := Finset.mem_Ioc.mp hm
      have hm0 : 0 < m := hn.trans hbounds.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, hbounds.2⟩, ?_⟩
      apply (log_ratio_mem_Ioc hnR (show (0 : ℝ) < m by exact_mod_cast hm0)).mpr
      rw [Real.exp_zero, mul_one, target_right_endpoint hT hn]
      exact ⟨by exact_mod_cast hbounds.1, by exact_mod_cast hbounds.2⟩
  trans ∑ m ∈ Finset.Ioc n T,
    rho y m * targetLogProfile (Real.log ((T : ℝ) / n)) (Real.log ((m : ℝ) / n))
  · apply Finset.sum_congr
    · apply Finset.ext
      intro m
      have hh := Finset.ext_iff.mp hs m
      simpa only [Finset.mem_filter] using hh
    · intro m _
      rfl
  unfold lowerTargetTotal
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : 0 < m := hn.trans (Finset.mem_Ioc.mp hm).1
  rw [target_profile_at_log hT hn hm0]
  rfl

end MatchingEstimate710
end

section
open MeasureTheory Set


namespace MatchingEstimate710

theorem profile_comparison_bounds {y W δ : ℝ} (hy : 0 < y) (hW : 0 < W)
    {n T : ℕ} (hn : 0 < n) (hnT : n ≤ T)
    (hb : 0 ≤ Real.log ((n : ℝ) * y / T))
    (hcount : ∀ v ∈ Icc (-Real.log ((n : ℝ) * y / T)) (Real.log ((T : ℝ) / n)),
      |weightedSum y ((n : ℝ) * Real.exp v) - weightedSum y n - W * v| ≤ δ * W) :
    W * (Real.log ((n : ℝ) * y / T) - 3 / 2) - 4 * δ * W ≤ lowerSourceTotal y T n ∧
      lowerTargetTotal y T n ≤ W * (Real.log ((T : ℝ) / n) + 1 / 2) + 4 * δ * W := by
  let a := Real.log ((T : ℝ) / n)
  let b := Real.log ((n : ℝ) * y / T)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : 0 < T := hn.trans_le hnT
  have ha : 0 ≤ a := by
    apply Real.log_nonneg
    exact (one_le_div hnR).mpr (by exact_mod_cast hnT)
  have hb0 : 0 ≤ b := hb
  have hab : -b ≤ a := by linarith
  let E := fun v : ℝ => weightedSum y ((n : ℝ) * Real.exp v) - weightedSum y n - W * v
  have hE : ∀ v ∈ Icc (-b) a, |E v| ≤ δ * W := hcount
  have hscdf : ∀ x ∈ Icc (-b) 0,
      |(finiteLogMeasure y n T).real (Ioc (-b) x) - W * (x - -b)| ≤ 2 * δ * W := by
    intro x hx
    have hNx : (n : ℝ) * Real.exp x ≤ T := by
      have hh : (n : ℝ) * Real.exp x ≤ n := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hx.2) hnR.le
      exact hh.trans (by exact_mod_cast hnT)
    rw [finiteLogMeasure_Ioc y hn hx.1 hNx]
    have heq : weightedSum y ((n : ℝ) * Real.exp x) - weightedSum y ((n : ℝ) * Real.exp (-b)) -
        W * (x - -b) = E x - E (-b) := by dsimp [E]; ring
    rw [heq]
    have h₁ := hE x ⟨hx.1, hx.2.trans ha⟩
    have h₂ := hE (-b) ⟨le_rfl, hab⟩
    exact (abs_sub _ _).trans (by linarith)
  have htcdf : ∀ x ∈ Icc 0 a,
      |(finiteLogMeasure y n T).real (Ioc 0 x) - W * (x - 0)| ≤ δ * W := by
    intro x hx
    have hNx : (n : ℝ) * Real.exp x ≤ T := by
      have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.2) hnR.le
      exact hh.trans_eq (target_right_endpoint hT hn)
    rw [finiteLogMeasure_Ioc y hn hx.1 hNx]
    simpa only [Real.exp_zero, mul_one, sub_zero] using hE x ⟨by linarith [hx.1], hx.2⟩
  have hs := profile_error_from_cumulative (by linarith : -b ≤ (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) hW.le (sourceLogProfile_continuousOn b)
    (sourceLogProfile_strictMonoOn b) (fun _ hx => sourceLogProfile_bounds hx) hscdf
  have ht := profile_error_from_cumulative ha (by norm_num : (0 : ℝ) ≤ 2) hW.le
    (targetLogProfile_continuousOn a) (targetLogProfile_strictMonoOn a)
    (fun _ hx => targetLogProfile_bounds hx) htcdf
  change |(∫ v in Ioc (-Real.log ((n : ℝ) * y / T)) 0,
      sourceLogProfile (Real.log ((n : ℝ) * y / T)) v ∂finiteLogMeasure y n T) -
      W * ∫ v in (-b)..0, sourceLogProfile b v| ≤ 2 * 1 * (2 * δ * W) at hs
  rw [source_profile_integral_eq_total hy hn hnT] at hs
  change |(∫ v in Ioc 0 (Real.log ((T : ℝ) / n)),
      targetLogProfile (Real.log ((T : ℝ) / n)) v ∂finiteLogMeasure y n T) -
      W * ∫ v in 0..a, targetLogProfile a v| ≤ 2 * 2 * (δ * W) at ht
  rw [target_profile_integral_eq_total hn hnT] at ht
  have hsource : b - 3 / 2 ≤ ∫ v in (-b)..0, sourceLogProfile b v := by
    rw [sourceLogProfile_integral hb0]
    have hp := (leftParameter_spec (exp_neg_mem_unit hb0)).1.1
    nlinarith [sq_nonneg (leftParameter (Real.exp (-b)))]
  have htarget : (∫ v in 0..a, targetLogProfile a v) ≤ a + 1 / 2 := by
    rw [targetLogProfile_integral ha]
    have hp := (rightParameter_spec (exp_neg_mem_unit ha)).1
    nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]
  constructor
  · have hh := (abs_le.mp hs).1
    have hmul := mul_le_mul_of_nonneg_left hsource hW.le
    dsimp [b] at *
    linarith
  · have hh := (abs_le.mp ht).2
    have hmul := mul_le_mul_of_nonneg_left htarget hW.le
    dsimp [a] at *
    linarith

theorem source_total_gt_target_of_uniform_counts {y W δ : ℝ}
    (hy : 0 < y) (hW : 0 < W) {n T : ℕ} (hn : 0 < n) (hnT : n ≤ T)
    (hb : 0 ≤ Real.log ((n : ℝ) * y / T))
    (hgap : 2 + 8 * δ < Real.log ((n : ℝ) * y / T) - Real.log ((T : ℝ) / n))
    (hcount : ∀ v ∈ Icc (-Real.log ((n : ℝ) * y / T)) (Real.log ((T : ℝ) / n)),
      |weightedSum y ((n : ℝ) * Real.exp v) - weightedSum y n - W * v| ≤ δ * W) :
    lowerTargetTotal y T n < lowerSourceTotal y T n := by
  have hbds := profile_comparison_bounds hy hW hn hnT hb hcount
  have hh := mul_pos (sub_pos.mpr hgap) hW
  nlinarith [hbds.1, hbds.2]

end MatchingEstimate710
end

section
open Filter Set
open scoped Topology BigOperators


namespace MatchingEstimate710

theorem sum_fin_successors (g : ℕ → ℝ) (n : ℕ) :
    (∑ i : Fin n, g (i.val + 1)) = ∑ m ∈ Finset.Icc 1 n, g m := by
  calc
    _ = ∑ k ∈ Finset.range n, g (k + 1) := Fin.sum_univ_eq_sum_range (fun k => g (k + 1)) n
    _ = _ := by
      have hh := Finset.sum_Ico_eq_sum_range g 1 (n + 1)
      simpa only [Finset.Ico_add_one_right_eq_Icc, Nat.add_sub_cancel, Nat.add_comm] using hh.symm

theorem length_lt_f_of_total_gap {y : ℝ} (hy : 0 < y) {n T : ℕ} (hnT : n ≤ T)
    (hgap : lowerTargetTotal y T n < lowerSourceTotal y T n) : T - n + 1 < f n := by
  apply f_gt_of_lower_weight_gap n (T - n + 1) hy
  have he : n + (T - n + 1) - 1 = T := by omega
  have hi : Finset.Ioo n (n + (T - n + 1)) = Finset.Ioc n T := by
    ext m
    simp only [Finset.mem_Ioo, Finset.mem_Ioc]
    omega
  rw [he, hi, sum_fin_successors]
  exact hgap

theorem exists_lower_parameters {κ : ℝ} (hκ : 0 < κ) (hk : κ < sharpConstant) :
    ∃ β θ δ : ℝ, 0 < β ∧ β / 2 < θ ∧ θ < 1 ∧ 0 < δ ∧
      2 + 8 * δ < Real.log (β / κ ^ 2) := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hks : κ * Real.exp 1 < Real.sqrt 2 := by
    exact (lt_div_iff₀ he).mp hk
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hD : κ ^ 2 * (Real.exp 1) ^ 2 < 2 := by
    nlinarith [mul_pos hκ he, Real.sqrt_nonneg (2 : ℝ)]
  let β := (κ ^ 2 * (Real.exp 1) ^ 2 + 2) / 2
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβ2 : β < 2 := by dsimp [β]; linarith
  have hβD : κ ^ 2 * (Real.exp 1) ^ 2 < β := by dsimp [β]; linarith
  have hratio : Real.exp 2 < β / κ ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hκ)).mpr
    have hh : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [hh]
    nlinarith [hβD]
  have hK : 2 < Real.log (β / κ ^ 2) := by
    rw [← Real.exp_lt_exp, Real.exp_log (div_pos hβ0 (sq_pos_of_pos hκ))]
    exact hratio
  refine ⟨β, (β / 2 + 1) / 2, (Real.log (β / κ ^ 2) - 2) / 16,
    hβ0, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem endpointLength_lt_f {κ : ℝ} (hκ : 0 < κ) (hk : κ < sharpConstant) :
    ∀ᶠ n : ℕ in atTop, endpointLength κ n < f n := by
  obtain ⟨β, θ, δ, hβ, hθlo, hθhi, hδ, hδK⟩ := exists_lower_parameters hκ hk
  have hW := log_nat_tendsto_atTop.eventually (arithmeticMainWeight_bounds hβ hθlo hθhi)
  have hc := weightedSum_uniform_integer_error hβ hθlo hθhi (show (0 : ℝ) ≤ 1 by norm_num) hδ
  have hg := (window_difference_tendsto hβ hκ).eventually (eventually_gt_nhds hδK)
  have hwindows := endpoint_window_bounds hβ hκ
  have hTn := (lowerEndpoint_div_nat_tendsto hκ).eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hW, hc, hg, hwindows, hTn, eventually_ge_atTop (2 : ℕ)]
    with n hWn hcn hgn hwin hTnn hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnT : n ≤ lowerEndpoint κ n := by exact_mod_cast (one_le_div hnR).mp hTnn
  have hy : 0 < β * Real.log n :=
    mul_pos hβ (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hcount : ∀ v ∈ Icc (-lowerWindow β κ n) (upperWindow κ n),
      |weightedSum (β * Real.log n) ((n : ℝ) * Real.exp v) - weightedSum (β * Real.log n) n -
        arithmeticMainWeight β θ (Real.log n) * v| ≤ δ * arithmeticMainWeight β θ (Real.log n) := by
    intro v hv
    have hav : |v| ≤ Real.log (Real.log n) := by
      apply abs_le.mpr
      constructor <;> linarith [hv.1, hv.2, hwin.1.2, hwin.2.2]
    simpa only [one_mul, mul_comm] using hcn v (by simpa only [one_mul] using hav)
  have hgap := source_total_gt_target_of_uniform_counts hy hWn.1 hn0 hnT hwin.2.1 hgn hcount
  exact length_lt_f_of_total_gap hy hnT hgap


theorem lowerEstimate : LowerEstimate := by
  intro c hc
  by_cases hc0 : c ≤ 0
  · apply Filter.Eventually.of_forall
    intro n
    have hs : 0 ≤ scale n := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    exact (mul_nonpos_of_nonpos_of_nonneg hc0 hs).trans (Nat.cast_nonneg _)
  have hcpos : 0 < c := lt_of_not_ge hc0
  let κ := (c + sharpConstant) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith [sharpConstant_pos]
  have hk : κ < sharpConstant := by dsimp [κ]; linarith
  have hck : c < κ := by dsimp [κ]; linarith
  have hratio := (endpointLength_ratio_tendsto hκ).eventually (eventually_gt_nhds hck)
  filter_upwards [hratio, endpointLength_lt_f hκ hk, eventually_scale_pos] with n hr hn hs
  have hh : c * scale n < (endpointLength κ n : ℝ) := (lt_div_iff₀ hs).mp hr
  have hf : (endpointLength κ n : ℝ) < f n := by exact_mod_cast hn
  exact (hh.trans hf).le

end MatchingEstimate710
end

section
namespace MatchingEstimate710
namespace SourceStatement

def HasDivisibleDistinctTuple (n m L : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, Function.Injective a ∧
    ∀ i : Fin n, m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

noncomputable def f (n : ℕ) : ℕ :=
  sInf {L : ℕ | HasDivisibleDistinctTuple n n L}

end SourceStatement

theorem matching_iff_source (n h : ℕ) :
    HasMatching n h ↔ SourceStatement.HasDivisibleDistinctTuple n n h := Iff.rfl

theorem minimum_eq_source (n : ℕ) : f n = SourceStatement.f n := by
  apply le_antisymm
  · apply f_le
    exact csInf_mem (matching_exists n)
  · exact Nat.sInf_le (f_spec n)


def SourceAsymptoticFormula : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun n : ℕ => (SourceStatement.f n : ℝ))
    (fun n => Real.sqrt 2 / Real.exp 1 * (n : ℝ) * Real.sqrt (Real.log (n : ℝ)))

theorem asymptotic_iff_source : AsymptoticFormula ↔ SourceAsymptoticFormula := by
  simp only [AsymptoticFormula, SourceAsymptoticFormula, ← minimum_eq_source,
    sharpConstant, scale, mul_assoc]

end MatchingEstimate710
end

open Filter
open scoped Topology

theorem OMA.solution : type_of% @Erdos710.erdos_710.variants.lower_bound := by
  intro ε hε
  let A : ℝ := 2 / Real.sqrt (Real.exp 1)
  let c : ℝ := MatchingEstimate710.sharpConstant / 2
  have hc : 0 < c := half_pos MatchingEstimate710.sharpConstant_pos
  have hlt : c < MatchingEstimate710.sharpConstant := half_lt_self MatchingEstimate710.sharpConstant_pos
  have hlog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [MatchingEstimate710.lowerEstimate c hlt, eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (max 1 ((A / c) ^ 2))] with n hbound hn hl
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hd : 0 < Real.log (Real.log n) := lt_of_lt_of_le zero_lt_one
    ((le_max_left _ _).trans hl)
  have hsq : (A / c) ^ 2 ≤ Real.log (Real.log n) := (le_max_right _ _).trans hl
  have hA : A ≤ c * Real.sqrt (Real.log (Real.log n)) := by
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by dsimp [A]; positivity)] at h
    simpa [mul_comm] using (div_le_iff₀ hc).mp h
  have hcomparison : (A - ε) / Real.sqrt (Real.log (Real.log n)) ≤ c :=
    (div_le_iff₀ (Real.sqrt_pos.2 hd)).2 (by linarith)
  have hs : 0 ≤ (n : ℝ) * Real.sqrt (Real.log n) := by positivity
  have hef : MatchingEstimate710.f n = Erdos710.f n := MatchingEstimate710.minimum_eq_source n
  rw [hef] at hbound
  calc
    _ = ((A - ε) / Real.sqrt (Real.log (Real.log n))) * MatchingEstimate710.scale n := by
      rw [Real.sqrt_div hln]
      unfold MatchingEstimate710.scale
      change (A - ε) * (n : ℝ) * (Real.sqrt (Real.log n) /
        Real.sqrt (Real.log (Real.log n))) = _
      ring
    _ ≤ c * MatchingEstimate710.scale n := mul_le_mul_of_nonneg_right hcomparison hs
    _ ≤ _ := hbound

