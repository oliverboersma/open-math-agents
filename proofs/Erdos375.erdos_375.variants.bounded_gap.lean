import FormalConjectures.ErdosProblems.«375»
import Mathlib

/-!
Proof of the bounded-gap consequence of Grimm's conjecture.
Prepared for submission by @stevenczp with Codex.

The three previously merged reductions are reproduced with their original
credits. Their pull requests identify the authors and original commits:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2978
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5802
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6294

The two previously merged auxiliary proofs are included as separately
named lemmas. References to all reused sources follow.
- src/OMAReductions/R_Erdos375_erdos_375_variants_bounded_gap_R1.lean — https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/reductions/Erdos375.erdos_375.variants.bounded_gap.R1.lean
- src/OMAReductions/R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1.lean — https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/reductions/Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.lean
- src/OMAReductions/R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.lean — https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/reductions/Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.H2.R1.lean
- src/PrimeDensity.lean — https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/proofs/Erdos375.erdos_375.variants.bounded_gap.R1.H2.lean
- src/Reciprocal.lean — https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/proofs/Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.H1.lean
- src/Salt/ExpSum/Kusmin.lean — https://github.com/jyh/salt/blob/main/Salt/ExpSum/Kusmin.lean
- src/Salt/ExpSum/VdCorput2.lean — https://github.com/jyh/salt/blob/main/Salt/ExpSum/VdCorput2.lean

SALT: Copyright (c) 2026 Jason Hickey. Original file headers are preserved.
Changes for this single-file submission: the two Exponential Sum modules
are embedded in scoped sections; standalone imports are consolidated,
and module documentation is preserved as ordinary comments.
The following license applies to the included SALT code.

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
/- 用周期二次 Bernoulli 多项式的差分在跳点两侧控制锯齿函数。 -/

namespace Erdos375Envelope

noncomputable def B (x : ℝ) : ℝ := bernoulliFun 2 (Int.fract x)

/-- 差分窗口最多穿过一个整数。跳过整数时，前向斜率降低、后向斜率升高。 -/
theorem sandwich (x d : ℝ) (hd : 0 < d) (hd' : d ≤ 1) :
    (B (x+d) - B x)/(2*d) - d/2 ≤ Int.fract x - 1/2 ∧
    Int.fract x - 1/2 ≤ (B x - B (x-d))/(2*d) + d/2 := by
  let r := Int.fract x
  have hr : 0 ≤ r := Int.fract_nonneg _
  have hr' : r < 1 := Int.fract_lt_one _
  have shift (s : ℝ) : Int.fract (x+s) = Int.fract (r+s) := by
    conv_lhs => rw [← Int.fract_add_floor x]
    rw [add_right_comm, Int.fract_add_intCast]
  have hplus := shift d
  have hminus : Int.fract (x-d) = Int.fract (r-d) := by simpa [sub_eq_add_neg] using shift (-d)
  simp only [B, bernoulliFun_two, hplus, hminus]
  change _ - _ ≤ r - 1/2 ∧ r - 1/2 ≤ _ + _
  constructor
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    by_cases h : r+d < 1
    · rw [Int.fract_eq_self.mpr ⟨by linarith, h⟩]
      dsimp [r] at *
      nlinarith
    · rw [← Int.fract_sub_one (r+d), Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      dsimp [r] at *
      nlinarith
  · rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity)]
    by_cases h : 0 ≤ r-d
    · rw [Int.fract_eq_self.mpr ⟨h, by linarith⟩]
      dsimp [r] at *
      nlinarith
    · rw [← Int.fract_add_one (r-d), (Int.fract_eq_self (a := r-d+1)).mpr ⟨by linarith, by linarith⟩]
      dsimp [r] at *
      nlinarith

end Erdos375Envelope
end

section
/- Erdős 375 的锯齿误差：将逐点三角多项式上界转化为区间和的上界。 -/

open Finset

namespace Erdos375Fourier

/-- 此处锯齿在整数上取 1/2，整数商的端点也包含在内。 -/
theorem centered_quotient (t d : ℕ) :
    ((t / d : ℕ) : ℝ) - (t : ℝ) / d + 1/2 =
      1/2 - Int.fract ((t : ℝ) / d) := by
  rw [Int.fract, Int.floor_div_natCast, Int.floor_natCast, ← Int.natCast_ediv]
  rw [Int.cast_natCast]
  ring

/-- 频率从 1 开始编号。上界的常数项和每个非零频率分别求和。 -/
theorem sum_le_of_majorant {ι : Type*} (s : Finset ι) {H : ℕ}
    (v : ι → ℝ) (z : Fin H → ι → ℂ) (c : Fin H → ℂ) (η B : ℝ)
    (hc : ∀ h, ‖c h‖ ≤ 1) (hz : ∀ h, ‖∑ i ∈ s, z h i‖ ≤ B)
    (hv : ∀ i ∈ s, v i ≤ η + ∑ h, (c h * z h i).re) :
    ∑ i ∈ s, v i ≤ s.card * η + H * B := by
  have hfreq (h : Fin H) : ∑ i ∈ s, (c h * z h i).re ≤ B := by
    rw [← Complex.re_sum, ← Finset.mul_sum]
    calc
      _ ≤ ‖c h * ∑ i ∈ s, z h i‖ := Complex.re_le_norm _
      _ = _ := norm_mul _ _
      _ ≤ 1 * ‖∑ i ∈ s, z h i‖ := mul_le_mul_of_nonneg_right (hc h) (norm_nonneg _)
      _ ≤ B := by simpa using hz h
  calc
    _ ≤ ∑ i ∈ s, (η + ∑ h, (c h * z h i).re) := sum_le_sum hv
    _ = s.card * η + ∑ h, ∑ i ∈ s, (c h * z h i).re := by
      rw [sum_add_distrib, sum_comm (s := s) (t := univ)]
      simp
    _ ≤ _ := by
      gcongr
      simpa using (sum_le_sum (fun h (_ : h ∈ (univ : Finset (Fin H))) => hfreq h))

/-- 取截断阶数 N^12。即使舍去傅里叶系数的衰减，仍留有两个幂次余量。 -/
theorem truncation_budget {N K : ℕ} (hN : 2 ≤ N) (hK : K ≤ N^504) :
    (K : ℝ) * (1/(N:ℝ)^12) + (N:ℝ)^12 * (10*(N:ℝ)^484)
      ≤ 1000*(N:ℝ)^498 := by
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpos : (0 : ℝ) < N := by linarith
  have h₁ : (K : ℝ) * (1/(N:ℝ)^12) ≤ (N:ℝ)^492 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    rw [← pow_add]
    exact_mod_cast hK
  have h₂ : (N:ℝ)^12 * (10*(N:ℝ)^484) = 10*(N:ℝ)^496 := by
    rw [mul_left_comm, ← pow_add]
  have h₃ := pow_le_pow_right₀ hone (show 492 ≤ 498 by decide)
  have h₄ := pow_le_pow_right₀ hone (show 496 ≤ 498 by decide)
  linarith [show 0 ≤ (N:ℝ)^498 by positivity]

/-- 原始 H3 的有限样本形式。剩余条件是一个与素数无关的三角多项式逼近。 -/
theorem centered_sum_of_polynomials {ι : Type*} (S : Finset ι) (t : ℕ) (d : ι → ℕ)
    {N : ℕ} (hN : 2 ≤ N) (hS : S.card ≤ N^504)
    (wave : ℕ → ℝ → ℂ)
    (hmoment : ∀ h, 1 ≤ h → h ≤ N^20 →
      ‖∑ i ∈ S, wave h ((t : ℝ) / d i)‖ ≤ 10*(N:ℝ)^484)
    (hpoly : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∃ c : Fin (N^12) → ℂ, (∀ h, ‖c h‖ ≤ 1) ∧ ∀ x : ℝ,
        σ * (1/2 - Int.fract x) ≤ 1/(N:ℝ)^12 +
          ∑ h, (c h * wave (h.val+1) x).re) :
    |∑ i ∈ S, (((t / d i : ℕ) : ℝ) - (t:ℝ) / d i + 1/2)| ≤ 1000*(N:ℝ)^498 := by
  let v := fun i => ((t / d i : ℕ) : ℝ) - (t:ℝ) / d i + 1/2
  have hsign (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) : σ * ∑ i ∈ S, v i ≤ 1000*(N:ℝ)^498 := by
    obtain ⟨c, hc, hpoint⟩ := hpoly σ hσ
    have hcut : N^12 ≤ N^20 := Nat.pow_le_pow_right (by omega) (by decide)
    rw [Finset.mul_sum]
    apply le_trans (sum_le_of_majorant S (fun i => σ * v i)
      (fun h i => wave (h.val+1) ((t:ℝ) / d i)) c _ _ hc
      (fun h => hmoment _ (by omega) (le_trans h.isLt hcut)) ?_)
    · simpa using truncation_budget hN hS
    · intro i _
      dsimp only [v]
      rw [centered_quotient]
      simpa only [one_div] using hpoint ((t:ℝ) / d i)
  change |∑ i ∈ S, v i| ≤ _
  exact abs_le.mpr ⟨by linarith [hsign (-1) (Or.inr rfl)], by simpa using hsign 1 (Or.inl rfl)⟩

/-- 对所有样本作同一平移，只会给指数和乘上一个模长为一的复数。 -/
private theorem shifted_cos_le {ι : Type*} (S : Finset ι) (x : ι → ℝ) (s ω : ℝ) :
    |∑ i ∈ S, Real.cos (ω*(x i+s))| ≤
    ‖∑ i ∈ S, Complex.exp ((ω*x i : ℝ) * Complex.I)‖ := by
  simp_rw [← Complex.exp_ofReal_mul_I_re, mul_add, Complex.ofReal_add, add_mul,
    Complex.exp_add]
  rw [← Complex.re_sum, ← Finset.sum_mul]
  simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
    Complex.abs_re_le_norm ((∑ i ∈ S, Complex.exp (↑(ω*x i) * Complex.I)) *
      Complex.exp (↑(ω*s) * Complex.I))

/-- 逐项的 1/n² 权重可求和，界与截断的频率个数无关。 -/
theorem shifted_bernoulli_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ) (shift : ℝ)
    (H : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ h : ℕ, 1 ≤ h → h ≤ H →
      ‖∑ i ∈ S, Complex.exp (((2*Real.pi*h*x i : ℝ) : ℂ) * Complex.I)‖ ≤ M)
    (htr : ∀ w : ℝ, |Real.pi^2*(Int.fract w ^ 2 - Int.fract w + 1/6) -
      ∑ n ∈ range (H+1), (1 / (n:ℝ)^2) * Real.cos (2*Real.pi*n*w)| ≤ 1/(H:ℝ)) :
    |∑ i ∈ S, Real.pi^2*(Int.fract (x i+shift)^2 - Int.fract (x i+shift) + 1/6)| ≤
      S.card/(H:ℝ) + 2*M := by
  let b := fun i => Real.pi^2*(Int.fract (x i+shift)^2 - Int.fract (x i+shift) + 1/6)
  let term := fun (n : ℕ) i => 1/(n:ℝ)^2 * Real.cos (2*Real.pi*n*(x i+shift))
  let F := fun i => ∑ n ∈ range (H+1), term n i
  have hE : |∑ i ∈ S, (b i - F i)| ≤ S.card/(H:ℝ) := calc
    _ ≤ ∑ i ∈ S, |b i-F i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, 1/(H:ℝ) := sum_le_sum fun i _ => htr _
    _ = _ := by simp [div_eq_mul_inv]
  have hcoef : (∑ n ∈ range (H+1), 1/(n:ℝ)^2) ≤ 2 := by
    have hs := hasSum_zeta_two.summable.sum_le_tsum (range (H+1))
      (fun (n : ℕ) _ => by positivity)
    rw [hasSum_zeta_two.tsum_eq] at hs
    exact hs.trans (by nlinarith [Real.pi_lt_d2, Real.pi_pos])
  have hfreq (n : ℕ) (hn : n ∈ range (H+1)) : |∑ i ∈ S, term n i| ≤ (1/(n:ℝ)^2) * M := by
    by_cases hn0 : n = 0
    · simp [hn0, term]
    simp only [term, ← mul_sum, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1/(n:ℝ)^2)]
    exact mul_le_mul_of_nonneg_left ((shifted_cos_le S x shift (2*Real.pi*n)).trans
      (hm n (by omega) (by have := mem_range.mp hn; omega))) (by positivity)
  have hF : |∑ i ∈ S, F i| ≤ 2*M := by
    dsimp only [F]
    rw [sum_comm]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((sum_le_sum hfreq).trans
      (by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hcoef hM))
  change |∑ i ∈ S, b i| ≤ _
  have hsplit : (∑ i ∈ S, b i) = (∑ i ∈ S, (b i - F i)) + ∑ i ∈ S, F i := by
    rw [Finset.sum_sub_distrib, sub_add_cancel]
  rw [hsplit]
  exact (abs_add_le ..).trans (add_le_add hE hF)

end Erdos375Fourier
end

section
open Filter Finset

namespace Erdos375Bernoulli

private theorem series (x : ℝ) :
    HasSum (fun n : ℕ => (1/(n:ℝ)^2) * Real.cos (2*Real.pi*n*x))
      (Real.pi^2 * (Int.fract x ^ 2 - Int.fract x + 1/6)) := by
  have hs := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide)
    (x := Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hcos (n : ℕ) : Real.cos (2*Real.pi*n*Int.fract x) = Real.cos (2*Real.pi*n*x) := by
    rw [Int.fract]
    convert Real.cos_sub_int_mul_two_pi (2*Real.pi*n*x) ((n:ℤ)*⌊x⌋) using 2 <;> push_cast <;> ring
  simp only [show 2*1 = 2 by decide, hcos] at hs
  convert hs using 1
  change _ = _ * bernoulliFun 2 (Int.fract x)
  rw [bernoulliFun_two]
  norm_num [Nat.factorial] <;> ring_nf <;> simp

/-- 在正整数频率 H 截断二次 Bernoulli 多项式的傅里叶级数。 -/
theorem truncation (x : ℝ) (H : ℕ) (hH : 0 < H) :
    |Real.pi^2*(Int.fract x ^ 2 - Int.fract x + 1/6) -
      ∑ n ∈ range (H+1), (1 / (n:ℝ)^2) * Real.cos (2*Real.pi*n*x)| ≤ 1/(H:ℝ) := by
  let f (n : ℕ) := (1/(n:ℝ)^2) * Real.cos (2*Real.pi*n*x)
  have term (n : ℕ) (hn : H ≤ n) : |f (n+1)| ≤ 1/(n:ℝ) - 1/((n:ℝ)+1) := by
    have hp : (0:ℝ) < n := by exact_mod_cast hH.trans_le hn
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1/((n+1:ℕ):ℝ)^2)]
    push_cast
    calc
      _ ≤ (1/((n:ℝ)+1)^2)*1 := by gcongr; exact Real.abs_cos_le_one _
      _ ≤ _ := by
        field_simp
        nlinarith
  have tail : ∀ n ≥ H,
      |(∑ j ∈ range (n+1), f j) - ∑ j ∈ range (H+1), f j| ≤ 1/(H:ℝ) - 1/(n:ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [sum_range_succ]
      calc
        _ = |((∑ j ∈ range (n+1), f j) - ∑ j ∈ range (H+1), f j) + f (n+1)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := by push_cast; linarith [term n hn]
  have ht := ((series x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub_const
    (∑ j ∈ range (H+1), f j)
  apply le_of_tendsto (continuous_abs.continuousAt.tendsto.comp ht)
  filter_upwards [eventually_ge_atTop H] with n hn
  exact (tail n hn).trans (sub_le_self _ (by positivity))

end Erdos375Bernoulli
end

section
-- Credit: @marcusbuffett
/-
Following Laishram and Murty, *Grimm's conjecture and smooth numbers*,
Michigan Math. J. 61 (2012), Lemmas 2.3–2.4. A long prime-free interval would
assign distinct small primes to more smooth numbers than there are such primes.
-/
namespace OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1

open Filter Finset

/-- The Friedlander–Lagarias short-interval smooth-number lower bound
in the form of Laishram–Murty, Lemma 2.3. -/
def H1 : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
    let k := ⌊(x : ℝ) ^ a⌋₊
    c * k ≤ (((univ : Finset (Fin k)).filter
      (fun i : Fin k => x + (i : ℕ) + 1 ∈ Nat.smoothNumbers (k + 1))).card : ℝ)

/-- The primes have relative density zero among the natural numbers. -/
def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ᶠ k : ℕ in atTop,
  ((k + 1).primesBelow.card : ℝ) < c * k

theorem main : H1 → H2 → type_of% @Erdos375.erdos_375.variants.bounded_gap := by
  classical
  rintro ⟨a, ha, ha', c, hc, hSmooth⟩ hPrimes hGrimm
  let p := Nat.nth Nat.Prime
  have hpTop : Tendsto p atTop atTop :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  let k (x : ℕ) := ⌊(x : ℝ) ^ a⌋₊
  have hkTop : Tendsto k atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSmooth
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hPrimes c hc)
  refine ⟨(1 / 2 - a) / 2, by linarith, ?_⟩
  filter_upwards [hpTop.eventually_ge_atTop N, (hkTop.comp hpTop).eventually_ge_atTop M] with n hn hm
  have hp : 1 < p n := by have := Nat.add_two_le_nth_prime n; dsimp [p]; omega
  have hg : p (n + 1) ≤ p n + k (p n) := by
    by_contra! hgap
    have hcomp : ∀ i < k (p n), ¬(p n + i + 1).Prime := by
      intro i hi hiPrime
      have hlt : p n + i + 1 < p (n + 1) := by omega
      have := Nat.le_nth_of_lt_nth_succ hlt hiPrime
      change p n + i + 1 ≤ p n at this
      omega
    obtain ⟨q, hq, hd⟩ := hGrimm (p n) hp.le (k (p n)) hcomp
    let S := (univ : Finset (Fin (k (p n)))).filter
      (fun i : Fin (k (p n)) => p n + (i : ℕ) + 1 ∈ Nat.smoothNumbers (k (p n) + 1))
    have hsub : S.image q ⊆ (k (p n) + 1).primesBelow := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      have hs := (mem_filter.mp hi).2
      exact Nat.mem_primesBelow.mpr ⟨Nat.mem_smoothNumbers'.mp hs _ (hd i).1 (hd i).2, (hd i).1⟩
    have hcard := card_le_card hsub
    rw [card_image_of_injective _ hq] at hcard
    have hcardR : (S.card : ℝ) ≤ ((k (p n) + 1).primesBelow.card : ℝ) := by exact_mod_cast hcard
    have hlow : c * k (p n) ≤ (S.card : ℝ) := hN _ hn
    exact (hM _ hm).not_ge (hlow.trans hcardR)
  change (p (n + 1) : ℝ) - p n < (p n : ℝ) ^ _
  have hgR : (p (n+1) : ℝ) ≤ (p n : ℝ) + k (p n) := by exact_mod_cast hg
  calc (p (n+1) : ℝ) - p n ≤ k (p n) := by linarith
    _ ≤ (p n : ℝ) ^ a := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hp) (by linarith)

end OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1
end

section
/- Count two prime divisors just above the fourth root of x. Their cofactor
is short, four distinct divisors are already too large, and summing the two
endpoint floor errors reduces the short interval count to a bilinear estimate.
Credit: @marcusbuffett. -/

namespace OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1

open Finset Filter
open scoped BigOperators

private lemma count_div (x k d : ℕ) :
    ((Ioc x (x+k)).filter (d ∣ ·)).card = (x+k)/d - x/d := by
  have hu : (Ioc 0 (x+k)).filter (d ∣ ·) =
      ((Ioc 0 x).filter (d ∣ ·)) ∪ ((Ioc x (x+k)).filter (d ∣ ·)) := by
    ext n
    simp only [mem_union, mem_filter, mem_Ioc]
    omega
  have hd : Disjoint ((Ioc 0 x).filter (d ∣ ·)) ((Ioc x (x+k)).filter (d ∣ ·)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [mem_filter, mem_Ioc] at hn hm
    omega
  have hh := congrArg Finset.card hu
  rw [card_union_of_disjoint hd, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at hh
  omega

private lemma bound_fiber {N n k : ℕ} (hN : 2 ≤ N) (hn : 0 < n)
    (hb : n ≤ N^1001) (hk : N^499 ≤ k) :
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    ((P ×ˢ P).filter (fun w => w.1*w.2 ∣ n)).card ≤
      if n ∈ Nat.smoothNumbers (k+1) then 9 else 0 := by
  classical
  intro P
  let Q := P.filter (· ∣ n)
  have hmem {p : ℕ} (hp : p ∈ P) : N^251 < p ∧ p ≤ N^252 ∧ p.Prime := by
    simpa [P, and_assoc] using hp
  have hq : Q ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨h,d⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hmem h).2.2,d,hn.ne'⟩
  have hc : Q.card ≤ 3 := by
    by_contra! h
    have hl : (N^251)^Q.card ≤ ∏ p ∈ Q, p := by
      simpa using Finset.prod_le_prod' (fun p (hp : p ∈ Q) => (hmem (mem_filter.mp hp).1).1.le)
    have h4 : (N^251)^4 ≤ (N^251)^Q.card :=
      Nat.pow_le_pow_right (by positivity) (by omega)
    have hd := (Finset.prod_dvd_prod_of_subset Q n.primeFactors id hq).trans (Nat.prod_primeFactors_dvd n)
    have he : (N^251)^4 = N^1004 := by rw [← pow_mul]
    have hg : N^1001 < N^1004 := Nat.pow_lt_pow_right (by omega) (by decide)
    rw [he] at h4
    have hh := Nat.le_of_dvd hn hd
    change (∏ p ∈ Q, p) ≤ n at hh
    omega
  let T := (P ×ˢ P).filter (fun w => w.1*w.2 ∣ n)
  have hsub : T ⊆ Q ×ˢ Q := by
    intro w hw
    obtain ⟨hw,hd⟩ := mem_filter.mp hw
    obtain ⟨h1,h2⟩ := mem_product.mp hw
    exact mem_product.mpr ⟨mem_filter.mpr ⟨h1,(dvd_mul_right _ _).trans hd⟩,
      mem_filter.mpr ⟨h2,(dvd_mul_left _ _).trans hd⟩⟩
  change T.card ≤ _
  split_ifs with hs
  · have ht := card_le_card hsub
    rw [card_product] at ht
    nlinarith
  · apply le_of_eq
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨p,q⟩ hw
    obtain ⟨hw,hd⟩ := mem_filter.mp hw
    obtain ⟨hp,hq⟩ := mem_product.mp hw
    obtain ⟨r,hr⟩ := hd
    have hpq : N^502 ≤ p*q := by
      rw [show (502:ℕ) = 251+251 by decide, pow_add]
      exact Nat.mul_le_mul (hmem hp).1.le (hmem hq).1.le
    have hr0 : 0 < r := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hr; omega
    have h502 : 0 < N^502 := by positivity
    have hrk : r ≤ N^499 := by
      apply Nat.le_of_mul_le_mul_left _ h502
      calc N^502*r ≤ (p*q)*r := Nat.mul_le_mul_right _ hpq
           _ = n := hr.symm
           _ ≤ N^502*N^499 := by simpa [← pow_add] using hb
    have he : N^252 ≤ N^499 := Nat.pow_le_pow_right (by omega) (by decide)
    apply hs
    rw [hr]
    apply Nat.mul_mem_smoothNumbers
    · apply Nat.mul_mem_smoothNumbers
      · exact Nat.mem_smoothNumbers_of_lt (hmem hp).2.2.pos (by have := (hmem hp).2.1; omega)
      · exact Nat.mem_smoothNumbers_of_lt (hmem hq).2.2.pos (by have := (hmem hq).2.1; omega)
    · exact Nat.mem_smoothNumbers_of_lt hr0 (by omega)

private lemma smooth_indices (x k : ℕ) :
    ((Ioc x (x+k)).filter (· ∈ Nat.smoothNumbers (k+1))).card =
    ((univ : Finset (Fin k)).filter (fun i => x+i.val+1 ∈ Nat.smoothNumbers (k+1))).card := by
  symm
  apply card_bij (fun i _ => x+i.val+1)
  · intro i hi
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by have := i.isLt; omega⟩,(mem_filter.mp hi).2⟩
  · intro i hi j hj h
    apply Fin.ext
    omega
  · intro n hn
    obtain ⟨h,hs⟩ := mem_filter.mp hn
    obtain ⟨hl,hr⟩ := mem_Ioc.mp h
    let i : Fin k := ⟨n-x-1,by omega⟩
    have he : x+i.val+1=n := by dsimp [i]; omega
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,he.symm ▸ hs⟩,he⟩

private lemma count_upper {N x k : ℕ} (hN : 2 ≤ N) (hb : x+k ≤ N^1001) (hk : N^499 ≤ k) :
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    (∑ w ∈ P ×ˢ P, ((x+k)/(w.1*w.2)-x/(w.1*w.2))) ≤
      9 * ((univ : Finset (Fin k)).filter (fun i => x+i.val+1 ∈ Nat.smoothNumbers (k+1))).card := by
  classical
  intro P
  simp_rw [← count_div x k, card_filter]
  rw [sum_comm]
  calc _ ≤ ∑ n ∈ Ioc x (x+k), (if n ∈ Nat.smoothNumbers (k+1) then 9 else 0) := by
          apply sum_le_sum
          intro n hn
          obtain ⟨hl,hr⟩ := mem_Ioc.mp hn
          simpa only [card_filter] using bound_fiber hN (by omega : 0 < n) (hr.trans hb) hk
       _ = _ := by
          rw [← card_filter, ← smooth_indices x k, card_filter, mul_sum]
          apply sum_congr rfl
          intro n hn
          split_ifs <;> simp

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    c ≤ ∑ p ∈ (Ioc (N^251) (N^252)).filter Nat.Prime, 1/(p:ℝ)

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ t : ℕ, N^1000 ≤ t → t ≤ N^1001 →
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    |∑ w ∈ P ×ˢ P, ((((t/(w.1*w.2):ℕ):ℝ) - (t:ℝ)/((w.1*w.2:ℕ):ℝ)) + 1/2)| ≤
      ε*(N:ℝ)^499

private lemma interval_lower (P : Finset ℕ) (x k : ℕ) :
    let B := fun t : ℕ => ∑ w ∈ P ×ˢ P,
      ((((t/(w.1*w.2):ℕ):ℝ) - (t:ℝ)/((w.1*w.2:ℕ):ℝ)) + 1/2)
    ((∑ w ∈ P ×ˢ P, ((x+k)/(w.1*w.2)-x/(w.1*w.2)) : ℕ) : ℝ) =
      B (x+k) - B x + (k:ℝ)*(∑ p ∈ P, 1/(p:ℝ))^2 := by
  dsimp only
  have hs : (∑ p ∈ P, 1/(p:ℝ))^2 = ∑ w ∈ P ×ˢ P, 1/((w.1*w.2:ℕ):ℝ) := by
    rw [sq, sum_mul, sum_product]
    apply sum_congr rfl
    intro p hp
    rw [mul_sum]
    apply sum_congr rfl
    intro q hq
    simp [Nat.cast_mul, div_eq_mul_inv, mul_comm]
  rw [hs, ← sum_sub_distrib, mul_sum, ← sum_add_distrib, Nat.cast_sum]
  apply sum_congr rfl
  intro w hw
  rw [Nat.cast_sub (Nat.div_le_div_right (by omega : x ≤ x+k)), Nat.cast_add]
  ring

theorem main : H1 → H2 → OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.H1 := by
  rintro ⟨c,hc,hm⟩ herror
  refine ⟨499/1000,by norm_num,by norm_num,c^2/18,by positivity,?_⟩
  let ε := c^2/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ht : Tendsto (Nat.nthRoot 1000) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b^1000)] with x hx
    exact (Nat.le_nthRoot_iff (by decide)).2 hx
  filter_upwards [ht.eventually hm, ht.eventually (herror ε hε),
    ht.eventually (eventually_ge_atTop (2^1001))] with x hx he hlarge
  let N := Nat.nthRoot 1000 x
  let k := ⌊(x:ℝ)^(499/1000:ℝ)⌋₊
  let P := (Ioc (N^251) (N^252)).filter Nat.Prime
  change c ≤ ∑ p ∈ P, 1/(p:ℝ) at hx
  change 2^1001 ≤ N at hlarge
  have hN : 2 ≤ N := (show 2 ≤ 2^1001 from (pow_one (2:ℕ)) ▸ Nat.pow_le_pow_right (by decide) (by decide : 1 ≤ 1001)).trans hlarge
  have hl : N^1000 ≤ x := Nat.pow_nthRoot_le (.inl (by decide))
  have hx1 : 1 ≤ x := le_trans (Nat.one_le_pow _ _ (by omega : 0 < N)) hl
  have hkx : k ≤ x := by
    apply Nat.floor_le_of_le
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast hx1) (by norm_num)
  have hk : N^499 ≤ k := by
    apply Nat.le_floor
    push_cast
    have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (N:ℝ)^1000)
      (by exact_mod_cast hl : (N:ℝ)^1000 ≤ (x:ℝ)) (by norm_num : 0 ≤ (499/1000:ℝ))
    rw [← Real.rpow_natCast_mul (by positivity)] at h
    rw [show ((1000:ℕ):ℝ)*(499/1000) = ((499:ℕ):ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  have hu : x+k ≤ N^1001 := by
    have hlt : x < (N+1)^1000 := (Nat.nthRoot_lt_iff (by decide : (1000:ℕ) ≠ 0)).mp (show N < N+1 by omega)
    have hle : (N+1)^1000 ≤ (2*N)^1000 := Nat.pow_le_pow_left (by omega) _
    rw [mul_pow] at hle
    calc x+k ≤ 2*(2^1000*N^1000) := by omega
         _ = 2^1001*N^1000 := by rw [← Nat.mul_assoc, ← pow_succ' (2:ℕ) 1000]
         _ ≤ N*N^1000 := Nat.mul_le_mul_right _ hlarge
         _ = N^1001 := by rw [pow_succ N 1000, Nat.mul_comm]
  let B := fun t : ℕ => ∑ w ∈ P ×ˢ P,
    ((((t/(w.1*w.2):ℕ):ℝ) - (t:ℝ)/((w.1*w.2:ℕ):ℝ)) + 1/2)
  have he1 : |B x| ≤ ε*(N:ℝ)^499 := he x hl ((Nat.le_add_right x k).trans hu)
  have he2 : |B (x+k)| ≤ ε*(N:ℝ)^499 := he (x+k) (hl.trans (Nat.le_add_right x k)) hu
  have herr : ε*(N:ℝ)^499 ≤ ε*(k:ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact_mod_cast hk
  have hd := (abs_le.mp (he1.trans herr)).2
  have hd' := (abs_le.mp (he2.trans herr)).1
  have hsq := mul_self_le_mul_self hc.le hx
  rw [←sq,←sq] at hsq
  have hpos := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) k)
  have hu' := count_upper hN hu hk
  have hreal : ((∑ w ∈ P ×ˢ P, ((x+k)/(w.1*w.2)-x/(w.1*w.2)) : ℕ) : ℝ) ≤
      9 * (((univ : Finset (Fin k)).filter
        (fun i => x+i.val+1 ∈ Nat.smoothNumbers (k+1))).card : ℝ) := by exact_mod_cast hu'
  rw [interval_lower] at hreal
  change B (x+k) - B x + _ ≤ _ at hreal
  change c^2/18*(k:ℝ) ≤ _
  dsimp [ε] at hd hd'
  linarith

end OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1
end

section
/- Short-interval smooth numbers. We remove the prime restriction in one
variable by Cauchy–Schwarz on blocks of width N^40. Van der Corput's
second-derivative estimate applies to the reciprocal phase for each pair
from the same block. A truncated Fourier bound for the periodic second
Bernoulli polynomial recovers the centered floor error. -/

namespace OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1
open Filter Finset

/-- Off-diagonal estimate on the full integer interval, for nearby denominators. -/
def H1 : Prop :=
  ∀ N t h : ℕ, 2 ≤ N → N^1000 ≤ t → t ≤ N^1001 → 1 ≤ h → h ≤ N^20 →
    let J := Ioc (N^251) (N^252)
    let u (p q : ℕ) := (t:ℝ)/((p*q:ℕ):ℝ)
    let e (u : ℝ) := Complex.exp (((2*Real.pi*u : ℝ) : ℂ)*Complex.I)
    ∀ a ∈ J, ∀ b ∈ J, a < b → b-a ≤ N^40 →
      ‖∑ p ∈ J, e ((h:ℝ)*(u p a - u p b))‖ ≤ 16*(N:ℝ)^188

/-- Squaring on blocks and completing the first variable to all integers. -/
def H2 : Prop :=
  ∀ N t h : ℕ, 2 ≤ N → N^1000 ≤ t → t ≤ N^1001 → 1 ≤ h → h ≤ N^20 →
    let J := Ioc (N^251) (N^252)
    let u (p q : ℕ) := (t:ℝ)/((p*q:ℕ):ℝ)
    let e (u : ℝ) := Complex.exp (((2*Real.pi*u : ℝ) : ℂ)*Complex.I)
    let P := J.filter Nat.Prime
    (∀ a ∈ J, ∀ b ∈ J, a < b → b-a ≤ N^40 →
      ‖∑ p ∈ J, e ((h:ℝ)*(u p a - u p b))‖ ≤ 16*(N:ℝ)^188) →
      ‖∑ w ∈ P ×ˢ P, e ((h:ℝ)*u w.1 w.2)‖ ≤ 10*(N:ℝ)^484

/-- Truncated Fourier smoothing of the centered quotient error. -/
def H3 : Prop :=
  ∀ N t : ℕ, 2 ≤ N →
    let J := Ioc (N^251) (N^252)
    let P := J.filter Nat.Prime
    let u (p q : ℕ) := (t:ℝ)/((p*q:ℕ):ℝ)
    let e (u : ℝ) := Complex.exp (((2*Real.pi*u : ℝ) : ℂ)*Complex.I)
    (∀ h : ℕ, 1 ≤ h → h ≤ N^20 → ‖∑ w ∈ P ×ˢ P, e ((h:ℝ)*u w.1 w.2)‖ ≤ 10*(N:ℝ)^484) →
    |∑ w ∈ P ×ˢ P, ((((t/(w.1*w.2):ℕ):ℝ) - u w.1 w.2) + 1/2)| ≤ 1000*(N:ℝ)^498

theorem main : H1 → H2 → H3 → OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1.H2 := by
  intro estimate blocks smooth ε hε
  obtain ⟨n₀,hn₀⟩ := exists_nat_ge (1000/ε)
  filter_upwards [eventually_ge_atTop (max 2 n₀)] with N hN
  have two : 2 ≤ N := (le_max_left _ _).trans hN
  have hn : n₀ ≤ N := (le_max_right _ _).trans hN
  intro t ht ht'
  have bound := smooth N t two (fun h hp hmax =>
    blocks N t h two ht ht' hp hmax (estimate N t h two ht ht' hp hmax))
  apply bound.trans
  have rat : 1000/ε ≤ (N:ℝ) := hn₀.trans (Nat.cast_le.mpr hn)
  have coeff := (div_le_iff₀ hε).mp rat
  calc
    1000*(N:ℝ)^498 ≤ ((N:ℝ)*ε)*(N:ℝ)^498 := by gcongr
    _ = ε*(N:ℝ)^499 := by ring

end OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1
end

section
-- Step Erdos375.erdos_375.variants.bounded_gap.R1.H2: hypothesis H2 of reduction Erdos375.erdos_375.variants.bounded_gap.R1
-- Credit: @loremcdmx
-- H2 := ∀ c : ℝ, 0 < c → ∀ᶠ k : ℕ in atTop,   ((k + 1).primesBelow.card : ℝ) < c * k

open Filter

theorem Erdos375Upstream.PrimeDensity : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.H2 := by
  intro c hc
  have h1 := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
  have h1' : ∀ᶠ k : ℕ in atTop, Nat.primeCounting ⌊(k : ℝ)⌋₊ ≤ (Real.log 4 + 1) * (k : ℝ) / Real.log k :=
    tendsto_natCast_atTop_atTop.eventually h1
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := hlog.eventually_gt_atTop (2 * (Real.log 4 + 1) / c)
  filter_upwards [h1', h2, eventually_ge_atTop 2] with k hk hl hk2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc4 : 0 < Real.log 4 + 1 := by have := Real.log_pos (by norm_num : (1:ℝ) < 4); linarith
  have hl0 : 0 < Real.log k := lt_trans (by positivity) hl
  have hcard : ((k + 1).primesBelow.card : ℝ) = (Nat.primeCounting k : ℝ) := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [hcard]
  simp only [Nat.floor_natCast] at hk
  have : (Real.log 4 + 1) * k / Real.log k < c * k := by
    rw [div_lt_iff₀ hl0]
    rw [div_lt_iff₀ hc] at hl
    nlinarith [mul_pos hc hkpos, mul_pos hc4 hkpos]
  exact lt_of_le_of_lt hk this
end

section
/- The first Mertens bound below is due to @senamakel, adapted in the merged Erdős 377 and 1100 proofs by @marcusbuffett. -/

section
open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith


end OMALib.Mertens

end

open Real Finset Filter OMALib.Mertens

theorem Erdos375Upstream.Reciprocal : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1.H1 := by
  refine ⟨1/504,by norm_num,?_⟩
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (4*mertens1Const + 1)
  filter_upwards [hl,eventually_ge_atTop 2] with N hL hN
  change 4*mertens1Const+1 ≤ log N at hL
  have hpos : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hpow : N^251 ≤ N^252 := Nat.pow_le_pow_right (by omega) (by decide)
  let P := (Ioc (N^251) (N^252)).filter Nat.Prime
  have hsub : (N^251).primesLE ⊆ (N^252).primesLE := by
    intro p hp
    obtain ⟨h,pr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨h.trans hpow,pr⟩
  have heq : (N^252).primesLE \ (N^251).primesLE = P := by
    apply Finset.ext
    intro p
    rw [Finset.mem_sdiff,Nat.mem_primesLE,Nat.mem_primesLE]
    change (p ≤ N^252 ∧ p.Prime) ∧ ¬(p ≤ N^251 ∧ p.Prime) ↔ p∈P
    simp only [P,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨⟨hi,pr⟩,no⟩
      exact ⟨⟨lt_of_not_ge (fun lo => no ⟨lo,pr⟩),hi⟩,pr⟩
    · rintro ⟨⟨lo,hi⟩,pr⟩
      exact ⟨⟨hi,pr⟩,fun x => (not_le_of_gt lo) x.1⟩
  have hd := sum_sdiff hsub (f:=fun p:ℕ => log (p:ℝ)/p)
  rw [heq] at hd
  have h1 := (abs_le.mp (abs_sum_log_div_sub_log_le_nat (N^251))).2
  have h2 := (abs_le.mp (abs_sum_log_div_sub_log_le_nat (N^252))).1
  simp only [Nat.cast_pow,log_pow] at h1 h2
  have h3 : ∑ p ∈ P, log (p:ℝ)/p ≤ 252*log (N:ℝ)*(∑ p ∈ P, 1/(p:ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hh,pr⟩ := mem_filter.mp hp
    have hlog := log_le_log (by exact_mod_cast pr.pos : 0 < (p:ℝ))
      (by exact_mod_cast (mem_Ioc.mp hh).2 : (p:ℝ) ≤ ((N^252:ℕ):ℝ))
    simp only [Nat.cast_pow,log_pow] at hlog
    calc _ ≤ (252*log (N:ℝ))/(p:ℝ) := by
             apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
             simpa using hlog
         _ = _ := by ring
  have hm : log (N:ℝ)/2 ≤ 252*log (N:ℝ)*(∑ p ∈ P,1/(p:ℝ)) := by
    norm_num at h1 h2
    linarith
  change 1/504 ≤ ∑ p ∈ P,1/(p:ℝ)
  apply le_of_mul_le_mul_left (a:=252*log (N:ℝ)) _ (by positivity)
  linarith
end

section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-
# The Kusmin–Landau inequality and van der Corput's second-derivative test

This file develops the B-side foundation of the van der Corput exponential-sum
toolkit: the **Kusmin–Landau inequality** (`kusmin_landau`, milestone 1), on the
character `eK`, the telescoping weight `wK` and their trigonometric identities
(`eK_re`, `eK_im`, `one_sub_eK_re`, `one_sub_eK_im`, `normSq_one_sub_eK`,
`norm_one_sub_eK`, `wK_re`, `wK_im`, `norm_wK`). The discrete **second-derivative
test** built on it (milestone 2) is `vdC_second_derivative` in
`Salt/ExpSum/VdCorput2.lean`, with the constant `8`; the arithmetic recorded at the
foot of this file was written before it landed and advertised `5`.

## House note on the character

A concurrent executor is building `Salt/ExpSum/Basic.lean` with an additive
character `eR (x : ℝ) : ℂ := Complex.exp (2πi x)` and its API.  To stay
independent this file defines a **private local copy** `eK` with the *same*
definition.  The house should **unify `eK` with `eR` at wire-in** — every use
of `eK` here is exactly `Complex.exp (2 * π * x * I)`.

## Milestone 1 — Kusmin–Landau

Stated discretely on the consecutive differences `g n := f (n+1) - f n`.

**Mathematical note (a real catch).**  The naive discrete hypothesis
"`Int.fract (g n) ∈ [δ, 1-δ]` and `g` monotone" is *insufficient*: without
pinning `g n` into a *single* unit interval the bound degrades to
`O((b-a)/δ)` (each integer that `g` crosses between samples costs `≍ 1/δ` of
total variation).  In the continuous Kusmin–Landau this cannot happen —
continuity + monotonicity + "bounded away from integers" force `g` to stay in
one interval `(m+δ, m+1-δ)`.  We therefore state the honest discrete shadow:
there is a fixed integer `m` with `g n ∈ [m+δ, m+1-δ]` throughout.  This is
exactly the window that milestone 2's decomposition produces, so the two
milestones are internally consistent.

Result: `‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`  (absolute constant `C = 1`).

The engine is the telescoping weight `w n := (1 - eK (g n))⁻¹`.  Its key
feature (`wK_re`) is that `Re (w n) = 1/2` is *constant*, so the Abel
differences `w (n+1) - w n` are purely imaginary and their total variation
telescopes through `Im (w n) = cot(π · g n)/2`, which is monotone because `g`
is monotone.
-/

namespace Salt.ExpSum

open Real Finset

/-- Private local additive character `eK x = exp(2πi x)`.  **Unify with
`Basic.eR` at wire-in** (identical definition). -/
noncomputable def eK (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

/-- `‖eK x‖ = 1`. -/
@[simp] lemma eK_norm (x : ℝ) : ‖eK x‖ = 1 := by
  simp only [eK]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `eK (x + y) = eK x * eK y`. -/
lemma eK_add (x y : ℝ) : eK (x + y) = eK x * eK y := by
  simp only [eK, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- Periodicity: `eK` is unchanged by adding an integer. -/
lemma eK_add_intCast (x : ℝ) (k : ℤ) : eK (x + (k : ℝ)) = eK x := by
  have h : (((2 * π * (x + (k : ℝ))) : ℝ) : ℂ) * Complex.I
      = (((2 * π * x : ℝ)) : ℂ) * Complex.I + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast; ring
  simp only [eK, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `eK` in real cos/sin form. -/
lemma eK_eq (s : ℝ) :
    eK s = (Real.cos (2 * π * s) : ℂ) + (Real.sin (2 * π * s) : ℂ) * Complex.I := by
  simp only [eK, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `(eK s).re = cos (2πs)`. -/
lemma eK_re (s : ℝ) : (eK s).re = Real.cos (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- `(eK s).im = sin (2πs)`. -/
lemma eK_im (s : ℝ) : (eK s).im = Real.sin (2 * π * s) := by
  rw [eK_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

/-- `(1 - eK s).re = 2 sin²(πs)`. -/
lemma one_sub_eK_re (s : ℝ) : (1 - eK s).re = 2 * Real.sin (π * s) ^ 2 := by
  have h1 : (1 - eK s).re = 1 - Real.cos (2 * π * s) := by simp [eK_re]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

/-- `(1 - eK s).im = -2 sin(πs) cos(πs)`. -/
lemma one_sub_eK_im (s : ℝ) : (1 - eK s).im = -(2 * Real.sin (π * s) * Real.cos (π * s)) := by
  have h1 : (1 - eK s).im = -Real.sin (2 * π * s) := by simp [eK_im]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.sin_two_mul]

/-- `normSq (1 - eK s) = 4 sin²(πs)`. -/
lemma normSq_one_sub_eK (s : ℝ) : Complex.normSq (1 - eK s) = 4 * Real.sin (π * s) ^ 2 := by
  rw [Complex.normSq_apply, one_sub_eK_re, one_sub_eK_im]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

/-- Norm of `1 - eK s` as `2|sin(πs)|`. -/
lemma norm_one_sub_eK (s : ℝ) : ‖1 - eK s‖ = 2 * |Real.sin (π * s)| := by
  rw [Complex.norm_def, normSq_one_sub_eK]
  rw [show (4 : ℝ) * Real.sin (π * s) ^ 2 = (2 * |Real.sin (π * s)|) ^ 2 by
        rw [mul_pow]; rw [sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- The telescoping weight. -/
noncomputable def wK (s : ℝ) : ℂ := (1 - eK s)⁻¹

/-- `Re (wK s) = 1/2` (constant!) whenever `sin(πs) ≠ 0`. -/
lemma wK_re (s : ℝ) (hs : Real.sin (π * s) ≠ 0) : (wK s).re = 1 / 2 := by
  rw [wK, Complex.inv_re, normSq_one_sub_eK, one_sub_eK_re]
  have : Real.sin (π * s) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp
  ring

/-- `Im (wK s) = cos(πs)/(2 sin(πs)) = cot(πs)/2`. -/
lemma wK_im (s : ℝ) (hs : Real.sin (π * s) ≠ 0) :
    (wK s).im = Real.cos (π * s) / (2 * Real.sin (π * s)) := by
  rw [wK, Complex.inv_im, normSq_one_sub_eK, one_sub_eK_im]
  field_simp
  ring

/-- `‖wK s‖ = 1 / (2|sin(πs)|)`. -/
lemma norm_wK (s : ℝ) : ‖wK s‖ = 1 / (2 * |Real.sin (π * s)|) := by
  rw [wK, norm_inv, norm_one_sub_eK, inv_eq_one_div]

/-- `sin(πs) > 0` for `s ∈ (0,1)`. -/
lemma sin_pi_mul_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < Real.sin (π * s) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith only [h1, Real.pi_pos]

/-- Jordan's inequality, symmetrised: `sin(πs) ≥ 2δ` for `s ∈ [δ, 1-δ]`, `δ ≤ 1/2`. -/
lemma sin_pi_mul_ge {δ s : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hs1 : δ ≤ s)
    (hs2 : s ≤ 1 - δ) : 2 * δ ≤ Real.sin (π * s) := by
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ≤ Real.sin (π * t) := by
    intro t ht0 ht1
    have hj := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith [Real.pi_pos])
    have hid : 2 / π * (π * t) = 2 * t := by field_simp
    linarith [hid ▸ hj]
  by_cases h : s ≤ 1 / 2
  · exact le_trans (by linarith) (hkey s (by linarith) h)
  · replace h := not_le.mp h
    have hsym : Real.sin (π * s) = Real.sin (π * (1 - s)) := by
      rw [show π * (1 - s) = π - π * s by ring, Real.sin_pi_sub]
    rw [hsym]
    exact le_trans (by linarith) (hkey (1 - s) (by linarith) (by linarith))

/-- Monotonicity of `Im (wK ·) = cot(π ·)/2`: antitone on `(0,1)`. -/
lemma wK_im_antitone {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ < 1) :
    Real.cos (π * s₂) / (2 * Real.sin (π * s₂))
      ≤ Real.cos (π * s₁) / (2 * Real.sin (π * s₁)) := by
  have hs1 : 0 < Real.sin (π * s₁) := sin_pi_mul_pos h1 (lt_of_le_of_lt h12 h2)
  have hs2 : 0 < Real.sin (π * s₂) := sin_pi_mul_pos (lt_of_lt_of_le h1 h12) h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsin : 0 ≤ Real.sin (π * s₂ - π * s₁) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith only [h12, Real.pi_pos]
    · nlinarith only [h2, h12, h1, Real.pi_pos, mul_pos Real.pi_pos h1]
  rw [Real.sin_sub] at hsin
  linarith only [hsin]

/-- A purely imaginary complex number has norm equal to `|Im|`. -/
lemma norm_eq_abs_im_of_re_eq_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  rw [Complex.norm_def, Complex.normSq_apply, h, zero_mul, zero_add, ← sq,
    Real.sqrt_sq_eq_abs]

/-- Abel summation over `range (N+1)`, telescoped form. -/
lemma abel_range (C B : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (N + 1), C k * (B k - B (k + 1))
      = C 0 * B 0 - C N * B (N + 1) + ∑ k ∈ range N, (C (k + 1) - C k) * B (k + 1) := by
  induction N with
  | zero => simp; ring
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- **The Kusmin–Landau inequality (discrete form).**

Let `g n := f (n+1) - f n` be the consecutive differences of a phase `f`.
If `g` is monotone (increasing) on `(a, b]` and stays in a single unit
interval bounded away from the integers, `g n ∈ [m + δ, m + 1 - δ]` with
`δ ∈ (0, 1/2]`, then the exponential sum obeys
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 1 / δ`.  The constant is absolute (`C = 1`).

See the file header for why the single-interval hypothesis is essential
(the `Int.fract`-only form is genuinely too weak). -/
theorem kusmin_landau {f : ℕ → ℝ} {a b : ℕ} {δ : ℝ} {m : ℤ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hg_lb : ∀ n, a < n → n ≤ b → (m : ℝ) + δ ≤ f (n + 1) - f n)
    (hg_ub : ∀ n, a < n → n ≤ b → f (n + 1) - f n ≤ (m : ℝ) + 1 - δ)
    (hmono : ∀ n, a < n → n < b → f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ 1 / δ := by
  rcases Nat.lt_or_ge a b with hab | hab
  · -- Main case `a < b`.
    set N : ℕ := b - a - 1 with hNdef
    have hbN : b = a + 1 + N := by omega
    -- reindex `Ioc a b` to `range (N+1)`
    have hIoc : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.sum_Ico_eq_sum_range, show b + 1 - (a + 1) = N + 1 by omega]
    -- local sequences
    set σ : ℕ → ℝ := fun k => f (a + 1 + k + 1) - f (a + 1 + k) - (m : ℝ) with hσdef
    set B : ℕ → ℂ := fun k => eK (f (a + 1 + k)) with hBdef
    set W : ℕ → ℂ := fun k => wK (σ k) with hWdef
    -- range facts on `σ`
    have hσ_range : ∀ k, k ≤ N → δ ≤ σ k ∧ σ k ≤ 1 - δ := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k ≤ b := by omega
      have hlb := hg_lb (a + 1 + k) h1 h2
      have hub := hg_ub (a + 1 + k) h1 h2
      simp only [hσdef]; constructor <;> [linarith; linarith]
    have hsin_pos : ∀ k, k ≤ N → 0 < Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_pos (by linarith) (by linarith)
    have hsin_ge : ∀ k, k ≤ N → 2 * δ ≤ Real.sin (π * σ k) := by
      intro k hk
      obtain ⟨hl, hu⟩ := hσ_range k hk
      exact sin_pi_mul_ge hδ0 hδ hl hu
    have hσ_mono : ∀ k, k < N → σ k ≤ σ (k + 1) := by
      intro k hk
      have h1 : a < a + 1 + k := by omega
      have h2 : a + 1 + k < b := by omega
      have := hmono (a + 1 + k) h1 h2
      simp only [hσdef]
      have he : a + 1 + (k + 1) = a + 1 + k + 1 := by ring
      have he2 : a + 1 + k + 1 + 1 = a + 1 + k + 2 := by ring
      rw [he, he2]; linarith
    -- `Re W = 1/2`, `Im W = cot/2`, monotone, norm-bounded
    have hWre : ∀ k, k ≤ N → (W k).re = 1 / 2 := by
      intro k hk; simp only [hWdef]; exact wK_re _ (ne_of_gt (hsin_pos k hk))
    have hWim : ∀ k, k ≤ N →
        (W k).im = Real.cos (π * σ k) / (2 * Real.sin (π * σ k)) := by
      intro k hk; simp only [hWdef]; exact wK_im _ (ne_of_gt (hsin_pos k hk))
    have hWmono : ∀ k, k < N → (W (k + 1)).im ≤ (W k).im := by
      intro k hk
      rw [hWim (k + 1) (by omega), hWim k (by omega)]
      obtain ⟨hl, _⟩ := hσ_range k (by omega)
      obtain ⟨_, hu⟩ := hσ_range (k + 1) (by omega)
      exact wK_im_antitone (by linarith) (hσ_mono k hk) (by linarith)
    have hWimabs : ∀ k, k ≤ N → |(W k).im| ≤ 1 / (4 * δ) := by
      intro k hk
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [hWim k hk, abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hs) (by positivity)]
      have hcos : |Real.cos (π * σ k)| ≤ 1 := Real.abs_cos_le_one _
      linarith only [hsg,
          mul_le_mul_of_nonneg_right hcos (by positivity : (0 : ℝ) ≤ 4 * δ)]
    have hWnorm : ∀ k, k ≤ N → ‖W k‖ ≤ 1 / (4 * δ) := by
      intro k hk
      simp only [hWdef, norm_wK]
      have hs := hsin_pos k hk
      have hsg := hsin_ge k hk
      rw [abs_of_pos hs]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    -- pointwise Kusmin–Landau identity
    have hid : ∀ k, k ≤ N → W k * (B k - B (k + 1)) = B k := by
      intro k hk
      have hne : 1 - eK (σ k) ≠ 0 := by
        intro hzero
        rw [← norm_eq_zero, norm_one_sub_eK] at hzero
        have hs := hsin_pos k hk
        have : |Real.sin (π * σ k)| = 0 := by linarith [abs_nonneg (Real.sin (π * σ k))]
        rw [abs_eq_zero] at this; linarith
      have hBrec : B (k + 1) = B k * eK (σ k) := by
        simp only [hBdef]
        rw [show f (a + 1 + (k + 1)) = f (a + 1 + k) + (σ k + (m : ℝ)) by
              simp only [hσdef]; ring]
        rw [eK_add, eK_add_intCast]
      rw [hBrec]
      have hfac : B k - B k * eK (σ k) = B k * (1 - eK (σ k)) := by ring
      rw [hfac]
      simp only [hWdef, wK]
      rw [mul_comm (B k) (1 - eK (σ k)), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    -- Abel + triangle inequality
    have hsumeq : ∑ k ∈ Finset.range (N + 1), B k
        = ∑ k ∈ Finset.range (N + 1), W k * (B k - B (k + 1)) :=
      Finset.sum_congr rfl fun k hk => (hid k (by simpa using Finset.mem_range.mp hk)).symm
    have hBnorm : ∀ k, ‖B k‖ = 1 := fun k => by simp only [hBdef]; exact eK_norm _
    rw [hsumeq, abel_range W B N]
    -- variation telescopes to `Im (W 0) - Im (W N)`
    have hvar : ∀ k, k < N → ‖W (k + 1) - W k‖ = (W k).im - (W (k + 1)).im := by
      intro k hk
      have hre : (W (k + 1) - W k).re = 0 := by
        rw [Complex.sub_re, hWre (k + 1) (by omega), hWre k (by omega)]; ring
      rw [norm_eq_abs_im_of_re_eq_zero hre, Complex.sub_im,
        abs_of_nonpos (by linarith [hWmono k hk])]; ring
    have hvarsum : ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ = (W 0).im - (W N).im := by
      rw [Finset.sum_congr rfl fun k hk => hvar k (Finset.mem_range.mp hk)]
      exact Finset.sum_range_sub' (fun k => (W k).im) N
    calc ‖W 0 * B 0 - W N * B (N + 1)
              + ∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖
        ≤ ‖W 0 * B 0 - W N * B (N + 1)‖
            + ‖∑ k ∈ Finset.range N, (W (k + 1) - W k) * B (k + 1)‖ := norm_add_le _ _
      _ ≤ (‖W 0 * B 0‖ + ‖W N * B (N + 1)‖)
            + ∑ k ∈ Finset.range N, ‖(W (k + 1) - W k) * B (k + 1)‖ := by
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ = (‖W 0‖ + ‖W N‖) + ∑ k ∈ Finset.range N, ‖W (k + 1) - W k‖ := by
          simp only [norm_mul, hBnorm, mul_one]
      _ = (‖W 0‖ + ‖W N‖) + ((W 0).im - (W N).im) := by rw [hvarsum]
      _ ≤ (1 / (4 * δ) + 1 / (4 * δ)) + (1 / (4 * δ) + 1 / (4 * δ)) := by
          gcongr
          · exact hWnorm 0 (by omega)
          · exact hWnorm N (by omega)
          · have h0 := le_trans (le_abs_self (W 0).im) (hWimabs 0 (by omega))
            have hN := le_trans (neg_le_abs (W N).im) (hWimabs N (by omega))
            linarith
      _ = 1 / δ := by field_simp; ring
  · -- Empty case `b ≤ a`.
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity

/-
## Milestone 2 — the second-derivative test (the paper arithmetic, recorded before
`Salt/ExpSum/VdCorput2.lean` landed `vdC_second_derivative`)

**Target statement.**  With `g n := f (n+1) - f n`, additionally assume the
second differences obey `λ ≤ g (n+1) - g n ≤ c · λ` for all `n` in range
(`0 < λ`, `1 ≤ c`).  Then, with `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 5 · (c · L · √λ + 1 / √λ)`   (absolute `C' = 5`).

**Paper arithmetic (fully worked; this is the deliverable design).**

Set `δ := √λ`.  Split on the size of `λ`:

* **Case `λ > 1/4`** (so `√λ > 1/2`).  Bound trivially:
  `‖S‖ ≤ #(Ioc a b) = L` (each `‖eK‖ = 1`).  Since `c ≥ 1` and `√λ > 1/2`,
  `L < 2·c·L·√λ ≤ 5·(c L √λ + 1/√λ)`.  ✔

* **Case `λ ≤ 1/4`** (so `δ = √λ ≤ 1/2`, and `λ ≤ 1`).  Because
  `g (n+1) - g n ≥ λ > 0`, `g` is *strictly increasing*.  Decompose
  `Ioc a b` fibrewise by `k := ⌊g n⌋` (`Finset.sum_fiberwise_of_maps_to`):
  each fibre `F_k := {n ∈ Ioc a b : ⌊g n⌋ = k}` is contiguous (`g` mono) and
  the fibres partition the range.  Within `F_k` split by monotonicity into

    - the **good part** `G_k := {n ∈ F_k : g n ∈ [k+δ, k+1-δ]}` — a single
      sub-`Ioc`, so `kusmin_landau` (with this `m := k`) gives
      `‖∑_{G_k} eK (f n)‖ ≤ 1/δ`;
    - the **bad part** `B_k := F_k \ G_k` = `{g n ∈ [k,k+δ) ∪ (k+1-δ,k+1)}`.
      Bound trivially by `#B_k`.  Since `g` increases by `≥ λ` per step, a
      window of `g`-length `w` holds `≤ w/λ + 1` indices, so each of the two
      bad sub-windows (length `δ`) has `≤ δ/λ + 1` indices:
      `#B_k ≤ 2·(δ/λ) + 2`.

  Number of non-empty fibres:
  `K ≤ ⌊g_b⌋ - ⌊g_{a+1}⌋ + 1 ≤ (g_b - g_{a+1}) + 1 ≤ c·λ·L + 1`.

  Summing over the `K` fibres:
  `‖S‖ ≤ K·(1/δ) + K·(2δ/λ + 2) = K·(1/δ + 2δ/λ + 2)`.
  With `δ = √λ`:  `1/δ = 1/√λ`, `2δ/λ = 2/√λ`, so the bracket is
  `3/√λ + 2`, and
  `‖S‖ ≤ (c λ L + 1)·(3/√λ + 2)`
       `= 3 c L √λ + 2 c λ L + 3/√λ + 2`.
  Using `λ ≤ 1` (`⇒ √λ ≤ 1`):  `2 c λ L = 2√λ·(c L √λ) ≤ 2 c L √λ` and
  `2 = 2√λ/√λ ≤ 2/√λ`.  Hence
  `‖S‖ ≤ 5 c L √λ + 5/√λ = 5·(c L √λ + 1/√λ)`.  ✔

Both cases give `C' = 5`.

**What the Lean build needed (the three pieces; `VdCorput2.lean` built (2) and (3)).**
The elementary content above needs three pieces of `Finset` engineering, the
middle one being a genuine sub-obstacle with no mathlib shortcut (see the
recon: only the *identity* predicate has `filter_lt_le_eq_Ioc`):

1.  fibrewise decomposition — available (`Finset.sum_fiberwise_of_maps_to`);
2.  **`G_k` (a monotone-predicate filter of an interval) equals an explicit
    `Finset.Ioc`** — must be built from `StrictMono (g)` by hand; this is a
    C-tier node in its own right and gates the `kusmin_landau` application;
3.  the crossing/window count `#B_k ≤ 2δ/λ + 2` and `K ≤ cλL + 1` from the
    per-step lower bound `g (n+1) - g n ≥ λ`.

`kusmin_landau` (milestone 1) is stated exactly to receive the good windows
`G_k` (single interval `m := k`, `g` increasing). The residual `VK-N2-M2` in
`flags.md` records both the deferral and its closure (2026-07-17): `VdCorput2.lean`
takes (1) from mathlib (`Finset.sum_fiberwise_of_maps_to`) and builds (2) as
`fibre_is_interval` and (3) as `count_window` and `step_accum`, and its
fibre count `K ≤ cλL + 2` (the step `⌊x⌋ - ⌊y⌋ ≤ x - y` above is false in general)
lands `vdC_second_derivative` with `C' = 8` in place of the `5` derived above.
-/

end Salt.ExpSum
end

section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-
# van der Corput's second-derivative test (Milestone 2)

This file discharges the `VK-N2-M2` residual: the discrete second-derivative
test built on top of `kusmin_landau` (Milestone 1, `Salt/ExpSum/Kusmin.lean`).

With `g n := f (n+1) - f n` the consecutive differences, if the second
differences satisfy `lam ≤ g (n+1) - g n ≤ c · lam` on the range (`0 < lam`,
`1 ≤ c`), then for `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · L · √lam + 1 / √lam)`.

See the file `Kusmin.lean`'s Milestone-2 docstring for the full paper
arithmetic.  The engine here:

* `step_accum` — accumulate a per-step difference bound `g (n+1) - g n ≤ β`
  into `g q - g p ≤ (q - p) · β`.  Used twice (with `β = c·lam` and, via `-g`,
  with the lower bound `lam`).
* `fibre_is_interval` — **the sub-obstacle**: a `g`-monotone-predicate filter of
  an interval `Ioc a b` is itself a `Finset.Ioc`.  Built by hand from strict
  monotonicity via `min'`/`max'` (no mathlib shortcut exists for a general
  monotone predicate).  This is what lets each good window feed `kusmin_landau`.
* `count_window` — a window of `g`-length `w` holds `≤ w/lam + 1` indices, since
  `g` steps up by `≥ lam`.  Bounds the two bad windows per fibre.

**Constant.**  The recorded arithmetic advertised `C' = 5` using the (in general
false) step `⌊x⌋ - ⌊y⌋ ≤ x - y`; the honest fibre count is `K ≤ c·lam·L + 2`,
which lands the constant at `C' = 8` (explicitly permitted by the task).
-/

namespace Salt.ExpSum

open Real Finset

/-- **Step accumulation.**  If `g (n+1) - g n ≤ β` for every `n` strictly inside
`(a, b)`, then `g q - g p ≤ (q - p) · β` for `a < p ≤ q ≤ b`. -/
lemma step_accum {g : ℕ → ℝ} {a b : ℕ} {β : ℝ}
    (hstep : ∀ n, a < n → n < b → g (n + 1) - g n ≤ β)
    (p : ℕ) (hp : a < p) :
    ∀ q, p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * β := by
  intro q hpq
  induction q, hpq using Nat.le_induction with
  | base => intro _; simp
  | succ q hpq ih =>
      intro hqb
      have h1 := ih (by omega)
      have h2 := hstep q (by omega) (by omega)
      have hexp : ((q + 1 : ℕ) : ℝ) - p = ((q : ℝ) - p) + 1 := by push_cast; ring
      rw [hexp, add_mul, one_mul]
      linarith

/-- **The fibre-is-an-interval lemma (the sub-obstacle).**  For a `g` strictly
monotone on `(a, b]` and reals `u ≤ v` (or any `u v`), the filter of `Ioc a b`
by the monotone predicate `u ≤ g n ∧ g n ≤ v` is a `Finset.Ioc a' b'` with
`a ≤ a'` and `b' ≤ b` (empty when `b' ≤ a'`). -/
lemma fibre_is_interval {g : ℕ → ℝ} {a b : ℕ}
    (hmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q) (u v : ℝ) :
    ∃ a' b' : ℕ, a ≤ a' ∧ b' ≤ b ∧
      (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) = Finset.Ioc a' b' := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · exact ⟨a, 0, le_refl a, Nat.zero_le b, by rw [he, Finset.Ioc_eq_empty (by omega)]⟩
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    refine ⟨n0 - 1, n1, by omega, hb1, ?_⟩
    ext x
    simp only [Finset.mem_Ioc]
    constructor
    · intro hx
      have hx0 : n0 ≤ x := Finset.min'_le T x hx
      have hx1 : x ≤ n1 := Finset.le_max' T x hx
      omega
    · rintro ⟨hlt, hle⟩
      have hx0 : n0 ≤ x := by omega
      have hxa : a < x := by omega
      have hxb : x ≤ b := le_trans hle hb1
      have hgx_lb : u ≤ g x := by
        rcases eq_or_lt_of_le hx0 with h | h
        · rw [← h]; exact hn0lb
        · exact le_trans hn0lb (le_of_lt (hmono n0 x ha0 h hxb))
      have hgx_ub : g x ≤ v := by
        rcases eq_or_lt_of_le hle with h | h
        · rw [h]; exact hn1ub
        · exact le_trans (le_of_lt (hmono x n1 hxa h hb1)) hn1ub
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxa, hxb⟩, hgx_lb, hgx_ub⟩

/-- **Window count.**  If `g` steps up by `≥ lam > 0` (encoded via the lower
accumulation `hacc`), a window `[u, u+w)` of `g`-values holds at most
`w / lam + 1` indices in `Ioc a b`. -/
lemma count_window {g : ℕ → ℝ} {a b : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hacc : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p)
    (u w : ℝ) (hw : 0 ≤ w) :
    (((Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w)).card : ℝ)
      ≤ w / lam + 1 := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ w / lam := div_nonneg hw (le_of_lt hlam)
    linarith
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    have hn01 : n0 ≤ n1 := T.min'_le_max' hne
    have hsub : T ⊆ Finset.Icc n0 n1 := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le T x hx, Finset.le_max' T x hx⟩
    have hcard : T.card ≤ (Finset.Icc n0 n1).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcardR : (T.card : ℝ) ≤ (n1 : ℝ) - n0 + 1 := by
      calc (T.card : ℝ) ≤ ((n1 + 1 - n0 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (n1 : ℝ) - n0 + 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hspread : ((n1 : ℝ) - n0) * lam ≤ g n1 - g n0 := hacc n0 n1 ha0 hn01 hb1
    have hgdiff : g n1 - g n0 < w := by linarith
    have hn1n0 : (n1 : ℝ) - n0 ≤ w / lam := by
      rw [le_div_iff₀ hlam]; linarith
    linarith

/-- **van der Corput's second-derivative test (Milestone 2).**

With `g n := f (n+1) - f n`, if the second differences satisfy
`lam ≤ g (n+1) - g n ≤ c · lam` for all `a < n < b` (`0 < lam`, `1 ≤ c`), then
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · (b - a) · √lam + 1 / √lam)`.

The absolute constant is `C' = 8` (the recorded arithmetic advertised `5` using
a step that is false in general; see the header). -/
theorem vdC_second_derivative {f : ℕ → ℝ} {a b : ℕ} {lam c : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (h2nd_lb : ∀ n, a < n → n < b →
        lam ≤ (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n))
    (h2nd_ub : ∀ n, a < n → n < b →
        (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
      ≤ 8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  set g : ℕ → ℝ := fun n => f (n + 1) - f n with hgdef
  set δ := Real.sqrt lam with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr hlam
  have hne : δ ≠ 0 := ne_of_gt hδpos
  -- step bounds in terms of g
  have hstep_lb : ∀ n, a < n → n < b → lam ≤ g (n + 1) - g n := by
    intro n h1 h2; have := h2nd_lb n h1 h2; simpa only [hgdef] using this
  have hstep_ub : ∀ n, a < n → n < b → g (n + 1) - g n ≤ c * lam := by
    intro n h1 h2; have := h2nd_ub n h1 h2; simpa only [hgdef] using this
  -- accumulations
  have hacc_hi : ∀ p q, a < p → p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * (c * lam) := by
    intro p q hp hpq hqb; exact step_accum hstep_ub p hp q hpq hqb
  have hacc_lo : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p := by
    intro p q hp hpq hqb
    have hstep' : ∀ n, a < n → n < b → (fun m => -g m) (n + 1) - (fun m => -g m) n ≤ -lam := by
      intro n hn1 hn2; dsimp only; linarith [hstep_lb n hn1 hn2]
    have key : -g q - -g p ≤ ((q : ℝ) - p) * (-lam) :=
      step_accum (g := fun m => -g m) hstep' p hp q hpq hqb
    rw [mul_neg] at key; linarith
  have hstrictmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q := by
    intro p q hp hpq hqb
    have h := hacc_lo p q hp (le_of_lt hpq) hqb
    have hpos : (0 : ℝ) < ((q : ℝ) - p) * lam := by
      apply mul_pos _ hlam
      have : (p : ℝ) < q := by exact_mod_cast hpq
      linarith
    linarith
  by_cases hsmall : lam ≤ 1 / 4
  · -- ═══ main case: lam ≤ 1/4 (δ ≤ 1/2) ═══
    have hδhalf : δ ≤ 1 / 2 := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hsmall
    have hδsq : lam = δ ^ 2 := by rw [hδdef]; exact (Real.sq_sqrt (le_of_lt hlam)).symm
    have hδlam : δ / lam = 1 / δ := by rw [hδsq, sq]; field_simp
    rcases eq_or_lt_of_le hab with hEq | haltb
    · -- empty: a = b
      have hEq2 : b = a := hEq.symm
      subst hEq2
      rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      simp only [sub_self, mul_zero, zero_mul, zero_add]
      positivity
    · -- a < b
      have hLpos : (0 : ℝ) < (b : ℝ) - a := by
        have : (a : ℝ) < b := by exact_mod_cast haltb
        linarith
      have hLnn : (0 : ℝ) ≤ (b : ℝ) - a := le_of_lt hLpos
      set φ : ℕ → ℤ := fun n => ⌊g n⌋ with hφdef
      set K := (Finset.Ioc a b).image φ with hKdef
      have hmaps : ∀ n ∈ Finset.Ioc a b, φ n ∈ K := fun n hn => Finset.mem_image_of_mem φ hn
      -- STEP 1: triangle over fibres
      have hStep1 : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => eK (f n))]
        exact norm_sum_le _ _
      -- PER-FIBRE bound
      have hfibre : ∀ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ ≤ 3 / δ + 2 := by
        intro k _
        set Fk := (Finset.Ioc a b).filter (fun n => φ n = k) with hFkdef
        set Gk := (Finset.Ioc a b).filter
          (fun n => (k : ℝ) + δ ≤ g n ∧ g n ≤ (k : ℝ) + 1 - δ) with hGkdef
        have hGsub : Gk ⊆ Fk := by
          intro n hn
          rw [hGkdef, Finset.mem_filter] at hn
          obtain ⟨hnIoc, hlb, hub⟩ := hn
          rw [hFkdef, Finset.mem_filter]
          refine ⟨hnIoc, ?_⟩
          rw [hφdef]
          exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
        have hsplit : ∑ n ∈ Fk, eK (f n)
            = (∑ n ∈ Fk \ Gk, eK (f n)) + (∑ n ∈ Gk, eK (f n)) :=
          (Finset.sum_sdiff hGsub).symm
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        -- good part via kusmin
        have hgood : ‖∑ n ∈ Gk, eK (f n)‖ ≤ 1 / δ := by
          obtain ⟨a', b', ha', hb', hGeq⟩ :=
            fibre_is_interval hstrictmono ((k : ℝ) + δ) ((k : ℝ) + 1 - δ)
          have hGkeq : Gk = Finset.Ioc a' b' := by rw [hGkdef]; exact hGeq
          rw [hGkeq]
          apply kusmin_landau hδpos hδhalf
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.1
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.2
          · intro n hn1 hn2
            exact le_of_lt (hstrictmono n (n + 1) (by omega) (by omega) (by omega))
        -- bad part via count_window
        have hbad : ‖∑ n ∈ Fk \ Gk, eK (f n)‖ ≤ 2 / δ + 2 := by
          have hcardbound : ((Fk \ Gk).card : ℝ) ≤ 2 / δ + 2 := by
            set Left := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) ≤ g n ∧ g n < (k : ℝ) + δ) with hLeftdef
            set Right := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) + 1 - δ ≤ g n ∧ g n < (k : ℝ) + 1 - δ + δ) with hRightdef
            have hsubLR : Fk \ Gk ⊆ Left ∪ Right := by
              intro n hn
              rw [Finset.mem_sdiff] at hn
              obtain ⟨hnFk, hnGk⟩ := hn
              rw [hFkdef, Finset.mem_filter] at hnFk
              obtain ⟨hnIoc, hφk⟩ := hnFk
              rw [hφdef] at hφk
              obtain ⟨hgk1, hgk2⟩ := Int.floor_eq_iff.mp hφk
              rw [hGkdef, Finset.mem_filter, not_and] at hnGk
              have hnotpred := hnGk hnIoc
              rw [not_and_or] at hnotpred
              rw [Finset.mem_union]
              rcases hnotpred with h | h
              · left
                rw [hLeftdef, Finset.mem_filter]
                rw [not_le] at h
                exact ⟨hnIoc, hgk1, h⟩
              · right
                rw [hRightdef, Finset.mem_filter]
                rw [not_le] at h
                refine ⟨hnIoc, le_of_lt h, ?_⟩
                have he : (k : ℝ) + 1 - δ + δ = (k : ℝ) + 1 := by ring
                rw [he]; exact hgk2
            have hcLR : (Fk \ Gk).card ≤ Left.card + Right.card :=
              le_trans (Finset.card_le_card hsubLR) (Finset.card_union_le Left Right)
            have hLeftC : (Left.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo (k : ℝ) δ (le_of_lt hδpos)
            have hRightC : (Right.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo ((k : ℝ) + 1 - δ) δ (le_of_lt hδpos)
            rw [hδlam] at hLeftC hRightC
            have hcast : ((Fk \ Gk).card : ℝ) ≤ (Left.card : ℝ) + (Right.card : ℝ) := by
              exact_mod_cast hcLR
            have hbridge : (2 : ℝ) / δ = 1 / δ + 1 / δ := by ring
            linarith [hcast, hLeftC, hRightC, hbridge]
          calc ‖∑ n ∈ Fk \ Gk, eK (f n)‖
              ≤ ∑ n ∈ Fk \ Gk, ‖eK (f n)‖ := norm_sum_le _ _
            _ = ∑ n ∈ Fk \ Gk, (1 : ℝ) := by simp [eK_norm]
            _ = ((Fk \ Gk).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ 2 / δ + 2 := hcardbound
        have hbridge : (3 : ℝ) / δ = 2 / δ + 1 / δ := by ring
        linarith [hgood, hbad, hbridge]
      -- STEP 2: sum the fibre bounds
      have hStep2 : ∑ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
          ≤ (K.card : ℝ) * (3 / δ + 2) := by
        calc ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
            ≤ ∑ _k ∈ K, (3 / δ + 2) := Finset.sum_le_sum hfibre
          _ = (K.card : ℝ) * (3 / δ + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      -- fibre count K ≤ c·lam·L + 2
      have hKcard : (K.card : ℝ) ≤ c * lam * ((b : ℝ) - a) + 2 := by
        have hφmono : ∀ n ∈ Finset.Ioc a b, φ (a + 1) ≤ φ n ∧ φ n ≤ φ b := by
          intro n hn
          obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
          simp only [hφdef]
          refine ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩
          · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hna) with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono (a + 1) n (by omega) h hnb)
          · rcases eq_or_lt_of_le hnb with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono n b hna h (le_refl b))
        have hKsub : K ⊆ Finset.Icc (φ (a + 1)) (φ b) := by
          intro z hz
          rw [hKdef, Finset.mem_image] at hz
          obtain ⟨n, hn, rfl⟩ := hz
          rw [Finset.mem_Icc]
          exact hφmono n hn
        have hmemA : a + 1 ∈ Finset.Ioc a b :=
          Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        have hφab : φ (a + 1) ≤ φ b := (hφmono (a + 1) hmemA).2
        have hcardZ : (K.card : ℤ) ≤ φ b + 1 - φ (a + 1) := by
          have h1 : K.card ≤ (Finset.Icc (φ (a + 1)) (φ b)).card := Finset.card_le_card hKsub
          have h2 : ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) = φ b + 1 - φ (a + 1) := by
            rw [Int.card_Icc, Int.toNat_of_nonneg (show (0 : ℤ) ≤ φ b + 1 - φ (a + 1) by omega)]
          calc (K.card : ℤ) ≤ ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) := by exact_mod_cast h1
            _ = φ b + 1 - φ (a + 1) := h2
        have hKR : (K.card : ℝ) ≤ (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by
          calc (K.card : ℝ) = ((K.card : ℤ) : ℝ) := by push_cast; ring
            _ ≤ ((φ b + 1 - φ (a + 1) : ℤ) : ℝ) := by exact_mod_cast hcardZ
            _ = (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by push_cast; ring
        have hfb : (φ b : ℝ) ≤ g b := by rw [hφdef]; exact Int.floor_le (g b)
        have hfa : g (a + 1) - 1 < (φ (a + 1) : ℝ) := by
          rw [hφdef]; exact Int.sub_one_lt_floor (g (a + 1))
        have hgub := hacc_hi (a + 1) b (by omega) (by omega) (le_refl b)
        have hclam : (0 : ℝ) ≤ c * lam := mul_nonneg (by linarith) (le_of_lt hlam)
        have hgub2 : g b - g (a + 1) ≤ c * lam * ((b : ℝ) - a) := by
          have hstep : ((b : ℝ) - (a + 1)) * (c * lam) ≤ c * lam * ((b : ℝ) - a) := by
            linarith only [hclam]
          push_cast at hgub
          linarith [hgub, hstep]
        linarith [hKR, hfb, hfa, hgub2]
      -- FINAL arithmetic
      have hfinal : (K.card : ℝ) * (3 / δ + 2) ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by
        have hcleared : (c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)
            ≤ 8 * (c * ((b : ℝ) - a) * δ) * δ + 8 := by
          rw [hδsq]
          linarith only
              [hδhalf, mul_nonneg
              (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hLnn) (sq_nonneg δ))
              (by linarith : (0 : ℝ) ≤ 5 - 2 * δ)]
        have e1 : (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2)
            = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := by field_simp
        have e2 : 8 * (c * ((b : ℝ) - a) * δ + 1 / δ)
            = (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ := by field_simp
        calc (K.card : ℝ) * (3 / δ + 2)
            ≤ (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2) :=
              mul_le_mul_of_nonneg_right hKcard (by positivity)
          _ = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := e1
          _ ≤ (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ :=
              (div_le_div_iff_of_pos_right hδpos).mpr hcleared
          _ = 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := e2.symm
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := hStep1
        _ ≤ (K.card : ℝ) * (3 / δ + 2) := hStep2
        _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := hfinal
  · -- ═══ trivial case: lam > 1/4 (δ > 1/2) ═══
    have hbig : (1 : ℝ) / 4 < lam := not_le.mp hsmall
    have hδhalf : (1 : ℝ) / 2 < δ := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hbig
    have hL : (0 : ℝ) ≤ (b : ℝ) - a := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have hnorm : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := by
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ n ∈ Finset.Ioc a b, ‖eK (f n)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.Ioc a b, (1 : ℝ) := by simp [eK_norm]
        _ = ((Finset.Ioc a b).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (b : ℝ) - a := by rw [Nat.card_Ioc, Nat.cast_sub hab]
    have hcδ : (1 : ℝ) / 2 ≤ c * δ := by
      linarith only [hδhalf, mul_nonneg (sub_nonneg.mpr hc) (le_of_lt hδpos)]
    have hbound : (b : ℝ) - a ≤ 8 * (c * ((b : ℝ) - a) * δ) := by
      linarith only [hL, mul_nonneg hL (by linarith [hcδ] : (0 : ℝ) ≤ c * δ - 1 / 2)]
    have h1δ : (0 : ℝ) ≤ 1 / δ := by positivity
    calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := hnorm
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ) := hbound
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by linarith

end Salt.ExpSum
end

section
namespace Erdos375Phase

/-- 项目指数和的两项倒数之差可写作一个倒数相位。 -/
theorem phase_eq {h t m a b : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) :
    h * (t / (m*a) - t / (m*b)) = (h*t*(b-a)/(a*b)) / m := by
  field_simp

noncomputable def diff₂ (A m : ℝ) : ℝ := (A / (m + 2) - A / (m + 1)) - (A / (m + 1) - A/m)

theorem reciprocal_diff₂ {m : ℝ} (hm : 0 < m) (A : ℝ) :
    diff₂ A m = 2*A/(m*(m+1)*(m+2)) := by
  unfold diff₂
  have h1 : 0 < m + 1 := by linarith
  have h2 : 0 < m + 2 := by linarith
  field_simp
  ring

/-- 在指数和的整个区间上，二阶差都落在 λ 与 8N³λ 之间。 -/
theorem diff₂_bounds {N m A : ℝ} (hN : 2 ≤ N) (hA : 0 ≤ A)
    (hlo : N^251 ≤ m) (hhi : m ≤ N^252) :
    let lam := A / (4 * N^756)
    lam ≤ diff₂ A m ∧ diff₂ A m ≤ (8*N^3)*lam := by
  dsimp only
  have hpos : 0 < N := by linarith
  have hn : 1 ≤ N := by linarith
  have hm : 0 < m := lt_of_lt_of_le (pow_pos hpos _) hlo
  have h252 : 2 ≤ N^252 := le_trans hN (by simpa using pow_le_pow_right₀ hn (show 1 ≤ 252 by decide))
  have hden : 0 < m*(m+1)*(m+2) := by positivity
  have hu : m*(m+1)*(m+2) ≤ 8*N^756 := by
    calc
      _ ≤ (2*N^252)*(2*N^252)*(2*N^252) := by
        gcongr <;> linarith
      _ = _ := by ring
  have hl : N^753 ≤ m*(m+1)*(m+2) := by
    calc
      _ = (N^251)*(N^251)*(N^251) := by ring
      _ ≤ _ := by gcongr <;> linarith
  rw [reciprocal_diff₂ hm]
  constructor
  · apply (div_le_div_iff₀ (by positivity) hden).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hu hA]
  · have e : (8*N^3)*(A/(4*N^756)) = 2*A/N^753 := by
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hl

theorem amplitude_bounds {N h t a b : ℝ} (hN : 2 ≤ N)
    (ht₀ : N^1000 ≤ t) (ht₁ : t ≤ N^1001) (hh₀ : 1 ≤ h) (hh₁ : h ≤ N^20)
    (ha : N^251 ≤ a) (hb : b ≤ N^252) (hd₀ : 1 ≤ b-a) (hd₁ : b-a ≤ N^40) :
    N^496 ≤ h*t*(b-a)/(a*b) ∧ h*t*(b-a)/(a*b) ≤ N^559 := by
  have hpos : 0 < N := by linarith
  have hap : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hbp : 0 < b := by linarith
  have hab : a ≤ b := by linarith
  have ht : 0 ≤ t := le_trans (by positivity) ht₀
  have hh : 0 ≤ h := by linarith
  have hht : 0 ≤ h*t := mul_nonneg hh ht
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ N^496 * (N^252*N^252) := by gcongr <;> linarith
      _ = 1 * N^1000 * 1 := by ring
      _ ≤ _ := by gcongr
  · apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ N^20 * N^1001 * N^40 := by gcongr
      _ = N^559 * (N^251 * N^251) := by ring
      _ ≤ _ := by gcongr <;> linarith

/-- 将离散二阶导数检验的显式常数收进项目要求的 16 N^188。 -/
theorem vdC_rhs_bound {N A : ℝ} (hN : 2 ≤ N) (hl : N^496 ≤ A) (hu : A ≤ N^559) :
    let lam := A/(4*N^756)
    8*((8*N^3)*(N^252-N^251)*Real.sqrt lam + 1/Real.sqrt lam) ≤ 16*N^188 := by
  dsimp only
  have hn : 0 < N := by linarith
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hl
  let s := Real.sqrt (A/(4*N^756))
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s^2*(4*N^756) = A := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hsU : s * N^98 ≤ 1 := by
    have h559 : N^559 ≤ N^560 := pow_le_pow_right₀ (by linarith) (by decide)
    have hmul : (s*N^98)^2 * N^560 ≤ 1^2 * N^560 := by
      calc
        _ = A/4 := by rw [← hs2]; ring
        _ ≤ _ := by linarith
    have hsq := (mul_le_mul_iff_left₀ (by positivity : 0 < N^560)).mp hmul
    nlinarith only [hsq, sq_nonneg (s*N^98-1)]
  have hsL : 1 ≤ 2 * s * N^130 := by
    have hmul : 1^2 * N^496 ≤ (2*s*N^130)^2 * N^496 := by
      calc
        _ ≤ A := by simpa using hl
        _ = _ := by rw [← hs2]; ring
    have hsq := (mul_le_mul_iff_left₀ (by positivity : 0 < N^496)).mp hmul
    exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity) hsq
  have hmass : (8*N^3)*(N^252-N^251)*s ≤ 8*N^157 := by
    calc
      _ ≤ (8*N^3)*N^252*s := by gcongr; linarith [show 0 ≤ N^251 by positivity]
      _ = (8*N^157)*(s*N^98) := by ring
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hsU (by positivity : 0 ≤ 8*N^157)
  have ht1 : 8*N^157 ≤ N^188 := by
    have hc : (2:ℝ)^3 ≤ N^3 := by gcongr
    calc
      _ ≤ N^3*N^157 := by gcongr; norm_num at hc; exact hc
      _ = N^160 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  have ht2 : 1/s ≤ N^188 := by
    calc
      _ ≤ 2*N^130 := (div_le_iff₀ hs).mpr (by linarith only [hsL, show 2*s*N^130 = 2*N^130*s by ring])
      _ ≤ N*N^130 := by gcongr
      _ = N^131 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  change 8 * (_ * _ * s + 1/s) ≤ _
  linarith

noncomputable def character (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- 离散二阶差检验推出问题所需的指数和估计。 -/
theorem reciprocal_exponential_sum
    (N t h : ℕ) (hN : 2 ≤ N) (ht₀ : N^1000 ≤ t) (ht₁ : t ≤ N^1001)
    (hh₀ : 1 ≤ h) (hh₁ : h ≤ N^20)
    (a : ℕ) (ha : a ∈ Finset.Ioc (N^251) (N^252))
    (b : ℕ) (hb : b ∈ Finset.Ioc (N^251) (N^252)) (hab : a < b) (hd : b-a ≤ N^40) :
    ‖∑ p ∈ Finset.Ioc (N^251) (N^252), character
      ((h:ℝ)*((t:ℝ)/((p*a:ℕ):ℝ) - (t:ℝ)/((p*b:ℕ):ℝ)))‖ ≤ 16*(N:ℝ)^188 := by
  obtain ⟨ha₀, ha₁⟩ := Finset.mem_Ioc.mp ha
  obtain ⟨hb₀, hb₁⟩ := Finset.mem_Ioc.mp hb
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hn' : 0 < (N:ℝ) := by linarith
  let A : ℝ := h*t*((b:ℝ)-a)/((a:ℝ)*b)
  let lam := A / (4*(N:ℝ)^756)
  let f (m : ℕ) := A/(m:ℝ)
  have bounds : (N:ℝ)^496 ≤ A ∧ A ≤ (N:ℝ)^559 := by
    apply amplitude_bounds hn
    · exact_mod_cast ht₀
    · exact_mod_cast ht₁
    · exact_mod_cast hh₀
    · exact_mod_cast hh₁
    · exact_mod_cast ha₀.le
    · exact_mod_cast hb₁
    · have : (a:ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
      linarith
    · rw [← Nat.cast_sub hab.le]; exact_mod_cast hd
  have hA : 0 < A := lt_of_lt_of_le (by positivity) bounds.1
  have hl : 0 < lam := div_pos hA (by positivity)
  have dc (m : ℕ) (hm₀ : N^251 < m) (hm₁ : m < N^252) :
      lam ≤ (f (m+1+1)-f (m+1))-(f (m+1)-f m) ∧
      (f (m+1+1)-f (m+1))-(f (m+1)-f m) ≤ (8*(N:ℝ)^3)*lam := by
    have hdif := diff₂_bounds (m := (m:ℝ)) hn hA.le (by exact_mod_cast hm₀.le)
      (by exact_mod_cast hm₁.le)
    simpa [f, lam, diff₂, add_assoc] using hdif
  have hc : (1:ℝ) ≤ 8*(N:ℝ)^3 := by
    have : (1:ℝ) ≤ (N:ℝ)^3 := one_le_pow₀ (by linarith)
    linarith
  have hv := Salt.ExpSum.vdC_second_derivative (f := f) (a := N^251) (b := N^252)
    (pow_le_pow_right₀ (by omega : 1 ≤ N) (by decide)) hl hc
    (fun m h₀ h₁ => (dc m h₀ h₁).1) (fun m h₀ h₁ => (dc m h₀ h₁).2)
  have hsum : (∑ p ∈ Finset.Ioc (N^251) (N^252), character
      ((h:ℝ)*((t:ℝ)/((p*a:ℕ):ℝ) - (t:ℝ)/((p*b:ℕ):ℝ)))) =
      ∑ p ∈ Finset.Ioc (N^251) (N^252), character (f p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (Finset.mem_Ioc.mp hp).1
    have hp₀ : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    simp only [Nat.cast_mul]
    exact congrArg character (phase_eq hp₀ (by exact_mod_cast (by omega : 0 < a))
      (by exact_mod_cast (by omega : 0 < b)))
  rw [hsum]
  push_cast at hv
  exact hv.trans (vdC_rhs_bound hn bounds.1 bounds.2)

end Erdos375Phase
end

section
open Finset
open scoped ComplexConjugate

namespace Erdos375Attempt

/-- 将行和的平方展开为各列之间的相关和，从而利用在整段上的抵消。 -/
theorem block_correlation_bound (P J B : Finset ℕ) (hPJ : P ⊆ J)
    (z : ℕ → ℕ → ℂ) (U : ℝ) (hU : 0 ≤ U)
    (hz : ∀ p ∈ J, ∀ a ∈ B, ‖z p a‖ = 1)
    (hc : ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
      ‖∑ p ∈ J, z p a * conj (z p b)‖ ≤ U) :
    ‖∑ p ∈ P, ∑ a ∈ B, z p a‖ ^ 2 ≤
      (P.card : ℝ) * ((B.card : ℝ) * J.card + (B.card : ℝ)^2 * U) := by
  classical
  let r (p : ℕ) := ∑ a ∈ B, z p a
  let T (a b : ℕ) := (∑ p ∈ J, z p a * conj (z p b)).re
  have hexpand (p : ℕ) :
      ‖r p‖^2 = ∑ a ∈ B, ∑ b ∈ B, (z p a * conj (z p b)).re := by
    calc
      ‖r p‖^2 = (r p * conj (r p)).re := by
        rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      _ = _ := by
        simp [r, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
        rw [Finset.sum_comm]
  have hperm : (∑ p ∈ J, ‖r p‖^2) = ∑ a ∈ B, ∑ b ∈ B, T a b := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    simp [T, Complex.re_sum]
  have hb (a : ℕ) (ha : a ∈ B) :
      (∑ b ∈ B, T a b) ≤ (J.card : ℝ) + B.card * U := by
    calc
      _ ≤ ∑ b ∈ B, ((if b = a then (J.card : ℝ) else 0) + U) := by
        apply Finset.sum_le_sum
        intro b hb
        by_cases h : b = a
        · subst b
          have hdiag : T a a = J.card := by
            simp only [T, Complex.re_sum, Complex.mul_conj', ← Complex.ofReal_pow,
              Complex.ofReal_re]
            calc
              _ = ∑ _p ∈ J, (1:ℝ) := Finset.sum_congr rfl fun p hp => by rw [hz p hp a ha]; norm_num
              _ = _ := by simp
          simpa [hdiag] using hU
        · simpa only [h, if_false, zero_add, T] using (Complex.re_le_norm _).trans (hc a ha b hb (Ne.symm h))
      _ = _ := by simp [Finset.sum_add_distrib, ha]
  have htotal : ∑ p ∈ J, ‖r p‖ ^ 2 ≤ (B.card : ℝ) * J.card + (B.card : ℝ)^2 * U := by
    rw [hperm]
    refine (Finset.sum_le_sum hb).trans_eq ?_
    simp
    ring
  have hcs : (∑ p ∈ P, ‖r p‖)^2 ≤ (P.card : ℝ) * ∑ p ∈ P, ‖r p‖^2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    _ ≤ (∑ p ∈ P, ‖r p‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := hcs.trans (mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg hPJ (fun _ _ _ => sq_nonneg _)).trans htotal)
      (by positivity))

/-- 将第二个变量按长为 N^40 的连续块分组，再对各块应用相关和估计。 -/
theorem double_sum_bound (N : ℕ) (hN : 2 ≤ N) (J P : Finset ℕ)
    (hPJ : P ⊆ J) (hJ : J ⊆ Finset.Icc 1 (N^252))
    (z : ℕ → ℕ → ℂ) (hz : ∀ p ∈ J, ∀ a ∈ P, ‖z p a‖ = 1)
    (hc : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → a-b ≤ N^40 → b-a ≤ N^40 →
      ‖∑ p ∈ J, z p a * conj (z p b)‖ ≤ 16*(N:ℝ)^188) :
    ‖∑ p ∈ P, ∑ a ∈ P, z p a‖ ≤ 10*(N:ℝ)^484 := by
  classical
  let L := N^40
  let D := N^212
  let B (d : ℕ) := P.filter (fun a => a/L = d)
  have hl : 0 < L := pow_pos (by omega : 0 < N) _
  have hd : 0 < D := pow_pos (by omega : 0 < N) _
  have hprod : D*L = N^252 := (pow_add N 212 40).symm
  have hmap : ∀ a ∈ P, a/L ∈ range (D+1) := by
    intro a ha
    have ha' := (mem_Icc.mp (hJ (hPJ ha))).2
    rw [mem_range, Nat.div_lt_iff_lt_mul hl, Nat.add_mul, one_mul, hprod]
    omega
  have hband (d a : ℕ) (ha : a ∈ B d) : d*L ≤ a ∧ a < d*L + L := by
    have he := (mem_filter.mp ha).2
    have hlo := Nat.div_mul_le_self a L
    have hhi := (Nat.div_lt_iff_lt_mul hl).mp (Nat.lt_succ_self (a/L))
    rw [Nat.succ_mul, he] at hhi
    simpa [he] using And.intro hlo hhi
  have hjn : J.card ≤ N^252 := by simpa using card_le_card hJ
  have hpow : (N:ℝ)^268 ≤ (N:ℝ)^292 :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ N by omega)) (by decide : 268 ≤ 292)
  have hblock (d : ℕ) : ‖∑ p ∈ P, ∑ a ∈ B d, z p a‖ ≤ 5*(N:ℝ)^272 := by
    have hbc : (B d).card ≤ L := by
      have hsub : B d ⊆ Ico (d*L) (d*L+L) := fun a ha => mem_Ico.mpr (hband d a ha)
      simpa using card_le_card hsub
    have hb := block_correlation_bound P J (B d) hPJ z (16*(N:ℝ)^188) (by positivity)
      (fun p hp a ha => hz p hp a (mem_filter.mp ha).1)
      (fun a ha b hb hab => hc a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab
        (by have := hband d a ha; have := hband d b hb; change a-b ≤ L; omega)
        (by have := hband d a ha; have := hband d b hb; change b-a ≤ L; omega))
    have hpr : (P.card:ℝ) ≤ (N:ℝ)^252 := by exact_mod_cast (card_le_card hPJ).trans hjn
    have hjr : (J.card:ℝ) ≤ (N:ℝ)^252 := by exact_mod_cast hjn
    have hbr : ((B d).card:ℝ) ≤ (N:ℝ)^40 := by exact_mod_cast hbc
    have hlarge : ‖∑ p ∈ P, ∑ a ∈ B d, z p a‖^2 ≤
        (N:ℝ)^252 * ((N:ℝ)^40 * (N:ℝ)^252 + ((N:ℝ)^40)^2 * (16*(N:ℝ)^188)) := by
      refine hb.trans ?_
      gcongr
    have harr : (N:ℝ)^252 * ((N:ℝ)^40 * (N:ℝ)^252 + ((N:ℝ)^40)^2 * (16*(N:ℝ)^188))
        ≤ (5*(N:ℝ)^272)^2 := by
      calc
        _ = (N:ℝ)^252 * ((N:ℝ)^292 + 16*(N:ℝ)^268) := by ring
        _ ≤ (N:ℝ)^252 * ((N:ℝ)^292 + 16*(N:ℝ)^292) := by gcongr
        _ ≤ (5*(N:ℝ)^272)^2 := by
          calc
            _ = 17*(N:ℝ)^544 := by ring
            _ ≤ 25*(N:ℝ)^544 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = _ := by ring
    exact le_of_sq_le_sq (hlarge.trans harr) (by positivity)
  have hsum : (∑ p ∈ P, ∑ a ∈ P, z p a) =
      ∑ d ∈ range (D+1), ∑ p ∈ P, ∑ a ∈ B d, z p a := by
    rw [Finset.sum_comm (s := range (D+1))]
    apply Finset.sum_congr rfl
    intro p hp
    exact (Finset.sum_fiberwise_of_maps_to hmap (z p)).symm
  rw [hsum]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ range (D+1), 5*(N:ℝ)^272 := Finset.sum_le_sum fun d _ => hblock d
    _ = ((D:ℝ)+1)*(5*(N:ℝ)^272) := by simp
    _ ≤ ((D:ℝ)+D)*(5*(N:ℝ)^272) := by gcongr; exact_mod_cast hd
    _ = _ := by dsimp [D]; push_cast; ring

end Erdos375Attempt
end

section
/- 从有序列对的指数和界推出短区间双素数和界。 -/

open Finset
open scoped ComplexConjugate

namespace Erdos375Attempt

private noncomputable def character (s : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)

private theorem character_sub (x y : ℝ) :
    character x * conj (character y) = character (x-y) := by
  unfold character
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  norm_num
  rw [show (starRingEnd ℂ) 2 = 2 by simpa only [one_add_one_eq_two] using
    (map_ofNat (starRingEnd ℂ) 2)]
  ring

private theorem correlation_symm (J : Finset ℕ) (z : ℕ → ℕ → ℂ) (a b : ℕ) :
    ‖∑ p ∈ J, z p a * conj (z p b)‖ = ‖∑ p ∈ J, z p b * conj (z p a)‖ := by
  conv_rhs => rw [← Complex.norm_conj]
  simp [mul_comm]

/-- 项目分解 R1.H1.R1.H2.R1 的第二个子命题。 -/
theorem bilinear_prime_bound : ∀ N t h : ℕ, 2 ≤ N → N^1000 ≤ t → t ≤ N^1001 →
    1 ≤ h → h ≤ N^20 →
    let J := Ioc (N^251) (N^252)
    let u (p q : ℕ) := (t:ℝ)/((p*q:ℕ):ℝ)
    let e (v : ℝ) := Complex.exp (((2*Real.pi*v : ℝ) : ℂ)*Complex.I)
    let P := J.filter Nat.Prime
    (∀ a ∈ J, ∀ b ∈ J, a < b → b-a ≤ N^40 →
      ‖∑ p ∈ J, e ((h:ℝ)*(u p a - u p b))‖ ≤ 16*(N:ℝ)^188) →
      ‖∑ w ∈ P ×ˢ P, e ((h:ℝ)*u w.1 w.2)‖ ≤ 10*(N:ℝ)^484 := by
  intro N t h hN _ _ _ _ J u e P H
  let z (p a : ℕ) := character ((h:ℝ)*u p a)
  have hPJ : P ⊆ J := filter_subset _ _
  have ordered (a b : ℕ) (ha : a ∈ P) (hb : b ∈ P)
      (hab : a < b) (hd : b-a ≤ N^40) :
      ‖∑ p ∈ J, z p a * conj (z p b)‖ ≤ 16*(N:ℝ)^188 := by
    simpa only [z, character_sub, ← mul_sub] using
      (show ‖∑ p ∈ J, character ((h:ℝ)*(u p a - u p b))‖ ≤ _ from
        H a (hPJ ha) b (hPJ hb) hab hd)
  rw [sum_product]
  apply double_sum_bound N hN J P hPJ _ z
  · intro p hp a ha
    simp [z, character, Complex.norm_exp]
  · intro a ha b hb hne hab hba
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ordered a b ha hb hlt hba
    · rw [correlation_symm J z a b]
      exact ordered b a hb ha hgt hab
  · intro p hp
    exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hp).1; omega, (mem_Ioc.mp hp).2⟩

end Erdos375Attempt
end

section
namespace Erdos375Attempt

/-- 将两个本地证明直接与公开归约中的原始子命题比对。 -/
theorem certified_off_diagonal :
    OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.H1 :=
  Erdos375Phase.reciprocal_exponential_sum

theorem certified_bilinear :
    OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.H2 :=
  bilinear_prime_bound

/-- 剩下的傅里叶截断估计一旦成立，三层公开归约就给出原题所要求的结论。 -/
theorem bounded_gap_of_fourier_truncation
    (hf : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.H3) :
    type_of% @Erdos375.erdos_375.variants.bounded_gap :=
  OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.main
    (OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1.main
      Erdos375Upstream.Reciprocal
      (OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.main
        certified_off_diagonal certified_bilinear hf))
    Erdos375Upstream.PrimeDensity

end Erdos375Attempt
end

section
/- 以二次 Bernoulli 多项式的有限差分控制商的锯齿误差。 -/

open Finset Erdos375Envelope

namespace Erdos375Attempt

private theorem sum_sandwich {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (d L : ℝ) (hd : 0 < d) (hd' : d ≤ 1)
    (bound : ∀ v : ℝ, |∑ i ∈ S, B (x i + v)| ≤ L) :
    |∑ i ∈ S, (1/2 - Int.fract (x i))| ≤ L/d + S.card*d/2 := by
  have h0 := abs_le.mp (bound 0)
  simp only [add_zero] at h0
  have h₁ := (abs_le.mp (bound d)).1
  have h₂ := (abs_le.mp (bound (-d))).1
  have hp := sum_le_sum (s := S) (fun i _ => (sandwich (x i) d hd hd').1)
  have hm := sum_le_sum (s := S) (fun i _ => (sandwich (x i) d hd hd').2)
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_div, sum_const, nsmul_eq_mul] at hp hm ⊢
  rw [abs_le]
  simp only [← sub_eq_add_neg] at h₂
  have htop := h0.2
  constructor <;> field_simp [ne_of_gt hd] at hp hm ⊢ <;> nlinarith

private theorem error_budget {N C : ℕ} (hN : 2 ≤ N) (hC : C ≤ N^504) :
    ((C : ℝ)/(N:ℝ)^20 + 2*(10*(N:ℝ)^484))/(1/(N:ℝ)^7) +
      (C:ℝ)*(1/(N:ℝ)^7)/2 ≤ 1000*(N:ℝ)^498 := by
  have h1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0:ℝ) < N := by linarith
  have hc : (C:ℝ) ≤ (N:ℝ)^504 := by exact_mod_cast hC
  have eq : (((N:ℝ)^504/(N:ℝ)^20 + 2*(10*(N:ℝ)^484))/(1/(N:ℝ)^7) +
      (N:ℝ)^504*(1/(N:ℝ)^7)/2) = 21*(N:ℝ)^491 + (N:ℝ)^497/2 := by
    field_simp
    ring
  calc
    _ ≤ ((N:ℝ)^504/(N:ℝ)^20 + 2*(10*(N:ℝ)^484))/(1/(N:ℝ)^7) +
      (N:ℝ)^504*(1/(N:ℝ)^7)/2 := by gcongr
    _ = _ := eq
    _ ≤ _ := by
      linarith [pow_le_pow_right₀ h1 (show 491 ≤ 498 by decide),
        pow_le_pow_right₀ h1 (show 497 ≤ 498 by decide), show 0 ≤ (N:ℝ)^498 by positivity]

theorem certified_sawtooth :
    OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.H3 := by
  intro N t hN J P u e H
  let S := P ×ˢ P
  let x (w : ℕ × ℕ) := u w.1 w.2
  let M := 10 * (N:ℝ)^484
  let d := 1 / (N:ℝ)^7
  let L := (S.card:ℝ)/(N:ℝ)^20 + 2*M
  have hn : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn' : (0:ℝ) < N := by linarith
  have hK : 0 < N^20 := by positivity
  have hP : P.card ≤ N^252 := by
    calc
      _ ≤ J.card := card_le_card (filter_subset _ _)
      _ ≤ _ := by simp [J, Nat.card_Ioc]
  have hS : S.card ≤ N^504 := by
    simpa [S, ← pow_add] using Nat.mul_le_mul hP hP
  have bound (v : ℝ) : |∑ i ∈ S, B (x i + v)| ≤ L := by
    have hb := Erdos375Fourier.shifted_bernoulli_sum S x v (N^20) M
      (by dsimp [M]; positivity) (by
        intro h hh hle
        simpa only [e, x, mul_assoc] using H h hh hle)
      (fun w => Erdos375Bernoulli.truncation w _ hK)
    have hscale : Real.pi ^ 2 * |∑ i ∈ S, B (x i + v)| ≤ L := by
      simpa [L, B, bernoulliFun_two, ← Finset.mul_sum, abs_mul,
        abs_of_nonneg (sq_nonneg Real.pi), one_div] using hb
    have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
    exact (le_mul_of_one_le_left (abs_nonneg _) hpi).trans hscale
  have hd : 0 < d := by dsimp [d]; positivity
  have hd' : d ≤ 1 := by
    dsimp [d]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hn)
  have hs := sum_sandwich S x d L hd hd' bound
  change |∑ w ∈ S, (((t/(w.1*w.2):ℕ):ℝ) - (t:ℝ)/((w.1*w.2:ℕ):ℝ) + 1/2)| ≤ _
  simp_rw [Erdos375Fourier.centered_quotient]
  exact hs.trans (error_budget hN hS)

/-- 与上游声明同型的完整证明。 -/
theorem solution : type_of% @Erdos375.erdos_375.variants.bounded_gap :=
  bounded_gap_of_fourier_truncation certified_sawtooth

end Erdos375Attempt
end

section
theorem OMA.solution : type_of% @Erdos375.erdos_375.variants.bounded_gap :=
  Erdos375Attempt.solution
end
