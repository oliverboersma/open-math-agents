import OMAReductions.R_OeisA189286_conjecture_3_R1
import Mathlib

/-
Copyright 2026 The Formal Conjectures Authors and Yuto Nakahara.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-! Converse parity step in ihateSAS's reduction #3393 of Zhi-Wei Sun's conjecture.
The natural convolution and factorial lemmas are adapted from Yuto Nakahara
via JamesSlash (#586), github.com/YutoNakahara/oeis-a189286-lean at 259c8073. The binary digit-sum lemmas are adapted from
PastaPastaPasta (#3184) and PanPapag (#4960). Stronger full proofs
are in DomTheDeveloper's #424 and PastaPastaPasta's #3184.
Here the binomial row supplies a comparison sum for the original convolution:
its parity pattern agrees term by term after dividing out the common power of two.
Pairing symmetric terms then lifts the comparison by one more binary digit. -/

namespace OeisA189286

private def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

private def sNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

private lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

private lemma sNat_pos (n : ℕ) : 0 < sNat n :=
  Finset.sum_pos (fun k _ => Nat.mul_pos (tNat_pos k) (tNat_pos (n - k)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

private lemma denom_pos {n : ℕ} (hn : 0 < n) : 0 < (2 * n - 1) * (3 * n).choose n :=
  Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

private lemma a_eq_div_nat {n : ℕ} (hn : 0 < n) :
    a n = (sNat n : ℚ) / (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
  unfold a sNat tTerm
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp only [tNat, Nat.cast_sum, Nat.cast_mul, hsub]

private lemma tNat_mul_factorials (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
    rwa [show 6 * k - 3 * k = 3 * k by omega] at this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
    rwa [show 3 * k - k = 2 * k by omega] at this
  calc
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
            unfold tNat; ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma padicValNat_two_fac (n : ℕ) : padicValNat 2 n.factorial = n - s2 n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s2] using this

private lemma s2_le_self (n : ℕ) : s2 n ≤ n := by
  exact Nat.digit_sum_le 2 n

private lemma s2_mul_two (n : ℕ) : s2 (2 * n) = s2 n := by
  by_cases hn : n = 0
  · subst hn; simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [h1, h2]

private lemma s2_pow_two (k : ℕ) : s2 (2 ^ k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ', s2_mul_two, ih]

private lemma s2_eq_zero_iff (n : ℕ) : s2 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
    have hpos : 0 < (Nat.digits 2 n).sum := by
      have hlast : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hne
      have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
      exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_, hmem, Nat.pos_of_ne_zero hlast⟩
    unfold s2 at h
    omega
  · rintro rfl; simp [s2]

private lemma s2_eq_one_iff (n : ℕ) : s2 n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hs1
      have hn0 : n ≠ 0 := fun h => by subst h; simp [s2] at hs1
      have hdef : Nat.digits 2 n = n % 2 :: Nat.digits 2 (n / 2) :=
        Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn0)
      unfold s2 at hs1
      rw [hdef, List.sum_cons] at hs1
      by_cases hpar : n % 2 = 0
      · have hhalf : s2 (n / 2) = 1 := by unfold s2; omega
        obtain ⟨k, hk⟩ := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by norm_num)) hhalf
        refine ⟨k + 1, ?_⟩
        rw [pow_succ']
        omega
      · have hmod1 : n % 2 = 1 := by omega
        have hhalf0 : s2 (n / 2) = 0 := by unfold s2; omega
        have hdiv0 : n / 2 = 0 := (s2_eq_zero_iff _).mp hhalf0
        refine ⟨0, ?_⟩
        omega
  · rintro ⟨k, rfl⟩
    exact s2_pow_two k

private lemma s2_three_mul_ge_two {n : ℕ} (hn : 0 < n) : 2 ≤ s2 (3 * n) := by
  by_contra hlt
  have hcases : s2 (3 * n) = 0 ∨ s2 (3 * n) = 1 := by omega
  rcases hcases with h0 | h1
  · have := (s2_eq_zero_iff (3 * n)).mp h0
    omega
  · obtain ⟨k, hk⟩ := (s2_eq_one_iff (3 * n)).mp h1
    have h3dvd : 3 ∣ 2 ^ k := ⟨n, hk.symm⟩
    have h3_dvd_2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3dvd
    omega

private lemma padicValNat_two_T (k : ℕ) : padicValNat 2 (tNat k) = 2 * s2 k := by
  have hfac := tNat_mul_factorials k
  have hT_pos : 0 < tNat k := mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hT_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac] at hv
  have h6 : s2 (6 * k) = s2 (3 * k) := by rw [show 6 * k = 2 * (3 * k) by ring, s2_mul_two]
  have h2 : s2 (2 * k) = s2 k := s2_mul_two k
  have hle6 := s2_le_self (6 * k)
  have hle3 := s2_le_self (3 * k)
  have hle2 := s2_le_self (2 * k)
  have hle1 := s2_le_self k
  omega

private lemma padicValNat_two_choose3 (n : ℕ) :
    padicValNat 2 ((3 * n).choose n) = 2 * s2 n - s2 (3 * n) := by
  have hfac : (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    simpa [show 3 * n - n = 2 * n by omega] using this
  have hc_pos : 0 < (3 * n).choose n := Nat.choose_pos (by omega)
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hc_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac, s2_mul_two] at hv
  have hle3 := s2_le_self (3 * n)
  have hle2 := s2_le_self (2 * n)
  have hle1 := s2_le_self n
  omega


/-- Legendre's formula records the number of carries in the binomial coefficient. -/
private lemma choose_digits {n k : ℕ} (hk : k ≤ n) :
    padicValNat 2 (n.choose k) + s2 n = s2 k + s2 (n-k) := by
  have hv := congrArg (padicValNat 2) (Nat.choose_mul_factorial_mul_factorial hk)
  have hc := (Nat.choose_pos hk).ne'
  simp only [padicValNat.mul, hc, Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac] at hv
  have := s2_le_self n
  have := s2_le_self k
  have := s2_le_self (n-k)
  omega

/-- Each rescaled convolution summand has the parity of its binomial coefficient. -/
private lemma term_comparison {n k : ℕ} (hk : k ≤ n) :
    2 ^ (2*s2 n+1) ∣ tNat k * tNat (n-k) + 2^(2*s2 n) * n.choose k := by
  let x := tNat k * tNat (n-k)
  have hx : x ≠ 0 := mul_ne_zero (tNat_pos _).ne' (tNat_pos _).ne'
  have hval : padicValNat 2 x = 2*s2 n + 2*padicValNat 2 (n.choose k) := by
    dsimp [x]
    rw [padicValNat.mul (tNat_pos _).ne' (tNat_pos _).ne', padicValNat_two_T,
      padicValNat_two_T]
    have := choose_digits hk
    omega
  obtain ⟨q, hq⟩ := (padicValNat_dvd_iff_le (p := 2) hx).2
    (show 2*s2 n ≤ padicValNat 2 x by omega)
  have hq0 : q ≠ 0 := by rintro rfl; simp [hq] at hx
  have hqv : padicValNat 2 q = 2 * padicValNat 2 (n.choose k) := by
    rw [hq, padicValNat.mul (by positivity) hq0, padicValNat.prime_pow] at hval
    omega
  have hpar : 2 ∣ q ↔ 2 ∣ n.choose k := by
    rw [dvd_iff_padicValNat_ne_zero hq0, dvd_iff_padicValNat_ne_zero (Nat.choose_pos hk).ne']
    omega
  have hsum : 2 ∣ q + n.choose k := by omega
  change 2^(2*s2 n+1) ∣ x + _
  rw [hq, ← Nat.mul_add, pow_succ]
  exact Nat.mul_dvd_mul_left _ hsum

private lemma convolution_bound {n : ℕ} (hs : 2 ≤ s2 n) :
    2^(2*s2 n+2) ∣ sNat n := by
  let u := 2*s2 n
  let M := 2^(u+2)
  let f := fun k => tNat k * tNat (n-k) + 2^u * n.choose k
  have hsym (k : ℕ) (hk : k ≤ n) : f (n-k) = f k := by
    dsimp [f]
    rw [Nat.sub_sub_self hk, Nat.choose_symm hk, mul_comm (tNat (n-k))]
  have hpairs : M ∣ ∑ k ∈ Finset.range (n+1), f k := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    apply Finset.sum_involution (fun k _ => n-k)
    · intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hpair : M ∣ 2 * f k := by
        dsimp [M]
        rw [show u+2 = (u+1)+1 by omega, pow_succ']
        exact Nat.mul_dvd_mul_left 2 (term_comparison hkn)
      have hz := (ZMod.natCast_eq_zero_iff _ _).2 hpair
      push_cast at hz
      rw [hsym k hkn]
      convert hz using 1 <;> ring
    · intro k hk hne hmid
      apply hne
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hn : n = 2*k := by omega
      have hs' : s2 n = s2 k := hn ▸ s2_mul_two k
      have hprod : M ∣ tNat k * tNat k := by
        apply (padicValNat_dvd_iff_le (p := 2) (mul_ne_zero (tNat_pos k).ne' (tNat_pos k).ne')).2
        rw [padicValNat.mul (tNat_pos _).ne' (tNat_pos _).ne', padicValNat_two_T]
        dsimp [u]
        omega
      have hbin : 2^2 ∣ n.choose k := by
        apply (padicValNat_dvd_iff_le (p := 2) (Nat.choose_pos hkn).ne').2
        have hc := choose_digits hkn
        rw [hmid] at hc
        omega
      apply (ZMod.natCast_eq_zero_iff _ _).2
      change M ∣ tNat k * tNat (n-k) + 2^u * n.choose k
      rw [hmid]
      apply dvd_add hprod
      dsimp [M]
      rw [pow_add]
      exact Nat.mul_dvd_mul_left _ hbin
    · intro k _
      exact Finset.mem_range.mpr (by omega)
    · intro k hk
      have := Finset.mem_range.mp hk
      omega
  have hc : M ∣ 2^u * 2^n := by
    have := s2_le_self n
    dsimp [M]
    rw [pow_add]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 2 (by omega))
  dsimp only [f] at hpairs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Nat.sum_range_choose] at hpairs
  exact (Nat.dvd_add_iff_left hc).mpr hpairs

end OeisA189286

open OeisA189286 in
theorem OMA.solution : OMA.R_OeisA189286_conjecture_3_R1.H3 := by
  intro n hn m hm hodd
  apply (s2_eq_one_iff n).1
  by_contra h
  have h0 : s2 n ≠ 0 := fun hz => hn.ne' ((s2_eq_zero_iff n).mp hz)
  have hs : 2 ≤ s2 n := by omega
  let D := (2*n-1) * (3*n).choose n
  have hd : D ≠ 0 := (denom_pos hn).ne'
  rw [a_eq_div_nat hn] at hm
  have heq := (div_eq_iff (Nat.cast_ne_zero.mpr (denom_pos hn).ne')).1 hm
  have heq' : (sNat n : ℤ) = 8*m*(D : ℕ) := by exact_mod_cast heq
  have habs : sNat n = 8*m.natAbs*D := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs heq'
  have hm0 : m.natAbs ≠ 0 := by
    intro hz
    simp [hz] at habs
    exact (sNat_pos n).ne' habs
  have hmval : padicValNat 2 m.natAbs = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro he
    have he' : (2 : ℤ) ∣ m := Int.dvd_natAbs.mp (by exact_mod_cast he)
    obtain ⟨t, ht⟩ := hodd
    omega
  have hD : padicValNat 2 D = 2*s2 n - s2 (3*n) := by
    have hoddD : padicValNat 2 (2*n-1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    dsimp [D]
    rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne', hoddD, zero_add,
      padicValNat_two_choose3]
  have hv := (padicValNat_dvd_iff_le (p := 2) (sNat_pos n).ne').1 (convolution_bound hs)
  rw [habs, padicValNat.mul (mul_ne_zero (by decide) hm0) hd,
    padicValNat.mul (by decide) hm0, hmval, hD] at hv
  have h8 : padicValNat 2 8 = 3 := by
    rw [show (8 : ℕ) = 2^3 by decide, padicValNat.prime_pow]
  have := s2_three_mul_ge_two hn
  omega
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
