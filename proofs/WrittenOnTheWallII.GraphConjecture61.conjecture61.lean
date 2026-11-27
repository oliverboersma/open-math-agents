import FormalConjectures.WrittenOnTheWallII.GraphConjecture61
import Mathlib

/-
Source: https://github.com/Sann2810/wowii61-lean/blob/594ca9419e2b4293c2ce54ca7093e12550666527/Wowii61/Main.lean
Original proof and formalization authors are credited in the source repository.
Adaptation: use the pinned Formal Conjectures definitions and package the proof as one file.


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

/-! Threshold sums for comparison of Havel--Hakimi reductions. -/

namespace Graffiti61.HH
open SimpleGraph

def excess (t : ℕ) (l : List ℕ) : ℕ := (l.map (· - t)).sum
def above (t : ℕ) (l : List ℕ) : ℕ := l.countP (t < ·)

theorem excess_succ (t : ℕ) (l : List ℕ) :
    excess t l = excess (t+1) l + above t l := by
  induction l with
  | nil => simp [excess, above]
  | cons x xs ih =>
    simp only [excess, List.map_cons, List.sum_cons, above, List.countP_cons] at *
    split <;> rename_i h <;> simp_all <;> omega

theorem excess_perm {a b : List ℕ} (t : ℕ) (h : a.Perm b) :
    excess t a = excess t b := (h.map _).sum_eq

theorem above_zero_of_le (t : ℕ) (l : List ℕ) (h : ∀ x ∈ l, x ≤ t) : above t l = 0 := by
  simpa [above, List.countP_eq_zero] using h

theorem dec_prefix_excess (t r : ℕ) (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) :
    excess t (((l.take r).map (·-1)) ++ l.drop r) + min r (above t l) = excess t l := by
  induction r generalizing l with
  | zero => simp [excess]
  | succ r ih =>
    cases l with
    | nil => simp [excess, above]
    | cons x xs =>
      obtain ⟨hall,hxs⟩ := List.pairwise_cons.mp hl
      have step := ih xs hxs
      by_cases h : t < x
      · simp [excess, above, h, Nat.succ_min_succ] at step ⊢
        omega
      · have az := above_zero_of_le t xs (fun z hz => le_trans (hall z hz) (by omega))
        simp only [above] at az
        simp [excess, above, h, az] at step ⊢
        omega

theorem hh_threshold (d t : ℕ) (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) :
    excess t (havelHakimiStep (d :: l)) + min d (above t l) = excess t l := by
  rw [havelHakimiStep, List.splitAt_eq]
  rw [excess_perm _ (List.mergeSort_perm _ _)]
  exact dec_prefix_excess t d l hl


abbrev Degrees := Multiset ℕ
def prof (a : Degrees) (t : ℕ) := (a.map (·-t)).sum
def countGt (a : Degrees) (t : ℕ) := a.countP (t < ·)
def lower (r : ℕ) (a : Degrees) : Degrees :=
  let l := a.sort (· ≥ ·)
  (((l.take r).map (·-1) ++ l.drop r : List ℕ) : Multiset ℕ)

@[simp] theorem prof_cons (x : ℕ) (a : Degrees) (t : ℕ) :
    prof (x ::ₘ a) t = x-t + prof a t := by simp [prof]
@[simp] theorem prof_list (l : List ℕ) (t : ℕ) : prof (↑l) t = excess t l := rfl

theorem prof_succ (a : Degrees) (t : ℕ) :
    prof a t = prof a (t+1) + countGt a t := by
  induction a using Quotient.inductionOn with
  | _ l => exact excess_succ t l

@[simp] theorem card_lower (r : ℕ) (a : Degrees) : (lower r a).card = a.card := by
  simp [lower]; omega

theorem lower_prof (r : ℕ) (a : Degrees) (t : ℕ) :
    prof (lower r a) t = max (prof a t - r) (prof a (t+1)) := by
  let l := a.sort (· ≥ ·)
  have hl : l.Pairwise (· ≥ ·) := Multiset.pairwise_sort _ _
  have hs : (↑l : Degrees) = a := Multiset.sort_eq _ _
  have hh := dec_prefix_excess t r l hl
  have ht := excess_succ t l
  rw [←hs, prof_list, prof_list]
  have he : prof (lower r (↑l)) t = excess t (((l.take r).map (·-1)) ++ l.drop r) := by
    rw [hs]; rfl
  rw [he]
  omega

def Weak (a b : Degrees) : Prop := ∀ t, prof a t ≤ prof b t

theorem lower_weak {a b : Degrees} (h : Weak a b) (r : ℕ) : Weak (lower r a) (lower r b) := by
  intro t
  simp only [lower_prof]
  exact max_le_max (Nat.sub_le_sub_right (h t) _) (h _)

theorem countGt_prev (a : Degrees) (t : ℕ) :
    countGt a t = countGt a (t+1) + a.count (t+1) := by
  induction a using Multiset.induction_on with
  | empty => simp [countGt]
  | cons x a ih =>
    simp only [countGt,Multiset.countP_cons,Multiset.count_cons] at *
    split_ifs <;> omega

theorem countGt_zero (a : Degrees) : a.card = countGt a 0 + a.count 0 := by
  induction a using Multiset.induction_on with
  | empty => simp [countGt]
  | cons x a ih =>
    simp only [countGt,Multiset.countP_cons,Multiset.count_cons,Multiset.card_cons] at *
    split_ifs <;> omega

theorem ext_prof {a b : Degrees} (hc : a.card = b.card) (h : ∀ t, prof a t = prof b t) :
    a = b := by
  have cnt (t : ℕ) : countGt a t = countGt b t := by
    have := prof_succ a t
    have := prof_succ b t
    have := h t
    have := h (t+1)
    omega
  apply Multiset.ext.mpr
  intro t
  cases t with
  | zero => have := countGt_zero a; have := countGt_zero b; have := cnt 0; omega
  | succ t => have := countGt_prev a t; have := countGt_prev b t; have := cnt t
              have := cnt (t+1); omega

theorem lower_twice (p q : ℕ) (a : Degrees) (t : ℕ) :
    prof (lower p (lower q a)) t =
    max (max (prof a t - (p+q)) (prof a (t+1) - min p q)) (prof a (t+2)) := by
  simp only [lower_prof, show t+1+1 = t+2 by omega]
  by_cases pq : p ≤ q <;> simp [pq, le_of_not_ge] <;> omega

theorem lower_comm (p q : ℕ) (a : Degrees) :
    lower p (lower q a) = lower q (lower p a) := by
  apply ext_prof (by simp)
  intro t
  rw [lower_twice, lower_twice, Nat.add_comm p q, min_comm p q]

def energy (b : Degrees) : ℕ := (b.map fun x => x*x).sum
@[simp] theorem energy_cons (x : ℕ) (a : Degrees) : energy (x ::ₘ a) = x*x + energy a := by
  simp [energy]

theorem prof_zero_of_ge {a : Degrees} {t : ℕ} (h : ∀ x ∈ a, x ≤ t) : prof a t = 0 := by
  induction a using Multiset.induction_on with
  | empty => simp [prof]
  | cons x a ih =>
    rw [prof_cons, Nat.sub_eq_zero_of_le (h _ (by simp)), zero_add]
    exact ih fun y hy => h _ (by simp [hy])

theorem prof_large (a : Degrees) (t : ℕ) (h : a.sum ≤ t) : prof a t = 0 :=
  by
  apply prof_zero_of_ge
  intro x hx
  obtain ⟨s,rfl⟩ := Multiset.exists_cons_of_mem hx
  simp at h
  omega

/-- Reduce weak excess comparison to the elementary operations that raise one
degree or transfer a unit from the smaller of two entries to the larger. -/
theorem weak_induction {a b : Degrees} (hc : a.card = b.card) (hw : Weak a b)
    (P : Degrees → Prop) (init : P b)
    (down : ∀ x s, (x ::ₘ s).card = a.card → P ((x+1) ::ₘ s) → P (x ::ₘ s))
    (smooth : ∀ x y s, x ≤ y → (x ::ₘ y ::ₘ s).card = a.card →
      P ((y+1) ::ₘ x ::ₘ s) → P (y ::ₘ (x+1) ::ₘ s)) : P a := by
  classical
  induction H : energy b using Nat.strong_induction_on generalizing b with
  | h n ih =>
    by_cases eq : ∀ t, prof a t = prof b t
    · rwa [ext_prof hc eq]
    have gap : ∃ t, prof a t < prof b t := by
      push Not at eq
      obtain ⟨t,ht⟩ := eq
      exact ⟨t,lt_of_le_of_ne (hw _) ht⟩
    let l := Nat.find gap
    have atL : prof a l < prof b l := Nat.find_spec gap
    have before (t) (ht : t < l) : prof a t = prof b t :=
      le_antisymm (hw t) (not_lt.mp (Nat.find_min gap ht))
    have close : ∃ j, prof a (l+j) = prof b (l+j) := by
      use a.sum+b.sum
      rw [prof_large a _ (by omega), prof_large b _ (by omega)]
    let r := l + Nat.find close
    have atR : prof a r = prof b r := Nat.find_spec close
    have lr : l < r := by
      have hle : l ≤ r := Nat.le_add_right _ _
      by_contra! bad
      have hh : r = l := by omega
      rw [hh] at atR
      omega
    have interval (t : ℕ) (ht : l ≤ t) (ht' : t < r) : prof a t < prof b t := by
      have hj : t-l < Nat.find close := by dsimp [r] at ht'; omega
      have neq := Nat.find_min close hj
      rw [Nat.add_sub_of_le ht] at neq
      exact lt_of_le_of_ne (hw t) neq
    have hasR : r ∈ b := by
      have aa := prof_succ a (r-1)
      have bb := prof_succ b (r-1)
      have c := interval (r-1) (by omega) (by omega)
      have ha := prof_succ a r
      have hb := prof_succ b r
      have next := hw (r+1)
      have ca := countGt_prev a (r-1)
      have cb := countGt_prev b (r-1)
      have er : r-1+1 = r := by omega
      rw [er] at aa bb ca cb
      exact Multiset.count_pos.mp (by omega)
    obtain ⟨s,bs⟩ := Multiset.exists_cons_of_mem hasR
    cases l0 : l with
    | zero =>
      let c := (r-1) ::ₘ s
      have wc : Weak a c := by
        intro t
        have wt := hw t
        rw [bs,prof_cons] at wt
        dsimp [c]; rw [prof_cons]
        by_cases tr : t < r
        · have it := interval t (by omega) tr
          rw [bs,prof_cons] at it
          omega
        · omega
      have Hc : energy c < n := by simp only [c,←H,bs,energy_cons]; nlinarith [Nat.sub_add_cancel (show 1 ≤ r by omega)]
      apply ih _ Hc (b := c) (by simpa [c,bs] using hc) wc _ rfl
      apply down (r-1) s (by simpa [bs] using hc.symm)
      simpa [show r-1+1 = r by omega, ←bs] using init
    | succ k =>
      have hk : k ∈ b := by
        have aa := prof_succ a k
        have bb := prof_succ b k
        have c := before k (by omega)
        rw [l0] at atL
        cases k with
        | zero =>
          have ca := countGt_zero a; have cb := countGt_zero b
          exact Multiset.count_pos.mp (by omega)
        | succ j =>
          have pr := before j (by omega)
          have da := prof_succ a j; have db := prof_succ b j
          have ca := countGt_prev a j; have cb := countGt_prev b j
          exact Multiset.count_pos.mp (by omega)
      have ks : k ∈ s := by
        rw [bs,Multiset.mem_cons] at hk
        exact hk.resolve_left (by omega)
      obtain ⟨u,su⟩ := Multiset.exists_cons_of_mem ks
      let c := (r-1) ::ₘ (k+1) ::ₘ u
      have wc : Weak a c := by
        intro t
        have wt := hw t
        rw [bs,su,prof_cons,prof_cons] at wt
        dsimp [c]; rw [prof_cons,prof_cons]
        by_cases inside : l ≤ t ∧ t < r
        · have it := interval t inside.1 inside.2
          rw [bs,su,prof_cons,prof_cons] at it
          omega
        · omega
      have Hc : energy c < n := by
        simp only [c,←H,bs,su,energy_cons]
        nlinarith [Nat.sub_add_cancel (show 1 ≤ r by omega), show k+2 ≤ r by omega]
      apply ih _ Hc (b := c) (by simpa [c,bs,su] using hc) wc _ rfl
      apply smooth k (r-1) u (by omega) (by simpa [bs,su] using hc.symm)
      simpa [show r-1+1 = r by omega, ←su, ←bs] using init

def Upper (a : Degrees) (x : ℕ) := ∀ y ∈ a, y ≤ x

def work : List ℕ → ℕ
  | [] => 0
  | h :: l => (h-1) + work (havelHakimiStep (h :: l))
termination_by a => a.length
decreasing_by rw [havelHakimiStep_length_cons]; simp

def F (a : Degrees) := work (a.sort (· ≥ ·))

theorem F_head (k : ℕ) (d : Degrees) (hk : Upper d k) :
    F (k ::ₘ d) = k-1 + F (lower k d) := by
  rw [F,Multiset.sort_cons k d (· ≥ ·) hk,work]
  simp only [F,lower,havelHakimiStep,List.splitAt_eq,Multiset.coe_sort]

theorem upper_iff_prof (a : Degrees) (k : ℕ) : Upper a k ↔ prof a k = 0 := by
  refine ⟨prof_zero_of_ge,?_⟩
  intro h y hy
  obtain ⟨d,rfl⟩ := Multiset.exists_cons_of_mem hy
  rw [prof_cons] at h
  omega

theorem upper_lower (a : Degrees) (k r : ℕ) (h : Upper a k) : Upper (lower r a) k := by
  apply (upper_iff_prof _ _).mpr
  have h1 := (upper_iff_prof _ _).mp h
  have h2 := prof_succ a k
  rw [lower_prof]; omega

theorem countGt_anti (a : Degrees) {x y : ℕ} (h : x ≤ y) : countGt a y ≤ countGt a x := by
  induction a using Multiset.induction_on with
  | empty => simp [countGt]
  | cons v a ih =>
    simp only [countGt, Multiset.countP_cons] at *
    split_ifs <;> omega

theorem lower_spare (a : Degrees) (w r : ℕ) (h : r ≤ a.countP (w ≤ ·)) :
    lower r (w ::ₘ a) = w ::ₘ lower r a := by
  apply ext_prof (by simp)
  intro t
  simp only [lower_prof,prof_cons]
  by_cases ht : t < w
  · have hn : r ≤ countGt a t := by
      refine h.trans ?_
      change a.countP (w ≤ ·) ≤ a.countP (t < ·)
      clear h
      induction a using Multiset.induction_on with
      | empty => simp
      | cons x a ih => simp only [Multiset.countP_cons]; split_ifs <;> omega
    have ha := prof_succ a t
    omega
  · omega

theorem lower_hit (a : Degrees) (w r : ℕ) (h : countGt a w < r) :
    lower r (w ::ₘ a) = (w-1) ::ₘ lower (r-1) a := by
  apply ext_prof (by simp)
  intro t
  simp only [lower_prof,prof_cons]
  by_cases ht : t < w
  · omega
  · have hh := countGt_anti a (show w ≤ t by omega)
    have ha := prof_succ a t
    omega

theorem upper_cons_iff {a : Degrees} {x y : ℕ} :
    Upper (x ::ₘ a) y ↔ x ≤ y ∧ Upper a y := by simp [Upper]

theorem upper_lower_tight (d : Degrees) (w r : ℕ) (h : Upper d w)
    (hb : d.countP (w ≤ ·) ≤ r) : Upper (lower r d) (w-1) := by
  by_cases z : w = 0
  · simpa [z] using upper_lower d w r h
  apply (upper_iff_prof _ _).mpr
  have hp := (upper_iff_prof _ _).mp h
  have hs := prof_succ d (w-1)
  have he : w-1+1=w := by omega
  rw [he] at hs
  have hh : countGt d (w-1) = d.countP (w ≤ ·) := by
    unfold countGt
    congr 1
    funext x
    exact propext (by omega)
  rw [lower_prof,he]
  omega

/-- If a second deletion can use the displayed vertex, commute its quota
on the other degrees past that of the first vertex. -/
theorem undo_second (k w e : ℕ) (d : Degrees)
    (h1 : Upper (w ::ₘ d) k) (h2 : Upper (lower (k-e) d) (w-e))
    (h3 : Upper (lower (w-e) d) (k-e))
    (h4 : lower k (w ::ₘ d) = (w-e) ::ₘ lower (k-e) d)
    (he : e ≤ 1) (hw : 2 ≤ w) :
    F (k ::ₘ w ::ₘ d) = w-1 + F ((k-e) ::ₘ lower (w-e) d) := by
  rw [F_head _ _ h1,h4,F_head _ _ h2,F_head _ _ h3,lower_comm]
  have hkw := (upper_cons_iff.mp h1).1
  omega

def paired (k w : ℕ) (d : Degrees) := if k ≤ d.countP (w ≤ ·) then 0 else 1

theorem undo_common (k w : ℕ) (d : Degrees) (hk : w ≤ k) (hw : 2 ≤ w) (hd : Upper d w) :
    F (k ::ₘ w ::ₘ d) =
      w-1 + F ((k-paired k w d) ::ₘ lower (w-paired k w d) d) := by
  have up : Upper (w ::ₘ d) k := upper_cons_iff.mpr ⟨hk, fun y hy => (hd _ hy).trans hk⟩
  unfold paired
  split <;> rename_i h
  · simp only [Nat.sub_zero]
    apply undo_second k w 0 d up (upper_lower _ _ _ hd) (upper_lower d k w (fun y hy => (hd _ hy).trans hk)) (lower_spare _ _ _ h) (by decide) hw
  · have hn : countGt d w = 0 := by
      have := (upper_iff_prof _ _).mp hd; have := prof_succ d w; omega
    have ht := upper_lower_tight d w (k-1) hd (by omega)
    have hr : Upper (lower (w-1) d) (k-1) := by
      by_cases eq : w=k
      · subst k; exact ht
      · exact fun y hy => le_trans (upper_lower d w (w-1) hd _ hy) (by omega)
    exact undo_second k w 1 d up ht hr (lower_hit _ _ _ (by omega)) (by decide) hw

theorem exists_head (s : Degrees) (hs : s ≠ 0) :
    ∃ k d, s = k ::ₘ d ∧ Upper d k := by
  let k := s.toFinset.max' (by simpa using hs)
  have hk : k ∈ s := by simpa [k] using s.toFinset.max'_mem (by simpa using hs)
  obtain ⟨d,hd⟩ := Multiset.exists_cons_of_mem hk
  refine ⟨k,d,hd,fun y hy => Finset.le_max' _ _ ?_⟩
  exact Multiset.mem_toFinset.mpr (hd ▸ Multiset.mem_cons_of_mem hy)

theorem F_zero_of_small (s : Degrees) (h : Upper s 1) : F s = 0 := by
  induction H : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases z : s = 0
    · simp [z,F,work]
    obtain ⟨k,d,rfl,hd⟩ := exists_head s z
    have hk := upper_cons_iff.mp h
    rw [F_head k d hd,ih _ (by simp [←H]) _ (upper_lower _ _ _ hk.2) rfl]
    omega

def Short (n : ℕ) : Prop := ∀ a b : Degrees, a.card < n → a.card = b.card → Weak a b → F a ≤ F b

theorem F_common_max {n k : ℕ} (ih : Short n) (d d' : Degrees)
    (hc : d.card < n) (size : d.card = d'.card)
    (hu : Upper d k) (hu' : Upper d' k) (hw : Weak d d') :
    F (k ::ₘ d) ≤ F (k ::ₘ d') := by
  rw [F_head _ _ hu,F_head _ _ hu']
  exact Nat.add_le_add_left (ih _ _ (by simpa) (by simpa) (lower_weak hw k)) _

theorem lower_loss_one {a b : Degrees} (h : ∀ t, prof a t ≤ prof b t + 1) (r t : ℕ) :
    prof (lower r a) t ≤ prof (lower r b) t + 1 := by
  have := h t
  have := h (t+1)
  rw [lower_prof,lower_prof]
  omega

theorem count_atleast_le (a : Degrees) {t w : ℕ} (ht : t < w) :
    a.countP (w ≤ ·) ≤ countGt a t := by
  unfold countGt
  induction a using Multiset.induction_on with
  | empty => simp
  | cons x a ih => simp only [Multiset.countP_cons]; split_ifs <;> omega

theorem F_common_second {n k w : ℕ} (ih : Short n) (d d' : Degrees) (hk : w ≤ k)
    (size : d.card = d'.card) (sm : d.card+1 < n)
    (hu : Upper d w) (hu' : Upper d' w) (loss : ∀ t, prof d t ≤ prof d' t + 1) :
    F (k ::ₘ w ::ₘ d) ≤ F ((k+1) ::ₘ w ::ₘ d') := by
  have top : Upper (w ::ₘ d) k := upper_cons_iff.mpr ⟨hk, fun y hy => (hu y hy).trans hk⟩
  have top' : Upper (w ::ₘ d') (k+1) := upper_cons_iff.mpr ⟨show w ≤ k+1 by omega, fun y hy => (hu' y hy).trans (by omega)⟩
  by_cases small : w ≤ 1
  · rw [F_head _ _ top, F_zero_of_small _ (upper_lower _ _ _ (upper_cons_iff.mpr ⟨small, fun y hy => (hu y hy).trans small⟩)),F_head _ _ top']
    omega
  rw [undo_common _ _ _ hk (by omega) hu,undo_common _ _ _ (by omega) (by omega) hu']
  apply Nat.add_le_add_left
  apply ih
  · simpa
  · simpa
  intro t
  rw [prof_cons,prof_cons,lower_prof,lower_prof]
  have gap := loss t
  have gap' := loss (t+1)
  have wt := prof_succ d t
  have wzero (z) (hz : w ≤ z) : prof d z = 0 := prof_zero_of_ge fun x hx => (hu x hx).trans hz
  have enough := @count_atleast_le d t w
  unfold paired
  split <;> rename_i h <;> split <;> rename_i h'
  all_goals by_cases ht : t < w
  all_goals first | have := enough ht; omega | have := wzero t (by omega); have := wzero (t+1) (by omega); omega

theorem F_singleton (k : ℕ) : F {k} = k-1 := by
  change F (k ::ₘ 0) = _
  rw [F_head _ _ (by simp [Upper])]
  simp [lower,F,work]

theorem weak_bump (x : ℕ) (d : Degrees) : Weak (x ::ₘ d) ((x+1) ::ₘ d) := by
  intro t; simp only [prof_cons]; omega

theorem weak_shift (x y : ℕ) (d : Degrees) (h : x ≤ y) :
    Weak (y ::ₘ (x+1) ::ₘ d) ((y+1) ::ₘ x ::ₘ d) := by
  intro t; simp only [prof_cons]; omega

theorem F_inc {n : ℕ} (ih : Short n) (x : ℕ) (s : Degrees) (sz : (x ::ₘ s).card = n) :
    F (x ::ₘ s) ≤ F ((x+1) ::ₘ s) := by
  by_cases z : s = 0
  · subst s; simpa only [Multiset.cons_zero,F_singleton] using (show x-1 ≤ x+1-1 by omega)
  obtain ⟨w,d,rfl,hd⟩ := exists_head s z
  by_cases h : w ≤ x
  · exact F_common_second ih d d h rfl (by simp_all; omega) hd hd (by omega)
  · rw [Multiset.cons_swap x,Multiset.cons_swap (x+1)]
    apply F_common_max ih _ _ (by simp_all; omega) (by simp)
      (upper_cons_iff.mpr ⟨by omega,hd⟩) (upper_cons_iff.mpr ⟨by omega, hd⟩) (weak_bump _ _)

theorem F_two_shift {n x y : ℕ} (ih : Short n) (d : Degrees) (hxy : x < y)
    (hu : Upper d x) (hc : d.card + 1 < n) :
    F (y ::ₘ (x+1) ::ₘ d) ≤ F ((y+1) ::ₘ x ::ₘ d) := by
  have o : Upper ((x+1) ::ₘ d) y := upper_cons_iff.mpr ⟨by omega, fun z hz => (hu _ hz).trans (by omega)⟩
  have o' : Upper (x ::ₘ d) (y+1) := upper_cons_iff.mpr ⟨by omega, fun z hz => (hu _ hz).trans (by omega)⟩
  have count0 : countGt d (x+1) = 0 := by
    have hz := prof_zero_of_ge (a := d) (t := x+1) (fun z hz => (hu _ hz).trans (by omega))
    have := prof_succ d (x+1); omega
  have hit := lower_hit d (x+1) y (by omega)
  rw [show x+1-1=x by omega] at hit
  have old : F (y ::ₘ (x+1) ::ₘ d) = y-1 + (x-1 + F (lower x (lower (y-1) d))) := by
    rw [F_head _ _ o,hit,F_head _ _ (upper_lower d x (y-1) hu)]
  by_cases small : x ≤ 1
  · rw [old,F_head _ _ o',F_zero_of_small _ (upper_lower _ _ _ (upper_lower d 1 (y-1) (fun z hz => (hu _ hz).trans small)))]
    omega
  by_cases spare : y+1 ≤ d.countP (x ≤ ·)
  · have hx : x ∈ d := by
      by_contra nh
      have hn : d.countP (x ≤ ·) = 0 := by
        apply Multiset.countP_eq_zero.mpr
        intro z hz hzx
        have eq : z=x := le_antisymm (hu _ hz) hzx
        exact nh (eq ▸ hz)
      omega
    obtain ⟨e,de⟩ := Multiset.exists_cons_of_mem hx
    subst d
    have he := (upper_cons_iff.mp hu).2
    rw [Multiset.cons_swap (x+1) x]
    have count : y ≤ ((x+1) ::ₘ e).countP (x ≤ ·) := by
      simpa [Multiset.countP_cons] using Nat.le_of_succ_le spare
    have tailold : Upper (lower y ((x+1) ::ₘ e)) x := by
      have hh : ((x+1) ::ₘ e).countP (x+1 ≤ ·) ≤ y := by
        have hz : e.countP (x+1 ≤ ·) = 0 := by
          apply Multiset.countP_eq_zero.mpr
          intro z hz; have := he _ hz; omega
        rw [Multiset.countP_cons, hz]; simp only [le_refl, if_true, zero_add]; omega
      simpa using upper_lower_tight ((x+1) ::ₘ e) (x+1) y
        (upper_cons_iff.mpr ⟨le_rfl, fun z hz => (he _ hz).trans (by omega)⟩) hh
    have upold : Upper (x ::ₘ (x+1) ::ₘ e) y :=
      upper_cons_iff.mpr ⟨by omega, upper_cons_iff.mpr ⟨by omega, fun z hz => (he _ hz).trans (by omega)⟩⟩
    have hs1 := undo_second y x 0 ((x+1) ::ₘ e) upold tailold
      (upper_lower _ _ _ (upper_cons_iff.mp upold).2) (lower_spare _ _ _ count) (by decide) (by omega)
    have hs2 := undo_second (y+1) x 0 (x ::ₘ e) o'
      (upper_lower _ _ _ hu) (upper_lower _ _ _ (upper_cons_iff.mp o').2)
      (lower_spare _ _ _ spare) (by decide) (by omega)
    simp only [Nat.sub_zero] at hs1 hs2
    rw [hs1,hs2]
    apply Nat.add_le_add_left
    apply ih
    · simpa using hc
    · simp
    · intro t
      have hgap (t) : prof ((x+1) ::ₘ e) t ≤ prof (x ::ₘ e) t + 1 := by
        simp only [prof_cons]; omega
      have gap := lower_loss_one hgap x t
      by_cases yt : t < y
      · simp only [prof_cons]; omega
      · have hzero := prof_zero_of_ge (a := lower x ((x+1) ::ₘ e)) (t := t)
            (fun z hz => (upper_lower _ _ _ (upper_cons_iff.mp upold).2 z hz).trans (by omega))
        simp only [prof_cons]; omega
  · have hd0 : countGt d x = 0 := by
      have := (upper_iff_prof d x).mp hu; have := prof_succ d x; omega
    have hx := lower_hit d x (y+1) (by omega)
    simp only [Nat.add_sub_cancel] at hx
    have residual := upper_lower_tight d x y hu (by omega)
    rw [old,F_head _ _ o',hx,F_head _ _ residual]
    have comp : F (lower x (lower (y-1) d)) ≤ F (lower (x-1) (lower y d)) := by
      apply ih
      · simp; omega
      · simp
      · intro t
        rw [lower_twice,lower_twice]
        have e : x+(y-1)=x-1+y := by omega
        rw [e]
        have mn : min x (y-1)=x := Nat.min_eq_left (by omega)
        have mn' : min (x-1) y=x-1 := Nat.min_eq_left (by omega)
        rw [mn,mn']; omega
    omega

theorem F_transfer {n : ℕ} (ih : Short n) (x y : ℕ) (s : Degrees) (hxy : x ≤ y)
    (sz : (x ::ₘ y ::ₘ s).card = n) :
    F (y ::ₘ (x+1) ::ₘ s) ≤ F ((y+1) ::ₘ x ::ₘ s) := by
  by_cases eq : x=y
  · subst y; rw [Multiset.cons_swap x (x+1)]
  have sz' : s.card+1 < n := by simp at sz; omega
  by_cases z : s=0
  · apply F_two_shift ih _ (by omega) _ sz'
    simp [z,Upper]
  obtain ⟨w,d,rfl,hd⟩ := exists_head s z
  by_cases top : y < w
  · have a : y ::ₘ (x+1) ::ₘ w ::ₘ d = w ::ₘ y ::ₘ (x+1) ::ₘ d := by rw [Multiset.cons_swap (x+1) w, Multiset.cons_swap y w]
    have b : (y+1) ::ₘ x ::ₘ w ::ₘ d = w ::ₘ (y+1) ::ₘ x ::ₘ d := by rw [Multiset.cons_swap x w, Multiset.cons_swap (y+1) w]
    rw [a,b]
    apply F_common_max ih _ _ (by simpa using sz') (by simp)
    · exact upper_cons_iff.mpr ⟨by omega,upper_cons_iff.mpr ⟨by omega,hd⟩⟩
    · exact upper_cons_iff.mpr ⟨by omega,upper_cons_iff.mpr ⟨by omega,hd⟩⟩
    · exact weak_shift _ _ _ hxy
  by_cases mid : x < w
  · rw [Multiset.cons_swap (x+1) w,Multiset.cons_swap x w]
    apply F_common_second ih _ _ (by omega) (by simp) (by simpa using sz')
      (upper_cons_iff.mpr ⟨by omega,hd⟩) (upper_cons_iff.mpr ⟨by omega,hd⟩)
    intro t; simp only [prof_cons]; omega
  · exact F_two_shift ih _ (by omega) (upper_cons_iff.mpr ⟨by omega,fun z hz => (hd _ hz).trans (by omega)⟩) sz'

theorem F_weak {a b : Degrees} (hc : a.card = b.card) (h : Weak a b) : F a ≤ F b := by
  induction sz : a.card using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    have short : Short n := fun x y hx he hw => ih x.card hx he hw rfl
    apply weak_induction hc h (fun s => F s ≤ F b) le_rfl
    · intro x s he hF
      exact (F_inc short x s (he.trans sz)).trans hF
    · intro x y s hxy he hF
      exact (F_transfer short x y s hxy (he.trans sz)).trans hF


def potential (a : Degrees) : ℤ := 2*(a.card : ℤ) + 2*(F a : ℤ) - (a.sum : ℤ)

theorem prof_0 (a : Degrees) : prof a 0 = a.sum := by simp [prof]

theorem potential_step (k : ℕ) (d u : Degrees) (hk : Upper d k) (pos : 0 < k)
    (hc : u.card = d.card) (hs : u.sum + k = d.sum) (hd : Weak (lower k d) u) :
    potential (k ::ₘ d) ≤ potential u := by
  have hf := F_weak (a := lower k d) (b := u) (by simpa using hc.symm) hd
  simp only [potential,F_head k d hk,Multiset.card_cons,Multiset.sum_cons]
  omega

theorem residue_le_potential (a : Degrees) :
    2*(residueAux (a.sort (· ≥ ·)) : ℤ) ≤ potential a := by
  induction hsize : a.card using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases z : a = 0
    · simp [z,potential,F,work,residueAux]
    obtain ⟨k,d,rfl,hd⟩ := exists_head a z
    rw [Multiset.sort_cons k d (· ≥ ·) hd]
    cases k with
    | zero =>
      have hs := prof_zero_of_ge hd
      rw [prof_0] at hs
      simp only [residueAux,potential,Multiset.card_cons,Multiset.sum_cons,zero_add,
        Multiset.length_sort,hs]
      omega
    | succ k =>
      rw [residueAux] <;> try omega
      have he : havelHakimiStep ((k+1) :: d.sort (· ≥ ·)) =
          (lower (k+1) d).sort (· ≥ ·) := by simp [havelHakimiStep,lower,List.splitAt_eq]
      rw [he]
      have hi := ih _ (by simp [←hsize] : (lower (k+1) d).card < n) (lower (k+1) d) rfl
      have loss := lower_prof (k+1) d 0
      simp only [prof_0] at loss
      have le : d.sum ≤ (lower (k+1) d).sum + (k+1) := by omega
      simp only [potential,F_head (k+1) d hd,Multiset.card_cons,Multiset.sum_cons,card_lower] at *
      omega

theorem potential_small (a : Degrees) (h : Upper a 1) :
    potential a = 2*(a.card : ℤ) - (a.sum : ℤ) := by simp [potential,F_zero_of_small _ h]

variable {V : Type*} [DecidableEq V]

def vec (A : Finset V) (f : V → ℕ) : Degrees := A.val.map f

omit [DecidableEq V] in
@[simp] theorem card_vec (A : Finset V) (f : V → ℕ) : (vec A f).card = A.card := by
  simp [vec]
omit [DecidableEq V] in
theorem sum_vec (A : Finset V) (f : V → ℕ) : (vec A f).sum = ∑ x ∈ A, f x := rfl
omit [DecidableEq V] in
theorem prof_vec (A : Finset V) (f : V → ℕ) (t : ℕ) :
    prof (vec A f) t = ∑ x ∈ A, (f x - t) := by
  unfold prof vec
  rw [Multiset.map_map]; rfl

theorem vec_insert (A : Finset V) (f : V → ℕ) (x : V) (hx : x ∉ A) :
    vec (insert x A) f = f x ::ₘ vec A f := by simp [vec, Finset.insert_val_of_notMem hx]

omit [DecidableEq V] in
theorem upper_vec (A : Finset V) (f : V → ℕ) (k : ℕ) (h : ∀ x ∈ A, f x ≤ k) :
    Upper (vec A f) k := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hy
  exact h x hx

theorem selected_sum (A N : Finset V) (sub : N ⊆ A) :
    (∑ x ∈ A, if x ∈ N then 1 else 0) = N.card := by
  simp [Finset.inter_eq_right.mpr sub]

theorem numerical_max_delete (A N : Finset V) (f g : V → ℕ) (x : V)
    (hx : x ∉ A) (sub : N ⊆ A) (deg : f x = N.card) (pos : 0 < f x)
    (highest : ∀ y ∈ A, f y ≤ f x)
    (dec : ∀ y ∈ A, f y = g y + (if y ∈ N then 1 else 0)) :
    potential (vec (insert x A) f) ≤ potential (vec A g) := by
  rw [vec_insert _ _ _ hx]
  apply potential_step (f x) _ _ (upper_vec _ _ _ highest) pos (by simp)
  · rw [sum_vec,sum_vec,deg,←selected_sum A N sub,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y hy => (dec y hy).symm)
  · intro t
    rw [lower_prof,prof_vec,prof_vec,prof_vec]
    apply max_le
    · apply Nat.sub_le_of_le_add
      rw [deg,←selected_sum A N sub,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro y hy
      rw [dec y hy]; split <;> omega
    · apply Finset.sum_le_sum
      intro y hy
      rw [dec y hy]; split <;> omega


end Graffiti61.HH

/- Geodesic markers and the induced forest for conjecture 61. -/

open SimpleGraph
namespace Graffiti61

variable {V : Type*}

theorem acyclic_of_leaves_and_matching (G : SimpleGraph V) (leaf : V → Prop)
    (hL : ∀ x, leaf x → ∀ y z, G.Adj x y → G.Adj x z → y = z)
    (hM : ∀ x y z, ¬leaf x → ¬leaf y → ¬leaf z → G.Adj x y → G.Adj x z → y = z) :
    G.IsAcyclic := by
  intro x p hp
  let C := p.toSubgraph.spanningCoe
  have cycles : C.IsCycles := hp.isCycles_spanningCoe_toSubgraph
  have incl {a b : V} (h : C.Adj a b) : G.Adj a b := p.toSubgraph.adj_sub h
  have core {a b : V} (h : C.Adj a b) : ¬leaf a := by
    intro ha
    obtain ⟨c, hne, hc⟩ := cycles.other_adj_of_adj h
    exact hne (hL a ha b c (incl h) (incl hc))
  have hxy : C.Adj x p.snd := p.toSubgraph_adj_snd hp.not_nil
  obtain ⟨z, hne, hxz⟩ := cycles.other_adj_of_adj hxy
  exact hne (hM _ _ _ (core hxy) (core hxy.symm) (core hxz.symm) (incl hxy) (incl hxz))

theorem forest_card_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {s : Finset V} (hs : (G.induce (s : Set V)).IsAcyclic) :
    s.card ≤ G.largestInducedForestSize := by
  unfold largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card V, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨s, hs, rfl⟩

theorem geodesic_level {G : SimpleGraph V} (h : G.Connected) {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b) (i : ℕ) (hi : i ≤ p.length) :
    G.dist a (p.getVert i) = i := by
  have h1 := G.dist_le (p.take i)
  have h2 := G.dist_le (p.drop i)
  rw [Walk.take_length, Nat.min_eq_left hi] at h1
  rw [Walk.drop_length] at h2
  have h3 := h.dist_triangle (u := a) (v := p.getVert i) (w := b)
  omega

theorem level_diff_le_one {G : SimpleGraph V} (h : G.Connected) (a : V)
    {x y : V} (hxy : G.Adj x y) : G.dist a x ≤ G.dist a y + 1 := by
  have ht := h.dist_triangle (u := a) (v := y) (w := x)
  simpa [dist_eq_one_iff_adj.mpr hxy.symm] using ht


variable [Fintype V] [DecidableEq V]

/-- The markers in each side are three levels apart. -/
structure Markers (G : SimpleGraph V) (m : ℕ) where
  left : Finset V
  right : Finset V
  left_card : left.card = m
  right_card : right.card = m
  apart : Disjoint left right
  match_one : ∀ x ∈ left ∪ right, ∃ y ∈ left ∪ right, G.Adj x y ∧
    ∀ z ∈ left ∪ right, G.Adj x z → z = y
  sparse_left : ∀ x y z, y ∈ left → z ∈ left → G.Adj x y → G.Adj x z → y = z
  sparse_right : ∀ x y z, y ∈ right → z ∈ right → G.Adj x y → G.Adj x z → y = z

omit [Fintype V] in
theorem markers_exist (G : SimpleGraph V) [Nonempty V] (h : G.Connected) :
    Nonempty (Markers G ((G.diam+2)/3)) := by
  classical
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a b
  let m := (G.diam+2)/3
  let v (t : ℕ) (i : Fin m) := p.getVert (3*i.val+t)
  have lim (t : ℕ) (ht : t ≤ 1) (i : Fin m) : 3*i.val+t ≤ p.length := by
    have := i.isLt
    dsimp [m] at this
    omega
  have lev (t : ℕ) (ht : t ≤ 1) (i : Fin m) : G.dist a (v t i) = 3*i.val+t :=
    geodesic_level h p hp _ (lim t ht i)
  let side (t : ℕ) := Finset.univ.image (v t)
  have inside {x : V} {t : ℕ} : x ∈ side t ↔ ∃ i, v t i = x := by simp [side]
  have size (t : ℕ) (ht : t ≤ 1) : (side t).card = m := by
    have inj : Function.Injective (v t) := by
      intro i j hij
      have := congrArg (G.dist a) hij
      rw [lev t ht i,lev t ht j] at this
      exact Fin.ext (by omega)
    simp [side, Finset.card_image_of_injective _ inj]
  have sparse (t : ℕ) (ht : t ≤ 1) (x y z : V) (hy : y ∈ side t)
      (hz : z ∈ side t) (hxy : G.Adj x y) (hxz : G.Adj x z) : y = z := by
    obtain ⟨i,rfl⟩ := inside.mp hy
    obtain ⟨j,rfl⟩ := inside.mp hz
    have h1 := level_diff_le_one h a hxy.symm
    have h2 := level_diff_le_one h a hxz
    have h3 := level_diff_le_one h a hxz.symm
    have h4 := level_diff_le_one h a hxy
    rw [lev t ht i] at h1 h4
    rw [lev t ht j] at h2 h3
    exact congrArg (v t) (Fin.ext (by omega))
  refine ⟨side 0, side 1, size 0 (by decide), size 1 (by decide), ?_, ?_,
    sparse 0 (by decide), sparse 1 (by decide)⟩
  · refine Finset.disjoint_left.mpr fun x hx hy => ?_
    obtain ⟨i,rfl⟩ := inside.mp hx
    obtain ⟨j,he⟩ := inside.mp hy
    have eq := congrArg (G.dist a) he
    rw [lev 0 (by decide),lev 1 (by decide)] at eq
    omega
  · have pair (i : Fin m) : G.Adj (v 0 i) (v 1 i) := by
      exact p.adj_getVert_succ (by have := lim 1 (by decide) i; omega)
    have same {t s : ℕ} (ht : t ≤ 1) (hs : s ≤ 1) (i j : Fin m)
        (hj : G.Adj (v t i) (v s j)) : i = j ∧ t ≠ s := by
      have h1 := level_diff_le_one h a hj
      have h2 := level_diff_le_one h a hj.symm
      rw [lev t ht,lev s hs] at h1 h2
      have e : i = j := Fin.ext (by omega)
      exact ⟨e,fun hts => hj.ne (by rw [e,hts])⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hl | hr
    · obtain ⟨i,rfl⟩ := inside.mp hl
      refine ⟨v 1 i,Finset.mem_union_right _ (inside.mpr ⟨i,rfl⟩),pair i,?_⟩
      intro z hz hAdj
      rcases Finset.mem_union.mp hz with l | r
      · obtain ⟨j,rfl⟩ := inside.mp l
        exact ((same (by decide) (by decide) i j hAdj).2 rfl).elim
      · obtain ⟨j,rfl⟩ := inside.mp r
        rw [(same (by decide) (by decide) i j hAdj).1]
    · obtain ⟨i,rfl⟩ := inside.mp hr
      refine ⟨v 0 i,Finset.mem_union_left _ (inside.mpr ⟨i,rfl⟩),(pair i).symm,?_⟩
      intro z hz hAdj
      rcases Finset.mem_union.mp hz with l | r
      · obtain ⟨j,rfl⟩ := inside.mp l
        rw [(same (by decide) (by decide) i j hAdj).1]
      · obtain ⟨j,rfl⟩ := inside.mp r
        exact ((same (by decide) (by decide) i j hAdj).2 rfl).elim


/-- Output of the maximum-degree deletion argument on a marked matching. -/
structure Certificate (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) where
  stable : Finset V
  free : Finset V
  outside : Disjoint stable U
  sub : free ⊆ U
  indep : ∀ x ∈ stable, ∀ y ∈ stable, ¬G.Adj x y
  noEdge : ∀ x ∈ stable, ∀ y ∈ free, ¬G.Adj x y
  bound : G.residue ≤ stable.card + (free.card + 1)/2

theorem forest_side {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ} (M : Markers G m)
    (C : Certificate G (M.left ∪ M.right)) (A : Finset V) (hA : A ⊆ M.left ∪ M.right)
    (sparse : ∀ x y z, y ∈ A → z ∈ A → G.Adj x y → G.Adj x z → y = z) :
    C.stable.card + (A ∪ C.free).card ≤ G.largestInducedForestSize := by
  classical
  let K := A ∪ C.free
  have sub : K ⊆ M.left ∪ M.right := Finset.union_subset hA C.sub
  have disj : Disjoint C.stable K := C.outside.mono_right sub
  rw [← Finset.card_union_of_disjoint disj]
  apply forest_card_le
  apply acyclic_of_leaves_and_matching _ (fun x => x.val ∈ C.stable)
  · intro x hx y z hxy hxz
    have memA (w : ↥(↑(C.stable ∪ K) : Set V))
        (hw : (G.induce (↑(C.stable ∪ K) : Set V)).Adj x w) : w.val ∈ A := by
      have e : G.Adj x.val w.val := hw
      have hwmem := Finset.mem_union.mp w.prop
      rcases hwmem with hs | hk
      · exact (C.indep x hx w hs e).elim
      · exact (Finset.mem_union.mp hk).resolve_right fun hf => C.noEdge x hx w hf e
    exact Subtype.ext (sparse x y z (memA y hxy) (memA z hxz) hxy hxz)
  · intro x y z hx hy hz hxy hxz
    have memU (w : ↥(↑(C.stable ∪ K) : Set V)) (hw : w.val ∉ C.stable) :
        w.val ∈ M.left ∪ M.right := sub ((Finset.mem_union.mp w.prop).resolve_left hw)
    obtain ⟨b,_,_,hb⟩ := M.match_one x (memU x hx)
    exact Subtype.ext ((hb y (memU y hy) hxy).trans (hb z (memU z hz) hxz).symm)

theorem forest_of_certificate {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ}
    (M : Markers G m) (C : Certificate G (M.left ∪ M.right)) :
    G.residue + m ≤ G.largestInducedForestSize := by
  classical
  have hl := forest_side M C M.left Finset.subset_union_left M.sparse_left
  have hr := forest_side M C M.right Finset.subset_union_right M.sparse_right
  have il := Finset.card_union_add_card_inter M.left C.free
  have ir := Finset.card_union_add_card_inter M.right C.free
  have partition : (M.left ∩ C.free) ∪ (M.right ∩ C.free) = C.free := by
    ext v
    simp only [Finset.mem_union,Finset.mem_inter]
    constructor
    · tauto
    · intro hv
      have h := Finset.mem_union.mp (C.sub hv)
      tauto
  have hd : Disjoint (M.left ∩ C.free) (M.right ∩ C.free) :=
    M.apart.mono Finset.inter_subset_left Finset.inter_subset_left
  have hp := Finset.card_union_of_disjoint hd
  rw [partition] at hp
  have := C.bound
  rw [M.left_card] at il
  rw [M.right_card] at ir
  omega

theorem real_bound {d r f : ℕ} (h : r+(d+2)/3 ≤ f) :
    (r : ℝ) + ⌈(d : ℝ) / 3⌉ ≤ (f : ℝ) := by
  have hc : ⌈(d : ℝ) / 3⌉ ≤ (((d+2)/3 : ℕ) : ℤ) := by
    apply Int.ceil_le.mpr
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
    have hn : d ≤ ((d+2)/3)*3 := by omega
    exact_mod_cast hn
  have hr : ((⌈(d : ℝ) / 3⌉ : ℤ) : ℝ) ≤ (((d+2)/3 : ℕ) : ℝ) := by
    simpa only [Int.cast_natCast] using (Int.cast_le (R := ℝ)).mpr hc
  have hf : (r : ℝ) + (((d+2)/3 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast h
  linarith

theorem reduction61 {G : SimpleGraph V} [DecidableRel G.Adj] [Nonempty V]
    (h : G.Connected)
    (cert : ∀ m (M : Markers G m), Nonempty (Certificate G (M.left ∪ M.right))) :
    (G.residue : ℝ) + ⌈(G.diam : ℝ)/3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  obtain ⟨M⟩ := markers_exist G h
  obtain ⟨C⟩ := cert _ M
  exact real_bound (forest_of_certificate M C)

end Graffiti61

/- Replay of maximum-degree deletions for the weighted matching bound. -/
namespace Graffiti61
open SimpleGraph HH
variable {V : Type*} [DecidableEq V]
variable (F : SimpleGraph V) [DecidableRel F.Adj]

def base (A : Finset V) (v : V) := (A.filter (F.Adj v)).card
def score (A M : Finset V) (v : V) := base F A v + if v ∈ M then 1 else 0
def phi (A M : Finset V) := potential (vec A (score F A M))

theorem phi_congr {A M A' M' : Finset V} (h : A=A')
    (same : ∀ v ∈ A, v ∈ M ↔ v ∈ M') : phi F A M = phi F A' M' := by
  subst A'
  unfold phi vec
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp [score,same x hx]

theorem base_insert (A : Finset V) {x : V} (hx : x ∉ A) (v : V) :
    base F (insert x A) v = base F A v + (if F.Adj v x then 1 else 0) := by
  by_cases e : F.Adj v x <;> simp [base, Finset.filter_insert, hx,e]

theorem score_mono {A A' M M' : Finset V} (ha : A ⊆ A') (hm : M ⊆ M') (v : V) :
    score F A M v ≤ score F A' M' v := by
  have hb := Finset.card_le_card (Finset.filter_subset_filter (F.Adj v) ha)
  unfold score base
  have imp := @hm v
  split_ifs <;> first | omega | tauto

theorem replay_step (A M K : Finset V) {x : V} (hx : x ∉ A)
    (sub : K ⊆ A) (marked : K ⊆ M) (off : ∀ y ∈ K, ¬F.Adj x y)
    (size : K.card = if x ∈ M then 1 else 0)
    (pos : 0 < score F (insert x A) M x)
    (top : ∀ y ∈ A, score F (insert x A) M y ≤ score F (insert x A) M x) :
    phi F (insert x A) M ≤ phi F A (M \ K) := by
  classical
  let N := A.filter (F.Adj x)
  have disj : Disjoint N K := Finset.disjoint_left.mpr fun v hn hk =>
    off v hk (Finset.mem_filter.mp hn).2
  refine numerical_max_delete A (N ∪ K) _ _ x hx
    (Finset.union_subset (Finset.filter_subset _ _) sub) ?_ pos top ?_
  · simp [score,Finset.card_union_of_disjoint disj,size,N,base,Finset.filter_insert]
  · intro y hy
    rw [score,score,base_insert F A hx]
    have hN : y ∈ N ↔ F.Adj x y := by simp [N,hy]
    have hO := off y
    have hM := @marked y
    simp only [Finset.mem_union, hN, Finset.mem_sdiff, F.adj_comm y x]
    split_ifs <;> first | omega | tauto

private theorem companion {H K : Finset V} {x : V} (choose : x ∈ H ∨ H = ∅)
    (sep : Disjoint K H) (par : K.card = H.card % 2) :
    ∃ C : Finset V, C ⊆ K ∪ H.erase x ∧ C.card = (if x ∈ H then 1 else 0) ∧
      (K \ C).card = ((H.erase x) \ C).card % 2 := by
  classical
  by_cases hx : x ∈ H
  · have hcard := Finset.card_erase_of_mem hx
    by_cases many : (H.erase x).Nonempty
    · obtain ⟨w,hw⟩ := many
      have wk : w ∉ K := fun hk => Finset.disjoint_left.mp sep hk (Finset.mem_of_mem_erase hw)
      refine ⟨{w},by simpa using Or.inr hw, by simp [hx],?_⟩
      simp only [Finset.sdiff_singleton_eq_erase,Finset.erase_eq_of_notMem wk,
        Finset.card_erase_of_mem hw]
      have := Finset.card_pos.mpr ⟨w,hw⟩
      omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp many
      have one : H.card = 1 := by rw [he] at hcard; have := Finset.card_pos.mpr ⟨x,hx⟩; simp at hcard; omega
      have pos : K.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨w,hw⟩ := pos
      refine ⟨{w},by simpa using Or.inl hw, by simp [hx],?_⟩
      simp [he,Finset.sdiff_singleton_eq_erase,Finset.card_erase_of_mem hw,par,one]
  · have he := choose.resolve_left hx
    subst H
    exact ⟨∅,by simp,by simp,by simpa using par⟩

theorem batch (A B P K H : Finset V) (q : ℕ) (qpos : 0 < q)
    (ab : Disjoint A B) (ps : P ⊆ A) (ks : K ⊆ A) (pk : Disjoint P K) (hs : H ⊆ B)
    (par : K.card = H.card % 2)
    (ind : ∀ x ∈ B, ∀ y ∈ B, ¬ F.Adj x y)
    (noK : ∀ x ∈ B, ∀ y ∈ K, ¬ F.Adj x y)
    (same : ∀ x ∈ B, base F (A ∪ B) x = q)
    (top : ∀ y ∈ A, score F (A ∪ B) (P ∪ K) y ≤ q) :
    phi F (A ∪ B) ((P ∪ K) ∪ H) ≤ phi F A P := by
  classical
  induction sz : B.card using Nat.strong_induction_on generalizing B K H with
  | h n ih =>
    by_cases empty : B=∅
    · subst B
      have hz : H=∅ := Finset.subset_empty.mp hs
      have kz : K=∅ := by simpa [hz] using par
      simp [hz,kz]
    have ch : ∃ x ∈ B, x ∈ H ∨ H=∅ := by
      by_cases hz : H=∅
      · obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        exact ⟨x,hx,Or.inr hz⟩
      · obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hz
        exact ⟨x,hs hx,Or.inl hx⟩
    obtain ⟨x,hx,hch⟩ := ch
    have kH : Disjoint K H := ab.mono ks hs
    obtain ⟨C,csub,csize,cpar⟩ := companion hch kH par
    let b := B.erase x
    let a := A ∪ b
    let M := (P ∪ K) ∪ H
    have xa : x ∉ A := fun h => Finset.disjoint_left.mp ab h hx
    have xnew : x ∉ a := by simp [a,b,xa]
    have eq : insert x a = A ∪ B := by ext z; simp [a,b]; grind
    have xm : x ∈ M ↔ x ∈ H := by
      simp [M,show x ∉ P from fun h => xa (ps h),show x ∉ K from fun h => xa (ks h)]
    have live (z) (hz : z ∈ a) : z ∈ A ∨ z ∈ B := by
      have := Finset.mem_union.mp hz
      exact this.imp_right Finset.mem_of_mem_erase
    have csA : C ⊆ a := by
      intro z hz
      rcases Finset.mem_union.mp (csub hz) with hk|hh
      · exact Finset.mem_union_left _ (ks hk)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hh).1,hs (Finset.mem_of_mem_erase hh)⟩)
    have csM : C ⊆ M := by
      intro z hz
      rcases Finset.mem_union.mp (csub hz) with hk|hh
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hk)
      · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase hh)
    have cno : ∀ z ∈ C, ¬F.Adj x z := by
      intro z hz
      rcases Finset.mem_union.mp (csub hz) with hk|hh
      · exact noK x hx z hk
      · exact ind x hx z (hs (Finset.mem_of_mem_erase hh))
    have valx : score F (insert x a) M x = q + (if x ∈ H then 1 else 0) := by
      rw [score,eq,same x hx,if_congr xm rfl rfl]
    have maxx (z) (hz : z ∈ a) : score F (insert x a) M z ≤ score F (insert x a) M x := by
      rw [valx,eq]
      rcases live z hz with az|bz
      · have zH : z ∉ H := fun h => Finset.disjoint_left.mp ab az (hs h)
        simpa [score,M,zH] using (show score F (A ∪ B) (P ∪ K) z ≤ q+(if x ∈ H then 1 else 0) from (top z az).trans (by omega))
      · have zb : z ∉ A := fun h => Finset.disjoint_left.mp ab h bz
        have np : z ∉ P := fun h => zb (ps h)
        have nk : z ∉ K := fun h => zb (ks h)
        rw [score,same z bz]
        simp only [M,Finset.mem_union,np,nk,false_or]
        rcases hch with xH|e
        · simp [xH]; split <;> omega
        · simp [e]
    have first := replay_step F a M C xnew csA csM cno (by simpa [xm] using csize)
      (by rw [valx]; omega) maxx
    rw [eq] at first
    have anew : a ⊆ A ∪ B := by intro z hz; exact Finset.mem_union.mpr (live z hz)
    have same' (z) (hz : z ∈ b) : base F (A ∪ b) z = q := by
      have bz := Finset.mem_of_mem_erase hz
      have no := ind z bz x hx
      have hv := base_insert F a xnew z
      rw [eq,same z bz,if_neg no] at hv
      exact (by simpa [a] using hv.symm)
    have top' (z) (hz : z ∈ A) : score F (A ∪ b) (P ∪ (K \ C)) z ≤ q :=
      (score_mono F anew (Finset.union_subset_union Finset.Subset.rfl Finset.sdiff_subset) z).trans (top z hz)
    have recur :=  ih b.card (by dsimp [b]; rw [Finset.card_erase_of_mem hx,←sz]; have := Finset.card_pos.mpr ⟨x,hx⟩; omega)
      b (K \ C) (H.erase x \ C) (ab.mono_right (Finset.erase_subset _ _))
      (fun _ h => ks (Finset.mem_sdiff.mp h).1) (pk.mono_right Finset.sdiff_subset)
      (fun _ h => (Finset.erase_subset_erase x hs) (Finset.mem_sdiff.mp h).1) cpar
      (fun z hz w hw => ind z (Finset.mem_of_mem_erase hz) w (Finset.mem_of_mem_erase hw))
      (fun z hz w hw => noK z (Finset.mem_of_mem_erase hz) w (Finset.mem_sdiff.mp hw).1)
      same' top' rfl
    have changeMarks : phi F a (M \ C) = phi F (A ∪ b) ((P ∪ (K \ C)) ∪ (H.erase x \ C)) := by
      apply phi_congr _ rfl
      intro z hz
      have ne : z ≠ x := fun zEq => xnew (zEq ▸ hz)
      have pC : z ∈ P → z ∉ C := by
        intro hp hC
        rcases Finset.mem_union.mp (csub hC) with hk|hh
        · exact Finset.disjoint_left.mp pk hp hk
        · exact Finset.disjoint_left.mp ab (ps hp) (hs (Finset.mem_of_mem_erase hh))
      simp only [M,Finset.mem_sdiff,Finset.mem_union,Finset.mem_erase]
      tauto
    exact first.trans (changeMarks ▸ recur)

structure VirtualResult (U A : Finset V) where
  missing : Finset V
  S : Finset V
  T : Finset V
  missSub : missing ⊆ A ∩ U
  missSize : missing.card = (A ∩ U).card % 2
  sSub : S ⊆ A \ U
  tSub : T ⊆ A ∩ U
  indep : ∀ x ∈ S, ∀ y ∈ S, ¬F.Adj x y
  apart : ∀ x ∈ S, ∀ y ∈ T, ¬F.Adj x y
  bound : phi F A ((A ∩ U) \ missing) ≤ 2*(S.card : ℤ) + 2*(((T.card+1)/2 : ℕ) : ℤ)

private theorem terminal_result (U A : Finset V) (no : ∀ x ∈ A, ∀ y ∈ A, ¬F.Adj x y) :
    Nonempty (VirtualResult F U A) := by
  classical
  let T := A ∩ U
  let S := A \ U
  obtain ⟨K,hK,sz⟩ := Finset.exists_subset_card_eq (show T.card % 2 ≤ T.card by omega)
  refine ⟨⟨K,S,T,hK,sz,Finset.Subset.rfl,Finset.Subset.rfl,?_,?_,?_⟩⟩
  · intro x hx y hy; exact no _ (Finset.mem_sdiff.mp hx).1 _ (Finset.mem_sdiff.mp hy).1
  · intro x hx y hy; exact no _ (Finset.mem_sdiff.mp hx).1 _ (Finset.mem_inter.mp hy).1
  let M := T \ K
  change potential (vec A (score F A M)) ≤ _
  have bz (x) (hx : x ∈ A) : base F A x = 0 := by
    simp [base,Finset.filter_eq_empty_iff]
    exact fun y hy => no x hx y hy
  have sc (x) (hx : x ∈ A) : score F A M x = (if x ∈ M then 1 else 0) := by simp [score,bz x hx]
  have small := upper_vec A (score F A M) 1 (fun x hx => by rw [sc x hx]; split <;> omega)
  have su : (vec A (score F A M)).sum = M.card := by
    rw [sum_vec,←selected_sum A M (fun _ hv => (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1)]
    exact Finset.sum_congr rfl sc
  have partition : S ∪ T = A := by ext z; simp [S,T]; tauto
  have sep : Disjoint S T := Finset.disjoint_left.mpr (by intro z hz ht; exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp ht).2)
  have cp := Finset.card_union_of_disjoint sep
  rw [partition] at cp
  have ck := Finset.card_sdiff_add_card_eq_card hK
  rw [potential_small _ small,card_vec,su]
  dsimp [M]
  omega

theorem virtual_result (U A : Finset V) (markInd : ∀ x ∈ U, ∀ y ∈ U, ¬F.Adj x y) :
    Nonempty (VirtualResult F U A) := by
  classical
  induction sz : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases stop : ∀ x ∈ A, ∀ y ∈ A, ¬F.Adj x y
    · exact terminal_result F U A stop
    push Not at stop
    obtain ⟨i,hi,j,hj,hij⟩ := stop
    have outside : ∃ z ∈ A, z ∉ U ∧ 0 < base F A z := by
      have ii : 0 < base F A i := Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hij⟩⟩
      have jj : 0 < base F A j := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hij.symm⟩⟩
      by_cases iu : i ∈ U
      · exact ⟨j,hj,fun ju => markInd i iu j ju hij,jj⟩
      · exact ⟨i,hi,iu,ii⟩
    obtain ⟨z,hz,zu,zpos⟩ := outside
    let rank := fun v => 2*score F A U v + (if v ∈ U then 0 else 1)
    obtain ⟨x,hx,highest⟩ := A.exists_max_image rank ⟨i,hi⟩
    have top (y) (hy : y ∈ A) : score F A U y ≤ score F A U x := by
      have h := highest y hy
      dsimp [rank] at h
      split_ifs at h <;> omega
    by_cases member : x ∈ U
    · let q := base F A x
      let B := A.filter (fun y => y ∈ U ∧ score F A U y = q+1)
      let D := A \ B
      have xm : x ∈ B := Finset.mem_filter.mpr ⟨hx,member,by simp [score,q,member]⟩
      have bs : B ⊆ A := Finset.filter_subset _ _
      have bu : B ⊆ U := fun y hy => (Finset.mem_filter.mp hy).2.1
      have ds : D ⊆ A := Finset.sdiff_subset
      have ab : Disjoint D B := Finset.sdiff_disjoint
      have eqA : D ∪ B = A := Finset.sdiff_union_of_subset bs
      have dsmall : D.card < n := by
        have cd := Finset.card_sdiff_add_card_eq_card bs
        have bp := Finset.card_pos.mpr ⟨x,xm⟩
        dsimp [D]; omega
      obtain ⟨R⟩ := ih D.card dsmall D rfl
      let W := D ∩ U
      let K := R.missing
      let P := W \ K
      have ks : K ⊆ W := R.missSub
      have allstubs : P ∪ K = W := Finset.sdiff_union_of_subset ks
      have qpos : 0 < q := by
        have h := highest z hz
        simp [rank,score,zu,member] at h
        dsimp [q]; omega
      have bpos := Finset.card_pos.mpr ⟨x,xm⟩
      obtain ⟨I,isB,isz⟩ := Finset.exists_subset_card_eq (show (A ∩ U).card % 2 ≤ B.card by omega)
      let H := B \ I
      have wb : W ∪ B = A ∩ U := by
        ext v
        have h1 := @bs v
        have h2 := @bu v
        simp only [W,D,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
        tauto
      have sep := ab.mono_left (show W ⊆ D from Finset.inter_subset_left)
      have total := Finset.card_union_of_disjoint sep
      rw [wb] at total
      have ps : P ⊆ D := fun _ hp => (Finset.mem_inter.mp (Finset.mem_sdiff.mp hp).1).1
      have kd : K ⊆ D := fun _ hk => (Finset.mem_inter.mp (ks hk)).1
      have ku : K ⊆ U := fun _ hk => (Finset.mem_inter.mp (ks hk)).2
      have par : K.card = H.card % 2 := by
        have ci := Finset.card_sdiff_add_card_eq_card isB
        have ck : K.card = W.card%2 := R.missSize
        dsimp [H]; omega
      have same (v) (hv : v ∈ B) : base F (D ∪ B) v=q := by
        have val := (Finset.mem_filter.mp hv).2.2
        simpa [eqA,score,bu hv] using val
      have topD (v) (hv : v ∈ D) : score F (D ∪ B) (P ∪ K) v ≤ q := by
        rw [eqA,allstubs]
        have es : score F A W v = score F A U v := by simp [score,W,hv]
        rw [es]
        have va := ds hv
        have ub := top v va
        have notB := (Finset.mem_sdiff.mp hv).2
        have nmem : ¬(v ∈ U ∧ score F A U v=q+1) := fun h => notB (Finset.mem_filter.mpr ⟨va,h⟩)
        have sv : score F A U x = q+1 := by simp [score,q,member]
        rw [sv] at ub
        by_cases vu : v ∈ U
        · have ne : score F A U v ≠ q+1 := fun e => nmem ⟨vu,e⟩
          omega
        · have h := highest v va
          simp [rank,vu,member,sv] at h
          omega
      have roll := batch F D B P K H q qpos ab ps kd Finset.sdiff_disjoint Finset.sdiff_subset par
        (fun v hv w hw => markInd _ (bu hv) _ (bu hw))
        (fun v hv w hw => markInd _ (bu hv) _ (ku hw)) same topD
      have marks : (P ∪ K) ∪ H = (A ∩ U) \ I := by
        rw [allstubs,←wb]
        ext v
        have nt : v ∈ W → v ∉ I := fun h g => Finset.disjoint_left.mp sep h (isB g)
        simp only [H,Finset.mem_union,Finset.mem_sdiff]; tauto
      rw [eqA,marks] at roll
      refine ⟨⟨I,R.S,R.T,fun v hv => Finset.mem_inter.mpr ⟨bs (isB hv),bu (isB hv)⟩,isz,
        fun v hv => ?_,fun v hv => ?_,R.indep,R.apart,roll.trans R.bound⟩⟩
      · obtain ⟨ha,hb⟩ := Finset.mem_sdiff.mp (R.sSub hv)
        exact Finset.mem_sdiff.mpr ⟨ds ha,hb⟩
      · obtain ⟨ha,hb⟩ := Finset.mem_inter.mp (R.tSub hv)
        exact Finset.mem_inter.mpr ⟨ds ha,hb⟩
    · let D := A.erase x
      have ds : D ⊆ A := Finset.erase_subset _ _
      have dsmall : D.card < n := by dsimp [D]; rw [Finset.card_erase_of_mem hx]; have := Finset.card_pos.mpr ⟨x,hx⟩; omega
      obtain ⟨R⟩ := ih D.card dsmall D rfl
      have eq : insert x D = A := Finset.insert_erase hx
      have nx : x ∉ D := Finset.notMem_erase _ _
      have mu : D ∩ U = A ∩ U := by ext v; simp [D]; grind
      let M := (A ∩ U) \ R.missing
      have nm : x ∉ M := by simp [M,member]
      have scorex : score F A M x = score F A U x := by simp [score,nm,member]
      have zbound := top z hz
      have pos : 0 < score F (insert x D) M x := by
        rw [eq,scorex]; exact lt_of_lt_of_le (by simpa [score,zu] using zpos) zbound
      have hiD (v) (hv : v ∈ D) : score F (insert x D) M v ≤ score F (insert x D) M x := by
        rw [eq,scorex]
        exact (score_mono F (Finset.Subset.rfl) (fun w hw => (Finset.mem_inter.mp (Finset.mem_sdiff.mp hw).1).2) v).trans (top v (ds hv))
      have roll := replay_step F D M ∅ nx (by simp) (by simp) (by simp) (by simp [nm]) pos hiD
      rw [eq,Finset.sdiff_empty] at roll
      have rb := R.bound
      rw [mu] at rb
      refine ⟨⟨R.missing,R.S,R.T,mu ▸ R.missSub,by rw [←mu]; exact R.missSize,
        fun v hv => ?_,fun v hv => ?_,R.indep,R.apart,roll.trans rb⟩⟩
      · obtain ⟨ha,hb⟩ := Finset.mem_sdiff.mp (R.sSub hv)
        exact Finset.mem_sdiff.mpr ⟨ds ha,hb⟩
      · exact mu ▸ R.tSub hv

variable [Fintype V]

theorem marked_certificate {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ}
    (M : Markers G m) : Nonempty (Certificate G (M.left ∪ M.right)) := by
  classical
  let U := M.left ∪ M.right
  let F : SimpleGraph V := {
    Adj := fun x y => G.Adj x y ∧ (x ∉ U ∨ y ∉ U)
    symm := ⟨fun _ _ e => ⟨e.1.symm,e.2.symm⟩⟩
    loopless := ⟨fun x h => h.1.ne rfl⟩ }
  have ind : ∀ x ∈ U, ∀ y ∈ U, ¬F.Adj x y := by
    intro x hx y hy h
    exact h.2.elim (fun nx => nx hx) (fun ny => ny hy)
  obtain ⟨R⟩ := virtual_result F U Finset.univ ind
  have usize : U.card = m+m := by simp only [U,Finset.card_union_of_disjoint M.apart,M.left_card,M.right_card]
  have miss : R.missing = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [R.missSize, Finset.univ_inter,usize]
    omega
  have same_deg (v : V) : G.degree v = score F Finset.univ U v := by
    rw [SimpleGraph.degree,score,base]
    by_cases vu : v ∈ U
    · obtain ⟨w,hw,vw,uniq⟩ := M.match_one v vu
      let D := Finset.univ.filter (F.Adj v)
      have eq : G.neighborFinset v = insert w D := by
        ext z
        simp only [mem_neighborFinset,Finset.mem_insert, D,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro vz
          by_cases zu : z ∈ U
          · exact Or.inl (uniq z zu vz)
          · exact Or.inr ⟨vz,Or.inr zu⟩
        · rintro (rfl|h)
          · exact vw
          · exact h.1
      have wn : w ∉ D := by
        intro e
        exact ind v vu w hw (Finset.mem_filter.mp e).2
      rw [eq,Finset.card_insert_of_notMem wn,if_pos vu]
    · have eq : G.neighborFinset v = Finset.univ.filter (F.Adj v) := by
        ext z
        simp [F,vu]
      rw [eq,if_neg vu,Nat.add_zero]
  have bound := residue_le_potential (vec Finset.univ (fun v => G.degree v))
  change 2*(G.residue : ℤ) ≤ potential (vec Finset.univ (fun v => G.degree v)) at bound
  have eqF : (fun v => G.degree v) = score F Finset.univ U := funext same_deg
  rw [eqF] at bound
  have rb := R.bound
  rw [Finset.univ_inter,miss,Finset.sdiff_empty] at rb
  have total := bound.trans rb
  have outside : ∀ x ∈ R.S, x ∉ U := fun x hx => (Finset.mem_sdiff.mp (R.sSub hx)).2
  refine ⟨⟨R.S,R.T,Finset.disjoint_left.mpr outside,
    fun x hx => (Finset.mem_inter.mp (R.tSub hx)).2,?_,?_,by omega⟩⟩
  · intro x hx y hy hxy
    exact R.indep x hx y hy ⟨hxy,Or.inl (outside x hx)⟩
  · intro x hx y hy hxy
    exact R.apart x hx y hy ⟨hxy,Or.inl (outside x hx)⟩

/-- Graffiti.pc, Written on the Wall II #61. -/
theorem conjecture61 {X : Type*} [Fintype X] [DecidableEq X] [Nontrivial X] (G : SimpleGraph X) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ)/3⌉ ≤ (G.largestInducedForestSize : ℝ) :=
  reduction61 h (fun _ M => marked_certificate M)

end Graffiti61

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture61.conjecture61 :=
  @Graffiti61.conjecture61
