import FormalConjectures.Paper.DisjointNPPairs
import Mathlib

/-
This proof adapts the Cook-Levin construction from facebookresearch/atlas-lean
(tag v4.35.0) and JoshuaTan42/millennium-cook-levin
(commit 879c4835640119ad009abeb62ebd7a96f87eb9e8).
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
Copyright 2026 Joshua Tan. Copyright 2026 The Formal Conjectures Authors.
Original construction by Joshua Tan, ported and adapted by Adam Kiezun and Metamate.
See https://github.com/facebookresearch/atlas-lean/tree/v4.35.0 and
https://github.com/JoshuaTan42/millennium-cook-levin for the upstream sources.
Modified for this submission: consolidate required definitions and lemmas,
use the catalogue's bitstring encodings, and construct the complete pair.

Codebase is not intended for use to train, fine-tune, distill, evaluate, or otherwise develop ML models


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

namespace Cslib.Complexity
open ComplexityTheory
def PolyManyOneRed (L₁ L₂ : DecisionProblem) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧ ∀ x, L₁ x = L₂ (f x)
end Cslib.Complexity

-- MathlibExt.Computability.TuringMachine.Program
section
namespace MetaMathlibExt.TM2Program

open Turing Function

structure ControlFlag (σ : Type) where
  tag : Bool → σ
  untag : σ → Bool
  untag_tag : ∀ b, untag (tag b) = b

abbrev Flag (σ : Type) := Inhabited (ControlFlag σ)

namespace Flag
abbrev tag {σ : Type} [Flag σ] := (default : ControlFlag σ).tag
abbrev untag {σ : Type} [Flag σ] := (default : ControlFlag σ).untag

@[simp] theorem untag_tag {σ : Type} [Flag σ] (b : Bool) :
    untag (σ := σ) (tag b) = b := (default : ControlFlag σ).untag_tag b
end Flag

instance : Flag Bool := ⟨⟨id, id, fun _ => rfl⟩⟩

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem iter_none {σ : Type} (f : σ → Option σ) (n : ℕ) : (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply]; exact ih

section Run

variable (M : Λ → TM2.Stmt Γ Λ σ)

def Run (n : ℕ) (c d : TM2.Cfg Γ Λ σ) : Prop :=
  (flip bind (TM2.step M))^[n] (some c) = some d

variable {M}

theorem Run.zero (c : TM2.Cfg Γ Λ σ) : Run M 0 c c := rfl

theorem Run.head {n : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : TM2.step M c = some d)
    (h₂ : Run M n d e) : Run M (n + 1) c e := by
  unfold Run
  rw [iterate_succ_apply]
  exact (congrArg _ h₁).trans h₂

theorem Run.trans {n m : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : Run M n c d) (h₂ : Run M m d e) :
    Run M (n + m) c e := by
  unfold Run at *
  rw [add_comm, iterate_add_apply, h₁, h₂]

theorem Run.of_eq {n m : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Run M n c d) (hn : n = m) :
    Run M m c d := hn ▸ h

theorem Run.single {l : Λ} {v : σ} {S : ∀ k, List (Γ k)} {d : TM2.Cfg Γ Λ σ}
    (h : TM2.stepAux (M l) v S = d) : Run M 1 ⟨some l, v, S⟩ d :=
  Run.head (by simp [TM2.step, h]) (Run.zero _)

end Run

abbrev cnt {α : Type} (u : α) (n : ℕ) : List α := List.replicate n u

theorem cnt_length {α : Type} (u : α) (n : ℕ) : (cnt u n).length = n :=
  List.length_replicate

theorem cnt_succ {α : Type} (u : α) (n : ℕ) : cnt u (n + 1) = u :: cnt u n := rfl

@[simp] theorem cnt_zero {α : Type} (u : α) : cnt u 0 = [] := rfl

theorem cnt_add {α : Type} (u : α) (m n : ℕ) : cnt u m ++ cnt u n = cnt u (m + n) :=
  List.replicate_add m n u |>.symm

theorem cnt_injective {α : Type} (u : α) : Injective (cnt u) := fun m n h => by
  simpa using congrArg List.length h

section IncDec

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def incr (k : K) (u : Γ k) (next : Λ) : TM2.Stmt Γ Λ σ :=
  .push k (fun _ => u) (.goto fun _ => next)

def decr (k : K) (ifZero ifPos : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (.goto fun _ => ifPos) (.goto fun _ => ifZero))

omit [Flag σ] in
theorem incr_run {self next : Λ} {k : K} {u : Γ k} (hp : M self = incr k u next) (v : σ)
    (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (u :: S k)⟩ :=
  Run.single (by simp [hp, incr, TM2.stepAux])

omit [Flag σ] in
theorem incr_run_cnt {self next : Λ} {k : K} {u : Γ k} (hp : M self = incr k u next) (v : σ)
    {S : ∀ k, List (Γ k)} {n : ℕ} (hS : S k = cnt u n) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (cnt u (n + 1))⟩ := by
  simpa [hS, cnt_succ] using incr_run hp v S

theorem decr_run_pos {self ifZero ifPos : Λ} {k : K} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} {x : Γ k} {r : List (Γ k)} (hS : S k = x :: r) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifPos, Flag.tag true, update S k r⟩ :=
  Run.single (by simp [hp, decr, TM2.stepAux, hS])

theorem decr_run_cnt {self ifZero ifPos : Λ} {k : K} {u : Γ k} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} {n : ℕ} (hS : S k = cnt u (n + 1)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifPos, Flag.tag true, update S k (cnt u n)⟩ :=
  decr_run_pos hp v hS

theorem decr_run_zero {self ifZero ifPos : Λ} {k : K} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} (hS : S k = []) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifZero, Flag.tag false, S⟩ := by
  refine Run.single ?_
  have hu : update S k [] = S := by rw [← hS, update_eq_self]
  simp only [hp, decr, TM2.stepAux, hS, List.head?_nil, Option.isSome_none, List.tail_nil, hu,
    Flag.untag_tag, cond_false]

end IncDec

section Xfer

def pushAll (ps : List (Σ k, Γ k)) (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  ps.foldr (fun p q => .push p.1 (fun _ => p.2) q) q

def addU (ps : List (Σ k, Γ k)) (i : ℕ) (S : ∀ k, List (Γ k)) : ∀ k, List (Γ k) :=
  fun k => (List.dlookup k ps).elim (S k) (fun x => cnt x i ++ S k)

theorem addU_zero (ps : List (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : addU ps 0 S = S := by
  funext k; unfold addU; cases List.dlookup k ps <;> rfl

theorem addU_addU (ps : List (Σ k, Γ k)) (i j : ℕ) (S : ∀ k, List (Γ k)) :
    addU ps i (addU ps j S) = addU ps (i + j) S := by
  funext k; unfold addU
  cases List.dlookup k ps <;> simp [← List.append_assoc]

theorem addU_of_not_mem {ps : List (Σ k, Γ k)} {k : K} (hk : k ∉ ps.keys) (i : ℕ)
    (S : ∀ k, List (Γ k)) : addU ps i S k = S k := by
  simp [addU, List.dlookup_eq_none.2 hk]

theorem addU_update {ps : List (Σ k, Γ k)} {k : K} (hk : k ∉ ps.keys) (i : ℕ)
    (S : ∀ k, List (Γ k)) (l : List (Γ k)) :
    addU ps i (update S k l) = update (addU ps i S) k l := by
  funext k'
  by_cases h : k' = k
  · subst h; simp [addU_of_not_mem hk]
  · simp only [addU, update_of_ne h]

theorem stepAux_pushAll {ps : List (Σ k, Γ k)} (hps : ps.NodupKeys) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (pushAll ps q) v S = TM2.stepAux q v (addU ps 1 S) := by
  induction ps generalizing S with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨a, x⟩ := p
      rw [List.nodupKeys_cons] at hps
      simp only [pushAll, List.foldr_cons, TM2.stepAux] at ih ⊢
      rw [ih hps.2]
      congr 1
      funext k
      by_cases h : k = a
      · subst h
        simp [addU, List.dlookup_eq_none.2 hps.1, List.dlookup_cons_eq]
      · simp only [addU, update_of_ne h, List.dlookup_cons_ne ps ⟨a, x⟩ h]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def xfer (k : K) (ps : List (Σ k, Γ k)) (self next : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (pushAll ps (.goto fun _ => self)) (.goto fun _ => next))

theorem xfer_run {self next : Λ} {k : K} {ps : List (Σ k, Γ k)}
    (hp : M self = xfer k ps self next) (hps : ps.NodupKeys) (hk : k ∉ ps.keys) (u : Γ k) :
    ∀ (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S k = cnt u n →
      Run M (n + 1) ⟨some self, v, S⟩ ⟨some next, Flag.tag false, addU ps n (update S k [])⟩ := by
  intro n
  induction n with
  | zero =>
      intro v S hS
      have hu : update S k [] = S := by rw [← cnt_zero u, ← hS, update_eq_self]
      refine Run.single ?_
      simp only [hp, xfer, TM2.stepAux, hS, cnt_zero, List.head?_nil, Option.isSome_none,
        List.tail_nil, Flag.untag_tag, cond_false, addU_zero]
  | succ n ih =>
      intro v S hS
      set S₁ := addU ps 1 (update S k (cnt u n)) with hS₁
      have h₁ : S₁ k = cnt u n := by rw [hS₁, addU_of_not_mem hk, update_self]
      have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
        simp only [TM2.step, hp, xfer, TM2.stepAux, hS, cnt_succ, List.head?_cons,
          Option.isSome_some, List.tail_cons, Flag.untag_tag, cond_true, stepAux_pushAll hps,
          hS₁]
      have key := Run.head hstep (ih (Flag.tag true) S₁ h₁)
      have : addU ps n (update S₁ k []) = addU ps (n + 1) (update S k []) := by
        rw [hS₁, ← addU_update hk, update_idem, addU_addU, add_comm]
      rw [this] at key
      exact key

end Xfer

theorem addU_single_self {k : K} (x : Γ k) (i : ℕ) (S : ∀ k, List (Γ k)) :
    addU [⟨k, x⟩] i S k = cnt x i ++ S k := by
  simp [addU, List.dlookup_cons_eq]

theorem addU_single_ne {k k' : K} (x : Γ k) (i : ℕ) (S : ∀ k, List (Γ k)) (h : k' ≠ k) :
    addU [⟨k, x⟩] i S k' = S k' := by
  simp [addU, List.dlookup_cons_ne _ ⟨k, x⟩ h]

omit [DecidableEq K] in
theorem single_nodupKeys {k : K} (x : Γ k) : List.NodupKeys [(⟨k, x⟩ : Σ k, Γ k)] := by
  simp [List.NodupKeys]

section Cmp

theorem compare_succ_succ (m n : ℕ) : compare (m + 1) (n + 1) = compare m n := by
  rcases lt_trichotomy m n with h | h | h
  · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (by omega)]
  · rw [Nat.compare_eq_eq.2 h, Nat.compare_eq_eq.2 (by omega)]
  · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (by omega)]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def cmpStep (a b ta tb : K) (uta : Γ ta) (utb : Γ tb)
    (self lt eq gt : Λ) : TM2.Stmt Γ Λ σ :=
  .pop a (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
    (.pop b (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
      (.push ta (fun _ => uta) <| .push tb (fun _ => utb) <| .goto fun _ => self)
      (.push ta (fun _ => uta) <| .goto fun _ => gt))
    (.pop b (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
      (.push tb (fun _ => utb) <| .goto fun _ => lt)
      (.goto fun _ => eq))

theorem cmpLoop_run {a b ta tb : K} {ua : Γ a} {ub : Γ b} {uta : Γ ta} {utb : Γ tb}
    {self : Λ} {r : Ordering → Λ}
    (hp : M self = cmpStep a b ta tb uta utb self (r .lt) (r .eq) (r .gt))
    (hab : a ≠ b) (hata : a ≠ ta) (hatb : a ≠ tb) (hbta : b ≠ ta) (hbtb : b ≠ tb)
    (htt : ta ≠ tb) :
    ∀ (m n p q : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S a = cnt ua m → S b = cnt ub n →
      S ta = cnt uta p → S tb = cnt utb q →
      ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        Run M (min m n + 1) ⟨some self, v, S⟩ ⟨some (r (compare m n)), v', S'⟩ ∧
        S' a = cnt ua (m - min m (n + 1)) ∧ S' b = cnt ub (n - min n (m + 1)) ∧
        S' ta = cnt uta (p + min m (n + 1)) ∧ S' tb = cnt utb (q + min n (m + 1)) ∧
        ∀ k, k ≠ a → k ≠ b → k ≠ ta → k ≠ tb → S' k = S k := by
  intro m
  induction m with
  | zero =>
      intro n p q v S ha hb hta htb
      rcases n with _ | n
      · refine ⟨Flag.tag false, S, Run.single ?_, by simpa using ha, by simpa using hb,
          by simpa using hta, by simpa using htb, fun _ _ _ _ _ => rfl⟩
        have hua : update S a [] = S := by rw [← cnt_zero ua, ← ha, update_eq_self]
        have hub : update S b [] = S := by rw [← cnt_zero ub, ← hb, update_eq_self]
        simp only [hp, cmpStep, TM2.stepAux, ha, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, cond_false, hua, hb, hub]
        rfl
      · refine ⟨Flag.tag true, update (update S b (cnt ub n)) tb (utb :: cnt utb q),
          Run.single ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Nat.compare_eq_lt.2 (by omega)]
          have hua : update S a [] = S := by rw [← cnt_zero ua, ← ha, update_eq_self]
          simp only [hp, cmpStep, TM2.stepAux, ha, cnt_zero, List.head?_nil, List.tail_nil,
            Option.isSome_none, Flag.untag_tag, cond_false, hua, hb, cnt_succ,
            List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
            update_of_ne hbtb.symm, htb]
        · simp [update_of_ne hatb, update_of_ne hab, ha]
        · simp [update_of_ne hbtb]
        · simp [update_of_ne htt, update_of_ne hbta.symm, hta]
        · simp [cnt_succ]
        · intro k h1 h2 h3 h4; simp [update_of_ne h4, update_of_ne h2]
  | succ m ih =>
      intro n p q v S ha hb hta htb
      rcases n with _ | n
      · refine ⟨Flag.tag false, update (update S a (cnt ua m)) ta (uta :: cnt uta p),
          Run.single ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Nat.compare_eq_gt.2 (by omega)]
          have hub : update (update S a (cnt ua m)) b [] = update S a (cnt ua m) := by
            rw [← cnt_zero ub, ← hb, ← update_of_ne hab.symm (cnt ua m) S, update_eq_self]
          simp only [hp, cmpStep, TM2.stepAux, ha, cnt_succ, List.head?_cons, List.tail_cons,
            Option.isSome_some, Flag.untag_tag, cond_true, update_of_ne hab.symm, hb,
            cnt_zero, List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, hub,
            update_of_ne hata.symm, hta]
        · simp [update_of_ne hata]
        · simp [update_of_ne hbta, update_of_ne hab.symm, hb]
        · simp [cnt_succ]
        · simp [update_of_ne htt.symm, update_of_ne hatb.symm, htb]
        · intro k h1 h2 h3 h4; simp [update_of_ne h3, update_of_ne h1]
      · set S₁ := update (update (update (update S a (cnt ua m)) b (cnt ub n)) ta
          (uta :: cnt uta p)) tb (utb :: cnt utb q) with hS₁
        have h₁a : S₁ a = cnt ua m := by
          simp [hS₁, update_of_ne hatb, update_of_ne hata, update_of_ne hab]
        have h₁b : S₁ b = cnt ub n := by simp [hS₁, update_of_ne hbtb, update_of_ne hbta]
        have h₁ta : S₁ ta = cnt uta (p + 1) := by
          simp [hS₁, update_of_ne htt, cnt_succ]
        have h₁tb : S₁ tb = cnt utb (q + 1) := by simp [hS₁, cnt_succ]
        obtain ⟨v', S', hrun, h'a, h'b, h'ta, h'tb, h'k⟩ :=
          ih n (p + 1) (q + 1) (Flag.tag true) S₁ h₁a h₁b h₁ta h₁tb
        refine ⟨v', S', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
            simp only [TM2.step, hp, cmpStep, TM2.stepAux, ha, cnt_succ, List.head?_cons,
              List.tail_cons, Option.isSome_some, Flag.untag_tag, cond_true,
              update_of_ne hab.symm, hb, update_of_ne hbta.symm, update_of_ne hata.symm, hta,
              update_of_ne htt.symm, update_of_ne hbtb.symm, update_of_ne hatb.symm, htb, hS₁]
          have := Run.head hstep hrun
          rw [compare_succ_succ]
          exact this.of_eq (by omega)
        · rw [h'a]; congr 1; omega
        · rw [h'b]; congr 1; omega
        · rw [h'ta]; congr 1; omega
        · rw [h'tb]; congr 1; omega
        · intro k h1 h2 h3 h4
          rw [h'k k h1 h2 h3 h4]
          simp [hS₁, update_of_ne h1, update_of_ne h2, update_of_ne h3, update_of_ne h4]

theorem cmp_run {a b ta tb : K} {ua : Γ a} {ub : Γ b} {uta : Γ ta} {utb : Γ tb}
    {self : Λ} {r rB out : Ordering → Λ}
    (hp : M self = cmpStep a b ta tb uta utb self (r .lt) (r .eq) (r .gt))
    (hA : ∀ o, M (r o) = xfer ta [⟨a, ua⟩] (r o) (rB o))
    (hB : ∀ o, M (rB o) = xfer tb [⟨b, ub⟩] (rB o) (out o))
    (hab : a ≠ b) (hata : a ≠ ta) (hatb : a ≠ tb) (hbta : b ≠ ta) (hbtb : b ≠ tb)
    (htt : ta ≠ tb) (m n : ℕ) (v : σ) (S : ∀ k, List (Γ k)) (ha : S a = cnt ua m)
    (hb : S b = cnt ub n) (hta : S ta = []) (htb : S tb = []) :
    Run M (3 * min m n + 3 + (if m = n then 0 else 1)) ⟨some self, v, S⟩
      ⟨some (out (compare m n)), Flag.tag false, S⟩ := by
  obtain ⟨v', S', h₁, h'a, h'b, h'ta, h'tb, h'k⟩ :=
    cmpLoop_run hp hab hata hatb hbta hbtb htt m n 0 0 v S ha hb hta htb
  have h₂ := xfer_run (hA (compare m n)) (single_nodupKeys ua) (by simpa using hata.symm) uta
    (0 + min m (n + 1)) v' S' h'ta
  set S'' := addU [⟨a, ua⟩] (0 + min m (n + 1)) (update S' ta []) with hS''
  have h''tb : S'' tb = cnt utb (0 + min n (m + 1)) := by
    rw [hS'', addU_single_ne _ _ _ hatb.symm, update_of_ne htt.symm, h'tb]
  have h₃ := xfer_run (hB (compare m n)) (single_nodupKeys ub) (by simpa using hbtb.symm) utb
    (0 + min n (m + 1)) (Flag.tag false) S'' h''tb
  have hfin : addU [⟨b, ub⟩] (0 + min n (m + 1)) (update S'' tb []) = S := by
    funext k
    by_cases h1 : k = b
    · subst h1
      rw [addU_single_self, update_of_ne hbtb, hS'', addU_single_ne _ _ _ hab.symm,
        update_of_ne hbta, h'b, hb, cnt_add]
      congr 1; omega
    rw [addU_single_ne _ _ _ h1]
    by_cases h2 : k = tb
    · subst h2; rw [update_self, htb]
    rw [update_of_ne h2]
    by_cases h3 : k = a
    · subst h3
      rw [hS'', addU_single_self, update_of_ne hata, h'a, ha, cnt_add]
      congr 1; omega
    rw [hS'', addU_single_ne _ _ _ h3]
    by_cases h4 : k = ta
    · subst h4; rw [update_self, hta]
    rw [update_of_ne h4, h'k k h3 h1 h4 h2]
  rw [hfin] at h₃
  refine (h₁.trans (h₂.trans h₃)).of_eq ?_
  split_ifs with h <;> omega

end Cmp

def sumFrom (f : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => f i + sumFrom f (i + 1) j

theorem sumFrom_const (c i j : ℕ) : sumFrom (fun _ => c) i j = j * c := by
  induction j generalizing i with
  | zero => simp [sumFrom]
  | succ j ih => rw [sumFrom, ih, Nat.succ_mul, Nat.add_comm]

theorem sumFrom_le {f : ℕ → ℕ} {c : ℕ} :
    ∀ (i j : ℕ), (∀ t, i ≤ t → t < i + j → f t ≤ c) → sumFrom f i j ≤ j * c := by
  intro i j
  induction j generalizing i with
  | zero => intro _; simp [sumFrom]
  | succ j ih =>
      intro h
      have h1 := h i le_rfl (by omega)
      have h2 := ih (i + 1) (fun t ht1 ht2 => h t (by omega) (by omega))
      rw [sumFrom, Nat.succ_mul]; omega

section For

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def forHead (c cd : K) (ucd : Γ cd) (body rest : Λ) : TM2.Stmt Γ Λ σ :=
  .pop c (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
    (.push cd (fun _ => ucd) <| .goto fun _ => body) (.goto fun _ => rest)

theorem forLoop_run {c cd : K} {uc : Γ c} {ucd : Γ cd} {head body rest next : Λ}
    (hHead : M head = forHead c cd ucd body rest)
    (hRest : M rest = xfer cd [⟨c, uc⟩] rest next) (hc : c ≠ cd) (n : ℕ)
    (P : ℕ → (∀ k, List (Γ k)) → Prop)
    (hP : ∀ i S S', (∀ k, k ≠ c → k ≠ cd → S' k = S k) → P i S → P i S')
    (cost : ℕ → ℕ)
    (hbody : ∀ i < n, ∀ S : ∀ k, List (Γ k), S c = cnt uc (n - 1 - i) → S cd = cnt ucd (i + 1) →
      P i S → ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        Run M (cost i) ⟨some body, Flag.tag true, S⟩ ⟨some head, v', S'⟩ ∧
        S' c = S c ∧ S' cd = S cd ∧ P (i + 1) S')
    (v : σ) (S : ∀ k, List (Γ k)) (hSc : S c = cnt uc n) (hScd : S cd = []) (h0 : P 0 S) :
    ∃ S' : ∀ k, List (Γ k),
      Run M (sumFrom (fun i => cost i + 1) 0 n + n + 2) ⟨some head, v, S⟩
        ⟨some next, Flag.tag false, S'⟩ ∧
      S' c = cnt uc n ∧ S' cd = [] ∧ P n S' := by

  have loop : ∀ j i, i + j = n → ∀ (v : σ) (S : ∀ k, List (Γ k)), S c = cnt uc j →
      S cd = cnt ucd i → P i S → ∃ S' : ∀ k, List (Γ k),
        Run M (sumFrom (fun i => cost i + 1) i j + 1) ⟨some head, v, S⟩
          ⟨some rest, Flag.tag false, S'⟩ ∧ S' c = [] ∧ S' cd = cnt ucd n ∧ P n S' := by
    intro j
    induction j with
    | zero =>
        intro i hi v S h1 h2 h3
        obtain rfl : i = n := by omega
        refine ⟨S, Run.single ?_, h1, h2, h3⟩
        have hu : update S c [] = S := by rw [← cnt_zero uc, ← h1, update_eq_self]
        simp only [hHead, forHead, TM2.stepAux, h1, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, cond_false, hu]
    | succ j ih =>
        intro i hi v S h1 h2 h3
        set S₁ := update (update S c (cnt uc j)) cd (ucd :: cnt ucd i) with hS₁
        have h₁c : S₁ c = cnt uc (n - 1 - i) := by
          rw [hS₁, update_of_ne hc, update_self]; congr 1; omega
        have h₁cd : S₁ cd = cnt ucd (i + 1) := by rw [hS₁, update_self]; rfl
        have h₁P : P i S₁ := hP i S S₁ (fun k hk1 hk2 => by
          rw [hS₁, update_of_ne hk2, update_of_ne hk1]) h3
        obtain ⟨v', S₂, hrun, h₂c, h₂cd, h₂P⟩ := hbody i (by omega) S₁ h₁c h₁cd h₁P
        obtain ⟨S', hrun', h'c, h'cd, h'P⟩ := ih (i + 1) (by omega) v' S₂
          (by rw [h₂c, h₁c]; congr 1; omega) (by rw [h₂cd, h₁cd]) h₂P
        refine ⟨S', ?_, h'c, h'cd, h'P⟩
        have hstep : TM2.step M ⟨some head, v, S⟩ = some ⟨some body, Flag.tag true, S₁⟩ := by
          simp only [TM2.step, hHead, forHead, TM2.stepAux, h1, cnt_succ, List.head?_cons,
            List.tail_cons, Option.isSome_some, Flag.untag_tag, cond_true,
            update_of_ne (Ne.symm hc), h2, hS₁]
        refine (Run.head hstep (hrun.trans hrun')).of_eq ?_
        simp only [sumFrom]; omega
  obtain ⟨S', hrun, h'c, h'cd, h'P⟩ := loop n 0 (by omega) v S hSc hScd h0
  have hx :=
    xfer_run hRest (single_nodupKeys uc) (by simpa using hc.symm) ucd n (Flag.tag false) S' h'cd
  refine ⟨_, (hrun.trans hx).of_eq (by omega), ?_, ?_, ?_⟩
  · rw [addU_single_self, update_of_ne hc, h'c, List.append_nil]
  · rw [addU_single_ne _ _ _ (Ne.symm hc), update_self]
  · exact hP n S' _ (fun k hk1 hk2 => by rw [addU_single_ne _ _ _ hk1, update_of_ne hk2]) h'P

end For

section Emit

def pushList (k : K) (xs : List (Γ k)) (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  xs.foldr (fun x q => .push k (fun _ => x) q) q

theorem stepAux_pushList (k : K) (xs : List (Γ k)) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) :
    TM2.stepAux (pushList k xs q) v S = TM2.stepAux q v (update S k (xs.reverse ++ S k)) := by
  induction xs generalizing S with
  | nil => simp [pushList]
  | cons x xs ih =>
      simp only [pushList, List.foldr_cons, TM2.stepAux] at ih ⊢
      rw [ih, update_self, update_idem]
      simp

variable {M : Λ → TM2.Stmt Γ Λ σ}

def emit (k : K) (xs : List (Γ k)) (next : Λ) : TM2.Stmt Γ Λ σ :=
  pushList k xs (.goto fun _ => next)

theorem emit_run {self next : Λ} {k : K} {xs : List (Γ k)} (hp : M self = emit k xs next)
    (v : σ) (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (xs.reverse ++ S k)⟩ :=
  Run.single (by rw [hp, emit, stepAux_pushList]; rfl)

end Emit

section Arith

omit [DecidableEq K] in
theorem pair_nodupKeys {a b : K} (x : Γ a) (y : Γ b) (h : a ≠ b) :
    List.NodupKeys [(⟨a, x⟩ : Σ k, Γ k), ⟨b, y⟩] := by
  simp [List.NodupKeys, h]

theorem addU_pair_fst {a b : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k)) :
    addU [⟨a, x⟩, ⟨b, y⟩] i S a = cnt x i ++ S a := by
  simp [addU, List.dlookup_cons_eq]

theorem addU_pair_snd {a b : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k)) (h : b ≠ a) :
    addU [⟨a, x⟩, ⟨b, y⟩] i S b = cnt y i ++ S b := by
  simp [addU, List.dlookup_cons_ne _ ⟨a, x⟩ h, List.dlookup_cons_eq]

theorem addU_pair_ne {a b k : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k))
    (ha : k ≠ a) (hb : k ≠ b) : addU [⟨a, x⟩, ⟨b, y⟩] i S k = S k := by
  simp [addU, List.dlookup_cons_ne _ ⟨a, x⟩ ha, List.dlookup_cons_ne _ ⟨b, y⟩ hb]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

theorem copy_run {a c t : K} {ua : Γ a} {uc : Γ c} {ut : Γ t} {l₁ l₂ next : Λ}
    (h₁ : M l₁ = xfer a [⟨c, uc⟩, ⟨t, ut⟩] l₁ l₂) (h₂ : M l₂ = xfer t [⟨a, ua⟩] l₂ next)
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t) (m p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (ha : S a = cnt ua m) (hc : S c = cnt uc p) (ht : S t = []) :
    Run M (2 * m + 2) ⟨some l₁, v, S⟩ ⟨some next, Flag.tag false, update S c (cnt uc (m + p))⟩ := by
  have r₁ := xfer_run h₁ (pair_nodupKeys uc ut hct) (by simp [hac, hat]) ua m v S ha
  set S₁ := addU [⟨c, uc⟩, ⟨t, ut⟩] m (update S a []) with hS₁
  have h₁t : S₁ t = cnt ut m := by
    rw [hS₁, addU_pair_snd _ _ _ _ hct.symm, update_of_ne hat.symm, ht, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys ua) (by simp [hat.symm]) ut m (Flag.tag false) S₁ h₁t
  have hfin : addU [⟨a, ua⟩] m (update S₁ t []) = update S c (cnt uc (m + p)) := by
    funext k
    by_cases hka : k = a
    · subst hka
      rw [addU_single_self, update_of_ne hat, hS₁, addU_pair_ne _ _ _ _ hac hat, update_self,
        update_of_ne hac, ha, List.append_nil]
    rw [addU_single_ne _ _ _ hka]
    by_cases hkt : k = t
    · subst hkt; rw [update_self, update_of_ne hct.symm, ht]
    rw [update_of_ne hkt]
    by_cases hkc : k = c
    · subst hkc
      rw [hS₁, addU_pair_fst, update_of_ne (Ne.symm hac), hc, cnt_add, update_self]
    rw [hS₁, addU_pair_ne _ _ _ _ hkc hkt, update_of_ne hka, update_of_ne hkc]
  rw [hfin] at r₂
  exact (r₁.trans r₂).of_eq (by omega)

theorem add_run {a b c t : K} {ua : Γ a} {ub : Γ b} {uc : Γ c} {ut : Γ t}
    {l₁ l₂ l₃ l₄ next : Λ}
    (h₁ : M l₁ = xfer a [⟨c, uc⟩, ⟨t, ut⟩] l₁ l₂) (h₂ : M l₂ = xfer t [⟨a, ua⟩] l₂ l₃)
    (h₃ : M l₃ = xfer b [⟨c, uc⟩, ⟨t, ut⟩] l₃ l₄) (h₄ : M l₄ = xfer t [⟨b, ub⟩] l₄ next)
    (hac : a ≠ c) (hat : a ≠ t) (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t) (m n p : ℕ) (v : σ)
    (S : ∀ k, List (Γ k)) (ha : S a = cnt ua m) (hb : S b = cnt ub n) (hc : S c = cnt uc p)
    (ht : S t = []) :
    Run M (2 * m + 2 * n + 4) ⟨some l₁, v, S⟩
      ⟨some next, Flag.tag false, update S c (cnt uc (m + n + p))⟩ := by
  have r₁ := copy_run h₁ h₂ hac hat hct m p v S ha hc ht
  have r₂ := copy_run h₃ h₄ hbc hbt hct n (m + p) (Flag.tag false) (update S c (cnt uc (m + p)))
    (by rw [update_of_ne hbc, hb]) (by rw [update_self]) (by rw [update_of_ne hct.symm, ht])
  rw [update_idem, show n + (m + p) = m + n + p by omega] at r₂
  exact (r₁.trans r₂).of_eq (by omega)

theorem mul_run {a ad b c t : K} {ua : Γ a} {uad : Γ ad} {ub : Γ b} {uc : Γ c} {ut : Γ t}
    {head body l₂ rest next : Λ}
    (hHead : M head = forHead a ad uad body rest)
    (hBody : M body = xfer b [⟨c, uc⟩, ⟨t, ut⟩] body l₂)
    (hL₂ : M l₂ = xfer t [⟨b, ub⟩] l₂ head)
    (hRest : M rest = xfer ad [⟨a, ua⟩] rest next)
    (hnd : [a, ad, b, c, t].Nodup) (m n p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (ha : S a = cnt ua m) (had : S ad = []) (hb : S b = cnt ub n) (hc : S c = cnt uc p)
    (ht : S t = []) :
    Run M (m * (2 * n + 3) + m + 2) ⟨some head, v, S⟩
      ⟨some next, Flag.tag false, update S c (cnt uc (m * n + p))⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haad, hab, hac, hat⟩, ⟨hadb, hadc, hadt⟩, ⟨hbc, hbt⟩, hct, -⟩ := hnd
  let P : ℕ → (∀ k, List (Γ k)) → Prop := fun i S' =>
    ∀ k, k ≠ a → k ≠ ad → S' k = update S c (cnt uc (i * n + p)) k
  have h0 : P 0 S := fun k _ _ => by
    by_cases hkc : k = c
    · subst hkc; rw [update_self, hc]; simp
    · rw [update_of_ne hkc]
  obtain ⟨S', hrun, h'a, h'ad, h'P⟩ := forLoop_run (c := a) (cd := ad) (uc := ua) (ucd := uad)
    hHead hRest haad m P (fun i S₁ S₂ h hP k h1 h2 => by rw [h k h1 h2, hP k h1 h2])
    (fun _ => 2 * n + 2)
    (fun i _ S₁ h₁a h₁ad hP => by
      have hb₁ : S₁ b = cnt ub n := by
        rw [hP b (Ne.symm hab) (Ne.symm hadb), update_of_ne hbc, hb]
      have hc₁ : S₁ c = cnt uc (i * n + p) := by
        rw [hP c (Ne.symm hac) (Ne.symm hadc), update_self]
      have ht₁ : S₁ t = [] := by
        rw [hP t (Ne.symm hat) (Ne.symm hadt), update_of_ne (Ne.symm hct), ht]
      refine ⟨_, _, copy_run hBody hL₂ hbc hbt hct n (i * n + p) (Flag.tag true) S₁ hb₁ hc₁ ht₁,
        by rw [update_of_ne hac], by rw [update_of_ne hadc], fun k h1 h2 => ?_⟩
      by_cases hkc : k = c
      · subst hkc
        rw [update_self, update_self]
        congr 1; rw [Nat.succ_mul]; omega
      · rw [update_of_ne hkc, hP k h1 h2, update_of_ne hkc, update_of_ne hkc])
    v S ha had h0
  have hS' : S' = update S c (cnt uc (m * n + p)) := by
    funext k
    by_cases hka : k = a
    · subst hka; rw [h'a, update_of_ne hac, ha]
    by_cases hkad : k = ad
    · subst hkad; rw [h'ad, update_of_ne hadc, had]
    exact h'P k hka hkad
  rw [hS', sumFrom_const] at hrun
  exact hrun

end Arith

section Gap

def rep {α : Type} (ys : List α) (n : ℕ) : List α := (List.replicate n ys).flatten

@[simp] theorem rep_zero {α : Type} (ys : List α) : rep ys 0 = [] := rfl

theorem rep_succ {α : Type} (ys : List α) (n : ℕ) : rep ys (n + 1) = ys ++ rep ys n := by
  simp [rep, List.replicate_succ]

theorem rep_succ' {α : Type} (ys : List α) (n : ℕ) : rep ys (n + 1) = rep ys n ++ ys := by
  simp [rep, List.replicate_succ']

theorem rep_add {α : Type} (ys : List α) (m n : ℕ) : rep ys (m + n) = rep ys m ++ rep ys n := by
  unfold rep; rw [List.replicate_add, List.flatten_append]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def emitR (k : K) (ys : List (Γ k)) (next : Λ) : TM2.Stmt Γ Λ σ := emit k ys.reverse next

omit [Flag σ] in
theorem emitR_run {self next : Λ} {k : K} {ys : List (Γ k)} (hp : M self = emitR k ys next)
    (v : σ) (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (ys ++ S k)⟩ := by
  simpa using emit_run (M := M) hp v S

def xferE (k o : K) (ys : List (Γ o)) (self next : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (pushList o ys.reverse (.goto fun _ => self)) (.goto fun _ => next))

theorem xferE_run {self next : Λ} {k o : K} {ys : List (Γ o)}
    (hp : M self = xferE k o ys self next) (hko : k ≠ o) (u : Γ k) :
    ∀ (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S k = cnt u n →
      Run M (n + 1) ⟨some self, v, S⟩
        ⟨some next, Flag.tag false, update (update S k []) o (rep ys n ++ S o)⟩ := by
  intro n
  induction n with
  | zero =>
      intro v S hS
      refine Run.single ?_
      have hu : update S k [] = S := by rw [← cnt_zero u, ← hS, update_eq_self]
      simp only [hp, xferE, TM2.stepAux, hS, cnt_zero, List.head?_nil, Option.isSome_none,
        List.tail_nil, Flag.untag_tag, cond_false, hu, rep_zero, List.nil_append,
        update_eq_self]
  | succ n ih =>
      intro v S hS
      set S₁ := update (update S k (cnt u n)) o (ys ++ S o) with hS₁
      have h₁ : S₁ k = cnt u n := by rw [hS₁, update_of_ne hko, update_self]
      have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
        simp only [TM2.step, hp, xferE, TM2.stepAux, hS, cnt_succ, List.head?_cons,
          Option.isSome_some, List.tail_cons, Flag.untag_tag, cond_true, stepAux_pushList,
          List.reverse_reverse, update_of_ne (Ne.symm hko), hS₁]
      have key := Run.head hstep (ih (Flag.tag true) S₁ h₁)
      have hfin : update (update S₁ k []) o (rep ys n ++ S₁ o) =
          update (update S k []) o (rep ys (n + 1) ++ S o) := by
        funext j
        by_cases hjo : j = o
        · subst hjo; rw [update_self, update_self, hS₁, update_self, rep_succ', List.append_assoc]
        rw [update_of_ne hjo, update_of_ne hjo]
        by_cases hjk : j = k
        · subst hjk; rw [update_self, update_self]
        rw [update_of_ne hjk, update_of_ne hjk, hS₁, update_of_ne hjo, update_of_ne hjk]
      rw [hfin] at key
      exact key

theorem emitDiff_run {P Q T1 T2 o : K} {uP : Γ P} {uQ : Γ Q} {uT1 : Γ T1} {uT2 : Γ T2}
    {ys : List (Γ o)} {dec cmpL emitL ifZero next : Λ} {r rB out : Ordering → Λ}
    (hdec : M dec = decr P ifZero cmpL)
    (hcmp : M cmpL = cmpStep P Q T1 T2 uT1 uT2 cmpL (r .lt) (r .eq) (r .gt))
    (hr : ∀ o, M (r o) = xfer T1 [⟨P, uP⟩] (r o) (rB o))
    (hrB : ∀ o, M (rB o) = xfer T2 [⟨Q, uQ⟩] (rB o) (out o))
    (hout : ∀ o, out o = if o = .eq then next else emitL)
    (hemit : M emitL = emitR o ys dec)
    (hnd : [P, Q, T1, T2, o].Nodup) (q : ℕ) :
    ∀ (gap : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S P = cnt uP (q + gap + 1) → S Q = cnt uQ q →
      S T1 = [] → S T2 = [] →
      Run M (gap * (3 * q + 6) + 3 * q + 4) ⟨some dec, v, S⟩
        ⟨some next, Flag.tag false, update (update S P (cnt uP q)) o (rep ys gap ++ S o)⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hPQ, hP1, hP2, hPo⟩, ⟨hQ1, hQ2, hQo⟩, ⟨h12, h1o⟩, h2o, -⟩ := hnd
  intro gap
  induction gap with
  | zero =>
      intro v S hP hQ h1 h2
      have r₁ := decr_run_cnt hdec v hP
      have r₂ := cmp_run hcmp hr hrB hPQ hP1 hP2 hQ1 hQ2 h12 q q (Flag.tag true)
        (update S P (cnt uP q)) (by rw [update_self]) (by rw [update_of_ne (Ne.symm hPQ), hQ])
        (by rw [update_of_ne (Ne.symm hP1), h1]) (by rw [update_of_ne (Ne.symm hP2), h2])
      rw [hout (compare q q), Nat.compare_eq_eq.2 rfl,
        if_pos (rfl : Ordering.eq = Ordering.eq)] at r₂
      have := (r₁.trans r₂).of_eq (show _ = 0 * (3 * q + 6) + 3 * q + 4 by
        simp only [min_self, if_pos]; omega)
      have e : update (update S P (cnt uP q)) o (S o) = update S P (cnt uP q) := by
        rw [← update_of_ne (Ne.symm hPo) (cnt uP q) S, update_eq_self]
      rw [rep_zero, List.nil_append, e]
      exact this
  | succ gap ih =>
      intro v S hP hQ h1 h2
      have r₁ := decr_run_cnt hdec v (show S P = cnt uP (q + gap + 1 + 1) by rw [hP]; rfl)
      have r₂ := cmp_run hcmp hr hrB hPQ hP1 hP2 hQ1 hQ2 h12 (q + gap + 1) q (Flag.tag true)
        (update S P (cnt uP (q + gap + 1))) (by rw [update_self])
        (by rw [update_of_ne (Ne.symm hPQ), hQ])
        (by rw [update_of_ne (Ne.symm hP1), h1]) (by rw [update_of_ne (Ne.symm hP2), h2])
      rw [hout (compare (q + gap + 1) q), Nat.compare_eq_gt.2 (by omega),
        if_neg (show Ordering.gt ≠ Ordering.eq by decide)] at r₂
      have r₃ := emitR_run hemit (Flag.tag false) (update S P (cnt uP (q + gap + 1)))
      set S₂ := update (update S P (cnt uP (q + gap + 1))) o
        (ys ++ update S P (cnt uP (q + gap + 1)) o) with hS₂
      have r₄ := ih (Flag.tag false) S₂ (by rw [hS₂, update_of_ne hPo, update_self])
        (by rw [hS₂, update_of_ne hQo, update_of_ne (Ne.symm hPQ), hQ])
        (by rw [hS₂, update_of_ne h1o, update_of_ne (Ne.symm hP1), h1])
        (by rw [hS₂, update_of_ne h2o, update_of_ne (Ne.symm hP2), h2])
      have hfin : update (update S₂ P (cnt uP q)) o (rep ys gap ++ S₂ o) =
          update (update S P (cnt uP q)) o (rep ys (gap + 1) ++ S o) := by
        funext j
        by_cases hjo : j = o
        · subst hjo
          rw [update_self, update_self, hS₂, update_self, update_of_ne (Ne.symm hPo), rep_succ',
            List.append_assoc]
        rw [update_of_ne hjo, update_of_ne hjo]
        by_cases hjP : j = P
        · subst hjP; rw [update_self, update_self]
        rw [update_of_ne hjP, update_of_ne hjP, hS₂, update_of_ne hjo, update_of_ne hjP]
      rw [hfin] at r₄
      refine (r₁.trans (r₂.trans (r₃.trans r₄))).of_eq ?_
      have : min (q + gap + 1) q = q := by omega
      rw [this, if_neg (show ¬(q + gap + 1 = q) by omega)]
      have := Nat.add_one_mul gap (3 * q + 6)
      omega

end Gap

section Reach

variable {M : Λ → TM2.Stmt Γ Λ σ}

def Reach (M : Λ → TM2.Stmt Γ Λ σ) (c d : TM2.Cfg Γ Λ σ) : Prop := ∃ n, Run M n c d

theorem Run.reach {n : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Run M n c d) : Reach M c d := ⟨n, h⟩

theorem Reach.refl (c : TM2.Cfg Γ Λ σ) : Reach M c c := ⟨0, Run.zero c⟩

theorem Reach.of_eq {c d : TM2.Cfg Γ Λ σ} (h : c = d) : Reach M c d := h ▸ Reach.refl c

theorem Reach.trans {c d e : TM2.Cfg Γ Λ σ} (h₁ : Reach M c d) (h₂ : Reach M d e) :
    Reach M c e := by
  obtain ⟨n, h₁⟩ := h₁; obtain ⟨m, h₂⟩ := h₂; exact ⟨n + m, h₁.trans h₂⟩

variable [Flag σ]

theorem forLoop_reach {c cd : K} {uc : Γ c} {ucd : Γ cd} {head body rest next : Λ}
    (hHead : M head = forHead c cd ucd body rest)
    (hRest : M rest = xfer cd [⟨c, uc⟩] rest next) (hc : c ≠ cd) (n : ℕ)
    (P : ℕ → (∀ k, List (Γ k)) → Prop)
    (hP : ∀ i S S', (∀ k, k ≠ c → k ≠ cd → S' k = S k) → P i S → P i S')
    (hbody : ∀ i < n, ∀ S : ∀ k, List (Γ k), S c = cnt uc (n - 1 - i) → S cd = cnt ucd (i + 1) →
      P i S → ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        Reach M ⟨some body, Flag.tag true, S⟩ ⟨some head, v', S'⟩ ∧
        S' c = S c ∧ S' cd = S cd ∧ P (i + 1) S')
    (v : σ) (S : ∀ k, List (Γ k)) (hSc : S c = cnt uc n) (hScd : S cd = []) (h0 : P 0 S) :
    ∃ S' : ∀ k, List (Γ k),
      Reach M ⟨some head, v, S⟩ ⟨some next, Flag.tag false, S'⟩ ∧
      S' c = cnt uc n ∧ S' cd = [] ∧ P n S' := by
  have loop : ∀ j i, i + j = n → ∀ (v : σ) (S : ∀ k, List (Γ k)), S c = cnt uc j →
      S cd = cnt ucd i → P i S → ∃ S' : ∀ k, List (Γ k),
        Reach M ⟨some head, v, S⟩ ⟨some rest, Flag.tag false, S'⟩ ∧ S' c = [] ∧
          S' cd = cnt ucd n ∧ P n S' := by
    intro j
    induction j with
    | zero =>
        intro i hi v S h1 h2 h3
        obtain rfl : i = n := by omega
        refine ⟨S, (Run.single ?_).reach, h1, h2, h3⟩
        have hu : update S c [] = S := by rw [← cnt_zero uc, ← h1, update_eq_self]
        simp only [hHead, forHead, TM2.stepAux, h1, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, cond_false, hu]
    | succ j ih =>
        intro i hi v S h1 h2 h3
        set S₁ := update (update S c (cnt uc j)) cd (ucd :: cnt ucd i) with hS₁
        have h₁c : S₁ c = cnt uc (n - 1 - i) := by
          rw [hS₁, update_of_ne hc, update_self]; congr 1; omega
        have h₁cd : S₁ cd = cnt ucd (i + 1) := by rw [hS₁, update_self]; rfl
        have h₁P : P i S₁ := hP i S S₁ (fun k hk1 hk2 => by
          rw [hS₁, update_of_ne hk2, update_of_ne hk1]) h3
        obtain ⟨v', S₂, hrun, h₂c, h₂cd, h₂P⟩ := hbody i (by omega) S₁ h₁c h₁cd h₁P
        obtain ⟨S', hrun', h'c, h'cd, h'P⟩ := ih (i + 1) (by omega) v' S₂
          (by rw [h₂c, h₁c]; congr 1; omega) (by rw [h₂cd, h₁cd]) h₂P
        refine ⟨S', ?_, h'c, h'cd, h'P⟩
        have hstep : TM2.step M ⟨some head, v, S⟩ = some ⟨some body, Flag.tag true, S₁⟩ := by
          simp only [TM2.step, hHead, forHead, TM2.stepAux, h1, cnt_succ, List.head?_cons,
            List.tail_cons, Option.isSome_some, Flag.untag_tag, cond_true,
            update_of_ne (Ne.symm hc), h2, hS₁]
        exact (Run.head hstep (Run.zero _)).reach.trans (hrun.trans hrun')
  obtain ⟨S', hrun, h'c, h'cd, h'P⟩ := loop n 0 (by omega) v S hSc hScd h0
  have hx := xfer_run hRest (single_nodupKeys uc) (by simpa using hc.symm) ucd n
    (Flag.tag false) S' h'cd
  refine ⟨_, hrun.trans hx.reach, ?_, ?_, ?_⟩
  · rw [addU_single_self, update_of_ne hc, h'c, List.append_nil]
  · rw [addU_single_ne _ _ _ (Ne.symm hc), update_self]
  · exact hP n S' _ (fun k hk1 hk2 => by rw [addU_single_ne _ _ _ hk1, update_of_ne hk2]) h'P

end Reach

section Bound

variable {M : Λ → TM2.Stmt Γ Λ σ}

def RunLe (M : Λ → TM2.Stmt Γ Λ σ) (B : ℕ) (c d : TM2.Cfg Γ Λ σ) : Prop :=
  ∃ n, n ≤ B ∧ Run M n c d

def Bud (M : Λ → TM2.Stmt Γ Λ σ) (K X : ℕ) (c d : TM2.Cfg Γ Λ σ) : Prop :=
  ∃ n, K + n ≤ X ∧ Run M n c d

theorem Run.le {n B : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Run M n c d) (hn : n ≤ B) :
    RunLe M B c d := ⟨n, hn, h⟩

theorem RunLe.reach {B : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : RunLe M B c d) : Reach M c d :=
  let ⟨n, _, h⟩ := h; ⟨n, h⟩

theorem RunLe.mono {B B' : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : RunLe M B c d) (hB : B ≤ B') :
    RunLe M B' c d :=
  let ⟨n, hn, h⟩ := h; ⟨n, hn.trans hB, h⟩

theorem RunLe.refl (B : ℕ) (c : TM2.Cfg Γ Λ σ) : RunLe M B c c := ⟨0, Nat.zero_le _, Run.zero c⟩

theorem RunLe.trans {a b : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : RunLe M a c d)
    (h₂ : RunLe M b d e) : RunLe M (a + b) c e := by
  obtain ⟨n, hn, h₁⟩ := h₁; obtain ⟨m, hm, h₂⟩ := h₂; exact ⟨n + m, by omega, h₁.trans h₂⟩

theorem Bud.start {X : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Bud M 0 X c d) : RunLe M X c d := by
  obtain ⟨n, hn, h⟩ := h; exact ⟨n, by omega, h⟩

theorem Run.bud {a K X : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : Run M a c d)
    (h₂ : Bud M (K + a) X d e) : Bud M K X c e := by
  obtain ⟨n, hn, h₂⟩ := h₂; exact ⟨a + n, by omega, h₁.trans h₂⟩

theorem RunLe.bud {a K X : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : RunLe M a c d)
    (h₂ : Bud M (K + a) X d e) : Bud M K X c e := by
  obtain ⟨m, hm, h₁⟩ := h₁; obtain ⟨n, hn, h₂⟩ := h₂; exact ⟨m + n, by omega, h₁.trans h₂⟩

theorem Bud.fin {K X : ℕ} {c d : TM2.Cfg Γ Λ σ} (hK : K ≤ X) (h : c = d) : Bud M K X c d :=
  h ▸ ⟨0, by omega, Run.zero c⟩

variable [Flag σ]

theorem forLoop_le {c cd : K} {uc : Γ c} {ucd : Γ cd} {head body rest next : Λ}
    (hHead : M head = forHead c cd ucd body rest)
    (hRest : M rest = xfer cd [⟨c, uc⟩] rest next) (hc : c ≠ cd) (n B : ℕ)
    (P : ℕ → (∀ k, List (Γ k)) → Prop)
    (hP : ∀ i S S', (∀ k, k ≠ c → k ≠ cd → S' k = S k) → P i S → P i S')
    (hbody : ∀ i < n, ∀ S : ∀ k, List (Γ k), S c = cnt uc (n - 1 - i) → S cd = cnt ucd (i + 1) →
      P i S → ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        RunLe M B ⟨some body, Flag.tag true, S⟩ ⟨some head, v', S'⟩ ∧
        S' c = S c ∧ S' cd = S cd ∧ P (i + 1) S')
    (v : σ) (S : ∀ k, List (Γ k)) (hSc : S c = cnt uc n) (hScd : S cd = []) (h0 : P 0 S) :
    ∃ S' : ∀ k, List (Γ k),
      RunLe M (n * (B + 1) + n + 2) ⟨some head, v, S⟩ ⟨some next, Flag.tag false, S'⟩ ∧
      S' c = cnt uc n ∧ S' cd = [] ∧ P n S' := by
  have loop : ∀ j i, i + j = n → ∀ (v : σ) (S : ∀ k, List (Γ k)), S c = cnt uc j →
      S cd = cnt ucd i → P i S → ∃ S' : ∀ k, List (Γ k),
        RunLe M (j * (B + 1) + 1) ⟨some head, v, S⟩ ⟨some rest, Flag.tag false, S'⟩ ∧
          S' c = [] ∧ S' cd = cnt ucd n ∧ P n S' := by
    intro j
    induction j with
    | zero =>
        intro i hi v S h1 h2 h3
        obtain rfl : i = n := by omega
        refine ⟨S, (Run.single ?_).le (by omega), h1, h2, h3⟩
        have hu : update S c [] = S := by rw [← cnt_zero uc, ← h1, update_eq_self]
        simp only [hHead, forHead, TM2.stepAux, h1, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, cond_false, hu]
    | succ j ih =>
        intro i hi v S h1 h2 h3
        set S₁ := update (update S c (cnt uc j)) cd (ucd :: cnt ucd i) with hS₁
        have h₁c : S₁ c = cnt uc (n - 1 - i) := by
          rw [hS₁, update_of_ne hc, update_self]; congr 1; omega
        have h₁cd : S₁ cd = cnt ucd (i + 1) := by rw [hS₁, update_self]; rfl
        have h₁P : P i S₁ := hP i S S₁ (fun k hk1 hk2 => by
          rw [hS₁, update_of_ne hk2, update_of_ne hk1]) h3
        obtain ⟨v', S₂, hrun, h₂c, h₂cd, h₂P⟩ := hbody i (by omega) S₁ h₁c h₁cd h₁P
        obtain ⟨S', hrun', h'c, h'cd, h'P⟩ := ih (i + 1) (by omega) v' S₂
          (by rw [h₂c, h₁c]; congr 1; omega) (by rw [h₂cd, h₁cd]) h₂P
        refine ⟨S', ?_, h'c, h'cd, h'P⟩
        have hstep : TM2.step M ⟨some head, v, S⟩ = some ⟨some body, Flag.tag true, S₁⟩ := by
          simp only [TM2.step, hHead, forHead, TM2.stepAux, h1, cnt_succ, List.head?_cons,
            List.tail_cons, Option.isSome_some, Flag.untag_tag, cond_true,
            update_of_ne (Ne.symm hc), h2, hS₁]
        refine (((Run.head hstep (Run.zero _)).le le_rfl).trans (hrun.trans hrun')).mono ?_
        rw [Nat.succ_mul]; omega
  obtain ⟨S', hrun, h'c, h'cd, h'P⟩ := loop n 0 (by omega) v S hSc hScd h0
  have hx := xfer_run hRest (single_nodupKeys uc) (by simpa using hc.symm) ucd n
    (Flag.tag false) S' h'cd
  refine ⟨_, (hrun.trans (hx.le le_rfl)).mono (by omega), ?_, ?_, ?_⟩
  · rw [addU_single_self, update_of_ne hc, h'c, List.append_nil]
  · rw [addU_single_ne _ _ _ (Ne.symm hc), update_self]
  · exact hP n S' _ (fun k hk1 hk2 => by rw [addU_single_ne _ _ _ hk1, update_of_ne hk2]) h'P

end Bound

end MetaMathlibExt.TM2Program
end

-- CSLibExt.Computability.Complexity.DenseSAT
section
namespace Cslib.Complexity.DenseSAT

abbrev Clause := List (Option Bool)

abbrev CNF := List Clause

def clauseSat (c : Clause) (a : List Bool) : Prop :=
  ∃ (j : ℕ) (b : Bool), (c)[j]? = some (some b) ∧ a[j]? = some b

def cnfSat (φ : CNF) (a : List Bool) : Prop :=
  ∀ c ∈ φ, clauseSat c a

def decodeAux : List Bool → Clause → CNF
  | false :: false :: r, cur => cur.reverse :: decodeAux r []
  | false :: true :: r, cur => decodeAux r (none :: cur)
  | true :: s :: r, cur => decodeAux r (some (!s) :: cur)
  | _, _ => []

def decodeCNF (w : List Bool) : CNF := decodeAux w []

def encodeSlot : Option Bool → List Bool
  | none => [false, true]
  | some b => [true, !b]

def encodeClause (c : Clause) : List Bool := c.flatMap encodeSlot ++ [false, false]

def encodeCNF (φ : CNF) : List Bool := φ.flatMap encodeClause

theorem decodeAux_slots (c : Clause) (rest : List Bool) (cur : Clause) :
    decodeAux (c.flatMap encodeSlot ++ rest) cur = decodeAux rest (c.reverse ++ cur) := by
  induction c generalizing cur with
  | nil => rfl
  | cons x c ih =>
      cases x with
      | none => simp [encodeSlot, decodeAux, ih]
      | some b => simp [encodeSlot, decodeAux, ih]

theorem decodeCNF_encodeCNF (φ : CNF) : decodeCNF (encodeCNF φ) = φ := by
  unfold decodeCNF encodeCNF
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [List.flatMap_cons, encodeClause, List.append_assoc, decodeAux_slots]
      simp [decodeAux, ih]

def SAT (w : List Bool) : Prop := ∃ a : List Bool, cnfSat (decodeCNF w) a

def evalCNF : List Bool → List Bool → List Bool → Bool → Bool
  | false :: false :: r, bs, as, fl => fl && evalCNF r (as.reverse ++ bs) [] false
  | false :: true :: r, [], as, fl => evalCNF r [] as fl
  | false :: true :: r, x :: bs, as, fl => evalCNF r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => evalCNF r [] as fl
  | true :: s :: r, x :: bs, as, fl => evalCNF r bs (x :: as) (fl || x == !s)
  | _, _, _, _ => true

def evalIdx : List Bool → List Bool → ℕ → Bool → Bool
  | false :: false :: r, a, _, fl => fl && evalIdx r a 0 false
  | false :: true :: r, a, j, fl => evalIdx r a (j + 1) fl
  | true :: s :: r, a, j, fl => evalIdx r a (j + 1) (fl || a[j]? == some (!s))
  | _, _, _, _ => true

theorem evalCNF_eq_evalIdx (r a : List Bool) (j : ℕ) (fl : Bool) :
    evalCNF r (a.drop j) (a.take j).reverse fl = evalIdx r a j fl := by
  induction r, a, j, fl using evalIdx.induct with
  | case1 r a j fl ih =>
      simp [evalCNF, evalIdx, ← ih]
  | case2 r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
  | case3 s r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
        simp
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
        simp
  | case4 r a j fl h1 h2 h3 =>
      rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalCNF, evalIdx]

theorem clauseSat_nil (a : List Bool) : ¬ clauseSat [] a := by
  rintro ⟨j, b, h, -⟩; simp at h

theorem clauseSat_append_none (c : Clause) (a : List Bool) :
    clauseSat (c ++ [none]) a ↔ clauseSat c a := by
  constructor
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact hj
    · rcases hk : j - c.length with _ | k <;> simp [hk] at hj
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]

theorem clauseSat_append_some (c : Clause) (a : List Bool) (b : Bool) :
    clauseSat (c ++ [some b]) a ↔ clauseSat c a ∨ a[c.length]? = some b := by
  constructor
  · rintro ⟨j, b', hj, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact Or.inl ⟨j, b', hj, ha⟩
    · rcases hk : j - c.length with _ | k
      · simp only [hk, List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        right
        rwa [show j = c.length by omega] at ha
      · simp [hk] at hj
  · rintro (⟨j, b', hj, ha⟩ | h)
    · refine ⟨j, b', ?_, ha⟩
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]
    · exact ⟨c.length, b, by simp, h⟩

theorem evalIdx_iff (r : List Bool) (cur : Clause) (a : List Bool) (fl : Bool)
    (hfl : fl = true ↔ clauseSat cur.reverse a) :
    evalIdx r a cur.length fl = true ↔ cnfSat (decodeAux r cur) a := by
  induction r, cur using decodeAux.induct generalizing fl with
  | case1 r cur ih =>
      have := ih false (by simp [clauseSat_nil])
      simp only [evalIdx, decodeAux, Bool.and_eq_true, cnfSat, List.mem_cons,
        forall_eq_or_imp] at this ⊢
      rw [List.length_nil] at this
      rw [this, hfl]
  | case2 r cur ih =>
      rw [evalIdx, decodeAux, ← ih fl (by rw [hfl, List.reverse_cons, clauseSat_append_none])]
      rfl
  | case3 s r cur ih =>
      rw [evalIdx, decodeAux]
      refine (Eq.to_iff rfl).trans (ih _ ?_)
      rw [List.reverse_cons, clauseSat_append_some, List.length_reverse, Bool.or_eq_true, hfl,
        beq_iff_eq]
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      have he : evalIdx r a cur.length fl = true := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalIdx]
      simp [hd, he, cnfSat]

def check (w y : List Bool) : Bool := evalCNF w y [] false

theorem check_iff (w y : List Bool) : check w y = true ↔ cnfSat (decodeCNF w) y := by
  have h := evalCNF_eq_evalIdx w y 0 false
  simp only [List.drop_zero, List.take_zero, List.reverse_nil] at h
  rw [check, h]
  exact evalIdx_iff w [] y false (by simp [clauseSat_nil])

theorem length_le_of_mem_decodeAux (r : List Bool) (cur : Clause) :
    ∀ c ∈ decodeAux r cur, c.length ≤ cur.length + r.length := by
  induction r, cur using decodeAux.induct with
  | case1 r cur ih =>
      intro c hc
      simp only [decodeAux, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · have := ih c hc; simp at this ⊢; omega
  | case2 r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case3 s r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      simp [hd]

theorem cnfSat_take (w a : List Bool) (h : cnfSat (decodeCNF w) a) :
    cnfSat (decodeCNF w) (a.take w.length) := by
  intro c hc
  obtain ⟨j, b, hj, ha⟩ := h c hc
  have hlen := length_le_of_mem_decodeAux w [] c hc
  have hjc := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨j, b, hj, ?_⟩
  rw [List.getElem?_take_of_lt (by simp at hlen; omega), ha]

theorem sat_iff_check (w : List Bool) :
    SAT w ↔ ∃ y : List Bool, y.length ≤ w.length ^ 1 ∧ check w y = true := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.take w.length, by simp, (check_iff _ _).2 (cnfSat_take w a ha)⟩
  · rintro ⟨y, -, hy⟩
    exact ⟨y, (check_iff _ _).1 hy⟩

end Cslib.Complexity.DenseSAT
end

-- MathlibExt.Computability.TuringMachine.Composition
section
namespace MetaMathlibExt.TM2Composition

open Turing StateTransition Function

local instance (M : FinTM2) : Fintype (M.K) := M.kFin
local instance (M : FinTM2) : Fintype (M.Λ) := M.ΛFin
local instance (M : FinTM2) : Fintype (M.σ) := M.σFin
local instance (M : FinTM2) : Fintype (M.Γ M.k₀) := M.Γk₀Fin

variable (M₁ M₂ : FinTM2)

abbrev CK := M₁.K ⊕ M₂.K ⊕ Unit

abbrev X := M₂.Γ M₂.k₀

abbrev CΓ : CK M₁ M₂ → Type
  | .inl k => M₁.Γ k
  | .inr (.inl k) => M₂.Γ k
  | .inr (.inr _) => X M₂

abbrev CΛ := M₁.Λ ⊕ M₂.Λ ⊕ (Option (X M₂) ⊕ Option (X M₂))

abbrev Cσ := M₁.σ × M₂.σ × Option (X M₂)

abbrev pop1 : CΛ M₁ M₂ := .inr (.inr (.inl none))

abbrev push1 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inl (some x)))

abbrev pop2 : CΛ M₁ M₂ := .inr (.inr (.inr none))

abbrev push2 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inr (some x)))

abbrev tmp : CK M₁ M₂ := .inr (.inr ())

def lift₁ : TM2.Stmt M₁.Γ M₁.Λ M₁.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inl k) (fun s => f s.1) (lift₁ q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .load a q => .load (fun s => (a s.1, s.2)) (lift₁ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (lift₁ q₁) (lift₁ q₂)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => pop1 M₁ M₂)

def lift₂ : TM2.Stmt M₂.Γ M₂.Λ M₂.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inr (.inl k)) (fun s => f s.2.1) (lift₂ q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (lift₂ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (lift₂ q₁) (lift₂ q₂)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .halt

variable (φ : M₁.Γ M₁.k₁ → X M₂)

def prog : CΛ M₁ M₂ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .inl l => lift₁ M₁ M₂ (M₁.m l)
  | .inr (.inl l) => lift₂ M₁ M₂ (M₂.m l)
  | .inr (.inr (.inl none)) =>
      .pop (.inl M₁.k₁) (fun s o => (s.1, s.2.1, o.map φ))
        (.goto fun s => match s.2.2 with
          | some x => push1 M₁ M₂ x
          | none => pop2 M₁ M₂)
  | .inr (.inr (.inl (some x))) =>
      .push (tmp M₁ M₂) (fun _ => x) (.goto fun _ => pop1 M₁ M₂)
  | .inr (.inr (.inr none)) =>
      .pop (tmp M₁ M₂) (fun s o => (s.1, s.2.1, o))
        (.goto fun s => match s.2.2 with
          | some x => push2 M₁ M₂ x
          | none => .inr (.inl M₂.main))
  | .inr (.inr (.inr (some x))) =>
      .push (.inr (.inl M₂.k₀)) (fun _ => x) (.goto fun _ => pop2 M₁ M₂)

noncomputable def compTM : FinTM2 where
  K := CK M₁ M₂
  k₀ := .inl M₁.k₀
  k₁ := .inr (.inl M₂.k₁)
  Γ := CΓ M₁ M₂
  Λ := CΛ M₁ M₂
  main := .inl M₁.main
  σ := Cσ M₁ M₂
  initialState := (M₁.initialState, M₂.initialState, none)
  Γk₀Fin := M₁.Γk₀Fin
  m := prog M₁ M₂ φ

def mkStk (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    ∀ k : CK M₁ M₂, List (CΓ M₁ M₂ k)
  | .inl k => S₁ k
  | .inr (.inl k) => S₂ k
  | .inr (.inr _) => t

variable {M₁ M₂}

theorem update_mkStk_inl (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₁.K) (x : List (M₁.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inl k) x = mkStk M₁ M₂ (update S₁ k x) S₂ t := by
  funext k'
  rcases k' with k' | k' | u
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_inr (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₂.K) (x : List (M₂.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inr (.inl k)) x = mkStk M₁ M₂ S₁ (update S₂ k x) t := by
  funext k'
  rcases k' with k' | k' | u
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_tmp (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (x : List (X M₂)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (tmp M₁ M₂) x = mkStk M₁ M₂ S₁ S₂ x := by
  funext k'
  rcases k' with k' | k' | ⟨⟩
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl
  · simp [mkStk]

def lab₁ : Option M₁.Λ → CΛ M₁ M₂
  | some l => .inl l
  | none => pop1 M₁ M₂

theorem stepAux_lift₁ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v : M₁.σ) (S₁ : ∀ k, List (M₁.Γ k))
    (v₂ : M₂.σ) (o : Option (X M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₁ M₁ M₂ q) (v, v₂, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨some (lab₁ (TM2.stepAux q v S₁).l), ((TM2.stepAux q v S₁).var, v₂, o),
        mkStk M₁ M₂ (TM2.stepAux q v S₁).stk S₂ t⟩ := by
  induction q generalizing v S₁ with
  | push k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | peek k f q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | load a q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₁, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₁, TM2.stepAux, lab₁]
  | halt => simp [lift₁, TM2.stepAux, lab₁]

theorem stepAux_lift₂ (q : TM2.Stmt M₂.Γ M₂.Λ M₂.σ) (v : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k))
    (v₁ : M₁.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₂ M₁ M₂ q) (v₁, v, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨(TM2.stepAux q v S₂).l.map (fun l => .inr (.inl l)), (v₁, (TM2.stepAux q v S₂).var, o),
        mkStk M₁ M₂ S₁ (TM2.stepAux q v S₂).stk t⟩ := by
  induction q generalizing v S₂ with
  | push k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | peek k f q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | load a q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₂, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₂, TM2.stepAux]
  | halt => simp [lift₂, TM2.stepAux]

def emb₁ (c : TM2.Cfg M₁.Γ M₁.Λ M₁.σ) : TM2.Cfg (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂) :=
  ⟨some (lab₁ c.l), (c.var, M₂.initialState, none), mkStk M₁ M₂ c.stk (fun _ => []) []⟩

def emb₂ (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) : TM2.Cfg (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂) :=
  ⟨c.l.map (fun l => .inr (.inl l)), (M₁.initialState, c.var, none),
    mkStk M₁ M₂ (fun _ => []) c.stk []⟩

theorem step_emb₁ {c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ} (h : TM2.step M₁.m c = some c') :
    TM2.step (prog M₁ M₂ φ) (emb₁ c) = some (emb₁ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [emb₁, lab₁, TM2.step, prog]
    rw [stepAux_lift₁]
    rfl

theorem step_emb₂ {c c' : TM2.Cfg M₂.Γ M₂.Λ M₂.σ} (h : TM2.step M₂.m c = some c') :
    TM2.step (prog M₁ M₂ φ) (emb₂ c) = some (emb₂ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [emb₂, Option.map_some, TM2.step, prog]
    rw [stepAux_lift₂]

theorem iter_step {σ : Type} {f : σ → Option σ} {c c' : σ} (h : f c = some c') (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some c') := by
  rw [iterate_succ_apply]
  change (flip bind f)^[n] (f c) = _
  rw [h]

theorem iter_sim {α β : Type} {f : α → Option α} {g : β → Option β} (e : α → β)
    (H : ∀ c c', f c = some c' → g (e c) = some (e c')) :
    ∀ (n : ℕ) (c d : α), (flip bind f)^[n] (some c) = some d →
      (flip bind g)^[n] (some (e c)) = some (e d) := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h ⊢
      rw [h]
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind f)^[n] (f c) = some d at h
      cases hc : f c with
      | none => rw [hc, TM2Program.iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          rw [iter_step (H c c' hc)]
          exact ih c' d h

section copy

variable (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k))
  (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))

theorem step_pop1_cons (y : M₁.Γ M₁.k₁) (ys : List (M₁.Γ M₁.k₁)) (hy : S₁ M₁.k₁ = y :: ys) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (push1 M₁ M₂ (φ y)), (v₁, v₂, some (φ y)),
        mkStk M₁ M₂ (update S₁ M₁.k₁ ys) S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, hy, update_mkStk_inl]

theorem step_pop1_nil (hy : S₁ M₁.k₁ = []) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none), mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, hy, update_mkStk_inl]

theorem step_push1 (x : X M₂) (s : Cσ M₁ M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (push1 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop1 M₁ M₂), s, mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_pop2_cons (x : X M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ =
      some ⟨some (push2 M₁ M₂ x), (v₁, v₂, some x), mkStk M₁ M₂ S₁ S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_pop2_nil :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ []⟩ =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none), mkStk M₁ M₂ S₁ S₂ []⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_push2 (x : X M₂) (s : Cσ M₁ M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (push2 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), s, mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (x :: S₂ M₂.k₀)) t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_inr]

end copy

theorem copy₁ (ys : List (M₁.Γ M₁.k₁)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (hy : S₁ M₁.k₁ = ys) :
    (flip bind (TM2.step (prog M₁ M₂ φ)))^[2 * ys.length + 1]
        (some ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none),
        mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ ((ys.map φ).reverse ++ t)⟩ := by
  induction ys generalizing o S₁ t with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop1_nil φ v₁ v₂ o S₁ S₂ t hy)]
      simp
  | cons y ys ih =>
      rw [show 2 * (y :: ys).length + 1 = (2 * ys.length + 1) + 1 + 1 by
          simp only [List.length_cons]; omega,
        iter_step (step_pop1_cons φ v₁ v₂ o S₁ S₂ t y ys hy), iter_step (step_push1 φ _ _ _ _ _),
        ih _ _ _ (update_self _ _ _)]
      simp [update_idem]

theorem copy₂ (t : List (X M₂)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) :
    (flip bind (TM2.step (prog M₁ M₂ φ)))^[2 * t.length + 1]
        (some ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none),
        mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (t.reverse ++ S₂ M₂.k₀)) []⟩ := by
  induction t generalizing o S₂ with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop2_nil φ v₁ v₂ o S₁ S₂)]
      simp
  | cons x t ih =>
      rw [show 2 * (x :: t).length + 1 = (2 * t.length + 1) + 1 + 1 by
          simp only [List.length_cons]; omega,
        iter_step (step_pop2_cons φ v₁ v₂ o S₁ S₂ t x), iter_step (step_push2 φ _ _ _ _ _), ih]
      simp [update_idem]

section length

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => pushes q₁ + pushes q₂
  | .goto _ => 0
  | .halt => 0

theorem length_stepAux (k : K) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
      simp only [TM2.stepAux, pushes]
      refine (ih _ _).trans ?_
      by_cases h : k = k'
      · subst h; simp; omega
      · simp [update_of_ne h]
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
      simp only [TM2.stepAux, pushes]
      refine (ih _ _).trans ?_
      by_cases h : k = k'
      · subst h; simp
      · simp [update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, pushes]
      cases f v
      · exact (ih₂ v S).trans (by omega)
      · exact (ih₁ v S).trans (by omega)
  | goto f => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

end length

noncomputable def pushBound (M : FinTM2) : ℕ := ∑ l, pushes (M.m l)

theorem length_step (M : FinTM2) (k : M.K) {c c' : M.Cfg} (h : M.step c = some c') :
    (c'.stk k).length ≤ (c.stk k).length + pushBound M := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    rw [← Option.some.inj h]
    have hl : pushes (M.m l) ≤ pushBound M :=
      Finset.single_le_sum (f := fun l => pushes (M.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
    exact (length_stepAux k _ v S).trans (Nat.add_le_add_left hl _)

theorem length_iter (M : FinTM2) (k : M.K) :
    ∀ (n : ℕ) (c d : M.Cfg), (flip bind M.step)^[n] (some c) = some d →
      (d.stk k).length ≤ (c.stk k).length + pushBound M * n := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h
      subst h; simp
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind M.step)^[n] (M.step c) = some d at h
      cases hc : M.step c with
      | none => rw [hc, TM2Program.iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          have h₁ := ih c' d h
          have h₂ := length_step M k hc
          rw [Nat.mul_succ]
          omega

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

theorem initList_stk_length_le (M : FinTM2) (l : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M l).stk k).length ≤ l.length := by
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem haltList_stk_self (M : FinTM2) (l : List (M.Γ M.k₁)) : (haltList M l).stk M.k₁ = l := by
  simp [haltList]

theorem update_haltList_stk (M : FinTM2) (l : List (M.Γ M.k₁)) :
    update (haltList M l).stk M.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [haltList, h]

theorem update_nil_eq_initList (M : FinTM2) (l : List (M.Γ M.k₀)) :
    update (fun _ => []) M.k₀ l = (initList M l).stk := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem initList_compTM (l : List (M₁.Γ M₁.k₀)) :
    initList (compTM M₁ M₂ φ) l = emb₁ (initList M₁ l) := by
  simp only [initList, emb₁, lab₁]
  congr 1
  funext k
  rcases k with k | k | u
  · by_cases h : k = M₁.k₀
    · subst h; simp [mkStk, compTM]; try rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]
  · simp [mkStk, compTM]

theorem haltList_compTM (l : List (M₂.Γ M₂.k₁)) :
    haltList (compTM M₁ M₂ φ) l = emb₂ (haltList M₂ l) := by
  simp only [haltList, emb₂, Option.map_none]
  congr 1
  funext k
  rcases k with k | k | u
  · simp [mkStk, compTM]
  · by_cases h : k = M₂.k₁
    · subst h; simp [mkStk, compTM]; try rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]

section main

variable {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
  {f : α → β} {g : β → γ}

def glue (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    h₁.tm.Γ h₁.tm.k₁ → X h₂.tm :=
  fun y => h₂.inputAlphabet.symm (h₁.outputAlphabet y)

noncomputable def midPoly (h₁ : TM2ComputableInPolyTime eα eβ f) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (pushBound h₁.tm) * h₁.time

noncomputable def compTime (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : Polynomial ℕ :=
  h₁.time + Polynomial.C 4 * midPoly h₁ + Polynomial.C 2 + h₂.time.comp (midPoly h₁)

noncomputable def compOutputs (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (a : α) :
    TM2OutputsInTime (compTM h₁.tm h₂.tm (glue h₁ h₂))
      (List.map h₁.inputAlphabet.invFun (eα a))
      (some (List.map h₂.outputAlphabet.invFun (eγ (g (f a)))))
      ((compTime h₁ h₂).eval (eα a).length) := by
  let φ := glue h₁ h₂
  let inp := List.map h₁.inputAlphabet.invFun (eα a)
  let L := List.map h₁.outputAlphabet.invFun (eβ (f a))
  let inp₂ := List.map h₂.inputAlphabet.invFun (eβ (f a))
  let out := List.map h₂.outputAlphabet.invFun (eγ (g (f a)))
  obtain ⟨⟨s₁, e₁⟩, hs₁⟩ := h₁.outputsFun a
  obtain ⟨⟨s₂, e₂⟩, hs₂⟩ := h₂.outputsFun (f a)
  change (flip bind h₁.tm.step)^[s₁] (some (initList h₁.tm inp)) =
      some (haltList h₁.tm L) at e₁
  change (flip bind h₂.tm.step)^[s₂] (some (initList h₂.tm inp₂)) =
      some (haltList h₂.tm out) at e₂

  have P₁ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[s₁]
      (some (emb₁ (M₂ := h₂.tm) (initList h₁.tm inp))) =
      some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L)) :=
    iter_sim (emb₁ (M₂ := h₂.tm)) (fun _ _ h => step_emb₁ φ h) _ _ _ e₁

  have P₂ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[2 * L.length + 1]
      (some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L))) =
      some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩ :=
    copy₁ φ L _ _ _ _ _ _ (haltList_stk_self _ _)

  have hT : ((L.map φ).reverse ++ []).reverse ++ [] = inp₂ := by
    simp [L, inp₂, φ, glue, List.map_map, Function.comp_def]
  have P₃ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[2 * ((L.map φ).reverse ++ []).length + 1]
      (some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩) =
      some (emb₂ (M₁ := h₁.tm) (initList h₂.tm inp₂)) := by
    rw [copy₂, update_haltList_stk]
    rw [hT, update_nil_eq_initList]
    rfl

  have P₄ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[s₂]
      (some (emb₂ (M₁ := h₁.tm) (initList h₂.tm inp₂))) =
      some (emb₂ (M₁ := h₁.tm) (haltList h₂.tm out)) :=
    iter_sim (emb₂ (M₁ := h₁.tm)) (fun _ _ h => step_emb₂ φ h) _ _ _ e₂
  refine ⟨⟨s₂ + (2 * ((L.map φ).reverse ++ []).length + 1) + (2 * L.length + 1) +
    s₁, ?_⟩, ?_⟩
  · change (flip bind (compTM h₁.tm h₂.tm φ).step)^[_]
        (some (initList (compTM h₁.tm h₂.tm φ) inp)) =
      Option.map (haltList (compTM h₁.tm h₂.tm φ)) (some out)
    rw [initList_compTM]; simp only [Option.map]; rw [haltList_compTM]
    change (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[_] _ = _
    erw [iterate_add_apply, iterate_add_apply, iterate_add_apply]
    erw [P₁, P₂, P₃, P₄]
    rfl
  ·
    change s₁ ≤ h₁.time.eval (eα a).length at hs₁
    change s₂ ≤ h₂.time.eval (eβ (f a)).length at hs₂
    have hlen := length_iter h₁.tm h₁.tm.k₁ _ _ _ e₁
    rw [haltList_stk_self] at hlen
    have hinit := initList_stk_length_le h₁.tm inp h₁.tm.k₁
    have hL : L.length = (eβ (f a)).length := by simp [L]
    have hinp : inp.length = (eα a).length := by simp [inp]
    have hm : (eβ (f a)).length ≤
        (eα a).length + pushBound h₁.tm * h₁.time.eval (eα a).length := by
      have := Nat.mul_le_mul_left (pushBound h₁.tm) hs₁
      omega
    have hp₂ := eval_mono h₂.time hm
    have hmid : (midPoly h₁).eval (eα a).length =
        (eα a).length + pushBound h₁.tm * h₁.time.eval (eα a).length := by
      simp [midPoly]
    simp only [compTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, hmid]
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_nil,
      Nat.add_zero, hL]
    omega

noncomputable def compComputable (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : TM2ComputableInPolyTime eα eγ (g ∘ f) where
  tm := compTM h₁.tm h₂.tm (glue h₁ h₂)
  inputAlphabet := h₁.inputAlphabet
  outputAlphabet := h₂.outputAlphabet
  time := compTime h₁ h₂
  outputsFun := compOutputs h₁ h₂

end main

end MetaMathlibExt.TM2Composition

namespace MetaMathlibExt

open Turing

theorem tm2ComputableInPolyTime_comp {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) :=
  ⟨TM2Composition.compComputable h₁ h₂⟩

namespace ComplexityTheory

open Computability

end ComplexityTheory

end MetaMathlibExt
end

-- MathlibExt.Computability.TuringMachine.StackEmbedding
section
namespace MetaMathlibExt.TM2Embedding

open MetaMathlibExt.TM2Program Turing Function

structure SEmb {K K' : Type} (Γ : K → Type) (Γ' : K' → Type) where

  e : K → K'

  inj : Injective e

  ι : ∀ k, Γ k ≃ Γ' (e k)

section Embed

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {Γ : K → Type} {Γ' : K' → Type}
  {Λ Λ' σ : Type} (E : SEmb Γ Γ') (φ : Λ → Λ')

def mapS : TM2.Stmt Γ Λ σ → TM2.Stmt Γ' Λ' σ
  | .push k f q => .push (E.e k) (fun s => E.ι k (f s)) (mapS q)
  | .peek k f q => .peek (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .pop k f q => .pop (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .load a q => .load a (mapS q)
  | .branch f q₁ q₂ => .branch f (mapS q₁) (mapS q₂)
  | .goto f => .goto fun s => φ (f s)
  | .halt => .halt

def Embeds (M : Λ → TM2.Stmt Γ Λ σ) (M' : Λ' → TM2.Stmt Γ' Λ' σ) : Prop :=
  ∀ l, M' (φ l) = mapS E φ (M l) ∨ M l = .halt

def Agree (S : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k')) : Prop :=
  ∀ k, S' (E.e k) = (S k).map (E.ι k)

def Frame (S' S'' : ∀ k', List (Γ' k')) : Prop :=
  ∀ k', (∀ k, E.e k ≠ k') → S'' k' = S' k'

variable {E}

omit [DecidableEq K] [DecidableEq K'] in
theorem Frame.refl (S' : ∀ k', List (Γ' k')) : Frame E S' S' := fun _ _ => rfl

omit [DecidableEq K] [DecidableEq K'] in
theorem Frame.trans {S₁ S₂ S₃ : ∀ k', List (Γ' k')} (h₁ : Frame E S₁ S₂) (h₂ : Frame E S₂ S₃) :
    Frame E S₁ S₃ := fun k' hk => (h₂ k' hk).trans (h₁ k' hk)

omit [DecidableEq K] in
theorem Frame.update (S' : ∀ k', List (Γ' k')) (k : K) (l : List (Γ' (E.e k))) :
    Frame E S' (update S' (E.e k) l) := fun _ hk => update_of_ne (hk k).symm _ _

theorem Agree.update {S : ∀ k, List (Γ k)} {S' : ∀ k', List (Γ' k')} (h : Agree E S S') (k : K)
    (l : List (Γ k)) :
    Agree E (Function.update S k l) (Function.update S' (E.e k) (l.map (E.ι k))) := by
  intro k₂
  by_cases hk : k₂ = k
  · subst hk; simp
  · rw [update_of_ne (E.inj.ne hk), update_of_ne hk]; exact h k₂

theorem stepAux_mapS (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k'))
    (hA : Agree E S S') :
    ∃ T' : ∀ k', List (Γ' k'),
      TM2.stepAux (mapS E φ q) v S' =
        ⟨(TM2.stepAux q v S).l.map φ, (TM2.stepAux q v S).var, T'⟩ ∧
      Agree E (TM2.stepAux q v S).stk T' ∧ Frame E S' T' := by
  induction q generalizing v S S' with
  | push k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih v _ _ (hA.update k (f v :: S k))
      refine ⟨T', ?_, h2, (Frame.update S' k _).trans h3⟩
      simp only [mapS, TM2.stepAux, hA k]
      exact h1
  | peek k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (f v (S k).head?) S S' hA
      refine ⟨T', ?_, h2, h3⟩
      simp only [mapS, TM2.stepAux, hA k, List.head?_map, Option.map_map, Equiv.symm_comp_self,
        Option.map_id_fun, id_eq]
      exact h1
  | pop k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (f v (S k).head?) _ _ (hA.update k (S k).tail)
      refine ⟨T', ?_, h2, (Frame.update S' k _).trans h3⟩
      simp only [mapS, TM2.stepAux, hA k, List.head?_map, Option.map_map, Equiv.symm_comp_self,
        Option.map_id_fun, id_eq, ← List.map_tail]
      exact h1
  | load a q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (a v) S S' hA
      exact ⟨T', by simpa only [mapS, TM2.stepAux] using h1, h2, h3⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases hf : f v
      · obtain ⟨T', h1, h2, h3⟩ := ih₂ v S S' hA
        exact ⟨T', by simpa only [mapS, TM2.stepAux, hf, cond_false] using h1,
          by simpa only [TM2.stepAux, hf, cond_false] using h2, h3⟩
      · obtain ⟨T', h1, h2, h3⟩ := ih₁ v S S' hA
        exact ⟨T', by simpa only [mapS, TM2.stepAux, hf, cond_true] using h1,
          by simpa only [TM2.stepAux, hf, cond_true] using h2, h3⟩
  | goto f => exact ⟨S', by simp [mapS, TM2.stepAux], hA, Frame.refl S'⟩
  | halt => exact ⟨S', by simp [mapS, TM2.stepAux], hA, Frame.refl S'⟩

theorem run_embed {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ' Λ' σ} (hM : Embeds E φ M M') :
    ∀ (n : ℕ) (l : Option Λ) (v : σ) (S : ∀ k, List (Γ k)) (l' : Λ) (v' : σ)
      (T : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k')),
      Run M n ⟨l, v, S⟩ ⟨some l', v', T⟩ → Agree E S S' →
      ∃ T' : ∀ k', List (Γ' k'),
        Run M' n ⟨l.map φ, v, S'⟩ ⟨some (φ l'), v', T'⟩ ∧ Agree E T T' ∧ Frame E S' T' := by
  intro n
  induction n with
  | zero =>
      intro l v S l' v' T S' h hA
      simp only [Run, iterate_zero, id_eq, Option.some.injEq, TM2.Cfg.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨S', Run.zero _, hA, Frame.refl S'⟩
  | succ n ih =>
      intro l v S l' v' T S' h hA
      unfold Run at h
      rw [iterate_succ_apply] at h
      rcases l with _ | l
      · have : (flip bind (TM2.step M)) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
        rw [this, iter_none] at h
        exact absurd h (by simp)
      · have e : (flip bind (TM2.step M)) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
            some (TM2.stepAux (M l) v S) := rfl
        rw [e] at h
        rcases hM l with hl | hl
        · obtain ⟨T₁, h1, h2, h3⟩ := stepAux_mapS φ (M l) v S S' hA
          obtain ⟨T', r, h4, h5⟩ := ih _ _ _ _ _ _ T₁ h h2
          refine ⟨T', Run.head ?_ r, h4, h3.trans h5⟩
          simp only [Option.map_some, TM2.step, hl, h1]
        · rw [hl] at h
          simp only [TM2.stepAux] at h
          cases n with
          | zero => simp at h
          | succ n =>
              rw [iterate_succ_apply] at h
              have : (flip bind (TM2.step M)) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none :=
                rfl
              rw [this, iter_none] at h
              exact absurd h (by simp)

theorem runLe_embed {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ' Λ' σ} (hM : Embeds E φ M M')
    {B : ℕ} {l : Λ} {v : σ} {S : ∀ k, List (Γ k)} {l' : Λ} {v' : σ} {T : ∀ k, List (Γ k)}
    {S' : ∀ k', List (Γ' k')} (h : RunLe M B ⟨some l, v, S⟩ ⟨some l', v', T⟩) (hA : Agree E S S') :
    ∃ T' : ∀ k', List (Γ' k'),
      RunLe M' B ⟨some (φ l), v, S'⟩ ⟨some (φ l'), v', T'⟩ ∧ Agree E T T' ∧ Frame E S' T' := by
  obtain ⟨n, hn, r⟩ := h
  obtain ⟨T', r', h1, h2⟩ := run_embed φ hM n (some l) v S l' v' T S' r hA
  exact ⟨T', ⟨n, hn, r'⟩, h1, h2⟩

end Embed

end MetaMathlibExt.TM2Embedding
end

-- CSLibExt.Computability.Complexity.CookLevin.CounterView
section
namespace Cslib.Complexity.CookLevin.CounterView

open MetaMathlibExt MetaMathlibExt.TM2Program Turing Function

inductive MS | head | body | l2 | rest
  deriving DecidableEq
instance MS.instFintypeEnumFix : Fintype MS where
  elems := ⟨↑[MS.head, MS.body, MS.l2, MS.rest], by decide⟩
  complete := fun x => by cases x <;> decide

inductive SK (C : Type)
  | out
  | c (x : C)
  deriving DecidableEq, Fintype

abbrev SΓ (C : Type) : SK C → Type
  | .out => Bool
  | .c _ => Unit

section View

variable {C : Type} [DecidableEq C]

def st (f : C → ℕ) (o : List Bool) : ∀ k, List (SΓ C k)
  | .out => o
  | .c x => cnt () (f x)

omit [DecidableEq C] in
@[simp] theorem st_c (f : C → ℕ) (o : List Bool) (x : C) : st f o (.c x) = cnt () (f x) := rfl
omit [DecidableEq C] in
@[simp] theorem st_out (f : C → ℕ) (o : List Bool) : st f o .out = o := rfl

theorem update_st_c (f : C → ℕ) (o : List Bool) (x : C) (n : ℕ) :
    update (st f o) (.c x) (cnt () n) = st (update f x n) o := by
  funext k
  rcases k with _ | y
  · rfl
  · by_cases h : y = x
    · subst h; simp
    · rw [update_of_ne (by simpa using h)]; simp [update_of_ne h]

theorem update_st_nil (f : C → ℕ) (o : List Bool) (x : C) :
    update (st f o) (.c x) [] = st (update f x 0) o := update_st_c f o x 0

theorem update_st_out (f : C → ℕ) (o l : List Bool) : update (st f o) .out l = st f l := by
  funext k
  rcases k with _ | y
  · simp
  · rw [update_of_ne (by simp)]; rfl

theorem addU_nil {K : Type} [DecidableEq K] {Γ : K → Type} (n : ℕ) (S : ∀ k, List (Γ k)) :
    addU [] n S = S := rfl

variable {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem emitS {self next : Λ} {x : C} {n : ℕ}
    (hp : M self = emitR (.c x) (List.replicate n ()) next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (n + F x)) o⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_c, show List.replicate n () = cnt () n from rfl, cnt_add, update_st_c] at this
  exact this

theorem emitOut {self next : Λ} {ys : List Bool} (hp : M self = emitR .out ys next)
    (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st F (ys ++ o)⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_out, update_st_out] at this
  exact this

theorem incS {self next : Λ} {x : C} (hp : M self = incr (.c x) () next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (F x + 1)) o⟩ := by
  have := incr_run_cnt hp v (S := st F o) (n := F x) rfl
  rw [update_st_c] at this
  exact this

theorem drainS {self next : Λ} {x : C} (hp : M self = xfer (.c x) [] self next) (F : C → ℕ)
    (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (update F x 0) o⟩ := by
  have := xfer_run hp (by simp [List.NodupKeys]) (by simp) () (F x) v (st F o) rfl
  rw [addU_nil, update_st_nil] at this
  exact this

theorem xferES {self next : Λ} {x : C} {ys : List Bool}
    (hp : M self = xferE (.c x) .out ys self next) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩
      ⟨some next, false, st (update F x 0) (rep ys (F x) ++ o)⟩ := by
  have := xferE_run hp (by simp) () (F x) v (st F o) rfl
  rw [update_st_nil, update_st_out, st_out] at this
  exact this

theorem copyS {l₁ l₂ next : Λ} {a c t : C}
    (h₁ : M l₁ = xfer (.c a) [⟨.c c, ()⟩, ⟨.c t, ()⟩] l₁ l₂)
    (h₂ : M l₂ = xfer (.c t) [⟨.c a, ()⟩] l₂ next)
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t) (F : C → ℕ) (ht : F t = 0) (v : Bool)
    (o : List Bool) :
    Run M (2 * F a + 2) ⟨some l₁, v, st F o⟩
      ⟨some next, false, st (update F c (F a + F c)) o⟩ := by
  have := copy_run h₁ h₂ (by simpa using hac) (by simpa using hat) (by simpa using hct) (F a)
    (F c) v (st F o) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

def mulS (a ad b c t : C) (mk : MS → Λ) (next : Λ) : MS → TM2.Stmt (SΓ C) Λ Bool
  | .head => forHead (.c a) (.c ad) () (mk .body) (mk .rest)
  | .body => xfer (.c b) [⟨.c c, ()⟩, ⟨.c t, ()⟩] (mk .body) (mk .l2)
  | .l2 => xfer (.c t) [⟨.c b, ()⟩] (mk .l2) (mk .head)
  | .rest => xfer (.c ad) [⟨.c a, ()⟩] (mk .rest) next

theorem mulS_run {a ad b c t : C} {mk : MS → Λ} {next : Λ}
    (hp : ∀ s, M (mk s) = mulS a ad b c t mk next s)
    (hnd : ([.c a, .c ad, .c b, .c c, .c t] : List (SK C)).Nodup)
    (F : C → ℕ) (had : F ad = 0) (ht : F t = 0) (v : Bool) (o : List Bool) :
    Run M (F a * (2 * F b + 3) + F a + 2) ⟨some (mk .head), v, st F o⟩
      ⟨some next, false, st (update F c (F a * F b + F c)) o⟩ := by
  have := mul_run (hp .head) (hp .body) (hp .l2) (hp .rest) hnd (F a) (F b) (F c) v (st F o) rfl
    (by simp [had]) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

theorem gapS {P Q T1 T2 : C} {ys : List Bool} {dec cmpL emitL ifZero next : Λ}
    {r rB out : Ordering → Λ}
    (hdec : M dec = decr (.c P) ifZero cmpL)
    (hcmp : M cmpL = cmpStep (.c P) (.c Q) (.c T1) (.c T2) () () cmpL (r .lt) (r .eq) (r .gt))
    (hr : ∀ o, M (r o) = xfer (.c T1) [⟨.c P, ()⟩] (r o) (rB o))
    (hrB : ∀ o, M (rB o) = xfer (.c T2) [⟨.c Q, ()⟩] (rB o) (out o))
    (hout : ∀ o, out o = if o = .eq then next else emitL)
    (hemit : M emitL = emitR .out ys dec)
    (hnd : ([.c P, .c Q, .c T1, .c T2, .out] : List (SK C)).Nodup) (q gap : ℕ) (F : C → ℕ)
    (hP : F P = q + gap + 1) (hQ : F Q = q) (h1 : F T1 = 0) (h2 : F T2 = 0) (v : Bool)
    (o : List Bool) :
    Run M (gap * (3 * q + 6) + 3 * q + 4) ⟨some dec, v, st F o⟩
      ⟨some next, false, st (update F P q) (rep ys gap ++ o)⟩ := by
  have := emitDiff_run hdec hcmp hr hrB hout hemit hnd q gap v (st F o) (by simp [hP])
    (by simp [hQ]) (by simp [h1]) (by simp [h2])
  rw [update_st_c, update_st_out, st_out] at this
  exact this

theorem bud_st {K X : ℕ} {F F' : C → ℕ} {l : Option Λ} {v : Bool} {o : List Bool}
    {d : TM2.Cfg (SΓ C) Λ Bool} (h : F = F') (h' : Bud M K X ⟨l, v, st F' o⟩ d) :
    Bud M K X ⟨l, v, st F o⟩ d := h ▸ h'

omit [DecidableEq C] in
theorem st_eta (S : ∀ k, List (SΓ C k)) : S = st (fun x => (S (.c x)).length) (S .out) := by
  funext k
  rcases k with _ | x
  · rfl
  · exact List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩

theorem stLoop {c cd : C} {head body rest next : Λ}
    (hHead : M head = forHead (.c c) (.c cd) () body rest)
    (hRest : M rest = xfer (.c cd) [⟨.c c, ()⟩] rest next) (hc : c ≠ cd) (n B : ℕ)
    (blk : ℕ → List Bool) (f : C → ℕ) (hfc : f c = n) (hfcd : f cd = 0)
    (hbody : ∀ t < n, ∀ o, ∃ v', RunLe M B
      ⟨some body, true, st (update (update f c t) cd (n - t)) o⟩
      ⟨some head, v', st (update (update f c t) cd (n - t)) (blk t ++ o)⟩)
    (v : Bool) (o : List Bool) :
    RunLe M (n * (B + 1) + n + 2) ⟨some head, v, st f o⟩
      ⟨some next, false, st f ((List.range n).flatMap blk ++ o)⟩ := by
  obtain ⟨S', hrun, h'c, h'cd, h'o, h'x⟩ := forLoop_le (M := M) (c := .c c) (cd := .c cd)
    (uc := ()) (ucd := ()) hHead
    hRest (by simpa using hc) n B
    (fun i S => S .out = (List.range' (n - i) i).flatMap blk ++ o ∧
      ∀ x, x ≠ c → x ≠ cd → (S (.c x)).length = f x)
    (fun i S S' h ⟨h1, h2⟩ => ⟨by rw [h .out (by simp) (by simp), h1],
      fun x hx1 hx2 => by rw [h (.c x) (by simpa using hx1) (by simpa using hx2), h2 x hx1 hx2]⟩)
    (fun i hi S hS1 hS2 ⟨h1, h2⟩ => by
      have hS : S = st (update (update f c (n - 1 - i)) cd (n - (n - 1 - i))) (S .out) := by
        funext k
        rcases k with _ | x
        · rfl
        · by_cases hx1 : x = c
          · subst hx1; rw [hS1]; simp [hc]
          · by_cases hx2 : x = cd
            · subst hx2; rw [hS2]; simp only [st_c, update_self]; congr 1; omega
            · simp only [st_c, update_of_ne hx2, update_of_ne hx1]
              exact List.eq_replicate_iff.2 ⟨h2 x hx1 hx2, fun _ _ => rfl⟩
      obtain ⟨v', r⟩ := hbody (n - 1 - i) (by omega) (S .out)
      rw [← hS] at r
      refine ⟨v', _, r, ?_, ?_, ?_, fun x hx1 hx2 => ?_⟩
      · rw [hS1]; simp [hc]
      · rw [hS2]; simp only [st_c, update_self]; congr 1; omega
      · simp only [st_out, h1]
        rw [show n - (i + 1) = n - 1 - i by omega, List.range'_succ,
          show n - 1 - i + 1 = n - i by omega, List.flatMap_cons, List.append_assoc]
      · simp [update_of_ne hx1, update_of_ne hx2])
    v (st f o) (by simp [hfc]) (by simp [hfcd]) ⟨by simp, fun x _ _ => by simp⟩
  have hS' : S' = st f ((List.range n).flatMap blk ++ o) := by
    funext k
    rcases k with _ | x
    · rw [h'o, Nat.sub_self, ← List.range_eq_range']; rfl
    · by_cases hx1 : x = c
      · subst hx1; rw [h'c]; simp [hfc]
      · by_cases hx2 : x = cd
        · subst hx2; rw [h'cd]; simp [hfcd]
        · exact List.eq_replicate_iff.2 ⟨h'x x hx1 hx2, fun _ _ => rfl⟩
  rw [hS'] at hrun
  exact hrun

end View

section Addu

variable {C : Type} [DecidableEq C]

theorem emitR_st (f : C → ℕ) (o : List Bool) (x : C) (n : ℕ) :
    update (st f o) (.c x) (List.replicate n () ++ st f o (.c x)) =
      st (update f x (n + f x)) o := by
  rw [st_c, show List.replicate n () = cnt () n from rfl, cnt_add, update_st_c]

theorem addU_st_single (f : C → ℕ) (o : List Bool) (y : C) (n : ℕ) :
    addU [⟨.c y, ()⟩] n (st f o) = st (update f y (n + f y)) o := by
  funext k
  rcases k with _ | z
  · rw [addU_single_ne _ _ _ (by simp)]; rfl
  · by_cases h : z = y
    · subst h; rw [addU_single_self]; simp
    · rw [addU_single_ne _ _ _ (by simpa using h)]; simp [update_of_ne h]

theorem addU_st_pair (f : C → ℕ) (o : List Bool) (y z : C) (hyz : y ≠ z) (n : ℕ) :
    addU [⟨.c y, ()⟩, ⟨.c z, ()⟩] n (st f o) =
      st (update (update f y (n + f y)) z (n + f z)) o := by
  funext k
  rcases k with _ | w
  · rw [addU_pair_ne _ _ _ _ (by simp) (by simp)]; rfl
  · by_cases h : w = y
    · subst h; rw [addU_pair_fst]; simp [update_of_ne hyz]
    · by_cases h' : w = z
      · subst h'; rw [addU_pair_snd _ _ _ _ (by simpa using hyz.symm)]; simp
      · rw [addU_pair_ne _ _ _ _ (by simpa using h) (by simpa using h')]
        simp [update_of_ne h, update_of_ne h']

end Addu

end Cslib.Complexity.CookLevin.CounterView
end

-- CSLibExt.Computability.Complexity.DenseSATVerifier
section
namespace Cslib.Complexity.DenseSAT

namespace Verifier

open Turing Function MetaMathlibExt

inductive W | inp | F | A | B
  deriving DecidableEq
instance W.instFintypeEnumFix : Fintype W where
  elems := ⟨↑[W.inp, W.F, W.A, W.B], by decide⟩
  complete := fun x => by cases x <;> decide

abbrev G := Bool ⊕ Option Bool

def pairEncode (p : List Bool × List Bool) : List G :=
  p.1.map Sum.inl ++ Sum.inr none :: p.2.map fun b => Sum.inr (some b)

abbrev Γ : Option W → Type
  | none => Bool
  | some _ => G

inductive Lab
  | read1 | read2 | back1 | back2
  | c0 (fl : Bool) | c1 (fl b : Bool) | adv (fl : Bool) (o : Option Bool) | restore (fl : Bool)
  | drainI (ans : Bool) | drainA (ans : Bool) | drainB (ans : Bool) | finish (ans : Bool)
  deriving DecidableEq, Fintype

abbrev St := Option G

abbrev Stmt := TM2.Stmt Γ Lab St

abbrev Cfg := TM2.Cfg Γ Lab St

def loop (s : W) (g : G → Option G) (t : Option W) (self next : Lab) : Stmt :=
  .pop (some s) (fun _ o => o) <|
    .branch (fun v => (v.bind g).isSome)
      (match t with
        | some t => .push (some t) (fun v => (v.bind g).getD (.inl false)) (.goto fun _ => self)
        | none => .goto fun _ => self)
      (.goto fun _ => next)

def gRead1 : G → Option G
  | .inl b => some (.inl b)
  | .inr _ => none

def gRead2 : G → Option G
  | .inr (some b) => some (.inl b)
  | _ => none

def prog : Lab → Stmt
  | .read1 => loop .inp gRead1 (some .F) .read1 .read2
  | .read2 => loop .inp gRead2 (some .A) .read2 .back1
  | .back1 => loop .F some (some .inp) .back1 .back2
  | .back2 => loop .A some (some .B) .back2 (.c0 false)
  | .c0 fl => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl b) => .c1 fl b
      | _ => .drainI true
  | .c1 fl false => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl false) => .restore fl
      | some (.inl true) => .adv fl none
      | _ => .drainI true
  | .c1 fl true => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl s) => .adv fl (some s)
      | _ => .drainI true
  | .adv fl o => .pop (some .B) (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push (some .A) (fun v => v.getD (.inl false)) <|
          .goto fun v => .c0 (fl || decide (v = o.map fun s => .inl (!s))))
        (.goto fun _ => .c0 fl)
  | .restore fl => loop .A some (some .B) (.restore fl) (if fl then .c0 false else .drainI false)
  | .drainI ans => loop .inp some none (.drainI ans) (.drainA ans)
  | .drainA ans => loop .A some none (.drainA ans) (.drainB ans)
  | .drainB ans => loop .B some none (.drainB ans) (.finish ans)
  | .finish ans => .push none (fun _ => ans) <| .load (fun _ => none) .halt

def tm : FinTM2 where
  K := Option W
  k₀ := some .inp
  k₁ := none
  Γ := Γ
  Λ := Lab
  main := .read1
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype G)
  m := prog

def stk (V : W → List G) (o : List Bool) : ∀ k, List (Γ k)
  | none => o
  | some w => V w

theorem update_stk_some (V : W → List G) (o : List Bool) (w : W) (l : List G) :
    update (stk V o) (some w) l = stk (update V w l) o := by
  funext k
  rcases k with _ | k
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k = w
    · subst h; simp [stk]
    · rw [update_of_ne (by simpa using h)]
      simp [stk, update_of_ne h]

theorem update_stk_none (V : W → List G) (o l : List Bool) :
    update (stk V o) none l = stk V l := by
  funext k
  rcases k with _ | k
  · simp [stk]
  · rw [update_of_ne (by simp)]; rfl

def mkV (i f a b : List G) : W → List G
  | .inp => i
  | .F => f
  | .A => a
  | .B => b

@[simp] theorem update_mkV_inp (i f a b x : List G) :
    update (mkV i f a b) .inp x = mkV x f a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_F (i f a b x : List G) :
    update (mkV i f a b) .F x = mkV i x a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_A (i f a b x : List G) :
    update (mkV i f a b) .A x = mkV i f x b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_B (i f a b x : List G) :
    update (mkV i f a b) .B x = mkV i f a x := by
  funext k; cases k <;> rfl

def pushAll : Option W → List G → (W → List G) → W → List G
  | none, _, V => V
  | some t, ys, V => update V t (ys.reverse ++ V t)

theorem loop_run (s : W) (g : G → Option G) (t : Option W) (self next : Lab)
    (hp : prog self = loop s g t self next) (hst : t ≠ some s) (o : List Bool) :
    ∀ (xs ys rest : List G) (v : St) (V : W → List G),
      xs.map g = ys.map some → rest.head?.bind g = none → V s = xs ++ rest →
      TM2Program.Run prog (xs.length + 1) ⟨some self, v, stk V o⟩
        ⟨some next, rest.head?, stk (pushAll t ys (update V s rest.tail)) o⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro ys rest v V hg hr hV
      obtain rfl : ys = [] := by simpa using hg.symm
      refine TM2Program.Run.head ?_ (TM2Program.Run.zero _)
      simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
        List.nil_append, hr, Option.isSome_none, cond_false]
      rw [update_stk_some]
      rcases t with _ | t
      · rfl
      · simp [pushAll]
  | cons x xs ih =>
      intro ys rest v V hg hr hV
      rcases ys with _ | ⟨y, ys⟩
      · simp at hg
      simp only [List.map_cons, List.cons.injEq] at hg
      obtain ⟨hxy, hg⟩ := hg
      rcases t with _ | t
      · have key := ih ys rest (some x) (update V s (xs ++ rest)) hg hr (by simp)
        simp only [pushAll, update_idem] at key ⊢
        refine TM2Program.Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, cond_true]
        rw [update_stk_some]
      · have hts : t ≠ s := fun h => hst (by rw [h])
        have key := ih ys rest (some x) (update (update V s (xs ++ rest)) t (y :: V t)) hg hr
          (by rw [update_of_ne (Ne.symm hts)]; simp)
        have hfin : pushAll (some t) ys
              (update (update (update V s (xs ++ rest)) t (y :: V t)) s rest.tail) =
            pushAll (some t) (y :: ys) (update V s rest.tail) := by
          funext k
          simp only [pushAll]
          by_cases hk : k = t
          · subst hk; simp [update_of_ne hts]
          · by_cases hk' : k = s
            · subst hk'; simp [update_of_ne hk]
            · simp [update_of_ne hk, update_of_ne hk']
        rw [hfin] at key
        refine TM2Program.Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, cond_true, Option.getD_some]
        rw [update_stk_some, show stk (update V s (xs ++ rest)) o (some t) =
          update V s (xs ++ rest) t from rfl, update_stk_some, update_of_ne hts]

theorem drain_run (ans : Bool) (i a b : List G) (v : St) :
    TM2Program.Run prog (i.length + a.length + b.length + 3)
      ⟨some (.drainI ans), v, stk (mkV i [] a b) []⟩
      ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩ := by
  have h₁ := loop_run .inp some none (.drainI ans) (.drainA ans) rfl (by simp) [] i i [] v
    (mkV i [] a b) rfl rfl (by simp [mkV])
  have h₂ := loop_run .A some none (.drainA ans) (.drainB ans) rfl (by simp) [] a a [] none
    (mkV [] [] a b) rfl rfl (by simp [mkV])
  have h₃ := loop_run .B some none (.drainB ans) (.finish ans) rfl (by simp) [] b b [] none
    (mkV [] [] [] b) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_inp, update_mkV_A,
    update_mkV_B] at h₁ h₂ h₃
  exact (h₁.trans (h₂.trans h₃)).of_eq (by omega)

theorem finish_run (ans : Bool) :
    TM2Program.Run prog 1 ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩
      ⟨none, none, stk (mkV [] [] [] []) [ans]⟩ := by
  refine TM2Program.Run.head ?_ (TM2Program.Run.zero _)
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_none]
  rfl

def enc (l : List Bool) : List G := l.map Sum.inl

@[simp] theorem enc_nil : enc [] = [] := rfl
@[simp] theorem enc_cons (b : Bool) (l : List Bool) : enc (b :: l) = .inl b :: enc l := rfl
@[simp] theorem length_enc (l : List Bool) : (enc l).length = l.length := List.length_map _

theorem step_c0_nil (fl : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c0_cons (fl x : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV (enc (x :: r)) [] a b) []⟩ =
      some ⟨some (.c1 fl x), some (.inl x), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_nil (fl x : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl x), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  cases x <;>
  · simp only [TM2.step, prog, TM2.stepAux]
    rw [update_stk_some]
    simp [stk, mkV]

theorem step_c1_ff (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (false :: r)) [] a b) []⟩ =
      some ⟨some (.restore fl), some (.inl false), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_ft (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (true :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl none), some (.inl true), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_t (fl s : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl true), v, stk (mkV (enc (s :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl (some s)), some (.inl s), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_nil (fl : Bool) (o : Option Bool) (i a : List G) (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a []) []⟩ =
      some ⟨some (.c0 fl), none, stk (mkV i [] a []) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_cons (fl : Bool) (o : Option Bool) (x : Bool) (i a : List G) (bs : List Bool)
    (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || decide (some (Sum.inl x : G) = o.map fun s => .inl (!s)))),
        some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [stk, mkV, update_stk_some]

theorem step_adv_none_cons (fl x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl none), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 fl), some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; simp

theorem step_adv_some_cons (fl s x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl (some s)), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || x == !s)), some (.inl x),
        stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; cases x <;> cases s <;> simp

def T : List Bool → List Bool → List Bool → Bool → ℕ
  | false :: false :: r, bs, as, fl =>
      as.length + 3 +
        if fl then T r (as.reverse ++ bs) [] false else r.length + (as.length + bs.length) + 3
  | false :: true :: r, [], as, fl => 3 + T r [] as fl
  | false :: true :: r, x :: bs, as, fl => 3 + T r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => 3 + T r [] as fl
  | true :: s :: r, x :: bs, as, fl => 3 + T r bs (x :: as) (fl || x == !s)
  | r, bs, as, _ => r.length + as.length + bs.length + 4

theorem T_nil (bs as : List Bool) (fl : Bool) : T [] bs as fl = 0 + as.length + bs.length + 4 :=
  rfl

theorem T_single (b : Bool) (bs as : List Bool) (fl : Bool) :
    T [b] bs as fl = 1 + as.length + bs.length + 4 := by
  cases b <;> rfl

theorem enc_reverse_append (as bs : List Bool) :
    (enc as).reverse ++ enc bs = enc (as.reverse ++ bs) := by
  simp [enc]

theorem scan (r bs as : List Bool) (fl : Bool) (v : St) :
    TM2Program.Run prog (T r bs as fl) ⟨some (.c0 fl), v, stk (mkV (enc r) [] (enc as) (enc bs)) []⟩
      ⟨some (.finish (evalCNF r bs as fl)), none, stk (mkV [] [] [] []) []⟩ := by
  induction r, bs, as, fl using evalCNF.induct generalizing v with
  | case1 r bs as fl ih =>
      have hR := loop_run .A some (some .B) (.restore fl)
        (if fl then .c0 false else .drainI false) rfl (by simp) [] (enc as) (enc as) []
        (some (.inl false)) (mkV (enc r) [] (enc as) (enc bs)) rfl rfl (by simp [mkV])
      simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_A, mkV, update_mkV_B,
        enc_reverse_append] at hR
      have h₀ := step_c0_cons fl false (false :: r) (enc as) (enc bs) v
      have h₁ := step_c1_ff fl r (enc as) (enc bs) (some (.inl false))
      cases fl
      · have hD := drain_run false (enc r) [] (enc (as.reverse ++ bs)) none
        exact (TM2Program.Run.head h₀ (TM2Program.Run.head h₁ (hR.trans hD))).of_eq
          (by simp [T]; omega)
      · have hI := ih none
        exact (TM2Program.Run.head h₀ (TM2Program.Run.head h₁ (hR.trans hI))).of_eq
          (by simp [T]; omega)
  | case2 r as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl false (true :: r) (enc as) [] v)
        (TM2Program.Run.head (step_c1_ft fl r (enc as) [] _)
          (TM2Program.Run.head (step_adv_nil fl none (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case3 r x bs as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl false (true :: r) (enc as) (enc (x :: bs)) v)
        (TM2Program.Run.head (step_c1_ft fl r (enc as) (enc (x :: bs)) _)
          (TM2Program.Run.head (step_adv_none_cons fl x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case4 s r as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl true (s :: r) (enc as) [] v)
        (TM2Program.Run.head (step_c1_t fl s r (enc as) [] _)
          (TM2Program.Run.head (step_adv_nil fl (some s) (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case5 s r x bs as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl true (s :: r) (enc as) (enc (x :: bs)) v)
        (TM2Program.Run.head (step_c1_t fl s r (enc as) (enc (x :: bs)) _)
          (TM2Program.Run.head (step_adv_some_cons fl s x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := TM2Program.Run.head (step_c0_nil fl (enc as) (enc bs) v) hD
        rw [T_nil]
        exact h.of_eq (by simp)
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := TM2Program.Run.head (step_c0_cons fl b [] (enc as) (enc bs) v)
          (TM2Program.Run.head (step_c1_nil fl b (enc as) (enc bs) (some (.inl b))) hD)
        rw [T_single]
        have h' := h.of_eq (m := 1 + as.length + bs.length + 4) (by simp; omega)
        cases b <;> exact h'
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

theorem T_le (r bs as : List Bool) (fl : Bool) :
    T r bs as fl ≤ (r.length + 1) * (bs.length + as.length + 5) := by
  induction r, bs, as, fl using evalCNF.induct with
  | case1 r bs as fl ih =>
      cases fl
      · simp [T]; nlinarith
      · simp [T] at ih ⊢; nlinarith
  | case2 r as fl ih => simp [T] at ih ⊢; nlinarith
  | case3 r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case4 s r as fl ih => simp [T] at ih ⊢; nlinarith
  | case5 s r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · rw [T_nil]; simp; nlinarith
      · rw [T_single]; simp; nlinarith
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

def encR (y : List Bool) : List G := y.map fun b => .inr (some b)

theorem prefix_run (w y : List Bool) :
    TM2Program.Run prog (w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1))
      ⟨some .read1, none, stk (mkV (enc w ++ .inr none :: encR y) [] [] []) []⟩
      ⟨some (.c0 false), none, stk (mkV (enc w) [] [] (enc y)) []⟩ := by
  have h₁ := loop_run .inp gRead1 (some .F) .read1 .read2 rfl (by simp) [] (enc w) (enc w)
    (.inr none :: encR y) none (mkV (enc w ++ .inr none :: encR y) [] [] [])
    (by simp [enc, gRead1]) rfl rfl
  have h₂ := loop_run .inp gRead2 (some .A) .read2 .back1 rfl (by simp) [] (encR y) (enc y) []
    (some (.inr none)) (mkV (encR y) (enc w).reverse [] []) (by simp [encR, enc, gRead2]) rfl
    (by simp [mkV])
  have h₃ := loop_run .F some (some .inp) .back1 .back2 rfl (by simp) [] (enc w).reverse
    (enc w).reverse [] none (mkV [] (enc w).reverse (enc y).reverse []) rfl rfl (by simp [mkV])
  have h₄ := loop_run .A some (some .B) .back2 (.c0 false) rfl (by simp) [] (enc y).reverse
    (enc y).reverse [] none (mkV (enc w) [] (enc y).reverse []) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil,
    update_mkV_inp, update_mkV_F, update_mkV_A, update_mkV_B, mkV, List.append_nil,
    List.reverse_reverse] at h₁ h₂ h₃ h₄
  exact (((h₁.trans h₂).trans h₃).trans h₄).of_eq (by simp [encR])

theorem initList_tm (l : List G) :
    initList tm l = ⟨some .read1, none, stk (mkV l [] [] []) []⟩ := by
  simp only [initList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

theorem haltList_tm (l : List Bool) :
    haltList tm l = ⟨none, none, stk (mkV [] [] [] []) l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

def totalSteps (w y : List Bool) : ℕ :=
  w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1) + T w y [] false + 1

noncomputable def time : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.X + Polynomial.C 5) ^ 2

noncomputable def verifier :
    TM2ComputableInPolyTime pairEncode (fun b : Bool => [b]) (fun p => check p.1 p.2) where
  tm := tm
  inputAlphabet := Equiv.refl G
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun p => by
    obtain ⟨w, y⟩ := p
    have hin : List.map (Equiv.refl G).invFun (pairEncode (w, y)) =
        enc w ++ .inr none :: encR y := by
      simp [pairEncode, enc, encR]
    have hlen : (pairEncode (w, y)).length = w.length + 1 + y.length := by
      simp only [pairEncode, List.length_append, List.length_map, List.length_cons]
      omega
    have hrun := ((prefix_run w y).trans (scan w y [] false none)).trans (finish_run (check w y))
    unfold TM2OutputsInTime
    refine { steps := totalSteps w y, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      erw [hin, initList_tm, Option.map_some, haltList_tm]
      exact hrun
    · rw [hlen, totalSteps]
      have hT := T_le w y [] false
      simp only [time, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, List.length_nil] at hT ⊢
      nlinarith

end Verifier

end Cslib.Complexity.DenseSAT
end

-- CSLibExt.Computability.Complexity.CookLevin.Family
section
namespace Cslib.Complexity.CookLevin.Family

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.CounterView

structure Layout where

  A : ℕ

  KK : ℕ

  g : ℕ

  d : ℕ

namespace Layout

variable (L : Layout)

def rowW (H : ℕ) : ℕ := L.A + L.KK * (H * L.g)

def numVars (T H : ℕ) : ℕ := (T + 1) * L.rowW H

def xIdx (H t a : ℕ) : ℕ := t * L.rowW H + a

def cIdx (H t k j x : ℕ) : ℕ := t * L.rowW H + L.A + (k * H + j) * L.g + x

def nLits : ℕ := L.KK * L.d + 2

end Layout

section Spec

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ)

def litPos (H t i j : ℕ) : ℕ :=
  if j = 0 then L.xIdx H t (la i)
  else if j ≤ L.KK * L.d then
    L.cIdx H t ((j - 1) / L.d) ((j - 1) % L.d) (wa i ((j - 1) / L.d) ((j - 1) % L.d))
  else L.xIdx H (t + 1) (na i)

def lits (H t i : ℕ) : List (ℕ × Bool) :=
  (List.range L.nLits).map fun j => (litPos L la na wa H t i j, decide (j = L.nLits - 1))

def denseClause (V : ℕ) (ls : List (ℕ × Bool)) : Clause :=
  (List.range V).map fun v => ls.lookup v

def family (T H N : ℕ) : CNF :=
  (List.range T).flatMap fun t =>
    (List.range N).map fun i => denseClause (L.numVars T H) (lits L la na wa H t i)

end Spec

def gapEnc : ℕ → List (ℕ × Bool) → ℕ → List Bool
  | lo, [], V => rep [false, true] (V - lo)
  | lo, (p, b) :: r, V => rep [false, true] (p - lo) ++ encodeSlot (some b) ++ gapEnc (p + 1) r V

def Inc : ℕ → List (ℕ × Bool) → ℕ → Prop
  | lo, [], V => lo ≤ V
  | lo, (p, _) :: r, V => lo ≤ p ∧ Inc (p + 1) r V

theorem Inc.le : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Inc lo ls V → lo ≤ V
  | _, [], _, h => h
  | _, (_, _) :: _, _, ⟨h1, h2⟩ => by have := Inc.le h2; omega

theorem lookup_cons_ne {p i : ℕ} {b : Bool} {r : List (ℕ × Bool)} (h : i ≠ p) :
    ((p, b) :: r).lookup i = r.lookup i := by
  have : (i == p) = false := beq_eq_false_iff_ne.mpr h
  rw [List.lookup_cons, this]

theorem Inc.mono_lo {lo lo' : ℕ} {ls : List (ℕ × Bool)} {V : ℕ} (h : lo' ≤ lo) (hi : Inc lo ls V) :
    Inc lo' ls V := by
  cases ls with
  | nil => exact le_trans h hi
  | cons pb r => obtain ⟨p, b⟩ := pb; exact ⟨le_trans h hi.1, hi.2⟩

theorem Inc.lookup_none : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Inc lo ls V →
    ∀ i, i < lo → ls.lookup i = none
  | _, [], _, _, _, _ => rfl
  | _, (_, _) :: _, _, ⟨h1, h2⟩, i, hi => by
      rw [lookup_cons_ne (by omega)]; exact Inc.lookup_none h2 i (by omega)

theorem flatMap_none {l : List ℕ} {f : ℕ → Option Bool} (h : ∀ i ∈ l, f i = none) :
    (l.map f).flatMap encodeSlot = rep [false, true] l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_cons, rep_succ]
      rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]
      rfl

theorem gapEnc_eq : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Inc lo ls V →
    ((List.range' lo (V - lo)).map fun v => ls.lookup v).flatMap encodeSlot = gapEnc lo ls V
  | lo, [], V, _ => by
      rw [flatMap_none (f := fun v => List.lookup v []) (fun _ _ => rfl), List.length_range']; rfl
  | lo, (p, b) :: r, V, ⟨h1, h2⟩ => by
      have hV := Inc.le h2
      have hsplit : List.range' lo (V - lo) =
          List.range' lo (p - lo) ++ (p :: List.range' (p + 1) (V - (p + 1))) := by
        rw [show V - lo = (p - lo) + (V - (p + 1) + 1) by omega, ← List.range'_append,
          show lo + 1 * (p - lo) = p by omega]
        rfl
      rw [hsplit, List.map_append, List.flatMap_append, List.map_cons, List.flatMap_cons,
        gapEnc, flatMap_none, List.length_range']
      · have hp : ((p, b) :: r).lookup p = some b := by simp
        have hm : (List.range' (p + 1) (V - (p + 1))).map (fun v => ((p, b) :: r).lookup v) =
            (List.range' (p + 1) (V - (p + 1))).map (fun v => r.lookup v) := by
          refine List.map_congr_left fun v hv => ?_
          rw [List.mem_range'_1] at hv
          exact lookup_cons_ne (by omega)
        rw [hp, hm, gapEnc_eq h2]
        simp [List.append_assoc]
      · intro v hv
        rw [List.mem_range'_1] at hv
        rw [lookup_cons_ne (by omega)]
        exact Inc.lookup_none h2 v (by omega)

theorem encodeClause_denseClause {ls : List (ℕ × Bool)} {V : ℕ} (h : Inc 0 ls V) :
    encodeClause (denseClause V ls) = gapEnc 0 ls V ++ [false, false] := by
  rw [encodeClause, denseClause, List.range_eq_range', ← gapEnc_eq h]
  rfl

theorem gapEnc_shift {lo lo' : ℕ} {ls : List (ℕ × Bool)} {V : ℕ} (hlo : lo ≤ lo')
    (h : Inc lo' ls V) : gapEnc lo ls V = rep [false, true] (lo' - lo) ++ gapEnc lo' ls V := by
  cases ls with
  | nil => simp only [gapEnc]; rw [← rep_add]; congr 1; have := Inc.le h; simp [Inc] at h; omega
  | cons pb r =>
      obtain ⟨p, b⟩ := pb
      obtain ⟨h1, -⟩ := h
      simp only [gapEnc, ← List.append_assoc, ← rep_add]
      congr 3; omega

theorem div_mod_succ_of_lt {c d : ℕ} (hd : 0 < d) (h : c % d + 1 < d) :
    (c + 1) / d = c / d ∧ (c + 1) % d = c % d + 1 := by
  have hc := Nat.div_add_mod c d
  have e : c + 1 = (c % d + 1) + d * (c / d) := by omega
  constructor
  · rw [e, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt h, Nat.zero_add]
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem div_mod_succ_of_eq {c d : ℕ} (hd : 0 < d) (h : c % d + 1 = d) :
    (c + 1) / d = c / d + 1 ∧ (c + 1) % d = 0 := by
  have hc := Nat.div_add_mod c d
  have e : c + 1 = d * (c / d + 1) := by rw [Nat.mul_succ]; omega
  rw [e, Nat.mul_div_cancel_left _ hd, Nat.mul_mod_right]
  exact ⟨rfl, rfl⟩

theorem inc_of_mono (f : ℕ → ℕ × Bool) (m V : ℕ)
    (hmono : ∀ j, j + 1 < m → (f j).1 < (f (j + 1)).1) (hlast : ∀ j, j + 1 = m → (f j).1 < V) :
    ∀ n a lo, a + n = m → (n = 0 → lo ≤ V) → (0 < n → lo ≤ (f a).1) →
      Inc lo ((List.range' a n).map f) V := by
  intro n
  induction n with
  | zero => intro a lo _ h0 _; exact h0 rfl
  | succ n ih =>
      intro a lo ham _ hpos
      refine ⟨hpos (Nat.succ_pos _), ih (a + 1) _ (by omega) (fun hn => ?_) (fun _ => ?_)⟩
      · exact hlast a (by omega)
      · exact hmono a (by omega)

section Sorted

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ)

structure WF (H i : ℕ) : Prop where
  la_lt : la i < L.A
  na_lt : na i < L.A
  wa_lt : ∀ k < L.KK, ∀ j < L.d, wa i k j < L.g
  d_le : L.d ≤ H

variable {L la na wa}

theorem cIdx_lt_next_row {H t k j x : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.cIdx H t k j x < (t + 1) * L.rowW H := by
  unfold Layout.cIdx Layout.rowW
  have h1 : (k * H + j) * L.g + x < (k * H + H) * L.g := by
    have : (k * H + j) * L.g + L.g ≤ (k * H + H) * L.g := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : (k * H + H) * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk)
  rw [Nat.succ_mul]; omega

theorem litPos_mono {H t i : ℕ} (hwf : WF L la na wa H i) (j : ℕ) (hj : j + 1 < L.nLits) :
    litPos L la na wa H t i j < litPos L la na wa H t i (j + 1) := by
  obtain ⟨hla, hna, hwa, hdH⟩ := hwf
  unfold Layout.nLits at hj
  have hW : L.A ≤ L.rowW H := Nat.le_add_right _ _
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  ·
    rw [litPos, litPos, if_pos rfl, if_neg (by omega : (0 : ℕ) + 1 ≠ 0)]
    split_ifs with h1
    · unfold Layout.xIdx Layout.cIdx; omega
    · unfold Layout.xIdx; rw [Nat.add_one_mul]; omega
  · have hd : 0 < L.d := Nat.pos_of_ne_zero fun h => by simp [h] at hj; omega
    have hcell : j ≤ L.KK * L.d := by omega
    simp only [litPos, if_neg (show j ≠ 0 by omega), if_neg (show j + 1 ≠ 0 by omega),
      if_pos hcell, Nat.add_sub_cancel]
    have hq : (j - 1) / L.d < L.KK := by
      rw [Nat.div_lt_iff_lt_mul hd]; omega
    have hr : (j - 1) % L.d < L.d := Nat.mod_lt _ hd
    split_ifs with h2
    ·
      have hc := Nat.div_add_mod (j - 1) L.d
      have hj' : j = j - 1 + 1 := by omega
      rcases Nat.lt_or_ge ((j - 1) % L.d + 1) L.d with h3 | h3
      · obtain ⟨e1, e2⟩ := div_mod_succ_of_lt hd h3
        rw [hj'] at e1 e2 ⊢
        simp only [Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        unfold Layout.cIdx
        have := hwa ((j - 1) / L.d) hq ((j - 1) % L.d) hr
        rw [show (j - 1) / L.d * H + ((j - 1) % L.d + 1) =
          (j - 1) / L.d * H + (j - 1) % L.d + 1 by omega, Nat.succ_mul]
        omega
      · obtain ⟨e1, e2⟩ := div_mod_succ_of_eq (c := j - 1) hd (by omega)
        rw [hj'] at e1 e2 ⊢
        simp only [Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        unfold Layout.cIdx
        have := hwa ((j - 1) / L.d) hq ((j - 1) % L.d) hr
        have hle : ((j - 1) / L.d * H + (j - 1) % L.d) * L.g + L.g ≤
            ((j - 1) / L.d + 1) * H * L.g := by
          rw [← Nat.succ_mul, Nat.succ_mul ((j - 1) / L.d)]
          exact Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_zero]; omega
    ·
      unfold Layout.xIdx
      have := cIdx_lt_next_row (H := H) (t := t) hq (by omega : (j - 1) % L.d < H)
        (hwa ((j - 1) / L.d) hq ((j - 1) % L.d) hr)
      omega

theorem lits_inc {T H t i : ℕ} (ht : t < T) (hwf : WF L la na wa H i) :
    Inc 0 (lits L la na wa H t i) (L.numVars T H) := by
  unfold lits
  rw [List.range_eq_range']
  refine inc_of_mono _ L.nLits _ (fun j hj => litPos_mono hwf j hj) (fun j hj => ?_)
    L.nLits 0 0 (by omega) (by simp [Layout.nLits]) (fun _ => Nat.zero_le _)
  have hj : j = L.KK * L.d + 1 := by unfold Layout.nLits at hj; omega
  simp only [hj, litPos, Nat.add_one_ne_zero, if_false,
    if_neg (show ¬(L.KK * L.d + 1 ≤ L.KK * L.d) by omega)]
  unfold Layout.xIdx Layout.numVars
  have : na i < L.rowW H := lt_of_lt_of_le hwf.na_lt (Nat.le_add_right _ _)
  have : (t + 1 + 1) * L.rowW H ≤ (T + 1) * L.rowW H := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul (t + 1)] at this; omega

end Sorted

inductive CK
  | Tn | Ti | Hs | Gc | HG | Ka | Wc | Vc | TW | P | Q | tmp | md | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Ti, CK.Hs, CK.Gc, CK.HG, CK.Ka, CK.Wc, CK.Vc, CK.TW, CK.P, CK.Q, CK.tmp,
      CK.md, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

abbrev GK := SK CK

abbrev GΓ := SΓ CK

inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | dk | cp1 | cp2 | inc | v (s : MS) | dk2
  deriving DecidableEq, Fintype

inductive LS
  | cp1 | cp2 | ea | ma (s : MS) | da | eb | mb (s : MS) | db | ec
  | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

inductive GeneratorLabel (N m : ℕ)
  | pre (s : PS)
  | tHead | tRest
  | tw (s : MS)
  | e00 (i : Fin N) | cv1 (i : Fin N) | cv2 (i : Fin N)
  | lit (i : Fin N) (j : Fin m) (s : LS)
  | fin (i : Fin N)
  | dtw | done
  deriving DecidableEq, Fintype

namespace GeneratorLabel

variable {N m : ℕ}

def litL (i : Fin N) (j : ℕ) : GeneratorLabel N m := if h : j < m then .lit i ⟨j, h⟩ .cp1 else .done

def after (i : Fin N) (j : ℕ) : GeneratorLabel N m := if j = 0 then .fin i else litL i (j - 1)

def sitL (i : ℕ) : GeneratorLabel N m := if h : i < N then .e00 ⟨i, h⟩ else .dtw

def afterS (i : ℕ) : GeneratorLabel N m := if i = 0 then .dtw else sitL (i - 1)

theorem litL_of_lt {i : Fin N} {j : ℕ} (h : j < m) : (litL i j : GeneratorLabel N m) = .lit i ⟨j, h⟩ .cp1 :=
  dif_pos h

theorem sitL_of_lt {i : ℕ} (h : i < N) : (sitL i : GeneratorLabel N m) = .e00 ⟨i, h⟩ := dif_pos h

end GeneratorLabel

section Machine

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N : ℕ)

def kA (j : ℕ) : ℕ := if j = 0 then 0 else if j ≤ L.KK * L.d then (j - 1) / L.d else 0

def kB (j : ℕ) : ℕ := if j = 0 then 0 else if j ≤ L.KK * L.d then 0 else 1

def cst (i j : ℕ) : ℕ :=
  if j = 0 then la i
  else if j ≤ L.KK * L.d then L.A + (j - 1) % L.d * L.g + wa i ((j - 1) / L.d) ((j - 1) % L.d)
  else na i

def sgn (j : ℕ) : Bool := decide (j = L.nLits - 1)

def litP (i : Fin N) (j : Fin L.nLits) : LS → TM2.Stmt GΓ (GeneratorLabel N L.nLits) Bool
  | .cp1 => xfer (.c .TW) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit i j .cp1) (.lit i j .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.lit i j .cp2) (.lit i j .ea)
  | .ea => emitR (.c .Ka) (List.replicate (kA L j) ()) (.lit i j (.ma .head))
  | .ma s => mulS .Ka .md .HG .Q .tmp (fun s => .lit i j (.ma s)) (.lit i j .da) s
  | .da => xfer (.c .Ka) [] (.lit i j .da) (.lit i j .eb)
  | .eb => emitR (.c .Ka) (List.replicate (kB L j) ()) (.lit i j (.mb .head))
  | .mb s => mulS .Ka .md .Wc .Q .tmp (fun s => .lit i j (.mb s)) (.lit i j .db) s
  | .db => xfer (.c .Ka) [] (.lit i j .db) (.lit i j .ec)
  | .ec => emitR (.c .Q) (List.replicate (cst L la na wa i j) ()) (.lit i j .dec)
  | .dec => decr (.c .P) (.lit i j .bad) (.lit i j .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit i j .cmp)
      (.lit i j (.r .lt)) (.lit i j (.r .eq)) (.lit i j (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit i j (.r o)) (.lit i j (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit i j (.rB o))
      (if o = .eq then .lit i j .slot else .lit i j .emL)
  | .emL => emitR .out [false, true] (.lit i j .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (sgn L j))) (.lit i j .dq)
  | .dq => xfer (.c .Q) [] (.lit i j .dq) (GeneratorLabel.after i j)

def prog : GeneratorLabel N L.nLits → TM2.Stmt GΓ (GeneratorLabel N L.nLits) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Ka) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Ka .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre .dk) s
  | .pre .dk => xfer (.c .Ka) [] (.pre .dk) (.pre .cp1)
  | .pre .cp1 => xfer (.c .Tn) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.pre .cp1) (.pre .cp2)
  | .pre .cp2 => xfer (.c .tmp) [⟨.c .Tn, ()⟩] (.pre .cp2) (.pre .inc)
  | .pre .inc => incr (.c .Ka) () (.pre (.v .head))
  | .pre (.v s) => mulS .Ka .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .dk2) s
  | .pre .dk2 => xfer (.c .Ka) [] (.pre .dk2) .tHead
  | .tHead => forHead (.c .Tn) (.c .Ti) () (.tw .head) .tRest
  | .tRest => xfer (.c .Ti) [⟨.c .Tn, ()⟩] .tRest .done
  | .tw s => mulS .Tn .md .Wc .TW .tmp .tw (GeneratorLabel.afterS N) s
  | .e00 i => emitR .out [false, false] (.cv1 i)
  | .cv1 i => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 i) (.cv2 i)
  | .cv2 i => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 i) (GeneratorLabel.litL i (L.nLits - 1))
  | .lit i j s => litP L la na wa N i j s
  | .fin i => xferE (.c .P) .out [false, true] (.fin i) (GeneratorLabel.afterS i)
  | .dtw => xfer (.c .TW) [] .dtw .tHead
  | .done => .halt

def genTM : FinTM2 where
  K := GK
  k₀ := .c .Tn
  k₁ := .out
  Γ := GΓ
  Λ := GeneratorLabel N L.nLits
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L la na wa N

end Machine

theorem kA_le (L : Layout) (j : ℕ) : kA L j ≤ L.KK := by
  unfold kA
  split_ifs with h0 h1
  · exact Nat.zero_le _
  · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; omega)
  · exact Nat.zero_le _

theorem kB_le (L : Layout) (j : ℕ) : kB L j ≤ 1 := by
  unfold kB; split_ifs <;> omega

section Correct

variable (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N : ℕ)

structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  Ka : F .Ka = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem lit_run (i : Fin N) (j : Fin L.nLits) (F : CK → ℕ) (hF : Rest F) (q gap : ℕ)
    (hq : q = F .TW + kA L j * F .HG + kB L j * F .Wc + cst L la na wa i j)
    (hp : F .P = q + gap + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L la na wa N)
      (gap * (3 * q + 6) + 2 * F .TW + L.KK * (2 * F .HG + 3) + 2 * L.KK + 2 * F .Wc + 4 * q + 22)
      ⟨some (.lit i j .cp1), v, st F o⟩
      ⟨some (GeneratorLabel.after i j), false,
        st (update F .P q) (encodeSlot (some (sgn L j)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, hKa, htmp, hmd, hc1, hc2⟩ := hF
  refine Bud.start ?_

  refine (copy_run (M := prog L la na wa N) (a := .c .TW) (c := .c .Q) (t := .c .tmp)
    (l₁ := .lit i j .cp1) (l₂ := .lit i j .cp2) (next := .lit i j .ea) rfl rfl
    (by decide) (by decide) (by decide) (F .TW) 0 v (st F o) rfl (by simp [hQ])
    (by simp [htmp])).bud ?_
  rw [update_st_c]

  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .ea)
    (next := .lit i j (.ma .head)) (k := .c .Ka) rfl _ _).bud ?_
  rw [emitR_st]

  refine (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .HG)
    (c := .c .Q) (t := .c .tmp) (head := .lit i j (.ma .head)) (body := .lit i j (.ma .body))
    (l₂ := .lit i j (.ma .l2)) (rest := .lit i j (.ma .rest)) (next := .lit i j .da)
    rfl rfl rfl rfl (by decide) _ _ _ _ _ rfl (by simp [hmd]) rfl rfl
    (by simp [htmp])).bud ?_
  rw [update_st_c]

  refine (xfer_run (M := prog L la na wa N) (self := .lit i j .da) (next := .lit i j .eb)
    (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
    rfl).bud ?_
  rw [addU_nil, update_st_nil]

  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .eb)
    (next := .lit i j (.mb .head)) (k := .c .Ka) rfl _ _).bud ?_
  rw [emitR_st]

  refine (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .Wc)
    (c := .c .Q) (t := .c .tmp) (head := .lit i j (.mb .head)) (body := .lit i j (.mb .body))
    (l₂ := .lit i j (.mb .l2)) (rest := .lit i j (.mb .rest)) (next := .lit i j .db)
    rfl rfl rfl rfl (by decide) _ _ _ _ _ rfl (by simp [hmd]) rfl rfl
    (by simp [htmp])).bud ?_
  rw [update_st_c]

  refine (xfer_run (M := prog L la na wa N) (self := .lit i j .db) (next := .lit i j .ec)
    (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
    rfl).bud ?_
  rw [addU_nil, update_st_nil]

  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .ec)
    (next := .lit i j .dec) (k := .c .Q) rfl _ _).bud ?_
  rw [emitR_st]

  refine (emitDiff_run (M := prog L la na wa N) (P := .c .P) (Q := .c .Q) (T1 := .c .c1)
    (T2 := .c .c2) (o := .out) (ys := [false, true]) (dec := .lit i j .dec)
    (cmpL := .lit i j .cmp) (emitL := .lit i j .emL) (ifZero := .lit i j .bad)
    (next := .lit i j .slot) (r := fun o => .lit i j (.r o)) (rB := fun o => .lit i j (.rB o))
    (out := fun o => if o = .eq then .lit i j .slot else .lit i j .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _ _
    (by simp [hp]) (by rw [st_c]; congr 1; simp [hKa, hq]; ring) (by simp [hc1])
    (by simp [hc2])).bud ?_
  rw [update_st_c, update_st_out]

  refine (emitR_run (M := prog L la na wa N) (self := .lit i j .slot)
    (next := .lit i j .dq) (k := .out) rfl _ _).bud ?_
  rw [update_st_out]

  refine (xfer_run (M := prog L la na wa N) (self := .lit i j .dq)
    (next := GeneratorLabel.after i j)
    (k := .c .Q) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
    rfl).bud ?_
  rw [addU_nil, update_st_nil]
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * F .HG + 3) (kA_le L j)
    have h2 := Nat.mul_le_mul_right (2 * F .Wc + 3) (kB_le L j)
    have h3 := kA_le L j
    have h4 := kB_le L j
    simp [hKa]
    omega
  simp only [TM2.Cfg.mk.injEq, true_and]
  refine ⟨rfl, ?_⟩
  congr 1
  funext x; cases x <;> simp [hQ, hKa]

end Correct

section Clause

variable {L : Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

theorem litPos_eq (H t i j : ℕ) :
    litPos L la na wa H t i j =
      t * L.rowW H + kA L j * (H * L.g) + kB L j * L.rowW H + cst L la na wa i j := by
  unfold litPos kA kB cst Layout.xIdx Layout.cIdx
  split_ifs <;> ring

theorem lits_drop (H t i j : ℕ) :
    (lits L la na wa H t i).drop j =
      (List.range' j (L.nLits - j)).map
        fun j => (litPos L la na wa H t i j, decide (j = L.nLits - 1)) := by
  rw [lits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

def bnd (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (T H t i j : ℕ) : ℕ :=
  if j < L.nLits then litPos L la na wa H t i j else L.numVars T H

theorem inc_drop {T H t i : ℕ} (ht : t < T) (hwf : WF L la na wa H i) (j : ℕ)
    (hjm : j ≤ L.nLits) :
    Inc (bnd L la na wa T H t i j) ((lits L la na wa H t i).drop j) (L.numVars T H) := by
  have h0 := lits_inc (T := T) ht hwf
  rw [lits_drop]
  unfold lits at h0
  refine inc_of_mono _ L.nLits _ (fun j hj => litPos_mono hwf j hj) (fun k hk => ?_)
    (L.nLits - j) j _ ?_ (fun hn => ?_) (fun hn => ?_)
  ·
    have := lits_inc (T := T) ht hwf
    have hlast : litPos L la na wa H t i k < L.numVars T H := by
      have hk' : k = L.KK * L.d + 1 := by unfold Layout.nLits at hk; omega
      simp only [hk', litPos, Nat.add_one_ne_zero, if_false,
        if_neg (show ¬(L.KK * L.d + 1 ≤ L.KK * L.d) by omega)]
      unfold Layout.xIdx Layout.numVars
      have h1 : na i < L.rowW H := lt_of_lt_of_le hwf.na_lt (Nat.le_add_right _ _)
      have h2 : (t + 1 + 1) * L.rowW H ≤ (T + 1) * L.rowW H := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_one_mul (t + 1)] at h2; omega
    exact hlast
  · omega
  · simp only [bnd]; split_ifs with h
    · omega
    · exact le_rfl
  · simp only [bnd, if_pos (show j < L.nLits by omega)]; exact le_rfl

theorem bnd_lt {T H t i j : ℕ} (ht : t < T) (hwf : WF L la na wa H i) (hj : j < L.nLits) :
    litPos L la na wa H t i j < bnd L la na wa T H t i (j + 1) := by
  unfold bnd
  split_ifs with h
  · exact litPos_mono hwf j h
  · have := inc_drop (T := T) ht hwf j hj.le
    rw [lits_drop, show L.nLits - j = 0 + 1 by omega] at this
    simp only [List.range'_succ, List.map_cons, List.range'_zero, List.map_nil] at this
    obtain ⟨-, h2⟩ := this
    exact h2

structure Base (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Rest F where
  TW : F .TW = t * L.rowW H
  HG : F .HG = H * L.g
  Wc : F .Wc = L.rowW H
  Vc : F .Vc = L.numVars T H

theorem Rest.update_P {F : CK → ℕ} (h : Rest F) (n : ℕ) : Rest (update F .P n) :=
  ⟨by simp [h.Q], by simp [h.Ka], by simp [h.tmp], by simp [h.md], by simp [h.c1], by simp [h.c2]⟩

def litE (L : Layout) (T H : ℕ) : ℕ :=
  6 * L.numVars T H + L.KK * (2 * (H * L.g) + 3) + 2 * L.KK + 2 * L.rowW H + 22

def clauseB (L : Layout) (T H : ℕ) : ℕ :=
  L.numVars T H * (3 * L.numVars T H + 6) + L.nLits * litE L T H + 3 * L.numVars T H + 4

theorem bnd_le {T H t i : ℕ} (ht : t < T) (hwf : WF L la na wa H i) {j : ℕ} (hj : j ≤ L.nLits) :
    bnd L la na wa T H t i j ≤ L.numVars T H :=
  (inc_drop ht hwf j hj).le

theorem tW_le {T H t : ℕ} (ht : t < T) : t * L.rowW H ≤ L.numVars T H :=
  Nat.mul_le_mul_right _ (by omega)

theorem lits_run {T H t : ℕ} {i : Fin N} (ht : t < T) (hwf : WF L la na wa H i) (F : CK → ℕ)
    (hF : Base L T H t F) (o : List Bool) :
    ∀ j, j ≤ L.nLits → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L la na wa N)
        (bnd L la na wa T H t i j * (3 * L.numVars T H + 6) + j * litE L T H)
        ⟨some (GeneratorLabel.after i j), v,
          st (update F .P (bnd L la na wa T H t i j))
            (gapEnc (bnd L la na wa T H t i j) ((lits L la na wa H t i).drop j)
              (L.numVars T H) ++ [false, false] ++ o)⟩
        ⟨some (.fin i), v',
          st (update F .P (bnd L la na wa T H t i 0))
            (gapEnc (bnd L la na wa T H t i 0) (lits L la na wa H t i)
              (L.numVars T H) ++ [false, false] ++ o)⟩ := by
  intro j
  induction j with
  | zero => intro _ v; exact ⟨v, by simpa [GeneratorLabel.after] using RunLe.refl _ _⟩
  | succ j ih =>
      intro hj v
      have hjm : j < L.nLits := by omega
      set p := litPos L la na wa H t i j with hp
      set b := bnd L la na wa T H t i (j + 1) with hb
      have hpb : p < b := bnd_lt ht hwf hjm
      have r := lit_run L la na wa N i ⟨j, hjm⟩ (update F .P b) (hF.toRest.update_P b) p (b - p - 1)
        (by rw [hp, litPos_eq]; simp [hF.TW, hF.HG, hF.Wc])
        (by simp; omega) (gapEnc b ((lits L la na wa H t i).drop (j + 1)) (L.numVars T H) ++
          [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GeneratorLabel.after, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, GeneratorLabel.litL_of_lt hjm]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbj : bnd L la na wa T H t i j = p := by simp [bnd, hjm, hp]
      have hdrop : (lits L la na wa H t i).drop j =
          (p, sgn L j) :: (lits L la na wa H t i).drop (j + 1) := by
        rw [lits_drop, lits_drop, show L.nLits - j = (L.nLits - (j + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
        rfl
      have hshift := gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop ht hwf (j + 1) hj)
      rw [hbj, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)

      have hbV := bnd_le ht hwf hj
      have htw := tW_le (L := L) (H := H) ht
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * L.numVars T H + 6 by omega)
      have h2 : (b - p - 1) * (3 * L.numVars T H + 6) + p * (3 * L.numVars T H + 6) ≤
          b * (3 * L.numVars T H + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF.TW, hF.HG, hF.Wc]
      rw [Nat.add_one_mul j]
      unfold litE
      omega

theorem clause_run {T H t : ℕ} {i : Fin N} (ht : t < T) (hwf : WF L la na wa H i) (F : CK → ℕ)
    (hF : Base L T H t F) (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L la na wa N) (clauseB L T H) ⟨some (.e00 i), v, st F o⟩
      ⟨some (GeneratorLabel.afterS i), false,
        st F (encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i)) ++ o)⟩ := by

  refine Bud.start ?_
  refine (emitR_run (M := prog L la na wa N) (self := .e00 i) (next := .cv1 i) (k := .out)
    rfl v _).bud ?_
  rw [update_st_out]

  refine (copy_run (M := prog L la na wa N) (a := .c .Vc) (c := .c .P) (t := .c .tmp)
    (l₁ := .cv1 i) (l₂ := .cv2 i) (next := GeneratorLabel.litL i (L.nLits - 1)) rfl rfl
    (by decide) (by decide) (by decide) _ 0 v _ rfl (by simp [hP])
    (by simp [hF.tmp])).bud ?_
  rw [update_st_c]

  have hm : L.nLits ≠ 0 := by unfold Layout.nLits; omega
  obtain ⟨v', r⟩ := lits_run (N := N) ht hwf F hF o L.nLits le_rfl
    (Flag.tag false)
  have hbm : bnd L la na wa T H t i L.nLits = L.numVars T H := by simp [bnd]
  rw [GeneratorLabel.after, if_neg hm, hbm, List.drop_eq_nil_of_le (by simp [lits]), gapEnc, Nat.sub_self,
    rep_zero, List.nil_append] at r
  rw [hF.Vc, Nat.add_zero]
  refine r.bud ?_

  refine (xferE_run (M := prog L la na wa N) (self := .fin i)
    (next := GeneratorLabel.afterS i) (k := .c .P) (o := .out)
    (ys := [false, true]) rfl (by simp) () _ v' _ rfl).bud ?_
  rw [update_st_nil, update_st_out]
  have e1 : update (update F .P (bnd L la na wa T H t i 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop (T := T) ht hwf 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i)) =
      rep [false, true] (bnd L la na wa T H t i 0) ++
        gapEnc (bnd L la na wa T H t i 0) (lits L la na wa H t i) (L.numVars T H) ++
          [false, false] := by
    rw [encodeClause_denseClause (lits_inc ht hwf), gapEnc_shift (Nat.zero_le _) h0,
      Nat.sub_zero]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le (j := 0) ht hwf (Nat.zero_le _)
  simp only [update_self]
  unfold clauseB
  omega

end Clause

section Top

variable {L : Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

def blk (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N T H t : ℕ) : List Bool :=
  (List.range N).flatMap fun i => encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i))

theorem sits_run {T H t : ℕ} (ht : t < T) (hwf : ∀ i < N, WF L la na wa H i) (F : CK → ℕ)
    (hF : Base L T H t F) (hP : F .P = 0) :
    ∀ i, i < N → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L la na wa N) ((i + 1) * clauseB L T H) ⟨some (GeneratorLabel.sitL i), v, st F o⟩
        ⟨some .dtw, false, st F ((List.range (i + 1)).flatMap (fun i =>
          encodeClause (denseClause (L.numVars T H) (lits L la na wa H t i))) ++ o)⟩ := by
  intro i
  induction i with
  | zero =>
      intro h0 o v
      rw [GeneratorLabel.sitL_of_lt h0]
      simpa [GeneratorLabel.afterS] using clause_run (i := ⟨0, h0⟩) ht (hwf 0 h0) F hF hP o v
  | succ i ih =>
      intro hi o v
      have r := clause_run (i := ⟨i + 1, hi⟩) ht (hwf (i + 1) hi) F hF hP o v
      rw [GeneratorLabel.sitL_of_lt hi]
      simp only [GeneratorLabel.afterS, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at r
      refine Bud.start (r.bud ?_)
      have := ih (by omega)
        (encodeClause (denseClause (L.numVars T H) (lits L la na wa H t (i + 1))) ++ o) false
      rw [List.range_succ (n := i + 1), List.flatMap_append, List.flatMap_singleton,
          List.append_assoc]
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (i + 1)]; omega

structure LoopP (L : Layout) (T H : ℕ) (f : CK → ℕ) : Prop extends Rest f where
  P : f .P = 0
  TW : f .TW = 0
  HG : f .HG = H * L.g
  Wc : f .Wc = L.rowW H
  Vc : f .Vc = L.numVars T H

def bodyB (L : Layout) (N T H : ℕ) : ℕ :=
  T * (2 * L.rowW H + 3) + T * L.rowW H + T + 3 + N * clauseB L T H

def preB (L : Layout) (T H : ℕ) : ℕ :=
  H * (2 * L.g + 3) + L.KK * (2 * (H * L.g) + 3) + (T + 1) * (2 * L.rowW H + 3) + H + 2 * L.KK +
    4 * T + 16

def genBound (L : Layout) (N T H : ℕ) : ℕ :=
  preB L T H + (T * (bodyB L N T H + 1) + T + 2)

theorem time_body {T H t : ℕ} (ht : t < T) (hwf : ∀ i < N, WF L la na wa H i) (f : CK → ℕ)
    (hf : LoopP L T H f) (hTn : f .Tn = t) (o : List Bool) :
    RunLe (prog L la na wa N) (bodyB L N T H) ⟨some (.tw .head), Flag.tag true, st f o⟩
      ⟨some .tHead, Flag.tag false, st f (blk L la na wa N T H t ++ o)⟩ := by

  refine Bud.start ?_
  refine (mul_run (M := prog L la na wa N) (a := .c .Tn) (ad := .c .md) (b := .c .Wc)
    (c := .c .TW) (t := .c .tmp) (head := .tw .head) (body := .tw .body) (l₂ := .tw .l2)
    (rest := .tw .rest) (next := GeneratorLabel.afterS N) rfl rfl rfl rfl
    (by decide) _ _ _ _ _ rfl (by simp [hf.md]) rfl rfl
    (by simp [hf.tmp])).bud ?_
  rw [update_st_c]
  set F := update f .TW (f .Tn * f .Wc + f .TW) with hFdef
  have hB : Base L T H t F :=
    { Q := by simp [hFdef, hf.Q], Ka := by simp [hFdef, hf.Ka], tmp := by simp [hFdef, hf.tmp],
      md := by simp [hFdef, hf.md], c1 := by simp [hFdef, hf.c1], c2 := by simp [hFdef, hf.c2],
      TW := by simp [hFdef, hTn, hf.Wc, hf.TW], HG := by simp [hFdef, hf.HG],
      Wc := by simp [hFdef, hf.Wc], Vc := by simp [hFdef, hf.Vc] }
  have hFP : F .P = 0 := by simp [hFdef, hf.P]

  have hs : RunLe (prog L la na wa N) (N * clauseB L T H)
      ⟨some (GeneratorLabel.afterS N), Flag.tag false, st F o⟩
      ⟨some .dtw, false, st F (blk L la na wa N T H t ++ o)⟩ := by
    by_cases hN : N = 0
    · subst hN
      simp only [GeneratorLabel.afterS, blk, List.range_zero, List.flatMap_nil, List.nil_append]
      exact RunLe.refl _ _
    · rw [GeneratorLabel.afterS, if_neg hN]
      have := sits_run ht hwf F hB hFP (N - 1) (by omega) o (Flag.tag false)
      rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hN)] at this
  refine hs.bud ?_

  refine (xfer_run (M := prog L la na wa N) (self := .dtw) (next := .tHead) (k := .c .TW)
    (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _ rfl).bud ?_
  rw [addU_nil, update_st_nil]
  have : update F .TW 0 = f := by rw [hFdef, update_idem, ← hf.TW, update_eq_self]
  rw [this]
  refine Bud.fin ?_ rfl
  have h1 := Nat.mul_le_mul_right (2 * L.rowW H + 3) ht.le
  have h2 := Nat.mul_le_mul_right (L.rowW H) ht.le
  simp only [hFdef, update_self, hTn, hf.Wc, hf.TW]
  unfold bodyB
  omega

theorem ex_bud {α Λ : Type} {M : Λ → TM2.Stmt GΓ Λ Bool} {a K X : ℕ}
    {c d : TM2.Cfg GΓ Λ Bool} {P : α → Prop} {e : α → TM2.Cfg GΓ Λ Bool} (h : Run M a c d)
    (h' : ∃ x, P x ∧ Bud M (K + a) X d (e x)) : ∃ x, P x ∧ Bud M K X c (e x) := by
  obtain ⟨x, hx, h'⟩ := h'; exact ⟨x, hx, h.bud h'⟩

theorem LoopP.congr {T H : ℕ} {f f' : CK → ℕ} (h : LoopP L T H f)
    (e : ∀ x, x ≠ .Tn → x ≠ .Ti → f' x = f x) : LoopP L T H f' :=
  { Q := by rw [e _ (by decide) (by decide), h.Q], Ka := by rw [e _ (by decide) (by decide), h.Ka],
    tmp := by rw [e _ (by decide) (by decide), h.tmp],
    md := by rw [e _ (by decide) (by decide), h.md], c1 := by rw [e _ (by decide) (by decide),
        h.c1],
    c2 := by rw [e _ (by decide) (by decide), h.c2], P := by rw [e _ (by decide) (by decide), h.P],
    TW := by rw [e _ (by decide) (by decide), h.TW], HG := by rw [e _ (by decide) (by decide),
        h.HG],
    Wc := by rw [e _ (by decide) (by decide), h.Wc], Vc := by rw [e _ (by decide) (by decide),
        h.Vc] }

def outAfter (L : Layout) (la na : ℕ → ℕ) (wa : ℕ → ℕ → ℕ → ℕ) (N T H ii : ℕ)
    (o : List Bool) : List Bool :=
  (List.range' (T - ii) ii).flatMap (blk L la na wa N T H) ++ o

def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

theorem encodeCNF_family (T H : ℕ) :
    encodeCNF (family L la na wa T H N) = (List.range T).flatMap (blk L la na wa N T H) := by
  simp [encodeCNF, family, List.flatMap_assoc, List.flatMap_map]; rfl

theorem gen_run (T H : ℕ) (hwf : ∀ i < N, WF L la na wa H i) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      RunLe (prog L la na wa N) (genBound L N T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (family L la na wa T H N) ++ o := by

  have pre : ∃ f : CK → ℕ, (LoopP L T H f ∧ f .Tn = T ∧ f .Ti = 0) ∧
      Bud (prog L la na wa N) 0 (preB L T H) ⟨some (.pre .eg), false, st (initF T H) o⟩
        ⟨some .tHead, Flag.tag false, st f o⟩ := by
    refine ex_bud (emitR_run (M := prog L la na wa N) (self := .pre .eg)
      (next := .pre (.hg .head)) (k := .c .Gc) rfl _ _) ?_
    rw [emitR_st]
    refine ex_bud (mul_run (M := prog L la na wa N) (a := .c .Hs) (ad := .c .md) (b := .c .Gc)
      (c := .c .HG) (t := .c .tmp) (head := .pre (.hg .head)) (body := .pre (.hg .body))
      (l₂ := .pre (.hg .l2)) (rest := .pre (.hg .rest)) (next := .pre .ew) rfl rfl rfl rfl
      (by decide) _ _ _ _ _ rfl (by simp [initF]) rfl rfl (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (emitR_run (M := prog L la na wa N) (self := .pre .ew)
      (next := .pre .ek) (k := .c .Wc) rfl _ _) ?_
    rw [emitR_st]
    refine ex_bud (emitR_run (M := prog L la na wa N) (self := .pre .ek)
      (next := .pre (.w .head)) (k := .c .Ka) rfl _ _) ?_
    rw [emitR_st]
    refine ex_bud (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .HG)
      (c := .c .Wc) (t := .c .tmp) (head := .pre (.w .head)) (body := .pre (.w .body))
      (l₂ := .pre (.w .l2)) (rest := .pre (.w .rest)) (next := .pre .dk) rfl rfl rfl rfl
      (by decide) _ _ _ _ _ rfl (by simp [initF]) rfl rfl (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (xfer_run (M := prog L la na wa N) (self := .pre .dk) (next := .pre .cp1)
      (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
      rfl) ?_
    rw [addU_nil, update_st_nil]
    refine ex_bud (copy_run (M := prog L la na wa N) (a := .c .Tn) (c := .c .Ka) (t := .c .tmp)
      (l₁ := .pre .cp1) (l₂ := .pre .cp2) (next := .pre .inc) rfl rfl
      (by decide) (by decide) (by decide) _ 0 _ _ rfl (by simp) (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (incr_run_cnt (M := prog L la na wa N) (self := .pre .inc)
      (next := .pre (.v .head)) (k := .c .Ka) (u := ()) rfl _ (n := T + 0)
      (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (mul_run (M := prog L la na wa N) (a := .c .Ka) (ad := .c .md) (b := .c .Wc)
      (c := .c .Vc) (t := .c .tmp) (head := .pre (.v .head)) (body := .pre (.v .body))
      (l₂ := .pre (.v .l2)) (rest := .pre (.v .rest)) (next := .pre .dk2) rfl rfl rfl rfl
      (by decide) _ _ _ _ _ rfl (by simp [initF]) rfl rfl
      (by simp [initF])) ?_
    rw [update_st_c]
    refine ex_bud (xfer_run (M := prog L la na wa N) (self := .pre .dk2) (next := .tHead)
      (k := .c .Ka) (ps := []) rfl (by simp [List.NodupKeys]) (by simp) () _ _ _
      rfl) ?_
    rw [addU_nil, update_st_nil]
    refine ⟨_, ⟨?_, by simp [initF], by simp [initF]⟩, Bud.fin ?_ rfl⟩
    · exact
      { Q := (by simp [initF]), Ka := (by simp [initF]), tmp := (by simp [initF]),
        md := (by simp [initF]), c1 := (by simp [initF]), c2 := (by simp [initF]),
        P := (by simp [initF]), TW := (by simp [initF]), HG := (by simp [initF]),
        Wc := (by simp [initF, Layout.rowW]; ring),
        Vc := (by simp [initF, Layout.numVars, Layout.rowW]; ring) }
    · simp [initF, preB, Layout.rowW]
      ring_nf
      omega
  obtain ⟨f, ⟨hf, hTn, hTi⟩, hpre⟩ := pre

  obtain ⟨S', hloop, -, -, hout, -⟩ := forLoop_le (M := prog L la na wa N)
    (c := .c .Tn) (cd := .c .Ti) (uc := ()) (ucd := ()) (head := .tHead) (body := .tw .head)
    (rest := .tRest) (next := .done) rfl rfl (by decide) T (bodyB L N T H)
    (fun ii S => S .out = outAfter L la na wa N T H ii o ∧
      LoopP L T H (fun x => (S (.c x)).length))
    (fun ii S S' h ⟨h1, h2⟩ => ⟨by rw [h .out (by simp) (by simp), h1],
      h2.congr fun x h1 h2 => by rw [h (.c x) (by simpa using h1) (by simpa using h2)]⟩)
    (fun ii hii S hS1 hS2 ⟨h1, h2⟩ => by
      have hTn : (fun x => (S (.c x)).length) .Tn = T - 1 - ii := by simp [hS1]
      have r := time_body (N := N) (t := T - 1 - ii) (by omega) hwf _ h2 hTn (S .out)
      rw [← st_eta S] at r
      refine ⟨_, _, r, ?_, ?_, ?_, ?_⟩
      · exact (congrFun (st_eta S) (.c .Tn)).symm
      · exact (congrFun (st_eta S) (.c .Ti)).symm
      · simp only [st_out, h1, outAfter]
        rw [show T - (ii + 1) = T - 1 - ii by omega, List.range'_succ,
          show T - 1 - ii + 1 = T - ii by omega, List.flatMap_cons, List.append_assoc]
      · simpa using h2)
    (Flag.tag false) (st f o) (by simp [hTn]) (by simp [hTi])
    ⟨by simp [outAfter], by simpa using hf⟩
  exact ⟨_, S', (Bud.start hpre).trans hloop, by rw [hout, outAfter, Nat.sub_self,
    ← List.range_eq_range', encodeCNF_family]⟩

theorem gen_correct (T H : ℕ) (hwf : ∀ i < N, WF L la na wa H i) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      Reach (prog L la na wa N) ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (family L la na wa T H N) ++ o :=
  let ⟨v, S, h, h'⟩ := gen_run T H hwf o; ⟨v, S, h.reach, h'⟩

end Top

section Poly

def Layout.uni (k : ℕ) : Layout := ⟨k, k, k, k⟩

theorem genBound_mono {L L' : Layout} {N N' T T' H H' : ℕ} (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK)
    (hg : L.g ≤ L'.g) (hd : L.d ≤ L'.d) (hN : N ≤ N') (hT : T ≤ T') (hH : H ≤ H') :
    genBound L N T H ≤ genBound L' N' T' H' := by
  unfold genBound preB bodyB clauseB litE Layout.numVars Layout.rowW Layout.nLits
  gcongr

theorem genBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    genBound (Layout.uni k) k y y ≤ 323 * k ^ 5 * y ^ 5 := by
  have m : ∀ a b, a ≤ 5 → b ≤ 5 → k ^ a * y ^ b ≤ k ^ 5 * y ^ 5 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold genBound preB bodyB clauseB litE Layout.numVars Layout.rowW Layout.nLits Layout.uni
  simp only
  nlinarith [m 0 0 (by norm_num) (by norm_num), m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num), m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num), m 1 2 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num), m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num), m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num), m 3 3 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num), m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num), m 4 4 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num), m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num)]

def genC (L : Layout) (N : ℕ) : ℕ := 323 * (L.A + L.KK + L.g + L.d + N + 1) ^ 5

theorem genBound_le (L : Layout) (N T H : ℕ) : genBound L N T H ≤ genC L N * (T + H + 1) ^ 5 := by
  have := genBound_mono (L := L) (L' := Layout.uni (L.A + L.KK + L.g + L.d + N + 1))
    (N := N) (N' := L.A + L.KK + L.g + L.d + N + 1) (T := T) (T' := T + H + 1) (H := H)
    (H' := T + H + 1) (by simp only [Layout.uni]; omega) (by simp only [Layout.uni]; omega)
    (by simp only [Layout.uni]; omega) (by simp only [Layout.uni]; omega) (by omega) (by omega)
    (by omega)
  exact this.trans (genBound_uni _ _ (by omega) (by omega))

open Polynomial in

noncomputable def genPoly (L : Layout) (N : ℕ) : Polynomial ℕ := C (genC L N) * (X + 1) ^ 5

theorem genPoly_eval (L : Layout) (N T H : ℕ) :
    (genPoly L N).eval (T + H) = genC L N * (T + H + 1) ^ 5 := by
  simp [genPoly]

theorem gen_time {L : Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N : ℕ} (T H : ℕ)
    (hwf : ∀ i < N, WF L la na wa H i) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      RunLe (prog L la na wa N) (genC L N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (family L la na wa T H N) ++ o :=
  let ⟨v, S, h, h'⟩ := gen_run T H hwf o; ⟨v, S, h.mono (genBound_le L N T H), h'⟩

end Poly

end Cslib.Complexity.CookLevin.Family
end

-- CSLibExt.Computability.Complexity.PairEncodingConverter
section
namespace Cslib.Complexity.DenseSAT.Converter

open Turing Function MetaMathlibExt

def encFst (x : List Bool) : List Bool := x.flatMap fun b => [true, true, true, b, true, false]

def encSnd (w : List Bool) : List Bool := w.flatMap fun b => [true, b, false]

theorem delimit_eq (l : List Bool) :
    BitstringEncoding.delimit l = l.flatMap (fun c => [true, c]) ++ [false] := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [BitstringEncoding.delimit, ih]

theorem bitEncode_list (x : List Bool) : BitstringEncoding.bitEncode x = encSnd x := by
  change (((x.map BitstringEncoding.bitEncode).map BitstringEncoding.delimit).flatten) = _
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp only [List.map_cons, List.flatten_cons, encSnd, List.flatMap_cons] at ih ⊢
      rw [ih]
      rfl

theorem flatMap_delimit_encSnd (x : List Bool) :
    (encSnd x).flatMap (fun c => [true, c]) = encFst x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp only [encSnd, encFst, List.flatMap_cons, List.flatMap_append] at ih ⊢
      rw [ih]
      rfl

theorem bitEncode_pair_eq (x w : List Bool) :
    (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode (x, w) =
      encFst x ++ false :: encSnd w := by
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++
      BitstringEncoding.bitEncode w = _
  rw [bitEncode_list, bitEncode_list, delimit_eq, flatMap_delimit_encSnd]
  simp

inductive Stk | inp | out | fst | snd
  deriving DecidableEq

instance : Fintype Stk where
  elems := ⟨↑[Stk.inp, Stk.out, Stk.fst, Stk.snd], by decide⟩
  complete := fun k => by cases k <;> decide

abbrev Γ : Stk → Type
  | .out => Verifier.G
  | _ => Bool

inductive Lab | readFst | readSnd | emitSnd | sep | emitFst
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.readFst, Lab.readSnd, Lab.emitSnd, Lab.sep, Lab.emitFst], by decide⟩
  complete := fun l => by cases l <;> decide

abbrev St := Option Bool

def prog : Lab → TM2.Stmt Γ Lab St
  | .readFst =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s == some true)
        (.pop .inp (fun s _ => s) <| .pop .inp (fun s _ => s) <| .pop .inp (fun _ o => o) <|
          .pop .inp (fun s _ => s) <| .pop .inp (fun s _ => s) <|
          .push .fst (fun s => s.getD false) <| .goto fun _ => .readFst)
        (.goto fun _ => .readSnd)
  | .readSnd =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s == some true)
        (.pop .inp (fun _ o => o) <| .pop .inp (fun s _ => s) <|
          .push .snd (fun s => s.getD false) <| .goto fun _ => .readSnd)
        (.goto fun _ => .emitSnd)
  | .emitSnd =>
      .pop .snd (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun s => .inr (some (s.getD false))) <| .goto fun _ => .emitSnd)
        (.goto fun _ => .sep)
  | .sep => .push .out (fun _ => .inr none) <| .goto fun _ => .emitFst
  | .emitFst =>
      .pop .fst (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun s => .inl (s.getD false)) <| .goto fun _ => .emitFst)
        .halt

def tm : FinTM2 where
  K := Stk
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := Lab
  main := .readFst
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog

def stk (i : List Bool) (o : List Verifier.G) (a b : List Bool) : ∀ k, List (Γ k)
  | .inp => i
  | .out => o
  | .fst => a
  | .snd => b

@[simp] theorem update_stk_inp (i : List Bool) (o : List Verifier.G) (a b l : List Bool) :
    update (stk i o a b) .inp l = stk l o a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_out (i : List Bool) (o : List Verifier.G) (a b : List Bool)
    (l : List Verifier.G) : update (stk i o a b) .out l = stk i l a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_fst (i : List Bool) (o : List Verifier.G) (a b l : List Bool) :
    update (stk i o a b) .fst l = stk i o l b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_snd (i : List Bool) (o : List Verifier.G) (a b l : List Bool) :
    update (stk i o a b) .snd l = stk i o a l := by
  funext k; cases k <;> rfl

abbrev Run (n : ℕ) (c d : TM2.Cfg Γ Lab St) : Prop := TM2Program.Run prog n c d

theorem readFst_run (x : List Bool) :
    ∀ (rest : List Bool) (o : List Verifier.G) (a b : List Bool) (v : St),
      Run (x.length + 1) ⟨some .readFst, v, stk (encFst x ++ false :: rest) o a b⟩
        ⟨some .readSnd, some false, stk rest o (x.reverse ++ a) b⟩ := by
  induction x with
  | nil =>
      intro rest o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, encFst])
  | cons c x ih =>
      intro rest o a b v
      have h := ih rest o (c :: a) b (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, encFst]

theorem readSnd_run (w : List Bool) :
    ∀ (o : List Verifier.G) (a b : List Bool) (v : St),
      Run (w.length + 1) ⟨some .readSnd, v, stk (encSnd w) o a b⟩
        ⟨some .emitSnd, none, stk [] o a (w.reverse ++ b)⟩ := by
  induction w with
  | nil =>
      intro o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, encSnd])
  | cons c w ih =>
      intro o a b v
      have h := ih o a (c :: b) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, encSnd]

theorem emitSnd_run (b : List Bool) :
    ∀ (o : List Verifier.G) (a : List Bool) (v : St),
      Run (b.length + 1) ⟨some .emitSnd, v, stk [] o a b⟩
        ⟨some .sep, none, stk [] (b.reverse.map (fun c => .inr (some c)) ++ o) a []⟩ := by
  induction b with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])
  | cons c b ih =>
      intro o a v
      have h := ih (.inr (some c) :: o) a (some c)
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk]

theorem sep_run (o : List Verifier.G) (a : List Bool) :
    Run 1 ⟨some .sep, none, stk [] o a []⟩ ⟨some .emitFst, none, stk [] (.inr none :: o) a []⟩ :=
  TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])

theorem emitFst_run (a : List Bool) :
    ∀ (o : List Verifier.G) (v : St),
      Run (a.length + 1) ⟨some .emitFst, v, stk [] o a []⟩
        ⟨none, none, stk [] (a.reverse.map Sum.inl ++ o) [] []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])
  | cons c a ih =>
      intro o v
      have h := ih (.inl c :: o) (some c)
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk]

theorem convert_run (x w : List Bool) :
    Run (2 * x.length + 2 * w.length + 5)
      ⟨some .readFst, none, stk (encFst x ++ false :: encSnd w) [] [] []⟩
      ⟨none, none, stk [] (Verifier.pairEncode (x, w)) [] []⟩ := by
  have h₁ := readFst_run x (encSnd w) [] [] [] none
  have h₂ := readSnd_run w [] (x.reverse ++ []) [] (some false)
  have h₃ := emitSnd_run (w.reverse ++ []) [] (x.reverse ++ []) none
  have h₄ := sep_run ((w.reverse ++ []).reverse.map (fun c => .inr (some c)) ++ [])
    (x.reverse ++ [])
  have h₅ := emitFst_run (x.reverse ++ [])
    (.inr none :: ((w.reverse ++ []).reverse.map (fun c => .inr (some c)) ++ [])) none
  have h := h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
  exact h.of_eq (by omega)

theorem initList_tm (l : List Bool) :
    initList tm l = ⟨some .readFst, none, stk l [] [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Verifier.G) : haltList tm l = ⟨none, none, stk [] l [] []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

noncomputable def computable :
    TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode
      Verifier.pairEncode id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Verifier.G
  time := Polynomial.X + Polynomial.C 5
  outputsFun := fun p => by
    obtain ⟨x, w⟩ := p
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2 * w.length + 5, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      rw [bitEncode_pair_eq]
      erw [List.map_id, List.map_id, initList_tm, Option.map_some, haltList_tm]
      exact convert_run x w
    · rw [bitEncode_pair_eq]
      simp only [encFst, encSnd, List.length_append, List.length_cons, List.length_flatMap,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_nil]
      omega

end Cslib.Complexity.DenseSAT.Converter
end

-- CSLibExt.Computability.Complexity.CookLevin.OneHot
section
namespace Cslib.Complexity.CookLevin.OneHot
open Cslib.Complexity.CookLevin.Family
variable {L : Layout}
theorem kb_le {T H t k : ℕ} (ht : t ≤ T) (hk : k < L.KK) :
    k * (H * L.g) + (t * L.rowW H + L.A) ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h2 : k * (H * L.g) + H * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have h3 : (t + 1) * (L.A + L.KK * (H * L.g)) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at h3
  omega

theorem base_le {T H t k j : ℕ} (ht : t ≤ T) (hk : k < L.KK) (hj : j < H) :
    j * L.g + (k * (H * L.g) + (t * L.rowW H + L.A)) + L.g ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h1 : j * L.g + L.g ≤ H * L.g := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have h2 : k * (H * L.g) + H * L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  have h3 : (t + 1) * (L.A + L.KK * (H * L.g)) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at h3
  omega

theorem base_eq (H t k j : ℕ) :
    j * L.g + (k * (H * L.g) + (t * L.rowW H + L.A)) = L.cIdx H t k j 0 := by
  unfold Layout.cIdx; ring

end Cslib.Complexity.CookLevin.OneHot
end

-- CSLibExt.Computability.Complexity.DenseSATInNP
section
namespace Cslib.Complexity.DenseSAT

open MetaMathlibExt ComplexityTheory

open Classical in

noncomputable def denseSatDec : DecisionProblem := fun w => decide (SAT w)

theorem isPolyTime_check : IsPolyTime (fun p : List Bool × List Bool => check p.1 p.2) :=
  tm2ComputableInPolyTime_comp Converter.computable Verifier.verifier

theorem denseSatDec_mem_NP : denseSatDec ∈ NP :=
  ⟨Polynomial.X, fun p => check p.1 p.2, isPolyTime_check, fun w => by
    simpa [denseSatDec] using sat_iff_check w⟩

end Cslib.Complexity.DenseSAT
end

-- CSLibExt.Computability.Complexity.EncodingConverters
section
namespace Cslib.Complexity.DenseSAT

open Turing Function MetaMathlibExt Converter

namespace ToCanonical

inductive Stk | inp | out | fst | snd
  deriving DecidableEq

instance : Fintype Stk where
  elems := ⟨↑[Stk.inp, Stk.out, Stk.fst, Stk.snd], by decide⟩
  complete := fun k => by cases k <;> decide

abbrev Γ : Stk → Type
  | .inp => Verifier.G
  | _ => Bool

inductive Lab | readFst | readSnd | emitSnd | sep | emitFst
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.readFst, Lab.readSnd, Lab.emitSnd, Lab.sep, Lab.emitFst], by decide⟩
  complete := fun l => by cases l <;> decide

abbrev St := Option Verifier.G

def isFst : St → Bool
  | some (.inl _) => true
  | _ => false

def isSnd : St → Bool
  | some (.inr (some _)) => true
  | _ => false

def bit : St → Bool
  | some (.inl b) => b
  | some (.inr (some b)) => b
  | _ => false

def prog : Lab → TM2.Stmt Γ Lab St
  | .readFst =>
      .pop .inp (fun _ o => o) <| .branch isFst
        (.push .fst bit <| .goto fun _ => .readFst)
        (.goto fun _ => .readSnd)
  | .readSnd =>
      .pop .inp (fun _ o => o) <| .branch isSnd
        (.push .snd bit <| .goto fun _ => .readSnd)
        (.goto fun _ => .emitSnd)
  | .emitSnd =>
      .pop .snd (fun _ o => o.map Sum.inl) <| .branch isFst
        (.push .out (fun _ => false) <| .push .out bit <| .push .out (fun _ => true) <|
          .goto fun _ => .emitSnd)
        (.goto fun _ => .sep)
  | .sep => .push .out (fun _ => false) <| .goto fun _ => .emitFst
  | .emitFst =>
      .pop .fst (fun _ o => o.map Sum.inl) <| .branch isFst
        (.push .out (fun _ => false) <| .push .out (fun _ => true) <| .push .out bit <|
          .push .out (fun _ => true) <| .push .out (fun _ => true) <|
          .push .out (fun _ => true) <| .goto fun _ => .emitFst)
        .halt

def tm : FinTM2 where
  K := Stk
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := Lab
  main := .readFst
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Verifier.G)
  m := prog

def stk (i : List Verifier.G) (o a b : List Bool) : ∀ k, List (Γ k)
  | .inp => i
  | .out => o
  | .fst => a
  | .snd => b

@[simp] theorem update_stk_inp (i : List Verifier.G) (o a b : List Bool) (l : List Verifier.G) :
    update (stk i o a b) .inp l = stk l o a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_out (i : List Verifier.G) (o a b l : List Bool) :
    update (stk i o a b) .out l = stk i l a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_fst (i : List Verifier.G) (o a b l : List Bool) :
    update (stk i o a b) .fst l = stk i o l b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_snd (i : List Verifier.G) (o a b l : List Bool) :
    update (stk i o a b) .snd l = stk i o a l := by
  funext k; cases k <;> rfl

abbrev Run (n : ℕ) (c d : TM2.Cfg Γ Lab St) : Prop := TM2Program.Run prog n c d

theorem readFst_run (x : List Bool) :
    ∀ (rest : List Verifier.G) (o a b : List Bool) (v : St),
      Run (x.length + 1) ⟨some .readFst, v, stk (x.map Sum.inl ++ .inr none :: rest) o a b⟩
        ⟨some .readSnd, some (.inr none), stk rest o (x.reverse ++ a) b⟩ := by
  induction x with
  | nil =>
      intro rest o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isFst])
  | cons c x ih =>
      intro rest o a b v
      have h := ih rest o (c :: a) b (some (.inl c))
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isFst, bit]

theorem readSnd_run (w : List Bool) :
    ∀ (o a b : List Bool) (v : St),
      Run (w.length + 1)
        ⟨some .readSnd, v, stk (w.map fun c => .inr (some c)) o a b⟩
        ⟨some .emitSnd, none, stk [] o a (w.reverse ++ b)⟩ := by
  induction w with
  | nil =>
      intro o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isSnd])
  | cons c w ih =>
      intro o a b v
      have h := ih o a (c :: b) (some (.inr (some c)))
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isSnd, bit]

theorem emitSnd_run (b : List Bool) :
    ∀ (o a : List Bool) (v : St),
      Run (b.length + 1) ⟨some .emitSnd, v, stk [] o a b⟩
        ⟨some .sep, none, stk [] (encSnd b.reverse ++ o) a []⟩ := by
  induction b with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isFst, encSnd])
  | cons c b ih =>
      intro o a v
      have h := ih (true :: c :: false :: o) a (some (.inl c))
      simp only [List.reverse_cons, encSnd, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isFst, bit]

theorem sep_run (o a : List Bool) :
    Run 1 ⟨some .sep, none, stk [] o a []⟩ ⟨some .emitFst, none, stk [] (false :: o) a []⟩ :=
  TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])

theorem emitFst_run (a : List Bool) :
    ∀ (o : List Bool) (v : St),
      Run (a.length + 1) ⟨some .emitFst, v, stk [] o a []⟩
        ⟨none, none, stk [] (encFst a.reverse ++ o) [] []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isFst, encFst])
  | cons c a ih =>
      intro o v
      have h := ih (true :: true :: true :: c :: true :: false :: o) (some (.inl c))
      simp only [List.reverse_cons, encFst, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isFst, bit]

theorem convert_run (x w : List Bool) :
    Run (2 * x.length + 2 * w.length + 5)
      ⟨some .readFst, none, stk (Verifier.pairEncode (x, w)) [] [] []⟩
      ⟨none, none, stk [] (encFst x ++ false :: encSnd w) [] []⟩ := by
  have h₁ := readFst_run x (w.map fun c => .inr (some c)) [] [] [] none
  have h₂ := readSnd_run w [] (x.reverse ++ []) [] (some (.inr none))
  have h₃ := emitSnd_run (w.reverse ++ []) [] (x.reverse ++ []) none
  have h₄ := sep_run (encSnd (w.reverse ++ []).reverse ++ []) (x.reverse ++ [])
  have h₅ := emitFst_run (x.reverse ++ []) (false :: (encSnd (w.reverse ++ []).reverse ++ []))
    none
  have h := h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
  exact h.of_eq (by omega)

theorem initList_tm (l : List Verifier.G) :
    initList tm l = ⟨some .readFst, none, stk l [] [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Bool) : haltList tm l = ⟨none, none, stk [] l [] []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

noncomputable def computable :
    TM2ComputableInPolyTime Verifier.pairEncode
      (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode id where
  tm := tm
  inputAlphabet := Equiv.refl Verifier.G
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun := fun p => by
    obtain ⟨x, w⟩ := p
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2 * w.length + 5, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      erw [List.map_id, List.map_id, id, bitEncode_pair_eq, initList_tm, Option.map_some,
        haltList_tm]
      exact convert_run x w
    · simp only [Verifier.pairEncode, List.length_append, List.length_cons, List.length_map,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      omega

end ToCanonical

inductive BStk | inp | out | stash
  deriving DecidableEq

instance : Fintype BStk where
  elems := ⟨↑[BStk.inp, BStk.out, BStk.stash], by decide⟩
  complete := fun k => by cases k <;> decide

inductive BLab | read | emit
  deriving DecidableEq

instance : Fintype BLab where
  elems := ⟨↑[BLab.read, BLab.emit], by decide⟩
  complete := fun l => by cases l <;> decide

def bstk (i o a : List Bool) : BStk → List Bool
  | .inp => i
  | .out => o
  | .stash => a

@[simp] theorem update_bstk_inp (i o a l : List Bool) :
    update (bstk i o a) .inp l = bstk l o a := by
  funext k; cases k <;> rfl
@[simp] theorem update_bstk_out (i o a l : List Bool) :
    update (bstk i o a) .out l = bstk i l a := by
  funext k; cases k <;> rfl
@[simp] theorem update_bstk_stash (i o a l : List Bool) :
    update (bstk i o a) .stash l = bstk i o l := by
  funext k; cases k <;> rfl

namespace DecodeBits

def prog : BLab → TM2.Stmt (fun _ : BStk => Bool) BLab (Option Bool)
  | .read =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s == some true)
        (.pop .inp (fun _ o => o) <| .pop .inp (fun s _ => s) <|
          .push .stash (fun s => s.getD false) <| .goto fun _ => .read)
        (.goto fun _ => .emit)
  | .emit =>
      .pop .stash (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun s => s.getD false) <| .goto fun _ => .emit)
        .halt

def tm : FinTM2 where
  K := BStk
  k₀ := .inp
  k₁ := .out
  Γ := fun _ => Bool
  Λ := BLab
  main := .read
  σ := Option Bool
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog

abbrev Run (n : ℕ) (c d : TM2.Cfg (fun _ : BStk => Bool) BLab (Option Bool)) : Prop :=
  TM2Program.Run prog n c d

theorem read_run (x : List Bool) :
    ∀ (o a : List Bool) (v : Option Bool),
      Run (x.length + 1) ⟨some .read, v, bstk (encSnd x) o a⟩
        ⟨some .emit, none, bstk [] o (x.reverse ++ a)⟩ := by
  induction x with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk, encSnd])
  | cons c x ih =>
      intro o a v
      have h := ih o (c :: a) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk, encSnd]

theorem emit_run (a : List Bool) :
    ∀ (o : List Bool) (v : Option Bool),
      Run (a.length + 1) ⟨some .emit, v, bstk [] o a⟩ ⟨none, none,
          bstk [] (a.reverse ++ o) []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk])
  | cons c a ih =>
      intro o v
      have h := ih (c :: o) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk]

theorem initList_tm (l : List Bool) : initList tm l = ⟨some .read, none, bstk l [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Bool) : haltList tm l = ⟨none, none, bstk [] l []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

noncomputable def computable :
    TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := List Bool)).encode
      (fun l : List Bool => l) id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + Polynomial.C 2
  outputsFun := fun x => by
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      have h := (read_run x [] [] none).trans (emit_run (x.reverse ++ []) [] none)
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
      have hx : (BitstringEncoding.toEncoding (α := List Bool)).encode x = encSnd x :=
        bitEncode_list x
      erw [List.map_id, List.map_id, id, hx, initList_tm, Option.map_some, haltList_tm]
      exact h.of_eq (by omega)
    · change 2 * x.length + 2 ≤ (Polynomial.X + Polynomial.C 2).eval
        (BitstringEncoding.bitEncode x).length
      rw [bitEncode_list]
      simp only [encSnd, List.length_flatMap, List.length_cons, List.length_nil,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, List.map_const',
        List.sum_replicate, smul_eq_mul]
      omega

end DecodeBits

namespace EncodeBits

def prog : BLab → TM2.Stmt (fun _ : BStk => Bool) BLab (Option Bool)
  | .read =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .stash (fun s => s.getD false) <| .goto fun _ => .read)
        (.goto fun _ => .emit)
  | .emit =>
      .pop .stash (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun _ => false) <| .push .out (fun s => s.getD false) <|
          .push .out (fun _ => true) <| .goto fun _ => .emit)
        .halt

def tm : FinTM2 where
  K := BStk
  k₀ := .inp
  k₁ := .out
  Γ := fun _ => Bool
  Λ := BLab
  main := .read
  σ := Option Bool
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog

abbrev Run (n : ℕ) (c d : TM2.Cfg (fun _ : BStk => Bool) BLab (Option Bool)) : Prop :=
  TM2Program.Run prog n c d

theorem read_run (x : List Bool) :
    ∀ (o a : List Bool) (v : Option Bool),
      Run (x.length + 1) ⟨some .read, v, bstk x o a⟩ ⟨some .emit, none,
          bstk [] o (x.reverse ++ a)⟩ := by
  induction x with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk])
  | cons c x ih =>
      intro o a v
      have h := ih o (c :: a) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk]

theorem emit_run (a : List Bool) :
    ∀ (o : List Bool) (v : Option Bool),
      Run (a.length + 1) ⟨some .emit, v, bstk [] o a⟩
        ⟨none, none, bstk [] (encSnd a.reverse ++ o) []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk, encSnd])
  | cons c a ih =>
      intro o v
      have h := ih (true :: c :: false :: o) (some c)
      simp only [List.reverse_cons, encSnd, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk]

theorem initList_tm (l : List Bool) : initList tm l = ⟨some .read, none, bstk l [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Bool) : haltList tm l = ⟨none, none, bstk [] l []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

noncomputable def computable :
    TM2ComputableInPolyTime (fun l : List Bool => l)
      (BitstringEncoding.toEncoding (α := List Bool)).encode id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun := fun x => by
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      have h := (read_run x [] [] none).trans (emit_run (x.reverse ++ []) [] none)
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
      have hx : (BitstringEncoding.toEncoding (α := List Bool)).encode x = encSnd x :=
        bitEncode_list x
      erw [List.map_id, List.map_id, id, hx, initList_tm, Option.map_some, haltList_tm]
      exact h.of_eq (by omega)
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      omega

end EncodeBits

end Cslib.Complexity.DenseSAT
end

-- CSLibExt.Computability.Complexity.CookLevin.Shift
section
namespace Cslib.Complexity.CookLevin.Shift

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc Inc.le encodeClause_denseClause gapEnc_shift inc_of_mono denseClause cIdx_lt_next_row)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out update_st_c emitS emitOut incS
  drainS xferES copyS mulS mulS_run gapS bud_st stLoop)

theorem decS {C Λ : Type} [DecidableEq C] {M : Λ → TM2.Stmt (SΓ C) Λ Bool} {self ifZero ifPos : Λ}
    {x : C} (hp : M self = decr (.c x) ifZero ifPos) (F : C → ℕ) (n : ℕ) (hF : F x = n + 1)
    (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifPos, true, st (update F x n) o⟩ := by
  have := decr_run_cnt hp v (S := st F o) (u := ()) (n := n) (by simp [hF])
  rw [update_st_c] at this
  exact this

section Spec

variable (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ)

def shLits (H t i k u x : ℕ) : List (ℕ × Bool) :=
  [(L.cIdx H t k (u + cn i k) x, false), (L.xIdx H (t + 1) (sa i), false),
    (L.cIdx H (t + 1) k (u + pl i k) x, true)]

def ovLits (H t i k r : ℕ) : List (ℕ × Bool) :=
  [(L.xIdx H (t + 1) (sa i), false), (L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0, true)]

def pfLits (H t i k j : ℕ) : List (ℕ × Bool) :=
  [(L.xIdx H (t + 1) (sa i), false), (L.cIdx H (t + 1) k j (pu i k j), true)]

def shBlk (T H t i k : ℕ) : CNF :=
  ((List.range (H - max (pl i k) (cn i k))).flatMap fun u =>
      (List.range L.g).map fun x => denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x)) ++
    ((List.range (cn i k - pl i k)).map fun r =>
      denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r)) ++
    (List.range (pl i k)).map fun j => denseClause (L.numVars T H) (pfLits L sa pu H t i k j)

def shFamily (N T H : ℕ) : CNF :=
  (List.range T).flatMap fun t => (List.range N).flatMap fun i =>
    (List.range L.KK).flatMap fun k => shBlk L sa pl cn pu T H t i k

structure WF (N H : ℕ) : Prop where
  g_pos : 0 < L.g
  d_le : L.d ≤ H
  sa_lt : ∀ i < N, sa i < L.A
  pl_le : ∀ i < N, ∀ k < L.KK, pl i k ≤ L.d
  cn_le : ∀ i < N, ∀ k < L.KK, cn i k ≤ L.d
  pu_lt : ∀ i < N, ∀ k < L.KK, ∀ j < pl i k, pu i k j < L.g

theorem depth_cover {p c H : ℕ} (hp : p ≤ H) (hc : c ≤ H) (j : ℕ) (hj : j < H) :
    j < p ∨ (∃ u < H - max p c, j = u + p) ∨ (∃ r < c - p, j = H - c + p + r) := by
  by_cases h1 : j < p
  · exact Or.inl h1
  by_cases h2 : j < H - max p c + p
  · exact Or.inr (Or.inl ⟨j - p, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨j - (H - c + p), by omega, by omega⟩)

theorem depth_disjoint {p c H : ℕ} (hp : p ≤ H) (hc : c ≤ H) :
    (∀ u < H - max p c, p ≤ u + p ∧ u + p < H - c + p ∧ u + p < H) ∧
    (∀ r < c - p, H - max p c + p = H - c + p ∧ H - c + p + r < H) := by
  constructor <;> intro _ _ <;> omega

end Spec

inductive CK
  | Tn | Ti | Hs | Gc | HG | Wc | Vc | TW | TW1 | KB | U | Ui | R | Ri | CB | CW | P | Q | tmp | md | Ka
  | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Ti, CK.Hs, CK.Gc, CK.HG, CK.Wc, CK.Vc, CK.TW, CK.TW1, CK.KB, CK.U, CK.Ui,
      CK.R, CK.Ri, CK.CB, CK.CW, CK.P, CK.Q, CK.tmp, CK.md, CK.Ka, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

inductive BS | s | cb | cw
  deriving DecidableEq
instance BS.instFintypeEnumFix : Fintype BS where
  elems := ⟨↑[BS.s, BS.cb, BS.cw], by decide⟩
  complete := fun x => by cases x <;> decide

def BS.k : BS → CK
  | .s => .TW1
  | .cb => .CB
  | .cw => .CW

inductive CL (g d : ℕ)
  | sh (x : Fin g)
  | ov
  | pf (j : Fin d)
  deriving DecidableEq, Fintype

namespace CL

variable {g d : ℕ}

def nl : CL g d → ℕ
  | sh _ => 3
  | ov => 2
  | pf _ => 2

def bs : CL g d → ℕ → BS
  | sh _, l => if l = 0 then .cb else if l = 1 then .s else .cw
  | ov, l => if l = 0 then .s else .cw
  | pf _, l => if l = 0 then .s else .cw

def cs (s p c : ℕ) (q : ℕ → ℕ) : CL g d → ℕ → ℕ
  | sh x, l => if l = 0 then c * g + x else if l = 1 then s else p * g + x
  | ov, l => if l = 0 then s else p * g
  | pf j, l => if l = 0 then s else j.val * g + q j.val

def sg (cl : CL g d) (l : ℕ) : Bool := decide (l + 1 = cl.nl)

theorem nl_le (cl : CL g d) : cl.nl ≤ 3 := by cases cl <;> simp [nl]

end CL

inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | dk | v (s : MS) | vw1 | vw2
  deriving DecidableEq, Fintype

inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

inductive ST
  | kbE | kbC1 | kbC2 | kbK | kbM (s : MS) | kbD | uC1 | uC2
  | oE | oHead | oRest | oC1 | oC2 | oR1 | oR2 | oM (s : MS) | oD
  | sHead | sRest | dU | dR | dKB
  | fC1 | fC2 | fW1 | fW2 | fD1
  deriving DecidableEq, Fintype

inductive BD (g d : ℕ)
  | bC1 (b : Bool) | bC2 (b : Bool) | sM (s : MS)
  | w1 (b : Bool) | w2 (b : Bool) | w3 (b : Bool) | w4 (b : Bool)
  | e00 (c : CL g d) | cv1 (c : CL g d) | cv2 (c : CL g d) | lit (c : CL g d) (l : Fin 3) (s : LS)
  | fin (c : CL g d)
  | dCB (b : Bool) | dCW (b : Bool)
  deriving DecidableEq, Fintype

inductive GeneratorLabel (N KK g d : ℕ)
  | pre (s : PS)
  | tHead | tRest | tw (s : MS) | t1a | t1b | t1c | t1d | tEnd | tEnd2
  | s (i : Fin N) (k : Fin KK) (x : ST)
  | sb (i : Fin N) (k : Fin KK) (r : Fin (d + 1))
  | b (i : Fin N) (k : Fin KK) (x : BD g d)
  | bad | done
  deriving DecidableEq, Fintype

namespace GeneratorLabel

variable {N KK g d : ℕ}

def litL (i : Fin N) (k : Fin KK) (c : CL g d) (l : ℕ) : GeneratorLabel N KK g d :=
  if h : l < 3 then .b i k (.lit c ⟨l, h⟩ .cp1) else .done

def after (i : Fin N) (k : Fin KK) (c : CL g d) (l : ℕ) : GeneratorLabel N KK g d :=
  if l = 0 then .b i k (.fin c) else litL i k c (l - 1)

def xFrom (i : Fin N) (k : Fin KK) (n : ℕ) : GeneratorLabel N KK g d :=
  if n = 0 then .b i k (.dCB true) else if h : n - 1 < g then .b i k (.e00 (.sh ⟨n - 1, h⟩))
  else .done

def pfFrom (i : Fin N) (k : Fin KK) (n : ℕ) : GeneratorLabel N KK g d :=
  if n = 0 then .s i k .fD1 else if h : n - 1 < d then .b i k (.e00 (.pf ⟨n - 1, h⟩)) else .done

def nextC (i : Fin N) (k : Fin KK) : CL g d → GeneratorLabel N KK g d
  | .sh x => xFrom i k x.val
  | .ov => .b i k (.dCB false)
  | .pf j => pfFrom i k j.val

def sbL (i : Fin N) (k : Fin KK) (n : ℕ) : GeneratorLabel N KK g d :=
  if n = 0 then .s i k .fC1 else if h : n - 1 < d + 1 then .sb i k ⟨n - 1, h⟩ else .done

def iFrom (n : ℕ) : GeneratorLabel N KK g d :=
  if n = 0 then .tEnd
  else if h : n - 1 < N ∧ 0 < KK then .s ⟨n - 1, h.1⟩ ⟨KK - 1, by omega⟩ .kbE
  else if KK = 0 then .tEnd else .done

def ik (i n : ℕ) : GeneratorLabel N KK g d :=
  if n = 0 then iFrom i else if h : i < N ∧ n - 1 < KK then .s ⟨i, h.1⟩ ⟨n - 1, h.2⟩ .kbE
  else .done

theorem litL_of_lt {i : Fin N} {k : Fin KK} {c : CL g d} {l : ℕ} (h : l < 3) :
    (litL i k c l : GeneratorLabel N KK g d) = .b i k (.lit c ⟨l, h⟩ .cp1) := dif_pos h

theorem xFrom_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < g) :
    (xFrom i k (n + 1) : GeneratorLabel N KK g d) = .b i k (.e00 (.sh ⟨n, h⟩)) := by
  simp [xFrom, h]

theorem pfFrom_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < d) :
    (pfFrom i k (n + 1) : GeneratorLabel N KK g d) = .b i k (.e00 (.pf ⟨n, h⟩)) := by
  simp [pfFrom, h]

theorem sbL_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < d + 1) :
    (sbL i k (n + 1) : GeneratorLabel N KK g d) = .sb i k ⟨n, h⟩ := by
  simp [sbL, h]

theorem ik_succ {i n : ℕ} (hi : i < N) (hn : n < KK) :
    (ik i (n + 1) : GeneratorLabel N KK g d) = .s ⟨i, hi⟩ ⟨n, hn⟩ .kbE := by
  simp [ik, hi, hn]

theorem iFrom_succ {n : ℕ} (hn : n < N) (hK : 0 < KK) :
    (iFrom (n + 1) : GeneratorLabel N KK g d) = ik n KK := by
  have h1 : KK - 1 < KK := by omega
  simp [iFrom, ik, hn, hK, h1, hK.ne']

theorem iFrom_KK0 (hK : KK = 0) (n : ℕ) : (iFrom n : GeneratorLabel N KK g d) = .tEnd := by
  unfold iFrom; split_ifs <;> first | rfl | omega

end GeneratorLabel

section Machine

variable (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (N : ℕ)

abbrev Lab := GeneratorLabel N L.KK L.g L.d

def csv (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : ℕ) : ℕ :=
  c.cs (sa i) (pl i k) (cn i k) (pu i k) l

def litP (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : Fin 3) :
    LS → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .cp1 => xfer (.c (c.bs l).k) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.lit c l .cp1))
      (.b i k (.lit c l .cp2))
  | .cp2 => xfer (.c .tmp) [⟨.c (c.bs l).k, ()⟩] (.b i k (.lit c l .cp2)) (.b i k (.lit c l .eo))
  | .eo => emitR (.c .Q) (List.replicate (csv L sa pl cn pu N i k c l) ()) (.b i k (.lit c l .dec))
  | .dec => decr (.c .P) (.b i k (.lit c l .bad)) (.b i k (.lit c l .cmp))
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.b i k (.lit c l .cmp))
      (.b i k (.lit c l (.r .lt))) (.b i k (.lit c l (.r .eq))) (.b i k (.lit c l (.r .gt)))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.b i k (.lit c l (.r o))) (.b i k (.lit c l (.rB o)))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.b i k (.lit c l (.rB o)))
      (if o = .eq then .b i k (.lit c l .slot) else .b i k (.lit c l .emL))
  | .emL => emitR .out [false, true] (.b i k (.lit c l .dec))
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg l))) (.b i k (.lit c l .dq))
  | .dq => xfer (.c .Q) [] (.b i k (.lit c l .dq)) (GeneratorLabel.after i k c l)

def stP (i : Fin N) (k : Fin L.KK) : ST → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .kbE => emitR (.c .KB) (List.replicate L.A ()) (.s i k .kbC1)
  | .kbC1 => xfer (.c .TW) [⟨.c .KB, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .kbC1) (.s i k .kbC2)
  | .kbC2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.s i k .kbC2) (.s i k .kbK)
  | .kbK => emitR (.c .Ka) (List.replicate k.val ()) (.s i k (.kbM .head))
  | .kbM s => mulS .Ka .md .HG .KB .tmp (fun s => .s i k (.kbM s)) (.s i k .kbD) s
  | .kbD => xfer (.c .Ka) [] (.s i k .kbD) (.s i k .uC1)
  | .uC1 => xfer (.c .Hs) [⟨.c .U, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .uC1) (.s i k .uC2)
  | .uC2 => xfer (.c .tmp) [⟨.c .Hs, ()⟩] (.s i k .uC2) (GeneratorLabel.sbL i k (max (pl i k) (cn i k)))
  | .oE => emitR (.c .R) (List.replicate (cn i k - pl i k) ()) (.s i k .oHead)

  | .oHead => forHead (.c .R) (.c .Ri) () (.s i k .oC1) (.s i k .oRest)
  | .oRest => xfer (.c .Ri) [⟨.c .R, ()⟩] (.s i k .oRest) (.s i k .sHead)
  | .oC1 => xfer (.c .U) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .oC1) (.s i k .oC2)
  | .oC2 => xfer (.c .tmp) [⟨.c .U, ()⟩] (.s i k .oC2) (.s i k .oR1)
  | .oR1 => xfer (.c .R) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .oR1) (.s i k .oR2)
  | .oR2 => xfer (.c .tmp) [⟨.c .R, ()⟩] (.s i k .oR2) (.s i k (.oM .head))
  | .oM s => mulS .Ka .md .Gc .CB .tmp (fun s => .s i k (.oM s)) (.s i k .oD) s
  | .oD => xfer (.c .Ka) [] (.s i k .oD) (.b i k (.bC1 false))

  | .sHead => forHead (.c .U) (.c .Ui) () (.b i k (.bC1 true)) (.s i k .sRest)
  | .sRest => xfer (.c .Ui) [⟨.c .U, ()⟩] (.s i k .sRest) (.s i k .dU)
  | .dU => xfer (.c .U) [] (.s i k .dU) (.s i k .dR)
  | .dR => xfer (.c .R) [] (.s i k .dR) (.s i k .dKB)
  | .dKB => xfer (.c .KB) [] (.s i k .dKB) (GeneratorLabel.ik i.val k.val)

  | .fC1 => xfer (.c .KB) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .fC1) (.s i k .fC2)
  | .fC2 => xfer (.c .tmp) [⟨.c .KB, ()⟩] (.s i k .fC2) (.s i k .fW1)
  | .fW1 => xfer (.c .Wc) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .fW1) (.s i k .fW2)
  | .fW2 => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.s i k .fW2) (GeneratorLabel.pfFrom i k (pl i k))
  | .fD1 => xfer (.c .CW) [] (.s i k .fD1) (.s i k .oE)

def bdP (i : Fin N) (k : Fin L.KK) : BD L.g L.d → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .bC1 b => xfer (.c .KB) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.bC1 b)) (.b i k (.bC2 b))
  | .bC2 b => xfer (.c .tmp) [⟨.c .KB, ()⟩] (.b i k (.bC2 b))
      (if b then .b i k (.sM .head) else .b i k (.w1 b))
  | .sM s => mulS .U .md .Gc .CB .tmp (fun s => .b i k (.sM s)) (.b i k (.w1 true)) s
  | .w1 b => xfer (.c .CB) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.w1 b)) (.b i k (.w2 b))
  | .w2 b => xfer (.c .tmp) [⟨.c .CB, ()⟩] (.b i k (.w2 b)) (.b i k (.w3 b))
  | .w3 b => xfer (.c .Wc) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.w3 b)) (.b i k (.w4 b))
  | .w4 b => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.b i k (.w4 b))
      (if b then GeneratorLabel.xFrom i k L.g else .b i k (.e00 .ov))
  | .e00 c => emitR .out [false, false] (.b i k (.cv1 c))
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.cv1 c)) (.b i k (.cv2 c))
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.b i k (.cv2 c)) (GeneratorLabel.after i k c c.nl)
  | .lit c l s => litP L sa pl cn pu N i k c l s
  | .fin c => xferE (.c .P) .out [false, true] (.b i k (.fin c)) (GeneratorLabel.nextC i k c)
  | .dCB b => xfer (.c .CB) [] (.b i k (.dCB b)) (.b i k (.dCW b))
  | .dCW b => xfer (.c .CW) [] (.b i k (.dCW b)) (if b then .s i k .sHead else .s i k .oHead)

def prog : Lab L N → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Ka) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Ka .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre .dk) s
  | .pre .dk => xfer (.c .Ka) [] (.pre .dk) (.pre (.v .head))
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .vw1) s
  | .pre .vw1 => xfer (.c .Wc) [⟨.c .Vc, ()⟩, ⟨.c .tmp, ()⟩] (.pre .vw1) (.pre .vw2)
  | .pre .vw2 => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.pre .vw2) .tHead
  | .tHead => forHead (.c .Tn) (.c .Ti) () (.tw .head) .tRest
  | .tRest => xfer (.c .Ti) [⟨.c .Tn, ()⟩] .tRest .done
  | .tw s => mulS .Tn .md .Wc .TW .tmp .tw .t1a s
  | .t1a => xfer (.c .TW) [⟨.c .TW1, ()⟩, ⟨.c .tmp, ()⟩] .t1a .t1b
  | .t1b => xfer (.c .tmp) [⟨.c .TW, ()⟩] .t1b .t1c
  | .t1c => xfer (.c .Wc) [⟨.c .TW1, ()⟩, ⟨.c .tmp, ()⟩] .t1c .t1d
  | .t1d => xfer (.c .tmp) [⟨.c .Wc, ()⟩] .t1d (GeneratorLabel.iFrom N)
  | .tEnd => xfer (.c .TW) [] .tEnd .tEnd2
  | .tEnd2 => xfer (.c .TW1) [] .tEnd2 .tHead
  | .s i k x => stP L pl cn N i k x
  | .sb i k r => decr (.c .U) .bad (GeneratorLabel.sbL i k r.val)
  | .b i k x => bdP L sa pl cn pu N i k x
  | .bad => .halt
  | .done => .halt

def shTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := Lab L N
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L sa pl cn pu N

end Machine

section Lits

variable {g d : ℕ}

theorem BS.k_ne (b : BS) : b.k ≠ .Q ∧ b.k ≠ .tmp ∧ b.k ≠ .P ∧ b.k ≠ .c1 ∧ b.k ≠ .c2 ∧ b.k ≠ .md :=
  by cases b <;> decide

def clits (pos : ℕ → ℕ) (cl : CL g d) : List (ℕ × Bool) :=
  (List.range cl.nl).map fun l => (pos l, cl.sg l)

structure Mono (pos : ℕ → ℕ) (n V : ℕ) : Prop where
  mono : ∀ l, l + 1 < n → pos l < pos (l + 1)
  last : ∀ l, l + 1 = n → pos l < V

theorem clits_drop (pos : ℕ → ℕ) (cl : CL g d) (l : ℕ) :
    (clits pos cl).drop l = (List.range' l (cl.nl - l)).map fun l => (pos l, cl.sg l) := by
  rw [clits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

def bnd (V : ℕ) (pos : ℕ → ℕ) (n l : ℕ) : ℕ := if l < n then pos l else V

theorem inc_drop {V : ℕ} {pos : ℕ → ℕ} {cl : CL g d} (h : Mono pos cl.nl V) (l : ℕ)
    (hl : l ≤ cl.nl) : Inc (bnd V pos cl.nl l) ((clits pos cl).drop l) V := by
  rw [clits_drop]
  refine inc_of_mono _ cl.nl V (fun j hj => h.mono j hj) (fun j hj => h.last j hj) (cl.nl - l) l _
    (by omega) (fun hn => ?_) (fun _ => ?_)
  · simp only [bnd]; split_ifs with h'
    · omega
    · exact le_rfl
  · simp only [bnd, if_pos (show l < cl.nl by omega)]; exact le_rfl

theorem bnd_le {V : ℕ} {pos : ℕ → ℕ} {cl : CL g d} (h : Mono pos cl.nl V) {l : ℕ} (hl : l ≤ cl.nl) :
    bnd V pos cl.nl l ≤ V := (inc_drop h l hl).le

theorem bnd_lt {V : ℕ} {pos : ℕ → ℕ} {n l : ℕ} (h : Mono pos n V) (hl : l < n) :
    pos l < bnd V pos n (l + 1) := by
  unfold bnd
  split_ifs with h'
  · exact h.mono l h'
  · exact h.last l (by omega)

end Lits

section Clause

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem Rest.upd {F : CK → ℕ} (h : Rest F) {x : CK} (hQ : x ≠ .Q) (ht : x ≠ .tmp) (hm : x ≠ .md)
    (h1 : x ≠ .c1) (h2 : x ≠ .c2) (n : ℕ) : Rest (update F x n) :=
  ⟨by rw [update_of_ne hQ.symm, h.Q], by rw [update_of_ne ht.symm, h.tmp],
    by rw [update_of_ne hm.symm, h.md], by rw [update_of_ne h1.symm, h.c1],
    by rw [update_of_ne h2.symm, h.c2]⟩

theorem lit_run (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : Fin 3) (F : CK → ℕ) (hF : Rest F)
    (q gap : ℕ) (hq : q = F (c.bs l).k + csv L sa pl cn pu N i k c l) (hp : F .P = q + gap + 1)
    (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (gap * (3 * q + 6) + 2 * F (c.bs l).k + 4 * q + 9)
      ⟨some (.b i k (.lit c l .cp1)), v, st F o⟩
      ⟨some (GeneratorLabel.after i k c l), false,
        st (update F .P q) (encodeSlot (some (c.sg l)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨n1, n2, n3, -, -, -⟩ := BS.k_ne (c.bs l)
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.lit c l .cp1))
    (l₂ := .b i k (.lit c l .cp2)) (next := .b i k (.lit c l .eo)) rfl rfl n1 n2 (by decide) F
    htmp v o).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .eo))
    (next := .b i k (.lit c l .dec)) rfl _ _ _).bud ?_
  refine (gapS (M := prog L sa pl cn pu N) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true]) (dec := .b i k (.lit c l .dec)) (cmpL := .b i k (.lit c l .cmp))
    (emitL := .b i k (.lit c l .emL)) (ifZero := .b i k (.lit c l .bad))
    (next := .b i k (.lit c l .slot)) (r := fun o => .b i k (.lit c l (.r o)))
    (rB := fun o => .b i k (.lit c l (.rB o)))
    (out := fun o => if o = .eq then .b i k (.lit c l .slot) else .b i k (.lit c l .emL))
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .slot))
    (next := .b i k (.lit c l .dq)) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .dq)) (next := GeneratorLabel.after i k c l)
    (x := .Q) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

def litE (V : ℕ) : ℕ := 6 * V + 9

def clauseB (V : ℕ) : ℕ := V * (3 * V + 6) + 3 * litE V + 3 * V + 4

theorem lits_run {V : ℕ} (i : Fin N) (k : Fin L.KK) {c : CL L.g L.d} (pos : ℕ → ℕ) (F : CK → ℕ)
    (hF : Rest F) (hpos : ∀ l, pos l = F (c.bs l).k + csv L sa pl cn pu N i k c l)
    (hbase : ∀ l, F (c.bs l).k ≤ V) (hM : Mono pos c.nl V) (o : List Bool) :
    ∀ l, l ≤ c.nl → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (bnd V pos c.nl l * (3 * V + 6) + l * litE V)
        ⟨some (GeneratorLabel.after i k c l), v,
          st (update F .P (bnd V pos c.nl l)) (gapEnc (bnd V pos c.nl l) ((clits pos c).drop l) V ++
            [false, false] ++ o)⟩
        ⟨some (.b i k (.fin c)), v',
          st (update F .P (bnd V pos c.nl 0)) (gapEnc (bnd V pos c.nl 0) (clits pos c) V ++
            [false, false] ++ o)⟩ := by
  intro l
  induction l with
  | zero => intro _ v; exact ⟨v, by simpa [GeneratorLabel.after] using RunLe.refl _ _⟩
  | succ l ih =>
      intro hl v
      have hlm : l < c.nl := by omega
      have hl3 : l < 3 := lt_of_lt_of_le hlm c.nl_le
      set p := pos l with hp
      set b := bnd V pos c.nl (l + 1) with hb
      have hpb : p < b := bnd_lt hM hlm
      obtain ⟨-, -, nP, -, -, -⟩ := BS.k_ne (c.bs l)
      have r := lit_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) i k c ⟨l, hl3⟩ (update F .P b)
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) b) p (b - p - 1)
        (by simp [hp, hpos, update_of_ne nP]) (by simp; omega)
        (gapEnc b ((clits pos c).drop (l + 1)) V ++ [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GeneratorLabel.after, if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel, GeneratorLabel.litL_of_lt hl3]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbl : bnd V pos c.nl l = p := by simp [bnd, hlm, hp]
      have hdrop : (clits pos c).drop l = (p, c.sg l) :: (clits pos c).drop (l + 1) := by
        rw [clits_drop, clits_drop, show c.nl - l = (c.nl - (l + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
      have hshift := gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop hM (l + 1) hl)
      rw [hbl, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      have hbV := bnd_le hM hl
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * V + 6 by omega)
      have h2 : (b - p - 1) * (3 * V + 6) + p * (3 * V + 6) ≤ b * (3 * V + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      have h3 := hbase l
      simp only [update_of_ne nP]
      rw [Nat.add_one_mul l]
      unfold litE
      omega

theorem clause_run {V : ℕ} (i : Fin N) (k : Fin L.KK) {c : CL L.g L.d} (pos : ℕ → ℕ) (F : CK → ℕ)
    (hF : Rest F) (hpos : ∀ l, pos l = F (c.bs l).k + csv L sa pl cn pu N i k c l)
    (hbase : ∀ l, F (c.bs l).k ≤ V) (hM : Mono pos c.nl V) (hV : F .Vc = V) (hP : F .P = 0)
    (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (clauseB V) ⟨some (.b i k (.e00 c)), v, st F o⟩
      ⟨some (GeneratorLabel.nextC i k c), false, st F (encodeClause (denseClause V (clits pos c)) ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := prog L sa pl cn pu N) (self := .b i k (.e00 c)) (next := .b i k (.cv1 c)) rfl
    _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.cv1 c)) (l₂ := .b i k (.cv2 c))
    (next := GeneratorLabel.after i k c c.nl) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  obtain ⟨v', r⟩ := lits_run i k pos F hF hpos hbase hM o c.nl le_rfl false
  have hbm : bnd V pos c.nl c.nl = V := by simp [bnd]
  rw [hbm, List.drop_eq_nil_of_le (by simp [clits]), gapEnc, Nat.sub_self, rep_zero,
    List.nil_append] at r
  rw [hV, hP, Nat.add_zero]
  refine r.bud ?_
  refine (xferES (M := prog L sa pl cn pu N) (self := .b i k (.fin c)) (next := GeneratorLabel.nextC i k c)
    (x := .P) rfl _ _ _).bud ?_
  have e1 : update (update F .P (bnd V pos c.nl 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop hM 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause V (clits pos c)) =
      rep [false, true] (bnd V pos c.nl 0) ++ gapEnc (bnd V pos c.nl 0) (clits pos c) V ++
        [false, false] := by
    rw [encodeClause_denseClause (Family.Inc.mono_lo (Nat.zero_le _) h0),
      gapEnc_shift (Nat.zero_le _) h0, Nat.sub_zero]
  simp only [update_self]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le hM (l := 0) (Nat.zero_le _)
  have := Nat.mul_le_mul_right (litE V) c.nl_le
  unfold clauseB
  omega

end Clause

section Cells

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

def kbv (L : Layout) (H t k : ℕ) : ℕ := k * (H * L.g) + (t * L.rowW H + L.A)

def shPos (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (H t i k u x l : ℕ) : ℕ :=
  if l = 0 then L.cIdx H t k (u + cn i k) x else if l = 1 then L.xIdx H (t + 1) (sa i)
  else L.cIdx H (t + 1) k (u + pl i k) x

def ovPos (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (H t i k r l : ℕ) : ℕ :=
  if l = 0 then L.xIdx H (t + 1) (sa i) else L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0

theorem rowW_le {T H t : ℕ} (ht : t < T) : (t + 1) * L.rowW H + L.rowW H ≤ L.numVars T H := by
  unfold Layout.numVars
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)

theorem cw_le {T H t k j : ℕ} (ht : t < T) (hk : k < L.KK) (hj : j < H) :
    j * L.g + kbv L H t k + L.rowW H ≤ L.numVars T H := by
  have := Cslib.Complexity.CookLevin.OneHot.base_le (L := L) (T := T) (H := H) (t := t + 1) (k := k) (j := j) ht hk hj
  unfold kbv; rw [Nat.succ_mul] at this; omega

theorem kbw_le {T H t k : ℕ} (ht : t < T) (hk : k < L.KK) :
    kbv L H t k + L.rowW H ≤ L.numVars T H := by
  have h1 := rowW_le (L := L) (H := H) ht
  have h2 := Nat.mul_le_mul_right (H * L.g) hk.le
  have h3 : (t + 1) * L.rowW H = t * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have h4 : L.rowW H = L.A + L.KK * (H * L.g) := rfl
  unfold kbv; omega

theorem shPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u x : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (hx : x < L.g) :
    Mono (shPos L sa pl cn H t i k u x) 3 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have h1 := cIdx_lt_next_row (L := L) (t := t) k.2 (show u + cn i k < H by omega) hx
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2 (show u + pl i k < H by omega) hx
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : shPos L sa pl cn H t i k u x 0 = L.cIdx H t k (u + cn i k) x := rfl
  have e1 : shPos L sa pl cn H t i k u x 1 = (t + 1) * L.rowW H + sa i := rfl
  have e2 : shPos L sa pl cn H t i k u x 2 = L.cIdx H (t + 1) k (u + pl i k) x := rfl
  have e2' : L.cIdx H (t + 1) k (u + pl i k) x =
      (t + 1) * L.rowW H + L.A + (k * H + (u + pl i k)) * L.g + x := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
    · rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
    · rw [e1, show 1 + 1 = 2 from rfl, e2]; omega
  · obtain rfl : l = 2 := by omega
    rw [e2]; omega

theorem ovPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {r : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hr : r < cn i k - pl i k) :
    Mono (ovPos L sa pl cn H t i k r) 2 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2
    (show H - cn i k + pl i k + r < H by omega) hwf.g_pos
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have h5 : (t + 1) * L.rowW H = t * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : ovPos L sa pl cn H t i k r 0 = (t + 1) * L.rowW H + sa i := rfl
  have e1 : ovPos L sa pl cn H t i k r 1 = L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0 := rfl
  have e1' : L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0 =
      (t + 1) * L.rowW H + L.A + (k * H + (H - cn i k + pl i k + r)) * L.g + 0 := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl : l = 0 := by omega
    rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
  · obtain rfl : l = 1 := by omega
    rw [e1]; omega

theorem clits_sh (H t : ℕ) (i : Fin N) (k : Fin L.KK) (u x : ℕ) (hx : x < L.g) :
    clits (shPos L sa pl cn H t i k u x) (.sh ⟨x,
        hx⟩ : CL L.g L.d) = shLits L sa pl cn H t i k u x := by
  simp [clits, CL.nl, CL.sg, shPos, shLits, List.range_succ]

theorem clits_ov (H t : ℕ) (i : Fin N) (k : Fin L.KK) (r : ℕ) :
    clits (ovPos L sa pl cn H t i k r) (.ov : CL L.g L.d) = ovLits L sa pl cn H t i k r := by
  simp [clits, CL.nl, CL.sg, ovPos, ovLits, List.range_succ]

def pfPos (L : Layout) (sa : ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (H t i k j l : ℕ) : ℕ :=
  if l = 0 then L.xIdx H (t + 1) (sa i) else L.cIdx H (t + 1) k j (pu i k j)

theorem pfPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {j : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hj : j < pl i k) :
    Mono (pfPos L sa pu H t i k j) 2 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have hp := hwf.pl_le i i.2 k k.2
  have hd := hwf.d_le
  have hx := hwf.pu_lt i i.2 k k.2 j hj
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2 (show j < H by omega) hx
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : pfPos L sa pu H t i k j 0 = (t + 1) * L.rowW H + sa i := rfl
  have e1 : pfPos L sa pu H t i k j 1 = L.cIdx H (t + 1) k j (pu i k j) := rfl
  have e1' : L.cIdx H (t + 1) k j (pu i k j) =
      (t + 1) * L.rowW H + L.A + (k * H + j) * L.g + pu i k j := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl : l = 0 := by omega
    rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
  · obtain rfl : l = 1 := by omega
    rw [e1]; omega

theorem clits_pf (H t : ℕ) (i : Fin N) (k : Fin L.KK) (j : ℕ) (hj : j < L.d) :
    clits (pfPos L sa pu H t i k j) (.pf ⟨j, hj⟩ : CL L.g L.d) = pfLits L sa pu H t i k j := by
  simp [clits, CL.nl, CL.sg, pfPos, pfLits, List.range_succ]

structure Body (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Rest F where
  P : F .P = 0
  Vc : F .Vc = L.numVars T H
  Gc : F .Gc = L.g
  Wc : F .Wc = L.rowW H
  TW : F .TW = t * L.rowW H
  TW1 : F .TW1 = (t + 1) * L.rowW H

theorem xs_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (F : CK → ℕ)
    (hF : Body L T H t F) (hCB : F .CB = u * L.g + kbv L H t k)
    (hCW : F .CW = u * L.g + kbv L H t k + L.rowW H) :
    ∀ n, n ≤ L.g → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * clauseB (L.numVars T H)) ⟨some (GeneratorLabel.xFrom i k n), v, st F o⟩
        ⟨some (.b i k (.dCB true)), v', st F ((List.range n).flatMap (fun x =>
          encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GeneratorLabel.xFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have hng : n < L.g := by omega
      have hV := cw_le (L := L) (T := T) ht k.2 (show u < H by omega)
      have r := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k
        (c := .sh ⟨n, hng⟩) (shPos L sa pl cn H t i k u n) F hF.toRest
        (fun l => by
          simp only [shPos, CL.bs, csv, CL.cs]
          split_ifs <;> simp only [BS.k, hF.TW1, hCB, hCW, kbv, Layout.xIdx, Layout.cIdx] <;> ring)
        (fun l => by
          have := rowW_le (L := L) (H := H) ht
          simp only [CL.bs]; split_ifs <;> simp only [BS.k, hF.TW1, hCB, hCW] <;> omega)
        (shPos_mono ht hwf hu hng) hF.Vc hF.P o v
      rw [show GeneratorLabel.nextC i k (CL.sh ⟨n, hng⟩) = GeneratorLabel.xFrom i k n from rfl, clits_sh] at r
      rw [GeneratorLabel.xFrom_succ hng]
      obtain ⟨v', r'⟩ := ih (by omega) _ false
      refine ⟨v', Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))⟩
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem pf_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (F : CK → ℕ) (hF : Body L T H t F)
    (hCW : F .CW = kbv L H t k + L.rowW H) :
    ∀ n, n ≤ pl i k → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * clauseB (L.numVars T H))
        ⟨some (GeneratorLabel.pfFrom i k n), v, st F o⟩
        ⟨some (.s i k .fD1), v', st F ((List.range n).flatMap (fun j =>
          encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GeneratorLabel.pfFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have hnd : n < L.d := by have := hwf.pl_le i i.2 k k.2; omega
      have r := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k
        (c := .pf ⟨n, hnd⟩) (pfPos L sa pu H t i k n) F hF.toRest
        (fun l => by
          simp only [pfPos, CL.bs, csv, CL.cs]
          split_ifs
          · simp only [BS.k, hF.TW1, Layout.xIdx]
          · simp only [BS.k, hCW, kbv, Layout.cIdx]; ring)
        (fun l => by
          have := rowW_le (L := L) (H := H) ht
          have := kbw_le (L := L) (H := H) ht k.2
          simp only [CL.bs]; split_ifs <;> simp only [BS.k, hF.TW1, hCW] <;> omega)
        (pfPos_mono ht hwf (by omega)) hF.Vc hF.P o v
      rw [show GeneratorLabel.nextC i k (CL.pf ⟨n, hnd⟩ : CL L.g L.d) = GeneratorLabel.pfFrom i k n from rfl,
        clits_pf] at r
      rw [GeneratorLabel.pfFrom_succ hnd]
      obtain ⟨v', r'⟩ := ih (by omega) _ false
      refine ⟨v', Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))⟩
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem sb_run (i : Fin N) (k : Fin L.KK) :
    ∀ n, n ≤ L.d + 1 → ∀ (F : CK → ℕ) (h : ℕ), F .U = h + n → ∀ (v : Bool) (o : List Bool),
      ∃ v' : Bool, Run (prog L sa pl cn pu N) n ⟨some (GeneratorLabel.sbL i k n), v, st F o⟩
        ⟨some (.s i k .fC1), v', st (update F .U h) o⟩ := by
  intro n
  induction n with
  | zero =>
      intro _ F h hF v o
      refine ⟨v, ?_⟩
      rw [show update F .U h = F by rw [update_eq_self_iff]; omega]
      exact Run.zero _
  | succ n ih =>
      intro hn F h hF v o
      have r := decS (M := prog L sa pl cn pu N) (self := .sb i k ⟨n, by omega⟩)
        (ifZero := .bad) (ifPos := GeneratorLabel.sbL i k n) (x := .U) rfl F (h + n) (by omega) v o
      obtain ⟨v', r'⟩ := ih (by omega) (update F .U (h + n)) h (by simp) true o
      rw [update_idem] at r'
      refine ⟨v', ?_⟩
      rw [GeneratorLabel.sbL_succ (by omega), show n + 1 = 1 + n by omega]
      exact r.trans r'

end Cells

section Bodies

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

theorem Body.upd {T H t : ℕ} {F : CK → ℕ} (h : Body L T H t F) {x : CK}
    (hx : x ≠ .Q ∧ x ≠ .tmp ∧ x ≠ .md ∧ x ≠ .c1 ∧ x ≠ .c2 ∧ x ≠ .P ∧ x ≠ .Vc ∧ x ≠ .Gc ∧
      x ≠ .Wc ∧ x ≠ .TW ∧ x ≠ .TW1) (n : ℕ) : Body L T H t (update F x n) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hx
  exact ⟨h.toRest.upd a1 a2 a3 a4 a5 n, by rw [update_of_ne a6.symm, h.P],
    by rw [update_of_ne a7.symm, h.Vc], by rw [update_of_ne a8.symm, h.Gc],
    by rw [update_of_ne a9.symm, h.Wc], by rw [update_of_ne a10.symm, h.TW],
    by rw [update_of_ne a11.symm, h.TW1]⟩

theorem kbv_le {T H t k : ℕ} (ht : t < T) (hk : k < L.KK) : kbv L H t k ≤ L.numVars T H :=
  Cslib.Complexity.CookLevin.OneHot.kb_le (by omega) hk

theorem rowW_le' {T H : ℕ} : L.rowW H ≤ L.numVars T H := by
  unfold Layout.numVars; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

def sBodyB (g H V : ℕ) : ℕ :=
  (2 * V + 2) + (H * (2 * g + 3) + H + 2) + (2 * V + 2) + (2 * V + 2) + g * clauseB V + (V + 1) +
    (V + 1)

def oBodyB (g H d V : ℕ) : ℕ :=
  (2 * H + 2) + (2 * d + 2) + (H * (2 * g + 3) + H + 2) + (H + 1) + (2 * V + 2) + (2 * V + 2) +
    (2 * V + 2) + clauseB V + (V + 1) + (V + 1)

theorem sbody_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (F : CK → ℕ)
    (hF : Body L T H t F) (hKB : F .KB = kbv L H t k) (hU : F .U = u) (hCB : F .CB = 0)
    (hCW : F .CW = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (sBodyB L.g H (L.numVars T H)) ⟨some (.b i k (.bC1 true)), v,
        st F o⟩
      ⟨some (.s i k .sHead), false, st F ((List.range L.g).flatMap (fun x =>
          encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++ o)⟩ := by
  have hV := cw_le (L := L) (T := T) ht k.2 (show u < H by omega)
  have hW := rowW_le' (L := L) (T := T) (H := H)
  set cb := u * L.g + kbv L H t k with hcb
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.bC1 true)) (l₂ := .b i k (.bC2 true))
    (next := .b i k (.sM .head)) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .b i k (.sM s))
    (next := .b i k (.w1 true)) (a := .U) (ad := .md) (b := .Gc) (c := .CB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w1 true)) (l₂ := .b i k (.w2 true))
    (next := .b i k (.w3 true)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w3 true)) (l₂ := .b i k (.w4 true))
    (next := GeneratorLabel.xFrom i k L.g) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .CB cb) .CW (cb + L.rowW H)) (by
    funext x; cases x <;> simp [hKB, hU, hF.Gc, hF.Wc, hCB, hCW, hcb]; omega) ?_
  have hF' : Body L T H t (update (update F .CB cb) .CW (cb + L.rowW H)) :=
    (hF.upd (by decide) cb).upd (by decide) _
  obtain ⟨v1,
      rx⟩ := xs_run (sa := sa) (pu := pu) ht hwf hu _ hF' (by simp [hcb]) (by simp [hcb]) L.g le_rfl o
    false
  refine rx.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCB true))
    (next := .b i k (.dCW true)) (x := .CB) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCW true)) (next := .s i k .sHead)
    (x := .CW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) (show u ≤ H by omega)
    have h2 := kbv_le (L := L) (H := H) ht k.2
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKB, hU, hF.Gc,
      hF.Wc, hCB, hCW, Nat.add_zero]
    unfold sBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB, hCW]

theorem obody_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {r : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hr : r < cn i k - pl i k) (F : CK → ℕ)
    (hF : Body L T H t F) (hKB : F .KB = kbv L H t k) (hU : F .U = H - max (pl i k) (cn i k))
    (hR : F .R = r) (hKa : F .Ka = 0) (hCB : F .CB = 0) (hCW : F .CW = 0) (o : List Bool)
    (v : Bool) :
    RunLe (prog L sa pl cn pu N) (oBodyB L.g H L.d (L.numVars T H)) ⟨some (.s i k .oC1), v, st F o⟩
      ⟨some (.s i k .oHead), false,
        st F (encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r)) ++ o)⟩ := by
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have hm : max (pl i k) (cn i k) = cn i k := max_eq_right (by omega)
  have hV := cw_le (L := L) (T := T) ht k.2 (show H - cn i k + r < H by omega)
  have hW := rowW_le' (L := L) (T := T) (H := H)
  set cb := (H - cn i k + r) * L.g + kbv L H t k with hcb
  rw [hm] at hU
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .oC1) (l₂ := .s i k .oC2)
    (next := .s i k .oR1) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .oR1) (l₂ := .s i k .oR2)
    (next := .s i k (.oM .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .s i k (.oM s))
    (next := .s i k .oD) (a := .Ka) (ad := .md) (b := .Gc) (c := .CB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .oD) (next := .b i k (.bC1 false))
    (x := .Ka) rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.bC1 false)) (l₂ := .b i k (.bC2 false))
    (next := .b i k (.w1 false)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w1 false)) (l₂ := .b i k (.w2 false))
    (next := .b i k (.w3 false)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w3 false)) (l₂ := .b i k (.w4 false))
    (next := .b i k (.e00 .ov)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .CB cb) .CW (cb + L.rowW H)) (by
    funext x; cases x <;> simp [hKB, hU, hR, hKa, hF.Gc, hF.Wc, hCB, hCW, hcb] <;> ring) ?_
  have hF' : Body L T H t (update (update F .CB cb) .CW (cb + L.rowW H)) :=
    (hF.upd (by decide) cb).upd (by decide) _
  have rc := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k (c := .ov)
    (ovPos L sa pl cn H t i k r) _ hF'.toRest
    (fun l => by
      simp only [ovPos, CL.bs, csv, CL.cs]
      split_ifs
      · simp [BS.k, hF.TW1, Layout.xIdx]
      · simp only [BS.k, update_self, hcb, kbv, Layout.cIdx]
        have : H - cn i k + pl i k + r = H - cn i k + r + pl i k := by omega
        rw [this]; ring)
    (fun l => by
      have := rowW_le (L := L) (H := H) ht
      simp only [CL.bs]; split_ifs <;> simp [BS.k, hF.TW1] <;> omega)
    (ovPos_mono ht hwf hr) (by simp [hF.Vc]) (by simp [hF.P]) o false
  rw [clits_ov] at rc
  refine rc.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCB false))
    (next := .b i k (.dCW false)) (x := .CB) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCW false)) (next := .s i k .oHead)
    (x := .CW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) (show r + (H - cn i k) ≤ H by omega)
    have h2 := kbv_le (L := L) (H := H) ht k.2
    have h3 : (r + (H - cn i k)) * L.g = (H - cn i k + r) * L.g := by ring
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKB, hU, hR,
      hKa, hF.Gc, hF.Wc, hCB, hCW, Nat.add_zero]
    unfold oBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB, hCW]

end Bodies

section Top

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

structure Blk (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Body L T H t F where
  KB : F .KB = 0
  U : F .U = 0
  Ui : F .Ui = 0
  R : F .R = 0
  Ri : F .Ri = 0
  Ka : F .Ka = 0
  CB : F .CB = 0
  CW : F .CW = 0
  HG : F .HG = H * L.g
  Hs : F .Hs = H

def ikB (g KK H d V : ℕ) : ℕ :=
  1 + (2 * V + 2) + 1 + (KK * (2 * V + 3) + KK + 2) + (KK + 1) + (2 * H + 2) + d + 1 +
    ((2 * V + 2) + (2 * V + 2) + d * clauseB V + (V + 1)) +
    (d * (oBodyB g H d V + 1) + d + 2) + (H * (sBodyB g H V + 1) + H + 2) + (H + 1) + (d + 1) +
    (V + 1)

theorem encodeCNF_shBlk (T H t i k : ℕ) :
    encodeCNF (shBlk L sa pl cn pu T H t i k) =
      (List.range (H - max (pl i k) (cn i k))).flatMap (fun u => (List.range L.g).flatMap
        fun x => encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++
      (List.range (cn i k - pl i k)).flatMap
        (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) ++
      (List.range (pl i k)).flatMap
        (fun j => encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) := by
  simp [encodeCNF, shBlk, List.flatMap_append, List.flatMap_assoc, List.flatMap_map]

theorem hg_le {T H : ℕ} (hK : 0 < L.KK) : H * L.g ≤ L.numVars T H := by
  have h1 : H * L.g ≤ L.KK * (H * L.g) := Nat.le_mul_of_pos_left _ hK
  have h2 := rowW_le' (L := L) (T := T) (H := H)
  unfold Layout.rowW at h2; omega

theorem ik_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (i : Fin N) (k : Fin L.KK)
    (F : CK → ℕ) (hF : Blk L T H t F) (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (ikB L.g L.KK H L.d (L.numVars T H)) ⟨some (.s i k .kbE), v,
        st F o⟩
      ⟨some (GeneratorLabel.ik i.val k.val), false, st F (encodeCNF (shBlk L sa pl cn pu T H t i k) ++ o)⟩ := by
  have hp := hwf.pl_le i i.2 k k.2
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have hmd : max (pl i k) (cn i k) ≤ L.d := max_le hp hc
  have hmp : pl i k ≤ max (pl i k) (cn i k) := le_max_left _ _
  have hmc : cn i k ≤ max (pl i k) (cn i k) := le_max_right _ _
  set m := max (pl i k) (cn i k) with hm
  refine Bud.start ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .kbE) (next := .s i k .kbC1) (x := .KB)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .kbC1) (l₂ := .s i k .kbC2)
    (next := .s i k .kbK) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) v
    o).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .kbK) (next := .s i k (.kbM .head))
    (x := .Ka) rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .s i k (.kbM s))
    (next := .s i k .kbD) (a := .Ka) (ad := .md) (b := .HG) (c := .KB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .kbD) (next := .s i k .uC1) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .uC1) (l₂ := .s i k .uC2)
    (next := GeneratorLabel.sbL i k m) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .KB (kbv L H t k)) .U (H - m + m)) (by
    funext x; cases x <;> simp [hF.KB, hF.U, hF.Ka, hF.TW, hF.HG, hF.Hs, kbv]; omega) ?_
  obtain ⟨v1, rsb⟩ := sb_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) i k m (by omega)
    (update (update F .KB (kbv L H t k)) .U (H - m + m)) (H - m) (by simp) false o
  refine rsb.bud ?_

  set F1 := update (update F .KB (kbv L H t k)) .U (H - m) with hF1
  refine bud_st (F' := F1) (by funext x; cases x <;> simp [hF1]) ?_
  have hB1 : Body L T H t F1 := (hF.toBody.upd (by decide) _).upd (by decide) _
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .fC1) (l₂ := .s i k .fC2)
    (next := .s i k .fW1) rfl rfl (by decide) (by decide) (by decide) F1 hB1.tmp v1 o).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .fW1) (l₂ := .s i k .fW2)
    (next := GeneratorLabel.pfFrom i k (pl i k)) rfl rfl (by decide) (by decide) (by decide) _
    (by simp [hB1.tmp]) _ _).bud ?_
  set Ff := update F1 .CW (kbv L H t k + L.rowW H) with hFf
  refine bud_st (F' := Ff) (by
    funext x; cases x <;> simp [hFf, hF1, hF.CW, hF.Wc]; omega) ?_
  have hBf : Body L T H t Ff := hB1.upd (by decide) _
  obtain ⟨v2, rpf⟩ := pf_run (sa := sa) (cn := cn) (i := i) (k := k) ht hwf Ff hBf
    (by simp [hFf]) (pl i k) le_rfl o false
  refine rpf.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .fD1) (next := .s i k .oE)
    (x := .CW) rfl _ _ _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .oE) (next := .s i k .oHead) (x := .R)
    rfl _ _ _).bud ?_
  set F2 := update (update (update F .KB (kbv L H t k)) .U (H - m)) .R (cn i k - pl i k) with hF2
  refine bud_st (F' := F2) (by
    funext x; cases x <;> simp [hF2, hFf, hF1, hF.R, hF.CW]) ?_
  have hB2 : Body L T H t F2 :=
    ((hF.toBody.upd (by decide) _).upd (by decide) _).upd (by decide) _
  have l1 := stLoop (M := prog L sa pl cn pu N) (c := .R) (cd := .Ri) (head := .s i k .oHead)
    (body := .s i k .oC1) (rest := .s i k .oRest) (next := .s i k .sHead) rfl rfl (by decide)
    (cn i k - pl i k) (oBodyB L.g H L.d (L.numVars T H))
    (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) F2
    (by simp [hF2]) (by simp [hF2, hF.Ri])
    (fun r hr o' => ⟨false, obody_run ht hwf hr _ ((hB2.upd (by decide) _).upd (by decide) _)
      (by simp [hF2]) (by simp [hF2, hm]) (by simp) (by simp [hF2, hF.Ka]) (by simp [hF2, hF.CB])
      (by simp [hF2, hF.CW]) o' true⟩)
    false ((List.range (pl i k)).flatMap (fun j =>
      encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o)
  refine l1.bud ?_
  have l2 := stLoop (M := prog L sa pl cn pu N) (c := .U) (cd := .Ui) (head := .s i k .sHead)
    (body := .b i k (.bC1 true)) (rest := .s i k .sRest) (next := .s i k .dU) rfl rfl (by decide)
    (H - m) (sBodyB L.g H (L.numVars T H))
    (fun u => (List.range L.g).flatMap fun x =>
      encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) F2
    (by simp [hF2]) (by simp [hF2, hF.Ui])
    (fun u hu o' => ⟨false, sbody_run ht hwf (by omega) _
      ((hB2.upd (by decide) _).upd (by decide) _) (by simp [hF2]) (by simp)
      (by simp [hF2, hF.CB]) (by simp [hF2, hF.CW]) o' true⟩)
    false ((List.range (cn i k - pl i k)).flatMap
      (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) ++
      ((List.range (pl i k)).flatMap (fun j =>
        encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o))
  refine l2.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dU) (next := .s i k .dR) (x := .U) rfl _
    _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dR) (next := .s i k .dKB) (x := .R) rfl
    _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dKB) (next := GeneratorLabel.ik i.val k.val)
    (x := .KB) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := kbv_le (L := L) (H := H) ht k.2
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have hHG := hg_le (L := L) (T := T) (H := H) (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2)
    have h3 : k.val * (2 * (H * L.g) + 3) ≤ L.KK * (2 * L.numVars T H + 3) :=
      Nat.mul_le_mul k.2.le (by omega)
    have h4 := Nat.mul_le_mul_right (oBodyB L.g H L.d (L.numVars T H) + 1)
      (show cn i k - pl i k ≤ L.d by omega)
    have h5 := Nat.mul_le_mul_right (sBodyB L.g H (L.numVars T H) + 1) (show H - m ≤ H by omega)
    have h6 := Nat.mul_le_mul_right (clauseB (L.numVars T H)) hp
    have h7 := kbw_le (L := L) (H := H) ht k.2
    have h8 := rowW_le' (L := L) (T := T) (H := H)
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF2, hFf, hF1,
      hF.KB, hF.Ka, hF.TW, hF.HG, hF.Hs, hF.Wc, hF.CW, Nat.add_zero]
    unfold ikB
    omega
  · simp only [encodeCNF_shBlk, List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hF2, hF.KB, hF.U, hF.R]

def blkI (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (T H t i : ℕ) : List Bool :=
  (List.range L.KK).flatMap fun k => encodeCNF (shBlk L sa pl cn pu T H t i k)

def blkT (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (N T H t : ℕ) : List Bool :=
  (List.range N).flatMap (blkI L sa pl cn pu T H t)

theorem ks_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (i : Fin N) (F : CK → ℕ)
    (hF : Blk L T H t F) :
    ∀ n, n ≤ L.KK → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * ikB L.g L.KK H L.d (L.numVars T H))
        ⟨some (GeneratorLabel.ik i.val n), v, st F o⟩
        ⟨some (GeneratorLabel.iFrom i.val), v', st F ((List.range n).flatMap
          (fun k => encodeCNF (shBlk L sa pl cn pu T H t i k)) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GeneratorLabel.ik] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have r := ik_run ht hwf i ⟨n, by omega⟩ F hF o v
      obtain ⟨v', r'⟩ := ih (by omega) (encodeCNF (shBlk L sa pl cn pu T H t i n) ++ o) false
      refine ⟨v', ?_⟩
      rw [GeneratorLabel.ik_succ i.2 (by omega)]
      refine Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem is_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (F : CK → ℕ)
    (hF : Blk L T H t F) :
    ∀ n, n ≤ N → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * (L.KK * ikB L.g L.KK H L.d (L.numVars T H)))
        ⟨some (GeneratorLabel.iFrom n), v, st F o⟩
        ⟨some .tEnd, v', st F ((List.range n).flatMap (blkI L sa pl cn pu T H t) ++ o)⟩ := by
  by_cases hK : L.KK = 0
  · intro n _ o v
    refine ⟨v, ?_⟩
    rw [GeneratorLabel.iFrom_KK0 hK]
    have : (List.range n).flatMap (blkI L sa pl cn pu T H t) = [] := by simp [blkI, hK]
    rw [this, List.nil_append]
    exact RunLe.refl _ _
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GeneratorLabel.iFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      obtain ⟨v1, r⟩ := ks_run ht hwf ⟨n, by omega⟩ F hF L.KK le_rfl o v
      obtain ⟨v', r'⟩ := ih (by omega) (blkI L sa pl cn pu T H t n ++ o) v1
      refine ⟨v', ?_⟩
      rw [GeneratorLabel.iFrom_succ (by omega) (by omega)]
      refine Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

def tBodyB (L : Layout) (N T H : ℕ) : ℕ :=
  (T * (2 * L.numVars T H + 3) + T + 2) + (2 * L.numVars T H + 2) + (2 * L.numVars T H + 2) +
    N * (L.KK * ikB L.g L.KK H L.d (L.numVars T H)) + (L.numVars T H + 1) + (L.numVars T H + 1)

theorem tbody_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (F : CK → ℕ)
    (hF : Rest F) (hP : F .P = 0) (hV : F .Vc = L.numVars T H) (hG : F .Gc = L.g)
    (hW : F .Wc = L.rowW H) (hTW : F .TW = 0) (hTW1 : F .TW1 = 0) (hTn : F .Tn = t)
    (hKB : F .KB = 0) (hU : F .U = 0)
    (hUi : F .Ui = 0) (hR : F .R = 0) (hRi : F .Ri = 0) (hKa : F .Ka = 0) (hCB : F .CB = 0)
    (hCW : F .CW = 0) (hHG : F .HG = H * L.g) (hHs : F .Hs = H) (o : List Bool) (v : Bool) :
    ∃ v' : Bool, RunLe (prog L sa pl cn pu N) (tBodyB L N T H) ⟨some (.tw .head), v, st F o⟩
      ⟨some .tHead, v', st F (blkT L sa pl cn pu N T H t ++ o)⟩ := by
  set F1 := update (update F .TW (t * L.rowW H)) .TW1 ((t + 1) * L.rowW H) with hF1
  have hB : Blk L T H t F1 :=
    ⟨⟨(hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _).upd (by decide)
      (by decide) (by decide) (by decide) (by decide) _, by simp [hF1, hP], by simp [hF1, hV],
      by simp [hF1, hG], by simp [hF1, hW], by simp [hF1], by simp [hF1]⟩, by simp [hF1, hKB],
      by simp [hF1, hU], by simp [hF1, hUi], by simp [hF1, hR], by simp [hF1, hRi],
      by simp [hF1, hKa], by simp [hF1, hCB], by simp [hF1, hCW], by simp [hF1, hHG],
      by simp [hF1, hHs]⟩
  obtain ⟨v1, ri⟩ := is_run ht hwf _ hB N le_rfl o false
  refine ⟨false, Bud.start ?_⟩
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := .tw) (next := .t1a) (a := .Tn) (ad := .md)
    (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .t1a) (l₂ := .t1b) (next := .t1c) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .t1c) (l₂ := .t1d) (next := GeneratorLabel.iFrom N) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := F1) (by
    funext x; cases x <;> simp [hF1, hTn, hW, hTW, hTW1]; ring) ?_
  refine ri.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .tEnd) (next := .tEnd2) (x := .TW) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .tEnd2) (next := .tHead) (x := .TW1) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.rowW H + 3) ht.le
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have h3 := Nat.mul_le_mul_left T (show 2 * L.rowW H + 3 ≤ 2 * L.numVars T H + 3 by
      have := rowW_le' (L := L) (T := T) (H := H); omega)
    have h4 := rowW_le (L := L) (H := H) ht
    have h5 := rowW_le' (L := L) (T := T) (H := H)
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF1, hTn, hW,
      hTW, hTW1, Nat.add_zero, Nat.zero_add]
    unfold tBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hF1, hTW, hTW1]

def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

def preF (L : Layout) (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Vc => L.numVars T H
  | _ => 0

def preB (L : Layout) (T H : ℕ) : ℕ :=
  1 + (H * (2 * L.g + 3) + H + 2) + 1 + 1 + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) + (L.KK + 1) +
    (T * (2 * L.rowW H + 3) + T + 2) + (2 * L.rowW H + 2)

def shBound (L : Layout) (N T H : ℕ) : ℕ := preB L T H + (T * (tBodyB L N T H + 1) + T + 2)

theorem encodeCNF_shFamily (T H : ℕ) :
    encodeCNF (shFamily L sa pl cn pu N T H) = (List.range T).flatMap (blkT L sa pl cn pu N T H) := by
  simp [encodeCNF, shFamily, List.flatMap_assoc]
  rfl

theorem sh_run (T H : ℕ) (hwf : WF L sa pl cn pu N H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L sa pl cn pu N) (shBound L N T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (shFamily L sa pl cn pu N T H) ++ o := by
  refine ⟨false, st (preF L T H) (encodeCNF (shFamily L sa pl cn pu N T H) ++ o), ?_, rfl⟩
  refine Bud.start ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.hg s)) (next := .pre .ew)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .ek) (next := .pre (.w .head)) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.w s)) (next := .pre .dk)
    (a := .Ka) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .pre .dk) (next := .pre (.v .head)) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.v s)) (next := .pre .vw1)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .pre .vw1) (l₂ := .pre .vw2) (next := .tHead) rfl
    rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars] <;> ring) ?_
  have hloop := stLoop (M := prog L sa pl cn pu N) (c := .Tn) (cd := .Ti) (head := .tHead)
    (body := .tw .head) (rest := .tRest) (next := .done) rfl rfl (by decide) T (tBodyB L N T H)
    (blkT L sa pl cn pu N T H) (preF L T H) rfl rfl
    (fun t ht o' => tbody_run ht hwf _
      ⟨by simp [preF], by simp [preF], by simp [preF], by simp [preF], by simp [preF]⟩
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) o' true)
    false o
  rw [← encodeCNF_shFamily] at hloop
  refine hloop.bud (Bud.fin ?_ rfl)
  simp [initF, preB, shBound, Layout.rowW]
  ring_nf
  omega

end Top

section Poly

theorem shBound_mono {L L' : Layout} {N N' T T' H H' : ℕ} (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK)
    (hg : L.g ≤ L'.g) (hd : L.d ≤ L'.d) (hN : N ≤ N') (hT : T ≤ T') (hH : H ≤ H') :
    shBound L N T H ≤ shBound L' N' T' H' := by
  unfold shBound preB tBodyB ikB oBodyB sBodyB clauseB litE Layout.numVars Layout.rowW
  gcongr

theorem shBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    shBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k y y ≤ 828 * k ^ 7 * y ^ 6 := by
  have m : ∀ a b, a ≤ 7 → b ≤ 6 → k ^ a * y ^ b ≤ k ^ 7 * y ^ 6 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold shBound preB tBodyB ikB oBodyB sBodyB clauseB litE Layout.numVars Layout.rowW
    Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  linarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num),
    m 6 2 (by norm_num) (by norm_num),
    m 6 3 (by norm_num) (by norm_num),
    m 6 4 (by norm_num) (by norm_num),
    m 6 5 (by norm_num) (by norm_num),
    m 7 3 (by norm_num) (by norm_num),
    m 7 4 (by norm_num) (by norm_num),
    m 7 5 (by norm_num) (by norm_num),
    m 7 6 (by norm_num) (by norm_num)]

def shC (L : Layout) (N : ℕ) : ℕ := 828 * (L.A + L.KK + L.g + L.d + N + 1) ^ 7

theorem shBound_le (L : Layout) (N T H : ℕ) : shBound L N T H ≤ shC L N * (T + H + 1) ^ 6 := by
  have := shBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + L.d + N + 1))
    (N := N) (N' := L.A + L.KK + L.g + L.d + N + 1) (T := T) (T' := T + H + 1) (H := H)
    (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by omega) (by omega) (by omega)
  have h2 := shBound_uni (L.A + L.KK + L.g + L.d + N + 1) (T + H + 1) (by omega) (by omega)
  unfold shC
  exact this.trans h2

open Polynomial in

noncomputable def shPoly (L : Layout) (N : ℕ) : Polynomial ℕ := C (shC L N) * (X + 1) ^ 6

theorem shPoly_eval (L : Layout) (N T H : ℕ) :
    (shPoly L N).eval (T + H) = shC L N * (T + H + 1) ^ 6 := by
  simp [shPoly]

theorem sh_time {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}
    (T H : ℕ)
    (hwf : WF L sa pl cn pu N H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L sa pl cn pu N) (shC L N * (T + H + 1) ^ 6)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (shFamily L sa pl cn pu N T H) ++ o :=
  let ⟨v, S, h, h'⟩ := sh_run T H hwf o; ⟨v, S, h.mono (shBound_le L N T H), h'⟩

end Poly

end Cslib.Complexity.CookLevin.Shift
end

-- CSLibExt.Computability.Complexity.CookLevin.Situation
section
namespace Cslib.Complexity.CookLevin.Situation

open MetaMathlibExt

open Turing Function

section Eff

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def readTop (W : ∀ k, List (Option (Γ k))) (P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K) :
    Option (Γ k) :=
  match P k with
  | x :: _ => some x
  | [] => (W k).getD (c k) none

def eff (W : ∀ k, List (Option (Γ k))) :
    TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → (K → ℕ) →
      Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)
  | .push k f q, v, P, c => eff W q v (update P k (f v :: P k)) c
  | .peek k f q, v, P, c => eff W q (f v (readTop W P c k)) P c
  | .pop k f q, v, P, c =>
      eff W q (f v (readTop W P c k)) (update P k (P k).tail)
        (if (P k).isEmpty then update c k (c k + 1) else c)
  | .load a q, v, P, c => eff W q (a v) P c
  | .branch p q₁ q₂, v, P, c => cond (p v) (eff W q₁ v P c) (eff W q₂ v P c)
  | .goto f, v, P, c => (some (f v), v, P, c)
  | .halt, v, P, c => (none, v, P, c)

def ops : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => ops q + 1
  | .peek _ _ q => ops q + 1
  | .pop _ _ q => ops q + 1
  | .load _ q => ops q
  | .branch _ q₁ q₂ => max (ops q₁) (ops q₂)
  | .goto _ => 0
  | .halt => 0

def PushSym (k : K) : TM2.Stmt Γ Λ σ → Γ k → Prop
  | .push k' f q, x => (∃ (h : k' = k) (v : σ), x = cast (congrArg Γ h) (f v)) ∨ PushSym k q x
  | .peek _ _ q, x => PushSym k q x
  | .pop _ _ q, x => PushSym k q x
  | .load _ q, x => PushSym k q x
  | .branch _ q₁ q₂, x => PushSym k q₁ x ∨ PushSym k q₂ x
  | .goto _, _ => False
  | .halt, _ => False

theorem length_update_le (P : ∀ k, List (Γ k)) (k₀ k : K) (l : List (Γ k₀))
    (h : l.length ≤ (P k₀).length + 1) : (update P k₀ l k).length ≤ (P k).length + 1 := by
  by_cases hk : k = k₀
  · subst hk; simpa using h
  · rw [update_of_ne hk]; omega

theorem eff_bound (W : ∀ k, List (Option (Γ k))) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K),
      ((eff W q v P c).2.2.1 k).length ≤ (P k).length + ops q ∧
        (eff W q v P c).2.2.2 k ≤ c k + ops q := by
  induction q with
  | push k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih v (update P k₀ (f v :: P k₀)) c k
      have := length_update_le P k₀ k (f v :: P k₀) (by simp)
      simp only [eff, ops]; omega
  | peek k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih (f v (readTop W P c k₀)) P c k
      simp only [eff, ops]; omega
  | pop k₀ f q ih =>
      intro v P c k
      obtain ⟨h1, h2⟩ := ih (f v (readTop W P c k₀)) (update P k₀ (P k₀).tail)
        (if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c) k
      have e1 := length_update_le P k₀ k (P k₀).tail (by simp; omega)
      have e2 : (if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c) k ≤ c k + 1 := by
        split
        · by_cases hk : k = k₀
          · subst hk; simp
          · rw [update_of_ne hk]; omega
        · omega
      simp only [eff, ops]; omega
  | load a q ih =>
      intro v P c k
      exact ih (a v) P c k
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c k
      simp only [eff, ops]
      cases p v
      · obtain ⟨h1, h2⟩ := ih₂ v P c k; simp only [cond_false]; omega
      · obtain ⟨h1, h2⟩ := ih₁ v P c k; simp only [cond_true]; omega
  | goto f => intro v P c k; simp [eff]
  | halt => intro v P c k; simp [eff]

theorem eff_pushed (W : ∀ k, List (Option (Γ k))) (Q : ∀ k, Γ k → Prop) (q : TM2.Stmt Γ Λ σ)
    (hq : ∀ k x, PushSym k q x → Q k x) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ), (∀ k, ∀ x ∈ P k, Q k x) →
      ∀ k, ∀ x ∈ (eff W q v P c).2.2.1 k, Q k x := by
  induction q with
  | push k₀ f q ih =>
      intro v P c hP
      refine ih (fun k x h => hq k x (Or.inr h)) v _ c ?_
      intro k x hx
      by_cases hk : k = k₀
      · subst hk
        rw [update_self, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hq k (f v) (Or.inl ⟨rfl, v, rfl⟩)
        · exact hP k x hx
      · rw [update_of_ne hk] at hx; exact hP k x hx
  | peek k₀ f q ih =>
      intro v P c hP; exact ih hq _ P c hP
  | pop k₀ f q ih =>
      intro v P c hP
      refine ih hq _ _ _ ?_
      intro k x hx
      by_cases hk : k = k₀
      · subst hk
        rw [update_self] at hx
        exact hP k x (List.mem_of_mem_tail hx)
      · rw [update_of_ne hk] at hx; exact hP k x hx
  | load a q ih =>
      intro v P c hP; exact ih hq _ P c hP
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c hP
      simp only [eff]
      cases p v
      · exact ih₂ (fun k x h => hq k x (Or.inr h)) v P c hP
      · exact ih₁ (fun k x h => hq k x (Or.inl h)) v P c hP
  | goto f => intro v P c hP; exact hP
  | halt => intro v P c hP; exact hP

end Eff

structure Enc (M : FinTM2) where

  KK : ℕ

  kc : M.K → ℕ

  kd : ℕ → M.K
  kc_lt : ∀ k, kc k < KK
  kd_kc : ∀ k, kd (kc k) = k
  kc_kd : ∀ n < KK, kc (kd n) = n

  A0 : ℕ

  lc : Option M.Λ × M.σ → ℕ

  ld : ℕ → Option M.Λ × M.σ
  lc_lt : ∀ x, lc x < A0
  ld_lc : ∀ x, ld (lc x) = x
  lc_ld : ∀ c < A0, lc (ld c) = c

  sz : M.K → ℕ

  dec : ∀ k, Fin (sz k) → M.Γ k

  enc : ∀ k, M.Γ k → ℕ
  enc_dec : ∀ k i, enc k (dec k i) = i + 1
  push_mem : ∀ l k x, PushSym k (M.m l) x → ∃ i, dec k i = x
  input_mem : ∀ x : M.Γ M.k₀, ∃ i, dec M.k₀ i = x

def depth (M : FinTM2) : ℕ :=
  letI := M.ΛFin
  Finset.univ.sup fun l => ops (M.m l)

theorem ops_le_depth (M : FinTM2) (l : M.Λ) : ops (M.m l) ≤ depth M := by
  letI := M.ΛFin
  exact Finset.le_sup (f := fun l => ops (M.m l)) (Finset.mem_univ l)

def sitStep (M : FinTM2) (l : Option M.Λ) (v : M.σ) (W : ∀ k, List (Option (M.Γ k))) :
    Option M.Λ × M.σ × (∀ k, List (M.Γ k)) × (M.K → ℕ) :=
  match l with
  | none => (none, v, fun _ => [], fun _ => 0)
  | some l => eff W (M.m l) v (fun _ => []) (fun _ => 0)

namespace Enc

variable {M : FinTM2} (E : Enc M)

def g : ℕ :=
  letI := M.kFin
  1 + Finset.univ.sup E.sz

def G : ℕ := E.g ^ (E.KK * depth M)

def N : ℕ := E.A0 * E.G

def layout : Family.Layout := ⟨E.A0 + E.N, E.KK, E.g, depth M⟩

def la (i : ℕ) : ℕ := i / E.G % E.A0

def wa (i k j : ℕ) : ℕ := i / E.g ^ (k * depth M + j) % E.g

def sa (i : ℕ) : ℕ := E.A0 + i

def decO (k : M.K) (c : ℕ) : Option (M.Γ k) :=
  if h : 1 ≤ c ∧ c - 1 < E.sz k then some (E.dec k ⟨c - 1, h.2⟩) else none

def win (i : ℕ) : ∀ k, List (Option (M.Γ k)) := fun k =>
  (List.range (depth M)).map fun j => E.decO k (E.wa i (E.kc k) j)

def res (i : ℕ) : Option M.Λ × M.σ × (∀ k, List (M.Γ k)) × (M.K → ℕ) :=
  sitStep M (E.ld (E.la i)).1 (E.ld (E.la i)).2 (E.win i)

def na (i : ℕ) : ℕ := E.lc ((E.res i).1, (E.res i).2.1)

def pl (i k : ℕ) : ℕ := ((E.res i).2.2.1 (E.kd k)).length

def cn (i k : ℕ) : ℕ := (E.res i).2.2.2 (E.kd k)

def pu (i k j : ℕ) : ℕ := (((E.res i).2.2.1 (E.kd k))[j]?).elim 0 (E.enc (E.kd k))

theorem g_pos : 0 < E.g := by unfold g; omega

theorem sz_lt_g (k : M.K) : E.sz k < E.g := by
  letI := M.kFin
  have := Finset.le_sup (f := E.sz) (Finset.mem_univ k)
  unfold g; omega

theorem A0_pos : 0 < E.A0 := Nat.lt_of_le_of_lt (Nat.zero_le _) (E.lc_lt (none, M.initialState))

theorem la_lt (i : ℕ) : E.la i < E.A0 := Nat.mod_lt _ E.A0_pos

theorem na_lt (i : ℕ) : E.na i < E.A0 := E.lc_lt _

theorem wa_lt (i k j : ℕ) : E.wa i k j < E.g := Nat.mod_lt _ E.g_pos

theorem res_bound (i : ℕ) (k : M.K) :
    ((E.res i).2.2.1 k).length ≤ depth M ∧ (E.res i).2.2.2 k ≤ depth M := by
  unfold res sitStep
  split
  · simp
  · next l _ =>
    have := eff_bound (E.win i) (M.m l) (E.ld (E.la i)).2 (fun _ => []) (fun _ => 0) k
    have := ops_le_depth M l
    simp only [List.length_nil] at *; omega

theorem pl_le (i k : ℕ) : E.pl i k ≤ depth M := (E.res_bound i (E.kd k)).1

theorem cn_le (i k : ℕ) : E.cn i k ≤ depth M := (E.res_bound i (E.kd k)).2

theorem res_pushed (i : ℕ) (k : M.K) (x : M.Γ k) (hx : x ∈ (E.res i).2.2.1 k) :
    ∃ n, E.dec k n = x := by
  unfold res sitStep at hx
  split at hx
  · simp at hx
  · next l _ =>
    exact eff_pushed (E.win i) (fun k x => ∃ n, E.dec k n = x) (M.m l)
      (fun k x h => E.push_mem l k x h) _ _ _ (fun _ _ h => by simp at h) k x hx

theorem decO_succ (k : M.K) (n : Fin (E.sz k)) : E.decO k (n + 1) = some (E.dec k n) := by
  unfold decO
  rw [dif_pos ⟨by omega, by simp⟩]
  simp

theorem pu_valid (i k j : ℕ) (hj : j < E.pl i k) :
    ∃ x, ((E.res i).2.2.1 (E.kd k))[j]? = some x ∧ E.pu i k j = E.enc (E.kd k) x ∧
      1 ≤ E.pu i k j ∧ E.pu i k j ≤ E.sz (E.kd k) ∧ E.decO (E.kd k) (E.pu i k j) = some x := by
  unfold pl at hj
  obtain ⟨x, hx⟩ : ∃ x, ((E.res i).2.2.1 (E.kd k))[j]? = some x :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  have hmem : x ∈ (E.res i).2.2.1 (E.kd k) := List.mem_of_getElem? hx
  obtain ⟨n, rfl⟩ := E.res_pushed i _ x hmem
  have hpu : E.pu i k j = n + 1 := by unfold pu; rw [hx]; simp [E.enc_dec]
  refine ⟨_, hx, by rw [hpu, E.enc_dec], by omega, by have := n.2; omega, ?_⟩
  rw [hpu]; exact E.decO_succ _ n

theorem pu_lt (i k j : ℕ) (hj : j < E.pl i k) : E.pu i k j < E.g := by
  obtain ⟨_, _, _, _, h, _⟩ := E.pu_valid i k j hj
  have := E.sz_lt_g (E.kd k); omega

theorem wf_upd {H : ℕ} (hH : depth M ≤ H) (i : ℕ) : Family.WF E.layout E.la E.na E.wa H i :=
  ⟨by have := E.la_lt i; simp only [layout]; omega,
   by have := E.na_lt i; simp only [layout]; omega,
   fun k _ j _ => E.wa_lt i k j, hH⟩

theorem wf_sdef {H : ℕ} (hH : depth M ≤ H) (i : ℕ) (hi : i < E.N) :
    Family.WF E.layout E.la E.sa E.wa H i :=
  ⟨by have := E.la_lt i; simp only [layout]; omega,
   by simp only [layout, sa]; omega,
   fun k _ j _ => E.wa_lt i k j, hH⟩

theorem wf_sh {H : ℕ} (hH : depth M ≤ H) : Shift.WF E.layout E.sa E.pl E.cn E.pu E.N H :=
  ⟨E.g_pos, hH, fun i hi => by simp only [layout, sa]; omega,
   fun i _ k _ => E.pl_le i k, fun i _ k _ => E.cn_le i k,
   fun i _ k _ j hj => E.pu_lt i k j hj⟩

def mix (b c : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => c
  | m + 1, D => D 0 + b * mix b c m (fun n => D (n + 1))

theorem mix_spec (b c : ℕ) : ∀ (m : ℕ) (D : ℕ → ℕ), (∀ n < m, D n < b) →
    (∀ n < m, mix b c m D / b ^ n % b = D n) ∧ mix b c m D / b ^ m = c ∧
      mix b c m D < (c + 1) * b ^ m := by
  intro m
  induction m with
  | zero => intro D _; simp [mix]
  | succ m ih =>
      intro D hD
      obtain ⟨h1, h2, h3⟩ := ih (fun n => D (n + 1)) (fun n hn => hD (n + 1) (by omega))
      have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) (hD 0 (by omega))
      have h0 := hD 0 (by omega)
      have hdiv : (D 0 + b * mix b c m (fun n => D (n + 1))) / b =
          mix b c m (fun n => D (n + 1)) := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h0, Nat.zero_add]
      simp only [mix]
      refine ⟨?_, ?_, ?_⟩
      · intro n hn
        cases n with
        | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
        | succ n =>
            rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]; exact h1 n (by omega)
      · rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv, h2]
      · have : b * (mix b c m (fun n => D (n + 1)) + 1) ≤ b * ((c + 1) * b ^ m) :=
          Nat.mul_le_mul_left _ h3
        rw [pow_succ']
        have e : b * ((c + 1) * b ^ m) = (c + 1) * (b * b ^ m) := by ring
        rw [Nat.mul_add, e] at this; omega

theorem mix_sit (c : ℕ) (hc : c < E.A0) (w : ℕ → ℕ → ℕ)
    (hw : ∀ k < E.KK, ∀ j < depth M, w k j < E.g) :
    mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M)) < E.N ∧
    E.la (mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M))) = c ∧
    ∀ k < E.KK, ∀ j < depth M,
      E.wa (mix E.g c (E.KK * depth M) (fun n => w (n / depth M) (n % depth M))) k j = w k j := by
  set d := depth M
  have hD : ∀ n < E.KK * d, (fun n => w (n / d) (n % d)) n < E.g := by
    intro n hn
    have hd : 0 < d := Nat.pos_of_ne_zero fun h => by simp [h] at hn
    exact hw _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn)) _ (Nat.mod_lt _ hd)
  obtain ⟨h1, h2, h3⟩ := mix_spec E.g c (E.KK * d) _ hD
  refine ⟨?_, ?_, ?_⟩
  · have h3' : _ < (c + 1) * E.G := h3
    exact Nat.lt_of_lt_of_le h3' (Nat.mul_le_mul_right _ hc)
  · unfold la G; rw [h2, Nat.mod_eq_of_lt hc]
  · intro k hk j hj
    have hkj : k * d + j < E.KK * d := by
      have : (k + 1) * d ≤ E.KK * d := Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at this; omega
    unfold wa; rw [h1 _ hkj]
    have hd : 0 < d := by omega
    have e1 : (k * d + j) / d = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (k * d + j) % d = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [e1, e2]

end Enc

section Classical

open Classical

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Fintype σ]

noncomputable def pushFS (k : K) : TM2.Stmt Γ Λ σ → Finset (Γ k)
  | .push k' f q =>
      (if h : k' = k then Finset.univ.image fun v => cast (congrArg Γ h) (f v) else ∅) ∪
        pushFS k q
  | .peek _ _ q => pushFS k q
  | .pop _ _ q => pushFS k q
  | .load _ q => pushFS k q
  | .branch _ q₁ q₂ => pushFS k q₁ ∪ pushFS k q₂
  | .goto _ => ∅
  | .halt => ∅

theorem mem_pushFS (k : K) (q : TM2.Stmt Γ Λ σ) (x : Γ k) (h : PushSym k q x) :
    x ∈ pushFS k q := by
  induction q with
  | push k' f q ih =>
      simp only [PushSym] at h
      simp only [pushFS, Finset.mem_union]
      rcases h with ⟨rfl, v, rfl⟩ | h
      · left; rw [dif_pos rfl]; exact Finset.mem_image_of_mem _ (Finset.mem_univ v)
      · right; exact ih h
  | peek _ _ q ih => exact ih h
  | pop _ _ q ih => exact ih h
  | load _ q ih => exact ih h
  | branch _ q₁ q₂ ih₁ ih₂ =>
      simp only [PushSym] at h
      simp only [pushFS, Finset.mem_union]
      exact h.imp ih₁ ih₂
  | goto _ => exact h.elim
  | halt => exact h.elim

noncomputable def symSet (M : FinTM2) (k : M.K) : Finset (M.Γ k) :=
  letI := M.ΛFin; letI := M.σFin; letI := M.Γk₀Fin
  (Finset.univ.biUnion fun l => pushFS k (M.m l)) ∪
    (if h : M.k₀ = k then Finset.univ.image fun x : M.Γ M.k₀ => cast (congrArg M.Γ h) x else ∅)

theorem push_mem_symSet (M : FinTM2) (l : M.Λ) (k : M.K) (x : M.Γ k)
    (h : PushSym k (M.m l) x) : x ∈ symSet M k := by
  letI := M.ΛFin; letI := M.σFin
  unfold symSet
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, mem_pushFS k _ x h⟩)

theorem input_mem_symSet (M : FinTM2) (x : M.Γ M.k₀) : x ∈ symSet M M.k₀ := by
  letI := M.Γk₀Fin
  unfold symSet
  refine Finset.mem_union_right _ ?_
  rw [dif_pos rfl]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

end Classical

section Gen

variable {M : FinTM2} (E : Enc M) {H : ℕ} (hH : depth M ≤ H)
include hH

open Cslib.Complexity.CookLevin.Family Cslib.Complexity.CookLevin.CounterView in

theorem upd_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      TM2Program.RunLe (prog E.layout E.la E.na E.wa E.N) (genC E.layout E.N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (family E.layout E.la E.na E.wa T H E.N) ++ o :=
  gen_time T H (fun i _ => E.wf_upd hH i) o

open Cslib.Complexity.CookLevin.Family Cslib.Complexity.CookLevin.CounterView in

theorem sdef_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (GΓ k)),
      TM2Program.RunLe (prog E.layout E.la E.sa E.wa E.N) (genC E.layout E.N * (T + H + 1) ^ 5)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (family E.layout E.la E.sa E.wa T H E.N) ++ o :=
  gen_time T H (fun i hi => E.wf_sdef hH i hi) o

open Cslib.Complexity.CookLevin.Shift Cslib.Complexity.CookLevin.CounterView in

theorem shift_time (T : ℕ) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ Shift.CK k)),
      TM2Program.RunLe (Shift.prog E.layout E.sa E.pl E.cn E.pu E.N) (shC E.layout E.N * (T + H + 1) ^ 6)
        ⟨some (.pre .eg), false, CounterView.st (Shift.initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = DenseSAT.encodeCNF (shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) ++ o :=
  sh_time T H (E.wf_sh hH) o

end Gen

section Agree

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def window {α : Type} (d : ℕ) (L : List α) : List (Option α) :=
  (List.range d).map fun j => L[j]?

def applyEff (S0 : ∀ k, List (Γ k)) (r : Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)) :
    TM2.Cfg Γ Λ σ :=
  ⟨r.1, r.2.1, fun k => r.2.2.1 k ++ (S0 k).drop (r.2.2.2 k)⟩

omit [DecidableEq K] in

theorem readTop_eq (d : ℕ) (S0 P : ∀ k, List (Γ k)) (c : K → ℕ) (k : K) (hc : c k < d) :
    readTop (fun k => window d (S0 k)) P c k = (P k ++ (S0 k).drop (c k)).head? := by
  unfold readTop
  cases P k with
  | cons x _ => rfl
  | nil =>
      simp [window, List.getD_eq_getElem?_getD, List.getElem?_range hc, List.head?_drop]

theorem eff_agree (d : ℕ) (S0 : ∀ k, List (Γ k)) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (P : ∀ k, List (Γ k)) (c : K → ℕ), (∀ k, c k + ops q ≤ d) →
      TM2.stepAux q v (fun k => P k ++ (S0 k).drop (c k)) =
        applyEff S0 (eff (fun k => window d (S0 k)) q v P c) := by
  induction q with
  | push k₀ f q ih =>
      intro v P c hc
      have e : update (fun k => P k ++ (S0 k).drop (c k)) k₀
          (f v :: (P k₀ ++ (S0 k₀).drop (c k₀))) =
          fun k => update P k₀ (f v :: P k₀) k ++ (S0 k).drop (c k) := by
        funext k
        by_cases hk : k = k₀
        · subst hk; simp
        · simp [update_of_ne hk]
      simp only [TM2.stepAux, eff]
      rw [e]
      exact ih v _ c fun k => by have := hc k; simp only [ops] at this; omega
  | peek k₀ f q ih =>
      intro v P c hc
      have hk : c k₀ < d := by have := hc k₀; simp only [ops] at this; omega
      simp only [TM2.stepAux, eff]
      rw [← readTop_eq d S0 P c k₀ hk]
      exact ih _ P c fun k => by have := hc k; simp only [ops] at this; omega
  | pop k₀ f q ih =>
      intro v P c hc
      have hk : c k₀ < d := by have := hc k₀; simp only [ops] at this; omega
      set c' := if (P k₀).isEmpty then update c k₀ (c k₀ + 1) else c with hc'
      have e : update (fun k => P k ++ (S0 k).drop (c k)) k₀
          (P k₀ ++ (S0 k₀).drop (c k₀)).tail =
          fun k => update P k₀ (P k₀).tail k ++ (S0 k).drop (c' k) := by
        funext k
        by_cases hk : k = k₀
        · subst hk
          rcases h : P k with _ | ⟨x, xs⟩
          · simp [hc', h, List.tail_drop]
          · simp [hc', h]
        · rw [update_of_ne hk, update_of_ne hk, hc']
          split
          · rw [update_of_ne hk]
          · rfl
      have hb : ∀ k, c' k + ops q ≤ d := by
        intro k
        have := hc k
        simp only [ops] at this
        rw [hc']
        split
        · by_cases hk : k = k₀
          · subst hk; simp; omega
          · rw [update_of_ne hk]; omega
        · omega
      simp only [TM2.stepAux, eff]
      rw [← readTop_eq d S0 P c k₀ hk, e]
      exact ih _ _ c' hb
  | load a q ih =>
      intro v P c hc
      simp only [TM2.stepAux, eff]
      exact ih _ P c fun k => by have := hc k; simp only [ops] at this; omega
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro v P c hc
      simp only [TM2.stepAux, eff]
      cases p v
      · simp only [cond_false]
        exact ih₂ v P c fun k => by have := hc k; simp only [ops] at this; omega
      · simp only [cond_true]
        exact ih₁ v P c fun k => by have := hc k; simp only [ops] at this; omega
  | goto f => intro v P c _; rfl
  | halt => intro v P c _; rfl

end Agree

def stepI (M : FinTM2) (c : M.Cfg) : M.Cfg := (TM2.step M.m c).getD c

def runI (M : FinTM2) (c : M.Cfg) : ℕ → M.Cfg
  | 0 => c
  | t + 1 => stepI M (runI M c t)

def winC (M : FinTM2) (c : M.Cfg) : ∀ k, List (Option (M.Γ k)) :=
  fun k => window (depth M) (c.stk k)

theorem step_agree (M : FinTM2) (c : M.Cfg) :
    stepI M c = applyEff c.stk (sitStep M c.l c.var (winC M c)) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [stepI, TM2.step, sitStep, applyEff]; try rfl
  | some l =>
      simp only [stepI, TM2.step, Option.getD_some, sitStep]
      have := eff_agree (depth M) S (M.m l) v (fun _ => []) (fun _ => 0)
        (fun _ => by simpa using ops_le_depth M l)
      simp only [List.nil_append, List.drop_zero] at this
      exact this

namespace Enc

variable {M : FinTM2} (E : Enc M)

def code (c : M.Cfg) : ℕ := E.lc (c.l, c.var)

def cell (c : M.Cfg) (k j : ℕ) : ℕ := ((c.stk (E.kd k))[j]?).elim 0 (E.enc (E.kd k))

def sitIdx (c : M.Cfg) : ℕ :=
  mix E.g (E.code c) (E.KK * depth M) fun n => E.cell c (n / depth M) (n % depth M)

def tabRow (H i : ℕ) (old : ℕ → ℕ → ℕ) (k j : ℕ) : ℕ :=
  if j < E.pl i k then E.pu i k j
  else if j < H - max (E.pl i k) (E.cn i k) + E.pl i k then old k (j - E.pl i k + E.cn i k)
  else 0

def Good (c : M.Cfg) : Prop := ∀ k, ∀ x ∈ c.stk k, ∃ n, E.dec k n = x

theorem cell_kc (c : M.Cfg) (k : M.K) (j : ℕ) :
    E.cell c (E.kc k) j = ((c.stk k)[j]?).elim 0 (E.enc k) := by
  unfold cell; rw [E.kd_kc]

theorem decO_zero (k : M.K) : E.decO k 0 = none := by
  unfold decO; rw [dif_neg (by omega)]

theorem decO_cell (c : M.Cfg) (hc : E.Good c) (k : M.K) (j : ℕ) :
    E.decO k (((c.stk k)[j]?).elim 0 (E.enc k)) = (c.stk k)[j]? := by
  rcases h : (c.stk k)[j]? with _ | x
  · exact E.decO_zero k
  · obtain ⟨n, rfl⟩ := hc k x (List.mem_of_getElem? h)
    simp only [Option.elim_some, E.enc_dec]
    exact E.decO_succ k n

theorem cell_lt (c : M.Cfg) (hc : E.Good c) (k j : ℕ) : E.cell c k j < E.g := by
  unfold cell
  rcases h : (c.stk (E.kd k))[j]? with _ | x
  · exact E.g_pos
  · obtain ⟨n, rfl⟩ := hc _ x (List.mem_of_getElem? h)
    simp only [Option.elim_some, E.enc_dec]
    have := n.2; have := E.sz_lt_g (E.kd k); omega

theorem sitIdx_spec (c : M.Cfg) (hc : E.Good c) :
    E.sitIdx c < E.N ∧ E.la (E.sitIdx c) = E.code c ∧
      ∀ k < E.KK, ∀ j < depth M, E.wa (E.sitIdx c) k j = E.cell c k j :=
  E.mix_sit _ (E.lc_lt _) _ fun k _ j _ => E.cell_lt c hc k j

theorem win_sitIdx (c : M.Cfg) (hc : E.Good c) : E.win (E.sitIdx c) = winC M c := by
  funext k
  unfold win winC window
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  rw [(E.sitIdx_spec c hc).2.2 _ (E.kc_lt k) j hj, E.cell_kc, E.decO_cell c hc]

theorem res_sitIdx (c : M.Cfg) (hc : E.Good c) :
    E.res (E.sitIdx c) = sitStep M c.l c.var (winC M c) := by
  unfold res
  rw [(E.sitIdx_spec c hc).2.1, code, E.ld_lc, E.win_sitIdx c hc]

theorem row_cell {α : Type} (e : α → ℕ) (P S : List α) (n H d j : ℕ) (hP : P.length ≤ d)
    (hn : n ≤ d) (hS : S.length ≤ H - d) :
    ((P ++ S.drop n)[j]?).elim 0 e =
      if j < P.length then (P[j]?).elim 0 e
      else if j < H - max P.length n + P.length then (S[j - P.length + n]?).elim 0 e
      else 0 := by
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop, Nat.add_comm]
  · have hm : max P.length n ≤ d := max_le hP hn
    rw [List.getElem?_eq_none]
    · rfl
    · simp only [List.length_append, List.length_drop]; omega

theorem table_agree (H : ℕ) (c : M.Cfg) (hc : E.Good c)
    (hh : ∀ k, (c.stk k).length ≤ H - depth M) :
    E.code (stepI M c) = E.na (E.sitIdx c) ∧
      ∀ k < E.KK, ∀ j < H, E.cell (stepI M c) k j = E.tabRow H (E.sitIdx c) (E.cell c) k j := by
  have hr := E.res_sitIdx c hc
  have hs := step_agree M c
  refine ⟨?_, fun k _ j _ => ?_⟩
  · rw [hs]; simp only [code, na, hr]; try rfl
  · have hpl := E.pl_le (E.sitIdx c) k
    have hcn := E.cn_le (E.sitIdx c) k
    unfold pl at hpl; unfold cn at hcn
    rw [hr] at hpl hcn
    unfold tabRow pl cn pu cell
    rw [hr, hs]
    exact row_cell _ _ _ _ H (depth M) j hpl hcn (hh _)

theorem good_step (c : M.Cfg) (hc : E.Good c) : E.Good (stepI M c) := by
  rw [step_agree]
  intro k x hx
  simp only [applyEff, List.mem_append] at hx
  rcases hx with hx | hx
  · unfold sitStep at hx
    split at hx
    · simp at hx
    · next l _ =>
      exact eff_pushed (winC M c) (fun k x => ∃ n, E.dec k n = x) (M.m l)
        (fun k x h => E.push_mem l k x h) _ _ _ (fun _ _ h => by simp at h) k x hx
  · exact hc k x (List.mem_of_mem_drop hx)

theorem good_init (s : List (M.Γ M.k₀)) : E.Good (initList M s) := by
  intro k x hx
  by_cases hk : k = M.k₀
  · subst hk
    simp only [initList, dif_pos] at hx
    exact E.input_mem x
  · simp [initList, hk] at hx

theorem run_good (s : List (M.Γ M.k₀)) : ∀ t, E.Good (runI M (initList M s) t)
  | 0 => E.good_init s
  | t + 1 => E.good_step _ (run_good s t)

theorem table_agree_run (H : ℕ) (s : List (M.Γ M.k₀)) (t : ℕ)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    let c := runI M (initList M s) t
    E.sitIdx c < E.N ∧ E.la (E.sitIdx c) = E.code c ∧
      (∀ k < E.KK, ∀ j < depth M, E.wa (E.sitIdx c) k j = E.cell c k j) ∧
      E.code (runI M (initList M s) (t + 1)) = E.na (E.sitIdx c) ∧
      ∀ k < E.KK, ∀ j < H,
        E.cell (runI M (initList M s) (t + 1)) k j = E.tabRow H (E.sitIdx c) (E.cell c) k j :=
  ⟨(E.sitIdx_spec _ (E.run_good s t)).1, (E.sitIdx_spec _ (E.run_good s t)).2.1,
    (E.sitIdx_spec _ (E.run_good s t)).2.2, E.table_agree H _ (E.run_good s t) hh⟩

end Enc

section DecS

variable {α : Type}

end DecS

theorem stepI_height {M : FinTM2} (c : M.Cfg) (k : M.K) :
    ((stepI M c).stk k).length ≤ (c.stk k).length + depth M := by
  rw [step_agree]
  simp only [applyEff, List.length_append, List.length_drop]
  have : ((sitStep M c.l c.var (winC M c)).2.2.1 k).length ≤ depth M := by
    unfold sitStep
    split
    · simp
    · next l _ =>
      have := eff_bound (winC M c) (M.m l) c.var (fun _ => []) (fun _ => 0) k
      have := ops_le_depth M l
      simp only [List.length_nil] at *; omega
  omega

namespace Enc

variable {M : FinTM2} (E : Enc M)

end Enc

section C6

open Cslib.Complexity.DenseSAT

def Tr (a : List Bool) (v : ℕ) : Prop := a[v]? = some true

theorem mem_of_lookup {p : ℕ} {b : Bool} :
    ∀ {ls : List (ℕ × Bool)}, ls.lookup p = some b → (p, b) ∈ ls
  | [], h => by simp at h
  | (q, c) :: r, h => by
    by_cases hq : p = q
    · subst hq
      simp at h
      simp [h]
    · rw [Family.lookup_cons_ne hq] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem clauseSat_dense {V : ℕ} {ls : List (ℕ × Bool)} {a : List Bool}
    (h : clauseSat (Family.denseClause V ls) a) : ∃ p b, (p, b) ∈ ls ∧ a[p]? = some b := by
  obtain ⟨j, b, hc, ha⟩ := h
  unfold Family.denseClause at hc
  have hj : j < V := by
    by_contra hj
    rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)] at hc
    simp at hc
  rw [List.getElem?_map, List.getElem?_range hj] at hc
  simp only [Option.map_some, Option.some.injEq] at hc
  exact ⟨j, b, mem_of_lookup hc, ha⟩

theorem sh_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k u x : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK)
    (hu : u < H - max (pl i k) (cn i k)) (hx : x < L.g)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) (hC : Tr a (L.cIdx H t k (u + cn i k) x)) :
    Tr a (L.cIdx H (t + 1) k (u + pl i k) x) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.shLits L sa pl cn H t i k u x) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u,
        List.mem_range.2 hu,
      List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩⟩))
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.shLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS hC ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hC] at hab; simp at hab
  · rw [hS] at hab; simp at hab
  · exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

def CellsHold (a : List Bool) (H t : ℕ) (w : ℕ → ℕ → ℕ) : Prop :=
  ∀ k < E.KK, ∀ j < H, Tr a (E.layout.cIdx H t k j (w k j))

theorem sh_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hrow : E.CellsHold a H t (E.cell c))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j =
      E.cell c k (j - E.pl (E.sitIdx c) k + E.cn (E.sitIdx c) k) := by
    unfold tabRow; rw [if_neg (by omega), if_pos hj2]
  have hu : j - E.pl (E.sitIdx c) k < H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) := by
    omega
  have := sh_force ha ht (E.sitIdx_spec c hc).1 hk hu (E.cell_lt c hc k _) hS
    (hrow k hk _ (by omega))
  rwa [Nat.sub_add_cancel hj1, ← htab] at this

theorem sh_step_run_pos {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t)))
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj1 : E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j)
    (hj2 : j < H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) + E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.sh_hold ha ht _ (E.run_good s t) hrow hS hk hj1 hj2

end Enc

theorem fam_force {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    {a : List Bool} (ha : cnfSat (Family.family L la na wa T H N) a) {t i : ℕ} (ht : t < T)
    (hi : i < N) (hX : Tr a (L.xIdx H t (la i)))
    (hW : ∀ n < L.KK * L.d, Tr a (L.cIdx H t (n / L.d) (n % L.d) (wa i (n / L.d) (n % L.d)))) :
    Tr a (L.xIdx H (t + 1) (na i)) := by
  have hm : Family.denseClause (L.numVars T H) (Family.lits L la na wa H t i) ∈
      Family.family L la na wa T H N :=
    List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  unfold Family.lits at hp
  obtain ⟨j, hj, hjp⟩ := List.mem_map.1 hp
  rw [List.mem_range] at hj
  simp only [Prod.mk.injEq] at hjp
  obtain ⟨rfl, rfl⟩ := hjp
  have hn : L.nLits - 1 = L.KK * L.d + 1 := by unfold Family.Layout.nLits; omega
  have hj2 : j < L.KK * L.d + 2 := hj
  unfold Tr at hX hW ⊢
  by_cases h0 : j = 0
  · subst h0
    simp only [Family.litPos, if_true] at hab
    rw [hX] at hab
    simp [hn] at hab
  · by_cases h1 : j ≤ L.KK * L.d
    · simp only [Family.litPos, if_neg h0, if_pos h1] at hab
      rw [hW (j - 1) (by omega)] at hab
      have : j ≠ L.nLits - 1 := by omega
      simp [this] at hab
    · have hj' : j = L.KK * L.d + 1 := by omega
      simp only [Family.litPos, if_neg h0, if_neg h1] at hab
      rw [hj', hn] at hab
      simpa using hab

theorem fam_force_kj {L : Family.Layout} {la na : ℕ → ℕ} {wa : ℕ → ℕ → ℕ → ℕ} {N T H : ℕ}
    {a : List Bool} (ha : cnfSat (Family.family L la na wa T H N) a) {t i : ℕ} (ht : t < T)
    (hi : i < N) (hX : Tr a (L.xIdx H t (la i)))
    (hW : ∀ k < L.KK, ∀ j < L.d, Tr a (L.cIdx H t k j (wa i k j))) :
    Tr a (L.xIdx H (t + 1) (na i)) :=
  fam_force ha ht hi hX fun n hn =>
    hW _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hn; exact hn)) _
      (Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp [h] at hn))

namespace Enc

variable {M : FinTM2} (E : Enc M)

def CodeHolds (a : List Bool) (H t : ℕ) (c : M.Cfg) : Prop :=
  Tr a (E.layout.xIdx H t (E.code c))

theorem sd_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t c) (hrow : E.CellsHold a H t (E.cell c)) :
    Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))) := by
  obtain ⟨hi, hla, hwa⟩ := E.sitIdx_spec c hc
  refine fam_force_kj ha ht hi ?_ fun k hk j hj => ?_
  · rw [hla]; exact hcode
  · rw [hwa k hk j hj]; exact hrow k hk j (lt_of_lt_of_le hj hdH)

theorem sd_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a) (ht : t < T)
    (hdH : depth M ≤ H) (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))) :=
  E.sd_hold ha ht _ (E.run_good s t) hdH hcode hrow

end Enc

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem upd_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t c) (hrow : E.CellsHold a H t (E.cell c)) :
    Tr a (E.layout.xIdx H (t + 1) (E.na (E.sitIdx c))) := by
  obtain ⟨hi, hla, hwa⟩ := E.sitIdx_spec c hc
  refine fam_force_kj ha ht hi ?_ fun k hk j hj => ?_
  · rw [hla]; exact hcode
  · rw [hwa k hk j hj]; exact hrow k hk j (lt_of_lt_of_le hj hdH)

theorem upd_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a H (t + 1) (runI M (initList M s) (t + 1)) := by
  have h := E.upd_hold ha ht _ (E.run_good s t) hdH hcode hrow
  unfold CodeHolds
  rw [(E.table_agree_run H s t hh).2.2.2.1]
  exact h

end Enc

theorem pf_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k j : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK) (hj : j < pl i k)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) : Tr a (L.cIdx H (t + 1) k j (pu i k j)) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.pfLits L sa pu H t i k j) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.pfLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hS] at hab; simp at hab
  · exact hab

theorem ov_force {L : Family.Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ}
    {N T H : ℕ} {a : List Bool} (ha : cnfSat (Shift.shFamily L sa pl cn pu N T H) a)
    {t i k r : ℕ} (ht : t < T) (hi : i < N) (hk : k < L.KK) (hr : r < cn i k - pl i k)
    (hS : Tr a (L.xIdx H (t + 1) (sa i))) :
    Tr a (L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0) := by
  have hm : Family.denseClause (L.numVars T H) (Shift.ovLits L sa pl cn H t i k r) ∈
      Shift.shFamily L sa pl cn pu N T H := by
    refine List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩⟩⟩
    unfold Shift.shBlk
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2
      ⟨r, List.mem_range.2 hr, rfl⟩))
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (ha _ hm)
  simp only [Shift.ovLits, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  unfold Tr at hS ⊢
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hS] at hab; simp at hab
  · exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem pf_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK) (hj : j < E.pl (E.sitIdx c) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j = E.pu (E.sitIdx c) k j := by
    unfold tabRow; rw [if_pos hj]
  rw [htab]
  exact pf_force ha ht (E.sitIdx_spec c hc).1 hk hj hS

theorem ov_hold {T H t : ℕ} {a : List Bool}
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (c : M.Cfg) (hc : E.Good c) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx c))))
    {k j : ℕ} (hk : k < E.KK)
    (hj1 : H - max (E.pl (E.sitIdx c) k) (E.cn (E.sitIdx c) k) + E.pl (E.sitIdx c) k ≤ j)
    (hj2 : j < H) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.tabRow H (E.sitIdx c) (E.cell c) k j)) := by
  have hp := E.pl_le (E.sitIdx c) k
  have hq := E.cn_le (E.sitIdx c) k
  have htab : E.tabRow H (E.sitIdx c) (E.cell c) k j = 0 := by
    unfold tabRow; rw [if_neg (by omega), if_neg (by omega)]
  rw [htab]
  have := ov_force ha ht (E.sitIdx_spec c hc).1 hk
    (r := j - (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k)) (by omega) hS
  rwa [show H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k +
    (j - (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k)) = j by omega] at this

theorem pf_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK) (hj : j < E.pl (E.sitIdx (runI M (initList M s) t)) k) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  have := E.pl_le (E.sitIdx (runI M (initList M s) t)) k
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j (by omega)]
  exact E.pf_hold ha ht _ (E.run_good s t) hS hk hj

theorem ov_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hS : Tr a (E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))))
    {k j : ℕ} (hk : k < E.KK)
    (hj1 : H - max (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) +
      E.pl (E.sitIdx (runI M (initList M s) t)) k ≤ j) (hj2 : j < H) :
    Tr a (E.layout.cIdx H (t + 1) k j (E.cell (runI M (initList M s) (t + 1)) k j)) := by
  rw [(E.table_agree_run H s t hh).2.2.2.2 k hk j hj2]
  exact E.ov_hold ha ht _ (E.run_good s t) hdH hS hk hj1 hj2

end Enc

def capH (m T d : ℕ) : ℕ := m + (T + 1) * d + 1

theorem runI_height {M : FinTM2} (c : M.Cfg) (k : M.K) :
    ∀ t, ((runI M c t).stk k).length ≤ (c.stk k).length + t * depth M
  | 0 => by simp [runI]
  | t + 1 => by
    have h1 := stepI_height (runI M c t) k
    have h2 := runI_height c k t
    have h3 : (t + 1) * depth M = t * depth M + depth M := Nat.succ_mul _ _
    change ((stepI M (runI M c t)).stk k).length ≤ _
    omega

theorem initList_height {M : FinTM2} (s : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M s).stk k).length ≤ s.length := by
  by_cases hk : k = M.k₀
  · subst hk; simp [initList]
  · simp [initList, hk]

theorem capH_height {M : FinTM2} {m T t : ℕ} (s : List (M.Γ M.k₀)) (hs : s.length ≤ m)
    (ht : t ≤ T) (k : M.K) :
    ((runI M (initList M s) t).stk k).length ≤ capH m T (depth M) - depth M := by
  have h1 := runI_height (initList M s) k t
  have h2 := initList_height s k
  have h3 : t * depth M ≤ T * depth M := Nat.mul_le_mul_right _ ht
  have h4 : (T + 1) * depth M = T * depth M + depth M := Nat.succ_mul _ _
  unfold capH; omega

theorem depth_le_capH (M : FinTM2) (m T : ℕ) : depth M ≤ capH m T (depth M) := by
  have h4 : (T + 1) * depth M = T * depth M + depth M := Nat.succ_mul _ _
  unfold capH; omega

theorem region_cover (p q H j : ℕ) (hj : j < H) :
    (j < p ∨ (p ≤ j ∧ j < H - max p q + p) ∨ (H - max p q + p ≤ j ∧ j < H)) ∧
    ¬ (j < p ∧ p ≤ j) ∧ ¬ (j < p ∧ H - max p q + p ≤ j) ∧
    ¬ (j < H - max p q + p ∧ H - max p q + p ≤ j) := by
  omega

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem cells_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CellsHold a H (t + 1) (E.cell (runI M (initList M s) (t + 1))) := by
  have hS := E.sd_step_run s hs ht hdH hcode hrow
  intro k hk j hj
  rcases (region_cover (E.pl (E.sitIdx (runI M (initList M s) t)) k)
      (E.cn (E.sitIdx (runI M (initList M s) t)) k) H j hj).1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact E.pf_step_run s ha ht hh hdH hS hk h
  · exact E.sh_step_run_pos s ha ht hh hrow hS hk h1 h2
  · exact E.ov_step_run s ha ht hh hdH hS hk h1 h2

theorem row_step_run {T H t : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a) (ht : t < T)
    (hh : ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) (hdH : depth M ≤ H)
    (hcode : E.CodeHolds a H t (runI M (initList M s) t))
    (hrow : E.CellsHold a H t (E.cell (runI M (initList M s) t))) :
    E.CodeHolds a H (t + 1) (runI M (initList M s) (t + 1)) ∧
      E.CellsHold a H (t + 1) (E.cell (runI M (initList M s) (t + 1))) :=
  ⟨E.upd_step_run s hu ht hh hdH hcode hrow, E.cells_step_run s hs ha ht hh hdH hcode hrow⟩

end Enc

namespace Enc

variable {M : FinTM2} (E : Enc M)

def Row0 (a : List Bool) (H : ℕ) (s : List (M.Γ M.k₀)) : Prop :=
  E.CodeHolds a H 0 (initList M s) ∧ E.CellsHold a H 0 (E.cell (initList M s))

def InitObl (a : List Bool) (x Ys : List (M.Γ M.k₀)) (m T : ℕ) : Prop :=
  ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
    E.Row0 a (capH m T (depth M)) (x ++ y)

theorem rows_run {T H : ℕ} {a : List Bool} (s : List (M.Γ M.k₀))
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) a)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M)
    (hdH : depth M ≤ H) (h0 : E.Row0 a H s) :
    ∀ t ≤ T, E.CodeHolds a H t (runI M (initList M s) t) ∧
      E.CellsHold a H t (E.cell (runI M (initList M s) t)) := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ t ih =>
    intro ht
    have hlt : t < T := Nat.lt_of_succ_le ht
    obtain ⟨hc, hr⟩ := ih hlt.le
    exact E.row_step_run s hu hs ha hlt (hh t hlt) hdH hc hr

theorem rows_capH {m T : ℕ} {a : List Bool} (s : List (M.Γ M.k₀)) (hsm : s.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (h0 : E.Row0 a (capH m T (depth M)) s) :
    ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M s) t) ∧
      E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M s) t)) :=
  E.rows_run s hu hs ha (fun _ ht k => capH_height s hsm ht.le k) (depth_le_capH M m T) h0

theorem rows_of_init {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool}
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : E.InitObl a x Ys m T) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M (x ++ y)) t) ∧
        E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M (x ++ y)) t)) := by
  obtain ⟨y, hy, hsm, h0⟩ := hI
  exact ⟨y, hy, hsm, E.rows_capH (x ++ y) hsm hu hs ha h0⟩

end Enc

theorem cnfSat_append {φ ψ : CNF} {a : List Bool} : cnfSat (φ ++ ψ) a ↔ cnfSat φ a ∧ cnfSat ψ a := by
  simp only [cnfSat, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

theorem unit_force {V v : ℕ} {φ : CNF} {a : List Bool} (h : cnfSat φ a)
    (hm : Family.denseClause V [(v, true)] ∈ φ) : Tr a v := by
  obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (h _ hm)
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact hab

namespace Enc

variable {M : FinTM2} (E : Enc M)

def zIdx (H j : ℕ) : ℕ := E.layout.cIdx H 0 (E.kc M.k₀) j 0

def initCode (T H : ℕ) : CNF :=
  [Family.denseClause (E.layout.numVars T H) [(E.layout.xIdx H 0 (E.lc (some M.main,
      M.initialState)), true)]]

def initOther (T H : ℕ) : CNF :=
  ((List.range E.KK).filter (· ≠ E.kc M.k₀)).flatMap fun k =>
    (List.range H).map fun j => Family.denseClause (E.layout.numVars T H) [(E.layout.cIdx H 0 k j 0, true)]

def initIn (x : List (M.Γ M.k₀)) (T H : ℕ) : CNF :=
  (List.range x.length).map fun j => Family.denseClause (E.layout.numVars T H)
    [(E.layout.cIdx H 0 (E.kc M.k₀) j ((x[j]?).elim 0 (E.enc M.k₀)), true)]

def initCert (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  (List.range (m - x.length)).map fun i => Family.denseClause (E.layout.numVars T H)
    ((E.zIdx H (x.length + i), true) ::
      Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true))

def initPre (x : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  (List.range (m - x.length)).map fun i => Family.denseClause (E.layout.numVars T H)
    [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1), true)]

def initTail (m T H : ℕ) : CNF :=
  (List.range (H - m)).map fun i => Family.denseClause (E.layout.numVars T H) [(E.zIdx H (m + i),
      true)]

def initFamily (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) : CNF :=
  E.initCode T H ++ E.initOther T H ++ E.initIn x T H ++ E.initCert x Ys m T H ++
    E.initPre x m T H ++ E.initTail m T H

theorem initList_k₀ (s : List (M.Γ M.k₀)) : (initList M s).stk M.k₀ = s := by
  simp [initList]

theorem initList_ne (s : List (M.Γ M.k₀)) (k : M.K) (hk : k ≠ M.k₀) : (initList M s).stk k = [] := by
  simp [initList, hk]

theorem init_row0 {x Ys : List (M.Γ M.k₀)} {m T H : ℕ} {a : List Bool}
    (hx : x.length ≤ m) (hmH : m < H) (hI : cnfSat (E.initFamily x Ys m T H) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧ E.Row0 a H (x ++ y) := by
  simp only [initFamily, cnfSat_append] at hI
  obtain ⟨⟨⟨⟨⟨hC, hO⟩, hIn⟩, hCe⟩, hP⟩, hTl⟩ := hI

  have tail : ∀ j, m ≤ j → j < H → Tr a (E.zIdx H j) := fun j h1 h2 => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    exact unit_force hTl (List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩)
  have pre : ∀ j, x.length ≤ j → j < m → Tr a (E.zIdx H j) → Tr a (E.zIdx H (j + 1)) := by
    intro j h1 h2 hz
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    have hm : Family.denseClause (E.layout.numVars T H)
        [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1),
            true)] ∈ E.initPre x m T H :=
      List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
    obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (hP _ hm)
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
    unfold Tr at hz ⊢
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hz] at hab; simp at hab
    · exact hab
  have cert : ∀ j, x.length ≤ j → j < m → ¬ Tr a (E.zIdx H j) →
      ∃ z, z ∈ Ys ∧ Tr a (E.layout.cIdx H 0 (E.kc M.k₀) j (E.enc M.k₀ z)) := by
    intro j h1 h2 hz
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
    have hm : Family.denseClause (E.layout.numVars T H) ((E.zIdx H (x.length + i), true) ::
        Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true)) ∈
        E.initCert x Ys m T H :=
      List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
    obtain ⟨p, b, hp, hab⟩ := clauseSat_dense (hCe _ hm)
    rcases List.mem_cons.1 hp with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact absurd hab hz
    · obtain ⟨z, hz, he⟩ := List.mem_map.1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨z, hz, hab⟩

  have hex : ∃ j, x.length ≤ j ∧ Tr a (E.zIdx H j) := ⟨m, hx, tail m le_rfl hmH⟩
  classical
  let ℓ := Nat.find hex
  have hxℓ : x.length ≤ ℓ := (Nat.find_spec hex).1
  have hℓm : ℓ ≤ m := Nat.find_min' hex ⟨hx, tail m le_rfl hmH⟩
  have zall : ∀ j, ℓ ≤ j → j < H → Tr a (E.zIdx H j) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ => (Nat.find_spec hex).2
    | succ j hj ih =>
      intro hjH
      by_cases hjm : j < m
      · exact pre j (by omega) hjm (ih (by omega))
      · exact tail _ (by omega) hjH
  have free : ∀ i, i < ℓ - x.length →
      ∃ z, z ∈ Ys ∧ Tr a (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z)) :=
    fun i hi => cert _ (by omega) (by omega) fun hz =>
      Nat.find_min hex (show x.length + i < ℓ by omega) ⟨by omega, hz⟩
  let y : List (M.Γ M.k₀) := List.ofFn fun i : Fin (ℓ - x.length) => Classical.choose (free i i.2)
  have hyl : y.length = ℓ - x.length := List.length_ofFn
  refine ⟨y, fun z hz => ?_, by rw [List.length_append, hyl]; omega, ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    exact (Classical.choose_spec (free i i.2)).1
  · exact unit_force hC (List.mem_singleton.2 rfl)
  · intro k hk j hj
    by_cases hk0 : k = E.kc M.k₀
    · subst hk0
      rw [E.cell_kc, initList_k₀]
      by_cases hjx : j < x.length
      · rw [List.getElem?_append_left hjx]
        exact unit_force hIn (List.mem_map.2 ⟨j, List.mem_range.2 hjx, rfl⟩)
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hjx)
        rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        by_cases hi : i < ℓ - x.length
        · rw [List.getElem?_ofFn, dif_pos hi]
          exact (Classical.choose_spec (free i hi)).2
        · rw [List.getElem?_eq_none (by omega)]
          exact zall _ (by omega) hj
    · have hne : E.kd k ≠ M.k₀ := fun h => hk0 (by rw [← h, E.kc_kd k hk])
      unfold cell
      rw [initList_ne _ _ hne]
      exact unit_force hO (List.mem_flatMap.2 ⟨k, List.mem_filter.2 ⟨List.mem_range.2 hk,
        by simpa using hk0⟩, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)

theorem init_obl {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool} (hx : x.length ≤ m)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a) : E.InitObl a x Ys m T :=
  E.init_row0 hx (by unfold capH; omega) hI

theorem rows_of_initFamily {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {a : List Bool} (hx : x.length ≤ m)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      ∀ t ≤ T, E.CodeHolds a (capH m T (depth M)) t (runI M (initList M (x ++ y)) t) ∧
        E.CellsHold a (capH m T (depth M)) t (E.cell (runI M (initList M (x ++ y)) t)) :=
  E.rows_of_init hu hs ha (E.init_obl hx hI)

end Enc

def Faithful (V : ℕ) (ls : List (ℕ × Bool)) : Prop :=
  ∀ p b, (p, b) ∈ ls → p < V ∧ ls.lookup p = some b

theorem clauseSat_iff {V : ℕ} {ls : List (ℕ × Bool)} {a : List Bool} (h : Faithful V ls) :
    clauseSat (Family.denseClause V ls) a ↔ ∃ p b, (p, b) ∈ ls ∧ a[p]? = some b := by
  refine ⟨clauseSat_dense, fun ⟨p, b, hp, ha⟩ => ⟨p, b, ?_, ha⟩⟩
  obtain ⟨hV, hl⟩ := h p b hp
  unfold Family.denseClause
  rw [List.getElem?_map, List.getElem?_range hV]
  simp [hl]

theorem lookup_of_mem {p : ℕ} {b : Bool} :
    ∀ {ls : List (ℕ × Bool)}, (p, b) ∈ ls → ∃ b', ls.lookup p = some b'
  | [], h => by simp at h
  | (q, c) :: r, h => by
    by_cases hq : p = q
    · subst hq; exact ⟨c, by simp⟩
    · rw [Family.lookup_cons_ne hq]
      rcases List.mem_cons.1 h with h | h
      · exact absurd (Prod.mk.inj h).1 hq
      · exact lookup_of_mem h

theorem faithful_of_pol {V : ℕ} {ls : List (ℕ × Bool)} (hV : ∀ p b, (p, b) ∈ ls → p < V)
    (hb : ∀ p b b', (p, b) ∈ ls → (p, b') ∈ ls → b = b') : Faithful V ls := by
  intro p b hp
  obtain ⟨b', hl⟩ := lookup_of_mem hp
  exact ⟨hV p b hp, by rw [hl, hb p b' b (mem_of_lookup hl) hp]⟩

theorem faithful_pos {V : ℕ} {ls : List (ℕ × Bool)} (h : ∀ p b, (p, b) ∈ ls → p < V ∧ b = true) :
    Faithful V ls :=
  faithful_of_pol (fun p b hp => (h p b hp).1) fun p b b' hp hp' => by
    rw [(h p b hp).2, (h p b' hp').2]

theorem faithful_single {V p : ℕ} {b : Bool} (h : p < V) : Faithful V [(p, b)] := by
  intro q c hq
  simp only [List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  exact ⟨h, by simp⟩

theorem Inc.ge : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Family.Inc lo ls V →
    ∀ p b, (p, b) ∈ ls → lo ≤ p
  | _, [], _, _, _, _, h => by simp at h
  | _, (q, _) :: _, _, ⟨h1, h2⟩, p, b, h => by
    rcases List.mem_cons.1 h with h | h
    · rw [(Prod.mk.inj h).1]; exact h1
    · have := Inc.ge h2 p b h; omega

theorem faithful_of_inc : ∀ {lo : ℕ} {ls : List (ℕ × Bool)} {V : ℕ}, Family.Inc lo ls V →
    Faithful V ls
  | _, [], _, _, _, _, h => by simp at h
  | _, (q, c) :: r, _, ⟨h1, h2⟩, p, b, h => by
    have hV := Family.Inc.le h2
    rcases List.mem_cons.1 h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨by omega, by simp⟩
    · have hq := Inc.ge h2 p b h
      obtain ⟨hp, hl⟩ := faithful_of_inc h2 p b h
      exact ⟨hp, by rw [Family.lookup_cons_ne (by omega)]; exact hl⟩

theorem lt_numVars {L : Family.Layout} {T H t p : ℕ} (ht : t ≤ T) (hp : p < (t + 1) * L.rowW H) :
    p < L.numVars T H :=
  lt_of_lt_of_le hp (Nat.mul_le_mul_right _ (by omega))

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem enc_lt (k : M.K) (z : M.Γ k) (h : ∃ i, E.dec k i = z) : E.enc k z < E.g := by
  obtain ⟨i, rfl⟩ := h
  rw [E.enc_dec]; have := E.sz_lt_g k; omega

theorem xIdx_lt {T H t u : ℕ} (ht : t ≤ T) (hu : u < E.A0) :
    E.layout.xIdx H t u < E.layout.numVars T H := by
  refine lt_numVars ht ?_
  unfold Family.Layout.xIdx Family.Layout.rowW
  rw [Nat.succ_mul]
  have : E.layout.A = E.A0 + E.N := rfl
  omega

theorem cIdx_lt {T H t k j x : ℕ} (ht : t ≤ T) (hk : k < E.KK) (hj : j < H) (hx : x < E.g) :
    E.layout.cIdx H t k j x < E.layout.numVars T H :=
  lt_numVars ht (Family.cIdx_lt_next_row (L := E.layout) hk hj hx)

def acode : ℕ := E.lc (none, M.initialState)

def accCode (T H : ℕ) : CNF :=
  (List.range E.A0).map fun u => Family.denseClause (E.layout.numVars T H)
    [(E.layout.xIdx H T u, decide (u = E.acode))]

def accCell (acc : M.Γ M.k₁) (T H : ℕ) : CNF :=
  (List.range E.g).map fun x => Family.denseClause (E.layout.numVars T H)
    [(E.layout.cIdx H T (E.kc M.k₁) 0 x, decide (x = E.enc M.k₁ acc))]

def accFamily (acc : M.Γ M.k₁) (T H : ℕ) : CNF := E.accCode T H ++ E.accCell acc T H

theorem unit_pol {V p : ℕ} {b : Bool} {φ : CNF} {a : List Bool} (h : cnfSat φ a)
    (hm : Family.denseClause V [(p, b)] ∈ φ) (ht : Tr a p) : b = true := by
  obtain ⟨q, c, hq, hab⟩ := clauseSat_dense (h _ hm)
  simp only [List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  unfold Tr at ht
  rw [ht] at hab
  exact (Option.some.inj hab).symm

theorem acc_code {acc : M.Γ M.k₁} {T H u : ℕ} {a : List Bool} (h : cnfSat (E.accFamily acc T H) a)
    (hu : u < E.A0) (ht : Tr a (E.layout.xIdx H T u)) : u = E.acode :=
  of_decide_eq_true (unit_pol h (List.mem_append_left _ (List.mem_map.2 ⟨u, List.mem_range.2 hu,
      rfl⟩)) ht)

theorem acc_cell {acc : M.Γ M.k₁} {T H x : ℕ} {a : List Bool} (h : cnfSat (E.accFamily acc T H) a)
    (hx : x < E.g) (ht : Tr a (E.layout.cIdx H T (E.kc M.k₁) 0 x)) : x = E.enc M.k₁ acc :=
  of_decide_eq_true (unit_pol h (List.mem_append_right _ (List.mem_map.2 ⟨x, List.mem_range.2 hx,
      rfl⟩)) ht)

end Enc

def Accepts (M : FinTM2) (c : M.Cfg) (acc : M.Γ M.k₁) : Prop :=
  c.l = none ∧ c.var = M.initialState ∧ (c.stk M.k₁).head? = some acc

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem accept_sound {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁} {a : List Bool}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc)
    (hu : cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a)
    (hs : cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a)
    (ha : cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a)
    (hI : cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a)
    (hA : cnfSat (E.accFamily acc T (capH m T (depth M))) a) :
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc := by
  obtain ⟨y, hy, hl, hrow⟩ := E.rows_of_initFamily hx hu hs ha hI
  obtain ⟨hc, hr⟩ := hrow T le_rfl
  refine ⟨y, hy, hl, ?_⟩
  have hgood := E.run_good (x ++ y) T
  generalize runI M (initList M (x ++ y)) T = c at hc hr hgood
  have h1 : E.code c = E.acode := E.acc_code hA (E.lc_lt _) hc
  have h2 : (c.l, c.var) = ((none : Option M.Λ), M.initialState) := by
    have := congrArg E.ld h1
    simpa only [code, acode, E.ld_lc] using this
  obtain ⟨h2l, h2v⟩ := Prod.mk.inj h2
  have hH : 0 < capH m T (depth M) := by unfold capH; omega
  have h3 := E.acc_cell hA (E.cell_lt c hgood _ _) (hr _ (E.kc_lt M.k₁) 0 hH)
  rw [E.cell_kc] at h3
  obtain ⟨i, rfl⟩ := hacc
  refine ⟨h2l, h2v, ?_⟩
  rw [List.head?_eq_getElem?]
  cases hz : (c.stk M.k₁)[0]? with
  | none => rw [hz, E.enc_dec] at h3; simp at h3
  | some z =>
    rw [hz] at h3
    obtain ⟨n, rfl⟩ := hgood M.k₁ z (List.mem_of_getElem? hz)
    simp only [Option.elim, E.enc_dec, Nat.add_right_cancel_iff] at h3
    rw [Fin.ext h3]

end Enc

theorem runI_succ' (M : FinTM2) (c : M.Cfg) : ∀ n, runI M c (n + 1) = runI M (stepI M c) n
  | 0 => rfl
  | n + 1 => by rw [runI, runI_succ' M c n]; rfl

theorem iterate_bind_none {σ : Type} (f : σ → Option σ) : ∀ n, (flip bind f)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iterate_bind_none f n

theorem runI_of_iterate (M : FinTM2) : ∀ (n : ℕ) (c c' : M.Cfg),
    (flip bind (TM2.step M.m))^[n] (some c) = some c' → runI M c n = c'
  | 0, c, c', h => Option.some.inj h
  | n + 1, c, c', h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind (TM2.step M.m))^[n] (TM2.step M.m c) = some c' at h
    cases hs : TM2.step M.m c with
    | none => rw [hs, iterate_bind_none] at h; exact absurd h (by simp)
    | some c1 =>
      rw [hs] at h
      rw [runI_succ', show stepI M c = c1 by simp [stepI, hs]; try rfl]
      exact runI_of_iterate M n c1 c' h

theorem runI_add (M : FinTM2) (c : M.Cfg) (a : ℕ) : ∀ b, runI M c (a + b) = runI M (runI M c a) b
  | 0 => rfl
  | b + 1 => by
    change stepI M (runI M c (a + b)) = stepI M (runI M (runI M c a) b)
    rw [runI_add M c a b]

theorem runI_halted (M : FinTM2) (c : M.Cfg) (hc : c.l = none) : ∀ t, runI M c t = c
  | 0 => rfl
  | t + 1 => by
    rw [runI, runI_halted M c hc t]
    obtain ⟨l, v, S⟩ := c
    subst hc
    simp [stepI, TM2.step]; try rfl

theorem runI_haltList (M : FinTM2) (s : List (M.Γ M.k₀)) (l' : List (M.Γ M.k₁)) {p : ℕ}
    (h : TM2OutputsInTime M s (some l') p) {T : ℕ} (hT : p ≤ T) :
    runI M (initList M s) T = haltList M l' := by
  have h1 := runI_of_iterate M h.steps _ _ h.evals_in_steps
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (h.steps_le_m.trans hT)
  rw [runI_add, h1, runI_halted _ _ rfl]

theorem accepts_haltList (M : FinTM2) (l' : List (M.Γ M.k₁)) (acc : M.Γ M.k₁) :
    Accepts M (haltList M l') acc ↔ l'.head? = some acc := by
  simp [Accepts, haltList]

theorem row_pos_inj {W t t' r r' : ℕ} (hr : r < W) (hr' : r' < W)
    (h : t * W + r = t' * W + r') : t = t' ∧ r = r' := by
  have hW : 0 < W := by omega
  have e : ∀ t r, r < W → (t * W + r) / W = t := fun t r hr => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
  have ht : t = t' := by rw [← e t r hr, h, e t' r' hr']
  subst ht
  exact ⟨rfl, by omega⟩

section Inv

variable {L : Family.Layout}

theorem cIdx_split (H t k j x : ℕ) :
    L.cIdx H t k j x = t * L.rowW H + (L.A + ((k * H + j) * L.g + x)) := by
  unfold Family.Layout.cIdx; ring

theorem cell_off_lt {H k j x : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.A + ((k * H + j) * L.g + x) < L.rowW H := by
  have h1 : (k * H + j) * L.g + x < (k * H + j + 1) * L.g := by
    rw [Nat.add_one_mul]; omega
  have h2 : k * H + j + 1 ≤ L.KK * H := by
    have := Nat.mul_le_mul_right H (show k + 1 ≤ L.KK by omega)
    rw [Nat.add_one_mul] at this; omega
  have h3 := Nat.mul_le_mul_right L.g h2
  have e : L.KK * H * L.g = L.KK * (H * L.g) := by ring
  unfold Family.Layout.rowW; omega

theorem A_le_rowW (H : ℕ) : L.A ≤ L.rowW H := by unfold Family.Layout.rowW; omega

theorem xIdx_inj {H t t' u u' : ℕ} (hu : u < L.A) (hu' : u' < L.A)
    (h : L.xIdx H t u = L.xIdx H t' u') : t = t' ∧ u = u' :=
  row_pos_inj (lt_of_lt_of_le hu (A_le_rowW H)) (lt_of_lt_of_le hu' (A_le_rowW H)) h

theorem xIdx_ne_cIdx {H t t' u k j x : ℕ} (hu : u < L.A) (hk : k < L.KK) (hj : j < H) (hx : x < L.g) :
    L.xIdx H t u ≠ L.cIdx H t' k j x := by
  intro h
  rw [cIdx_split] at h
  have := (row_pos_inj (lt_of_lt_of_le hu (A_le_rowW H)) (cell_off_lt hk hj hx) h).2
  omega

theorem cIdx_inj {H t t' k k' j j' x x' : ℕ} (hk : k < L.KK) (hj : j < H) (hx : x < L.g)
    (hk' : k' < L.KK) (hj' : j' < H) (hx' : x' < L.g)
    (h : L.cIdx H t k j x = L.cIdx H t' k' j' x') : t = t' ∧ k = k' ∧ j = j' ∧ x = x' := by
  rw [cIdx_split, cIdx_split] at h
  obtain ⟨rfl, h⟩ := row_pos_inj (cell_off_lt hk hj hx) (cell_off_lt hk' hj' hx') h
  obtain ⟨h1, rfl⟩ := row_pos_inj (t := k * H + j) (t' := k' * H + j') hx hx' (by omega)
  obtain ⟨rfl, rfl⟩ := row_pos_inj hj hj' h1
  exact ⟨rfl, rfl, rfl, rfl⟩

end Inv

theorem mod_pow_eq_of_digits {b i i' : ℕ} : ∀ n, (∀ e < n, i / b ^ e % b = i' / b ^ e % b) →
    i % b ^ n = i' % b ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, mod_pow_eq_of_digits n fun e he => h e (by omega),
      h n (by omega)]

namespace Enc

variable {M : FinTM2} (E : Enc M)

theorem sit_inj (c : M.Cfg) (hc : E.Good c) {i : ℕ} (hi : i < E.N) (hl : E.la i = E.code c)
    (hw : ∀ k < E.KK, ∀ j < depth M, E.wa i k j = E.cell c k j) : i = E.sitIdx c := by
  obtain ⟨hN, hl', hw'⟩ := E.sitIdx_spec c hc
  set i' := E.sitIdx c
  have hG : 0 < E.G := pow_pos E.g_pos _
  have top : ∀ n, n < E.N → E.la n = n / E.G := fun n hn => by
    unfold la
    exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hG).2 hn)
  have hdig : ∀ e < E.KK * depth M, i / E.g ^ e % E.g = i' / E.g ^ e % E.g := by
    intro e he
    have hd : 0 < depth M := Nat.pos_of_ne_zero fun h => by simp [h] at he
    have hk : e / depth M < E.KK := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
    have hj : e % depth M < depth M := Nat.mod_lt _ hd
    have h1 := hw _ hk _ hj
    have h2 := hw' _ hk _ hj
    unfold wa at h1 h2
    rw [Nat.div_add_mod'] at h1 h2
    rw [h1, h2]
  have hmod := mod_pow_eq_of_digits (b := E.g) (i := i) (i' := i') _ hdig
  have hdiv : i / E.G = i' / E.G := by rw [← top i hi, ← top i' hN, hl, hl']
  rw [← Nat.mod_add_div i E.G, ← Nat.mod_add_div i' E.G]
  unfold G at hdiv ⊢
  rw [hmod, hdiv]

def RunLit (s : List (M.Γ M.k₀)) (H p : ℕ) : Prop :=
  ∃ t, p = E.layout.xIdx H t (E.code (runI M (initList M s) t)) ∨
    (∃ k < E.KK, ∃ j < H, p = E.layout.cIdx H t k j (E.cell (runI M (initList M s) t) k j)) ∨
    p = E.layout.xIdx H (t + 1) (E.sa (E.sitIdx (runI M (initList M s) t)))

open Classical in

noncomputable def runAsg (s : List (M.Γ M.k₀)) (T H : ℕ) : List Bool :=
  (List.range (E.layout.numVars T H)).map fun p => decide (E.RunLit s H p)

theorem runAsg_length (s : List (M.Γ M.k₀)) (T H : ℕ) :
    (E.runAsg s T H).length = E.layout.numVars T H := by
  simp [runAsg]

theorem runAsg_get {s : List (M.Γ M.k₀)} {T H p : ℕ} (hp : p < E.layout.numVars T H) (b : Bool)
    (hb : b = true ↔ E.RunLit s H p) : (E.runAsg s T H)[p]? = some b := by
  unfold runAsg
  rw [List.getElem?_map, List.getElem?_range hp]
  cases b <;> simp_all

theorem sat_run {s : List (M.Γ M.k₀)} {T H : ℕ} {ls : List (ℕ × Bool)}
    (hf : Faithful (E.layout.numVars T H) ls) {p : ℕ} {b : Bool} (hp : (p, b) ∈ ls)
    (hb : b = true ↔ E.RunLit s H p) :
    clauseSat (Family.denseClause (E.layout.numVars T H) ls) (E.runAsg s T H) :=
  (clauseSat_iff hf).2 ⟨p, b, hp, E.runAsg_get (hf p b hp).1 b hb⟩

theorem sa_lt {i : ℕ} (hi : i < E.N) : E.sa i < E.layout.A := by
  change E.A0 + i < E.A0 + E.N; omega

theorem code_lt (c : M.Cfg) : E.code c < E.layout.A := by
  have := E.lc_lt (c.l, c.var); show _ < E.A0 + E.N; unfold code; omega

theorem lit_x (s : List (M.Γ M.k₀)) {H t u : ℕ} (hu : u < E.A0) :
    E.RunLit s H (E.layout.xIdx H t u) ↔ u = E.code (runI M (initList M s) t) := by
  have hu' : u < E.layout.A := by show u < E.A0 + E.N; omega
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inl (by rw [h])⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k, hk, j, hj, h⟩ | h
  · obtain ⟨rfl, rfl⟩ := xIdx_inj hu' (E.code_lt _) h; rfl
  · exact absurd h (xIdx_ne_cIdx hu' hk hj (E.cell_lt _ hg k j))
  · have := (xIdx_inj hu' (E.sa_lt (E.sitIdx_spec _ hg).1) h).2
    unfold sa at this; omega

theorem lit_c (s : List (M.Γ M.k₀)) {H t k j x : ℕ} (hk : k < E.KK) (hj : j < H) (hx : x < E.g) :
    E.RunLit s H (E.layout.cIdx H t k j x) ↔ x = E.cell (runI M (initList M s) t) k j := by
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inr (Or.inl ⟨k, hk, j, hj, by rw [h]⟩)⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k', hk', j', hj', h⟩ | h
  · exact absurd h.symm (xIdx_ne_cIdx (E.code_lt _) hk hj hx)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := cIdx_inj hk hj hx hk' hj' (E.cell_lt _ hg k' j') h; rfl
  · exact absurd h.symm (xIdx_ne_cIdx (E.sa_lt (E.sitIdx_spec _ hg).1) hk hj hx)

theorem lit_s (s : List (M.Γ M.k₀)) {H t i : ℕ} (hi : i < E.N) :
    E.RunLit s H (E.layout.xIdx H (t + 1) (E.sa i)) ↔ i = E.sitIdx (runI M (initList M s) t) := by
  refine ⟨fun ⟨t', h⟩ => ?_, fun h => ⟨t, Or.inr (Or.inr (by rw [h]))⟩⟩
  have hg := E.run_good s t'
  rcases h with h | ⟨k, hk, j, hj, h⟩ | h
  · have := (xIdx_inj (E.sa_lt hi) (E.code_lt _) h).2
    have := E.lc_lt ((runI M (initList M s) t').l, (runI M (initList M s) t').var)
    unfold sa code at *; omega
  · exact absurd h (xIdx_ne_cIdx (E.sa_lt hi) hk hj (E.cell_lt _ hg k j))
  · obtain ⟨h1, h2⟩ := xIdx_inj (E.sa_lt hi) (E.sa_lt (E.sitIdx_spec _ hg).1) h
    obtain rfl : t = t' := by omega
    unfold sa at h2; omega

theorem fam_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (nx : ℕ → ℕ)
    (hwf : ∀ i < E.N, Family.WF E.layout E.la nx E.wa H i) (hdH : depth M ≤ H)
    (hnx : ∀ t < T,
        E.RunLit s H (E.layout.xIdx H (t + 1) (nx (E.sitIdx (runI M (initList M s) t))))) :
    cnfSat (Family.family E.layout E.la nx E.wa T H E.N) (E.runAsg s T H) := by
  intro c hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  rw [List.mem_range] at ht hi
  have hf := faithful_of_inc (Family.lits_inc ht (hwf i hi))
  have hn : E.layout.nLits = E.KK * depth M + 2 := rfl
  have mem : ∀ j < E.layout.nLits, (Family.litPos E.layout E.la nx E.wa H t i j,
      decide (j = E.layout.nLits - 1)) ∈ Family.lits E.layout E.la nx E.wa H t i :=
    fun j hj => List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  set c := runI M (initList M s) t with hc
  by_cases hsit : i = E.sitIdx c
  · refine E.sat_run hf (mem (E.layout.nLits - 1) (by omega)) ?_
    have : Family.litPos E.layout E.la nx E.wa H t i (E.layout.nLits - 1) =
        E.layout.xIdx H (t + 1) (nx i) := by
      unfold Family.litPos; rw [if_neg (by omega),
          if_neg (show ¬ _ ≤ E.layout.KK * E.layout.d by
        change ¬ _ ≤ E.KK * depth M; omega)]
    rw [this, hsit]; simpa using hnx t ht
  by_cases hla : E.la i = E.code c
  · have : ∃ k < E.KK, ∃ j < depth M, E.wa i k j ≠ E.cell c k j := by
      by_contra hno
      push Not at hno
      exact hsit (E.sit_inj c (E.run_good s t) hi hla hno)
    obtain ⟨k, hk, j, hj, hne⟩ := this
    have hkj : k * depth M + j < E.KK * depth M := by
      have := Nat.mul_le_mul_right (depth M) (show k + 1 ≤ E.KK by omega)
      rw [Nat.add_one_mul] at this; omega
    refine E.sat_run hf (mem (k * depth M + j + 1) (by omega)) ?_
    have hd : 0 < depth M := by omega
    have e1 : (k * depth M + j) / depth M = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (k * depth M + j) % depth M = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have : Family.litPos E.layout E.la nx E.wa H t i (k * depth M + j + 1) =
        E.layout.cIdx H t k j (E.wa i k j) := by
      unfold Family.litPos
      rw [if_neg (by omega), if_pos (show _ ≤ E.layout.KK * E.layout.d from
        show _ ≤ E.KK * depth M by omega)]
      change E.layout.cIdx H t ((k * depth M + j + 1 - 1) / depth M) ((k * depth M + j + 1 - 1) % depth M)
        (E.wa i ((k * depth M + j + 1 - 1) / depth M) ((k * depth M + j + 1 - 1) % depth M)) = _
      rw [Nat.add_sub_cancel, e1, e2]
    rw [this, E.lit_c s hk (by omega) (E.wa_lt i k j)]
    simp only [show k * depth M + j + 1 ≠ E.layout.nLits - 1 by omega, decide_false]
    simpa using hne
  · refine E.sat_run hf (mem 0 (by omega)) ?_
    have : Family.litPos E.layout E.la nx E.wa H t i 0 = E.layout.xIdx H t (E.la i) := by
      unfold Family.litPos; rw [if_pos rfl]
    rw [this, E.lit_x s (E.la_lt i)]
    simp only [show (0 : ℕ) ≠ E.layout.nLits - 1 by omega, decide_false]
    simpa using hla

theorem upd_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    cnfSat (Family.family E.layout E.la E.na E.wa T H E.N) (E.runAsg s T H) :=
  E.fam_complete s E.na (fun i _ => E.wf_upd hdH i) hdH fun t ht =>
    ⟨t + 1, Or.inl (by rw [(E.table_agree_run H s t (hh t ht)).2.2.2.1])⟩

theorem sdef_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H) :
    cnfSat (Family.family E.layout E.la E.sa E.wa T H E.N) (E.runAsg s T H) :=
  E.fam_complete s E.sa (fun i hi => E.wf_sdef hdH i hi) hdH fun t _ =>
    ⟨t, Or.inr (Or.inr rfl)⟩

theorem shift_complete {T H : ℕ} (s : List (M.Γ M.k₀)) (hdH : depth M ≤ H)
    (hh : ∀ t < T, ∀ k, ((runI M (initList M s) t).stk k).length ≤ H - depth M) :
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T H) (E.runAsg s T H) := by
  have hwf := E.wf_sh hdH
  intro c hc
  simp only [Shift.shFamily, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨t, ht, i, hi, k, hk, hc⟩ := hc
  obtain ⟨-, -, -, -, hrow⟩ := E.table_agree_run H s t (hh t ht)
  have hS := E.lit_s s (H := H) (t := t) hi
  set c := runI M (initList M s) t with hcdef
  have hpl := E.pl_le i k
  have hcn := E.cn_le i k
  simp only [Shift.shBlk, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with (⟨u, hu, x, hx, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨j, hj, rfl⟩
  · have := Shift.inc_drop (cl := (.sh ⟨x, hx⟩ : Shift.CL E.layout.g E.layout.d))
      (Shift.shPos_mono (i := ⟨i, hi⟩) (k := ⟨k,
          hk⟩) ht hwf (Nat.add_lt_of_lt_sub hu) hx) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_sh] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      by_cases hxc : x = E.cell c k (u + E.cn (E.sitIdx c) k)
      · refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k (u + E.pl (E.sitIdx c) k) x) (b := true)
          (by simp [Shift.shLits]) ?_
        rw [E.lit_c s hk (by omega) hx, hrow k hk _ (by omega)]
        unfold tabRow
        rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel, ← hxc]
        simp
      · refine E.sat_run hf (p := E.layout.cIdx H t k (u + E.cn (E.sitIdx c) k) x) (b := false)
          (by simp [Shift.shLits]) ?_
        rw [E.lit_c s hk (by omega) hx]
        simpa using hxc
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.shLits]) (by rw [hS]; simpa using hsit)
  · have := Shift.inc_drop (cl := (.ov : Shift.CL E.layout.g E.layout.d))
      (Shift.ovPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hr) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_ov] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k (H - E.cn (E.sitIdx c) k + E.pl (E.sitIdx c) k + r) 0)
        (b := true) (by simp [Shift.ovLits]) ?_
      rw [E.lit_c s hk (by omega) E.g_pos, hrow k hk _ (by omega)]
      unfold tabRow
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.ovLits]) (by rw [hS]; simpa using hsit)
  · have hjd : j < E.layout.d := lt_of_lt_of_le hj (hwf.pl_le i hi k hk)
    have := Shift.inc_drop (cl := (.pf ⟨j, hjd⟩ : Shift.CL E.layout.g E.layout.d))
      (Shift.pfPos_mono (i := ⟨i, hi⟩) (k := ⟨k, hk⟩) ht hwf hj) 0 (Nat.zero_le _)
    rw [List.drop_zero, Shift.clits_pf] at this
    have hf := faithful_of_inc this
    by_cases hsit : i = E.sitIdx c
    · subst hsit
      refine E.sat_run hf (p := E.layout.cIdx H (t + 1) k j (E.pu (E.sitIdx c) k j)) (b := true)
        (by simp [Shift.pfLits]) ?_
      rw [E.lit_c s hk (by omega) (E.pu_lt _ k j hj), hrow k hk _ (by omega)]
      unfold tabRow
      rw [if_pos hj]
      simp
    · exact E.sat_run hf (p := E.layout.xIdx H (t + 1) (E.sa i)) (b := false)
        (by simp [Shift.pfLits]) (by rw [hS]; simpa using hsit)

theorem sat_unit {s : List (M.Γ M.k₀)} {T H p : ℕ} (hp : p < E.layout.numVars T H)
    (h : E.RunLit s H p) :
    clauseSat (Family.denseClause (E.layout.numVars T H) [(p, true)]) (E.runAsg s T H) :=
  E.sat_run (faithful_single hp) (List.mem_singleton.2 rfl) (iff_of_true rfl h)

theorem lit_cell0 (s : List (M.Γ M.k₀)) {H k j : ℕ} (hk : k < E.KK) (hj : j < H) :
    E.RunLit s H (E.layout.cIdx H 0 k j (E.cell (initList M s) k j)) :=
  ⟨0, Or.inr (Or.inl ⟨k, hk, j, hj, rfl⟩)⟩

theorem cell0_k₀ (s : List (M.Γ M.k₀)) (j : ℕ) :
    E.cell (initList M s) (E.kc M.k₀) j = (s[j]?).elim 0 (E.enc M.k₀) := by
  rw [E.cell_kc, initList_k₀]

theorem init_complete {x y Ys : List (M.Γ M.k₀)} {m T H : ℕ} (hy : ∀ z ∈ y, z ∈ Ys)
    (hl : (x ++ y).length ≤ m) (hmH : m < H) :
    cnfSat (E.initFamily x Ys m T H) (E.runAsg (x ++ y) T H) := by
  have cl : ∀ k j v, k < E.KK → j < H → v < E.g → E.layout.cIdx H 0 k j v < E.layout.numVars T H :=
    fun k j v hk hj hv => E.cIdx_lt (Nat.zero_le T) hk hj hv
  have e0 : ∀ z : M.Γ M.k₀, E.enc M.k₀ z < E.g := fun z => E.enc_lt _ z (E.input_mem z)
  have hk0 := E.kc_lt M.k₀
  have hxl : x.length ≤ (x ++ y).length := by simp

  have z0 : ∀ j, (x ++ y).length ≤ j → E.cell (initList M (x ++ y)) (E.kc M.k₀) j = 0 := by
    intro j hj; rw [E.cell0_k₀, List.getElem?_eq_none hj]; rfl
  have z1 : ∀ j, j < (x ++ y).length → E.cell (initList M (x ++ y)) (E.kc M.k₀) j ≠ 0 := by
    intro j hj
    rw [E.cell0_k₀, List.getElem?_eq_getElem hj, Option.elim_some]
    obtain ⟨n, hn⟩ := E.input_mem (x ++ y)[j]
    rw [← hn, E.enc_dec]; omega
  simp only [initFamily, cnfSat_append]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    intro c hc
    obtain rfl := List.mem_singleton.1 hc
    exact E.sat_unit (E.xIdx_lt (Nat.zero_le T) (E.lc_lt _)) ⟨0, Or.inl rfl⟩
  ·
    intro c hc
    obtain ⟨k, hk, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    obtain ⟨hk, hne⟩ := List.mem_filter.1 hk
    rw [List.mem_range] at hk hj
    have hne : E.kd k ≠ M.k₀ := fun h => by
      have := E.kc_kd k hk; rw [h] at this; simp [this] at hne
    have h0 : E.cell (initList M (x ++ y)) k j = 0 := by
      unfold cell; rw [initList_ne _ _ hne]; rfl
    refine E.sat_unit (cl _ _ _ hk hj E.g_pos) ?_
    have := E.lit_cell0 (x ++ y) hk hj
    rwa [h0] at this
  ·
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hj
    have hjH : j < H := by omega
    refine E.sat_unit (cl _ _ _ hk0 hjH (by rw [List.getElem?_eq_getElem hj]; exact e0 _)) ?_
    have := E.lit_cell0 (x ++ y) hk0 hjH
    rwa [E.cell0_k₀, List.getElem?_append_left hj] at this
  ·
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    have hjH : x.length + i < H := by omega
    have hf : Faithful (E.layout.numVars T H) ((E.zIdx H (x.length + i), true) ::
        Ys.map fun z => (E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ z), true)) := by
      refine faithful_pos fun p b hp => ?_
      rcases List.mem_cons.1 hp with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨cl _ _ _ hk0 hjH E.g_pos, rfl⟩
      · obtain ⟨z, _, he⟩ := List.mem_map.1 h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨cl _ _ _ hk0 hjH (e0 z), rfl⟩
    have hlit := E.lit_cell0 (x ++ y) hk0 hjH
    by_cases hin : x.length + i < (x ++ y).length
    · have hiy : i < y.length := by simp at hin; omega
      refine E.sat_run hf (p := E.layout.cIdx H 0 (E.kc M.k₀) (x.length + i) (E.enc M.k₀ y[i]))
        (b := true) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, hy _ (List.getElem_mem hiy), rfl⟩))
        (iff_of_true rfl ?_)
      rwa [E.cell0_k₀, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hiy, Option.elim_some] at hlit
    · refine E.sat_run hf (p := E.zIdx H (x.length + i)) (b := true) List.mem_cons_self
        (iff_of_true rfl ?_)
      unfold zIdx
      rwa [z0 _ (by omega)] at hlit
  ·
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    have h2 := cl (E.kc M.k₀) (x.length + i + 1) 0 hk0 (by omega) E.g_pos
    have hg := E.g_pos
    have h1 : E.zIdx H (x.length + i) + 1 ≤ E.zIdx H (x.length + i + 1) := by
      unfold zIdx Family.Layout.cIdx
      have : (E.kc M.k₀ * H + (x.length + i + 1)) * E.layout.g =
          (E.kc M.k₀ * H + (x.length + i)) * E.layout.g + E.layout.g := by ring
      have : E.layout.g = E.g := rfl
      omega
    have hf := faithful_of_inc (lo := 0) (V := E.layout.numVars T H)
      (ls := [(E.zIdx H (x.length + i), false), (E.zIdx H (x.length + i + 1), true)])
      ⟨Nat.zero_le _, h1, h2⟩
    by_cases hin : x.length + i < (x ++ y).length
    · refine E.sat_run hf (p := E.zIdx H (x.length + i)) (b := false) List.mem_cons_self ?_
      unfold zIdx
      rw [E.lit_c _ hk0 (by omega) E.g_pos]
      simpa [runI] using (z1 _ hin).symm
    · refine E.sat_run hf (p := E.zIdx H (x.length + i + 1)) (b := true)
        (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) (iff_of_true rfl ?_)
      have := E.lit_cell0 (x ++ y) hk0 (show x.length + i + 1 < H by omega)
      unfold zIdx
      rwa [z0 _ (by omega)] at this
  ·
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hi
    refine E.sat_unit (cl _ _ _ hk0 (by omega) E.g_pos) ?_
    have := E.lit_cell0 (x ++ y) hk0 (show m + i < H by omega)
    unfold zIdx
    rwa [z0 _ (by omega)] at this

theorem acc_complete (s : List (M.Γ M.k₀)) {T H : ℕ} {acc : M.Γ M.k₁} (hH : 0 < H)
    (hA : Accepts M (runI M (initList M s) T) acc) :
    cnfSat (E.accFamily acc T H) (E.runAsg s T H) := by
  obtain ⟨hl, hv, hk⟩ := hA
  have hcode : E.code (runI M (initList M s) T) = E.acode := by
    unfold code acode; rw [hl, hv]
  have hcell : E.cell (runI M (initList M s) T) (E.kc M.k₁) 0 = E.enc M.k₁ acc := by
    rw [E.cell_kc, ← List.head?_eq_getElem?, hk]; rfl
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hu
    refine E.sat_run (faithful_single (E.xIdx_lt le_rfl hu)) (List.mem_singleton.2 rfl) ?_
    rw [E.lit_x s hu, hcode]; simp
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at hx
    refine E.sat_run (faithful_single (E.cIdx_lt le_rfl (E.kc_lt _) hH hx))
      (List.mem_singleton.2 rfl) ?_
    rw [E.lit_c s (E.kc_lt _) hH hx, hcell]; simp

theorem accept_complete {x y Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hy : ∀ z ∈ y, z ∈ Ys) (hl : (x ++ y).length ≤ m)
    (hA : Accepts M (runI M (initList M (x ++ y)) T) acc) :
    let a := E.runAsg (x ++ y) T (capH m T (depth M))
    a.length = E.layout.numVars T (capH m T (depth M)) ∧
    cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
    cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
    cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
    cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
    cnfSat (E.accFamily acc T (capH m T (depth M))) a := by
  have hh : ∀ t < T, ∀ k, ((runI M (initList M (x ++ y)) t).stk k).length ≤
      capH m T (depth M) - depth M := fun t ht k => capH_height (x ++ y) hl ht.le k
  have hdH := depth_le_capH M m T
  exact ⟨E.runAsg_length _ _ _, E.upd_complete _ hdH hh, E.sdef_complete _ hdH,
    E.shift_complete _ hdH hh, E.init_complete hy hl (by unfold capH; omega),
    E.acc_complete _ (by unfold capH; omega) hA⟩

theorem five_iff {x Ys : List (M.Γ M.k₀)} {m T : ℕ} {acc : M.Γ M.k₁}
    (hx : x.length ≤ m) (hacc : ∃ i, E.dec M.k₁ i = acc) :
    (∃ a : List Bool,
      cnfSat (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N) a ∧
      cnfSat (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M))) a ∧
      cnfSat (E.initFamily x Ys m T (capH m T (depth M))) a ∧
      cnfSat (E.accFamily acc T (capH m T (depth M))) a) ↔
    ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
      Accepts M (runI M (initList M (x ++ y)) T) acc := by
  constructor
  · rintro ⟨a, hu, hs, ha, hI, hA⟩
    exact E.accept_sound hx hacc hu hs ha hI hA
  · rintro ⟨y, hy, hl, hA⟩
    obtain ⟨_, h⟩ := E.accept_complete hy hl hA
    exact ⟨_, h⟩

end Enc

end C6

end Cslib.Complexity.CookLevin.Situation
end

-- CSLibExt.Computability.Complexity.CookLevin.Accept
section
namespace Cslib.Complexity.CookLevin.Accept

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc encodeClause_denseClause denseClause)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out emitS emitOut incS drainS
  xferES copyS mulS mulS_run gapS bud_st)

section Spec

variable (L : Layout) (n1 ac k1 ea : ℕ)

def codeLits (T H u : ℕ) : List (ℕ × Bool) := [(L.xIdx H T u, decide (u = ac))]

def cellLits (T H x : ℕ) : List (ℕ × Bool) := [(L.cIdx H T k1 0 x, decide (x = ea))]

def accFam (T H : ℕ) : CNF :=
  (List.range n1).map (fun u => denseClause (L.numVars T H) (codeLits L ac T H u)) ++
    (List.range L.g).map (fun x => denseClause (L.numVars T H) (cellLits L k1 ea T H x))

end Spec

inductive CK
  | Tn | Hs | Gc | HG | Wc | Kc | K1 | Vc | TW | CB | P | Q | tmp | md | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Hs, CK.Gc, CK.HG, CK.Wc, CK.Kc, CK.K1, CK.Vc, CK.TW, CK.CB, CK.P, CK.Q,
      CK.tmp, CK.md, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

inductive AK (n1 g : ℕ)
  | code (u : Fin n1)
  | cell (x : Fin g)
  deriving DecidableEq, Fintype

namespace AK

variable {n1 g : ℕ}

def bc : AK n1 g → CK
  | code _ => .TW
  | cell _ => .CB

def off : AK n1 g → ℕ
  | code u => u
  | cell x => x

def sg (ac ea : ℕ) : AK n1 g → Bool
  | code u => decide (u.val = ac)
  | cell x => decide (x.val = ea)

theorem bc_ne (c : AK n1 g) : c.bc ≠ .Q ∧ c.bc ≠ .tmp ∧ c.bc ≠ .P := by
  cases c <;> simp [bc]

end AK

inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | tw (s : MS) | inc | v (s : MS)
  | cb1 | cb2 | cbA | k1 | cbM (s : MS)
  deriving DecidableEq, Fintype

inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

inductive GeneratorLabel (n1 g : ℕ)
  | pre (s : PS)
  | e00 (c : AK n1 g) | cv1 (c : AK n1 g) | cv2 (c : AK n1 g) | lit (c : AK n1 g) (s : LS)
  | fin (c : AK n1 g)
  | done
  deriving DecidableEq, Fintype

namespace GeneratorLabel

variable {n1 g : ℕ}

def codeFrom (u : ℕ) : GeneratorLabel n1 g := if h : u < n1 then .e00 (.code ⟨u, h⟩) else .done

def codeStart : GeneratorLabel n1 g := if n1 = 0 then .done else codeFrom (n1 - 1)

def cellFrom (x : ℕ) : GeneratorLabel n1 g := if h : x < g then .e00 (.cell ⟨x, h⟩) else codeStart

def start : GeneratorLabel n1 g := if g = 0 then codeStart else cellFrom (g - 1)

def nextC : AK n1 g → GeneratorLabel n1 g
  | .code u => if u.val = 0 then .done else codeFrom (u.val - 1)
  | .cell x => if x.val = 0 then codeStart else cellFrom (x.val - 1)

theorem codeFrom_of_lt {u : ℕ} (h : u < n1) : (codeFrom u : GeneratorLabel n1 g) = .e00 (.code ⟨u, h⟩) :=
  dif_pos h

theorem cellFrom_of_lt {x : ℕ} (h : x < g) : (cellFrom x : GeneratorLabel n1 g) = .e00 (.cell ⟨x, h⟩) :=
  dif_pos h

end GeneratorLabel

section Machine

variable (L : Layout) (n1 ac k1 ea : ℕ)

def litP (c : AK n1 L.g) : LS → TM2.Stmt (SΓ CK) (GeneratorLabel n1 L.g) Bool
  | .cp1 => xfer (.c c.bc) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit c .cp1) (.lit c .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c c.bc, ()⟩] (.lit c .cp2) (.lit c .eo)
  | .eo => emitR (.c .Q) (List.replicate c.off ()) (.lit c .dec)
  | .dec => decr (.c .P) (.lit c .bad) (.lit c .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit c .cmp)
      (.lit c (.r .lt)) (.lit c (.r .eq)) (.lit c (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit c (.r o)) (.lit c (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit c (.rB o))
      (if o = .eq then .lit c .slot else .lit c .emL)
  | .emL => emitR .out [false, true] (.lit c .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg ac ea))) (.lit c .dq)
  | .dq => xfer (.c .Q) [] (.lit c .dq) (.fin c)

def prog : GeneratorLabel n1 L.g → TM2.Stmt (SΓ CK) (GeneratorLabel n1 L.g) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Kc) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Kc .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre (.tw .head)) s
  | .pre (.tw s) => mulS .Tn .md .Wc .TW .tmp (fun s => .pre (.tw s)) (.pre .inc) s
  | .pre .inc => incr (.c .Tn) () (.pre (.v .head))
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .cb1) s
  | .pre .cb1 => xfer (.c .TW) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.pre .cb1) (.pre .cb2)
  | .pre .cb2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.pre .cb2) (.pre .cbA)
  | .pre .cbA => emitR (.c .CB) (List.replicate L.A ()) (.pre .k1)
  | .pre .k1 => emitR (.c .K1) (List.replicate k1 ()) (.pre (.cbM .head))
  | .pre (.cbM s) => mulS .K1 .md .HG .CB .tmp (fun s => .pre (.cbM s)) GeneratorLabel.start s
  | .e00 c => emitR .out [false, false] (.cv1 c)
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 c) (.cv2 c)
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 c) (.lit c .cp1)
  | .lit c s => litP L n1 ac ea c s
  | .fin c => xferE (.c .P) .out [false, true] (.fin c) (GeneratorLabel.nextC c)
  | .done => .halt

def accTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := GeneratorLabel n1 L.g
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L n1 ac k1 ea

end Machine

section Clause

variable {L : Layout} {n1 ac k1 ea : ℕ}

structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem lit_run (c : AK n1 L.g) (F : CK → ℕ) (hF : Rest F) (q gap : ℕ)
    (hq : q = F c.bc + c.off) (hp : F .P = q + gap + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L n1 ac k1 ea) (gap * (3 * q + 6) + 2 * F c.bc + 4 * q + 9)
      ⟨some (.lit c .cp1), v, st F o⟩
      ⟨some (.fin c), false,
        st (update F .P q) (encodeSlot (some (c.sg ac ea)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  refine Bud.start ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .lit c .cp1) (l₂ := .lit c .cp2)
    (next := .lit c .eo) rfl rfl b1 b2 (by decide) F htmp v o).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .lit c .eo) (next := .lit c .dec) rfl _ _
    _).bud ?_
  refine (gapS (M := prog L n1 ac k1 ea) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true])
    (dec := .lit c .dec) (cmpL := .lit c .cmp) (emitL := .lit c .emL)
    (ifZero := .lit c .bad) (next := .lit c .slot) (r := fun o => .lit c (.r o))
    (rB := fun o => .lit c (.rB o))
    (out := fun o => if o = .eq then .lit c .slot else .lit c .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L n1 ac k1 ea) (self := .lit c .slot) (next := .lit c .dq) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L n1 ac k1 ea) (self := .lit c .dq) (next := .fin c) (x := .Q) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

def clauseB (V : ℕ) : ℕ := V * (3 * V + 6) + 10 * V + 13

theorem encodeClause_unit {V p : ℕ} {b : Bool} (h : p < V) :
    encodeClause (denseClause V [(p, b)]) =
      rep [false, true] p ++ encodeSlot (some b) ++ rep [false, true] (V - p - 1) ++
        [false, false] := by
  rw [encodeClause_denseClause (show Inc 0 [(p, b)] V from ⟨Nat.zero_le _, h⟩)]
  simp only [gapEnc, Nat.sub_zero, List.append_assoc]
  rw [show V - (p + 1) = V - p - 1 by omega]

theorem clause_run {V : ℕ} (c : AK n1 L.g) (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V)
    (hP : F .P = 0) (hlt : F c.bc + c.off < V) (o : List Bool) (v : Bool) :
    RunLe (prog L n1 ac k1 ea) (clauseB V) ⟨some (.e00 c), v, st F o⟩
      ⟨some (GeneratorLabel.nextC c), false,
        st F (encodeClause (denseClause V [(F c.bc + c.off, c.sg ac ea)]) ++ o)⟩ := by
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  set p := F c.bc + c.off with hpdef
  refine Bud.start ?_
  refine (emitOut (M := prog L n1 ac k1 ea) (self := .e00 c) (next := .cv1 c) rfl _ _ _).bud ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .cv1 c) (l₂ := .cv2 c) (next := .lit c .cp1)
    rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  have r := lit_run (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) c (update F .P (F .Vc + F .P))
    ⟨by simp [hF.Q], by simp [hF.tmp], by simp [hF.md], by simp [hF.c1], by simp [hF.c2]⟩
    p (V - p - 1) (by simp [hpdef, b3]) (by simp [hV, hP]; omega) ([false, false] ++ o) false
  refine r.bud ?_
  refine (xferES (M := prog L n1 ac k1 ea) (self := .fin c) (next := GeneratorLabel.nextC c) (x := .P) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp only [update_self, ne_eq, b3, not_false_eq_true, update_of_ne, hV, hP]
    have h1 : (V - p - 1) * (3 * p + 6) ≤ V * (3 * V + 6) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold clauseB
    omega
  · rw [encodeClause_unit hlt]
    simp only [update_self, update_idem, List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hP]

end Clause

section Top

variable {L : Layout} {n1 ac k1 ea : ℕ}

theorem codes_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) :
    ∀ u, u < n1 → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L n1 ac k1 ea) ((u + 1) * clauseB V) ⟨some (GeneratorLabel.codeFrom u), v, st F o⟩
        ⟨some .done, false, st F ((List.range (u + 1)).flatMap
          (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++ o)⟩ := by
  intro u
  induction u with
  | zero =>
      intro hu o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.code ⟨0,
          hu⟩) F hF hV hP
        (by simp only [AK.bc, AK.off]; omega) o v
      rw [GeneratorLabel.codeFrom_of_lt hu]
      simpa [GeneratorLabel.nextC, AK.bc, AK.off, AK.sg] using r
  | succ u ih =>
      intro hu o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.code ⟨u + 1,
          hu⟩) F hF
        hV hP (by simp only [AK.bc, AK.off]; omega) o v
      simp only [GeneratorLabel.nextC, AK.bc, AK.off, AK.sg, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel] at r
      rw [GeneratorLabel.codeFrom_of_lt hu]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V [(F .TW + (u + 1),
          decide (u + 1 = ac))]) ++ o)
        false
      rw [List.range_succ (n := u + 1), List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (u + 1)]; omega

theorem codeStart_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) (o : List Bool) :
    RunLe (prog L n1 ac k1 ea) (n1 * clauseB V) ⟨some GeneratorLabel.codeStart, false, st F o⟩
      ⟨some .done, false, st F ((List.range n1).flatMap
        (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++ o)⟩ := by
  by_cases h : n1 = 0
  · subst h
    simp only [GeneratorLabel.codeStart, if_true, List.range_zero, List.flatMap_nil, List.nil_append]
    exact ⟨0, Nat.zero_le _, Run.zero _⟩
  · rw [GeneratorLabel.codeStart, if_neg h]
    have := codes_run (L := L) (ac := ac) (k1 := k1) (ea := ea) F hF hV hP hlt (n1 - 1) (by omega)
      o false
    rwa [Nat.sub_add_cancel (by omega)] at this

theorem cells_run {V : ℕ} (F : CK → ℕ) (hF : Rest F) (hV : F .Vc = V) (hP : F .P = 0)
    (hlt : F .TW + n1 ≤ V) (hlc : F .CB + L.g ≤ V) :
    ∀ x, x < L.g → ∀ (o : List Bool) (v : Bool),
      RunLe (prog L n1 ac k1 ea) ((x + 1) * clauseB V + n1 * clauseB V)
        ⟨some (GeneratorLabel.cellFrom x), v, st F o⟩
        ⟨some .done, false, st F ((List.range n1).flatMap
          (fun u => encodeClause (denseClause V [(F .TW + u, decide (u = ac))])) ++
          (List.range (x + 1)).flatMap
          (fun x => encodeClause (denseClause V [(F .CB + x, decide (x = ea))])) ++ o)⟩ := by
  intro x
  induction x with
  | zero =>
      intro hx o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.cell ⟨0,
          hx⟩) F hF hV hP
        (by simp only [AK.bc, AK.off]; omega) o v
      rw [GeneratorLabel.cellFrom_of_lt hx]
      simp only [GeneratorLabel.nextC, AK.bc, AK.off, AK.sg, if_true] at r
      refine Bud.start (r.bud ?_)
      have := codeStart_run (L := L) (ac := ac) (k1 := k1) (ea := ea) F hF hV hP hlt
        (encodeClause (denseClause V [(F .CB + 0, decide (0 = ea))]) ++ o)
      simp only [zero_add, List.range_one, List.flatMap_singleton, List.append_assoc] at this ⊢
      refine this.bud (Bud.fin ?_ rfl)
      omega
  | succ x ih =>
      intro hx o v
      have r := clause_run (L := L) (n1 := n1) (ac := ac) (k1 := k1) (ea := ea) (.cell ⟨x + 1,
          hx⟩) F hF
        hV hP (by simp only [AK.bc, AK.off]; omega) o v
      simp only [GeneratorLabel.nextC, AK.bc, AK.off, AK.sg, Nat.add_one_ne_zero, if_false,
        Nat.add_sub_cancel] at r
      rw [GeneratorLabel.cellFrom_of_lt hx]
      refine Bud.start (r.bud ?_)
      have := ih (by omega) (encodeClause (denseClause V [(F .CB + (x + 1),
          decide (x + 1 = ea))]) ++ o)
        false
      rw [List.range_succ (n := x + 1), List.flatMap_append, List.flatMap_singleton]
      simp only [List.append_assoc] at this ⊢
      refine this.bud (Bud.fin ?_ rfl)
      rw [Nat.succ_mul (x + 1)]; omega

def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

def preF (L : Layout) (k1 T H : ℕ) : CK → ℕ
  | .Tn => T + 1
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Kc => L.KK
  | .K1 => k1
  | .Vc => L.numVars T H
  | .TW => T * L.rowW H
  | .CB => L.cIdx H T k1 0 0
  | _ => 0

def preB (L : Layout) (k1 T H : ℕ) : ℕ :=
  3 + (H * (2 * L.g + 3) + H + 2) + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) +
    (T * (2 * L.rowW H + 3) + T + 2) + 1 + ((T + 1) * (2 * L.rowW H + 3) + (T + 1) + 2) +
    (2 * (T * L.rowW H) + 2) + 2 + (k1 * (2 * (H * L.g) + 3) + k1 + 2)

def accBound (L : Layout) (n1 k1 T H : ℕ) : ℕ :=
  preB L k1 T H + (L.g + n1) * clauseB (L.numVars T H)

theorem encodeCNF_accFam (T H : ℕ) :
    encodeCNF (accFam L n1 ac k1 ea T H) =
      (List.range n1).flatMap (fun u => encodeClause (denseClause (L.numVars T H)
        [(T * L.rowW H + u, decide (u = ac))])) ++
      (List.range L.g).flatMap (fun x => encodeClause (denseClause (L.numVars T H)
        [(L.cIdx H T k1 0 0 + x, decide (x = ea))])) := by
  simp only [encodeCNF, accFam, List.flatMap_append, List.flatMap_map, codeLits, cellLits]
  rfl

theorem pre_run (T H : ℕ) (o : List Bool) :
    RunLe (prog L n1 ac k1 ea) (preB L k1 T H)
      ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some GeneratorLabel.start, false, st (preF L k1 T H) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.hg s)) (next := .pre .ew)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .ek) (next := .pre (.w .head)) (x := .Kc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.w s)) (next := .pre (.tw .head))
    (a := .Kc) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.tw s)) (next := .pre .inc)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (incS (M := prog L n1 ac k1 ea) (self := .pre .inc) (next := .pre (.v .head)) (x := .Tn)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.v s)) (next := .pre .cb1)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L n1 ac k1 ea) (l₁ := .pre .cb1) (l₂ := .pre .cb2) (next := .pre .cbA)
    rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .cbA) (next := .pre .k1) (x := .CB) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L n1 ac k1 ea) (self := .pre .k1) (next := .pre (.cbM .head)) (x := .K1)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L n1 ac k1 ea) (mk := fun s => .pre (.cbM s)) (next := GeneratorLabel.start)
    (a := .K1) (ad := .md) (b := .HG) (c := .CB) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L k1 T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars, Layout.cIdx] <;>
      first | ring1 | (left; ring1)) (Bud.fin ?_ rfl)
  simp [initF, preB, Layout.rowW]
  ring_nf
  omega

theorem acc_run (hn1 : n1 ≤ L.A) (hk1 : k1 < L.KK) (T H : ℕ) (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L n1 ac k1 ea) (accBound L n1 k1 T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (accFam L n1 ac k1 ea T H) ++ o := by
  refine ⟨false, st (preF L k1 T H) ((List.range n1).flatMap (fun u => encodeClause
    (denseClause (L.numVars T H) [(T * L.rowW H + u, decide (u = ac))])) ++
      (List.range L.g).flatMap (fun x => encodeClause (denseClause (L.numVars T H)
        [(L.cIdx H T k1 0 0 + x, decide (x = ea))])) ++ o), ?_, by
    rw [encodeCNF_accFam]; rfl⟩
  refine Bud.start ((pre_run (ac := ac) (ea := ea) T H o).bud ?_)
  have hR : Rest (preF L k1 T H) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hW : L.A ≤ L.rowW H := Nat.le_add_right _ _
  have hlt : preF L k1 T H .TW + n1 ≤ L.numVars T H := by
    simp only [preF, Layout.numVars]; rw [Nat.succ_mul]; omega
  have hlc : preF L k1 T H .CB + L.g ≤ L.numVars T H := by
    have := Cslib.Complexity.CookLevin.OneHot.base_le (L := L) (T := T) (H := H) (t := T) (k := k1) (j := 0) le_rfl hk1 hH
    simp only [preF]
    rw [← Cslib.Complexity.CookLevin.OneHot.base_eq]; simpa using this
  by_cases hg : L.g = 0
  · have hst : (GeneratorLabel.start : GeneratorLabel n1 L.g) = GeneratorLabel.codeStart := by simp [GeneratorLabel.start, hg]
    rw [hst, show List.range L.g = [] by simp [hg], List.flatMap_nil, List.append_nil]
    refine (codeStart_run (L := L) (ac := ac) (k1 := k1) (ea := ea) _ hR rfl rfl hlt o).bud
      (Bud.fin ?_ rfl)
    unfold accBound; simp only [preF, hg, zero_add]; omega
  · have hst : (GeneratorLabel.start : GeneratorLabel n1 L.g) = GeneratorLabel.cellFrom (L.g - 1) := by simp [GeneratorLabel.start, hg]
    rw [hst]
    have r := cells_run (L := L) (ac := ac) (k1 := k1) (ea := ea) _ hR rfl rfl hlt hlc (L.g - 1)
      (by omega) o false
    rw [Nat.sub_add_cancel (by omega)] at r
    simp only [List.append_assoc] at r ⊢
    refine r.bud (Bud.fin ?_ rfl)
    unfold accBound; simp only [preF]; rw [Nat.add_mul]; omega

end Top

section Poly

theorem accBound_mono {L L' : Layout} {n1 n1' k1 k1' T T' H H' : ℕ} (hA : L.A ≤ L'.A)
    (hK : L.KK ≤ L'.KK) (hg : L.g ≤ L'.g) (hn : n1 ≤ n1') (hk : k1 ≤ k1') (hT : T ≤ T')
    (hH : H ≤ H') : accBound L n1 k1 T H ≤ accBound L' n1' k1' T' H' := by
  unfold accBound preB clauseB Layout.numVars Layout.rowW
  gcongr

theorem accBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    accBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k k y y ≤ 314 * k ^ 5 * y ^ 4 := by
  have m : ∀ a b, a ≤ 5 → b ≤ 4 → k ^ a * y ^ b ≤ k ^ 5 * y ^ 4 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold accBound preB clauseB Layout.numVars Layout.rowW Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  nlinarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 0 3 (by norm_num) (by norm_num),
    m 0 4 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 1 4 (by norm_num) (by norm_num),
    m 2 0 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num),
    m 3 0 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 3 4 (by norm_num) (by norm_num),
    m 4 0 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 5 0 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num)]

example : accBound (Cslib.Complexity.CookLevin.Family.Layout.uni 1) 1 1 1 1 = 314 := rfl

def accC (L : Layout) (n1 k1 : ℕ) : ℕ := 314 * (L.A + L.KK + L.g + n1 + k1 + 1) ^ 5

theorem accBound_le (L : Layout) (n1 k1 T H : ℕ) :
    accBound L n1 k1 T H ≤ accC L n1 k1 * (T + H + 1) ^ 4 := by
  have := accBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + n1 + k1 + 1))
    (n1 := n1) (k1 := k1)
    (n1' := L.A + L.KK + L.g + n1 + k1 + 1) (k1' := L.A + L.KK + L.g + n1 + k1 + 1)
    (T := T) (T' := T + H + 1) (H := H) (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := accBound_uni (L.A + L.KK + L.g + n1 + k1 + 1) (T + H + 1) (by omega) (by omega)
  unfold accC
  exact this.trans h2

theorem acc_time {L : Layout} {n1 ac k1 ea : ℕ} (hn1 : n1 ≤ L.A) (hk1 : k1 < L.KK) (T H : ℕ)
    (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L n1 ac k1 ea) (accC L n1 k1 * (T + H + 1) ^ 4)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (accFam L n1 ac k1 ea T H) ++ o :=
  let ⟨v, S, h, h'⟩ := acc_run hn1 hk1 T H hH o; ⟨v, S, h.mono (accBound_le L n1 k1 T H), h'⟩

end Poly

section Link

variable {M : FinTM2} (E : Cslib.Complexity.CookLevin.Situation.Enc M)

theorem accFamily_eq (acc : M.Γ M.k₁) (T H : ℕ) :
    E.accFamily acc T H = accFam E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc) T H := rfl

theorem acc_gen_time (acc : M.Γ M.k₁) (T H : ℕ) (hH : 0 < H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc))
        (accC E.layout E.A0 (E.kc M.k₁) * (T + H + 1) ^ 4)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (E.accFamily acc T H) ++ o :=
  acc_time (Nat.le_add_right _ _) (E.kc_lt _) T H hH o

end Link

end Cslib.Complexity.CookLevin.Accept
end

-- CSLibExt.Computability.Complexity.CookLevin.InitFamily
section
namespace Cslib.Complexity.CookLevin.InitFamily

open MetaMathlibExt

open MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc encodeClause_denseClause denseClause)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out emitS emitOut incS drainS
  xferES copyS mulS mulS_run gapS bud_st stLoop)

inductive IK (C : Type)
  | b (k : SK C)
  | inp
  deriving DecidableEq, Fintype

abbrev IΓ (C G : Type) : IK C → Type
  | .b k => SΓ C k
  | .inp => G

section Lift

variable {C G Λ : Type} [DecidableEq C]

def emb (S : ∀ k, List (SΓ C k)) (xs : List G) : ∀ k, List (IΓ C G k)
  | .b k => S k
  | .inp => xs

omit [DecidableEq C] in
@[simp] theorem emb_b (S : ∀ k, List (SΓ C k)) (xs : List G) (k : SK C) : emb S xs (.b k) = S k :=
  rfl

omit [DecidableEq C] in
@[simp] theorem emb_inp (S : ∀ k, List (SΓ C k)) (xs : List G) : emb S xs .inp = xs := rfl

theorem update_emb (S : ∀ k, List (SΓ C k)) (xs : List G) (k : SK C) (l : List (SΓ C k)) :
    update (emb S xs) (.b k) l = emb (update S k l) xs := by
  funext k'
  rcases k' with k' | _
  · by_cases h : k' = k
    · subst h; simp
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl

theorem update_emb_inp (S : ∀ k, List (SΓ C k)) (xs ys : List G) :
    update (emb S xs) .inp ys = emb S ys := by
  funext k'
  rcases k' with k' | _
  · rw [update_of_ne (by simp)]; rfl
  · simp

def liftE : SEmb (SΓ C) (IΓ C G) where
  e := IK.b
  inj := fun _ _ h => by cases h; rfl
  ι := fun _ => Equiv.refl _

omit [DecidableEq C] in
theorem agree_emb (S : ∀ k, List (SΓ C k)) (xs : List G) : Agree liftE S (emb S xs) := by
  intro k; exact (List.map_id _).symm

theorem run_lift {M : Λ → TM2.Stmt (SΓ C) Λ Bool} {M' : Λ → TM2.Stmt (IΓ C G) Λ Bool}
    (hM : Embeds liftE id M M') (xs : List G) (n : ℕ) (l : Option Λ) (v : Bool)
    (S : ∀ k, List (SΓ C k)) (l' : Λ) (v' : Bool) (S' : ∀ k, List (SΓ C k))
    (h : Run M n ⟨l, v, S⟩ ⟨some l', v', S'⟩) :
    Run M' n ⟨l, v, emb S xs⟩ ⟨some l', v', emb S' xs⟩ := by
  obtain ⟨T', r, hA, hF⟩ := run_embed id hM n l v S l' v' S' (emb S xs) h (agree_emb S xs)
  have hT : T' = emb S' xs := by
    funext k
    rcases k with k | _
    · exact (hA k).trans (List.map_id _)
    · exact hF .inp (fun k h => by cases h)
  rw [Option.map_id] at r
  exact hT ▸ r

theorem runLe_lift {M : Λ → TM2.Stmt (SΓ C) Λ Bool} {M' : Λ → TM2.Stmt (IΓ C G) Λ Bool}
    (hM : Embeds liftE id M M') (xs : List G) {B : ℕ} {l : Option Λ} {v : Bool}
    {S : ∀ k, List (SΓ C k)} {l' : Λ} {v' : Bool} {S' : ∀ k, List (SΓ C k)}
    (h : RunLe M B ⟨l, v, S⟩ ⟨some l', v', S'⟩) :
    RunLe M' B ⟨l, v, emb S xs⟩ ⟨some l', v', emb S' xs⟩ :=
  let ⟨n, hn, r⟩ := h; ⟨n, hn, run_lift hM xs n l v S l' v' S' r⟩

end Lift

section Read

variable {C Λ : Type} [DecidableEq C] {g : ℕ}

def rdS (hit miss : Fin g → Λ) (i : Fin g) : TM2.Stmt (IΓ C (Fin g)) Λ Bool :=
  .peek .inp (fun _ o => decide (o = some i))
    (.branch id (.pop .inp (fun v _ => v) (.goto fun _ => hit i)) (.goto fun _ => miss i))

theorem read_run {M' : Λ → TM2.Stmt (IΓ C (Fin g)) Λ Bool} {rd hit miss : Fin g → Λ}
    (hrd : ∀ i, M' (rd i) = rdS hit miss i)
    (hmiss : ∀ i : Fin g, ∀ h : i.val + 1 < g, miss i = rd ⟨i.val + 1, h⟩)
    (S : ∀ k, List (SΓ C k)) (c : Fin g) (xs : List (Fin g)) :
    ∀ k (i : Fin g), i.val + k = c.val → ∀ v : Bool,
      Run M' (k + 1) ⟨some (rd i), v, emb S (c :: xs)⟩ ⟨some (hit c), true, emb S xs⟩ := by
  intro k
  induction k with
  | zero =>
      intro i hi v
      obtain rfl : i = c := Fin.ext (by omega)
      refine Run.single ?_
      simp [hrd, rdS, TM2.stepAux, update_emb_inp]
  | succ k ih =>
      intro i hi v
      have hne : c ≠ i := fun h => by subst h; omega
      have hlt : i.val + 1 < g := by have := c.2; omega
      refine Run.head (d := ⟨some (rd ⟨i.val + 1, hlt⟩), false, emb S (c :: xs)⟩) ?_
        (ih ⟨i.val + 1, hlt⟩ (by simp only; omega) false)
      simp [TM2.step, hrd, rdS, TM2.stepAux, hne, hmiss i hlt]

end Read

section Spec

variable (L : Layout) (ic k0 : ℕ) (ycs : List ℕ)

def zB (H j : ℕ) : ℕ := L.cIdx H 0 k0 j 0

def iCode (T H : ℕ) : CNF := [denseClause (L.numVars T H) [(L.xIdx H 0 ic, true)]]

def iOther (T H : ℕ) : CNF :=
  ((List.range L.KK).filter (· ≠ k0)).flatMap fun k =>
    (List.range H).map fun j => denseClause (L.numVars T H) [(L.cIdx H 0 k j 0, true)]

def iIn (xs : List (Fin L.g)) (T H : ℕ) : CNF :=
  (List.range xs.length).map fun j => denseClause (L.numVars T H)
    [(L.cIdx H 0 k0 j ((xs[j]?).elim 0 Fin.val), true)]

def iCert (n m T H : ℕ) : CNF :=
  (List.range (m - n)).map fun i => denseClause (L.numVars T H)
    ((zB L k0 H (n + i), true) :: ycs.map fun c => (L.cIdx H 0 k0 (n + i) c, true))

def iPre (n m T H : ℕ) : CNF :=
  (List.range (m - n)).map fun i => denseClause (L.numVars T H)
    [(zB L k0 H (n + i), false), (zB L k0 H (n + i + 1), true)]

def iTail (m T H : ℕ) : CNF :=
  (List.range (H - m)).map fun i => denseClause (L.numVars T H) [(zB L k0 H (m + i), true)]

def initFam (xs : List (Fin L.g)) (m T H : ℕ) : CNF :=
  iCode L ic T H ++ iOther L k0 T H ++ iIn L k0 xs T H ++ iCert L k0 ycs xs.length m T H ++
    iPre L k0 xs.length m T H ++ iTail L k0 m T H

end Spec

inductive CK
  | Tn | Xn | En | Fn | Gc | Mm | Hs | HG | Wc | Vc | KA | ZA | Z45 | Z6 | Z1 | Z2 | N1 | N2
  | CB | Zr | P | Q | tmp | md | c1 | c2 | Id
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Xn, CK.En, CK.Fn, CK.Gc, CK.Mm, CK.Hs, CK.HG, CK.Wc, CK.Vc, CK.KA, CK.ZA,
      CK.Z45, CK.Z6, CK.Z1, CK.Z2, CK.N1, CK.N2, CK.CB, CK.Zr, CK.P, CK.Q, CK.tmp, CK.md, CK.c1, CK.c2, CK.Id], by decide⟩
  complete := fun x => by cases x <;> decide

inductive PH
  | tail | pre | cert | o2 | o1
  deriving DecidableEq
instance PH.instFintypeEnumFix : Fintype PH where
  elems := ⟨↑[PH.tail, PH.pre, PH.cert, PH.o2, PH.o1], by decide⟩
  complete := fun x => by cases x <;> decide

namespace PH

def cN : PH → CK
  | tail => .Fn
  | pre => .En
  | cert => .En
  | o2 => .N2
  | o1 => .N1

def cZ : PH → CK
  | tail => .Z6
  | pre => .Z45
  | cert => .Z45
  | o2 => .Z2
  | o1 => .Z1

end PH

inductive CL (g n : ℕ)
  | code
  | inp (c : Fin g)
  | ph (p : PH)
  deriving DecidableEq, Fintype

namespace CL

variable {g n : ℕ}

def nl : CL g n → ℕ
  | ph .cert => n + 1
  | ph .pre => 2
  | _ => 1

def off (ic g' : ℕ) (ycs : List ℕ) : CL g n → ℕ → ℕ
  | code, _ => ic
  | inp c, _ => c
  | ph .cert, l => (0 :: ycs).getD l 0
  | ph .pre, l => if l = 0 then 0 else g'
  | ph _, _ => 0

def sg : CL g n → ℕ → Bool
  | ph .pre, l => decide (l ≠ 0)
  | _, _ => true

def bc : CL g n → CK
  | code => .Zr
  | _ => .CB

theorem bc_ne (c : CL g n) : c.bc ≠ .Q ∧ c.bc ≠ .tmp ∧ c.bc ≠ .P := by
  cases c <;> simp [bc]

theorem nl_le (c : CL g n) : c.nl ≤ n + 2 := by
  rcases c with _ | _ | p
  · simp [nl]
  · simp [nl]
  · cases p <;> simp [nl]

end CL

inductive PS1
  | eg | cpM1 | cpM2 | cpE1 | cpE2 | cpH1 | cpH2 | cpF1 | cpF2 | hg (s : MS)
  | wA | wK | w (s : MS) | wD | inc | v (s : MS)
  deriving DecidableEq, Fintype

inductive PS2
  | zA | zK | z (s : MS) | zD | f1 | f2 | f (s : MS) | s1 | s2 | s (s : MS) | z1
  | t1 | t2 | t3 | t4 | nK | n (s : MS) | nD | qK | q (s : MS) | qD
  deriving DecidableEq, Fintype

inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

inductive GeneratorLabel (g n : ℕ)
  | pre1 (s : PS1) | pre2 (s : PS2)
  | hd (p : PH) | rs (p : PH) | b1 (p : PH) | b2 (p : PH) | bM (p : PH) (s : MS) | dr (p : PH)
  | i3h | i3b1 | i3b2 | i3M (s : MS) | rd (i : Fin g) | i3d | bad
  | e00 (c : CL g n) | cv1 (c : CL g n) | cv2 (c : CL g n)
  | lit (c : CL g n) (l : Fin (n + 2)) (s : LS) | fin (c : CL g n)
  | done
  deriving DecidableEq, Fintype

namespace GeneratorLabel

variable {g n : ℕ}

def litL (c : CL g n) (l : ℕ) : GeneratorLabel g n := if h : l < n + 2 then .lit c ⟨l, h⟩ .cp1 else .done

def after (c : CL g n) (l : ℕ) : GeneratorLabel g n := if l = 0 then .fin c else litL c (l - 1)

def next : PH → GeneratorLabel g n
  | .tail => .hd .pre
  | .pre => .hd .cert
  | .cert => .i3h
  | .o2 => .hd .o1
  | .o1 => .e00 .code

def nextC : CL g n → GeneratorLabel g n
  | .code => .done
  | .inp _ => .i3d
  | .ph p => .dr p

def rd0 : GeneratorLabel g n := if h : 0 < g then .rd ⟨0, h⟩ else .bad

def miss (i : Fin g) : GeneratorLabel g n := if h : i.val + 1 < g then .rd ⟨i.val + 1, h⟩ else .bad

theorem litL_of_lt {c : CL g n} {l : ℕ} (h : l < n + 2) : (litL c l : GeneratorLabel g n) = .lit c ⟨l,
    h⟩ .cp1 :=
  dif_pos h

end GeneratorLabel

section Machine

variable (L : Layout) (ic k0 : ℕ) (ycs : List ℕ)

abbrev Lb := GeneratorLabel L.g ycs.length

def litP (c : CL L.g ycs.length) (l : Fin (ycs.length + 2)) : LS → TM2.Stmt (SΓ CK) (Lb L ycs) Bool
  | .cp1 => xfer (.c c.bc) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.lit c l .cp1) (.lit c l .cp2)
  | .cp2 => xfer (.c .tmp) [⟨.c c.bc, ()⟩] (.lit c l .cp2) (.lit c l .eo)
  | .eo => emitR (.c .Q) (List.replicate (c.off ic L.g ycs l) ()) (.lit c l .dec)
  | .dec => decr (.c .P) (.lit c l .bad) (.lit c l .cmp)
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.lit c l .cmp)
      (.lit c l (.r .lt)) (.lit c l (.r .eq)) (.lit c l (.r .gt))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.lit c l (.r o)) (.lit c l (.rB o))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.lit c l (.rB o))
      (if o = .eq then .lit c l .slot else .lit c l .emL)
  | .emL => emitR .out [false, true] (.lit c l .dec)
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg l))) (.lit c l .dq)
  | .dq => xfer (.c .Q) [] (.lit c l .dq) (GeneratorLabel.after c l)

def prog : Lb L ycs → TM2.Stmt (SΓ CK) (Lb L ycs) Bool
  | .pre1 .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre1 .cpM1)
  | .pre1 .cpM1 => xfer (.c .Xn) [⟨.c .Mm, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpM1) (.pre1 .cpM2)
  | .pre1 .cpM2 => xfer (.c .tmp) [⟨.c .Xn, ()⟩] (.pre1 .cpM2) (.pre1 .cpE1)
  | .pre1 .cpE1 => xfer (.c .En) [⟨.c .Mm, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpE1) (.pre1 .cpE2)
  | .pre1 .cpE2 => xfer (.c .tmp) [⟨.c .En, ()⟩] (.pre1 .cpE2) (.pre1 .cpH1)
  | .pre1 .cpH1 => xfer (.c .Mm) [⟨.c .Hs, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpH1) (.pre1 .cpH2)
  | .pre1 .cpH2 => xfer (.c .tmp) [⟨.c .Mm, ()⟩] (.pre1 .cpH2) (.pre1 .cpF1)
  | .pre1 .cpF1 => xfer (.c .Fn) [⟨.c .Hs, ()⟩, ⟨.c .tmp, ()⟩] (.pre1 .cpF1) (.pre1 .cpF2)
  | .pre1 .cpF2 => xfer (.c .tmp) [⟨.c .Fn, ()⟩] (.pre1 .cpF2) (.pre1 (.hg .head))
  | .pre1 (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre1 (.hg s)) (.pre1 .wA) s
  | .pre1 .wA => emitR (.c .Wc) (List.replicate L.A ()) (.pre1 .wK)
  | .pre1 .wK => emitR (.c .KA) (List.replicate L.KK ()) (.pre1 (.w .head))
  | .pre1 (.w s) => mulS .KA .md .HG .Wc .tmp (fun s => .pre1 (.w s)) (.pre1 .wD) s
  | .pre1 .wD => xfer (.c .KA) [] (.pre1 .wD) (.pre1 .inc)
  | .pre1 .inc => incr (.c .Tn) () (.pre1 (.v .head))
  | .pre1 (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre1 (.v s)) (.pre2 .zA) s
  | .pre2 .zA => emitR (.c .ZA) (List.replicate L.A ()) (.pre2 .zK)
  | .pre2 .zK => emitR (.c .KA) (List.replicate k0 ()) (.pre2 (.z .head))
  | .pre2 (.z s) => mulS .KA .md .HG .ZA .tmp (fun s => .pre2 (.z s)) (.pre2 .zD) s
  | .pre2 .zD => xfer (.c .KA) [] (.pre2 .zD) (.pre2 .f1)
  | .pre2 .f1 => xfer (.c .ZA) [⟨.c .Z45, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .f1) (.pre2 .f2)
  | .pre2 .f2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] (.pre2 .f2) (.pre2 (.f .head))
  | .pre2 (.f s) => mulS .Xn .md .Gc .Z45 .tmp (fun s => .pre2 (.f s)) (.pre2 .s1) s
  | .pre2 .s1 => xfer (.c .ZA) [⟨.c .Z6, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .s1) (.pre2 .s2)
  | .pre2 .s2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] (.pre2 .s2) (.pre2 (.s .head))
  | .pre2 (.s s) => mulS .Mm .md .Gc .Z6 .tmp (fun s => .pre2 (.s s)) (.pre2 .z1) s
  | .pre2 .z1 => emitR (.c .Z1) (List.replicate L.A ()) (.pre2 .t1)
  | .pre2 .t1 => xfer (.c .ZA) [⟨.c .Z2, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .t1) (.pre2 .t2)
  | .pre2 .t2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] (.pre2 .t2) (.pre2 .t3)
  | .pre2 .t3 => xfer (.c .HG) [⟨.c .Z2, ()⟩, ⟨.c .tmp, ()⟩] (.pre2 .t3) (.pre2 .t4)
  | .pre2 .t4 => xfer (.c .tmp) [⟨.c .HG, ()⟩] (.pre2 .t4) (.pre2 .nK)
  | .pre2 .nK => emitR (.c .KA) (List.replicate k0 ()) (.pre2 (.n .head))
  | .pre2 (.n s) => mulS .KA .md .Hs .N1 .tmp (fun s => .pre2 (.n s)) (.pre2 .nD) s
  | .pre2 .nD => xfer (.c .KA) [] (.pre2 .nD) (.pre2 .qK)
  | .pre2 .qK => emitR (.c .KA) (List.replicate (L.KK - k0 - 1) ()) (.pre2 (.q .head))
  | .pre2 (.q s) => mulS .KA .md .Hs .N2 .tmp (fun s => .pre2 (.q s)) (.pre2 .qD) s
  | .pre2 .qD => xfer (.c .KA) [] (.pre2 .qD) (.hd .tail)
  | .hd p => forHead (.c p.cN) (.c .Id) () (.b1 p) (.rs p)
  | .rs p => xfer (.c .Id) [⟨.c p.cN, ()⟩] (.rs p) (GeneratorLabel.next p)
  | .b1 p => xfer (.c p.cZ) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.b1 p) (.b2 p)
  | .b2 p => xfer (.c .tmp) [⟨.c p.cZ, ()⟩] (.b2 p) (.bM p .head)
  | .bM p s => mulS p.cN .md .Gc .CB .tmp (.bM p) (.e00 (.ph p)) s
  | .dr p => xfer (.c .CB) [] (.dr p) (.hd p)
  | .i3h => decr (.c .Xn) (.hd .o2) .i3b1
  | .i3b1 => xfer (.c .ZA) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] .i3b1 .i3b2
  | .i3b2 => xfer (.c .tmp) [⟨.c .ZA, ()⟩] .i3b2 (.i3M .head)
  | .i3M s => mulS .Xn .md .Gc .CB .tmp .i3M GeneratorLabel.rd0 s
  | .rd _ => .halt
  | .i3d => xfer (.c .CB) [] .i3d .i3h
  | .bad => .halt
  | .e00 c => emitR .out [false, false] (.cv1 c)
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.cv1 c) (.cv2 c)
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.cv2 c) (GeneratorLabel.after c c.nl)
  | .lit c l s => litP L ic ycs c l s
  | .fin c => xferE (.c .P) .out [false, true] (.fin c) (GeneratorLabel.nextC c)
  | .done => .halt

def iprog : Lb L ycs → TM2.Stmt (IΓ CK (Fin L.g)) (Lb L ycs) Bool
  | .rd i => rdS (fun c => .e00 (.inp c)) GeneratorLabel.miss i
  | l => mapS liftE id (prog L ic k0 ycs l)

theorem lifts : Embeds liftE id (prog L ic k0 ycs) (iprog L ic k0 ycs) := by
  intro l
  cases l with
  | rd i => exact Or.inr rfl
  | _ => exact Or.inl rfl

def initTM : FinTM2 where
  K := IK CK
  k₀ := .inp
  k₁ := .b .out
  Γ := IΓ CK (Fin L.g)
  Λ := Lb L ycs
  main := .pre1 .eg
  σ := Bool
  initialState := false
  m := iprog L ic k0 ycs

end Machine

section Lits

variable {g n : ℕ} (ic g' : ℕ) (ycs : List ℕ)

def clits (B : ℕ) (c : CL g n) : List (ℕ × Bool) :=
  (List.range c.nl).map fun l => (B + c.off ic g' ycs l, c.sg l)

def WF (c : CL g n) : Prop := ∀ l, l + 1 < c.nl → c.off ic g' ycs l < c.off ic g' ycs (l + 1)

variable {ic g' ycs}

theorem clits_drop (B : ℕ) (c : CL g n) (l : ℕ) :
    (clits ic g' ycs B c).drop l =
      (List.range' l (c.nl - l)).map fun l => (B + c.off ic g' ycs l, c.sg l) := by
  rw [clits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

def bnd (V B : ℕ) (c : CL g n) (l : ℕ) : ℕ := if l < c.nl then B + c.off ic g' ycs l else V

variable (ic g' ycs) in

def InR (V B : ℕ) (c : CL g n) : Prop := ∀ l, l < c.nl → B + c.off ic g' ycs l < V

theorem inc_drop {V B : ℕ} {c : CL g n} (hc : WF ic g' ycs c) (hBV : InR ic g' ycs V B c) (l : ℕ)
    (hl : l ≤ c.nl) : Inc (bnd (ic := ic) (g' := g') (ycs := ycs) V B c l)
      ((clits ic g' ycs B c).drop l) V := by
  rw [clits_drop]
  refine Cslib.Complexity.CookLevin.Family.inc_of_mono _ c.nl V (fun j hj => ?_) (fun j hj => ?_) (c.nl - l) l _
    (by omega) (fun hn => ?_) (fun _ => ?_)
  · simpa using hc j hj
  · exact hBV j (by omega)
  · simp only [bnd]; split_ifs with h
    · omega
    · exact le_rfl
  · simp only [bnd, if_pos (show l < c.nl by omega)]; exact le_rfl

theorem bnd_le {V B : ℕ} {c : CL g n} (hc : WF ic g' ycs c) (hBV : InR ic g' ycs V B c) {l : ℕ}
    (hl : l ≤ c.nl) : bnd (ic := ic) (g' := g') (ycs := ycs) V B c l ≤ V :=
  (inc_drop hc hBV l hl).le

theorem bnd_lt {V B : ℕ} {c : CL g n} (hc : WF ic g' ycs c) (hBV : InR ic g' ycs V B c) {l : ℕ}
    (hl : l < c.nl) : B + c.off ic g' ycs l < bnd (ic := ic) (g' := g') (ycs := ycs) V B c (l + 1) := by
  unfold bnd
  split_ifs with h
  · exact Nat.add_lt_add_left (hc l h) B
  · exact hBV l hl

end Lits

section Clause

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem Rest.upd {F : CK → ℕ} (h : Rest F) {x : CK} (hQ : x ≠ .Q) (ht : x ≠ .tmp) (hm : x ≠ .md)
    (h1 : x ≠ .c1) (h2 : x ≠ .c2) (n : ℕ) : Rest (update F x n) :=
  ⟨by rw [update_of_ne hQ.symm, h.Q], by rw [update_of_ne ht.symm, h.tmp],
    by rw [update_of_ne hm.symm, h.md], by rw [update_of_ne h1.symm, h.c1],
    by rw [update_of_ne h2.symm, h.c2]⟩

theorem lit_run (c : CL L.g ycs.length) (l : Fin (ycs.length + 2)) (F : CK → ℕ) (hF : Rest F)
    (q gap : ℕ) (hq : q = F c.bc + c.off ic L.g ycs l) (hp : F .P = q + gap + 1) (o : List Bool)
    (v : Bool) :
    RunLe (prog L ic k0 ycs) (gap * (3 * q + 6) + 2 * F c.bc + 4 * q + 9)
      ⟨some (.lit c l .cp1), v, st F o⟩
      ⟨some (GeneratorLabel.after c l), false,
        st (update F .P q) (encodeSlot (some (c.sg l)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨b1, b2, b3⟩ := c.bc_ne
  refine Bud.start ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .lit c l .cp1) (l₂ := .lit c l .cp2)
    (next := .lit c l .eo) rfl rfl b1 b2 (by decide) F htmp v o).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .lit c l .eo) (next := .lit c l .dec) rfl _ _
    _).bud ?_
  refine (gapS (M := prog L ic k0 ycs) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true])
    (dec := .lit c l .dec) (cmpL := .lit c l .cmp) (emitL := .lit c l .emL)
    (ifZero := .lit c l .bad) (next := .lit c l .slot) (r := fun o => .lit c l (.r o))
    (rB := fun o => .lit c l (.rB o))
    (out := fun o => if o = .eq then .lit c l .slot else .lit c l .emL)
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L ic k0 ycs) (self := .lit c l .slot) (next := .lit c l .dq) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .lit c l .dq) (next := GeneratorLabel.after c l) (x := .Q)
    rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

def litE (V : ℕ) : ℕ := 6 * V + 9

def clauseB (nm V : ℕ) : ℕ := V * (3 * V + 6) + nm * litE V + 3 * V + 4

theorem lits_run {V B : ℕ} {c : CL L.g ycs.length} (hc : WF ic L.g ycs c)
    (hBV : InR ic L.g ycs V B c) (F : CK → ℕ) (hF : Rest F) (hB : F c.bc = B) (o : List Bool) :
    ∀ l, l ≤ c.nl → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L ic k0 ycs) (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l * (3 * V + 6) +
          l * litE V)
        ⟨some (GeneratorLabel.after c l), v,
          st (update F .P (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l))
            (gapEnc (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l)
              ((clits ic L.g ycs B c).drop l) V ++ [false, false] ++ o)⟩
        ⟨some (.fin c), v',
          st (update F .P (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0))
            (gapEnc (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0) (clits ic L.g ycs B c) V ++
              [false, false] ++ o)⟩ := by
  intro l
  induction l with
  | zero => intro _ v; exact ⟨v, by simpa [GeneratorLabel.after] using RunLe.refl _ _⟩
  | succ l ih =>
      intro hl v
      have hlm : l < c.nl := by omega
      have hln : l < ycs.length + 2 := lt_of_lt_of_le hlm c.nl_le
      obtain ⟨b1, b2, b3⟩ := c.bc_ne
      set p := B + c.off ic L.g ycs l with hp
      set b := bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c (l + 1) with hb
      have hpb : p < b := bnd_lt hc hBV hlm
      have r := lit_run (ic := ic) (k0 := k0) c ⟨l, hln⟩ (update F .P b)
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) b) p (b - p - 1)
        (by rw [update_of_ne b3, hB]) (by simp; omega)
        (gapEnc b ((clits ic L.g ycs B c).drop (l + 1)) V ++ [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GeneratorLabel.after, if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel, GeneratorLabel.litL_of_lt hln]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbl : bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c l = p := by simp [bnd, hlm, hp]
      have hdrop : (clits ic L.g ycs B c).drop l =
          (p, c.sg l) :: (clits ic L.g ycs B c).drop (l + 1) := by
        rw [clits_drop, clits_drop, show c.nl - l = (c.nl - (l + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
      have hshift := Cslib.Complexity.CookLevin.Family.gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop hc hBV (l + 1) hl)
      rw [hbl, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      have hbV := bnd_le hc hBV hl
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * V + 6 by omega)
      have h2 : (b - p - 1) * (3 * V + 6) + p * (3 * V + 6) ≤ b * (3 * V + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      have hBp : B ≤ p := by omega
      rw [update_of_ne b3, hB, Nat.add_one_mul l]
      unfold litE
      omega

theorem clause_run {V B : ℕ} {c : CL L.g ycs.length} (hc : WF ic L.g ycs c)
    (hBV : InR ic L.g ycs V B c) (F : CK → ℕ) (hF : Rest F) (hB : F c.bc = B) (hV : F .Vc = V)
    (hP : F .P = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L ic k0 ycs) (clauseB (ycs.length + 2) V) ⟨some (.e00 c), v, st F o⟩
      ⟨some (GeneratorLabel.nextC c), false,
          st F (encodeClause (denseClause V (clits ic L.g ycs B c)) ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := prog L ic k0 ycs) (self := .e00 c) (next := .cv1 c) rfl _ _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .cv1 c) (l₂ := .cv2 c) (next := GeneratorLabel.after c c.nl)
    rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  obtain ⟨v', r⟩ := lits_run (k0 := k0) hc hBV F hF hB o c.nl le_rfl false
  have hbm : bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c c.nl = V := by simp [bnd]
  rw [hbm, List.drop_eq_nil_of_le (by simp [clits]), gapEnc, Nat.sub_self, rep_zero,
    List.nil_append] at r
  rw [hV, hP, Nat.add_zero]
  refine r.bud ?_
  refine (xferES (M := prog L ic k0 ycs) (self := .fin c) (next := GeneratorLabel.nextC c) (x := .P) rfl _ _
    _).bud ?_
  have e1 : update (update F .P (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop hc hBV 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause V (clits ic L.g ycs B c)) =
      rep [false, true] (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0) ++
        gapEnc (bnd (ic := ic) (g' := L.g) (ycs := ycs) V B c 0) (clits ic L.g ycs B c) V ++
          [false, false] := by
    rw [encodeClause_denseClause (Family.Inc.mono_lo (Nat.zero_le _) h0),
      Cslib.Complexity.CookLevin.Family.gapEnc_shift (Nat.zero_le _) h0, Nat.sub_zero]
  simp only [update_self]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le hc hBV (l := 0) (Nat.zero_le _)
  have := Nat.mul_le_mul_right (litE V) c.nl_le
  unfold clauseB
  omega

end Clause

namespace PH

theorem cN_ne (p : PH) : p.cN ≠ .Q ∧ p.cN ≠ .tmp ∧ p.cN ≠ .md ∧ p.cN ≠ .c1 ∧ p.cN ≠ .c2 ∧
    p.cN ≠ .CB ∧ p.cN ≠ .P ∧ p.cN ≠ .Vc ∧ p.cN ≠ .Gc ∧ p.cN ≠ .Id ∧ p.cN ≠ p.cZ := by
  cases p <;> decide

theorem cZ_ne (p : PH) : p.cZ ≠ .CB ∧ p.cZ ≠ .tmp ∧ p.cZ ≠ .Id ∧ p.cZ ≠ .md := by
  cases p <;> decide

end PH

section Loops

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

def bodyB (nm g N V : ℕ) : ℕ :=
  2 * V + 2 + (N * (2 * g + 3) + N + 2) + g + 1 + clauseB nm V + V + 1

theorem body_run {p : PH} {V Z N t : ℕ} (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hZ : F p.cZ = Z) (ht : F p.cN = t)
    (htN : t < N) (hBV : t * L.g + Z ≤ V) (hW : WF ic L.g ycs (CL.ph p : CL L.g ycs.length))
    (hR : InR ic L.g ycs V (t * L.g + Z) (CL.ph p : CL L.g ycs.length)) (o : List Bool)
    (v : Bool) :
    RunLe (prog L ic k0 ycs) (bodyB (ycs.length + 2) L.g N V) ⟨some (.b1 p), v, st F o⟩
      ⟨some (.hd p), false,
        st F (encodeClause (denseClause V (clits ic L.g ycs (t * L.g + Z)
          (CL.ph p : CL L.g ycs.length))) ++ o)⟩ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := p.cN_ne
  obtain ⟨z1, z2, z3, z4⟩ := p.cZ_ne
  refine Bud.start ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .b1 p) (l₂ := .b2 p) (next := .bM p .head) rfl rfl
    z1 z2 (by decide) F hF.tmp v o).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := .bM p) (next := .e00 (.ph p)) (a := p.cN)
    (ad := .md) (b := .Gc) (c := .CB) (t := .tmp) (fun _ => rfl) (by cases p <;> decide) _
    (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := update F .CB (t * L.g + Z))
    (by rw [update_idem]; simp [n6, ht, hG, hZ, hCB]) ?_
  have hF' : Rest (update F .CB (t * L.g + Z)) :=
    hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _
  refine (clause_run (k0 := k0) (c := .ph p) hW hR _ hF' (by simp [CL.bc]) (by simp [hV])
    (by simp [hP]) o _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .dr p) (next := .hd p) (x := .CB) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 : t * (2 * L.g + 3) ≤ N * (2 * L.g + 3) := Nat.mul_le_mul_right _ htN.le
    simp only [update_self, update_apply, n6, reduceCtorEq, if_false, hZ, hCB, ht, hG]
    unfold bodyB
    omega
  · rw [update_idem, update_eq_self_iff.2 hCB.symm]

theorem phase_run {p : PH} {V Z N Nb : ℕ} (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hZ : F p.cZ = Z) (hN : F p.cN = N)
    (hId : F .Id = 0) (hNb : N ≤ Nb) (hW : WF ic L.g ycs (CL.ph p : CL L.g ycs.length))
    (hBV : ∀ t < N, t * L.g + Z ≤ V)
    (hR : ∀ t < N, InR ic L.g ycs V (t * L.g + Z) (CL.ph p : CL L.g ycs.length)) (o : List Bool)
    (v : Bool) :
    RunLe (prog L ic k0 ycs) (Nb * (bodyB (ycs.length + 2) L.g Nb V + 1) + Nb + 2)
      ⟨some (.hd p), v, st F o⟩
      ⟨some (GeneratorLabel.next p), false, st F ((List.range N).flatMap
        (fun t => encodeClause (denseClause V (clits ic L.g ycs (t * L.g + Z)
          (CL.ph p : CL L.g ycs.length)))) ++ o)⟩ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := p.cN_ne
  obtain ⟨z1, z2, z3, z4⟩ := p.cZ_ne
  refine (stLoop (M := prog L ic k0 ycs) (c := p.cN) (cd := .Id) (head := .hd p) (body := .b1 p)
    (rest := .rs p) (next := GeneratorLabel.next p) rfl rfl n10 N (bodyB (ycs.length + 2) L.g Nb V) _ F hN hId
    (fun t ht o => ⟨false, ?_⟩) v o).mono ?_
  · have hF' : Rest (update (update F p.cN t) .Id (N - t)) :=
      (hF.upd n1 n2 n3 n4 n5 t).upd (by decide) (by decide) (by decide) (by decide) (by decide) _
    exact body_run (k0 := k0) _ hF' (by simp [n6.symm, hCB])
      (by simp [n7.symm, hP]) (by simp [n8.symm, hV])
      (by simp [n9.symm, hG]) (by simp [n11.symm, z3, hZ])
      (by rw [update_of_ne n10, update_self]) (by omega) (hBV t ht) hW (hR t ht) o true
  · have := Nat.mul_le_mul_right (bodyB (ycs.length + 2) L.g Nb V + 1) hNb
    omega

theorem i3pre_run {r ZA : ℕ} (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0) (hG : F .Gc = L.g)
    (hZA : F .ZA = ZA) (hX : F .Xn = r + 1) (o : List Bool) (v : Bool) :
    RunLe (prog L ic k0 ycs) (1 + (2 * ZA + 2) + (r * (2 * L.g + 3) + r + 2))
      ⟨some .i3h, v, st F o⟩
      ⟨some GeneratorLabel.rd0, false, st (update (update F .Xn r) .CB (r * L.g + ZA)) o⟩ := by
  refine Bud.start ?_
  have d := decr_run_cnt (M := prog L ic k0 ycs) (self := .i3h) (ifZero := .hd .o2)
    (ifPos := .i3b1) (k := .c .Xn) (u := ()) rfl v (S := st F o) (n := r) (by simp [hX])
  rw [CounterView.update_st_c] at d
  refine d.bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .i3b1) (l₂ := .i3b2) (next := .i3M .head) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ o).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := .i3M) (next := GeneratorLabel.rd0) (a := .Xn)
    (ad := .md) (b := .Gc) (c := .CB) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hZA, hG]
  · congr 2
    rw [update_idem]
    simp [hG, hZA, hCB]

end Loops

section I3

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

theorem clits_inp {g n : ℕ} (B : ℕ) (c : Fin g) :
    clits ic L.g ycs B (CL.inp c : CL g n) = [(B + c.val, true)] := by
  simp [clits, CL.nl, CL.off, CL.sg]

theorem i3_run {V ZA Nb : ℕ} (xs : List (Fin L.g)) (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0)
    (hP : F .P = 0) (hV : F .Vc = V) (hG : F .Gc = L.g) (hZA : F .ZA = ZA)
    (hR : ∀ j < xs.length, j * L.g + ZA + L.g ≤ V) (hNb : xs.length ≤ Nb) :
    ∀ r, r ≤ xs.length → ∀ (o : List Bool) (v : Bool),
      RunLe (iprog L ic k0 ycs) (r * bodyB (ycs.length + 2) L.g Nb V + 1)
        ⟨some .i3h, v, emb (st (update F .Xn r) o) (xs.take r).reverse⟩
        ⟨some (.hd .o2), false, emb (st (update F .Xn 0) ((List.range r).flatMap
          (fun j => encodeClause (denseClause V
            [(j * L.g + ZA + (xs[j]?).elim 0 Fin.val, true)])) ++ o)) []⟩ := by
  intro r
  induction r with
  | zero =>
      intro _ o v
      have d := decr_run_zero (M := prog L ic k0 ycs) (self := .i3h) (ifZero := .hd .o2)
        (ifPos := .i3b1) (k := .c .Xn) rfl v (S := st (update F .Xn 0) o) (by simp)
      have := runLe_lift (lifts L ic k0 ycs) [] (d.le le_rfl)
      simp only [List.take_zero, List.reverse_nil, List.range_zero, List.flatMap_nil,
        List.nil_append, zero_mul, zero_add]
      exact this
  | succ r ih =>
      intro hr o v
      have hrx : r < xs.length := by omega
      set c := xs[r] with hc
      have hg : 0 < L.g := lt_of_le_of_lt (Nat.zero_le _) c.2
      have hB := hR r hrx
      have hcg := c.2

      have r1 := i3pre_run (L := L) (k0 := k0) (ic := ic) (ycs := ycs) (r := r) (ZA := ZA)
        (update F .Xn (r + 1))
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _)
        (by simp [hCB]) (by simp [hG]) (by simp [hZA]) (by simp) o v
      rw [GeneratorLabel.rd0, dif_pos hg, update_idem] at r1
      have htake : (xs.take (r + 1)).reverse = c :: (xs.take r).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem hrx]; simp [hc]
      have l1 := runLe_lift (lifts L ic k0 ycs) (c :: (xs.take r).reverse) r1
      rw [htake]
      refine Bud.start (l1.bud ?_)

      have rd := read_run (M' := iprog L ic k0 ycs) (rd := GeneratorLabel.rd)
        (hit := fun c => GeneratorLabel.e00 (CL.inp c)) (miss := GeneratorLabel.miss) (fun _ => rfl)
        (fun i h => dif_pos h) (st (update (update F .Xn r) .CB (r * L.g + ZA)) o) c
        (xs.take r).reverse c.val ⟨0, hg⟩ (by simp) false
      refine (rd.bud ?_)

      set F2 := update (update F .Xn r) .CB (r * L.g + ZA) with hF2
      have hF2r : Rest F2 :=
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _).upd
          (by decide) (by decide) (by decide) (by decide) (by decide) _
      have cl := clause_run (L := L) (ic := ic) (k0 := k0) (ycs := ycs) (V := V)
        (B := r * L.g + ZA) (c := (CL.inp c : CL L.g ycs.length))
        (fun l hl => by simp [CL.nl] at hl)
        (fun l hl => by simp only [CL.off]; omega) F2 hF2r (by simp [hF2, CL.bc])
        (by simp [hF2, hV]) (by simp [hF2, hP]) o true
      have dr := drainS (M := prog L ic k0 ycs) (self := .i3d) (next := .i3h) (x := .CB) rfl F2
        false (encodeClause (denseClause V (clits ic L.g ycs (r * L.g + ZA) (CL.inp c : CL L.g ycs.length))) ++ o)
      have e2 : update F2 .CB 0 = update F .Xn r := by
        rw [hF2, update_idem]
        exact update_eq_self_iff.2 (by simp [hCB])
      rw [e2] at dr
      have l2 := runLe_lift (lifts L ic k0 ycs) (xs.take r).reverse ((cl.trans (dr.le le_rfl)))
      refine (l2.bud ?_)
      have l3 := ih (Nat.le_of_succ_le hr) (encodeClause (denseClause V
        (clits ic L.g ycs (r * L.g + ZA) (CL.inp c : CL L.g ycs.length))) ++ o) false
      refine (l3.bud (Bud.fin ?_ ?_))
      · simp only [hF2, update_self]
        rw [Nat.add_one_mul r]
        have h1 : r * (2 * L.g + 3) ≤ Nb * (2 * L.g + 3) := Nat.mul_le_mul_right _ (by omega)
        unfold bodyB
        omega
      · rw [clits_inp, List.range_succ, List.flatMap_append, List.flatMap_singleton,
          List.getElem?_eq_getElem hrx]
        simp only [Option.elim_some, List.append_assoc, hc]

end I3

section Kinds

variable {g n : ℕ} {ic g' : ℕ} {ycs : List ℕ}

theorem clits_code (B : ℕ) : clits ic g' ycs B (CL.code : CL g n) = [(B + ic, true)] := by
  simp [clits, CL.nl, CL.off, CL.sg]

theorem clits_unit (B : ℕ) {p : PH} (hp : p = .tail ∨ p = .o1 ∨ p = .o2) :
    clits ic g' ycs B (CL.ph p : CL g n) = [(B, true)] := by
  rcases hp with rfl | rfl | rfl <;> simp [clits, CL.nl, CL.off, CL.sg]

theorem clits_pre (B : ℕ) : clits ic g' ycs B (CL.ph .pre : CL g n) = [(B, false), (B + g',
    true)] := by
  simp [clits, CL.nl, CL.off, CL.sg, List.range_succ]

theorem map_range_getD {α : Type} (l : List ℕ) (f : ℕ → α) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem clits_cert (B : ℕ) :
    clits ic g' ycs B (CL.ph .cert : CL g ycs.length) =
      (B, true) :: ycs.map fun c => (B + c, true) := by
  have := map_range_getD (0 :: ycs) (fun c => (B + c, true))
  simp only [List.length_cons, List.map_cons, Nat.add_zero] at this
  simpa [clits, CL.nl, CL.off, CL.sg] using this

theorem wf_unit {c : CL g n} (hc : c.nl = 1) : WF ic g' ycs c := fun l hl => by omega

theorem wf_pre (hg : 0 < g') : WF ic g' ycs (CL.ph .pre : CL g n) := by
  intro l hl
  simp only [CL.nl] at hl
  obtain rfl : l = 0 := by omega
  simpa [CL.off] using hg

theorem wf_cert (hy : (0 :: ycs).Pairwise (· < ·)) : WF ic g' ycs (CL.ph .cert : CL g ycs.length) := by
  intro l hl
  simp only [CL.nl] at hl
  simp only [CL.off]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
  exact List.pairwise_iff_getElem.1 hy l (l + 1) (by simp; omega) (by simp; omega) (by omega)

theorem inr_unit {c : CL g n} (hc : c.nl = 1) {V B : ℕ} (h : B + c.off ic g' ycs 0 < V) :
    InR ic g' ycs V B c := fun l hl => by obtain rfl : l = 0 := by omega
                                          exact h

theorem inr_pre {V B : ℕ} (h : B + g' < V) : InR ic g' ycs V B (CL.ph .pre : CL g n) := by
  intro l hl
  simp only [CL.nl] at hl
  simp only [CL.off]
  split_ifs <;> omega

theorem inr_cert (hyg : ∀ c ∈ ycs, c < g') {V B : ℕ} (h : B + g' ≤ V) (hg : 0 < g') :
    InR ic g' ycs V B (CL.ph .cert : CL g ycs.length) := by
  intro l hl
  simp only [CL.nl] at hl
  simp only [CL.off]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  have : (0 :: ycs)[l]'(by simp; omega) < g' := by
    have hm := List.getElem_mem (show l < (0 :: ycs).length by simp; omega)
    rcases List.mem_cons.1 hm with h0 | h0
    · rw [h0]; exact hg
    · exact hyg _ h0
  omega

end Kinds

section Out

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

theorem cIdx0 (H k j x : ℕ) : L.cIdx H 0 k j x = L.A + (k * H + j) * L.g + x := by
  simp [Layout.cIdx]

theorem qpos {T H q : ℕ} (hq : q < L.KK * H) : L.A + q * L.g + L.g ≤ L.numVars T H := by
  unfold Layout.numVars Layout.rowW
  have h1 : q * L.g + L.g ≤ L.KK * (H * L.g) := by
    rw [← Nat.succ_mul, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hq
  have h2 : L.A + L.KK * (H * L.g) ≤ (T + 1) * (L.A + L.KK * (H * L.g)) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

theorem kq_lt {H k j : ℕ} (hk : k < L.KK) (hj : j < H) : k * H + j < L.KK * H := by
  have : k * H + H ≤ L.KK * H := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  omega

theorem enc_code (T H : ℕ) :
    encodeCNF (iCode L ic T H) = encodeClause (denseClause (L.numVars T H)
      (clits ic L.g ycs 0 (CL.code : CL L.g ycs.length))) := by
  simp [encodeCNF, iCode, clits_code, Layout.xIdx]

theorem enc_tail (m T H : ℕ) :
    encodeCNF (iTail L k0 m T H) = (List.range (H - m)).flatMap (fun t => encodeClause
      (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 k0 m 0)
        (CL.ph .tail : CL L.g ycs.length)))) := by
  simp only [encodeCNF, iTail, List.flatMap_map]
  congr 1; funext t
  rw [clits_unit _ (Or.inl rfl), zB, cIdx0, cIdx0]
  congr 4; ring1

theorem enc_pre (n m T H : ℕ) :
    encodeCNF (iPre L k0 n m T H) = (List.range (m - n)).flatMap (fun t => encodeClause
      (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 k0 n 0)
        (CL.ph .pre : CL L.g ycs.length)))) := by
  simp only [encodeCNF, iPre, List.flatMap_map]
  congr 1; funext t
  rw [clits_pre, zB, zB, cIdx0, cIdx0, cIdx0]
  congr 4
  · ring1
  · congr 1; ring1

theorem enc_cert (n m T H : ℕ) :
    encodeCNF (iCert L k0 ycs n m T H) = (List.range (m - n)).flatMap (fun t => encodeClause
      (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 k0 n 0)
        (CL.ph .cert : CL L.g ycs.length)))) := by
  simp only [encodeCNF, iCert, List.flatMap_map]
  congr 1; funext t
  rw [clits_cert, zB, cIdx0, cIdx0]
  have e : t * L.g + (L.A + (k0 * H + n) * L.g + 0) = L.A + (k0 * H + (n + t)) * L.g := by ring1
  rw [e]
  simp [cIdx0]

theorem enc_in (xs : List (Fin L.g)) (T H : ℕ) :
    encodeCNF (iIn L k0 xs T H) = (List.range xs.length).flatMap (fun j => encodeClause
      (denseClause (L.numVars T H) [(j * L.g + L.cIdx H 0 k0 0 0 + (xs[j]?).elim 0 Fin.val,
          true)])) := by
  simp only [encodeCNF, iIn, List.flatMap_map]
  congr 1; funext j
  rw [cIdx0, cIdx0]
  congr 4; ring1

theorem flat_blocks {α : Type} (H : ℕ) (φ : ℕ → α) (s : ℕ) : ∀ r : ℕ,
    ((List.range r).map (s + ·)).flatMap (fun k => (List.range H).map fun j => φ (k * H + j)) =
      (List.range (r * H)).map fun q => φ (s * H + q)
  | 0 => by simp
  | r + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flat_blocks H φ s r, Nat.add_one_mul,
      List.range_add, List.map_append, List.map_map]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    congr 1; ring1

theorem filter_ne_range {k0 KK : ℕ} (hk : k0 < KK) :
    (List.range KK).filter (· ≠ k0) = (List.range k0).map (0 + ·) ++
      (List.range (KK - k0 - 1)).map ((k0 + 1) + ·) := by
  conv_lhs => rw [show KK = k0 + 1 + (KK - k0 - 1) by omega, List.range_add, List.range_succ]
  rw [List.filter_append, List.filter_append, List.filter_singleton]
  simp only [ne_eq, not_true_eq_false, decide_false, cond_false, List.append_nil, zero_add,
    List.map_id']
  congr 1
  · exact List.filter_eq_self.2 (fun a ha => by simp at ha; simp; omega)
  · exact List.filter_eq_self.2 (fun a ha => by simp at ha; obtain ⟨b, -, rfl⟩ := ha; simp; omega)

theorem enc_other (hk0 : k0 < L.KK) (T H : ℕ) :
    encodeCNF (iOther L k0 T H) =
      (List.range (k0 * H)).flatMap (fun t => encodeClause (denseClause (L.numVars T H)
        (clits ic L.g ycs (t * L.g + L.A) (CL.ph .o1 : CL L.g ycs.length)))) ++
      (List.range ((L.KK - k0 - 1) * H)).flatMap (fun t => encodeClause
        (denseClause (L.numVars T H) (clits ic L.g ycs (t * L.g + L.cIdx H 0 (k0 + 1) 0 0)
          (CL.ph .o2 : CL L.g ycs.length)))) := by
  have e : iOther L k0 T H = ((List.range L.KK).filter (· ≠ k0)).flatMap fun k =>
      (List.range H).map fun j => (fun q => denseClause (L.numVars T H) [(L.A + q * L.g, true)])
        (k * H + j) := by
    unfold iOther; congr 1; funext k; congr 1; funext j; rw [cIdx0]; simp
  rw [e, filter_ne_range hk0, List.flatMap_append,
    flat_blocks H (fun q => denseClause (L.numVars T H) [(L.A + q * L.g, true)]) 0 k0,
    flat_blocks H (fun q => denseClause (L.numVars T H) [(L.A + q * L.g, true)]) (k0 + 1)]
  simp only [encodeCNF, List.flatMap_append, List.flatMap_map]
  congr 1
  · congr 1; funext t; rw [clits_unit _ (Or.inr (Or.inl rfl))]; congr 4; ring1
  · congr 1; funext t; rw [clits_unit _ (Or.inr (Or.inr rfl)), cIdx0]; congr 4; ring1

end Out

section Top

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

def initF (T n e f : ℕ) : CK → ℕ
  | .Tn => T
  | .Xn => n
  | .En => e
  | .Fn => f
  | _ => 0

def preF (L : Layout) (k0 T n e f : ℕ) : CK → ℕ
  | .Tn => T + 1
  | .Xn => n
  | .En => e
  | .Fn => f
  | .Gc => L.g
  | .Mm => n + e
  | .Hs => n + e + f
  | .HG => (n + e + f) * L.g
  | .Wc => L.rowW (n + e + f)
  | .Vc => L.numVars T (n + e + f)
  | .ZA => L.cIdx (n + e + f) 0 k0 0 0
  | .Z45 => L.cIdx (n + e + f) 0 k0 n 0
  | .Z6 => L.cIdx (n + e + f) 0 k0 (n + e) 0
  | .Z1 => L.A
  | .Z2 => L.cIdx (n + e + f) 0 (k0 + 1) 0 0
  | .N1 => k0 * (n + e + f)
  | .N2 => (L.KK - k0 - 1) * (n + e + f)
  | _ => 0

def preB (L : Layout) (k0 q T n e f : ℕ) : ℕ :=
  1 + (2 * n + 2) + (2 * e + 2) + (2 * (n + e) + 2) + (2 * f + 2) +
    ((n + e + f) * (2 * L.g + 3) + (n + e + f) + 2) + 1 + 1 +
    (L.KK * (2 * ((n + e + f) * L.g) + 3) + L.KK + 2) + (L.KK + 1) + 1 +
    ((T + 1) * (2 * (L.KK * ((n + e + f) * L.g) + L.A) + 3) + (T + 1) + 2) + 1 + 1 +
    (k0 * (2 * ((n + e + f) * L.g) + 3) + k0 + 2) + (k0 + 1) +
    (2 * (k0 * ((n + e + f) * L.g) + L.A) + 2) + (n * (2 * L.g + 3) + n + 2) +
    (2 * (k0 * ((n + e + f) * L.g) + L.A) + 2) + ((n + e) * (2 * L.g + 3) + (n + e) + 2) + 1 +
    (2 * (k0 * ((n + e + f) * L.g) + L.A) + 2) + (2 * ((n + e + f) * L.g) + 2) + 1 +
    (k0 * (2 * (n + e + f) + 3) + k0 + 2) + (k0 + 1) + 1 +
    (q * (2 * (n + e + f) + 3) + q + 2) + (q + 1)

set_option maxHeartbeats 1600000 in

theorem pre_run (T n e f : ℕ) (o : List Bool) :
    RunLe (prog L ic k0 ycs) (preB L k0 (L.KK - k0 - 1) T n e f)
      ⟨some (.pre1 .eg), false, st (initF T n e f) o⟩
      ⟨some (.hd .tail), false, st (preF L k0 T n e f) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre1 .eg) (next := .pre1 .cpM1) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpM1) (l₂ := .pre1 .cpM2)
    (next := .pre1 .cpE1) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpE1) (l₂ := .pre1 .cpE2)
    (next := .pre1 .cpH1) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpH1) (l₂ := .pre1 .cpH2)
    (next := .pre1 .cpF1) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre1 .cpF1) (l₂ := .pre1 .cpF2)
    (next := .pre1 (.hg .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _
    _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre1 (.hg s)) (next := .pre1 .wA)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre1 .wA) (next := .pre1 .wK) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre1 .wK) (next := .pre1 (.w .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre1 (.w s)) (next := .pre1 .wD)
    (a := .KA) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre1 .wD) (next := .pre1 .inc) (x := .KA) rfl _ _
    _).bud ?_
  refine (incS (M := prog L ic k0 ycs) (self := .pre1 .inc) (next := .pre1 (.v .head)) (x := .Tn)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre1 (.v s)) (next := .pre2 .zA)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .zA) (next := .pre2 .zK) (x := .ZA) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .zK) (next := .pre2 (.z .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.z s)) (next := .pre2 .zD)
    (a := .KA) (ad := .md) (b := .HG) (c := .ZA) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre2 .zD) (next := .pre2 .f1) (x := .KA) rfl _ _
    _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .f1) (l₂ := .pre2 .f2)
    (next := .pre2 (.f .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _
    _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.f s)) (next := .pre2 .s1)
    (a := .Xn) (ad := .md) (b := .Gc) (c := .Z45) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .s1) (l₂ := .pre2 .s2)
    (next := .pre2 (.s .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _
    _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.s s)) (next := .pre2 .z1)
    (a := .Mm) (ad := .md) (b := .Gc) (c := .Z6) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .z1) (next := .pre2 .t1) (x := .Z1) rfl _ _
    _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .t1) (l₂ := .pre2 .t2)
    (next := .pre2 .t3) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L ic k0 ycs) (l₁ := .pre2 .t3) (l₂ := .pre2 .t4)
    (next := .pre2 .nK) rfl rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .nK) (next := .pre2 (.n .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.n s)) (next := .pre2 .nD)
    (a := .KA) (ad := .md) (b := .Hs) (c := .N1) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre2 .nD) (next := .pre2 .qK) (x := .KA) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L ic k0 ycs) (self := .pre2 .qK) (next := .pre2 (.q .head)) (x := .KA)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L ic k0 ycs) (mk := fun s => .pre2 (.q s)) (next := .pre2 .qD)
    (a := .KA) (ad := .md) (b := .Hs) (c := .N2) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L ic k0 ycs) (self := .pre2 .qD) (next := .hd .tail) (x := .KA) rfl _ _
    _).bud ?_
  refine bud_st (F' := preF L k0 T n e f) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars, Layout.cIdx] <;>
      first | ring1 | (left; ring1)) (Bud.fin ?_ rfl)
  simp [initF, preB]
  ring_nf
  omega

end Top

theorem i3_full {L : Layout} {ic k0 : ℕ} {ycs : List ℕ} {V ZA Nb : ℕ} (xs : List (Fin L.g))
    (F : CK → ℕ) (hF : Rest F) (hCB : F .CB = 0) (hP : F .P = 0) (hV : F .Vc = V)
    (hG : F .Gc = L.g) (hZA : F .ZA = ZA) (hX : F .Xn = xs.length)
    (hR : ∀ j < xs.length, j * L.g + ZA + L.g ≤ V) (hNb : xs.length ≤ Nb) (o : List Bool)
    (v : Bool) :
    RunLe (iprog L ic k0 ycs) (xs.length * bodyB (ycs.length + 2) L.g Nb V + 1)
      ⟨some .i3h, v, emb (st F o) xs.reverse⟩
      ⟨some (.hd .o2), false, emb (st (update F .Xn 0) ((List.range xs.length).flatMap
        (fun j => encodeClause (denseClause V
          [(j * L.g + ZA + (xs[j]?).elim 0 Fin.val, true)])) ++ o)) []⟩ := by
  have := i3_run (ic := ic) (k0 := k0) (ycs := ycs) xs F hF hCB hP hV hG hZA hR hNb xs.length
    le_rfl o v
  rwa [List.take_length,
    show update F .Xn xs.length = F from update_eq_self_iff.2 hX.symm] at this

section Gen

variable {L : Layout} {ic k0 : ℕ} {ycs : List ℕ}

def loopB (nm g NB V : ℕ) : ℕ := NB * (bodyB nm g NB V + 1) + NB + 2

def initBound (L : Layout) (nY k0 q T n e f : ℕ) : ℕ :=
  preB L k0 q T n e f +
    6 * loopB (nY + 2) L.g (L.KK * (n + e + f) + (n + e + f)) (L.numVars T (n + e + f)) +
    clauseB (nY + 2) (L.numVars T (n + e + f))

theorem shiftC (H k j t : ℕ) : t * L.g + L.cIdx H 0 k j 0 = L.A + (k * H + (j + t)) * L.g := by
  rw [cIdx0]; ring1

theorem enc_initFam (hk0 : k0 < L.KK) (xs : List (Fin L.g)) (e f T : ℕ) :
    encodeCNF (initFam L ic k0 ycs xs (xs.length + e) T (xs.length + e + f)) =
      encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs 0 (CL.code : CL L.g ycs.length))) ++
      ((List.range (k0 * (xs.length + e + f))).flatMap (fun t => encodeClause
          (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.A) (CL.ph .o1 : CL L.g ycs.length)))) ++
      ((List.range ((L.KK - k0 - 1) * (xs.length + e + f))).flatMap (fun t => encodeClause
          (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 (k0 + 1) 0 0)
            (CL.ph .o2 : CL L.g ycs.length)))) ++
      ((List.range xs.length).flatMap (fun j => encodeClause
          (denseClause (L.numVars T (xs.length + e + f))
          [(j * L.g + L.cIdx (xs.length + e + f) 0 k0 0 0 + (xs[j]?).elim 0 Fin.val, true)])) ++
      ((List.range e).flatMap (fun t => encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 k0 xs.length 0)
            (CL.ph .cert : CL L.g ycs.length)))) ++
      ((List.range e).flatMap (fun t => encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 k0 xs.length 0)
            (CL.ph .pre : CL L.g ycs.length)))) ++
      (List.range f).flatMap (fun t => encodeClause (denseClause (L.numVars T (xs.length + e + f))
          (clits ic L.g ycs (t * L.g + L.cIdx (xs.length + e + f) 0 k0 (xs.length + e) 0)
            (CL.ph .tail : CL L.g ycs.length))))))))) := by
  have hfa : ∀ a b : CNF, encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b :=
    fun a b => List.flatMap_append
  rw [initFam, hfa, hfa, hfa, hfa, hfa, enc_code (ycs := ycs),
      enc_other (ic := ic) (ycs := ycs) hk0,
    enc_in, enc_cert (ic := ic), enc_pre (ic := ic) (ycs := ycs),
    enc_tail (ic := ic) (ycs := ycs), Nat.add_sub_cancel_left,
    show xs.length + e + f - (xs.length + e) = f by omega]
  simp only [List.append_assoc]

theorem init_run (hk0 : k0 < L.KK) (hic : ic < L.A) (hg : 0 < L.g)
    (hy : (0 :: ycs).Pairwise (· < ·)) (hyg : ∀ c ∈ ycs, c < L.g) (xs : List (Fin L.g))
    (T e f : ℕ) (hf : 0 < f) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin L.g) k)),
      RunLe (iprog L ic k0 ycs) (initBound L ycs.length k0 (L.KK - k0 - 1) T xs.length e f)
        ⟨some (.pre1 .eg), false, emb (st (initF T xs.length e f) o) xs.reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (initFam L ic k0 ycs xs (xs.length + e) T (xs.length + e + f)) ++ o := by
  have lf := lifts L ic k0 ycs
  have hR0 : Rest (preF L k0 T xs.length e f) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hR1 : Rest (update (preF L k0 T xs.length e f) .Xn 0) :=
    hR0.upd (by decide) (by decide) (by decide) (by decide) (by decide) 0

  have posA : ∀ k j, k < L.KK → j < xs.length + e + f →
      L.A + (k * (xs.length + e + f) + j) * L.g + L.g ≤ L.numVars T (xs.length + e + f) :=
    fun k j hk hj => qpos (kq_lt hk hj)
  have hAV : L.A ≤ L.numVars T (xs.length + e + f) := by
    unfold Layout.numVars Layout.rowW
    exact le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hNB : xs.length + e + f ≤ L.KK * (xs.length + e + f) + (xs.length + e + f) :=
    Nat.le_add_left _ _
  have hk2 : (k0 + 1) * (xs.length + e + f) + (L.KK - k0 - 1) * (xs.length + e + f) =
      L.KK * (xs.length + e + f) := by rw [← Nat.add_mul]; congr 1; omega
  have hk1 : k0 * (xs.length + e + f) ≤ L.KK * (xs.length + e + f) :=
    Nat.mul_le_mul_right _ hk0.le
  refine ⟨false, ?_⟩
  apply Exists.intro
  refine And.intro ?run ?eq
  case run =>
    refine Bud.start ((runLe_lift lf xs.reverse
      (pre_run (ic := ic) (ycs := ycs) T xs.length e f o)).bud ?_)

    refine (runLe_lift lf xs.reverse (phase_run (p := .tail) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR0 rfl rfl rfl
      rfl rfl rfl rfl (by first | omega | (simp only [PH.cN, preF]; omega)) (wf_unit rfl)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + e + t) hk0 (by omega)
        omega)
      (fun t ht => inr_unit rfl (by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢; simp only [CL.off]; rw [Nat.add_zero, shiftC]
        have := posA k0 (xs.length + e + t) hk0 (by omega)
        omega)) _ _)).bud ?_

    refine (runLe_lift lf xs.reverse (phase_run (p := .pre) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR0 rfl rfl rfl
      rfl rfl rfl rfl (by first | omega | (simp only [PH.cN, preF]; omega)) (wf_pre hg)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + t) hk0 (by omega)
        omega)
      (fun t ht => inr_pre (by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢; rw [shiftC]
        have := posA k0 (xs.length + t + 1) hk0 (by omega)
        have e1 : (k0 * (xs.length + e + f) + (xs.length + t + 1)) * L.g =
            (k0 * (xs.length + e + f) + (xs.length + t)) * L.g + L.g := by ring1
        omega)) _ _)).bud ?_

    refine (runLe_lift lf xs.reverse (phase_run (p := .cert) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR0 rfl rfl rfl
      rfl rfl rfl rfl (by first | omega | (simp only [PH.cN, preF]; omega)) (wf_cert hy)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + t) hk0 (by omega)
        omega)
      (fun t ht => inr_cert hyg (by
        simp only [PH.cZ, PH.cN, preF] at ht ⊢
        rw [shiftC]; have := posA k0 (xs.length + t) hk0 (by omega)
        omega) hg) _ _)).bud ?_

    refine (i3_full (ic := ic) (k0 := k0) (ycs := ycs) xs _ hR0 rfl rfl rfl rfl rfl rfl
      (fun j hj => by
        simp only [preF]; rw [shiftC]; have := posA k0 (0 + j) hk0 (by omega)
        omega) (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) (by omega) _ _).bud ?_

    refine (runLe_lift lf [] (phase_run (p := .o2) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR1 rfl rfl rfl
      rfl rfl rfl rfl (by simp only [PH.cN, preF, update_apply]; simp; omega) (wf_unit rfl)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, if_false] at ht ⊢
        rw [shiftC]; have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := (k0 + 1) * (xs.length + e + f) + (0 + t))
          (by omega)
        omega)
      (fun t ht => inr_unit rfl (by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, if_false] at ht ⊢
        simp only [CL.off]; rw [Nat.add_zero, shiftC]
        have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := (k0 + 1) * (xs.length + e + f) + (0 + t)) (by omega)
        omega)) _ _)).bud ?_

    refine (runLe_lift lf [] (phase_run (p := .o1) (k0 := k0)
      (Nb := L.KK * (xs.length + e + f) + (xs.length + e + f)) _ hR1 rfl rfl rfl
      rfl rfl rfl rfl (by simp only [PH.cN, preF, update_apply]; simp; omega) (wf_unit rfl)
      (fun t ht => by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, if_false] at ht ⊢
        have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := t) (by omega)
        omega)
      (fun t ht => inr_unit rfl (by
        simp only [PH.cZ, PH.cN, preF, update_apply, reduceCtorEq, if_false] at ht ⊢
        simp only [CL.off]
        have := qpos (L := L) (T := T) (H := xs.length + e + f) (q := t) (by omega)
        omega)) _ _)).bud ?_

    refine (runLe_lift lf [] (clause_run (k0 := k0) (c := (CL.code : CL L.g ycs.length)) (B := 0)
      (wf_unit rfl) (inr_unit rfl (by simp [CL.off, preF]; omega)) _ hR1 rfl rfl rfl _ _)).bud ?_
    refine Bud.fin ?_ rfl
    have h3 : xs.length * bodyB (ycs.length + 2) L.g (L.KK * (xs.length + e + f) +
        (xs.length + e + f)) (L.numVars T (xs.length + e + f)) ≤
        (L.KK * (xs.length + e + f) + (xs.length + e + f)) * (bodyB (ycs.length + 2) L.g
          (L.KK * (xs.length + e + f) + (xs.length + e + f)) (L.numVars T (xs.length + e + f)) + 1) :=
      Nat.mul_le_mul (by omega) (Nat.le_succ _)
    unfold initBound loopB
    simp only [preF, update_apply, reduceCtorEq, if_false]
    omega
  case eq =>
    rw [enc_initFam (ic := ic) (ycs := ycs) hk0 xs e f T]
    simp only [emb_b, st_out, preF, PH.cZ, PH.cN, update_apply, reduceCtorEq, if_false,
      List.append_assoc]

end Gen

section Poly

theorem initBound_mono {L L' : Layout} {nY nY' k0 k0' q q' T T' n n' e e' f f' : ℕ}
    (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK) (hg : L.g ≤ L'.g) (hnY : nY ≤ nY') (hk : k0 ≤ k0')
    (hq : q ≤ q') (hT : T ≤ T') (hn : n ≤ n') (he : e ≤ e') (hf : f ≤ f') :
    initBound L nY k0 q T n e f ≤ initBound L' nY' k0' q' T' n' e' f' := by
  unfold initBound preB loopB bodyB clauseB litE Layout.numVars Layout.rowW
  gcongr

theorem initBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    initBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k k k y y y y ≤ 18928 * k ^ 5 * y ^ 5 := by
  have m : ∀ a b, a ≤ 5 → b ≤ 5 → k ^ a * y ^ b ≤ k ^ 5 * y ^ 5 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold initBound preB loopB bodyB clauseB litE Layout.numVars Layout.rowW
    Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  ring_nf
  linarith [m 0 0 (by norm_num) (by norm_num), m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num), m 0 3 (by norm_num) (by norm_num),
    m 0 4 (by norm_num) (by norm_num), m 0 5 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num), m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num), m 1 3 (by norm_num) (by norm_num),
    m 1 4 (by norm_num) (by norm_num), m 1 5 (by norm_num) (by norm_num),
    m 2 0 (by norm_num) (by norm_num), m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num), m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num), m 2 5 (by norm_num) (by norm_num),
    m 3 0 (by norm_num) (by norm_num), m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num), m 3 3 (by norm_num) (by norm_num),
    m 3 4 (by norm_num) (by norm_num), m 3 5 (by norm_num) (by norm_num),
    m 4 0 (by norm_num) (by norm_num), m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num), m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num), m 4 5 (by norm_num) (by norm_num),
    m 5 0 (by norm_num) (by norm_num), m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num), m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num), m 5 5 (by norm_num) (by norm_num)]

example : initBound (Cslib.Complexity.CookLevin.Family.Layout.uni 1) 1 1 1 1 1 1 1 = 18928 := rfl

def initC (L : Layout) (nY k0 : ℕ) : ℕ := 18928 * (L.A + L.KK + L.g + nY + k0 + 1) ^ 5

theorem initBound_le (L : Layout) (nY k0 T n e f : ℕ) :
    initBound L nY k0 (L.KK - k0 - 1) T n e f ≤ initC L nY k0 * (T + (n + e + f) + 1) ^ 5 := by
  have := initBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + nY + k0 + 1))
    (nY := nY) (k0 := k0) (q := L.KK - k0 - 1) (T := T) (n := n) (e := e) (f := f)
    (nY' := L.A + L.KK + L.g + nY + k0 + 1) (k0' := L.A + L.KK + L.g + nY + k0 + 1)
    (q' := L.A + L.KK + L.g + nY + k0 + 1)
    (T' := T + (n + e + f) + 1) (n' := T + (n + e + f) + 1) (e' := T + (n + e + f) + 1)
    (f' := T + (n + e + f) + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have h2 := initBound_uni (L.A + L.KK + L.g + nY + k0 + 1) (T + (n + e + f) + 1) (by omega)
    (by omega)
  unfold initC
  exact this.trans h2

theorem init_time {L : Layout} {ic k0 : ℕ} {ycs : List ℕ} (hk0 : k0 < L.KK) (hic : ic < L.A)
    (hg : 0 < L.g) (hy : (0 :: ycs).Pairwise (· < ·)) (hyg : ∀ c ∈ ycs, c < L.g)
    (xs : List (Fin L.g)) (T e f : ℕ) (hf : 0 < f) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin L.g) k)),
      RunLe (iprog L ic k0 ycs)
        (initC L ycs.length k0 * (T + (xs.length + e + f) + 1) ^ 5)
        ⟨some (.pre1 .eg), false, emb (st (initF T xs.length e f) o) xs.reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (initFam L ic k0 ycs xs (xs.length + e) T (xs.length + e + f)) ++ o :=
  let ⟨v, S, h, h'⟩ := init_run hk0 hic hg hy hyg xs T e f hf o
  ⟨v, S, h.mono (initBound_le L ycs.length k0 T xs.length e f), h'⟩

end Poly

section Link

theorem lookup_pos (v : ℕ) : ∀ ls : List (ℕ × Bool), (∀ p ∈ ls, p.2 = true) →
    ls.lookup v = if v ∈ ls.map Prod.fst then some true else none
  | [], _ => by simp [List.lookup]
  | (p, b) :: r, h => by
    have hb : b = true := h (p, b) (List.mem_cons_self ..)
    subst hb
    have ih := lookup_pos v r (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases hv : v = p
    · subst hv; simp [List.lookup]
    · simp only [List.lookup, List.map_cons, List.mem_cons, hv, false_or]
      rw [show (v == p) = false from by simpa using hv]
      exact ih

theorem denseClause_congr {V : ℕ} {ls ls' : List (ℕ × Bool)} (h : ∀ p ∈ ls, p.2 = true)
    (h' : ∀ p ∈ ls', p.2 = true) (hm : ∀ v, v ∈ ls.map Prod.fst ↔ v ∈ ls'.map Prod.fst) :
    denseClause V ls = denseClause V ls' := by
  unfold denseClause
  congr 1; funext v
  rw [lookup_pos v ls h, lookup_pos v ls' h']
  simp only [hm v]

variable {M : FinTM2} (E : Cslib.Complexity.CookLevin.Situation.Enc M)

noncomputable def ycs (Ys : List (M.Γ M.k₀)) : List ℕ :=
  ((Ys.map (E.enc M.k₀)).toFinset).sort (· ≤ ·)

def encF (z : M.Γ M.k₀) : Fin E.layout.g := ⟨E.enc M.k₀ z, E.enc_lt _ z (E.input_mem z)⟩

theorem mem_ycs (Ys : List (M.Γ M.k₀)) (c : ℕ) : c ∈ ycs E Ys ↔ ∃ z ∈ Ys, E.enc M.k₀ z = c := by
  simp [ycs]

theorem enc_pos (z : M.Γ M.k₀) : 0 < E.enc M.k₀ z := by
  obtain ⟨i, rfl⟩ := E.input_mem z
  rw [E.enc_dec]; omega

theorem ycs_ok (Ys : List (M.Γ M.k₀)) :
    (0 :: ycs E Ys).Pairwise (· < ·) ∧ ∀ c ∈ ycs E Ys, c < E.layout.g := by
  have hs : (ycs E Ys).Pairwise (· < ·) := List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort _)
  refine ⟨List.pairwise_cons.2 ⟨fun c hc => ?_, hs⟩, fun c hc => ?_⟩
  · obtain ⟨z, -, rfl⟩ := (mem_ycs E Ys c).1 hc; exact enc_pos E z
  · obtain ⟨z, -, rfl⟩ := (mem_ycs E Ys c).1 hc; exact E.enc_lt _ z (E.input_mem z)

theorem initFamily_eq (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) :
    E.initFamily x Ys m T H =
      initFam E.layout (E.lc (some M.main, M.initialState)) (E.kc M.k₀) (ycs E Ys)
        (x.map (encF E)) m T H := by
  have hI : E.initIn x T H = iIn E.layout (E.kc M.k₀) (x.map (encF E)) T H := by
    unfold Cslib.Complexity.CookLevin.Situation.Enc.initIn iIn
    rw [List.length_map]
    congr 1; funext j
    rw [List.getElem?_map]
    cases x[j]? <;> rfl
  have hC : E.initCert x Ys m T H = iCert E.layout (E.kc M.k₀) (ycs E Ys) (x.map (encF E)).length m T H := by
    unfold Cslib.Complexity.CookLevin.Situation.Enc.initCert iCert
    rw [List.length_map]
    congr 1; funext i
    refine denseClause_congr ?_ ?_ (fun v => ?_)
    · intro p hp; simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨z, -, rfl⟩ <;> rfl
    · intro p hp; simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨c, -, rfl⟩ <;> rfl
    · simp only [List.map_cons, List.mem_cons, List.map_map, List.mem_map, Function.comp_def,
        mem_ycs]
      constructor
      · rintro (h | ⟨z, hz, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      · rintro (h | ⟨c, ⟨z, hz, rfl⟩, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨z, hz, rfl⟩
  have hP : E.initPre x m T H = iPre E.layout (E.kc M.k₀) (x.map (encF E)).length m T H := by
    rw [List.length_map]; rfl
  unfold Cslib.Complexity.CookLevin.Situation.Enc.initFamily initFam
  rw [hI, hC, hP, List.length_map]
  rfl

theorem init_gen_time (x Ys : List (M.Γ M.k₀)) (m T H : ℕ) (hx : x.length ≤ m) (hmH : m < H)
    (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin E.layout.g) k)),
      RunLe (iprog E.layout (E.lc (some M.main, M.initialState)) (E.kc M.k₀) (ycs E Ys))
        (initC E.layout (ycs E Ys).length (E.kc M.k₀) * (T + H + 1) ^ 5)
        ⟨some (.pre1 .eg), false,
          emb (st (initF T x.length (m - x.length) (H - m)) o) (x.map (encF E)).reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (E.initFamily x Ys m T H) ++ o := by
  obtain ⟨hy, hyg⟩ := ycs_ok E Ys
  have hg : 0 < E.layout.g := by show 0 < E.g; unfold Cslib.Complexity.CookLevin.Situation.Enc.g; omega
  have hic : E.lc (some M.main, M.initialState) < E.layout.A :=
    lt_of_lt_of_le (E.lc_lt _) (Nat.le_add_right _ _)
  obtain ⟨v, S, h, h'⟩ := init_time (ic := E.lc (some M.main, M.initialState)) (E.kc_lt M.k₀) hic hg
    hy hyg (x.map (encF E)) T (m - x.length) (H - m) (by omega) o
  rw [List.length_map] at h h'
  have e1 : x.length + (m - x.length) = m := by omega
  have e2 : x.length + (m - x.length) + (H - m) = H := by omega
  rw [e2] at h
  rw [e1, show m + (H - m) = H by omega, ← initFamily_eq E] at h'
  exact ⟨v, S, h, h'⟩

theorem init_gen_capH (x Ys : List (M.Γ M.k₀)) (m T : ℕ) (hx : x.length ≤ m) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (IΓ CK (Fin E.layout.g) k)),
      RunLe (iprog E.layout (E.lc (some M.main, M.initialState)) (E.kc M.k₀) (ycs E Ys))
        (initC E.layout (ycs E Ys).length (E.kc M.k₀) *
          (T + Cslib.Complexity.CookLevin.Situation.capH m T (Cslib.Complexity.CookLevin.Situation.depth M) + 1) ^ 5)
        ⟨some (.pre1 .eg), false, emb (st (initF T x.length (m - x.length)
          (Cslib.Complexity.CookLevin.Situation.capH m T (Cslib.Complexity.CookLevin.Situation.depth M) - m)) o) (x.map (encF E)).reverse⟩
        ⟨some .done, v, S⟩ ∧
      S (.b .out) = encodeCNF (E.initFamily x Ys m T (Cslib.Complexity.CookLevin.Situation.capH m T (Cslib.Complexity.CookLevin.Situation.depth M))) ++ o :=
  init_gen_time E x Ys m T _ hx (by unfold Cslib.Complexity.CookLevin.Situation.capH; omega) o

end Link

end Cslib.Complexity.CookLevin.InitFamily
end

-- CSLibExt.Computability.Complexity.CookLevin.Assembly
section
namespace Cslib.Complexity.CookLevin.Assembly

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT MetaMathlibExt.TM2Embedding Turing Function
open Cslib.Complexity.CookLevin.CounterView (SK SΓ)
open Cslib.Complexity.CookLevin.InitFamily (IK IΓ emb)

inductive HK
  | out
  | inp
  | up (x : Family.CK)
  | sd (x : Family.CK)
  | sh (x : Shift.CK)
  | ac (x : Accept.CK)
  | ini (x : InitFamily.CK)
  deriving DecidableEq, Fintype

abbrev HΓ (g : ℕ) : HK → Type
  | .out => Bool
  | .inp => Fin g
  | .up _ => Unit
  | .sd _ => Unit
  | .sh _ => Unit
  | .ac _ => Unit
  | .ini _ => Unit

section Embs

variable (g : ℕ)

def eU : Family.GK → HK
  | .out => .out
  | .c x => .up x

def eS : Family.GK → HK
  | .out => .out
  | .c x => .sd x

def eH : SK Shift.CK → HK
  | .out => .out
  | .c x => .sh x

def eA : SK Accept.CK → HK
  | .out => .out
  | .c x => .ac x

def eI : IK InitFamily.CK → HK
  | .b .out => .out
  | .b (.c x) => .ini x
  | .inp => .inp

def embU : SEmb Family.GΓ (HΓ g) where
  e := eU
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eU]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

def embS : SEmb Family.GΓ (HΓ g) where
  e := eS
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eS]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

def embH : SEmb (SΓ Shift.CK) (HΓ g) where
  e := eH
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eH]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

def embA : SEmb (SΓ Accept.CK) (HΓ g) where
  e := eA
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eA]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

def embI : SEmb (IΓ InitFamily.CK (Fin g)) (HΓ g) where
  e := eI
  inj := by
    intro a b h
    rcases a with (_ | a) | _ <;> rcases b with (_ | b) | _ <;> simp_all [eI]
  ι := fun k => match k with
    | .b .out => Equiv.refl _
    | .b (.c _) => Equiv.refl _
    | .inp => Equiv.refl _

end Embs

section AgreeLemmas

variable {g : ℕ} (S : ∀ k, List (HΓ g k))

theorem agree_U {F : Family.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.up x) = cnt () (F x)) : Agree (embU g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embU, eU, ho, hc]
  exact (List.map_id _).symm

theorem agree_S {F : Family.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.sd x) = cnt () (F x)) : Agree (embS g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embS, eS, ho, hc]
  exact (List.map_id _).symm

theorem agree_H {F : Shift.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.sh x) = cnt () (F x)) : Agree (embH g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embH, eH, ho, hc]
  exact (List.map_id _).symm

theorem agree_A {F : Accept.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.ac x) = cnt () (F x)) : Agree (embA g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embA, eA, ho, hc]
  exact (List.map_id _).symm

theorem agree_I {F : InitFamily.CK → ℕ} {o : List Bool} {xs : List (Fin g)} (ho : S .out = o)
    (hi : S .inp = xs) (hc : ∀ x, S (.ini x) = cnt () (F x)) :
    Agree (embI g) (emb (CounterView.st F o) xs) S := by
  intro k; rcases k with (_ | x) | _ <;> simp [embI, eI, ho, hi, hc] <;> exact (List.map_id _).symm

end AgreeLemmas

inductive HL (N nL KK g d n1 ny : ℕ)
  | up (l : Family.GeneratorLabel N nL)
  | sd (l : Family.GeneratorLabel N nL)
  | sh (l : Shift.GeneratorLabel N KK g d)
  | ac (l : Accept.GeneratorLabel n1 g)
  | ini (l : InitFamily.GeneratorLabel g ny)
  | fin
  deriving DecidableEq, Fintype

section Seq

variable {g N nL KK d n1 ny : ℕ}
  (Pu Ps : Family.GeneratorLabel N nL → TM2.Stmt Family.GΓ (Family.GeneratorLabel N nL) Bool)
  (Ph : Shift.GeneratorLabel N KK g d → TM2.Stmt (SΓ Shift.CK) (Shift.GeneratorLabel N KK g d) Bool)
  (Pa : Accept.GeneratorLabel n1 g → TM2.Stmt (SΓ Accept.CK) (Accept.GeneratorLabel n1 g) Bool)
  (Pi : InitFamily.GeneratorLabel g ny → TM2.Stmt (IΓ InitFamily.CK (Fin g)) (InitFamily.GeneratorLabel g ny) Bool)

def chain (l : HL N nL KK g d n1 ny) : TM2.Stmt (HΓ g) (HL N nL KK g d n1 ny) Bool :=
  .load (fun _ => false) (.goto fun _ => l)

def hprog : HL N nL KK g d n1 ny → TM2.Stmt (HΓ g) (HL N nL KK g d n1 ny) Bool
  | .ini l => if l = .done then chain (.up (.pre .eg)) else mapS (embI g) HL.ini (Pi l)
  | .up l => if l = .done then chain (.sd (.pre .eg)) else mapS (embU g) HL.up (Pu l)
  | .sd l => if l = .done then chain (.sh (.pre .eg)) else mapS (embS g) HL.sd (Ps l)
  | .sh l => if l = .done then chain (.ac (.pre .eg)) else mapS (embH g) HL.sh (Ph l)
  | .ac l => if l = .done then chain .fin else mapS (embA g) HL.ac (Pa l)
  | .fin => .halt

def hostTM : FinTM2 where
  K := HK
  k₀ := .inp
  k₁ := .out
  Γ := HΓ g
  Λ := HL N nL KK g d n1 ny
  main := .ini (.pre1 .eg)
  σ := Bool
  initialState := false
  m := hprog Pu Ps Ph Pa Pi

variable {Pu Ps Ph Pa Pi}

theorem embeds_I (h : Pi .done = .halt) : Embeds (embI g) HL.ini Pi (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, if_neg hl])

theorem embeds_U (h : Pu .done = .halt) : Embeds (embU g) HL.up Pu (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, if_neg hl])

theorem embeds_S (h : Ps .done = .halt) : Embeds (embS g) HL.sd Ps (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, if_neg hl])

theorem embeds_H (h : Ph .done = .halt) : Embeds (embH g) HL.sh Ph (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, if_neg hl])

theorem embeds_A (h : Pa .done = .halt) : Embeds (embA g) HL.ac Pa (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, if_neg hl])

theorem chain_run {l l' : HL N nL KK g d n1 ny} (h : hprog Pu Ps Ph Pa Pi l = chain l') (v : Bool)
    (S : ∀ k, List (HΓ g k)) :
    RunLe (hprog Pu Ps Ph Pa Pi) 1 ⟨some l, v, S⟩ ⟨some l', false, S⟩ :=
  (Run.single (by rw [h]; rfl)).le le_rfl

theorem seq_run (hu0 : Pu .done = .halt) (hs0 : Ps .done = .halt) (hh0 : Ph .done = .halt)
    (ha0 : Pa .done = .halt) (hi0 : Pi .done = .halt)
    {Fu Fs : Family.CK → ℕ} {Fh : Shift.CK → ℕ} {Fa : Accept.CK → ℕ} {Fi : InitFamily.CK → ℕ}
    {xs : List (Fin g)} {wu ws wh wa wi : List Bool} {Bu Bs Bh Ba Bi : ℕ}
    (hu : ∀ o, ∃ (v : Bool) (S : ∀ k, List (Family.GΓ k)),
      RunLe Pu Bu ⟨some (.pre .eg), false, CounterView.st Fu o⟩ ⟨some .done, v, S⟩ ∧ S .out = wu ++ o)
    (hs : ∀ o, ∃ (v : Bool) (S : ∀ k, List (Family.GΓ k)),
      RunLe Ps Bs ⟨some (.pre .eg), false, CounterView.st Fs o⟩ ⟨some .done, v, S⟩ ∧ S .out = ws ++ o)
    (hh : ∀ o, ∃ (v : Bool) (S : ∀ k, List (SΓ Shift.CK k)),
      RunLe Ph Bh ⟨some (.pre .eg), false, CounterView.st Fh o⟩ ⟨some .done, v, S⟩ ∧ S .out = wh ++ o)
    (ha : ∀ o, ∃ (v : Bool) (S : ∀ k, List (SΓ Accept.CK k)),
      RunLe Pa Ba ⟨some (.pre .eg), false, CounterView.st Fa o⟩ ⟨some .done, v, S⟩ ∧ S .out = wa ++ o)
    (hi : ∀ o, ∃ (v : Bool) (S : ∀ k, List (IΓ InitFamily.CK (Fin g) k)),
      RunLe Pi Bi ⟨some (.pre1 .eg), false, emb (CounterView.st Fi o) xs⟩ ⟨some .done, v, S⟩ ∧
        S (.b .out) = wi ++ o)
    (S₀ : ∀ k, List (HΓ g k)) (o : List Bool) (ho : S₀ .out = o) (hin : S₀ .inp = xs)
    (cu : ∀ x, S₀ (.up x) = cnt () (Fu x)) (cs : ∀ x, S₀ (.sd x) = cnt () (Fs x))
    (ch : ∀ x, S₀ (.sh x) = cnt () (Fh x)) (ca : ∀ x, S₀ (.ac x) = cnt () (Fa x))
    (ci : ∀ x, S₀ (.ini x) = cnt () (Fi x)) :
    ∃ (v : Bool) (S : ∀ k, List (HΓ g k)),
      RunLe (hprog Pu Ps Ph Pa Pi) (Bi + Bu + Bs + Bh + Ba + 5)
        ⟨some (.ini (.pre1 .eg)), false, S₀⟩ ⟨some .fin, v, S⟩ ∧
      S .out = wa ++ (wh ++ (ws ++ (wu ++ (wi ++ o)))) := by

  obtain ⟨v1, S1, r1, o1⟩ := hi o
  obtain ⟨T1, q1, a1, f1⟩ := runLe_embed HL.ini (embeds_I hi0) r1 (agree_I S₀ ho hin ci)
  have t1o : T1 .out = wi ++ o := ((a1 (.b .out)).trans (List.map_id _)).trans o1
  have t1u : ∀ x, T1 (.up x) = S₀ (.up x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1s : ∀ x, T1 (.sd x) = S₀ (.sd x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1h : ∀ x, T1 (.sh x) = S₀ (.sh x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1a : ∀ x, T1 (.ac x) = S₀ (.ac x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])

  obtain ⟨v2, S2, r2, o2⟩ := hu (wi ++ o)
  obtain ⟨T2, q2, a2, f2⟩ := runLe_embed HL.up (embeds_U hu0) r2
    (agree_U T1 t1o (fun x => (t1u x).trans (cu x)))
  have t2o : T2 .out = wu ++ (wi ++ o) := ((a2 .out).trans (List.map_id _)).trans o2
  have t2s : ∀ x, T2 (.sd x) = S₀ (.sd x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1s x)
  have t2h : ∀ x, T2 (.sh x) = S₀ (.sh x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1h x)
  have t2a : ∀ x, T2 (.ac x) = S₀ (.ac x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1a x)

  obtain ⟨v3, S3, r3, o3⟩ := hs (wu ++ (wi ++ o))
  obtain ⟨T3, q3, a3, f3⟩ := runLe_embed HL.sd (embeds_S hs0) r3
    (agree_S T2 t2o (fun x => (t2s x).trans (cs x)))
  have t3o : T3 .out = ws ++ (wu ++ (wi ++ o)) := ((a3 .out).trans (List.map_id _)).trans o3
  have t3h : ∀ x, T3 (.sh x) = S₀ (.sh x) := fun x =>
    (f3 _ (fun k => by cases k <;> simp [embS, eS])).trans (t2h x)
  have t3a : ∀ x, T3 (.ac x) = S₀ (.ac x) := fun x =>
    (f3 _ (fun k => by cases k <;> simp [embS, eS])).trans (t2a x)

  obtain ⟨v4, S4, r4, o4⟩ := hh (ws ++ (wu ++ (wi ++ o)))
  obtain ⟨T4, q4, a4, f4⟩ := runLe_embed HL.sh (embeds_H hh0) r4
    (agree_H T3 t3o (fun x => (t3h x).trans (ch x)))
  have t4o : T4 .out = wh ++ (ws ++ (wu ++ (wi ++ o))) :=
    ((a4 .out).trans (List.map_id _)).trans o4
  have t4a : ∀ x, T4 (.ac x) = S₀ (.ac x) := fun x =>
    (f4 _ (fun k => by cases k <;> simp [embH, eH])).trans (t3a x)

  obtain ⟨v5, S5, r5, o5⟩ := ha (wh ++ (ws ++ (wu ++ (wi ++ o))))
  obtain ⟨T5, q5, a5, _⟩ := runLe_embed HL.ac (embeds_A ha0) r5
    (agree_A T4 t4o (fun x => (t4a x).trans (ca x)))
  have t5o : T5 .out = wa ++ (wh ++ (ws ++ (wu ++ (wi ++ o)))) :=
    ((a5 .out).trans (List.map_id _)).trans o5
  refine ⟨false, T5, ?_, t5o⟩
  have c1 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .ini .done) (l' := .up (.pre .eg)) (by simp [hprog]) v1 T1
  have c2 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .up .done) (l' := .sd (.pre .eg)) (by simp [hprog]) v2 T2
  have c3 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .sd .done) (l' := .sh (.pre .eg)) (by simp [hprog]) v3 T3
  have c4 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .sh .done) (l' := .ac (.pre .eg)) (by simp [hprog]) v4 T4
  have c5 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .ac .done) (l' := .fin) (by simp [hprog]) v5 T5
  exact ((((((((((q1.trans c1).trans q2).trans c2).trans q3).trans c3).trans q4).trans c4).trans
    q5).trans c5).mono (by omega))

end Seq

section Real

open Cslib.Complexity.CookLevin.Situation

variable {M : FinTM2} (E : Enc M)

noncomputable abbrev realProg (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) :=
  hprog (Family.prog E.layout E.la E.na E.wa E.N) (Family.prog E.layout E.la E.sa E.wa E.N)
    (Shift.prog E.layout E.sa E.pl E.cn E.pu E.N)
    (Accept.prog E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc))
    (InitFamily.iprog E.layout (E.lc (some M.main,
        M.initialState)) (E.kc M.k₀) (InitFamily.ycs E Ys))

noncomputable def Phi (x Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (m T : ℕ) : CNF :=
  E.accFamily acc T (capH m T (depth M)) ++
    (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M)) ++
      (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N ++
        (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N ++
          E.initFamily x Ys m T (capH m T (depth M)))))

noncomputable def realB (Ys : List (M.Γ M.k₀)) (m T : ℕ) : ℕ :=
  InitFamily.initC E.layout (InitFamily.ycs E Ys).length (E.kc M.k₀) * (T + capH m T (depth M) + 1) ^ 5 +
    Family.genC E.layout E.N * (T + capH m T (depth M) + 1) ^ 5 +
    Family.genC E.layout E.N * (T + capH m T (depth M) + 1) ^ 5 +
    Shift.shC E.layout E.N * (T + capH m T (depth M) + 1) ^ 6 +
    Accept.accC E.layout E.A0 (E.kc M.k₁) * (T + capH m T (depth M) + 1) ^ 4 + 5

theorem real_run (x Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (m T : ℕ) (hx : x.length ≤ m)
    (S₀ : ∀ k, List (HΓ E.layout.g k)) (o : List Bool) (ho : S₀ .out = o)
    (hin : S₀ .inp = (x.map (InitFamily.encF E)).reverse)
    (cu : ∀ z, S₀ (.up z) = cnt () (Family.initF T (capH m T (depth M)) z))
    (cs : ∀ z, S₀ (.sd z) = cnt () (Family.initF T (capH m T (depth M)) z))
    (ch : ∀ z, S₀ (.sh z) = cnt () (Shift.initF T (capH m T (depth M)) z))
    (ca : ∀ z, S₀ (.ac z) = cnt () (Accept.initF T (capH m T (depth M)) z))
    (ci : ∀ z, S₀ (.ini z) = cnt () (InitFamily.initF T x.length (m - x.length)
      (capH m T (depth M) - m) z)) :
    ∃ (v : Bool) (S : ∀ k, List (HΓ E.layout.g k)),
      RunLe (realProg E Ys acc) (realB E Ys m T)
        ⟨some (.ini (.pre1 .eg)), false, S₀⟩ ⟨some .fin, v, S⟩ ∧
      S .out = encodeCNF (Phi E x Ys acc m T) ++ o := by
  have hH := depth_le_capH M m T
  have hpos : 0 < capH m T (depth M) := by unfold capH; omega
  obtain ⟨v, S, h, h'⟩ := seq_run rfl rfl rfl rfl rfl
    (fun o => upd_time E hH T o) (fun o => sdef_time E hH T o) (fun o => shift_time E hH T o)
    (fun o => Accept.acc_gen_time E acc T _ hpos o)
    (fun o => InitFamily.init_gen_capH E x Ys m T hx o) S₀ o ho hin cu cs ch ca ci
  refine ⟨v, S, h, ?_⟩
  rw [h']
  simp only [Phi, encodeCNF, List.flatMap_append, List.append_assoc]

theorem phi_iff {x Ys : List (M.Γ M.k₀)} {acc : M.Γ M.k₁} {m T : ℕ} (hx : x.length ≤ m)
    (hacc : ∃ i, E.dec M.k₁ i = acc) :
    (∃ a, cnfSat (Phi E x Ys acc m T) a) ↔
      ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
        Accepts M (runI M (initList M (x ++ y)) T) acc := by
  rw [← E.five_iff hx hacc]
  simp only [Phi, cnfSat_append]
  constructor
  · rintro ⟨a, ha, hh, hs, hu, hi⟩; exact ⟨a, hu, hs, hh, hi, ha⟩
  · rintro ⟨a, hu, hs, hh, hi, ha⟩; exact ⟨a, ha, hh, hs, hu, hi⟩

end Real

end Cslib.Complexity.CookLevin.Assembly
end

-- CSLibExt.Computability.Complexity.CookLevin.Precompute
section
namespace Cslib.Complexity.CookLevin.Precompute

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT MetaMathlibExt.TM2Embedding Turing Function
open Cslib.Complexity.CookLevin.CounterView (SK SΓ st st_c st_out update_st_c update_st_nil emitS
  incS drainS copyS mulS mulS_run bud_st MS)

section CLib

variable {C : Type} [DecidableEq C] {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem decS_pos {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) {j : ℕ} (hx : F x = j + 1) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifPos, true, st (update F x j) o⟩ := by
  have := decr_run_cnt hp v (S := st F o) (u := ()) (n := j) (by simp [hx])
  rw [update_st_c] at this
  exact this

theorem decS_zero {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) (hx : F x = 0) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifZero, false, st F o⟩ :=
  decr_run_zero hp v (by simp [hx])

def tg (ys : List C) : List (Σ k, SΓ C k) := ys.map fun y => ⟨.c y, ()⟩

omit [DecidableEq C] in
theorem tg_keys (ys : List C) : (tg ys).keys = ys.map SK.c := by
  simp [tg, List.keys]

omit [DecidableEq C] in
theorem tg_nodupKeys {ys : List C} (h : ys.Nodup) : (tg ys).NodupKeys := by
  unfold List.NodupKeys
  rw [tg_keys]
  exact h.map (fun _ _ h => by cases h; rfl)

theorem dlookup_tg (ys : List C) (z : C) :
    List.dlookup (SK.c z) (tg ys) = if z ∈ ys then some () else none := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : z = y
      · subst h; simp [tg, List.dlookup_cons_eq]
      · rw [tg, List.map_cons, List.dlookup_cons_ne _ _ (by simpa using h)]
        rw [← tg, ih]; simp [h]

theorem dlookup_tg_out (ys : List C) : List.dlookup (SK.out) (tg ys) = none := by
  rw [List.dlookup_eq_none, tg_keys]; simp

def xf (F : C → ℕ) (x : C) (ys : List C) : C → ℕ :=
  fun z => if z = x then 0 else if z ∈ ys then F z + F x else F z

theorem xferS {self next : Λ} {x : C} {ys : List C} (hp : M self = xfer (.c x) (tg ys) self next)
    (hnd : ys.Nodup) (hx : x ∉ ys) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (xf F x ys) o⟩ := by
  have := xfer_run hp (tg_nodupKeys hnd) (by rw [tg_keys]; simpa using hx) () (F x) v (st F o) rfl
  have e : addU (tg ys) (F x) (update (st F o) (SK.c x) []) = st (xf F x ys) o := by
    funext k
    rcases k with _ | z
    · simp [addU, dlookup_tg_out]
    · simp only [addU, dlookup_tg]
      by_cases hz : z = x
      · subst hz; simp [xf, hx]
      · rw [update_of_ne (by simpa using hz)]
        by_cases hy : z ∈ ys
        · simp [xf, hz, hy, add_comm]
        · simp [xf, hz, hy]
  rw [e] at this
  exact this

inductive PW
  | hd
  | mul (s : MS)
  | drn
  | mv
  deriving DecidableEq, Fintype

def powS (b kc p q ad t : C) (mk : PW → Λ) (exit : Λ) : PW → TM2.Stmt (SΓ C) Λ Bool
  | .hd => decr (.c kc) exit (mk (.mul .head))
  | .mul s => mulS p ad b q t (fun s => mk (.mul s)) (mk .drn) s
  | .drn => xfer (.c p) [] (mk .drn) (mk .mv)
  | .mv => xfer (.c q) (tg [p]) (mk .mv) (mk .hd)

def powB (j p b : ℕ) : ℕ := j * (p * (b + 1) ^ j * (3 * b + 5) + 5) + 1

theorem pow_run {b kc p q ad t : C} {mk : PW → Λ} {exit : Λ}
    (hp : ∀ s, M (mk s) = powS b kc p q ad t mk exit s)
    (hnd : [b, kc, p, q, ad, t].Nodup) :
    ∀ (j : ℕ) (F : C → ℕ), F kc = j → F q = 0 → F ad = 0 → F t = 0 → ∀ (v : Bool) (o : List Bool),
      RunLe M (powB j (F p) (F b)) ⟨some (mk .hd), v, st F o⟩
        ⟨some exit, false, st (update (update F p (F p * F b ^ j)) kc 0) o⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hbk, hbp, hbq, hbad, hbt⟩, ⟨hkp, hkq, hkad, hkt⟩, ⟨hpq, hpad, hpt⟩, ⟨hqad, hqt⟩,
    hadt, -⟩ := hnd
  intro j
  induction j with
  | zero =>
      intro F hk hq had ht v o
      have r := decS_zero (hp .hd) F hk v o
      have hF : update (update F p (F p * F b ^ 0)) kc 0 = F := by
        funext z; by_cases h1 : z = kc
        · subst h1; simp [hk]
        · by_cases h2 : z = p
          · subst h2; simp [h1]
          · simp [h1]
      rw [hF]; exact r.le (by simp [powB])
  | succ j ih =>
      intro F hk hq had ht v o

      have r1 := decS_pos (hp .hd) F hk v o
      set F1 := update F kc j with hF1

      have r2 := mulS_run (a := p) (ad := ad) (b := b) (c := q) (t := t)
        (mk := fun s => mk (.mul s)) (next := mk .drn) (M := M) (fun s => hp (.mul s))
        (by simp [hpad, (Ne.symm hbp), hpq, hpt, (Ne.symm hbad), (Ne.symm hqad), hadt, hbq, hbt,
            hqt])
        F1 (by simp [hF1, (Ne.symm hkad), had]) (by simp [hF1, (Ne.symm hkt), ht]) true o
      set F2 := update F1 q (F1 p * F1 b + F1 q) with hF2

      have r3 := drainS (hp .drn) F2 false o
      set F3 := update F2 p 0 with hF3

      have r4 := xferS (hp .mv) (by simp) (by simpa using (Ne.symm hpq)) F3 false o
      set F4 := xf F3 q [p] with hF4
      have hF1p : F1 p = F p := by rw [hF1, update_of_ne (Ne.symm hkp)]
      have hF1b : F1 b = F b := by rw [hF1, update_of_ne hbk]
      have hF1q : F1 q = 0 := by rw [hF1, update_of_ne (Ne.symm hkq), hq]
      have hF2p : F2 p = F p := by rw [hF2, update_of_ne hpq, hF1p]
      have hF3q : F3 q = F p * F b := by
        rw [hF3, update_of_ne (Ne.symm hpq), hF2, update_self, hF1p, hF1b, hF1q, add_zero]
      have hrest : ∀ z, z ≠ q → z ≠ p → z ≠ kc → F4 z = F z := by
        intro z h1 h2 h3
        simp only [hF4, xf, if_neg h1, List.mem_singleton, if_neg h2, hF3, hF2, hF1,
          update_of_ne h1, update_of_ne h2, update_of_ne h3]
      have h4p : F4 p = F p * F b := by
        simp only [hF4, xf, if_neg hpq, List.mem_singleton, if_true, hF3, update_self,
            zero_add]
        exact hF3q
      have h4k : F4 kc = j := by
        simp only [hF4, xf, if_neg hkq, List.mem_singleton, if_neg hkp, hF3, hF2, hF1,
          update_of_ne hkp, update_of_ne hkq, update_self]
      have h4b : F4 b = F b := hrest b hbq hbp hbk
      have r5 := ih F4 h4k (by simp [hF4, xf])
        (by rw [hrest ad (Ne.symm hqad) (Ne.symm hpad) (Ne.symm hkad), had])
        (by rw [hrest t (Ne.symm hqt) (Ne.symm hpt) (Ne.symm hkt), ht]) false o
      have hend : update (update F4 p (F4 p * F4 b ^ j)) kc 0 =
          update (update F p (F p * F b ^ (j + 1))) kc 0 := by
        funext z
        by_cases h1 : z = kc
        · subst h1; simp
        rw [update_of_ne h1, update_of_ne h1]
        by_cases h2 : z = p
        · subst h2; rw [update_self, update_self, h4p, h4b, pow_succ]; ring
        rw [update_of_ne h2, update_of_ne h2]
        by_cases h3 : z = q
        · subst h3; simp [hF4, xf, hq]
        exact hrest z h3 h2 h1
      rw [hend, h4p, h4b] at r5
      rw [hF2p] at r3
      rw [hF3q] at r4
      rw [hF1p, hF1b] at r2
      have := ((((r1.le le_rfl).trans (r2.le le_rfl)).trans (r3.le le_rfl)).trans
        (r4.le le_rfl)).trans r5
      refine this.mono ?_
      unfold powB
      have hpw : F p * F b * (F b + 1) ^ j ≤ F p * (F b + 1) ^ (j + 1) := by
        rw [pow_succ, mul_assoc, mul_comm (F b)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
      have hp1 : F p ≤ F p * (F b + 1) ^ (j + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))
      have h1 := Nat.mul_le_mul_right (3 * F b + 5) hp1
      have h2 := Nat.mul_le_mul_left j (Nat.add_le_add_right
        (Nat.mul_le_mul_right (3 * F b + 5) hpw) 5)
      nlinarith [h1, h2]

inductive HW
  | mul (s : MS)
  | drn
  | mv
  | add
  deriving DecidableEq, Fintype

def hornS (b acc q ad t : C) (a : ℕ) (mk : HW → Λ) (next : Λ) : HW → TM2.Stmt (SΓ C) Λ Bool
  | .mul s => mulS acc ad b q t (fun s => mk (.mul s)) (mk .drn) s
  | .drn => xfer (.c acc) [] (mk .drn) (mk .mv)
  | .mv => xfer (.c q) (tg [acc]) (mk .mv) (mk .add)
  | .add => emitR (.c acc) (List.replicate a ()) next

def hornStep (A b : ℕ) : ℕ := A * (2 * b + 3) + A + 2 + (A + 1) + (A * b + 1) + 1

theorem horn_round {b acc q ad t : C} {a : ℕ} {mk : HW → Λ} {next : Λ}
    (hp : ∀ s, M (mk s) = hornS b acc q ad t a mk next s)
    (hnd : [b, acc, q, ad, t].Nodup) (F : C → ℕ) (hq : F q = 0) (had : F ad = 0)
    (ht : F t = 0) (v : Bool) (o : List Bool) :
    Run M (hornStep (F acc) (F b)) ⟨some (mk (.mul .head)), v, st F o⟩
      ⟨some next, false, st (update F acc (F acc * F b + a)) o⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hba, hbq, hbad, hbt⟩, ⟨haq, haad, hat⟩, ⟨hqad, hqt⟩, hadt, -⟩ := hnd
  have r1 := mulS_run (a := acc) (ad := ad) (b := b) (c := q) (t := t)
    (mk := fun s => mk (.mul s)) (next := mk .drn) (M := M) (fun s => hp (.mul s))
    (by simp [haad, Ne.symm hba, haq, hat, Ne.symm hbad, Ne.symm hqad, hadt, hbq, hbt, hqt])
    F had ht v o
  set F1 := update F q (F acc * F b + F q) with hF1
  have r2 := drainS (hp .drn) F1 false o
  set F2 := update F1 acc 0 with hF2
  have r3 := xferS (hp .mv) (by simp) (by simpa using Ne.symm haq) F2 false o
  set F3 := xf F2 q [acc] with hF3
  have r4 := emitS (n := a) (hp .add) F3 false o
  have hF1a : F1 acc = F acc := by rw [hF1, update_of_ne haq]
  have hF2q : F2 q = F acc * F b := by
    rw [hF2, update_of_ne (Ne.symm haq), hF1, update_self, hq, add_zero]
  have hF3a : F3 acc = F acc * F b := by
    simp only [hF3, xf, if_neg haq, List.mem_singleton, if_true, hF2, update_self,
      zero_add]
    exact hF2q
  have hend : update F3 acc (a + F3 acc) = update F acc (F acc * F b + a) := by
    funext z
    by_cases h1 : z = acc
    · subst h1; rw [update_self, update_self, hF3a, add_comm]
    rw [update_of_ne h1, update_of_ne h1]
    by_cases h2 : z = q
    · subst h2; simp [hF3, xf, hq]
    simp only [hF3, xf, if_neg h2, List.mem_singleton, if_neg h1, hF2, hF1,
      update_of_ne h1, update_of_ne h2]
  rw [hend] at r4
  rw [hF1a] at r2
  rw [hF2q] at r3
  exact (r1.trans (r2.trans (r3.trans r4))).of_eq (by unfold hornStep; ring)

def hornVal (cs : List ℕ) (b A : ℕ) : ℕ := cs.foldl (fun A a => A * b + a) A

def hornT : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | a :: cs, b, A => hornStep A b + hornT cs b (A * b + a)

theorem horner_run {b acc q ad t : C} (cs : List ℕ) {mk : ℕ → HW → Λ} {exit : Λ}
    (hp : ∀ i (hi : i < cs.length) s, M (mk i s) = hornS b acc q ad t cs[i] (mk i)
      (if i + 1 < cs.length then mk (i + 1) (.mul .head) else exit) s)
    (hnd : [b, acc, q, ad, t].Nodup) :
    ∀ (j i : ℕ), i + j = cs.length → ∀ (F : C → ℕ), F q = 0 → F ad = 0 → F t = 0 →
      ∀ (v : Bool) (o : List Bool),
      ∃ v' : Bool, Run M (hornT (cs.drop i) (F b) (F acc))
        ⟨some (if i < cs.length then mk i (.mul .head) else exit), v, st F o⟩
        ⟨some exit, v', st (update F acc (hornVal (cs.drop i) (F b) (F acc))) o⟩ := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hba, hbq, hbad, hbt⟩, ⟨haq, haad, hat⟩, ⟨hqad, hqt⟩, hadt, -⟩ := hnd'
  intro j
  induction j with
  | zero =>
      intro i hi F _ _ _ v o
      have hd : cs.drop i = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨v, ?_⟩
      rw [hd, if_neg (by omega)]
      simp only [hornT, hornVal, List.foldl_nil, update_eq_self]
      exact TM2Program.Run.zero _
  | succ j ih =>
      intro i hi F hq had ht v o
      have hlt : i < cs.length := by omega
      have hd : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hlt
      have r1 := horn_round (a := cs[i]) (mk := mk i) (hp i hlt) hnd F hq had ht v o
      set F1 := update F acc (F acc * F b + cs[i]) with hF1
      obtain ⟨v', r2⟩ := ih (i + 1) (by omega) F1 (by rw [hF1, update_of_ne (Ne.symm haq), hq])
        (by rw [hF1, update_of_ne (Ne.symm haad), had])
        (by rw [hF1, update_of_ne (Ne.symm hat), ht]) false o
      have hF1b : F1 b = F b := by rw [hF1, update_of_ne hba]
      have hF1a : F1 acc = F acc * F b + cs[i] := by rw [hF1, update_self]
      rw [hF1b, hF1a] at r2
      have hupd : update F1 acc (hornVal (cs.drop (i + 1)) (F b) (F acc * F b + cs[i])) =
          update F acc (hornVal (cs.drop (i + 1)) (F b) (F acc * F b + cs[i])) := by
        rw [hF1, update_idem]
      rw [hupd] at r2
      refine ⟨v', ?_⟩
      rw [if_pos hlt, hd]
      exact r1.trans r2

theorem hornVal_eq (cs : List ℕ) (b A : ℕ) :
    hornVal cs b A = A * b ^ cs.length + hornVal cs b 0 := by
  induction cs generalizing A with
  | nil => simp [hornVal]
  | cons a cs ih =>
      simp only [hornVal, List.foldl_cons, List.length_cons] at ih ⊢
      rw [ih (A * b + a), ih (0 * b + a)]
      ring

noncomputable def coeffs (p : Polynomial ℕ) : List ℕ :=
  (List.range (p.natDegree + 1)).reverse.map p.coeff

theorem hornVal_range (f : ℕ → ℕ) (b D : ℕ) :
    hornVal ((List.range D).reverse.map f) b 0 = ∑ i ∈ Finset.range D, f i * b ^ i := by
  induction D with
  | zero => simp [hornVal]
  | succ D ih =>
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, Finset.sum_range_succ]
      have := hornVal_eq ((List.range D).reverse.map f) b (0 * b + f D)
      simp only [hornVal, List.foldl_cons, List.length_map, List.length_reverse,
        List.length_range] at this ih ⊢
      rw [this, ih]
      ring

theorem hornVal_coeffs (p : Polynomial ℕ) (b : ℕ) : hornVal (coeffs p) b 0 = p.eval b := by
  rw [coeffs, hornVal_range, Polynomial.eval_eq_sum_range]

end CLib

inductive PS
  | N | P | Q | AD | TMP | KC | Mc | B | Tc | Fx | Dd | Hc
  deriving DecidableEq
instance PS.instFintypeEnumFix : Fintype PS where
  elems := ⟨↑[PS.N, PS.P, PS.Q, PS.AD, PS.TMP, PS.KC, PS.Mc, PS.B, PS.Tc, PS.Fx, PS.Dd, PS.Hc],
      by decide⟩
  complete := fun x => by cases x <;> decide

inductive PT
  | uT | uH | sT | sH | hT | hH | aT | aH | iT | iX | iE | iF
  deriving DecidableEq
instance PT.instFintypeEnumFix : Fintype PT where
  elems := ⟨↑[PT.uT, PT.uH, PT.sT, PT.sH, PT.hT, PT.hH, PT.aT, PT.aH, PT.iT, PT.iX, PT.iE, PT.iF],
      by decide⟩
  complete := fun x => by cases x <;> decide

inductive CC
  | s (x : PS)
  | t (y : PT)
  deriving DecidableEq, Fintype

inductive PL (D : ℕ)
  | p1 | hr (i : Fin D) (s : HW) | x1 | x2 | x3 | x4 | c1 | c2 | x6 | x7 | x8 | w2 (s : PW) | x9
  | ml (s : MS) | x10 | x11 | x12 | x13 | x14 | done
  deriving DecidableEq, Fintype

def hlab {D : ℕ} (i : ℕ) (s : HW) : PL D := if h : i < D then .hr ⟨i, h⟩ s else .x1

open CC PS PT in

noncomputable def cprog (k : Polynomial ℕ) (c e d : ℕ) :
    PL (coeffs k).length → TM2.Stmt (SΓ CC) (PL (coeffs k).length) Bool
  | .p1 => emitR (.c (s P)) (List.replicate 0 ()) (if 0 < (coeffs k).length then hlab 0 (.mul .head) else .x1)
  | .hr i q => hornS (s N) (s P) (s Q) (s AD) (s TMP) (coeffs k)[i] (hlab i.1)
      (if i.1 + 1 < (coeffs k).length then hlab (i.1 + 1) (.mul .head) else .x1) q
  | .x1 => xfer (.c (s P)) (tg [s Mc, t iE]) .x1 .x2
  | .x2 => xfer (.c (s N)) (tg [s Mc, t iX]) .x2 .x3
  | .x3 => emitR (.c (s Mc)) (List.replicate 1 ()) .x4
  | .x4 => emitR (.c (t iX)) (List.replicate 1 ()) .c1
  | .c1 => xfer (.c (s Mc)) [⟨.c (s B), ()⟩, ⟨.c (s TMP), ()⟩] .c1 .c2
  | .c2 => xfer (.c (s TMP)) [⟨.c (s Mc), ()⟩] .c2 .x6
  | .x6 => emitR (.c (s B)) (List.replicate c ()) .x7
  | .x7 => emitR (.c (s KC)) (List.replicate e ()) .x8
  | .x8 => emitR (.c (s Tc)) (List.replicate 1 ()) (.w2 .hd)
  | .w2 q => powS (s B) (s KC) (s Tc) (s Q) (s AD) (s TMP) PL.w2 .x9 q
  | .x9 => emitR (.c (s Dd)) (List.replicate d ()) (.ml .head)
  | .ml q => mulS (s Dd) (s AD) (s Tc) (s Fx) (s TMP) PL.ml .x10 q
  | .x10 => emitR (.c (s Fx)) (List.replicate (d + 1) ()) .x11
  | .x11 => xfer (.c (s Fx)) (tg [s Hc, t iF]) .x11 .x12
  | .x12 => xfer (.c (s Mc)) (tg [s Hc]) .x12 .x13
  | .x13 => xfer (.c (s Tc)) (tg [t uT, t sT, t hT, t aT, t iT]) .x13 .x14
  | .x14 => xfer (.c (s Hc)) (tg [t uH, t sH, t hH, t aH]) .x14 .done
  | .done => .halt

def mOf (k : Polynomial ℕ) (n : ℕ) : ℕ := n + 1 + k.eval n

def TOf (k : Polynomial ℕ) (c e n : ℕ) : ℕ := (mOf k n + c) ^ e

def F0 (n : ℕ) : CC → ℕ
  | .s .N => n
  | _ => 0

def F1 (k : Polynomial ℕ) (n : ℕ) : CC → ℕ
  | .s .N => n
  | .s .P => k.eval n
  | _ => 0

def F2 (k : Polynomial ℕ) (c e n : ℕ) : CC → ℕ
  | .s .Mc => mOf k n
  | .s .B => mOf k n + c
  | .s .KC => e
  | .s .Tc => 1
  | .t .iX => n + 1
  | .t .iE => k.eval n
  | _ => 0

def F3 (k : Polynomial ℕ) (c e n : ℕ) : CC → ℕ
  | .s .Mc => mOf k n
  | .s .B => mOf k n + c
  | .s .Tc => TOf k c e n
  | .t .iX => n + 1
  | .t .iE => k.eval n
  | _ => 0

def tv (k : Polynomial ℕ) (c e d n : ℕ) : PT → ℕ
  | .uT | .sT | .hT | .aT | .iT => TOf k c e n
  | .uH | .sH | .hH | .aH => Situation.capH (mOf k n) (TOf k c e n) d
  | .iX => n + 1
  | .iE => k.eval n
  | .iF => (TOf k c e n + 1) * d + 1

def F4 (k : Polynomial ℕ) (c e d n : ℕ) : CC → ℕ
  | .s .B => mOf k n + c
  | .s .Dd => d
  | .t y => tv k c e d n y
  | _ => 0

noncomputable def cB (k : Polynomial ℕ) (c e d n : ℕ) : ℕ :=
  1 + hornT (coeffs k) n 0 + (k.eval n + 1) + (n + 1) + 2 + (2 * mOf k n + 2) + 3 + powB e 1 (mOf k n + c) +
    1 + (d * (2 * TOf k c e n + 3) + d + 2) + 1 + (d * TOf k c e n + d + 2) + (mOf k n + 1) +
    (TOf k c e n + 1) + (Situation.capH (mOf k n) (TOf k c e n) d + 1)

open CC PS PT in

theorem cprog_run (k : Polynomial ℕ) (c e d n : ℕ) (v : Bool) (o : List Bool) :
    RunLe (cprog k c e d) (cB k c e d n) ⟨some .p1, v, st (F0 n) o⟩
      ⟨some .done, false, st (F4 k c e d n) o⟩ := by
  refine Bud.start ?_
  refine (emitS (M := cprog k c e d) (self := .p1) rfl _ _ _).bud ?_
  obtain ⟨vh, rh⟩ := horner_run (M := cprog k c e d) (b := s N) (acc := s P) (q := s Q)
    (ad := s AD) (t := s TMP) (coeffs k) (mk := hlab) (exit := .x1)
    (fun i hi q => by rw [show hlab i q = PL.hr ⟨i, hi⟩ q from dif_pos hi]; rfl) (by decide)
    (coeffs k).length 0 (by omega)
    (update (F0 n) (s P) (0 + F0 n (s P))) (by simp [F0]) (by simp [F0]) (by simp [F0]) v o
  rw [List.drop_zero] at rh
  refine rh.bud ?_
  refine bud_st (F' := F1 k n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [F0, F1, hornVal_coeffs]) ?_
  refine (xferS (M := cprog k c e d) (self := .x1) (next := .x2) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x2) (next := .x3) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x3) (next := .x4) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x4) (next := .c1) rfl _ _ _).bud ?_
  refine (copyS (M := cprog k c e d) (l₁ := .c1) (l₂ := .c2) (next := .x6) rfl rfl (by decide)
    (by decide) (by decide) _ (by simp [xf, F1]) _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x6) (next := .x7) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x7) (next := .x8) rfl _ _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x8) (next := .w2 .hd) rfl _ _ _).bud ?_
  refine bud_st (F' := F2 k c e n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [xf, F1, F2, mOf] <;> omega) ?_
  refine (pow_run (M := cprog k c e d) (mk := PL.w2) (exit := .x9) (fun _ => rfl) (by decide) e _
    (by simp [F2]) (by simp [F2]) (by simp [F2]) (by simp [F2]) _ _).bud ?_
  refine bud_st (F' := F3 k c e n) (by
    funext z; rcases z with z | z <;> cases z <;> simp [F2, F3, TOf]) ?_
  refine (emitS (M := cprog k c e d) (self := .x9) (next := .ml .head) rfl _ _ _).bud ?_
  refine (mulS_run (M := cprog k c e d) (mk := PL.ml) (next := .x10) (fun _ => rfl) (by decide) _
    (by simp [F3]) (by simp [F3]) _ _).bud ?_
  refine (emitS (M := cprog k c e d) (self := .x10) (next := .x11) rfl _ _ _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x11) (next := .x12) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x12) (next := .x13) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x13) (next := .x14) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine (xferS (M := cprog k c e d) (self := .x14) (next := .done) rfl (by decide) (by decide) _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [xf, F0, F1, F2, F3, cB, Situation.capH, mOf]
    generalize TOf k c e n = T
    linarith
  · congr 2
    funext z; rcases z with z | z <;> cases z <;> simp [xf, F3, F4, tv, Situation.capH] <;> ring

open Cslib.Complexity.CookLevin.Assembly

inductive FK
  | h (k : HK)
  | raw
  | pc (x : PS)
  deriving DecidableEq, Fintype

abbrev FΓ (g r : ℕ) : FK → Type
  | .h k => HΓ g k
  | .raw => Fin r
  | .pc _ => Unit

inductive FL (D : ℕ) (Λ : Type)
  | rd
  | pre (l : PL D)
  | h (l : Λ)
  deriving DecidableEq, Fintype

def tgt : PT → HK
  | .uT => .up .Tn
  | .uH => .up .Hs
  | .sT => .sd .Tn
  | .sH => .sd .Hs
  | .hT => .sh .Tn
  | .hH => .sh .Hs
  | .aT => .ac .Tn
  | .aH => .ac .Hs
  | .iT => .ini .Tn
  | .iX => .ini .Xn
  | .iE => .ini .En
  | .iF => .ini .Fn

def eC : SK CC → FK
  | .out => .h .out
  | .c (.s x) => .pc x
  | .c (.t y) => .h (tgt y)

section Embs

variable (g r : ℕ)

def embC : SEmb (SΓ CC) (FΓ g r) where
  e := eC
  inj := by
    intro a b h
    rcases a with _ | (x | y) <;> rcases b with _ | (x' | y') <;>
      simp only [eC, FK.h.injEq, FK.pc.injEq, reduceCtorEq] at h ⊢
    all_goals first
      | exact h
      | (subst h; rfl)
      | (cases y <;> cases h)
      | (cases y' <;> cases h)
      | (cases y <;> cases y' <;> first | rfl | cases h)
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c (.s _) => Equiv.refl _
    | .c (.t y) => match y with
      | .uT | .uH | .sT | .sH | .hT | .hH | .aT | .aH | .iT | .iX | .iE | .iF => Equiv.refl _

def embH : SEmb (HΓ g) (FΓ g r) where
  e := FK.h
  inj := fun _ _ h => by cases h; rfl
  ι := fun _ => Equiv.refl _

end Embs

section Read

variable {g r D : ℕ} {Λ : Type}

def rdT (cf : Fin r → Fin g) (cs : Fin g) : List (Fin r) → TM2.Stmt (FΓ g r) (FL D Λ) Bool
  | [] => .push (.h .inp) (fun _ => cs) (.load (fun _ => false) (.goto fun _ => .pre .p1))
  | i :: L => .peek .raw (fun _ o => decide (o = some i))
      (.branch id (.pop .raw (fun v _ => v) (.push (.h .inp) (fun _ => cf i)
        (.push (.pc .N) (fun _ => ()) (.goto fun _ => .rd)))) (rdT cf cs L))

def fst (s : List (Fin r)) (ins : List (Fin g)) (n : ℕ) (o : List Bool) : ∀ k, List (FΓ g r k)
  | .raw => s
  | .h .inp => ins
  | .h .out => o
  | .pc .N => cnt () n
  | _ => []

theorem rdT_hit (cf : Fin r → Fin g) (cs : Fin g) (a : Fin r) (s : List (Fin r))
    (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    ∀ (L : List (Fin r)), a ∈ L → ∀ v : Bool,
      TM2.stepAux (rdT (D := D) (Λ := Λ) cf cs L) v (fst (a :: s) ins n o) =
        ⟨some .rd, true, fst s (cf a :: ins) (n + 1) o⟩ := by
  intro L
  induction L with
  | nil => intro h; cases h
  | cons i L ih =>
      intro h v
      by_cases hi : a = i
      · subst hi
        simp only [rdT, TM2.stepAux]
        simp only [fst, List.head?_cons, decide_true, id, cond_true, List.tail_cons]
        congr 1
        funext k
        rcases k with k | _ | x
        · cases k <;> simp [fst]
        · simp [fst]
        · cases x <;> simp [fst, cnt_succ]
      · have hL : a ∈ L := by
          rcases List.mem_cons.1 h with h | h
          · exact absurd h hi
          · exact h
        simp only [rdT, TM2.stepAux]
        simp only [fst, List.head?_cons, Option.some.injEq, hi, decide_false, id, cond_false]
        exact ih hL false

theorem rdT_nil (cf : Fin r → Fin g) (cs : Fin g) (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    ∀ (L : List (Fin r)) (v : Bool),
      TM2.stepAux (rdT (D := D) (Λ := Λ) cf cs L) v (fst [] ins n o) =
        ⟨some (.pre .p1), false, fst [] (cs :: ins) n o⟩ := by
  intro L
  induction L with
  | nil =>
      intro v
      simp only [rdT, TM2.stepAux]
      congr 1
      funext k
      rcases k with k | _ | x
      · cases k <;> simp [fst]
      · simp [fst]
      · cases x <;> simp [fst]
  | cons i L ih =>
      intro v
      simp only [rdT, TM2.stepAux]
      simp only [fst, List.head?_nil, reduceCtorEq, decide_false, id, cond_false]
      exact ih false

theorem read_run {M : FL D Λ → TM2.Stmt (FΓ g r) (FL D Λ) Bool} {cf : Fin r → Fin g} {cs : Fin g}
    (hM : M .rd = rdT cf cs (List.finRange r)) (o : List Bool) :
    ∀ (s : List (Fin r)) (ins : List (Fin g)) (n : ℕ) (v : Bool),
      Run M (s.length + 1) ⟨some .rd, v, fst s ins n o⟩
        ⟨some (.pre .p1), false, fst [] (cs :: ((s.map cf).reverse ++ ins)) (n + s.length) o⟩ := by
  intro s
  induction s with
  | nil =>
      intro ins n v
      refine Run.single ?_
      simp [hM, rdT_nil]
  | cons a s ih =>
      intro ins n v
      have := ih (cf a :: ins) (n + 1) true
      rw [show (s.map cf).reverse ++ cf a :: ins = ((a :: s).map cf).reverse ++ ins by simp,
        show n + 1 + s.length = n + (a :: s).length by simp; omega] at this
      refine Run.head ?_ this
      simp only [TM2.step, hM, rdT_hit cf cs a s ins n o _ (List.mem_finRange a)]

end Read

section Comp

variable {g r : ℕ} {Λ : Type}

noncomputable def fprog (cf : Fin r → Fin g) (cs : Fin g) (k : Polynomial ℕ) (c e d : ℕ) (hp : Λ → TM2.Stmt (HΓ g) Λ Bool)
    (start : Λ) : FL (coeffs k).length Λ → TM2.Stmt (FΓ g r) (FL (coeffs k).length Λ) Bool
  | .rd => rdT cf cs (List.finRange r)
  | .pre l => if l = .done then .load (fun _ => false) (.goto fun _ => .h start)
      else mapS (embC g r) FL.pre (cprog k c e d l)
  | .h l => mapS (embH g r) FL.h (hp l)

variable {cf : Fin r → Fin g} {cs : Fin g} {k : Polynomial ℕ} {c e d : ℕ} {hp : Λ → TM2.Stmt (HΓ g) Λ Bool}
  {start : Λ}

theorem embeds_C : Embeds (embC g r) FL.pre (cprog k c e d) (fprog cf cs k c e d hp start) := by
  intro l
  by_cases hl : l = .done
  · exact Or.inr (by subst hl; rfl)
  · exact Or.inl (by simp only [fprog, if_neg hl])

theorem embeds_H : Embeds (embH g r) FL.h hp (fprog cf cs k c e d hp start) :=
  fun _ => Or.inl rfl

theorem agree_C (ins : List (Fin g)) (n : ℕ) (o : List Bool) :
    Agree (embC g r) (st (F0 n) o) (fst [] ins n o) := by
  intro k
  rcases k with _ | (x | y)
  · exact (List.map_id _).symm
  · cases x <;> exact (List.map_id _).symm
  · cases y <;> exact (List.map_id _).symm

theorem eC_ne_inp (k : SK CC) : eC k ≠ .h .inp := by
  rcases k with _ | (x | y) <;> simp [eC]
  cases y <;> simp [tgt]

theorem pre_run (s : List (Fin r)) (o : List Bool) :
    ∃ S : ∀ k, List (FΓ g r k),
      RunLe (fprog cf cs k c e d hp start) (s.length + 1 + cB k c e d s.length + 1)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h start), false, S⟩ ∧
      S (.h .out) = o ∧ S (.h .inp) = cs :: (s.map cf).reverse ∧
      (∀ y, (S (.h (tgt y))).length = tv k c e d s.length y) ∧
      (∀ hk, (∀ y, tgt y ≠ hk) → hk ≠ .out → hk ≠ .inp → S (.h hk) = []) := by
  have r1 := read_run (M := fprog cf cs k c e d hp start) rfl o s [] 0 false
  rw [List.append_nil, Nat.zero_add] at r1
  obtain ⟨T1, r2, a2, f2⟩ := runLe_embed (E := embC g r) FL.pre embeds_C
    (cprog_run k c e d s.length false o) (agree_C _ _ o)
  have r3 : Run (fprog cf cs k c e d hp start) 1 ⟨some (.pre .done), false, T1⟩
      ⟨some (.h start), false, T1⟩ :=
    Run.single (by simp [fprog, TM2.stepAux])
  refine ⟨T1, ((r1.le le_rfl).trans r2).trans (r3.le le_rfl), (a2 .out).trans (List.map_id _),
    ?_, fun y => by
      have := congrArg List.length (a2 (.c (.t y)))
      rw [List.length_map] at this
      exact this.trans (by simp [F4]), fun hk h1 h2 h3 => ?_⟩
  · exact (f2 _ eC_ne_inp).trans rfl
  · rw [f2 _ (fun k => by
      rcases k with _ | (x | y)
      · exact fun h => h2 (FK.h.inj h).symm
      · simp [embC, eC]
      · exact fun h => h1 y (FK.h.inj h))]
    cases hk with
    | out => exact absurd rfl h2
    | inp => exact absurd rfl h3
    | _ => rfl

end Comp

section Real

open Cslib.Complexity.CookLevin.Situation

variable {r : ℕ} {M : FinTM2} (E : Enc M)

noncomputable abbrev fullProg (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) :=
  fprog (fun i => InitFamily.encF E (ι i)) (InitFamily.encF E sep) k c e (depth M) (realProg E Ys acc)
    (.ini (.pre1 .eg))

noncomputable def fullB (Ys : List (M.Γ M.k₀)) (k : Polynomial ℕ) (c e n : ℕ) : ℕ :=
  n + 1 + cB k c e (depth M) n + 1 + realB E Ys (mOf k n) (TOf k c e n)

theorem cnt_of_len {l : List Unit} {n : ℕ} (h : l.length = n) : l = cnt () n :=
  List.eq_replicate_iff.2 ⟨h, fun _ _ => rfl⟩

theorem full_run (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (FΓ E.layout.g r k)),
      RunLe (fullProg E Ys acc ι sep k c e) (fullB E Ys k c e s.length)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h .fin), v, S⟩ ∧
      S (.h .out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
        (TOf k c e s.length)) ++ o := by
  obtain ⟨T1, r1, ho, hin, ht, hz⟩ := pre_run (cf := fun i => InitFamily.encF E (ι i))
    (cs := InitFamily.encF E sep) (k := k) (c := c) (e := e) (d := depth M) (hp := realProg E Ys acc)
    (start := .ini (.pre1 .eg)) s o
  have e1 : (s.map ι ++ [sep]).length = s.length + 1 := by simp
  have hx : (s.map ι ++ [sep]).length ≤ mOf k s.length := by rw [e1, mOf]; omega
  have e2 : mOf k s.length - (s.length + 1) = k.eval s.length := by rw [mOf]; omega
  have e3 : capH (mOf k s.length) (TOf k c e s.length) (depth M) - mOf k s.length =
      (TOf k c e s.length + 1) * depth M + 1 := by unfold capH; omega
  have nt : ∀ hk : HK, (∀ y, tgt y ≠ hk) → hk ≠ .out → hk ≠ .inp →
      T1 (.h hk) = [] := hz
  obtain ⟨v, S, hr, hout⟩ := real_run E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
    (TOf k c e s.length) hx (fun hk => T1 (.h hk)) o ho
    (hin.trans (by simp [List.map_append, List.reverse_append]))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .uT)
      case Hs => exact cnt_of_len (ht .uH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .sT)
      case Hs => exact cnt_of_len (ht .sH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .hT)
      case Hs => exact cnt_of_len (ht .hH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      cases z
      case Tn => exact cnt_of_len (ht .aT)
      case Hs => exact cnt_of_len (ht .aH)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
    (fun z => by
      rw [e1, e2, e3]
      cases z
      case Tn => exact cnt_of_len (ht .iT)
      case Xn => exact cnt_of_len (ht .iX)
      case En => exact cnt_of_len (ht .iE)
      case Fn => exact cnt_of_len (ht .iF)
      all_goals exact nt _ (by intro y; cases y <;> simp [tgt]) (by simp) (by simp))
  obtain ⟨T2, r2, a2, -⟩ := runLe_embed (E := embH E.layout.g r) FL.h embeds_H hr
    (S' := T1) (fun _ => (List.map_id _).symm)
  exact ⟨v, T2, r1.trans r2, ((a2 .out).trans (List.map_id _)).trans hout⟩

noncomputable def fullTM (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : FinTM2 where
  K := FK
  k₀ := .raw
  k₁ := .h .out
  Γ := FΓ E.layout.g r
  Λ := FL _ _
  main := .rd
  σ := Bool
  initialState := false
  m := fullProg E Ys acc ι sep k c e

theorem initList_full (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) :
    initList (fullTM E Ys acc ι sep k c e) s = ⟨some .rd, false, fst s [] 0 []⟩ := by
  simp only [initList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · cases x <;> rfl

end Real

def NatPolynomialBound (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n = p.eval n

namespace NatPolynomialBound

theorem const (a : ℕ) : NatPolynomialBound fun _ => a := ⟨Polynomial.C a, fun _ => by simp⟩

theorem id : NatPolynomialBound fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : NatPolynomialBound f) (hg : NatPolynomialBound g) : NatPolynomialBound fun n => f n + g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p + q, fun n => by simp [hp, hq]⟩

theorem mul {f g : ℕ → ℕ} (hf : NatPolynomialBound f) (hg : NatPolynomialBound g) : NatPolynomialBound fun n => f n * g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p * q, fun n => by simp [hp, hq]⟩

theorem pow {f : ℕ → ℕ} (hf : NatPolynomialBound f) (j : ℕ) : NatPolynomialBound fun n => f n ^ j := by
  obtain ⟨p, hp⟩ := hf; exact ⟨p ^ j, fun n => by simp [hp]⟩

theorem eval (p : Polynomial ℕ) : NatPolynomialBound fun n => p.eval n := ⟨p, fun _ => rfl⟩

theorem hornT (cs : List ℕ) : ∀ {A : ℕ → ℕ}, NatPolynomialBound A → NatPolynomialBound fun n => Precompute.hornT cs n (A n) := by
  induction cs with
  | nil => intro A _; exact const 0
  | cons a cs ih =>
      intro A hA
      have hstep : NatPolynomialBound fun n => hornStep (A n) n := by
        unfold hornStep
        exact ((((((hA.mul ((const 2).mul id |>.add (const 3))).add hA).add (const 2)).add
          (hA.add (const 1))).add ((hA.mul id).add (const 1))).add (const 1))
      exact hstep.add (ih ((hA.mul id).add (const a)))

end NatPolynomialBound

theorem fullB_poly {M : FinTM2} (E : Situation.Enc M) (Ys : List (M.Γ M.k₀)) (k : Polynomial ℕ) (c e : ℕ) :
    NatPolynomialBound (fullB E Ys k c e) := by
  unfold fullB
  simp only [cB, powB, realB, TOf, mOf, Situation.capH]
  generalize InitFamily.initC _ _ _ = A1
  generalize Family.genC _ _ = A2
  generalize Shift.shC _ _ = A3
  generalize Accept.accC _ _ _ = A4
  generalize Situation.depth M = d

  repeat' first
    | exact NatPolynomialBound.hornT _ (NatPolynomialBound.const 0)
    | exact NatPolynomialBound.eval _
    | with_reducible exact NatPolynomialBound.const _
    | with_reducible exact NatPolynomialBound.id
    | with_reducible apply NatPolynomialBound.add
    | with_reducible apply NatPolynomialBound.mul
    | with_reducible apply NatPolynomialBound.pow

theorem full_time_poly {r : ℕ} {M : FinTM2} (E : Situation.Enc M) (Ys : List (M.Γ M.k₀))
    (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (s : List (Fin r)) (o : List Bool), ∃ (v : Bool) (S : ∀ k,
        List (FΓ E.layout.g r k)),
      RunLe (fullProg E Ys acc ι sep k c e) (p.eval s.length)
        ⟨some .rd, false, fst s [] 0 o⟩ ⟨some (.h .fin), v, S⟩ ∧
      S (.h .out) = encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length)
        (TOf k c e s.length)) ++ o := by
  obtain ⟨p, hp⟩ := fullB_poly E Ys k c e
  refine ⟨p, fun s o => ?_⟩
  obtain ⟨v, S, h1, h2⟩ := full_run E Ys acc ι sep k c e s o
  exact ⟨v, S, h1.mono (hp _).le, h2⟩

end Cslib.Complexity.CookLevin.Precompute
end

-- CSLibExt.Computability.Complexity.CookLevin.Package
section
namespace Cslib.Complexity.CookLevin.Package

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT MetaMathlibExt.TM2Embedding Cslib.Complexity.CookLevin.Precompute Turing Function

section Grow

open Cslib.Complexity.CookLevin.Situation

theorem run_height {M : FinTM2} {n : ℕ} {c d : M.Cfg} (h : Run M.m n c d) (k : M.K) :
    (d.stk k).length ≤ (c.stk k).length + n * depth M := by
  rw [← runI_of_iterate M n c d h]
  exact runI_height c k n

end Grow

section Drain

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Flag σ]
  {M : Λ → TM2.Stmt Γ Λ σ}

theorem xfer_drain {self next : Λ} {k : K} (hp : M self = xfer k [] self next) :
    ∀ (l : List (Γ k)) (v : σ) (S : ∀ k, List (Γ k)), S k = l →
      Run M (l.length + 1) ⟨some self, v, S⟩ ⟨some next, Flag.tag false, update S k []⟩ := by
  intro l
  induction l with
  | nil =>
      intro v S hS
      have hu : update S k [] = S := by rw [← hS, update_eq_self]
      refine Run.single ?_
      simp only [hp, xfer, TM2.stepAux, hS, List.head?_nil, Option.isSome_none, List.tail_nil,
        Flag.untag_tag, cond_false, hu]
  | cons x l ih =>
      intro v S hS
      have hstep : TM2.step M ⟨some self, v, S⟩ =
          some ⟨some self, Flag.tag true, update S k l⟩ := by
        simp only [TM2.step, hp, xfer, TM2.stepAux, hS, List.head?_cons, Option.isSome_some,
          List.tail_cons, Flag.untag_tag, cond_true, pushAll, List.foldr_nil]
      have key := Run.head hstep (ih (Flag.tag true) (update S k l) (by simp))
      rw [update_idem] at key
      exact key.of_eq (by simp)

def drainS (ks : List K) (lab : ℕ → Λ) (i : ℕ) : TM2.Stmt Γ Λ σ :=
  match ks[i]? with
  | some k => xfer k [] (lab i) (lab (i + 1))
  | none => .load (fun _ => Flag.tag false) .halt

def drainB (ks : List K) (S : ∀ k, List (Γ k)) : ℕ :=
  (ks.map fun k => (S k).length + 1).sum + 1

theorem drain_run :
    ∀ (ks : List K) (lab : ℕ → Λ), ks.Nodup → (∀ i ≤ ks.length, M (lab i) = drainS ks lab i) →
      ∀ (v : σ) (S : ∀ k, List (Γ k)),
        Run M (drainB ks S) ⟨some (lab 0), v, S⟩
          ⟨none, Flag.tag false, fun k => if k ∈ ks then [] else S k⟩ := by
  intro ks
  induction ks with
  | nil =>
      intro lab _ hp v S
      refine Run.single ?_
      rw [hp 0 le_rfl]
      simp [drainS, TM2.stepAux]
  | cons k ks ih =>
      intro lab hnd hp v S
      rw [List.nodup_cons] at hnd
      have r1 := xfer_drain (M := M) (self := lab 0) (next := lab 1) (k := k)
        (by rw [hp 0 (by simp)]; rfl) (S k) v S rfl
      have r2 := ih (fun j => lab (j + 1)) hnd.2 (fun i hi => by
        rw [hp (i + 1) (by simp; omega)]; rfl) (Flag.tag false) (update S k [])
      have e1 : drainB ks (update S k []) = drainB ks S := by
        unfold drainB
        congr 2
        refine List.map_congr_left fun k' hk' => ?_
        rw [update_of_ne (fun h : k' = k => hnd.1 (h ▸ hk'))]
      have e2 : (fun k' => if k' ∈ ks then [] else update S k [] k') =
          fun k' => if k' ∈ k :: ks then [] else S k' := by
        funext k'
        by_cases h1 : k' = k
        · subst h1; simp
        · by_cases h2 : k' ∈ ks <;> simp [h1, h2]
      rw [e1, e2] at r2
      exact (r1.trans r2).of_eq (by simp [drainB]; omega)

end Drain

section Glue

inductive DL (Λ : Type) (n : ℕ)
  | f (l : Λ)
  | dr (i : Fin (n + 1))
  deriving DecidableEq, Fintype

def dlab {Λ : Type} (n j : ℕ) : DL Λ n := .dr ⟨min j n, by omega⟩

def idE {K : Type} (Γ : K → Type) : SEmb Γ Γ := ⟨id, injective_id, fun _ => Equiv.refl _⟩

noncomputable def dks : List FK := (Finset.univ.erase (FK.h .out)).toList

theorem mem_dks (q : FK) : q ∈ dks ↔ q ≠ FK.h .out := by simp [dks]

theorem dks_nodup : dks.Nodup := Finset.nodup_toList _

theorem drained {Γ : FK → Type} (T : ∀ k, List (Γ k)) :
    (fun q => if q ∈ dks then [] else T q) = fun q => if q = FK.h .out then T q else [] := by
  funext q
  by_cases hq : q = FK.h .out
  · rw [if_pos hq, if_neg (by rw [mem_dks]; exact not_not.2 hq)]
  · rw [if_neg hq, if_pos ((mem_dks q).2 hq)]

variable {g r : ℕ} {Λ : Type} [DecidableEq Λ]

noncomputable def gprog (P : Λ → TM2.Stmt (FΓ g r) Λ Bool) (fin : Λ) :
    DL Λ dks.length → TM2.Stmt (FΓ g r) (DL Λ dks.length) Bool
  | .f l => if l = fin then .goto (fun _ => dlab _ 0) else mapS (idE _) DL.f (P l)
  | .dr i => drainS dks (dlab _) i.val

theorem embeds_g {P : Λ → TM2.Stmt (FΓ g r) Λ Bool} {fin : Λ} (hfin : P fin = .halt) :
    Embeds (idE (FΓ g r)) DL.f P (gprog P fin) := by
  intro l
  by_cases hl : l = fin
  · exact Or.inr (hl ▸ hfin)
  · exact Or.inl (by simp only [gprog, if_neg hl])

theorem g_run_gen {P : Λ → TM2.Stmt (FΓ g r) Λ Bool} {fin : Λ} (hfin : P fin = .halt)
    {B : ℕ} {l : Λ} {v v' : Bool} {S T : ∀ k, List (FΓ g r k)}
    (h : RunLe P B ⟨some l, v, S⟩ ⟨some fin, v', T⟩) :
    RunLe (gprog P fin) (B + 1 + drainB dks T) ⟨some (.f l), v, S⟩
      ⟨none, false, fun k => if k ∈ dks then [] else T k⟩ := by
  obtain ⟨T', r1, a1, -⟩ := runLe_embed (E := idE (FΓ g r)) DL.f (embeds_g hfin) h
    (S' := S) (fun _ => (List.map_id _).symm)
  have hT : T' = T := funext fun k => (a1 k).trans (List.map_id _)
  subst hT
  have r2 : Run (gprog P fin) 1 ⟨some (.f fin), v', T'⟩ ⟨some (dlab _ 0), v', T'⟩ :=
    Run.single (by simp [gprog, TM2.stepAux])
  have r3 := drain_run (M := gprog P fin) dks (dlab _) dks_nodup
    (fun i hi => by simp [gprog, dlab, min_eq_left hi]) v' T'
  exact (r1.trans (r2.le le_rfl)).trans (r3.le le_rfl)

theorem drainB_le {T : ∀ k, List (FΓ g r k)} {h : ℕ} (hT : ∀ k, (T k).length ≤ h) :
    drainB dks T ≤ dks.length * (h + 1) + 1 := by
  unfold drainB
  have := List.sum_le_card_nsmul (dks.map fun k => (T k).length + 1) (h + 1) (by
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact Nat.add_le_add_right (hT k) 1)
  simp only [List.length_map, smul_eq_mul] at this
  omega

end Glue

section Real

open Cslib.Complexity.CookLevin.Situation Cslib.Complexity.CookLevin.Assembly

variable {r : ℕ} {M : FinTM2} (E : Enc M)

theorem fullProg_fin (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : fullProg E Ys acc ι sep k c e (.h .fin) = .halt := rfl

noncomputable def gTM (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : FinTM2 where
  K := FK
  k₀ := .raw
  k₁ := .h .out
  Γ := FΓ E.layout.g r
  Λ := DL (FL _ _) dks.length
  main := .f .rd
  σ := Bool
  initialState := false
  m := gprog (fullProg E Ys acc ι sep k c e) (.h .fin)

noncomputable def phiOf (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) : List Bool :=
  encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length) (TOf k c e s.length))

noncomputable def gB (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e n : ℕ) : ℕ :=
  fullB E Ys k c e n + 1 +
    (dks.length * (n + fullB E Ys k c e n * depth (fullTM E Ys acc ι sep k c e) + 1) + 1)

theorem initList_g (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) :
    initList (gTM E Ys acc ι sep k c e) s = ⟨some (.f .rd), false, fst s [] 0 []⟩ := by
  simp only [initList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · cases x <;> rfl

theorem haltList_g (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (T : ∀ k, List (FΓ E.layout.g r k)) :
    haltList (gTM E Ys acc ι sep k c e) (T (.h .out)) =
      ⟨none, false, fun q : FK => if q = FK.h .out then T q else []⟩ := by
  classical
  simp only [haltList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · rfl

theorem g_run (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) :
    RunLe (gTM E Ys acc ι sep k c e).m (gB E Ys acc ι sep k c e s.length)
      (initList (gTM E Ys acc ι sep k c e) s)
      (haltList (gTM E Ys acc ι sep k c e) (phiOf E Ys acc ι sep k c e s)) := by
  obtain ⟨v, S, ⟨n1, hn1, r1⟩, hout⟩ := full_run E Ys acc ι sep k c e s []
  rw [List.append_nil] at hout

  have hh : ∀ q, (S q).length ≤
      s.length + fullB E Ys k c e s.length * depth (fullTM E Ys acc ι sep k c e) := by
    intro q
    have r1' : Run (fullTM E Ys acc ι sep k c e).m n1 (initList (fullTM E Ys acc ι sep k c e) s)
        ⟨some (.h .fin), v, S⟩ := by rw [initList_full]; exact r1
    have h1 := run_height r1' q
    have h2 : ((initList (fullTM E Ys acc ι sep k c e) s).stk q).length ≤ s.length :=
      initList_height (M := fullTM E Ys acc ι sep k c e) s q
    have h3 := Nat.mul_le_mul_right (depth (fullTM E Ys acc ι sep k c e)) hn1
    exact h1.trans (by omega)
  have hg := g_run_gen (fullProg_fin E Ys acc ι sep k c e) ⟨n1, hn1, r1⟩
  rw [drained] at hg
  rw [initList_g, show phiOf E Ys acc ι sep k c e s = S (.h .out) from hout.symm, haltList_g]
  refine hg.mono ?_
  have := drainB_le hh
  unfold gB
  omega

end Real

section Pkg

open Cslib.Complexity.CookLevin.Situation Cslib.Complexity.CookLevin.Assembly

noncomputable def outputsOfRunLe {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)}
    {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l')) :
    TM2OutputsInTime tm l (some l') B where
  steps := Classical.choose h
  evals_in_steps := (Classical.choose_spec h).2
  steps_le_m := (Classical.choose_spec h).1

noncomputable def outputsOfRunLe' {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' l'' : List (tm.Γ tm.k₁)} {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l''))
    (he : l'' = l') : TM2OutputsInTime tm l (some l') B :=
  outputsOfRunLe (he ▸ h)

variable {r : ℕ} {M : FinTM2} (E : Enc M)

theorem gB_poly (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : NatPolynomialBound (gB E Ys acc ι sep k c e) := by
  unfold gB
  generalize depth (fullTM E Ys acc ι sep k c e) = D
  generalize (dks : List FK).length = L
  have hf := fullB_poly E Ys k c e
  exact (hf.add (NatPolynomialBound.const 1)).add (((NatPolynomialBound.const L).mul
    ((NatPolynomialBound.id.add (hf.mul (NatPolynomialBound.const D))).add (NatPolynomialBound.const 1))).add (NatPolynomialBound.const 1))

theorem g_outputs (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) :
    ∃ p : Polynomial ℕ, ∀ s : List (Fin r),
      Nonempty (TM2OutputsInTime (gTM E Ys acc ι sep k c e) s
        (some (phiOf E Ys acc ι sep k c e s)) (p.eval s.length)) := by
  obtain ⟨p, hp⟩ := gB_poly E Ys acc ι sep k c e
  exact ⟨p, fun s => ⟨outputsOfRunLe ((g_run E Ys acc ι sep k c e s).mono (hp _).le)⟩⟩

noncomputable def fR {α αΓ : Type} (ea : α → List αΓ) (eqv : Fin r ≃ αΓ)
    (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k : Polynomial ℕ) (c e : ℕ) (a : α) : List Bool :=
  phiOf E Ys acc ι sep k c e ((ea a).map eqv.invFun)

noncomputable def gComp {α αΓ : Type} (ea : α → List αΓ) (eqv : Fin r ≃ αΓ)
    (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k : Polynomial ℕ) (c e : ℕ) :
    TM2ComputableInPolyTime ea (fun l : List Bool => l)
      (fR E ea eqv Ys acc ι sep k c e) where
  tm := gTM E Ys acc ι sep k c e
  inputAlphabet := eqv
  outputAlphabet := Equiv.refl Bool
  time := Classical.choose (gB_poly E Ys acc ι sep k c e)
  outputsFun a := outputsOfRunLe' (by
    have h := g_run E Ys acc ι sep k c e ((ea a).map eqv.invFun)
    rw [List.length_map, Classical.choose_spec (gB_poly E Ys acc ι sep k c e)] at h
    exact h) (List.map_id _).symm

end Pkg

end Cslib.Complexity.CookLevin.Package
end

-- CSLibExt.Computability.Complexity.CookLevin.Hardness
section
namespace Cslib.Complexity.CookLevin.Hardness

open MetaMathlibExt ComplexityTheory Cslib.Complexity.DenseSAT Cslib.Complexity.CookLevin.Situation
  Cslib.Complexity.CookLevin.Assembly Cslib.Complexity.CookLevin.Precompute
  Cslib.Complexity.CookLevin.Package Turing

theorem pow_weaken {j c e c' e' : ℕ} (hc : 1 ≤ c) (h1 : c ≤ c') (h2 : e ≤ e') :
    (j + c) ^ e ≤ (j + c') ^ e' :=
  (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) h2)

theorem eval_le_pow (p : Polynomial ℕ) : ∃ c e, 1 ≤ c ∧ ∀ j, p.eval j ≤ (j + c) ^ e := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨c1, e1, hc1, h1⟩ := hp
      obtain ⟨c2, e2, hc2, h2⟩ := hq
      refine ⟨c1 + c2, e1 + e2 + 1, by omega, fun j => ?_⟩
      have a1 := (h1 j).trans
        (pow_weaken (j := j) hc1 (Nat.le_add_right c1 c2) (Nat.le_add_right e1 e2))
      have a2 := (h2 j).trans
        (pow_weaken (j := j) hc2 (Nat.le_add_left c2 c1) (Nat.le_add_left e2 e1))
      have h2le : 2 ≤ j + (c1 + c2) := by omega
      rw [Polynomial.eval_add, pow_succ]
      calc p.eval j + q.eval j
          ≤ (j + (c1 + c2)) ^ (e1 + e2) + (j + (c1 + c2)) ^ (e1 + e2) := Nat.add_le_add a1 a2
        _ = (j + (c1 + c2)) ^ (e1 + e2) * 2 := by ring
        _ ≤ (j + (c1 + c2)) ^ (e1 + e2) * (j + (c1 + c2)) := Nat.mul_le_mul_left _ h2le
  | monomial n a =>
      refine ⟨a + 1, n + 1, by omega, fun j => ?_⟩
      rw [Polynomial.eval_monomial, pow_succ]
      calc a * j ^ n ≤ (j + (a + 1)) * (j + (a + 1)) ^ n :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) n)
        _ = _ := mul_comm _ _

theorem pull {α β : Type} (f : α → β) (L : List α) :
    ∀ l : List β, (∀ z ∈ l, z ∈ L.map f) → ∃ l0 : List α, l0.map f = l
  | [], _ => ⟨[], rfl⟩
  | z :: l, h => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 (h z (by simp))
      obtain ⟨l0, rfl⟩ := pull f L l (fun w hw => h w (by simp [hw]))
      exact ⟨u :: l0, rfl⟩

section Classical

open Classical

noncomputable def symSetX (M : FinTM2) (acc : M.Γ M.k₁) (k : M.K) : Finset (M.Γ k) :=
  symSet M k ∪ (if h : M.k₁ = k then {cast (congrArg M.Γ h) acc} else ∅)

theorem acc_mem_symSetX (M : FinTM2) (acc : M.Γ M.k₁) : acc ∈ symSetX M acc M.k₁ := by
  unfold symSetX
  exact Finset.mem_union_right _ (by rw [dif_pos rfl]; exact Finset.mem_singleton_self _)

noncomputable def encX (M : FinTM2) (acc : M.Γ M.k₁) : Enc M :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { KK := Fintype.card M.K
    kc := fun k => Fintype.equivFin M.K k
    kd := fun n => if h : n < Fintype.card M.K then (Fintype.equivFin M.K).symm ⟨n, h⟩ else M.k₀
    kc_lt := fun k => (Fintype.equivFin M.K k).2
    kd_kc := fun k => by simp
    kc_kd := fun n hn => by simp [hn]
    A0 := Fintype.card (Option M.Λ × M.σ)
    lc := fun x => Fintype.equivFin _ x
    ld := fun c => if h : c < Fintype.card (Option M.Λ × M.σ) then
      (Fintype.equivFin _).symm ⟨c, h⟩ else (none, M.initialState)
    lc_lt := fun x => (Fintype.equivFin _ x).2
    ld_lc := fun x => by rw [dif_pos (Fintype.equivFin _ x).2]; simp
    lc_ld := fun c hc => by rw [dif_pos hc]; simp
    sz := fun k => (symSetX M acc k).card
    dec := fun k i => ((symSetX M acc k).equivFin.symm i).1
    enc := fun k x => if h : x ∈ symSetX M acc k then (symSetX M acc k).equivFin ⟨x, h⟩ + 1 else 0
    enc_dec := fun k i => by simp
    push_mem := fun l k x h => ⟨(symSetX M acc k).equivFin
      ⟨x, Finset.mem_union_left _ (push_mem_symSet M l k x h)⟩, by simp⟩
    input_mem := fun x => ⟨(symSetX M acc M.k₀).equivFin
      ⟨x, Finset.mem_union_left _ (input_mem_symSet M x)⟩, by simp⟩ }

theorem encX_acc (M : FinTM2) (acc : M.Γ M.k₁) : ∃ i, (encX M acc).dec M.k₁ i = acc :=
  ⟨(symSetX M acc M.k₁).equivFin ⟨acc, acc_mem_symSetX M acc⟩, by simp [encX]⟩

end Classical

section Ver

variable {fv : List Bool × List Bool → Bool}
  (V : TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) fv)

def vacc : V.tm.Γ V.tm.k₁ := V.outputAlphabet.symm true

noncomputable def vE : Enc V.tm := encX V.tm (vacc V)

noncomputable def veqv : Fin (Fintype.card Bool) ≃ Bool := (Fintype.equivFin Bool).symm

noncomputable def vι (i : Fin (Fintype.card Bool)) : V.tm.Γ V.tm.k₀ :=
  V.inputAlphabet.symm (Sum.inl (veqv i))

def vsep : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr none)

def vY (g : Bool) : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr (some g))

noncomputable def vYs : List (V.tm.Γ V.tm.k₀) := (Finset.univ : Finset Bool).toList.map (vY V)

noncomputable def vc : ℕ := Classical.choose (eval_le_pow V.time)

noncomputable def ve : ℕ := Classical.choose (Classical.choose_spec (eval_le_pow V.time))

theorem v_time (j : ℕ) : V.time.eval j ≤ (j + vc V) ^ ve V :=
  (Classical.choose_spec (Classical.choose_spec (eval_le_pow V.time))).2 j

theorem v_input (a y : List Bool) :
    List.map V.inputAlphabet.invFun (Verifier.pairEncode (a, y)) =
      (a.map veqv.invFun).map (vι V) ++ [vsep V] ++ y.map (vY V) := by
  unfold vι vsep vY
  simp [Verifier.pairEncode, Function.comp_def]
  exact ⟨fun _ => veqv.apply_symm_apply _, fun _ => veqv.apply_symm_apply _⟩

theorem v_run (a y : List Bool) {T : ℕ} (hT : V.time.eval (a.length + 1 + y.length) ≤ T) :
    runI V.tm (initList V.tm ((a.map veqv.invFun).map (vι V) ++ [vsep V] ++ y.map (vY V))) T =
      haltList V.tm [V.outputAlphabet.symm (fv (a, y))] := by
  have h := V.outputsFun (a, y)
  rw [v_input] at h
  have hl : (Verifier.pairEncode (a, y)).length = a.length + 1 + y.length := by
    simp only [Verifier.pairEncode, List.length_append, List.length_cons, List.length_map]
    omega
  rw [hl] at h
  exact runI_haltList V.tm _ _ h hT

noncomputable def red (p : Polynomial ℕ) : List Bool → List Bool :=
  fR (vE V) (fun l : List Bool => l) veqv (vYs V) (vacc V) (vι V) (vsep V) p (vc V) (ve V)

theorem v_correct {R : List Bool → List Bool → Prop} {p : Polynomial ℕ} {L' : List Bool → Prop}
    (hfv : ∀ q : List Bool × List Bool, R q.1 q.2 ↔ fv q = true)
    (hL : ∀ a, L' a ↔ ∃ y : List Bool, y.length ≤ p.eval a.length ∧ R a y) (a : List Bool) :
    L' a ↔ SAT (red V p a) := by
  set n := a.length with hn
  set s := a.map veqv.invFun with hs
  have hsl : s.length = n := by rw [hs, List.length_map]
  have hx : (s.map (vι V) ++ [vsep V]).length ≤ mOf p s.length := by
    simp only [List.length_append, List.length_map, List.length_singleton, mOf]; omega
  change L' a ↔ ∃ asg, cnfSat (decodeCNF (encodeCNF (Phi (vE V) (s.map (vι V) ++ [vsep V]) (vYs V)
    (vacc V) (mOf p s.length) (TOf p (vc V) (ve V) s.length)))) asg
  rw [decodeCNF_encodeCNF, phi_iff (vE V) hx (encX_acc _ _), hL, hsl]
  have hT : ∀ y : List Bool, n + 1 + y.length ≤ mOf p n →
      V.time.eval (n + 1 + y.length) ≤ TOf p (vc V) (ve V) n := fun y hy =>
    (TM2Composition.eval_mono _ hy).trans (v_time V _)
  have hacc : ∀ y : List Bool, n + 1 + y.length ≤ mOf p n →
      (Accepts V.tm (runI V.tm (initList V.tm (s.map (vι V) ++ [vsep V] ++ y.map (vY V)))
        (TOf p (vc V) (ve V) n)) (vacc V) ↔ fv (a, y) = true) := by
    intro y hy
    rw [hs, v_run V a y (hT y hy), accepts_haltList]
    simp [vacc]
  constructor
  · rintro ⟨y, hy, hR⟩
    rw [← hn] at hy
    have hyl : n + 1 + y.length ≤ mOf p n := by unfold mOf; omega
    refine ⟨y.map (vY V), fun z hz => ?_, ?_, (hacc y hyl).2 ((hfv (a, y)).1 hR)⟩
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hz
      exact List.mem_map.2 ⟨g, Finset.mem_toList.2 (Finset.mem_univ g), rfl⟩
    · simp only [List.length_append, List.length_map, List.length_singleton]; rw [hsl]; exact hyl
  · rintro ⟨y', hY, hlen, hA⟩
    obtain ⟨y, rfl⟩ := pull (vY V) _ y' hY
    have hyl : n + 1 + y.length ≤ mOf p n := by
      simp only [List.length_append, List.length_map, List.length_singleton] at hlen
      rw [hsl] at hlen; exact hlen
    refine ⟨y, by rw [← hn]; unfold mOf at hyl; omega, (hfv (a, y)).2 ((hacc y hyl).1 ?_)⟩
    exact hA

theorem isPolyTime_red (p : Polynomial ℕ) : IsPolyTime (red V p) := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable
    (gComp (vE V) (fun l : List Bool => l) veqv (vYs V) (vacc V) (vι V) (vsep V) p (vc V) (ve V))
  have h2 := tm2ComputableInPolyTime_comp h EncodeBits.computable
  exact h2

end Ver

theorem denseSatDec_npHard (L : DecisionProblem) (hL : L ∈ NP) :
    Cslib.Complexity.PolyManyOneRed L denseSatDec := by
  obtain ⟨p, R, ⟨V₀⟩, hLR⟩ := hL
  let V : TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) (R ∘ id) :=
    TM2Composition.compComputable ToCanonical.computable V₀
  refine ⟨red V p, isPolyTime_red V p, fun x => ?_⟩
  have h := v_correct V (R := fun a y => R (a, y) = true) (L' := fun a => L a = true)
    (fun _ => Iff.rfl) hLR x
  classical
  rw [Bool.eq_iff_iff, denseSatDec, decide_eq_true_iff]
  exact h

theorem denseSatDec_npComplete :
    denseSatDec ∈ NP ∧
      ∀ L : DecisionProblem, L ∈ NP → Cslib.Complexity.PolyManyOneRed L denseSatDec :=
  ⟨denseSatDec_mem_NP, denseSatDec_npHard⟩

end Cslib.Complexity.CookLevin.Hardness
end

theorem OMA.solution :
    type_of% @DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP := by
  intro h
  let C := Cslib.Complexity.DenseSAT.denseSatDec
  obtain ⟨hC, hard⟩ := Cslib.Complexity.CookLevin.Hardness.denseSatDec_npComplete
  have hco : C ∈ ComplexityTheory.coNP := h ▸ hC
  refine ⟨C, Cᶜ, ⟨hC, hco, ?_⟩, ?_⟩
  · intro x
    change ¬ (C x = true ∧ (! C x) = true)
    cases C x <;> decide
  · intro A B pair
    obtain ⟨f, poly, correct⟩ := hard A pair.memA
    refine ⟨f, poly, fun x hx => (correct x).symm.trans hx, ?_⟩
    intro x hx
    change (! C (f x)) = true
    have hn : A x ≠ true := fun hit => pair.disjoint x ⟨hit, hx⟩
    change (! Cslib.Complexity.DenseSAT.denseSatDec (f x)) = true
    rw [← correct x]
    cases ha : A x <;> simp_all

