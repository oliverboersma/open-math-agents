import FormalConjectures.Wikipedia.CernyConjecture
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
The finite bound below is adapted from Anton Borisov’s cerny-lean, revision
cce904976550e15a378a13e424f2bf3ca7eea9c2, with permission under Apache-2.0.
https://github.com/antonborisov571/cerny-lean/tree/cce904976550e15a378a13e424f2bf3ca7eea9c2/Cerny

The retained material comes from Defs.lean, Combinatorial.lean,
AdditionalClasses.lean and SubPinFrankl.lean. This port restates the
image-cardinality lemma from SmallCases.lean using a Mathlib theorem,
adjusts the proof for the pinned Mathlib and connects the finite bound
to the upstream DFA type and uniform little-o claim.

The mathematical result is due to Yaroslav Shitov, An improvement to a
recent upper bound for synchronizing words of finite automata, J. Autom.
Lang. Comb. 24 (2019), 367–373. https://arxiv.org/abs/1901.06542
-/

--                                  Apache License
--                            Version 2.0, January 2004
--                         http://www.apache.org/licenses/
--
--    TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION
--
--    1. Definitions.
--
--       "License" shall mean the terms and conditions for use, reproduction,
--       and distribution as defined by Sections 1 through 9 of this document.
--
--       "Licensor" shall mean the copyright owner or entity authorized by
--       the copyright owner that is granting the License.
--
--       "Legal Entity" shall mean the union of the acting entity and all
--       other entities that control, are controlled by, or are under common
--       control with that entity. For the purposes of this definition,
--       "control" means (i) the power, direct or indirect, to cause the
--       direction of the management or policies of such entity, whether by
--       contract or otherwise, or (ii) ownership of fifty percent (50%) or
--       more of the outstanding shares, or (iii) beneficial ownership of
--       such entity.
--
--       "You" (or "Your") shall mean an individual or Legal Entity
--       exercising permissions granted by this License.
--
--       "Source" form shall mean the preferred form for making modifications,
--       including but not limited to software source code, documentation
--       source, and configuration files.
--
--       "Object" form shall mean any form resulting from mechanical
--       transformation or translation of a Source form, including but
--       not limited to compiled object code, generated documentation,
--       and conversions to other media types.
--
--       "Work" shall mean the work of authorship, whether in Source or
--       Object form, made available under the License, as indicated by a
--       copyright notice that is included in or attached to the work
--       (an example is provided in the Appendix below).
--
--       "Derivative Works" shall mean any work, whether in Source or Object
--       form, that is based on (or derived from) the Work and for which the
--       editorial revisions, annotations, elaborations, or other modifications
--       represent, as a whole, an original work of authorship. For the purposes
--       of this License, Derivative Works shall not include works that remain
--       separable from, or merely link (or bind) by name to the interfaces of,
--       the Work and Derivative Works thereof.
--
--       "Contribution" shall mean any work of authorship, including
--       the original version of the Work and any modifications or additions
--       to that Work or Derivative Works thereof, that is intentionally
--       submitted to Licensor for inclusion in the Work by the copyright owner
--       or by an individual or Legal Entity authorized to submit on behalf of
--       the copyright owner. For the purposes of this definition, "submitted"
--       means any form of electronic, verbal, or written communication sent
--       to the Licensor or its representatives, including but not limited to
--       communication on electronic mailing lists, source code hosting systems,
--       and issue tracking systems that are managed by, or on behalf of, the
--       Licensor for the purpose of discussing and improving the Work, but
--       excluding communication that is conspicuously marked or otherwise
--       designated in writing by the Licensor as "Not a Contribution."
--
--       "Contributor" shall mean Licensor and any individual or Legal Entity
--       authorized to submit on behalf of the Work and whose Contribution has
--       been received by Licensor and subsequently incorporated within the Work.
--
--    2. Grant of Copyright License. Subject to the terms and conditions of
--       this License, each Contributor hereby grants to You a perpetual,
--       worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--       copyright license to reproduce, prepare Derivative Works of,
--       publicly display, publicly perform, sublicense, and distribute the
--       Work and such Derivative Works in Source or Object form.
--
--    3. Grant of Patent License. Subject to the terms and conditions of
--       this License, each Contributor hereby grants to You a perpetual,
--       worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--       (except as stated in this section) patent license to make, have made,
--       use, offer to sell, sell, import, and otherwise transfer the Work,
--       where such license applies only to those patent claims licensable
--       by such Contributor that are necessarily infringed by their
--       Contribution(s) alone or by combination of their Contribution(s)
--       with the Work to which such Contribution(s) was submitted. If You
--       institute patent litigation against any entity (including a
--       cross-claim or counterclaim in a lawsuit) alleging that the Work
--       or a Contribution incorporated within the Work constitutes direct
--       or contributory patent infringement, then any patent licenses
--       granted to You under this License for this Work shall terminate
--       as of the date such litigation is filed.
--
--    4. Redistribution. You may reproduce and distribute copies of the
--       Work or Derivative Works thereof in any medium, with or without
--       modifications, and in Source or Object form, provided that You
--       meet the following conditions:
--
--       (a) You must give any other recipients of the Work or
--           Derivative Works a copy of this License; and
--
--       (b) You must cause any modified files to carry prominent notices
--           stating that You changed the files; and
--
--       (c) You must retain, in the Source form of any Derivative Works
--           that You distribute, all copyright, patent, trademark, and
--           attribution notices from the Source form of the Work,
--           excluding those notices that do not pertain to any part of
--           the Work; and
--
--       (d) If the Work includes a "NOTICE" text file as part of its
--           distribution, then any Derivative Works that You distribute must
--           include a readable copy of the attribution notices contained
--           within such NOTICE file, excluding those notices that do not
--           pertain to any part of the Work, in at least one of the
--           following places: within a NOTICE text file distributed
--           as part of the Work; within a text file or other documentation
--           provided along with the Work; or, within a display generated
--           by the Derivative Works, if and wherever such third-party notices
--           are normally distributed. The contents of the NOTICE file are
--           for informational purposes only and do not modify the License. You
--           may add Your own copyright notice to Your own Derivative Works
--           and may provide additional or different licensing terms and
--           notice requirements for the Derivative Works, provided that Your
--           use, reproduction, and distribution of Your own Derivative Works
--           are otherwise in compliance with the License.
--
--    5. Submission of Contributions. Unless You explicitly state otherwise,
--       any Contribution intentionally submitted for inclusion in the Work
--       by You to Licensor shall be under the terms and conditions of
--       this License, without any additional terms or conditions.
--       Notwithstanding the above, nothing herein shall supersede or modify
--       the terms of any separate license agreement that You may have
--       executed with Licensor with respect to such Contribution.
--
--    6. Trademarks. This License does not grant permission to use the trade
--       names, trademarks, service marks, or product names of the Licensor,
--       except as required for reasonable and factual attribution of the
--       Work and for reproducing the contents of the NOTICE file.
--
--    7. Disclaimer of Warranty. Unless required by applicable law or
--       agreed to in writing, Licensor provides the Work (and each
--       Contributor provides its Contribution) on an "AS IS" BASIS,
--       WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
--       implied, including, without limitation, any warranties or conditions
--       of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
--       PARTICULAR PURPOSE. You are solely responsible for determining the
--       interest or appropriateness of using or redistributing the Work and
--       assume any risks associated with Your exercise of permissions under
--       this License.
--
--    8. Limitation of Liability. In no event and under the terms of any
--       legal theory, whether in tort (including negligence), contract,
--       or otherwise, unless required by applicable law (such as deliberate
--       and grossly negligent acts) or agreed to in writing, shall any
--       Contributor be liable to You for damages, including any direct,
--       indirect, special, incidental, or consequential damages of any
--       character arising as a result of this License or out of the use or inability
--       to use the Work (including but not limited to damages for loss of
--       goodwill, work stoppage, computer failure or malfunction, or any
--       and all other commercial damages or losses), even if such Contributor
--       has been advised of the possibility of such damages.
--
--    9. Accepting Warranty or Liability. While redistributing the Work or
--       Derivative Works thereof, You may choose to offer, and legally
--       accept, additional terms and conditions, and/or charge a fee
--       for support, warranty, or indemnity obligations consistent with
--       this License. However, in accepting such obligations, You may act
--       only on Your own behalf and on Your own responsibility, and not
--       on behalf of any other Contributor, and only if You agree to indemnify,
--       defend, and hold each Contributor harmless for any liability
--       incurred by, or claims associated with, such Contributor.
--
--    END OF TERMS AND CONDITIONS
--
--    APPENDIX: How to apply the Apache License to your work.
--
--       To apply the Apache License to your work, attach the following
--       boilerplate notice, with the fields enclosed by brackets "[]"
--       replaced with your own identifying information. (Don't include
--       the brackets!)  The text should be enclosed in the appropriate
--       comment syntax for the file. We also recommend that a file or
--       class name and a description of the file should be included on the
--       same line as the "same page" as the copyright notice for easier
--       identification within third-party archives.
--
--    Copyright 2026 Anton Borisov
--
--    Licensed under the Apache License, Version 2.0 (the "License");
--    you may not use this file except in compliance with the License.
--    You may obtain a copy of the License at
--
--        http://www.apache.org/licenses/LICENSE-2.0
--
--    Unless required by applicable law or agreed to in writing, software
--    distributed under the License is distributed on an "AS IS" BASIS,
--    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
--    See the License for the specific language governing permissions and
--    limitations under the License.

namespace Cerny

universe u v

/-- A deterministic finite (semi)automaton with state set `Q` and input alphabet `α`. -/
structure DFA (Q : Type u) (α : Type v) where
  /-- Transition function: `step q a` is the state reached from `q` on input letter `a`. -/
  step : Q → α → Q

namespace DFA

variable {Q : Type u} {α : Type v}

/- ### Word evaluation -/

/-- Evaluate a word `w` starting from state `q` by folding transitions from left to right. -/
def eval (A : DFA Q α) (q : Q) (w : List α) : Q :=
  w.foldl A.step q

@[simp]
theorem eval_nil (A : DFA Q α) (q : Q) : A.eval q [] = q :=
  rfl

@[simp]
theorem eval_cons (A : DFA Q α) (q : Q) (a : α) (w : List α) :
    A.eval q (a :: w) = A.eval (A.step q a) w :=
  rfl

@[simp]
theorem eval_singleton (A : DFA Q α) (q : Q) (a : α) : A.eval q [a] = A.step q a :=
  rfl

@[simp]
theorem eval_append (A : DFA Q α) (q : Q) (u v : List α) :
    A.eval q (u ++ v) = A.eval (A.eval q u) v := by
  simp [eval, List.foldl_append]

theorem eval_replicate (A : DFA Q α) (q : Q) (n : ℕ) (a : α) :
    A.eval q (List.replicate n a) = (fun x => A.step x a)^[n] q := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, eval_cons, ih, Function.iterate_succ_apply]

/- ### Forward images and backward preimages -/

/-- Forward image of a finite set of states `S` under word `w`. -/
def image [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) : Finset Q :=
  S.image (fun q => A.eval q w)

/-- Backward preimage of a finite set of states `S` under word `w`. -/
def preimage [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) : Finset Q :=
  Finset.univ.filter (fun q => A.eval q w ∈ S)

@[simp]
theorem mem_image [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) (q : Q) :
    q ∈ A.image S w ↔ ∃ p ∈ S, A.eval p w = q :=
  Finset.mem_image

@[simp]
theorem image_nil [DecidableEq Q] (A : DFA Q α) (S : Finset Q) :
    A.image S [] = S := by
  simp [image]

@[simp]
theorem image_append [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (u v : List α) :
    A.image S (u ++ v) = A.image (A.image S u) v := by
  ext q
  simp only [mem_image, eval_append]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨A.eval p u, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem image_cons [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (a : α) (w : List α) :
    A.image S (a :: w) = A.image (A.image S [a]) w := by
  simpa using A.image_append S [a] w

@[simp]
theorem image_empty [DecidableEq Q] (A : DFA Q α) (w : List α) :
    A.image ∅ w = ∅ := by
  simp [image]

@[simp]
theorem image_singleton [DecidableEq Q] (A : DFA Q α) (q : Q) (w : List α) :
    A.image {q} w = {A.eval q w} := by
  simp [image]

theorem image_mono [DecidableEq Q] (A : DFA Q α) {S T : Finset Q} (h : S ⊆ T) (w : List α) :
    A.image S w ⊆ A.image T w :=
  Finset.image_subset_image h

theorem card_image_le [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) :
    (A.image S w).card ≤ S.card :=
  Finset.card_image_le

@[simp]
theorem mem_preimage [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α)
    (q : Q) : q ∈ A.preimage S w ↔ A.eval q w ∈ S := by
  simp [preimage]

@[simp]
theorem preimage_nil [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) :
    A.preimage S [] = S := by
  ext q
  simp

@[simp]
theorem preimage_append [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (u v : List α) :
    A.preimage S (u ++ v) = A.preimage (A.preimage S v) u := by
  ext q
  simp

theorem preimage_cons [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (a : α)
    (w : List α) : A.preimage S (a :: w) = A.preimage (A.preimage S w) [a] := by
  ext q
  simp

@[simp]
theorem preimage_empty [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    A.preimage ∅ w = ∅ := by
  ext q
  simp

@[simp]
theorem preimage_univ [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    A.preimage Finset.univ w = Finset.univ := by
  ext q
  simp

theorem preimage_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α) {S T : Finset Q} (h : S ⊆ T)
    (w : List α) : A.preimage S w ⊆ A.preimage T w := by
  intro q hq
  simp only [mem_preimage] at hq ⊢
  exact h hq

theorem preimage_union [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S T : Finset Q) (w : List α) :
    A.preimage (S ∪ T) w = A.preimage S w ∪ A.preimage T w := by
  ext q
  simp

theorem preimage_inter [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S T : Finset Q) (w : List α) :
    A.preimage (S ∩ T) w = A.preimage S w ∩ A.preimage T w := by
  ext q
  simp

theorem preimage_compl [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q) (w : List α) :
    A.preimage Sᶜ w = (A.preimage S w)ᶜ := by
  ext q
  simp

theorem image_subset_iff_subset_preimage [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (S T : Finset Q) (w : List α) : A.image S w ⊆ T ↔ S ⊆ A.preimage T w := by
  simp [Finset.subset_iff]

theorem card_preimage_eq_sum_singleton [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q)
    (w : List α) : (A.preimage S w).card = ∑ q ∈ S, (A.preimage {q} w).card := by
  have h : A.preimage S w = S.biUnion (fun q => A.preimage {q} w) := by
    ext p
    simp
  rw [h, Finset.card_biUnion]
  intro q₁ _ q₂ _ hne
  change Disjoint (A.preimage {q₁} w) (A.preimage {q₂} w)
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  simp only [mem_preimage, Finset.mem_singleton] at hp₁ hp₂
  exact hne (hp₁.symm.trans hp₂)

theorem sum_card_preimage_singleton [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    ∑ q : Q, (A.preimage {q} w).card = Fintype.card Q := by
  rw [← card_preimage_eq_sum_singleton, preimage_univ, Finset.card_univ]

/- ### Synchronizing words and reset threshold -/

/-- A word `w` is a synchronizing (reset) word for `A` if it sends every state to the same state. -/
def IsSyncWord (A : DFA Q α) (w : List α) : Prop :=
  ∃ q₀ : Q, ∀ q : Q, A.eval q w = q₀

theorem IsSyncWord.nonempty {A : DFA Q α} {w : List α} (hw : A.IsSyncWord w) : Nonempty Q :=
  let ⟨q₀, _⟩ := hw
  ⟨q₀⟩

theorem isSyncWord_iff_card_image_univ_eq_one [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (w : List α) : A.IsSyncWord w ↔ (A.image Finset.univ w).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, ?_⟩
    ext q
    simp only [mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨p, hp⟩ => hp.symm.trans (hq₀ p), fun h => ⟨q₀, (hq₀ q₀).trans h.symm⟩⟩
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, fun q => ?_⟩
    have hmem : A.eval q w ∈ A.image Finset.univ w := by
      rw [mem_image]
      exact ⟨q, Finset.mem_univ q, rfl⟩
    rw [hq₀, Finset.mem_singleton] at hmem
    exact hmem

theorem isSyncWord_iff_exists_preimage_eq_univ [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (w : List α) : A.IsSyncWord w ↔ ∃ q₀ : Q, A.preimage {q₀} w = Finset.univ := by
  constructor
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, ?_⟩
    ext q
    simp [hq₀ q]
  · rintro ⟨q₀, hq₀⟩
    refine ⟨q₀, fun q => ?_⟩
    have hmem : q ∈ A.preimage {q₀} w := by
      rw [hq₀]
      exact Finset.mem_univ q
    simpa using hmem

theorem isSyncWord_append_right (A : DFA Q α) {u : List α} (hu : A.IsSyncWord u) (v : List α) :
    A.IsSyncWord (u ++ v) := by
  rcases hu with ⟨q₀, hq₀⟩
  exact ⟨A.eval q₀ v, fun q => by rw [eval_append, hq₀ q]⟩

theorem isSyncWord_append_left (A : DFA Q α) (u : List α) {v : List α} (hv : A.IsSyncWord v) :
    A.IsSyncWord (u ++ v) := by
  rcases hv with ⟨q₀, hq₀⟩
  exact ⟨q₀, fun q => by rw [eval_append, hq₀]⟩

/-- A DFA is synchronizing if it admits at least one synchronizing word. -/
def IsSynchronizing (A : DFA Q α) : Prop :=
  ∃ w : List α, A.IsSyncWord w

theorem IsSynchronizing.nonempty {A : DFA Q α} (h : A.IsSynchronizing) : Nonempty Q :=
  let ⟨_, hw⟩ := h
  hw.nonempty

end DFA

/- ## Pin–Frankl cubic bound -/

section PinFrankl

/-- Ordered pairs `(u, v)` in `Fin (b + 1) × Fin (b + 1)` with `u ≤ v`. -/
private abbrev SymPairIdx (b : ℕ) := { p : Fin (b + 1) × Fin (b + 1) // p.1 ≤ p.2 }

private theorem sum_range_succ_eq_choose (b : ℕ) :
    ∑ v ∈ Finset.range (b + 1), (v + 1) = (b + 2).choose 2 := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    have hsucc : (b + 1 + 2).choose 2 = (b + 2).choose 1 + (b + 2).choose 2 := by
      exact Nat.choose_succ_succ (b + 2) 1
    rw [hsucc, Nat.choose_one_right, add_comm]

private theorem card_symPairIdx (b : ℕ) :
    Fintype.card (SymPairIdx b) = (b + 2).choose 2 := by
  let e : SymPairIdx b ≃ Σ v : Fin (b + 1), Fin (v.val + 1) :=
    { toFun := fun ⟨(u, v), huv⟩ => ⟨v, ⟨u.val, Nat.lt_succ_of_le huv⟩⟩
      invFun := fun ⟨v, u⟩ =>
        ⟨(⟨u.val, lt_of_lt_of_le u.isLt (Nat.succ_le_of_lt v.isLt)⟩, v),
          Nat.le_of_lt_succ u.isLt⟩
      left_inv := fun ⟨(u, v), huv⟩ => rfl
      right_inv := fun ⟨v, u⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun v => v + 1) (b + 1)]
  exact sum_range_succ_eq_choose b

private theorem sum_symPairIdx_eq (b : ℕ) (c a d : Fin (b + 1) → ℚ) :
    (∑ p : SymPairIdx b,
      (c p.1.1 * c p.1.2) *
        (if p.1.1 = p.1.2 then a p.1.1 * d p.1.1
         else a p.1.1 * d p.1.2 + a p.1.2 * d p.1.1)) =
    (∑ u : Fin (b + 1), c u * a u) * (∑ v : Fin (b + 1), c v * d v) := by
  let S_le : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.1 ≤ p.2)
  let S_eq : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.1 = p.2)
  let S_lt : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.1 < p.2)
  let S_gt : Finset (Fin (b + 1) × Fin (b + 1)) := Finset.univ.filter (fun p => p.2 < p.1)
  let F : Fin (b + 1) × Fin (b + 1) → ℚ := fun p =>
    (c p.1 * c p.2) * (if p.1 = p.2 then a p.1 * d p.1 else a p.1 * d p.2 + a p.2 * d p.1)
  have hsub_sum : (∑ p : SymPairIdx b, F p.1) = ∑ p ∈ S_le, F p := by
    exact (Finset.sum_subtype S_le (p := fun p : Fin (b + 1) × Fin (b + 1) => p.1 ≤ p.2)
      (fun p => by simp [S_le]) F).symm
  have hle_union : S_le = S_eq ∪ S_lt := by
    ext p
    simp only [S_le, S_eq, S_lt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact le_iff_eq_or_lt
  have hdisj_eq_lt : Disjoint S_eq S_lt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S_eq, S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    exact ne_of_lt hp2 hp1
  have hswap :
      (∑ p ∈ S_lt, c p.1 * c p.2 * (a p.2 * d p.1)) =
      ∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2) := by
    refine Finset.sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.swap_injective h
    · intro p hp
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact hp
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      ring
  have hsum_eq : (∑ p ∈ S_eq, F p) = ∑ p ∈ S_eq, c p.1 * a p.1 * (c p.2 * d p.2) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [F, hp, ↓reduceIte]
    ring
  have hsum_lt : (∑ p ∈ S_lt, F p) =
      (∑ p ∈ S_lt, c p.1 * a p.1 * (c p.2 * d p.2)) +
      (∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2)) := by
    rw [← hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hne : p.1 ≠ p.2 := ne_of_lt hp
    simp only [F, hne, ↓reduceIte]
    ring
  have huniv_eq : (Finset.univ : Finset (Fin (b + 1) × Fin (b + 1))) = S_le ∪ S_gt := by
    ext p
    simp only [S_le, S_gt, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    exact le_or_gt p.1 p.2
  have hdisj_le_gt : Disjoint S_le S_gt := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [S_le, S_gt, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    exact not_lt_of_ge hp1 hp2
  calc
    (∑ p : SymPairIdx b, F p.1)
        = ∑ p ∈ S_le, F p := hsub_sum
    _ = (∑ p ∈ S_eq, F p) + (∑ p ∈ S_lt, F p) := by
        rw [hle_union, Finset.sum_union hdisj_eq_lt]
    _ = ((∑ p ∈ S_eq, c p.1 * a p.1 * (c p.2 * d p.2)) +
          (∑ p ∈ S_lt, c p.1 * a p.1 * (c p.2 * d p.2))) +
        (∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2)) := by
        rw [hsum_eq, hsum_lt, add_assoc]
    _ = (∑ p ∈ S_le, c p.1 * a p.1 * (c p.2 * d p.2)) +
        (∑ p ∈ S_gt, c p.1 * a p.1 * (c p.2 * d p.2)) := by
        rw [hle_union, Finset.sum_union hdisj_eq_lt]
    _ = ∑ p : Fin (b + 1) × Fin (b + 1), c p.1 * a p.1 * (c p.2 * d p.2) := by
        rw [← Finset.sum_union hdisj_le_gt, ← huniv_eq]
    _ = (∑ u : Fin (b + 1), c u * a u) * (∑ v : Fin (b + 1), c v * d v) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Frankl's Skew Bollobás Theorem (`a = 2`), proved over `ℚ` using symmetric
products of univariate polynomials (zero exterior algebra). -/
theorem frankl_skew_two {Q : Type*} [Fintype Q] [DecidableEq Q]
    (m b : ℕ) (x y : Fin m → Q) (B : Fin m → Finset Q)
    (hB : ∀ i, (B i).card ≤ b)
    (hdisj : ∀ i, x i ∉ B i ∧ y i ∉ B i)
    (hinter : ∀ i j : Fin m, j < i → x i ∈ B j ∨ y i ∈ B j) :
    m ≤ (b + 2).choose 2 := by
  let t : Q → ℚ := fun q => ((Fintype.equivFin Q q).val : ℚ)
  have ht_inj : Function.Injective t := by
    intro q₁ q₂ hq
    dsimp [t] at hq
    have hval : (Fintype.equivFin Q q₁).val = (Fintype.equivFin Q q₂).val := by
      exact_mod_cast hq
    exact (Fintype.equivFin Q).injective (Fin.ext hval)
  let P : Fin m → Polynomial ℚ := fun j =>
    ∏ q ∈ B j, (Polynomial.X - Polynomial.C (t q))
  have hP_deg : ∀ j : Fin m, (P j).natDegree ≤ b := by
    intro j
    calc (P j).natDegree
        ≤ ∑ q ∈ B j, (Polynomial.X - Polynomial.C (t q)).natDegree :=
          Polynomial.natDegree_prod_le (B j) _
      _ = ∑ _q ∈ B j, 1 := Finset.sum_congr rfl fun q _ => Polynomial.natDegree_X_sub_C (t q)
      _ = (B j).card := by simp
      _ ≤ b := hB j
  have hP_eval : ∀ (j : Fin m) (r : ℚ),
      (P j).eval r = ∑ u : Fin (b + 1), (P j).coeff u.val * r ^ u.val := by
    intro j r
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hP_deg j)),
      ← Fin.sum_univ_eq_sum_range]
  have hP_eval_prod : ∀ (j : Fin m) (r : ℚ),
      (P j).eval r = ∏ q ∈ B j, (r - t q) := by
    intro j r
    simp [P, Polynomial.eval_prod]
  let w : Fin m → (SymPairIdx b → ℚ) := fun j p =>
    (P j).coeff p.1.1.val * (P j).coeff p.1.2.val
  let z : Fin m → (SymPairIdx b → ℚ) := fun i p =>
    if p.1.1 = p.1.2 then (t (x i)) ^ p.1.1.val * (t (y i)) ^ p.1.1.val
    else (t (x i)) ^ p.1.1.val * (t (y i)) ^ p.1.2.val +
         (t (x i)) ^ p.1.2.val * (t (y i)) ^ p.1.1.val
  have hdot : ∀ i j : Fin m,
      (∑ p : SymPairIdx b, w j p * z i p) = (P j).eval (t (x i)) * (P j).eval (t (y i)) := by
    intro i j
    rw [hP_eval j (t (x i)), hP_eval j (t (y i))]
    exact sum_symPairIdx_eq b (fun u => (P j).coeff u.val)
      (fun u => (t (x i)) ^ u.val) (fun v => (t (y i)) ^ v.val)
  have hdot_lt : ∀ i j : Fin m, j < i → (∑ p : SymPairIdx b, w j p * z i p) = 0 := by
    intro i j hji
    rw [hdot, hP_eval_prod, hP_eval_prod]
    rcases hinter i j hji with hx | hy
    · have h0 : ∏ q ∈ B j, (t (x i) - t q) = 0 :=
        Finset.prod_eq_zero hx (sub_self _)
      rw [h0, zero_mul]
    · have h0 : ∏ q ∈ B j, (t (y i) - t q) = 0 :=
        Finset.prod_eq_zero hy (sub_self _)
      rw [h0, mul_zero]
  have hdot_diag : ∀ i : Fin m, (∑ p : SymPairIdx b, w i p * z i p) ≠ 0 := by
    intro i
    rw [hdot, hP_eval_prod, hP_eval_prod]
    refine mul_ne_zero ?_ ?_
    · rw [Finset.prod_ne_zero_iff]
      intro q hq hsub
      exact (hdisj i).1 ((ht_inj (sub_eq_zero.mp hsub)) ▸ hq)
    · rw [Finset.prod_ne_zero_iff]
      intro q hq hsub
      exact (hdisj i).2 ((ht_inj (sub_eq_zero.mp hsub)) ▸ hq)
  have hlin : LinearIndependent ℚ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    let s := Finset.univ.filter (fun j : Fin m => c j ≠ 0)
    have hs_ne : s.Nonempty := by
      rcases hne with ⟨j, hj⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    let i := s.max' hs_ne
    have hi_mem : i ∈ s := Finset.max'_mem s hs_ne
    have hci_ne : c i ≠ 0 := (Finset.mem_filter.mp hi_mem).2
    have hsum0 : (∑ p : SymPairIdx b, (∑ j : Fin m, c j • w j) p * z i p) = 0 := by
      rw [hc]
      simp
    have hswap :
        (∑ p : SymPairIdx b, (∑ j : Fin m, c j • w j) p * z i p) =
        ∑ j : Fin m, c j * (∑ p : SymPairIdx b, w j p * z i p) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hswap] at hsum0
    have hsingle : (∑ j : Fin m, c j * (∑ p : SymPairIdx b, w j p * z i p)) =
        c i * (∑ p : SymPairIdx b, w i p * z i p) := by
      refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [hdot_lt i j hlt, mul_zero]
      · have hcj0 : c j = 0 := by
          by_contra hcj_ne
          have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcj_ne⟩
          exact not_lt_of_ge (Finset.le_max' s j hjs) hgt
        rw [hcj0, zero_mul]
    rw [hsingle] at hsum0
    exact mul_ne_zero hci_ne (hdot_diag i) hsum0
  have hcard := hlin.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_pi, card_symPairIdx] at hcard
  exact hcard

/-- Pin's Compression Lemma (1983): in a synchronizing `n`-state DFA, every subset `R` of
size `r ≥ 2` is compressed (`|R · w| < r`) by some word `w` of length at most `(n - r + 2).choose 2`. -/
theorem pin_compression_bound {Q α : Type*} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) (R : Finset Q) (hR : 2 ≤ R.card) :
    ∃ w : List α, w.length ≤ (Fintype.card Q - R.card + 2).choose 2 ∧
      (A.image R w).card < R.card := by
  classical
  have hex : ∃ k : ℕ, ∃ w : List α, w.length = k ∧ (A.image R w).card < R.card := by
    rcases hSync with ⟨w, q₀, hq₀⟩
    refine ⟨w.length, w, rfl, ?_⟩
    have hsub : A.image R w ⊆ {q₀} := by
      intro q hq
      rw [DFA.mem_image] at hq
      rcases hq with ⟨p, _, rfl⟩
      simp [hq₀ p]
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  let m := Nat.find hex
  obtain ⟨w, hwlen, hwcomp⟩ := Nat.find_spec hex
  have hmin : ∀ v : List α, (A.image R v).card < R.card → m ≤ v.length := fun v hv =>
    Nat.find_min' hex ⟨v, rfl, hv⟩
  refine ⟨w, ?_, hwcomp⟩
  rw [hwlen]
  -- Pick distinct x₀, y₀ ∈ R merged by w
  have hex_pair : ∃ x₀ ∈ R, ∃ y₀ ∈ R, x₀ ≠ y₀ ∧ A.eval x₀ w = A.eval y₀ w := by
    by_contra hall
    push Not at hall
    have hinj : Set.InjOn (fun q => A.eval q w) R := fun x hx y hy hxy => by
      by_contra hne
      exact hall x hx y hy hne hxy
    have heq := Finset.card_image_of_injOn hinj
    change (A.image R w).card = R.card at heq
    omega
  rcases hex_pair with ⟨x₀, hx₀, y₀, hy₀, hx₀y₀, hmerge⟩
  let x : Fin m → Q := fun k => A.eval x₀ (w.take k.val)
  let y : Fin m → Q := fun k => A.eval y₀ (w.take k.val)
  let Rk : Fin m → Finset Q := fun k => A.image R (w.take k.val)
  let B : Fin m → Finset Q := fun k => Finset.univ \ Rk k
  have hRk_card : ∀ k : Fin m, (Rk k).card = R.card := by
    intro k
    have hle : (Rk k).card ≤ R.card := A.card_image_le R (w.take k.val)
    have hnotlt : ¬ (Rk k).card < R.card := by
      intro hlt
      have hb := hmin (w.take k.val) hlt
      rw [List.length_take] at hb
      omega
    omega
  have hB_card : ∀ k : Fin m, (B k).card ≤ Fintype.card Q - R.card := by
    intro k
    dsimp [B]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hRk_card k]
  have hdisj : ∀ k : Fin m, x k ∉ B k ∧ y k ∉ B k := by
    intro k
    have hx_in : x k ∈ Rk k := by rw [DFA.mem_image]; exact ⟨x₀, hx₀, rfl⟩
    have hy_in : y k ∈ Rk k := by rw [DFA.mem_image]; exact ⟨y₀, hy₀, rfl⟩
    exact ⟨fun h => (Finset.mem_sdiff.mp h).2 hx_in, fun h => (Finset.mem_sdiff.mp h).2 hy_in⟩
  have hxy_ne : ∀ k : Fin m, x k ≠ y k := by
    intro k heq
    have hlt : (Rk k).card < R.card := by
      have himg_eq : Rk k = A.image (R.erase x₀) (w.take k.val) := by
        ext q
        simp only [Rk, DFA.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨p, hp, rfl⟩
          by_cases hpx : p = x₀
          · subst hpx; exact ⟨y₀, ⟨hx₀y₀.symm, hy₀⟩, heq.symm⟩
          · exact ⟨p, ⟨hpx, hp⟩, rfl⟩
        · rintro ⟨p, ⟨_, hp⟩, rfl⟩
          exact ⟨p, hp, rfl⟩
      rw [himg_eq]
      exact lt_of_le_of_lt (A.card_image_le _ _) (Finset.card_erase_lt_of_mem hx₀)
    have := hRk_card k
    omega
  have hinter : ∀ i j : Fin m, j < i → x i ∈ B j ∨ y i ∈ B j := by
    intro i j hji
    by_contra hnot
    push Not at hnot
    have hxi_in : x i ∈ Rk j := by
      by_contra hnotR
      exact hnot.1 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotR⟩)
    have hyi_in : y i ∈ Rk j := by
      by_contra hnotR
      exact hnot.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotR⟩)
    have hmerge_drop : A.eval (x i) (w.drop i.val) = A.eval (y i) (w.drop i.val) := by
      dsimp [x, y]
      rw [← DFA.eval_append, ← DFA.eval_append, List.take_append_drop]
      exact hmerge
    let w' := w.take j.val ++ w.drop i.val
    have hcomp' : (A.image R w').card < R.card := by
      dsimp [w']
      rw [DFA.image_append]
      change (A.image (Rk j) (w.drop i.val)).card < R.card
      rw [← hRk_card j]
      have himg_eq : A.image (Rk j) (w.drop i.val) = A.image ((Rk j).erase (x i)) (w.drop i.val) := by
        ext q
        simp only [DFA.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨p, hp, rfl⟩
          by_cases hpx : p = x i
          · subst hpx; exact ⟨y i, ⟨(hxy_ne i).symm, hyi_in⟩, hmerge_drop.symm⟩
          · exact ⟨p, ⟨hpx, hp⟩, rfl⟩
        · rintro ⟨p, ⟨_, hp⟩, rfl⟩
          exact ⟨p, hp, rfl⟩
      rw [himg_eq]
      exact lt_of_le_of_lt (A.card_image_le _ _) (Finset.card_erase_lt_of_mem hxi_in)
    have hb := hmin w' hcomp'
    simp only [w', List.length_append, List.length_take, List.length_drop] at hb
    have hji' : j.val < i.val := hji
    omega
  exact frankl_skew_two m (Fintype.card Q - R.card) x y B hB_card hdisj hinter

private theorem six_mul_sum_choose_two (k : ℕ) :
    6 * (∑ r ∈ Finset.range k, (r + 2).choose 2) = k * (k + 1) * (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hch : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [Nat.choose_two_right]
      have heven : 2 ∣ (k + 2) * (k + 1) := by
        have := Nat.even_mul_succ_self (k + 1)
        rcases this.two_dvd with ⟨t, ht⟩
        exact ⟨t, by linarith⟩
      rcases heven with ⟨t, ht⟩
      have hsub : k + 2 - 1 = k + 1 := by omega
      rw [hsub, ht]
      omega
    linarith

private theorem pin_frankl_induction {Q α : Type*} [Fintype Q] [DecidableEq Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∀ r : ℕ, 1 ≤ r → r ≤ Fintype.card Q →
      ∀ R : Finset Q, R.card = r →
        ∃ w : List α, (A.image R w).card = 1 ∧
          w.length ≤ ∑ j ∈ Finset.range (r - 1), (Fintype.card Q - (j + 2) + 2).choose 2 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr1 hrn R hR
    by_cases h1 : r = 1
    · subst h1
      exact ⟨[], by simpa using hR, by simp⟩
    · have hr2 : 2 ≤ R.card := by omega
      obtain ⟨v, hvlen, hvcomp⟩ := pin_compression_bound A hSync R hr2
      let R' := A.image R v
      have hR'_lt : R'.card < R.card := hvcomp
      have hR'_ne : R'.Nonempty := by
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
        exact ⟨A.eval x v, by rw [DFA.mem_image]; exact ⟨x, hx, rfl⟩⟩
      have hR'_pos : 1 ≤ R'.card := Finset.card_pos.mpr hR'_ne
      obtain ⟨u, hu1, hulen⟩ := ih R'.card (by omega) hR'_pos (by omega) R' rfl
      refine ⟨v ++ u, ?_, ?_⟩
      · rw [DFA.image_append]; exact hu1
      · rw [List.length_append]
        have hsum_le :
            (∑ j ∈ Finset.range (R'.card - 1), (Fintype.card Q - (j + 2) + 2).choose 2) ≤
            (∑ j ∈ Finset.range (r - 2), (Fintype.card Q - (j + 2) + 2).choose 2) :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
        have hsplit :
            (∑ j ∈ Finset.range (r - 1), (Fintype.card Q - (j + 2) + 2).choose 2) =
            (∑ j ∈ Finset.range (r - 2), (Fintype.card Q - (j + 2) + 2).choose 2) +
            (Fintype.card Q - r + 2).choose 2 := by
          have hr_eq : r - 1 = (r - 2) + 1 := by omega
          have harg : (r - 2) + 2 = r := by omega
          rw [hr_eq, Finset.sum_range_succ, harg]
        rw [hR] at hvlen
        omega

/-- Pin–Frankl Cubic Upper Bound (1982/1983, division-free):
every synchronizing `n`-state DFA (`n ≥ 1`) admits a synchronizing word of length `L`
with `6 * L ≤ n ^ 3 - n`. -/
theorem pin_frankl_bound {Q α : Type*} [Fintype Q] [Nonempty Q]
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ 6 * w.length ≤ (Fintype.card Q) ^ 3 - Fintype.card Q := by
  classical
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos
  obtain ⟨w, hw1, hwlen⟩ := pin_frankl_induction A hSync (Fintype.card Q) hpos le_rfl
    Finset.univ Finset.card_univ
  refine ⟨w, (A.isSyncWord_iff_card_image_univ_eq_one w).mpr hw1, ?_⟩
  let n := Fintype.card Q
  have hreindex :
      (∑ j ∈ Finset.range (n - 1), (n - (j + 2) + 2).choose 2) =
      ∑ r ∈ Finset.range (n - 1), (r + 2).choose 2 := by
    refine Finset.sum_bij (fun j _ => n - 2 - j) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega
    · intro j₁ hj₁ j₂ hj₂ h
      rw [Finset.mem_range] at hj₁ hj₂
      omega
    · intro r hr
      rw [Finset.mem_range] at hr
      refine ⟨n - 2 - r, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      rw [Finset.mem_range] at hj
      congr 1
      omega
  have hsum := six_mul_sum_choose_two (n - 1)
  have hn1 : 1 ≤ n := hpos
  have hn3 : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
  have hmul : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) = n ^ 3 - n := by
    zify [hn1, hn3]
    ring
  change w.length ≤ ∑ j ∈ Finset.range (n - 1), (n - (j + 2) + 2).choose 2 at hwlen
  rw [hreindex] at hwlen
  have h6 : 6 * w.length ≤ 6 * ∑ r ∈ Finset.range (n - 1), (r + 2).choose 2 :=
    Nat.mul_le_mul_left 6 hwlen
  rw [hsum, hmul] at h6
  exact h6

end PinFrankl

/- ## Szykuła’s avoiding-subset lemma -/

section Avoiding

variable {Q : Type u} {α : Type v}

/-- Identifying two distinct members of the image domain strictly reduces its cardinality. -/
private theorem card_image_lt_of_merge [DecidableEq Q] (A : DFA Q α) {S : Finset Q} (w : List α)
    {x y : Q} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hmerge : A.eval x w = A.eval y w) :
    (A.image S w).card < S.card := by
  refine lt_of_le_of_ne (A.card_image_le S w) fun heq => hxy ?_
  exact Finset.injOn_of_card_image_eq heq hx hy hmerge

private def avoidPush [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α) :
    (Q → ℚ) →ₗ[ℚ] (Q → ℚ) where
  toFun x q := ∑ p : Q, if A.eval p w = q then x p else 0
  map_add' x y := by
    ext q
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  map_smul' c x := by
    ext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp

private theorem avoidPush_nil [Fintype Q] [DecidableEq Q] (A : DFA Q α) (x : Q → ℚ) :
    avoidPush A [] x = x := by
  ext q
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk, DFA.eval_nil]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp; simp [hp]
  · intro h; exact absurd (Finset.mem_univ q) h

private theorem avoidPush_append [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w₁ w₂ : List α)
    (x : Q → ℚ) :
    avoidPush A (w₁ ++ w₂) x = avoidPush A w₂ (avoidPush A w₁ x) := by
  ext q
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ p : Q, if A.eval p (w₁ ++ w₂) = q then x p else 0)
        = ∑ p : Q, ∑ r : Q, if A.eval p w₁ = r then (if A.eval r w₂ = q then x p else 0) else 0 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp [Finset.sum_ite_eq, DFA.eval_append]
    _ = ∑ r : Q, ∑ p : Q, if A.eval p w₁ = r then (if A.eval r w₂ = q then x p else 0) else 0 :=
          Finset.sum_comm
    _ = ∑ r : Q, if A.eval r w₂ = q then (∑ p : Q, if A.eval p w₁ = r then x p else 0) else 0 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          by_cases hr : A.eval r w₂ = q
          · simp [hr]
          · simp [hr]

private theorem avoidPush_sum_all [Fintype Q] [DecidableEq Q] (A : DFA Q α) (w : List α)
    (x : Q → ℚ) :
    (∑ q : Q, avoidPush A w x q) = ∑ p : Q, x p := by
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Finset.sum_ite_eq]

private def avoidInd [DecidableEq Q] (S : Finset Q) : Q → ℚ :=
  fun q => if q ∈ S then 1 else 0

private theorem avoidPush_ind_apply [Fintype Q] [DecidableEq Q] (A : DFA Q α) (S : Finset Q)
    (w : List α) (t : Q) :
    avoidPush A w (avoidInd S) t = ((S.filter (fun p => A.eval p w = t)).card : ℚ) := by
  simp only [avoidPush, LinearMap.coe_mk, AddHom.coe_mk, avoidInd]
  trans (∑ p : Q, if p ∈ S ∧ A.eval p w = t then (1 : ℚ) else 0)
  · refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h1 : A.eval p w = t <;> by_cases h2 : p ∈ S <;> simp [h1, h2]
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    apply congrArg Nat.cast
    apply congrArg Finset.card
    ext p
    simp

/-- **Szykuła's Avoiding-Subset Lemma (2018, Lemma 2)**:
If `∅ ⊂ T ⊆ S` with `T ≠ univ`, and some word `u` avoids `T` from `S` (`¬ T ⊆ S · u`),
then there exists a word `w` of length `≤ |Q| - |T|` that either avoids `T` from `S`
or strictly compresses `S` (`|S · w| < |S|`). -/
theorem szykula_avoiding_lemma [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (S T : Finset Q) (hTne : T.Nonempty) (hTS : T ⊆ S) (hTun : T ≠ Finset.univ)
    (hAvoid : ∃ u : List α, ¬ (T ⊆ A.image S u)) :
    ∃ w : List α, w.length ≤ Fintype.card Q - T.card ∧
      (¬ (T ⊆ A.image S w) ∨ (A.image S w).card < S.card) := by
  classical
  have hSpos : 1 ≤ S.card := le_trans (Finset.card_pos.mpr hTne) (Finset.card_le_card hTS)
  have hS_ne0 : (S.card : ℚ) ≠ 0 := by exact_mod_cast (show S.card ≠ 0 by omega)
  have hT_lt : T.card < Fintype.card Q := by
    have hssub : T ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hTun⟩
    simpa [Finset.card_univ] using Finset.card_lt_card hssub
  obtain ⟨q₀, _, hq₀_notT⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T, hTun⟩)
  -- Linear map Φ : (Q → ℚ) →ₗ[ℚ] ({t // t ∈ T} → ℚ), (Φ x) t = |S| * x t - ∑ p, x p
  let Φ : (Q → ℚ) →ₗ[ℚ] ({t // t ∈ T} → ℚ) :=
    { toFun := fun x t => (S.card : ℚ) * x t.1 - ∑ p : Q, x p
      map_add' := fun x₁ x₂ => by
        ext t
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        ext t
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        ring }
  -- Surjectivity of Φ via basis vectors (1/|S|)(e_t - e_{q₀})
  have hΦ_surj : Function.Surjective Φ := by
    intro b
    have hbasis : ∀ t : {t // t ∈ T}, ∃ v : Q → ℚ, Φ v = Pi.single t 1 := by
      intro t
      let v : Q → ℚ := fun q =>
        (1 / (S.card : ℚ)) * ((if q = t.1 then (1 : ℚ) else 0) - (if q = q₀ then (1 : ℚ) else 0))
      refine ⟨v, ?_⟩
      ext t'
      have hsum_v : (∑ p : Q, v p) = 0 := by
        simp only [v, ← Finset.mul_sum, Finset.sum_sub_distrib]
        simp
      have ht'_ne_q₀ : t'.1 ≠ q₀ := fun h => hq₀_notT (h ▸ t'.2)
      change (S.card : ℚ) * v t'.1 - ∑ p : Q, v p = (Pi.single t (1 : ℚ) : {t // t ∈ T} → ℚ) t'
      rw [hsum_v, sub_zero]
      dsimp only [v]
      simp only [ht'_ne_q₀, ↓reduceIte, sub_zero]
      by_cases htt : t' = t
      · subst htt
        simp [hS_ne0]
      · have hval_ne : t'.1 ≠ t.1 := fun h => htt (Subtype.ext h)
        simp [hval_ne, htt]
    choose basis hbasis using hbasis
    refine ⟨∑ t : {t // t ∈ T}, b t • basis t, ?_⟩
    rw [map_sum]
    ext t'
    simp only [map_smul, hbasis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single t']
    · simp
    · intro t _ htt
      simp [Pi.single_eq_of_ne (Ne.symm htt)]
    · intro h; exact absurd (Finset.mem_univ t') h
  let H : Submodule ℚ (Q → ℚ) := LinearMap.ker Φ
  have hdimH : Module.finrank ℚ H = Fintype.card Q - T.card := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    have hrange : LinearMap.range Φ = ⊤ := LinearMap.range_eq_top.mpr hΦ_surj
    rw [hrange, finrank_top, Module.finrank_pi, Module.finrank_pi, Fintype.card_coe] at hrn
    change T.card + Module.finrank ℚ H = Fintype.card Q at hrn
    omega
  -- Escaping H certifies either avoiding T or compressing S
  have hnotH_cert : ∀ w : List α, avoidPush A w (avoidInd S) ∉ H →
      ¬ (T ⊆ A.image S w) ∨ (A.image S w).card < S.card := by
    intro w hnotH
    have hne0 : Φ (avoidPush A w (avoidInd S)) ≠ 0 := by
      simpa [H, LinearMap.mem_ker] using hnotH
    have hex_t : ∃ t : {t // t ∈ T}, Φ (avoidPush A w (avoidInd S)) t ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne0 (funext hall)
    obtain ⟨⟨t, ht⟩, ht_ne0⟩ := hex_t
    have hval : Φ (avoidPush A w (avoidInd S)) ⟨t, ht⟩ =
        (S.card : ℚ) * ((S.filter (fun p => A.eval p w = t)).card : ℚ) - (S.card : ℚ) := by
      change (S.card : ℚ) * avoidPush A w (avoidInd S) t - ∑ p : Q, avoidPush A w (avoidInd S) p = _
      rw [avoidPush_ind_apply, avoidPush_sum_all]
      simp [avoidInd]
    rw [hval] at ht_ne0
    let m_t := (S.filter (fun p => A.eval p w = t)).card
    have hmt_ne1 : m_t ≠ 1 := by
      intro h1
      apply ht_ne0
      change (S.card : ℚ) * (m_t : ℚ) - (S.card : ℚ) = 0
      rw [h1]
      ring
    by_cases hmt0 : m_t = 0
    · left
      intro hsub
      have ht_mem : t ∈ A.image S w := hsub ht
      rw [DFA.mem_image] at ht_mem
      rcases ht_mem with ⟨p, hpS, hp_ev⟩
      have hpos : 0 < m_t := Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpS, hp_ev⟩⟩
      omega
    · right
      have h1lt : 1 < (S.filter (fun p => A.eval p w = t)).card := by omega
      obtain ⟨p₁, hp₁, p₂, hp₂, hp12⟩ := Finset.one_lt_card.mp h1lt
      rw [Finset.mem_filter] at hp₁ hp₂
      exact card_image_lt_of_merge A w hp₁.1 hp₂.1 hp12 (hp₁.2.trans hp₂.2.symm)
  -- Check w = []
  by_cases h0 : avoidInd S ∉ H
  · exact ⟨[], by simp, hnotH_cert [] (by rw [avoidPush_nil]; exact h0)⟩
  push Not at h0
  -- Witness u escapes H
  obtain ⟨u, hu_not⟩ := hAvoid
  have hu_notH : avoidPush A u (avoidInd S) ∉ H := by
    intro huH
    have h0' : Φ (avoidPush A u (avoidInd S)) = 0 := LinearMap.mem_ker.mp huH
    have hex_t : ∃ t ∈ T, t ∉ A.image S u := by
      by_contra hall
      push Not at hall
      exact hu_not hall
    obtain ⟨t, htT, htNot⟩ := hex_t
    have hht := congrFun h0' ⟨t, htT⟩
    change (S.card : ℚ) * avoidPush A u (avoidInd S) t - ∑ p : Q, avoidPush A u (avoidInd S) p = 0 at hht
    rw [avoidPush_ind_apply, avoidPush_sum_all] at hht
    have hemp : S.filter (fun p => A.eval p u = t) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hpS hpev
      exact htNot (by rw [DFA.mem_image]; exact ⟨p, hpS, hpev⟩)
    rw [hemp, Finset.card_empty] at hht
    simp only [avoidInd, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_zero, mul_zero, zero_sub,
      neg_eq_zero] at hht
    exact hS_ne0 hht
  -- Ascending chain V d = span {avoidPush A w (avoidInd S) | w.length ≤ d}
  let V : ℕ → Submodule ℚ (Q → ℚ) := fun d =>
    Submodule.span ℚ { v : Q → ℚ | ∃ w : List α, w.length ≤ d ∧ v = avoidPush A w (avoidInd S) }
  have hV_mono : ∀ {i j}, i ≤ j → V i ≤ V j := by
    intro i j hij
    apply Submodule.span_mono
    rintro v ⟨w, hwlen, rfl⟩
    exact ⟨w, le_trans hwlen hij, rfl⟩
  have hex_esc : ∃ d : ℕ, ¬ (V d ≤ H) :=
    ⟨u.length, fun hle => hu_notH (hle (Submodule.subset_span ⟨u, le_rfl, rfl⟩))⟩
  let d₀ := Nat.find hex_esc
  have hd₀_not : ¬ (V d₀ ≤ H) := Nat.find_spec hex_esc
  have hd₀_min : ∀ j < d₀, V j ≤ H := fun j hj => by
    by_contra hnot
    exact Nat.find_min hex_esc hj hnot
  have hd₀_pos : 1 ≤ d₀ := by
    by_contra h0'
    have hzd : d₀ = 0 := by omega
    rw [hzd] at hd₀_not
    apply hd₀_not
    rw [Submodule.span_le]
    rintro v ⟨w, hwlen, rfl⟩
    have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil, avoidPush_nil]
    exact h0
  have hV_strict : ∀ j < d₀, V j < V (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hV_mono (by omega)) fun heq => ?_
    have hclosed : ∀ a : α, ∀ v ∈ V j, avoidPush A [a] v ∈ V j := by
      intro a v hv
      have hmap : Submodule.map (avoidPush A [a]) (V j) ≤ V (j + 1) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨w, hwlen, rfl⟩
        rw [← avoidPush_append]
        exact Submodule.subset_span ⟨w ++ [a], by simp; omega, rfl⟩
      rw [← heq] at hmap
      exact hmap ⟨v, hv, rfl⟩
    have hall_words : ∀ w : List α, avoidPush A w (avoidInd S) ∈ V j := by
      intro w
      induction w using List.reverseRecOn with
      | nil =>
        rw [avoidPush_nil]
        exact Submodule.subset_span ⟨[], by simp, (avoidPush_nil A _).symm⟩
      | append_singleton w a ih =>
        rw [avoidPush_append]
        exact hclosed a _ ih
    exact hu_notH (hd₀_min j hj (hall_words u))
  have hdim_V0 : 1 ≤ Module.finrank ℚ (V 0) := by
    have hmem0 : avoidInd S ∈ V 0 := Submodule.subset_span ⟨[], le_rfl, (avoidPush_nil A _).symm⟩
    have hne0 : avoidInd S ≠ 0 := by
      obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      intro hzero
      have := congrFun hzero s
      simp [avoidInd, hs] at this
    have hbot : (⊥ : Submodule ℚ (Q → ℚ)) < V 0 := by
      rw [bot_lt_iff_ne_bot]
      intro hbot'
      rw [hbot', Submodule.mem_bot] at hmem0
      exact hne0 hmem0
    have hlt := Submodule.finrank_lt_finrank_of_lt hbot
    rw [finrank_bot] at hlt
    omega
  have hdim_Vj : ∀ j < d₀, 1 + j ≤ Module.finrank ℚ (V j) := by
    intro j
    induction j with
    | zero => intro _; simpa using hdim_V0
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hlt := Submodule.finrank_lt_finrank_of_lt (hV_strict j (by omega))
      omega
  have hd₀_le : d₀ ≤ Fintype.card Q - T.card := by
    have h1 := hdim_Vj (d₀ - 1) (by omega)
    have h2 : Module.finrank ℚ (V (d₀ - 1)) ≤ Module.finrank ℚ H :=
      Submodule.finrank_mono (hd₀_min (d₀ - 1) (by omega))
    omega
  have hex_gen : ∃ v ∈ { v : Q → ℚ | ∃ w : List α, w.length ≤ d₀ ∧ v = avoidPush A w (avoidInd S) },
      v ∉ H := by
    by_contra hall
    push Not at hall
    exact hd₀_not (Submodule.span_le.mpr hall)
  rcases hex_gen with ⟨_, ⟨w, hwlen, rfl⟩, hw_notH⟩
  exact ⟨w, le_trans hwlen hd₀_le, hnotH_cert w hw_notH⟩

end Avoiding

/- ## Part 1: Corank-Gap Framework -/

section CorankFramework

variable {Q : Type u} {α : Type v}

theorem exists_corank_word [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (i : ℕ) (hi : i ≤ Fintype.card Q - 1) :
    ∃ m : ℕ, ∃ w : List α, w.length = m ∧ (A.image Finset.univ w).card ≤ Fintype.card Q - i := by
  rcases hSync with ⟨w, hw⟩
  have h1 : (A.image Finset.univ w).card = 1 :=
    (A.isSyncWord_iff_card_image_univ_eq_one w).mp hw
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr hw.nonempty
  exact ⟨w.length, w, rfl, by omega⟩

/-- Minimum length `λ_i` of a word achieving corank at least `i` (rank `≤ n - i`). -/
noncomputable def minCorankLen [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (i : ℕ) : ℕ := by
  classical
  exact if hi : i ≤ Fintype.card Q - 1 then Nat.find (exists_corank_word A hSync i hi) else 0

/-- Corank gap `δ_j = λ_{j+1} - λ_j`. -/
noncomputable def corankGap [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) (j : ℕ) : ℕ :=
  minCorankLen A hSync (j + 1) - minCorankLen A hSync j

theorem minCorankLen_spec [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {i : ℕ} (hi : i ≤ Fintype.card Q - 1) :
    ∃ w : List α, w.length = minCorankLen A hSync i ∧
      (A.image Finset.univ w).card ≤ Fintype.card Q - i := by
  classical
  unfold minCorankLen
  simp only [hi, ↓reduceDIte]
  exact Nat.find_spec (exists_corank_word A hSync i hi)

theorem minCorankLen_le [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {i : ℕ} (hi : i ≤ Fintype.card Q - 1)
    {w : List α} (hw : (A.image Finset.univ w).card ≤ Fintype.card Q - i) :
    minCorankLen A hSync i ≤ w.length := by
  classical
  unfold minCorankLen
  simp only [hi, ↓reduceDIte]
  exact Nat.find_min' (exists_corank_word A hSync i hi) ⟨w, rfl, hw⟩

theorem minCorankLen_zero [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    minCorankLen A hSync 0 = 0 := by
  have hle : minCorankLen A hSync 0 ≤ ([] : List α).length :=
    minCorankLen_le A hSync (Nat.zero_le _) (by simp)
  simpa using hle

theorem minCorankLen_mono [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ Fintype.card Q - 1) :
    minCorankLen A hSync i ≤ minCorankLen A hSync j := by
  obtain ⟨w, hwlen, hwcard⟩ := minCorankLen_spec A hSync hj
  rw [← hwlen]
  exact minCorankLen_le A hSync (le_trans hij hj) (by omega)

theorem exists_syncWord_len_minCorankLen [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧ w.length = minCorankLen A hSync (Fintype.card Q - 1) := by
  obtain ⟨q⟩ := hSync.nonempty
  have hpos : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q⟩
  obtain ⟨w, hwlen, hwcard⟩ := minCorankLen_spec A hSync le_rfl
  have hge1 : 1 ≤ (A.image Finset.univ w).card :=
    Finset.card_pos.mpr ⟨A.eval q w, by rw [DFA.mem_image]; exact ⟨q, Finset.mem_univ q, rfl⟩⟩
  have heq1 : (A.image Finset.univ w).card = 1 := by omega
  exact ⟨w, (A.isSyncWord_iff_card_image_univ_eq_one w).mpr heq1, hwlen⟩

theorem minCorankLen_eq_add_sum_Ico [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Fintype.card Q - 1) :
    minCorankLen A hSync b =
      minCorankLen A hSync a + ∑ j ∈ Finset.Ico a b, corankGap A hSync j := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq; simp
    · have hab' : a ≤ b := by omega
      have hsplit : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hb_not : b ∉ Finset.Ico a b := by simp
      rw [hsplit, Finset.sum_insert hb_not, add_comm (corankGap A hSync b),
        ← add_assoc, ← ih hab' (by omega)]
      have hmono := minCorankLen_mono A hSync (Nat.le_add_right b 1) hb
      dsimp only [corankGap]
      omega

theorem minCorankLen_eq_sum_range [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {b : ℕ} (hb : b ≤ Fintype.card Q - 1) :
    minCorankLen A hSync b = ∑ j ∈ Finset.range b, corankGap A hSync j := by
  have h := minCorankLen_eq_add_sum_Ico A hSync (Nat.zero_le b) hb
  rw [minCorankLen_zero, zero_add, Nat.Ico_zero_eq_range] at h
  exact h

/-- Pin–Frankl upper bound on every individual corank gap: `δ_j ≤ (j + 2).choose 2`. -/
theorem corankGap_le_pinFrankl [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {j : ℕ} (hj : j + 1 ≤ Fintype.card Q - 1) :
    corankGap A hSync j ≤ (j + 2).choose 2 := by
  obtain ⟨u, hulen, hucard⟩ := minCorankLen_spec A hSync (by omega : j ≤ Fintype.card Q - 1)
  by_cases hskip : (A.image Finset.univ u).card ≤ Fintype.card Q - (j + 1)
  · have hle := minCorankLen_le A hSync hj hskip
    dsimp only [corankGap]
    omega
  · have heq : (A.image Finset.univ u).card = Fintype.card Q - j := by omega
    have hge2 : 2 ≤ (A.image Finset.univ u).card := by omega
    obtain ⟨w, hwlen, hwcomp⟩ := pin_compression_bound A hSync (A.image Finset.univ u) hge2
    have hcard' : (A.image Finset.univ (u ++ w)).card ≤ Fintype.card Q - (j + 1) := by
      rw [DFA.image_append]
      omega
    have hle := minCorankLen_le A hSync hj hcard'
    rw [List.length_append, hulen] at hle
    rw [heq] at hwlen
    have hsub : Fintype.card Q - (Fintype.card Q - j) + 2 = j + 2 := by omega
    rw [hsub] at hwlen
    dsimp only [corankGap]
    omega

end CorankFramework

/- ## Part 2: Shitov's Corank-Gap Upgrade Theorem (2019, Theorem 2) -/

section ShitovTheorem

variable {Q : Type u} {α : Type v}

/-- **Shitov's Corank-Gap Upgrade Theorem (2019, Theorem 2)**:
If `1 ≤ r`, `2 * r + 2 ≤ n`, `τ + 1 ≤ n - 1`, and `2 * r < δ_τ`, then
`δ_r ≤ λ_τ + 2 * r`. Proved via singleton-preimage counting and `szykula_avoiding_lemma`. -/
theorem shitov_corank_gap [Fintype Q] [DecidableEq Q] (A : DFA Q α)
    (hSync : A.IsSynchronizing) {r τ : ℕ}
    (hr1 : 1 ≤ r) (hr2 : 2 * r + 2 ≤ Fintype.card Q)
    (hτ : τ + 1 ≤ Fintype.card Q - 1) (hgap : 2 * r < corankGap A hSync τ) :
    corankGap A hSync r ≤ minCorankLen A hSync τ + 2 * r := by
  classical
  let n := Fintype.card Q
  have hr_le : r + 1 ≤ n - 1 := by omega
  obtain ⟨u, hulen, hucard⟩ := minCorankLen_spec A hSync (by omega : r ≤ n - 1)
  by_cases hskip : (A.image Finset.univ u).card ≤ n - (r + 1)
  · have hle := minCorankLen_le A hSync hr_le hskip
    dsimp only [corankGap]
    omega
  have hImg_card : (A.image Finset.univ u).card = n - r := by omega
  let Img := A.image Finset.univ u
  obtain ⟨v, hvlen, hvcard⟩ := minCorankLen_spec A hSync (by omega : τ ≤ n - 1)
  let S := A.image Finset.univ v
  have hS_le : S.card ≤ n - τ := hvcard
  have hS_card : S.card = n - τ := by
    by_contra hne
    have hlt : S.card ≤ n - (τ + 1) := by omega
    have hle := minCorankLen_le A hSync hτ hlt
    dsimp only [corankGap] at hgap
    omega
  have hS_no_comp : ∀ w : List α, w.length ≤ 2 * r → S.card ≤ (A.image S w).card := by
    intro w hwlen
    by_contra hlt
    have hle_next : (A.image Finset.univ (v ++ w)).card ≤ n - (τ + 1) := by
      rw [DFA.image_append]
      change (A.image S w).card ≤ n - (τ + 1)
      omega
    have hmin := minCorankLen_le A hSync hτ hle_next
    rw [List.length_append, hvlen] at hmin
    have hmono := minCorankLen_mono A hSync (Nat.le_succ τ) hτ
    dsimp only [corankGap] at hgap
    omega
  let Sing : Finset Q := Img.filter (fun y => (A.preimage {y} u).card = 1)
  let Aset : Finset Q := A.preimage Sing u
  have hAset_eq_Sing : Aset.card = Sing.card := by
    dsimp only [Aset]
    rw [A.card_preimage_eq_sum_singleton]
    have hsum : ∑ y ∈ Sing, (A.preimage {y} u).card = ∑ _y ∈ Sing, 1 := by
      refine Finset.sum_congr rfl fun y hy => (Finset.mem_filter.mp hy).2
    rw [hsum]
    simp
  have hAset_ge : n - 2 * r ≤ Aset.card := by
    have hpre_univ : A.preimage Img u = Finset.univ := by
      ext q
      simp only [DFA.mem_preimage, Finset.mem_univ, iff_true]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
    have htotal : n = ∑ y ∈ Img, (A.preimage {y} u).card := by
      calc n = (Finset.univ : Finset Q).card := Finset.card_univ.symm
        _ = (A.preimage Img u).card := by rw [hpre_univ]
        _ = ∑ y ∈ Img, (A.preimage {y} u).card := A.card_preimage_eq_sum_singleton Img u
    have hSing_sub : Sing ⊆ Img := Finset.filter_subset _ _
    have hsplit : (∑ y ∈ Img, (A.preimage {y} u).card) =
        (∑ y ∈ Sing, (A.preimage {y} u).card) +
        (∑ y ∈ Img \ Sing, (A.preimage {y} u).card) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hSing_sub]
    have hpart1 : (∑ y ∈ Sing, (A.preimage {y} u).card) = Sing.card := by
      rw [← A.card_preimage_eq_sum_singleton]
      exact hAset_eq_Sing
    have hpart2 : 2 * (Img \ Sing).card ≤ ∑ y ∈ Img \ Sing, (A.preimage {y} u).card := by
      calc 2 * (Img \ Sing).card
          = ∑ _y ∈ Img \ Sing, 2 := by simp [mul_comm]
        _ ≤ ∑ y ∈ Img \ Sing, (A.preimage {y} u).card := by
            refine Finset.sum_le_sum fun y hy => ?_
            rw [Finset.mem_sdiff] at hy
            have hy_img : y ∈ Img := hy.1
            have hy_not : y ∉ Sing := hy.2
            have hge1 : 1 ≤ (A.preimage {y} u).card := by
              rw [DFA.mem_image] at hy_img
              rcases hy_img with ⟨q, _, hqu⟩
              exact Finset.card_pos.mpr ⟨q, by simp [DFA.mem_preimage, hqu]⟩
            have hne1 : (A.preimage {y} u).card ≠ 1 := fun h1 =>
              hy_not (Finset.mem_filter.mpr ⟨hy_img, h1⟩)
            omega
    have hsdiff_card : (Img \ Sing).card = Img.card - Sing.card :=
      Finset.card_sdiff_of_subset hSing_sub
    have hSing_le_Img : Sing.card ≤ Img.card := Finset.card_le_card hSing_sub
    change Img.card = n - r at hImg_card
    omega
  have hAset_ge2 : 2 ≤ Aset.card := by omega
  have hAset_ne : Aset.Nonempty := Finset.card_pos.mp (by omega)
  have hAset_ne_univ : Aset ≠ Finset.univ := by
    intro huniv
    have hSing_le : Sing.card ≤ Img.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hcard_eq : Aset.card = n := by rw [huniv, Finset.card_univ]
    change Img.card = n - r at hImg_card
    omega
  have hex_avoid_w : ∃ w : List α, w.length ≤ 2 * r ∧ ¬ (Aset ⊆ A.image S w) := by
    by_cases hsub : Aset ⊆ S
    · have hAvoid_sync : ∃ w₀ : List α, ¬ (Aset ⊆ A.image S w₀) := by
        rcases hSync with ⟨w₀, hw₀⟩
        refine ⟨w₀, fun hAsub => ?_⟩
        have hle1 : (A.image S w₀).card ≤ 1 := by
          calc (A.image S w₀).card
              ≤ (A.image Finset.univ w₀).card :=
                Finset.card_le_card (A.image_mono (Finset.subset_univ S) w₀)
            _ = 1 := (A.isSyncWord_iff_card_image_univ_eq_one w₀).mp hw₀
        have hle := Finset.card_le_card hAsub
        omega
      obtain ⟨w, hwlen, hwres⟩ :=
        szykula_avoiding_lemma A S Aset hAset_ne hsub hAset_ne_univ hAvoid_sync
      have hwlen2r : w.length ≤ 2 * r := by omega
      rcases hwres with hnot_sub | hcomp
      · exact ⟨w, hwlen2r, hnot_sub⟩
      · exfalso
        have := hS_no_comp w hwlen2r
        omega
    · exact ⟨[], by simp, by simpa using hsub⟩
  obtain ⟨w, hwlen, hnot_sub⟩ := hex_avoid_w
  have hex_x : ∃ x ∈ Aset, x ∉ A.image S w := by
    by_contra hall
    push Not at hall
    exact hnot_sub hall
  obtain ⟨x, hxAset, hxNot⟩ := hex_x
  have hxu_Sing : A.eval x u ∈ Sing := (A.mem_preimage Sing u x).mp hxAset
  have hxu_Img : A.eval x u ∈ Img := (Finset.mem_filter.mp hxu_Sing).1
  have hxu_card1 : (A.preimage {A.eval x u} u).card = 1 := (Finset.mem_filter.mp hxu_Sing).2
  have hxu_not_img : A.eval x u ∉ A.image Finset.univ (v ++ w ++ u) := by
    intro hmem
    rw [DFA.mem_image] at hmem
    rcases hmem with ⟨p, _, hpev⟩
    rw [DFA.eval_append] at hpev
    have hpre1 : x ∈ A.preimage {A.eval x u} u := by simp [DFA.mem_preimage]
    have hpre2 : A.eval p (v ++ w) ∈ A.preimage {A.eval x u} u := by
      rw [DFA.mem_preimage, Finset.mem_singleton]
      exact hpev
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hxu_card1
    rw [hz, Finset.mem_singleton] at hpre1 hpre2
    have hxeq : A.eval p (v ++ w) = x := hpre2.trans hpre1.symm
    apply hxNot
    rw [← DFA.image_append]
    exact (A.mem_image Finset.univ (v ++ w) x).mpr ⟨p, Finset.mem_univ p, hxeq⟩
  have hsub_erase : A.image Finset.univ (v ++ w ++ u) ⊆ Img.erase (A.eval x u) := by
    intro y hy
    rw [Finset.mem_erase]
    refine ⟨fun h => hxu_not_img (h ▸ hy), ?_⟩
    rw [DFA.image_append] at hy
    exact A.image_mono (Finset.subset_univ _) u hy
  have hcard_new : (A.image Finset.univ (v ++ w ++ u)).card ≤ n - (r + 1) := by
    have hle := Finset.card_le_card hsub_erase
    rw [Finset.card_erase_of_mem hxu_Img] at hle
    change Img.card = n - r at hImg_card
    omega
  have hle_next := minCorankLen_le A hSync hr_le hcard_new
  simp only [List.length_append, hvlen, hulen] at hle_next
  dsimp only [corankGap]
  omega

end ShitovTheorem

/- ## Part 3: Zero-Calculus Telescoping Rational Dual for Exact Shitov (2019) -/

section TelescopingDualHelpers

private theorem six_mul_sum_range_choose_two (m : ℕ) :
    6 * (∑ r ∈ Finset.range m, (r + 2).choose 2) = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hch : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
      rw [Nat.choose_two_right]
      have heven : 2 ∣ (m + 2) * (m + 1) := by
        rcases (Nat.even_mul_succ_self (m + 1)).two_dvd with ⟨t, ht⟩
        exact ⟨t, by linarith⟩
      rcases heven with ⟨t, ht⟩
      have hsub : m + 2 - 1 = m + 1 := by omega
      rw [hsub, ht]
      omega
    linarith

private theorem six_mul_sum_Ico_choose_two {a b : ℕ} (hab : a ≤ b) :
    6 * (∑ r ∈ Finset.Ico a b, (r + 2).choose 2) =
      b * (b + 1) * (b + 2) - a * (a + 1) * (a + 2) := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun r => (r + 2).choose 2) hab
  have ha := six_mul_sum_range_choose_two a
  have hb := six_mul_sum_range_choose_two b
  omega

/-- Pure rational telescoping identity:
`∑_{r=a}^b 1 / (r * (r + 1)) = 1 / a - 1 / (b + 1)` for `1 ≤ a ≤ b`. -/
private theorem sum_Icc_inv_mul_succ {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ r ∈ Finset.Icc a b, (1 : ℚ) / ((r : ℚ) * ((r : ℚ) + 1))) =
      1 / (a : ℚ) - 1 / ((b : ℚ) + 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq
      rw [Finset.Icc_self, Finset.sum_singleton]
      have hpos : (b : ℚ) + 1 ≠ 0 := by positivity
      have hpos2 : (b : ℚ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · have hab' : a ≤ b := by omega
      have hsplit : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : b + 1 ∉ Finset.Icc a b := by simp
      rw [hsplit, Finset.sum_insert hnot, ih hab']
      push_cast
      have h1 : (b : ℚ) + 1 ≠ 0 := by positivity
      have h2 : (b : ℚ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- Lower bound on `∑_{r=β}^γ r / (r + 1)` via `r / (r + 1) ≥ 1 - 1 / β`. -/
private theorem sum_Icc_div_succ_ge {β γ : ℕ} (hβ : 1 ≤ β) (hβγ : β ≤ γ) :
    ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) ≤
      ∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1) := by
  have hβ_pos : (0 : ℚ) < β := by exact_mod_cast (show 0 < β by omega)
  have hterm : ∀ r ∈ Finset.Icc β γ, 1 - 1 / (β : ℚ) ≤ (r : ℚ) / ((r : ℚ) + 1) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr_ge : (β : ℚ) ≤ r := by exact_mod_cast hr.1
    have hr1_pos : (0 : ℚ) < (r : ℚ) + 1 := by positivity
    rw [sub_le_iff_le_add]
    have hmul : (1 : ℚ) * ((β : ℚ) * ((r : ℚ) + 1)) ≤
        ((r : ℚ) / ((r : ℚ) + 1) + 1 / (β : ℚ)) * ((β : ℚ) * ((r : ℚ) + 1)) := by
      have hβ_ne : (β : ℚ) ≠ 0 := ne_of_gt hβ_pos
      have hr1_ne : (r : ℚ) + 1 ≠ 0 := ne_of_gt hr1_pos
      have hrhs : ((r : ℚ) / ((r : ℚ) + 1) + 1 / (β : ℚ)) * ((β : ℚ) * ((r : ℚ) + 1)) =
          (r : ℚ) * (β : ℚ) + ((r : ℚ) + 1) := by
        field_simp
      rw [hrhs]
      have hβ1 : (1 : ℚ) ≤ (β : ℚ) := by exact_mod_cast hβ
      nlinarith
    exact le_of_mul_le_mul_right hmul (mul_pos hβ_pos hr1_pos)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have hcard : ((γ : ℚ) - (β : ℚ)) ≤ ((γ + 1 - β : ℕ) : ℚ) := by
    have : γ - β ≤ γ + 1 - β := by omega
    have hcast : ((γ - β : ℕ) : ℚ) = (γ : ℚ) - (β : ℚ) := Nat.cast_sub hβγ
    rw [← hcast]
    exact_mod_cast this
  have hnonneg : (0 : ℚ) ≤ 1 - 1 / (β : ℚ) := by
    rw [sub_nonneg, div_le_one hβ_pos]
    exact_mod_cast hβ
  exact le_trans (mul_le_mul_of_nonneg_right hcard hnonneg) hsum

/-- Telescoping dual weight bound:
for `1 ≤ β ≤ γ < k`, `k ≤ 2 * γ`, `M = γ * (k - γ)`, and `1 ≤ i ≤ k`,
`i * ∑_{r ∈ Icc (max β i) k} α_r ≤ (γ + 1) * (k - γ)`. -/
private theorem shitov_dual_weight_le {β γ k i : ℕ}
    (hβ1 : 1 ≤ β) (hβγ : β ≤ γ) (hγk : γ < k) (h2γ : k ≤ 2 * γ)
    (hi1 : 1 ≤ i) (hik : i ≤ k) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    let α : ℕ → ℚ := fun r =>
      if r < β then 0
      else if r ≤ γ then M / ((r : ℚ) * ((r : ℚ) + 1))
      else 1
    (i : ℚ) * (∑ r ∈ Finset.Icc (max β i) k, α r) ≤
      ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
  intro M α
  by_cases hi_gt : γ < i
  · -- Case i > γ: max β i = i, every r ∈ Icc i k has r > γ so α r = 1
    have hmax : max β i = i := max_eq_right (by omega)
    rw [hmax]
    have hsum1 : (∑ r ∈ Finset.Icc i k, α r) = ((k + 1 - i : ℕ) : ℚ) := by
      have hcongr : (∑ r ∈ Finset.Icc i k, α r) = ∑ _r ∈ Finset.Icc i k, (1 : ℚ) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : ¬ r ≤ γ := by omega
        simp only [α, h1, h2, ↓reduceIte]
      rw [hcongr, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    rw [hsum1]
    have hcast : ((k + 1 - i : ℕ) : ℚ) = (k : ℚ) + 1 - (i : ℚ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    rw [hcast]
    have hi_ge : (γ : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast (show γ + 1 ≤ i by omega)
    have h2γ' : (k : ℚ) ≤ 2 * (γ : ℚ) := by exact_mod_cast h2γ
    nlinarith
  · -- Case i ≤ γ: split Icc (max β i) k = Icc (max β i) γ ∪ Icc (γ + 1) k
    let m := max β i
    have hm_ge1 : 1 ≤ m := by omega
    have hm_geβ : β ≤ m := le_max_left β i
    have hm_gei : i ≤ m := le_max_right β i
    have hm_leγ : m ≤ γ := by omega
    have hsplit : Finset.Icc m k = Finset.Icc m γ ∪ Finset.Icc (γ + 1) k := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc m γ) (Finset.Icc (γ + 1) k) := by
      rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have hpart1 : (∑ r ∈ Finset.Icc m γ, α r) =
        M * (1 / (m : ℚ) - 1 / ((γ : ℚ) + 1)) := by
      have hcongr : (∑ r ∈ Finset.Icc m γ, α r) =
          ∑ r ∈ Finset.Icc m γ, M * (1 / ((r : ℚ) * ((r : ℚ) + 1))) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : r ≤ γ := hr.2
        simp only [α, h1, h2, ↓reduceIte]
        ring
      rw [hcongr, ← Finset.mul_sum, sum_Icc_inv_mul_succ hm_ge1 hm_leγ]
    have hpart2 : (∑ r ∈ Finset.Icc (γ + 1) k, α r) = (k : ℚ) - (γ : ℚ) := by
      have hcongr : (∑ r ∈ Finset.Icc (γ + 1) k, α r) = ∑ _r ∈ Finset.Icc (γ + 1) k, (1 : ℚ) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : ¬ r ≤ γ := by omega
        simp only [α, h1, h2, ↓reduceIte]
      rw [hcongr, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      have hsub : k + 1 - (γ + 1) = k - γ := by omega
      rw [hsub, Nat.cast_sub (by omega)]
    change (i : ℚ) * (∑ r ∈ Finset.Icc m k, α r) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))
    rw [hsplit, Finset.sum_union hdisj, hpart1, hpart2]
    have hsimp : M * (1 / (m : ℚ) - 1 / ((γ : ℚ) + 1)) + ((k : ℚ) - (γ : ℚ)) =
        M / (m : ℚ) + ((k : ℚ) - (γ : ℚ)) / ((γ : ℚ) + 1) := by
      dsimp only [M]
      have hγ1_ne : (γ : ℚ) + 1 ≠ 0 := by positivity
      have hm_ne : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      field_simp
      ring
    rw [hsimp, mul_add]
    have hm_pos : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
    have hγ1_pos : (0 : ℚ) < (γ : ℚ) + 1 := by positivity
    have hM_nonneg : (0 : ℚ) ≤ M := by
      dsimp only [M]
      have hkg : (0 : ℚ) ≤ (k : ℚ) - (γ : ℚ) := by
        have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
        linarith
      exact mul_nonneg (by positivity) hkg
    have hkg_nonneg : (0 : ℚ) ≤ (k : ℚ) - (γ : ℚ) := by
      have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
      linarith
    have h1 : (i : ℚ) * (M / (m : ℚ)) ≤ M := by
      rw [mul_div_left_comm]
      have hratio : (i : ℚ) / (m : ℚ) ≤ 1 := by
        rw [div_le_one hm_pos]
        exact_mod_cast hm_gei
      nlinarith
    have h2 : (i : ℚ) * (((k : ℚ) - (γ : ℚ)) / ((γ : ℚ) + 1)) ≤ (k : ℚ) - (γ : ℚ) := by
      rw [mul_div_left_comm]
      have hratio : (i : ℚ) / ((γ : ℚ) + 1) ≤ 1 := by
        rw [div_le_one hγ1_pos]
        have : i ≤ γ + 1 := by omega
        exact_mod_cast this
      nlinarith
    have hsum_eq : M + ((k : ℚ) - (γ : ℚ)) = ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
      dsimp only [M]; ring
    linarith

/-- Exact rational square identity yielding Shitov's `8257 / 49923` cubic coefficient
with zero calculus! -/
private theorem shitov_cubic_poly_bound {n ρ β : ℚ} (hn : 0 ≤ n) (hρ : 0 ≤ ρ)
    (hcases : β = ρ ∨ (ρ ≤ n / 10 ∧ β ≤ n / 10)) :
    (7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - ρ ^ 3) / 6 -
      (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - β) +
      (250 / 16641 : ℚ) * ρ * n ^ 2 ≤ (8257 / 49923 : ℚ) * n ^ 3 := by
  have hsq_bound : ∀ x : ℚ, 0 ≤ x →
      (7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - x ^ 3) / 6 -
        (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - x) +
        (250 / 16641 : ℚ) * x * n ^ 2 ≤ (8257 / 49923 : ℚ) * n ^ 3 := by
    intro x hx
    have hid :
        (8257 / 49923 : ℚ) * n ^ 3 -
          ((7 / 48 : ℚ) * n ^ 3 + ((125 / 258 : ℚ) ^ 3 * n ^ 3 - x ^ 3) / 6 -
            (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - x) +
            (250 / 16641 : ℚ) * x * n ^ 2) =
        (1 / 6 : ℚ) * (x - (25 / 129 : ℚ) * n) ^ 2 * (x + (50 / 129 : ℚ) * n) := by
      ring
    have hnonneg : (0 : ℚ) ≤
        (1 / 6 : ℚ) * (x - (25 / 129 : ℚ) * n) ^ 2 * (x + (50 / 129 : ℚ) * n) := by
      positivity
    linarith
  rcases hcases with hβρ | ⟨hρ_le, hβ_le⟩
  · rw [hβρ]
    exact hsq_bound ρ hρ
  · let c : ℚ := n / 10
    have hc_eq : c = n / 10 := rfl
    have hc_nonneg : 0 ≤ c := by positivity
    have hmono_β :
        (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - c) ≤
        (125 / 33282 : ℚ) * n ^ 2 * ((125 / 258 : ℚ) * n - β) := by
      have hcoef : (0 : ℚ) ≤ (125 / 33282 : ℚ) * n ^ 2 := by positivity
      have hbc : β ≤ c := hβ_le
      nlinarith
    have hmono_ρ :
        (250 / 16641 : ℚ) * ρ * n ^ 2 - ρ ^ 3 / 6 ≤
        (250 / 16641 : ℚ) * c * n ^ 2 - c ^ 3 / 6 := by
      have hfac :
          ((250 / 16641 : ℚ) * c * n ^ 2 - c ^ 3 / 6) -
            ((250 / 16641 : ℚ) * ρ * n ^ 2 - ρ ^ 3 / 6) =
          (c - ρ) * ((250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6) := by
        ring
      have hpos2 : (0 : ℚ) ≤ (250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6 := by
        rw [hc_eq]
        nlinarith
      have hρc : ρ ≤ c := hρ_le
      have hprod : (0 : ℚ) ≤ (c - ρ) * ((250 / 16641 : ℚ) * n ^ 2 - (c ^ 2 + c * ρ + ρ ^ 2) / 6) :=
        mul_nonneg (by linarith) hpos2
      linarith
    have hbase := hsq_bound c hc_nonneg
    linarith

set_option maxHeartbeats 1000000 in
/-- Clean standalone rounding-error assembly lemma over `ℚ` for `n ≥ 100`. -/
private theorem shitov_rounding_assembly {n k γ ρ β : ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10)) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
      (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      (7 / 48 : ℚ) * (n : ℚ) ^ 3 + (n : ℚ) ^ 2 + ((k : ℚ) + 1) ^ 2 ≤
    (8257 / 49923 : ℚ) * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 := by
  intro M
  have hn_q : (100 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn100
  have hγ_le : (γ : ℚ) ≤ (125 / 258 : ℚ) * n := by
    have : 258 * γ ≤ 125 * n := by omega
    have hq : (258 : ℚ) * γ ≤ 125 * n := by exact_mod_cast this
    linarith
  have hγ_ge : (125 / 258 : ℚ) * n - 1 ≤ (γ : ℚ) := by
    have : 125 * n ≤ 258 * γ + 257 := by omega
    have hq : (125 : ℚ) * n ≤ 258 * γ + 257 := by exact_mod_cast this
    linarith
  have hk_le : (k : ℚ) ≤ (n : ℚ) / 2 - 1 := by
    have : 2 * k + 2 ≤ n := by omega
    have hq : (2 : ℚ) * k + 2 ≤ n := by exact_mod_cast this
    linarith
  have hk_ge : (n : ℚ) / 2 - 3 / 2 ≤ (k : ℚ) := by
    have : n ≤ 2 * k + 3 := by omega
    have hq : (n : ℚ) ≤ 2 * k + 3 := by exact_mod_cast this
    linarith
  have hkg_le : (k : ℚ) - γ ≤ (2 / 129 : ℚ) * n := by
    have h1 : 258 * k + 258 ≤ 129 * n := by omega
    have h2 : 125 * n ≤ 258 * γ + 257 := by omega
    have hq1 : (258 : ℚ) * k + 258 ≤ 129 * n := by exact_mod_cast h1
    have hq2 : (125 : ℚ) * n ≤ 258 * γ + 257 := by exact_mod_cast h2
    linarith
  have hkg_ge : (2 / 129 : ℚ) * n - 3 / 2 ≤ (k : ℚ) - γ := by linarith
  have hM_le : M ≤ (125 / 16641 : ℚ) * (n : ℚ) ^ 2 := by
    dsimp only [M]
    have h1 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have h2 : (0 : ℚ) ≤ (k : ℚ) - γ := by linarith
    have hprod : (γ : ℚ) * ((k : ℚ) - γ) ≤ ((125 / 258 : ℚ) * n) * ((2 / 129 : ℚ) * n) :=
      mul_le_mul hγ_le hkg_le h2 (by positivity)
    linarith
  have hM_ge : (125 / 16641 : ℚ) * (n : ℚ) ^ 2 - (n : ℚ) ≤ M := by
    dsimp only [M]
    have h1 : (0 : ℚ) ≤ (125 / 258 : ℚ) * n - 1 := by linarith
    have h2 : (0 : ℚ) ≤ (2 / 129 : ℚ) * n - 3 / 2 := by linarith
    have hprod : ((125 / 258 : ℚ) * n - 1) * ((2 / 129 : ℚ) * n - 3 / 2) ≤ (γ : ℚ) * ((k : ℚ) - γ) :=
      mul_le_mul hγ_ge hkg_ge h2 (by linarith)
    nlinarith
  have hγ_cub : ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 ≤
      (125 / 258 : ℚ) ^ 3 * (n : ℚ) ^ 3 / 6 + (1 / 2 : ℚ) * (n : ℚ) ^ 2 := by
    have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have h1 : ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) ≤
        ((125 / 258 : ℚ) * n + 1) * ((125 / 258 : ℚ) * n + 2) * ((125 / 258 : ℚ) * n + 3) := by
      have ha : (γ : ℚ) + 1 ≤ (125 / 258 : ℚ) * n + 1 := by linarith
      have hb : (γ : ℚ) + 2 ≤ (125 / 258 : ℚ) * n + 2 := by linarith
      have hc : (γ : ℚ) + 3 ≤ (125 / 258 : ℚ) * n + 3 := by linarith
      exact mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity)) hc
        (by positivity) (by positivity)
    nlinarith
  have hβ_le_γ : (β : ℚ) ≤ γ := by
    have : β ≤ γ := by omega
    exact_mod_cast this
  have hβ_pos : (0 : ℚ) < β := by
    have : 1 ≤ β := by omega
    exact_mod_cast (show 0 < β by omega)
  have hratio_le6 : ((γ : ℚ) - β) / (β : ℚ) ≤ 6 := by
    rw [div_le_iff₀ hβ_pos]
    have : γ ≤ 7 * β := by omega
    have hq : (γ : ℚ) ≤ 7 * β := by exact_mod_cast this
    linarith
  have hM_nonneg : (0 : ℚ) ≤ M := by
    dsimp only [M]
    have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
    have hkg0 : (0 : ℚ) ≤ (k : ℚ) - γ := by linarith
    exact mul_nonneg hγ0 hkg0
  have hM_div : (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) ≤ (1 / 40 : ℚ) * (n : ℚ) ^ 2 := by
    have heq : (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) = (M / 2) * (((γ : ℚ) - β) / (β : ℚ)) := by
      ring
    rw [heq]
    have h1 : (M / 2) * (((γ : ℚ) - β) / (β : ℚ)) ≤ (M / 2) * 6 :=
      mul_le_mul_of_nonneg_left hratio_le6 (by positivity)
    linarith
  have hM_main :
      (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((125 / 258 : ℚ) * n - β) -
        (1 / 2 : ℚ) * (n : ℚ) ^ 2 ≤ (M / 2) * ((γ : ℚ) - β) := by
    have hdiff_nonneg : (0 : ℚ) ≤ (γ : ℚ) - β := by linarith
    have hdiff_le : (γ : ℚ) - β ≤ (n : ℚ) / 2 := by linarith
    have h1 : ((125 / 16641 : ℚ) * (n : ℚ) ^ 2 - (n : ℚ)) / 2 * ((γ : ℚ) - β) ≤
        (M / 2) * ((γ : ℚ) - β) :=
      mul_le_mul_of_nonneg_right (by linarith) hdiff_nonneg
    have h2 : (n : ℚ) / 2 * ((γ : ℚ) - β) ≤ (1 / 4 : ℚ) * (n : ℚ) ^ 2 := by nlinarith
    have h3 : (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((125 / 258 : ℚ) * n - 1 - β) ≤
        (125 / 33282 : ℚ) * (n : ℚ) ^ 2 * ((γ : ℚ) - β) := by
      have hc : (0 : ℚ) ≤ (125 / 33282 : ℚ) * (n : ℚ) ^ 2 := by positivity
      nlinarith
    nlinarith
  have hρ_le_half : (ρ : ℚ) ≤ (n : ℚ) / 2 := by
    have hρ_q : (ρ : ℚ) ≤ γ := by exact_mod_cast hρ_le_γ
    linarith
  have hρ_nonneg : (0 : ℚ) ≤ ρ := Nat.cast_nonneg ρ
  have hρ_term : 2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - γ) ≤
      (250 / 16641 : ℚ) * (ρ : ℚ) * (n : ℚ) ^ 2 + (1 / 50 : ℚ) * (n : ℚ) ^ 2 := by
    have heq : ((γ : ℚ) + 1) * ((k : ℚ) - γ) = M + ((k : ℚ) - γ) := by
      dsimp only [M]; ring
    rw [mul_assoc (2 * (ρ : ℚ)), heq]
    have h1 : 2 * (ρ : ℚ) * (M + ((k : ℚ) - γ)) ≤
        2 * (ρ : ℚ) * ((125 / 16641 : ℚ) * (n : ℚ) ^ 2 + (2 / 129 : ℚ) * n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hk1_sq : ((k : ℚ) + 1) ^ 2 ≤ (1 / 4 : ℚ) * (n : ℚ) ^ 2 := by
    have hk0 : (0 : ℚ) ≤ (k : ℚ) + 1 := by positivity
    nlinarith
  have hpoly_cases : (β : ℚ) = ρ ∨ ((ρ : ℚ) ≤ n / 10 ∧ (β : ℚ) ≤ n / 10) := by
    by_cases hcmp : n / 10 ≤ ρ
    · left
      have hβ_eq : β = ρ := by rw [hβ, max_eq_left hcmp]
      exact_mod_cast hβ_eq
    · right
      have hβ_eq : β = n / 10 := by rw [hβ, max_eq_right (by omega : ρ ≤ n / 10)]
      have h10ρ : 10 * ρ ≤ n := by omega
      have h10β : 10 * β ≤ n := by rw [hβ_eq]; omega
      have h1 : (10 : ℚ) * ρ ≤ n := by exact_mod_cast h10ρ
      have h2 : (10 : ℚ) * β ≤ n := by exact_mod_cast h10β
      exact ⟨by linarith only [h1], by linarith only [h2]⟩
  have hcubic := shitov_cubic_poly_bound (by positivity) hρ_nonneg hpoly_cases
  have hexpand :
      (M / 2) * ((γ : ℚ) - β) * (1 - 1 / (β : ℚ)) =
      (M / 2) * ((γ : ℚ) - β) - (M / 2) * ((γ : ℚ) - β) * (1 / (β : ℚ)) := by
    ring
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  linarith only [hγ_cub, hM_div, hM_main, hρ_term, hk1_sq, hcubic, hexpand, hn2]

private theorem eight_mul_cube_ge {n k : ℕ} (hn : 100 ≤ n) (hk : n ≤ 2 * k + 3) :
    n ^ 3 ≤ 8 * ((k + 1) * ((k + 1) + 1) * ((k + 1) + 2)) := by
  have h1 : n - 1 ≤ 2 * (k + 1) := by omega
  have h2 : n + 1 ≤ 2 * ((k + 1) + 1) := by omega
  have h3 : n + 3 ≤ 2 * ((k + 1) + 2) := by omega
  have hprod : (n - 1) * (n + 1) * (n + 3) ≤
      (2 * (k + 1)) * (2 * ((k + 1) + 1)) * (2 * ((k + 1) + 2)) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hcub : n ^ 3 ≤ (n - 1) * (n + 1) * (n + 3) := by
    zify [show 1 ≤ n by omega]
    have hn' : (100 : ℤ) ≤ n := by omega
    nlinarith
  linarith

/-- Middle-sum telescoping dual bound over `r ∈ [ρ, k]` in Case 2 (`ρ ≤ γ`). -/
private theorem shitov_case2_mid_bound {n k γ ρ β : ℕ} {δ s : ℕ → ℕ}
    (hn100 : 100 ≤ n) (hk : k = (n - 2) / 2) (hγ : γ = (125 * n) / 258)
    (hρ_ge1 : 1 ≤ ρ) (hρ_le_γ : ρ ≤ γ) (hβ : β = max ρ (n / 10))
    (hsum_s_le : (∑ i ∈ Finset.Icc 1 k, s i) ≤ ρ)
    (hδ_pf : ∀ r ∈ Finset.Icc ρ k, δ r ≤ (r + 2).choose 2)
    (hδ_sh : ∀ r ∈ Finset.Icc ρ k, δ r ≤ 2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r) :
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    ((∑ r ∈ Finset.Icc ρ k, δ r : ℕ) : ℚ) ≤
      ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
        (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
      2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
      ((k : ℚ) + 1) ^ 2 := by
  intro M
  have hγ_lt_k : γ < k := by omega
  have h2γ_ge_k : k ≤ 2 * γ := by omega
  have hβ_ge10 : 10 ≤ β := by omega
  have hβ_le_γ : β ≤ γ := by omega
  have hρ_le_β : ρ ≤ β := by omega
  let α : ℕ → ℚ := fun r =>
    if r < β then 0
    else if r ≤ γ then M / ((r : ℚ) * ((r : ℚ) + 1))
    else 1
  have hM_nonneg : (0 : ℚ) ≤ M := by
    dsimp only [M]
    have : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
    nlinarith
  have hα_bounds : ∀ r ∈ Finset.Icc ρ k, (0 : ℚ) ≤ α r ∧ α r ≤ 1 := by
    intro r _hr
    dsimp only [α]
    split_ifs with h1 h2
    · exact ⟨le_rfl, zero_le_one⟩
    · have hr_geβ : β ≤ r := by omega
      have hr_pos : (0 : ℚ) < (r : ℚ) * ((r : ℚ) + 1) := by
        have : 0 < r := by omega
        positivity
      refine ⟨div_nonneg hM_nonneg hr_pos.le, ?_⟩
      rw [div_le_one hr_pos]
      have hM_nat : 66564 * (γ * (k - γ)) ≤ 500 * n ^ 2 := by
        have h1' : 258 * γ ≤ 125 * n := by omega
        have h2' : 258 * (k - γ) ≤ 4 * n := by omega
        have hprod : (258 * γ) * (258 * (k - γ)) ≤ (125 * n) * (4 * n) :=
          Nat.mul_le_mul h1' h2'
        linarith
      have hr_nat : 500 * n ^ 2 ≤ 66564 * (r * (r + 1)) := by
        have h10r1 : n ≤ 10 * (r + 1) := by omega
        have h10r : n ≤ 10 * r + 9 := by omega
        have hprod : (n - 9) * n ≤ (10 * r) * (10 * (r + 1)) :=
          Nat.mul_le_mul (by omega) h10r1
        zify [show 9 ≤ n by omega] at hprod ⊢
        nlinarith
      have hnat : γ * (k - γ) ≤ r * (r + 1) := by omega
      have hq : ((γ * (k - γ) : ℕ) : ℚ) ≤ ((r * (r + 1) : ℕ) : ℚ) := by exact_mod_cast hnat
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hq
      exact hq
    · exact ⟨zero_le_one, le_rfl⟩
  have hpt : ∀ r ∈ Finset.Icc ρ k,
      (δ r : ℚ) ≤
        (1 - α r) * ((r : ℚ) ^ 2 / 2) +
        2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) +
        (2 * (r : ℚ) + 1) := by
    intro r hr
    have hpf_nat : δ r ≤ (r + 2).choose 2 := hδ_pf r hr
    have hpf_2 : 2 * δ r ≤ (r + 2) * (r + 1) := by
      have hch : 2 * (r + 2).choose 2 = (r + 2) * (r + 1) := by
        rw [Nat.choose_two_right]
        rcases (Nat.even_mul_succ_self (r + 1)).two_dvd with ⟨t, ht⟩
        have hsub : r + 2 - 1 = r + 1 := by omega
        rw [hsub, show (r + 2) * (r + 1) = 2 * t by linarith]
        omega
      omega
    have hpf_q : (δ r : ℚ) ≤ (r : ℚ) ^ 2 / 2 + (2 * (r : ℚ) + 1) := by
      have h2q : (2 : ℚ) * δ r ≤ ((r : ℚ) + 2) * ((r : ℚ) + 1) := by
        exact_mod_cast hpf_2
      linarith
    have hsh_nat := hδ_sh r hr
    have hsh_q : (δ r : ℚ) ≤
        2 * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) + (2 * (r : ℚ) + 1) := by
      have hq : (δ r : ℚ) ≤
          ((2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r : ℕ) : ℚ) := by exact_mod_cast hsh_nat
      push_cast at hq
      linarith
    have ⟨hα0, hα1⟩ := hα_bounds r hr
    have h1 : (1 - α r) * (δ r : ℚ) ≤
        (1 - α r) * ((r : ℚ) ^ 2 / 2 + (2 * (r : ℚ) + 1)) :=
      mul_le_mul_of_nonneg_left hpf_q (by linarith)
    have h2 : α r * (δ r : ℚ) ≤
        α r * (2 * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) + (2 * (r : ℚ) + 1)) :=
      mul_le_mul_of_nonneg_left hsh_q hα0
    linarith
  have hPieceA :
      (∑ r ∈ Finset.Icc ρ k, (1 - α r) * ((r : ℚ) ^ 2 / 2)) ≤
        ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
          (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) := by
    have hsplit1 : Finset.Icc ρ k = Finset.Icc ρ γ ∪ Finset.Icc (γ + 1) k := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj1 : Disjoint (Finset.Icc ρ γ) (Finset.Icc (γ + 1) k) := by
      rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have hzero_hi : (∑ r ∈ Finset.Icc (γ + 1) k, (1 - α r) * ((r : ℚ) ^ 2 / 2)) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.mem_Icc] at hr
      have h1 : ¬ r < β := by omega
      have h2 : ¬ r ≤ γ := by omega
      simp [α, h1, h2]
    have hsplit2 : Finset.Icc ρ γ = Finset.Ico ρ β ∪ Finset.Icc β γ := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_union]; omega
    have hdisj2 : Disjoint (Finset.Ico ρ β) (Finset.Icc β γ) := by
      rw [Finset.disjoint_left]; intro r h1 h2
      simp only [Finset.mem_Ico, Finset.mem_Icc] at h1 h2; omega
    have hrew_sub :
        (∑ r ∈ Finset.Icc ρ γ, (1 - α r) * ((r : ℚ) ^ 2 / 2)) =
        (∑ r ∈ Finset.Icc ρ γ, (r : ℚ) ^ 2 / 2) -
        (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
      rw [hsplit2, Finset.sum_union hdisj2, Finset.sum_union hdisj2]
      have hlo : (∑ r ∈ Finset.Ico ρ β, (1 - α r) * ((r : ℚ) ^ 2 / 2)) =
          ∑ r ∈ Finset.Ico ρ β, (r : ℚ) ^ 2 / 2 := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Ico] at hr
        simp [α, hr.2]
      have hhi : (∑ r ∈ Finset.Icc β γ, (1 - α r) * ((r : ℚ) ^ 2 / 2)) =
          (∑ r ∈ Finset.Icc β γ, (r : ℚ) ^ 2 / 2) -
          (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        have h1 : ¬ r < β := by omega
        have h2 : r ≤ γ := hr.2
        have hr_ne : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
        have hr1_ne : (r : ℚ) + 1 ≠ 0 := by positivity
        simp only [α, h1, h2, ↓reduceIte]
        field_simp
      rw [hlo, hhi]
      ring
    have hsq_sum : (∑ r ∈ Finset.Icc ρ γ, (r : ℚ) ^ 2 / 2) ≤
        ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 := by
      have hle_choose : (∑ r ∈ Finset.Icc ρ γ, (r : ℚ) ^ 2 / 2) ≤
          ((∑ r ∈ Finset.Ico ρ (γ + 1), (r + 2).choose 2 : ℕ) : ℚ) := by
        have hIco : Finset.Icc ρ γ = Finset.Ico ρ (γ + 1) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hIco, Nat.cast_sum]
        refine Finset.sum_le_sum fun r _ => ?_
        have hch : 2 * (r + 2).choose 2 = (r + 2) * (r + 1) := by
          rw [Nat.choose_two_right]
          rcases (Nat.even_mul_succ_self (r + 1)).two_dvd with ⟨t, ht⟩
          have hsub : r + 2 - 1 = r + 1 := by omega
          rw [hsub, show (r + 2) * (r + 1) = 2 * t by linarith]
          omega
        have hq : (2 : ℚ) * ((r + 2).choose 2 : ℕ) = ((r : ℚ) + 2) * ((r : ℚ) + 1) := by
          exact_mod_cast hch
        have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg r
        nlinarith only [hq, hr0]
      have h6 := six_mul_sum_Ico_choose_two (by omega : ρ ≤ γ + 1)
      have hsub_le : ρ * (ρ + 1) * (ρ + 2) ≤ (γ + 1) * ((γ + 1) + 1) * ((γ + 1) + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      have h6q : (6 : ℚ) * ((∑ r ∈ Finset.Ico ρ (γ + 1), (r + 2).choose 2 : ℕ) : ℚ) =
          ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) - (ρ : ℚ) * ((ρ : ℚ) + 1) * ((ρ : ℚ) + 2) := by
        have hcast : ((6 * ∑ r ∈ Finset.Ico ρ (γ + 1), (r + 2).choose 2 : ℕ) : ℚ) =
            (((γ + 1) * ((γ + 1) + 1) * ((γ + 1) + 2) - ρ * (ρ + 1) * (ρ + 2) : ℕ) : ℚ) := by
          exact_mod_cast h6
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hsub_le] at hcast
        rw [hcast]
        push_cast
        ring
      have hρ_nonneg : (0 : ℚ) ≤ ρ := Nat.cast_nonneg ρ
      nlinarith only [hle_choose, h6q, hρ_nonneg]
    have hdiv_ge := sum_Icc_div_succ_ge (by omega : 1 ≤ β) hβ_le_γ
    have hM_half : (0 : ℚ) ≤ M / 2 := by linarith only [hM_nonneg]
    have hsub_ge : (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) ≤
        (M / 2) * (∑ r ∈ Finset.Icc β γ, (r : ℚ) / ((r : ℚ) + 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hdiv_ge hM_half
    rw [hsplit1, Finset.sum_union hdisj1, hzero_hi, add_zero, hrew_sub]
    linarith only [hsq_sum, hsub_ge]
  have hPieceB :
      (∑ r ∈ Finset.Icc ρ k, 2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ))) ≤
        2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
    have hswap :
        (∑ r ∈ Finset.Icc ρ k, 2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ))) =
        2 * ∑ i ∈ Finset.Icc 1 k, (s i : ℚ) * ((i : ℚ) * ∑ r ∈ Finset.Icc (max β i) k, α r) := by
      have hinner : ∀ r ∈ Finset.Icc ρ k,
          2 * α r * (∑ i ∈ Finset.Icc 1 r, (i : ℚ) * (s i : ℚ)) =
          ∑ i ∈ Finset.Icc 1 k, if i ≤ r then 2 * (s i : ℚ) * ((i : ℚ) * α r) else 0 := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        rw [← Finset.sum_filter, Finset.mul_sum]
        have hfilt : (Finset.Icc 1 k).filter (fun i => i ≤ r) = Finset.Icc 1 r := by
          ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [hfilt]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Icc] at hi
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Icc ρ k).filter (fun r => i ≤ r) = Finset.Icc (max ρ i) k := by
        ext r; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hfilt]
      have hdrop : (∑ r ∈ Finset.Icc (max ρ i) k, 2 * (s i : ℚ) * ((i : ℚ) * α r)) =
          ∑ r ∈ Finset.Icc (max β i) k, 2 * (s i : ℚ) * ((i : ℚ) * α r) := by
        have hsub : Finset.Icc (max β i) k ⊆ Finset.Icc (max ρ i) k := by
          intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
        symm
        refine Finset.sum_subset hsub fun r hr hnot => ?_
        simp only [Finset.mem_Icc] at hr hnot
        have hltβ : r < β := by omega
        simp [α, hltβ]
      rw [hdrop, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [hswap]
    have hle_sum :
        (∑ i ∈ Finset.Icc 1 k, (s i : ℚ) * ((i : ℚ) * ∑ r ∈ Finset.Icc (max β i) k, α r)) ≤
        ∑ i ∈ Finset.Icc 1 k, (s i : ℚ) * (((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ))) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mem_Icc] at hi
      exact mul_le_mul_of_nonneg_left
        (shitov_dual_weight_le (by omega) hβ_le_γ hγ_lt_k h2γ_ge_k hi.1 hi.2)
        (Nat.cast_nonneg _)
    rw [← Finset.sum_mul] at hle_sum
    have hsum_s_q : (∑ i ∈ Finset.Icc 1 k, (s i : ℚ)) ≤ (ρ : ℚ) := by
      exact_mod_cast hsum_s_le
    have hfactor_nonneg : (0 : ℚ) ≤ ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) := by
      have hγ0 : (0 : ℚ) ≤ γ := Nat.cast_nonneg γ
      have hγk : (γ : ℚ) ≤ k := by exact_mod_cast (by omega : γ ≤ k)
      nlinarith only [hγ0, hγk]
    have hmul := mul_le_mul_of_nonneg_right hsum_s_q hfactor_nonneg
    linarith only [hle_sum, hmul]
  have hPieceC : (∑ r ∈ Finset.Icc ρ k, (2 * (r : ℚ) + 1)) ≤ ((k : ℚ) + 1) ^ 2 := by
    have hnat : (∑ r ∈ Finset.Icc ρ k, (2 * r + 1)) ≤ (k + 1) ^ 2 := by
      have hsub : Finset.Icc ρ k ⊆ Finset.range (k + 1) := by
        intro r hr; rw [Finset.mem_Icc] at hr; rw [Finset.mem_range]; omega
      have hsum_odd : ∀ m : ℕ, (∑ r ∈ Finset.range m, (2 * r + 1)) = m ^ 2 := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm => rw [Finset.sum_range_succ, ihm]; ring
      calc (∑ r ∈ Finset.Icc ρ k, (2 * r + 1))
          ≤ ∑ r ∈ Finset.range (k + 1), (2 * r + 1) := Finset.sum_le_sum_of_subset hsub
        _ = (k + 1) ^ 2 := hsum_odd (k + 1)
    have hq : ((∑ r ∈ Finset.Icc ρ k, (2 * r + 1) : ℕ) : ℚ) ≤ (((k + 1) ^ 2 : ℕ) : ℚ) := by
      exact_mod_cast hnat
    push_cast at hq
    exact hq
  have hsum_pt := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_pt
  rw [Nat.cast_sum]
  linarith only [hsum_pt, hPieceA, hPieceB, hPieceC]

end TelescopingDualHelpers

/- ## Part 4: Main Sub-Pin–Frankl Theorems -/

section MainTheorems

/-- **Exact Shitov (2019) General Cubic Upper Bound (`8257 / 49923 n³ + 3 n²`)**:
For every synchronizing DFA on `n ≥ 1` states, there exists a synchronizing word `w` with
`49923 * w.length ≤ 8257 * n ^ 3 + 149769 * n ^ 2` (`8257/49923 ≈ 0.165395 < 1/6 ≈ 0.166667`). -/
theorem sub_pin_frankl_shitov_bound {Q : Type u} [Fintype Q] [Nonempty Q] {α : Type v}
    (A : DFA Q α) (hSync : A.IsSynchronizing) :
    ∃ w : List α, A.IsSyncWord w ∧
      49923 * w.length ≤ 8257 * (Fintype.card Q) ^ 3 + 149769 * (Fintype.card Q) ^ 2 := by
  classical
  let n := Fintype.card Q
  have hn1 : 1 ≤ n := Fintype.card_pos
  -- Small n < 100: directly from verified Pin–Frankl (6 * L ≤ n^3)
  by_cases hsmall : n < 100
  · obtain ⟨w, hw, hpf⟩ := pin_frankl_bound A hSync
    refine ⟨w, hw, ?_⟩
    change 6 * w.length ≤ n ^ 3 - n at hpf
    have h6 : 6 * w.length ≤ n ^ 3 := le_trans hpf (Nat.sub_le _ _)
    have hn_le : n ≤ 99 := by omega
    -- 6 * 49923 * L ≤ 49923 * n^3 = 49542 * n^3 + 381 * n^3 ≤ 49542 * n^3 + 381 * 99 * n^2
    -- and 381 * 99 = 37719 ≤ 6 * 149769 = 898614
    nlinarith
  -- Main regime: n ≥ 100
  have hn100 : 100 ≤ n := by omega
  obtain ⟨w_opt, hw_opt_sync, hw_opt_len⟩ := exists_syncWord_len_minCorankLen A hSync
  refine ⟨w_opt, hw_opt_sync, ?_⟩
  rw [hw_opt_len]
  change 49923 * minCorankLen A hSync (n - 1) ≤ 8257 * n ^ 3 + 149769 * n ^ 2
  let k := (n - 2) / 2
  have hk_ge49 : 49 ≤ k := by omega
  have hk_2le : 2 * k + 2 ≤ n := by omega
  have hk_2ge : n ≤ 2 * k + 3 := by omega
  -- Case 0: every corank gap δ_j (j ≤ n - 2) is at most 2 * k
  by_cases hbig : ∃ j : ℕ, j ≤ n - 2 ∧ 2 * k < corankGap A hSync j
  swap
  · push Not at hbig
    have hlam_le : minCorankLen A hSync (n - 1) ≤ n ^ 2 := by
      rw [minCorankLen_eq_sum_range A hSync le_rfl]
      calc (∑ j ∈ Finset.range (n - 1), corankGap A hSync j)
          ≤ ∑ _j ∈ Finset.range (n - 1), (2 * k) := by
            refine Finset.sum_le_sum fun j hj => hbig j (by rw [Finset.mem_range] at hj; omega)
        _ = (n - 1) * (2 * k) := by simp
        _ ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
        _ = n ^ 2 := by ring
    nlinarith
  -- Otherwise let ρ = min {j : δ_j > 2 * k}
  let ρ := Nat.find hbig
  have hρ_spec : ρ ≤ n - 2 ∧ 2 * k < corankGap A hSync ρ := Nat.find_spec hbig
  have hρ_min : ∀ j < ρ, corankGap A hSync j ≤ 2 * k := by
    intro j hj
    by_contra hgt
    push Not at hgt
    exact Nat.find_min hbig hj ⟨by omega, hgt⟩
  have hρ_ge1 : 1 ≤ ρ := by
    by_contra h0
    have hρ0 : ρ = 0 := by omega
    have hgap0 := corankGap_le_pinFrankl A hSync (by omega : 0 + 1 ≤ n - 1)
    have hch : (0 + 2).choose 2 = 1 := by decide
    have hgt := hρ_spec.2
    rw [hρ0] at hgt
    omega
  have hlam_ρ_le : minCorankLen A hSync ρ ≤ n ^ 2 := by
    rw [minCorankLen_eq_sum_range A hSync (by omega : ρ ≤ n - 1)]
    calc (∑ j ∈ Finset.range ρ, corankGap A hSync j)
        ≤ ∑ _j ∈ Finset.range ρ, (2 * k) :=
          Finset.sum_le_sum fun j hj => hρ_min j (Finset.mem_range.mp hj)
      _ = ρ * (2 * k) := by simp
      _ ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
      _ = n ^ 2 := by ring
  let γ := (125 * n) / 258
  -- Case 1: γ < ρ ⇒ ρ ≥ (2/5) n, pure Pin–Frankl gives ≤ (117/750) n³ < (8257/49923) n³!
  by_cases hρ_gt_γ : γ < ρ
  · have h5ρ : 2 * n ≤ 5 * ρ := by omega
    have htail : 6 * (∑ j ∈ Finset.Ico ρ (n - 1), corankGap A hSync j) ≤ n ^ 3 - ρ ^ 3 := by
      have hpf : (∑ j ∈ Finset.Ico ρ (n - 1), corankGap A hSync j) ≤
          ∑ j ∈ Finset.Ico ρ (n - 1), (j + 2).choose 2 := by
        refine Finset.sum_le_sum fun j hj => corankGap_le_pinFrankl A hSync
          (by rw [Finset.mem_Ico] at hj; omega)
      have h6 := Nat.mul_le_mul_left 6 hpf
      rw [six_mul_sum_Ico_choose_two (by omega : ρ ≤ n - 1)] at h6
      have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by
        zify [hn1]; nlinarith
      have hbot : ρ ^ 3 ≤ ρ * (ρ + 1) * (ρ + 2) := by nlinarith
      omega
    have htele := minCorankLen_eq_add_sum_Ico A hSync (by omega : ρ ≤ n - 1) le_rfl
    have hρ_le_n : ρ ≤ n := by omega
    have hcub : ρ ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hρ_le_n 3
    have h5cub : (2 * n) ^ 3 ≤ (5 * ρ) ^ 3 := Nat.pow_le_pow_left h5ρ 3
    zify [hcub] at htail
    zify at h5cub hlam_ρ_le htele ⊢
    nlinarith
  -- Case 2: ρ ≤ γ — apply the Zero-Calculus Telescoping Rational Dual!
  · have hρ_le_γ : ρ ≤ γ := by omega
    let β := max ρ (n / 10)
    have hk1_le_n1 : k + 1 ≤ n - 1 := by omega
    -- Telescoping split: lam(n - 1) = lam(ρ) + S_mid + S_tail
    let S_mid := ∑ r ∈ Finset.Icc ρ k, corankGap A hSync r
    let S_tail := ∑ j ∈ Finset.Ico (k + 1) (n - 1), corankGap A hSync j
    have hdecomp : minCorankLen A hSync (n - 1) = minCorankLen A hSync ρ + S_mid + S_tail := by
      have h1 := minCorankLen_eq_add_sum_Ico A hSync (by omega : ρ ≤ k + 1) hk1_le_n1
      have h2 := minCorankLen_eq_add_sum_Ico A hSync hk1_le_n1 le_rfl
      have hIco_eq : Finset.Ico ρ (k + 1) = Finset.Icc ρ k := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [hIco_eq] at h1
      omega
    -- Tail bound: S_tail ≤ (7/48) n^3 (in ℚ)
    have hS_tail_q : (S_tail : ℚ) ≤ (7 / 48 : ℚ) * (n : ℚ) ^ 3 := by
      have hpf : S_tail ≤ ∑ j ∈ Finset.Ico (k + 1) (n - 1), (j + 2).choose 2 := by
        refine Finset.sum_le_sum fun j hj => corankGap_le_pinFrankl A hSync
          (by rw [Finset.mem_Ico] at hj; omega)
      have h6 := Nat.mul_le_mul_left 6 hpf
      rw [six_mul_sum_Ico_choose_two hk1_le_n1] at h6
      have htop : (n - 1) * ((n - 1) + 1) * ((n - 1) + 2) ≤ n ^ 3 := by
        zify [hn1]; nlinarith
      have hbot : n ^ 3 ≤ 8 * ((k + 1) * ((k + 1) + 1) * ((k + 1) + 2)) :=
        eight_mul_cube_ge hn100 hk_2ge
      have h48 : 48 * S_tail ≤ 7 * n ^ 3 := by omega
      have hq : (48 : ℚ) * S_tail ≤ 7 * (n : ℚ) ^ 3 := by exact_mod_cast h48
      linarith
    -- Bucket counts s_i = |{j < ρ : 2i - 1 ≤ δ_j ≤ 2i}|
    let B : ℕ → Finset ℕ := fun i =>
      (Finset.range ρ).filter (fun j => 2 * i - 1 ≤ corankGap A hSync j ∧ corankGap A hSync j ≤ 2 * i)
    let s : ℕ → ℕ := fun i => (B i).card
    have hB_disj : ∀ i₁ ∈ Finset.Icc 1 k, ∀ i₂ ∈ Finset.Icc 1 k, i₁ ≠ i₂ → Disjoint (B i₁) (B i₂) := by
      intro i₁ hi₁ i₂ hi₂ hne
      rw [Finset.mem_Icc] at hi₁ hi₂
      rw [Finset.disjoint_left]
      intro j hj₁ hj₂
      simp only [B, Finset.mem_filter] at hj₁ hj₂
      omega
    have hsum_s_le : (∑ i ∈ Finset.Icc 1 k, s i) ≤ ρ := by
      have hcard_bi : ((Finset.Icc 1 k).biUnion B).card = ∑ i ∈ Finset.Icc 1 k, s i :=
        Finset.card_biUnion (fun i₁ hi₁ i₂ hi₂ hne => hB_disj i₁ hi₁ i₂ hi₂ hne)
      rw [← hcard_bi]
      have hsub : (Finset.Icc 1 k).biUnion B ⊆ Finset.range ρ := by
        intro j hj
        rw [Finset.mem_biUnion] at hj
        rcases hj with ⟨i, _, hji⟩
        exact (Finset.mem_filter.mp hji).1
      calc ((Finset.Icc 1 k).biUnion B).card
          ≤ (Finset.range ρ).card := Finset.card_le_card hsub
        _ = ρ := Finset.card_range ρ
    -- Both bounds on each δ_r (r ∈ Icc ρ k)
    have hdelta_shitov : ∀ r ∈ Finset.Icc ρ k,
        corankGap A hSync r ≤ 2 * (∑ i ∈ Finset.Icc 1 r, i * s i) + 2 * r := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hex_τ : ∃ τ : ℕ, τ ≤ n - 2 ∧ 2 * r < corankGap A hSync τ := ⟨ρ, hρ_spec.1, by omega⟩
      let τ := Nat.find hex_τ
      have hτ_spec : τ ≤ n - 2 ∧ 2 * r < corankGap A hSync τ := Nat.find_spec hex_τ
      have hτ_le_ρ : τ ≤ ρ := Nat.find_min' hex_τ ⟨hρ_spec.1, by omega⟩
      have hτ_min : ∀ j < τ, corankGap A hSync j ≤ 2 * r := by
        intro j hj
        by_contra hgt
        push Not at hgt
        exact Nat.find_min hex_τ hj ⟨by omega, hgt⟩
      have hshitov : corankGap A hSync r ≤ minCorankLen A hSync τ + 2 * r :=
        shitov_corank_gap A hSync (by omega) (by omega) (by omega) hτ_spec.2
      have hlam_τ_le : minCorankLen A hSync τ ≤ 2 * ∑ i ∈ Finset.Icc 1 r, i * s i := by
        rw [minCorankLen_eq_sum_range A hSync (by omega : τ ≤ n - 1)]
        have hpos_sum : (∑ j ∈ Finset.range τ, corankGap A hSync j) =
            ∑ j ∈ (Finset.range τ).filter (fun j => 1 ≤ corankGap A hSync j),
              corankGap A hSync j := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases h0 : corankGap A hSync j = 0
          · simp [h0]
          · have h1 : 1 ≤ corankGap A hSync j := by omega
            simp [h1]
        rw [hpos_sum]
        have hsub_bi : (Finset.range τ).filter (fun j => 1 ≤ corankGap A hSync j) ⊆
            (Finset.Icc 1 r).biUnion B := by
          intro j hj
          rw [Finset.mem_filter, Finset.mem_range] at hj
          have hle2r := hτ_min j hj.1
          rw [Finset.mem_biUnion]
          refine ⟨(corankGap A hSync j + 1) / 2, Finset.mem_Icc.mpr (by omega), ?_⟩
          simp only [B, Finset.mem_filter, Finset.mem_range]
          omega
        have hdisj_r : Set.PairwiseDisjoint (↑(Finset.Icc 1 r) : Set ℕ) B := fun i₁ hi₁ i₂ hi₂ hne =>
          hB_disj i₁ (Finset.Icc_subset_Icc_right (by omega) hi₁)
            i₂ (Finset.Icc_subset_Icc_right (by omega) hi₂) hne
        calc (∑ j ∈ (Finset.range τ).filter (fun j => 1 ≤ corankGap A hSync j),
                corankGap A hSync j)
            ≤ ∑ j ∈ (Finset.Icc 1 r).biUnion B, corankGap A hSync j :=
              Finset.sum_le_sum_of_subset hsub_bi
          _ = ∑ i ∈ Finset.Icc 1 r, ∑ j ∈ B i, corankGap A hSync j :=
              Finset.sum_biUnion hdisj_r
          _ ≤ ∑ i ∈ Finset.Icc 1 r, ∑ _j ∈ B i, (2 * i) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2.2
          _ = ∑ i ∈ Finset.Icc 1 r, (B i).card * (2 * i) := by simp
          _ = 2 * ∑ i ∈ Finset.Icc 1 r, i * s i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by dsimp only [s]; ring
      omega
    -- Apply the standalone telescoping rational dual middle-sum bound
    let M : ℚ := (γ : ℚ) * ((k : ℚ) - (γ : ℚ))
    have hS_mid_q :
        (S_mid : ℚ) ≤
          ((γ : ℚ) + 1) * ((γ : ℚ) + 2) * ((γ : ℚ) + 3) / 6 - (ρ : ℚ) ^ 3 / 6 -
            (M / 2) * ((γ : ℚ) - (β : ℚ)) * (1 - 1 / (β : ℚ)) +
          2 * (ρ : ℚ) * ((γ : ℚ) + 1) * ((k : ℚ) - (γ : ℚ)) +
          ((k : ℚ) + 1) ^ 2 :=
      shitov_case2_mid_bound hn100 rfl rfl hρ_ge1 hρ_le_γ rfl hsum_s_le
        (fun r hr => corankGap_le_pinFrankl A hSync (by rw [Finset.mem_Icc] at hr; omega))
        hdelta_shitov
    have hlam_ρ_q : (minCorankLen A hSync ρ : ℚ) ≤ (n : ℚ) ^ 2 := by exact_mod_cast hlam_ρ_le
    have hdecomp_q : (minCorankLen A hSync (n - 1) : ℚ) =
        (minCorankLen A hSync ρ : ℚ) + (S_mid : ℚ) + (S_tail : ℚ) := by
      exact_mod_cast hdecomp
    have hasm := shitov_rounding_assembly hn100 rfl rfl hρ_le_γ rfl
    have hfinal_q : (minCorankLen A hSync (n - 1) : ℚ) ≤
        (8257 / 49923 : ℚ) * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 := by
      linarith only [hdecomp_q, hlam_ρ_q, hS_mid_q, hS_tail_q, hasm]
    have hmul_q : (49923 : ℚ) * (minCorankLen A hSync (n - 1) : ℚ) ≤
        8257 * (n : ℚ) ^ 3 + 149769 * (n : ℚ) ^ 2 := by
      linarith only [hfinal_q]
    exact_mod_cast hmul_q

end MainTheorems

end Cerny

open Filter Asymptotics in
theorem OMA.solution : type_of% @CernyConjecture.shitov_upper_bound := by
  refine ⟨fun n : ℝ => 3 * n ^ 2, ?_, ?_⟩
  · exact (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (p := 2) (q := 3) (by norm_num)).const_mul_left 3
  · intro α σ inst M hM
    obtain ⟨w₀, p, hp⟩ := hM
    let A : Cerny.DFA σ α := ⟨M.step⟩
    have hSync : A.IsSynchronizing := ⟨w₀, p, hp⟩
    obtain ⟨w, hw, hlen⟩ := @Cerny.sub_pin_frankl_shitov_bound σ inst ⟨p⟩ α A hSync
    refine ⟨w, hw, ?_⟩
    have hlenReal : (49923 : ℝ) * (w.length : ℝ) ≤
        8257 * (Fintype.card σ : ℝ) ^ 3 + 149769 * (Fintype.card σ : ℝ) ^ 2 := by
      exact_mod_cast hlen
    have hcoeff : (7 / 48 + 2 * 15625 / 1597536 : ℝ) = 8257 / 49923 := by norm_num
    rw [hcoeff]
    linarith only [hlenReal]
