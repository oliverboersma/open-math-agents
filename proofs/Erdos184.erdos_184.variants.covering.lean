import FormalConjectures.ErdosProblems.«184»
import Mathlib

/-!
# Pyber's cycle-and-edge covering theorem

We prove the component-corrected bound for all finite simple graphs. In each
connected component, choose a maximal even subgraph. Its edge complement is a
forest. Adding a length-two path parallel to each edge of that forest makes
the graph Eulerian and increases the vertex count to at most twice its
original size minus one. Fan's bound then gives a cycle cover within the
required budget. Suppressing the added vertices gives cycles and single
edges in the original graph. The bounds add over the connected components.
-/

/-
The Lovasz partition proof below is adapted from OpenAI Math.
Source commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CycleDecomposition/Lovasz.lean
The import, classical scope, and several lemma names were adjusted for Lean 4.33.1.
The adapted portion is distributed under the Apache License, Version 2.0.

The covering bound is due to Genghua Fan, Covers of eulerian graphs (2003).
https://doi.org/10.1016/S0095-8956(03)00068-6

The main proof uses the Lovasz partition at a universal vertex and increases the
degree of the chosen vertex by switching edges. It preserves the parity of every
edge multiplicity and keeps multiplicity one for edges between neighbors of the
chosen vertex.
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
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

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


namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64 cycleUniverse65 cycleUniverse66 cycleUniverse67 cycleUniverse68 cycleUniverse69 cycleUniverse70 cycleUniverse71 cycleUniverse72 cycleUniverse73 cycleUniverse74 cycleUniverse75 cycleUniverse76 cycleUniverse77 cycleUniverse78 cycleUniverse79 cycleUniverse80 cycleUniverse81 cycleUniverse82 cycleUniverse83 cycleUniverse84 cycleUniverse85

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Lovasz
universe u
noncomputable section
open SimpleGraph
open scoped Classical

def StarActive {V : Type cycleUniverse1} (S : Set V) (R : V → V → Prop) (v : V) : Prop :=
  ∃ a ∈ S, Relation.ReflTransGen R a v

lemma starActive_source {V : Type cycleUniverse2} {S : Set V} {R : V → V → Prop}
    {v : V} (hv : v ∈ S) : StarActive S R v :=
  ⟨v, hv, .refl⟩

lemma starActive_step {V : Type cycleUniverse3} {S : Set V} {R : V → V → Prop}
    {v w : V} (hv : StarActive S R v) (h : R v w) : StarActive S R w := by
  obtain ⟨a, ha, hr⟩ := hv
  exact ⟨a, ha, hr.tail h⟩

lemma starActive_iff {V : Type cycleUniverse4} {S : Set V} {R : V → V → Prop} {v : V} :
    StarActive S R v ↔ v ∈ S ∨ ∃ w, StarActive S R w ∧ R w v := by
  constructor
  · rintro ⟨a, ha, hr⟩
    rcases hr.cases_tail with rfl | ⟨w, hw, h⟩
    · exact Or.inl ha
    · exact Or.inr ⟨w, ⟨a, ha, hw⟩, h⟩
  · rintro (h | ⟨w, hw, h⟩)
    · exact starActive_source h
    · exact starActive_step hw h

lemma starActive_original_iff {V : Type cycleUniverse5} {S T : Set V} {R : V → V → Prop}
    (hST : Disjoint S T) {v : V} (hv : v ∈ T) :
    StarActive S R v ↔ ∃ w, StarActive S R w ∧ R w v := by
  rw [starActive_iff]
  have hs : v ∉ S := fun h => Set.disjoint_left.mp hST h hv
  simp [hs]

lemma starActive_subset {V : Type cycleUniverse6} {S T : Set V} {R : V → V → Prop}
    (hS : S ⊆ T) (hR : ∀ a b, R a b → b ∈ T) :
    {v | StarActive S R v} ⊆ T := by
  rintro v ⟨a, ha, hr⟩
  rcases hr.cases_tail with rfl | ⟨w, _, h⟩
  · exact hS ha
  · exact hR w v h

lemma starActive_no_loop {V : Type cycleUniverse7} {S : Set V} {R : V → V → Prop}
    (hinj : ∀ a b c, R a c → R b c → a = b)
    (hsource : ∀ a b, a ∈ S → ¬ R b a)
    {v : V} (hv : StarActive S R v) : ¬ R v v := by
  obtain ⟨a, ha, hr⟩ := hv
  induction hr with
  | refl => exact hsource a a ha
  | @tail b c hab hbc ih =>
    intro hcc
    have he : b = c := hinj b c c hbc hcc
    subst c
    exact ih hbc

lemma star_inj {V : Type cycleUniverse8} {x a b : V} : s(x,a) = s(x,b) ↔ a = b := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, h'⟩)
    · exact h
    · exact h'.trans h
  · intro h; exact Or.inl ⟨rfl, h⟩

structure PathPiece {V : Type cycleUniverse9} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  positive : 0 < walk.length

lemma PathPiece.ends_ne {V : Type cycleUniverse10} {G : SimpleGraph V} (P : PathPiece G) :
    P.start ≠ P.finish := by
  intro h
  have hz := (P.isPath.nil_iff_eq.mpr h).length_eq_zero
  have := P.positive
  omega

structure Piece {V : Type cycleUniverse11} (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish
  simple : (walk.IsPath ∧ 0 < walk.length) ∨
    ∃ h : finish = start, (walk.copy rfl h).IsCycle

namespace Piece
variable {V : Type cycleUniverse12} {G : SimpleGraph V}

def ofPath (p : PathPiece G) : Piece G :=
  ⟨p.start, p.finish, p.walk, Or.inl ⟨p.isPath, p.positive⟩⟩

def ofCycle {v : V} (p : G.Walk v v) (h : p.IsCycle) : Piece G :=
  ⟨v, v, p, Or.inr ⟨rfl, h⟩⟩

end Piece

structure Arm {V : Type cycleUniverse13} (G : SimpleGraph V) (x : V) where
  near : V
  far : V
  adj : G.Adj x near
  walk : G.Walk near far
  isPath : walk.IsPath
  avoids : x ∉ walk.support

namespace Arm
variable {V : Type cycleUniverse14} {G : SimpleGraph V} {x : V}

def tip (A : Arm G x) : PathPiece G where
  start := x
  finish := A.far
  walk := .cons A.adj A.walk
  isPath := A.isPath.cons A.avoids
  positive := by simp

def flip (A : Arm G x) (h : G.Adj x A.far) : Arm G x where
  near := A.far
  far := A.near
  adj := h
  walk := A.walk.reverse
  isPath := A.isPath.reverse
  avoids := by simpa using A.avoids

@[simp] lemma flip_edges (A : Arm G x) (h : G.Adj x A.far) :
    (A.flip h).walk.edgeSet = A.walk.edgeSet := by simp [flip]

@[simp] lemma mem_flip_support (A : Arm G x) (h : G.Adj x A.far) (v : V) :
    v ∈ (A.flip h).walk.support ↔ v ∈ A.walk.support := by simp [flip]

lemma two_arms_isPath (A B : Arm G x)
    (hd : A.walk.support.Disjoint B.walk.support) :
    ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).IsPath := by
  apply Walk.IsPath.mk'
  simp only [Walk.support_append, Walk.support_reverse, Walk.support_cons,
    List.tail_cons, List.reverse_cons, List.append_assoc]
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_reverse.mpr A.isPath.support_nodup, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨B.avoids, B.isPath.support_nodup⟩
  · rw [List.disjoint_left]
    intro v hv hq
    have hav : v ∈ A.walk.support := List.mem_reverse.mp hv
    rcases List.mem_cons.mp hq with rfl | hq
    · exact A.avoids hav
    · exact List.disjoint_left.mp hd hav hq

def join (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) : PathPiece G where
  start := A.far
  finish := B.far
  walk := (Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)
  isPath := two_arms_isPath A B hd
  positive := by simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons]; omega

lemma join_edges (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    (A.join B hd).walk.edgeSet =
      A.walk.edgeSet ∪ B.walk.edgeSet ∪ {s(x,A.near), s(x,B.near)} := by
  simp only [join, Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons]
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma near_ne (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    A.near ≠ B.near := by
  intro h
  exact List.disjoint_left.mp hd A.walk.start_mem_support (by simpa only [h] using B.walk.start_mem_support)

lemma far_ne (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    A.far ≠ B.far := (A.join B hd).ends_ne

lemma far_ne_center (A : Arm G x) : A.far ≠ x := by
  intro h
  apply A.avoids
  simpa only [h] using A.walk.end_mem_support

lemma star_not_mem (A : Arm G x) (v : V) : s(x,v) ∉ A.walk.edgeSet := by
  intro he
  exact A.avoids (Walk.mem_support_iff_exists_mem_edges.mpr
    (Or.inr ⟨s(x,v), he, by simp⟩))

lemma flip_disjoint_left (A B : Arm G x) (h : G.Adj x A.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    (A.flip h).walk.support.Disjoint B.walk.support := by
  rw [List.disjoint_left] at hd ⊢
  intro v hv hb
  exact hd ((A.mem_flip_support h v).mp hv) hb

lemma flip_disjoint_right (A B : Arm G x) (h : G.Adj x B.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    A.walk.support.Disjoint (B.flip h).walk.support := by
  exact (flip_disjoint_left B A h hd.symm).symm

def orient (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) : Arm G x :=
  if ha : active then A.flip (h ha) else A

@[simp] lemma orient_edges (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).walk.edgeSet = A.walk.edgeSet := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A.flip (h ha) by simp [Arm.orient, ha])).trans (A.flip_edges _)
  · exact congrArg (fun B : Arm G x => B.walk.edgeSet)
      (show A.orient active h = A by simp [Arm.orient, ha])

@[simp] lemma orient_near (A : Arm G x) (active : Prop) (h : active → G.Adj x A.far) :
    (A.orient active h).near = if active then A.far else A.near := by
  by_cases ha : active <;> simp [orient, flip, ha]

@[simp] lemma mem_orient_support (A : Arm G x) (active : Prop)
    (h : active → G.Adj x A.far) (v : V) :
    v ∈ (A.orient active h).walk.support ↔ v ∈ A.walk.support := by
  by_cases ha : active
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A.flip (h ha) by simp [Arm.orient, ha])).to_iff.trans
        (A.mem_flip_support _ v)
  · exact (congrArg (fun B : Arm G x => v ∈ B.walk.support)
      (show A.orient active h = A by simp [Arm.orient, ha])).to_iff

lemma orient_disjoint (A B : Arm G x) (p q : Prop)
    (ha : p → G.Adj x A.far) (hb : q → G.Adj x B.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    (A.orient p ha).walk.support.Disjoint (B.orient q hb).walk.support := by
  rw [List.disjoint_left]
  intro v hv hw
  exact List.disjoint_left.mp hd ((A.mem_orient_support p ha v).mp hv)
    ((B.mem_orient_support q hb v).mp hw)

end Arm

inductive Frame {V : Type cycleUniverse15} (G : SimpleGraph V) (x : V) where
  | away (p : PathPiece G) (avoid : x ∉ p.walk.support)
  | tip (A : Arm G x)
  | through (A B : Arm G x) (disjoint : A.walk.support.Disjoint B.walk.support)

namespace Frame
variable {V : Type cycleUniverse16} {G : SimpleGraph V} {x : V}

def path : Frame G x → PathPiece G
  | .away p _ => p
  | .tip A => A.tip
  | .through A B hd => A.join B hd

def Port : Frame G x → Type
  | .away _ _ => Bool
  | .tip _ => Unit
  | .through _ _ _ => Bool

def endpoint : (F : Frame G x) → F.Port → V
  | .away p _, false => p.start
  | .away p _, true => p.finish
  | .tip A, _ => A.far
  | .through A _ _, false => A.far
  | .through _ B _, true => B.far

def exit : (F : Frame G x) → F.Port → Option V
  | .away _ _, _ => none
  | .tip _, _ => none
  | .through A _ _, false => some A.near
  | .through _ B _, true => some B.near

def inserted (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x, F.endpoint p)}

def removed (F : Frame G x) (active : F.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, F.exit p = some v ∧ e = s(x,v)}

lemma endpoint_ne_center (F : Frame G x) (p : F.Port) : F.endpoint p ≠ x := by
  cases F with
  | away P hx =>
    cases p
    · change P.start ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.start_mem_support
    · change P.finish ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.end_mem_support
  | tip A => exact A.far_ne_center
  | through A B hd => cases p <;> exact Arm.far_ne_center _

lemma endpoint_injective (F : Frame G x) : Function.Injective F.endpoint := by
  cases F with
  | away P hx =>
    intro a b hab
    cases a <;> cases b <;> first | rfl | exact False.elim (P.ends_ne hab) |
      exact False.elim (P.ends_ne hab.symm)
  | tip A =>
    change Function.Injective (fun (_ : Unit) => A.far)
    exact fun _ _ _ => Subsingleton.elim _ _
  | through A B hd =>
    intro a b hab
    cases a <;> cases b <;> first | rfl | exact False.elim (A.far_ne B hd hab) |
      exact False.elim (A.far_ne B hd hab.symm)

lemma port_iff_endpoint (F : Frame G x) (v : V) :
    (∃ p : F.Port, F.endpoint p = v) ↔
      (F.path.start = v ∨ F.path.finish = v) ∧ v ≠ x := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨?_, (F.endpoint_ne_center p)⟩
    cases F with
    | away P hx => cases p <;> simp [endpoint, path]
    | tip A => exact Or.inr rfl
    | through A B hd => cases p <;> simp [endpoint, path, Arm.join]
  · rintro ⟨he, hx⟩
    cases F with
    | away P hp =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩
    | tip A =>
      rcases he with he | he
      · exact (hx he.symm).elim
      · exact ⟨(), he⟩
    | through A B hd =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩

lemma exit_edge (F : Frame G x) (p : F.Port) (v : V) (h : F.exit p = some v) :
    s(x,v) ∈ F.path.walk.edgeSet := by
  cases F with
  | away P hx => cases h
  | tip A => cases h
  | through A B hd =>
    cases p
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)

lemma removed_subset (F : Frame G x) (active : F.Port → Prop) :
    F.removed active ⊆ F.path.walk.edgeSet := by
  rintro e ⟨p, hp, v, hv, rfl⟩
  exact F.exit_edge p v hv

@[simp] lemma removed_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).removed active = ∅ := by
  ext e; simp [removed, exit]

@[simp] lemma removed_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).removed active = ∅ := by
  ext e; simp [removed, exit]

lemma inserted_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).inserted active =
      (if active false then {s(x,P.start)} else ∅) ∪
      (if active true then {s(x,P.finish)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma inserted_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).inserted active = if active () then {s(x,A.far)} else ∅ := by
  ext e
  by_cases h : active () <;> simp [inserted, endpoint, Port, h]

lemma inserted_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).inserted active =
      (if active false then {s(x,A.far)} else ∅) ∪
      (if active true then {s(x,B.far)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma removed_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).removed active =
      (if active false then {s(x,A.near)} else ∅) ∪
      (if active true then {s(x,B.near)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [removed, exit, Port, Bool.exists_bool, h0, h1, or_comm]

end Frame

lemma replace_two_attachments {E : Type cycleUniverse17} (B : Set E) (e f a b : E)
    (he : e ∉ B) (hf : f ∉ B) (hne : e ≠ f) (p q : Prop) [Decidable p] [Decidable q] :
    ((B ∪ {e,f}) \ ((if p then {e} else ∅) ∪ (if q then {f} else ∅))) ∪
      ((if p then {a} else ∅) ∪ (if q then {b} else ∅)) =
      B ∪ {if p then a else e, if q then b else f} := by
  classical
  ext z
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp, hq, ↓reduceIte, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false] <;> aesop

namespace Frame
variable {V : Type cycleUniverse18} {G : SimpleGraph V} {x : V}

lemma modify_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.through A B hd).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.through A B hd).path.walk.edgeSet \ (Frame.through A B hd).removed active) ∪
        (Frame.through A B hd).inserted active := by
  have ha : active false → G.Adj x A.far := hadj false
  have hb : active true → G.Adj x B.far := hadj true
  let A' := A.orient (active false) ha
  let B' := B.orient (active true) hb
  have hd' : A'.walk.support.Disjoint B'.walk.support :=
    A.orient_disjoint B _ _ _ _ hd
  refine ⟨Piece.ofPath (A'.join B' hd'), ?_⟩
  have he : s(x,A.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hf : s(x,B.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hne : s(x,A.near) ≠ s(x,B.near) := fun h => A.near_ne B hd (star_inj.mp h)
  change (A'.join B' hd').walk.edgeSet = _
  rw [inserted_through, removed_through]
  change (A'.join B' hd').walk.edgeSet = ((A.join B hd).walk.edgeSet \ _) ∪ _
  rw [Arm.join_edges, Arm.join_edges]
  dsimp only [A', B']
  simp only [Arm.orient_edges, Arm.orient_near]
  have hh := (replace_two_attachments _ _ _ s(x,A.far) s(x,B.far) he hf hne
    (active false) (active true)).symm
  by_cases h0 : active false <;> by_cases h1 : active true
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simp [h0, h1]

lemma modify_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.tip A).endpoint p))
    (hnew : ∀ p, active p → s(x,(Frame.tip A).endpoint p) ∉
      (Frame.tip A).path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.tip A).path.walk.edgeSet \ (Frame.tip A).removed active) ∪
        (Frame.tip A).inserted active := by
  rw [removed_tip, inserted_tip, Set.sdiff_empty]
  by_cases ha : active ()
  · have haG : G.Adj x A.far := hadj () ha
    have he : s(A.far,x) ∉ A.tip.walk.edges := by
      intro he
      exact hnew () ha (Sym2.eq_swap ▸ he)
    let c : G.Walk A.far A.far := Walk.cons haG.symm A.tip.walk
    have hc : c.IsCycle := Path.cons_isCycle ⟨A.tip.walk,A.tip.isPath⟩ _ he
    refine ⟨Piece.ofCycle c hc, ?_⟩
    change c.edgeSet = _
    dsimp only [c, Arm.tip, path]
    simp only [Walk.edgeSet_cons, ha, ↓reduceIte]
    rw [Sym2.eq_swap]
    ext e
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  · refine ⟨Piece.ofPath A.tip, ?_⟩
    simp [Piece.ofPath, path, ha]

lemma modify_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.away P hx).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.away P hx).path.walk.edgeSet \ (Frame.away P hx).removed active) ∪
        (Frame.away P hx).inserted active := by
  rw [removed_away, inserted_away, Set.sdiff_empty]
  change ∃ Q : Piece G, Q.walk.edgeSet = P.walk.edgeSet ∪ _
  by_cases h0 : active false
  · have h0G : G.Adj x P.start := hadj false h0
    let q : G.Walk x P.finish := Walk.cons h0G P.walk
    have hq : q.IsPath := P.isPath.cons hx
    by_cases h1 : active true
    · have he : s(P.finish,x) ∉ q.edges := by
        intro he
        have hh := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
        have hp := P.positive
        simp only [q, Walk.length_cons] at hh
        omega
      have h1G : G.Adj x P.finish := hadj true h1
      let c : G.Walk P.finish P.finish := Walk.cons h1G.symm q
      have hc : c.IsCycle := Path.cons_isCycle ⟨q,hq⟩ _ he
      refine ⟨Piece.ofCycle c hc, ?_⟩
      change c.edgeSet = _
      simp only [c, q, Walk.edgeSet_cons, h0, h1, ↓reduceIte]
      rw [Sym2.eq_swap]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · let Q : PathPiece G := ⟨x, P.finish, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, h0, h1, ↓reduceIte, Set.union_empty]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
  · by_cases h1 : active true
    · have h1G : G.Adj x P.finish := hadj true h1
      let q : G.Walk x P.start := Walk.cons h1G P.walk.reverse
      have hq : q.IsPath := P.isPath.reverse.cons (by simpa using hx)
      let Q : PathPiece G := ⟨x, P.start, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, Walk.edgeSet_reverse, h0, h1, ↓reduceIte,
        Set.empty_union]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · refine ⟨Piece.ofPath P, ?_⟩
      simp [Piece.ofPath, h0, h1]

theorem modify (F : Frame G x) (active : F.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (F.endpoint p))
    (hnew : ∀ p, active p → F.exit p = none → s(x,F.endpoint p) ∉ F.path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet = (F.path.walk.edgeSet \ F.removed active) ∪
      F.inserted active := by
  cases F with
  | away P hx => exact modify_away P hx active hadj
  | through A B hd => exact modify_through A B hd active hadj
  | tip A => exact modify_tip A active hadj (fun p hp => hnew p hp rfl)

end Frame

theorem rewire_partition {E : Type cycleUniverse19} {I : Type cycleUniverse20} (old remove add : I → Set E) (fresh : Set E)
    (hsub : ∀ i, remove i ⊆ old i)
    (hold : Pairwise fun i j => Disjoint (old i) (old j))
    (hadd : Pairwise fun i j => Disjoint (add i) (add j))
    (hfresh : Disjoint fresh (⋃ i, old i))
    (hbalance : (⋃ i, add i) = (⋃ i, remove i) ∪ fresh) :
    Pairwise (fun i j => Disjoint ((old i \ remove i) ∪ add i)
      ((old j \ remove j) ∪ add j)) ∧
    (⋃ i, ((old i \ remove i) ∪ add i)) = (⋃ i, old i) ∪ fresh := by
  have hcross : ∀ i j, Disjoint (old i \ remove i) (add j) := by
    intro i j
    apply Set.disjoint_left.mpr
    rintro e ⟨hei, hnot⟩ hej
    have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
      rw [← hbalance]
      exact Set.mem_iUnion.mpr ⟨j, hej⟩
    rcases hh with hh | hh
    · obtain ⟨l, hel⟩ := Set.mem_iUnion.mp hh
      by_cases hil : i = l
      · subst l; exact hnot hel
      · exact Set.disjoint_left.mp (hold hil) hei (hsub l hel)
    · exact Set.disjoint_left.mp hfresh hh (Set.mem_iUnion.mpr ⟨i, hei⟩)
  constructor
  · intro i j hij
    exact Disjoint.union_left
      (Disjoint.union_right ((hold hij).mono Set.sdiff_subset Set.sdiff_subset) (hcross i j))
      (Disjoint.union_right (hcross j i).symm (hadd hij))
  · ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi.1⟩)
      · have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
          rw [← hbalance]
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        rcases hh with hh | hh
        · obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hh
          exact Or.inl (Set.mem_iUnion.mpr ⟨l, hsub l hl⟩)
        · exact Or.inr hh
    · rintro (he | he)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        by_cases hr : e ∈ remove i
        · have hh : e ∈ ⋃ l, add l := by
            rw [hbalance]
            exact Or.inl (Set.mem_iUnion.mpr ⟨i, hr⟩)
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
          exact Set.mem_iUnion.mpr ⟨j, Or.inr hj⟩
        · exact Set.mem_iUnion.mpr ⟨i, Or.inl ⟨hi, hr⟩⟩
      · have hh : e ∈ ⋃ l, add l := by rw [hbalance]; exact Or.inr he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨i, Or.inr hi⟩

inductive Centered {V : Type cycleUniverse21} (G : SimpleGraph V) (x : V) where
  | path (F : Frame G x)
  | cycle {v : V} (c : G.Walk v v) (hc : c.IsCycle)

namespace Centered
variable {V : Type cycleUniverse22} {G : SimpleGraph V} {x : V}

def piece : Centered G x → Piece G
  | .path F => .ofPath F.path
  | .cycle c hc => .ofCycle c hc

def Port : Centered G x → Type
  | .path F => F.Port
  | .cycle _ _ => Empty

def endpoint : (K : Centered G x) → K.Port → V
  | .path F, p => F.endpoint p
  | .cycle _ _, p => nomatch p

def exit : (K : Centered G x) → K.Port → Option V
  | .path F, p => F.exit p
  | .cycle _ _, p => nomatch p

def inserted (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ e = s(x,K.endpoint p)}

def removed (K : Centered G x) (active : K.Port → Prop) : Set (Sym2 V) :=
  {e | ∃ p, active p ∧ ∃ v, K.exit p = some v ∧ e = s(x,v)}

lemma exit_edge (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    s(x,v) ∈ K.piece.walk.edgeSet := by
  cases K with
  | path F => exact F.exit_edge p v h
  | cycle c hc => exact p.elim

lemma exit_adj (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    G.Adj x v := by
  exact G.mem_edgeSet.mp (K.piece.walk.edges_subset_edgeSet (K.exit_edge p v h))

lemma exit_none_all (K : Centered G x) (p : K.Port) (h : K.exit p = none) :
    ∀ q, K.exit q = none := by
  cases K with
  | cycle c hc => exact p.elim
  | path F =>
    cases F with
    | away P hx => exact fun _ => rfl
    | tip A => exact fun _ => rfl
    | through A B hd => cases p <;> cases h

lemma removed_subset (K : Centered G x) (active : K.Port → Prop) :
    K.removed active ⊆ K.piece.walk.edgeSet := by
  rintro e ⟨p, hp, v, hv, rfl⟩
  exact K.exit_edge p v hv

lemma modify (K : Centered G x) (active : K.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (K.endpoint p))
    (hnew : ∀ p, active p → K.exit p = none →
      s(x,K.endpoint p) ∉ K.piece.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      (K.piece.walk.edgeSet \ K.removed active) ∪ K.inserted active := by
  cases K with
  | path F => exact F.modify active hadj hnew
  | cycle c hc =>
    refine ⟨.ofCycle c hc, ?_⟩
    have hr : (Centered.cycle c hc).removed active = ∅ := by
      ext e; simp only [removed, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    have hi : (Centered.cycle c hc).inserted active = ∅ := by
      ext e; simp only [inserted, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    simp only [hr, hi, Set.sdiff_empty, Set.union_empty]
    rfl

end Centered

theorem restore_selected {V : Type cycleUniverse23} {I : Type cycleUniverse24} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (selected : Set (Σ i, (K i).Port))
    (hinj : Set.InjOn (fun z : Σ i, (K i).Port => (K z.1).endpoint z.2) selected)
    (hcov : ∀ v, G.Adj x v → ∃ z ∈ selected, (K z.1).endpoint z.2 = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let R : V → V → Prop := fun a b => ∃ z ∈ selected,
    (K z.1).endpoint z.2 = a ∧ (K z.1).exit z.2 = some b
  let active : (i : I) → (K i).Port → Prop := fun i p =>
    (⟨i,p⟩ : Σ j, (K j).Port) ∈ selected ∧ StarActive S R ((K i).endpoint p)
  have hactive_adj : ∀ v, StarActive S R v → G.Adj x v := by
    intro v hv
    exact starActive_subset (T := {v | G.Adj x v}) hS
      (by rintro a b ⟨z, _, _, hz⟩; exact (K z.1).exit_adj z.2 b hz) hv
  have hbalance : (⋃ i, (K i).inserted (active i)) =
      (⋃ i, (K i).removed (active i)) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
    ext e
    constructor
    · intro he
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp he
      rcases (starActive_iff.mp hp.2) with hs | ⟨w, hw, z, hz, hzw, hzv⟩
      · exact Or.inr ⟨_, hs, rfl⟩
      · exact Or.inl (Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzw.symm ▸ hw⟩,
          _, hzv, rfl⟩)
    · rintro (he | ⟨v, hv, rfl⟩)
      · obtain ⟨i, p, hp, v, hpv, rfl⟩ := Set.mem_iUnion.mp he
        have hv : StarActive S R v := starActive_step hp.2 ⟨⟨i,p⟩, hp.1, rfl, hpv⟩
        obtain ⟨z, hz, hzv⟩ := hcov v (hactive_adj v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ hv⟩, congrArg (s(x,·)) hzv.symm⟩
      · obtain ⟨z, hz, hzv⟩ := hcov v (hS v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ starActive_source hv⟩,
          congrArg (s(x,·)) hzv.symm⟩
  have hadd : Pairwise fun i j =>
      Disjoint ((K i).inserted (active i)) ((K j).inserted (active j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    have h : (⟨i,p⟩ : Σ l, (K l).Port) = ⟨j,q⟩ :=
      hinj hp.1 hq.1 (star_inj.mp (he.symm.trans hf))
    exact hij (congrArg Sigma.fst h)
  have hnew : ∀ i p, active i p → (K i).exit p = none →
      s(x,(K i).endpoint p) ∉ (K i).piece.walk.edgeSet := by
    intro i p hp hn he
    have ha : s(x,(K i).endpoint p) ∈ ⋃ j, (K j).inserted (active j) :=
      Set.mem_iUnion.mpr ⟨i, p, hp, rfl⟩
    rw [hbalance] at ha
    rcases ha with ha | ha
    · obtain ⟨j, q, hq, v, hqv, hev⟩ := Set.mem_iUnion.mp ha
      have hej : s(x,(K i).endpoint p) ∈ (K j).piece.walk.edgeSet :=
        hev ▸ (K j).exit_edge q v hqv
      have hij : i = j := by
        by_contra h; exact Set.disjoint_left.mp (hold h) he hej
      subst j
      rw [(K i).exit_none_all p hn q] at hqv
      cases hqv
    · exact Set.disjoint_left.mp hfresh ha (Set.mem_iUnion.mpr ⟨i, he⟩)
  choose Q hQ using fun i => (K i).modify (active i)
    (fun p hp => hactive_adj _ hp.2) (hnew i)
  have hh := rewire_partition (fun i => (K i).piece.walk.edgeSet)
    (fun i => (K i).removed (active i)) (fun i => (K i).inserted (active i))
    {e | ∃ v ∈ S, e = s(x,v)} (fun i => (K i).removed_subset _) hold hadd hfresh hbalance
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hQ] using hh.1
  · simpa only [hQ] using hh.2

theorem restore_star {V : Type cycleUniverse25} {I : Type cycleUniverse26} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (hcov : ∀ v, G.Adj x v → ∃ i p, (K i).endpoint p = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let T := {v // G.Adj x v}
  have hh : ∀ v : T, ∃ z : Σ i, (K i).Port, (K z.1).endpoint z.2 = v.val := by
    intro v
    obtain ⟨i,p,h⟩ := hcov v.val v.property
    exact ⟨⟨i,p⟩,h⟩
  choose f hf using hh
  apply restore_selected G x K S hS hold hfresh (Set.range f)
  · rintro z ⟨v,rfl⟩ w ⟨u,rfl⟩ he
    have hvu : v = u := Subtype.ext ((hf v).symm.trans (he.trans (hf u)))
    exact congrArg f hvu
  · intro v hv
    exact ⟨f ⟨v,hv⟩, ⟨⟨v,hv⟩, rfl⟩, hf ⟨v,hv⟩⟩

namespace Arm
variable {V : Type cycleUniverse27} {G : SimpleGraph V} {x b : V}

def fromWalk (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) : Arm G x :=
  match w with
  | .nil => False.elim (hn .nil)
  | @Walk.cons _ _ _ y _ h q =>
    ⟨y, b, h, q, (Walk.cons_isPath_iff h q).mp hp |>.1,
      (Walk.cons_isPath_iff h q).mp hp |>.2⟩

@[simp] lemma fromWalk_far (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).far = b := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_support (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).walk.support = w.support.tail := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl

@[simp] lemma fromWalk_tip_edges (w : G.Walk x b) (hp : w.IsPath) (hn : ¬w.Nil) :
    (fromWalk w hp hn).tip.walk.edgeSet = w.edgeSet := by
  cases w with
  | nil => exact (hn .nil).elim
  | cons h q => rfl
end Arm

lemma PathPiece.exists_frame {V : Type cycleUniverse28} {G : SimpleGraph V} (P : PathPiece G) (x : V) :
    ∃ F : Frame G x, F.path.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, (F.path.start = v ∨ F.path.finish = v) ↔ (P.start = v ∨ P.finish = v) := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨q,r,hq,hr,hqr⟩ := P.isPath.mem_support_iff_exists_append.mp hx
    have hp : (q.append r).IsPath := hqr ▸ P.isPath
    by_cases hqn : q.Nil
    · have hx : P.start = x := hqn.eq
      have hrn : ¬r.Nil := by
        intro hn; exact P.ends_ne (hx.trans hn.eq)
      let A := Arm.fromWalk r hr hrn
      refine ⟨.tip A, ?_, ?_⟩
      · change A.tip.walk.edgeSet = P.walk.edgeSet
        rw [Arm.fromWalk_tip_edges]
        rw [hqr, Walk.edgeSet_append]
        simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hqn]
      · intro v
        change (x = v ∨ A.far = v) ↔ _
        simp only [A, Arm.fromWalk_far, hx]
    · by_cases hrn : r.Nil
      · have hx : x = P.finish := hrn.eq
        have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        refine ⟨.tip A, ?_, ?_⟩
        · change A.tip.walk.edgeSet = P.walk.edgeSet
          rw [Arm.fromWalk_tip_edges, Walk.edgeSet_reverse]
          rw [hqr, Walk.edgeSet_append]
          simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hrn]
        · intro v
          change (x = v ∨ A.far = v) ↔ _
          simp only [A, Arm.fromWalk_far, hx, or_comm]
      · have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        let B := Arm.fromWalk r hr hrn
        have hd : A.walk.support.Disjoint B.walk.support := by
          rw [Arm.fromWalk_support, Arm.fromWalk_support]
          have hd := hp.disjoint_support_of_append hrn
          rw [Walk.support_tail_of_not_nil r hrn] at hd
          apply List.disjoint_left.mpr
          intro v hv hw
          exact List.disjoint_left.mp hd
            (by simpa using (List.mem_of_mem_tail hv : v ∈ q.reverse.support)) hw
        refine ⟨.through A B hd, ?_, ?_⟩
        · change ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).edgeSet = _
          rw [Walk.edgeSet_append, Walk.edgeSet_reverse]
          change A.tip.walk.edgeSet ∪ B.tip.walk.edgeSet = _
          rw [Arm.fromWalk_tip_edges, Arm.fromWalk_tip_edges, Walk.edgeSet_reverse,
            hqr, Walk.edgeSet_append]
        · intro v
          change (A.far = v ∨ B.far = v) ↔ _
          simp only [A, B, Arm.fromWalk_far]
  · exact ⟨.away P hx, rfl, fun _ => Iff.rfl⟩

namespace Piece
variable {V : Type cycleUniverse29} {G H : SimpleGraph V}

lemma isTrail (P : Piece G) : P.walk.IsTrail := by
  rcases P.simple with hp | ⟨h,hc⟩
  · exact hp.1.isTrail
  · exact (P.walk.isTrail_copy rfl h).mp hc.isTrail

def mapLe (h : H ≤ G) (P : Piece H) : Piece G := by
  rcases P with ⟨a,b,w,hs⟩
  refine ⟨a,b,w.mapLe h, ?_⟩
  rcases hs with hp | ⟨hb,hc⟩
  · exact Or.inl ⟨hp.1.mapLe h, by simpa using hp.2⟩
  · subst b
    exact Or.inr ⟨rfl, by simpa using hc.mapLe h⟩

@[simp] lemma mapLe_edges (h : H ≤ G) (P : Piece H) :
    (P.mapLe h).walk.edgeSet = P.walk.edgeSet := by
  cases P
  exact Walk.edgeSet_mapLe_eq_edgeSet _ _

@[simp] lemma mapLe_start (h : H ≤ G) (P : Piece H) : (P.mapLe h).start = P.start := by
  cases P; rfl
@[simp] lemma mapLe_finish (h : H ≤ G) (P : Piece H) : (P.mapLe h).finish = P.finish := by
  cases P; rfl

lemma exists_centered (P : Piece G) (x : V) :
    ∃ K : Centered G x, K.piece.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, P.start ≠ P.finish → (P.start = v ∨ P.finish = v) → v ≠ x →
        ∃ p, K.endpoint p = v := by
  rcases P with ⟨a,b,w,hs⟩
  rcases hs with hp | ⟨hb,hc⟩
  · let Q : PathPiece G := ⟨a,b,w,hp.1,hp.2⟩
    obtain ⟨F,he,hv⟩ := Q.exists_frame x
    refine ⟨.path F, he, ?_⟩
    intro v _ he hx
    exact (F.port_iff_endpoint v).mpr ⟨(hv v).mpr he, hx⟩
  · subst b
    refine ⟨.cycle w (by simpa using hc), rfl, ?_⟩
    exact fun _ hn => (hn rfl).elim
end Piece

theorem trail_partition_degree_sum {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse32} {I : Type cycleUniverse33} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

lemma endpoint_of_odd {V : Type cycleUniverse34} {I : Type cycleUniverse35} [Fintype V] [Fintype I]
    (H : SimpleGraph V) (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet)
    (v : V) (hv : Odd (H.degree v)) :
    ∃ i, (P i).start ≠ (P i).finish ∧ ((P i).start = v ∨ (P i).finish = v) := by
  classical
  have ho := (trail_partition_even_degree_iff H (fun i => (P i).walk)
    (fun i => (P i).isTrail) hd hc v).not.mp (Nat.not_even_iff_odd.mpr hv)
  have hp : 0 < (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card := by
    by_contra hn
    have hz : (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card = 0 := by omega
    exact ho (hz ▸ ⟨0, rfl⟩)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, (Finset.mem_filter.mp hi).2.1, by
    simpa only [eq_comm] using (Finset.mem_filter.mp hi).2.2⟩

theorem restore_partition {V : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V] [Fintype I]
    (G H : SimpleGraph V) (hHG : H ≤ G) (x : V) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hedges : G.edgeSet = H.edgeSet ∪ {e | ∃ v ∈ S, e = s(x,v)})
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} H.edgeSet)
    (hodd : ∀ v, G.Adj x v → Odd (H.degree v))
    (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  choose K hk hv using fun i => ((P i).mapLe hHG).exists_centered x
  have he : ∀ i, (K i).piece.walk.edgeSet = (P i).walk.edgeSet := by
    intro i; exact (hk i).trans ((P i).mapLe_edges hHG)
  have hKC : (⋃ i, (K i).piece.walk.edgeSet) = H.edgeSet := by simpa only [he] using hc
  obtain ⟨Q,hQ,hQC⟩ := restore_star G x K S hS
    (by simpa only [he] using hd) (by rwa [hKC]) (by
      intro v hxv
      obtain ⟨i, hi, hiv⟩ := endpoint_of_odd H P hd hc v (hodd v hxv)
      obtain ⟨p,hp⟩ := hv i v (by simpa using hi) (by simpa using hiv) hxv.ne.symm
      exact ⟨i,p,hp⟩)
  exact ⟨Q,hQ,by simpa only [hKC, ← hedges] using hQC⟩

def activeOrder {V : Type cycleUniverse38} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.support.toFinset.card

lemma activeOrder_mono {V : Type cycleUniverse39} [Fintype V] {G H : SimpleGraph V} (h : H ≤ G) :
    activeOrder H ≤ activeOrder G := by
  apply Finset.card_le_card
  intro v hv
  exact Set.mem_toFinset.mpr (SimpleGraph.support_mono h (Set.mem_toFinset.mp hv))

def HasPartition {V : Type cycleUniverse40} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Piece G),
    (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
    (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧ 2 * k ≤ activeOrder G

def evenStarVertices {V : Type cycleUniverse41} [Fintype V] (G : SimpleGraph V) (x : V) : Set V :=
  {y | G.Adj x y ∧ Even (G.degree y)}

def evenStarEdges {V : Type cycleUniverse42} [Fintype V] (G : SimpleGraph V) (x : V) : Set (Sym2 V) :=
  {e | ∃ y ∈ evenStarVertices G x, e = s(x,y)}

def deleteEvenStar {V : Type cycleUniverse43} [Fintype V] (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (evenStarEdges G x)

lemma evenStar_subset {V : Type cycleUniverse44} [Fintype V] (G : SimpleGraph V) (x : V) :
    evenStarEdges G x ⊆ G.edgeSet := by
  rintro e ⟨y,hy,rfl⟩; exact hy.1

lemma deleteEvenStar_neighbor_even {V : Type cycleUniverse45} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = (G.neighborFinset v).erase x := by
  classical
  ext w
  rw [Finset.mem_erase, (deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  constructor
  · rintro ⟨hvw, hn⟩
    refine ⟨?_,hvw⟩
    intro hw; subst w
    exact hn ⟨v,⟨hxv,he⟩, Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨hw,hvw⟩
    refine ⟨hvw, ?_⟩
    rintro ⟨y,_,h⟩
    rcases h with ⟨h,_⟩ | ⟨_,h⟩
    · exact hxv.ne h.symm
    · exact hw h

lemma deleteEvenStar_neighbor_odd {V : Type cycleUniverse46} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : ¬Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = G.neighborFinset v := by
  classical
  ext w
  rw [(deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
  rintro ⟨y,hy,h⟩
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  · exact hxv.ne h.symm
  · subst y; exact he hy.2

lemma deleteEvenStar_neighbor_degree {V : Type cycleUniverse47} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) : Odd ((deleteEvenStar G x).degree v) := by
  classical
  by_cases he : Even (G.degree v)
  · have hcard := Finset.card_erase_add_one (s := G.neighborFinset v)
      (a := x) (by simpa using hxv.symm)
    rw [← deleteEvenStar_neighbor_even G x v hxv he,
      G.card_neighborFinset_eq_degree, (deleteEvenStar G x).card_neighborFinset_eq_degree] at hcard
    obtain ⟨k,hk⟩ := he
    exact ⟨k-1, by omega⟩
  · rw [← (deleteEvenStar G x).card_neighborFinset_eq_degree v,
      deleteEvenStar_neighbor_odd G x v hxv he, G.card_neighborFinset_eq_degree]
    exact Nat.not_even_iff_odd.mp he

lemma deleteEvenStar_edges {V : Type cycleUniverse48} [Fintype V] (G : SimpleGraph V) (x : V) :
    G.edgeSet = (deleteEvenStar G x).edgeSet ∪ evenStarEdges G x := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges,
    Set.sdiff_union_of_subset (evenStar_subset G x)]

lemma deleteEvenStar_fresh {V : Type cycleUniverse49} [Fintype V] (G : SimpleGraph V) (x : V) :
    Disjoint (evenStarEdges G x) (deleteEvenStar G x).edgeSet := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges]
  exact Set.disjoint_sdiff_right

lemma deleteEvenStar_lt {V : Type cycleUniverse50} [Fintype V] (G : SimpleGraph V) (x y : V)
    (hxy : G.Adj x y) (he : Even (G.degree y)) :
    (deleteEvenStar G x).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro e he
    exact G.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono
      (show deleteEvenStar G x ≤ G from G.deleteEdges_le _)
      ((deleteEvenStar G x).mem_edgeFinset.mp he))
  · intro h
    have hh : s(x,y) ∈ (deleteEvenStar G x).edgeFinset := h.symm ▸ G.mem_edgeFinset.mpr hxy
    have hf : s(x,y) ∈ evenStarEdges G x := ⟨y,⟨hxy,he⟩,rfl⟩
    exact Set.disjoint_left.mp (deleteEvenStar_fresh G x) hf (SimpleGraph.mem_edgeFinset.mp hh)

theorem even_vertex_step {V : Type cycleUniverse51} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph V, H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (hpos : ∃ y, 0 < G.degree y ∧ Even (G.degree y)) : HasPartition G := by
  classical
  obtain ⟨y,hy,he⟩ := hpos
  obtain ⟨x,hxy⟩ := (G.degree_pos_iff_exists_adj y).mp hy
  let H := deleteEvenStar G x
  obtain ⟨k,P,hd,hc,hk⟩ := hIH H (deleteEvenStar_lt G x y hxy.symm he)
  obtain ⟨Q,hQ,hQC⟩ := restore_partition G H (G.deleteEdges_le _) x
    (evenStarVertices G x) (fun _ h => h.1) (deleteEvenStar_edges G x)
    (deleteEvenStar_fresh G x) (deleteEvenStar_neighbor_degree G x) P hd hc
  exact ⟨k,Q,hQ,hQC,hk.trans (activeOrder_mono (G.deleteEdges_le _))⟩

lemma single_edge_piece {V : Type cycleUniverse52} (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ P : Piece G, P.walk.edgeSet = {e} := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    let P : PathPiece G := ⟨a,b,Walk.cons hab Walk.nil,
      (Walk.IsPath.nil).cons (by simpa using hab.ne), by simp⟩
    exact ⟨.ofPath P, by simp [Piece.ofPath, P]⟩

lemma partition_single_edges {V : Type cycleUniverse53} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Fin G.edgeFinset.card → Piece G,
      (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = G.edgeSet := by
  classical
  choose P hP using fun e : G.edgeSet => single_edge_piece G e.val e.property
  let e : G.edgeSet ≃ Fin G.edgeFinset.card := (Fintype.equivFin G.edgeSet).trans
    (finCongr (G.card_edgeSet))
  refine ⟨fun i => P (e.symm i), ?_, ?_⟩
  · intro i j hij
    rw [hP, hP]
    exact Set.disjoint_singleton.mpr (fun h => hij (e.symm.injective (Subtype.ext h)))
  · ext z
    simp only [Set.mem_iUnion,hP,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩; exact (e.symm i).property
    · intro hz
      exact ⟨e ⟨z,hz⟩, by simp⟩

lemma matching_partition {V : Type cycleUniverse54} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 1) : HasPartition G := by
  classical
  obtain ⟨P,hd,hc⟩ := partition_single_edges G
  refine ⟨_,P,hd,hc,?_⟩
  rw [← G.sum_degrees_support_eq_twice_card_edges]
  simpa [activeOrder] using Finset.sum_le_sum (s := G.support.toFinset)
    (f := fun v => G.degree v) (g := fun _ => 1) (fun v _ => hdeg v)

def subdivision {V : Type cycleUniverse55} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | some a, some b => G.Adj a b ∧ s(a,b) ≠ s(x,y)
    | none, some b => b = x ∨ b = y
    | some a, none => a = x ∨ a = y
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by
    intro a h
    cases a
    · exact h
    · exact G.irrefl h.1⟩

@[simp] lemma subdivision_some {V : Type cycleUniverse56} (G : SimpleGraph V) (x y a b : V) :
    (subdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := Iff.rfl
@[simp] lemma subdivision_none_some {V : Type cycleUniverse57} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj none (some a) ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_some_none {V : Type cycleUniverse58} (G : SimpleGraph V) (x y a : V) :
    (subdivision G x y).Adj (some a) none ↔ a = x ∨ a = y := Iff.rfl
@[simp] lemma subdivision_none_none {V : Type cycleUniverse59} (G : SimpleGraph V) (x y : V) :
    ¬(subdivision G x y).Adj none none := id

def halfSubdivision {V : Type cycleUniverse60} (G : SimpleGraph V) (x y : V) : SimpleGraph (Option V) :=
  (subdivision G x y).deleteEdges {s(none,some x)}

@[simp] lemma half_some {V : Type cycleUniverse61} (G : SimpleGraph V) (x y a b : V) :
    (halfSubdivision G x y).Adj (some a) (some b) ↔ G.Adj a b ∧ s(a,b) ≠ s(x,y) := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp []

@[simp] lemma half_none_some {V : Type cycleUniverse62} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj none (some a) ↔ a = y := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp only [subdivision_none_some, Set.mem_singleton_iff, star_inj, Option.some.injEq]
  aesop

@[simp] lemma half_some_none {V : Type cycleUniverse63} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj (some a) none ↔ a = y := by
  rw [(halfSubdivision G x y).adj_comm, half_none_some G x y a hxy]

lemma option_degree_some {V : Type cycleUniverse64} [Fintype V] (K : SimpleGraph (Option V)) (v : V) :
    K.degree (some v) = (Finset.univ.filter (fun u : V => K.Adj (some v) (some u))).card +
      if K.Adj (some v) none then 1 else 0 := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  omega

lemma option_degree_none {V : Type cycleUniverse65} [Fintype V] (K : SimpleGraph (Option V)) :
    K.degree none = (Finset.univ.filter (fun u : V => K.Adj none (some u))).card := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp

lemma subdivision_old_neighbors {V : Type cycleUniverse66} [Fintype V] (G : SimpleGraph V)
    (x y v : V) :
    (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) =
      if v = x then (G.neighborFinset v).erase y else
      if v = y then (G.neighborFinset v).erase x else G.neighborFinset v := by
  classical
  ext u
  by_cases hx : v = x
  · subst v
    simp [eq_comm, and_comm]
    aesop
  · by_cases hy : v = y
    · subst v
      simp [hx,  eq_comm, and_comm]
      tauto
    · simp [hx, hy]

lemma subdivision_degree {V : Type cycleUniverse67} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (subdivision G x y).degree (some v) = G.degree v := by
  classical
  rw [option_degree_some, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy]

lemma subdivision_degree_none {V : Type cycleUniverse68} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (subdivision G x y).degree none = 2 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (subdivision G x y).Adj none (some u)) =
      {x,y} := by ext u; simp
  rw [he]
  simp [hxy.ne]

lemma half_degree {V : Type cycleUniverse69} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).degree (some v) + (if v = x then 1 else 0) = G.degree v := by
  classical
  rw [option_degree_some]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj (some v) (some u)) =
      (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) := by
    ext u; simp
  rw [he, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa [hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx, hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy,half_some_none G x y v hxy.ne]

lemma half_degree_none {V : Type cycleUniverse70} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (halfSubdivision G x y).degree none = 1 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj none (some u)) =
      {y} := by ext u; simp [half_none_some G x y u hxy.ne]
  rw [he]
  simp

lemma subdivision_edge_count {V : Type cycleUniverse71} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (subdivision G x y).edgeFinset.card = G.edgeFinset.card + 1 := by
  classical
  have hd := (subdivision G x y).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, subdivision_degree_none G x y hxy] at hd
  simp_rw [subdivision_degree G x y _ hxy] at hd
  rw [G.sum_degrees_eq_twice_card_edges] at hd
  omega

lemma half_edge_count {V : Type cycleUniverse72} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).edgeFinset.card = G.edgeFinset.card := by
  classical
  have he : (halfSubdivision G x y).edgeFinset =
      (subdivision G x y).edgeFinset.erase s(none,some x) := by
    ext e
    rw [(halfSubdivision G x y).mem_edgeFinset, Finset.mem_erase,
      (subdivision G x y).mem_edgeFinset]
    simp [halfSubdivision, SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [he, Finset.card_erase_of_mem, subdivision_edge_count G x y hxy]
  · omega
  · exact (subdivision G x y).mem_edgeFinset.mpr (Or.inl rfl)

lemma subdivision_activeOrder {V : Type cycleUniverse73} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    activeOrder (subdivision G x y) = activeOrder G + 1 := by
  classical
  have he : (subdivision G x y).support.toFinset =
      insert none (G.support.toFinset.image Option.some) := by
    ext v
    cases v with
    | none => simp [← SimpleGraph.degree_pos_iff_mem_support, subdivision_degree_none G x y hxy]
    | some v =>
      simp only [Set.mem_toFinset, Finset.mem_insert, Option.some_ne_none, Finset.mem_image,
        Option.some.injEq, false_or, exists_eq_right]
      rw [← (subdivision G x y).degree_pos_iff_mem_support,
        subdivision_degree G x y v hxy, G.degree_pos_iff_mem_support]
  dsimp [activeOrder]
  rw [he, Finset.card_insert_of_notMem, Finset.card_image_of_injective]
  · exact Option.some_injective V
  · simp

lemma suppress_path {V : Type cycleUniverse74} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    {a b : V} (p : (subdivision G x y).Walk (some a) (some b)) (hp : p.IsPath) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.support = p.support.filterMap id ∧
      ∀ e : Sym2 V, e ∈ q.edgeSet ↔
        e.map Option.some ∈ p.edgeSet ∨ (e = s(x,y) ∧ s(none,some x) ∈ p.edgeSet) := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    cases p with
    | nil =>
      refine ⟨.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | @cons _ v _ h p =>
      have ht : p.IsPath := hp.of_cons
      have ha : some a ∉ p.support := (Walk.cons_isPath_iff _ _ |>.mp hp).2
      cases v with
      | some c =>
        obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht rfl
        have hac : G.Adj a c := (subdivision_some G x y a c).mp h |>.1
        refine ⟨.cons hac q, hq.cons ?_, ?_, ?_⟩
        · intro ha'
          apply ha
          rw [hqs] at ha'
          simpa using ha'
        · simp [hqs]
        · intro e
          have hinj : Function.Injective (Sym2.map (Option.some : V → Option V)) :=
            Sym2.map.injective (Option.some_injective V)
          have he : e.map Option.some = s(some a,some c) ↔ e = s(a,c) :=
            by simpa only [Sym2.map_mk] using (hinj.eq_iff (a := e) (b := s(a,c)))
          have hnedge : s(none,some x) ≠ s(some a,some c) := by simp []
          simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he, hnedge, false_or, hqe]
          tauto
      | none =>
        cases p with
        | @cons _ v _ h' p =>
          cases v with
          | none => exact (h'.ne rfl).elim
          | some c =>
            have hac : a ≠ c := by
              intro he
              apply ha
              simp [he]
            have hae : a = x ∨ a = y := (subdivision_some_none G x y a).mp h
            have hce : c = x ∨ c = y := (subdivision_none_some G x y c).mp h'
            have hexy : s(a,c) = s(x,y) := by
              rcases hae with rfl | rfl <;> rcases hce with rfl | rfl
              · exact (hac rfl).elim
              · rfl
              · exact Sym2.eq_swap
              · exact (hac rfl).elim
            have hacG : G.Adj a c := G.mem_edgeSet.mp (hexy.symm ▸ hxy)
            obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht.of_cons rfl
            refine ⟨.cons hacG q, hq.cons ?_, ?_, ?_⟩
            · intro ha'
              apply ha
              have hh : some a ∈ p.support := by rw [hqs] at ha'; simpa using ha'
              simp [hh]
            · simp [hqs]
            · intro e
              have he1 : e.map Option.some ≠ s(some a,none) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have he2 : e.map Option.some ≠ s(none,some c) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have hn : s(none,some x) = s(some a,none) ∨
                  s(none,some x) = s(none,some c) := by
                rcases hae with rfl | hay
                · exact Or.inl Sym2.eq_swap
                · rcases hce with rfl | hcy
                  · exact Or.inr rfl
                  · exact (hac (hay.trans hcy.symm)).elim
              simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he1, he2, false_or,
                hexy, hqe]
              tauto

lemma tight_partition_endpoints {V : Type cycleUniverse75} {I : Type cycleUniverse76} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (P : I → Piece G) (S : Finset V)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v)) (hk : 2 * Fintype.card I ≤ S.card) :
    ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ∈ S ∧ (P i).finish ∈ S := by
  classical
  let endpoint : I × Bool → V := fun z => if z.2 then (P z.1).start else (P z.1).finish
  have he : ∀ v : S, ∃ z : I × Bool, endpoint z = v := by
    intro v
    obtain ⟨i,_, h | h⟩ := endpoint_of_odd G P hd hc v (ho v v.property)
    · exact ⟨(i,true),h⟩
    · exact ⟨(i,false),h⟩
  choose pick hpick using he
  have hinj : Function.Injective pick := by
    intro v w hvw
    apply Subtype.ext
    exact (hpick v).symm.trans ((congrArg endpoint hvw).trans (hpick w))
  have hsurj : Function.Surjective pick := by
    by_contra hn
    have hh := Fintype.card_lt_of_injective_not_surjective pick hinj hn
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] at hh
    omega
  have hendinj : Function.Injective endpoint := by
    intro z t heq
    obtain ⟨v,rfl⟩ := hsurj z
    obtain ⟨w,rfl⟩ := hsurj t
    have hvw : v = w := Subtype.ext (by simpa only [hpick] using heq)
    exact congrArg pick hvw
  have hmem : ∀ z, endpoint z ∈ S := by
    intro z
    obtain ⟨v,rfl⟩ := hsurj z
    rw [hpick]
    exact v.property
  intro i
  refine ⟨?_, hmem (i,true), hmem (i,false)⟩
  intro heq
  have hh := hendinj (show endpoint (i,true) = endpoint (i,false) from heq)
  have := congrArg Prod.snd hh
  contradiction

def subdivisionRepresentative {V : Type cycleUniverse77} (x y : V) (e : Sym2 V) : Sym2 (Option V) :=
  if e = s(x,y) then s(none,some x) else e.map Option.some

lemma representative_mem {V : Type cycleUniverse78} (G : SimpleGraph V) (x y : V) (_hxy : G.Adj x y)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    subdivisionRepresentative x y e ∈ (subdivision G x y).edgeSet := by
  classical
  by_cases h : e = s(x,y)
  · simp [subdivisionRepresentative, h]
  · rw [subdivisionRepresentative, if_neg h]
    induction e using Sym2.ind with
    | _ a b => exact ⟨he,h⟩

lemma suppress_piece {V : Type cycleUniverse79} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : Piece (subdivision G x y)) (hne : P.start ≠ P.finish)
    (ha : P.start ≠ none) (hb : P.finish ≠ none) :
    ∃ Q : Piece G, ∀ e, e ∈ Q.walk.edgeSet ↔ subdivisionRepresentative x y e ∈ P.walk.edgeSet := by
  classical
  rcases P with ⟨a,b,p,hp⟩
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b =>
      have hab : a ≠ b := fun h => hne (congrArg some h)
      have hpath : p.IsPath := by
        rcases hp with h | ⟨h,_⟩
        · exact h.1
        · exact (hne h.symm).elim
      obtain ⟨q,hq,_,hqe⟩ := suppress_path G x y hxy p hpath
      have hpos : 0 < q.length := by
        by_contra hn
        exact hab (Walk.eq_of_length_eq_zero (by omega : q.length = 0))
      refine ⟨.ofPath ⟨a,b,q,hq,hpos⟩, ?_⟩
      intro e
      change e ∈ q.edgeSet ↔ _
      rw [hqe]
      by_cases he : e = s(x,y)
      · subst e
        have hn : (s(x,y) : Sym2 V).map some ∉ p.edgeSet := by
          intro h
          have hh := p.edges_subset_edgeSet h
          exact hh.2 rfl
        simp only [subdivisionRepresentative, ite_true, hn, false_or, true_and]
      · simp [subdivisionRepresentative, he]

lemma suppress_partition {V : Type cycleUniverse80} {I : Type cycleUniverse81} [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : I → Piece (subdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (subdivision G x y).edgeSet)
    (hp : ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ≠ none ∧ (P i).finish ≠ none) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  classical
  choose Q hQ using fun i => suppress_piece G x y hxy (P i) (hp i).1 (hp i).2.1 (hp i).2.2
  refine ⟨Q, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun e hei hej =>
      Set.disjoint_left.mp (hd hij) ((hQ i e).mp hei) ((hQ j e).mp hej)
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => (Q i).walk.edges_subset_edgeSet
    · intro e he
      have hrep := representative_mem G x y hxy e he
      rw [← hc] at hrep
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hrep
      exact Set.mem_iUnion.mpr ⟨i,(hQ i e).mpr hi⟩

lemma even_activeOrder {V : Type cycleUniverse82} [Fintype V] (G : SimpleGraph V)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) : Even (activeOrder G) := by
  classical
  have he : G.support.toFinset = Finset.univ.filter (fun v => Odd (G.degree v)) := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      ← G.degree_pos_iff_mem_support]
    refine ⟨ho v, ?_⟩
    rintro ⟨k,hk⟩
    omega
  simpa only [activeOrder, he] using G.even_card_odd_degree_vertices

lemma half_restore {V : Type cycleUniverse83} {I : Type cycleUniverse84} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v))
    (P : I → Piece (halfSubdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (halfSubdivision G x y).edgeSet) :
    ∃ Q : I → Piece (subdivision G x y),
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = (subdivision G x y).edgeSet := by
  classical
  have he : {e : Sym2 (Option V) | ∃ v ∈ ({none} : Set (Option V)), e = s(some x,v)} =
      {s(none,some x)} := by
    ext e
    simp [Sym2.eq_swap]
  apply restore_partition (subdivision G x y) (halfSubdivision G x y)
    ((subdivision G x y).deleteEdges_le _) (some x) {none}
    (by intro v hv; rcases hv with rfl; exact Or.inl rfl) ?_ ?_ ?_ P hd hc
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    symm
    apply Set.sdiff_union_of_subset
    intro e he
    rcases he with rfl
    exact Or.inl rfl
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_right
  · intro v hv
    cases v with
    | none => rw [half_degree_none G x y hxy]; exact ⟨0,rfl⟩
    | some v =>
      have hxv : G.Adj x v := hv.1
      have hh := half_degree G x y v hxy
      rw [if_neg hxv.ne.symm, add_zero] at hh
      rw [hh]
      exact ho v ((G.degree_pos_iff_exists_adj v).mpr ⟨x,hxv.symm⟩)

theorem odd_vertex_step {V : Type cycleUniverse85} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph (Option V), H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) (x : V) (hx : 3 ≤ G.degree x) :
    HasPartition G := by
  classical
  obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hp : ∃ v, 0 < (halfSubdivision G x y).degree v ∧
      Even ((halfSubdivision G x y).degree v) := by
    refine ⟨some x, ?_, ?_⟩
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      omega
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      obtain ⟨k,hk⟩ := ho x (by omega)
      exact ⟨k,by omega⟩
  obtain ⟨k,P,hd,hc,hk⟩ := even_vertex_step (halfSubdivision G x y)
    (fun H hh => hIH H (by rwa [half_edge_count G x y hxy] at hh)) hp
  have hbound : 2 * k ≤ activeOrder G + 1 := by
    have hm := activeOrder_mono ((subdivision G x y).deleteEdges_le {s(none,some x)})
    rw [subdivision_activeOrder G x y hxy] at hm
    exact hk.trans hm
  have hk' : 2 * k ≤ activeOrder G := by
    obtain ⟨a,ha⟩ := even_activeOrder G ho
    omega
  obtain ⟨Q,hQ,hQC⟩ := half_restore G x y hxy ho P hd hc
  let S := G.support.toFinset.image Option.some
  have hScard : S.card = activeOrder G := by
    exact Finset.card_image_of_injective _ (Option.some_injective V)
  have hSodd : ∀ v ∈ S, Odd ((subdivision G x y).degree v) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [subdivision_degree G x y w hxy]
    exact ho w ((G.degree_pos_iff_mem_support w).mpr (Set.mem_toFinset.mp hw))
  have hends := tight_partition_endpoints (subdivision G x y) Q S hQ hQC hSodd
    (by simpa only [Fintype.card_fin, hScard] using hk')
  have hnon : ∀ i, (Q i).start ≠ (Q i).finish ∧
      (Q i).start ≠ none ∧ (Q i).finish ≠ none := by
    intro i
    refine ⟨(hends i).1, ?_, ?_⟩
    · intro h
      have hh := (hends i).2.1
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
    · intro h
      have hh := (hends i).2.2
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
  obtain ⟨R,hR,hRC⟩ := suppress_partition G x y hxy Q hQ hQC hnon
  exact ⟨k,R,hR,hRC,hk'⟩

theorem path_cycle_partition {V : Type u} [Fintype V] (G : SimpleGraph V) : HasPartition G := by
  classical
  suffices ∀ (n : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
      H.edgeFinset.card = n → HasPartition H by
    exact this G.edgeFinset.card V G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ H hcount
    by_cases he : ∃ v, 0 < H.degree v ∧ Even (H.degree v)
    · exact even_vertex_step H (fun K hk => ih K.edgeFinset.card (by omega) W K rfl) he
    · have ho : ∀ v, 0 < H.degree v → Odd (H.degree v) := by
        intro v hv
        exact Nat.not_even_iff_odd.mp (fun hev => he ⟨v,hv,hev⟩)
      by_cases hm : ∀ v, H.degree v ≤ 1
      · exact matching_partition H hm
      · push Not at hm
        obtain ⟨x,hx⟩ := hm
        have hx3 : 3 ≤ H.degree x := by
          obtain ⟨k,hk⟩ := ho x (by omega)
          omega
        exact odd_vertex_step H
          (fun K hk => ih K.edgeFinset.card (by omega) (Option W) K rfl) ho x hx3

end
end ErdosGallai.Lovasz

end
end
end

end OAI



/-
The cycle switching operation is encoded by up to two arrows per cycle. If the cycle
visits both centers, each arrow represents swapping the two attachments of a path
between the centers. A cycle visiting one center can transfer either or both of its
attachments to the other center. A distinguished sink represents the free attachment.
The outgoing minus incoming balance records the change in edge multiplicities.
-/

open SimpleGraph

namespace OMA.Erdos184Fan

section Routing

variable {A E : Type*} [DecidableEq A] [DecidableEq E]

/-- The arrows are indexed by `E`, so parallel arrows have independent capacities. -/
private def along (src dst : E → A) (F : Finset E) (u v : A) : Prop :=
  ∃ e ∈ F, src e = u ∧ dst e = v

/-- A directed trail uses each arrow at most once. -/
private inductive Trail (src dst : E → A) : A → A → Finset E → Prop
  | nil (u : A) : Trail src dst u u ∅
  | cons (e : E) {u : A} {T : Finset E} (he : e ∉ T)
      (p : Trail src dst (dst e) u T) : Trail src dst (src e) u (insert e T)

omit [DecidableEq A] in
private theorem Trail.suffix {src dst : E → A} {u v : A} {T : Finset E}
    (p : Trail src dst u v T) {e : E} (he : e ∈ T) :
    ∃ R ⊆ T, Trail src dst (src e) v R := by
  induction p with
  | nil => simp at he
  | @cons f u T hf p ih =>
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨insert e T, fun _ ha => ha, .cons e hf p⟩
    · obtain ⟨R, hR, q⟩ := ih he
      exact ⟨R, fun _ ha => Finset.mem_insert_of_mem (hR ha), q⟩

omit [DecidableEq A] in
private theorem exists_trail_of_reachable {src dst : E → A} {F : Finset E} {u v : A}
    (p : Relation.ReflTransGen (along src dst F) u v) :
    ∃ T ⊆ F, Trail src dst u v T := by
  induction p using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨∅, Finset.empty_subset _, .nil _⟩
  | @head u w huw _ ih =>
    obtain ⟨e, he, rfl, rfl⟩ := huw
    obtain ⟨T, hT, q⟩ := ih
    by_cases heT : e ∈ T
    · obtain ⟨R, hR, r⟩ := q.suffix heT
      exact ⟨R, hR.trans hT, r⟩
    · exact ⟨insert e T, Finset.insert_subset he hT, .cons e heT q⟩

private def mark (u v : A) : ℤ := if u = v then 1 else 0

/-- The outgoing count minus the incoming count at a vertex. -/
def divergence (src dst : E → A) (F : Finset E) (v : A) : ℤ :=
  ∑ e ∈ F, (mark (src e) v - mark (dst e) v)

private theorem Trail.divergence_eq {src dst : E → A} {u v : A} {T : Finset E}
    (p : Trail src dst u v T) (x : A) :
    divergence src dst T x = mark u x - mark v x := by
  induction p with
  | nil => simp [divergence]
  | cons e he _ ih =>
    simp only [divergence, Finset.sum_insert he] at ih ⊢
    omega

private theorem divergence_union {src dst : E → A} {T R : Finset E}
    (h : Disjoint T R) (v : A) :
    divergence src dst (T ∪ R) v = divergence src dst T v + divergence src dst R v :=
  Finset.sum_union h

omit [DecidableEq E] in
private theorem reachable_sink_of_divergence_pos [Fintype A]
    {src dst : E → A} {F : Finset E} {v sink : A}
    (hnonneg : ∀ w, w ≠ sink → 0 ≤ divergence src dst F w)
    (hpos : 0 < divergence src dst F v) :
    Relation.ReflTransGen (along src dst F) v sink := by
  classical
  by_contra hno
  let R : Finset A := Finset.univ.filter (Relation.ReflTransGen (along src dst F) v)
  have hvR : v ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  have hsinkR : sink ∉ R := fun h => hno (Finset.mem_filter.mp h).2
  have hclosed (e : E) (he : e ∈ F) (hsrc : src e ∈ R) : dst e ∈ R :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hsrc).2.tail ⟨e, he, rfl, rfl⟩⟩
  have hsumpos : 0 < ∑ w ∈ R, divergence src dst F w :=
    hpos.trans_le (Finset.single_le_sum
      (fun w hw => hnonneg w (fun h => hsinkR (h ▸ hw))) hvR)
  have hsumle : (∑ w ∈ R, divergence src dst F w) ≤ 0 := by
    unfold divergence
    rw [Finset.sum_comm]
    refine Finset.sum_nonpos fun e he => ?_
    simp only [Finset.sum_sub_distrib, mark, Finset.sum_ite_eq]
    by_cases hsrc : src e ∈ R
    · simp [hsrc, hclosed e he hsrc]
    · by_cases hdst : dst e ∈ R <;> simp [hsrc, hdst]
  omega

/-- Let every vertex other than `sink` have nonnegative divergence. For any requested
nonnegative divergence bounded by the original divergence, there is a subset of arrows
realizing all requests simultaneously. -/
theorem exists_subfamily_of_divergence [Fintype A] (src dst : E → A) (F : Finset E) (sink : A)
    (demand : A → ℕ) (h : ∀ v, v ≠ sink → (demand v : ℤ) ≤ divergence src dst F v) :
    ∃ T ⊆ F, ∀ v, v ≠ sink → divergence src dst T v = (demand v : ℤ) := by
  classical
  have aux : ∀ (n : ℕ) (F : Finset E), F.card = n → ∀ (demand : A → ℕ),
      (∀ v, v ≠ sink → (demand v : ℤ) ≤ divergence src dst F v) →
      ∃ T ⊆ F, ∀ v, v ≠ sink → divergence src dst T v = (demand v : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hcard demand hF
      by_cases hd : ∃ x, x ≠ sink ∧ 0 < demand x
      · obtain ⟨x, hxs, hx⟩ := hd
        have hnonneg v (hv : v ≠ sink) : 0 ≤ divergence src dst F v :=
          (Int.natCast_nonneg _).trans (hF v hv)
        have hxpos : 0 < divergence src dst F x :=
          (Int.natCast_pos.mpr hx).trans_le (hF x hxs)
        obtain ⟨P, hP, p⟩ := exists_trail_of_reachable
          (reachable_sink_of_divergence_pos hnonneg hxpos)
        let R := F \ P
        have hPR : Disjoint P R := Finset.disjoint_sdiff
        have hpartition : P ∪ R = F := Finset.union_sdiff_of_subset hP
        have hsum v : divergence src dst F v = divergence src dst P v + divergence src dst R v := by
          rw [← hpartition, divergence_union hPR]
        have hPne : P.Nonempty := by
          by_contra! hn
          have hp := p.divergence_eq x
          rw [hn] at hp
          simp [divergence, mark, Ne.symm hxs] at hp
        have hRcard : R.card < n := by
          rw [← hcard, ← hpartition, Finset.card_union_of_disjoint hPR]
          have := Finset.card_pos.mpr hPne
          omega
        let d v := if v = x then demand v - 1 else demand v
        have hR v (hv : v ≠ sink) : (d v : ℤ) ≤ divergence src dst R v := by
          have hf := hF v hv
          rw [hsum v, p.divergence_eq v] at hf
          by_cases hvx : v = x
          · subst v
            simp [d, mark, Ne.symm hxs] at hf ⊢
            omega
          · simp [d, mark, hvx, Ne.symm hvx, Ne.symm hv] at hf ⊢
            exact hf
        obtain ⟨U, hU, hu⟩ := ih R.card hRcard R rfl d hR
        refine ⟨P ∪ U, Finset.union_subset hP (hU.trans Finset.sdiff_subset), ?_⟩
        intro v hv
        rw [divergence_union (hPR.mono_right hU), p.divergence_eq v, hu v hv]
        by_cases hvx : v = x
        · subst v
          simp [d, mark, Ne.symm hxs]
          omega
        · simp [d, mark, hvx, Ne.symm hvx, Ne.symm hv]
      · refine ⟨∅, Finset.empty_subset _, fun v hv => ?_⟩
        have hz : demand v = 0 := Nat.eq_zero_of_not_pos (fun hp => hd ⟨v, hv, hp⟩)
        simp [divergence, hz]
  exact aux F.card F rfl demand h

end Routing

section Switching

variable {V : Type*} {G : SimpleGraph V} {x y a b : V}

private theorem walk_frame {u v : V} (p : G.Walk u v) (hp : 2 ≤ p.length) :
    ∃ (a b : V) (r : G.Walk a b) (hua : G.Adj u a) (hbv : G.Adj b v),
      p = (r.concat hbv).cons hua := by
  cases p with
  | nil => simp at hp
  | @cons _ a _ hua q =>
    have hq : ¬ q.Nil := by
      rw [Walk.not_nil_iff_lt_length]
      simp only [Walk.length_cons] at hp
      omega
    exact ⟨a, q.penultimate, q.dropLast, hua, q.adj_penultimate hq,
      congrArg (Walk.cons hua) (Walk.concat_dropLast _).symm⟩

private theorem inner_of_framed_path {u v : V} (r : G.Walk a b)
    (hua : G.Adj u a) (hbv : G.Adj b v) (hp : ((r.concat hbv).cons hua).IsPath) :
    r.IsPath ∧ u ∉ r.support ∧ v ∉ r.support := by
  obtain ⟨hq, hu⟩ := (Walk.cons_isPath_iff hua _).mp hp
  obtain ⟨hr, hv⟩ := (Walk.concat_isPath_iff hbv).mp hq
  exact ⟨hr, fun h => hu (r.support_subset_support_concat hbv h), hv⟩

private theorem inner_of_framed_cycle {u : V} (r : G.Walk a b)
    (hua : G.Adj u a) (hbu : G.Adj b u) (hp : ((r.concat hbu).cons hua).IsCycle) :
    r.IsPath ∧ u ∉ r.support ∧ 0 < r.length := by
  obtain ⟨hq, hlen⟩ := Walk.isCycle_iff_isPath_tail_and_le_length.mp hp
  have hq' : (r.concat hbu).IsPath := by simpa using hq
  obtain ⟨hr, hv⟩ := (Walk.concat_isPath_iff hbu).mp hq'
  simp only [Walk.length_cons, Walk.length_concat] at hlen
  exact ⟨hr, hv, by omega⟩

private theorem framed_path_flip {u v : V} (r : G.Walk a b)
    (hua : G.Adj u a) (hbv : G.Adj b v) (hub : G.Adj u b) (hav : G.Adj a v)
    (hp : ((r.concat hbv).cons hua).IsPath) (huv : u ≠ v) :
    ((r.reverse.concat hav).cons hub).IsPath := by
  obtain ⟨hr, hu, hv⟩ := inner_of_framed_path r hua hbv hp
  refine (hr.reverse.concat (by simpa using hv) hav).cons ?_
  simp [Walk.support_concat, Walk.support_reverse, hu, huv]

private theorem framed_cycle {u : V} (r : G.Walk a b) (hr : r.IsPath)
    (hu : u ∉ r.support) (hpos : 0 < r.length) (hua : G.Adj u a) (hbu : G.Adj b u) :
    ((r.concat hbu).cons hua).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simpa using hr.concat hu hbu
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

private theorem framed_cycle_via_edge {u v : V} (r : G.Walk a b) (hr : r.IsPath)
    (hu : u ∉ r.support) (hv : v ∉ r.support)
    (huv : G.Adj u v) (hva : G.Adj v a) (hbu : G.Adj b u) (hpos : 0 < r.length) :
    (((r.concat hbu).cons hva).cons huv).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · refine (hr.concat hu hbu).cons ?_
    simp [Walk.support_concat, hv, huv.ne.symm]
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

private def edgeCount [DecidableEq V] (s : List (Sym2 V)) (e : Sym2 V) : ℤ := s.count e

private def edgeMark [DecidableEq V] (e : Sym2 V) (u v : V) : ℤ :=
  if s(u,v) = e then 1 else 0

private theorem frame_edgeCount [DecidableEq V] {u v : V} (r : G.Walk a b)
    (hua : G.Adj u a) (hbv : G.Adj b v) (e : Sym2 V) :
    edgeCount ((r.concat hbv).cons hua).edges e =
      edgeCount r.edges e + edgeMark e u a + edgeMark e v b := by
  simp only [edgeCount, edgeMark, Walk.edges_cons, Walk.edges_concat, List.count_cons,
    Int.natCast_add]
  rw [show s(b,v) = s(v,b) from Sym2.eq_swap]
  by_cases h₁ : s(u,a) = e <;> by_cases h₂ : s(v,b) = e <;> simp_all

private theorem inner_count_eq_zero [DecidableEq V] (r : G.Walk a b)
    (hu : x ∉ r.support) (v : V) : edgeCount r.edges s(x,v) = 0 := by
  have h : s(x,v) ∉ r.edges := fun he => hu (r.fst_mem_support_of_mem_edges he)
  simp [edgeCount, List.count_eq_zero_of_not_mem h]

private def moveCount [DecidableEq V] (x y : V) (a b : Option V) (e : Sym2 V) : ℤ :=
  a.elim 0 (fun v => edgeMark e y v - edgeMark e x v) +
    b.elim 0 (fun v => edgeMark e x v - edgeMark e y v)

private theorem mark_own [DecidableEq V] (x v z : V) :
    edgeMark s(x,z) x v = mark (some v) (some z) := by
  by_cases h : v = z
  · simp [edgeMark, mark, h]
  · have h' : ¬ (x = z ∧ v = x) := fun ⟨h₁, h₂⟩ => h (h₂.trans h₁)
    simp [edgeMark, mark, h, h']

private theorem mark_other [DecidableEq V] {u v w z : V} (huv : u ≠ v)
    (hwu : w ≠ u) : edgeMark s(u,z) v w = 0 := by
  simp [edgeMark, Ne.symm huv, hwu]

private theorem flip_framed_path [DecidableEq V] (r : G.Walk a b)
    (hxa : G.Adj x a) (hby : G.Adj b y) (hxb : G.Adj x b) (hay : G.Adj a y)
    (hp : ((r.concat hby).cons hxa).IsPath) (hxy : x ≠ y) :
    ∃ q : G.Walk x y, q.IsPath ∧ q.length = ((r.concat hby).cons hxa).length ∧
      q.support.Perm ((r.concat hby).cons hxa).support ∧
      ∀ e, edgeCount q.edges e = edgeCount ((r.concat hby).cons hxa).edges e +
        moveCount x y (some a) (some b) e := by
  refine ⟨(r.reverse.concat hay).cons hxb,
    framed_path_flip r hxa hby hxb hay hp hxy, by simp, ?_, ?_⟩
  · simpa [Walk.support_cons, Walk.support_concat, Walk.support_reverse] using
      ((List.reverse_perm r.support).append_right [y]).cons x
  · intro e
    rw [frame_edgeCount, frame_edgeCount]
    have hrc : edgeCount r.reverse.edges e = edgeCount r.edges e := by
      simp [edgeCount, Walk.edges_reverse]
    simp only [moveCount, Option.elim_some, hrc]
    omega

private theorem edgeCount_append [DecidableEq V] (s t : List (Sym2 V)) (e : Sym2 V) :
    edgeCount (s ++ t) e = edgeCount s e + edgeCount t e := by
  simp [edgeCount, List.count_append]

private theorem edgeCount_reverse [DecidableEq V] {u v : V} (p : G.Walk u v) (e : Sym2 V) :
    edgeCount p.reverse.edges e = edgeCount p.edges e := by simp [edgeCount, Walk.edges_reverse]

private structure ArcPlan [DecidableEq V] (p : G.Walk x y) where
  src : Option V
  dst : Option V
  src_adj : ∀ z, src = some z → G.Adj x z
  dst_adj : ∀ z, dst = some z → G.Adj y z
  src_ne : src ≠ some y
  dst_ne : dst ≠ some x
  balance : ∀ z, z ≠ x → z ≠ y →
    edgeCount p.edges s(x,z) - edgeCount p.edges s(y,z) = mark src (some z) - mark dst (some z)
  modify : ∀ chosen : Bool,
    (∀ z, src = some z → chosen = true → G.Adj y z) →
    (∀ z, dst = some z → chosen = true → G.Adj x z) →
    ∃ q : G.Walk x y, q.IsPath ∧ q.length = p.length ∧ q.support.Perm p.support ∧
      ∀ e, edgeCount q.edges e = edgeCount p.edges e +
        (if chosen then moveCount x y src dst e else 0)

private theorem arc_plan [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath) (hxy : x ≠ y) :
    Nonempty (ArcPlan p) := by
  by_cases hlen : 2 ≤ p.length
  · obtain ⟨a, b, r, hxa, hby, rfl⟩ := walk_frame p hlen
    obtain ⟨_, hx, hy⟩ := inner_of_framed_path r hxa hby hp
    have hya' : a ≠ y := fun h => hy (h ▸ r.start_mem_support)
    have hxb' : b ≠ x := fun h => hx (h ▸ r.end_mem_support)
    refine ⟨⟨some a, some b, fun z hz => Option.some.inj hz ▸ hxa,
      fun z hz => Option.some.inj hz ▸ hby.symm, by simpa using hya', by simpa using hxb', ?_, ?_⟩⟩
    · intro z _ _
      rw [frame_edgeCount, frame_edgeCount, inner_count_eq_zero r hx, inner_count_eq_zero r hy,
        mark_own, mark_own, mark_other hxy (fun h => hx (h ▸ r.end_mem_support)),
        mark_other hxy.symm (fun h => hy (h ▸ r.start_mem_support))]
      simp
    · intro chosen hs hd
      cases chosen
      · exact ⟨_, hp, rfl, List.Perm.refl _, by simp⟩
      · simpa using flip_framed_path r hxa hby (hd _ rfl rfl) (hs _ rfl rfl).symm hp hxy
  · have hlen' : p.length = 1 := by
      have := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hxy : ¬p.Nil)
      omega
    have hsingle : p.edges = [s(x,y)] := by
      cases p with
      | nil => simp at hlen'
      | cons h q =>
        have hz : q.length = 0 := by simpa using hlen'
        rcases Walk.length_eq_zero_iff.mp hz with ⟨⟩
        rfl
    refine ⟨⟨none, none, by simp, by simp, by simp, by simp, ?_, ?_⟩⟩
    · intro z hzx hzy
      have hxz : s(x,y) ≠ s(x,z) := by simp [Ne.symm hzy, hxy.symm]
      have hyz : s(x,y) ≠ s(y,z) := by simp [hxy, Ne.symm hzx]
      simp [hsingle, edgeCount, hxz, hyz, mark]
    · intro chosen _ _
      exact ⟨_, hp, rfl, List.Perm.refl _, by simp [moveCount]⟩

private theorem tail_perm {u v : V} {p q : G.Walk u v} (h : p.support.Perm q.support) :
    p.support.tail.Perm q.support.tail := by
  have heq (r : G.Walk u v) : r.support = u :: r.support.tail := by cases r <;> rfl
  rw [heq p, heq q] at h
  exact h.cons_inv

private structure CyclePlan [DecidableEq V] (G : SimpleGraph V) (x y : V)
    (old : List (Sym2 V)) where
  src : Fin 2 → Option V
  dst : Fin 2 → Option V
  src_adj : ∀ i z, src i = some z → G.Adj x z
  dst_adj : ∀ i z, dst i = some z → G.Adj y z
  src_ne : ∀ i, src i ≠ some y
  dst_ne : ∀ i, dst i ≠ some x
  balance : ∀ z, z ≠ x → z ≠ y → edgeCount old s(x,z) - edgeCount old s(y,z) =
    ∑ i : Fin 2, (mark (src i) (some z) - mark (dst i) (some z))
  modify : ∀ chosen : Fin 2 → Bool,
    (∀ i z, src i = some z → chosen i = true → G.Adj y z) →
    (∀ i z, dst i = some z → chosen i = true → G.Adj x z) →
    ∃ (u : V) (q : G.Walk u u), q.IsCycle ∧ ∀ e, e ≠ s(x,y) →
      edgeCount q.edges e = edgeCount old e +
        ∑ i : Fin 2, (if chosen i then moveCount x y (src i) (dst i) e else 0)

private theorem two_center_cycle_plan [DecidableEq V] (p : G.Walk x y) (q : G.Walk y x)
    (hpq : (p.append q).IsCycle) (hxy : x ≠ y) :
    Nonempty (CyclePlan G x y (p.append q).edges) := by
  have hp0 : ¬p.Nil := Walk.not_nil_of_ne hxy
  have hq0 : ¬q.Nil := Walk.not_nil_of_ne hxy.symm
  have hp := hpq.isPath_of_append_left hq0
  have hq := hpq.isPath_of_append_right hp0
  obtain ⟨P⟩ := arc_plan p hp hxy
  obtain ⟨Q⟩ := arc_plan q.reverse hq.reverse hxy
  let src : Fin 2 → Option V := ![P.src, Q.src]
  let dst : Fin 2 → Option V := ![P.dst, Q.dst]
  refine ⟨⟨src, dst, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    fin_cases i
    · exact P.src_adj
    · exact Q.src_adj
  · intro i
    fin_cases i
    · exact P.dst_adj
    · exact Q.dst_adj
  · intro i
    fin_cases i
    · exact P.src_ne
    · exact Q.src_ne
  · intro i
    fin_cases i
    · exact P.dst_ne
    · exact Q.dst_ne
  · intro z hzx hzy
    have hP := P.balance z hzx hzy
    have hQ := Q.balance z hzx hzy
    simp only [edgeCount_reverse] at hQ
    simp only [Walk.edges_append, edgeCount_append, Fin.sum_univ_two, src, dst,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · intro chosen hs hd
    obtain ⟨p', hp', hlp, hsp, hep⟩ := P.modify (chosen 0) (hs 0) (hd 0)
    obtain ⟨q', hq', hlq, hsq, heq⟩ := Q.modify (chosen 1) (hs 1) (hd 1)
    have hsq' : q'.reverse.support.Perm q.support := by
      rw [Walk.support_reverse] at hsq ⊢
      exact (List.reverse_perm _).trans (hsq.trans (List.reverse_perm _))
    have hsplit := hpq.support_nodup
    rw [Walk.tail_support_append, List.nodup_append'] at hsplit
    have hsep : p'.support.tail.Disjoint q'.reverse.support.tail :=
      (tail_perm hsp).disjoint_left.mpr ((tail_perm hsq').disjoint_right.mpr hsplit.2.2)
    have hlen : 1 < p'.length ∨ 1 < q'.reverse.length := by
      have h3 := hpq.three_le_length
      simp only [Walk.length_append] at h3
      simp only [Walk.length_reverse, hlp, hlq]
      omega
    refine ⟨x, p'.append q'.reverse, hp'.isCycle_append hq'.reverse hsep hlen, ?_⟩
    intro e _
    have hP := hep e
    have hQ := heq e
    simp only [edgeCount_reverse] at hQ
    simp only [Walk.edges_append, edgeCount_append, edgeCount_reverse, Fin.sum_univ_two, src, dst,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    omega

private theorem via_edge_edgeCount [DecidableEq V] (r : G.Walk a b)
    (hxy : G.Adj x y) (hya : G.Adj y a) (hbx : G.Adj b x) (e : Sym2 V)
    (he : e ≠ s(x,y)) : edgeCount (((r.concat hbx).cons hya).cons hxy).edges e =
      edgeCount r.edges e + edgeMark e y a + edgeMark e x b := by
  rw [← frame_edgeCount r hya hbx]
  simp [edgeCount, Walk.edges_cons, List.count_cons, Ne.symm he]

private theorem one_center_cycle_plan [DecidableEq V] (p : G.Walk x x) (hp : p.IsCycle)
    (hxy : G.Adj x y) (hy : y ∉ p.support) : Nonempty (CyclePlan G x y p.edges) := by
  have hlen := hp.three_le_length
  obtain ⟨a, b, r, hxa, hbx, rfl⟩ := walk_frame p (by omega)
  obtain ⟨hr, hx, hrpos⟩ := inner_of_framed_cycle r hxa hbx hp
  have hyr : y ∉ r.support := fun h => hy (by
    simp [Walk.support_cons, Walk.support_concat, h])
  have hay : a ≠ y := fun h => hyr (h ▸ r.start_mem_support)
  have hby : b ≠ y := fun h => hyr (h ▸ r.end_mem_support)
  have hrc (e) := edgeCount_reverse r e
  let src : Fin 2 → Option V := ![some a, some b]
  let dst : Fin 2 → Option V := fun _ => none
  refine ⟨⟨src, dst, ?_, by simp [dst], ?_, by simp [dst], ?_, ?_⟩⟩
  · intro i z hz
    fin_cases i
    · exact Option.some.inj hz ▸ hxa
    · exact Option.some.inj hz ▸ hbx.symm
  · intro i
    fin_cases i
    · exact fun h => hay (Option.some.inj h)
    · exact fun h => hby (Option.some.inj h)
  · intro z _ _
    rw [frame_edgeCount, frame_edgeCount, inner_count_eq_zero r hx, inner_count_eq_zero r hyr,
      mark_own, mark_own, mark_other hxy.ne.symm hay, mark_other hxy.ne.symm hby]
    simp only [Fin.sum_univ_two, src, dst, Matrix.cons_val_zero, Matrix.cons_val_one,
      mark]
    simp
  · intro chosen hs _
    have hxa' (h : chosen 0 = true) : G.Adj y a := hs 0 a rfl h
    have hxb' (h : chosen 1 = true) : G.Adj y b := hs 1 b rfl h
    cases h0 : chosen 0 <;> cases h1 : chosen 1
    · refine ⟨x, _, hp, fun e _ => ?_⟩
      simp [Fin.sum_univ_two, src, dst, h0, h1]
    · refine ⟨x, ((r.reverse.concat hxa.symm).cons (hxb' h1)).cons hxy,
        framed_cycle_via_edge r.reverse hr.reverse (by simpa using hx) (by simpa using hyr)
          hxy (hxb' h1) hxa.symm (by simpa using hrpos), ?_⟩
      intro e he
      rw [via_edge_edgeCount _ _ _ _ _ he, frame_edgeCount, hrc]
      simp [Fin.sum_univ_two, src, dst, h0, h1, moveCount]
      omega
    · refine ⟨x, ((r.concat hbx).cons (hxa' h0)).cons hxy,
        framed_cycle_via_edge r hr hx hyr hxy (hxa' h0) hbx hrpos, ?_⟩
      intro e he
      rw [via_edge_edgeCount _ _ _ _ _ he, frame_edgeCount]
      simp [Fin.sum_univ_two, src, dst, h0, h1, moveCount]
      omega
    · refine ⟨y, (r.concat (hxb' h1).symm).cons (hxa' h0),
        framed_cycle r hr hyr hrpos (hxa' h0) (hxb' h1).symm, ?_⟩
      intro e _
      rw [frame_edgeCount, frame_edgeCount]
      simp [Fin.sum_univ_two, src, dst, h0, h1, moveCount]
      omega

private def CyclePlan.swap [DecidableEq V] {old : List (Sym2 V)} (P : CyclePlan G x y old) :
    CyclePlan G y x old where
  src := P.dst
  dst := P.src
  src_adj := P.dst_adj
  dst_adj := P.src_adj
  src_ne := P.dst_ne
  dst_ne := P.src_ne
  balance z hzY hzX := by
    have hb := P.balance z hzX hzY
    simp only [Fin.sum_univ_two] at hb ⊢
    omega
  modify chosen hs hd := by
    obtain ⟨u, q, hq, h⟩ := P.modify chosen hd hs
    refine ⟨u, q, hq, fun e he => ?_⟩
    have hex : e ≠ s(x,y) := by simpa only [Sym2.eq_swap] using he
    have hm := h e hex
    simpa only [moveCount, add_comm] using hm

private theorem cycle_plan [DecidableEq V] (hxy : G.Adj x y) {u : V} (p : G.Walk u u)
    (hp : p.IsCycle) : Nonempty (CyclePlan G x y p.edges) := by
  by_cases hx : x ∈ p.support
  · let r := p.rotate x hx
    have hrc : r.IsCycle := hp.rotate hx
    have he := (p.rotate_edges x hx).perm
    have hc (e : Sym2 V) : edgeCount r.edges e = edgeCount p.edges e := by
      unfold edgeCount
      exact_mod_cast he.count_eq e
    by_cases hyr : y ∈ r.support
    · let l := r.takeUntil y hyr
      let q := r.dropUntil y hyr
      have hlq : l.append q = r := r.take_spec hyr
      obtain ⟨P⟩ := two_center_cycle_plan l q (hlq.symm ▸ hrc) hxy.ne
      have hh (e : Sym2 V) : edgeCount (l.append q).edges e = edgeCount p.edges e := by
        rw [hlq, hc]
      exact ⟨⟨P.src, P.dst, P.src_adj, P.dst_adj, P.src_ne, P.dst_ne,
        fun z hzX hzY => by simpa only [hh] using P.balance z hzX hzY,
        fun b hs hd => by simpa only [hh] using P.modify b hs hd⟩⟩
    · obtain ⟨P⟩ := one_center_cycle_plan r hrc hxy hyr
      exact ⟨⟨P.src, P.dst, P.src_adj, P.dst_adj, P.src_ne, P.dst_ne,
        fun z hzX hzY => by simpa only [hc] using P.balance z hzX hzY,
        fun b hs hd => by simpa only [hc] using P.modify b hs hd⟩⟩
  · by_cases hy : y ∈ p.support
    · let r := p.rotate y hy
      have hxr : x ∉ r.support := fun h => hx ((p.mem_support_rotate_iff y hy).mp h)
      have he := (p.rotate_edges y hy).perm
      have hc (e : Sym2 V) : edgeCount r.edges e = edgeCount p.edges e := by
        unfold edgeCount
        exact_mod_cast he.count_eq e
      obtain ⟨P'⟩ := one_center_cycle_plan r (hp.rotate hy) hxy.symm hxr
      let P := P'.swap
      exact ⟨⟨P.src, P.dst, P.src_adj, P.dst_adj, P.src_ne, P.dst_ne,
        fun z hzX hzY => by simpa only [hc] using P.balance z hzX hzY,
        fun b hs hd => by simpa only [hc] using P.modify b hs hd⟩⟩
    · refine ⟨⟨fun _ => none, fun _ => none, by simp, by simp, by simp, by simp, ?_, ?_⟩⟩
      · intro z _ _
        rw [inner_count_eq_zero p hx, inner_count_eq_zero p hy]
        simp [mark]
      · intro b _ _
        exact ⟨u, p, hp, fun e _ => by simp [moveCount]⟩

private theorem moveCount_y [DecidableEq V] (hxy : x ≠ y) (z : V) {s t : Option V}
    (hs : s ≠ some y) (ht : t ≠ some y) :
    moveCount x y s t s(y,z) = mark s (some z) - mark t (some z) := by
  have key (v : V) (hv : v ≠ y) : edgeMark s(y,z) x v = 0 := mark_other hxy.symm hv
  cases s <;> cases t <;> simp_all [moveCount, mark_own, mark, sub_eq_add_neg]

private theorem moveCount_x [DecidableEq V] (hxy : x ≠ y) (z : V) {s t : Option V}
    (hs : s ≠ some x) (ht : t ≠ some x) :
    moveCount x y s t s(x,z) = -(mark s (some z) - mark t (some z)) := by
  have hm := moveCount_y hxy.symm z ht hs
  have he : moveCount x y s t s(x,z) = moveCount y x t s s(x,z) := by
    simp only [moveCount, add_comm]
  rw [he, hm]
  omega

private theorem moveCount_other [DecidableEq V] (u v : Option V) {e : Sym2 V}
    (hx : x ∉ e) (hy : y ∉ e) : moveCount x y u v e = 0 := by
  have keyX (z : V) : s(x,z) ≠ e := fun h => hx (h ▸ by simp)
  have keyY (z : V) : s(y,z) ≠ e := fun h => hy (h ▸ by simp)
  cases u <;> cases v <;> simp_all [moveCount, edgeMark]

/-- Count appearances of an edge in an indexed cycle family. -/
def occ [DecidableEq V] {k : ℕ} (C : Fin k → Finset (Sym2 V)) (e : Sym2 V) : ℕ :=
  (Finset.univ.filter fun i => e ∈ C i).card

private theorem occ_eq_edgeCounts [DecidableEq V] {k : ℕ} (C : Fin k → Finset (Sym2 V))
    (l : Fin k → List (Sym2 V)) (hn : ∀ i, (l i).Nodup) (hl : ∀ i, C i = (l i).toFinset)
    (e : Sym2 V) : (occ C e : ℤ) = ∑ i, edgeCount (l i) e := by
  unfold occ
  rw [← Finset.sum_boole (R := ℤ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases he : e ∈ l i
  · simp [hl, he, edgeCount, List.count_eq_one_of_mem (hn i) he]
  · simp [hl, he, edgeCount, List.count_eq_zero_of_not_mem he]

/-- Transfer cycle incidences from `x` to an adjacent vertex `y`, retaining the family size.
The transfer may change the number of copies of `xy`. -/
theorem switch_cycles [Fintype V] [DecidableEq V] (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (dom : ∀ z : V, z ≠ x → z ≠ y → G.Adj y z → G.Adj x z)
    {k : ℕ} (C : Fin k → Finset (Sym2 V))
    (hC : ∀ i, ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ C i = p.edges.toFinset)
    (d : V → ℕ) (hd : ∀ z : V, z ≠ x → z ≠ y → d z + occ C s(y,z) ≤ occ C s(x,z))
    (hdAdj : ∀ z : V, z ≠ x → z ≠ y → 0 < d z → G.Adj y z) :
    ∃ D : Fin k → Finset (Sym2 V),
      (∀ i, ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ D i = p.edges.toFinset) ∧
      (∀ z : V, z ≠ x → z ≠ y → occ D s(y,z) = occ C s(y,z) + d z ∧
        occ D s(x,z) + d z = occ C s(x,z)) ∧
      (∀ e : Sym2 V, x ∉ e → y ∉ e → occ D e = occ C e) := by
  classical
  choose u p hp hcp using hC
  let P (i : Fin k) := Classical.choice (cycle_plan hxy (p i) (hp i))
  let A := Fin k × Fin 2
  let src (a : A) := (P a.1).src a.2
  let dst (a : A) := (P a.1).dst a.2
  have hsA (a : A) (z : V) (h : src a = some z) : G.Adj x z := (P a.1).src_adj a.2 z h
  have htA (a : A) (z : V) (h : dst a = some z) : G.Adj y z := (P a.1).dst_adj a.2 z h
  have hsX (a : A) : src a ≠ some x := fun h => (hsA a x h).ne rfl
  have htY (a : A) : dst a ≠ some y := fun h => (htA a y h).ne rfl
  have hsY (a : A) : src a ≠ some y := (P a.1).src_ne a.2
  have htX (a : A) : dst a ≠ some x := (P a.1).dst_ne a.2
  have hbefore := occ_eq_edgeCounts C (fun i => (p i).edges) (fun i => (hp i).edges_nodup) hcp
  let demand (v : Option V) : ℕ := v.elim 0 (fun z => if z = x ∨ z = y then 0 else d z)
  have hdiv (z : V) (hzX : z ≠ x) (hzY : z ≠ y) :
      divergence src dst Finset.univ (some z) = (occ C s(x,z) : ℤ) - occ C s(y,z) := by
    unfold divergence
    rw [Fintype.sum_prod_type, hbefore, hbefore, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => ((P i).balance z hzX hzY).symm
  have hbound (v : Option V) (hv : v ≠ none) :
      (demand v : ℤ) ≤ divergence src dst Finset.univ v := by
    cases v with
    | none => exact (hv rfl).elim
    | some z =>
      by_cases hzX : z = x
      · subst z
        simp [demand, divergence, mark, hsX, htX]
      by_cases hzY : z = y
      · subst z
        simp [demand, divergence, mark, hsY, htY]
      rw [hdiv z hzX hzY]
      have hc := hd z hzX hzY
      simp [demand, hzX, hzY]
      omega
  obtain ⟨T, _, hT⟩ := exists_subfamily_of_divergence src dst Finset.univ none demand hbound
  have hselectedSrc (i : Fin k) (j : Fin 2) (z : V) (hs : src (i,j) = some z)
      (hm : (i,j) ∈ T) : G.Adj y z := by
    by_contra hz
    have hzX : z ≠ x := fun h => hsX (i,j) (h ▸ hs)
    have hzY : z ≠ y := fun h => hsY (i,j) (h ▸ hs)
    have hzd : d z = 0 := Nat.eq_zero_of_not_pos fun h => hz (hdAdj z hzX hzY h)
    have ht (a : A) : dst a ≠ some z := fun h => hz (htA a z h)
    have hTz := hT (some z) (by simp)
    have hsum : (0 : ℤ) = ∑ a ∈ T, mark (src a) (some z) := by
      simpa [divergence, mark, ht, demand, hzX, hzY, hzd] using hTz.symm
    have hge := Finset.single_le_sum
      (f := fun a => mark (src a) (some z)) (fun a _ => by unfold mark; split <;> omega) hm
    rw [← hsum] at hge
    simp [mark, hs] at hge
  have hselectedDst (i : Fin k) (j : Fin 2) (z : V) (hs : dst (i,j) = some z) :
      G.Adj x z := dom z (fun h => htX (i,j) (h ▸ hs)) (fun h => htY (i,j) (h ▸ hs))
        (htA (i,j) z hs)
  let select (i : Fin k) (j : Fin 2) := decide ((i,j) ∈ T)
  have hlocal (i : Fin k) : ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧
      ∀ e, e ≠ s(x,y) → edgeCount q.edges e = edgeCount (p i).edges e +
        ∑ j : Fin 2, (if select i j then moveCount x y (src (i,j)) (dst (i,j)) e else 0) :=
    (P i).modify (select i)
      (fun j z hs hm => hselectedSrc i j z hs (of_decide_eq_true hm))
      (fun j z hs _ => hselectedDst i j z hs)
  choose v q hq hdelta using hlocal
  let D (i : Fin k) := (q i).edges.toFinset
  have hafter := occ_eq_edgeCounts D (fun i => (q i).edges) (fun i => (hq i).edges_nodup) (fun _ => rfl)
  have hchange (e : Sym2 V) (he : e ≠ s(x,y)) :
      (occ D e : ℤ) = occ C e + ∑ a ∈ T, moveCount x y (src a) (dst a) e := by
    rw [hbefore, hafter]
    simp_rw [fun i => hdelta i e he, Finset.sum_add_distrib]
    congr 1
    let w (a : A) := moveCount x y (src a) (dst a) e
    calc
      _ = ∑ a : A, if a ∈ T then w a else 0 := by
        rw [Fintype.sum_prod_type]
        simp [select, w]
      _ = _ := by rw [← Finset.sum_filter]; simp [w]
  refine ⟨D, fun i => ⟨v i, q i, hq i, rfl⟩, ?_, ?_⟩
  · intro z hzX hzY
    have hY : s(y,z) ≠ s(x,y) := by simp [hxy.ne.symm, hzX]
    have hX : s(x,z) ≠ s(x,y) := by simp [hxy.ne, hzY]
    have hTz := hT (some z) (by simp)
    simp [demand, hzX, hzY] at hTz
    have hy' := hchange s(y,z) hY
    have hx' := hchange s(x,z) hX
    simp_rw [fun a => moveCount_y hxy.ne z (hsY a) (htY a)] at hy'
    simp_rw [fun a => moveCount_x hxy.ne z (hsX a) (htX a), Finset.sum_neg_distrib] at hx'
    change (occ D s(y,z) : ℤ) = occ C s(y,z) + divergence src dst T (some z) at hy'
    change (occ D s(x,z) : ℤ) = occ C s(x,z) + -divergence src dst T (some z) at hx'
    omega
  · intro e heX heY
    have hne : e ≠ s(x,y) := fun h => heX (h ▸ by simp)
    have hm := hchange e hne
    simp_rw [fun a => moveCount_other (src a) (dst a) heX heY, Finset.sum_const_zero] at hm
    omega

end Switching

end OMA.Erdos184Fan



/- The graph-side change of state for a rooted edge switch. -/

namespace OMA.Erdos184FanAlt

open SimpleGraph
open scoped Classical

variable {V : Type*}

/-- The simple graph having exactly the edges from `x` to the other vertices in `Z`. -/
def starEdges (x : V) (Z : Set V) : SimpleGraph V where
  Adj u v := (u = x ∧ v ∈ Z ∧ v ≠ x) ∨ (v = x ∧ u ∈ Z ∧ u ≠ x)
  symm := ⟨by intro u v h; exact or_comm.mp h⟩
  loopless := ⟨by intro u h; rcases h with h | h <;> exact h.2.2 h.1⟩

@[simp] theorem starEdges_adj {x u v : V} {Z : Set V} :
    (starEdges x Z).Adj u v ↔ (u = x ∧ v ∈ Z ∧ v ≠ x) ∨
      (v = x ∧ u ∈ Z ∧ u ≠ x) := Iff.rfl

theorem neighborSet_starEdges_center (x : V) {Z : Set V} (hx : x ∉ Z) :
    (starEdges x Z).neighborSet x = Z := by
  ext z
  change (starEdges x Z).Adj x z ↔ z ∈ Z
  simp only [starEdges_adj, true_and, ne_eq, not_true_eq_false, and_false, or_false]
  exact ⟨And.left, fun hz => ⟨hz, fun hzx => hx (hzx ▸ hz)⟩⟩

theorem neighborSet_starEdges_other {x u : V} (hu : u ≠ x) (Z : Set V) :
    (starEdges x Z).neighborSet u = if u ∈ Z then {x} else ∅ := by
  classical
  ext z
  by_cases hz : u ∈ Z <;>
    simp [hz, hu, SimpleGraph.mem_neighborSet]

/-- Move the `y`-edges of `Z` to `x`. -/
def moveStar (G : SimpleGraph V) (x y : V) (Z : Set V) : SimpleGraph V :=
  (G \ starEdges y Z) ⊔ starEdges x Z

@[simp] theorem moveStar_adj {G : SimpleGraph V} {x y u v : V} {Z : Set V} :
    (moveStar G x y Z).Adj u v ↔
      (G.Adj u v ∧ ¬ (starEdges y Z).Adj u v) ∨ (starEdges x Z).Adj u v := Iff.rfl

theorem moveStar_mono {A B : SimpleGraph V} (h : B ≤ A) (x y : V) (Z : Set V) :
    moveStar B x y Z ≤ moveStar A x y Z := by
  intro u v huv
  rw [moveStar_adj] at huv ⊢
  exact huv.imp (fun h' => ⟨h h'.1, h'.2⟩) id

theorem moveStar_retains_root_edge {G : SimpleGraph V} {x y : V} {Z : Set V}
    (hxy : G.Adj x y) (hx : x ∉ Z) : (moveStar G x y Z).Adj x y := by
  simp [hxy, hx, hxy.ne]

theorem neighborSet_moveStar_root {G : SimpleGraph V} {x y : V} {Z : Set V}
    (hxy : x ≠ y) (hx : x ∉ Z) :
    (moveStar G x y Z).neighborSet x = G.neighborSet x ∪ Z := by
  classical
  rw [moveStar, neighborSet_sup, neighborSet_sdiff, neighborSet_starEdges_other hxy,
    if_neg hx, Set.sdiff_empty, neighborSet_starEdges_center x hx]

theorem neighborSet_moveStar_source {G : SimpleGraph V} {x y : V} {Z : Set V}
    (hxy : x ≠ y) (hy : y ∉ Z) :
    (moveStar G x y Z).neighborSet y = G.neighborSet y \ Z := by
  classical
  rw [moveStar, neighborSet_sup, neighborSet_sdiff, neighborSet_starEdges_center y hy,
    neighborSet_starEdges_other hxy.symm, if_neg hy, Set.union_empty]

theorem neighborSet_moveStar_other {G : SimpleGraph V} {x y u : V} {Z : Set V}
    (hux : u ≠ x) (huy : u ≠ y) :
    (moveStar G x y Z).neighborSet u =
      if u ∈ Z then (G.neighborSet u \ {y}) ∪ {x} else G.neighborSet u := by
  classical
  by_cases hu : u ∈ Z <;>
    simp [moveStar, neighborSet_sup, neighborSet_sdiff, neighborSet_starEdges_other hux,
      neighborSet_starEdges_other huy, hu]

theorem moveStar_connected {G : SimpleGraph V} {x y : V} {Z : Set V}
    (hc : G.Connected) (hxy : G.Adj x y) (hx : x ∉ Z) :
    (moveStar G x y Z).Connected := by
  let G' := moveStar G x y Z
  have hxy' : G'.Adj x y := moveStar_retains_root_edge hxy hx
  have adjacent_reachable {u v : V} (huv : G.Adj u v) : G'.Reachable u v := by
    by_cases hremoved : (starEdges y Z).Adj u v
    · rcases starEdges_adj.mp hremoved with ⟨rfl, hz, _⟩ | ⟨rfl, hz, _⟩
      · have hxv : G'.Adj x v := moveStar_adj.mpr
          (Or.inr (starEdges_adj.mpr (Or.inl ⟨rfl, hz, fun h => hx (h ▸ hz)⟩)))
        exact hxy'.symm.reachable.trans hxv.reachable
      · have hxu : G'.Adj x u := moveStar_adj.mpr
          (Or.inr (starEdges_adj.mpr (Or.inl ⟨rfl, hz, fun h => hx (h ▸ hz)⟩)))
        exact hxu.symm.reachable.trans hxy'.reachable
    · exact (moveStar_adj.mpr (Or.inl ⟨huv, hremoved⟩)).reachable
  refine { preconnected := fun u v => ?_, nonempty := hc.nonempty }
  obtain ⟨p⟩ := hc u v
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons hadj _ ih => exact (adjacent_reachable hadj).trans ih

theorem moveStar_root_grows [Finite V] {G : SimpleGraph V} {x y : V} {Z : Set V}
    (hxy : x ≠ y) (hx : x ∉ Z) (hnew : ∃ z ∈ Z, ¬ G.Adj x z) :
    (G.neighborSet x).ncard < ((moveStar G x y Z).neighborSet x).ncard := by
  rw [neighborSet_moveStar_root hxy hx]
  apply Set.ncard_lt_ncard (ht := Set.toFinite _)
  apply (Set.ssubset_iff_of_subset Set.subset_union_left).mpr
  obtain ⟨z, hz, hn⟩ := hnew
  exact ⟨z, Or.inr hz, hn⟩

theorem moveStar_root_adj_iff {G : SimpleGraph V} {x y z : V} {Z : Set V}
    (hxy : x ≠ y) (hx : x ∉ Z) :
    (moveStar G x y Z).Adj x z ↔ G.Adj x z ∨ z ∈ Z := by
  rw [← mem_neighborSet, neighborSet_moveStar_root hxy hx, Set.mem_union, mem_neighborSet]

theorem moveStar_source_adj_iff {G : SimpleGraph V} {x y z : V} {Z : Set V}
    (hxy : x ≠ y) (hy : y ∉ Z) :
    (moveStar G x y Z).Adj y z ↔ G.Adj y z ∧ z ∉ Z := by
  rw [← mem_neighborSet, neighborSet_moveStar_source hxy hy, Set.mem_sdiff, mem_neighborSet]

theorem moveStar_away_adj_iff {G : SimpleGraph V} {x y u v : V} {Z : Set V}
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y) :
    (moveStar G x y Z).Adj u v ↔ G.Adj u v := by
  simp [hux, huy, hvx, hvy]

theorem moveStar_domination {A : SimpleGraph V} {x y : V} {Z : Set V}
    (hxy : x ≠ y)
    (hmeets : ∀ z : V, z ≠ x → z ≠ y → A.Adj y z → ¬ A.Adj x z → z ∈ Z) :
    ∀ z : V, z ≠ x → z ≠ y → (A ⊔ moveStar A x y Z).Adj y z →
      (A ⊔ moveStar A x y Z).Adj x z := by
  intro z hzx hzy h
  have hyz : A.Adj y z := by
    change A.Adj y z ∨ (moveStar A x y Z).Adj y z at h
    rcases h with hyz | hyz
    · exact hyz
    · have hm : A.Adj y z ∧ ¬ (starEdges y Z).Adj y z := by
        simpa only [moveStar_adj, starEdges_adj, hxy.symm, hzx, false_and, or_false] using hyz
      exact hm.1
  by_cases hxz : A.Adj x z
  · exact Or.inl hxz
  · exact Or.inr (moveStar_adj.mpr (Or.inr (starEdges_adj.mpr
      (Or.inl ⟨rfl, hmeets z hzx hzy hyz hxz, hzx⟩))))

noncomputable def toggleEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  if G.Adj x y then G \ edge x y else G ⊔ edge x y

theorem toggleEdge_comm (G : SimpleGraph V) (x y : V) :
    toggleEdge G x y = toggleEdge G y x := by
  unfold toggleEdge
  rw [edge_comm x y, G.adj_comm x y]

private theorem neighborSet_edge_center {x y : V} (hxy : x ≠ y) :
    (edge x y).neighborSet x = {y} := by
  ext z
  simp [mem_neighborSet, edge_adj, hxy, Set.mem_singleton_iff]
  exact fun hz => hz ▸ hxy

private theorem neighborSet_edge_other {x y u : V} (hux : u ≠ x) (huy : u ≠ y) :
    (edge x y).neighborSet u = ∅ := by
  ext z
  simp [mem_neighborSet, edge_adj, hux, huy]

theorem toggleEdge_even_root_iff [Finite V] (G : SimpleGraph V) {x y : V} (hxy : x ≠ y) :
    Even ((toggleEdge G x y).neighborSet x).ncard ↔ ¬ Even (G.neighborSet x).ncard := by
  unfold toggleEdge
  by_cases he : G.Adj x y
  · rw [if_pos he, neighborSet_sdiff, neighborSet_edge_center hxy]
    have h := Set.ncard_sdiff_singleton_add_one ((mem_neighborSet _ _ _).mpr he)
    simp only [Nat.even_iff]
    omega
  · rw [if_neg he, neighborSet_sup, neighborSet_edge_center hxy, Set.union_singleton,
      Set.ncard_insert_of_notMem (fun hy => he ((mem_neighborSet _ _ _).mp hy))]
    simp only [Nat.even_iff]
    omega

theorem neighborSet_toggleEdge_other (G : SimpleGraph V) {x y u : V} (hux : u ≠ x) (huy : u ≠ y) :
    (toggleEdge G x y).neighborSet u = G.neighborSet u := by
  by_cases he : G.Adj x y <;>
    simp [toggleEdge, he, neighborSet_sdiff, neighborSet_sup, neighborSet_edge_other hux huy]

theorem toggleEdge_le {A G : SimpleGraph V} {x y : V} (hle : G ≤ A) (hxy : A.Adj x y) :
    toggleEdge G x y ≤ A := by
  unfold toggleEdge
  split
  · exact sdiff_le.trans hle
  · exact sup_le hle ((edge_le_iff (G := A)).mpr (Or.inr hxy))

theorem toggleEdge_nonroot_adj {G : SimpleGraph V} {x y u v : V} (hu : u ≠ x) (hv : v ≠ x) :
    (toggleEdge G x y).Adj u v ↔ G.Adj u v := by
  by_cases he : G.Adj x y <;> simp [toggleEdge, he, sdiff_adj, sup_adj, edge_adj, hu, hv]

theorem toggleEdge_adj_of_other {G : SimpleGraph V} {x y u v : V} (huv : ¬ (edge x y).Adj u v) :
    (toggleEdge G x y).Adj u v ↔ G.Adj u v := by
  by_cases he : G.Adj x y <;> simp [toggleEdge, he, sdiff_adj, sup_adj, huv]

/-- Restore even degrees after moving the edges by changing `xy` when the moved set is odd. -/
noncomputable def moveStarEven (G : SimpleGraph V) (x y : V) (Z : Set V) : SimpleGraph V :=
  if Even Z.ncard then moveStar G x y Z else toggleEdge (moveStar G x y Z) x y

theorem moveStarEven_even [Finite V] {G : SimpleGraph V} {x y : V} {Z : Set V}
    (hg : ∀ v, Even (G.neighborSet v).ncard) (hxy : x ≠ y) (hx : x ∉ Z) (hy : y ∉ Z)
    (hZ : Z ⊆ G.neighborSet y) (hdis : Disjoint (G.neighborSet x) Z) :
    ∀ v, Even ((moveStarEven G x y Z).neighborSet v).ncard := by
  let G' := moveStar G x y Z
  have hroot : Even (G'.neighborSet x).ncard ↔ Even Z.ncard := by
    rw [show G'.neighborSet x = G.neighborSet x ∪ Z from neighborSet_moveStar_root hxy hx,
      Set.ncard_union_eq hdis]
    have h := hg x
    simp only [Nat.even_iff] at h ⊢
    omega
  have hsource : Even (G'.neighborSet y).ncard ↔ Even Z.ncard := by
    rw [show G'.neighborSet y = G.neighborSet y \ Z from neighborSet_moveStar_source hxy hy]
    have h := hg y
    have hsum := Set.ncard_sdiff_add_ncard_of_subset hZ
    simp only [Nat.even_iff] at h ⊢
    omega
  have hother {v : V} (hvx : v ≠ x) (hvy : v ≠ y) :
      (G'.neighborSet v).ncard = (G.neighborSet v).ncard := by
    rw [show G'.neighborSet v = _ from neighborSet_moveStar_other hvx hvy (Z := Z)]
    by_cases hv : v ∈ Z
    · have hyv : y ∈ G.neighborSet v := ((mem_neighborSet _ _ _).mp (hZ hv)).symm
      have hxv : x ∉ G.neighborSet v := fun h =>
        (Set.disjoint_left.mp hdis) (((mem_neighborSet _ _ _).mp h).symm) hv
      rw [if_pos hv, Set.union_singleton, Set.ncard_insert_of_notMem (fun h => hxv h.1)]
      exact Set.ncard_sdiff_singleton_add_one hyv
    · rw [if_neg hv]
  intro v
  change Even ((if Even Z.ncard then G' else toggleEdge G' x y).neighborSet v).ncard
  by_cases hz : Even Z.ncard
  · rw [if_pos hz]
    by_cases hvx : v = x
    · subst v
      exact hroot.mpr hz
    · by_cases hvy : v = y
      · subst v
        exact hsource.mpr hz
      · rw [hother hvx hvy]
        exact hg v
  · rw [if_neg hz]
    by_cases hvx : v = x
    · subst v
      rw [toggleEdge_even_root_iff G' hxy, hroot]
      exact hz
    · by_cases hvy : v = y
      · subst v
        rw [toggleEdge_comm G' x y, toggleEdge_even_root_iff G' hxy.symm, hsource]
        exact hz
      · rw [neighborSet_toggleEdge_other G' hvx hvy, hother hvx hvy]
        exact hg v

theorem moveStarEven_le {A B : SimpleGraph V} {x y : V} {Z : Set V}
    (hBA : B ≤ A) (hxy : A.Adj x y) (hx : x ∉ Z) : moveStarEven B x y Z ≤ moveStar A x y Z := by
  unfold moveStarEven
  split
  · exact moveStar_mono hBA _ _ _
  · exact toggleEdge_le (moveStar_mono hBA _ _ _) (moveStar_retains_root_edge hxy hx)

theorem moveStarEven_nonroot_adj {A B : SimpleGraph V} {x y : V} {Z : Set V}
    (hAB : ∀ u v, u ≠ x → v ≠ x → (A.Adj u v ↔ B.Adj u v)) :
    ∀ u v, u ≠ x → v ≠ x → ((moveStar A x y Z).Adj u v ↔ (moveStarEven B x y Z).Adj u v) := by
  intro u v hu hv
  have h := hAB u v hu hv
  have hm : (moveStar A x y Z).Adj u v ↔ (moveStar B x y Z).Adj u v := by
    rw [moveStar_adj, moveStar_adj, h]
  unfold moveStarEven
  split
  · exact hm
  · exact hm.trans (toggleEdge_nonroot_adj hu hv).symm

theorem moveStarEven_adj_of_other {G : SimpleGraph V} {x y u v : V} {Z : Set V}
    (huv : ¬ (edge x y).Adj u v) :
    (moveStarEven G x y Z).Adj u v ↔ (moveStar G x y Z).Adj u v := by
  unfold moveStarEven
  split
  · rfl
  · exact toggleEdge_adj_of_other huv

/-- The edges moved from `y` are exactly those with a corresponding root edge absent from `B`. -/
def switchTargets (A B : SimpleGraph V) (x y : V) : Set V :=
  {z | z ≠ x ∧ A.Adj y z ∧ ¬ B.Adj x z}

theorem switch_progress [Finite V] (A B : SimpleGraph V) (x y : V)
    (hconn : A.Connected) (hBA : B ≤ A) (hEven : ∀ v, Even (B.neighborSet v).ncard)
    (hAB : ∀ u v, u ≠ x → v ≠ x → (A.Adj u v ↔ B.Adj u v))
    (hxy : A.Adj x y) (hboundary : ∃ z, z ≠ x ∧ A.Adj y z ∧ ¬ A.Adj x z) :
    let Z := switchTargets A B x y
    let A' := moveStar A x y Z
    let B' := moveStarEven B x y Z
    A'.Connected ∧ B' ≤ A' ∧ (∀ v, Even (B'.neighborSet v).ncard) ∧
      (∀ u v, u ≠ x → v ≠ x → (A'.Adj u v ↔ B'.Adj u v)) ∧
      (A.neighborSet x).ncard < (A'.neighborSet x).ncard ∧
      (∀ z, z ≠ x → z ≠ y → (A ⊔ A').Adj y z → (A ⊔ A').Adj x z) := by
  intro Z A' B'
  have hx : x ∉ Z := fun h => h.1 rfl
  have hy : y ∉ Z := fun h => A.loopless.irrefl _ h.2.1
  have hZB : Z ⊆ B.neighborSet y := fun z hz => (hAB y z hxy.ne.symm hz.1).mp hz.2.1
  have hdis : Disjoint (B.neighborSet x) Z := Set.disjoint_left.mpr (fun _ h hz => hz.2.2 h)
  have hin {z : V} (hz : z ≠ x) (hyz : A.Adj y z) (hn : ¬ A.Adj x z) : z ∈ Z :=
    ⟨hz, hyz, fun h => hn (hBA h)⟩
  have hnew : ∃ z ∈ Z, ¬ A.Adj x z := by
    obtain ⟨z, hz, hyz, hn⟩ := hboundary
    exact ⟨z, hin hz hyz hn, hn⟩
  exact ⟨moveStar_connected hconn hxy hx, moveStarEven_le hBA hxy hx,
    moveStarEven_even hEven hxy.ne hx hy hZB hdis, moveStarEven_nonroot_adj hAB,
    moveStar_root_grows hxy.ne hx hnew, moveStar_domination hxy.ne (fun _ hz _ => hin hz)⟩

def switchCount [DecidableEq V] {k : ℕ} (C : Fin k → Finset (Sym2 V)) (e : Sym2 V) : ℕ :=
  (Finset.univ.filter fun i => e ∈ C i).card

/-- Move every copy of a new edge `xz` back to `yz`. For an `xz` already present in the old
ambient graph, move only one copy to retain the protected multiplicity of `yz`. -/
noncomputable def switchDemand [DecidableEq V] (A B : SimpleGraph V) (x y : V)
    {k : ℕ} (C : Fin k → Finset (Sym2 V)) (z : V) : ℕ :=
  if z ∈ switchTargets A B x y then
    if A.Adj x z then 1 else switchCount C s(x,z)
  else 0

private theorem switchCount_eq_zero_of_not_adj [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} {C : Fin k → Finset (Sym2 V)}
    (hC : ∀ i, ∃ (r : V) (p : G.Walk r r), p.IsCycle ∧ C i = p.edges.toFinset)
    {u v : V} (h : ¬ G.Adj u v) : switchCount C s(u,v) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨r, p, _, hEq⟩ := hC i
  have he := (Finset.mem_filter.mp hi).2
  rw [hEq] at he
  exact h (p.edges_subset_edgeSet (List.mem_toFinset.mp he))

theorem switchDemand_le [DecidableEq V] (A B : SimpleGraph V) (x y : V)
    (hBA : B ≤ A) (hxy : A.Adj x y) {k : ℕ} (C : Fin k → Finset (Sym2 V))
    (hC : ∀ i, ∃ (r : V) (p : (moveStar A x y (switchTargets A B x y)).Walk r r),
      p.IsCycle ∧ C i = p.edges.toFinset)
    (hParity : ∀ e : Sym2 V, Odd (switchCount C e) ↔
      e ∈ (moveStarEven B x y (switchTargets A B x y)).edgeSet)
    (hProtected : ∀ u v : V,
      let A' := moveStar A x y (switchTargets A B x y)
      A'.Adj x u → A'.Adj x v → A'.Adj u v → switchCount C s(u,v) = 1) :
    ∀ z : V, z ≠ x → z ≠ y →
      switchDemand A B x y C z + switchCount C s(y,z) ≤ switchCount C s(x,z) := by
  let Z := switchTargets A B x y
  let A' := moveStar A x y Z
  let B' := moveStarEven B x y Z
  have hxZ : x ∉ Z := fun h => h.1 rfl
  have hyZ : y ∉ Z := fun h => A.loopless.irrefl _ h.2.1
  have hxy' : A'.Adj x y := moveStar_retains_root_edge hxy hxZ
  intro z hzx hzy
  have hnotEdge : ¬ (edge x y).Adj x z := by simp [edge_adj, hxy.ne, hzy]
  have hxCount : B.Adj x z ∨ z ∈ Z → 0 < switchCount C s(x,z) := by
    intro hb
    have hAdj : B'.Adj x z := (moveStarEven_adj_of_other hnotEdge).mpr
      ((moveStar_root_adj_iff hxy.ne hxZ).mpr hb)
    have hOdd := (hParity s(x,z)).mpr hAdj
    rw [Nat.odd_iff] at hOdd
    omega
  by_cases hz : z ∈ Z
  · have hnot : ¬ A'.Adj y z := fun h =>
      ((moveStar_source_adj_iff hxy.ne hyZ).mp h).2 hz
    have hZero : switchCount C s(y,z) = 0 := switchCount_eq_zero_of_not_adj hC hnot
    change (if z ∈ Z then if A.Adj x z then 1 else switchCount C s(x,z) else 0) +
      switchCount C s(y,z) ≤ switchCount C s(x,z)
    rw [if_pos hz, hZero, add_zero]
    by_cases haxz : A.Adj x z
    · rw [if_pos haxz]
      exact hxCount (Or.inr hz)
    · rw [if_neg haxz]
  · change (if z ∈ Z then if A.Adj x z then 1 else switchCount C s(x,z) else 0) +
      switchCount C s(y,z) ≤ switchCount C s(x,z)
    rw [if_neg hz, zero_add]
    by_cases hyz : A'.Adj y z
    · have hayz : A.Adj y z := ((moveStar_source_adj_iff hxy.ne hyZ).mp hyz).1
      have hbxz : B.Adj x z := by
        by_contra h
        exact hz ⟨hzx, hayz, h⟩
      have hxz' : A'.Adj x z := (moveStar_root_adj_iff hxy.ne hxZ).mpr (Or.inl (hBA hbxz))
      rw [hProtected y z hxy' hxz' hyz]
      exact hxCount (Or.inl hbxz)
    · rw [switchCount_eq_zero_of_not_adj hC hyz]
      exact Nat.zero_le _

theorem switchDemand_adj [DecidableEq V] {A B : SimpleGraph V} {x y : V}
    {k : ℕ} {C : Fin k → Finset (Sym2 V)} {z : V}
    (h : 0 < switchDemand A B x y C z) :
    (A ⊔ moveStar A x y (switchTargets A B x y)).Adj y z := by
  by_cases hz : z ∈ switchTargets A B x y
  · exact Or.inl hz.2.1
  · simp [switchDemand, hz] at h

end OMA.Erdos184FanAlt


namespace OMA.FanDegreeHelper

open SimpleGraph

theorem exists_neighbor_non_neighbor_step {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (x : V)
    (hfar : ∃ z : V, z ≠ x ∧ ¬G.Adj x z) :
    ∃ y z : V, G.Adj x y ∧ G.Adj y z ∧ z ≠ x ∧ ¬G.Adj x z := by
  classical
  by_contra hno
  have hclose : ∀ y z : V, G.Adj x y → G.Adj y z → z = x ∨ G.Adj x z := by
    intro y z hxy hyz
    by_cases hzx : z = x
    · exact Or.inl hzx
    · right
      by_contra hxz
      exact hno ⟨y, z, hxy, hyz, hzx, hxz⟩
  have hwalk : ∀ {u v : V} (p : G.Walk u v),
      (u = x ∨ G.Adj x u) → (v = x ∨ G.Adj x v) := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      intro hu
      apply ih
      rcases hu with rfl | hxu
      · exact Or.inr huv
      · exact hclose u v hxu huv
  obtain ⟨z, hzx, hxz⟩ := hfar
  obtain ⟨p⟩ := hG.preconnected x z
  rcases hwalk p (Or.inl rfl) with hz | hz
  · exact hzx hz
  · exact hxz hz




end OMA.FanDegreeHelper

open SimpleGraph
open scoped Classical

namespace OMA.Erdos184FanParity

theorem root_matrix_complete {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V → V → ZMod 2) (x : V)
    (haSym : ∀ u v, a u v = a v u) (hbSym : ∀ u v, b u v = b v u)
    (haDiag : ∀ v, a v v = 0) (hbDiag : ∀ v, b v v = 0)
    (haSum : ∀ v, ∑ w, a v w = 0) (hbSum : ∀ v, ∑ w, b v w = 0)
    (hAway : ∀ u v, u ≠ x → v ≠ x → a u v = b u v) : a = b := by
  have hroot (u : V) (hu : u ≠ x) : a u x = b u x := by
    have hrem : ∑ w ∈ Finset.univ.erase x, a u w =
        ∑ w ∈ Finset.univ.erase x, b u w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hAway u w hu (Finset.ne_of_mem_erase hw)
    have ha := Finset.sum_erase_add Finset.univ (a u) (Finset.mem_univ x)
    have hb := Finset.sum_erase_add Finset.univ (b u) (Finset.mem_univ x)
    rw [haSum] at ha
    rw [hbSum, ← hrem] at hb
    exact add_left_cancel (ha.trans hb.symm)
  funext u v
  by_cases hu : u = x
  · subst u
    by_cases hv : v = x
    · subst v; rw [haDiag, hbDiag]
    · rw [haSym, hbSym]; exact hroot v hv
  · by_cases hv : v = x
    · subst v; exact hroot u hu
    · exact hAway u v hu hv

noncomputable def weight {V : Type*} (G : SimpleGraph V) (u v : V) : ZMod 2 :=
  if G.Adj u v then 1 else 0

theorem sum_weight {V : Type*} [Fintype V] (G : SimpleGraph V) (u : V) :
    (∑ v, weight G u v) = ((G.neighborSet u).ncard : ZMod 2) := by
  classical
  have hs : (Finset.univ.filter (G.Adj u)) = (G.neighborSet u).toFinset := by
    ext v; simp
  simp only [weight, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hs, ← Set.ncard_eq_toFinset_card']

theorem family_parity_complete {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (C : I → SimpleGraph V) (B : SimpleGraph V) (x : V)
    (hC : ∀ i v, Even (((C i).neighborSet v).ncard))
    (hB : ∀ v, Even ((B.neighborSet v).ncard))
    (hAway : ∀ u v, u ≠ x → v ≠ x →
      (Odd ((Finset.univ.filter fun i => (C i).Adj u v).card) ↔ B.Adj u v)) :
    ∀ u v, Odd ((Finset.univ.filter fun i => (C i).Adj u v).card) ↔ B.Adj u v := by
  classical
  let a (u v : V) : ZMod 2 := ∑ i, weight (C i) u v
  have hcast (u v : V) :
      a u v = ((Finset.univ.filter fun i => (C i).Adj u v).card : ZMod 2) := by
    simp [a, weight]
  have heq : a = weight B := by
    apply root_matrix_complete a (weight B) x
    · intro u v
      apply Finset.sum_congr rfl
      intro i _
      simp only [weight, (C i).adj_comm]
    · intro u v; simp only [weight, B.adj_comm]
    · intro v; simp [a, weight]
    · intro v; simp [weight]
    · intro v
      dsimp [a]
      rw [Finset.sum_comm]
      simp only [sum_weight, (hC _ _).natCast_zmod_two, Finset.sum_const_zero]
    · intro v; rw [sum_weight]; exact (hB v).natCast_zmod_two
    · intro u v hu hv
      rw [hcast]
      by_cases hb : B.Adj u v
      · simp only [weight, if_pos hb]
        exact ((hAway u v hu hv).mpr hb).natCast_zmod_two
      · simp only [weight, if_neg hb]
        exact (Nat.not_odd_iff_even.mp (fun ho => hb ((hAway u v hu hv).mp ho))).natCast_zmod_two
  intro u v
  rw [← ZMod.natCast_eq_one_iff_odd, ← hcast, heq]
  by_cases hb : B.Adj u v <;> simp [weight, hb]

theorem cycle_spanning_even {V : Type*} [Fintype V] {A : SimpleGraph V}
    {u : V} {p : A.Walk u u} (hp : p.IsCycle) (v : V) :
    Even ((p.toSubgraph.spanningCoe.neighborSet v).ncard) := by
  change Even ((p.toSubgraph.neighborSet v).ncard)
  by_cases hv : v ∈ p.support
  · rw [hp.ncard_neighborSet_toSubgraph_eq_two hv]
    exact even_two
  · have hs : p.toSubgraph.neighborSet v = ∅ := by
      ext w
      constructor
      · intro hw
        exact (hv ((Walk.mem_verts_toSubgraph p).mp (p.toSubgraph.edge_vert hw))).elim
      · intro hw; exact hw.elim
    simp [hs]

/-- Parity of an even graph's cycle family is determined away from one root. -/
theorem cycle_family_parity_complete {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) (x : V) (k : ℕ) (S : Fin k → Finset (Sym2 V))
    (hCycles : ∀ i, ∃ (u : V) (p : A.Walk u u), p.IsCycle ∧ S i = p.edges.toFinset)
    (hB : ∀ v, Even ((B.neighborSet v).ncard))
    (hAway : ∀ e : Sym2 V, x ∉ e →
      (Odd ((Finset.univ.filter fun i => e ∈ S i).card) ↔ e ∈ B.edgeSet)) :
    ∀ e : Sym2 V,
      Odd ((Finset.univ.filter fun i => e ∈ S i).card) ↔ e ∈ B.edgeSet := by
  classical
  choose u p hp hs using hCycles
  let C (i : Fin k) := (p i).toSubgraph.spanningCoe
  have hAdj (i : Fin k) (v w : V) : (C i).Adj v w ↔ s(v,w) ∈ S i := by
    change s(v,w) ∈ (p i).toSubgraph.edgeSet ↔ s(v,w) ∈ S i
    rw [Walk.edgeSet_toSubgraph, hs i]
    simp
  have hComplete := family_parity_complete C B x
    (fun i v => cycle_spanning_even (hp i) v) hB (by
      intro v w hv hw
      have he : x ∉ s(v,w) := by simpa only [Sym2.mem_iff, not_or] using ⟨Ne.symm hv, Ne.symm hw⟩
      simpa only [hAdj, SimpleGraph.mem_edgeSet] using hAway s(v,w) he)
  intro e
  induction e using Sym2.ind with
  | h v w => simpa only [hAdj, SimpleGraph.mem_edgeSet] using hComplete v w

end OMA.Erdos184FanParity


open SimpleGraph

namespace OMA.Erdos184FanInduction

abbrev RootComplement {V : Type*} (x : V) := {v : V // v ≠ x}

def deleteRoot {V : Type*} (A : SimpleGraph V) (x : V) : SimpleGraph (RootComplement x) :=
  A.induce {v | v ≠ x}

private def deleteRootHom {V : Type*} (A : SimpleGraph V) (x : V) : deleteRoot A x →g A where
  toFun := Subtype.val
  map_rel' := id

private theorem close_deleted_path {V : Type*} [DecidableEq V] (A : SimpleGraph V) (x : V)
    (hUniversal : ∀ v ≠ x, A.Adj x v) {u v : RootComplement x}
    (p : (deleteRoot A x).Walk u v) (hp : p.IsPath) (hpositive : 0 < p.length) :
    ∃ c : A.Walk x x, c.IsCycle ∧ ∀ e : Sym2 V, x ∉ e →
      (e ∈ c.edges.toFinset ↔ e ∈ p.edges.toFinset.image (Sym2.map Subtype.val)) := by
  let f := deleteRootHom A x
  let q := p.map f
  have hq : q.IsPath := hp.map Subtype.val_injective
  have hxq : x ∉ q.support := by
    intro hx
    have hmem : x ∈ p.support.map f := by simpa only [q, Walk.support_map] using hx
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hmem
    exact w.property hw
  have huv : u.val ≠ v.val := by
    intro heq
    have hnil := hp.nil_iff_eq.mpr (Subtype.ext heq)
    have hzero := Walk.length_eq_zero_iff.mpr hnil
    omega
  have hxu : A.Adj x u.val := hUniversal _ u.property
  have hvx : A.Adj v.val x := (hUniversal _ v.property).symm
  let r := q.concat hvx
  have hr : r.IsPath := hq.concat hxq hvx
  have hrEdges : r.edges = q.edges ++ [s(v.val,x)] := by
    exact (Walk.edges_concat q hvx).trans (List.concat_eq_append ..)
  have hnot : s(x,u.val) ∉ r.edges := by
    intro he
    rw [hrEdges] at he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact hxq (q.fst_mem_support_of_mem_edges he)
    · rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨_, h⟩
      · exact v.property h.symm
      · exact huv h
  let c := Walk.cons hxu r
  have hc : c.IsCycle := (Walk.cons_isCycle_iff r hxu).mpr ⟨hr, hnot⟩
  refine ⟨c, hc, fun e hxe => ?_⟩
  have hf : e ≠ s(x,u.val) := fun h => hxe (h ▸ Sym2.mem_mk_left x u.val)
  have hl : e ≠ s(v.val,x) := fun h => hxe (h ▸ Sym2.mem_mk_right v.val x)
  have hqEdges : q.edges = p.edges.map (Sym2.map Subtype.val) := Walk.edges_map f p
  rw [List.mem_toFinset]
  change e ∈ s(x,u.val) :: r.edges ↔ _
  rw [hrEdges, hqEdges]
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, hf, hl,
    false_or, or_false, List.mem_map, Finset.mem_image, List.mem_toFinset]

private theorem retain_deleted_cycle {V : Type*} [DecidableEq V] (A : SimpleGraph V) (x : V)
    {u : RootComplement x} (p : (deleteRoot A x).Walk u u) (hp : p.IsCycle) :
    ∃ (v : V) (c : A.Walk v v), c.IsCycle ∧ ∀ e : Sym2 V,
      (e ∈ c.edges.toFinset ↔ e ∈ p.edges.toFinset.image (Sym2.map Subtype.val)) := by
  let f := deleteRootHom A x
  refine ⟨f u, p.map f, hp.map Subtype.val_injective, fun e => ?_⟩
  have he : (p.map f).edges = p.edges.map (Sym2.map Subtype.val) := Walk.edges_map f p
  rw [List.mem_toFinset, he]
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]

theorem partition_bound_at_root {V : Type*} [Fintype V] [DecidableEq V] (x : V) (k : ℕ)
    (hk : 2 * k ≤ Fintype.card (RootComplement x)) : k ≤ (Fintype.card V - 1) / 2 := by
  have hcard : Fintype.card (Option (RootComplement x)) = Fintype.card V :=
    Fintype.card_congr (Equiv.optionSubtypeNe x)
  rw [Fintype.card_option] at hcard
  omega

open scoped Classical in
/-- Close each nonempty path through a universal root and lift the cycles unchanged.
Every edge away from the root retains its original multiplicity. -/
theorem fill_from_path_partition {V : Type*} [DecidableEq V] (A : SimpleGraph V) (x : V)
    (hUniversal : ∀ v ≠ x, A.Adj x v) {k : ℕ}
    (P : Fin k → Finset (Sym2 (RootComplement x)))
    (hP : ∀ i,
      (∃ (u v : RootComplement x) (p : (deleteRoot A x).Walk u v),
        p.IsPath ∧ 0 < p.length ∧ P i = p.edges.toFinset) ∨
      (∃ (u : RootComplement x) (p : (deleteRoot A x).Walk u u),
        p.IsCycle ∧ P i = p.edges.toFinset))
    (hDisjoint : Pairwise fun i j => Disjoint (P i) (P j))
    (hCover : ∀ e ∈ (deleteRoot A x).edgeSet, ∃ i, e ∈ P i) :
    ∃ S : Fin k → Finset (Sym2 V),
      (∀ i, ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧ S i = c.edges.toFinset) ∧
      ∀ e : Sym2 V, x ∉ e →
        (Finset.univ.filter (fun i => e ∈ S i)).card = if e ∈ A.edgeSet then 1 else 0 := by
  classical
  have hp (i : Fin k) : ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧
      ∀ e : Sym2 V, x ∉ e →
        (e ∈ c.edges.toFinset ↔ e ∈ (P i).image (Sym2.map Subtype.val)) := by
    rcases hP i with ⟨_, _, p, hp, hl, hEq⟩ | ⟨_, p, hp, hEq⟩
    · obtain ⟨c, hc, he⟩ := close_deleted_path A x hUniversal p hp hl
      exact ⟨x, c, hc, fun e h => hEq ▸ he e h⟩
    · obtain ⟨v, c, hc, he⟩ := retain_deleted_cycle A x p hp
      exact ⟨v, c, hc, fun e _ => hEq ▸ he e⟩
  choose u c hc hsame using hp
  let S : Fin k → Finset (Sym2 V) := fun i => (c i).edges.toFinset
  refine ⟨S, fun i => ⟨u i, c i, hc i, rfl⟩, ?_⟩
  intro e hxe
  by_cases he : e ∈ A.edgeSet
  · rw [if_pos he]
    have hex : ∃ e' ∈ (deleteRoot A x).edgeSet, Sym2.map Subtype.val e' = e := by
      induction e using Sym2.ind with
      | h a b =>
        have ha : a ≠ x := fun h => hxe (h ▸ Sym2.mem_mk_left a b)
        have hb : b ≠ x := fun h => hxe (h ▸ Sym2.mem_mk_right a b)
        exact ⟨s(⟨a, ha⟩,⟨b, hb⟩), he, rfl⟩
    obtain ⟨e', he', hemap⟩ := hex
    obtain ⟨i, hi⟩ := hCover e' he'
    have hfilter : (Finset.univ.filter (fun j => e ∈ S j)) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change e ∈ (c j).edges.toFinset ↔ j = i
      rw [hsame j e hxe]
      constructor
      · intro hj
        obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hj
        have hfe' : f = e' := Sym2.map.injective Subtype.val_injective (hfe.trans hemap.symm)
        subst f
        by_contra hne
        exact Finset.disjoint_left.mp (hDisjoint hne) hf hi
      · rintro rfl
        exact Finset.mem_image.mpr ⟨e', hi, hemap⟩
    rw [hfilter, Finset.card_singleton]
  · rw [if_neg he, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hmem : e ∈ (c i).edges := List.mem_toFinset.mp (Finset.mem_filter.mp hi).2
    exact he ((c i).edges_subset_edgeSet hmem)

theorem ordinary_of_odd_cycle_family {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) {k : ℕ} (S : Fin k → Finset (Sym2 V))
    (hCycle : ∀ i, ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧ S i = c.edges.toFinset)
    (hOdd : ∀ e ∈ A.edgeSet, Odd ((Finset.univ.filter (fun i => e ∈ S i)).card))
    (hBound : k ≤ (Fintype.card V - 1) / 2) :
    ∃ T : Finset (Finset (Sym2 V)),
      (∀ s ∈ T, ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧ s = c.edges.toFinset) ∧
      (∀ e ∈ A.edgeSet, ∃ s ∈ T, e ∈ s) ∧ T.card ≤ Fintype.card V / 2 := by
  let T := Finset.univ.image S
  have hCard : T.card ≤ k := Finset.card_image_le.trans_eq (by simp)
  refine ⟨T, ?_, ?_, by omega⟩
  · intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact hCycle i
  · intro e he
    have hn : 0 < (Finset.univ.filter (fun i => e ∈ S i)).card := by
      obtain ⟨l, h⟩ := hOdd e he
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hn
    exact ⟨S i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, (Finset.mem_filter.mp hi).2⟩

/-- The multiplicity-preserving cover used in the strengthened Eulerian induction. -/
def ProtectedOddCover {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) (x : V) : Prop :=
  ∃ (k : ℕ) (S : Fin k → Finset (Sym2 V)),
    (∀ i, ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧ S i = c.edges.toFinset) ∧
    (∀ e : Sym2 V, Odd ((Finset.univ.filter (fun i => e ∈ S i)).card) ↔ e ∈ B.edgeSet) ∧
    (∀ u v, A.Adj x u → A.Adj x v → A.Adj u v →
      (Finset.univ.filter (fun i => s(u,v) ∈ S i)).card = 1) ∧
    k ≤ (Fintype.card V - 1) / 2

theorem protected_cover_at_universal_root {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) (x : V) (hUniversal : ∀ v ≠ x, A.Adj x v)
    (hAgree : ∀ u v : V, u ≠ x → v ≠ x → (B.Adj u v ↔ A.Adj u v))
    (complete : ∀ (k : ℕ) (S : Fin k → Finset (Sym2 V)),
      (∀ i, ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧ S i = c.edges.toFinset) →
      (∀ e : Sym2 V, x ∉ e →
        (Odd ((Finset.univ.filter (fun i => e ∈ S i)).card) ↔ e ∈ B.edgeSet)) →
      ∀ e : Sym2 V, Odd ((Finset.univ.filter (fun i => e ∈ S i)).card) ↔ e ∈ B.edgeSet)
    {k : ℕ} (P : Fin k → Finset (Sym2 (RootComplement x)))
    (hP : ∀ i,
      (∃ (u v : RootComplement x) (p : (deleteRoot A x).Walk u v),
        p.IsPath ∧ 0 < p.length ∧ P i = p.edges.toFinset) ∨
      (∃ (u : RootComplement x) (p : (deleteRoot A x).Walk u u),
        p.IsCycle ∧ P i = p.edges.toFinset))
    (hDisjoint : Pairwise fun i j => Disjoint (P i) (P j))
    (hCover : ∀ e ∈ (deleteRoot A x).edgeSet, ∃ i, e ∈ P i)
    (hBound : 2 * k ≤ Fintype.card (RootComplement x)) : ProtectedOddCover A B x := by
  classical
  obtain ⟨S, hCycles, hCount⟩ := fill_from_path_partition A x hUniversal P hP hDisjoint hCover
  refine ⟨k, S, hCycles, complete k S hCycles ?_, ?_, partition_bound_at_root x k hBound⟩
  · intro e hxe
    rw [hCount e hxe]
    have hMem : e ∈ B.edgeSet ↔ e ∈ A.edgeSet := by
      induction e using Sym2.ind with
      | h u v =>
        have hu : u ≠ x := fun h => hxe (h ▸ Sym2.mem_mk_left u v)
        have hv : v ≠ x := fun h => hxe (h ▸ Sym2.mem_mk_right u v)
        exact hAgree u v hu hv
    by_cases he : e ∈ A.edgeSet <;> simp [he, hMem]
  · intro u v hxu hxv huv
    have hxe : x ∉ s(u,v) := by simp [hxu.ne, hxv.ne]
    exact (hCount s(u,v) hxe).trans (if_pos (show s(u,v) ∈ A.edgeSet from huv))

theorem protected_cover_at_universal_root_of_walks {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) (x : V) (hUniversal : ∀ v ≠ x, A.Adj x v)
    (hAgree : ∀ u v : V, u ≠ x → v ≠ x → (B.Adj u v ↔ A.Adj u v))
    (complete : ∀ (k : ℕ) (S : Fin k → Finset (Sym2 V)),
      (∀ i, ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧ S i = c.edges.toFinset) →
      (∀ e : Sym2 V, x ∉ e →
        (Odd ((Finset.univ.filter (fun i => e ∈ S i)).card) ↔ e ∈ B.edgeSet)) →
      ∀ e : Sym2 V, Odd ((Finset.univ.filter (fun i => e ∈ S i)).card) ↔ e ∈ B.edgeSet)
    {k : ℕ} (P : Fin k → Σ u v : RootComplement x, (deleteRoot A x).Walk u v)
    (hSimple : ∀ i, ((P i).2.2.IsPath ∧ 0 < (P i).2.2.length) ∨
      ∃ h : (P i).2.1 = (P i).1, ((P i).2.2.copy rfl h).IsCycle)
    (hDisjoint : Pairwise fun i j => Disjoint (P i).2.2.edgeSet (P j).2.2.edgeSet)
    (hCover : (⋃ i, (P i).2.2.edgeSet) = (deleteRoot A x).edgeSet)
    (hBound : 2 * k ≤ Fintype.card (RootComplement x)) : ProtectedOddCover A B x := by
  let S := fun i => (P i).2.2.edges.toFinset
  apply protected_cover_at_universal_root A B x hUniversal hAgree complete S _ _ _ hBound
  · intro i
    rcases hSimple i with ⟨hp, hl⟩ | ⟨heq, hc⟩
    · exact Or.inl ⟨_, _, (P i).2.2, hp, hl, rfl⟩
    · exact Or.inr ⟨_, (P i).2.2.copy rfl heq, hc, by simp [S]⟩
  · intro i j hij
    exact Finset.disjoint_left.mpr fun _ hi hj => Set.disjoint_left.mp (hDisjoint hij)
      (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj)
  · intro e he
    rw [← hCover] at he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    exact ⟨i, List.mem_toFinset.mpr hi⟩

def ValidRootState {V : Type*} (A B : SimpleGraph V) (x : V) : Prop :=
  A.Connected ∧ B ≤ A ∧
    (∀ u v : V, u ≠ x → v ≠ x → (B.Adj u v ↔ A.Adj u v)) ∧
    (∀ v, Even ((B.neighborSet v).ncard))

/-- A reversible step that grows the root neighborhood reduces the cover problem
to the case where the root is universal. -/
theorem protected_cover_from_switch {V : Type*} [Fintype V] [DecidableEq V] (x : V)
    (hBase : ∀ A B : SimpleGraph V, ValidRootState A B x →
      (∀ v ≠ x, A.Adj x v) → ProtectedOddCover A B x)
    (hStep : ∀ A B : SimpleGraph V, ValidRootState A B x →
      (∃ v, v ≠ x ∧ ¬ A.Adj x v) →
      ∃ A' B' : SimpleGraph V, ValidRootState A' B' x ∧
        (A.neighborSet x).ncard < (A'.neighborSet x).ncard ∧
        (ProtectedOddCover A' B' x → ProtectedOddCover A B x)) :
    ∀ A B : SimpleGraph V, ValidRootState A B x → ProtectedOddCover A B x := by
  have hBound (A : SimpleGraph V) : (A.neighborSet x).ncard ≤ Fintype.card V := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using
      (Set.ncard_le_ncard (Set.subset_univ (A.neighborSet x)) (Set.toFinite _))
  have key (n : ℕ) : ∀ A B : SimpleGraph V, ValidRootState A B x →
      Fintype.card V - (A.neighborSet x).ncard = n → ProtectedOddCover A B x := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B hValid hN
      by_cases hUniversal : ∀ v ≠ x, A.Adj x v
      · exact hBase A B hValid hUniversal
      · push Not at hUniversal
        obtain ⟨A', B', hValid', hGrow, hBack⟩ := hStep A B hValid hUniversal
        have hLT : Fintype.card V - (A'.neighborSet x).ncard < n := by
          have hBound' := hBound A'
          omega
        exact hBack (ih _ hLT A' B' hValid' rfl)
  intro A B hValid
  exact key _ A B hValid rfl

theorem ordinary_of_protected_cover {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) (x : V) (h : ProtectedOddCover A A x) :
    ∃ T : Finset (Finset (Sym2 V)),
      (∀ s ∈ T, ∃ (u : V) (c : A.Walk u u), c.IsCycle ∧ s = c.edges.toFinset) ∧
      (∀ e ∈ A.edgeSet, ∃ s ∈ T, e ∈ s) ∧ T.card ≤ Fintype.card V / 2 := by
  obtain ⟨_, S, hS, hParity, _, hBudget⟩ := h
  exact ordinary_of_odd_cycle_family A S hS (fun e he => (hParity e).mpr he) hBudget

open OMA.Erdos184Fan OMA.Erdos184FanAlt

private theorem occ_zero_of_nonedge {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} {C : Fin k → Finset (Sym2 V)}
    (hC : ∀ i, ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ C i = p.edges.toFinset)
    {e : Sym2 V} (he : e ∉ G.edgeSet) : occ C e = 0 := by
  unfold occ
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨u, p, _, hpi⟩ := hC i
  have hmem := (Finset.mem_filter.mp hi).2
  rw [hpi] at hmem
  exact he (p.edges_subset_edgeSet (List.mem_toFinset.mp hmem))

private theorem cycle_family_transfer {V : Type*} [DecidableEq V] {A G : SimpleGraph V}
    {k : ℕ} {D : Fin k → Finset (Sym2 V)}
    (hD : ∀ i, ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ D i = p.edges.toFinset)
    (hZero : ∀ e : Sym2 V, e ∉ A.edgeSet → occ D e = 0) :
    ∀ i, ∃ (u : V) (p : A.Walk u u), p.IsCycle ∧ D i = p.edges.toFinset := by
  intro i
  obtain ⟨u, p, hp, heq⟩ := hD i
  have hSub : ∀ e ∈ p.edges, e ∈ A.edgeSet := by
    intro e he
    by_contra hn
    have hp' : 0 < occ D e := by
      apply Finset.card_pos.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [heq]
      exact List.mem_toFinset.mpr he
    rw [hZero e hn] at hp'
    exact (Nat.lt_irrefl _) hp'
  refine ⟨u, p.transfer A hSub, hp.transfer hSub, ?_⟩
  rw [Walk.edges_transfer]
  exact heq

open scoped Classical in
theorem restore_switched_cover {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) (x y : V) (hState : ValidRootState A B x) (hxy : A.Adj x y)
    {k : ℕ} (C D : Fin k → Finset (Sym2 V)) (hBudget : k ≤ (Fintype.card V - 1) / 2) :
    let Z := switchTargets A B x y
    let A' := moveStar A x y Z
    let B' := moveStarEven B x y Z
    let d := fun z : V => if z ∈ Z then if A.Adj x z then 1 else occ C s(x,z) else 0
    (∀ i, ∃ (u : V) (p : A'.Walk u u), p.IsCycle ∧ C i = p.edges.toFinset) →
    (∀ e : Sym2 V, Odd (occ C e) ↔ e ∈ B'.edgeSet) →
    (∀ u v, A'.Adj x u → A'.Adj x v → A'.Adj u v → occ C s(u,v) = 1) →
    (∀ i, ∃ (u : V) (p : (A ⊔ A').Walk u u), p.IsCycle ∧ D i = p.edges.toFinset) →
    (∀ z : V, z ≠ x → z ≠ y → occ D s(y,z) = occ C s(y,z) + d z ∧
      occ D s(x,z) + d z = occ C s(x,z)) →
    (∀ e : Sym2 V, x ∉ e → y ∉ e → occ D e = occ C e) →
    ProtectedOddCover A B x := by
  intro Z A' B' d hC hParity hProt hD hCounts hRestCounts
  have hxZ : x ∉ Z := fun h => h.1 rfl
  have hyZ : y ∉ Z := fun h => A.loopless.irrefl _ h.2.1
  have hAroot (z : V) : A'.Adj x z ↔ A.Adj x z ∨ z ∈ Z :=
    moveStar_root_adj_iff hxy.ne hxZ
  have hAsource (z : V) : A'.Adj y z ↔ A.Adj y z ∧ z ∉ Z :=
    moveStar_source_adj_iff hxy.ne hyZ
  have hBroot (z : V) (hzy : z ≠ y) : B'.Adj x z ↔ B.Adj x z ∨ z ∈ Z := by
    have hnot : ¬ (edge x y).Adj x z := by simp [edge_adj, hzy, hxy.ne]
    exact (moveStarEven_adj_of_other hnot).trans (moveStar_root_adj_iff hxy.ne hxZ)
  have hBA' (u v : V) (hu : u ≠ x) (hv : v ≠ x) : B'.Adj u v ↔ A'.Adj u v :=
    (moveStarEven_nonroot_adj (fun a b ha hb => (hState.2.2.1 a b ha hb).symm) u v hu hv).symm
  have hRest (u v : V) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y) :
      A'.Adj u v ↔ A.Adj u v := moveStar_away_adj_iff hux huy hvx hvy
  have hXzero (z : V) (hn : ¬ A.Adj x z) : occ D s(x,z) = 0 := by
    by_cases hzx : z = x
    · subst z
      exact occ_zero_of_nonedge hD (show s(x,x) ∉ (A ⊔ A').edgeSet from
        (A ⊔ A').loopless.irrefl x)
    by_cases hzy : z = y
    · subst z
      exact (hn hxy).elim
    have hcount := (hCounts z hzx hzy).2
    by_cases hz : z ∈ Z
    · simp only [d, if_pos hz, if_neg hn] at hcount
      omega
    · have hc := occ_zero_of_nonedge hC (show s(x,z) ∉ A'.edgeSet from
        fun h => ((hAroot z).mp h).elim hn hz)
      omega
  have hYzero (z : V) (hn : ¬ A.Adj y z) : occ D s(y,z) = 0 := by
    by_cases hzy : z = y
    · subst z
      exact occ_zero_of_nonedge hD (show s(y,y) ∉ (A ⊔ A').edgeSet from
        (A ⊔ A').loopless.irrefl y)
    by_cases hzx : z = x
    · subst z
      exact (hn hxy.symm).elim
    have hz : z ∉ Z := fun h => hn h.2.1
    have hc := occ_zero_of_nonedge hC (show s(y,z) ∉ A'.edgeSet from
      fun h => hn ((hAsource z).mp h).1)
    simp [(hCounts z hzx hzy).1, d, hz, hc]
  have hD' : ∀ i, ∃ (u : V) (p : A.Walk u u), p.IsCycle ∧ D i = p.edges.toFinset := by
    apply cycle_family_transfer hD
    intro e hn
    by_cases hxe : x ∈ e
    · rw [← Sym2.other_spec hxe] at hn ⊢
      exact hXzero _ hn
    by_cases hye : y ∈ e
    · rw [← Sym2.other_spec hye] at hn ⊢
      exact hYzero _ hn
    rw [hRestCounts e hxe hye]
    apply occ_zero_of_nonedge hC
    induction e using Sym2.ind with
    | h u v =>
      simp only [Sym2.mem_iff, not_or] at hxe hye
      exact fun ha => hn ((hRest u v (Ne.symm hxe.1) (Ne.symm hye.1)
        (Ne.symm hxe.2) (Ne.symm hye.2)).mp ha)
  have hAwayY (z : V) (hzx : z ≠ x) : Odd (occ D s(y,z)) ↔ B.Adj y z := by
    by_cases hzy : z = y
    · subst z
      have hz := hYzero y (A.loopless.irrefl y)
      simp [hz]
    rw [(hCounts z hzx hzy).1]
    by_cases hz : z ∈ Z
    · have hBeforeZero := occ_zero_of_nonedge hC (show s(y,z) ∉ A'.edgeSet from
        fun h => (hAsource z).mp h |>.2 hz)
      rw [hBeforeZero, zero_add]
      have hDemandOdd : Odd (d z) := by
        by_cases hAx : A.Adj x z
        · simp [d, hz, hAx]
        · simpa [d, hz, hAx] using (hParity s(x,z)).mpr ((hBroot z hzy).mpr (Or.inr hz))
      exact iff_of_true hDemandOdd ((hState.2.2.1 y z hxy.ne.symm hzx).mpr hz.2.1)
    · simp only [d, if_neg hz, add_zero]
      rw [hParity]
      change B'.Adj y z ↔ B.Adj y z
      refine (hBA' y z hxy.ne.symm hzx).trans ((hAsource z).trans ?_)
      simpa only [hz, not_false_eq_true, and_true] using (hState.2.2.1 y z hxy.ne.symm hzx).symm
  have hAway : ∀ e : Sym2 V, x ∉ e → (Odd (occ D e) ↔ e ∈ B.edgeSet) := by
    intro e hxe
    by_cases hye : y ∈ e
    · rw [← Sym2.other_spec hye] at hxe ⊢
      exact hAwayY _ (fun h => hxe (h ▸ Sym2.mem_mk_right y _))
    rw [hRestCounts e hxe hye, hParity]
    induction e using Sym2.ind with
    | h u v =>
      simp only [Sym2.mem_iff, not_or] at hxe hye
      exact (hBA' u v (Ne.symm hxe.1) (Ne.symm hxe.2)).trans
        ((hRest u v (Ne.symm hxe.1) (Ne.symm hye.1) (Ne.symm hxe.2) (Ne.symm hye.2)).trans
          (hState.2.2.1 u v (Ne.symm hxe.1) (Ne.symm hxe.2)).symm)
  have hProtY (z : V) (hxz : A.Adj x z) (hyz : A.Adj y z) : occ D s(y,z) = 1 := by
    rw [(hCounts z hxz.ne.symm hyz.ne.symm).1]
    by_cases hz : z ∈ Z
    · have hBeforeZero := occ_zero_of_nonedge hC (show s(y,z) ∉ A'.edgeSet from
        fun h => (hAsource z).mp h |>.2 hz)
      simp [hBeforeZero, d, hz, hxz]
    · have hBefore := hProt y z ((hAroot y).mpr (Or.inl hxy))
        ((hAroot z).mpr (Or.inl hxz)) ((hAsource z).mpr ⟨hyz, hz⟩)
      simp [hBefore, d, hz]
  refine ⟨k, D, hD', OMA.Erdos184FanParity.cycle_family_parity_complete
    A B x k D hD' hState.2.2.2 hAway, ?_, hBudget⟩
  intro u v hxu hxv huv
  change occ D s(u,v) = 1
  by_cases huy : u = y
  · subst u
    exact hProtY v hxv huv
  by_cases hvy : v = y
  · subst v
    rw [Sym2.eq_swap]
    exact hProtY u hxu huv.symm
  have hxe : x ∉ s(u,v) := by simp [hxu.ne, hxv.ne]
  have hye : y ∉ s(u,v) := by simp [Ne.symm huy, Ne.symm hvy]
  rw [hRestCounts s(u,v) hxe hye]
  exact hProt u v ((hAroot u).mpr (Or.inl hxu)) ((hAroot v).mpr (Or.inl hxv))
    ((hRest u v hxu.ne.symm huy hxv.ne.symm hvy).mpr huv)

theorem protected_switch_step {V : Type*} [Fintype V] [DecidableEq V] (x : V)
    (A B : SimpleGraph V) (hState : ValidRootState A B x)
    (hfar : ∃ v, v ≠ x ∧ ¬ A.Adj x v) :
    ∃ A' B' : SimpleGraph V, ValidRootState A' B' x ∧
      (A.neighborSet x).ncard < (A'.neighborSet x).ncard ∧
      (ProtectedOddCover A' B' x → ProtectedOddCover A B x) := by
  classical
  obtain ⟨y, z, hxy, hyz, hzx, hxz⟩ :=
    OMA.FanDegreeHelper.exists_neighbor_non_neighbor_step A hState.1 x hfar
  let Z := switchTargets A B x y
  let A' := moveStar A x y Z
  let B' := moveStarEven B x y Z
  obtain ⟨hConn', hBA', hEven', hAgree', hGrow, hDom⟩ :=
    switch_progress A B x y hState.1 hState.2.1 hState.2.2.2
      (fun a b ha hb => (hState.2.2.1 a b ha hb).symm) hxy ⟨z, hzx, hyz, hxz⟩
  refine ⟨A', B', ⟨hConn', hBA', fun a b ha hb => (hAgree' a b ha hb).symm, hEven'⟩,
    hGrow, ?_⟩
  rintro ⟨k, C, hC, hParity, hProtected, hBudget⟩
  have hC' : ∀ i, ∃ (u : V) (p : (A ⊔ A').Walk u u),
      p.IsCycle ∧ C i = p.edges.toFinset := by
    intro i
    obtain ⟨u, p, hp, heq⟩ := hC i
    exact ⟨u, p.mapLe le_sup_right, hp.mapLe le_sup_right, by simpa using heq⟩
  let d := switchDemand A B x y C
  have hd := switchDemand_le A B x y hState.2.1 hxy C hC hParity hProtected
  obtain ⟨D, hD, hCounts, hRest⟩ := switch_cycles (A ⊔ A') (Or.inl hxy) hDom C hC' d hd
    (fun z _ _ hp => switchDemand_adj hp)
  exact restore_switched_cover A B x y hState hxy C D hBudget hC hParity hProtected hD hCounts hRest

theorem fan_cover_from_universal_base
    (hBase : ∀ (V : Type) [Fintype V] [DecidableEq V] (A B : SimpleGraph V) (x : V),
      ValidRootState A B x → (∀ v ≠ x, A.Adj x v) → ProtectedOddCover A B x) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (A : SimpleGraph V),
      A.Connected → (∀ v, Even ((A.neighborSet v).ncard)) →
      ∃ T : Finset (Finset (Sym2 V)),
        (∀ s ∈ T, ∃ (u : V) (p : A.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
        (∀ e ∈ A.edgeSet, ∃ s ∈ T, e ∈ s) ∧ T.card ≤ Fintype.card V / 2 := by
  intro V _ _ A hConnected hEven
  obtain ⟨x⟩ := hConnected.nonempty
  apply ordinary_of_protected_cover A x
  exact protected_cover_from_switch x (fun A B h => hBase V A B x h) (protected_switch_step x)
    A A ⟨hConnected, le_rfl, fun _ _ _ _ => Iff.rfl, hEven⟩

theorem universal_base_from_lovasz {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) (x : V) (hState : ValidRootState A B x)
    (hUniversal : ∀ v ≠ x, A.Adj x v) : ProtectedOddCover A B x := by
  classical
  obtain ⟨k, P, hd, hc, hk⟩ := OAI.ErdosGallai.Lovasz.path_cycle_partition (deleteRoot A x)
  have hBound : 2 * k ≤ Fintype.card (RootComplement x) := hk.trans (by
    unfold OAI.ErdosGallai.Lovasz.activeOrder
    exact Finset.card_le_univ _)
  exact protected_cover_at_universal_root_of_walks A B x hUniversal hState.2.2.1
    (fun k S hc ha => OMA.Erdos184FanParity.cycle_family_parity_complete A B x k S hc hState.2.2.2 ha)
    (fun i => ⟨(P i).start, (P i).finish, (P i).walk⟩) (fun i => (P i).simple) hd hc hBound

theorem fan_cycle_bound :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (A : SimpleGraph V),
      A.Connected → (∀ v, Even ((A.neighborSet v).ncard)) →
      ∃ T : Finset (Finset (Sym2 V)),
        (∀ s ∈ T, ∃ (u : V) (p : A.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
        (∀ e ∈ A.edgeSet, ∃ s ∈ T, e ∈ s) ∧ T.card ≤ Fintype.card V / 2 :=
  fan_cover_from_universal_base (fun _ _ _ A B x h hu => universal_base_from_lovasz A B x h hu)

end OMA.Erdos184FanInduction

/-
The covering bound follows from Fan's theorem for connected Eulerian graphs.
Add a length-two path along each edge outside a maximal even subgraph. These
edges form a forest, so the number of vertices grows to at most `2*n - 1`.
Suppress the added vertices of each cycle and assemble the connected components.
-/

open SimpleGraph

namespace OMA.Erdos184Cover

def IsPiece {V : Type} [DecidableEq V] (G : SimpleGraph V) (s : Finset (Sym2 V)) : Prop :=
  (∃ e ∈ G.edgeSet, s = {e}) ∨ ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset

def Covers {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset (Finset (Sym2 V))) : Prop :=
  (∀ s ∈ S, IsPiece G s) ∧ (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s)

theorem isPiece_image {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    {s : Finset (Sym2 V)} (hs : IsPiece G s) : IsPiece H (s.image (Sym2.map f)) := by
  rcases hs with ⟨e, he, rfl⟩ | ⟨u, p, hp, rfl⟩
  · exact Or.inl ⟨_, f.map_mem_edgeSet he, Finset.image_singleton _ _⟩
  · refine Or.inr ⟨f u, p.map f, hp.map hf, ?_⟩
    rw [Walk.edges_map]
    ext e
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]

theorem sum_card_component {V : Type} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] [∀ c : G.ConnectedComponent, Fintype c] :
    (∑ c : G.ConnectedComponent, Fintype.card c) = Fintype.card V := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)

/-- A connected-case covering theorem gives the stated budget on all graphs. -/
theorem of_connected
    (h : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → ∃ S, Covers G S ∧ S.card + 1 ≤ Fintype.card V) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ S, Covers G S ∧ S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  intro V _ _ G
  classical
  choose S hcover hsize using fun (c : G.ConnectedComponent) =>
    h c c.toSimpleGraph c.connected_toSimpleGraph
  let L (c : G.ConnectedComponent) : Finset (Finset (Sym2 V)) :=
    (S c).image (fun s => s.image (Sym2.map c.toSimpleGraph_hom))
  let U := Finset.univ.biUnion L
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · intro s hs
    obtain ⟨c, _, hcs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hcs
    exact isPiece_image c.toSimpleGraph_hom Subtype.val_injective ((hcover c).1 t ht)
  · intro e he
    induction e using Sym2.ind with
    | h v w =>
      have hvw : G.Adj v w := by simpa using he
      let c := G.connectedComponentMk v
      let v' : c := ⟨v, rfl⟩
      let w' : c := ⟨w, c.mem_supp_of_adj_mem_supp (u := v) rfl hvw⟩
      have he' : s(v', w') ∈ c.toSimpleGraph.edgeSet := hvw
      obtain ⟨t, ht, he'⟩ := (hcover c).2 _ he'
      refine ⟨t.image (Sym2.map c.toSimpleGraph_hom), ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr
          ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
      · exact Finset.mem_image.mpr ⟨s(v', w'), he', rfl⟩
  · have hcardU : U.card ≤ ∑ c : G.ConnectedComponent, (S c).card :=
      Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun _ _ => Finset.card_image_le
    calc
      U.card + Nat.card G.ConnectedComponent ≤
          (∑ c : G.ConnectedComponent, (S c).card) + (∑ _ : G.ConnectedComponent, 1) := by
        simpa [Nat.card_eq_fintype_card] using hcardU
      _ = ∑ c : G.ConnectedComponent, ((S c).card + 1) := Finset.sum_add_distrib.symm
      _ ≤ ∑ c : G.ConnectedComponent, Fintype.card c :=
        Finset.sum_le_sum fun c _ => hsize c
      _ = Fintype.card V := sum_card_component G

private def augmentAdj {V : Type} (G F : SimpleGraph V) :
    V ⊕ F.edgeSet → V ⊕ F.edgeSet → Prop
  | .inl v, .inl w => G.Adj v w
  | .inl v, .inr e => v ∈ (e.val : Sym2 V)
  | .inr e, .inl v => v ∈ (e.val : Sym2 V)
  | .inr _, .inr _ => False

/-- Keep every edge of `G` and add a two-edge path for each edge of `F`. -/
def augment {V : Type} (G F : SimpleGraph V) : SimpleGraph (V ⊕ F.edgeSet) where
  Adj := augmentAdj G F
  symm := by
    constructor
    intro u v huv
    cases u <;> cases v
    · exact G.adj_symm huv
    · exact huv
    · exact huv
    · exact huv
  loopless := by
    constructor
    intro v hv
    cases v with
    | inl u => exact G.loopless.irrefl u hv
    | inr e => exact hv

@[simp] theorem augment_adj_old_old {V : Type} (G F : SimpleGraph V) (v w : V) :
    (augment G F).Adj (.inl v) (.inl w) ↔ G.Adj v w := Iff.rfl

@[simp] theorem augment_adj_old_new {V : Type} (G F : SimpleGraph V) (v : V) (e : F.edgeSet) :
    (augment G F).Adj (.inl v) (.inr e) ↔ v ∈ (e.val : Sym2 V) := Iff.rfl

@[simp] theorem augment_adj_new_old {V : Type} (G F : SimpleGraph V) (e : F.edgeSet) (v : V) :
    (augment G F).Adj (.inr e) (.inl v) ↔ v ∈ (e.val : Sym2 V) := Iff.rfl

@[simp] theorem augment_not_adj_new_new {V : Type} (G F : SimpleGraph V) (e f : F.edgeSet) :
    ¬ (augment G F).Adj (.inr e) (.inr f) := id

def augmentHom {V : Type} (G F : SimpleGraph V) : G →g augment G F where
  toFun := Sum.inl
  map_rel' := id

private def oldNeighborEquiv {V : Type} (G F : SimpleGraph V) (v : V) :
    (augment G F).neighborSet (.inl v) ≃ (G.neighborSet v ⊕ F.incidenceSet v) where
  toFun
    | ⟨.inl w, hw⟩ => .inl ⟨w, hw⟩
    | ⟨.inr e, he⟩ => .inr ⟨e.val, ⟨e.property, he⟩⟩
  invFun
    | .inl w => ⟨.inl w.val, w.property⟩
    | .inr e => ⟨.inr ⟨e.val, e.property.1⟩, e.property.2⟩
  left_inv := by rintro ⟨w, hw⟩; cases w <;> rfl
  right_inv := by intro w; cases w <;> rfl

private def newNeighborEquiv {V : Type} (G F : SimpleGraph V) (e : F.edgeSet) :
    (augment G F).neighborSet (.inr e) ≃ {v : V // v ∈ (e.val : Sym2 V)} where
  toFun
    | ⟨.inl v, hv⟩ => ⟨v, hv⟩
    | ⟨.inr _, hf⟩ => False.elim hf
  invFun v := ⟨.inl v.val, v.property⟩
  left_inv := by
    rintro ⟨w, hw⟩
    cases w with
    | inl => rfl
    | inr => exact False.elim hw
  right_inv := by intro v; rfl

theorem augment_ncard_old {V : Type} [Finite V] (G F : SimpleGraph V) (v : V) :
    ((augment G F).neighborSet (.inl v)).ncard =
      (G.neighborSet v).ncard + (F.neighborSet v).ncard := by
  classical
  simp only [← Nat.card_coe_set_eq]
  rw [Nat.card_congr (oldNeighborEquiv G F v), Nat.card_sum,
    Nat.card_congr (F.incidenceSetEquivNeighborSet v)]

theorem augment_ncard_new {V : Type} (G F : SimpleGraph V) (e : F.edgeSet) :
    ((augment G F).neighborSet (.inr e)).ncard = 2 := by
  classical
  rw [← Nat.card_coe_set_eq, Nat.card_congr (newNeighborEquiv G F e)]
  have h : (↑e.val.toFinset : Set V) = {v | v ∈ (e.val : Sym2 V)} := by ext v; simp
  change Nat.card ↥{v : V | v ∈ (e.val : Sym2 V)} = 2
  rw [← h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact e.val.card_toFinset_of_not_isDiag (F.not_isDiag_of_mem_edgeSet e.property)

theorem augment_even {V : Type} [Finite V] {G E : SimpleGraph V} (hEG : E ≤ G)
    (hE : ∀ v, Even ((E.neighborSet v).ncard)) (z : V ⊕ (G \ E).edgeSet) :
    Even (((augment G (G \ E)).neighborSet z).ncard) := by
  cases z with
  | inr e => rw [augment_ncard_new]; exact even_two
  | inl v =>
    let F := G \ E
    have hsup : E ⊔ F = G := sup_sdiff_cancel_right hEG
    have hdisj : Disjoint E F := disjoint_sdiff_self_right
    have hdegree : (G.neighborSet v).ncard = (E.neighborSet v).ncard + (F.neighborSet v).ncard := by
      rw [← hsup, neighborSet_sup, Set.ncard_union_eq (disjoint_neighborSet.mpr hdisj v)]
    rw [augment_ncard_old, hdegree, add_assoc]
    exact (hE v).add ⟨_, rfl⟩

theorem augment_connected {V : Type} {G : SimpleGraph V} (hG : G.Connected)
    (F : SimpleGraph V) : (augment G F).Connected := by
  have hold (z : V ⊕ F.edgeSet) : ∃ v : V, (augment G F).Reachable z (.inl v) := by
    cases z with
    | inl v => exact ⟨v, Reachable.rfl⟩
    | inr e =>
      have he (s : Sym2 V) : ∃ v, v ∈ s := by
        induction s using Sym2.ind with
        | h v w => exact ⟨v, by simp⟩
      obtain ⟨v, hv⟩ := he e.val
      exact ⟨v, ((augment_adj_new_old G F e v).mpr hv).reachable⟩
  refine { preconnected := ?_, nonempty := hG.nonempty.map Sum.inl }
  intro x y
  obtain ⟨u, hu⟩ := hold x
  obtain ⟨v, hv⟩ := hold y
  exact hu.trans (((hG.preconnected u v).map (augmentHom G F)).trans hv.symm)

def IsCyclePiece {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (s : Finset (Sym2 V)) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset

/-- The ordinary covering consequence of Fan's theorem suffices for the reduction. -/
def FanCycleBound : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → (∀ v, Even ((G.neighborSet v).ncard)) →
    ∃ S : Finset (Finset (Sym2 V)),
      (∀ s ∈ S, IsCyclePiece G s) ∧ (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧
      S.card ≤ Fintype.card V / 2

/-- Every augmented cycle descends to a single piece containing its original edges. -/
def AugmentedCyclesSuppress : Prop :=
  ∀ (V : Type) [DecidableEq V] (G F : SimpleGraph V), F ≤ G →
    ∀ (u : V ⊕ F.edgeSet) (p : (augment G F).Walk u u), p.IsCycle →
      ∃ s, IsPiece G s ∧ ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ p.edges → e ∈ s

def AugmentedPathsCompress : Prop :=
  ∀ (V : Type) [DecidableEq V] (G F : SimpleGraph V), F ≤ G →
    ∀ (u v : V) (p : (augment G F).Walk (.inl u) (.inl v)), p.IsPath →
      ∃ q : G.Walk u v, q.IsPath ∧ ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ p.edges → e ∈ q.edges

private theorem compress_path_aux {V : Type} (G F : SimpleGraph V) (hFG : F ≤ G)
    (u v : V) (p : (augment G F).Walk (.inl u) (.inl v)) (hp : p.IsPath) :
    ∃ q : G.Walk u v, q.IsPath ∧
      List.Sublist (q.support.map Sum.inl) p.support ∧
      ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ p.edges → e ∈ q.edges := by
  have key : ∀ (n : ℕ) (u v : V)
      (p : (augment G F).Walk (.inl u) (.inl v)), p.length = n → p.IsPath →
      ∃ q : G.Walk u v, q.IsPath ∧
        List.Sublist (q.support.map Sum.inl) p.support ∧
        ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ p.edges → e ∈ q.edges := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u v p hlen hp
      cases p with
      | nil => exact ⟨Walk.nil, Walk.IsPath.nil, by simp, by simp⟩
      | @cons _ z _ h p =>
        have hp' := (Walk.cons_isPath_iff h p).mp hp
        cases z with
        | inl w =>
          have hG : G.Adj u w := h
          have hlt : p.length < n := by simp only [Walk.length_cons] at hlen; omega
          obtain ⟨q, hq, hsub, hedge⟩ := ih p.length hlt w v p rfl hp'.1
          refine ⟨Walk.cons hG q, hq.cons ?_, ?_, ?_⟩
          · intro hu
            exact hp'.2 (hsub.subset (List.mem_map.mpr ⟨u, hu, rfl⟩))
          · simpa only [Walk.support_cons, List.map_cons] using hsub.cons_cons (Sum.inl u)
          · intro e he
            simp only [Walk.edges_cons, List.mem_cons] at he ⊢
            rcases he with he | he
            · left
              exact (Sym2.map.injective Sum.inl_injective) he
            · exact Or.inr (hedge e he)
        | inr f =>
          cases p with
          | @cons _ z _ h₂ p =>
            cases z with
            | inr f₂ => exact (augment_not_adj_new_new G F f f₂ h₂).elim
            | inl w =>
              have htail := hp'.1.of_cons
              have huw : u ≠ w := by
                intro huw
                subst w
                exact hp'.2 (by simp)
              have huwAdj : G.Adj u w := hFG
                (F.adj_of_mem_incidenceSet huw ⟨f.property, h⟩ ⟨f.property, h₂⟩)
              have hlt : p.length < n := by simp only [Walk.length_cons] at hlen; omega
              obtain ⟨q, hq, hsub, hedge⟩ := ih p.length hlt w v p rfl htail
              refine ⟨Walk.cons huwAdj q, hq.cons ?_, ?_, ?_⟩
              · intro hu
                apply hp'.2
                exact List.mem_cons_of_mem _ (hsub.subset (List.mem_map.mpr ⟨u, hu, rfl⟩))
              · simpa only [Walk.support_cons, List.map_cons] using
                  (List.Sublist.cons (Sum.inr f) hsub).cons_cons (Sum.inl u)
              · intro e he
                simp only [Walk.edges_cons, List.mem_cons] at he ⊢
                rcases he with he | he | he
                · induction e using Sym2.ind with
                  | h a b => simp [Sym2.map_mk] at he
                · induction e using Sym2.ind with
                  | h a b => simp [Sym2.map_mk] at he
                · exact Or.inr (hedge e he)
  exact key p.length u v p rfl hp

theorem paths_compress : AugmentedPathsCompress := by
  intro V _ G F hFG u v p hp
  obtain ⟨q, hq, _, he⟩ := compress_path_aux G F hFG u v p hp
  exact ⟨q, hq, he⟩

private theorem close_path_isPiece {V : Type} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (p : G.Walk v u) (hp : p.IsPath) :
    ∃ s, IsPiece G s ∧ s(u,v) ∈ s ∧ ∀ e ∈ p.edges, e ∈ s := by
  by_cases he : s(u,v) ∈ p.edges
  · refine ⟨{s(u,v)}, Or.inl ⟨s(u,v), huv, rfl⟩, Finset.mem_singleton_self _, ?_⟩
    have hp' := hp.eq_adj_toWalk_of_mem_edges (by simpa only [Sym2.eq_swap] using he :
      s(v,u) ∈ p.edges)
    intro e he
    simpa [hp', Sym2.eq_swap] using he
  · let c := Walk.cons huv p
    have hc : c.IsCycle := (Walk.cons_isCycle_iff p huv).mpr ⟨hp, he⟩
    refine ⟨c.edges.toFinset, Or.inr ⟨u, c, hc, rfl⟩, by simp [c], ?_⟩
    intro e he
    exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ he)

private theorem old_edge_ne_mixed {V : Type} {F : SimpleGraph V} (e : Sym2 V)
    (v : V) (f : F.edgeSet) : Sym2.map Sum.inl e ≠ s(Sum.inl v, Sum.inr f) := by
  induction e using Sym2.ind with
  | h x y => simp [Sym2.map_mk]

private theorem cycle_has_old_vertex {V : Type} {G F : SimpleGraph V} {z : V ⊕ F.edgeSet}
    (p : (augment G F).Walk z z) (hp : p.IsCycle) : ∃ u : V, Sum.inl u ∈ p.support := by
  cases z with
  | inl u => exact ⟨u, p.start_mem_support⟩
  | inr e =>
    cases p with
    | nil => exact (Walk.not_isCycle_nil hp).elim
    | @cons _ z _ hadj q =>
      cases z with
      | inl u => exact ⟨u, by simp⟩
      | inr f => exact (augment_not_adj_new_new G F e f hadj).elim

theorem suppress_of_path_compression (hCompress : AugmentedPathsCompress) :
    AugmentedCyclesSuppress := by
  intro V _ G F hFG z p hp
  have hold (u : V) (c : (augment G F).Walk (.inl u) (.inl u)) (hc : c.IsCycle) :
      ∃ s, IsPiece G s ∧ ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ c.edges → e ∈ s := by
    cases c with
    | nil => exact (Walk.not_isCycle_nil hc).elim
    | @cons _ z _ h q =>
      obtain ⟨hq, hnone⟩ := (Walk.cons_isCycle_iff q h).mp hc
      cases z with
      | inl v =>
        obtain ⟨r, hr, hpres⟩ := hCompress V G F hFG v u q hq
        obtain ⟨s, hs, hedge, hcover⟩ := close_path_isPiece
          ((augment_adj_old_old G F u v).mp h) r hr
        refine ⟨s, hs, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · have he' : e = s(u,v) := Sym2.map.injective Sum.inl_injective he
          exact he' ▸ hedge
        · exact hcover e (hpres e he)
      | inr f =>
        cases q with
        | @cons _ z _ h' q' =>
          cases z with
          | inr g => exact (augment_not_adj_new_new G F f g h').elim
          | inl v =>
            have hne : u ≠ v := by
              intro eq
              subst v
              exact hnone (List.mem_cons.mpr (Or.inl Sym2.eq_swap))
            have huv : G.Adj u v := hFG (F.adj_of_mem_incidenceSet hne
              ⟨f.property, (augment_adj_old_new G F u f).mp h⟩
              ⟨f.property, (augment_adj_new_old G F f v).mp h'⟩)
            have hq' : q'.IsPath := hq.of_cons
            obtain ⟨r, hr, hpres⟩ := hCompress V G F hFG v u q' hq'
            obtain ⟨s, hs, _, hcover⟩ := close_path_isPiece huv r hr
            refine ⟨s, hs, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with he | he
            · exact (old_edge_ne_mixed e u f he).elim
            rcases List.mem_cons.mp he with he | he
            · exact (old_edge_ne_mixed e v f (he.trans Sym2.eq_swap)).elim
            · exact hcover e (hpres e he)
  obtain ⟨u, hu⟩ := cycle_has_old_vertex p hp
  obtain ⟨s, hs, hpres⟩ := hold u (p.rotate (.inl u) hu) (hp.rotate hu)
  exact ⟨s, hs, fun e he => hpres e ((p.rotate_edges (.inl u) hu).perm.mem_iff.mpr he)⟩

theorem cover_of_augment (hSuppress : AugmentedCyclesSuppress)
    {V : Type} [DecidableEq V] {G F : SimpleGraph V} (hFG : F ≤ G)
    (S : Finset (Finset (Sym2 (V ⊕ F.edgeSet))))
    (hgood : ∀ s ∈ S, IsCyclePiece (augment G F) s)
    (hcover : ∀ e ∈ (augment G F).edgeSet, ∃ s ∈ S, e ∈ s) :
    ∃ T, Covers G T ∧ T.card ≤ S.card := by
  classical
  have hpiece (t : S) : ∃ s, IsPiece G s ∧
      ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ t.val → e ∈ s := by
    obtain ⟨u, p, hp, ht⟩ := hgood t.val t.property
    obtain ⟨s, hs, hpreserve⟩ := hSuppress V G F hFG u p hp
    refine ⟨s, hs, ?_⟩
    intro e he
    exact hpreserve e (List.mem_toFinset.mp (ht ▸ he))
  choose f hf using hpiece
  refine ⟨S.attach.image f, ⟨?_, ?_⟩, Finset.card_image_le.trans_eq Finset.card_attach⟩
  · intro s hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    exact (hf t).1
  · intro e he
    have hplus : Sym2.map Sum.inl e ∈ (augment G F).edgeSet := (augmentHom G F).map_mem_edgeSet he
    obtain ⟨t, ht, het⟩ := hcover _ hplus
    exact ⟨f ⟨t, ht⟩, Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩,
      (hf ⟨t, ht⟩).2 e het⟩

open scoped Classical in
private theorem forest_card_with_vertex {V : Type} [Fintype V] [Nonempty V]
    (F : SimpleGraph V) (hF : F.IsAcyclic) : F.edgeFinset.card + 1 ≤ Fintype.card V := by
  obtain ⟨T, hFT, _, hT⟩ :=
    (connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic (le_top : F ≤ ⊤) hF
  have hcard : F.edgeFinset.card ≤ T.edgeFinset.card :=
    Finset.card_le_card (edgeFinset_mono hFT)
  have hTreeCard := hT.card_edgeFinset
  omega

private lemma degree_eq_ncard_neighborSet {V : Type} (G : SimpleGraph V) (x : V)
    [Fintype (G.neighborSet x)] : G.degree x = (G.neighborSet x).ncard :=
  (Set.ncard_eq_toFinset_card' _).symm

open scoped Classical in
private lemma cycle_spanning_even {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (x : V) : Even (p.toSubgraph.spanningCoe.degree x) := by
  let C : SimpleGraph V := p.toSubgraph.spanningCoe
  have hEdges : C.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [C, mem_edgeFinset, Subgraph.edgeSet_spanningCoe,
      Walk.mem_edges_toSubgraph, List.mem_toFinset]
  have hParity := (hp.isTrail.even_countP_edges_iff x).2 (fun h => (h rfl).elim)
  change Even (C.degree x)
  rw [← C.card_incidenceFinset_eq_degree, C.incidenceFinset_eq_filter, hEdges]
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter] at hParity
  change Even (Multiset.filter (fun e => x ∈ e) (p.edges.toFinset.val)).card
  rwa [List.toFinset_val, List.dedup_eq_self.mpr hp.edges_nodup]

open scoped Classical in
theorem exists_even_with_acyclic_sdiff {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∃ E ≤ G, (∀ x, Even ((E.neighborSet x).ncard)) ∧ (G \ E).IsAcyclic := by
  let candidates := (Finset.univ : Finset (SimpleGraph V)).filter
    (fun E => E ≤ G ∧ ∀ x, Even (E.degree x))
  have hcandidates : candidates.Nonempty := ⟨⊥, by simp [candidates]⟩
  obtain ⟨E, hE, maximal⟩ := Finset.exists_max_image candidates
    (fun K => K.edgeSet.ncard) hcandidates
  obtain ⟨hEG, hEeven⟩ : E ≤ G ∧ ∀ x, Even (E.degree x) := (Finset.mem_filter.mp hE).2
  refine ⟨E, hEG, fun x => degree_eq_ncard_neighborSet E x ▸ hEeven x, ?_⟩
  intro v p hp
  let C : SimpleGraph V := p.toSubgraph.spanningCoe
  have hC : C ≤ G \ E := p.toSubgraph.spanningCoe_le
  have hDisj : Disjoint E C := disjoint_sdiff_self_right.mono_right hC
  have hSup : E ⊔ C ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, sup_le hEG (hC.trans sdiff_le), ?_⟩
    intro x
    rw [degree_eq_ncard_neighborSet, neighborSet_sup,
      Set.ncard_union_eq (disjoint_neighborSet.mpr hDisj x)]
    simpa only [degree_eq_ncard_neighborSet] using
      (hEeven x).add (cycle_spanning_even p hp x)
  have hCne : C ≠ ⊥ := by
    have hl : p.edges ≠ [] := fun he => hp.not_nil (Walk.edges_eq_nil.mp he)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges hl
    have he' : e ∈ C.edgeSet := by
      simp only [C, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph, he]
    intro hz
    simp [hz] at he'
  have hStrict : E < E ⊔ C := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hCE : C ≤ E := he ▸ le_sup_right
    exact hCne (disjoint_self.mp (hDisj.mono_left hCE))
  exact (not_lt_of_ge (maximal _ hSup))
    (Set.ncard_lt_ncard (edgeSet_ssubset_edgeSet.mpr hStrict) (Set.toFinite _))

/-- Pyber's covering bound follows from the Eulerian covering bound and cycle suppression. -/
theorem of_eulerian_cover (hFan : FanCycleBound) (hSuppress : AugmentedCyclesSuppress) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ S, Covers G S ∧ S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  apply of_connected
  intro V _ _ G hconn
  classical
  obtain ⟨E, hEG, hEeven, hforest⟩ := exists_even_with_acyclic_sdiff G
  let F := G \ E
  have hFcard : Fintype.card F.edgeSet + 1 ≤ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card]
    have hcard := @forest_card_with_vertex V _ hconn.nonempty F hforest
    simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard
  obtain ⟨S, hS, hcover, hcard⟩ := hFan (V ⊕ F.edgeSet) (augment G F)
    (augment_connected hconn F) (augment_even hEG hEeven)
  obtain ⟨T, hT, hTcard⟩ := cover_of_augment hSuppress (show F ≤ G from sdiff_le) S hS hcover
  refine ⟨T, hT, ?_⟩
  rw [Fintype.card_sum] at hcard
  omega

theorem of_eulerian_cover_and_paths (hFan : FanCycleBound) (hCompress : AugmentedPathsCompress) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ S, Covers G S ∧ S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V :=
  of_eulerian_cover hFan (suppress_of_path_compression hCompress)


end OMA.Erdos184Cover

/-
# From finite edge-piece covers to Pyber's subgraph cover

Credit: @Heart-galaxy
The conversion and `piece_of_item` follow the Apache-2.0 reduction by @ivillar.
The helpers `edge_card_eq_ncard`, `coe_edge_card`, and `cycle_subgraph_good`
were originally reused there from @Genbox's proof of the n-log-n variant (PR #720).
No contraction hypothesis or theorem with an unproved body is used.
-/

namespace OMA.Erdos184PyberGeneral

open SimpleGraph
open scoped Classical
lemma edge_card_eq_ncard {V : Type} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : G.edgeFinset.card = G.edgeSet.ncard := by
  exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm

lemma coe_edge_card {V : Type} [Fintype V] (G : SimpleGraph V) (H : G.Subgraph) :
    H.coe.edgeFinset.card = H.edgeSet.ncard := by
  rw [edge_card_eq_ncard, ← H.image_coe_edgeSet_coe]
  exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm

lemma cycle_subgraph_good {V : Type} [Fintype V] (G : SimpleGraph V)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : Erdos184.IsCycleOrEdge p.toSubgraph.coe := by
  apply Or.inl
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  intro w
  rw [Subgraph.coe_degree]
  change Fintype.card (p.toSubgraph.neighborSet (w : V)) = 2
  rw [Set.fintypeCard_eq_ncard]
  exact hp.ncard_neighborSet_toSubgraph_eq_two ((Walk.mem_verts_toSubgraph p).mp w.property)

lemma piece_of_item {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (s : Finset (Sym2 V))
    (hs : (∃ e ∈ G.edgeSet, s = {e}) ∨
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) :
    ∃ H : G.Subgraph, Erdos184.IsCycleOrEdge H.coe ∧ H.edgeSet = (s : Set (Sym2 V)) := by
  rcases hs with ⟨e, he, rfl⟩ | ⟨u, p, hp, rfl⟩
  · induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := by simpa using he
      have hH : (G.subgraphOfAdj hab).edgeSet = {s(a, b)} := by simp
      have hcount : (G.subgraphOfAdj hab).edgeSet.ncard = 1 := by
        rw [hH, Set.ncard_singleton]
      exact ⟨G.subgraphOfAdj hab, Or.inr ((coe_edge_card G _).trans hcount), by rw [hH]; simp⟩
  · refine ⟨p.toSubgraph, cycle_subgraph_good G p hp, ?_⟩
    rw [Walk.edgeSet_toSubgraph]
    ext e
    simp


/-- Edge-piece covers with a component-corrected vertex budget. -/
def ComponentCoverBound : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ S : Finset (Finset (Sym2 V)),
      (∀ s ∈ S, (∃ e ∈ G.edgeSet, s = {e}) ∨
        ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s = p.edges.toFinset) ∧
      (∀ e ∈ G.edgeSet, ∃ s ∈ S, e ∈ s) ∧
      S.card + Nat.card G.ConnectedComponent ≤ Fintype.card V

/-- The component-corrected bound implies the original Pyber covering target. -/
theorem covering_of_component_bound (hbound : ComponentCoverBound) :
    type_of% @Erdos184.erdos_184.variants.covering := by
  intro V _ _ _ G
  obtain ⟨S, hS, hcov, hcard⟩ := hbound V G
  have hex : ∀ s ∈ S, ∃ H : G.Subgraph,
      Erdos184.IsCycleOrEdge H.coe ∧ H.edgeSet = (s : Set (Sym2 V)) :=
    fun s hs => piece_of_item G s (hS s hs)
  choose f hf using hex
  have hfinC : Finite G.ConnectedComponent :=
    Finite.of_surjective G.connectedComponentMk (fun c => Quot.exists_rep c)
  have hneC : Nonempty G.ConnectedComponent :=
    ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  have hpos : 0 < Nat.card G.ConnectedComponent := Nat.card_pos
  refine ⟨S.attach.image (fun s => f s.1 s.2), ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hH
    exact (hf s.1 s.2).1
  · ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨H, -, he⟩
      exact H.edgeSet_subset he
    · intro he
      obtain ⟨s, hs, hes⟩ := hcov e he
      refine ⟨f s hs, Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      rw [(hf s hs).2]
      exact hes
  · have hle : (S.attach.image (fun s => f s.1 s.2)).card ≤ S.card :=
      Finset.card_image_le.trans_eq Finset.card_attach
    have hnat : (S.attach.image (fun s => f s.1 s.2)).card + 1 ≤ Fintype.card V := by omega
    have hreal : (((S.attach.image (fun s => f s.1 s.2)).card + 1 : ℕ) : ℝ) ≤
        (Fintype.card V : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal
    linarith

end OMA.Erdos184PyberGeneral

theorem OMA.solution : type_of% @Erdos184.erdos_184.variants.covering := by
  apply OMA.Erdos184PyberGeneral.covering_of_component_bound
  intro V _ _ G
  obtain ⟨S, hS, hsize⟩ := OMA.Erdos184Cover.of_eulerian_cover_and_paths
    OMA.Erdos184FanInduction.fan_cycle_bound OMA.Erdos184Cover.paths_compress V G
  exact ⟨S, hS.1, hS.2, hsize⟩
