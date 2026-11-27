import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1
import Mathlib

/-! A finite rainbow coloring embeds a large subfamily into words. -/

/-
Ported from OpenAI math, commit 3344da59991ed94f9ba711217b29c1d760badfa6.
The source modules are Basic, ColorCount, Rounding and Transfer in
lean/OAI/Combinatorics/Sunflower. Changes inline the dependency modules, retain
the coloring and embedding arguments and pin the resulting statement to H2.
Licensed under the Apache License, Version 2.0, reproduced below.
-/

/- # Sunflowers in set families and in word families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {ι I α β : Type*}

/-- Every entry of the tuple has the same value. This includes the empty tuple. -/
def IsConstant (f : ι → β) : Prop :=
  ∀ i j, f i = f j

/-- One coordinate of a sunflower has either a common symbol or pairwise distinct symbols. -/
def Admissible (f : ι → β) : Prop :=
  IsConstant f ∨ Function.Injective f

/-- Each coordinate of the tuple of words is admissible. -/
def WordAdmissible (w : ι → I → β) : Prop :=
  ∀ c, Admissible (fun i => w i c)

/-- Every admissible ordered tuple of words in the family repeats one word. -/
def WordFree (r : ℕ) (W : Finset (I → β)) : Prop :=
  ∀ w : Fin r → I → β, (∀ i, w i ∈ W) → WordAdmissible w → IsConstant w

theorem WordAdmissible.isConstant_of_repeat {w : ι → I → β} (h : WordAdmissible w)
    {i j : ι} (hne : i ≠ j) (hw : w i = w j) : IsConstant w := by
  intro a b
  funext c
  rcases h c with hc | hc
  · exact hc a b
  · exact (hne (hc (congrFun hw c))).elim

theorem WordAdmissible.injective_of_not_isConstant {w : ι → I → β}
    (h : WordAdmissible w) (hn : ¬ IsConstant w) : Function.Injective w := by
  intro i j heq
  by_contra hne
  exact hn (h.isConstant_of_repeat hne heq)

/-- A family contains a subfamily of size `r` whose distinct members intersect in one
fixed core. The core can be empty. -/
def HasSunflower [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

theorem hasSunflower_of_indexed [DecidableEq α] {r : ℕ} {F : Finset (Finset α)}
    {w : Fin r → Finset α} (hmem : ∀ i, w i ∈ F) (hinj : Function.Injective w)
    {K : Finset α} (hcore : ∀ i j, i ≠ j → w i ∩ w j = K) : HasSunflower r F := by
  let e : Fin r ↪ Finset α := ⟨w, hinj⟩
  refine ⟨Finset.univ.map e, ?_, by simp, K, ?_⟩
  · intro A hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    exact hmem i
  · intro A hA B hB hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hB
    exact hcore i j (fun heq => hne (congrArg e heq))

end Sunflower
end Combinatorics
end OAI

/- # Counting rainbow members of uniform set families -/

open Finset

namespace OAI
namespace Combinatorics
namespace Sunflower

private noncomputable def extendColor {α : Type*} {k : ℕ} (hk : 0 < k)
    (U : Finset α) (f : U → Fin k) (x : α) : Fin k := by
  classical
  exact if h : x ∈ U then f ⟨x, h⟩ else ⟨0, hk⟩

/-- Fixing a bijection on a member of the family leaves all colors on its complement free. -/
private theorem card_good_colors {α : Type*} [DecidableEq α] {k : ℕ} (hk : 0 < k)
    (A U : Finset α) (hAU : A ⊆ U) (hA : A.card = k) :
    k.factorial * k ^ U.card ≤
      (univ.filter (fun f : U → Fin k =>
        Function.Bijective (fun x : A => extendColor hk U f x))).card * k ^ k := by
  classical
  let Good := fun f : U → Fin k => Function.Bijective (fun x : A => extendColor hk U f x)
  let join : (A ≃ Fin k) × ((U \ A : Finset α) → Fin k) → (U → Fin k) :=
    fun p u => if h : u.val ∈ A then p.1 ⟨u, h⟩
      else p.2 ⟨u, mem_sdiff.mpr ⟨u.property, h⟩⟩
  have hjoin (p) : Good (join p) := by
    change Function.Bijective (fun x : A => extendColor hk U (join p) x)
    convert p.1.bijective using 1
    funext x
    simp [extendColor, join, x.property, hAU x.property]
  have hinj : Function.Injective join := by
    intro p q h
    apply Prod.ext
    · apply Equiv.ext
      intro x
      have he := congrFun h (⟨x, hAU x.property⟩ : U)
      simpa [join, x.property] using he
    · funext x
      obtain ⟨hxU, hxA⟩ := mem_sdiff.mp x.property
      have he := congrFun h (⟨x, hxU⟩ : U)
      simpa [join, hxA] using he
  have hcount := Fintype.card_le_of_injective
    (fun p => (⟨join p, hjoin p⟩ : {f // Good f})) (fun _ _ h => hinj (congrArg Subtype.val h))
  have e : A ≃ Fin k := Fintype.equivFinOfCardEq (by simpa using hA)
  rw [Fintype.card_prod, Fintype.card_equiv e, Fintype.card_fun] at hcount
  simp only [Fintype.card_coe, hA, Fintype.card_fin] at hcount
  rw [Fintype.card_of_subtype (univ.filter Good) (by simp)] at hcount
  have hsum : (U \ A).card + k = U.card := hA ▸ card_sdiff_add_card_eq_card hAU
  calc
    k.factorial * k ^ U.card =
        (k.factorial * k ^ (U \ A).card) * k ^ k := by rw [← hsum, pow_add, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

/-- Some coloring retains at least the fraction `k! / k^k` of a finite uniform family. -/
theorem exists_rainbow_subfamily {α : Type*} {k : ℕ} (hk : 0 < k)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = k) :
    ∃ (c : α → Fin k) (G : Finset (Finset α)), G ⊆ F ∧
      (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
      F.card * k.factorial ≤ G.card * k ^ k := by
  classical
  let U : Finset α := F.biUnion id
  let Good := fun (c : U → Fin k) (A : Finset α) =>
    Function.Bijective (fun x : A => extendColor hk U c x)
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨c, _, hc⟩ := (univ : Finset (U → Fin k)).exists_max_image
    (fun c => (F.filter (Good c)).card) univ_nonempty
  refine ⟨extendColor hk U c, F.filter (Good c), filter_subset _ _, ?_, ?_⟩
  · exact fun _ hA => (mem_filter.mp hA).2
  · have hcount (A) (hA : A ∈ F) := card_good_colors hk A U
        (subset_biUnion_of_mem id hA) (hF A hA)
    have hswap :
        ∑ A ∈ F, (univ.filter (fun c => Good c A)).card =
          ∑ f : U → Fin k, (F.filter (Good f)).card := by
      simp only [card_filter]
      rw [sum_comm]
    have allColors : Fintype.card (U → Fin k) = k ^ U.card := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have htotal :
        F.card * (k.factorial * k ^ U.card) ≤
          (k ^ U.card * (F.filter (Good c)).card) * k ^ k := calc
      _ = ∑ _A ∈ F, k.factorial * k ^ U.card := by simp
      _ ≤ ∑ A ∈ F, (univ.filter (fun c => Good c A)).card * k ^ k :=
        sum_le_sum hcount
      _ = (∑ f : U → Fin k, (F.filter (Good f)).card) * k ^ k := by rw [← sum_mul, hswap]
      _ ≤ (∑ _f : U → Fin k, (F.filter (Good c)).card) * k ^ k :=
        Nat.mul_le_mul_right _ (sum_le_sum hc)
      _ = _ := by simp [allColors]
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < k ^ U.card from Nat.pow_pos hk)
    · simpa only [mul_left_comm, mul_assoc, mul_comm] using htotal

end Sunflower
end Combinatorics
end OAI

/- # Exponential bounds for coloring and word comparisons -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A uniformly random coloring with `k` colors is rainbow on a fixed `k`-set
with probability at least `3⁻ᵏ`. -/
theorem pow_self_le_three_pow_mul_factorial (k : ℕ) :
    k ^ k ≤ 3 ^ k * k.factorial := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hExp : Real.exp k ≤ (3 : ℝ) ^ k := by
    calc
      Real.exp k = (Real.exp 1) ^ k := by simp
      _ ≤ 3 ^ k := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h := (div_le_iff₀ hk).mp ((Real.pow_div_factorial_le_exp k (Nat.cast_nonneg k) k).trans hExp)
  exact_mod_cast h

end Sunflower
end Combinatorics
end OAI

/- # Transferring word bounds to uniform set families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- Ordering each rainbow member by color gives a word. A finite alphabet suffices
even when the ground type is infinite. -/
private theorem rainbow_encoding {α : Type*} [DecidableEq α] {k : ℕ}
    (G : Finset (Finset α)) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x)) :
    ∃ (n : ℕ) (encode : G → Fin k → Fin n) (decode : Fin n → α),
      Function.Injective decode ∧
      ∀ (A : G) (x : α), x ∈ (A : Finset α) ↔ decode (encode A (c x)) = x := by
  classical
  let U := G.biUnion id
  let e (A : G) : (A : Finset α) ≃ Fin k := Equiv.ofBijective _ (hc A A.property)
  let point (A : G) (j : Fin k) : U :=
    ⟨(e A).symm j, Finset.mem_biUnion.mpr ⟨A, A.property, ((e A).symm j).property⟩⟩
  let encode (A : G) (j : Fin k) := U.equivFin (point A j)
  let decode (u : Fin U.card) : α := U.equivFin.symm u
  have hdecode (A : G) (j : Fin k) :
      decode (encode A j) = ((e A).symm j).val := by
    simp [decode, encode, point]
  refine ⟨U.card, encode, decode, Subtype.val_injective.comp U.equivFin.symm.injective, ?_⟩
  intro A x
  rw [hdecode]
  constructor
  · intro hx
    have he : (e A) ⟨x, hx⟩ = c x := rfl
    rw [← he, Equiv.symm_apply_apply]
  · intro hx
    exact hx ▸ ((e A).symm (c x)).property

/-- A rainbow subfamily of a sunflower-free family embeds as an equally large
sunflower-free family of words over one finite alphabet. -/
theorem exists_word_family_of_rainbow {α : Type*} [DecidableEq α] {k r : ℕ}
    {G F : Finset (Finset α)} (hGF : G ⊆ F) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x))
    (hfree : ¬ HasSunflower r F) :
    ∃ (n : ℕ) (W : Finset (Fin k → Fin n)), W.card = G.card ∧ WordFree r W := by
  classical
  obtain ⟨n, encode, decode, hd, hmem⟩ := rainbow_encoding G c hc
  have hinj : Function.Injective encode := by
    intro A B hab
    apply Subtype.ext
    ext x
    rw [hmem, hmem, hab]
  let W := Finset.univ.image encode
  refine ⟨n, W, ?_, ?_⟩
  · simp [W, Finset.card_image_of_injective _ hinj]
  intro w hw hadm
  by_contra hnc
  have hwi := hadm.injective_of_not_isConstant hnc
  have hlift (i : Fin r) : ∃ A : G, encode A = w i := by
    obtain ⟨A, _, ha⟩ := Finset.mem_image.mp (hw i)
    exact ⟨A, ha⟩
  choose A hA using hlift
  have hAinj : Function.Injective (fun i => (A i : Finset α)) := by
    intro i j hij
    apply hwi
    rw [← hA i, ← hA j, Subtype.ext hij]
  have hAmem (i : Fin r) (x : α) :
      x ∈ (A i : Finset α) ↔ decode (w i (c x)) = x := by rw [← hA, hmem]
  let K := (G.biUnion id).filter fun x => ∀ i, x ∈ (A i : Finset α)
  apply hfree
  apply hasSunflower_of_indexed (K := K) (fun i => hGF (A i).property) hAinj
  intro i j hij
  ext x
  constructor
  · intro hx
    obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨A i, (A i).property, hi⟩, ?_⟩
    have heq : w i (c x) = w j (c x) :=
      hd (((hAmem i x).mp hi).trans ((hAmem j x).mp hj).symm)
    rcases hadm (c x) with hall | hdistinct
    · intro t
      exact (hAmem t x).mpr ((congrArg decode (hall t i)).trans ((hAmem i x).mp hi))
    · exact (hij (hdistinct heq)).elim
  · intro hx
    have hAll := (Finset.mem_filter.mp hx).2
    exact Finset.mem_inter.mpr ⟨hAll i, hAll j⟩

end Sunflower
end Combinatorics
end OAI

open OAI.Combinatorics.Sunflower

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1.H2 := by
  intro r k hk F hUniform hFree
  obtain ⟨c, G, hGF, hc, hCount⟩ := exists_rainbow_subfamily hk F hUniform
  obtain ⟨m, W, hCard, hW⟩ := exists_word_family_of_rainbow hGF c hc
    (show ¬ HasSunflower r F from hFree)
  refine ⟨m, W, ?_, hW⟩
  apply Nat.le_of_mul_le_mul_right (c := k.factorial) _ (Nat.factorial_pos k)
  calc
    F.card * k.factorial ≤ G.card * k ^ k := hCount
    _ ≤ G.card * (3 ^ k * k.factorial) :=
      Nat.mul_le_mul_left _ (pow_self_le_three_pow_mul_factorial k)
    _ = (3 ^ k * W.card) * k.factorial := by rw [hCard]; ac_rfl

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
