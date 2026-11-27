import OMAReductions.R_Erdos44_erdos_44_R1
import Mathlib

/- Port for Erdős 44. Adapted from the accepted Erdős 707 three-point source, Git blob 291047a3bd7e735992f922e1d8133a00eb112fe7. The last three Singer lemmas retain the original field size and cardinality. Original attribution and license follow. -/
-- Credit: @my-other-github-account; R1 reduction: @mucoucah.
/- Adapted from AxiomMath / StacksFrontier, revision 012108f61d7f92a6ffc35ec3f263b6da5d438125. Bundled and ported to the pinned Mathlib; license follows.
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
-- Bundled module: DivisorDegree707
section


namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]

private theorem swapCoeff (p : K[X][X]) (i j : ℕ) :
    ((Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => simp [ha, hb]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simpa only [map_add, coeff_add] using congrArg₂ (· + ·) ha hb
    | monomial m a =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hn : n = j <;> by_cases hm : m = i <;> simp [coeff_monomial, hn, hm]

private theorem swapDegree_iff (p : K[X][X]) (d : ℕ) :
    (Bivariate.swap p).natDegree ≤ d ↔ ∀ j, (p.coeff j).natDegree ≤ d := by
  constructor
  · intro h j
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [← swapCoeff, natDegree_le_iff_coeff_eq_zero.mp h i hi, coeff_zero]
  · intro h
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext j
    rw [swapCoeff, natDegree_le_iff_coeff_eq_zero.mp (h j) i hi, coeff_zero]

/-- Every divisor of a nonzero chart polynomial inherits its coordinate degree bounds. -/
theorem chartDivisorDegree {f g : K[X][X]} {d : ℕ} (hgf : g ∣ f) (hf : f ≠ 0)
    (hd : ∀ j, (f.coeff j).natDegree ≤ d) :
    g.natDegree ≤ f.natDegree ∧ ∀ j, (g.coeff j).natDegree ≤ d := by
  refine ⟨natDegree_le_of_dvd hgf hf, (swapDegree_iff g d).mp ?_⟩
  exact (natDegree_le_of_dvd (map_dvd Bivariate.swap hgf)
    (fun h => hf (Bivariate.swap.injective (h.trans (map_zero _).symm)))).trans
      ((swapDegree_iff f d).mpr hd)


end E707Partial

end

-- Bundled module: Descent707
section

namespace E707Partial
/-- Descent of the slope and intercept of the line through conjugate points. -/
theorem descendLine {F K : Type*} [Field F] [Field K] [Algebra F K]
    (σ : K →+* K) (fixed : ∀ k, σ k = k → ∃ a : F, algebraMap F K a = k)
    (X Y : K) (hX : σ X ≠ X)
    (det : (σ Y - Y) * (σ (σ X) - σ X) = (σ (σ Y) - σ Y) * (σ X - X)) :
    ∃ s t : F, Y = algebraMap F K s + algebraMap F K t * X := by
  let T := (σ Y - Y) / (σ X - X)
  have hd := sub_ne_zero.mpr hX
  have hd' := sub_ne_zero.mpr (σ.injective.ne hX)
  have hT : σ T = T := by
    unfold T
    rw [map_div₀, map_sub, map_sub]
    exact (div_eq_div_iff hd' hd).2 det.symm
  have he : T * (σ X - X) = σ Y - Y := div_mul_cancel₀ _ hd
  obtain ⟨t, ht⟩ := fixed _ hT
  obtain ⟨s, hs⟩ := fixed (Y - T * X) (by
    rw [map_sub, map_mul, hT]
    linear_combination -he)
  exact ⟨s, t, by rw [hs, ht]; ring⟩

end E707Partial

end

-- Bundled module: FrobLine707
section



namespace E707Partial
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Finite K] [Algebra F K]


theorem frobFixed (z : K) (hz : z ^ (Fintype.card F) = z) : ∃ a : F, algebraMap F K a = z := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed z).mpr
  intro f
  obtain ⟨n,rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).surjective f
  rw [AlgEquiv.coe_pow]
  exact Function.iterate_fixed (f := ⇑(FiniteField.frobeniusAlgEquivOfAlgebraic F K)) hz _

/-- A primitive projective point on Sawin's determinant locus yields the required line. -/
theorem frobLine {α : K} (hα : α ≠ 0) {u v N : ℕ} (hu : 0 < u) (hun : u < N)
    (hp : IsPrimitiveRoot (α ^ ((Fintype.card F)-1)) N)
    (det : ((α^v)^(Fintype.card F) - α^v) * (((α^u)^(Fintype.card F))^(Fintype.card F) - (α^u)^(Fintype.card F)) =
      (((α^v)^(Fintype.card F))^(Fintype.card F) - (α^v)^(Fintype.card F)) * ((α^u)^(Fintype.card F) - α^u)) :
    ∃ s t : F, α^v = algebraMap F K s + algebraMap F K t * α^u := by
  apply descendLine (FiniteField.frobeniusAlgHom F K).toRingHom (frobFixed (F := F)) _ _ _ det
  intro he
  change (α^u)^(Fintype.card F) = α^u at he
  have h1 : (α ^ ((Fintype.card F)-1)) ^ u = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    apply mul_right_cancel₀ (pow_ne_zero u hα)
    rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos, one_mul, he]
  exact (Nat.le_of_dvd hu (hp.dvd_of_pow_eq_one u h1)).not_gt hun

end E707Partial

end

-- Bundled module: Combine707
section



/- Exact split-fiber counts for finite cyclic groups. No point estimates. -/
namespace SplitFiber
open Finset
variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]

theorem roots_card {r : ℕ} (hr : r ≠ 0) (hd : r ∣ Fintype.card G) :
    (univ.filter fun x : G => x ^ r = 1).card = r := by
  rw [← sum_card_orderOf_eq_card_pow_eq_one hr]
  calc
    ∑ d ∈ r.divisors, (univ.filter fun x : G => orderOf x = d).card =
        ∑ d ∈ r.divisors, Nat.totient d := by
      apply sum_congr rfl
      intro d h
      exact IsCyclic.card_orderOf_eq_totient ((Nat.mem_divisors.mp h).1.trans hd)
    _ = r := Nat.sum_totient r

theorem fiber_card {r : ℕ} (hr : r ≠ 0) (hd : r ∣ Fintype.card G)
    {y : G} (hy : y ∈ Set.range (fun x : G => x ^ r)) :
    (univ.filter fun x : G => x ^ r = y).card = r := by
  calc
    _ = (univ.filter fun x : G => x ^ r = 1).card :=
      MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom r) hy ⟨1, by simp⟩
    _ = r := roots_card hr hd

theorem pullback_card {r : ℕ} (hr : r ≠ 0) (hd : r ∣ Fintype.card G)
    (s : Finset G) (hs : ∀ y ∈ s, y ∈ Set.range (fun x : G => x ^ r)) :
    (univ.filter fun x : G => x ^ r ∈ s).card = s.card * r := by
  rw [← sum_card_fiberwise_eq_card_filter]
  calc
    ∑ y ∈ s, (univ.filter fun x : G => x ^ r = y).card = ∑ _y ∈ s, r := by
      apply sum_congr rfl
      intro y hy
      exact fiber_card hr hd (hs y hy)
    _ = s.card * r := by simp

theorem split_count {r : ℕ} (hr : r.Prime) (hd : r ∣ Fintype.card G)
    (s : Finset G) (hs : ∀ y ∈ s, y ∈ Set.range (fun x : G => x ^ r)) :
    s.card = (univ.filter fun x : G => x ^ r ∈ s).card / r := by
  rw [pullback_card hr.ne_zero hd s hs, Nat.mul_div_cancel _ hr.pos]


open scoped Classical in
/-- In an arbitrary base subset, bad points mean those with a rational r-th root. -/
theorem bad_count {r : ℕ} (hr : r.Prime) (hd : r ∣ Fintype.card G)
    (s : Finset G) :
    (s.filter fun y => y ∈ Set.range (fun x : G => x ^ r)).card =
      (univ.filter fun x : G => x ^ r ∈ s).card / r := by
  classical
  have h := split_count hr hd
    (s.filter fun y => y ∈ Set.range (fun x : G => x ^ r))
    (fun y hy => (mem_filter.mp hy).2)
  simpa only [mem_filter, and_iff_left (Set.mem_range_self _)] using h

end SplitFiber





namespace E707Partial
open Finset
open scoped BigOperators
/-- A positive main term survives deleting all exceptional prime-index subsets. -/
theorem survive {G : Type*} [DecidableEq G] (s : Finset G) (P : Finset ℕ)
    (bad : ℕ → Finset G) (Q E : ℝ) (hQ : 0 ≤ Q)
    (hr : ∑ r ∈ P, (1 / (r : ℝ)) ≤ 1/16)
    (hc : ∀ r ∈ P, ((bad r).card : ℝ) ≤ Q * (1 / (r : ℝ)) + E)
    (hs : Q/16 + P.card * E < s.card) : ∃ x ∈ s, ∀ r ∈ P, x ∉ bad r := by
  by_contra! hf
  have hsub : s ⊆ P.biUnion bad := fun x hx => by
    obtain ⟨r, hr', hx'⟩ := hf x hx
    exact mem_biUnion.mpr ⟨r, hr', hx'⟩
  have hcard := (card_le_card hsub).trans (card_biUnion_le ..)
  have hreal : (s.card : ℝ) ≤ ∑ r ∈ P, ((bad r).card : ℝ) := by exact_mod_cast hcard
  have h := hreal.trans (sum_le_sum hc)
  rw [sum_add_distrib, ← mul_sum] at h
  simp only [sum_const, nsmul_eq_mul] at h
  nlinarith [mul_le_mul_of_nonneg_left hr hQ]
end E707Partial

namespace E707Partial
open Finset
open scoped Classical in
theorem survivePowers {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (s : Finset G) (Q E : ℝ) (hQ : 0 ≤ Q)
    (hr : ∑ r ∈ (Fintype.card G).primeFactors, (1 / (r : ℝ)) ≤ 1/16)
    (hc : ∀ r ∈ (Fintype.card G).primeFactors,
      ((univ.filter fun x : G => x^r ∈ s).card : ℝ) ≤ Q + r*E)
    (hs : Q/16 + (Fintype.card G).primeFactors.card * E < s.card) :
    ∃ x ∈ s, ∀ r ∈ (Fintype.card G).primeFactors, x ∉ Set.range (fun y : G => y^r) := by
  classical
  let bad (r : ℕ) := s.filter fun y => y ∈ Set.range (fun x : G => x ^ r)
  obtain ⟨x, hx, h⟩ := survive s _ bad Q E hQ hr (fun r hr' => by
    have hp := Nat.prime_of_mem_primeFactors hr'
    have hd := Nat.dvd_of_mem_primeFactors hr'
    have hh : (bad r).card * r ≤ (univ.filter fun x : G => x^r ∈ s).card := by
      dsimp [bad]; rw [SplitFiber.bad_count hp hd]; exact Nat.div_mul_le_self ..
    have h' : ((bad r).card : ℝ) * r ≤ Q + r*E := (by exact_mod_cast hh : ((bad r).card : ℝ)*r ≤ ((univ.filter fun x : G => x^r ∈ s).card : ℝ)).trans (hc r hr')
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast hp.pos
    rw [← le_div_iff₀ hrpos] at h'
    calc
      _ ≤ (Q + r*E) / r := h'
      _ = _ := by field_simp) hs
  exact ⟨x,hx, fun r hr' hy => h r hr' (mem_filter.mpr ⟨hx,hy⟩)⟩
end E707Partial

end

-- Bundled module: Generator707
section


namespace E707Partial
open Subgroup
 theorem orderOf_survivor {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] (x : G)
    (hx : ∀ r ∈ (Fintype.card G).primeFactors, x ∉ Set.range (fun y : G => y^r)) :
    orderOf x = Fintype.card G := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨k,hk⟩ := show x ∈ Submonoid.powers g from mem_powers_iff_mem_zpowers.2 (hg x)
  have hN : orderOf g = Fintype.card G := by simpa [Nat.card_eq_fintype_card] using orderOf_eq_card_of_forall_mem_zpowers hg
  have hcop : (Fintype.card G).Coprime k := by
    by_contra hn
    obtain ⟨r,hp,hd,hh⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    obtain ⟨j,hj⟩ := hh
    apply hx r (Nat.mem_primeFactors.mpr ⟨hp,hd,Fintype.card_ne_zero⟩)
    exact ⟨g^j, by change (g^j)^r = x; rw [← pow_mul, Nat.mul_comm, ← hj]; exact hk⟩
  rw [← hk, orderOf_pow, hN, hcop.gcd_eq_one, Nat.div_one]
end E707Partial

end

-- Bundled module: Torus707
section



namespace E707Partial
variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

abbrev projectiveImage := (powMonoidHom (α := Kˣ) ((Fintype.card F) - 1)).range

theorem card_projectiveImage (h3 : Module.finrank F K = 3) :
    Nat.card (projectiveImage F K) = (Fintype.card F)^2 + (Fintype.card F) + 1 := by
  classical
  let f := powMonoidHom (α := Kˣ) ((Fintype.card F)-1)
  have hq := Fintype.one_lt_card (α := F)
  have ha : Fintype.card Kˣ = ((Fintype.card F)-1)*((Fintype.card F)^2+(Fintype.card F)+1) := by
    rw [Fintype.card_units, Module.card_eq_pow_finrank (K := F), h3]
    zify [show 1 ≤ (Fintype.card F) by omega, show 1 ≤ (Fintype.card F)^3 by exact Nat.one_le_pow _ _ (by omega)]; ring
  have hk : Nat.card f.ker = (Fintype.card F)-1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [MonoidHom.mem_ker, f, powMonoidHom_apply] using SplitFiber.roots_card (by omega) (ha ▸ dvd_mul_right _ _)
  have he := f.ker.card_mul_index
  rw [Subgroup.index_ker, hk, Nat.card_eq_fintype_card (α := Kˣ), ha] at he
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < (Fintype.card F)-1) he

end E707Partial

end

-- Bundled module: ProjectiveWitness707
section

namespace E707Partial
variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

/-- Sawin's determinant on the projective torus, normalized to conjugates (1,z,z*z^(Fintype.card F)). -/
def onCurve (u v : ℕ) (z : K) : Prop :=
  (z^v - 1) * ((z*z^(Fintype.card F))^u - z^u) = ((z*z^(Fintype.card F))^v - z^v) * (z^u - 1)

theorem fromProjective {u v : ℕ} (hu : 0 < u) (huN : u < (Fintype.card F)^2+(Fintype.card F)+1)
    (h3 : Module.finrank F K = 3) (z : projectiveImage F K)
    (ho : orderOf z = Nat.card (projectiveImage F K)) (hz : onCurve F K u v (z.val : K)) :
    ∃ (α : K) (s t : F), IsPrimitiveRoot (α^((Fintype.card F)-1)) ((Fintype.card F)^2+(Fintype.card F)+1) ∧
      α^v = algebraMap F K s + algebraMap F K t * α^u := by
  obtain ⟨a,ha⟩ := z.property
  change a^((Fintype.card F)-1) = z.val at ha
  let x := (a : K)
  have he : x^((Fintype.card F)-1) = (z.val : K) := by exact congrArg Units.val ha
  have hp : IsPrimitiveRoot (x^((Fintype.card F)-1)) ((Fintype.card F)^2+(Fintype.card F)+1) := by
    rw [IsPrimitiveRoot.iff_orderOf, he, orderOf_units, Subgroup.orderOf_coe, ho, card_projectiveImage F K h3]
  have hq : x^(Fintype.card F) = x * (z.val : K) := by
    rw [← he, ← pow_succ', Nat.sub_add_cancel Fintype.card_pos]
  have hqq : (x^(Fintype.card F))^(Fintype.card F) = x * ((z.val : K)*(z.val : K)^(Fintype.card F)) := by
    calc
      (x^(Fintype.card F))^(Fintype.card F) = (x*(z.val : K))^(Fintype.card F) := congrArg (·^(Fintype.card F)) hq
      _ = _ := by rw [mul_pow,hq]; ring
  have swap (i : ℕ) : (x^i)^(Fintype.card F) = (x^(Fintype.card F))^i := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  have twice (i : ℕ) : ((x^i)^(Fintype.card F))^(Fintype.card F) = ((x^(Fintype.card F))^(Fintype.card F))^i := by
    rw [swap, ← pow_mul, Nat.mul_comm i (Fintype.card F), pow_mul]
  obtain ⟨s,t,hl⟩ := frobLine (v := v) (F := F) (α := x) a.ne_zero hu huN hp (by
    rw [twice u, twice v, swap u, swap v, hqq, hq]; simp only [mul_pow]
    unfold onCurve at hz
    linear_combination x^u*x^v*hz)
  exact ⟨x,s,t,hp,hl⟩

end E707Partial

end

-- Bundled module: Counts707
section

namespace E707Partial
open Finset
variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


open scoped Classical in
noncomputable def locus (u v : ℕ) : Finset (projectiveImage F K) := univ.filter fun z => onCurve F K u v (z.val : K)
open scoped Classical in
theorem witnessOfCounts {u v : ℕ} (hu : 0 < u) (hun : u < (Fintype.card F)^2+(Fintype.card F)+1)
    (h3 : Module.finrank F K = 3) (Q E : ℝ) (hQ : 0 ≤ Q)
    (hr : ((Fintype.card F)^2+(Fintype.card F)+1).primeFactors.sum (fun r : ℕ => 1 / (r : ℝ)) ≤ 1/16)
    (hc : ∀ (r : ℕ), r ∈ ((Fintype.card F)^2+(Fintype.card F)+1).primeFactors →
      ((univ.filter fun x : (projectiveImage F K) => x^r ∈ locus F K u v).card : ℝ) ≤ Q + r*E)
    (hs : Q/16 + ((Fintype.card F)^2+(Fintype.card F)+1).primeFactors.card * E < (locus F K u v).card) :
    ∃ (α : K) (s t : F), IsPrimitiveRoot (α^((Fintype.card F)-1)) ((Fintype.card F)^2+(Fintype.card F)+1) ∧
      α^v = algebraMap F K s + algebraMap F K t * α^u := by
  classical
  have hN : Fintype.card (projectiveImage F K) = (Fintype.card F)^2+(Fintype.card F)+1 := by rw [← Nat.card_eq_fintype_card, card_projectiveImage F K h3]
  rw [← hN] at hr hc hs
  obtain ⟨z,hz,h⟩ := survivePowers (locus F K u v) Q E hQ hr hc hs
  exact fromProjective F K hu hun h3 z (by simpa [Nat.card_eq_fintype_card] using orderOf_survivor z h) (mem_filter.mp hz).2

end E707Partial

end

-- Bundled module: TowerSieve707
section


namespace E707Partial
/-- Sparse prime divisors of the projective Singer modulus along cubic towers. -/
theorem towerOrder (p k r : ℕ) (hr : r.Prime) (hr3 : r ≠ 3)
    (hd : r ∣ (p^(3^k))^2 + p^(3^k) + 1) :
    orderOf (p : ZMod r) = 3^(k+1) ∧ 3^(k+1) ∣ r-1 := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let q : ZMod r := (p : ZMod r)^(3^k)
  have hz : q^2 + q + 1 = 0 := by
    dsimp [q]; exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have h3 : (3 : ZMod r) ≠ 0 := by
    intro he
    have hh : r ∣ 3 := (ZMod.natCast_eq_zero_iff 3 r).mp he
    exact hr3 (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hh).resolve_left hr.ne_one)
  have hq : q ≠ 1 := by
    intro he; apply h3; rw [he] at hz; linear_combination hz
  have ho : orderOf (p : ZMod r) = 3^(k+1) := by
    apply orderOf_eq_prime_pow hq
    rw [pow_succ, pow_mul]; change q^3 = 1
    linear_combination (q-1)*hz
  have hp : (p : ZMod r) ≠ 0 := by
    intro he; have hq0 : q = 0 := by simp [q, he]
    simp [hq0] at hz
  exact ⟨ho, ho ▸ ZMod.orderOf_dvd_card_sub_one hp⟩

end E707Partial

namespace E707Partial
open scoped BigOperators
/-- Pack distinct primes by multiplying their common lower bound. -/
theorem pack (N L : ℕ) (hn : N ≠ 0) (h : ∀ r ∈ N.primeFactors, L ≤ r) :
    L ^ N.primeFactors.card ≤ N := by
  calc
    _ = ∏ _r ∈ N.primeFactors, L := by simp
    _ ≤ ∏ r ∈ N.primeFactors, r := Finset.prod_le_prod' h
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd N)
/-- Reciprocal loss in the union sieve. -/
theorem reciprocalLoss (S : Finset ℕ) (L : ℕ) (hl : 0 < L)
    (h : ∀ r ∈ S, L ≤ r) :
    ∑ r ∈ S, (1 / (r : ℝ)) ≤ (S.card : ℝ) / L := by
  calc
    _ ≤ ∑ _r ∈ S, (1 / (L : ℝ)) := Finset.sum_le_sum fun r hr =>
      one_div_le_one_div_of_le (by exact_mod_cast hl) (by exact_mod_cast h r hr)
    _ = _ := by simp [div_eq_mul_inv]
/-- A fixed power threshold avoids real logarithms in the tower sieve. -/
theorem towerPack (p t : ℕ) (hp : 2 ≤ p) (ht : 0 < t)
    (h : ∀ r ∈ ( (p^t)^2 + p^t + 1 ).primeFactors, p^16 ≤ r) :
    16 * ((p^t)^2 + p^t + 1).primeFactors.card ≤ 3*t := by
  let q := p^t
  have hq : 2 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  have hb : q^2 + q + 1 ≤ q^3 := by nlinarith [Nat.zero_le ((q-2)*q^2), Nat.mul_le_mul_right (q^2) hq, Nat.mul_le_mul_left q hq]
  have hc := pack (q^2+q+1) (p^16) (by omega) h
  rw [← pow_mul] at hc
  have hd := hc.trans hb
  change _ ≤ (p^t)^3 at hd
  rw [← pow_mul p t 3, Nat.mul_comm t 3] at hd
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < p)).mp hd
end E707Partial



namespace E707Partial
open scoped BigOperators
theorem towerSieve (p k : ℕ) (hp : 2 ≤ p) (hp3 : p % 3 = 2)
    (hk : p^16 ≤ 3*3^k) :
    let N := (p^(3^k))^2 + p^(3^k) + 1
    N.primeFactors.sum (fun (r : ℕ) => (1/(r:ℝ))) ≤ 1/16 := by
  intro N
  have hpz : (p : ZMod 3) = -1 := by
    calc
      _ = ((p % 3 : ℕ) : ZMod 3) := by simp
      _ = -1 := by rw [hp3]; decide
  have oddk : Odd (3^k) := (by decide : Odd 3).pow
  have h3 : ¬ 3 ∣ N := by
    intro hd
    have hz := (ZMod.natCast_eq_zero_iff N 3).2 hd
    dsimp [N] at hz
    push_cast at hz
    rw [hpz, oddk.neg_one_pow] at hz
    norm_num at hz
  have lower : ∀ r ∈ N.primeFactors, 3*3^k ≤ r := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hd := Nat.dvd_of_mem_primeFactors hr
    have h := (towerOrder p k r hrp (fun he => h3 (he ▸ hd)) hd).2
    have hj := Nat.le_of_dvd (by have := hrp.two_le; omega : 0 < r-1) h
    rw [pow_succ] at hj
    omega
  have hc := towerPack p (3^k) hp (by positivity) (fun r hr => hk.trans (lower r hr))
  have hsum := reciprocalLoss N.primeFactors (3*3^k) (by positivity) lower
  refine hsum.trans ((div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 16)).2 ?_)
  change 16 * N.primeFactors.card ≤ 3*3^k at hc
  exact_mod_cast (by omega : N.primeFactors.card * 16 ≤ 1 * (3*3^k))
end E707Partial

end

-- Bundled module: Margin707
section


namespace E707Partial
open Filter Real
/-- The number of prime-divisor error terms grows at most logarithmically. -/
theorem countLog (q : ℕ) (hq : 2 ≤ q) :
    ((q^2+q+1).primeFactors.card : ℝ) * log 2 ≤ 3 * log q := by
  let m := (q^2+q+1).primeFactors.card
  have hp := pack (q^2+q+1) 2 (by positivity) (fun r h => (Nat.prime_of_mem_primeFactors h).two_le)
  have hb : q^2+q+1 ≤ q^3 := by nlinarith [Nat.mul_le_mul_right (q^2) hq, Nat.mul_le_mul_right q hq]
  have ht : (2:ℝ)^m ≤ (q:ℝ)^3 := by exact_mod_cast hp.trans hb
  have h := Real.log_le_log (by positivity) ht
  simpa only [Real.log_pow,Nat.cast_ofNat,m] using h
/-- Eventual margin for both the main-curve and all prime-cover Weil errors. -/
theorem sieveMargin (C : ℝ) (hC : 0 < C) : ∃ T : ℕ, ∀ q : ℕ, T ≤ q →
    (((q^2+q+1).primeFactors.card : ℝ)+1) * (C * √(q:ℝ)) < (q:ℝ)/2 := by
  let ε := log 2 / (16*C)
  have hε : 0 < ε := div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound hε
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hl)
  refine ⟨max 2 T, fun q hq => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_left ..) hq
  have hlog := countLog q hq2
  have h1 := hT q (le_trans (le_max_right ..) hq)
  change ‖log (q:ℝ)‖ ≤ ε * ‖(q:ℝ)^(1/2:ℝ)‖ at h1
  rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1≤q))), Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
  have h2 : log 2 ≤ log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
  have hmain : (((q^2+q+1).primeFactors.card : ℝ)+1)*log 2 ≤ 4*log q := by linarith
  have he : ε * (16*C) = log 2 := div_mul_cancel₀ _ (by positivity)
  have hfin : (((q^2+q+1).primeFactors.card : ℝ)+1) * C ≤ √(q:ℝ)/4 := by
    apply (mul_le_mul_iff_left₀ (log_pos (by norm_num : (1:ℝ)<2))).mp
    nlinarith [mul_le_mul_of_nonneg_right (hmain.trans (mul_le_mul_of_nonneg_left h1 (by norm_num))) hC.le, congrArg (fun z : ℝ => z * √(q:ℝ)) he]
  have := mul_le_mul_of_nonneg_right hfin (Real.sqrt_nonneg (q:ℝ))
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ q), (show (0:ℝ)<q by exact_mod_cast (by omega : 0<q))]

end E707Partial

end

-- Bundled module: Component707
section


namespace E707Partial
open Finset Real
/- A single component suffices: other components of the determinant locus need no upper bound. -/
open scoped Classical in
theorem witnessOfComponent (C : ℝ) (hC : 0 < C) : ∃ T : ℕ,
    ∀ (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K],
    let q := Fintype.card F
    let N := q^2+q+1
    ∀ (u v : ℕ), 0<u → u<N → Module.finrank F K = 3 → T ≤ q →
    N.primeFactors.sum (fun r : ℕ => 1/(r:ℝ)) ≤ 1/16 →
    ∀ S : Finset (projectiveImage F K), S ⊆ locus F K u v →
    (q:ℝ)-C*√(q:ℝ) ≤ S.card →
    (∀ r ∈ N.primeFactors, ((univ.filter fun x : projectiveImage F K => x^r ∈ S).card : ℝ) ≤ q + r*(C*√(q:ℝ))) →
    ∃ (α : K) (s t : F), IsPrimitiveRoot (α^(q-1)) N ∧
      α^v = algebraMap F K s + algebraMap F K t * α^u := by
  classical
  obtain ⟨T,hT⟩ := sieveMargin C hC
  refine ⟨T, ?_⟩
  intro F K _ _ _ _ _ q N u v hu hun h3 hq hr S hsub hs hc
  have hN : Fintype.card (projectiveImage F K) = N := by rw [← Nat.card_eq_fintype_card, card_projectiveImage F K h3]
  have hm := hT q hq
  change ((N.primeFactors.card:ℝ)+1) * _ < _ at hm
  have hsur : (q:ℝ)/16 + N.primeFactors.card * (C*√(q:ℝ)) < S.card := by nlinarith [show (0:ℝ) ≤ q by positivity]
  rw [← hN] at hr hc hsur
  obtain ⟨z,hz,h⟩ := survivePowers S q (C*√(q:ℝ)) (by positivity) hr hc hsur
  exact fromProjective F K hu hun h3 z (by simpa [Nat.card_eq_fintype_card] using orderOf_survivor z h) (mem_filter.mp (hsub hz)).2

end E707Partial

end

-- Bundled module: Choose707
section



namespace E707Partial
/-- First exclude bad characteristics, then satisfy any characteristic-dependent field-size bound. -/
theorem chooseTower (B : ℕ) (T : ℕ → ℕ) : ∃ p k : ℕ, B < p ∧ p.Prime ∧ p % 3 = 2 ∧
    T p < p^(3^k) ∧ (((p^(3^k))^2+p^(3^k)+1).primeFactors.sum (fun r : ℕ => 1/(r:ℝ))) ≤ 1/16 := by
  obtain ⟨p,hB,hp,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq B (q := 3) (a := 2) (by decide) (by decide)
  let k := max (T p) (p^16)
  have h1 : k < 3^k := Nat.lt_pow_self (by decide)
  have h2 : 3^k < p^(3^k) := Nat.lt_pow_self hp.one_lt
  have hp3 : p % 3 = 2 := hmod
  exact ⟨p,k,hB,hp,hp3,lt_of_le_of_lt (le_max_left ..) (h1.trans h2),
    towerSieve p k hp.two_le hp3 (by have : p^16 ≤ k := le_max_right ..; omega)⟩

end E707Partial

end

-- Bundled module: Fields707
section

namespace E707Partial
theorem chooseCubic (B : ℕ) (T : ℕ → ℕ) : ∃ (p k : ℕ) (F K : Type) (_ : Field F) (_ : Field K)
    (_ : Fintype F) (_ : Fintype K) (_ : Algebra F K), B < p ∧ p.Prime ∧ p%3=2 ∧
    Fintype.card F = p^(3^k) ∧ T p < Fintype.card F ∧ Module.finrank F K = 3 ∧
    ((Fintype.card F^2 + Fintype.card F + 1).primeFactors.sum (fun r : ℕ => 1/(r:ℝ))) ≤ 1/16 := by
  obtain ⟨p,k,hB,hp,hm,hT,hr⟩ := chooseTower B T
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p (3^k)
  letI : NeZero (3^k) := ⟨by positivity⟩
  let K := FiniteField.Extension F p 3
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite K
  have hF : Fintype.card F = p^(3^k) := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p _ (by positivity)
  exact ⟨p,k,F,K,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,hB,hp,hm,hF,hF ▸ hT,FiniteField.finrank_extension F p 3,hF ▸ hr⟩

end E707Partial

end

-- Bundled module: FieldsChar707
section

namespace E707Partial
theorem chooseCubicChar (B : ℕ) (T : ℕ → ℕ) : ∃ (p k : ℕ) (F K : Type) (_ : Field F) (_ : Field K)
    (_ : Fintype F) (_ : Fintype K) (_ : Algebra F K), CharP F p ∧ CharP K p ∧ B < p ∧ p.Prime ∧ p%3=2 ∧
    Fintype.card F = p^(3^k) ∧ T p < Fintype.card F ∧ Module.finrank F K = 3 ∧
    ((Fintype.card F^2 + Fintype.card F + 1).primeFactors.sum (fun r : ℕ => 1/(r:ℝ))) ≤ 1/16 := by
  obtain ⟨p,k,hB,hp,hm,hT,hr⟩ := chooseTower B T
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p (3^k)
  letI : NeZero (3^k) := ⟨by positivity⟩
  let K := FiniteField.Extension F p 3
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite K
  have hF : Fintype.card F = p^(3^k) := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p _ (by positivity)
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  exact ⟨p,k,F,K,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,hB,hp,hm,hF,hF ▸ hT,FiniteField.finrank_extension F p 3,hF ▸ hr⟩

end E707Partial
end

-- Bundled module: Equiv707
section



namespace E707Partial

theorem reflect {K : Type*} [Field K] {x s t : K} {u v : ℕ}
    (hx : x ≠ 0) (hs : s ≠ 0) (hu : u ≤ v) (h : x ^ v = s + t * x ^ u) :
    (x⁻¹) ^ v = s⁻¹ - t / s * (x⁻¹) ^ (v-u) := by
  have he : x ^ (v-u) * x ^ u = x ^ v := by rw [← pow_add, Nat.sub_add_cancel hu]
  simp only [inv_pow]
  field_simp
  linear_combination (x ^ (v-u)) * (-h) - t * he

theorem reflectWitness {F K : Type*} [Field F] [Field K] [Finite F] [Algebra F K]
    {x : K} {s t : F} {u v n : ℕ} (huv : u < v) (hvn : v < n)
    (hord : IsPrimitiveRoot (x ^ (Nat.card F - 1)) n)
    (h : x ^ v = algebraMap F K s + algebraMap F K t * x ^ u) :
    IsPrimitiveRoot ((x⁻¹) ^ (Nat.card F - 1)) n ∧
    (x⁻¹) ^ v = algebraMap F K s⁻¹ + algebraMap F K (-(t/s)) * (x⁻¹) ^ (v-u) := by
  classical
  let _ := Fintype.ofFinite F
  have hq : 0 < Nat.card F - 1 := Nat.sub_pos_of_lt Finite.one_lt_card
  have hx : x ≠ 0 := by
    rintro rfl
    exact hord.ne_zero (by omega) (zero_pow hq.ne')
  have hs : s ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_add] at h
    have hc : x ^ (v-u) = algebraMap F K t := by
      apply mul_right_cancel₀ (pow_ne_zero u hx)
      rwa [← pow_add, Nat.sub_add_cancel huv.le]
    have ht : t ≠ 0 := by
      rintro rfl
      exact pow_ne_zero _ hx (hc.trans (map_zero _))
    have hd := hord.dvd_of_pow_eq_one (v-u) (by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hc, ← map_pow, Nat.card_eq_fintype_card,
        FiniteField.pow_card_sub_one_eq_one t ht, map_one])
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt huv) hd
    omega
  constructor
  · rw [inv_pow]; exact hord.inv
  · simpa [sub_eq_add_neg] using reflect hx (show algebraMap F K s ≠ 0 by simpa using hs) huv.le h

def H1 : Prop := ∀ u v : ℕ, 0 < u → u < v → v < 2 * u →
  ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K) (_ : Algebra F K),
    Module.finrank F K = 3 ∧ v < Nat.card F ^ 2 + Nat.card F + 1 ∧
    ∃ (α : K) (s t : F),
      IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1) ∧
      α ^ v = algebraMap F K s + algebraMap F K t * α ^ u

/-- Field witness for normalized triples `{0, u, v}` with `2u < v`. -/
def H2 : Prop := ∀ u v : ℕ, 0 < u → 2 * u < v →
  ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K) (_ : Algebra F K),
    Module.finrank F K = 3 ∧ v < Nat.card F ^ 2 + Nat.card F + 1 ∧
    ∃ (α : K) (s t : F),
      IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1) ∧
      α ^ v = algebraMap F K s + algebraMap F K t * α ^ u

theorem reflection_equivalence : H1 ↔ H2 := by
  constructor
  · intro h u v hu huv
    obtain ⟨F,K,iF,iK,fF,fK,alg,h3,hn,x,s,t,hx,hr⟩ := h (v-u) v (by omega) (by omega) (by omega)
    have h' := reflectWitness (u := v-u) (by omega) hn hx hr
    exact ⟨F,K,iF,iK,fF,fK,alg,h3,hn,x⁻¹,s⁻¹,-(t/s),h'.1,by simpa [show v-(v-u)=u by omega] using h'.2⟩
  · intro h u v hu huv hv
    obtain ⟨F,K,iF,iK,fF,fK,alg,h3,hn,x,s,t,hx,hr⟩ := h (v-u) v (by omega) (by omega)
    have h' := reflectWitness (u := v-u) (by omega) hn hx hr
    exact ⟨F,K,iF,iK,fF,fK,alg,h3,hn,x⁻¹,s⁻¹,-(t/s),h'.1,by simpa [show v-(v-u)=u by omega] using h'.2⟩


end E707Partial

end

-- Bundled module: Assembly707
section



namespace E707Partial
open Finset Real
open scoped Classical
/-- Remaining geometric input for a normalized triple. Constants may depend on the characteristic. -/
def ComponentEstimates (u v : ℕ) : Prop := ∃ B : ℕ, ∀ p : ℕ, B < p → p.Prime → p%3=2 →
  ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ (k : ℕ) (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K] [CharP F p] [CharP K p],
    let q := Fintype.card F
    q = p^(3^k) → M ≤ q → Module.finrank F K = 3 →
    ∃ S : Finset (projectiveImage F K), S ⊆ locus F K u v ∧
    (q:ℝ)-C*√(q:ℝ) ≤ S.card ∧
    ∀ (r : ℕ), r ∈ (q^2+q+1).primeFactors → ((univ.filter fun x : projectiveImage F K => x^r ∈ S).card : ℝ) ≤ q + r*(C*√(q:ℝ))
/- Conditional assembly only; `ComponentEstimates` is not yet discharged. -/
set_option maxHeartbeats 1500000 in
theorem witnessesOfEstimates (geo : ∀ u v : ℕ, 0<u → 2*u<v → ComponentEstimates u v) : H1 ∧ H2 := by
  classical
  suffices h : H2 from ⟨reflection_equivalence.mpr h,h⟩
  intro u v hu hv
  obtain ⟨B,hB⟩ := geo u v hu hv
  let Good (p : ℕ) := B<p ∧ p.Prime ∧ p%3=2
  have all (p : ℕ) (h : Good p) := hB p h.1 h.2.1 h.2.2
  let C (p : ℕ) := if h : Good p then (all p h).choose else 1
  let M (p : ℕ) := if h : Good p then (all p h).choose_spec.choose else 0
  have pos (p : ℕ) : 0 < C p := by
    by_cases h : Good p
    · simpa [C,h] using (all p h).choose_spec.choose_spec.1
    · simp [C,h]
  let T (p : ℕ) := (witnessOfComponent (C p) (pos p)).choose
  obtain ⟨p,k,F,K,iF,iK,fF,fK,iA,cF,cK,hBp,hp,hm,hq,hgt,h3,hr⟩ := chooseCubicChar B (fun p => max v (max (T p) (M p)))
  let q := Fintype.card F
  have good : Good p := ⟨hBp,hp,hm⟩
  have hvq : v < q := lt_of_le_of_lt (le_max_left ..) hgt
  have htq := lt_of_le_of_lt (le_max_right ..) hgt
  have ht : T p ≤ q := (le_max_left ..).trans htq.le
  have hM : M p ≤ q := (le_max_right ..).trans htq.le
  simp only [M,dif_pos good] at hM
  obtain ⟨S,hsub,hlo,hhi⟩ := (all p good).choose_spec.choose_spec.2 k F K hq hM h3
  have hn : v < q^2+q+1 := by omega
  have hw := (witnessOfComponent (C p) (pos p)).choose_spec F K u v hu (show u < q^2+q+1 by omega) h3 ht hr S hsub
  specialize hw (by simpa only [C,dif_pos good] using hlo) (by simpa only [C,dif_pos good] using hhi)
  exact ⟨F,K,iF,iK,inferInstance,inferInstance,iA,h3,by simpa [q,Nat.card_eq_fintype_card] using hn,by simpa [Nat.card_eq_fintype_card] using hw⟩

end E707Partial

end

-- Bundled module: Scale707
section

namespace E707Partial
open Finset
open scoped Classical
variable (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

/-- Raising to d transports the determinant locus for a scaled exponent pair. -/
theorem curveScale (z : K) (d u v : ℕ) : onCurve F K (d*u) (d*v) z ↔ onCurve F K u v (z^d) := by
  unfold onCurve
  have h : (z^d)^(Fintype.card F) = (z^(Fintype.card F))^d := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  simp only [h, ← mul_pow, pow_mul]
/-- Prime-cover counts are unchanged when a common exponent multiplier is inverted. -/
theorem scaleComponent (u v d : ℕ) (hd : (Nat.card (projectiveImage F K)).Coprime d) (S : Finset (projectiveImage F K))
    (hs : S ⊆ locus F K u v) : ∃ T : Finset (projectiveImage F K), T ⊆ locus F K (d*u) (d*v) ∧ T.card = S.card ∧
      ∀ r : ℕ, (univ.filter fun x : (projectiveImage F K) => x^r ∈ T).card = (univ.filter fun x : (projectiveImage F K) => x^r ∈ S).card := by
  classical
  let e : (projectiveImage F K) ≃ (projectiveImage F K) := powCoprime hd
  let T := S.map e.symm.toEmbedding
  have mem (x : (projectiveImage F K)) : x ∈ T ↔ x^d ∈ S := by simp [T, e, powCoprime]
  refine ⟨T, ?_, card_map .., ?_⟩
  · intro x hx
    apply mem_filter.mpr
    exact ⟨mem_univ _, (curveScale F K _ d u v).mpr (mem_filter.mp (hs ((mem x).mp hx))).2⟩
  · intro r
    apply card_bij' (fun x _ => e x) (fun x _ => e.symm x)
    · intro x hx
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      change (x^d)^r ∈ S
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      exact (mem _).mp (mem_filter.mp hx).2
    · intro x hx
      apply mem_filter.mpr
      refine ⟨mem_univ _, (mem _).mpr ?_⟩
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      change (e (e.symm x))^r ∈ S
      simpa using (mem_filter.mp hx).2
    · simp
    · simp

end E707Partial

end

-- Bundled module: ScaleTower707
section

namespace E707Partial
open scoped Classical
/-- Every fixed positive multiplier is invertible on all sufficiently high cubic towers. -/
theorem towerCoprime (p k d : ℕ) (hp : p%3=2) (hd : 0<d) (hk : d ≤ k) :
    ((p^(3^k))^2+p^(3^k)+1).Coprime d := by
  let N := (p^(3^k))^2+p^(3^k)+1
  have hpz : (p : ZMod 3) = -1 := by
    calc
      _ = ((p % 3 : ℕ) : ZMod 3) := by simp
      _ = -1 := by rw [hp]; decide
  have oddk : Odd (3^k) := (by decide : Odd 3).pow
  have h3 : ¬ 3 ∣ N := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff N 3).2 h
    dsimp [N] at hz
    push_cast at hz
    rw [hpz, oddk.neg_one_pow] at hz
    norm_num at hz
  apply Nat.coprime_of_dvd
  intro r hr hN hrd
  have h := (towerOrder p k r hr (fun he => h3 (he ▸ hN)) hN).2
  have h' := Nat.le_of_dvd (by have := hr.two_le; omega : 0<r-1) h
  have := Nat.le_of_dvd hd hrd
  have := Nat.lt_pow_self (n := k+1) (by decide : 1 < 3)
  omega

theorem estimatesScale {u v : ℕ} (h : ComponentEstimates u v) (d : ℕ) (hd : 0<d) :
    ComponentEstimates (d*u) (d*v) := by
  obtain ⟨B,hB⟩ := h
  refine ⟨B, fun p hp hp' hmod => ?_⟩
  obtain ⟨C,M,hC,H⟩ := hB p hp hp' hmod
  refine ⟨C,max M (p^(3^d)),hC,?_⟩
  intro k F K _ _ _ _ _ _ _ q hq hm h3
  have hkd : d ≤ k := by
    have h₁ := (le_max_right M (p^(3^d))).trans hm
    rw [hq] at h₁
    exact (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp ((Nat.pow_le_pow_iff_right hp'.one_lt).mp h₁)
  obtain ⟨S,hs,hl,hu⟩ := H k F K hq ((le_max_left ..).trans hm) h3
  have hcop : (Nat.card (projectiveImage F K)).Coprime d := by
    rw [card_projectiveImage F K h3]; change (q^2+q+1).Coprime d; rw [hq]; exact towerCoprime p k d hmod hd hkd
  obtain ⟨T,ht,he,her⟩ := scaleComponent F K u v d hcop S hs
  exact ⟨T,ht,he ▸ hl,fun r hr => (her r) ▸ hu r hr⟩

end E707Partial

end

-- Bundled module: ScaledProjective707
section

namespace E707Partial
variable (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


/-- Take the d-th root projectively, not in the full cubic field's unit group. -/
theorem scaledProjectiveWitness {p k d u v : ℕ} (hp : p%3=2) (hq : (Fintype.card F)=p^(3^k))
    (hd : 0<d) (hk : d≤k) (hu : 0<u) (hun : d*u < (Fintype.card F)^2+(Fintype.card F)+1)
    (h3 : Module.finrank F K = 3) (z : (projectiveImage F K)) (ho : orderOf z = Nat.card (projectiveImage F K))
    (hz : onCurve F K u v (z.val : K)) :
    ∃ (α : K) (s t : F), IsPrimitiveRoot (α^((Fintype.card F)-1)) ((Fintype.card F)^2+(Fintype.card F)+1) ∧
      α^(d*v) = algebraMap F K s + algebraMap F K t * α^(d*u) := by
  have hc : (Nat.card (projectiveImage F K)).Coprime d := by
    rw [card_projectiveImage F K h3,hq]; exact towerCoprime p k d hp hd hk
  let e : (projectiveImage F K) ≃ (projectiveImage F K) := powCoprime hc
  let w := e.symm z
  have hw : w^d=z := e.apply_symm_apply z
  have hdiv := orderOf_pow_dvd (x := w) d
  rw [hw,ho] at hdiv
  apply fromProjective F K (Nat.mul_pos hd hu) hun h3 w (Nat.dvd_antisymm (orderOf_dvd_natCard w) hdiv)
  apply (curveScale F K _ d u v).mpr
  exact (congrArg (fun t : (projectiveImage F K) => onCurve F K u v (t.val : K)) hw).mpr hz

end E707Partial

end

-- Bundled module: CofinalAssembly707
section

namespace E707Partial
/-- Arbitrarily high primitive projective witnesses for each coprime shape suffice. -/
def CofinalPoints (u v : ℕ) : Prop := ∀ L : ℕ,
  ∃ (p k : ℕ) (F K : Type) (_ : Field F) (_ : Fintype F) (_ : Field K) (_ : Fintype K) (_ : Algebra F K),
  p%3=2 ∧ L≤k ∧ Fintype.card F=p^(3^k) ∧ Module.finrank F K=3 ∧
  ∃ z : projectiveImage F K, orderOf z=Nat.card (projectiveImage F K) ∧ onCurve F K u v (z.val : K)

theorem witnessesOfCofinal (h : ∀ u v, 0<u → 2*u<v → Nat.Coprime u v → CofinalPoints u v) : H1 ∧ H2 := by
  suffices h2 : H2 from ⟨reflection_equivalence.mpr h2,h2⟩
  intro u v hu hv
  let d := u.gcd v
  have hd : 0<d := Nat.gcd_pos_of_pos_left v hu
  have h1 : d*(u/d) = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have h2 : d*(v/d) = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have hu' : 0<u/d := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left ..)) hd
  have hv' : 2*(u/d)<v/d := by
    apply (Nat.mul_lt_mul_left hd).mp
    rw [Nat.mul_left_comm d 2,h1,h2]; exact hv
  obtain ⟨p,k,F,K,iF,fF,iK,fK,iA,hp,hk,hq,h3,z,ho,hz⟩ :=
    h _ _ hu' hv' (Nat.coprime_div_gcd_div_gcd hd) (max v d)
  have hp' : 1<p := by omega
  have hlt := (Nat.lt_pow_self (n := k) (by decide : 1<3)).trans (Nat.lt_pow_self hp')
  have hvq : v < Fintype.card F := by rw [hq]; exact lt_of_le_of_lt ((le_max_left ..).trans hk) hlt
  have hn : v < Fintype.card F^2+Fintype.card F+1 := by omega
  have W := scaledProjectiveWitness F K hp hq hd ((le_max_right ..).trans hk) hu'
    (show d*(u/d)<Fintype.card F^2+Fintype.card F+1 by omega) h3 z ho hz
  rw [h1,h2] at W
  exact ⟨F,K,iF,iK,inferInstance,inferInstance,iA,h3,by simpa [Nat.card_eq_fintype_card] using hn,by simpa [Nat.card_eq_fintype_card] using W⟩

end E707Partial

end

-- Bundled module: SqrtSieve707
section

namespace E707Partial
open Finset Real
/-- Telescoping square-root harmonic estimate, including the empty interval. -/
theorem sumInvSqrt (n : ℕ) : ∑ i ∈ range n, (1 / √((i:ℝ)+1)) ≤ 2*√(n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,Nat.cast_succ]
    have h : 0 < √((n:ℝ)+1) := by positivity
    have m : √(n:ℝ) ≤ √((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
    have hn := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
    have hn' := Real.sq_sqrt (show 0 ≤ (n:ℝ)+1 by positivity)
    have step : 1 / √((n:ℝ)+1) ≤ 2*(√((n:ℝ)+1)-√(n:ℝ)) := by
      apply (div_le_iff₀ h).mpr
      nlinarith [sq_nonneg (√((n:ℝ)+1)-√(n:ℝ))]
    linarith

end E707Partial

end

-- Bundled module: ProgressionRank707
section


namespace E707Partial
open Finset Real
/-- The ith positive member of a set in progression 1 mod L is at least L(i+1)
when 1 itself is excluded. -/
theorem progressionRank (S : Finset ℕ) (L : ℕ) (hl : 0 < L)
    (h : ∀ r ∈ S, 1 < r ∧ L ∣ r-1) (i : ℕ) (hi : i < S.card) :
    L*(i+1) ≤ S.orderEmbOfFin rfl ⟨i,hi⟩ := by
  let e := S.orderEmbOfFin rfl
  have rep (j : Fin S.card) : ∃ t : ℕ, 0<t ∧ e j = L*t+1 := by
    obtain ⟨hr,t,ht⟩ := h (e j) (S.orderEmbOfFin_mem rfl j)
    refine ⟨t,?_,by omega⟩
    by_contra! hh
    have hz : t=0 := by omega
    rw [hz,mul_zero] at ht
    omega
  induction i with
  | zero =>
    obtain ⟨t,ht,he⟩ := rep ⟨0,hi⟩
    change L*(0+1) ≤ e _
    nlinarith
  | succ i ih =>
    have hprev : i < S.card := by omega
    have hh := ih hprev
    obtain ⟨t,ht,he⟩ := rep ⟨i,hprev⟩
    obtain ⟨u,hu,hf⟩ := rep ⟨i+1,hi⟩
    have hinc := e.strictMono (show (⟨i,hprev⟩ : Fin S.card) < ⟨i+1,hi⟩ by exact Nat.lt_succ_self _)
    change L*(i+1) ≤ e _ at hh
    rw [he] at hh hinc
    rw [hf] at hinc
    change L*((i+1)+1) ≤ e _
    rw [hf]
    have htu : t < u := (Nat.mul_lt_mul_left hl).mp (by omega)
    nlinarith [Nat.mul_le_mul_left L (show t+1 ≤ u by omega)]

end E707Partial

end

-- Bundled module: ProgressionLoss707
section

namespace E707Partial
open Finset Real
theorem progressionSqrtLoss (S : Finset ℕ) (L : ℕ) (hl : 0<L)
    (h : ∀ r ∈ S, 1<r ∧ L ∣ r-1) :
    ∑ r ∈ S, 1/√(r:ℝ) ≤ 2*√(S.card:ℝ)/√(L:ℝ) := by
  classical
  let e := S.orderEmbOfFin rfl
  have hL : 0 < √(L:ℝ) := by positivity
  calc
    _ = ∑ i : Fin S.card, 1/√(e i:ℝ) := by
      conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl,sum_map]
      rfl
    _ ≤ ∑ i : Fin S.card, (1/√((i.val:ℝ)+1))/√(L:ℝ) := by
      apply sum_le_sum
      intro i _
      have he : (L:ℝ)*((i.val:ℝ)+1) ≤ (e i:ℝ) := by exact_mod_cast progressionRank S L hl h i.val i.isLt
      have hr := Real.sqrt_le_sqrt he
      rw [Real.sqrt_mul (by positivity)] at hr
      rw [div_div, mul_comm (√((i.val:ℝ)+1))]
      exact one_div_le_one_div_of_le (by positivity) hr
    _ = (∑ i ∈ range S.card, 1/√((i:ℝ)+1))/√(L:ℝ) := by rw [← sum_div,Fin.sum_univ_eq_sum_range (fun i : ℕ => 1/√((i:ℝ)+1))]
    _ ≤ _ := div_le_div_of_nonneg_right (sumInvSqrt _) hL.le

end E707Partial

end

-- Bundled module: TowerLoss707
section


namespace E707Partial
open Finset Real
theorem towerPackParam (p t A : ℕ) (hp : 2 ≤ p) (ht : 0 < t)
    (h : ∀ r ∈ ( (p^t)^2 + p^t + 1 ).primeFactors, p^A ≤ r) :
    A * ((p^t)^2 + p^t + 1).primeFactors.card ≤ 3*t := by
  let q := p^t
  have hq : 2 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  have hb : q^2 + q + 1 ≤ q^3 := by nlinarith [Nat.zero_le ((q-2)*q^2), Nat.mul_le_mul_right (q^2) hq, Nat.mul_le_mul_left q hq]
  have hc := pack (q^2+q+1) (p^A) (by omega) h
  rw [← pow_mul] at hc
  have hd := hc.trans hb
  change _ ≤ (p^t)^3 at hd
  rw [← pow_mul p t 3, Nat.mul_comm t 3] at hd
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < p)).mp hd
theorem towerSqrtLoss (p k A : ℕ) (hp : 2 ≤ p) (hp3 : p%3=2) (hk : p^A ≤ 3*3^k) :
    let N := (p^(3^k))^2+p^(3^k)+1
    √(A:ℝ) * (N.primeFactors.sum (fun r : ℕ => 1/√(r:ℝ))) ≤ 2 := by
  intro N
  have hpz : (p : ZMod 3) = -1 := by
    calc
      _ = ((p % 3 : ℕ) : ZMod 3) := by simp
      _ = -1 := by rw [hp3]; decide
  have oddk : Odd (3^k) := (by decide : Odd 3).pow
  have h3 : ¬ 3 ∣ N := by
    intro hd
    have hz := (ZMod.natCast_eq_zero_iff N 3).2 hd
    dsimp [N] at hz
    push_cast at hz
    rw [hpz, oddk.neg_one_pow] at hz
    norm_num at hz
  have lower : ∀ r ∈ N.primeFactors, 3*3^k ≤ r := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hd := Nat.dvd_of_mem_primeFactors hr
    have h := (towerOrder p k r hrp (fun he => h3 (he ▸ hd)) hd).2
    have hj := Nat.le_of_dvd (by have := hrp.two_le; omega : 0 < r-1) h
    rw [pow_succ] at hj
    omega
  let L := 3*3^k
  have hl : 0<L := by dsimp [L]; positivity
  have hs := progressionSqrtLoss N.primeFactors L hl (fun r hr => ⟨(Nat.prime_of_mem_primeFactors hr).one_lt, by
    have hd := Nat.dvd_of_mem_primeFactors hr
    simpa [L,pow_succ,Nat.mul_comm] using (towerOrder p k r (Nat.prime_of_mem_primeFactors hr) (fun he => h3 (he ▸ hd)) hd).2⟩)
  have hc := towerPackParam p (3^k) A hp (by positivity) (fun r hr => hk.trans (lower r hr))
  have hc' : (A:ℝ)*(N.primeFactors.card:ℝ) ≤ (L:ℝ) := by exact_mod_cast hc
  have hroot := Real.sqrt_le_sqrt hc'
  rw [Real.sqrt_mul (by positivity)] at hroot
  apply (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)).trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [show √(A:ℝ)*(2*√(N.primeFactors.card:ℝ)) = 2*(√(A:ℝ)*√(N.primeFactors.card:ℝ)) by ring,hroot]

end E707Partial

end

-- Bundled module: RatioPacking707
section

namespace E707Partial
open Finset
variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
open scoped Classical in
theorem ratioPacking (S : Finset G) (H : Subgroup G) (D : ℕ)
    (hb : ∀ t ∈ H, t ≠ 1 → (S.offDiag.filter fun p => p.1/p.2=t).card ≤ D) :
    let B := S.filter (· ∈ H)
    B.card*(B.card-1) ≤ D*Nat.card H := by
  classical
  intro B
  let T := (H : Set G).toFinset
  have hm : ∀ p ∈ B.offDiag, p.1/p.2 ∈ T := by
    intro p hp
    obtain ⟨hx,hy,_⟩ := mem_offDiag.mp hp
    exact Set.mem_toFinset.mpr (H.div_mem (mem_filter.mp hx).2 (mem_filter.mp hy).2)
  have hc := card_eq_sum_card_fiberwise hm
  have hle : B.offDiag.card ≤ ∑ _t ∈ T, D := by
    rw [hc]; apply sum_le_sum
    intro t ht
    by_cases e : t=1
    · subst t
      have hh : (B.offDiag.filter fun p => p.1/p.2=1) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact (mem_offDiag.mp (mem_filter.mp hp).1).2.2 (div_eq_one.mp (mem_filter.mp hp).2)
      simp [hh]
    · apply le_trans _ (hb t (Set.mem_toFinset.mp ht) e)
      apply card_le_card
      intro p hp
      obtain ⟨ht',hr⟩ := mem_filter.mp hp
      obtain ⟨hx,hy,hxy⟩ := mem_offDiag.mp ht'
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hy).1,hxy⟩,hr⟩
  rw [offDiag_card] at hle
  simpa [T,Nat.mul_sub,Nat.mul_comm,Nat.card_eq_fintype_card] using hle

end E707Partial

end

-- Bundled module: PowerIndex707
section

namespace SplitFiber
open Finset
variable {A : Type*} [CommGroup A] [Fintype A] [DecidableEq A] [IsCyclic A]
theorem powerIndex {r : ℕ} (hr : r ≠ 0) (hd : r ∣ Fintype.card A) : (powMonoidHom (α := A) r).range.index = r := by
  classical
  rw [Subgroup.index_range,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simpa only [MonoidHom.mem_ker,powMonoidHom_apply] using roots_card hr hd
open scoped Classical in
theorem powerPreimage {r : ℕ} (hr : r ≠ 0) (hd : r ∣ Fintype.card A) (D : Finset A) :
    (univ.filter fun x : A => x^r ∈ D).card = (D.filter (· ∈ (powMonoidHom (α := A) r).range)).card*r := by
  classical
  let S := D.filter (· ∈ (powMonoidHom (α := A) r).range)
  have hs := pullback_card hr hd S (fun y hy => (mem_filter.mp hy).2)
  have he : (univ.filter fun x : A => x^r ∈ S) = univ.filter fun x : A => x^r ∈ D := by
    ext x
    have hm : x^r ∈ (powMonoidHom (α := A) r).range := ⟨x,rfl⟩
    simp only [S,mem_filter,mem_univ,true_and,hm,and_true]
  rw [he] at hs
  exact hs
open scoped Classical in
theorem powerBound {r : ℕ} (hr : r ≠ 0) (hd : r ∣ Fintype.card A) (D : Finset A) (a b : ℝ)
    (h : ∀ H : Subgroup A, (H.index : ℝ)*(D.filter (· ∈ H)).card ≤ a+H.index*b) :
    ((univ.filter fun x : A => x^r ∈ D).card : ℝ) ≤ a+r*b := by
  classical
  have ht := h (powMonoidHom (α := A) r).range
  rw [powerIndex hr hd] at ht
  rw [powerPreimage hr hd,Nat.cast_mul,mul_comm]
  convert ht using 1 <;> congr 3 <;> ext <;> simp
end SplitFiber

end

-- Bundled module: PowerPacking707
section


namespace E707Partial
open Finset Real
open scoped Classical
variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
theorem powerPacking (S : Finset G) (D r : ℕ) (hr : r ≠ 0) (hd : r ∣ Fintype.card G)
    (hb : ∀ t : G, t ≠ 1 → (S.offDiag.filter fun p => p.1/p.2=t).card ≤ D) :
    ((S.filter fun y => y ∈ Set.range (fun x : G => x^r)).card : ℝ) ≤
      (1+√(D:ℝ))*√(Fintype.card G:ℝ)*(1/√(r:ℝ)) := by
  classical
  let H := (powMonoidHom (α := G) r).range
  let B := S.filter (· ∈ H)
  change (B.card:ℝ) ≤ _
  have hp : B.card*(B.card-1) ≤ D*Nat.card H := by
    convert ratioPacking S H D (fun t _ => hb t) using 1
    congr 2 <;> congr 1 <;> ext x <;> simp [B]
  have hc := H.card_mul_index
  rw [show H.index=r from SplitFiber.powerIndex hr hd,Nat.card_eq_fintype_card (α := G)] at hc
  have hm : (Nat.card H:ℝ)*(r:ℝ) = Fintype.card G := by exact_mod_cast hc
  have hh : 1 ≤ Nat.card H := Nat.card_pos
  have hh' : (1:ℝ) ≤ √(Nat.card H:ℝ) := by simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ Nat.card H by exact_mod_cast hh)
  have hs : √(Nat.card H:ℝ)*√(r:ℝ) = √(Fintype.card G:ℝ) := by rw [← Real.sqrt_mul (by positivity),hm]
  have ht : (B.card:ℝ) ≤ 1+√(D:ℝ)*√(Nat.card H:ℝ) := by
    cases he : B.card with
    | zero => push_cast; positivity
    | succ b =>
      rw [he] at hp
      simp only [Nat.add_one_sub_one] at hp
      have hl : b*b ≤ D*Nat.card H := le_trans (Nat.mul_le_mul_right b (Nat.le_succ b)) hp
      have hl' : (b:ℝ)*(b:ℝ) ≤ (D:ℝ)*(Nat.card H:ℝ) := by exact_mod_cast hl
      have := Real.sqrt_le_sqrt hl'
      rw [Real.sqrt_mul_self (by positivity),Real.sqrt_mul (by positivity)] at this
      push_cast; linarith
  rw [← hs]
  have hr' : 0 < √(r:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hr)
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right (show (B.card:ℝ) ≤ (1+√(D:ℝ))*√(Nat.card H:ℝ) by nlinarith) hr'.le]

end E707Partial

end

-- Bundled module: PackedGenerator707
section


namespace E707Partial
open Finset Real
open scoped Classical
variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
theorem packedGenerator (S : Finset G) (D : ℕ)
    (hb : ∀ t : G, t ≠ 1 → (S.offDiag.filter fun p => p.1/p.2=t).card ≤ D)
    (hm : (1+√(D:ℝ))*√(Fintype.card G:ℝ)*((Fintype.card G).primeFactors.sum (fun r => 1/√(r:ℝ))) < S.card) :
    ∃ x ∈ S, orderOf x = Fintype.card G := by
  classical
  let P := (Fintype.card G).primeFactors
  let B (r : ℕ) := S.filter fun y => y ∈ Set.range (fun x : G => x^r)
  by_contra! hn
  have hs : S ⊆ P.biUnion B := by
    intro x hx
    apply mem_biUnion.mpr
    by_contra! he
    apply hn x hx (orderOf_survivor x (fun r hr hy => he r hr (mem_filter.mpr ⟨hx,hy⟩)))
  have h := (card_le_card hs).trans (card_biUnion_le ..)
  have hc : (S.card:ℝ) ≤ ∑ r ∈ P, ((B r).card:ℝ) := by exact_mod_cast h
  apply hm.not_ge
  rw [mul_sum]
  refine hc.trans (sum_le_sum fun r hr => ?_)
  exact powerPacking S D r (Nat.prime_of_mem_primeFactors hr).ne_zero (Nat.dvd_of_mem_primeFactors hr) hb

 theorem towerPackedGenerator (p k A D : ℕ) (hp : 2 ≤ p) (hp3 : p%3=2) (hk : p^A ≤ 3*3^k)
    (hN : Fintype.card G = (p^(3^k))^2+p^(3^k)+1) (S : Finset G)
    (hb : ∀ t : G, t ≠ 1 → (S.offDiag.filter fun z => z.1/z.2=t).card ≤ D)
    (hs : 2*((1+√(D:ℝ))*√(Fintype.card G:ℝ)) < √(A:ℝ)*S.card) :
    ∃ x ∈ S, orderOf x = Fintype.card G := by
  apply packedGenerator S D hb
  have hl := towerSqrtLoss p k A hp hp3 hk
  dsimp only at hl
  rw [← hN] at hl
  by_contra! hn
  have h1 := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (A:ℝ))
  have h2 := mul_le_mul_of_nonneg_left hl (show 0 ≤ (1+√(D:ℝ))*√(Fintype.card G:ℝ) by positivity)
  linarith only [hs,h1,h2]

end E707Partial

end

-- Bundled module: DensityPoint
section


namespace E707Partial
open Finset Real
open scoped Classical
variable (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


 -- Adapted from math04 PackedWitness707.
theorem densityPackedPoint (p k D b u v L : ℕ) (hp : 2 ≤ p) (hp3 : p%3=2)
    (hk : p^(b^2) ≤ 3*3^k) (hb : 4*(1+√(D:ℝ))*(L:ℝ) < b) (hq : (Fintype.card F) = p^(3^k))
    (h3 : Module.finrank F K = 3)
    (S : Finset (projectiveImage F K)) (hsub : S ⊆ locus F K u v) (hs : (Fintype.card F) ≤ L*S.card)
    (hm : ∀ t : (projectiveImage F K), t ≠ 1 → (S.offDiag.filter fun z => z.1/z.2=t).card ≤ D) :
    ∃ z : (projectiveImage F K), orderOf z = Nat.card (projectiveImage F K) ∧ onCurve F K u v (z.val : K) := by
  classical
  have hN : Fintype.card (projectiveImage F K) = (Fintype.card F)^2+(Fintype.card F)+1 := by rw [← Nat.card_eq_fintype_card,card_projectiveImage F K h3]
  have hq1 : (1:ℝ) ≤ (Fintype.card F) := by exact_mod_cast Fintype.card_pos (α := F)
  have hr : √(Fintype.card (projectiveImage F K):ℝ) ≤ 2*(Fintype.card F) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [hN]; push_cast; nlinarith [sq_nonneg (((Fintype.card F):ℝ)-1)]
  obtain ⟨z,hz,hord⟩ := towerPackedGenerator p k (b^2) D hp hp3 hk (by simpa only [← hq] using hN) S hm (by
    rw [Nat.cast_pow,Real.sqrt_sq (by positivity)]
    have ha := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*(1+√(D:ℝ)) by positivity)
    have hpos : 0 < S.card := by
      by_contra! hz
      rw [Nat.eq_zero_of_le_zero hz, mul_zero] at hs
      have := Fintype.card_pos (α:=F); omega
    have hl := mul_lt_mul_of_pos_right hb (show (0:ℝ)<S.card by exact_mod_cast hpos)
    have hf : ((Fintype.card F):ℝ) ≤ L*S.card := by exact_mod_cast hs
    nlinarith only [ha,hl,mul_le_mul_of_nonneg_left hf (show 0 ≤ 4*(1+√(D:ℝ)) by positivity)])
  exact ⟨z,by simpa [Nat.card_eq_fintype_card] using hord,(mem_filter.mp (hsub hz)).2⟩

end E707Partial

end

-- Bundled module: FactorPigeon707
section

namespace E707Partial
open Polynomial Finset
variable {K Z : Type*} [Field K]

/-- Additive on nonzero products; detects nonconstant bivariate polynomials. -/
private noncomputable def factorWeight (f : K[X][X]) : ℕ :=
  f.natDegree + f.leadingCoeff.natDegree

private theorem factorWeight_mul {a b : K[X][X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    factorWeight (a*b) = factorWeight a + factorWeight b := by
  simp only [factorWeight, natDegree_mul ha hb, leadingCoeff_mul,
    natDegree_mul (leadingCoeff_ne_zero.mpr ha) (leadingCoeff_ne_zero.mpr hb)]
  omega

private theorem factorWeight_pos {i : K[X][X]} (hi : Irreducible i) : 0 < factorWeight i := by
  by_contra! hz
  unfold factorWeight at hz
  have ho : i.natDegree = 0 := by omega
  have hl : (i.coeff 0).natDegree = 0 := by
    rw [← ho, coeff_natDegree]; omega
  have he := eq_C_of_natDegree_eq_zero ho
  rw [eq_C_of_natDegree_eq_zero hl] at he
  have hc : (i.coeff 0).coeff 0 ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at he
    exact hi.ne_zero he
  exact hi.not_isUnit (he ▸ ((isUnit_iff_ne_zero.mpr hc).map C).map C)

private theorem factorPigeonAux (e : Z → K[X][X] →+* K) (f : K[X][X]) (hf : f ≠ 0)
    (S : Finset Z) (hs : S.Nonempty) (hz : ∀ z ∈ S, e z f = 0) :
    ∃ (g : K[X][X]) (T : Finset Z), Irreducible g ∧ g ∣ f ∧ T ⊆ S ∧
      (∀ z ∈ T, e z g = 0) ∧ S.card ≤ factorWeight f * T.card := by
  classical
  induction f using WfDvdMonoid.induction_on_irreducible generalizing S with
  | zero => exact (hf rfl).elim
  | unit u hu =>
    obtain ⟨z,hzS⟩ := hs
    exact ((hu.map (e z)).ne_zero (hz z hzS)).elim
  | mul a i ha hi ih =>
    let A := S.filter (fun z => e z i = 0)
    let B := S \ A
    have hAS : A ⊆ S := filter_subset _ _
    have hBS : B ⊆ S := sdiff_subset
    have hA : ∀ z ∈ A, e z i = 0 := fun z h => (mem_filter.mp h).2
    have hsum : B.card + A.card = S.card := card_sdiff_add_card_eq_card hAS
    have hw := factorWeight_pos hi
    rw [factorWeight_mul hi.ne_zero ha]
    by_cases hb : B.Nonempty
    · have hB : ∀ z ∈ B, e z a = 0 := by
        intro z h
        have ht := hz z (hBS h)
        rw [map_mul, mul_eq_zero] at ht
        exact ht.resolve_left (fun hzi => (mem_sdiff.mp h).2 (mem_filter.mpr ⟨hBS h,hzi⟩))
      obtain ⟨g,T,hg,hga,hT,hzT,hcnt⟩ := ih ha B hb hB
      by_cases hcmp : A.card ≤ T.card
      · refine ⟨g,T,hg,dvd_mul_of_dvd_right hga i,hT.trans hBS,hzT,?_⟩
        rw [add_mul, ← hsum, Nat.add_comm (factorWeight i * _)]
        exact Nat.add_le_add hcnt (hcmp.trans (Nat.le_mul_of_pos_left _ hw))
      · refine ⟨i,A,hi,dvd_mul_right _ _,hAS,hA,?_⟩
        rw [add_mul, ← hsum, Nat.add_comm (factorWeight i * _)]
        exact Nat.add_le_add (hcnt.trans (Nat.mul_le_mul_left _ (by omega))) (Nat.le_mul_of_pos_left _ hw)
    · refine ⟨i,A,hi,dvd_mul_right _ _,hAS,hA,?_⟩
      have h0 : B.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hb)
      rw [← hsum,h0,zero_add]
      exact Nat.le_mul_of_pos_left _ (by omega)

/-- A single irreducible factor vanishes on at least a `1/(2*D)` fraction of the sample.
Use `x z := ((z : Kˣ) : K)` for a projective-image sample. -/
theorem chartFactorPigeon (x : Z → K) (q D : ℕ) (f : K[X][X]) (hf : f ≠ 0)
    (hy : f.natDegree ≤ D) (hx : ∀ j, (f.coeff j).natDegree ≤ D)
    (S : Finset Z) (hs : S.Nonempty)
    (hz : ∀ z ∈ S, (f.map (evalRingHom (x z))).eval ((x z)^q) = 0) :
    ∃ (g : K[X][X]) (T : Finset Z), Irreducible g ∧ g ∣ f ∧ T ⊆ S ∧
      (∀ z ∈ T, (g.map (evalRingHom (x z))).eval ((x z)^q) = 0) ∧ S.card ≤ (2*D)*T.card := by
  let e := fun z => (evalRingHom ((x z)^q)).comp (mapRingHom (evalRingHom (x z)))
  obtain ⟨g,T,hg,hgf,hT,hzT,hcnt⟩ := factorPigeonAux e f hf S hs hz
  refine ⟨g,T,hg,hgf,hT,hzT,hcnt.trans (Nat.mul_le_mul_right _ ?_)⟩
  have h := hx f.natDegree
  rw [coeff_natDegree] at h
  unfold factorWeight
  omega


end E707Partial

end

-- Bundled module: PackedWitness707
section


namespace E707Partial
open Finset Real
open scoped Classical
variable (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


 theorem packedWitness (p k D b u v : ℕ) (hp : 2 ≤ p) (hp3 : p%3=2)
    (hk : p^(b^2) ≤ 3*3^k) (hb : 8*(1+√(D:ℝ)) < b) (hq : (Fintype.card F) = p^(3^k))
    (h3 : Module.finrank F K = 3) (hu : 0<u) (hun : u<(Fintype.card F)^2+(Fintype.card F)+1)
    (S : Finset (projectiveImage F K)) (hsub : S ⊆ locus F K u v) (hs : (Fintype.card F) ≤ 2*S.card)
    (hm : ∀ t : (projectiveImage F K), t ≠ 1 → (S.offDiag.filter fun z => z.1/z.2=t).card ≤ D) :
    ∃ (α : K) (s t : F), IsPrimitiveRoot (α^((Fintype.card F)-1)) ((Fintype.card F)^2+(Fintype.card F)+1) ∧
      α^v = algebraMap F K s + algebraMap F K t * α^u := by
  classical
  have hN : Fintype.card (projectiveImage F K) = (Fintype.card F)^2+(Fintype.card F)+1 := by rw [← Nat.card_eq_fintype_card,card_projectiveImage F K h3]
  have hq1 : (1:ℝ) ≤ (Fintype.card F) := by exact_mod_cast Fintype.card_pos (α := F)
  have hr : √(Fintype.card (projectiveImage F K):ℝ) ≤ 2*(Fintype.card F) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [hN]; push_cast; nlinarith [sq_nonneg (((Fintype.card F):ℝ)-1)]
  obtain ⟨z,hz,hord⟩ := towerPackedGenerator p k (b^2) D hp hp3 hk (by simpa only [← hq] using hN) S hm (by
    rw [Nat.cast_pow,Real.sqrt_sq (by positivity)]
    have ha := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*(1+√(D:ℝ)) by positivity)
    have hl := mul_lt_mul_of_pos_right hb (show (0:ℝ)<(Fintype.card F) by positivity)
    have hf : ((Fintype.card F):ℝ) ≤ 2*S.card := by exact_mod_cast hs
    nlinarith only [ha,hl,mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg b)])
  exact fromProjective F K hu hun h3 z (by simpa [Nat.card_eq_fintype_card] using hord) (mem_filter.mp (hsub hz)).2

end E707Partial

end

-- Bundled module: SmallPeriod707
section


namespace E707Partial
/-- Bounded-period exceptions to a translate estimate disappear up the tower. -/
theorem noSmallPeriod {G : Type*} [Group G] [Fintype G] (p k d : ℕ) (hp : p%3=2)
    (hN : Fintype.card G = (p^(3^k))^2+p^(3^k)+1) (hd : 0<d) (hk : d ≤ k)
    (x : G) (hx : x^d=1) : x=1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Fintype.card G := orderOf_dvd_card
  rw [hN] at h2
  have h := (towerCoprime p k d hp hd hk).gcd_eq_one
  have he := Nat.dvd_gcd h2 h1
  rw [h] at he
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one he)

end E707Partial

end

-- Bundled module: CharacterPeriod707
section

namespace E707Partial
/-- The norm of a nontrivial character bounds its kernel on the cubic rational torus.
    The character on a rational point has exponent a+b*q. -/
theorem normPeriod {G : Type*} [Group G] (z : G) (q : ℕ) (a b : ℤ)
    (hN : z^(q^2+q+1) = 1) (hc : z^(a+b*q)=1) : z^(a^2-a*b+b^2)=1 := by
  have hN' : z^((q:ℤ)^2+q+1)=1 := by exact_mod_cast hN
  have h : a^2-a*b+b^2 = (a+b*q)*(a-b-b*q)+((q:ℤ)^2+q+1)*b^2 := by ring
  rw [h,zpow_add,zpow_mul,zpow_mul,hc,hN']; simp
 theorem normPeriod_pos (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) : 0 < a^2-a*b+b^2 := by
  rcases h with h|h
  · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (a-b),sq_nonneg b]
  · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (a-b),sq_nonneg a]

end E707Partial

end

-- Bundled module: SupportPeriod707
section

namespace E707Partial
/-- Evaluation of a Laurent character on the cubic rational torus. -/
def weight (q : ℕ) (e : ℤ × ℤ) : ℤ := e.1 + e.2*q
/-- A diagonal translation that preserves a Laurent equation up to scalar
    kills every difference of supported characters. -/
theorem supportPeriod {K : Type*} [Field K] (f : AddMonoidAlgebra K (ℤ × ℤ))
    (z : Kˣ) (q : ℕ) (c : K) (i j : ℤ × ℤ)
    (hi : f.coeff i ≠ 0) (hj : f.coeff j ≠ 0)
    (h : ∀ e, f.coeff e * ↑(z ^ weight q e) = f.coeff e * c) :
    z ^ ((i.1-j.1)+(i.2-j.2)*q) = 1 := by
  have he : z ^ weight q i = z ^ weight q j := Units.ext <|
    (mul_left_cancel₀ hi (h i)).trans (mul_left_cancel₀ hj (h j)).symm
  have hh : (i.1-j.1)+(i.2-j.2)*q = weight q i - weight q j := by unfold weight; ring
  rw [hh,zpow_sub,he]; simp

end E707Partial

end

-- Bundled module: TrivialStabilizer707
section

namespace E707Partial
open scoped Classical
variable (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


/-- A two-term support certificate rules out every nontrivial rational scalar stabilizer. -/
theorem trivialSupportStabilizer (p k : ℕ) (hp : p%3=2) (hq : (Fintype.card F)=p^(3^k))
    (h3 : Module.finrank F K = 3) (z : (projectiveImage F K)) (f : AddMonoidAlgebra K (ℤ × ℤ))
    (c : K) (i j : ℤ × ℤ) (hne : i ≠ j) (hi : f.coeff i ≠ 0) (hj : f.coeff j ≠ 0)
    (hk : ((i.1-j.1)^2-(i.1-j.1)*(i.2-j.2)+(i.2-j.2)^2).toNat ≤ k)
    (h : ∀ e, f.coeff e * ↑((z:Kˣ) ^ weight (Fintype.card F) e) = f.coeff e * c) : z=1 := by
  let a := i.1-j.1
  let b := i.2-j.2
  have hn : 0 < a^2-a*b+b^2 := normPeriod_pos a b (by
    by_contra! hh
    exact hne (Prod.ext (sub_eq_zero.mp hh.1) (sub_eq_zero.mp hh.2)))
  have hcard : Fintype.card (projectiveImage F K)=(Fintype.card F)^2+(Fintype.card F)+1 := by rw [← Nat.card_eq_fintype_card,card_projectiveImage F K h3]
  have hN : z^((Fintype.card F)^2+(Fintype.card F)+1)=1 := by rw [← hcard]; exact pow_card_eq_one
  have hchar : z^(a+b*(Fintype.card F))=1 := Subtype.ext (supportPeriod f z (Fintype.card F) c i j hi hj h)
  have hnorm := normPeriod z (Fintype.card F) a b hN hchar
  have hd : ((a^2-a*b+b^2).toNat : ℤ)=a^2-a*b+b^2 := Int.toNat_of_nonneg hn.le
  apply noSmallPeriod p k (a^2-a*b+b^2).toNat hp (hq ▸ hcard) (by omega) hk z
  rw [←hd] at hnorm
  exact_mod_cast hnorm

end E707Partial

end

-- Bundled module: ElimRoot707
section


namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]
/-- Projection to the first torus coordinate of a common zero kills the eliminant. -/
theorem elimRoot (f g : Polynomial (Polynomial K)) (x y : K)
    (hd : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0)
    (hf : (f.map (evalRingHom x)).eval y = 0)
    (hg : (g.map (evalRingHom x)).eval y = 0) :
    (f.resultant g).eval x = 0 := by
  obtain ⟨u,v,_,_,he⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hd
  have hh := congrArg (fun h : Polynomial (Polynomial K) => (h.map (evalRingHom x)).eval y) he
  simpa [hf,hg] using hh.symm

end E707Partial

end

-- Bundled module: DetDegree707
section

namespace E707Partial
open Polynomial Matrix
/-- Uniform bound for the x-degree of a Sylvester determinant, independent of q. -/
theorem detDegree {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K)) (d : ℕ) (hd : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.natDegree ≤ Fintype.card ι * d := by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply, Multiset.mem_map,
    exists_imp, Finset.mem_univ_val]
  intro g
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hs|hs <;>
    simp only [hs,one_smul,Units.neg_smul,natDegree_neg]
  all_goals
    refine (natDegree_prod_le _ _).trans ?_
    simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => (M (g i) i).natDegree) d (fun i _ => hd _ _)

end E707Partial

end

-- Bundled module: ChartIntersection707
section

namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]
theorem chartIntersection (f g : Polynomial (Polynomial K)) (d : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ d) (hg : ∀ i, (g.coeff i).natDegree ≤ d)
    (hd : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) (hr : f.resultant g ≠ 0)
    (S : Finset K) (hs : ∀ x ∈ S, ∃ y, (f.map (evalRingHom x)).eval y=0 ∧
      (g.map (evalRingHom x)).eval y=0) : S.card ≤ (f.natDegree+g.natDegree)*d := by
  refine (card_le_degree_of_subset_roots (p := f.resultant g) ?_).trans ?_
  · intro x hx
    obtain ⟨y,hy,hz⟩ := hs x hx
    exact (mem_roots hr).mpr (elimRoot f g x y hd hy hz)
  · unfold resultant
    apply le_trans (detDegree _ d ?_) (by simp)
    intro i j
    induction j using Fin.addCases <;> simp [sylvester] <;> split <;> simp_all

end E707Partial

end

-- Bundled module: ChartResultant707
section


namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]
theorem chartResultant (f g : Polynomial (Polynomial K)) (hp : f.IsPrimitive)
    (hi : Irreducible f) (hn : ¬ f ∣ g) : f.resultant g ≠ 0 := by
  let φ := algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hif : Irreducible (f.map φ) := hp.irreducible_iff_irreducible_map_fraction_map.mp hi
  have hnf : ¬ f.map φ ∣ g.map φ := fun h => hn (hp.dvd_of_fraction_map_dvd_fraction_map h)
  have hc : IsCoprime (f.map φ) (g.map φ) := hif.coprime_iff_not_dvd.mpr hnf
  have hr := resultant_ne_zero _ _ hc
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj, resultant_map_map] at hr
  exact fun h => hr (by rw [h, map_zero])

end E707Partial

end

-- Bundled module: ScalarChart707
section

namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]
theorem scalarOfChartDvd {f g : Polynomial (Polynomial K)} (hf : Irreducible f)
    (hg : Irreducible g) (h : f ∣ g) : ∃ c : K, g = f * C (C c) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨a, ha, har⟩ := Polynomial.isUnit_iff.mp ((hg.isUnit_or_isUnit hr).resolve_left hf.not_isUnit)
  obtain ⟨c, _, hca⟩ := Polynomial.isUnit_iff.mp ha
  exact ⟨c, by rw [hr, ←har, ←hca]⟩
theorem chartResultantOfNonScalar {f g : Polynomial (Polynomial K)} (hf : Irreducible f)
    (hg : Irreducible g) (hd : f.natDegree ≠ 0) (hn : ∀ c : K, g ≠ f * C (C c)) :
    f.resultant g ≠ 0 := by
  apply chartResultant f g (hf.isPrimitive hd) hf
  intro h
  obtain ⟨c,hc⟩ := scalarOfChartDvd hf hg h
  exact hn c hc

end E707Partial

end

-- Bundled module: DiagScale707
section

namespace E707Partial
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R]
def scaleVar (z : Rˣ) : R[X] ≃+* R[X] :=
  letI : Invertible (z:R) := ⟨↑z⁻¹, z.inv_val, z.val_inv⟩
  (algEquivCMulXAddC (z:R) 0).toRingEquiv
@[simp] theorem scaleVar_coeff (z : Rˣ) (f : R[X]) (i : ℕ) :
    ((scaleVar z) f).coeff i = f.coeff i * (z:R)^i := by
  simp [scaleVar, algEquivCMulXAddC_apply, ←comp_eq_aeval]
def diagScale (z w : Rˣ) : R[X][X] ≃+* R[X][X] :=
  (mapEquiv (scaleVar z)).trans (scaleVar (Units.map C.toMonoidHom w))
@[simp] theorem diagScale_coeff (z w : Rˣ) (f : R[X][X]) (j i : ℕ) :
    (((diagScale z w) f).coeff j).coeff i = (f.coeff j).coeff i * (z:R)^i * (w:R)^j := by
  change (((scaleVar (Units.map C.toMonoidHom w)) (f.map (scaleVar z).toRingHom)).coeff j).coeff i = _
  rw [scaleVar_coeff, coeff_map]
  change (((scaleVar z) (f.coeff j)) * (C (w:R))^j).coeff i = _
  rw [← C_pow, coeff_mul_C, scaleVar_coeff]

end
end E707Partial

end

-- Bundled module: WeightChart707
section


namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]
theorem weightEqOfScalar (f : K[X][X]) (z : Kˣ) (q : ℕ) (c : K)
    (h : diagScale z (z^q) f = f * C (C c)) (i j : ℕ) (hi : (f.coeff j).coeff i ≠ 0) :
    ↑(z^(i+j*q) : Kˣ) = c := by
  have he := congrArg (fun g : K[X][X] => (g.coeff j).coeff i) h
  simp only [diagScale_coeff, coeff_mul_C, Units.val_pow_eq_pow_val] at he
  apply mul_left_cancel₀ hi
  simpa only [Units.val_pow_eq_pow_val, pow_add, Nat.mul_comm j q, pow_mul, Units.val_mul, mul_assoc] using he

end E707Partial

end

-- Bundled module: TranslateResultant707
section

namespace E707Partial
open Polynomial
variable (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


 theorem translateResultant (p k : ℕ) (hp : p%3=2) (hq : (Fintype.card F)=p^(3^k))
    (h3 : Module.finrank F K = 3) (z : (projectiveImage F K)) (hz : z ≠ 1) (f : K[X][X])
    (hf : Irreducible f) (hd : f.natDegree ≠ 0) (i j l m : ℕ)
    (hi : (f.coeff j).coeff i ≠ 0) (hl : (f.coeff m).coeff l ≠ 0)
    (a b : ℤ) (ha : a=(i:ℤ)-l) (hb : b=(j:ℤ)-m) (hne : a ≠ 0 ∨ b ≠ 0)
    (hk : (a^2-a*b+b^2).toNat ≤ k) :
    f.resultant (diagScale (z:Kˣ) ((z:Kˣ)^(Fintype.card F)) f) ≠ 0 := by
  classical
  apply chartResultantOfNonScalar hf ((MulEquiv.irreducible_iff (diagScale (z:Kˣ) ((z:Kˣ)^(Fintype.card F)))).mpr hf) hd
  intro c hc
  have he : z^(i+j*(Fintype.card F))=z^(l+m*(Fintype.card F)) := Subtype.ext (Units.ext <|
    (weightEqOfScalar f z (Fintype.card F) c hc i j hi).trans (weightEqOfScalar f z (Fintype.card F) c hc l m hl).symm)
  have hh : a+b*(Fintype.card F)=((i+j*(Fintype.card F):ℕ):ℤ)-(l+m*(Fintype.card F):ℕ) := by push_cast; rw [ha,hb]; ring
  have hchar : z^(a+b*(Fintype.card F))=1 := by rw [hh,zpow_sub,zpow_natCast,zpow_natCast,he,mul_inv_cancel]
  have hn := normPeriod_pos a b hne
  have hcard : Fintype.card (projectiveImage F K)=(Fintype.card F)^2+(Fintype.card F)+1 := by rw [← Nat.card_eq_fintype_card,card_projectiveImage F K h3]
  have hN : z^((Fintype.card F)^2+(Fintype.card F)+1)=1 := by rw [← hcard]; exact pow_card_eq_one
  have hnorm := normPeriod z (Fintype.card F) a b hN hchar
  have heq : ((a^2-a*b+b^2).toNat : ℤ)=a^2-a*b+b^2 := Int.toNat_of_nonneg hn.le
  apply hz (noSmallPeriod p k _ hp (hq ▸ hcard) (by omega) hk z ?_)
  rw [← heq] at hnorm
  exact_mod_cast hnorm

end E707Partial

end

-- Bundled module: TranslateCount707
section


namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]
theorem translateCount (f : K[X][X]) (z w : Kˣ) (d : ℕ)
    (hd : f.natDegree ≠ 0) (hx : ∀ j, (f.coeff j).natDegree ≤ d)
    (hr : f.resultant (diagScale z w f) ≠ 0) (S : Finset K)
    (hs : ∀ x ∈ S, ∃ y, (f.map (evalRingHom x)).eval y = 0 ∧
      ((diagScale z w f).map (evalRingHom x)).eval y = 0) :
    S.card ≤ (2*f.natDegree)*d := by
  have hdeg : (diagScale z w f).natDegree ≤ f.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i
    simp [diagScale_coeff,coeff_eq_zero_of_natDegree_lt hj]
  apply (chartIntersection f _ d hx ?_ (Or.inl hd) hr S hs).trans
  · exact Nat.mul_le_mul_right d (by omega)
  · intro j
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    simp [diagScale_coeff,coeff_eq_zero_of_natDegree_lt ((hx j).trans_lt hi)]

end E707Partial

end

-- Bundled module: ScaleEval707
section

namespace E707Partial
open Polynomial
variable {K : Type*} [Field K]
theorem scale_eval (z : Kˣ) (f : K[X]) (x : K) : ((scaleVar z) f).eval x = f.eval (↑z*x) := by
  simp [scaleVar, algEquivCMulXAddC_apply, ←comp_eq_aeval,eval_comp]
theorem diag_eval (z w : Kˣ) (f : K[X][X]) (x y : K) :
    (((diagScale z w f).map (evalRingHom x)).eval y) =
      (f.map (evalRingHom (↑z*x))).eval (↑w*y) := by
  change (((scaleVar (Units.map C.toMonoidHom w) (f.map (scaleVar z).toRingHom)).map _).eval y) = _
  have hhom : (evalRingHom x).comp (scaleVar z).toRingHom = evalRingHom (↑z*x) := by
    apply RingHom.ext
    intro g
    exact scale_eval z _ x
  have hcomp (u : (K[X])ˣ) (g : K[X][X]) : scaleVar u g = g.comp (C (u:K[X])*X) := by
    simp [scaleVar, algEquivCMulXAddC_apply, ←comp_eq_aeval]
  rw [hcomp,map_comp,eval_comp,map_map,hhom]
  simp

end E707Partial

end

-- Bundled module: ChartRatio707
section


namespace E707Partial
open Polynomial Finset
open scoped Classical
variable {K : Type*} [Field K] (G : Subgroup Kˣ)
 theorem chartRatio (S : Finset G) (f : K[X][X]) (q d : ℕ) (t : G)
    (hd : f.natDegree ≠ 0) (hx : ∀ j, (f.coeff j).natDegree ≤ d)
    (hS : ∀ a ∈ S, (f.map (evalRingHom ((a:Kˣ):K))).eval (((a:Kˣ):K)^q) = 0)
    (hr : f.resultant (diagScale (t:Kˣ) ((t:Kˣ)^q) f) ≠ 0) :
    (S.offDiag.filter fun z => z.1/z.2=t).card ≤ 2*f.natDegree*d := by
  classical
  let P := S.offDiag.filter fun z => z.1/z.2=t
  let X : G × G → K := fun z => ((z.2:Kˣ):K)
  have he {a b : G} (h : (a,b) ∈ P) : a=t*b := (div_eq_iff_eq_mul).mp (mem_filter.mp h).2
  have hinj : Set.InjOn X (P : Set _) := by
    rintro ⟨a,b⟩ hab ⟨c,e⟩ hce hh
    have hbe : b=e := Subtype.ext (Units.ext hh)
    exact Prod.ext ((he hab).trans (hbe ▸ (he hce).symm)) hbe
  change P.card ≤ _
  rw [←card_image_of_injOn hinj]
  apply translateCount f _ _ d hd hx hr
  intro x h
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp h
  obtain ⟨ha,hb,_⟩ := mem_offDiag.mp (mem_filter.mp hab).1
  refine ⟨((b:Kˣ):K)^q,hS b hb,?_⟩
  rw [diag_eval]
  have hval : ((t:Kˣ):K)*((b:Kˣ):K) = ((a:Kˣ):K) := congrArg (fun z : G => ((z:Kˣ):K)) (he hab).symm
  change (f.map (evalRingHom (((t:Kˣ):K)*((b:Kˣ):K)))).eval (((t:Kˣ):K)^q*((b:Kˣ):K)^q) = 0
  rw [←mul_pow,hval]; exact hS a ha

end E707Partial

end

-- Bundled module: ChartWitness707
section


namespace E707Partial
open Polynomial Real
variable (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


 theorem chartWitness (p k b u v d : ℕ) (hp : 2 ≤ p) (hp3 : p%3=2)
    (hk : p^(b^2) ≤ 3*3^k) (hq : (Fintype.card F) = p^(3^k)) (h3 : Module.finrank F K = 3)
    (hu : 0<u) (hun : u<(Fintype.card F)^2+(Fintype.card F)+1) (f : K[X][X]) (hf : Irreducible f)
    (hd : f.natDegree ≠ 0) (hx : ∀ j, (f.coeff j).natDegree ≤ d)
    (hb : 8*(1+√((2*f.natDegree*d:ℕ):ℝ)) < b) (i j l m : ℕ)
    (hi : (f.coeff j).coeff i ≠ 0) (hl : (f.coeff m).coeff l ≠ 0)
    (a c : ℤ) (ha : a=(i:ℤ)-l) (hc : c=(j:ℤ)-m) (hne : a ≠ 0 ∨ c ≠ 0)
    (hn : (a^2-a*c+c^2).toNat ≤ k) (S : Finset (projectiveImage F K)) (hsub : S ⊆ locus F K u v)
    (hs : (Fintype.card F) ≤ 2*S.card)
    (hS : ∀ x ∈ S, (f.map (evalRingHom ((x:Kˣ):K))).eval (((x:Kˣ):K)^(Fintype.card F)) = 0) :
    ∃ (α : K) (s t : F), IsPrimitiveRoot (α^((Fintype.card F)-1)) ((Fintype.card F)^2+(Fintype.card F)+1) ∧
      α^v = algebraMap F K s + algebraMap F K t * α^u := by
  apply packedWitness F K p k _ b u v hp hp3 hk hb hq h3 hu hun S hsub hs
  intro t ht
  exact chartRatio (projectiveImage F K) S f (Fintype.card F) d t hd hx hS (translateResultant F K p k hp3 hq h3 t ht f hf hd i j l m hi hl a c ha hc hne hn)

end E707Partial

end

-- Bundled module: DetChart707
section

namespace E707Partial
open Polynomial
variable (K : Type*) [Field K]
/-- Sawin's determinant for the normalized projective conjugates (1,x,xy). -/
noncomputable def detChart (u v : ℕ) : K[X][X] :=
  let x : K[X][X] := C X
  let y : K[X][X] := X
  (x^v-1)*((x*y)^u-x^u)-((x*y)^v-x^v)*(x^u-1)
variable (F : Type*) [Field F] [Fintype F] [Fintype K] [Algebra F K]

 theorem locusOfFactor {u v : ℕ} (f : K[X][X]) (hf : f ∣ detChart K u v)
    (S : Finset (projectiveImage F K))
    (hS : ∀ x ∈ S, (f.map (evalRingHom ((x:Kˣ):K))).eval (((x:Kˣ):K)^(Fintype.card F))=0) :
    S ⊆ locus F K u v := by
  classical
  intro z hz
  let x : K := (z:Kˣ)
  let e := (evalRingHom (x^(Fintype.card F))).comp (mapRingHom (evalRingHom x))
  have hzero : e f = 0 := hS z hz
  obtain ⟨g,hg⟩ := hf
  have hd : e (detChart K u v) = 0 := by rw [hg,map_mul,hzero,zero_mul]
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  apply sub_eq_zero.mp
  simpa [e,x,detChart] using hd

end E707Partial

end

-- Bundled module: DetUniform
section

namespace E707Geometry
open E707Partial Polynomial
variable {K : Type*} [Field K]
theorem detChart_ne_zero (u v : ℕ) (hu : 0<u) (hv : u<v) : detChart K u v ≠ 0 := by
  intro he
  have h := congrArg (Polynomial.eval (0 : K[X])) he
  have h1 : (X : K[X])^u = X^v := by
    simp [detChart,hu.ne',(hu.trans hv).ne'] at h
    linear_combination h
  have := congrArg Polynomial.natDegree h1
  simp only [natDegree_X_pow] at this; omega
noncomputable def integerChart (u v : ℕ) : ℤ[X][X] :=
  let x : ℤ[X][X] := C X
  let y : ℤ[X][X] := X
  (x^v-1)*((x*y)^u-x^u)-((x*y)^v-x^v)*(x^u-1)
theorem map_integerChart (u v : ℕ) :
    (integerChart u v).map (mapRingHom (Int.castRingHom K)) = detChart K u v := by
  simp [integerChart,detChart]
noncomputable def chartBudget (u v : ℕ) : ℕ := let P := integerChart u v
  P.natDegree + P.support.sup (fun j => (P.coeff j).natDegree)
theorem det_bidegree (u v : ℕ) : (detChart K u v).natDegree ≤ chartBudget u v ∧
    ∀ j, ((detChart K u v).coeff j).natDegree ≤ chartBudget u v := by
  rw [← map_integerChart]; constructor
  · exact natDegree_map_le.trans (Nat.le_add_right ..)
  · intro j; rw [coeff_map]; change ((integerChart u v).coeff j |>.map _).natDegree ≤ _
    apply natDegree_map_le.trans
    by_cases hj : j ∈ (integerChart u v).support
    · exact (Finset.le_sup (f:=fun i => ((integerChart u v).coeff i).natDegree) hj).trans (Nat.le_add_left ..)
    · simp [notMem_support_iff.mp hj]
end E707Geometry


end

-- Bundled module: DenseTorusFactor
section


namespace E707Geometry
open E707Partial Polynomial
variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


/-- Linear-size projective locus gives a linear-size single torus-chart factor,
with loss uniform in the cubic extension and characteristic. -/
theorem denseTorusFactor (u v : ℕ) (hu : 0<u) (hv : u<v) (S : Finset (projectiveImage F K))
    (hS : S ⊆ locus F K u v) (hs : (Fintype.card F) ≤ 2*S.card) :
    ∃ (g : K[X][X]) (T : Finset (projectiveImage F K)), Irreducible g ∧ g ∣ detChart K u v ∧
      T ⊆ locus F K u v ∧ (Fintype.card F) ≤ (4*chartBudget u v)*T.card ∧
      ∀ z ∈ T, (g.map (evalRingHom ((z:Kˣ):K))).eval (((z:Kˣ):K)^(Fintype.card F))=0 := by
  classical
  obtain ⟨hy,hx⟩ := det_bidegree (K:=K) u v
  have hn : S.Nonempty := by
    apply Finset.card_pos.mp
    have := Fintype.card_pos (α:=F); omega
  obtain ⟨g,T,hi,hdiv,hsub,hz,hcount⟩ := chartFactorPigeon
    (fun z : (projectiveImage F K) => ((z:Kˣ):K)) (Fintype.card F) _ _ (detChart_ne_zero (K:=K) u v hu hv) hy hx S hn (by
      intro z h
      have he := (Finset.mem_filter.mp (hS h)).2
      exact (by simpa [detChart] using (sub_eq_zero.mpr he)))
  refine ⟨g,T,hi,hdiv,hsub.trans hS,?_,hz⟩
  calc (Fintype.card F) ≤ 2*S.card := hs
       _ ≤ _ := Nat.mul_le_mul_left 2 hcount
       _ = _ := by ring
end E707Geometry

end

-- Bundled module: DenseChart707
section

namespace E707Partial
open Polynomial Finset
open scoped Classical
variable {K : Type*} [Field K]

/-- A dense set of torus roots forces a term below the highest outer power. -/
theorem denseChartLowerCoeff (G : Subgroup Kˣ) (T : Finset G) (f : K[X][X])
    (hf : f ≠ 0) (q d : ℕ) (hx : ∀ j, (f.coeff j).natDegree ≤ d) (hT : d < T.card)
    (hv : ∀ z ∈ T, (f.map (evalRingHom ((z:Kˣ):K))).eval (((z:Kˣ):K)^q) = 0) :
    ∃ m < f.natDegree, f.coeff m ≠ 0 := by
  classical
  by_contra! h
  have he : f = monomial f.natDegree f.leadingCoeff := by
    apply Polynomial.ext
    intro j
    rcases lt_trichotomy j f.natDegree with hj|rfl|hj
    · simp [coeff_monomial,ne_of_gt hj,h j hj]
    · simp
    · simp [coeff_monomial,ne_of_lt hj,coeff_eq_zero_of_natDegree_lt hj]
  let X : G → K := fun z => ((z:Kˣ):K)
  have hinj : Function.Injective X := fun _ _ hh => Subtype.ext (Units.ext hh)
  have hr : (T.image X).card ≤ f.leadingCoeff.natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hmem
    obtain ⟨z,hz,rfl⟩ := mem_image.mp (show x ∈ T.image X from hmem)
    apply (mem_roots (leadingCoeff_ne_zero.mpr hf)).mpr
    have hh := hv z hz
    conv at hh => lhs; arg 2; arg 2; rw [he]
    simpa [IsRoot,X, map_monomial, eval_monomial] using hh
  rw [card_image_of_injective _ hinj] at hr
  exact (not_lt_of_ge (hr.trans (hx _))) hT

private theorem diffNormBound (a b D : ℤ) (ha : -D ≤ a) (ha' : a ≤ D)
    (hb : -D ≤ b) (hb' : b ≤ D) : a^2-a*b+b^2 ≤ 3*D^2 := by
  nlinarith [mul_nonneg (show 0 ≤ D+a by omega) (show 0 ≤ D-a by omega),
    mul_nonneg (show 0 ≤ D+b by omega) (show 0 ≤ D-b by omega),sq_nonneg (a+b)]

variable (F L : Type) [Field F] [Fintype F] [Field L] [Fintype L] [Algebra F L]



theorem denseChartRatio (p k d : ℕ) (hp : p%3=2) (hq : (Fintype.card F)=p^(3^k))
    (h3 : Module.finrank F L = 3) (hk : 3*d^2 ≤ k) (T : Finset (projectiveImage F L)) (hT : d < T.card)
    (f : L[X][X]) (hf : Irreducible f) (hy : f.natDegree ≤ d)
    (hx : ∀ j, (f.coeff j).natDegree ≤ d)
    (hv : ∀ z ∈ T, (f.map (evalRingHom ((z: Lˣ): L))).eval (((z: Lˣ): L)^(Fintype.card F)) = 0)
    (t : (projectiveImage F L)) (ht : t ≠ 1) : (T.offDiag.filter fun z => z.1/z.2=t).card ≤ 2*d^2 := by
  classical
  obtain ⟨m,hm,hcm⟩ := denseChartLowerCoeff (projectiveImage F L) T f hf.ne_zero (Fintype.card F) d hx hT hv
  let j := f.natDegree
  let i := (f.coeff j).natDegree
  let l := (f.coeff m).natDegree
  have hi : (f.coeff j).coeff i ≠ 0 := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero)
  have hl : (f.coeff m).coeff l ≠ 0 := leadingCoeff_ne_zero.mpr hcm
  have hd : f.natDegree ≠ 0 := by omega
  apply (chartRatio (projectiveImage F L) T f (Fintype.card F) d t hd hx hv ?_).trans (by nlinarith [Nat.mul_le_mul_right d hy])
  apply translateResultant F L p k hp hq h3 t ht f hf hd i j l m hi hl _ _ rfl rfl (Or.inr (by dsimp [j]; omega))
  have hi' : i ≤ d := hx j
  have hl' : l ≤ d := hx m
  have hj' : j ≤ d := hy
  have hm' : m ≤ d := hm.le.trans hy
  have H := diffNormBound ((i:ℤ)-l) ((j:ℤ)-m) (d:ℤ) (by omega) (by omega) (by omega) (by omega)
  apply le_trans _ hk
  rw [Int.toNat_le]
  exact_mod_cast H

end E707Partial

end

-- Bundled module: DenseTower
section




namespace E707Geometry
open E707Partial Polynomial
/-- Tower parameters can simultaneously absorb index, density and multiplicity thresholds. -/
theorem chooseDenseTower (B L Q d : ℕ) : ∃ (p k b : ℕ) (F K : Type) (_ : Field F) (_ : Fintype F)
    (_ : Field K) (_ : Fintype K) (_ : Algebra F K), CharP F p ∧ CharP K p ∧ B<p ∧ p.Prime ∧
    p%3=2 ∧ L≤k ∧ 3*d^2≤k ∧ p^(b^2)≤3*3^k ∧
    4*(1+Real.sqrt ((2*d^2:ℕ):ℝ))*((4*d:ℕ):ℝ)<b ∧
    Fintype.card F=p^(3^k) ∧ Q≤Fintype.card F ∧ 4*d*d<Fintype.card F ∧ Module.finrank F K=3 := by
  obtain ⟨p,hpB,hp,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq B (q:=3) (a:=2) (by decide) (by decide)
  obtain ⟨b,hb⟩ := exists_nat_gt (4*(1+Real.sqrt ((2*d^2:ℕ):ℝ))*((4*d:ℕ):ℝ))
  let k := max (max L (3*d^2)) (max (p^(b^2)) (max Q (4*d*d)))
  have hk : k < 3^k := Nat.lt_pow_self (by decide)
  have hq : k < p^(3^k) := hk.trans (Nat.lt_pow_self hp.one_lt)
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p (3^k)
  letI : NeZero (3^k) := ⟨by positivity⟩
  let K := FiniteField.Extension F p 3
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite K
  have hF : Fintype.card F = p^(3^k) := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p _ (by positivity)
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  refine ⟨p,k,b,F,K,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,hpB,hp,hmod,?_,?_,?_,hb,hF,?_,?_,FiniteField.finrank_extension F p 3⟩
  all_goals dsimp only [k] at *; omega
end E707Geometry

end

-- Bundled module: ChartAlpha
section


namespace E707Geometry
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]


noncomputable def chartAlpha (x : K) (v : Fin 2 → F) : K :=
  ∑ j : Fin 3, algebraMap F K ((Fin.cons 1 v : Fin 3 → F) j) * x^j.val

omit [Fintype K] in
private theorem coeff_zero (x : K) (hx : Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val)))
    (a : Fin 3 → F) (h : (∑ j, algebraMap F K (a j) * x^j.val) = 0) : ∀ j, a j = 0 := by
  have hz : (fun j => algebraMap F K (a j)) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero hx
    intro i
    let e := (FiniteField.frobeniusAlgHom F K)^i.val
    have he := congrArg (fun y => e y) h
    simpa only [map_sum,map_mul,map_pow,AlgHom.commutes,map_zero,
      e,AlgHom.coe_pow,FiniteField.coe_frobeniusAlgHom,pow_iterate] using he
  intro j
  apply (algebraMap F K).injective
  simpa using congrFun hz j

omit [Fintype K] in
theorem chartAlpha_ne_zero (x : K) (hx : Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val)))
    (v : Fin 2 → F) : chartAlpha x v ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : F) ≠ 0) (coeff_zero x hx (Fin.cons 1 v) h 0)

theorem chartAlpha_power_injective (x : K) (hx : Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val))) :
    Function.Injective (fun v : Fin 2 → F => (chartAlpha x v)^((Fintype.card F)-1)) := by
  intro v w he
  change (chartAlpha x v)^((Fintype.card F)-1) = (chartAlpha x w)^((Fintype.card F)-1) at he
  let z := chartAlpha x v / chartAlpha x w
  have hw := chartAlpha_ne_zero x hx w
  have h1 : z^((Fintype.card F)-1) = 1 := by
    rw [show z = _ / _ from rfl,div_pow,he,div_self (pow_ne_zero _ hw)]
  have hf : z^(Fintype.card F) = z := by
    calc _ = z^(((Fintype.card F)-1)+1) := by rw [Nat.sub_add_cancel Fintype.card_pos]
         _ = z := by rw [pow_succ,h1,one_mul]
  have hz : z ∈ (algebraMap F K).range := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed z).mpr
    intro f
    obtain ⟨n,rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).surjective f
    rw [AlgEquiv.coe_pow]
    exact Function.iterate_fixed (f := ⇑(FiniteField.frobeniusAlgEquivOfAlgebraic F K)) hf _
  obtain ⟨r,hr⟩ := hz
  have hm : chartAlpha x v = algebraMap F K r * chartAlpha x w := by
    rw [hr,div_mul_cancel₀ _ hw]
  have hc := coeff_zero x hx (fun j => (Fin.cons 1 v : Fin 3 → F) j - r * (Fin.cons 1 w : Fin 3 → F) j) (by
    simp only [map_sub,map_mul,sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
    exact sub_eq_zero.mpr hm)
  have hr1 : r = 1 := by simpa using (sub_eq_zero.mp (hc 0)).symm
  funext j
  simpa [hr1] using sub_eq_zero.mp (hc j.succ)

end E707Geometry


end

-- Bundled module: ComponentDescent
section

open MvPolynomial
namespace E707Geometry
/-- Descend the equation of a stable geometric component, not the entire residual.
Normalizing one nonzero coefficient removes the scalar ambiguity. -/
theorem descendAssociated {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    (σ : K →+* K) (fixed : ∀ k, σ k = k → ∃ a : F, algebraMap F K a = k)
    (p : MvPolynomial ι K) (hp : p ≠ 0) (h : Associated p (p.map σ)) :
    ∃ f : MvPolynomial ι F, Associated p (f.map (algebraMap F K)) := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, p.coeff i ≠ 0 := by
    by_contra! hh
    exact hp (by ext i; simp [hh])
  obtain ⟨u,hu⟩ := h
  obtain ⟨r,hr,he⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  rw [he] at hu
  have hcoeff (j) : σ (p.coeff j) = r * p.coeff j := by
    have H := congrArg (coeff j) hu.symm
    simpa [coeff_map,mul_comm p (C r)] using H
  let g := C (p.coeff i)⁻¹ * p
  have hmem : g ∈ Set.range (MvPolynomial.map (algebraMap F K)) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro v hv
    obtain ⟨j,-,rfl⟩ := mem_coeffs_iff.mp hv
    apply fixed
    simp only [g,coeff_C_mul,map_mul,map_inv₀,hcoeff]
    field_simp [hr.ne_zero,hi]
  obtain ⟨f,hf⟩ := hmem
  refine ⟨f,?_⟩
  rw [hf]
  exact ⟨(Units.map (MvPolynomial.C : K →+* MvPolynomial ι K).toMonoidHom (Units.mk0 _ (inv_ne_zero hi))), by simp [g,mul_comm]⟩
end E707Geometry

end

-- Bundled module: Torus
section



namespace E707Geometry
/-- Pullback on monomials x^a w^b after eliminating y=w^r/x^q. -/
def rotExponent (q r s : ℤ) : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun z := (-(q+1)*z.1-s*z.2,r*z.1+q*z.2)
  map_zero' := by simp
  map_add' a b := by ext <;> simp <;> ring

theorem rotExponent_cube {q r s : ℤ} (h : r*s=q^2+q+1) (z : ℤ × ℤ) :
    rotExponent q r s (rotExponent q r s (rotExponent q r s z)) = z := by
  rcases z with ⟨a,b⟩
  apply Prod.ext <;> simp [rotExponent] <;> grind

def rotLattice {q r s : ℤ} (h : r*s=q^2+q+1) : (ℤ × ℤ) ≃+ (ℤ × ℤ) where
  toFun := rotExponent q r s
  invFun := fun z => rotExponent q r s (rotExponent q r s z)
  left_inv := rotExponent_cube h
  right_inv := rotExponent_cube h
  map_add' := map_add _

noncomputable def rotTorus (K : Type*) [CommRing K] {q r s : ℤ} (h : r*s=q^2+q+1) :=
  AddMonoidAlgebra.domCongr K K (rotLattice h)

theorem rotTorus_cube (K : Type*) [CommRing K] {q r s : ℤ} (h : r*s=q^2+q+1)
    (f : AddMonoidAlgebra K (ℤ × ℤ)) : rotTorus K h (rotTorus K h (rotTorus K h f)) = f := by
  ext z
  simp only [rotTorus, AddMonoidAlgebra.coeff_domCongr]
  change f.coeff (rotExponent q r s (rotExponent q r s (rotExponent q r s
    (rotExponent q r s (rotExponent q r s (rotExponent q r s z)))))) = f.coeff z
  rw [rotExponent_cube h, rotExponent_cube h]

/-- The cubic descent operator: act on coefficients and characters together. -/
noncomputable def twistTorus {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) {q r s : ℤ} (h : r*s=q^2+q+1) :=
  (AddMonoidAlgebra.mapAlgEquiv k (ℤ × ℤ) σ).trans
    (AddMonoidAlgebra.domCongr k K (rotLattice h))

theorem coeff_twist {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) {q r s : ℤ} (h : r*s=q^2+q+1) (f : AddMonoidAlgebra K (ℤ × ℤ)) (z) :
    ((twistTorus σ h) f).coeff z = σ (f.coeff ((rotLattice h).symm z)) := by
  simp [twistTorus, AddMonoidAlgebra.mapAlgEquiv, AddMonoidAlgebra.mapAlgHom]

theorem twistTorus_cube {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) (hc : ∀ a, σ (σ (σ a)) = a) {q r s : ℤ} (h : r*s=q^2+q+1)
    (f : AddMonoidAlgebra K (ℤ × ℤ)) : twistTorus σ h (twistTorus σ h (twistTorus σ h f)) = f := by
  ext z
  simp only [coeff_twist, hc]
  change f.coeff (rotExponent q r s (rotExponent q r s (rotExponent q r s
    (rotExponent q r s (rotExponent q r s (rotExponent q r s z)))))) = f.coeff z
  rw [rotExponent_cube h, rotExponent_cube h]

noncomputable def rationalTorusRing {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) {q r s : ℤ} (h : r*s=q^2+q+1) : Subalgebra k (AddMonoidAlgebra K (ℤ × ℤ)) :=
  AlgHom.equalizer (twistTorus σ h).toAlgHom (AlgHom.id _ _)

theorem finiteTwist_cube (k K : Type*) [Field k] [Fintype k] [Field K] [Algebra k K]
    [FiniteDimensional k K] (hd : Module.finrank k K = 3) {r s : ℤ}
    (h : r*s=(Fintype.card k : ℤ)^2 + Fintype.card k + 1) (f : AddMonoidAlgebra K (ℤ × ℤ)) :
    let τ := twistTorus (FiniteField.frobeniusAlgEquivOfAlgebraic k K) h
    τ (τ (τ f)) = f := by
  apply twistTorus_cube
  intro a
  let : Finite K := Module.finite_of_finite k
  have hh := pow_orderOf_eq_one (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
  rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hd] at hh
  simpa [pow_succ, AlgEquiv.mul_apply] using DFunLike.congr_fun hh a

theorem eval_twist_iff {k K : Type*} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) {q r s : ℤ} (h : r*s=q^2+q+1)
    (χ : Multiplicative (ℤ × ℤ) →* K) :
    (∀ f, AddMonoidAlgebra.lift K K _ χ (twistTorus σ h f) = σ (AddMonoidAlgebra.lift K K _ χ f)) ↔
      ∀ z, χ (.ofAdd (rotLattice h z)) = σ (χ (.ofAdd z)) := by
  have hs (z : ℤ × ℤ) (a : K) : twistTorus σ h (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (rotLattice h z) (σ a) := by
    simp [twistTorus, AddMonoidAlgebra.mapAlgEquiv, AddMonoidAlgebra.mapAlgHom]
  constructor
  · intro H z
    simpa [hs] using H (AddMonoidAlgebra.single z 1)
  · intro H f
    induction f using AddMonoidAlgebra.induction with
    | zero => simp
    | single_add z a f _ _ ih => simp [hs, H, ih, smul_eq_mul]
end E707Geometry




end

-- Bundled module: Covariance
section

namespace E707Geometry
variable {R : Type*} [CommRing R]
/-- Alternant in the chart (1,x,y), following Sawin, MO 501999. -/
def altChart (a b : ℕ) (x y : R) := (x^a-1)*(y^b-1)-(y^a-1)*(x^b-1)
/-- Clear the common homogeneous scale under cyclic rotation. Valid in any
commutative ring, including the Laurent coordinate algebra itself. -/
theorem rot_altChart (a b : ℕ) (x y u v : R) (hu : u*x=y) (hv : v*x=1) :
    altChart a b u v * x^(a+b) = altChart a b x y := by
  have hu' (n : ℕ) : u^n*x^n=y^n := by rw [←mul_pow,hu]
  have hv' (n : ℕ) : v^n*x^n=1 := by rw [←mul_pow,hv,one_pow]
  unfold altChart
  rw [pow_add]
  calc
    _ = (u^a*x^a-x^a)*(v^b*x^b-x^b)-(v^a*x^a-x^a)*(u^b*x^b-x^b) := by ring
    _ = _ := by rw [hu',hv',hu',hv']; ring

theorem rot_vandermonde (c : ℕ) (x y u v : R) (hu : u*x=y) (hv : v*x=1) :
    ((u^c-1)*(v^c-1)*(v^c-u^c))*x^(3*c) = (x^c-1)*(y^c-1)*(y^c-x^c) := by
  have hu' : u^c*x^c=y^c := by rw [←mul_pow,hu]
  have hv' : v^c*x^c=1 := by rw [←mul_pow,hv,one_pow]
  rw [Nat.mul_comm,pow_mul]
  calc
    _ = (u^c*x^c-x^c)*(v^c*x^c-x^c)*(v^c*x^c-u^c*x^c) := by ring
    _ = _ := by rw [hu',hv']; ring

/-- Covariance of the quotient itself: only cancel the Vandermonde in a
 domain before passage to the curve, not in a singular specialization. -/
theorem rot_quotient [IsDomain R] {a b c d : ℕ} (hd : d+3*c=a+b)
    (x y u v P Q : R) (hu : u*x=y) (hv : v*x=1)
    (D : (x^c-1)*(y^c-1)*(y^c-x^c) ≠ 0)
    (hP : P*((x^c-1)*(y^c-1)*(y^c-x^c)) = altChart a b x y)
    (hQ : Q*((u^c-1)*(v^c-1)*(v^c-u^c)) = altChart a b u v) : Q*x^d=P := by
  apply mul_right_cancel₀ D
  rw [hP, ←rot_altChart a b x y u v hu hv, ← hQ, ←hd, pow_add,
    ←rot_vandermonde c x y u v hu hv]
  ring
end E707Geometry



end

-- Bundled module: Equation
section

namespace E707Geometry
variable {R : Type*} [CommRing R]
def geomChart (x : R) : ℕ → R
  | 0 => 0
  | n+1 => 1+x*geomChart x n

def diffChart (x y : R) : ℕ → R
  | 0 => 0
  | n+1 => geomChart x n + y*diffChart x y n

theorem geomChart_spec (x : R) (n : ℕ) : (x-1)*geomChart x n=x^n-1 := by
  induction n with
  | zero => simp [geomChart]
  | succ n ih => simp only [geomChart,pow_succ]; linear_combination x*ih

theorem diffChart_spec (x y : R) (n : ℕ) : (y-x)*diffChart x y n=geomChart y n-geomChart x n := by
  induction n with
  | zero => simp [geomChart,diffChart]
  | succ n ih => simp only [geomChart,diffChart]; linear_combination y*ih

/-- Polynomial, division-free form of the coprime alternant quotient. -/
def equationChart (a b : ℕ) (x y : R) := geomChart x a * diffChart x y b - geomChart x b * diffChart x y a

theorem equationChart_spec (a b : ℕ) (x y : R) :
    equationChart a b x y * ((x-1)*(y-1)*(y-x)) = altChart a b x y := by
  unfold equationChart altChart
  rw [←geomChart_spec x a,←geomChart_spec y b,←geomChart_spec y a,←geomChart_spec x b]
  linear_combination (x-1)*(y-1)*(geomChart x a * diffChart_spec x y b - geomChart x b * diffChart_spec x y a)
end E707Geometry

end

-- Bundled module: Stability
section



namespace E707Geometry
open AddMonoidAlgebra
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
private abbrev A (K : Type*) [Field K] := AddMonoidAlgebra K (ℤ × ℤ)
noncomputable abbrev m (K : Type*) [Field K] (z : ℤ × ℤ) : A K := single z 1
private theorem tau_m (σ : K ≃ₐ[k] K) {q r s : ℤ} (h : r*s=q^2+q+1) (z) :
    twistTorus σ h (m K z) = m K (rotExponent q r s z) := by
  simp [m,twistTorus, AddMonoidAlgebra.mapAlgEquiv, AddMonoidAlgebra.mapAlgHom,rotLattice]

theorem twistEquation {q r s : ℤ} (h : r*s=q^2+q+1) (hr : r ≠ 0)
    (σ : K ≃ₐ[k] K) (a b d : ℕ) (hd : d+3=a+b) :
    let x := m K (1,0); let y := m K (-q,r); let τ := twistTorus σ h
    τ (equationChart a b x y) * x^d = equationChart a b x y := by
  dsimp only
  let x := m K (1,0); let y := m K (-q,r); let τ := twistTorus σ h
  change τ (equationChart a b x y) * x^d = equationChart a b x y
  have hu : τ x*x=y := by
    dsimp only [τ,x,y]; rw [tau_m]; simp [m,single_mul_single, rotExponent]
  have hv : τ y*x=1 := by
    dsimp only [τ,x,y]; rw [tau_m]; simp only [m,single_mul_single,one_mul]
    change single _ (1:K) = single (0 : ℤ × ℤ) 1
    congr 1; ext <;> simp [rotExponent] <;> grind
  have D : (x-1)*(y-1)*(y-x) ≠ 0 := by
    have hone : (1:A K) = m K 0 := rfl
    simp [hone,x,y,m,sub_ne_zero,single_left_inj,Prod.ext_iff,hr]
  have spec := equationChart_spec a b x y
  have Q := congrArg τ spec
  simp only [map_mul,map_sub,map_one,altChart,map_pow] at Q
  apply rot_quotient (c:=1) (by omega : d+3*1=a+b) x y (τ x) (τ y) _ _ hu hv
  · simpa using D
  · simpa using spec
  · simpa [altChart] using Q

/-- The actual principal ideal, not only its point set, is invariant. -/
theorem twistEquationIdeal {q r s : ℤ} (h : r*s=q^2+q+1) (hr : r ≠ 0)
    (σ : K ≃ₐ[k] K) (a b d : ℕ) (hd : d+3=a+b) :
    let P := equationChart a b (m K (1,0)) (m K (-q,r))
    Ideal.map (twistTorus σ h).toRingHom (Ideal.span {P}) = Ideal.span {P} := by
  dsimp only
  rw [Ideal.map_span,Set.image_singleton,Ideal.span_singleton_eq_span_singleton]
  have hx : IsUnit (m K (1,0)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨m K (-1,0), ?_⟩
    simp [m,single_mul_single]; rfl
  obtain ⟨u,hu⟩ := hx.pow d
  exact ⟨u, by simpa [hu] using twistEquation h hr σ a b d hd⟩
end E707Geometry


end

-- Bundled module: CurveAction
section


namespace E707Geometry
noncomputable def chartIdeal (K : Type*) [Field K] (q r : ℤ) (a b : ℕ) :=
  Ideal.span {equationChart a b (m K (1,0)) (m K (-q,r))}
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
noncomputable def curveTwist {q r s : ℤ} (h : r*s=q^2+q+1) (hr : r ≠ 0)
    (σ : K ≃ₐ[k] K) (a b d : ℕ) (hd : d+3=a+b) :=
  Ideal.quotientEquivAlg (chartIdeal K q r a b) (chartIdeal K q r a b) (twistTorus σ h)
    (twistEquationIdeal h hr σ a b d hd).symm

theorem curveTwist_cube {q r s : ℤ} (h : r*s=q^2+q+1) (hr : r ≠ 0)
    (σ : K ≃ₐ[k] K) (hc : ∀ z, σ (σ (σ z))=z) (a b d : ℕ) (hd : d+3=a+b)
    (z : AddMonoidAlgebra K (ℤ × ℤ) ⧸ chartIdeal K q r a b) :
    let τ := curveTwist h hr σ a b d hd
    τ (τ (τ z)) = z := by
  obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk _ (twistTorus σ h (twistTorus σ h (twistTorus σ h w))) = _
  rw [twistTorus_cube σ hc]
end E707Geometry

end

-- Bundled module: FixedUnique
section

namespace E707Geometry
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
/-- Uniqueness of coordinates in the cubic power basis over the fixed algebra.
The target ring need not be reduced or an integral domain. -/
theorem cubicFixedUnique (τ : A ≃+* A) (σ : K ≃+* K)
    (hs : ∀ c : K, τ (algebraMap K A c) = algebraMap K A (σ c))
    (t : K) (h₁ : t ≠ σ t) (h₂ : t ≠ σ (σ t))
    (x y z : A) (hx : τ x = x) (hy : τ y = y) (hz : τ z = z)
    (H : x + algebraMap K A t * y + (algebraMap K A t)^2 * z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  let f := algebraMap K A
  have e₁ := congrArg τ H
  simp only [map_add,map_mul,map_pow,map_zero,hs,hx,hy,hz] at e₁
  have e₂ := congrArg τ e₁
  simp only [map_add,map_mul,map_pow,map_zero,hs,hx,hy,hz] at e₂
  have cancel (a : K) (ha : a ≠ 0) (w : A) (hw : f a*w=0) : w=0 := by
    have e := congrArg (fun v => f a⁻¹ * v) hw
    simpa only [←mul_assoc, ← map_mul, inv_mul_cancel₀ ha,map_one,one_mul,mul_zero] using e
  have hbc : σ t ≠ σ (σ t) := σ.injective.ne h₁
  have Z : z=0 := by
    apply cancel ((t-σ t)*(t-σ (σ t))*(σ t-σ (σ t))) (by exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂)) (sub_ne_zero.mpr hbc))
    simp only [f,map_mul,map_sub]
    linear_combination (algebraMap K A (σ t)-algebraMap K A (σ (σ t)))*H - (algebraMap K A t-algebraMap K A (σ (σ t)))*e₁ + (algebraMap K A t-algebraMap K A (σ t))*e₂
  subst z
  simp only [mul_zero,add_zero] at H e₁
  have Y : y=0 := by
    apply cancel (t-σ t) (sub_ne_zero.mpr h₁)
    simp only [f,map_sub]; linear_combination H-e₁
  exact ⟨by simpa [Y] using H,Y,rfl⟩
end E707Geometry

end

-- Bundled module: FixedCoords
section

namespace E707Geometry
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
/-- Interpolate the three orbit values to get three fixed coefficients. -/
theorem cubicFixedCoords (τ : A ≃+* A) (σ : K ≃+* K)
    (hc : ∀ u, σ (σ (σ u)) = u) (ha : ∀ z, τ (τ (τ z)) = z)
    (hs : ∀ u : K, τ (algebraMap K A u) = algebraMap K A (σ u))
    (t : K) (h₁ : t ≠ σ t) (h₂ : t ≠ σ (σ t)) (z : A) :
    ∃ x y w : A, τ x = x ∧ τ y = y ∧ τ w = w ∧
      x + algebraMap K A t * y + algebraMap K A t ^ 2 * w = z := by
  let f := algebraMap K A
  let T (v : A) := v + τ v + τ (τ v)
  have fix (v : A) : τ (T v) = T v := by simp only [T,map_add,ha]; abel
  let b := σ t
  let c := σ b
  let u := f (((t-b)*(t-c))⁻¹) * z
  refine ⟨T (f (b*c)*u), T (-(f (b+c))*u), T u, fix _, fix _, fix _, ?_⟩
  have hb : σ b = c := rfl
  have hct : σ c = t := hc t
  have hf (x : K) : τ (f x) = f (σ x) := hs x
  have e : T (f (b*c)*u) + f t*T (-(f (b+c))*u) + f t ^ 2*T u = f ((t-b)*(t-c))*u := by
    simp only [T,map_mul,map_add,map_sub,map_neg,hf,hb,hct,show σ t = b from rfl]
    ring
  rw [e]; dsimp only [u]; rw [←mul_assoc, ←map_mul, mul_inv_cancel₀ (mul_ne_zero (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂)),map_one,one_mul]
end E707Geometry

end

-- Bundled module: BaseChange
section



open scoped TensorProduct
namespace E707Geometry
variable {k K A : Type*} [Field k] [Field K] [CommRing A]
variable [Algebra k K] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
open TensorProduct
/-- Coordinate normal form for the tensor, obtained before applying multiplication. -/
theorem tensorCubicCoords (B : Subalgebra k A) (t : K)
    (h : ∀ u : K, ∃ i j l : k, u = i • (1:K) + j • t + l • t^2)
    (z : K ⊗[k] B) : ∃ x y w : B,
      z = (1:K) ⊗ₜ[k] x + t ⊗ₜ[k] y + (t^2) ⊗ₜ[k] w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0,0,0,by simp⟩
  | tmul u v =>
    obtain ⟨i,j,l,rfl⟩ := h u
    exact ⟨i • v,j • v,l • v,by simp only [add_tmul,smul_tmul]⟩
  | add u v hu hv =>
    obtain ⟨x,y,w,rfl⟩ := hu
    obtain ⟨x',y',w',rfl⟩ := hv
    exact ⟨x+x',y+y',w+w',by simp only [tmul_add]; abel⟩

theorem cubicDescentBijective (τ : A ≃ₐ[k] A) (σ : K ≃+* K)
    (hc : ∀ u, σ (σ (σ u)) = u) (ha : ∀ z, τ (τ (τ z)) = z)
    (hs : ∀ u : K, τ (algebraMap K A u) = algebraMap K A (σ u))
    (t : K) (h₁ : t ≠ σ t) (h₂ : t ≠ σ (σ t))
    (ht : ∀ u : K, ∃ i j l : k, u = i • (1:K) + j • t + l • t^2) :
    let B := AlgHom.equalizer τ.toAlgHom (AlgHom.id k A)
    Function.Bijective (AlgHom.liftEquiv k K B A B.val) := by
  let B := AlgHom.equalizer τ.toAlgHom (AlgHom.id k A)
  let f := AlgHom.liftEquiv k K B A B.val
  change Function.Bijective f
  constructor
  · apply (injective_iff_map_eq_zero f).2
    intro z hz
    obtain ⟨x,y,w,rfl⟩ := tensorCubicCoords B t ht z
    simp only [f,map_add,AlgHom.liftEquiv_tmul,map_one,one_mul,Subalgebra.val_apply,Algebra.smul_def,map_pow] at hz
    obtain ⟨hx,hy,hw⟩ := cubicFixedUnique τ.toRingEquiv σ hs t h₁ h₂ x y w x.property y.property w.property hz
    have ex : x=0 := Subtype.ext hx
    have ey : y=0 := Subtype.ext hy
    have ew : w=0 := Subtype.ext hw
    simp [ex,ey,ew]
  · intro z
    obtain ⟨x,y,w,hx,hy,hw,e⟩ := cubicFixedCoords τ.toRingEquiv σ hc ha hs t h₁ h₂ z
    refine ⟨(1:K) ⊗ₜ[k] (⟨x,hx⟩:B) + t ⊗ₜ[k] (⟨y,hy⟩:B) + (t^2) ⊗ₜ[k] (⟨w,hw⟩:B), ?_⟩
    simpa only [f,map_add,AlgHom.liftEquiv_tmul,map_one,one_mul,Subalgebra.val_apply,Algebra.smul_def,map_pow] using e
end E707Geometry

end

-- Bundled module: CurveBaseChange
section


namespace E707Geometry
variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Fintype k] [FiniteDimensional k L]
theorem curveBaseChange (hdim : Module.finrank k L = 3) {q r s : ℤ}
    (h : r*s=q^2+q+1) (hr : r ≠ 0) (a b d : ℕ) (hd : d+3=a+b) :
    let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
    let τ := curveTwist h hr σ a b d hd
    let B := AlgHom.equalizer τ.toAlgHom (AlgHom.id k _)
    Function.Bijective (AlgHom.liftEquiv k L B _ B.val) := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  letI : Finite L := Module.finite_of_finite k
  have ho : orderOf σ = 3 := (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k L).trans hdim
  have hp := pow_orderOf_eq_one σ
  rw [ho] at hp
  have hc (z : L) : σ (σ (σ z)) = z := by
    simpa [pow_succ, AlgEquiv.mul_apply] using DFunLike.congr_fun hp z
  obtain ⟨t, ht⟩ : ∃ t : L, t ≠ σ t := by
    by_contra! H
    have hi : σ = 1 := DFunLike.ext _ _ (fun z => (H z).symm)
    simp [hi] at ho
  have ht' : t ≠ σ (σ t) := fun e => ht ((congrArg σ e).trans (hc t)).symm
  have fixed (v : L) (hv : σ v = v) : ∃ x : k, algebraMap k L x = v := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed v).2
    intro ψ
    obtain ⟨i, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).surjective ψ
    change (σ ^ i.val) v = v
    generalize i.val = n
    induction n with
    | zero => rfl
    | succ n ih => simpa [pow_succ,AlgEquiv.mul_apply,hv] using ih
  refine cubicDescentBijective (curveTwist h hr σ a b d hd) σ.toRingEquiv hc (curveTwist_cube h hr σ hc a b d hd) ?_ t ht ht' ?_
  · intro v
    change Ideal.Quotient.mk _ (twistTorus σ h (AddMonoidAlgebra.single 0 v)) =
      Ideal.Quotient.mk _ (AddMonoidAlgebra.single 0 (σ v))
    simp [twistTorus, AddMonoidAlgebra.mapAlgEquiv, AddMonoidAlgebra.mapAlgHom]
  · intro u
    obtain ⟨x,y,w,hx,hy,hw,e⟩ := cubicFixedCoords σ.toRingEquiv σ.toRingEquiv hc hc (fun _ => rfl) t ht ht' u
    obtain ⟨i,rfl⟩ := fixed x hx
    obtain ⟨j,rfl⟩ := fixed y hy
    obtain ⟨l,rfl⟩ := fixed w hw
    exact ⟨i,j,l,by simpa [Algebra.smul_def,mul_comm] using e.symm⟩
end E707Geometry

end

-- Bundled module: PlaneAlt
section

open MvPolynomial
namespace E707Geometry
variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Fintype k] [FiniteDimensional k L]
/-- The cyclic sum giving the homogeneous alternant numerator on the nonsplit affine chart. -/
noncomputable def planeAlt {ι : Type*} (σ : L ≃ₐ[k] L) (z : MvPolynomial ι L) (a b : ℕ) :=
  let rot := MvPolynomial.map (σ : L →+* L)
  let u := z^a * (rot z)^b - z^b * (rot z)^a
  u + rot u + rot (rot u)

theorem planeAlt_descends {ι : Type*} (hdim : Module.finrank k L = 3)
    (z : MvPolynomial ι L) (a b : ℕ) :
    ∃ p : MvPolynomial ι k, p.map (algebraMap k L) =
      planeAlt (FiniteField.frobeniusAlgEquivOfAlgebraic k L) z a b := by
  classical
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  let rot := MvPolynomial.map (σ : L →+* L) (σ := ι)
  letI : Finite L := Module.finite_of_finite k
  have hp := pow_orderOf_eq_one σ
  rw [(FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k L).trans hdim] at hp
  have hc (x : L) : σ (σ (σ x)) = x := by
    simpa [pow_succ, AlgEquiv.mul_apply] using DFunLike.congr_fun hp x
  have hrot (u : MvPolynomial ι L) : rot (rot (rot u)) = u := by
    ext n; simp only [rot,coeff_map]; exact hc (u.coeff n)
  let f := planeAlt σ z a b
  have inv : rot f = f := by
    change rot (_ + _ + _) = _ + _ + _
    rw [map_add,map_add,hrot]; abel
  apply mem_range_map_iff_coeffs_subset.mpr
  intro v hv
  obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hv
  have hh := congrArg (coeff n) inv
  have hh' : σ (f.coeff n) = f.coeff n := by simp only [rot,coeff_map] at hh; exact hh
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).2
  intro ψ
  obtain ⟨i,rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).surjective ψ
  change (σ ^ i.val) (f.coeff n) = f.coeff n
  generalize i.val = j
  induction j with
  | zero => rfl
  | succ j ih => simpa [pow_succ,AlgEquiv.mul_apply,hh'] using ih
end E707Geometry

end

-- Bundled module: AltQuot
section

namespace E707Geometry
variable {R : Type*} [CommRing R]
/-- Coefficients of T^n reduced modulo T³-sT²+tT-u. -/
def cubicRem (s t u : R) : ℕ → R × R × R
  | 0 => (1,0,0)
  | n+1 => let (i,j,k) := cubicRem s t u n; (k*u,i-k*t,j+k*s)

theorem cubicRem_spec (s t u x : R) (hx : x^3 = s*x^2-t*x+u) (n : ℕ) :
    let v := cubicRem s t u n; x^n = v.1 + v.2.1*x + v.2.2*x^2 := by
  induction n with
  | zero => simp [cubicRem]
  | succ n ih =>
    obtain ⟨i,j,k,h⟩ := (show ∃ i j k, cubicRem s t u n = (i,j,k) from ⟨_,_,_,rfl⟩)
    simp only [cubicRem,h,pow_succ] at ih ⊢
    linear_combination x * ih + k * hx

def altQuot (s t u : R) (a b : ℕ) : R :=
  let v := cubicRem s t u a; let w := cubicRem s t u b
  v.2.1*w.2.2-v.2.2*w.2.1

/-- The symmetric polynomial after removing all three generalized Vandermonde factors. -/
theorem altQuot_spec (x y z : R) (a b : ℕ) :
    altQuot (x+y+z) (x*y+y*z+z*x) (x*y*z) a b * ((y-x)*(z-x)*(z-y)) =
    x^a*y^b-x^b*y^a + (y^a*z^b-y^b*z^a) + (z^a*x^b-z^b*x^a) := by
  let s := x+y+z; let t := x*y+y*z+z*x; let u := x*y*z
  have hx : x^3=s*x^2-t*x+u := by dsimp [s,t,u]; ring
  have hy : y^3=s*y^2-t*y+u := by dsimp [s,t,u]; ring
  have hz : z^3=s*z^2-t*z+u := by dsimp [s,t,u]; ring
  rw [cubicRem_spec _ _ _ _ hx a,cubicRem_spec _ _ _ _ hx b,
      cubicRem_spec _ _ _ _ hy a,cubicRem_spec _ _ _ _ hy b,
      cubicRem_spec _ _ _ _ hz a,cubicRem_spec _ _ _ _ hz b]
  change altQuot s t u a b * _ = _
  unfold altQuot; ring
end E707Geometry

end

-- Bundled module: ChartQuot
section

open MvPolynomial
namespace E707Geometry
variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Fintype k] [FiniteDimensional k L]
variable {ι : Type*}
theorem chartQuot_descends (hdim : Module.finrank k L = 3) (z : MvPolynomial ι L) (a b c : ℕ) :
    let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
    let rot := MvPolynomial.map (σ : L →+* L) (σ := ι)
    let x := z^c; let y := rot x; let w := rot y
    ∃ p : MvPolynomial ι k, p.map (algebraMap k L) = altQuot (x+y+w) (x*y+y*w+w*x) (x*y*w) a b := by
  classical
  intro σ rot x y w
  letI : Finite L := Module.finite_of_finite k
  have hp := pow_orderOf_eq_one σ
  rw [(FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k L).trans hdim] at hp
  have hc (x : L) : σ (σ (σ x)) = x := by
    simpa [pow_succ, AlgEquiv.mul_apply] using DFunLike.congr_fun hp x
  have hrot (u : MvPolynomial ι L) : rot (rot (rot u)) = u := by
    ext n; simp only [rot,coeff_map]; exact hc (u.coeff n)
  have hx : rot x = y := rfl
  have hy : rot y = w := rfl
  have hw : rot w = x := hrot x
  have hs : rot (x+y+w) = x+y+w := by rw [map_add,map_add,hx,hy,hw]; ring
  have ht : rot (x*y+y*w+w*x) = x*y+y*w+w*x := by simp only [map_add,map_mul,hx,hy,hw]; ring
  have hu : rot (x*y*w) = x*y*w := by rw [map_mul,map_mul,hx,hy,hw]; ring
  let v := cubicRem (x+y+w) (x*y+y*w+w*x) (x*y*w)
  have hv (n : ℕ) : rot (v n).1 = (v n).1 ∧ rot (v n).2.1 = (v n).2.1 ∧ rot (v n).2.2 = (v n).2.2 := by
    induction n with
    | zero => simp [v,cubicRem]
    | succ n ih =>
      change _ ∧ _ ∧ _
      simp only [v,cubicRem,map_add,map_sub,map_mul,hs,ht,hu] at *
      simp [ih]
  let f := altQuot (x+y+w) (x*y+y*w+w*x) (x*y*w) a b
  have inv : rot f = f := by
    change rot ((v a).2.1*(v b).2.2-(v a).2.2*(v b).2.1) = _
    rw [map_sub,map_mul,map_mul,(hv a).2.1,(hv b).2.2,(hv a).2.2,(hv b).2.1]; rfl
  apply mem_range_map_iff_coeffs_subset.mpr
  intro v hv
  obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hv
  have hh := congrArg (coeff n) inv
  have hh' : σ (f.coeff n) = f.coeff n := by simp only [rot,coeff_map] at hh; exact hh
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).2
  intro ψ
  obtain ⟨i,rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).surjective ψ
  change (σ ^ i.val) (f.coeff n) = f.coeff n
  generalize i.val = j
  induction j with
  | zero => rfl
  | succ j ih => simpa [pow_succ,AlgEquiv.mul_apply,hh'] using ih
end E707Geometry

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.BivariateWeightedDegree
section




/-!
# Weighted degree of bivariate polynomials

For `g ∈ R[X][Y]` and weights `1` on `X` and `w` on `Y`, we say `g` has *weighted degree at most
`n`* if `deg (coeff_j g) + w j ≤ n` for every `j` with `coeff_j g ≠ 0`. This filtration is closed
under sums, products, powers and derivatives, and reduction modulo a polynomial `Ψ` monic in `Y`
does not increase it when `Ψ` itself has weighted degree `w · deg_Y Ψ`.

## Main definitions

* `Polynomial.Bivariate.WeightedDegreeLE`: the predicate of having weighted degree at most `n`.
* `Polynomial.Bivariate.monomialXY`: the monomial `Xⁱ Yʲ` of `R[X][Y]`.

## Main results

* `Polynomial.Bivariate.WeightedDegreeLE.mul`: weighted degrees add under multiplication.
* `Polynomial.Bivariate.WeightedDegreeLE.modByMonic`: reduction modulo a monic `Ψ` of weighted
  degree `w · deg_Y Ψ` preserves weighted degree.
* `Polynomial.Bivariate.mem_span_monomialXY_of_natDegree_lt`: a polynomial of `Y`-degree `< m`
  all of whose coefficients have degree `≤ N` lies in the span of the `m (N + 1)` monomials
  `Xⁱ Yʲ`, `i ≤ N`, `j < m`.
-/


open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- `g` has weighted degree at most `n` for the weights `1` on `X` and `w` on `Y`. -/
def WeightedDegreeLE (w n : ℕ) (g : R[X][Y]) : Prop :=
  ∀ j, g.coeff j ≠ 0 → (g.coeff j).natDegree + w * j ≤ n

namespace WeightedDegreeLE

variable {w n n' : ℕ} {g h : R[X][Y]}

/-- The zero polynomial has weighted degree at most `n`. -/
theorem zero : WeightedDegreeLE w n (0 : R[X][Y]) := fun j hj => absurd (by simp) hj

/-- Weighted degree at most `n` implies weighted degree at most `n'` for `n ≤ n'`. -/
theorem mono (hg : WeightedDegreeLE w n g) (hn : n ≤ n') : WeightedDegreeLE w n' g :=
  fun j hj => (hg j hj).trans hn

/-- A sum of polynomials of weighted degree at most `n` has weighted degree at most `n`. -/
theorem add (hg : WeightedDegreeLE w n g) (hh : WeightedDegreeLE w n h) :
    WeightedDegreeLE w n (g + h) := by
  intro j hj
  rw [coeff_add] at hj ⊢
  by_cases hgj : g.coeff j = 0
  · rw [hgj, zero_add] at hj ⊢; exact hh j hj
  by_cases hhj : h.coeff j = 0
  · rw [hhj, add_zero] at hj ⊢; exact hg j hj
  have := natDegree_add_le (g.coeff j) (h.coeff j)
  have h1 := hg j hgj
  have h2 := hh j hhj
  omega

/-- The negation of a polynomial of weighted degree at most `n` has weighted degree at most `n`. -/
theorem neg (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (-g) := by
  intro j hj
  rw [coeff_neg, natDegree_neg]
  exact hg j (by simpa using hj)

/-- A difference of polynomials of weighted degree at most `n` has weighted degree at most `n`. -/
theorem sub (hg : WeightedDegreeLE w n g) (hh : WeightedDegreeLE w n h) :
    WeightedDegreeLE w n (g - h) := by
  rw [sub_eq_add_neg]; exact hg.add hh.neg

/-- If `deg a + w j ≤ n`, then `C a * Y ^ j` has weighted degree at most `n`. -/
theorem C_mul_X_pow {a : R[X]} {j : ℕ} (ha : a.natDegree + w * j ≤ n) :
    WeightedDegreeLE w n (C a * X ^ j) := by
  intro j' hj'
  rw [coeff_C_mul_X_pow] at hj' ⊢
  split_ifs at hj' ⊢ with h
  · subst h; exact ha
  · exact absurd rfl hj'

/-- If `deg a ≤ n`, then the constant `C a` has weighted degree at most `n`. -/
theorem C {a : R[X]} (ha : a.natDegree ≤ n) : WeightedDegreeLE w n (C a : R[X][Y]) := by
  simpa using C_mul_X_pow (w := w) (j := 0) (a := a) (by simpa using ha)

/-- A scalar multiple of a polynomial of weighted degree at most `n` has weighted degree at most
`n`. -/
theorem smul (hg : WeightedDegreeLE w n g) (c : R) : WeightedDegreeLE w n (c • g) := by
  intro j hj
  rw [coeff_smul] at hj ⊢
  exact (Nat.add_le_add_right (natDegree_smul_le c _) _).trans (hg j fun h => by simp [h] at hj)

/-- A finite sum of polynomials of weighted degree at most `n` has weighted degree at most `n`. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → R[X][Y]}
    (hf : ∀ i ∈ s, WeightedDegreeLE w n (f i)) : WeightedDegreeLE w n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- If `g` and `h` have weighted degrees at most `n` and `n'`, then `g * h` has weighted degree at
most `n + n'`. -/
theorem mul (hg : WeightedDegreeLE w n g) (hh : WeightedDegreeLE w n' h) :
    WeightedDegreeLE w (n + n') (g * h) := by
  intro j hj
  rw [coeff_mul] at hj ⊢
  have key : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal j, g.coeff x.1 * h.coeff x.2 ≠ 0 →
      (g.coeff x.1 * h.coeff x.2).natDegree + w * j ≤ n + n' := by
    intro x hx hne
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have h1 := hg x.1 (left_ne_zero_of_mul hne)
    have h2 := hh x.2 (right_ne_zero_of_mul hne)
    have : w * j = w * x.1 + w * x.2 := by rw [← mul_add, hx']
    have := natDegree_mul_le (p := g.coeff x.1) (q := h.coeff x.2)
    omega
  obtain ⟨x₀, hx₀, hne₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  have := key x₀ hx₀ hne₀
  refine (Nat.add_le_add_right (natDegree_sum_le_of_forall_le _ _ (n := n + n' - w * j)
    fun x hx => ?_) _).trans (by omega)
  by_cases hne : g.coeff x.1 * h.coeff x.2 = 0
  · simp [hne]
  have := key x hx hne
  omega

/-- The polynomial `1` has weighted degree at most `n`. -/
theorem one : WeightedDegreeLE w n (1 : R[X][Y]) := by
  simpa using C (w := w) (n := n) (a := (1 : R[X])) (by simp)

/-- If `g` has weighted degree at most `n`, then `g ^ k` has weighted degree at most `k * n`. -/
theorem pow (hg : WeightedDegreeLE w n g) (k : ℕ) : WeightedDegreeLE w (k * n) (g ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact ih.mul hg

/-- The `Y`-derivative of a polynomial of weighted degree at most `n` has weighted degree at most
`n`. -/
theorem derivative (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (derivative g) := by
  intro j hj
  rw [coeff_derivative] at hj ⊢
  have hgj : g.coeff (j + 1) ≠ 0 := fun h => by simp [h] at hj
  have := hg (j + 1) hgj
  have h2 := natDegree_mul_le (p := g.coeff (j + 1)) (q := ((j : R[X]) + 1))
  have h3 : ((j : R[X]) + 1).natDegree = 0 := by
    rw [show ((j : R[X]) + 1) = ((j + 1 : ℕ) : R[X]) by push_cast; ring, natDegree_natCast]
  have : w * j ≤ w * (j + 1) := Nat.mul_le_mul_left _ (Nat.le_succ j)
  omega

/-- Every `Y`-coefficient of a polynomial of weighted degree at most `n` has degree at most `n`. -/
theorem coeff_natDegree_le (hg : WeightedDegreeLE w n g) (j : ℕ) : (g.coeff j).natDegree ≤ n := by
  by_cases hj : g.coeff j = 0
  · simp [hj]
  · exact (Nat.le_add_right _ _).trans (hg j hj)

/-- Reduction modulo a monic `Ψ` of weighted degree `w · deg_Y Ψ` preserves weighted degree. -/
theorem modByMonic {Ψ : R[X][Y]} (hΨ : Ψ.Monic) (hΨw : WeightedDegreeLE w (w * Ψ.natDegree) Ψ)
    (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (g %ₘ Ψ) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro j hj; exact absurd (Subsingleton.elim _ _) hj
  by_cases hΨ0 : Ψ.natDegree = 0
  · rw [eq_one_of_monic_natDegree_zero hΨ hΨ0, modByMonic_one]; exact zero
  induction hd : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ d ih =>
  by_cases hlt : g.natDegree < Ψ.natDegree
  · rwa [(modByMonic_eq_self_iff hΨ).mpr ((degree_le_natDegree).trans_lt
      (by rwa [degree_eq_natDegree hΨ.ne_zero, Nat.cast_lt]))]
  push Not at hlt
  have hg0 : g ≠ 0 := by rintro rfl; simp at hlt; omega
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hlcdeg : g.leadingCoeff.natDegree + w * g.natDegree ≤ n := hg _ hlc
  set a := g.natDegree - Ψ.natDegree
  have ha : a + Ψ.natDegree = g.natDegree := Nat.sub_add_cancel hlt
  set t := Polynomial.C g.leadingCoeff * X ^ a * Ψ
  have hlct : (Polynomial.C g.leadingCoeff * X ^ a).leadingCoeff * Ψ.leadingCoeff ≠ 0 := by
    rwa [leadingCoeff_C_mul_X_pow, hΨ.leadingCoeff, mul_one]
  have htdeg : t.natDegree = g.natDegree := by
    simp only [t]; rw [natDegree_mul' hlct, natDegree_C_mul_X_pow _ _ hlc, ha]
  have htlc : t.leadingCoeff = g.leadingCoeff := by
    simp only [t]; rw [leadingCoeff_mul' hlct, leadingCoeff_C_mul_X_pow, hΨ.leadingCoeff, mul_one]
  have ht : WeightedDegreeLE w n t := by
    have h1 : WeightedDegreeLE w (g.leadingCoeff.natDegree + w * a)
        (Polynomial.C g.leadingCoeff * X ^ a) := C_mul_X_pow le_rfl
    refine (h1.mul hΨw).mono ?_
    have : w * a + w * Ψ.natDegree = w * g.natDegree := by rw [← mul_add, ha]
    omega
  have hdvd : Ψ ∣ g - (g - t) := ⟨Polynomial.C g.leadingCoeff * X ^ a, by simp only [t]; ring⟩
  rw [modByMonic_eq_of_dvd_sub hΨ hdvd]
  by_cases hz : g - t = 0
  · rw [hz, zero_modByMonic]; exact zero
  have ht0 : t ≠ 0 := fun h => hlc (by rw [← htlc, h, leadingCoeff_zero])
  have hdeg : (g - t).natDegree < g.natDegree := by
    refine (natDegree_lt_iff_degree_lt hz).mpr ?_
    refine (degree_eq_natDegree hg0).symm ▸ degree_sub_lt ?_ hg0 htlc.symm
    rw [degree_eq_natDegree hg0, degree_eq_natDegree ht0, htdeg]
  exact ih _ (hd ▸ hdeg) (hg.sub ht) rfl

end WeightedDegreeLE

/-- The monomial `Xⁱ Yʲ` of `R[X][Y]`. -/
noncomputable def monomialXY (ij : ℕ × ℕ) : R[X][Y] := Polynomial.C (X ^ ij.1) * X ^ ij.2

/-- The coefficient of `Xⁱ Yʲ` in the monomial `monomialXY ij` is `1` if `ij = (i, j)` and `0`
otherwise. -/
theorem coeff_coeff_monomialXY (ij : ℕ × ℕ) (i j : ℕ) :
    ((monomialXY ij : R[X][Y]).coeff j).coeff i = if ij = (i, j) then 1 else 0 := by
  obtain ⟨i', j'⟩ := ij
  simp only [monomialXY, coeff_C_mul_X_pow, Prod.mk.injEq]
  by_cases hj : j = j'
  · subst hj; simp [coeff_X_pow, eq_comm]
  · simp [hj, Ne.symm hj]

/-- If `i + w j ≤ n`, then the monomial `Xⁱ Yʲ` has weighted degree at most `n`. -/
theorem WeightedDegreeLE.monomialXY {w n : ℕ} {ij : ℕ × ℕ} (h : ij.1 + w * ij.2 ≤ n) :
    WeightedDegreeLE w n (monomialXY ij : R[X][Y]) :=
  WeightedDegreeLE.C_mul_X_pow ((Nat.add_le_add_right (natDegree_X_pow_le _) _).trans h)

/-- Distinct monomials `Xⁱ Yʲ` are linearly independent. -/
theorem eq_zero_of_sum_smul_monomialXY_eq_zero {K : Type*} [Field K] {s : Finset (ℕ × ℕ)}
    {c : ℕ × ℕ → K} (h : ∑ ij ∈ s, c ij • (monomialXY ij : K[X][Y]) = 0) {ij : ℕ × ℕ}
    (hij : ij ∈ s) : c ij = 0 := by
  have := congrArg (fun g : K[X][Y] => (g.coeff ij.2).coeff ij.1) h
  simp only [finset_sum_coeff, coeff_smul, smul_eq_mul, coeff_coeff_monomialXY, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Polynomial.coeff_zero, Prod.mk.eta] at this
  simpa [hij] using this

/-- A polynomial of `Y`-degree `< m` whose coefficients all have degree `≤ N` lies in the span of
the monomials `Xⁱ Yʲ` with `i ≤ N` and `j < m`. -/
theorem mem_span_monomialXY_of_natDegree_lt {K : Type*} [Field K] [DecidableEq K[X][Y]]
    {g : K[X][Y]} {m N : ℕ} (hm : g.natDegree < m) (hN : ∀ j, (g.coeff j).natDegree ≤ N) :
    g ∈ Submodule.span K
      (((Finset.range (N + 1) ×ˢ Finset.range m).image (monomialXY (R := K)) :
        Finset K[X][Y]) : Set K[X][Y]) := by
  rw [as_sum_range' g m hm]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [← C_mul_X_pow_eq_monomial, as_sum_range' (g.coeff j) (N + 1) (Nat.lt_succ_of_le (hN j)),
    map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [← C_mul_X_pow_eq_monomial, map_mul, mul_assoc,
    show (Polynomial.C (Polynomial.C ((g.coeff j).coeff i)) : K[X][Y]) =
      algebraMap K K[X][Y] ((g.coeff j).coeff i) from rfl, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
  exact ⟨(i, j), ⟨hi, hj⟩, rfl⟩

end Polynomial.Bivariate

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.PlaneCurveIntersection
section





/-!
# Common zeros of two plane curves

Let `K` be a field and let `f, g ∈ K[X, Y]` with `f` irreducible and `f ∤ g`. Then `f` and `g`
have only finitely many common zeros in `K²`, and their number is bounded in terms of the degrees
of `f` and `g` alone. We prove the crude bound `2 D³` when every coefficient of `f` and `g`, viewed
as polynomials in `Y` over `K[X]`, has degree at most `D` and both have `Y`-degree at most `D`.
This is a weak form of Bézout's theorem: the `X`-coordinate of a common zero is a root of the
resultant `Res_Y(f, g)`, which is nonzero by Gauss's lemma, and above each such root the fibre of
`f` (or of `g`) is a nonzero polynomial of degree at most `D`.

## Main results

* `Polynomial.Bivariate.card_le_of_evalEval_eq_zero_of_not_dvd`: the bound for bivariate
  polynomials `K[X][Y]` and a finite set of common zeros.
* `MvPolynomial.ncard_zeroSet_inter_le_of_not_dvd`: the bound `2 d³` for `f, g ∈ K[X₀, X₁]` of
  total degree at most `d`.
-/


open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial

/-- The determinant of a square matrix of polynomials whose entries have degree at most `D`
has degree at most `D` times the size of the matrix. -/
theorem natDegree_det_le_card_mul {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R[X]) {D : ℕ} (h : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ Fintype.card n * D := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  have := Finset.sum_le_card_nsmul Finset.univ (fun i => (M (σ i) i).natDegree) D
    fun i _ => h _ _
  rwa [Finset.card_univ, smul_eq_mul] at this

/-- The resultant of two polynomials over `R[X]` whose coefficients have degree at most `D` has
degree at most `(m + n) D`. -/
theorem natDegree_resultant_le_add_mul {R : Type*} [CommRing R] (f g : R[X][Y]) (m n : ℕ)
    {D : ℕ} (hf : ∀ i, (f.coeff i).natDegree ≤ D) (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (resultant f g m n).natDegree ≤ (m + n) * D := by
  refine (natDegree_det_le_card_mul (D := D) _ fun i j => ?_).trans (by simp)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right] <;>
    split_ifs <;> simp [hf, hg]

end Polynomial

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- The fibre of a bivariate polynomial `h` over `x = a` vanishes identically if and only if
`X - a` divides `h`. -/
theorem map_evalRingHom_eq_zero_iff {h : K[X][Y]} {a : K} :
    h.map (evalRingHom a) = 0 ↔ C (X - C a) ∣ h := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  simp [dvd_iff_isRoot]

/-- If `f` is irreducible and `f ∤ g`, the fibres of `f` and `g` over a point never both vanish
identically. -/
theorem map_evalRingHom_ne_zero_or {f g : K[X][Y]} (hf : Irreducible f) (hfg : ¬ f ∣ g) (a : K) :
    f.map (evalRingHom a) ≠ 0 ∨ g.map (evalRingHom a) ≠ 0 := by
  by_contra! h
  rw [map_evalRingHom_eq_zero_iff, map_evalRingHom_eq_zero_iff] at h
  have hu : ¬ IsUnit (C (X - C a) : K[X][Y]) := mt isUnit_C.mp (not_isUnit_X_sub_C a)
  obtain ⟨u, hu'⟩ := (hf.dvd_iff.mp h.1).resolve_left hu
  exact hfg (Units.mul_right_dvd.mp (hu' ▸ h.2))

/-- A polynomial of degree at most `D` has at most `D` distinct roots. -/
private theorem card_roots_toFinset_le [DecidableEq K] (p : K[X]) {D : ℕ} (h : p.natDegree ≤ D) :
    p.roots.toFinset.card ≤ D :=
  (Multiset.toFinset_card_le _).trans ((card_roots' _).trans h)

/-- A finite set of points, each lying over a point of `A` and on the zero set of a nonzero
polynomial of degree at most `D` attached to that point, has at most `#A * D` elements. -/
theorem card_le_card_mul_of_fibres [DecidableEq K] (A : Finset K) (T : Finset (K × K))
    (h : K → K[X]) {D : ℕ} (hA : ∀ P ∈ T, P.1 ∈ A ∧ h P.1 ≠ 0 ∧ (h P.1).IsRoot P.2)
    (hD : ∀ a ∈ A, (h a).natDegree ≤ D) : T.card ≤ A.card * D := by
  classical
  have hT : T ⊆ A.biUnion fun a => {a} ×ˢ (h a).roots.toFinset := by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := hA P hP
    exact Finset.mem_biUnion.mpr ⟨P.1, h1, Finset.mem_product.mpr
      ⟨Finset.mem_singleton_self _, Multiset.mem_toFinset.mpr ((mem_roots h2).mpr h3)⟩⟩
  refine (Finset.card_le_card hT).trans (Finset.card_biUnion_le.trans ?_)
  rw [← smul_eq_mul]
  refine Finset.sum_le_card_nsmul A _ D fun a ha => ?_
  rw [Finset.card_product, Finset.card_singleton, one_mul]
  exact card_roots_toFinset_le _ (hD a ha)

end Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- If `f` is irreducible of positive `Y`-degree and `f ∤ g`, the resultant `Res_Y(f, g)` is
nonzero. -/
theorem resultant_ne_zero_of_irreducible_of_not_dvd {f g : K[X][Y]} (hf : Irreducible f)
    (hpos : f.natDegree ≠ 0) (hfg : ¬ f ∣ g) : resultant f g ≠ 0 := by
  let L := FractionRing K[X]
  have hinj : Function.Injective (algebraMap K[X] L) := IsFractionRing.injective _ _
  have hprim : f.IsPrimitive := hf.isPrimitive hpos
  have hfL : Irreducible (f.map (algebraMap K[X] L)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hf
  have hcop : IsCoprime (f.map (algebraMap K[X] L)) (g.map (algebraMap K[X] L)) :=
    (Irreducible.coprime_iff_not_dvd hfL).mpr
      (hfg ∘ (hprim.dvd_iff_fraction_map_dvd_fraction_map L).mpr)
  have hres := mt resultant_eq_zero_iff.mp (fun h => h.2 hcop)
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hres
  exact fun h => hres (by rw [h, map_zero])

/-- **A weak Bézout bound.** Let `f, g ∈ K[X][Y]` with `f` irreducible and `f ∤ g`, and suppose
that `f` and `g` have `Y`-degree at most `D` and coefficients of degree at most `D`. Then any
finite set of common zeros of `f` and `g` in `K²` has at most `2 D³` elements. -/
theorem card_le_of_evalEval_eq_zero_of_not_dvd [DecidableEq K] {f g : K[X][Y]}
    (hf : Irreducible f) (hfg : ¬ f ∣ g) {D : ℕ} (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D) (hfn : f.natDegree ≤ D) (hgn : g.natDegree ≤ D)
    (T : Finset (K × K)) (hT : ∀ P ∈ T, f.evalEval P.1 P.2 = 0 ∧ g.evalEval P.1 P.2 = 0) :
    T.card ≤ 2 * D ^ 3 := by
  by_cases h0 : f.natDegree = 0
  · obtain ⟨p, rfl⟩ : ∃ p, f = C p := ⟨_, eq_C_of_natDegree_eq_zero h0⟩
    have hp0 : p ≠ 0 := C_ne_zero.mp hf.ne_zero
    refine (card_le_card_mul_of_fibres p.roots.toFinset T (fun a => g.map (evalRingHom a))
      (D := D) (fun P hP => ?_) (fun a _ => natDegree_map_le.trans hgn)).trans ?_
    · have h1 : p.eval P.1 = 0 := by simpa [evalEval_C] using (hT P hP).1
      refine ⟨Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr h1),
        (map_evalRingHom_ne_zero_or hf hfg P.1).resolve_left (not_not.mpr (by simp [h1])), ?_⟩
      simpa [IsRoot, map_evalRingHom_eval] using (hT P hP).2
    · have hp : p.natDegree ≤ D := by simpa using hfD 0
      calc p.roots.toFinset.card * D ≤ D * D :=
            Nat.mul_le_mul_right _ (card_roots_toFinset_le _ hp)
        _ ≤ 2 * D ^ 3 := by
            rcases Nat.eq_zero_or_pos D with rfl | hD
            · simp
            · nlinarith [Nat.one_le_pow 1 D hD]
  · have hr := resultant_ne_zero_of_irreducible_of_not_dvd hf h0 hfg
    obtain ⟨u, v, -, -, huv⟩ :=
      exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl h0)
    refine (card_le_card_mul_of_fibres (resultant f g).roots.toFinset T
      (fun a => f.map (evalRingHom a)) (D := D) (fun P hP => ?_)
      (fun a _ => natDegree_map_le.trans hfn)).trans ?_
    · have h1 : (resultant f g).eval P.1 = 0 := by
        simpa [evalEval_add, evalEval_mul, evalEval_C, (hT P hP).1, (hT P hP).2] using
          (congrArg (evalEval P.1 P.2) huv).symm
      refine ⟨Multiset.mem_toFinset.mpr ((mem_roots hr).mpr h1), fun hz => ?_, ?_⟩
      · obtain ⟨w, hw⟩ := (map_evalRingHom_eq_zero_iff).mp hz
        have hw0 : w ≠ 0 := by rintro rfl; exact hf.ne_zero (by simpa using hw)
        apply h0
        rw [hw, natDegree_mul (C_ne_zero.mpr (X_sub_C_ne_zero _)) hw0, natDegree_C, zero_add]
        exact natDegree_eq_zero_of_isUnit
          ((hf.isUnit_or_isUnit hw).resolve_left (mt isUnit_C.mp (not_isUnit_X_sub_C _)))
      · simpa [IsRoot, map_evalRingHom_eval] using (hT P hP).1
    · have hdeg : (resultant f g).natDegree ≤ (D + D) * D :=
        (natDegree_resultant_le_add_mul f g _ _ hfD hgD).trans
          (Nat.mul_le_mul_right _ (Nat.add_le_add hfn hgn))
      calc (resultant f g).roots.toFinset.card * D ≤ (D + D) * D * D :=
            Nat.mul_le_mul_right _ (card_roots_toFinset_le _ hdeg)
        _ = 2 * D ^ 3 := by ring

end Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- Evaluating `equivMvPolynomial R f` at `p` is evaluating `f` at `(p 0, p 1)`. -/
theorem eval_equivMvPolynomial (f : R[X][Y]) (p : Fin 2 → R) :
    MvPolynomial.eval p (equivMvPolynomial R f) = f.evalEval (p 0) (p 1) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg, evalEval_add]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp [map_add, evalEval_add, ha, hb]
    | monomial m c =>
      simp [equivMvPolynomial, ← C_mul_X_pow_eq_monomial, evalEval_mul, evalEval_pow,
        evalEval_X, evalEval_C]

/-- The coefficient of `X₀ⁱ X₁ʲ` in `equivMvPolynomial R f` is the coefficient of `Xⁱ` in the
coefficient of `Yʲ` in `f`. -/
theorem coeff_equivMvPolynomial (f : R[X][Y]) (i j : ℕ) :
    MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 j) (equivMvPolynomial R f) =
      (f.coeff j).coeff i := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp [map_add, ha, hb]
    | monomial m c =>
      have hmon : equivMvPolynomial R (monomial n (monomial m c)) =
          MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n) c := by
        simp [equivMvPolynomial, ← C_mul_X_pow_eq_monomial, MvPolynomial.monomial_eq, mul_assoc]
      rw [hmon, MvPolynomial.coeff_monomial, coeff_monomial]
      by_cases hn : n = j
      · subst hn
        rw [if_pos rfl, coeff_monomial]
        by_cases hm : m = i
        · simp [hm]
        · rw [if_neg, if_neg hm]
          intro h
          exact hm (by simpa using congrArg (· 0) h)
      · rw [if_neg hn, coeff_zero, if_neg]
        intro h
        exact hn (by simpa using congrArg (· 1) h)

/-- The coefficients of `f`, and its `Y`-degree, are bounded by the total degree of the
corresponding polynomial in two variables. -/
theorem natDegree_coeff_add_le_totalDegree (f : R[X][Y]) (j : ℕ) (hj : f.coeff j ≠ 0) :
    (f.coeff j).natDegree + j ≤ (equivMvPolynomial R f).totalDegree := by
  have h := coeff_equivMvPolynomial f (f.coeff j).natDegree j
  rw [coeff_natDegree] at h
  have hne : MvPolynomial.coeff (Finsupp.single 0 (f.coeff j).natDegree + Finsupp.single 1 j)
      (equivMvPolynomial R f) ≠ 0 := by
    rw [h]
    exact leadingCoeff_ne_zero.mpr hj
  simpa [Finsupp.sum_add_index, Finsupp.sum_single_index] using
    MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)

/-- The degree of each coefficient of `f` is at most the total degree of the corresponding
polynomial in two variables. -/
theorem natDegree_coeff_le_totalDegree (f : R[X][Y]) (j : ℕ) :
    (f.coeff j).natDegree ≤ (equivMvPolynomial R f).totalDegree := by
  by_cases hj : f.coeff j = 0
  · simp [hj]
  · exact (Nat.le_add_right _ _).trans (natDegree_coeff_add_le_totalDegree f j hj)

/-- The `Y`-degree of `f` is at most the total degree of the corresponding polynomial in two
variables. -/
theorem natDegree_le_totalDegree (f : R[X][Y]) :
    f.natDegree ≤ (equivMvPolynomial R f).totalDegree := by
  by_cases hf : f = 0
  · simp [hf]
  · exact (Nat.le_add_left _ _).trans
      (natDegree_coeff_add_le_totalDegree f _ (leadingCoeff_ne_zero.mpr hf))

end Polynomial.Bivariate

namespace MvPolynomial

open Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- **A weak Bézout bound.** If `f, g ∈ K[X₀, X₁]` have total degree at most `d`, `f` is
irreducible and `f ∤ g`, then `f` and `g` have finitely many common zeros in `K²`, at most
`2 d³` of them. -/
theorem finite_zeroSet_inter_of_not_dvd {f g : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hfg : ¬ f ∣ g) {d : ℕ} (hdf : f.totalDegree ≤ d) (hdg : g.totalDegree ≤ d) :
    {p : Fin 2 → K | eval p f = 0 ∧ eval p g = 0}.Finite ∧
      {p : Fin 2 → K | eval p f = 0 ∧ eval p g = 0}.ncard ≤ 2 * d ^ 3 := by
  classical
  set e := equivMvPolynomial K
  set Z := {p : Fin 2 → K | eval p f = 0 ∧ eval p g = 0}
  have key : ∀ T : Finset (Fin 2 → K), ↑T ⊆ Z → T.card ≤ 2 * d ^ 3 := by
    intro T hT
    have hf' : Irreducible (e.symm f) := (MulEquiv.irreducible_iff e.symm.toMulEquiv).mpr hf
    have hfg' : ¬ e.symm f ∣ e.symm g := fun h => hfg (by simpa using map_dvd e h)
    have hdf' : (e (e.symm f)).totalDegree ≤ d := by simpa using hdf
    have hdg' : (e (e.symm g)).totalDegree ≤ d := by simpa using hdg
    have hinj : Function.Injective fun p : Fin 2 → K => (p 0, p 1) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rw [← Finset.card_image_of_injective T hinj]
    refine card_le_of_evalEval_eq_zero_of_not_dvd hf' hfg'
      (fun i => (natDegree_coeff_le_totalDegree _ i).trans hdf')
      (fun i => (natDegree_coeff_le_totalDegree _ i).trans hdg')
      ((natDegree_le_totalDegree _).trans hdf') ((natDegree_le_totalDegree _).trans hdg') _ ?_
    simp only [Finset.mem_image]
    rintro _ ⟨p, hp, rfl⟩
    have := hT hp
    simp only [Set.mem_setOf_eq, Z] at this
    rw [← eval_equivMvPolynomial, ← eval_equivMvPolynomial]
    simpa [e] using this
  have hfin : Z.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * d ^ 3 + 1)
    have := key T hT
    omega
  refine ⟨hfin, ?_⟩
  rw [← hfin.coe_toFinset, Set.ncard_coe_finset]
  exact key _ (by simp)

end MvPolynomial

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.MonicNormalization
section









/-!
# Normalizing an absolutely irreducible plane curve to be monic and separable in `Y`

Let `F` be a finite field and let `f ∈ F[x, y]` be irreducible over an algebraic closure of `F`,
of total degree `d`. If `F` has more than `d + 1` elements there is a shear
`(x, y) ↦ (x + a y, y)` of the plane after which `f`, rescaled by a constant, becomes a polynomial
`g ∈ F[X][Y]` which is monic of degree `d` in `Y`, has weighted degree at most `d` for the weights
`1, 1`, has nonzero `Y`-derivative, is still irreducible over the algebraic closure, and has as
many zeros in `F²` as `f`.

The leading coefficient of the sheared polynomial in `Y` is `f_d(a, 1)`, where `f_d` is the top
homogeneous component of `f`; it vanishes for at most `d` values of `a`. Its `Y`-derivative is the
shear of `a ∂f/∂x + ∂f/∂y`, which vanishes for at most one value of `a`: the two partial
derivatives cannot both vanish, since otherwise `f` would be a `p`-th power.

## Main definitions

* `MvPolynomial.shear`: the automorphism `(x, y) ↦ (x + a y, y)` of `R[x, y]`.

## Main results

* `MvPolynomial.exists_pow_eq_of_forall_pderiv_eq_zero`: over a perfect ring of characteristic
  `p`, a polynomial all of whose partial derivatives vanish is a `p`-th power.
* `MvPolynomial.irreducible_of_irreducible_map`: a polynomial over a field which is irreducible
  over an extension field is irreducible.
* `MvPolynomial.exists_monic_normalization`: the normalization.
-/


open Polynomial
open scoped Polynomial.Bivariate

namespace MvPolynomial

section PthPower

variable {σ R : Type*} [CommRing R] [NoZeroDivisors R] (p : ℕ) [CharP R p]

/-- In characteristic `p`, if every partial derivative of `f` vanishes then every exponent of
every monomial of `f` is divisible by `p`. -/
theorem dvd_of_forall_pderiv_eq_zero {f : MvPolynomial σ R} (h : ∀ i, pderiv i f = 0)
    {m : σ →₀ ℕ} (hm : m ∈ f.support) (i : σ) : p ∣ m i := by
  classical
  by_contra hp
  have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr fun h0 => hp (h0 ▸ dvd_zero p)
  have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr hmi
  have hc := coeff_pderiv (i := i) f (m - Finsupp.single i 1)
  rw [h i, coeff_zero, tsub_add_cancel_of_le hle, Finsupp.tsub_apply, Finsupp.single_eq_same,
    eq_comm, mul_eq_zero] at hc
  rcases hc with hc | hc
  · exact (mem_support_iff.mp hm) hc
  · rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hmi,
      CharP.cast_eq_zero_iff R p] at hc
    exact hp hc

/-- Over a perfect ring of characteristic `p`, a polynomial all of whose partial derivatives
vanish is a `p`-th power. -/
theorem exists_pow_eq_of_forall_pderiv_eq_zero [Fact p.Prime] [PerfectRing R p]
    {f : MvPolynomial σ R} (h : ∀ i, pderiv i f = 0) : ∃ g : MvPolynomial σ R, g ^ p = f := by
  classical
  set g' : MvPolynomial σ R := ∑ m ∈ f.support,
    monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) m) (coeff m f)
  have hg' : expand p g' = f := by
    conv_rhs => rw [← support_sum_monomial_coeff f]
    simp only [g', map_sum, expand_monomial]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) m = m := by
      ext i
      simp [Nat.mul_div_cancel' (dvd_of_forall_pderiv_eq_zero p h hm i)]
    rw [hm']
  refine ⟨map ((frobeniusEquiv R p).symm : R →+* R) g', ?_⟩
  have : (frobenius R p).comp ((frobeniusEquiv R p).symm : R →+* R) = RingHom.id R := by
    ext x; exact frobenius_apply_frobeniusEquiv_symm R p x
  rw [← map_frobenius_expand p, ← map_expand, map_map, this, map_id, hg']

end PthPower

section Shear

variable {R : Type*} [CommRing R]

/-- The shear `(x, y) ↦ (x + a y, y)` of the plane, as an automorphism of `R[x, y]`. -/
noncomputable def shear (a : R) : MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (aeval ![X 0 + C a * X 1, X 1]) (aeval ![X 0 - C a * X 1, X 1])
    (by ext i : 1; fin_cases i <;> simp) (by ext i : 1; fin_cases i <;> simp)

/-- The shear substitutes `x + a y` for `x` and `y` for `y`. -/
theorem shear_apply (a : R) (f : MvPolynomial (Fin 2) R) :
    shear a f = aeval ![X 0 + C a * X 1, X 1] f := rfl

/-- Evaluating a sheared polynomial at `(x₀, x₁)` is evaluating the original polynomial at
`(x₀ + a x₁, x₁)`. -/
theorem eval_shear (a : R) (f : MvPolynomial (Fin 2) R) (x : Fin 2 → R) :
    eval x (shear a f) = eval ![x 0 + a * x 1, x 1] f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [shear_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, hp]; fin_cases n <;> simp [shear_apply]

/-- The shear commutes with mapping the coefficients along a ring homomorphism `φ`. -/
theorem map_shear {S : Type*} [CommRing S] (φ : R →+* S) (a : R) (f : MvPolynomial (Fin 2) R) :
    map φ (shear a f) = shear (φ a) (map φ f) := by
  rw [shear_apply, shear_apply, aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
  apply congrArg (fun s : Fin 2 → MvPolynomial (Fin 2) S => bind₁ s (map φ f))
  funext i
  fin_cases i <;> simp

/-- The chain rule for the shear: `∂/∂y (f (x + a y, y)) = (a ∂f/∂x + ∂f/∂y) (x + a y, y)`. -/
theorem pderiv_one_shear (a : R) (f : MvPolynomial (Fin 2) R) :
    pderiv 1 (shear a f) = shear a (C a * pderiv 0 f + pderiv 1 f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [shear_apply]
  | add p q hp hq => simp only [map_add, mul_add, hp, hq]; abel
  | mul_X p n hp =>
    rw [map_mul, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul]
    fin_cases n <;> simp [shear_apply] <;> ring

/-- The shear is a linear change of variables, so it preserves homogeneity of every degree. -/
theorem isHomogeneous_shear (a : R) {f : MvPolynomial (Fin 2) R} {n : ℕ}
    (hf : f.IsHomogeneous n) : (shear a f).IsHomogeneous n := by
  have h := hf.aeval (![X 0 + C a * X 1, X 1] : Fin 2 → MvPolynomial (Fin 2) R) (n := 1) fun i => by
    fin_cases i
    · simpa using (isHomogeneous_X R 0).add ((isHomogeneous_C _ a).mul (isHomogeneous_X R 1))
    · simpa using isHomogeneous_X R 1
  rw [shear_apply]
  simpa [one_mul] using h

/-- The shear does not increase the total degree: it sends each homogeneous component of `f` to a
homogeneous polynomial of the same degree. -/
theorem totalDegree_shear_le (a : R) (f : MvPolynomial (Fin 2) R) :
    (shear a f).totalDegree ≤ f.totalDegree := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => ?_)
  exact (isHomogeneous_shear a (homogeneousComponent_isHomogeneous i f)).totalDegree_le.trans
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- The dehomogenization `G(t, 1)` of `G`, evaluated at `a`, is `G(a, 1)`. -/
theorem eval_aeval_X_one (a : R) (G : MvPolynomial (Fin 2) R) :
    (aeval ![Polynomial.X, 1] G).eval a = eval ![a, 1] G := by
  rw [← Polynomial.coe_aeval_eq_eval, comp_aeval_apply,
    show (fun i => Polynomial.aeval a (![Polynomial.X, 1] i)) = ![a, 1] from by
      funext i; fin_cases i <;> simp]
  rfl

/-- The coefficient of `y ^ d` in a homogeneous polynomial of degree `d` in `x, y` is its value
at `(0, 1)`. -/
theorem IsHomogeneous.coeff_single_one_eq_eval {G : MvPolynomial (Fin 2) R} {d : ℕ}
    (hG : G.IsHomogeneous d) : coeff (Finsupp.single 1 d) G = eval ![0, 1] G := by
  conv_lhs => rw [← Polynomial.homogenize_eq_of_isHomogeneous hG rfl]
  rw [Polynomial.coeff_homogenize]
  simp only [Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), Finsupp.single_eq_same,
    zero_add, if_true, Polynomial.coeff_zero_eq_eval_zero, eval_aeval_X_one]

/-- The coefficient of `y ^ d` after the shear is the top homogeneous component evaluated at
`(a, 1)`. -/
theorem coeff_single_one_shear (a : R) (f : MvPolynomial (Fin 2) R) (d : ℕ) :
    coeff (Finsupp.single 1 d) (shear a f) = eval ![a, 1] (homogeneousComponent d f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, coeff_sum, Finset.sum_eq_single d]
  · rw [(isHomogeneous_shear a (homogeneousComponent_isHomogeneous d f)).coeff_single_one_eq_eval,
      eval_shear]
    simp
  · intro i _ hid
    refine (isHomogeneous_shear a (homogeneousComponent_isHomogeneous i f)).coeff_eq_zero ?_
    simpa using Ne.symm hid
  · intro hd'
    rw [homogeneousComponent_eq_zero d f (by simpa [Nat.lt_succ_iff] using hd'), map_zero,
      coeff_zero]

end Shear

end MvPolynomial

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- `equivMvPolynomial` commutes with change of coefficients. -/
theorem equivMvPolynomial_map {S : Type*} [CommRing S] (φ : R →+* S) (q : R[X][Y]) :
    equivMvPolynomial S (q.map (mapRingHom φ)) =
      MvPolynomial.map φ (equivMvPolynomial R q) := by
  ext m
  obtain ⟨i, j, rfl⟩ : ∃ i j, m = Finsupp.single 0 i + Finsupp.single 1 j :=
    ⟨m 0, m 1, by ext k; fin_cases k <;> simp⟩
  rw [coeff_equivMvPolynomial, MvPolynomial.coeff_map, coeff_equivMvPolynomial]
  simp [Polynomial.coeff_map]

end Polynomial.Bivariate

namespace MvPolynomial

open Polynomial.Bivariate

/-- A polynomial over a field which is irreducible over an extension is irreducible. -/
theorem irreducible_of_irreducible_map {σ K L : Type*} [Field K] [Field L] (φ : K →+* L)
    {f : MvPolynomial σ K} (hf : Irreducible (map φ f)) : Irreducible f := by
  classical
  have hunit : ∀ u : MvPolynomial σ K, IsUnit (map φ u) → IsUnit u := by
    intro u hu
    obtain ⟨c, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    have hu' : u = C (coeff 0 u) := by
      ext m
      by_cases hm : m = 0
      · simp [hm]
      · rw [coeff_C, if_neg (Ne.symm hm)]
        have := congrArg (coeff m) hc.2
        rw [coeff_map, coeff_C, if_neg (Ne.symm hm)] at this
        exact (map_eq_zero φ).mp this
    have h0 := congrArg (coeff 0) hc.2
    rw [coeff_map, coeff_C, if_pos rfl] at h0
    rw [hu']
    refine (isUnit_iff_ne_zero.mpr fun h => ?_).map C
    rw [h, map_zero] at h0
    exact hc.1.ne_zero h0.symm
  refine ⟨fun h => hf.not_isUnit (h.map (map φ)), fun a b hab => ?_⟩
  rw [hab, map_mul] at hf
  exact (hf.isUnit_or_isUnit rfl).imp (hunit a) (hunit b)

/-- **Normalization of an absolutely irreducible plane curve.** Let `F` be a finite field and
let `f ∈ F[x, y]` be irreducible over an algebraic closure of `F`, with `deg f + 1 < #F`. Then
after a shear `(x, y) ↦ (x + a y, y)` and a rescaling, `f` becomes `g ∈ F[X][Y]`, monic in `Y`
of degree `deg f > 0`, of weighted degree at most `deg f` for the weights `1, 1`, with nonzero
`Y`-derivative, still irreducible over the algebraic closure, and with as many zeros in `F²`. -/
theorem exists_monic_normalization {F : Type*} [Field F] [Fintype F]
    (f : MvPolynomial (Fin 2) F)
    (hf : Irreducible (f.map (algebraMap F (AlgebraicClosure F))))
    (hq : f.totalDegree + 1 < Fintype.card F) :
    ∃ g : F[X][X], g.Monic ∧ 0 < g.natDegree ∧ g.natDegree = f.totalDegree ∧
      Polynomial.Bivariate.WeightedDegreeLE 1 g.natDegree g ∧ derivative g ≠ 0 ∧
      Irreducible (g.map (mapRingHom (algebraMap F (AlgebraicClosure F)))) ∧
      {p : Fin 2 → F | MvPolynomial.eval p f = 0}.ncard =
        {P : F × F | g.evalEval P.1 P.2 = 0}.ncard := by
  classical
  set φ := algebraMap F (AlgebraicClosure F)
  -- The two partial derivatives of `f` do not both vanish: otherwise `f` is a `p`-th power.
  have hpd : pderiv 0 f ≠ 0 ∨ pderiv 1 f ≠ 0 := by
    by_contra! h
    obtain ⟨p, _⟩ := CharP.exists F
    have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
    obtain ⟨g, hg⟩ := exists_pow_eq_of_forall_pderiv_eq_zero p (f := f)
      (fun i => by fin_cases i; exacts [h.1, h.2])
    rw [← hg, map_pow] at hf
    exact not_irreducible_pow (Fact.out : p.Prime).ne_one hf
  -- Hence `a ∂f/∂x + ∂f/∂y ≠ 0` for all but at most one `a`.
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : F, ∀ a, a ≠ a₀ → C a * pderiv 0 f + pderiv 1 f ≠ 0 := by
    by_cases hex : ∃ a₀ : F, C a₀ * pderiv 0 f + pderiv 1 f = 0
    · obtain ⟨a₀, h₀⟩ := hex
      refine ⟨a₀, fun a ha h => ?_⟩
      have h₁ : C (a - a₀) * pderiv 0 f = 0 := by
        rw [C_sub]; linear_combination h - h₀
      rcases mul_eq_zero.mp h₁ with h₂ | h₂
      · exact ha (sub_eq_zero.mp (C_eq_zero.mp h₂))
      · rw [h₂, mul_zero, zero_add] at h₀
        exact hpd.elim (· h₂) (· h₀)
    · exact ⟨0, fun a _ h => hex ⟨a, h⟩⟩
  set d := f.totalDegree with hd
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by rw [h, map_zero])
  -- `f` is not constant.
  have hd0 : d ≠ 0 := by
    intro h0
    rw [totalDegree_eq_zero_iff_eq_C.mp h0, map_C] at hf
    by_cases hb : φ (coeff 0 f) = 0
    · exact hf.ne_zero (by rw [hb, map_zero])
    · exact hf.not_isUnit ((isUnit_iff_ne_zero.mpr hb).map C)
  -- The top homogeneous component `H` of `f`, and its dehomogenization `P(t) = H(t, 1)`.
  set H := homogeneousComponent d f
  have hH : H.IsHomogeneous d := homogeneousComponent_isHomogeneous d f
  have hH0 : H ≠ 0 := by
    obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf0)
      fun s => s.sum fun _ e => e
    intro h
    have := congrArg (coeff m) h
    rw [coeff_homogeneousComponent, if_pos (show m.degree = d from hmd.symm),
      coeff_zero] at this
    exact mem_support_iff.mp hm this
  set P : Polynomial F := aeval ![Polynomial.X, 1] H
  have hP0 : P ≠ 0 := fun h => hH0 <| by
    rw [← Polynomial.homogenize_eq_of_isHomogeneous hH h, Polynomial.homogenize_zero]
  have hPd : P.natDegree ≤ d :=
    (aeval_natDegree_le (n := 1) H hH.totalDegree_le _ fun i => by fin_cases i <;> simp).trans
      (by rw [mul_one])
  -- Choose `a` with `P(a) ≠ 0` and `a ≠ a₀`.
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert a₀ P.roots.toFinset) (t := Finset.univ) <| by
      rw [Finset.card_univ]
      refine lt_of_le_of_lt ((Finset.card_insert_le _ _).trans ?_) hq
      exact Nat.add_le_add_right ((Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' P).trans hPd)) 1
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot.def, eval_aeval_X_one] at ha
  obtain ⟨haa₀, hc⟩ := ha
  set c := eval ![a, 1] H
  -- The sheared polynomial, as a polynomial in `Y` over `F[X]`.
  set f' := shear a f
  set E := equivMvPolynomial F
  set g' : F[X][X] := E.symm f'
  have hEg' : E g' = f' := E.apply_symm_apply f'
  have htd : (E g').totalDegree ≤ d := hEg' ▸ totalDegree_shear_le a f
  have hcoeff : ∀ j, g'.coeff j ≠ 0 → (g'.coeff j).natDegree + j ≤ d := fun j hj =>
    (natDegree_coeff_add_le_totalDegree g' j hj).trans htd
  have hlead : g'.coeff d = Polynomial.C c := by
    ext i
    rw [← coeff_equivMvPolynomial g' i d, Polynomial.coeff_C]
    split_ifs with hi
    · rw [hi, Finsupp.single_zero, zero_add, hEg', coeff_single_one_shear]
    · by_contra hne
      have := (le_totalDegree (mem_support_iff.mpr hne)).trans htd
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_single_index rfl] at this
      omega
  have hnat' : g'.natDegree = d := by
    exact le_antisymm ((natDegree_le_totalDegree g').trans htd)
      (le_natDegree_of_ne_zero (by rw [hlead]; exact Polynomial.C_ne_zero.mpr hc))
  have hder' : derivative g' ≠ 0 := by
    intro h
    have := pderiv_one_equivMvPolynomial g'
    rw [h, map_zero, hEg', pderiv_one_shear] at this
    exact ha₀ a haa₀ ((shear a).injective (this.trans (map_zero _).symm))
  -- Rescale to make it monic.
  have hu : (Polynomial.C c⁻¹ : F[X]) ≠ 0 := Polynomial.C_ne_zero.mpr (inv_ne_zero hc)
  set g : F[X][X] := Polynomial.C (Polynomial.C c⁻¹) * g'
  have hnat : g.natDegree = d := by rw [Polynomial.natDegree_C_mul hu, hnat']
  have hEg : E g = C c⁻¹ * f' := by
    rw [map_mul, hEg', equivMvPolynomial_C_C]
  have hev : ∀ x y : F, g.evalEval x y = c⁻¹ * eval ![x + a * y, y] f := by
    intro x y
    have := eval_equivMvPolynomial g ![x, y]
    rw [hEg, map_mul, eval_C, eval_shear] at this
    simpa using this.symm
  refine ⟨g, ?_, by omega, hnat, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, Polynomial.coeff_C_mul, hlead,
      ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]
  · intro j hj
    rw [Polynomial.coeff_C_mul] at hj ⊢
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hc), hnat, one_mul]
    exact hcoeff j (right_ne_zero_of_mul hj)
  · rw [Polynomial.derivative_C_mul]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hu) hder'
  · have hmap : equivMvPolynomial (AlgebraicClosure F) (g.map (mapRingHom φ)) =
        C (φ c⁻¹) * shear (φ a) (map φ f) := by
      rw [equivMvPolynomial_map, hEg, map_mul, map_C, map_shear]
    rw [← (equivMvPolynomial (AlgebraicClosure F)).symm_apply_apply (g.map (mapRingHom φ)), hmap,
      MulEquiv.irreducible_iff, irreducible_isUnit_mul
        ((isUnit_iff_ne_zero.mpr ((map_ne_zero φ).mpr (inv_ne_zero hc))).map C),
      MulEquiv.irreducible_iff]
    exact hf
  · have hinj : Function.Injective fun P : F × F => ![P.1 + a * P.2, P.2] := by
      intro P Q h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      exact Prod.ext (by simpa [h1] using h0) h1
    have hset : {p : Fin 2 → F | eval p f = 0} =
        (fun P : F × F => ![P.1 + a * P.2, P.2]) '' {P : F × F | g.evalEval P.1 P.2 = 0} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_image, hev, mul_eq_zero, inv_eq_zero, hc, false_or]
      have hp : ![p 0, p 1] = p := by ext i; fin_cases i <;> rfl
      constructor
      · intro h
        exact ⟨(p 0 - a * p 1, p 1), by simpa [hp] using h, by simpa using hp⟩
      · rintro ⟨P, hP, rfl⟩
        exact hP
    rw [hset, Set.ncard_image_of_injective _ hinj]

end MvPolynomial

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.GaloisResolvent
section







/-!
# The Galois resolvent of a polynomial

Let `f ∈ A[X]` have roots `b₁, …, bₘ` (after some ring map `A → B`) and let `c ∈ Aᵐ`. For a
permutation `π` of the roots put `t(π) = ∑ᵢ cᵢ b_{π i}`. The **Galois resolvent**
`Φ(T) = ∏_π (T - t(π))`, its **discriminant** `Δ = ∏_{π ≠ π'} (t(π) - t(π'))` and the
**Lagrange-type polynomials** `R_τ` with `R_τ(t(π)) = Δ · t(π τ)` have coefficients which are
polynomials in the coefficients of `f` and in `c`: they are symmetric in the roots, so the
fundamental theorem of symmetric polynomials writes them in the elementary symmetric functions of
the roots, which are the signed coefficients of `f`.

They are built here as universal polynomials over `ℤ[γ₁, …, γₘ][u₁, …, uₘ]` and specialized.

## Main definitions

* `Polynomial.galoisResolvent`, `Polynomial.resolventDisc`, `Polynomial.resolventPerm`.
* `Polynomial.twistedComp`: the composite `Δ^{deg Ψ} Ψ^{fr}(R / Δ)`, without denominators.

## Main results

* `Polynomial.galoisResolvent_spec`: the three defining properties after a map splitting `f`.
* `Polynomial.galoisResolvent_monic`.
* `Polynomial.exists_natDegree_resolvent_le`: uniform degree bounds over `R[X]` for linear forms
  with constant coefficients.
* `Polynomial.exists_resolventDisc_ne_zero`: for separable monic `f` over a domain the
  discriminant does not vanish at some `c` with coordinates in any large enough finite set.
-/


open Polynomial Finset Nat

noncomputable section

namespace Polynomial

namespace GaloisResolvent

variable (m : ℕ)

/-- The ring `ℤ[γ₁, …, γₘ]` of the universal coefficients of the linear form. -/
abbrev CoeffRing := MvPolynomial (Fin m) ℤ

/-- The ring `ℤ[γ][u₁, …, uₘ]` of the universal roots. -/
abbrev RootRing := MvPolynomial (Fin m) (CoeffRing m)

/-- The universal value of the linear form `∑ γᵢ u_{π i}`. -/
def t (π : Equiv.Perm (Fin m)) : RootRing m :=
  ∑ i, MvPolynomial.C (MvPolynomial.X i) * MvPolynomial.X (π i)

/-- Permuting the universal roots by `e` sends `t(π)` to `t(e π)`. -/
theorem rename_t (e π : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (t m π) = t m (e * π) := by
  simp [t, map_sum, Equiv.Perm.mul_apply]

/-- The universal resolvent `∏_π (T - t(π))`. -/
def Φ : (RootRing m)[X] := ∏ π : Equiv.Perm (Fin m), (X - C (t m π))

/-- The universal discriminant `∏_{π ≠ π'} (t(π) - t(π'))`. -/
def Δ : RootRing m := ∏ π : Equiv.Perm (Fin m), ∏ π' ∈ univ.erase π, (t m π - t m π')

/-- The universal Lagrange-type polynomial with `R_τ(t(π)) = Δ · t(π τ)`. -/
def R (τ : Equiv.Perm (Fin m)) : (RootRing m)[X] :=
  ∑ π : Equiv.Perm (Fin m), C (t m (π * τ) * ∏ ρ ∈ univ.erase π, ∏ ρ' ∈ univ.erase ρ,
    (t m ρ - t m ρ')) * ∏ π' ∈ univ.erase π, (X - C (t m π'))

/-- Reindexing by left multiplication by `e`: the product of `F` over the permutations other than
`e π` equals the product of `F (e ρ)` over the permutations `ρ` other than `π`. -/
theorem prod_erase_mul_left {M : Type*} [CommMonoid M] (e π : Equiv.Perm (Fin m))
    (F : Equiv.Perm (Fin m) → M) :
    ∏ ρ ∈ univ.erase (e * π), F ρ = ∏ ρ ∈ univ.erase π, F (e * ρ) := by
  refine Finset.prod_nbij' (e⁻¹ * ·) (e * ·) ?_ ?_ ?_ ?_ ?_ <;> intro x hx
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hx ⊢
    exact fun h => hx (by rw [← h]; group)
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hx ⊢
    exact fun h => hx (mul_left_cancel h)
  · simp
  · simp
  · simp

/-- The universal discriminant with the factor of index `π` removed. -/
def discOff (π : Equiv.Perm (Fin m)) : RootRing m :=
  ∏ ρ ∈ univ.erase π, ∏ ρ' ∈ univ.erase ρ, (t m ρ - t m ρ')

/-- The Lagrange basis numerator `∏_{π' ≠ π} (T - t(π'))`. -/
def lagNum (π : Equiv.Perm (Fin m)) : (RootRing m)[X] :=
  ∏ π' ∈ univ.erase π, (X - C (t m π'))

/-- Permuting the universal roots by `e` sends `discOff m π` to `discOff m (e * π)`. -/
theorem rename_discOff (e π : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (discOff m π) = discOff m (e * π) := by
  simp only [discOff, map_prod, map_sub, rename_t]
  rw [prod_erase_mul_left]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [prod_erase_mul_left]

/-- Permuting the universal roots by `e` sends `lagNum m π` to `lagNum m (e * π)`. -/
theorem map_rename_lagNum (e π : Equiv.Perm (Fin m)) :
    (lagNum m π).map (MvPolynomial.rename e).toRingHom = lagNum m (e * π) := by
  simp only [lagNum, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_t]
  rw [prod_erase_mul_left]

/-- The universal resolvent `Φ m` is invariant under permutations of the universal roots. -/
theorem map_rename_Φ (e : Equiv.Perm (Fin m)) :
    (Φ m).map (MvPolynomial.rename e).toRingHom = Φ m := by
  simp only [Φ, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, rename_t]
  exact Fintype.prod_equiv (Equiv.mulLeft e) _ _ (fun _ => rfl)

/-- The universal discriminant `Δ m` is invariant under permutations of the universal roots. -/
theorem rename_Δ (e : Equiv.Perm (Fin m)) : MvPolynomial.rename e (Δ m) = Δ m := by
  simp only [Δ, map_prod, map_sub, rename_t]
  exact Fintype.prod_equiv (Equiv.mulLeft e) _ _ fun π => (prod_erase_mul_left m e π
    (fun π' => t m (e * π) - t m π')).symm

/-- `R m τ = ∑_π t(π τ) · discOff m π · lagNum m π`. -/
theorem R_eq (τ : Equiv.Perm (Fin m)) :
    R m τ = ∑ π, C (t m (π * τ) * discOff m π) * lagNum m π := rfl

/-- The universal Lagrange-type polynomial `R m τ` is invariant under permutations of the
universal roots. -/
theorem map_rename_R (e τ : Equiv.Perm (Fin m)) :
    (R m τ).map (MvPolynomial.rename e).toRingHom = R m τ := by
  rw [R_eq, Polynomial.map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft e) _ _ fun π => ?_
  rw [Polynomial.map_mul, map_C, map_rename_lagNum]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, rename_t,
    rename_discOff, Equiv.coe_mulLeft, mul_assoc]

/-- Every coefficient of the universal resolvent `Φ m` is symmetric in the universal roots. -/
theorem isSymmetric_coeff_Φ (k : ℕ) : (Φ m |>.coeff k).IsSymmetric := fun e => by
  have := congrArg (fun P => P.coeff k) (map_rename_Φ m e)
  simpa using this

/-- The universal discriminant `Δ m` is symmetric in the universal roots. -/
theorem isSymmetric_Δ : (Δ m).IsSymmetric := rename_Δ m

/-- Every coefficient of `R m τ` is symmetric in the universal roots. -/
theorem isSymmetric_coeff_R (τ : Equiv.Perm (Fin m)) (k : ℕ) : ((R m τ).coeff k).IsSymmetric :=
  fun e => by
    have := congrArg (fun P => P.coeff k) (map_rename_R m e τ)
    simpa using this

/-- Write a symmetric polynomial in the universal roots as a polynomial in the elementary
symmetric polynomials (the fundamental theorem of symmetric polynomials). -/
def desym (s : RootRing m) (hs : s.IsSymmetric) : MvPolynomial (Fin m) (CoeffRing m) :=
  (MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m)).symm ⟨s, hs⟩

/-- Substituting the elementary symmetric polynomials into `desym m s hs` recovers `s`. -/
theorem aeval_desym (s : RootRing m) (hs : s.IsSymmetric) :
    MvPolynomial.aeval (fun i : Fin m => MvPolynomial.esymm (Fin m) (CoeffRing m) (i + 1))
      (desym m s hs) = s := by
  rw [← MvPolynomial.esymmAlgHom_apply]
  show ((MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m))
    ((MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m)).symm ⟨s, hs⟩)).val = s
  rw [AlgEquiv.apply_symm_apply]

variable {m} {A B : Type*} [CommRing A] [CommRing B]

/-- Specialize the elementary symmetric polynomials to the signed coefficients of `f` and keep the
coefficients of the linear form as variables. -/
def κ (f : A[X]) : MvPolynomial (Fin m) (CoeffRing m) →+* MvPolynomial (Fin m) A :=
  MvPolynomial.eval₂Hom (MvPolynomial.map (Int.castRingHom A))
    (fun j : Fin m => MvPolynomial.C ((-1) ^ ((j : ℕ) + 1) * f.coeff (m - ((j : ℕ) + 1))))

/-- Evaluation of the universal roots at `b` and of the universal coefficients at `ψ ∘ c`. -/
def evalRoot (ψ : A →+* B) (c : Fin m → A) (b : Fin m → B) : RootRing m →+* B :=
  MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Int.castRingHom B) fun i => ψ (c i)) b

/-- `evalRoot ψ c b` sends `t(π)` to `∑ᵢ ψ (c i) * b (π i)`. -/
theorem evalRoot_t (ψ : A →+* B) (c : Fin m → A) (b : Fin m → B) (π : Equiv.Perm (Fin m)) :
    evalRoot ψ c b (t m π) = ∑ i, ψ (c i) * b (π i) := by
  simp [evalRoot, t]

/-- Evaluating the `n`-th elementary symmetric polynomial at `b` gives the `n`-th elementary
symmetric function of the values of `b`. -/
theorem eval₂_esymm {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Fintype σ]
    (g : R →+* S) (b : σ → S) (n : ℕ) :
    MvPolynomial.eval₂ g b (MvPolynomial.esymm σ R n) = (univ.val.map b).esymm n := by
  simp_rw [MvPolynomial.esymm, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_X, Finset.esymm_map_val]

/-- **The specialization of a symmetric function.** If `f` maps to `∏ (X - b i)`, then evaluating
the specialization of a symmetric polynomial `s` at `c` is evaluating `s` at the roots `b`. -/
theorem map_eval_κ_desym (f : A[X]) (ψ : A →+* B) (b : Fin m → B)
    (hb : f.map ψ = ∏ i, (X - C (b i))) (c : Fin m → A) (s : RootRing m) (hs : s.IsSymmetric) :
    ψ (MvPolynomial.eval c (κ f (desym m s hs))) = evalRoot ψ c b s := by
  conv_rhs => rw [← aeval_desym m s hs]
  generalize desym m s hs = P
  have hγ : ∀ r : CoeffRing m, ψ (MvPolynomial.eval₂ (Int.castRingHom A) c r) =
      MvPolynomial.eval₂ (Int.castRingHom B) (fun i => ψ (c i)) r := by
    intro r
    rw [MvPolynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have hvieta : ∀ j : Fin m, ψ ((-1) ^ ((j : ℕ) + 1) * f.coeff (m - ((j : ℕ) + 1))) =
      (univ.val.map b).esymm ((j : ℕ) + 1) := by
    intro j
    have hcoeff := congrArg (fun P => P.coeff (m - ((j : ℕ) + 1))) hb
    simp only [coeff_map] at hcoeff
    rw [Finset.prod_eq_multiset_prod] at hcoeff
    rw [show (univ.val.map fun i => X - C (b i)) = (univ.val.map b).map (fun t => X - C t) by
      rw [Multiset.map_map]; rfl] at hcoeff
    rw [Multiset.prod_X_sub_C_coeff _ (by simp)] at hcoeff
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin] at hcoeff
    have hk : m - (m - ((j : ℕ) + 1)) = (j : ℕ) + 1 := by omega
    rw [hk] at hcoeff
    rw [map_mul, hcoeff, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
    simp
  induction P using MvPolynomial.induction_on with
  | C a => simpa [κ, evalRoot] using hγ a
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp, MvPolynomial.aeval_X]
    congr 1
    simp only [κ, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_C, evalRoot,
      MvPolynomial.coe_eval₂Hom, eval₂_esymm, hvieta]

variable (m) in
/-- The universal resolvent `Φ m` is monic. -/
theorem monic_Φ : (Φ m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

variable (m) in
/-- The universal resolvent `Φ m` has degree `m !`. -/
theorem natDegree_Φ : (Φ m).natDegree = m ! := by
  rw [Φ, natDegree_prod_of_monic _ _ fun π _ => monic_X_sub_C _]
  simp [Fintype.card_perm]

variable (m) in
/-- The universal Lagrange-type polynomial `R m τ` has degree at most `m !`. -/
theorem natDegree_R_le (τ : Equiv.Perm (Fin m)) : (R m τ).natDegree ≤ m ! := by
  rw [R_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun π _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [lagNum, natDegree_prod_of_monic _ _ fun π _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  exact Nat.sub_le _ _

variable (m) in
/-- `Δ m` is the product of the factor `∏_{π' ≠ π} (t(π) - t(π'))` of index `π` and
`discOff m π`. -/
theorem Δ_eq_mul_discOff (π : Equiv.Perm (Fin m)) :
    Δ m = (∏ π' ∈ univ.erase π, (t m π - t m π')) * discOff m π := by
  rw [Δ, discOff, ← Finset.mul_prod_erase _ _ (Finset.mem_univ π)]

variable (m) in
/-- `R_τ(t(π)) = Δ · t(π τ)` for the universal polynomials. -/
theorem eval_R (τ π : Equiv.Perm (Fin m)) : (R m τ).eval (t m π) = Δ m * t m (π * τ) := by
  rw [R_eq, eval_finset_sum, Finset.sum_eq_single π]
  · rw [eval_mul, eval_C, lagNum, eval_prod, Δ_eq_mul_discOff m π]
    simp only [eval_sub, eval_X, eval_C]
    ring
  · intro ρ _ hρ
    rw [eval_mul, lagNum, eval_prod, Finset.prod_eq_zero (i := π)
      (Finset.mem_erase.mpr ⟨Ne.symm hρ, Finset.mem_univ π⟩) (by simp), mul_zero]
  · intro h; exact absurd (Finset.mem_univ π) h

/-- The specialization of a universal polynomial with symmetric coefficients of degree at most
`m !`. -/
def specPoly (f : A[X]) (c : Fin m → A) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) : A[X] :=
  ∑ k ∈ range (m ! + 1), C (MvPolynomial.eval c (κ f (desym m _ (hP k)))) * X ^ k

/-- If `f` maps to `∏ (X - b i)` under `ψ`, then the image under `ψ` of `specPoly f c P hP` is
`P` with its coefficients evaluated by `evalRoot ψ c b`. -/
theorem map_specPoly (f : A[X]) (ψ : A →+* B) (b : Fin m → B)
    (hb : f.map ψ = ∏ i, (X - C (b i))) (c : Fin m → A) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) (hdeg : P.natDegree ≤ m !) :
    (specPoly f c P hP).map ψ = P.map (evalRoot ψ c b) := by
  rw [specPoly, Polynomial.map_sum]
  simp only [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
    map_eval_κ_desym f ψ b hb c]
  conv_rhs => rw [(P.map (evalRoot ψ c b)).as_sum_range' (m ! + 1)
    ((natDegree_map_le).trans_lt (Nat.lt_succ_of_le hdeg))]
  simp [coeff_map, C_mul_X_pow_eq_monomial]

/-- The `k`-th coefficient of `specPoly f c P hP`. -/
private theorem coeff_specPoly (f : A[X]) (c : Fin m → A) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) (k : ℕ) :
    (specPoly f c P hP).coeff k =
      if k ∈ range (m ! + 1) then MvPolynomial.eval c (κ f (desym m _ (hP k))) else 0 := by
  simp only [specPoly, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]

end GaloisResolvent

open GaloisResolvent

variable {m : ℕ} {A B : Type*} [CommRing A] [CommRing B]

/-- The **Galois resolvent** `Φ(T) = ∏_π (T - ∑ᵢ cᵢ b_{π i})` of `f` for the linear form with
coefficients `c`, where the `b i` are the roots of `f`; its coefficients are polynomials in the
coefficients of `f` and in `c`, by the fundamental theorem of symmetric polynomials. -/
def galoisResolvent (f : A[X]) (c : Fin m → A) : A[X] :=
  specPoly f c (Φ m) (isSymmetric_coeff_Φ m)

variable (m) in
/-- The discriminant of the Galois resolvent as a polynomial in the coefficients `c` of the linear
form. -/
def resolventDiscPoly (f : A[X]) : MvPolynomial (Fin m) A :=
  κ f (desym m (Δ m) (isSymmetric_Δ m))

/-- The **resolvent discriminant** `∏_{π ≠ π'} (t(π) - t(π'))`. -/
def resolventDisc (f : A[X]) (c : Fin m → A) : A :=
  MvPolynomial.eval c (resolventDiscPoly m f)

/-- The **Lagrange-type polynomial** `R_τ`, with `R_τ(t(π)) = Δ · t(π τ)`. -/
def resolventPerm (f : A[X]) (c : Fin m → A) (τ : Equiv.Perm (Fin m)) : A[X] :=
  specPoly f c (R m τ) (isSymmetric_coeff_R m τ)

/-- The twisted composite `Δ^{deg Ψ} Ψ^{fr}(R / Δ)`, written without denominators. -/
def twistedComp (fr : A →+* A) (Ψ : A[X][X]) (R : A[X][X]) (Δ : A[X]) : A[X][X] :=
  ∑ k ∈ Finset.range (Ψ.natDegree + 1), C (Δ ^ (Ψ.natDegree - k) * (Ψ.coeff k).map fr) * R ^ k

/-- If `f` maps to `∏ (X - b i)` under `ψ`, then with `t(π) = ∑ᵢ ψ (c i) * b (π i)` the image of
`galoisResolvent f c` is `∏_π (X - t(π))`, the image of `resolventDisc f c` is
`Δ = ∏_{π ≠ π'} (t(π) - t(π'))`, and the image of `resolventPerm f c τ` takes the value
`Δ · t(π τ)` at `t(π)`. -/
theorem galoisResolvent_spec (f : A[X]) (c : Fin m → A) (ψ : A →+* B) (b : Fin m → B)
    (hb : f.map ψ = ∏ i, (X - C (b i))) :
    (galoisResolvent f c).map ψ = ∏ π : Equiv.Perm (Fin m), (X - C (∑ i, ψ (c i) * b (π i))) ∧
      ψ (resolventDisc f c) = ∏ π : Equiv.Perm (Fin m), ∏ π' ∈ Finset.univ.erase π,
        ((∑ i, ψ (c i) * b (π i)) - ∑ i, ψ (c i) * b (π' i)) ∧
      ∀ τ π : Equiv.Perm (Fin m), ((resolventPerm f c τ).map ψ).eval (∑ i, ψ (c i) * b (π i)) =
        ψ (resolventDisc f c) * ∑ i, ψ (c i) * b ((π * τ) i) := by
  have hΔ : ψ (resolventDisc f c) = evalRoot ψ c b (Δ m) := map_eval_κ_desym f ψ b hb c _ _
  refine ⟨?_, ?_, fun τ π => ?_⟩
  · rw [galoisResolvent, map_specPoly f ψ b hb c _ _ (natDegree_Φ m).le, Φ, Polynomial.map_prod]
    simp [evalRoot_t]
  · rw [hΔ, Δ]; simp [evalRoot_t]
  · rw [resolventPerm, map_specPoly f ψ b hb c _ _ (natDegree_R_le m τ), ← evalRoot_t ψ c b π,
      eval_map, eval₂_at_apply, eval_R, map_mul, hΔ, evalRoot_t]

/-- The Galois resolvent `galoisResolvent f c` is monic. -/
theorem galoisResolvent_monic (f : A[X]) (c : Fin m → A) : (galoisResolvent f c).Monic := by
  nontriviality A
  have hdeg : (galoisResolvent f c).natDegree ≤ m ! := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [galoisResolvent, coeff_specPoly, if_neg (by simpa using hk)]
  refine monic_of_natDegree_le_of_coeff_eq_one _ hdeg ?_
  rw [galoisResolvent, coeff_specPoly, if_pos (by simp)]
  have h1 : (Φ m).coeff (m !) = 1 := by
    rw [← natDegree_Φ m]; exact monic_Φ m
  have : desym m _ (isSymmetric_coeff_Φ m (m !)) = 1 := by
    rw [show desym m _ (isSymmetric_coeff_Φ m (m !)) = desym m 1 MvPolynomial.IsSymmetric.one
      by simp only [desym, h1]]
    simp only [desym]
    exact (MvPolynomial.esymmAlgEquiv (Fin m) (CoeffRing m) (Fintype.card_fin m)).symm.map_one
  rw [this, map_one, map_one]



namespace GaloisResolvent

/-- Evaluating a multivariate polynomial at polynomials of degree at most `d`, with constant
coefficients, gives a polynomial of degree at most `totalDegree * d`. -/
theorem natDegree_eval₂_le {σ S R : Type*} [CommSemiring S] [CommSemiring R] (g : S →+* R[X])
    (hg : ∀ s, (g s).natDegree = 0) (x : σ → R[X]) (d : ℕ) (hx : ∀ i, (x i).natDegree ≤ d)
    (P : MvPolynomial σ S) : (MvPolynomial.eval₂ g x P).natDegree ≤ P.totalDegree * d := by
  classical
  rw [MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun α hα => ?_
  refine (natDegree_mul_le).trans ?_
  rw [hg, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ α.support, (x i ^ α i).natDegree ≤ ∑ i ∈ α.support, α i * d :=
        Finset.sum_le_sum fun i _ => (natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hx i))
    _ = (α.sum fun _ e => e) * d := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ P.totalDegree * d := Nat.mul_le_mul_right _ (MvPolynomial.le_totalDegree hα)

/-- If the coefficients of `f ∈ R[X][X]` have degree at most `d`, then evaluating `κ f P` at
constants `C (c i)` gives a polynomial of degree at most `P.totalDegree * d`. -/
theorem natDegree_eval_κ_le {R : Type*} [CommRing R] (f : R[X][X]) (c : Fin m → R) (d : ℕ)
    (hf : ∀ j, (f.coeff j).natDegree ≤ d) (P : MvPolynomial (Fin m) (CoeffRing m)) :
    (MvPolynomial.eval (fun i => C (c i)) (κ f P)).natDegree ≤ P.totalDegree * d := by
  rw [κ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine natDegree_eval₂_le _ (fun r => ?_) _ d (fun j => ?_) P
  · have : (MvPolynomial.eval fun i => C (c i)) (MvPolynomial.map (Int.castRingHom R[X]) r) =
        C (MvPolynomial.eval₂ (Int.castRingHom R) c r) := by
      rw [MvPolynomial.eval_map, MvPolynomial.hom_eval₂]
      congr 1
    simp only [RingHom.comp_apply]
    rw [this, natDegree_C]
  simp only [Function.comp_apply, MvPolynomial.eval_C]
  refine (natDegree_mul_le).trans ?_
  rw [show ((-1 : R[X]) ^ ((j : ℕ) + 1)) = C ((-1) ^ ((j : ℕ) + 1)) by simp, natDegree_C, zero_add]
  exact hf _

/-- The coefficients of `specPoly` at constant `c` have degree at most `S * d`, if the total
degrees of the `desym` of the coefficients of `P` are at most `S`. -/
private theorem natDegree_coeff_specPoly_le {R : Type*} [CommRing R] (f : R[X][X]) (c : Fin m → R)
    (d : ℕ) (hf : ∀ j, (f.coeff j).natDegree ≤ d) (P : (RootRing m)[X])
    (hP : ∀ k, (P.coeff k).IsSymmetric) (S : ℕ)
    (hS : ∀ k ∈ range (m ! + 1), (desym m _ (hP k)).totalDegree ≤ S) (k : ℕ) :
    ((specPoly f (fun i => C (c i)) P hP).coeff k).natDegree ≤ S * d := by
  rw [coeff_specPoly]
  split_ifs with hk
  · exact (natDegree_eval_κ_le f c d hf _).trans (Nat.mul_le_mul_right _ (hS k hk))
  · simp

end GaloisResolvent

open GaloisResolvent in
/-- There is a bound `D`, depending only on `m` and `d`, such that for every monic `f ∈ R[X][X]`
of degree `m` whose coefficients have degree at most `d` and every `c` with constant coordinates,
the coefficients of `galoisResolvent f c`, the discriminant `resolventDisc f c`, and each
`resolventPerm f c τ` and its coefficients have degree at most `D`. -/
theorem exists_natDegree_resolvent_le (m d : ℕ) : ∃ D : ℕ, ∀ (R : Type*) [CommRing R]
    (f : R[X][X]) (c : Fin m → R), f.Monic → f.natDegree = m → (∀ j, (f.coeff j).natDegree ≤ d) →
      (∀ k, ((galoisResolvent f (fun i => C (c i))).coeff k).natDegree ≤ D) ∧
      (resolventDisc f (fun i => C (c i))).natDegree ≤ D ∧
      ∀ τ, (resolventPerm f (fun i => C (c i)) τ).natDegree ≤ D ∧
        ∀ k, ((resolventPerm f (fun i => C (c i)) τ).coeff k).natDegree ≤ D := by
  classical
  let S₁ := ∑ k ∈ range (m ! + 1), (desym m _ (isSymmetric_coeff_Φ m k)).totalDegree
  let S₂ := (desym m _ (isSymmetric_Δ m)).totalDegree
  let S₃ := ∑ τ : Equiv.Perm (Fin m), ∑ k ∈ range (m ! + 1),
    (desym m _ (isSymmetric_coeff_R m τ k)).totalDegree
  refine ⟨m ! + (S₁ + S₂ + S₃) * d, fun R _ f c _ _ hf =>
    ⟨fun k => ?_, ?_, fun τ => ⟨?_, fun k => ?_⟩⟩⟩
  · refine (natDegree_coeff_specPoly_le f c d hf _ _ S₁ (fun k hk => ?_) k).trans ?_
    · exact Finset.single_le_sum (f := fun k => (desym m _ (isSymmetric_coeff_Φ m k)).totalDegree)
        (fun _ _ => Nat.zero_le _) hk
    · nlinarith
  · rw [resolventDisc, resolventDiscPoly]
    refine (natDegree_eval_κ_le f c d hf _).trans ?_
    nlinarith
  · rw [resolventPerm, specPoly]
    refine (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_)
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have := Finset.mem_range.mp hk
    omega
  · refine (natDegree_coeff_specPoly_le f c d hf _ _ S₃ (fun k hk => ?_) k).trans ?_
    · refine le_trans (Finset.single_le_sum (f := fun k =>
        (desym m _ (isSymmetric_coeff_R m τ k)).totalDegree) (fun _ _ => Nat.zero_le _) hk)
        (Finset.single_le_sum (f := fun τ => ∑ k ∈ range (m ! + 1),
          (desym m _ (isSymmetric_coeff_R m τ k)).totalDegree) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ τ))
    · nlinarith

namespace GaloisResolvent

/-- Specializing along `f` viewed with constant coefficients in `MvPolynomial (Fin m) A` and then
evaluating at the variables gives the specialization `κ f P`. -/
theorem eval_X_κ_map_C {A : Type*} [CommRing A] (f : A[X])
    (P : MvPolynomial (Fin m) (CoeffRing m)) :
    MvPolynomial.eval MvPolynomial.X (κ (f.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)) P) =
      κ f P := by
  rw [κ, κ, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  congr 1
  · refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => by simp)
    simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C]
    rfl
  · funext j; simp [coeff_map]

/-- Mapping the coefficients along an injective ring homomorphism preserves the total degree. -/
theorem totalDegree_map_of_injective {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {g : R →+* S} (hg : Function.Injective g) (p : MvPolynomial σ R) :
    (MvPolynomial.map g p).totalDegree = p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree,
    MvPolynomial.support_map_of_injective _ hg]

end GaloisResolvent

open GaloisResolvent in
/-- For a monic `f` of degree `m` over a domain, separable over the fraction field, and a finite
set `S` with more than `(m !) ^ 2` elements, some `c` with coordinates in `S` has
`resolventDisc f c ≠ 0`. -/
theorem exists_resolventDisc_ne_zero {A : Type*} [CommRing A] [IsDomain A] (f : A[X])
    (hf : f.Monic) (hm : f.natDegree = m)
    (hsep : (f.map (algebraMap A (FractionRing A))).Separable) (S : Finset A)
    (hS : (m !) ^ 2 < S.card) :
    ∃ c : Fin m → A, (∀ i, c i ∈ S) ∧ resolventDisc f c ≠ 0 := by
  classical
  let K := FractionRing A
  let L := SplittingField (f.map (algebraMap A K))
  let fL := f.map (algebraMap A L)
  have hfL : fL = (f.map (algebraMap A K)).map (algebraMap K L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hsplit : Splits fL := hfL ▸ SplittingField.splits _
  have hsepL : fL.Separable := hfL ▸ hsep.map
  have hnodup := nodup_roots hsepL
  have hcard : fL.roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots,
      show fL.natDegree = f.natDegree from hf.natDegree_map _, hm]
  let e : fL.roots.toFinset ≃ Fin m := Fintype.equivFinOfCardEq (by simpa using hcard)
  let b : Fin m → L := fun i => (e.symm i : L)
  have hbinj : Function.Injective b := fun i j h => e.symm.injective (Subtype.ext h)
  have hb : fL = ∏ i, (X - C (b i)) := by
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic (hf.map _)]
    rw [show fL.roots = fL.roots.toFinset.val by
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup], ← Finset.prod_eq_multiset_prod,
      ← Finset.prod_coe_sort]
    exact Fintype.prod_equiv e _ _ fun x => by simp [b]
  let A' := MvPolynomial (Fin m) A
  let ψ : A' →+* MvPolynomial (Fin m) L := MvPolynomial.map (algebraMap A L)
  have hAL : Function.Injective (algebraMap A L) := IsScalarTower.algebraMap_eq A K L ▸
    (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let f' : A'[X] := f.map MvPolynomial.C
  have hb' : f'.map ψ = ∏ i, (X - C (MvPolynomial.C (b i))) := by
    have : f'.map ψ = fL.map MvPolynomial.C := by
      simp only [f', fL, Polynomial.map_map]; congr 1; exact MvPolynomial.map_comp_C _
    rw [this, hb, Polynomial.map_prod]; simp
  have hQ := (galoisResolvent_spec f' MvPolynomial.X ψ _ hb').2.1
  have hQeq : resolventDisc f' MvPolynomial.X = resolventDiscPoly m f := eval_X_κ_map_C f _
  rw [hQeq] at hQ
  have hfac : ∀ π : Equiv.Perm (Fin m), ∀ π' ∈ Finset.univ.erase π,
      ((∑ i, ψ (MvPolynomial.X i) * MvPolynomial.C (b (π i))) -
        ∑ i, ψ (MvPolynomial.X i) * MvPolynomial.C (b (π' i))) =
      ∑ i, MvPolynomial.C (b (π i) - b (π' i)) * MvPolynomial.X i := by
    intro π π' _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ψ (MvPolynomial.X i) = MvPolynomial.X i from MvPolynomial.map_X _ _, map_sub]
    ring
  have hlin : ∀ π : Equiv.Perm (Fin m), ∀ π' ∈ Finset.univ.erase π,
      (∑ i, MvPolynomial.C (b (π i) - b (π' i)) * MvPolynomial.X i : MvPolynomial (Fin m) L) ≠ 0 ∧
      (∑ i, MvPolynomial.C (b (π i) - b (π' i)) * MvPolynomial.X i :
        MvPolynomial (Fin m) L).totalDegree ≤ 1 := by
    intro π π' hπ'
    have hne : π' ≠ π := (Finset.mem_erase.mp hπ').1
    obtain ⟨i, hi⟩ : ∃ i, π i ≠ π' i := by
      by_contra! h; exact hne (Equiv.ext fun i => (h i).symm)
    refine ⟨fun h0 => ?_, ?_⟩
    · have := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h0
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
        MvPolynomial.coeff_zero, Finsupp.single_left_inj one_ne_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact hi (hbinj (sub_eq_zero.mp this))
    · refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hQ0 : resolventDiscPoly m f ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ
    refine (Finset.prod_ne_zero_iff.mpr fun π _ => Finset.prod_ne_zero_iff.mpr fun π' hπ' => ?_)
      hQ.symm
    rw [hfac π π' hπ']; exact (hlin π π' hπ').1
  have hdeg : (resolventDiscPoly m f).totalDegree < S.card := by
    have hmap : (ψ (resolventDiscPoly m f)).totalDegree = (resolventDiscPoly m f).totalDegree :=
      totalDegree_map_of_injective hAL _
    rw [← hmap, hQ]
    refine lt_of_le_of_lt ?_ hS
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans
      ((Finset.sum_le_sum fun π _ => ?_).trans (le_of_eq (show ∑ _π : Equiv.Perm (Fin m), m ! =
        (m !) ^ 2 by simp [Fintype.card_perm, sq])))
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine (Finset.sum_le_sum fun π' hπ' => ?_).trans (show ∑ _π' ∈ univ.erase π, 1 ≤ (m !) by
      simp [Finset.card_erase_of_mem (Finset.mem_univ π), Fintype.card_perm])
    rw [hfac π π' hπ']; exact (hlin π π' hπ').2
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hQ0 S
  by_contra! hall
  have hfilter : ({x ∈ Fintype.piFinset fun _ : Fin m => S |
      MvPolynomial.eval x (resolventDiscPoly m f) = 0} : Finset (Fin m → A)) =
      Fintype.piFinset fun _ => S :=
    Finset.filter_true_of_mem fun x hx => hall x (Fintype.mem_piFinset.mp hx)
  rw [hfilter, Fintype.card_piFinset_const, Nat.cast_pow] at hsz
  have hSpos : (0 : ℚ≥0) < S.card := by exact_mod_cast (Nat.zero_le _).trans_lt hS
  rw [div_self (pow_ne_zero _ hSpos.ne'), le_div_iff₀ hSpos, one_mul] at hsz
  exact absurd hsz (not_le.mpr (mod_cast hdeg))

end Polynomial

end
end

-- Bundled module: StacksFrontier.FieldTheory.GaloisResolventFactors
section






/-!
# The factors of the Galois resolvent and the twisted count

Let `K` be a field and `f ∈ K[X][Y]` monic of `Y`-degree `m`, irreducible and separable over
`K(X)`. Let `fr` be a ring automorphism of `K` fixing `f` (coefficientwise) and the coefficients
`c` of a linear form whose resolvent discriminant does not vanish. The Galois resolvent of `f`
factors over `K[X]` into the minimal polynomials `Ψ` of the values `t(π)`, one for each orbit of
the Galois group `G` of `f` over `K(X)`. Twisting by `fr` permutes the roots of `f` by a
permutation `π_σ`, and

* the permutations `τ` with `Ψ ∣ Ψ^{fr}(R_τ / Δ)` number `m !` in total, `|G|` for each factor;
* their fixed points number `m !` in total, by a twisted Burnside count.

## Main results

* `Polynomial.GaloisResolventFactors.sum_card_fixed_mul`: twisted Burnside.
* `Polynomial.exists_factors_galoisResolvent`: the factorization and the two counts.
-/


open Polynomial Finset Nat

namespace Polynomial

namespace GaloisResolventFactors

/-- Conjugating a permutation does not change its number of fixed points. -/
theorem card_fixed_conj {n : ℕ} (α ρ : Equiv.Perm (Fin n)) :
    (univ.filter fun i => (ρ⁻¹ * α * ρ) i = i).card = (univ.filter fun i => α i = i).card := by
  refine Finset.card_bij (fun i _ ↦ ρ i) (fun i hi ↦ ?_) (fun i _ j _ h ↦ ρ.injective h)
    (fun j hj ↦ ⟨ρ⁻¹ j, ?_, by simp⟩)
  · have hi' := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [Equiv.Perm.mul_apply] using congrArg ρ hi'
  · have hj' := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp [Equiv.Perm.mul_apply, hj']

/-- **Twisted Burnside.** If a finite group acts transitively on `Fin n` (`n > 0`) through `σ`,
then for every permutation `π` the elements `π σ(h)` have `|H|` fixed points in total. -/
theorem sum_card_fixed_mul {H : Type*} [Group H] [Fintype H] {n : ℕ} (hn : 0 < n)
    (σ : H →* Equiv.Perm (Fin n)) (htrans : ∀ i j, ∃ h, σ h i = j) (π : Equiv.Perm (Fin n)) :
    ∑ h : H, (univ.filter fun i => (π * σ h) i = i).card = Fintype.card H := by
  classical
  have hfib : ∀ i j, n * (univ.filter fun h : H ↦ σ h i = j).card = Fintype.card H := by
    intro i j
    have hsize : ∀ j', (univ.filter fun h : H ↦ σ h i = j').card =
        (univ.filter fun h : H ↦ σ h i = i).card := by
      intro j'
      obtain ⟨g, hg⟩ := htrans i j'
      refine Finset.card_bij (fun h _ ↦ g⁻¹ * h) (fun h hh ↦ ?_) (fun a _ b _ hab ↦ ?_)
        (fun h hh ↦ ⟨g * h, ?_, by simp⟩)
      · have hh' := (Finset.mem_filter.mp hh).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [map_mul, Equiv.Perm.mul_apply, hh', ← hg, map_inv]
        simp [Equiv.Perm.inv_def]
      · simpa using hab
      · have hh' := (Finset.mem_filter.mp hh).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [map_mul, Equiv.Perm.mul_apply, hh', hg]
    have htot : ∑ j' : Fin n, (univ.filter fun h : H ↦ σ h i = j').card = Fintype.card H := by
      rw [← Finset.card_univ, ← Finset.card_eq_sum_card_fiberwise (f := fun h : H ↦ σ h i)
        (fun _ _ ↦ Finset.mem_univ _)]
    simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at htot
    rw [hsize j, htot]
  have hswap : ∑ h : H, (univ.filter fun i ↦ (π * σ h) i = i).card =
      ∑ i : Fin n, (univ.filter fun h : H ↦ σ h i = π⁻¹ i).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun h _ ↦ ?_
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq]
    congr
  rw [hswap]
  have : ∀ i : Fin n, (univ.filter fun h : H ↦ σ h i = π⁻¹ i).card = Fintype.card H / n :=
    fun i ↦ by rw [← hfib i (π⁻¹ i), Nat.mul_div_cancel_left _ hn]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h0 := hfib ⟨0, hn⟩ ⟨0, hn⟩
  rw [← h0, Nat.mul_div_cancel_left _ hn]

variable {K : Type*} [Field K]

/-- An element `x` of `L` lies in the root set of `p` exactly when it is a root of the image of
`p` in `L[X]`. -/
theorem mem_rootSet_iff_mem_roots_map {F L : Type*} [Field F] [Field L] [Algebra F L]
    (p : F[X]) (x : L) : x ∈ p.rootSet L ↔ x ∈ (p.map (algebraMap F L)).roots := by
  classical
  rw [rootSet_def, Finset.mem_coe, aroots_def, Multiset.mem_toFinset]

/-- The roots of a monic separable `f ∈ K[X][Y]` in the splitting field of its image over `K(X)`,
labelled by `Fin m`. -/
theorem exists_roots_labelling {m : ℕ} (f : K[X][X]) (hf : f.Monic) (hm : f.natDegree = m)
    (hsep : (f.map (algebraMap K[X] (FractionRing K[X]))).Separable) :
    ∃ e : Fin m ≃ (f.map (algebraMap K[X] (FractionRing K[X]))).rootSet
        (f.map (algebraMap K[X] (FractionRing K[X]))).SplittingField,
      f.map (algebraMap K[X] (f.map (algebraMap K[X] (FractionRing K[X]))).SplittingField) =
        ∏ i, (X - C (e i : (f.map (algebraMap K[X] (FractionRing K[X]))).SplittingField)) := by
  classical
  set F := FractionRing K[X]
  set fF := f.map (algebraMap K[X] F)
  set L := fF.SplittingField
  have hsplit : Splits (fF.map (algebraMap F L)) := SplittingField.splits fF
  have hfL : f.map (algebraMap K[X] L) = fF.map (algebraMap F L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hmon : (f.map (algebraMap K[X] L)).Monic := hf.map _
  have hcard : Fintype.card (fF.rootSet L) = m := by
    rw [card_rootSet_eq_natDegree hsep hsplit, hf.natDegree_map, hm]
  let e : Fin m ≃ fF.rootSet L := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e, ?_⟩
  have hnodup : (fF.map (algebraMap F L)).roots.Nodup := nodup_roots hsep.map
  rw [hfL, hsplit.eq_prod_roots_of_monic ((hf.map (algebraMap K[X] F)).map (algebraMap F L))]
  rw [show (fF.map (algebraMap F L)).roots = (fF.map (algebraMap F L)).roots.toFinset.val by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup], ← Finset.prod_eq_multiset_prod]
  refine (Finset.prod_bij (fun x hx ↦ e.symm ⟨x, ?_⟩) (fun _ _ ↦ Finset.mem_univ _)
    (fun a ha b hb h ↦ by simpa using congrArg (fun i ↦ ((e i : _) : L)) h)
    (fun i _ ↦ ⟨(e i : L), ?_, by simp⟩) (fun x hx ↦ by simp)).trans rfl
  · exact (mem_rootSet_iff_mem_roots_map fF x).mpr (Multiset.mem_toFinset.mp hx)
  · exact Multiset.mem_toFinset.mpr ((mem_rootSet_iff_mem_roots_map fF _).mp (e i).2)

/-- `L` with its `F`-algebra structure twisted by a ring endomorphism `tw` of `F`. -/
def TwistedField (F L : Type*) [Field F] [Field L] [Algebra F L] (_tw : F →+* F) : Type _ := L

/-- `TwistedField F L tw` is a field, namely `L`. -/
instance {F L : Type*} [Field F] [Field L] [Algebra F L] (tw : F →+* F) :
    Field (TwistedField F L tw) := inferInstanceAs (Field L)

/-- The `F`-algebra structure on `TwistedField F L tw` given by `algebraMap F L ∘ tw`. -/
instance {F L : Type*} [Field F] [Field L] [Algebra F L] (tw : F →+* F) :
    Algebra F (TwistedField F L tw) := ((algebraMap F L).comp tw).toAlgebra

/-- A ring endomorphism of `F` fixing `p` extends to the splitting field of `p`. -/
theorem exists_ringHom_extend {F L : Type*} [Field F] [Field L] [Algebra F L] (p : F[X])
    [IsSplittingField F L p] (tw : F →+* F) (hp : p.map tw = p) :
    ∃ σt : L →+* L, ∀ x, σt (algebraMap F L x) = algebraMap F L (tw x) := by
  have hspl : Splits (p.map (algebraMap F (TwistedField F L tw))) := by
    show Splits (p.map ((algebraMap F L).comp tw))
    rw [← Polynomial.map_map, hp]
    exact IsSplittingField.splits L p
  let l : L →ₐ[F] TwistedField F L tw := IsSplittingField.lift L p hspl
  exact ⟨l.toRingHom, fun x ↦ l.commutes x⟩

end GaloisResolventFactors

open GaloisResolventFactors in
open scoped Classical in
/-- Let `f ∈ K[X][Y]` be monic of `Y`-degree `m`, irreducible, and separable over `K(X)`, let
`fr` be a ring automorphism of `K` fixing `f` and the coefficients `c`, and suppose
`resolventDisc f c ≠ 0`. Then `galoisResolvent f c` is the product of a finite set `𝒪` of monic
irreducible polynomials `Ψ`, the permutations `τ` with
`Ψ ∣ twistedComp fr Ψ (resolventPerm f c τ) (resolventDisc f c)` number `m !` in total over
`Ψ ∈ 𝒪`, and the fixed points of these permutations also number `m !` in total. -/
theorem exists_factors_galoisResolvent {K : Type*} [Field K] {m : ℕ} (f : K[X][X])
    (hf : f.Monic) (hm : f.natDegree = m) (hirr : Irreducible f)
    (hsep : (f.map (algebraMap K[X] (FractionRing K[X]))).Separable)
    (fr : K ≃+* K) (hfr : f.map (mapRingHom (fr : K →+* K)) = f) (c : Fin m → K)
    (hc : ∀ i, fr (c i) = c i) (hΔ : resolventDisc f (fun i => C (c i)) ≠ 0) :
    ∃ 𝒪 : Finset K[X][X], (∀ Ψ ∈ 𝒪, Ψ.Monic ∧ Irreducible Ψ) ∧
      ∏ Ψ ∈ 𝒪, Ψ = galoisResolvent f (fun i => C (c i)) ∧
      ∑ Ψ ∈ 𝒪, (Finset.univ.filter fun τ : Equiv.Perm (Fin m) =>
        Ψ ∣ twistedComp (fr : K →+* K) Ψ (resolventPerm f (fun i => C (c i)) τ)
          (resolventDisc f (fun i => C (c i)))).card = m ! ∧
      ∑ Ψ ∈ 𝒪, ∑ τ ∈ (Finset.univ.filter fun τ : Equiv.Perm (Fin m) =>
        Ψ ∣ twistedComp (fr : K →+* K) Ψ (resolventPerm f (fun i => C (c i)) τ)
          (resolventDisc f (fun i => C (c i)))),
        (Finset.univ.filter fun i => τ i = i).card = m ! := by
  classical
  set c' : Fin m → K[X] := fun i ↦ C (c i)
  set F := FractionRing K[X]
  set fF := f.map (algebraMap K[X] F)
  set L := fF.SplittingField
  set ψ := algebraMap K[X] L
  have hψ : Function.Injective ψ := by
    rw [show ψ = (algebraMap F L).comp (algebraMap K[X] F) from IsScalarTower.algebraMap_eq _ _ _]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective K[X] F)
  have : IsGalois F L := IsGalois.of_separable_splitting_field hsep
  have hm0 : 0 < m := by
    rw [← hm]; exact Nat.pos_of_ne_zero fun h ↦ hirr.not_isUnit (by
      rw [eq_one_of_monic_natDegree_zero hf h]; exact isUnit_one)
  obtain ⟨e, hb⟩ := exists_roots_labelling f hf hm hsep
  set b : Fin m → L := fun i ↦ (e i : L)
  have hbinj : Function.Injective b := fun i j h ↦ e.injective (Subtype.ext h)
  have hirrF : Irreducible fF :=
    (hf.irreducible_iff_irreducible_map_fraction_map).mp hirr
  let G := fF.Gal
  have hbroot : ∀ i, b i ∈ fF.rootSet L := fun i ↦ (e i).2
  let σ : G →* Equiv.Perm (Fin m) :=
    (Equiv.permCongrHom e.symm).toMonoidHom.comp (MulAction.toPermHom G (fF.rootSet L))
  have hσ : ∀ g i, b (σ g i) = g (b i) := fun g i ↦ by
    simp [σ, b, Equiv.permCongrHom_coe, Equiv.permCongr_apply]; rfl
  have hσinj : Function.Injective σ := by
    intro g g' h
    refine Gal.ext fF fun x hx ↦ ?_
    have h1 := hσ g (e.symm ⟨x, hx⟩)
    have h2 := hσ g' (e.symm ⟨x, hx⟩)
    simp only [b, Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, h]
  have hroot : ∀ i, Polynomial.aeval (b i) fF = 0 := fun i ↦
    (Polynomial.mem_rootSet.mp (hbroot i)).2
  have htrans : ∀ i j, ∃ g, σ g i = j := by
    intro i j
    have hi := minpoly.eq_of_irreducible hirrF (hroot i)
    have hj := minpoly.eq_of_irreducible hirrF (hroot j)
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) (E := L)).mp (hj.symm.trans hi)
    exact ⟨g, hbinj ((hσ g i).trans hg)⟩
  let t : Equiv.Perm (Fin m) → L := fun π ↦ ∑ i, ψ (c' i) * b (π i)
  have hgψ : ∀ (g : G) (x : K[X]), g (ψ x) = ψ x := fun g x ↦ by
    rw [IsScalarTower.algebraMap_apply K[X] F L]; exact g.commutes _
  have htg : ∀ (g : G) π, g (t π) = t (σ g * π) := fun g π ↦ by
    simp only [t, map_sum, map_mul, hgψ, Equiv.Perm.mul_apply, hσ]
  have hΔψ : ψ (resolventDisc f c') ≠ 0 := by
    rw [ne_eq, ← map_zero ψ]; exact fun h0 ↦ hΔ (hψ h0)
  have htinj : Function.Injective t := by
    intro π π' h
    by_contra hne
    have hspec := (galoisResolvent_spec f c' ψ b hb).2.1
    rw [hspec] at hΔψ
    exact (Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hΔψ π (Finset.mem_univ _)) π'
      (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩)) (sub_eq_zero.mpr h)
  have hΦ : (galoisResolvent f c').map ψ = ∏ π, (X - C (t π)) :=
    (galoisResolvent_spec f c' ψ b hb).1
  let frX : K[X] ≃+* K[X] := Polynomial.mapEquiv fr
  let frF : F ≃+* F := IsFractionRing.ringEquivOfRingEquiv frX
  have hfrF : ∀ x : K[X], frF (algebraMap K[X] F x) = algebraMap K[X] F (frX x) :=
    fun x ↦ IsFractionRing.ringEquivOfRingEquiv_algebraMap frX x
  have hfF : fF.map (frF : F →+* F) = fF := by
    simp only [fF, Polynomial.map_map]
    have : (frF : F →+* F).comp (algebraMap K[X] F) =
        (algebraMap K[X] F).comp (frX : K[X] →+* K[X]) :=
      RingHom.ext hfrF
    rw [this, ← Polynomial.map_map]
    congr 1
  obtain ⟨σt, hσtF⟩ := exists_ringHom_extend (L := L) fF (frF : F →+* F) hfF
  have hσtψ : ∀ x : K[X], σt (ψ x) = ψ (frX x) := fun x ↦ by
    rw [IsScalarTower.algebraMap_apply K[X] F L, hσtF]
    show algebraMap F L (frF (algebraMap K[X] F x)) = _
    rw [hfrF, ← IsScalarTower.algebraMap_apply]
  have hσtroot : ∀ i, σt (b i) ∈ fF.rootSet L := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨(hf.map _).ne_zero, ?_⟩
    have h0 := hroot i
    rw [Polynomial.aeval_def] at h0 ⊢
    have hcomp : σt.comp (algebraMap F L) = (algebraMap F L).comp (frF : F →+* F) :=
      RingHom.ext hσtF
    have := congrArg σt h0
    rwa [map_zero, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hfF] at this
  have hπinj : Function.Injective fun i ↦ e.symm ⟨σt (b i), hσtroot i⟩ := by
    intro i j h
    have := congrArg (fun x ↦ ((e x : fF.rootSet L) : L)) h
    simp only [Equiv.apply_symm_apply] at this
    exact hbinj (σt.injective this)
  let πσ : Equiv.Perm (Fin m) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hπinj)
  have hσtb : ∀ i, σt (b i) = b (πσ i) := fun i ↦ by
    simp [πσ, b, Equiv.ofBijective_apply]
  have hσtt : ∀ π, σt (t π) = t (πσ * π) := fun π ↦ by
    simp only [t, map_sum, map_mul, hσtψ, hσtb, Equiv.Perm.mul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 2
    simp [frX, c', hc]
  have hΦmon : (galoisResolvent f c').Monic := galoisResolvent_monic f c'
  have hint : ∀ π, IsIntegral K[X] (t π) := fun π ↦ ⟨_, hΦmon, by
    rw [← Polynomial.eval_map, hΦ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ π) (by simp)⟩
  have : Module.IsTorsionFree K[X] L := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  let Ψ : Equiv.Perm (Fin m) → K[X][X] := fun π ↦ minpoly K[X] (t π)
  have hΨmon : ∀ π, (Ψ π).Monic := fun π ↦ minpoly.monic (hint π)
  have hΨirr : ∀ π, Irreducible (Ψ π) := fun π ↦
    (minpoly.prime_of_isIntegrallyClosed (hint π)).irreducible
  have hΨF : ∀ π, (Ψ π).map (algebraMap K[X] F) = minpoly F (t π) := fun π ↦
    (minpoly.isIntegrallyClosed_eq_field_fractions' F (hint π)).symm
  have hΨL : ∀ π, (Ψ π).map ψ = ∏ g : G, (X - C (t (σ g * π))) := by
    intro π
    set P : L[X] := ∏ g : G, (X - C (t (σ g * π)))
    have hPmon : P.Monic := monic_prod_of_monic _ _ fun g _ ↦ monic_X_sub_C _
    have hN : (Ψ π).map ψ = (minpoly F (t π)).map (algebraMap F L) := by
      rw [← hΨF, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hNmon : ((Ψ π).map ψ).Monic := (hΨmon π).map ψ
    have hinjG : Function.Injective fun g : G ↦ t (σ g * π) := fun g g' h ↦
      hσinj (mul_right_cancel (htinj h))
    have hdvd : P ∣ (Ψ π).map ψ := by
      have hle : (Finset.univ.val.map fun g : G ↦ t (σ g * π)) ≤ ((Ψ π).map ψ).roots := by
        refine (Multiset.le_iff_subset (Multiset.Nodup.map hinjG Finset.univ.nodup)).mpr ?_
        intro x hx
        obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hx
        rw [mem_roots hNmon.ne_zero, IsRoot, hN, ← htg, eval_map, ← aeval_def]
        rw [show (g : L ≃ₐ[F] L) (t π) = (g : L ≃ₐ[F] L).toAlgHom (t π) from rfl,
          aeval_algHom_apply, minpoly.aeval, map_zero]
      have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hNmon.ne_zero _).mpr hle
      rwa [Multiset.map_map] at this
    have hfix : ∀ n (h : G), (h : L ≃ₐ[F] L) (P.coeff n) = P.coeff n := by
      intro n h
      have : P.map ((h : L ≃ₐ[F] L) : L →+* L) = P := by
        simp only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
        refine Fintype.prod_equiv (Equiv.mulLeft h) _ _ fun g ↦ ?_
        simp only [Equiv.coe_mulLeft, RingHom.coe_coe, htg, map_mul, mul_assoc]
      simpa using congrArg (fun Q ↦ Q.coeff n) this
    have hlifts : P ∈ Polynomial.lifts (algebraMap F L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n ↦ (IsGalois.mem_range_algebraMap_iff_fixed (P.coeff n)).mpr fun h ↦ hfix n h
    obtain ⟨Q, hQ, hQdeg, hQmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hPmon
    have hQroot : Polynomial.aeval (t π) Q = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, hQ, eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ 1) ?_
      simp
    have hdeg : ((Ψ π).map ψ).natDegree ≤ P.natDegree := by
      rw [hN, (minpoly.monic (hint π).tower_top).natDegree_map, ← hQdeg]
      exact natDegree_le_of_dvd (minpoly.dvd F (t π) hQroot) hQmon.ne_zero
    exact eq_of_monic_of_dvd_of_natDegree_le hPmon hNmon hdvd hdeg
  have hfibre : ∀ π π', Ψ π' = Ψ π ↔ ∃ g : G, π' = σ g * π := by
    intro π π'
    constructor
    · intro h
      have h0 : ((Ψ π).map ψ).eval (t π') = 0 := by
        rw [← h, eval_map, ← aeval_def]; exact minpoly.aeval _ _
      rw [hΨL, eval_prod] at h0
      obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.mp h0
      exact ⟨g, htinj (sub_eq_zero.mp (by simpa using hg))⟩
    · rintro ⟨g, rfl⟩
      simp only [Ψ, ← htg]
      exact minpoly.algEquiv_eq ((g : L ≃ₐ[F] L).restrictScalars K[X]) (t π)
  have hfibre_eq : ∀ π, (Finset.univ.filter fun π' ↦ Ψ π' = Ψ π) =
      Finset.univ.image fun g : G ↦ σ g * π := by
    intro π
    ext π'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hfibre π π']
    exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, hg.symm⟩, fun ⟨g, hg⟩ ↦ ⟨g, hg.symm⟩⟩
  have hσπinj : ∀ π, Function.Injective fun g : G ↦ σ g * π := fun π g g' h ↦
    hσinj (mul_right_cancel h)
  have hfibre_card : ∀ π, (Finset.univ.filter fun π' ↦ Ψ π' = Ψ π).card = Fintype.card G := by
    intro π
    rw [hfibre_eq, Finset.card_image_of_injective _ (hσπinj π), Finset.card_univ]
  set 𝒪 := Finset.univ.image Ψ with h𝒪
  have hrep : ∀ Ψ₀ ∈ 𝒪, ∃ π, Ψ π = Ψ₀ := fun Ψ₀ h ↦ by
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp h; exact ⟨π, hπ⟩
  have hconst : ∀ F : K[X][X] → ℕ, (∀ π, F (Ψ π) = Fintype.card G) →
      ∑ Ψ₀ ∈ 𝒪, F Ψ₀ = m ! := fun F hF ↦ by
    have := Finset.card_eq_sum_card_fiberwise (f := Ψ) (s := Finset.univ) (t := 𝒪)
      (fun π _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ π))
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this
    rw [this]
    refine Finset.sum_congr rfl fun Ψ₀ h ↦ ?_
    obtain ⟨π, rfl⟩ := hrep Ψ₀ h
    rw [hF, hfibre_card]
  have hprod : ∏ Ψ₀ ∈ 𝒪, Ψ₀ = galoisResolvent f c' := by
    apply Polynomial.map_injective ψ hψ
    rw [Polynomial.map_prod, hΦ, ← Finset.prod_fiberwise_of_maps_to (g := Ψ) (t := 𝒪)
      (fun π _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ π))]
    refine Finset.prod_congr rfl fun Ψ₀ h ↦ ?_
    obtain ⟨π, rfl⟩ := hrep Ψ₀ h
    rw [hΨL, hfibre_eq, Finset.prod_image fun g _ g' _ hg ↦ hσπinj π hg]
  have hcomp : ψ.comp (frX : K[X] →+* K[X]) = σt.comp ψ := RingHom.ext fun x ↦ (hσtψ x).symm
  have hTC : ∀ π₀ τ, Polynomial.aeval (t π₀) (twistedComp (fr : K →+* K) (Ψ π₀)
      (resolventPerm f c' τ) (resolventDisc f c')) =
      ψ (resolventDisc f c') ^ (Ψ π₀).natDegree *
        (((Ψ π₀).map ψ).map σt).eval (t (π₀ * τ)) := by
    intro π₀ τ
    have hR : Polynomial.aeval (t π₀) (resolventPerm f c' τ) =
        ψ (resolventDisc f c') * t (π₀ * τ) := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (galoisResolvent_spec f c' ψ b hb).2.2 τ π₀
    have hmap : ((Ψ π₀).map ψ).map σt = ((Ψ π₀).map (frX : K[X] →+* K[X])).map ψ := by
      rw [Polynomial.map_map, Polynomial.map_map, hcomp]
    have hdeg : (((Ψ π₀).map (frX : K[X] →+* K[X])).map ψ).natDegree < (Ψ π₀).natDegree + 1 :=
      Nat.lt_succ_of_le (natDegree_map_le.trans natDegree_map_le)
    rw [hmap, eval_eq_sum_range' hdeg, twistedComp]
    simp only [map_sum, map_mul, aeval_C, map_pow, hR]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ (Ψ π₀).natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [coeff_map, coeff_map]
    have : ((Ψ π₀).coeff k).map (fr : K →+* K) = frX ((Ψ π₀).coeff k) := rfl
    rw [show algebraMap K[X] L = ψ from rfl, this, mul_pow,
      show ψ (resolventDisc f c') ^ (Ψ π₀).natDegree =
          ψ (resolventDisc f c') ^ ((Ψ π₀).natDegree - k) * ψ (resolventDisc f c') ^ k by
        rw [← pow_add, Nat.sub_add_cancel hk']]
    simp only [RingEquiv.coe_toRingHom]
    ring
  have hT : ∀ π₀, (Finset.univ.filter fun τ : Equiv.Perm (Fin m) ↦
      Ψ π₀ ∣ twistedComp (fr : K →+* K) (Ψ π₀) (resolventPerm f c' τ) (resolventDisc f c')) =
      Finset.univ.image fun g : G ↦ π₀⁻¹ * (πσ * (σ g * π₀)) := by
    intro π₀
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [← minpoly.isIntegrallyClosed_dvd_iff (hint π₀), hTC]
    refine Iff.trans (mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hΔψ))) ?_
    rw [hΨL, Polynomial.map_prod, eval_prod]
    simp only [Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C, hσtt]
    rw [Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, sub_eq_zero]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      rw [← htinj hg]; group
    · rintro ⟨g, rfl⟩
      refine ⟨g, congrArg t ?_⟩
      group
  have hTinj : ∀ π₀, Function.Injective fun g : G ↦ π₀⁻¹ * (πσ * (σ g * π₀)) := by
    intro π₀ g g' h
    simp only [mul_left_cancel_iff, mul_right_cancel_iff] at h
    exact hσinj h
  refine ⟨𝒪, fun Ψ₀ h ↦ ?_, hprod, ?_, ?_⟩
  · obtain ⟨π, rfl⟩ := hrep Ψ₀ h
    exact ⟨hΨmon π, hΨirr π⟩
  · refine hconst _ fun π ↦ ?_
    rw [hT, Finset.card_image_of_injective _ (hTinj π), Finset.card_univ]
  · refine hconst _ fun π ↦ ?_
    rw [hT, Finset.sum_image fun g _ g' _ hg ↦ hTinj π hg, ← sum_card_fixed_mul hm0 σ htrans πσ]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simpa only [mul_assoc] using card_fixed_conj (πσ * σ g) π

end Polynomial

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.GaloisResolventPoints
section






/-!
# Points of the factors of the Galois resolvent

Auxiliary facts for counting points on the factors of the Galois resolvent of a plane curve over
a finite field.

## Main results

* `FiniteField.exists_algebraMap_eq_of_pow_card_eq`: an element fixed by the `q`-power map lies
  in the image of the field with `q` elements.
* `Polynomial.Bivariate.WeightedDegreeLE.of_dvd`: a divisor of a nonzero polynomial of total
  degree at most `T` has total degree at most `T`.
* `Polynomial.Bivariate.existsUnique_factor_root`: over a point where the resolvent splits into
  distinct linear factors, each root lies on exactly one factor, and is a simple point of it.
* `Polynomial.evalEval_twistedComp`: the twisted composite at a point.
* `Polynomial.Bivariate.weightedDegreeLE_zero_twistedComp`, `Polynomial.natDegree_twistedComp_le`:
  degree bounds for the twisted composite.
-/


open Polynomial Finset
open scoped Polynomial.Bivariate

/-- **Fixed points of the Frobenius are rational.** In an extension `L` of a finite field `F`
with `q` elements, an element `x` with `x ^ q = x` lies in the image of `F`. -/
theorem FiniteField.exists_algebraMap_eq_of_pow_card_eq {F L : Type*} [Field F] [Fintype F]
    [Field L] [Algebra F L] {x : L} (hx : x ^ Fintype.card F = x) :
    ∃ a : F, algebraMap F L a = x := by
  classical
  by_contra hne
  push Not at hne
  set q := Fintype.card F
  have hq : 1 < q := Fintype.one_lt_card
  set p : L[X] := X ^ q - X
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hq
  set S := Finset.univ.image (algebraMap F L)
  have hS : S.card = q := by
    rw [Finset.card_image_of_injective _ (algebraMap F L).injective, Finset.card_univ]
  have hsub : insert x S ⊆ p.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
      rw [← map_pow, FiniteField.pow_card]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (fun h => by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h; exact hne a ha), hS] at hcard
  have := (Multiset.toFinset_card_le _).trans (card_roots' p)
  rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), natDegree_X_pow] at this
  omega

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- If `g` has weighted degree at most `T` for the weights `1` on `X` and `1` on `Y`, then the
total degree of `equivMvPolynomial R g` is at most `T`. -/
theorem totalDegree_equivMvPolynomial_le_of_weightedDegreeLE {g : R[X][Y]} {T : ℕ}
    (hg : WeightedDegreeLE 1 T g) : (equivMvPolynomial R g).totalDegree ≤ T := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun s hs => ?_
  have hs' : s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) := by
    ext i; fin_cases i <;> simp
  have hcoeff := MvPolynomial.mem_support_iff.mp hs
  rw [hs', coeff_equivMvPolynomial] at hcoeff
  have hj : g.coeff (s 1) ≠ 0 := fun h => hcoeff (by rw [h, coeff_zero])
  have hi : s 0 ≤ (g.coeff (s 1)).natDegree := le_natDegree_of_ne_zero hcoeff
  have := hg (s 1) hj
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  omega

/-- A polynomial `g` has weighted degree, for the weights `1` on `X` and `1` on `Y`, at most the
total degree of `equivMvPolynomial R g`. -/
theorem weightedDegreeLE_one_totalDegree (g : R[X][Y]) :
    WeightedDegreeLE 1 (equivMvPolynomial R g).totalDegree g := fun j hj => by
  simpa using natDegree_coeff_add_le_totalDegree g j hj

/-- A divisor of a nonzero polynomial of total degree at most `T` has total degree at most
`T`. -/
theorem WeightedDegreeLE.of_dvd {K : Type*} [Field K] {Ψ Φ : K[X][X]} (hΦ : Φ ≠ 0) (h : Ψ ∣ Φ)
    {T : ℕ} (hT : WeightedDegreeLE 1 T Φ) : WeightedDegreeLE 1 T Ψ := by
  obtain ⟨Q, rfl⟩ := h
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hΦ
  have hΨ : Ψ ≠ 0 := left_ne_zero_of_mul hΦ
  have htot := totalDegree_equivMvPolynomial_le_of_weightedDegreeLE hT
  have hne : ∀ g : K[X][X], g ≠ 0 → equivMvPolynomial K g ≠ 0 := fun g hg => by
    rwa [ne_eq, map_eq_zero_iff _ (equivMvPolynomial K).injective]
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain (hne _ hΨ) (hne _ hQ)] at htot
  exact (weightedDegreeLE_one_totalDegree Ψ).mono (by omega)

end Polynomial.Bivariate

namespace Polynomial.Bivariate

/-- **Each root lies on exactly one factor, simply.** If `∏_{Ψ ∈ 𝒪} Ψ = Φ` and the fibre of `Φ`
over `a` splits into distinct linear factors `X - t i`, then each `t i` is a root of exactly one
`Ψ(a, ·)`, and a simple one. -/
theorem existsUnique_factor_root {K : Type*} [Field K] {𝒪 : Finset K[X][X]} {Φ : K[X][X]}
    (hΦ : ∏ Ψ ∈ 𝒪, Ψ = Φ) {a : K} {ι : Type*} [Fintype ι] {t : ι → K}
    (ht : Function.Injective t) (hspl : Φ.map (evalRingHom a) = ∏ i, (X - C (t i))) (i : ι) :
    (∃! Ψ, Ψ ∈ 𝒪 ∧ Ψ.evalEval a (t i) = 0) ∧
      ∀ Ψ ∈ 𝒪, Ψ.evalEval a (t i) = 0 → (derivative Ψ).evalEval a (t i) ≠ 0 := by
  classical
  set P : K[X][X] → K[X] := fun Ψ => Ψ.map (evalRingHom a)
  have hprod : ∏ Ψ ∈ 𝒪, P Ψ = ∏ j, (X - C (t j)) := by
    rw [← hspl, ← hΦ, Polynomial.map_prod]
  have hne : ∏ j, (X - C (t j)) ≠ 0 := (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _).ne_zero
  have hPne : ∀ Ψ ∈ 𝒪, P Ψ ≠ 0 := fun Ψ hΨ h =>
    hne (hprod ▸ Finset.prod_eq_zero hΨ h)
  -- multiplicities add up to one
  have hmult_prod : ∀ (s : Finset K[X][X]), s ⊆ 𝒪 →
      (∏ Ψ ∈ s, P Ψ).rootMultiplicity (t i) = ∑ Ψ ∈ s, (P Ψ).rootMultiplicity (t i) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert Ψ s hΨ ih =>
      have hs' : s ⊆ 𝒪 := (Finset.subset_insert _ _).trans hs
      rw [Finset.prod_insert hΨ, Finset.sum_insert hΨ, rootMultiplicity_mul, ih hs']
      exact mul_ne_zero (hPne Ψ (hs (Finset.mem_insert_self _ _)))
        (Finset.prod_ne_zero_iff.mpr fun Ψ' h => hPne Ψ' (hs' h))
  have hone : ∑ Ψ ∈ 𝒪, (P Ψ).rootMultiplicity (t i) = 1 := by
    rw [← hmult_prod 𝒪 subset_rfl, hprod, ← count_roots, Finset.prod_eq_multiset_prod,
      show (Finset.univ.val.map fun j => X - C (t j)) =
        (Finset.univ.val.map t).map (fun x => X - C x) by rw [Multiset.map_map]; rfl,
      roots_multiset_prod_X_sub_C]
    rw [Multiset.count_eq_one_of_mem (Multiset.Nodup.map ht Finset.univ.nodup)
      (Multiset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)]
  have hroot : ∀ Ψ, Ψ.evalEval a (t i) = 0 ↔ (P Ψ).IsRoot (t i) := fun Ψ => by
    rw [IsRoot, map_evalRingHom_eval]
  refine ⟨?_, fun Ψ hΨ h0 h1 => ?_⟩
  · obtain ⟨Ψ, hΨ, hpos⟩ : ∃ Ψ ∈ 𝒪, 0 < (P Ψ).rootMultiplicity (t i) := by
      by_contra! h
      rw [Finset.sum_eq_zero fun Ψ hΨ => Nat.le_zero.mp (h Ψ hΨ)] at hone
      exact zero_ne_one hone
    refine ⟨Ψ, ⟨hΨ, (hroot Ψ).mpr ((rootMultiplicity_pos (hPne Ψ hΨ)).mp hpos)⟩, ?_⟩
    rintro Ψ' ⟨hΨ', h'⟩
    by_contra hne'
    have h1 : 0 < (P Ψ').rootMultiplicity (t i) :=
      (rootMultiplicity_pos (hPne Ψ' hΨ')).mpr ((hroot Ψ').mp h')
    have : (P Ψ).rootMultiplicity (t i) + (P Ψ').rootMultiplicity (t i) ≤
        ∑ Ψ ∈ 𝒪, (P Ψ).rootMultiplicity (t i) := by
      rw [← Finset.sum_pair (f := fun Ψ => (P Ψ).rootMultiplicity (t i)) (Ne.symm hne')]
      exact Finset.sum_le_sum_of_subset (by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hΨ
        · rw [Finset.mem_singleton.mp hx]; exact hΨ')
    omega
  · have hlt : 1 < (P Ψ).rootMultiplicity (t i) := by
      rw [one_lt_rootMultiplicity_iff_isRoot (hPne Ψ hΨ)]
      refine ⟨(hroot Ψ).mp h0, ?_⟩
      rw [IsRoot, show derivative (P Ψ) = (derivative Ψ).map (evalRingHom a) from
        derivative_map _ _, map_evalRingHom_eval]
      exact h1
    have := Finset.single_le_sum (f := fun Ψ => (P Ψ).rootMultiplicity (t i))
      (fun _ _ => Nat.zero_le _) hΨ
    omega

end Polynomial.Bivariate

namespace Polynomial

/-- **The twisted composite at a point.** If `fr a = a` and `R(a, u) = Δ(a) fr(u)`, then the
twisted composite `Δ^{deg Ψ} Ψ^{fr}(R / Δ)` takes the value `Δ(a)^{deg Ψ} fr(Ψ(a, u))` at
`(a, u)`. -/
theorem evalEval_twistedComp {K : Type*} [Field K] (fr : K →+* K) (Ψ R : K[X][X]) (Δ : K[X])
    {a u : K} (ha : fr a = a) (hR : R.evalEval a u = Δ.eval a * fr u) :
    (twistedComp fr Ψ R Δ).evalEval a u = Δ.eval a ^ Ψ.natDegree * fr (Ψ.evalEval a u) := by
  have hcoef : ∀ k, ((Ψ.coeff k).map fr).eval a = fr ((Ψ.coeff k).eval a) := fun k => by
    rw [eval_map, eval, hom_eval₂, RingHom.comp_id, ha]
  have hΨ : Ψ.evalEval a u = ∑ k ∈ range (Ψ.natDegree + 1), (Ψ.coeff k).eval a * u ^ k := by
    rw [← map_evalRingHom_eval, eval_eq_sum_range' (Nat.lt_succ_of_le natDegree_map_le)]
    simp [coeff_map]
  rw [twistedComp, evalEval_finsetSum, hΨ, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ Ψ.natDegree := Finset.mem_range_succ_iff.mp hk
  rw [evalEval_mul, evalEval_C, evalEval_pow, hR, eval_mul, eval_pow, hcoef, map_mul, map_pow,
    mul_pow, show Δ.eval a ^ Ψ.natDegree = Δ.eval a ^ (Ψ.natDegree - k) * Δ.eval a ^ k by
      rw [← pow_add, Nat.sub_add_cancel hk']]
  ring

end Polynomial

namespace Polynomial.Bivariate

/-- **Coefficient degrees of the twisted composite.** If the coefficients of `Ψ` and `R` have
degree at most `DΨ` and `DR` and `Δ` has degree at most `DΔ`, then the coefficients of
`twistedComp fr Ψ R Δ` have degree at most `Ψ.natDegree * (DΔ + DR) + DΨ`. -/
theorem weightedDegreeLE_zero_twistedComp {K : Type*} [Field K] (fr : K →+* K) {Ψ R : K[X][X]}
    {Δ : K[X]} {DΨ DR DΔ : ℕ} (hΨ : WeightedDegreeLE 0 DΨ Ψ) (hR : WeightedDegreeLE 0 DR R)
    (hΔ : Δ.natDegree ≤ DΔ) :
    WeightedDegreeLE 0 (Ψ.natDegree * (DΔ + DR) + DΨ) (twistedComp fr Ψ R Δ) := by
  refine WeightedDegreeLE.sum _ fun k hk => ?_
  have hk' : k ≤ Ψ.natDegree := Finset.mem_range_succ_iff.mp hk
  have hC : (Δ ^ (Ψ.natDegree - k) * (Ψ.coeff k).map fr).natDegree ≤
      (Ψ.natDegree - k) * DΔ + DΨ :=
    (natDegree_mul_le).trans (Nat.add_le_add
      ((natDegree_pow_le).trans (Nat.mul_le_mul_left _ hΔ))
      (natDegree_map_le.trans (hΨ.coeff_natDegree_le k)))
  refine ((WeightedDegreeLE.C hC).mul (hR.pow k)).mono ?_
  have : (Ψ.natDegree - k) * DΔ ≤ Ψ.natDegree * DΔ := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have : k * DR ≤ Ψ.natDegree * DR := Nat.mul_le_mul_right _ hk'
  nlinarith

end Polynomial.Bivariate

namespace Polynomial

/-- **The `Y`-degree of the twisted composite.** The degree of `twistedComp fr Ψ R Δ` is at most
`Ψ.natDegree * R.natDegree`. -/
theorem natDegree_twistedComp_le {K : Type*} [Field K] (fr : K →+* K) (Ψ R : K[X][X])
    (Δ : K[X]) : (twistedComp fr Ψ R Δ).natDegree ≤ Ψ.natDegree * R.natDegree := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' : k ≤ Ψ.natDegree := Finset.mem_range_succ_iff.mp hk
  refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
  exact Nat.mul_le_mul_right _ hk'

end Polynomial

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.CurveDerivation
section



/-!
# The derivation along a plane curve

For `Ψ ∈ R[X][Y]`, the derivation `δ_Ψ = Ψ_Y ∂_X - Ψ_X ∂_Y` of `R[X][Y]` kills `Ψ`, so it is a
derivation along the curve `Ψ = 0`. On a power-series branch `s ↦ (a + s, β(s))` of the curve it
becomes `u · d/ds`, where `u = Ψ_Y(a + s, β(s))`: this is the chain rule
`d/ds g(a + s, β(s)) = g_X(a + s, β(s)) + g_Y(a + s, β(s)) β'(s)` together with
`Ψ(a + s, β(s)) = 0`.

## Main definitions

* `Polynomial.Bivariate.derivX`: the partial derivative in the inner variable `X`.
* `Polynomial.Bivariate.curveDeriv`: the derivation `Ψ_Y ∂_X - Ψ_X ∂_Y`.
* `Polynomial.Bivariate.branchEval`: evaluation along the power-series curve `s ↦ (a + s, β)`.

## Main results

* `Polynomial.Bivariate.WeightedDegreeLE.iterate_curveDeriv`: `δ_Ψ` raises weighted degree by at
  most that of `Ψ`.
* `Polynomial.Bivariate.derivative_branchEval`: the chain rule along a branch.
* `Polynomial.Bivariate.branchEval_iterate_curveDeriv`: on a branch, `δ_Ψ^j` becomes
  `(u · d/ds)^j`.
-/


open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

section CommRing

variable {R : Type*} [CommRing R]

/-- The partial derivative of a bivariate polynomial with respect to the inner variable `X`. -/
noncomputable def derivX (g : R[X][Y]) : R[X][Y] :=
  ∑ j ∈ g.support, monomial j (derivative (g.coeff j))

/-- The `j`-th coefficient of `∂_X g` is the derivative of the `j`-th coefficient of `g`. -/
@[simp]
theorem coeff_derivX (g : R[X][Y]) (j : ℕ) : (derivX g).coeff j = derivative (g.coeff j) := by
  rw [derivX, finset_sum_coeff]
  simp only [coeff_monomial]
  by_cases hj : j ∈ g.support
  · rw [Finset.sum_eq_single j (fun b _ hb => if_neg hb) (fun h => absurd hj h), if_pos rfl]
  · rw [Finset.sum_eq_zero fun b hb => if_neg fun h => hj (by rw [← h]; exact hb)]
    rw [notMem_support_iff.mp hj, derivative_zero]

/-- `∂_X` is additive. -/
theorem derivX_add (g h : R[X][Y]) : derivX (g + h) = derivX g + derivX h := by
  ext1 j; simp

/-- `∂_X` commutes with subtraction. -/
theorem derivX_sub (g h : R[X][Y]) : derivX (g - h) = derivX g - derivX h := by
  ext1 j; simp

/-- `∂_X` commutes with scalar multiplication by `R`. -/
theorem derivX_smul (c : R) (g : R[X][Y]) : derivX (c • g) = c • derivX g := by
  ext1 j; simp

/-- The Leibniz rule for `∂_X`. -/
theorem derivX_mul (g h : R[X][Y]) : derivX (g * h) = derivX g * h + g * derivX h := by
  ext1 j
  simp only [coeff_derivX, coeff_mul, coeff_add, derivative_sum, derivative_mul,
    Finset.sum_add_distrib]

/-- `∂_X` of a constant `C a` in `Y` is `C a'`. -/
@[simp]
theorem derivX_C (a : R[X]) : derivX (C a : R[X][Y]) = C (derivative a) := by
  ext1 j; simp [coeff_C]; split_ifs <;> simp

/-- `∂_X` of the outer variable `Y` vanishes. -/
@[simp]
theorem derivX_X : derivX (X : R[X][Y]) = 0 := by
  ext1 j; simp [coeff_X]; split_ifs <;> simp

/-- `∂_X` as an `R`-linear map. -/
noncomputable def derivXLinear : R[X][Y] →ₗ[R] R[X][Y] where
  toFun := derivX
  map_add' := derivX_add
  map_smul' := derivX_smul

/-- The derivation `δ_Ψ = Ψ_Y ∂_X - Ψ_X ∂_Y` along the curve `Ψ = 0`, as an `R`-linear map. -/
noncomputable def curveDeriv (Ψ : R[X][Y]) : R[X][Y] →ₗ[R] R[X][Y] :=
  LinearMap.mulLeft R (derivative Ψ) ∘ₗ derivXLinear -
    LinearMap.mulLeft R (derivX Ψ) ∘ₗ (derivative : R[X][Y] →ₗ[R[X]] R[X][Y]).restrictScalars R

/-- `δ_Ψ g = Ψ_Y · ∂_X g - Ψ_X · ∂_Y g`. -/
theorem curveDeriv_apply (Ψ g : R[X][Y]) :
    curveDeriv Ψ g = derivative Ψ * derivX g - derivX Ψ * derivative g := rfl

namespace WeightedDegreeLE

variable {w n : ℕ} {g : R[X][Y]}

/-- `∂_X` does not increase the `w`-weighted degree. -/
theorem derivX (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (derivX g) := by
  intro j hj
  rw [coeff_derivX] at hj ⊢
  have hgj : g.coeff j ≠ 0 := fun h => by simp [h] at hj
  exact (Nat.add_le_add_right (natDegree_derivative_le _) _).trans
    ((Nat.add_le_add_right (Nat.sub_le _ 1) _).trans (hg j hgj))

/-- If `Ψ` has weighted degree at most `nΨ` and `g` at most `n`, then `δ_Ψ g` has weighted
degree at most `n + nΨ`. -/
theorem curveDeriv {Ψ : R[X][Y]} {nΨ : ℕ} (hΨ : WeightedDegreeLE w nΨ Ψ)
    (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w (n + nΨ) (curveDeriv Ψ g) := by
  rw [curveDeriv_apply, add_comm n]
  exact (hΨ.derivative.mul hg.derivX).sub (hΨ.derivX.mul hg.derivative)

/-- If `Ψ` has weighted degree at most `nΨ` and `g` at most `n`, then `δ_Ψ^j g` has weighted
degree at most `n + j * nΨ`. -/
theorem iterate_curveDeriv {Ψ : R[X][Y]} {nΨ : ℕ} (hΨ : WeightedDegreeLE w nΨ Ψ)
    (hg : WeightedDegreeLE w n g) (j : ℕ) :
    WeightedDegreeLE w (n + j * nΨ) ((Polynomial.Bivariate.curveDeriv Ψ)^[j] g) := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul, ← add_assoc]
    exact WeightedDegreeLE.curveDeriv hΨ ih

end WeightedDegreeLE

end CommRing

section Branch

variable {K : Type*} [Field K]

/-- Evaluation of a bivariate polynomial along the power-series curve `s ↦ (a + s, β)`. -/
noncomputable def branchEval (a : K) (β : PowerSeries K) : K[X][Y] →+* PowerSeries K :=
  (eval₂RingHom (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom β)

/-- `branchEval a β g` is `g`, with `a + s` substituted for `X`, evaluated at `Y = β`. -/
theorem branchEval_apply (a : K) (β : PowerSeries K) (g : K[X][Y]) :
    branchEval a β g =
      (g.map (aeval (R := K)
        (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval β := by
  rw [branchEval, coe_eval₂RingHom, eval_map]

/-- Evaluation along a branch commutes with scalar multiplication by `K`. -/
theorem branchEval_smul (a : K) (β : PowerSeries K) (c : K) (g : K[X][Y]) :
    branchEval a β (c • g) = c • branchEval a β g := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  simp [branchEval, Polynomial.algebraMap_apply]

/-- The derivative of `h(a + s)` is `h'(a + s)`. -/
theorem derivative_aeval_C_add_X (a : K) (h : K[X]) :
    PowerSeries.derivative K (aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K) h) =
      aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K) (derivative h) := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, derivative_monomial, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_pow, map_add, PowerSeries.derivative_C, PowerSeries.derivative_X,
      zero_add, mul_one]
    rw [show (algebraMap K (PowerSeries K) c) = PowerSeries.C c from rfl,
      PowerSeries.derivative_C, mul_zero, add_zero, map_mul, map_natCast,
      show (algebraMap K (PowerSeries K) c) = PowerSeries.C c from rfl]
    ring

/-- **The chain rule along a branch**: the derivative of `g(a + s, β(s))` is
`g_X(a + s, β(s)) + g_Y(a + s, β(s)) β'(s)`. -/
theorem derivative_branchEval (a : K) (β : PowerSeries K) (g : K[X][Y]) :
    PowerSeries.derivative K (branchEval a β g) =
      branchEval a β (derivX g) + branchEval a β (derivative g) * PowerSeries.derivative K β := by
  induction g using Polynomial.induction_on with
  | C h =>
    simp [branchEval]
  | add g h hg hh =>
    rw [map_add, map_add, hg, hh, derivX_add, derivative_add, map_add, map_add]
    ring
  | monomial n h ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih,
      derivX_mul (C h * X ^ n), derivative_mul (f := C h * X ^ n)]
    simp [branchEval]
    ring

/-- On a branch of the curve `Ψ = 0`, the derivation `δ_Ψ` becomes `Ψ_Y · d/ds`. -/
theorem branchEval_curveDeriv {Ψ : K[X][Y]} {a : K} {β : PowerSeries K}
    (hβ : branchEval a β Ψ = 0) (g : K[X][Y]) :
    branchEval a β (curveDeriv Ψ g) =
      branchEval a β (derivative Ψ) * PowerSeries.derivative K (branchEval a β g) := by
  have h0 := derivative_branchEval a β Ψ
  rw [hβ, map_zero] at h0
  rw [curveDeriv_apply, map_sub, map_mul, map_mul, derivative_branchEval,
    eq_neg_of_add_eq_zero_left h0.symm]
  ring

/-- On a branch of the curve `Ψ = 0`, the iterates of `δ_Ψ` become the iterates of
`u · d/ds`, with `u = Ψ_Y` along the branch. -/
theorem branchEval_iterate_curveDeriv {Ψ : K[X][Y]} {a : K} {β : PowerSeries K}
    (hβ : branchEval a β Ψ = 0) (g : K[X][Y]) (j : ℕ) :
    branchEval a β ((curveDeriv Ψ)^[j] g) =
      (fun G => branchEval a β (derivative Ψ) * PowerSeries.derivative K G)^[j]
        (branchEval a β g) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', branchEval_curveDeriv hβ, ih]

end Branch

end Polynomial.Bivariate

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.PowerSeriesBranch
section








/-!
# Power series branches of a plane curve and the multiplicity zero count

Let `Ψ ∈ K[X][Y]` be monic in `Y`. At a point `(a, b)` of the curve `Ψ = 0` where `∂Ψ/∂Y` does not
vanish, Hensel's lemma in `K⟦s⟧` gives a branch: a power series `β(s)` with `β(0) = b` and
`Ψ(a + s, β(s)) = 0`. The order of vanishing of a second polynomial `g` along such branches is
controlled by the resultant: summed over finitely many branches through distinct points, the
orders of `g(a + s, β(s))` are at most the `X`-degree of `Res_Y(Ψ, g)`.

## Main results

* `Polynomial.exists_powerSeries_root_of_simple_root`: the branch through a simple point.
* `Polynomial.order_aeval_C_add_X`: the order of `r(a + s)` is the multiplicity of the root `a`.
* `Polynomial.sum_order_le_rootMultiplicity_resultant`: the branches over one value of `X`.
* `Polynomial.sum_order_le_natDegree_resultant`: the multiplicity zero count.
-/


open Polynomial


namespace Polynomial

variable {K : Type*} [Field K]

/-- The constant coefficient of `r(a + s)` is `r(a)`, as an equality of ring homomorphisms. -/
private theorem constantCoeff_comp_aeval_C_add_X (a : K) :
    PowerSeries.constantCoeff.comp
      (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom =
      evalRingHom a := by
  ext <;> simp

/-- The constant coefficient of `Ψ(a + s, β(s))` is `Ψ(a, β(0))`. -/
theorem constantCoeff_eval_map_aeval_C_add_X (Ψ : K[X][X]) (a : K) (β : PowerSeries K) :
    PowerSeries.constantCoeff
        ((Ψ.map (aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval β) =
      Ψ.evalEval a (PowerSeries.constantCoeff β) := by
  rw [eval_map, hom_eval₂, constantCoeff_comp_aeval_C_add_X, eval₂_evalRingHom]

/-- **Hensel's lemma along a branch.** If `b` is a simple root of `Ψ(a, Y)` for `Ψ ∈ K[X][Y]`
monic in `Y`, then there is a power series `β(s)` with `β(0) = b` and `Ψ(a + s, β(s)) = 0`. -/
theorem exists_powerSeries_root_of_simple_root {Ψ : K[X][X]} (hΨ : Ψ.Monic) {a b : K}
    (h0 : Ψ.evalEval a b = 0) (h1 : (derivative Ψ).evalEval a b ≠ 0) :
    ∃ β : PowerSeries K, PowerSeries.constantCoeff β = b ∧
      (Ψ.map (aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval β = 0 := by
  set φ := (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom
  have hmon : (Ψ.map φ).Monic := hΨ.map φ
  have hc : ∀ f : K[X][X], PowerSeries.constantCoeff ((f.map φ).eval (PowerSeries.C b)) =
      f.evalEval a b := fun f => by
    rw [constantCoeff_eval_map_aeval_C_add_X]; simp
  have hmem : (Ψ.map φ).eval (PowerSeries.C b) ∈ Ideal.span {PowerSeries.X} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, hc, h0]
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {PowerSeries.X})
      ((Ψ.map φ).derivative.eval (PowerSeries.C b))) := by
    refine IsUnit.map _ ?_
    rw [PowerSeries.isUnit_iff_constantCoeff, derivative_map, hc]
    exact h1.isUnit
  obtain ⟨β, hβ, hβb⟩ := HenselianRing.is_henselian (I := Ideal.span {PowerSeries.X})
    (Ψ.map φ) hmon (PowerSeries.C b) hmem hunit
  refine ⟨β, ?_, hβ⟩
  rwa [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C,
    sub_eq_zero] at hβb

end Polynomial

namespace Polynomial

variable {K : Type*} [Field K]

/-- The order at `s = 0` of `r(a + s)` is the multiplicity of `a` as a root of `r`. -/
theorem order_aeval_C_add_X {r : K[X]} (hr : r ≠ 0) (a : K) :
    (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K) r).order =
      r.rootMultiplicity a := by
  obtain ⟨q, hq, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr a
  have hq0 : q.eval a ≠ 0 := fun h => hdvd (dvd_iff_isRoot.mpr h)
  conv_lhs => rw [hq]
  rw [map_mul, map_pow, PowerSeries.order_mul, map_sub, aeval_X, aeval_C,
    show (PowerSeries.C a + PowerSeries.X : PowerSeries K) -
      algebraMap K (PowerSeries K) a = PowerSeries.X by simp,
    PowerSeries.order_X_pow, PowerSeries.order_zero_of_unit, add_zero]
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h : PowerSeries.constantCoeff (aeval (R := K)
      (PowerSeries.C a + PowerSeries.X : PowerSeries K) q) = q.eval a :=
    RingHom.congr_fun (constantCoeff_comp_aeval_C_add_X a) q
  rw [h]; exact hq0.isUnit

/-- The multiplicities of finitely many roots of a nonzero polynomial add up to at most its
degree. -/
theorem sum_rootMultiplicity_le_natDegree {p : K[X]} (hp : p ≠ 0) (A : Finset K) :
    ∑ a ∈ A, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  calc ∑ a ∈ A, p.rootMultiplicity a = ∑ a ∈ A, p.roots.count a := by simp [count_roots]
    _ ≤ ∑ a ∈ A ∪ p.roots.toFinset, p.roots.count a :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ a ∈ p.roots.toFinset, p.roots.count a := by
        refine (Finset.sum_subset Finset.subset_union_right fun a _ ha => ?_).symm
        exact Multiset.count_eq_zero.mpr (by simpa using ha)
    _ = Multiset.card p.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ p.natDegree := card_roots' p

end Polynomial

namespace Polynomial

variable {K : Type*} [Field K]

/-- **The branches over one point.** Fix `a`. If the power series `β t` for `t ∈ T` are pairwise
distinct roots of `Ψ(a + s, Y)`, then the orders of `g(a + s, β t)` add up to at most the
multiplicity of `a` as a root of `Res_Y(Ψ, g)`. -/
theorem sum_order_le_rootMultiplicity_resultant {Ψ g : K[X][X]} (hΨ : Ψ.Monic)
    (hres : resultant Ψ g ≠ 0) (a : K) (T : Finset (PowerSeries K))
    (hT : ∀ t ∈ T,
      (Ψ.map (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval t
        = 0) :
    ∑ t ∈ T, ((g.map (aeval (R := K)
      (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval t).order ≤
        ((resultant Ψ g).rootMultiplicity a : ℕ∞) := by
  classical
  set φ := (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom
  set Ψa := Ψ.map φ
  set ga := g.map φ
  have hΨa : Ψa.Monic := hΨ.map φ
  have hΨa0 : Ψa ≠ 0 := hΨa.ne_zero
  have hle : T.val ≤ Ψa.roots :=
    (Multiset.le_iff_subset T.nodup).mpr fun t ht =>
      (mem_roots hΨa0).mpr (hT t (Finset.mem_def.mpr ht))
  obtain ⟨H, hH⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hΨa0 T.val).mpr hle
  set Pr : (PowerSeries K)[X] := ∏ t ∈ T, (X - C t)
  have hPr : (T.val.map fun t => X - C t).prod = Pr := rfl
  rw [hPr] at hH
  have hPrm : Pr.Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hHm : H.Monic := hPrm.of_mul_monic_left (hH ▸ hΨa)
  have hdeg : Ψ.natDegree = Pr.natDegree + H.natDegree := by
    rw [← hΨ.natDegree_map φ, ← hPrm.natDegree_mul hHm, ← hH]
  have hga : ga.natDegree ≤ g.natDegree := natDegree_map_le
  have hφres : φ (resultant Ψ g) =
      (∏ t ∈ T, ga.eval t) * resultant H ga H.natDegree g.natDegree := by
    rw [resultant, ← resultant, ← resultant_map_map, hdeg]
    show Ψa.resultant ga _ _ = _
    rw [hH, resultant_mul_left _ _ _ _ hga,
      resultant_prod_left _ _ _ _ (by simp [leadingCoeff_X_sub_C]) hga]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [natDegree_X_sub_C, ← pow_one (X - C t), resultant_X_sub_C_pow_left _ _ _ _ hga, pow_one]
  have hord := order_aeval_C_add_X hres a
  rw [← hord]
  show _ ≤ (φ (resultant Ψ g)).order
  rw [hφres, PowerSeries.order_mul, PowerSeries.order_prod]
  exact le_self_add

/-- **The multiplicity zero count.** Let `Ψ ∈ K[X][Y]` be monic in `Y`, and let `S` be a finite set
of points `P = (P.1, P.2)` together with power series branches `β P` through them, i.e. roots of
`Ψ(P.1 + s, Y)` with `β P (0) = P.2`. Then the orders of vanishing of `g(P.1 + s, β P(s))` add up
to at most the `X`-degree of the resultant `Res_Y(Ψ, g)`, provided it is nonzero. -/
theorem sum_order_le_natDegree_resultant {Ψ g : K[X][X]} (hΨ : Ψ.Monic)
    (S : Finset (K × K)) (β : K × K → PowerSeries K)
    (hβ : ∀ P ∈ S, PowerSeries.constantCoeff (β P) = P.2 ∧
      (Ψ.map (aeval (PowerSeries.C P.1 + PowerSeries.X : PowerSeries K)).toRingHom).eval (β P) = 0)
    (hres : resultant Ψ g ≠ 0) :
    ∑ P ∈ S, ((g.map (aeval (PowerSeries.C P.1 + PowerSeries.X : PowerSeries K)).toRingHom).eval
      (β P)).order ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
  classical
  set A := S.image Prod.fst
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := A)
    (fun P hP => Finset.mem_image_of_mem _ hP)]
  calc ∑ a ∈ A, ∑ P ∈ S with P.1 = a,
        ((g.map (aeval (PowerSeries.C P.1 + PowerSeries.X : PowerSeries K)).toRingHom).eval
          (β P)).order
      ≤ ∑ a ∈ A, ((resultant Ψ g).rootMultiplicity a : ℕ∞) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hinj : Set.InjOn β (S.filter fun P => P.1 = a) := by
          intro P hP P' hP' h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hP hP'
          have h2 : P.2 = P'.2 := by rw [← (hβ P hP.1).1, ← (hβ P' hP'.1).1, h]
          exact Prod.ext (hP.2.trans hP'.2.symm) h2
        rw [Finset.sum_congr rfl (g := fun P => ((g.map (aeval (R := K)
          (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval (β P)).order)
          (fun P hP => by rw [(Finset.mem_filter.mp hP).2]),
          ← Finset.sum_image (f := fun t => ((g.map (aeval (R := K)
            (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval t).order) hinj]
        refine sum_order_le_rootMultiplicity_resultant hΨ hres a _ fun t ht => ?_
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨hPS, rfl⟩ := Finset.mem_filter.mp hP
        exact (hβ P hPS).2
    _ = ((∑ a ∈ A, (resultant Ψ g).rootMultiplicity a : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
        exact_mod_cast sum_rootMultiplicity_le_natDegree hres A

end Polynomial

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.ResultantWeightedDegree
section


/-!
# A weighted degree bound for the resultant

For `Ψ, g ∈ R[X][Y]`, give `Y` the weight `w`. If every monomial of `Ψ` has weighted degree at most
`w · deg_Y Ψ` and every monomial of `g` has weighted degree at most `n`, then the resultant
`Res_Y(Ψ, g) ∈ R[X]` has degree at most `deg_Y Ψ · n`. The proof bounds the degree of each entry of
the Sylvester matrix by a row weight plus a column weight, and the determinant by their sums.

## Main results

* `Polynomial.natDegree_det_le_of_natDegree_le_add`: if the entries of a matrix of polynomials
  satisfy `deg M i j ≤ a i + b j`, the determinant has degree at most `∑ a + ∑ b`.
* `Polynomial.natDegree_resultant_le_of_weightedDegree_le`: the weighted degree bound.
-/


open Polynomial


namespace Polynomial

/-- If every nonzero entry `M i j` of a square matrix of polynomials has degree at most
`a i + b j`, then the determinant has degree at most `∑ i, a i + ∑ j, b j`. -/
theorem natDegree_det_le_of_natDegree_le_add {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R[X]) (a b : ι → ℤ)
    (hM : ∀ i j, M i j ≠ 0 → ((M i j).natDegree : ℤ) ≤ a i + b j) :
    M.det.natDegree ≤ (∑ i, a i + ∑ j, b j).toNat := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => (natDegree_smul_le _ _).trans ?_
  by_cases h0 : ∃ i, M (σ i) i = 0
  · obtain ⟨i, hi⟩ := h0
    have h : ∏ i, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [h, natDegree_zero]
    exact Nat.zero_le _
  push Not at h0
  refine (natDegree_prod_le _ _).trans ?_
  have hsum : ((∑ i, (M (σ i) i).natDegree : ℕ) : ℤ) ≤ ∑ i, a i + ∑ j, b j := by
    push_cast
    calc ∑ i, ((M (σ i) i).natDegree : ℤ) ≤ ∑ i, (a (σ i) + b i) :=
          Finset.sum_le_sum fun i _ => hM _ _ (h0 i)
      _ = ∑ i, a i + ∑ j, b j := by
          rw [Finset.sum_add_distrib, Equiv.sum_comp σ a]
  omega

end Polynomial

namespace Polynomial

/-- **Weighted degree bound for the resultant.** Let `Ψ, g ∈ R[X][Y]`. If the coefficient of `Yⁱ`
in `Ψ` has `X`-degree at most `w (deg_Y Ψ - i)` and that of `Yʲ` in `g` has `X`-degree at most
`n - w j`, then `Res_Y(Ψ, g)` has `X`-degree at most `deg_Y Ψ * n`. -/
theorem natDegree_resultant_le_of_weightedDegree_le {R : Type*} [CommRing R] {Ψ g : R[X][X]}
    (hΨ : Ψ.Monic) {w n : ℕ}
    (hΨw : ∀ i, Ψ.coeff i ≠ 0 → (Ψ.coeff i).natDegree + w * i ≤ w * Ψ.natDegree)
    (hgw : ∀ j, g.coeff j ≠ 0 → (g.coeff j).natDegree + w * j ≤ n) :
    (resultant Ψ g).natDegree ≤ Ψ.natDegree * n := by
  classical
  set m := Ψ.natDegree
  set k := g.natDegree
  let a : Fin (m + k) → ℤ := fun i => -((w : ℤ) * (i : ℕ))
  let b : Fin (m + k) → ℤ := fun j => j.addCases (fun j₁ => (n : ℤ) + w * (j₁ : ℕ))
    (fun j₁ => (w : ℤ) * m + w * (j₁ : ℕ))
  have hbound := natDegree_det_le_of_natDegree_le_add (sylvester Ψ g m k) a b ?_
  · refine hbound.trans (le_of_eq ?_)
    have hsum : ∑ i, a i + ∑ j, b j = ((m * n : ℕ) : ℤ) := by
      simp [a, b, Fin.sum_univ_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [hsum]; exact Int.toNat_natCast _
  · have key : ∀ (p : R[X][X]) (c d : ℕ), (∀ j, p.coeff j ≠ 0 → (p.coeff j).natDegree + w * j ≤ c) →
        ∀ i j : ℕ, (if i ∈ Set.Icc j (j + d) then p.coeff (i - j) else 0) ≠ 0 →
          ((if i ∈ Set.Icc j (j + d) then p.coeff (i - j) else 0).natDegree : ℤ) ≤
            -(w * i) + (c + w * j) := by
      intro p c d hp i j hij
      split_ifs at hij ⊢ with hi
      · have h' := hp _ hij
        zify [hi.1] at h'
        linarith
      · exact absurd rfl hij
    intro i j hij
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, b, a] at hij ⊢
      exact key g n k hgw _ _ hij
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, b, a] at hij ⊢
      exact key Ψ (w * m) m hΨw _ _ hij

end Polynomial

end

-- Bundled module: StacksFrontier.RingTheory.PowerSeries.OrderOfDerivative
section



/-!
# Vanishing order from iterated derivatives

Let `K` be a field and `u ∈ K⟦X⟧` a power series with nonzero constant term. Write
`D F = u · F'` for the twisted derivative. If `k` is such that `1, …, k - 1` are nonzero in `K`
(for instance `k ≤ p` in characteristic `p`), and the constant terms of `F, D F, …, D^{k-1} F` all
vanish, then `F` has order at least `k`. This is the form in which Stepanov's method uses
derivatives along a plane curve: at a smooth point the derivation `Ψ_Y ∂_X - Ψ_X ∂_Y` becomes
`u · d/ds` on the branch, with `u` the value of `Ψ_Y` there.

## Main results

* `PowerSeries.order_mul_derivative_eq`: `D` lowers an order `t + 1` to `t` when `t + 1 ≠ 0`.
* `PowerSeries.nat_le_order_of_constantCoeff_iterate_eq_zero`: the vanishing criterion.
-/


namespace PowerSeries

variable {K : Type*} [Field K]

/-- If `F` has order `t + 1` and `t + 1 ≠ 0` in `K`, then `u * F'` has order `t` for any `u`
with nonzero constant term. -/
theorem order_mul_derivative_eq {u F : K⟦X⟧} (hu : constantCoeff u ≠ 0) {t : ℕ}
    (hF : F.order = (t + 1 : ℕ)) (ht : ((t + 1 : ℕ) : K) ≠ 0) :
    (u * d⁄dX K F).order = t := by
  have hu0 : u.order = 0 := by
    by_contra h
    exact hu (order_ne_zero_iff_constCoeff_eq_zero.mp h)
  rw [order_mul, hu0, zero_add, order_eq_nat]
  obtain ⟨h1, h2⟩ := order_eq_nat.mp hF
  refine ⟨?_, fun i hi => ?_⟩
  · rw [coeff_derivative]
    exact mul_ne_zero h1 (by exact_mod_cast ht)
  · rw [coeff_derivative, h2 (i + 1) (by omega), zero_mul]

/-- **Vanishing order from iterated twisted derivatives.** Let `u` have nonzero constant term and
let `D F = u * F'`. If `1, …, k - 1` are nonzero in `K` and the constant terms of
`F, D F, …, D^{k-1} F` vanish, then `F` has order at least `k`. -/
theorem nat_le_order_of_constantCoeff_iterate_eq_zero {u : K⟦X⟧} (hu : constantCoeff u ≠ 0)
    (F : K⟦X⟧) {k : ℕ} (hk : ∀ t : ℕ, 0 < t → t < k → (t : K) ≠ 0)
    (h : ∀ j < k, constantCoeff ((fun G => u * d⁄dX K G)^[j] F) = 0) :
    (k : ℕ∞) ≤ F.order := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ : ∃ r : ℕ, F.order = r := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt) |>.imp
    fun _ h => h.symm
  have hrk : r < k := by exact_mod_cast hr ▸ hlt
  have key : ∀ i ≤ r, ((fun G => u * d⁄dX K G)^[i] F).order = (r - i : ℕ) := by
    intro i hi
    induction i with
    | zero => simpa using hr
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have h' := ih (by omega)
      rw [show r - i = (r - (i + 1)) + 1 by omega] at h'
      exact order_mul_derivative_eq hu h' (hk _ (by omega) (by omega))
  have h0 := key r le_rfl
  rw [Nat.sub_self, Nat.cast_zero] at h0
  exact (order_ne_zero_iff_constCoeff_eq_zero.mpr (h r hrk)) h0

end PowerSeries

end

-- Bundled module: StacksFrontier.RingTheory.PowerSeries.FrobeniusIndependence
section





/-!
# Independence of Frobenius powers over a space of small vanishing order

Let `K` be a perfect field of characteristic `p`, let `σ = p ^ a`, and let `U ⊆ K⟦X⟧` be a
finite-dimensional subspace all of whose nonzero elements have order `< σ`. If
`y₁, …, yₙ ∈ K⟦X⟧` are linearly independent over `K`, then

  `u₁ y₁ ^ σ + ⋯ + uₙ yₙ ^ σ = 0` with `uᵢ ∈ U` forces `u₁ = ⋯ = uₙ = 0`.

This is the independence lemma at the heart of Bombieri's version of Stepanov's method: choosing
a basis of `U` with distinct orders, the terms of the sum have orders in distinct residue classes
modulo `σ`, so they cannot cancel. We prove it by induction on `dim U`, splitting off an element
of minimal order and keeping track of the residue modulo `σ` of the order of a nonzero sum.

## Main results

* `PowerSeries.eq_zero_of_sum_mul_pow_eq_zero`: the independence lemma.
-/


namespace PowerSeries

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

private lemma eq_of_add_mul_eq {σ o₁ o₂ t₁ t₂ : ℕ} (h₁ : o₁ < σ) (h₂ : o₂ < σ)
    (h : o₁ + σ * t₁ = o₂ + σ * t₂) : o₁ = o₂ := by
  have := congrArg (· % σ) h
  simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] using this

private lemma aux (a : ℕ) {ι : Type*} [Fintype ι] {y : ι → K⟦X⟧} (hy : LinearIndependent K y) :
    ∀ (n : ℕ) (U : Submodule K K⟦X⟧) [FiniteDimensional K U], Module.finrank K U = n →
      (∀ u ∈ U, u ≠ 0 → u.order < (p ^ a : ℕ)) →
      ∀ u : ι → K⟦X⟧, (∀ i, u i ∈ U) →
        ((∑ i, u i * y i ^ p ^ a = 0) → ∀ i, u i = 0) ∧
        (∑ i, u i * y i ^ p ^ a ≠ 0 → ∃ v ∈ U, v ≠ 0 ∧
          ∃ N : ℕ, (∑ i, u i * y i ^ p ^ a).order = (v.order.toNat + p ^ a * N : ℕ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U _ hn hU u hu
  set σ := p ^ a
  by_cases hbot : U = ⊥
  · have h0 : ∀ i, u i = 0 := fun i => by simpa [hbot] using hu i
    simp [h0]
  -- an element `e` of `U` of minimal order `o₀`
  have hex : ∃ o : ℕ, ∃ u ∈ U, u ≠ 0 ∧ u.order = o := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    exact ⟨v.order.toNat, v, hv, hv0, (ENat.coe_toNat (order_eq_top.not.mpr hv0)).symm⟩
  classical
  set o₀ := Nat.find hex
  obtain ⟨e, he, he0, heo⟩ := Nat.find_spec hex
  have hmin : ∀ v ∈ U, v ≠ 0 → (o₀ : ℕ∞) ≤ v.order := by
    intro v hv hv0
    have hfin : v.order ≠ ⊤ := order_eq_top.not.mpr hv0
    rw [← ENat.coe_toNat hfin]
    exact_mod_cast Nat.find_min' hex ⟨v, hv, hv0, (ENat.coe_toNat hfin).symm⟩
  have hγ : coeff o₀ e ≠ 0 := by
    have := coeff_order he0
    rwa [heo, ENat.toNat_coe] at this
  -- the subspace `U'` of elements of `U` whose coefficient of index `o₀` vanishes
  set U' : Submodule K K⟦X⟧ := U ⊓ LinearMap.ker (coeff o₀)
  have hU'le : U' ≤ U := inf_le_left
  have hU'lt : U' < U := lt_of_le_of_ne hU'le fun h => by
    have : e ∈ U' := h ▸ he
    exact hγ (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have : FiniteDimensional K U' := Submodule.finiteDimensional_of_le hU'le
  have hrank : Module.finrank K U' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hU'lt
  have hU' : ∀ v ∈ U', v ≠ 0 → v.order < (σ : ℕ) := fun v hv hv0 => hU v (hU'le hv) hv0
  have hU'o : ∀ v ∈ U', v ≠ 0 → (o₀ : ℕ∞) < v.order := by
    intro v hv hv0
    refine lt_of_le_of_ne (hmin v (hU'le hv) hv0) fun h => ?_
    have hc := coeff_order hv0
    rw [← h, ENat.toNat_coe] at hc
    exact hc (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hv).2)
  -- decompose `u i = c i • e + u' i`
  set c : ι → K := fun i => coeff o₀ (u i) / coeff o₀ e
  set u' : ι → K⟦X⟧ := fun i => u i - c i • e
  have hu' : ∀ i, u' i ∈ U' := by
    intro i
    refine Submodule.mem_inf.mpr ⟨U.sub_mem (hu i) (U.smul_mem _ he), ?_⟩
    simp [u', c, LinearMap.mem_ker, div_mul_cancel₀ _ hγ]
  obtain ⟨ih1, ih2⟩ := ih _ hrank U' rfl hU' u' hu'
  have : CharP K⟦X⟧ p := charP_of_injective_algebraMap (algebraMap K K⟦X⟧).injective p
  set fr := iterateFrobeniusEquiv K p a
  set z : K⟦X⟧ := ∑ i, fr.symm (c i) • y i
  have hzpow : z ^ σ = ∑ i, c i • y i ^ σ := by
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow]
    congr 1
    have := fr.apply_symm_apply (c i)
    rwa [iterateFrobeniusEquiv_def] at this
  have hsplit : ∑ i, u i * y i ^ σ = e * z ^ σ + ∑ i, u' i * y i ^ σ := by
    rw [hzpow, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u', sub_mul, smul_mul_assoc, mul_smul_comm]
    abel
  by_cases hz : z = 0
  · -- all `c i` vanish, so `u = u'`
    have hc0 : ∀ i, c i = 0 := by
      intro i
      have := (Fintype.linearIndependent_iff.mp hy) (fun i => fr.symm (c i)) hz i
      simpa using this
    have huu : ∀ i, u' i = u i := fun i => by simp [u', hc0 i]
    simp only [huu] at ih1 ih2
    refine ⟨ih1, fun hne => ?_⟩
    obtain ⟨v, hv, hv0, N, hN⟩ := ih2 hne
    exact ⟨v, hU'le hv, hv0, N, hN⟩
  · -- the term `e * z ^ σ` has order `o₀ + σ * ord z`
    have hzfin : z.order ≠ ⊤ := order_eq_top.not.mpr hz
    set t := z.order.toNat
    have hA : (e * z ^ σ).order = (o₀ + σ * t : ℕ) := by
      rw [order_mul, order_pow, heo, ← ENat.coe_toNat hzfin, nsmul_eq_mul]
      push_cast; ring
    have key : ∃ v ∈ U, v ≠ 0 ∧ ∃ N : ℕ,
        (∑ i, u i * y i ^ σ).order = (v.order.toNat + σ * N : ℕ) := by
      rw [hsplit]
      have heord : e.order.toNat = o₀ := by rw [heo, ENat.toNat_coe]
      by_cases hB : ∑ i, u' i * y i ^ σ = 0
      · exact ⟨e, he, he0, t, by rw [hB, add_zero, hA, heord]⟩
      · obtain ⟨v, hv, hv0, N, hN⟩ := ih2 hB
        have hvfin : v.order ≠ ⊤ := order_eq_top.not.mpr hv0
        have hvlt : v.order.toNat < σ := by
          have := hU' v hv hv0
          rw [← ENat.coe_toNat hvfin] at this
          exact_mod_cast this
        have hvgt : o₀ < v.order.toNat := by
          have := hU'o v hv hv0
          rw [← ENat.coe_toNat hvfin] at this
          exact_mod_cast this
        have ho₀σ : o₀ < σ := hvgt.trans hvlt
        have hne : (e * z ^ σ).order ≠ (∑ i, u' i * y i ^ σ).order := by
          rw [hA, hN]
          intro h
          have := eq_of_add_mul_eq ho₀σ hvlt (by exact_mod_cast h)
          omega
        rw [order_add_of_order_ne _ _ hne]
        rcases le_total (e * z ^ σ).order (∑ i, u' i * y i ^ σ).order with hle | hle
        · exact ⟨e, he, he0, t, by rw [min_eq_left hle, hA, heord]⟩
        · exact ⟨v, hU'le hv, hv0, N, by rw [min_eq_right hle, hN]⟩
    refine ⟨fun h0 => ?_, fun _ => key⟩
    obtain ⟨v, -, -, N, hN⟩ := key
    rw [h0, order_zero] at hN
    exact absurd hN (ENat.top_ne_coe _)

/-- **Independence of Frobenius powers.** Let `K` be a perfect field of characteristic `p`, let
`U ⊆ K⟦X⟧` be a finite-dimensional subspace whose nonzero elements have order `< p ^ a`, and let
`y : ι → K⟦X⟧` be linearly independent over `K`. If `∑ uᵢ yᵢ ^ (p ^ a) = 0` with all `uᵢ ∈ U`,
then every `uᵢ` vanishes. -/
theorem eq_zero_of_sum_mul_pow_eq_zero (a : ℕ) (U : Submodule K K⟦X⟧) [FiniteDimensional K U]
    (hU : ∀ u ∈ U, u ≠ 0 → u.order < (p ^ a : ℕ)) {ι : Type*} [Fintype ι] {y : ι → K⟦X⟧}
    (hy : LinearIndependent K y) {u : ι → K⟦X⟧} (hu : ∀ i, u i ∈ U)
    (h : ∑ i, u i * y i ^ p ^ a = 0) (i : ι) : u i = 0 :=
  (aux p a hy _ U rfl hU u hu).1 h i

end PowerSeries

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.StepanovUpperBound
section








/-!
# Stepanov's upper bound for the points of a plane curve

Let `K` be an algebraically closed field of characteristic `p`, `q = p ^ e`, and let `Ψ ∈ K[X][Y]`
be monic and irreducible of `Y`-degree `m` with `∂Ψ/∂Y ≠ 0`. Let `R, D ∈ K[X][Y]` describe a
(possibly twisted) Frobenius: consider the points `P = (a, b)` of `Ψ = 0` with
`∂Ψ/∂Y (P) ≠ 0`, `a ^ q = a`, `D(P) ≠ 0` and `D(P) b ^ q = R(P)`. For `R = Y` and `D = 1` these
are the smooth `𝔽_q`-points of the curve. Stepanov's method, in the form combining Bombieri's
`ρ`-th powers (`ρ = p ^ ⌊e/2⌋`) with derivatives of order `< p` along the curve, bounds the number
of such points by `q + O(√q)`, the implied constant depending only on `m`, the weight `w` of `Ψ`
and the degrees of `R` and `D`.

## Main results

* `Polynomial.Bivariate.le_order_branchEval_sum_mul_pow`: the auxiliary function vanishes to
  order `k` at each point.
-/


open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- If the power series `β` has constant coefficient `b`, then the constant coefficient of
`branchEval a β g` is the value `g(a, b)`. -/
theorem constantCoeff_branchEval {a b : K} {β : PowerSeries K}
    (hβ0 : PowerSeries.constantCoeff β = b) (g : K[X][Y]) :
    PowerSeries.constantCoeff (branchEval a β g) = g.evalEval a b := by
  rw [branchEval_apply, constantCoeff_eval_map_aeval_C_add_X, hβ0]

/-- The twisted derivative `G ↦ u * G'` as a `K`-linear map. -/
noncomputable def twistedDerivative (u : PowerSeries K) : PowerSeries K →ₗ[K] PowerSeries K :=
  LinearMap.mulLeft K u ∘ₗ (PowerSeries.derivative K).toLinearMap

/-- The `j`-th iterate of `G ↦ u * G'` is the `j`-th power of `twistedDerivative u`. -/
theorem iterate_twistedDerivative (u : PowerSeries K) (j : ℕ) (G : PowerSeries K) :
    (fun G => u * PowerSeries.derivative K G)^[j] G = (twistedDerivative u ^ j) G := by
  rw [Module.End.pow_apply]; rfl

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The inverse of the `e`-fold Frobenius is a `p ^ e`-th root. -/
private theorem pow_iterateFrobeniusEquiv_symm (e : ℕ) (x : K) :
    ((iterateFrobeniusEquiv K p e).symm x) ^ p ^ e = x := by
  have := (iterateFrobeniusEquiv K p e).apply_symm_apply x
  rwa [iterateFrobeniusEquiv_def] at this

/-- **The auxiliary function vanishes to order `k`.** Let `(a₀, b₀)` be a point of `Ψ = 0` with
`∂Ψ/∂Y ≠ 0` there, and `β` the branch through it. Let `q = p ^ (a + b)`, `ρ = p ^ a`,
`σ = p ^ b`, and suppose `F i (P) = λ · W i (P) ^ q` with `λ ≠ 0`. If for every `j < k`
(`k ≤ p`, `k ρ ≤ q`) the combination `∑ (δ_Ψ ^ j v i) ^ ρ F i` vanishes at `P`, then
`∑ v i · W i ^ σ` vanishes to order at least `k` along the branch. -/
theorem le_order_branchEval_sum_mul_pow {Ψ : K[X][Y]} {a₀ b₀ : K} {β : PowerSeries K}
    (hβ0 : PowerSeries.constantCoeff β = b₀) (hβ : branchEval a₀ β Ψ = 0)
    (hP : (derivative Ψ).evalEval a₀ b₀ ≠ 0) {ι : Type*} [Fintype ι] (v W F : ι → K[X][Y])
    {a b k : ℕ} (hk : k ≤ p) (hkq : k * p ^ a ≤ p ^ (a + b)) {lam : K} (hlam : lam ≠ 0)
    (hF : ∀ i, (F i).evalEval a₀ b₀ = lam * (W i).evalEval a₀ b₀ ^ p ^ (a + b))
    (hE : ∀ j < k, (∑ i, ((curveDeriv Ψ)^[j] (v i)) ^ p ^ a * F i).evalEval a₀ b₀ = 0) :
    (k : ℕ∞) ≤ (branchEval a₀ β (∑ i, v i * W i ^ p ^ b)).order := by
  classical
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  set ι₀ := branchEval a₀ β
  set ρ := p ^ a
  set q := p ^ (a + b)
  have hρ0 : 0 < ρ := pow_pos (Fact.out : p.Prime).pos a
  have hq : q = p ^ b * ρ := by simp only [q, ρ, pow_add, mul_comm]
  have hconst : ∀ g, PowerSeries.constantCoeff (ι₀ g) = g.evalEval a₀ b₀ :=
    constantCoeff_branchEval hβ0
  set fr := iterateFrobeniusEquiv K p a
  have hfr : ∀ x : K, (fr.symm x) ^ ρ = x := pow_iterateFrobeniusEquiv_symm p a
  set c : ι → K := fun i => (W i).evalEval a₀ b₀ ^ q
  set γ : ι → K := fun i => fr.symm (c i)
  set G : PowerSeries K := ∑ i, γ i • ι₀ (v i)
  -- `(ι₀ g) ^ ρ = ∑ ι₀ (v i) ^ ρ * ι₀ (W i) ^ q`
  have h1 : (ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ = ∑ i, ι₀ (v i) ^ ρ * ι₀ (W i) ^ q := by
    rw [← map_pow, sum_pow_char_pow, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, map_mul, map_pow, map_pow, hq, mul_comm (p ^ b)]
  -- `G ^ ρ = ∑ ι₀ (v i) ^ ρ * C (c i)`
  have h3 : G ^ ρ = ∑ i, ι₀ (v i) ^ ρ * PowerSeries.C (c i) := by
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.smul_pow, hfr, PowerSeries.smul_eq_C_mul, mul_comm]
  -- the difference has order at least `q`
  have hdiff : (q : ℕ∞) ≤ ((ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ - G ^ ρ).order := by
    rw [h1, h3, ← Finset.sum_sub_distrib]
    refine PowerSeries.nat_le_order _ _ fun d hd => ?_
    have hdvd : (PowerSeries.X : PowerSeries K) ^ q ∣
        ∑ i, (ι₀ (v i) ^ ρ * ι₀ (W i) ^ q - ι₀ (v i) ^ ρ * PowerSeries.C (c i)) := by
      refine Finset.dvd_sum fun i _ => ?_
      rw [← mul_sub]
      refine Dvd.dvd.mul_left ?_ _
      have hX : (PowerSeries.X : PowerSeries K) ∣ ι₀ (W i) - PowerSeries.C ((W i).evalEval a₀ b₀) :=
        PowerSeries.X_dvd_iff.mpr (by simp [hconst])
      rw [show PowerSeries.C (c i) = (PowerSeries.C ((W i).evalEval a₀ b₀)) ^ q by
        simp [c, map_pow], ← sub_pow_char_pow]
      exact pow_dvd_pow_of_dvd hX q
    exact PowerSeries.X_pow_dvd_iff.mp hdvd d hd
  -- `G` vanishes to order `k`
  have hG : (k : ℕ∞) ≤ G.order := by
    refine PowerSeries.nat_le_order_of_constantCoeff_iterate_eq_zero
      (u := ι₀ (derivative Ψ)) (by rw [hconst]; exact hP) G (fun t ht htk => ?_) fun j hj => ?_
    · intro h0
      rw [CharP.cast_eq_zero_iff K p] at h0
      exact absurd (Nat.le_of_dvd ht h0) (by omega)
    · have hit : (fun G => ι₀ (derivative Ψ) * PowerSeries.derivative K G)^[j] G =
          ∑ i, γ i • ι₀ ((curveDeriv Ψ)^[j] (v i)) := by
        rw [iterate_twistedDerivative, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← iterate_twistedDerivative, ← branchEval_iterate_curveDeriv hβ]
      rw [hit, map_sum]
      simp only [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.constantCoeff_C, hconst]
      set s := ∑ i, γ i * ((curveDeriv Ψ)^[j] (v i)).evalEval a₀ b₀
      have hs : lam * s ^ ρ = 0 := by
        rw [sum_pow_char_pow, Finset.mul_sum]
        have := hE j hj
        simp only [evalEval_finsetSum, evalEval_mul, evalEval_pow, hF] at this
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, hfr]
        ring
      exact pow_eq_zero_iff (n := ρ) hρ0.ne' |>.mp
        ((mul_eq_zero.mp hs).resolve_left hlam)
  -- conclude
  have hGρ : ((k * ρ : ℕ) : ℕ∞) ≤ (G ^ ρ).order := by
    rw [PowerSeries.order_pow, nsmul_eq_mul, mul_comm]
    push_cast
    exact mul_le_mul_right hG _
  have hsum : ((k * ρ : ℕ) : ℕ∞) ≤ ((ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ).order := by
    have := PowerSeries.min_order_le_order_add (G ^ ρ)
      ((ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ - G ^ ρ)
    rw [add_sub_cancel] at this
    refine le_trans (le_min hGρ (le_trans (by exact_mod_cast hkq) hdiff)) this
  rw [PowerSeries.order_pow, nsmul_eq_mul] at hsum
  generalize (ι₀ (∑ i, v i * W i ^ p ^ b)).order = o at hsum ⊢
  cases o with
  | top => exact le_top
  | coe n =>
    have : k * ρ ≤ ρ * n := by exact_mod_cast hsum
    exact_mod_cast Nat.le_of_mul_le_mul_left (by linarith) hρ0


section Auxiliary

/-- Elements of the span of monomials `Xⁱ Yʲ` with `j < m` and `i + w j ≤ n` have `Y`-degree
`< m` and weighted degree `≤ n`. -/
theorem degree_lt_and_weightedDegreeLE_of_mem_span {ι : Type*} {f : ι → ℕ × ℕ} {m w n : ℕ}
    (hf : ∀ i, (f i).2 < m ∧ (f i).1 + w * (f i).2 ≤ n) {h : K[X][Y]}
    (hh : h ∈ Submodule.span K (Set.range fun i => (monomialXY (f i) : K[X][Y]))) :
    h.degree < m ∧ WeightedDegreeLE w n h := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨?_, WeightedDegreeLE.monomialXY (hf i).2⟩
    simp only [monomialXY]
    rw [degree_C_mul_X_pow _ (pow_ne_zero _ X_ne_zero)]
    exact_mod_cast (hf i).1
  | zero => exact ⟨by simp, WeightedDegreeLE.zero⟩
  | add x y _ _ hx hy => exact ⟨(degree_add_le _ _).trans_lt (max_lt hx.1 hy.1), hx.2.add hy.2⟩
  | smul c x _ hx => exact ⟨(degree_smul_le _ _).trans_lt hx.1, hx.2.smul c⟩

/-- Monomials attached to an injective family of exponents are linearly independent. -/
theorem eq_zero_of_sum_smul_monomialXY_eq_zero' {ι : Type*} [Fintype ι] {f : ι → ℕ × ℕ}
    (hf : Function.Injective f) {c : ι → K}
    (h : ∑ i, c i • (monomialXY (f i) : K[X][Y]) = 0) (i : ι) : c i = 0 := by
  classical
  have := congrArg (fun g : K[X][Y] => (g.coeff (f i).2).coeff (f i).1) h
  simp only [finset_sum_coeff, coeff_smul, smul_eq_mul, coeff_coeff_monomialXY, Prod.mk.eta,
    mul_ite, mul_one, mul_zero, Polynomial.coeff_zero] at this
  rwa [Finset.sum_eq_single i (fun j _ hj => if_neg (hf.ne hj)) (by simp), if_pos rfl] at this

/-- A monic irreducible `Ψ ∈ K[X][Y]` with `∂Ψ/∂Y ≠ 0` over an algebraically closed field has a
point where `∂Ψ/∂Y` does not vanish. -/
theorem exists_simple_point [IsAlgClosed K] {Ψ : K[X][Y]} (hΨ : Ψ.Monic) (hirr : Irreducible Ψ)
    (hder : derivative Ψ ≠ 0) :
    ∃ a b : K, Ψ.evalEval a b = 0 ∧ (derivative Ψ).evalEval a b ≠ 0 := by
  classical
  have hdeg : Ψ.natDegree ≠ 0 := (hΨ.natDegree_pos.mpr hirr.ne_one).ne'
  have hndvd : ¬ Ψ ∣ derivative Ψ := fun h =>
    (natDegree_derivative_lt hdeg).not_ge (natDegree_le_of_dvd h hder)
  have hres := resultant_ne_zero_of_irreducible_of_not_dvd hirr hdeg hndvd
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (resultant Ψ (derivative Ψ)).roots.toFinset
  have hra : (resultant Ψ (derivative Ψ)).eval a ≠ 0 := fun h0 =>
    ha (Multiset.mem_toFinset.mpr ((mem_roots hres).mpr h0))
  have hmon : (Ψ.map (evalRingHom a)).Monic := hΨ.map _
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root (Ψ.map (evalRingHom a))
    (by rw [degree_eq_natDegree hmon.ne_zero, hΨ.natDegree_map]; exact_mod_cast hdeg)
  have hb' : Ψ.evalEval a b = 0 := by rwa [IsRoot, map_evalRingHom_eval] at hb
  refine ⟨a, b, hb', fun h1 => hra ?_⟩
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant Ψ (derivative Ψ) le_rfl le_rfl
    (Or.inl hdeg)
  have := congrArg (evalEval a b) huv
  simpa [evalEval_add, evalEval_mul, evalEval_C, hb', h1] using this.symm

/-- Along a branch of `Ψ = 0`, a polynomial `g` with `Res_Y(Ψ, g) ≠ 0` vanishes to order at most
`deg Res_Y(Ψ, g)`. -/
theorem order_branchEval_le {Ψ g : K[X][Y]} (hΨ : Ψ.Monic) {a b : K} {β : PowerSeries K}
    (hβ0 : PowerSeries.constantCoeff β = b) (hβ : branchEval a β Ψ = 0)
    (hres : resultant Ψ g ≠ 0) :
    (branchEval a β g).order ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
  have := sum_order_le_natDegree_resultant hΨ {(a, b)} (fun _ => β)
    (fun P hP => by
      rw [Finset.mem_singleton] at hP
      subst hP
      exact ⟨hβ0, by rw [← branchEval_apply]; exact hβ⟩) hres
  simpa [branchEval_apply] using this

end Auxiliary


section Construction

/-- The monomial `Xⁱ Yʲ` indexed by `(i, j) ∈ Fin (A + 1) × Fin m`. -/
noncomputable abbrev monoFin {A m : ℕ} (x : Fin (A + 1) × Fin m) : K[X][Y] :=
  monomialXY ((x.1 : ℕ), (x.2 : ℕ))

/-- The map `Fin (A + 1) × Fin m → ℕ × ℕ` taking `(i, j)` to `((i : ℕ), (j : ℕ))` is injective. -/
theorem injective_val_prod {A m : ℕ} :
    Function.Injective fun x : Fin (A + 1) × Fin m => ((x.1 : ℕ), (x.2 : ℕ)) := by
  intro x y h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The exponents of a `monoFin` monomial satisfy `i + w j ≤ A + w (m - 1)`. -/
private theorem fin_add_mul_le {A m : ℕ} (w : ℕ) (x : Fin (A + 1) × Fin m) :
    (x.1 : ℕ) + w * (x.2 : ℕ) ≤ A + w * (m - 1) := by
  have := x.1.2; have := x.2.2
  have : w * (x.2 : ℕ) ≤ w * (m - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Elements of the span of the `monoFin` monomials have `Y`-degree `< m` and weighted degree
`≤ A + w (m - 1)`. -/
private theorem degree_lt_and_weightedDegreeLE_of_mem_span_monoFin {A m : ℕ} (w : ℕ)
    {h : K[X][Y]}
    (hh : h ∈ Submodule.span K (Set.range fun x : Fin (A + 1) × Fin m => (monoFin x : K[X][Y]))) :
    h.degree < m ∧ WeightedDegreeLE w (A + w * (m - 1)) h :=
  degree_lt_and_weightedDegreeLE_of_mem_span (f := fun x : Fin (A + 1) × Fin m => (x.1.1, x.2.1))
    (fun x => ⟨x.2.2, fin_add_mul_le w x⟩) hh

/-- The polynomial `Xⁱ Rʲ D^{m-1-j}`, whose value at a twisted Frobenius point `P` is
`D(P)^{m-1} (Xⁱ Yʲ)(P)^q`. -/
noncomputable def frobModel (R D : K[X][Y]) (m : ℕ) (x : ℕ × ℕ) : K[X][Y] :=
  C (X ^ x.1) * R ^ x.2 * D ^ (m - 1 - x.2)

/-- If `R` and `D` have weighted degree at most `r`, `x.2 < m` and `x.1 ≤ A`, then
`frobModel R D m x` has weighted degree at most `A + r (m - 1)`. -/
theorem WeightedDegreeLE.frobModel {R D : K[X][Y]} {w r m : ℕ} (hR : WeightedDegreeLE w r R)
    (hD : WeightedDegreeLE w r D) {x : ℕ × ℕ} (hx : x.2 < m) {A : ℕ} (hA : x.1 ≤ A) :
    WeightedDegreeLE w (A + r * (m - 1)) (frobModel R D m x) := by
  have h1 : WeightedDegreeLE w A (Polynomial.C (X ^ x.1) : K[X][Y]) :=
    WeightedDegreeLE.C ((natDegree_X_pow_le _).trans hA)
  refine ((h1.mul (hR.pow x.2)).mul (hD.pow (m - 1 - x.2))).mono (le_of_eq ?_)
  rw [add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (by omega), mul_comm]

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- **The auxiliary polynomial.** If the number of unknowns exceeds the number of linear
conditions, there are `v ι` in the span of the monomials `Xⁱ Yʲ` (`i ≤ aV`, `j < m`), not all
zero, such that `Ψ` divides `∑ (δ_Ψ ^ j v ι) ^ ρ · Xⁱ Rʲ D^{m-1-j}` for every `j < k`. -/
theorem exists_auxiliary {Ψ R D : K[X][Y]} (hΨ : Ψ.Monic) {m w r : ℕ} (hm : Ψ.natDegree = m)
    (hm0 : 0 < m) (hΨw : WeightedDegreeLE w (w * m) Ψ) (hR : WeightedDegreeLE w r R)
    (hD : WeightedDegreeLE w r D) {a k aV aW : ℕ}
    (hcount : k * (m * (p ^ a * (aV + w * (m - 1) + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) <
      (m * (aW + 1)) * (m * (aV + 1))) :
    ∃ v : Fin (aW + 1) × Fin m → K[X][Y],
      (∀ ι, v ι ∈ Submodule.span K (Set.range fun β : Fin (aV + 1) × Fin m => monoFin β)) ∧
      (∃ ι, v ι ≠ 0) ∧
      ∀ j < k, Ψ ∣ ∑ ι, ((curveDeriv Ψ)^[j] (v ι)) ^ p ^ a *
        frobModel R D m ((ι.1 : ℕ), (ι.2 : ℕ)) := by
  classical
  set nV := aV + w * (m - 1)
  set N := p ^ a * (nV + (k - 1) * (w * m)) + (aW + r * (m - 1))
  let vec : ℕ → (Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K[X][Y] := fun j x =>
    ((curveDeriv Ψ)^[j] (monoFin x.2)) ^ p ^ a * frobModel R D m ((x.1.1 : ℕ), (x.1.2 : ℕ))
  let M : Submodule K K[X][Y] := Submodule.span K
    (((Finset.range (N + 1) ×ˢ Finset.range m).image (monomialXY (R := K)) : Finset K[X][Y]) :
      Set K[X][Y])
  letI : AddCommGroup M := inferInstance
  letI : Module.Free K M := Module.Free.of_divisionRing K M
  letI : Module.Finite K M := inferInstanceAs (Module.Finite K (Submodule.span K _))
  let Lj : ℕ → ((Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K) →ₗ[K] K[X][Y] := fun j =>
    ((modByMonicHom Ψ).restrictScalars K) ∘ₗ ∑ x, (LinearMap.proj x).smulRight (vec j x)
  have hLj : ∀ j d, Lj j d = (∑ x, d x • vec j x) %ₘ Ψ := by
    intro j d
    simp [Lj, modByMonicHom]
  have hΨw' : WeightedDegreeLE w (w * Ψ.natDegree) Ψ := hm ▸ hΨw
  have hvec : ∀ j < k, ∀ x, WeightedDegreeLE w N (vec j x) := by
    intro j hj x
    have h1 : WeightedDegreeLE w nV (monoFin x.2 : K[X][Y]) :=
      WeightedDegreeLE.monomialXY (fin_add_mul_le w x.2)
    have h2 := (WeightedDegreeLE.iterate_curveDeriv hΨw h1 j).pow (p ^ a)
    have h3 := WeightedDegreeLE.frobModel (K := K) hR hD (m := m) (x := ((x.1.1 : ℕ), (x.1.2 : ℕ)))
      x.1.2.2 (A := aW) (by have := x.1.1.2; simp only; omega)
    refine (h2.mul h3).mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hmem : ∀ j < k, ∀ d, Lj j d ∈ M := by
    intro j hj d
    rw [hLj]
    have hsum : WeightedDegreeLE w N (∑ x, d x • vec j x) :=
      WeightedDegreeLE.sum _ fun x _ => (hvec j hj x).smul _
    have hred := WeightedDegreeLE.modByMonic hΨ hΨw' hsum
    refine mem_span_monomialXY_of_natDegree_lt ?_ hred.coeff_natDegree_le
    have hΨ1 : Ψ ≠ 1 := fun h => by rw [h, natDegree_one] at hm; omega
    exact (natDegree_modByMonic_lt _ hΨ hΨ1).trans_eq hm
  let L : ((Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K) →ₗ[K] (Fin k → M) :=
    LinearMap.pi fun j => (Lj j).codRestrict M (hmem j j.2)
  have hfin : Module.finrank K (Fin k → M) <
      Module.finrank K ((Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Fintype.card_prod]
    have hM : Module.finrank K M ≤ (N + 1) * m := by
      refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
      simp
    calc k * Module.finrank K M ≤ k * ((N + 1) * m) := Nat.mul_le_mul_left _ hM
      _ = k * (m * (N + 1)) := by ring
      _ < (m * (aW + 1)) * (m * (aV + 1)) := hcount
      _ = (aW + 1) * m * ((aV + 1) * m) := by ring
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hfin)
  have hdvd : ∀ j < k, Ψ ∣ ∑ x, d x • vec j x := by
    intro j hj
    have h0 := congrArg (fun f : Fin k → M => ((f ⟨j, hj⟩ : M) : K[X][Y]))
      (LinearMap.mem_ker.mp hd)
    have h1 : Lj j d = 0 := by simpa [L] using h0
    rw [hLj] at h1
    exact (modByMonic_eq_zero_iff_dvd hΨ).mp h1
  set fr := iterateFrobeniusEquiv K p a
  have hfr : ∀ x : K, (fr.symm x) ^ p ^ a = x := pow_iterateFrobeniusEquiv_symm p a
  let v : Fin (aW + 1) × Fin m → K[X][Y] := fun ι => ∑ β, fr.symm (d (ι, β)) • monoFin β
  refine ⟨v, fun ι => Submodule.sum_mem _ fun β _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, rfl⟩), ?_, fun j hj => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.mp hd0
    refine ⟨x.1, fun h0 => hx ?_⟩
    have := eq_zero_of_sum_smul_monomialXY_eq_zero' (K := K) injective_val_prod h0 x.2
    rwa [Prod.mk.eta, map_eq_zero_iff _ fr.symm.injective] at this
  · convert hdvd j hj using 1
    rw [show (∑ x, d x • vec j x) = ∑ ι, ∑ β, d (ι, β) • vec j (ι, β) from
      Fintype.sum_prod_type _]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [v, vec, ← Module.End.coe_pow, map_sum, map_smul, sum_pow_char_pow, _root_.smul_pow, hfr,
      Finset.sum_mul, smul_mul_assoc]


/-- **The auxiliary function is nonzero on the curve.** If the `v ι` lie in the span of the
monomials `Xⁱ Yʲ` (`i ≤ aV`, `j < m`), are not all zero, and `m (aV + w (m - 1)) < σ = p ^ b`,
then `Ψ` does not divide `∑ v ι · (Xⁱ Yʲ) ^ σ`, so their resultant is nonzero. This is
Bombieri's independence argument at a simple point of the curve. -/
theorem resultant_ne_zero_auxiliary [IsAlgClosed K] {Ψ : K[X][Y]} (hΨ : Ψ.Monic)
    (hirr : Irreducible Ψ) (hder : derivative Ψ ≠ 0) {m w : ℕ} (hm : Ψ.natDegree = m)
    (hΨw : WeightedDegreeLE w (w * m) Ψ) {b aV aW : ℕ} (hV : m * (aV + w * (m - 1)) < p ^ b)
    (v : Fin (aW + 1) × Fin m → K[X][Y])
    (hv : ∀ ι, v ι ∈ Submodule.span K (Set.range fun β : Fin (aV + 1) × Fin m => monoFin β))
    (hv0 : ∃ ι, v ι ≠ 0) :
    resultant Ψ (∑ ι, v ι * monoFin ι ^ p ^ b) ≠ 0 := by
  classical
  obtain ⟨a₀, b₀, h0, h1⟩ := exists_simple_point hΨ hirr hder
  obtain ⟨β₀, hβ₀, hβ⟩ := exists_powerSeries_root_of_simple_root hΨ h0 h1
  have hβ' : branchEval a₀ β₀ Ψ = 0 := by rw [branchEval_apply]; exact hβ
  set ι₀ := branchEval a₀ β₀
  have hdeg : Ψ.natDegree ≠ 0 := (hΨ.natDegree_pos.mpr hirr.ne_one).ne'
  have key : ∀ h : K[X][Y], h ≠ 0 → h.degree < m →
      ι₀ h ≠ 0 ∧ (ι₀ h).order ≤ ((resultant Ψ h).natDegree : ℕ∞) := by
    intro h hh hlt
    have hres : resultant Ψ h ≠ 0 := by
      refine resultant_ne_zero_of_irreducible_of_not_dvd hirr hdeg fun hd => ?_
      have h1 := natDegree_le_of_dvd hd hh
      have h2 := (natDegree_lt_iff_degree_lt hh).mpr hlt
      omega
    have hord := order_branchEval_le hΨ hβ₀ hβ' hres
    refine ⟨fun h0' => ?_, hord⟩
    rw [h0', PowerSeries.order_zero] at hord
    exact absurd hord (by simp)
  have hΨw' : ∀ i, Ψ.coeff i ≠ 0 → (Ψ.coeff i).natDegree + w * i ≤ w * Ψ.natDegree :=
    hm ▸ hΨw
  let ι₀L : K[X][Y] →ₗ[K] PowerSeries K :=
    { toFun := ι₀, map_add' := map_add ι₀, map_smul' := branchEval_smul a₀ β₀ }
  set V := Submodule.span K (Set.range fun β : Fin (aV + 1) × Fin m => (monoFin β : K[X][Y]))
  have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
  set U := V.map ι₀L
  have hspanV : ∀ h ∈ V, h.degree < m ∧ WeightedDegreeLE w (aV + w * (m - 1)) h :=
    fun h hh => degree_lt_and_weightedDegreeLE_of_mem_span_monoFin w hh
  have hU : ∀ u ∈ U, u ≠ 0 → u.order < (p ^ b : ℕ) := by
    intro u hu hu0
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hu
    have hh0 : h ≠ 0 := by rintro rfl; exact hu0 (map_zero _)
    obtain ⟨hlt, hw⟩ := hspanV h hh
    have hb : (resultant Ψ h).natDegree ≤ m * (aV + w * (m - 1)) :=
      (natDegree_resultant_le_of_weightedDegree_le hΨ hΨw' hw).trans_eq (by rw [hm])
    calc (ι₀L h).order ≤ ((resultant Ψ h).natDegree : ℕ∞) := (key h hh0 hlt).2
      _ ≤ ((m * (aV + w * (m - 1)) : ℕ) : ℕ∞) := by exact_mod_cast hb
      _ < ((p ^ b : ℕ) : ℕ∞) := by exact_mod_cast hV
  have hy : LinearIndependent K fun ι : Fin (aW + 1) × Fin m => ι₀ (monoFin ι) := by
    refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
    have hc' : ι₀ (∑ ι, c ι • monoFin ι) = 0 := by
      rw [map_sum, Finset.sum_congr rfl fun i _ => branchEval_smul a₀ β₀ (c i) (monoFin i)]
      exact hc
    by_cases hz : ∑ ι, c ι • (monoFin ι : K[X][Y]) = 0
    · exact eq_zero_of_sum_smul_monomialXY_eq_zero' injective_val_prod hz i
    · have hlt := (degree_lt_and_weightedDegreeLE_of_mem_span_monoFin w
        (h := ∑ ι, c ι • monoFin ι) (Submodule.sum_mem _ fun ι _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨ι, rfl⟩))).1
      exact absurd hc' (key _ hz hlt).1
  intro hres0
  have hdvd : Ψ ∣ ∑ ι, v ι * monoFin ι ^ p ^ b := by
    by_contra hnd
    exact resultant_ne_zero_of_irreducible_of_not_dvd hirr hdeg hnd hres0
  have hzero : ∑ ι, ι₀ (v ι) * ι₀ (monoFin ι) ^ p ^ b = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    have := congrArg ι₀ ht
    simpa [map_sum, map_mul, map_pow, hβ'] using this
  obtain ⟨ι, hι⟩ := hv0
  have := PowerSeries.eq_zero_of_sum_mul_pow_eq_zero p b U hU hy
    (u := fun ι => ι₀ (v ι)) (fun ι => Submodule.mem_map_of_mem (hv ι)) hzero ι
  exact (key _ hι (hspanV _ (hv ι)).1).1 this

/-- **Stepanov's bound, in counting form.** With the parameters `ρ = p ^ a`, `σ = p ^ b`,
`q = ρ σ`, `k ≤ p`, `k ρ ≤ q`, the degree bounds `aV`, `aW` subject to `m (aV + w (m-1)) < σ`
and to the dimension count `hcount`, every finite set `S` of twisted Frobenius points of `Ψ = 0`
at which `∂Ψ/∂Y ≠ 0` satisfies `k · #S ≤ m (aV + w (m - 1) + σ (aW + w (m - 1)))`. -/
theorem card_mul_le_of_stepanov [IsAlgClosed K] {Ψ R D : K[X][Y]} (hΨ : Ψ.Monic)
    (hirr : Irreducible Ψ) (hder : derivative Ψ ≠ 0) {m w r : ℕ} (hm : Ψ.natDegree = m)
    (hΨw : WeightedDegreeLE w (w * m) Ψ) (hR : WeightedDegreeLE w r R)
    (hD : WeightedDegreeLE w r D) {a b k aV aW : ℕ} (hk : k ≤ p)
    (hkq : k * p ^ a ≤ p ^ (a + b)) (hV : m * (aV + w * (m - 1)) < p ^ b)
    (hcount : k * (m * (p ^ a * (aV + w * (m - 1) + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) <
      (m * (aW + 1)) * (m * (aV + 1)))
    (S : Finset (K × K))
    (hS : ∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
      P.1 ^ p ^ (a + b) = P.1 ∧ D.evalEval P.1 P.2 ≠ 0 ∧
      D.evalEval P.1 P.2 * P.2 ^ p ^ (a + b) = R.evalEval P.1 P.2) :
    k * S.card ≤ m * (aV + w * (m - 1) + p ^ b * (aW + w * (m - 1))) := by
  classical
  have hdeg : Ψ.natDegree ≠ 0 := (hΨ.natDegree_pos.mpr hirr.ne_one).ne'
  have hm0 : 0 < m := by omega
  obtain ⟨v, hv, hv0, hE⟩ := exists_auxiliary p hΨ hm hm0 hΨw hR hD hcount
  obtain ⟨g, hg⟩ : ∃ g, g = ∑ ι, v ι * monoFin ι ^ p ^ b := ⟨_, rfl⟩
  have hres : resultant Ψ g ≠ 0 :=
    hg ▸ resultant_ne_zero_auxiliary p hΨ hirr hder hm hΨw hV v hv hv0
  choose! βf hβf using fun P (hP : P ∈ S) =>
    exists_powerSeries_root_of_simple_root hΨ (hS P hP).1 (hS P hP).2.1
  have hord : ∀ P ∈ S, (k : ℕ∞) ≤ (branchEval P.1 (βf P) g).order := by
    intro P hP
    obtain ⟨h0, h1, hq, hD0, hRD⟩ := hS P hP
    have hβ : branchEval P.1 (βf P) Ψ = 0 := by rw [branchEval_apply]; exact (hβf P hP).2
    rw [hg]
    refine le_order_branchEval_sum_mul_pow p (hβf P hP).1 hβ h1 v (fun ι => monoFin ι)
      (fun ι => frobModel R D m ((ι.1 : ℕ), (ι.2 : ℕ))) hk hkq
      (lam := D.evalEval P.1 P.2 ^ (m - 1)) (pow_ne_zero _ hD0) (fun ι => ?_) (fun j hj => ?_)
    · have hl : (ι.2 : ℕ) + (m - 1 - ι.2) = m - 1 := by have := ι.2.2; omega
      simp only [frobModel, monoFin, monomialXY, evalEval_mul, evalEval_pow, evalEval_C,
        eval_pow, eval_X, evalEval_X, ← hRD, mul_pow, ← pow_mul]
      have hD' : D.evalEval P.1 P.2 ^ (m - 1) =
          D.evalEval P.1 P.2 ^ (ι.2 : ℕ) * D.evalEval P.1 P.2 ^ (m - 1 - ι.2) := by
        rw [← pow_add, hl]
      rw [pow_mul' P.1, hq, mul_comm (ι.2 : ℕ) (p ^ (a + b)), hD']
      ring
    · obtain ⟨t, ht⟩ := hE j hj
      rw [ht, evalEval_mul, h0, zero_mul]
  have hsum := sum_order_le_natDegree_resultant hΨ S βf hβf hres
  simp only [← branchEval_apply] at hsum
  have hlow : (S.card • (k : ℕ∞)) ≤ ∑ P ∈ S, (branchEval P.1 (βf P) g).order :=
    Finset.card_nsmul_le_sum S _ _ hord
  have hΨw' : ∀ i, Ψ.coeff i ≠ 0 → (Ψ.coeff i).natDegree + w * i ≤ w * Ψ.natDegree :=
    hm ▸ hΨw
  have hgw : WeightedDegreeLE w (aV + w * (m - 1) + p ^ b * (aW + w * (m - 1))) g := by
    rw [hg]
    refine WeightedDegreeLE.sum _ fun ι _ => ?_
    have h1 := (degree_lt_and_weightedDegreeLE_of_mem_span_monoFin w (hv ι)).2
    have h2 : WeightedDegreeLE w (aW + w * (m - 1)) (monoFin ι : K[X][Y]) :=
      WeightedDegreeLE.monomialXY (fin_add_mul_le w ι)
    exact h1.mul (h2.pow _)
  have hdegR : (resultant Ψ g).natDegree ≤
      m * (aV + w * (m - 1) + p ^ b * (aW + w * (m - 1))) :=
    (natDegree_resultant_le_of_weightedDegree_le hΨ hΨw' hgw).trans_eq (by rw [hm])
  have h1 : ((S.card * k : ℕ) : ℕ∞) ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
    refine le_trans (le_of_eq ?_) (hlow.trans hsum)
    simp [nsmul_eq_mul]
  have h2 : S.card * k ≤ (resultant Ψ g).natDegree := ENat.coe_le_coe.mp h1
  rw [mul_comm k]
  exact h2.trans hdegR

end Construction

end Polynomial.Bivariate

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.PlaneCurvePointUpperBound
section




/-!
# The upper bound `q + O(√q)` for the Frobenius points of a plane curve

Let `K` be an algebraically closed field of characteristic `p`, `q = p ^ e` with `e ≥ 1`, and
`Ψ ∈ K[X][Y]` monic irreducible of `Y`-degree `m` and weight `w` (that is, the coefficient of
`Yⁱ` has degree `≤ w (m - i)`), with `∂Ψ/∂Y ≠ 0`. For `R, D` of weighted degree `≤ r`, the points
`P = (a, b)` of `Ψ = 0` with `∂Ψ/∂Y(P) ≠ 0`, `a ^ q = a`, `D(P) ≠ 0` and `D(P) b ^ q = R(P)`
number at most `q + C √q`, where `C` depends only on `m`, `w` and `r`.

This is `Polynomial.Bivariate.card_mul_le_of_stepanov` with the parameters
`ρ = p ^ ⌊e/2⌋`, `σ = p ^ ⌈e/2⌉`, `k = 1` if `e` is even and `k = ⌊√p⌋` if `e` is odd, and
`aV ≈ σ/m`, `aW ≈ kρ/m`; small `q` are covered by the trivial bound `m q`.

## Main results

* `Polynomial.Bivariate.card_le_mul_of_frobenius`: the trivial bound `#S ≤ q m`.
* `Polynomial.Bivariate.exists_card_le_add_mul_sqrt`: the bound `#S ≤ q + C √q`.
-/


open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- **The trivial bound.** Points of `Ψ = 0` whose first coordinate satisfies `a ^ q = a`
(`q ≥ 2`) number at most `q · deg_Y Ψ`. -/
theorem card_le_mul_of_frobenius {Ψ : K[X][Y]} (hΨ : Ψ.Monic) {q : ℕ} (hq : 1 < q)
    (S : Finset (K × K)) (hS : ∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ P.1 ^ q = P.1) :
    S.card ≤ q * Ψ.natDegree := by
  classical
  have hX : (X ^ q - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  refine (card_le_card_mul_of_fibres (X ^ q - X : K[X]).roots.toFinset S
    (fun a => Ψ.map (evalRingHom a)) (D := Ψ.natDegree) (fun P hP => ⟨?_, ?_, ?_⟩)
    (fun a _ => natDegree_map_le)).trans (Nat.mul_le_mul_right _ ?_)
  · refine Multiset.mem_toFinset.mpr ((mem_roots hX).mpr ?_)
    simp [(hS P hP).2]
  · exact (hΨ.map _).ne_zero
  · rw [IsRoot, map_evalRingHom_eval]
    exact (hS P hP).1
  · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq K hq).le)

/-- Floor division by `m > 0` is sandwiched: `m * (n / m) ≤ n < m * (n / m) + m`. -/
private theorem mul_div_bounds {m : ℕ} (hm : 0 < m) (n : ℕ) :
    m * (n / m) ≤ n ∧ n < m * (n / m) + m :=
  ⟨Nat.mul_div_le _ _, by simpa [mul_add_one] using Nat.lt_mul_div_succ n hm⟩

/-- The arithmetic behind the choice of parameters: for `σ` large and `k² ρ ≤ σ`, suitable
`aV`, `aW` exist. -/
theorem exists_stepanov_parameters (m w r : ℕ) (hm : 0 < m) :
    ∃ σ₀ C₀ : ℕ, ∀ ρ σ k : ℕ, 1 ≤ k → 1 ≤ ρ → k ^ 2 * ρ ≤ σ → σ₀ ≤ σ → ∃ aV aW : ℕ,
      m * (aV + w * (m - 1)) < σ ∧
      k * (m * (ρ * (aV + w * (m - 1) + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) <
        (m * (aW + 1)) * (m * (aV + 1)) ∧
      m * (aV + w * (m - 1) + σ * (aW + w * (m - 1))) ≤ k * ρ * σ + σ * C₀ := by
  set A := m * (w * (m - 1) + 1)
  set c := A + w * m ^ 2 + 1
  set B := c + m * (r * m + 1)
  refine ⟨max (2 * (A * (c + 1)) + 1) (4 * B ^ 2), 1 + c + m * (w * (m - 1)), ?_⟩
  intro ρ σ k hk hρ1 hkρ hσ
  obtain ⟨hσ1, hσ2⟩ := max_le_iff.mp hσ
  have hk2 : k ^ 2 ≤ σ := le_trans (Nat.le_mul_of_pos_right _ hρ1) hkρ
  have hkk : k ≤ k ^ 2 := Nat.le_self_pow two_ne_zero k
  have hρ : k * ρ ≤ σ := le_trans (Nat.mul_le_mul_right _ hkk) hkρ
  have hAc : A ≤ A * (c + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  obtain ⟨hmt1, hmt2⟩ := mul_div_bounds hm (σ - 1)
  set t := (σ - 1) / m
  have ht3 : w * (m - 1) + 1 ≤ t := (Nat.le_div_iff_mul_le hm).mpr (by
    have : (w * (m - 1) + 1) * m = A := by
      simp only [A]
      ring
    omega)
  obtain ⟨hmw1, hmw2⟩ := mul_div_bounds hm (k * ρ + c)
  set aW := (k * ρ + c) / m
  have htu : t - w * (m - 1) + w * (m - 1) = t := Nat.sub_add_cancel (by omega)
  refine ⟨t - w * (m - 1), aW, ?_, ?_, ?_⟩
  · rw [htu]
    omega
  · rw [htu]
    have hkB : 2 * (k * B) ≤ σ := by
      have : (2 * (k * B)) ^ 2 ≤ σ ^ 2 := by
        calc (2 * (k * B)) ^ 2 = k ^ 2 * (4 * B ^ 2) := by ring
          _ ≤ σ * σ := Nat.mul_le_mul hk2 hσ2
          _ = σ ^ 2 := by ring
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
    set Yv := m * (t - w * (m - 1) + 1)
    have hY : σ ≤ Yv + A := by
      have hu : (t - w * (m - 1) + 1) + (w * (m - 1) + 1) = t + 2 := by omega
      have h' : Yv + A = m * t + 2 * m := by
        simp only [Yv, A]
        rw [← mul_add, hu]
        ring
      omega
    have hwm : (k - 1) * (w * m) * (k * m * ρ) ≤ σ * (w * m ^ 2) := by
      calc (k - 1) * (w * m) * (k * m * ρ) ≤ k * (w * m) * (k * m * ρ) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
        _ = (k ^ 2 * ρ) * (w * m ^ 2) := by ring
        _ ≤ σ * (w * m ^ 2) := Nat.mul_le_mul_right _ hkρ
    have hrm : k * m * (r * (m - 1)) ≤ k * m * (r * m) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have e1 : k * ρ * (m * t) + k * ρ ≤ k * ρ * σ := by
      have := Nat.mul_le_mul_left (k * ρ) (show m * t + 1 ≤ σ by omega)
      rwa [mul_add, mul_one] at this
    have e2 : k * (m * aW) ≤ k * (k * ρ) + k * c := by
      have := Nat.mul_le_mul_left k hmw1
      rwa [mul_add] at this
    have e3 : k * (k * ρ) ≤ σ := by
      have : k * (k * ρ) = k ^ 2 * ρ := by ring
      omega
    have expand : k * (m * (ρ * (t + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) =
        k * ρ * (m * t) + (k - 1) * (w * m) * (k * m * ρ) + k * (m * aW) +
          k * m * (r * (m - 1)) + k * m := by ring
    have hrhs : k * ρ * σ + c * σ + σ ≤ (k * ρ + c + 1) * Yv + (k * ρ * A + c * A + A) := by
      have h := Nat.mul_le_mul_left (k * ρ + c + 1) hY
      have e : (k * ρ + c + 1) * (Yv + A) = (k * ρ + c + 1) * Yv + (k * ρ * A + c * A + A) := by
        ring
      have e' : (k * ρ + c + 1) * σ = k * ρ * σ + c * σ + σ := by ring
      omega
    have h1 : k * ρ * A ≤ σ * A := Nat.mul_le_mul_right _ hρ
    have hB : k * B = k * c + k * m * (r * m) + k * m := by simp only [B]; ring
    have hcA : A * (c + 1) = c * A + A := by ring
    have hcσ : c * σ = σ * A + σ * (w * m ^ 2) + σ := by simp only [c]; ring
    rw [expand]
    calc _ < (k * ρ + c + 1) * Yv := by omega
      _ ≤ m * (aW + 1) * Yv := Nat.mul_le_mul_right _ hmw2
  · rw [htu]
    have hmt : m * t ≤ σ := by omega
    calc m * (t + σ * (aW + w * (m - 1))) = m * t + σ * (m * aW) + σ * (m * (w * (m - 1))) := by
          ring
      _ ≤ σ + σ * (k * ρ + c) + σ * (m * (w * (m - 1))) := by
          gcongr
      _ = k * ρ * σ + σ * (1 + c + m * (w * (m - 1))) := by ring

/-- The choice `k = 1` (`e` even) or `k = ⌊√p⌋` (`e` odd), with `ρ = p ^ ⌊e/2⌋`,
`σ = p ^ (e - ⌊e/2⌋)`: then `k ≤ p`, `k² ρ ≤ σ ≤ 4 k² ρ`. -/
theorem exists_stepanov_k (p e : ℕ) (hp : p.Prime) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ p ∧ k ^ 2 * p ^ (e / 2) ≤ p ^ (e - e / 2) ∧
      p ^ (e - e / 2) ≤ 4 * k ^ 2 * p ^ (e / 2) := by
  have hp2 := hp.two_le
  rcases Nat.even_or_odd e with he | he
  · have h : e - e / 2 = e / 2 := by
      obtain ⟨j, rfl⟩ := he
      omega
    rw [h]
    exact ⟨1, le_rfl, by omega, by simp, by nlinarith [Nat.one_le_pow (e / 2) p (by omega)]⟩
  · have hb : e - e / 2 = e / 2 + 1 := by
      obtain ⟨j, rfl⟩ := he
      omega
    rw [hb, pow_succ]
    have hk1 : 1 ≤ Nat.sqrt p := Nat.sqrt_pos.mpr (by omega)
    have hk2 : Nat.sqrt p ^ 2 ≤ p := Nat.sqrt_le' p
    have hk3 : p < (Nat.sqrt p + 1) ^ 2 := Nat.lt_succ_sqrt' p
    refine ⟨Nat.sqrt p, hk1, Nat.sqrt_le_self p, ?_, ?_⟩
    · rw [mul_comm]
      exact Nat.mul_le_mul_left _ hk2
    · have : p ≤ 4 * Nat.sqrt p ^ 2 := by nlinarith
      calc p ^ (e / 2) * p ≤ p ^ (e / 2) * (4 * Nat.sqrt p ^ 2) := Nat.mul_le_mul_left _ this
        _ = 4 * Nat.sqrt p ^ 2 * p ^ (e / 2) := by ring

/-- **The upper bound `q + C √q`.** For given `m`, `w`, `r` there is a constant `C` such that,
over every algebraically closed field `K` of characteristic `p` and for every `q = p ^ e` with
`e ≥ 1`, every finite set `S` of twisted Frobenius points of a monic irreducible `Ψ` of
`Y`-degree `m` and weight `w` with `∂Ψ/∂Y ≠ 0`, at which `∂Ψ/∂Y` does not vanish, has
`#S ≤ q + C √q`. -/
theorem exists_card_le_add_mul_sqrt (m w r : ℕ) :
    ∃ C : ℝ, ∀ (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] (e : ℕ),
      0 < e → ∀ Ψ R D : K[X][Y], Ψ.Monic → Irreducible Ψ → derivative Ψ ≠ 0 →
      Ψ.natDegree = m → WeightedDegreeLE w (w * m) Ψ → WeightedDegreeLE w r R →
      WeightedDegreeLE w r D → ∀ S : Finset (K × K),
      (∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
        P.1 ^ p ^ e = P.1 ∧ D.evalEval P.1 P.2 ≠ 0 ∧
        D.evalEval P.1 P.2 * P.2 ^ p ^ e = R.evalEval P.1 P.2) →
      (S.card : ℝ) ≤ (p : ℝ) ^ e + C * √((p : ℝ) ^ e) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, fun K _ _ p _ _ e he Ψ R D hΨ hirr _ hm _ _ _ S hS => ?_⟩
    simpa [eq_one_of_monic_natDegree_zero hΨ hm] using hirr.not_isUnit
  obtain ⟨σ₀, C₀, hpar⟩ := exists_stepanov_parameters m w r hm
  refine ⟨max (2 * (C₀ : ℝ)) (((m : ℝ) - 1) * σ₀), fun K _ _ p _ _ e he Ψ R D hΨ hirr hder hmΨ
    hΨw hR hD S hS => ?_⟩
  have : PerfectRing K p := PerfectField.toPerfectRing p
  have hp := (Fact.out : p.Prime)
  set a := e / 2
  set b := e - e / 2
  have hab : e = a + b := by omega
  obtain ⟨k, hk1, hkp, hkρ, hkσ⟩ := exists_stepanov_k p e hp
  set ρ := p ^ a
  set σ := p ^ b
  have hρ1 : 1 ≤ ρ := Nat.one_le_pow _ _ hp.pos
  have hq : (p : ℝ) ^ e = (ρ : ℝ) * σ := by
    rw [hab, pow_add]
    simp [ρ, σ]
  by_cases hσ : σ₀ ≤ σ
  · obtain ⟨aV, aW, hV, hcount, hfin⟩ := hpar ρ σ k hk1 hρ1 hkρ hσ
    have hkq : k * p ^ a ≤ p ^ (a + b) := by
      rw [pow_add]
      calc k * p ^ a ≤ k ^ 2 * p ^ a := Nat.mul_le_mul_right _ (Nat.le_self_pow two_ne_zero k)
        _ ≤ σ := hkρ
        _ ≤ p ^ a * σ := Nat.le_mul_of_pos_left _ hρ1
    have hmain : k * S.card ≤ k * ρ * σ + σ * C₀ :=
      (card_mul_le_of_stepanov p hΨ hirr hder hmΨ hΨw hR hD hkp hkq hV hcount S
        (by rwa [← hab])).trans hfin
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    -- `σ ≤ 2 k √q`
    have hσk : (σ : ℝ) ≤ 2 * k * √((p : ℝ) ^ e) := by
      rw [show (2 * k * √((p : ℝ) ^ e) : ℝ) = √((2 * k) ^ 2 * (p : ℝ) ^ e) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
      refine Real.le_sqrt_of_sq_le ?_
      rw [hq]
      have h1 : (σ : ℝ) ≤ 4 * k ^ 2 * ρ := by exact_mod_cast hkσ
      have h2 : (0 : ℝ) ≤ σ := by positivity
      nlinarith
    have hcard : (S.card : ℝ) ≤ ρ * σ + C₀ * (σ / k) := by
      have h : (k : ℝ) * S.card ≤ k * ρ * σ + σ * C₀ := by exact_mod_cast hmain
      have e : (ρ : ℝ) * σ + C₀ * (σ / k) = (k * ρ * σ + σ * C₀) / k := by
        field_simp
      rw [e, le_div_iff₀ hk0]
      linarith
    calc (S.card : ℝ) ≤ ρ * σ + C₀ * (σ / k) := hcard
      _ ≤ ρ * σ + C₀ * (2 * √((p : ℝ) ^ e)) := by
          gcongr
          rw [div_le_iff₀ hk0]
          linarith
      _ = (p : ℝ) ^ e + (2 * C₀) * √((p : ℝ) ^ e) := by rw [hq]; ring
      _ ≤ (p : ℝ) ^ e + max (2 * (C₀ : ℝ)) (((m : ℝ) - 1) * σ₀) * √((p : ℝ) ^ e) := by
          gcongr
          exact le_max_left _ _
  · push Not at hσ
    have hq1 : 1 < p ^ e := Nat.one_lt_pow he.ne' hp.one_lt
    have htriv := card_le_mul_of_frobenius hΨ hq1 S fun P hP => ⟨(hS P hP).1, (hS P hP).2.2.1⟩
    rw [hmΨ] at htriv
    have hρσ : ρ ≤ σ := Nat.pow_le_pow_right hp.pos (by omega)
    have hsq : (p : ℝ) ^ e ≤ σ₀ * √((p : ℝ) ^ e) := by
      have hσ0 : (0 : ℝ) ≤ σ := by positivity
      have h1 : (p : ℝ) ^ e ≤ (σ : ℝ) ^ 2 := by
        rw [hq, sq]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hρσ) hσ0
      have h2 : √((p : ℝ) ^ e) ≤ σ₀ :=
        ((Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq hσ0)).trans (by exact_mod_cast hσ.le)
      calc (p : ℝ) ^ e = √((p : ℝ) ^ e) * √((p : ℝ) ^ e) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ σ₀ * √((p : ℝ) ^ e) := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc (S.card : ℝ) ≤ (p : ℝ) ^ e * m := by exact_mod_cast htriv
      _ = (p : ℝ) ^ e + (m - 1) * (p : ℝ) ^ e := by ring
      _ ≤ (p : ℝ) ^ e + (m - 1) * (σ₀ * √((p : ℝ) ^ e)) := by
          gcongr
      _ = (p : ℝ) ^ e + ((m - 1) * σ₀) * √((p : ℝ) ^ e) := by ring
      _ ≤ (p : ℝ) ^ e + max (2 * (C₀ : ℝ)) (((m : ℝ) - 1) * σ₀) * √((p : ℝ) ^ e) := by
          gcongr
          exact le_max_right _ _

end Polynomial.Bivariate

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.PlaneCurvePointLowerBound
section




/-!
# The lower bound `q - C √q` for the points of an absolutely irreducible plane curve

Let `g ∈ 𝔽_q[X][Y]` be monic of `Y`-degree `m` and total degree `m`, with `∂g/∂Y ≠ 0`, and
absolutely irreducible. Over `Kbar = 𝔽̄_q`, label the roots `b₁, …, b_m` of `g(a, Y)` at a good
`a ∈ 𝔽_q`; Frobenius permutes them by some `π_a`, and the number of `𝔽_q`-points of `g` over `a`
is the number of fixed points of `π_a`. The Galois resolvent `Φ(a, T) = ∏_π (T - Σ cᵢ b_{π i})`
factors over `Kbar[X]` into absolutely irreducible `Ψ`, and for each `τ ∈ S_m` the points
`(a, t)` of `Ψ` with `Δ(a) t^q = R_τ(a, t)` are counted by Stepanov's upper bound when the twisted
Frobenius preserves `Ψ`, and by Bézout otherwise. The twisted orbit counts of the Galois group
turn these upper bounds into the lower bound.

## Main results

* `Polynomial.Bivariate.exists_card_ge_of_monic`: the lower bound `#C(𝔽_q) ≥ q - c √q`, with `c`
  depending only on the degree `m`, for every finite field.
* `Polynomial.Bivariate.fiber_twisted_count`, `Polynomial.Bivariate.global_twisted_count`: the
  counting identities over the fibres.
* `Polynomial.Bivariate.card_le_of_twisted_points`: the stable/unstable dichotomy for one factor
  of the resolvent and one twist.
* `Polynomial.Bivariate.le_of_twisted_counts`: the inequality bookkeeping.
-/


open Polynomial Finset
open scoped Polynomial.Bivariate Nat

namespace Polynomial.Bivariate

/-- **The bookkeeping.** Let `sᵢ ≤ eᵢ q + U` (`i ∈ I`), with `∑ sᵢ = M · n` and `q - D ≤ n`,
`∑ eᵢ = M`, `∑ fᵢ eᵢ = M` and `0 ≤ fᵢ ≤ μ`. Then `∑ fᵢ sᵢ ≥ M q - μ (#I U + M D)`. -/
theorem le_of_twisted_counts {ι : Type*} (I : Finset ι) (s e f : ι → ℝ) {q U M n D μ : ℝ}
    (hs : ∀ i ∈ I, s i ≤ e i * q + U) (hf : ∀ i ∈ I, 0 ≤ f i ∧ f i ≤ μ)
    (hsum : ∑ i ∈ I, s i = M * n) (hn : q - D ≤ n) (he : ∑ i ∈ I, e i = M)
    (hfe : ∑ i ∈ I, f i * e i = M) (hU : 0 ≤ U) (_hq : 0 ≤ q) (hM : 0 ≤ M) (hμ : 0 ≤ μ) :
    M * q - μ * (I.card * U + M * D) ≤ ∑ i ∈ I, f i * s i := by
  set t : ι → ℝ := fun i => e i * q + U - s i
  have ht0 : ∀ i ∈ I, 0 ≤ t i := fun i hi => by simp only [t]; linarith [hs i hi]
  have hsumt : ∑ i ∈ I, t i ≤ I.card * U + M * D := by
    simp only [t, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, he,
      Finset.sum_const, nsmul_eq_mul, hsum]
    nlinarith
  have hft : ∑ i ∈ I, f i * t i ≤ μ * ∑ i ∈ I, t i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hf i hi).2 (ht0 i hi)
  have hfU : 0 ≤ ∑ i ∈ I, f i * U := Finset.sum_nonneg fun i hi => mul_nonneg (hf i hi).1 hU
  have hfs : ∑ i ∈ I, f i * s i = q * M + ∑ i ∈ I, f i * U - ∑ i ∈ I, f i * t i := by
    simp only [t, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [show ∑ i ∈ I, f i * (e i * q) = q * ∑ i ∈ I, f i * e i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hfe]
    ring
  rw [hfs]
  nlinarith [mul_le_mul_of_nonneg_left hsumt hμ]

/-- **The counting identities over one fibre.** Suppose every `π ∈ S_m` is attached to exactly
one `Ψ ∈ 𝒪` (through `Z Ψ π`), and let `α ∈ S_m`. Counting, for each `Ψ` and `τ`, the `π` attached
to `Ψ` with `α π = π τ`, the totals are `m!`, and `m!` times the number of fixed points of `α`
when each `τ` is weighted by its number of fixed points. -/
theorem fiber_twisted_count {m : ℕ} {X : Type*} (𝒪 : Finset X)
    (Z : X → Equiv.Perm (Fin m) → Prop) [∀ Ψ π, Decidable (Z Ψ π)]
    (hZ : ∀ π, ∃! Ψ, Ψ ∈ 𝒪 ∧ Z Ψ π) (α : Equiv.Perm (Fin m)) :
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card = m ! ∧
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), (univ.filter fun i => τ i = i).card *
      (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card =
      m ! * (univ.filter fun i => α i = i).card := by
  classical
  have hconj : ∀ π τ : Equiv.Perm (Fin m), α * π = π * τ ↔ τ = π⁻¹ * α * π := fun π τ => by
    rw [mul_assoc, eq_inv_mul_iff_mul_eq, eq_comm]
  have hone : ∀ π : Equiv.Perm (Fin m), ∑ Ψ ∈ 𝒪, (if Z Ψ π then 1 else 0 : ℕ) = 1 := by
    intro π
    obtain ⟨Ψ, ⟨hΨ, hZΨ⟩, huniq⟩ := hZ π
    rw [Finset.sum_eq_single Ψ (fun Ψ' hΨ' hne => if_neg fun h => hne (huniq Ψ' ⟨hΨ', h⟩))
      (fun h => absurd hΨ h), if_pos hZΨ]
  have key : ∀ (w : Equiv.Perm (Fin m) → ℕ),
      ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), w τ *
        (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card =
      ∑ π : Equiv.Perm (Fin m), w (π⁻¹ * α * π) := by
    intro w
    calc ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), w τ *
          (univ.filter fun π => Z Ψ π ∧ α * π = π * τ).card
        = ∑ Ψ ∈ 𝒪, ∑ π : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
            w τ * (if Z Ψ π ∧ α * π = π * τ then 1 else 0) := by
          refine Finset.sum_congr rfl fun Ψ _ => ?_
          simp only [Finset.card_filter, Finset.mul_sum]
          exact Finset.sum_comm
      _ = ∑ π : Equiv.Perm (Fin m), ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m),
            w τ * (if Z Ψ π ∧ α * π = π * τ then 1 else 0) := Finset.sum_comm
      _ = _ := ?_
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [hconj, mul_ite, mul_one, mul_zero]
    have : ∀ Ψ ∈ 𝒪, (∑ τ : Equiv.Perm (Fin m),
        if Z Ψ π ∧ τ = π⁻¹ * α * π then w τ else 0) = if Z Ψ π then w (π⁻¹ * α * π) else 0 := by
      intro Ψ _
      by_cases h : Z Ψ π <;> simp [h]
    rw [Finset.sum_congr rfl this]
    calc ∑ Ψ ∈ 𝒪, (if Z Ψ π then w (π⁻¹ * α * π) else 0)
        = w (π⁻¹ * α * π) * ∑ Ψ ∈ 𝒪, (if Z Ψ π then 1 else 0 : ℕ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun Ψ _ => by split_ifs <;> simp
      _ = w (π⁻¹ * α * π) := by rw [hone, mul_one]
  refine ⟨?_, ?_⟩
  · simpa only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      smul_eq_mul, mul_one] using key fun _ => 1
  · rw [key fun τ => (univ.filter fun i => τ i = i).card]
    simp only [GaloisResolventFactors.card_fixed_conj, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, smul_eq_mul]

/-- A monic polynomial of degree `n` over an algebraically closed field is a product of `n`
linear factors, labelled by `Fin n`. -/
theorem exists_eq_prod_X_sub_C {K : Type*} [Field K] [IsAlgClosed K] :
    ∀ (n : ℕ) {p : K[X]}, p.Monic → p.natDegree = n → ∃ b : Fin n → K, p = ∏ i, (X - C (b i)) := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    exact ⟨Fin.elim0, by rw [eq_one_of_monic_natDegree_zero hp hn]; simp⟩
  | succ n ih =>
    intro p hp hn
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p (by
      rw [degree_eq_natDegree hp.ne_zero, hn]; exact_mod_cast Nat.succ_ne_zero n)
    obtain ⟨p', hp'⟩ := dvd_iff_isRoot.mpr hr
    have hmon' : p'.Monic := by
      have := hp; rw [hp'] at this; exact (monic_X_sub_C r).of_mul_monic_left this
    have hdeg' : p'.natDegree = n := by
      have := congrArg natDegree hp'
      rw [(monic_X_sub_C r).natDegree_mul hmon', natDegree_X_sub_C, hn] at this
      omega
    obtain ⟨b, hb⟩ := ih hmon' hdeg'
    exact ⟨Fin.cons r b, by rw [Fin.prod_univ_succ, Fin.cons_zero, hp', hb]; simp⟩

variable {Kbar : Type*} [Field Kbar]

/-- **The fibre of the resolvent at a good point.** Let `f ∈ Kbar[X][Y]` be monic of `Y`-degree `m`,
`c : Fin m → Kbar`, and let `α ∈ Kbar` with `Δ(α) ≠ 0`. Then the roots `b` of `f(α, Y)` are distinct,
the values `t_π = ∑ cᵢ b_{π i}` are distinct and are the roots of `Φ(α, T)`, and
`R_τ(α, t_π) = Δ(α) t_{π τ}`. -/
theorem exists_fibre_labelling [IsAlgClosed Kbar] {m : ℕ} {f : Kbar[X][Y]} (hf : f.Monic)
    (hm : f.natDegree = m) (c : Fin m → Kbar) {α : Kbar}
    (hα : (resolventDisc f fun i => C (c i)).eval α ≠ 0) :
    ∃ b : Fin m → Kbar, f.map (evalRingHom α) = ∏ i, (X - C (b i)) ∧ Function.Injective b ∧
      Function.Injective (fun π : Equiv.Perm (Fin m) => ∑ i, c i * b (π i)) ∧
      (galoisResolvent f fun i => C (c i)).map (evalRingHom α) =
        ∏ π : Equiv.Perm (Fin m), (X - C (∑ i, c i * b (π i))) ∧
      ∀ τ π : Equiv.Perm (Fin m), (resolventPerm f (fun i => C (c i)) τ).evalEval α
        (∑ i, c i * b (π i)) =
          (resolventDisc f fun i => C (c i)).eval α * ∑ i, c i * b ((π * τ) i) := by
  classical
  have hmon : (f.map (evalRingHom α)).Monic := hf.map _
  obtain ⟨b, hb⟩ := exists_eq_prod_X_sub_C m hmon (by rw [hf.natDegree_map, hm])
  obtain ⟨h1, h2, h3⟩ := galoisResolvent_spec f (fun i => C (c i)) (evalRingHom α) b hb
  simp only [coe_evalRingHom, eval_C] at h1 h2 h3
  have hu : Function.Injective (fun π : Equiv.Perm (Fin m) => ∑ i, c i * b (π i)) := by
    intro π π' h
    by_contra hne
    apply hα
    rw [h2]
    refine Finset.prod_eq_zero (Finset.mem_univ π) (Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩) ?_)
    exact sub_eq_zero.mpr h
  refine ⟨b, hb, fun i j hij => ?_, hu, h1, fun τ π => ?_⟩
  · by_contra hne
    have := @hu 1 (Equiv.swap i j) (by
      simp only [Equiv.Perm.one_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hki : k = i
      · subst hki; simp [Equiv.swap_apply_left, hij]
      · by_cases hkj : k = j
        · subst hkj; simp [Equiv.swap_apply_right, hij]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj])
    exact hne (by simpa using congrArg (· i) this.symm |>.symm)
  · have := h3 τ π
    rw [← map_evalRingHom_eval, this]

/-- **Frobenius permutes the roots of a fibre.** If a ring automorphism `fr` of `Kbar` fixes `f`,
the point `α` and the `cᵢ`, it permutes the roots `b` of `f(α, Y)` by some `π_α`, and then
`fr (t_π) = t_{π_α π}`. -/
theorem exists_frobenius_perm {m : ℕ} {f : Kbar[X][Y]} (fr : Kbar ≃+* Kbar)
    (hfr : f.map (mapRingHom (fr : Kbar →+* Kbar)) = f) {α : Kbar} (hα : fr α = α) {b : Fin m → Kbar}
    (hb : f.map (evalRingHom α) = ∏ i, (X - C (b i))) (hbinj : Function.Injective b)
    (c : Fin m → Kbar) (hc : ∀ i, fr (c i) = c i) :
    ∃ πa : Equiv.Perm (Fin m), (∀ i, b (πa i) = fr (b i)) ∧
      ∀ π : Equiv.Perm (Fin m), fr (∑ i, c i * b (π i)) = ∑ i, c i * b ((πa * π) i) := by
  classical
  have hP : (f.map (evalRingHom α)).map (fr : Kbar →+* Kbar) = f.map (evalRingHom α) := by
    conv_rhs => rw [← hfr]
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext h <;> simp [hα]
  have hroot : ∀ i, ∃ j, b j = fr (b i) := by
    intro i
    have h0 : (f.map (evalRingHom α)).eval (fr (b i)) = 0 := by
      have h := eval_map_apply (p := f.map (evalRingHom α)) (f := (fr : Kbar →+* Kbar)) (b i)
      rw [hP] at h
      rw [show fr (b i) = (fr : Kbar →+* Kbar) (b i) from rfl, h, hb]
      simp [eval_prod, Finset.prod_eq_zero (Finset.mem_univ i)]
    rw [hb, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨j, -, hj⟩ := h0
    exact ⟨j, (sub_eq_zero.mp (by simpa using hj)).symm⟩
  choose σ hσ using hroot
  have hinj : Function.Injective σ := fun i j h => hbinj (fr.injective (by rw [← hσ, ← hσ, h]))
  let πa := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
  refine ⟨πa, fun i => hσ i, fun π => ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hc, Equiv.Perm.mul_apply]
  exact congrArg _ (hσ (π i)).symm

open scoped Classical in
/-- **The bound for one factor and one twist.** For a finite set `S` of points of `Ψ = 0` that
are fixed by the twisted Frobenius `(a, t) ↦ (a, R(a, t) / Δ(a))`: if `Ψ` divides its twisted
composite `G`, Stepanov's bound gives `#S ≤ q + C √q`; otherwise `S` lies on `Ψ = G = 0` and
Bézout gives `#S ≤ 2 D³`. -/
theorem card_le_of_twisted_points [IsAlgClosed Kbar] (p : ℕ) [Fact p.Prime] [CharP Kbar p] {e : ℕ}
    (fr : Kbar ≃+* Kbar) (hfr : ∀ x, fr x = x ^ p ^ e) {Ψ R : Kbar[X][Y]} {Δ : Kbar[X]}
    (hirr : Irreducible Ψ) {Dz : ℕ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ S : Finset (Kbar × Kbar), (∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧
        (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧ P.1 ^ p ^ e = P.1 ∧
        (Polynomial.C Δ : Kbar[X][Y]).evalEval P.1 P.2 ≠ 0 ∧
        (Polynomial.C Δ : Kbar[X][Y]).evalEval P.1 P.2 * P.2 ^ p ^ e = R.evalEval P.1 P.2) →
      (S.card : ℝ) ≤ (p : ℝ) ^ e + C * √((p : ℝ) ^ e))
    (hΨD : ∀ j, (Ψ.coeff j).natDegree ≤ Dz) (hΨn : Ψ.natDegree ≤ Dz)
    (hGD : ∀ j, ((twistedComp (fr : Kbar →+* Kbar) Ψ R Δ).coeff j).natDegree ≤ Dz)
    (hGn : (twistedComp (fr : Kbar →+* Kbar) Ψ R Δ).natDegree ≤ Dz)
    (S : Finset (Kbar × Kbar))
    (hS : ∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
      fr P.1 = P.1 ∧ Δ.eval P.1 ≠ 0 ∧ R.evalEval P.1 P.2 = Δ.eval P.1 * fr P.2)
    (hG : ∀ P ∈ S, (twistedComp (fr : Kbar →+* Kbar) Ψ R Δ).evalEval P.1 P.2 = 0) :
    (S.card : ℝ) ≤ (if Ψ ∣ twistedComp (fr : Kbar →+* Kbar) Ψ R Δ then 1 else 0) * (p : ℝ) ^ e +
      (C * √((p : ℝ) ^ e) + 2 * Dz ^ 3) := by
  classical
  have hsq : 0 ≤ C * √((p : ℝ) ^ e) := mul_nonneg hC0 (Real.sqrt_nonneg _)
  split_ifs with hdvd
  · have := hC S fun P hP => by
      obtain ⟨h0, h1, h2, h3, h4⟩ := hS P hP
      refine ⟨h0, h1, by rw [← hfr]; exact h2, by simpa [evalEval_C] using h3, ?_⟩
      rw [h4, evalEval_C, hfr]
    have h2 : (0 : ℝ) ≤ 2 * Dz ^ 3 := by positivity
    linarith
  · have := card_le_of_evalEval_eq_zero_of_not_dvd hirr hdvd hΨD hGD hΨn hGn S
      fun P hP => ⟨(hS P hP).1, hG P hP⟩
    have h1 : (S.card : ℝ) ≤ 2 * Dz ^ 3 := by exact_mod_cast this
    linarith

/-- **The counting identities over all good fibres**, from `fiber_twisted_count`. -/
theorem global_twisted_count {m : ℕ} {A X : Type*} (good : Finset A) (𝒪 : Finset X)
    (Z : A → X → Equiv.Perm (Fin m) → Prop) [∀ a Ψ π, Decidable (Z a Ψ π)]
    (hZ : ∀ a ∈ good, ∀ π, ∃! Ψ, Ψ ∈ 𝒪 ∧ Z a Ψ π) (πF : A → Equiv.Perm (Fin m)) :
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), ((good ×ˢ univ).filter fun x : A × Equiv.Perm (Fin m) =>
        Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ).card = m ! * good.card ∧
    ∑ Ψ ∈ 𝒪, ∑ τ : Equiv.Perm (Fin m), (univ.filter fun i => τ i = i).card *
      ((good ×ˢ univ).filter fun x : A × Equiv.Perm (Fin m) =>
        Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ).card =
      m ! * ∑ a ∈ good, (univ.filter fun i => πF a i = i).card := by
  classical
  have hsplit : ∀ Ψ τ, ((good ×ˢ univ).filter fun x : A × Equiv.Perm (Fin m) =>
      Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ).card =
      ∑ a ∈ good, (univ.filter fun π => Z a Ψ π ∧ πF a * π = π * τ).card := by
    intro Ψ τ
    rw [Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  simp only [hsplit, Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun Ψ _ => Finset.sum_comm, Finset.sum_comm]
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm, (fiber_twisted_count 𝒪 (Z a) (hZ a ha) (πF a)).1, mul_one]
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun Ψ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm]
    exact (fiber_twisted_count 𝒪 (Z a) (hZ a ha) (πF a)).2

/-- The final arithmetic of the lower bound. -/
theorem sub_mul_sqrt_le_of_twisted_counts {M m q S N I C B D s : ℝ} (hM : 0 < M) (hm : 0 ≤ m)
    (hs : 1 ≤ s) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D) (hI : I ≤ M * M)
    (key : M * q - m * (I * (C * s + B) + M * D) ≤ M * S) (hSN : S ≤ N) :
    q - (m * M * C + m * M * B + m * D + M) * s ≤ N := by
  have hU : 0 ≤ C * s + B := by positivity
  have h2 : m * (I * (C * s + B) + M * D) ≤ m * (M * M * (C * s + B) + M * D) := by
    gcongr
  have h3 : M * (q - m * (M * (C * s + B) + D)) ≤ M * S := by nlinarith
  have h4 : q - m * (M * (C * s + B) + D) ≤ S := le_of_mul_le_mul_left h3 hM
  have h5 : m * (M * (C * s + B) + D) ≤ (m * M * C + m * M * B + m * D + M) * s := by
    have : 0 ≤ m * M * B + m * D := by positivity
    nlinarith
  linarith

universe u

/-- **The lower bound `q - c √q` for a monic absolutely irreducible plane curve.** For every
`m` there is `c` such that for every finite field `𝔽_q` and every `g ∈ 𝔽_q[X][Y]` monic of
`Y`-degree and total degree `m`, with `∂g/∂Y ≠ 0` and `g` irreducible over `𝔽̄_q`, the curve
`g = 0` has at least `q - c √q` points in `𝔽_q²`. -/
theorem exists_card_ge_of_monic (m : ℕ) :
    ∃ c : ℝ, ∀ (F : Type u) [Field F] [Fintype F] (g : F[X][Y]), g.Monic → g.natDegree = m →
      WeightedDegreeLE 1 m g → derivative g ≠ 0 →
      Irreducible (g.map (mapRingHom (algebraMap F (AlgebraicClosure F)))) →
      (Fintype.card F : ℝ) - c * √(Fintype.card F) ≤
        ({P : F × F | g.evalEval P.1 P.2 = 0}.ncard : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, fun F _ _ g hg hgm _ _ hirr => ?_⟩
    exact (hirr.not_isUnit
      (by rw [eq_one_of_monic_natDegree_zero hg hgm, Polynomial.map_one]; exact isUnit_one)).elim
  obtain ⟨D, hD⟩ := exists_natDegree_resolvent_le.{u} m m
  set M := m.factorial
  set T := D + M
  set r := D + T * D
  choose Cf hCf using fun j => exists_card_le_add_mul_sqrt.{u} j T r
  set Cmax : ℝ := ∑ j ∈ range (M + 1), |Cf j|
  set Dz : ℕ := M * (D + D) + T + M * D + M
  set B : ℝ := 2 * (Dz : ℝ) ^ 3
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hB0 : 0 ≤ B := by positivity
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  refine ⟨m * M * Cmax + m * M * B + m * D + M, fun F _ _ g hg hgm hgw hgd hirr => ?_⟩
  set q := Fintype.card F
  have hsq0 : (0 : ℝ) ≤ √(q : ℝ) := Real.sqrt_nonneg _
  have hncard0 : (0 : ℝ) ≤ ({P : F × F | g.evalEval P.1 P.2 = 0}.ncard : ℝ) := by positivity
  by_cases hq : q ≤ M ^ 2
  · -- small `q`: the left side is `≤ 0`
    have h1 : √(q : ℝ) ≤ M := by
      rw [show (M : ℝ) = √((M : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
    have h2 : (q : ℝ) = √(q : ℝ) * √(q : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
    have h3 : 0 ≤ (m * M * Cmax + m * M * B + m * D : ℝ) := by positivity
    nlinarith
  push Not at hq
  -- the field `F`, its algebraic closure `Kbar` and the Frobenius `fr = (·) ^ q`
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' F
  have := hchar
  have : Fact p.Prime := ⟨hp⟩
  set alg := algebraMap F (AlgebraicClosure F)
  have : CharP (AlgebraicClosure F) p := charP_of_injective_algebraMap alg.injective p
  have : PerfectRing (AlgebraicClosure F) p := PerfectField.toPerfectRing p
  set e : ℕ := (n : ℕ)
  have he : 0 < e := n.pos
  have hqe : q = p ^ e := hcard
  set fr := iterateFrobeniusEquiv (AlgebraicClosure F) p e
  have hfrx : ∀ x, fr x = x ^ p ^ e := fun x => iterateFrobeniusEquiv_def _ p e x
  have hfrφ : ∀ a : F, fr (alg a) = alg a := fun a => by
    rw [hfrx, ← map_pow, ← hqe, FiniteField.pow_card]
  -- the curve over `Kbar`
  set f : (AlgebraicClosure F)[X][Y] := g.map (mapRingHom alg)
  have hf : f.Monic := hg.map _
  have hinjX : Function.Injective (mapRingHom alg) := Polynomial.map_injective _ alg.injective
  have hfm : f.natDegree = m := by rw [natDegree_map_eq_of_injective hinjX, hgm]
  have hfcoeff : ∀ j, (f.coeff j).natDegree ≤ m := fun j => by
    rw [coeff_map, coe_mapRingHom]
    exact natDegree_map_le.trans (hgm ▸ hgw.coeff_natDegree_le j)
  have hfd : derivative f ≠ 0 := by
    rw [derivative_map]; exact (Polynomial.map_ne_zero_iff hinjX).mpr hgd
  have hfsep : (f.map (algebraMap (AlgebraicClosure F)[X]
      (FractionRing (AlgebraicClosure F)[X]))).Separable := by
    have hirrK := (hf.isPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (AlgebraicClosure F)[X])).mp hirr
    refine (Polynomial.separable_iff_derivative_ne_zero hirrK).mpr ?_
    rw [derivative_map]
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective _ _)).mpr hfd
  have hfr : f.map (mapRingHom (fr : AlgebraicClosure F →+* AlgebraicClosure F)) = f := by
    simp only [f, Polynomial.map_map, mapRingHom_comp]
    congr 2
    exact RingHom.ext hfrφ
  -- the coefficients `cᵢ ∈ F` of the resolvent
  set S0 : Finset (AlgebraicClosure F)[X] := univ.image fun a : F => (C (alg a) : _)
  have hS0 : S0.card = q :=
    Finset.card_image_of_injective _ fun a b h => alg.injective (C_injective h)
  obtain ⟨c0, hc0S, hΔ0⟩ := exists_resolventDisc_ne_zero f hf hfm hfsep S0 (by rw [hS0]; exact hq)
  have hac : ∀ i, ∃ a : F, (C (alg a) : (AlgebraicClosure F)[X]) = c0 i := fun i => by
    simpa [S0] using hc0S i
  choose ac hac using hac
  set c' : Fin m → AlgebraicClosure F := fun i => alg (ac i)
  have hc0 : c0 = fun i => C (c' i) := _root_.funext fun i => (hac i).symm
  rw [hc0] at hΔ0
  have hc' : ∀ i, fr (c' i) = c' i := fun i => hfrφ _
  -- the factors of the resolvent and the degree bounds
  obtain ⟨𝒪, h𝒪, hprod, hcnt1, hcnt2⟩ :=
    exists_factors_galoisResolvent f hf hfm hirr hfsep fr hfr c' hc' hΔ0
  obtain ⟨hΦD, hΔD, hRD⟩ := hD _ f c' hf hfm hfcoeff
  set Φ := galoisResolvent f fun i => C (c' i)
  set Δ := resolventDisc f fun i => C (c' i)
  -- the good fibres
  set good : Finset F := univ.filter fun a => Δ.eval (alg a) ≠ 0
  have hgood : (q : ℝ) - D ≤ good.card := by
    have hbad : (univ.filter fun a : F => ¬ Δ.eval (alg a) ≠ 0).card ≤ D := by
      refine (Finset.card_le_card_of_injOn alg (t := Δ.roots.toFinset) (fun a ha => ?_)
        alg.injective.injOn).trans ((Multiset.toFinset_card_le _).trans
          ((card_roots' _).trans hΔD))
      have ha' := (Finset.mem_filter.mp ha).2
      push Not at ha'
      exact Multiset.mem_toFinset.mpr ((mem_roots hΔ0).mpr ha')
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset F))
      (fun a => Δ.eval (alg a) ≠ 0)
    rw [Finset.card_univ] at this
    have h' : (q : ℝ) = good.card + (univ.filter fun a : F => ¬ Δ.eval (alg a) ≠ 0).card := by
      exact_mod_cast this.symm
    have h'' : ((univ.filter fun a : F => ¬ Δ.eval (alg a) ≠ 0).card : ℝ) ≤ D := by
      exact_mod_cast hbad
    linarith
  -- the labelled fibres and the Frobenius permutations
  have hfib : ∀ a ∈ good, ∃ b : Fin m → AlgebraicClosure F, ∃ πa : Equiv.Perm (Fin m),
      f.map (evalRingHom (alg a)) = ∏ i, (X - C (b i)) ∧ Function.Injective b ∧
      Function.Injective (fun π : Equiv.Perm (Fin m) => ∑ i, c' i * b (π i)) ∧
      Φ.map (evalRingHom (alg a)) = ∏ π : Equiv.Perm (Fin m), (X - C (∑ i, c' i * b (π i))) ∧
      (∀ τ π : Equiv.Perm (Fin m), (resolventPerm f (fun i => C (c' i)) τ).evalEval (alg a)
        (∑ i, c' i * b (π i)) = Δ.eval (alg a) * ∑ i, c' i * b ((π * τ) i)) ∧
      (∀ i, b (πa i) = fr (b i)) ∧
      ∀ π : Equiv.Perm (Fin m), fr (∑ i, c' i * b (π i)) = ∑ i, c' i * b ((πa * π) i) := by
    intro a ha
    obtain ⟨b, hb, hbinj, hu, hΦa, hRa⟩ :=
      exists_fibre_labelling hf hfm c' (Finset.mem_filter.mp ha).2
    obtain ⟨πa, h1, h2⟩ := exists_frobenius_perm fr hfr (hfrφ a) hb hbinj c' hc'
    exact ⟨b, πa, hb, hbinj, hu, hΦa, hRa, h1, h2⟩
  choose! bF πF hbF using hfib
  set u : F → Equiv.Perm (Fin m) → AlgebraicClosure F := fun a π => ∑ i, c' i * bF a (π i)
  set Z : F → (AlgebraicClosure F)[X][Y] → Equiv.Perm (Fin m) → Prop :=
    fun a Ψ π => Ψ.evalEval (alg a) (u a π) = 0
  have hZ : ∀ a ∈ good, ∀ π, ∃! Ψ, Ψ ∈ 𝒪 ∧ Z a Ψ π := fun a ha π =>
    (existsUnique_factor_root hprod (hbF a ha).2.2.1 (hbF a ha).2.2.2.1 π).1
  have hsimple : ∀ a ∈ good, ∀ π, ∀ Ψ ∈ 𝒪, Z a Ψ π →
      (derivative Ψ).evalEval (alg a) (u a π) ≠ 0 := fun a ha π =>
    (existsUnique_factor_root hprod (hbF a ha).2.2.1 (hbF a ha).2.2.2.1 π).2
  -- degree bounds for the factors and the twists
  have hΦmon : Φ.Monic := galoisResolvent_monic _ _
  have hΦdeg : Φ.natDegree = M := by
    obtain ⟨b, hb⟩ := exists_eq_prod_X_sub_C m (hf.map (evalRingHom (0 : AlgebraicClosure F)))
      (by rw [hf.natDegree_map, hfm])
    have h := (galoisResolvent_spec f (fun i => C (c' i)) (evalRingHom 0) b hb).1
    rw [← hΦmon.natDegree_map (evalRingHom 0)]
    show (Φ.map _).natDegree = M
    rw [h, natDegree_prod_of_monic _ _ fun π _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, smul_eq_mul, mul_one, M]
  have hΦw : WeightedDegreeLE 1 T Φ := fun j hj => by
    have hjM : j ≤ M := hΦdeg ▸ le_natDegree_of_ne_zero hj
    have := hΦD j
    simp only [T]; omega
  have h𝒪deg : ∀ Ψ ∈ 𝒪, Ψ.natDegree ≤ M ∧ WeightedDegreeLE 1 T Ψ := by
    intro Ψ hΨ
    have hdvd : Ψ ∣ Φ := hprod ▸ Finset.dvd_prod_of_mem _ hΨ
    exact ⟨hΦdeg ▸ natDegree_le_of_dvd hdvd hΦmon.ne_zero,
      WeightedDegreeLE.of_dvd hΦmon.ne_zero hdvd hΦw⟩
  have h𝒪w : ∀ Ψ ∈ 𝒪, WeightedDegreeLE T (T * Ψ.natDegree) Ψ := by
    intro Ψ hΨ j hj
    have hj' : j ≤ Ψ.natDegree := le_natDegree_of_ne_zero hj
    rcases hj'.lt_or_eq with hlt | heq
    · have h1 := (h𝒪deg Ψ hΨ).2.coeff_natDegree_le j
      have : T * j + T ≤ T * Ψ.natDegree := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · subst heq
      rw [(h𝒪 Ψ hΨ).1.coeff_natDegree, natDegree_one, zero_add]
  have hRw : ∀ τ, WeightedDegreeLE T r (resolventPerm f (fun i => C (c' i)) τ) := by
    intro τ j hj
    have hj' : j ≤ D := (le_natDegree_of_ne_zero hj).trans (hRD τ).1
    exact Nat.add_le_add ((hRD τ).2 j) (Nat.mul_le_mul_left T hj')
  have hΔw : WeightedDegreeLE T r (C Δ : (AlgebraicClosure F)[X][Y]) :=
    WeightedDegreeLE.C (hΔD.trans (Nat.le_add_right _ _))
  -- the point sets and their bounds
  set G : (AlgebraicClosure F)[X][Y] → Equiv.Perm (Fin m) → (AlgebraicClosure F)[X][Y] :=
    fun Ψ τ => twistedComp (fr : AlgebraicClosure F →+* AlgebraicClosure F) Ψ
      (resolventPerm f (fun i => C (c' i)) τ) Δ
  set Fset : (AlgebraicClosure F)[X][Y] → Equiv.Perm (Fin m) → Finset (F × Equiv.Perm (Fin m)) :=
    fun Ψ τ => (good ×ˢ univ).filter fun x => Z x.1 Ψ x.2 ∧ πF x.1 * x.2 = x.2 * τ
  have hq' : (q : ℝ) = (p : ℝ) ^ e := by rw [hqe]; push_cast; ring
  have hbound : ∀ Ψ ∈ 𝒪, ∀ τ, ((Fset Ψ τ).card : ℝ) ≤
      (if Ψ ∣ G Ψ τ then 1 else 0) * (q : ℝ) + (Cmax * √(q : ℝ) + B) := by
    intro Ψ hΨ τ
    set Sset := (Fset Ψ τ).image fun x => (alg x.1, u x.1 x.2)
    have hcard : Sset.card = (Fset Ψ τ).card := by
      refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
      have hx' := (Finset.mem_filter.mp hx).1
      have hy' := (Finset.mem_filter.mp hy).1
      simp only [Prod.mk.injEq] at hxy
      have h1 : x.1 = y.1 := alg.injective hxy.1
      have hxg : x.1 ∈ good := (Finset.mem_product.mp hx').1
      have h2 : x.2 = y.2 := (hbF x.1 hxg).2.2.1 (by
        have := hxy.2; simp only [u] at this; rw [h1] at this ⊢; exact this)
      exact Prod.ext h1 h2
    -- the points of `Sset` satisfy the hypotheses of the one-factor bound
    have hS' : ∀ P ∈ Sset, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
        fr P.1 = P.1 ∧ Δ.eval P.1 ≠ 0 ∧ (resolventPerm f (fun i => C (c' i)) τ).evalEval P.1 P.2 =
          Δ.eval P.1 * fr P.2 := fun P hP => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨hx1, hx2, hx3⟩ := Finset.mem_filter.mp hx
      have hxg : x.1 ∈ good := (Finset.mem_product.mp hx1).1
      refine ⟨hx2, hsimple x.1 hxg x.2 Ψ hΨ hx2, hfrφ x.1, (Finset.mem_filter.mp hxg).2, ?_⟩
      simp only [u]
      rw [(hbF x.1 hxg).2.2.2.2.1 τ x.2, (hbF x.1 hxg).2.2.2.2.2.2 x.2, hx3]
    rw [← hcard, hq']
    refine card_le_of_twisted_points p fr hfrx (h𝒪 Ψ hΨ).2 hCmax0 (fun S hS => ?_)
      (fun j => ((h𝒪deg Ψ hΨ).2.coeff_natDegree_le j).trans (by simp only [Dz]; omega))
      ((h𝒪deg Ψ hΨ).1.trans (by simp only [Dz]; omega)) (fun j => ?_) ?_ Sset hS'
      (fun P hP => ?_)
    · -- Stepanov's bound for the factor `Ψ`
      by_cases hd : derivative Ψ = 0
      · have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun P hP =>
          (hS P hP).2.1 (by rw [hd]; simp)
        rw [hS0, Finset.card_empty, Nat.cast_zero]
        positivity
      · have h := hCf Ψ.natDegree (AlgebraicClosure F) p e he Ψ
          (resolventPerm f (fun i => C (c' i)) τ) (C Δ) (h𝒪 Ψ hΨ).1 (h𝒪 Ψ hΨ).2 hd rfl
          (h𝒪w Ψ hΨ) (hRw τ) hΔw S hS
        have hCle : Cf Ψ.natDegree ≤ Cmax :=
          (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
            (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (h𝒪deg Ψ hΨ).1)))
        nlinarith [Real.sqrt_nonneg ((p : ℝ) ^ e)]
    · -- the coefficients of the twisted composite
      have hw0 := weightedDegreeLE_zero_twistedComp (fr : AlgebraicClosure F →+* AlgebraicClosure F)
        (Ψ := Ψ) (R := resolventPerm f (fun i => C (c' i)) τ) (Δ := Δ) (DΨ := T) (DR := D)
        (DΔ := D) (fun j _ => by simpa using (h𝒪deg Ψ hΨ).2.coeff_natDegree_le j)
        (fun j _ => by simpa using (hRD τ).2 j) hΔD
      refine (hw0.coeff_natDegree_le j).trans ?_
      have : Ψ.natDegree * (D + D) ≤ M * (D + D) := Nat.mul_le_mul_right _ (h𝒪deg Ψ hΨ).1
      simp only [Dz]; omega
    · refine (natDegree_twistedComp_le _ _ _ _).trans ?_
      have : Ψ.natDegree * (resolventPerm f (fun i => C (c' i)) τ).natDegree ≤ M * D :=
        Nat.mul_le_mul (h𝒪deg Ψ hΨ).1 (hRD τ).1
      simp only [Dz]; omega
    · obtain ⟨h0, -, h2, -, h4⟩ := hS' P hP
      rw [evalEval_twistedComp _ _ _ _ h2 h4, h0, map_zero, mul_zero]
  -- the fixed points of the Frobenius permutations are the `F`-points of `g`
  have hfix : ∀ a ∈ good, (univ.filter fun i => πF a i = i).card =
      (univ.filter fun y : F => g.evalEval a y = 0).card := by
    intro a ha
    obtain ⟨hb, hbinj, -, -, -, hπ1, -⟩ := hbF a ha
    have hroot : ∀ x, f.evalEval (alg a) x = ∏ i, (x - bF a i) := fun x => by
      rw [← map_evalRingHom_eval, hb, eval_prod]; simp
    have halg : ∀ y : F, f.evalEval (alg a) (alg y) = alg (g.evalEval a y) := fun y =>
      map_mapRingHom_evalEval alg g a y
    have himg : (univ.filter fun i => πF a i = i).image (bF a) =
        (univ.filter fun y : F => g.evalEval a y = 0).image alg := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hfixi : fr (bF a i) = bF a i := by rw [← hπ1, hi]
        obtain ⟨y, hy⟩ := FiniteField.exists_algebraMap_eq_of_pow_card_eq (F := F)
          (x := bF a i) (by
            have h := hfrx (bF a i)
            rw [hfixi, ← hqe] at h
            exact h.symm)
        refine ⟨y, alg.injective ?_, hy⟩
        rw [map_zero, ← halg, hy, hroot]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
      · rintro ⟨y, hy, rfl⟩
        have h0 : ∏ i, (alg y - bF a i) = 0 := by rw [← hroot, halg, hy, map_zero]
        obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h0
        have hi' : alg y = bF a i := sub_eq_zero.mp hi
        refine ⟨i, hbinj ?_, hi'.symm⟩
        rw [hπ1, ← hi', hfrφ]
    rw [← Finset.card_image_of_injective _ hbinj, himg,
      Finset.card_image_of_injective _ alg.injective]
  -- the `F`-points over the good fibres
  have hpoints : ∑ a ∈ good, (univ.filter fun y : F => g.evalEval a y = 0).card ≤
      {P : F × F | g.evalEval P.1 P.2 = 0}.ncard := by
    rw [← Finset.card_sigma]
    have := Finset.card_le_card_of_injOn (fun x : Σ _ : F, F => (x.1, x.2))
      (s := good.sigma fun a => univ.filter fun y : F => g.evalEval a y = 0)
      (t := univ.filter fun P : F × F => g.evalEval P.1 P.2 = 0)
      (fun x hx => by
        obtain ⟨-, h⟩ := Finset.mem_sigma.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
      (fun x _ y _ h => by
        simp only [Prod.mk.injEq] at h
        exact Sigma.ext h.1 (heq_of_eq h.2))
    refine this.trans (le_of_eq ?_)
    rw [← Set.ncard_coe_finset]
    congr 1
    ext P
    simp
  -- the number of factors
  have h𝒪card : 𝒪.card ≤ M := by
    calc 𝒪.card = ∑ Ψ ∈ 𝒪, 1 := by simp
      _ ≤ ∑ Ψ ∈ 𝒪, Ψ.natDegree := Finset.sum_le_sum fun Ψ hΨ =>
          (h𝒪 Ψ hΨ).1.natDegree_pos_of_not_isUnit (h𝒪 Ψ hΨ).2.not_isUnit
      _ = Φ.natDegree := by
          rw [← hprod, natDegree_prod_of_monic _ _ fun Ψ hΨ => (h𝒪 Ψ hΨ).1]
      _ = M := hΦdeg
  -- the bookkeeping
  obtain ⟨hsum1, hsum2⟩ := global_twisted_count good 𝒪 Z hZ πF
  set I := 𝒪 ×ˢ (univ : Finset (Equiv.Perm (Fin m)))
  set sF : (AlgebraicClosure F)[X][Y] × Equiv.Perm (Fin m) → ℝ :=
    fun x => ((Fset x.1 x.2).card : ℝ)
  set eF : (AlgebraicClosure F)[X][Y] × Equiv.Perm (Fin m) → ℝ :=
    fun x => if x.1 ∣ G x.1 x.2 then 1 else 0
  set fF : (AlgebraicClosure F)[X][Y] × Equiv.Perm (Fin m) → ℝ :=
    fun x => ((univ.filter fun i => x.2 i = i).card : ℝ)
  have hU : 0 ≤ Cmax * √(q : ℝ) + B := by positivity
  have hs : ∀ x ∈ I, sF x ≤ eF x * q + (Cmax * √(q : ℝ) + B) := fun x hx =>
    hbound x.1 (Finset.mem_product.mp hx).1 x.2
  have hfF : ∀ x ∈ I, 0 ≤ fF x ∧ fF x ≤ m := fun x _ => ⟨by positivity, by
    have := Finset.card_filter_le (univ : Finset (Fin m)) fun i => x.2 i = i
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simp only [fF]
    exact_mod_cast this⟩
  have hsumI : ∑ x ∈ I, sF x = M * good.card := by
    rw [Finset.sum_product]
    simp only [sF]
    exact_mod_cast hsum1
  have heI : ∑ x ∈ I, eF x = M := by
    rw [Finset.sum_product]
    simp only [eF, Finset.sum_boole]
    exact_mod_cast hcnt1
  have hfeI : ∑ x ∈ I, fF x * eF x = M := by
    rw [Finset.sum_product]
    simp only [fF, eF, mul_ite, mul_one, mul_zero]
    simp only [← Finset.sum_filter]
    exact_mod_cast hcnt2
  have hfsI : ∑ x ∈ I, fF x * sF x =
      M * ∑ a ∈ good, ((univ.filter fun y : F => g.evalEval a y = 0).card : ℝ) := by
    rw [Finset.sum_product]
    have h := congrArg (Nat.cast : ℕ → ℝ) hsum2
    push_cast at h
    rw [Finset.sum_congr rfl fun a ha => (congrArg (Nat.cast : ℕ → ℝ) (hfix a ha)).symm]
    exact h
  have key := le_of_twisted_counts I sF eF fF hs hfF hsumI hgood heI hfeI hU (by positivity)
    (by positivity) (by positivity)
  rw [hfsI] at key
  have hpts : ∑ a ∈ good, ((univ.filter fun y : F => g.evalEval a y = 0).card : ℝ) ≤
      ({P : F × F | g.evalEval P.1 P.2 = 0}.ncard : ℝ) := by exact_mod_cast hpoints
  have hIcard : (I.card : ℝ) ≤ M * M := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    exact_mod_cast Nat.mul_le_mul_right _ h𝒪card
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hsq1 : (1 : ℝ) ≤ √(q : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast Fintype.card_pos
  exact sub_mul_sqrt_le_of_twisted_counts hMpos (by positivity) hsq1 hCmax0 hB0 (by positivity)
    hIcard key hpts

end Polynomial.Bivariate

end

-- Bundled module: StacksFrontier.RingTheory.Polynomial.StepanovBound
section




/-!
# The Weil lower bound for absolutely irreducible plane curves

Let `F` be a finite field with `q` elements and let `f ∈ F[x, y]` be irreducible over an algebraic
closure of `F`, of total degree at most `d`. Then `f` has at least `q - c √q` zeros in `F²`, where
`c` depends only on `d`.

## Main results

* `MvPolynomial.exists_card_zeroSet_ge_of_absolutelyIrreducible`: the Weil lower bound for
  absolutely irreducible plane curves.
-/


open Polynomial
open scoped Polynomial.Bivariate

universe u

namespace MvPolynomial

open Polynomial.Bivariate

/-- **The Weil lower bound for absolutely irreducible plane curves.** There is `c`, depending
only on `d`, such that over every finite field `F` with `q` elements every `f ∈ F[x, y]` of total
degree at most `d` which is irreducible over an algebraic closure of `F` has at least `q - c √q`
zeros in `F²`. -/
theorem exists_card_zeroSet_ge_of_absolutelyIrreducible (d : ℕ) :
    ∃ c : ℝ, ∀ (F : Type u) [Field F] [Fintype F] (f : MvPolynomial (Fin 2) F),
      f.totalDegree ≤ d → Irreducible (f.map (algebraMap F (AlgebraicClosure F))) →
      (Fintype.card F : ℝ) - c * √(Fintype.card F) ≤
        ({p : Fin 2 → F | MvPolynomial.eval p f = 0}.ncard : ℝ) := by
  choose cm hcm using fun m => Polynomial.Bivariate.exists_card_ge_of_monic.{u} m
  set S : ℝ := ∑ m ∈ Finset.range (d + 1), |cm m|
  have hS : 0 ≤ S := Finset.sum_nonneg fun m _ => abs_nonneg (cm m)
  refine ⟨S + √(d + 2), fun F _ _ f hfd hirr => ?_⟩
  have hsq := Real.sqrt_nonneg (Fintype.card F : ℝ)
  have hss : √(Fintype.card F : ℝ) * √(Fintype.card F) = Fintype.card F :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  rcases le_or_gt (Fintype.card F) (d + 1) with hq | hq
  · have hle : √(Fintype.card F : ℝ) ≤ √(d + 2) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (by omega : Fintype.card F ≤ d + 2))
    have : (Fintype.card F : ℝ) ≤ (S + √(d + 2)) * √(Fintype.card F) := by
      nlinarith [mul_le_mul_of_nonneg_right hle hsq]
    exact (sub_nonpos.mpr this).trans (Nat.cast_nonneg _)
  · obtain ⟨g, hmon, -, hnat, hw, hder, hirr', hcard⟩ :=
      exists_monic_normalization f hirr (lt_of_le_of_lt (by omega) hq)
    rw [hnat] at hw
    have h := hcm f.totalDegree F g hmon hnat hw hder hirr'
    rw [← hcard] at h
    have hcS : cm f.totalDegree ≤ S + √(d + 2) :=
      (le_abs_self _).trans ((Finset.single_le_sum (fun m _ => abs_nonneg (cm m))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hfd))).trans
          (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    nlinarith [mul_le_mul_of_nonneg_right hcS hsq]

end MvPolynomial

end

-- Bundled module: ComponentCount
section


open MvPolynomial
namespace E707Geometry
universe u
/-- Uniform half-field threshold; the zero set counted may be enlarged to an ambient locus. -/
theorem halfCountOfComponent (d : ℕ) : ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F]
    (p : MvPolynomial (Fin 2) F) (S : Set (Fin 2 → F)), Q ≤ Fintype.card F →
    p.totalDegree ≤ d → Irreducible (p.map (algebraMap F (AlgebraicClosure F))) →
    {v | eval v p = 0} ⊆ S → Fintype.card F ≤ 2*S.ncard := by
  obtain ⟨c,hc⟩ := exists_card_zeroSet_ge_of_absolutelyIrreducible.{u} d
  obtain ⟨Q,hQ⟩ := exists_nat_gt ((2*|c|+1)^2)
  refine ⟨Q,?_⟩
  intro F _ _ p S hq hd hi hsub
  have hp := hc F p hd hi
  have hm := Set.ncard_le_ncard hsub (Set.toFinite S)
  let q : ℝ := Fintype.card F
  have hh : (2*|c|+1)^2 < q := hQ.trans_le (by dsimp [q]; exact_mod_cast hq)
  have hs : (Real.sqrt q)^2 = q := Real.sq_sqrt (by positivity)
  have hroot : 2*c ≤ Real.sqrt q := by
    have hpos := abs_nonneg c
    have hle := le_abs_self c
    have hnn := Real.sqrt_nonneg q
    by_contra! hn
    have hbad : (Real.sqrt q)^2 ≤ (2*|c|+1)^2 := by gcongr <;> linarith
    linarith
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg q)
  have hm' : (({v : Fin 2 → F | eval v p = 0} : Set _).ncard : ℝ) ≤ S.ncard := by exact_mod_cast hm
  change q - c*Real.sqrt q ≤ _ at hp
  have : (Fintype.card F : ℝ) ≤ 2*(S.ncard : ℝ) := by change q ≤ _; nlinarith
  exact_mod_cast this
end E707Geometry

end

-- Bundled module: StableCount
section



open MvPolynomial IntermediateField
namespace E707Geometry
universe u
variable {F : Type u} [Field F] [Fintype F]
/-- Even in the infinite algebraic closure the q-Frobenius fixes exactly F. -/
theorem closureFrobFixed (z : AlgebraicClosure F) (hz : z ^ Fintype.card F = z) :
    ∃ a : F, algebraMap F _ a = z := by
  let L := F⟮z⟯
  let w : L := ⟨z, mem_adjoin_simple_self _ _⟩
  let : FiniteDimensional F L := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  let : Finite L := Module.finite_of_finite F
  obtain ⟨a,ha⟩ := E707Partial.frobFixed (F := F) w (Subtype.ext hz)
  exact ⟨a, congrArg Subtype.val ha⟩

/-- A Frobenius-stable geometric component already supplies the uniform point lower bound. -/
theorem halfCountStable (d : ℕ) : ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F]
    (p : MvPolynomial (Fin 2) (AlgebraicClosure F)), Q ≤ Fintype.card F →
    p.totalDegree ≤ d → Irreducible p →
    Associated p (p.map (FiniteField.frobeniusAlgHom F _).toRingHom) →
    Fintype.card F ≤ 2*({v : Fin 2 → F | eval (algebraMap F _ ∘ v) p = 0} : Set _).ncard := by
  obtain ⟨Q,hQ⟩ := halfCountOfComponent.{u} d
  refine ⟨Q,?_⟩
  intro F _ _ p hq hd hi ha
  let i := algebraMap F (AlgebraicClosure F)
  obtain ⟨f,hf⟩ := descendAssociated (FiniteField.frobeniusAlgHom F _).toRingHom
    (closureFrobFixed (F := F)) p hi.ne_zero ha
  apply hQ F f _ hq _ (hf.irreducible hi)
  · intro v hv
    have hzero : eval (i ∘ v) (f.map i) = 0 := by
      change eval v f = 0 at hv
      rw [eval_map, ← eval₂_comp,hv,map_zero]
    obtain ⟨g,hg⟩ := hf.dvd'
    change eval (i ∘ v) p = 0
    rw [hg,map_mul,hzero,zero_mul]
  · have H := totalDegree_le_of_dvd_of_isDomain hf.dvd' hi.ne_zero
    simpa only [totalDegree,support_map_of_injective _ (algebraMap F (AlgebraicClosure F)).injective] using H.trans hd
end E707Geometry


end

-- Bundled module: TwistAssociated
section

open MvPolynomial
namespace E707Geometry
variable {K I J : Type*} [Field K]
/-- Coefficient Frobenius on the substituted equation rotates the coordinate forms.
Stability of both split-coordinate actions therefore gives stability on the chart. -/
theorem twistAssociated (σ : K →+* K) (r : I → I) (L : I → MvPolynomial J K)
    (cycle : ∀ i, map σ (L i) = L (r i)) (p : MvPolynomial I K)
    (hc : Associated p (p.map σ)) (hr : Associated p (rename r p)) :
    Associated (aeval L p) (map σ (aeval L p)) := by
  have commute (f : MvPolynomial I K) :
      map σ (aeval L f) = aeval L (rename r (f.map σ)) := by
    induction f using MvPolynomial.induction_on with
    | C a => simp [aeval_C]
    | add f g hf hg => simp only [map_add,hf,hg]
    | mul_X f i hf => simp only [map_mul,aeval_X,map_X,rename_X,hf,cycle]
  rw [commute]
  exact (hr.trans (hc.map (rename r).toRingHom.toMonoidHom)).map (aeval L).toRingHom.toMonoidHom
end E707Geometry

end

-- Bundled module: Axis
section


namespace E707Geometry
open Polynomial
/-- Sawin axis section: the polynomial quotient has a simple zero outside both other axes. -/
theorem transverse {K : Type*} [Field K] [IsSepClosed K] {m c e : ℕ}
    [NeZero (m : K)] (hc : 0 < c) (hcm : c < m) (F : K[X])
    (hid : F * (X^c-1) = X^e*(X^m-1)) :
    ∃ t : K, t ≠ 0 ∧ t^c ≠ 1 ∧ F.eval t = 0 ∧ F.derivative.eval t ≠ 0 := by
  obtain ⟨t,ht⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have hm : 0 < m := by omega
  have ht0 : t ≠ 0 := by intro h; simpa [h, hm.ne'] using ht.pow_eq_one
  have htc : t^c ≠ 1 := fun h => (Nat.not_dvd_of_pos_of_lt hc hcm) ((ht.pow_eq_one_iff_dvd c).mp h)
  have hv := congrArg (eval t) hid
  simp [ht.pow_eq_one] at hv
  have hF : F.eval t = 0 := hv.resolve_right (sub_ne_zero.mpr htc)
  refine ⟨t, ht0, htc, hF, ?_⟩
  intro hd
  have hdv := congrArg (fun P : K[X] => P.derivative.eval t) hid
  simp [derivative_mul, derivative_sub, derivative_X_pow, ht.pow_eq_one, hd,hF,
    ht0, NeZero.ne (m:K)] at hdv

/-- The specialized alternant divided by the specialized Vandermonde. -/
theorem determinantAxis {K : Type*} [Field K] [IsSepClosed K] {a b c : ℕ}
    (hc : 0 < c) (hca : c ≤ a) (hab : a ≤ b) (hlt : c < b-a)
    [NeZero ((b-a : ℕ) : K)] (F : K[X])
    (hspec : F * (X^c * (X^c-1)) = X^b-X^a) :
    ∃ t : K, t ≠ 0 ∧ t^c ≠ 1 ∧ F.eval t = 0 ∧ F.derivative.eval t ≠ 0 := by
  apply transverse (m := b-a) (e := a-c) hc hlt
  apply mul_left_cancel₀ (pow_ne_zero c (X_ne_zero : (X : K[X]) ≠ 0))
  calc
    X^c * (F * (X^c - 1)) = F * (X^c * (X^c-1)) := by ring
    _ = X^b-X^a := hspec
    _ = X^c*(X^(a-c)*(X^(b-a)-1)) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hca, mul_sub, ← pow_add,
        Nat.add_sub_of_le hab, mul_one]


/-- Specialization at y=0 of the alternant/Vandermonde identity in K[x][y]. -/
theorem axisOfAlternant {K : Type*} [Field K] [IsSepClosed K] {a b c : ℕ}
    (hc : 0 < c) (hca : c ≤ a) (hab : a ≤ b) (hlt : c < b-a)
    [NeZero ((b-a : ℕ) : K)] (P : (K[X])[X])
    (hP : let x := C (X : K[X]); let y : (K[X])[X] := X
          P*((x^c-1)*(y^c-1)*(y^c-x^c)) =
          (x^a-1)*(y^b-1)-(y^a-1)*(x^b-1)) :
    ∃ t : K, t ≠ 0 ∧ t^c ≠ 1 ∧ (P.eval 0).eval t = 0 ∧
      (P.eval 0).derivative.eval t ≠ 0 := by
  apply determinantAxis hc hca hab hlt
  have he := congrArg (eval (0 : K[X])) hP
  have ha : a ≠ 0 := by omega
  have hb : b ≠ 0 := by omega
  simp [ha,hb,hc.ne'] at he
  linear_combination he

end E707Geometry



end

-- Bundled module: SmoothPoint707
section


namespace E707Monge
open E707Geometry Polynomial
/-- Axis section of the actual quotient: the transverse point is constructed,
    not an assumption on its specialization. -/
theorem existsSmoothAxis {K : Type*} [Field K] [IsSepClosed K] (c u v : ℕ)
    (hc : 0<c) (hu : c ≤ c*u) (huv : c*u ≤ c*v) (hlt : c<c*v-c*u)
    [NeZero ((c*v-c*u:ℕ):K)] :
    let F := altQuot (1+(X:K[X])^c) (X^c) 0 u v
    ∃ t : K, t ≠ 0 ∧ t^c ≠ 1 ∧ F.eval t = 0 ∧ F.derivative.eval t ≠ 0 := by
  intro F
  apply determinantAxis hc hu huv hlt
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu; omega
  have hv0 : v ≠ 0 := by rintro rfl; simp at hlt
  have h := altQuot_spec (1 : K[X]) (X^c) 0 u v
  simp only [one_mul,mul_zero,zero_mul,add_zero,zero_sub,one_pow,zero_pow hu0,zero_pow hv0,sub_zero] at h
  simp only [F,pow_mul]
  linear_combination h
end E707Monge

end

-- Bundled module: AxisFactor707
section

namespace E707Monge
open E707Geometry Polynomial
variable {K : Type*} [Field K]
noncomputable def planeQ (c u v : ℕ) : K[X][X] :=
  let x := C ((X:K[X])^c); let z := (X:K[X][X])^c
  altQuot (1+x+z) (x+x*z+z) (x*z) u v

theorem mapQ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s t w : R) (u v : ℕ) :
    f (altQuot s t w u v) = altQuot (f s) (f t) (f w) u v := by
  have h (n : ℕ) : let a := cubicRem s t w n; let b := cubicRem (f s) (f t) (f w) n
                    f a.1 = b.1 ∧ f a.2.1 = b.2.1 ∧ f a.2.2 = b.2.2 := by
    induction n with
    | zero => simp [cubicRem]
    | succ n ih => dsimp only [cubicRem] at *; simp [ih]
  simp only [altQuot,map_sub,map_mul,(h u).2.1,(h u).2.2,(h v).2.1,(h v).2.2]

theorem primeAtRoot {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]
    (e : R →+* K) (P : R) (hn : P ≠ 0) (hz : e P = 0) :
    ∃ i : R, Irreducible i ∧ i ∣ P ∧ e i = 0 := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit u hu => exact False.elim ((hu.map e).ne_zero hz)
  | mul a i ha hi ih =>
    rw [map_mul,mul_eq_zero] at hz
    rcases hz with h|h
    · exact ⟨i,hi,dvd_mul_right _ _,h⟩
    · obtain ⟨j,hj,hd,he⟩ := ih ha h
      exact ⟨j,hj,hd.trans (dvd_mul_left _ _),he⟩

/-- A geometric component crossing the axis away from the diagonals, unconditionally.
    The cyclic invariance of this component is a separate question. -/
theorem existsAxisFactor [IsAlgClosed K] (c u v : ℕ)
    (hc : 0<c) (hu : c ≤ c*u) (huv : c*u ≤ c*v) (hlt : c<c*v-c*u)
    [NeZero ((c*v-c*u:ℕ):K)] :
    ∃ (t : K) (f g : K[X][X]), t≠0 ∧ t^c ≠ 1 ∧ Irreducible f ∧ planeQ c u v = f*g ∧
      (f.eval 0).eval t = 0 ∧ (f.eval 0).derivative.eval t ≠ 0 ∧ (g.eval 0).eval t ≠ 0 := by
  let Q := planeQ (K:=K) c u v
  have haxis : Q.eval 0 = altQuot (1+(X:K[X])^c) (X^c) 0 u v := by
    change evalRingHom 0 _ = _
    simp only [Q,planeQ,mapQ,map_add,map_mul,coe_evalRingHom,eval_one,eval_C,eval_pow,eval_X,zero_pow hc.ne',mul_zero,add_zero]
  obtain ⟨t,ht,htc,hz,hd⟩ := existsSmoothAxis (K:=K) c u v hc hu huv hlt
  rw [← haxis] at hz hd
  have hn : Q ≠ 0 := by intro h; simp [h] at hd
  let e := (evalRingHom t).comp (evalRingHom (0 : K[X]))
  obtain ⟨f,hf,⟨g,hg⟩,he⟩ := primeAtRoot e Q hn hz
  change (f.eval 0).eval t = 0 at he
  rw [hg,eval_mul,derivative_mul,eval_add,eval_mul,eval_mul,he,zero_mul,add_zero] at hd
  exact ⟨t,f,g,ht,htc,hf,hg,he,left_ne_zero_of_mul hd,right_ne_zero_of_mul hd⟩
end E707Monge

end

-- Bundled module: PlaneTop707
section


namespace E707Monge
open Polynomial E707Geometry
variable {K : Type*} [Field K]
theorem planeTop (c u v : ℕ) (hc : 0<c) (ha : 0<c*u) (hab : c*u<c*v) :
    let Q := planeQ (K:=K) c u v
    Q.natDegree + 2*c = c*v ∧ Q.leadingCoeff * ((X:K[X])^c-1) = X^(c*u)-1 := by
  intro Q
  let y : K[X] := X
  let A := y^(c*u)-1; let B := y^(c*v)-1; let D := y^c-1
  let V := (X^c-1 : K[X][X])*(X^c-C (y^c))
  have eqn : Q*(C D*V) = C A*X^(c*v) - C B*X^(c*u) + C (B-A) := by
    have h := altQuot_spec (1 : K[X][X]) (C (y^c)) (X^c) u v
    simp only [one_pow,one_mul,mul_one,←map_pow,←pow_mul] at h
    dsimp only [Q,planeQ,A,B,D,V,y] at *
    simp only [map_sub,map_one]; linear_combination h
  have n (k : ℕ) (hk : 0<k) : y^k-1 ≠ 0 := by
    intro he; have hh := congrArg (fun f : K[X] => f.coeff k) he
    simp [y,coeff_one,hk.ne',eq_comm] at hh
  have hD := C_ne_zero.mpr (n c hc)
  have hA := C_ne_zero.mpr (n (c*u) ha)
  have mV : V.Monic := (monic_X_pow_sub_C 1 hc.ne').mul (monic_X_pow_sub_C _ hc.ne')
  have dV : V.natDegree=2*c := by
    dsimp only [V]; rw [← C_1, natDegree_mul (monic_X_pow_sub_C (1 : K[X]) hc.ne').ne_zero (monic_X_pow_sub_C _ hc.ne').ne_zero]; rw [natDegree_X_pow_sub_C,natDegree_X_pow_sub_C]; omega
  let T := C A * X^(c*v)
  let L := -C B * X^(c*u) + C (B-A)
  have hdT : T.natDegree = c*v := by dsimp only [T]; rw [natDegree_mul (show C A ≠ 0 from hA) (pow_ne_zero _ X_ne_zero),natDegree_C,natDegree_X_pow,zero_add]
  have hdL : L.natDegree ≤ c*u := by
    apply natDegree_add_le_of_degree_le <;> first | exact (natDegree_mul_le.trans (by simp)) | simp
  have hlt : L.natDegree < T.natDegree := by omega
  have eq' : Q*(C D*V) = T+L := by rw [eqn]; dsimp only [T,L]; ring
  have hne : T+L ≠ 0 := by intro hz; have hh := natDegree_add_eq_left_of_natDegree_lt hlt; rw [hz,natDegree_zero] at hh; omega
  have hQ : Q ≠ 0 := by intro hz; rw [hz,zero_mul] at eq'; exact hne eq'.symm
  constructor
  · have hh := congrArg natDegree eq'; rw [natDegree_mul hQ (mul_ne_zero hD mV.ne_zero),natDegree_mul hD mV.ne_zero,natDegree_C,zero_add,dV,natDegree_add_eq_left_of_natDegree_lt hlt,hdT] at hh; exact hh
  · have hh := congrArg leadingCoeff eq'; rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree hlt),leadingCoeff_mul,leadingCoeff_mul,mV.leadingCoeff,mul_one,leadingCoeff_C] at hh
    simpa only [T,leadingCoeff_mul,leadingCoeff_X_pow,leadingCoeff_C,mul_one] using hh
end E707Monge

end

-- Bundled module: Signatures707
section


namespace E707Monge
open E707Geometry Polynomial
variable {K : Type*} [Field K]
noncomputable def sectionQ (t : K) (c u v : ℕ) : K[X] :=
  let y := C (t^c); let z := (X:K[X])^c
  altQuot (1+y+z) (y+y*z+z) (y*z) u v
noncomputable def sectionV (t : K) (c : ℕ) : K[X] :=
  (C (t^c)-1)*(X^c-1)*(X^c-C (t^c))
theorem section_spec (t : K) (c u v : ℕ) :
  sectionQ t c u v * sectionV t c = C (t^(c*v)) - C (t^(c*u)) +
    (C (t^(c*u))*X^(c*v) - C (t^(c*v))*X^(c*u)) + (X^(c*u)-X^(c*v)) := by
  simpa only [sectionQ,sectionV,pow_mul,map_pow,one_pow,one_mul,mul_one] using
    altQuot_spec (1 : K[X]) (C (t^c)) (X^c) u v

/-- Lower signature length of the explicit quotient at a nontrivial root of t^(b-a)=1. -/
theorem lowerOrder (t : K) (c u v : ℕ) (hc : 0<c) (huv : c*u<c*v)
    (ht : t ≠ 0) (htc : t^c ≠ 1) (hroot : t^(c*u)=t^(c*v)) (hne : t^(c*u) ≠ 1) :
    (sectionQ t c u v).natTrailingDegree = c*u := by
  let d := c*v-c*u
  have hsum : c*u+d=c*v := by dsimp [d];omega
  have hd : d≠0 := by dsimp [d];omega
  have hV : (sectionV t c).eval 0 ≠ 0 := by simp [sectionV,hc.ne',ht,sub_ne_zero.mpr htc.symm]
  let T := (C (t^(c*u))-1)*((X:K[X])^d-1)
  have hT : T.eval 0 ≠ 0 := by simp [T,hd,sub_ne_zero.mpr hne.symm]
  have nonz (p : K[X]) (h : p.eval 0 ≠ 0) : p ≠ 0 := by rintro rfl; simp at h
  have tvr (p : K[X]) (h : p.eval 0 ≠ 0) : p.natTrailingDegree = 0 := by
    apply natTrailingDegree_eq_zero.mpr; right; simpa only [coeff_zero_eq_eval_zero] using h
  have he : sectionQ t c u v * sectionV t c = T*X^(c*u) := by
    rw [section_spec,← hroot,← hsum,pow_add]; unfold T; ring
  have hn : sectionQ t c u v ≠ 0 := by
    intro h; rw [h,zero_mul] at he
    exact (mul_ne_zero (nonz T hT) (pow_ne_zero _ X_ne_zero)) he.symm
  have hh := congrArg natTrailingDegree he
  simpa only [natTrailingDegree_mul hn (nonz _ hV),natTrailingDegree_mul_X_pow (nonz T hT),tvr _ hV,tvr _ hT,zero_add,add_zero] using hh

/-- At a root of t^a=1 outside t^c=1 the degree drops to a-2c. -/
theorem upperDegree (t : K) (c u v : ℕ) (hc : 0<c) (ha : 0<c*u)
    (htc : t^c ≠ 1) (hr : t^(c*u)=1) (hne : t^(c*v) ≠ 1) :
    (sectionQ t c u v).natDegree + 2*c = c*u := by
  let k := t^(c*v)-1
  have hk : k ≠ 0 := sub_ne_zero.mpr hne
  have hd (n : ℕ) (hn : 0<n) (w : K) : ((X:K[X])^n-C w).natDegree=n := by simp
  have hn (n : ℕ) (hn : 0<n) (w : K) : ((X:K[X])^n-C w) ≠ 0 := by
    intro h; have h' := hd n hn w; rw [h,natDegree_zero] at h'; omega
  have h1 (n : ℕ) (hn' : 0<n) : ((X:K[X])^n-1) ≠ 0 := by simpa using hn n hn' 1
  have hC : C (t^c-1) ≠ (0:K[X]) := by exact C_ne_zero.mpr (sub_ne_zero.mpr htc)
  have hV : sectionV t c ≠ 0 := by
    unfold sectionV; rw [← C_1, ← map_sub]; exact mul_ne_zero (mul_ne_zero hC (hn c hc 1)) (hn c hc _)
  have degV : (sectionV t c).natDegree = 2*c := by
    unfold sectionV; rw [← C_1, ← map_sub, natDegree_mul (mul_ne_zero hC (hn c hc 1)) (hn c hc _), natDegree_mul hC (hn c hc 1)]
    rw [natDegree_C,hd _ hc 1,hd _ hc _]; omega
  have he : sectionQ t c u v * sectionV t c = -C k*(X^(c*u)-1) := by
    rw [section_spec,hr]; simp only [map_one,one_mul,k,map_sub]; ring
  have hnC : -C k ≠ (0:K[X]) := by simpa using hk
  have hnQ : sectionQ t c u v ≠ 0 := by
    intro h; rw [h,zero_mul] at he; exact (mul_ne_zero hnC (h1 _ ha)) he.symm
  have hh := congrArg natDegree he
  rw [natDegree_mul hnQ hV,degV,natDegree_mul hnC (h1 _ ha)] at hh
  rw [← C_1,hd _ ha 1,natDegree_neg,natDegree_C,zero_add] at hh; exact hh
end E707Monge


end

-- Bundled module: UpperFactor707
section


namespace E707Monge
open Polynomial E707Geometry
variable {K : Type*} [Field K]
theorem topPrime (t : K) (P : K[X][X]) (hP : P ≠ 0) (h : P.leadingCoeff.eval t=0) :
    ∃ f : K[X][X], Irreducible f ∧ f ∣ P ∧ f.leadingCoeff.eval t = 0 := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit p hp => exact False.elim (((hp.map (leadingCoeffHom)).map (evalRingHom t)).ne_zero h)
  | mul a i ha hi ih =>
    rw [leadingCoeff_mul,eval_mul,mul_eq_zero] at h
    rcases h with h|h
    · exact ⟨i,hi,dvd_mul_right _ _,h⟩
    · obtain ⟨j,hj,hd,he⟩ := ih ha h
      exact ⟨j,hj,hd.trans (dvd_mul_left _ _),he⟩

theorem upperFactor (t : K) (c u v : ℕ) (hc : 0<c) (ha : 0<c*u) (hab : c*u<c*v)
    (ht : t^c ≠ 1) (hr : t^(c*u)=1) (hb : t^(c*v)≠1) (hp : ((c*u:ℕ):K)≠0) :
    ∃ f g : K[X][X], Irreducible f ∧ planeQ c u v = f*g ∧ f.leadingCoeff.eval t=0 ∧
      g.leadingCoeff.eval t≠0 ∧ c*v-c*u ≤ f.natDegree := by
  let Q := planeQ (K:=K) c u v
  let e := evalRingHom t
  obtain ⟨hd,hl⟩ := planeTop (K:=K) c u v hc ha hab
  change Q.natDegree+2*c=c*v at hd
  change Q.leadingCoeff * _ = _ at hl
  have hz : Q.leadingCoeff.eval t = 0 := by
    have hh := congrArg (eval t) hl
    simp only [eval_mul,eval_sub,eval_pow,eval_X,eval_one,hr,sub_self,mul_eq_zero] at hh
    exact hh.resolve_right (sub_ne_zero.mpr ht)
  have ht0 : t ≠ 0 := by rintro rfl; simp [ha.ne'] at hr
  have deriv : Q.leadingCoeff.derivative.eval t ≠ 0 := by
    intro h
    have hh := congrArg (fun p : K[X] => p.derivative.eval t) hl
    simp [derivative_mul,derivative_X_pow,h,hz,ht0] at hh
    exact hp (by simpa using hh)
  have hn : Q ≠ 0 := by intro h; simp [h] at deriv
  obtain ⟨f,hf,⟨g,hg⟩,hfz⟩ := topPrime t Q hn hz
  have hgz : g.leadingCoeff.eval t ≠ 0 := by
    intro H; apply deriv; rw [hg,leadingCoeff_mul,derivative_mul]; simp [H,hfz]
  have hsec : Q.map e = sectionQ t c u v := by
    change mapRingHom e _ = _
    simp only [Q,planeQ,sectionQ,mapQ,map_add,map_one,map_mul,coe_mapRingHom,map_C,map_pow,map_X,e,coe_evalRingHom,eval_pow,eval_X]
  have hdeg := upperDegree t c u v hc ha ht hr hb
  rw [←hsec] at hdeg
  have hmf : f.map e ≠ 0 := by
    intro h; have hzero : sectionQ t c u v = 0 := by rw [←hsec,hg,Polynomial.map_mul,h,zero_mul]
    have he := section_spec t c u v
    rw [hzero,zero_mul,hr] at he
    have he0 := congrArg (eval 0) he
    simp [ha.ne',(by omega : c*v≠0)] at he0
    exact hb (by linear_combination -he0)
  have hmg : g.map e ≠ 0 := by
    intro H; apply hgz; change e (g.coeff g.natDegree) = 0; rw [←coeff_map,H,Polynomial.coeff_zero]
  rw [hg,Polynomial.map_mul,natDegree_mul hmf hmg,natDegree_map_of_leadingCoeff_ne_zero e hgz] at hdeg
  rw [hg,natDegree_mul hf.ne_zero (by rintro rfl; simp [hg] at hn)] at hd
  exact ⟨f,g,hf,hg,hfz,hgz,by omega⟩
end E707Monge

end

-- Bundled module: MajorFactor707
section

namespace E707Monge
open Polynomial
variable {K : Type*} [Field K] [IsAlgClosed K]
theorem majorFactor (c u v : ℕ) (hc : 0<c) (hca : c<c*u) (hab : 2*(c*u)<c*v)
    (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):K)] :
    ∃ f g : K[X][X], Irreducible f ∧ planeQ c u v = f*g ∧
      c*v-c*u ≤ f.natDegree ∧ g.leadingCoeff.natDegree=0 ∧ f.leadingCoeff.natDegree+c=c*u := by
  let Q := planeQ (K:=K) c u v
  have hp := NeZero.ne ((c*u:ℕ):K)
  have ha : 0<c*u := by omega
  have hlt : c*u<c*v := by omega
  obtain ⟨hd, hl⟩ := planeTop (K:=K) c u v hc ha hlt
  change Q.natDegree+2*c=c*v at hd
  change Q.leadingCoeff * _ = _ at hl
  have admiss (t : K) (hz : Q.leadingCoeff.eval t=0) : t^c≠1 ∧ t^(c*u)=1 ∧ t^(c*v)≠1 := by
    have he := congrArg (eval t) hl
    simp [hz] at he
    have hr : t^(c*u)=1 := sub_eq_zero.mp he.symm
    have ht0 : t≠0 := by rintro rfl; simp [ha.ne'] at hr
    have ht : t^c≠1 := by
      intro h
      have hh := congrArg (fun p : K[X] => p.derivative.eval t) hl
      simp [derivative_mul,derivative_X_pow,h,hz,ht0] at hh
      exact hp (by simpa using hh)
    refine ⟨ht,hr,fun h => ht ?_⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [←hgcd]; exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hr) (orderOf_dvd_iff_pow_eq_one.mpr h)
  have dne : Q.leadingCoeff.natDegree+c=c*u := by
    have hh := congrArg natDegree hl
    have hn (n : ℕ) (hn : 0<n) : (X:K[X])^n-1 ≠ 0 := (monic_X_pow_sub_C 1 hn.ne').ne_zero
    have hQ : Q.leadingCoeff ≠ 0 := by intro h; rw [h,zero_mul] at hl; exact hn _ ha hl.symm
    rw [natDegree_mul hQ (hn _ hc)] at hh
    simpa only [←C_1,natDegree_X_pow_sub_C] using hh
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_root Q.leadingCoeff (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
  obtain ⟨htc,hta,htb⟩ := admiss t ht
  obtain ⟨f,g,hf,hfg,_,_,hbig⟩ := upperFactor t c u v hc ha hlt htc hta htb hp
  change Q=f*g at hfg
  have hg : g ≠ 0 := by intro h; simp [hfg,h] at dne; omega
  have dsum : f.natDegree+g.natDegree+2*c=c*v := by rwa [hfg,natDegree_mul hf.ne_zero hg] at hd
  have dg : g.leadingCoeff.natDegree=0 := by
    by_contra h
    obtain ⟨w,hw⟩ := IsAlgClosed.exists_root g.leadingCoeff (ne_of_gt (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h)))
    have hwQ : Q.leadingCoeff.eval w=0 := by rw [hfg,leadingCoeff_mul,eval_mul,hw, mul_zero]
    obtain ⟨hwc,hwa,hwb⟩ := admiss w hwQ
    obtain ⟨F,G,hF,hFG,hFw,hGw,hFb⟩ := upperFactor w c u v hc ha hlt hwc hwa hwb hp
    change Q=F*G at hFG
    have hdiv : F ∣ f*g := ⟨G,hfg.symm.trans hFG⟩
    rcases hF.prime.dvd_or_dvd hdiv with h|h
    · obtain ⟨r,hr⟩ := h
      have hcanc : G=r*g := by apply mul_left_cancel₀ hF.ne_zero; rw [←mul_assoc,←hr,←hfg,hFG]
      apply hGw; rw [hcanc,leadingCoeff_mul,eval_mul,hw,mul_zero]
    · have hle := natDegree_le_of_dvd h hg; omega
  refine ⟨f,g,hf,hfg,hbig,dg,?_⟩
  rwa [hfg,leadingCoeff_mul,natDegree_mul (leadingCoeff_ne_zero.mpr hf.ne_zero) (leadingCoeff_ne_zero.mpr hg),dg,add_zero] at dne
end E707Monge

end

-- Bundled module: HomMajor707
section


namespace E707Monge
open MvPolynomial E707Geometry
open scoped Polynomial
variable {K : Type*} [Field K]
abbrev P3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
noncomputable def homQ (c u v : ℕ) : P3 K :=
  let x := (X 2 : P3 K)^c; let y := (X 1 : P3 K)^c; let z := (X 0 : P3 K)^c
  altQuot (x+y+z) (x*y+y*z+z*x) (x*y*z) u v
noncomputable def spec2 : MvPolynomial (Fin 2) K →+* K[X] :=
  eval₂Hom Polynomial.C (fun i => if i=0 then Polynomial.X else 1)
noncomputable def spec3 : P3 K →+* K[X][X] :=
  (Polynomial.mapRingHom spec2).comp (finSuccEquiv K 2).toRingHom
lemma spec_homQ (c u v : ℕ) : spec3 (homQ (K:=K) c u v) = planeQ c u v := by
  have h0 : spec3 (X 0 : P3 K) = Polynomial.X := by simp [spec3,finSuccEquiv_X_zero]
  have h1 : spec3 (X 1 : P3 K) = Polynomial.C Polynomial.X := by
    change Polynomial.map _ (finSuccEquiv K 2 (X (0 : Fin 2).succ)) = _; rw [finSuccEquiv_X_succ]; simp [spec2]
  have h2 : spec3 (X 2 : P3 K) = 1 := by
    change Polynomial.map _ (finSuccEquiv K 2 (X (1 : Fin 2).succ)) = _; rw [finSuccEquiv_X_succ]; simp [spec2]
  simp [homQ,mapQ,h0,h1,h2,planeQ]
lemma spec_deg (F : P3 K) : (spec3 F).natDegree ≤ F.totalDegree := by
  apply Polynomial.natDegree_map_le.trans
  change (finSuccEquiv K 2 F).natDegree ≤ _
  rw [natDegree_finSuccEquiv]; exact degreeOf_le_totalDegree _ _
lemma lift_prime {R S : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R] [CommRing S] [IsDomain S]
    (e : R →+* S) {P : R} {f : S} (hp : e P ≠ 0) (hf : Prime f) (hd : f ∣ e P) :
    ∃ F : R, Irreducible F ∧ F ∣ P ∧ f ∣ e F := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at hp
  | unit a ha => exact False.elim (hf.not_unit (isUnit_of_dvd_unit hd (ha.map e)))
  | mul a i ha hi ih =>
    rw [map_mul] at hp hd
    rcases hf.dvd_or_dvd hd with h|h
    · exact ⟨i,hi,dvd_mul_right _ _,h⟩
    · obtain ⟨j,hj,hja,hjf⟩ := ih (right_ne_zero_of_mul hp) h
      exact ⟨j,hj,hja.trans (dvd_mul_left _ _),hjf⟩
theorem homMajor [IsAlgClosed K] (c u v : ℕ) (hc : 0<c) (hca : c<c*u) (hab : 2*(c*u)<c*v)
    (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):K)] :
    ∃ F : P3 K, Irreducible F ∧ F ∣ homQ c u v ∧ c*v-c*u ≤ (spec3 F).natDegree := by
  obtain ⟨f,g,hf,hfg,hbig,-,-⟩ := majorFactor (K:=K) c u v hc hca hab hgcd
  have hd := (planeTop (K:=K) c u v hc (by omega) (by omega)).1
  have hn : spec3 (homQ (K:=K) c u v) ≠ 0 := by rw [spec_homQ]; intro hz; rw [hz,Polynomial.natDegree_zero] at hd; omega
  obtain ⟨F,hF,hdiv,hsp⟩ := lift_prime spec3 hn hf.prime (by rw [spec_homQ]; exact ⟨g,hfg⟩)
  have hnF : spec3 F ≠ 0 := by intro hz; apply hn; exact zero_dvd_iff.mp (hz ▸ map_dvd spec3 hdiv)
  exact ⟨F,hF,hdiv,hbig.trans (Polynomial.natDegree_le_of_dvd hsp hnF)⟩
end E707Monge

end

-- Bundled module: HomBudget707
section


namespace E707Monge
open MvPolynomial E707Geometry
variable {K : Type*} [Field K]
lemma hom_bound (c u v : ℕ) (hc : 0<c) : (homQ (K:=K) c u v).totalDegree ≤ c*u+c*v := by
  let V (i : Fin 3) := (X i : P3 K)^c
  have sep (i j : Fin 3) (h : i ≠ j) : V i - V j ≠ 0 := by
    intro he; have hh := congrArg (eval (fun k => if k=i then (0:K) else 1)) (sub_eq_zero.mp he)
    simp [V,h.symm,hc.ne'] at hh
  have hD := mul_ne_zero (mul_ne_zero (sep 1 2 (by decide)) (sep 0 2 (by decide))) (sep 0 1 (by decide))
  let H := homQ (K:=K) c u v
  change H.totalDegree ≤ _
  by_cases hn : H=0
  · simp [hn]
  have he := altQuot_spec (V 2) (V 1) (V 0) u v
  change H * _ = _ at he
  have mono (i j : Fin 3) (r t : ℕ) : ((V i)^r*(V j)^t).totalDegree ≤ c*r+c*t := by
    apply (totalDegree_mul _ _).trans; simp [V,←pow_mul,totalDegree_X_pow]
  have pair (i j : Fin 3) : ((V i)^u*(V j)^v-(V i)^v*(V j)^u).totalDegree ≤ c*u+c*v :=
    (totalDegree_sub _ _).trans (max_le (mono i j u v) (by simpa [add_comm] using mono i j v u))
  have hh := (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le (pair 2 1) (pair 1 0))) (pair 0 2))
  rw [←he,totalDegree_mul_of_isDomain hn hD] at hh; omega
end E707Monge

end

-- Bundled module: HomOrbit707
section


namespace E707Monge
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable def rot : P3 K ≃ₐ[K] P3 K := renameEquiv K (finRotate 3)
lemma rot_cube (F : P3 K) : rot (rot (rot F))=F := by
  change rename _ (rename _ (rename _ F))=F
  rw [rename_rename,rename_rename]; have h : ((⇑(finRotate 3) ∘ ⇑(finRotate 3)) ∘ ⇑(finRotate 3)) = id := by decide
  rw [h,rename_id_apply]
lemma rotQ (c u v : ℕ) : rot (homQ (K:=K) c u v)=homQ c u v := by
  change (rot.toRingHom) _ = _
  simp only [homQ,mapQ,map_add,map_mul,map_pow]
  change E707Geometry.altQuot _ _ _ _ _ = _
  congr 1 <;> simp only [rot,renameEquiv_apply,rename_X] <;>
    change _ = _ <;> simp [finRotate_apply, show (2+1 : Fin 3)=0 by decide, show (1+1 : Fin 3)=2 by decide] <;> ring
lemma orbitStable {F H : P3 K} (hn : H≠0) (hr : rot H=H) (hF : Irreducible F) (hd : F ∣ H)
    (hb : H.totalDegree < 3*F.totalDegree) : Associated F (rot F) := by
  by_contra h
  let r := rot (K:=K)
  have h1 : Irreducible (r F) := hF.map r
  have h2 : Irreducible (r (r F)) := h1.map r
  have h01 : ¬ F ∣ r F := fun h' => h (hF.associated_of_dvd h1 h')
  have h12 : ¬ r F ∣ r (r F) := fun h' => h01 (by simpa using map_dvd r.symm h')
  have h20 : ¬ r (r F) ∣ F := by intro he; apply h12; have h' := map_dvd r (map_dvd r he); simpa only [r,rot_cube] using h'
  have d1 : r F ∣ H := hr ▸ map_dvd r hd
  have d2 : r (r F) ∣ H := hr ▸ map_dvd r d1
  have d01 := (hF.isRelPrime_iff_not_dvd.mpr h01).mul_dvd hd d1
  have hn21 : ¬ r (r F) ∣ r F := fun he => h12 (h2.associated_of_dvd h1 he).symm.dvd
  have hall := (h2.isRelPrime_iff_not_dvd.mpr (fun he => (h2.prime.dvd_or_dvd he).elim h20 hn21)).mul_dvd d2 d01
  have ht := totalDegree_le_of_dvd_of_isDomain hall hn
  have eqd (G : P3 K) : (r G).totalDegree=G.totalDegree := totalDegree_renameEquiv _ _
  rw [totalDegree_mul_of_isDomain h2.ne_zero (mul_ne_zero hF.ne_zero h1.ne_zero),totalDegree_mul_of_isDomain hF.ne_zero h1.ne_zero,eqd,eqd] at ht; omega
end E707Monge

end

-- Bundled module: StableMajor707
section

namespace E707Monge
open MvPolynomial
variable {K : Type*} [Field K] [IsAlgClosed K]
theorem stableMajor (c u v : ℕ) (hc : 0<c) (hca : c<c*u) (hab : 2*(c*u)<c*v)
    (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):K)] :
    ∃ F : P3 K, Irreducible F ∧ F ∣ homQ c u v ∧ c*v-c*u ≤ (spec3 F).natDegree ∧
      Associated F (rot F) ∧ (∀ L : P3 K, L ≠ 0 → L.totalDegree ≤ 1 → ¬ F ∣ L) ∧
      ∀ G : P3 K, Irreducible G → G ∣ homQ c u v → c*v-c*u ≤ (spec3 G).natDegree → Associated F G := by
  obtain ⟨F,hF,hd,hb⟩ := homMajor (K:=K) c u v hc hca hab hgcd
  have htot := spec_deg F
  have hh := (planeTop (K:=K) c u v hc (by omega) (by omega)).1
  have hn : spec3 (homQ (K:=K) c u v) ≠ 0 := by rw [spec_homQ]; intro hz; rw [hz,Polynomial.natDegree_zero] at hh; omega
  have hn' : homQ (K:=K) c u v ≠ 0 := fun hz => hn (by rw [hz,map_zero])
  have hbound := hom_bound (K:=K) c u v hc
  refine ⟨F,hF,hd,hb,orbitStable hn' (rotQ ..) hF hd (by omega),?_,?_⟩
  · intro L hnL hL hdiv; have := totalDegree_le_of_dvd_of_isDomain hdiv hnL; omega
  · intro G hG hdiv hbg; by_contra h
    have hprod := (hF.isRelPrime_iff_not_dvd.mpr (fun he => h (hF.associated_of_dvd hG he))).mul_dvd hd hdiv
    have hsp := map_dvd spec3 hprod
    have hne (A : P3 K) (hA : A ∣ homQ c u v) : spec3 A ≠ 0 := by
      intro he; apply hn; exact zero_dvd_iff.mp (he ▸ map_dvd spec3 hA)
    have hle := Polynomial.natDegree_le_of_dvd hsp hn
    rw [map_mul,Polynomial.natDegree_mul (hne F hd) (hne G hdiv),spec_homQ] at hle; omega
end E707Monge

end

-- Bundled module: GaloisMajor707
section

namespace E707Monge
open MvPolynomial
open scoped Polynomial
variable {K : Type*} [Field K]
lemma specCoeffComm (e : K ≃+* K) (F : P3 K) : spec3 (map e F) =
    (spec3 F).map (Polynomial.mapRingHom (e : K →+* K)) := by
  let m := Polynomial.mapRingHom (Polynomial.mapRingHom (e : K →+* K))
  suffices h : spec3.comp (map (σ:=Fin 3) (e : K →+* K)) = m.comp spec3 from RingHom.congr_fun h F
  apply MvPolynomial.ringHom_ext
  · intro x; simp [m,spec3,spec2,finSuccEquiv_apply]
  · intro i
    have h0 : spec3 (X 0 : P3 K) = Polynomial.X := by simp [spec3,finSuccEquiv_X_zero]
    have h1 : spec3 (X 1 : P3 K) = Polynomial.C Polynomial.X := by
      change Polynomial.map _ (finSuccEquiv K 2 (X (0 : Fin 2).succ)) = _; rw [finSuccEquiv_X_succ]; simp [spec2]
    have h2 : spec3 (X 2 : P3 K) = 1 := by
      change Polynomial.map _ (finSuccEquiv K 2 (X (1 : Fin 2).succ)) = _; rw [finSuccEquiv_X_succ]; simp [spec2]
    fin_cases i <;> simp [m,h0,h1,h2]
theorem galoisStableMajor [IsAlgClosed K] (c u v : ℕ) (hc : 0<c) (hca : c<c*u) (hab : 2*(c*u)<c*v)
    (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):K)] :
    ∃ F : P3 K, Irreducible F ∧ F ∣ homQ c u v ∧ c*v-c*u ≤ (spec3 F).natDegree ∧
      Associated F (rot F) ∧ (∀ L : P3 K, L ≠ 0 → L.totalDegree ≤ 1 → ¬ F ∣ L) ∧
      ∀ e : K ≃+* K, Associated F (map e F) := by
  obtain ⟨F,hF,hdiv,hb,hr,hl,hu⟩ := stableMajor (K:=K) c u v hc hca hab hgcd
  refine ⟨F,hF,hdiv,hb,hr,hl,fun e => hu _ (hF.map (mapEquiv (Fin 3) e)) ?_ ?_⟩
  · have hQ : map (e : K →+* K) (homQ (K:=K) c u v) = homQ c u v := by simp [homQ,mapQ]
    exact hQ ▸ map_dvd (map (σ:=Fin 3) (e : K →+* K)) hdiv
  · rw [specCoeffComm,Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective (e : K →+* K) e.injective)]; exact hb
end E707Monge

end

-- Bundled module: TwistedMajor
section


namespace E707Geometry
open MvPolynomial E707Monge
variable {K : Type*} [Field K] [IsAlgClosed K]
/-- The actual Monge factor remains stable under Frobenius after cyclic substitution.
For an invertible substitution its image is again a geometric prime. -/
theorem twistedMajor {J : Type*} (c u v : ℕ) (hc : 0<c) (hca : c<c*u) (hab : 2*(c*u)<c*v)
    (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):K)]
    (e : K ≃+* K) (L : Fin 3 → MvPolynomial J K)
    (cycle : ∀ i, map (e : K →+* K) (L i) = L (finRotate 3 i)) :
    ∃ H : P3 K, Irreducible H ∧ H ∣ homQ c u v ∧
      (∀ A : P3 K, A ≠ 0 → A.totalDegree ≤ 1 → ¬ H ∣ A) ∧
      aeval L H ∣ aeval L (homQ (K:=K) c u v) ∧
      Associated (aeval L H) (map (e : K →+* K) (aeval L H)) := by
  obtain ⟨H,hi,hd,_,hr,hl,he⟩ := galoisStableMajor (K:=K) c u v hc hca hab hgcd
  exact ⟨H,hi,hd,hl,map_dvd (aeval L) hd,twistAssociated _ _ L cycle H (he e) hr⟩
end E707Geometry

end

-- Bundled module: ChartLinear
section

open MvPolynomial Matrix
namespace E707Geometry
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
noncomputable def rowForm (A : Matrix n n K) (i : n) : MvPolynomial n K :=
  ∑ j, C (A i j) * X j
lemma substRows (A B : Matrix n n K) (i : n) :
    aeval (rowForm A) (rowForm B i) = rowForm (B*A) i := by
  simp only [rowForm,map_sum,map_mul,aeval_C,aeval_X,algebraMap_eq,Matrix.mul_apply,map_sum]
  simp only [Finset.mul_sum,Finset.sum_mul,← mul_assoc,← C_mul]
  rw [Finset.sum_comm]
lemma rowForm_one (i : n) : rowForm (1 : Matrix n n K) i = X i := by
  classical
  simp [rowForm,Matrix.one_apply,ite_mul]
noncomputable def rowEquiv (A : Matrix n n K) (ha : IsUnit A.det) :
    MvPolynomial n K ≃ₐ[K] MvPolynomial n K :=
  AlgEquiv.ofAlgHom (aeval (rowForm A)) (aeval (rowForm A⁻¹))
    (by ext1 i; simp only [AlgHom.comp_apply,aeval_X,AlgHom.id_apply]; change aeval (rowForm A) (rowForm A⁻¹ i) = X i; rw [substRows, Matrix.nonsing_inv_mul _ ha,rowForm_one])
    (by ext1 i; simp only [AlgHom.comp_apply,aeval_X,AlgHom.id_apply]; change aeval (rowForm A⁻¹) (rowForm A i) = X i; rw [substRows, Matrix.mul_nonsing_inv _ ha,rowForm_one])

/-- The Vandermonde twist is an automorphism for any three distinct conjugates. -/
theorem vandermondeMajor [IsAlgClosed K] (c u v : ℕ) (hc : 0<c) (hca : c<c*u)
    (hab : 2*(c*u)<c*v) (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):K)]
    (e : K ≃+* K) (t : Fin 3 → K) (ht : Function.Injective t)
    (he : ∀ i, e (t i) = t (finRotate 3 i)) :
    let L := rowForm (vandermonde t)
    ∃ G : MvPolynomial (Fin 3) K, Irreducible G ∧ G ∣ aeval L (E707Monge.homQ (K:=K) c u v) ∧
      Associated G (map (e : K →+* K) G) := by
  intro L
  have hcyc (i) : map (e : K →+* K) (L i) = L (finRotate 3 i) := by
    simp [L,rowForm,vandermonde_apply,he]
  obtain ⟨H,hi,_,_,hd,hs⟩ := twistedMajor c u v hc hca hab hgcd e L hcyc
  let E := rowEquiv (vandermonde t) (isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr ht))
  exact ⟨_,hi.map E.toMulEquiv,hd,hs⟩
end E707Geometry


end

-- Bundled module: Alternant707
section

namespace E707Partial
open Polynomial Finset
/-- The three diagonal components split off over the coefficient ring itself. -/
theorem alternantDiv {R : Type*} [CommRing R] (a b : R) (u v : ℕ) :
    (a-1)*(b-1)*(b-a) ∣ (a^v-1)*(b^u-a^u)-(b^v-a^v)*(a^u-1) := by
  classical
  let G (n : ℕ) : R[X] := ∑ i ∈ range n, X^i
  have he (n : ℕ) (t : R) : (t-1)*(G n).eval t = t^n-1 := by
    simpa [G, eval_finsetSum] using mul_geom_sum t n
  let P : R[X] := C ((G v).eval a)*G u - C ((G u).eval a)*G v
  obtain ⟨h, hh⟩ := sub_dvd_eval_sub b a P
  simp [P] at hh
  refine ⟨h,?_⟩
  calc
    _ = (a^v-1)*(b^u-1)-(b^v-1)*(a^u-1) := by ring
    _ = (a-1)*(b-1)*((G v).eval a*(G u).eval b-(G u).eval a*(G v).eval b) := by
      rw [← he v a, ← he u b, ← he v b, ← he u a]; ring
    _ = _ := by rw [mul_assoc ((a-1)*(b-1)), ← hh]; ring
theorem detChartDiv (K : Type*) [Field K] (u v : ℕ) :
    let a : K[X][X] := C X
    let b : K[X][X] := a*X
    (a-1)*(b-1)*(b-a) ∣ detChart K u v :=
  alternantDiv _ _ u v


end E707Partial

end

-- Bundled module: VandHom707
section

namespace E707Partial
open Polynomial Finset
/-- Sawin's homogeneous alternant before division by the Vandermonde. -/
def alt3 {R : Type*} [CommRing R] (u v : ℕ) (a b c : R) : R :=
  (b^v-a^v)*(c^u-a^u)-(c^v-a^v)*(b^u-a^u)
def vand3 {R : Type*} [CommRing R] (a b c : R) : R := (b-a)*(c-a)*(c-b)
 theorem vand3_dvd {R : Type*} [CommRing R] (u v : ℕ) (a b c : R) :
    vand3 a b c ∣ alt3 u v a b c := by
  classical
  let G (n : ℕ) : R[X] := ∑ i ∈ range n, X^i * C (a^(n-1-i))
  have he (n : ℕ) (t : R) : (t-a)*(G n).eval t = t^n-a^n := by
    simpa [G,eval_finsetSum,mul_comm] using geom_sum₂_mul t a n
  let P := C ((G v).eval b)*G u - C ((G u).eval b)*G v
  obtain ⟨h, hh⟩ := sub_dvd_eval_sub c b P
  simp [P] at hh
  refine ⟨h,?_⟩
  unfold alt3 vand3
  rw [← he v b, ← he u c, ← he v c, ← he u b]
  linear_combination (b-a)*(c-a)*hh
 theorem alt3_cycle {R : Type*} [CommRing R] (u v : ℕ) (a b c : R) :
    alt3 u v b c a = alt3 u v a b c := by unfold alt3; ring
 theorem vand3_cycle {R : Type*} [CommRing R] (a b c : R) :
    vand3 b c a = vand3 a b c := by unfold vand3; ring

end E707Partial

end

-- Bundled module: ResidualCycle707
section

namespace E707Partial
open MvPolynomial
abbrev Poly3 := MvPolynomial (Fin 3) ℤ
noncomputable def residual3 (u v : ℕ) : Poly3 :=
  (vand3_dvd u v (X 0 : Poly3) (X 1) (X 2)).choose
theorem residual3_spec (u v : ℕ) :
    alt3 u v (X 0) (X 1) (X 2) = vand3 (X 0) (X 1) (X 2) * residual3 u v :=
  (vand3_dvd u v (X 0 : Poly3) (X 1) (X 2)).choose_spec
 theorem residual3_cycle (u v : ℕ) :
    rename (fun i : Fin 3 => i+1) (residual3 u v) = residual3 u v := by
  let r := rename (R:=ℤ) (fun i : Fin 3 => i+1)
  have h := congrArg r (residual3_spec u v)
  change r _ = r _ at h
  have h0 : r (X 0) = X 1 := rename_X _ _
  have h1 : r (X 1) = X 2 := rename_X _ _
  have h2 : r (X 2) = X 0 := rename_X _ _
  simp only [alt3,vand3,map_sub,map_mul,map_pow,h0,h1,h2] at h
  change alt3 u v (X 1) (X 2) (X 0) = vand3 (X 1) (X 2) (X 0) * r _ at h
  rw [alt3_cycle u v (X 0) (X 1) (X 2),vand3_cycle (X 0) (X 1) (X 2),residual3_spec] at h
  apply mul_left_cancel₀ _ h.symm
  unfold vand3
  apply mul_ne_zero (mul_ne_zero _ _) <;> apply sub_ne_zero.mpr <;> intro he <;>
    apply_fun (fun f : Poly3 => eval ![0,1,2] f) at he <;> norm_num at he <;> first | exact (by decide : (2:ℤ) ≠ 1) he | exact (by decide : (2:ℤ) ≠ 0) he

end E707Partial

end

-- Bundled module: ResidualFixed707
section

namespace E707Partial
open MvPolynomial
/-- Evaluation along a cyclic orbit is fixed, including over polynomial rings. -/
 theorem residual3_fixed {R : Type*} [CommRing R] (σ : R →+* R) (L : Fin 3 → R)
    (h : ∀ i, σ (L i) = L (i+1)) (u v : ℕ) :
    σ (eval₂Hom (Int.castRingHom R) L (residual3 u v)) =
      eval₂Hom (Int.castRingHom R) L (residual3 u v) := by
  rw [map_eval₂Hom]
  have hi : σ.comp (Int.castRingHom R) = Int.castRingHom R := Subsingleton.elim _ _
  rw [hi,show (fun i => σ (L i)) = L ∘ (fun i => i+1) from funext h,← eval₂Hom_rename,residual3_cycle]

end E707Partial

end

-- Bundled module: TwistedResidual707
section


namespace E707Partial
open MvPolynomial
/-- Descent of the twisted equation itself, not only its finite-field values. -/
 theorem twistedResidual {F K I : Type*} [Field F] [Fintype F] [Field K] [Finite K]
    [Algebra F K] (L : Fin 3 → MvPolynomial I K)
    (h : ∀ i, map (FiniteField.frobeniusAlgHom F K).toRingHom (L i) = L (i+1)) (u v : ℕ) :
    ∃ P : MvPolynomial I F, map (algebraMap F K) P =
      eval₂Hom (Int.castRingHom _) L (residual3 u v) := by
  classical
  let σ := (FiniteField.frobeniusAlgHom F K).toRingHom
  have hf := residual3_fixed (map (σ:=I) σ) L h u v
  apply mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨n,_,rfl⟩ := mem_coeffs_iff.mp hc
  apply frobFixed (F:=F)
  have he := congrArg (coeff n) hf
  change σ _ = _
  simpa only [coeff_map] using he

end E707Partial

end

-- Bundled module: CubicResidual707
section

namespace E707Partial
open MvPolynomial
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

noncomputable def conjugateForm (b : Fin 3 → K) (i : Fin 3) : MvPolynomial (Fin 3) K :=
  ∑ j, C ((b j)^((Fintype.card F)^i.val)) * X j
 theorem conjugateForm_cycle (h3 : Module.finrank F K = 3) (b : Fin 3 → K) (i : Fin 3) :
    map (FiniteField.frobeniusAlgHom F K).toRingHom (conjugateForm (F:=F) b i) =
      conjugateForm (F:=F) b (i+1) := by
  classical
  unfold conjugateForm
  simp only [map_sum,map_mul,map_C,map_X]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  change ((b j)^((Fintype.card F)^i.val))^(Fintype.card F) = _
  rw [← pow_mul, ← pow_succ]
  fin_cases i
  · rfl
  · rfl
  · change (b j)^((Fintype.card F)^3) = (b j)^((Fintype.card F)^0)
    rw [← h3, ← Module.card_eq_pow_finrank (K:=F),FiniteField.pow_card,pow_zero,pow_one]
 theorem cubicResidual (h3 : Module.finrank F K = 3) (b : Fin 3 → K) (u v : ℕ) :
    ∃ P : MvPolynomial (Fin 3) F, map (algebraMap F K) P =
      eval₂Hom (Int.castRingHom _) (conjugateForm (F:=F) b) (residual3 u v) :=
  twistedResidual _ (conjugateForm_cycle h3 b) u v

end E707Partial

end

-- Bundled module: CubicOrbit707
section


namespace E707Partial
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

 theorem cubicOrbit (h3 : Module.finrank F K = 3) :
    ∃ x : K, Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val)) := by
  let σ := (FiniteField.frobeniusAlgHom F K).toRingHom
  have hc : Fintype.card K = (Fintype.card F)^3 := by rw [Module.card_eq_pow_finrank (K:=F),h3]
  have hn : ¬ Function.Surjective (algebraMap F K) := by
    intro hs
    have := Fintype.card_le_of_surjective _ hs
    rw [hc] at this
    have hq := Fintype.one_lt_card (α:=F)
    nlinarith [Nat.mul_le_mul_left ((Fintype.card F)*(Fintype.card F)) (show 2 ≤ (Fintype.card F) by omega),Nat.mul_le_mul_left (Fintype.card F) (show 2 ≤ (Fintype.card F) by omega)]
  unfold Function.Surjective at hn
  push Not at hn
  obtain ⟨x,hx⟩ := hn
  have h1 : σ x ≠ x := fun h => let ⟨a,ha⟩ := frobFixed (F:=F) x h; hx a ha
  have h3x : σ (σ (σ x)) = x := by
    change ((x^(Fintype.card F))^(Fintype.card F))^(Fintype.card F) = x
    rw [← pow_mul,← pow_mul,show (Fintype.card F)*((Fintype.card F)*(Fintype.card F))=(Fintype.card F)^3 by ring,← hc,FiniteField.pow_card]
  have h2 : σ (σ x) ≠ x := fun h => h1 ((congrArg σ h).symm.trans h3x)
  have h12 : σ (σ x) ≠ σ x := σ.injective.ne h1
  refine ⟨x, ?_⟩
  intro i j he
  fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (h1 (by simpa [σ,pow_succ,pow_mul] using he)) | exact False.elim (h2 (by simpa [σ,pow_succ,pow_mul] using he)) | exact False.elim (h12 (by simpa [σ,pow_succ,pow_mul] using he)) | exact False.elim (h1 (by simpa [σ,pow_succ,pow_mul] using he.symm)) | exact False.elim (h2 (by simpa [σ,pow_succ,pow_mul] using he.symm)) | exact False.elim (h12 (by simpa [σ,pow_succ,pow_mul] using he.symm)) 
theorem cubicVandermonde (h3 : Module.finrank F K = 3) :
    ∃ x : K, (Matrix.of (fun i j : Fin 3 => (x^j.val)^((Fintype.card F)^i.val))).det ≠ 0 := by
  obtain ⟨x,hx⟩ := cubicOrbit h3
  refine ⟨x,?_⟩
  have he : Matrix.of (fun i j : Fin 3 => (x^j.val)^((Fintype.card F)^i.val)) =
      Matrix.vandermonde (fun i : Fin 3 => x^((Fintype.card F)^i.val)) := by
    ext i j; simp [Matrix.vandermonde_apply, ← pow_mul,Nat.mul_comm]
  rw [he]; exact Matrix.det_vandermonde_ne_zero_iff.mpr hx

end E707Partial

end

-- Bundled module: CubicChartMajor
section


namespace E707Geometry
open MvPolynomial Matrix
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

/-- Conjugate power-basis chart of the actual cubic extension. -/
theorem cubicChartMajor (h3 : Module.finrank F K = 3) (ι : K →ₐ[F] AlgebraicClosure F)
    (c u v : ℕ) (hc : 0<c) (hca : c<c*u) (hab : 2*(c*u)<c*v)
    (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):AlgebraicClosure F)] :
    ∃ x : K, let t := fun i : Fin 3 => ι (x^((Fintype.card F)^i.val))
      ∃ G : MvPolynomial (Fin 3) (AlgebraicClosure F), Irreducible G ∧
        G ∣ aeval (rowForm (vandermonde t)) (E707Monge.homQ (K:=AlgebraicClosure F) c u v) ∧
        Associated G (map (FiniteField.frobeniusAlgHom F _).toRingHom G) := by
  obtain ⟨x,hx⟩ := E707Partial.cubicOrbit h3
  refine ⟨x,?_⟩
  let t := fun i : Fin 3 => ι (x^((Fintype.card F)^i.val))
  let e := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hcard : Fintype.card K = (Fintype.card F)^3 := by rw [Module.card_eq_pow_finrank (K:=F),h3]
  have hcycle (i) : e (t i) = t (finRotate 3 i) := by
    change (ι _) ^ (Fintype.card F) = ι _
    rw [← map_pow,← pow_mul]
    fin_cases i <;> simp [finRotate_apply, pow_succ]
    rw [show (Fintype.card F)*(Fintype.card F)*(Fintype.card F) = (Fintype.card F)^3 by ring, ← hcard, ← map_pow,FiniteField.pow_card]
  exact vandermondeMajor c u v hc hca hab hgcd e.toRingEquiv t (ι.injective.comp hx) hcycle
end E707Geometry

end

-- Bundled module: MajorHomData
section

namespace E707Geometry
open MvPolynomial E707Monge Matrix
variable {K : Type*} [Field K]
/-- Explicit nonzero homogeneous determinant multiple, before the cubic twist. -/
theorem homMultiple (c u v : ℕ) (hc : 0<c) (hu : c<c*u) (hv : 2*(c*u)<c*v) :
    ∃ P : P3 K, P ≠ 0 ∧ P.IsHomogeneous (c*u+c*v) ∧ homQ c u v ∣ P := by
  let V (i : Fin 3) := (X i : P3 K)^c
  have sep (i j : Fin 3) (h : i ≠ j) : V i - V j ≠ 0 := by
    intro he; have hh := congrArg (eval (fun k => if k=i then (0:K) else 1)) (sub_eq_zero.mp he)
    simp [V,h.symm,hc.ne'] at hh
  have hD := mul_ne_zero (mul_ne_zero (sep 1 2 (by decide)) (sep 0 2 (by decide))) (sep 0 1 (by decide))
  have hh := (planeTop (K:=K) c u v hc (by omega) (by omega)).1
  have hn : spec3 (homQ (K:=K) c u v) ≠ 0 := by rw [spec_homQ]; intro hz; rw [hz,Polynomial.natDegree_zero] at hh; omega
  have hn' : homQ (K:=K) c u v ≠ 0 := fun hz => hn (by rw [hz,map_zero])
  have he := altQuot_spec (V 2) (V 1) (V 0) u v
  change homQ c u v * _ = _ at he
  refine ⟨_,mul_ne_zero hn' hD,?_,dvd_mul_right _ _⟩
  rw [he]
  have mono (i j : Fin 3) (r t : ℕ) : ((V i)^r*(V j)^t).IsHomogeneous (c*r+c*t) :=
    ((isHomogeneous_X_pow (R:=K) i c).pow r).mul ((isHomogeneous_X_pow j c).pow t)
  have pair (i j : Fin 3) := (mono i j u v).sub (show ((V i)^v*(V j)^u).IsHomogeneous (c*u+c*v) by simpa [add_comm] using mono i j v u)
  exact ((pair 2 1).add (pair 1 0)).add (pair 0 2)
lemma rowHom (A : Matrix (Fin 3) (Fin 3) K) (i) : (rowForm A i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _; exact isHomogeneous_C_mul_X _ _
lemma rowSubstHom (A : Matrix (Fin 3) (Fin 3) K) {P : P3 K} {d : ℕ} (h : P.IsHomogeneous d) :
    (aeval (rowForm A) P).IsHomogeneous d := by
  simp only [aeval_def, algebraMap_eq]
  simpa only [one_mul] using h.eval₂ C (rowForm A) (isHomogeneous_C _) (rowHom A)
/-- Retain nonlinearity through the invertible substitution and exhibit a degree-bounded
homogeneous multiple of the same twisted factor. -/
theorem majorChartData [IsAlgClosed K] (c u v : ℕ) (hc : 0<c) (hca : c<c*u)
    (hab : 2*(c*u)<c*v) (hgcd : (c*u).gcd (c*v)=c) [NeZero ((c*u:ℕ):K)]
    (e : K ≃+* K) (t : Fin 3 → K) (ht : Function.Injective t)
    (he : ∀ i, e (t i) = t (finRotate 3 i)) :
    let L := rowForm (vandermonde t)
    ∃ G P : P3 K, Irreducible G ∧ G ∣ aeval L (homQ (K:=K) c u v) ∧
      Associated G (map (e : K →+* K) G) ∧ ¬ Associated G (X 0) ∧
      P ≠ 0 ∧ P.IsHomogeneous (c*u+c*v) ∧ G ∣ P := by
  intro L
  have hcyc (i) : map (e : K →+* K) (L i) = L (finRotate 3 i) := by
    simp [L,rowForm,vandermonde_apply,he]
  obtain ⟨H,hi,hd,hl,hd',hs⟩ := twistedMajor c u v hc hca hab hgcd e L hcyc
  let E := rowEquiv (vandermonde t) (isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr ht))
  obtain ⟨P,hP,hPh,hPd⟩ := homMultiple (K:=K) c u v hc hca hab
  refine ⟨E H,E P,hi.map E.toMulEquiv,hd',hs,?_,(fun hz => hP (E.injective (hz.trans (map_zero E).symm))),rowSubstHom _ hPh,map_dvd E (hd.trans hPd)⟩
  intro ha
  have hb := map_dvd E.symm ha.dvd
  rw [E.symm_apply_apply] at hb
  apply hl _ (fun hz => X_ne_zero 0 (E.symm.injective (hz.trans (map_zero E.symm).symm))) _ hb
  change (aeval (rowForm (vandermonde t)⁻¹) (X 0)).totalDegree ≤ 1
  rw [aeval_X]; exact (rowHom _ _).totalDegree_le
end E707Geometry


end

-- Bundled module: HomDiv707
section



namespace HomDiv707
open MvPolynomial

theorem homogeneous_of_dvd {K : Type*} [Field K] {P G : MvPolynomial (Fin 3) K}
    {d : ℕ} (hP : P ≠ 0) (hom : P.IsHomogeneous d) (dvd : G ∣ P) :
    G.IsHomogeneous G.totalDegree := by
  obtain ⟨H, rfl⟩ := dvd
  obtain ⟨hG, hH⟩ := mul_ne_zero_iff.mp hP
  have low : (d : ℕ∞) ≤ ((G * H : MvPolynomial (Fin 3) K) : MvPowerSeries (Fin 3) K).order := by
    apply MvPowerSeries.nat_le_order
    intro m hm
    rw [MvPolynomial.coeff_coe]
    by_contra hn
    have he : m.degree = d := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hom hn
    exact (Nat.ne_of_lt hm) he
  rw [MvPolynomial.coe_mul, MvPowerSeries.order_mul] at low
  have top := hom.totalDegree hP
  rw [totalDegree_mul_of_isDomain hG hH] at top
  obtain ⟨b, hb⟩ := exists_coeff_ne_zero hH
  intro a ha
  have bound {F : MvPolynomial (Fin 3) K} {m : Fin 3 →₀ ℕ} (hm : coeff m F ≠ 0) :
      (F : MvPowerSeries (Fin 3) K).order ≤ m.degree := MvPowerSeries.order_le hm
  have hsum : (d : ℕ∞) ≤ ↑a.degree + (b.degree : ℕ∞) :=
    low.trans (add_le_add (bound ha) (bound hb))
  have hnat : d ≤ a.degree + b.degree := by exact_mod_cast hsum
  have maxdeg {F : MvPolynomial (Fin 3) K} {m : Fin 3 →₀ ℕ} (hm : coeff m F ≠ 0) :
      m.degree ≤ F.totalDegree := le_totalDegree (mem_support_iff.mpr hm)
  have h₁ := maxdeg ha
  have h₂ := maxdeg hb
  rw [Pi.one_def, ← Finsupp.degree_eq_weight_one]
  omega


end HomDiv707

end

-- Bundled module: Dehom707
section

namespace E707Monge
open MvPolynomial Finset
variable {K : Type*} [Field K] {n d : ℕ}
private abbrev P (K : Type*) [Field K] (n : ℕ) := MvPolynomial (Fin n) K

/-- Set the zeroth coordinate to one, retaining the successor coordinates. -/
noncomputable def affineChart (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (Fin (n+1)) K →+* MvPolynomial (Fin n) K :=
  (Polynomial.evalRingHom 1).comp (finSuccEquiv K n).toRingHom

@[simp] theorem affineChart_X_zero : affineChart K n (X 0) = 1 := by
  simp [affineChart, finSuccEquiv_X_zero]
@[simp] theorem affineChart_X_succ (i : Fin n) : affineChart K n (X i.succ) = X i := by
  simp [affineChart, finSuccEquiv_X_succ]

private theorem chart_sum {F : P K (n+1)} (h : F.IsHomogeneous d) :
    affineChart K n F = ∑ i ∈ range (d+1), ((finSuccEquiv K n) F).coeff i := by
  have hb := (degreeOf_le_totalDegree F 0).trans h.totalDegree_le
  change Polynomial.eval 1 ((finSuccEquiv K n) F) = _
  rw [Polynomial.eval_eq_sum_range' (n := d+1) (by rw [natDegree_finSuccEquiv]; omega)]
  simp

private theorem recover {F : P K (n+1)} (h : F.IsHomogeneous d) {i : ℕ} (hi : i ≤ d) :
    homogeneousComponent (d-i) (affineChart K n F) = ((finSuccEquiv K n) F).coeff i := by
  rw [chart_sum h, map_sum, Finset.sum_eq_single i]
  · exact homogeneousComponent_eq_self (h.finSuccEquiv_coeff_isHomogeneous i _ (by omega))
  · intro j hj hji
    have hj' := mem_range.mp hj
    rw [homogeneousComponent_of_mem (h.finSuccEquiv_coeff_isHomogeneous j (d-j) (by omega)), if_neg (by omega)]
  · simp [mem_range, Nat.lt_succ_of_le hi]

private theorem chart_inj {F G : P K (n+1)} (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (he : affineChart K n F = affineChart K n G) : F = G := by
  apply (finSuccEquiv K n).injective
  ext1 i
  by_cases hi : i ≤ d
  · rw [← recover hF hi, ← recover hG hi, he]
  · have hb (A : P K (n+1)) (h : A.IsHomogeneous d) : ((finSuccEquiv K n) A).natDegree < i := by
      rw [natDegree_finSuccEquiv]; exact ((degreeOf_le_totalDegree A 0).trans h.totalDegree_le).trans_lt (by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hb F hF), Polynomial.coeff_eq_zero_of_natDegree_lt (hb G hG)]

private noncomputable def liftChart (A : P K n) : P K (n+1) :=
  ∑ i ∈ range (A.totalDegree+1), rename Fin.succ (homogeneousComponent i A) * X 0 ^ (A.totalDegree-i)

private theorem lift_hom (A : P K n) : (liftChart A).IsHomogeneous A.totalDegree := by
  apply IsHomogeneous.sum
  intro i hi
  have he := mem_range.mp hi
  have hp := (isHomogeneous_X (R := K) (0 : Fin (n+1))).pow (A.totalDegree-i)
  simpa [Nat.add_sub_of_le (show i ≤ A.totalDegree by omega)] using
    (homogeneousComponent_isHomogeneous i A).rename_isHomogeneous.mul hp

private theorem chart_rename (A : P K n) : affineChart K n (rename Fin.succ A) = A := by
  induction A using MvPolynomial.induction_on with
  | C a => simp [affineChart, finSuccEquiv_apply]
  | add A B hA hB => simp [hA,hB]
  | mul_X A i hA => simp [hA]

private theorem chart_lift (A : P K n) : affineChart K n (liftChart A) = A := by
  simp [liftChart, chart_rename, sum_homogeneousComponent]

/-- A homogeneous irreducible other than the chart coordinate remains irreducible,
with unchanged degree, on the standard affine chart. -/
theorem irreducible_affineChart {F : MvPolynomial (Fin (n+1)) K} (h : F.IsHomogeneous d)
    (hir : Irreducible F) (hx : ¬ Associated F (X 0)) :
    Irreducible (affineChart K n F) ∧ (affineChart K n F).totalDegree = d := by
  have hc : ((finSuccEquiv K n) F).coeff 0 ≠ 0 := by
    intro hz
    obtain ⟨q,hq⟩ := Polynomial.X_dvd_iff.mpr hz
    apply hx
    apply Associated.symm
    apply (X_prime (i := (0 : Fin (n+1))) (R := K)).irreducible.associated_of_dvd hir
    refine ⟨(finSuccEquiv K n).symm q, (finSuccEquiv K n).injective ?_⟩
    simpa [finSuccEquiv_X_zero] using hq
  have hr := recover h (i := 0) (Nat.zero_le d)
  simp only [Nat.sub_zero] at hr
  have hd : (affineChart K n F).totalDegree = d := by
    apply le_antisymm
    · rw [chart_sum h]; apply totalDegree_finsetSum_le
      intro i hi
      have := mem_range.mp hi
      exact (h.finSuccEquiv_coeff_isHomogeneous i (d-i) (by omega)).totalDegree_le.trans (Nat.sub_le ..)
    · by_contra! hlt
      exact hc (hr.symm.trans (homogeneousComponent_eq_zero d _ hlt))
  have hn : affineChart K n F ≠ 0 := by
    intro he; apply hc; rw [← hr, he, map_zero]
  have hdpos : d ≠ 0 := by
    intro he
    have heq := totalDegree_eq_zero_iff_eq_C.mp ((h.totalDegree hir.ne_zero).trans he)
    have hc' : F.coeff 0 ≠ 0 := by intro hz; exact hir.ne_zero (by simpa [hz] using heq)
    exact hir.not_isUnit (heq ▸ (isUnit_iff_ne_zero.mpr hc').map (C : K →+* _))
  refine ⟨⟨fun hu => hdpos (hd.symm.trans (isUnit_iff_totalDegree_of_isReduced.mp hu).2), ?_⟩, hd⟩
  intro A B he
  have hne := mul_ne_zero_iff.mp (he ▸ hn)
  have hs : A.totalDegree + B.totalDegree = d := by
    rwa [he, totalDegree_mul_of_isDomain hne.1 hne.2] at hd
  have hf : F = liftChart A * liftChart B := chart_inj h
    (hs ▸ (lift_hom A).mul (lift_hom B)) (by simpa [chart_lift] using he)
  exact (hir.isUnit_or_isUnit hf).imp (fun u => chart_lift A ▸ u.map (affineChart K n))
    (fun u => chart_lift B ▸ u.map (affineChart K n))

end E707Monge

end

-- Bundled module: AffineStableCount
section


namespace E707Geometry
open MvPolynomial E707Monge
variable {K : Type*} [Field K]
lemma affineChart_map (e : K →+* K) (G : MvPolynomial (Fin 3) K) :
    affineChart K 2 (map e G) = map e (affineChart K 2 G) := by
  suffices h : (affineChart K 2).comp (map e) = (map e).comp (affineChart K 2) from RingHom.congr_fun h G
  apply MvPolynomial.ringHom_ext
  · intro a; simp [affineChart,finSuccEquiv_apply]
  · intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
universe u
/-- A homogeneous nonlinear stable geometric prime contributes at least half the field
in a single affine chart, without a loss for the points at infinity. -/
theorem halfCountChart (D : ℕ) : ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F]
    (G : MvPolynomial (Fin 3) (AlgebraicClosure F)) (d : ℕ), Q ≤ Fintype.card F →
    d ≤ D → G.IsHomogeneous d → Irreducible G → ¬ Associated G (X 0) →
    Associated G (map (FiniteField.frobeniusAlgHom F _).toRingHom G) →
    Fintype.card F ≤ 2*({v : Fin 2 → F | eval (algebraMap F _ ∘ v) (affineChart _ 2 G) = 0} : Set _).ncard := by
  obtain ⟨Q,hQ⟩ := halfCountStable.{u} D
  refine ⟨Q,?_⟩
  intro F _ _ G d hq hd hh hi hx hs
  obtain ⟨hi',hd'⟩ := irreducible_affineChart hh hi hx
  apply hQ F _ hq (hd'.le.trans hd) hi'
  rw [← affineChart_map]
  exact hs.map (affineChart _ 2).toMonoidHom
end E707Geometry

end

-- Bundled module: CubicMajorCount
section




namespace E707Geometry
open MvPolynomial Matrix E707Monge
universe u w
/-- Uniform rational point count on a geometric prime of the actual cubic quotient chart. -/
theorem cubicMajorCount (c a b : ℕ) (hc : 0<c) (ha : c<c*a) (hb : 2*(c*a)<c*b)
    (hg : (c*a).gcd (c*b)=c) : ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F]
    (K : Type w) [Field K] [Fintype K] [Algebra F K] [NeZero ((c*a:ℕ):AlgebraicClosure F)]
    (ι : K →ₐ[F] AlgebraicClosure F), Module.finrank F K = 3 → Q ≤ Fintype.card F →
    ∃ x : K, Function.Injective (fun i : Fin 3 => x^(Fintype.card F^i.val)) ∧
      ∃ G : P3 (AlgebraicClosure F), let g := affineChart _ 2 G
        Irreducible g ∧ g.totalDegree ≤ c*a+c*b ∧
        G ∣ aeval (rowForm (vandermonde (fun i : Fin 3 => ι (x^(Fintype.card F^i.val))))) (homQ (K:=AlgebraicClosure F) c a b) ∧
        Fintype.card F ≤ 2*({v : Fin 2 → F | eval (algebraMap F _ ∘ v) g = 0} : Set _).ncard := by
  obtain ⟨Q,hQ⟩ := halfCountChart.{u} (c*a+c*b)
  refine ⟨Q,?_⟩
  intro F _ _ K _ _ _ _ ι h3 hq
  let q := Fintype.card F
  obtain ⟨x,hx⟩ := E707Partial.cubicOrbit h3
  refine ⟨x,hx,?_⟩
  let t := fun i : Fin 3 => ι (x^(q^i.val))
  let e := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hcard : Fintype.card K = q^3 := by rw [Module.card_eq_pow_finrank (K:=F),h3]
  have hcycle (i) : e (t i) = t (finRotate 3 i) := by
    change (ι _) ^ q = ι _
    rw [← map_pow,← pow_mul]
    fin_cases i <;> simp [finRotate_apply, pow_succ]
    rw [show q*q*q = q^3 by ring, ← hcard, ← map_pow,FiniteField.pow_card]
  obtain ⟨G,P,hi,hd,hs,hn,hP,hh,hdiv⟩ := majorChartData c a b hc ha hb hg e.toRingEquiv t (ι.injective.comp hx) hcycle
  have hG := HomDiv707.homogeneous_of_dvd hP hh hdiv
  have hdeg := (totalDegree_le_of_dvd_of_isDomain hdiv hP).trans hh.totalDegree_le
  obtain ⟨hir,hgd⟩ := irreducible_affineChart hG hi hn
  exact ⟨G,hir,hgd.le.trans hdeg,hd,hQ F G _ hq hdeg hG hi hn hs⟩
end E707Geometry

end

-- Bundled module: QuotLocus
section


namespace E707Geometry
variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

/-- A quotient zero on a conjugate triple yields the normalized point in the sieve locus. -/
theorem quotientZero_onCurve (α : Kˣ) (a b c : ℕ) :
    let x := (α:K)^c; let y := ((α:K)^(Fintype.card F))^c; let w := (((α:K)^(Fintype.card F))^(Fintype.card F))^c
    altQuot (x+y+w) (x*y+y*w+w*x) (x*y*w) a b = 0 →
    E707Partial.onCurve F K (c*a) (c*b) ((α:K)^((Fintype.card F)-1)) := by
  intro x y w h
  let z := (α:K)^((Fintype.card F)-1)
  have hy : (α:K)^(Fintype.card F) = (α:K)*z := by dsimp [z]; rw [← pow_succ',Nat.sub_add_cancel Fintype.card_pos]
  have hw : ((α:K)^(Fintype.card F))^(Fintype.card F) = (α:K)*(z*z^(Fintype.card F)) := by rw [hy,mul_pow,hy]; ring
  have he' := altQuot_spec x y w a b
  rw [h,zero_mul] at he'
  dsimp only [x,y,w] at he'
  rw [hw,hy] at he'
  simp only [←pow_mul _ c] at he'
  simp only [mul_pow] at he'
  unfold E707Partial.onCurve
  change (z^(c*b)-1)*((z*z^(Fintype.card F))^(c*a)-z^(c*a)) = ((z*z^(Fintype.card F))^(c*b)-z^(c*b))*(z^(c*a)-1)
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (c*a) α.ne_zero) (pow_ne_zero (c*b) α.ne_zero))
  simp only [mul_pow]
  linear_combination he'
end E707Geometry

end

-- Bundled module: ChartToLocus
section


namespace E707Geometry
open MvPolynomial E707Monge Matrix
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

lemma eval_chart {k : Type*} [Field k] (v : Fin 2 → k) (G : P3 k) :
    eval v (affineChart k 2 G) = eval (Fin.cons 1 v) G := by
  induction G using MvPolynomial.induction_on with
  | C a => simp [affineChart,finSuccEquiv_apply]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => refine Fin.cases ?_ (fun j => ?_) i <;> simp [hf]
lemma chartRows (ι : K →ₐ[F] AlgebraicClosure F) (x : K) (v : Fin 2 → F) (i : Fin 3) :
    eval (Fin.cons 1 (algebraMap F _ ∘ v))
      (rowForm (vandermonde (fun j : Fin 3 => ι (x^((Fintype.card F)^j.val)))) i) =
    ι ((∑ j : Fin 3, algebraMap F K ((Fin.cons 1 v : Fin 3 → F) j) * x^j.val)^((Fintype.card F)^i.val)) := by
  let e := (FiniteField.frobeniusAlgHom F K)^i.val
  have ef (y : K) : e y = y^((Fintype.card F)^i.val) := by
    fin_cases i <;> simp [e, pow_two, AlgHom.mul_apply, FiniteField.coe_frobeniusAlgHom, pow_mul]
  rw [← ef,map_sum,map_sum]
  simp only [rowForm,map_sum,map_mul,eval_C,eval_X,vandermonde_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_pow,map_pow,e.commutes,ι.commutes,ef]
  rw [mul_comm]; congr 1
  all_goals first | (refine Fin.cases ?_ (fun k => ?_) j <;> simp) | simp
lemma eval_rows {k : Type*} [Field k] (v : Fin 3 → k) (A : Matrix (Fin 3) (Fin 3) k) (P : P3 k) :
    eval v (aeval (rowForm A) P) = eval (fun i => eval v (rowForm A i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp only [map_mul,aeval_X,eval_X,hf]
theorem chartQuotientZero (ι : K →ₐ[F] AlgebraicClosure F) (x : K) (v : Fin 2 → F)
    (c a b : ℕ) (G : P3 (AlgebraicClosure F))
    (hd : G ∣ aeval (rowForm (vandermonde (fun i : Fin 3 => ι (x^((Fintype.card F)^i.val))))) (homQ (K:=AlgebraicClosure F) c a b))
    (hv : eval (algebraMap F _ ∘ v) (affineChart _ 2 G) = 0) :
    let α := ∑ j : Fin 3, algebraMap F K ((Fin.cons 1 v : Fin 3 → F) j) * x^j.val
    let A := α^c; let B := (α^(Fintype.card F))^c; let D := ((α^(Fintype.card F))^(Fintype.card F))^c
    altQuot (A+B+D) (A*B+B*D+D*A) (A*B*D) a b = 0 := by
  intro α A B D
  rw [eval_chart] at hv
  obtain ⟨r,hr⟩ := hd
  have hh := congrArg (eval (Fin.cons 1 (algebraMap F (AlgebraicClosure F) ∘ v))) hr
  rw [map_mul,hv,zero_mul,eval_rows] at hh
  simp_rw [chartRows] at hh
  simp only [homQ,mapQ,map_add,map_mul,map_pow,eval_X] at hh
  apply ι.injective
  rw [map_zero,mapQ]
  simp only [map_add,map_mul]
  convert hh using 2 <;> simp [A,B,D,α,pow_two,pow_mul] <;> ring
end E707Geometry


end

-- Bundled module: ProjectiveChartSet
section



namespace E707Geometry
open MvPolynomial E707Monge E707Partial
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

noncomputable def chartPoint (x : K) (hx : Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val)))
    (v : Fin 2 → F) : projectiveImage F K :=
  let u := Units.mk0 (chartAlpha x v) (chartAlpha_ne_zero x hx v)
  ⟨u^((Fintype.card F)-1),u,rfl⟩
lemma chartPoint_injective (x : K) (hx : Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val))) :
    Function.Injective (chartPoint x hx) := fun _ _ h => chartAlpha_power_injective x hx
      (congrArg (fun z : projectiveImage F K => ((z.val : Kˣ):K)) h)
noncomputable def chartSet (x : K) (hx : Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val)))
    (G : P3 (AlgebraicClosure F)) : Finset (projectiveImage F K) := by
  classical
  exact ({v : Fin 2 → F | eval (algebraMap F _ ∘ v) (affineChart _ 2 G) = 0} : Set _).toFinset.image (chartPoint x hx)
theorem chartSet_spec (ι : K →ₐ[F] AlgebraicClosure F) (x : K)
    (hx : Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val))) (c a b : ℕ) (G : P3 (AlgebraicClosure F))
    (hd : G ∣ aeval (rowForm (Matrix.vandermonde (fun i : Fin 3 => ι (x^((Fintype.card F)^i.val))))) (homQ (K:=AlgebraicClosure F) c a b)) :
    chartSet x hx G ⊆ locus F K (c*a) (c*b) ∧ (chartSet x hx G).card =
      ({v : Fin 2 → F | eval (algebraMap F _ ∘ v) (affineChart _ 2 G) = 0} : Set _).ncard := by
  classical
  constructor
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    simp only [Set.mem_toFinset,Set.mem_ofPred_eq] at hv
    have h := chartQuotientZero ι x v c a b G hd hv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,quotientZero_onCurve F K (Units.mk0 (chartAlpha x v) (chartAlpha_ne_zero x hx v)) a b c h⟩
  · rw [chartSet,Finset.card_image_of_injective _ (chartPoint_injective x hx), Set.ncard_eq_toFinset_card']
universe u w
theorem largeProjectiveComponent (c a b : ℕ) (hc : 0<c) (ha : c<c*a) (hb : 2*(c*a)<c*b)
    (hg : (c*a).gcd (c*b)=c) : ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F]
    (K : Type w) [Field K] [Fintype K] [Algebra F K] [NeZero ((c*a:ℕ):AlgebraicClosure F)]
    (ι : K →ₐ[F] AlgebraicClosure F), Module.finrank F K = 3 → Q ≤ Fintype.card F →
    ∃ (x : K) (hx : Function.Injective (fun i : Fin 3 => x^(Fintype.card F^i.val)))
      (G : P3 (AlgebraicClosure F)), Irreducible (affineChart _ 2 G) ∧
      (affineChart _ 2 G).totalDegree ≤ c*a+c*b ∧ chartSet x hx G ⊆ locus F K (c*a) (c*b) ∧
      Fintype.card F ≤ 2*(chartSet x hx G).card := by
  obtain ⟨Q,hQ⟩ := cubicMajorCount.{u,w} c a b hc ha hb hg
  refine ⟨Q,?_⟩
  intro F _ _ K _ _ _ _ ι h3 hq
  obtain ⟨x,hx,G,hi,hd,hdiv,hcount⟩ := hQ F K ι h3 hq
  obtain ⟨hs,hcard⟩ := chartSet_spec ι x hx c a b G hdiv
  exact ⟨x,hx,G,hi,hd,hs,hcard ▸ hcount⟩
end E707Geometry


end

-- Bundled module: Newton707
section


namespace E707Monge
open E707Geometry Polynomial
variable {R : Type*} [CommRing R]
def sec (y z : R) : ℕ → R
  | 0 => 0
  | n+1 => z^n + y * sec y z n

def dd (x y z : R) : ℕ → R
  | 0 => 0
  | n+1 => sec y z n + x*dd x y z n

lemma remNewton (x y z : R) (n : ℕ) :
    cubicRem (x+y+z) (x*y+y*z+z*x) (x*y*z) n =
    (z^n-sec y z n*z + dd x y z n*y*z,sec y z n-dd x y z n*(y+z),dd x y z n) := by
  induction n with
  | zero => simp [cubicRem,sec,dd]
  | succ n ih => rw [cubicRem,ih]; simp only [dd,sec,pow_succ, Prod.mk.injEq]; exact ⟨by ring, by ring, by ring⟩

lemma quotientNewton (x y z : R) (n : ℕ) :
    altQuot (x+y+z) (x*y+y*z+z*x) (x*y*z) 1 n = dd x y z n := by
  simp [altQuot, remNewton, sec, dd]

lemma interpNewton (x y z : R) (n : ℕ) :
    x^n = z^n + sec y z n*(x-z) + dd x y z n*(x-y)*(x-z) := by
  have h := cubicRem_spec (x+y+z) (x*y+y*z+z*x) (x*y*z) x (by ring) n
  rw [remNewton] at h
  linear_combination h

lemma sec_map {S : Type*} [CommRing S] (f : R →+* S) (y z : R) (n : ℕ) :
  f (sec y z n) = sec (f y) (f z) n := by induction n with | zero => simp [sec] | succ n h => simp [sec,h]

lemma dd_map {S : Type*} [CommRing S] (f : R →+* S) (x y z : R) (n : ℕ) :
  f (dd x y z n) = dd (f x) (f y) (f z) n := by induction n with | zero => simp [dd] | succ n h => simp [dd,sec_map,h]
end E707Monge

end

-- Bundled module: Tangency707
section

namespace E707Monge
open Polynomial
variable {K : Type*} [Field K]
lemma secDiff (x y z : K) (n : ℕ) : sec x z n - sec y z n = (x-y)*dd x y z n := by
  induction n with
  | zero => simp [sec,dd]
  | succ n ih => simp only [sec,dd]; linear_combination x*ih

lemma ddCycle (x y z : K) (n : ℕ) : dd x y z n = dd y z x n := by
  rw [←quotientNewton,←quotientNewton]; congr 1 <;> ring

lemma secComm (x y : K) (n : ℕ) : sec x y n = sec y x n := by
  by_cases h : x=y
  · simp [h]
  have h₁ := interpNewton x x y n
  have h₂ := interpNewton y y x n
  simp only [sub_self,mul_zero,zero_mul,add_zero] at h₁ h₂
  apply mul_right_cancel₀ (sub_ne_zero.mpr h) (b:=x-y)
  linear_combination -h₂ - h₁

noncomputable abbrev slice (y z : K) (n : ℕ) : K[X] := dd X (C y) (C z) n

lemma tangent (x y z : K) (n : ℕ) (hq : dd x y z (n+1) = 0)
    (hd : (slice y z (n+1)).derivative.eval x = 0) :
    ((n+1:ℕ):K)*x^n = sec y z (n+1) := by
  have h := interpNewton (X : K[X]) (C y) (C z) (n+1)
  rw [←map_pow,←sec_map] at h
  have h' := congrArg (fun f : K[X] => f.derivative.eval x) h
  have he := dd_map (evalRingHom x) (X : K[X]) (C y) (C z) (n+1)
  simp only [coe_evalRingHom,eval_X,eval_C,hq] at he
  simp only [slice] at hd
  simp [derivative_mul, derivative_X_pow,hd,he] at h'
  simpa only [←map_pow, derivative_C, eval_zero, zero_add,Nat.cast_add_one] using h'

lemma noTwoTangents (x y z : K) (n : ℕ) (hn : 0<n) (hN : ((n+1:ℕ):K) ≠ 0)
    (hnK : (n:K) ≠ 0) (hq : dd x y z (n+1)=0)
    (hx : (slice y z (n+1)).derivative.eval x = 0)
    (hy : (slice z x (n+1)).derivative.eval y = 0) : x=y := by
  have tx := tangent x y z n hq hx
  have ty := tangent y z x n ((ddCycle x y z _).symm.trans hq) hy
  rw [secComm z x] at ty
  have hs := secDiff x y z (n+1)
  rw [hq,mul_zero,sub_eq_zero] at hs
  rw [hs] at ty
  have hp : x^n=y^n := mul_left_cancel₀ hN (tx.trans ty.symm)
  have hi := interpNewton x y z (n+1)
  have hj := interpNewton y y z (n+1)
  simp only [hq,zero_mul,add_zero,sub_self,mul_zero,pow_succ] at hi hj
  rw [←hp,←tx] at hj
  rw [←tx] at hi
  have hh : (n:K)*x^n*(x-y)=0 := by push_cast at hi hj; linear_combination hj-hi
  rcases mul_eq_zero.mp hh with h|h
  · have h0 := (mul_eq_zero.mp h).resolve_left hnK
    have h1 := eq_zero_of_pow_eq_zero h0
    have h2 := eq_zero_of_pow_eq_zero (hp ▸ h0 : y^n = 0)
    exact h1.trans h2.symm
  · exact sub_eq_zero.mp h
end E707Monge

end

-- Bundled module: PowerSing707
section

namespace E707Monge
variable {K : Type*} [Field K]
lemma secDiag (t : K) (m : ℕ) : sec t t (m+1) = (m+1:ℕ)*t^m := by
  induction m with
  | zero => simp [sec]
  | succ m h => rw [sec,h,pow_succ]; push_cast; ring
lemma ddDiag (t : K) (m : ℕ) : 2 * dd t t t (m+2) = ((m+2:ℕ):K)*(m+1:ℕ)*t^m := by
  induction m with
  | zero => norm_num [dd,sec]
  | succ m h => rw [dd,secDiag,pow_succ]; push_cast at *; linear_combination t*h
lemma sec0 (t : K) (m : ℕ) : sec 0 t (m+1) = t^m := by simp [sec]
lemma ddTwo (t : K) (m : ℕ) : dd 0 t t (m+2) = (m+1:ℕ)*t^m := by simp [dd,secDiag]
lemma ddOne (t : K) (m : ℕ) : dd 0 0 t (m+2) = t^m := by simp [dd,sec]

open Polynomial
/-- The nonzero coordinates of a singular power pullback have equal c-th powers. -/
theorem noPowerSing (x y z : K) (m : ℕ)
    (hN : ((m+2:ℕ):K) ≠ 0) (hn : ((m+1:ℕ):K) ≠ 0)
    (hq : dd x y z (m+2) = 0)
    (hx : x ≠ 0 → (slice y z (m+2)).derivative.eval x = 0)
    (hy : y ≠ 0 → (slice z x (m+2)).derivative.eval y = 0)
    (hz : z ≠ 0 → (slice x y (m+2)).derivative.eval z = 0) : x=0 ∧ y=0 ∧ z=0 := by
  have hq' := (ddCycle x y z _).symm.trans hq
  have hq'' := (ddCycle y z x _).symm.trans hq'
  have xy := fun a b => noTwoTangents x y z (m+1) (by omega) hN hn hq (hx a) (hy b)
  have yz := fun a b => noTwoTangents y z x (m+1) (by omega) hN hn hq' (hy a) (hz b)
  have zx := fun a b => noTwoTangents z x y (m+1) (by omega) hN hn hq'' (hz a) (hx b)
  by_cases a : x=0 <;> by_cases b : y=0 <;> by_cases c : z=0
  · exact ⟨a,b,c⟩
  all_goals exfalso
  · rw [a,b,ddOne] at hq; exact pow_ne_zero _ c hq
  · rw [c,a,ddOne] at hq''; exact pow_ne_zero _ b hq''
  · rw [a,yz b c,ddTwo] at hq; exact mul_ne_zero hn (pow_ne_zero _ c) hq
  · rw [b,c,ddOne] at hq'; exact pow_ne_zero _ a hq'
  · rw [b,zx c a,ddTwo] at hq'; exact mul_ne_zero hn (pow_ne_zero _ a) hq'
  · rw [c,xy a b,ddTwo] at hq''; exact mul_ne_zero hn (pow_ne_zero _ b) hq''
  · rw [xy a b,yz b c] at hq
    have h := ddDiag z m
    rw [hq,mul_zero] at h
    exact mul_ne_zero (mul_ne_zero hN hn) (pow_ne_zero _ c) h.symm
end E707Monge

end

-- Bundled module: CutSing707
section


namespace E707Monge
open MvPolynomial
open scoped Polynomial
variable {K : Type*} [Field K]
noncomputable def cutAt (v : Fin 3 → K) (i : Fin 3) : P3 K →ₐ[K] K[X] :=
  aeval fun j => if j=i then Polynomial.X else Polynomial.C (v j)
lemma cutEval (v : Fin 3 → K) (i : Fin 3) (f : P3 K) :
  (cutAt v i f).eval (v i) = aeval v f := by
  have he : (Polynomial.aeval (v i)).comp (cutAt v i) = aeval v := by
    ext1 j; by_cases h : j=i <;> simp [cutAt,h]
  simpa using AlgHom.congr_fun he f
lemma cutDerivative (v : Fin 3 → K) (i : Fin 3) {f g : P3 K}
    (hf : aeval v f=0) (hg : aeval v g=0) :
    (cutAt v i (f*g)).derivative.eval (v i) = 0 := by
  simp [Polynomial.derivative_mul,cutEval,hf,hg]
lemma cutDD (v : Fin 3 → K) {i j l : Fin 3} (hj : j ≠ i) (hl : l ≠ i) (n c : ℕ) :
    cutAt v i (dd ((X i)^c) ((X j)^c) ((X l)^c) n) =
    (slice ((v j)^c) ((v l)^c) n).comp (Polynomial.X^c) := by
  change (cutAt v i).toRingHom _ = _
  rw [dd_map];
  have he := dd_map (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X^c : K[X]))
    Polynomial.X (Polynomial.C ((v j)^c)) (Polynomial.C ((v l)^c)) n
  simpa [slice,cutAt,hj,hl,map_pow,Polynomial.comp,Polynomial.eval₂RingHom] using he.symm
lemma cutTangent (v : Fin 3 → K) {i j l : Fin 3} (hj : j ≠ i) (hl : l ≠ i) (n c : ℕ) (hc : (c:K) ≠ 0)
    {f g : P3 K} (hf : aeval v f=0) (hg : aeval v g=0)
    (he : dd ((X i)^c) ((X j)^c) ((X l)^c) n = f*g) (hi : (v i)^c ≠ 0) :
    (slice ((v j)^c) ((v l)^c) n).derivative.eval ((v i)^c) = 0 := by
  have h := cutDerivative v i hf hg
  rw [←he,cutDD v hj hl,Polynomial.derivative_comp] at h
  simp only [Polynomial.eval_mul,Polynomial.eval_comp, Polynomial.eval_pow,Polynomial.eval_X,Polynomial.derivative_X_pow,Polynomial.eval_natCast] at h
  by_cases hz : v i=0
  · have hc' : c ≠ 0 := by rintro rfl; simp at hc
    simp [hz,hc'] at hi
  · exact (mul_eq_zero.mp h).resolve_left (by simpa using mul_ne_zero hc (pow_ne_zero (c-1) hz))
end E707Monge

end

-- Bundled module: Origin707
section



namespace E707Monge
open MvPolynomial
variable {K : Type*} [Field K]
abbrev A3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
noncomputable def trunc3 (n : ℕ) : A3 K →ₐ[K] A3 K := aeval fun i => if i.val < n then 0 else X i
noncomputable abbrev J3 (K : Type*) [Field K] (n : ℕ) := RingHom.ker (trunc3 (K:=K) n).toRingHom
instance J3prime (n : ℕ) : (J3 K n).IsPrime := RingHom.ker_isPrime _
lemma J3_lt (i : Fin 3) : J3 K i.val < J3 K (i.val+1) := by
  have comp : (trunc3 (K:=K) (i.val+1)).comp (trunc3 i.val) = trunc3 (i.val+1) := by
    ext1 j; by_cases h : j < i
    · simp [trunc3,h,le_of_lt h]
    · simp [trunc3,h]
  constructor
  · intro f hf; change trunc3 (i.val+1) f = 0; rw [←comp,AlgHom.comp_apply]; change trunc3 i.val f = 0 at hf; simp [hf]
  · intro h; have hmem : X i ∈ J3 K (i.val+1) := by change trunc3 _ _ = 0; simp [trunc3]
    have := h hmem; change trunc3 i.val (X i : A3 K) = 0 at this; simpa [trunc3] using this

lemma heightOrigin : 3 ≤ (vanishingIdeal K ({0} : Set (Fin 3 → K))).height := by
  have h := fun i : Fin 3 => Ideal.height_add_one_le_of_lt_of_isPrime (J3_lt (K:=K) i)
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have hL : 3 ≤ (J3 K 3).height := calc
    3 = (0+1+1+1 : ℕ∞) := by norm_num
    _ ≤ (J3 K 0).height+1+1+1 := by gcongr; exact bot_le
    _ ≤ _ := add_le_add (add_le_add h0 (le_refl 1)) (le_refl 1)
    _ ≤ _ := add_le_add h1 (le_refl 1)
    _ ≤ _ := h2
  apply hL.trans (Ideal.height_mono _)
  intro f hf; rw [mem_vanishingIdeal_singleton_iff]; change trunc3 3 f = 0 at hf
  have hE : (aeval (R:=K) (0 : Fin 3 → K)).comp (trunc3 3) = aeval 0 := by
    ext i; simp [trunc3,i.isLt]
  rw [←hE,AlgHom.comp_apply,hf,map_zero]
end E707Monge

end

-- Bundled module: PlaneMeet707
section

namespace E707Monge
open MvPolynomial
variable {K : Type*} [Field K] [IsAlgClosed K]
theorem planeMeet (f g : A3 K) (hf : aeval (0 : Fin 3 → K) f = 0) (hg : aeval (0 : Fin 3 → K) g = 0) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ aeval v f = 0 ∧ aeval v g = 0 := by
  classical
  by_contra! hn
  let s : Finset (A3 K) := {f,g}
  have hs : (s : Set (A3 K)) = {f,g} := by simp [s]
  have hZ : zeroLocus K (Ideal.span (s : Set (A3 K))) = {0} := by
    rw [hs,zeroLocus_span]; ext v; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h; by_contra hv; exact hn v hv (h _ (by simp)) (h _ (by simp))
    · rintro rfl p (rfl|hp); exact hf; obtain rfl := Set.mem_singleton_iff.mp hp; exact hg
  have hR := vanishingIdeal_zeroLocus_eq_radical (K:=K) (Ideal.span (s : Set (A3 K)))
  rw [hZ] at hR
  have hmin : vanishingIdeal K ({0} : Set (Fin 3 → K)) ∈ (Ideal.span (s : Set (A3 K))).minimalPrimes := by
    rw [←Ideal.radical_minimalPrimes,←hR]; exact ⟨⟨inferInstance,le_rfl⟩,fun _ hp _ => hp.2⟩
  have hu := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hcard : s.card ≤ 2 := by exact (Finset.card_insert_le _ _).trans (by simp)
  have ht : (3:ℕ∞) ≤ 2 := (heightOrigin (K:=K)).trans (hu.trans (by exact_mod_cast hcard))
  norm_num at ht
end E707Monge

end

-- Bundled module: EqualGcd707
section




namespace E707Monge
open MvPolynomial
variable {K : Type*} [Field K]
lemma secHom {x y : P3 K} {c : ℕ} (hx : x.IsHomogeneous c) (hy : y.IsHomogeneous c) (m : ℕ) :
    (sec x y (m+1)).IsHomogeneous (c*m) := by
  induction m with
  | zero => simp [sec]; exact isHomogeneous_one _ _
  | succ m ih => rw [sec]; exact (hy.pow _).add (by simpa [Nat.mul_succ,add_comm] using hx.mul ih)
lemma ddHom {x y z : P3 K} {c : ℕ} (hx : x.IsHomogeneous c) (hy : y.IsHomogeneous c) (hz : z.IsHomogeneous c) (m : ℕ) :
    (dd x y z (m+2)).IsHomogeneous (c*m) := by
  induction m with
  | zero => simp [dd,sec]; exact isHomogeneous_one _ _
  | succ m ih => rw [dd]; exact (secHom hy hz _).add (by simpa [Nat.mul_succ,add_comm] using hx.mul ih)
lemma eqDD (c n : ℕ) : homQ (K:=K) c 1 n = dd ((X 2)^c) ((X 1)^c) ((X 0)^c) n := quotientNewton ..
lemma ddRot {R : Type*} [CommRing R] (x y z : R) (n : ℕ) : dd x y z n = dd y z x n := by
  rw [←quotientNewton,←quotientNewton]; congr 1 <;> ring
lemma homNonunitOrigin {f : P3 K} (hn : f ≠ 0) (hh : f.IsHomogeneous f.totalDegree) (hu : ¬IsUnit f) : aeval (0 : Fin 3 → K) f = 0 := by
  rw [aeval_zero,constantCoeff_eq]; simp only [Algebra.algebraMap_self_apply]
  by_contra h
  have hd := hh h
  have h0 : f.totalDegree = 0 := by simpa using hd.symm
  have he := totalDegree_eq_zero_iff_eq_C.mp h0
  exact hu (he ▸ (isUnit_iff_ne_zero.mpr h).map (C : K →+* _))

theorem equalGcdIrred [IsAlgClosed K] (c m : ℕ) (hc : 0 < c) (hm : 0 < m) (hp : (c:K) ≠ 0)
    (hN : ((m+2:ℕ):K) ≠ 0) (hn : ((m+1:ℕ):K) ≠ 0) : Irreducible (homQ (K:=K) c 1 (m+2)) := by
  let H := homQ (K:=K) c 1 (m+2)
  have hhom : H.IsHomogeneous (c*m) := by
    change (homQ (K:=K) _ _ _).IsHomogeneous _; rw [eqDD]; exact ddHom (isHomogeneous_X_pow 2 c) (isHomogeneous_X_pow 1 c) (isHomogeneous_X_pow 0 c) _
  have hd := (planeTop (K:=K) c 1 (m+2) hc (by simpa) (by simp; nlinarith)).1
  have hH : H ≠ 0 := by
    intro he; have hs := spec_homQ (K:=K) c 1 (m+2); change spec3 H = _ at hs; rw [he,map_zero] at hs; rw [←hs,Polynomial.natDegree_zero] at hd; nlinarith
  refine ⟨fun hu => ?_,?_⟩
  · have h0 := (isUnit_iff_totalDegree_of_isReduced.mp hu).2; have h1 := hhom.totalDegree hH; change H.totalDegree=0 at h0; nlinarith
  intro f g he; change H = f*g at he
  by_contra! hbad
  have aux {p : P3 K} (hdiv : p ∣ H) (hu : ¬IsUnit p) : aeval (0 : Fin 3 → K) p = 0 :=
    homNonunitOrigin (fun e => hH (zero_dvd_iff.mp (e ▸ hdiv))) (HomDiv707.homogeneous_of_dvd hH hhom hdiv) hu
  obtain ⟨v,hv,hf,hg⟩ := planeMeet f g (aux (he ▸ dvd_mul_right ..) hbad.1) (aux (he ▸ dvd_mul_left ..) hbad.2)
  let w (i : Fin 3) := (X i : P3 K)^c
  let t (i : Fin 3) := (v i)^c
  have he0 : dd (w 2) (w 1) (w 0) (m+2) = f*g := (eqDD _ _).symm.trans he
  have he1 := (ddRot (w 2) (w 1) (w 0) (m+2)).symm.trans he0
  have he2 := (ddRot (w 1) (w 0) (w 2) (m+2)).symm.trans he1
  have hz : dd (t 2) (t 1) (t 0) (m+2) = 0 := by
    have h := congrArg (aeval v).toRingHom he0; rw [dd_map] at h; change eval v f = 0 at hf; simpa [t,w,hf] using h
  obtain ⟨a,b,d⟩ := noPowerSing (t 2) (t 1) (t 0) m hN hn hz
    (cutTangent v (by decide : (1:Fin 3)≠2) (by decide) _ c hp hf hg he0)
    (cutTangent v (by decide : (0:Fin 3)≠1) (by decide) _ c hp hf hg he1)
    (cutTangent v (by decide : (2:Fin 3)≠0) (by decide) _ c hp hf hg he2)
  apply hv; funext i; fin_cases i <;> first | exact eq_zero_of_pow_eq_zero d | exact eq_zero_of_pow_eq_zero b | exact eq_zero_of_pow_eq_zero a
end E707Monge

end

-- Bundled module: EqualProjective707
section


namespace E707Geometry
open MvPolynomial Matrix E707Monge E707Partial
variable {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

omit [Fintype K] in
private lemma shiftOrbit (x : K) (n : ℕ) : (x+1)^((Fintype.card F)^n) = x^((Fintype.card F)^n)+1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, pow_mul, ih]
    exact (map_add (FiniteField.frobeniusAlgHom F K) _ _).trans (by rw [map_one]; rfl)
private lemma goodOrbit (h3 : Module.finrank F K = 3) (hchar : (3:K) ≠ 0) :
    ∃ x : K, Function.Injective (fun i : Fin 3 => x^((Fintype.card F)^i.val)) ∧
      x^((Fintype.card F)^2)+x^((Fintype.card F)^1)+x^((Fintype.card F)^0) ≠ 0 := by
  obtain ⟨x,hx⟩ := cubicOrbit h3
  by_cases h : x^((Fintype.card F)^2)+x^((Fintype.card F)^1)+x^((Fintype.card F)^0) = 0
  · refine ⟨x+1,fun i j hij => hx ?_,?_⟩
    · simpa only [shiftOrbit (F:=F),add_left_inj] using hij
    · simp only [shiftOrbit (F:=F)]; intro he; apply hchar; linear_combination he-h
  · exact ⟨x,hx,h⟩
private lemma lineAvoid {k : Type*} [Field k] (t : Fin 3 → k) (ht : t 2+t 1+t 0 ≠ 0) :
    ¬ Associated (aeval (rowForm (vandermonde t)) (homQ (K:=k) 1 1 3)) (X 0) := by
  intro h
  let v : Fin 3 → k := ![0,1,0]
  have he := h.symm.dvd
  obtain ⟨g,hg⟩ := he
  have ev := congrArg (eval v) hg
  rw [eqDD] at ev
  apply ht
  have hz : t 0+t 1+t 2=0 := by simpa [dd,sec,rowForm,vandermonde_apply,Fin.sum_univ_three,v] using ev
  linear_combination hz

universe u w
/-- Equal-gcd branch: the entire twisted quotient is a geometric prime. -/
theorem equalGcdProjectiveComponent (c m : ℕ) (hc : 0 < c) (hm : 0 < m) :
    ∃ Q : ℕ, ∀ (F : Type u) [Field F] [Fintype F]
    (K : Type w) [Field K] [Fintype K] [Algebra F K]
    (_ι : K →ₐ[F] AlgebraicClosure F), Module.finrank F K = 3 → Q ≤ Fintype.card F →
    (c : AlgebraicClosure F) ≠ 0 → ((m+2:ℕ):AlgebraicClosure F) ≠ 0 →
    ((m+1:ℕ):AlgebraicClosure F) ≠ 0 →
    ∃ (x : K) (hx : Function.Injective (fun i : Fin 3 => x^(Fintype.card F^i.val)))
      (G : P3 (AlgebraicClosure F)), Irreducible (affineChart _ 2 G) ∧
      (affineChart _ 2 G).totalDegree = c*m ∧ chartSet x hx G ⊆ locus F K c (c*(m+2)) ∧
      Fintype.card F ≤ 2*(chartSet x hx G).card := by
  obtain ⟨Q,hQ⟩ := halfCountChart.{u} (c*m)
  refine ⟨Q,?_⟩
  intro F _ _ K _ _ _ ι h3 hq hp hN hn
  let q₀ := Fintype.card F
  obtain ⟨x,hx,hline⟩ : ∃ x : K, Function.Injective (fun i : Fin 3 => x^(q₀^i.val)) ∧
      (c*m=1 → x^(q₀^2)+x^(q₀^1)+x^(q₀^0) ≠ 0) := by
    by_cases h : c*m=1
    · have hm1 : m=1 := by nlinarith [Nat.mul_le_mul_right m hc]
      have hn3 : (3:AlgebraicClosure F) ≠ 0 := by simpa [hm1] using hN
      have h3K : (3:K) ≠ 0 := by
        intro he; apply hn3
        exact (map_ofNat ι 3).symm.trans ((congrArg ι he).trans (map_zero ι))
      obtain ⟨x,hx,ht⟩ := goodOrbit h3 h3K
      exact ⟨x,hx,fun _ => ht⟩
    · obtain ⟨x,hx⟩ := cubicOrbit h3
      exact ⟨x,hx,fun h' => (h h').elim⟩
  let t := fun i : Fin 3 => ι (x^(q₀^i.val))
  let e := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hcard : Fintype.card K = q₀^3 := by rw [Module.card_eq_pow_finrank (K:=F),h3]
  have hcycle (i) : e (t i) = t (finRotate 3 i) := by
    change (ι _) ^ q₀ = ι _
    rw [← map_pow,← pow_mul]
    fin_cases i <;> simp [finRotate_apply, pow_succ]
    rw [show q₀*q₀*q₀ = q₀^3 by ring, ← hcard, ← map_pow,FiniteField.pow_card]
  let A := vandermonde t
  let E := rowEquiv A (isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr (ι.injective.comp hx)))
  let H := homQ (K:=AlgebraicClosure F) c 1 (m+2)
  let G := E H
  have hi : Irreducible G := (equalGcdIrred c m hc hm hp hN hn).map E.toMulEquiv
  have hh : G.IsHomogeneous (c*m) := by
    apply rowSubstHom A
    change (homQ (K:=AlgebraicClosure F) c 1 (m+2)).IsHomogeneous _
    rw [eqDD]; exact ddHom (isHomogeneous_X_pow 2 c) (isHomogeneous_X_pow 1 c) (isHomogeneous_X_pow 0 c) _
  have ha : ¬Associated G (X 0) := by
    by_cases h : c*m=1
    · have hc1 : c=1 := by nlinarith [Nat.mul_le_mul_left c hm]
      have hm1 : m=1 := by nlinarith [Nat.mul_le_mul_right m hc]
      have ht : t 2+t 1+t 0 ≠ 0 := by
        intro he; apply hline h; apply ι.injective; simpa [t] using he
      change ¬Associated (aeval (rowForm A) (homQ (K:=AlgebraicClosure F) c 1 (m+2))) _
      rw [hc1,hm1]; exact lineAvoid t ht
    · intro he
      have hle := totalDegree_le_of_dvd_of_isDomain he.dvd (X_ne_zero (R:=AlgebraicClosure F) (0:Fin 3))
      rw [hh.totalDegree hi.ne_zero,totalDegree_X] at hle
      have hpos := Nat.mul_pos hc hm; omega
  have hs : Associated G (map (e : AlgebraicClosure F →+* _) G) := by
    apply twistAssociated _ (finRotate 3) (rowForm A)
    · intro i; simp [A,rowForm,vandermonde_apply,hcycle]
    · have he : MvPolynomial.map (e : AlgebraicClosure F →+* _) H = H := by simp [H,homQ,mapQ]
      rw [he]
    · rw [show rename (finRotate 3) H = H from rotQ ..]
  obtain ⟨hi',hd⟩ := irreducible_affineChart hh hi ha
  have count := hQ F G _ hq le_rfl hh hi ha hs
  obtain ⟨hsub,hcard⟩ := chartSet_spec ι x hx c 1 (m+2) G (dvd_refl _)
  exact ⟨x,hx,G,hi',hd,by simpa using hsub,hcard ▸ count⟩
end E707Geometry

end

-- Bundled module: CoprimeLocusCount
section


namespace E707Geometry
open E707Partial
/-- For all coprime exponent shapes, the projective sieve locus has at least q/2 points. -/
theorem coprimeLocusCount (u v : ℕ) (hu : 0<u) (hv : 2*u<v) (hg : u.Coprime v) :
    ∃ Q : ℕ, ∀ (p : ℕ) (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    [CharP F p], v<p → Q≤Fintype.card F → Module.finrank F K=3 →
    Fintype.card F ≤ 2*(locus F K u v).card := by
  by_cases he : u=1
  · subst u
    let m := v-2
    have hm : 0 < m := by dsimp [m]; omega
    have he : m+2=v := by dsimp [m]; omega
    obtain ⟨Q,hQ⟩ := equalGcdProjectiveComponent.{0,0} 1 m (by decide) hm
    refine ⟨Q,?_⟩; intro p F K _ _ _ _ _ _ hp hq h3
    haveI : CharP (AlgebraicClosure F) p := charP_of_injective_algebraMap (algebraMap F _).injective p
    have nz (n : ℕ) (h : 0<n) (hn : n<p) : (n : AlgebraicClosure F) ≠ 0 := by
      intro h0; exact (Nat.not_dvd_of_pos_of_lt h hn) ((CharP.cast_eq_zero_iff _ p n).mp h0)
    obtain ⟨x,hx,G,-,-,hs,hc⟩ := hQ F K IsAlgClosed.lift h3 hq (by norm_num) (nz _ (by omega) (by omega)) (nz _ (by omega) (by omega))
    simp only [one_mul,he] at hs
    exact hc.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hs))
  · obtain ⟨Q,hQ⟩ := largeProjectiveComponent.{0,0} 1 u v (by decide) (by simp; omega) (by simpa using hv) (by simpa using hg)
    refine ⟨Q,?_⟩; intro p F K _ _ _ _ _ _ hp hq h3
    haveI : CharP (AlgebraicClosure F) p := charP_of_injective_algebraMap (algebraMap F _).injective p
    haveI : NeZero ((1*u:ℕ):AlgebraicClosure F) := ⟨by
      rw [one_mul]; intro h0; exact (Nat.not_dvd_of_pos_of_lt hu (by omega : u<p)) ((CharP.cast_eq_zero_iff _ p u).mp h0)⟩
    obtain ⟨x,hx,G,-,-,hs,hc⟩ := hQ F K IsAlgClosed.lift h3 hq
    simp only [one_mul] at hs
    exact hc.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hs))
end E707Geometry

end

-- Bundled module: PrimitiveInputs
section



namespace E707Geometry
open E707Partial Polynomial
private theorem cofinalOfDivisorBounds (u v : ℕ) (hu : 0<u) (hv : 2*u<v) (hg : u.Coprime v)
    (hdeg : ∀ (K : Type) [Field K] (g : K[X][X]), g ∣ detChart K u v →
      g.natDegree ≤ chartBudget u v ∧ ∀ j, (g.coeff j).natDegree ≤ chartBudget u v) : CofinalPoints u v := by
  classical
  intro L
  let d := chartBudget u v
  obtain ⟨Q,hQ⟩ := coprimeLocusCount u v hu hv hg
  obtain ⟨p,k,b,F,K,iF,fF,iK,fK,iA,cF,cK,hvp,hp,hp3,hL,hk,hb,hmargin,hq,hQq,hdq,h3⟩ := chooseDenseTower v L Q d
  have hs := hQ p F K hvp hQq h3
  obtain ⟨g,T,hi,hdiv,hsub,hsize,hzeros⟩ := denseTorusFactor F K u v hu (by omega) _ (Finset.Subset.refl _) hs
  have ht : d < T.card := by
    by_contra! he; exact hdq.not_ge (hsize.trans (Nat.mul_le_mul_left _ he))
  obtain ⟨hy,hx⟩ := hdeg K g hdiv
  have hr := denseChartRatio F K p k d hp3 hq h3 hk T ht g hi hy hx hzeros
  obtain ⟨z,ho,hz⟩ := densityPackedPoint F K p k (2*d^2) b u v (4*d) hp.two_le hp3 hb hmargin hq h3 T hsub hsize hr
  exact ⟨p,k,F,K,iF,fF,iK,fK,iA,hp3,hL,hq,h3,z,ho,hz⟩
theorem primitiveInputs : H1 ∧ H2 := by
  apply witnessesOfCofinal
  intro u v hu hv hg
  apply cofinalOfDivisorBounds u v hu hv hg
  intro K _ g hdiv
  obtain ⟨hy,hx⟩ := det_bidegree (K:=K) u v
  obtain ⟨hg',hg''⟩ := chartDivisorDegree hdiv (detChart_ne_zero (K:=K) u v hu (by omega)) hx
  exact ⟨hg'.trans hy,hg''⟩
end E707Geometry

end


-- Reduction Erdos707.erdos_707.variants.small_sidon_sets.R1 of Erdős Problem 707: Embedding Sidon Sets in Perfect Difference Sets — small sidon sets
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
namespace OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R1

/-- Field witness for normalized triples `{0, u, v}` with `v < 2u`. -/
def H1 : Prop := ∀ u v : ℕ, 0 < u → u < v → v < 2 * u →
  ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K) (_ : Algebra F K),
    Module.finrank F K = 3 ∧ v < Nat.card F ^ 2 + Nat.card F + 1 ∧
    ∃ (α : K) (s t : F),
      IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1) ∧
      α ^ v = algebraMap F K s + algebraMap F K t * α ^ u

/-- Field witness for normalized triples `{0, u, v}` with `2u < v`. -/
def H2 : Prop := ∀ u v : ℕ, 0 < u → 2 * u < v →
  ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K) (_ : Algebra F K),
    Module.finrank F K = 3 ∧ v < Nat.card F ^ 2 + Nat.card F + 1 ∧
    ∃ (α : K) (s t : F),
      IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1) ∧
      α ^ v = algebraMap F K s + algebraMap F K t * α ^ u

/-! Singer construction adapted from the local proof of the sibling variant. -/

namespace OMA707Singer

lemma cube_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hq
  apply Nat.sub_eq_of_eq_add
  simp only [Nat.add_sub_cancel_left]
  ring

/-- An element fixed by the `q`-th power map lies in the subfield with `q` elements. -/
lemma mem_range_of_pow_card_eq {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (x : K) (hx : x ^ Nat.card F = x) : ∃ a : F, algebraMap F K a = x := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at hx
  have hP0 : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hdeg : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).natDegree
      = Fintype.card F := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hroot : ∀ y : K, y ^ Fintype.card F = y →
      y ∈ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hy, sub_self]
  have hsub : (Finset.univ.image (algebraMap F K)) ⊆
      (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
    apply hroot
    rw [← map_pow, FiniteField.pow_card]
  have hcard : (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset.card
      ≤ (Finset.univ.image (algebraMap F K)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap F K).injective, Finset.card_univ]
    calc (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.toFinset.card
        ≤ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ Fintype.card F - Polynomial.X : Polynomial K).natDegree :=
          Polynomial.card_roots' _
      _ = Fintype.card F := hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hxmem := hroot x hx
  rw [← heq] at hxmem
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hxmem
  exact ⟨a, ha⟩

/-- A generator of the multiplicative group of a finite field, as an element of the field. -/
lemma exists_gen (K : Type*) [Field K] [Finite K] :
    ∃ γ : K, γ ≠ 0 ∧ (∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x) ∧
      (∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m) ∧ γ ^ (Nat.card K - 1) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hg, Nat.card_units]
  refine ⟨(g : K), g.ne_zero, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (hg (Units.mk0 x hx))
    exact ⟨i, by rw [← Units.val_pow_eq_pow_val, hi, Units.val_mk0]⟩
  · intro m hm
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hm, Units.val_one]
  · rw [← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

lemma exists_plane {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) : ∃ W : Submodule F K, Module.finrank F W = 2 := by
  have hli : LinearIndependent F
      (fun i : Fin 2 => (Module.finBasisOfFinrankEq F K h3) (Fin.castSucc i)) :=
    (Module.finBasisOfFinrankEq F K h3).linearIndependent.comp _ (Fin.castSucc_injective 2)
  exact ⟨Submodule.span F
    (Set.range (fun i : Fin 2 => (Module.finBasisOfFinrankEq F K h3) (Fin.castSucc i))), by
      rw [finrank_span_eq_card hli, Fintype.card_fin]⟩

/-- A plane is not stable under multiplication by an element outside the base field. -/
lemma not_stable {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc : c ∉ (algebraMap F K).range) : ¬ ∀ w ∈ W, c * w ∈ W := by
  intro hst
  have hpos : 0 < Module.finrank F W := by omega
  obtain ⟨⟨w, hwW⟩, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hw : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hdeg : (minpoly F c).natDegree = 3 := by
    have hdvd := minpoly.degree_dvd hint
    rw [h3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
    · exact absurd (minpoly.natDegree_eq_one_iff.1 h1) hc
    · exact h3'
  have hli := linearIndependent_pow (K := F) c
  rw [hdeg] at hli
  have hli2 : LinearIndependent F (fun i : Fin 3 => c ^ (i : ℕ) * w) := by
    have hker : LinearMap.ker (LinearMap.mulRight F w) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact mul_right_cancel₀ hw hxy
    exact hli.map' (LinearMap.mulRight F w) hker
  have hmem : ∀ i : ℕ, c ^ i * w ∈ W := by
    intro i
    induction i with
    | zero => simpa using hwW
    | succ k ih =>
      rw [pow_succ', mul_assoc]
      exact hst _ ih
  have hspan : Submodule.span F (Set.range (fun i : Fin 3 => c ^ (i : ℕ) * w)) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hle := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli2, Fintype.card_fin, hW] at hle
  omega

/-- Two planes in a three-dimensional space meet: some nonzero `y ∈ W` has `c * y ∈ W`. -/
lemma key_exists {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc0 : c ≠ 0) : ∃ y ∈ W, y ≠ 0 ∧ c * y ∈ W := by
  have hinj : Function.Injective (LinearMap.mulLeft F c) := by
    intro x y hxy
    exact mul_left_cancel₀ hc0 hxy
  have h1 : Module.finrank F
      (W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) = 2 := by
    rw [LinearEquiv.finrank_map_eq, hW]
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq W
    (W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
      K →ₗ[F] K))
  have h4 : Module.finrank F
      ↥(W ⊔ W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) ≤ 3 := by
    rw [← h3]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F
      ↥(W ⊓ W.map ((LinearEquiv.ofInjectiveEndo (LinearMap.mulLeft F c) hinj : K ≃ₗ[F] K) :
        K →ₗ[F] K)) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hx' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  rw [Submodule.mem_inf, Submodule.mem_map] at hx
  obtain ⟨hxW, y, hyW, hyx⟩ := hx
  have hcy : c * y = x := by
    rw [← hyx]
    rfl
  refine ⟨y, hyW, ?_, ?_⟩
  · rintro rfl
    exact hx' (by rw [← hcy, mul_zero])
  · rw [hcy]
    exact hxW

/-- For `c` outside the base field, the solutions `y ∈ W` of `c * y ∈ W` form a line. -/
lemma key_unique {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]
    (h3 : Module.finrank F K = 3) (W : Submodule F K) (hW : Module.finrank F W = 2)
    (c : K) (hc : c ∉ (algebraMap F K).range) {y y' : K} (hy : y ∈ W) (hy0 : y ≠ 0)
    (hcy : c * y ∈ W) (hy' : y' ∈ W) (hcy' : c * y' ∈ W) : ∃ a : F, y' = a • y := by
  have hne : W ⊓ W.comap (LinearMap.mulLeft F c) ≠ W := by
    intro h
    apply not_stable h3 W hW c hc
    intro w hw
    rw [← h] at hw
    exact (Submodule.mem_inf.1 hw).2
  have hlt : W ⊓ W.comap (LinearMap.mulLeft F c) < W := lt_of_le_of_ne inf_le_left hne
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  have hle1 : Module.finrank F ↥(W ⊓ W.comap (LinearMap.mulLeft F c)) ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hle1
  have hyU : y ∈ W ⊓ W.comap (LinearMap.mulLeft F c) := Submodule.mem_inf.2 ⟨hy, hcy⟩
  have hyU' : y' ∈ W ⊓ W.comap (LinearMap.mulLeft F c) := Submodule.mem_inf.2 ⟨hy', hcy'⟩
  obtain ⟨t, ht⟩ := hv ⟨y, hyU⟩
  obtain ⟨t', ht'⟩ := hv ⟨y', hyU'⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hy0 (congrArg Subtype.val ht).symm
  have e1 : t • (v : K) = y := congrArg Subtype.val ht
  have e2 : t' • (v : K) = y' := congrArg Subtype.val ht'
  refine ⟨t' * t⁻¹, ?_⟩
  rw [← e1, ← e2, smul_smul, inv_mul_cancel_right₀ ht0]

/-- The Singer construction with a specified generator and plane. -/
theorem core_with_plane {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    (γ : K) (hγ0 : γ ≠ 0) (hγsurj : ∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x)
    (hγord : ∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m)
    (hγpow : γ ^ (Nat.card K - 1) = 1)
    (W : Submodule F K) (hW : Module.finrank F W = 2) :
    ∃ B : Set ℕ, IsPerfectDifferenceSet B (Nat.card F ^ 2 + Nat.card F + 1) ∧
      B.ncard = Nat.card F + 1 ∧
      ∀ a : ℕ, a % (Nat.card F ^ 2 + Nat.card F + 1) ∈ B ↔ γ ^ a ∈ W := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨q, hqdef⟩ : ∃ q, q = Nat.card F := ⟨_, rfl⟩
  rw [← hqdef]
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    exact Finite.one_lt_card
  obtain ⟨n, hn⟩ : ∃ n, n = q ^ 2 + q + 1 := ⟨_, rfl⟩
  rw [← hn]
  have hnpos : 0 < n := by omega
  have : NeZero n := ⟨hnpos.ne'⟩
  have hcardK : Nat.card K = q ^ 3 := by
    rw [hqdef, ← h3]
    exact Module.natCard_eq_pow_finrank
  have hN : Nat.card K - 1 = (q - 1) * n := by
    rw [hcardK, hn]
    exact cube_sub_one q (by omega)
  rw [hN] at hγord hγpow
  -- powers of `γ` in the base field
  have hA1 : ∀ (i : ℕ) (a : F), algebraMap F K a = γ ^ i → n ∣ i := by
    intro i a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact pow_ne_zero i hγ0 ha.symm
    have h1 : a ^ (q - 1) = 1 := by
      rw [hqdef, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one a ha0
    have h2 : γ ^ (i * (q - 1)) = 1 := by
      rw [pow_mul, ← ha, ← map_pow, h1, map_one]
    have h3' := hγord _ h2
    rw [mul_comm i] at h3'
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h3'
  have hA2 : ∀ i : ℕ, n ∣ i → ∃ a : F, algebraMap F K a = γ ^ i := by
    rintro i ⟨m, rfl⟩
    apply mem_range_of_pow_card_eq
    have h1 : (γ ^ (n * m)) ^ (q - 1) = 1 := by
      rw [← pow_mul, show n * m * (q - 1) = (q - 1) * n * m by ring, pow_mul, hγpow, one_pow]
    rw [← hqdef]
    calc (γ ^ (n * m)) ^ q = (γ ^ (n * m)) ^ (q - 1 + 1) := by
          rw [Nat.sub_add_cancel (by omega)]
      _ = γ ^ (n * m) := by rw [pow_succ, h1, one_mul]
  -- the exponent `M'` acts as `-1`
  obtain ⟨M', hM'⟩ : ∃ M', (q - 1) * n = M' + 1 :=
    ⟨(q - 1) * n - 1, by
      have : 0 < (q - 1) * n := Nat.mul_pos (by omega) hnpos
      omega⟩
  have hM'cast : (M' : ZMod n) = -1 := by
    have h : ((M' + 1 : ℕ) : ZMod n) = 0 := by
      rw [← hM', Nat.cast_mul, ZMod.natCast_self, mul_zero]
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hrel1 : ∀ i j : ℕ, γ ^ (j + M' * i) * γ ^ i = γ ^ j := by
    intro i j
    rw [← pow_add, show j + M' * i + i = j + (M' + 1) * i by ring, ← hM', pow_add, pow_mul,
      hγpow, one_pow, mul_one]
  have hrel2 : ∀ i j : ℕ, ((j + M' * i : ℕ) : ZMod n) = (j : ZMod n) - (i : ZMod n) := by
    intro i j
    push_cast
    rw [hM'cast]
    ring
  -- proportional powers have congruent exponents, and conversely
  have hP : ∀ (i j : ℕ) (a : F), γ ^ j = algebraMap F K a * γ ^ i →
      (j : ZMod n) = (i : ZMod n) := by
    intro i j a h
    have h1 : algebraMap F K a = γ ^ (j + M' * i) := by
      have h' := hrel1 i j
      rw [h] at h'
      exact (mul_right_cancel₀ (pow_ne_zero i hγ0) h').symm
    have h2 := hA1 _ a h1
    have h3' : ((j + M' * i : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
    rw [hrel2] at h3'
    exact sub_eq_zero.1 h3'
  have hQ : ∀ i j : ℕ, (j : ZMod n) = (i : ZMod n) →
      ∃ a : F, γ ^ j = algebraMap F K a * γ ^ i := by
    intro i j h
    have h1 : ((j + M' * i : ℕ) : ZMod n) = 0 := by rw [hrel2, h, sub_self]
    obtain ⟨a, ha⟩ := hA2 _ ((ZMod.natCast_eq_zero_iff _ _).1 h1)
    exact ⟨a, by rw [ha, hrel1]⟩
  have hWmod : ∀ i j : ℕ, (j : ZMod n) = (i : ZMod n) → γ ^ i ∈ W → γ ^ j ∈ W := by
    intro i j h hi
    obtain ⟨a, ha⟩ := hQ i j h
    rw [ha, ← Algebra.smul_def]
    exact W.smul_mem a hi
  have hcast : ∀ a b : ℕ, a < n → b < n → (a : ZMod n) = (b : ZMod n) → a = b := by
    intro a b ha hb h
    have h' := (ZMod.natCast_eq_natCast_iff' a b n).1 h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  -- the difference set
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, B = {i : ℕ | i < n ∧ γ ^ i ∈ W} := ⟨_, rfl⟩
  have hBmem : ∀ i : ℕ, i ∈ B ↔ i < n ∧ γ ^ i ∈ W := by
    intro i
    rw [hB]
    rfl
  have hpds : IsPerfectDifferenceSet B n := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb, hne⟩ := hab
      show (a : ZMod n) - (b : ZMod n) ≠ 0
      intro h
      exact hne (hcast a b ((hBmem a).1 ha).1 ((hBmem b).1 hb).1 (sub_eq_zero.1 h))
    · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
      obtain ⟨ha, hb, hne⟩ := hab
      obtain ⟨ha', hb', hne'⟩ := hab'
      have heq' : (a : ZMod n) - (b : ZMod n) = (a' : ZMod n) - (b' : ZMod n) := heq
      obtain ⟨han, haW⟩ := (hBmem a).1 ha
      obtain ⟨hbn, hbW⟩ := (hBmem b).1 hb
      obtain ⟨han', haW'⟩ := (hBmem a').1 ha'
      obtain ⟨hbn', hbW'⟩ := (hBmem b').1 hb'
      -- `c = γ ^ a / γ ^ b`, written as a power of `γ`
      have hc : γ ^ (a + M' * b) ∉ (algebraMap F K).range := by
        rintro ⟨t, ht⟩
        have h1 := hA1 _ t ht
        have h2 : ((a + M' * b : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
        rw [hrel2] at h2
        exact hne (hcast a b han hbn (sub_eq_zero.1 h2))
      have hcy : γ ^ (a + M' * b) * γ ^ b ∈ W := by
        rw [hrel1]
        exact haW
      have hcy' : γ ^ (a + M' * b) * γ ^ b' ∈ W := by
        rw [← pow_add]
        refine hWmod a' _ ?_ haW'
        push_cast
        rw [hM'cast]
        linear_combination heq'
      obtain ⟨s, hs⟩ := key_unique h3 W hW _ hc hbW (pow_ne_zero b hγ0) hcy hbW' hcy'
      rw [Algebra.smul_def] at hs
      have hbb : b' = b := hcast b' b hbn' hbn (hP b b' s hs)
      subst hbb
      have haa : (a : ZMod n) = (a' : ZMod n) := by linear_combination heq'
      have haa' : a = a' := hcast a a' han han' haa
      subst haa'
      rfl
    · intro x hx
      have hx0 : x ≠ 0 := hx
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ZMod n) = x := ⟨x.val, ZMod.natCast_zmod_val x⟩
      obtain ⟨y, hyW, hy0, hcy⟩ := key_exists h3 W hW (γ ^ d) (pow_ne_zero d hγ0)
      obtain ⟨j, rfl⟩ := hγsurj y hy0
      rw [← pow_add] at hcy
      refine ⟨((d + j) % n, j % n), ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod (d + j) _ (ZMod.natCast_mod _ _) hcy⟩
      · exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod j _ (ZMod.natCast_mod _ _) hyW⟩
      · intro h
        apply hx0
        have h' : ((d + j : ℕ) : ZMod n) = (j : ZMod n) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).2 h
        push_cast at h'
        rw [← hd]
        linear_combination h'
      · show (((d + j) % n : ℕ) : ZMod n) - ((j % n : ℕ) : ZMod n) = x
        rw [ZMod.natCast_mod, ZMod.natCast_mod, ← hd]
        push_cast
        ring
  -- counting the differences gives the size
  have hfin : B.Finite := (Set.finite_Iio n).subset (fun i hi => ((hBmem i).1 hi).1)
  have hcard : B.ncard = q + 1 := by
    have h1 : B.offDiag.ncard = n - 1 := by
      have h' := hpds.injOn.ncard_image
      rw [hpds.image_eq] at h'
      rw [← h']
      have h0 : {x : ZMod n | x ≠ 0} = ({0} : Set (ZMod n))ᶜ := by
        ext x
        simp
      rw [h0, Set.ncard_compl, Set.ncard_singleton, Nat.card_zmod]
    clear hB hBmem
    lift B to Finset ℕ using hfin
    rw [← Finset.coe_offDiag, Set.ncard_coe_finset, Finset.offDiag_card] at h1
    rw [Set.ncard_coe_finset]
    have hk : B.card * B.card = q ^ 2 + q + B.card := by
      have := Nat.le_mul_self B.card
      omega
    have hz : ((B.card : ℤ) - (q + 1)) * ((B.card : ℤ) + q) = 0 := by
      have hk' : (B.card : ℤ) * B.card = q ^ 2 + q + B.card := by exact_mod_cast hk
      linear_combination hk'
    rcases mul_eq_zero.1 hz with h | h
    · omega
    · omega
  refine ⟨B, hpds, hcard, ?_⟩
  intro a
  constructor
  · intro ha
    exact hWmod (a % n) a (ZMod.natCast_mod a n).symm ((hBmem _).1 ha).2
  · intro ha
    exact (hBmem _).2 ⟨Nat.mod_lt _ hnpos, hWmod a (a % n) (ZMod.natCast_mod a n) ha⟩

/-- The Singer construction for a field `F` with a cubic extension `K`. -/
theorem core {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3) :
    ∃ B : Set ℕ, IsPerfectDifferenceSet B (Nat.card F ^ 2 + Nat.card F + 1) ∧
      B.ncard = Nat.card F + 1 := by
  obtain ⟨γ, hγ0, hγsurj, hγord, hγpow⟩ := exists_gen K
  obtain ⟨W, hW⟩ := exists_plane (F := F) (K := K) h3
  obtain ⟨B, hB, hcard, _⟩ := core_with_plane h3 γ hγ0 hγsurj hγord hγpow W hW
  exact ⟨B, hB, hcard⟩

end OMA707Singer

namespace OMA707

/-- Shifting a perfect difference set by a map that acts as a translation on residues. -/
lemma pds_shift (D : Set ℕ) (n : ℕ) (f : ℕ → ℕ) (c : ZMod n)
    (hf : ∀ x ∈ D, ((f x : ℕ) : ZMod n) = (x : ZMod n) + c)
    (h : IsPerfectDifferenceSet D n) : IsPerfectDifferenceSet (f '' D) n := by
  have key : ∀ x ∈ D, ∀ y ∈ D,
      ((f x : ℕ) : ZMod n) - ((f y : ℕ) : ZMod n) = (x : ZMod n) - (y : ZMod n) := by
    intro x hx y hy; rw [hf x hx, hf y hy]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, v⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩
    have hab : (a, b) ∈ D.offDiag := ⟨ha, hb, fun e => hne (by simp only at e ⊢; rw [e])⟩
    have := h.mapsTo hab
    simp only [Set.mem_ofPred_eq] at this ⊢
    rw [key a ha b hb]; exact this
  · rintro ⟨u, v⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩ ⟨u', v'⟩ ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩, hne'⟩ heq
    have hab : (a, b) ∈ D.offDiag := ⟨ha, hb, fun e => hne (by simp only at e ⊢; rw [e])⟩
    have hab' : (a', b') ∈ D.offDiag := ⟨ha', hb', fun e => hne' (by simp only at e ⊢; rw [e])⟩
    simp only at heq
    rw [key a ha b hb, key a' ha' b' hb'] at heq
    have := h.injOn hab hab' heq
    simp only [Prod.mk.injEq] at this ⊢
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨rfl, rfl⟩
  · intro z hz
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hne⟩, hz'⟩ := h.surjOn hz
    refine ⟨(f a, f b), ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_⟩, ?_⟩
    · intro e
      have h1 := key a ha b hb
      simp only at e
      rw [e, sub_self] at h1
      have := h.mapsTo (show (a, b) ∈ D.offDiag from ⟨ha, hb, hne⟩)
      simp only [Set.mem_ofPred_eq] at this
      exact this h1.symm
    · simp only at hz' ⊢
      rw [key a ha b hb]; exact hz'

lemma pds7 : IsPerfectDifferenceSet ({1, 2, 4} : Set ℕ) 7 := by
  unfold IsPerfectDifferenceSet
  refine ⟨?mapsTo, ?injOn, ?surjOn⟩
  · intro ⟨a, b⟩ hab; simp only [Set.mem_offDiag, Set.mem_insert_iff, Set.mem_singleton_iff] at hab
    obtain ⟨ha, hb, hne⟩ := hab
    simp only [Set.mem_ofPred]
    rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    simp_all <;> decide
  · intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
    simp only [Set.mem_offDiag, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    obtain ⟨ha1, hb1, hne1⟩ := h1; obtain ⟨ha2, hb2, hne2⟩ := h2
    rcases ha1 with rfl | rfl | rfl <;>
    rcases hb1 with rfl | rfl | rfl <;>
    rcases ha2 with rfl | rfl | rfl <;>
    rcases hb2 with rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd rfl hne1
      | exact absurd rfl hne2
      | exact absurd heq (by decide)
  · intro x hx
    simp only [Set.mem_ofPred] at hx
    fin_cases x
    · exact absurd rfl hx
    · refine ⟨(2, 1), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(4, 2), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(4, 1), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(1, 4), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(2, 4), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩
    · refine ⟨(1, 2), by simp [Set.mem_offDiag, Set.mem_insert_iff], by rfl⟩

/-- Any set with at most one element embeds in a perfect difference set modulo 7. -/
lemma small_le_one (A : Set ℕ) (a : ℕ) (hA : A ⊆ {a}) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ A ⊆ B ∧ IsPerfectDifferenceSet B (p^2 + p + 1) := by
  refine ⟨(fun x => x - 1 + a) '' ({1, 2, 4} : Set ℕ), 2, Nat.prime_two.isPrimePow, ?_, ?_⟩
  · intro x hx
    rw [hA hx]
    exact ⟨1, by simp, by simp⟩
  · have : (2 : ℕ) ^ 2 + 2 + 1 = 7 := by norm_num
    rw [this]
    refine pds_shift _ 7 _ ((a : ZMod 7) - 1) ?_ pds7
    intro x hx
    have hx1 : 1 ≤ x := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> norm_num
    push_cast [Nat.cast_sub hx1]
    ring

/-- Choose representatives of a translate of a perfect difference set that contain A. -/
lemma lift_pds {A D : Set ℕ} {n : ℕ} [NeZero n] (c : ZMod n)
    (hD : IsPerfectDifferenceSet D n)
    (hA : Set.InjOn (fun a : ℕ => (a : ZMod n)) A)
    (hcover : ∀ a ∈ A, ∃ d ∈ D, (a : ZMod n) = (d : ZMod n) + c) :
    ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSet B n := by
  classical
  let f (d : ℕ) : ℕ :=
    if h : ∃ a ∈ A, (a : ZMod n) = (d : ZMod n) + c then h.choose
    else ((d : ZMod n) + c).val
  refine ⟨f '' D, ?_, pds_shift D n f c ?_ hD⟩
  · intro a ha
    obtain ⟨d, hd, had⟩ := hcover a ha
    have h : ∃ x ∈ A, (x : ZMod n) = (d : ZMod n) + c := ⟨a, ha, had⟩
    refine ⟨d, hd, ?_⟩
    dsimp only [f]
    rw [dif_pos h]
    exact hA h.choose_spec.1 ha (h.choose_spec.2.trans had.symm)
  · intro d _
    dsimp only [f]
    split
    · rename_i h
      exact h.choose_spec.2
    · exact ZMod.natCast_zmod_val _

/-- Embed a set whose exponents in a Singer construction give points on a single line. -/
lemma embed_singer {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    (γ : K) (hγ0 : γ ≠ 0) (hγsurj : ∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x)
    (hγord : ∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m)
    (hγpow : γ ^ (Nat.card K - 1) = 1)
    (W : Submodule F K) (hW : Module.finrank F W = 2)
    (A : Set ℕ) (hn : Set.InjOn (fun a : ℕ => (a : ZMod (Nat.card F ^ 2 + Nat.card F + 1))) A)
    (hA : ∀ a ∈ A, γ ^ a ∈ W) :
    ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSet B (Nat.card F ^ 2 + Nat.card F + 1) := by
  obtain ⟨D, hD, _, hmem⟩ := OMA707Singer.core_with_plane h3 γ hγ0 hγsurj hγord hγpow W hW
  have : NeZero (Nat.card F ^ 2 + Nat.card F + 1) := ⟨by omega⟩
  apply lift_pds 0 hD hn
  intro a ha
  exact ⟨a % (Nat.card F ^ 2 + Nat.card F + 1), (hmem a).2 (hA a ha), by
    rw [ZMod.natCast_mod, add_zero]⟩

lemma embed_pair {D : Set ℕ} {n : ℕ} [NeZero n] (hD : IsPerfectDifferenceSet D n)
    {a b : ℕ} (hab : (a : ZMod n) ≠ (b : ZMod n)) :
    ∃ B : Set ℕ, {a, b} ⊆ B ∧ IsPerfectDifferenceSet B n := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy, _⟩, hxy⟩ := hD.surjOn
    (show (a : ZMod n) - (b : ZMod n) ∈ {z : ZMod n | z ≠ 0} from sub_ne_zero.mpr hab)
  change (x : ZMod n) - (y : ZMod n) = (a : ZMod n) - (b : ZMod n) at hxy
  apply lift_pds ((b : ZMod n) - (y : ZMod n)) hD
  · intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact (hab huv).elim
    · exact (hab huv.symm).elim
    · rfl
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact ⟨x, hx, by linear_combination -hxy⟩
    · exact ⟨y, hy, by ring⟩

lemma singer_prime_power (p : ℕ) (hp : IsPrimePow p) :
    ∃ D : Set ℕ, IsPerfectDifferenceSet D (p ^ 2 + p + 1) := by
  obtain ⟨r, k, hr, hk, rfl⟩ := hp
  have : Fact r.Prime := ⟨Nat.prime_iff.2 hr⟩
  obtain ⟨D, hD, _⟩ := OMA707Singer.core (F := GaloisField r k)
    (K := FiniteField.Extension (GaloisField r k) r 3)
    (FiniteField.finrank_extension (GaloisField r k) r 3)
  rw [GaloisField.card r k hk.ne'] at hD
  exact ⟨D, hD⟩

lemma small_pair (a b : ℕ) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ {a, b} ⊆ B ∧
      IsPerfectDifferenceSet B (p ^ 2 + p + 1) := by
  by_cases hab : a = b
  · subst b
    exact small_le_one {a, a} a (by simp)
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max a b + 1)
  obtain ⟨D, hD⟩ := singer_prime_power p hprime.isPrimePow
  let n := p ^ 2 + p + 1
  have ha : a < n := by
    have := le_max_left a b
    dsimp [n]
    omega
  have hb : b < n := by
    have := le_max_right a b
    dsimp [n]
    omega
  have : NeZero n := ⟨(Nat.zero_lt_of_lt ha).ne'⟩
  have hab' : (a : ZMod n) ≠ (b : ZMod n) := by
    intro he
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at he
    exact hab he
  obtain ⟨B, hAB, hB⟩ := embed_pair hD hab'
  exact ⟨B, p, hprime.isPrimePow, hAB, hB⟩

/-- Write a three-element set in increasing order. -/
lemma ordered_triple {A : Set ℕ} (hA : A.ncard = 3) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ A = {a, b, c} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.mp hA
  rcases lt_or_gt_of_ne hab with hab | hba <;>
    rcases lt_or_gt_of_ne hac with hac | hca <;>
    rcases lt_or_gt_of_ne hbc with hbc | hcb
  · exact ⟨a, b, c, hab, hbc, rfl⟩
  · exact ⟨a, c, b, hac, hcb, by ext; simp [or_comm]⟩
  · omega
  · exact ⟨c, a, b, hca, hab, by ext; simp [or_comm, or_left_comm]⟩
  · exact ⟨b, a, c, hba, hac, by ext; simp [or_left_comm]⟩
  · omega
  · exact ⟨b, c, a, hbc, hca, by ext; simp [or_comm, or_left_comm]⟩
  · exact ⟨c, b, a, hcb, hba, by ext; simp [or_comm, or_left_comm]⟩

lemma translate_triple {a b c : ℕ} (hab : a ≤ b) (hac : a ≤ c)
    (hD : ∃ (D : Set ℕ) (p : ℕ), IsPrimePow p ∧ {0, b - a, c - a} ⊆ D ∧
      IsPerfectDifferenceSet D (p ^ 2 + p + 1)) :
    ∃ (B : Set ℕ) (p : ℕ), IsPrimePow p ∧ {a, b, c} ⊆ B ∧
      IsPerfectDifferenceSet B (p ^ 2 + p + 1) := by
  obtain ⟨D, p, hp, hD, hpds⟩ := hD
  refine ⟨(fun x : ℕ => x + a) '' D, p, hp, ?_, pds_shift D _ _ (a : ZMod _) ?_ hpds⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, hD (by simp), Nat.zero_add _⟩
    · exact ⟨x - a, hD (by simp), Nat.sub_add_cancel hab⟩
    · exact ⟨x - a, hD (by simp), Nat.sub_add_cancel hac⟩
  · intro x _
    exact Nat.cast_add x a

/-- For a normalized triple, a plane containing its powers suffices once the modulus exceeds b. -/
lemma normalized_of_singer {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    (γ : K) (hγ0 : γ ≠ 0) (hγsurj : ∀ x : K, x ≠ 0 → ∃ i : ℕ, γ ^ i = x)
    (hγord : ∀ m : ℕ, γ ^ m = 1 → (Nat.card K - 1) ∣ m)
    (hγpow : γ ^ (Nat.card K - 1) = 1)
    (W : Submodule F K) (hW : Module.finrank F W = 2)
    {a b : ℕ} (hab : a < b) (hb : b < Nat.card F ^ 2 + Nat.card F + 1)
    (h0 : 1 ∈ W) (haW : γ ^ a ∈ W) (hbW : γ ^ b ∈ W) :
    ∃ D : Set ℕ, IsPerfectDifferenceSet D (Nat.card F ^ 2 + Nat.card F + 1) ∧
      D.ncard = Nat.card F + 1 ∧ 0 ∈ D ∧ a ∈ D ∧ b ∈ D := by
  let n := Nat.card F ^ 2 + Nat.card F + 1
  obtain ⟨D,hD,hcard,hmem⟩ := OMA707Singer.core_with_plane h3 γ hγ0 hγsurj hγord hγpow W hW
  refine ⟨D,hD,hcard,?_,?_,?_⟩
  · simpa using (hmem 0).mpr (by simpa using h0)
  · simpa only [Nat.mod_eq_of_lt (hab.trans hb)] using (hmem a).mpr haW
  · simpa only [Nat.mod_eq_of_lt hb] using (hmem b).mpr hbW

/-- A primitive root of a trinomial with the prescribed exponents gives an embedding. -/
lemma normalized_of_primitive_relation {F K : Type*}
    [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b < Nat.card F ^ 2 + Nat.card F + 1)
    {γ : K} (hγ : IsPrimitiveRoot γ (Nat.card K - 1)) (s t : F)
    (hrel : γ ^ b = algebraMap F K s + algebraMap F K t * γ ^ a) :
    ∃ D : Set ℕ, IsPerfectDifferenceSet D (Nat.card F ^ 2 + Nat.card F + 1) ∧
      D.ncard = Nat.card F + 1 ∧ 0 ∈ D ∧ a ∈ D ∧ b ∈ D := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K := Fintype.ofFinite K
  have hF : 1 < Nat.card F := Finite.one_lt_card
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have : NeZero (Nat.card K - 1) := ⟨by omega⟩
  have hγ0 : γ ≠ 0 := hγ.ne_zero NeZero.out
  have hγsurj (x : K) (hx : x ≠ 0) : ∃ i : ℕ, γ ^ i = x := by
    have hxpow : x ^ (Nat.card K - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    obtain ⟨i, _, hi⟩ := hγ.eq_pow_of_pow_eq_one hxpow
    exact ⟨i, hi⟩
  have hcardK : Nat.card K - 1 = (Nat.card F - 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h3]
    exact OMA707Singer.cube_sub_one _ hF.le
  have hli : LinearIndependent F ![(1 : K), γ ^ a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro c hc
    rw [Algebra.smul_def, mul_one] at hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact pow_ne_zero a hγ0 hc.symm
    have hpow : γ ^ (a * (Nat.card F - 1)) = 1 := by
      rw [pow_mul, ← hc, ← map_pow, Nat.card_eq_fintype_card,
        FiniteField.pow_card_sub_one_eq_one c hc0, map_one]
    have hd := hγ.dvd_of_pow_eq_one _ hpow
    rw [hcardK, mul_comm a] at hd
    have hd' := Nat.dvd_of_mul_dvd_mul_left (show 0 < Nat.card F - 1 by omega) hd
    exact (not_le_of_gt (lt_trans hab hb)) (Nat.le_of_dvd ha hd')
  let W := Submodule.span F ({(1 : K), γ ^ a} : Set K)
  have hW : Module.finrank F W = 2 := by
    have hspan : Submodule.span F (Set.range ![(1 : K), γ ^ a]) = W :=
      congrArg (Submodule.span F) (Matrix.range_cons_cons_empty _ _ _)
    exact (congrArg (fun V : Submodule F K => Module.finrank F V) hspan).symm.trans
      (by simpa only [Fintype.card_fin] using finrank_span_eq_card hli)
  have h1 : (1 : K) ∈ W := Submodule.subset_span (by simp)
  have haW : γ ^ a ∈ W := Submodule.subset_span (by simp)
  have hbW : γ ^ b ∈ W := by
    rw [hrel, ← Algebra.smul_def, ← mul_one (algebraMap F K s), ← Algebra.smul_def]
    exact W.add_mem (W.smul_mem s h1) (W.smul_mem t haW)
  exact normalized_of_singer h3 γ hγ0 hγsurj hγ.dvd_of_pow_eq_one hγ.pow_eq_one
    W hW hab hb h1 haW hbW

/-- An element generating the group modulo base-field scalars has a primitive representative. -/
lemma rescale_projective_generator {F K : Type*}
    [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3) {α : K}
    (hα : IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1)) :
    ∃ (β : K) (c : F), IsPrimitiveRoot β (Nat.card K - 1) ∧
      β = algebraMap F K c * α := by
  let q := Nat.card F
  let n := q ^ 2 + q + 1
  let N := Nat.card K - 1
  change IsPrimitiveRoot (α ^ (q - 1)) n at hα
  have hq : 1 < q := Finite.one_lt_card
  have hn : 0 < n := by dsimp [n]; omega
  have hq1 : 0 < q - 1 := by omega
  have hN : N = (q - 1) * n := by
    dsimp [N, n, q]
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h3]
    exact OMA707Singer.cube_sub_one _ hq.le
  have : NeZero N := ⟨by rw [hN]; exact (Nat.mul_pos hq1 hn).ne'⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα.ne_zero hn.ne' (zero_pow hq1.ne')
  obtain ⟨g, _, hgSurj, hgDvd, hgPow⟩ := OMA707Singer.exists_gen K
  have hg : IsPrimitiveRoot g N := ⟨hgPow, hgDvd⟩
  have hg' : IsPrimitiveRoot (g ^ (q - 1)) n := by
    constructor
    · rw [← pow_mul, ← hN]
      exact hg.pow_eq_one
    · intro i hi
      rw [← pow_mul] at hi
      have hd := hg.dvd_of_pow_eq_one _ hi
      rw [hN] at hd
      exact Nat.dvd_of_mul_dvd_mul_left hq1 hd
  obtain ⟨j, hj⟩ := hgSurj α hα0
  have hα' : (g ^ (q - 1)) ^ j = α ^ (q - 1) := by
    rw [← pow_mul, mul_comm, pow_mul, hj]
  have hj' : j.Coprime n := (hg'.pow_iff_coprime hn j).mp (by rw [hα']; exact hα)
  have hd : n ∣ N := by rw [hN]; exact dvd_mul_left _ _
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime j hj')
  let k := (u : ZMod N).val
  have hk : k.Coprime N := ZMod.val_coe_unit_coprime u
  have hcast : (k : ZMod n) = (j : ZMod n) := by
    have hu' := congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) hu
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (u : ZMod N),
      ZMod.cast_natCast hd] at hu'
    exact hu'
  have hmod : k ≡ j [MOD n] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  let β := g ^ k
  have hβ : IsPrimitiveRoot β N := hg.pow_of_coprime k hk
  have hpow : β ^ (q - 1) = α ^ (q - 1) := by
    calc
      β ^ (q - 1) = (g ^ (q - 1)) ^ k := by dsimp [β]; rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (g ^ (q - 1)) ^ j := pow_eq_pow_of_modEq hmod hg'.pow_eq_one
      _ = α ^ (q - 1) := hα'
  have hratio : (β / α) ^ (q - 1) = 1 := by
    rw [div_pow, hpow, div_self (pow_ne_zero _ hα0)]
  obtain ⟨c, hc⟩ := OMA707Singer.mem_range_of_pow_card_eq (F := F) (β / α) (by
    change (β / α) ^ q = β / α
    calc
      (β / α) ^ q = (β / α) ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = β / α := by rw [pow_succ, hratio, one_mul])
  exact ⟨β, c, hβ, ((eq_div_iff hα0).mp hc).symm⟩

lemma normalized_of_projective_relation {F K : Type*}
    [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
    (h3 : Module.finrank F K = 3)
    {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b < Nat.card F ^ 2 + Nat.card F + 1)
    {α : K} (hα : IsPrimitiveRoot (α ^ (Nat.card F - 1)) (Nat.card F ^ 2 + Nat.card F + 1))
    (s t : F) (hrel : α ^ b = algebraMap F K s + algebraMap F K t * α ^ a) :
    ∃ D : Set ℕ, IsPerfectDifferenceSet D (Nat.card F ^ 2 + Nat.card F + 1) ∧
      D.ncard = Nat.card F + 1 ∧ 0 ∈ D ∧ a ∈ D ∧ b ∈ D := by
  obtain ⟨β, c, hβ, hc⟩ := rescale_projective_generator h3 hα
  apply normalized_of_primitive_relation h3 ha hab hb hβ (c ^ b * s) (c ^ (b - a) * t)
  rw [hc, mul_pow, mul_pow, map_mul, map_mul, map_pow, map_pow, hrel]
  have hcb : (algebraMap F K c) ^ b =
      (algebraMap F K c) ^ (b - a) * (algebraMap F K c) ^ a := by
    rw [← pow_add, Nat.sub_add_cancel hab.le]
  rw [mul_add, hcb]
  ring

end OMA707

end OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R1

namespace OMA.SidonThree
open OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R1.OMA707

/-- Rotate a cyclic difference set, taking its representatives in the positive interval. -/
private theorem positive_lift {D : Set ℕ} {n a u v q : ℕ}
    (hn : 0 < n) (ha : 0 < a) (huv : u < v) (hfit : a + v ≤ n)
    (hpds : IsPerfectDifferenceSet D n) (hc : D.ncard = q + 1)
    (h0 : 0 ∈ D) (hu : u ∈ D) (hv : v ∈ D) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ a ∈ S ∧ a + u ∈ S ∧ a + v ∈ S ∧
      IsSidon (S : Set ℕ) ∧ S.card = q + 1 := by
  classical
  let f (x : ℕ) := (x + (a - 1)) % n + 1
  have hcast (x : ℕ) : (f x : ZMod n) = (x : ZMod n) + ((a - 1 : ℕ) : ZMod n) + 1 := by
    simp [f, ZMod.natCast_mod]
  have hfin := Set.finite_of_ncard_pos (show 0 < D.ncard by omega)
  let S := hfin.toFinset.image f
  have hinj : Set.InjOn f D := by
    intro x hx y hy heq
    by_contra hne
    have hd : (x : ZMod n) - (y : ZMod n) ≠ 0 :=
      hpds.mapsTo (show (x,y) ∈ D.offDiag from ⟨hx,hy,hne⟩)
    have h := congrArg (fun k : ℕ => (k : ZMod n)) heq
    change (f x : ZMod n) = (f y : ZMod n) at h
    rw [hcast, hcast] at h
    exact hd (by linear_combination h)
  have hit (x : ℕ) (hx : x ∈ D) (hxv : x ≤ v) : a + x ∈ S := by
    refine Finset.mem_image.mpr ⟨x, hfin.mem_toFinset.mpr hx, ?_⟩
    dsimp only [f]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨S, ?_, by simpa using hit 0 h0 (Nat.zero_le _), hit u hu huv.le,
    hit v hv le_rfl, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    have := Nat.mod_lt (y + (a - 1)) hn
    simp only [Finset.mem_Icc, f]
    omega
  · have hp := pds_shift D n f (((a - 1 : ℕ) : ZMod n) + 1)
        (fun x _ => (hcast x).trans (add_assoc _ _ _)) hpds
    have him : (S : Set ℕ) = f '' D := by simp [S]
    rw [him]
    intro x hx y hy z hz w hw hsum
    by_cases hxy : x = y
    · exact Or.inl ⟨hxy, by omega⟩
    have hwz : w ≠ z := by omega
    have hs : (x : ZMod n) + z = y + w := by
      simpa only [Nat.cast_add] using congrArg (fun k : ℕ => (k : ZMod n)) hsum
    have he := hp.injOn (show (x,y) ∈ (f '' D).offDiag from ⟨hx,hy,hxy⟩)
      (show (w,z) ∈ (f '' D).offDiag from ⟨hw,hz,hwz⟩)
      (show (x : ZMod n) - y = w - z by linear_combination hs)
    exact Or.inr ⟨congrArg Prod.fst he, (congrArg Prod.snd he).symm⟩
  · calc
      S.card = hfin.toFinset.card := Finset.card_image_of_injOn (by simpa using hinj)
      _ = D.ncard := (D.ncard_eq_toFinset_card hfin).symm
      _ = q + 1 := hc

/-- Dilating both gaps forces a large Singer modulus. Its odd order allows the
dilation to be absorbed into the projective generator. -/
private theorem unbounded_plane (u v B : ℕ) (hu : 0 < u) (huv : u < v) (hne : v ≠ 2*u) :
    ∃ (q : ℕ) (D : Set ℕ), B < q^2+q+1 ∧ IsPerfectDifferenceSet D (q^2+q+1) ∧
      D.ncard = q+1 ∧ 0 ∈ D ∧ u ∈ D ∧ v ∈ D := by
  let d := 2^(B+1)
  have hd : 0 < d := by positivity
  have hBd : B < d := by
    exact (Nat.lt_succ_self B).trans (Nat.lt_pow_self (by decide : 1 < 2))
  have hw : ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K)
      (_ : Algebra F K), Module.finrank F K = 3 ∧ d*v < Nat.card F^2 + Nat.card F + 1 ∧
        ∃ (α : K) (s t : F), IsPrimitiveRoot (α^(Nat.card F-1)) (Nat.card F^2+Nat.card F+1) ∧
          α^(d*v) = algebraMap F K s + algebraMap F K t * α^(d*u) := by
    have hdu := Nat.mul_pos hd hu
    have hduv := Nat.mul_lt_mul_of_pos_left huv hd
    by_cases hlt : v < 2*u
    · exact E707Geometry.primitiveInputs.1 (d*u) (d*v) hdu hduv
        (by simpa only [mul_left_comm] using Nat.mul_lt_mul_of_pos_left hlt hd)
    · have hgt : 2*u < v := by omega
      exact E707Geometry.primitiveInputs.2 (d*u) (d*v) hdu
        (by simpa only [mul_left_comm] using Nat.mul_lt_mul_of_pos_left hgt hd)
  obtain ⟨F,K,iF,iK,fF,fK,alg,h3,hdv,α,s,t,hα,hrel⟩ := hw
  let q := Nat.card F
  have hn : d*v < q^2+q+1 := hdv
  have h1 : v ≤ d*v := Nat.le_mul_of_pos_left _ hd
  have h2 : d ≤ d*v := Nat.le_mul_of_pos_right _ (by omega)
  have hodd : Odd (q^2+q+1) := by
    rcases Nat.even_or_odd q with ⟨k,hk⟩ | ⟨k,hk⟩
    · refine ⟨k * (q+1), ?_⟩
      rw [hk]
      ring
    · refine ⟨(k+1) * q, ?_⟩
      rw [hk]
      ring
  have hcop : d.Coprime (q^2+q+1) := hodd.coprime_two_left.pow_left _
  have hprim : IsPrimitiveRoot ((α^d)^(q-1)) (q^2+q+1) := by
    rw [← pow_mul, mul_comm d, pow_mul]
    exact hα.pow_of_coprime d hcop
  refine ⟨q, ?_⟩
  obtain ⟨D, hD⟩ := normalized_of_projective_relation h3 hu huv
    (show v < q^2+q+1 by omega) hprim s t (by simpa only [← pow_mul] using hrel)
  exact ⟨D, by omega, hD⟩

theorem embed : OMA.R_Erdos44_erdos_44_R1.H1 := by
  classical
  intro A hzero hsid hc δ hδ L
  obtain ⟨a,b,c,hab,hbc,hset⟩ := ordered_triple (A := (A : Set ℕ)) (by simpa using hc)
  have haA : a ∈ (A : Set ℕ) := by rw [hset]; simp
  have hbA : b ∈ (A : Set ℕ) := by rw [hset]; simp
  have hcA : c ∈ (A : Set ℕ) := by rw [hset]; simp
  have ha : 0 < a := Nat.pos_of_ne_zero (fun e => hzero (e ▸ haA))
  let u := b-a
  let v := c-a
  have hu : 0<u := by dsimp [u]; omega
  have huv : u<v := by dsimp [u,v]; omega
  have hab' : a+u=b := by dsimp [u]; omega
  have hac' : a+v=c := by dsimp [v]; omega
  have hne : v ≠ 2*u := by
    intro e
    rcases hsid b hbA a haA b hbA c hcA (by omega) with h | h <;> omega
  obtain ⟨q,D,hn,hpds,hcard,h0,huD,hvD⟩ := unbounded_plane u v (L+c) hu huv hne
  obtain ⟨S,hS,haS,hbS,hcS,hs,hsc⟩ := positive_lift (a := a) (q := q)
    (by omega) ha huv (by omega) hpds hcard h0 huD hvD
  rw [hab'] at hbS
  rw [hac'] at hcS
  refine ⟨q^2+q+1, by omega, S, hS, ?_, hs, ?_⟩
  · intro x hx
    have hm : x ∈ ({a,b,c} : Set ℕ) := hset ▸ (show x ∈ (A : Set ℕ) from hx)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl <;> assumption
  · rw [hsc]
    apply (mul_le_of_le_one_left (Real.sqrt_nonneg _) (show 1-δ ≤ 1 by linarith)).trans
    apply Real.sqrt_le_iff.mpr
    push_cast
    constructor <;> nlinarith [show (0:ℝ) ≤ q by positivity]

end OMA.SidonThree

theorem OMA.solution : OMA.R_Erdos44_erdos_44_R1.H1 := OMA.SidonThree.embed
