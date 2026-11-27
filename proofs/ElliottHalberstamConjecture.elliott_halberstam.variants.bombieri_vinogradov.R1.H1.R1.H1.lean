import OMAReductions.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1
import Mathlib

/- Adapted from Bombieri–Vinogradov in Lean, by Jonas Whidden (@kimihiro64),
commit 7a1748306e026825ed6a5555516cc2f28989b2ac, used under Apache-2.0.
The character lifting bound and the maximal endpoint estimate come from the
CharacterReduction and CenteredPsiMax modules. -/
section
noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve


def primitiveCharacters (q : Nat) : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter DirichletCharacter.IsPrimitive


def intervalCharacterSum (a : Int -> Complex) (M : Int) (N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)), a n * chi (n : ZMod q)


def unitCharacterSum {q : Nat} (a : (ZMod q)ˣ -> Complex)
    (chi : DirichletCharacter Complex q) : Complex := by
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  exact ∑ x, a x * chi (x : ZMod q)


def CharacterLargeSieveStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧
      ∀ (M : Int) (N Q : Nat) (a : Int -> Complex), 1 <= Q ->
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
            ∑ chi ∈ primitiveCharacters q,
              ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
          C * ((N : Real) + (Q : Real) ^ 2) *
            ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2

end BombieriVinogradov.LargeSieve
end

section
noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve


def psiCharacterSum (y q : Nat) (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Icc 1 y,
    (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)


def maximalPsiNorm (x : Real) {q : Nat}
    (chi : DirichletCharacter Complex q) : Real :=
  (range (⌊x⌋₊ + 1)).sup' (by simp) fun y => ‖psiCharacterSum y q chi‖


def primitivePsiMean (x : Real) (Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalPsiNorm x chi


def basicMeanValueMajorant (x : Real) (Q : Nat) : Real :=
  (x + x ^ (5 / 6 : Real) * (Q : Real) +
      x ^ (1 / 2 : Real) * (Q : Real) ^ 2) *
    Real.log (x * (Q : Real)) ^ 3


def VaughanMeanValueStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧ ∀ (x : Real) (Q : Nat), 2 <= x -> 1 <= Q ->
      primitivePsiMean x Q <= C * basicMeanValueMajorant x Q


def restrictedBilinearCharacterSum (a b : Nat -> Complex)
    (M N Y q : Nat) (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
    if m * n <= Y then a m * b n * chi ((m * n : Nat) : ZMod q) else 0


def maximalBilinearNorm (a b : Nat -> Complex)
    (M N X : Nat) {q : Nat} (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖restrictedBilinearCharacterSum a b M N Y q chi‖


def coefficientMass (a : Nat -> Complex) (M : Nat) : Real :=
  ∑ m ∈ Icc 1 M, ‖a m‖ ^ 2


def MaximalBilinearLargeSieveStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧
      ∀ (X M N Q : Nat) (a b : Nat -> Complex),
        2 <= X -> 1 <= M -> 1 <= N -> 1 <= Q ->
          ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
              ∑ chi ∈ primitiveCharacters q,
                maximalBilinearNorm a b M N X chi <=
            C * Real.log ((X * M * N : Nat) : Real) *
              Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
                ((N : Real) + (Q : Real) ^ 2) *
                coefficientMass a M * coefficientMass b N)


def positiveIntervalCoefficients (a : Nat -> Complex) (n : Int) : Complex :=
  a n.toNat


def positiveCharacterSum (a : Nat -> Complex) (M q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  intervalCharacterSum (positiveIntervalCoefficients a) 0 M q chi


def positiveCoefficientMass (a : Nat -> Complex) (M : Nat) : Real :=
  ∑ n ∈ Ioc (0 : Int) (M : Int), ‖positiveIntervalCoefficients a n‖ ^ 2


def bilinearCharacterProduct (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  positiveCharacterSum a M q chi * positiveCharacterSum b N q chi

end BombieriVinogradov.VaughanMeanValue
end

section
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov


noncomputable def nonprincipalPrimitiveMaximalSum (X : Real) (q : Nat) : Real :=
  Finset.sum ((LargeSieve.primitiveCharacters q).erase 1)
    (fun chi => VaughanMeanValue.maximalPsiNorm X chi)


noncomputable def primitiveConductorMean (X : Real) (Q : Nat) : Real :=
  Finset.sum (Finset.Icc 1 Q)
    (fun d => nonprincipalPrimitiveMaximalSum X d / (d.totient : Real))

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


noncomputable def psiGlobal (x : Nat) : Real :=
  Finset.sum (Finset.Icc 1 x) ArithmeticFunction.vonMangoldt


noncomputable def psiProgression (x N : Nat) (a : ZMod N) : Real :=
  Finset.sum (Finset.Icc 1 x)
    (fun n => if a = (n : ZMod N) then ArithmeticFunction.vonMangoldt n else 0)

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


noncomputable def maximalWeightedDiscrepancy (X : Real) (q : Nat) : Real :=
  iSup (fun a : Units (ZMod q) => iSup (fun y : Fin (Nat.floor X + 1) =>
    abs (psiProgression y.val q (a : ZMod q) - psiGlobal y.val / (q.totient : Real))))


noncomputable def averageWeightedDiscrepancy (X : Real) (Q : Nat) : Real :=
  Finset.sum (Finset.Icc 1 Q) (maximalWeightedDiscrepancy X)

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.VaughanMeanValue

theorem norm_psiCharacterSum_le_maximalPsiNorm {X : Real} {y q : Nat}
    (chi : _root_.DirichletCharacter Complex q) (hy : y <= Nat.floor X) :
    norm (psiCharacterSum y q chi) <= maximalPsiNorm X chi := by
  unfold maximalPsiNorm
  exact Finset.le_sup' (fun n => norm (psiCharacterSum n q chi))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hy))

theorem maximalPsiNorm_nonneg (X : Real) {q : Nat}
    (chi : _root_.DirichletCharacter Complex q) : 0 <= maximalPsiNorm X chi :=
  (norm_nonneg (psiCharacterSum 0 q chi)).trans
    (norm_psiCharacterSum_le_maximalPsiNorm chi (Nat.zero_le _))

end BombieriVinogradov.VaughanMeanValue
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


theorem nonprincipalPrimitiveMaximalSum_nonneg (X : Real) (q : Nat) :
    0 <= nonprincipalPrimitiveMaximalSum X q := by
  unfold nonprincipalPrimitiveMaximalSum
  exact Finset.sum_nonneg (fun chi _ => VaughanMeanValue.maximalPsiNorm_nonneg X chi)


theorem primitiveConductorMean_nonneg (X : Real) (Q : Nat) :
    0 <= primitiveConductorMean X Q := by
  unfold primitiveConductorMean
  exact Finset.sum_nonneg (fun d _ =>
    div_nonneg (nonprincipalPrimitiveMaximalSum_nonneg X d) (Nat.cast_nonneg d.totient))

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov

theorem divisorSigma_pair_inj (Q : Nat) :
    Set.InjOn (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2))
      (Finset.sigma (Finset.Icc 1 Q) Nat.divisors : Set (Sigma (fun _ : Nat => Nat))) := by
  intro p hp q hq h
  have hDivisor : p.2 = q.2 := congrArg Prod.fst h
  have hQuotient : p.1 / p.2 = q.1 / q.2 := congrArg Prod.snd h
  have hpDvd := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).2
  have hqDvd := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hq).2
  have hLevel : p.1 = q.1 := by
    calc
      p.1 = p.2 * (p.1 / p.2) := (Nat.mul_div_cancel' hpDvd).symm
      _ = q.2 * (q.1 / q.2) := by rw [hQuotient, hDivisor]
      _ = q.1 := Nat.mul_div_cancel' hqDvd
  exact Sigma.ext hLevel (heq_of_eq hDivisor)

theorem divisorSigma_pair_mem_product {Q : Nat} (p : Sigma (fun _ : Nat => Nat))
    (hp : (Finset.sigma (Finset.Icc 1 Q) Nat.divisors :
      Set (Sigma (fun _ : Nat => Nat))) p) :
    ((Finset.Icc 1 Q).product (Finset.Icc 1 Q) : Set (Prod Nat Nat))
      (Prod.mk p.2 (p.1 / p.2)) := by
  have hData := Finset.mem_sigma.mp hp
  have hRange := Finset.mem_Icc.mp hData.1
  have hLevelPos := Nat.lt_of_lt_of_le Nat.zero_lt_one hRange.1
  have hDvd := Nat.dvd_of_mem_divisors hData.2
  have hDivisorPos := Nat.pos_of_mem_divisors hData.2
  have hDivisorLe := Nat.le_of_dvd hLevelPos hDvd
  exact Finset.mem_product.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro (Nat.succ_le_iff.mpr hDivisorPos)
      (hDivisorLe.trans hRange.2)))
    (Finset.mem_Icc.mpr (And.intro
      (Nat.succ_le_iff.mpr (Nat.div_pos hDivisorLe hDivisorPos))
      ((Nat.div_le_self p.1 p.2).trans hRange.2))))

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem sum_divisors_le_sum_product (Q : Nat) (h g : Nat -> Nat -> Real)
    (hBound : forall n d : Nat, (Finset.Icc 1 Q : Set Nat) n ->
      (n.divisors : Set Nat) d -> h n d <= g d (n / d))
    (hNonneg : forall a b : Nat, (Finset.Icc 1 Q : Set Nat) a ->
      (Finset.Icc 1 Q : Set Nat) b -> 0 <= g a b) :
    Finset.sum (Finset.Icc 1 Q) (fun n => Finset.sum n.divisors (h n)) <=
      Finset.sum (Finset.Icc 1 Q) (fun a => Finset.sum (Finset.Icc 1 Q) (g a)) := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n => Finset.sum n.divisors (h n)) =
        Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
          (fun p : Sigma (fun _ : Nat => Nat) => h p.1 p.2) :=
      (Finset.sum_sigma (Finset.Icc 1 Q) Nat.divisors
        (fun p : Sigma (fun _ : Nat => Nat) => h p.1 p.2)).symm
    _ <= Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
        (fun p : Sigma (fun _ : Nat => Nat) => g p.2 (p.1 / p.2)) :=
      Finset.sum_le_sum (fun p hp =>
        hBound p.1 p.2 (Finset.mem_sigma.mp hp).1 (Finset.mem_sigma.mp hp).2)
    _ = Finset.sum ((Finset.sigma (Finset.Icc 1 Q) Nat.divisors).image
        (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2)))
        (fun z => g z.1 z.2) :=
      (Finset.sum_image (f := fun z : Prod Nat Nat => g z.1 z.2) (divisorSigma_pair_inj Q)).symm
    _ <= Finset.sum ((Finset.Icc 1 Q).product (Finset.Icc 1 Q))
        (fun z => g z.1 z.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr (fun p hp => divisorSigma_pair_mem_product p hp))
        (fun z hz _ => hNonneg z.1 z.2 (Finset.mem_product.mp hz).1
          (Finset.mem_product.mp hz).2)
    _ = Finset.sum (Finset.Icc 1 Q) (fun a => Finset.sum (Finset.Icc 1 Q) (g a)) :=
      Finset.sum_product (Finset.Icc 1 Q) (Finset.Icc 1 Q) (fun z : Prod Nat Nat => g z.1 z.2)

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem one_div_nat_eq_divisor_reciprocal_product {n d : Nat} (hd : Dvd.dvd d n) :
    1 / (n : Real) = 1 / (d : Real) * (1 / ((n / d : Nat) : Real)) := by
  rw [one_div_mul_one_div, <- Nat.cast_mul, Nat.mul_div_cancel' hd]

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem sum_divisor_card_div_le_sum_one_div_sq (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) <=
      (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 := by
  have hExpand :
      Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) =
        Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
          (fun p : Sigma (fun _ : Nat => Nat) => 1 / (p.1 : Real)) := by
    rw [Finset.sum_sigma (Finset.Icc 1 Q) Nat.divisors
      (fun p : Sigma (fun _ : Nat => Nat) => 1 / (p.1 : Real))]
    apply Finset.sum_congr rfl
    intro n _hn
    change (n.divisors.card : Real) / (n : Real) =
      Finset.sum n.divisors (fun _ => 1 / (n : Real))
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hSubset : forall z : Prod Nat Nat,
      ((Finset.sigma (Finset.Icc 1 Q) Nat.divisors).image
        (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2)) :
          Set (Prod Nat Nat)) z ->
      ((Finset.Icc 1 Q).product (Finset.Icc 1 Q) : Set (Prod Nat Nat)) z := by
    intro z hz
    have hData := Finset.mem_image.mp hz
    rw [<- hData.choose_spec.2]
    exact divisorSigma_pair_mem_product hData.choose hData.choose_spec.1
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) =
        Finset.sum (Finset.sigma (Finset.Icc 1 Q) Nat.divisors)
          (fun p : Sigma (fun _ : Nat => Nat) => 1 / (p.1 : Real)) := hExpand
    _ = Finset.sum ((Finset.sigma (Finset.Icc 1 Q) Nat.divisors).image
          (fun p : Sigma (fun _ : Nat => Nat) => Prod.mk p.2 (p.1 / p.2)))
        (fun z => 1 / (z.1 : Real) * (1 / (z.2 : Real))) := by
      rw [Finset.sum_image (divisorSigma_pair_inj Q)]
      apply Finset.sum_congr rfl
      intro p hp
      exact one_div_nat_eq_divisor_reciprocal_product
        (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).2)
    _ <= Finset.sum ((Finset.Icc 1 Q).product (Finset.Icc 1 Q))
        (fun z => 1 / (z.1 : Real) * (1 / (z.2 : Real))) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun z _ _ =>
        mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg z.1))
          (one_div_nonneg.mpr (Nat.cast_nonneg z.2)))
    _ = Finset.sum (Finset.Icc 1 Q) (fun a => Finset.sum (Finset.Icc 1 Q)
        (fun b => 1 / (a : Real) * (1 / (b : Real)))) :=
      Finset.sum_product (Finset.Icc 1 Q) (Finset.Icc 1 Q)
        (fun z : Prod Nat Nat => 1 / (z.1 : Real) * (1 / (z.2 : Real)))
    _ = (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 := by
      rw [<- Finset.sum_mul_sum]
      ring

end BombieriVinogradov
end

section
namespace BombieriVinogradov.RealAnalysis

theorem sum_one_div_Icc_le_one_add_log (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) <=
      1 + Real.log (Q : Real) := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) = (harmonic Q : Real) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, one_div]
    _ <= 1 + Real.log (Q : Real) := harmonic_le_one_add_log Q

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov

theorem le_totient_mul_card_divisors {n : Nat} (hn : 0 < n) :
    n <= n.totient * n.divisors.card := by
  calc
    n = Finset.sum n.divisors Nat.totient := (Nat.sum_totient n).symm
    _ <= Finset.sum n.divisors (fun _ => n.totient) :=
      Finset.sum_le_sum (fun d hd => Nat.le_of_dvd (Nat.totient_pos.mpr hn)
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
    _ = n.totient * n.divisors.card := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem one_div_totient_le_divisor_card_div {n : Nat} (hn : 0 < n) :
    1 / (n.totient : Real) <= (n.divisors.card : Real) / (n : Real) := by
  have hnReal : (0 : Real) < (n : Real) := Nat.cast_pos.mpr hn
  have hPhi : (0 : Real) < (n.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hn)
  have hCast : (n : Real) <= ((n.totient * n.divisors.card : Nat) : Real) :=
    Nat.cast_le.mpr (le_totient_mul_card_divisors hn)
  rw [Nat.cast_mul] at hCast
  have hFirst := div_le_div_of_nonneg_right hCast hPhi.le
  have hCancel :
      ((n.totient : Real) * (n.divisors.card : Real)) / (n.totient : Real) =
        (n.divisors.card : Real) := by field_simp
  rw [hCancel] at hFirst
  have hSecond := div_le_div_of_nonneg_right hFirst hnReal.le
  have hNormalize :
      (n : Real) / (n.totient : Real) / (n : Real) = 1 / (n.totient : Real) := by field_simp
  rw [hNormalize] at hSecond
  exact hSecond

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem sum_one_div_totient_le_sum_one_div_sq (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
      (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 := by
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
        Finset.sum (Finset.Icc 1 Q) (fun n : Nat => (n.divisors.card : Real) / (n : Real)) :=
      Finset.sum_le_sum (fun n hn => one_div_totient_le_divisor_card_div
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
    _ <= (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 :=
      sum_divisor_card_div_le_sum_one_div_sq Q

theorem sum_one_div_totient_le_one_add_log_sq (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
      (1 + Real.log (Q : Real)) ^ 2 := by
  have hUpper := RealAnalysis.sum_one_div_Icc_le_one_add_log Q
  have hNonneg : 0 <= Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) :=
    Finset.sum_nonneg (fun n _ => one_div_nonneg.mpr (Nat.cast_nonneg n))
  have hSquare :
      Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) *
        Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) <=
      (1 + Real.log (Q : Real)) * (1 + Real.log (Q : Real)) :=
    (mul_le_mul_of_nonneg_right hUpper hNonneg).trans
      (mul_le_mul_of_nonneg_left hUpper (hNonneg.trans hUpper))
  calc
    Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n.totient : Real)) <=
        (Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real))) ^ 2 :=
      sum_one_div_totient_le_sum_one_div_sq Q
    _ = Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) *
        Finset.sum (Finset.Icc 1 Q) (fun n : Nat => 1 / (n : Real)) := by ring
    _ <= (1 + Real.log (Q : Real)) * (1 + Real.log (Q : Real)) := hSquare
    _ = (1 + Real.log (Q : Real)) ^ 2 := by ring

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem one_div_totient_mul_le_product {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    1 / ((a * b).totient : Real) <=
      1 / (a.totient : Real) * (1 / (b.totient : Real)) := by
  have hPositive : (0 : Real) < (a.totient : Real) * (b.totient : Real) :=
    mul_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr ha))
      (Nat.cast_pos.mpr (Nat.totient_pos.mpr hb))
  have hCast : ((a.totient * b.totient : Nat) : Real) <= ((a * b).totient : Real) :=
    Nat.cast_le.mpr (Nat.totient_super_multiplicative a b)
  rw [Nat.cast_mul] at hCast
  calc
    1 / ((a * b).totient : Real) <= 1 / ((a.totient : Real) * (b.totient : Real)) :=
      one_div_le_one_div_of_le hPositive hCast
    _ = 1 / (a.totient : Real) * (1 / (b.totient : Real)) :=
      (one_div_mul_one_div (a := (a.totient : Real)) (b := (b.totient : Real))).symm

theorem div_totient_le_divisor_quotient_weight {n d : Nat}
    (hn : 0 < n) (hd : Dvd.dvd d n) (hdPos : 0 < d) (w : Real) (hw : 0 <= w) :
    w / (n.totient : Real) <=
      w / (d.totient : Real) * (1 / ((n / d).totient : Real)) := by
  have hQuotientPos := Nat.div_pos (Nat.le_of_dvd hn hd) hdPos
  have hWeight := one_div_totient_mul_le_product hdPos hQuotientPos
  rw [Nat.mul_div_cancel' hd] at hWeight
  calc
    w / (n.totient : Real) = w * (1 / (n.totient : Real)) := by ring
    _ <= w * (1 / (d.totient : Real) * (1 / ((n / d).totient : Real))) :=
      mul_le_mul_of_nonneg_left hWeight hw
    _ = w / (d.totient : Real) * (1 / ((n / d).totient : Real)) := by ring

end BombieriVinogradov
end

section
namespace BombieriVinogradov


theorem sum_weighted_divisors_div_totient_le_product (Q : Nat) (F : Nat -> Real)
    (hF : forall n, 0 <= F n) :
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) <=
      (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
        Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k.totient : Real)) := by
  calc
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) =
        Finset.sum (Finset.Icc 1 Q)
          (fun n => Finset.sum n.divisors (fun d => F d / (n.totient : Real))) :=
      Finset.sum_congr rfl (fun n _ => Finset.sum_div n.divisors F (n.totient : Real))
    _ <= Finset.sum (Finset.Icc 1 Q) (fun d => Finset.sum (Finset.Icc 1 Q)
        (fun k => F d / (d.totient : Real) * (1 / (k.totient : Real)))) :=
      sum_divisors_le_sum_product Q
        (fun n d => F d / (n.totient : Real))
        (fun d k => F d / (d.totient : Real) * (1 / (k.totient : Real)))
        (fun n d hn hd => div_totient_le_divisor_quotient_weight
          (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
          (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_mem_divisors hd) (F d) (hF d))
        (fun a b _ _ => mul_nonneg (div_nonneg (hF a) (Nat.cast_nonneg a.totient))
          (one_div_nonneg.mpr (Nat.cast_nonneg b.totient)))
    _ = (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
        Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k.totient : Real)) :=
      (Finset.sum_mul_sum (Finset.Icc 1 Q) (Finset.Icc 1 Q)
        (fun d => F d / (d.totient : Real)) (fun k => 1 / (k.totient : Real))).symm


theorem sum_weighted_divisors_div_totient_le_log_sq (Q : Nat) (F : Nat -> Real)
    (hF : forall n, 0 <= F n) :
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) <=
      (1 + Real.log Q) ^ 2 *
        Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real)) := by
  have hNonneg : 0 <=
      Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real)) :=
    Finset.sum_nonneg (fun d _ => div_nonneg (hF d) (Nat.cast_nonneg d.totient))
  calc
    Finset.sum (Finset.Icc 1 Q)
        (fun n => Finset.sum n.divisors F / (n.totient : Real)) <=
        (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
          Finset.sum (Finset.Icc 1 Q) (fun k => 1 / (k.totient : Real)) :=
      sum_weighted_divisors_div_totient_le_product Q F hF
    _ <= (Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real))) *
        (1 + Real.log Q) ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_one_div_totient_le_one_add_log_sq Q) hNonneg
    _ = (1 + Real.log Q) ^ 2 *
        Finset.sum (Finset.Icc 1 Q) (fun d => F d / (d.totient : Real)) :=
      mul_comm _ _

end BombieriVinogradov
end

section
namespace BombieriVinogradov.RealAnalysis


theorem sum_log_mul_log_div_log_two_le (Q : Nat) {X : Real} (hX : 1 <= X) :
    Finset.sum (Finset.Icc 1 Q)
        (fun q => Real.log q * Real.log X / Real.log (2 : Real)) <=
      (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) := by
  have hLogX : 0 <= Real.log X := Real.log_nonneg hX
  have hLogTwo : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  calc
    Finset.sum (Finset.Icc 1 Q)
        (fun q => Real.log q * Real.log X / Real.log (2 : Real)) <=
        Finset.sum (Finset.Icc 1 Q)
          (fun _ => Real.log Q * Real.log X / Real.log (2 : Real)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : 0 < q :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
      have hCast : (q : Real) <= (Q : Real) :=
        Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2
      have hLog : Real.log q <= Real.log Q :=
        Real.log_le_log (Nat.cast_pos.mpr hqPos) hCast
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLog hLogX) hLogTwo
    _ = (Q : Real) * (Real.log Q * Real.log X / Real.log (2 : Real)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ = (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) := by ring

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem psiGlobal_zero : psiGlobal 0 = 0 := by
  simp [psiGlobal]

theorem psiProgression_zero (N : Nat) (a : ZMod N) : psiProgression 0 N a = 0 := by
  simp [psiProgression]

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.RealAnalysis

theorem log_mul_log_nat_le_of_le_floor {N y : Nat} {X : Real}
    (hX : 0 <= X) (hy : 0 < y) (hyX : y <= Nat.floor X) :
    Real.log N * Real.log y / Real.log (2 : Real) <=
      Real.log N * Real.log X / Real.log (2 : Real) := by
  have hLog := Real.log_le_log (Nat.cast_pos.mpr hy)
    ((Nat.cast_le.mpr hyX).trans (Nat.floor_le hX))
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLog (Real.log_natCast_nonneg N))
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le

theorem log_mul_log_div_log_two_nonneg (N : Nat) {X : Real} (hX : 1 <= X) :
    0 <= Real.log N * Real.log X / Real.log (2 : Real) :=
  div_nonneg (mul_nonneg (Real.log_natCast_nonneg N) (Real.log_nonneg hX))
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.DirichletCharacter


theorem three_le_level_of_ne_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ≠ 1) : 3 ≤ N := by
  by_contra hN
  have hNle : N ≤ 2 := by omega
  interval_cases N
  · exact (NeZero.ne 0) rfl
  · exact hchi (Subsingleton.elim _ _)
  · apply hchi
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    simp

theorem primitiveCharacter_ne_one_of_ne_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem primitiveCharacter_pow_ne_one_of_pow_ne_one
    {N m : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N)
    (hchi : chi ^ m ≠ 1) : chi.primitiveCharacter ^ m ≠ 1 := by
  intro hPrimitive
  apply hchi
  let lift : _root_.DirichletCharacter Complex chi.conductor →*
      _root_.DirichletCharacter Complex N :=
    _root_.DirichletCharacter.changeLevel (R := Complex)
      chi.conductor_dvd_level
  have hLift : lift chi.primitiveCharacter = chi :=
    chi.changeLevel_primitiveCharacter
  calc
    chi ^ m = (lift chi.primitiveCharacter) ^ m := by rw [hLift]
    _ = lift (chi.primitiveCharacter ^ m) := by
      rw [map_pow]
    _ = lift 1 := by
      rw [hPrimitive]
    _ = 1 := by
      rw [map_one]

theorem inv_eq_self_of_sq_eq_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ^ 2 = 1) :
    chi⁻¹ = chi := by
  have hProduct : chi * chi = 1 := by
    simpa [pow_two] using hchi
  exact (eq_inv_of_mul_eq_one_left hProduct).symm

theorem primitiveCharacter_pow_eq_one_of_pow_eq_one
    {N m : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N)
    (hchi : chi ^ m = 1) : chi.primitiveCharacter ^ m = 1 := by
  apply _root_.DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
  rw [map_pow, chi.changeLevel_primitiveCharacter, hchi, map_one]

theorem conductor_le_level {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) : chi.conductor ≤ N :=
  Nat.le_of_dvd (NeZero.pos N) chi.conductor_dvd_level

theorem three_le_conductor_of_ne_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact three_le_level_of_ne_one chi.primitiveCharacter
    (primitiveCharacter_ne_one_of_ne_one chi hchi)

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov.DirichletCharacter

theorem primitive_sigma_eq_of_lift_eq {d e N : Nat} [NeZero N]
    (hd : Dvd.dvd d N) (he : Dvd.dvd e N)
    (chi : _root_.DirichletCharacter Complex d) (psi : _root_.DirichletCharacter Complex e)
    (hchi : chi.IsPrimitive) (hpsi : psi.IsPrimitive)
    (h : _root_.DirichletCharacter.changeLevel hd chi =
      _root_.DirichletCharacter.changeLevel he psi) :
    (Sigma.mk d chi : Sigma (fun q : Nat => _root_.DirichletCharacter Complex q)) =
      Sigma.mk e psi := by
  have hConductor := congrArg
    (fun eta : _root_.DirichletCharacter Complex N => eta.conductor) h
  rw [_root_.DirichletCharacter.conductor_changeLevel,
    _root_.DirichletCharacter.conductor_changeLevel] at hConductor
  rw [(_root_.DirichletCharacter.isPrimitive_def chi).mp hchi,
    (_root_.DirichletCharacter.isPrimitive_def psi).mp hpsi] at hConductor
  subst e
  have hChar := _root_.DirichletCharacter.changeLevel_injective hd h
  cases hChar
  rfl

theorem primitiveCharacter_sigma_changeLevel_eq {d N : Nat} [NeZero N]
    (hd : Dvd.dvd d N) (chi : _root_.DirichletCharacter Complex d)
    (hchi : chi.IsPrimitive) :
    (Sigma.mk (_root_.DirichletCharacter.changeLevel hd chi).conductor
      (_root_.DirichletCharacter.changeLevel hd chi).primitiveCharacter :
        Sigma (fun q : Nat => _root_.DirichletCharacter Complex q)) = Sigma.mk d chi := by
  exact primitive_sigma_eq_of_lift_eq
    (_root_.DirichletCharacter.changeLevel hd chi).conductor_dvd_level hd
    (_root_.DirichletCharacter.changeLevel hd chi).primitiveCharacter chi
    (_root_.DirichletCharacter.changeLevel hd chi).primitiveCharacter_isPrimitive hchi
    (_root_.DirichletCharacter.changeLevel hd chi).changeLevel_primitiveCharacter

end BombieriVinogradov.DirichletCharacter
end

section
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem sum_nonprincipal_eq_sum_primitive_conductors {N : Nat} [NeZero N]
    (F : (q : Nat) -> _root_.DirichletCharacter Complex q -> Real) :
    Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
      (fun chi => F chi.conductor chi.primitiveCharacter) =
    Finset.sum N.divisors (fun q =>
      Finset.sum ((LargeSieve.primitiveCharacters q).erase 1) (F q)) := by
  symm
  rw [Finset.sum_sigma']
  refine Finset.sum_bij
    (fun p hp => _root_.DirichletCharacter.changeLevel
      (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).1) p.2)
    ?mem ?inj ?surj ?weight
  case mem =>
    intro p hp
    have hChar := (Finset.mem_erase.mp (Finset.mem_sigma.mp hp).2).1
    apply Finset.mem_erase.mpr
    exact And.intro
      (fun h => hChar ((_root_.DirichletCharacter.changeLevel_eq_one_iff _).mp h))
      (Finset.mem_univ _)
  case inj =>
    intro p hp q hq h
    exact primitive_sigma_eq_of_lift_eq _ _ p.2 q.2
      (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hp).2).2).2
      (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hq).2).2).2 h
  case surj =>
    intro chi hchi
    exact Exists.intro (Sigma.mk chi.conductor chi.primitiveCharacter)
      (Exists.intro (Finset.mem_sigma.mpr (And.intro
        (Nat.mem_divisors.mpr (And.intro chi.conductor_dvd_level (NeZero.ne N)))
        (Finset.mem_erase.mpr (And.intro
          (primitiveCharacter_ne_one_of_ne_one chi (Finset.mem_erase.mp hchi).1)
          (Finset.mem_filter.mpr (And.intro (Finset.mem_univ _)
            chi.primitiveCharacter_isPrimitive)))))) chi.changeLevel_primitiveCharacter)
  case weight =>
    intro p hp
    exact (congrArg (fun z : Sigma (fun q : Nat => _root_.DirichletCharacter Complex q) =>
      F z.1 z.2) (primitiveCharacter_sigma_changeLevel_eq
        (Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp hp).1) p.2
        (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_sigma.mp hp).2).2).2)).symm

end BombieriVinogradov.DirichletCharacter
end

section
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem card_nonprincipal_add_one_eq_totient {N : Nat} [NeZero N] :
    (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N)).card + 1 = N.totient := by
  have hCard := Finset.card_erase_add_one
    (Finset.mem_univ (1 : _root_.DirichletCharacter Complex N))
  rw [Finset.card_univ, <- Nat.card_eq_fintype_card,
    _root_.DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity Complex N] at hCard
  exact hCard

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov

theorem exists_primeFactor_pow_with_log_bound
    {N n x : Nat} (hN : Ne N 0) (hn : n <= x)
    (hBad : Not (Nat.Coprime n N)) (hPrimePow : IsPrimePow n) :
    exists p k : Nat, And ((N.primeFactors : Set Nat) p)
      (And (0 < k) (And (k <= Nat.log 2 x) (n = p ^ k))) := by
  have hWitness := (isPrimePow_nat_iff_bounded_log n).mp hPrimePow
  let k : Nat := hWitness.choose
  have hkBound : k <= Nat.log 2 n := hWitness.choose_spec.1
  have hkPos : 0 < k := hWitness.choose_spec.2.1
  have hPrimeWitness : exists p : Nat,
      And (p <= n) (And (n = p ^ k) (Nat.Prime p)) := hWitness.choose_spec.2.2
  let p : Nat := hPrimeWitness.choose
  have hPower : n = p ^ k := hPrimeWitness.choose_spec.2.1
  have hPrime : Nat.Prime p := hPrimeWitness.choose_spec.2.2
  have hDiv : Dvd.dvd p N := by
    by_cases h : Dvd.dvd p N
    case pos => exact h
    case neg =>
      have hCoprime : Nat.Coprime p N := hPrime.coprime_iff_not_dvd.mpr h
      have hPowerCoprime : Nat.Coprime (p ^ k) N := hCoprime.pow_left k
      have hNCoprime : Nat.Coprime n N := by
        rw [hPower]
        exact hPowerCoprime
      exact False.elim (hBad hNCoprime)
  have hpMem : (N.primeFactors : Set Nat) p :=
    Nat.mem_primeFactors.mpr (And.intro hPrime (And.intro hDiv hN))
  have hLogMono : Nat.log 2 n <= Nat.log 2 x := Nat.log_mono_right hn
  exact Exists.intro p (Exists.intro k
    (And.intro hpMem (And.intro hkPos (And.intro (hkBound.trans hLogMono) hPower))))

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem badPrimePower_dvd_level_pow_log
    {N n x : Nat} (hN : Ne N 0) (hn : n <= x)
    (hBad : Not (Nat.Coprime n N)) (hPrimePow : IsPrimePow n) :
    Dvd.dvd n (N ^ Nat.log 2 x) := by
  have hWitness := exists_primeFactor_pow_with_log_bound hN hn hBad hPrimePow
  let p : Nat := hWitness.choose
  let k : Nat := hWitness.choose_spec.choose
  have hData := hWitness.choose_spec.choose_spec
  have hDiv : Dvd.dvd p N := (Nat.mem_primeFactors.mp hData.1).2.1
  have hExponent : k <= Nat.log 2 x := hData.2.2.1
  have hPower : n = p ^ k := hData.2.2.2
  have hPowerDiv : Dvd.dvd (p ^ k) (N ^ Nat.log 2 x) :=
    pow_dvd_pow_of_dvd_of_le hDiv hExponent
  rw [hPower]
  exact hPowerDiv

end BombieriVinogradov
end

section
namespace BombieriVinogradov

theorem nonCoprimeMangoldtSum_le_natLog_mul_log
    {N : Nat} (hN : Ne N 0) (x : Nat) :
    Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
      ArithmeticFunction.vonMangoldt <=
        (Nat.log 2 x : Real) * Real.log N := by
  classical
  let s : Finset Nat := (Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N))
  have hPowerNe : Ne (N ^ Nat.log 2 x) 0 := pow_ne_zero _ hN
  have hCover : forall n : Nat,
      (s.filter (fun m => Ne (ArithmeticFunction.vonMangoldt m) 0) : Set Nat) n ->
        ((N ^ Nat.log 2 x).divisors : Set Nat) n := by
    intro n hn
    have hNonzeroData :
        And ((s : Set Nat) n) (Ne (ArithmeticFunction.vonMangoldt n) 0) :=
      (Finset.mem_filter (s := s) (a := n)
        (p := fun m : Nat => Ne (ArithmeticFunction.vonMangoldt m) 0)).mp hn
    have hBadData :
        And ((Finset.Icc 1 x : Set Nat) n) (Not (Nat.Coprime n N)) :=
      (Finset.mem_filter (s := Finset.Icc 1 x) (a := n)
        (p := fun m : Nat => Not (Nat.Coprime m N))).mp hNonzeroData.1
    have hnLe : n <= x := (Finset.mem_Icc.mp hBadData.1).2
    have hDiv := badPrimePower_dvd_level_pow_log hN hnLe hBadData.2
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hNonzeroData.2)
    exact Nat.mem_divisors.mpr (And.intro hDiv hPowerNe)
  change Finset.sum s ArithmeticFunction.vonMangoldt <= _
  calc
    Finset.sum s ArithmeticFunction.vonMangoldt =
        Finset.sum (s.filter (fun n => Ne (ArithmeticFunction.vonMangoldt n) 0))
          ArithmeticFunction.vonMangoldt :=
      (Finset.sum_filter_ne_zero s).symm
    _ <= Finset.sum (N ^ Nat.log 2 x).divisors ArithmeticFunction.vonMangoldt :=
      Finset.sum_le_sum_of_subset_of_nonneg hCover
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((N ^ Nat.log 2 x : Nat) : Real) := ArithmeticFunction.vonMangoldt_sum
    _ = (Nat.log 2 x : Real) * Real.log N := by
      rw [Nat.cast_pow, Real.log_pow]

end BombieriVinogradov
end

section
namespace BombieriVinogradov.RealAnalysis

theorem natLog_two_le_real_log_div {x : Nat} (hx : 0 < x) :
    (Nat.log 2 x : Real) <= Real.log x / Real.log (2 : Real) := by
  have hxNe : Ne x 0 := by omega
  have hPower : 2 ^ Nat.log 2 x <= x := Nat.pow_log_le_self 2 hxNe
  have hRaw : ((2 ^ Nat.log 2 x : Nat) : Real) <= (x : Real) :=
    Nat.cast_le.mpr hPower
  norm_num only [Nat.cast_pow] at hRaw
  have hLogPower : Real.log ((2 : Real) ^ Nat.log 2 x) <= Real.log x :=
    Real.log_le_log (by positivity) hRaw
  rw [Real.log_pow] at hLogPower
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogTwoNe : Ne (Real.log (2 : Real)) 0 := by linarith
  have hCancel :
      (Real.log x / Real.log (2 : Real)) * Real.log (2 : Real) = Real.log x := by
    field_simp [hLogTwoNe]
  nlinarith

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov

theorem nonCoprimeMangoldtSum_le_log_mul_log
    {N x : Nat} (hN : Ne N 0) (hx : 0 < x) :
    Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
      ArithmeticFunction.vonMangoldt <=
        Real.log N * Real.log x / Real.log (2 : Real) := by
  calc
    Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
        ArithmeticFunction.vonMangoldt <=
          (Nat.log 2 x : Real) * Real.log N :=
      nonCoprimeMangoldtSum_le_natLog_mul_log hN x
    _ <= (Real.log x / Real.log (2 : Real)) * Real.log N :=
      mul_le_mul_of_nonneg_right (RealAnalysis.natLog_two_le_real_log_div hx)
        (Real.log_natCast_nonneg N)
    _ = Real.log N * Real.log x / Real.log (2 : Real) := by ring

end BombieriVinogradov
end

section
namespace BombieriVinogradov.DirichletCharacter

theorem natCast_sub_primitiveCharacter_eq {N : Nat}
    (chi : _root_.DirichletCharacter Complex N) (n : Nat) :
    chi (n : ZMod N) - chi.primitiveCharacter (n : ZMod chi.conductor) =
      if Nat.Coprime n N then 0
      else -chi.primitiveCharacter (n : ZMod chi.conductor) := by
  by_cases h : Nat.Coprime n N
  case pos =>
    rw [if_pos h]
    have hInt := chi.primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr h)
    have hNat :
        chi.primitiveCharacter (n : ZMod chi.conductor) = chi (n : ZMod N) := by
      simpa only [Int.cast_natCast] using hInt
    rw [hNat]
    ring
  case neg =>
    rw [if_neg h]
    have hZero : chi (n : ZMod N) = 0 :=
      chi.map_nonunit (fun hUnit => h ((ZMod.isUnit_iff_coprime n N).mp hUnit))
    rw [hZero]
    ring

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov.DirichletCharacter

theorem norm_mangoldt_mul_natCast_sub_primitive_le
    {N : Nat} (chi : _root_.DirichletCharacter Complex N) (n : Nat) :
    norm ((ArithmeticFunction.vonMangoldt n : Complex) *
      (chi (n : ZMod N) - chi.primitiveCharacter (n : ZMod chi.conductor))) <=
        if Nat.Coprime n N then 0 else ArithmeticFunction.vonMangoldt n := by
  rw [natCast_sub_primitiveCharacter_eq]
  by_cases h : Nat.Coprime n N
  case pos =>
    rw [if_pos h, if_pos h]
    simp only [mul_zero, norm_zero, le_refl]
  case neg =>
    simp only [h, if_false]
    rw [norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (chi.primitiveCharacter.norm_le_one n)

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov.VaughanMeanValue

theorem norm_psiCharacterSum_sub_primitive_le_mangoldt
    {N : Nat} (chi : _root_.DirichletCharacter Complex N) (x : Nat) :
    norm (psiCharacterSum x N chi -
      psiCharacterSum x chi.conductor chi.primitiveCharacter) <=
        Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
          ArithmeticFunction.vonMangoldt := by
  classical
  unfold psiCharacterSum
  rw [<- Finset.sum_sub_distrib]
  calc
    norm (Finset.sum (Finset.Icc 1 x) (fun n =>
        (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N) -
          (ArithmeticFunction.vonMangoldt n : Complex) *
            chi.primitiveCharacter (n : ZMod chi.conductor))) <=
        Finset.sum (Finset.Icc 1 x) (fun n => norm
          ((ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N) -
            (ArithmeticFunction.vonMangoldt n : Complex) *
              chi.primitiveCharacter (n : ZMod chi.conductor))) := norm_sum_le _ _
    _ <= Finset.sum (Finset.Icc 1 x) (fun n =>
        if Nat.Coprime n N then 0 else ArithmeticFunction.vonMangoldt n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [<- mul_sub]
      exact DirichletCharacter.norm_mangoldt_mul_natCast_sub_primitive_le chi n
    _ = Finset.sum ((Finset.Icc 1 x).filter (fun n => Not (Nat.Coprime n N)))
        ArithmeticFunction.vonMangoldt := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : Nat.Coprime n N
      case pos =>
        have hh : Not (Not (Nat.Coprime n N)) := fun hn => hn h
        rw [if_pos h, if_neg hh]
      case neg => rw [if_neg h, if_pos h]

end BombieriVinogradov.VaughanMeanValue
end

section
namespace BombieriVinogradov.VaughanMeanValue

theorem norm_psiCharacterSum_le_primitive_add_log_mul_log
    {N x : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N) (hx : 0 < x) :
    norm (psiCharacterSum x N chi) <=
      norm (psiCharacterSum x chi.conductor chi.primitiveCharacter) +
        Real.log N * Real.log x / Real.log (2 : Real) := by
  exact (norm_le_norm_add_norm_sub' (psiCharacterSum x N chi)
    (psiCharacterSum x chi.conductor chi.primitiveCharacter)).trans
    (add_le_add (le_refl _) ((norm_psiCharacterSum_sub_primitive_le_mangoldt chi x).trans
      (nonCoprimeMangoldtSum_le_log_mul_log (NeZero.ne N) hx)))

end BombieriVinogradov.VaughanMeanValue
end

section
namespace BombieriVinogradov.RealAnalysis

theorem sum_div_add_error_div_le_sum_div_add_error
    {I : Type} (s : Finset I) (f g : I -> Real) {B t : Real}
    (ht : 0 < t) (hCard : (s.card : Real) + 1 = t)
    (hfg : forall i : I, (s : Set I) i -> f i <= g i + B) :
    Finset.sum s f / t + B / t <= Finset.sum s g / t + B := by
  have hSum := Finset.sum_le_sum hfg
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hSum
  have hDiv := div_le_div_of_nonneg_right hSum ht.le
  have hCancel : t * B / t = B := by field_simp
  calc
    Finset.sum s f / t + B / t <=
        (Finset.sum s g + (s.card : Real) * B) / t + B / t :=
      add_le_add hDiv (le_refl _)
    _ = Finset.sum s g / t + ((s.card : Real) + 1) * B / t := by ring
    _ = Finset.sum s g / t + B := by rw [hCard, hCancel]

end BombieriVinogradov.RealAnalysis
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem ofReal_psiGlobal (x : Nat) :
    (psiGlobal x : Complex) =
      Finset.sum (Finset.Icc 1 x) (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) := by
  rw [psiGlobal, Complex.ofReal_sum]

theorem ofReal_psiProgression (x N : Nat) (a : ZMod N) :
    (psiProgression x N a : Complex) =
      Finset.sum (Finset.Icc 1 x) (fun n =>
        if a = (n : ZMod N) then (ArithmeticFunction.vonMangoldt n : Complex) else 0) := by
  rw [psiProgression, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases h : a = (n : ZMod N)
  case pos => simp only [if_pos h]
  case neg => simp only [if_neg h, Complex.ofReal_zero]

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.DirichletCharacter

theorem sum_characters_weighted_eq_totient_mul_residue
    {N : Nat} [NeZero N] (a : Units (ZMod N))
    (s : Finset Nat) (f : Nat -> Complex) :
    Finset.sum Finset.univ (fun chi : _root_.DirichletCharacter Complex N =>
      chi (Inv.inv (a : ZMod N)) *
        Finset.sum s (fun n => f n * chi (n : ZMod N))) =
      (N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  calc
    Finset.sum Finset.univ (fun chi : _root_.DirichletCharacter Complex N =>
        chi (Inv.inv (a : ZMod N)) * (f n * chi (n : ZMod N))) =
        f n * Finset.sum Finset.univ (fun chi : _root_.DirichletCharacter Complex N =>
          chi (Inv.inv (a : ZMod N)) * chi (n : ZMod N)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _hchi
      ring
    _ = f n * (if (a : ZMod N) = (n : ZMod N) then (N.totient : Complex) else 0) := by
      rw [_root_.DirichletCharacter.sum_char_inv_mul_char_eq (R := Complex) a.isUnit]
    _ = (N.totient : Complex) *
        (if (a : ZMod N) = (n : ZMod N) then f n else 0) := by
      by_cases h : (a : ZMod N) = (n : ZMod N)
      case pos => rw [if_pos h, if_pos h]; ring
      case neg => rw [if_neg h, if_neg h]; ring

end BombieriVinogradov.DirichletCharacter
end

section
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem totient_mul_residue_eq_nonprincipal_add_principal
    {N : Nat} [NeZero N] (a : Units (ZMod N))
    (s : Finset Nat) (f : Nat -> Complex) :
    (N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) =
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N))) +
        Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N)) := by
  have hOne : (1 : _root_.DirichletCharacter Complex N)
      (Inv.inv (a : ZMod N)) = 1 := by
    rw [ZMod.inv_coe_unit]
    exact MulChar.one_apply_coe (Inv.inv a)
  have hSplit := Finset.sum_erase_add
    (Finset.univ : Finset (_root_.DirichletCharacter Complex N))
    (fun chi => chi (Inv.inv (a : ZMod N)) *
      Finset.sum s (fun n => f n * chi (n : ZMod N)))
    (Finset.mem_univ (1 : _root_.DirichletCharacter Complex N))
  rw [hOne, one_mul, sum_characters_weighted_eq_totient_mul_residue] at hSplit
  exact hSplit.symm

end BombieriVinogradov.DirichletCharacter
end

section
open scoped Classical

namespace BombieriVinogradov.DirichletCharacter

theorem norm_totient_mul_residue_sub_sum_le
    {N : Nat} [NeZero N] (a : Units (ZMod N))
    (s : Finset Nat) (f : Nat -> Complex) :
    norm ((N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) -
          Finset.sum s f) <=
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (Finset.sum s (fun n => f n * chi (n : ZMod N)))) +
      norm (Finset.sum s f - Finset.sum s (fun n => f n *
        (1 : _root_.DirichletCharacter Complex N) (n : ZMod N))) := by
  have hRest :
      norm (Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N)))) <=
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (Finset.sum s (fun n => f n * chi (n : ZMod N)))) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro chi _hchi
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (chi.norm_le_one (Inv.inv (a : ZMod N)))
  calc
    norm ((N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) -
          Finset.sum s f) =
      norm (Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N))) -
        (Finset.sum s f - Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N)))) := by
      rw [totient_mul_residue_eq_nonprincipal_add_principal]
      congr 1
      ring
    _ <= norm (Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => chi (Inv.inv (a : ZMod N)) *
          Finset.sum s (fun n => f n * chi (n : ZMod N)))) +
        norm (Finset.sum s f - Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N))) := norm_sub_le _ _
    _ <= Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (Finset.sum s (fun n => f n * chi (n : ZMod N)))) +
        norm (Finset.sum s f - Finset.sum s (fun n => f n *
          (1 : _root_.DirichletCharacter Complex N) (n : ZMod N))) :=
      add_le_add hRest (le_refl _)

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov.DirichletCharacter

theorem principal_natCast_eq_indicator (N n : Nat) :
    (1 : _root_.DirichletCharacter Complex N) (n : ZMod N) =
      if Nat.Coprime n N then 1 else 0 := by
  by_cases h : Nat.Coprime n N
  case pos =>
    rw [if_pos h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n N).mpr h)
  case neg =>
    rw [if_neg h]
    exact (1 : _root_.DirichletCharacter Complex N).map_nonunit
      (fun hUnit => h ((ZMod.isUnit_iff_coprime n N).mp hUnit))

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov.DirichletCharacter

theorem sum_sub_principal_eq_sum_filter (N : Nat)
    (s : Finset Nat) (f : Nat -> Complex) :
    Finset.sum s f - Finset.sum s (fun n =>
      f n * (1 : _root_.DirichletCharacter Complex N) (n : ZMod N)) =
      Finset.sum (s.filter (fun n => Not (Nat.Coprime n N))) f := by
  rw [<- Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [principal_natCast_eq_indicator]
  by_cases h : Nat.Coprime n N
  case pos =>
    have hNot : Not (Not (Nat.Coprime n N)) := fun hBad => hBad h
    rw [if_pos h, if_neg hNot, mul_one, sub_self]
  case neg =>
    rw [if_neg h, if_pos h, mul_zero, sub_zero]

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov.DirichletCharacter

theorem norm_psiGlobal_sub_principal_le_log_mul_log
    {N x : Nat} [NeZero N] (hx : 0 < x) :
    norm ((WeightedBombieriVinogradov.psiGlobal x : Complex) -
      VaughanMeanValue.psiCharacterSum x N (1 : _root_.DirichletCharacter Complex N)) <=
        Real.log N * Real.log x / Real.log (2 : Real) := by
  rw [WeightedBombieriVinogradov.ofReal_psiGlobal, VaughanMeanValue.psiCharacterSum,
    sum_sub_principal_eq_sum_filter, <- Complex.ofReal_sum]
  rw [Complex.norm_of_nonneg
    (Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))]
  exact nonCoprimeMangoldtSum_le_log_mul_log (NeZero.ne N) hx

end BombieriVinogradov.DirichletCharacter
end

section
namespace BombieriVinogradov.RealAnalysis

theorem abs_sub_div_le_of_abs_mul_sub_le {t p q B : Real}
    (ht : 0 < t) (h : abs (t * p - q) <= B) :
    abs (p - q / t) <= B / t := by
  have hId : t * (p - q / t) = t * p - q := by field_simp
  have hQuotient : t * (B / t) = B := by field_simp
  have hAbs : abs (t * p - q) = t * abs (p - q / t) := by
    rw [<- hId, abs_mul, abs_of_pos ht]
  have hScaled : t * abs (p - q / t) <= t * (B / t) := by
    rw [<- hAbs, hQuotient]
    exact h
  exact le_of_mul_le_mul_left hScaled ht

end BombieriVinogradov.RealAnalysis
end

section
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem abs_psiProgression_sub_psiGlobal_div_totient_le
    {N x : Nat} [NeZero N] (a : Units (ZMod N)) (hx : 0 < x) :
    abs (psiProgression x N (a : ZMod N) - psiGlobal x / (N.totient : Real)) <=
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (VaughanMeanValue.psiCharacterSum x N chi)) / (N.totient : Real) +
      Real.log N * Real.log x / ((N.totient : Real) * Real.log (2 : Real)) := by
  have hFinite := DirichletCharacter.norm_totient_mul_residue_sub_sum_le a
    (Finset.Icc 1 x) (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
  rw [<- ofReal_psiProgression, <- ofReal_psiGlobal] at hFinite
  change norm ((N.totient : Complex) * (psiProgression x N (a : ZMod N) : Complex) -
      (psiGlobal x : Complex)) <=
    Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
      (fun chi => norm (VaughanMeanValue.psiCharacterSum x N chi)) +
    norm ((psiGlobal x : Complex) - VaughanMeanValue.psiCharacterSum x N
      (1 : _root_.DirichletCharacter Complex N)) at hFinite
  have hBound := hFinite.trans (add_le_add (le_refl _)
    (DirichletCharacter.norm_psiGlobal_sub_principal_le_log_mul_log hx))
  rw [<- Complex.ofReal_natCast N.totient, <- Complex.ofReal_mul,
    <- Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hBound
  have hTotient : (0 : Real) < (N.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  have hNormalized := RealAnalysis.abs_sub_div_le_of_abs_mul_sub_le hTotient hBound
  simpa only [add_div, div_div, mul_comm (Real.log (2 : Real)) (N.totient : Real)]
    using hNormalized

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem abs_psiProgression_sub_psiGlobal_div_totient_le_primitive
    {N x : Nat} [NeZero N] (a : Units (ZMod N)) (hx : 0 < x) :
    abs (psiProgression x N (a : ZMod N) - psiGlobal x / (N.totient : Real)) <=
      Finset.sum N.divisors (fun d =>
        Finset.sum ((LargeSieve.primitiveCharacters d).erase 1)
          (fun chi => norm (VaughanMeanValue.psiCharacterSum x d chi))) / (N.totient : Real) +
      Real.log N * Real.log x / Real.log (2 : Real) := by
  have hCard :
      ((Finset.univ.erase (1 : _root_.DirichletCharacter Complex N)).card : Real) + 1 =
        (N.totient : Real) := by
    have hCast := congrArg (fun m : Nat => (m : Real))
      (DirichletCharacter.card_nonprincipal_add_one_eq_totient (N := N))
    simpa only [Nat.cast_add, Nat.cast_one] using hCast
  have hTotient : (0 : Real) < (N.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  have hAverage := RealAnalysis.sum_div_add_error_div_le_sum_div_add_error
    (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
    (fun chi => norm (VaughanMeanValue.psiCharacterSum x N chi))
    (fun chi => norm (VaughanMeanValue.psiCharacterSum x chi.conductor chi.primitiveCharacter))
    hTotient hCard
    (fun chi _ => VaughanMeanValue.norm_psiCharacterSum_le_primitive_add_log_mul_log chi hx)
  simp only [div_div, mul_comm (Real.log (2 : Real)) (N.totient : Real)] at hAverage
  have hCombined := (abs_psiProgression_sub_psiGlobal_div_totient_le a hx).trans hAverage
  rw [DirichletCharacter.sum_nonprincipal_eq_sum_primitive_conductors (N := N)
    (fun d chi => norm (VaughanMeanValue.psiCharacterSum x d chi))] at hCombined
  exact hCombined

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem abs_psiProgression_sub_psiGlobal_div_totient_le_maximal_primitive
    {X : Real} {N y : Nat} [NeZero N] (a : Units (ZMod N))
    (hX : 2 <= X) (hy : y <= Nat.floor X) :
    abs (psiProgression y N (a : ZMod N) - psiGlobal y / (N.totient : Real)) <=
      Finset.sum N.divisors (fun d =>
        Finset.sum ((LargeSieve.primitiveCharacters d).erase 1)
          (fun chi => VaughanMeanValue.maximalPsiNorm X chi)) / (N.totient : Real) +
      Real.log N * Real.log X / Real.log (2 : Real) := by
  have hX0 : 0 <= X := by linarith
  have hX1 : 1 <= X := by linarith
  have hTotient : (0 : Real) < (N.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  by_cases hZero : y = 0
  case pos =>
    subst y
    rw [psiProgression_zero, psiGlobal_zero, zero_div, sub_zero, abs_zero]
    exact add_nonneg (div_nonneg
      (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg
        (fun chi _ => VaughanMeanValue.maximalPsiNorm_nonneg X chi))) hTotient.le)
      (RealAnalysis.log_mul_log_div_log_two_nonneg N hX1)
  case neg =>
    apply (abs_psiProgression_sub_psiGlobal_div_totient_le_primitive a
      (Nat.pos_of_ne_zero hZero)).trans
    exact add_le_add (div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun d _ => Finset.sum_le_sum
        (fun chi _ => VaughanMeanValue.norm_psiCharacterSum_le_maximalPsiNorm chi hy)))
      hTotient.le) (RealAnalysis.log_mul_log_nat_le_of_le_floor hX0
        (Nat.pos_of_ne_zero hZero) hy)

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


theorem maximalWeightedDiscrepancy_le_primitive
    {X : Real} {N : Nat} [NeZero N] (hX : 2 <= X) :
    maximalWeightedDiscrepancy X N <=
      Finset.sum N.divisors (nonprincipalPrimitiveMaximalSum X) / (N.totient : Real) +
        Real.log N * Real.log X / Real.log (2 : Real) := by
  unfold maximalWeightedDiscrepancy
  exact ciSup_le (fun a => ciSup_le (fun y =>
    abs_psiProgression_sub_psiGlobal_div_totient_le_maximal_primitive
      a hX (Nat.le_of_lt_succ y.isLt)))

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.WeightedBombieriVinogradov


theorem averageWeightedDiscrepancy_le_primitiveConductorMean
    (Q : Nat) {X : Real} (hX : 2 <= X) :
    averageWeightedDiscrepancy X Q <=
      (1 + Real.log Q) ^ 2 * primitiveConductorMean X Q +
        (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) := by
  have hX1 : 1 <= X := by linarith
  unfold averageWeightedDiscrepancy
  calc
    Finset.sum (Finset.Icc 1 Q) (maximalWeightedDiscrepancy X) <=
        Finset.sum (Finset.Icc 1 Q) (fun q =>
          Finset.sum q.divisors (nonprincipalPrimitiveMaximalSum X) / (q.totient : Real) +
            Real.log q * Real.log X / Real.log (2 : Real)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : 0 < q :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
      let : NeZero q := NeZero.mk (Nat.ne_of_gt hqPos)
      exact maximalWeightedDiscrepancy_le_primitive hX
    _ = Finset.sum (Finset.Icc 1 Q)
          (fun q => Finset.sum q.divisors (nonprincipalPrimitiveMaximalSum X) /
            (q.totient : Real)) +
        Finset.sum (Finset.Icc 1 Q)
          (fun q => Real.log q * Real.log X / Real.log (2 : Real)) :=
      Finset.sum_add_distrib
    _ <= (1 + Real.log Q) ^ 2 * primitiveConductorMean X Q +
        (Q : Real) * Real.log Q * Real.log X / Real.log (2 : Real) :=
      add_le_add
        (sum_weighted_divisors_div_totient_le_log_sq Q
          (nonprincipalPrimitiveMaximalSum X) (nonprincipalPrimitiveMaximalSum_nonneg X))
        (RealAnalysis.sum_log_mul_log_div_log_two_le Q (X := X) hX1)

end BombieriVinogradov.WeightedBombieriVinogradov
end

section
namespace BombieriVinogradov.PrimeCountingConversion


noncomputable def thetaGlobalNat (N : Nat) : Real :=
  Finset.sum (Finset.Icc 1 N) (fun n => if n.Prime then Real.log (n : Real) else 0)


noncomputable def thetaProgressionNat (N q : Nat) (a : ZMod q) : Real :=
  Finset.sum (Finset.Icc 1 N)
    (fun n : Nat => if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0)


def primeProgressionNat (N q : Nat) (a : ZMod q) : Nat :=
  ((Finset.Icc 1 N).filter (fun n : Nat => And n.Prime ((n : ZMod q) = a))).card


def primeGlobalNat (N : Nat) : Nat :=
  ((Finset.Icc 1 N).filter Nat.Prime).card


noncomputable def centeredPsiCoefficient (n q : Nat) (a : ZMod q) : Real :=
  (if a = (n : ZMod q) then ArithmeticFunction.vonMangoldt n else 0) -
    ArithmeticFunction.vonMangoldt n / (q.totient : Real)


noncomputable def centeredThetaCoefficient (n q : Nat) (a : ZMod q) : Real :=
  (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) -
    (if n.Prime then Real.log (n : Real) else 0) / (q.totient : Real)

end BombieriVinogradov.PrimeCountingConversion
end

section
namespace BombieriVinogradov.PrimeCountingConversion


theorem sum_centeredPsiCoefficient (N q : Nat) (a : ZMod q) :
    Finset.sum (Finset.Icc 1 N) (fun n => centeredPsiCoefficient n q a) =
      WeightedBombieriVinogradov.psiProgression N q a -
        WeightedBombieriVinogradov.psiGlobal N / (q.totient : Real) := by
  unfold centeredPsiCoefficient WeightedBombieriVinogradov.psiProgression
    WeightedBombieriVinogradov.psiGlobal
  rw [Finset.sum_sub_distrib, Finset.sum_div]


theorem sum_centeredThetaCoefficient (N q : Nat) (a : ZMod q) :
    Finset.sum (Finset.Icc 1 N) (fun n => centeredThetaCoefficient n q a) =
      thetaProgressionNat N q a - thetaGlobalNat N / (q.totient : Real) := by
  unfold centeredThetaCoefficient thetaProgressionNat thetaGlobalNat
  rw [Finset.sum_sub_distrib, Finset.sum_div]


theorem centeredPsiCoefficient_one (q : Nat) (a : ZMod q) :
    centeredPsiCoefficient 1 q a = 0 := by
  simp [centeredPsiCoefficient]


theorem centeredThetaCoefficient_one (q : Nat) (a : ZMod q) :
    centeredThetaCoefficient 1 q a = 0 := by
  simp [centeredThetaCoefficient]

end BombieriVinogradov.PrimeCountingConversion
end

section
namespace BombieriVinogradov.PrimeCountingConversion


theorem abs_sum_centeredPsiCoefficient_le_maximal {X : Real} {q k : Nat}
    (a : Units (ZMod q)) (hk : k <= Nat.floor X) :
    abs (Finset.sum (Finset.Icc 1 k)
      (fun n => centeredPsiCoefficient n q (a : ZMod q))) <=
      WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q := by
  let F : Units (ZMod q) -> Real := fun u =>
    iSup (fun y : Fin (Nat.floor X + 1) =>
      abs (WeightedBombieriVinogradov.psiProgression y.val q (u : ZMod q) -
        WeightedBombieriVinogradov.psiGlobal y.val / (q.totient : Real)))
  let H : Fin (Nat.floor X + 1) -> Real := fun y =>
    abs (WeightedBombieriVinogradov.psiProgression y.val q (a : ZMod q) -
      WeightedBombieriVinogradov.psiGlobal y.val / (q.totient : Real))
  let y : Fin (Nat.floor X + 1) :=
    { val := k, isLt := Nat.lt_succ_of_le hk }
  unfold WeightedBombieriVinogradov.maximalWeightedDiscrepancy
  change abs (Finset.sum (Finset.Icc 1 k)
    (fun n => centeredPsiCoefficient n q (a : ZMod q))) <= iSup F
  calc
    abs (Finset.sum (Finset.Icc 1 k)
      (fun n => centeredPsiCoefficient n q (a : ZMod q))) = H y := by
        dsimp [H, y]
        rw [sum_centeredPsiCoefficient]
    _ <= iSup H := le_ciSup (Set.finite_range H).bddAbove y
    _ = F a := by rfl
    _ <= iSup F := le_ciSup (Set.finite_range F).bddAbove a

end BombieriVinogradov.PrimeCountingConversion
end

open Finset ArithmeticFunction BombieriVinogradov BombieriVinogradov.WeightedBombieriVinogradov

theorem OMA.solution : OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1.H1 := by
  classical
  intro x Q hx
  refine ⟨maximalWeightedDiscrepancy x, ?_, ?_⟩
  · intro q _ a t ht
    have he := PrimeCountingConversion.abs_sum_centeredPsiCoefficient_le_maximal (X := (x:ℝ)) a
      (show t ≤ ⌊(x:ℝ)⌋₊ by simpa using ht)
    have ee : (∑ n ∈ Icc 1 t, ((if (n : ZMod q) = (a : ZMod q) then (1:ℝ) else 0)
        - 1/q.totient) * (Λ n : ℝ)) =
        ∑ n ∈ Icc 1 t, PrimeCountingConversion.centeredPsiCoefficient n q a := by
      apply sum_congr rfl
      intro n hn
      unfold PrimeCountingConversion.centeredPsiCoefficient
      by_cases h : (n : ZMod q) = (a : ZMod q)
      · simp [h,sub_mul,div_eq_mul_inv,mul_comm]
      · simp [h,Ne.symm h,div_eq_mul_inv,mul_comm]
    simpa only [ee] using he
  · have hx' : (2:ℝ) ≤ x := by exact_mod_cast hx.le
    simpa only [averageWeightedDiscrepancy,primitiveConductorMean,nonprincipalPrimitiveMaximalSum,
      LargeSieve.primitiveCharacters,VaughanMeanValue.maximalPsiNorm,VaughanMeanValue.psiCharacterSum,
      Nat.floor_natCast] using averageWeightedDiscrepancy_le_primitiveConductorMean Q hx'

