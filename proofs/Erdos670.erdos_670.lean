import FormalConjectures.ErdosProblems.«670»
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
A fixed-dimensional counterexample to the separated-distances conjecture.

John Tripodo's Lean 4 formalization is reproduced from
https://github.com/jjtripodo-lgtm/erdos-670-r29/tree/6d629227b1e8d21ab9f09d8a3a667015e78e468a .
The source modules are combined and the final statement uses the repository's pinned definition.
-/

/-
MIT License

Copyright (c) 2026 John Tripodo

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

-- From MatrixCertificates.lean
noncomputable section

open scoped Matrix BigOperators
namespace Erdos670R29

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_infinity : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(154907868127150589 / 1923304880250000 : ℝ), (1696688651775479 / 25644065070000 : ℝ), (125479651378551811 / 1923304880250000 : ℝ), (-855013526827973 / 80137703343750 : ℝ), (23678332272023071 / 384660976050000 : ℝ);
    (1696688651775479 / 25644065070000 : ℝ), (60360400398257 / 657540130000 : ℝ), (123342327356291711 / 1282203253500000 : ℝ), (-103654360977957 / 5342513556250 : ℝ), (1382104386128603 / 25644065070000 : ℝ);
    (125479651378551811 / 1923304880250000 : ℝ), (123342327356291711 / 1282203253500000 : ℝ), (65529018175226903 / 641101626750000 : ℝ), (-6486353065612211 / 240413110031250 : ℝ), (18316487478235019 / 384660976050000 : ℝ);
    (-855013526827973 / 80137703343750 : ℝ), (-103654360977957 / 5342513556250 : ℝ), (-6486353065612211 / 240413110031250 : ℝ), (18566550141185716 / 120206555015625 : ℝ), (33932098089378769 / 769321952100000 : ℝ);
    (23678332272023071 / 384660976050000 : ℝ), (1382104386128603 / 25644065070000 : ℝ), (18316487478235019 / 384660976050000 : ℝ), (33932098089378769 / 769321952100000 : ℝ), (2231708054059801 / 15386439042000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_infinity_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (127251648883160925 / 154907868127150589 : ℝ), 1, 0, 0, 0;
    (11407241034413801 / 14082533466104599 : ℝ), (940189106051962783726244985260481 / 826418379305755437956618593630400 : ℝ), 1, 0, 0;
    (-20520324643871352 / 154907868127150589 : ℝ), (-4401708670379836325207292598169 / 15495344611982914461686598630570 : ℝ), (-19823264814784431790740600874691621189601491918560 / 2857769742550140136253930920634931306700264567177 : ℝ), 1, 0;
    (118391661360115355 / 154907868127150589 : ℝ), (734725316100714292495683378729 / 8264183793057554379566185936304 : ℝ), (-19177189492590380806528344572703713557366728500700 / 2857769742550140136253930920634931306700264567177 : ℝ), (1921252513749450223033767133331831316902219064182260320967130125 / 18055884486521964222273206776163857603931042197563329670022013952 : ℝ), 1]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_infinity_D : Fin 5 → ℝ := ![(154907868127150589 / 1923304880250000 : ℝ), (3099068922396582892337319726114 / 82759738543908932041767213125 : ℝ), (2857769742550140136253930920634931306700264567177 / 3178909004094110081469881257834479769519200000000 : ℝ), (4822618719690695572188356510727526069426026227981658565711008 / 45170631923713597997851621407820009950691390253268228678125 : ℝ), (11969803639470114375654033899666963971150011319277788530276681095214814201858963 / 213704435385587440846239719024081948943425507957182994540264378823478087680000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_infinity_factor :
    completion_infinity_L * Matrix.diagonal completion_infinity_D * completion_infinity_Lᵀ = completion_infinity := by
  ext i j
  change (∑ k : Fin 5, (completion_infinity_L * Matrix.diagonal completion_infinity_D) i k *
    completion_infinity_L j k) = completion_infinity i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [completion_infinity, completion_infinity_L, completion_infinity_D, Fin.sum_univ_succ]


set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_infinity_posDef : completion_infinity.PosDef := by
  have htri : completion_infinity_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [completion_infinity_L] at *
  have hdet : completion_infinity_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [completion_infinity_L, Fin.prod_univ_succ]
  have hunit : IsUnit completion_infinity_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal completion_infinity_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [completion_infinity_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, completion_infinity_factor] at h
  exact h



set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_k0 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(1394026811024556049 / 17309743922250000 : ℝ), (46328598787702541 / 692389756890000 : ℝ), (381882790308755381 / 5769914640750000 : ℝ), (-9863605491658714 / 1081858995140625 : ℝ), (1092251527626516371 / 17309743922250000 : ℝ);
    (46328598787702541 / 692389756890000 : ℝ), (124223500469139577 / 1331518763250000 : ℝ), (9099428306584243 / 92318634252000 : ℝ), (-68639378160196897 / 4327435980562500 : ℝ), (110547438593911493 / 1923304880250000 : ℝ);
    (381882790308755381 / 5769914640750000 : ℝ), (9099428306584243 / 92318634252000 : ℝ), (1825298239967760569 / 17309743922250000 : ℝ), (-46808311449577981 / 2163717990281250 : ℝ), (306177224272754669 / 5769914640750000 : ℝ);
    (-9863605491658714 / 1081858995140625 : ℝ), (-68639378160196897 / 4327435980562500 : ℝ), (-46808311449577981 / 2163717990281250 : ℝ), (175152359377665304 / 1081858995140625 : ℝ), (1830238021736459117 / 34619487844500000 : ℝ);
    (1092251527626516371 / 17309743922250000 : ℝ), (110547438593911493 / 1923304880250000 : ℝ), (306177224272754669 / 5769914640750000 : ℝ), (1830238021736459117 / 34619487844500000 : ℝ), (894977181933524927 / 5769914640750000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_k0_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (1158214969692563525 / 1394026811024556049 : ℝ), 1, 0, 0, 0;
    (1145648370926266143 / 1394026811024556049 : ℝ), (701001149239642661585311528660832325 / 606506437835320855794175275045360616 : ℝ), 1, 0, 0;
    (-157817687866539424 / 1394026811024556049 : ℝ), (-49988431305044237060027259593152553 / 227439914188245320922815728142010231 : ℝ), (-95808687642163620578013701553598383430821956996062360 / 14511543996807096861690871210606487595401269863065701 : ℝ), 1, 0;
    (1092251527626516371 / 1394026811024556049 : ℝ), (60946384821714233961183041071986319 / 454879828376490641845631456284020462 : ℝ), (-97249975348567947158845090161863269255545192027701580 / 14511543996807096861690871210606487595401269863065701 : ℝ), (3540868483579262142574972748292894248293979898053213181968089309757551 / 14946270143939288956934877871713144894543430749669055765832500920369152 : ℝ), 1]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def completion_k0_D : Fin 5 → ℝ := ![(1394026811024556049 / 17309743922250000 : ℝ), (75813304729415106974271909380670077 / 2010853926632154863723518599187500 : ℝ), (14511543996807096861690871210606487595401269863065701 / 20996942252250885259923788328335306031731032212000000 : ℝ), (35928533999854059992631917960848905996498631609781384052481973366272 / 278688362242450205222619016415794913155603344743491428591552234375 : ℝ), (295064111565677587494222415859176640559512433739282003640599757740230038816292365092873 / 4422497586057431447782735798785173077500115685602524773359238496032093334331392000000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_k0_factor :
    completion_k0_L * Matrix.diagonal completion_k0_D * completion_k0_Lᵀ = completion_k0 := by
  ext i j
  change (∑ k : Fin 5, (completion_k0_L * Matrix.diagonal completion_k0_D) i k *
    completion_k0_L j k) = completion_k0 i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [completion_k0, completion_k0_L, completion_k0_D, Fin.sum_univ_succ]


set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem completion_k0_posDef : completion_k0.PosDef := by
  have htri : completion_k0_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [completion_k0_L] at *
  have hdet : completion_k0_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [completion_k0_L, Fin.prod_univ_succ]
  have hunit : IsUnit completion_k0_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal completion_k0_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [completion_k0_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, completion_k0_factor] at h
  exact h



set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def coarseGram : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(40846909 / 250000 : ℝ), (1576997 / 10000 : ℝ), (41367491 / 250000 : ℝ), (3749361 / 31250 : ℝ), (9827551 / 50000 : ℝ);
    (1576997 / 10000 : ℝ), (2673189 / 10000 : ℝ), (144778173 / 500000 : ℝ), (1528947 / 6250 : ℝ), (3186129 / 10000 : ℝ);
    (41367491 / 250000 : ℝ), (144778173 / 500000 : ℝ), (95402629 / 250000 : ℝ), (11540109 / 31250 : ℝ), (22033739 / 50000 : ℝ);
    (3749361 / 31250 : ℝ), (1528947 / 6250 : ℝ), (11540109 / 31250 : ℝ), (13487796 / 15625 : ℝ), (74121489 / 100000 : ℝ);
    (9827551 / 50000 : ℝ), (3186129 / 10000 : ℝ), (22033739 / 50000 : ℝ), (74121489 / 100000 : ℝ), (1884761 / 2000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def coarseGram_L : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
    (39424925 / 40846909 : ℝ), 1, 0, 0, 0;
    (41367491 / 40846909 : ℝ), (2651920397490907 / 2350925968628800 : ℝ), 1, 0, 0;
    (29994888 / 40846909 : ℝ), (16444551865119 / 14693287303930 : ℝ), (17204047980065279905440 / 11344946112641979397877 : ℝ), 1, 0;
    (49137755 / 40846909 : ℝ), (26326714551763 / 23509259686288 : ℝ), (113091931577409573265100 / 79414622788493855785139 : ℝ), (115989202024860860556311618375 / 179843218143509606247601277952 : ℝ), 1]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
def coarseGram_D : Fin 5 → ℝ := ![(40846909 / 250000 : ℝ), (2938657460786 / 25529318125 : ℝ), (79414622788493855785139 / 1175462984314400000000 : ℝ), (16860301700954025585712619808 / 35452956602006185618365625 : ℝ), (271870469926137074239387919119179863 / 1198954787623397374984008519680000 : ℝ)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem coarseGram_factor :
    coarseGram_L * Matrix.diagonal coarseGram_D * coarseGram_Lᵀ = coarseGram := by
  ext i j
  change (∑ k : Fin 5, (coarseGram_L * Matrix.diagonal coarseGram_D) i k *
    coarseGram_L j k) = coarseGram i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [coarseGram, coarseGram_L, coarseGram_D, Fin.sum_univ_succ]


set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem coarseGram_posDef : coarseGram.PosDef := by
  have htri : coarseGram_L.IsLowerTriangular := by
    intro i j h
    change i < j at h
    fin_cases i <;> fin_cases j <;> norm_num [coarseGram_L] at *
  have hdet : coarseGram_L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    norm_num [coarseGram_L, Fin.prod_univ_succ]
  have hunit : IsUnit coarseGram_L := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdet]
    exact isUnit_one
  have hdiag : (Matrix.diagonal coarseGram_D).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [coarseGram_D]
  have h := hdiag.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, coarseGram_factor] at h
  exact h



end Erdos670R29

end

-- From MatrixInterpolation.lean
section

open scoped Matrix BigOperators
namespace Erdos670R29

lemma gram_affine_identity {ι κ : Type*} [Fintype κ]
    (X Y : Matrix ι κ ℝ) (t : ℝ) :
    ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ =
      (1-t) • (X*Xᵀ) + t • (Y*Yᵀ) - (t*(1-t)) • ((Y-X)*(Y-X)ᵀ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Whole-matrix endpoint certificates control every point of the affine segment. -/
theorem completion_interpolation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℝ) (X Y : Matrix ι κ ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hX : (B-X*Xᵀ).PosSemidef) (hY : (B-Y*Yᵀ).PosSemidef) :
    (B - ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ).PosSemidef := by
  have hG : ((Y-X)*(Y-X)ᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (Y-X)
  have h := ((hX.smul (sub_nonneg.mpr ht1)).add (hY.smul ht0)).add
    (hG.smul (mul_nonneg ht0 (sub_nonneg.mpr ht1)))
  have heq : B - ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ =
      (1-t) • (B-X*Xᵀ) + t • (B-Y*Yᵀ) + (t*(1-t)) • ((Y-X)*(Y-X)ᵀ) := by
    rw [gram_affine_identity]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact h


end Erdos670R29

end

-- From SourceMatrices.lean
noncomputable section

open scoped Matrix BigOperators

namespace Erdos670R29

set_option maxHeartbeats 3000000 in
def labels : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,3,5,7,14,15; 3,0,2,4,13,12; 5,2,0,1,11,10;
     7,4,1,0,9,8; 14,13,11,9,0,6; 15,12,10,8,6,0]
set_option maxHeartbeats 3000000 in
def sourceD (A B : Fin 6) : ℝ :=
  if A = B then 0 else 457/25 + (569/500)*labels A B
set_option maxHeartbeats 3000000 in
def sourceE (A B : Fin 6) : ℝ :=
  if A = B then 0 else (sourceD A B)^2 - 2*((507/100)^2+(1131/100)^2)
set_option maxHeartbeats 3000000 in
def sourceMacro : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (sourceE 0 i.succ + sourceE 0 j.succ - sourceE i.succ j.succ)/2
set_option maxHeartbeats 3000000 in
def PG (A B : Fin 6) : ℝ := if A.val < B.val then sourceD A B else 0
set_option maxHeartbeats 3000000 in
def PF (A B : Fin 6) : ℝ := sourceD A B - PG A B
set_option maxHeartbeats 3000000 in
def TG : Matrix (Fin 5) (Fin 6) ℝ := fun j A => PG A 0 - PG A j.succ
set_option maxHeartbeats 3000000 in
def TF : Matrix (Fin 5) (Fin 6) ℝ := fun j A => PF A 0 - PF A j.succ
set_option maxHeartbeats 3000000 in
def normalizedDirections (x : ℝ) : Matrix (Fin 5) (Fin 6) ℝ :=
  ((519/1000 : ℝ)*(507/100))⁻¹ • ((138/125 : ℝ) • TG + ((533/500)*x) • TF)
set_option maxHeartbeats 3000000 in
def sourceCompletion (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  sourceMacro - normalizedDirections x * (normalizedDirections x)ᵀ

set_option maxHeartbeats 3000000 in
theorem sourceMacro_eq : sourceMacro = coarseGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.succ, sourceMacro, sourceE, sourceD, labels, coarseGram]

set_option maxHeartbeats 3000000 in
theorem TG_entries : TG = !![(-10847/500 : ℝ), 0, 0, 0, 0, 0;
    (-2397/100 : ℝ), (-5139/250 : ℝ), 0, 0, 0, 0;
    (-13123/500 : ℝ), (-2854/125 : ℝ), (-9709/500 : ℝ), 0, 0, 0;
    (-8553/250 : ℝ), (-16537/500 : ℝ), (-15399/500 : ℝ), (-14261/500 : ℝ), 0, 0;
    (-707/20 : ℝ), (-3992/125 : ℝ), (-1483/50 : ℝ), (-3423/125 : ℝ), (-6277/250 : ℝ), 0] := by
  ext j A
  fin_cases j <;> fin_cases A <;>
    norm_num [Fin.succ, TG, PG, PF, sourceD, labels]

set_option maxHeartbeats 3000000 in
theorem TF_entries : TF = !![0, (10847/500 : ℝ), (1707/500 : ℝ), (1707/500 : ℝ), (569/500 : ℝ), (1707/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (1707/250 : ℝ), (1707/500 : ℝ), (569/100 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (569/100 : ℝ), (3983/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (8553/250 : ℝ), (5121/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (8553/250 : ℝ), (707/20 : ℝ)] := by
  ext j A
  fin_cases j <;> fin_cases A <;>
    norm_num [Fin.succ, TF, PG, PF, sourceD, labels]

set_option maxHeartbeats 3000000 in
theorem sourceCompletion_zero : sourceCompletion 0 = completion_infinity := by
  ext i j
  change sourceMacro i j - (∑ k : Fin 6,
    normalizedDirections 0 i k * normalizedDirections 0 j k) = completion_infinity i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceCompletion, sourceMacro_eq, coarseGram,
      normalizedDirections, TG_entries, TF_entries, completion_infinity,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 3000000 in
theorem sourceCompletion_endpoint : sourceCompletion (1/100) = completion_k0 := by
  ext i j
  change sourceMacro i j - (∑ k : Fin 6,
    normalizedDirections (1/100) i k * normalizedDirections (1/100) j k) = completion_k0 i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceCompletion, sourceMacro_eq, coarseGram,
      normalizedDirections, TG_entries, TF_entries, completion_k0,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.sum_univ_succ]

set_option maxHeartbeats 3000000 in
theorem sourceMacro_posDef : sourceMacro.PosDef := by
  rw [sourceMacro_eq]
  exact coarseGram_posDef

set_option maxHeartbeats 3000000 in
/-- The full actual source matrix budget holds throughout the finite-k interval. -/
theorem sourceCompletion_posSemidef (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/100) :
    (sourceCompletion x).PosSemidef := by
  have h0 : (sourceCompletion 0).PosSemidef := by
    rw [sourceCompletion_zero]
    exact completion_infinity_posDef.posSemidef
  have h1 : (sourceCompletion (1/100)).PosSemidef := by
    rw [sourceCompletion_endpoint]
    exact completion_k0_posDef.posSemidef
  have heq : (1-100*x) • normalizedDirections 0 +
      (100*x) • normalizedDirections (1/100) = normalizedDirections x := by
    ext i j
    simp only [normalizedDirections, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h := completion_interpolation sourceMacro (normalizedDirections 0)
    (normalizedDirections (1/100)) (100*x) (by positivity) (by linarith) h0 h1
  rw [heq] at h
  exact h



end Erdos670R29

end

-- From SchurTransfer.lean
section

open scoped Matrix
namespace Erdos670R29

/-- The certified five-row budget is equivalent to the six-column residual budget. -/
theorem schur_transfer {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (T : Matrix ι κ ℝ) (hB : B.PosDef)
    (h : (B-T*Tᵀ).PosSemidef) :
    ((1 : Matrix κ κ ℝ)-Tᵀ*B⁻¹*T).PosSemidef := by
  letI := hB.isUnit.invertible
  letI : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  have hblock : (Matrix.fromBlocks B T Tᴴ (1 : Matrix κ κ ℝ)).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ B T Matrix.PosDef.one).2
    simpa only [inv_one, Matrix.mul_one,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hresult := (Matrix.PosDef.fromBlocks₁₁ T (1 : Matrix κ κ ℝ) hB).1 hblock
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hresult


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.GlobalCompletion.lean
section

/-! A source-pinned kernel for the three-active-group Gram completion used in
JRL PR 2974. This module does not assert the construction's analytic bounds or
its final fixed-dimensional configuration theorem. -/

open scoped BigOperators Matrix
open Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma square_sum_three_le (a b c : ℝ) :
    (a + b + c)^2 ≤ 3 * a^2 + 3 * b^2 + 3 * c^2 := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

/-- A whole-matrix completion from three quadratic group budgets. In particular,
the hypotheses must bound each entire group, not each column independently. -/
theorem three_group_completion
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B C : Matrix ι κ ℝ) (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian)
    (hbudget : ∀ x : κ → ℝ,
      3 * ∑ i, (A *ᵥ x) i ^ 2 +
      3 * ∑ i, (B *ᵥ x) i ^ 2 +
      3 * ∑ i, (C *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D *ᵥ x)) :
    (D - (A + B + C)ᵀ * (A + B + C)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact hD.sub (by simpa using Matrix.isHermitian_conjTranspose_mul_self (A+B+C))
  intro x
  have hsum : (∑ i, ((A+B+C) *ᵥ x) i ^ 2) ≤
      3 * ∑ i, (A *ᵥ x) i ^ 2 +
      3 * ∑ i, (B *ᵥ x) i ^ 2 +
      3 * ∑ i, (C *ᵥ x) i ^ 2 := by
    simp only [Matrix.add_mulVec, Pi.add_apply]
    calc
      _ ≤ ∑ i, (3 * (A *ᵥ x) i ^ 2 + 3 * (B *ᵥ x) i ^ 2 +
          3 * (C *ᵥ x) i ^ 2) := Finset.sum_le_sum fun i _ => square_sum_three_le _ _ _
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hgram : x ⬝ᵥ (((A+B+C)ᵀ * (A+B+C)) *ᵥ x) =
      ∑ i, ((A+B+C) *ᵥ x) i ^ 2 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [Matrix.vecMul_transpose]
    simp only [dotProduct, pow_two]
  simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hgram, sub_nonneg] using
    hsum.trans (hbudget x)

/-- The block-diagonal budget may be verified separately for the three groups. -/
theorem three_group_completion_of_separate_budgets
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B C : Matrix ι κ ℝ) (D₀ D₁ D₂ : Matrix κ κ ℝ)
    (h₀ : D₀.IsHermitian) (h₁ : D₁.IsHermitian) (h₂ : D₂.IsHermitian)
    (b₀ : ∀ x : κ → ℝ, 3 * ∑ i, (A *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D₀ *ᵥ x))
    (b₁ : ∀ x : κ → ℝ, 3 * ∑ i, (B *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D₁ *ᵥ x))
    (b₂ : ∀ x : κ → ℝ, 3 * ∑ i, (C *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D₂ *ᵥ x)) :
    (D₀ + D₁ + D₂ - (A+B+C)ᵀ * (A+B+C)).PosSemidef := by
  apply three_group_completion A B C (D₀+D₁+D₂) ((h₀.add h₁).add h₂)
  intro x
  simpa only [Matrix.add_mulVec, dotProduct_add] using add_le_add (add_le_add (b₀ x) (b₁ x)) (b₂ x)

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletionFactor.lean
section

/-! A fixed-coordinate-count PSD residual factor, for the global completion.
Unlike an existential finite-dimensional Gram realization, this does not hide
an unbounded auxiliary dimension. -/

open scoped BigOperators Matrix MatrixOrder
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Every real PSD matrix has a Gram factor with exactly the same index type. -/
theorem psd_same_size_gram_factor {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Q : Matrix κ κ ℝ) (hQ : Q.PosSemidef) :
    ∃ V : Matrix κ κ ℝ, Vᵀ * V = Q := by
  refine ⟨CFC.sqrt Q, ?_⟩
  have hs := (CFC.sqrt_nonneg Q).isSelfAdjoint
  have hstar : (CFC.sqrt Q)ᵀ = CFC.sqrt Q := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hs.star_eq
  rw [hstar, ← pow_two]
  exact CFC.sq_sqrt Q hQ.nonneg

/-- The residual occupies κ coordinates; the original output occupies ι.
The factor has no additional dimension depending on the number of points. -/
theorem three_group_completion_factor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B C : Matrix ι κ ℝ) (D : Matrix κ κ ℝ)
    (hD : D.IsHermitian)
    (hbudget : ∀ x : κ → ℝ,
      3 * ∑ i, (A *ᵥ x) i ^ 2 +
      3 * ∑ i, (B *ᵥ x) i ^ 2 +
      3 * ∑ i, (C *ᵥ x) i ^ 2 ≤ x ⬝ᵥ (D *ᵥ x)) :
    ∃ V : Matrix κ κ ℝ, (A+B+C)ᵀ*(A+B+C) + Vᵀ*V = D := by
  obtain ⟨V, hV⟩ := psd_same_size_gram_factor _
    (three_group_completion A B C D hD hbudget)
  refine ⟨V, ?_⟩
  rw [hV]
  abel

/-- Exact cancellation of the combined macro and residual inner products. -/
theorem completed_bilinear_identity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (V D : Matrix κ κ ℝ)
    (hfactor : Mᵀ*M + Vᵀ*V = D) (x y : κ → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ y) + (V *ᵥ x) ⬝ᵥ (V *ᵥ y) =
      x ⬝ᵥ (D *ᵥ y) := by
  rw [← hfactor, Matrix.add_mulVec, dotProduct_add]
  congr 1 <;> rw [← Matrix.mulVec_mulVec] <;> symm <;>
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From GramCompletion.lean
section

open scoped Matrix BigOperators
namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- A whole-matrix certificate constructs one shared macro/direction/residual family. -/
theorem gram_completion {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (T : Matrix ι κ ℝ) (hB : B.PosDef)
    (hbudget : (B-T*Tᵀ).PosSemidef) :
    ∃ Q : Matrix ι ι ℝ, ∃ U : Matrix ι κ ℝ, ∃ W : Matrix κ κ ℝ,
      Qᵀ*Q = B ∧ Qᵀ*U = T ∧ Uᵀ*U + Wᵀ*W = 1 := by
  obtain ⟨Q, hQ⟩ := psd_same_size_gram_factor B hB.posSemidef
  let U := Q*(B⁻¹*T)
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 hB.isUnit
  have hproj : Qᵀ*U = T := by
    dsimp [U]
    rw [← Matrix.mul_assoc, hQ, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv B hdet, Matrix.one_mul]
  have hBinv : (B⁻¹)ᵀ = B⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.inv.eq
  have hU : Uᵀ*U = Tᵀ*B⁻¹*T := by
    calc
      Uᵀ*U = (B⁻¹*T)ᵀ*(Qᵀ*U) := by
        change (Q*(B⁻¹*T))ᵀ*U = _
        rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Tᵀ*B⁻¹*T := by
        rw [hproj, Matrix.transpose_mul, hBinv]
  have hres : ((1 : Matrix κ κ ℝ)-Uᵀ*U).PosSemidef := by
    rw [hU]
    exact schur_transfer B T hB hbudget
  obtain ⟨W, hW⟩ := psd_same_size_gram_factor _ hres
  refine ⟨Q, U, W, hQ, hproj, ?_⟩
  rw [hW]
  abel


end Erdos670R29

end

-- From FiniteKCompletion.lean
section

open scoped Matrix BigOperators
namespace Erdos670R29

lemma scale_factor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (h : Uᵀ*U + Wᵀ*W = 1) :
    (R • U)ᵀ*(R • U) + (R • W)ᵀ*(R • W) = Matrix.diagonal (fun _ => R^2) := by
  ext i j
  have hc := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hc
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  have hU : (∑ k, (R*U k i)*(R*U k j)) = R^2*(∑ k, U k i*U k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hW : (∑ k, (R*W k i)*(R*W k j)) = R^2*(∑ k, W k i*W k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hU, hW, ← mul_add, hc]
  by_cases hij : i=j <;> simp [hij]

/-- For every finite k≥100 one shared five-dimensional macro factor and six
completed directions realize the literal source potentials and radius budget. -/
theorem finite_k_completion (k : ℝ) (hk : 100 ≤ k) :
    ∃ Q : Matrix (Fin 5) (Fin 5) ℝ,
    ∃ U : Matrix (Fin 5) (Fin 6) ℝ,
    ∃ W : Matrix (Fin 6) (Fin 6) ℝ,
      Qᵀ*Q = sourceMacro ∧
      Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF) ∧
      Uᵀ*U + Wᵀ*W = Matrix.diagonal (fun _ => ((507/100 : ℝ)*k^2)^2) := by
  have hk0 : 0 < k := by linarith
  have hrec : (1/k : ℝ) ≤ 1/100 := one_div_le_one_div_of_le (by norm_num) hk
  obtain ⟨Q,U,W,hQ,hproj,hfactor⟩ := gram_completion sourceMacro
    (normalizedDirections (1/k)) sourceMacro_posDef
    (sourceCompletion_posSemidef (1/k) (by positivity) hrec)
  let R : ℝ := (507/100)*k^2
  refine ⟨Q,R • U,R • W,hQ,?_,scale_factor U W R hfactor⟩
  have hscale : Qᵀ*(R • U) = R • normalizedDirections (1/k) := by
    calc
      Qᵀ*(R • U) = R • (Qᵀ*U) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [hproj]
  rw [hscale]
  ext i j
  simp only [normalizedDirections, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, R]
  field_simp
  <;> ring


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.Defs.lean
section

/-!
Definitions for the unrestricted-dimensional separated Euclidean distance problem.

The development uses an explicit construction surface first.  `Separated` records
unit separation between distances belonging to distinct unordered pairs; the
increment Gram construction is developed in later modules.
-/

namespace Erdos488.Geometry.SeparatedDistances

open scoped BigOperators

/-- The colexicographic edge label, indexed by the smaller and larger endpoints. -/
def colexLabel (i j : ℕ) : ℕ := Nat.choose j 2 + i + 1

/-- The gap-seeded/colex hybrid label used in the square-root-log construction. -/
def hybridLabel (r i j : ℕ) : ℕ :=
  if j < r then
    let δ := j - i
    (δ - 1) * r - δ * (δ - 1) / 2 + i + 1
  else
    colexLabel i j

/-- Squared-distance data on a finite vertex type. -/
abbrev SqDistanceData (ι : Type*) := Matrix ι ι ℝ

/-- Finite-difference increment Gram matrix based at consecutive vertices. -/
noncomputable def incrementGram {n : ℕ} (D : SqDistanceData (Fin (n + 1))) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    -(1 / 2 : ℝ) *
      (D i.succ j.succ - D i.succ j.castSucc - D i.castSucc j.succ + D i.castSucc j.castSucc)

/-- Unit separation of all distances attached to distinct unordered pairs. -/
def PairwiseDistanceSeparated {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Prop :=
  ∀ ⦃i j k l : ι⦄, ({i, j} : Set ι) ≠ {k, l} →
    1 ≤ |dist (p i) (p j) - dist (p k) (p l)|

/-- An unordered pair of distinct vertices. -/
abbrev Edge (ι : Type*) := {e : Sym2 ι // ¬e.IsDiag}

/-- Distance attached to an unordered pair. -/
noncomputable def edgeDistance {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Sym2 ι → ℝ :=
  Sym2.lift ⟨fun i j => dist (p i) (p j), fun i j => dist_comm _ _⟩

/-- Publication-facing unit-separation condition on the unordered edge set. -/
def SeparatedConfiguration {ι E : Type*} [PseudoMetricSpace E]
    (p : ι → E) : Prop :=
  ∀ e f : Edge ι, e ≠ f →
    1 ≤ |edgeDistance p e.1 - edgeDistance p f.1|

/-- The finite set of distances belonging to distinct unordered pairs. -/
noncomputable def edgeDistances {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [PseudoMetricSpace E] (p : ι → E) : Finset ℝ :=
  Finset.univ.image (fun e : Edge ι => edgeDistance p e.1)

end Erdos488.Geometry.SeparatedDistances

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.TrigonometricChord.lean
section

/-! Actual trigonometric circle identities and uniform chord lower slope.
These provide analytic inputs, not an assumed final Euclidean configuration. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def circleChord (R d : ℝ) : ℝ := 2*R*Real.sin (d/(2*R))

/-- The squared coordinate distance on a unit circle is the half-angle chord square. -/
theorem unit_circle_chord_square (x y : ℝ) :
    (Real.cos x-Real.cos y)^2+(Real.sin x-Real.sin y)^2 =
      (2*Real.sin ((x-y)/2))^2 := by
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  have hh := Real.sin_sq_eq_half_sub ((x-y)/2)
  have hc := Real.cos_sub x y
  rw [show 2*((x-y)/2)=x-y by ring] at hh
  nlinarith

/-- Exact coordinate identity for a radius-R private circle. -/
theorem circle_chord_coordinate_square (R x y : ℝ) (hR : R ≠ 0) :
    (R*Real.cos (x/R)-R*Real.cos (y/R))^2+
      (R*Real.sin (x/R)-R*Real.sin (y/R))^2 = (circleChord R (x-y))^2 := by
  have h := unit_circle_chord_square (x/R) (y/R)
  have he : (x/R-y/R)/2=(x-y)/(2*R) := by field_simp
  rw [he] at h
  dsimp [circleChord]
  have hm := congrArg (fun z : ℝ => R^2*z) h
  nlinarith only [hm]

/-- The derivative of the actual scaled circle chord. -/
theorem hasDerivAt_circleChord (R d : ℝ) (hR : R ≠ 0) :
    HasDerivAt (circleChord R) (Real.cos (d/(2*R))) d := by
  have h := (((hasDerivAt_id d).div_const (2*R)).sin).const_mul (2*R)
  have he : 2*R*(Real.cos (d/(2*R))*(1/(2*R)))=Real.cos (d/(2*R)) := by
    field_simp
  convert h using 1 <;> first | rfl | exact he.symm

/-- Uniform lower slope on the full ruler interval, not merely at sampled points. -/
theorem circleChord_lower_difference (R Y x y : ℝ) (hR : 0 < R)
    (hangle : Y/(2*R) ≤ Real.pi) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    Real.cos (Y/(2*R))*(y-x) ≤ circleChord R y-circleChord R x := by
  have hd (z : ℝ) := hasDerivAt_circleChord R z hR.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx, hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  rw [(hd z).deriv]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (div_nonneg hz'.1 (by positivity)) hangle
    ((div_le_div_iff_of_pos_right (by positivity)).2 hz'.2)

/-- In particular every ruler chord has a certified positive linear lower bound. -/
theorem circleChord_lower (R Y d : ℝ) (hR : 0 < R)
    (hangle : Y/(2*R) ≤ Real.pi) (hd : 0 ≤ d) (hdY : d ≤ Y) :
    Real.cos (Y/(2*R))*d ≤ circleChord R d := by
  have h := circleChord_lower_difference R Y 0 d hR hangle (by norm_num) hd hdY
  simpa [circleChord] using h

/-- A circle chord never exceeds its nonnegative arc length. -/
theorem circleChord_le_arc (R d : ℝ) (hR : 0 < R) (hd : 0 ≤ d) :
    circleChord R d ≤ d := by
  have h := Real.sin_le (show 0 ≤ d/(2*R) by positivity)
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*R by positivity)
  have he : 2*R*(d/(2*R))=d := by field_simp
  simpa [circleChord,he] using hmul

/-- Algebraic replacement for differentiating the full square-root length.
The feature energy may increase between endpoints. This is essential for
comparisons between different lag classes. -/
theorem augmented_length_lower_gap (C₀ C₁ Q₀ Q₁ D₀ D₁ K : ℝ)
    (hC₀ : 0 < C₀) (hC : C₀ ≤ C₁) (hQ : Q₀ ≤ Q₁)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hK : 0 < K)
    (hsq₀ : D₀^2=C₀^2+Q₀) (hsq₁ : D₁^2=C₁^2+Q₁)
    (hcone₀ : D₀ ≤ K*C₀) (hcone₁ : D₁ ≤ K*C₁) :
    (C₁-C₀)/K ≤ D₁-D₀ := by
  have hmono : 0 ≤ D₁-D₀ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left
    (show D₁+D₀ ≤ K*(C₁+C₀) by nlinarith) hmono
  have hsqgap : (C₁-C₀)*(C₁+C₀) ≤ (D₁-D₀)*(D₁+D₀) := by nlinarith
  have hcancel : C₁-C₀ ≤ K*(D₁-D₀) :=
    (mul_le_mul_iff_of_pos_right (show 0 < C₁+C₀ by linarith)).1 (by nlinarith [hmul])
  apply (div_le_iff₀ hK).2
  nlinarith

/-- A quadratic feature-to-chord bound gives the exact cone constant. -/
theorem augmented_length_cone (C Q D q : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsq : D^2=C^2+Q) (hQ : Q ≤ q^2*C^2) :
    D ≤ Real.sqrt (1+q^2)*C := by
  have hs : Real.sqrt (1+q^2)^2=1+q^2 := Real.sq_sqrt (by positivity)
  have hp : 0 ≤ Real.sqrt (1+q^2)*C := mul_nonneg (Real.sqrt_nonneg _) hC
  have he : (Real.sqrt (1+q^2)*C)^2=(1+q^2)*C^2 := by
    rw [mul_pow,hs]
  nlinarith [sq_nonneg (D-Real.sqrt (1+q^2)*C)]

/-- Local distance lower slope, allowing a nondecreasing harmonic feature energy.
The full square identity and both cone bounds are visible hypotheses. -/
theorem local_length_lower_difference (R Y x y Q₀ Q₁ D₀ D₁ K : ℝ)
    (hR : 0 < R) (hangle : Y/(2*R) ≤ Real.pi)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y)
    (hchord : 0 < circleChord R x) (hγ : 0 ≤ Real.cos (Y/(2*R)))
    (hQ : Q₀ ≤ Q₁) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hK : 0 < K)
    (hsq₀ : D₀^2=(circleChord R x)^2+Q₀)
    (hsq₁ : D₁^2=(circleChord R y)^2+Q₁)
    (hcone₀ : D₀ ≤ K*circleChord R x) (hcone₁ : D₁ ≤ K*circleChord R y) :
    (Real.cos (Y/(2*R))/K)*(y-x) ≤ D₁-D₀ := by
  have hch := circleChord_lower_difference R Y x y hR hangle hx hxy hy
  have hmon : circleChord R x ≤ circleChord R y := by
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr hxy)]
  have h := augmented_length_lower_gap (circleChord R x) (circleChord R y)
    Q₀ Q₁ D₀ D₁ K hchord hmon hQ hD₀ hD₁ hK hsq₀ hsq₁ hcone₀ hcone₁
  have hd := div_le_div_of_nonneg_right hch hK.le
  have he : Real.cos (Y/(2*R))*(y-x)/K=(Real.cos (Y/(2*R))/K)*(y-x) := by ring
  rw [he] at hd
  exact hd.trans h

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.HarmonicLocalModel.lean
section

/-! Literal two-harmonic local distance model: feature monotonicity, cone bounds,
and uniform lower separation transfer. This is independent of the global Gram construction. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def harmonicEnergy (θ b₁ b₂ δ : ℝ) : ℝ :=
  (2*b₁*Real.sin (θ*δ/2))^2+(2*b₂*Real.sin (θ*δ))^2

noncomputable def localDistanceModel (R θ b₁ b₂ δ d : ℝ) : ℝ :=
  Real.sqrt ((circleChord R d)^2+harmonicEnergy θ b₁ b₂ δ)

theorem harmonicEnergy_nonneg (θ b₁ b₂ δ : ℝ) : 0 ≤ harmonicEnergy θ b₁ b₂ δ := by
  unfold harmonicEnergy
  positivity

/-- Increasing positive lags increase both squared harmonic features. -/
theorem harmonicEnergy_mono (θ b₁ b₂ δ ε : ℝ) (hθ : 0 ≤ θ)
    (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (hangle : θ*ε ≤ Real.pi/2) :
    harmonicEnergy θ b₁ b₂ δ ≤ harmonicEnergy θ b₁ b₂ ε := by
  have hmul : θ*δ ≤ θ*ε := mul_le_mul_of_nonneg_left hδε hθ
  have hzero : 0 ≤ θ*δ := mul_nonneg hθ hδ
  have hs₁ : Real.sin (θ*δ/2) ≤ Real.sin (θ*ε/2) :=
    Real.monotoneOn_sin ⟨by linarith [Real.pi_pos],by linarith⟩
      ⟨by linarith [Real.pi_pos],by linarith⟩ (by linarith)
  have hs₂ : Real.sin (θ*δ) ≤ Real.sin (θ*ε) :=
    Real.monotoneOn_sin ⟨by linarith [Real.pi_pos],by linarith⟩
      ⟨by linarith [Real.pi_pos],hangle⟩ hmul
  have hp₁ : 0 ≤ Real.sin (θ*δ/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hp₂ : 0 ≤ Real.sin (θ*δ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hzero (by linarith [Real.pi_pos])
  have hsq₁ := sq_le_sq₀ hp₁ (hp₁.trans hs₁) |>.2 hs₁
  have hsq₂ := sq_le_sq₀ hp₂ (hp₂.trans hs₂) |>.2 hs₂
  have hm₁ := mul_le_mul_of_nonneg_left hsq₁ (show 0 ≤ 4*b₁^2 by positivity)
  have hm₂ := mul_le_mul_of_nonneg_left hsq₂ (show 0 ≤ 4*b₂^2 by positivity)
  unfold harmonicEnergy
  nlinarith

/-- Exact global quadratic envelope for both harmonic features. -/
theorem harmonicEnergy_le_quadratic (θ b₁ b₂ δ : ℝ) :
    harmonicEnergy θ b₁ b₂ δ ≤ θ^2*(b₁^2+4*b₂^2)*δ^2 := by
  have h₁ := mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := θ*δ/2))
    (show 0 ≤ 4*b₁^2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := θ*δ))
    (show 0 ≤ 4*b₂^2 by positivity)
  unfold harmonicEnergy
  nlinarith

theorem localDistanceModel_nonneg (R θ b₁ b₂ δ d : ℝ) :
    0 ≤ localDistanceModel R θ b₁ b₂ δ d := Real.sqrt_nonneg _

theorem localDistanceModel_square (R θ b₁ b₂ δ d : ℝ) :
    (localDistanceModel R θ b₁ b₂ δ d)^2 =
      (circleChord R d)^2+harmonicEnergy θ b₁ b₂ δ := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (harmonicEnergy_nonneg _ _ _ _))

/-- A lower ruler-arc bound gives the cone ratio used by the local separation proof. -/
theorem localDistanceModel_cone (R Y θ b₁ b₂ δ d J c : ℝ)
    (hR : 0 < R) (hangle : Y/(2*R) ≤ Real.pi)
    (hγ : 0 < Real.cos (Y/(2*R))) (hδ : 0 ≤ δ) (hc : 0 < c)
    (hd : c*δ ≤ d) (hdY : d ≤ Y) (hJ : 0 ≤ J)
    (hJbound : θ^2*(b₁^2+4*b₂^2) ≤ J^2) :
    localDistanceModel R θ b₁ b₂ δ d ≤
      Real.sqrt (1+(J/(c*Real.cos (Y/(2*R))))^2)*circleChord R d := by
  have hd₀ : 0 ≤ d := le_trans (mul_nonneg hc.le hδ) hd
  have hch := circleChord_lower R Y d hR hangle hd₀ hdY
  have hC : 0 ≤ circleChord R d := le_trans (mul_nonneg hγ.le hd₀) hch
  have hbase : c*Real.cos (Y/(2*R))*δ ≤ circleChord R d := by
    have h := mul_le_mul_of_nonneg_left hd hγ.le
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hbase hJ
  have hratio : J*δ ≤ (J/(c*Real.cos (Y/(2*R))))*circleChord R d := by
    calc
      J*δ ≤ J*circleChord R d/(c*Real.cos (Y/(2*R))) :=
        (le_div_iff₀ (mul_pos hc hγ)).2 (by nlinarith)
      _ = _ := by ring
  have hQ := harmonicEnergy_le_quadratic θ b₁ b₂ δ
  have hJδ := mul_le_mul_of_nonneg_right hJbound (sq_nonneg δ)
  have hsq := sq_le_sq₀ (mul_nonneg hJ hδ)
    ((mul_nonneg hJ hδ).trans hratio) |>.2 hratio
  apply augmented_length_cone _ _ _ _ hC (localDistanceModel_nonneg _ _ _ _ _ _)
    (localDistanceModel_square _ _ _ _ _ _)
  nlinarith

/-- Uniform local-model lower gap across equal or increasing lags. -/
theorem localDistanceModel_lower_gap (R Y θ b₁ b₂ δ ε x y J c : ℝ)
    (hR : 0 < R) (hangle : Y/(2*R) ≤ Real.pi)
    (hγ : 0 < Real.cos (Y/(2*R))) (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hδε : δ ≤ ε) (hfeature : θ*ε ≤ Real.pi/2)
    (hc : 0 < c) (hx : c*δ ≤ x) (hy : c*ε ≤ y)
    (hxy : x ≤ y) (hyY : y ≤ Y) (hJ : 0 ≤ J)
    (hJbound : θ^2*(b₁^2+4*b₂^2) ≤ J^2) :
    (Real.cos (Y/(2*R))/Real.sqrt (1+(J/(c*Real.cos (Y/(2*R))))^2))*(y-x) ≤
      localDistanceModel R θ b₁ b₂ ε y-localDistanceModel R θ b₁ b₂ δ x := by
  have hx₀ : 0 < x := lt_of_lt_of_le (mul_pos hc hδ) hx
  have hch := circleChord_lower R Y x hR hangle hx₀.le (hxy.trans hyY)
  have hch₀ : 0 < circleChord R x := lt_of_lt_of_le (mul_pos hγ hx₀) hch
  exact local_length_lower_difference R Y x y
    (harmonicEnergy θ b₁ b₂ δ) (harmonicEnergy θ b₁ b₂ ε)
    (localDistanceModel R θ b₁ b₂ δ x) (localDistanceModel R θ b₁ b₂ ε y)
    (Real.sqrt (1+(J/(c*Real.cos (Y/(2*R))))^2))
    hR hangle hx₀.le hxy hyY hch₀ hγ.le
    (harmonicEnergy_mono θ b₁ b₂ δ ε hθ hδ.le hδε hfeature)
    (localDistanceModel_nonneg _ _ _ _ _ _) (localDistanceModel_nonneg _ _ _ _ _ _)
    (Real.sqrt_pos.2 (by positivity))
    (localDistanceModel_square _ _ _ _ _ _) (localDistanceModel_square _ _ _ _ _ _)
    (localDistanceModel_cone R Y θ b₁ b₂ δ x J c hR hangle hγ hδ.le hc
      hx (hxy.trans hyY) hJ hJbound)
    (localDistanceModel_cone R Y θ b₁ b₂ ε y J c hR hangle hγ (hδ.le.trans hδε) hc
      hy hyY hJ hJbound)

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.TrigonometricFeatures.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators

/-- The literal five coordinates used by the completed construction. -/
noncomputable def trigFeature (z : ℝ) : Fin 5 → ℝ :=
  ![1,Real.sin z,Real.cos z,Real.sin (2*z),Real.cos (2*z)]

/-- One exact diagonal reserve block. -/
def trigWeight (b₀ b₁ b₂ : ℝ) : Fin 5 → ℝ := ![b₀^2,b₁^2,b₁^2,b₂^2,b₂^2]

/-- The weighted feature norm is independent of the local point. -/
theorem trigFeature_constant_norm (b₀ b₁ b₂ z : ℝ) :
    (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*(trigFeature z a)^2)=b₀^2+b₁^2+b₂^2 := by
  simp only [Fin.sum_univ_succ,trigFeature,trigWeight,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero,one_pow,mul_one]
  have h₁ := congrArg (fun x : ℝ => b₁^2*x) (Real.sin_sq_add_cos_sq z)
  have h₂ := congrArg (fun x : ℝ => b₂^2*x) (Real.sin_sq_add_cos_sq (2*z))
  nlinarith only [h₁,h₂]

/-- The full weighted five-coordinate difference gives precisely two harmonics. -/
theorem trigFeature_difference_square (b₀ b₁ b₂ z w : ℝ) :
    (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*(trigFeature z a-trigFeature w a)^2)=
      (2*b₁*Real.sin ((z-w)/2))^2+(2*b₂*Real.sin (z-w))^2 := by
  have h₁ := congrArg (fun x : ℝ => b₁^2*x) (unit_circle_chord_square z w)
  have h₂ := congrArg (fun x : ℝ => b₂^2*x) (unit_circle_chord_square (2*z) (2*w))
  rw [show (2*z-2*w)/2=z-w by ring] at h₂
  simp only [Fin.sum_univ_succ,trigFeature,trigWeight,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Fin.sum_univ_zero,add_zero,sub_self]
  nlinarith only [h₁,h₂]

/-- Centering cancels from feature differences, leaving only the local lag. -/
theorem trigFeature_centered_difference (b₀ b₁ b₂ θ center i j : ℝ) :
    (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*
      (trigFeature (θ*(j-center)) a-trigFeature (θ*(i-center)) a)^2)=
      harmonicEnergy θ b₁ b₂ (j-i) := by
  rw [trigFeature_difference_square]
  have h : θ*(j-center)-θ*(i-center)=θ*(j-i) := by ring
  simp only [h,harmonicEnergy]

/-- Adding the private circle gives the literal local-model squared length. -/
theorem circle_and_feature_local_square (R b₀ b₁ b₂ θ center i j yi yj : ℝ)
    (hR : R ≠ 0) :
    (R*Real.cos (yj/R)-R*Real.cos (yi/R))^2+
      (R*Real.sin (yj/R)-R*Real.sin (yi/R))^2+
      (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*
        (trigFeature (θ*(j-center)) a-trigFeature (θ*(i-center)) a)^2)=
    (localDistanceModel R θ b₁ b₂ (j-i) (yj-yi))^2 := by
  rw [circle_chord_coordinate_square R yj yi hR,trigFeature_centered_difference,
    localDistanceModel_square]

/-- Embed a feature into its own five-coordinate macro-cluster block. -/
noncomputable def clusteredFeature {m : ℕ} (A : Fin m) (z : ℝ) : Fin m × Fin 5 → ℝ :=
  fun q => if q.1=A then trigFeature z q.2 else 0

/-- Literal block disjointness, with no orthogonality assumption. -/
theorem clusteredFeature_weighted_dot {m : ℕ} (A B : Fin m) (b₀ b₁ b₂ z w : ℝ) :
    (∑ q : Fin m × Fin 5, trigWeight b₀ b₁ b₂ q.2*
      clusteredFeature A z q*clusteredFeature B w q)=
    if A=B then ∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*trigFeature z a*trigFeature w a else 0 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ C : Fin m,
      (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*clusteredFeature A z (C,a)*
        clusteredFeature B w (C,a)) =
      if C=A then (if A=B then ∑ a : Fin 5,
        trigWeight b₀ b₁ b₂ a*trigFeature z a*trigFeature w a else 0) else 0 := by
    intro C
    by_cases hC : C=A
    · subst C
      by_cases hAB : A=B <;> simp [clusteredFeature,hAB]
    · simp [clusteredFeature,hC]
  simp_rw [he]
  simp

/-- Constant feature reserve survives embedding in the full 5m-coordinate space. -/
theorem clusteredFeature_constant_norm {m : ℕ} (A : Fin m) (b₀ b₁ b₂ z : ℝ) :
    (∑ q : Fin m × Fin 5, trigWeight b₀ b₁ b₂ q.2*(clusteredFeature A z q)^2)=
      b₀^2+b₁^2+b₂^2 := by
  have h := clusteredFeature_weighted_dot A A b₀ b₁ b₂ z z
  simp only [if_pos rfl] at h
  simp_rw [mul_assoc,← sq] at h
  exact h.trans (trigFeature_constant_norm b₀ b₁ b₂ z)

/-- The same-cluster feature difference lives in one block and retains its harmonics. -/
theorem clusteredFeature_difference_square {m : ℕ} (A : Fin m) (b₀ b₁ b₂ z w : ℝ) :
    (∑ q : Fin m × Fin 5, trigWeight b₀ b₁ b₂ q.2*
      (clusteredFeature A z q-clusteredFeature A w q)^2)=
      (2*b₁*Real.sin ((z-w)/2))^2+(2*b₂*Real.sin (z-w))^2 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ C : Fin m,
      (∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*
        (clusteredFeature A z (C,a)-clusteredFeature A w (C,a))^2)=
      if C=A then ∑ a : Fin 5, trigWeight b₀ b₁ b₂ a*(trigFeature z a-trigFeature w a)^2 else 0 := by
    intro C
    by_cases hC : C=A <;> simp [clusteredFeature,hC]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact trigFeature_difference_square b₀ b₁ b₂ z w

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletedTrigonometricFeatures.lean
section

/-! Exact global factor-to-coordinate feature identities, following C1--C3.
The matrix factor equality is supplied by the independent global PSD construction. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

theorem diagonal_bilinear_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (w x y : κ → ℝ) :
    x ⬝ᵥ ((Matrix.diagonal w) *ᵥ y) = ∑ q, w q*x q*y q := by
  simp only [Matrix.mulVec_diagonal,dotProduct,Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Off-cluster cancellation for the actual embedded five-coordinate features. -/
theorem completed_feature_cross_cancel {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w : ℝ) :
    (M *ᵥ clusteredFeature A z) ⬝ᵥ (M *ᵥ clusteredFeature B w)+
      (V *ᵥ clusteredFeature A z) ⬝ᵥ (V *ᵥ clusteredFeature B w)=0 := by
  rw [completed_bilinear_identity M V _ hfactor,diagonal_bilinear_sum,
    clusteredFeature_weighted_dot,if_neg hAB]

/-- The completed macro-plus-residual perturbation has the exact common norm. -/
theorem completed_feature_constant_norm {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A : Fin m) (z : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q)^2)=b₀^2+b₁^2+b₂^2 := by
  have h := completed_bilinear_identity M V _ hfactor (clusteredFeature A z) (clusteredFeature A z)
  rw [diagonal_bilinear_sum] at h
  simp_rw [dotProduct,mul_assoc,← sq] at h
  exact h.trans (clusteredFeature_constant_norm A b₀ b₁ b₂ z)

/-- The actual completed coordinates have precisely the claimed same-cluster harmonics. -/
theorem completed_feature_difference_square {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A : Fin m) (z w : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q-(M *ᵥ clusteredFeature A w) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q-(V *ᵥ clusteredFeature A w) q)^2)=
      (2*b₁*Real.sin ((z-w)/2))^2+(2*b₂*Real.sin (z-w))^2 := by
  have h := completed_bilinear_identity M V _ hfactor
    (clusteredFeature A z-clusteredFeature A w) (clusteredFeature A z-clusteredFeature A w)
  rw [diagonal_bilinear_sum] at h
  simp_rw [Matrix.mulVec_sub,Pi.sub_apply,dotProduct,mul_assoc,← sq] at h
  exact h.trans (clusteredFeature_difference_square A b₀ b₁ b₂ z w)

/-- The private circle and constant axis turn the common feature reserve into 2R².
The nonnegative square-root reserve is a genuine explicit requirement. -/
theorem completed_full_perturbation_norm {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ R : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (hreserve : b₀^2+b₁^2+b₂^2 ≤ R^2) (A : Fin m) (z angle : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q)^2)+
      (R*Real.cos angle)^2+(R*Real.sin angle)^2+
      (Real.sqrt (R^2-(b₀^2+b₁^2+b₂^2)))^2=2*R^2 := by
  rw [completed_feature_constant_norm M V b₀ b₁ b₂ hfactor A z]
  rw [Real.sq_sqrt (sub_nonneg.mpr hreserve)]
  have h := congrArg (fun x : ℝ => R^2*x) (Real.sin_sq_add_cos_sq angle)
  nlinarith only [h]

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanClusterCoordinates.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

abbrev ClusterCoordinate (ι : Type*) (m : ℕ) :=
  ι ⊕ ((Fin m × Fin 2) ⊕ (Fin m ⊕ (Fin m × Fin 5)))

noncomputable def privateCircle {m : ℕ} (A : Fin m) (R y : ℝ) : Fin m × Fin 2 → ℝ :=
  fun q => if q.1=A then ![R*Real.cos (y/R),R*Real.sin (y/R)] q.2 else 0

/-- Literal finite Euclidean coordinates; macro, private plane, axis, residual. -/
noncomputable def clusterPoint {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis : ℝ)
    (A : Fin m) (z y : ℝ) : EuclideanSpace ℝ (ClusterCoordinate ι m) :=
  WithLp.toLp 2 (Sum.elim (fun q => S*centers A q+(M *ᵥ clusteredFeature A z) q)
    (Sum.elim (privateCircle A R y)
      (Sum.elim (fun B => if B=A then axis else 0) (V *ᵥ clusteredFeature A z))))

theorem privateCircle_difference_square {m : ℕ} (A : Fin m) (R yj yi : ℝ) :
    (∑ q, (privateCircle A R yj q-privateCircle A R yi q)^2)=
      (R*Real.cos (yj/R)-R*Real.cos (yi/R))^2+
      (R*Real.sin (yj/R)-R*Real.sin (yi/R))^2 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ B : Fin m, (∑ a : Fin 2,
      (privateCircle A R yj (B,a)-privateCircle A R yi (B,a))^2)=
      if B=A then (R*Real.cos (yj/R)-R*Real.cos (yi/R))^2+
        (R*Real.sin (yj/R)-R*Real.sin (yi/R))^2 else 0 := by
    intro B
    by_cases h : B=A <;> simp [privateCircle,h,Fin.sum_univ_succ]
  simp_rw [he]
  simp

/-- Actual Euclidean same-cluster distance, including all coordinate blocks. -/
theorem clusterPoint_same_cluster_square {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis b₀ b₁ b₂ : ℝ)
    (hR : R ≠ 0)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A : Fin m) (z w yj yi : ℝ) :
    dist (clusterPoint centers M V S R axis A z yj)
      (clusterPoint centers M V S R axis A w yi)^2=
      (circleChord R (yj-yi))^2+(2*b₁*Real.sin ((z-w)/2))^2+
        (2*b₂*Real.sin (z-w))^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [clusterPoint,WithLp.ofLp_toLp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Real.dist_eq,sq_abs,add_sub_add_left_eq_sub,sub_self,zero_pow,Finset.sum_const_zero,zero_add]
  rw [privateCircle_difference_square]
  simp only [show (0 : ℝ)^2=0 by norm_num,Finset.sum_const_zero,zero_add]
  have hc := circle_chord_coordinate_square R yj yi hR
  have hf := completed_feature_difference_square M V b₀ b₁ b₂ hfactor A z w
  linarith

/-- The intended coordinate count is exactly 9m-1 when the macro space has m-1 coordinates. -/
theorem clusterCoordinate_card (m : ℕ) (hm : 0 < m) :
    Fintype.card (ClusterCoordinate (Fin (m-1)) m)=9*m-1 := by
  simp only [ClusterCoordinate,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanCrossCoordinates.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open scoped BigOperators Matrix
open Matrix

/-- Exact finite sum identity used to expand Euclidean squared distances. -/
theorem sum_sq_sub {κ : Type*} [Fintype κ] (x y : κ → ℝ) :
    (∑ q, (x q-y q)^2)=(∑ q, (x q)^2)+(∑ q, (y q)^2)-2*(x ⬝ᵥ y) := by
  have he : ∀ q, (x q-y q)^2=(x q)^2+(y q)^2-2*(x q*y q) := by
    intro q
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,dotProduct,← Finset.mul_sum]

/-- Squared feature distance across distinct clusters is twice the reserve. -/
theorem completed_cross_feature_square {ι : Type*} [Fintype ι] {m : ℕ}
    (M : Matrix ι (Fin m × Fin 5) ℝ) (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ)
    (b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w : ℝ) :
    (∑ q, ((M *ᵥ clusteredFeature A z) q-(M *ᵥ clusteredFeature B w) q)^2)+
      (∑ q, ((V *ᵥ clusteredFeature A z) q-(V *ᵥ clusteredFeature B w) q)^2)=
        2*(b₀^2+b₁^2+b₂^2) := by
  rw [sum_sq_sub,sum_sq_sub]
  have h₀ := completed_feature_constant_norm M V b₀ b₁ b₂ hfactor A z
  have h₁ := completed_feature_constant_norm M V b₀ b₁ b₂ hfactor B w
  have hcross := completed_feature_cross_cancel M V b₀ b₁ b₂ hfactor A B hAB z w
  linarith

theorem privateCircle_norm_square {m : ℕ} (A : Fin m) (R y : ℝ) :
    (∑ q, (privateCircle A R y q)^2)=R^2 := by
  rw [Fintype.sum_prod_type]
  have he : ∀ B : Fin m, (∑ a : Fin 2, (privateCircle A R y (B,a))^2)=
      if B=A then (R*Real.cos (y/R))^2+(R*Real.sin (y/R))^2 else 0 := by
    intro B
    by_cases h : B=A <;> simp [privateCircle,h,Fin.sum_univ_succ]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have h := congrArg (fun x : ℝ => R^2*x) (Real.sin_sq_add_cos_sq (y/R))
  nlinarith only [h]

theorem privateCircle_cross_dot {m : ℕ} (A B : Fin m) (hAB : A ≠ B) (R yj yi : ℝ) :
    privateCircle A R yj ⬝ᵥ privateCircle B R yi=0 := by
  apply Finset.sum_eq_zero
  intro q _
  by_cases h : q.1=A
  · have h' : q.1 ≠ B := by simpa [h] using hAB
    simp [privateCircle,h,hAB]
  · simp [privateCircle,h]

theorem privateCircle_cross_square {m : ℕ} (A B : Fin m) (hAB : A ≠ B) (R yj yi : ℝ) :
    (∑ q, (privateCircle A R yj q-privateCircle B R yi q)^2)=2*R^2 := by
  rw [sum_sq_sub,privateCircle_norm_square,privateCircle_norm_square,
    privateCircle_cross_dot A B hAB]
  ring

theorem privateAxis_cross_square {m : ℕ} (A B : Fin m) (hAB : A ≠ B) (axis : ℝ) :
    (∑ C : Fin m, ((if C=A then axis else 0)-(if C=B then axis else 0))^2)=2*axis^2 := by
  have he : ∀ C : Fin m, ((if C=A then axis else 0)-(if C=B then axis else 0))^2=
      (if C=A then axis^2 else 0)+(if C=B then axis^2 else 0) := by
    intro C
    by_cases ha : C=A
    · have hb : C ≠ B := by simpa [ha] using hAB
      simp [ha,hb,hAB,Ne.symm hAB]
    · by_cases hb : C=B <;> simp [ha,hb,hAB,Ne.symm hAB]
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  ring

/-- General macro-coordinate expansion, with both signed projection terms retained. -/
theorem coarse_coordinate_expansion {ι : Type*} [Fintype ι] (a b u v : ι → ℝ) (S : ℝ) :
    (∑ q, (S*a q+u q-(S*b q+v q))^2)=
      S^2*(∑ q, (a q-b q)^2)+2*S*((a-b) ⬝ᵥ (u-v))+(∑ q, (u q-v q)^2) := by
  have he : ∀ q, (S*a q+u q-(S*b q+v q))^2=
      S^2*(a q-b q)^2+2*S*((a q-b q)*(u q-v q))+(u q-v q)^2 := by
    intro q
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,dotProduct,Pi.sub_apply]

/-- The actual cross-cluster Euclidean square, before imposing projection targets. -/
theorem clusterPoint_cross_square {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis b₀ b₁ b₂ : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w yj yi : ℝ) :
    dist (clusterPoint centers M V S R axis A z yj)
      (clusterPoint centers M V S R axis B w yi)^2=
      S^2*(∑ q, (centers A q-centers B q)^2)+
      2*S*((centers A-centers B) ⬝ᵥ
        ((M *ᵥ clusteredFeature A z)-(M *ᵥ clusteredFeature B w)))+
      2*(R^2+axis^2+b₀^2+b₁^2+b₂^2) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [clusterPoint,WithLp.ofLp_toLp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Real.dist_eq,sq_abs]
  rw [coarse_coordinate_expansion,privateCircle_cross_square A B hAB,
    privateAxis_cross_square A B hAB]
  have h := completed_cross_feature_square M V b₀ b₁ b₂ hfactor A B hAB z w
  linarith

/-- The exact cross metric now follows from actual Euclidean coordinates and
both directed projection equations; the mixed product is retained. -/
theorem clusterPoint_cross_metric_square {ι : Type*} [Fintype ι] {m : ℕ}
    (centers : Fin m → ι → ℝ) (M : Matrix ι (Fin m × Fin 5) ℝ)
    (V : Matrix (Fin m × Fin 5) (Fin m × Fin 5) ℝ) (S R axis b₀ b₁ b₂ ν α β : ℝ)
    (hfactor : Mᵀ*M+Vᵀ*V=Matrix.diagonal (fun q => trigWeight b₀ b₁ b₂ q.2))
    (A B : Fin m) (hAB : A ≠ B) (z w yj yi : ℝ)
    (haxis : axis^2=R^2-(b₀^2+b₁^2+b₂^2))
    (hbase : S^2*(∑ q, (centers A q-centers B q)^2)+4*R^2=ν^2)
    (hprojA : 2*S*((centers A-centers B) ⬝ᵥ (M *ᵥ clusteredFeature A z))=2*ν*α+α^2)
    (hprojB : -2*S*((centers A-centers B) ⬝ᵥ (M *ᵥ clusteredFeature B w))=2*ν*β+β^2) :
    dist (clusterPoint centers M V S R axis A z yj)
      (clusterPoint centers M V S R axis B w yi)^2=(ν+α+β)^2-2*α*β := by
  have h := clusterPoint_cross_square centers M V S R axis b₀ b₁ b₂ hfactor A B hAB z w yj yi
  rw [dotProduct_sub] at h
  nlinarith

/-- The absolute cross-error envelope follows from the square identity and a
positive nominal lower bound. No adjacent or differential error bound is used. -/
theorem cross_error_uniform_bound (D u α β B Tmin : ℝ) (hD : 0 ≤ D)
    (hT : 0 < Tmin) (hu : Tmin ≤ u) (hB : |α*β| ≤ B)
    (hsquare : D^2=u^2-2*α*β) : |D-u| ≤ 2*B/Tmin := by
  have hden : 0 < D+u := by linarith
  have heq : D-u=(-2*(α*β))/(D+u) := by
    apply (eq_div_iff hden.ne').2
    nlinarith
  rw [heq,abs_div,abs_mul,abs_of_pos hden]
  norm_num
  have hbound := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ 2 by norm_num)
  have h₀ := div_le_div_of_nonneg_right hbound hden.le
  have h₁ := div_le_div_of_nonneg_left (show 0 ≤ 2*B by nlinarith [abs_nonneg (α*β)]) hT
    (show Tmin ≤ D+u by linarith)
  simpa only [abs_mul] using h₀.trans h₁

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleGeometry.lean
section

/-!
Orthogonal-circle geometry for the fifth-pass construction.
Source: consecutive-euclidean-distances, merge 1d8de6b,
candidate/fixed670-orthogonal-circles-pass5-20261013/orthogonal_circles.tex,
Lemma completion and equations cross-expansion and actual-point.

The old nine-block construction is not modified. The whole-matrix quadratic
budget below is the operator-norm hypothesis, not a columnwise substitute.
-/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
namespace Pass5
open scoped BigOperators Matrix
open Matrix

/-- A norm budget for the entire direction matrix yields a same-size residual. -/
theorem circle_completion_factor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (R : ℝ)
    (hbudget : ∀ x : κ → ℝ, ∑ i, (U *ᵥ x) i ^ 2 ≤ R^2 * ∑ a, x a ^ 2) :
    ∃ W : Matrix κ κ ℝ, Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2) := by
  have hpsd : (Matrix.diagonal (fun _ : κ => R^2) - Uᵀ * U).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (Matrix.isHermitian_diagonal (fun _ : κ => R^2)).sub
        (by simpa using Matrix.isHermitian_conjTranspose_mul_self U)
    intro x
    have hgram : x ⬝ᵥ ((Uᵀ * U) *ᵥ x) = ∑ i, (U *ᵥ x) i ^ 2 := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      simp only [dotProduct, pow_two]
    have hdiag : x ⬝ᵥ ((Matrix.diagonal (fun _ : κ => R^2)) *ᵥ x) =
        R^2 * ∑ a, x a ^ 2 := by
      simp only [Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hgram, hdiag,
      sub_nonneg] using hbudget x
  obtain ⟨W, hW⟩ := psd_same_size_gram_factor _ hpsd
  refine ⟨W, ?_⟩
  rw [hW]
  abel

/-- Coordinate type of the new construction: macro space and two m-blocks. -/
abbrev CircleCoordinate (ι κ : Type*) := ι ⊕ (κ ⊕ κ)

/-- The literal circle perturbation, with the prescribed macro projection. -/
noncomputable def circlePerturbation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (R : ℝ) (A : κ) (z : ℝ) : CircleCoordinate ι κ → ℝ :=
  Sum.elim (fun i => U i A * Real.sin z)
    (Sum.elim (fun i => W i A * Real.sin z)
      (fun i => if i = A then R * Real.cos z else 0))

/-- Actual Euclidean coordinates; all points share the same three blocks. -/
noncomputable def circlePoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (A : κ) (z : ℝ) : EuclideanSpace ℝ (CircleCoordinate ι κ) :=
  WithLp.toLp 2 (Sum.elim (fun i => S * q A i + U i A * Real.sin z)
    (Sum.elim (fun i => W i A * Real.sin z)
      (fun i => if i = A then R * Real.cos z else 0)))

/-- The factor equation gives the exact pairwise column Gram matrix. -/
theorem completed_column_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2)) (A B : κ) :
    (∑ i, U i A * U i B) + (∑ i, W i A * W i B) =
      if A = B then R^2 else 0 := by
  have h := congrFun (congrFun hfactor A) B
  simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply] using h

/-- The circle planes for distinct anchors are genuinely orthogonal. -/
theorem circlePerturbation_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (z w : ℝ) :
    circlePerturbation U W R A z ⬝ᵥ circlePerturbation U W R B w =
      if A = B then R^2 * (Real.sin z * Real.sin w + Real.cos z * Real.cos w)
      else 0 := by
  have hm (M : Matrix ι κ ℝ) :
      (∑ i, (M i A * Real.sin z) * (M i B * Real.sin w)) =
        (∑ i, M i A * M i B) * (Real.sin z * Real.sin w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hw : (∑ i, (W i A * Real.sin z) * (W i B * Real.sin w)) =
      (∑ i, W i A * W i B) * (Real.sin z * Real.sin w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [circlePerturbation, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  rw [hm, hw]
  have hc := completed_column_dot U W R hfactor A B
  by_cases hAB : A = B
  · subst B
    simp only [ite_true] at hc ⊢
    have hp : (∑ i, (if i = A then R * Real.cos z else 0) *
        (if i = A then R * Real.cos w else 0)) =
        R^2 * (Real.cos z * Real.cos w) := by
      have he (i : κ) :
          (if i = A then R * Real.cos z else 0) *
            (if i = A then R * Real.cos w else 0) =
          if i = A then R^2 * (Real.cos z * Real.cos w) else 0 := by
        by_cases hi : i = A <;> simp [hi] <;> ring
      simp_rw [he]
      simp
    rw [hp]
    linear_combination (Real.sin z * Real.sin w) * hc
  · have hp : (∑ i, (if i = A then R * Real.cos z else 0) *
        (if i = B then R * Real.cos w else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = A
      · subst i
        simp [hAB]
      · simp [hi]
    rw [hp, if_neg hAB]
    rw [if_neg hAB] at hc
    linear_combination (Real.sin z * Real.sin w) * hc

/-- Every perturbation has the common squared norm R². -/
theorem circlePerturbation_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z : ℝ) :
    (∑ i, (circlePerturbation U W R A z i)^2) = R^2 := by
  have h := circlePerturbation_dot U W R hfactor A A z z
  simp only [ite_true, dotProduct, ← pow_two] at h
  rw [Real.sin_sq_add_cos_sq, mul_one] at h
  exact h

/-- Exact common-circle chord square, derived from the completed Gram matrix. -/
theorem circlePerturbation_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    (∑ i, (circlePerturbation U W R A z i - circlePerturbation U W R A w i)^2) =
      (2*R*Real.sin ((z-w)/2))^2 := by
  rw [sum_sq_sub, circlePerturbation_square U W R hfactor,
    circlePerturbation_square U W R hfactor, circlePerturbation_dot U W R hfactor]
  simp only [ite_true]
  have h := Real.sin_sq_eq_half_sub ((z-w)/2)
  rw [show 2*((z-w)/2)=z-w by ring, Real.cos_sub] at h
  nlinarith [congrArg (fun t : ℝ => R^2*t) h]

/-- Distinct circle planes contribute precisely 2R² to the squared distance. -/
theorem circlePerturbation_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ) :
    (∑ i, (circlePerturbation U W R A z i - circlePerturbation U W R B w i)^2) =
      2*R^2 := by
  rw [sum_sq_sub, circlePerturbation_square U W R hfactor,
    circlePerturbation_square U W R hfactor, circlePerturbation_dot U W R hfactor,
    if_neg hAB]
  ring

/-- Same-cluster distances are actual circle chords, with no extra correction. -/
theorem circlePoint_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R A w)^2 =
      (2*R*Real.sin ((z-w)/2))^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simpa only [circlePoint, circlePerturbation, WithLp.ofLp_toLp,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Real.dist_eq, sq_abs,
    add_sub_add_left_eq_sub] using circlePerturbation_same_square U W R hfactor A z w

/-- The unsigned chord formula for actual points. -/
theorem circlePoint_same_distance {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hR : 0 ≤ R)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R A w) =
      2*R*|Real.sin ((z-w)/2)| := by
  have hsq := circlePoint_same_square q U W S R hfactor A z w
  have habs := sq_abs (Real.sin ((z-w)/2))
  have hd := dist_nonneg (x := circlePoint q U W S R A z)
    (y := circlePoint q U W S R A w)
  have hrhs : 0 ≤ 2*R*|Real.sin ((z-w)/2)| := by positivity
  nlinarith [congrArg (fun t : ℝ => (2*R)^2*t) habs]

/-- Exact cross expansion in the literal r+2m coordinate space. -/
theorem circlePoint_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R B w)^2 =
      S^2*(∑ i, (q A i-q B i)^2) + 2*R^2 +
        2*S*((q A-q B) ⬝ᵥ ((fun i => U i A*Real.sin z)-(fun i => U i B*Real.sin w))) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [circlePoint, WithLp.ofLp_toLp, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Real.dist_eq, sq_abs]
  rw [coarse_coordinate_expansion]
  have hp := circlePerturbation_cross_square U W R hfactor A B hAB z w
  simp only [circlePerturbation, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hp
  linarith

/-- The shortened macro metric and the two directed projections give the exact
new cross metric. This is linear in both digits; no quadratic feature is used. -/
theorem circlePoint_cross_metric_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R D α β : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ)
    (hbase : S^2*(∑ i, (q A i-q B i)^2)+2*R^2 = (S*D)^2)
    (hprojA : (q A-q B) ⬝ᵥ (fun i => U i A*Real.sin z) = D*α)
    (hprojB : (q B-q A) ⬝ᵥ (fun i => U i B*Real.sin w) = D*β) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R B w)^2 =
      (S*D)^2 + 2*(S*D)*(α+β) := by
  have h := circlePoint_cross_square q U W S R hfactor A B hAB z w
  have hneg : (q A-q B) ⬝ᵥ (fun i => U i B*Real.sin w) = -(D*β) := by
    rw [show q A-q B = -(q B-q A) by abel, neg_dotProduct, hprojB]
  rw [dotProduct_sub, hprojA, hneg] at h
  nlinarith only [h, hbase]

/-- The exact square-root cross-length formula for actual points. -/
theorem circlePoint_cross_distance {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R D α β : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ)
    (hbase : S^2*(∑ i, (q A i-q B i)^2)+2*R^2 = (S*D)^2)
    (hprojA : (q A-q B) ⬝ᵥ (fun i => U i A*Real.sin z) = D*α)
    (hprojB : (q B-q A) ⬝ᵥ (fun i => U i B*Real.sin w) = D*β) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R B w) =
      Real.sqrt ((S*D)^2 + 2*(S*D)*(α+β)) := by
  rw [← circlePoint_cross_metric_square q U W S R D α β hfactor A B hAB z w
    hbase hprojA hprojB, Real.sqrt_sq (dist_nonneg)]

/-- Source shortening cancels the entire common radius contribution. -/
theorem shortened_macro_cancellation (S R D Q : ℝ) (hS : S ≠ 0)
    (hQ : Q = D^2 - 2*(R/S)^2) :
    S^2*Q + 2*R^2 = (S*D)^2 := by
  rw [hQ]
  field_simp [hS]
  <;> ring

/-- Exact dimension of the new coordinate family. -/
theorem circleCoordinate_card (m : ℕ) (hm : 0 < m) :
    Fintype.card (CircleCoordinate (Fin (m-1)) (Fin m)) = 3*m-1 := by
  simp only [CircleCoordinate, Fintype.card_sum, Fintype.card_fin]
  omega

end Pass5
end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From TwoCircleGeometry.lean
section

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5

abbrev TwoCircleCoordinate (ι κ : Type*) :=
  CircleCoordinate ι κ ⊕ CircleCoordinate (Fin 0) κ

noncomputable def joinPoints {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℝ α) (y : EuclideanSpace ℝ β) :
    EuclideanSpace ℝ (α ⊕ β) := WithLp.toLp 2 (Sum.elim x y)

theorem joinPoints_dist_sq {α β : Type*} [Fintype α] [Fintype β]
    (x x' : EuclideanSpace ℝ α) (y y' : EuclideanSpace ℝ β) :
    dist (joinPoints x y) (joinPoints x' y') ^ 2 =
      dist x x' ^ 2 + dist y y' ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, joinPoints, WithLp.ofLp_toLp,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem private_factor {κ : Type*} [Fintype κ] [DecidableEq κ] (R : ℝ) :
    (0 : Matrix (Fin 0) κ ℝ)ᵀ * (0 : Matrix (Fin 0) κ ℝ) +
      (diagonal (fun _ : κ => R))ᵀ * diagonal (fun _ => R) =
      diagonal (fun _ => R ^ 2) := by
  simp [Matrix.diagonal_mul_diagonal, pow_two]

noncomputable def privatePoint {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℝ) (A : κ) (w : ℝ) : EuclideanSpace ℝ (CircleCoordinate (Fin 0) κ) :=
  circlePoint (fun _ _ => 0) 0 (diagonal (fun _ => R)) 0 R A w

noncomputable def twoCirclePoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ) (A : κ) (z w : ℝ) :
    EuclideanSpace ℝ (TwoCircleCoordinate ι κ) :=
  joinPoints (circlePoint q U W S R₀ A z) (privatePoint R₁ A w)

theorem twoCircle_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = diagonal (fun _ => R₀ ^ 2))
    (A : κ) (z z' w w' : ℝ) :
    dist (twoCirclePoint q U W S R₀ R₁ A z w)
      (twoCirclePoint q U W S R₀ R₁ A z' w') ^ 2 =
      (2 * R₀ * Real.sin ((z-z')/2)) ^ 2 +
      (2 * R₁ * Real.sin ((w-w')/2)) ^ 2 := by
  unfold twoCirclePoint privatePoint
  rw [joinPoints_dist_sq, circlePoint_same_square q U W S R₀ hfactor,
    circlePoint_same_square _ _ _ _ _ (private_factor R₁)]

theorem twoCircle_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = diagonal (fun _ => R₀ ^ 2))
    (A B : κ) (hAB : A ≠ B) (z z' w w' : ℝ) :
    dist (twoCirclePoint q U W S R₀ R₁ A z w)
      (twoCirclePoint q U W S R₀ R₁ B z' w') ^ 2 =
      S^2 * (∑ i, (q A i-q B i)^2) + 2*(R₀^2+R₁^2) +
      2*S*((q A-q B) ⬝ᵥ ((fun i => U i A*Real.sin z)-
        (fun i => U i B*Real.sin z'))) := by
  unfold twoCirclePoint privatePoint
  rw [joinPoints_dist_sq, circlePoint_cross_square q U W S R₀ hfactor A B hAB,
    circlePoint_cross_square _ _ _ _ _ (private_factor R₁) A B hAB]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add]
  ring

theorem coordinate_card : Fintype.card (TwoCircleCoordinate (Fin 5) (Fin 6)) = 29 := by
  decide




end Erdos670R29

end

-- From AnchorInterface.lean
section

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

def anchor (Q : Matrix (Fin 5) (Fin 5) ℝ) (A : Fin 6) : Fin 5 → ℝ :=
  Fin.cases (fun _ => 0) (fun j i => Q i j) A

lemma sourceE_self (A : Fin 6) : sourceE A A = 0 := by simp [sourceE]
lemma sourceE_symm (A B : Fin 6) : sourceE A B = sourceE B A := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceE, sourceD, labels]
lemma sourceD_self (A : Fin 6) : sourceD A A = 0 := by simp [sourceD]
lemma PG_self (A : Fin 6) : PG A A = 0 := by simp [PG]
lemma PF_self (A : Fin 6) : PF A A = 0 := by simp [PF, PG_self, sourceD_self]

lemma anchor_dot (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (hQ : Qᵀ*Q = sourceMacro) (A B : Fin 6) :
    anchor Q A ⬝ᵥ anchor Q B =
      (sourceE 0 A + sourceE 0 B - sourceE A B)/2 := by
  refine Fin.cases ?_ (fun a => ?_) A
  · simp [anchor, dotProduct, sourceE_self]
  refine Fin.cases ?_ (fun b => ?_) B
  · simp [anchor, dotProduct, sourceE_self, sourceE_symm a.succ 0]
  have h := congrFun (congrFun hQ a) b
  simpa [anchor, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, sourceMacro] using h

lemma anchor_distance_square (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (hQ : Qᵀ*Q = sourceMacro) (A B : Fin 6) :
    (∑ i, (anchor Q A i-anchor Q B i)^2) = sourceE A B := by
  rw [sum_sq_sub]
  have hA := anchor_dot Q hQ A A
  have hB := anchor_dot Q hQ B B
  have hAB := anchor_dot Q hQ A B
  simp only [sourceE_self, sub_zero, dotProduct] at hA hB hAB
  simp only [pow_two, dotProduct]
  linarith

lemma anchor_projection (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A J : Fin 6) :
    anchor Q J ⬝ᵥ (fun i => U i A) =
      k/(519/1000) * ((138/125*k)*(PG A 0-PG A J)+(533/500)*(PF A 0-PF A J)) := by
  refine Fin.cases ?_ (fun j => ?_) J
  · simp [anchor, dotProduct]
  have h := congrFun (congrFun hp j) A
  simpa [anchor, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, TG, TF] using h

lemma anchored_projection (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A B : Fin 6) :
    (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A) =
      k/(519/1000) * ((138/125*k)*PG A B+(533/500)*PF A B) := by
  rw [sub_dotProduct, anchor_projection Q U k hp, anchor_projection Q U k hp]
  rw [PG_self, PF_self]
  ring



end Erdos670R29

end

-- From ActualCoordinates.lean
section

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma sourceD_symm (A B : Fin 6) : sourceD A B = sourceD B A := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceD, labels]

lemma sourceE_offdiag (A B : Fin 6) (hAB : A ≠ B) :
    sourceE A B = (sourceD A B)^2 - 2*((507/100 : ℝ)^2+(1131/100 : ℝ)^2) := by
  simp [sourceE, hAB]

lemma oriented_projections (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A B : Fin 6) (hAB : A < B) :
    (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A) =
        k/(519/1000)*(138/125*k)*sourceD A B ∧
    (anchor Q B-anchor Q A) ⬝ᵥ (fun i => U i B) =
        k/(519/1000)*(533/500)*sourceD A B := by
  have hBA : ¬ B.val < A.val := by omega
  rw [anchored_projection Q U k hp, anchored_projection Q U k hp]
  simp only [PG, PF, show A.val < B.val from hAB, hBA, if_true, if_false,
    sub_self, mul_zero, add_zero, zero_add, sub_zero, sourceD_symm B A]
  constructor <;> ring

/-- Exact literal-coordinate cross identity for every ordered pair of anchors.
The private ruler angles are arbitrary: their contribution is exactly constant. -/
theorem actual_cross_square (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (W : Matrix (Fin 6) (Fin 6) ℝ) (k : ℝ)
    (hQ : Qᵀ*Q = sourceMacro)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*k^2)^2))
    (A B : Fin 6) (hAB : A < B) (z z' w w' : ℝ) :
    dist (twoCirclePoint (anchor Q) U W (k^2) ((507/100)*k^2) ((1131/100)*k^2) A z w)
      (twoCirclePoint (anchor Q) U W (k^2) ((507/100)*k^2) ((1131/100)*k^2) B z' w') ^ 2 =
      (k^2*sourceD A B)^2 + 2*(k^2*sourceD A B)*
        ((138/125*k)*(k/(519/1000)*Real.sin z)+(533/500)*(k/(519/1000)*Real.sin z')) := by
  rw [twoCircle_cross_square _ _ _ _ _ _ hfactor A B (ne_of_lt hAB),
    anchor_distance_square Q hQ, sourceE_offdiag A B (ne_of_lt hAB)]
  obtain ⟨ha,hb⟩ := oriented_projections Q U k hp A B hAB
  have hsA : (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A*Real.sin z) =
      ((anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A))*Real.sin z := by
    simp only [dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsB : (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i B*Real.sin z') =
      -((anchor Q B-anchor Q A) ⬝ᵥ (fun i => U i B))*Real.sin z' := by
    simp only [dotProduct, Pi.sub_apply]
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [dotProduct_sub, hsA, hsB, ha, hb]
  ring


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRuler.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Same-lag residues distinguish the cluster and the initial local index.
The sharper `i + δ < k` endpoint condition is retained explicitly. -/
theorem same_lag_residue_injective
    (p m k δ A B i j : ℕ) (hp : p.Prime) (hδ : 0 < δ) (hδp : δ < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+δ < k)
    (heq : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p) :
    A=B ∧ i=j := by
  have hcop : p.Coprime δ := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hδ hδp)
  have hmod : 2*i+δ+2*k*A ≡ 2*j+δ+2*k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hcop heq
  have hleft : 2*i+δ+2*k*A < p := by
    have hh := Nat.mul_le_mul_left (2*k) (show A+1 ≤ m by omega)
    nlinarith
  have hright : 2*j+δ+2*k*B < p := by
    have hh := Nat.mul_le_mul_left (2*k) (show B+1 ≤ m by omega)
    nlinarith
  have hbracket := hmod.eq_of_lt_of_lt hleft hright
  have hab : A=B := by
    rcases lt_trichotomy A B with hab | hab | hab
    · have hh := Nat.mul_le_mul_left k (show A+1 ≤ B by omega)
      nlinarith
    · exact hab
    · have hh := Nat.mul_le_mul_left k (show B+1 ≤ A by omega)
      nlinarith
  exact ⟨hab, by subst B; omega⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SineDigits.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sineDigit (θ center x : ℝ) : ℝ := Real.sin (θ*(x-center))/θ

theorem hasDerivAt_sineDigit (θ center x : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (sineDigit θ center) (Real.cos (θ*(x-center))) x := by
  have h := ((((hasDerivAt_id x).sub_const center).const_mul θ).sin).div_const θ
  have he : (Real.cos (θ*(x-center))*(θ*1))/θ=Real.cos (θ*(x-center)) := by field_simp
  convert h using 1 <;> first | rfl | exact he.symm

/-- The normalized sine digit never exceeds its centered coordinate in magnitude. -/
theorem sineDigit_abs_le (θ center x : ℝ) (hθ : 0 < θ) :
    |sineDigit θ center x| ≤ |x-center| := by
  unfold sineDigit
  rw [abs_div,abs_of_pos hθ]
  calc
    |Real.sin (θ*(x-center))|/θ ≤ |θ*(x-center)|/θ :=
      div_le_div_of_nonneg_right Real.abs_sin_le_abs hθ.le
    _ = |x-center| := by rw [abs_mul,abs_of_pos hθ]; field_simp

/-- Centered coordinate bounds apply to every digit in the full interval. -/
theorem sineDigit_centered_bound (θ center x : ℝ) (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxc : x ≤ 2*center) : |sineDigit θ center x| ≤ center := by
  apply (sineDigit_abs_le θ center x hθ).trans
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Uniform adjacent and nonadjacent sine digit lower slope on the centered interval. -/
theorem sineDigit_lower_difference (θ center x y : ℝ) (hθ : 0 < θ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*center) :
    (1-(θ*center)^2/2)*(y-x) ≤ sineDigit θ center y-sineDigit θ center x := by
  have hc : 0 ≤ center := by linarith
  have hd (z : ℝ) := hasDerivAt_sineDigit θ center z hθ.ne'
  apply (convex_Icc (0 : ℝ) (2*center)).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) (2*center) := interior_subset hz
  have hb : |z-center| ≤ center := abs_le.mpr ⟨by linarith [hz'.1],by linarith [hz'.2]⟩
  have harg : |θ*(z-center)| ≤ |θ*center| := by
    rw [abs_mul,abs_mul,abs_of_pos hθ,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hb hθ.le
  have hsq : (θ*(z-center))^2 ≤ (θ*center)^2 := sq_le_sq.mpr harg
  rw [(hd z).deriv]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ*(z-center))
  linarith

/-- Source-shaped finite digit bound, valid for all k and every legal index. -/
theorem finite_sineDigit_bound (θ : ℝ) (k i : ℕ) (hθ : 0 < θ) (hi : i < k) :
    |sineDigit θ (((k : ℝ)-1)/2) i| ≤ ((k : ℝ)-1)/2 := by
  apply sineDigit_centered_bound θ (((k : ℝ)-1)/2) i hθ (by positivity)
  have h : (i : ℝ)+1 ≤ k := by exact_mod_cast hi
  linarith

/-- Uniform lower step from the source's θ²k²≤epsilon envelope. -/
theorem finite_sineDigit_step (θ ε : ℝ) (k i : ℕ) (hθ : 0 < θ)
    (hi : i+1 < k) (hscale : θ^2*(k : ℝ)^2 ≤ ε) :
    1-ε/8 ≤ sineDigit θ (((k : ℝ)-1)/2) (i+1)-
      sineDigit θ (((k : ℝ)-1)/2) i := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hi' : (i : ℝ)+2 ≤ k := by exact_mod_cast hi
  have h := sineDigit_lower_difference θ (((k : ℝ)-1)/2) i ((i : ℝ)+1)
    hθ (by positivity) (by linarith) (by linarith)
  have hb : θ^2*((k : ℝ)-1)^2 ≤ θ^2*(k : ℝ)^2 := by
    have hsq : ((k : ℝ)-1)^2 ≤ (k : ℝ)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg θ)
  norm_num at h
  nlinarith

/-- The fixed epsilon1/32 source gives r=255/256 uniformly. -/
theorem finite_sineDigit_source_step (θ : ℝ) (k i : ℕ) (hθ : 0 < θ)
    (hi : i+1 < k) (hscale : θ^2*(k : ℝ)^2 ≤ 1/32) :
    (255 : ℝ)/256 ≤ sineDigit θ (((k : ℝ)-1)/2) (i+1)-
      sineDigit θ (((k : ℝ)-1)/2) i := by
  have h := finite_sineDigit_step θ (1/32) k i hθ hi hscale
  norm_num at h ⊢
  exact h

/-- The source square-root scaling meets the required uniform envelope exactly. -/
theorem source_theta_scale (k : ℕ) (hk : 0 < k) :
    (Real.sqrt (1/32)/(k : ℝ))^2*(k : ℝ)^2=1/32 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [div_pow,Real.sq_sqrt (by norm_num)]
  field_simp

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Ruler.lean
section

/-! Exact integer-ruler layer. Unlike a residue-only statement, these theorems
refer to the actual differences of the explicit ruler positions. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The fifth-pass ruler, with the linear spacing parameter L explicit. -/
def pass5Ruler (L p k A i : ℕ) : ℤ :=
  (L : ℤ) * (p : ℤ) * (i : ℤ) + ((i^2 + 2*k*A*i) % p : ℕ)

/-- A positive-lag difference, kept in the integers so subtraction never truncates. -/
def pass5RulerGap (L p k A i δ : ℕ) : ℤ :=
  pass5Ruler L p k A (i + δ) - pass5Ruler L p k A i

/-- Every actual ruler difference lies in its strict lag window. -/
theorem pass5RulerGap_window (L p k A i δ : ℕ) (hp : 0 < p) :
    ((L : ℤ) * (δ : ℤ) - 1) * p < pass5RulerGap L p k A i δ ∧
      pass5RulerGap L p k A i δ < ((L : ℤ) * (δ : ℤ) + 1) * p := by
  have h₀ : (0 : ℤ) ≤ ((i^2 + 2*k*A*i) % p : ℕ) := by positivity
  have h₁ : (0 : ℤ) ≤ (((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) := by positivity
  have h₂ : (((i^2 + 2*k*A*i) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  have h₃ : ((((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  dsimp [pass5RulerGap, pass5Ruler]
  push_cast at *
  constructor <;> nlinarith

/-- Strictly positive lags give positive actual ruler gaps. -/
theorem pass5RulerGap_pos (L p k A i δ : ℕ) (hp : 0 < p) (hL : 2 ≤ L) (hδ : 0 < δ) :
    0 < pass5RulerGap L p k A i δ := by
  have hw := (pass5RulerGap_window L p k A i δ hp).1
  have hδ' : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hL' : (2 : ℤ) ≤ L := by exact_mod_cast hL
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ L-2) (by omega : (0 : ℤ) ≤ δ)]

/-- Different lag windows are strictly ordered for every L ≥ 2. -/
theorem pass5RulerGap_different_lag (L p k A B i j δ ε : ℕ)
    (hp : 0 < p) (hL : 2 ≤ L) (hδε : δ < ε) :
    0 < pass5RulerGap L p k B j ε - pass5RulerGap L p k A i δ := by
  have h₀ := (pass5RulerGap_window L p k A i δ hp).2
  have h₁ := (pass5RulerGap_window L p k B j ε hp).1
  have hδε' : (δ : ℤ) + 1 ≤ ε := by exact_mod_cast hδε
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hL' : (2 : ℤ) ≤ L := by exact_mod_cast hL
  have hd : (L : ℤ) * δ + 2 ≤ (L : ℤ) * ε := by
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ L) (by omega : (0 : ℤ) ≤ ε-δ-1)]
  nlinarith

/-- The actual ruler difference has exactly the stated quadratic residue. -/
theorem pass5RulerGap_residue (L p k A i δ : ℕ) :
    pass5RulerGap L p k A i δ % (p : ℤ) =
      ((δ * (2*i + δ + 2*k*A) : ℕ) : ℤ) % (p : ℤ) := by
  have hpoly : (((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
      ((i^2 + 2*k*A*i : ℕ) : ℤ) = ((δ*(2*i+δ+2*k*A) : ℕ) : ℤ) := by
    push_cast
    ring
  calc
    pass5RulerGap L p k A i δ % (p : ℤ) =
        ((((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
          ((i^2 + 2*k*A*i : ℕ) : ℤ)) % (p : ℤ) := by
      simp [pass5RulerGap, pass5Ruler, Int.add_emod, Int.sub_emod,
        Int.mul_emod, Int.natCast_emod]
    _ = _ := congrArg (fun z : ℤ => z % (p : ℤ)) hpoly

/-- Equal same-lag *actual* gaps force the same cluster and starting index. -/
theorem pass5RulerGap_same_lag_injective (L p m k δ A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hδp : δ < p) (hsize : 2*m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : pass5RulerGap L p k A i δ = pass5RulerGap L p k B j δ) : A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [pass5RulerGap_residue, pass5RulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective p m k δ A B i j hp hδ hδp hsize hA hB hi hj hnat

/-- Exhaustive uniqueness of all positive actual ruler gaps, across all clusters.
Different lags use disjoint windows; equal lags use prime cancellation. -/
theorem pass5RulerGap_injective (L p m k δ ε A B i j : ℕ)
    (hp : p.Prime) (hL : 2 ≤ L) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k)
    (heq : pass5RulerGap L p k A i δ = pass5RulerGap L p k B j ε) :
    A = B ∧ i = j ∧ δ = ε := by
  have hδε : δ = ε := by
    rcases lt_trichotomy δ ε with hlt | he | hgt
    · have h := pass5RulerGap_different_lag L p k A B i j δ ε hp.pos hL hlt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
    · exact he
    · have h := pass5RulerGap_different_lag L p k B A j i ε δ hp.pos hL hgt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
  subst ε
  obtain ⟨hAB,hij⟩ := pass5RulerGap_same_lag_injective L p m k δ A B i j
    hp hδ hδp hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩



/-- The uncentered normalized ruler coordinate. -/
noncomputable def pass5Raw (L p k A i : ℕ) : ℝ :=
  (pass5Ruler L p k A i : ℝ) / ((L : ℝ) * p)

/-- Every normalized coordinate lies in the same short interval. -/
theorem pass5Raw_bounds (L p k A i : ℕ) (hL : 2 ≤ L) (hp : 0 < p) (hi : i < k) :
    0 ≤ pass5Raw L p k A i ∧ pass5Raw L p k A i < (k : ℝ) - (1 - 1/(L : ℝ)) := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hi' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
  have hr0 : (0 : ℝ) ≤ ((i^2+2*k*A*i)%p : ℕ) := by positivity
  have hr1 : (((i^2+2*k*A*i)%p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt _ hp
  have hd : 0 < (L : ℝ)*p := by positivity
  unfold pass5Raw pass5Ruler
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  constructor
  · positivity
  · apply (div_lt_iff₀ hd).2
    have hLi : (L : ℝ)*(i+1) ≤ (L : ℝ)*k :=
      mul_le_mul_of_nonneg_left hi' (by positivity)
    have hLip := mul_le_mul_of_nonneg_right hLi hp'.le
    have he : ((k : ℝ)-(1-1/(L : ℝ)))*((L : ℝ)*p) =
        (L : ℝ)*p*(k-1)+p := by field_simp <;> ring
    rw [he]
    nlinarith

/-- The exact raw adjacent step exceeds kappa=1−1/L. -/
theorem pass5Raw_step (L p k A i : ℕ) (hL : 2 ≤ L) (hp : 0 < p) :
    1-1/(L : ℝ) < pass5Raw L p k A (i+1)-pass5Raw L p k A i := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hd : 0 < (L : ℝ)*p := by positivity
  have hw := (pass5RulerGap_window L p k A i 1 hp).1
  norm_num only [Nat.cast_one, mul_one] at hw
  have hw' : ((L : ℝ)-1)*p < (pass5RulerGap L p k A i 1 : ℝ) := by
    exact_mod_cast hw
  have he : pass5Raw L p k A (i+1)-pass5Raw L p k A i =
      (pass5RulerGap L p k A i 1 : ℝ) / ((L : ℝ)*p) := by
    unfold pass5Raw pass5RulerGap
    push_cast
    ring
  rw [he]
  apply (lt_div_iff₀ hd).2
  have he' : (1-1/(L : ℝ))*((L : ℝ)*p)=((L : ℝ)-1)*p := by field_simp <;> ring
  rw [he']
  exact hw'

/-- Centering the ruler gives the paper's position and angular envelope. -/
theorem pass5_position_bounds (L p k A i : ℕ) (hL : 2 ≤ L) (hp : 0 < p)
    (hi : i < k) :
    |pass5Raw L p k A i - ((k : ℝ)-(1-1/(L : ℝ)))/2| ≤
      ((k : ℝ)-(1-1/(L : ℝ)))/2 ∧
    ((k : ℝ)-(1-1/(L : ℝ)))/2 < (k : ℝ)/2 := by
  obtain ⟨h0,h1⟩ := pass5Raw_bounds L p k A i hL hp hi
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hrec : 1/(L : ℝ) ≤ (1/2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hL'
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩

/-- A generic sine-digit lower step on the paper's small-angle interval.
All premises are explicit raw-coordinate bounds, so this can be instantiated
with the normalized clustered ruler without any approximation axiom. -/
theorem pass5_sine_digit_step (a k h κ x y : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k/2)
    (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hy : y ≤ 2*h) (hgap : κ < y-x) :
    κ*(1-a^2/8) < sineDigit (a/k) h y - sineDigit (a/k) h x := by
  have hθ : 0 < a/k := div_pos ha hk
  have hxy : x ≤ y := by linarith
  have hbase := sineDigit_lower_difference (a/k) h x y hθ hx hxy hy
  have harg : (a/k)*h ≤ a/2 := by
    have he : (a/k)*h = (a*h)/k := by ring
    rw [he]
    apply (div_le_iff₀ hk).2
    nlinarith [mul_le_mul_of_nonneg_left hhk ha.le]
  have harg0 : 0 ≤ (a/k)*h := mul_nonneg hθ.le hh
  have hs : ((a/k)*h)^2 ≤ a^2/4 := by nlinarith
  have hγ : 0 < 1-a^2/8 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (1-((a/k)*h)^2/2)-(1-a^2/8) by nlinarith)
    (show 0 ≤ y-x by linarith)
  have hstrict := mul_lt_mul_of_pos_right hgap hγ
  nlinarith


noncomputable def pass5H (k : ℕ) : ℝ := ((k : ℝ)-(1-1/(12 : ℝ)))/2
noncomputable def pass5Theta (k : ℕ) : ℝ := (49/100 : ℝ)/(k : ℝ)
noncomputable def pass5Digit (p k A i : ℕ) : ℝ :=
  sineDigit (pass5Theta k) (pass5H k) (pass5Raw 12 p k A i)

theorem pass5H_pos (k : ℕ) (hk : 2 ≤ k) : 0 < pass5H k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold pass5H
  linarith

theorem pass5Theta_pos (k : ℕ) (hk : 0 < k) : 0 < pass5Theta k := by
  unfold pass5Theta
  positivity

theorem pass5Digit_abs_le (p k A i : ℕ) (hp : 0 < p) (hi : i < k) :
    |pass5Digit p k A i| ≤ pass5H k := by
  obtain ⟨h0,h1⟩ := pass5Raw_bounds 12 p k A i (by norm_num) hp hi
  apply sineDigit_centered_bound _ _ _ (pass5Theta_pos k (by omega)) h0
  unfold pass5H
  linarith

theorem pass5Digit_step (p k A i : ℕ) (hp : 0 < p) (hi : i+1 < k) :
    (853589/960000 : ℝ) < pass5Digit p k A (i+1)-pass5Digit p k A i := by
  have hk : 2 ≤ k := by omega
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨hx0,hx1⟩ := pass5Raw_bounds 12 p k A i (by norm_num) hp (by omega)
  obtain ⟨hy0,hy1⟩ := pass5Raw_bounds 12 p k A (i+1) (by norm_num) hp hi
  have hgap := pass5Raw_step 12 p k A i (by norm_num) hp
  have hh0 := (pass5H_pos k hk).le
  have hh1 : pass5H k ≤ (k : ℝ)/2 := by unfold pass5H; linarith
  have hy : pass5Raw 12 p k A (i+1) ≤ 2*pass5H k := by unfold pass5H; linarith
  have h := pass5_sine_digit_step (49/100) (k : ℝ) (pass5H k) (1-1/12)
    (pass5Raw 12 p k A i) (pass5Raw 12 p k A (i+1))
    (by norm_num) (by norm_num) hk' hh0 hh1 (by norm_num) hx0 hy hgap
  norm_num only [show (1-1/(12 : ℝ))*(1-(49/100 : ℝ)^2/8) = 853589/960000 by norm_num] at h
  exact h

/-- The upper sine derivative never exceeds one. -/
theorem pass5_sineDigit_upper_difference (θ h x y : ℝ) (hθ : θ ≠ 0) (hxy : x ≤ y) :
    sineDigit θ h y-sineDigit θ h x ≤ y-x := by
  have hd (z : ℝ) := hasDerivAt_sineDigit θ h z hθ
  have hh := image_sub_le_mul_sub_of_deriv_le (fun z => (hd z).differentiableAt)
    (fun z => by rw [(hd z).deriv]; exact Real.cos_le_one _) hxy
  simpa using hh

theorem pass5Digit_span (p k A : ℕ) (hp : 0 < p) (hk : 2 ≤ k) :
    pass5Digit p k A (k-1)-pass5Digit p k A 0 < (k : ℝ)-11/12 := by
  have hx : pass5Raw 12 p k A 0 = 0 := by simp [pass5Raw, pass5Ruler]
  obtain ⟨hy0,hy1⟩ := pass5Raw_bounds 12 p k A (k-1) (by norm_num) hp (by omega)
  have hxy : pass5Raw 12 p k A 0 ≤ pass5Raw 12 p k A (k-1) := by rw [hx]; exact hy0
  have h := pass5_sineDigit_upper_difference (pass5Theta k) (pass5H k)
    (pass5Raw 12 p k A 0) (pass5Raw 12 p k A (k-1))
    (pass5Theta_pos k (by omega)).ne' hxy
  unfold pass5Digit
  rw [hx] at h ⊢
  linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Parameters.lean
section

/-! Exact scalar certificates for the orthogonal-circle fifth-pass manuscript.
These results prove the numerical hypotheses; they do not assert existence
of the geometric configuration supplied by the finite criterion. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Offset (m : ℕ) : ℕ :=
  ⌈(m : ℝ) * ((m : ℝ) - 1) / 64⌉₊

noncomputable def pass5Tau (m : ℕ) : ℝ :=
  Real.sqrt (1 - 1 / ((9 / 8 : ℝ) * ((pass5Offset m : ℝ) + 1)))

/-- The chosen harmonic reserve is valid throughout the new parameter range. -/
theorem pass5_harmonic_linear_bound {m : ℕ} (hm : 18177 ≤ m) :
    (harmonic m : ℝ) ≤ (m : ℝ) / 1100 := by
  induction m, hm using Nat.le_induction with
  | base =>
      have hlog : Real.log (18177 : ℝ) ≤ Real.log ((2 : ℝ)^15) := by
        rw [Real.log_le_log_iff (by norm_num) (by positivity)]
        norm_num
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h ⊢
        exact h
      have hH := harmonic_le_one_add_log 18177
      change (harmonic 18177 : ℝ) ≤ 1 + Real.log (18177 : ℝ) at hH
      change (harmonic 18177 : ℝ) ≤ (18177 : ℝ) / 1100
      rw [Real.log_pow] at hlog
      norm_num at hlog
      nlinarith
  | succ m hm ih =>
      have hden : (1100 : ℝ) ≤ (m+1 : ℕ) := by
        exact_mod_cast (show 1100 ≤ m+1 by omega)
      have hi : ((m+1 : ℕ) : ℝ)⁻¹ ≤ (1/1100 : ℝ) := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1100) hden
      rw [harmonic_succ]
      push_cast
      push_cast at hi
      linarith

theorem pass5Offset_lower (m : ℕ) :
    (m : ℝ) * ((m : ℝ) - 1) / 64 ≤ (pass5Offset m : ℝ) :=
  Nat.le_ceil _

theorem pass5Offset_upper (m : ℕ) (hm : 1 ≤ m) :
    (pass5Offset m : ℝ) < (m : ℝ) * ((m : ℝ) - 1) / 64 + 1 := by
  apply Nat.ceil_lt_add_one
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  positivity

theorem pass5Offset_ge_284_mul (m : ℕ) (hm : 18177 ≤ m) :
    284 * (m : ℝ) ≤ (pass5Offset m : ℝ) := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have h := pass5Offset_lower m
  nlinarith

theorem pass5Offset_add_m_upper (m : ℕ) (hm : 18177 ≤ m) :
    (pass5Offset m : ℝ) + m ≤ (m : ℝ)^2 / 63 := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have h := pass5Offset_upper m (by omega)
  nlinarith

theorem pass5Offset_harmonic_reserve (m : ℕ) (hm : 18177 ≤ m) :
    16384 * (harmonic m : ℝ)^2 ≤ (pass5Offset m : ℝ) := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have hH0 : (0 : ℝ) ≤ harmonic m := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic m by unfold harmonic; positivity)
  have hH := pass5_harmonic_linear_bound hm
  have hHsq : (harmonic m : ℝ)^2 ≤ ((m : ℝ)/1100)^2 := by nlinarith
  have hK := pass5Offset_lower m
  nlinarith

/-- The tolerance is bounded by an exact rational lower certificate. -/
theorem pass5Tau_bounds (m : ℕ) (hm : 18177 ≤ m) :
    (9999/10000 : ℝ) < pass5Tau m ∧ pass5Tau m < 1 := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have hK := pass5Offset_ge_284_mul m hm
  have hden : 0 < (9/8 : ℝ) * ((pass5Offset m : ℝ)+1) := by positivity
  have hrecip : 1 / ((9/8 : ℝ) * ((pass5Offset m : ℝ)+1)) <
      (19999/100000000 : ℝ) := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hrecip0 : 0 < 1 / ((9/8 : ℝ) * ((pass5Offset m : ℝ)+1)) :=
    one_div_pos.mpr hden
  unfold pass5Tau
  constructor
  · apply (Real.lt_sqrt (by norm_num)).2
    nlinarith
  · apply (Real.sqrt_lt (by linarith) (by norm_num)).2
    linarith

/-- All five finite-criterion inequalities at the exact concrete parameters.
The conjunction includes parameter admissibility and the actual derived tolerance. -/
theorem pass5_five_conditions (m : ℕ) (hm : 18177 ≤ m) :
    0 < pass5Tau m ∧ pass5Tau m < 1 ∧
    1 < pass5Tau m * (9/8 : ℝ) * (853589/960000 : ℝ) ∧
    max (m : ℝ) (16384 * (harmonic m : ℝ)^2) ≤ (pass5Offset m : ℝ) ∧
    4 * 101 * (m : ℝ) / (9/8 : ℝ)^3 ≤ (pass5Offset m : ℝ) ∧
    84 * (9/8 : ℝ)^2 / (49/100 : ℝ) *
      Real.sqrt ((pass5Offset m : ℝ) + m) ≤ 101 * (m : ℝ) ∧
    4 * (12 : ℝ) < 101 * (49/100 : ℝ) * (77599/80000 : ℝ) := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have hK := pass5Offset_ge_284_mul m hm
  have hH := pass5Offset_harmonic_reserve m hm
  have hupper := pass5Offset_add_m_upper m hm
  have hs0 := Real.sqrt_nonneg ((pass5Offset m : ℝ) + m)
  have hsq := Real.sq_sqrt (show 0 ≤ (pass5Offset m : ℝ) + m by positivity)
  refine ⟨by linarith, ht1, ?_, max_le (by linarith) hH, ?_, ?_, ?_⟩
  · nlinarith
  · norm_num at *
    linarith
  · have hs : Real.sqrt ((pass5Offset m : ℝ) + m) ≤ (m : ℝ)/7 := by
      nlinarith
    norm_num at *
    nlinarith
  · norm_num

/-- The rational definitions of kappa, gamma, and lambda are exact. -/
theorem pass5_digit_constants :
    (1 - 1/(12 : ℝ)) = 11/12 ∧
    (1 - (49/100 : ℝ)^2/8) = 77599/80000 ∧
    (1 - 1/(12 : ℝ)) * (1 - (49/100 : ℝ)^2/8) = 853589/960000 := by
  norm_num

/-- The finite-criterion diameter is strictly below the manuscript's leading
coefficient, without yet invoking the geometric finite criterion. -/
theorem pass5_finite_diameter_bound (m k : ℕ) (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    ((9/8 : ℝ)^3 * ((pass5Offset m : ℝ) + (m.choose 2 : ℝ)) +
      (9/8 : ℝ)^2 / (2 * pass5Tau m)) * (k : ℝ)^2 <
      (24057/32768 : ℝ) * ((m : ℝ) * k)^2 := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK := pass5Offset_upper m (by omega)
  have ht := (pass5Tau_bounds m hm).1
  have ht0 : 0 < pass5Tau m := by linarith
  have hrecip : (9/8 : ℝ)^2 / (2 * pass5Tau m) <
      (9/8 : ℝ)^2 / (2 * (9999/10000 : ℝ)) := by
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num)
    linarith
  have hcoeff : (9/8 : ℝ)^3 * ((pass5Offset m : ℝ) + (m.choose 2 : ℝ)) +
      (9/8 : ℝ)^2 / (2 * pass5Tau m) < (24057/32768 : ℝ)*(m : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  have h := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos (by linarith : (0 : ℝ) < k))
  nlinarith only [h]

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5GeometryParameters.lean
section

/-! The concrete circle scales discharge the macro/completion scalar gates.
This module constructs no points; the geometry source is kept separate. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5CircleTheta (k : ℕ) : ℝ := (49/100 : ℝ) / k
noncomputable def pass5Scale (k : ℕ) : ℝ := (9/8 : ℝ)^3 * (k : ℝ)^2
noncomputable def pass5Radius (m k : ℕ) : ℝ := 101 * (m : ℝ) * (k : ℝ)^2

theorem pass5_scale_pos {k : ℕ} (hk : 2 ≤ k) : 0 < pass5Scale k := by
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold pass5Scale
  positivity

theorem pass5_theta_pos {k : ℕ} (hk : 2 ≤ k) : 0 < pass5CircleTheta k := by
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold pass5CircleTheta
  positivity

theorem pass5_radius_pos {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    0 < pass5Radius m k := by
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold pass5Radius
  positivity

theorem pass5_radius_scale {m k : ℕ} (hk : 2 ≤ k) :
    pass5Radius m k / pass5Scale k = 101 * (m : ℝ) / (9/8 : ℝ)^3 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold pass5Radius pass5Scale
  field_simp
  <;> ring

theorem pass5_flattening_gate {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    (pass5Radius m k / pass5Scale k)^2 ≤ (pass5Offset m : ℝ)^2/16 := by
  have hK := pass5Offset_ge_284_mul m hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hK0 : (0 : ℝ) ≤ pass5Offset m := Nat.cast_nonneg _
  have hratio : 4 * (101 * (m : ℝ)/(9/8 : ℝ)^3) ≤ (pass5Offset m : ℝ) := by
    norm_num at *
    linarith
  rw [pass5_radius_scale hk]
  have hsq := mul_self_le_mul_self
    (by positivity : 0 ≤ 4*(101*(m : ℝ)/(9/8 : ℝ)^3)) hratio
  nlinarith only [hsq]

theorem pass5_completion_gate {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    7056*((9/8 : ℝ)/pass5CircleTheta k)^2*((9/8 : ℝ)*k)^2 *
      ((pass5Offset m : ℝ)+(m : ℝ)) ≤ (pass5Radius m k)^2 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hcond := (pass5_five_conditions m hm).2.2.2.2.2.1
  have hcond0 : 0 ≤ 84*(9/8 : ℝ)^2/(49/100 : ℝ) *
      Real.sqrt ((pass5Offset m : ℝ)+m) := by positivity
  have hsq := mul_self_le_mul_self hcond0 hcond
  have hsqrt := Real.sq_sqrt (show 0 ≤ (pass5Offset m : ℝ)+(m : ℝ) by positivity)
  have hcoeff : (84*(9/8 : ℝ)^2/(49/100 : ℝ))^2 *
      ((pass5Offset m : ℝ)+m) ≤ (101*(m : ℝ))^2 := by
    nlinarith only [hsq, hsqrt]
  have heq : 7056*((9/8 : ℝ)/pass5CircleTheta k)^2*((9/8 : ℝ)*k)^2 =
      (84*(9/8 : ℝ)^2/(49/100 : ℝ))^2 * (k : ℝ)^4 := by
    unfold pass5CircleTheta
    field_simp
    <;> ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ (k : ℝ)^4)
  unfold pass5Radius
  nlinarith only [h]

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Local.lean
section

/-! Exact local-circle length bounds for the fifth-pass parameters. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Chord (R θ D x : ℝ) : ℝ := 2*R*Real.sin (θ*x/(2*D))

theorem hasDerivAt_pass5Chord (R θ D x : ℝ) (hD : D ≠ 0) :
    HasDerivAt (pass5Chord R θ D)
      (R*θ/D*Real.cos (θ*x/(2*D))) x := by
  have h := ((((hasDerivAt_id x).const_mul θ).div_const (2*D)).sin).const_mul (2*R)
  have he : 2*R*(Real.cos (θ*x/(2*D))*(θ*1/(2*D))) =
      R*θ/D*Real.cos (θ*x/(2*D)) := by field_simp <;> ring
  convert h using 1 <;> first | rfl | exact he.symm

theorem pass5Chord_lower_difference (R θ D a Y x y : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hD : 0 < D) (ha : 0 ≤ a)
    (hscale : θ*Y ≤ a*D) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    (R*θ/D)*(1-a^2/8)*(y-x) ≤ pass5Chord R θ D y-pass5Chord R θ D x := by
  have hd (z : ℝ) := hasDerivAt_pass5Chord R θ D z hD.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  have harg0 : 0 ≤ θ*z/(2*D) :=
    div_nonneg (mul_nonneg hθ.le hz'.1) (by positivity)
  have harg : θ*z/(2*D) ≤ a/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*D)).2
    nlinarith [mul_le_mul_of_nonneg_left hz'.2 hθ.le]
  have harg2 : (θ*z/(2*D))^2 ≤ a^2/4 := by nlinarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ*z/(2*D))
  have hcos' : 1-a^2/8 ≤ Real.cos (θ*z/(2*D)) := by nlinarith
  rw [(hd z).deriv]
  exact mul_le_mul_of_nonneg_left hcos' (by positivity)

theorem pass5Chord_upper (R θ D x : ℝ) (hR : 0 < R) (hθ : 0 < θ)
    (hD : 0 < D) (hx : 0 ≤ x) : pass5Chord R θ D x ≤ (R*θ/D)*x := by
  have h := Real.sin_le (show 0 ≤ θ*x/(2*D) by positivity)
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*R by positivity)
  have he : 2*R*(θ*x/(2*D)) = (R*θ/D)*x := by field_simp <;> ring
  simpa only [pass5Chord, he] using hh

noncomputable def pass5LocalLength (m k p A i δ : ℕ) : ℝ :=
  pass5Chord (pass5Radius m k) (pass5Theta k) (12*(p : ℝ))
    (pass5RulerGap 12 p k A i δ : ℝ)

theorem pass5Radius_pos (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    0 < pass5Radius m k := by unfold pass5Radius; positivity

/-- The tiny strict C5 margin is retained exactly. -/
theorem pass5_local_slope_gt_one (m k p : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) :
    1 < (pass5Radius m k * pass5Theta k / (12*(p : ℝ))) * (1-(49/100 : ℝ)^2/8) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hup : (p : ℝ) < 4*(m : ℝ)*(k : ℝ) := by exact_mod_cast hpup
  have he : (pass5Radius m k * pass5Theta k / (12*(p : ℝ))) *
      (1-(49/100 : ℝ)^2/8) =
      (384037451/8000000 : ℝ) * ((m : ℝ)*k) / (12*(p : ℝ)) := by
    unfold pass5Radius pass5Theta
    field_simp <;> ring
  rw [he]
  apply (lt_div_iff₀ (by positivity : 0 < 12*(p : ℝ))).2
  nlinarith [mul_pos hm' hk']

theorem pass5_ruler_gap_bounds (p k A i δ : ℕ) (hp : 0 < p)
    (hδ : 0 < δ) (hi : i+δ < k) :
    1 ≤ (pass5RulerGap 12 p k A i δ : ℝ) ∧
    (pass5RulerGap 12 p k A i δ : ℝ) < 12*(p : ℝ)*k := by
  have hpos := pass5RulerGap_pos 12 p k A i δ hp (by norm_num) hδ
  have h1 : (1 : ℤ) ≤ pass5RulerGap 12 p k A i δ := by omega
  have hup := (pass5RulerGap_window 12 p k A i δ hp).2
  have hup' : (pass5RulerGap 12 p k A i δ : ℝ) < (12*(δ : ℝ)+1)*p := by
    exact_mod_cast hup
  have hδ' : (δ : ℝ)+1 ≤ k := by exact_mod_cast (show δ+1 ≤ k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  exact ⟨by exact_mod_cast h1, by nlinarith⟩

/-- Every source chord increases by more than one over a real gap of at least one. -/
theorem pass5_source_chord_gap (m k p : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) (x y : ℝ)
    (hx : 0 ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 12*(p : ℝ)*k) :
    1 < pass5Chord (pass5Radius m k) (pass5Theta k) (12*(p : ℝ)) y -
      pass5Chord (pass5Radius m k) (pass5Theta k) (12*(p : ℝ)) x := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hs : pass5Theta k * (12*(p : ℝ)*k) = (49/100 : ℝ)*(12*(p : ℝ)) := by
    unfold pass5Theta
    field_simp <;> ring
  have h := pass5Chord_lower_difference (pass5Radius m k) (pass5Theta k)
    (12*(p : ℝ)) (49/100) (12*(p : ℝ)*k) x y
    (pass5Radius_pos m k hm hk) (pass5Theta_pos k hk) (by positivity) (by norm_num)
    hs.le hx (by linarith) hy
  have hslope := pass5_local_slope_gt_one m k p hm hk hp hpup
  nlinarith

/-- Every local edge has length strictly greater than one. -/
theorem pass5LocalLength_gt_one (m k p A i δ : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) (hδ : 0 < δ) (hi : i+δ < k) :
    1 < pass5LocalLength m k p A i δ := by
  obtain ⟨hlo,hup⟩ := pass5_ruler_gap_bounds p k A i δ hp hδ hi
  have h := pass5_source_chord_gap m k p hm hk hp hpup 0
    (pass5RulerGap 12 p k A i δ : ℝ) (by norm_num) (by simpa using hlo) hup.le
  simpa [pass5LocalLength, pass5Chord] using h

/-- Source local lengths lie below the local-versus-cross guard. -/
theorem pass5LocalLength_upper (m k p A i δ : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hδ : 0 < δ) (hi : i+δ < k) :
    pass5LocalLength m k p A i δ < (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2 := by
  obtain ⟨hlo,hup⟩ := pass5_ruler_gap_bounds p k A i δ hp hδ hi
  have hR := pass5Radius_pos m k hm hk
  have hθ := pass5Theta_pos k hk
  have hD : 0 < 12*(p : ℝ) := by positivity
  have h := pass5Chord_upper (pass5Radius m k) (pass5Theta k) (12*(p : ℝ))
    (pass5RulerGap 12 p k A i δ : ℝ) hR hθ hD (by linarith)
  have hh := mul_lt_mul_of_pos_left hup (show 0 < pass5Radius m k*pass5Theta k/(12*(p : ℝ)) by positivity)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have he : (pass5Radius m k*pass5Theta k/(12*(p : ℝ))) * (12*(p : ℝ)*k) =
      (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2 := by
    unfold pass5Radius pass5Theta
    field_simp <;> ring
  rw [he] at hh
  exact h.trans_lt hh

/-- Local/local separation across all clusters, using actual prime-ruler uniqueness. -/
theorem pass5LocalLength_separated (m k p A B i j δ ε : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hp : p.Prime)
    (hsize : 2*m*k < p) (hpup : p < 4*m*k)
    (hA : A < m) (hB : B < m) (hδ : 0 < δ) (hε : 0 < ε)
    (hδp : δ < p) (hεp : ε < p) (hi : i+δ < k) (hj : j+ε < k)
    (hne : ¬ (A=B ∧ i=j ∧ δ=ε)) :
    1 < |pass5LocalLength m k p A i δ-pass5LocalLength m k p B j ε| := by
  have hneq : pass5RulerGap 12 p k A i δ ≠ pass5RulerGap 12 p k B j ε := by
    intro he
    exact hne (pass5RulerGap_injective 12 p m k δ ε A B i j hp (by norm_num)
      hδ hε hδp hεp hsize hA hB hi hj he)
  obtain ⟨hlo1,hup1⟩ := pass5_ruler_gap_bounds p k A i δ hp.pos hδ hi
  obtain ⟨hlo2,hup2⟩ := pass5_ruler_gap_bounds p k B j ε hp.pos hε hj
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hd : (1 : ℤ) ≤ pass5RulerGap 12 p k B j ε-pass5RulerGap 12 p k A i δ := by omega
    have hd' : (1 : ℝ) ≤ (pass5RulerGap 12 p k B j ε : ℝ)-
        (pass5RulerGap 12 p k A i δ : ℝ) := by exact_mod_cast hd
    have h := pass5_source_chord_gap m k p hm hk hp.pos hpup _ _ (by linarith) hd' hup2.le
    change 1 < pass5LocalLength m k p B j ε-pass5LocalLength m k p A i δ at h
    have hh := le_abs_self (pass5LocalLength m k p B j ε-pass5LocalLength m k p A i δ)
    rw [abs_sub_comm] at hh
    exact h.trans_le hh
  · have hd : (1 : ℤ) ≤ pass5RulerGap 12 p k A i δ-pass5RulerGap 12 p k B j ε := by omega
    have hd' : (1 : ℝ) ≤ (pass5RulerGap 12 p k A i δ : ℝ)-
        (pass5RulerGap 12 p k B j ε : ℝ) := by exact_mod_cast hd
    have h := pass5_source_chord_gap m k p hm hk hp.pos hpup _ _ (by linarith) hd' hup1.le
    exact h.trans_le (le_abs_self _)


/-- The actual source angle on each circle. -/
noncomputable def pass5Angle (p k A i : ℕ) : ℝ :=
  pass5Theta k * (pass5Raw 12 p k A i-pass5H k)

theorem pass5Angle_sine (p k A i : ℕ) (hk : 0 < k) :
    Real.sin (pass5Angle p k A i) = pass5Theta k*pass5Digit p k A i := by
  have hθ := (pass5Theta_pos k hk).ne'
  unfold pass5Angle pass5Digit sineDigit
  field_simp

theorem pass5Angle_difference (p k A i δ : ℕ) :
    (pass5Angle p k A (i+δ)-pass5Angle p k A i)/2 =
      pass5Theta k*(pass5RulerGap 12 p k A i δ : ℝ)/(2*(12*(p : ℝ))) := by
  unfold pass5Angle pass5Raw pass5RulerGap
  push_cast
  ring

/-- The positive local chord agrees with the absolute-sine distance identity
returned by the Euclidean circle geometry module. -/
theorem pass5LocalLength_eq_abs_chord (m k p A i δ : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hp : 0 < p) (hpup : p < 4*m*k)
    (hδ : 0 < δ) (hi : i+δ < k) :
    2*pass5Radius m k*|Real.sin ((pass5Angle p k A (i+δ)-pass5Angle p k A i)/2)| =
      pass5LocalLength m k p A i δ := by
  have hmin := pass5LocalLength_gt_one m k p A i δ hm hk hp hpup hδ hi
  have hR := pass5Radius_pos m k hm hk
  have hsin : 0 < Real.sin (pass5Theta k*(pass5RulerGap 12 p k A i δ : ℝ)/(2*(12*(p : ℝ)))) := by
    apply (mul_pos_iff_of_pos_left (show 0 < 2*pass5Radius m k by positivity)).1
    exact lt_trans zero_lt_one hmin
  rw [pass5Angle_difference, abs_of_pos hsin]
  rfl

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From TrigBounds.lean
section

namespace Erdos670R29

/-- Three angle doublings sharpen the elementary quadratic cosine bound.
This avoids adding an unformalized Taylor remainder estimate. -/
theorem cos_ruler_lower : (255/400 : ℝ) ≤ Real.cos (879/1000) := by
  have h0 := Real.one_sub_sq_div_two_le_cos (x := (879/8000 : ℝ))
  have h0' : (993963/1000000 : ℝ) ≤ Real.cos (879/8000) := by norm_num at h0 ⊢; linarith
  have e1 := Real.cos_two_mul (879/8000 : ℝ)
  have e2 := Real.cos_two_mul (879/4000 : ℝ)
  have e3 := Real.cos_two_mul (879/2000 : ℝ)
  norm_num at e1 e2 e3
  have h1 : (975924/1000000 : ℝ) ≤ Real.cos (879/4000) := by
    nlinarith [sq_nonneg (Real.cos (879/8000)-(993963/1000000 : ℝ))]
  have h2 : (904855/1000000 : ℝ) ≤ Real.cos (879/2000) := by
    nlinarith [sq_nonneg (Real.cos (879/4000)-(975924/1000000 : ℝ))]
  nlinarith [sq_nonneg (Real.cos (879/2000)-(904855/1000000 : ℝ))]

theorem sin_ruler_lower : (7658/10000 : ℝ) ≤ Real.sin (879/1000) := by
  have h := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 879/1000)
  norm_num at h ⊢
  linarith

theorem sin_ruler_upper : Real.sin (879/1000) ≤ (78/100 : ℝ) := by
  have h := Real.sin_sq_add_cos_sq (879/1000 : ℝ)
  have hc := cos_ruler_lower
  nlinarith [sq_nonneg (Real.cos (879/1000)-(255/400 : ℝ))]




end Erdos670R29

end

-- From LocalNorm.lean
section

namespace Erdos670R29

/-- A denominator-free lower secant bound for a two-coordinate norm. -/
theorem norm_secant_lower (H x y lam : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hbudget : lam^2*H^2 ≤ (1-lam^2)*x^2) :
    lam*(y-x) ≤ Real.sqrt (H^2+y^2)-Real.sqrt (H^2+x^2) := by
  let X := Real.sqrt (H^2+x^2)
  let Y := Real.sqrt (H^2+y^2)
  have hX : X^2 = H^2+x^2 := Real.sq_sqrt (by positivity)
  have hY : Y^2 = H^2+y^2 := Real.sq_sqrt (by positivity)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hxy2 : x^2 ≤ y^2 := sq_le_sq₀ hx (hx.trans hxy) |>.2 hxy
  have hl2 : 0 ≤ 1-lam^2 := by nlinarith
  have hby := mul_le_mul_of_nonneg_left hxy2 hl2
  have hlX : lam*X ≤ x := by nlinarith [mul_nonneg hlam hX0]
  have hlY : lam*Y ≤ y := by nlinarith [mul_nonneg hlam hY0]
  have hmono : X ≤ Y := Real.sqrt_le_sqrt (by nlinarith)
  by_cases hsum : X+Y=0
  · have : X=0 ∧ Y=0 := by constructor <;> linarith
    rcases this with ⟨hxx,hyy⟩
    have hxz : x=0 := by nlinarith [sq_nonneg H]
    have hyz : y=0 := by nlinarith [sq_nonneg H]
    change lam*(y-x) ≤ Y-X
    rw [hxz,hyz,hxx,hyy]
    simp
  have hsumpos : 0 < X+Y := by positivity
  change lam*(y-x) ≤ Y-X
  apply (mul_le_mul_iff_of_pos_right hsumpos).mp
  have hm := mul_le_mul_of_nonneg_right (add_le_add hlX hlY) (sub_nonneg.mpr hxy)
  nlinarith only [hm,hX,hY]

/-- A simple ray bound is sufficient for the local ratio budget. -/
theorem sin_ruler_ray (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 879/1000) :
    (87/100 : ℝ)*x ≤ Real.sin x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x; simp
  have hs := Real.sin_gt_sub_cube h
  have hx2 : x^2 ≤ (879/1000 : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hx2 hx
  nlinarith



end Erdos670R29

end

-- From LocalScalar.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def localH (k d : ℝ) : ℝ :=
  pass5Chord ((507/100)*k^2) ((519/1000)/k) 1 d
noncomputable def localB (k p g : ℝ) : ℝ :=
  pass5Chord ((1131/100)*k^2) ((879/500)/k) (2*p) g
noncomputable def localLength (k p d g : ℝ) : ℝ :=
  Real.sqrt ((localH k d)^2+(localB k p g)^2)

lemma chord_lower_cos (R θ D Y x y : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hD : 0 < D)
    (hscale : θ*Y ≤ (879/500)*D) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    (R*θ/D)*(255/400)*(y-x) ≤ pass5Chord R θ D y-pass5Chord R θ D x := by
  have hd (z : ℝ) := hasDerivAt_pass5Chord R θ D z hD.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  have harg0 : 0 ≤ θ*z/(2*D) := div_nonneg (mul_nonneg hθ.le hz'.1) (by positivity)
  have harg : θ*z/(2*D) ≤ (879/1000 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*D)).2
    nlinarith [mul_le_mul_of_nonneg_left hz'.2 hθ.le]
  have hpi : (879/1000 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have hcos := cos_ruler_lower.trans (Real.cos_le_cos_of_nonneg_of_le_pi harg0 hpi harg)
  rw [(hd z).deriv]
  exact mul_le_mul_of_nonneg_left hcos (by positivity)

lemma localB_slope (k p x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*p*k) :
    (5229/5000 : ℝ)*(y-x) ≤ localB k p y-localB k p x := by
  have hs : ((879/500)/k)*(2*p*k) = (879/500)*(2*p) := by field_simp <;> ring
  have h := chord_lower_cos ((1131/100)*k^2) ((879/500)/k) (2*p) (2*p*k) x y
    (by positivity) (by positivity) (by positivity) hs.le hx hxy hy
  have he : (((1131/100)*k^2)*((879/500)/k)/(2*p))*(255/400) =
      (50701599/8000000 : ℝ)*k/p := by field_simp <;> ring
  rw [he] at h
  have hl : (5229/5000 : ℝ) ≤ (50701599/8000000 : ℝ)*k/p := by
    apply (le_div_iff₀ hp).2
    nlinarith
  exact (mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hxy)).trans h

lemma localH_bounds (k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hdk : d ≤ k) :
    0 ≤ localH k d ∧ localH k d ≤ (263133/100000 : ℝ)*k*d := by
  have harg0 : 0 ≤ ((519/1000)/k)*d/(2*1) := by positivity
  have harg : ((519/1000)/k)*d/(2*1) ≤ (519/2000 : ℝ) := by
    field_simp
    nlinarith
  constructor
  · unfold localH pass5Chord
    apply mul_nonneg (by positivity)
    exact Real.sin_nonneg_of_nonneg_of_le_pi harg0 (harg.trans (by linarith [Real.two_le_pi]))
  · have h := pass5Chord_upper ((507/100)*k^2) ((519/1000)/k) 1 d
      (by positivity) (by positivity) (by norm_num) hd
    have he : ((507/100)*k^2)*((519/1000)/k)/1*d = (263133/100000 : ℝ)*k*d := by
      field_simp; ring
    simpa only [he, localH] using h

lemma localB_ray (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    (86490963/10000000 : ℝ)*k*d ≤ localB k p g := by
  have hg0 : 0 ≤ g := (mul_nonneg hp.le hd).trans hg
  have harg0 : 0 ≤ ((879/500)/k)*g/(2*(2*p)) := by positivity
  have he : ((879/500)/k)*g/(2*(2*p)) = (879/2000)*g/(p*k) := by field_simp <;> ring
  have harg : ((879/500)/k)*g/(2*(2*p)) ≤ (879/1000 : ℝ) := by
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < p*k)).2
    nlinarith
  have h := sin_ruler_ray _ harg0 harg
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*((1131/100 : ℝ)*k^2) by positivity)
  have hs : 2*((1131/100 : ℝ)*k^2)*((87/100)*(((879/500)/k)*g/(2*(2*p)))) =
      (86490963/10000000 : ℝ)*k*g/p := by field_simp <;> ring
  rw [hs] at hm
  have hl : (86490963/10000000 : ℝ)*k*d ≤ (86490963/10000000 : ℝ)*k*g/p := by
    apply (le_div_iff₀ hp).2
    nlinarith [mul_le_mul_of_nonneg_left hg (show 0 ≤ (86490963/10000000 : ℝ)*k by positivity)]
  exact hl.trans hm




end Erdos670R29

end

-- From LocalSeparation.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma local_ratio_budget (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hdk : d ≤ k) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    (2391/2500 : ℝ)^2*(localH k d)^2 ≤
      (1-(2391/2500 : ℝ)^2)*(localB k p g)^2 := by
  obtain ⟨hH0,hH⟩ := localH_bounds k d hk hd hdk
  have hB := localB_ray k p d g hk hp hd hg hgup
  have hkd : 0 ≤ k*d := mul_nonneg hk.le hd
  have hHsq : (localH k d)^2 ≤ ((263133/100000 : ℝ)*(k*d))^2 := by
    apply (sq_le_sq₀ hH0 (by positivity)).2
    nlinarith only [hH]
  have hBsq : ((86490963/10000000 : ℝ)*(k*d))^2 ≤ (localB k p g)^2 := by
    apply (sq_le_sq₀ (by positivity) (by nlinarith only [hB,hkd])).2
    nlinarith only [hB]
  nlinarith [sq_nonneg (k*d)]

/-- Strict unit separation follows from an integer-sized ruler increment. -/
theorem local_fixed_lag_gap (k p d x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hd : 0 ≤ d) (hdk : d ≤ k)
    (hx : p*d ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 2*p*k) :
    1 < localLength k p d y-localLength k p d x := by
  have hxy : x ≤ y := by linarith
  have hx0 : 0 ≤ x := (mul_nonneg hp.le hd).trans hx
  have hs := localB_slope k p x y hk hp hpk hx0 hxy hy
  have hbx := localB_ray k p d x hk hp hd hx (hxy.trans hy)
  have hb0 : 0 ≤ localB k p x := by nlinarith [mul_nonneg hk.le hd]
  have hbxy : localB k p x ≤ localB k p y := by linarith
  have hb := local_ratio_budget k p d x hk hp hd hdk hx (hxy.trans hy)
  have hnorm := norm_secant_lower (localH k d) (localB k p x) (localB k p y)
    (2391/2500) hb0 hbxy (by norm_num) (by norm_num) hb
  unfold localLength
  nlinarith

lemma localH_monotone (k d e : ℝ) (hk : 0 < k)
    (hd : 0 ≤ d) (hde : d ≤ e) (hek : e ≤ k) : localH k d ≤ localH k e := by
  have hscale : ((519/1000)/k)*k ≤ (519/1000 : ℝ)*1 := by
    field_simp <;> norm_num
  have h := pass5Chord_lower_difference ((507/100)*k^2) ((519/1000)/k) 1
    (519/1000) k d e (by positivity) (by positivity) (by norm_num) (by norm_num)
    hscale hd hde hek
  have hcoef : 0 ≤ (((507/100)*k^2)*((519/1000)/k)/1)*(1-(519/1000 : ℝ)^2/8) := by
    apply mul_nonneg (by positivity)
    norm_num
  have hm := mul_nonneg hcoef (sub_nonneg.mpr hde)
  exact le_of_sub_nonneg (hm.trans h)

/-- The full real local comparison permits a nondecreasing lag. -/
theorem local_ordered_gap (k p d e x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hd : 0 ≤ d) (hde : d ≤ e) (hek : e ≤ k)
    (hx : p*d ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 2*p*k) :
    1 < localLength k p e y-localLength k p d x := by
  have h := local_fixed_lag_gap k p d x y hk hp hpk hd (hde.trans hek) hx hgap hy
  have hH := localH_monotone k d e hk hd hde hek
  have hH0 := (localH_bounds k d hk hd (hde.trans hek)).1
  have hs : (localH k d)^2 ≤ (localH k e)^2 := (sq_le_sq₀ hH0 (hH0.trans hH)).2 hH
  have hmono : localLength k p d y ≤ localLength k p e y :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith


end Erdos670R29

end

-- From LocalBounds.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma localB_bounds (k p g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hg : 0 ≤ g) (hgup : g ≤ 2*p*k) :
    0 ≤ localB k p g ∧ localB k p g ≤ (44109/2500 : ℝ)*k^2 := by
  have harg0 : 0 ≤ ((879/500)/k)*g/(2*(2*p)) := by positivity
  have he : ((879/500)/k)*g/(2*(2*p)) = (879/2000)*g/(p*k) := by field_simp <;> ring
  have harg : ((879/500)/k)*g/(2*(2*p)) ≤ (879/1000 : ℝ) := by
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < p*k)).2
    nlinarith
  have hpi : (879/1000 : ℝ) ≤ Real.pi/2 := by linarith [Real.two_le_pi]
  have hs := (Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ ((879/500)/k)*g/(2*(2*p)) by linarith [Real.pi_pos]) hpi harg).trans sin_ruler_upper
  constructor
  · unfold localB pass5Chord
    apply mul_nonneg (by positivity)
    exact Real.sin_nonneg_of_nonneg_of_le_pi harg0 (by linarith [Real.pi_pos])
  · have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*((1131/100 : ℝ)*k^2) by positivity)
    dsimp [localB,pass5Chord]
    nlinarith only [hm]

theorem localLength_upper (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hdk : d ≤ k) (hg : 0 ≤ g) (hgup : g ≤ 2*p*k) :
    localLength k p d g < 18*k^2 := by
  obtain ⟨hH0,hH⟩ := localH_bounds k d hk hd hdk
  obtain ⟨hB0,hB⟩ := localB_bounds k p g hk hp hg hgup
  have hH' : localH k d ≤ (263133/100000 : ℝ)*k^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hdk hk.le]
  have hHsq : (localH k d)^2 ≤ ((263133/100000 : ℝ)*k^2)^2 :=
    (sq_le_sq₀ hH0 (by positivity)).2 hH'
  have hBsq : (localB k p g)^2 ≤ ((44109/2500 : ℝ)*k^2)^2 :=
    (sq_le_sq₀ hB0 (by positivity)).2 hB
  have hroot : (localLength k p d g)^2 = (localH k d)^2+(localB k p g)^2 :=
    Real.sq_sqrt (by positivity)
  have hpos : 0 < k^4 := pow_pos hk 4
  have hk2 : 0 < k^2 := sq_pos_of_pos hk
  nlinarith

theorem localLength_min (k p d g : ℝ) (hk : 100 ≤ k) (hp : 0 < p)
    (hd : 1 ≤ d) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    1 < localLength k p d g := by
  have hk0 : 0 < k := by linarith
  have hb := localB_ray k p d g hk0 hp (by linarith) hg hgup
  have hkd : k ≤ k*d := by nlinarith
  have hs : (localLength k p d g)^2 = (localH k d)^2+(localB k p g)^2 :=
    Real.sq_sqrt (by positivity)
  have hn : 0 ≤ localLength k p d g := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (localH k d)]



end Erdos670R29

end

-- From SharpRulerNext.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Prime cancellation needs p > m*k, with the odd prime condition explicit. -/
theorem same_lag_residue_injective_sharp
    (p m k δ A B i j : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hδ : 0 < δ) (hδp : δ < p) (hsize : m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p) :
    A = B ∧ i = j := by
  have hcop : p.Coprime δ := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hδ hδp)
  have hmod : 2*i+δ+2*k*A ≡ 2*j+δ+2*k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hcop heq
  have hmod' : 2*(i+k*A)+δ ≡ 2*(j+k*B)+δ [MOD p] := by
    have hleft : 2*(i+k*A)+δ = 2*i+δ+2*k*A := by ring
    have hright : 2*(j+k*B)+δ = 2*j+δ+2*k*B := by ring
    simpa only [hleft, hright] using hmod
  have htwo : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) hp2)
  have hs : i+k*A ≡ j+k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime htwo (Nat.ModEq.add_right_cancel' δ hmod')
  have hleft : i+k*A < p := by
    have hh := Nat.mul_le_mul_left k (show A+1 ≤ m by omega)
    nlinarith
  have hright : j+k*B < p := by
    have hh := Nat.mul_le_mul_left k (show B+1 ≤ m by omega)
    nlinarith
  have he := hs.eq_of_lt_of_lt hleft hright
  have hab : A = B := by
    rcases lt_trichotomy A B with h | h | h
    · have hh := Nat.mul_le_mul_left k (show A+1 ≤ B by omega)
      nlinarith
    · exact h
    · have hh := Nat.mul_le_mul_left k (show B+1 ≤ A by omega)
      nlinarith
  exact ⟨hab, by subst B; omega⟩

/-- The actual integer gaps inherit the sharp prime-size condition. -/
theorem rulerGap_same_lag_injective_sharp (L p m k δ A B i j : ℕ)
    (hp : p.Prime) (hp2 : 2 < p) (hδ : 0 < δ) (hδp : δ < p)
    (hsize : m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+δ < k)
    (heq : pass5RulerGap L p k A i δ = pass5RulerGap L p k B j δ) :
    A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [pass5RulerGap_residue, pass5RulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective_sharp p m k δ A B i j hp hp2 hδ hδp hsize
    hA hB hi hj hnat



end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From LocalRuler.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma ruler_window_real (p k A i d : ℕ) (hp : 0 < p) (hd : 0 < d) (hi : i+d < k) :
    (p : ℝ)*d ≤ (pass5RulerGap 2 p k A i d : ℝ) ∧
    (pass5RulerGap 2 p k A i d : ℝ) ≤ 2*(p : ℝ)*k := by
  obtain ⟨hl,hu⟩ := pass5RulerGap_window 2 p k A i d hp
  have hl' : (2*(d : ℝ)-1)*p < (pass5RulerGap 2 p k A i d : ℝ) := by exact_mod_cast hl
  have hu' : (pass5RulerGap 2 p k A i d : ℝ) < (2*(d : ℝ)+1)*p := by exact_mod_cast hu
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdk : (d : ℝ)+1 ≤ k := by exact_mod_cast (show d+1 ≤ k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  constructor <;> nlinarith

lemma ruler_order_lag (p k A B i j d e : ℕ) (hp : 0 < p)
    (hgap : pass5RulerGap 2 p k A i d < pass5RulerGap 2 p k B j e) : d ≤ e := by
  by_contra h
  have he : e < d := by omega
  have hw := pass5RulerGap_different_lag 2 p k B A j i e d hp (by norm_num) he
  omega

lemma ruler_injective (p k A B i j d e : ℕ) (hp : p.Prime) (hk : 100 ≤ k)
    (hsize : 6*k < p) (hA : A < 6) (hB : B < 6)
    (hd : 0 < d) (he : 0 < e) (hi : i+d < k) (hj : j+e < k)
    (heq : pass5RulerGap 2 p k A i d = pass5RulerGap 2 p k B j e) :
    A=B ∧ i=j ∧ d=e := by
  have hde : d=e := by
    rcases lt_trichotomy d e with h | h | h
    · have hw := pass5RulerGap_different_lag 2 p k A B i j d e hp.pos (by norm_num) h
      omega
    · exact h
    · have hw := pass5RulerGap_different_lag 2 p k B A j i e d hp.pos (by norm_num) h
      omega
  subst e
  obtain ⟨hAB,hij⟩ := rulerGap_same_lag_injective_sharp 2 p 6 k d A B i j
    hp (by omega) hd (by omega) hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩

noncomputable def localEdge (p k A i j : ℕ) : ℝ :=
  localLength k p ((j-i : ℕ) : ℝ) (pass5RulerGap 2 p k A i (j-i))

theorem local_edges_separated (p k A B i j u v : ℕ) (hp : p.Prime) (hk : 100 ≤ k)
    (hsize : 6*k < p) (hpup : 100*p ≤ 606*k) (hA : A < 6) (hB : B < 6)
    (hij : i < j) (huv : u < v) (hj : j < k) (hv : v < k)
    (hne : ¬ (A=B ∧ i=u ∧ j=v)) :
    1 < |localEdge p k A i j-localEdge p k B u v| := by
  have hdi : i+(j-i) < k := by omega
  have hdu : u+(v-u) < k := by omega
  have hd : 0 < j-i := by omega
  have he : 0 < v-u := by omega
  have hgneq : pass5RulerGap 2 p k A i (j-i) ≠ pass5RulerGap 2 p k B u (v-u) := by
    intro h
    obtain ⟨hAB,hi,hde⟩ := ruler_injective p k A B i u (j-i) (v-u) hp hk hsize hA hB hd he hdi hdu h
    apply hne
    exact ⟨hAB,hi,by omega⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpk : (p : ℝ) ≤ (303/50)*(k : ℝ) := by
    have h : (100 : ℝ)*p ≤ 606*k := by exact_mod_cast hpup
    linarith
  have ordered (A B i u d e : ℕ) (hd : 0 < d) (he : 0 < e)
      (hdi : i+d < k) (hdu : u+e < k)
      (hgap : pass5RulerGap 2 p k A i d < pass5RulerGap 2 p k B u e) :
      1 < localLength k p e (pass5RulerGap 2 p k B u e)-
        localLength k p d (pass5RulerGap 2 p k A i d) := by
    have hde := ruler_order_lag p k A B i u d e hp.pos hgap
    have hgap' : (1 : ℝ) ≤ (pass5RulerGap 2 p k B u e : ℝ)-(pass5RulerGap 2 p k A i d : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ pass5RulerGap 2 p k B u e-pass5RulerGap 2 p k A i d by omega)
    exact local_ordered_gap k p d e _ _ hk' hp' hpk (by positivity)
      (by exact_mod_cast hde) (by exact_mod_cast (show e ≤ k by omega))
      (ruler_window_real p k A i d hp.pos hd hdi).1 hgap'
      (ruler_window_real p k B u e hp.pos he hdu).2
  rcases lt_or_gt_of_ne hgneq with h | h
  · have hh := ordered A B i u (j-i) (v-u) hd he hdi hdu h
    unfold localEdge
    rw [abs_of_neg (by linarith)]
    linarith
  · have hh := ordered B A u i (v-u) (j-i) he hd hdu hdi h
    unfold localEdge
    rw [abs_of_pos (by linarith)]
    exact hh


end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SpectrumSeparation.lean
section

/-! The finite ordering layer only. No Euclidean realization or local-distance
geometry is assumed proved by this file. Every scalar guard is explicit. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Sum adjacent unit gaps over a bounded natural index interval. -/
theorem bounded_step_sum (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i) :
    ∀ i j, i ≤ j → j < N → (j : ℝ) - (i : ℝ) ≤ f j - f i := by
  intro i j
  induction j with
  | zero =>
      intro hij _
      have hi : i = 0 := by omega
      subst i
      simp
  | succ j ih =>
      intro hij hj
      by_cases h : i ≤ j
      · have h1 := ih h (by omega)
        have h2 := hstep j hj
        push_cast
        linarith
      · have hi : i = j + 1 := by omega
        subst i
        simp

/-- Adjacent unit gaps imply weak monotonicity, including equal endpoints. -/
theorem bounded_step_mono (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i)
    {i j : ℕ} (hij : i ≤ j) (hj : j < N) : f i ≤ f j := by
  have h := bounded_step_sum f N hstep i j hij hj
  have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- A nonempty chain of adjacent unit gaps has gap at least one. -/
theorem bounded_step_gap (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i)
    {i j : ℕ} (hij : i < j) (hj : j < N) : 1 ≤ f j - f i := by
  have h := bounded_step_sum f N hstep i j (by omega) hj
  have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  linarith

/-- Fine-digit gaps and last-to-first carries order the entire rectangular block.
The carry hypothesis is on the last fine digit, not on equal fine digits. -/
theorem rectangular_lex_gap (F : ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b a' b' : ℕ} (ha : a < M) (hb : b < k) (ha' : a' < M) (hb' : b' < k)
    (hlex : a < a' ∨ (a = a' ∧ b < b')) : 1 ≤ F a' b' - F a b := by
  have hrow (c : ℕ) (hc : c < M) {i j : ℕ} (hij : i ≤ j) (hj : j < k) :
      F c i ≤ F c j := bounded_step_mono (F c) k (hfine c hc) hij hj
  have hfirst : ∀ c, c + 1 < M → 1 ≤ F (c + 1) 0 - F c 0 := by
    intro c hc
    have h1 := hrow c (by omega) (show 0 ≤ k - 1 by omega) (by omega)
    have h2 := hcarry c hc
    linarith
  rcases hlex with haa | ⟨rfl, hbb⟩
  · have h1 := hrow a ha (show b ≤ k - 1 by omega) (by omega)
    have h2 := hcarry a (by omega)
    have h3 := bounded_step_mono (fun c => F c 0) M hfirst
      (show a + 1 ≤ a' by omega) ha'
    have h4 := hrow a' ha' (show 0 ≤ b' by omega) hb'
    linarith
  · exact bounded_step_gap (F a) k (hfine a ha) hbb hb'

/-- All distinct cells, not just adjacent cells, are separated. -/
theorem rectangular_all_pairs_separated (F : ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b a' b' : ℕ} (ha : a < M) (hb : b < k) (ha' : a' < M) (hb' : b' < k)
    (hne : (a,b) ≠ (a',b')) : 1 ≤ |F a b - F a' b'| := by
  by_cases hlex : a < a' ∨ (a = a' ∧ b < b')
  · have h := rectangular_lex_gap F M k hk hfine hcarry ha hb ha' hb' hlex
    have habs := le_abs_self (F a' b' - F a b)
    rw [abs_sub_comm] at habs
    linarith
  · have hrev : a' < a ∨ (a' = a ∧ b' < b) := by
      have hn : a ≠ a' ∨ b ≠ b' := by
        by_contra h
        push Not at h
        exact hne (by rcases h with ⟨rfl,rfl⟩; rfl)
      omega
    have h := rectangular_lex_gap F M k hk hfine hcarry ha' hb' ha hb hrev
    exact h.trans (le_abs_self _)

/-- The scalar fine-digit guard, retaining an explicit adjacent error difference. -/
theorem fine_step_guard (s r Flip f₀ f₁ e₀ e₁ : ℝ)
    (hf : s*r ≤ f₁-f₀) (he : |e₁-e₀| ≤ Flip)
    (hguard : 1 ≤ s*r-Flip) : 1 ≤ (f₁+e₁)-(f₀+e₀) := by
  have h := (abs_le.mp he).1
  linarith

/-- The scalar carry guard uses a full k-step error budget. -/
theorem carry_step_guard (s c r fstar Flip coarse₀ coarse₁ fine₀ fineLast e₀ e₁ : ℝ)
    (k : ℕ) (hc : s*c*r ≤ coarse₁-coarse₀)
    (hf : fineLast-fine₀ ≤ 2*s*fstar) (he : |e₁-e₀| ≤ k*Flip)
    (hguard : 1 ≤ s*(c*r-2*fstar)-k*Flip) :
    1 ≤ (coarse₁+fine₀+e₁)-(coarse₀+fineLast+e₀) := by
  have h := (abs_le.mp he).1
  nlinarith

/-- Macro blocks stay separate after both endpoint perturbations and errors. -/
theorem coarse_step_guard (S A E base₀ base₁ perturb₀ perturb₁ error₀ error₁ : ℝ)
    (hbase : S ≤ base₁-base₀) (hp₀ : |perturb₀| ≤ A) (hp₁ : |perturb₁| ≤ A)
    (he₀ : |error₀| ≤ E) (he₁ : |error₁| ≤ E) (hguard : 1 ≤ S-2*A-2*E) :
    1 ≤ (base₁+perturb₁+error₁)-(base₀+perturb₀+error₀) := by
  rcases abs_le.mp hp₀ with ⟨_,hp₀⟩
  rcases abs_le.mp hp₁ with ⟨hp₁,_⟩
  rcases abs_le.mp he₀ with ⟨_,he₀⟩
  rcases abs_le.mp he₁ with ⟨he₁,_⟩
  linarith

/-- A rectangular block has its first and last entries as genuine extrema. -/
theorem rectangular_endpoints (F : ℕ → ℕ → ℝ) (M k : ℕ) (hM : 0 < M) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b : ℕ} (ha : a < M) (hb : b < k) :
    F 0 0 ≤ F a b ∧ F a b ≤ F (M - 1) (k - 1) := by
  constructor
  · by_cases hz : a = 0 ∧ b = 0
    · rcases hz with ⟨rfl,rfl⟩; rfl
    · have hlex : 0 < a ∨ (0 = a ∧ 0 < b) := by omega
      have h := rectangular_lex_gap F M k hk hfine hcarry hM hk ha hb hlex
      linarith
  · by_cases hz : a = M - 1 ∧ b = k - 1
    · rcases hz with ⟨rfl,rfl⟩; rfl
    · have hlex : a < M-1 ∨ (a = M-1 ∧ b < k-1) := by omega
      have h := rectangular_lex_gap F M k hk hfine hcarry ha hb (by omega) (by omega) hlex
      linarith

/-- Ordered macro, coarse, and fine digits: all distinct triples are separated.
The proof exhausts equal/different macro blocks and both inner digit cases. -/
theorem three_digit_all_pairs_separated (D : ℕ → ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ i, i < k → ∀ j, j+1 < k →
      1 ≤ D a i (j+1)-D a i j)
    (hcarry : ∀ a, a < M → ∀ i, i+1 < k →
      1 ≤ D a (i+1) 0-D a i (k-1))
    (hmacro : ∀ a, a+1 < M → 1 ≤ D (a+1) 0 0-D a (k-1) (k-1))
    {a i j b u v : ℕ} (ha : a < M) (hi : i < k) (hj : j < k)
    (hb : b < M) (hu : u < k) (hv : v < k)
    (hne : (a,i,j) ≠ (b,u,v)) : 1 ≤ |D a i j-D b u v| := by
  have hend (c : ℕ) (hc : c < M) (x y : ℕ) (hx : x < k) (hy : y < k) :=
    rectangular_endpoints (D c) k k hk hk (hfine c hc) (hcarry c hc) hx hy
  have hfirst : ∀ c, c+1 < M → 1 ≤ D (c+1) 0 0-D c 0 0 := by
    intro c hc
    have h₀ := (hend c (by omega) 0 0 hk hk).2
    have h₁ := hmacro c hc
    linarith
  have hordered : ∀ c x y d z w, c < M → x < k → y < k → d < M → z < k → w < k →
      c < d → 1 ≤ D d z w-D c x y := by
    intro c x y d z w hc hx hy hd hz hw hcd
    have h₀ := (hend c hc x y hx hy).2
    have h₁ := hmacro c (by omega)
    have h₂ := bounded_step_mono (fun c => D c 0 0) M hfirst (show c+1 ≤ d by omega) hd
    have h₃ := (hend d hd z w hz hw).1
    linarith
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := hordered a i j b u v ha hi hj hb hu hv hab
    have ht := le_abs_self (D b u v-D a i j)
    rw [abs_sub_comm] at ht
    linarith
  · subst b
    have hne' : (i,j) ≠ (u,v) := by
      intro h
      apply hne
      rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      rfl
    exact rectangular_all_pairs_separated (D a) k k hk (hfine a ha) (hcarry a ha)
      hi hj hu hv hne'
  · exact (hordered b u v a i j hb hu hv ha hi hj hab).trans (le_abs_self _)

/-- The local/cross guard bounds actual scalar lengths, including their errors. -/
theorem local_cross_scalar_guard (loc cross R Tmin E : ℝ)
    (hl : loc ≤ 2*R) (hc : Tmin-E ≤ cross) (hg : 2*R+1 ≤ Tmin-E) :
    1 ≤ cross-loc := by linarith

/-- Exhaustive assembly for two disjoint families. The mixed cases are both
checked; this does not assert that a geometric configuration has been built. -/
theorem two_family_all_pairs_separated {ι κ : Type*} (L : ι → ℝ) (C : κ → ℝ)
    (hL : ∀ x y, x ≠ y → 1 ≤ |L x-L y|)
    (hC : ∀ x y, x ≠ y → 1 ≤ |C x-C y|)
    (hLC : ∀ x y, 1 ≤ C y-L x) :
    ∀ x y : ι ⊕ κ, x ≠ y → 1 ≤ |Sum.elim L C x-Sum.elim L C y| := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hL x y (by intro h; subst y; exact hxy rfl)
    | inr y =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [abs_sub_comm]
      exact (hLC x y).trans (le_abs_self _)
  | inr x =>
    cases y with
    | inl y => exact (hLC y x).trans (le_abs_self _)
    | inr y => exact hC x y (by intro h; subst y; exact hxy rfl)

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossScalar.lean
section

/-! The exact square-root metric used by the fifth-pass orthogonal circles.
All slope estimates below are algebraic secant estimates; no differentiability
or approximation error is assumed. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Phi (ν T : ℝ) : ℝ := Real.sqrt (ν^2 + 2*ν*T)

/-- The digit budget implies strict positivity of the exact radicand. -/
theorem pass5Phi_radicand_pos (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    0 < ν^2 + 2*ν*T := by
  have hlow := (abs_le.mp hT).1
  have hb := mul_le_mul_of_nonneg_left hbudget hν.le
  have ht := mul_le_mul_of_nonneg_left hlow hν.le
  have hp : 0 < (τ*ν)^2 := sq_pos_of_pos (mul_pos hτ hν)
  nlinarith

/-- The exact metric has the square prescribed by the geometry. -/
theorem pass5Phi_sq (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    (pass5Phi ν T)^2 = ν^2 + 2*ν*T := by
  exact Real.sq_sqrt (pass5Phi_radicand_pos ν τ H T hν hτ hT hbudget).le

/-- The root lies between τν and ν/τ, with the upper bound denominator-cleared. -/
theorem pass5Phi_range (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    τ*ν ≤ pass5Phi ν T ∧ τ*pass5Phi ν T ≤ ν := by
  have hsq := pass5Phi_sq ν τ H T hν hτ hT hbudget
  have hnonneg : 0 ≤ pass5Phi ν T := Real.sqrt_nonneg _
  have hlo := (abs_le.mp hT).1
  have hhi := (abs_le.mp hT).2
  have hb := mul_le_mul_of_nonneg_left hbudget hν.le
  have hl := mul_le_mul_of_nonneg_left hlo hν.le
  have hu := mul_le_mul_of_nonneg_left hhi hν.le
  have hrootlo : (τ*ν)^2 ≤ (pass5Phi ν T)^2 := by nlinarith
  have hrootup : (pass5Phi ν T)^2 ≤ (2-τ^2)*ν^2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hrootup (sq_nonneg τ)
  have hrem : 0 ≤ ((1-τ^2)*ν)^2 := sq_nonneg _
  constructor
  · nlinarith [mul_pos hτ hν]
  · have hs : (τ*pass5Phi ν T)^2 ≤ ν^2 := by nlinarith only [ht, hrem]
    nlinarith [mul_nonneg hτ.le hnonneg]

/-- Uniform lower and upper secant slopes on the entire digit interval. -/
theorem pass5Phi_secant (ν τ H u v : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hu : |u| ≤ H) (hv : |v| ≤ H)
    (hbudget : 2*H ≤ (1-τ^2)*ν) (huv : u ≤ v) :
    τ*(v-u) ≤ pass5Phi ν v-pass5Phi ν u ∧
      pass5Phi ν v-pass5Phi ν u ≤ (v-u)/τ := by
  have huSq := pass5Phi_sq ν τ H u hν hτ hu hbudget
  have hvSq := pass5Phi_sq ν τ H v hν hτ hv hbudget
  obtain ⟨huLo, huHi⟩ := pass5Phi_range ν τ H u hν hτ hτ1 hu hbudget
  obtain ⟨hvLo, hvHi⟩ := pass5Phi_range ν τ H v hν hτ hτ1 hv hbudget
  have hp : 0 < τ*ν := mul_pos hτ hν
  have hmono : pass5Phi ν u ≤ pass5Phi ν v := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hid : (pass5Phi ν v-pass5Phi ν u)*(pass5Phi ν v+pass5Phi ν u) =
      2*ν*(v-u) := by nlinarith only [huSq, hvSq]
  have hsum : 0 < pass5Phi ν v+pass5Phi ν u := by linarith
  constructor
  · apply (mul_le_mul_iff_of_pos_right hsum).mp
    have hb := mul_le_mul_of_nonneg_right (show
      τ*(pass5Phi ν v+pass5Phi ν u) ≤ 2*ν by linarith) (sub_nonneg.mpr huv)
    nlinarith only [hb, hid]
  · apply (le_div_iff₀ hτ).mpr
    have hb := mul_le_mul_of_nonneg_right (show
      2*τ*ν ≤ pass5Phi ν v+pass5Phi ν u by linarith) (sub_nonneg.mpr hmono)
    have hm : (2*ν)*((pass5Phi ν v-pass5Phi ν u)*τ) ≤ (2*ν)*(v-u) := by
      nlinarith only [hb, hid]
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2*ν)).mp hm

@[simp] theorem pass5Phi_zero (ν : ℝ) (hν : 0 ≤ ν) : pass5Phi ν 0 = ν := by
  simp [pass5Phi, Real.sqrt_sq_eq_abs, abs_of_nonneg hν]

/-- The exact baseline-displacement bound, uniform in all digit values. -/
theorem pass5Phi_displacement (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    |pass5Phi ν T-ν| ≤ H/τ := by
  have hH : 0 ≤ H := (abs_nonneg T).trans hT
  have hz : |(0 : ℝ)| ≤ H := by simpa using hH
  by_cases ht : 0 ≤ T
  · have hs := (pass5Phi_secant ν τ H 0 T hν hτ hτ1 hz hT hbudget ht).2
    rw [pass5Phi_zero ν hν.le] at hs
    have hmono : ν ≤ pass5Phi ν T := by
      have hl := (pass5Phi_secant ν τ H 0 T hν hτ hτ1 hz hT hbudget ht).1
      rw [pass5Phi_zero ν hν.le] at hl
      nlinarith [mul_nonneg hτ.le ht]
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    have hTH := (abs_le.mp hT).2
    exact hs.trans (div_le_div_of_nonneg_right (by linarith : T-0 ≤ H) hτ.le)
  · have hs := (pass5Phi_secant ν τ H T 0 hν hτ hτ1 hT hz hbudget (by linarith)).2
    rw [pass5Phi_zero ν hν.le] at hs
    have hmono : pass5Phi ν T ≤ ν := by
      have hl := (pass5Phi_secant ν τ H T 0 hν hτ hτ1 hT hz hbudget (by linarith)).1
      rw [pass5Phi_zero ν hν.le] at hl
      nlinarith [mul_nonneg hτ.le (show 0 ≤ -T by linarith)]
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    have hTH := (abs_le.mp hT).1
    have hd := div_le_div_of_nonneg_right (show 0-T ≤ H by linarith) hτ.le
    linarith



end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From PointFamily.lean
section

namespace Erdos670R29
open scoped Matrix BigOperators
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def angleZ (k i : ℕ) : ℝ := (519/1000)/(k : ℝ)*((i : ℝ)-((k : ℝ)-1)/2)
noncomputable def angleW (p k A i : ℕ) : ℝ :=
  (879/500)/(k : ℝ)*(pass5Ruler 2 p k A i : ℝ)/(2*(p : ℝ))
noncomputable def digit (k i : ℕ) : ℝ := (k : ℝ)/(519/1000)*Real.sin (angleZ k i)
noncomputable def crossLength (k : ℕ) (A B : Fin 6) (i j : ℕ) : ℝ :=
  pass5Phi ((k : ℝ)^2*sourceD A B) ((138/125)*(k : ℝ)*digit k i+(533/500)*digit k j)

noncomputable def pointFamily {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ) (A : Fin 6) (i : Fin k) :
    EuclideanSpace ℝ (TwoCircleCoordinate (Fin 5) (Fin 6)) :=
  twoCirclePoint (anchor Q) U W ((k : ℝ)^2) ((507/100)*(k : ℝ)^2)
    ((1131/100)*(k : ℝ)^2) A (angleZ k i.val) (angleW p k A.val i.val)

lemma angleZ_difference (k i j : ℕ) (hij : i ≤ j) :
    angleZ k j-angleZ k i = (519/1000)/(k : ℝ)*(j-i : ℕ) := by
  simp only [angleZ, Nat.cast_sub hij]
  ring
lemma angleW_difference (p k A i j : ℕ) (hij : i ≤ j) :
    angleW p k A j-angleW p k A i =
      (879/500)/(k : ℝ)*(pass5RulerGap 2 p k A i (j-i) : ℝ)/(2*(p : ℝ)) := by
  have he : i+(j-i)=j := Nat.add_sub_of_le hij
  simp only [angleW, pass5RulerGap, he, Int.cast_sub]
  ring

theorem pointFamily_local {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ)
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*(k : ℝ)^2)^2))
    (A : Fin 6) (i j : Fin k) (hij : i < j) :
    dist (pointFamily p Q U W A i) (pointFamily p Q U W A j) =
      localEdge p k A.val i.val j.val := by
  have hs := twoCircle_same_square (anchor Q) U W ((k : ℝ)^2)
    ((507/100)*(k : ℝ)^2) ((1131/100)*(k : ℝ)^2) hfactor A
    (angleZ k j.val) (angleZ k i.val) (angleW p k A.val j.val) (angleW p k A.val i.val)
  rw [angleZ_difference k i.val j.val hij.le, angleW_difference p k A.val i.val j.val hij.le] at hs
  have he : ((879/500)/(k : ℝ)*(pass5RulerGap 2 p k A.val i.val (j.val-i.val) : ℝ)/(2*p))/2 =
      ((879/500)/(k : ℝ))*(pass5RulerGap 2 p k A.val i.val (j.val-i.val) : ℝ)/(2*(2*p)) := by ring
  rw [he] at hs
  have hs' : dist (pointFamily p Q U W A j) (pointFamily p Q U W A i)^2 =
      (localH k ((j.val-i.val : ℕ) : ℝ))^2+(localB k p (pass5RulerGap 2 p k A.val i.val (j.val-i.val)))^2 := by
    simpa only [pointFamily, localH, localB, pass5Chord, mul_one] using hs
  unfold localEdge localLength
  rw [← hs', Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg, dist_comm]

theorem pointFamily_cross {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ)
    (hQ : Qᵀ*Q = sourceMacro)
    (hp : Qᵀ*U = ((k : ℝ)/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*(k : ℝ)^2)^2))
    (A B : Fin 6) (hAB : A < B) (i j : Fin k) :
    dist (pointFamily p Q U W A i) (pointFamily p Q U W B j) = crossLength k A B i.val j.val := by
  have hs := actual_cross_square Q U W k hQ hp hfactor A B hAB
    (angleZ k i.val) (angleZ k j.val) (angleW p k A.val i.val) (angleW p k B.val j.val)
  have hs' : dist (pointFamily p Q U W A i) (pointFamily p Q U W B j)^2 =
      ((k : ℝ)^2*sourceD A B)^2+2*((k : ℝ)^2*sourceD A B)*
        ((138/125)*(k : ℝ)*digit k i.val+(533/500)*digit k j.val) := by
    simpa only [pointFamily, digit, mul_assoc] using hs
  unfold crossLength pass5Phi
  rw [← hs', Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]



end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossSeparation.lean
section

/-! Exhaustive cross-edge separation for the exact orthogonal-circle metric.
The digit arrays may vary with the cluster. The macro-edge labels only enter
through their baseline separation, so any proved injective colex code applies. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5CrossDigit (s : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  s^2*(k : ℝ)*f i + s*g j

noncomputable def pass5DigitBudget (s h : ℝ) (k : ℕ) : ℝ := s*(s*(k : ℝ)+1)*h

/-- The full two-digit perturbation is bounded by the manuscript's exact budget. -/
theorem pass5CrossDigit_bound (s h : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ)
    (hs : 0 ≤ s) (hf : |f i| ≤ h) (hg : |g j| ≤ h) :
    |pass5CrossDigit s k f g i j| ≤ pass5DigitBudget s h k := by
  obtain ⟨hfl,hfu⟩ := abs_le.mp hf
  obtain ⟨hgl,hgu⟩ := abs_le.mp hg
  have hc : 0 ≤ s^2*(k : ℝ) := by positivity
  have h₀ := mul_le_mul_of_nonneg_left hfl hc
  have h₁ := mul_le_mul_of_nonneg_left hfu hc
  have h₂ := mul_le_mul_of_nonneg_left hgl hs
  have h₃ := mul_le_mul_of_nonneg_left hgu hs
  unfold pass5CrossDigit pass5DigitBudget
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Fine and carry steps separate all distinct digit pairs on one macro edge. -/
theorem pass5_one_macro_separated (s τ h lam ν : ℝ) (k : ℕ)
    (f g : ℕ → ℝ) (hk : 0 < k) (hs : 0 < s) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hf : ∀ i, i < k → |f i| ≤ h) (hg : ∀ j, j < k → |g j| ≤ h)
    (hfstep : ∀ i, i+1 < k → lam ≤ f (i+1)-f i)
    (hgstep : ∀ j, j+1 < k → lam ≤ g (j+1)-g j)
    (hbudget : 2*pass5DigitBudget s h k ≤ (1-τ^2)*ν)
    (hfine : 1 ≤ τ*s*lam) (hcarry : 1 ≤ τ*(s^2*(k : ℝ)*lam-2*s*h))
    {i j u v : ℕ} (hi : i < k) (hj : j < k) (hu : u < k) (hv : v < k)
    (hne : (i,j) ≠ (u,v)) :
    1 ≤ |pass5Phi ν (pass5CrossDigit s k f g i j) -
      pass5Phi ν (pass5CrossDigit s k f g u v)| := by
  let D : ℕ → ℕ → ℝ := fun a b => pass5Phi ν (pass5CrossDigit s k f g a b)
  have hbound (a b : ℕ) (ha : a < k) (hb : b < k) :=
    pass5CrossDigit_bound s h k f g a b hs.le (hf a ha) (hg b hb)
  have hFine : ∀ a, a < k → ∀ b, b+1 < k → 1 ≤ D a (b+1)-D a b := by
    intro a ha b hb
    have hb0 : b < k := by omega
    have hd := mul_le_mul_of_nonneg_left (hgstep b hb) hs.le
    have ht : s*lam ≤ pass5CrossDigit s k f g a (b+1)-pass5CrossDigit s k f g a b := by
      unfold pass5CrossDigit
      nlinarith only [hd]
    have hmono : pass5CrossDigit s k f g a b ≤ pass5CrossDigit s k f g a (b+1) := by
      nlinarith [mul_nonneg hs.le hlam]
    have hslope := (pass5Phi_secant ν τ (pass5DigitBudget s h k)
      (pass5CrossDigit s k f g a b) (pass5CrossDigit s k f g a (b+1))
      hν hτ hτ1 (hbound a b ha hb0) (hbound a (b+1) ha hb) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hfine]
  have hCarry : ∀ a, a+1 < k → 1 ≤ D (a+1) 0-D a (k-1) := by
    intro a ha
    have ha0 : a < k := by omega
    have hlast : k-1 < k := by omega
    have hc : 0 ≤ s^2*(k : ℝ) := by positivity
    have hfGap := mul_le_mul_of_nonneg_left (hfstep a ha) hc
    have hgLo := mul_le_mul_of_nonneg_left (abs_le.mp (hg 0 hk)).1 hs.le
    have hgHi := mul_le_mul_of_nonneg_left (abs_le.mp (hg (k-1) hlast)).2 hs.le
    have ht : s^2*(k : ℝ)*lam-2*s*h ≤
        pass5CrossDigit s k f g (a+1) 0-pass5CrossDigit s k f g a (k-1) := by
      unfold pass5CrossDigit
      nlinarith only [hfGap, hgLo, hgHi]
    have hguardpos : 0 < s^2*(k : ℝ)*lam-2*s*h := by nlinarith
    have hmono : pass5CrossDigit s k f g a (k-1) ≤ pass5CrossDigit s k f g (a+1) 0 := by
      linarith
    have hslope := (pass5Phi_secant ν τ (pass5DigitBudget s h k)
      (pass5CrossDigit s k f g a (k-1)) (pass5CrossDigit s k f g (a+1) 0)
      hν hτ hτ1 (hbound a (k-1) ha0 hlast) (hbound (a+1) 0 ha hk) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hcarry]
  exact rectangular_all_pairs_separated D k k hk hFine hCarry hi hj hu hv hne

/-- Distinct macro baselines remain separate after the two exact displacements. -/
theorem pass5_different_macro_separated (ν μ τ H T U S : ℝ)
    (hν : 0 < ν) (hμ : 0 < μ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hT : |T| ≤ H) (hU : |U| ≤ H)
    (hbν : 2*H ≤ (1-τ^2)*ν) (hbμ : 2*H ≤ (1-τ^2)*μ)
    (hbase : S ≤ |ν-μ|) (hguard : 1 ≤ S-2*H/τ) :
    1 ≤ |pass5Phi ν T-pass5Phi μ U| := by
  have hdν := pass5Phi_displacement ν τ H T hν hτ hτ1 hT hbν
  have hdμ := pass5Phi_displacement μ τ H U hμ hτ hτ1 hU hbμ
  have htri₀ := abs_sub_le ν (pass5Phi ν T) μ
  have htri₁ := abs_sub_le (pass5Phi ν T) (pass5Phi μ U) μ
  rw [abs_sub_comm ν (pass5Phi ν T)] at htri₀
  have hid : 2*H/τ = 2*(H/τ) := by ring
  linarith

/-- All cross pairs: exhaustive same-macro and different-macro cases.
The only macro-code hypothesis is separation of the two baselines when their
ordered cluster pairs differ. This is discharged by any injective integer code. -/
theorem pass5_cross_pairs_separated {ι : Type*}
    (f : ι → ℕ → ℝ) (ν : ι → ι → ℝ) (s τ h lam S : ℝ) (k : ℕ)
    (hk : 0 < k) (hs : 0 < s) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hlam : 0 ≤ lam)
    (hf : ∀ A i, i < k → |f A i| ≤ h)
    (hfstep : ∀ A i, i+1 < k → lam ≤ f A (i+1)-f A i)
    (hfine : 1 ≤ τ*s*lam) (hcarry : 1 ≤ τ*(s^2*(k : ℝ)*lam-2*s*h))
    (hmacro : 1 ≤ S-2*pass5DigitBudget s h k/τ)
    (A B C D : ι) (hν : 0 < ν A B) (hμ : 0 < ν C D)
    (hbν : 2*pass5DigitBudget s h k ≤ (1-τ^2)*(ν A B))
    (hbμ : 2*pass5DigitBudget s h k ≤ (1-τ^2)*(ν C D))
    (hbase : (A,B) ≠ (C,D) → S ≤ |ν A B-ν C D|)
    {i j u v : ℕ} (hi : i < k) (hj : j < k) (hu : u < k) (hv : v < k)
    (hne : (A,B,i,j) ≠ (C,D,u,v)) :
    1 ≤ |pass5Phi (ν A B) (pass5CrossDigit s k (f A) (f B) i j) -
      pass5Phi (ν C D) (pass5CrossDigit s k (f C) (f D) u v)| := by
  by_cases hp : (A,B) = (C,D)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
    apply pass5_one_macro_separated s τ h lam (ν A B) k (f A) (f B)
      hk hs hτ hτ1 hlam hν (hf A) (hf B) (hfstep A) (hfstep B) hbν hfine hcarry
      hi hj hu hv
    intro hij
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
    exact hne rfl
  · exact pass5_different_macro_separated (ν A B) (ν C D) τ
      (pass5DigitBudget s h k) _ _ S hν hμ hτ hτ1
      (pass5CrossDigit_bound s h k (f A) (f B) i j hs.le (hf A i hi) (hf B j hj))
      (pass5CrossDigit_bound s h k (f C) (f D) u v hs.le (hf C u hu) (hf D v hv))
      hbν hbμ (hbase hp) hmacro

/-- Distinct natural macro labels give a full scale-sized baseline gap. -/
theorem pass5_integer_baselines_separated (S K : ℝ) (a b : ℕ)
    (hS : 0 ≤ S) (hab : a ≠ b) :
    S ≤ |S*(K+(a : ℝ)+1)-S*(K+(b : ℝ)+1)| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hh : (a : ℝ)+1 ≤ b := by exact_mod_cast h
    have hm := mul_le_mul_of_nonneg_left hh hS
    have habs := le_abs_self (S*(K+(b : ℝ)+1)-S*(K+(a : ℝ)+1))
    rw [abs_sub_comm] at habs
    nlinarith only [hm, habs]
  · have hh : (b : ℝ)+1 ≤ a := by exact_mod_cast h
    have hm := mul_le_mul_of_nonneg_left hh hS
    have habs := le_abs_self (S*(K+(a : ℝ)+1)-S*(K+(b : ℝ)+1))
    nlinarith only [hm, habs]



end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From CrossGeneric.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def crossDigit (sig eta : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ) : ℝ :=
  sig*(k : ℝ)*f i + eta*g j

noncomputable def digitBudget (sig eta h : ℝ) (k : ℕ) : ℝ := (sig*(k : ℝ)+eta)*h

/-- The full two-digit perturbation is bounded by the manuscript's exact budget. -/
theorem crossDigit_bound (sig eta h : ℝ) (k : ℕ) (f g : ℕ → ℝ) (i j : ℕ)
    (hsig : 0 ≤ sig) (hs : 0 ≤ eta) (hf : |f i| ≤ h) (hg : |g j| ≤ h) :
    |crossDigit sig eta k f g i j| ≤ digitBudget sig eta h k := by
  obtain ⟨hfl,hfu⟩ := abs_le.mp hf
  obtain ⟨hgl,hgu⟩ := abs_le.mp hg
  have hc : 0 ≤ sig*(k : ℝ) := by positivity
  have h₀ := mul_le_mul_of_nonneg_left hfl hc
  have h₁ := mul_le_mul_of_nonneg_left hfu hc
  have h₂ := mul_le_mul_of_nonneg_left hgl hs
  have h₃ := mul_le_mul_of_nonneg_left hgu hs
  unfold crossDigit digitBudget
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Fine and carry steps separate all distinct digit pairs on one macro edge. -/
theorem one_macro_separated (sig eta τ h lam ν : ℝ) (k : ℕ)
    (f g : ℕ → ℝ) (hk : 0 < k) (hsig : 0 < sig) (hs : 0 < eta) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hf : ∀ i, i < k → |f i| ≤ h) (hg : ∀ j, j < k → |g j| ≤ h)
    (hfstep : ∀ i, i+1 < k → lam ≤ f (i+1)-f i)
    (hgstep : ∀ j, j+1 < k → lam ≤ g (j+1)-g j)
    (hbudget : 2*digitBudget sig eta h k ≤ (1-τ^2)*ν)
    (hfine : 1 ≤ τ*eta*lam) (hcarry : 1 ≤ τ*(sig*(k : ℝ)*lam-2*eta*h))
    {i j u v : ℕ} (hi : i < k) (hj : j < k) (hu : u < k) (hv : v < k)
    (hne : (i,j) ≠ (u,v)) :
    1 ≤ |pass5Phi ν (crossDigit sig eta k f g i j) -
      pass5Phi ν (crossDigit sig eta k f g u v)| := by
  let D : ℕ → ℕ → ℝ := fun a b => pass5Phi ν (crossDigit sig eta k f g a b)
  have hbound (a b : ℕ) (ha : a < k) (hb : b < k) :=
    crossDigit_bound sig eta h k f g a b hsig.le hs.le (hf a ha) (hg b hb)
  have hFine : ∀ a, a < k → ∀ b, b+1 < k → 1 ≤ D a (b+1)-D a b := by
    intro a ha b hb
    have hb0 : b < k := by omega
    have hd := mul_le_mul_of_nonneg_left (hgstep b hb) hs.le
    have ht : eta*lam ≤ crossDigit sig eta k f g a (b+1)-crossDigit sig eta k f g a b := by
      unfold crossDigit
      nlinarith only [hd]
    have hmono : crossDigit sig eta k f g a b ≤ crossDigit sig eta k f g a (b+1) := by
      nlinarith [mul_nonneg hs.le hlam]
    have hslope := (pass5Phi_secant ν τ (digitBudget sig eta h k)
      (crossDigit sig eta k f g a b) (crossDigit sig eta k f g a (b+1))
      hν hτ hτ1 (hbound a b ha hb0) (hbound a (b+1) ha hb) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hfine]
  have hCarry : ∀ a, a+1 < k → 1 ≤ D (a+1) 0-D a (k-1) := by
    intro a ha
    have ha0 : a < k := by omega
    have hlast : k-1 < k := by omega
    have hc : 0 ≤ sig*(k : ℝ) := by positivity
    have hfGap := mul_le_mul_of_nonneg_left (hfstep a ha) hc
    have hgLo := mul_le_mul_of_nonneg_left (abs_le.mp (hg 0 hk)).1 hs.le
    have hgHi := mul_le_mul_of_nonneg_left (abs_le.mp (hg (k-1) hlast)).2 hs.le
    have ht : sig*(k : ℝ)*lam-2*eta*h ≤
        crossDigit sig eta k f g (a+1) 0-crossDigit sig eta k f g a (k-1) := by
      unfold crossDigit
      nlinarith only [hfGap, hgLo, hgHi]
    have hguardpos : 0 < sig*(k : ℝ)*lam-2*eta*h := by nlinarith
    have hmono : crossDigit sig eta k f g a (k-1) ≤ crossDigit sig eta k f g (a+1) 0 := by
      linarith
    have hslope := (pass5Phi_secant ν τ (digitBudget sig eta h k)
      (crossDigit sig eta k f g a (k-1)) (crossDigit sig eta k f g (a+1) 0)
      hν hτ hτ1 (hbound a (k-1) ha0 hlast) (hbound (a+1) 0 ha hk) hbudget hmono).1
    have hmul := mul_le_mul_of_nonneg_left ht hτ.le
    dsimp [D]
    nlinarith only [hslope, hmul, hcarry]
  exact rectangular_all_pairs_separated D k k hk hFine hCarry hi hj hu hv hne



end Erdos670R29

end

-- From CrossDigits.lean
section

namespace Erdos670R29

open Erdos488.Geometry.SeparatedDistances.FixedDimension

set_option maxHeartbeats 1500000 in
lemma digit_eq_sineDigit (k i : ℕ) :
    digit k i = sineDigit ((519/1000)/(k : ℝ)) (((k : ℝ)-1)/2) i := by
  unfold digit angleZ sineDigit
  simp [div_eq_mul_inv, mul_comm]

set_option maxHeartbeats 1500000 in
lemma digit_bound (k i : ℕ) (hk : 0 < k) (hi : i < k) :
    |digit k i| ≤ ((k : ℝ)-1)/2 := by
  rw [digit_eq_sineDigit]
  exact finite_sineDigit_bound _ k i (by positivity) hi

set_option maxHeartbeats 1500000 in
lemma digit_step (k i : ℕ) (hk : 0 < k) (hi : i+1 < k) :
    (1-(519/1000 : ℝ)^2/8) ≤ digit k (i+1)-digit k i := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hscale : ((519/1000)/(k : ℝ))^2*(k : ℝ)^2 ≤ (519/1000 : ℝ)^2 := by
    field_simp <;> norm_num
  have h := finite_sineDigit_step ((519/1000)/(k : ℝ)) ((519/1000 : ℝ)^2) k i
    (by positivity) hi hscale
  simpa only [digit_eq_sineDigit, Nat.cast_add, Nat.cast_one] using h

set_option maxHeartbeats 1500000 in
lemma concrete_digit_budget (k : ℕ) (hk : 100 ≤ k) (D : ℝ) (hD : 9709/500 ≤ D) :
    2*digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k ≤
      (1-(971/1000 : ℝ)^2)*((k : ℝ)^2*D) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  unfold digitBudget
  nlinarith [sq_nonneg (k : ℝ)]

set_option maxHeartbeats 1500000 in
lemma concrete_fine : (1 : ℝ) ≤ (971/1000)*(533/500)*(1-(519/1000)^2/8) := by norm_num
set_option maxHeartbeats 1500000 in
lemma concrete_carry (k : ℕ) (hk : 100 ≤ k) :
    (1 : ℝ) ≤ (971/1000)*((138/125)*(k : ℝ)*(1-(519/1000)^2/8)-
      2*(533/500)*(((k : ℝ)-1)/2)) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith
set_option maxHeartbeats 1500000 in
lemma concrete_macro_gap (k : ℕ) (hk : 100 ≤ k) :
    (1 : ℝ) ≤ (569/500)*(k : ℝ)^2-
      2*digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k/(971/1000) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  unfold digitBudget
  nlinarith [sq_nonneg (k : ℝ)]




end Erdos670R29

end

-- From MacroLabels.lean
section

namespace Erdos670R29

set_option maxHeartbeats 3000000 in
lemma sourceD_bounds (A B : Fin 6) (hAB : A < B) :
    (9709/500 : ℝ) ≤ sourceD A B ∧ sourceD A B ≤ (707/20 : ℝ) := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceD,labels] at *

set_option maxHeartbeats 3000000 in
lemma sourceD_spacing (A B C D : Fin 6) (hAB : A < B) (hCD : C < D)
    (hne : (A,B) ≠ (C,D)) : (569/500 : ℝ) ≤ |sourceD A B-sourceD C D| := by
  fin_cases A <;> fin_cases B <;> norm_num at hAB
  all_goals fin_cases C <;> fin_cases D <;> norm_num at hCD
  all_goals norm_num [sourceD,labels] at *



end Erdos670R29

end

-- From CrossSpectrum.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma cross_digit_bound (k i j : ℕ) (hk : 0 < k) (hi : i < k) (hj : j < k) :
    |(138/125)*(k : ℝ)*digit k i+(533/500)*digit k j| ≤
      digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k :=
  crossDigit_bound _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (digit_bound k i hk hi) (digit_bound k j hk hj)

lemma baseline_pos (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B) :
    0 < (k : ℝ)^2*sourceD A B := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD := (sourceD_bounds A B hAB).1
  positivity

lemma cross_lower (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    (37/2 : ℝ)*(k : ℝ)^2 ≤ crossLength k A B i j := by
  have hD := (sourceD_bounds A B hAB).1
  have h := (pass5Phi_range ((k : ℝ)^2*sourceD A B) (971/1000)
    (digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k)
    ((138/125)*(k : ℝ)*digit k i+(533/500)*digit k j)
    (baseline_pos k hk A B hAB) (by norm_num) (by norm_num)
    (cross_digit_bound k i j (by omega) hi hj) (concrete_digit_budget k hk _ hD)).1
  have hm := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  dsimp [crossLength]
  nlinarith

lemma cross_displacement (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    |crossLength k A B i j-(k : ℝ)^2*sourceD A B| ≤
      digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k/(971/1000) :=
  pass5Phi_displacement _ _ _ _ (baseline_pos k hk A B hAB) (by norm_num) (by norm_num)
    (cross_digit_bound k i j (by omega) hi hj)
    (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)

lemma cross_upper (k : ℕ) (hk : 100 ≤ k) (A B : Fin 6) (hAB : A < B)
    (i j : ℕ) (hi : i < k) (hj : j < k) :
    crossLength k A B i j < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
  have h := (abs_le.mp (cross_displacement k hk A B hAB i j hi hj)).2
  have hD := (sourceD_bounds A B hAB).2
  have hm := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  unfold digitBudget at h
  nlinarith [sq_nonneg (k : ℝ)]

theorem cross_edges_separated (k : ℕ) (hk : 100 ≤ k)
    (A B C D : Fin 6) (hAB : A < B) (hCD : C < D)
    (i j u v : Fin k) (hne : (A,B,i,j) ≠ (C,D,u,v)) :
    1 ≤ |crossLength k A B i.val j.val-crossLength k C D u.val v.val| := by
  by_cases hmacro : (A,B)=(C,D)
  · have hA : A=C := congrArg Prod.fst hmacro
    have hB : B=D := congrArg Prod.snd hmacro
    subst C
    subst D
    have hpair : (i.val,j.val) ≠ (u.val,v.val) := by
      intro he
      have hi : i=u := Fin.ext (congrArg Prod.fst he)
      have hj : j=v := Fin.ext (congrArg Prod.snd he)
      exact hne (by subst u; subst v; rfl)
    exact one_macro_separated (138/125) (533/500) (971/1000) (((k : ℝ)-1)/2)
      (1-(519/1000)^2/8) ((k : ℝ)^2*sourceD A B) k (digit k) (digit k)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (baseline_pos k hk A B hAB) (fun i hi => digit_bound k i (by omega) hi)
      (fun i hi => digit_bound k i (by omega) hi)
      (fun i hi => digit_step k i (by omega) hi) (fun i hi => digit_step k i (by omega) hi)
      (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)
      concrete_fine (concrete_carry k hk) i.isLt j.isLt u.isLt v.isLt hpair
  · apply pass5_different_macro_separated ((k : ℝ)^2*sourceD A B)
      ((k : ℝ)^2*sourceD C D) (971/1000)
      (digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k) _ _ ((569/500)*(k : ℝ)^2)
      (baseline_pos k hk A B hAB) (baseline_pos k hk C D hCD)
      (by norm_num) (by norm_num)
      (cross_digit_bound k i.val j.val (by omega) i.isLt j.isLt)
      (cross_digit_bound k u.val v.val (by omega) u.isLt v.isLt)
      (concrete_digit_budget k hk _ (sourceD_bounds A B hAB).1)
      (concrete_digit_budget k hk _ (sourceD_bounds C D hCD).1) ?_ (concrete_macro_gap k hk)
    have h := mul_le_mul_of_nonneg_left (sourceD_spacing A B C D hAB hCD hmacro)
      (sq_nonneg (k : ℝ))
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (k : ℝ))]
    nlinarith only [h]




end Erdos670R29

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.UnorderedEdgeSeparation.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Every non-diagonal unordered edge has an increasing representative. -/
theorem edge_has_increasing_representative {ι : Type*} [LinearOrder ι] (e : Edge ι) :
    ∃ i j : ι, i < j ∧ e.val = s(i,j) := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf i j =>
    have hij : i ≠ j := by simpa only [Sym2.mk_isDiag_iff] using he
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨i,j,hij,rfl⟩
    · exact ⟨j,i,hji,Sym2.eq_swap⟩

/-- Increasing representatives of the same unordered edge coincide componentwise. -/
theorem increasing_edge_representative_unique {ι : Type*} [LinearOrder ι]
    {i j k l : ι} (hij : i < j) (hkl : k < l) (heq : s(i,j) = s(k,l)) :
    i = k ∧ j = l := by
  rcases Sym2.eq_iff.mp heq with h | ⟨rfl,rfl⟩
  · exact h
  · exact False.elim (lt_asymm hij hkl)

/-- A genuinely unordered Sym2 bridge: canonical increasing endpoint comparisons
suffice for the repository's publication-facing separation definition. -/
theorem separatedConfiguration_of_increasing_pairs
    {ι E : Type*} [LinearOrder ι] [PseudoMetricSpace E] (p : ι → E)
    (hgap : ∀ i j k l : ι, i < j → k < l → (i,j) ≠ (k,l) →
      1 ≤ |dist (p i) (p j)-dist (p k) (p l)|) : SeparatedConfiguration p := by
  intro e f hef
  obtain ⟨i,j,hij,he⟩ := edge_has_increasing_representative e
  obtain ⟨k,l,hkl,hf⟩ := edge_has_increasing_representative f
  have hne : (i,j) ≠ (k,l) := by
    intro h
    apply hef
    apply Subtype.ext
    rw [he,hf]
    rcases Prod.mk.inj h with ⟨rfl,rfl⟩
    rfl
  simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hgap i j k l hij hkl hne

/-- Zero must be excluded independently of edge-to-edge separation. -/
theorem minimum_distance_of_increasing_pairs
    {ι E : Type*} [LinearOrder ι] [PseudoMetricSpace E] (p : ι → E)
    (hmin : ∀ i j : ι, i < j → 1 ≤ dist (p i) (p j)) :
    ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hmin i j hij
  · simpa only [dist_comm] using hmin j i hji

/-- The independently proved minimum distance implies injectivity. -/
theorem injective_of_unit_minimum_distance
    {ι E : Type*} [PseudoMetricSpace E] (p : ι → E)
    (hmin : ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j)) : Function.Injective p := by
  intro i j heq
  by_contra hne
  have h := hmin i j hne
  rw [heq,dist_self] at h
  norm_num at h

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.ClusterEdgeAssembly.lean
section

/-! Exhaustive genuinely unordered cluster-edge classification and assembly.
Local separation, canonical cross separation and mixed band isolation are
explicit inputs; this module constructs no Gram matrix or scalar certificate. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Each non-diagonal edge is either local with increasing local endpoints,
or cross-cluster with increasing macro endpoints. -/
theorem cluster_edge_cases {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : Edge (α × β)) :
    (∃ A i j, i < j ∧ e.val=s((A,i),(A,j))) ∨
      (∃ A B i j, A < B ∧ e.val=s((A,i),(B,j))) := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨A,i⟩ := x
    obtain ⟨B,j⟩ := y
    by_cases hAB : A=B
    · subst B
      have hij : i ≠ j := by
        intro h
        subst j
        exact he (Sym2.mk_isDiag_iff.mpr rfl)
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl ⟨A,i,j,hij,rfl⟩
      · exact Or.inl ⟨A,j,i,hji,Sym2.eq_swap⟩
    · rcases lt_or_gt_of_ne hAB with hAB | hBA
      · exact Or.inr ⟨A,B,i,j,hAB,rfl⟩
      · exact Or.inr ⟨B,A,j,i,hBA,Sym2.eq_swap⟩

/-- All four combinations of unordered edge classes are checked. -/
theorem separatedConfiguration_of_cluster_gaps
    {α β E : Type*} [LinearOrder α] [LinearOrder β] [PseudoMetricSpace E]
    (p : α × β → E)
    (hlocal : ∀ A i j B u v, i < j → u < v → (A,i,j) ≠ (B,u,v) →
      1 ≤ |dist (p (A,i)) (p (A,j))-dist (p (B,u)) (p (B,v))|)
    (hcross : ∀ A B i j C D u v, A < B → C < D → (A,B,i,j) ≠ (C,D,u,v) →
      1 ≤ |dist (p (A,i)) (p (B,j))-dist (p (C,u)) (p (D,v))|)
    (hmixed : ∀ A i j B C u v, i < j → B < C →
      1 ≤ dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))) :
    SeparatedConfiguration p := by
  intro e f hef
  have hval : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  rcases cluster_edge_cases e with ⟨A,i,j,hij,he⟩ | ⟨A,B,i,j,hAB,he⟩
  · rcases cluster_edge_cases f with ⟨B,u,v,huv,hf⟩ | ⟨B,C,u,v,hBC,hf⟩
    · have hne : (A,i,j) ≠ (B,u,v) := by
        intro h
        have hA : A=B := congrArg Prod.fst h
        have hi : i=u := congrArg (fun q => q.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2) h
        apply hval
        simpa only [he,hf,hA,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hlocal A i j B u v hij huv hne
    · have h := (hmixed A i j B C u v hij hBC).trans
        (le_abs_self (dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))))
      rw [abs_sub_comm] at h
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
  · rcases cluster_edge_cases f with ⟨C,u,v,huv,hf⟩ | ⟨C,D,u,v,hCD,hf⟩
    · have h := (hmixed C u v A B i j huv hAB).trans (le_abs_self _)
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
    · have hne : (A,B,i,j) ≠ (C,D,u,v) := by
        intro h
        have hA : A=C := congrArg Prod.fst h
        have hB : B=D := congrArg (fun q => q.2.1) h
        have hi : i=u := congrArg (fun q => q.2.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2.2) h
        apply hval
        simpa only [he,hf,hA,hB,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hcross A B i j C D u v hAB hCD hne

/-- The two nonzero-distance classes must each clear zero independently. -/
theorem cluster_minimum_distance
    {α β E : Type*} [LinearOrder α] [LinearOrder β] [PseudoMetricSpace E]
    (p : α × β → E)
    (hlocal : ∀ A i j, i < j → 1 ≤ dist (p (A,i)) (p (A,j)))
    (hcross : ∀ A B i j, A < B → 1 ≤ dist (p (A,i)) (p (B,j))) :
    ∀ x y, x ≠ y → 1 ≤ dist (p x) (p y) := by
  rintro ⟨A,i⟩ ⟨B,j⟩ hxy
  by_cases hAB : A=B
  · subst B
    have hij : i ≠ j := by intro h; subst j; exact hxy rfl
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlocal A i j h
    · simpa only [dist_comm] using hlocal A j i h
  · rcases lt_or_gt_of_ne hAB with h | h
    · exact hcross A B i j h
    · simpa only [dist_comm] using hcross B A j i h

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.AllNArithmetic.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Every sufficiently large requested size is contained in a rectangular
cluster size with a bounded number of clusters. This closes only the integer
rounding step of PR 2974; configuration existence is not a premise or conclusion. -/
theorem every_large_n_cluster_parameters (n : ℕ) (hn : 68000 ≤ n) :
    ∃ k m : ℕ, 2 ≤ k ∧ 34000 ≤ m ∧ m ≤ 51000 ∧
      n ≤ m*k ∧ m*k < n+k ∧ 34000*k ≤ n := by
  let k := n / 34000
  let r := n % 34000
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hk0 : 0 < k := by omega
  have hr : r < 34000 := Nat.mod_lt _ (by norm_num)
  have hnkr : 34000*k+r = n := Nat.div_add_mod n 34000
  have hsub : r+k-1+1 = r+k := by omega
  let q := (r+k-1)/k
  have hqUpper : q ≤ 17000 := by
    have hnum : r+k-1 < (17000+1)*k := by omega
    have := (Nat.div_lt_iff_lt_mul hk0).2 hnum
    change q < 17001 at this
    omega
  have hqmul : q*k ≤ r+k-1 := Nat.div_mul_le_self _ _
  have hnext : r+k-1 < (q+1)*k := by
    simpa [q, Nat.mul_comm] using Nat.lt_mul_div_succ (r+k-1) hk0
  refine ⟨k, 34000+q, hk, Nat.le_add_right _ _, by linarith, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · omega

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.DirectCrossSpectrum.lean
section

/-! Derivative-free cross-spectrum ordering, adopting JRL PR 3002.
No adjacent quotient-error Lipschitz estimate or physical local-step H is used.
All geometric inputs are visible as scalar square identities and pointwise errors. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Exact cancellation of the coarse digit from a fine squared increment. -/
theorem cross_fine_polarization (ν α β₀ β₁ : ℝ) :
    ((ν+α+β₁)^2-2*α*β₁)-((ν+α+β₀)^2-2*α*β₀) =
      (β₁-β₀)*(2*ν+β₁+β₀) := by ring

/-- The symmetric coarse squared-increment identity. -/
theorem cross_coarse_polarization (ν α₀ α₁ β : ℝ) :
    ((ν+α₁+β)^2-2*α₁*β)-((ν+α₀+β)^2-2*α₀*β) =
      (α₁-α₀)*(2*ν+α₁+α₀) := by ring

/-- The polynomial form of the fine guard propagates to every larger baseline. -/
theorem direct_fine_guard_propagates (g ν₀ ν b A E : ℝ)
    (hg : 1 ≤ g) (hν : ν₀ ≤ ν) (hguard : ν₀+A+E ≤ g*(ν₀-b)) :
    ν+A+E ≤ g*(ν-b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hg) (sub_nonneg.mpr hν)]

/-- A unit fine gap follows directly from squares and endpoint upper bounds. -/
theorem polarized_fine_gap (ν b A E g β₀ β₁ D₀ D₁ : ℝ)
    (hg : 0 ≤ g) (hν : b ≤ ν) (hβ₀ : -b ≤ β₀) (hβ₁ : -b ≤ β₁)
    (hβ : g ≤ β₁-β₀) (hD₀ : 0 ≤ D₀) (hD₁ : 0 < D₁)
    (hu₀ : D₀ ≤ ν+A+E) (hu₁ : D₁ ≤ ν+A+E)
    (hsq : D₁^2-D₀^2=(β₁-β₀)*(2*ν+β₁+β₀))
    (hguard : ν+A+E ≤ g*(ν-b)) : 1 ≤ D₁-D₀ := by
  have hfactor : 2*(ν-b) ≤ 2*ν+β₁+β₀ := by linarith
  have hprod := mul_le_mul hβ hfactor
    (show 0 ≤ 2*(ν-b) by linarith) (show 0 ≤ β₁-β₀ by linarith)
  have hsum : 0 < D₁+D₀ := by linarith
  have hmul : 1*(D₁+D₀) ≤ (D₁-D₀)*(D₁+D₀) := by nlinarith
  exact (mul_le_mul_iff_of_pos_right hsum).1 hmul

/-- Two pointwise errors suffice for the coarse carry; no k*Flip term is needed. -/
theorem direct_carry_guard (s c r fstar E coarse₀ coarse₁ fine₀ fineLast e₀ e₁ : ℝ)
    (hc : s*c*r ≤ coarse₁-coarse₀) (hf : fineLast-fine₀ ≤ 2*s*fstar)
    (he₀ : |e₀| ≤ E) (he₁ : |e₁| ≤ E)
    (hguard : 1 ≤ s*(c*r-2*fstar)-2*E) :
    1 ≤ (coarse₁+fine₀+e₁)-(coarse₀+fineLast+e₀) := by
  have h₀ := (abs_le.mp he₀).2
  have h₁ := (abs_le.mp he₁).1
  nlinarith

/-- Complete derivative-free cross-spectrum theorem, for every distinct triple.
The exact metric square and absolute error bound are explicit inputs. -/
theorem direct_cross_spectrum_separated
    (D : ℕ → ℕ → ℕ → ℝ) (ν f : ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (s c r fstar E S νmin : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hν : ∀ a, a < M → νmin ≤ ν a) (hνmin : s*fstar ≤ νmin)
    (hf : ∀ i, i < k → |f i| ≤ fstar)
    (hstep : ∀ i, i+1 < k → r ≤ f (i+1)-f i)
    (hbase : ∀ a, a+1 < M → S ≤ ν (a+1)-ν a)
    (hpos : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 < D a i j)
    (hsquare : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      (D a i j)^2=(ν a+s*c*f i+s*f j)^2-2*(s*c*f i)*(s*f j))
    (herror : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      |D a i j-(ν a+s*c*f i+s*f j)| ≤ E)
    (hfine₁ : 1 ≤ s*r)
    (hfine₂ : νmin+s*(c+1)*fstar+E ≤ s*r*(νmin-s*fstar))
    (hcarry : 1 ≤ s*(c*r-2*fstar)-2*E)
    (hmacro : 1 ≤ S-2*(s*(c+1)*fstar)-2*E) :
    ∀ a i j b u v, a < M → i < k → j < k → b < M → u < k → v < k →
      (a,i,j) ≠ (b,u,v) → 1 ≤ |D a i j-D b u v| := by
  have hpert (i j : ℕ) (hi : i < k) (hj : j < k) :
      |s*c*f i+s*f j| ≤ s*(c+1)*fstar := by
    obtain ⟨hli,hui⟩ := abs_le.mp (hf i hi)
    obtain ⟨hlj,huj⟩ := abs_le.mp (hf j hj)
    have h₀ := mul_le_mul_of_nonneg_left hli (mul_nonneg hs hc)
    have h₁ := mul_le_mul_of_nonneg_left hui (mul_nonneg hs hc)
    have h₂ := mul_le_mul_of_nonneg_left hlj hs
    have h₃ := mul_le_mul_of_nonneg_left huj hs
    apply abs_le.mpr
    constructor <;> nlinarith
  have hupper (a i j : ℕ) (ha : a < M) (hi : i < k) (hj : j < k) :
      D a i j ≤ ν a+s*(c+1)*fstar+E := by
    have h₀ := (abs_le.mp (hpert i j hi hj)).2
    have h₁ := (abs_le.mp (herror a ha i hi j hj)).2
    linarith
  have hFine : ∀ a, a < M → ∀ i, i < k → ∀ j, j+1 < k →
      1 ≤ D a i (j+1)-D a i j := by
    intro a ha i hi j hj
    have hj₀ : j < k := by omega
    have hβ := mul_le_mul_of_nonneg_left (hstep j hj) hs
    have hβ₀ := mul_le_mul_of_nonneg_left (abs_le.mp (hf j hj₀)).1 hs
    have hβ₁ := mul_le_mul_of_nonneg_left (abs_le.mp (hf (j+1) hj)).1 hs
    apply polarized_fine_gap (ν a) (s*fstar) (s*(c+1)*fstar) E (s*r)
      (s*f j) (s*f (j+1)) (D a i j) (D a i (j+1))
      (by linarith) (hνmin.trans (hν a ha))
      (by nlinarith) (by nlinarith) (by nlinarith)
      (hpos a ha i hi j hj₀).le (hpos a ha i hi (j+1) hj)
      (hupper a i j ha hi hj₀) (hupper a i (j+1) ha hi hj)
    · rw [hsquare a ha i hi (j+1) hj, hsquare a ha i hi j hj₀]
      exact cross_fine_polarization _ _ _ _
    · exact direct_fine_guard_propagates _ _ _ _ _ _ hfine₁ (hν a ha) hfine₂
  have hCarry : ∀ a, a < M → ∀ i, i+1 < k →
      1 ≤ D a (i+1) 0-D a i (k-1) := by
    intro a ha i hi
    have hi₀ : i < k := by omega
    have hlast : k-1 < k := by omega
    have h₀ := mul_le_mul_of_nonneg_left (hstep i hi) (mul_nonneg hs hc)
    have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp (hf 0 hk)).1 hs
    have h₂ := mul_le_mul_of_nonneg_left (abs_le.mp (hf (k-1) hlast)).2 hs
    have he₀ := (abs_le.mp (herror a ha i hi₀ (k-1) hlast)).2
    have he₁ := (abs_le.mp (herror a ha (i+1) hi 0 hk)).1
    nlinarith
  have hMacro : ∀ a, a+1 < M → 1 ≤ D (a+1) 0 0-D a (k-1) (k-1) := by
    intro a ha
    have ha₀ : a < M := by omega
    have hlast : k-1 < k := by omega
    have h₀ := (abs_le.mp (hpert 0 0 hk hk)).1
    have h₁ := (abs_le.mp (hpert (k-1) (k-1) hlast hlast)).2
    have he₀ := (abs_le.mp (herror a ha₀ (k-1) hlast (k-1) hlast)).2
    have he₁ := (abs_le.mp (herror (a+1) ha 0 hk 0 hk)).1
    have hb := hbase a ha
    nlinarith
  intro a i j b u v ha hi hj hb hu hv hne
  exact three_digit_all_pairs_separated D M k hk hFine hCarry hMacro ha hi hj hb hu hv hne

/-- The exact fine universal rational certificate from the new source. -/
theorem direct_fine_rational_certificate :
    (1 : ℝ) < 15719289303849634494315/14027497163657672321024 := by norm_num

/-- The carry envelope clears one for every nonnegative k, not just sampled sizes. -/
theorem direct_carry_rational_certificate (k : ℝ) (hk : 0 ≤ k) :
    1 < 9/8+k*(13009148140329/95880445804544) := by nlinarith

/-- The macro envelope clears one uniformly in every nonnegative k. -/
theorem direct_macro_rational_certificate (k : ℝ) (hk : 0 ≤ k) :
    1 < 9/8+k*(52668618975/374532991424)+k^2*(81/512) := by nlinarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceCrossGuards.lean
section

/-! Universal source-parameter cross guards, not finite sampled certificates.
The hypotheses are k≥2 and K≥72247875/4, with the literal source formulas. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sourceMacroStep (k : ℝ) : ℝ := (9/8 : ℝ)^3*k^2
noncomputable def sourcePerturbationBound (k : ℝ) : ℝ := (9/8 : ℝ)*((9/8 : ℝ)*k+1)*((k-1)/2)
noncomputable def sourceBaseline (K k : ℝ) : ℝ := sourceMacroStep k*(K+1)
noncomputable def sourceTmin (K k : ℝ) : ℝ := sourceBaseline K k-sourcePerturbationBound k
noncomputable def sourceError (K k : ℝ) : ℝ := 2*(9/8 : ℝ)^3*k^3/sourceTmin K k

theorem source_perturbation_quadratic_bound (k : ℝ) (hk : 2 ≤ k) :
    sourcePerturbationBound k ≤ (117/128 : ℝ)*k^2 := by
  unfold sourcePerturbationBound
  nlinarith [sq_nonneg k]

theorem source_baseline_lower (K k : ℝ) (hK : 72247875/4 ≤ K) :
    (52668703791/2048 : ℝ)*k^2 ≤ sourceBaseline K k := by
  have h := mul_le_mul_of_nonneg_left hK (show 0 ≤ (9/8 : ℝ)^3*k^2 by positivity)
  unfold sourceBaseline sourceMacroStep
  nlinarith

theorem source_Tmin_lower (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    (52668701919/2048 : ℝ)*k^2 ≤ sourceTmin K k := by
  have h₀ := source_baseline_lower K k hK
  have h₁ := source_perturbation_quadratic_bound k hk
  unfold sourceTmin
  linarith

theorem source_Tmin_pos (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    0 < sourceTmin K k := by
  have h := source_Tmin_lower K k hK hk
  nlinarith [sq_nonneg (k-2)]

/-- The pointwise error is at most k times one exact rational, uniformly in K,k. -/
theorem source_error_linear_bound (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    sourceError K k ≤ (648/5852077991 : ℝ)*k := by
  have hT := source_Tmin_lower K k hK hk
  have hTpos := source_Tmin_pos K k hK hk
  have hm := mul_le_mul_of_nonneg_left hT (show 0 ≤ (648/5852077991 : ℝ)*k by positivity)
  unfold sourceError
  apply (div_le_iff₀ hTpos).2
  nlinarith

/-- Every direct polarization fine guard, in denominator-cleared form. -/
theorem source_direct_fine_guard (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    sourceBaseline K k+sourcePerturbationBound k+sourceError K k ≤
      ((9/8 : ℝ)*(255/256))*(sourceBaseline K k-(9/8)*((k-1)/2)) := by
  have hν := source_baseline_lower K k hK
  have hA := source_perturbation_quadratic_bound k hk
  have hE := source_error_linear_bound K k hK hk
  have hk₂ : 2*k ≤ k^2 := by nlinarith
  nlinarith

theorem source_direct_carry_guard (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    1 ≤ (9/8 : ℝ)*(((9/8)*k)*(255/256)-2*((k-1)/2))-2*sourceError K k := by
  have hE := source_error_linear_bound K k hK hk
  nlinarith

theorem source_direct_macro_guard (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    1 ≤ sourceMacroStep k-2*sourcePerturbationBound k-2*sourceError K k := by
  have hE := source_error_linear_bound K k hK hk
  unfold sourceMacroStep sourcePerturbationBound
  nlinarith [sq_nonneg k]

theorem source_baseline_exceeds_fine_bound (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    (9/8 : ℝ)*((k-1)/2) ≤ sourceBaseline K k := by
  have hν := source_baseline_lower K k hK
  nlinarith [sq_nonneg (k-2)]

/-- Actual ceiling offset from the candidate, with its universal macro-size bound. -/
noncomputable def sourceOffset (m : ℕ) : ℕ := ⌈(m : ℝ)*((m : ℝ)-1)/64⌉₊

theorem sourceOffset_lower (m : ℕ) (hm : 34000 ≤ m) :
    (72247875/4 : ℝ) ≤ sourceOffset m := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have h := Nat.le_ceil ((m : ℝ)*((m : ℝ)-1)/64)
  change (72247875/4 : ℝ) ≤ (⌈(m : ℝ)*((m : ℝ)-1)/64⌉₊ : ℝ)
  nlinarith [sq_nonneg ((m : ℝ)-34000)]

/-- The nominal lower bound remains positive after the actual pointwise error. -/
theorem source_error_lt_Tmin (K k : ℝ) (hK : 72247875/4 ≤ K) (hk : 2 ≤ k) :
    sourceError K k < sourceTmin K k := by
  have ht := source_Tmin_lower K k hK hk
  have he := source_error_linear_bound K k hK hk
  nlinarith [sq_nonneg (k-2)]

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceCrossSpectrum.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sourceDigit (k i : ℕ) : ℝ :=
  sineDigit (Real.sqrt (1/32)/(k : ℝ)) (((k : ℝ)-1)/2) i
noncomputable def sourceCrossBaseline (K : ℝ) (k a : ℕ) : ℝ :=
  sourceBaseline K k+sourceMacroStep k*a
noncomputable def sourceAlpha (k i : ℕ) : ℝ := (9/8 : ℝ)*((9/8)*(k : ℝ))*sourceDigit k i
noncomputable def sourceBeta (k i : ℕ) : ℝ := (9/8 : ℝ)*sourceDigit k i

theorem sourceDigit_bound (k i : ℕ) (hk : 2 ≤ k) (hi : i < k) :
    |sourceDigit k i| ≤ ((k : ℝ)-1)/2 := by
  apply finite_sineDigit_bound
  · have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  · exact hi

theorem sourceDigit_step (k i : ℕ) (hk : 2 ≤ k) (hi : i+1 < k) :
    (255 : ℝ)/256 ≤ sourceDigit k (i+1)-sourceDigit k i := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h := finite_sineDigit_source_step (Real.sqrt (1/32)/(k : ℝ)) k i
    (by positivity) hi (source_theta_scale k (by omega)).le
  simpa only [sourceDigit,Nat.cast_add,Nat.cast_one] using h

theorem source_digit_sum_bound (k i j : ℕ) (hk : 2 ≤ k) (hi : i < k) (hj : j < k) :
    |sourceAlpha k i+sourceBeta k j| ≤ sourcePerturbationBound k := by
  obtain ⟨hli,hui⟩ := abs_le.mp (sourceDigit_bound k i hk hi)
  obtain ⟨hlj,huj⟩ := abs_le.mp (sourceDigit_bound k j hk hj)
  have hk' : (0 : ℝ) ≤ k := by positivity
  have hi₀ := mul_le_mul_of_nonneg_left hli hk'
  have hi₁ := mul_le_mul_of_nonneg_left hui hk'
  unfold sourceAlpha sourceBeta sourcePerturbationBound
  apply abs_le.mpr
  constructor <;> nlinarith

theorem source_digit_product_bound (k i j : ℕ) (hk : 2 ≤ k) (hi : i < k) (hj : j < k) :
    |sourceAlpha k i*sourceBeta k j| ≤ (9/8 : ℝ)^3*(k : ℝ)^3 := by
  have hfi := sourceDigit_bound k i hk hi
  have hfj := sourceDigit_bound k j hk hj
  have hk' : (0 : ℝ) ≤ k := by positivity
  have hi' : |sourceDigit k i| ≤ (k : ℝ) := by linarith
  have hj' : |sourceDigit k j| ≤ (k : ℝ) := by linarith
  have hp := mul_le_mul hi' hj' (abs_nonneg _) hk'
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (9/8 : ℝ)^3*(k : ℝ) by positivity)
  have he : |sourceAlpha k i*sourceBeta k j|=
      (9/8 : ℝ)^3*(k : ℝ)*(|sourceDigit k i| * |sourceDigit k j|) := by
    unfold sourceAlpha sourceBeta
    rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_mul]
    simp only [abs_of_nonneg hk']
    norm_num
    ring
  rw [he]
  nlinarith

/-- Pointwise errors for the literal source digits, without assuming an error bound. -/
theorem source_cross_error (D K : ℝ) (k a i j : ℕ) (hK : 72247875/4 ≤ K)
    (hk : 2 ≤ k) (hi : i < k) (hj : j < k) (hD : 0 ≤ D)
    (hsq : D^2=(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)^2-
      2*sourceAlpha k i*sourceBeta k j) :
    |D-(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)| ≤ sourceError K k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : sourceBaseline K k ≤ sourceCrossBaseline K k a := by
    have h : 0 ≤ sourceMacroStep k*(a : ℝ) := by unfold sourceMacroStep; positivity
    unfold sourceCrossBaseline
    linarith
  have hpert := (abs_le.mp (source_digit_sum_bound k i j hk hi hj)).1
  have hu : sourceTmin K k ≤ sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j := by
    unfold sourceTmin
    linarith
  simpa only [sourceError,mul_assoc] using cross_error_uniform_bound D _ (sourceAlpha k i) (sourceBeta k j)
    ((9/8 : ℝ)^3*(k : ℝ)^3) (sourceTmin K k) hD (source_Tmin_pos K k hK hk') hu
    (source_digit_product_bound k i j hk hi hj) hsq

/-- Complete source-specific cross-spectrum separation. The only metric inputs
are nonnegativity and the corrected exact squared-distance formula. All sine,
pointwise-error, fine, carry and macro guards are proved, uniformly in k,K. -/
theorem source_cross_spectrum_separated (D : ℕ → ℕ → ℕ → ℝ) (M k : ℕ) (K : ℝ)
    (hk : 2 ≤ k) (hK : 72247875/4 ≤ K)
    (hD : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 ≤ D a i j)
    (hsq : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      (D a i j)^2=(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)^2-
        2*sourceAlpha k i*sourceBeta k j) :
    ∀ a i j b u v, a < M → i < k → j < k → b < M → u < k → v < k →
      (a,i,j) ≠ (b,u,v) → 1 ≤ |D a i j-D b u v| := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hν (a : ℕ) : sourceBaseline K k ≤ sourceCrossBaseline K k a := by
    have h : 0 ≤ sourceMacroStep k*(a : ℝ) := by unfold sourceMacroStep; positivity
    unfold sourceCrossBaseline
    linarith
  have herr : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      |D a i j-(sourceCrossBaseline K k a+sourceAlpha k i+sourceBeta k j)| ≤ sourceError K k := by
    intro a ha i hi j hj
    exact source_cross_error (D a i j) K k a i j hK hk hi hj (hD a ha i hi j hj)
      (hsq a ha i hi j hj)
  have hpos : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 < D a i j := by
    intro a ha i hi j hj
    have he := (abs_le.mp (herr a ha i hi j hj)).1
    have hu := (abs_le.mp (source_digit_sum_bound k i j hk hi hj)).1
    have hb := hν a
    have ht := source_error_lt_Tmin K k hK hk'
    unfold sourceTmin at ht
    linarith
  have hbase : ∀ a, a+1 < M → sourceMacroStep k ≤
      sourceCrossBaseline K k (a+1)-sourceCrossBaseline K k a := by
    intro a _
    simp only [sourceCrossBaseline,Nat.cast_add,Nat.cast_one]
    linarith
  exact direct_cross_spectrum_separated D (sourceCrossBaseline K k) (sourceDigit k) M k (by omega)
    (9/8) ((9/8)*(k : ℝ)) (255/256) (((k : ℝ)-1)/2)
    (sourceError K k) (sourceMacroStep k) (sourceBaseline K k)
    (by norm_num) (by positivity) (fun a _ => hν a)
    (source_baseline_exceeds_fine_bound K k hK hk')
    (fun i hi => sourceDigit_bound k i hk hi) (fun i hi => sourceDigit_step k i hk hi)
    hbase hpos hsq herr (by norm_num)
    (by simpa only [sourcePerturbationBound] using source_direct_fine_guard K k hK hk')
    (source_direct_carry_guard K k hK hk')
    (by simpa only [sourcePerturbationBound] using source_direct_macro_guard K k hK hk')

/-- The source's actual ceiling choice now discharges the macro-size premise. -/
theorem source_offset_cross_spectrum_separated (D : ℕ → ℕ → ℕ → ℝ) (M m k : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k)
    (hD : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 ≤ D a i j)
    (hsq : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      (D a i j)^2=(sourceCrossBaseline (sourceOffset m) k a+sourceAlpha k i+sourceBeta k j)^2-
        2*sourceAlpha k i*sourceBeta k j) :
    ∀ a i j b u v, a < M → i < k → j < k → b < M → u < k → v < k →
      (a,i,j) ≠ (b,u,v) → 1 ≤ |D a i j-D b u v| := by
  exact source_cross_spectrum_separated D M k (sourceOffset m) hk (sourceOffset_lower m hm) hD hsq

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRulerSeparation.lean
section

/-! Exact integer-ruler layer. Unlike a residue-only statement, these theorems
refer to the actual differences of the explicit ruler positions. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The unscaled deterministic integer ruler. The geometric candidate uses 3 times this. -/
def primeRuler (p k A i : ℕ) : ℤ :=
  4 * (p : ℤ) * (i : ℤ) + ((i^2 + 2*k*A*i) % p : ℕ)

/-- A positive-lag difference, kept in the integers so subtraction never truncates. -/
def primeRulerGap (p k A i δ : ℕ) : ℤ :=
  primeRuler p k A (i + δ) - primeRuler p k A i

/-- Every actual ruler difference lies in its strict lag window. -/
theorem primeRulerGap_window (p k A i δ : ℕ) (hp : 0 < p) :
    (4 * (δ : ℤ) - 1) * p < primeRulerGap p k A i δ ∧
      primeRulerGap p k A i δ < (4 * (δ : ℤ) + 1) * p := by
  have h₀ : (0 : ℤ) ≤ ((i^2 + 2*k*A*i) % p : ℕ) := by positivity
  have h₁ : (0 : ℤ) ≤ (((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) := by positivity
  have h₂ : (((i^2 + 2*k*A*i) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  have h₃ : ((((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  dsimp [primeRulerGap, primeRuler]
  push_cast at *
  constructor <;> nlinarith

/-- Strictly positive lags give positive actual ruler gaps. -/
theorem primeRulerGap_pos (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ) :
    0 < primeRulerGap p k A i δ := by
  have hw := (primeRulerGap_window p k A i δ hp).1
  have hδ' : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  nlinarith

/-- Different lag windows are strictly ordered, with a gap greater than 2p. -/
theorem primeRulerGap_different_lag (p k A B i j δ ε : ℕ)
    (hp : 0 < p) (hδε : δ < ε) :
    2 * (p : ℤ) < primeRulerGap p k B j ε - primeRulerGap p k A i δ := by
  have h₀ := (primeRulerGap_window p k A i δ hp).2
  have h₁ := (primeRulerGap_window p k B j ε hp).1
  have hδε' : (δ : ℤ) + 1 ≤ ε := by exact_mod_cast hδε
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  nlinarith

/-- The actual ruler difference has exactly the stated quadratic residue. -/
theorem primeRulerGap_residue (p k A i δ : ℕ) :
    primeRulerGap p k A i δ % (p : ℤ) =
      ((δ * (2*i + δ + 2*k*A) : ℕ) : ℤ) % (p : ℤ) := by
  have hpoly : (((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
      ((i^2 + 2*k*A*i : ℕ) : ℤ) = ((δ*(2*i+δ+2*k*A) : ℕ) : ℤ) := by
    push_cast
    ring
  calc
    primeRulerGap p k A i δ % (p : ℤ) =
        ((((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
          ((i^2 + 2*k*A*i : ℕ) : ℤ)) % (p : ℤ) := by
      simp [primeRulerGap, primeRuler, Int.add_emod, Int.sub_emod,
        Int.mul_emod, Int.natCast_emod]
    _ = _ := congrArg (fun z : ℤ => z % (p : ℤ)) hpoly

/-- Equal same-lag *actual* gaps force the same cluster and starting index. -/
theorem primeRulerGap_same_lag_injective (p m k δ A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hδp : δ < p) (hsize : 2*m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : primeRulerGap p k A i δ = primeRulerGap p k B j δ) : A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [primeRulerGap_residue, primeRulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective p m k δ A B i j hp hδ hδp hsize hA hB hi hj hnat

/-- Exhaustive uniqueness of all positive actual ruler gaps, across all clusters.
Different lags use disjoint windows; equal lags use prime cancellation. -/
theorem primeRulerGap_injective (p m k δ ε A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k)
    (heq : primeRulerGap p k A i δ = primeRulerGap p k B j ε) :
    A = B ∧ i = j ∧ δ = ε := by
  have hδε : δ = ε := by
    rcases lt_trichotomy δ ε with hlt | he | hgt
    · have h := primeRulerGap_different_lag p k A B i j δ ε hp.pos hlt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
    · exact he
    · have h := primeRulerGap_different_lag p k B A j i ε δ hp.pos hgt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
  subst ε
  obtain ⟨hAB,hij⟩ := primeRulerGap_same_lag_injective p m k δ A B i j
    hp hδ hδp hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩

/-- Useful coarse window: each positive-lag gap lies strictly between 3pδ and 5pδ. -/
theorem primeRulerGap_linear_bounds (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ) :
    3 * (p : ℤ) * δ < primeRulerGap p k A i δ ∧
      primeRulerGap p k A i δ < 5 * (p : ℤ) * δ := by
  obtain ⟨h₀,h₁⟩ := primeRulerGap_window p k A i δ hp
  have hδ' : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  constructor <;> nlinarith

/-- The actual t=3 ruler has gaps separated by at least 3 as real numbers.
This is across all macro clusters, not just within an individual ruler. -/
theorem scaled_primeRulerGap_separated (p m k δ ε A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬ (A = B ∧ i = j ∧ δ = ε)) :
    3 ≤ |3 * (primeRulerGap p k A i δ : ℝ) - 3 * (primeRulerGap p k B j ε : ℝ)| := by
  have hg : primeRulerGap p k A i δ ≠ primeRulerGap p k B j ε := by
    intro h
    exact hne (primeRulerGap_injective p m k δ ε A B i j
      hp hδ hε hδp hεp hsize hA hB hi hj h)
  have habs : (0 : ℤ) < |primeRulerGap p k A i δ - primeRulerGap p k B j ε| :=
    abs_pos.mpr (sub_ne_zero.mpr hg)
  have habs' : (1 : ℤ) ≤ |primeRulerGap p k A i δ - primeRulerGap p k B j ε| := by omega
  have hreal : (1 : ℝ) ≤ |(primeRulerGap p k A i δ : ℝ) -
      (primeRulerGap p k B j ε : ℝ)| := by exact_mod_cast habs'
  rw [← mul_sub, abs_mul]
  norm_num
  linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.LocalRulerSeparation.lean
section

/-! All local ruler-distance models, across every cluster and lag, are separated.
Only explicit scalar guards remain; no local-separation hypothesis is assumed. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def rulerArc (p k A i δ : ℕ) : ℝ := 3*(primeRulerGap p k A i δ : ℝ)

/-- One universal arc ceiling, exploiting the actual endpoint constraint i+δ<k. -/
theorem rulerArc_upper (p k A i δ : ℕ) (hp : 0 < p) (hi : i+δ < k) :
    rulerArc p k A i δ ≤ 12*(p : ℝ)*k := by
  have h := (primeRulerGap_window p k A i δ hp).2
  have hr : (primeRulerGap p k A i δ : ℝ) < (4*(δ : ℝ)+1)*p := by exact_mod_cast h
  have hδ : (δ : ℝ)+1 ≤ k := by exact_mod_cast (show δ+1 ≤ k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold rulerArc
  nlinarith

/-- The source's lower arc estimate 3tpδ for t=3. -/
theorem rulerArc_lower (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ) :
    9*(p : ℝ)*δ ≤ rulerArc p k A i δ := by
  have h := (primeRulerGap_linear_bounds p k A i δ hp hδ).1
  have hr : 3*(p : ℝ)*δ < (primeRulerGap p k A i δ : ℝ) := by exact_mod_cast h
  unfold rulerArc
  linarith

/-- Increasing arcs cannot come from decreasing lag bands. -/
theorem rulerArc_order_forces_lag_order (p k A B i j δ ε : ℕ) (hp : 0 < p)
    (h : rulerArc p k A i δ ≤ rulerArc p k B j ε) : δ ≤ ε := by
  by_contra hnot
  have hh := primeRulerGap_different_lag p k B A j i ε δ hp (by omega)
  have hr : 2*(p : ℝ) < (primeRulerGap p k A i δ : ℝ)-(primeRulerGap p k B j ε : ℝ) := by
    exact_mod_cast hh
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold rulerArc at h
  linarith

/-- Exhaustive local/local separation for the explicit ruler and two harmonics.
Distinct triples represent distinct local unordered pairs. The proof handles
same-lag and different-lag cases without assuming their distance separation. -/
theorem local_ruler_model_separated (p m k A B i j δ ε : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬ (A=B ∧ i=j ∧ δ=ε))
    (R Y θ b₁ b₂ J : ℝ) (hR : 0 < R) (hY : 12*(p : ℝ)*k ≤ Y)
    (hangle : Y/(2*R) ≤ Real.pi) (hγ : 0 < Real.cos (Y/(2*R)))
    (hθ : 0 ≤ θ) (hfeature : θ*k ≤ Real.pi/2) (hJ : 0 ≤ J)
    (hJbound : θ^2*(b₁^2+4*b₂^2) ≤ J^2)
    (hguard : 1 ≤ 3*(Real.cos (Y/(2*R))/
      Real.sqrt (1+(J/(9*(p : ℝ)*Real.cos (Y/(2*R))))^2))) :
    1 ≤ |localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ)-
      localDistanceModel R θ b₁ b₂ ε (rulerArc p k B j ε)| := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hSlope : 0 ≤ Real.cos (Y/(2*R))/
      Real.sqrt (1+(J/(9*(p : ℝ)*Real.cos (Y/(2*R))))^2) := by positivity
  have hsep := scaled_primeRulerGap_separated p m k δ ε A B i j
    hp hδ hε hδp hεp hsize hA hB hi hj hne
  change 3 ≤ |rulerArc p k A i δ-rulerArc p k B j ε| at hsep
  have hord : ∀ (A B i j δ ε : ℕ), 0 < δ → 0 < ε → i+δ < k → j+ε < k →
      rulerArc p k A i δ ≤ rulerArc p k B j ε →
      3 ≤ rulerArc p k B j ε-rulerArc p k A i δ →
      1 ≤ localDistanceModel R θ b₁ b₂ ε (rulerArc p k B j ε)-
        localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ) := by
    intro A B i j δ ε hd he hi hj hxy hgap
    have hδε := rulerArc_order_forces_lag_order p k A B i j δ ε hp.pos hxy
    have he' : (ε : ℝ) ≤ k := by exact_mod_cast (show ε ≤ k by omega)
    have hfeat : θ*(ε : ℝ) ≤ Real.pi/2 :=
      (mul_le_mul_of_nonneg_left he' hθ).trans hfeature
    have h := localDistanceModel_lower_gap R Y θ b₁ b₂ δ ε
      (rulerArc p k A i δ) (rulerArc p k B j ε) J (9*(p : ℝ))
      hR hangle hγ hθ (by exact_mod_cast hd) (by exact_mod_cast hδε) hfeat
      (by positivity) (rulerArc_lower p k A i δ hp.pos hd)
      (rulerArc_lower p k B j ε hp.pos he) hxy
      ((rulerArc_upper p k B j ε hp.pos hj).trans hY) hJ hJbound
    have hm := mul_le_mul_of_nonneg_left hgap hSlope
    nlinarith
  rcases le_total (rulerArc p k A i δ) (rulerArc p k B j ε) with hxy | hyx
  · have hg : 3 ≤ rulerArc p k B j ε-rulerArc p k A i δ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hsep
      linarith
    have h := hord A B i j δ ε hδ hε hi hj hxy hg
    have hab := le_abs_self (localDistanceModel R θ b₁ b₂ ε (rulerArc p k B j ε)-
      localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ))
    rw [abs_sub_comm] at hab
    exact h.trans hab
  · have hg : 3 ≤ rulerArc p k A i δ-rulerArc p k B j ε := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hsep
      exact hsep
    exact (hord B A j i ε δ hε hδ hj hi hyx hg).trans (le_abs_self _)

/-- The minimum local distance is checked separately; pairwise gaps do not imply it. -/
theorem local_ruler_model_ge_one (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ)
    (hi : i+δ < k) (R Y θ b₁ b₂ : ℝ) (hR : 0 < R) (hY : 12*(p : ℝ)*k ≤ Y)
    (hangle : Y/(2*R) ≤ Real.pi) (hγ : 0 ≤ Real.cos (Y/(2*R)))
    (hguard : 1 ≤ Real.cos (Y/(2*R))*(9*(p : ℝ))) :
    1 ≤ localDistanceModel R θ b₁ b₂ δ (rulerArc p k A i δ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hδ' : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hl := rulerArc_lower p k A i δ hp hδ
  have hd : 0 ≤ rulerArc p k A i δ := by nlinarith
  have hC := circleChord_lower R Y (rulerArc p k A i δ) hR hangle hd
    ((rulerArc_upper p k A i δ hp hi).trans hY)
  have hmul := mul_le_mul_of_nonneg_left
    (show 9*(p : ℝ) ≤ rulerArc p k A i δ by nlinarith) hγ
  have hC₁ : 1 ≤ circleChord R (rulerArc p k A i δ) := by linarith
  have hsq := localDistanceModel_square R θ b₁ b₂ δ (rulerArc p k A i δ)
  have hpos := localDistanceModel_nonneg R θ b₁ b₂ δ (rulerArc p k A i δ)
  have hQ := harmonicEnergy_nonneg θ b₁ b₂ δ
  nlinarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceLocalGuards.lean
section

/-! Coarse rational guards sufficient for all source local distances.
The budget600 deliberately leaves slack above the source's J² envelope. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The literal radius makes the universal ruler half-angle at most one quarter. -/
theorem source_local_angle_bound (m k R : ℝ) (hm : 0 < m) (hk : 0 < k) (hR : 0 < R)
    (hRsq : R^2=17500*m^2*k^4) : (48*m*k^2)/(2*R) ≤ 1/4 := by
  have ht : 0 < m*k^2 := mul_pos hm (sq_pos_of_pos hk)
  have he : R^2=17500*(m*k^2)^2 := by nlinarith only [hRsq]
  have hl : 96*(m*k^2) ≤ R := by nlinarith
  apply (div_le_iff₀ (show 0 < 2*R by positivity)).2
  nlinarith

/-- A conservative 9/10 lower cosine bound follows uniformly, with no sample grid. -/
theorem source_local_cosine_lower (m k R : ℝ) (hm : 0 < m) (hk : 0 < k) (hR : 0 < R)
    (hRsq : R^2=17500*m^2*k^4) :
    (9/10 : ℝ) ≤ Real.cos ((48*m*k^2)/(2*R)) := by
  have h₀ : 0 ≤ (48*m*k^2)/(2*R) := by positivity
  have h₁ := source_local_angle_bound m k R hm hk hR hRsq
  have hcos := Real.one_sub_sq_div_two_le_cos (x := (48*m*k^2)/(2*R))
  have hs : ((48*m*k^2)/(2*R))^2 ≤ (1/4 : ℝ)^2 := by nlinarith
  nlinarith

/-- One abstract local-slope guard, with a deliberately slack universal budget. -/
theorem local_slope_guard_of_coarse_budget (u p γ J : ℝ)
    (hu : 0 < u) (hp : 2*u ≤ p) (hγ : 9/10 ≤ γ) (hJ : J^2 ≤ 600*u^2) :
    1 ≤ 3*(γ/Real.sqrt (1+(J/(9*p*γ))^2)) := by
  have hp₀ : 0 < p := by linarith
  have hγ₀ : 0 < γ := by linarith
  have hd : 0 < 9*p*γ := by positivity
  have hg := mul_le_mul_of_nonneg_left hγ (show 0 ≤ 9*p by positivity)
  have hden : 15*u ≤ 9*p*γ := by nlinarith
  have hs := (sq_le_sq₀ (show 0 ≤ 15*u by positivity) hd.le).2 hden
  have hq : (J/(9*p*γ))^2 ≤ 3 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    nlinarith
  have hsqrt : Real.sqrt (1+(J/(9*p*γ))^2) ≤ 2 := by
    have h := Real.sqrt_le_sqrt (show 1+(J/(9*p*γ))^2 ≤ 4 by linarith)
    norm_num at h
    exact h
  have hsqrtpos : 0 < Real.sqrt (1+(J/(9*p*γ))^2) := Real.sqrt_pos.2 (by positivity)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hsqrtpos).2
  nlinarith

/-- Uniform source local slope certificate in the original m,k,p,R,J variables. -/
theorem source_local_slope_guard (m k p R J : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hp : 2*m*k ≤ p) (hR : 0 < R)
    (hRsq : R^2=17500*m^2*k^4) (hJ : J^2 ≤ 600*m^2*k^2) :
    1 ≤ 3*(Real.cos ((48*m*k^2)/(2*R))/
      Real.sqrt (1+(J/(9*p*Real.cos ((48*m*k^2)/(2*R))))^2)) := by
  apply local_slope_guard_of_coarse_budget (m*k) p _ J (mul_pos hm hk)
    (by nlinarith) (source_local_cosine_lower m k R hm hk hR hRsq)
  nlinarith only [hJ]

/-- The first positive local distance clears zero by a separate uniform estimate. -/
theorem source_local_zero_guard (m k p R : ℝ) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hp : 2*m*k ≤ p) (hR : 0 < R) (hRsq : R^2=17500*m^2*k^4) :
    1 ≤ Real.cos ((48*m*k^2)/(2*R))*(9*p) := by
  have hm₀ : 0 < m := by linarith
  have hk₀ : 0 < k := by linarith
  have hcos := source_local_cosine_lower m k R hm₀ hk₀ hR hRsq
  have hmk : 2 ≤ m*k := by nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hk)]
  have hp₀ : 0 < p := by nlinarith
  have h := mul_le_mul_of_nonneg_right hcos (show 0 ≤ 9*p by positivity)
  nlinarith

/-- The documented exact source operator envelope is strictly below the slack budget600. -/
theorem source_J_budget_below_six_hundred :
    (20175033783589348897071 : ℝ)/38009099183104000000 < 600 := by norm_num

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceLocalSpectrum.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def sourceRadius (m k : ℕ) : ℝ := Real.sqrt 17500*(m : ℝ)*(k : ℝ)^2
noncomputable def sourceTheta (k : ℕ) : ℝ := Real.sqrt (1/32)/(k : ℝ)
noncomputable def sourceLocalDistance (p m k : ℕ) (b₁ b₂ : ℝ) (A i δ : ℕ) : ℝ :=
  localDistanceModel (sourceRadius m k) (sourceTheta k) b₁ b₂ δ (rulerArc p k A i δ)

theorem sourceRadius_square (m k : ℕ) :
    (sourceRadius m k)^2=17500*(m : ℝ)^2*(k : ℝ)^4 := by
  unfold sourceRadius
  rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num)]
  ring

theorem sourceRadius_pos (m k : ℕ) (hm : 0 < m) (hk : 0 < k) : 0 < sourceRadius m k := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold sourceRadius
  positivity

theorem sourceTheta_pos (k : ℕ) (hk : 0 < k) : 0 < sourceTheta k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold sourceTheta
  positivity

theorem sourceTheta_feature_angle (k : ℕ) (hk : 0 < k) : sourceTheta k*(k : ℝ) ≤ Real.pi/2 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have he : sourceTheta k*(k : ℝ)=Real.sqrt (1/32) := by unfold sourceTheta; field_simp
  rw [he]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1/32 by norm_num)
  have hn := Real.sqrt_nonneg (1/32 : ℝ)
  have hp := Real.two_le_pi
  nlinarith

/-- All source local distances are separated, uniformly in m,k, once the
whole-operator harmonic budget is supplied. Radius, sine, arc and slope guards
are discharged internally, rather than exposed as conclusion-sized premises. -/
theorem source_local_spectrum_separated (p m k A B i j δ ε : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hp : p.Prime)
    (hsize : 2*m*k < p) (hupper : p < 4*m*k)
    (hA : A < m) (hB : B < m) (hδ : 0 < δ) (hε : 0 < ε)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬(A=B ∧ i=j ∧ δ=ε))
    (b₁ b₂ : ℝ)
    (hbudget : (sourceTheta k)^2*(b₁^2+4*b₂^2) ≤ 600*(m : ℝ)^2*(k : ℝ)^2) :
    1 ≤ |sourceLocalDistance p m k b₁ b₂ A i δ-sourceLocalDistance p m k b₁ b₂ B j ε| := by
  let R := sourceRadius m k
  let Y : ℝ := 48*(m : ℝ)*(k : ℝ)^2
  let J := Real.sqrt ((sourceTheta k)^2*(b₁^2+4*b₂^2))
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR : 0 < R := sourceRadius_pos m k (by omega) (by omega)
  have hRsq : R^2=17500*(m : ℝ)^2*(k : ℝ)^4 := sourceRadius_square m k
  have hpLower : 2*(m : ℝ)*(k : ℝ) ≤ p := by exact_mod_cast hsize.le
  have hpUpper : (p : ℝ) ≤ 4*(m : ℝ)*(k : ℝ) := by exact_mod_cast hupper.le
  have hY : 12*(p : ℝ)*k ≤ Y := by
    have h := mul_le_mul_of_nonneg_right hpUpper (show 0 ≤ 12*(k : ℝ) by positivity)
    dsimp [Y]
    nlinarith
  have hangle : Y/(2*R) ≤ Real.pi := by
    have h := source_local_angle_bound m k R hm₀ hk₀ hR hRsq
    dsimp [Y]
    linarith [Real.two_le_pi]
  have hγ : 0 < Real.cos (Y/(2*R)) := by
    have h := source_local_cosine_lower m k R hm₀ hk₀ hR hRsq
    dsimp [Y]
    linarith
  have hJsq : J^2=(sourceTheta k)^2*(b₁^2+4*b₂^2) := Real.sq_sqrt (by positivity)
  have hJbudget : J^2 ≤ 600*(m : ℝ)^2*(k : ℝ)^2 := hJsq ▸ hbudget
  have hkp : k < p := by
    have hh : k ≤ 2*m*k := by
      have hm₁ : 1 ≤ 2*m := by omega
      simpa using Nat.mul_le_mul_right k hm₁
    exact lt_of_le_of_lt hh hsize
  exact local_ruler_model_separated p m k A B i j δ ε hp hδ hε
    (lt_trans (by omega) hkp) (lt_trans (by omega) hkp) hsize hA hB hi hj hne
    R Y (sourceTheta k) b₁ b₂ J hR hY hangle hγ
    (sourceTheta_pos k (by omega)).le (sourceTheta_feature_angle k (by omega))
    (Real.sqrt_nonneg _) hJsq.ge
    (source_local_slope_guard m k p R J hm₀ hk₀ hpLower hR hRsq hJbudget)

/-- Zero is handled independently for the source's actual radius and prime bounds. -/
theorem source_local_distance_ge_one (p m k A i δ : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hp : 0 < p)
    (hsize : 2*m*k < p) (hupper : p < 4*m*k) (hδ : 0 < δ) (hi : i+δ < k)
    (b₁ b₂ : ℝ) : 1 ≤ sourceLocalDistance p m k b₁ b₂ A i δ := by
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR := sourceRadius_pos m k (by omega) (by omega)
  have hRsq := sourceRadius_square m k
  have hpLower : 2*(m : ℝ)*(k : ℝ) ≤ p := by exact_mod_cast hsize.le
  have hpUpper : (p : ℝ) ≤ 4*(m : ℝ)*(k : ℝ) := by exact_mod_cast hupper.le
  have hY : 12*(p : ℝ)*k ≤ 48*(m : ℝ)*(k : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_right hpUpper (show 0 ≤ 12*(k : ℝ) by positivity)
    nlinarith
  have hangle := source_local_angle_bound m k (sourceRadius m k) hm₀ hk₀ hR hRsq
  have hγ := source_local_cosine_lower m k (sourceRadius m k) hm₀ hk₀ hR hRsq
  exact local_ruler_model_ge_one p k A i δ hp hδ hi (sourceRadius m k)
    (48*(m : ℝ)*(k : ℝ)^2) (sourceTheta k) b₁ b₂ hR hY
    (by linarith [Real.two_le_pi]) (by linarith)
    (source_local_zero_guard m k p (sourceRadius m k)
      (by exact_mod_cast (show 1 ≤ m by omega)) (by exact_mod_cast hk) hpLower hR hRsq)

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceMixedBands.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- A radius budget for the two harmonic features bounds every local length,
without a restriction on the arc or the lag. -/
theorem localDistanceModel_le_three_radius (R θ b₁ b₂ δ d : ℝ)
    (hR : 0 ≤ R) (hbudget : b₁ ^ 2 + b₂ ^ 2 ≤ R ^ 2) :
    localDistanceModel R θ b₁ b₂ δ d ≤ 3 * R := by
  have hc₀ := Real.sin_sq_le_one (d / (2 * R))
  have hc := mul_le_mul_of_nonneg_left hc₀ (show 0 ≤ 4 * R ^ 2 by positivity)
  have hc' : (circleChord R d) ^ 2 ≤ 4 * R ^ 2 := by
    unfold circleChord
    nlinarith only [hc]
  have he₀ := Real.sin_sq_le_one (θ * δ / 2)
  have he₁ := Real.sin_sq_le_one (θ * δ)
  have he₀' := mul_le_mul_of_nonneg_left he₀ (show 0 ≤ 4 * b₁ ^ 2 by positivity)
  have he₁' := mul_le_mul_of_nonneg_left he₁ (show 0 ≤ 4 * b₂ ^ 2 by positivity)
  have he : harmonicEnergy θ b₁ b₂ δ ≤ 4 * (b₁ ^ 2 + b₂ ^ 2) := by
    unfold harmonicEnergy
    nlinarith only [he₀', he₁']
  have hs := localDistanceModel_square R θ b₁ b₂ δ d
  have hpos := localDistanceModel_nonneg R θ b₁ b₂ δ d
  nlinarith [sq_nonneg R]

theorem sourceOffset_ge_fivehundred_m (m : ℕ) (hm : 34000 ≤ m) :
    (500 : ℝ) * m ≤ sourceOffset m := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) ≤ m := by positivity
  have hceil := Nat.le_ceil ((m : ℝ) * ((m : ℝ) - 1) / 64)
  change (m : ℝ) * ((m : ℝ) - 1) / 64 ≤ (sourceOffset m : ℝ) at hceil
  have hmul := mul_nonneg hm₀ (show (0 : ℝ) ≤ m - 34000 by linarith)
  nlinarith

theorem sourceRadius_le_onehundredthirtythree (m k : ℕ) :
    sourceRadius m k ≤ 133 * (m : ℝ) * (k : ℝ) ^ 2 := by
  have hR : 0 ≤ sourceRadius m k := by unfold sourceRadius; positivity
  have hsq := sourceRadius_square m k
  let t : ℝ := (m : ℝ) * (k : ℝ) ^ 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsq' : (sourceRadius m k) ^ 2 = 17500 * t ^ 2 := by
    dsimp [t]
    nlinarith only [hsq]
  calc
    sourceRadius m k ≤ 133 * t := by nlinarith [sq_nonneg t]
    _ = 133 * (m : ℝ) * (k : ℝ) ^ 2 := by dsimp [t]; ring

theorem source_mixed_scalar_budget (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    3 * sourceRadius m k + 1 ≤
      sourceTmin (sourceOffset m) k - sourceError (sourceOffset m) k := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK := sourceOffset_ge_fivehundred_m m hm
  have hKfixed := sourceOffset_lower m hm
  have hmul := mul_le_mul_of_nonneg_left hK (sq_nonneg (k : ℝ))
  have hbase : 700 * (m : ℝ) * (k : ℝ) ^ 2 ≤
      sourceBaseline (sourceOffset m) k := by
    unfold sourceBaseline sourceMacroStep
    nlinarith [hmul]
  have hpert := source_perturbation_quadratic_bound (k : ℝ) hk'
  have herr := source_error_linear_bound (sourceOffset m) k hKfixed hk'
  have hmK := mul_le_mul_of_nonneg_right hm' (sq_nonneg (k : ℝ))
  have hk₂ : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hT : 600 * (m : ℝ) * (k : ℝ) ^ 2 ≤
      sourceTmin (sourceOffset m) k - sourceError (sourceOffset m) k := by
    unfold sourceTmin
    nlinarith
  have hR := sourceRadius_le_onehundredthirtythree m k
  have hmk : 1 ≤ (m : ℝ) * (k : ℝ) ^ 2 := by nlinarith [hmK]
  nlinarith

/-- The actual source cross distance lies above every local distance once the
local harmonic reserves fit inside the common radius budget. -/
theorem source_local_cross_gap (D b₁ b₂ : ℝ) (p m k A l δ a i j : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hi : i < k) (hj : j < k)
    (hD : 0 ≤ D)
    (hsq : D ^ 2 =
      (sourceCrossBaseline (sourceOffset m) k a + sourceAlpha k i + sourceBeta k j) ^ 2 -
        2 * sourceAlpha k i * sourceBeta k j)
    (hbudget : b₁ ^ 2 + b₂ ^ 2 ≤ (sourceRadius m k) ^ 2) :
    1 ≤ D - sourceLocalDistance p m k b₁ b₂ A l δ := by
  have hK := sourceOffset_lower m hm
  have herr := source_cross_error D (sourceOffset m) k a i j hK hk hi hj hD hsq
  have hpert := source_digit_sum_bound k i j hk hi hj
  have hbase : sourceBaseline (sourceOffset m) k ≤
      sourceCrossBaseline (sourceOffset m) k a := by
    have hnonneg : 0 ≤ sourceMacroStep k * (a : ℝ) := by
      unfold sourceMacroStep
      positivity
    unfold sourceCrossBaseline
    linarith
  have hcross : sourceTmin (sourceOffset m) k - sourceError (sourceOffset m) k ≤ D := by
    have he := (abs_le.mp herr).1
    have hp := (abs_le.mp hpert).1
    unfold sourceTmin at *
    linarith
  have hR : 0 ≤ sourceRadius m k := by unfold sourceRadius; positivity
  have hlocal : sourceLocalDistance p m k b₁ b₂ A l δ ≤ 3 * sourceRadius m k := by
    unfold sourceLocalDistance
    exact localDistanceModel_le_three_radius _ _ _ _ _ _ hR hbudget
  linarith [source_mixed_scalar_budget m k hm hk]

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceReserveBudgets.lean
section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Algebraically normalized squares of the source's constant/second-harmonic reserves. -/
noncomputable def sourceReserve0Sq (m k : ℕ) : ℝ :=
  3888*(m : ℝ)^2*(k : ℝ)^4/(sourceOffset m : ℝ)^2
/-- Algebraically normalized square of the source's first-harmonic reserve. -/
noncomputable def sourceReserve1Sq (m k : ℕ) : ℝ :=
  (21168*(9/8 : ℝ)^4*32)*(k : ℝ)^4*((sourceOffset m : ℝ)+(m : ℝ))

theorem sourceOffset_plus_m_upper (m : ℕ) (hm : 34000 ≤ m) :
    (sourceOffset m : ℝ)+(m : ℝ) ≤ (m : ℝ)^2/63 := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hnonneg : 0 ≤ (m : ℝ)*((m : ℝ)-1)/64 := by
    apply div_nonneg (mul_nonneg (by positivity) (by linarith)) (by norm_num)
  have hceil := Nat.ceil_lt_add_one hnonneg
  change (sourceOffset m : ℝ) < (m : ℝ)*((m : ℝ)-1)/64+1 at hceil
  have hmsq : (34000 : ℝ)*m ≤ (m : ℝ)^2 := by nlinarith
  nlinarith

theorem sourceReserve0Sq_bound (m k : ℕ) (hm : 34000 ≤ m) :
    sourceReserve0Sq m k ≤ (972/25 : ℝ)*(m : ℝ)^2*(k : ℝ)^4 := by
  have hK := sourceOffset_lower m hm
  have hKpos : (0 : ℝ) < sourceOffset m := by linarith
  have hKsq : (100 : ℝ) ≤ (sourceOffset m : ℝ)^2 := by nlinarith
  have hmulp := mul_le_mul_of_nonneg_left hKsq
    (show 0 ≤ (972/25 : ℝ)*(m : ℝ)^2*(k : ℝ)^4 by positivity)
  unfold sourceReserve0Sq
  apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
  nlinarith

theorem sourceReserve1Sq_bound (m k : ℕ) (hm : 34000 ≤ m) :
    sourceReserve1Sq m k ≤ (137781/8 : ℝ)*(m : ℝ)^2*(k : ℝ)^4 := by
  have h := mul_le_mul_of_nonneg_left (sourceOffset_plus_m_upper m hm)
    (show 0 ≤ (21168*(9/8 : ℝ)^4*32)*(k : ℝ)^4 by positivity)
  unfold sourceReserve1Sq
  nlinarith

/-- The full T² reserve fits strictly inside the chosen radius square. -/
theorem source_total_reserve_bound (m k : ℕ) (hm : 34000 ≤ m) :
    2*sourceReserve0Sq m k+sourceReserve1Sq m k ≤ (sourceRadius m k)^2 := by
  have h₀ := sourceReserve0Sq_bound m k hm
  have h₁ := sourceReserve1Sq_bound m k hm
  rw [sourceRadius_square]
  nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (show 0 ≤ (k : ℝ)^4 by positivity)]

/-- The actual source harmonic reserves satisfy the complete local slope budget. -/
theorem source_harmonic_reserve_bound (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    (sourceTheta k)^2*(sourceReserve1Sq m k+4*sourceReserve0Sq m k) ≤
      600*(m : ℝ)^2*(k : ℝ)^2 := by
  have h₀ := mul_le_mul_of_nonneg_left (sourceReserve0Sq_bound m k hm) (sq_nonneg (sourceTheta k))
  have h₁ := mul_le_mul_of_nonneg_left (sourceReserve1Sq_bound m k hm) (sq_nonneg (sourceTheta k))
  have hs : (sourceTheta k)^2*(k : ℝ)^2=1/32 := source_theta_scale k (by omega)
  have hmul := congrArg (fun x : ℝ => x*(m : ℝ)^2*(k : ℝ)^2) hs
  have hn : 0 ≤ (m : ℝ)^2*(k : ℝ)^2 := by positivity
  nlinarith

/-- The normalized first reserve is literally the source's original operator expression. -/
theorem sourceReserve1Sq_eq_operator_formula (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    sourceReserve1Sq m k =
      3*(84*(9/8 : ℝ)*((9/8)*(k : ℝ))*
        Real.sqrt ((sourceOffset m : ℝ)+(m : ℝ))/sourceTheta k)^2 := by
  have hK := sourceOffset_lower m hm
  have hm' : (0 : ℝ) ≤ m := by positivity
  have hsqrt := Real.sq_sqrt (show 0 ≤ (sourceOffset m : ℝ)+(m : ℝ) by positivity)
  have hθ : sourceTheta k ≠ 0 := (sourceTheta_pos k (by omega)).ne'
  have hs : (sourceTheta k)^2*(k : ℝ)^2=1/32 := source_theta_scale k (by omega)
  rw [div_pow,← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero 2 hθ)).2
  unfold sourceReserve1Sq
  simp only [mul_pow,hsqrt]
  have hmul := congrArg (fun x : ℝ => x*(k : ℝ)^2*((sourceOffset m : ℝ)+(m : ℝ))) hs
  nlinarith only [hmul]

/-- The constant/second-harmonic reserve agrees with the original source formula. -/
theorem sourceReserve0Sq_eq_original (m k : ℕ) :
    sourceReserve0Sq m k = 3*(m : ℝ)*
      ((m : ℝ)*(9/8 : ℝ)^2*(k : ℝ)^4/((1/32 : ℝ)^2*(sourceOffset m : ℝ)^2)) := by
  unfold sourceReserve0Sq
  ring

noncomputable def sourceReserve0 (m k : ℕ) : ℝ := Real.sqrt (sourceReserve0Sq m k)
noncomputable def sourceReserve1 (m k : ℕ) : ℝ := Real.sqrt (sourceReserve1Sq m k)

theorem sourceReserve0_square (m k : ℕ) : (sourceReserve0 m k)^2=sourceReserve0Sq m k := by
  apply Real.sq_sqrt
  unfold sourceReserve0Sq
  positivity

theorem sourceReserve1_square (m k : ℕ) : (sourceReserve1 m k)^2=sourceReserve1Sq m k := by
  apply Real.sq_sqrt
  unfold sourceReserve1Sq
  positivity

/-- All local spectrum scalar hypotheses are now discharged for the literal source reserves. -/
theorem concrete_source_local_spectrum_separated (p m k A B i j δ ε : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hp : p.Prime)
    (hsize : 2*m*k < p) (hupper : p < 4*m*k)
    (hA : A < m) (hB : B < m) (hδ : 0 < δ) (hε : 0 < ε)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬(A=B ∧ i=j ∧ δ=ε)) :
    1 ≤ |sourceLocalDistance p m k (sourceReserve1 m k) (sourceReserve0 m k) A i δ-
      sourceLocalDistance p m k (sourceReserve1 m k) (sourceReserve0 m k) B j ε| := by
  apply source_local_spectrum_separated p m k A B i j δ ε hm hk hp hsize hupper
    hA hB hδ hε hi hj hne
  rw [sourceReserve1_square,sourceReserve0_square]
  exact source_harmonic_reserve_bound m k hm hk

/-- The source reserves also discharge the local/cross radius reserve. -/
theorem concrete_source_local_cross_gap (D : ℝ) (p m k A l δ a i j : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) (hi : i < k) (hj : j < k) (hD : 0 ≤ D)
    (hsq : D^2=(sourceCrossBaseline (sourceOffset m) k a+sourceAlpha k i+sourceBeta k j)^2-
      2*sourceAlpha k i*sourceBeta k j) :
    1 ≤ D-sourceLocalDistance p m k (sourceReserve1 m k) (sourceReserve0 m k) A l δ := by
  apply source_local_cross_gap D (sourceReserve1 m k) (sourceReserve0 m k)
    p m k A l δ a i j hm hk hi hj hD hsq
  rw [sourceReserve1_square,sourceReserve0_square]
  have h := source_total_reserve_bound m k hm
  have h₀ : 0 ≤ sourceReserve0Sq m k := by unfold sourceReserve0Sq; positivity
  linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceFinalScalar.lean
section

/-! Scalar diameter estimates for the literal fixed-dimensional source construction. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The full source diameter cap is below `0.735 (mk)^2`, uniformly in the
number of macro clusters and the cluster size. -/
theorem source_diameter_cap_lt (m k : ℕ) (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    sourceMacroStep (k : ℝ) *
        ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
      sourcePerturbationBound (k : ℝ) +
      sourceError (sourceOffset m : ℝ) (k : ℝ) <
        (147 / 200 : ℝ) * ((m : ℝ) * (k : ℝ)) ^ 2 := by
  have hm' : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (sourceOffset m : ℝ) ≤ (m : ℝ) ^ 2 / 63 := by
    have h := sourceOffset_plus_m_upper m hm
    linarith
  have hM : (m.choose 2 : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hS : 0 ≤ sourceMacroStep (k : ℝ) := by
    unfold sourceMacroStep
    positivity
  have hmain := mul_le_mul_of_nonneg_left (add_le_add hK hM) hS
  have hA := source_perturbation_quadratic_bound (k : ℝ) hk'
  have hE := source_error_linear_bound (sourceOffset m : ℝ) (k : ℝ)
    (sourceOffset_lower m hm) hk'
  have hksq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hAE : sourcePerturbationBound (k : ℝ) +
      sourceError (sourceOffset m : ℝ) (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    nlinarith
  have hmsq : (34000 : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith
  have hmk := mul_le_mul_of_nonneg_right hmsq (sq_nonneg (k : ℝ))
  unfold sourceMacroStep at hmain
  unfold sourceMacroStep
  nlinarith

/-- Rounding from the source size `mk` to any requested `n` leaves enough
room below the target coefficient `37/50`. -/
theorem source_rounded_diameter_lt (n m k : ℕ) (hn : 68000 ≤ n)
    (hm : 34000 ≤ m) (hk : 2 ≤ k)
    (hsurplus : m * k < n + k)
    (hkbound : 34000 * k ≤ n) :
    sourceMacroStep (k : ℝ) *
        ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
      sourcePerturbationBound (k : ℝ) +
      sourceError (sourceOffset m : ℝ) (k : ℝ) <
        (37 / 50 : ℝ) * (n : ℝ) ^ 2 := by
  have hcap := source_diameter_cap_lt m k hm hk
  have hn' : (68000 : ℝ) ≤ n := by exact_mod_cast hn
  have hsize' : (m : ℝ) * (k : ℝ) < (n : ℝ) + (k : ℝ) := by
    exact_mod_cast hsurplus
  have hkbound' : (34000 : ℝ) * (k : ℝ) ≤ n := by
    exact_mod_cast hkbound
  have hratio : (m : ℝ) * (k : ℝ) < (34001 / 34000 : ℝ) * n := by
    nlinarith
  have hnonneg : 0 ≤ (m : ℝ) * (k : ℝ) := by positivity
  have hrnonneg : 0 ≤ (34001 / 34000 : ℝ) * n := by positivity
  have hsquare : ((m : ℝ) * (k : ℝ)) ^ 2 <
      ((34001 / 34000 : ℝ) * n) ^ 2 := by nlinarith
  have htarget : (147 / 200 : ℝ) *
      ((34001 / 34000 : ℝ) * n) ^ 2 < (37 / 50 : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < n by linarith)]
  nlinarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceAllNEmbedding.lean
section

/-! Distance-preserving deletion and coordinate padding for the all-size step. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

/-- The source's coordinate count fits in the claimed fixed dimension. -/
theorem source_cluster_coordinate_card_le_fixed {m : ℕ}
    (hm : 34000 ≤ m) (hmup : m ≤ 51000) :
    Fintype.card (ClusterCoordinate (Fin (m-1)) m) ≤ 458999 := by
  rw [clusterCoordinate_card m (by omega)]
  omega

/-- A family restricted along an injection retains its unit minimum. -/
theorem source_minimum_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (hf : Function.Injective f)
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) :
    ∀ a b, a ≠ b → 1 ≤ dist (P (f a)) (P (f b)) := by
  intro a b hab
  exact hmin _ _ (hf.ne hab)

/-- The induced map on non-diagonal unordered edges. -/
def sourceEdgeMap {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f) :
    Edge ι → Edge κ := fun e =>
  ⟨Sym2.map f e.1, (Sym2.isDiag_map hf).not.mpr e.2⟩

theorem sourceEdgeMap_injective {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) : Function.Injective (sourceEdgeMap f hf) := by
  intro e₁ e₂ h
  apply Subtype.ext
  exact (Sym2.map.injective hf) (congrArg Subtype.val h)

private theorem source_edgeDistance_map {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (e : Sym2 ι) :
    edgeDistance (P ∘ f) e = edgeDistance P (Sym2.map f e) := by
  induction e using Sym2.inductionOn with
  | hf a b => rfl

/-- Restricting a family along an injection preserves edge separation. -/
theorem source_separated_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (hf : Function.Injective f)
    (hsep : SeparatedConfiguration P) : SeparatedConfiguration (P ∘ f) := by
  intro e₁ e₂ hne
  have hne' : sourceEdgeMap f hf e₁ ≠ sourceEdgeMap f hf e₂ :=
    (sourceEdgeMap_injective f hf).ne hne
  convert hsep (sourceEdgeMap f hf e₁) (sourceEdgeMap f hf e₂) hne' using 1 <;>
    simp only [sourceEdgeMap, source_edgeDistance_map]

/-- Restriction cannot increase any pairwise distance bound. -/
theorem source_diameter_restrict {ι κ E : Type*} [PseudoMetricSpace E]
    (P : κ → E) (f : ι → κ) (D : ℝ)
    (hdiam : ∀ a b, dist (P a) (P b) ≤ D) :
    ∀ a b, dist (P (f a)) (P (f b)) ≤ D := by
  intro a b
  exact hdiam _ _

/-- Extend coordinates by zero along a disjoint sum. -/
noncomputable def sourceSumPad {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (ι ⊕ κ) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun _ => 0))

theorem sourceSumPad_dist {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : EuclideanSpace ℝ ι) :
    dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y) = dist x y := by
  have hsq : dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y)^2 =
      dist x y ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
    simp [sourceSumPad, Fintype.sum_sum_type]
  nlinarith [show 0 ≤ dist (sourceSumPad (κ := κ) x) (sourceSumPad (κ := κ) y) from dist_nonneg,
    show 0 ≤ dist x y from dist_nonneg]

/-- Pad an arbitrary finite Euclidean coordinate type into `Fin D`. -/
noncomputable def sourcePadCoordinates {ι : Type*} [Fintype ι] {D : ℕ}
    (hcard : Fintype.card ι ≤ D) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (Fin D) :=
  let e₁ := Fintype.equivFin ι
  let e₂ : Fin (Fintype.card ι) ⊕ Fin (D - Fintype.card ι) ≃
      Fin (Fintype.card ι + (D - Fintype.card ι)) := finSumFinEquiv
  let e₃ := finCongr (Nat.add_sub_of_le hcard)
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₃)
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₂)
      (sourceSumPad (κ := Fin (D - Fintype.card ι))
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e₁) x)))

theorem sourcePadCoordinates_dist {ι : Type*} [Fintype ι] {D : ℕ}
    (hcard : Fintype.card ι ≤ D) (x y : EuclideanSpace ℝ ι) :
    dist (sourcePadCoordinates hcard x) (sourcePadCoordinates hcard y) = dist x y := by
  simp [sourcePadCoordinates, sourceSumPad_dist]

/-- Delete the surplus vertices by taking the first `n` positions of a finite
enumeration of the rectangular cluster grid. -/
noncomputable def sourceDeletionEmbedding {n m k : ℕ} (hsize : n ≤ m*k) :
    Fin n → Fin m × Fin k :=
  (Fintype.equivFinOfCardEq (α := Fin m × Fin k) (by simp)).symm ∘
    Fin.castLE hsize

theorem sourceDeletionEmbedding_injective {n m k : ℕ} (hsize : n ≤ m*k) :
    Function.Injective (sourceDeletionEmbedding hsize) := by
  exact (Fintype.equivFinOfCardEq (α := Fin m × Fin k) (by simp)).symm.injective.comp
    (Fin.castLE_injective hsize)

/-- Isometric coordinate padding preserves minimum, unordered-edge gaps and diameter. -/
theorem source_pad_properties {ι κ : Type*} [Fintype κ] {D : ℕ}
    (hcard : Fintype.card κ ≤ D) (P : ι → EuclideanSpace ℝ κ)
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : SeparatedConfiguration P) (B : ℝ)
    (hdiam : ∀ a b, dist (P a) (P b) ≤ B) :
    (∀ a b, a ≠ b → 1 ≤ dist (sourcePadCoordinates hcard (P a))
      (sourcePadCoordinates hcard (P b))) ∧
    SeparatedConfiguration (sourcePadCoordinates hcard ∘ P) ∧
    (∀ a b, dist (sourcePadCoordinates hcard (P a))
      (sourcePadCoordinates hcard (P b)) ≤ B) := by
  constructor
  · intro a b hab
    rw [sourcePadCoordinates_dist]
    exact hmin a b hab
  constructor
  · intro e₁ e₂ hne
    induction e₁ using Subtype.rec with
    | _ s hs =>
      induction e₂ using Subtype.rec with
      | _ t ht =>
        induction s using Sym2.inductionOn with
        | hf a b =>
          induction t using Sym2.inductionOn with
          | hf c d =>
            simpa only [edgeDistance, Sym2.lift_mk, Function.comp_apply,
              sourcePadCoordinates_dist] using hsep ⟨s(a,b),hs⟩ ⟨s(c,d),ht⟩ hne
  · intro a b
    rw [sourcePadCoordinates_dist]
    exact hdiam a b

/-- The finite source's three metric properties pass to exactly `n` points
in the same fixed ambient space. The finite source facts are explicit hypotheses. -/
theorem source_delete_pad_fixed_dimension {n m k : ℕ}
    (hn : 68000 ≤ n) (hm : 34000 ≤ m) (hmup : m ≤ 51000)
    (hk : 2 ≤ k) (hsize : n ≤ m*k) (hsurplus : m*k < n+k)
    (hkbound : 34000*k ≤ n)
    (P : Fin m × Fin k → EuclideanSpace ℝ
      (ClusterCoordinate (Fin (m-1)) m))
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : SeparatedConfiguration P)
    (hdiam : ∀ a b, dist (P a) (P b) ≤
      sourceMacroStep (k : ℝ) *
          ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
        sourcePerturbationBound (k : ℝ) +
        sourceError (sourceOffset m : ℝ) (k : ℝ)) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin 458999),
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      SeparatedConfiguration Q ∧
      (∀ a b, dist (Q a) (Q b) < (37/50 : ℝ)*(n:ℝ)^2) := by
  let f := sourceDeletionEmbedding hsize
  have hf : Function.Injective f := sourceDeletionEmbedding_injective hsize
  let hc := source_cluster_coordinate_card_le_fixed hm hmup
  let B := sourceMacroStep (k : ℝ) *
          ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
        sourcePerturbationBound (k : ℝ) +
        sourceError (sourceOffset m : ℝ) (k : ℝ)
  have hmin' := source_minimum_restrict P f hf hmin
  have hsep' := source_separated_restrict P f hf hsep
  have hdiam' := source_diameter_restrict P f B hdiam
  obtain ⟨hminQ, hsepQ, hdiamQ⟩ :=
    source_pad_properties hc (P ∘ f) hmin' hsep' B hdiam'
  refine ⟨sourcePadCoordinates hc ∘ P ∘ f, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hminQ
  · simpa only [Function.comp_assoc] using hsepQ
  · intro a b
    have hbound := source_rounded_diameter_lt n m k hn hm hk hsurplus hkbound
    exact lt_of_le_of_lt (by simpa only [Function.comp_apply] using hdiamQ a b) hbound

/-- Honest all-`n` interface: a finite source at each rectangular parameter
supplies the three geometric facts, and this theorem performs the rounding,
deletion and zero-coordinate embedding. -/
theorem source_all_n_fixed_dimension_of_finite_sources
    (hsource : ∀ m k : ℕ, 34000 ≤ m → m ≤ 51000 → 2 ≤ k →
      ∃ P : Fin m × Fin k → EuclideanSpace ℝ
          (ClusterCoordinate (Fin (m-1)) m),
        (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
        SeparatedConfiguration P ∧
        (∀ a b, dist (P a) (P b) ≤
          sourceMacroStep (k : ℝ) *
              ((sourceOffset m : ℝ) + (m.choose 2 : ℝ)) +
            sourcePerturbationBound (k : ℝ) +
            sourceError (sourceOffset m : ℝ) (k : ℝ))) :
    ∀ n : ℕ, 68000 ≤ n →
      ∃ Q : Fin n → EuclideanSpace ℝ (Fin 458999),
        (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
        SeparatedConfiguration Q ∧
        (∀ a b, dist (Q a) (Q b) < (37/50 : ℝ)*(n:ℝ)^2) := by
  intro n hn
  obtain ⟨k, m, hk, hm, hmup, hsize, hsurplus, hkbound⟩ :=
    every_large_n_cluster_parameters n hn
  obtain ⟨P, hmin, hsep, hdiam⟩ := hsource m k hm hmup hk
  exact source_delete_pad_fixed_dimension hn hm hmup hk hsize hsurplus hkbound
    P hmin hsep hdiam

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Padding.lean
section

/-! All-size rounding, deletion, and dimension padding for the fifth pass.
The final theorem here is deliberately conditional on a finite configuration
source: no geometric existence assertion is hidden in this arithmetic layer. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

open Erdos488.Geometry.SeparatedDistances

/-- Exact integer padding at the new 36354 threshold. -/
theorem pass5_all_n_parameters (n : ℕ) (hn : 36354 ≤ n) :
    ∃ k m : ℕ, 2 ≤ k ∧ 18177 ≤ m ∧ m ≤ 27265 ∧
      n ≤ m*k ∧ m*k < n+k ∧ 18177*k ≤ n := by
  let k := n / 18177
  let r := n % 18177
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hk0 : 0 < k := by omega
  have hr : r < 18177 := Nat.mod_lt _ (by norm_num)
  have hnkr : 18177*k+r = n := Nat.div_add_mod n 18177
  have hsub : r+k-1+1 = r+k := by omega
  let q := (r+k-1)/k
  have hqUpper : q ≤ 9088 := by
    have hnum : r+k-1 < (9088+1)*k := by omega
    have := (Nat.div_lt_iff_lt_mul hk0).2 hnum
    change q < 9089 at this
    omega
  have hqmul : q*k ≤ r+k-1 := Nat.div_mul_le_self _ _
  have hnext : r+k-1 < (q+1)*k := by
    simpa [q, Nat.mul_comm] using Nat.lt_mul_div_succ (r+k-1) hk0
  refine ⟨k, 18177+q, hk, Nat.le_add_right _ _, by omega, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · omega

/-- The manuscript's rational rounded coefficient is below the final cap. -/
theorem pass5_rounded_coefficient :
    (24057/32768 : ℝ) * (18178/18177 : ℝ)^2 =
      220816318833/300740452352 ∧
    (24057/32768 : ℝ) * (18178/18177 : ℝ)^2 < 147/200 := by
  norm_num

theorem pass5_rounded_diameter_bound (n m k : ℕ) (hn : 36354 ≤ n)
    (hsurplus : m*k < n+k) (hkbound : 18177*k ≤ n) :
    (24057/32768 : ℝ) * ((m : ℝ)*k)^2 < (147/200 : ℝ)*(n : ℝ)^2 := by
  have hn' : (36354 : ℝ) ≤ n := by exact_mod_cast hn
  have hsize' : (m : ℝ)*(k : ℝ) < (n : ℝ)+(k : ℝ) := by
    exact_mod_cast hsurplus
  have hkbound' : (18177 : ℝ)*(k : ℝ) ≤ n := by exact_mod_cast hkbound
  have hratio : (m : ℝ)*(k : ℝ) < (18178/18177 : ℝ)*n := by linarith
  have hnonneg : 0 ≤ (m : ℝ)*(k : ℝ) := by positivity
  have hrnonneg : 0 ≤ (18178/18177 : ℝ)*n := by positivity
  have hsquare : ((m : ℝ)*(k : ℝ))^2 < ((18178/18177 : ℝ)*n)^2 := by
    nlinarith
  have htarget : (24057/32768 : ℝ)*((18178/18177 : ℝ)*n)^2 <
      (147/200 : ℝ)*(n : ℝ)^2 := by
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < n by linarith)]
  nlinarith

theorem pass5_dimension_bound {m : ℕ} (hm : m ≤ 27265) :
    3*m-1 ≤ 81794 := by omega

/-- Delete surplus points and pad coordinates, retaining all metric properties.
The input configuration and its properties remain explicit hypotheses. -/
theorem pass5_delete_pad {n m k : ℕ}
    (hn : 36354 ≤ n) (hmup : m ≤ 27265)
    (hsize : n ≤ m*k) (hsurplus : m*k < n+k) (hkbound : 18177*k ≤ n)
    (P : Fin m × Fin k → EuclideanSpace ℝ (Fin (3*m-1)))
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : SeparatedConfiguration P)
    (hdiam : ∀ a b, dist (P a) (P b) < (24057/32768 : ℝ)*((m : ℝ)*k)^2) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin 81794),
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      SeparatedConfiguration Q ∧
      (∀ a b, dist (Q a) (Q b) < (147/200 : ℝ)*(n : ℝ)^2) := by
  let f := sourceDeletionEmbedding hsize
  have hf : Function.Injective f := sourceDeletionEmbedding_injective hsize
  have hc : Fintype.card (Fin (3*m-1)) ≤ 81794 := by
    simpa using pass5_dimension_bound hmup
  let B : ℝ := (24057/32768 : ℝ)*((m : ℝ)*k)^2
  have hmin' := source_minimum_restrict P f hf hmin
  have hsep' := source_separated_restrict P f hf hsep
  have hdiam' := source_diameter_restrict P f B (fun a b => (hdiam a b).le)
  obtain ⟨hminQ, hsepQ, hdiamQ⟩ :=
    source_pad_properties hc (P ∘ f) hmin' hsep' B hdiam'
  refine ⟨sourcePadCoordinates hc ∘ P ∘ f, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hminQ
  · simpa only [Function.comp_assoc] using hsepQ
  · intro a b
    exact lt_of_le_of_lt (by simpa only [Function.comp_apply] using hdiamQ a b)
      (pass5_rounded_diameter_bound n m k hn hsurplus hkbound)

/-- Honest all-n endpoint interface. The geometric finite source must still be
supplied; this theorem proves all rounding, deletion, and coordinate padding. -/
theorem pass5_all_n_of_finite_sources
    (hsource : ∀ m k : ℕ, 18177 ≤ m → m ≤ 27265 → 2 ≤ k →
      ∃ P : Fin m × Fin k → EuclideanSpace ℝ (Fin (3*m-1)),
        (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
        SeparatedConfiguration P ∧
        (∀ a b, dist (P a) (P b) < (24057/32768 : ℝ)*((m : ℝ)*k)^2)) :
    ∀ n : ℕ, 36354 ≤ n →
      ∃ Q : Fin n → EuclideanSpace ℝ (Fin 81794),
        (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
        SeparatedConfiguration Q ∧
        (∀ a b, dist (Q a) (Q b) < (147/200 : ℝ)*(n : ℝ)^2) := by
  intro n hn
  obtain ⟨k, m, hk, hm, hmup, hsize, hsurplus, hkbound⟩ := pass5_all_n_parameters n hn
  obtain ⟨P, hmin, hsep, hdiam⟩ := hsource m k hm hmup hk
  exact pass5_delete_pad hn hmup hsize hsurplus hkbound P hmin hsep hdiam

end Erdos488.Geometry.SeparatedDistances.FixedDimension

end

-- From FiniteAssembly.lean
section

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

lemma localEdge_min (p k A i j : ℕ) (hk : 100 ≤ k) (hp : 0 < p)
    (hij : i < j) (hj : j < k) : 1 < localEdge p k A i j := by
  have hd : 0 < j-i := by omega
  have hdi : i+(j-i) < k := by omega
  obtain ⟨hl,hu⟩ := ruler_window_real p k A i (j-i) hp hd hdi
  exact localLength_min k p (j-i : ℕ) _ (by exact_mod_cast hk) (by exact_mod_cast hp)
    (by exact_mod_cast hd) hl hu

lemma localEdge_upper (p k A i j : ℕ) (hk : 100 ≤ k) (hp : 0 < p)
    (hij : i < j) (hj : j < k) : localEdge p k A i j < 18*(k : ℝ)^2 := by
  have hd : 0 < j-i := by omega
  have hdi : i+(j-i) < k := by omega
  obtain ⟨hl,hu⟩ := ruler_window_real p k A i (j-i) hp hd hdi
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  exact localLength_upper k p (j-i : ℕ) _ (by exact_mod_cast (show 0 < k by omega)) hp'
    (by positivity) (by exact_mod_cast (show j-i ≤ k by omega))
    ((by positivity : (0 : ℝ) ≤ (p : ℝ)*(j-i : ℕ)).trans hl) hu

theorem metric_properties {k p : ℕ} {E : Type*} [PseudoMetricSpace E]
    (hk : 100 ≤ k) (hp : p.Prime) (hsize : 6*k < p) (hpup : 100*p ≤ 606*k)
    (P : Fin 6 × Fin k → E)
    (hlocal : ∀ (A : Fin 6) (i j : Fin k), i < j →
      dist (P (A,i)) (P (A,j)) = localEdge p k A.val i.val j.val)
    (hcross : ∀ (A B : Fin 6), A < B → ∀ (i j : Fin k),
      dist (P (A,i)) (P (B,j)) = crossLength k A B i.val j.val) :
    (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
    (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*(6*(k : ℝ))^2) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hksq : 10000 ≤ (k : ℝ)^2 := by nlinarith
  have localMin (A : Fin 6) (i j : Fin k) (hij : i < j) : 1 ≤ dist (P (A,i)) (P (A,j)) := by
    rw [hlocal A i j hij]
    exact (localEdge_min p k A.val i.val j.val hk hp.pos hij j.isLt).le
  have crossMin (A B : Fin 6) (i j : Fin k) (hAB : A < B) : 1 ≤ dist (P (A,i)) (P (B,j)) := by
    rw [hcross A B hAB i j]
    have h := cross_lower k hk A B hAB i.val j.val i.isLt j.isLt
    nlinarith
  refine ⟨cluster_minimum_distance P localMin crossMin, ?_, ?_⟩
  · apply separatedConfiguration_of_cluster_gaps P
    · intro A i j B u v hij huv hne
      rw [hlocal A i j hij, hlocal B u v huv]
      apply (local_edges_separated p k A.val B.val i.val j.val u.val v.val hp hk hsize hpup
        A.isLt B.isLt hij huv j.isLt v.isLt ?_).le
      rintro ⟨hA,hi,hj⟩
      exact hne (Prod.ext (Fin.ext hA) (Prod.ext (Fin.ext hi) (Fin.ext hj)))
    · intro A B i j C D u v hAB hCD hne
      rw [hcross A B hAB i j, hcross C D hCD u v]
      exact cross_edges_separated k hk A B C D hAB hCD i j u v hne
    · intro A i j B C u v hij hBC
      rw [hlocal A i j hij, hcross B C hBC u v]
      have hl := localEdge_upper p k A.val i.val j.val hk hp.pos hij j.isLt
      have hc := cross_lower k hk B C hBC u.val v.val u.isLt v.isLt
      nlinarith
  · have localDiam (A : Fin 6) (i j : Fin k) (hij : i < j) :
        dist (P (A,i)) (P (A,j)) < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
      rw [hlocal A i j hij]
      have h := localEdge_upper p k A.val i.val j.val hk hp.pos hij j.isLt
      nlinarith
    have crossDiam (A B : Fin 6) (hAB : A < B) (i j : Fin k) :
        dist (P (A,i)) (P (B,j)) < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
      rw [hcross A B hAB i j]
      exact cross_upper k hk A B hAB i.val j.val i.isLt j.isLt
    rintro ⟨A,i⟩ ⟨B,j⟩
    rcases lt_trichotomy A B with hAB | hAB | hBA
    · exact crossDiam A B hAB i j
    · subst B
      rcases lt_trichotomy i j with hij | hij | hji
      · exact localDiam A i j hij
      · subst j
        rw [dist_self]
        positivity
      · rw [dist_comm]; exact localDiam A j i hji
    · rw [dist_comm]; exact crossDiam B A hBA j i


end Erdos670R29

end

-- From PrimeFirst.lean
section

namespace Erdos670R29

/-- Arbitrarily large cluster sizes have an admissible prime, using only Euclid's theorem. -/
theorem admissible_prime_sizes_unbounded (N : ℕ) :
    ∃ k p : ℕ, max 100 N ≤ k ∧ p.Prime ∧ 6*k < p ∧ 100*p ≤ 101*(6*k) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (6*(max 100 N)+1)
  refine ⟨(p-1)/6, p, ?_, hprime, ?_, ?_⟩ <;> omega


end Erdos670R29

end

-- From R29Endpoint.lean
section

namespace Erdos670R29
open scoped Matrix BigOperators
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

/-- Every admissible prime gives one actual separated configuration in R^29. -/
theorem finite_configuration (k p : ℕ) (hk : 100 ≤ k) (hp : p.Prime)
    (hsize : 6*k < p) (hpup : 100*p ≤ 606*k) :
    ∃ P : Fin (6*k) → EuclideanSpace ℝ (Fin 29),
      Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*((6*k : ℕ) : ℝ)^2) := by
  obtain ⟨Q,U,W,hQ,hproj,hfactor⟩ := finite_k_completion (k : ℝ) (by exact_mod_cast hk)
  let P₀ : Fin 6 × Fin k → EuclideanSpace ℝ (TwoCircleCoordinate (Fin 5) (Fin 6)) :=
    fun ai => pointFamily p Q U W ai.1 ai.2
  obtain ⟨hmin,hsep,hdiam⟩ := metric_properties hk hp hsize hpup P₀
    (fun A i j hij => pointFamily_local p Q U W hfactor A i j hij)
    (fun A B hAB i j => pointFamily_cross p Q U W hQ hproj hfactor A B hAB i j)
  have hc : Fintype.card (TwoCircleCoordinate (Fin 5) (Fin 6)) ≤ 29 := coordinate_card.le
  let P₁ := sourcePadCoordinates hc ∘ P₀
  obtain ⟨hmin₁,hsep₁,_⟩ := source_pad_properties hc P₀ hmin hsep
    ((499/500 : ℝ)*(6*(k : ℝ))^2) (fun a b => (hdiam a b).le)
  let f : Fin (6*k) → Fin 6 × Fin k := sourceDeletionEmbedding (le_refl (6*k))
  have hf : Function.Injective f := sourceDeletionEmbedding_injective _
  let P := P₁ ∘ f
  have hminP : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b) := source_minimum_restrict P₁ f hf hmin₁
  refine ⟨P,injective_of_unit_minimum_distance P hminP,hminP,
    source_separated_restrict P₁ f hf hsep₁,?_⟩
  intro a b
  dsimp [P,P₁]
  rw [sourcePadCoordinates_dist]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hdiam (f a) (f b)

lemma finite_range_diam_lt {ι E : Type*} [Fintype ι] [Nonempty ι] [PseudoMetricSpace E]
    (P : ι → E) (C : ℝ) (h : ∀ a b, dist (P a) (P b) < C) :
    Metric.diam (Set.range P) < C := by
  let s : Finset (ι × ι) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  let B := s.sup' hs (fun ab => dist (P ab.1) (P ab.2))
  have hB (a b : ι) : dist (P a) (P b) ≤ B :=
    Finset.le_sup' (s := s) (f := fun ab => dist (P ab.1) (P ab.2)) (Finset.mem_univ (a,b))
  have hBpos : 0 ≤ B := by
    let a : ι := Classical.choice inferInstance
    exact (dist_nonneg : 0 ≤ dist (P a) (P a)).trans (hB a a)
  have hBlt : B < C := by
    apply (Finset.sup'_lt_iff (s := s) hs).2
    intro ab _
    exact h ab.1 ab.2
  apply lt_of_le_of_lt ?_ hBlt
  apply Metric.diam_le_of_forall_dist_le hBpos
  intro x hx y hy
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact hB a b

/-- Prime-first endpoint: arbitrarily large finite configurations in the same R^29,
with unit minimum distance, separated unordered-edge lengths and diameter < .998 n². -/
theorem r29_unbounded_counterexamples (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 600 ≤ n ∧
    ∃ P : Fin n → EuclideanSpace ℝ (Fin 29), Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*(n : ℝ)^2) ∧
      Metric.diam (Set.range P) < (499/500 : ℝ)*(n : ℝ)^2 := by
  obtain ⟨k,p,hk,hp,hsize,hpup⟩ := admissible_prime_sizes_unbounded N
  have hk100 : 100 ≤ k := (le_max_left 100 N).trans hk
  have hkN : N ≤ k := (le_max_right 100 N).trans hk
  obtain ⟨P,hinj,hmin,hsep,hdiam⟩ := finite_configuration k p hk100 hp hsize (by omega)
  haveI : Nonempty (Fin (6*k)) := ⟨⟨0,by omega⟩⟩
  exact ⟨6*k,by omega,by omega,P,hinj,hmin,hsep,hdiam,finite_range_diam_lt P _ hdiam⟩



end Erdos670R29

end

-- From Solution.lean
section

/-!
Proofs of the two `Challenge` statements from the dimension-29 endpoint
`Erdos670R29.r29_unbounded_counterexamples`.
-/


open Filter Erdos488.Geometry.SeparatedDistances

namespace Erdos670

theorem r29_sets_600 (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 600 ≤ n ∧
    ∃ A : Finset (EuclideanSpace ℝ (Fin 29)), A.card = n ∧
      Erdos670.HasSeparatedDistances A ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 29))) < (499/500 : ℝ) * (n : ℝ)^2 := by
  classical
  obtain ⟨n,hN,hn,P,hinj,_,hsep,_,hdiam⟩ := Erdos670R29.r29_unbounded_counterexamples N
  refine ⟨n,hN,hn,Finset.univ.image P,?_,?_,?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ hinj
  · intro a ha b hb c hc e he hab hce hpairs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp he
    have hij : i ≠ j := fun h => hab (congrArg P h)
    have hkl : k ≠ l := fun h => hce (congrArg P h)
    let u : Edge (Fin n) := ⟨s(i,j), by simpa only [Sym2.mk_isDiag_iff] using hij⟩
    let v : Edge (Fin n) := ⟨s(k,l), by simpa only [Sym2.mk_isDiag_iff] using hkl⟩
    have huv : u ≠ v := by
      intro h
      have huv' : s(i,j) = s(k,l) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp huv' with ⟨hik,hjl⟩ | ⟨hil,hjk⟩
      · apply hpairs
        rw [hik,hjl]
      · apply hpairs
        rw [hil,hjk]
        exact Sym2.eq_swap
    simpa only [u,v,edgeDistance,Sym2.lift_mk] using hsep u v huv
  · have heq : (Finset.univ.image P : Set (EuclideanSpace ℝ (Fin 29))) = Set.range P := by
      ext x
      simp only [Finset.mem_coe,Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range]
    rw [heq]
    exact hdiam

theorem r29_refutation :
    ¬ (∀ d : ℕ, 1 ≤ d → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → Erdos670.HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d)))) := by
  intro h
  have hevent := h 29 (by norm_num) (1/1000) (by norm_num)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨n,hn,hn600,A,hcard,hsep,hdiam⟩ := r29_sets_600 N
  have hlower := hN n hn A hcard hsep
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2pos : 0 < (n : ℝ)^2 := sq_pos_of_pos hnpos
  norm_num at hlower
  nlinarith

end Erdos670

end

theorem OMA.disproof : ¬ (type_of% @Erdos670.erdos_670) :=
  Erdos670.r29_refutation
