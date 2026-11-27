import FormalConjectures.GreensOpenProblems.«31»
import Mathlib

/-!
Improved upper bound for Ben Green Open Problem 31 (Sidon sets in [1, N]):
  F(N) <= N^(1/2) + (9434 / 10000) * N^(1/4)   for all sufficiently large N,
improving the 0.94349 coefficient of Hou and Zhao (arXiv:2607.01169).

Method and attribution:
We formalize the vector-valued smoothing method of Hou and Zhao (arXiv:2607.01169, Theorem 2.1)
from scratch in elementary finite-sum arithmetic, and supply an original 13-component centered
uniform kernel-boundary certificate (m = 38, L = 3, widths 12, 14, ..., 36, boundary denominator
D_w = 50000, weight denominator S_lam = 10012) achieving:
  a = 6821 / 5006,
  b = 77650136087411 / 118892500000000 > 0,
  sqrt(a * b) = 0.94334919... < 9434 / 10000 = 0.9434 < 0.94349.

Proof outline (100% self-contained, no MeasureTheory, no native_decide):
1. Pure-Nat kernel verification (`decide +kernel`) of all 114 finite covering inequalities
   and the exact boundary L2 sum phiNum = 2688450544349644.
2. Step-function convolution kernels K_r of support H = 38 * h (symmetric, unit mass, explicit L2),
   giving the Sidon energy upper bound sum_r lam_r * ||u_r||_2^2 <= 1 + a * k / H.
3. Reflected boundary weights Q_r on [0, N + H - 1) satisfying exact L2 identity
   sum_r lam_r * ||Q_r||_2^2 = N + b * H - 1 and pointwise covering sum_r lam_r (K_r * Q_r)(x) >= 1.
4. Direct finite Cauchy-Schwarz on Fin 13 x Finset.range (N + H - 1) giving
   k^2 <= (N + b * H) * (1 + a * k / H), and asymptotic choice h = floor(1444/1000 * N^(3/4) / 38)
   yielding k <= N^(1/2) + (9434 / 10000) * N^(1/4) for all N >= 10^24.
-/

namespace OMA.Green31Upper

open Filter

-- ============================================================================
-- Section 1: Exact 13-kernel centered-uniform certificate (m = 38, L = 3)
-- ============================================================================

private def wsList : List ℕ := [12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36]
private def csList : List ℕ := [15, 8, 11, 14, 17, 21, 23, 30, 34, 38, 42, 47, 59]

private def row0 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80946, 80948, 85176, 85178, 89404, 89406, 93628, 93631, 97846, 97849, 102060, 102063, 28933, 28934, 30759, 30760, 32997],
  [32997, 35594, 35595, 38512, 38513, 41854, 41855, 41915, 41916, 44300, 44300, 46740, 46741, 49279, 49280, 51952, 51953, 54739, 54741, 58281, 58283, 56928, 56930, 55275, 55278, 53355, 53358, 51197, 51199, 48741],
  [48742, 45520, 45521, 46516, 46515, 47458, 47456, 48308, 48306, 49030, 49029, 49589, 49588, 49888, 49888, 50347, 50348, 50697, 50700, 50933, 50936, 51041, 51046, 51008, 51015, 50823, 50833, 50402, 50415, 50036],
  [50047, 49734, 49734, 49509, 49499, 49382, 49369, 49383, 49367, 49582, 49562, 49744, 49724, 49896, 49896, 50041, 50050, 50156, 50165, 50230, 50239, 50287, 50297, 50299]
]
private def row1 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69382, 69384, 73008, 73010, 76632, 76634, 80253, 80255, 83868, 83870, 87480, 87483, 94182, 94185, 29990, 29991, 31907, 31908],
  [34130, 34131, 36625, 36626, 39487, 39488, 42629, 42630, 43161, 43162, 45605, 45606, 48087, 48088, 50646, 50647, 53396, 53398, 56710, 56712, 56029, 56031, 55012, 55015, 53757, 53760, 52290, 52292, 50644, 50646],
  [48808, 48809, 45944, 45944, 46896, 46895, 47785, 47784, 48583, 48582, 49266, 49265, 49791, 49791, 50081, 50082, 50480, 50482, 50763, 50766, 50926, 50930, 50961, 50967, 50849, 50858, 50522, 50533, 50213, 50224],
  [49937, 49938, 49706, 49698, 49539, 49530, 49457, 49446, 49458, 49444, 49649, 49632, 49817, 49808, 49969, 49969, 50093, 50101, 50184, 50192, 50233, 50241, 50264, 50297]
]
private def row2 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60710, 60711, 63882, 63884, 67053, 67055, 70221, 70223, 73385, 73387, 76545, 76547, 82409, 82412, 86951, 86953, 31091, 31092, 33035],
  [33036, 35216, 35217, 37714, 37715, 40461, 40462, 43630, 43631, 44446, 44446, 46925, 46926, 49432, 49433, 52073, 52075, 55289, 55290, 54936, 54938, 54465, 54468, 53717, 53720, 52775, 52777, 51670, 51671, 50465],
  [50466, 48768, 48768, 46348, 46348, 47252, 47251, 48091, 48090, 48845, 48844, 49483, 49483, 49973, 49973, 50231, 50232, 50564, 50567, 50778, 50782, 50870, 50876, 50828, 50836, 50582, 50593, 50341, 50351, 50105],
  [50107, 49887, 49881, 49707, 49700, 49585, 49577, 49513, 49503, 49532, 49520, 49725, 49717, 49891, 49883, 50023, 50023, 50125, 50132, 50192, 50199, 50219, 50248, 50260]
]
private def row3 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53964, 53966, 56784, 56785, 59603, 59604, 62419, 62421, 65231, 65233, 68040, 68042, 73253, 73255, 77290, 77292, 81600, 81602, 32184, 32185],
  [34122, 34122, 36340, 36341, 38778, 38778, 41592, 41593, 44720, 44721, 45748, 45749, 48250, 48251, 50835, 50837, 53902, 53904, 53869, 53871, 53667, 53670, 53375, 53377, 52848, 52850, 52170, 52171, 51396, 51398],
  [50245, 50246, 48813, 48813, 46725, 46725, 47583, 47583, 48379, 48378, 49085, 49085, 49679, 49678, 50117, 50118, 50334, 50336, 50600, 50603, 50745, 50750, 50762, 50769, 50593, 50602, 50415, 50424, 50231, 50233],
  [50042, 50037, 49868, 49863, 49729, 49723, 49620, 49613, 49573, 49564, 49613, 49608, 49801, 49794, 49948, 49941, 50060, 50060, 50139, 50145, 50184, 50210, 50220, 50241]
]
private def row4 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 48568, 48569, 51106, 51107, 53642, 53644, 56177, 56179, 58708, 58709, 61236, 61238, 65928, 65929, 69561, 69562, 73440, 73442, 77533, 77535, 33247],
  [33248, 35243, 35244, 37435, 37435, 39963, 39964, 42776, 42777, 45865, 45866, 47058, 47059, 49632, 49633, 52605, 52607, 52764, 52766, 52834, 52837, 52765, 52768, 52627, 52629, 52296, 52298, 51874, 51875, 51106],
  [51106, 50138, 50139, 48906, 48907, 47076, 47076, 47893, 47893, 48642, 48641, 49301, 49300, 49838, 49839, 50221, 50223, 50389, 50391, 50588, 50592, 50660, 50667, 50557, 50566, 50442, 50450, 50309, 50310, 50162],
  [50158, 50009, 50005, 49872, 49867, 49747, 49741, 49664, 49657, 49641, 49639, 49693, 49688, 49862, 49855, 49989, 49982, 50079, 50079, 50137, 50161, 50189, 50208, 50204]
]
private def row5 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 44153, 44154, 46460, 46461, 48766, 48767, 51070, 51072, 53371, 53372, 55669, 55671, 59934, 59936, 63237, 63239, 66764, 66766, 70485, 70487, 74377, 74379],
  [34346, 34347, 36338, 36339, 38635, 38635, 41188, 41189, 43994, 43995, 47045, 47046, 48422, 48424, 51350, 51352, 51688, 51690, 51923, 51925, 52090, 52092, 52141, 52143, 52145, 52147, 52016, 52017, 51566, 51567],
  [50930, 50931, 50102, 50103, 49027, 49028, 47404, 47404, 48176, 48176, 48878, 48877, 49480, 49481, 49958, 49960, 50282, 50284, 50397, 50401, 50525, 50531, 50483, 50491, 50423, 50431, 50342, 50344, 50238, 50235],
  [50121, 50118, 50000, 49996, 49875, 49871, 49775, 49770, 49718, 49717, 49711, 49709, 49757, 49753, 49906, 49900, 50012, 50007, 50083, 50099, 50146, 50163, 50177, 50200]
]
private def row6 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 0, 40473, 40474, 42588, 42589, 44702, 44703, 46814, 46816, 48923, 48925, 51030, 51032, 54940, 54941, 57967, 57969, 61200, 61202, 64611, 64613, 68179, 68181, 71957],
  [71959, 35424, 35425, 37529, 37530, 39868, 39869, 42437, 42437, 45232, 45233, 48297, 48298, 50098, 50100, 50614, 50615, 51007, 51009, 51317, 51319, 51574, 51576, 51740, 51742, 51901, 51902, 51722, 51723, 51367],
  [51367, 50831, 50832, 50114, 50114, 49165, 49165, 47704, 47704, 48432, 48431, 49078, 49078, 49620, 49621, 50036, 50037, 50298, 50302, 50355, 50361, 50374, 50381, 50367, 50374, 50333, 50335, 50275, 50272, 50195],
  [50192, 50103, 50100, 49992, 49989, 49890, 49886, 49815, 49815, 49775, 49774, 49769, 49767, 49807, 49803, 49935, 49929, 50021, 50031, 50095, 50106, 50139, 50159, 50160]
]
private def row7 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 0, 37360, 37361, 39312, 39313, 41264, 41265, 43213, 43215, 45160, 45161, 47105, 47106, 50714, 50715, 53508, 53510, 56493, 56494, 59641, 59643, 62934, 62936, 66422, 66424],
  [70059, 70061, 36595, 36595, 38753, 38754, 41122, 41123, 43699, 43700, 46527, 46528, 49853, 49855, 49515, 49517, 50068, 50070, 50518, 50520, 50900, 50902, 51248, 51249, 51546, 51547, 51638, 51639, 51526, 51527],
  [51242, 51243, 50785, 50786, 50157, 50158, 49306, 49307, 47976, 47977, 48650, 48651, 49238, 49239, 49717, 49719, 50070, 50073, 50267, 50272, 50229, 50236, 50275, 50281, 50288, 50290, 50272, 50269, 50232, 50229],
  [50173, 50170, 50088, 50085, 49997, 49994, 49918, 49919, 49861, 49861, 49824, 49823, 49814, 49812, 49841, 49837, 49949, 49958, 50038, 50043, 50093, 50107, 50126, 50150]
]
private def row8 : List (List ℕ) := [
  [0, 0, 0, 0, 0, 34691, 34692, 36504, 36505, 38316, 38317, 40127, 40128, 41934, 41935, 43740, 43742, 47091, 47093, 49686, 49688, 52457, 52459, 55381, 55382, 58439, 58441, 61678, 61679, 65055],
  [65056, 68672, 68673, 37797, 37798, 39997, 39998, 42388, 42389, 45011, 45012, 48099, 48100, 49329, 49331, 49087, 49089, 49681, 49683, 50188, 50190, 50645, 50647, 51102, 51103, 51327, 51328, 51462, 51463, 51399],
  [51399, 51170, 51171, 50778, 50779, 50218, 50218, 49445, 49445, 48212, 48213, 48829, 48830, 49355, 49357, 49772, 49774, 50057, 50062, 50156, 50162, 50147, 50153, 50209, 50210, 50234, 50232, 50232, 50230, 50209],
  [50206, 50154, 50151, 50085, 50083, 50015, 50016, 49953, 49954, 49899, 49899, 49861, 49861, 49845, 49843, 49861, 49870, 49969, 49974, 50039, 50048, 50084, 50102, 50109]
]
private def row9 : List (List ℕ) := [
  [0, 0, 0, 0, 32379, 32380, 34071, 34071, 35762, 35763, 37452, 37453, 39139, 39140, 40824, 40826, 43952, 43953, 46374, 46375, 48960, 48962, 51689, 51690, 54543, 54545, 57566, 57567, 60718, 60719],
  [64094, 64095, 67656, 67658, 39022, 39023, 41254, 41255, 43700, 43701, 46579, 46580, 47726, 47728, 48942, 48944, 48791, 48793, 49429, 49430, 49998, 49999, 50550, 50551, 50928, 50929, 51184, 51184, 51348, 51349],
  [51321, 51322, 51137, 51138, 50793, 50794, 50286, 50287, 49567, 49568, 48408, 48410, 48966, 48968, 49430, 49433, 49780, 49784, 49968, 49973, 50085, 50090, 50094, 50095, 50164, 50161, 50200, 50198, 50211, 50208],
  [50189, 50186, 50147, 50144, 50097, 50098, 50041, 50042, 49983, 49984, 49930, 49930, 49887, 49887, 49863, 49874, 49886, 49892, 49975, 49984, 50035, 50048, 50071, 50095]
]
private def row10 : List (List ℕ) := [
  [0, 0, 0, 30355, 30356, 31941, 31942, 33527, 33528, 35111, 35112, 36693, 36694, 38273, 38274, 41205, 41206, 43476, 43477, 45900, 45901, 48458, 48460, 51134, 51136, 53968, 53969, 56923, 56924, 60088],
  [60089, 63427, 63429, 66938, 66940, 40261, 40262, 42554, 42555, 45252, 45253, 46325, 46326, 47463, 47465, 48674, 48675, 48610, 48612, 49297, 49299, 49948, 49950, 50421, 50422, 50818, 50819, 51094, 51095, 51278],
  [51279, 51281, 51282, 51129, 51130, 50821, 50822, 50348, 50349, 49666, 49668, 48563, 48565, 49061, 49063, 49460, 49463, 49714, 49718, 49912, 49917, 50039, 50040, 50059, 50057, 50136, 50134, 50182, 50179, 50192],
  [50189, 50180, 50178, 50154, 50155, 50116, 50117, 50064, 50065, 50006, 50007, 49950, 49950, 49902, 49912, 49886, 49893, 49897, 49906, 49975, 49987, 50025, 50045, 50051]
]
private def row11 : List (List ℕ) := [
  [0, 0, 28570, 28570, 30062, 30063, 31555, 31555, 33046, 33047, 34534, 34535, 36022, 36023, 38781, 38782, 40918, 40919, 43200, 43201, 45608, 45609, 48126, 48128, 50793, 50795, 53575, 53576, 56553, 56555],
  [59696, 59698, 63001, 63002, 66462, 66464, 41544, 41545, 44083, 44084, 45091, 45092, 46160, 46162, 47298, 47299, 48510, 48512, 48535, 48536, 49292, 49294, 49863, 49863, 50347, 50348, 50755, 50756, 51043, 51044],
  [51243, 51244, 51265, 51266, 51136, 51137, 50848, 50849, 50395, 50397, 49738, 49740, 48676, 48678, 49110, 49114, 49416, 49420, 49676, 49681, 49879, 49880, 50009, 50007, 50039, 50037, 50122, 50120, 50165, 50163],
  [50183, 50181, 50185, 50186, 50169, 50170, 50133, 50134, 50081, 50082, 50021, 50021, 49960, 49970, 49921, 49929, 49897, 49906, 49901, 49914, 49970, 49988, 50009, 50030]
]
private def row12 : List (List ℕ) := [
  [0, 26982, 26983, 28392, 28393, 29802, 29802, 31210, 31211, 32616, 32617, 34020, 34021, 36627, 36628, 38645, 38646, 40800, 40801, 43074, 43075, 45453, 45454, 47972, 47973, 50598, 50600, 53411, 53413, 56380],
  [56381, 59501, 59502, 62770, 62771, 66218, 66220, 43043, 43045, 43995, 43997, 45004, 45005, 46076, 46078, 47220, 47221, 48445, 48446, 48572, 48573, 49248, 49249, 49824, 49825, 50314, 50315, 50726, 50727, 51023],
  [51024, 51230, 51231, 51264, 51264, 51143, 51145, 50865, 50867, 50423, 50425, 49779, 49782, 48744, 48747, 49088, 49093, 49397, 49401, 49658, 49659, 49860, 49858, 49993, 49991, 50031, 50029, 50110, 50108, 50159],
  [50157, 50187, 50189, 50197, 50198, 50182, 50183, 50145, 50146, 50090, 50091, 50026, 50037, 49975, 49982, 49929, 49939, 49901, 49914, 49900, 49918, 49958, 49977, 50000]
]

private def getRow (r : ℕ) : List (List ℕ) :=
  match r with
  | 0 => row0
  | 1 => row1
  | 2 => row2
  | 3 => row3
  | 4 => row4
  | 5 => row5
  | 6 => row6
  | 7 => row7
  | 8 => row8
  | 9 => row9
  | 10 => row10
  | 11 => row11
  | 12 => row12
  | _ => []

private def extRow (r : ℕ) : List ℕ :=
  (getRow r).flatten ++ List.replicate 38 50000

private def wNat (r j : ℕ) : ℕ :=
  if j < 114 then ((getRow r).flatten).getD j 0 else 50000

private def wWidth (r : Fin 13) : ℕ := wsList.getD r.val 0
private def cNat (r : Fin 13) : ℕ := csList.getD r.val 0
private def offNat (r : Fin 13) : ℕ := (38 - wWidth r) / 2

private def windowSumsGo : List ℕ → List ℕ → ℕ → ℕ → List ℕ → List ℕ
  | _, _, _, 0, acc => acc.reverse
  | lead, trail, cur, rem + 1, acc =>
    match lead, trail with
    | a :: ls, b :: ts => windowSumsGo ls ts (cur + a - b) rem (cur :: acc)
    | _, _ => (cur :: acc).reverse

private def windowSumsFrom (xs : List ℕ) (W : ℕ) : List ℕ :=
  let init := (xs.take W).sum
  windowSumsGo (xs.drop W) xs init 114 []

private def addScaled (c : ℕ) (acc ws : List ℕ) : List ℕ :=
  List.zipWith (fun a b => a + c * b) acc ws

private def covPrefix : ℕ → List ℕ
  | 0 => List.replicate 114 0
  | k + 1 =>
    let W := wsList.getD k 0
    let off := (38 - W) / 2
    let c := csList.getD k 0
    addScaled c (covPrefix k) (windowSumsFrom ((extRow k).drop off) W)

private def checkCov : Bool := (covPrefix 13).all (fun v => 10012 * 50000 ≤ v)

private def sumSqList : List ℕ → ℕ
  | [] => 0
  | v :: vs => v * v + sumSqList vs

private def phiPrefix : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    phiPrefix k + csList.getD k 0 * wsList.getD k 0 * sumSqList (getRow k).flatten

private theorem hRowLen_all :
    (List.range 13).all (fun r => (getRow r).flatten.length == 114) = true := by
  decide +kernel

private theorem hRowLen (r : ℕ) (hr : r < 13) : (getRow r).flatten.length = 114 := by
  have hmem : r ∈ List.range 13 := List.mem_range.mpr hr
  have := List.all_eq_true.mp hRowLen_all r hmem
  simpa using this

private theorem hCov_bool : checkCov = true := by decide +kernel

private theorem hPhi_val : phiPrefix 13 = 2688450544349644 := by decide +kernel

private theorem hWidths (r : Fin 13) :
    0 < wWidth r ∧ 2 * offNat r + wWidth r = 38 := by
  fin_cases r <;> decide

private theorem hSlam_nat : ∑ r : Fin 13, cNat r * wWidth r = 10012 := by
  decide

private theorem hSumC_nat : ∑ r : Fin 13, cNat r = 359 := by
  decide

-- Bridge lemmas from List operations to Finset sums

private lemma list_getD_eq_getElem (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs.getD i 0 = xs[i] := by
  simp [List.getD, List.getElem?_eq_getElem hi]

private lemma extRow_length (r : ℕ) (hr : r < 13) : (extRow r).length = 152 := by
  simp [extRow, hRowLen r hr]

private lemma extRow_getD (r : ℕ) (hr : r < 13) (j : ℕ) (hj : j < 152) :
    (extRow r).getD j 0 = wNat r j := by
  have hlen : (getRow r).flatten.length = 114 := hRowLen r hr
  unfold extRow wNat
  rw [List.getD_eq_getElem?_getD]
  by_cases h114 : j < 114
  · rw [if_pos h114, List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD]
  · rw [if_neg h114, List.getElem?_append_right (by omega), hlen,
      List.getElem?_replicate]
    simp [show j - 114 < 38 by omega]

private lemma take_sum_eq_finset_sum (ys : List ℕ) :
    ∀ W ≤ ys.length, (ys.take W).sum = ∑ i ∈ Finset.range W, ys.getD i 0 := by
  intro W
  induction W with
  | zero => intro _; simp
  | succ W ih =>
    intro hW
    rw [List.take_succ_eq_append_getElem (by omega), List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, ih (by omega), list_getD_eq_getElem ys W (by omega)]

private lemma windowSumsGo_spec (W : ℕ) (_hW : 1 ≤ W) :
    ∀ (rem : ℕ) (trail acc : List ℕ),
      rem + W ≤ trail.length →
      (windowSumsGo (trail.drop W) trail (trail.take W).sum rem acc).length = acc.length + rem ∧
      (∀ k < acc.length,
        (windowSumsGo (trail.drop W) trail (trail.take W).sum rem acc).getD k 0 =
          acc.reverse.getD k 0) ∧
      (∀ k < rem,
        (windowSumsGo (trail.drop W) trail (trail.take W).sum rem acc).getD (acc.length + k) 0 =
          ((trail.drop k).take W).sum) := by
  intro rem
  induction rem with
  | zero =>
    intro trail acc _
    exact ⟨by simp [windowSumsGo], fun k _ => by simp [windowSumsGo], fun k hk => by omega⟩
  | succ rem ih =>
    intro trail acc hlen
    cases trail with
    | nil => simp at hlen
    | cons b ts =>
      have hWlt : W ≤ ts.length := by simp at hlen; omega
      have hdrop_ne : (b :: ts).drop W ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        omega
      obtain ⟨a, ls, hdrop⟩ : ∃ a ls, (b :: ts).drop W = a :: ls :=
        List.exists_cons_of_ne_nil hdrop_ne
      have ha_eq : a = (b :: ts)[W]'(by simp; omega) := by
        have h0 := congrArg (fun l => l[0]?) hdrop
        simp only [List.getElem?_drop, add_zero, List.getElem?_cons_zero] at h0
        rw [List.getElem?_eq_getElem (by simp; omega)] at h0
        exact (Option.some.inj h0).symm
      have hls_eq : ls = ts.drop W := by
        have ht := congrArg List.tail hdrop
        simp only [List.tail_cons] at ht
        rw [← ht]
        calc List.tail ((b :: ts).drop W)
            = ((b :: ts).drop W).drop 1 := List.drop_one.symm
          _ = (b :: ts).drop (W + 1) := by rw [List.drop_drop]
          _ = ts.drop W := rfl
      have hcur_step : ((b :: ts).take W).sum + a - b = (ts.take W).sum := by
        have h1 : (b :: ts).take (W + 1) = (b :: ts).take W ++ [a] := by
          rw [ha_eq]
          exact List.take_succ_eq_append_getElem (by simp; omega)
        have h2 : (b :: ts).take (W + 1) = b :: ts.take W := rfl
        have hsum := congrArg List.sum (h1.symm.trans h2)
        simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hsum
        omega
      have hgo : windowSumsGo ((b :: ts).drop W) (b :: ts) ((b :: ts).take W).sum (rem + 1) acc =
          windowSumsGo (ts.drop W) ts (ts.take W).sum rem (((b :: ts).take W).sum :: acc) := by
        conv_lhs => unfold windowSumsGo
        rw [hdrop]
        dsimp only
        rw [hls_eq, hcur_step]
      rw [hgo]
      obtain ⟨ih_len, ih_acc, ih_rem⟩ := ih ts (((b :: ts).take W).sum :: acc) (by simp at hlen; omega)
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih_len, ?_, ?_⟩
      · intro k hk
        have h1 := ih_acc k (by simp; omega)
        rw [h1, List.reverse_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp; omega)]
      · intro k hk
        cases k with
        | zero =>
          have h1 := ih_acc acc.length (by simp)
          rw [add_zero, h1, List.reverse_cons, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by simp)]
          simp
        | succ k' =>
          have hidx : acc.length + (k' + 1) = (((b :: ts).take W).sum :: acc).length + k' := by
            simp; omega
          rw [hidx, ih_rem k' (by omega)]
          rfl

private lemma windowSumsFrom_spec (r : ℕ) (hr : r < 13) :
    let W := wsList.getD r 0
    let off := (38 - W) / 2
    (windowSumsFrom ((extRow r).drop off) W).length = 114 ∧
    ∀ q < 114,
      (windowSumsFrom ((extRow r).drop off) W).getD q 0 =
        ∑ i ∈ Finset.range W, wNat r (q + off + i) := by
  have hWspec := hWidths ⟨r, hr⟩
  dsimp only [wWidth, offNat] at hWspec
  set W := wsList.getD r 0
  set off := (38 - W) / 2
  have hWpos : 1 ≤ W := hWspec.1
  have hdrop_len : ((extRow r).drop off).length = 152 - off := by
    rw [List.length_drop, extRow_length r hr]
  have hlen_ok : 114 + W ≤ ((extRow r).drop off).length := by omega
  obtain ⟨hlen, _, hget⟩ := windowSumsGo_spec W hWpos 114 ((extRow r).drop off) [] hlen_ok
  refine ⟨by simpa [windowSumsFrom] using hlen, ?_⟩
  intro q hq
  have h1 := hget q hq
  simp only [List.length_nil, zero_add] at h1
  change (windowSumsGo (((extRow r).drop off).drop W) ((extRow r).drop off)
      (((extRow r).drop off).take W).sum 114 []).getD q 0 = _
  rw [h1, List.drop_drop, take_sum_eq_finset_sum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
      extRow_getD r hr (off + q + i) (by omega)]
    congr 1; omega
  · rw [List.length_drop, extRow_length r hr]; omega

private lemma covPrefix_spec :
    ∀ k ≤ 13, (covPrefix k).length = 114 ∧
      ∀ q < 114, (covPrefix k).getD q 0 =
        ∑ r ∈ Finset.range k,
          csList.getD r 0 * ∑ i ∈ Finset.range (wsList.getD r 0),
            wNat r (q + (38 - wsList.getD r 0) / 2 + i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [covPrefix], ?_⟩
    intro q hq
    rw [covPrefix, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hq,
      Option.getD_some, Finset.sum_range_zero]
  | succ k ih =>
    intro hk
    obtain ⟨ih_len, ih_get⟩ := ih (by omega)
    obtain ⟨hw_len, hw_get⟩ := windowSumsFrom_spec k (by omega)
    set wL := windowSumsFrom ((extRow k).drop ((38 - wsList.getD k 0) / 2)) (wsList.getD k 0)
    refine ⟨?_, ?_⟩
    · change (addScaled (csList.getD k 0) (covPrefix k) wL).length = 114
      simp only [addScaled, List.length_zipWith, ih_len, hw_len, min_self]
    · intro q hq
      change (addScaled (csList.getD k 0) (covPrefix k) wL).getD q 0 = _
      unfold addScaled
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
      have h1 : (covPrefix k)[q]? = some ((covPrefix k).getD q 0) := by
        rw [List.getElem?_eq_getElem (by omega), list_getD_eq_getElem (covPrefix k) q (by omega)]
      have h2 : wL[q]? = some (wL.getD q 0) := by
        rw [List.getElem?_eq_getElem (by omega), list_getD_eq_getElem wL q (by omega)]
      rw [h1, h2]
      dsimp only [Option.map₂, Option.getD]
      rw [ih_get q hq, hw_get q hq, Finset.sum_range_succ]

private theorem hCov_nat (q : ℕ) (hq : q < 114) :
    10012 * 50000 ≤
      ∑ r : Fin 13, cNat r * ∑ i ∈ Finset.range (wWidth r), wNat r.val (q + offNat r + i) := by
  obtain ⟨hlen, hget⟩ := covPrefix_spec 13 le_rfl
  have hmem : (covPrefix 13)[q]'(by omega) ∈ covPrefix 13 := List.getElem_mem (by omega)
  have hval := List.all_eq_true.mp hCov_bool _ hmem
  have hle : 10012 * 50000 ≤ (covPrefix 13).getD q 0 := by
    rw [list_getD_eq_getElem (covPrefix 13) q (by omega)]
    simpa using hval
  rw [hget q hq] at hle
  have hfin : ∑ r : Fin 13, cNat r * ∑ i ∈ Finset.range (wWidth r), wNat r.val (q + offNat r + i) =
      ∑ r ∈ Finset.range 13,
        csList.getD r 0 * ∑ i ∈ Finset.range (wsList.getD r 0),
          wNat r (q + (38 - wsList.getD r 0) / 2 + i) := by
    exact Fin.sum_univ_eq_sum_range (fun r =>
      csList.getD r 0 * ∑ i ∈ Finset.range (wsList.getD r 0),
        wNat r (q + (38 - wsList.getD r 0) / 2 + i)) 13
  rw [hfin]
  exact hle

private lemma sumSqList_eq (xs : List ℕ) :
    sumSqList xs = ∑ j ∈ Finset.range xs.length, (xs.getD j 0) ^ 2 := by
  induction xs with
  | nil => simp [sumSqList]
  | cons v vs ih =>
    rw [sumSqList, List.length_cons, Finset.sum_range_succ', ih, add_comm]
    congr 1
    simp [List.getD, sq]

private lemma sumSqList_row (k : ℕ) (hk : k < 13) :
    sumSqList (getRow k).flatten = ∑ j ∈ Finset.range 114, (wNat k j) ^ 2 := by
  rw [sumSqList_eq, hRowLen k hk]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < 114 := Finset.mem_range.mp hj
  rw [wNat, if_pos hj']

private lemma phiPrefix_spec :
    ∀ k ≤ 13, phiPrefix k =
      ∑ r ∈ Finset.range k,
        csList.getD r 0 * wsList.getD r 0 * ∑ j ∈ Finset.range 114, (wNat r j) ^ 2 := by
  intro k
  induction k with
  | zero => intro _; simp [phiPrefix]
  | succ k ih =>
    intro hk
    rw [phiPrefix, ih (by omega), Finset.sum_range_succ, sumSqList_row k (by omega)]

private theorem hPhi_nat :
    ∑ r : Fin 13, cNat r * wWidth r * ∑ j ∈ Finset.range 114, (wNat r.val j) ^ 2 =
      2688450544349644 := by
  have h1 : ∑ r ∈ Finset.range 13,
      csList.getD r 0 * wsList.getD r 0 * ∑ j ∈ Finset.range 114, (wNat r j) ^ 2 = 2688450544349644 :=
    (phiPrefix_spec 13 le_rfl).symm.trans hPhi_val
  have h2 : ∑ r : Fin 13, cNat r * wWidth r * ∑ j ∈ Finset.range 114, (wNat r.val j) ^ 2 =
      ∑ r ∈ Finset.range 13,
        csList.getD r 0 * wsList.getD r 0 * ∑ j ∈ Finset.range 114, (wNat r j) ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun r =>
      csList.getD r 0 * wsList.getD r 0 * ∑ j ∈ Finset.range 114, (wNat r j) ^ 2) 13
  exact h2.trans h1

-- ============================================================================
-- Section 2: Real-valued kernel-boundary system and exact constants a, b
-- ============================================================================

noncomputable section

private def pVal (r : Fin 13) (i : ℕ) : ℝ :=
  if offNat r ≤ i ∧ i < offNat r + wWidth r then 1 / (wWidth r : ℝ) else 0

private def lam (r : Fin 13) : ℝ :=
  ((cNat r * wWidth r : ℕ) : ℝ) / (10012 : ℝ)

private def wReal (r : Fin 13) (j : ℕ) : ℝ :=
  (wNat r.val j : ℝ) / (50000 : ℝ)

private def aConst : ℝ := (38 * 359 : ℝ) / (10012 : ℝ)

private def bConst : ℝ :=
  1 + 2 * ((2688450544349644 : ℝ) / ((38 : ℝ) * 10012 * 50000 ^ 2) - 3)

private lemma pVal_nonneg (r : Fin 13) (i : ℕ) : 0 ≤ pVal r i := by
  unfold pVal; split_ifs <;> positivity

private lemma lam_nonneg (r : Fin 13) : 0 ≤ lam r := by
  unfold lam; positivity

private lemma lam_sum : ∑ r : Fin 13, lam r = 1 := by
  unfold lam
  rw [← Finset.sum_div]
  have h : (∑ r : Fin 13, ((cNat r * wWidth r : ℕ) : ℝ)) = 10012 := by
    exact_mod_cast hSlam_nat
  rw [h]
  norm_num

private lemma wReal_ge (r : Fin 13) (j : ℕ) (hj : 114 ≤ j) : wReal r j = 1 := by
  unfold wReal wNat
  rw [if_neg (by omega)]
  norm_num

private lemma pVal_symm (r : Fin 13) (i : ℕ) (hi : i < 38) :
    pVal r (37 - i) = pVal r i := by
  have hw := hWidths r
  unfold pVal
  have hiff : (offNat r ≤ 37 - i ∧ 37 - i < offNat r + wWidth r) ↔
      (offNat r ≤ i ∧ i < offNat r + wWidth r) := by omega
  simp only [hiff]

private lemma sum_pVal_mul (r : Fin 13) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range 38, pVal r i * f i =
      (1 / (wWidth r : ℝ)) * ∑ i ∈ Finset.range (wWidth r), f (offNat r + i) := by
  have hw := hWidths r
  have hsub : Finset.Ico (offNat r) (offNat r + wWidth r) ⊆ Finset.range 38 := by
    intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  rw [← Finset.sum_subset hsub]
  · calc ∑ i ∈ Finset.Ico (offNat r) (offNat r + wWidth r), pVal r i * f i
        = ∑ i ∈ Finset.Ico (offNat r) (offNat r + wWidth r), (1 / (wWidth r : ℝ)) * f i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_Ico] at hi
          simp [pVal, hi.1, hi.2]
      _ = (1 / (wWidth r : ℝ)) * ∑ i ∈ Finset.Ico (offNat r) (offNat r + wWidth r), f i := by
          rw [← Finset.mul_sum]
      _ = (1 / (wWidth r : ℝ)) * ∑ i ∈ Finset.range (wWidth r), f (offNat r + i) := by
          congr 1
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel_left]
  · intro i _ hi
    simp only [Finset.mem_Ico] at hi
    simp [pVal, hi]

private lemma pVal_sum (r : Fin 13) : ∑ i ∈ Finset.range 38, pVal r i = 1 := by
  have hw := (hWidths r).1
  have h := sum_pVal_mul r (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  rw [h]
  have hw_pos : (wWidth r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

private lemma pVal_sq_sum (r : Fin 13) :
    ∑ i ∈ Finset.range 38, (pVal r i) ^ 2 = 1 / (wWidth r : ℝ) := by
  have hw := (hWidths r).1
  have h := sum_pVal_mul r (pVal r)
  have hsq : ∑ i ∈ Finset.range 38, (pVal r i) ^ 2 =
      ∑ i ∈ Finset.range 38, pVal r i * pVal r i := by
    refine Finset.sum_congr rfl fun i _ => sq _
  rw [hsq, h]
  have hinner : ∑ i ∈ Finset.range (wWidth r), pVal r (offNat r + i) = 1 := by
    calc ∑ i ∈ Finset.range (wWidth r), pVal r (offNat r + i)
        = ∑ _i ∈ Finset.range (wWidth r), (1 / (wWidth r : ℝ)) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          simp [pVal, hi]
      _ = (wWidth r : ℝ) * (1 / (wWidth r : ℝ)) := by simp
      _ = 1 := by
          have hw_pos : (wWidth r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp
  rw [hinner, mul_one]

private lemma aConst_eq :
    (38 : ℝ) * ∑ r : Fin 13, lam r * ∑ i ∈ Finset.range 38, (pVal r i) ^ 2 = aConst := by
  have hterm : ∀ r : Fin 13,
      lam r * ∑ i ∈ Finset.range 38, (pVal r i) ^ 2 = (cNat r : ℝ) / 10012 := by
    intro r
    rw [pVal_sq_sum r]
    unfold lam
    have hw_pos : (wWidth r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (hWidths r).1; omega)
    push_cast
    field_simp
  simp_rw [hterm, ← Finset.sum_div]
  have hsum : (∑ r : Fin 13, (cNat r : ℝ)) = 359 := by exact_mod_cast hSumC_nat
  rw [hsum]
  unfold aConst
  ring

private lemma bConst_eq :
    1 + 2 * ((1 / (38 : ℝ)) * ∑ r : Fin 13, lam r * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 - 3) =
      bConst := by
  have hinner : ∑ r : Fin 13, lam r * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 =
      (2688450544349644 : ℝ) / (10012 * 50000 ^ 2) := by
    have h1 : ∀ r : Fin 13,
        lam r * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 =
          ((cNat r * wWidth r * ∑ j ∈ Finset.range 114, (wNat r.val j) ^ 2 : ℕ) : ℝ) /
            (10012 * 50000 ^ 2) := by
      intro r
      unfold lam wReal
      simp_rw [div_pow, ← Finset.sum_div]
      push_cast
      ring
    simp_rw [h1, ← Finset.sum_div]
    have hphi : (∑ r : Fin 13,
        ((cNat r * wWidth r * ∑ j ∈ Finset.range 114, (wNat r.val j) ^ 2 : ℕ) : ℝ)) =
        (2688450544349644 : ℝ) := by
      exact_mod_cast hPhi_nat
    rw [hphi]
  rw [hinner]
  unfold bConst
  ring

private lemma cov_real (q : ℕ) :
    1 ≤ ∑ r : Fin 13, lam r * ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + i) := by
  by_cases hq : q < 114
  · have hterm : ∀ r : Fin 13,
        lam r * ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + i) =
          ((cNat r * ∑ i ∈ Finset.range (wWidth r), wNat r.val (q + offNat r + i) : ℕ) : ℝ) /
            (10012 * 50000) := by
      intro r
      rw [sum_pVal_mul]
      unfold lam wReal
      have hw_pos : (wWidth r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (hWidths r).1; omega)
      have hidx : ∀ i, q + (offNat r + i) = q + offNat r + i := fun i => by omega
      simp_rw [hidx, ← Finset.sum_div]
      push_cast
      field_simp
    simp_rw [hterm, ← Finset.sum_div]
    rw [one_le_div (by norm_num : (0 : ℝ) < 10012 * 50000)]
    have hnat : ((10012 * 50000 : ℕ) : ℝ) ≤
        ((∑ r : Fin 13, cNat r * ∑ i ∈ Finset.range (wWidth r),
          wNat r.val (q + offNat r + i) : ℕ) : ℝ) := by
      exact_mod_cast hCov_nat q hq
    rw [Nat.cast_sum] at hnat
    have h1 : ((10012 * 50000 : ℕ) : ℝ) = (10012 : ℝ) * 50000 := by norm_num
    rw [← h1]
    exact hnat
  · have hge : 114 ≤ q := by omega
    have hterm : ∀ r : Fin 13,
        ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + i) = 1 := by
      intro r
      calc ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + i)
          = ∑ i ∈ Finset.range 38, pVal r i * 1 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [wReal_ge r (q + i) (by omega)]
        _ = 1 := by simp [pVal_sum r]
    simp_rw [hterm, mul_one]
    rw [lam_sum]

-- ============================================================================
-- Section 3: Discrete smoothing kernels K_r and Sidon energy upper bound
-- ============================================================================

private lemma mul_add_div_eq (q h t : ℕ) (hh : 0 < h) (ht : t < h) :
    (q * h + t) / h = q := by
  rw [Nat.mul_comm q h, Nat.mul_add_div hh, Nat.div_eq_of_lt ht, add_zero]

private def K (h : ℕ) (r : Fin 13) (s : ℤ) : ℝ :=
  if 0 ≤ s ∧ s < (38 * h : ℕ) then pVal r (s.toNat / h) / (h : ℝ) else 0

private lemma K_nonneg (h : ℕ) (r : Fin 13) (s : ℤ) : 0 ≤ K h r s := by
  unfold K; split_ifs
  · exact div_nonneg (pVal_nonneg r _) (Nat.cast_nonneg h)
  · exact le_rfl

private lemma K_eq_zero_of_not_mem (h : ℕ) (r : Fin 13) (s : ℤ)
    (hs : ¬ (0 ≤ s ∧ s < (38 * h : ℕ))) : K h r s = 0 := by
  unfold K; rw [if_neg hs]

private lemma K_symm (h : ℕ) (hh : 0 < h) (r : Fin 13) (s : ℕ) (hs : s < 38 * h) :
    K h r ((38 * h - 1 - s : ℕ) : ℤ) = K h r (s : ℤ) := by
  have hs' : 38 * h - 1 - s < 38 * h := by omega
  unfold K
  rw [if_pos ⟨by omega, by exact_mod_cast hs'⟩, if_pos ⟨by omega, by exact_mod_cast hs⟩]
  simp only [Int.toNat_natCast]
  have hq : s / h < 38 := Nat.div_lt_of_lt_mul (by omega)
  have hdiv : (38 * h - 1 - s) / h = 37 - s / h := by
    set q := s / h
    set t := s % h
    have hrem : s = q * h + t := (Nat.div_add_mod' s h).symm
    have hmod : t < h := Nat.mod_lt s hh
    have heq : 38 * h - 1 - s = (37 - q) * h + (h - 1 - t) := by
      have h1 : q ≤ 37 := by omega
      have h2 : t ≤ h - 1 := by omega
      have h3 : s ≤ 38 * h - 1 := by omega
      have h4 : 1 ≤ 38 * h := by omega
      have h5 : 1 ≤ h := by omega
      zify [h1, h2, h3, h4, h5]
      have hremZ : (s : ℤ) = (q : ℤ) * (h : ℤ) + (t : ℤ) := by exact_mod_cast hrem
      linear_combination -hremZ
    rw [heq, mul_add_div_eq (37 - q) h (h - 1 - t) hh (by omega)]
  rw [hdiv, pVal_symm r (s / h) hq]

private lemma sum_range_mul (a b : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ Finset.range (a * b), f s =
      ∑ i ∈ Finset.range a, ∑ t ∈ Finset.range b, f (i * b + t) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

private lemma K_sum (h : ℕ) (hh : 0 < h) (r : Fin 13) :
    ∑ s ∈ Finset.range (38 * h), K h r (s : ℤ) = 1 := by
  rw [sum_range_mul]
  have hterm : ∀ i ∈ Finset.range 38,
      ∑ t ∈ Finset.range h, K h r ((i * h + t : ℕ) : ℤ) = pVal r i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsub : ∀ t ∈ Finset.range h,
        K h r ((i * h + t : ℕ) : ℤ) = pVal r i / (h : ℝ) := by
      intro t ht
      rw [Finset.mem_range] at ht
      have hlt : i * h + t < 38 * h := by nlinarith
      unfold K
      rw [if_pos ⟨by omega, by exact_mod_cast hlt⟩]
      simp only [Int.toNat_natCast]
      rw [mul_add_div_eq i h t hh ht]
    rw [Finset.sum_congr rfl hsub, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hh_ne : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  rw [Finset.sum_congr rfl hterm, pVal_sum r]

private lemma K_sq_sum (h : ℕ) (hh : 0 < h) (r : Fin 13) :
    ∑ s ∈ Finset.range (38 * h), (K h r (s : ℤ)) ^ 2 =
      (38 : ℝ) / ((38 * h : ℕ) : ℝ) * ∑ i ∈ Finset.range 38, (pVal r i) ^ 2 := by
  rw [sum_range_mul]
  have hh_ne : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ i ∈ Finset.range 38,
      ∑ t ∈ Finset.range h, (K h r ((i * h + t : ℕ) : ℤ)) ^ 2 = (pVal r i) ^ 2 / (h : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsub : ∀ t ∈ Finset.range h,
        (K h r ((i * h + t : ℕ) : ℤ)) ^ 2 = (pVal r i / (h : ℝ)) ^ 2 := by
      intro t ht
      rw [Finset.mem_range] at ht
      have hlt : i * h + t < 38 * h := by nlinarith
      unfold K
      rw [if_pos ⟨by omega, by exact_mod_cast hlt⟩]
      simp only [Int.toNat_natCast]
      rw [mul_add_div_eq i h t hh ht]
    rw [Finset.sum_congr rfl hsub, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  push_cast
  field_simp

private def autoCorr (h : ℕ) (r : Fin 13) (d : ℤ) : ℝ :=
  ∑ s ∈ Finset.range (38 * h), K h r (s : ℤ) * K h r ((s : ℤ) + d)

private lemma autoCorr_nonneg (h : ℕ) (r : Fin 13) (d : ℤ) : 0 ≤ autoCorr h r d :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (K_nonneg _ _ _) (K_nonneg _ _ _)

private lemma autoCorr_zero (h : ℕ) (r : Fin 13) :
    autoCorr h r 0 = ∑ s ∈ Finset.range (38 * h), (K h r (s : ℤ)) ^ 2 := by
  unfold autoCorr
  refine Finset.sum_congr rfl fun s _ => by ring

private lemma autoCorr_eq_zero_of_abs_ge (h : ℕ) (r : Fin 13) (d : ℤ)
    (hd : (38 * h : ℤ) ≤ |d|) : autoCorr h r d = 0 := by
  unfold autoCorr
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hnot : ¬ (0 ≤ (s : ℤ) + d ∧ (s : ℤ) + d < (38 * h : ℕ)) := by
    rcases le_or_gt 0 d with h0 | h0
    · rw [abs_of_nonneg h0] at hd; omega
    · rw [abs_of_neg h0] at hd; omega
  rw [K_eq_zero_of_not_mem h r _ hnot, mul_zero]

private lemma autoCorr_neg (h : ℕ) (r : Fin 13) (d : ℤ) :
    autoCorr h r (-d) = autoCorr h r d := by
  unfold autoCorr
  set H := 38 * h
  have h1 : ∑ s ∈ Finset.range H, K h r (s : ℤ) * K h r ((s : ℤ) + -d) =
      ∑ s ∈ (Finset.range H).filter (fun s : ℕ => 0 ≤ (s : ℤ) - d ∧ (s : ℤ) - d < (H : ℤ)),
        K h r (s : ℤ) * K h r ((s : ℤ) - d) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range H)
      (p := fun s : ℕ => 0 ≤ (s : ℤ) - d ∧ (s : ℤ) - d < (H : ℤ))]
    have hzero : ∑ s ∈ (Finset.range H).filter (fun s : ℕ => ¬ (0 ≤ (s : ℤ) - d ∧ (s : ℤ) - d < (H : ℤ))),
        K h r (s : ℤ) * K h r ((s : ℤ) + -d) = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Finset.mem_filter] at hs
      have hnot : ¬ (0 ≤ (s : ℤ) + -d ∧ (s : ℤ) + -d < (38 * h : ℕ)) := by
        intro h'; exact hs.2 ⟨by omega, by omega⟩
      rw [K_eq_zero_of_not_mem h r _ hnot, mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun s _ => by rw [sub_eq_add_neg]
  have h2 : ∑ t ∈ Finset.range H, K h r (t : ℤ) * K h r ((t : ℤ) + d) =
      ∑ t ∈ (Finset.range H).filter (fun t : ℕ => 0 ≤ (t : ℤ) + d ∧ (t : ℤ) + d < (H : ℤ)),
        K h r (t : ℤ) * K h r ((t : ℤ) + d) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range H)
      (p := fun t : ℕ => 0 ≤ (t : ℤ) + d ∧ (t : ℤ) + d < (H : ℤ))]
    have hzero : ∑ t ∈ (Finset.range H).filter (fun t : ℕ => ¬ (0 ≤ (t : ℤ) + d ∧ (t : ℤ) + d < (H : ℤ))),
        K h r (t : ℤ) * K h r ((t : ℤ) + d) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [Finset.mem_filter] at ht
      have hnot : ¬ (0 ≤ (t : ℤ) + d ∧ (t : ℤ) + d < (38 * h : ℕ)) := by
        intro h'; exact ht.2 ⟨h'.1, by omega⟩
      rw [K_eq_zero_of_not_mem h r _ hnot, mul_zero]
    rw [hzero, add_zero]
  rw [h1, h2]
  refine Finset.sum_nbij' (fun s => ((s : ℤ) - d).toNat) (fun t => ((t : ℤ) + d).toNat)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    omega
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    have hcast : (((((s : ℤ) - d).toNat : ℕ) : ℤ)) = (s : ℤ) - d := by omega
    rw [hcast, sub_add_cancel, mul_comm]

private lemma autoCorr_total_sum (h : ℕ) (hh : 0 < h) (r : Fin 13) :
    autoCorr h r 0 + 2 * ∑ d ∈ Finset.Icc 1 (38 * h), autoCorr h r (d : ℤ) = 1 := by
  set H := 38 * h
  have hfull : ∑ d ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), autoCorr h r d = 1 := by
    unfold autoCorr
    rw [Finset.sum_comm]
    have hinner : ∀ s ∈ Finset.range H,
        ∑ d ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), K h r (s : ℤ) * K h r ((s : ℤ) + d) =
          K h r (s : ℤ) := by
      intro s hs
      rw [Finset.mem_range] at hs
      rw [← Finset.mul_sum]
      have h1 : ∑ d ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), K h r ((s : ℤ) + d) =
          ∑ t ∈ Finset.range H, K h r (t : ℤ) := by
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.Icc (-(H : ℤ)) (H : ℤ))
          (p := fun d => 0 ≤ (s : ℤ) + d ∧ (s : ℤ) + d < (H : ℤ))]
        have hzero : ∑ d ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
            (fun d => ¬ (0 ≤ (s : ℤ) + d ∧ (s : ℤ) + d < (H : ℤ))), K h r ((s : ℤ) + d) = 0 := by
          refine Finset.sum_eq_zero fun d hd => ?_
          rw [Finset.mem_filter] at hd
          have hnot : ¬ (0 ≤ (s : ℤ) + d ∧ (s : ℤ) + d < (38 * h : ℕ)) := by
            intro h'; exact hd.2 ⟨h'.1, by omega⟩
          exact K_eq_zero_of_not_mem h r _ hnot
        rw [hzero, add_zero]
        refine Finset.sum_nbij' (fun d => ((s : ℤ) + d).toNat) (fun t => (t : ℤ) - (s : ℤ))
          ?_ ?_ ?_ ?_ ?_
        · intro d hd
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hd ⊢
          omega
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at ht ⊢
          refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
        · intro d hd
          simp only [Finset.mem_filter, Finset.mem_Icc] at hd
          omega
        · intro t ht
          simp only [Finset.mem_range] at ht
          omega
        · intro d hd
          simp only [Finset.mem_filter] at hd
          have : ((((s : ℤ) + d).toNat : ℕ) : ℤ) = (s : ℤ) + d := by omega
          rw [this]
      rw [h1, K_sum h hh r, mul_one]
    rw [Finset.sum_congr rfl hinner, K_sum h hh r]
  have hpart : Finset.Icc (-(H : ℤ)) (H : ℤ) =
      insert (0 : ℤ) (Finset.Icc (1 : ℤ) (H : ℤ) ∪ Finset.Icc (-(H : ℤ)) (-1 : ℤ)) := by
    ext d; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_union]; omega
  have h0_not : (0 : ℤ) ∉ Finset.Icc (1 : ℤ) (H : ℤ) ∪ Finset.Icc (-(H : ℤ)) (-1 : ℤ) := by
    simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc (1 : ℤ) (H : ℤ)) (Finset.Icc (-(H : ℤ)) (-1 : ℤ)) := by
    rw [Finset.disjoint_left]; intro d hd1 hd2; simp only [Finset.mem_Icc] at hd1 hd2; omega
  rw [hpart, Finset.sum_insert h0_not, Finset.sum_union hdisj] at hfull
  have hneg : ∑ d ∈ Finset.Icc (-(H : ℤ)) (-1 : ℤ), autoCorr h r d =
      ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), autoCorr h r d := by
    refine Finset.sum_nbij' (fun d => -d) (fun d => -d) ?_ ?_ ?_ ?_ ?_
    · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
    · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
    · intro d _; ring
    · intro d _; ring
    · intro d _; exact (autoCorr_neg h r d).symm
  have hpos : ∑ d ∈ Finset.Icc (1 : ℤ) (H : ℤ), autoCorr h r d =
      ∑ d ∈ Finset.Icc 1 H, autoCorr h r (d : ℤ) := by
    refine Finset.sum_nbij' (fun d => d.toNat) (fun d => (d : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
    · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
    · intro d hd; simp only [Finset.mem_Icc] at hd; omega
    · intro d _; exact Int.toNat_natCast d
    · intro d hd
      simp only [Finset.mem_Icc] at hd
      have : ((d.toNat : ℕ) : ℤ) = d := by omega
      rw [this]
  rw [hneg, hpos] at hfull
  linarith

private def uVal (A : Finset ℕ) (h : ℕ) (r : Fin 13) (n : ℕ) : ℝ :=
  ∑ x ∈ A, K h r ((n : ℤ) - (x : ℤ))

private lemma uVal_sq_sum_le (A : Finset ℕ) (hA_sub : ∀ x ∈ A, x < N)
    (hSidon : IsSidon (A : Set ℕ)) (h : ℕ) (hh : 0 < h) (r : Fin 13) :
    ∑ n ∈ Finset.range (N + 38 * h - 1), (uVal A h r n) ^ 2 ≤
      1 + (A.card : ℝ) * autoCorr h r 0 := by
  set H := 38 * h
  have hH_pos : 0 < H := by omega
  have hexp : ∑ n ∈ Finset.range (N + H - 1), (uVal A h r n) ^ 2 =
      ∑ a ∈ A, ∑ b ∈ A, autoCorr h r ((a : ℤ) - (b : ℤ)) := by
    have h1 : ∀ n, (uVal A h r n) ^ 2 =
        ∑ a ∈ A, ∑ b ∈ A, K h r ((n : ℤ) - (a : ℤ)) * K h r ((n : ℤ) - (b : ℤ)) := by
      intro n
      unfold uVal
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have haN : a < N := hA_sub a ha
    unfold autoCorr
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (N + H - 1))
      (p := fun n => a ≤ n ∧ n < a + H)]
    have hzero : ∑ n ∈ (Finset.range (N + H - 1)).filter (fun n => ¬ (a ≤ n ∧ n < a + H)),
        K h r ((n : ℤ) - (a : ℤ)) * K h r ((n : ℤ) - (b : ℤ)) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      have : K h r ((n : ℤ) - (a : ℤ)) = 0 := K_eq_zero_of_not_mem h r _ (by omega)
      rw [this, zero_mul]
    rw [hzero, add_zero]
    refine Finset.sum_nbij' (fun n => n - a) (fun s => a + s) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢; omega
    · intro s hs; simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
      refine ⟨by omega, by omega, by omega⟩
    · intro n hn; simp only [Finset.mem_filter] at hn; omega
    · intro s _; omega
    · intro n hn
      simp only [Finset.mem_filter] at hn
      have hc1 : ((n - a : ℕ) : ℤ) = (n : ℤ) - (a : ℤ) := by omega
      rw [hc1]
      congr 2
      ring
  rw [hexp]
  rw [← Finset.sum_product']
  let P := A ×ˢ A
  let Peq := P.filter (fun p => p.1 = p.2)
  let Pgt := P.filter (fun p => p.2 < p.1)
  let Plt := P.filter (fun p => p.1 < p.2)
  have hP_union : P = Peq ∪ (Pgt ∪ Plt) := by
    ext ⟨a, b⟩
    simp only [P, Peq, Pgt, Plt, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro hab; rcases lt_trichotomy a b with h1 | h1 | h1
      · exact Or.inr (Or.inr ⟨hab, h1⟩)
      · exact Or.inl ⟨hab, h1⟩
      · exact Or.inr (Or.inl ⟨hab, h1⟩)
    · rintro (⟨hab, _⟩ | ⟨hab, _⟩ | ⟨hab, _⟩) <;> exact hab
  have hd1 : Disjoint Peq (Pgt ∪ Plt) := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    simp only [Peq, Pgt, Plt, Finset.mem_union, Finset.mem_filter] at hp1 hp2; omega
  have hd2 : Disjoint Pgt Plt := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    simp only [Pgt, Plt, Finset.mem_filter] at hp1 hp2; omega
  change ∑ p ∈ P, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) ≤ _
  rw [hP_union, Finset.sum_union hd1, Finset.sum_union hd2]
  have hEq : ∑ p ∈ Peq, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) =
      (A.card : ℝ) * autoCorr h r 0 := by
    have hbij : ∑ p ∈ Peq, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ _a ∈ A, autoCorr h r 0 := by
      refine Finset.sum_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_ ?_
      · intro p hp; simp only [Peq, P, Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
      · intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩
      · intro p hp; simp only [Peq, Finset.mem_filter] at hp; ext <;> [rfl; exact hp.2]
      · intro _ _; rfl
      · intro p hp; simp only [Peq, Finset.mem_filter] at hp; rw [hp.2, sub_self]
    rw [hbij, Finset.sum_const, nsmul_eq_mul]
  have hSym : ∑ p ∈ Plt, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) =
      ∑ p ∈ Pgt, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Plt, Pgt, P, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p hp; simp only [Plt, Pgt, P, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _; rfl
    · intro p _; rfl
    · intro p _
      have : ((p.1 : ℤ) - (p.2 : ℤ)) = -((p.2 : ℤ) - (p.1 : ℤ)) := by ring
      rw [this, autoCorr_neg]
  have hGt : ∑ p ∈ Pgt, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) ≤
      ∑ d ∈ Finset.Icc 1 H, autoCorr h r (d : ℤ) := by
    let PgtS := Pgt.filter (fun p => p.1 - p.2 ≤ H)
    have hdrop_gt : ∑ p ∈ Pgt, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ p ∈ PgtS, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Pgt) (p := fun p => p.1 - p.2 ≤ H)]
      have hzero : ∑ p ∈ Pgt.filter (fun p => ¬ p.1 - p.2 ≤ H),
          autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        simp only [Pgt, Finset.mem_filter] at hp
        refine autoCorr_eq_zero_of_abs_ge h r _ ?_
        rw [abs_of_nonneg (by omega)]; omega
      rw [hzero, add_zero]
    rw [hdrop_gt]
    let diffFn : ℕ × ℕ → ℕ := fun p => p.1 - p.2
    have hinj : Set.InjOn diffFn (PgtS : Set (ℕ × ℕ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [PgtS, Pgt, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
      have h := Finset.IsSidon.eq_of_tsub hSidon hp₁.1.1.1 hp₁.1.1.2 hp₂.1.1.1 hp₂.1.1.2
        hp₁.1.2 hp₂.1.2 heq
      ext
      · exact h.1
      · exact h.2
    have himg : ∑ p ∈ PgtS, autoCorr h r ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ d ∈ PgtS.image diffFn, autoCorr h r (d : ℤ) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [PgtS, Pgt, Finset.mem_filter] at hp
      have : ((diffFn p : ℕ) : ℤ) = (p.1 : ℤ) - (p.2 : ℤ) := by
        dsimp only [diffFn]; omega
      rw [this]
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => autoCorr_nonneg h r (d : ℤ))
    intro d hd
    simp only [Finset.mem_image, PgtS, Pgt, Finset.mem_filter] at hd
    rcases hd with ⟨p, ⟨⟨_, hlt⟩, hle⟩, rfl⟩
    simp only [Finset.mem_Icc, diffFn]
    omega
  rw [hEq, hSym]
  have htot := autoCorr_total_sum h hh r
  have hc0 : 0 ≤ autoCorr h r 0 := autoCorr_nonneg h r 0
  linarith

private lemma weighted_energy_le (A : Finset ℕ) (hA_sub : ∀ x ∈ A, x < N)
    (hSidon : IsSidon (A : Set ℕ)) (h : ℕ) (hh : 0 < h) :
    ∑ r : Fin 13, lam r * ∑ n ∈ Finset.range (N + 38 * h - 1), (uVal A h r n) ^ 2 ≤
      1 + aConst * (A.card : ℝ) / ((38 * h : ℕ) : ℝ) := by
  have hstep : ∑ r : Fin 13, lam r * ∑ n ∈ Finset.range (N + 38 * h - 1), (uVal A h r n) ^ 2 ≤
      ∑ r : Fin 13, lam r * (1 + (A.card : ℝ) * autoCorr h r 0) :=
    Finset.sum_le_sum fun r _ =>
      mul_le_mul_of_nonneg_left (uVal_sq_sum_le A hA_sub hSidon h hh r) (lam_nonneg r)
  have hrhs : ∑ r : Fin 13, lam r * (1 + (A.card : ℝ) * autoCorr h r 0) =
      1 + aConst * (A.card : ℝ) / ((38 * h : ℕ) : ℝ) := by
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib, lam_sum]
    congr 1
    have h2 : ∑ r : Fin 13, lam r * ((A.card : ℝ) * autoCorr h r 0) =
        ∑ r : Fin 13, ((A.card : ℝ) / ((38 * h : ℕ) : ℝ)) *
          ((38 : ℝ) * (lam r * ∑ i ∈ Finset.range 38, (pVal r i) ^ 2)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [autoCorr_zero, K_sq_sum h hh r]
      ring
    rw [h2, ← Finset.mul_sum, ← Finset.mul_sum, aConst_eq]
    ring
  linarith

-- ============================================================================
-- Section 4: Boundary weights Q_r, covering inequality, and Cauchy-Schwarz
-- ============================================================================

private def Q (h N : ℕ) (r : Fin 13) (n : ℕ) : ℝ :=
  if n < 3 * (38 * h) then wReal r (n / h)
  else if N + 38 * h - 2 - n < 3 * (38 * h) ∧ n ≤ N + 38 * h - 2 then
    wReal r ((N + 38 * h - 2 - n) / h)
  else 1

private lemma Q_left_region (h N : ℕ) (hh : 0 < h) (hN : 6 * (38 * h) ≤ N)
    (r : Fin 13) (x s : ℕ) (hx : x < 3 * (38 * h)) (hs : s < 38 * h) :
    Q h N r (x + s) = wReal r ((x + s) / h) := by
  unfold Q
  by_cases h1 : x + s < 3 * (38 * h)
  · rw [if_pos h1]
  · rw [if_neg h1]
    have h2 : ¬ (N + 38 * h - 2 - (x + s) < 3 * (38 * h) ∧ x + s ≤ N + 38 * h - 2) := by omega
    rw [if_neg h2]
    have hdiv : 114 ≤ (x + s) / h := by
      have : 114 * h ≤ x + s := by omega
      exact (Nat.le_div_iff_mul_le hh).mpr this
    exact (wReal_ge r _ hdiv).symm

private lemma covering_left (h N : ℕ) (hh : 0 < h) (hN : 6 * (38 * h) ≤ N)
    (x : ℕ) (hx : x < 3 * (38 * h)) :
    1 ≤ ∑ r : Fin 13, lam r * ∑ s ∈ Finset.range (38 * h), K h r (s : ℤ) * Q h N r (x + s) := by
  set q := x / h
  set t := x % h
  have ht_lt : t < h := Nat.mod_lt x hh
  have hx_eq : x = q * h + t := (Nat.div_add_mod' x h).symm
  have hh_pos : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
  have hh_ne : (h : ℝ) ≠ 0 := ne_of_gt hh_pos
  have hinner : ∀ r : Fin 13,
      ∑ s ∈ Finset.range (38 * h), K h r (s : ℤ) * Q h N r (x + s) =
        (1 - (t : ℝ) / (h : ℝ)) * (∑ i ∈ Finset.range 38, pVal r i * wReal r (q + i)) +
          ((t : ℝ) / (h : ℝ)) * (∑ i ∈ Finset.range 38, pVal r i * wReal r (q + 1 + i)) := by
    intro r
    rw [sum_range_mul]
    have hblk : ∀ i ∈ Finset.range 38,
        ∑ u ∈ Finset.range h, K h r ((i * h + u : ℕ) : ℤ) * Q h N r (x + (i * h + u)) =
          (1 - (t : ℝ) / (h : ℝ)) * (pVal r i * wReal r (q + i)) +
            ((t : ℝ) / (h : ℝ)) * (pVal r i * wReal r (q + 1 + i)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hsplit : Finset.range h = Finset.range (h - t) ∪ Finset.Ico (h - t) h := by
        ext u; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (h - t)) (Finset.Ico (h - t) h) := by
        rw [Finset.disjoint_left]; intro u h1 h2; simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj]
      have hpart1 : ∑ u ∈ Finset.range (h - t),
          K h r ((i * h + u : ℕ) : ℤ) * Q h N r (x + (i * h + u)) =
            ((h - t : ℕ) : ℝ) * (pVal r i / (h : ℝ) * wReal r (q + i)) := by
        have hconst : ∀ u ∈ Finset.range (h - t),
            K h r ((i * h + u : ℕ) : ℤ) * Q h N r (x + (i * h + u)) =
              pVal r i / (h : ℝ) * wReal r (q + i) := by
          intro u hu
          rw [Finset.mem_range] at hu
          have hu_lt : u < h := by omega
          have hs_lt : i * h + u < 38 * h := by nlinarith
          rw [Q_left_region h N hh hN r x (i * h + u) hx hs_lt]
          have hK : K h r ((i * h + u : ℕ) : ℤ) = pVal r i / (h : ℝ) := by
            unfold K
            rw [if_pos ⟨by omega, by exact_mod_cast hs_lt⟩]
            simp only [Int.toNat_natCast]
            rw [mul_add_div_eq i h u hh hu_lt]
          have hdiv : (x + (i * h + u)) / h = q + i := by
            have heq : x + (i * h + u) = (q + i) * h + (t + u) := by
              rw [hx_eq]; ring
            rw [heq, mul_add_div_eq (q + i) h (t + u) hh (by omega)]
          rw [hK, hdiv]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hpart2 : ∑ u ∈ Finset.Ico (h - t) h,
          K h r ((i * h + u : ℕ) : ℤ) * Q h N r (x + (i * h + u)) =
            (t : ℝ) * (pVal r i / (h : ℝ) * wReal r (q + 1 + i)) := by
        have hconst : ∀ u ∈ Finset.Ico (h - t) h,
            K h r ((i * h + u : ℕ) : ℤ) * Q h N r (x + (i * h + u)) =
              pVal r i / (h : ℝ) * wReal r (q + 1 + i) := by
          intro u hu
          rw [Finset.mem_Ico] at hu
          have hs_lt : i * h + u < 38 * h := by nlinarith
          rw [Q_left_region h N hh hN r x (i * h + u) hx hs_lt]
          have hK : K h r ((i * h + u : ℕ) : ℤ) = pVal r i / (h : ℝ) := by
            unfold K
            rw [if_pos ⟨by omega, by exact_mod_cast hs_lt⟩]
            simp only [Int.toNat_natCast]
            rw [mul_add_div_eq i h u hh hu.2]
          have hdiv : (x + (i * h + u)) / h = q + 1 + i := by
            have heq : x + (i * h + u) = (q + 1 + i) * h + (t + u - h) := by
              zify [show h ≤ t + u by omega]
              have hxZ : (x : ℤ) = (q : ℤ) * (h : ℤ) + (t : ℤ) := by exact_mod_cast hx_eq
              linarith
            rw [heq, mul_add_div_eq (q + 1 + i) h (t + u - h) hh (by omega)]
          rw [hK, hdiv]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico,
          show h - (h - t) = t by omega, nsmul_eq_mul]
      rw [hpart1, hpart2, Nat.cast_sub (le_of_lt ht_lt)]
      field_simp
    rw [Finset.sum_congr rfl hblk, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [hinner, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ r : Fin 13, lam r * ((1 - (t : ℝ) / (h : ℝ)) *
        ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + i)) =
      (1 - (t : ℝ) / (h : ℝ)) *
        ∑ r : Fin 13, lam r * ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + i) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
  have h2 : ∑ r : Fin 13, lam r * (((t : ℝ) / (h : ℝ)) *
        ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + 1 + i)) =
      ((t : ℝ) / (h : ℝ)) *
        ∑ r : Fin 13, lam r * ∑ i ∈ Finset.range 38, pVal r i * wReal r (q + 1 + i) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
  rw [h1, h2]
  have ht_nonneg : 0 ≤ (t : ℝ) / (h : ℝ) := by positivity
  have ht_le_one : (t : ℝ) / (h : ℝ) ≤ 1 := by
    rw [div_le_one hh_pos]; exact_mod_cast le_of_lt ht_lt
  have hc1 := cov_real q
  have hc2 := cov_real (q + 1)
  nlinarith

private lemma covering_all (h N : ℕ) (hh : 0 < h) (hN : 6 * (38 * h) ≤ N)
    (x : ℕ) (hx : x < N) :
    1 ≤ ∑ r : Fin 13, lam r * ∑ s ∈ Finset.range (38 * h), K h r (s : ℤ) * Q h N r (x + s) := by
  set H := 38 * h
  by_cases hxL : x < 3 * H
  · exact covering_left h N hh hN x hxL
  · by_cases hxR : x < N - 3 * H
    · have hterm : ∀ r : Fin 13,
          ∑ s ∈ Finset.range H, K h r (s : ℤ) * Q h N r (x + s) = 1 := by
        intro r
        have hQ1 : ∀ s ∈ Finset.range H, K h r (s : ℤ) * Q h N r (x + s) = K h r (s : ℤ) := by
          intro s hs
          rw [Finset.mem_range] at hs
          have hq : Q h N r (x + s) = 1 := by
            unfold Q
            rw [if_neg (by omega), if_neg (by omega)]
          rw [hq, mul_one]
        rw [Finset.sum_congr rfl hQ1, K_sum h hh r]
      simp_rw [hterm, mul_one, lam_sum]
      exact le_rfl
    · set x' := N - 1 - x
      have hx'L : x' < 3 * H := by omega
      have hrefl : ∀ r : Fin 13,
          ∑ s ∈ Finset.range H, K h r (s : ℤ) * Q h N r (x + s) =
            ∑ s' ∈ Finset.range H, K h r (s' : ℤ) * Q h N r (x' + s') := by
        intro r
        refine Finset.sum_nbij' (fun s => H - 1 - s) (fun s' => H - 1 - s') ?_ ?_ ?_ ?_ ?_
        · intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
        · intro s' hs'; simp only [Finset.mem_range] at hs' ⊢; omega
        · intro s hs; simp only [Finset.mem_range] at hs; omega
        · intro s' hs'; simp only [Finset.mem_range] at hs'; omega
        · intro s hs
          simp only [Finset.mem_range] at hs
          rw [← K_symm h hh r s hs]
          congr 1
          have hsum_eq : N + H - 2 - (x + s) = x' + (H - 1 - s) := by omega
          have hQeq : Q h N r (x + s) = Q h N r (x' + (H - 1 - s)) := by
            unfold Q
            rw [if_neg (by omega)]
            by_cases hc : x' + (H - 1 - s) < 3 * H
            · rw [if_pos ⟨by omega, by omega⟩, if_pos hc, hsum_eq]
            · rw [if_neg (by omega), if_neg hc, if_neg (by omega)]
          exact hQeq
      simp_rw [hrefl]
      exact covering_left h N hh hN x' hx'L

private lemma Q_sq_sum (h N : ℕ) (hh : 0 < h) (hN : 6 * (38 * h) ≤ N) (r : Fin 13) :
    ∑ n ∈ Finset.range (N + 38 * h - 1), (Q h N r n) ^ 2 =
      ((N + 38 * h - 1 : ℕ) : ℝ) - 2 * ((3 * (38 * h) : ℕ) : ℝ) +
        2 * (h : ℝ) * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 := by
  set H := 38 * h
  set M := N + H - 1
  have hM : 6 * H ≤ M := by omega
  have hsplit : Finset.range M =
      Finset.range (3 * H) ∪ (Finset.Ico (3 * H) (M - 3 * H) ∪ Finset.Ico (M - 3 * H) M) := by
    ext n; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
  have hd1 : Disjoint (Finset.range (3 * H))
      (Finset.Ico (3 * H) (M - 3 * H) ∪ Finset.Ico (M - 3 * H) M) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at h1 h2; omega
  have hd2 : Disjoint (Finset.Ico (3 * H) (M - 3 * H)) (Finset.Ico (M - 3 * H) M) := by
    rw [Finset.disjoint_left]; intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2]
  have hL : ∑ n ∈ Finset.range (3 * H), (Q h N r n) ^ 2 =
      (h : ℝ) * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 := by
    have h3H : 3 * H = 114 * h := by omega
    rw [h3H, sum_range_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hsub : ∀ t ∈ Finset.range h, (Q h N r (j * h + t)) ^ 2 = (wReal r j) ^ 2 := by
      intro t ht
      rw [Finset.mem_range] at ht
      have hlt : j * h + t < 3 * H := by nlinarith
      unfold Q
      rw [if_pos hlt, mul_add_div_eq j h t hh ht]
    rw [Finset.sum_congr rfl hsub, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hMid : ∑ n ∈ Finset.Ico (3 * H) (M - 3 * H), (Q h N r n) ^ 2 =
      ((M - 6 * H : ℕ) : ℝ) := by
    have h1 : ∀ n ∈ Finset.Ico (3 * H) (M - 3 * H), (Q h N r n) ^ 2 = 1 := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      unfold Q
      rw [if_neg (by omega), if_neg (by omega), one_pow]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Ico,
      show M - 3 * H - 3 * H = M - 6 * H by omega, nsmul_eq_mul, mul_one]
  have hR : ∑ n ∈ Finset.Ico (M - 3 * H) M, (Q h N r n) ^ 2 =
      ∑ n ∈ Finset.range (3 * H), (Q h N r n) ^ 2 := by
    refine Finset.sum_nbij' (fun n => M - 1 - n) (fun n => M - 1 - n) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
    · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
    · intro n hn; simp only [Finset.mem_Ico] at hn; omega
    · intro n hn; simp only [Finset.mem_range] at hn; omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      have heq : N + H - 2 - n = M - 1 - n := by omega
      unfold Q
      rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, if_pos (by omega), heq]
  rw [hR, hL, hMid, Nat.cast_sub hM]
  push_cast
  ring

private lemma weighted_Q_sq_sum (h N : ℕ) (hh : 0 < h) (hN : 6 * (38 * h) ≤ N) :
    ∑ r : Fin 13, lam r * ∑ n ∈ Finset.range (N + 38 * h - 1), (Q h N r n) ^ 2 ≤
      (N : ℝ) + bConst * ((38 * h : ℕ) : ℝ) := by
  have h1 : ∀ r : Fin 13,
      ∑ n ∈ Finset.range (N + 38 * h - 1), (Q h N r n) ^ 2 =
        ((N + 38 * h - 1 : ℕ) : ℝ) - 2 * ((3 * (38 * h) : ℕ) : ℝ) +
          2 * (h : ℝ) * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 :=
    fun r => Q_sq_sum h N hh hN r
  simp_rw [h1, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, lam_sum, one_mul]
  have h2 : ∑ r : Fin 13, lam r * (2 * (h : ℝ) * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2) =
      2 * (h : ℝ) * ∑ r : Fin 13, lam r * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring
  rw [h2]
  have hb := bConst_eq
  have hN1 : 1 ≤ N + 38 * h := by omega
  have hcast : ((N + 38 * h - 1 : ℕ) : ℝ) = (N : ℝ) + ((38 * h : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hN1, Nat.cast_add, Nat.cast_one]
  rw [hcast]
  have hb_mul : bConst * ((38 * h : ℕ) : ℝ) =
      ((38 * h : ℕ) : ℝ) +
        2 * (h : ℝ) * ∑ r : Fin 13, lam r * ∑ j ∈ Finset.range 114, (wReal r j) ^ 2 -
          2 * ((3 * (38 * h) : ℕ) : ℝ) := by
    rw [← hb]
    push_cast
    ring
  linarith

private lemma sidon_quadratic_bound (A : Finset ℕ) (hA_sub : ∀ x ∈ A, x < N)
    (hSidon : IsSidon (A : Set ℕ)) (h : ℕ) (hh : 0 < h) (hN : 6 * (38 * h) ≤ N) :
    ((A.card : ℝ)) ^ 2 ≤
      ((N : ℝ) + bConst * ((38 * h : ℕ) : ℝ)) *
        (1 + aConst * (A.card : ℝ) / ((38 * h : ℕ) : ℝ)) := by
  set H := 38 * h
  set J := Finset.range (N + H - 1)
  have hcov_sum : (A.card : ℝ) ≤
      ∑ r : Fin 13, ∑ n ∈ J, (Real.sqrt (lam r) * Q h N r n) * (Real.sqrt (lam r) * uVal A h r n) := by
    have h1 : (A.card : ℝ) ≤
        ∑ x ∈ A, ∑ r : Fin 13, lam r * ∑ s ∈ Finset.range H, K h r (s : ℤ) * Q h N r (x + s) := by
      calc (A.card : ℝ) = ∑ _x ∈ A, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun x hx => covering_all h N hh hN x (hA_sub x hx)
    have h2 : ∑ x ∈ A, ∑ r : Fin 13, lam r * ∑ s ∈ Finset.range H, K h r (s : ℤ) * Q h N r (x + s) =
        ∑ r : Fin 13, ∑ n ∈ J, lam r * Q h N r n * uVal A h r n := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hswap : ∀ x ∈ A,
          ∑ s ∈ Finset.range H, K h r (s : ℤ) * Q h N r (x + s) =
            ∑ n ∈ J, K h r ((n : ℤ) - (x : ℤ)) * Q h N r n := by
        intro x hx
        have hxN : x < N := hA_sub x hx
        rw [← Finset.sum_filter_add_sum_filter_not (s := J) (p := fun n => x ≤ n ∧ n < x + H)]
        have hzero : ∑ n ∈ J.filter (fun n => ¬ (x ≤ n ∧ n < x + H)),
            K h r ((n : ℤ) - (x : ℤ)) * Q h N r n = 0 := by
          refine Finset.sum_eq_zero fun n hn => ?_
          rw [Finset.mem_filter] at hn
          rw [K_eq_zero_of_not_mem h r _ (by omega), zero_mul]
        rw [hzero, add_zero]
        refine Finset.sum_nbij' (fun s => x + s) (fun n => n - x) ?_ ?_ ?_ ?_ ?_
        · intro s hs; simp only [J, Finset.mem_filter, Finset.mem_range] at hs ⊢
          refine ⟨by omega, by omega, by omega⟩
        · intro n hn; simp only [J, Finset.mem_filter, Finset.mem_range] at hn ⊢; omega
        · intro s _; omega
        · intro n hn; simp only [Finset.mem_filter] at hn; omega
        · intro s _; have : (((x + s : ℕ) : ℤ) - (x : ℤ)) = (s : ℤ) := by omega
          rw [this]
      calc ∑ x ∈ A, lam r * ∑ s ∈ Finset.range H, K h r (s : ℤ) * Q h N r (x + s)
          = ∑ x ∈ A, lam r * ∑ n ∈ J, K h r ((n : ℤ) - (x : ℤ)) * Q h N r n := by
            refine Finset.sum_congr rfl fun x hx => by rw [hswap x hx]
        _ = ∑ x ∈ A, ∑ n ∈ J, lam r * Q h N r n * K h r ((n : ℤ) - (x : ℤ)) := by
            refine Finset.sum_congr rfl fun x _ => by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
        _ = ∑ n ∈ J, ∑ x ∈ A, lam r * Q h N r n * K h r ((n : ℤ) - (x : ℤ)) := Finset.sum_comm
        _ = ∑ n ∈ J, lam r * Q h N r n * uVal A h r n := by
            refine Finset.sum_congr rfl fun n _ => by rw [← Finset.mul_sum]; rfl
    have h3 : ∑ r : Fin 13, ∑ n ∈ J, lam r * Q h N r n * uVal A h r n =
        ∑ r : Fin 13, ∑ n ∈ J,
          (Real.sqrt (lam r) * Q h N r n) * (Real.sqrt (lam r) * uVal A h r n) := by
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun n _ => ?_
      have hs : Real.sqrt (lam r) * Real.sqrt (lam r) = lam r := Real.mul_self_sqrt (lam_nonneg r)
      calc lam r * Q h N r n * uVal A h r n
          = (Real.sqrt (lam r) * Real.sqrt (lam r)) * Q h N r n * uVal A h r n := by rw [hs]
        _ = (Real.sqrt (lam r) * Q h N r n) * (Real.sqrt (lam r) * uVal A h r n) := by ring
    linarith
  let S := (Finset.univ : Finset (Fin 13)) ×ˢ J
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun p : Fin 13 × ℕ => Real.sqrt (lam p.1) * Q h N p.1 p.2)
    (fun p : Fin 13 × ℕ => Real.sqrt (lam p.1) * uVal A h p.1 p.2)
  have hcov_prod : (A.card : ℝ) ≤
      ∑ p ∈ S, (Real.sqrt (lam p.1) * Q h N p.1 p.2) *
        (Real.sqrt (lam p.1) * uVal A h p.1 p.2) := by
    rw [Finset.sum_product]; exact hcov_sum
  have hsq_le : ((A.card : ℝ)) ^ 2 ≤
      (∑ p ∈ S, (Real.sqrt (lam p.1) * Q h N p.1 p.2) ^ 2) *
        (∑ p ∈ S, (Real.sqrt (lam p.1) * uVal A h p.1 p.2) ^ 2) := by
    have h0 : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
    calc ((A.card : ℝ)) ^ 2
        ≤ (∑ p ∈ S, (Real.sqrt (lam p.1) * Q h N p.1 p.2) *
            (Real.sqrt (lam p.1) * uVal A h p.1 p.2)) ^ 2 :=
          pow_le_pow_left₀ h0 hcov_prod 2
      _ ≤ _ := hcs
  have hQ_eq : ∑ p ∈ S, (Real.sqrt (lam p.1) * Q h N p.1 p.2) ^ 2 =
      ∑ r : Fin 13, lam r * ∑ n ∈ J, (Q h N r n) ^ 2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (lam_nonneg r)]
  have hu_eq : ∑ p ∈ S, (Real.sqrt (lam p.1) * uVal A h p.1 p.2) ^ 2 =
      ∑ r : Fin 13, lam r * ∑ n ∈ J, (uVal A h r n) ^ 2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (lam_nonneg r)]
  rw [hQ_eq, hu_eq] at hsq_le
  have hQ_nonneg : 0 ≤ ∑ r : Fin 13, lam r * ∑ n ∈ J, (Q h N r n) ^ 2 :=
    Finset.sum_nonneg fun r _ => mul_nonneg (lam_nonneg r) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hu_nonneg : 0 ≤ ∑ r : Fin 13, lam r * ∑ n ∈ J, (uVal A h r n) ^ 2 :=
    Finset.sum_nonneg fun r _ => mul_nonneg (lam_nonneg r) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hQ_le := weighted_Q_sq_sum h N hh hN
  have hu_le := weighted_energy_le A hA_sub hSidon h hh
  have hQ_rhs_nn : 0 ≤ (N : ℝ) + bConst * (H : ℝ) := le_trans hQ_nonneg hQ_le
  calc ((A.card : ℝ)) ^ 2
      ≤ (∑ r : Fin 13, lam r * ∑ n ∈ J, (Q h N r n) ^ 2) *
          (∑ r : Fin 13, lam r * ∑ n ∈ J, (uVal A h r n) ^ 2) := hsq_le
    _ ≤ ((N : ℝ) + bConst * (H : ℝ)) *
          (1 + aConst * (A.card : ℝ) / (H : ℝ)) :=
        mul_le_mul hQ_le hu_le hu_nonneg hQ_rhs_nn

-- ============================================================================
-- Section 5: Asymptotic bound for all N >= 10^24 and final theorems
-- ============================================================================

private lemma poly_close (t H k : ℝ) (ht : (10 ^ 6 : ℝ) ≤ t)
    (hH_pos : 0 < H) (hH_gt : (1444 / 1000 : ℝ) * t ^ 3 - 38 < H)
    (hH_le : H ≤ (1444 / 1000 : ℝ) * t ^ 3)
    (hquadH : H * k ^ 2 ≤ (t ^ 4 + bConst * H) * (H + aConst * k)) :
    k ≤ t ^ 2 + (9434 / 10000 : ℝ) * t := by
  set ρ : ℝ := 1444 / 1000
  set γ : ℝ := 9434 / 10000
  set M : ℝ := t ^ 2 + γ * t
  have ha_pos : 0 < aConst := by unfold aConst; norm_num
  have ha_le : aConst < 2 := by unfold aConst; norm_num
  have hb_pos : 0 < bConst := by unfold bConst; norm_num
  have hb_le : bConst < 1 := by unfold bConst; norm_num
  have h2γ_sub : 0 < 2 * γ - bConst * ρ := by
    dsimp only [γ, ρ]; unfold bConst; norm_num
  have h2γ_le : 2 * γ - bConst * ρ < 2 := by
    dsimp only [γ, ρ]; unfold bConst; norm_num
  have hlead : (1 / 10000 : ℝ) < ρ * (2 * γ - bConst * ρ) - aConst := by
    dsimp only [γ, ρ]; unfold bConst aConst; norm_num
  have hcoeff1 : aConst * (γ + bConst * ρ) ≤ 6 := by
    dsimp only [γ, ρ]; unfold aConst bConst; norm_num
  have hcoeff2 : aConst * bConst * ρ * γ ≤ 4 := by
    dsimp only [γ, ρ]; unfold aConst bConst; norm_num
  have ht_pos : 0 < t := by linarith
  have ht2 : (10 ^ 12 : ℝ) ≤ t ^ 2 := by nlinarith
  have ht3 : (10 ^ 18 : ℝ) ≤ t ^ 3 := by nlinarith
  have ht4_ge : (10 ^ 24 : ℝ) ≤ t ^ 4 := by nlinarith
  by_contra hgt
  push Not at hgt
  have hslope : aConst * (t ^ 4 + bConst * H) < H * (k + M) := by
    have hH_ge1 : t ^ 3 ≤ H := by
      have hρ : ρ * t ^ 3 - 38 ≥ t ^ 3 := by dsimp only [ρ]; linarith
      linarith
    have hM_ge : t ^ 2 ≤ M := by
      have : 0 ≤ γ * t := by dsimp only [γ]; positivity
      dsimp only [M]; linarith
    have h1 : bConst * H ≤ 2 * t ^ 3 := by
      have hH2 : H ≤ 2 * t ^ 3 := by
        have : ρ * t ^ 3 ≤ 2 * t ^ 3 := by dsimp only [ρ]; linarith
        linarith
      nlinarith
    have h2 : aConst * (t ^ 4 + bConst * H) ≤ 2 * (t ^ 4 + 2 * t ^ 3) := by nlinarith
    have h3 : 2 * t ^ 5 ≤ H * (k + M) := by
      have : 2 * t ^ 2 ≤ k + M := by linarith
      have : t ^ 3 * (2 * t ^ 2) ≤ H * (k + M) :=
        mul_le_mul hH_ge1 this (by positivity) (le_of_lt hH_pos)
      linarith
    have h4 : 2 * (t ^ 4 + 2 * t ^ 3) < 2 * t ^ 5 := by
      have h5 : t ^ 4 + 2 * t ^ 3 < t ^ 4 * t := by nlinarith
      linarith
    linarith
  have hf_lt : H * M ^ 2 - aConst * (t ^ 4 + bConst * H) * M < H * (t ^ 4 + bConst * H) := by
    have hdiff : 0 < (k - M) * (H * (k + M) - aConst * (t ^ 4 + bConst * H)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hM2 : (2 * γ - bConst * ρ) * t ^ 3 ≤ M ^ 2 - t ^ 4 - bConst * H := by
    have hMsq : M ^ 2 - t ^ 4 = 2 * γ * t ^ 3 + γ ^ 2 * t ^ 2 := by dsimp only [M]; ring
    have hbH : bConst * H ≤ bConst * ρ * t ^ 3 := by
      have : H ≤ ρ * t ^ 3 := hH_le
      nlinarith
    have hγsq : 0 ≤ γ ^ 2 * t ^ 2 := by positivity
    linarith
  have hLHS_lb : (ρ * t ^ 3 - 38) * ((2 * γ - bConst * ρ) * t ^ 3) ≤
      H * (M ^ 2 - t ^ 4 - bConst * H) := by
    have h1 : (ρ * t ^ 3 - 38) * ((2 * γ - bConst * ρ) * t ^ 3) ≤
        H * ((2 * γ - bConst * ρ) * t ^ 3) :=
      mul_le_mul_of_nonneg_right (le_of_lt hH_gt) (by positivity)
    have h2 : H * ((2 * γ - bConst * ρ) * t ^ 3) ≤ H * (M ^ 2 - t ^ 4 - bConst * H) :=
      mul_le_mul_of_nonneg_left hM2 (le_of_lt hH_pos)
    linarith
  have hRHS_ub : aConst * (t ^ 4 + bConst * H) * M ≤
      aConst * (t ^ 4 + bConst * ρ * t ^ 3) * (t ^ 2 + γ * t) := by
    have h1 : t ^ 4 + bConst * H ≤ t ^ 4 + bConst * ρ * t ^ 3 := by
      have : bConst * H ≤ bConst * (ρ * t ^ 3) :=
        mul_le_mul_of_nonneg_left hH_le (le_of_lt hb_pos)
      linarith
    have hM_nn : 0 ≤ M := by dsimp only [M, γ]; positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (le_of_lt ha_pos)) hM_nn
  have hpoly : aConst * (t ^ 4 + bConst * ρ * t ^ 3) * (t ^ 2 + γ * t) ≤
      (ρ * t ^ 3 - 38) * ((2 * γ - bConst * ρ) * t ^ 3) := by
    have hid : (ρ * t ^ 3 - 38) * ((2 * γ - bConst * ρ) * t ^ 3) -
        aConst * (t ^ 4 + bConst * ρ * t ^ 3) * (t ^ 2 + γ * t) =
        t ^ 3 * ((ρ * (2 * γ - bConst * ρ) - aConst) * t ^ 3 -
          aConst * (γ + bConst * ρ) * t ^ 2 -
          aConst * bConst * ρ * γ * t -
          38 * (2 * γ - bConst * ρ)) := by ring
    have h1 : (1 / 10000 : ℝ) * t ^ 3 ≤ (ρ * (2 * γ - bConst * ρ) - aConst) * t ^ 3 :=
      mul_le_mul_of_nonneg_right (le_of_lt hlead) (by positivity)
    have h2 : aConst * (γ + bConst * ρ) * t ^ 2 ≤ 6 * t ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff1 (sq_nonneg t)
    have h3 : aConst * bConst * ρ * γ * t ≤ 4 * t :=
      mul_le_mul_of_nonneg_right hcoeff2 (le_of_lt ht_pos)
    have h4 : 38 * (2 * γ - bConst * ρ) ≤ 76 := by linarith
    have h5 : 6 * t ^ 2 + 4 * t + 76 ≤ (1 / 10000 : ℝ) * t ^ 3 := by
      have h6 : 100 * t ^ 2 ≤ (1 / 10000 : ℝ) * t ^ 3 := by nlinarith
      nlinarith
    have hinner : 0 ≤ (ρ * (2 * γ - bConst * ρ) - aConst) * t ^ 3 -
        aConst * (γ + bConst * ρ) * t ^ 2 -
        aConst * bConst * ρ * γ * t -
        38 * (2 * γ - bConst * ρ) := by
      have ha : (1 / 10000 : ℝ) * t ^ 3 - 6 * t ^ 2 - 4 * t - 76 ≤
          (ρ * (2 * γ - bConst * ρ) - aConst) * t ^ 3 -
            aConst * (γ + bConst * ρ) * t ^ 2 -
            aConst * bConst * ρ * γ * t -
            38 * (2 * γ - bConst * ρ) :=
        sub_le_sub (sub_le_sub (sub_le_sub h1 h2) h3) h4
      exact le_trans (by linarith only [h5]) ha
    have hmul : 0 ≤ t ^ 3 * ((ρ * (2 * γ - bConst * ρ) - aConst) * t ^ 3 -
        aConst * (γ + bConst * ρ) * t ^ 2 -
        aConst * bConst * ρ * γ * t -
        38 * (2 * γ - bConst * ρ)) := mul_nonneg (by positivity) hinner
    linarith
  linarith

private lemma card_le_of_large (N : ℕ) (hN : 10 ^ 24 ≤ N) (A₁ : Finset ℕ)
    (hA₁_sub : A₁ ⊆ Finset.Icc 1 N) (hSidon₁ : IsSidon (A₁ : Set ℕ)) :
    (A₁.card : ℝ) ≤ Real.sqrt (N : ℝ) + (9434 / 10000 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  let A : Finset ℕ := A₁.image (fun x => x - 1)
  have hA_card : A.card = A₁.card := by
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    dsimp only at hxy
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hA₁_sub hx)).1
    have hy1 : 1 ≤ y := (Finset.mem_Icc.mp (hA₁_sub hy)).1
    omega
  have hA_sub : ∀ x ∈ A, x < N := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hyI := Finset.mem_Icc.mp (hA₁_sub hy)
    omega
  have hSidon : IsSidon (A : Set ℕ) := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hsum
    rcases Finset.mem_image.mp ha₁ with ⟨x₁, hx₁, rfl⟩
    rcases Finset.mem_image.mp hb₁ with ⟨y₁, hy₁, rfl⟩
    rcases Finset.mem_image.mp ha₂ with ⟨x₂, hx₂, rfl⟩
    rcases Finset.mem_image.mp hb₂ with ⟨y₂, hy₂, rfl⟩
    have hx₁1 := (Finset.mem_Icc.mp (hA₁_sub hx₁)).1
    have hy₁1 := (Finset.mem_Icc.mp (hA₁_sub hy₁)).1
    have hx₂1 := (Finset.mem_Icc.mp (hA₁_sub hx₂)).1
    have hy₂1 := (Finset.mem_Icc.mp (hA₁_sub hy₂)).1
    have hsum' : x₁ + x₂ = y₁ + y₂ := by omega
    rcases hSidon₁ x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  rw [← hA_card]
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have ht_nn : 0 ≤ t := Real.rpow_nonneg hN_nn _
  have ht4 : t ^ 4 = (N : ℝ) := by
    change ((N : ℝ) ^ (4⁻¹ : ℝ)) ^ (4 : ℕ) = (N : ℝ)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN_nn]
    norm_num
  have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
    have hsq : (t ^ 2) ^ 2 = (N : ℝ) := by linear_combination ht4
    rw [← hsq, Real.sqrt_sq (sq_nonneg t)]
  have ht_ge : (10 ^ 6 : ℝ) ≤ t := by
    by_contra hlt
    push Not at hlt
    have hN_cast : ((10 ^ 6 : ℝ)) ^ 4 ≤ (N : ℝ) := by
      have : ((10 ^ 24 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith [show ((10 ^ 6 : ℝ)) ^ 4 = ((10 ^ 24 : ℕ) : ℝ) by norm_num]
    have hpow : t ^ 4 < ((10 ^ 6 : ℝ)) ^ 4 := pow_lt_pow_left₀ hlt ht_nn (by norm_num)
    linarith
  let h : ℕ := Nat.floor ((1444 / 1000 : ℝ) * t ^ 3 / 38)
  have h_arg_ge : (1 : ℝ) ≤ (1444 / 1000 : ℝ) * t ^ 3 / 38 := by
    have ht3 : (10 ^ 18 : ℝ) ≤ t ^ 3 := by nlinarith
    linarith
  have hh_pos : 0 < h := Nat.floor_pos.mpr h_arg_ge
  have h38_eq : 38 * ((1444 / 1000 : ℝ) * t ^ 3 / 38) = (1444 / 1000 : ℝ) * t ^ 3 := by ring
  have hH_le : ((38 * h : ℕ) : ℝ) ≤ (1444 / 1000 : ℝ) * t ^ 3 := by
    have hfl : (h : ℝ) ≤ (1444 / 1000 : ℝ) * t ^ 3 / 38 := Nat.floor_le (by linarith)
    push_cast
    linarith
  have hH_gt : (1444 / 1000 : ℝ) * t ^ 3 - 38 < ((38 * h : ℕ) : ℝ) := by
    have hfl : (1444 / 1000 : ℝ) * t ^ 3 / 38 < (h : ℝ) + 1 := Nat.lt_floor_add_one _
    push_cast
    linarith
  have hN_6H : 6 * (38 * h) ≤ N := by
    have hreal : ((6 * (38 * h) : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : ((6 * (38 * h) : ℕ) : ℝ) = 6 * ((38 * h : ℕ) : ℝ) := by push_cast; ring
      rw [this, ← ht4]
      have ht3_nn : 0 ≤ t ^ 3 := by positivity
      have h6 : 6 * (1444 / 1000 : ℝ) ≤ t := by linarith
      nlinarith
    exact_mod_cast hreal
  have hquad := sidon_quadratic_bound A hA_sub hSidon h hh_pos hN_6H
  set H : ℝ := ((38 * h : ℕ) : ℝ)
  have hH_pos : 0 < H := Nat.cast_pos.mpr (by omega)
  have hquadH : H * (A.card : ℝ) ^ 2 ≤
      (t ^ 4 + bConst * H) * (H + aConst * (A.card : ℝ)) := by
    rw [← ht4] at hquad
    have hmul := mul_le_mul_of_nonneg_left hquad (le_of_lt hH_pos)
    have hsimp : H * ((t ^ 4 + bConst * H) * (1 + aConst * (A.card : ℝ) / H)) =
        (t ^ 4 + bConst * H) * (H + aConst * (A.card : ℝ)) := by field_simp
    linarith
  rw [← ht2]
  exact poly_close t H (A.card : ℝ) ht_ge hH_pos hH_gt hH_le hquadH

lemma F_le_of_large (N : ℕ) (hN : 10 ^ 24 ≤ N) :
    Green31.F N ≤ Real.sqrt (N : ℝ) + (9434 / 10000 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  unfold Green31.F Finset.maxSidonSubsetCard
  set B : ℝ := Real.sqrt (N : ℝ) + (9434 / 10000 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ)
  have hB_nn : 0 ≤ B := by positivity
  have hsup : ((Finset.Icc 1 N).powerset.filter fun S : Finset ℕ => IsSidon (S : Set ℕ)).sup
      Finset.card ≤ Nat.floor B := by
    refine Finset.sup_le fun S hS => ?_
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    exact Nat.le_floor (card_le_of_large N hN S hS.1 hS.2)
  calc (((((Finset.Icc 1 N).powerset.filter fun S : Finset ℕ => IsSidon (S : Set ℕ)).sup
          Finset.card) : ℕ) : ℝ)
      ≤ ((Nat.floor B : ℕ) : ℝ) := by exact_mod_cast hsup
    _ ≤ B := Nat.floor_le hB_nn

lemma eventually_F_le :
    ∀ᶠ N in atTop,
      Green31.F N ≤ Real.sqrt (N : ℝ) + (9434 / 10000 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) :=
  Filter.eventually_atTop.mpr ⟨10 ^ 24, fun N hN => F_le_of_large N hN⟩

end

end OMA.Green31Upper

noncomputable def OMA.answer (N : ℕ) : ℝ :=
  Real.sqrt (N : ℝ) + (9434 / 10000 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ)

theorem OMA.solution :
    Green31.green_31.upper.answer = OMA.answer →
      type_of% @Green31.green_31.upper := by
  intro hans
  rw [hans]
  refine ⟨OMA.Green31Upper.eventually_F_le.frequently, 9434 / 10000, by norm_num, 0,
    Filter.Eventually.of_forall fun N => ?_⟩
  simp only [OMA.answer]
  linarith
