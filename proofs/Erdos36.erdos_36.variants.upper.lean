import FormalConjectures.ErdosProblems.«36»
import Mathlib

/-!
Upper bound for Erdos Problem 36 (Minimum Overlap Problem):
  limsup_{N -> infty} M(N) / N <= 3809 / 10000 = 0.3809 < 0.380926853433087.

Construction and attribution:
We use a 512-bin rational step function h : Fin 512 -> Q cap [0, 1] with denominator D = 2000,
obtained by block-averaging the MIT-licensed step function from atrislabs/records
(1b-erdos-minimum-overlap, commit 1fa857a021dd) onto 512 equal bins and rounding to denominator 2000
with exact mass sum_i a_i = 512000. Its exact discrete maximum overlap is
  C_cert = 2 * 390031388 / (512 * 2000^2) = 0.38089002734375 < 3809 / 10000.

Proof outline (100% self-contained, no MeasureTheory):
1. Kernel-verified convolution bound via base-(2^32) Kronecker substitution (`decide +kernel`,
   no `native_decide`), proving every shifted correlation of h with (1 - h) is at most 256 * C_cert.
2. For large N, define probabilities pN : Fin (2*N) -> R from the 512 bins (with 1/2 on the < 512
   remainder indices), so sum_x pN(x) = N exactly and the expected overlap at every shift k is
   at most C_cert * N + 1024.
3. Endow Conf (2*N) = (Fin (2*N) -> Bool) with finite product weights wt(S). Prove disjoint-support
   expectation factorization via Equiv.piEquivPiSubtypeProd, yielding a 2nd-moment bound on |A_S| - N
   and a 4th-moment bound on the even/odd-split overlap deviations for every nonzero shift k.
4. Combine all deviations into a single nonnegative potential Z(S) with E[Z] < 1 for large N,
   extract S with Z(S) < 1, and rebalance A_S to exact cardinality N by moving ||A_S| - N| elements,
   giving M(N) / N <= 3809 / 10000 for all sufficiently large N and hence limsup <= 3809 / 10000.
-/

namespace OMA.Erdos36Upper

open Filter

-- ============================================================================
-- Section 1: 512-bin rational step function and Kronecker convolution certificate
-- ============================================================================

private def m : ℕ := 512
private def D : ℕ := 2000
private def peak : ℕ := 390031388
private def B : ℕ := 2 ^ 32
private def B32 : ℕ := B ^ 32

private def evalBase (l : List ℕ) : ℕ :=
  l.foldr (fun x acc => x + B * acc) 0

private def evalChunks (cs : List (List ℕ)) : ℕ :=
  cs.foldr (fun l acc => evalBase l + B32 * acc) 0

private def aChunks : List (List ℕ) :=
[
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 16, 21, 35, 295, 572, 973, 1276],
  [1765, 1706, 1827, 1910, 1312, 1146, 1313, 1312, 1118, 1229, 1260, 1161, 1621, 1664, 1773, 1974, 1994, 1974, 1921, 1988, 1997, 2000, 1896, 1786, 1428, 1040, 826, 774, 13, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 770, 1131, 1184, 1524, 1665, 1644, 1722, 1861, 1973, 1756, 1477, 1404, 1527, 1380, 1310, 1202, 808, 1097],
  [942, 779, 627, 764, 869, 1067, 995, 797, 928, 946, 936, 710, 977, 1100, 1377, 1462, 1488, 1472, 1692, 1951, 1970, 2000, 1970, 1873, 1491, 1337, 846, 892, 833, 969, 673, 493],
  [586, 580, 634, 557, 579, 485, 656, 793, 677, 624, 977, 1030, 1489, 1790, 1962, 1987, 1996, 1983, 2000, 1753, 1193, 785, 707, 718, 758, 801, 1194, 1240, 1334, 1594, 1528, 1653],
  [1989, 2000, 1865, 1982, 1971, 1958, 1808, 1485, 1778, 1712, 1244, 1187, 1214, 1267, 1111, 1018, 1152, 1149, 1051, 1173, 1401, 1382, 1989, 2000, 2000, 2000, 2000, 2000, 2000, 1999, 1996, 910],
  [682, 1006, 1179, 1460, 1889, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 1885, 1763, 1944, 1800, 1981, 1896, 1764, 1707, 1960, 1814, 1723, 1965, 1965, 1976, 2000, 2000, 2000, 2000],
  [2000, 2000, 2000, 2000, 2000, 2000, 2000, 1963, 1905, 1594, 1608, 1874, 1722, 1831, 1987, 2000, 2000, 1973, 1919, 1906, 1335, 1402, 1609, 1394, 1500, 1345, 1008, 1452, 1882, 1846, 1572, 1972],
  [2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 1910, 1386, 1403, 1306, 912, 1153, 1149, 1020, 1108, 1264, 1220, 1184, 1093, 1714, 1615, 1786, 1851, 1941, 2000, 2000, 1853, 1948, 2000],
  [1656, 1519, 1594, 1332, 1242, 1195, 749, 809, 719, 707, 781, 1196, 1754, 2000, 1983, 1996, 1987, 1962, 1790, 1489, 1030, 977, 624, 677, 790, 659, 485, 579, 558, 633, 580, 586],
  [493, 673, 969, 833, 892, 846, 1337, 1490, 1874, 1970, 2000, 1970, 1951, 1692, 1472, 1488, 1462, 1377, 1100, 976, 710, 936, 946, 928, 797, 995, 1067, 869, 764, 627, 779, 942],
  [1096, 808, 1202, 1310, 1380, 1527, 1404, 1477, 1756, 1973, 1862, 1722, 1644, 1664, 1524, 1184, 1131, 770, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 13, 773, 826, 1040, 1428, 1786, 1896, 2000, 1997, 1988, 1921, 1974, 1994, 1974, 1773, 1664, 1621, 1161, 1258, 1231, 1118, 1312, 1311, 1147, 1313, 1910, 1827, 1708, 1763],
  [1277, 974, 571, 295, 35, 21, 16, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

private def bChunks : List (List ℕ) :=
[
  [2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000],
  [2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 1999, 2000, 2000, 2000, 2000, 1984, 1979, 1965, 1705, 1429, 1026, 723],
  [237, 292, 173, 90, 687, 853, 689, 688, 882, 769, 742, 839, 379, 336, 227, 26, 6, 26, 79, 12, 3, 0, 104, 214, 572, 960, 1174, 1227, 1987, 2000, 2000, 2000],
  [2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 1230, 869, 816, 476, 336, 356, 278, 138, 27, 244, 523, 596, 473, 620, 690, 798, 1192, 904],
  [1058, 1221, 1373, 1236, 1131, 933, 1005, 1203, 1072, 1054, 1064, 1290, 1024, 900, 623, 538, 512, 528, 308, 49, 30, 0, 30, 126, 510, 663, 1154, 1108, 1167, 1031, 1327, 1507],
  [1414, 1420, 1367, 1442, 1421, 1515, 1341, 1210, 1323, 1376, 1023, 970, 511, 210, 38, 13, 4, 17, 0, 246, 804, 1219, 1293, 1281, 1191, 1251, 805, 758, 668, 406, 481, 344],
  [0, 52, 147, 0, 0, 59, 149, 214, 385, 286, 907, 816, 780, 736, 892, 980, 851, 847, 1088, 694, 597, 614, 90, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [28, 428, 154, 118, 548, 992, 655, 500, 606, 391, 598, 665, 94, 81, 27, 0, 0, 13, 169, 278, 126, 392, 406, 95, 37, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 24, 35, 35, 277, 186, 40, 293, 236, 104, 19, 200, 56, 237, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 540, 821, 994, 1318],
  [1090, 4, 1, 0, 0, 0, 0, 0, 0, 11, 618, 599, 827, 949, 851, 848, 982, 889, 733, 786, 813, 756, 288, 222, 515, 192, 42, 29, 18, 135, 0, 11],
  [347, 472, 406, 666, 760, 806, 1199, 1242, 1282, 1293, 1215, 807, 247, 0, 17, 4, 13, 38, 210, 511, 970, 1023, 1376, 1323, 1207, 1344, 1515, 1421, 1443, 1366, 1420, 1414],
  [1507, 1327, 1031, 1167, 1108, 1154, 663, 509, 127, 30, 0, 30, 49, 308, 528, 512, 538, 623, 900, 1023, 1290, 1064, 1054, 1072, 1203, 1005, 933, 1131, 1236, 1373, 1221, 1058],
  [903, 1192, 798, 690, 620, 473, 596, 523, 244, 27, 139, 278, 356, 335, 476, 816, 869, 1230, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000],
  [2000, 2000, 2000, 1987, 1226, 1174, 960, 572, 214, 104, 0, 3, 12, 79, 26, 6, 26, 227, 336, 379, 839, 740, 771, 882, 688, 687, 854, 688, 90, 173, 294, 235],
  [724, 1027, 1428, 1705, 1965, 1979, 1984, 2000, 2000, 2000, 2000, 1999, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000],
  [2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000, 2000]
]

private def cChunks : List (List ℕ) :=
[
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2000, 2000, 2000, 2000, 2000, 34000, 76000, 146000, 736000, 1880000, 3826000, 6378000],
  [9908000, 13320000, 16974000, 20794000, 23418000, 25710000, 28336000, 30960000, 33196000, 35654000, 38174000, 40496000, 43738000, 47066000, 50612000, 54560000, 58548000, 62496000, 66338000, 70314000, 74308000, 78308000, 82100000, 85672000, 88528000, 90608000, 92260000, 93808000, 93834000, 93834000, 93834000, 93834000],
  [93834000, 93834000, 93834000, 93834000, 93834000, 93834000, 93834000, 93834000, 93833999, 93834000, 93834000, 93834000, 93834000, 93833968, 95373958, 97635930, 100003410, 103050857, 106379797, 109666775, 113108911, 116821676, 120746443, 124214375, 127036610, 129538316, 131988332, 133747892, 134782918, 135132704, 134188976, 133477484],
  [132423076, 131377930, 130342597, 129921244, 130355997, 131194846, 131921716, 132455874, 132787210, 132576172, 132150527, 130955215, 129313664, 127789030, 126657267, 125281871, 124417421, 123742095, 123532613, 124116468, 125350848, 127053631, 129394483, 132540808, 135919930, 139913715, 143638305, 147787234, 152187473, 156245447, 159612430, 162664862],
  [164947567, 166887240, 169252110, 171549076, 173903504, 176656648, 180142176, 184023639, 188556321, 193134272, 198156068, 202973154, 207910964, 212460627, 215921538, 218732427, 220777247, 221748856, 222856680, 223624471, 222495422, 220386755, 218578098, 217012333, 215139987, 214007645, 213536433, 212871016, 212135086, 211459842, 211045635, 210543144],
  [210744517, 210627912, 209506202, 208716369, 208210821, 207578728, 207053067, 207580905, 209427871, 211855326, 215099190, 218421420, 221797838, 226035637, 229822034, 232558300, 235331993, 237770636, 239784235, 241621279, 243452314, 245235797, 249060073, 253725204, 258762468, 263737648, 268443640, 273398686, 277364705, 280556550, 283096651, 282749782],
  [281420439, 281031646, 280092690, 278711320, 278555707, 279332845, 281081890, 282938012, 285356174, 287730186, 290425356, 293597504, 296908025, 300058188, 303703976, 308086549, 313165287, 318775375, 325172152, 331269106, 337034073, 342770366, 347461100, 351232458, 353091928, 353928504, 352969994, 350888437, 347953673, 344061538, 339955897, 335501734],
  [331051666, 326882528, 323129287, 320065578, 318036887, 317424375, 318527755, 320965764, 325296988, 329728345, 335713249, 341948035, 347795338, 353649321, 359115501, 363720003, 367891164, 371063272, 373134187, 375245793, 376371320, 377074474, 378050341, 378983932, 379904846, 381217033, 381309263, 382012885, 382927882, 384244160, 385374625, 386867511],
  [387033482, 387003951, 386926467, 386386341, 386448236, 386817136, 387103433, 388041038, 389424147, 390006279, 390003713, 390007803, 390003829, 389994204, 390006550, 389999926, 389986857, 389995191, 389983683, 390000955, 390008162, 389692656, 389709509, 389372653, 389964331, 389934723, 389982123, 389996497, 389985551, 389739528, 389987016, 390007766],
  [390002748, 390008999, 389996505, 389990826, 389994694, 389997453, 389896621, 390001426, 390009712, 390004509, 389980728, 389997282, 389991276, 390004053, 390005143, 390004866, 389998744, 390000175, 389993158, 390000068, 389993480, 389992690, 390002259, 390007079, 389984023, 390004843, 390008627, 390006772, 389993779, 390002303, 389986244, 389992779],
  [390005312, 390004559, 390001228, 390000793, 389994322, 390000529, 389999733, 389994784, 389995863, 390004790, 390000007, 390009136, 390006752, 390004125, 390000461, 390005802, 389993825, 389999930, 390003484, 389998730, 389988177, 389999778, 390000166, 389996058, 389987025, 389995685, 390006622, 390004460, 389995213, 390009687, 390009605, 390007722],
  [389995526, 389996462, 390001288, 389998698, 390003101, 389998123, 389993205, 389999631, 389995528, 389995348, 389988930, 389989850, 390000493, 389998174, 389999874, 390013511, 389995660, 390003505, 390007183, 389993708, 389985642, 389995761, 389998923, 390007844, 390008536, 390007072, 390008554, 390011076, 389994581, 389997622, 389994573, 389995682],
  [389991393, 390001677, 390004771, 390004968, 390013703, 390006188, 390008382, 390021338, 390005385, 389996705, 389993528, 390009617, 390006409, 389997181, 389994442, 390010350, 390001906, 390005666, 389985058, 389993143, 389998016, 389997205, 389974368, 389984707, 390003358, 390020139, 389991647, 389985940, 390008385, 390016814, 390001950, 389989162],
  [389988593, 390021070, 389991193, 389992637, 389991102, 389981408, 390001652, 389995127, 390001820, 390004193, 390014750, 390009949, 389987308, 389996405, 390015274, 389999864, 389983863, 389997470, 390014218, 390023567, 389990282, 389985198, 389988038, 389984925, 389994523, 390000766, 389990568, 390022957, 390010551, 390031388, 389987484, 389989820],
  [390005625, 389985015, 390000844, 390003974, 389983707, 390016831, 390010063, 389936843, 389928285, 389692886, 390014426, 389925082, 390000498, 389776764, 387355222, 385827484, 383234941, 380452528, 377471248, 373349322, 366665258, 357877666, 346897273, 333768699, 317339102, 298708729, 279857542, 260042470, 241571231, 226737129, 213728792, 204777768],
  [213728792, 226737129, 241571231, 260042470, 279857542, 298708729, 317339102, 333768699, 346897273, 357877666, 366665258, 373349322, 377471248, 380452528, 383234941, 385827484, 387355222, 389776764, 390000498, 389925082, 390014426, 389692886, 389928285, 389936843, 390010063, 390016831, 389983707, 390003974, 390000844, 389985015, 390005625, 389989820],
  [389987484, 390031388, 390010551, 390022957, 389990568, 390000766, 389994523, 389984925, 389988038, 389985198, 389990282, 390023567, 390014218, 389997470, 389983863, 389999864, 390015274, 389996405, 389987308, 390009949, 390014750, 390004193, 390001820, 389995127, 390001652, 389981408, 389991102, 389992637, 389991193, 390019070, 389988593, 389991162],
  [389999950, 390018814, 390010385, 389987940, 389995647, 390026139, 390005358, 389986707, 389976368, 390003205, 390000016, 389995143, 389987058, 390007666, 390003906, 390012350, 389996442, 389999181, 390008409, 390011617, 389995528, 389998705, 390007385, 390023338, 390010382, 390008188, 390015703, 390004968, 390004771, 390001677, 389991393, 389995682],
  [389994573, 389997622, 389994581, 390011076, 390008554, 390007072, 390008536, 390007844, 389998923, 389995761, 389985642, 389993708, 390007183, 390003505, 389995660, 390013511, 389999874, 389998174, 389998493, 389987850, 389986930, 389995348, 389995528, 389999631, 389993205, 389998123, 390003101, 389998698, 390001288, 389996462, 389995526, 390005722],
  [390007605, 390007687, 389993213, 390002460, 390004622, 389993685, 389985025, 389994058, 389998166, 389997778, 389986177, 389996730, 389999484, 389995930, 389989825, 390001802, 389996461, 390000125, 390002752, 390005136, 389996007, 390000790, 389991863, 389992784, 389995733, 389996529, 389990322, 389996793, 389997228, 390000559, 390001312, 389988779],
  [389982244, 389998303, 389987779, 390002772, 390004627, 390000843, 389986023, 390003079, 389998259, 389988690, 389989480, 389996068, 389989158, 389996175, 389994744, 390000866, 390001143, 390000053, 389987276, 389995282, 389984728, 390000509, 390005712, 389999426, 389996621, 389993453, 389992694, 389992826, 389994505, 390006999, 389982748, 389993766],
  [389995016, 389643528, 389865551, 389912497, 389956123, 389874723, 389990331, 390000653, 390011509, 389998656, 390012162, 389998955, 389993683, 389999191, 389984857, 390001926, 390002550, 389998204, 389729829, 389999803, 389999713, 390010279, 389270147, 387887038, 386949433, 386663136, 386294236, 386232341, 386772467, 386851951, 386889482, 388903511],
  [389990625, 389992160, 390009882, 389938885, 388361263, 386285033, 383662846, 381741932, 379596341, 377838474, 375939320, 373483793, 371184187, 368951272, 365955164, 362258003, 357765501, 352673321, 346519338, 340324035, 334309249, 328126345, 322962988, 318813764, 316855755, 315822375, 316504887, 318581578, 321645287, 325398528, 329567666, 334017734],
  [338471897, 342577538, 346469673, 349404437, 351437994, 352326504, 351419928, 349080458, 345127100, 341168366, 335630073, 329645106, 323896152, 317799375, 311815287, 306624549, 301767976, 297946188, 294958025, 291835504, 289993356, 288494186, 286902174, 285696012, 284839890, 284400845, 285607707, 286637320, 287174690, 286779646, 286036439, 284785782],
  [282952651, 280404550, 277210705, 273244686, 268289640, 263583648, 258608468, 253571204, 248906073, 245239797, 243448314, 241613279, 239510235, 237774636, 235327993, 232560300, 229820034, 226039637, 221807838, 218419420, 215103190, 212161326, 209729871, 208208905, 207079067, 207518728, 208184821, 208632369, 209386202, 210531912, 210752517, 210529144],
  [211025635, 211457842, 212133086, 212873016, 213534433, 214003645, 215239987, 217010333, 218574098, 220382755, 222499422, 223622471, 222852680, 221744856, 220773247, 218728427, 215917538, 212456627, 207906964, 202969154, 198152068, 193130272, 188552321, 184019639, 180144176, 176652648, 173899504, 171545076, 169246110, 166883240, 164943567, 162660862],
  [159608430, 156241447, 152183473, 147783234, 143634305, 139909715, 135915930, 132538808, 129390483, 127049631, 125346848, 124112468, 123528613, 123738095, 124413421, 125277871, 126653267, 127785030, 129309664, 130953215, 132148527, 132574172, 132785210, 132453874, 131919716, 131192846, 130353997, 129919244, 130340597, 131375930, 132421076, 133475484],
  [134188976, 135132704, 134782918, 133747892, 131988332, 129538316, 127036610, 124214375, 120746443, 116821676, 113106911, 109664775, 106377797, 103050857, 100003410, 97635930, 95373958, 93833968, 93834000, 93834000, 93834000, 93834000, 93833999, 93834000, 93834000, 93834000, 93834000, 93834000, 93834000, 93834000, 93834000, 93834000],
  [93834000, 93834000, 93834000, 93808000, 92262000, 90610000, 88530000, 85674000, 82102000, 78310000, 74310000, 70316000, 66340000, 62498000, 58550000, 54562000, 50614000, 47068000, 43740000, 40498000, 38176000, 35660000, 33198000, 30962000, 28338000, 25716000, 23422000, 20796000, 16976000, 13322000, 9906000, 6380000],
  [3826000, 1878000, 736000, 146000, 76000, 34000, 2000, 2000, 2000, 2000, 2000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

private lemma cert_mul : evalChunks aChunks * evalChunks bChunks = evalChunks cChunks := by
  decide +kernel

private lemma cert_bound : cChunks.all (fun l => l.all (fun x => decide (x ≤ peak))) = true := by
  decide +kernel

private lemma cert_a_sum : (aChunks.map List.sum).sum = 512000 := by
  decide +kernel

private lemma cert_a_le : aChunks.all (fun l => l.all (fun x => decide (x ≤ D))) = true := by
  decide +kernel

private lemma cert_a_lens :
    aChunks.length = 16 ∧ aChunks.all (fun l => decide (l.length = 32)) = true := by
  decide +kernel

private lemma cert_b_lens :
    bChunks.length = 16 ∧ bChunks.all (fun l => decide (l.length = 32)) = true := by
  decide +kernel

private lemma cert_c_lens :
    cChunks.length = 32 ∧ cChunks.all (fun l => decide (l.length = 32)) = true := by
  decide +kernel

private lemma cert_b_eq :
    bChunks = aChunks.reverse.map (fun l => l.reverse.map (fun x => D - x)) := by
  decide +kernel

private def aFlat : List ℕ := aChunks.flatten
private def bFlat : List ℕ := bChunks.flatten
private def cFlat : List ℕ := cChunks.flatten

private lemma evalBase_append (l₁ l₂ : List ℕ) :
    evalBase (l₁ ++ l₂) = evalBase l₁ + B ^ l₁.length * evalBase l₂ := by
  induction l₁ with
  | nil => simp [evalBase]
  | cons x xs ih =>
    simp only [List.cons_append, evalBase, List.foldr_cons, List.length_cons, pow_succ']
    have ih' : (xs ++ l₂).foldr (fun x acc => x + B * acc) 0 =
        xs.foldr (fun x acc => x + B * acc) 0 +
          B ^ xs.length * l₂.foldr (fun x acc => x + B * acc) 0 := ih
    rw [ih']
    ring

private lemma evalChunks_eq_evalBase_flatten (cs : List (List ℕ))
    (h : ∀ l ∈ cs, l.length = 32) :
    evalChunks cs = evalBase cs.flatten := by
  induction cs with
  | nil => simp [evalChunks, evalBase]
  | cons l ls ih =>
    have hl : l.length = 32 := h l (by simp)
    have hls : ∀ l' ∈ ls, l'.length = 32 := fun l' hl' => h l' (by simp [hl'])
    simp only [evalChunks, List.foldr_cons, List.flatten_cons]
    rw [evalBase_append, hl, ← ih hls]
    rfl

private lemma evalBase_eq_sum_range (l : List ℕ) :
    evalBase l = ∑ i ∈ Finset.range l.length, l.getD i 0 * B ^ i := by
  induction l with
  | nil => simp [evalBase]
  | cons x xs ih =>
    simp only [evalBase, List.foldr_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
    have ih' : xs.foldr (fun x acc => x + B * acc) 0 =
        ∑ i ∈ Finset.range xs.length, xs.getD i 0 * B ^ i := ih
    rw [ih', Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ']
    ring

private lemma evalBase_div_pow_mod (l : List ℕ) (hl : ∀ x ∈ l, x < B) (k : ℕ) :
    (evalBase l / B ^ k) % B = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp [evalBase]
  | cons x xs ih =>
    have hx : x < B := hl x (by simp)
    have hxs : ∀ y ∈ xs, y < B := fun y hy => hl y (by simp [hy])
    have hB : 0 < B := by decide
    cases k with
    | zero =>
      simp only [evalBase, List.foldr_cons, pow_zero, Nat.div_one, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ k =>
      simp only [evalBase, List.foldr_cons, List.getD_cons_succ]
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt hx, zero_add]
      exact ih hxs k

private lemma aFlat_len : aFlat.length = m := by
  unfold aFlat m
  rw [List.length_flatten]
  have h1 : aChunks.map List.length = List.replicate aChunks.length 32 := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.getElem_map, List.getElem_replicate]
    have hall := List.all_eq_true.mp cert_a_lens.2
    exact of_decide_eq_true (hall _ (List.getElem_mem (by simpa using hi)))
  rw [h1, List.sum_replicate, smul_eq_mul, cert_a_lens.1]

private lemma bFlat_len : bFlat.length = m := by
  unfold bFlat m
  rw [List.length_flatten]
  have h1 : bChunks.map List.length = List.replicate bChunks.length 32 := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.getElem_map, List.getElem_replicate]
    have hall := List.all_eq_true.mp cert_b_lens.2
    exact of_decide_eq_true (hall _ (List.getElem_mem (by simpa using hi)))
  rw [h1, List.sum_replicate, smul_eq_mul, cert_b_lens.1]

private lemma aFlat_le_D : ∀ x ∈ aFlat, x ≤ D := by
  intro x hx
  rw [aFlat, List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  have h1 := List.all_eq_true.mp cert_a_le l hl
  have h2 := List.all_eq_true.mp h1 x hxl
  exact of_decide_eq_true h2

private lemma cFlat_le_peak : ∀ x ∈ cFlat, x ≤ peak := by
  intro x hx
  rw [cFlat, List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  have h1 := List.all_eq_true.mp cert_bound l hl
  have h2 := List.all_eq_true.mp h1 x hxl
  exact of_decide_eq_true h2

private lemma aFlat_sum : aFlat.sum = 512000 := by
  unfold aFlat
  rw [List.sum_flatten]
  exact cert_a_sum

private lemma bFlat_eq : bFlat = aFlat.reverse.map (fun x => D - x) := by
  unfold bFlat aFlat
  rw [cert_b_eq, List.reverse_flatten, List.map_flatten, List.map_reverse, List.map_reverse, List.map_map]
  rfl

private def aVal (i : ℕ) : ℕ := aFlat.getD i 0
private def bVal (j : ℕ) : ℕ := bFlat.getD j 0

private lemma aVal_le_D (i : ℕ) : aVal i ≤ D := by
  unfold aVal
  by_cases hi : i < aFlat.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact aFlat_le_D _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    exact Nat.zero_le D

private lemma list_getElem_congr {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂)
    {j : ℕ} (h1 : j < l₁.length) (h2 : j < l₂.length) : l₁[j]'h1 = l₂[j]'h2 := by
  subst h; rfl

private lemma list_getElem_idx_congr {α : Type*} (l : List α) {i j : ℕ} (h : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst h; rfl

private lemma bVal_eq (j : ℕ) (hj : j < m) : bVal j = D - aVal (m - 1 - j) := by
  unfold bVal aVal
  have hbl : j < bFlat.length := by rwa [bFlat_len]
  have hal : m - 1 - j < aFlat.length := by rw [aFlat_len]; omega
  rw [List.getD_eq_getElem _ _ hbl, List.getD_eq_getElem _ _ hal]
  have hlen_rm : j < (aFlat.reverse.map (fun x => D - x)).length := by
    rw [List.length_map, List.length_reverse, aFlat_len]; exact hj
  rw [list_getElem_congr bFlat_eq hbl hlen_rm, List.getElem_map, List.getElem_reverse]
  exact congrArg (D - ·) (list_getElem_idx_congr aFlat (i := aFlat.length - 1 - j) (j := m - 1 - j)
    (by rw [aFlat_len]) _ hal)

private lemma bVal_le_D (j : ℕ) : bVal j ≤ D := by
  by_cases hj : j < m
  · rw [bVal_eq j hj]; omega
  · unfold bVal
    rw [List.getD_eq_default _ _ (by rw [bFlat_len]; omega)]
    exact Nat.zero_le D

private def convEntry (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
    if i + j = k then aVal i * bVal j else 0

private lemma convEntry_lt_B (k : ℕ) : convEntry k < B := by
  have hle : convEntry k ≤ m * (D * D) := by
    unfold convEntry
    calc ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i + j = k then aVal i * bVal j else 0)
        ≤ ∑ i ∈ Finset.range m, (D * D) := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases hk : i ≤ k ∧ k - i < m
          · rw [Finset.sum_eq_single (k - i)]
            · have heq : i + (k - i) = k := by omega
              simp only [heq, ↓reduceIte]
              exact Nat.mul_le_mul (aVal_le_D i) (bVal_le_D (k - i))
            · intro j _ hjne
              have : i + j ≠ k := by omega
              simp [this]
            · intro hnot
              exact absurd (Finset.mem_range.mpr hk.2) hnot
          · have hzero : ∀ j ∈ Finset.range m, (if i + j = k then aVal i * bVal j else 0) = 0 := by
              intro j hj
              rw [Finset.mem_range] at hj
              have : i + j ≠ k := by omega
              simp [this]
            rw [Finset.sum_eq_zero hzero]
            exact Nat.zero_le _
      _ = m * (D * D) := by simp
  have hlt : m * (D * D) < B := by decide
  exact Nat.lt_of_le_of_lt hle hlt

private lemma convEntry_le_peak (k : ℕ) (hk : k < 2 * m) : convEntry k ≤ peak := by
  let convList : List ℕ := (List.range (2 * m)).map convEntry
  have hconv_eval : evalBase convList = evalBase aFlat * evalBase bFlat := by
    rw [evalBase_eq_sum_range, evalBase_eq_sum_range, evalBase_eq_sum_range]
    simp only [convList, List.length_map, List.length_range, aFlat_len, bFlat_len]
    rw [Finset.sum_mul]
    have hL :
        (∑ k ∈ Finset.range (2 * m),
          ((List.range (2 * m)).map convEntry).getD k 0 * B ^ k) =
        ∑ k ∈ Finset.range (2 * m), convEntry k * B ^ k := by
      refine Finset.sum_congr rfl fun k hk' => ?_
      rw [Finset.mem_range] at hk'
      rw [List.getD_eq_getElem _ _ (by simpa using hk')]
      simp
    rw [hL]
    have hR :
        (∑ i ∈ Finset.range m, (aFlat.getD i 0 * B ^ i) *
          ∑ j ∈ Finset.range m, bFlat.getD j 0 * B ^ j) =
        ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (aVal i * bVal j) * B ^ (i + j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold aVal bVal
      rw [pow_add]
      ring
    rw [hR]
    trans ∑ k ∈ Finset.range (2 * m), ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (if i + j = k then aVal i * bVal j * B ^ k else 0)
    · refine Finset.sum_congr rfl fun k _ => ?_
      unfold convEntry
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hi hj
      rw [Finset.sum_eq_single (i + j)]
      · simp
      · intro k' _ hk'ne
        simp [Ne.symm hk'ne]
      · intro hnot
        exact absurd (Finset.mem_range.mpr (by omega)) hnot
  have ha_eval : evalChunks aChunks = evalBase aFlat :=
    evalChunks_eq_evalBase_flatten aChunks (fun l hl =>
      of_decide_eq_true (List.all_eq_true.mp cert_a_lens.2 l hl))
  have hb_eval : evalChunks bChunks = evalBase bFlat :=
    evalChunks_eq_evalBase_flatten bChunks (fun l hl =>
      of_decide_eq_true (List.all_eq_true.mp cert_b_lens.2 l hl))
  have hc_eval : evalChunks cChunks = evalBase cFlat :=
    evalChunks_eq_evalBase_flatten cChunks (fun l hl =>
      of_decide_eq_true (List.all_eq_true.mp cert_c_lens.2 l hl))
  have heq : evalBase convList = evalBase cFlat := by
    rw [hconv_eval, ← ha_eval, ← hb_eval, cert_mul, hc_eval]
  have hconv_lt : ∀ x ∈ convList, x < B := by
    intro x hx
    simp only [convList, List.mem_map, List.mem_range] at hx
    obtain ⟨idx, _, rfl⟩ := hx
    exact convEntry_lt_B idx
  have hc_lt : ∀ x ∈ cFlat, x < B := by
    intro x hx
    have h1 := cFlat_le_peak x hx
    have h2 : peak < B := by decide
    exact Nat.lt_of_le_of_lt h1 h2
  have hget : convList.getD k 0 = cFlat.getD k 0 := by
    rw [← evalBase_div_pow_mod convList hconv_lt k, heq, evalBase_div_pow_mod cFlat hc_lt k]
  have hck : convList.getD k 0 = convEntry k := by
    rw [List.getD_eq_getElem _ _ (by simp [convList, hk])]
    simp [convList]
  rw [← hck, hget]
  by_cases hcl : k < cFlat.length
  · rw [List.getD_eq_getElem _ _ hcl]
    exact cFlat_le_peak _ (List.getElem_mem hcl)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hcl)]
    exact Nat.zero_le peak

private noncomputable def hReal (i : Fin m) : ℝ := (aVal i.1 : ℝ) / (D : ℝ)

private noncomputable def C_cert : ℝ := (2 * peak : ℝ) / ((m : ℝ) * (D : ℝ) ^ 2)

private lemma hReal_bounds (i : Fin m) : 0 ≤ hReal i ∧ hReal i ≤ 1 := by
  unfold hReal
  have hD : (0 : ℝ) < (D : ℝ) := by norm_num [D]
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hD.le
  · rw [div_le_one hD]
    exact_mod_cast aVal_le_D i.1

private lemma sum_hReal : ∑ i : Fin m, hReal i = (m : ℝ) / 2 := by
  unfold hReal
  rw [← Finset.sum_div]
  have hsum_nat : (∑ i : Fin m, aVal i.1) = 512000 := by
    rw [← aFlat_sum]
    have h1 : ∀ l : List ℕ, l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.sum_cons, List.length_cons, Finset.sum_range_succ',
          List.getD_cons_zero, List.getD_cons_succ, ih, add_comm]
    rw [h1 aFlat, aFlat_len, Fin.sum_univ_eq_sum_range (fun i => aVal i)]
    rfl
  have hsum_real : (∑ i : Fin m, (aVal i.1 : ℝ)) = 512000 := by exact_mod_cast hsum_nat
  rw [hsum_real]
  norm_num [m, D]

private lemma hReal_corr_le (s : ℤ) :
    (∑ i : Fin m,
      if h : 0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ) then
        hReal i * (1 - hReal ⟨((i.1 : ℤ) - s).toNat, by omega⟩)
      else 0) ≤ (m : ℝ) / 2 * C_cert := by
  have hD : (0 : ℝ) < (D : ℝ) := by norm_num [D]
  have hD2 : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hm_pos : (0 : ℝ) < (m : ℝ) := by norm_num [m]
  have hC : (m : ℝ) / 2 * C_cert = (peak : ℝ) / (D : ℝ) ^ 2 := by
    unfold C_cert
    field_simp
  rw [hC]
  by_cases hs : -(m : ℤ) + 1 ≤ s ∧ s ≤ (m : ℤ) - 1
  · let k : ℕ := ((m : ℤ) - 1 + s).toNat
    have hk : k < 2 * m := by omega
    have hnat_sum :
        (∑ i : Fin m,
          if h : 0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ) then
            aVal i.1 * (D - aVal ((i.1 : ℤ) - s).toNat)
          else 0) = convEntry k := by
      unfold convEntry
      rw [Fin.sum_univ_eq_sum_range
        (fun i => if h : 0 ≤ (i : ℤ) - s ∧ (i : ℤ) - s < (m : ℤ) then
          aVal i * (D - aVal ((i : ℤ) - s).toNat) else 0)]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      by_cases hcond : 0 ≤ (i : ℤ) - s ∧ (i : ℤ) - s < (m : ℤ)
      · rw [dif_pos hcond]
        let j0 : ℕ := m - 1 - ((i : ℤ) - s).toNat
        have hj0 : j0 < m := by omega
        have hij0 : i + j0 = k := by omega
        rw [Finset.sum_eq_single j0]
        · simp only [hij0, ↓reduceIte]
          rw [bVal_eq j0 hj0]
          have hidx : m - 1 - j0 = ((i : ℤ) - s).toNat := by omega
          rw [hidx]
        · intro j _ hjne
          have : i + j ≠ k := by omega
          simp [this]
        · intro hnot
          exact absurd (Finset.mem_range.mpr hj0) hnot
      · rw [dif_neg hcond]
        symm
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_range] at hj
        have : i + j ≠ k := by omega
        simp [this]
    have hreal_eq :
        (∑ i : Fin m,
          if h : 0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ) then
            hReal i * (1 - hReal ⟨((i.1 : ℤ) - s).toNat, by omega⟩)
          else 0) =
        ((∑ i : Fin m,
          if h : 0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ) then
            aVal i.1 * (D - aVal ((i.1 : ℤ) - s).toNat)
          else 0 : ℕ) : ℝ) / (D : ℝ) ^ 2 := by
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hcond : 0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ)
      · rw [dif_pos hcond, dif_pos hcond]
        unfold hReal
        have hle : aVal ((i.1 : ℤ) - s).toNat ≤ D := aVal_le_D _
        rw [Nat.cast_mul, Nat.cast_sub hle]
        field_simp
      · rw [dif_neg hcond, dif_neg hcond]
        simp
    rw [hreal_eq, hnat_sum]
    exact div_le_div_of_nonneg_right (by exact_mod_cast convEntry_le_peak k hk) hD2.le
  · have hzero :
        (∑ i : Fin m,
          if h : 0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ) then
            hReal i * (1 - hReal ⟨((i.1 : ℤ) - s).toNat, by omega⟩)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hnot : ¬ (0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ)) := by
        have := i.2; omega
      rw [dif_neg hnot]
    rw [hzero]
    exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

-- ============================================================================
-- Section 2: Discretized probability profile pN on Fin (2 * N)
-- ============================================================================

private noncomputable def pN (N : ℕ) (x : Fin (2 * N)) : ℝ :=
  let blk := (2 * N) / m
  if hx : x.1 < m * blk then
    hReal ⟨x.1 / blk, Nat.div_lt_of_lt_mul (mul_comm m blk ▸ hx)⟩
  else
    1 / 2

private lemma pN_bounds (N : ℕ) (x : Fin (2 * N)) : 0 ≤ pN N x ∧ pN N x ≤ 1 := by
  unfold pN
  dsimp only
  split_ifs with hx
  · exact hReal_bounds _
  · constructor <;> norm_num

private lemma sum_filter_lt_blk (N : ℕ) (hN : m ≤ 2 * N) (f : Fin (2 * N) → ℝ) :
    let blk := (2 * N) / m
    (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * N) => x.1 < m * blk), f x) =
      ∑ t : Fin blk, ∑ i : Fin m,
        f ⟨i.1 * blk + t.1, by
          have h1 := i.2; have h2 := t.2
          have hmblk : m * blk ≤ 2 * N := Nat.mul_div_le (2 * N) m
          have : i.1 * blk + t.1 < m * blk := by
            calc i.1 * blk + t.1 < i.1 * blk + blk := Nat.add_lt_add_left h2 _
              _ = (i.1 + 1) * blk := by ring
              _ ≤ m * blk := Nat.mul_le_mul_right blk h1
          omega⟩ := by
  intro blk
  have hblk_pos : 0 < blk := Nat.div_pos hN (by decide)
  have hmblk_le : m * blk ≤ 2 * N := Nat.mul_div_le (2 * N) m
  let g : Fin blk × Fin m → ℝ := fun p =>
    f ⟨p.2.1 * blk + p.1.1, by
      have h1 := p.2.2; have h2 := p.1.2
      have : p.2.1 * blk + p.1.1 < m * blk := by
        calc p.2.1 * blk + p.1.1 < p.2.1 * blk + blk := Nat.add_lt_add_left h2 _
          _ = (p.2.1 + 1) * blk := by ring
          _ ≤ m * blk := Nat.mul_le_mul_right blk h1
      omega⟩
  change _ = ∑ t : Fin blk, ∑ i : Fin m, g (t, i)
  rw [← Fintype.sum_prod_type g]
  refine Finset.sum_nbij'
    (fun x => (⟨x.1 % blk, Nat.mod_lt _ hblk_pos⟩,
      if hx : x.1 < m * blk then
        ⟨x.1 / blk, Nat.div_lt_of_lt_mul (mul_comm m blk ▸ hx)⟩
      else ⟨0, by decide⟩))
    (fun p => ⟨p.2.1 * blk + p.1.1, by
      have h1 := p.2.2; have h2 := p.1.2
      have : p.2.1 * blk + p.1.1 < m * blk := by
        calc p.2.1 * blk + p.1.1 < p.2.1 * blk + blk := Nat.add_lt_add_left h2 _
          _ = (p.2.1 + 1) * blk := by ring
          _ ≤ m * blk := Nat.mul_le_mul_right blk h1
      omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := p.2.2; have h2 := p.1.2
    calc p.2.1 * blk + p.1.1 < p.2.1 * blk + blk := Nat.add_lt_add_left h2 _
      _ = (p.2.1 + 1) * blk := by ring
      _ ≤ m * blk := Nat.mul_le_mul_right blk h1
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    ext
    simp only [hx, ↓reduceDIte]
    have := Nat.div_add_mod x.1 blk
    linarith
  · intro p _
    have hlt : p.2.1 * blk + p.1.1 < m * blk := by
      have h1 := p.2.2; have h2 := p.1.2
      calc p.2.1 * blk + p.1.1 < p.2.1 * blk + blk := Nat.add_lt_add_left h2 _
        _ = (p.2.1 + 1) * blk := by ring
        _ ≤ m * blk := Nat.mul_le_mul_right blk h1
    ext
    · simp only
      rw [mul_comm p.2.1 blk, Nat.mul_add_mod, Nat.mod_eq_of_lt p.1.2]
    · simp only [hlt, ↓reduceDIte]
      rw [mul_comm p.2.1 blk, Nat.mul_add_div hblk_pos, Nat.div_eq_of_lt p.1.2, add_zero]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    dsimp only [g]
    congr 1
    ext
    simp only [hx, ↓reduceDIte]
    have := Nat.div_add_mod x.1 blk
    linarith

private lemma sum_pN (N : ℕ) (hN : m ≤ 2 * N) :
    ∑ x : Fin (2 * N), pN N x = (N : ℝ) := by
  let blk := (2 * N) / m
  have hblk_pos : 0 < blk := Nat.div_pos hN (by decide)
  have hmblk_le : m * blk ≤ 2 * N := Nat.mul_div_le (2 * N) m
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (2 * N)))
    (fun x : Fin (2 * N) => x.1 < m * blk) (fun x => pN N x)
  rw [← hsplit]
  have h1 : (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * N) => x.1 < m * blk), pN N x) =
      (blk : ℝ) * ((m : ℝ) / 2) := by
    rw [sum_filter_lt_blk N hN (pN N)]
    have hinner : ∀ (t : Fin blk) (i : Fin m),
        pN N ⟨i.1 * blk + t.1, by
          have h1 := i.2; have h2 := t.2
          have : i.1 * blk + t.1 < m * blk := by
            calc i.1 * blk + t.1 < i.1 * blk + blk := Nat.add_lt_add_left h2 _
              _ = (i.1 + 1) * blk := by ring
              _ ≤ m * blk := Nat.mul_le_mul_right blk h1
          omega⟩ = hReal i := by
      intro t i
      have hlt : i.1 * blk + t.1 < m * blk := by
        have h1 := i.2; have h2 := t.2
        calc i.1 * blk + t.1 < i.1 * blk + blk := Nat.add_lt_add_left h2 _
          _ = (i.1 + 1) * blk := by ring
          _ ≤ m * blk := Nat.mul_le_mul_right blk h1
      unfold pN
      simp only [blk, hlt, ↓reduceDIte]
      congr 1
      ext
      dsimp only
      rw [mul_comm i.1 blk, Nat.mul_add_div hblk_pos, Nat.div_eq_of_lt t.2, add_zero]
    trans ∑ _t : Fin blk, ∑ i : Fin m, hReal i
    · exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => hinner t i
    · simp only [sum_hReal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * N) => ¬ x.1 < m * blk), pN N x) =
      ((2 * N - m * blk : ℕ) : ℝ) * (1 / 2) := by
    have hconst : ∀ x ∈ Finset.univ.filter (fun x : Fin (2 * N) => ¬ x.1 < m * blk),
        pN N x = 1 / 2 := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      unfold pN
      exact dif_neg hx
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard : (Finset.univ.filter (fun x : Fin (2 * N) => ¬ x.1 < m * blk)).card =
        2 * N - m * blk := by
      have hcomp := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (2 * N)))
        (fun x : Fin (2 * N) => x.1 < m * blk) (fun _ => (1 : ℕ))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hcomp
      have hcard_lt : (Finset.univ.filter (fun x : Fin (2 * N) => x.1 < m * blk)).card = m * blk := by
        have hmblk_pos : 0 < m * blk := Nat.mul_pos (by decide) hblk_pos
        trans (Finset.univ : Finset (Fin (m * blk))).card
        · refine Finset.card_nbij'
            (fun x => if hx : x.1 < m * blk then (⟨x.1, hx⟩ : Fin (m * blk)) else ⟨0, hmblk_pos⟩)
            (fun y => (⟨y.1, by have := y.2; omega⟩ : Fin (2 * N))) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro y _; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]; exact y.2
          · intro x hx
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            ext; simp [hx]
          · intro y _
            ext; simp [y.2]
        · simp
      omega
    exact_mod_cast hcard
  rw [h1, h2, Nat.cast_sub hmblk_le]
  push_cast
  ring

private noncomputable def meanOverlap (N : ℕ) (k : ℤ) : ℝ :=
  ∑ x : Fin (2 * N),
    if h : 0 ≤ (x.1 : ℤ) - k ∧ (x.1 : ℤ) - k < (2 * N : ℤ) then
      pN N x * (1 - pN N ⟨((x.1 : ℤ) - k).toNat, by omega⟩)
    else 0

private lemma meanOverlap_le (N : ℕ) (hN : m ≤ 2 * N) (k : ℤ) :
    meanOverlap N k ≤ C_cert * (N : ℝ) + 2 * (m : ℝ) := by
  let blk := (2 * N) / m
  have hblk_pos : 0 < blk := Nat.div_pos hN (by decide)
  have hmblk_le : m * blk ≤ 2 * N := Nat.mul_div_le (2 * N) m
  have hrem_lt : 2 * N - m * blk < m := by
    have h1 := Nat.div_add_mod (2 * N) m
    have h2 := Nat.mod_lt (2 * N) (by decide : 0 < m)
    dsimp only [blk]
    omega
  let term : Fin (2 * N) → ℝ := fun x =>
    if h : 0 ≤ (x.1 : ℤ) - k ∧ (x.1 : ℤ) - k < (2 * N : ℤ) then
      pN N x * (1 - pN N ⟨((x.1 : ℤ) - k).toNat, by omega⟩)
    else 0
  have hterm_le_one : ∀ x : Fin (2 * N), term x ≤ 1 := by
    intro x; dsimp only [term]; split_ifs with h
    · have hp1 := pN_bounds N x
      have hp2 := pN_bounds N ⟨((x.1 : ℤ) - k).toNat, by omega⟩
      nlinarith
    · norm_num
  have hterm_nonneg : ∀ x : Fin (2 * N), 0 ≤ term x := by
    intro x; dsimp only [term]; split_ifs with h
    · have hp1 := pN_bounds N x
      have hp2 := pN_bounds N ⟨((x.1 : ℤ) - k).toNat, by omega⟩
      nlinarith
    · norm_num
  let interior := Finset.univ.filter (fun x : Fin (2 * N) =>
    x.1 < m * blk ∧ 0 ≤ (x.1 : ℤ) - k ∧ (x.1 : ℤ) - k < (m * blk : ℤ))
  have hsplit : meanOverlap N k = (∑ x ∈ interior, term x) + (∑ x ∈ interiorᶜ, term x) := by
    unfold meanOverlap
    rw [Finset.sum_add_sum_compl]
  rw [hsplit]
  have hbdry : ∑ x ∈ interiorᶜ, term x ≤ 2 * (m : ℝ) := by
    let S1 := Finset.univ.filter (fun x : Fin (2 * N) => m * blk ≤ x.1)
    let S2 := Finset.univ.filter (fun x : Fin (2 * N) =>
      (m * blk : ℤ) ≤ (x.1 : ℤ) - k ∧ (x.1 : ℤ) - k < (2 * N : ℤ))
    have hsub : ∀ x ∈ interiorᶜ, term x ≠ 0 → x ∈ S1 ∪ S2 := by
      intro x hx hne
      simp only [Finset.mem_compl, interior, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hcond : 0 ≤ (x.1 : ℤ) - k ∧ (x.1 : ℤ) - k < (2 * N : ℤ) := by
        by_contra hnot
        exact hne (dif_neg hnot)
      rw [Finset.mem_union]
      by_cases h1 : x.1 < m * blk
      · right
        simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, hcond.2⟩
      · left
        simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    have hsum_le : ∑ x ∈ interiorᶜ, term x ≤ ((S1 ∪ S2).card : ℝ) := by
      calc ∑ x ∈ interiorᶜ, term x
          = ∑ x ∈ interiorᶜ.filter (fun x => term x ≠ 0), term x := by
            symm
            exact Finset.sum_filter_of_ne (fun _ _ h => h)
        _ ≤ ∑ x ∈ S1 ∪ S2, term x := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hterm_nonneg x)
            intro x hx
            rw [Finset.mem_filter] at hx
            exact hsub x hx.1 hx.2
        _ ≤ ∑ _x ∈ S1 ∪ S2, (1 : ℝ) := Finset.sum_le_sum fun x _ => hterm_le_one x
        _ = ((S1 ∪ S2).card : ℝ) := by simp
    have hS1 : S1.card ≤ m := by
      have hcard : S1.card ≤ (Finset.range (2 * N - m * blk)).card := by
        refine Finset.card_le_card_of_injOn (fun x => x.1 - m * blk) ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have := x.2
          simp only [Finset.coe_range, Set.mem_Iio]; omega
        · intro x hx y hy heq
          simp only [Finset.mem_coe, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
          dsimp only at heq
          have := x.2; have := y.2
          ext; omega
      rw [Finset.card_range] at hcard; omega
    have hS2 : S2.card ≤ m := by
      have hcard : S2.card ≤ (Finset.range (2 * N - m * blk)).card := by
        refine Finset.card_le_card_of_injOn
          (fun x => ((x.1 : ℤ) - k - (m * blk : ℤ)).toNat) ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have := x.2
          simp only [Finset.coe_range, Set.mem_Iio]; omega
        · intro x hx y hy heq
          simp only [Finset.mem_coe, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
          dsimp only at heq
          have := x.2; have := y.2
          ext; omega
      rw [Finset.card_range] at hcard; omega
    have hunion : (S1 ∪ S2).card ≤ 2 * m := by
      calc (S1 ∪ S2).card ≤ S1.card + S2.card := Finset.card_union_le S1 S2
        _ ≤ m + m := Nat.add_le_add hS1 hS2
        _ = 2 * m := by ring
    exact le_trans hsum_le (by exact_mod_cast hunion)
  have hint : ∑ x ∈ interior, term x ≤ C_cert * (N : ℝ) := by
    let intTerm : Fin (2 * N) → ℝ := fun x =>
      if h : 0 ≤ (x.1 : ℤ) - k ∧ (x.1 : ℤ) - k < (m * blk : ℤ) then term x else 0
    have hint_eq : ∑ x ∈ interior, term x =
        ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * N) => x.1 < m * blk), intTerm x := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only [intTerm]
      by_cases h1 : x.1 < m * blk
      · by_cases h2 : 0 ≤ (x.1 : ℤ) - k ∧ (x.1 : ℤ) - k < (m * blk : ℤ)
        · simp [h1, h2]
        · simp [h1]
      · simp [h1]
    rw [hint_eq, sum_filter_lt_blk N hN intTerm]
    let s : ℤ := k / (blk : ℤ)
    let r : ℕ := (k % (blk : ℤ)).toNat
    have hr_lt : r < blk := by
      have h1 := Int.emod_nonneg k (by omega : (blk : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < (blk : ℤ))
      omega
    have hk_eq : k = s * (blk : ℤ) + (r : ℤ) := by
      have h1 := Int.emod_nonneg k (by omega : (blk : ℤ) ≠ 0)
      have h2 := Int.ediv_mul_add_emod k (blk : ℤ)
      dsimp only [s, r]
      omega
    have hblk_int : (0 : ℤ) < (blk : ℤ) := by omega
    have hper_t : ∀ t : Fin blk,
        (∑ i : Fin m, intTerm ⟨i.1 * blk + t.1, by
          have h1 := i.2; have h2 := t.2
          have : i.1 * blk + t.1 < m * blk := by
            calc i.1 * blk + t.1 < i.1 * blk + blk := Nat.add_lt_add_left h2 _
              _ = (i.1 + 1) * blk := by ring
              _ ≤ m * blk := Nat.mul_le_mul_right blk h1
          omega⟩) ≤ (m : ℝ) / 2 * C_cert := by
      intro t
      by_cases htr : r ≤ t.1
      · refine le_trans (le_of_eq ?_) (hReal_corr_le s)
        refine Finset.sum_congr rfl fun i _ => ?_
        have hlt_x : i.1 * blk + t.1 < m * blk := by
          have h1 := i.2; have h2 := t.2
          calc i.1 * blk + t.1 < i.1 * blk + blk := Nat.add_lt_add_left h2 _
            _ = (i.1 + 1) * blk := by ring
            _ ≤ m * blk := Nat.mul_le_mul_right blk h1
        have hdiff_eq : ((i.1 * blk + t.1 : ℕ) : ℤ) - k =
            ((i.1 : ℤ) - s) * (blk : ℤ) + ((t.1 - r : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub htr]; rw [hk_eq]; ring
        have htr_int : (0 : ℤ) ≤ ((t.1 - r : ℕ) : ℤ) ∧ ((t.1 - r : ℕ) : ℤ) < (blk : ℤ) := by
          have := t.2; omega
        have hiff : (0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
            ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (m * blk : ℤ)) ↔
            (0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ)) := by
          rw [hdiff_eq]
          constructor
          · intro ⟨hlo, hhi⟩
            constructor
            · by_contra hneg; push Not at hneg
              have : ((i.1 : ℤ) - s) ≤ -1 := by omega
              nlinarith
            · by_contra hbig; push Not at hbig
              nlinarith
          · intro ⟨hlo, hhi⟩
            constructor
            · nlinarith
            · have : ((i.1 : ℤ) - s) ≤ (m : ℤ) - 1 := by omega
              nlinarith
        dsimp only [intTerm, term]
        by_cases hc : 0 ≤ (i.1 : ℤ) - s ∧ (i.1 : ℤ) - s < (m : ℤ)
        · have hc1 : 0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
              ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (m * blk : ℤ) := hiff.mpr hc
          have hc2 : 0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
              ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (2 * N : ℤ) := ⟨hc1.1, by omega⟩
          rw [dif_pos hc1, dif_pos hc2, dif_pos hc]
          have hp1 : pN N ⟨i.1 * blk + t.1, by omega⟩ = hReal i := by
            unfold pN; simp only [blk, hlt_x, ↓reduceDIte]
            congr 1; ext; dsimp only
            rw [mul_comm i.1 blk, Nat.mul_add_div hblk_pos, Nat.div_eq_of_lt t.2, add_zero]
          have hlt_y : (((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat < m * blk := by omega
          have hdiv_y : (((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat / blk = ((i.1 : ℤ) - s).toNat := by
            have hy_eq : (((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat =
                ((i.1 : ℤ) - s).toNat * blk + (t.1 - r) := by
              exact Int.ofNat_inj.mp (by
                rw [Int.toNat_of_nonneg hc1.1, hdiff_eq]
                push_cast
                rw [Int.toNat_of_nonneg hc.1])
            rw [hy_eq, mul_comm _ blk, Nat.mul_add_div hblk_pos,
              Nat.div_eq_of_lt (by have := t.2; omega : t.1 - r < blk), add_zero]
          have hp2 : pN N ⟨(((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat, by omega⟩ =
              hReal ⟨((i.1 : ℤ) - s).toNat, by omega⟩ := by
            unfold pN; simp only [blk, hlt_y, ↓reduceDIte]
            congr 1; ext; exact hdiv_y
          rw [hp1, hp2]
        · have hc1 : ¬ (0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
              ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (m * blk : ℤ)) := fun h => hc (hiff.mp h)
          rw [dif_neg hc1, dif_neg hc]
      · refine le_trans (le_of_eq ?_) (hReal_corr_le (s + 1))
        refine Finset.sum_congr rfl fun i _ => ?_
        have hlt_x : i.1 * blk + t.1 < m * blk := by
          have h1 := i.2; have h2 := t.2
          calc i.1 * blk + t.1 < i.1 * blk + blk := Nat.add_lt_add_left h2 _
            _ = (i.1 + 1) * blk := by ring
            _ ≤ m * blk := Nat.mul_le_mul_right blk h1
        have hrem_pos : blk + t.1 - r < blk := by omega
        have hdiff_eq : ((i.1 * blk + t.1 : ℕ) : ℤ) - k =
            ((i.1 : ℤ) - (s + 1)) * (blk : ℤ) + ((blk + t.1 - r : ℕ) : ℤ) := by
          have hle_r : r ≤ blk + t.1 := by omega
          push_cast [Nat.cast_sub hle_r]; rw [hk_eq]; ring
        have htr_int : (0 : ℤ) ≤ ((blk + t.1 - r : ℕ) : ℤ) ∧
            ((blk + t.1 - r : ℕ) : ℤ) < (blk : ℤ) := by omega
        have hiff : (0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
            ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (m * blk : ℤ)) ↔
            (0 ≤ (i.1 : ℤ) - (s + 1) ∧ (i.1 : ℤ) - (s + 1) < (m : ℤ)) := by
          rw [hdiff_eq]
          constructor
          · intro ⟨hlo, hhi⟩
            constructor
            · by_contra hneg; push Not at hneg
              have : ((i.1 : ℤ) - (s + 1)) ≤ -1 := by omega
              nlinarith
            · by_contra hbig; push Not at hbig
              nlinarith
          · intro ⟨hlo, hhi⟩
            constructor
            · nlinarith
            · have : ((i.1 : ℤ) - (s + 1)) ≤ (m : ℤ) - 1 := by omega
              nlinarith
        dsimp only [intTerm, term]
        by_cases hc : 0 ≤ (i.1 : ℤ) - (s + 1) ∧ (i.1 : ℤ) - (s + 1) < (m : ℤ)
        · have hc1 : 0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
              ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (m * blk : ℤ) := hiff.mpr hc
          have hc2 : 0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
              ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (2 * N : ℤ) := ⟨hc1.1, by omega⟩
          rw [dif_pos hc1, dif_pos hc2, dif_pos hc]
          have hp1 : pN N ⟨i.1 * blk + t.1, by omega⟩ = hReal i := by
            unfold pN; simp only [blk, hlt_x, ↓reduceDIte]
            congr 1; ext; dsimp only
            rw [mul_comm i.1 blk, Nat.mul_add_div hblk_pos, Nat.div_eq_of_lt t.2, add_zero]
          have hlt_y : (((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat < m * blk := by omega
          have hdiv_y : (((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat / blk =
              ((i.1 : ℤ) - (s + 1)).toNat := by
            have hy_eq : (((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat =
                ((i.1 : ℤ) - (s + 1)).toNat * blk + (blk + t.1 - r) := by
              exact Int.ofNat_inj.mp (by
                rw [Int.toNat_of_nonneg hc1.1, hdiff_eq]
                push_cast
                rw [Int.toNat_of_nonneg hc.1])
            rw [hy_eq, mul_comm _ blk, Nat.mul_add_div hblk_pos,
              Nat.div_eq_of_lt hrem_pos, add_zero]
          have hp2 : pN N ⟨(((i.1 * blk + t.1 : ℕ) : ℤ) - k).toNat, by omega⟩ =
              hReal ⟨((i.1 : ℤ) - (s + 1)).toNat, by omega⟩ := by
            unfold pN; simp only [blk, hlt_y, ↓reduceDIte]
            congr 1; ext; exact hdiv_y
          rw [hp1, hp2]
        · have hc1 : ¬ (0 ≤ ((i.1 * blk + t.1 : ℕ) : ℤ) - k ∧
              ((i.1 * blk + t.1 : ℕ) : ℤ) - k < (m * blk : ℤ)) := fun h => hc (hiff.mp h)
          rw [dif_neg hc1, dif_neg hc]
    calc (∑ t : Fin blk, ∑ i : Fin m, intTerm ⟨i.1 * blk + t.1, _⟩)
        ≤ ∑ _t : Fin blk, ((m : ℝ) / 2 * C_cert) := Finset.sum_le_sum fun t _ => hper_t t
      _ = (blk : ℝ) * ((m : ℝ) / 2 * C_cert) := by simp
      _ = ((m * blk : ℕ) : ℝ) / 2 * C_cert := by push_cast; ring
      _ ≤ ((2 * N : ℕ) : ℝ) / 2 * C_cert := by
          have hC_nn : 0 ≤ C_cert := by unfold C_cert; exact div_nonneg (by positivity) (by positivity)
          gcongr
      _ = C_cert * (N : ℝ) := by push_cast; ring
  linarith

-- ============================================================================
-- Section 3: Finite product probability space on Conf M = (Fin M -> Bool)
-- ============================================================================

private abbrev Conf (M : ℕ) := Fin M → Bool

private def wt {M : ℕ} (p : Fin M → ℝ) (S : Conf M) : ℝ :=
  ∏ x : Fin M, if S x then p x else 1 - p x

private def exp {M : ℕ} (p : Fin M → ℝ) (f : Conf M → ℝ) : ℝ :=
  ∑ S : Conf M, wt p S * f S

private lemma wt_nonneg {M : ℕ} (p : Fin M → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (S : Conf M) :
    0 ≤ wt p S := by
  unfold wt
  refine Finset.prod_nonneg fun x _ => ?_
  have := hp x
  cases S x <;> simp <;> linarith

private lemma sum_wt_gen {α : Type*} [Fintype α] [DecidableEq α] (q : α → ℝ) :
    ∑ S : α → Bool, ∏ x : α, (if S x then q x else 1 - q x) = 1 := by
  rw [← Fintype.prod_sum (fun x (b : Bool) => if b then q x else 1 - q x)]
  simp

private lemma sum_wt {M : ℕ} (p : Fin M → ℝ) : ∑ S : Conf M, wt p S = 1 :=
  sum_wt_gen p

private lemma exp_const {M : ℕ} (p : Fin M → ℝ) (c : ℝ) : exp p (fun _ => c) = c := by
  unfold exp
  rw [← Finset.sum_mul, sum_wt, one_mul]

private lemma exp_add {M : ℕ} (p : Fin M → ℝ) (f g : Conf M → ℝ) :
    exp p (fun S => f S + g S) = exp p f + exp p g := by
  unfold exp
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

private lemma exp_sub {M : ℕ} (p : Fin M → ℝ) (f g : Conf M → ℝ) :
    exp p (fun S => f S - g S) = exp p f - exp p g := by
  unfold exp
  simp_rw [mul_sub]
  exact Finset.sum_sub_distrib (f := fun S => wt p S * f S) (g := fun S => wt p S * g S)

private lemma exp_smul {M : ℕ} (p : Fin M → ℝ) (c : ℝ) (f : Conf M → ℝ) :
    exp p (fun S => c * f S) = c * exp p f := by
  unfold exp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

private lemma exp_sum {M : ℕ} {ι : Type*} (p : Fin M → ℝ) (s : Finset ι) (f : ι → Conf M → ℝ) :
    exp p (fun S => ∑ i ∈ s, f i S) = ∑ i ∈ s, exp p (f i) := by
  unfold exp
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private lemma exp_mono {M : ℕ} (p : Fin M → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (f g : Conf M → ℝ) (hfg : ∀ S, f S ≤ g S) : exp p f ≤ exp p g := by
  unfold exp
  refine Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hfg S) (wt_nonneg p hp S)

private lemma exp_le_const {M : ℕ} (p : Fin M → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (f : Conf M → ℝ) (c : ℝ) (hf : ∀ S, f S ≤ c) : exp p f ≤ c := by
  calc exp p f ≤ exp p (fun _ => c) := exp_mono p hp f (fun _ => c) hf
    _ = c := exp_const p c

private lemma exists_lt_of_exp_lt {M : ℕ} (p : Fin M → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (f : Conf M → ℝ) (c : ℝ) (h : exp p f < c) : ∃ S : Conf M, f S < c := by
  by_contra hall
  push Not at hall
  have hge : c ≤ exp p f := by
    calc c = exp p (fun _ => c) := (exp_const p c).symm
      _ ≤ exp p f := exp_mono p hp (fun _ => c) f hall
  linarith

private lemma exp_mul_of_disjoint {M : ℕ} (p : Fin M → ℝ)
    (T₁ T₂ : Finset (Fin M)) (hdisj : Disjoint T₁ T₂)
    (f g : Conf M → ℝ)
    (hf : ∀ S₁ S₂, (∀ x ∈ T₁, S₁ x = S₂ x) → f S₁ = f S₂)
    (hg : ∀ S₁ S₂, (∀ x ∈ T₂, S₁ x = S₂ x) → g S₁ = g S₂) :
    exp p (fun S => f S * g S) = exp p f * exp p g := by
  let e : Conf M ≃ ({x : Fin M // x ∈ T₁} → Bool) × ({x : Fin M // x ∉ T₁} → Bool) :=
    Equiv.piEquivPiSubtypeProd (fun x : Fin M => x ∈ T₁) (fun _ => Bool)
  let w₁ : ({x : Fin M // x ∈ T₁} → Bool) → ℝ :=
    fun u => ∏ x : {x : Fin M // x ∈ T₁}, if u x then p x.1 else 1 - p x.1
  let w₂ : ({x : Fin M // x ∉ T₁} → Bool) → ℝ :=
    fun v => ∏ x : {x : Fin M // x ∉ T₁}, if v x then p x.1 else 1 - p x.1
  have hw_split : ∀ u v, wt p (e.symm (u, v)) = w₁ u * w₂ v := by
    intro u v
    unfold wt
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun x : Fin M => x ∈ T₁)]
    dsimp only [w₁, w₂]
    congr 1
    · convert Fintype.prod_congr
        (fun x : {x : Fin M // x ∈ T₁} => if (e.symm (u, v)) x.1 then p x.1 else 1 - p x.1)
        (fun x : {x : Fin M // x ∈ T₁} => if u x then p x.1 else 1 - p x.1)
        (fun x => by
          have h1 : (e.symm (u, v)) x.1 = u x :=
            congrFun (congrArg Prod.fst (e.apply_symm_apply (u, v))) x
          rw [h1])
    · convert Fintype.prod_congr
        (fun x : {x : Fin M // x ∉ T₁} => if (e.symm (u, v)) x.1 then p x.1 else 1 - p x.1)
        (fun x : {x : Fin M // x ∉ T₁} => if v x then p x.1 else 1 - p x.1)
        (fun x => by
          have h2 : (e.symm (u, v)) x.1 = v x :=
            congrFun (congrArg Prod.snd (e.apply_symm_apply (u, v))) x
          rw [h2])
  have hw₁_sum : ∑ u, w₁ u = 1 := sum_wt_gen (fun x : {x : Fin M // x ∈ T₁} => p x.1)
  have hw₂_sum : ∑ v, w₂ v = 1 := sum_wt_gen (fun x : {x : Fin M // x ∉ T₁} => p x.1)
  let f' : ({x : Fin M // x ∈ T₁} → Bool) → ℝ := fun u => f (e.symm (u, fun _ => false))
  let g' : ({x : Fin M // x ∉ T₁} → Bool) → ℝ := fun v => g (e.symm (fun _ => false, v))
  have hf_eq : ∀ u v, f (e.symm (u, v)) = f' u := by
    intro u v
    apply hf
    intro x hx
    have h1 : (e.symm (u, v)) x = u ⟨x, hx⟩ :=
      congrFun (congrArg Prod.fst (e.apply_symm_apply (u, v))) ⟨x, hx⟩
    have h2 : (e.symm (u, fun _ => false)) x = u ⟨x, hx⟩ :=
      congrFun (congrArg Prod.fst (e.apply_symm_apply (u, fun _ => false))) ⟨x, hx⟩
    rw [h1, h2]
  have hg_eq : ∀ u v, g (e.symm (u, v)) = g' v := by
    intro u v
    apply hg
    intro x hx
    have hx1 : x ∉ T₁ := Finset.disjoint_right.mp hdisj hx
    have h1 : (e.symm (u, v)) x = v ⟨x, hx1⟩ :=
      congrFun (congrArg Prod.snd (e.apply_symm_apply (u, v))) ⟨x, hx1⟩
    have h2 : (e.symm (fun _ => false, v)) x = v ⟨x, hx1⟩ :=
      congrFun (congrArg Prod.snd (e.apply_symm_apply (fun _ => false, v))) ⟨x, hx1⟩
    rw [h1, h2]
  have hfg_sum : exp p (fun S => f S * g S) = (∑ u, w₁ u * f' u) * (∑ v, w₂ v * g' v) := by
    unfold exp
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    simp_rw [hw_split, hf_eq, hg_eq]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have hf_sum : exp p f = ∑ u, w₁ u * f' u := by
    unfold exp
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    simp_rw [hw_split, hf_eq]
    have : (∑ u, ∑ v, w₁ u * w₂ v * f' u) = (∑ u, w₁ u * f' u) * (∑ v, w₂ v) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    rw [this, hw₂_sum, mul_one]
  have hg_sum : exp p g = ∑ v, w₂ v * g' v := by
    unfold exp
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    simp_rw [hw_split, hg_eq]
    have : (∑ u, ∑ v, w₁ u * w₂ v * g' v) = (∑ u, w₁ u) * (∑ v, w₂ v * g' v) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    rw [this, hw₁_sum, one_mul]
  rw [hfg_sum, hf_sum, hg_sum]

private lemma exp_single_bool {M : ℕ} (p : Fin M → ℝ) (x : Fin M) (h : Bool → ℝ) :
    exp p (fun S => h (S x)) = p x * h true + (1 - p x) * h false := by
  unfold exp wt
  have h1 : ∀ S : Conf M,
      (∏ y : Fin M, if S y then p y else 1 - p y) * h (S x) =
      ∏ y : Fin M, (if S y then p y else 1 - p y) * (if y = x then h (S y) else 1) := by
    intro S
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ x (fun y => h (S y))]
    simp
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun y (b : Bool) => (if b then p y else 1 - p y) * (if y = x then h b else 1))]
  rw [Finset.prod_eq_single x]
  · simp
  · intro y _ hyx
    simp [hyx]
  · intro hx; exact absurd (Finset.mem_univ x) hx

private lemma exp_ind_true {M : ℕ} (p : Fin M → ℝ) (x : Fin M) :
    exp p (fun S => if S x then (1 : ℝ) else 0) = p x := by
  have := exp_single_bool p x (fun b => if b then (1 : ℝ) else 0)
  simpa using this

private lemma exp_ind_false {M : ℕ} (p : Fin M → ℝ) (x : Fin M) :
    exp p (fun S => if S x then (0 : ℝ) else 1) = 1 - p x := by
  have := exp_single_bool p x (fun b => if b then (0 : ℝ) else 1)
  simpa using this

-- ============================================================================
-- Section 4: 2nd-moment and 4th-moment bounds
-- ============================================================================

private lemma exp_sq_sum_centered_le {M : ℕ} (p : Fin M → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    exp p (fun S => (∑ x : Fin M, ((if S x then (1 : ℝ) else 0) - p x)) ^ 2) ≤ (M : ℝ) := by
  let X : Fin M → Conf M → ℝ := fun x S => (if S x then (1 : ℝ) else 0) - p x
  have hmean : ∀ x, exp p (X x) = 0 := by
    intro x
    dsimp only [X]
    rw [exp_sub, exp_ind_true, exp_const, sub_self]
  have hsq : ∀ S, (∑ x : Fin M, X x S) ^ 2 = ∑ x : Fin M, ∑ y : Fin M, X x S * X y S := by
    intro S
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
  simp_rw [show (fun S => (∑ x : Fin M, ((if S x then (1 : ℝ) else 0) - p x)) ^ 2) =
      (fun S => ∑ x : Fin M, ∑ y : Fin M, X x S * X y S) from funext hsq]
  rw [exp_sum]
  calc ∑ x : Fin M, exp p (fun S => ∑ y : Fin M, X x S * X y S)
      = ∑ x : Fin M, ∑ y : Fin M, exp p (fun S => X x S * X y S) := by
        refine Finset.sum_congr rfl fun x _ => exp_sum p _ _
    _ ≤ ∑ x : Fin M, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · refine exp_le_const p hp _ 1 fun S => ?_
          have hpx := hp x
          dsimp only [X]
          cases S x <;> simp <;> nlinarith
        · intro y _ hyx
          have hmul := exp_mul_of_disjoint p {x} {y}
            (Finset.disjoint_singleton.mpr (Ne.symm hyx)) (X x) (X y)
            (fun S₁ S₂ h => by dsimp only [X]; rw [h x (by simp)])
            (fun S₁ S₂ h => by dsimp only [X]; rw [h y (by simp)])
          rw [hmul, hmean x, zero_mul]
        · intro hx; exact absurd (Finset.mem_univ x) hx
    _ = (M : ℝ) := by simp

private lemma exp_pow_four_sum_le {M : ℕ} {ι : Type*} [DecidableEq ι]
    (p : Fin M → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (J : Finset ι) (Y : ι → Conf M → ℝ) (supp : ι → Finset (Fin M))
    (hsupp : ∀ i ∈ J, ∀ S₁ S₂, (∀ x ∈ supp i, S₁ x = S₂ x) → Y i S₁ = Y i S₂)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (supp i) (supp j))
    (hmean : ∀ i ∈ J, exp p (Y i) = 0)
    (hbdd : ∀ i ∈ J, ∀ S, |Y i S| ≤ 1) :
    exp p (fun S => (∑ i ∈ J, Y i S) ^ 4) ≤ 3 * (J.card : ℝ) ^ 2 := by
  have hexp4 : ∀ S, (∑ i ∈ J, Y i S) ^ 4 =
      ∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J, Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S := by
    intro S
    rw [show (∑ i ∈ J, Y i S) ^ 4 =
      (∑ i ∈ J, Y i S) * ((∑ i ∈ J, Y i S) * ((∑ i ∈ J, Y i S) * (∑ i ∈ J, Y i S))) by ring]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₂ _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₃ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₄ _ => ?_
    ring
  simp_rw [show (fun S => (∑ i ∈ J, Y i S) ^ 4) =
      (fun S => ∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J, Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S)
      from funext hexp4]
  rw [exp_sum]
  have hswap :
      (∑ i₁ ∈ J, exp p (fun S => ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J, Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S)) =
      ∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J, exp p (fun S => Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S) := by
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    rw [exp_sum]
    refine Finset.sum_congr rfl fun i₂ _ => ?_
    rw [exp_sum]
    refine Finset.sum_congr rfl fun i₃ _ => ?_
    rw [exp_sum]
  rw [hswap]
  have hsingle_zero : ∀ a b c d, a ∈ J → b ∈ J → c ∈ J → d ∈ J →
      a ≠ b → a ≠ c → a ≠ d →
      exp p (fun S => Y a S * (Y b S * Y c S * Y d S)) = 0 := by
    intro a b c d ha hb hc hd hab hac had
    have hd_u : Disjoint (supp a) (supp b ∪ (supp c ∪ supp d)) :=
      Finset.disjoint_union_right.mpr
        ⟨hdisj a ha b hb hab,
         Finset.disjoint_union_right.mpr ⟨hdisj a ha c hc hac, hdisj a ha d hd had⟩⟩
    have hdep : ∀ S₁ S₂, (∀ x ∈ supp b ∪ (supp c ∪ supp d), S₁ x = S₂ x) →
        Y b S₁ * Y c S₁ * Y d S₁ = Y b S₂ * Y c S₂ * Y d S₂ := by
      intro S₁ S₂ hS
      rw [hsupp b hb S₁ S₂ (fun x hx => hS x (by simp [hx])),
          hsupp c hc S₁ S₂ (fun x hx => hS x (by simp [hx])),
          hsupp d hd S₁ S₂ (fun x hx => hS x (by simp [hx]))]
    rw [exp_mul_of_disjoint p (supp a) (supp b ∪ (supp c ∪ supp d)) hd_u
      (Y a) (fun S => Y b S * Y c S * Y d S) (hsupp a ha) hdep, hmean a ha, zero_mul]
  have hterm_le : ∀ i₁ ∈ J, ∀ i₂ ∈ J, ∀ i₃ ∈ J, ∀ i₄ ∈ J,
      exp p (fun S => Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S) ≤
        (if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
        (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
        (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0) := by
    intro i₁ h1 i₂ h2 i₃ h3 i₄ h4
    by_cases hpair : (i₁ = i₂ ∧ i₃ = i₄) ∨ (i₁ = i₃ ∧ i₂ = i₄) ∨ (i₁ = i₄ ∧ i₂ = i₃)
    · have hexp_le1 : exp p (fun S => Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S) ≤ 1 := by
        refine exp_le_const p hp _ 1 fun S => ?_
        have habs : |Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S| ≤ 1 := by
          rw [abs_mul, abs_mul, abs_mul]
          have b1 := hbdd i₁ h1 S; have b2 := hbdd i₂ h2 S
          have b3 := hbdd i₃ h3 S; have b4 := hbdd i₄ h4 S
          have a1 := abs_nonneg (Y i₁ S); have a2 := abs_nonneg (Y i₂ S)
          have a3 := abs_nonneg (Y i₃ S); have a4 := abs_nonneg (Y i₄ S)
          have p12 : |Y i₁ S| * |Y i₂ S| ≤ 1 := by nlinarith
          have p123 : |Y i₁ S| * |Y i₂ S| * |Y i₃ S| ≤ 1 := by nlinarith
          nlinarith
        exact (abs_le.mp habs).2
      have hrhs_ge1 : (1 : ℝ) ≤
          (if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
          (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
          (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0) := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> split_ifs <;> norm_num
      exact le_trans hexp_le1 hrhs_ge1
    · have hrhs_nn : 0 ≤
          (if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
          (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
          (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0) := by positivity
      have hzero : exp p (fun S => Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S) = 0 := by
        by_cases h12 : i₁ = i₂
        · subst h12
          have h34 : i₃ ≠ i₄ := fun h => hpair (Or.inl ⟨rfl, h⟩)
          by_cases h13 : i₁ = i₃
          · subst h13
            have h41 : i₄ ≠ i₁ := Ne.symm h34
            have hrew : (fun S => Y i₁ S * Y i₁ S * Y i₁ S * Y i₄ S) =
                (fun S => Y i₄ S * (Y i₁ S * Y i₁ S * Y i₁ S)) := funext fun S => by ring
            rw [hrew]
            exact hsingle_zero i₄ i₁ i₁ i₁ h4 h1 h1 h1 h41 h41 h41
          · have h31 : i₃ ≠ i₁ := Ne.symm h13
            have hrew : (fun S => Y i₁ S * Y i₁ S * Y i₃ S * Y i₄ S) =
                (fun S => Y i₃ S * (Y i₁ S * Y i₁ S * Y i₄ S)) := funext fun S => by ring
            rw [hrew]
            exact hsingle_zero i₃ i₁ i₁ i₄ h3 h1 h1 h4 h31 h31 h34
        · by_cases h13 : i₁ = i₃
          · subst h13
            have h24 : i₂ ≠ i₄ := fun h => hpair (Or.inr (Or.inl ⟨rfl, h⟩))
            by_cases h14 : i₁ = i₄
            · subst h14
              have h21 : i₂ ≠ i₁ := Ne.symm h12
              have hrew : (fun S => Y i₁ S * Y i₂ S * Y i₁ S * Y i₁ S) =
                  (fun S => Y i₂ S * (Y i₁ S * Y i₁ S * Y i₁ S)) := funext fun S => by ring
              rw [hrew]
              exact hsingle_zero i₂ i₁ i₁ i₁ h2 h1 h1 h1 h21 h21 h21
            · have h41 : i₄ ≠ i₁ := Ne.symm h14
              have h42 : i₄ ≠ i₂ := Ne.symm h24
              have hrew : (fun S => Y i₁ S * Y i₂ S * Y i₁ S * Y i₄ S) =
                  (fun S => Y i₄ S * (Y i₁ S * Y i₂ S * Y i₁ S)) := funext fun S => by ring
              rw [hrew]
              exact hsingle_zero i₄ i₁ i₂ i₁ h4 h1 h2 h1 h41 h42 h41
          · by_cases h14 : i₁ = i₄
            · subst h14
              have h23 : i₂ ≠ i₃ := fun h => hpair (Or.inr (Or.inr ⟨rfl, h⟩))
              have h21 : i₂ ≠ i₁ := Ne.symm h12
              have hrew : (fun S => Y i₁ S * Y i₂ S * Y i₃ S * Y i₁ S) =
                  (fun S => Y i₂ S * (Y i₁ S * Y i₃ S * Y i₁ S)) := funext fun S => by ring
              rw [hrew]
              exact hsingle_zero i₂ i₁ i₃ i₁ h2 h1 h3 h1 h21 h23 h21
            · have hrew : (fun S => Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S) =
                  (fun S => Y i₁ S * (Y i₂ S * Y i₃ S * Y i₄ S)) := funext fun S => by ring
              rw [hrew]
              exact hsingle_zero i₁ i₂ i₃ i₄ h1 h2 h3 h4 h12 h13 h14
      rw [hzero]
      exact hrhs_nn
  calc ∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J,
        exp p (fun S => Y i₁ S * Y i₂ S * Y i₃ S * Y i₄ S)
      ≤ ∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J,
        ((if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
         (if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
         (if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun i₁ h1 => Finset.sum_le_sum fun i₂ h2 =>
          Finset.sum_le_sum fun i₃ h3 => Finset.sum_le_sum fun i₄ h4 =>
            hterm_le i₁ h1 i₂ h2 i₃ h3 i₄ h4
    _ = (∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J, if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) +
        (∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J, if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) +
        (∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J, if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0) := by
        simp_rw [Finset.sum_add_distrib]
    _ = (J.card : ℝ) ^ 2 + (J.card : ℝ) ^ 2 + (J.card : ℝ) ^ 2 := by
        have hsum1 : (∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J,
            if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) = (J.card : ℝ) ^ 2 := by
          have : ∀ i₁ ∈ J, (∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J,
              if i₁ = i₂ ∧ i₃ = i₄ then (1 : ℝ) else 0) = (J.card : ℝ) := by
            intro i₁ h1
            rw [Finset.sum_eq_single i₁]
            · simp only [true_and]
              have : ∀ i₃ ∈ J, (∑ i₄ ∈ J, if i₃ = i₄ then (1 : ℝ) else 0) = 1 := by
                intro i₃ h3
                rw [Finset.sum_eq_single i₃]
                · simp
                · intro i₄ _ hne; simp [Ne.symm hne]
                · intro hnot; exact absurd h3 hnot
              rw [Finset.sum_congr rfl this]; simp
            · intro i₂ _ hne; simp [Ne.symm hne]
            · intro hnot; exact absurd h1 hnot
          rw [Finset.sum_congr rfl this]; simp [sq]
        have hsum2 : (∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J,
            if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) = (J.card : ℝ) ^ 2 := by
          have : ∀ i₁ ∈ J, ∀ i₂ ∈ J, (∑ i₃ ∈ J, ∑ i₄ ∈ J,
              if i₁ = i₃ ∧ i₂ = i₄ then (1 : ℝ) else 0) = 1 := by
            intro i₁ h1 i₂ h2
            rw [Finset.sum_eq_single i₁]
            · simp only [true_and]
              rw [Finset.sum_eq_single i₂]
              · simp
              · intro i₄ _ hne; simp [Ne.symm hne]
              · intro hnot; exact absurd h2 hnot
            · intro i₃ _ hne; simp [Ne.symm hne]
            · intro hnot; exact absurd h1 hnot
          trans ∑ i₁ ∈ J, ∑ i₂ ∈ J, (1 : ℝ)
          · exact Finset.sum_congr rfl fun i₁ h1 => Finset.sum_congr rfl fun i₂ h2 => this i₁ h1 i₂ h2
          · simp [sq]
        have hsum3 : (∑ i₁ ∈ J, ∑ i₂ ∈ J, ∑ i₃ ∈ J, ∑ i₄ ∈ J,
            if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0) = (J.card : ℝ) ^ 2 := by
          have : ∀ i₁ ∈ J, ∀ i₂ ∈ J, (∑ i₃ ∈ J, ∑ i₄ ∈ J,
              if i₁ = i₄ ∧ i₂ = i₃ then (1 : ℝ) else 0) = 1 := by
            intro i₁ h1 i₂ h2
            rw [Finset.sum_eq_single i₂]
            · rw [Finset.sum_eq_single i₁]
              · simp
              · intro i₄ _ hne; simp [Ne.symm hne]
              · intro hnot; exact absurd h1 hnot
            · intro i₃ _ hne; simp [Ne.symm hne]
            · intro hnot; exact absurd h2 hnot
          trans ∑ i₁ ∈ J, ∑ i₂ ∈ J, (1 : ℝ)
          · exact Finset.sum_congr rfl fun i₁ h1 => Finset.sum_congr rfl fun i₂ h2 => this i₁ h1 i₂ h2
          · simp [sq]
        rw [hsum1, hsum2, hsum3]
    _ = 3 * (J.card : ℝ) ^ 2 := by ring

-- ============================================================================
-- Section 5: Shift overlap deviations, potential Z(S), rebalancing, and limsup
-- ============================================================================

private def setA {N : ℕ} (S : Conf (2 * N)) : Finset ℤ :=
  (Finset.univ.filter fun x : Fin (2 * N) => S x = true).image (fun x : Fin (2 * N) => (x.1 : ℤ) + 1)

private def setB {N : ℕ} (S : Conf (2 * N)) : Finset ℤ :=
  (Finset.univ.filter fun x : Fin (2 * N) => S x = false).image (fun x : Fin (2 * N) => (x.1 : ℤ) + 1)

private lemma setA_disj_setB {N : ℕ} (S : Conf (2 * N)) : Disjoint (setA S) (setB S) := by
  rw [Finset.disjoint_left]
  intro z hzA hzB
  simp only [setA, setB, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hzA hzB
  obtain ⟨x, hx, rfl⟩ := hzA
  obtain ⟨y, hy, hxy⟩ := hzB
  have hxy' : x = y := by ext; omega
  rw [hxy'] at hx
  rw [hx] at hy
  exact Bool.noConfusion hy

private lemma setA_union_setB {N : ℕ} (S : Conf (2 * N)) :
    setA S ∪ setB S = Finset.Icc (1 : ℤ) (2 * N) := by
  ext z
  simp only [Finset.mem_union, setA, setB, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro (⟨x, _, rfl⟩ | ⟨x, _, rfl⟩) <;> have := x.2 <;> omega
  · intro ⟨h1, h2⟩
    let x : Fin (2 * N) := ⟨(z - 1).toNat, by omega⟩
    have hx : (x.1 : ℤ) + 1 = z := by dsimp [x]; omega
    cases hSx : S x
    · right; exact ⟨x, hSx, hx⟩
    · left; exact ⟨x, hSx, hx⟩

private lemma setA_card_eq_sum {N : ℕ} (S : Conf (2 * N)) :
    ((setA S).card : ℝ) = ∑ x : Fin (2 * N), if S x then (1 : ℝ) else 0 := by
  unfold setA
  rw [Finset.card_image_of_injective _ (fun x y h => by ext; omega)]
  rw [Finset.sum_boole]

private lemma overlap_setA_setB_pos {N : ℕ} (S : Conf (2 * N)) (k : ℕ) (hk : 1 ≤ k) (hkm : k < 2 * N) :
    (Erdos36.Overlap (setA S) (setB S) (k : ℤ) : ℝ) =
      ∑ b ∈ Finset.range (2 * N - k),
        (if h : b + k < 2 * N then
          (if S ⟨b + k, h⟩ then (1 : ℝ) else 0) * (if S ⟨b, by omega⟩ then (0 : ℝ) else 1)
         else 0) := by
  have hcard :
      Erdos36.Overlap (setA S) (setB S) (k : ℤ) =
        ((Finset.range (2 * N - k)).filter fun b =>
          if h : b + k < 2 * N then S ⟨b + k, h⟩ = true ∧ S ⟨b, by omega⟩ = false else False).card := by
    unfold Erdos36.Overlap
    rw [Finset.product_eq_sprod]
    refine Finset.card_nbij'
      (fun p => (p.2 - 1).toNat)
      (fun b => ((b : ℤ) + k + 1, (b : ℤ) + 1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, setA, setB, Finset.mem_image,
        Finset.mem_univ, true_and] at hp
      obtain ⟨⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩, hdiff⟩ := hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      have hy_eq : (p.2 - 1).toNat = y.1 := by omega
      have hx_eq : y.1 + k = x.1 := by omega
      have hlt : y.1 + k < 2 * N := by rw [hx_eq]; exact x.2
      refine ⟨by omega, ?_⟩
      rw [dif_pos (by omega : (p.2 - 1).toNat + k < 2 * N)]
      constructor
      · have : (⟨(p.2 - 1).toNat + k, by omega⟩ : Fin (2 * N)) = x := by ext; dsimp; omega
        rw [this]; exact hx
      · have : (⟨(p.2 - 1).toNat, by omega⟩ : Fin (2 * N)) = y := by ext; dsimp; omega
        rw [this]; exact hy
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [dif_pos (by omega : b + k < 2 * N)] at hb2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, setA, setB, Finset.mem_image,
        Finset.mem_univ, true_and]
      refine ⟨⟨⟨⟨b + k, by omega⟩, hb2.1, by push_cast; ring⟩,
               ⟨⟨b, by omega⟩, hb2.2, rfl⟩⟩, by ring⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, setA, setB, Finset.mem_image,
        Finset.mem_univ, true_and] at hp
      obtain ⟨⟨⟨x, _, _⟩, ⟨y, _, _⟩⟩, hdiff⟩ := hp
      ext <;> dsimp <;> omega
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb
      dsimp; omega
  rw [hcard, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  have hlt : b + k < 2 * N := by omega
  simp only [dif_pos hlt]
  cases S ⟨b + k, hlt⟩ <;> cases S ⟨b, by omega⟩ <;> simp

private lemma overlap_setA_setB_neg {N : ℕ} (S : Conf (2 * N)) (k : ℕ) (hk : 1 ≤ k) (hkm : k < 2 * N) :
    (Erdos36.Overlap (setA S) (setB S) (-(k : ℤ)) : ℝ) =
      ∑ b ∈ Finset.range (2 * N - k),
        (if h : b + k < 2 * N then
          (if S ⟨b, by omega⟩ then (1 : ℝ) else 0) * (if S ⟨b + k, h⟩ then (0 : ℝ) else 1)
         else 0) := by
  have hcard :
      Erdos36.Overlap (setA S) (setB S) (-(k : ℤ)) =
        ((Finset.range (2 * N - k)).filter fun b =>
          if h : b + k < 2 * N then S ⟨b, by omega⟩ = true ∧ S ⟨b + k, h⟩ = false else False).card := by
    unfold Erdos36.Overlap
    rw [Finset.product_eq_sprod]
    refine Finset.card_nbij'
      (fun p => (p.1 - 1).toNat)
      (fun b => ((b : ℤ) + 1, (b : ℤ) + k + 1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, setA, setB, Finset.mem_image,
        Finset.mem_univ, true_and] at hp
      obtain ⟨⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩, hdiff⟩ := hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      have hx_eq : (p.1 - 1).toNat = x.1 := by omega
      have hy_eq : x.1 + k = y.1 := by omega
      have hlt : x.1 + k < 2 * N := by rw [hy_eq]; exact y.2
      refine ⟨by omega, ?_⟩
      rw [dif_pos (by omega : (p.1 - 1).toNat + k < 2 * N)]
      constructor
      · have : (⟨(p.1 - 1).toNat, by omega⟩ : Fin (2 * N)) = x := by ext; dsimp; omega
        rw [this]; exact hx
      · have : (⟨(p.1 - 1).toNat + k, by omega⟩ : Fin (2 * N)) = y := by ext; dsimp; omega
        rw [this]; exact hy
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [dif_pos (by omega : b + k < 2 * N)] at hb2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, setA, setB, Finset.mem_image,
        Finset.mem_univ, true_and]
      refine ⟨⟨⟨⟨b, by omega⟩, hb2.1, rfl⟩,
               ⟨⟨b + k, by omega⟩, hb2.2, by push_cast; ring⟩⟩, by ring⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, setA, setB, Finset.mem_image,
        Finset.mem_univ, true_and] at hp
      obtain ⟨⟨⟨x, _, _⟩, ⟨y, _, _⟩⟩, hdiff⟩ := hp
      ext <;> dsimp <;> omega
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb
      dsimp; omega
  rw [hcard, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  have hlt : b + k < 2 * N := by omega
  simp only [dif_pos hlt]
  cases S ⟨b, by omega⟩ <;> cases S ⟨b + k, hlt⟩ <;> simp

private lemma meanOverlap_pos_eq (N k : ℕ) (hk : 1 ≤ k) (hkm : k < 2 * N) :
    meanOverlap N (k : ℤ) =
      ∑ b ∈ Finset.range (2 * N - k),
        if h : b + k < 2 * N then pN N ⟨b + k, h⟩ * (1 - pN N ⟨b, by omega⟩) else 0 := by
  unfold meanOverlap
  let f : ℕ → ℝ := fun x =>
    if hx : x < 2 * N then
      if h : 0 ≤ (x : ℤ) - (k : ℤ) ∧ (x : ℤ) - (k : ℤ) < (2 * N : ℤ) then
        pN N ⟨x, hx⟩ * (1 - pN N ⟨((x : ℤ) - (k : ℤ)).toNat, by omega⟩)
      else 0
    else 0
  have h1 : (∑ x : Fin (2 * N),
      if h : 0 ≤ (x.1 : ℤ) - (k : ℤ) ∧ (x.1 : ℤ) - (k : ℤ) < (2 * N : ℤ) then
        pN N x * (1 - pN N ⟨((x.1 : ℤ) - (k : ℤ)).toNat, by omega⟩)
      else 0) = ∑ x ∈ Finset.range (2 * N), f x := by
    rw [← Fin.sum_univ_eq_sum_range f]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only [f]
    rw [dif_pos x.2]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * N)) (fun x => k ≤ x)]
  have hzero : ∑ x ∈ (Finset.range (2 * N)).filter (fun x => ¬ k ≤ x), f x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    dsimp only [f]
    rw [dif_pos hx.1, dif_neg (by omega)]
  rw [hzero, add_zero]
  refine Finset.sum_nbij' (fun x => x - k) (fun b => b + k) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢; omega
  · intro b hb; simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢; omega
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx; omega
  · intro b _; omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hc : 0 ≤ (x : ℤ) - (k : ℤ) ∧ (x : ℤ) - (k : ℤ) < (2 * N : ℤ) := by omega
    have hlt : x - k + k < 2 * N := by omega
    dsimp only [f]
    rw [dif_pos hx.1, dif_pos hc, dif_pos hlt]
    have heq1 : (⟨x, hx.1⟩ : Fin (2 * N)) = ⟨x - k + k, hlt⟩ := by ext; dsimp; omega
    have heq2 : (⟨((x : ℤ) - (k : ℤ)).toNat, by omega⟩ : Fin (2 * N)) = ⟨x - k, by omega⟩ := by
      ext; dsimp; omega
    rw [heq1, heq2]

private lemma meanOverlap_neg_eq (N k : ℕ) (hk : 1 ≤ k) (hkm : k < 2 * N) :
    meanOverlap N (-(k : ℤ)) =
      ∑ b ∈ Finset.range (2 * N - k),
        if h : b + k < 2 * N then pN N ⟨b, by omega⟩ * (1 - pN N ⟨b + k, h⟩) else 0 := by
  unfold meanOverlap
  let f : ℕ → ℝ := fun x =>
    if hx : x < 2 * N then
      if h : 0 ≤ (x : ℤ) - (-(k : ℤ)) ∧ (x : ℤ) - (-(k : ℤ)) < (2 * N : ℤ) then
        pN N ⟨x, hx⟩ * (1 - pN N ⟨((x : ℤ) - (-(k : ℤ))).toNat, by omega⟩)
      else 0
    else 0
  have h1 : (∑ x : Fin (2 * N),
      if h : 0 ≤ (x.1 : ℤ) - (-(k : ℤ)) ∧ (x.1 : ℤ) - (-(k : ℤ)) < (2 * N : ℤ) then
        pN N x * (1 - pN N ⟨((x.1 : ℤ) - (-(k : ℤ))).toNat, by omega⟩)
      else 0) = ∑ x ∈ Finset.range (2 * N), f x := by
    rw [← Fin.sum_univ_eq_sum_range f]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only [f]
    rw [dif_pos x.2]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * N)) (fun x => x < 2 * N - k)]
  have hzero : ∑ x ∈ (Finset.range (2 * N)).filter (fun x => ¬ x < 2 * N - k), f x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    dsimp only [f]
    rw [dif_pos hx.1, dif_neg (by omega)]
  rw [hzero, add_zero]
  have hfilt : (Finset.range (2 * N)).filter (fun x => x < 2 * N - k) = Finset.range (2 * N - k) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilt]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  have hc : 0 ≤ (b : ℤ) - (-(k : ℤ)) ∧ (b : ℤ) - (-(k : ℤ)) < (2 * N : ℤ) := by omega
  have hlt : b + k < 2 * N := by omega
  dsimp only [f]
  rw [dif_pos (by omega : b < 2 * N), dif_pos hc, dif_pos hlt]
  have heq2 : (⟨((b : ℤ) - (-(k : ℤ))).toNat, by omega⟩ : Fin (2 * N)) = ⟨b + k, hlt⟩ := by
    ext; dsimp; omega
  rw [heq2]

private lemma rebalance_partition (N : ℕ) (A B : Finset ℤ)
    (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * N)) :
    ∃ A' B' : Finset ℤ,
      Disjoint A' B' ∧
      A' ∪ B' = Finset.Icc (1 : ℤ) (2 * N) ∧
      A'.card = B'.card ∧
      ∀ k : ℤ, (Erdos36.Overlap A' B' k : ℝ) ≤
        (Erdos36.Overlap A B k : ℝ) + |(A.card : ℝ) - (N : ℝ)| := by
  have htot : A.card + B.card = 2 * N := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
    omega
  by_cases hle : A.card ≤ N
  · have hsub_le : N - A.card ≤ B.card := by omega
    obtain ⟨T, hTB, hTcard⟩ := Finset.exists_subset_card_eq hsub_le
    refine ⟨A ∪ T, B \ T, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj, Finset.disjoint_sdiff⟩
    · rw [Finset.union_assoc, Finset.union_sdiff_of_subset hTB, hunion]
    · have hdisjAT : Disjoint A T := Finset.disjoint_of_subset_right hTB hdisj
      rw [Finset.card_union_of_disjoint hdisjAT, Finset.card_sdiff, Finset.inter_eq_left.mpr hTB, hTcard]
      omega
    · intro k
      have hcard_ov : Erdos36.Overlap (A ∪ T) (B \ T) k ≤ Erdos36.Overlap A B k + T.card := by
        unfold Erdos36.Overlap
        rw [Finset.product_eq_sprod, Finset.product_eq_sprod]
        let P_new := (((A ∪ T) ×ˢ (B \ T)).filter fun p => p.1 - p.2 = k)
        let P_old := ((A ×ˢ B).filter fun p => p.1 - p.2 = k)
        let P_extra := P_new.filter (fun p => p.1 ∈ T)
        have hsub_u : P_new ⊆ P_old ∪ P_extra := by
          intro p hp
          rw [Finset.mem_union]
          by_cases hpT : p.1 ∈ T
          · right; exact Finset.mem_filter.mpr ⟨hp, hpT⟩
          · left
            simp only [P_new, P_old, Finset.mem_filter, Finset.mem_product, Finset.mem_union,
              Finset.mem_sdiff] at hp ⊢
            exact ⟨⟨hp.1.1.resolve_right hpT, hp.1.2.1⟩, hp.2⟩
        have hextra_le : P_extra.card ≤ T.card := by
          refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
          · intro p hp
            exact (Finset.mem_filter.mp hp).2
          · intro p hp q hq heq
            have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have hq' := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
            exact Prod.ext heq (by omega)
        calc P_new.card ≤ (P_old ∪ P_extra).card := Finset.card_le_card hsub_u
          _ ≤ P_old.card + P_extra.card := Finset.card_union_le _ _
          _ ≤ P_old.card + T.card := Nat.add_le_add_left hextra_le _
      have hTreal : (T.card : ℝ) = |(A.card : ℝ) - (N : ℝ)| := by
        rw [hTcard, Nat.cast_sub hle, abs_of_nonpos (by
          have : (A.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
          linarith)]
        ring
      have hreal : (Erdos36.Overlap (A ∪ T) (B \ T) k : ℝ) ≤
          (Erdos36.Overlap A B k : ℝ) + (T.card : ℝ) := by exact_mod_cast hcard_ov
      linarith
  · have hge : N ≤ A.card := by omega
    have hsub_le : A.card - N ≤ A.card := by omega
    obtain ⟨T, hTA, hTcard⟩ := Finset.exists_subset_card_eq hsub_le
    refine ⟨A \ T, B ∪ T, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_union_right]
      exact ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj, Finset.sdiff_disjoint⟩
    · rw [← Finset.union_assoc, Finset.union_comm (A \ T) B, Finset.union_assoc,
        Finset.sdiff_union_of_subset hTA, Finset.union_comm, hunion]
    · have hdisjBT : Disjoint B T := Finset.disjoint_of_subset_right hTA hdisj.symm
      rw [Finset.card_union_of_disjoint hdisjBT, Finset.card_sdiff, Finset.inter_eq_left.mpr hTA, hTcard]
      omega
    · intro k
      have hcard_ov : Erdos36.Overlap (A \ T) (B ∪ T) k ≤ Erdos36.Overlap A B k + T.card := by
        unfold Erdos36.Overlap
        rw [Finset.product_eq_sprod, Finset.product_eq_sprod]
        let P_new := (((A \ T) ×ˢ (B ∪ T)).filter fun p => p.1 - p.2 = k)
        let P_old := ((A ×ˢ B).filter fun p => p.1 - p.2 = k)
        let P_extra := P_new.filter (fun p => p.2 ∈ T)
        have hsub_u : P_new ⊆ P_old ∪ P_extra := by
          intro p hp
          rw [Finset.mem_union]
          by_cases hpT : p.2 ∈ T
          · right; exact Finset.mem_filter.mpr ⟨hp, hpT⟩
          · left
            simp only [P_new, P_old, Finset.mem_filter, Finset.mem_product, Finset.mem_union,
              Finset.mem_sdiff] at hp ⊢
            exact ⟨⟨hp.1.1.1, hp.1.2.resolve_right hpT⟩, hp.2⟩
        have hextra_le : P_extra.card ≤ T.card := by
          refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
          · intro p hp
            exact (Finset.mem_filter.mp hp).2
          · intro p hp q hq heq
            have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have hq' := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
            exact Prod.ext (by omega) heq
        calc P_new.card ≤ (P_old ∪ P_extra).card := Finset.card_le_card hsub_u
          _ ≤ P_old.card + P_extra.card := Finset.card_union_le _ _
          _ ≤ P_old.card + T.card := Nat.add_le_add_left hextra_le _
      have hTreal : (T.card : ℝ) = |(A.card : ℝ) - (N : ℝ)| := by
        rw [hTcard, Nat.cast_sub hge, abs_of_nonneg (by
          have : (N : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hge
          linarith)]
      have hreal : (Erdos36.Overlap (A \ T) (B ∪ T) k : ℝ) ≤
          (Erdos36.Overlap A B k : ℝ) + (T.card : ℝ) := by exact_mod_cast hcard_ov
      linarith

-- Modular shift-deviation definitions and 4th-moment lemmas (keeps contexts small and fast)
private noncomputable def Ypos (N k b : ℕ) (S : Conf (2 * N)) : ℝ :=
  if h : b + k < 2 * N then
    (if S ⟨b + k, h⟩ then (1 : ℝ) else 0) * (if S ⟨b, by omega⟩ then (0 : ℝ) else 1) -
      pN N ⟨b + k, h⟩ * (1 - pN N ⟨b, by omega⟩)
  else 0

private noncomputable def Yneg (N k b : ℕ) (S : Conf (2 * N)) : ℝ :=
  if h : b + k < 2 * N then
    (if S ⟨b, by omega⟩ then (1 : ℝ) else 0) * (if S ⟨b + k, h⟩ then (0 : ℝ) else 1) -
      pN N ⟨b, by omega⟩ * (1 - pN N ⟨b + k, h⟩)
  else 0

private def Ipar (N k r : ℕ) : Finset ℕ :=
  (Finset.range (2 * N - k)).filter (fun b => (b / k) % 2 = r)

private noncomputable def Dpos (N k r : ℕ) (S : Conf (2 * N)) : ℝ :=
  ∑ b ∈ Ipar N k r, Ypos N k b S

private noncomputable def Dneg (N k r : ℕ) (S : Conf (2 * N)) : ℝ :=
  ∑ b ∈ Ipar N k r, Yneg N k b S

private lemma fourth_moment_pos (N k r : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * N) :
    exp (pN N) (fun S => (Dpos N k r S) ^ 4) ≤ 12 * (N : ℝ) ^ 2 := by
  have hk_pos : 0 < k := by omega
  let supp : ℕ → Finset (Fin (2 * N)) := fun b =>
    if h : b + k < 2 * N then {⟨b + k, h⟩, ⟨b, by omega⟩} else ∅
  have hle := exp_pow_four_sum_le (pN N) (pN_bounds N) (Ipar N k r) (Ypos N k) supp
    (by
      intro b hb S₁ S₂ hS
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at hb
      have hlt : b + k < 2 * N := by omega
      simp only [Ypos, dif_pos hlt]
      dsimp only [supp] at hS
      rw [dif_pos hlt] at hS
      rw [hS ⟨b + k, hlt⟩ (by simp), hS ⟨b, by omega⟩ (by simp)])
    (by
      intro b₁ h1 b₂ h2 hne
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at h1 h2
      have hlt1 : b₁ + k < 2 * N := by omega
      have hlt2 : b₂ + k < 2 * N := by omega
      dsimp only [supp]
      rw [dif_pos hlt1, dif_pos hlt2, Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
      · have : b₁ + k = b₂ + k := congrArg Fin.val h; omega
      · have heq : b₁ + k = b₂ := congrArg Fin.val h
        have hdiv : b₂ / k = b₁ / k + 1 := by rw [← heq, Nat.add_div_right _ hk_pos]
        omega
      · have heq : b₁ = b₂ + k := congrArg Fin.val h
        have hdiv : b₁ / k = b₂ / k + 1 := by rw [heq, Nat.add_div_right _ hk_pos]
        omega
      · have : b₁ = b₂ := congrArg Fin.val h; exact hne this)
    (by
      intro b hb
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at hb
      have hlt : b + k < 2 * N := by omega
      have hfun : Ypos N k b = fun S =>
          (if S ⟨b + k, hlt⟩ then (1 : ℝ) else 0) * (if S ⟨b, by omega⟩ then (0 : ℝ) else 1) -
            pN N ⟨b + k, hlt⟩ * (1 - pN N ⟨b, by omega⟩) := by
        funext S; simp only [Ypos, dif_pos hlt]
      rw [hfun, exp_sub, exp_const]
      have hne_fin : (⟨b + k, hlt⟩ : Fin (2 * N)) ≠ ⟨b, by omega⟩ := by
        intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
      rw [exp_mul_of_disjoint (pN N) {⟨b + k, hlt⟩} {⟨b, by omega⟩}
        (Finset.disjoint_singleton.mpr hne_fin)
        (fun S => if S ⟨b + k, hlt⟩ then (1 : ℝ) else 0)
        (fun S => if S ⟨b, by omega⟩ then (0 : ℝ) else 1)
        (fun S₁ S₂ h => by rw [h _ (by simp)])
        (fun S₁ S₂ h => by rw [h _ (by simp)]),
        exp_ind_true, exp_ind_false, sub_self])
    (by
      intro b hb S
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at hb
      have hlt : b + k < 2 * N := by omega
      simp only [Ypos, dif_pos hlt]
      have hp1 := pN_bounds N ⟨b + k, hlt⟩; have hp2 := pN_bounds N ⟨b, by omega⟩
      rw [abs_le]
      cases S ⟨b + k, hlt⟩ <;> cases S ⟨b, by omega⟩ <;> simp <;> constructor <;> nlinarith)
  have hcard_le : ((Ipar N k r).card : ℝ) ≤ 2 * (N : ℝ) := by
    have : (Ipar N k r).card ≤ 2 * N :=
      le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range]; exact Nat.sub_le _ _)
    exact_mod_cast this
  calc exp (pN N) (fun S => (Dpos N k r S) ^ 4)
      ≤ 3 * ((Ipar N k r).card : ℝ) ^ 2 := hle
    _ ≤ 3 * (2 * (N : ℝ)) ^ 2 := by gcongr
    _ = 12 * (N : ℝ) ^ 2 := by ring

private lemma fourth_moment_neg (N k r : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * N) :
    exp (pN N) (fun S => (Dneg N k r S) ^ 4) ≤ 12 * (N : ℝ) ^ 2 := by
  have hk_pos : 0 < k := by omega
  let supp : ℕ → Finset (Fin (2 * N)) := fun b =>
    if h : b + k < 2 * N then {⟨b, by omega⟩, ⟨b + k, h⟩} else ∅
  have hle := exp_pow_four_sum_le (pN N) (pN_bounds N) (Ipar N k r) (Yneg N k) supp
    (by
      intro b hb S₁ S₂ hS
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at hb
      have hlt : b + k < 2 * N := by omega
      simp only [Yneg, dif_pos hlt]
      dsimp only [supp] at hS
      rw [dif_pos hlt] at hS
      rw [hS ⟨b, by omega⟩ (by simp), hS ⟨b + k, hlt⟩ (by simp)])
    (by
      intro b₁ h1 b₂ h2 hne
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at h1 h2
      have hlt1 : b₁ + k < 2 * N := by omega
      have hlt2 : b₂ + k < 2 * N := by omega
      dsimp only [supp]
      rw [dif_pos hlt1, dif_pos hlt2, Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
      · have : b₁ = b₂ := congrArg Fin.val h; exact hne this
      · have heq : b₁ = b₂ + k := congrArg Fin.val h
        have hdiv : b₁ / k = b₂ / k + 1 := by rw [heq, Nat.add_div_right _ hk_pos]
        omega
      · have heq : b₁ + k = b₂ := congrArg Fin.val h
        have hdiv : b₂ / k = b₁ / k + 1 := by rw [← heq, Nat.add_div_right _ hk_pos]
        omega
      · have : b₁ + k = b₂ + k := congrArg Fin.val h; omega)
    (by
      intro b hb
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at hb
      have hlt : b + k < 2 * N := by omega
      have hfun : Yneg N k b = fun S =>
          (if S ⟨b, by omega⟩ then (1 : ℝ) else 0) * (if S ⟨b + k, hlt⟩ then (0 : ℝ) else 1) -
            pN N ⟨b, by omega⟩ * (1 - pN N ⟨b + k, hlt⟩) := by
        funext S; simp only [Yneg, dif_pos hlt]
      rw [hfun, exp_sub, exp_const]
      have hne_fin : (⟨b, by omega⟩ : Fin (2 * N)) ≠ ⟨b + k, hlt⟩ := by
        intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
      rw [exp_mul_of_disjoint (pN N) {⟨b, by omega⟩} {⟨b + k, hlt⟩}
        (Finset.disjoint_singleton.mpr hne_fin)
        (fun S => if S ⟨b, by omega⟩ then (1 : ℝ) else 0)
        (fun S => if S ⟨b + k, hlt⟩ then (0 : ℝ) else 1)
        (fun S₁ S₂ h => by rw [h _ (by simp)])
        (fun S₁ S₂ h => by rw [h _ (by simp)]),
        exp_ind_true, exp_ind_false, sub_self])
    (by
      intro b hb S
      simp only [Ipar, Finset.mem_filter, Finset.mem_range] at hb
      have hlt : b + k < 2 * N := by omega
      simp only [Yneg, dif_pos hlt]
      have hp1 := pN_bounds N ⟨b, by omega⟩; have hp2 := pN_bounds N ⟨b + k, hlt⟩
      rw [abs_le]
      cases S ⟨b, by omega⟩ <;> cases S ⟨b + k, hlt⟩ <;> simp <;> constructor <;> nlinarith)
  have hcard_le : ((Ipar N k r).card : ℝ) ≤ 2 * (N : ℝ) := by
    have : (Ipar N k r).card ≤ 2 * N :=
      le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range]; exact Nat.sub_le _ _)
    exact_mod_cast this
  calc exp (pN N) (fun S => (Dneg N k r S) ^ 4)
      ≤ 3 * ((Ipar N k r).card : ℝ) ^ 2 := hle
    _ ≤ 3 * (2 * (N : ℝ)) ^ 2 := by gcongr
    _ = 12 * (N : ℝ) ^ 2 := by ring

private lemma exists_good_conf (N : ℕ) (hN : 10 ^ 28 ≤ N) :
    let δ : ℝ := 3 / 1000000
    ∃ S : Conf (2 * N),
      |((setA S).card : ℝ) - (N : ℝ)| < δ * (N : ℝ) ∧
      ∀ k ∈ Finset.Ico 1 (2 * N),
        |Dpos N k 0 S| < δ * (N : ℝ) / 2 ∧ |Dpos N k 1 S| < δ * (N : ℝ) / 2 ∧
        |Dneg N k 0 S| < δ * (N : ℝ) / 2 ∧ |Dneg N k 1 S| < δ * (N : ℝ) / 2 := by
  intro δ
  have hmN : m ≤ 2 * N := by unfold m; omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hδ_pos : 0 < δ := by norm_num [δ]
  have hδN_pos : 0 < δ * (N : ℝ) := by positivity
  have hδN2_pos : 0 < δ * (N : ℝ) / 2 := by positivity
  let Z (S : Conf (2 * N)) : ℝ :=
    ((setA S).card - (N : ℝ)) ^ 2 / (δ * (N : ℝ)) ^ 2 +
      ∑ k ∈ Finset.Ico 1 (2 * N),
        ((Dpos N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
         (Dpos N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
         (Dneg N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
         (Dneg N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4)
  have hEZ_lt : exp (pN N) Z < 1 := by
    dsimp only [Z]
    rw [exp_add, exp_sum]
    have hcard_exp : exp (pN N) (fun S => ((setA S).card - (N : ℝ)) ^ 2 / (δ * (N : ℝ)) ^ 2) ≤
        2 / (δ ^ 2 * (N : ℝ)) := by
      have hrew : (fun S => ((setA S).card - (N : ℝ)) ^ 2 / (δ * (N : ℝ)) ^ 2) =
          (fun S => ((δ * (N : ℝ)) ^ 2)⁻¹ *
            (∑ x : Fin (2 * N), ((if S x then (1 : ℝ) else 0) - pN N x)) ^ 2) := by
        funext S
        rw [div_eq_inv_mul, setA_card_eq_sum, ← sum_pN N hmN, Finset.sum_sub_distrib]
      rw [hrew, exp_smul]
      have h2 := exp_sq_sum_centered_le (pN N) (pN_bounds N)
      have hinv_nn : 0 ≤ ((δ * (N : ℝ)) ^ 2)⁻¹ := by positivity
      calc ((δ * (N : ℝ)) ^ 2)⁻¹ *
            exp (pN N) (fun S => (∑ x : Fin (2 * N), ((if S x then (1 : ℝ) else 0) - pN N x)) ^ 2)
          ≤ ((δ * (N : ℝ)) ^ 2)⁻¹ * ((2 * N : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h2 hinv_nn
        _ = 2 / (δ ^ 2 * (N : ℝ)) := by push_cast; field_simp
    have hshift_exp :
        (∑ k ∈ Finset.Ico 1 (2 * N),
          exp (pN N) (fun S =>
            (Dpos N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
            (Dpos N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
            (Dneg N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
            (Dneg N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4)) ≤
        1536 / (δ ^ 4 * (N : ℝ)) := by
      have hper_k : ∀ k ∈ Finset.Ico 1 (2 * N),
          exp (pN N) (fun S =>
            (Dpos N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
            (Dpos N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
            (Dneg N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
            (Dneg N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4) ≤
          768 / (δ ^ 4 * (N : ℝ) ^ 2) := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [exp_add, exp_add, exp_add]
        have hdiv : ∀ f : Conf (2 * N) → ℝ,
            exp (pN N) (fun S => f S / (δ * (N : ℝ) / 2) ^ 4) =
              ((δ * (N : ℝ) / 2) ^ 4)⁻¹ * exp (pN N) f := fun f => by
          simp_rw [div_eq_inv_mul]; exact exp_smul (pN N) _ f
        rw [hdiv, hdiv, hdiv, hdiv]
        have hinv_nn : 0 ≤ ((δ * (N : ℝ) / 2) ^ 4)⁻¹ := by positivity
        have b1 := mul_le_mul_of_nonneg_left (fourth_moment_pos N k 0 hk.1 hk.2) hinv_nn
        have b2 := mul_le_mul_of_nonneg_left (fourth_moment_pos N k 1 hk.1 hk.2) hinv_nn
        have b3 := mul_le_mul_of_nonneg_left (fourth_moment_neg N k 0 hk.1 hk.2) hinv_nn
        have b4 := mul_le_mul_of_nonneg_left (fourth_moment_neg N k 1 hk.1 hk.2) hinv_nn
        have hsum4 : ((δ * (N : ℝ) / 2) ^ 4)⁻¹ * (12 * (N : ℝ) ^ 2) * 4 =
            768 / (δ ^ 4 * (N : ℝ) ^ 2) := by field_simp; ring
        linarith
      calc (∑ k ∈ Finset.Ico 1 (2 * N), _)
          ≤ ∑ _k ∈ Finset.Ico 1 (2 * N), (768 / (δ ^ 4 * (N : ℝ) ^ 2)) :=
            Finset.sum_le_sum hper_k
        _ = ((Finset.Ico 1 (2 * N)).card : ℝ) * (768 / (δ ^ 4 * (N : ℝ) ^ 2)) := by simp
        _ ≤ (2 * (N : ℝ)) * (768 / (δ ^ 4 * (N : ℝ) ^ 2)) := by
            have hcard : ((Finset.Ico 1 (2 * N)).card : ℝ) ≤ 2 * (N : ℝ) := by
              rw [Nat.card_Ico]; exact_mod_cast (by omega : 2 * N - 1 ≤ 2 * N)
            have hr_nn : 0 ≤ 768 / (δ ^ 4 * (N : ℝ) ^ 2) := by positivity
            exact mul_le_mul_of_nonneg_right hcard hr_nn
        _ = 1536 / (δ ^ 4 * (N : ℝ)) := by field_simp; ring
    have hN_big : (10 ^ 28 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hnum : 2 / (δ ^ 2 * (N : ℝ)) + 1536 / (δ ^ 4 * (N : ℝ)) < 1 := by
      have h1 : 2 / (δ ^ 2 * (N : ℝ)) ≤ 2 / (δ ^ 2 * (10 ^ 28 : ℝ)) := by gcongr
      have h2 : 1536 / (δ ^ 4 * (N : ℝ)) ≤ 1536 / (δ ^ 4 * (10 ^ 28 : ℝ)) := by gcongr
      have h3 : 2 / (δ ^ 2 * (10 ^ 28 : ℝ)) + 1536 / (δ ^ 4 * (10 ^ 28 : ℝ)) < 1 := by
        dsimp only [δ]; norm_num
      linarith
    linarith
  obtain ⟨S, hZS⟩ := exists_lt_of_exp_lt (pN N) (pN_bounds N) Z 1 hEZ_lt
  refine ⟨S, ?_, ?_⟩
  · have hsum_nn : 0 ≤ ∑ k ∈ Finset.Ico 1 (2 * N),
        ((Dpos N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
         (Dpos N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
         (Dneg N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
         (Dneg N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4) :=
      Finset.sum_nonneg fun k _ => by positivity
    have hsq_lt : ((setA S).card - (N : ℝ)) ^ 2 / (δ * (N : ℝ)) ^ 2 < 1 := by
      dsimp only [Z] at hZS; linarith
    rw [div_lt_one (by positivity)] at hsq_lt
    have := sq_lt_sq.mp hsq_lt
    rwa [abs_of_pos hδN_pos] at this
  · intro k hk
    have hpow4_abs : ∀ x : ℝ, x ^ 4 / (δ * (N : ℝ) / 2) ^ 4 < 1 → |x| < δ * (N : ℝ) / 2 := by
      intro x hx
      rw [div_lt_one (by positivity)] at hx
      by_contra hge
      push Not at hge
      have h1 : (δ * (N : ℝ) / 2) ^ 2 ≤ x ^ 2 := by
        have := mul_le_mul hge hge (le_of_lt hδN2_pos) (abs_nonneg x)
        simpa [sq, abs_mul_abs_self] using this
      have h2 : (δ * (N : ℝ) / 2) ^ 4 ≤ x ^ 4 := by
        have := mul_le_mul h1 h1 (by positivity) (sq_nonneg x)
        linarith [show ((δ * (N : ℝ) / 2) ^ 2) * ((δ * (N : ℝ) / 2) ^ 2) = (δ * (N : ℝ) / 2) ^ 4 by ring,
                  show (x ^ 2) * (x ^ 2) = x ^ 4 by ring]
      linarith
    have hk_le :
        (Dpos N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
        (Dpos N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
        (Dneg N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
        (Dneg N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 < 1 := by
      have hsingle := Finset.single_le_sum (f := fun j =>
          (Dpos N j 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
          (Dpos N j 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
          (Dneg N j 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 +
          (Dneg N j 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4)
        (fun j _ => by positivity) hk
      have hcard_nn : 0 ≤ ((setA S).card - (N : ℝ)) ^ 2 / (δ * (N : ℝ)) ^ 2 := by positivity
      dsimp only [Z] at hZS
      linarith
    have nn1 : 0 ≤ (Dpos N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 := by positivity
    have nn2 : 0 ≤ (Dpos N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 := by positivity
    have nn3 : 0 ≤ (Dneg N k 0 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 := by positivity
    have nn4 : 0 ≤ (Dneg N k 1 S) ^ 4 / (δ * (N : ℝ) / 2) ^ 4 := by positivity
    exact ⟨hpow4_abs _ (by linarith), hpow4_abs _ (by linarith),
           hpow4_abs _ (by linarith), hpow4_abs _ (by linarith)⟩

private lemma quotient_le_of_large (N : ℕ) (hN : 10 ^ 28 ≤ N) :
    Erdos36.MinOverlapQuotient N ≤ 3809 / 10000 := by
  have hmN : m ≤ 2 * N := by unfold m; omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  obtain ⟨S, hcard_lt, hshift_small⟩ := exists_good_conf N hN
  obtain ⟨A', B', hdisj', hunion', hcard', hov_rebal⟩ :=
    rebalance_partition N (setA S) (setB S) (setA_disj_setB S) (setA_union_setB S)
  have hA'_sub : A' ⊆ Finset.Icc (1 : ℤ) (2 * N) := hunion' ▸ Finset.subset_union_left
  have hB'_sub : B' ⊆ Finset.Icc (1 : ℤ) (2 * N) := hunion' ▸ Finset.subset_union_right
  have hmargin : C_cert * (N : ℝ) + 2 * (m : ℝ) + 2 * ((3 / 1000000 : ℝ) * (N : ℝ)) ≤
      (3809 / 10000 : ℝ) * (N : ℝ) := by
    have hN_big : (10 ^ 28 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hC_val : C_cert < 380891 / 1000000 := by
      unfold C_cert peak m D; norm_num
    have hm_val : 2 * (m : ℝ) ≤ (1 / 1000000 : ℝ) * (N : ℝ) := by
      unfold m; linarith
    nlinarith
  have hov_all : ∀ k : ℤ, (Erdos36.Overlap A' B' k : ℝ) ≤ (3809 / 10000 : ℝ) * (N : ℝ) := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      have hzero : Erdos36.Overlap A' B' 0 = 0 := by
        unfold Erdos36.Overlap
        rw [Finset.product_eq_sprod, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p hp heq
        rw [Finset.mem_product] at hp
        have : p.1 = p.2 := by dsimp at heq; omega
        exact Finset.disjoint_left.mp hdisj' hp.1 (this ▸ hp.2)
      rw [hzero, Nat.cast_zero]; positivity
    · by_cases hrange : 0 < k ∧ k < (2 * N : ℤ)
      · let kn : ℕ := k.toNat
        have hkn_eq : (kn : ℤ) = k := Int.toNat_of_nonneg (by omega)
        have hkn1 : 1 ≤ kn := by omega
        have hkn2 : kn < 2 * N := by omega
        have hkn_mem : kn ∈ Finset.Ico 1 (2 * N) := Finset.mem_Ico.mpr ⟨hkn1, hkn2⟩
        have hs := hshift_small kn hkn_mem
        have hsplit_eo : Dpos N kn 0 S + Dpos N kn 1 S =
            (Erdos36.Overlap (setA S) (setB S) (kn : ℤ) : ℝ) - meanOverlap N (kn : ℤ) := by
          unfold Dpos Ipar
          have hcomp : ((Finset.range (2 * N - kn)).filter (fun b => (b / kn) % 2 = 1)) =
              (Finset.range (2 * N - kn)).filter (fun b => ¬ (b / kn) % 2 = 0) := by
            ext b; simp only [Finset.mem_filter]
            constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
          rw [hcomp, Finset.sum_filter_add_sum_filter_not]
          rw [overlap_setA_setB_pos S kn hkn1 hkn2, meanOverlap_pos_eq N kn hkn1 hkn2,
              ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [Finset.mem_range] at hb
          have hlt : b + kn < 2 * N := by omega
          simp only [Ypos, dif_pos hlt]
        have hov_S : (Erdos36.Overlap (setA S) (setB S) k : ℝ) ≤
            C_cert * (N : ℝ) + 2 * (m : ℝ) + (3 / 1000000 : ℝ) * (N : ℝ) := by
          rw [← hkn_eq]
          have h1 : Dpos N kn 0 S < (3 / 1000000 : ℝ) * (N : ℝ) / 2 := (abs_lt.mp hs.1).2
          have h2 : Dpos N kn 1 S < (3 / 1000000 : ℝ) * (N : ℝ) / 2 := (abs_lt.mp hs.2.1).2
          have h3 : meanOverlap N (kn : ℤ) ≤ C_cert * (N : ℝ) + 2 * (m : ℝ) :=
            meanOverlap_le N hmN (kn : ℤ)
          linarith
        have hrb := hov_rebal k
        linarith
      · by_cases hrange_neg : -(2 * N : ℤ) < k ∧ k < 0
        · let kn : ℕ := (-k).toNat
          have hkn_eq : -(kn : ℤ) = k := by
            have := Int.toNat_of_nonneg (by omega : 0 ≤ -k); dsimp [kn]; omega
          have hkn1 : 1 ≤ kn := by omega
          have hkn2 : kn < 2 * N := by omega
          have hkn_mem : kn ∈ Finset.Ico 1 (2 * N) := Finset.mem_Ico.mpr ⟨hkn1, hkn2⟩
          have hs := hshift_small kn hkn_mem
          have hsplit_eo : Dneg N kn 0 S + Dneg N kn 1 S =
              (Erdos36.Overlap (setA S) (setB S) (-(kn : ℤ)) : ℝ) - meanOverlap N (-(kn : ℤ)) := by
            unfold Dneg Ipar
            have hcomp : ((Finset.range (2 * N - kn)).filter (fun b => (b / kn) % 2 = 1)) =
                (Finset.range (2 * N - kn)).filter (fun b => ¬ (b / kn) % 2 = 0) := by
              ext b; simp only [Finset.mem_filter]
              constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
            rw [hcomp, Finset.sum_filter_add_sum_filter_not]
            rw [overlap_setA_setB_neg S kn hkn1 hkn2, meanOverlap_neg_eq N kn hkn1 hkn2,
                ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun b hb => ?_
            rw [Finset.mem_range] at hb
            have hlt : b + kn < 2 * N := by omega
            simp only [Yneg, dif_pos hlt]
          have hov_S : (Erdos36.Overlap (setA S) (setB S) k : ℝ) ≤
              C_cert * (N : ℝ) + 2 * (m : ℝ) + (3 / 1000000 : ℝ) * (N : ℝ) := by
            rw [← hkn_eq]
            have h1 : Dneg N kn 0 S < (3 / 1000000 : ℝ) * (N : ℝ) / 2 := (abs_lt.mp hs.2.2.1).2
            have h2 : Dneg N kn 1 S < (3 / 1000000 : ℝ) * (N : ℝ) / 2 := (abs_lt.mp hs.2.2.2).2
            have h3 : meanOverlap N (-(kn : ℤ)) ≤ C_cert * (N : ℝ) + 2 * (m : ℝ) :=
              meanOverlap_le N hmN (-(kn : ℤ))
            linarith
          have hrb := hov_rebal k
          linarith
        · have hzero : Erdos36.Overlap A' B' k = 0 := by
            unfold Erdos36.Overlap
            rw [Finset.product_eq_sprod, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro p hp heq
            rw [Finset.mem_product] at hp
            have hp1 := Finset.mem_Icc.mp (hA'_sub hp.1)
            have hp2 := Finset.mem_Icc.mp (hB'_sub hp.2)
            dsimp at heq
            omega
          rw [hzero, Nat.cast_zero]; positivity
  let K : ℕ := ⌊(3809 / 10000 : ℝ) * (N : ℝ)⌋₊
  have hMax_le : Erdos36.MaxOverlap A' B' ≤ K := by
    unfold Erdos36.MaxOverlap
    exact ciSup_le fun k => Nat.le_floor (hov_all k)
  have hM_le : Erdos36.M N ≤ K := by
    have hmem : Erdos36.MaxOverlap A' B' ∈
        {Erdos36.MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
          (_disjoint : Disjoint A B)
          (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * N))
          (_same_card : A.card = B.card)} :=
      ⟨A', B', hdisj', hunion', hcard', rfl⟩
    exact le_trans (Nat.sInf_le hmem) hMax_le
  unfold Erdos36.MinOverlapQuotient
  rw [div_le_iff₀ hN_pos]
  calc (Erdos36.M N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hM_le
    _ ≤ (3809 / 10000 : ℝ) * (N : ℝ) := Nat.floor_le (by positivity)

lemma limsup_le : atTop.limsup Erdos36.MinOverlapQuotient ≤ 3809 / 10000 := by
  refine Filter.limsup_le_of_le ?_ ?_
  · exact Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Filter.Eventually.of_forall fun N => by unfold Erdos36.MinOverlapQuotient; positivity)
  · exact Filter.eventually_atTop.mpr ⟨10 ^ 28, fun N hN => quotient_le_of_large N hN⟩

end OMA.Erdos36Upper

noncomputable def OMA.answer : ℝ := 3809 / 10000

theorem OMA.solution :
    Erdos36.erdos_36.variants.upper.answer = OMA.answer →
      type_of% @Erdos36.erdos_36.variants.upper := by
  intro hans
  refine ⟨OMA.answer, ?_, ?_, hans.symm⟩
  · unfold OMA.answer; norm_num
  · exact OMA.Erdos36Upper.limsup_le
