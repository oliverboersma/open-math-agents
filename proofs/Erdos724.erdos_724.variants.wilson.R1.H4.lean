import OMAReductions.R_Erdos724_erdos_724_variants_wilson_R1
import Mathlib.NumberTheory.Chebyshev

/-!
Proof of `Erdos724.erdos_724.variants.wilson.R1.H4`.
Uses a finite-step + `s ^ (-10)` Rosser-Iwaniec beta-sieve (`beta_- = 4.94`, `beta_+ = 4.76`)
verified by `decide`, elementary Mertens first theorem via `Chebyshev.theta_le_log4_mul_x`,
and elementary CRT on `Finset.Ico`.
-/

namespace H4Sieve

open Finset

/- ## Section 1: Verified Rosser-Iwaniec Table and Step Functions -/

def tabMList : List ℕ := [1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 955865, 932989, 910620, 888749, 867363, 846451, 826002, 806007, 786455, 767335, 748639, 730357, 712479, 694997, 677902, 661186, 644839, 628855, 613224, 597940, 582995, 568381, 554091, 540119, 526457, 513099, 500038, 487269, 474784, 462577, 450644, 438977, 427572, 416423, 405524, 394871, 384458, 374279, 364332, 354609, 345107, 335822, 326748, 317882, 309219, 300755, 292486, 284407, 276516, 268808, 261280, 253927, 246747, 239736, 232890, 226206, 219681, 213312, 207095, 201028, 195108, 189331, 183695, 178197, 172834, 167604, 162504, 157531, 152683, 147958, 143353, 138865, 134493, 130234, 126086, 122046, 118114, 114286, 110560, 106936, 103409, 99980, 96645, 93404, 90253, 87192, 84219, 81332, 78530, 75810, 73171, 70613, 68132, 65728, 63399, 61144, 58961, 56849, 54807, 52834, 50927, 49086, 47309, 45592, 43935, 42335, 40789, 39298, 37858, 36467, 35125, 33830, 32580, 31374, 30209, 29086, 28002, 26956, 25947, 24973, 24035, 23129, 22256, 21413, 20601, 19818, 19063, 18335, 17633, 16957, 16305, 15677, 15071, 14488, 13926, 13385, 12863, 12361, 11877, 11412, 10963, 10531, 10115, 9715, 9330, 8959, 8603, 8259, 7929, 7612, 7306, 7012, 6730, 6458, 6197, 5945, 5704, 5472, 5249, 5035, 4829, 4631, 4441, 4259, 4083, 3915, 3753, 3598, 3449, 3307, 3169, 3038, 2911, 2790, 2674, 2562, 2455, 2353, 2255, 2160, 2070, 1983, 1900, 1820, 1744, 1671, 1601, 1534, 1469, 1407, 1348, 1292, 1238, 1186, 1136, 1088, 1043, 999, 957, 917, 879, 842, 807, 773, 741, 710, 681, 653, 626, 600, 575, 551, 529, 507, 486, 466, 447, 429, 412, 395, 379, 364, 349, 335, 322, 309, 297, 285, 274, 263, 253, 243, 234, 225, 216, 208, 200, 193, 186, 179, 172, 166, 160, 154, 149, 143, 138, 133, 129, 124, 120, 116, 112, 108, 105, 102, 98, 95, 92, 89, 87, 84, 81, 79, 77, 74, 72, 70, 68, 67, 65, 63, 61, 60, 58, 57, 55, 54, 53, 51, 50, 49, 48, 47, 46, 45, 44, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43]
def tabPList : List ℕ := [2269062, 2234005, 2199510, 2165563, 2132153, 2099270, 2066902, 2035038, 2003669, 1972783, 1942371, 1912423, 1882931, 1853884, 1825273, 1797091, 1769329, 1741978, 1715030, 1688477, 1662312, 1636527, 1611115, 1586068, 1561380, 1537044, 1513054, 1489401, 1466082, 1443088, 1420414, 1398055, 1376004, 1354256, 1332805, 1311646, 1290773, 1270182, 1249867, 1229824, 1210048, 1190533, 1171276, 1152271, 1133515, 1115003, 1096731, 1078695, 1060890, 1043313, 1025960, 1008828, 991911, 975208, 958713, 942425, 926338, 910451, 894760, 879261, 863951, 848828, 833888, 819128, 804546, 790139, 775903, 761837, 747936, 734200, 720625, 707209, 693949, 680844, 667889, 655084, 642426, 629912, 617541, 605310, 593217, 581261, 569438, 557748, 546187, 534755, 523450, 512268, 501210, 490272, 479454, 468752, 458167, 447695, 437336, 427088, 416949, 406917, 396992, 387171, 377454, 367838, 358323, 348906, 339587, 330365, 321237, 312203, 303261, 294411, 285650, 276978, 268349, 260124, 252134, 244373, 236835, 229514, 222403, 215497, 208790, 202277, 195952, 189810, 183846, 178055, 172432, 166973, 161674, 156529, 151535, 146687, 141981, 137414, 132982, 128680, 124506, 120456, 116526, 112713, 109014, 105426, 101945, 98569, 95295, 92120, 89041, 86055, 83161, 80355, 77635, 74998, 72443, 69966, 67567, 65242, 62989, 60807, 58694, 56647, 54665, 52746, 50888, 49089, 47348, 45662, 44032, 42454, 40927, 39451, 38022, 36641, 35306, 34014, 32766, 31560, 30394, 29268, 28179, 27128, 26113, 25132, 24186, 23272, 22390, 21539, 20718, 19925, 19161, 18424, 17714, 17029, 16368, 15732, 15119, 14528, 13959, 13411, 12884, 12376, 11887, 11416, 10963, 10528, 10109, 9705, 9318, 8945, 8587, 8242, 7911, 7593, 7287, 6993, 6710, 6439, 6178, 5927, 5686, 5455, 5233, 5020, 4815, 4618, 4429, 4247, 4073, 3906, 3745, 3591, 3443, 3301, 3164, 3033, 2908, 2787, 2672, 2561, 2454, 2352, 2254, 2160, 2070, 1984, 1901, 1821, 1745, 1672, 1602, 1535, 1471, 1409, 1350, 1294, 1239, 1187, 1138, 1090, 1044, 1001, 959, 919, 880, 843, 808, 774, 742, 711, 682, 653, 626, 600, 575, 552, 529, 507, 486, 466, 447, 429, 412, 395, 379, 364, 349, 335, 322, 309, 297, 285, 274, 263, 253, 243, 234, 225, 216, 208, 200, 193, 185, 179, 172, 166, 160, 154, 148, 143, 138, 133, 129, 124, 120, 116, 112, 108, 105, 102, 98, 95, 92, 89, 87, 84, 81, 79, 77, 74, 72, 70, 68, 67, 65, 63, 61, 60, 58, 57, 55, 54, 53, 51, 50, 49, 48, 47, 46, 45, 44, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43]
def fmList : List ℕ := [2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2269062, 2234005, 2199510, 2165563, 2132153, 2099270, 2066902, 2035038, 2003669, 1972783, 1942371, 1912423, 1882931, 1853884, 1825273, 1797091, 1769329, 1741978, 1715030, 1688477, 1662312, 1636527, 1611115, 1586068, 1561380, 1537044, 1513054, 1489401, 1466082, 1443088, 1420414, 1398055, 1376004, 1354256, 1332805, 1311646, 1290773, 1270182, 1249867, 1229824, 1210048, 1190533, 1171276, 1152271, 1133515, 1115003, 1096731, 1078695, 1060890, 1043313, 1025960, 1008828, 991911, 975208, 958713, 942425, 926338, 910451, 894760, 879261, 863951, 848828, 833888, 819128, 804546, 790139, 775903, 761837, 747936, 734200, 720625, 707209, 693949, 680844, 667889, 655084, 642426, 629912, 617541, 605310, 593217, 581261, 569438, 557748, 546187, 534755, 523450, 512268, 501210, 490272, 479454, 468752, 458167, 447695, 437336, 427088, 416949, 406917, 396992, 387171, 377454, 367838, 358323, 348906, 339587, 330365, 321237, 312203, 303261, 294411, 285650, 276978, 268349, 260124, 252134, 244373, 236835, 229514, 222403, 215497, 208790, 202277, 195952, 189810, 183846, 178055, 172432, 166973, 161674, 156529, 151535, 146687, 141981, 137414, 132982, 128680, 124506, 120456, 116526, 112713, 109014, 105426, 101945, 98569, 95295, 92120, 89041, 86055, 83161, 80355, 77635, 74998, 72443, 69966, 67567, 65242, 62989, 60807, 58694, 56647, 54665, 52746, 50888, 49089, 47348, 45662, 44032, 42454, 40927, 39451, 38022, 36641, 35306, 34014, 32766, 31560, 30394, 29268, 28179, 27128, 26113, 25132, 24186, 23272, 22390, 21539, 20718, 19925, 19161, 18424, 17714, 17029, 16368, 15732, 15119, 14528, 13959, 13411, 12884, 12376, 11887, 11416, 10963, 10528, 10109, 9705, 9318, 8945, 8587, 8242, 7911, 7593, 7287, 6993, 6710, 6439, 6178, 5927, 5686, 5455, 5233, 5020, 4815, 4618, 4429, 4247, 4073, 3906, 3745, 3591, 3443, 3301, 3164, 3033, 2908, 2787, 2672, 2561, 2454, 2352, 2254, 2160, 2070, 1984, 1901, 1821, 1745, 1672, 1602, 1535, 1471, 1409, 1350, 1294, 1239, 1187, 1138, 1090, 1044, 1001, 959, 919, 880, 843, 808, 774, 742, 711, 682, 653, 626, 600, 575, 552, 529, 507, 486, 466, 447, 429, 412, 395, 379, 364, 349, 335, 322, 309, 297, 285, 274, 263, 253, 243, 234, 225, 216, 208, 200, 193, 185, 179, 172, 166, 160, 154, 148, 143, 138, 133, 129, 124, 120, 116, 112, 112]
def fpList : List ℕ := [1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 1000000, 955865, 932989, 910620, 888749, 867363, 846451, 826002, 806007, 786455, 767335, 748639, 730357, 712479, 694997, 677902, 661186, 644839, 628855, 613224, 597940, 582995, 568381, 554091, 540119, 526457, 513099, 500038, 487269, 474784, 462577, 450644, 438977, 427572, 416423, 405524, 394871, 384458, 374279, 364332, 354609, 345107, 335822, 326748, 317882, 309219, 300755, 292486, 284407, 276516, 268808, 261280, 253927, 246747, 239736, 232890, 226206, 219681, 213312, 207095, 201028, 195108, 189331, 183695, 178197, 172834, 167604, 162504, 157531, 152683, 147958, 143353, 138865, 134493, 130234, 126086, 122046, 118114, 114286, 110560, 106936, 103409, 99980, 96645, 93404, 90253, 87192, 84219, 81332, 78530, 75810, 73171, 70613, 68132, 65728, 63399, 61144, 58961, 56849, 54807, 52834, 50927, 49086, 47309, 45592, 43935, 42335, 40789, 39298, 37858, 36467, 35125, 33830, 32580, 31374, 30209, 29086, 28002, 26956, 25947, 24973, 24035, 23129, 22256, 21413, 20601, 19818, 19063, 18335, 17633, 16957, 16305, 15677, 15071, 14488, 13926, 13385, 12863, 12361, 11877, 11412, 10963, 10531, 10115, 9715, 9330, 8959, 8603, 8259, 7929, 7612, 7306, 7012, 6730, 6458, 6197, 5945, 5704, 5472, 5249, 5035, 4829, 4631, 4441, 4259, 4083, 3915, 3753, 3598, 3449, 3307, 3169, 3038, 2911, 2790, 2674, 2562, 2455, 2353, 2255, 2160, 2070, 1983, 1900, 1820, 1744, 1671, 1601, 1534, 1469, 1407, 1348, 1292, 1238, 1186, 1136, 1088, 1043, 999, 957, 917, 879, 842, 807, 773, 741, 710, 681, 653, 626, 600, 575, 551, 529, 507, 486, 466, 447, 429, 412, 395, 379, 364, 349, 335, 322, 309, 297, 285, 274, 263, 253, 243, 234, 225, 216, 208, 200, 193, 186, 179, 172, 166, 160, 154, 149, 143, 138, 133, 129, 124, 120, 116, 112, 112]
def sufMList : List ℕ := [195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 195508781929, 193556247257, 191618697602, 189695803734, 187787391124, 185893330324, 184013364516, 182147281220, 180294973139, 178456144243, 176630663943, 174818330775, 173019053347, 171232546659, 169458636048, 167697261048, 165948227286, 164211329382, 162486414850, 160773321502, 159071942377, 157382096617, 155703659429, 154036430921, 152380335193, 150735221593, 149100998803, 147477362271, 145864410360, 144261820536, 142669538886, 141087505482, 139515511743, 137953483391, 136401267580, 134858776480, 133325842487, 131802437943, 130288381308, 128783633040, 127288073040, 125801498400, 124323928047, 122855145627, 121395159831, 119943819031, 118501043639, 117066748775, 115640764130, 114223073618, 112813576193, 111412247121, 110018810748, 108633397116, 107255718221, 105885897421, 104523634174, 103169045006, 101821988347, 100482316783, 99149964033, 97824947265, 96507104805, 95196357765, 93892712383, 92596082383, 91306286547, 90023411083, 88747174174, 87477747998, 86214933623, 84958713047, 83708971307, 82465778587, 81228822232, 79998261732, 78773967314, 77555804498, 76343829999, 75137902323, 73937974398, 72744096062, 71556014615, 70373875055, 69197416134, 68026779334, 66861900829, 65702506341, 64548836259, 63400608771, 62257957521, 61120591769, 59988748304, 58862128656, 57740860137, 56624852937, 55514013958, 54408246790, 53307673465, 52212081989, 51121591664, 50035983728, 48955374693, 47879538945, 46808590146, 45742526946, 44681113978, 43624461202, 42572443844, 41525170244, 40482392219, 39444215067, 38405205806, 37409125406, 36435935416, 35485212916, 34556523778, 33649422594, 32763327995, 31897895699, 31052646024, 30227214456, 29421099531, 28633916243, 27865269959, 27114756359, 26381961376, 25666592180, 24968348249, 24286656329, 23621330679, 22971911991, 22338065557, 21719584149, 21116118597, 20527174797, 19952661263, 19392206063, 18845429093, 18312081905, 17791910030, 17284652942, 16789901893, 16307525509, 15837244875, 15378774875, 14931824156, 14496095092, 14071577126, 13657815590, 13254643590, 12861741138, 12479081343, 12106183855, 11743164776, 11389532276, 11045091383, 10709796535, 10383445798, 10065677706, 9756436156, 9455506252, 9162668730, 8877699934, 8600530993, 8330770993, 8068665363, 7813654251, 7565655708, 7324748892, 7090357167, 6862718651, 6641577236, 6426505748, 6217739060, 6015010460, 5818048574, 5626916830, 5441167189, 5261029993, 5086221618, 4916453682, 4751954688, 4592256952, 4437412150, 4287295750, 4141780889, 4000560277, 3863858521, 3731363609, 3603119859, 3478808799, 3358289330, 3241784306, 3128967173, 3019691273, 2913993264, 2811723312, 2712916609, 2617231761, 2524700736, 2435165520, 2348656563, 2265204423, 2184454324, 2106239924, 2030975777, 1958105005, 1887847863, 1819835943, 1754289668, 1691034380, 1629892826, 1570885850, 1513832767, 1458955267, 1405867606, 1354587302, 1305131933, 1257519137, 1211559587, 1167269219, 1124455174, 1083131666, 1043312957, 1004801757, 967823103, 932177955, 897664546, 864508962, 832507662, 801671510, 771793317, 743101173, 715606048, 688877148, 663365433, 638636409, 614697406, 591780454, 569669204, 548371060, 527893450, 508243826, 489200223, 470768223, 453184787, 436225135, 419894905, 404199753, 389145353, 374501201, 360508230, 347172166, 334020511, 321535311, 309722342, 298103270, 286923016, 276429468, 266138418, 256297778, 246664427, 237488279, 228773244, 220273244, 212241212, 204429088, 197091827, 189725363, 182839688, 176182752, 169756527, 163821055, 157862192, 152139992, 146656451, 141413571, 136413360, 131657832, 127149007, 122622655, 118346031, 114321171, 110280756, 106495156, 102966423, 99424131, 96141783, 92846871, 89814996, 86771560, 83994270, 81206430, 78687861, 76159761, 73622112, 71357920, 69085208, 67089116, 64799316, 63075540, 61056957, 59320293, 57577167, 55827567, 54071481, 52602661, 51128416, 49648736, 48460636, 46970056, 45773220, 44572004, 43366400, 43366400]
def sufPList : List ℕ := [111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 111771863510, 107878759295, 105847278991, 103847468022, 101879078022, 99941485036, 98034226988, 96156824747, 94308966827, 92490142027, 90699821707, 88937742403, 87203438755, 85496429437, 83816409237, 82162963742, 80535761438, 78934262195, 77358303731, 75807317756, 74281118652, 72779310547, 71301484411, 69847319721, 68416586921, 67008840779, 65623829907, 64261188838, 62920750294, 61602022169, 60304711037, 59028727280, 57773544752, 56539056147, 55324930047, 54130824708, 52956608436, 51801921279, 50666392755, 49550090680, 48452402872, 47373270234, 46312514694, 45269721540, 44244811940, 43237469637, 42247486341, 41274646760, 40318610216, 39379383941, 38456613013, 37550174061, 36659696349, 35785165169, 34926317669, 34082883623, 33254709287, 32441635562, 31643497958, 30860000533, 30091093221, 29336595141, 28596191713, 27869818397, 27157277597, 26458366074, 25773005954, 25100984054, 24442081446, 23796206646, 23163264546, 22543021701, 21935238789, 21339942897, 20756885797, 20185950929, 19626879569, 19079824341, 18544379013, 18020410263, 17508063639, 17006774656, 16516825420, 16037782685, 15569782285, 15112379974, 14665706610, 14229600213, 13803894741, 13388568291, 12983299171, 12588058780, 12202967228, 11827539827, 11461891427, 11105831578, 10759319258, 10422157091, 10094298659, 9775695609, 9466297641, 9165737278, 8874115514, 8591215337, 8316495337, 8050048080, 7791481680, 7540397366, 7297042310, 7060846310, 6831559434, 6609258476, 6393687596, 6184586346, 5981857746, 5785064781, 5594442269, 5409545473, 5230265257, 5056490232, 4887933688, 4724825806, 4566525862, 4413261109, 4264555909, 4120636217, 3981196445, 3846105050, 3715228122, 3588429372, 3465751596, 3346873088, 3231833536, 3120304690, 3012507990, 2908110308, 2807146724, 2709277466, 2614722754, 2523137854, 2434743214, 2348998133, 2266121525, 2185949589, 2108509589, 2033634404, 1961154360, 1891289716, 1823474932, 1758126682, 1695070310, 1633928756, 1574921780, 1518070298, 1462990298, 1409902637, 1358418029, 1308962660, 1261143748, 1214977173, 1170478869, 1127455975, 1085922703, 1045893313, 1007382113, 969978417, 934119825, 899392047, 866021167, 833803642, 802967490, 772871208, 744179064, 716244017, 689515117, 663781561, 638829753, 614890750, 591973798, 569862548, 548337828, 527860218, 507982110, 488938507, 470506507, 452923071, 435963419, 419633189, 403938037, 388648412, 374004260, 360011289, 346675225, 333762691, 321277491, 309223441, 297604369, 286667164, 275929580, 265638530, 255797890, 246411548, 237235400, 228520365, 220020365, 211988333, 204176209, 196838948, 189726500, 182840825, 176183889, 169757664, 163564128, 157864346, 152142146, 146658605, 141415725, 136415514, 131659986, 127151161, 122624809, 118348185, 114323325, 110282910, 106497310, 102968577, 99426285, 96143937, 92849025, 89817150, 86773714, 83996424, 81208584, 78690015, 76161915, 73624266, 71360074, 69087362, 67091270, 65087695, 63076623, 61058040, 59321376, 57578250, 55828650, 54365245, 52602661, 51128416, 49648736, 48460636, 46970056, 45773220, 44572004, 43366400, 43366400]

def checkMono : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => a ≥ b && checkMono (b :: t)

def checkSuf : ℕ → List ℕ → List ℕ → Bool
  | _, [_], [_] => true
  | k, a :: b :: ft, sa :: sb :: st =>
    a ≥ b && sa == sb + (a - b) * (185 + k + 1) ^ 2 && checkSuf (k + 1) (b :: ft) (sb :: st)
  | _, _, _ => false

def checkRecM : ℕ → List ℕ → List ℕ → List ℕ → Bool
  | _, [], [], [] => true
  | j, m :: mt, f :: ft, s :: st =>
    (j < 62 || 1001 * s ≤ 1000 * (185 + j) ^ 2 * (m + f)) && checkRecM (j + 1) mt ft st
  | _, _, _, _ => false

def checkRecP : ℕ → List ℕ → List ℕ → List ℕ → Bool
  | _, [], [], [] => true
  | j, p :: pt, f :: ft, s :: st =>
    1001 * s ≤ 1000 * (185 + j) ^ 2 * (p + f) && checkRecP (j + 1) pt ft st
  | _, _, _, _ => false

def checkFmMatch : ℕ → ℕ → List ℕ → List ℕ → Bool
  | _, _, [], _ => true
  | _, _, [_], _ => true
  | k, p0, f :: ft, ps =>
    if k < 50 then p0 ≤ f && checkFmMatch (k + 1) p0 ft ps
    else match ps with
      | p :: pt => p ≤ f && checkFmMatch (k + 1) p0 ft pt
      | [] => false

def checkFpMatch : ℕ → List ℕ → List ℕ → Bool
  | _, [], _ => true
  | _, [_], _ => true
  | k, f :: ft, ms =>
    if k < 53 then 1000000 ≤ f && checkFpMatch (k + 1) ft ms
    else match ms with
      | m :: mt => m ≤ f && checkFpMatch (k + 1) ft mt
      | [] => false

def checkTail : ℕ → List ℕ → List ℕ → Bool
  | _, [], [] => true
  | j, m :: mt, p :: pt =>
    m * (185 + j + 1) ^ 10 ≤ 1115309257843 * 50 ^ 10 &&
    p * (185 + j + 1) ^ 10 ≤ 1115309257843 * 50 ^ 10 &&
    checkTail (j + 1) mt pt
  | _, _, _ => false

set_option maxRecDepth 32768 in
private lemma h_monoM : checkMono tabMList = true := by decide
set_option maxRecDepth 32768 in
private lemma h_monoP : checkMono tabPList = true := by decide
set_option maxRecDepth 32768 in
private lemma h_sufM : checkSuf 0 fmList sufMList = true := by decide
set_option maxRecDepth 32768 in
private lemma h_sufP : checkSuf 0 fpList sufPList = true := by decide
set_option maxRecDepth 32768 in
private lemma h_recM : checkRecM 0 tabMList fmList.dropLast sufMList.dropLast = true := by decide
set_option maxRecDepth 32768 in
private lemma h_recP : checkRecP 0 tabPList fpList.dropLast sufPList.dropLast = true := by decide
set_option maxRecDepth 32768 in
private lemma h_fm : checkFmMatch 0 (tabPList.getD 0 0) fmList tabPList = true := by decide
set_option maxRecDepth 32768 in
private lemma h_fp : checkFpMatch 0 fpList (tabMList.drop 3) = true := by decide
private lemma h_tail : checkTail 315 (tabMList.drop 315) (tabPList.drop 315) = true := by decide
set_option maxRecDepth 32768 in
private lemma h_lenM : tabMList.length = 365 := by decide
set_option maxRecDepth 32768 in
private lemma h_lenP : tabPList.length = 365 := by decide
set_option maxRecDepth 32768 in
private lemma h_lenFm : fmList.length = 366 := by decide
set_option maxRecDepth 32768 in
private lemma h_lenFp : fpList.length = 366 := by decide
set_option maxRecDepth 32768 in
private lemma h_lenSufM : sufMList.length = 366 := by decide
set_option maxRecDepth 32768 in
private lemma h_lenSufP : sufPList.length = 366 := by decide
private lemma h_m0_eq : tabMList.getD 0 0 = 1000000 := by decide
set_option maxRecDepth 32768 in
private lemma h_m64_le : tabMList.getD 64 0 ≤ 920000 := by decide
set_option maxRecDepth 32768 in
private lemma h_m364_eq : tabMList.getD 364 0 = 43 := by decide
set_option maxRecDepth 32768 in
private lemma h_p364_eq : tabPList.getD 364 0 = 43 := by decide
set_option maxRecDepth 32768 in
private lemma h_fm_last : fmList.getD 365 0 = 112 := by decide
set_option maxRecDepth 32768 in
private lemma h_fp_last : fpList.getD 365 0 = 112 := by decide
set_option maxRecDepth 32768 in
private lemma h_sufM_last : sufMList.getD 365 0 = 112 * 387200 := by decide
set_option maxRecDepth 32768 in
private lemma h_sufP_last : sufPList.getD 365 0 = 112 * 387200 := by decide
private lemma h_Ftail_ge : 1115309257843 ≤ 112 * 10 ^ 10 := by decide
private lemma h_A_le_11 : 1115309257843 = 43 * 11 ^ 10 := by decide

def A_num_nat : ℕ := 1115309257843
def k_tail_nat : ℕ := 43
def F_tail_nat : ℕ := 112


private lemma checkMono_getD : ∀ (l : List ℕ), checkMono l = true →
    ∀ i j, i ≤ j → j < l.length → l.getD j 0 ≤ l.getD i 0 := by
  intro l
  induction l with
  | nil => intro _ i j _ hj; simp at hj
  | cons a t ih =>
    cases t with
    | nil =>
      intro _ i j hij hj
      simp only [List.length_cons, List.length_nil] at hj
      have hi : i = 0 := by omega
      have hje : j = 0 := by omega
      subst hi; subst hje; simp
    | cons b t' =>
      intro h i j hij hj
      simp only [checkMono, Bool.and_eq_true, decide_eq_true_eq] at h
      cases i with
      | zero =>
        cases j with
        | zero => simp
        | succ j' =>
          have h1 : (b :: t').getD j' 0 ≤ b := ih h.2 0 j' (Nat.zero_le _) (by simpa using hj)
          simpa using h1.trans h.1
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          simpa using ih h.2 i' j' (Nat.succ_le_succ_iff.mp hij) (by simpa using hj)

private lemma checkSuf_getD : ∀ (k : ℕ) (fl sl : List ℕ), checkSuf k fl sl = true →
    fl.length = sl.length →
    ∀ i, i + 1 < fl.length →
      fl.getD (i + 1) 0 ≤ fl.getD i 0 ∧
      sl.getD i 0 = sl.getD (i + 1) 0 + (fl.getD i 0 - fl.getD (i + 1) 0) * (185 + k + i + 1) ^ 2 := by
  intro k fl
  induction fl generalizing k with
  | nil => intro sl h; simp [checkSuf] at h
  | cons a ft ih =>
    intro sl h hlen i hi
    cases sl with
    | nil => simp at hlen
    | cons sa st =>
      cases ft with
      | nil => simp at hi
      | cons b ft' =>
        cases st with
        | nil => simp at hlen
        | cons sb st' =>
          simp only [checkSuf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
          cases i with
          | zero => simpa using h.1
          | succ i' =>
            have hrec := ih (k + 1) (sb :: st') h.2 (by simpa using hlen) i' (by simpa using hi)
            refine ⟨hrec.1, ?_⟩
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec.2

private lemma checkRecM_getD : ∀ (k : ℕ) (ms fs ss : List ℕ), checkRecM k ms fs ss = true →
    ∀ j < ms.length, 62 ≤ k + j →
      1001 * ss.getD j 0 ≤ 1000 * (185 + k + j) ^ 2 * (ms.getD j 0 + fs.getD j 0) := by
  intro k ms
  induction ms generalizing k with
  | nil => intro _ _ _ j hj; simp at hj
  | cons m mt ih =>
    intro fs ss h j hj h62
    cases fs with
    | nil => simp [checkRecM] at h
    | cons f ft =>
      cases ss with
      | nil => simp [checkRecM] at h
      | cons s st =>
        simp only [checkRecM, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        cases j with
        | zero =>
          rcases h.1 with hlt | hle
          · omega
          · simpa using hle
        | succ j' =>
          have := ih (k + 1) ft st h.2 j' (by simpa using hj) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private lemma checkRecP_getD : ∀ (k : ℕ) (ps fs ss : List ℕ), checkRecP k ps fs ss = true →
    ∀ j < ps.length,
      1001 * ss.getD j 0 ≤ 1000 * (185 + k + j) ^ 2 * (ps.getD j 0 + fs.getD j 0) := by
  intro k ps
  induction ps generalizing k with
  | nil => intro _ _ _ j hj; simp at hj
  | cons p pt ih =>
    intro fs ss h j hj
    cases fs with
    | nil => simp [checkRecP] at h
    | cons f ft =>
      cases ss with
      | nil => simp [checkRecP] at h
      | cons s st =>
        simp only [checkRecP, Bool.and_eq_true, decide_eq_true_eq] at h
        cases j with
        | zero => simpa using h.1
        | succ j' =>
          have := ih (k + 1) ft st h.2 j' (by simpa using hj)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private lemma checkFmMatch_getD : ∀ (k p0 : ℕ) (fs ps : List ℕ), checkFmMatch k p0 fs ps = true →
    ∀ i, i + 1 < fs.length →
      (if k + i < 50 then p0 else ps.getD (k + i - max k 50) 0) ≤ fs.getD i 0 := by
  intro k p0 fs
  induction fs generalizing k with
  | nil => intro _ _ i hi; simp at hi
  | cons f ft ih =>
    intro ps h i hi
    cases ft with
    | nil => simp at hi
    | cons f2 ft' =>
      simp only [checkFmMatch] at h
      split_ifs at h with hk
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        cases i with
        | zero => simp [hk, h.1]
        | succ i' =>
          have hrec := ih (k + 1) ps h.2 i' (by simpa using hi)
          have hmax : max k 50 = 50 := Nat.max_eq_right (by omega)
          have hmax1 : max (k + 1) 50 = 50 := Nat.max_eq_right (by omega)
          rw [hmax]
          rw [hmax1] at hrec
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec
      · cases ps with
        | nil => simp at h
        | cons p pt =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          cases i with
          | zero =>
            have hnot : ¬ (k < 50) := by omega
            have hmax : max k 50 = k := Nat.max_eq_left (by omega)
            rw [Nat.add_zero, if_neg hnot, hmax, Nat.sub_self]
            simpa using h.1
          | succ i' =>
            have hrec := ih (k + 1) pt h.2 i' (by simpa using hi)
            have hnot : ¬ (k + (i' + 1) < 50) := by omega
            have hnot1 : ¬ ((k + 1) + i' < 50) := by omega
            have hmax : max k 50 = k := Nat.max_eq_left (by omega)
            have hmax1 : max (k + 1) 50 = k + 1 := Nat.max_eq_left (by omega)
            simp only [hnot, ↓reduceIte, hmax]
            simp only [hnot1, ↓reduceIte, hmax1] at hrec
            have hidx : k + (i' + 1) - k = i' + 1 := by omega
            have hidx1 : k + 1 + i' - (k + 1) = i' := by omega
            rw [hidx]
            rw [hidx1] at hrec
            simpa [List.getD_cons_succ] using hrec

private lemma checkFpMatch_getD : ∀ (k : ℕ) (fs ms : List ℕ), checkFpMatch k fs ms = true →
    ∀ i, i + 1 < fs.length →
      (if k + i < 53 then 1000000 else ms.getD (k + i - max k 53) 0) ≤ fs.getD i 0 := by
  intro k fs
  induction fs generalizing k with
  | nil => intro _ _ i hi; simp at hi
  | cons f ft ih =>
    intro ms h i hi
    cases ft with
    | nil => simp at hi
    | cons f2 ft' =>
      simp only [checkFpMatch] at h
      split_ifs at h with hk
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        cases i with
        | zero => simp [hk, h.1]
        | succ i' =>
          have hrec := ih (k + 1) ms h.2 i' (by simpa using hi)
          have hmax : max k 53 = 53 := Nat.max_eq_right (by omega)
          have hmax1 : max (k + 1) 53 = 53 := Nat.max_eq_right (by omega)
          rw [hmax]
          rw [hmax1] at hrec
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec
      · cases ms with
        | nil => simp at h
        | cons m mt =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          cases i with
          | zero =>
            have hnot : ¬ (k < 53) := by omega
            have hmax : max k 53 = k := Nat.max_eq_left (by omega)
            rw [Nat.add_zero, if_neg hnot, hmax, Nat.sub_self]
            simpa using h.1
          | succ i' =>
            have hrec := ih (k + 1) mt h.2 i' (by simpa using hi)
            have hnot : ¬ (k + (i' + 1) < 53) := by omega
            have hnot1 : ¬ ((k + 1) + i' < 53) := by omega
            have hmax : max k 53 = k := Nat.max_eq_left (by omega)
            have hmax1 : max (k + 1) 53 = k + 1 := Nat.max_eq_left (by omega)
            simp only [hnot, ↓reduceIte, hmax]
            simp only [hnot1, ↓reduceIte, hmax1] at hrec
            have hidx : k + (i' + 1) - k = i' + 1 := by omega
            have hidx1 : k + 1 + i' - (k + 1) = i' := by omega
            rw [hidx]
            rw [hidx1] at hrec
            simpa [List.getD_cons_succ] using hrec

private lemma checkTail_getD : ∀ (k : ℕ) (ms ps : List ℕ), checkTail k ms ps = true →
    ∀ d < ms.length,
      ms.getD d 0 * (185 + k + d + 1) ^ 10 ≤ A_num_nat * 50 ^ 10 ∧
      ps.getD d 0 * (185 + k + d + 1) ^ 10 ≤ A_num_nat * 50 ^ 10 := by
  intro k ms
  induction ms generalizing k with
  | nil => intro _ _ d hd; simp at hd
  | cons m mt ih =>
    intro ps h d hd
    cases ps with
    | nil => simp [checkTail] at h
    | cons p pt =>
      simp only [checkTail, Bool.and_eq_true, decide_eq_true_eq] at h
      cases d with
      | zero => exact ⟨h.1.1, h.1.2⟩
      | succ d' =>
        have hrec := ih (k + 1) pt h.2 d' (by simpa using hd)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

noncomputable def A_val : ℝ := (A_num_nat : ℝ) / 1000000
noncomputable def F_tail_val : ℝ := (F_tail_nat : ℝ) / 1000000

noncomputable def phiM (s : ℝ) : ℝ :=
  if s < 37 / 10 then 1
  else if s < 11 then (tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) / 1000000
  else A_val / s ^ 10

noncomputable def phiP (s : ℝ) : ℝ :=
  if s < 37 / 10 then (tabPList.getD 0 0 : ℝ) / 1000000
  else if s < 11 then (tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) / 1000000
  else A_val / s ^ 10

noncomputable def F_m (u : ℝ) : ℝ := phiP (u - 1)
noncomputable def F_p (u : ℝ) : ℝ := if u < 476 / 100 then 1 else phiM (u - 1)

private lemma idx_lt_365 {s : ℝ} (hs1 : 37 / 10 ≤ s) (hs2 : s < 11) :
    ⌊50 * (s - 37 / 10)⌋₊ < 365 := by
  rw [Nat.floor_lt (by linarith)]
  linarith

private lemma idx_bounds {s : ℝ} (hs1 : 37 / 10 ≤ s) (_hs2 : s < 11) :
    (185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ)) / 50 ≤ s ∧
    s < (185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) / 50 := by
  have h1 : (⌊50 * (s - 37 / 10)⌋₊ : ℝ) ≤ 50 * (s - 37 / 10) := Nat.floor_le (by linarith)
  have h2 : 50 * (s - 37 / 10) < (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor <;> linarith

private lemma phiM_nonneg (s : ℝ) : 0 ≤ phiM s := by
  unfold phiM A_val
  split_ifs <;> positivity

private lemma phiP_nonneg (s : ℝ) : 0 ≤ phiP s := by
  unfold phiP A_val
  split_ifs <;> positivity

private lemma phiM_antitone : Antitone phiM := by
  intro s₁ s₂ hle
  unfold phiM
  by_cases h1 : s₁ < 37 / 10
  · rw [if_pos h1]
    split_ifs with h2 h3
    · exact le_rfl
    · have hj : ⌊50 * (s₂ - 37 / 10)⌋₊ < 365 := idx_lt_365 (not_lt.mp h2) h3
      have hm := checkMono_getD tabMList h_monoM 0 ⌊50 * (s₂ - 37 / 10)⌋₊ (Nat.zero_le _) (by rw [h_lenM]; exact hj)
      rw [h_m0_eq] at hm
      have : (tabMList.getD ⌊50 * (s₂ - 37 / 10)⌋₊ 0 : ℝ) ≤ 1000000 := by exact_mod_cast hm
      linarith
    · have hs11 : (11 : ℝ) ≤ s₂ := not_lt.mp h3
      have hA : A_val / s₂ ^ 10 ≤ A_val / 11 ^ 10 := by
        apply div_le_div_of_nonneg_left (by unfold A_val; positivity) (by positivity)
        exact pow_le_pow_left₀ (by norm_num) hs11 10
      have h11 : A_val / 11 ^ 10 = (k_tail_nat : ℝ) / 1000000 := by
        unfold A_val
        have : (A_num_nat : ℝ) = (k_tail_nat : ℝ) * (11 : ℝ) ^ 10 := by norm_num [A_num_nat, k_tail_nat]
        rw [this]; ring
      rw [h11] at hA
      have hk : (k_tail_nat : ℝ) ≤ 1000000 := by norm_num [k_tail_nat]
      linarith
  · have hs1 : 37 / 10 ≤ s₁ := not_lt.mp h1
    have hs2 : 37 / 10 ≤ s₂ := hs1.trans hle
    rw [if_neg h1, if_neg (not_lt.mpr hs2)]
    by_cases h2 : s₂ < 11
    · have hs1_lt : s₁ < 11 := hle.trans_lt h2
      rw [if_pos hs1_lt, if_pos h2]
      have hj1 : ⌊50 * (s₁ - 37 / 10)⌋₊ ≤ ⌊50 * (s₂ - 37 / 10)⌋₊ := Nat.floor_mono (by linarith)
      have hj2 : ⌊50 * (s₂ - 37 / 10)⌋₊ < 365 := idx_lt_365 hs2 h2
      have hm := checkMono_getD tabMList h_monoM _ _ hj1 (by rw [h_lenM]; exact hj2)
      have hmR : (tabMList.getD ⌊50 * (s₂ - 37 / 10)⌋₊ 0 : ℝ) ≤ (tabMList.getD ⌊50 * (s₁ - 37 / 10)⌋₊ 0 : ℝ) := by
        exact_mod_cast hm
      linarith
    · rw [if_neg h2]
      have hs2_ge : (11 : ℝ) ≤ s₂ := not_lt.mp h2
      by_cases hs1_lt : s₁ < 11
      · rw [if_pos hs1_lt]
        have hj1 : ⌊50 * (s₁ - 37 / 10)⌋₊ ≤ 364 := by
          have := idx_lt_365 hs1 hs1_lt; omega
        have hm := checkMono_getD tabMList h_monoM _ 364 hj1 (by rw [h_lenM]; omega)
        rw [h_m364_eq] at hm
        have hA : A_val / s₂ ^ 10 ≤ A_val / 11 ^ 10 := by
          apply div_le_div_of_nonneg_left (by unfold A_val; positivity) (by positivity)
          exact pow_le_pow_left₀ (by norm_num) hs2_ge 10
        have h11 : A_val / 11 ^ 10 = (k_tail_nat : ℝ) / 1000000 := by
          unfold A_val
          have : (A_num_nat : ℝ) = (k_tail_nat : ℝ) * (11 : ℝ) ^ 10 := by norm_num [A_num_nat, k_tail_nat]
          rw [this]; ring
        have hmR : (k_tail_nat : ℝ) ≤ (tabMList.getD ⌊50 * (s₁ - 37 / 10)⌋₊ 0 : ℝ) := by exact_mod_cast hm
        linarith
      · rw [if_neg hs1_lt]
        apply div_le_div_of_nonneg_left (by unfold A_val; positivity) (pow_pos (by linarith) 10)
        exact pow_le_pow_left₀ (by linarith) hle 10

private lemma phiP_antitone : Antitone phiP := by
  intro s₁ s₂ hle
  unfold phiP
  by_cases h1 : s₁ < 37 / 10
  · rw [if_pos h1]
    split_ifs with h2 h3
    · exact le_rfl
    · have hj : ⌊50 * (s₂ - 37 / 10)⌋₊ < 365 := idx_lt_365 (not_lt.mp h2) h3
      have hp := checkMono_getD tabPList h_monoP 0 ⌊50 * (s₂ - 37 / 10)⌋₊ (Nat.zero_le _) (by rw [h_lenP]; exact hj)
      have hpR : (tabPList.getD ⌊50 * (s₂ - 37 / 10)⌋₊ 0 : ℝ) ≤ (tabPList.getD 0 0 : ℝ) := by exact_mod_cast hp
      linarith
    · have hs11 : (11 : ℝ) ≤ s₂ := not_lt.mp h3
      have hA : A_val / s₂ ^ 10 ≤ A_val / 11 ^ 10 := by
        apply div_le_div_of_nonneg_left (by unfold A_val; positivity) (by positivity)
        exact pow_le_pow_left₀ (by norm_num) hs11 10
      have h11 : A_val / 11 ^ 10 = (k_tail_nat : ℝ) / 1000000 := by
        unfold A_val
        have : (A_num_nat : ℝ) = (k_tail_nat : ℝ) * (11 : ℝ) ^ 10 := by norm_num [A_num_nat, k_tail_nat]
        rw [this]; ring
      have hp := checkMono_getD tabPList h_monoP 0 364 (Nat.zero_le _) (by rw [h_lenP]; omega)
      rw [h_p364_eq] at hp
      have hpR : (k_tail_nat : ℝ) ≤ (tabPList.getD 0 0 : ℝ) := by exact_mod_cast hp
      linarith
  · have hs1 : 37 / 10 ≤ s₁ := not_lt.mp h1
    have hs2 : 37 / 10 ≤ s₂ := hs1.trans hle
    rw [if_neg h1, if_neg (not_lt.mpr hs2)]
    by_cases h2 : s₂ < 11
    · have hs1_lt : s₁ < 11 := hle.trans_lt h2
      rw [if_pos hs1_lt, if_pos h2]
      have hj1 : ⌊50 * (s₁ - 37 / 10)⌋₊ ≤ ⌊50 * (s₂ - 37 / 10)⌋₊ := Nat.floor_mono (by linarith)
      have hj2 : ⌊50 * (s₂ - 37 / 10)⌋₊ < 365 := idx_lt_365 hs2 h2
      have hp := checkMono_getD tabPList h_monoP _ _ hj1 (by rw [h_lenP]; exact hj2)
      have hpR : (tabPList.getD ⌊50 * (s₂ - 37 / 10)⌋₊ 0 : ℝ) ≤ (tabPList.getD ⌊50 * (s₁ - 37 / 10)⌋₊ 0 : ℝ) := by
        exact_mod_cast hp
      linarith
    · rw [if_neg h2]
      have hs2_ge : (11 : ℝ) ≤ s₂ := not_lt.mp h2
      by_cases hs1_lt : s₁ < 11
      · rw [if_pos hs1_lt]
        have hj1 : ⌊50 * (s₁ - 37 / 10)⌋₊ ≤ 364 := by
          have := idx_lt_365 hs1 hs1_lt; omega
        have hp := checkMono_getD tabPList h_monoP _ 364 hj1 (by rw [h_lenP]; omega)
        rw [h_p364_eq] at hp
        have hA : A_val / s₂ ^ 10 ≤ A_val / 11 ^ 10 := by
          apply div_le_div_of_nonneg_left (by unfold A_val; positivity) (by positivity)
          exact pow_le_pow_left₀ (by norm_num) hs2_ge 10
        have h11 : A_val / 11 ^ 10 = (k_tail_nat : ℝ) / 1000000 := by
          unfold A_val
          have : (A_num_nat : ℝ) = (k_tail_nat : ℝ) * (11 : ℝ) ^ 10 := by norm_num [A_num_nat, k_tail_nat]
          rw [this]; ring
        have hpR : (k_tail_nat : ℝ) ≤ (tabPList.getD ⌊50 * (s₁ - 37 / 10)⌋₊ 0 : ℝ) := by exact_mod_cast hp
        linarith
      · rw [if_neg hs1_lt]
        apply div_le_div_of_nonneg_left (by unfold A_val; positivity) (pow_pos (by linarith) 10)
        exact pow_le_pow_left₀ (by linarith) hle 10

private lemma phiM_le_one (s : ℝ) : phiM s ≤ 1 := by
  by_cases hs : s < 37 / 10
  · simp [phiM, hs]
  · have h1 : phiM s ≤ phiM (37 / 10) := phiM_antitone (not_lt.mp hs)
    have h0 : phiM (37 / 10) = 1 := by
      unfold phiM
      rw [if_neg (by norm_num), if_pos (by norm_num),
        show ⌊50 * ((37 : ℝ) / 10 - 37 / 10)⌋₊ = 0 by norm_num, h_m0_eq]
      norm_num
    linarith

private lemma F_m_antitone : Antitone F_m :=
  fun _ _ h => phiP_antitone (by linarith)

private lemma F_p_antitone : Antitone F_p := by
  intro u₁ u₂ hle
  unfold F_p
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; exact h2 (hle.trans_lt h1)
  · exact phiM_le_one _
  · exact phiM_antitone (by linarith)

private lemma F_m_nonneg (u : ℝ) : 0 ≤ F_m u := phiP_nonneg _
private lemma F_p_nonneg (u : ℝ) : 0 ≤ F_p u := by
  unfold F_p; split_ifs <;> [norm_num; exact phiM_nonneg _]

private lemma getD_drop (l : List ℕ) (k i d : ℕ) : (l.drop k).getD i d = l.getD (k + i) d := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    cases l with
    | nil => simp
    | cons _ t =>
      simp only [List.drop_succ_cons, Nat.succ_add, List.getD_eq_getElem?_getD,
        List.getElem?_cons_succ]
      simp [List.getD_eq_getElem?_getD]

private lemma phiM_le_tail {s : ℝ} (hs : 10 ≤ s) : phiM s ≤ A_val / s ^ 10 := by
  by_cases hs11 : s < 11
  · unfold phiM
    rw [if_neg (by linarith), if_pos hs11]
    have hj_ge : 315 ≤ ⌊50 * (s - 37 / 10)⌋₊ := Nat.le_floor (by linarith)
    have hj_lt : ⌊50 * (s - 37 / 10)⌋₊ < 365 := idx_lt_365 (by linarith) hs11
    have ht := checkTail_getD 315 (tabMList.drop 315) (tabPList.drop 315) h_tail
      (⌊50 * (s - 37 / 10)⌋₊ - 315) (by simp [h_lenM]; omega)
    have ht1 : tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 * (185 + ⌊50 * (s - 37 / 10)⌋₊ + 1) ^ 10 ≤
        A_num_nat * 50 ^ 10 := by
      have hidx : (tabMList.drop 315).getD (⌊50 * (s - 37 / 10)⌋₊ - 315) 0 =
          tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 := by
        rw [getD_drop, show 315 + (⌊50 * (s - 37 / 10)⌋₊ - 315) = ⌊50 * (s - 37 / 10)⌋₊ by omega]
      rw [hidx] at ht
      have hadd : 185 + 315 + (⌊50 * (s - 37 / 10)⌋₊ - 315) + 1 = 185 + ⌊50 * (s - 37 / 10)⌋₊ + 1 := by omega
      rw [hadd] at ht
      exact ht.1
    have htR : (tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) *
        ((185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) / 50) ^ 10 ≤ (A_num_nat : ℝ) := by
      have htR0 : (tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) *
          (185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) ^ 10 ≤ (A_num_nat : ℝ) * 50 ^ 10 := by
        exact_mod_cast ht1
      rw [div_pow]
      linarith [show (A_num_nat : ℝ) * 50 ^ 10 / 50 ^ 10 = (A_num_nat : ℝ) by ring]
    have hsb := (idx_bounds (by linarith) hs11).2
    have hpow : s ^ 10 ≤ ((185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) / 50) ^ 10 :=
      pow_le_pow_left₀ (by linarith) hsb.le 10
    have h1 : (tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) * s ^ 10 ≤ (A_num_nat : ℝ) := by
      calc (tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) * s ^ 10
          ≤ (tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) *
            ((185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) / 50) ^ 10 :=
              mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
        _ ≤ (A_num_nat : ℝ) := htR
    unfold A_val
    rw [div_div, le_div_iff₀ (by positivity)]
    linarith
  · unfold phiM
    rw [if_neg (by linarith), if_neg hs11]

private lemma phiP_le_tail {s : ℝ} (hs : 10 ≤ s) : phiP s ≤ A_val / s ^ 10 := by
  by_cases hs11 : s < 11
  · unfold phiP
    rw [if_neg (by linarith), if_pos hs11]
    have hj_ge : 315 ≤ ⌊50 * (s - 37 / 10)⌋₊ := Nat.le_floor (by linarith)
    have hj_lt : ⌊50 * (s - 37 / 10)⌋₊ < 365 := idx_lt_365 (by linarith) hs11
    have ht := checkTail_getD 315 (tabMList.drop 315) (tabPList.drop 315) h_tail
      (⌊50 * (s - 37 / 10)⌋₊ - 315) (by simp [h_lenM]; omega)
    have ht1 : tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 * (185 + ⌊50 * (s - 37 / 10)⌋₊ + 1) ^ 10 ≤
        A_num_nat * 50 ^ 10 := by
      have hidx : (tabPList.drop 315).getD (⌊50 * (s - 37 / 10)⌋₊ - 315) 0 =
          tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 := by
        rw [getD_drop, show 315 + (⌊50 * (s - 37 / 10)⌋₊ - 315) = ⌊50 * (s - 37 / 10)⌋₊ by omega]
      rw [hidx] at ht
      have hadd : 185 + 315 + (⌊50 * (s - 37 / 10)⌋₊ - 315) + 1 = 185 + ⌊50 * (s - 37 / 10)⌋₊ + 1 := by omega
      rw [hadd] at ht
      exact ht.2
    have htR : (tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) *
        ((185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) / 50) ^ 10 ≤ (A_num_nat : ℝ) := by
      have htR0 : (tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) *
          (185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) ^ 10 ≤ (A_num_nat : ℝ) * 50 ^ 10 := by
        exact_mod_cast ht1
      rw [div_pow]
      linarith [show (A_num_nat : ℝ) * 50 ^ 10 / 50 ^ 10 = (A_num_nat : ℝ) by ring]
    have hsb := (idx_bounds (by linarith) hs11).2
    have hpow : s ^ 10 ≤ ((185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) / 50) ^ 10 :=
      pow_le_pow_left₀ (by linarith) hsb.le 10
    have h1 : (tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) * s ^ 10 ≤ (A_num_nat : ℝ) := by
      calc (tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) * s ^ 10
          ≤ (tabPList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 : ℝ) *
            ((185 + (⌊50 * (s - 37 / 10)⌋₊ : ℝ) + 1) / 50) ^ 10 :=
              mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
        _ ≤ (A_num_nat : ℝ) := htR
    unfold A_val
    rw [div_div, le_div_iff₀ (by positivity)]
    linarith
  · unfold phiP
    rw [if_neg (by linarith), if_neg hs11]

private lemma F_m_le_tail {u : ℝ} (hu : 11 ≤ u) : F_m u ≤ A_val / (u - 1) ^ 10 :=
  phiP_le_tail (by linarith)

private lemma F_p_le_tail {u : ℝ} (hu : 11 ≤ u) : F_p u ≤ A_val / (u - 1) ^ 10 := by
  unfold F_p
  rw [if_neg (by linarith)]
  exact phiM_le_tail (by linarith)

private lemma F_m_le_grid {k : ℕ} (hk : k < 365) {u : ℝ}
    (hu1 : (185 + (k : ℝ)) / 50 ≤ u) (hu2 : u < (185 + (k : ℝ) + 1) / 50) :
    F_m u ≤ (fmList.getD k 0 : ℝ) / 1000000 := by
  unfold F_m
  have hfm_k := checkFmMatch_getD 0 (tabPList.getD 0 0) fmList tabPList h_fm k (by rw [h_lenFm]; omega)
  simp only [Nat.zero_add, max_eq_right (Nat.zero_le 50)] at hfm_k
  have hu_lt : u - 1 < 11 := by linarith [show (k : ℝ) ≤ 364 by exact_mod_cast (by omega : k ≤ 364)]
  by_cases h50 : k < 50
  · have hu1_lt : u - 1 < 37 / 10 := by
      have : (k : ℝ) + 1 ≤ 50 := by exact_mod_cast h50
      linarith
    have hphi : phiP (u - 1) = (tabPList.getD 0 0 : ℝ) / 1000000 := by simp [phiP, hu1_lt]
    rw [hphi]
    rw [if_pos h50] at hfm_k
    exact div_le_div_of_nonneg_right (by exact_mod_cast hfm_k) (by norm_num)
  · have hu1_ge : 37 / 10 ≤ u - 1 := by
      have : (50 : ℝ) ≤ k := by exact_mod_cast (not_lt.mp h50)
      linarith
    have hidx : ⌊50 * ((u - 1) - 37 / 10)⌋₊ = k - 50 := by
      rw [Nat.floor_eq_iff (by linarith)]
      have h50R : ((k - 50 : ℕ) : ℝ) = (k : ℝ) - 50 := by
        exact_mod_cast Nat.cast_sub (not_lt.mp h50)
      rw [h50R]
      constructor <;> linarith
    have hphi : phiP (u - 1) = (tabPList.getD (k - 50) 0 : ℝ) / 1000000 := by
      unfold phiP
      rw [if_neg (not_lt.mpr hu1_ge), if_pos hu_lt, hidx]
    rw [hphi]
    rw [if_neg h50] at hfm_k
    exact div_le_div_of_nonneg_right (by exact_mod_cast hfm_k) (by norm_num)

private lemma F_p_le_grid {k : ℕ} (hk : k < 365) {u : ℝ}
    (hu1 : (185 + (k : ℝ)) / 50 ≤ u) (hu2 : u < (185 + (k : ℝ) + 1) / 50) :
    F_p u ≤ (fpList.getD k 0 : ℝ) / 1000000 := by
  unfold F_p
  have hfp_k := checkFpMatch_getD 0 fpList (tabMList.drop 3) h_fp k (by rw [h_lenFp]; omega)
  simp only [Nat.zero_add, max_eq_right (Nat.zero_le 53)] at hfp_k
  by_cases h53 : k < 53
  · rw [if_pos h53] at hfp_k
    have hf1 : (1 : ℝ) ≤ (fpList.getD k 0 : ℝ) / 1000000 := by
      have : (1000000 : ℝ) ≤ (fpList.getD k 0 : ℝ) := by exact_mod_cast hfp_k
      linarith
    split_ifs
    · exact hf1
    · exact (phiM_le_one _).trans hf1
  · have hu_ge : 476 / 100 ≤ u := by
      have : (53 : ℝ) ≤ k := by exact_mod_cast (not_lt.mp h53)
      linarith
    rw [if_neg (not_lt.mpr hu_ge)]
    have hu1_ge : 37 / 10 ≤ u - 1 := by linarith
    have hu1_lt : u - 1 < 11 := by
      have : (k : ℝ) ≤ 364 := by exact_mod_cast (by omega : k ≤ 364)
      linarith
    have hidx : ⌊50 * ((u - 1) - 37 / 10)⌋₊ = k - 50 := by
      rw [Nat.floor_eq_iff (by linarith)]
      have h50R : ((k - 50 : ℕ) : ℝ) = (k : ℝ) - 50 := by
        exact_mod_cast Nat.cast_sub (by omega)
      rw [h50R]
      constructor <;> linarith
    have hphi : phiM (u - 1) = (tabMList.getD (k - 50) 0 : ℝ) / 1000000 := by
      unfold phiM
      rw [if_neg (not_lt.mpr hu1_ge), if_pos hu1_lt, hidx]
    rw [hphi]
    rw [if_neg h53] at hfp_k
    have hdrop : (tabMList.drop 3).getD (k - 53) 0 = tabMList.getD (k - 50) 0 := by
      rw [getD_drop, show 3 + (k - 53) = k - 50 by omega]
    rw [hdrop] at hfp_k
    exact div_le_div_of_nonneg_right (by exact_mod_cast hfp_k) (by norm_num)

/- ## Section 2: Elementary Mertens First Theorem and Prime Product Bound -/

private lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.add_one_le_exp (-1 / 2 : ℝ)
  have h1 : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg] at h
    linarith
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    calc Real.exp (1 / 2) = ((Real.exp (1 / 2))⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 2 := by norm_num
  calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
    _ ≤ Real.log 2 := Real.log_le_log (Real.exp_pos _) h2

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

private lemma log_factorial_bounds : ∀ n : ℕ, 1 ≤ n →
    (n : ℝ) * Real.log n - n ≤ Real.log (Nat.factorial n : ℝ) ∧
    Real.log (Nat.factorial n : ℝ) ≤ (n + 1 : ℝ) * Real.log (n + 1) - n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [Nat.factorial_one, Nat.cast_one, Real.log_one, one_mul, zero_sub]
    constructor
    · linarith
    · have := log_two_ge_half
      norm_num
      linarith
  | succ n hn ih =>
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    have hfac : Real.log (Nat.factorial (n + 1) : ℝ) = Real.log (n + 1 : ℝ) + Real.log (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul]
      · push_cast; rfl
      · positivity
      · exact_mod_cast (Nat.factorial_pos n).ne'
    have h_ub_step : (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      rw [Real.log_div hn1_pos.ne' hn_pos.ne'] at h
      have : (((n : ℝ) + 1) / n - 1) * n = 1 := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_right h hn_pos.le]
    have h_lb_step : 1 ≤ ((n : ℝ) + 2) * (Real.log (n + 2) - Real.log (n + 1)) := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((n : ℝ) + 2) / (n + 1) by positivity)
      rw [Real.log_div hn2_pos.ne' hn1_pos.ne', inv_div] at h
      have : (1 - ((n : ℝ) + 1) / (n + 2)) * ((n : ℝ) + 2) = 1 := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_right h hn2_pos.le]
    rw [hfac]
    push_cast
    rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 by ring]
    constructor <;> linarith [ih.1, ih.2]

private lemma inv_sqrt_sub_ge (m : ℕ) (hm : 2 ≤ m) :
    (1 : ℝ) / (2 * (m : ℝ) * Real.sqrt m) ≤
      1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ) := by
  have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    have : 1 ≤ m - 1 := by omega
    exact_mod_cast this
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set u := Real.sqrt ((m - 1 : ℕ) : ℝ)
  set v := Real.sqrt (m : ℝ)
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hm1_pos
  have hv_pos : 0 < v := Real.sqrt_pos.mpr hm_pos
  have huv_sq : v ^ 2 - u ^ 2 = 1 := by
    rw [Real.sq_sqrt hm_pos.le, Real.sq_sqrt hm1_pos.le]
    have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega)
    linarith
  have hle : u ≤ v := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le m 1)
  have hsub : v - u = 1 / (v + u) := by
    have hvup : v + u ≠ 0 := by linarith
    field_simp
    linarith
  have h1 : 1 / u - 1 / v = 1 / (u * v * (v + u)) := by
    rw [div_sub_div _ _ hu_pos.ne' hv_pos.ne', one_mul, mul_one, hsub]
    field_simp
  rw [h1]
  have hden : u * v * (v + u) ≤ 2 * (m : ℝ) * v := by
    have hvu : v + u ≤ 2 * v := by linarith
    calc u * v * (v + u) ≤ v * v * (2 * v) := by gcongr
      _ = 2 * v ^ 2 * v := by ring
      _ = 2 * (m : ℝ) * v := by rw [Real.sq_sqrt hm_pos.le]
  exact one_div_le_one_div_of_le (by positivity) hden

private lemma sum_log_prime_div_mul_sub_one_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1)) ≤ 8 := by
  have hterm : ∀ p ∈ Nat.primesLE n,
      Real.log p / ((p : ℝ) * (p - 1)) ≤
        8 * (1 / Real.sqrt ((p - 1 : ℕ) : ℝ) - 1 / Real.sqrt (p : ℝ)) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hp2 : 2 ≤ p := hp_prime.two_le
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp_pos
    have hlog : Real.log p ≤ 2 * Real.sqrt p := by
      have h := Real.log_le_sub_one_of_pos hsqrt_pos
      have hsq : Real.log p = 2 * Real.log (Real.sqrt p) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.log_pow, Real.sq_sqrt hp_pos.le]
      linarith
    have hden : (p : ℝ) ^ 2 / 2 ≤ (p : ℝ) * (p - 1) := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      nlinarith
    calc Real.log p / ((p : ℝ) * (p - 1))
        ≤ (2 * Real.sqrt p) / ((p : ℝ) ^ 2 / 2) := by
          apply div_le_div₀ (by positivity) hlog (by positivity) hden
      _ = 4 / ((p : ℝ) * Real.sqrt p) := by
          have : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp_pos.le
          field_simp
          nlinarith
      _ = 8 * (1 / (2 * (p : ℝ) * Real.sqrt p)) := by ring
      _ ≤ 8 * (1 / Real.sqrt ((p - 1 : ℕ) : ℝ) - 1 / Real.sqrt (p : ℝ)) := by
          gcongr
          exact inv_sqrt_sub_ge p hp2
  have hsub : Nat.primesLE n ⊆ Finset.Icc 2 n := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesLE hp).two_le, Nat.le_of_mem_primesLE hp⟩
  have hnonneg : ∀ m ∈ Finset.Icc 2 n,
      0 ≤ 8 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have h1 := inv_sqrt_sub_ge m hm2
    have h2 : (0 : ℝ) ≤ 1 / (2 * (m : ℝ) * Real.sqrt m) := by positivity
    linarith
  calc ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1))
      ≤ ∑ p ∈ Nat.primesLE n, 8 * (1 / Real.sqrt ((p - 1 : ℕ) : ℝ) - 1 / Real.sqrt (p : ℝ)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ Finset.Icc 2 n, 8 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => hnonneg m hm
    _ = 8 * ∑ m ∈ Finset.Icc 2 n, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 8 * 1 := by
        gcongr
        cases n with
        | zero => simp
        | succ n' =>
          cases n' with
          | zero => simp
          | succ m' =>
            have htel : ∀ k : ℕ, 1 ≤ k →
                ∑ m ∈ Finset.Icc 2 (k + 1),
                  (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) =
                1 - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) := by
              intro k hk
              induction k, hk using Nat.le_induction with
              | base => simp
              | succ k hk ih =>
                rw [Finset.sum_Icc_succ_top (by omega), ih]
                simp only [Nat.add_sub_cancel]
                ring
            rw [htel (m' + 1) (by omega)]
            have : (0 : ℝ) ≤ 1 / Real.sqrt (((m' + 1 + 1 : ℕ) : ℝ)) := by positivity
            linarith
    _ = 8 := by ring

private lemma mertens_first (n : ℕ) (hn : 1 ≤ n) :
    |∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) - Real.log n| ≤ 9 := by
  have hfac_log : Real.log (Nat.factorial n : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((Nat.factorial n).factorization p : ℝ) * Real.log p := by
    have hpos : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hpos]
    rw [Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · have hpf : (Nat.factorial n).factorization.support = Nat.primesLE n := by
        ext p
        rw [Nat.support_factorization, Nat.mem_primeFactors, Nat.mem_primesLE]
        refine ⟨fun ⟨hp, hd, _⟩ => ⟨hp.dvd_factorial.mp hd, hp⟩,
               fun ⟨hle, hp⟩ => ⟨hp, hp.dvd_factorial.mpr hle, hpos⟩⟩
      rw [hpf]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp (by rwa [← Nat.support_factorization])).1
      exact_mod_cast pow_ne_zero _ hp_prime.ne_zero
  have hsum_k : ∀ p ∈ Nat.primesLE n,
      ((Nat.factorial n).factorization p : ℝ) =
        (n / p : ℕ) + ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hlog : Nat.log p n < n + 1 := Nat.lt_succ_of_le (Nat.log_le_self p n)
    rw [Nat.factorization_factorial hp_prime hlog]
    have hsplit : ∑ i ∈ Finset.Ico 1 (n + 1), n / p ^ i =
        n / p + ∑ i ∈ Finset.Icc 2 (n + 1), n / p ^ i := by
      have h1 : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ico 2 (n + 1)) := by
        ext x; simp; omega
      have h3 : ∑ i ∈ Finset.Icc 2 (n + 1), n / p ^ i =
          ∑ i ∈ Finset.Ico 2 (n + 1), n / p ^ i + n / p ^ (n + 1) := by
        have : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Ico 2 (n + 1)) := by
          ext x; simp; omega
        rw [this, Finset.sum_insert (by simp), add_comm]
      have hzero : n / p ^ (n + 1) = 0 := by
        apply Nat.div_eq_of_lt
        have : 2 ≤ p := hp_prime.two_le
        calc n < 2 ^ (n + 1) := (Nat.lt_pow_succ_log_self (by norm_num) n).trans_le
              (Nat.pow_le_pow_right (by norm_num) (by have := Nat.log_le_self 2 n; omega))
          _ ≤ p ^ (n + 1) := Nat.pow_le_pow_left this _
      rw [h1, Finset.sum_insert (by simp), pow_one, h3, hzero, add_zero]
    rw [hsplit]
    push_cast
    rfl
  set S : ℝ := ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)
  have hS_lower : (n : ℝ) * S - Chebyshev.theta n ≤ Real.log (Nat.factorial n : ℝ) := by
    rw [hfac_log, Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
    have hdiv : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
      have hmod : (n / p : ℕ) * p + n % p = n := Nat.div_add_mod' n p
      have hmod_lt : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hp_prime.pos
      have hmodR : ((n / p : ℕ) : ℝ) * p + ((n % p : ℕ) : ℝ) = n := by exact_mod_cast hmod
      have heq : (n : ℝ) / p = ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) / p := by field_simp; linarith
      have hlt1 : ((n % p : ℕ) : ℝ) / p < 1 := (div_lt_one hp_pos).mpr hmod_lt
      linarith
    have hfac_ge : ((n / p : ℕ) : ℝ) ≤ ((Nat.factorial n).factorization p : ℝ) := by
      rw [hsum_k p hp]
      have : 0 ≤ ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) :=
        Finset.sum_nonneg fun _ _ => by positivity
      linarith
    have := mul_le_mul_of_nonneg_right (hdiv.trans hfac_ge) hlog_nn
    linarith [show (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p by ring]
  have hS_upper : Real.log (Nat.factorial n : ℝ) ≤ (n : ℝ) * S + 8 * n := by
    have h1 : Real.log (Nat.factorial n : ℝ) ≤ (n : ℝ) * S +
        (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1)) := by
      rw [hfac_log, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primesLE hp
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
        linarith
      have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
      rw [hsum_k p hp, add_mul]
      have hterm1 : ((n / p : ℕ) : ℝ) * Real.log p ≤ (n : ℝ) * (Real.log p / p) := by
        have hdiv : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := by
          rw [le_div_iff₀ hp_pos]
          exact_mod_cast Nat.div_mul_le_self n p
        calc ((n / p : ℕ) : ℝ) * Real.log p ≤ ((n : ℝ) / p) * Real.log p :=
              mul_le_mul_of_nonneg_right hdiv hlog_nn
          _ = (n : ℝ) * (Real.log p / p) := by ring
      have hterm2 : (∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ)) * Real.log p ≤
          (n : ℝ) * (Real.log p / ((p : ℝ) * (p - 1))) := by
        have hgeom : ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) ≤
            (n : ℝ) / ((p : ℝ) * (p - 1)) := by
          have hsub : ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) ≤
              (n : ℝ) * ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun k _ => ?_
            rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hp_pos k)]
            exact_mod_cast Nat.div_mul_le_self n (p ^ k)
          have hgeom_sum : ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k ≤
              1 / ((p : ℝ) * (p - 1)) := by
            have hshift : ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k =
                (1 / (p : ℝ)) ^ 2 * ∑ j ∈ Finset.range n, (1 / (p : ℝ)) ^ j := by
              rw [Finset.mul_sum]
              refine Finset.sum_bij (fun k _ => k - 2) ?_ ?_ ?_ ?_
              · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
              · intro a ha b hb hab; rw [Finset.mem_Icc] at ha hb; omega
              · intro j hj; rw [Finset.mem_range] at hj
                refine ⟨j + 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro k hk
                rw [Finset.mem_Icc] at hk
                rw [← pow_add, show 2 + (k - 2) = k by omega]
            rw [hshift]
            have hr_lt : (1 / (p : ℝ)) < 1 := by
              rw [div_lt_one hp_pos]
              exact_mod_cast hp_prime.one_lt
            have hg2 : ∑ j ∈ Finset.range n, (1 / (p : ℝ)) ^ j ≤ 1 / (1 - 1 / (p : ℝ)) := by
              rw [geom_sum_eq hr_lt.ne]
              have hnum : 0 ≤ (1 / (p : ℝ)) ^ n := by positivity
              have h1m : 0 < 1 - 1 / (p : ℝ) := by linarith
              have hs1 : (1 / (p : ℝ)) ^ n - 1 = -(1 - (1 / (p : ℝ)) ^ n) := by ring
              have hs2 : 1 / (p : ℝ) - 1 = -(1 - 1 / (p : ℝ)) := by ring
              rw [hs1, hs2, neg_div_neg_eq]
              exact div_le_div_of_nonneg_right (by linarith) h1m.le
            calc (1 / (p : ℝ)) ^ 2 * ∑ j ∈ Finset.range n, (1 / (p : ℝ)) ^ j
                ≤ (1 / (p : ℝ)) ^ 2 * (1 / (1 - 1 / (p : ℝ))) := by gcongr
              _ = 1 / ((p : ℝ) * (p - 1)) := by field_simp
          calc ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ)
              ≤ (n : ℝ) * ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k := hsub
            _ ≤ (n : ℝ) * (1 / ((p : ℝ) * (p - 1))) := by gcongr
            _ = (n : ℝ) / ((p : ℝ) * (p - 1)) := by ring
        calc (∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ)) * Real.log p
            ≤ ((n : ℝ) / ((p : ℝ) * (p - 1))) * Real.log p :=
              mul_le_mul_of_nonneg_right hgeom hlog_nn
          _ = (n : ℝ) * (Real.log p / ((p : ℝ) * (p - 1))) := by ring
      linarith
    have h2 := sum_log_prime_div_mul_sub_one_le n
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hfac_b := log_factorial_bounds n hn
  have hth := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ n by positivity)
  have hth2 : Chebyshev.theta n ≤ 2 * (n : ℝ) := by
    have := log_four_le_two
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow : (n : ℝ) * Real.log n - 9 * n ≤ (n : ℝ) * S := by linarith
  have hup : (n : ℝ) * S ≤ (n : ℝ) * Real.log n + 4 * n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h_diff : ((n : ℝ) + 1) * Real.log (n + 1) - n ≤ (n : ℝ) * Real.log n + 1 + Real.log (n + 1) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      rw [Real.log_div (by linarith) hn_pos.ne'] at h
      have : (((n : ℝ) + 1) / n - 1) * n = 1 := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_right h hn_pos.le]
    have hlog_n1 : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n + 1)
      linarith
    linarith
  rw [abs_le]
  constructor <;> nlinarith

private lemma sum_Icc_by_parts (A B : ℕ) (hAB : A + 1 ≤ B) (S f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc (A + 1) B, (S n - S (n - 1)) * f n =
      S B * f B - S A * f (A + 1) +
        ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (f n - f (n + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
    have h2 : A + 1 - 1 < A + 1 := by omega
    rw [Finset.Icc_self, Finset.sum_singleton, Finset.Icc_eq_empty_of_lt h2, Finset.sum_empty]
    simp only [Nat.add_sub_cancel]
    ring
  | succ B hAB ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hB1 : (B + 1 - 1 : ℕ) = B := by omega
    have hsumB : ∑ n ∈ Finset.Icc (A + 1) B, S n * (f n - f (n + 1)) =
        ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (f n - f (n + 1)) +
          S B * (f B - f (B + 1)) := by
      have hB_eq : B = (B - 1) + 1 := by omega
      conv_lhs => rw [hB_eq, Finset.sum_Icc_succ_top (by omega)]
      rw [show (B - 1) + 1 = B by omega]
    rw [hB1, hsumB]
    ring

private lemma sum_inv_prime_Icc_le (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log B / Real.log A) + 19 / Real.log A := by
  rcases eq_or_lt_of_le hAB with rfl | hlt
  · have hlogB : Real.log (A : ℝ) > 0 := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
    have : Finset.Icc (A + 1) A = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [this, Finset.filter_empty, Finset.sum_empty, div_self hlogB.ne', Real.log_one, zero_add]
    positivity
  set S : ℕ → ℝ := fun n => ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)
  have hdiff : ∀ n : ℕ, 2 ≤ n →
      S n - S (n - 1) = if n.Prime then Real.log n / (n : ℝ) else 0 := by
    intro n hn
    have hsub : Nat.primesLE n =
        if n.Prime then insert n (Nat.primesLE (n - 1)) else Nat.primesLE (n - 1) := by
      ext p
      simp only [Nat.mem_primesLE]
      split_ifs with hnp
      · rw [Finset.mem_insert, Nat.mem_primesLE]
        constructor
        · rintro ⟨hle, hp⟩
          rcases eq_or_lt_of_le hle with rfl | hlt'
          · exact Or.inl rfl
          · exact Or.inr ⟨by omega, hp⟩
        · rintro (rfl | ⟨hle, hp⟩)
          · exact ⟨le_rfl, hnp⟩
          · exact ⟨by omega, hp⟩
      · constructor
        · rintro ⟨hle, hp⟩
          rw [Nat.mem_primesLE]
          refine ⟨?_, hp⟩
          by_contra hnot
          have : p = n := by omega
          subst this
          exact hnp hp
        · intro h
          rw [Nat.mem_primesLE] at h
          exact ⟨by omega, h.2⟩
    dsimp only [S]
    rw [hsub]
    split_ifs with hnp
    · rw [Finset.sum_insert]
      · simp
      · simp [Nat.mem_primesLE]; omega
    · simp
  have hsum_eq : ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, (1 : ℝ) / p =
      ∑ n ∈ Finset.Icc (A + 1) B, (S n - S (n - 1)) * (1 / Real.log n) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := by rw [Finset.mem_Icc] at hn; omega
    rw [hdiff n hn2]
    split_ifs with hnp
    · have hlog_ne : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hnp.one_lt)).ne'
      field_simp
    · simp
  rw [hsum_eq, sum_Icc_by_parts A B (by omega) S (fun n => 1 / Real.log n)]
  have hlogA_pos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hlogA1_pos : 0 < Real.log ((A + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < A + 1))
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hlogA_le_A1 : Real.log (A : ℝ) ≤ Real.log ((A + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : A ≤ A + 1))
  have hSB : S B * (1 / Real.log B) ≤ 1 + 9 / Real.log B := by
    have hm := (abs_le.mp (mertens_first B (by omega))).2
    have h1 := div_le_div_of_nonneg_right (by linarith : S B ≤ Real.log B + 9) hlogB_pos.le
    rw [add_div, div_self hlogB_pos.ne'] at h1
    linarith [show S B * (1 / Real.log B) = S B / Real.log B by ring]
  have hSA : - (S A * (1 / Real.log ((A + 1 : ℕ) : ℝ))) ≤
      - Real.log A / Real.log ((A + 1 : ℕ) : ℝ) + 9 / Real.log ((A + 1 : ℕ) : ℝ) := by
    have hm := (abs_le.mp (mertens_first A (by omega))).1
    have h1 := div_le_div_of_nonneg_right (by linarith : Real.log A - 9 ≤ S A) hlogA1_pos.le
    rw [sub_div] at h1
    rw [neg_div]
    linarith [show S A * (1 / Real.log ((A + 1 : ℕ) : ℝ)) = S A / Real.log ((A + 1 : ℕ) : ℝ) by ring]
  have hmid : ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) +
        9 * (1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log B) := by
    have hterm : ∀ n ∈ Finset.Icc (A + 1) (B - 1),
        S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
          (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) +
            9 * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
      intro n hn
      have hn3 : 3 ≤ n := by rw [Finset.mem_Icc] at hn; omega
      have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hlogn1_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
      have hdiff_nn : 0 ≤ 1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ) := by
        apply sub_nonneg.mpr
        apply one_div_le_one_div_of_le hlogn_pos
        exact Real.log_le_log (by positivity) (by push_cast; linarith)
      have hm := (abs_le.mp (mertens_first n (by omega))).2
      have h1 : S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
          (Real.log n + 9) * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hdiff_nn
      have h2 : Real.log n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
          Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ)) := by
        have h_log := Real.one_sub_inv_le_log_of_pos
          (show 0 < Real.log ((n + 1 : ℕ) : ℝ) / Real.log n by positivity)
        rw [Real.log_div hlogn1_pos.ne' hlogn_pos.ne', inv_div] at h_log
        have h_eq : Real.log n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
            1 - Real.log n / Real.log ((n + 1 : ℕ) : ℝ) := by
          field_simp
        linarith
      linarith
    have htel_log : ∑ n ∈ Finset.Icc (A + 1) (B - 1),
        (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) =
        Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) := by
      rw [Real.log_div hlogB_pos.ne' hlogA1_pos.ne']
      rcases eq_or_lt_of_le (show A + 1 ≤ B by omega) with h_eq | h_lt
      · have : B - 1 < A + 1 := by omega
        rw [Finset.Icc_eq_empty_of_lt this, Finset.sum_empty, h_eq, sub_self]
      · have hB_eq : B - 1 + 1 = B := by omega
        have hind : ∀ k : ℕ, A + 1 ≤ k →
            ∑ n ∈ Finset.Icc (A + 1) k,
              (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) =
            Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log ((A + 1 : ℕ) : ℝ)) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ k hk ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]
            ring
        rw [hind (B - 1) (by omega), hB_eq]
    have htel_inv : ∑ n ∈ Finset.Icc (A + 1) (B - 1), (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
        1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log B := by
      rcases eq_or_lt_of_le (show A + 1 ≤ B by omega) with h_eq | h_lt
      · have : B - 1 < A + 1 := by omega
        rw [Finset.Icc_eq_empty_of_lt this, Finset.sum_empty, h_eq, sub_self]
      · have hB_eq : B - 1 + 1 = B := by omega
        have hind : ∀ k : ℕ, A + 1 ≤ k →
            ∑ n ∈ Finset.Icc (A + 1) k, (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
            1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ k hk ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]
            ring
        rw [hind (B - 1) (by omega)]
        congr 1; simp [hB_eq]
    calc ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ))
        ≤ ∑ n ∈ Finset.Icc (A + 1) (B - 1),
            ((Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) +
              9 * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ))) := Finset.sum_le_sum hterm
      _ = Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) +
            9 * (1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log B) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, htel_log, htel_inv]
  have hlog_mono : Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log B / Real.log A) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left hlogB_pos.le hlogA_pos hlogA_le_A1
  have h_end : 1 - Real.log A / Real.log ((A + 1 : ℕ) : ℝ) ≤ 1 / Real.log A := by
    have hlog1 : Real.log ((A + 1 : ℕ) : ℝ) - Real.log A ≤ 1 / (A : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((A : ℝ) + 1) / A by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      push_cast
      linarith [show (((A : ℝ) + 1) / A - 1) = 1 / A by field_simp; ring]
    have h1 : 1 - Real.log A / Real.log ((A + 1 : ℕ) : ℝ) =
        (Real.log ((A + 1 : ℕ) : ℝ) - Real.log A) / Real.log ((A + 1 : ℕ) : ℝ) := by
      field_simp
    rw [h1]
    calc (Real.log ((A + 1 : ℕ) : ℝ) - Real.log A) / Real.log ((A + 1 : ℕ) : ℝ)
        ≤ (1 / (A : ℝ)) / Real.log A :=
          div_le_div₀ (by positivity) hlog1 hlogA_pos hlogA_le_A1
      _ ≤ 1 / Real.log A := by
          apply div_le_div_of_nonneg_right _ hlogA_pos.le
          have : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
          rw [div_le_one (by positivity)]; exact this
  have h18 : 18 / Real.log ((A + 1 : ℕ) : ℝ) ≤ 18 / Real.log A :=
    div_le_div_of_nonneg_left (by norm_num) hlogA_pos hlogA_le_A1
  rw [mul_sub, mul_one_div, mul_one_div] at hmid
  have h9 : 9 / Real.log ((A + 1 : ℕ) : ℝ) + 9 / Real.log ((A + 1 : ℕ) : ℝ) =
      18 / Real.log ((A + 1 : ℕ) : ℝ) := by ring
  rw [neg_div] at hSA
  have h19 : 1 / Real.log (A : ℝ) + 18 / Real.log (A : ℝ) = 19 / Real.log (A : ℝ) := by ring
  have hsum_cast : (∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))) =
      ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
    refine Finset.sum_congr rfl fun n _ => by push_cast; rfl
  linarith

private lemma neg_log_one_sub_le {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    -Real.log (1 - t) ≤ t + 2 * t ^ 2 := by
  have h1t_pos : 0 < 1 - t := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1t_pos
  have h2 : t / (1 - t) ≤ t + 2 * t ^ 2 := by
    rw [div_le_iff₀ h1t_pos]
    nlinarith [sq_nonneg t]
  have h3 : -Real.log (1 - t) ≤ t / (1 - t) := by
    have : 1 - (1 - t)⁻¹ = -(t / (1 - t)) := by field_simp; ring
    linarith
  linarith

private lemma prod_one_sub_two_div_inv_le {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    {x y : ℝ} (hx : (y0 : ℝ) ≤ x) (hxy : x ≤ y) :
    ∏ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 - 2 / (p : ℝ))⁻¹ ≤
      (10009 / 10000 : ℝ) * (Real.log y / Real.log x) ^ 2 := by
  have hy0_ge_4 : 4 ≤ y0 := by
    have h2 : 2 ^ 2 ≤ 2 ^ 200000 := Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.le_of_lt (by decide : 2 < 200000))
    exact le_trans (by norm_num) (le_trans h2 hy0)
  have hx_ge_4 : 4 ≤ x := by
    have : (4 : ℝ) ≤ y0 := by exact_mod_cast hy0_ge_4
    linarith
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have hA_ge_4 : 4 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx_ge_4)
  have hA_le_B : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogA_pos : 0 < Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊x⌋₊))
  have hlog_y0 : 100000 ≤ Real.log (y0 : ℝ) := by
    have h2 : Real.log ((2 ^ 200000 : ℕ) : ℝ) ≤ Real.log (y0 : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hy0)
    rw [Nat.cast_pow, Real.log_pow] at h2
    norm_num at h2
    have h3 := log_two_ge_half
    linarith
  have hlogx_100k : 100000 ≤ Real.log x :=
    hlog_y0.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < y0)) hx)
  have hlogA_99k : 99000 ≤ Real.log (⌊x⌋₊ : ℝ) := by
    have hxA : x ≤ (⌊x⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one x).le
    have hle : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊x⌋₊)
      linarith
    have hlog_le : Real.log x ≤ Real.log (⌊x⌋₊ : ℝ) + Real.log 2 := by
      have := Real.log_le_log hx_pos hle
      rw [Real.log_mul (by norm_num) (by positivity)] at this
      linarith
    have hlog2_le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    linarith
  have hpos_fac : ∀ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
      0 < 1 - 2 / (p : ℝ) := by
    intro p hp
    have hp4 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
    have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp4
    have : 2 / (p : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    linarith
  rw [← Real.exp_log (Finset.prod_pos fun p hp => inv_pos.mpr (hpos_fac p hp))]
  rw [Real.log_prod fun p hp => (inv_pos.mpr (hpos_fac p hp)).ne']
  have hlog_sum : ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ))⁻¹ ≤
      2 * Real.log (Real.log y / Real.log x) + 7 / 10000 := by
    have hterm : ∀ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
        Real.log (1 - 2 / (p : ℝ))⁻¹ ≤ 2 / (p : ℝ) + 8 / (p : ℝ) ^ 2 := by
      intro p hp
      rw [Real.log_inv]
      have hp5 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have ht : 2 / (p : ℝ) ≤ 1 / 2 := by
        calc 2 / (p : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
          _ ≤ 1 / 2 := by norm_num
      have hnl := neg_log_one_sub_le (by positivity) ht
      linarith [show 2 / (p : ℝ) + 2 * (2 / (p : ℝ)) ^ 2 = 2 / (p : ℝ) + 8 / (p : ℝ) ^ 2 by ring]
    have hsum1 := sum_inv_prime_Icc_le ⌊x⌋₊ ⌊y⌋₊ (by omega) hA_le_B
    have hsum2 : ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (8 : ℝ) / (p : ℝ) ^ 2 ≤
        8 / (⌊x⌋₊ : ℝ) := by
      have htel : ∀ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
          (8 : ℝ) / (p : ℝ) ^ 2 ≤ 8 * (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := by
        intro p hp
        have hp5 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
        have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        have hp1R : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega)
        rw [hp1R, div_sub_div _ _ (by linarith) (by linarith)]
        have : 1 / ((p : ℝ) ^ 2) ≤ 1 / (((p : ℝ) - 1) * p) :=
          one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
        have hsimp : (1 * (p : ℝ) - ((p : ℝ) - 1) * 1) / (((p : ℝ) - 1) * p) =
            1 / (((p : ℝ) - 1) * p) := by ring
        have h8 : 8 / (p : ℝ) ^ 2 ≤ 8 * (1 / (((p : ℝ) - 1) * p)) := by
          rw [← mul_one_div (8 : ℝ)]
          exact mul_le_mul_of_nonneg_left this (by norm_num)
        rw [hsimp]
        exact h8
      calc ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (8 : ℝ) / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
              8 * (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := Finset.sum_le_sum htel
        _ ≤ ∑ m ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊,
              8 * (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro m hm _
            have hm5 : 5 ≤ m := by rw [Finset.mem_Icc] at hm; omega
            have hm1R : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega)
            rw [hm1R]
            have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm5
            have : (1 : ℝ) / (m : ℝ) ≤ 1 / ((m : ℝ) - 1) :=
              one_div_le_one_div_of_le (by linarith) (by linarith)
            linarith
        _ ≤ 8 / (⌊x⌋₊ : ℝ) := by
            rw [← Finset.mul_sum]
            rcases eq_or_lt_of_le hA_le_B with h_eq | h_lt
            · have : ⌊y⌋₊ < ⌊x⌋₊ + 1 := by omega
              rw [Finset.Icc_eq_empty_of_lt this, Finset.sum_empty, mul_zero]
              positivity
            · have hind : ∀ k : ℕ, ⌊x⌋₊ + 1 ≤ k →
                  ∑ m ∈ Finset.Icc (⌊x⌋₊ + 1) k, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
                  1 / (⌊x⌋₊ : ℝ) - 1 / (k : ℝ) := by
                intro k hk
                induction k, hk using Nat.le_induction with
                | base => simp
                | succ k hk ih =>
                  rw [Finset.sum_Icc_succ_top (by omega), ih]
                  simp only [Nat.add_sub_cancel]
                  push_cast; ring
              rw [hind ⌊y⌋₊ (by omega), mul_sub]
              have h_eq : 8 * (1 / (⌊x⌋₊ : ℝ)) = 8 / (⌊x⌋₊ : ℝ) := by ring
              have h_nn : (0 : ℝ) ≤ 8 * (1 / (⌊y⌋₊ : ℝ)) := by positivity
              linarith
    have hlog_comp : Real.log (Real.log (⌊y⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)) ≤
        Real.log (Real.log y / Real.log x) + 1 / 10000 := by
      have h1 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊y⌋₊)) (Nat.floor_le hy_pos.le)
      have h2 : Real.log (⌊x⌋₊ : ℝ) ≥ Real.log x - Real.log 2 := by
        have hxA : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
          have := Nat.lt_floor_add_one x
          have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊x⌋₊)
          linarith
        have hle := Real.log_le_log hx_pos hxA
        rw [Real.log_mul (by norm_num) (by positivity)] at hle
        linarith
      have hlog2_le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      have hlogy_pos : 0 < Real.log y := Real.log_pos (by linarith)
      have h_ratio : Real.log (⌊y⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ) ≤
          (Real.log y / Real.log x) * (1 + 1 / 10000) := by
        have h3 : Real.log x / Real.log (⌊x⌋₊ : ℝ) ≤ 1 + 1 / 10000 := by
          rw [div_le_iff₀ hlogA_pos]
          linarith
        calc Real.log (⌊y⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)
            ≤ Real.log y / Real.log (⌊x⌋₊ : ℝ) :=
              div_le_div_of_nonneg_right h1 hlogA_pos.le
          _ = (Real.log y / Real.log x) * (Real.log x / Real.log (⌊x⌋₊ : ℝ)) := by
              field_simp
          _ ≤ (Real.log y / Real.log x) * (1 + 1 / 10000) :=
              mul_le_mul_of_nonneg_left h3 (div_pos hlogy_pos hlogx_pos).le
      calc Real.log (Real.log (⌊y⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ))
          ≤ Real.log ((Real.log y / Real.log x) * (1 + 1 / 10000)) :=
            Real.log_le_log (div_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊y⌋₊))) hlogA_pos) h_ratio
        _ = Real.log (Real.log y / Real.log x) + Real.log (1 + 1 / 10000) :=
            Real.log_mul (div_pos hlogy_pos hlogx_pos).ne' (by norm_num)
        _ ≤ Real.log (Real.log y / Real.log x) + 1 / 10000 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 10000)
            linarith
    have h_err1 : 19 / Real.log (⌊x⌋₊ : ℝ) ≤ 19 / 99000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogA_99k
    have hy0_big : 1048576 ≤ y0 := by
      have h2 : 2 ^ 20 ≤ 2 ^ 200000 := Nat.pow_le_pow_right (by norm_num) (by decide)
      exact le_trans (by norm_num) (le_trans h2 hy0)
    have h_err2 : 8 / (⌊x⌋₊ : ℝ) ≤ 1 / 10000 := by
      have hy0R : (1048576 : ℝ) ≤ (y0 : ℝ) := by exact_mod_cast hy0_big
      have hxA : x ≤ (⌊x⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one x).le
      have hA_big : (80000 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by linarith
      rw [div_le_iff₀ (by linarith)]
      linarith
    calc ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ))⁻¹
        ≤ ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
            (2 / (p : ℝ) + 8 / (p : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = 2 * ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 : ℝ) / p +
            ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (8 : ℝ) / (p : ℝ) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ 2 * (Real.log (Real.log (⌊y⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)) + 19 / Real.log (⌊x⌋₊ : ℝ)) +
            8 / (⌊x⌋₊ : ℝ) := by linarith
      _ ≤ 2 * (Real.log (Real.log y / Real.log x) + 1 / 10000 + 19 / 99000) + 1 / 10000 := by linarith
      _ ≤ 2 * Real.log (Real.log y / Real.log x) + 7 / 10000 := by linarith
  calc Real.exp (∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ))⁻¹)
      ≤ Real.exp (2 * Real.log (Real.log y / Real.log x) + 7 / 10000) := Real.exp_le_exp.mpr hlog_sum
    _ = Real.exp (7 / 10000) * Real.exp (Real.log ((Real.log y / Real.log x) ^ 2)) := by
        rw [Real.log_pow, Real.exp_add, mul_comm (Real.exp (7 / 10000))]
        simp
    _ = Real.exp (7 / 10000) * (Real.log y / Real.log x) ^ 2 := by
        have hlogy_pos : 0 < Real.log y := Real.log_pos (by linarith)
        rw [Real.exp_log (pow_pos (div_pos hlogy_pos hlogx_pos) 2)]
    _ ≤ (10009 / 10000 : ℝ) * (Real.log y / Real.log x) ^ 2 := by
        gcongr
        have h_exp : Real.exp (7 / 10000 : ℝ) ≤ 10000 / 9993 := by
          have h := Real.add_one_le_exp (-7 / 10000 : ℝ)
          rw [show (-7 / 10000 : ℝ) = -(7 / 10000) by ring, Real.exp_neg] at h
          have h1 : (9993 / 10000 : ℝ) ≤ (Real.exp (7 / 10000))⁻¹ := by linarith
          calc Real.exp (7 / 10000 : ℝ) = ((Real.exp (7 / 10000))⁻¹)⁻¹ := (inv_inv _).symm
            _ ≤ (9993 / 10000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
            _ = 10000 / 9993 := by norm_num
        linarith [show (10000 / 9993 : ℝ) ≤ 10009 / 10000 by norm_num]

/- ## Section 3: Prime Product Lower Bound, Telescoping Bound, and Main Sieve Induction -/

private lemma list_Vprod_inv_le {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    (w : ℕ → ℝ) (_hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    {x y : ℝ} (hx : (y0 : ℝ) ≤ x) (hxy : x ≤ y)
    (l : List ℕ) (hl_nodup : l.Nodup)
    (hl : ∀ p ∈ l, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y) :
    (l.map fun p => 1 - w p).prod⁻¹ ≤ (10009 / 10000 : ℝ) * (Real.log y / Real.log x) ^ 2 := by
  have hy0_4 : 4 ≤ y0 := by
    have h2 : 2 ^ 2 ≤ 2 ^ 200000 := Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.le_of_lt (by decide : 2 < 200000))
    exact le_trans (by norm_num) (le_trans h2 hy0)
  have hx_4 : 4 ≤ x := by
    have : (4 : ℝ) ≤ y0 := by exact_mod_cast hy0_4
    linarith
  have hx_fl4 : 4 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx_4)
  have hmem : ∀ p ∈ l, p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hp_prime, hxp, hpy⟩ := hl p hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, Nat.le_floor hpy⟩, hp_prime⟩
    have : ⌊x⌋₊ < p := (Nat.floor_lt (by linarith)).mpr hxp
    omega
  have hpos_w : ∀ p ∈ l, 0 < 1 - w p := by
    intro p hp
    have hmemp := hmem p hp
    have hp5 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hmemp; omega
    have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    have hwp : w p ≤ 2 / 5 := (hw2 p).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR)
    linarith
  have hl_pos : 0 < (l.map fun p => 1 - w p).prod :=
    List.prod_pos (by simp only [List.mem_map]; rintro _ ⟨p, hp, rfl⟩; exact hpos_w p hp)
  have hsub : l.toFinset ⊆ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime := by
    intro p hp; exact hmem p (List.mem_toFinset.mp hp)
  have hprod_ge : ∏ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 - 2 / (p : ℝ)) ≤
      (l.map fun p => 1 - w p).prod := by
    have heq : (l.map fun p => 1 - w p).prod = ∏ p ∈ l.toFinset, (1 - w p) := by
      rw [← List.prod_toFinset _ hl_nodup]
    rw [heq]
    have hpos_full : ∀ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, 0 < 1 - 2 / (p : ℝ) := by
      intro p hp
      have hp5 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have : 2 / (p : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
      linarith
    have hle1 : ∏ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 - 2 / (p : ℝ)) ≤
        ∏ p ∈ l.toFinset, (1 - 2 / (p : ℝ)) := by
      rw [← Finset.prod_sdiff hsub]
      have hsdiff : ∏ p ∈ ((Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime) \ l.toFinset,
          (1 - 2 / (p : ℝ)) ≤ 1 := by
        apply Finset.prod_le_one
        · intro p hp; exact (hpos_full p (Finset.sdiff_subset hp)).le
        · intro p _
          have : 0 ≤ 2 / (p : ℝ) := by positivity
          linarith
      have hpr_pos : 0 ≤ ∏ p ∈ l.toFinset, (1 - 2 / (p : ℝ)) :=
        Finset.prod_nonneg fun p hp => (hpos_full p (hsub hp)).le
      nlinarith
    have hle2 : ∏ p ∈ l.toFinset, (1 - 2 / (p : ℝ)) ≤ ∏ p ∈ l.toFinset, (1 - w p) := by
      apply Finset.prod_le_prod
      · intro p hp; exact (hpos_full p (hsub hp)).le
      · intro p _; linarith [hw2 p]
    exact hle1.trans hle2
  have hprod_full_pos : 0 < ∏ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 - 2 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp5 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
    have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    have : 2 / (p : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    linarith
  calc (l.map fun p => 1 - w p).prod⁻¹
      ≤ (∏ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 - 2 / (p : ℝ)))⁻¹ :=
        inv_anti₀ hprod_full_pos hprod_ge
    _ = ∏ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 - 2 / (p : ℝ))⁻¹ := by
        rw [Finset.prod_inv_distrib]
    _ ≤ (10009 / 10000 : ℝ) * (Real.log y / Real.log x) ^ 2 :=
        prod_one_sub_two_div_inv_le hy0 hx hxy

noncomputable def Vprod (w : ℕ → ℝ) (ps : List ℕ) : ℝ :=
  (ps.map fun p => 1 - w p).prod

def tailsPair : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | p :: rest => (p, rest) :: tailsPair rest

mutual
noncomputable def W_minus (w : ℕ → ℝ) : List ℕ → ℝ → ℝ
  | [], _ => 1
  | p :: rest, D =>
      if D < (p : ℝ) ^ (494 / 100 : ℝ) then 0
      else W_minus w rest D - w p * W_plus w rest (D / p)

noncomputable def W_plus (w : ℕ → ℝ) : List ℕ → ℝ → ℝ
  | [], _ => 1
  | p :: rest, D =>
      W_plus w rest D - (if (p : ℝ) ^ (476 / 100 : ℝ) ≤ D then w p * W_minus w rest (D / p) else 0)
end

mutual
noncomputable def indMinus (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)] :
    List ℕ → ℝ → ℕ → ℝ
  | [], _, _ => 1
  | p :: rest, D, y =>
      if D < (p : ℝ) ^ (494 / 100 : ℝ) then 0
      else indMinus bad rest D y - (if bad p y then indPlus bad rest (D / p) y else 0)

noncomputable def indPlus (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)] :
    List ℕ → ℝ → ℕ → ℝ
  | [], _, _ => 1
  | p :: rest, D, y =>
      indPlus bad rest D y -
        (if (p : ℝ) ^ (476 / 100 : ℝ) ≤ D ∧ bad p y then indMinus bad rest (D / p) y else 0)
end

mutual
noncomputable def divsMinus : List ℕ → List ℕ → ℝ → List (List ℕ)
  | d, [], _ => [d]
  | d, p :: rest, D =>
      if D < (p : ℝ) ^ (494 / 100 : ℝ) then []
      else divsMinus d rest D ++ divsPlus (p :: d) rest (D / p)

noncomputable def divsPlus : List ℕ → List ℕ → ℝ → List (List ℕ)
  | d, [], _ => [d]
  | d, p :: rest, D =>
      if (p : ℝ) ^ (476 / 100 : ℝ) ≤ D then
        divsPlus d rest D ++ divsMinus (p :: d) rest (D / p)
      else divsPlus d rest D
end

private lemma Vprod_pos (w : ℕ → ℝ) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    (ps : List ℕ) (hps : ∀ p ∈ ps, 5 ≤ p) : 0 < Vprod w ps := by
  unfold Vprod
  apply List.prod_pos
  simp only [List.mem_map]
  rintro _ ⟨p, hp, rfl⟩
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hps p hp
  have : w p ≤ 2 / 5 := (hw2 p).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR)
  linarith

private lemma Vprod_append (w : ℕ → ℝ) (l₁ l₂ : List ℕ) :
    Vprod w (l₁ ++ l₂) = Vprod w l₁ * Vprod w l₂ := by
  simp [Vprod, List.map_append, List.prod_append]

private lemma h_m61_eq : tabMList.getD 61 0 = 1000000 := by decide

private lemma phiM_eq_one_of_lt {s : ℝ} (hs : s < 494 / 100) : phiM s = 1 := by
  unfold phiM
  by_cases h1 : s < 37 / 10
  · simp [h1]
  · have hs1 : 37 / 10 ≤ s := not_lt.mp h1
    have hs11 : s < 11 := by linarith
    rw [if_neg h1, if_pos hs11]
    have hj61 : ⌊50 * (s - 37 / 10)⌋₊ ≤ 61 := by
      have : ⌊50 * (s - 37 / 10)⌋₊ < 62 := (Nat.floor_lt (by linarith)).mpr (by linarith)
      omega
    have h_ub := checkMono_getD tabMList h_monoM 0 ⌊50 * (s - 37 / 10)⌋₊ (Nat.zero_le _)
      (by rw [h_lenM]; omega)
    have h_lb := checkMono_getD tabMList h_monoM ⌊50 * (s - 37 / 10)⌋₊ 61 hj61
      (by rw [h_lenM]; omega)
    rw [h_m0_eq] at h_ub
    rw [h_m61_eq] at h_lb
    have heq : tabMList.getD ⌊50 * (s - 37 / 10)⌋₊ 0 = 1000000 := le_antisymm h_ub h_lb
    rw [heq]; norm_num

private lemma getD_dropLast {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : i + 1 < l.length) :
    l.dropLast.getD i d = l.getD i d := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases t with
    | nil => simp at hi
    | cons b t' =>
      cases i with
      | zero => simp [List.dropLast]
      | succ i' =>
        simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b t'), List.getD_eq_getElem?_getD,
          List.getElem?_cons_succ]
        exact ih i' (by simpa using hi)

private lemma mem_tailsPair_fst : ∀ {l : List ℕ} {pr : ℕ × List ℕ},
    pr ∈ tailsPair l → pr.1 ∈ l := by
  intro l
  induction l with
  | nil => intro pr h; simp [tailsPair] at h
  | cons p rest ih =>
    intro pr h
    simp only [tailsPair, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

private lemma mem_tailsPair_sub : ∀ {l : List ℕ} {pr : ℕ × List ℕ},
    pr ∈ tailsPair l → ∀ q ∈ pr.2, q ∈ l := by
  intro l
  induction l with
  | nil => intro pr h; simp [tailsPair] at h
  | cons p rest ih =>
    intro pr h q hq
    simp only [tailsPair, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_of_mem _ hq
    · exact List.mem_cons_of_mem _ (ih h q hq)

private lemma mem_tailsPair_pairwise : ∀ {l : List ℕ} {pr : ℕ × List ℕ},
    l.Pairwise (· > ·) → pr ∈ tailsPair l →
    pr.2.Pairwise (· > ·) ∧ ∀ q ∈ pr.2, q < pr.1 := by
  intro l
  induction l with
  | nil => intro pr _ h; simp [tailsPair] at h
  | cons p rest ih =>
    intro pr hpw h
    have hpw_c := List.pairwise_cons.mp hpw
    simp only [tailsPair, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨hpw_c.2, hpw_c.1⟩
    · exact ih hpw_c.2 h

private lemma mem_tailsPair_length_lt : ∀ {l : List ℕ} {pr : ℕ × List ℕ},
    pr ∈ tailsPair l → pr.2.length < l.length := by
  intro l
  induction l with
  | nil => intro pr h; simp [tailsPair] at h
  | cons p rest ih =>
    intro pr h
    simp only [tailsPair, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact (ih h).trans (Nat.lt_succ_self _)

noncomputable def sufAfter (D U : ℝ) : List ℕ → List ℕ
  | [] => []
  | p :: rest => if Real.log D / Real.log p < U then sufAfter D U rest else p :: rest

private lemma sufAfter_append (D U : ℝ) : ∀ ps : List ℕ,
    ∃ pref, ps = pref ++ sufAfter D U ps ∧ ∀ q ∈ pref, Real.log D / Real.log q < U := by
  intro ps
  induction ps with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons p rest ih =>
    unfold sufAfter
    split_ifs with h
    · obtain ⟨pref, hEq, hpref⟩ := ih
      refine ⟨p :: pref, ?_, ?_⟩
      · rw [List.cons_append]; exact congrArg (p :: ·) hEq
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact h
        · exact hpref q hq
    · exact ⟨[], rfl, by simp⟩

private lemma sum_tailsPair_ite (w : ℕ → ℝ) (D U : ℝ) (hD : 1 ≤ D) :
    ∀ ps : List ℕ, ps.Pairwise (· > ·) → (∀ p ∈ ps, 2 ≤ p) →
      ((tailsPair ps).map fun pr =>
        if Real.log D / Real.log pr.1 < U then w pr.1 * Vprod w pr.2 else 0).sum =
      Vprod w (sufAfter D U ps) - Vprod w ps := by
  intro ps
  induction ps with
  | nil => intro _ _; simp [tailsPair, sufAfter]
  | cons p rest ih =>
    intro hpw h2
    have hp_rest : ∀ q ∈ rest, q < p := (List.pairwise_cons.mp hpw).1
    have hpw_rest : rest.Pairwise (· > ·) := (List.pairwise_cons.mp hpw).2
    have h2_rest : ∀ q ∈ rest, 2 ≤ q := fun q hq => h2 q (List.mem_cons_of_mem _ hq)
    unfold sufAfter tailsPair
    simp only [List.map_cons, List.sum_cons]
    by_cases hlt : Real.log D / Real.log p < U
    · rw [if_pos hlt, if_pos hlt, ih hpw_rest h2_rest]
      have hV : Vprod w (p :: rest) = (1 - w p) * Vprod w rest := by
        simp [Vprod, List.map_cons, List.prod_cons]
      rw [hV]; ring
    · rw [if_neg hlt, if_neg hlt, zero_add]
      have hzero : ∀ pr ∈ tailsPair rest,
          (if Real.log D / Real.log pr.1 < U then w pr.1 * Vprod w pr.2 else 0) = 0 := by
        intro pr hpr
        have hmem : pr.1 ∈ rest := mem_tailsPair_fst hpr
        have hqp : pr.1 < p := hp_rest pr.1 hmem
        have hq2 : 2 ≤ pr.1 := h2_rest pr.1 hmem
        have hlogq : 0 < Real.log (pr.1 : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < pr.1))
        have hlogp : Real.log (pr.1 : ℝ) ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hqp.le)
        have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
        have hle : Real.log D / Real.log (p : ℝ) ≤ Real.log D / Real.log (pr.1 : ℝ) :=
          div_le_div_of_nonneg_left hlogD hlogq hlogp
        rw [if_neg (by linarith)]
      have hsum0 : ((tailsPair rest).map fun pr =>
          if Real.log D / Real.log pr.1 < U then w pr.1 * Vprod w pr.2 else 0).sum = 0 := by
        apply List.sum_eq_zero
        simp only [List.mem_map]
        rintro _ ⟨pr, hpr, rfl⟩
        exact hzero pr hpr
      rw [hsum0, sub_self]

private lemma sufAfter_bound {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    {z D U : ℝ} (hz : (y0 : ℝ) ≤ z) (hD : 1 ≤ D)
    (hs_pos : 0 < Real.log D / Real.log z) (hsU : Real.log D / Real.log z < U)
    (ps : List ℕ) (hpw : ps.Pairwise (· > ·))
    (hps : ∀ p ∈ ps, p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z) :
    Vprod w (sufAfter D U ps) - Vprod w ps ≤
      Vprod w ps * ((1001 / 1000 : ℝ) * (U / (Real.log D / Real.log z)) ^ 2 - 1) := by
  have hy0_5 : 5 ≤ y0 := by
    have h2 : 2 ^ 3 ≤ 2 ^ 200000 := Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.le_of_lt (by decide : 3 < 200000))
    exact le_trans (by norm_num) (le_trans h2 hy0)
  have hz_5 : (5 : ℝ) ≤ z := by
    have : (5 : ℝ) ≤ y0 := by exact_mod_cast hy0_5
    linarith
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogD_pos : 0 < Real.log D := by
    by_contra hle
    have : Real.log D / Real.log z ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hle) hlogz_pos.le
    linarith
  have hU_pos : 0 < U := hs_pos.trans hsU
  have hV_pos : 0 < Vprod w ps := Vprod_pos w hw2 ps fun p hp => by
    have := (hps p hp).2.1; omega
  obtain ⟨pref, hEq, hpref⟩ := sufAfter_append D U ps
  by_cases hnil : pref = []
  · subst hnil
    have hsuf : sufAfter D U ps = ps := by simpa using hEq.symm
    rw [hsuf, sub_self]
    have hrat : 1 < U / (Real.log D / Real.log z) := by
      rw [one_lt_div hs_pos]; exact hsU
    have hrhs : 0 ≤ (1001 / 1000 : ℝ) * (U / (Real.log D / Real.log z)) ^ 2 - 1 := by
      nlinarith
    exact mul_nonneg hV_pos.le hrhs
  · obtain ⟨q0, hq0_mem⟩ := List.exists_mem_of_ne_nil pref hnil
    have hq0_ps : q0 ∈ ps := by rw [hEq]; exact List.mem_append_left _ hq0_mem
    have hq0_spec := hps q0 hq0_ps
    have hq0_lt : Real.log D / Real.log (q0 : ℝ) < U := hpref q0 hq0_mem
    have hq0_pos : 0 < Real.log (q0 : ℝ) :=
      Real.log_pos (by exact_mod_cast hq0_spec.1.one_lt)
    have hlogDU_lt_z : Real.log D / U < Real.log z := by
      have h1 : Real.log D / U < Real.log (q0 : ℝ) := by
        rw [div_lt_iff₀ hU_pos]
        exact (div_lt_iff₀ hq0_pos).mp hq0_lt |>.trans_eq (mul_comm _ _)
      have h2 : Real.log (q0 : ℝ) ≤ Real.log z :=
        Real.log_le_log (by exact_mod_cast hq0_spec.1.pos) hq0_spec.2.2
      exact h1.trans_le h2
    let x := max (y0 : ℝ) (Real.exp (Real.log D / U))
    have hx_ge : (y0 : ℝ) ≤ x := le_max_left _ _
    have hx_le : x ≤ z := by
      apply max_le hz
      calc Real.exp (Real.log D / U) ≤ Real.exp (Real.log z) := Real.exp_le_exp.mpr hlogDU_lt_z.le
        _ = z := Real.exp_log (by linarith)
    have hpref_nodup : pref.Nodup := by
      have hps_nd : ps.Nodup := hpw.imp fun {a b} (h : a > b) => h.ne'
      rw [hEq] at hps_nd
      exact (List.nodup_append.mp hps_nd).1
    have hpref_spec : ∀ q ∈ pref, q.Prime ∧ x < (q : ℝ) ∧ (q : ℝ) ≤ z := by
      intro q hq
      have hq_ps : q ∈ ps := by rw [hEq]; exact List.mem_append_left _ hq
      have hq_sp := hps q hq_ps
      have hq_lt := hpref q hq
      have hq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq_sp.1.one_lt)
      have hq_exp : Real.exp (Real.log D / U) < (q : ℝ) := by
        have h1 : Real.log D / U < Real.log (q : ℝ) := by
          rw [div_lt_iff₀ hU_pos]
          exact (div_lt_iff₀ hq_pos).mp hq_lt |>.trans_eq (mul_comm _ _)
        calc Real.exp (Real.log D / U) < Real.exp (Real.log (q : ℝ)) := Real.exp_lt_exp.mpr h1
          _ = (q : ℝ) := Real.exp_log (by exact_mod_cast hq_sp.1.pos)
      exact ⟨hq_sp.1, max_lt (by exact_mod_cast hq_sp.2.1) hq_exp, hq_sp.2.2⟩
    have hinv := list_Vprod_inv_le hy0 w hw0 hw2 hx_ge hx_le pref hpref_nodup hpref_spec
    have hlogx_ge : Real.log D / U ≤ Real.log x := by
      calc Real.log D / U = Real.log (Real.exp (Real.log D / U)) := (Real.log_exp _).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    have hlogDU_pos : 0 < Real.log D / U := div_pos hlogD_pos hU_pos
    have hratio : Real.log z / Real.log x ≤ U / (Real.log D / Real.log z) := by
      calc Real.log z / Real.log x ≤ Real.log z / (Real.log D / U) :=
            div_le_div_of_nonneg_left hlogz_pos.le hlogDU_pos hlogx_ge
        _ = U / (Real.log D / Real.log z) := by field_simp
    have hinv2 : (Vprod w pref)⁻¹ ≤ (1001 / 1000 : ℝ) * (U / (Real.log D / Real.log z)) ^ 2 := by
      have h1x : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast (by omega : 1 ≤ y0)) hx_ge
      have hlogx_base : 0 ≤ Real.log x := Real.log_nonneg h1x
      have hlogx_nn : 0 ≤ Real.log z / Real.log x := div_nonneg hlogz_pos.le hlogx_base
      calc (pref.map fun p => 1 - w p).prod⁻¹
          ≤ (10009 / 10000 : ℝ) * (Real.log z / Real.log x) ^ 2 := hinv
        _ ≤ (1001 / 1000 : ℝ) * (U / (Real.log D / Real.log z)) ^ 2 :=
            mul_le_mul (by norm_num) (pow_le_pow_left₀ hlogx_nn hratio 2) (by positivity) (by norm_num)
    have hVp_pos : 0 < Vprod w pref := Vprod_pos w hw2 pref fun p hp => by
      have := (hps p (by rw [hEq]; exact List.mem_append_left _ hp)).2.1; omega
    have hVeq : Vprod w ps = Vprod w pref * Vprod w (sufAfter D U ps) := by
      conv_lhs => rw [hEq, Vprod_append]
    have hsuf_eq : Vprod w (sufAfter D U ps) - Vprod w ps = Vprod w ps * ((Vprod w pref)⁻¹ - 1) := by
      rw [hVeq]; field_simp [hVp_pos.ne']
    rw [hsuf_eq]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hinv2 1) hV_pos.le

private lemma list_sum_map_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private lemma list_sum_map_finset_sum {α : Type*} (l : List α) (S : Finset ℕ) (f : α → ℕ → ℝ) :
    (l.map fun a => ∑ t ∈ S, f a t).sum = ∑ t ∈ S, (l.map fun a => f a t).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private lemma list_sum_map_const_mul {α : Type*} (l : List α) (c : ℝ) (f : α → ℝ) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma sum_tails_step_le {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    {z D : ℝ} (hz : (y0 : ℝ) ≤ z) (hD : 1 ≤ D)
    (hs_pos : 0 < Real.log D / Real.log z)
    (ps : List ℕ) (hpw : ps.Pairwise (· > ·))
    (hps : ∀ p ∈ ps, p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z)
    (K : ℕ) (b c : ℕ → ℝ) (F : ℝ → ℝ)
    (hc_anti : ∀ t < K, c (t + 1) ≤ c t)
    (hF : ∀ p ∈ ps, F (Real.log D / Real.log p) ≤
      ∑ t ∈ Finset.range K, (if Real.log D / Real.log p < b (t + 1) then c t - c (t + 1) else 0)) :
    ((tailsPair ps).map fun pr => w pr.1 * Vprod w pr.2 * F (Real.log D / Real.log pr.1)).sum ≤
      Vprod w ps * ∑ t ∈ Finset.range K,
        (c t - c (t + 1)) *
          (if Real.log D / Real.log z < b (t + 1) then
            (1001 / 1000 : ℝ) * (b (t + 1) / (Real.log D / Real.log z)) ^ 2 - 1
          else 0) := by
  have hy0_5 : 5 ≤ y0 := by
    have h2 : 2 ^ 3 ≤ 2 ^ 200000 := Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.le_of_lt (by decide : 3 < 200000))
    exact le_trans (by norm_num) (le_trans h2 hy0)
  have h2_ps : ∀ p ∈ ps, 2 ≤ p := fun p hp => (hps p hp).1.two_le
  have hV_pos : 0 < Vprod w ps := Vprod_pos w hw2 ps fun p hp => by
    have := (hps p hp).2.1; omega
  have h_le1 : ((tailsPair ps).map fun pr => w pr.1 * Vprod w pr.2 * F (Real.log D / Real.log pr.1)).sum ≤
      ((tailsPair ps).map fun pr =>
        ∑ t ∈ Finset.range K,
          (c t - c (t + 1)) * (if Real.log D / Real.log pr.1 < b (t + 1) then w pr.1 * Vprod w pr.2 else 0)).sum := by
    apply list_sum_map_le
    intro pr hpr
    have hw_nn : 0 ≤ w pr.1 := hw0 pr.1
    have hV2_pos : 0 < Vprod w pr.2 := Vprod_pos w hw2 pr.2 fun q hq => by
      have := (hps q (mem_tailsPair_sub hpr q hq)).2.1; omega
    have h1 := mul_le_mul_of_nonneg_left (hF pr.1 (mem_tailsPair_fst hpr)) (mul_nonneg hw_nn hV2_pos.le)
    rw [Finset.mul_sum] at h1
    refine h1.trans_eq (Finset.sum_congr rfl fun t _ => ?_)
    split_ifs <;> ring
  rw [list_sum_map_finset_sum] at h_le1
  have h_le2 : ∑ t ∈ Finset.range K, ((tailsPair ps).map fun pr =>
      (c t - c (t + 1)) * (if Real.log D / Real.log pr.1 < b (t + 1) then w pr.1 * Vprod w pr.2 else 0)).sum ≤
      ∑ t ∈ Finset.range K, (c t - c (t + 1)) *
        (Vprod w ps * (if Real.log D / Real.log z < b (t + 1) then
          (1001 / 1000 : ℝ) * (b (t + 1) / (Real.log D / Real.log z)) ^ 2 - 1 else 0)) := by
    refine Finset.sum_le_sum fun t ht => ?_
    have ht' : t < K := Finset.mem_range.mp ht
    rw [list_sum_map_const_mul]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hc_anti t ht'))
    by_cases hsb : Real.log D / Real.log z < b (t + 1)
    · rw [if_pos hsb, sum_tailsPair_ite w D (b (t + 1)) hD ps hpw h2_ps]
      exact sufAfter_bound hy0 w hw0 hw2 hz hD hs_pos hsb ps hpw hps
    · rw [if_neg hsb, mul_zero]
      have hsum0 : ((tailsPair ps).map fun pr =>
          if Real.log D / Real.log pr.1 < b (t + 1) then w pr.1 * Vprod w pr.2 else 0).sum = 0 := by
        apply List.sum_eq_zero
        simp only [List.mem_map]
        rintro _ ⟨pr, hpr, rfl⟩
        have hsp := hps pr.1 (mem_tailsPair_fst hpr)
        have hlogp_pos : 0 < Real.log (pr.1 : ℝ) := Real.log_pos (by exact_mod_cast hsp.1.one_lt)
        have hlogpz : Real.log (pr.1 : ℝ) ≤ Real.log z :=
          Real.log_le_log (by exact_mod_cast hsp.1.pos) hsp.2.2
        have hle_s : Real.log D / Real.log z ≤ Real.log D / Real.log (pr.1 : ℝ) :=
          div_le_div_of_nonneg_left (Real.log_nonneg hD) hlogp_pos hlogpz
        rw [if_neg (by linarith)]
      linarith
  calc ((tailsPair ps).map fun pr => w pr.1 * Vprod w pr.2 * F (Real.log D / Real.log pr.1)).sum
      ≤ ∑ t ∈ Finset.range K, ((tailsPair ps).map fun pr =>
          (c t - c (t + 1)) * (if Real.log D / Real.log pr.1 < b (t + 1) then w pr.1 * Vprod w pr.2 else 0)).sum := h_le1
    _ ≤ ∑ t ∈ Finset.range K, (c t - c (t + 1)) *
          (Vprod w ps * (if Real.log D / Real.log z < b (t + 1) then
            (1001 / 1000 : ℝ) * (b (t + 1) / (Real.log D / Real.log z)) ^ 2 - 1 else 0)) := h_le2
    _ = Vprod w ps * ∑ t ∈ Finset.range K,
          (c t - c (t + 1)) * (if Real.log D / Real.log z < b (t + 1) then
            (1001 / 1000 : ℝ) * (b (t + 1) / (Real.log D / Real.log z)) ^ 2 - 1 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => by ring

private lemma sum_range_sub_tail : ∀ (K t0 : ℕ) (c : ℕ → ℝ), t0 < K →
    ∑ t ∈ Finset.range K, (if t0 ≤ t then c t - c (t + 1) else 0) = c t0 - c K := by
  intro K
  induction K with
  | zero => intro t0 _ ht0; omega
  | succ K ih =>
    intro t0 c ht0
    rw [Finset.sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht0 with hlt | heq
    · rw [ih t0 c hlt, if_pos hlt.le]
      ring
    · rw [heq]
      have h0 : ∑ t ∈ Finset.range K, (if K ≤ t then c t - c (t + 1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_range] at ht
        rw [if_neg (by omega)]
      rw [h0, if_pos le_rfl]
      ring

private lemma le_sum_step_of_lt {K : ℕ} (b c : ℕ → ℝ) (hb : ∀ t < K, b t < b (t + 1))
    (hc_last : c K = 0) {u val : ℝ} (hbu : b 0 ≤ u) (huK : u < b K)
    (hval : ∀ t < K, b t ≤ u → u < b (t + 1) → val ≤ c t) :
    val ≤ ∑ t ∈ Finset.range K, (if u < b (t + 1) then c t - c (t + 1) else 0) := by
  have hb_mono : ∀ i j, i ≤ j → j ≤ K → b i ≤ b j := by
    intro i j hij hjK
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hb j (by omega)).le
  have hex : ∀ M ≤ K, b 0 ≤ u → u < b M → ∃ t0 < M, b t0 ≤ u ∧ u < b (t0 + 1) := by
    intro M
    induction M with
    | zero => intro _ h1 h2; linarith
    | succ M ih =>
      intro hMK h1 h2
      by_cases huM : u < b M
      · obtain ⟨t0, ht0, hbt, hbt1⟩ := ih (by omega) h1 huM
        exact ⟨t0, by omega, hbt, hbt1⟩
      · exact ⟨M, Nat.lt_succ_self M, not_lt.mp huM, h2⟩
  obtain ⟨t0, ht0, hbt0, hbt01⟩ := hex K le_rfl hbu huK
  have heq : ∑ t ∈ Finset.range K, (if u < b (t + 1) then c t - c (t + 1) else 0) =
      ∑ t ∈ Finset.range K, (if t0 ≤ t then c t - c (t + 1) else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    by_cases hle : t0 ≤ t
    · have hlt : u < b (t + 1) := hbt01.trans_le (hb_mono (t0 + 1) (t + 1) (by omega) (by omega))
      rw [if_pos hlt, if_pos hle]
    · have hge : b (t + 1) ≤ u := (hb_mono (t + 1) t0 (by omega) (by omega)).trans hbt0
      rw [if_neg (by linarith), if_neg hle]
  rw [heq, sum_range_sub_tail K t0 c ht0, hc_last, sub_zero]
  exact hval t0 ht0 hbt0 hbt01

private lemma geo_tail_bound (N : ℕ) (hN : 46 ≤ N) :
    let r : ℝ := 51 / 50
    let g : ℕ → ℝ := fun n => if n < N then r⁻¹ ^ (10 * n) else 0
    (∑ n ∈ Finset.range N, (g n - g (n + 1)) * r ^ (2 * (n + 1)) ≤ 32 / 25) ∧
    (∑ n ∈ Finset.range N, (g n - g (n + 1)) = 1) ∧
    (∀ n < N, g (n + 1) ≤ g n) := by
  intro r g
  have hr_gt1 : (1 : ℝ) < r := by norm_num [r]
  have hr_pos : (0 : ℝ) < r := by norm_num [r]
  have hri_lt1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr_gt1
  have hri_nn : 0 ≤ r⁻¹ := by positivity
  have hanti : ∀ n < N, g (n + 1) ≤ g n := by
    intro n hn
    dsimp only [g]
    rw [if_pos hn]
    by_cases hn1 : n + 1 < N
    · rw [if_pos hn1]
      exact pow_le_pow_of_le_one hri_nn hri_lt1.le (by omega)
    · rw [if_neg hn1]
      positivity
  have hsum1 : ∑ n ∈ Finset.range N, (g n - g (n + 1)) = 1 := by
    have htel : ∀ m, ∑ n ∈ Finset.range m, (g n - g (n + 1)) = g 0 - g m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [htel N]
    have h0 : g 0 = 1 := by simp [g, show 0 < N by omega]
    have hN0 : g N = 0 := by simp [g]
    rw [h0, hN0, sub_zero]
  have hsum2 : ∑ n ∈ Finset.range N, (g n - g (n + 1)) * r ^ (2 * (n + 1)) ≤ 32 / 25 := by
    have hN_eq : N = (N - 1) + 1 := by omega
    conv_lhs => rw [hN_eq, Finset.sum_range_succ]
    have hterm_lt : ∀ n ∈ Finset.range (N - 1),
        (g n - g (n + 1)) * r ^ (2 * (n + 1)) =
          (1 - r⁻¹ ^ 10) * r ^ 2 * (r⁻¹ ^ 8) ^ n := by
      intro n hn
      rw [Finset.mem_range] at hn
      have hnN : n < N := by omega
      have hn1N : n + 1 < N := by omega
      dsimp only [g]
      rw [if_pos hnN, if_pos hn1N]
      have hpow1 : r⁻¹ ^ (10 * (n + 1)) = r⁻¹ ^ 10 * r⁻¹ ^ (10 * n) := by
        rw [← pow_add]; congr 1; omega
      have hpow2 : r⁻¹ ^ (10 * n) * r ^ (2 * (n + 1)) = r ^ 2 * (r⁻¹ ^ 8) ^ n := by
        have h1 : 10 * n = 8 * n + 2 * n := by omega
        have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
        rw [h1, h2, pow_add, pow_add]
        have hmul : r⁻¹ ^ (2 * n) * r ^ (2 * n) = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hr_pos.ne', one_pow]
        calc r⁻¹ ^ (8 * n) * r⁻¹ ^ (2 * n) * (r ^ (2 * n) * r ^ 2)
            = r ^ 2 * (r⁻¹ ^ 8) ^ n * (r⁻¹ ^ (2 * n) * r ^ (2 * n)) := by
              rw [← pow_mul]; ring
          _ = r ^ 2 * (r⁻¹ ^ 8) ^ n := by rw [hmul, mul_one]
      rw [hpow1]
      calc (r⁻¹ ^ (10 * n) - r⁻¹ ^ 10 * r⁻¹ ^ (10 * n)) * r ^ (2 * (n + 1))
          = (1 - r⁻¹ ^ 10) * (r⁻¹ ^ (10 * n) * r ^ (2 * (n + 1))) := by ring
        _ = (1 - r⁻¹ ^ 10) * (r ^ 2 * (r⁻¹ ^ 8) ^ n) := by rw [hpow2]
        _ = (1 - r⁻¹ ^ 10) * r ^ 2 * (r⁻¹ ^ 8) ^ n := by ring
    have hlast : (g (N - 1) - g (N - 1 + 1)) * r ^ (2 * (N - 1 + 1)) =
        r ^ 2 * (r⁻¹ ^ 8) ^ (N - 1) := by
      dsimp only [g]
      rw [if_pos (by omega : N - 1 < N), if_neg (by omega : ¬ N - 1 + 1 < N), sub_zero]
      have h1 : 10 * (N - 1) = 8 * (N - 1) + 2 * (N - 1) := by omega
      have h2 : 2 * (N - 1 + 1) = 2 * (N - 1) + 2 := by omega
      rw [h1, h2, pow_add, pow_add]
      have hmul : r⁻¹ ^ (2 * (N - 1)) * r ^ (2 * (N - 1)) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hr_pos.ne', one_pow]
      calc r⁻¹ ^ (8 * (N - 1)) * r⁻¹ ^ (2 * (N - 1)) * (r ^ (2 * (N - 1)) * r ^ 2)
          = r ^ 2 * (r⁻¹ ^ 8) ^ (N - 1) * (r⁻¹ ^ (2 * (N - 1)) * r ^ (2 * (N - 1))) := by
            rw [← pow_mul]; ring
        _ = r ^ 2 * (r⁻¹ ^ 8) ^ (N - 1) := by rw [hmul, mul_one]
    have hgeom : ∑ n ∈ Finset.range (N - 1), (r⁻¹ ^ 8) ^ n ≤ 1 / (1 - r⁻¹ ^ 8) := by
      have h8_lt1 : r⁻¹ ^ 8 < 1 := pow_lt_one₀ hri_nn hri_lt1 (by norm_num)
      rw [geom_sum_eq h8_lt1.ne]
      have h1m : 0 < 1 - r⁻¹ ^ 8 := by linarith
      have hpow_nn : 0 ≤ (r⁻¹ ^ 8) ^ (N - 1) := by positivity
      have hs1 : (r⁻¹ ^ 8) ^ (N - 1) - 1 = -(1 - (r⁻¹ ^ 8) ^ (N - 1)) := by ring
      have hs2 : r⁻¹ ^ 8 - 1 = -(1 - r⁻¹ ^ 8) := by ring
      rw [hs1, hs2, neg_div_neg_eq]
      exact div_le_div_of_nonneg_right (by linarith) h1m.le
    have hlast_le : (r⁻¹ ^ 8) ^ (N - 1) ≤ 1 / 1024 := by
      have h36 : (2 : ℝ) ≤ r ^ 36 := by norm_num [r]
      have h360 : (1024 : ℝ) ≤ r ^ 360 := by
        calc (1024 : ℝ) = 2 ^ 10 := by norm_num
          _ ≤ (r ^ 36) ^ 10 := pow_le_pow_left₀ (by norm_num) h36 10
          _ = r ^ 360 := by rw [← pow_mul]
      have h8N : r ^ 360 ≤ r ^ (8 * (N - 1)) :=
        pow_le_pow_right₀ hr_gt1.le (by omega)
      have hinv : (r⁻¹ ^ 8) ^ (N - 1) = (r ^ (8 * (N - 1)))⁻¹ := by
        rw [← pow_mul, inv_pow]
      rw [hinv, one_div]
      exact inv_anti₀ (by norm_num) (h360.trans h8N)
    have hsum_pre : ∑ n ∈ Finset.range (N - 1), (g n - g (n + 1)) * r ^ (2 * (n + 1)) =
        (1 - r⁻¹ ^ 10) * r ^ 2 * ∑ n ∈ Finset.range (N - 1), (r⁻¹ ^ 8) ^ n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hterm_lt
    rw [hsum_pre, hlast]
    have hcoef_nn : 0 ≤ (1 - r⁻¹ ^ 10) * r ^ 2 := by
      have : r⁻¹ ^ 10 ≤ 1 := pow_le_one₀ hri_nn hri_lt1.le
      nlinarith [sq_nonneg r]
    have hpart1 : (1 - r⁻¹ ^ 10) * r ^ 2 * ∑ n ∈ Finset.range (N - 1), (r⁻¹ ^ 8) ^ n ≤
        (1 - r⁻¹ ^ 10) * r ^ 2 * (1 / (1 - r⁻¹ ^ 8)) :=
      mul_le_mul_of_nonneg_left hgeom hcoef_nn
    have hpart2 : r ^ 2 * (r⁻¹ ^ 8) ^ (N - 1) ≤ r ^ 2 * (1 / 1024) :=
      mul_le_mul_of_nonneg_left hlast_le (by positivity)
    have hnum : (1 - r⁻¹ ^ 10) * r ^ 2 * (1 / (1 - r⁻¹ ^ 8)) + r ^ 2 * (1 / 1024) ≤ 32 / 25 := by
      norm_num [r]
    linarith
  exact ⟨hsum2, hsum1, hanti⟩

private lemma grid_tail_sum_le (gridList sufList : List ℕ)
    (hsuf_chk : checkSuf 0 gridList sufList = true)
    (hlen_g : gridList.length = 366) (hlen_s : sufList.length = 366)
    (hlast_g : gridList.getD 365 0 = F_tail_nat)
    (hlast_s : sufList.getD 365 0 = F_tail_nat * 387200)
    {s : ℝ} (hs1 : 37 / 10 ≤ s) (hs2 : s < 11) (N : ℕ) (hN : 46 ≤ N) :
    let j := ⌊50 * (s - 37 / 10)⌋₊
    let r : ℝ := 51 / 50
    let b : ℕ → ℝ := fun t => if t ≤ 365 then (185 + (t : ℝ)) / 50 else 11 * r ^ (t - 365)
    let c : ℕ → ℝ := fun t =>
      if t < 365 then (gridList.getD t 0 : ℝ) / 1000000
      else if t < 365 + N then F_tail_val * r⁻¹ ^ (10 * (t - 365))
      else 0
    ∑ t ∈ Finset.range (365 + N),
      (c t - c (t + 1)) * (if s < b (t + 1) then (1001 / 1000 : ℝ) * (b (t + 1) / s) ^ 2 - 1 else 0) ≤
    (1001 * (sufList.getD j 0 : ℝ) / (1000 * (185 + (j : ℝ)) ^ 2) - (gridList.getD j 0 : ℝ)) / 1000000 := by
  intro j r b c
  have hs_pos : 0 < s := by linarith
  have hj_lt : j < 365 := idx_lt_365 hs1 hs2
  have hj_bounds := idx_bounds hs1 hs2
  have hg_props := geo_tail_bound N hN
  let g : ℕ → ℝ := fun n => if n < N then r⁻¹ ^ (10 * n) else 0
  have hc_tail : ∀ n, c (365 + n) = F_tail_val * g n := by
    intro n
    dsimp only [c, g]
    rw [if_neg (by omega)]
    by_cases hn : n < N
    · rw [if_pos (by omega), if_pos hn]; simp [Nat.add_sub_cancel_left]
    · rw [if_neg (by omega), if_neg hn, mul_zero]
  have hc_365 : c 365 = (gridList.getD 365 0 : ℝ) / 1000000 := by
    rw [hc_tail 0, show g 0 = 1 by simp [g, show 0 < N by omega], mul_one, hlast_g]
    unfold F_tail_val; rfl
  rw [Finset.sum_range_add]
  have htail_eq : ∑ n ∈ Finset.range N,
      (c (365 + n) - c (365 + n + 1)) *
        (if s < b (365 + n + 1) then (1001 / 1000 : ℝ) * (b (365 + n + 1) / s) ^ 2 - 1 else 0) =
      (1001 / 1000 : ℝ) * (F_tail_val * 121 / s ^ 2) *
          (∑ n ∈ Finset.range N, (g n - g (n + 1)) * r ^ (2 * (n + 1))) -
        F_tail_val * (∑ n ∈ Finset.range N, (g n - g (n + 1))) := by
    have hterm : ∀ n ∈ Finset.range N,
        (c (365 + n) - c (365 + n + 1)) *
          (if s < b (365 + n + 1) then (1001 / 1000 : ℝ) * (b (365 + n + 1) / s) ^ 2 - 1 else 0) =
        (1001 / 1000 : ℝ) * (F_tail_val * 121 / s ^ 2) * ((g n - g (n + 1)) * r ^ (2 * (n + 1))) -
          F_tail_val * (g n - g (n + 1)) := by
      intro n _
      have hb_n : b (365 + n + 1) = 11 * r ^ (n + 1) := by
        dsimp only [b]; rw [if_neg (by omega)]; simp [Nat.add_assoc]
      have hr1 : 1 ≤ r ^ (n + 1) := one_le_pow₀ (by norm_num [r])
      have hs_lt_b : s < b (365 + n + 1) := by rw [hb_n]; linarith
      rw [if_pos hs_lt_b, hb_n, hc_tail n, show 365 + n + 1 = 365 + (n + 1) by omega, hc_tail (n + 1)]
      have hpow : (11 * r ^ (n + 1) / s) ^ 2 = 121 / s ^ 2 * r ^ (2 * (n + 1)) := by
        rw [div_pow, mul_pow, ← pow_mul, mul_comm (n + 1) 2]; ring
      rw [hpow]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have htail_ub : ∑ n ∈ Finset.range N,
      (c (365 + n) - c (365 + n + 1)) *
        (if s < b (365 + n + 1) then (1001 / 1000 : ℝ) * (b (365 + n + 1) / s) ^ 2 - 1 else 0) ≤
      (1001 / 1000 : ℝ) * ((sufList.getD 365 0 : ℝ) / (2500 * 1000000 * s ^ 2)) -
        (gridList.getD 365 0 : ℝ) / 1000000 := by
    rw [htail_eq, hg_props.2.1, mul_one]
    have hF_nn : 0 ≤ F_tail_val := by unfold F_tail_val; positivity
    have h2 : (1001 / 1000 : ℝ) * (F_tail_val * 121 / s ^ 2) * (32 / 25) =
        (1001 / 1000 : ℝ) * ((sufList.getD 365 0 : ℝ) / (2500 * 1000000 * s ^ 2)) := by
      rw [hlast_s]; unfold F_tail_val; push_cast; ring
    have h3 : F_tail_val = (gridList.getD 365 0 : ℝ) / 1000000 := by
      rw [hlast_g]; unfold F_tail_val; rfl
    calc (1001 / 1000 : ℝ) * (F_tail_val * 121 / s ^ 2) *
          (∑ n ∈ Finset.range N, (g n - g (n + 1)) * r ^ (2 * (n + 1))) - F_tail_val
        ≤ (1001 / 1000 : ℝ) * (F_tail_val * 121 / s ^ 2) * (32 / 25) - F_tail_val := by
          gcongr; exact hg_props.1
      _ = (1001 / 1000 : ℝ) * ((sufList.getD 365 0 : ℝ) / (2500 * 1000000 * s ^ 2)) -
            (gridList.getD 365 0 : ℝ) / 1000000 := by
          rw [h2, h3]
  have hsuf_props : ∀ t < 365,
      gridList.getD (t + 1) 0 ≤ gridList.getD t 0 ∧
      sufList.getD t 0 = sufList.getD (t + 1) 0 + (gridList.getD t 0 - gridList.getD (t + 1) 0) * (185 + t + 1) ^ 2 := by
    intro t ht
    have h := checkSuf_getD 0 gridList sufList hsuf_chk (by rw [hlen_g, hlen_s]) t (by rw [hlen_g]; omega)
    simpa only [Nat.add_zero] using h
  have hgrid_split : ∑ t ∈ Finset.range 365,
      (c t - c (t + 1)) * (if s < b (t + 1) then (1001 / 1000 : ℝ) * (b (t + 1) / s) ^ 2 - 1 else 0) =
      (1001 / 1000 : ℝ) * (((sufList.getD j 0 : ℝ) - (sufList.getD 365 0 : ℝ)) / (2500 * 1000000 * s ^ 2)) -
        ((gridList.getD j 0 : ℝ) - (gridList.getD 365 0 : ℝ)) / 1000000 := by
    have hterm_g : ∀ t ∈ Finset.range 365,
        (c t - c (t + 1)) * (if s < b (t + 1) then (1001 / 1000 : ℝ) * (b (t + 1) / s) ^ 2 - 1 else 0) =
        if j ≤ t then
          (1001 / 1000 : ℝ) * (((sufList.getD t 0 : ℝ) - (sufList.getD (t + 1) 0 : ℝ)) / (2500 * 1000000 * s ^ 2)) -
            ((gridList.getD t 0 : ℝ) - (gridList.getD (t + 1) 0 : ℝ)) / 1000000
        else 0 := by
      intro t ht
      rw [Finset.mem_range] at ht
      have hb_t : b (t + 1) = (185 + (t : ℝ) + 1) / 50 := by
        dsimp only [b]; rw [if_pos (by omega)]; push_cast; ring
      have hc_t : c t = (gridList.getD t 0 : ℝ) / 1000000 := by dsimp only [c]; rw [if_pos ht]
      have hc_t1 : c (t + 1) = (gridList.getD (t + 1) 0 : ℝ) / 1000000 := by
        by_cases ht364 : t + 1 < 365
        · dsimp only [c]; rw [if_pos ht364]
        · have : t + 1 = 365 := by omega
          rw [this, hc_365]
      by_cases hjt : j ≤ t
      · have hs_lt : s < b (t + 1) := by
          rw [hb_t]
          have : (j : ℝ) ≤ t := by exact_mod_cast hjt
          linarith [hj_bounds.2]
        rw [if_pos hs_lt, if_pos hjt, hc_t, hc_t1, hb_t]
        have hsp := hsuf_props t ht
        have hsuf_R : (sufList.getD t 0 : ℝ) - (sufList.getD (t + 1) 0 : ℝ) =
            ((gridList.getD t 0 : ℝ) - (gridList.getD (t + 1) 0 : ℝ)) * (185 + (t : ℝ) + 1) ^ 2 := by
          have hsub_eq : sufList.getD t 0 - sufList.getD (t + 1) 0 =
              (gridList.getD t 0 - gridList.getD (t + 1) 0) * (185 + t + 1) ^ 2 := by omega
          have h1 : sufList.getD (t + 1) 0 ≤ sufList.getD t 0 := by omega
          have hR1 : ((sufList.getD t 0 - sufList.getD (t + 1) 0 : ℕ) : ℝ) =
              (sufList.getD t 0 : ℝ) - (sufList.getD (t + 1) 0 : ℝ) := Nat.cast_sub h1
          have hR2 : ((gridList.getD t 0 - gridList.getD (t + 1) 0 : ℕ) : ℝ) =
              (gridList.getD t 0 : ℝ) - (gridList.getD (t + 1) 0 : ℝ) := Nat.cast_sub hsp.1
          have hR := congrArg (Nat.cast : ℕ → ℝ) hsub_eq
          rw [hR1, Nat.cast_mul, hR2] at hR
          push_cast at hR
          exact hR
        rw [hsuf_R]
        have hsq : (((185 + (t : ℝ) + 1) / 50) / s) ^ 2 = (185 + (t : ℝ) + 1) ^ 2 / (2500 * s ^ 2) := by
          ring
        rw [hsq]; ring
      · have hs_ge : b (t + 1) ≤ s := by
          rw [hb_t]
          have : (t : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : t + 1 ≤ j)
          linarith [hj_bounds.1]
        rw [if_neg (by linarith), if_neg hjt, mul_zero]
    rw [Finset.sum_congr rfl hterm_g]
    have hsplit_Ico : ∀ M ≤ 365, j ≤ M →
        ∑ t ∈ Finset.range M, (if j ≤ t then
          (1001 / 1000 : ℝ) * (((sufList.getD t 0 : ℝ) - (sufList.getD (t + 1) 0 : ℝ)) / (2500 * 1000000 * s ^ 2)) -
            ((gridList.getD t 0 : ℝ) - (gridList.getD (t + 1) 0 : ℝ)) / 1000000
        else 0) =
        (1001 / 1000 : ℝ) * (((sufList.getD j 0 : ℝ) - (sufList.getD M 0 : ℝ)) / (2500 * 1000000 * s ^ 2)) -
          ((gridList.getD j 0 : ℝ) - (gridList.getD M 0 : ℝ)) / 1000000 := by
      intro M hM hjM
      induction M, hjM using Nat.le_induction with
      | base =>
        have h0 : ∑ t ∈ Finset.range j, (if j ≤ t then
            (1001 / 1000 : ℝ) * (((sufList.getD t 0 : ℝ) - (sufList.getD (t + 1) 0 : ℝ)) / (2500 * 1000000 * s ^ 2)) -
              ((gridList.getD t 0 : ℝ) - (gridList.getD (t + 1) 0 : ℝ)) / 1000000 else 0) = 0 := by
          apply Finset.sum_eq_zero; intro t ht; rw [Finset.mem_range] at ht; rw [if_neg (by omega)]
        rw [h0]; ring
      | succ M hjM ih =>
        rw [Finset.sum_range_succ, ih (by omega), if_pos hjM]
        ring
    exact hsplit_Ico 365 le_rfl hj_lt.le
  have hden_le : (185 + (j : ℝ)) ^ 2 ≤ 2500 * s ^ 2 := by
    have h1 : (185 + (j : ℝ)) ≤ 50 * s := by linarith [hj_bounds.1]
    have h2 : (185 + (j : ℝ)) ^ 2 ≤ (50 * s) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    linarith [show (50 * s) ^ 2 = 2500 * s ^ 2 by ring]
  have hsufj_nn : 0 ≤ (sufList.getD j 0 : ℝ) := Nat.cast_nonneg _
  have hdiv_le : (sufList.getD j 0 : ℝ) / (2500 * 1000000 * s ^ 2) ≤
      (sufList.getD j 0 : ℝ) / (1000000 * (185 + (j : ℝ)) ^ 2) := by
    apply div_le_div_of_nonneg_left hsufj_nn (by positivity)
    linarith
  have hcomb : (1001 / 1000 : ℝ) * (((sufList.getD j 0 : ℝ) - (sufList.getD 365 0 : ℝ)) / (2500 * 1000000 * s ^ 2)) -
      ((gridList.getD j 0 : ℝ) - (gridList.getD 365 0 : ℝ)) / 1000000 +
      ((1001 / 1000 : ℝ) * ((sufList.getD 365 0 : ℝ) / (2500 * 1000000 * s ^ 2)) -
        (gridList.getD 365 0 : ℝ) / 1000000) =
      (1001 / 1000 : ℝ) * ((sufList.getD j 0 : ℝ) / (2500 * 1000000 * s ^ 2)) - (gridList.getD j 0 : ℝ) / 1000000 := by
    ring
  have hfin : (1001 / 1000 : ℝ) * ((sufList.getD j 0 : ℝ) / (1000000 * (185 + (j : ℝ)) ^ 2)) -
      (gridList.getD j 0 : ℝ) / 1000000 =
      (1001 * (sufList.getD j 0 : ℝ) / (1000 * (185 + (j : ℝ)) ^ 2) - (gridList.getD j 0 : ℝ)) / 1000000 := by
    have : (185 + (j : ℝ)) ≠ 0 := by positivity
    field_simp
  linarith

private lemma telescoping_step_tail {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    {z D : ℝ} (hz : (y0 : ℝ) ≤ z) (hD : 1 ≤ D)
    (hs11 : 11 ≤ Real.log D / Real.log z)
    (ps : List ℕ) (hpw : ps.Pairwise (· > ·))
    (hps : ∀ p ∈ ps, p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z)
    (F : ℝ → ℝ) (hF_tail : ∀ u, 11 ≤ u → F u ≤ A_val / (u - 1) ^ 10) :
    ((tailsPair ps).map fun pr => w pr.1 * Vprod w pr.2 * F (Real.log D / Real.log pr.1)).sum ≤
      Vprod w ps * (A_val / (Real.log D / Real.log z) ^ 10) := by
  let s := Real.log D / Real.log z
  have hs_pos : 0 < s := by linarith
  have hV_pos : 0 < Vprod w ps := Vprod_pos w hw2 ps fun p hp => by
    have := (hps p hp).2.1; omega
  let r : ℝ := 51 / 50
  have hr_gt1 : (1 : ℝ) < r := by norm_num [r]
  let M_u : ℝ := ps.foldr (fun q acc => max (Real.log D / Real.log q) acc) s
  have hMu_ge : ∀ p ∈ ps, Real.log D / Real.log p ≤ M_u := by
    intro p hp
    have : ∀ (l : List ℕ) (init : ℝ), p ∈ l →
        Real.log D / Real.log p ≤ l.foldr (fun q acc => max (Real.log D / Real.log q) acc) init := by
      intro l init hl
      induction l with
      | nil => simp at hl
      | cons a t ih =>
        simp only [List.mem_cons] at hl
        change Real.log D / Real.log p ≤ max (Real.log D / Real.log a) _
        rcases hl with rfl | ht
        · exact le_max_left _ _
        · exact (ih ht).trans (le_max_right _ _)
    exact this ps s hp
  have h_ex : ∃ N ≥ 46, M_u / s < r ^ N := by
    obtain ⟨N0, hN0⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr_gt1).eventually_gt_atTop (M_u / s)).exists_forall_of_atTop
    exact ⟨max N0 46, le_max_right _ _, hN0 _ (le_max_left _ _)⟩
  obtain ⟨N, hN46, hN_gt⟩ := h_ex
  let b : ℕ → ℝ := fun n => s * r ^ n
  let K0 : ℝ := A_val * (11 / 10 : ℝ) ^ 10 / s ^ 10
  let c : ℕ → ℝ := fun n => if n < N then K0 * r⁻¹ ^ (10 * n) else 0
  have hb_inc : ∀ t < N, b t < b (t + 1) := by
    intro t _
    dsimp only [b]
    rw [pow_succ]
    have : 0 < s * r ^ t := mul_pos hs_pos (pow_pos (by linarith) t)
    nlinarith
  have hc_anti : ∀ t < N, c (t + 1) ≤ c t := by
    intro t ht
    dsimp only [c]
    rw [if_pos ht]
    by_cases ht1 : t + 1 < N
    · rw [if_pos ht1]
      apply mul_le_mul_of_nonneg_left _ (by unfold K0 A_val; positivity)
      exact pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hr_gt1).le (by omega)
    · rw [if_neg ht1]; unfold K0 A_val; positivity
  have hF_step : ∀ p ∈ ps, F (Real.log D / Real.log p) ≤
      ∑ t ∈ Finset.range N, (if Real.log D / Real.log p < b (t + 1) then c t - c (t + 1) else 0) := by
    intro p hp
    have hsp := hps p hp
    have hpz : Real.log (p : ℝ) ≤ Real.log z :=
      Real.log_le_log (by exact_mod_cast hsp.1.pos) hsp.2.2
    have hp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hsp.1.one_lt)
    have hu_ge : b 0 ≤ Real.log D / Real.log p := by
      dsimp only [b]; rw [pow_zero, mul_one]
      exact div_le_div_of_nonneg_left (Real.log_nonneg hD) hp_pos hpz
    have hu_lt : Real.log D / Real.log p < b N := by
      dsimp only [b]
      have h1 : M_u < s * r ^ N := (div_lt_iff₀ hs_pos).mp hN_gt |>.trans_eq (mul_comm _ _)
      exact (hMu_ge p hp).trans_lt h1
    apply le_sum_step_of_lt b c hb_inc (by simp [c]) hu_ge hu_lt
    intro t ht hbt _
    dsimp only [c]
    rw [if_pos ht]
    have hbt_11 : 11 ≤ b t := by
      dsimp only [b]
      have : 1 ≤ r ^ t := one_le_pow₀ hr_gt1.le
      nlinarith
    have hu_11 : 11 ≤ Real.log D / Real.log p := hbt_11.trans hbt
    have hu_sub : (10 / 11 : ℝ) * b t ≤ Real.log D / Real.log p - 1 := by linarith
    have hpow_le : ((10 / 11 : ℝ) * (s * r ^ t)) ^ 10 ≤ (Real.log D / Real.log p - 1) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hu_sub 10
    have hA_nn : 0 ≤ A_val := by unfold A_val; positivity
    calc F (Real.log D / Real.log p)
        ≤ A_val / (Real.log D / Real.log p - 1) ^ 10 := hF_tail _ hu_11
      _ ≤ A_val / ((10 / 11 : ℝ) * (s * r ^ t)) ^ 10 :=
          div_le_div_of_nonneg_left hA_nn (by positivity) hpow_le
      _ = K0 * r⁻¹ ^ (10 * t) := by
          dsimp only [K0]
          rw [mul_pow, mul_pow, inv_pow, ← pow_mul, mul_comm 10 t]
          field_simp
  have hmain := sum_tails_step_le hy0 w hw0 hw2 hz hD hs_pos ps hpw hps N b c F hc_anti hF_step
  have hg := geo_tail_bound N hN46
  let g : ℕ → ℝ := fun n => if n < N then r⁻¹ ^ (10 * n) else 0
  have hterm_eq : ∀ t ∈ Finset.range N,
      (c t - c (t + 1)) * (if s < b (t + 1) then (1001 / 1000 : ℝ) * (b (t + 1) / s) ^ 2 - 1 else 0) =
      K0 * ((1001 / 1000 : ℝ) * ((g t - g (t + 1)) * r ^ (2 * (t + 1))) - (g t - g (t + 1))) := by
    intro t _
    have hs_lt : s < b (t + 1) := by
      dsimp only [b]; have : 1 < r ^ (t + 1) := one_lt_pow₀ hr_gt1 (Nat.succ_ne_zero t); nlinarith
    rw [if_pos hs_lt]
    have hct : c t = K0 * g t := by dsimp only [c, g]; split_ifs <;> simp
    have hct1 : c (t + 1) = K0 * g (t + 1) := by dsimp only [c, g]; split_ifs <;> simp
    have hb_eq : (b (t + 1) / s) ^ 2 = r ^ (2 * (t + 1)) := by
      dsimp only [b]
      rw [show s * r ^ (t + 1) / s = r ^ (t + 1) by field_simp, ← pow_mul, mul_comm (t + 1) 2]
    rw [hct, hct1, hb_eq]
    ring
  have hsum_eq : ∑ t ∈ Finset.range N, (c t - c (t + 1)) *
      (if s < b (t + 1) then (1001 / 1000 : ℝ) * (b (t + 1) / s) ^ 2 - 1 else 0) =
      K0 * ((1001 / 1000 : ℝ) * ∑ t ∈ Finset.range N, (g t - g (t + 1)) * r ^ (2 * (t + 1)) -
        ∑ t ∈ Finset.range N, (g t - g (t + 1))) := by
    rw [Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hK0_nn : 0 ≤ K0 := by unfold K0 A_val; positivity
  have hbound_K0 : K0 * ((1001 / 1000 : ℝ) * ∑ t ∈ Finset.range N, (g t - g (t + 1)) * r ^ (2 * (t + 1)) -
      ∑ t ∈ Finset.range N, (g t - g (t + 1))) ≤ A_val / s ^ 10 := by
    have h1 : (1001 / 1000 : ℝ) * ∑ t ∈ Finset.range N, (g t - g (t + 1)) * r ^ (2 * (t + 1)) -
        ∑ t ∈ Finset.range N, (g t - g (t + 1)) ≤ (1001 / 1000 : ℝ) * (32 / 25) - 1 := by
      rw [hg.2.1]
      gcongr
      exact hg.1
    have h2 : K0 * ((1001 / 1000 : ℝ) * (32 / 25) - 1) ≤ A_val / s ^ 10 := by
      dsimp only [K0]
      have hc : (11 / 10 : ℝ) ^ 10 * ((1001 / 1000 : ℝ) * (32 / 25) - 1) ≤ 1 := by norm_num
      have hAs : 0 ≤ A_val / s ^ 10 := by unfold A_val; positivity
      calc A_val * (11 / 10 : ℝ) ^ 10 / s ^ 10 * ((1001 / 1000 : ℝ) * (32 / 25) - 1)
          = (A_val / s ^ 10) * ((11 / 10 : ℝ) ^ 10 * ((1001 / 1000 : ℝ) * (32 / 25) - 1)) := by ring
        _ ≤ (A_val / s ^ 10) * 1 := mul_le_mul_of_nonneg_left hc hAs
        _ = A_val / s ^ 10 := mul_one _
    exact (mul_le_mul_of_nonneg_left h1 hK0_nn).trans h2
  exact hmain.trans (mul_le_mul_of_nonneg_left (hsum_eq ▸ hbound_K0) hV_pos.le)

private lemma telescoping_step_grid {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    {z D : ℝ} (hz : (y0 : ℝ) ≤ z) (hD : 1 ≤ D)
    (hs1 : 37 / 10 ≤ Real.log D / Real.log z) (hs2 : Real.log D / Real.log z < 11)
    (ps : List ℕ) (hpw : ps.Pairwise (· > ·))
    (hps : ∀ p ∈ ps, p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z)
    (gridList sufList : List ℕ)
    (hsuf_chk : checkSuf 0 gridList sufList = true)
    (hlen_g : gridList.length = 366) (hlen_s : sufList.length = 366)
    (hlast_g : gridList.getD 365 0 = F_tail_nat)
    (hlast_s : sufList.getD 365 0 = F_tail_nat * 387200)
    (F phi : ℝ → ℝ)
    (hF_grid : ∀ k : ℕ, k < 365 → ∀ u, (185 + (k : ℝ)) / 50 ≤ u → u < (185 + (k : ℝ) + 1) / 50 →
      F u ≤ (gridList.getD k 0 : ℝ) / 1000000)
    (hF_tail : ∀ u, 11 ≤ u → F u ≤ A_val / (u - 1) ^ 10)
    (h_rec : ∀ j : ℕ, j < 365 → (185 + (j : ℝ)) / 50 ≤ Real.log D / Real.log z →
      Real.log D / Real.log z < (185 + (j : ℝ) + 1) / 50 →
      (1001 * (sufList.getD j 0 : ℝ) / (1000 * (185 + (j : ℝ)) ^ 2) - (gridList.getD j 0 : ℝ)) / 1000000 ≤
        phi (Real.log D / Real.log z)) :
    ((tailsPair ps).map fun pr => w pr.1 * Vprod w pr.2 * F (Real.log D / Real.log pr.1)).sum ≤
      Vprod w ps * phi (Real.log D / Real.log z) := by
  let s := Real.log D / Real.log z
  have hs_pos : 0 < s := by linarith
  have hV_pos : 0 < Vprod w ps := Vprod_pos w hw2 ps fun p hp => by
    have := (hps p hp).2.1; omega
  let r : ℝ := 51 / 50
  have hr_gt1 : (1 : ℝ) < r := by norm_num [r]
  let M_u : ℝ := ps.foldr (fun q acc => max (Real.log D / Real.log q) acc) 11
  have hMu_ge : ∀ p ∈ ps, Real.log D / Real.log p ≤ M_u := by
    intro p hp
    have : ∀ (l : List ℕ) (init : ℝ), p ∈ l →
        Real.log D / Real.log p ≤ l.foldr (fun q acc => max (Real.log D / Real.log q) acc) init := by
      intro l init hl
      induction l with
      | nil => simp at hl
      | cons a t ih =>
        simp only [List.mem_cons] at hl
        change Real.log D / Real.log p ≤ max (Real.log D / Real.log a) _
        rcases hl with rfl | ht
        · exact le_max_left _ _
        · exact (ih ht).trans (le_max_right _ _)
    exact this ps 11 hp
  have h_ex : ∃ N ≥ 46, M_u / 11 < r ^ N := by
    obtain ⟨N0, hN0⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr_gt1).eventually_gt_atTop (M_u / 11)).exists_forall_of_atTop
    exact ⟨max N0 46, le_max_right _ _, hN0 _ (le_max_left _ _)⟩
  obtain ⟨N, hN46, hN_gt⟩ := h_ex
  let K := 365 + N
  let b : ℕ → ℝ := fun t => if t ≤ 365 then (185 + (t : ℝ)) / 50 else 11 * r ^ (t - 365)
  let c : ℕ → ℝ := fun t =>
    if t < 365 then (gridList.getD t 0 : ℝ) / 1000000
    else if t < 365 + N then F_tail_val * r⁻¹ ^ (10 * (t - 365))
    else 0
  have hb_inc : ∀ t < K, b t < b (t + 1) := by
    intro t _
    dsimp only [b]
    by_cases ht : t < 365
    · rw [if_pos (by omega), if_pos (by omega)]; push_cast; linarith
    · by_cases ht365 : t = 365
      · subst ht365
        have h366 : ¬ (365 + 1 ≤ 365) := by decide
        have h1exp : 365 + 1 - 365 = 1 := by decide
        rw [if_pos le_rfl, if_neg h366, h1exp, pow_one]
        norm_num [r]
      · have ht_gt : ¬ t ≤ 365 := by omega
        have ht1_gt : ¬ t + 1 ≤ 365 := by omega
        rw [if_neg ht_gt, if_neg ht1_gt]
        have hsub : t + 1 - 365 = (t - 365) + 1 := by omega
        rw [hsub, pow_succ]
        have hpos_term : 0 < 11 * r ^ (t - 365) := by positivity
        linarith [mul_lt_mul_of_pos_left hr_gt1 hpos_term, show 11 * r ^ (t - 365) * 1 = 11 * r ^ (t - 365) from mul_one _]
  have hc_anti : ∀ t < K, c (t + 1) ≤ c t := by
    intro t ht
    have hsuf_props : ∀ i < 365, gridList.getD (i + 1) 0 ≤ gridList.getD i 0 := fun i hi =>
      (checkSuf_getD 0 gridList sufList hsuf_chk (by rw [hlen_g, hlen_s]) i (by rw [hlen_g]; omega)).1
    dsimp only [c]
    by_cases ht1 : t + 1 < 365
    · have ht365' : t < 365 := by omega
      rw [if_pos ht1, if_pos ht365']
      exact div_le_div_of_nonneg_right (by exact_mod_cast hsuf_props t ht365') (by norm_num)
    · by_cases ht364 : t = 364
      · subst ht364
        have h1 : ¬ (364 + 1 < 365) := by decide
        have h2 : 364 + 1 < 365 + N := by clear hy0; omega
        have h3 : 364 < 365 := by decide
        have hsub0 : 10 * (364 + 1 - 365) = 0 := by decide
        conv_lhs => rw [if_neg h1, if_pos h2, hsub0, pow_zero, mul_one]
        conv_rhs => rw [if_pos h3]
        have hle := hsuf_props 364 h3
        rw [show 364 + 1 = 365 by decide, hlast_g] at hle
        have hF : F_tail_val = (F_tail_nat : ℝ) / 1000000 := rfl
        rw [hF]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (by norm_num)
      · have hnt : ¬ (t < 365) := by clear hy0; omega
        have htk : t < 365 + N := by clear hy0; omega
        conv_rhs => rw [if_neg hnt, if_pos htk]
        by_cases htK1 : t + 1 < 365 + N
        · conv_lhs => rw [if_neg ht1, if_pos htK1]
          apply mul_le_mul_of_nonneg_left _ (by unfold F_tail_val; positivity)
          exact pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hr_gt1).le (by clear hy0; omega)
        · conv_lhs => rw [if_neg ht1, if_neg htK1]
          unfold F_tail_val; positivity
  have hF_step : ∀ p ∈ ps, F (Real.log D / Real.log p) ≤
      ∑ t ∈ Finset.range K, (if Real.log D / Real.log p < b (t + 1) then c t - c (t + 1) else 0) := by
    intro p hp
    have hsp := hps p hp
    have hpz : Real.log (p : ℝ) ≤ Real.log z :=
      Real.log_le_log (by exact_mod_cast hsp.1.pos) hsp.2.2
    have hp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hsp.1.one_lt)
    have hu_ge : b 0 ≤ Real.log D / Real.log p := by
      have h1 : s ≤ Real.log D / Real.log p :=
        div_le_div_of_nonneg_left (Real.log_nonneg hD) hp_pos hpz
      have h0 : b 0 = 37 / 10 := by norm_num [b]
      linarith
    have hu_lt : Real.log D / Real.log p < b K := by
      dsimp only [b, K]
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      have h1 : M_u < 11 * r ^ N := by linarith [(div_lt_iff₀ (by norm_num : (0 : ℝ) < 11)).mp hN_gt]
      exact (hMu_ge p hp).trans_lt h1
    apply le_sum_step_of_lt b c hb_inc (by simp [c, K]) hu_ge hu_lt
    intro t ht hbt hbt1
    by_cases ht365 : t < 365
    · have hb1 : b t = (185 + (t : ℝ)) / 50 := by dsimp only [b]; rw [if_pos (by omega)]
      have hb2 : b (t + 1) = (185 + (t : ℝ) + 1) / 50 := by
        dsimp only [b]; rw [if_pos (by omega)]; push_cast; ring
      have hc_t : c t = (gridList.getD t 0 : ℝ) / 1000000 := by dsimp only [c]; rw [if_pos ht365]
      rw [hc_t]
      exact hF_grid t ht365 _ (hb1 ▸ hbt) (hb2 ▸ hbt1)
    · have hbt_eq : b t = 11 * r ^ (t - 365) := by
        dsimp only [b]
        by_cases h365 : t = 365
        · subst h365; rw [if_pos le_rfl]; norm_num
        · rw [if_neg (by omega)]
      have hbt_11 : 11 ≤ b t := by
        rw [hbt_eq]
        have : 1 ≤ r ^ (t - 365) := one_le_pow₀ hr_gt1.le
        linarith
      have hu_11 : 11 ≤ Real.log D / Real.log p := hbt_11.trans hbt
      have hu_sub : 10 * r ^ (t - 365) ≤ Real.log D / Real.log p - 1 := by
        have hbt' : 11 * r ^ (t - 365) ≤ Real.log D / Real.log p := by rwa [← hbt_eq]
        have h1 : 1 ≤ r ^ (t - 365) := one_le_pow₀ hr_gt1.le
        linarith
      have hc_t : c t = F_tail_val * r⁻¹ ^ (10 * (t - 365)) := by
        dsimp only [c]; rw [if_neg ht365, if_pos ht]
      rw [hc_t]
      have hA_le_F : A_val / 10 ^ 10 ≤ F_tail_val := by
        unfold A_val F_tail_val
        have hR : (A_num_nat : ℝ) ≤ (F_tail_nat : ℝ) * 10 ^ 10 := by exact_mod_cast h_Ftail_ge
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have hpow_le : (10 * r ^ (t - 365)) ^ 10 ≤ (Real.log D / Real.log p - 1) ^ 10 :=
        pow_le_pow_left₀ (by positivity) hu_sub 10
      have hA_nn : 0 ≤ A_val := by unfold A_val; positivity
      calc F (Real.log D / Real.log p)
          ≤ A_val / (Real.log D / Real.log p - 1) ^ 10 := hF_tail _ hu_11
        _ ≤ A_val / (10 * r ^ (t - 365)) ^ 10 :=
            div_le_div_of_nonneg_left hA_nn (by positivity) hpow_le
        _ = (A_val / 10 ^ 10) * r⁻¹ ^ (10 * (t - 365)) := by
            rw [mul_pow, inv_pow, ← pow_mul, mul_comm 10 (t - 365)]; field_simp
        _ ≤ F_tail_val * r⁻¹ ^ (10 * (t - 365)) :=
            mul_le_mul_of_nonneg_right hA_le_F (by positivity)
  have hmain := sum_tails_step_le hy0 w hw0 hw2 hz hD hs_pos ps hpw hps K b c F hc_anti hF_step
  have hgrid := grid_tail_sum_le gridList sufList hsuf_chk hlen_g hlen_s hlast_g hlast_s hs1 hs2 N hN46
  let j := ⌊50 * (s - 37 / 10)⌋₊
  have hj_lt : j < 365 := idx_lt_365 hs1 hs2
  have hj_b := idx_bounds hs1 hs2
  have hrec := h_rec j hj_lt hj_b.1 hj_b.2
  exact hmain.trans (mul_le_mul_of_nonneg_left (hgrid.trans hrec) hV_pos.le)

private lemma telescoping_step {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    {z D : ℝ} (hz : (y0 : ℝ) ≤ z) (hD : 1 ≤ D)
    (ps : List ℕ) (hpw : ps.Pairwise (· > ·))
    (hps : ∀ p ∈ ps, p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z) :
    (494 / 100 ≤ Real.log D / Real.log z →
      ((tailsPair ps).map fun pr => w pr.1 * Vprod w pr.2 * F_m (Real.log D / Real.log pr.1)).sum ≤
        Vprod w ps * phiM (Real.log D / Real.log z)) ∧
    (37 / 10 ≤ Real.log D / Real.log z →
      ((tailsPair ps).map fun pr => w pr.1 * Vprod w pr.2 * F_p (Real.log D / Real.log pr.1)).sum ≤
        Vprod w ps * phiP (Real.log D / Real.log z)) := by
  constructor
  · intro hs
    by_cases hs11 : Real.log D / Real.log z < 11
    · refine telescoping_step_grid hy0 w hw0 hw2 hz hD (by linarith) hs11 ps hpw hps
        fmList sufMList h_sufM h_lenFm h_lenSufM h_fm_last h_sufM_last F_m phiM
        (fun k hk u hu1 hu2 => F_m_le_grid hk hu1 hu2)
        (fun u hu => F_m_le_tail hu) ?_
      intro j hj hj1 hj2
      have hj62 : 62 ≤ j := by
        have h1 : (62 : ℝ) ≤ 50 * (Real.log D / Real.log z - 37 / 10) := by linarith
        have : 50 * (Real.log D / Real.log z - 37 / 10) < (j : ℝ) + 1 := by linarith
        have : (61 : ℝ) < (j : ℝ) := by linarith
        have : 61 < j := by exact_mod_cast this
        omega
      have hrec := checkRecM_getD 0 tabMList fmList.dropLast sufMList.dropLast h_recM j
        (by rw [h_lenM]; exact hj) (by omega)
      simp only [Nat.add_zero] at hrec
      rw [getD_dropLast fmList j 0 (by rw [h_lenFm]; omega),
          getD_dropLast sufMList j 0 (by rw [h_lenSufM]; omega)] at hrec
      have hrecR : (1001 : ℝ) * (sufMList.getD j 0 : ℝ) ≤
          1000 * (185 + (j : ℝ)) ^ 2 * ((tabMList.getD j 0 : ℝ) + (fmList.getD j 0 : ℝ)) := by
        exact_mod_cast hrec
      have hden_pos : (0 : ℝ) < 1000 * (185 + (j : ℝ)) ^ 2 := by positivity
      have h1 : 1001 * (sufMList.getD j 0 : ℝ) / (1000 * (185 + (j : ℝ)) ^ 2) ≤
          (tabMList.getD j 0 : ℝ) + (fmList.getD j 0 : ℝ) :=
        (div_le_iff₀ hden_pos).mpr (by linarith)
      have hidx : ⌊50 * (Real.log D / Real.log z - 37 / 10)⌋₊ = j :=
        Nat.floor_eq_iff (by linarith) |>.mpr ⟨by linarith, by linarith⟩
      have hphi : phiM (Real.log D / Real.log z) = (tabMList.getD j 0 : ℝ) / 1000000 := by
        unfold phiM
        rw [if_neg (by linarith), if_pos hs11, hidx]
      rw [hphi]; linarith
    · have hs11' : 11 ≤ Real.log D / Real.log z := not_lt.mp hs11
      have hphi : phiM (Real.log D / Real.log z) = A_val / (Real.log D / Real.log z) ^ 10 := by
        unfold phiM; rw [if_neg (by linarith), if_neg hs11]
      rw [hphi]
      exact telescoping_step_tail hy0 w hw0 hw2 hz hD hs11' ps hpw hps F_m (fun u hu => F_m_le_tail hu)
  · intro hs
    by_cases hs11 : Real.log D / Real.log z < 11
    · refine telescoping_step_grid hy0 w hw0 hw2 hz hD hs hs11 ps hpw hps
        fpList sufPList h_sufP h_lenFp h_lenSufP h_fp_last h_sufP_last F_p phiP
        (fun k hk u hu1 hu2 => F_p_le_grid hk hu1 hu2)
        (fun u hu => F_p_le_tail hu) ?_
      intro j hj hj1 hj2
      have hrec := checkRecP_getD 0 tabPList fpList.dropLast sufPList.dropLast h_recP j
        (by rw [h_lenP]; exact hj)
      simp only [Nat.add_zero] at hrec
      rw [getD_dropLast fpList j 0 (by rw [h_lenFp]; omega),
          getD_dropLast sufPList j 0 (by rw [h_lenSufP]; omega)] at hrec
      have hrecR : (1001 : ℝ) * (sufPList.getD j 0 : ℝ) ≤
          1000 * (185 + (j : ℝ)) ^ 2 * ((tabPList.getD j 0 : ℝ) + (fpList.getD j 0 : ℝ)) := by
        exact_mod_cast hrec
      have hden_pos : (0 : ℝ) < 1000 * (185 + (j : ℝ)) ^ 2 := by positivity
      have h1 : 1001 * (sufPList.getD j 0 : ℝ) / (1000 * (185 + (j : ℝ)) ^ 2) ≤
          (tabPList.getD j 0 : ℝ) + (fpList.getD j 0 : ℝ) :=
        (div_le_iff₀ hden_pos).mpr (by linarith)
      have hidx : ⌊50 * (Real.log D / Real.log z - 37 / 10)⌋₊ = j :=
        Nat.floor_eq_iff (by linarith) |>.mpr ⟨by linarith, by linarith⟩
      have hphi : phiP (Real.log D / Real.log z) = (tabPList.getD j 0 : ℝ) / 1000000 := by
        unfold phiP
        rw [if_neg (by linarith), if_pos hs11, hidx]
      rw [hphi]; linarith
    · have hs11' : 11 ≤ Real.log D / Real.log z := not_lt.mp hs11
      have hphi : phiP (Real.log D / Real.log z) = A_val / (Real.log D / Real.log z) ^ 10 := by
        unfold phiP; rw [if_neg (by linarith), if_neg hs11]
      rw [hphi]
      exact telescoping_step_tail hy0 w hw0 hw2 hz hD hs11' ps hpw hps F_p (fun u hu => F_p_le_tail hu)

private lemma V_sub_W_minus_le_sum (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (D : ℝ) :
    ∀ l : List ℕ, (∀ p ∈ l, (p : ℝ) ^ (494 / 100 : ℝ) ≤ D) →
      (∀ pr ∈ tailsPair l, W_plus w pr.2 (D / pr.1) - Vprod w pr.2 ≤
        Vprod w pr.2 * F_m (Real.log D / Real.log pr.1)) →
      Vprod w l - W_minus w l D ≤
        ((tailsPair l).map fun pr => w pr.1 * Vprod w pr.2 * F_m (Real.log D / Real.log pr.1)).sum := by
  intro l
  induction l with
  | nil => intro _ _; simp [Vprod, W_minus, tailsPair]
  | cons p rest ih =>
    intro hD h_wp
    have hpD : ¬ D < (p : ℝ) ^ (494 / 100 : ℝ) := not_lt.mpr (hD p List.mem_cons_self)
    unfold W_minus tailsPair
    rw [if_neg hpD, List.map_cons, List.sum_cons]
    have hV : Vprod w (p :: rest) = (1 - w p) * Vprod w rest := by
      simp [Vprod, List.map_cons, List.prod_cons]
    have h1 := ih (fun q hq => hD q (List.mem_cons_of_mem _ hq))
      (fun pr hpr => h_wp pr (List.mem_cons_of_mem _ hpr))
    have h2 := mul_le_mul_of_nonneg_left (h_wp (p, rest) List.mem_cons_self) (hw0 p)
    linarith

private lemma W_plus_sub_V_le_sum (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ))
    (D : ℝ) (hD : 1 ≤ D) :
    ∀ l : List ℕ, (∀ p ∈ l, 5 ≤ p) →
      (∀ pr ∈ tailsPair l, (pr.1 : ℝ) ^ (476 / 100 : ℝ) ≤ D →
        Vprod w pr.2 - W_minus w pr.2 (D / pr.1) ≤
          Vprod w pr.2 * F_p (Real.log D / Real.log pr.1)) →
      W_plus w l D - Vprod w l ≤
        ((tailsPair l).map fun pr => w pr.1 * Vprod w pr.2 * F_p (Real.log D / Real.log pr.1)).sum := by
  intro l
  induction l with
  | nil => intro _ _; simp [Vprod, W_plus, tailsPair]
  | cons p rest ih =>
    intro h5 h_wm
    unfold W_plus tailsPair
    simp only [List.map_cons, List.sum_cons]
    have hV : Vprod w (p :: rest) = (1 - w p) * Vprod w rest := by
      simp [Vprod, List.map_cons, List.prod_cons]
    have h1 := ih (fun q hq => h5 q (List.mem_cons_of_mem _ hq))
      (fun pr hpr => h_wm pr (List.mem_cons_of_mem _ hpr))
    by_cases hpD : (p : ℝ) ^ (476 / 100 : ℝ) ≤ D
    · rw [if_pos hpD]
      have h2 := mul_le_mul_of_nonneg_left (h_wm (p, rest) List.mem_cons_self hpD) (hw0 p)
      linarith
    · rw [if_neg hpD, sub_zero]
      have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h5 p List.mem_cons_self
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
      have hlogD_lt : Real.log D < (476 / 100 : ℝ) * Real.log (p : ℝ) := by
        have hlt : D < (p : ℝ) ^ (476 / 100 : ℝ) := lt_of_not_ge hpD
        calc Real.log D < Real.log ((p : ℝ) ^ (476 / 100 : ℝ)) := Real.log_lt_log (by linarith) hlt
          _ = (476 / 100 : ℝ) * Real.log (p : ℝ) := Real.log_rpow (by linarith) _
      have hs_lt : Real.log D / Real.log (p : ℝ) < 476 / 100 := (div_lt_iff₀ hlogp_pos).mpr hlogD_lt
      have hFp1 : F_p (Real.log D / Real.log (p : ℝ)) = 1 := by simp [F_p, hs_lt]
      rw [hFp1, mul_one]
      linarith

private lemma sieve_main_bound {y0 : ℕ} (hy0 : 2 ^ 200000 ≤ y0)
    (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw2 : ∀ p, w p ≤ 2 / (p : ℝ)) :
    ∀ n : ℕ, ∀ (ps : List ℕ), ps.length ≤ n →
      ps.Pairwise (· > ·) → (∀ p ∈ ps, p.Prime ∧ y0 < p) →
      ∀ (z D : ℝ), (y0 : ℝ) ≤ z → (∀ p ∈ ps, (p : ℝ) ≤ z) →
      1 ≤ D → 37 / 10 ≤ Real.log D / Real.log z →
      (Vprod w ps - W_minus w ps D ≤ Vprod w ps * phiM (Real.log D / Real.log z)) ∧
      (W_plus w ps D - Vprod w ps ≤ Vprod w ps * phiP (Real.log D / Real.log z)) := by
  have hy0_5 : 5 ≤ y0 := by
    have h2 : 2 ^ 3 ≤ 2 ^ 200000 := Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.le_of_lt (by decide : 3 < 200000))
    exact le_trans (by norm_num) (le_trans h2 hy0)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ps hlen hpw hps z D hz hle_z hD hs37
    cases ps with
    | nil =>
      simp only [Vprod, W_minus, W_plus, List.map_nil, List.prod_nil, sub_self, one_mul]
      exact ⟨phiM_nonneg _, phiP_nonneg _⟩
    | cons p rest =>
      have hp_sp := hps p List.mem_cons_self
      have hp5 : 5 ≤ p := by omega
      have hp_z : (p : ℝ) ≤ z := hle_z p List.mem_cons_self
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_sp.1.pos
      have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp_sp.1.one_lt
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt1
      have hlogz_pos : 0 < Real.log z := hlogp_pos.trans_le (Real.log_le_log hp_pos hp_z)
      have hp_pw := List.pairwise_cons.mp hpw
      have hps_p : ∀ q ∈ p :: rest, q.Prime ∧ y0 < q ∧ (q : ℝ) ≤ p := fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hqr
        · exact ⟨hp_sp.1, hp_sp.2, le_rfl⟩
        · have hqsp := hps q (List.mem_cons_of_mem _ hqr)
          exact ⟨hqsp.1, hqsp.2, by exact_mod_cast (hp_pw.1 q hqr).le⟩
      have hps_z : ∀ q ∈ p :: rest, q.Prime ∧ y0 < q ∧ (q : ℝ) ≤ z := fun q hq =>
        ⟨(hps q hq).1, (hps q hq).2, hle_z q hq⟩
      have hlogp_le_z : Real.log (p : ℝ) ≤ Real.log z := Real.log_le_log hp_pos hp_z
      have hs_le_sp : Real.log D / Real.log z ≤ Real.log D / Real.log (p : ℝ) :=
        div_le_div_of_nonneg_left (Real.log_nonneg hD) hlogp_pos hlogp_le_z
      have hsp37 : 37 / 10 ≤ Real.log D / Real.log (p : ℝ) := hs37.trans hs_le_sp
      have hV_pos : 0 < Vprod w (p :: rest) := Vprod_pos w hw2 (p :: rest) fun q hq => by
        have := (hps q hq).2; omega
      constructor
      · by_cases hpD : D < (p : ℝ) ^ (494 / 100 : ℝ)
        · unfold W_minus
          rw [if_pos hpD, sub_zero]
          have hlogD_lt : Real.log D < (494 / 100 : ℝ) * Real.log (p : ℝ) := by
            calc Real.log D < Real.log ((p : ℝ) ^ (494 / 100 : ℝ)) := Real.log_lt_log (by linarith) hpD
              _ = (494 / 100 : ℝ) * Real.log (p : ℝ) := Real.log_rpow hp_pos _
          have hs_lt : Real.log D / Real.log z < 494 / 100 := by
            calc Real.log D / Real.log z < (494 / 100 : ℝ) * Real.log (p : ℝ) / Real.log z :=
                  div_lt_div_of_pos_right hlogD_lt hlogz_pos
              _ ≤ (494 / 100 : ℝ) * Real.log z / Real.log z := by gcongr
              _ = 494 / 100 := by field_simp
          rw [phiM_eq_one_of_lt hs_lt, mul_one]
        · have hpD_ge : (p : ℝ) ^ (494 / 100 : ℝ) ≤ D := not_lt.mp hpD
          have hqD_ge : ∀ q ∈ p :: rest, (q : ℝ) ^ (494 / 100 : ℝ) ≤ D := by
            intro q hq
            have hqp : (q : ℝ) ≤ p := (hps_p q hq).2.2
            have hq_nn : (0 : ℝ) ≤ q := Nat.cast_nonneg q
            exact (Real.rpow_le_rpow hq_nn hqp (by norm_num)).trans hpD_ge
          have h_wp : ∀ pr ∈ tailsPair (p :: rest),
              W_plus w pr.2 (D / pr.1) - Vprod w pr.2 ≤
                Vprod w pr.2 * F_m (Real.log D / Real.log pr.1) := by
            intro pr hpr
            have hpr_mem := mem_tailsPair_fst hpr
            have hpr_sp := hps pr.1 hpr_mem
            have hpr_pos : (0 : ℝ) < pr.1 := by exact_mod_cast hpr_sp.1.pos
            have hpr_gt1 : (1 : ℝ) < pr.1 := by exact_mod_cast hpr_sp.1.one_lt
            have hpr_y0 : (y0 : ℝ) ≤ pr.1 := by exact_mod_cast hpr_sp.2.le
            have hpr_D : (pr.1 : ℝ) ^ (494 / 100 : ℝ) ≤ D := hqD_ge pr.1 hpr_mem
            have hD1 : (pr.1 : ℝ) ^ (394 / 100 : ℝ) ≤ D / pr.1 := by
              rw [le_div_iff₀ hpr_pos]
              have hrp : (pr.1 : ℝ) ^ (394 / 100 : ℝ) * (pr.1 : ℝ) = (pr.1 : ℝ) ^ (494 / 100 : ℝ) := by
                rw [← Real.rpow_add_one hpr_pos.ne']; norm_num
              linarith [hrp]
            have hD1_ge : 1 ≤ D / pr.1 := by
              have : 1 ≤ (pr.1 : ℝ) ^ (394 / 100 : ℝ) := Real.one_le_rpow hpr_gt1.le (by norm_num)
              exact this.trans hD1
            have hs_pr37 : 37 / 10 ≤ Real.log (D / pr.1) / Real.log pr.1 := by
              have hlog_ge : (394 / 100 : ℝ) * Real.log (pr.1 : ℝ) ≤ Real.log (D / pr.1) := by
                calc (394 / 100 : ℝ) * Real.log (pr.1 : ℝ)
                    = Real.log ((pr.1 : ℝ) ^ (394 / 100 : ℝ)) := (Real.log_rpow hpr_pos _).symm
                  _ ≤ Real.log (D / pr.1) := Real.log_le_log (Real.rpow_pos_of_pos hpr_pos _) hD1
              have hlog_pos := Real.log_pos hpr_gt1
              have h1 := (le_div_iff₀ hlog_pos).mpr hlog_ge
              linarith
            have hpw_sub := mem_tailsPair_pairwise hpw hpr
            have hlt_len : pr.2.length < n := (mem_tailsPair_length_lt hpr).trans_le hlen
            have hih := (ih pr.2.length hlt_len pr.2 le_rfl hpw_sub.1
              (fun q hq => hps q (mem_tailsPair_sub hpr q hq)) (pr.1 : ℝ) (D / pr.1) hpr_y0
              (fun q hq => by exact_mod_cast (hpw_sub.2 q hq).le) hD1_ge hs_pr37).2
            have heq_Fm : phiP (Real.log (D / pr.1) / Real.log pr.1) = F_m (Real.log D / Real.log pr.1) := by
              unfold F_m
              congr 1
              rw [Real.log_div (by linarith) hpr_pos.ne']
              have : Real.log (pr.1 : ℝ) ≠ 0 := (Real.log_pos hpr_gt1).ne'
              field_simp
            rwa [← heq_Fm]
          have hV_sum := V_sub_W_minus_le_sum w hw0 D (p :: rest) hqD_ge h_wp
          have hsp494 : 494 / 100 ≤ Real.log D / Real.log (p : ℝ) := by
            have hlog_ge : (494 / 100 : ℝ) * Real.log (p : ℝ) ≤ Real.log D := by
              calc (494 / 100 : ℝ) * Real.log (p : ℝ)
                  = Real.log ((p : ℝ) ^ (494 / 100 : ℝ)) := (Real.log_rpow hp_pos _).symm
                _ ≤ Real.log D := Real.log_le_log (Real.rpow_pos_of_pos hp_pos _) hpD_ge
            exact (le_div_iff₀ hlogp_pos).mpr hlog_ge
          have htel := (telescoping_step hy0 w hw0 hw2 (by exact_mod_cast hp_sp.2.le) hD (p :: rest) hpw
            (fun q hq => ⟨(hps q hq).1, (hps q hq).2, (hps_p q hq).2.2⟩)).1 hsp494
          have hanti := phiM_antitone hs_le_sp
          calc Vprod w (p :: rest) - W_minus w (p :: rest) D
              ≤ Vprod w (p :: rest) * phiM (Real.log D / Real.log (p : ℝ)) := hV_sum.trans htel
            _ ≤ Vprod w (p :: rest) * phiM (Real.log D / Real.log z) :=
                mul_le_mul_of_nonneg_left hanti hV_pos.le
      · have h_wm : ∀ pr ∈ tailsPair (p :: rest), (pr.1 : ℝ) ^ (476 / 100 : ℝ) ≤ D →
            Vprod w pr.2 - W_minus w pr.2 (D / pr.1) ≤
              Vprod w pr.2 * F_p (Real.log D / Real.log pr.1) := by
          intro pr hpr hpr_D
          have hpr_mem := mem_tailsPair_fst hpr
          have hpr_sp := hps pr.1 hpr_mem
          have hpr_pos : (0 : ℝ) < pr.1 := by exact_mod_cast hpr_sp.1.pos
          have hpr_gt1 : (1 : ℝ) < pr.1 := by exact_mod_cast hpr_sp.1.one_lt
          have hpr_y0 : (y0 : ℝ) ≤ pr.1 := by exact_mod_cast hpr_sp.2.le
          have hD1 : (pr.1 : ℝ) ^ (376 / 100 : ℝ) ≤ D / pr.1 := by
            rw [le_div_iff₀ hpr_pos]
            have hrp : (pr.1 : ℝ) ^ (376 / 100 : ℝ) * (pr.1 : ℝ) = (pr.1 : ℝ) ^ (476 / 100 : ℝ) := by
              rw [← Real.rpow_add_one hpr_pos.ne']; norm_num
            linarith [hrp]
          have hD1_ge : 1 ≤ D / pr.1 := by
            have : 1 ≤ (pr.1 : ℝ) ^ (376 / 100 : ℝ) := Real.one_le_rpow hpr_gt1.le (by norm_num)
            exact this.trans hD1
          have hs_pr37 : 37 / 10 ≤ Real.log (D / pr.1) / Real.log pr.1 := by
            have hlog_ge : (376 / 100 : ℝ) * Real.log (pr.1 : ℝ) ≤ Real.log (D / pr.1) := by
              calc (376 / 100 : ℝ) * Real.log (pr.1 : ℝ)
                  = Real.log ((pr.1 : ℝ) ^ (376 / 100 : ℝ)) := (Real.log_rpow hpr_pos _).symm
                _ ≤ Real.log (D / pr.1) := Real.log_le_log (Real.rpow_pos_of_pos hpr_pos _) hD1
            have hlog_pos := Real.log_pos hpr_gt1
            have h1 := (le_div_iff₀ hlog_pos).mpr hlog_ge
            linarith
          have hpw_sub := mem_tailsPair_pairwise hpw hpr
          have hlt_len : pr.2.length < n := (mem_tailsPair_length_lt hpr).trans_le hlen
          have hih := (ih pr.2.length hlt_len pr.2 le_rfl hpw_sub.1
            (fun q hq => hps q (mem_tailsPair_sub hpr q hq)) (pr.1 : ℝ) (D / pr.1) hpr_y0
            (fun q hq => by exact_mod_cast (hpw_sub.2 q hq).le) hD1_ge hs_pr37).1
          have h476 : 476 / 100 ≤ Real.log D / Real.log pr.1 := by
            have hlog_ge : (476 / 100 : ℝ) * Real.log (pr.1 : ℝ) ≤ Real.log D := by
              calc (476 / 100 : ℝ) * Real.log (pr.1 : ℝ)
                  = Real.log ((pr.1 : ℝ) ^ (476 / 100 : ℝ)) := (Real.log_rpow hpr_pos _).symm
                _ ≤ Real.log D := Real.log_le_log (Real.rpow_pos_of_pos hpr_pos _) hpr_D
            exact (le_div_iff₀ (Real.log_pos hpr_gt1)).mpr hlog_ge
          have heq_Fp : phiM (Real.log (D / pr.1) / Real.log pr.1) = F_p (Real.log D / Real.log pr.1) := by
            unfold F_p
            rw [if_neg (not_lt.mpr h476)]
            congr 1
            rw [Real.log_div (by linarith) hpr_pos.ne']
            have : Real.log (pr.1 : ℝ) ≠ 0 := (Real.log_pos hpr_gt1).ne'
            field_simp
          rwa [← heq_Fp]
        have hW_sum := W_plus_sub_V_le_sum w hw0 hw2 D hD (p :: rest) (fun q hq => by
          have := (hps q hq).2; omega) h_wm
        have htel := (telescoping_step hy0 w hw0 hw2 (by exact_mod_cast hp_sp.2.le) hD (p :: rest) hpw
          (fun q hq => ⟨(hps q hq).1, (hps q hq).2, (hps_p q hq).2.2⟩)).2 hsp37
        have hanti := phiP_antitone hs_le_sp
        calc W_plus w (p :: rest) D - Vprod w (p :: rest)
            ≤ Vprod w (p :: rest) * phiP (Real.log D / Real.log (p : ℝ)) := hW_sum.trans htel
          _ ≤ Vprod w (p :: rest) * phiP (Real.log D / Real.log z) :=
              mul_le_mul_of_nonneg_left hanti hV_pos.le

/- ## Section 4: Inclusion-Exclusion, Divisor Count, CRT, and Final Proof of H4 -/

private lemma ind_sound (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)] :
    ∀ (ps : List ℕ) (D : ℝ) (y : ℕ),
      indMinus bad ps D y ≤ (if ∀ p ∈ ps, ¬ bad p y then (1 : ℝ) else 0) ∧
      (if ∀ p ∈ ps, ¬ bad p y then (1 : ℝ) else 0) ≤ indPlus bad ps D y := by
  intro ps
  induction ps with
  | nil => intro D y; simp [indMinus, indPlus]
  | cons p rest ih =>
    intro D y
    have ihD := ih D y
    have ihDp := ih (D / p) y
    have h01 : (0 : ℝ) ≤ if ∀ q ∈ rest, ¬ bad q y then 1 else 0 := by split_ifs <;> norm_num
    have heq : (if ∀ q ∈ p :: rest, ¬ bad q y then (1 : ℝ) else 0) =
        (if ∀ q ∈ rest, ¬ bad q y then (1 : ℝ) else 0) -
          (if bad p y then (if ∀ q ∈ rest, ¬ bad q y then (1 : ℝ) else 0) else 0) := by
      by_cases hp : bad p y <;> by_cases hr : ∀ q ∈ rest, ¬ bad q y <;> simp [hp, hr]
    constructor
    · rw [indMinus]
      by_cases hlt : D < (p : ℝ) ^ (494 / 100 : ℝ)
      · rw [if_pos hlt]; split_ifs <;> norm_num
      · rw [if_neg hlt, heq]
        by_cases hp : bad p y
        · rw [if_pos hp, if_pos hp]; linarith [ihD.1, ihDp.2]
        · rw [if_neg hp, if_neg hp, sub_zero, sub_zero]; exact ihD.1
    · unfold indPlus
      rw [heq]
      by_cases hp : bad p y
      · simp only [hp, ↓reduceIte]
        by_cases hD : (p : ℝ) ^ (476 / 100 : ℝ) ≤ D
        · simp only [hD, and_self, ↓reduceIte]; linarith [ihD.2, ihDp.1]
        · simp only [hD, false_and, ↓reduceIte, sub_zero]
          linarith [ihD.2, h01]
      · simp only [hp, and_false, ↓reduceIte, sub_zero]; exact ihD.2

private lemma W_eq_divs (w : ℕ → ℝ) :
    ∀ (ps d : List ℕ) (D : ℝ),
      ((-1 : ℝ) ^ d.length * (d.map w).prod * W_minus w ps D =
        ((divsMinus d ps D).map fun e => (-1 : ℝ) ^ e.length * (e.map w).prod).sum) ∧
      ((-1 : ℝ) ^ d.length * (d.map w).prod * W_plus w ps D =
        ((divsPlus d ps D).map fun e => (-1 : ℝ) ^ e.length * (e.map w).prod).sum) := by
  intro ps
  induction ps with
  | nil =>
    intro d D
    simp [W_minus, W_plus, divsMinus, divsPlus]
  | cons p rest ih =>
    intro d D
    have ihD := ih d D
    have ihDp := ih (p :: d) (D / p)
    have hp_sgn : (-1 : ℝ) ^ (p :: d).length * ((p :: d).map w).prod =
        -((-1 : ℝ) ^ d.length * (d.map w).prod * w p) := by
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      ring
    constructor
    · unfold W_minus divsMinus
      split_ifs with hlt
      · simp
      · simp only [List.map_append, List.sum_append]
        rw [mul_sub, ihD.1, ← ihDp.2, hp_sgn]
        ring
    · unfold W_plus divsPlus
      split_ifs with hle
      · simp only [List.map_append, List.sum_append]
        rw [mul_sub, ihD.2, ← ihDp.1, hp_sgn]
        ring
      · rw [sub_zero]; exact ihD.2

private lemma ind_eq_divs (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)] :
    ∀ (ps d : List ℕ) (D : ℝ) (y : ℕ),
      ((-1 : ℝ) ^ d.length * (if ∀ q ∈ d, bad q y then (1 : ℝ) else 0) * indMinus bad ps D y =
        ((divsMinus d ps D).map fun e =>
          (-1 : ℝ) ^ e.length * (if ∀ q ∈ e, bad q y then (1 : ℝ) else 0)).sum) ∧
      ((-1 : ℝ) ^ d.length * (if ∀ q ∈ d, bad q y then (1 : ℝ) else 0) * indPlus bad ps D y =
        ((divsPlus d ps D).map fun e =>
          (-1 : ℝ) ^ e.length * (if ∀ q ∈ e, bad q y then (1 : ℝ) else 0)).sum) := by
  intro ps
  induction ps with
  | nil =>
    intro d D y
    simp [indMinus, indPlus, divsMinus, divsPlus]
  | cons p rest ih =>
    intro d D y
    have ihD := ih d D y
    have ihDp := ih (p :: d) (D / p) y
    have hp_ind : (-1 : ℝ) ^ (p :: d).length * (if ∀ q ∈ p :: d, bad q y then (1 : ℝ) else 0) =
        -((-1 : ℝ) ^ d.length * (if ∀ q ∈ d, bad q y then (1 : ℝ) else 0) *
          (if bad p y then (1 : ℝ) else 0)) := by
      simp only [List.length_cons, pow_succ]
      by_cases hpd : ∀ q ∈ p :: d, bad q y
      · rw [if_pos hpd, if_pos (fun q hq => hpd q (List.mem_cons_of_mem _ hq)),
            if_pos (hpd p List.mem_cons_self)]
        ring
      · rw [if_neg hpd]
        by_cases hp : bad p y
        · have hnd : ¬ ∀ q ∈ d, bad q y := fun h => hpd fun q hq => by
            rcases List.mem_cons.mp hq with rfl | hqd; exact hp; exact h q hqd
          rw [if_neg hnd]; ring
        · rw [if_neg hp]; ring
    constructor
    · rw [indMinus, divsMinus]
      by_cases hlt : D < (p : ℝ) ^ (494 / 100 : ℝ)
      · rw [if_pos hlt, if_pos hlt]; simp
      · rw [if_neg hlt, if_neg hlt, List.map_append, List.sum_append, ← ihDp.2, hp_ind, ← ihD.1]
        by_cases hp : bad p y
        · rw [if_pos hp, if_pos hp]; ring
        · rw [if_neg hp, if_neg hp]; ring
    · rw [indPlus, divsPlus]
      by_cases hle : (p : ℝ) ^ (476 / 100 : ℝ) ≤ D
      · rw [if_pos hle, List.map_append, List.sum_append]
        by_cases hd : ∀ q ∈ d, bad q y
        · rw [if_pos hd]
          by_cases hp : bad p y
          · rw [if_pos ⟨hle, hp⟩, ← ihDp.1, hp_ind, if_pos hd, if_pos hp, ← ihD.2, if_pos hd]; ring
          · rw [if_neg (fun h => hp h.2), sub_zero, ← ihDp.1, hp_ind, if_pos hd, if_neg hp, ← ihD.2, if_pos hd]; ring
        · rw [if_neg hd, mul_zero, zero_mul, ← ihDp.1, hp_ind, if_neg hd, ← ihD.2, if_neg hd]
          simp [mul_zero, zero_mul]
      · rw [if_neg hle]
        by_cases hd : ∀ q ∈ d, bad q y
        · rw [if_pos hd, if_neg (fun h => hle h.1), sub_zero, ← ihD.2, if_pos hd]
        · rw [if_neg hd, mul_zero, zero_mul, ← ihD.2, if_neg hd, mul_zero, zero_mul]

private lemma divs_invariant :
    ∀ (ps d : List ℕ) (D : ℝ),
      ps.Pairwise (· > ·) → d.Pairwise (· < ·) → (∀ q ∈ d, ∀ p ∈ ps, p < q) →
      (∀ p ∈ ps, 2 ≤ p) → 1 ≤ D → (∀ q ∈ d, 2 ≤ q) →
      (∀ e ∈ divsMinus d ps D,
        e.Pairwise (· < ·) ∧ (∀ q ∈ e, q ∈ ps ∨ q ∈ d) ∧ (∀ q ∈ e, 2 ≤ q) ∧
        (∀ q ∈ d, q ∈ e) ∧ (e.prod : ℝ) ≤ (d.prod : ℝ) * D) ∧
      (∀ e ∈ divsPlus d ps D,
        e.Pairwise (· < ·) ∧ (∀ q ∈ e, q ∈ ps ∨ q ∈ d) ∧ (∀ q ∈ e, 2 ≤ q) ∧
        (∀ q ∈ d, q ∈ e) ∧ (e.prod : ℝ) ≤ (d.prod : ℝ) * D) ∧
      (divsMinus d ps D).Nodup ∧ (divsPlus d ps D).Nodup := by
  intro ps
  induction ps with
  | nil =>
    intro d D _ hd _ _ hD hd2
    refine ⟨?_, ?_, List.nodup_singleton d, List.nodup_singleton d⟩ <;>
    · intro e he
      change e ∈ [d] at he
      simp only [List.mem_singleton] at he
      subst he
      refine ⟨hd, fun q hq => Or.inr hq, hd2, fun q hq => hq, ?_⟩
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) hD
  | cons p rest ih =>
    intro d D hpw hd hlt hp2 hD hd2
    have hpw_c := List.pairwise_cons.mp hpw
    have hp_rest : ∀ q ∈ rest, q < p := hpw_c.1
    have hpw_rest : rest.Pairwise (· > ·) := hpw_c.2
    have hp2_p : 2 ≤ p := hp2 p List.mem_cons_self
    have hrest2 : ∀ q ∈ rest, 2 ≤ q := fun q hq => hp2 q (List.mem_cons_of_mem _ hq)
    have hlt_rest : ∀ q ∈ d, ∀ r ∈ rest, r < q := fun q hq r hr => hlt q hq r (List.mem_cons_of_mem _ hr)
    have hpd_pw : (p :: d).Pairwise (· < ·) :=
      List.pairwise_cons.mpr ⟨fun q hq => hlt q hq p List.mem_cons_self, hd⟩
    have hpd_lt : ∀ q ∈ p :: d, ∀ r ∈ rest, r < q := by
      intro q hq r hr
      rcases List.mem_cons.mp hq with rfl | hqd
      · exact hp_rest r hr
      · exact hlt_rest q hqd r hr
    have hpd2 : ∀ q ∈ p :: d, 2 ≤ q := by
      intro q hq; rcases List.mem_cons.mp hq with rfl | hqd; exact hp2_p; exact hd2 q hqd
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    have hihD := ih d D hpw_rest hd hlt_rest hrest2 hD hd2
    have h_p_not_d : p ∉ d := fun h => absurd (hlt p h p List.mem_cons_self) (lt_irrefl p)
    have h_p_not_rest : p ∉ rest := fun h => absurd (hp_rest p h) (lt_irrefl p)
    have hm : (∀ e ∈ divsMinus d (p :: rest) D,
        e.Pairwise (· < ·) ∧ (∀ q ∈ e, q ∈ p :: rest ∨ q ∈ d) ∧ (∀ q ∈ e, 2 ≤ q) ∧
        (∀ q ∈ d, q ∈ e) ∧ (e.prod : ℝ) ≤ (d.prod : ℝ) * D) ∧
        (divsMinus d (p :: rest) D).Nodup := by
      unfold divsMinus
      split_ifs with hltD
      · exact ⟨fun _ h => by simp at h, List.nodup_nil⟩
      · have hpD : (p : ℝ) ^ (494 / 100 : ℝ) ≤ D := not_lt.mp hltD
        have hDp : (1 : ℝ) ≤ D / p := by
          rw [one_le_div hp_pos]
          calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (p : ℝ) ^ (494 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp_gt1.le (by norm_num)
            _ ≤ D := hpD
        have hihDp := ih (p :: d) (D / p) hpw_rest hpd_pw hpd_lt hrest2 hDp hpd2
        refine ⟨?_, ?_⟩
        · intro e he
          rcases List.mem_append.mp he with he1 | he2
          · obtain ⟨a, b, c, d1, e1⟩ := hihD.1 e he1
            exact ⟨a, fun q hq => (b q hq).imp (List.mem_cons_of_mem p) id, c, d1, e1⟩
          · obtain ⟨a, b, c, d1, e1⟩ := hihDp.2.1 e he2
            refine ⟨a, ?_, c, fun q hq => d1 q (List.mem_cons_of_mem p hq), ?_⟩
            · intro q hq
              rcases b q hq with hqr | hqd
              · exact Or.inl (List.mem_cons_of_mem _ hqr)
              · rcases List.mem_cons.mp hqd with rfl | hqd'
                · exact Or.inl List.mem_cons_self
                · exact Or.inr hqd'
            · calc (e.prod : ℝ) ≤ ((p :: d).prod : ℝ) * (D / p) := e1
                _ = (p : ℝ) * (d.prod : ℝ) * (D / p) := by simp [List.prod_cons]
                _ = (d.prod : ℝ) * D := by field_simp
        · rw [List.nodup_append]
          refine ⟨hihD.2.2.1, hihDp.2.2.2, ?_⟩
          intro e₁ he1 e₂ he2 heq
          subst heq
          have hp_not_e : p ∉ e₁ := by
            intro hpe
            rcases (hihD.1 e₁ he1).2.1 p hpe with hpr | hpd
            · exact h_p_not_rest hpr
            · exact h_p_not_d hpd
          exact hp_not_e ((hihDp.2.1 e₁ he2).2.2.2.1 p List.mem_cons_self)
    have hp_b : (∀ e ∈ divsPlus d (p :: rest) D,
        e.Pairwise (· < ·) ∧ (∀ q ∈ e, q ∈ p :: rest ∨ q ∈ d) ∧ (∀ q ∈ e, 2 ≤ q) ∧
        (∀ q ∈ d, q ∈ e) ∧ (e.prod : ℝ) ≤ (d.prod : ℝ) * D) ∧
        (divsPlus d (p :: rest) D).Nodup := by
      unfold divsPlus
      split_ifs with hleD
      · have hDp : (1 : ℝ) ≤ D / p := by
          rw [one_le_div hp_pos]
          calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (p : ℝ) ^ (476 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp_gt1.le (by norm_num)
            _ ≤ D := hleD
        have hihDp := ih (p :: d) (D / p) hpw_rest hpd_pw hpd_lt hrest2 hDp hpd2
        refine ⟨?_, ?_⟩
        · intro e he
          rcases List.mem_append.mp he with he1 | he2
          · obtain ⟨a, b, c, d1, e1⟩ := hihD.2.1 e he1
            exact ⟨a, fun q hq => (b q hq).imp (List.mem_cons_of_mem p) id, c, d1, e1⟩
          · obtain ⟨a, b, c, d1, e1⟩ := hihDp.1 e he2
            refine ⟨a, ?_, c, fun q hq => d1 q (List.mem_cons_of_mem p hq), ?_⟩
            · intro q hq
              rcases b q hq with hqr | hqd
              · exact Or.inl (List.mem_cons_of_mem _ hqr)
              · rcases List.mem_cons.mp hqd with rfl | hqd'
                · exact Or.inl List.mem_cons_self
                · exact Or.inr hqd'
            · calc (e.prod : ℝ) ≤ ((p :: d).prod : ℝ) * (D / p) := e1
                _ = (p : ℝ) * (d.prod : ℝ) * (D / p) := by simp [List.prod_cons]
                _ = (d.prod : ℝ) * D := by field_simp
        · rw [List.nodup_append]
          refine ⟨hihD.2.2.2, hihDp.2.2.1, ?_⟩
          intro e₁ he1 e₂ he2 heq
          subst heq
          have hp_not_e : p ∉ e₁ := by
            intro hpe
            rcases (hihD.2.1 e₁ he1).2.1 p hpe with hpr | hpd
            · exact h_p_not_rest hpr
            · exact h_p_not_d hpd
          exact hp_not_e ((hihDp.1 e₁ he2).2.2.2.1 p List.mem_cons_self)
      · refine ⟨?_, hihD.2.2.2⟩
        intro e he
        obtain ⟨a, b, c, d1, e1⟩ := hihD.2.1 e he
        exact ⟨a, fun q hq => (b q hq).imp (List.mem_cons_of_mem p) id, c, d1, e1⟩
    exact ⟨hm.1, hp_b.1, hm.2, hp_b.2⟩

private lemma prime_dvd_list_prod : ∀ {p : ℕ} {l : List ℕ},
    p.Prime → p ∣ l.prod → ∃ q ∈ l, p ∣ q := by
  intro p l hp hd
  induction l with
  | nil =>
    simp only [List.prod_nil] at hd
    exact absurd (Nat.dvd_one.mp hd) hp.ne_one
  | cons a t ih =>
    simp only [List.prod_cons] at hd
    rcases hp.dvd_mul.mp hd with hpa | hpt
    · exact ⟨a, List.mem_cons_self, hpa⟩
    · obtain ⟨q, hqt, hqp⟩ := ih hpt
      exact ⟨q, List.mem_cons_of_mem _ hqt, hqp⟩

private lemma prod_inj_of_pairwise_prime : ∀ e₁ e₂ : List ℕ,
    e₁.Pairwise (· < ·) → e₂.Pairwise (· < ·) →
    (∀ p ∈ e₁, p.Prime) → (∀ p ∈ e₂, p.Prime) →
    e₁.prod = e₂.prod → e₁ = e₂ := by
  intro e₁
  induction e₁ with
  | nil =>
    intro e₂ _ _ _ hp2 heq
    cases e₂ with
    | nil => rfl
    | cons q t =>
      simp only [List.prod_nil, List.prod_cons] at heq
      have hq2 := (hp2 q List.mem_cons_self).two_le
      have h1 : q ∣ 1 := ⟨t.prod, heq⟩
      have := Nat.dvd_one.mp h1
      omega
  | cons p t₁ ih =>
    intro e₂ hw1 hw2 hp1 hp2 heq
    cases e₂ with
    | nil =>
      simp only [List.prod_nil, List.prod_cons] at heq
      have hp2' := (hp1 p List.mem_cons_self).two_le
      have h1 : p ∣ 1 := ⟨t₁.prod, heq.symm⟩
      have := Nat.dvd_one.mp h1
      omega
    | cons q t₂ =>
      have hp_prime := hp1 p List.mem_cons_self
      have hq_prime := hp2 q List.mem_cons_self
      have hp_lt_t1 := (List.pairwise_cons.mp hw1).1
      have hq_lt_t2 := (List.pairwise_cons.mp hw2).1
      have hp_dvd : p ∣ (q :: t₂).prod := by rw [← heq]; exact List.dvd_prod List.mem_cons_self
      have hq_dvd : q ∣ (p :: t₁).prod := by rw [heq]; exact List.dvd_prod List.mem_cons_self
      obtain ⟨r₁, hr₁_mem, hr₁_dvd⟩ := prime_dvd_list_prod hp_prime hp_dvd
      obtain ⟨r₂, hr₂_mem, hr₂_dvd⟩ := prime_dvd_list_prod hq_prime hq_dvd
      have hp_eq_r1 : p = r₁ := ((Nat.dvd_prime (hp2 r₁ hr₁_mem)).mp hr₁_dvd).resolve_left hp_prime.ne_one
      have hq_eq_r2 : q = r₂ := ((Nat.dvd_prime (hp1 r₂ hr₂_mem)).mp hr₂_dvd).resolve_left hq_prime.ne_one
      have hq_le_p : q ≤ p := by
        rcases List.mem_cons.mp hr₁_mem with rfl | hr1
        · exact hp_eq_r1.ge
        · exact (hq_lt_t2 r₁ hr1).le.trans hp_eq_r1.ge
      have hp_le_q : p ≤ q := by
        rcases List.mem_cons.mp hr₂_mem with rfl | hr2
        · exact hq_eq_r2.ge
        · exact (hp_lt_t1 r₂ hr2).le.trans hq_eq_r2.ge
      have hpq : p = q := le_antisymm hp_le_q hq_le_p
      subst hpq
      simp only [List.prod_cons] at heq
      have ht_eq : t₁.prod = t₂.prod := Nat.eq_of_mul_eq_mul_left hp_prime.pos heq
      have ht := ih t₂ (List.pairwise_cons.mp hw1).2 (List.pairwise_cons.mp hw2).2
        (fun a ha => hp1 a (List.mem_cons_of_mem _ ha))
        (fun a ha => hp2 a (List.mem_cons_of_mem _ ha)) ht_eq
      rw [ht]

private lemma two_pow_le_card_divisors (e : List ℕ) (hnd : e.Nodup) (hp : ∀ p ∈ e, p.Prime) :
    2 ^ e.length ≤ e.prod.divisors.card := by
  have he_pos : e.prod ≠ 0 :=
    List.prod_ne_zero fun h0 => (hp 0 h0).ne_zero rfl
  have he_eq : e.prod = ∏ p ∈ e.toFinset, p := by
    conv_rhs => rw [List.prod_toFinset (fun p : ℕ => p) hnd]
    simp
  have hinj : ∀ s₁ ∈ e.toFinset.powerset, ∀ s₂ ∈ e.toFinset.powerset,
      (∏ p ∈ s₁, p) = (∏ p ∈ s₂, p) → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ hprod
    have hsub1 : s₁ ⊆ e.toFinset := Finset.mem_powerset.mp hs₁
    have hsub2 : s₂ ⊆ e.toFinset := Finset.mem_powerset.mp hs₂
    ext p
    constructor
    · intro hp1
      have hp_prime := hp p (List.mem_toFinset.mp (hsub1 hp1))
      have hdvd : p ∣ ∏ q ∈ s₂, q := by rw [← hprod]; exact Finset.dvd_prod_of_mem _ hp1
      obtain ⟨q, hq2, hqp⟩ := (hp_prime.prime.dvd_finsetProd_iff id).mp hdvd
      have hq_prime := hp q (List.mem_toFinset.mp (hsub2 hq2))
      have heq : p = q := ((Nat.dvd_prime hq_prime).mp hqp).resolve_left hp_prime.ne_one
      rwa [heq]
    · intro hp2
      have hp_prime := hp p (List.mem_toFinset.mp (hsub2 hp2))
      have hdvd : p ∣ ∏ q ∈ s₁, q := by rw [hprod]; exact Finset.dvd_prod_of_mem _ hp2
      obtain ⟨q, hq1, hqp⟩ := (hp_prime.prime.dvd_finsetProd_iff id).mp hdvd
      have hq_prime := hp q (List.mem_toFinset.mp (hsub1 hq1))
      have heq : p = q := ((Nat.dvd_prime hq_prime).mp hqp).resolve_left hp_prime.ne_one
      rwa [heq]
  have hcard : e.toFinset.powerset.card ≤ e.prod.divisors.card := by
    apply Finset.card_le_card_of_injOn (fun s => ∏ p ∈ s, p)
    · intro s hs
      rw [Finset.mem_coe, Nat.mem_divisors]
      refine ⟨?_, he_pos⟩
      rw [he_eq]
      exact Finset.prod_dvd_prod_of_subset s e.toFinset id (Finset.mem_powerset.mp hs)
    · intro s₁ hs₁ s₂ hs₂ hprod
      exact hinj s₁ hs₁ s₂ hs₂ hprod
  rw [Finset.card_powerset, List.toFinset_card_of_nodup hnd] at hcard
  exact hcard

private lemma sum_card_divisors_Icc_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ≤ (N : ℝ) * (Real.log N + 1) := by
  have hharm : ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d ≤ Real.log N + 1 := by
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) := by
        have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((N + 1 : ℕ) : ℝ) / N by positivity)
        rw [Real.log_div (by positivity) (by positivity), inv_div] at h
        have heq : 1 - (N : ℝ) / ((N + 1 : ℕ) : ℝ) = 1 / ((N + 1 : ℕ) : ℝ) := by
          push_cast; field_simp <;> ring
        linarith
      linarith
  have hbij : ∑ n ∈ Finset.Icc 1 N, n.divisors.card = ∑ d ∈ Finset.Icc 1 N, (N / d) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, n.divisors.card = ((Finset.Icc 1 N).sigma Nat.divisors).card := by
      rw [Finset.card_sigma]
    have h2 : ∑ d ∈ Finset.Icc 1 N, (N / d) =
        ((Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d))).card := by
      rw [Finset.card_sigma]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_Icc] at hd
      have hdiv_pos : 1 ≤ N / d := Nat.div_pos hd.2 hd.1
      rw [Nat.card_Icc]; omega
    rw [h1, h2]
    apply Finset.card_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
    · intro ⟨n, d⟩ hnd
      rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hnd
      dsimp only at hnd
      rcases hnd with ⟨⟨hn1, hnN⟩, hd_dvd, _⟩
      have hd_pos : 1 ≤ d := Nat.pos_of_ne_zero fun h0 => by
        subst h0; simp only [zero_dvd_iff] at hd_dvd; omega
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd
      have hq_pos : 1 ≤ n / d := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hmul; omega
      have hd_le_N : d ≤ N := (Nat.le_of_dvd (by omega) hd_dvd).trans hnN
      have hq_le : n / d ≤ N / d := Nat.div_le_div_right hnN
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨hd_pos, hd_le_N⟩, ⟨hq_pos, hq_le⟩⟩
    · intro ⟨n₁, d₁⟩ h₁ ⟨n₂, d₂⟩ h₂ heq
      rw [Finset.mem_sigma, Nat.mem_divisors] at h₁ h₂
      dsimp only at h₁ h₂ heq
      have hd : d₁ = d₂ := congrArg Sigma.fst heq
      subst hd
      have hq : n₁ / d₁ = n₂ / d₁ := congrArg Sigma.snd heq
      have hn : n₁ = n₂ := by
        rw [← Nat.mul_div_cancel' h₁.2.1, ← Nat.mul_div_cancel' h₂.2.1, hq]
      simp [hn]
    · intro ⟨d, k⟩ hdk
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hdk
      dsimp only at hdk
      rcases hdk with ⟨⟨hd1, hdN⟩, ⟨hk1, hkN⟩⟩
      refine ⟨⟨d * k, d⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
        have hmul_le : d * k ≤ N := (Nat.mul_le_mul_left d hkN).trans (Nat.mul_div_le N d)
        have hmul_pos : 1 ≤ d * k := Nat.mul_pos hd1 hk1
        exact ⟨⟨hmul_pos, hmul_le⟩, dvd_mul_right d k, (Nat.mul_pos hd1 hk1).ne'⟩
      · dsimp only
        have : d * k / d = k := Nat.mul_div_cancel_left k hd1
        simp [this]
  calc ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) := by exact_mod_cast hbij
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (N : ℝ) / d := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd_pos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
        rw [le_div_iff₀ hd_pos]
        exact_mod_cast Nat.div_mul_le_self N d
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ (N : ℝ) * (Real.log N + 1) := mul_le_mul_of_nonneg_left hharm (Nat.cast_nonneg _)

private lemma divs_sum_le (ps : List ℕ) (hpw : ps.Pairwise (· > ·)) (hps : ∀ p ∈ ps, p.Prime)
    {D : ℝ} (hD : 1 ≤ D) :
    ((divsMinus [] ps D).map fun e => (2 : ℝ) ^ e.length).sum ≤ D * (Real.log D + 1) := by
  have hinv := divs_invariant ps [] D hpw List.Pairwise.nil (by simp)
    (fun p hp => (hps p hp).two_le) hD (by simp)
  have hnodup : (divsMinus [] ps D).Nodup := hinv.2.2.1
  rw [← List.sum_toFinset _ hnodup]
  have hfloor_pos : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hD)
  have hcard_le : ∑ e ∈ (divsMinus [] ps D).toFinset, (2 : ℝ) ^ e.length ≤
      ∑ n ∈ Finset.Icc 1 ⌊D⌋₊, (n.divisors.card : ℝ) := by
    have h1 : ∑ e ∈ (divsMinus [] ps D).toFinset, (2 : ℝ) ^ e.length ≤
        ∑ e ∈ (divsMinus [] ps D).toFinset, (e.prod.divisors.card : ℝ) := by
      refine Finset.sum_le_sum fun e he => ?_
      have he_mem := List.mem_toFinset.mp he
      have he_inv := hinv.1 e he_mem
      have he_nd : e.Nodup := he_inv.1.imp fun {a b} (h : a < b) => h.ne
      have he_pr : ∀ q ∈ e, q.Prime := fun q hq => by
        rcases he_inv.2.1 q hq with hqp | hqd
        · exact hps q hqp
        · simp at hqd
      exact_mod_cast two_pow_le_card_divisors e he_nd he_pr
    have h_inj : Set.InjOn List.prod ((divsMinus [] ps D).toFinset : Set (List ℕ)) := by
      intro e₁ he₁ e₂ he₂ heq
      have h1' := hinv.1 e₁ (List.mem_toFinset.mp he₁)
      have h2' := hinv.1 e₂ (List.mem_toFinset.mp he₂)
      have hp1 : ∀ q ∈ e₁, q.Prime := fun q hq => by
        rcases h1'.2.1 q hq with hqp | hqd; exact hps q hqp; simp at hqd
      have hp2 : ∀ q ∈ e₂, q.Prime := fun q hq => by
        rcases h2'.2.1 q hq with hqp | hqd; exact hps q hqp; simp at hqd
      exact prod_inj_of_pairwise_prime e₁ e₂ h1'.1 h2'.1 hp1 hp2 heq
    have h2 : ∑ e ∈ (divsMinus [] ps D).toFinset, (e.prod.divisors.card : ℝ) ≤
        ∑ n ∈ Finset.Icc 1 ⌊D⌋₊, (n.divisors.card : ℝ) := by
      rw [← Finset.sum_image (f := fun n : ℕ => (n.divisors.card : ℝ)) (g := List.prod) h_inj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨e, he, rfl⟩
      rw [Finset.mem_Icc]
      have he_mem := List.mem_toFinset.mp he
      have he_inv := hinv.1 e he_mem
      have he_pos : 1 ≤ e.prod := by
        refine Nat.pos_of_ne_zero (List.prod_ne_zero fun h0 => ?_)
        have := he_inv.2.2.1 0 h0
        omega
      have he_le : e.prod ≤ ⌊D⌋₊ := Nat.le_floor (by simpa using he_inv.2.2.2.2)
      exact ⟨he_pos, he_le⟩
    exact h1.trans h2
  have hfl_le : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le (by linarith)
  have hlog_le : Real.log (⌊D⌋₊ : ℝ) + 1 ≤ Real.log D + 1 := by
    linarith [Real.log_le_log (by exact_mod_cast hfloor_pos) hfl_le]
  calc ∑ e ∈ (divsMinus [] ps D).toFinset, (2 : ℝ) ^ e.length
      ≤ ∑ n ∈ Finset.Icc 1 ⌊D⌋₊, (n.divisors.card : ℝ) := hcard_le
    _ ≤ (⌊D⌋₊ : ℝ) * (Real.log (⌊D⌋₊ : ℝ) + 1) := sum_card_divisors_Icc_le ⌊D⌋₊ hfloor_pos
    _ ≤ D * (Real.log D + 1) := by
        apply mul_le_mul hfl_le hlog_le
        · have : 0 ≤ Real.log (⌊D⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hfloor_pos)
          linarith
        · linarith

private lemma crt_const_exists (y0 : ℕ) (a b : ℤ)
    (ha : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ y0 → ¬ ((p : ℤ) ∣ a)) :
    let Q0 := 2 * ∏ p ∈ (Finset.Icc 3 y0).filter Nat.Prime, p
    ∃ x0 < Q0, ¬ 2 ∣ x0 ∧
      ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ y0 →
        ¬ ((p : ℤ) ∣ (x0 : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x0 : ℤ) + b) := by
  intro Q0
  have hgen : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ 3 ≤ p ∧ ¬ ((p : ℤ) ∣ a)) →
      ∃ x0 < 2 * ∏ p ∈ T, p, ¬ 2 ∣ x0 ∧
        ∀ p ∈ T, ¬ ((p : ℤ) ∣ (x0 : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x0 : ℤ) + b) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, by norm_num, by omega, by simp⟩
    | @insert p T hpT ih =>
      intro hT
      have hp_sp := hT p (Finset.mem_insert_self p T)
      have hT_sub : ∀ q ∈ T, q.Prime ∧ 3 ≤ q ∧ ¬ ((q : ℤ) ∣ a) :=
        fun q hq => hT q (Finset.mem_insert_of_mem hq)
      obtain ⟨x', hx'_lt, hx'_odd, hx'_good⟩ := ih hT_sub
      let QT := 2 * ∏ q ∈ T, q
      have hQT_pos : 0 < QT := by
        refine mul_pos (by norm_num) (Finset.prod_pos fun q hq => (hT_sub q hq).1.pos)
      have hcop_prod : Nat.Coprime p (∏ q ∈ T, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        exact (Nat.coprime_primes hp_sp.1 (hT_sub q hq).1).mpr (fun h => hpT (h ▸ hq))
      have hcop_2 : Nat.Coprime p 2 :=
        (Nat.coprime_primes hp_sp.1 Nat.prime_two).mpr (by omega)
      have hcop_QT : Nat.Coprime p QT := hcop_2.mul_right hcop_prod
      have hp_ndvd_QT : ¬ p ∣ QT := hp_sp.1.coprime_iff_not_dvd.mp hcop_QT
      have hp_int_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_sp.1
      have h_inj_x : ∀ k₁ k₂ : ℕ, k₁ < k₂ → k₂ ≤ 2 →
          (p : ℤ) ∣ ((x' + k₁ * QT : ℕ) : ℤ) → ¬ ((p : ℤ) ∣ ((x' + k₂ * QT : ℕ) : ℤ)) := by
        intro k₁ k₂ h12 h2 hd1 hd2
        have hsub : (p : ℤ) ∣ ((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ) := by
          have : ((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ) = ((x' + k₂ * QT : ℕ) : ℤ) - ((x' + k₁ * QT : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub h12.le]; ring
          rw [this]; exact dvd_sub hd2 hd1
        have hnat : p ∣ (k₂ - k₁) * QT := Int.natCast_dvd_natCast.mp (by exact_mod_cast hsub)
        rcases hp_sp.1.dvd_mul.mp hnat with hd_k | hd_Q
        · have : p ≤ k₂ - k₁ := Nat.le_of_dvd (by omega) hd_k
          omega
        · exact hp_ndvd_QT hd_Q
      have h_inj_ax : ∀ k₁ k₂ : ℕ, k₁ < k₂ → k₂ ≤ 2 →
          (p : ℤ) ∣ a * ((x' + k₁ * QT : ℕ) : ℤ) + b →
          ¬ ((p : ℤ) ∣ a * ((x' + k₂ * QT : ℕ) : ℤ) + b) := by
        intro k₁ k₂ h12 h2 hd1 hd2
        have hsub : (p : ℤ) ∣ a * (((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ)) := by
          have : a * (((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ)) =
              (a * ((x' + k₂ * QT : ℕ) : ℤ) + b) - (a * ((x' + k₁ * QT : ℕ) : ℤ) + b) := by
            push_cast [Nat.cast_sub h12.le]; ring
          rw [this]; exact dvd_sub hd2 hd1
        rcases hp_int_prime.dvd_or_dvd hsub with hda | hd_mul
        · exact hp_sp.2.2 hda
        · have hnat : p ∣ (k₂ - k₁) * QT := Int.natCast_dvd_natCast.mp (by exact_mod_cast hd_mul)
          rcases hp_sp.1.dvd_mul.mp hnat with hd_k | hd_Q
          · have : p ≤ k₂ - k₁ := Nat.le_of_dvd (by omega) hd_k
            omega
          · exact hp_ndvd_QT hd_Q
      have hex_k : ∃ k ≤ 2,
          ¬ ((p : ℤ) ∣ ((x' + k * QT : ℕ) : ℤ)) ∧
          ¬ ((p : ℤ) ∣ a * ((x' + k * QT : ℕ) : ℤ) + b) := by
        by_cases h0x : (p : ℤ) ∣ ((x' + 0 * QT : ℕ) : ℤ)
        · have h1x := h_inj_x 0 1 (by omega) (by omega) h0x
          have h2x := h_inj_x 0 2 (by omega) (by omega) h0x
          by_cases h1a : (p : ℤ) ∣ a * ((x' + 1 * QT : ℕ) : ℤ) + b
          · exact ⟨2, by omega, h2x, h_inj_ax 1 2 (by omega) (by omega) h1a⟩
          · exact ⟨1, by omega, h1x, h1a⟩
        · by_cases h0a : (p : ℤ) ∣ a * ((x' + 0 * QT : ℕ) : ℤ) + b
          · have h1a := h_inj_ax 0 1 (by omega) (by omega) h0a
            have h2a := h_inj_ax 0 2 (by omega) (by omega) h0a
            by_cases h1x : (p : ℤ) ∣ ((x' + 1 * QT : ℕ) : ℤ)
            · exact ⟨2, by omega, h_inj_x 1 2 (by omega) (by omega) h1x, h2a⟩
            · exact ⟨1, by omega, h1x, h1a⟩
          · exact ⟨0, by omega, h0x, h0a⟩
      obtain ⟨k, hk2, hkx, hka⟩ := hex_k
      refine ⟨x' + k * QT, ?_, ?_, ?_⟩
      · have hx'_Q : x' < QT := hx'_lt
        calc x' + k * QT < QT + 2 * QT := by nlinarith
          _ = 3 * QT := by ring
          _ ≤ p * QT := Nat.mul_le_mul_right QT hp_sp.2.1
          _ = 2 * ∏ q ∈ insert p T, q := by rw [Finset.prod_insert hpT]; dsimp only [QT]; ring
      · intro h2dvd
        have h2QT : 2 ∣ k * QT := dvd_mul_of_dvd_right (dvd_mul_right 2 _) k
        exact hx'_odd ((Nat.dvd_add_left h2QT).mp h2dvd)
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqT
        · exact ⟨hkx, hka⟩
        · have hq_dvd_QT : q ∣ QT := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hqT) 2
          have hqZ_dvd : (q : ℤ) ∣ (k * QT : ℕ) := Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hq_dvd_QT k)
          have hxg := hx'_good q hqT
          refine ⟨fun hd => hxg.1 ?_, fun hd => hxg.2 ?_⟩
          · have : ((x' : ℕ) : ℤ) = ((x' + k * QT : ℕ) : ℤ) - ((k * QT : ℕ) : ℤ) := by push_cast; ring
            rw [this]; exact dvd_sub hd hqZ_dvd
          · have : a * (x' : ℤ) + b = (a * ((x' + k * QT : ℕ) : ℤ) + b) - a * ((k * QT : ℕ) : ℤ) := by
              push_cast; ring
            rw [this]; exact dvd_sub hd (dvd_mul_of_dvd_right hqZ_dvd a)
  obtain ⟨x0, hx0_lt, hx0_odd, hx0_good⟩ := hgen ((Finset.Icc 3 y0).filter Nat.Prime)
    (fun p hp => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      exact ⟨hp.2, hp.1.1, ha p hp.2 hp.1.1 hp.1.2⟩)
  exact ⟨x0, hx0_lt, hx0_odd, fun p hp hp3 hpy =>
    hx0_good p (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hpy⟩, hp⟩)⟩

private lemma card_bad_period (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)]
    (hper : ∀ p y, bad p y ↔ bad p (y % p)) :
    ∀ (d : List ℕ) (A : ℕ), d.Nodup → (∀ p ∈ d, p.Prime) →
      ((Finset.Ico A (A + d.prod)).filter (fun y => ∀ p ∈ d, bad p y)).card =
        (d.map fun p => ((Finset.range p).filter (fun r => bad p r)).card).prod := by
  intro d A hd_nd hd_pr
  have hQ_pos : 0 < d.prod := List.prod_pos fun p hp => (hd_pr p hp).pos
  have h_ico_range : ((Finset.Ico A (A + d.prod)).filter (fun y => ∀ p ∈ d, bad p y)).card =
      ((Finset.range d.prod).filter (fun r => ∀ p ∈ d, bad p r)).card := by
    apply Finset.card_bij (fun y _ => y % d.prod)
    · intro y hy
      rw [Finset.mem_filter, Finset.mem_Ico] at hy
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt y hQ_pos, fun p hp => ?_⟩
      have hpd : p ∣ d.prod := List.dvd_prod hp
      rw [hper p (y % d.prod), Nat.mod_mod_of_dvd y hpd, ← hper p y]
      exact hy.2 p hp
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [Finset.mem_filter, Finset.mem_Ico] at hy₁ hy₂
      wlog hle : y₁ ≤ y₂ generalizing y₁ y₂
      · exact (this y₂ hy₂ y₁ hy₁ heq.symm (le_of_not_ge hle)).symm
      have hdvd : d.prod ∣ y₂ - y₁ := by
        have h1 : y₁ % d.prod = y₂ % d.prod := heq
        have h2 := Nat.div_add_mod y₂ d.prod
        have h3 := Nat.div_add_mod y₁ d.prod
        have hdiv : d.prod * (y₁ / d.prod) ≤ d.prod * (y₂ / d.prod) :=
          Nat.mul_le_mul_left d.prod (Nat.div_le_div_right hle)
        refine ⟨y₂ / d.prod - y₁ / d.prod, ?_⟩
        rw [Nat.mul_sub_left_distrib]
        omega
      by_contra hne
      have hpos_diff : 0 < y₂ - y₁ := by omega
      have hle_Q := Nat.le_of_dvd hpos_diff hdvd
      omega
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      let k := (A + d.prod - 1 - r) / d.prod
      have hrQ : r < d.prod := hr.1
      let y := r + ((A + d.prod - 1 - r) / d.prod) * d.prod
      have hy_ge : A ≤ y := by
        have hmod : (A + d.prod - 1 - r) / d.prod * d.prod + (A + d.prod - 1 - r) % d.prod = A + d.prod - 1 - r :=
          Nat.div_add_mod' _ _
        have hlt : (A + d.prod - 1 - r) % d.prod < d.prod := Nat.mod_lt _ hQ_pos
        dsimp only [y]; omega
      have hy_lt : y < A + d.prod := by
        have hle : (A + d.prod - 1 - r) / d.prod * d.prod ≤ A + d.prod - 1 - r := Nat.div_mul_le_self _ _
        dsimp only [y]; omega
      refine ⟨y, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨hy_ge, hy_lt⟩, fun p hp => ?_⟩
        have hpd : p ∣ d.prod := List.dvd_prod hp
        have hym : y % d.prod = r := by
          dsimp only [y]
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrQ]
        rw [hper p y, ← Nat.mod_mod_of_dvd y hpd, hym, ← hper p r]
        exact hr.2 p hp
      · dsimp only [y]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrQ]
  rw [h_ico_range]
  clear h_ico_range hQ_pos
  induction d with
  | nil => simp
  | cons p rest ih =>
    have hp_nd := List.nodup_cons.mp hd_nd
    have hp_pr := hd_pr p List.mem_cons_self
    have hrest_pr : ∀ q ∈ rest, q.Prime := fun q hq => hd_pr q (List.mem_cons_of_mem _ hq)
    have hrest_pos : 0 < rest.prod := List.prod_pos fun q hq => (hrest_pr q hq).pos
    have hcop : Nat.Coprime p rest.prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro q hq
      exact (Nat.coprime_primes hp_pr (hrest_pr q hq)).mpr (fun h => hp_nd.1 (h ▸ hq))
    have hprod_eq : ((Finset.range (p :: rest).prod).filter (fun r => ∀ q ∈ p :: rest, bad q r)).card =
        ((Finset.range p).filter (fun r => bad p r)).card *
        ((Finset.range rest.prod).filter (fun r => ∀ q ∈ rest, bad q r)).card := by
      rw [← Finset.card_product]
      apply Finset.card_bij (fun r _ => (r % p, r % rest.prod))
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
        refine ⟨⟨Nat.mod_lt r hp_pr.pos, ?_⟩, ⟨Nat.mod_lt r hrest_pos, fun q hq => ?_⟩⟩
        · rw [← hper p r]; exact hr.2 p List.mem_cons_self
        · rw [hper q (r % rest.prod), Nat.mod_mod_of_dvd r (List.dvd_prod hq), ← hper q r]
          exact hr.2 q (List.mem_cons_of_mem _ hq)
      · intro r₁ hr₁ r₂ hr₂ heq
        rw [Finset.mem_filter, Finset.mem_range, List.prod_cons] at hr₁ hr₂
        wlog hle : r₁ ≤ r₂ generalizing r₁ r₂
        · exact (this r₂ hr₂ r₁ hr₁ heq.symm (le_of_not_ge hle)).symm
        have hp_eq : r₁ % p = r₂ % p := congrArg Prod.fst heq
        have hR_eq : r₁ % rest.prod = r₂ % rest.prod := congrArg Prod.snd heq
        have hd_p : p ∣ r₂ - r₁ := by
          have hdiv : p * (r₁ / p) ≤ p * (r₂ / p) := Nat.mul_le_mul_left p (Nat.div_le_div_right hle)
          have := Nat.div_add_mod r₁ p
          have := Nat.div_add_mod r₂ p
          refine ⟨r₂ / p - r₁ / p, ?_⟩
          rw [Nat.mul_sub_left_distrib]; omega
        have hd_R : rest.prod ∣ r₂ - r₁ := by
          have hdiv : rest.prod * (r₁ / rest.prod) ≤ rest.prod * (r₂ / rest.prod) :=
            Nat.mul_le_mul_left rest.prod (Nat.div_le_div_right hle)
          have := Nat.div_add_mod r₁ rest.prod
          have := Nat.div_add_mod r₂ rest.prod
          refine ⟨r₂ / rest.prod - r₁ / rest.prod, ?_⟩
          rw [Nat.mul_sub_left_distrib]; omega
        have hd_both := hcop.mul_dvd_of_dvd_of_dvd hd_p hd_R
        by_contra hne
        have hpos_d : 0 < r₂ - r₁ := by omega
        have := Nat.le_of_dvd hpos_d hd_both
        omega
      · intro ⟨r₁, r₂⟩ hpair
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range] at hpair
        obtain ⟨k, hkp, hkR⟩ := Nat.chineseRemainder hcop r₁ r₂
        -- Wait: we only need surjectivity onto Finset.range (p * rest.prod)!
        refine ⟨k % (p * rest.prod), ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_range, List.prod_cons]
          refine ⟨Nat.mod_lt k (mul_pos hp_pr.pos hrest_pos), fun q hq => ?_⟩
          rcases List.mem_cons.mp hq with hqp | hq_rest
          · rw [hqp, hper p (k % (p * rest.prod)), Nat.mod_mod_of_dvd k (dvd_mul_right p rest.prod)]
            have hkm : k % p = r₁ := by
              have : k ≡ r₁ [MOD p] := hkp
              simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.1.1] using this
            rw [hkm]; exact hpair.1.2
          · rw [hper q (k % (p * rest.prod)),
                Nat.mod_mod_of_dvd k (dvd_mul_of_dvd_right (List.dvd_prod hq_rest) p)]
            have hkm : k % rest.prod = r₂ := by
              have : k ≡ r₂ [MOD rest.prod] := hkR
              simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.2.1] using this
            rw [← Nat.mod_mod_of_dvd k (List.dvd_prod hq_rest), hkm, ← hper q r₂]
            exact hpair.2.2 q hq_rest
        · ext
          · rw [Nat.mod_mod_of_dvd k (dvd_mul_right p rest.prod)]
            have : k ≡ r₁ [MOD p] := hkp
            simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.1.1] using this
          · rw [Nat.mod_mod_of_dvd k (dvd_mul_left rest.prod p)]
            have : k ≡ r₂ [MOD rest.prod] := hkR
            simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.2.1] using this
    rw [hprod_eq, List.map_cons, List.prod_cons, ih hp_nd.2 hrest_pr]

private lemma card_bad_Ico_error (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)]
    (hper : ∀ p y, bad p y ↔ bad p (y % p))
    (w : ℕ → ℝ) (e : List ℕ) (he_nd : e.Nodup) (he_pr : ∀ p ∈ e, p.Prime)
    (hle2 : ∀ p ∈ e, ((Finset.range p).filter (fun r => bad p r)).card ≤ 2)
    (hw : ∀ p ∈ e, w p = (((Finset.range p).filter (fun r => bad p r)).card : ℝ) / p)
    (Y0 M : ℕ) :
    |(M : ℝ) * (e.map w).prod -
      (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card : ℝ)| ≤ (2 : ℝ) ^ e.length := by
  let Q := e.prod
  have hQ_pos : 0 < Q := List.prod_pos fun p hp => (he_pr p hp).pos
  let q := M / Q
  let r := M % Q
  have hM_eq : M = q * Q + r := (Nat.div_add_mod' M Q).symm
  have hr_lt : r < Q := Nat.mod_lt M hQ_pos
  let N_full := (e.map fun p => ((Finset.range p).filter (fun x => bad p x)).card).prod
  have hw_eq : (e.map w).prod = (N_full : ℝ) / (Q : ℝ) := by
    clear hM_eq hr_lt hQ_pos
    induction e with
    | nil => simp [N_full, Q]
    | cons p t ih =>
      simp only [List.map_cons, List.prod_cons, N_full, Q] at *
      rw [ih (List.nodup_cons.mp he_nd).2 (fun q hq => he_pr q (List.mem_cons_of_mem _ hq))
          (fun q hq => hle2 q (List.mem_cons_of_mem _ hq)) (fun q hq => hw q (List.mem_cons_of_mem _ hq))]
      rw [hw p List.mem_cons_self]
      push_cast; ring
  have hN_le : N_full ≤ 2 ^ e.length := by
    clear hw_eq hM_eq hr_lt hQ_pos
    induction e with
    | nil => simp [N_full]
    | cons p t ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ', N_full] at *
      exact Nat.mul_le_mul (hle2 p List.mem_cons_self)
        (ih (List.nodup_cons.mp he_nd).2 (fun q hq => he_pr q (List.mem_cons_of_mem _ hq))
          (fun q hq => hle2 q (List.mem_cons_of_mem _ hq)) (fun q hq => hw q (List.mem_cons_of_mem _ hq)))
  have hblock : ∀ A : ℕ, ((Finset.Ico A (A + Q)).filter (fun y => ∀ p ∈ e, bad p y)).card = N_full :=
    fun A => card_bad_period bad hper e A he_nd he_pr
  have hblocks : ∀ m : ℕ,
      ((Finset.Ico Y0 (Y0 + m * Q)).filter (fun y => ∀ p ∈ e, bad p y)).card = m * N_full := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hmQ : (m + 1) * Q = m * Q + Q := Nat.succ_mul m Q
      have hsplit : Finset.Ico Y0 (Y0 + (m + 1) * Q) =
          Finset.Ico Y0 (Y0 + m * Q) ∪ Finset.Ico (Y0 + m * Q) (Y0 + m * Q + Q) := by
        rw [hmQ]; ext x; simp only [Finset.mem_union, Finset.mem_Ico]; constructor <;> intro h <;> omega
      have hdisj : Disjoint (Finset.Ico Y0 (Y0 + m * Q)) (Finset.Ico (Y0 + m * Q) (Y0 + m * Q + Q)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Ico] at hx1 hx2; omega
      rw [hsplit, Finset.filter_union,
          Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
          ih, hblock (Y0 + m * Q), Nat.add_mul, one_mul]
  have hlow : q * N_full ≤ ((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card := by
    rw [← hblocks q]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro y hy; simp only [Finset.mem_Ico] at hy ⊢; omega
  have hup : ((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card ≤ (q + 1) * N_full := by
    have hqQ : (q + 1) * Q = q * Q + Q := Nat.succ_mul q Q
    rw [← hblocks (q + 1)]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro y hy; simp only [Finset.mem_Ico] at hy ⊢; rw [hqQ]; omega
  have hMW : (M : ℝ) * (e.map w).prod = (q : ℝ) * N_full + (r : ℝ) / Q * N_full := by
    rw [hw_eq, hM_eq]; push_cast; field_simp
  have hrQ0 : 0 ≤ (r : ℝ) / Q := by positivity
  have hrQ1 : (r : ℝ) / Q ≤ 1 := (div_le_one (by exact_mod_cast hQ_pos)).mpr (by exact_mod_cast hr_lt.le)
  have hN_nn : (0 : ℝ) ≤ N_full := Nat.cast_nonneg _
  have hMW_lo : (q : ℝ) * N_full ≤ (M : ℝ) * (e.map w).prod := by nlinarith
  have hMW_hi : (M : ℝ) * (e.map w).prod ≤ (q : ℝ) * N_full + N_full := by nlinarith
  have hcard_lo : (q : ℝ) * N_full ≤ (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card : ℝ) := by
    exact_mod_cast hlow
  have hcard_hi : (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card : ℝ) ≤
      (q : ℝ) * N_full + N_full := by
    have : ((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card ≤ q * N_full + N_full := by
      linarith [hup]
    exact_mod_cast this
  have hN_R : (N_full : ℝ) ≤ (2 : ℝ) ^ e.length := by exact_mod_cast hN_le
  rw [abs_le]
  constructor <;> linarith

private lemma sum_ind_error (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)]
    (hper : ∀ p y, bad p y ↔ bad p (y % p))
    (ps : List ℕ) (w : ℕ → ℝ)
    (hle2 : ∀ p ∈ ps, ((Finset.range p).filter (fun r => bad p r)).card ≤ 2)
    (hw : ∀ p ∈ ps, w p = (((Finset.range p).filter (fun r => bad p r)).card : ℝ) / p)
    (hpw : ps.Pairwise (· > ·)) (hps : ∀ p ∈ ps, p.Prime)
    {D : ℝ} (hD : 1 ≤ D) (Y0 M : ℕ) :
    (M : ℝ) * W_minus w ps D - ∑ y ∈ Finset.Ico Y0 (Y0 + M), indMinus bad ps D y ≤
      D * (Real.log D + 1) := by
  have hinv := divs_invariant ps [] D hpw List.Pairwise.nil (by simp)
    (fun p hp => (hps p hp).two_le) hD (by simp)
  have hnodup := hinv.2.2.1
  have hW_eq := (W_eq_divs w ps [] D).1
  simp only [List.length_nil, pow_zero, List.map_nil, List.prod_nil, mul_one, one_mul] at hW_eq
  have hind_eq : ∀ y, indMinus bad ps D y =
      ((divsMinus [] ps D).map fun e =>
        (-1 : ℝ) ^ e.length * (if ∀ q ∈ e, bad q y then (1 : ℝ) else 0)).sum := by
    intro y
    have h := (ind_eq_divs bad ps [] D y).1
    simpa using h
  rw [hW_eq, ← List.sum_toFinset _ hnodup]
  have hsum_ind : ∑ y ∈ Finset.Ico Y0 (Y0 + M), indMinus bad ps D y =
      ∑ e ∈ (divsMinus [] ps D).toFinset,
        (-1 : ℝ) ^ e.length * (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ q ∈ e, bad q y)).card : ℝ) := by
    have h1 : ∑ y ∈ Finset.Ico Y0 (Y0 + M), indMinus bad ps D y =
        ∑ y ∈ Finset.Ico Y0 (Y0 + M), ∑ e ∈ (divsMinus [] ps D).toFinset,
          (-1 : ℝ) ^ e.length * (if ∀ q ∈ e, bad q y then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hind_eq y, ← List.sum_toFinset _ hnodup]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum, Finset.sum_boole]
  rw [hsum_ind, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hle_sum : ∑ e ∈ (divsMinus [] ps D).toFinset,
      ((M : ℝ) * ((-1 : ℝ) ^ e.length * (e.map w).prod) -
        (-1 : ℝ) ^ e.length * (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ q ∈ e, bad q y)).card : ℝ)) ≤
      ∑ e ∈ (divsMinus [] ps D).toFinset, (2 : ℝ) ^ e.length := by
    refine Finset.sum_le_sum fun e he => ?_
    have he_mem := List.mem_toFinset.mp he
    have he_inv := hinv.1 e he_mem
    have he_nd : e.Nodup := he_inv.1.imp fun {a b} (h : a < b) => h.ne
    have he_in : ∀ q ∈ e, q ∈ ps := fun q hq => by
      rcases he_inv.2.1 q hq with hqp | hqd; exact hqp; simp at hqd
    have he_pr : ∀ q ∈ e, q.Prime := fun q hq => hps q (he_in q hq)
    have herr := card_bad_Ico_error bad hper w e he_nd he_pr
      (fun q hq => hle2 q (he_in q hq)) (fun q hq => hw q (he_in q hq)) Y0 M
    have h_eq : (M : ℝ) * ((-1 : ℝ) ^ e.length * (e.map w).prod) -
        (-1 : ℝ) ^ e.length * (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ q ∈ e, bad q y)).card : ℝ) =
        (-1 : ℝ) ^ e.length * ((M : ℝ) * (e.map w).prod -
          (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ q ∈ e, bad q y)).card : ℝ)) := by ring
    rw [h_eq]
    have hpow1 : |(-1 : ℝ) ^ e.length| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    have hle_abs : (-1 : ℝ) ^ e.length * ((M : ℝ) * (e.map w).prod -
        (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ q ∈ e, bad q y)).card : ℝ)) ≤
        |(M : ℝ) * (e.map w).prod -
          (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ q ∈ e, bad q y)).card : ℝ)| := by
      calc _ ≤ |(-1 : ℝ) ^ e.length * _| := le_abs_self _
        _ = |(-1 : ℝ) ^ e.length| * |_| := abs_mul _ _
        _ = _ := by rw [hpow1, one_mul]
    exact hle_abs.trans herr
  have hdivs := divs_sum_le ps hpw hps hD
  rw [← List.sum_toFinset _ hnodup] at hdivs
  exact hle_sum.trans hdivs

private lemma pairwise_lt_of_le_nodup : ∀ {l : List ℕ},
    l.Pairwise (· ≤ ·) → l.Nodup → l.Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | a :: t, hp, hn => by
    rw [List.pairwise_cons] at hp ⊢
    rw [List.nodup_cons] at hn
    refine ⟨fun b hb => lt_of_le_of_ne (hp.1 b hb) (fun h => hn.1 (h ▸ hb)),
      pairwise_lt_of_le_nodup hp.2 hn.2⟩

private lemma pairwise_gt_reverse_of_lt : ∀ {l : List ℕ},
    l.Pairwise (· < ·) → l.reverse.Pairwise (· > ·) := by
  intro l h
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    rw [List.reverse_cons, List.pairwise_append]
    refine ⟨ih h.2, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
    simp only [List.mem_singleton] at hy
    subst hy
    exact h.1 x (List.mem_reverse.mp hx)

private lemma rpow_log_z_lower (z : ℝ) (hz : 3 ≤ z) :
    (Real.log z) ^ 3 ≤ 8 * 10 ^ 6 * z ^ (2 / 100 : ℝ) := by
  have hz_pos : 0 < z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hlog_nn : 0 ≤ Real.log z := Real.log_nonneg hz1
  have hlog_le : Real.log z ≤ 200 * z ^ (1 / 200 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hz_pos (1 / 200 : ℝ))
    have h2 : Real.log (z ^ (1 / 200 : ℝ)) = (1 / 200 : ℝ) * Real.log z := Real.log_rpow hz_pos _
    linarith
  have hpow3 : (Real.log z) ^ 3 ≤ (200 * z ^ (1 / 200 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hlog_nn hlog_le 3
  have hpow_eq : (z ^ (1 / 200 : ℝ)) ^ 3 = z ^ (3 / 200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz_pos.le]; norm_num
  have hpow_le : z ^ (3 / 200 : ℝ) ≤ z ^ (2 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  calc (Real.log z) ^ 3 ≤ (200 * z ^ (1 / 200 : ℝ)) ^ 3 := hpow3
    _ = 8 * 10 ^ 6 * (z ^ (1 / 200 : ℝ)) ^ 3 := by ring
    _ = 8 * 10 ^ 6 * z ^ (3 / 200 : ℝ) := by rw [hpow_eq]
    _ ≤ 8 * 10 ^ 6 * z ^ (2 / 100 : ℝ) := by gcongr

private lemma h4_with_y0 (y0 : ℕ) (hy0_le : 2 ^ 200000 ≤ y0) :
    OMA.R_Erdos724_erdos_724_variants_wilson_R1.H4 := by
  let Q0 : ℕ := 2 * ∏ p ∈ (Finset.Icc 3 y0).filter Nat.Prime, p
  have hQ0_pos : 0 < Q0 := mul_pos (by norm_num) (Finset.prod_pos fun p hp =>
    (Finset.mem_filter.mp hp).2.pos)
  let C : ℝ := (y0 : ℝ) + 2 * (Q0 : ℝ) * 10 ^ 9
  have hy0_4 : 4 ≤ y0 := by
    have h2 : 2 ^ 2 ≤ 2 ^ 200000 := Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.le_of_lt (by decide : 2 < 200000))
    exact le_trans (by norm_num) (le_trans h2 hy0_le)
  have hC3 : 3 ≤ C := by
    have : (4 : ℝ) ≤ y0 := by exact_mod_cast hy0_4
    have : (0 : ℝ) ≤ 2 * (Q0 : ℝ) * 10 ^ 9 := by positivity
    linarith
  refine ⟨C, hC3, ?_⟩
  intro z X L a b hzC hLC ha
  have hz_ge_y0 : (y0 : ℝ) ≤ z := by
    have : (0 : ℝ) ≤ 2 * (Q0 : ℝ) * 10 ^ 9 := by positivity
    linarith
  have hz3 : 3 ≤ z := hC3.trans hzC
  have hz_pos : 0 < z := by linarith
  have hlogy0_ge : 100000 ≤ Real.log (y0 : ℝ) := by
    have h2 : Real.log ((2 ^ 200000 : ℕ) : ℝ) ≤ Real.log (y0 : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hy0_le)
    rw [Nat.cast_pow, Real.log_pow] at h2
    norm_num at h2
    have h3 := log_two_ge_half
    linarith
  have hlogz_ge : 100000 ≤ Real.log z :=
    hlogy0_ge.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < y0)) hz_ge_y0)
  have hlogz_pos : 0 < Real.log z := by linarith
  have ha_y0 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ y0 → ¬ ((p : ℤ) ∣ a) := by
    intro p hp hp3 hpy
    exact ha p hp hp3 ((by exact_mod_cast hpy : (p : ℝ) ≤ y0).trans hz_ge_y0)
  obtain ⟨x0, hx0_lt, hx0_odd, hx0_good⟩ := crt_const_exists y0 a b ha_y0
  let M : ℕ := L / Q0 - 1
  let Y0 : ℕ := X / Q0 + 1
  have hL_ge : 2 * (Q0 : ℝ) * 10 ^ 9 * z ^ 5 ≤ (L : ℝ) := by
    have h1 : 2 * (Q0 : ℝ) * 10 ^ 9 ≤ C := by dsimp only [C]; linarith [show (0 : ℝ) ≤ y0 by positivity]
    calc 2 * (Q0 : ℝ) * 10 ^ 9 * z ^ 5 ≤ C * z ^ 5 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (L : ℝ) := hLC
  have hQ0_R_pos : (0 : ℝ) < Q0 := by exact_mod_cast hQ0_pos
  have hM_ge : (10 : ℝ) ^ 9 * z ^ 5 ≤ (M : ℝ) := by
    have hL_div : 2 * 10 ^ 9 * z ^ 5 ≤ (L : ℝ) / Q0 := by
      rw [le_div_iff₀ hQ0_R_pos]; linarith
    have hmod_le : (L : ℝ) / Q0 - 1 < ((L / Q0 : ℕ) : ℝ) := by
      have hmod : (L / Q0 : ℕ) * Q0 + L % Q0 = L := Nat.div_add_mod' L Q0
      have hmod_lt : ((L % Q0 : ℕ) : ℝ) < Q0 := by exact_mod_cast Nat.mod_lt L hQ0_pos
      have hmodR : ((L / Q0 : ℕ) : ℝ) * Q0 + ((L % Q0 : ℕ) : ℝ) = L := by exact_mod_cast hmod
      have heq : (L : ℝ) / Q0 = ((L / Q0 : ℕ) : ℝ) + ((L % Q0 : ℕ) : ℝ) / Q0 := by field_simp; linarith
      have hlt1 : ((L % Q0 : ℕ) : ℝ) / Q0 < 1 := (div_lt_one hQ0_R_pos).mpr hmod_lt
      linarith
    have hLQ_ge : 2 ≤ L / Q0 := by
      have hz5 : (1 : ℝ) ≤ z ^ 5 := one_le_pow₀ (by linarith)
      have hR : (2 : ℝ) < ((L / Q0 : ℕ) : ℝ) := by linarith
      have : (2 : ℕ) < L / Q0 := by exact_mod_cast hR
      omega
    have hMR : (M : ℝ) = ((L / Q0 : ℕ) : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ L / Q0)
    have hz5 : (2 : ℝ) ≤ 10 ^ 9 * z ^ 5 := by
      have : (1 : ℝ) ≤ z ^ 5 := one_le_pow₀ (by linarith); linarith
    linarith
  have hQM_le_L : Q0 * (M + 1) ≤ L := by
    have h1 : 1 ≤ L / Q0 := by
      have hR : (1 : ℝ) ≤ (M : ℝ) := by
        have : (1 : ℝ) ≤ 10 ^ 9 * z ^ 5 := by
          have : (1 : ℝ) ≤ z ^ 5 := one_le_pow₀ (by linarith); linarith
        linarith
      have : 1 ≤ M := by exact_mod_cast hR
      omega
    have heq : M + 1 = L / Q0 := by omega
    rw [heq, mul_comm]
    exact Nat.div_mul_le_self L Q0
  let bad : ℕ → ℕ → Prop := fun p y =>
    (p : ℤ) ∣ ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) ∨
      (p : ℤ) ∣ a * ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) + b
  have hper : ∀ p y, bad p y ↔ bad p (y % p) := by
    intro p y
    have hym : (p : ℤ) ∣ ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by
      refine ⟨((y / p : ℕ) : ℤ), ?_⟩
      have hdivZ : (p : ℤ) * ((y / p : ℕ) : ℤ) + ((y % p : ℕ) : ℤ) = (y : ℤ) := by
        exact_mod_cast Nat.div_add_mod y p
      linarith
    dsimp only [bad]
    constructor <;> rintro (h | h)
    · left
      have : (x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ) =
          ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) - (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_sub h (dvd_mul_of_dvd_right hym _)
    · right
      have : a * ((x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ)) + b =
          (a * ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) + b) - a * (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_sub h (dvd_mul_of_dvd_right hym _)
    · left
      have : (x0 : ℤ) + (Q0 : ℤ) * (y : ℤ) =
          ((x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ)) + (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_add h (dvd_mul_of_dvd_right hym _)
    · right
      have : a * ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) + b =
          (a * ((x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ)) + b) + a * (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_add h (dvd_mul_of_dvd_right hym _)
  let S_ps := (Finset.Icc (y0 + 1) ⌊z⌋₊).filter Nat.Prime
  let ps : List ℕ := (S_ps.sort (· ≤ ·)).reverse
  have hpw : ps.Pairwise (· > ·) :=
    pairwise_gt_reverse_of_lt (pairwise_lt_of_le_nodup (Finset.pairwise_sort S_ps (· ≤ ·))
      (Finset.sort_nodup S_ps (· ≤ ·)))
  have hps_spec : ∀ p ∈ ps, p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z := by
    intro p hp
    have hmem : p ∈ S_ps := by
      rw [← Finset.mem_sort (r := (· ≤ ·))]
      exact List.mem_reverse.mp hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hmem
    exact ⟨hmem.2, by omega, (Nat.le_floor_iff hz_pos.le).mp hmem.1.2⟩
  have hps_pr : ∀ p ∈ ps, p.Prime := fun p hp => (hps_spec p hp).1
  have hps_ndvd : ∀ p : ℕ, p.Prime → y0 < p → (p : ℝ) ≤ z → ¬ (p ∣ Q0) ∧ ¬ ((p : ℤ) ∣ a) := by
    intro p hp hpy hpz
    refine ⟨?_, ha p hp (by omega) hpz⟩
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with hd2 | hd_prod
    · have := ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left hp.ne_one
      omega
    · obtain ⟨q, hq, hqp⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd_prod
      rw [Finset.mem_filter, Finset.mem_Icc] at hq
      have := ((Nat.dvd_prime hq.2).mp hqp).resolve_left hp.ne_one
      omega
  let w : ℕ → ℝ := fun p =>
    if p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z then
      (((Finset.range p).filter (fun r => bad p r)).card : ℝ) / p
    else 0
  have hbad_le2 : ∀ p : ℕ, p.Prime → y0 < p → (p : ℝ) ≤ z →
      ((Finset.range p).filter (fun r => bad p r)).card ≤ 2 := by
    intro p hp hpy hpz
    obtain ⟨hpQ0, hpa⟩ := hps_ndvd p hp hpy hpz
    have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hsub : (Finset.range p).filter (fun (r : ℕ) => bad p r) ⊆
        (Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ))) ∪
        (Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ a * ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ)) + b) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hr.2 with h1 | h2
      · exact Or.inl ⟨hr.1, h1⟩
      · exact Or.inr ⟨hr.1, h2⟩
    have hc1 : ((Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ)))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro r₁ hr₁ r₂ hr₂
      rw [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
      wlog hle : r₁ ≤ r₂ generalizing r₁ r₂
      · exact (this r₂ hr₂ r₁ hr₁ (le_of_not_ge hle)).symm
      have hsub_dvd : (p : ℤ) ∣ (Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ) := by
        have : (Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ) =
            ((x0 : ℤ) + (Q0 : ℤ) * (r₂ : ℤ)) - ((x0 : ℤ) + (Q0 : ℤ) * (r₁ : ℤ)) := by
          rw [Nat.cast_sub hle]; ring
        rw [this]; exact dvd_sub hr₂.2 hr₁.2
      have hnat : p ∣ Q0 * (r₂ - r₁) := Int.natCast_dvd_natCast.mp (by exact_mod_cast hsub_dvd)
      rcases hp.dvd_mul.mp hnat with hq | hr
      · exact absurd hq hpQ0
      · by_contra hne
        have := Nat.le_of_dvd (by omega) hr
        omega
    have hc2 : ((Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ a * ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ)) + b)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro r₁ hr₁ r₂ hr₂
      rw [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
      wlog hle : r₁ ≤ r₂ generalizing r₁ r₂
      · exact (this r₂ hr₂ r₁ hr₁ (le_of_not_ge hle)).symm
      have hsub_dvd : (p : ℤ) ∣ a * ((Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ)) := by
        have : a * ((Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ)) =
            (a * ((x0 : ℤ) + (Q0 : ℤ) * (r₂ : ℤ)) + b) - (a * ((x0 : ℤ) + (Q0 : ℤ) * (r₁ : ℤ)) + b) := by
          rw [Nat.cast_sub hle]; ring
        rw [this]; exact dvd_sub hr₂.2 hr₁.2
      rcases hp_int.dvd_or_dvd hsub_dvd with ha_dvd | hmul
      · exact absurd ha_dvd hpa
      · have hnat : p ∣ Q0 * (r₂ - r₁) := Int.natCast_dvd_natCast.mp (by exact_mod_cast hmul)
        rcases hp.dvd_mul.mp hnat with hq | hr
        · exact absurd hq hpQ0
        · by_contra hne
          have := Nat.le_of_dvd (by omega) hr
          omega
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  have hw0 : ∀ p, 0 ≤ w p := fun p => by
    dsimp only [w]
    split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_rfl
  have hw2 : ∀ p, w p ≤ 2 / (p : ℝ) := fun p => by
    dsimp only [w]
    split_ifs with h
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hbad_le2 p h.1 h.2.1 h.2.2) (Nat.cast_nonneg _)
    · exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  let D : ℝ := z ^ (498 / 100 : ℝ)
  have hD_ge : 1 ≤ D := Real.one_le_rpow (by linarith) (by norm_num)
  have hs_eq : Real.log D / Real.log z = 498 / 100 := by
    dsimp only [D]
    rw [Real.log_rpow hz_pos, mul_div_cancel_right₀ _ hlogz_pos.ne']
  have hs37 : 37 / 10 ≤ Real.log D / Real.log z := by rw [hs_eq]; norm_num
  have hmain_sieve := (sieve_main_bound hy0_le w hw0 hw2 ps.length ps le_rfl hpw
    (fun p hp => ⟨(hps_spec p hp).1, (hps_spec p hp).2.1⟩) z D hz_ge_y0
    (fun p hp => (hps_spec p hp).2.2) hD_ge hs37).1
  have hphiM_le : phiM (498 / 100) ≤ 92 / 100 := by
    unfold phiM
    rw [if_neg (by norm_num), if_pos (by norm_num),
      show ⌊50 * ((498 : ℝ) / 100 - 37 / 10)⌋₊ = 64 by norm_num]
    have h64 : (tabMList.getD 64 0 : ℝ) ≤ 920000 := by exact_mod_cast h_m64_le
    linarith
  have hW_lower : Vprod w ps * (8 / 100 : ℝ) ≤ W_minus w ps D := by
    have hV_nn : 0 ≤ Vprod w ps := (Vprod_pos w hw2 ps fun p hp => by
      have := (hps_spec p hp).2.1; omega).le
    rw [hs_eq] at hmain_sieve
    nlinarith [mul_le_mul_of_nonneg_left hphiM_le hV_nn]
  have hV_inv : (Vprod w ps)⁻¹ ≤ (10009 / 10000 : ℝ) * (Real.log z / Real.log (y0 : ℝ)) ^ 2 := by
    have hps_nd : ps.Nodup := hpw.imp fun {a b} (h : a > b) => h.ne'
    exact list_Vprod_inv_le hy0_le w hw0 hw2 le_rfl hz_ge_y0 ps hps_nd
      (fun p hp => let h := hps_spec p hp; ⟨h.1, by exact_mod_cast h.2.1, h.2.2⟩)
  have hV_lower : (10000 / 10009 : ℝ) * (Real.log (y0 : ℝ) / Real.log z) ^ 2 ≤ Vprod w ps := by
    have hV_pos : 0 < Vprod w ps := Vprod_pos w hw2 ps fun p hp => by
      have := (hps_spec p hp).2.1; omega
    have hlog_pos : 0 < Real.log (y0 : ℝ) := by linarith
    have hrat_pos : 0 < (10009 / 10000 : ℝ) * (Real.log z / Real.log (y0 : ℝ)) ^ 2 := by positivity
    calc (10000 / 10009 : ℝ) * (Real.log (y0 : ℝ) / Real.log z) ^ 2
        = ((10009 / 10000 : ℝ) * (Real.log z / Real.log (y0 : ℝ)) ^ 2)⁻¹ := by
          rw [mul_inv, ← inv_pow, inv_div]; norm_num
      _ ≤ (Vprod w ps)⁻¹⁻¹ := inv_anti₀ (inv_pos.mpr hV_pos) hV_inv
      _ = Vprod w ps := inv_inv _
  have hV_lower2 : (10000 / 10009 : ℝ) * (10 ^ 10 / (Real.log z) ^ 2) ≤ Vprod w ps := by
    have h1 : (100000 / Real.log z) ^ 2 ≤ (Real.log (y0 : ℝ) / Real.log z) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right hlogy0_ge hlogz_pos.le
    calc (10000 / 10009 : ℝ) * (10 ^ 10 / (Real.log z) ^ 2)
        = (10000 / 10009 : ℝ) * (100000 / Real.log z) ^ 2 := by ring
      _ ≤ (10000 / 10009 : ℝ) * (Real.log (y0 : ℝ) / Real.log z) ^ 2 := by gcongr
      _ ≤ Vprod w ps := hV_lower
  have herr_sum : (M : ℝ) * W_minus w ps D - ∑ y ∈ Finset.Ico Y0 (Y0 + M), indMinus bad ps D y ≤
      D * (Real.log D + 1) := by
    refine sum_ind_error bad hper ps w ?_ ?_ hpw hps_pr hD_ge Y0 M
    · intro p hp
      have hsp := hps_spec p hp
      exact hbad_le2 p hsp.1 hsp.2.1 hsp.2.2
    · intro p hp
      have hsp := hps_spec p hp
      dsimp only [w]
      rw [if_pos hsp]
  have h_pos_sum : 0 < ∑ y ∈ Finset.Ico Y0 (Y0 + M), (if ∀ p ∈ ps, ¬ bad p y then (1 : ℝ) else 0) := by
    have h1 : ∑ y ∈ Finset.Ico Y0 (Y0 + M), indMinus bad ps D y ≤
        ∑ y ∈ Finset.Ico Y0 (Y0 + M), (if ∀ p ∈ ps, ¬ bad p y then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun y _ => (ind_sound bad ps D y).1
    have hlogD_le : Real.log D + 1 ≤ 6 * Real.log z := by
      have h1' : Real.log D = (498 / 100 : ℝ) * Real.log z := by
        dsimp only [D]; exact Real.log_rpow hz_pos _
      have h2' : (1 : ℝ) ≤ Real.log z := by linarith [hlogz_ge]
      linarith
    have hD_err : D * (Real.log D + 1) ≤ z ^ (498 / 100 : ℝ) * (6 * Real.log z) := by
      exact mul_le_mul_of_nonneg_left hlogD_le (Real.rpow_nonneg hz_pos.le _)
    have hM_main : 7 * 10 ^ 17 * z ^ 5 / (Real.log z) ^ 2 ≤ (M : ℝ) * W_minus w ps D := by
      have hW_pos : (8 / 100 : ℝ) * ((10000 / 10009 : ℝ) * (10 ^ 10 / (Real.log z) ^ 2)) ≤ W_minus w ps D := by
        have : (10000 / 10009 : ℝ) * (10 ^ 10 / (Real.log z) ^ 2) * (8 / 100) ≤ Vprod w ps * (8 / 100) :=
          mul_le_mul_of_nonneg_right hV_lower2 (by norm_num)
        linarith
      have hconst : (7 : ℝ) * 10 ^ 17 ≤ (10 ^ 9) * ((8 / 100) * ((10000 / 10009) * 10 ^ 10)) := by norm_num
      calc 7 * 10 ^ 17 * z ^ 5 / (Real.log z) ^ 2
          = (7 * 10 ^ 17) * (z ^ 5 / (Real.log z) ^ 2) := by ring
        _ ≤ ((10 ^ 9) * ((8 / 100) * ((10000 / 10009) * 10 ^ 10))) * (z ^ 5 / (Real.log z) ^ 2) :=
            mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = ((10 : ℝ) ^ 9 * z ^ 5) * ((8 / 100 : ℝ) * ((10000 / 10009 : ℝ) * (10 ^ 10 / (Real.log z) ^ 2))) := by
            ring
        _ ≤ (M : ℝ) * W_minus w ps D :=
            mul_le_mul hM_ge hW_pos (by positivity) (Nat.cast_nonneg _)
    have hgap : z ^ (498 / 100 : ℝ) * (6 * Real.log z) < 7 * 10 ^ 17 * z ^ 5 / (Real.log z) ^ 2 := by
      have hrz := rpow_log_z_lower z hz3
      have hz5_eq : z ^ (498 / 100 : ℝ) * z ^ (2 / 100 : ℝ) = z ^ 5 := by
        calc z ^ (498 / 100 : ℝ) * z ^ (2 / 100 : ℝ)
            = z ^ ((498 / 100 : ℝ) + 2 / 100) := (Real.rpow_add hz_pos _ _).symm
          _ = z ^ ((5 : ℕ) : ℝ) := by norm_num
          _ = z ^ 5 := Real.rpow_natCast z 5
      have hlog3_pos : 0 < (Real.log z) ^ 2 := pow_pos hlogz_pos 2
      rw [lt_div_iff₀ hlog3_pos]
      have h1' : z ^ (498 / 100 : ℝ) * (6 * Real.log z) * (Real.log z) ^ 2 =
          6 * z ^ (498 / 100 : ℝ) * (Real.log z) ^ 3 := by ring
      have h2' : 6 * z ^ (498 / 100 : ℝ) * (Real.log z) ^ 3 ≤
          6 * z ^ (498 / 100 : ℝ) * (8 * 10 ^ 6 * z ^ (2 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrz (by positivity)
      have h3' : 6 * z ^ (498 / 100 : ℝ) * (8 * 10 ^ 6 * z ^ (2 / 100 : ℝ)) = 48 * 10 ^ 6 * z ^ 5 := by
        calc _ = 48 * 10 ^ 6 * (z ^ (498 / 100 : ℝ) * z ^ (2 / 100 : ℝ)) := by ring
          _ = 48 * 10 ^ 6 * z ^ 5 := by rw [hz5_eq]
      have h4' : (48 : ℝ) * 10 ^ 6 * z ^ 5 < 7 * 10 ^ 17 * z ^ 5 := by
        have hz5p : 0 < z ^ 5 := pow_pos hz_pos 5
        nlinarith
      linarith
    linarith
  have hex_y : ∃ y ∈ Finset.Ico Y0 (Y0 + M), ∀ p ∈ ps, ¬ bad p y := by
    by_contra hall
    push_neg at hall
    have h0 : ∑ y ∈ Finset.Ico Y0 (Y0 + M), (if ∀ p ∈ ps, ¬ bad p y then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      obtain ⟨p, hp, hbp⟩ := hall y hy
      rw [if_neg (by push_neg; exact ⟨p, hp, hbp⟩)]
    linarith
  obtain ⟨y, hy_mem, hy_good⟩ := hex_y
  rw [Finset.mem_Ico] at hy_mem
  let x := x0 + Q0 * y
  refine ⟨x, Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · have hmod : (X / Q0 : ℕ) * Q0 + X % Q0 = X := Nat.div_add_mod' X Q0
    have hmod_lt : X % Q0 < Q0 := Nat.mod_lt X hQ0_pos
    have hQy : Q0 * (X / Q0 + 1) ≤ Q0 * y := Nat.mul_le_mul_left Q0 hy_mem.1
    exact Nat.le_of_lt (calc X = (X / Q0 : ℕ) * Q0 + X % Q0 := hmod.symm
      _ < (X / Q0 : ℕ) * Q0 + Q0 := Nat.add_lt_add_left hmod_lt _
      _ = Q0 * (X / Q0 + 1) := by ring
      _ ≤ Q0 * y := hQy
      _ ≤ x0 + Q0 * y := Nat.le_add_left _ _)
  · have hmul : (X / Q0 : ℕ) * Q0 ≤ X := Nat.div_mul_le_self X Q0
    have hx0_Q : x0 < Q0 := hx0_lt
    have hy1 : y + 1 ≤ X / Q0 + (M + 1) := by
      have h1 : y + 1 ≤ Y0 + M := Nat.succ_le_of_lt hy_mem.2
      change y + 1 ≤ (X / Q0 + 1) + M at h1
      linarith
    have hQy1 : Q0 * (y + 1) ≤ Q0 * (X / Q0 + (M + 1)) := Nat.mul_le_mul_left Q0 hy1
    calc x0 + Q0 * y < Q0 + Q0 * y := Nat.add_lt_add_right hx0_Q _
      _ = Q0 * (y + 1) := by ring
      _ ≤ Q0 * (X / Q0 + (M + 1)) := hQy1
      _ = (X / Q0 : ℕ) * Q0 + Q0 * (M + 1) := by ring
      _ ≤ X + L := Nat.add_le_add hmul hQM_le_L
  · intro h2x
    have h2Q : 2 ∣ Q0 * y := dvd_mul_of_dvd_left (dvd_mul_right 2 _) y
    exact hx0_odd ((Nat.dvd_add_left h2Q).mp h2x)
  · intro p hp hp3 hpz
    by_cases hpy : p ≤ y0
    · obtain ⟨hx0_p, hx0_ap⟩ := hx0_good p hp hp3 hpy
      have hp_dvd_Q0 : p ∣ Q0 := by
        refine dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ ?_) 2
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp3, hpy⟩, hp⟩
      have hpZ : (p : ℤ) ∣ ((Q0 * y : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_left hp_dvd_Q0 y)
      refine ⟨fun hd => hx0_p ?_, fun hd => hx0_ap ?_⟩
      · have : (x0 : ℤ) = (x : ℤ) - ((Q0 * y : ℕ) : ℤ) := by dsimp only [x]; push_cast; ring
        rw [this]; exact dvd_sub hd hpZ
      · have : a * (x0 : ℤ) + b = (a * (x : ℤ) + b) - a * ((Q0 * y : ℕ) : ℤ) := by
          dsimp only [x]; push_cast; ring
        rw [this]; exact dvd_sub hd (dvd_mul_of_dvd_right hpZ a)
    · have hpy_gt : y0 + 1 ≤ p := by omega
      have hp_le_fl : p ≤ ⌊z⌋₊ := Nat.le_floor hpz
      have hp_mem : p ∈ ps := by
        have : p ∈ S_ps := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpy_gt, hp_le_fl⟩, hp⟩
        rw [← Finset.mem_sort (r := (· ≤ ·))] at this
        exact List.mem_reverse.mpr this
      have hy_nb := hy_good p hp_mem
      dsimp only [bad] at hy_nb
      push_neg at hy_nb
      exact ⟨by simpa [x] using hy_nb.1, by simpa [x] using hy_nb.2⟩

private lemma h4_main : OMA.R_Erdos724_erdos_724_variants_wilson_R1.H4 :=
  h4_with_y0 (2 ^ 200000) le_rfl

end H4Sieve

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_wilson_R1.H4 := H4Sieve.h4_main

