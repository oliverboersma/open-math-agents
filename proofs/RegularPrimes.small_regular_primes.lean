import FormalConjectures.Wikipedia.RegularPrimes
import Mathlib
/- Adapted from Brasca et al.,KummerCriterion (d6f2d561) and flt-regular (44c57d47),Apache-2.0. -/
namespace SReg.Cert
abbrev V:=List ℤ
def ev {R: Type*} [CommRing R] (x: R) : V → R
| [] => 0
| a :: b => a + x * ev x b
def add: V → V → V
| [],b => b
| a,[] => a
| a::as',b::bs => (a+b)::add as' bs
def scale (n: ℤ) (a: V):=a.map (n * ·)
def rot (a: V):=a.getLastD 0 :: a.dropLast
def rotN: ℕ → V → V
| 0,a => a
| k+1,a => rot (rotN k a)
def shift (k: ℕ) (a: V):=a.drop (a.length-k) ++ a.take (a.length-k)
namespace Speed
def act (k: ℕ) (a: V) : V → V
| [] => scale 0 a
| c::cs => add (scale c a) ((if k ≤ (act k a cs).length then shift k (act k a cs) else rotN k (act k a cs)))
def initV (p: ℕ) : V:=1 :: List.replicate (p-1) 0
end Speed
namespace Pack
def target (p n: ℕ) (c: ℤ):=add [n] (List.replicate p c)
end Pack
def valM (m : ℕ) (x : ℤ) : V → ℤ
| [] => 0
| a::b => (a+x*valM m x b)%m
lemma valM_eq (m : ℕ) (x : ℤ) (b : V) : (valM m x b : ZMod m) = ev (x : ZMod m) b:=by
  induction b with
  | nil => simp [valM,ev]
  | cons a b ih => simp [valM,ev,ZMod.intCast_mod,ih]
def prodM (m : ℕ) (x : ℤ) (b : V) : ℕ → ℤ
| 0 => 1
| k+1 => (prodM m x b k * valM m (x^(k+1)%m) b)%m
lemma prodM_eq (m : ℕ) (x : ℤ) (b : V) (k : ℕ) : (prodM m x b k : ZMod m) = ∏ i ∈ Finset.range k, ev ((x:ZMod m)^(i+1)) b:=by
  induction k with
  | zero => simp [prodM]
  | succ k ih => simp [prodM,Finset.prod_range_succ,ZMod.intCast_mod,valM_eq,ih]
lemma prodM_sound (m : ℕ) (x : ℤ) (a b : V) (k : ℕ) (h : prodM m x b k = valM m x a) : ∏ i ∈ Finset.range k, ev ((x:ZMod m)^(i+1)) b = ev (x:ZMod m) a:=by
  rw [← prodM_eq,← valM_eq,h]
lemma rootM_sound (m p : ℕ) (x : ℤ) (h : x^p%m = 1) : (x:ZMod m)^p=1:=by
  simpa [ZMod.intCast_mod] using congrArg (fun u:ℤ => (u:ZMod m)) h
namespace OneTable
def good (p N: ℕ) (b: V) : Bool :=
  let n:=N^2
  let c: ℤ:=(b.sum^(p-1)-n)/p
  let B: ℤ:=b.sum^(p-1)+2
  let M: ℕ:=(b.sum.toNat^(p-1)+2)^p-1
  decide (0 < N ∧ Speed.act (p-1) (Speed.initV p) b = Speed.act 1 (Speed.initV p) b ∧
    1 < B ∧ (M: ℤ) = B^p-1 ∧ B^p%(M:ℤ)=1 ∧ b.all (fun x => decide (0 ≤ x)) = true ∧
    (Pack.target p n c).length=p ∧ (Pack.target p n c).all (fun x => decide (0 ≤ x ∧ x < B-1)) = true ∧
    b.sum^(p-1) < B-1 ∧ prodM M B b (p-1) = valM M B (Pack.target p n c))
abbrev Row:=ℕ × ℕ × ℕ
def covers (rs: List Row) (q n: ℕ) : Bool:=rs.any fun r => decide (q ∣ r.1 ∧ r.1 ≤ n)
end OneTable
end SReg.Cert
section
namespace SReg.Cert.OneTable
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def digits (r w: ℕ) : ℕ → List ℤ | 0 => [] | n+1 => (w % r: ℕ) :: digits r (w/r) n
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def unpack (p: ℕ) (z: ℕ × ℕ × ℕ) : V:=let a:=digits z.2.1 z.2.2 ((p+1)/2); a ++ a.tail.reverse
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def rows17: List (ℕ × ℕ × ℕ):=[(16,3,19558),(17,5,20499)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def rows19: List (ℕ × ℕ × ℕ):=[(19,5,9663875),(37,3,7655),(113,2,468)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def rows23: List (ℕ × ℕ × ℕ):=[(23,3,226354),(47,3,239477),(137,2,13),(139,2,3721),(229,2,121),(277,2,3639),(367,3,205691),(461,3,262802),(599,4,9864539),(643,3,377985),(691,3,272011),(827,2,152),(829,3,264001)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def g0: List (ℕ × ℕ × ℕ):=[(16384,3,2),(289,3,7200696),(29,3,7174459),(1681,2,4270)]
def g4: List (ℕ × ℕ × ℕ):=[(59,3,22964),(24649,5,28991206275),(173,2,16374),(233,3,2311704)]
def g8: List (ℕ × ℕ × ℕ):=[(347,3,7234230),(349,2,12372),(463,3,7176560),(521,2,12141)]
def g12: List (ℕ × ℕ × ℕ):=[(523,2,26368),(811,2,9220),(929,4,89501695),(1103,3,373)]
def g16: List (ℕ × ℕ × ℕ):=[(1217,4,1051371860),(1277,2,552),(1451,3,816087),(1567,3,9116)]
def g20: List (ℕ × ℕ × ℕ):=[(1741,3,7351516),(1913,3,6620952),(1973,2,1591),(2029,3,6643336)]
def g24: List (ℕ × ℕ × ℕ):=[(2087,8,638131039743),(2089,130,51176593992425211511218886892660),(2203,2,26367),(2377,108,3171607230800439942276066763644)]
def g28: List (ℕ × ℕ × ℕ):=[(2437,28,7001588152067453587),(2551,3,7173894),(2609,5,30209960155),(2843,3,6704248)]
def g32: List (ℕ × ℕ × ℕ):=[(2957,2,8338),(3191,3,11961831),(3307,770,604384992054794675368454664440121281669),(3539,3,7054636)]
def g36: List (ℕ × ℕ × ℕ):=[(3769,2,8964),(3943,4,446273948),(4001,3,88826),(4003,301,15082159927821896754079986326417105782)]
def g40: List (ℕ × ℕ × ℕ):=[(4177,6,437708189),(4349,3,7194215),(4409,2,21804),(4523,3,11958149)]
def g44: List (ℕ × ℕ × ℕ):=[(4583,3,11426719),(4639,5,23131835905),(4813,3,262808),(4871,4,732259328)]
def g48: List (ℕ × ℕ × ℕ):=[(4931,4,374964583),(4987,27,2953994540486926779315),(5279,3,7338559),(5393,3,6979861)]
def g52: List (ℕ × ℕ × ℕ):=[(5569,2,8268),(5683,2,10257),(5741,3,10185952),(5743,2,25369)]
def g56: List (ℕ × ℕ × ℕ):=[(5801,2,24663),(5857,3,2385648),(6089,3,7292570),(6091,3,12173971)]
def g60: List (ℕ × ℕ × ℕ):=[(6263,3,9329606),(6323,2,4593),(6379,3,7331260),(6553,3,7891654)]
def g64: List (ℕ × ℕ × ℕ):=[(6959,3,2311697),(6961,47,5941141837020322629479),(7019,2,24476),(7193,3,10894810)]
def g68: List (ℕ × ℕ × ℕ):=[(7307,3,7708188),(7309,4,711026075),(7481,3,7224727),(7541,5,14258719)]
def g72: List (ℕ × ℕ × ℕ):=[(7829,4,984245333),(8179,3,13557199),(8237,3,5396450),(8293,3,8768698)]
def g76: List (ℕ × ℕ × ℕ):=[(8353,6,454076403120),(8467,3,7239579),(8527,2,15031),(8641,10,11223445678889)]
def g80: List (ℕ × ℕ × ℕ):=[(8699,2,15531),(8933,3,4022932),(9049,3,10546779),(9221,2,14573)]
def g84: List (ℕ × ℕ × ℕ):=[(9281,4,1068061776),(9337,3,803452),(9397,3,7174767),(9511,3,12101774)]
def g88: List (ℕ × ℕ × ℕ):=[(9629,3,737372),(9743,2,5643),(9803,3,7724365),(9859,3,7196242)]
def g92: List (ℕ × ℕ × ℕ):=[(10091,2,5724),(10093,2,1874),(10151,2,16192),(10267,2,21779)]
def g96: List (ℕ × ℕ × ℕ):=[(10499,3,8531041),(10613,2,4871),(10729,4,568759959),(10789,3,5042502)]
def g100: List (ℕ × ℕ × ℕ):=[(10847,4,5593707),(10903,3,6397340),(11251,3,7240098),(11311,3,916869)]
def g104: List (ℕ × ℕ × ℕ):=[(11369,3,13758373),(11483,11,4173764299558623),(11657,4,631085682),(11717,4,447400617)]
def g108: List (ℕ × ℕ × ℕ):=[(11831,3,6577169),(11833,9,23481712487996),(12007,3,4989752),(12239,33,60307985092428724958)]
def g112: List (ℕ × ℕ × ℕ):=[(12413,2,6737),(12527,3,2476511),(12703,3,3801127),(13049,2,13837)]
def g116: List (ℕ × ℕ × ℕ):=[(13109,8,35104588636744),(13339,3,7408004),(13397,3,12215841),(13399,79,9639560122746798763412999)]
def g120: List (ℕ × ℕ × ℕ):=[(13457,4,451484330),(13513,3,3967564),(13687,3,7324870),(13921,3,7766405)]
def g124: List (ℕ × ℕ × ℕ):=[(14153,5,24106422626),(14327,2,855),(14557,4,732355320),(14731,3,7030272)]
def g128: List (ℕ × ℕ × ℕ):=[(15137,3,8687854),(15139,4,999973957),(15313,2,14602),(15427,4,177621845)]
def g132: List (ℕ × ℕ × ℕ):=[(15601,4,631937436),(15661,2,9903),(16007,4,430294378),(16067,2,838)]
def g136: List (ℕ × ℕ × ℕ):=[(16183,3,6708784),(16529,12,15289479823158866),(16703,43,1803960401901389271781),(16763,3,7351875)]
def g140: List (ℕ × ℕ × ℕ):=[(16879,3,790594),(16937,5,28981440625),(16993,3,69623),(17053,3,13630365)]
def g144: List (ℕ × ℕ × ℕ):=[(17167,3,8765523),(17341,3,10125929),(17401,2,4760),(17573,3,7368849)]
def g148: List (ℕ × ℕ × ℕ):=[(17747,3,8749744),(17749,3,4499463),(17807,3,5918305),(17863,3,7504447)]
def g152: List (ℕ × ℕ × ℕ):=[(17921,3,12459420),(17923,22,310415998811885294),(17981,3,7728713),(18097,3,11937631)]
def g156: List (ℕ × ℕ × ℕ):=[(18211,2,7306),(18269,3,8749057),(18329,4,358487385),(18443,3,11938486)]
def g160: List (ℕ × ℕ × ℕ):=[(18503,3,5823234),(18617,3,768736),(18793,2,7593),(19081,2,5659)]
def g164: List (ℕ × ℕ × ℕ):=[(19139,3,10915222),(19141,3,7177127),(19373,4,324179286),(19429,3,200031)]
def g168: List (ℕ × ℕ × ℕ):=[(19489,5,29223547000),(19603,2,10066),(19661,4,632923816),(19777,3,7357810)]
def g172: List (ℕ × ℕ × ℕ):=[(20011,4,989526776),(20183,2,10165),(20357,3,14258074),(20359,3,7136787)]
def g176: List (ℕ × ℕ × ℕ):=[(20533,3,4969838),(20707,3,8780923),(20879,3,2411905),(20939,3,11780263)]
def g180: List (ℕ × ℕ × ℕ):=[(21169,3,6942361),(21227,2,1730),(21401,10,11123456678789),(21517,4,427207320)]
def g184: List (ℕ × ℕ × ℕ):=[(21577,3,731561),(21751,17,10564446784984910),(22039,11,3771325114995),(22157,2,13135)]
def g188: List (ℕ × ℕ × ℕ):=[(22271,12,1689206190899),(22273,3,2489726),(22447,3,6641067),(22619,3,8769013)]
def g192: List (ℕ × ℕ × ℕ):=[(22621,2,15081),(22679,3,7109031),(22853,4,1073736337),(23027,3,3436762)]
def g196: List (ℕ × ℕ × ℕ):=[(23143,3,5381224),(23201,3,10360992),(23431,4,22391529),(23549,2,10946)]
def g200: List (ℕ × ℕ × ℕ):=[(23663,3,7889599),(24071,3,5562606),(24359,4,732867496),(24419,3,8830067)]
def g204: List (ℕ × ℕ × ℕ):=[(24533,11,3768988589871),(24593,3,7141413),(24709,9,205572913327503),(24767,4,353737325)]
def g208: List (ℕ × ℕ × ℕ):=[(25057,3,7413866)]
def u0:=g0++g4
def u1:=g8++g12
def u2:=g16++g20
def u3:=g24++g28
def u4:=g32++g36
def u5:=g40++g44
def u6:=g48++g52
def u7:=g56++g60
def u8:=g64++g68
def u9:=g72++g76
def u10:=g80++g84
def u11:=g88++g92
def u12:=g96++g100
def u13:=g104++g108
def u14:=g112++g116
def u15:=g120++g124
def u16:=g128++g132
def u17:=g136++g140
def u18:=g144++g148
def u19:=g152++g156
def u20:=g160++g164
def u21:=g168++g172
def u22:=g176++g180
def u23:=g184++g188
def u24:=g192++g196
def u25:=g200++g204
def u26:=u0++u1
def u27:=u2++u3
def u28:=u4++u5
def u29:=u6++u7
def u30:=u8++u9
def u31:=u10++u11
def u32:=u12++u13
def u33:=u14++u15
def u34:=u16++u17
def u35:=u18++u19
def u36:=u20++u21
def u37:=u22++u23
def u38:=u24++u25
def u39:=u26++u27
def u40:=u28++u29
def u41:=u30++u31
def u42:=u32++u33
def u43:=u34++u35
def u44:=u36++u37
def u45:=u38++g208
def u46:=u39++u40
def u47:=u41++u42
def u48:=u43++u44
def u49:=u46++u47
def u50:=u48++u45
def u51:=u49++u50
def rows29:=u51
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
abbrev R31s:=List (ℕ × ℕ × ℕ)
def c0: R31s:=[(32,2,15932),(125,9,322140808376),(31,3,21483994),(50653,2,5223)]
def c4: R31s:=[(61,37,9526826812918556590350),(311,3,21347033),(373,3,35281777),(433,3,23117319)]
def c8: R31s:=[(557,5,32045918099),(619,6,2818485283464),(683,3,19906922),(743,2,4163)]
def c12: R31s:=[(929,2,81),(991,2,1034),(1117,5,144948241405),(1301,2,1556)]
def c16: R31s:=[(1303,2,32503),(1427,4,2576971416),(1487,2,40158),(1489,3,21936946)]
def c20: R31s:=[(1549,8,276438647906888),(1613,2,4611),(1861,3,19929373),(2293,2,5669)]
def c24: R31s:=[(2357,3,12607685),(2417,13,665062943753198263),(2543,76,1238403022331401874780711242556),(2729,3,37292386)]
def c28: R31s:=[(2789,4,2867500372),(2791,50,1525230423401383847231755000),(2851,5,152524410150),(3037,2,63459)]
def c32: R31s:=[(3163,2,2312),(3347,12,184873647998365632),(3533,3,19218170),(3659,3,23304342)]
def c36: R31s:=[(3719,2,25187),(3907,3,6817162),(3967,4,4290401616),(4091,2,9253)]
def c40: R31s:=[(4093,3,35784788),(4153,2,6171),(4217,3,7243343),(4339,3,23031421)]
def c44: R31s:=[(4463,49,489334720729433252745175),(4649,3,19889662),(4651,3,1248886),(5021,65,101508965170556196468728646575)]
def c48: R31s:=[(5023,2,51606),(5147,3,26102216),(5209,6,2820672197965),(5333,3,2430578)]
def c52: R31s:=[(5393,3,204482),(5519,2,4401),(5581,2,27084),(5641,2,54499)]
def c56: R31s:=[(5827,3,16475510),(5953,14,920522759387783),(6199,3,22115552),(6263,3,26280072)]
def c60: R31s:=[(6323,17,48481632575649637984),(6449,3,22054071),(6571,4,2590582234),(6883,3,28150738)]
def c64: R31s:=[(7069,2,4172),(7129,3,27899936),(7193,3,15146351),(7253,3,21531387)]
def c68: R31s:=[(7687,3,16827845),(7873,4,2930087252),(7937,3,22230032),(8059,3,20374455)]
def c72: R31s:=[(8123,6,449473283),(8369,3,35924272),(8431,11,38006367640624),(8681,3,19315641)]
def c76: R31s:=[(8741,3,23650129),(8803,2,54317),(8867,3,199390),(8929,3,20994440)]
def c80: R31s:=[(9239,4,1499026583),(9547,3,6111487),(9733,3,38230189),(9857,12,183473820192429084)]
def c84: R31s:=[(9859,3,16745497),(10169,2,26848),(10477,2,53459),(10601,3,7097881)]
def c88: R31s:=[(10663,3,20813286),(10789,4,2522243419),(10973,3,37709549),(11159,3,25779505)]
def c92: R31s:=[(11161,3,19849979),(11471,3,21582501),(11593,3,14591993),(11657,2,24045)]
def c96: R31s:=[(11717,4,1440127270),(11719,2,278),(11779,28,196036174356144674159),(11903,5,151061894526)]
def c100: R31s:=[(12277,4,2506713635),(12401,3,21368323),(12647,3,11406262),(12959,2,13347)]
def c104: R31s:=[(13267,4,1688311447),(13331,3,38056077),(13577,4,1427548863),(13763,3,14535896)]
def c108: R31s:=[(14011,3,7429684),(14197,3,40684668),(14321,2,33836),(14323,4,1365596827)]
def c112: R31s:=[(14447,3,22913563),(14633,3,9373126),(14879,3,41193237),(15313,3,35104465)]
def c116: R31s:=[(15377,29,249927256010809998674867),(15439,3,1879453),(15749,3,26365442),(15809,3,42170110)]
def c120: R31s:=[(16057,3,19773676),(16183,2,22926),(16369,3,36573939),(16493,3,21494905)]
def c124: R31s:=[(16553,2,26552),(16741,2,29943),(16927,10,9877666543210000),(16987,3,42778452)]
def c128: R31s:=[(17299,3,20992565),(17359,3,31090051),(17483,14,916182463773891),(17609,4,3148436753)]
def c132: R31s:=[(17669,2,25976),(17981,3,42434106),(18041,4,1447645479),(18043,5,1527933598)]
def c136: R31s:=[(18229,3,43044133),(18289,3,26293435),(18353,3,21632630),(18413,3,11979292)]
def c140: R31s:=[(18539,3,37643856),(18661,3,16661559),(18787,19,288394434933731503234),(18911,5,151303694530)]
def c144: R31s:=[(18973,3,42309328),(19157,4,354043),(19219,2,30677),(19469,3,23301740)]
def c148: R31s:=[(19531,2,23986),(19717,3,42975630),(19777,3,21530849),(19841,3,42298737)]
def c152: R31s:=[(19963,2,14309),(20089,3,38174925),(20149,3,18570185),(20399,2,35688)]
def c156: R31s:=[(20521,3,7885229),(20707,3,7377601),(20771,29,250235099708950758539986),(21017,11,45531662177619497)]
def c160: R31s:=[(21019,3,21476668),(21143,3,40593637),(21391,3,10323826),(21577,3,28452786)]
def c164: R31s:=[(21701,3,19449327),(22073,2,10674),(22133,2,4707),(22259,3,15441222)]
def c168: R31s:=[(22381,3,26365999),(22567,3,7161952),(22691,7,2360002531),(22817,3,40708052)]
def c172: R31s:=[(22877,10,9898876544221000),(23003,3,18347109),(23063,4,2578097892),(23189,4,2510641486)]
def c176: R31s:=[(23251,13,665389266228835421),(23311,5,307636873),(23497,3,16801909),(23561,8,88373124023)]
def c180: R31s:=[(23623,15,2363899035155624),(23747,3,36127430),(23869,255,29784074625972515542636283933108609),(23993,3,19926086)]
def c184: R31s:=[(24179,3,23714018),(24181,3,23117678),(24551,4,2863305403),(24677,3,42861882)]
def c188: R31s:=[(24799,2,54971),(24923,3,27880714),(25111,3,25614995),(25171,2,29591)]
def c192: R31s:=[(25357,4,446000811),(25667,3,27790096),(25793,3,20733330),(26041,3,22941274)]
def c196: R31s:=[(26227,3,16477598),(26597,4,22561895),(26723,2,6671),(26783,3,23113336)]
def c200: R31s:=[(27031,4,3579391321),(27281,3,6661876),(27527,3,6583966),(27529,3,20466961)]
def c204: R31s:=[(27653,16,77182862730587903),(27901,4,3917105130),(27961,3,26126969),(28087,3,16681460)]
def c208: R31s:=[(28211,3,19748916),(28643,3,36288608),(29017,3,21053145),(29077,3,19191254)]
def c212: R31s:=[(29201,3,7232764),(29327,3,8827837),(29387,3,13551916),(29389,3,16730663)]
def c216: R31s:=[(29573,2,14037),(29759,14,65753101459401),(29761,4,2846539428),(29947,4,359246335)]
def c220: R31s:=[(30071,2,2217),(30133,3,22824628),(30319,3,28137569),(30689,3,35688379)]
def c224: R31s:=[(30937,3,34277969),(31063,6,80988685439),(31123,2,19363),(31247,2,21919)]
def c228: R31s:=[(31249,3,26727289),(31991,5,144897051405),(32117,4,3260716678),(32303,3,21529445)]
def c232: R31s:=[(32363,4,1249468763),(32611,5,12777499),(32797,3,5578077),(32983,3,21542638)]
def c236: R31s:=[(33107,3,36055993),(33479,15,31427081273338649),(33791,3,21610832),(33851,3,534452)]
def c240: R31s:=[(34039,3,23083996),(34471,6,2807539272649),(34721,3,7113298),(34781,6,16108581455)]
def c244: R31s:=[(34843,3,2410897),(35153,3,448588),(35279,3,7201435),(35339,4,2844962453)]
def c248: R31s:=[(35401,4,3844793391),(35527,4,359246762),(35837,3,11982232),(35897,6,2820309673032)]
def c252: R31s:=[(35899,3,28058362),(36083,29,249927268226327751592847),(36209,4,2573806107),(36269,3,22320271)]
def c256: R31s:=[(36457,2,18999),(36643,3,31332847),(36767,3,36164609),(37013,4,2585106276)]
def c260: R31s:=[(37139,3,29433632),(37199,4,2842602148),(37201,3,12745313),(37447,3,8157846)]
def c264: R31s:=[(37511,2,20557),(37571,2,17258),(37573,4,184112489),(37633,60,16213084421048836931872799)]
def c268: R31s:=[(38069,3,13611792),(38317,3,38199572),(38377,3,26291111),(38501,3,21532077)]
def c272: R31s:=[(38749,22,3004815793073723846756),(38873,3,7187379),(39371,3,27907204),(39619,4,1726261925)]
def c276: R31s:=[(39679,4,3956688129),(39929,3,30373903),(39989,3,31030464),(40177,2,4587)]
def c280: R31s:=[(40237,3,28159809),(40361,3,26320967),(40423,3,19759176),(40487,4,1788455467)]
def c284: R31s:=[(40609,3,28132744),(41231,2,15419),(41479,3,14664809),(41539,2,11191)]
def c288: R31s:=[(41603,3,21550368),(41849,8,276997144650305),(41851,3,40694710),(41911,3,23138077)]
def c292: R31s:=[(42221,3,16977532),(42223,4,2639575446),(42283,4,3063585321),(42407,3,2742592)]
def c296: R31s:=[(42409,4,4205412353),(42533,3,40735463),(42719,3,30535903),(42841,3,20884657)]
def c300: R31s:=[(42967,3,22135719),(43151,2,28585),(43399,2,27771),(43649,3,2936766)]
def c304: R31s:=[(43711,4,2875898588),(44021,3,24535101),(44207,3,43019544),(44267,3,15611106)]
def c308: R31s:=[(44269,4,1436337305),(44453,4,1519798166),(44579,12,1410438667026094),(44641,2,18517)]
def c312: R31s:=[(44701,4,3014307495),(44887,3,31254620),(45013,7,32439316203070),(45137,3,21348343)]
def c316: R31s:=[(45197,3,42429255),(45259,3,21543746),(45569,8,276446164324928),(45631,3,26837443)]
def c320: R31s:=[(45757,4,4293543248),(45817,4,1772730984),(45943,3,7181098),(46439,37,9283257588607543357167)]
def c324: R31s:=[(46499,3,20374834),(46687,4,162424404),(46747,6,2188961901901),(46811,10,1123456799999)]
def c328: R31s:=[(46933,30,429955321078794675204930),(46997,3,40652698),(47057,6,2612810914),(47059,2,18101)]
def c332: R31s:=[(47119,3,16504197),(47431,3,26249727),(47491,14,2177036864615155760),(47741,4,2607310806)]
def c336: R31s:=[(48049,3,21702758),(48299,3,35936449),(48731,3,42844474),(48733,2,1521)]
def c340: R31s:=[(48857,3,1305912),(49043,3,17263246),(49103,2,5730),(49477,3,37296598)]
def c344: R31s:=[(49537,3,22059040),(49663,4,290825918),(49787,4,1768285833),(50033,3,37072939)]
def c348: R31s:=[(50159,3,20438582),(50221,4,1385649749),(50591,3,28577191),(50593,3,27555870)]
def c352: R31s:=[(50777,6,2726696236212),(50839,4,3063867308),(51151,3,29429257),(51461,3,541565)]
def c356: R31s:=[(51521,4,2854873753),(51647,3,35872950),(51769,3,20988785),(51893,4,2542414438)]
def c360: R31s:=[(52081,3,275),(52267,4,1726519659),(52391,3,7181121),(52453,3,39107893)]
def c364: R31s:=[(52639,4,2863551489),(53197,3,7903479),(53381,3,42257914),(53507,5,307656249)]
def c368: R31s:=[(53569,2,30366),(53629,3,5612203),(53693,4,2847823844),(53939,2,16478)]
def c372: R31s:=[(54001,9,322097688665),(54251,3,26333552),(54311,3,35848211),(54437,4,3198501121)]
def c376: R31s:=[(54497,3,20962812),(54499,12,10610896650035),(54559,4,2796148648),(54623,2,11961)]
def c380: R31s:=[(54869,16,18369280835531706624),(55057,190,2884089858046564602779214698480656080),(55117,10,9988776643221101),(55243,3,24705444)]
def c384: R31s:=[(55799,3,37533859),(55987,4,2862012840),(56171,3,26335024),(56359,2,10626)]
def c388: R31s:=[(56543,4,1377093729),(56731,4,2554752400),(57041,4,468004516),(57163,3,43036862)]
def c392: R31s:=[(57287,10,12234456678898),(57349,4,2590522261),(57413,73,650247264958056909738176904391),(57847,46,401513940191531793845408386)]
def c396: R31s:=[(58031,3,5579967),(58217,3,1835002),(58403,2,8552),(58901,3,31072570)]
def c400: R31s:=[(58963,96,52034344776396664988334920700000),(59023,3,27920658),(59149,5,121750878125),(59209,4,2876943000)]
def c404: R31s:=[(59273,3,21530642),(59333,15,2095797609710999),(59581,3,14556311),(59707,3,28157057)]
def c408: R31s:=[(60017,87,10769360000886822606277472411748),(60077,691,2701692820013977902454859050250599540786239049),(60139,3,10164073),(60449,5,22863866444)]
def c412: R31s:=[(60637,47,273770086989436231979783),(60761,3,20794825),(60821,4,778999513),(61007,20,655351138570637288400)]
def c416: R31s:=[(61379,2,11147),(61381,3,7428154),(61441,3,17809104),(61627,3,22313546)]
def c420: R31s:=[(61751,4,88507),(61813,3,43029225),(62311,29,250224826443995563136026),(62497,63,16528809986724799848843548)]
def c424: R31s:=[(62683,3,29180020),(62743,7,4876760311163),(62869,3,32773),(62929,3,35714968)]
def c428: R31s:=[(63179,7,32441333057427),(63241,3,5398335),(63487,3,22342773),(63611,4,1465164437)]
def c432: R31s:=[(63737,3,22253117),(63799,3,34475017),(64109,4,2935657557),(64171,23,6132058474955007142502)]
def c436: R31s:=[(64231,3,23634331),(64667,3,15077261),(64853,3,21582984),(65099,4,1553622677)]
def c440: R31s:=[(65101,3,3074481),(65287,3,20473365),(65657,4,3999880514),(65719,3,21456682)]
def c444: R31s:=[(65843,4,2825296231),(66029,4,18202623),(66403,4,22396671),(66463,3,554648)]
def c448: R31s:=[(66587,3,34015464),(66713,2,18718),(66959,3,17285706),(67021,3,42319458)]
def c452: R31s:=[(67271,4,2913638808),(67579,2,18344),(67829,3,11959585),(67891,2,54687)]
def c456: R31s:=[(68261,3,19919692),(68447,4,3937315564),(68449,3,62251),(68633,3,7793635)]
def c460: R31s:=[(68819,3,30852739),(68821,4,2578167704),(68881,3,5776771),(69067,4,1689556550)]
def c464: R31s:=[(69191,3,9360076),(69193,3,21562950),(69317,3,25771609),(69379,4,1716902038)]
def c468: R31s:=[(69439,3,16864861),(69997,4,2794630757),(70061,3,4790704),(70121,3,26490985)]
def c472: R31s:=[(70123,7,28370018116790),(70183,7,28383858580441),(70309,3,21427106),(70619,3,41008829)]
def c476: R31s:=[(70867,3,36483385),(70991,3,4964517),(71237,4,3853076138),(71363,4,1235898775)]
def c480: R31s:=[(71549,3,28518106),(71671,3,2566336),(71983,3,7999034),(72043,3,2214254)]
def c484: R31s:=[(72167,3,20994070),(72169,3,21365706),(72229,3,26568282),(72353,3,5399786)]
def c488: R31s:=[(72727,23,6120465638712035875524),(72911,3,28707561),(72973,3,22109476),(73037,9,25740799091657)]
def c492: R31s:=[(73471,3,35919014),(74027,3,21719705),(74587,6,2807964215538),(74771,32,1258064071569970232319)]
def c496: R31s:=[(74897,3,28395032),(74959,3,23647944),(75083,4,2505680275),(75269,3,21129752)]
def c500: R31s:=[(75329,3,39067963),(75391,47,566446935415380214586971127),(75577,3,43045252),(75641,3,20814522)]
def c504: R31s:=[(75703,3,7259758),(76259,3,16150519),(76261,3,42808242),(76507,18,1365202704355217)]
def c508: R31s:=[(76631,3,2220573),(76757,7,113409028137),(76819,3,14948641),(76943,2,10199)]
def c512: R31s:=[(77003,3,22120403),(77191,4,1503031960),(77377,61,36741150247954770909324720760),(77563,3,37732278)]
def c516: R31s:=[(77687,3,26157694),(77747,3,16537716),(77933,6,2334866785896),(78059,3,24593342)]
def c520: R31s:=[(78121,3,22226468),(78307,2,24259),(78367,82,4177230150341671243215180375314),(78553,3,2400465)]
def c524: R31s:=[(78803,110,116382946786836245625962649389),(78989,3,37465169),(79111,7,5441980811216),(79423,10,11224455577889)]
def c528: R31s:=[(79609,5,83385381593),(79669,3,26786822),(79979,3,21525588),(80167,40,1411911375690733820759)]
def c532: R31s:=[(80537,4,1074877867),(80599,3,24514925),(80849,3,6753811),(80909,3,23235805)]
def c536: R31s:=[(80911,4,1649793378),(81097,3,7702897),(81157,19,49191948808737448),(81281,3,7086950)]
def c540: R31s:=[(81283,3,185278),(81343,118,208207896944164714822230484853),(81839,4,1436386710),(81901,3,2369091)]
def w0:=c0++c4
def w1:=c8++c12
def w2:=c16++c20
def w3:=c24++c28
def w4:=c32++c36
def w5:=c40++c44
def w6:=c48++c52
def w7:=c56++c60
def w8:=c64++c68
def w9:=c72++c76
def w10:=c80++c84
def w11:=c88++c92
def w12:=c96++c100
def w13:=c104++c108
def w14:=c112++c116
def w15:=c120++c124
def w16:=c128++c132
def w17:=c136++c140
def w18:=c144++c148
def w19:=c152++c156
def w20:=c160++c164
def w21:=c168++c172
def w22:=c176++c180
def w23:=c184++c188
def w24:=c192++c196
def w25:=c200++c204
def w26:=c208++c212
def w27:=c216++c220
def w28:=c224++c228
def w29:=c232++c236
def w30:=c240++c244
def w31:=c248++c252
def w32:=c256++c260
def w33:=c264++c268
def w34:=c272++c276
def w35:=c280++c284
def w36:=c288++c292
def w37:=c296++c300
def w38:=c304++c308
def w39:=c312++c316
def w40:=c320++c324
def w41:=c328++c332
def w42:=c336++c340
def w43:=c344++c348
def w44:=c352++c356
def w45:=c360++c364
def w46:=c368++c372
def w47:=c376++c380
def w48:=c384++c388
def w49:=c392++c396
def w50:=c400++c404
def w51:=c408++c412
def w52:=c416++c420
def w53:=c424++c428
def w54:=c432++c436
def w55:=c440++c444
def w56:=c448++c452
def w57:=c456++c460
def w58:=c464++c468
def w59:=c472++c476
def w60:=c480++c484
def w61:=c488++c492
def w62:=c496++c500
def w63:=c504++c508
def w64:=c512++c516
def w65:=c520++c524
def w66:=c528++c532
def w67:=c536++c540
def w68:=w0++w1
def w69:=w2++w3
def w70:=w4++w5
def w71:=w6++w7
def w72:=w8++w9
def w73:=w10++w11
def w74:=w12++w13
def w75:=w14++w15
def w76:=w16++w17
def w77:=w18++w19
def w78:=w20++w21
def w79:=w22++w23
def w80:=w24++w25
def w81:=w26++w27
def w82:=w28++w29
def w83:=w30++w31
def w84:=w32++w33
def w85:=w34++w35
def w86:=w36++w37
def w87:=w38++w39
def w88:=w40++w41
def w89:=w42++w43
def w90:=w44++w45
def w91:=w46++w47
def w92:=w48++w49
def w93:=w50++w51
def w94:=w52++w53
def w95:=w54++w55
def w96:=w56++w57
def w97:=w58++w59
def w98:=w60++w61
def w99:=w62++w63
def w100:=w64++w65
def w101:=w66++w67
def w102:=w68++w69
def w103:=w70++w71
def w104:=w72++w73
def w105:=w74++w75
def w106:=w76++w77
def w107:=w78++w79
def w108:=w80++w81
def w109:=w82++w83
def w110:=w84++w85
def w111:=w86++w87
def w112:=w88++w89
def w113:=w90++w91
def w114:=w92++w93
def w115:=w94++w95
def w116:=w96++w97
def w117:=w98++w99
def w118:=w100++w101
def w119:=w102++w103
def w120:=w104++w105
def w121:=w106++w107
def w122:=w108++w109
def w123:=w110++w111
def w124:=w112++w113
def w125:=w114++w115
def w126:=w116++w117
def w127:=w119++w120
def w128:=w121++w122
def w129:=w123++w124
def w130:=w125++w126
def w131:=w127++w128
def w132:=w129++w130
def w133:=w131++w132
def w134:=w133++w118
def rows31:=w134
end SReg.Cert.OneTable
end
section
namespace SReg.Cert.OneTable
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def valid (p: ℕ) (r: ℕ × ℕ × ℕ):=good p r.1 (unpack p r)
lemma J {f : Row → Bool} {a b : List Row} (x : a.all f = true) (y : b.all f = true) : (a++b).all f = true:=by simp only [List.all_append,x,y,Bool.and_self]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem all17: rows17.all (valid 17):= by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem all19: rows19.all (valid 19):= by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem all23: rows23.all (valid 23):= by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg0:=show g0.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg4:=show g4.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg8:=show g8.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg12:=show g12.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg16:=show g16.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg20:=show g20.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg24:=show g24.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg28:=show g28.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg32:=show g32.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg36:=show g36.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg40:=show g40.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg44:=show g44.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg48:=show g48.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg52:=show g52.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg56:=show g56.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg60:=show g60.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg64:=show g64.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg68:=show g68.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg72:=show g72.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg76:=show g76.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg80:=show g80.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg84:=show g84.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg88:=show g88.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg92:=show g92.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg96:=show g96.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg100:=show g100.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg104:=show g104.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg108:=show g108.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg112:=show g112.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg116:=show g116.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg120:=show g120.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg124:=show g124.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg128:=show g128.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg132:=show g132.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg136:=show g136.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg140:=show g140.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg144:=show g144.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg148:=show g148.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg152:=show g152.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg156:=show g156.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg160:=show g160.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg164:=show g164.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg168:=show g168.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg172:=show g172.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg176:=show g176.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg180:=show g180.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg184:=show g184.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg188:=show g188.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg192:=show g192.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg196:=show g196.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg200:=show g200.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg204:=show g204.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def okg208:=show g208.all (valid 29) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def Hu0:=@J (valid 29) g0 g4 okg0 okg4
def Hu1:=@J (valid 29) g8 g12 okg8 okg12
def Hu2:=@J (valid 29) g16 g20 okg16 okg20
def Hu3:=@J (valid 29) g24 g28 okg24 okg28
def Hu4:=@J (valid 29) g32 g36 okg32 okg36
def Hu5:=@J (valid 29) g40 g44 okg40 okg44
def Hu6:=@J (valid 29) g48 g52 okg48 okg52
def Hu7:=@J (valid 29) g56 g60 okg56 okg60
def Hu8:=@J (valid 29) g64 g68 okg64 okg68
def Hu9:=@J (valid 29) g72 g76 okg72 okg76
def Hu10:=@J (valid 29) g80 g84 okg80 okg84
def Hu11:=@J (valid 29) g88 g92 okg88 okg92
def Hu12:=@J (valid 29) g96 g100 okg96 okg100
def Hu13:=@J (valid 29) g104 g108 okg104 okg108
def Hu14:=@J (valid 29) g112 g116 okg112 okg116
def Hu15:=@J (valid 29) g120 g124 okg120 okg124
def Hu16:=@J (valid 29) g128 g132 okg128 okg132
def Hu17:=@J (valid 29) g136 g140 okg136 okg140
def Hu18:=@J (valid 29) g144 g148 okg144 okg148
def Hu19:=@J (valid 29) g152 g156 okg152 okg156
def Hu20:=@J (valid 29) g160 g164 okg160 okg164
def Hu21:=@J (valid 29) g168 g172 okg168 okg172
def Hu22:=@J (valid 29) g176 g180 okg176 okg180
def Hu23:=@J (valid 29) g184 g188 okg184 okg188
def Hu24:=@J (valid 29) g192 g196 okg192 okg196
def Hu25:=@J (valid 29) g200 g204 okg200 okg204
def Hu26:=@J (valid 29) u0 u1 Hu0 Hu1
def Hu27:=@J (valid 29) u2 u3 Hu2 Hu3
def Hu28:=@J (valid 29) u4 u5 Hu4 Hu5
def Hu29:=@J (valid 29) u6 u7 Hu6 Hu7
def Hu30:=@J (valid 29) u8 u9 Hu8 Hu9
def Hu31:=@J (valid 29) u10 u11 Hu10 Hu11
def Hu32:=@J (valid 29) u12 u13 Hu12 Hu13
def Hu33:=@J (valid 29) u14 u15 Hu14 Hu15
def Hu34:=@J (valid 29) u16 u17 Hu16 Hu17
def Hu35:=@J (valid 29) u18 u19 Hu18 Hu19
def Hu36:=@J (valid 29) u20 u21 Hu20 Hu21
def Hu37:=@J (valid 29) u22 u23 Hu22 Hu23
def Hu38:=@J (valid 29) u24 u25 Hu24 Hu25
def Hu39:=@J (valid 29) u26 u27 Hu26 Hu27
def Hu40:=@J (valid 29) u28 u29 Hu28 Hu29
def Hu41:=@J (valid 29) u30 u31 Hu30 Hu31
def Hu42:=@J (valid 29) u32 u33 Hu32 Hu33
def Hu43:=@J (valid 29) u34 u35 Hu34 Hu35
def Hu44:=@J (valid 29) u36 u37 Hu36 Hu37
def Hu45:=@J (valid 29) u38 g208 Hu38 okg208
def Hu46:=@J (valid 29) u39 u40 Hu39 Hu40
def Hu47:=@J (valid 29) u41 u42 Hu41 Hu42
def Hu48:=@J (valid 29) u43 u44 Hu43 Hu44
def Hu49:=@J (valid 29) u46 u47 Hu46 Hu47
def Hu50:=@J (valid 29) u48 u45 Hu48 Hu45
def Hu51:=@J (valid 29) u49 u50 Hu49 Hu50
theorem all29: rows29.all (valid 29):=Hu51
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h0:=show c0.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h4:=show c4.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h8:=show c8.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h12:=show c12.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h16:=show c16.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h20:=show c20.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h24:=show c24.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h28:=show c28.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h32:=show c32.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h36:=show c36.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h40:=show c40.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h44:=show c44.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h48:=show c48.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h52:=show c52.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h56:=show c56.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h60:=show c60.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h64:=show c64.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h68:=show c68.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h72:=show c72.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h76:=show c76.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h80:=show c80.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h84:=show c84.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h88:=show c88.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h92:=show c92.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h96:=show c96.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h100:=show c100.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h104:=show c104.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h108:=show c108.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h112:=show c112.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h116:=show c116.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h120:=show c120.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h124:=show c124.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h128:=show c128.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h132:=show c132.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h136:=show c136.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h140:=show c140.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h144:=show c144.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h148:=show c148.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h152:=show c152.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h156:=show c156.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h160:=show c160.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h164:=show c164.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h168:=show c168.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h172:=show c172.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h176:=show c176.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h180:=show c180.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h184:=show c184.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h188:=show c188.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h192:=show c192.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h196:=show c196.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h200:=show c200.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h204:=show c204.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h208:=show c208.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h212:=show c212.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h216:=show c216.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h220:=show c220.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h224:=show c224.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h228:=show c228.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h232:=show c232.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h236:=show c236.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h240:=show c240.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h244:=show c244.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h248:=show c248.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h252:=show c252.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h256:=show c256.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h260:=show c260.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h264:=show c264.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h268:=show c268.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h272:=show c272.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h276:=show c276.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h280:=show c280.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h284:=show c284.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h288:=show c288.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h292:=show c292.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h296:=show c296.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h300:=show c300.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h304:=show c304.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h308:=show c308.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h312:=show c312.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h316:=show c316.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h320:=show c320.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h324:=show c324.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h328:=show c328.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h332:=show c332.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h336:=show c336.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h340:=show c340.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h344:=show c344.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h348:=show c348.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h352:=show c352.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h356:=show c356.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h360:=show c360.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h364:=show c364.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h368:=show c368.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h372:=show c372.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h376:=show c376.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h380:=show c380.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h384:=show c384.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h388:=show c388.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h392:=show c392.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h396:=show c396.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h400:=show c400.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h404:=show c404.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h408:=show c408.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h412:=show c412.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h416:=show c416.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h420:=show c420.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h424:=show c424.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h428:=show c428.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h432:=show c432.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h436:=show c436.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h440:=show c440.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h444:=show c444.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h448:=show c448.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h452:=show c452.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h456:=show c456.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h460:=show c460.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h464:=show c464.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h468:=show c468.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h472:=show c472.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h476:=show c476.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h480:=show c480.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h484:=show c484.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h488:=show c488.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h492:=show c492.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h496:=show c496.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h500:=show c500.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h504:=show c504.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h508:=show c508.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h512:=show c512.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h516:=show c516.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h520:=show c520.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h524:=show c524.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h528:=show c528.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h532:=show c532.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h536:=show c536.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def h540:=show c540.all (valid 31) from by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def Hw0:=@J (valid 31) c0 c4 h0 h4
def Hw1:=@J (valid 31) c8 c12 h8 h12
def Hw2:=@J (valid 31) c16 c20 h16 h20
def Hw3:=@J (valid 31) c24 c28 h24 h28
def Hw4:=@J (valid 31) c32 c36 h32 h36
def Hw5:=@J (valid 31) c40 c44 h40 h44
def Hw6:=@J (valid 31) c48 c52 h48 h52
def Hw7:=@J (valid 31) c56 c60 h56 h60
def Hw8:=@J (valid 31) c64 c68 h64 h68
def Hw9:=@J (valid 31) c72 c76 h72 h76
def Hw10:=@J (valid 31) c80 c84 h80 h84
def Hw11:=@J (valid 31) c88 c92 h88 h92
def Hw12:=@J (valid 31) c96 c100 h96 h100
def Hw13:=@J (valid 31) c104 c108 h104 h108
def Hw14:=@J (valid 31) c112 c116 h112 h116
def Hw15:=@J (valid 31) c120 c124 h120 h124
def Hw16:=@J (valid 31) c128 c132 h128 h132
def Hw17:=@J (valid 31) c136 c140 h136 h140
def Hw18:=@J (valid 31) c144 c148 h144 h148
def Hw19:=@J (valid 31) c152 c156 h152 h156
def Hw20:=@J (valid 31) c160 c164 h160 h164
def Hw21:=@J (valid 31) c168 c172 h168 h172
def Hw22:=@J (valid 31) c176 c180 h176 h180
def Hw23:=@J (valid 31) c184 c188 h184 h188
def Hw24:=@J (valid 31) c192 c196 h192 h196
def Hw25:=@J (valid 31) c200 c204 h200 h204
def Hw26:=@J (valid 31) c208 c212 h208 h212
def Hw27:=@J (valid 31) c216 c220 h216 h220
def Hw28:=@J (valid 31) c224 c228 h224 h228
def Hw29:=@J (valid 31) c232 c236 h232 h236
def Hw30:=@J (valid 31) c240 c244 h240 h244
def Hw31:=@J (valid 31) c248 c252 h248 h252
def Hw32:=@J (valid 31) c256 c260 h256 h260
def Hw33:=@J (valid 31) c264 c268 h264 h268
def Hw34:=@J (valid 31) c272 c276 h272 h276
def Hw35:=@J (valid 31) c280 c284 h280 h284
def Hw36:=@J (valid 31) c288 c292 h288 h292
def Hw37:=@J (valid 31) c296 c300 h296 h300
def Hw38:=@J (valid 31) c304 c308 h304 h308
def Hw39:=@J (valid 31) c312 c316 h312 h316
def Hw40:=@J (valid 31) c320 c324 h320 h324
def Hw41:=@J (valid 31) c328 c332 h328 h332
def Hw42:=@J (valid 31) c336 c340 h336 h340
def Hw43:=@J (valid 31) c344 c348 h344 h348
def Hw44:=@J (valid 31) c352 c356 h352 h356
def Hw45:=@J (valid 31) c360 c364 h360 h364
def Hw46:=@J (valid 31) c368 c372 h368 h372
def Hw47:=@J (valid 31) c376 c380 h376 h380
def Hw48:=@J (valid 31) c384 c388 h384 h388
def Hw49:=@J (valid 31) c392 c396 h392 h396
def Hw50:=@J (valid 31) c400 c404 h400 h404
def Hw51:=@J (valid 31) c408 c412 h408 h412
def Hw52:=@J (valid 31) c416 c420 h416 h420
def Hw53:=@J (valid 31) c424 c428 h424 h428
def Hw54:=@J (valid 31) c432 c436 h432 h436
def Hw55:=@J (valid 31) c440 c444 h440 h444
def Hw56:=@J (valid 31) c448 c452 h448 h452
def Hw57:=@J (valid 31) c456 c460 h456 h460
def Hw58:=@J (valid 31) c464 c468 h464 h468
def Hw59:=@J (valid 31) c472 c476 h472 h476
def Hw60:=@J (valid 31) c480 c484 h480 h484
def Hw61:=@J (valid 31) c488 c492 h488 h492
def Hw62:=@J (valid 31) c496 c500 h496 h500
def Hw63:=@J (valid 31) c504 c508 h504 h508
def Hw64:=@J (valid 31) c512 c516 h512 h516
def Hw65:=@J (valid 31) c520 c524 h520 h524
def Hw66:=@J (valid 31) c528 c532 h528 h532
def Hw67:=@J (valid 31) c536 c540 h536 h540
def Hw68:=@J (valid 31) w0 w1 Hw0 Hw1
def Hw69:=@J (valid 31) w2 w3 Hw2 Hw3
def Hw70:=@J (valid 31) w4 w5 Hw4 Hw5
def Hw71:=@J (valid 31) w6 w7 Hw6 Hw7
def Hw72:=@J (valid 31) w8 w9 Hw8 Hw9
def Hw73:=@J (valid 31) w10 w11 Hw10 Hw11
def Hw74:=@J (valid 31) w12 w13 Hw12 Hw13
def Hw75:=@J (valid 31) w14 w15 Hw14 Hw15
def Hw76:=@J (valid 31) w16 w17 Hw16 Hw17
def Hw77:=@J (valid 31) w18 w19 Hw18 Hw19
def Hw78:=@J (valid 31) w20 w21 Hw20 Hw21
def Hw79:=@J (valid 31) w22 w23 Hw22 Hw23
def Hw80:=@J (valid 31) w24 w25 Hw24 Hw25
def Hw81:=@J (valid 31) w26 w27 Hw26 Hw27
def Hw82:=@J (valid 31) w28 w29 Hw28 Hw29
def Hw83:=@J (valid 31) w30 w31 Hw30 Hw31
def Hw84:=@J (valid 31) w32 w33 Hw32 Hw33
def Hw85:=@J (valid 31) w34 w35 Hw34 Hw35
def Hw86:=@J (valid 31) w36 w37 Hw36 Hw37
def Hw87:=@J (valid 31) w38 w39 Hw38 Hw39
def Hw88:=@J (valid 31) w40 w41 Hw40 Hw41
def Hw89:=@J (valid 31) w42 w43 Hw42 Hw43
def Hw90:=@J (valid 31) w44 w45 Hw44 Hw45
def Hw91:=@J (valid 31) w46 w47 Hw46 Hw47
def Hw92:=@J (valid 31) w48 w49 Hw48 Hw49
def Hw93:=@J (valid 31) w50 w51 Hw50 Hw51
def Hw94:=@J (valid 31) w52 w53 Hw52 Hw53
def Hw95:=@J (valid 31) w54 w55 Hw54 Hw55
def Hw96:=@J (valid 31) w56 w57 Hw56 Hw57
def Hw97:=@J (valid 31) w58 w59 Hw58 Hw59
def Hw98:=@J (valid 31) w60 w61 Hw60 Hw61
def Hw99:=@J (valid 31) w62 w63 Hw62 Hw63
def Hw100:=@J (valid 31) w64 w65 Hw64 Hw65
def Hw101:=@J (valid 31) w66 w67 Hw66 Hw67
def Hw102:=@J (valid 31) w68 w69 Hw68 Hw69
def Hw103:=@J (valid 31) w70 w71 Hw70 Hw71
def Hw104:=@J (valid 31) w72 w73 Hw72 Hw73
def Hw105:=@J (valid 31) w74 w75 Hw74 Hw75
def Hw106:=@J (valid 31) w76 w77 Hw76 Hw77
def Hw107:=@J (valid 31) w78 w79 Hw78 Hw79
def Hw108:=@J (valid 31) w80 w81 Hw80 Hw81
def Hw109:=@J (valid 31) w82 w83 Hw82 Hw83
def Hw110:=@J (valid 31) w84 w85 Hw84 Hw85
def Hw111:=@J (valid 31) w86 w87 Hw86 Hw87
def Hw112:=@J (valid 31) w88 w89 Hw88 Hw89
def Hw113:=@J (valid 31) w90 w91 Hw90 Hw91
def Hw114:=@J (valid 31) w92 w93 Hw92 Hw93
def Hw115:=@J (valid 31) w94 w95 Hw94 Hw95
def Hw116:=@J (valid 31) w96 w97 Hw96 Hw97
def Hw117:=@J (valid 31) w98 w99 Hw98 Hw99
def Hw118:=@J (valid 31) w100 w101 Hw100 Hw101
def Hw119:=@J (valid 31) w102 w103 Hw102 Hw103
def Hw120:=@J (valid 31) w104 w105 Hw104 Hw105
def Hw121:=@J (valid 31) w106 w107 Hw106 Hw107
def Hw122:=@J (valid 31) w108 w109 Hw108 Hw109
def Hw123:=@J (valid 31) w110 w111 Hw110 Hw111
def Hw124:=@J (valid 31) w112 w113 Hw112 Hw113
def Hw125:=@J (valid 31) w114 w115 Hw114 Hw115
def Hw126:=@J (valid 31) w116 w117 Hw116 Hw117
def Hw127:=@J (valid 31) w119 w120 Hw119 Hw120
def Hw128:=@J (valid 31) w121 w122 Hw121 Hw122
def Hw129:=@J (valid 31) w123 w124 Hw123 Hw124
def Hw130:=@J (valid 31) w125 w126 Hw125 Hw126
def Hw131:=@J (valid 31) w127 w128 Hw127 Hw128
def Hw132:=@J (valid 31) w129 w130 Hw129 Hw130
def Hw133:=@J (valid 31) w131 w132 Hw131 Hw132
def Hw134:=@J (valid 31) w133 w118 Hw133 Hw118
theorem all31: rows31.all (valid 31):=Hw134
end SReg.Cert.OneTable
end
section
namespace SReg.Cert.OneTable
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cover17 (q f: ℕ) (hq: q.Prime) (hf: 0 < f) (hlt: q^f < 49) (hh: q = 17 ∨ (q: ZMod 17)^(f*2)=1) : covers rows17 q (q^f):= by
  letI: Fact (Nat.Prime 17):=⟨by decide⟩
  have hle:=Nat.le_self_pow hf.ne' q
  rcases hh with rfl | hs
  · obtain ⟨r,hr,hv⟩:=List.any_eq_true.mp (show covers rows17 17 17 by decide +kernel)
    obtain ⟨hd,hN⟩:=of_decide_eq_true hv
    exact List.any_eq_true.mpr ⟨r,hr,decide_eq_true (And.intro hd (hN.trans hle))⟩
  by_cases h1: f = 1
  · subst f; rw [pow_one] at hlt ⊢; rw [one_mul] at hs
    have C: ∀ j: Fin 3,∀ a: Fin 2,let n:=17*j.val+(if a.val=0 then 1 else 16); n.Prime → n<49 → covers rows17 n n:= by decide +kernel
    rcases sq_eq_one_iff.mp hs with h|h
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%17=1 at hh
      have eq: 17*(q/17)+1=q:= by omega
      exact eq ▸ C ⟨q/17,by omega⟩ 0 (eq.symm ▸ hq) (eq.symm ▸ hlt)
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%17=16 at hh
      have eq: 17*(q/17)+16=q:= by omega
      exact eq ▸ C ⟨q/17,by omega⟩ 1 (eq.symm ▸ hq) (eq.symm ▸ hlt)
  · have h2:=Nat.pow_le_pow_right hq.pos (show 2 ≤ f by omega)
    have ha: q < 8:= by by_contra! hh; have:=Nat.pow_le_pow_left hh 2; omega
    have hb: f < 6:= by by_contra! hh; have:=(Nat.pow_le_pow_left hq.two_le 6).trans (Nat.pow_le_pow_right hq.pos hh); omega
    have C: ∀ a: Fin 8,a.val.Prime → ∀ b: Fin 6,1 < b.val → a.val^b.val < 49 → (a.val: ZMod 17)^(b.val*2)=1 → covers rows17 a.val (a.val^b.val):= by decide +kernel
    exact C ⟨q,ha⟩ hq ⟨f,hb⟩ (by change 1 < f; omega) hlt hs
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cover19 (q f: ℕ) (hq: q.Prime) (hf: 0 < f) (hlt: q^f < 123) (hh: q = 19 ∨ (q: ZMod 19)^(f*2)=1) : covers rows19 q (q^f):= by
  letI: Fact (Nat.Prime 19):=⟨by decide⟩
  have hle:=Nat.le_self_pow hf.ne' q
  rcases hh with rfl | hs
  · obtain ⟨r,hr,hv⟩:=List.any_eq_true.mp (show covers rows19 19 19 by decide +kernel)
    obtain ⟨hd,hN⟩:=of_decide_eq_true hv
    exact List.any_eq_true.mpr ⟨r,hr,decide_eq_true (And.intro hd (hN.trans hle))⟩
  by_cases h1: f = 1
  · subst f; rw [pow_one] at hlt ⊢; rw [one_mul] at hs
    have C: ∀ j: Fin 7,∀ a: Fin 2,let n:=19*j.val+(if a.val=0 then 1 else 18); n.Prime → n<123 → covers rows19 n n:= by decide +kernel
    rcases sq_eq_one_iff.mp hs with h|h
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%19=1 at hh
      have eq: 19*(q/19)+1=q:= by omega
      exact eq ▸ C ⟨q/19,by omega⟩ 0 (eq.symm ▸ hq) (eq.symm ▸ hlt)
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%19=18 at hh
      have eq: 19*(q/19)+18=q:= by omega
      exact eq ▸ C ⟨q/19,by omega⟩ 1 (eq.symm ▸ hq) (eq.symm ▸ hlt)
  · have h2:=Nat.pow_le_pow_right hq.pos (show 2 ≤ f by omega)
    have ha: q < 12:= by by_contra! hh; have:=Nat.pow_le_pow_left hh 2; omega
    have hb: f < 7:= by by_contra! hh; have:=(Nat.pow_le_pow_left hq.two_le 7).trans (Nat.pow_le_pow_right hq.pos hh); omega
    have C: ∀ a: Fin 12,a.val.Prime → ∀ b: Fin 7,1 < b.val → a.val^b.val < 123 → (a.val: ZMod 19)^(b.val*2)=1 → covers rows19 a.val (a.val^b.val):= by decide +kernel
    exact C ⟨q,ha⟩ hq ⟨f,hb⟩ (by change 1 < f; omega) hlt hs
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cover23 (q f: ℕ) (hq: q.Prime) (hf: 0 < f) (hlt: q^f < 901) (hh: q = 23 ∨ (q: ZMod 23)^(f*2)=1) : covers rows23 q (q^f):= by
  letI: Fact (Nat.Prime 23):=⟨by decide⟩
  have hle:=Nat.le_self_pow hf.ne' q
  rcases hh with rfl | hs
  · obtain ⟨r,hr,hv⟩:=List.any_eq_true.mp (show covers rows23 23 23 by decide +kernel)
    obtain ⟨hd,hN⟩:=of_decide_eq_true hv
    exact List.any_eq_true.mpr ⟨r,hr,decide_eq_true (And.intro hd (hN.trans hle))⟩
  by_cases h1: f = 1
  · subst f; rw [pow_one] at hlt ⊢; rw [one_mul] at hs
    have C: ∀ j: Fin 40,∀ a: Fin 2,let n:=23*j.val+(if a.val=0 then 1 else 22); n.Prime → n<901 → covers rows23 n n:= by decide +kernel
    rcases sq_eq_one_iff.mp hs with h|h
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%23=1 at hh
      have eq: 23*(q/23)+1=q:= by omega
      exact eq ▸ C ⟨q/23,by omega⟩ 0 (eq.symm ▸ hq) (eq.symm ▸ hlt)
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%23=22 at hh
      have eq: 23*(q/23)+22=q:= by omega
      exact eq ▸ C ⟨q/23,by omega⟩ 1 (eq.symm ▸ hq) (eq.symm ▸ hlt)
  · have h2:=Nat.pow_le_pow_right hq.pos (show 2 ≤ f by omega)
    have ha: q < 31:= by by_contra! hh; have:=Nat.pow_le_pow_left hh 2; omega
    have hb: f < 10:= by by_contra! hh; have:=(Nat.pow_le_pow_left hq.two_le 10).trans (Nat.pow_le_pow_right hq.pos hh); omega
    have C: ∀ a: Fin 31,a.val.Prime → ∀ b: Fin 10,1 < b.val → a.val^b.val < 901 → (a.val: ZMod 23)^(b.val*2)=1 → covers rows23 a.val (a.val^b.val):= by decide +kernel
    exact C ⟨q,ha⟩ hq ⟨f,hb⟩ (by change 1 < f; omega) hlt hs
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def rp396 (rs: List Row) (i q n: ℕ) : Bool:=match rs[i]? with
  | some r => decide (q ∣ r.1 ∧ r.1 ≤ n)
  | none => false
lemma rp397 {rs: List Row} {i q n} (h: rp396 rs i q n) : covers rs q n:= by
  unfold rp396 at h
  split at h
  next r he => exact List.any_eq_true.mpr ⟨r,List.mem_of_getElem? he,h⟩
  next => contradiction
def sieveOK (rs: List Row) (p B n: ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => (decide (n < 2 ∨ B ≤ n) || (if d%2=0 then decide (1 < d/2 ∧ d/2 < n ∧ d/2 ∣ n) else rp396 rs (d/2) n n)) && sieveOK rs p B (n+p) ds
lemma rp398 {rs: List Row} {p B n: ℕ} {ds: List ℕ} (h: sieveOK rs p B n ds) {j: ℕ} (hj: j < ds.length) (hp: (n+p*j).Prime) (hb: n+p*j < B) : covers rs (n+p*j) (n+p*j):= by
  induction ds generalizing n j with
  | nil => simp at hj
  | cons d ds ih =>
    obtain ⟨ha,ht⟩:=Bool.and_eq_true_iff.mp h
    cases j with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero] at hp hb ⊢
      rcases Bool.or_eq_true_iff.mp ha with he|he
      · rcases of_decide_eq_true he with h|h <;> have:=hp.two_le <;> omega
      · split at he
        next => obtain ⟨h1,h2,h3⟩:=of_decide_eq_true he; rcases (Nat.dvd_prime hp).mp h3 with h|h <;> omega
        next => exact rp397 he
    | succ j =>
      rw [Nat.mul_succ] at hp hb ⊢
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (n:=n+p) ht (j:=j) (by simpa using hj) (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hp) (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hb)
def rp399: List ℕ:=[0,4,9,4,6,4,10,4,15,4,6,4,19,4,22,4,6,4,25,4,14,4,6,4,34,4,10,4,6,4,26,4,29,4,6,4,10,4,31,4,6,4,46,4,35,4,6,4,14,4,37,4,6,4,39,4,10,4,6,4,41,4,14,4,6,4,10,4,45,4,6,4,51,4,38,4,6,4,62,4,22,4,6,4,57,4,10,4,6,4,14,4,34,4,6,4,10,4,63,4,6,4,22,4,14,4,6,4,26,4,67,4,6,4,69,4,10,4,6,4,118,4,71,4,6,4,10,4,94,4,6,4,14,4,26,4,6,4,79,4,62,4,6,4,81,4,10,4,6,4,38,4,85,4,6,4,10,4,89,4,6,4,74,4,134,4,6,4,22,4,97,4,6,4,14,4,10,4,6,4,46,4,101,4,6,4,10,4,14,4,6,4,105,4,34,4,6,4,111,4,113,4,6,4,122,4,10,4,6,4,119,4,22,4,6,4,10,4,123,4,6,4,94,4,146,4,6,4,34,4,14,4,6,4,22,4,10,4,6,4,131,4,133,4,6,4,10,4,135,4,6,4,139,4,106,4,6,4,14,4,143,4,6,4,26,4,10,4,6,4,82,4,14,4,6,4,10,4,22,4,6,4,147,4,149,4,6,4,153,4,26,4,6,4,157,4,10,4,6,4,14,4,38,4,6,4,10,4,163,4,6,4,165,4,14,4,6,4,46,4,169,4,6,4,173,4,10,4,6,4,34,4,177,4,6,4,10,4,181,4,6,4,14,4,22,4,6,4,187,4,189,4,6,4,191,4,10,4,6,4,106,4,193,4,6,4,10,4,26,4,6,4,199,4,201,4,6,4,38,4,206,4,6,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp400: sieveOK rows29 29 25131 1 rp399:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp401 (j: ℕ) (lo: 0 ≤ j) (hi: j < 384) (hp: (29*j+1).Prime) (hb: 29*j+1 < 25131) : covers rows29 (29*j+1) (29*j+1):= by
  have he: 1+29*(j-0) = 29*j+1:= by omega
  exact he ▸ rp398 rp400 (j:=j-0) (by change j-0 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp402: List ℕ:=[14,4,10,4,6,4,207,4,209,4,6,4,10,4,14,4,6,4,178,4,215,4,6,4,219,4,22,4,6,4,221,4,10,4,6,4,26,4,223,4,6,4,10,4,225,4,6,4,22,4,82,4,6,4,229,4,14,4,6,4,158,4,10,4,6,4,62,4,233,4,6,4,10,4,74,4,6,4,239,4,241,4,6,4,14,4,86,4,6,4,118,4,10,4,6,4,247,4,14,4,6,4,10,4,249,4,6,4,38,4,251,4,6,4,22,4,34,4,6,4,94,4,10,4,6,4,14,4,62,4,6,4,10,4,166,4,6,4,259,4,14,4,6,4,261,4,38,4,6,4,34,4,10,4,6,4,267,4,22,4,6,4,10,4,46,4,6,4,14,4,271,4,6,4,273,4,218,4,6,4,22,4,10,4,6,4,122,4,106,4,6,4,10,4,279,4,6,4,281,4,283,4,6,4,287,4,142,4,6,4,14,4,10,4,6,4,293,4,26,4,6,4,10,4,14,4,6,4,299,4,301,4,6,4,307,4,309,4,6,4,311,4,10,4,6,4,22,4,317,4,6,4,10,4,321,4,6,4,86,4,38,4,6,4,325,4,14,4,6,4,26,4,10,4,6,4,331,4,146,4,6,4,10,4,333,4,6,4,337,4,22,4,6,4,14,4,26,4,6,4,166,4,10,4,6,4,345,4,14,4,6,4,10,4,62,4,6,4,351,4,34,4,6,4,353,4,118,4,6,4,355,4,10,4,6,4,14,4,359,4,6,4,10,4,86,4,6,4,26,4,14,4,6,4,34,4,22,4,6,4,369,4,10,4,6,4,371,4,226,4,6,4,10,4,26,4,6,4,14,4,375,4,6,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp403: sieveOK rows29 29 25131 11137 rp402:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp404 (j: ℕ) (lo: 384 ≤ j) (hi: j < 768) (hp: (29*j+1).Prime) (hb: 29*j+1 < 25131) : covers rows29 (29*j+1) (29*j+1):= by
  have he: 11137+29*(j-384) = 29*j+1:= by omega
  exact he ▸ rp398 rp403 (j:=j-384) (by change j-384 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp405: List ℕ:=[379,4,274,4,6,4,381,4,10,4,6,4,385,4,387,4,6,4,10,4,389,4,6,4,206,4,391,4,6,4,393,4,395,4,6,4,14,4,10,4,6,4,26,4,399,4,6,4,10,4,14,4,6,4,62,4,46,4,6,4,22,4,403,4,6,4,38,4,10,4,6,4,34,4,407,4,6,4,10,4,411,4,6,4,413,4,415,4,6,4,298,4,14,4,6,4,417,4,10]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp406: sieveOK rows29 29 25131 22273 rp405:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp407 (j: ℕ) (lo: 768 ≤ j) (hi: j < 867) (hp: (29*j+1).Prime) (hb: 29*j+1 < 25131) : covers rows29 (29*j+1) (29*j+1):= by
  have he: 22273+29*(j-768) = 29*j+1:= by omega
  exact he ▸ rp398 rp406 (j:=j-768) (by change j-768 < 99; omega) (he.symm ▸ hp) (he.symm ▸ hb)
theorem rp408 (j: ℕ) (lo: 0 ≤ j) (hi: j < 768) (hp: (29*j+1).Prime) (hb: 29*j+1 < 25131) : covers rows29 (29*j+1) (29*j+1):= by
  by_cases h: j < 384
  · exact rp401 j lo h hp hb
  · exact rp404 j (by omega) hi hp hb
theorem rp409 (j: ℕ) (lo: 0 ≤ j) (hi: j < 867) (hp: (29*j+1).Prime) (hb: 29*j+1 < 25131) : covers rows29 (29*j+1) (29*j+1):= by
  by_cases h: j < 768
  · exact rp408 j lo h hp hb
  · exact rp407 j (by omega) hi hp hb
def rp410: List ℕ:=[4,6,4,10,4,13,4,6,4,34,4,17,4,6,4,21,4,23,4,6,4,14,4,10,4,6,4,27,4,22,4,6,4,10,4,14,4,6,4,38,4,33,4,6,4,62,4,26,4,6,4,22,4,10,4,6,4,82,4,74,4,6,4,10,4,43,4,6,4,47,4,49,4,6,4,53,4,14,4,6,4,55,4,10,4,6,4,59,4,61,4,6,4,10,4,22,4,6,4,26,4,65,4,6,4,14,4,62,4,6,4,34,4,10,4,6,4,22,4,14,4,6,4,10,4,26,4,6,4,73,4,86,4,6,4,75,4,77,4,6,4,46,4,10,4,6,4,14,4,83,4,6,4,10,4,87,4,6,4,91,4,14,4,6,4,93,4,95,4,6,4,99,4,10,4,6,4,26,4,34,4,6,4,10,4,103,4,6,4,14,4,38,4,6,4,107,4,109,4,6,4,115,4,10,4,6,4,74,4,117,4,6,4,10,4,121,4,6,4,125,4,82,4,6,4,127,4,22,4,6,4,14,4,10,4,6,4,134,4,129,4,6,4,10,4,14,4,6,4,22,4,137,4,6,4,26,4,141,4,6,4,142,4,10,4,6,4,38,4,145,4,6,4,10,4,106,4,6,4,46,4,26,4,6,4,151,4,14,4,6,4,155,4,10,4,6,4,159,4,161,4,6,4,10,4,38,4,6,4,178,4,166,4,6,4,14,4,167,4,6,4,171,4,10,4,6,4,175,4,14,4,6,4,10,4,179,4,6,4,183,4,94,4,6,4,158,4,185,4,6,4,118,4,10,4,6,4,14,4,22,4,6,4,10,4,195,4,6,4,197,4,14,4,6,4,203,4,194,4,6,4,22,4,10]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp411: sieveOK rows29 29 25131 28 rp410:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp412 (j: ℕ) (lo: 0 ≤ j) (hi: j < 384) (hp: (29*j+28).Prime) (hb: 29*j+28 < 25131) : covers rows29 (29*j+28) (29*j+28):= by
  have he: 28+29*(j-0) = 29*j+28:= by omega
  exact he ▸ rp398 rp411 (j:=j-0) (by change j-0 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp413: List ℕ:=[4,6,4,205,4,86,4,6,4,10,4,211,4,6,4,14,4,213,4,6,4,122,4,217,4,6,4,26,4,10,4,6,4,34,4,38,4,6,4,10,4,22,4,6,4,74,4,227,4,6,4,94,4,26,4,6,4,14,4,10,4,6,4,22,4,231,4,6,4,10,4,14,4,6,4,235,4,237,4,6,4,243,4,82,4,6,4,245,4,10,4,6,4,166,4,62,4,6,4,10,4,34,4,6,4,26,4,22,4,6,4,38,4,14,4,6,4,253,4,10,4,6,4,255,4,46,4,6,4,10,4,26,4,6,4,34,4,257,4,6,4,14,4,122,4,6,4,263,4,10,4,6,4,265,4,14,4,6,4,10,4,142,4,6,4,82,4,269,4,6,4,46,4,22,4,6,4,86,4,10,4,6,4,14,4,275,4,6,4,10,4,277,4,6,4,22,4,14,4,6,4,285,4,34,4,6,4,289,4,10,4,6,4,291,4,254,4,6,4,10,4,295,4,6,4,14,4,297,4,6,4,303,4,305,4,6,4,34,4,10,4,6,4,313,4,315,4,6,4,10,4,319,4,6,4,134,4,323,4,6,4,22,4,38,4,6,4,14,4,10,4,6,4,327,4,329,4,6,4,10,4,14,4,6,4,335,4,26,4,6,4,339,4,341,4,6,4,343,4,10,4,6,4,142,4,22,4,6,4,10,4,347,4,6,4,106,4,349,4,6,4,118,4,14,4,6,4,22,4,10,4,6,4,94,4,357,4,6,4,10,4,74,4,6,4,361,4,363,4,6,4,14,4,365,4,6,4,367,4,10,4,6,4,218,4,14,4,6,4,10,4,22,4,6,4,373,4,38,4,6,4,194,4,377]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp414: sieveOK rows29 29 25131 11164 rp413:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp415 (j: ℕ) (lo: 384 ≤ j) (hi: j < 768) (hp: (29*j+28).Prime) (hb: 29*j+28 < 25131) : covers rows29 (29*j+28) (29*j+28):= by
  have he: 11164+29*(j-384) = 29*j+28:= by omega
  exact he ▸ rp398 rp414 (j:=j-384) (by change j-384 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp416: List ℕ:=[4,6,4,122,4,10,4,6,4,14,4,383,4,6,4,10,4,46,4,6,4,62,4,14,4,6,4,82,4,146,4,6,4,26,4,10,4,6,4,397,4,166,4,6,4,10,4,401,4,6,4,14,4,22,4,6,4,34,4,26,4,6,4,46,4,10,4,6,4,38,4,405,4,6,4,10,4,409,4,6,4,314,4,62,4,6,4,206,4,278,4,6,4,14,4,10,4,6,0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp417: sieveOK rows29 29 25131 22300 rp416:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp418 (j: ℕ) (lo: 768 ≤ j) (hi: j < 867) (hp: (29*j+28).Prime) (hb: 29*j+28 < 25131) : covers rows29 (29*j+28) (29*j+28):= by
  have he: 22300+29*(j-768) = 29*j+28:= by omega
  exact he ▸ rp398 rp417 (j:=j-768) (by change j-768 < 99; omega) (he.symm ▸ hp) (he.symm ▸ hb)
theorem rp419 (j: ℕ) (lo: 0 ≤ j) (hi: j < 768) (hp: (29*j+28).Prime) (hb: 29*j+28 < 25131) : covers rows29 (29*j+28) (29*j+28):= by
  by_cases h: j < 384
  · exact rp412 j lo h hp hb
  · exact rp415 j (by omega) hi hp hb
theorem rp420 (j: ℕ) (lo: 0 ≤ j) (hi: j < 867) (hp: (29*j+28).Prime) (hb: 29*j+28 < 25131) : covers rows29 (29*j+28) (29*j+28):= by
  by_cases h: j < 768
  · exact rp419 j lo h hp hb
  · exact rp418 j (by omega) hi hp hb
def rp421: List ℕ:=[0,4,6,4,10,4,22,4,6,4,11,4,13,4,6,4,14,4,26,4,6,4,21,4,10,4,6,4,22,4,14,4,6,4,10,4,29,4,6,4,34,4,33,4,6,4,35,4,39,4,6,4,43,4,10,4,6,4,14,4,45,4,6,4,10,4,46,4,6,4,26,4,14,4,6,4,49,4,82,4,6,4,53,4,10,4,6,4,55,4,59,4,6,4,10,4,26,4,6,4,14,4,65,4,6,4,38,4,34,4,6,4,46,4,10,4,6,4,71,4,122,4,6,4,10,4,75,4,6,4,58,4,81,4,6,4,85,4,22,4,6,4,14,4,10,4,6,4,26,4,93,4,6,4,10,4,14,4,6,4,22,4,97,4,6,4,99,4,101,4,6,4,103,4,10,4,6,4,107,4,109,4,6,4,10,4,146,4,6,4,86,4,115,4,6,4,118,4,14,4,6,4,119,4,10,4,6,4,123,4,34,4,6,4,10,4,74,4,6,4,38,4,127,4,6,4,14,4,129,4,6,4,133,4,10,4,6,4,94,4,14,4,6,4,10,4,58,4,6,4,46,4,26,4,6,4,141,4,38,4,6,4,145,4,10,4,6,4,14,4,22,4,6,4,10,4,86,4,6,4,151,4,14,4,6,4,157,4,159,4,6,4,22,4,10,4,6,4,161,4,142,4,6,4,10,4,106,4,6,4,14,4,34,4,6,4,194,4,169,4,6,4,134,4,10,4,6,4,171,4,26,4,6,4,10,4,22,4,6,4,166,4,46,4,6,4,34,4,179,4,6,4,14,4,10,4,6,4,22,4,185,4,6,4,10,4,14,4,6,4,187,4,38,4,6,4,191,4,195,4,6,4,26,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp422: sieveOK rows31 31 82161 1 rp421:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp423 (j: ℕ) (lo: 0 ≤ j) (hi: j < 384) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  have he: 1+31*(j-0) = 31*j+1:= by omega
  exact he ▸ rp398 rp422 (j:=j-0) (by change j-0 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp424: List ℕ:=[10,4,6,4,46,4,214,4,6,4,10,4,201,4,6,4,203,4,22,4,6,4,82,4,14,4,6,4,106,4,10,4,6,4,207,4,58,4,6,4,10,4,94,4,6,4,211,4,118,4,6,4,14,4,74,4,6,4,142,4,10,4,6,4,34,4,14,4,6,4,10,4,134,4,6,4,26,4,223,4,6,4,225,4,22,4,6,4,227,4,10,4,6,4,14,4,46,4,6,4,10,4,26,4,6,4,22,4,14,4,6,4,233,4,235,4,6,4,158,4,10,4,6,4,237,4,194,4,6,4,10,4,34,4,6,4,14,4,243,4,6,4,46,4,245,4,6,4,247,4,10,4,6,4,26,4,251,4,6,4,10,4,253,4,6,4,34,4,218,4,6,4,22,4,257,4,6,4,14,4,10,4,6,4,263,4,82,4,6,4,10,4,14,4,6,4,267,4,271,4,6,4,74,4,273,4,6,4,277,4,10,4,6,4,281,4,22,4,6,4,10,4,285,4,6,4,287,4,289,4,6,4,26,4,14,4,6,4,22,4,10,4,6,4,295,4,297,4,6,4,10,4,299,4,6,4,303,4,26,4,6,4,14,4,307,4,6,4,34,4,10,4,6,4,311,4,14,4,6,4,10,4,22,4,6,4,317,4,166,4,6,4,38,4,321,4,6,4,323,4,10,4,6,4,14,4,325,4,6,4,10,4,327,4,6,4,329,4,14,4,6,4,86,4,94,4,6,4,331,4,10,4,6,4,335,4,26,4,6,4,10,4,142,4,6,4,14,4,22,4,6,4,343,4,274,4,6,4,347,4,10,4,6,4,351,4,353,4,6,4,10,4,46,4,6,4,359,4,361,4,6,4,363,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp425: sieveOK rows31 31 82161 11905 rp424:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp426 (j: ℕ) (lo: 384 ≤ j) (hi: j < 768) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  have he: 11905+31*(j-384) = 31*j+1:= by omega
  exact he ▸ rp398 rp425 (j:=j-384) (by change j-384 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp427: List ℕ:=[58,4,6,4,14,4,10,4,6,4,178,4,371,4,6,4,10,4,14,4,6,4,38,4,86,4,6,4,375,4,22,4,6,4,46,4,10,4,6,4,74,4,381,4,6,4,10,4,82,4,6,4,22,4,34,4,6,4,58,4,14,4,6,4,389,4,10,4,6,4,166,4,391,4,6,4,10,4,393,4,6,4,26,4,122,4,6,4,14,4,134,4,6,4,397,4,10,4,6,4,142,4,14,4,6,4,10,4,26,4,6,4,403,4,74,4,6,4,22,4,407,4,6,4,409,4,10,4,6,4,14,4,411,4,6,4,10,4,415,4,6,4,417,4,14,4,6,4,146,4,298,4,6,4,202,4,10,4,6,4,26,4,22,4,6,4,10,4,421,4,6,4,14,4,38,4,6,4,427,4,431,4,6,4,22,4,10,4,6,4,34,4,437,4,6,4,10,4,439,4,6,4,441,4,443,4,6,4,158,4,445,4,6,4,14,4,10,4,6,4,218,4,94,4,6,4,10,4,14,4,6,4,58,4,451,4,6,4,26,4,457,4,6,4,274,4,10,4,6,4,22,4,206,4,6,4,10,4,34,4,6,4,74,4,26,4,6,4,461,4,14,4,6,4,463,4,10,4,6,4,106,4,86,4,6,4,10,4,38,4,6,4,34,4,22,4,6,4,14,4,226,4,6,4,334,4,10,4,6,4,46,4,14,4,6,4,10,4,262,4,6,4,477,4,194,4,6,4,122,4,481,4,6,4,254,4,10,4,6,4,14,4,26,4,6,4,10,4,58,4,6,4,485,4,14,4,6,4,134,4,22,4,6,4,38,4,10,4,6,4,493,4,118,4,6,4,10,4,499,4,6,4,14,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp428: sieveOK rows31 31 82161 23809 rp427:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp429 (j: ℕ) (lo: 768 ≤ j) (hi: j < 1152) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  have he: 23809+31*(j-768) = 31*j+1:= by omega
  exact he ▸ rp398 rp428 (j:=j-768) (by change j-768 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp430: List ℕ:=[142,4,6,4,501,4,505,4,6,4,26,4,10,4,6,4,509,4,38,4,6,4,10,4,513,4,6,4,314,4,515,4,6,4,517,4,26,4,6,4,14,4,10,4,6,4,521,4,525,4,6,4,10,4,14,4,6,4,529,4,533,4,6,4,22,4,122,4,6,4,86,4,10,4,6,4,537,4,34,4,6,4,10,4,539,4,6,4,26,4,278,4,6,4,38,4,14,4,6,4,74,4,10,4,6,4,118,4,22,4,6,4,10,4,26,4,6,4,549,4,94,4,6,4,14,4,551,4,6,4,22,4,10,4,6,4,555,4,14,4,6,4,10,4,559,4,6,4,382,4,362,4,6,4,567,4,46,4,6,4,178,4,10,4,6,4,14,4,302,4,6,4,10,4,22,4,6,4,571,4,14,4,6,4,166,4,573,4,6,4,577,4,10,4,6,4,22,4,581,4,6,4,10,4,254,4,6,4,14,4,587,4,6,4,34,4,593,4,6,4,595,4,10,4,6,4,597,4,358,4,6,4,10,4,601,4,6,4,82,4,22,4,6,4,26,4,38,4,6,4,14,4,10,4,6,4,607,4,609,4,6,4,10,4,14,4,6,4,611,4,26,4,6,4,613,4,617,4,6,4,206,4,10,4,6,4,621,4,623,4,6,4,10,4,46,4,6,4,158,4,629,4,6,4,631,4,14,4,6,4,122,4,10,4,6,4,34,4,398,4,6,4,10,4,641,4,6,4,22,4,645,4,6,4,14,4,326,4,6,4,46,4,10,4,6,4,647,4,14,4,6,4,10,4,651,4,6,4,655,4,38,4,6,4,659,4,663,4,6,4,58,4,10,4,6,4,14,4,667,4,6,4,10,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp431: sieveOK rows31 31 82161 35713 rp430:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp432 (j: ℕ) (lo: 1152 ≤ j) (hi: j < 1536) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  have he: 35713+31*(j-1152) = 31*j+1:= by omega
  exact he ▸ rp398 rp431 (j:=j-1152) (by change j-1152 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp433: List ℕ:=[34,4,6,4,671,4,14,4,6,4,22,4,74,4,6,4,26,4,10,4,6,4,675,4,274,4,6,4,10,4,86,4,6,4,14,4,679,4,6,4,681,4,26,4,6,4,683,4,10,4,6,4,38,4,22,4,6,4,10,4,687,4,6,4,386,4,691,4,6,4,693,4,158,4,6,4,14,4,10,4,6,4,697,4,699,4,6,4,10,4,14,4,6,4,26,4,703,4,6,4,82,4,34,4,6,4,218,4,10,4,6,4,94,4,709,4,6,4,10,4,22,4,6,4,711,4,134,4,6,4,715,4,14,4,6,4,34,4,10,4,6,4,22,4,721,4,6,4,10,4,723,4,6,4,725,4,727,4,6,4,14,4,729,4,6,4,38,4,10,4,6,4,26,4,14,4,6,4,10,4,731,4,6,4,142,4,22,4,6,4,735,4,737,4,6,4,741,4,10,4,6,4,14,4,34,4,6,4,10,4,226,4,6,4,747,4,14,4,6,4,751,4,755,4,6,4,759,4,10,4,6,4,46,4,74,4,6,4,10,4,763,4,6,4,14,4,767,4,6,4,26,4,22,4,6,4,146,4,10,4,6,4,278,4,82,4,6,4,10,4,771,4,6,4,22,4,26,4,6,4,38,4,775,4,6,4,14,4,10,4,6,4,122,4,779,4,6,4,10,4,14,4,6,4,781,4,34,4,6,4,178,4,118,4,6,4,789,4,10,4,6,4,478,4,46,4,6,4,10,4,791,4,6,4,58,4,262,4,6,4,22,4,14,4,6,4,82,4,10,4,6,4,214,4,26,4,6,4,10,4,106,4,6,4,799,4,801,4,6,4,14,4,805,4,6,4,809,4,10,4,6,4,74,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp434: sieveOK rows31 31 82161 47617 rp433:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp435 (j: ℕ) (lo: 1536 ≤ j) (hi: j < 1920) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  have he: 47617+31*(j-1536) = 31*j+1:= by omega
  exact he ▸ rp398 rp434 (j:=j-1536) (by change j-1536 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp436: List ℕ:=[14,4,6,4,10,4,815,4,6,4,38,4,202,4,6,4,817,4,146,4,6,4,22,4,10,4,6,4,14,4,122,4,6,4,10,4,825,4,6,4,827,4,14,4,6,4,118,4,26,4,6,4,226,4,10,4,6,4,34,4,835,4,6,4,10,4,22,4,6,4,14,4,74,4,6,4,86,4,46,4,6,4,106,4,10,4,6,4,22,4,845,4,6,4,10,4,847,4,6,4,26,4,849,4,6,4,362,4,853,4,6,4,14,4,10,4,6,4,857,4,859,4,6,4,10,4,14,4,6,4,206,4,22,4,6,4,865,4,867,4,6,4,194,4,10,4,6,4,869,4,871,4,6,4,10,4,278,4,6,4,34,4,38,4,6,4,875,4,14,4,6,4,877,4,10,4,6,4,26,4,881,4,6,4,10,4,883,4,6,4,298,4,466,4,6,4,14,4,22,4,6,4,314,4,10,4,6,4,82,4,14,4,6,4,10,4,46,4,6,4,22,4,893,4,6,4,142,4,34,4,6,4,899,4,10,4,6,4,14,4,58,4,6,4,10,4,166,4,6,4,905,4,14,4,6,4,26,4,502,4,6,4,34,4,10,4,6,4,909,4,911,4,6,4,10,4,38,4,6,4,14,4,26,4,6,4,22,4,917,4,6,4,94,4,10,4,6,4,58,4,923,4,6,4,10,4,302,4,6,4,146,4,931,4,6,4,933,4,935,4,6,4,14,4,10,4,6,4,454,4,22,4,6,4,10,4,14,4,6,4,941,4,945,4,6,4,398,4,949,4,6,4,22,4,10,4,6,4,951,4,26,4,6,4,10,4,953,4,6,4,955,4,82,4,6,4,218,4,14,4,6,4,959,4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp437: sieveOK rows31 31 82161 59521 rp436:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp438 (j: ℕ) (lo: 1920 ≤ j) (hi: j < 2304) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  have he: 59521+31*(j-1920) = 31*j+1:= by omega
  exact he ▸ rp398 rp437 (j:=j-1920) (by change j-1920 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp439: List ℕ:=[10,4,6,4,961,4,38,4,6,4,10,4,22,4,6,4,46,4,965,4,6,4,14,4,971,4,6,4,26,4,10,4,6,4,22,4,14,4,6,4,10,4,977,4,6,4,526,4,34,4,6,4,983,4,26,4,6,4,74,4,10,4,6,4,14,4,985,4,6,4,10,4,146,4,6,4,178,4,14,4,6,4,34,4,362,4,6,4,58,4,10,4,6,4,158,4,94,4,6,4,10,4,989,4,6,4,14,4,46,4,6,4,993,4,995,4,6,4,997,4,10,4,6,4,999,4,142,4,6,4,10,4,26,4,6,4,1007,4,1009,4,6,4,382,4,22,4,6,4,14,4,10,4,6,4,46,4,1013,4,6,4,10,4,14,4,6,4,22,4,394,4,6,4,1019,4,1021,4,6,4,1023,4,10,4,6,4,26,4,1027,4,6,4,10,4,1029,4,6,4,38,4,1031,4,6,4,1033,4,14,4,6,4,86,4,10,4,6,4,1039,4,1041,4,6,4,10,4,1043,4,6,4,214,4,106,4,6,4,14,4,38,4,6,4,1049,4,10,4,6,4,1051,4,14,4,6,4,10,4,34,4,6,4,122,4,1055,4,6,4,26,4,1057,4,6,4,142,4,10,4,6,4,14,4,22,4,6,4,10,4,1063,4,6,4,34,4,14,4,6,4,46,4,86,4,6,4,22,4,10,4,6,4,1069,4,1073,4,6,4,10,4,1075,4,6,4,14,4,1081,4,6,4,254,4,514,4,6,4,278,4,10,4,6,4,106,4,446,4,6,4,10,4,22,4,6,4,226]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp440: sieveOK rows31 31 82161 71425 rp439:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp441 (j: ℕ) (lo: 2304 ≤ j) (hi: j < 2651) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  have he: 71425+31*(j-2304) = 31*j+1:= by omega
  exact he ▸ rp398 rp440 (j:=j-2304) (by change j-2304 < 347; omega) (he.symm ▸ hp) (he.symm ▸ hb)
theorem rp442 (j: ℕ) (lo: 0 ≤ j) (hi: j < 768) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  by_cases h: j < 384
  · exact rp423 j lo h hp hb
  · exact rp426 j (by omega) hi hp hb
theorem rp443 (j: ℕ) (lo: 768 ≤ j) (hi: j < 1536) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  by_cases h: j < 1152
  · exact rp429 j lo h hp hb
  · exact rp432 j (by omega) hi hp hb
theorem rp444 (j: ℕ) (lo: 1536 ≤ j) (hi: j < 2304) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  by_cases h: j < 1920
  · exact rp435 j lo h hp hb
  · exact rp438 j (by omega) hi hp hb
theorem rp445 (j: ℕ) (lo: 0 ≤ j) (hi: j < 1536) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  by_cases h: j < 768
  · exact rp442 j lo h hp hb
  · exact rp443 j (by omega) hi hp hb
theorem rp446 (j: ℕ) (lo: 1536 ≤ j) (hi: j < 2651) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  by_cases h: j < 2304
  · exact rp444 j lo h hp hb
  · exact rp441 j (by omega) hi hp hb
theorem rp447 (j: ℕ) (lo: 0 ≤ j) (hi: j < 2651) (hp: (31*j+1).Prime) (hb: 31*j+1 < 82161) : covers rows31 (31*j+1) (31*j+1):= by
  by_cases h: j < 1536
  · exact rp445 j lo h hp hb
  · exact rp446 j (by omega) hi hp hb
def rp448: List ℕ:=[4,9,4,6,4,10,4,26,4,6,4,14,4,15,4,6,4,17,4,19,4,6,4,23,4,10,4,6,4,25,4,27,4,6,4,10,4,22,4,6,4,31,4,58,4,6,4,37,4,41,4,6,4,14,4,10,4,6,4,22,4,34,4,6,4,10,4,14,4,6,4,46,4,47,4,6,4,51,4,74,4,6,4,38,4,10,4,6,4,57,4,61,4,6,4,10,4,63,4,6,4,58,4,22,4,6,4,67,4,14,4,6,4,69,4,10,4,6,4,73,4,38,4,6,4,10,4,77,4,6,4,79,4,83,4,6,4,14,4,87,4,6,4,89,4,10,4,6,4,91,4,14,4,6,4,10,4,118,4,6,4,95,4,26,4,6,4,82,4,22,4,6,4,105,4,10,4,6,4,14,4,111,4,6,4,10,4,113,4,6,4,22,4,14,4,6,4,34,4,117,4,6,4,121,4,10,4,6,4,46,4,125,4,6,4,10,4,58,4,6,4,14,4,106,4,6,4,74,4,131,4,6,4,135,4,10,4,6,4,86,4,26,4,6,4,10,4,137,4,6,4,146,4,139,4,6,4,22,4,143,4,6,4,14,4,10,4,6,4,147,4,149,4,6,4,10,4,14,4,6,4,153,4,155,4,6,4,158,4,178,4,6,4,26,4,10,4,6,4,34,4,22,4,6,4,10,4,163,4,6,4,38,4,165,4,6,4,167,4,14,4,6,4,22,4,10,4,6,4,106,4,82,4,6,4,10,4,173,4,6,4,175,4,177,4,6,4,14,4,38,4,6,4,181,4,10,4,6,4,183,4,14,4,6,4,10,4,22,4,6,4,26,4,189,4,6,4,193,4,197,4,6,4,199]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp449: sieveOK rows31 31 82161 30 rp448:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp450 (j: ℕ) (lo: 0 ≤ j) (hi: j < 384) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  have he: 30+31*(j-0) = 31*j+30:= by omega
  exact he ▸ rp398 rp449 (j:=j-0) (by change j-0 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp451: List ℕ:=[4,10,4,6,4,14,4,58,4,6,4,10,4,26,4,6,4,34,4,14,4,6,4,205,4,142,4,6,4,82,4,10,4,6,4,94,4,206,4,6,4,10,4,209,4,6,4,14,4,22,4,6,4,213,4,46,4,6,4,215,4,10,4,6,4,26,4,217,4,6,4,10,4,219,4,6,4,221,4,38,4,6,4,178,4,34,4,6,4,14,4,10,4,6,4,229,4,134,4,6,4,10,4,14,4,6,4,202,4,231,4,6,4,86,4,22,4,6,4,34,4,10,4,6,4,239,4,118,4,6,4,10,4,241,4,6,4,22,4,74,4,6,4,26,4,14,4,6,4,249,4,10,4,6,4,38,4,106,4,6,4,10,4,255,4,6,4,142,4,26,4,6,4,14,4,259,4,6,4,261,4,10,4,6,4,265,4,14,4,6,4,10,4,38,4,6,4,269,4,86,4,6,4,22,4,275,4,6,4,279,4,10,4,6,4,14,4,283,4,6,4,10,4,94,4,6,4,122,4,14,4,6,4,291,4,293,4,6,4,46,4,10,4,6,4,118,4,22,4,6,4,10,4,301,4,6,4,14,4,305,4,6,4,106,4,309,4,6,4,22,4,10,4,6,4,82,4,313,4,6,4,10,4,315,4,6,4,74,4,34,4,6,4,319,4,214,4,6,4,14,4,10,4,6,4,146,4,38,4,6,4,10,4,14,4,6,4,94,4,278,4,6,4,34,4,26,4,6,4,333,4,10,4,6,4,22,4,337,4,6,4,10,4,339,4,6,4,341,4,122,4,6,4,345,4,14,4,6,4,349,4,10,4,6,4,134,4,355,4,6,4,10,4,357,4,6,4,26,4,22,4,6,4,14]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp452: sieveOK rows31 31 82161 11934 rp451:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp453 (j: ℕ) (lo: 384 ≤ j) (hi: j < 768) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  have he: 11934+31*(j-384) = 31*j+30:= by omega
  exact he ▸ rp398 rp452 (j:=j-384) (by change j-384 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp454: List ℕ:=[4,365,4,6,4,367,4,10,4,6,4,369,4,14,4,6,4,10,4,26,4,6,4,373,4,302,4,6,4,58,4,377,4,6,4,379,4,10,4,6,4,14,4,383,4,6,4,10,4,385,4,6,4,166,4,14,4,6,4,387,4,22,4,6,4,206,4,10,4,6,4,26,4,86,4,6,4,10,4,194,4,6,4,14,4,46,4,6,4,395,4,106,4,6,4,399,4,10,4,6,4,298,4,401,4,6,4,10,4,34,4,6,4,38,4,134,4,6,4,405,4,94,4,6,4,14,4,10,4,6,4,46,4,413,4,6,4,10,4,14,4,6,4,34,4,58,4,6,4,22,4,38,4,6,4,419,4,10,4,6,4,254,4,334,4,6,4,10,4,423,4,6,4,425,4,26,4,6,4,429,4,14,4,6,4,433,4,10,4,6,4,435,4,22,4,6,4,10,4,74,4,6,4,58,4,218,4,6,4,14,4,34,4,6,4,22,4,10,4,6,4,447,4,14,4,6,4,10,4,449,4,6,4,178,4,453,4,6,4,455,4,262,4,6,4,34,4,10,4,6,4,14,4,26,4,6,4,10,4,22,4,6,4,459,4,14,4,6,4,46,4,206,4,6,4,465,4,10,4,6,4,22,4,467,4,6,4,10,4,469,4,6,4,14,4,471,4,6,4,473,4,82,4,6,4,26,4,10,4,6,4,475,4,34,4,6,4,10,4,58,4,6,4,479,4,22,4,6,4,202,4,26,4,6,4,14,4,10,4,6,4,38,4,483,4,6,4,10,4,14,4,6,4,487,4,489,4,6,4,146,4,46,4,6,4,491,4,10,4,6,4,495,4,497,4,6,4,10,4,38,4,6,4,26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp455: sieveOK rows31 31 82161 23838 rp454:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp456 (j: ℕ) (lo: 768 ≤ j) (hi: j < 1152) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  have he: 23838+31*(j-768) = 31*j+30:= by omega
  exact he ▸ rp398 rp455 (j:=j-768) (by change j-768 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp457: List ℕ:=[4,166,4,6,4,503,4,14,4,6,4,507,4,10,4,6,4,511,4,94,4,6,4,10,4,26,4,6,4,22,4,34,4,6,4,14,4,74,4,6,4,519,4,10,4,6,4,523,4,14,4,6,4,10,4,527,4,6,4,531,4,535,4,6,4,34,4,118,4,6,4,38,4,10,4,6,4,14,4,362,4,6,4,10,4,541,4,6,4,543,4,14,4,6,4,22,4,545,4,6,4,547,4,10,4,6,4,278,4,38,4,6,4,10,4,46,4,6,4,14,4,146,4,6,4,346,4,553,4,6,4,106,4,10,4,6,4,557,4,22,4,6,4,10,4,561,4,6,4,563,4,565,4,6,4,26,4,569,4,6,4,14,4,10,4,6,4,34,4,214,4,6,4,10,4,14,4,6,4,314,4,26,4,6,4,38,4,575,4,6,4,122,4,10,4,6,4,579,4,583,4,6,4,10,4,22,4,6,4,585,4,589,4,6,4,591,4,14,4,6,4,382,4,10,4,6,4,22,4,599,4,6,4,10,4,34,4,6,4,603,4,158,4,6,4,14,4,605,4,6,4,142,4,10,4,6,4,218,4,14,4,6,4,10,4,226,4,6,4,34,4,22,4,6,4,615,4,194,4,6,4,619,4,10,4,6,4,14,4,625,4,6,4,10,4,627,4,6,4,38,4,14,4,6,4,633,4,635,4,6,4,26,4,10,4,6,4,637,4,639,4,6,4,10,4,643,4,6,4,14,4,358,4,6,4,386,4,22,4,6,4,58,4,10,4,6,4,649,4,202,4,6,4,10,4,653,4,6,4,22,4,657,4,6,4,661,4,665,4,6,4,14,4,10,4,6,4,86,4,669,4,6,4,10]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp458: sieveOK rows31 31 82161 35742 rp457:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp459 (j: ℕ) (lo: 1152 ≤ j) (hi: j < 1536) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  have he: 35742+31*(j-1152) = 31*j+30:= by omega
  exact he ▸ rp398 rp458 (j:=j-1152) (by change j-1152 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp460: List ℕ:=[4,14,4,6,4,26,4,46,4,6,4,94,4,673,4,6,4,134,4,10,4,6,4,74,4,82,4,6,4,10,4,26,4,6,4,677,4,118,4,6,4,22,4,14,4,6,4,685,4,10,4,6,4,46,4,34,4,6,4,10,4,689,4,6,4,106,4,38,4,6,4,14,4,58,4,6,4,695,4,10,4,6,4,26,4,14,4,6,4,10,4,218,4,6,4,701,4,74,4,6,4,705,4,707,4,6,4,22,4,10,4,6,4,14,4,166,4,6,4,10,4,206,4,6,4,713,4,14,4,6,4,58,4,717,4,6,4,719,4,10,4,6,4,38,4,46,4,6,4,10,4,22,4,6,4,14,4,34,4,6,4,26,4,302,4,6,4,202,4,10,4,6,4,22,4,146,4,6,4,10,4,38,4,6,4,733,4,26,4,6,4,34,4,739,4,6,4,14,4,10,4,6,4,743,4,745,4,6,4,10,4,14,4,6,4,749,4,22,4,6,4,753,4,757,4,6,4,298,4,10,4,6,4,761,4,326,4,6,4,10,4,765,4,6,4,74,4,58,4,6,4,86,4,14,4,6,4,38,4,10,4,6,4,769,4,26,4,6,4,10,4,82,4,6,4,773,4,106,4,6,4,14,4,22,4,6,4,777,4,10,4,6,4,34,4,14,4,6,4,10,4,454,4,6,4,22,4,783,4,6,4,785,4,787,4,6,4,26,4,10,4,6,4,14,4,394,4,6,4,10,4,158,4,6,4,793,4,14,4,6,4,795,4,26,4,6,4,797,4,10,4,6,4,82,4,178,4,6,4,10,4,34,4,6,4,14,4,803,4,6,4,22,4,807,4,6,4,811,4,10,4,6,4,106]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp461: sieveOK rows31 31 82161 47646 rp460:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp462 (j: ℕ) (lo: 1536 ≤ j) (hi: j < 1920) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  have he: 47646+31*(j-1536) = 31*j+30:= by omega
  exact he ▸ rp398 rp461 (j:=j-1536) (by change j-1536 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp463: List ℕ:=[4,813,4,6,4,10,4,118,4,6,4,26,4,334,4,6,4,819,4,821,4,6,4,14,4,10,4,6,4,823,4,22,4,6,4,10,4,14,4,6,4,829,4,214,4,6,4,831,4,346,4,6,4,22,4,10,4,6,4,833,4,837,4,6,4,10,4,839,4,6,4,841,4,843,4,6,4,482,4,14,4,6,4,46,4,10,4,6,4,26,4,194,4,6,4,10,4,22,4,6,4,38,4,851,4,6,4,14,4,855,4,6,4,34,4,10,4,6,4,22,4,14,4,6,4,10,4,861,4,6,4,863,4,82,4,6,4,262,4,38,4,6,4,218,4,10,4,6,4,14,4,873,4,6,4,10,4,74,4,6,4,466,4,14,4,6,4,26,4,134,4,6,4,278,4,10,4,6,4,879,4,34,4,6,4,10,4,202,4,6,4,14,4,26,4,6,4,885,4,887,4,6,4,889,4,10,4,6,4,891,4,58,4,6,4,10,4,382,4,6,4,46,4,895,4,6,4,897,4,22,4,6,4,14,4,10,4,6,4,901,4,903,4,6,4,10,4,14,4,6,4,22,4,38,4,6,4,214,4,907,4,6,4,158,4,10,4,6,4,58,4,26,4,6,4,10,4,122,4,6,4,913,4,34,4,6,4,915,4,14,4,6,4,919,4,10,4,6,4,921,4,925,4,6,4,10,4,927,4,6,4,929,4,46,4,6,4,14,4,937,4,6,4,26,4,10,4,6,4,38,4,14,4,6,4,10,4,939,4,6,4,943,4,947,4,6,4,334,4,26,4,6,4,314,4,10,4,6,4,14,4,22,4,6,4,10,4,38,4,6,4,454,4,14,4,6,4,957,4,74,4,6,4,22]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp464: sieveOK rows31 31 82161 59550 rp463:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp465 (j: ℕ) (lo: 1920 ≤ j) (hi: j < 2304) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  have he: 59550+31*(j-1920) = 31*j+30:= by omega
  exact he ▸ rp398 rp464 (j:=j-1920) (by change j-1920 < 384; omega) (he.symm ▸ hp) (he.symm ▸ hb)
def rp466: List ℕ:=[4,10,4,6,4,202,4,963,4,6,4,10,4,362,4,6,4,14,4,967,4,6,4,969,4,973,4,6,4,975,4,10,4,6,4,34,4,158,4,6,4,10,4,22,4,6,4,979,4,981,4,6,4,134,4,298,4,6,4,14,4,10,4,6,4,22,4,46,4,6,4,10,4,14,4,6,4,82,4,526,4,6,4,987,4,86,4,6,4,94,4,10,4,6,4,26,4,38,4,6,4,10,4,34,4,6,4,991,4,22,4,6,4,46,4,14,4,6,4,326,4,10,4,6,4,1001,4,1003,4,6,4,10,4,1005,4,6,4,34,4,478,4,6,4,14,4,106,4,6,4,254,4,10,4,6,4,1011,4,14,4,6,4,10,4,1015,4,6,4,1017,4,542,4,6,4,26,4,22,4,6,4,1025,4,10,4,6,4,14,4,134,4,6,4,10,4,422,4,6,4,22,4,14,4,6,4,1035,4,34,4,6,4,1037,4,10,4,6,4,382,4,74,4,6,4,10,4,1045,4,6,4,14,4,1047,4,6,4,58,4,142,4,6,4,34,4,10,4,6,4,274,4,1053,4,6,4,10,4,358,4,6,4,86,4,122,4,6,4,22,4,1059,4,6,4,14,4,10,4,6,4,1061,4,26,4,6,4,10,4,14,4,6,4,38,4,194,4,6,4,1065,4,1067,4,6,4,178,4,10,4,6,4,1071,4,22,4,6,4,10,4,1077,4,6,4,1079,4,1083,4,6,4,82,4,14,4,6,4,22,4,10,4,6,4,1085,4,1087,4,6,4,10,4,46,4,6,0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rp467: sieveOK rows31 31 82161 71454 rp466:= by decide +kernel
set_option maxRecDepth 100000 in
theorem rp468 (j: ℕ) (lo: 2304 ≤ j) (hi: j < 2651) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  have he: 71454+31*(j-2304) = 31*j+30:= by omega
  exact he ▸ rp398 rp467 (j:=j-2304) (by change j-2304 < 347; omega) (he.symm ▸ hp) (he.symm ▸ hb)
theorem rp469 (j: ℕ) (lo: 0 ≤ j) (hi: j < 768) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  by_cases h: j < 384
  · exact rp450 j lo h hp hb
  · exact rp453 j (by omega) hi hp hb
theorem rp470 (j: ℕ) (lo: 768 ≤ j) (hi: j < 1536) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  by_cases h: j < 1152
  · exact rp456 j lo h hp hb
  · exact rp459 j (by omega) hi hp hb
theorem rp471 (j: ℕ) (lo: 1536 ≤ j) (hi: j < 2304) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  by_cases h: j < 1920
  · exact rp462 j lo h hp hb
  · exact rp465 j (by omega) hi hp hb
theorem rp472 (j: ℕ) (lo: 0 ≤ j) (hi: j < 1536) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  by_cases h: j < 768
  · exact rp469 j lo h hp hb
  · exact rp470 j (by omega) hi hp hb
theorem rp473 (j: ℕ) (lo: 1536 ≤ j) (hi: j < 2651) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  by_cases h: j < 2304
  · exact rp471 j lo h hp hb
  · exact rp468 j (by omega) hi hp hb
theorem rp474 (j: ℕ) (lo: 0 ≤ j) (hi: j < 2651) (hp: (31*j+30).Prime) (hb: 31*j+30 < 82161) : covers rows31 (31*j+30) (31*j+30):= by
  by_cases h: j < 1536
  · exact rp472 j lo h hp hb
  · exact rp473 j (by omega) hi hp hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
def powOK (p B: ℕ) (rs: List Row) (q f: ℕ) : Bool :=
  decide (¬ q.Prime ∨ f ≤ 1 ∨ B ≤ q^f ∨ q^(f*2)%p ≠ 1) || covers rs q (q^f)
lemma rp475 {p B q f: ℕ} {rs: List Row} [Fact p.Prime] (h: powOK p B rs q f) (hq: q.Prime) (hf: 1 < f) (hb: q^f < B) (hz: (q: ZMod p)^(f*2)=1) : covers rs q (q^f):= by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · have he: (q^(f*2))%p=1:= by
      have hz' : ((q^(f*2) : ℕ) : ZMod p) = 1:= by simpa using hz
      have:=congrArg ZMod.val hz'
      simpa only [ZMod.val_natCast,ZMod.val_one] using this
    rcases of_decide_eq_true h with hn|hn|hn|hn
    · contradiction
    · omega
    · omega
    · contradiction
  · exact h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem powTab29: (List.range 159).all (fun q => (List.range 15).all (powOK 29 25131 rows29 q)):= by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem powTab31: (List.range 287).all (fun q => (List.range 17).all (powOK 31 82161 rows31 q)):= by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cover29 (q f: ℕ) (hq: q.Prime) (hf: 0 < f) (hlt: q^f < 25131) (hh: q = 29 ∨ (q: ZMod 29)^(f*2)=1) : covers rows29 q (q^f):= by
  letI: Fact (Nat.Prime 29):=⟨by decide⟩
  have hle:=Nat.le_self_pow hf.ne' q
  rcases hh with rfl | hs
  · obtain ⟨r,hr,hv⟩:=List.any_eq_true.mp (show covers rows29 29 29 by decide +kernel)
    obtain ⟨hd,hN⟩:=of_decide_eq_true hv
    exact List.any_eq_true.mpr ⟨r,hr,decide_eq_true (And.intro hd (hN.trans hle))⟩
  by_cases h1: f = 1
  · subst f; rw [pow_one] at hlt ⊢; rw [one_mul] at hs
    rcases sq_eq_one_iff.mp hs with h|h
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%29=1 at hh
      have eq: 29*(q/29)+1=q:= by omega
      exact eq ▸ rp409 (q/29) (Nat.zero_le _) (by omega) (eq.symm ▸ hq) (eq.symm ▸ hlt)
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%29=28 at hh
      have eq: 29*(q/29)+28=q:= by omega
      exact eq ▸ rp420 (q/29) (Nat.zero_le _) (by omega) (eq.symm ▸ hq) (eq.symm ▸ hlt)
  · have h2:=Nat.pow_le_pow_right hq.pos (show 2 ≤ f by omega)
    have ha: q < 159:= by by_contra! hh; have:=Nat.pow_le_pow_left hh 2; omega
    have hb: f < 15:= by by_contra! hh; have:=(Nat.pow_le_pow_left hq.two_le 15).trans (Nat.pow_le_pow_right hq.pos hh); omega
    have hqtab:=List.all_eq_true.mp powTab29 q (List.mem_range.mpr ha)
    exact rp475 (List.all_eq_true.mp hqtab f (List.mem_range.mpr hb)) hq (by omega) hlt hs
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cover31 (q f: ℕ) (hq: q.Prime) (hf: 0 < f) (hlt: q^f < 82161) (hh: q = 31 ∨ (q: ZMod 31)^(f*2)=1) : covers rows31 q (q^f):= by
  letI: Fact (Nat.Prime 31):=⟨by decide⟩
  have hle:=Nat.le_self_pow hf.ne' q
  rcases hh with rfl | hs
  · obtain ⟨r,hr,hv⟩:=List.any_eq_true.mp (show covers rows31 31 31 by decide +kernel)
    obtain ⟨hd,hN⟩:=of_decide_eq_true hv
    exact List.any_eq_true.mpr ⟨r,hr,decide_eq_true (And.intro hd (hN.trans hle))⟩
  by_cases h1: f = 1
  · subst f; rw [pow_one] at hlt ⊢; rw [one_mul] at hs
    rcases sq_eq_one_iff.mp hs with h|h
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%31=1 at hh
      have eq: 31*(q/31)+1=q:= by omega
      exact eq ▸ rp447 (q/31) (Nat.zero_le _) (by omega) (eq.symm ▸ hq) (eq.symm ▸ hlt)
    · have hh:=congrArg ZMod.val h; rw [ZMod.val_natCast] at hh; change q%31=30 at hh
      have eq: 31*(q/31)+30=q:= by omega
      exact eq ▸ rp474 (q/31) (Nat.zero_le _) (by omega) (eq.symm ▸ hq) (eq.symm ▸ hlt)
  · have h2:=Nat.pow_le_pow_right hq.pos (show 2 ≤ f by omega)
    have ha: q < 287:= by by_contra! hh; have:=Nat.pow_le_pow_left hh 2; omega
    have hb: f < 17:= by by_contra! hh; have:=(Nat.pow_le_pow_left hq.two_le 17).trans (Nat.pow_le_pow_right hq.pos hh); omega
    have hqtab:=List.all_eq_true.mp powTab31 q (List.mem_range.mpr ha)
    exact rp475 (List.all_eq_true.mp hqtab f (List.mem_range.mpr hb)) hq (by omega) hlt hs
end SReg.Cert.OneTable
end

section
noncomputable section
open Perfection PadicInt IsLocalRing
namespace KummerCriterion
variable (p: ℕ) [hp: Fact p.Prime]
noncomputable def rp0: ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField
instance maximalIdealQuotient_charP: CharP (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) p :=
  charP_of_injective_ringHom (f:=(rp0 p).symm.toRingHom)
    (rp0 p).symm.injective p
instance maximalIdealQuotient_finite: Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
  Finite.of_equiv _ (rp0 p).symm.toEquiv
noncomputable def rp1: ZMod p →*₀ ℤ_[p] :=
  (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])).comp <|
    (PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv.toRingHom.toMonoidWithZeroHom.comp
      (rp0 p).symm.toRingHom.toMonoidWithZeroHom
variable {p}
@[simp]
lemma rp2: rp1 p 0 = 0:=map_zero _
@[simp]
lemma rp3 (a: ZMod p) : PadicInt.toZMod (rp1 p a) = a:= by
  change PadicInt.toZMod
    (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])
      ((PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv
        ((rp0 p).symm a))) = a
  rw [PadicInt.toZMod_eq_residueField_comp_residue,RingHom.comp_apply]
  change PadicInt.residueField (Ideal.Quotient.mk _ _) = a
  rw [Perfection.mk_teichmuller₀,PerfectionMap.comp_equiv]
  exact (rp0 p).apply_symm_apply a
lemma rp4 {a: ZMod p} (ha: a ≠ 0) : rp1 p a ^ (p - 1) = 1:= by
  rw [← map_pow,ZMod.pow_card_sub_one_eq_one ha,map_one]
lemma rp5: Function.Injective (rp1 p):=fun _ _ hab => by
  simpa using congrArg PadicInt.toZMod hab
lemma rp6 (a: ZMod p) : rp1 p a ^ p = rp1 p a:= by
  rw [← map_pow,ZMod.pow_card]
lemma rp7 (a: ZMod p) :
    rp1 p a ≡ (a.val: ℤ_[p]) ^ p [SMOD (maximalIdeal ℤ_[p]) ^ 2]:= by
  have h_base: rp1 p a ≡ (a.val: ℤ_[p]) [SMOD maximalIdeal ℤ_[p]]:= by
    rw [SModEq.sub_mem,← ker_toZMod,RingHom.mem_ker,map_sub,rp3,
      map_natCast,ZMod.natCast_val,ZMod.cast_id,sub_self]
  have hp_mem: ((p: ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p]:= by
    rw [maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  have h_pow:=h_base.pow_pow_add_one hp_mem 1
  rwa [pow_one,rp6] at h_pow
lemma rp8 (a: ZMod p) :
    rp1 p a - (a.val: ℤ_[p]) ^ p ∈ (maximalIdeal ℤ_[p]) ^ 2 :=
  SModEq.sub_mem.mp (rp7 a)
noncomputable def rp9 (p: ℕ) [Fact p.Prime] : DirichletCharacter ℤ_[p] p where
  toFun:=rp1 p
  map_one':=map_one _
  map_mul':=map_mul _
  map_nonunit':=fun a ha => by
    rw [show a = 0 from by_contra fun hne => ha (isUnit_iff_ne_zero.mpr hne),rp2]
@[simp]
lemma rp10 (a: ZMod p) : rp9 p a = rp1 p a:=rfl
lemma rp11 {g: (ZMod p)ˣ}
    (hg_gen: ∀ x: (ZMod p)ˣ,x ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (rp1 p (g: ZMod p)) (p - 1):= by
  refine ⟨?_,fun l hl => ?_⟩
  · rw [← map_pow,← Units.val_pow_eq_pow_val,ZMod.units_pow_card_sub_one_eq_one,
      Units.val_one,map_one]
  · have h_units: g ^ l = 1:=Units.ext <| by
      rw [Units.val_pow_eq_pow_val,Units.val_one]
      exact rp5 (by rwa [map_pow,map_one])
    have h_order: orderOf g = p - 1:= by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen,Nat.card_eq_fintype_card,ZMod.card_units]
    rw [← h_order]; exact orderOf_dvd_of_pow_eq_one h_units
lemma rp12: (rp9 p) ^ (p - 1) = 1:= by
  ext a
  rw [MulChar.pow_apply_coe,rp10,MulChar.one_apply_coe]
  exact rp4 a.ne_zero
lemma rp13: orderOf (rp9 p) = p - 1:= by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (rp12 (p:=p))) ?_
  obtain ⟨g,hg_gen⟩:=IsCyclic.exists_generator (α:=(ZMod p)ˣ)
  have h_apply:=congrArg (fun χ: DirichletCharacter ℤ_[p] p => χ (g: ZMod p))
    (pow_orderOf_eq_one (rp9 p))
  simp only [MulChar.pow_apply_coe,rp10,MulChar.one_apply_coe] at h_apply
  exact (rp11 hg_gen).2 _ h_apply
lemma rp14 (hp_odd: p ≠ 2) : rp1 p (-1) = -1:= by
  have h_sq: rp1 p (-1: ZMod p) ^ 2 = 1:= by
    rw [sq,← map_mul,neg_one_mul,neg_neg,map_one]
  rcases sq_eq_one_iff.mp h_sq with h1 | h_neg
  · have: Fact (2 < p):=⟨lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)⟩
    exact absurd (by simpa using congrArg PadicInt.toZMod h1) ZMod.neg_one_ne_one
  · exact h_neg
lemma rp15 (hp_odd: p ≠ 2) (i: ℕ) :
    ((rp9 p) ^ i) (-1: ZMod p) = (-1: ℤ_[p]) ^ i:= by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero,pow_zero]; exact MulChar.one_apply isUnit_one.neg
  · rw [MulChar.pow_apply' _ hi.ne',rp10,rp14 hp_odd]
end KummerCriterion
end

section
open KummerCriterion PadicInt IsLocalRing
namespace FiniteMinus
variable (p: ℕ) [hp: Fact p.Prime]
lemma rp16 (a: ZMod p) : toZModPow 2 (rp1 p a) = (a.val: ZMod (p^2)) ^ p:= by
  have h:=rp8 a
  rw [maximalIdeal_eq_span_p,Ideal.span_singleton_pow,← ker_toZModPow,RingHom.mem_ker,map_sub,sub_eq_zero,map_pow,map_natCast] at h
  exact h
noncomputable def weighted (j: ℕ) : ℤ_[p]:=∑ a ∈ Finset.range p,(a: ℤ_[p]) * (rp1 p (a: ZMod p))^j
def residue (p j: ℕ) : ZMod (p^2):=∑ a ∈ Finset.range p,(a: ZMod (p^2)) * ((a: ZMod (p^2))^p)^j
lemma rp17 (j: ℕ) : toZModPow 2 (weighted p j) = residue p j:= by
  unfold weighted residue
  rw [map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp [rp16,ZMod.val_natCast,Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
end FiniteMinus
end

section
namespace FiniteMinus
def primes: List ℕ:=[3,5,7,11,13,17,19,23,29,31]
def good (p j: ℕ) : Prop:=let r:=(residue p j).val; r ≠ 0 ∧ (p ∣ r ↔ j + 2 ≠ p)
instance (p j: ℕ) : Decidable (good p j):= by unfold good; infer_instance
set_option maxRecDepth 10000 in
lemma table: ∀ p ∈ primes,∀ j: Fin 30,j.val < p-1 → j.val % 2 = 1 → good p j.val:= by decide +kernel
theorem actual (p j: ℕ) [Fact p.Prime] (hp: p ∈ primes) (hj: j < p-1) (ho: j%2=1) :
    let r:=(PadicInt.toZModPow 2 (weighted p j)).val; r ≠ 0 ∧ (p ∣ r ↔ j+2 ≠ p):= by
  have hh: ∀ x ∈ primes,x ≤ 31:= by decide
  have:=hh p hp
  simpa [rp17,good] using table p hp ⟨j,by omega⟩ hj ho
end FiniteMinus
end

section
noncomputable section
open Polynomial
namespace KummerCriterion
variable {N: ℕ} {R: Type*} [CommRing R] [Algebra ℚ R]
noncomputable def rp18 [NeZero N]
    (χ: DirichletCharacter R N) (n: ℕ) : R :=
  (N: R) ^ (n - 1) *
    ∑ a: ZMod N,χ a *
      algebraMap ℚ R ((Polynomial.bernoulli n).eval ((a.val: ℚ) / N))
lemma rp19 [IsDomain R] [NeZero N]
    {χ: DirichletCharacter R N} (hχ: χ ≠ 1) :
    rp18 χ 1 =
      ∑ a: ZMod N,χ a * algebraMap ℚ R ((a.val: ℚ) / N):= by
  unfold rp18
  rw [show (1 - 1: ℕ) = 0 from rfl,pow_zero,one_mul,Polynomial.bernoulli_one]
  simp_rw [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,map_sub,mul_sub]
  rw [Finset.sum_sub_distrib]
  conv_lhs =>
    rw [show (∑ a: ZMod N,χ a * algebraMap ℚ R (2⁻¹: ℚ))
          = algebraMap ℚ R (2⁻¹: ℚ) * ∑ a: ZMod N,χ a from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _]
  rw [MulChar.sum_eq_zero_of_ne_one hχ,mul_zero,sub_zero]
lemma rp20 [IsDomain R] [NeZero N]
    {χ: DirichletCharacter R N} (hχ: χ ≠ 1) :
    (N: R) * rp18 χ 1 =
      ∑ a: ZMod N,χ a * (a.val: R):= by
  rw [rp19 hχ,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hN_R: (N: R) = algebraMap ℚ R (N: ℚ):= by push_cast; rfl
  rw [hN_R,show algebraMap ℚ R ((N: ℚ)) * (χ a * algebraMap ℚ R ((a.val: ℚ) / N)) =
        χ a * (algebraMap ℚ R (N: ℚ) * algebraMap ℚ R ((a.val: ℚ) / N)) from by ring,
    ← map_mul,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  push_cast; rfl
noncomputable def rp21 (p: ℕ) [Fact p.Prime] : DirichletCharacter ℚ_[p] p :=
  (rp9 p).ringHomComp PadicInt.Coe.ringHom
variable (p: ℕ) [Fact p.Prime]
lemma rp22 (n: ℕ) :
    (rp21 p) ^ n =
      ((rp9 p) ^ n).ringHomComp PadicInt.Coe.ringHom:= by
  simpa [rp21] using
    (MulChar.ringHomComp_pow (χ:=rp9 p) (f:=PadicInt.Coe.ringHom) (n:=n))
lemma rp23 :
    (rp21 p) ^ (p - 1) = 1:= by
  rw [rp22 (p:=p) (n:=p - 1)]
  simp [rp12 (p:=p)]
lemma rp24 :
    orderOf (rp21 p) = p - 1:= by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (rp23 (p:=p))) ?_
  have hpowQ' :
      ((rp9 p) ^ orderOf (rp21 p)).ringHomComp
          PadicInt.Coe.ringHom = 1:= by
    rw [← rp22 (p:=p) (n:=orderOf (rp21 p))]
    simp only [pow_orderOf_eq_one]
  have hpowZ: (rp9 p) ^ orderOf (rp21 p) = 1 :=
    (MulChar.ringHomComp_eq_one_iff (f:=PadicInt.Coe.ringHom)
      (hf:=fun _ _ h => Subtype.coe_injective h)).mp hpowQ'
  simpa [rp13 (p:=p)] using orderOf_dvd_of_pow_eq_one hpowZ
lemma rp25 (n: ℕ) :
    (rp21 p) ^ n = 1 ↔ (p - 1) ∣ n:= by
  refine ⟨fun hpow => ?_,?_⟩
  · simpa [rp24 (p:=p)] using orderOf_dvd_of_pow_eq_one hpow
  · rintro ⟨m,rfl⟩
    rw [← rp24 (p:=p),pow_mul,pow_orderOf_eq_one,one_pow]
lemma rp26 {n: ℕ} (hn: ¬ (p - 1) ∣ n) :
    (rp21 p) ^ n ≠ 1 :=
  fun hpow => hn ((rp25 (p:=p) n).mp hpow)
end KummerCriterion
end

section
open KummerCriterion
namespace FiniteMinus
lemma indexSum (p: ℕ) [Fact p.Prime] {R: Type*} [AddCommMonoid R] (g: ZMod p → R) : (∑ a: ZMod p,g a) = ∑ a ∈ Finset.range p,g a:= by
  cases p with
  | zero => have he: Nat.Prime 0:=Fact.out; exact (Nat.not_prime_zero he).elim
  | succ n => rw [← Fin.sum_univ_eq_sum_range]; apply Finset.sum_congr rfl; intro i _; congr 1; apply Fin.ext; exact (Nat.mod_eq_of_lt i.isLt).symm
lemma rp27 (p j: ℕ) [Fact p.Prime] (h0: 0 < j) (hj: j < p-1) : (p: ℚ_[p]) * rp18 ((rp21 p)^j) 1 = (weighted p j: ℚ_[p]):= by
  rw [rp20 (rp26 p (Nat.not_dvd_of_pos_of_lt h0 hj)),indexSum,weighted,PadicInt.coe_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [MulChar.pow_apply' _ h0.ne',ZMod.val_natCast,Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
  change ((rp1 p (a: ZMod p) : ℤ_[p]) : ℚ_[p])^j * a = _
  simp [mul_comm]
end FiniteMinus
end

section
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section GaussSum
variable (p: ℕ) [hp: Fact p.Prime]
theorem rp28
    {χ: DirichletCharacter ℂ p} (hχ: χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar (N:=p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) =
      χ (-1) * p:= by
  have h_prim: (ZMod.stdAddChar: AddChar (ZMod p) ℂ).IsPrimitive :=
    ZMod.isPrimitive_stdAddChar p
  have h_card: (Fintype.card (ZMod p) : ℂ) = p:= by
    rw [ZMod.card]
  have h1: gaussSum χ (ZMod.stdAddChar (N:=p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹ = (p: ℂ):= by
    rw [← h_card]; exact gaussSum_mul_gaussSum_eq_card hχ h_prim
  have h2:=mul_gaussSum_inv_eq_gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))
  have h_neg_unit: IsUnit (-1: ZMod p):=isUnit_one.neg
  have h_sq: χ (-1) * χ (-1) = 1:= by
    rw [← map_mul,show (-1: ZMod p) * -1 = 1 from by ring,MulChar.map_one]
  have h_ne: χ (-1) ≠ 0:=fun h => by
    rw [h,mul_zero] at h_sq; exact zero_ne_one h_sq
  have h_inv_neg_one: χ⁻¹ (-1) = χ (-1):= by
    have h_inv_mul: χ⁻¹ (-1) * χ (-1) = 1:= by
      rw [← MulChar.mul_apply,MulChar.inv_mul,MulChar.one_apply h_neg_unit]
    exact mul_right_cancel₀ h_ne (h_inv_mul.trans h_sq.symm)
  rw [h_inv_neg_one] at h2
  have h3: χ (-1) * (gaussSum χ (ZMod.stdAddChar (N:=p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹) = χ (-1) * p:= by rw [h1]
  rw [show χ (-1) * (gaussSum χ (ZMod.stdAddChar (N:=p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹) =
      gaussSum χ (ZMod.stdAddChar (N:=p)) *
        (χ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹) from by ring,h2] at h3
  exact h3
theorem DirichletCharacter.isPrimitive_of_ne_one
    {χ: DirichletCharacter ℂ p} (hχ: χ ≠ 1) : χ.IsPrimitive:= by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.factorsThrough_one_iff χ).mp
      (h ▸ χ.factorsThrough_conductor)) hχ
  · exact h
end GaussSum
end KummerCriterion
end

section
noncomputable section
namespace KummerCriterion
section SignInvariant
open scoped BigOperators ComplexConjugate
variable (p: ℕ) [hp: Fact p.Prime]
@[simp] theorem dirichletCharacter_apply_zero (χ: DirichletCharacter ℂ p) :
    χ (0: ZMod p) = 0 :=
  MulChar.map_zero χ
end SignInvariant
end KummerCriterion
noncomputable section
namespace KummerCriterion
section SignInvariant
open scoped BigOperators ComplexConjugate
variable (p: ℕ) [hp: Fact p.Prime]
local instance: DecidableEq (DirichletCharacter ℂ p):=Classical.decEq _
local instance: DecidableEq (Option (DirichletCharacter ℂ p)):=Classical.decEq _
end SignInvariant
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped NumberField
namespace IsPrimitiveRoot
noncomputable def unit' {K: Type*} [Field K] [CharZero K] {ζ: K} {k: ℕ}
    [NeZero k] (hζ: IsPrimitiveRoot ζ k) : (𝓞 K)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne k)).unit
lemma rp29 {K: Type*} [Field K] [CharZero K] {ζ: K} {k: ℕ}
    [NeZero k] (hζ: IsPrimitiveRoot ζ k) : IsPrimitiveRoot (hζ.unit' : 𝓞 K) k :=
  hζ.toInteger_isPrimitiveRoot
lemma rp30 {K: Type*} [Field K] [CharZero K] {ζ: K} {k: ℕ}
    [NeZero k] (hζ: IsPrimitiveRoot ζ k) : hζ.unit' ^ k = 1 :=
  Units.ext hζ.toInteger_isPrimitiveRoot.pow_eq_one
lemma rp31 {A: Type*} [CommRing A] [IsDomain A] {ζ μ: A} {k: ℕ}
    [NeZero k] (hζ: IsPrimitiveRoot ζ k) (hμ: μ ^ k = 1) :
    algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A)) μ = 1:= by
  obtain ⟨i,-,hi⟩:=hζ.eq_pow_of_pow_eq_one hμ
  rw [← hi,map_pow]
  have hζ_mod: algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A)) ζ = 1:= by
    rw [← map_one (algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A))),← sub_eq_zero,
      ← map_sub,Ideal.Quotient.algebraMap_eq,Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hζ_mod,one_pow]
end IsPrimitiveRoot
end
end

section
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p: ℕ) [hp: Fact p.Prime] (hp_odd: p ≠ 2)
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem rp32 :
    ((zeta_spec p ℚ K).toInteger: 𝓞 K) ^ p = 1 :=
  (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
theorem rp33 :
    ((zeta_spec p ℚ K).toInteger: 𝓞 K) ^ (p - 1) *
      ((zeta_spec p ℚ K).toInteger: 𝓞 K) = 1:= by
  rw [← pow_succ,Nat.sub_one_add_one hp.1.ne_zero]
  exact rp32 p K
noncomputable def rp34: Ideal (𝓞 K) :=
  Ideal.span {((zeta_spec p ℚ K).toInteger - 1: 𝓞 K)}
instance zetaPrime_isPrime: (rp34 p K).IsPrime :=
  (Ideal.span_singleton_prime
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero).mpr
    (zeta_spec p ℚ K).zeta_sub_one_prime'
theorem rp35: rp34 p K ≠ ⊥:= by
  rw [rp34,Ne,Ideal.span_singleton_eq_bot]
  exact (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
noncomputable def rp36 [IsCMField K] : Ideal (𝓞 ((NumberField.maximalRealSubfield K))) :=
  (rp34 p K).under (𝓞 ((NumberField.maximalRealSubfield K)))
instance [IsCMField K] : (rp36 p K).IsPrime :=
  Ideal.IsPrime.under _ _
instance [IsCMField K] : (rp34 p K).LiesOver (rp36 p K) :=
  Ideal.over_under _
lemma rp37 [IsCMField K] :
    (ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger: 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger: 𝓞 K) ^ (p - 1):= by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hzeta_torsion: hζ.unit' ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨p,hp.1.pos,hζ.rp30⟩)
  have hconj:=unitsComplexConj_torsion (K:=K) ⟨hζ.unit',hzeta_torsion⟩
  have h1: (unitsComplexConj K hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹: (𝓞 K)ˣ) :=
    congrArg ((↑·) : (𝓞 K)ˣ → 𝓞 K) hconj
  have h2: (hζ.unit'⁻¹: (𝓞 K)ˣ) = hζ.unit' ^ (p - 1):= by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ,Nat.sub_one_add_one hp.1.ne_zero]
    ext; push_cast; exact hζ.pow_eq_one
  rw [show (ringOfIntegersComplexConj K hζ.toInteger: 𝓞 K) =
    (unitsComplexConj K hζ.unit' : 𝓞 K) from rfl,h1,h2,Units.val_pow_eq_pow_val]
  rfl
theorem rp38 [IsCMField K] (x: 𝓞 K) :
    (ringOfIntegersComplexConj K x: 𝓞 K) - x ∈ rp34 p K:= by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have htop: Algebra.adjoin ℤ {hζ.toInteger} = ⊤ :=
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ
  have hx: x ∈ Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 K)):=htop ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    have hp_pow: hζ.toInteger ^ p = 1:=rp32 p K
    have hc_pow: (ringOfIntegersComplexConj K hζ.toInteger) ^ p = 1:= by
      rw [← map_pow,hp_pow,map_one]
    have hmem_of_pow: ∀ μ: 𝓞 K,μ ^ p = 1 → μ - 1 ∈ rp34 p K:= by
      intro μ hμ
      have h1:=hζ.rp29.rp31 hμ
      have h2: (algebraMap (𝓞 K)
          (𝓞 K ⧸ Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)))) (μ - 1) = 0:= by
        rw [map_sub,h1,map_one,sub_self]
      rw [Ideal.Quotient.algebraMap_eq,Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    have h1: (hζ.toInteger: 𝓞 K) - 1 ∈ rp34 p K:=hmem_of_pow _ hp_pow
    have h2: (ringOfIntegersComplexConj K hζ.toInteger: 𝓞 K) - 1 ∈ rp34 p K :=
      hmem_of_pow _ hc_pow
    have: (ringOfIntegersComplexConj K hζ.toInteger: 𝓞 K) - hζ.toInteger =
        ((ringOfIntegersComplexConj K hζ.toInteger: 𝓞 K) - 1) -
          (hζ.toInteger - 1):= by ring
    rw [this]
    exact Ideal.sub_mem _ h2 h1
  | algebraMap r =>
    have: ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) r) =
        (algebraMap ℤ (𝓞 K)) r:= by
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K),AlgEquiv.commutes]
    rw [this,sub_self]
    exact Ideal.zero_mem _
  | add x y _ _ hpx hpy =>
    have: (ringOfIntegersComplexConj K (x + y) : 𝓞 K) - (x + y) =
        ((ringOfIntegersComplexConj K x: 𝓞 K) - x) +
          ((ringOfIntegersComplexConj K y: 𝓞 K) - y):= by
      push_cast [map_add]; ring
    rw [this]
    exact Ideal.add_mem _ hpx hpy
  | mul x y _ _ hpx hpy =>
    have: (ringOfIntegersComplexConj K (x * y) : 𝓞 K) - (x * y) =
        ((ringOfIntegersComplexConj K x: 𝓞 K) - x) *
            (ringOfIntegersComplexConj K y: 𝓞 K) +
          x * ((ringOfIntegersComplexConj K y: 𝓞 K) - y):= by
      push_cast [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ hpx)
      (Ideal.mul_mem_left _ _ hpy)
lemma rp39 [IsCMField K] :
    ((zeta_spec p ℚ K).toInteger - 1: 𝓞 K) *
      ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1) =
      -((zeta_spec p ℚ K).toInteger ^ (p - 1)) *
        ((zeta_spec p ℚ K).toInteger - 1) ^ 2:= by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hc_pi: (ringOfIntegersComplexConj K (hζ.toInteger - 1) : 𝓞 K) =
      hζ.toInteger ^ (p - 1) - 1:= by
    rw [map_sub,map_one,rp37]
  have hpow_succ: hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 :=
    rp33 p K
  rw [hc_pi]
  linear_combination (hζ.toInteger - 1) * hpow_succ
lemma rp40 [IsCMField K] :
    ringOfIntegersComplexConj K
        (((zeta_spec p ℚ K).toInteger - 1) *
          ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1)) =
      ((zeta_spec p ℚ K).toInteger - 1) *
        ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1):= by
  rw [map_mul,mul_comm]
  congr 1
  ext
  exact complexConj_apply_apply K _
noncomputable def piPlus [IsCMField K] : 𝓞 ((NumberField.maximalRealSubfield K)):= by
  have hfix:=rp40 p K
  rw [RingOfIntegers.ext_iff,coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  exact hfix.choose
lemma rp41 [IsCMField K] :
    (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) (piPlus p K) =
      ((zeta_spec p ℚ K).toInteger - 1: 𝓞 K) *
        ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1):= by
  have hfix:=rp40 p K
  rw [RingOfIntegers.ext_iff,coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  ext
  rw [← hfix.choose_spec]; rfl
theorem rp42 [IsCMField K] :
    (Ideal.span {piPlus p K}).map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) =
      rp34 p K ^ 2:= by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hζ_unit: IsUnit ((hζ.unit' : 𝓞 K) ^ (p - 1)):=(hζ.unit'.isUnit.pow _)
  have hneg_unit: IsUnit (-(hζ.toInteger: 𝓞 K) ^ (p - 1)):= by
    rw [show (hζ.toInteger: 𝓞 K) = (hζ.unit' : 𝓞 K) from rfl]
    exact hζ_unit.neg
  rw [Ideal.map_span,Set.image_singleton,rp41,
    rp39,rp34,Ideal.span_singleton_pow,
    show -(hζ.toInteger: 𝓞 K) ^ (p - 1) * ((hζ.toInteger - 1) ^ 2) =
        ((hζ.toInteger - 1) ^ 2) * -(hζ.toInteger) ^ (p - 1) from by ring,
    Ideal.span_singleton_mul_right_unit hneg_unit]
include hp_odd in
theorem rp43 [IsCMField K]
    (x: 𝓞 ((NumberField.maximalRealSubfield K))) (hx: x ≠ 0) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger - 1: 𝓞 K)
                      (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) x)):= by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  set α:=algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) x with hα_def
  have hα: α ≠ 0:=(map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hx
  have hπ_prime: Prime (hζ.toInteger - 1: 𝓞 K):=hζ.zeta_sub_one_prime'
  have hfin: FiniteMultiplicity (hζ.toInteger - 1: 𝓞 K) α :=
    FiniteMultiplicity.of_prime_left hπ_prime hα
  obtain ⟨u,hαu,hπ_nd_u⟩:=hfin.exists_eq_pow_mul_and_not_dvd
  set e:=multiplicity (hζ.toInteger - 1: 𝓞 K) α with he_def
  have hcα: ringOfIntegersComplexConj K α = α :=
    (ringOfIntegersComplexConj K).commutes x
  have hc_pi: ringOfIntegersComplexConj K (hζ.toInteger - 1) =
      -hζ.toInteger ^ (p - 1) * (hζ.toInteger - 1):= by
    rw [map_sub,map_one,rp37]
    linear_combination rp33 p K
  have hcα_expand: (-hζ.toInteger ^ (p - 1) * (hζ.toInteger - 1) : 𝓞 K) ^ e *
      ringOfIntegersComplexConj K u = (hζ.toInteger - 1) ^ e * u:= by
    have:=hcα
    rw [hαu,map_mul,map_pow,hc_pi] at this
    exact this
  have hπ_ne: (hζ.toInteger - 1: 𝓞 K) ≠ 0:=hπ_prime.ne_zero
  have hcu_eq: ((-hζ.toInteger ^ (p - 1)) ^ e: 𝓞 K) * ringOfIntegersComplexConj K u = u:= by
    have hreord: ((hζ.toInteger - 1) ^ e: 𝓞 K) *
        (((-hζ.toInteger ^ (p - 1)) ^ e) * ringOfIntegersComplexConj K u) =
        ((hζ.toInteger - 1) ^ e: 𝓞 K) * u:= by
      have hsplit: ((-hζ.toInteger ^ (p - 1) * (hζ.toInteger - 1)) ^ e: 𝓞 K) =
          ((hζ.toInteger - 1) ^ e) * (((-hζ.toInteger ^ (p - 1)) ^ e)):= by
        rw [mul_pow]; ring
      rw [← hcα_expand,hsplit,mul_assoc]
    exact mul_left_cancel₀ (pow_ne_zero _ hπ_ne) hreord
  have hres: (ringOfIntegersComplexConj K u: 𝓞 K) - u ∈ rp34 p K :=
    rp38 p K u
  have hpow_sub: ∀ n: ℕ,(hζ.toInteger ^ n - 1: 𝓞 K) ∈ rp34 p K:= by
    intro n
    rw [rp34,Ideal.mem_span_singleton]
    have:=sub_dvd_pow_sub_pow hζ.toInteger (1: 𝓞 K) n
    rwa [one_pow] at this
  have hneg_pow_sub: ((-hζ.toInteger ^ (p - 1)) ^ e - (-1) ^ e: 𝓞 K) ∈ rp34 p K:= by
    have key: ((-hζ.toInteger ^ (p - 1)) ^ e - (-1) ^ e: 𝓞 K) =
        (-1) ^ e * (hζ.toInteger ^ ((p - 1) * e) - 1):= by
      rw [neg_pow,← pow_mul]; ring
    rw [key]
    exact Ideal.mul_mem_left _ _ (hpow_sub _)
  have hkey: ((1 - (-1) ^ e) * u: 𝓞 K) ∈ rp34 p K:= by
    have h1: ((-hζ.toInteger ^ (p - 1)) ^ e: 𝓞 K) * ringOfIntegersComplexConj K u -
        (-1) ^ e * u ∈ rp34 p K:= by
      have h1a: ((-hζ.toInteger ^ (p - 1)) ^ e: 𝓞 K) * ringOfIntegersComplexConj K u -
          (-1) ^ e * u =
          (((-hζ.toInteger ^ (p - 1)) ^ e - (-1) ^ e) * ringOfIntegersComplexConj K u) +
          ((-1) ^ e) * (ringOfIntegersComplexConj K u - u):= by ring
      rw [h1a]
      exact Ideal.add_mem _
        (Ideal.mul_mem_right _ _ hneg_pow_sub)
        (Ideal.mul_mem_left _ _ hres)
    rw [hcu_eq] at h1
    convert h1 using 1
    ring
  rcases Nat.even_or_odd e with he | he
  · exact he
  · exfalso
    have hp2: 2 < p:=lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
    have h_two_u: (2 * u: 𝓞 K) ∈ rp34 p K:= by
      convert hkey using 2
      rw [Odd.neg_one_pow he]; ring
    have h_prime:=zetaPrime_isPrime p K
    rcases h_prime.mem_or_mem h_two_u with h | h
    · exact IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' p (zeta_spec p ℚ K) hp2 h
    · rw [rp34,Ideal.mem_span_singleton] at h
      exact hπ_nd_u h
include hp_odd in
theorem rp44 [IsCMField K] :
    (rp36 p K).map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) = (rp34 p K) ^ 2:= by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [rp36] at hy
    rw [Ideal.mem_comap,rp34,Ideal.mem_span_singleton] at hy
    by_cases hy0: y = 0
    · simp [hy0]
    have heven:=rp43 p hp_odd K y hy0
    have hfin: FiniteMultiplicity
        ((zeta_spec p ℚ K).toInteger - 1: 𝓞 K)
        (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) y) :=
      FiniteMultiplicity.of_prime_left (zeta_spec p ℚ K).zeta_sub_one_prime'
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hy0)
    have hge: 1 ≤ multiplicity ((zeta_spec p ℚ K).toInteger - 1: 𝓞 K)
        (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) y) :=
      hfin.pow_dvd_iff_le_multiplicity.mp (by rwa [pow_one])
    have h2le: 2 ≤ multiplicity ((zeta_spec p ℚ K).toInteger - 1: 𝓞 K)
        (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) y):= by
      rcases heven with ⟨k,hk⟩
      omega
    rw [Ideal.mem_comap,show (rp34 p K) ^ 2 =
        Ideal.span {((zeta_spec p ℚ K).toInteger - 1: 𝓞 K) ^ 2} from
      by rw [rp34,Ideal.span_singleton_pow],Ideal.mem_span_singleton]
    exact hfin.pow_dvd_iff_le_multiplicity.mpr h2le
  · rw [← rp42 p K]
    refine Ideal.map_mono ?_
    rw [Ideal.span_singleton_le_iff_mem]
    rw [rp36,Ideal.mem_comap,rp34,rp41,
      Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
end CyclotomicSetup
end KummerCriterion
end
end

section
variable {p: ℕ} [NeZero p] {K: Type*} [Field K]
variable {ζ: K} (hζ: IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open IsCyclotomicExtension NumberField Polynomial IsCMField
noncomputable section
theorem rp45 {A: Type*} [CommRing A] {t: A} :
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1:= by
  rw [← map_one <| algebraMap A <| A ⧸ Ideal.span ({t - 1} : Set A),← sub_eq_zero,← map_sub,
    Ideal.Quotient.algebraMap_eq,Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)
theorem rp46 {A B: Type*} [CommRing A] [CommRing B] (F: A →+* B) {u l: A} (hu: F u = 1) {t: ℕ} (f: Fin t → ℤ) (h: ∑ x,f x • u ^ (x: ℕ) = l) : F l = ∑ x,(f x: B):= by
  rw [← h,map_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp [zsmul_eq_mul,hu]
theorem aux {t} {l: 𝓞 K} {f: Fin t → ℤ} {μ: K} (hμ: IsPrimitiveRoot μ p)
    (h: ∑ x: Fin t,f x • (⟨μ,hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) ^ (x: ℕ) = l) :
    algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) l = ∑ x: Fin t,(f x: 𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))):= by
  have: (⟨μ,hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) ^ p = 1:= by
    ext
    push_cast
    exact hμ.pow_eq_one
  obtain ⟨k,-,hk⟩:=hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one this
  have: algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (⟨μ,hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) = 1:= by
    rw [← hk,map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K)) ^ k = 1
    rw [rp45,one_pow]
  exact rp46 _ this f h
variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem rp47 (hpo: Odd p) (x: K)
    (h: ∃ (n: ℕ) (_: 0 < n),x ^ n = 1) :
    ∃ (m k: ℕ),x = (-1) ^ k * (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit).1: K) ^ m:= by
  obtain ⟨n,hn,hxn⟩:=h
  have hη: (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit).1: K) = ζ:= by rw [IsUnit.unit_spec]; rfl
  simp only [hη]
  obtain ⟨r,-,hr | hr⟩:=hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hxn⟩)
  · exact ⟨r,2,by simp [hr]⟩
  · exact ⟨r,1,by simp [hr]⟩
lemma rp48 (u: (𝓞 K)ˣ) [Fact (p.Prime)] (hp: 2 < p) :
    haveI:=IsCyclotomicExtension.Rat.isCMField (S:={p}) K ⟨p,rfl,hp⟩
    algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (unitsMulComplexConjInv K u).1 = 1:= by
  have:=IsCyclotomicExtension.Rat.isCMField (S:={p}) K ⟨p,rfl,hp⟩
  have:=Units.coe_map_inv (N:=𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))) (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply,Units.val_mul,map_mul,← MonoidHom.coe_coe,← this,
    Units.mul_inv_eq_one,Units.coe_map,MonoidHom.coe_coe]
  have:=Fact.mk hp
  have hu:=hζ.integralPowerBasis.basis.sum_repr u
  let a:=hζ.integralPowerBasis.basis.repr
  let φn:=hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow,IsPrimitiveRoot.integralPowerBasis_gen] at hu
  have hu':=congr_arg (ringOfIntegersComplexConj K) hu
  replace hu' : ∑ x: Fin φn,(a u) x • (ringOfIntegersComplexConj K)
      (hζ.toInteger ^ (x: ℕ)) = unitsComplexConj K u:= by
    refine Eq.trans ?_ hu'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have: ∀ x: Fin φn,ringOfIntegersComplexConj K (hζ.toInteger ^ (x: ℕ)) =
      hζ.inv.toInteger ^ (x: ℕ):= by
    intro x
    ext
    simp only [map_pow,coe_ringOfIntegersComplexConj]
    suffices ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ∈ Units.torsion K by
      have H:=RingOfIntegers.ext_iff.1 <|
        Units.ext_iff.1 <| unitsComplexConj_torsion K ⟨((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit),‹_›⟩
      have: ↑↑((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) = ζ:=rfl
      simp only [Units.coe_mapEquiv,RingEquiv.coe_toMulEquiv,RingOfIntegers.mapRingEquiv_apply,
        this,AlgEquiv.coe_ringEquiv,InvMemClass.coe_inv,map_units_inv] at H
      change (complexConj K) ζ ^ (x: ℕ) = ζ⁻¹ ^ (x: ℕ)
      rw [H]
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p,by lia,?_⟩)
    ext
    exact hζ.pow_eq_one
  conv_lhs at hu' =>
    congr
    congr
    ext a
    rw [this a]
  exact (aux hζ hζ hu).trans (aux hζ hζ.inv hu').symm
theorem rp49 (u: (𝓞 K)ˣ) (n: ℕ) [Fact (p.Prime)] (hp: 2 < p) :
    haveI:=IsCyclotomicExtension.Rat.isCMField (S:={p}) K ⟨p,rfl,hp⟩
    u * (unitsComplexConj K u)⁻¹ ≠ -((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ^ n:= by
  by_contra H
  have hμ: algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) = 1:= by
    have hpow: ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) ^ p = 1:= by
      change (hζ.toInteger ^ n) ^ p = 1
      rw [← pow_mul,mul_comm,pow_mul,hζ.toInteger_isPrimitiveRoot.pow_eq_one,one_pow]
    obtain ⟨k,-,hk⟩:=hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hpow
    rw [← hk,map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K)) ^ k = 1
    rw [rp45,one_pow]
  have hμ' : algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) = -1:= by
    rw [← neg_eq_iff_eq_neg,← map_neg,← Units.val_pow_eq_pow_val,← Units.val_neg,← H]
    apply rp48 hζ u hp
  have:=Fact.mk hp
  apply (IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' _ hζ hp: (2: 𝓞 K) ∉ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1: 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))
  rw [← Ideal.Quotient.eq_zero_iff_mem,map_ofNat,← one_add_one_eq_two,← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ
theorem rp50 (u: (𝓞 K)ˣ) [H: Fact (p.Prime)] (hp: 2 < p) :
    haveI:=IsCyclotomicExtension.Rat.isCMField (S:={p}) K ⟨p,rfl,hp⟩
    ∃ m: ℕ,u * (unitsComplexConj K u)⁻¹ = (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ^ m) ^ 2:= by
  have:=IsCyclotomicExtension.Rat.isCMField (S:={p}) K ⟨p,rfl,hp⟩
  have hpo: Odd p:=H.out.odd_of_ne_two hp.ne'
  let: NormedAlgebra ℚ ℂ:=normedAlgebraRat
  have:=Embeddings.pow_eq_one_of_norm_eq_one K ℂ (x:=u * (unitsComplexConj K u)⁻¹) ?_ ?_
  · have H:=rp47 hζ hpo (u * (unitsComplexConj K u)⁻¹: K) this
    obtain ⟨n,k,hz⟩:=H
    simp_rw [← pow_mul]
    have hk:=Nat.even_or_odd k
    rcases hk with hk | hk
    · simp only [hk.neg_one_pow,one_mul] at hz
      rw [← map_mul,← Units.val_mul,← map_pow,← Units.val_pow_eq_pow_val] at hz
      norm_cast at hz
      rw [hz]
      refine (exists_congr fun a => ?_).mp
        ((hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n)
      · rw [mul_comm]
    · by_contra
      simp only [hk.neg_one_pow,neg_mul,one_mul] at hz
      rw [← map_mul,← Units.val_mul,← map_pow,← Units.val_pow_eq_pow_val,← map_neg] at hz
      norm_cast at hz
      simpa [hz] using rp49 hζ u n hp
  · apply RingHom.IsIntegralElem.mul
    · exact NumberField.RingOfIntegers.isIntegral_coe _
    · exact NumberField.RingOfIntegers.isIntegral_coe _
  · simp
end

section
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p: ℕ) [hp: Fact p.Prime] (hp_odd: p ≠ 2)
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem rp51 [IsCMField K] (a: 𝓞 K) :
    (Ideal.span {a}).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span {ringOfIntegersComplexConj K a}:= by
  simpa using
    (Ideal.map_span ((ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ({a} : Set (𝓞 K)))
theorem rp52 [IsCMField K]
    (I: Ideal (𝓞 (NumberField.maximalRealSubfield K))) :
    (I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)):= by
  rw [Ideal.map_map]
  congr
  ext x
  simp [RingHom.comp_apply,AlgEquiv.commutes]
theorem rp53 [IsCMField K]
    (a: 𝓞 K) (_ha: a ≠ 0) (I: Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (hIa: I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hIca: I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a}) :
    ∃ u: (𝓞 K)ˣ,ringOfIntegersComplexConj K a = u * a:= by
  let hspan: Ideal.span {a} = Ideal.span {ringOfIntegersComplexConj K a}:=hIa.symm.trans hIca
  obtain ⟨u,hu⟩:=Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u,?_⟩
  simpa [mul_comm] using hu.symm
theorem rp54 [IsCMField K]
    (a: 𝓞 K) (ha: a ≠ 0) (u: (𝓞 K)ˣ)
    (hu: ringOfIntegersComplexConj K a = u * a) :
    unitsComplexConj K u * u = 1:= by
  have hcc: ringOfIntegersComplexConj K (ringOfIntegersComplexConj K a) = a:= by
    apply RingOfIntegers.ext
    simp [coe_ringOfIntegersComplexConj,complexConj_apply_apply]
  have hu1: a = (unitsComplexConj K u: (𝓞 K)ˣ) * ringOfIntegersComplexConj K a:= by
    simpa [hcc,unitsComplexConj,map_mul] using! congrArg (ringOfIntegersComplexConj K) hu
  rw [hu] at hu1
  have hu2: a = (((unitsComplexConj K u * u: (𝓞 K)ˣ) : 𝓞 K) * a):= by
    simpa [mul_assoc] using hu1
  apply Units.ext
  apply mul_right_cancel₀ ha
  simpa [one_mul] using hu2.symm
include hp_odd in
theorem rp55 [IsCMField K]
    {hζ: IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u: (𝓞 K)ˣ) (_hu: unitsComplexConj K u * u = 1) :
    ∃ m: ℕ,u * (unitsComplexConj K u)⁻¹ = (hζ.unit' ^ m) ^ 2 :=
  rp50 (hζ:=hζ) u
    (lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd))
include hp_odd in
theorem rp56 [IsCMField K]
    {hζ: IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u: (𝓞 K)ˣ)
    (hu: unitsComplexConj K u * u = 1) :
    ∃ n k: ℕ,u = (-1: (𝓞 K)ˣ) ^ k * hζ.unit' ^ n:= by
  obtain ⟨m,hm⟩ :=
    rp55 (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) u hu
  have hcu: (unitsComplexConj K u)⁻¹ = u:=inv_eq_of_mul_eq_one_right hu
  have hu_sq: u ^ 2 = (hζ.unit' ^ m) ^ 2:= by
    simpa [pow_two,hcu] using hm
  have hu_fin: ∃ n: ℕ,∃ _: 0 < n,(u: K) ^ n = 1:= by
    refine ⟨2 * p,Nat.mul_pos (by decide) hp.1.pos,?_⟩
    have hu_sqK :
        (u: K) ^ 2 = (((((hζ.unit' ^ m) ^ 2: (𝓞 K)ˣ) : (𝓞 K)) : K)) :=
      congrArg (fun x: (𝓞 K)ˣ => (((x: (𝓞 K)) : K))) hu_sq
    calc
      (u: K) ^ (2 * p) = ((u: K) ^ 2) ^ p:= by rw [pow_mul]
      _ = (((((hζ.unit' ^ m) ^ 2: (𝓞 K)ˣ) : (𝓞 K)) : K)) ^ p:= by rw [hu_sqK]
      _ = 1:= by
        let ν: (𝓞 K)ˣ:=hζ.unit' ^ m
        have hνp: ν ^ p = 1:= by
          dsimp [ν]
          rw [← pow_mul,mul_comm,pow_mul,hζ.rp30,one_pow]
        have hν2p: (ν ^ 2) ^ p = 1:= by
          rw [← pow_mul,mul_comm,pow_mul,hνp,one_pow]
        exact congrArg (fun x: (𝓞 K)ˣ => (((x: (𝓞 K)) : K))) hν2p
  have hpo: Odd p:=hp.1.odd_of_ne_two hp_odd
  obtain ⟨n,k,hk⟩:=rp47 (K:=K) (hζ:=hζ) hpo (u: K) hu_fin
  refine ⟨n,k,?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  have hunit_coe: ((((hζ.unit' : (𝓞 K)ˣ) : 𝓞 K) : K)) =
      IsCyclotomicExtension.zeta p ℚ K:= by
    change (hζ.toInteger: K) = IsCyclotomicExtension.zeta p ℚ K
    exact hζ.coe_toInteger
  change (u: K) =
    (-1: K) ^ k * IsCyclotomicExtension.zeta p ℚ K ^ n
  change (u: K) = (-1: K) ^ k * hζ.toInteger.1 ^ n at hk
  rw [hζ.coe_toInteger] at hk
  exact hk
theorem rp57 [IsCMField K]
    {hζ: IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (m: ℕ) :
    complexConj K (hζ.unit' ^ m: (𝓞 K)ˣ) = ((hζ.unit' ^ m)⁻¹: (𝓞 K)ˣ):= by
  have hzeta_torsion: hζ.unit' ∈ NumberField.Units.torsion K:= by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p,hp.1.pos,?_⟩)
    exact hζ.rp30
  have hbase: unitsComplexConj K hζ.unit' = (hζ.unit'⁻¹: (𝓞 K)ˣ):= by
    simpa using unitsComplexConj_torsion K ⟨hζ.unit',hzeta_torsion⟩
  have hunits :
      unitsComplexConj K (hζ.unit' ^ m: (𝓞 K)ˣ) =
        ((hζ.unit' ^ m)⁻¹: (𝓞 K)ˣ):= by
    calc
      unitsComplexConj K (hζ.unit' ^ m: (𝓞 K)ˣ) =
          (unitsComplexConj K hζ.unit') ^ m:= by simp
      _ = ((hζ.unit')⁻¹: (𝓞 K)ˣ) ^ m:= by rw [hbase]
      _ = ((hζ.unit' ^ m)⁻¹: (𝓞 K)ˣ):= by simp
  have hro :
      ringOfIntegersComplexConj K (((hζ.unit' ^ m: (𝓞 K)ˣ) : 𝓞 K)) =
        (((hζ.unit' ^ m)⁻¹: (𝓞 K)ˣ) : 𝓞 K):=Units.ext_iff.1 hunits
  exact RingOfIntegers.ext_iff.mp hro
include hp_odd in
theorem rp58 [IsCMField K] :
    (rp34 p K).ramificationIdx (𝓞 (NumberField.maximalRealSubfield K)) = 2:= by
  have hmap0: Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
      (rp36 p K) ≠ ⊥:= by
    rw [rp44 p hp_odd K]
    exact pow_ne_zero 2 (rp35 p K)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (rp36 p K) (rp34 p K)
    hmap0,rp44 p hp_odd K,multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (rp35 p K) (zetaPrime_isPrime p K))]
include hp_odd in
theorem rp59 [IsCMField K]
    (I: Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a: 𝓞 K) (ha: a ≠ 0)
    (hIa :
      I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a}) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger - 1: 𝓞 K) a):= by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  let f: 𝓞 (NumberField.maximalRealSubfield K) →+* 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  let P: Ideal (𝓞 K):=rp34 p K
  let PPlus: Ideal (𝓞 (NumberField.maximalRealSubfield K)):=rp36 p K
  let π: 𝓞 K:=(zeta_spec p ℚ K).toInteger - 1
  have hI0: I ≠ ⊥:= by
    intro hbot
    rw [hbot,Ideal.map_bot] at hIa
    exact ha (by simpa [Ideal.span_singleton_eq_bot] using hIa.symm)
  have hmap0: I.map f ≠ ⊥:= by
    rw [hIa]
    simp [ha]
  have hP0: P ≠ ⊥:=rp35 p K
  have hPprime: P.IsPrime:= by
    dsimp [P]
    exact zetaPrime_isPrime p K
  have hPPlus0: PPlus ≠ ⊥:= by
    intro hbot
    have hmap: Ideal.map f PPlus = P ^ 2:= by
      simpa [f,P,PPlus] using rp44 p hp_odd K
    rw [hbot,Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 hP0) hmap.symm
  have hPIrr: Irreducible P:=(Ideal.prime_of_isPrime hP0 hPprime).irreducible
  have hPPlusIrr: Irreducible PPlus :=
    (Ideal.prime_of_isPrime hPPlus0 inferInstance).irreducible
  have hemul: emultiplicity P (I.map f) = PPlus.ramificationIdx' P * emultiplicity PPlus I:= by
    simpa [P,PPlus,f] using
      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
        (R:=𝓞 (NumberField.maximalRealSubfield K)) (S:=𝓞 K)
        (v:=PPlus) (w:=P) (I:=I) hI0 hPPlusIrr hPIrr hP0
  have hcount_even :
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f))):= by
    rw [Even]
    refine ⟨Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I),?_⟩
    have hemul':=hemul
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p:=PPlus) (q:=P) hPPlus0,
      rp58 (p:=p) (hp_odd:=hp_odd) (K:=K),
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPIrr hmap0,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPPlusIrr hI0,
      normalize_eq P,normalize_eq PPlus] at hemul'
    have hemul_nat :
        Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f)) =
          2 * Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I):= by
      exact_mod_cast hemul'
    simpa [two_mul] using hemul_nat
  have hπPrime: Prime π:= by simpa [π] using hζ.zeta_sub_one_prime'
  let e:=multiplicity π a
  have hπFin: FiniteMultiplicity π a:=FiniteMultiplicity.of_prime_left hπPrime ha
  have hπe_dvd: π ^ e ∣ a:=(hπFin.pow_dvd_iff_le_multiplicity).2 le_rfl
  have hπe_not_dvd: ¬π ^ (e + 1) ∣ a:= by
    rw [hπFin.pow_dvd_iff_le_multiplicity]
    exact Nat.not_succ_le_self e
  have hcount_span :
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = e:= by
    apply Ideal.count_normalizedFactors_eq (p:=P) (x:=Ideal.span {a})
    · dsimp [P]
      rw [rp34,Ideal.span_singleton_pow,Ideal.span_singleton_le_iff_mem,
        Ideal.mem_span_singleton]
      exact hπe_dvd
    · intro hle
      exact hπe_not_dvd <| by
        dsimp [P] at hle
        rw [rp34,Ideal.span_singleton_pow,Ideal.span_singleton_le_iff_mem,
          Ideal.mem_span_singleton] at hle
        exact hle
  have :
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))):= by
    rw [← hIa]
    simpa [f] using hcount_even
  simpa [e,hcount_span] using this
end CyclotomicSetup
end KummerCriterion
end
end

section
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p: ℕ) [hp: Fact p.Prime] (hp_odd: p ≠ 2)
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
include hp_odd in
theorem rp60 [IsCMField K]
    {hζ: IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I: Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a: 𝓞 K) (u: (𝓞 K)ˣ)
    (ha: a ≠ 0)
    (hIa: I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hu: ringOfIntegersComplexConj K a = u * a)
    (hclass: ∃ n k: ℕ,u = (-1: (𝓞 K)ˣ) ^ k * hζ.unit' ^ n) :
    ∃ n: ℕ,u = hζ.unit' ^ n:= by
  obtain ⟨n,k,huk⟩:=hclass
  by_cases hk_even: Even k
  · rcases hk_even with ⟨m,rfl⟩
    have hneg_even: (-1: (𝓞 K)ˣ) ^ (m + m) = 1 :=
      Even.neg_one_pow (show Even (m + m) from ⟨m,rfl⟩)
    refine ⟨n,?_⟩
    calc
      u = (-1: (𝓞 K)ˣ) ^ (m + m) * hζ.unit' ^ n:=huk
      _ = hζ.unit' ^ n:= by rw [hneg_even]; simp
  · have hk_odd: Odd k:=Nat.not_even_iff_odd.mp hk_even
    let π: 𝓞 K:=hζ.toInteger - 1
    let P: Ideal (𝓞 K):=rp34 p K
    let e:=multiplicity π a
    have heven: Even e :=
      rp59 (p:=p) (hp_odd:=hp_odd) (K:=K) I a ha hIa
    have hπPrime: Prime π:= by simpa [π] using hζ.zeta_sub_one_prime'
    have hπFin: FiniteMultiplicity π a:=FiniteMultiplicity.of_prime_left hπPrime ha
    obtain ⟨b,hpow,hnotdvd⟩:=hπFin.exists_eq_pow_mul_and_not_dvd
    have hb_not_mem: b ∉ P:= by
      simpa [P,π,rp34,Ideal.mem_span_singleton] using hnotdvd
    have hu_odd: u = (-1: (𝓞 K)ˣ) * hζ.unit' ^ n:= by
      calc
        u = (-1: (𝓞 K)ˣ) ^ k * hζ.unit' ^ n:=huk
        _ = (-1: (𝓞 K)ˣ) * hζ.unit' ^ n:= by rw [Odd.neg_one_pow hk_odd]
    let γ: (𝓞 K)ˣ:=(-1: (𝓞 K)ˣ) * hζ.unit' ^ (p - 1)
    have hc_pi: ringOfIntegersComplexConj K π = (γ: (𝓞 K)ˣ) * π:= by
      have hc_pi' : ringOfIntegersComplexConj K π = -hζ.toInteger ^ (p - 1) * π:= by
        rw [show π = hζ.toInteger - 1 by rfl,map_sub,map_one,rp37]
        linear_combination rp33 p K
      simpa [γ,π,mul_assoc,mul_left_comm,mul_comm] using! hc_pi'
    have hγ_mul: γ ^ e * hζ.unit' ^ e = 1:= by
      have hγhu: γ * hζ.unit' = (-1: (𝓞 K)ˣ):= by
        dsimp [γ]
        rw [mul_assoc,← pow_succ,Nat.sub_one_add_one hp.1.ne_zero,hζ.rp30,mul_one]
      have hmulpow: γ ^ e * hζ.unit' ^ e = (γ * hζ.unit') ^ e:= by
        simpa [mul_comm,mul_left_comm,mul_assoc] using (mul_pow γ (hζ.unit') e).symm
      calc
        γ ^ e * hζ.unit' ^ e = (γ * hζ.unit') ^ e:=hmulpow
        _ = (-1: (𝓞 K)ˣ) ^ e:= by rw [hγhu]
        _ = 1:= by simpa using (Even.neg_one_pow heven: (-1: (𝓞 K)ˣ) ^ e = 1)
    let u' : (𝓞 K)ˣ:=hζ.unit' ^ e * u
    have hcb: ringOfIntegersComplexConj K b = u' * b:= by
      have hcalc: ringOfIntegersComplexConj K (π ^ e * b) = u * (π ^ e * b):= by
        calc
          ringOfIntegersComplexConj K (π ^ e * b) = ringOfIntegersComplexConj K a:= by rw [hpow]
          _ = u * a:=hu
          _ = u * (π ^ e * b):= by rw [hpow]
      rw [map_mul,map_pow,hc_pi,mul_pow] at hcalc
      have hcancel: (((γ ^ e: (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b) =
          ((u: (𝓞 K)ˣ) : 𝓞 K) * b:= by
        have htmp: π ^ e * ((((γ ^ e: (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b)) =
            π ^ e * ((((u: (𝓞 K)ˣ) : 𝓞 K) * b)):= by
          simpa [mul_assoc,mul_left_comm,mul_comm] using hcalc
        exact mul_left_cancel₀ (pow_ne_zero _ hπPrime.ne_zero) htmp
      have hγ_mul' : hζ.unit' ^ e * γ ^ e = 1:= by simpa [mul_comm] using hγ_mul
      have hmult :=
        congrArg (fun x: 𝓞 K => (((hζ.unit' ^ e: (𝓞 K)ˣ) : 𝓞 K) * x)) hcancel
      have hγ_mul_coe: ((((hζ.unit' ^ e: (𝓞 K)ˣ) * γ ^ e: (𝓞 K)ˣ) : 𝓞 K)) = 1 :=
        congrArg (fun x: (𝓞 K)ˣ => (x: 𝓞 K)) hγ_mul'
      have hmult'' : ((((hζ.unit' ^ e: (𝓞 K)ˣ) * γ ^ e: (𝓞 K)ˣ) : 𝓞 K) *
          ringOfIntegersComplexConj K b) =
          ((((hζ.unit' ^ e: (𝓞 K)ˣ) * u: (𝓞 K)ˣ) : 𝓞 K) * b):= by
        simpa [mul_assoc,mul_left_comm,mul_comm] using hmult
      have hmult' : ringOfIntegersComplexConj K b =
          ((((hζ.unit' ^ e: (𝓞 K)ˣ) * u: (𝓞 K)ˣ) : 𝓞 K) * b):= by
        calc
          ringOfIntegersComplexConj K b =
              ((((hζ.unit' ^ e: (𝓞 K)ˣ) * γ ^ e: (𝓞 K)ˣ) : 𝓞 K) *
                ringOfIntegersComplexConj K b):= by rw [hγ_mul_coe]; simp
          _ =
              ((((hζ.unit' ^ e: (𝓞 K)ˣ) * u: (𝓞 K)ˣ) : 𝓞 K) * b):=hmult''
      simpa [u',mul_assoc,mul_left_comm,mul_comm] using hmult'
    have hpow_sub: ∀ m: ℕ,(hζ.toInteger ^ m - 1: 𝓞 K) ∈ P:= by
      intro m
      dsimp [P]
      rw [rp34,Ideal.mem_span_singleton]
      have hdiv:=sub_dvd_pow_sub_pow hζ.toInteger (1: 𝓞 K) m
      rwa [one_pow] at hdiv
    have hu'_class: u' = (-1: (𝓞 K)ˣ) * hζ.unit' ^ (e + n):= by
      dsimp [u']
      calc
        hζ.unit' ^ e * u =
            hζ.unit' ^ e * ((-1: (𝓞 K)ˣ) * hζ.unit' ^ n):= by rw [hu_odd]
        _ = (-1: (𝓞 K)ˣ) * (hζ.unit' ^ e * hζ.unit' ^ n):= by
          simp [mul_left_comm,mul_comm]
        _ = (-1: (𝓞 K)ˣ) * hζ.unit' ^ (e + n):= by rw [← pow_add]
    have hu'_plus_mem: ((((u' : (𝓞 K)ˣ) : 𝓞 K) + 1) : 𝓞 K) ∈ P:= by
      have hu'_plus_eq: (((u' : (𝓞 K)ˣ) : 𝓞 K) + 1: 𝓞 K) =
          (1 - hζ.toInteger ^ e * hζ.toInteger ^ n: 𝓞 K):= by
        rw [hu'_class]
        simp only [Units.val_mul,Units.val_neg]
        rw [show (((hζ.unit' ^ (e + n) : (𝓞 K)ˣ) : 𝓞 K)) =
          hζ.toInteger ^ (e + n) by rfl]
        rw [pow_add]
        simp [sub_eq_add_neg,add_comm]
      have hpow_sub' : (1 - hζ.toInteger ^ e * hζ.toInteger ^ n: 𝓞 K) ∈ P:= by
        have :
            (1 - hζ.toInteger ^ e * hζ.toInteger ^ n: 𝓞 K) =
              -(hζ.toInteger ^ (e + n) - 1):= by
          rw [pow_add]
          ring
        rw [this]
        exact P.neg_mem (hpow_sub (e + n))
      rw [hu'_plus_eq]
      exact hpow_sub'
    have hu'_minus_not_mem: ((((u' : (𝓞 K)ˣ) : 𝓞 K) - 1) : 𝓞 K) ∉ P:= by
      intro hminus
      have hp2: 2 < p:=lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
      have htwo: (2: 𝓞 K) ∈ P:= by
        have hsub:=Ideal.sub_mem _ hu'_plus_mem hminus
        convert hsub using 1
        ring
      exact IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' p (zeta_spec p ℚ K) hp2 htwo
    have hprod_mem: ((((u' : (𝓞 K)ˣ) : 𝓞 K) - 1) * b: 𝓞 K) ∈ P:= by
      have hres: (ringOfIntegersComplexConj K b: 𝓞 K) - b ∈ P :=
        rp38 p K b
      convert hres using 1
      rw [hcb]
      ring
    exfalso
    rcases (zetaPrime_isPrime p K).mem_or_mem hprod_mem with hunit_mem | hb_mem
    · exact hu'_minus_not_mem hunit_mem
    · exact hb_not_mem hb_mem
include hp_odd in
theorem rp61 [IsCMField K]
    {hζ: IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (a: 𝓞 K) (u: (𝓞 K)ˣ)
    (hu: ringOfIntegersComplexConj K a = u * a)
    (hclass: ∃ n: ℕ,u = hζ.unit' ^ n) :
    ∃ b: 𝓞 K,ringOfIntegersComplexConj K b = b ∧ Ideal.span {b} = Ideal.span {a}:= by
  have hpo: Odd p:=hp.1.odd_of_ne_two hp_odd
  obtain ⟨n,rfl⟩:=hclass
  obtain ⟨m,hm⟩:=exists_pow_eq_pow_two_mul hζ.rp30 hpo n
  let μ: (𝓞 K)ˣ:=hζ.unit' ^ m
  have hμsq: (hζ.unit' ^ n: (𝓞 K)ˣ) = μ ^ 2:= by
    dsimp [μ]
    calc
      (hζ.unit' ^ n: (𝓞 K)ˣ) = hζ.unit' ^ (2 * m):=hm
      _ = (hζ.unit' ^ m) ^ 2:= by simp [pow_mul,mul_comm]
  let b: 𝓞 K:=a * (μ: (𝓞 K)ˣ)
  refine ⟨b,?_,?_⟩
  · have hμconj: complexConj K μ = (μ⁻¹: (𝓞 K)ˣ):= by
      dsimp [μ]
      simpa using rp57 (p:=p) (K:=K) (hζ:=hζ) m
    have hμcoe :
        ringOfIntegersComplexConj K ((μ: (𝓞 K)ˣ) : 𝓞 K) =
          ((μ⁻¹: (𝓞 K)ˣ) : 𝓞 K):= by
      apply RingOfIntegers.ext
      simpa [coe_ringOfIntegersComplexConj] using hμconj
    have huμinv: (hζ.unit' ^ n: (𝓞 K)ˣ) * μ⁻¹ = μ:= by
      rw [hμsq]
      simp [pow_two,mul_assoc]
    calc
      ringOfIntegersComplexConj K b =
          ringOfIntegersComplexConj K a *
            ringOfIntegersComplexConj K ((μ: (𝓞 K)ˣ) : 𝓞 K):= by
            dsimp [b]
            simp
      _ = ((hζ.unit' ^ n: (𝓞 K)ˣ) : 𝓞 K) * a * (((μ⁻¹: (𝓞 K)ˣ)) : 𝓞 K):= by
            dsimp [b]
            simpa [mul_assoc,hμcoe] using congrArg
              (fun x: 𝓞 K =>
                x * ringOfIntegersComplexConj K (((μ: (𝓞 K)ˣ) : 𝓞 K))) hu
      _ =
          ((((hζ.unit' ^ n: (𝓞 K)ˣ) * μ⁻¹: (𝓞 K)ˣ) : 𝓞 K) * a):= by
            simp [mul_assoc,mul_comm]
      _ = (μ: (𝓞 K)ˣ) * a:= by rw [huμinv]
      _ = b:= by dsimp [b]; simp [mul_comm]
  · rw [Ideal.span_singleton_eq_span_singleton]
    dsimp [b]
    exact (associated_mul_unit_right a (μ: (𝓞 K)ˣ) μ.isUnit).symm
include hp_odd in
theorem rp62 [IsCMField K]
    {hζ: IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I: Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a: 𝓞 K) (u: (𝓞 K)ˣ)
    (hIa: I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hu: ringOfIntegersComplexConj K a = u * a)
    (hclass: ∃ n k: ℕ,u = (-1: (𝓞 K)ˣ) ^ k * hζ.unit' ^ n) :
    ∃ b: 𝓞 K,ringOfIntegersComplexConj K b = b ∧ Ideal.span {b} = Ideal.span {a}:= by
  by_cases ha: a = 0
  · refine ⟨0,?_,?_⟩ <;> simp [ha]
  · obtain ⟨n,hn⟩ :=
      rp60 (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ)
        I a u ha hIa hu hclass
    exact rp61
      (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) a u hu ⟨n,hn⟩
theorem rp63 [IsCMField K]
    (b: 𝓞 K) (hb: ringOfIntegersComplexConj K b = b) :
    b ∈ Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (ringOfIntegersComplexConj_eq_self_iff K b).mp hb
end CyclotomicSetup
end KummerCriterion
end
end

section
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p: ℕ) [hp: Fact p.Prime] (hp_odd: p ≠ 2)
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
include hp_odd in
theorem rp64: IsCMField K :=
  Rat.isCMField (S:={p}) _ ⟨p,by grind [hp.1.two_le]⟩
theorem rp65 [IsCMField K] :
    Module.finrank ((NumberField.maximalRealSubfield K)) K = 2 :=
  IsQuadraticExtension.finrank_eq_two _ _
theorem rp66 [IsCMField K] :
    Module.finrank ℚ ((NumberField.maximalRealSubfield K)) = (p - 1) / 2:= by
  have h1: Module.finrank ((NumberField.maximalRealSubfield K)) K = 2:=rp65 K
  have h2: Module.finrank ℚ K = p - 1:= by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.1.pos),
        Nat.totient_prime hp.1]
  have htow:=Module.finrank_mul_finrank ℚ ((NumberField.maximalRealSubfield K)) K
  rw [h1,h2] at htow
  exact (Nat.div_eq_of_eq_mul_left (by omega) htow.symm).symm
include hp_odd in
theorem rp67 [IsCMField K] :
    IsCMField.indexRealUnits K = 1:= by
  have hp2: 2 < p:=lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hzeta_torsion: hζ.unit' ∈ NumberField.Units.torsion K:= by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p,by omega,?_⟩)
    exact hζ.rp30
  have hrange :
      (IsCMField.unitsMulComplexConjInv K).range =
        (powMonoidHom 2: NumberField.Units.torsion K →* NumberField.Units.torsion K).range:= by
    refine le_antisymm ?_ ?_
    · rintro x ⟨u,rfl⟩
      obtain ⟨m,hm⟩:=rp50 hζ u hp2
      refine ⟨⟨hζ.unit' ^ m,(NumberField.Units.torsion K).pow_mem hzeta_torsion m⟩,?_⟩
      apply Subtype.ext
      simpa [pow_two] using! hm.symm
    · rintro x ⟨u,rfl⟩
      exact ⟨u,by simp [pow_two]⟩
  have hrange_idx: (IsCMField.unitsMulComplexConjInv K).range.index = 2:= by
    rw [hrange,IsCyclic.index_powMonoidHom_range,Nat.gcd_eq_right]
    exact even_iff_two_dvd.mp (NumberField.Units.even_torsionOrder K)
  have hmul: IsCMField.indexRealUnits K * 2 = 2:= by
    simpa [hrange_idx] using IsCMField.indexRealUnits_mul_eq K
  omega
noncomputable def h: ℕ:=Fintype.card (ClassGroup (𝓞 K))
noncomputable def hPlus [IsCMField K] : ℕ:=Fintype.card (ClassGroup (𝓞 ((NumberField.maximalRealSubfield K))))
end CyclotomicSetup
end KummerCriterion
end
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p: ℕ) [hp: Fact p.Prime] (hp_odd: p ≠ 2)
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem rp68
    (L: Type*) [Field L] [NumberField L]
    (J: Ideal (𝓞 (NumberField.maximalRealSubfield L))) :
    (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L))).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L)) = J:= by
  simpa using Ideal.comap_map_eq_self_of_faithfullyFlat J
theorem rp69
    (I: Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (b₀: 𝓞 ((NumberField.maximalRealSubfield K)))
    (hb: I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) =
      Ideal.span {algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) b₀}) :
    I.IsPrincipal:= by
  refine ⟨b₀,?_⟩
  let f: 𝓞 ((NumberField.maximalRealSubfield K)) →+* 𝓞 K:=algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)
  have hbc:=congrArg (Ideal.comap f) hb
  have hspan: Ideal.comap f (Ideal.span {f b₀}) = Ideal.span {b₀}:= by
    calc
      Ideal.comap f (Ideal.span {f b₀}) = Ideal.comap f ((Ideal.span {b₀}).map f):= by
        rw [Ideal.map_span,Set.image_singleton]
      _ = Ideal.span {b₀}:=rp68 K (Ideal.span {b₀})
  calc
    I = Ideal.comap f (I.map f):=(rp68 K I).symm
    _ = Ideal.comap f (Ideal.span {f b₀}):=hbc
    _ = Ideal.span {b₀}:=hspan
include hp_odd in
theorem rp70 [IsCMField K]
    (I: Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (hI: (I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal:= by
  obtain ⟨a,ha⟩:=hI
  by_cases hzero: a = 0
  · have: I = ⊥:= by
      rw [← Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)),ha,hzero]
      simp
    exact this ▸ bot_isPrincipal
  have hIa: I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) = Ideal.span {a}:=ha
  have hIcon:=rp52 (K:=K) I
  have hIca: I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a}:= by
    rw [← hIcon,hIa,rp51]
  obtain ⟨u,hu⟩:=rp53 (K:=K) a hzero I hIa hIca
  have hanti:=rp54 (K:=K) a hzero u hu
  have hζ: IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  obtain ⟨n,k,hclass⟩ :=
    rp56
      (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) u hanti
  obtain ⟨b,hb_conj,hb_span⟩ :=
    rp62
      (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) I a u hIa hu ⟨n,k,hclass⟩
  obtain ⟨b₀,hb₀⟩:=rp63 (K:=K) b hb_conj
  have hspan: I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) = Ideal.span {b}:= by
    rw [hIa,← hb_span]
  rw [← hb₀] at hspan
  exact rp69 K I b₀ hspan
include hp_odd in
theorem rp71 [IsCMField K]
    (I: Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (hI: (I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal :=
  rp70 (p:=p) (hp_odd:=hp_odd) (K:=K) I hI
abbrev rp72 [IsCMField K] :
    ClassGroup (𝓞 ((NumberField.maximalRealSubfield K))) →* ClassGroup (𝓞 K) :=
  ClassGroup.extendedHom (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)
include hp_odd in
theorem rp73 [IsCMField K] :
    Function.Injective (rp72 K):= by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨I,rfl⟩:=ClassGroup.mk0_surjective c
  rw [ClassGroup.mk0_eq_one_iff I.2]
  refine rp71 (p:=p) (hp_odd:=hp_odd) (K:=K) I.1 ?_
  have hne: I.1.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective _ _)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hne),
    ← ClassGroup.extendedHom_mk0]
  exact hc
include hp_odd in
theorem rp74 [IsCMField K] : (KummerCriterion.hPlus K) ∣ (KummerCriterion.h K):= by
  rw [KummerCriterion.hPlus,KummerCriterion.h,
    ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_injective (rp72 K)
    (rp73 p hp_odd K)
noncomputable def hMinus [IsCMField K] : ℕ:=(KummerCriterion.h K) / (KummerCriterion.hPlus K)
include hp_odd in
theorem rp75 [IsCMField K] : (KummerCriterion.h K) = (KummerCriterion.hPlus K) * (KummerCriterion.hMinus K):= by
  rw [hMinus,Nat.mul_div_cancel' (rp74 p hp_odd K)]
end CyclotomicSetup
end KummerCriterion
end
end

section
noncomputable section
open NumberField
open Polynomial
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section ZetaFactorisation
noncomputable instance instFintypeSym (α: Type*) [Finite α] (n: ℕ) :
    Fintype (Sym α n) :=
  Fintype.ofFinite (Sym α n)
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def rp76: DirichletCharacter ℂ p ≃* (ZMod p)ˣ:= by
  letI: NeZero p:=⟨hp.1.ne_zero⟩
  exact (DirichletCharacter.mulEquiv_units ℂ p).some
lemma rp77: Nat.card (DirichletCharacter ℂ p) = p - 1:= by
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,Nat.totient_prime hp.1]
lemma rp78 {s: ℂ} (hs: s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar p s =
      (1 - (p: ℂ) ^ (-s)) * riemannZeta s:= by
  have hpf: Nat.primeFactors p = {p}:= by
    simpa using (Nat.primeFactors_prime_pow (p:=p) (k:=1) (by decide: (1: ℕ) ≠ 0) hp.1)
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N:=p) hs,hpf,
    Finset.prod_singleton]
noncomputable def rp79 (ℓ: ℕ) : Ideal ℤ :=
  Ideal.span ({(ℓ: ℤ)} : Set ℤ)
noncomputable def rp80 (ℓ: ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (rp79 ℓ) (𝓞 K)
noncomputable def rp81: Finset (DirichletCharacter ℂ p):= by
  classical
  exact Finset.univ.erase 1
noncomputable def rp82: Finset (DirichletCharacter ℂ p):= by
  classical
  exact Finset.univ.filter fun χ => χ.Even ∧ χ ≠ 1
noncomputable def rp83: Finset (DirichletCharacter ℂ p):= by
  classical
  exact Finset.univ.filter fun χ => χ.Odd
theorem rp84 (p: ℕ) {χ: DirichletCharacter ℂ p}
    (hχ: χ ∈ rp83 p) : χ⁻¹ ∈ rp83 p:= by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  have hχ_odd: χ.Odd:=(Finset.mem_filter.mp hχ).2
  rw [DirichletCharacter.Odd] at hχ_odd ⊢
  rw [MulChar.inv_apply_eq_inv',hχ_odd]
  norm_num
noncomputable def rp85 (ℓ: ℕ) (s: ℂ) : ℂ :=
  ∏ χ: DirichletCharacter ℂ p,(1 - χ (ℓ: ZMod p) * (ℓ: ℂ) ^ (-s))
noncomputable def rp86 (ℓ: ℕ) (s: ℂ) : ℂ :=
  Finset.prod (rp82 (p:=p)) fun χ =>
    (1 - χ (ℓ: ZMod p) * (ℓ: ℂ) ^ (-s))
noncomputable def rp87 (ℓ: ℕ) (s: ℂ) : ℂ :=
  Finset.prod (rp80 K ℓ) fun P => (1 - (Ideal.absNorm P: ℂ) ^ (-s))
noncomputable def LProduct (s: ℂ) : ℂ :=
  ∏ χ: DirichletCharacter ℂ p,DirichletCharacter.LFunction χ s
noncomputable def rp88 (s: ℂ) : ℂ :=
  Finset.prod (rp81 (p:=p)) fun χ => DirichletCharacter.LFunction χ s
noncomputable def rp89 (s: ℂ) : ℂ :=
  Finset.prod (rp82 (p:=p)) fun χ => DirichletCharacter.LFunction χ s
noncomputable def rp90 (s: ℂ) : ℂ :=
  Finset.prod (rp83 (p:=p)) fun χ => DirichletCharacter.LFunction χ s
noncomputable def rp91: 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
lemma rp92 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) : p.Coprime ℓ :=
  (Nat.coprime_primes hp.out (Fact.out: ℓ.Prime)).mpr (Ne.symm hℓp)
noncomputable def rp93 (ℓ: ℕ) [Fact ℓ.Prime] (hℓp: ℓ ≠ p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime ℓ (rp92 (p:=p) hℓp).symm
noncomputable def rp94 (ℓ: ℕ) [Fact ℓ.Prime] (hℓp: ℓ ≠ p) : ℕ :=
  orderOf (rp93 (p:=p) ℓ hℓp)
noncomputable def rp95 (ℓ: ℕ) [Fact ℓ.Prime] (hℓp: ℓ ≠ p) : ℕ :=
  Nat.card (DirichletCharacter ℂ p) / rp94 (p:=p) ℓ hℓp
lemma rp96 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    rp94 (p:=p) ℓ hℓp ∣ Nat.card (DirichletCharacter ℂ p):= by
  rw [rp77 (p:=p)]
  simpa [rp94,ZMod.card_units p] using
    (orderOf_dvd_card (x:=rp93 (p:=p) ℓ hℓp))
lemma rp97 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    rp95 (p:=p) ℓ hℓp * rp94 (p:=p) ℓ hℓp =
      Nat.card (DirichletCharacter ℂ p) :=
  Nat.div_mul_cancel (rp96 (p:=p) hℓp)
lemma rp98 (d: ℕ) (hd: 0 < d) (T: ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset d (1: ℂ),(1 - ζ * T) = 1 - T ^ d:= by
  by_cases hT: T = 0
  · subst hT
    simp [zero_pow hd.ne']
  · have hζ: IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / d)) d :=
      Complex.isPrimitiveRoot_exp d hd.ne'
    have hcard: (Polynomial.nthRootsFinset d (1: ℂ)).card = d:=hζ.card_nthRootsFinset
    have hpoly: Polynomial.X ^ d - 1 = ∏ ζ ∈ Polynomial.nthRootsFinset d (1: ℂ),
        (Polynomial.X - Polynomial.C ζ):=Polynomial.X_pow_sub_one_eq_prod hd hζ
    have heval:=congrArg (Polynomial.eval T⁻¹) hpoly
    simp only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_prod,Polynomial.eval_C] at heval
    have key: ∀ ζ: ℂ,(1 - ζ * T) = T * (T⁻¹ - ζ):=fun ζ => by field_simp
    rw [Finset.prod_congr rfl (fun ζ _ => key ζ),Finset.prod_mul_distrib,
      Finset.prod_const,hcard,← heval]
    have hTT: T ^ d * T⁻¹ ^ d = 1:= by rw [← mul_pow,mul_inv_cancel₀ hT,one_pow]
    linear_combination hTT
lemma _root_.IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd
    {M: Type*} [CommMonoid M] {n: ℕ} (hn: 0 < n) (a: ℕ)
    {ω: M} (hω: IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω ^ a) (n / n.gcd a):= by
  set d:=n / n.gcd a with hd_def
  set c:=n.gcd a with hc_def
  have hc_dvd_n: c ∣ n:=Nat.gcd_dvd_left n a
  have hc_dvd_a: c ∣ a:=Nat.gcd_dvd_right n a
  have hc_mul_d: c * d = n:=Nat.mul_div_cancel' hc_dvd_n
  have hc_pos: 0 < c:=Nat.gcd_pos_of_pos_left _ hn
  obtain ⟨a',ha'⟩:=hc_dvd_a
  have ha'_cop: a'.Coprime d:= by
    have key: c * Nat.gcd a' d = c * 1:= by
      rw [mul_one]
      calc c * Nat.gcd a' d
          = (c * a').gcd (c * d):=(Nat.gcd_mul_left c a' d).symm
        _ = a.gcd n:= by rw [← ha',hc_mul_d]
        _ = c:= by rw [Nat.gcd_comm]
    exact Nat.eq_of_mul_eq_mul_left hc_pos key
  have hω_c: IsPrimitiveRoot (ω ^ c) d:=hω.pow hn hc_mul_d.symm
  rw [ha',pow_mul]
  exact hω_c.pow_of_coprime _ ha'_cop
lemma rp99 {n: ℕ} (hn: 0 < n) (a: ℕ)
    {ω: ℂ} (hω: IsPrimitiveRoot ω n) (T: ℂ) :
    ∏ k ∈ Finset.range n,(1 - ω ^ (k * a) * T) =
      (1 - T ^ (n / n.gcd a)) ^ n.gcd a:= by
  classical
  set d:=n / n.gcd a with hd_def
  set c:=n.gcd a with hc_def
  have hc_dvd_n: c ∣ n:=Nat.gcd_dvd_left n a
  have hc_dvd_a: c ∣ a:=Nat.gcd_dvd_right n a
  have hc_mul_d: c * d = n:=Nat.mul_div_cancel' hc_dvd_n
  have hc_pos: 0 < c:=Nat.gcd_pos_of_pos_left _ hn
  have hd_pos: 0 < d:=Nat.div_pos (Nat.le_of_dvd hn hc_dvd_n) hc_pos
  have hd_dvd_n: d ∣ n:=⟨c,by rw [mul_comm]; exact hc_mul_d.symm⟩
  have hω_a_prim: IsPrimitiveRoot (ω ^ a) d :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn a hω
  have h_period: ∀ k: ℕ,ω ^ (k * a) = ω ^ ((k % d) * a):= by
    intro k
    have hkd: k = d * (k / d) + k % d:=(Nat.div_add_mod k d).symm
    have h_da: ω ^ ((k / d) * (d * a)) = 1:= by
      obtain ⟨a',ha'⟩:=hc_dvd_a
      rw [ha',show (k / d) * (d * (c * a')) = (k / d) * a' * (c * d) from by ring,hc_mul_d]
      exact (hω.pow_eq_one_iff_dvd _).mpr ⟨(k / d) * a',mul_comm _ _⟩
    conv_lhs => rw [hkd]
    rw [show (d * (k / d) + k % d) * a = (k % d) * a + (k / d) * (d * a) from by ring,pow_add,
      h_da,mul_one]
  rw [show (∏ k ∈ Finset.range n,(1 - ω ^ (k * a) * T)) =
      ∏ k ∈ Finset.range n,(1 - ω ^ ((k % d) * a) * T) from
    Finset.prod_congr rfl (fun k _ => by rw [← h_period k])]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g:=fun k: ℕ => k % d) (t:=Finset.range d)
    (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hd_pos))]
  have h_inner: ∀ j ∈ Finset.range d,
      (∏ k ∈ (Finset.range n).filter (fun k => k % d = j),(1 - ω ^ ((k % d) * a) * T)) =
      (1 - ω ^ (j * a) * T) ^ c:= by
    intro j hj
    have h_rewrite: ∀ k ∈ (Finset.range n).filter (fun k => k % d = j),
        (1 - ω ^ ((k % d) * a) * T) = (1 - ω ^ (j * a) * T):=fun k hk => by
      rw [Finset.mem_filter] at hk; rw [hk.2]
    rw [Finset.prod_congr rfl h_rewrite,Finset.prod_const]
    congr 1
    rw [Finset.mem_range] at hj
    obtain ⟨c',hcd'⟩:=hd_dvd_n
    have hc_eq: c = c':= by
      have hd_mul: d * c = n:= by rw [mul_comm,hc_mul_d]
      exact Nat.eq_of_mul_eq_mul_left hd_pos (by rw [hd_mul,hcd'])
    rw [hc_eq]
    have hset: (Finset.range n).filter (fun k => k % d = j) =
        (Finset.range c').image (fun m => j + m * d):= by
      ext k
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_image]
      refine ⟨fun ⟨hk_lt,hk_mod⟩ => ?_,?_⟩
      · have hk_dec: k = j + (k / d) * d:= by
          have h1: k = d * (k / d) + k % d:=(Nat.div_add_mod k d).symm
          rw [hk_mod,mul_comm d (k / d)] at h1
          omega
        refine ⟨k / d,?_,hk_dec.symm⟩
        have h_lt_cd: (k / d) * d < c' * d:= by
          have h_le: (k / d) * d ≤ k:=Nat.div_mul_le_self k d
          rw [mul_comm c' d,← hcd']; omega
        exact Nat.lt_of_mul_lt_mul_right h_lt_cd
      · rintro ⟨m,hm_lt,rfl⟩
        refine ⟨?_,?_⟩
        · rw [hcd',mul_comm]; nlinarith
        · rw [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hj]
    rw [hset,Finset.card_image_of_injective _ (fun x y hxy => by simp at hxy; omega),
      Finset.card_range]
  rw [Finset.prod_congr rfl h_inner,Finset.prod_pow]
  congr 1
  have h_inj: Set.InjOn (fun j: ℕ => (ω ^ a) ^ j) ↑(Finset.range d):= by
    intro x hx y hy hxy
    simp only [Finset.coe_range,Set.mem_Iio] at hx hy
    exact hω_a_prim.pow_inj hx hy hxy
  have h_image: Finset.image (fun j: ℕ => (ω ^ a) ^ j) (Finset.range d) =
      Polynomial.nthRootsFinset d (1: ℂ):= by
    apply Finset.eq_of_subset_of_card_le
    · intro ζ hζ
      simp only [Finset.mem_image,Finset.mem_range] at hζ
      obtain ⟨j,_,rfl⟩:=hζ
      rw [Polynomial.mem_nthRootsFinset hd_pos,← pow_mul,mul_comm j d,pow_mul,
        hω_a_prim.pow_eq_one,one_pow]
    · rw [hω_a_prim.card_nthRootsFinset,Finset.card_image_of_injOn h_inj,Finset.card_range]
  calc ∏ j ∈ Finset.range d,(1 - ω ^ (j * a) * T)
      = ∏ j ∈ Finset.range d,(1 - (ω ^ a) ^ j * T):= by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← pow_mul,mul_comm a j]
    _ = ∏ ζ ∈ Finset.image (fun j: ℕ => (ω ^ a) ^ j) (Finset.range d),(1 - ζ * T):= by
        rw [Finset.prod_image h_inj]
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset d (1: ℂ),(1 - ζ * T):= by rw [h_image]
    _ = 1 - T ^ d:=rp98 d hd_pos T
lemma rp100 (u: (ZMod p)ˣ) (T: ℂ) :
    (∏ χ: DirichletCharacter ℂ p,(1 - χ (u: ZMod p) * T)) =
      (1 - T ^ orderOf u) ^ (Nat.card (DirichletCharacter ℂ p) / orderOf u):= by
  classical
  set d:=orderOf u with hd_def
  set n:=Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units: Fintype.card (ZMod p)ˣ = n:= by
    rw [hn_def,rp77 (p:=p),ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n:= by
    rw [Nat.card_eq_fintype_card,hn_units]
  have hn_pos: 0 < n:= by rw [← hn_units]; exact Fintype.card_pos
  obtain ⟨g,hg_mon⟩ : ∃ g: (ZMod p)ˣ,∀ x: (ZMod p)ˣ,x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x: (ZMod p)ˣ,∃ m: ℕ,g ^ m = x:=fun x => hg_mon x
  obtain ⟨a,ha⟩:=hg_mon' u
  have hg_zpow: ∀ x: (ZMod p)ˣ,x ∈ Subgroup.zpowers g:=fun x => by
    obtain ⟨m,hm⟩:=hg_mon' x
    refine ⟨(m: ℤ),?_⟩
    change g ^ (m: ℤ) = x
    rw [zpow_natCast]; exact hm
  have hg_order: orderOf g = n:= by
    rw [← hn_units']; exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hd_eq: d = n / n.gcd a:= by
    have hfin: IsOfFinOrder g:= by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨n,hn_pos,by rw [← hg_order]; exact pow_orderOf_eq_one g⟩
    have: d = orderOf (g ^ a):= by rw [hd_def,← ha]
    rw [this,hfin.orderOf_pow,hg_order]
  have hn_div_d: n / d = n.gcd a:= by
    have hcd: n.gcd a ∣ n:=Nat.gcd_dvd_left n a
    rw [hd_eq,Nat.div_div_self hcd hn_pos.ne']
  have hω: IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω: ℂ:=Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit: IsUnit ω:=hω.isUnit hn_pos.ne'
  set ωu: ℂˣ:=hω_unit.unit with hωu_def
  have hωu_val: (ωu: ℂ) = ω:= by simp [hωu_def]
  have hωu_roots: ∀ k: ℕ,(ωu ^ k: ℂˣ) ∈ rootsOfUnity n ℂ:= by
    intro k
    rw [mem_rootsOfUnity,← pow_mul,mul_comm]
    have h1: (ωu ^ n: ℂˣ) = 1:= by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val,Units.val_one,hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul,h1,one_pow]
  let χAt: ℕ → DirichletCharacter ℂ p:=fun k =>
    MulChar.ofRootOfUnity (M:=ZMod p) (R:=ℂ) (ζ:=ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g: ∀ k: ℕ,χAt k ((g: (ZMod p)ˣ) : ZMod p) = ω ^ k:=fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val,hωu_val]
  have hχAt_u: ∀ k: ℕ,χAt k (u: ZMod p) = ω ^ (k * a):=fun k => by
    have hu_eq: (u: ZMod p) = ((g: (ZMod p)ˣ) : ZMod p) ^ a:= by
      rw [← Units.val_pow_eq_pow_val,ha]
    rw [hu_eq,map_pow,hχAt_g,← pow_mul]
  have hχAt_inj: Set.InjOn χAt ↑(Finset.range n):= by
    intro j hj k hk hjk
    simp only [Finset.coe_range,Set.mem_Iio] at hj hk
    have hval: χAt j ((g: (ZMod p)ˣ) : ZMod p) = χAt k ((g: (ZMod p)ˣ) : ZMod p):= by
      rw [hjk]
    rw [hχAt_g,hχAt_g] at hval
    exact hω.pow_inj hj hk hval
  have hχAt_surj_onto_univ :
      Finset.image χAt (Finset.range n) = (Finset.univ: Finset (DirichletCharacter ℂ p)):= by
    apply Finset.eq_of_subset_of_card_le
    · exact fun _ _ => Finset.mem_univ _
    · rw [Finset.card_image_of_injOn hχAt_inj,Finset.card_range,Finset.card_univ,
        ← Nat.card_eq_fintype_card]
  have h_transfer: ∏ χ: DirichletCharacter ℂ p,(1 - χ (u: ZMod p) * T) =
      ∏ k ∈ Finset.range n,(1 - ω ^ (k * a) * T):= by
    calc ∏ χ: DirichletCharacter ℂ p,(1 - χ (u: ZMod p) * T)
        = ∏ χ ∈ (Finset.univ: Finset (DirichletCharacter ℂ p)),
            (1 - χ (u: ZMod p) * T):=rfl
      _ = ∏ χ ∈ Finset.image χAt (Finset.range n),(1 - χ (u: ZMod p) * T):= by
          rw [hχAt_surj_onto_univ]
      _ = ∏ k ∈ Finset.range n,(1 - (χAt k) (u: ZMod p) * T):= by
          rw [Finset.prod_image hχAt_inj]
      _ = ∏ k ∈ Finset.range n,(1 - ω ^ (k * a) * T):= by
          refine Finset.prod_congr rfl (fun k _ => ?_)
          rw [hχAt_u k]
  rw [h_transfer,rp99 hn_pos a hω T,← hd_eq,hn_div_d]
lemma rp101 {ℓ: ℕ} [Fact ℓ.Prime]
    (hℓp: ℓ ≠ p) {s: ℂ} :
    rp85 (p:=p) ℓ s =
      (1 - ((ℓ: ℂ) ^ (-s)) ^ rp94 (p:=p) ℓ hℓp) ^
        (Nat.card (DirichletCharacter ℂ p) / rp94 (p:=p) ℓ hℓp):= by
  have hval: ((rp93 p ℓ hℓp: (ZMod p)ˣ) : ZMod p) = (ℓ: ZMod p):= by
    simp [rp93]
  unfold rp85
  rw [← hval]
  unfold rp94
  exact rp100 p (rp93 p ℓ hℓp) ((ℓ: ℂ) ^ (-s))
lemma rp102 {ℓ: ℕ} [Fact ℓ.Prime]
    (hℓp: ℓ ≠ p) {s: ℂ} :
    rp85 (p:=p) ℓ s =
      (1 - (ℓ: ℂ) ^ (-(rp94 (p:=p) ℓ hℓp: ℂ) * s)) ^
        rp95 (p:=p) ℓ hℓp:= by
  rw [rp101 (p:=p) hℓp,
    show ((ℓ: ℂ) ^ (-s)) ^ rp94 (p:=p) ℓ hℓp =
        (ℓ: ℂ) ^ (-((rp94 (p:=p) ℓ hℓp: ℂ)) * s) by
      rw [show -((rp94 (p:=p) ℓ hℓp: ℂ)) * s =
          (-s) * ((rp94 (p:=p) ℓ hℓp: ℕ) : ℂ) by ring,
        Complex.cpow_mul_nat]]
  rfl
lemma rp103 {s: ℂ} :
    rp85 (p:=p) p s = 1 :=
  Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self,MulChar.map_nonunit _ not_isUnit_zero,zero_mul,sub_zero]
lemma rp104 {ℓ: ℕ} [Fact ℓ.Prime] {P: Ideal (𝓞 K)} :
    P ∈ rp80 K ℓ ↔ P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K):= by
  have: (rp79 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (rp79 ℓ) ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)
lemma rp105 :
    Algebra.adjoin ℤ ({rp91 (p:=p) (K:=K)} : Set (𝓞 K)) = ⊤:= by
  exact IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (IsCyclotomicExtension.zeta_spec p ℚ K)
lemma rp106 :
    RingOfIntegers.exponent (rp91 (p:=p) (K:=K)) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (rp105 (p:=p) (K:=K))
lemma rp107 {ℓ: ℕ} [Fact ℓ.Prime] :
    ¬ ℓ ∣ RingOfIntegers.exponent (rp91 (p:=p) (K:=K)):= by
  rw [rp106]
  exact Nat.Prime.not_dvd_one (Fact.out: ℓ.Prime)
noncomputable def rp108 (ℓ: ℕ) [Fact ℓ.Prime] :
  Ideal.primesOver (rp79 ℓ) (𝓞 K) ≃
      RingOfIntegers.monicFactorsMod (θ:=rp91 (p:=p) (K:=K)) (p:=ℓ) :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K:=K) (θ:=rp91 (p:=p) (K:=K))
    (p:=ℓ) (rp107 (p:=p) (K:=K) (ℓ:=ℓ))
lemma rp109 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    (RingOfIntegers.monicFactorsMod (θ:=rp91 (p:=p) (K:=K)) (p:=ℓ)).card =
      rp95 (p:=p) ℓ hℓp:= by
  classical
  have hmin: minpoly ℤ (rp91 (p:=p) (K:=K)) = cyclotomic p ℤ:= by
    rw [rp91,← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  have hcop: ℓ.Coprime p:=(rp92 (p:=p) hℓp).symm
  have hFcard: Fintype.card (ZMod ℓ) = ℓ ^ 1:= by
    rw [pow_one]; exact ZMod.card ℓ
  unfold RingOfIntegers.monicFactorsMod
  rw [hmin,Polynomial.map_cyclotomic_int,
    Polynomial.normalizedFactors_cyclotomic_card hFcard hcop]
  unfold rp95 rp94 rp93
  rw [rp77 (p:=p),Nat.totient_prime hp.out,
    ← orderOf_units (y:=ZMod.unitOfCoprime _ _),
    ← orderOf_units (y:=ZMod.unitOfCoprime ℓ _),ZMod.coe_unitOfCoprime,
    ZMod.coe_unitOfCoprime,pow_one]
lemma rp110 :
    map (Int.castRingHom (ZMod p))
        (minpoly ℤ (rp91 (p:=p) (K:=K))) =
      (X - 1) ^ (p - 1):= by
  have hmin: minpoly ℤ (rp91 (p:=p) (K:=K)) = cyclotomic p ℤ:= by
    rw [rp91,← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  rw [hmin,Polynomial.map_cyclotomic_int]
  have h1: (cyclotomic p (ZMod p)) * (X - 1) = X ^ p - 1 :=
    cyclotomic_prime_mul_X_sub_one (ZMod p) p
  have h2: (X - 1: (ZMod p)[X]) ^ p = X ^ p - 1:= by
    rw [sub_pow_char_of_commute p (Commute.one_right X)]
    ring
  have hne: (X - 1: (ZMod p)[X]) ≠ 0:=X_sub_C_ne_zero 1
  have hpow: (X - 1: (ZMod p)[X]) ^ p = (X - 1) ^ (p - 1) * (X - 1):= by
    have hpos: 0 < p:=hp.out.pos
    rw [← pow_succ]
    congr 1
    omega
  refine mul_right_cancel₀ hne ?_
  rw [← hpow,h2,← h1]
lemma rp111 :
    (RingOfIntegers.monicFactorsMod (θ:=rp91 (p:=p) (K:=K)) (p:=p)).card = 1:= by
  classical
  unfold RingOfIntegers.monicFactorsMod
  rw [rp110 (p:=p) (K:=K)]
  have hirr: Irreducible (X - 1: (ZMod p)[X]) :=
    irreducible_X_sub_C 1
  rw [hirr.normalizedFactors_pow,Multiset.toFinset_replicate]
  have hp_pos: p - 1 ≠ 0:=Nat.sub_ne_zero_of_lt hp.out.one_lt
  simp [hp_pos]
lemma rp112 :
    (Ideal.primesOver (rp79 p) (𝓞 K)).ncard = 1:= by
  classical
  rw [← rp111 (p:=p) (K:=K),
    ← Nat.card_coe_set_eq,Nat.card_congr (rp108 (p:=p) (K:=K) p),
    Nat.card_eq_finsetCard]
lemma rp113 (P: Ideal (𝓞 K))
    (hP: P ∈ Ideal.primesOver (rp79 p) (𝓞 K)) :
    P.inertiaDeg ℤ = 1:= by
  have: P.IsPrime:=hP.1
  have: P.LiesOver (Ideal.span {(p: ℤ)}):= by
    simpa [rp79] using hP.2
  simpa [rp79] using IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p K P
lemma rp114 {ℓ: ℕ} [Fact ℓ.Prime]
    (hℓp: ℓ ≠ p) (P: Ideal (𝓞 K))
    (hP: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K)) :
    P.inertiaDeg ℤ = rp94 (p:=p) ℓ hℓp:= by
  have: P.IsPrime:=hP.1
  have: P.LiesOver (Ideal.span {(ℓ: ℤ)}):=hP.2
  have hcop: ¬ ℓ ∣ p:=fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out: ℓ.Prime) hp.out).mp h)
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd ℓ K P hcop]
  unfold rp94 rp93
  rw [← orderOf_units]
  rfl
lemma rp115 {ℓ: ℕ} [Fact ℓ.Prime]
    (hℓp: ℓ ≠ p) (P: Ideal (𝓞 K))
    (hP: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K)) :
    P.ramificationIdx ℤ = 1:= by
  have: P.IsPrime:=hP.1
  have: P.LiesOver (Ideal.span {(ℓ: ℤ)}):=hP.2
  have hcop: ¬ ℓ ∣ p:=fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out: ℓ.Prime) hp.out).mp h)
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ℓ K P hcop
lemma rp116 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    (Ideal.primesOver (rp79 ℓ) (𝓞 K)).ncard =
      rp95 (p:=p) ℓ hℓp:= by
  classical
  rw [← rp109 (p:=p) (K:=K) hℓp,
    ← Nat.card_coe_set_eq,Nat.card_congr (rp108 (p:=p) (K:=K) ℓ),
    Nat.card_eq_finsetCard]
lemma rp117 {ℓ: ℕ} [Fact ℓ.Prime]
    (hℓp: ℓ ≠ p) {s: ℂ} :
    rp87 K ℓ s =
      (1 - (ℓ: ℂ) ^ (-(rp94 (p:=p) ℓ hℓp: ℂ) * s)) ^
        rp95 (p:=p) ℓ hℓp:= by
  classical
  have: (rp79 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (rp79 ℓ) ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
  have hcoe:=IsDedekindDomain.coe_primesOverFinset (p:=rp79 ℓ) hne (𝓞 K)
  have hcard_eq: (rp80 K ℓ).card = rp95 (p:=p) ℓ hℓp:= by
    have h1:=rp116 p K hℓp
    rw [← hcoe,Set.ncard_coe_finset] at h1
    exact h1
  unfold rp87
  have hprod_eq: ∀ P ∈ rp80 K ℓ,
      (1 - (Ideal.absNorm P: ℂ) ^ (-s)) =
        1 - (ℓ: ℂ) ^ (-(rp94 (p:=p) ℓ hℓp: ℂ) * s):= by
    intro P hP
    have hPmem: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K):= by
      have: (P: Ideal _) ∈
          (↑(IsDedekindDomain.primesOverFinset (rp79 ℓ) (𝓞 K)) : Set _) :=
        hP
      rwa [hcoe] at this
    have: P.IsPrime:=hPmem.1
    have: P.LiesOver (Ideal.span {(ℓ: ℤ)}):=hPmem.2
    have: P.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(ℓ: ℤ)})
    have habsNorm: Ideal.absNorm P = ℓ ^ (rp94 (p:=p) ℓ hℓp):= by
      rw [← rp114 p K hℓp P hPmem,
        ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(ℓ: ℤ)}) P]
      exact Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out: ℓ.Prime)
    rw [habsNorm]
    push_cast
    have:=Complex.natCast_cpow_natCast_mul ℓ (rp94 (p:=p) ℓ hℓp) (-s)
    rw [show -((rp94 (p:=p) ℓ hℓp: ℂ)) * s =
        ((rp94 (p:=p) ℓ hℓp: ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq,Finset.prod_const,hcard_eq]
lemma rp118 {s: ℂ} :
    rp87 K p s = 1 - (p: ℂ) ^ (-s):= by
  classical
  unfold rp87 rp80 rp79
  have hne: (Ideal.span {(p: ℤ)} : Ideal ℤ) ≠ ⊥:= by
    rw [Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe :=
    IsDedekindDomain.coe_primesOverFinset (p:=(Ideal.span {(p: ℤ)} : Ideal ℤ)) hne (𝓞 K)
  have hcard: (IsDedekindDomain.primesOverFinset
      (Ideal.span {(p: ℤ)} : Ideal ℤ) (𝓞 K)).card = 1:= by
    have hncard: ((Ideal.span {(p: ℤ)}).primesOver (𝓞 K)).ncard = 1:= by
      simpa [rp79] using rp112 (p:=p) (K:=K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨P,hP⟩:=Finset.card_eq_one.mp hcard
  rw [hP,Finset.prod_singleton]
  have hPmem: P ∈ (Ideal.span {(p: ℤ)}).primesOver (𝓞 K):= by
    rw [← hcoe,hP]
    exact Finset.mem_singleton_self P
  have: P.IsPrime:=hPmem.1
  have: P.LiesOver (Ideal.span {(p: ℤ)}):=hPmem.2
  have: P.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p: ℤ)})
  have habsNorm: Ideal.absNorm P = p ^ (1: ℕ):= by
    have hP' : P ∈ Ideal.primesOver (rp79 p) (𝓞 K):= by
      simpa [rp79] using hPmem
    rw [← rp113 (p:=p) (K:=K) P hP',
      ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p: ℤ)}) P]
    exact Ideal.absNorm_eq_pow_inertiaDeg' P hp.out
  rw [habsNorm]
  push_cast
  rw [pow_one]
end ZetaFactorisation
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
variable (p: ℕ) [hp: Fact p.Prime] (hp_odd: p ≠ 2)
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem rp119 :
    (h K: ℝ) =
      NumberField.dedekindZeta_residue K *
        (((Units.torsionOrder K: ℝ) * Real.sqrt |discr K|) /
          (2 ^ InfinitePlace.nrRealPlaces K *
            (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K)):= by
  let A: ℝ :=
    2 ^ InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K
  let B: ℝ:=(Units.torsionOrder K: ℝ) * Real.sqrt |discr K|
  have hA_pos: 0 < A:= by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos K)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA: A ≠ 0:=hA_pos.ne'
  have hB_pos: 0 < B:= by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos K
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  calc
    (h K: ℝ) = ((A * (h K: ℝ)) / B) * (B / A):= by
      field_simp [hA,hB_pos.ne']
    _ = NumberField.dedekindZeta_residue K * (B / A):= by
          dsimp [A,B]
          rw [NumberField.dedekindZeta_residue_def,KummerCriterion.h,NumberField.classNumber]
    _ = NumberField.dedekindZeta_residue K *
          (((Units.torsionOrder K: ℝ) * Real.sqrt |discr K|) /
            (2 ^ InfinitePlace.nrRealPlaces K *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K)):= by
          simp [A,B]
theorem rp120 :
    (hPlus K: ℝ) =
      NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) *
        (((Units.torsionOrder (NumberField.maximalRealSubfield K) : ℝ) *
            Real.sqrt |discr (NumberField.maximalRealSubfield K)|) /
          (2 ^ InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
            (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) *
              Units.regulator (NumberField.maximalRealSubfield K))):= by
  let L:=NumberField.maximalRealSubfield K
  let A: ℝ :=
    2 ^ InfinitePlace.nrRealPlaces L *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L
  let B: ℝ:=(Units.torsionOrder L: ℝ) * Real.sqrt |discr L|
  have hA_pos: 0 < A:= by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA: A ≠ 0:=hA_pos.ne'
  have hB_pos: 0 < B:= by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  calc
    (hPlus K: ℝ) = ((A * (hPlus K: ℝ)) / B) * (B / A):= by
      field_simp [hA,hB_pos.ne']
    _ = NumberField.dedekindZeta_residue L * (B / A):= by
          dsimp [A,B,L]
          rw [NumberField.dedekindZeta_residue_def,KummerCriterion.hPlus,NumberField.classNumber]
    _ = NumberField.dedekindZeta_residue L *
          (((Units.torsionOrder L: ℝ) * Real.sqrt |discr L|) /
            (2 ^ InfinitePlace.nrRealPlaces L *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L)):= by
          simp [A,B]
omit [IsCMField K] in
lemma rp121 :
    NumberField.InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) = 0 :=
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
      (K:=NumberField.maximalRealSubfield K)
lemma rp122 :
    NumberField.InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) = (p - 1) / 2:= by
  let L:=NumberField.maximalRealSubfield K
  calc
    NumberField.InfinitePlace.nrRealPlaces L = Module.finrank ℚ L:= by
      rw [← NumberField.IsTotallyReal.finrank (K:=L)]
    _ = (p - 1) / 2:= by
      rw [rp66 (p:=p) (K:=K)]
lemma rp123 :
    2 ^ NumberField.InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 1) / 2: ℕ):= by
  rw [rp121 (K:=K),pow_zero,mul_one,
    rp122 (p:=p) (K:=K)]
lemma rp124
    (x: NumberField.Units.torsion (NumberField.maximalRealSubfield K)) :
    (x: (𝓞 (NumberField.maximalRealSubfield K))ˣ) = 1 ∨
      (x: (𝓞 (NumberField.maximalRealSubfield K))ˣ) = -1:= by
  let L:=NumberField.maximalRealSubfield K
  let φ: L →+* ℂ:=Classical.choice inferInstance
  let hφ: ComplexEmbedding.IsReal φ :=
    NumberField.IsTotallyReal.complexEmbedding_isReal φ
  let u: (𝓞 L)ˣ:=x
  let r: ℝ:=hφ.embedding (u: L)
  have hur: ((r: ℂ)) = φ (u: L) :=
    hφ.coe_embedding_apply (u: L)
  have hu_fin: IsOfFinOrder u:=(CommGroup.mem_torsion u).1 x.prop
  obtain ⟨n,hn,hu_pow⟩:=isOfFinOrder_iff_pow_eq_one.mp hu_fin
  have hnorm: ‖φ (u: L)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one
      (by simpa [map_pow] using congrArg (fun z: (𝓞 L)ˣ => φ (z: L)) hu_pow)
      (Nat.ne_of_gt hn)
  have hr_norm: ‖(r: ℂ)‖ = 1:= by
    rwa [← hur] at hnorm
  have hr_abs: |r| = 1:= by
    simpa [Complex.norm_real] using hr_norm
  have hr_sq: r ^ 2 = 1:= by
    have hsquare:=congrArg (fun t: ℝ => t ^ 2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · left
    apply NumberField.Units.coe_injective (K:=L)
    apply φ.injective
    simpa [hr] using hur.symm
  · right
    apply NumberField.Units.coe_injective (K:=L)
    apply φ.injective
    simpa [hr] using hur.symm
lemma rp125 :
    Units.torsionOrder (NumberField.maximalRealSubfield K) = 2:= by
  let L:=NumberField.maximalRealSubfield K
  classical
  let:=Fintype.ofFinite (Units.torsion L)
  rw [Units.torsionOrder,Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2
    ⟨1,⟨-1,neg_one_mem_torsion⟩,by simp [← Subtype.coe_ne_coe],
      Finset.ext fun x ↦ ⟨fun _ ↦ ?_,fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert,Finset.mem_singleton,← Subtype.val_inj,← Subtype.val_inj]
  exact rp124 (K:=K) x
lemma rp126 (hp_odd' : p ≠ 2) :
    Units.torsionOrder K = 2 * p:= by
  have hneven: ¬ Even p:=fun h =>
    hp_odd' ((hp.out.even_iff).mp h)
  simpa [hneven,two_mul] using
    (IsCyclotomicExtension.Rat.torsionOrder_eq (n:=p) (K:=K))
lemma rp127 :
    Units.rank K = (p - 3) / 2:= by
  let L:=NumberField.maximalRealSubfield K
  rw [← NumberField.IsCMField.units_rank_eq_units_rank (K:=K),Units.rank]
  calc
    Fintype.card (NumberField.InfinitePlace L) - 1
        = NumberField.InfinitePlace.nrRealPlaces L - 1:= by
            rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
              NumberField.IsTotallyReal.nrComplexPlaces_eq_zero,add_zero]
    _ = Module.finrank ℚ L - 1:= by
          rw [← NumberField.IsTotallyReal.finrank (K:=L)]
    _ = (p - 1) / 2 - 1:= by
          rw [rp66 (p:=p) (K:=K)]
    _ = (p - 3) / 2:= by omega
lemma rp128 (hp_odd' : p ≠ 2) :
    Units.regulator K / Units.regulator (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 3) / 2: ℕ):= by
  rw [NumberField.IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv (K:=K),
    rp67 (p:=p) (K:=K) (hp_odd:=hp_odd'),
    rp127 (p:=p) (K:=K)]
  simp
lemma rp129 :
    |((NumberField.discr K: ℤ) : ℝ)| = (p: ℝ) ^ (p - 2):= by
  rw [IsCyclotomicExtension.Rat.discr_prime (p:=p) (K:=K)]
  rw [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,abs_mul,abs_pow,abs_neg,
    abs_one,one_pow]
  simp [abs_of_nonneg (show 0 ≤ ((p: ℝ) ^ (p - 2)) by positivity)]
lemma rp130 (hp_odd' : p ≠ 2) :
    IsCyclotomicExtension.zeta p ℚ K ∉ NumberField.maximalRealSubfield K:= by
  classical
  let ζ: K:=IsCyclotomicExtension.zeta p ℚ K
  have hζ: IsPrimitiveRoot ζ p:=IsCyclotomicExtension.zeta_spec p ℚ K
  intro hmem
  have hfix:=(NumberField.mem_maximalRealSubfield_iff (K:=K) ζ).mp hmem
  let φ: K →+* ℂ:=Classical.choice inferInstance
  have hstar: star (φ ζ) = φ ζ:=hfix φ
  have hpow: (φ ζ) ^ p = 1:= by
    simpa [map_pow] using congrArg φ hζ.pow_eq_one
  have hnorm: ‖φ ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow hp.out.ne_zero
  have him: (φ ζ).im = 0:= by
    simpa [RCLike.star_def] using (Complex.conj_eq_iff_im.mp hstar)
  let r: ℝ:=(φ ζ).re
  have hreal: φ ζ = (r: ℂ):= by
    apply Complex.ext <;> simp [r,him]
  rw [hreal] at hnorm
  have hr_abs: |r| = 1:= by
    simpa [Complex.norm_real] using hnorm
  have hr_sq: r ^ 2 = 1:= by
    have hsquare:=congrArg (fun t: ℝ => t ^ 2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · have hφζ: φ ζ = 1:= by
      calc
        φ ζ = (r: ℂ):=hreal
        _ = (1: ℂ):= by simp [hr]
    have hζeq: ζ = 1:=φ.injective <| by simpa using hφζ
    exact (hζ.ne_one hp.out.one_lt) hζeq
  · have hφζ: φ ζ = -1:= by
      calc
        φ ζ = (r: ℂ):=hreal
        _ = (-1: ℂ):= by simp [hr]
    have hpo: Odd p:=hp.out.odd_of_ne_two hp_odd'
    have: ((-1: ℂ) ^ p) = 1:= by simpa [hφζ] using hpow
    have hneg: (-1: ℂ) = 1:= by simpa [Odd.neg_one_pow hpo] using this
    have hneq: (-1: ℂ) ≠ 1:= by norm_num
    exact hneq hneg
lemma rp131 (hp_odd' : p ≠ 2) :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) : K) ∉
      Set.range (algebraMap (NumberField.maximalRealSubfield K) K):= by
  rintro ⟨x,hx⟩
  have hxmem: (algebraMap (NumberField.maximalRealSubfield K) K x) ∈
      NumberField.maximalRealSubfield K:=x.2
  have hzmem: (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) : K) ∈
      NumberField.maximalRealSubfield K:= by
    simpa [hx] using hxmem
  exact rp130 (p:=p) (K:=K) hp_odd' hzmem
lemma rp132 (hp_odd' : p ≠ 2) :
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ∉
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)):= by
  rintro ⟨x,hx⟩
  apply rp131 (p:=p) (K:=K) hp_odd'
  refine ⟨(x: NumberField.maximalRealSubfield K),?_⟩
  exact congrArg (fun y: 𝓞 K => (y: K)) hx
lemma rp133 (hp_odd' : p ≠ 2) :
    Algebra.adjoin (NumberField.maximalRealSubfield K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) : K)} : Set K) = ⊤:= by
  let L: IntermediateField (NumberField.maximalRealSubfield K) K :=
    IntermediateField.adjoin (NumberField.maximalRealSubfield K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) : K)} : Set K)
  have hL: L = ⊤:= by
    have hprime: Nat.Prime (Module.finrank (NumberField.maximalRealSubfield K) K):= by
      simpa [rp65 (K:=K)] using Nat.prime_two
    have hsimple :=
      ((IntermediateField.isSimpleOrder_of_finrank_prime (NumberField.maximalRealSubfield K) K
          hprime).eq_bot_or_eq_top L)
    refine hsimple.resolve_left ?_
    intro hbot
    have hzeta_mem: (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) : K) ∈ L :=
      IntermediateField.subset_adjoin _ _ (by simp)
    rw [hbot,IntermediateField.mem_bot] at hzeta_mem
    exact rp131 (p:=p) (K:=K) hp_odd' hzeta_mem
  have hzeta_alg: IsAlgebraic (NumberField.maximalRealSubfield K)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) : K)) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact Algebra.adjoin_eq_top_of_primitive_element hzeta_alg hL
lemma rp134 (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K)):= by
  have h :=
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.geom_sum_isUnit
      hp.out.two_le (Nat.coprime_two_left.mpr (hp.out.odd_of_ne_two hp_odd'))
  simpa [Finset.sum_range_succ] using h
lemma rp135 :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) ^ (p - 1) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) = 1 :=
  rp33 p K
lemma rp136 :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) : 𝓞 K) = 1:= by
  simpa [mul_comm] using rp135 (p:=p) (K:=K)
lemma rp137 (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) ^ (p - 1)):= by
  let ζi: 𝓞 K:=(IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hzeta_unit: IsUnit (ζi ^ (p - 1) : 𝓞 K):= by
    simpa using! (IsCyclotomicExtension.zeta_spec p ℚ K).unit'.isUnit.pow (p - 1)
  have hmul: (ζi ^ (p - 1) : 𝓞 K) * (1 + ζi) = 1 + ζi ^ (p - 1):= by
    rw [mul_add,mul_one,rp135 (p:=p) (K:=K)]
    ring
  rw [← hmul]
  exact hzeta_unit.mul (rp134 (p:=p) (K:=K) hp_odd')
lemma rp138 :
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) (piPlus p K) =
      (2: 𝓞 K) - (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1):= by
  let ζi: 𝓞 K:=(IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [rp41]
  have hconj: NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1) =
      ζi ^ (p - 1) - 1:= by
    rw [map_sub,map_one,rp37]
  calc
    (ζi - 1) * NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1)
        = (ζi - 1) * (ζi ^ (p - 1) - 1):= by rw [hconj]
    _ = ζi * ζi ^ (p - 1) - ζi - ζi ^ (p - 1) + 1:= by
          ring
    _ = (2: 𝓞 K) - ζi - ζi ^ (p - 1):= by
          rw [rp136 (p:=p) (K:=K)]
          ring_nf
lemma rp139 :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (NumberField.maximalRealSubfield K))) = 0:= by
  let ζi: 𝓞 K:=(IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hcalc :
      ζi ^ 2 + (((2: 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1 = 0:= by
    calc
      ζi ^ 2 + (((2: 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1
          = -(ζi ^ (p - 1) * ζi) + 1:= by ring
      _ = 0:= by
            rw [rp135 (p:=p) (K:=K)]
            norm_num
  simpa [Polynomial.aeval_def,rp138,
    pow_two,map_sub,add_assoc,add_left_comm,add_comm,mul_assoc,mul_left_comm,mul_comm]
    using! hcalc
lemma rp140 (hp_odd' : p ≠ 2) :
    minpoly (𝓞 (NumberField.maximalRealSubfield K))
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) =
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (NumberField.maximalRealSubfield K))):= by
  let A:=𝓞 (NumberField.maximalRealSubfield K)
  let ζi: 𝓞 K:=(IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hint: IsIntegral A ζi:=IsIntegralClosure.isIntegral A K ζi
  have hdeg :
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree ≤
        (minpoly A ζi).degree:= by
    have hnatdeg: 2 ≤ (minpoly A ζi).natDegree :=
      (minpoly.two_le_natDegree_iff hint).2
        (rp132 (p:=p) (K:=K) hp_odd')
    have hpoly_deg :
        (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree = 2:= by
      simpa [one_mul,Polynomial.C_1] using
        (Polynomial.degree_quadratic
          (R:=A)
          (a:=(1: A))
          (b:=piPlus p K - 2)
          (c:=(1: A))
          one_ne_zero)
    rw [hpoly_deg,Polynomial.degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast hnatdeg
  symm
  refine IsIntegrallyClosed.minpoly.unique (R:=A) (S:=𝓞 K) (s:=ζi) ?_ ?_ ?_
  · simpa [Polynomial.C_1] using
      (Polynomial.isMonicOfDegree_add_add_two (a:=piPlus p K - 2) (b:=(1: A))).monic
  · exact rp139 (p:=p) (K:=K)
  · intro Q hQ hQroot
    exact hdeg.trans (minpoly.min (A:=A) (x:=ζi) hQ hQroot)
lemma rp141 (hp_odd' : p ≠ 2) :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.derivative
        (minpoly (𝓞 (NumberField.maximalRealSubfield K))
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K))) =
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1):= by
  let ζi: 𝓞 K:=(IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have htwo :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) 2 = (2: 𝓞 K):= by
    simpa using map_natCast (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) 2
  rw [rp140 (p:=p) (K:=K) hp_odd']
  simpa [Polynomial.aeval_def,rp138,
    map_sub,htwo,add_assoc,add_left_comm,add_comm,mul_assoc,mul_left_comm,
    mul_comm] using
    (show ((1 + 1: 𝓞 K) * ζi) + (((2: 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) =
        ζi - ζi ^ (p - 1) by ring)
lemma rp142 (hp_odd' : p ≠ 2) :
    Ideal.span
        ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: 𝓞 K) -
            (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1)} :
          Set (𝓞 K)) =
      rp34 p K:= by
  let ζi: 𝓞 K:=(IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [rp34]
  have hcalc :
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - ζi ^ (p - 1):= by
    have hmul: ζi * ζi ^ (p - 1) = 1:=rp136 (p:=p) (K:=K)
    calc
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - 1 + (ζi * ζi ^ (p - 1) - ζi ^ (p - 1)):= by
        ring
      _ = ζi - ζi ^ (p - 1):= by
        rw [hmul]
        ring
  rw [← hcalc,Ideal.span_singleton_mul_right_unit]
  exact rp137 (p:=p) (K:=K) hp_odd'
lemma rp143 (hp_odd' : p ≠ 2) :
    differentIdeal (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) = rp34 p K:= by
  let A:=𝓞 (NumberField.maximalRealSubfield K)
  let B:=𝓞 K
  let PPlus: Ideal A:=rp36 p K
  let P: Ideal B:=rp34 p K
  have hPPlus0: PPlus ≠ ⊥:= by
    intro hbot
    have hmap: Ideal.map (algebraMap A B) PPlus = P ^ 2:= by
      simpa [A,B,PPlus,P] using rp44 (p:=p) (hp_odd:=hp_odd') (K:=K)
    rw [hbot,Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 (rp35 p K)) hmap.symm
  have hle: differentIdeal A B ≤ P:= by
    have: PPlus.IsMaximal:=Ideal.IsPrime.isMaximal inferInstance hPPlus0
    have hdiv: P ∣ differentIdeal A B:= by
      have hpow: P ^ 2 ∣ Ideal.map (algebraMap A B) PPlus:= by
        rw [rp44 (p:=p) (hp_odd:=hp_odd') (K:=K)]
      simpa [A,B,P,PPlus] using
        (pow_sub_one_dvd_differentIdeal (A:=A) (B:=B) (p:=PPlus) P 2 hPPlus0 hpow)
    exact Ideal.dvd_iff_le.mp hdiv
  have hmem :
      Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
          (Polynomial.derivative
            (minpoly A ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger: B))) ∈
        differentIdeal A B :=
    aeval_derivative_mem_differentIdeal (A:=A)
      (K:=NumberField.maximalRealSubfield K) (L:=K) (B:=B)
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger)
      (rp133 (p:=p) (K:=K) hp_odd')
  have hP_le: P ≤ differentIdeal A B:= by
    change rp34 p K ≤ differentIdeal A B
    rw [← rp142 (p:=p) (K:=K) hp_odd']
    rw [Ideal.span_singleton_le_iff_mem]
    convert hmem using 1
    symm
    exact rp141
      (p:=p) (K:=K) hp_odd'
  exact le_antisymm hle hP_le
lemma rp144 (hp_odd' : p ≠ 2) :
    Ideal.absNorm (differentIdeal (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = p:= by
  rw [rp143 (p:=p) (K:=K) hp_odd',
    rp34]
  rw [Ideal.absNorm_span_singleton,
    (IsCyclotomicExtension.zeta_spec p ℚ K).norm_toInteger_sub_one_of_prime_ne_two' hp_odd']
  simp [Int.natAbs_natCast]
lemma rp145 (hp_odd' : p ≠ 2) :
    (NumberField.discr (NumberField.maximalRealSubfield K)).natAbs = p ^ ((p - 3) / 2):= by
  let L:=NumberField.maximalRealSubfield K
  have hmain:=NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K:=L) (𝒪:=𝓞 L) (L:=K) (𝒪':=𝓞 K)
  have hdiscrK: (NumberField.discr K).natAbs = p ^ (p - 2):= by
    rw [IsCyclotomicExtension.Rat.discr_prime (p:=p) (K:=K)]
    simp [Int.natAbs_mul]
  have hfin: Module.finrank L K = 2:= by
    simpa [L] using (rp65 (K:=K))
  have hp3: 3 ≤ p:= by
    have hp2: 2 ≤ p:=hp.out.two_le
    omega
  rw [hdiscrK,rp144 (p:=p)
      (K:=K) hp_odd'] at hmain
  have hmain2: p ^ (p - 2) = p * (NumberField.discr L).natAbs ^ 2:= by
    conv_rhs => rw [← hfin]
    exact hmain
  have hsq: (NumberField.discr L).natAbs ^ 2 = p ^ (p - 3):= by
    have hmain' : p * p ^ (p - 3) = p * (NumberField.discr L).natAbs ^ 2:= by
      calc
        p * p ^ (p - 3) = p ^ (p - 2):= by
          rw [show p - 2 = (p - 3) + 1 by omega,pow_succ',mul_comm]
        _ = p * (NumberField.discr L).natAbs ^ 2:=hmain2
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hmain'.symm
  have hpow: (p ^ ((p - 3) / 2)) ^ 2 = p ^ (p - 3):= by
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n,hn⟩
    have hdiv: (p - 3) / 2 = n - 1:= by
      rw [hn,show 2 * n + 1 - 3 = 2 * (n - 1) by omega,
        Nat.mul_div_right _ (by decide: 0 < 2)]
    calc
      (p ^ ((p - 3) / 2)) ^ 2 = (p ^ (n - 1)) ^ 2:= by rw [hdiv]
      _ = p ^ ((n - 1) * 2):= by rw [← pow_mul]
      _ = p ^ (p - 3):= by
            congr
            rw [hn]
            omega
  have hsq' : (NumberField.discr L).natAbs ^ 2 = (p ^ ((p - 3) / 2)) ^ 2:= by
    rw [hpow,hsq]
  have:=congrArg Nat.sqrt hsq'
  simpa [Nat.sqrt_eq'] using this
lemma rp146 (hp_odd' : p ≠ 2) :
    |((NumberField.discr (NumberField.maximalRealSubfield K) : ℤ) : ℝ)| =
      (p: ℝ) ^ ((p - 3) / 2):= by
  have habs: (((NumberField.discr (NumberField.maximalRealSubfield K)).natAbs: ℕ) : ℝ) =
      |((NumberField.discr (NumberField.maximalRealSubfield K) : ℤ) : ℝ)|:= by
    convert
      (Nat.cast_natAbs (α:=ℝ) (NumberField.discr (NumberField.maximalRealSubfield K))) using 1
    simp
  rw [← habs,rp145 (p:=p) (K:=K) hp_odd',Nat.cast_pow]
theorem rp147 (hp_odd' : p ≠ 2) :
    (h K: ℝ) =
      NumberField.dedekindZeta_residue K *
        ((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ (p - 2))) /
          ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K)):= by
  have hp_gt2: 2 < p:=lt_of_le_of_ne hp.out.two_le (by simpa using hp_odd'.symm)
  have hreal: NumberField.InfinitePlace.nrRealPlaces K = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n:=p) (K:=K) hp_gt2
  have hcomplex: NumberField.InfinitePlace.nrComplexPlaces K = (p - 1) / 2:= by
    simpa [Nat.totient_prime hp.out] using
      (IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n:=p) (K:=K))
  rw [rp119 (K:=K),hreal,hcomplex,
    rp126 (p:=p) (K:=K) hp_odd',
    rp129 (p:=p) (K:=K)]
  simp [mul_assoc,mul_comm]
end KummerCriterion
end

section
noncomputable section
open NumberField
namespace KummerCriterion
section Factors
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
def rp148: ℂ :=
  (((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ (p - 2))) /
    ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K) : ℝ) : ℂ)
lemma rp149 (hp_odd' : p ≠ 2) :
    ((h K: ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue K: ℝ) : ℂ) *
        rp148 (p:=p) (K:=K):= by
  simpa [rp148] using congrArg (fun x: ℝ => (x: ℂ))
    (rp147 (p:=p) (K:=K) hp_odd')
def rp150: ℂ :=
  (((((Units.torsionOrder (NumberField.maximalRealSubfield K) : ℝ) *
      Real.sqrt |discr (NumberField.maximalRealSubfield K)|) /
    (2 ^ InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) *
        Units.regulator (NumberField.maximalRealSubfield K)) : ℝ) : ℂ))
lemma rp151 :
    ((hPlus K: ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) *
        rp150 (K:=K):= by
  simpa [rp150] using congrArg (fun x: ℝ => (x: ℂ))
    (rp120 (K:=K))
theorem rp152 (hp_odd' : p ≠ 2) :
    rp150 (K:=K) =
      (((((2: ℝ) * Real.sqrt ((p: ℝ) ^ ((p - 3) / 2))) /
        (2 ^ ((p - 1) / 2: ℕ) * Units.regulator (NumberField.maximalRealSubfield K)) : ℝ) :
        ℂ)):= by
  rw [rp150]
  congr 1
  rw [rp125 (K:=K),
    rp123 (p:=p) (K:=K),
    rp146 (p:=p) (K:=K) hp_odd']
  norm_num
theorem rp153
    {KplusResidue: ℂ}
    (hresPlus :
      ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) =
        KplusResidue) :
    ((hPlus K: ℕ) : ℂ) =
      rp150 (K:=K) * KplusResidue:= by
  rw [rp151 (K:=K),hresPlus]
  ring
omit [IsCMField K] in
lemma rp154 :
  rp150 (K:=K) ≠ 0:= by
  let L:=NumberField.maximalRealSubfield K
  let A: ℝ :=
    2 ^ InfinitePlace.nrRealPlaces L *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L
  let B: ℝ:=(Units.torsionOrder L: ℝ) * Real.sqrt |discr L|
  have hA_pos: 0 < A:= by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hB_pos: 0 < B:= by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  have hq_pos: 0 < B / A:=div_pos hB_pos hA_pos
  change (((B / A: ℝ) : ℂ) ≠ 0)
  exact_mod_cast hq_pos.ne'
def rp155: ℂ :=
  rp148 (p:=p) (K:=K) /
    rp150 (K:=K)
theorem rp156
    (hp_odd' : p ≠ 2) :
    rp155 (p:=p) (K:=K) =
      ((((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ (p - 2))) /
        ((2 * Real.pi) ^ ((p - 1) / 2) * Real.sqrt ((p: ℝ) ^ ((p - 3) / 2))) : ℝ) : ℂ)):= by
  let L:=NumberField.maximalRealSubfield K
  have hLreg_ne: Units.regulator L ≠ 0 :=
    (Units.regulator_pos L).ne'
  have hp_pos: 0 < (p: ℝ):= by
    exact_mod_cast hp.out.pos
  have hsqrt_pos: 0 < Real.sqrt ((p: ℝ) ^ ((p - 3) / 2)) :=
    Real.sqrt_pos.2 <| pow_pos hp_pos _
  have hsqrt_ne: Real.sqrt ((p: ℝ) ^ ((p - 3) / 2)) ≠ 0:=hsqrt_pos.ne'
  have hpow_pi_ne: ((2 * Real.pi) ^ ((p - 1) / 2: ℕ) : ℝ) ≠ 0:= by
    positivity
  have hpow_two_ne: (2: ℝ) ^ ((p - 3) / 2: ℕ) ≠ 0:= by
    positivity
  have hreg :
      Units.regulator K =
        (2: ℝ) ^ ((p - 3) / 2: ℕ) * Units.regulator L :=
    (div_eq_iff hLreg_ne).mp <| by
      simpa [L] using
        (rp128 (p:=p) (K:=K) hp_odd' : _)
  have hexp: ((p - 1) / 2: ℕ) = ((p - 3) / 2) + 1:= by
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n,hn⟩
    have hp3: 3 ≤ p:= by
      have hp2: 2 ≤ p:=hp.out.two_le
      omega
    have hn_pos: 0 < n:= by
      rw [hn] at hp3
      omega
    have hdiv1: (p - 1) / 2 = n:= by
      rw [hn,show 2 * n + 1 - 1 = 2 * n by omega,
        Nat.mul_div_right _ (by decide: 0 < 2)]
    have hdiv2: (p - 3) / 2 = n - 1:= by
      rw [hn,show 2 * n + 1 - 3 = 2 * (n - 1) by omega,
        Nat.mul_div_right _ (by decide: 0 < 2)]
    rw [hdiv1,hdiv2]
    exact (Nat.sub_add_cancel (n:=n) (m:=1) (Nat.succ_le_of_lt hn_pos)).symm
  have hpow_two :
      (2: ℝ) ^ ((p - 1) / 2: ℕ) =
        2 * (2: ℝ) ^ ((p - 3) / 2: ℕ):= by
    rw [hexp,pow_succ]
    ring
  rw [rp155,rp148,
    rp152 (p:=p) (K:=K) hp_odd']
  suffices hreal :
      ((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ (p - 2))) /
          ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K)) /
        (((2: ℝ) * Real.sqrt ((p: ℝ) ^ ((p - 3) / 2))) /
          (2 ^ ((p - 1) / 2: ℕ) * Units.regulator L)) =
      ((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ (p - 2))) /
        ((2 * Real.pi) ^ ((p - 1) / 2) * Real.sqrt ((p: ℝ) ^ ((p - 3) / 2))) : ℝ) by
    simpa [Complex.ofReal_div] using congrArg (fun x: ℝ => (x: ℂ)) hreal
  rw [hreg,hpow_two]
  field_simp [hLreg_ne,hsqrt_ne,hpow_pi_ne,hpow_two_ne]
theorem rp157
    (hp_odd' : p ≠ 2) :
    rp155 (p:=p) (K:=K) =
      ((((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ ((p - 1) / 2))) /
        (2 * Real.pi) ^ ((p - 1) / 2) : ℝ) : ℂ)):= by
  let a: ℕ:=(p - 1) / 2
  let b: ℕ:=(p - 3) / 2
  have hp_pos: 0 < (p: ℝ):= by
    exact_mod_cast hp.out.pos
  have hpowA_nonneg: 0 ≤ (p: ℝ) ^ a:= by
    positivity
  have hsqrtB_ne: Real.sqrt ((p: ℝ) ^ b) ≠ 0 :=
    Real.sqrt_ne_zero'.2 <| pow_pos hp_pos _
  have hpow_pi_ne: ((2 * Real.pi) ^ a: ℝ) ≠ 0:= by
    positivity
  have hsplit_exp: p - 2 = a + b:= by
    dsimp [a,b]
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n,hn⟩
    rw [hn]
    omega
  have hsqrt_split :
      Real.sqrt ((p: ℝ) ^ (p - 2)) =
        Real.sqrt ((p: ℝ) ^ a) * Real.sqrt ((p: ℝ) ^ b):= by
    rw [hsplit_exp,pow_add,Real.sqrt_mul hpowA_nonneg]
  suffices hreal :
      ((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ (p - 2))) /
          ((2 * Real.pi) ^ a * Real.sqrt ((p: ℝ) ^ b))) =
        ((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ a)) / (2 * Real.pi) ^ a: ℝ) by
    rw [rp156 (p:=p) (K:=K) hp_odd']
    simpa [a,b,Complex.ofReal_div] using congrArg (fun x: ℝ => (x: ℂ)) hreal
  rw [hsqrt_split]
  field_simp [hsqrtB_ne,hpow_pi_ne]
abbrev rp158: ℂ :=
  rp150 (K:=K)
omit hp [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
lemma rp159 :
    rp148 (p:=p) (K:=K) =
      rp155 (p:=p) (K:=K) *
        rp158 (K:=K):= by
  symm
  rw [rp155,rp158,div_eq_mul_inv,mul_assoc,
    inv_mul_cancel₀ (rp154 (K:=K)),mul_one]
end Factors
end KummerCriterion
end

section
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p: ℕ) [hp: Fact p.Prime]
lemma rp160 {a: ZMod p} (ha: a ≠ 0) :
    (a.val / p: ℝ) ∈ Set.Ioo 0 1:= by
  have hp_pos: 0 < p:=hp.out.pos
  have hval_pos: 0 < a.val:= by
    by_contra h
    have hval_zero: a.val = 0:=Nat.eq_zero_of_not_pos h
    exact ha <| (ZMod.val_eq_zero a).mp hval_zero
  refine Set.mem_Ioo.mpr ⟨?_,?_⟩
  · exact div_pos (Nat.cast_pos.mpr hval_pos) (Nat.cast_pos.mpr hp_pos)
  · exact (div_lt_one (Nat.cast_pos.mpr hp_pos)).2 <| Nat.cast_lt.mpr (ZMod.val_lt a)
lemma rp161 (a: ZMod p) (s: ℂ) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) s = HurwitzZeta.sinZeta (a.val / p: ℝ) s:= by
  rw [ZMod.toAddCircle_apply]
lemma rp162 (t: ℝ) :
    (1: ℂ) - Complex.exp (t * Complex.I) =
      (2 * Real.sin (t / 2) : ℝ) *
        (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I):= by
  calc
    (1: ℂ) - Complex.exp (t * Complex.I)
        = ((1 - Real.cos t: ℝ) : ℂ) + (-Real.sin t: ℝ) * Complex.I:= by
            rw [Complex.exp_ofReal_mul_I]
            simp [sub_eq_add_neg,add_comm,add_left_comm,add_assoc]
    _ = ((2 * Real.sin (t / 2) ^ 2: ℝ) : ℂ) +
          (-(2 * Real.sin (t / 2) * Real.cos (t / 2)) : ℝ) * Complex.I:= by
            rw [show t = 2 * (t / 2) by ring,Real.cos_two_mul,Real.sin_two_mul]
            have hsq: 1 - (2 * Real.cos (t / 2) ^ 2 - 1) = 2 * Real.sin (t / 2) ^ 2:= by
              nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
            rw [hsq]
            ring_nf
    _ = (2 * Real.sin (t / 2) : ℝ) *
          (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I):= by
            simp [Real.cos_sub_pi_div_two,Real.sin_sub_pi_div_two,sq]
            ring
lemma rp163 {t: ℝ} (ht₀: 0 < t) (ht₂π: t < 2 * Real.pi) :
    Complex.arg ((1: ℂ) - Complex.exp (t * Complex.I)) = t / 2 - Real.pi / 2:= by
  have hs: 0 < 2 * Real.sin (t / 2):= by
    have hhalf: 0 < t / 2 ∧ t / 2 < Real.pi:= by
      constructor <;> nlinarith [ht₀,ht₂π,Real.pi_pos]
    have hsin: 0 < Real.sin (t / 2):=Real.sin_pos_of_mem_Ioo hhalf
    positivity
  have hθ: t / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi:= by
    constructor
    · nlinarith [ht₀,Real.pi_pos]
    · nlinarith [ht₂π]
  rw [rp162]
  simpa using (Complex.arg_mul_cos_add_sin_mul_I hs hθ)
lemma rp164 {t: ℝ} (ht₀: 0 < t) (ht₂π: t < 2 * Real.pi) :
    (-Complex.log ((1: ℂ) - Complex.exp (t * Complex.I))).im = Real.pi / 2 - t / 2:= by
  rw [show (-Complex.log ((1: ℂ) - Complex.exp (t * Complex.I))).im =
      -(Complex.log ((1: ℂ) - Complex.exp (t * Complex.I))).im by simp]
  rw [Complex.log_im,rp163 ht₀ ht₂π]
  ring
lemma rp165 (x r: ℝ) (hr₀: 0 ≤ r) (hr₁: r < 1) :
    HasSum (fun n: ℕ => (r ^ n / n) * Real.sin (2 * Real.pi * x * n))
      (-Complex.log ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im:= by
  let z: ℂ:=(r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz: ‖z‖ < 1:= by
    have hexp: ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ = 1:= by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
    have hz' : ‖z‖ = r:= by
      calc
        ‖z‖ = ‖(r: ℂ)‖ * ‖Complex.exp (2 * Real.pi * x * Complex.I)‖:= by
          simp [z]
        _ = r * 1:= by rw [Complex.norm_real,Real.norm_of_nonneg hr₀,hexp]
        _ = r:= by ring
    rw [hz']
    exact hr₁
  refine (Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)).congr_fun ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [z]
  · rw [show z = (r: ℂ) * Complex.exp ((2 * Real.pi * x: ℝ) * Complex.I) by simp [z]]
    rw [Complex.div_natCast_im,mul_pow,Complex.mul_im,← Complex.ofReal_pow,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,← Complex.exp_nat_mul]
    rw [show (n: ℂ) * ((2 * Real.pi * x: ℝ) * Complex.I) =
        ((2 * Real.pi * x * n: ℝ) : ℂ) * Complex.I by
          norm_num
          ring]
    rw [Complex.exp_ofReal_mul_I_im]
    ring
lemma rp166 (x r: ℝ) (hr₀: 0 ≤ r) (hr₁: r < 1) :
    HasSum (fun n: ℕ => (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
      (-Real.log ‖(1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖):= by
  let z: ℂ:=(r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz: ‖z‖ < 1:= by
    have hexp: ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ = 1:= by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
    have hz' : ‖z‖ = r:= by
      calc
        ‖z‖ = ‖(r: ℂ)‖ * ‖Complex.exp (2 * Real.pi * x * Complex.I)‖:= by
          simp [z]
        _ = r * 1:= by rw [Complex.norm_real,Real.norm_of_nonneg hr₀,hexp]
        _ = r:= by ring
    rw [hz']
    exact hr₁
  have hsum :
      HasSum (fun n: ℕ => (z ^ n / n).re) (-Complex.log ((1: ℂ) - z)).re :=
    (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz))
  have hsum' :
      HasSum (fun n: ℕ => (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
        (-Complex.log ((1: ℂ) - z)).re:= by
    refine hsum.congr_fun ?_
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [z]
    · rw [show z = (r: ℂ) * Complex.exp ((2 * Real.pi * x: ℝ) * Complex.I) by simp [z]]
      rw [Complex.div_natCast_re,mul_pow,Complex.mul_re,← Complex.ofReal_pow,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,← Complex.exp_nat_mul]
      rw [show (n: ℂ) * ((2 * Real.pi * x: ℝ) * Complex.I) =
          ((2 * Real.pi * x * n: ℝ) : ℂ) * Complex.I by
            norm_num
            ring]
      rw [Complex.exp_ofReal_mul_I_re]
      ring
  have hvalue: (-Complex.log ((1: ℂ) - z)).re = -Real.log ‖(1: ℂ) - z‖:= by
    simpa using congrArg Neg.neg (Complex.log_re ((1: ℂ) - z))
  simpa [hvalue,z] using hsum'
lemma rp167 {t: ℝ} (ht₀: 0 < t) (ht₂π: t < 2 * Real.pi) :
    ‖(1: ℂ) - Complex.exp (t * Complex.I)‖ = 2 * Real.sin (t / 2):= by
  have hs: 0 < 2 * Real.sin (t / 2):= by
    have hhalf: 0 < t / 2 ∧ t / 2 < Real.pi:= by
      constructor <;> nlinarith [ht₀,ht₂π,Real.pi_pos]
    have hsin: 0 < Real.sin (t / 2):=Real.sin_pos_of_mem_Ioo hhalf
    positivity
  calc
    ‖(1: ℂ) - Complex.exp (t * Complex.I)‖
        = ‖((2 * Real.sin (t / 2) : ℝ) : ℂ)‖ *
            ‖Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I‖:= by
              rw [rp162,Complex.norm_mul]
    _ = |2 * Real.sin (t / 2)| * 1:= by
          rw [Complex.norm_real,Real.norm_eq_abs]
          have hunit :
              ‖Real.cos (t / 2 - Real.pi / 2) +
                  Real.sin (t / 2 - Real.pi / 2) * Complex.I‖ = 1:= by
            simpa using Complex.norm_cos_add_sin_mul_I (t / 2 - Real.pi / 2)
          rw [hunit]
    _ = 2 * Real.sin (t / 2):= by rw [abs_of_pos hs,mul_one]
end LValueAtOne
end KummerCriterion
end

section
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
lemma rp168
    {E: Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a: ℕ → ℝ} {z: ℕ → E} {B: ℝ}
    (ha: Antitone a) (ha_nonneg: ∀ n,0 ≤ a n)
    (hbound: ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤ B) (n: ℕ) :
    ‖∑ i ∈ Finset.range n,a i • z i‖ ≤ B * a 0:= by
  have hB: 0 ≤ B:= by
    simpa using hbound 0
  rcases n.eq_zero_or_pos with rfl | hn
  · have: 0 ≤ B * a 0:=mul_nonneg hB (ha_nonneg 0)
    simpa using this
  · rw [Finset.sum_range_by_parts (f:=a) (g:=z) (n:=n)]
    have hsum_le :
        ‖∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j‖ ≤
          B * (a 0 - a (n - 1)):= by
      calc
        ‖∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j‖
            ≤ ∑ i ∈ Finset.range (n - 1),
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j‖:= by
              simpa using norm_sum_le (Finset.range (n - 1))
                (fun i => (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j)
        _ ≤ ∑ i ∈ Finset.range (n - 1),B * (a i - a (i + 1)):= by
              refine Finset.sum_le_sum fun i hi => ?_
              have hdiff_nonpos: a (i + 1) - a i ≤ 0:=sub_nonpos.mpr (ha (Nat.le_succ i))
              calc
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j‖
                    = |a (i + 1) - a i| * ‖∑ j ∈ Finset.range (i + 1),z j‖:= by
                        rw [norm_smul,Real.norm_eq_abs]
                _ = (a i - a (i + 1)) * ‖∑ j ∈ Finset.range (i + 1),z j‖:= by
                      rw [abs_of_nonpos hdiff_nonpos]
                      ring
                _ ≤ (a i - a (i + 1)) * B:= by
                      gcongr
                      · exact sub_nonneg.mpr (ha (Nat.le_succ i))
                      · exact hbound (i + 1)
                _ = B * (a i - a (i + 1)):= by ring
        _ = B * (a 0 - a (n - 1)):= by
              rw [← Finset.mul_sum]
              have htel':=Finset.sum_range_sub (f:=a) (n:=n - 1)
              have htel: ∑ i ∈ Finset.range (n - 1),(a i - a (i + 1)) = a 0 - a (n - 1):= by
                calc
                  ∑ i ∈ Finset.range (n - 1),(a i - a (i + 1))
                      = ∑ i ∈ Finset.range (n - 1),-((a (i + 1) - a i)):= by
                          refine Finset.sum_congr rfl fun i hi => by ring
                  _ = -∑ i ∈ Finset.range (n - 1),(a (i + 1) - a i):= by
                        rw [Finset.sum_neg_distrib]
                  _ = a 0 - a (n - 1):= by linarith
              rw [htel]
    have hfirst: ‖a (n - 1) • ∑ i ∈ Finset.range n,z i‖ ≤ B * a (n - 1):= by
      calc
        ‖a (n - 1) • ∑ i ∈ Finset.range n,z i‖ =
            |a (n - 1)| * ‖∑ i ∈ Finset.range n,z i‖:= by
          rw [norm_smul,Real.norm_eq_abs]
        _ = a (n - 1) * ‖∑ i ∈ Finset.range n,z i‖:= by
          rw [abs_of_nonneg (ha_nonneg _)]
        _ ≤ a (n - 1) * B:= by
          gcongr
          · exact ha_nonneg _
          · exact hbound n
        _ = B * a (n - 1):= by ring
    calc
      ‖a (n - 1) • ∑ i ∈ Finset.range n,z i -
          ∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j‖
          ≤ ‖a (n - 1) • ∑ i ∈ Finset.range n,z i‖ +
              ‖∑ i ∈ Finset.range (n - 1),
                  (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j‖:= by
              simpa [sub_eq_add_neg] using
                (norm_sub_le (a (n - 1) • ∑ i ∈ Finset.range n,z i)
                  (∑ i ∈ Finset.range (n - 1),
                    (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1),z j))
      _ ≤ B * a (n - 1) + B * (a 0 - a (n - 1)):=add_le_add hfirst hsum_le
      _ = B * a 0:= by ring
lemma rp169
    {E: Type*} [NormedAddCommGroup E]
    {z: ℕ → E} {B: ℝ}
    (hbound: ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤ B) (m n: ℕ) :
    ‖∑ i ∈ Finset.range n,z (m + i)‖ ≤ 2 * B:= by
  have hshift :
      ∑ i ∈ Finset.range n,z (m + i) =
        ∑ i ∈ Finset.range (m + n),z i - ∑ i ∈ Finset.range m,z i:= by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm,add_left_comm,add_assoc] using (Finset.sum_range_add z m n).symm
  rw [hshift]
  calc
    ‖∑ i ∈ Finset.range (m + n),z i - ∑ i ∈ Finset.range m,z i‖
        ≤ ‖∑ i ∈ Finset.range (m + n),z i‖ + ‖∑ i ∈ Finset.range m,z i‖:= by
            simpa [sub_eq_add_neg] using
              (norm_sub_le (∑ i ∈ Finset.range (m + n),z i) (∑ i ∈ Finset.range m,z i))
    _ ≤ B + B:=add_le_add (hbound _) (hbound _)
    _ = 2 * B:= by ring
lemma rp170
    {E: Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a: ℕ → ℝ} {z: ℕ → E} {B: ℝ}
    (ha: Antitone a) (ha_nonneg: ∀ n,0 ≤ a n)
    (hbound: ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤ B) (m n: ℕ) :
    ‖∑ i ∈ Finset.range n,a (m + i) • z (m + i)‖ ≤ (2 * B) * a m:= by
  simpa [two_mul,add_comm,add_left_comm,add_assoc,mul_add,add_mul,mul_comm,mul_left_comm,
    mul_assoc] using
    (rp168
      (a:=fun k => a (m + k)) (z:=fun k => z (m + k)) (B:=2 * B)
      (ha:=fun i j hij => ha (Nat.add_le_add_left hij m))
      (ha_nonneg:=fun k => ha_nonneg (m + k))
      (hbound:=fun k => rp169 (z:=z) (B:=B) hbound m k) n)
end KummerCriterion
end

section
noncomputable section
open Filter
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p: ℕ) [hp: Fact p.Prime]
lemma rp171 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) (n: ℕ) :
    ‖∑ i ∈ Finset.range n,Real.sin (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
  let z: ℂ:=Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one: z ≠ 1:= by
    intro hz
    have hexp: Complex.exp ((2 * Real.pi * x) * Complex.I) = 1:= by simpa [z] using hz
    obtain ⟨m,hm⟩:=Complex.exp_eq_one_iff.mp hexp
    have him: 2 * Real.pi * x = (m: ℝ) * (2 * Real.pi):= by
      simpa using congrArg Complex.im hm
    have hm_pos: (0: ℝ) < m:= by nlinarith [Real.pi_pos,hx₀,him]
    have hm_lt_one: (m: ℝ) < 1:= by nlinarith [Real.pi_pos,hx₁,him]
    have hm_pos_int: 0 < m:= by exact_mod_cast hm_pos
    have hm_lt_one_int: m < 1:= by exact_mod_cast hm_lt_one
    lia
  have him :
      ((∑ i ∈ Finset.range n,z ^ i).im: ℝ) =
        ∑ i ∈ Finset.range n,Real.sin (2 * Real.pi * x * i):= by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i: ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring,Complex.exp_ofReal_mul_I_im]
  have hgeom: ‖∑ i ∈ Finset.range n,z ^ i‖ ≤ 2 / ‖z - 1‖:= by
    calc
      ‖∑ i ∈ Finset.range n,z ^ i‖ = ‖(z ^ n - 1) / (z - 1)‖:= by
        rw [geom_sum_eq hz_ne_one]
      _ = ‖z ^ n - 1‖ / ‖z - 1‖:= by rw [Complex.norm_div]
      _ ≤ 2 / ‖z - 1‖:= by
        have hden: 0 < ‖z - 1‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
        have hnum: ‖z ^ n - 1‖ ≤ 2:= by
          calc
            ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1: ℂ)‖:=norm_sub_le _ _
            _ = 1 + 1:= by
              rw [norm_pow]
              have hz_norm: ‖z‖ = 1:= by
                simpa [z] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
              rw [hz_norm]
              simp
            _ = 2:= by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n,Real.sin (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n,z ^ i).im: ℝ)‖:= by rw [him]
    _ ≤ ‖∑ i ∈ Finset.range n,z ^ i‖:= by
      simpa using (RCLike.norm_im_le_norm (∑ i ∈ Finset.range n,z ^ i))
    _ ≤ 2 / ‖z - 1‖:=hgeom
    _ = 2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
      simp [z,norm_sub_rev]
lemma rp172 (x: ℝ) (i: ℕ) :
    Continuous fun s: ℝ =>
      Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)):= by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1
lemma rp173 (x s: ℝ) (hs: 1 < s) :
    HasSum (fun n: ℕ => Real.sin (2 * Real.pi * x * (n + 1)) / ((n + 1: ℂ) ^ (s: ℂ)))
      (HurwitzZeta.sinZeta x s):= by
  let f: ℕ → ℂ:=fun n => Real.sin (2 * Real.pi * x * n) / ((n: ℂ) ^ (s: ℂ))
  have hfull: HasSum f (HurwitzZeta.sinZeta x s):= by
    simpa [f] using HurwitzZeta.hasSum_nat_sinZeta x (show 1 < ((s: ℂ)).re by simpa)
  have hshift: HasSum (fun n: ℕ => f (n + 1)) (∑' n: ℕ,f (n + 1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull' : HasSum f (f 0 + ∑' n: ℕ,f (n + 1)):=hshift.zero_add
  have hvalue: (∑' n: ℕ,f (n + 1)) = HurwitzZeta.sinZeta x s:= by
    have:=tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [f,hs.ne'] using this
  exact hvalue ▸ hshift.congr_fun (fun n => by simp [f])
lemma rp174 {x s: ℝ} (hx₀: 0 < x) (hx₁: x < 1) (hs: 1 ≤ s)
    (m n: ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1: ℕ) : ℂ) ^ (s: ℂ))‖ ≤
      (4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
        (1 / (m + 1: ℝ) ^ s):= by
  let a: ℕ → ℝ:=fun k => 1 / (k + 1: ℝ) ^ s
  let z: ℕ → ℂ:=fun k => Real.sin (2 * Real.pi * x * (k + 1))
  have ha: Antitone a:= by
    intro i j hij
    have hij' : (i + 1: ℝ) ≤ j + 1:= by exact_mod_cast Nat.succ_le_succ hij
    have hi_pos: 0 < (i + 1: ℝ):= by positivity
    have hs_nonneg: 0 ≤ s:=le_trans zero_lt_one.le hs
    have hpow: (i + 1: ℝ) ^ s ≤ (j + 1: ℝ) ^ s :=
      Real.rpow_le_rpow hi_pos.le hij' hs_nonneg
    simpa [a,one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hi_pos _) hpow
  have ha_nonneg: ∀ k,0 ≤ a k:= by
    intro k
    positivity
  have hzbound :
      ∀ k,‖∑ i ∈ Finset.range k,z i‖ ≤
        2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
    intro k
    have hsum :
        ∑ i ∈ Finset.range k,Real.sin (2 * Real.pi * x * (i + 1)) =
          ∑ i ∈ Finset.range (k + 1),Real.sin (2 * Real.pi * x * i):= by
      simpa [Nat.cast_add,add_assoc,add_comm,add_left_comm] using
        (Finset.sum_range_add (fun i => Real.sin (2 * Real.pi * x * i)) 1 k).symm
    rw [show (∑ i ∈ Finset.range k,z i) =
        ((∑ i ∈ Finset.range k,Real.sin (2 * Real.pi * x * (i + 1)) : ℝ) : ℂ) by
          simp [z,Complex.ofReal_sum]]
    rw [Complex.norm_real,hsum]
    exact rp171 hx₀ hx₁ (k + 1)
  calc
    ‖∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1: ℕ) : ℂ) ^ (s: ℂ))‖
        = ‖∑ i ∈ Finset.range n,a (m + i) • z (m + i)‖:= by
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            have hcpow :
                (((m + i + 1: ℕ) : ℂ) ^ (s: ℂ)) =
                  ((((m + i + 1: ℕ) : ℝ) ^ s: ℝ) : ℂ):= by
              simpa using
                (Complex.ofReal_cpow (x:=(m + i + 1: ℝ)) (by positivity) (y:=s)).symm
            rw [hcpow]
            simp [a,z,div_eq_mul_inv,mul_comm,mul_left_comm]
    _ ≤ (2 * (2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) * a m :=
          rp170 ha ha_nonneg hzbound m n
    _ = (4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
          (1 / (m + 1: ℝ) ^ s):= by
          have hcoef :
              (2 * (2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) =
                4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
            ring
          rw [hcoef]
lemma rp175 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    ∃ l: ℝ,
      Tendsto
        (fun n ↦
          ∑ i ∈ Finset.range n,if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
        atTop (𝓝 l):= by
  let f: ℕ → ℝ:=fun n => if n = 0 then 1 else 1 / n
  let z: ℕ → ℝ:=fun n => if n = 0 then 0 else Real.sin (2 * Real.pi * x * n)
  have hf: Antitone f:= by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f,hb.ne']
        have hb1: (1: ℝ) ≤ b:= by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb: 0 < b:=lt_of_lt_of_le ha hab
      simp [f,ha.ne',(Nat.ne_of_gt hb)]
      have ha' : (0: ℝ) < a:= by exact_mod_cast ha
      have hab' : (a: ℝ) ≤ b:= by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0: Tendsto f atTop (𝓝 0):= by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n: ℕ => 1 / (n + 1: ℝ)) atTop (𝓝 0))
  have hpartial :
      ∀ n,∑ i ∈ Finset.range n,z i =
        ∑ i ∈ Finset.range n,Real.sin (2 * Real.pi * x * i):= by
    intro n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [z]
    · simp [z,hi.ne']
  have hbound :
      ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤
        2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
    intro n
    rw [hpartial]
    exact rp171 hx₀ hx₁ n
  have hcauchy:=hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l,hl⟩:=cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l,?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n,f i • z i) =
        fun n ↦
          ∑ i ∈ Finset.range n,if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i:= by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f,z]
    · simp [f,z,hi.ne',smul_eq_mul,div_eq_mul_inv,mul_comm]
  exact hseries ▸ hl
lemma rp176 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n,if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
      atTop (𝓝 (Real.pi * (1 / 2 - x))):= by
  obtain ⟨l,hl⟩:=rp175 hx₀ hx₁
  let coeff: ℕ → ℝ:=fun n =>
    if n = 0 then 0 else Real.sin (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r: ℝ => ∑' n,coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r: ℝ => ∑' n,coeff n * r ^ n)
        (fun r: ℝ =>
          (-Complex.log ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (Set.Ioo 0 1):= by
    intro r hr
    have hr₀: 0 ≤ r:=hr.1.le
    have hr₁: r < 1:=hr.2
    calc
      ∑' n: ℕ,coeff n * r ^ n
          = ∑' n: ℕ,(r ^ n / n) * Real.sin (2 * Real.pi * x * n):= by
              refine tsum_congr fun n: ℕ => ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff,hn.ne',div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
      _ = (-Complex.log ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im :=
            (rp165 x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r: ℝ =>
          (-Complex.log ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hslit :
      ((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)) ∈ Complex.slitPlane:= by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre :
        (((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)).re: ℝ) =
          2 * Real.sin (Real.pi * x) ^ 2:= by
      have hExp :
          (Complex.exp ((2 * Real.pi * x) * Complex.I)).re = Real.cos (2 * Real.pi * x):= by
        simpa using (Complex.exp_ofReal_mul_I_re (2 * Real.pi * x))
      rw [Complex.sub_re,Complex.one_re,hExp]
      have hsq: 1 - Real.cos (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) ^ 2:= by
        rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
      exact hsq
    rw [hre]
    have hxπ: Real.pi * x ∈ Set.Ioo 0 Real.pi:= by
      constructor <;> nlinarith [hx₀,hx₁,Real.pi_pos]
    have hsin: 0 < Real.sin (Real.pi * x):=Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hcont :
      Tendsto
        (fun r: ℝ =>
          (-Complex.log ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 (Real.pi * (1 / 2 - x))):= by
    have hz :
        Tendsto
          (fun r: ℝ => (1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))
          (𝓝[<] 1)
          (𝓝 ((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I))):= by
      have hcont :
          Continuous fun r: ℝ =>
            (1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I):= by
        continuity
      have hcont1 :
          ContinuousAt
            (fun r: ℝ =>
              (1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)) 1 :=
        hcont.continuousAt
      convert tendsto_nhdsWithin_of_tendsto_nhds hcont1.tendsto using 1
      · simp
    have hlog :
        Tendsto
          (fun r: ℝ =>
            Complex.log ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)))
          (𝓝[<] 1)
          (𝓝 (Complex.log ((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))) :=
      hz.clog hslit
    have him0 :
        Tendsto
          (fun r: ℝ =>
            (Complex.log ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
          (𝓝[<] 1)
          (𝓝 ((Complex.log (((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im)) :=
      Complex.continuous_im.continuousAt.tendsto.comp hlog
    have hnegim :
        Tendsto
          (fun r: ℝ =>
            -((Complex.log
              ((1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im))
          (𝓝[<] 1)
          (𝓝 (-((Complex.log
            (((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im))) :=
      him0.neg
    have ht₀: 0 < 2 * Real.pi * x:= by nlinarith [hx₀,Real.pi_pos]
    have ht₂π: 2 * Real.pi * x < 2 * Real.pi:= by nlinarith [hx₁,Real.pi_pos]
    have hvalue:=rp164 ht₀ ht₂π
    have hvalue' :
        -((Complex.log (((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
          Real.pi * (1 / 2 - x):= by
      calc
        -((Complex.log (((1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
            Real.pi / 2 - (2 * Real.pi * x) / 2:= by
              simpa using hvalue
        _ = Real.pi * (1 / 2 - x):= by ring
    simpa [hvalue'] using hnegim
  have hl_eq: l = Real.pi * (1 / 2 - x):=tendsto_nhds_unique habel' hcont
  simpa [hl_eq] using hl
lemma rp177 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    Tendsto
      (fun n: ℕ => ∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (1: ℂ)))
      atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)):= by
  let F: ℕ → ℂ:=fun n =>
    ((∑ i ∈ Finset.range n,
        if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i: ℝ) : ℂ)
  have hbase: Tendsto F atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)):= by
    simpa [F] using (rp176 hx₀ hx₁).ofReal
  have hshifted: Tendsto (fun n: ℕ => F (n + 1)) atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n => ?_
  have hsum :=
    Finset.sum_range_add
      (fun i: ℕ => (((if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i: ℝ)) : ℂ)) 1 n
  simpa [F,add_comm,add_left_comm,add_assoc] using hsum
lemma rp178 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    UniformCauchySeqOn
      (fun n (s: ℝ) => ∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)))
      atTop (Set.Ici 1):= by
  rw [Metric.uniformCauchySeqOn_iff]
  let B: ℝ :=
    4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
  have hxπ: Real.pi * x ∈ Set.Ioo 0 Real.pi:= by
    constructor <;> nlinarith [hx₀,hx₁,Real.pi_pos]
  have hsin: 0 < Real.sin (Real.pi * x):=Real.sin_pos_of_mem_Ioo hxπ
  have hdenom: 0 < ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
    have htwo: 0 < 2 * Real.sin (Real.pi * x):= by positivity
    have hunit_ne :
        Real.cos (Real.pi * x - Real.pi / 2) +
            Real.sin (Real.pi * x - Real.pi / 2) * Complex.I ≠ 0:= by
      have hunit_pos :
          0 < ‖Real.cos (Real.pi * x - Real.pi / 2) +
              Real.sin (Real.pi * x - Real.pi / 2) * Complex.I‖:= by
        have hunit_pos' :
            0 < ‖Complex.cos ((Real.pi * x - Real.pi / 2: ℝ) : ℂ) +
                Complex.sin ((Real.pi * x - Real.pi / 2: ℝ) : ℂ) * Complex.I‖:= by
          rw [Complex.norm_cos_add_sin_mul_I]
          norm_num
        simpa [Complex.ofReal_cos,Complex.ofReal_sin] using hunit_pos'
      exact norm_pos_iff.mp hunit_pos
    have hfac_ne: ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) ≠ 0:= by
      exact_mod_cast htwo.ne'
    have hzero: (1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0:= by
      have hrewrite :
          (1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) =
            (2 * Real.sin ((2 * Real.pi * x) / 2) : ℝ) *
              (Real.cos ((2 * Real.pi * x) / 2 - Real.pi / 2) +
                Real.sin ((2 * Real.pi * x) / 2 - Real.pi / 2) * Complex.I):= by
        simpa [mul_assoc] using rp162 (2 * Real.pi * x)
      rw [hrewrite]
      simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using mul_ne_zero hfac_ne hunit_ne
    exact norm_pos_iff.mpr hzero
  have hB_pos: 0 < B:= by
    positivity
  intro ε hε
  obtain ⟨N,hN⟩:=exists_nat_one_div_lt (div_pos hε hB_pos)
  refine ⟨N,?_⟩
  have htail_bound :
      ∀ ⦃m n: ℕ⦄,N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1: ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)))
            (∑ i ∈ Finset.range n,
              Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)))
          < ε:= by
    intro m n hm hmn s hs
    let term: ℕ → ℂ:=fun k =>
      Real.sin (2 * Real.pi * x * (k + 1)) / ((k + 1: ℂ) ^ (s: ℂ))
    have hsplit :
        ∑ i ∈ Finset.range n,term i =
          ∑ i ∈ Finset.range m,term i + ∑ i ∈ Finset.range (n - m),term (m + i):= by
      simpa [term,Nat.add_sub_of_le hmn] using Finset.sum_range_add term m (n - m)
    have hs' : 1 ≤ s:=hs
    rw [dist_eq_norm,norm_sub_rev]
    calc
      ‖∑ i ∈ Finset.range n,term i - ∑ i ∈ Finset.range m,term i‖
          = ‖∑ i ∈ Finset.range (n - m),term (m + i)‖:= by
              rw [hsplit]
              ring_nf
      _ ≤ B * (1 / (m + 1: ℝ) ^ s):= by
            simpa [B,term,add_assoc,add_comm,add_left_comm] using
              rp174 (x:=x) hx₀ hx₁ hs' m (n - m)
      _ ≤ B * (1 / (m + 1: ℝ)):= by
            have hm1: 1 ≤ (m + 1: ℝ):= by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow: (m + 1: ℝ) ^ (1: ℝ) ≤ (m + 1: ℝ) ^ s:= by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv: 1 / (m + 1: ℝ) ^ s ≤ 1 / (m + 1: ℝ):= by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m + 1: ℝ) ^ (1: ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hB_pos.le
      _ ≤ B * (1 / (N + 1: ℝ)):= by
            have hm_inv: 1 / (m + 1: ℝ) ≤ 1 / (N + 1: ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N + 1: ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hB_pos.le
      _ < B * (ε / B) :=
            mul_lt_mul_of_pos_left hN hB_pos
      _ = ε:= by
            field_simp [hB_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs
theorem rp179 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    HurwitzZeta.sinZeta x 1 = (Real.pi * (1 / 2 - x) : ℂ):= by
  let boundary: ℂ:=(Real.pi * (1 / 2 - x) : ℂ)
  let S: ℕ → ℝ → ℂ:=fun n s =>
    ∑ i ∈ Finset.range n,
      Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ))
  let G: ℝ → ℂ:=fun s => if hs: s = 1 then boundary else HurwitzZeta.sinZeta x s
  have hCauchy: UniformCauchySeqOn S atTop (Set.Ici 1):= by
    simpa [S] using rp178 (x:=x) hx₀ hx₁
  have hpoint: ∀ s ∈ Set.Ici (1: ℝ),Tendsto (fun n => S n s) atTop (𝓝 (G s)):= by
    intro s hs
    by_cases hs1: s = 1
    · simpa [S,G,hs1,boundary] using rp177 (x:=x) hx₀ hx₁
    · have hslt: 1 < s:=lt_of_le_of_ne hs (by simpa [eq_comm] using hs1)
      simpa [S,G,hs1] using (rp173 (x:=x) s hslt).tendsto_sum_nat
  have hunif: TendstoUniformlyOn S G atTop (Set.Ici 1) :=
    hCauchy.tendstoUniformlyOn_of_tendsto hpoint
  have hcont: ContinuousOn G (Set.Ici (1: ℝ)):= by
    apply hunif.continuousOn
    refine Frequently.of_forall fun n => ?_
    classical
    dsimp [S]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _ => rp172 x i
  have hG_right: Tendsto G (𝓝[Set.Ioi 1] 1) (𝓝 boundary):= by
    have hG_Ici: Tendsto G (𝓝[Set.Ici 1] 1) (𝓝 boundary):= by
      simpa [G,boundary] using (hcont 1 (by simp)).tendsto
    exact hG_Ici.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hG_eq: G =ᶠ[𝓝[Set.Ioi 1] 1] fun s: ℝ => HurwitzZeta.sinZeta x s:= by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hslt: 1 < s:= by simpa using hs
    simp [G,ne_of_gt hslt]
  have hsin_right: Tendsto (fun s: ℝ => HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    Tendsto.congr' hG_eq hG_right
  have hsin_cont: Tendsto (fun s: ℝ => HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.sinZeta x 1)):= by
    have hcomplex: Tendsto (fun z: ℂ => HurwitzZeta.sinZeta x z) (𝓝 (1: ℂ))
        (𝓝 (HurwitzZeta.sinZeta x 1)) :=
      ((HurwitzZeta.differentiableAt_sinZeta x) (1: ℂ)).continuousAt.tendsto
    have hreal: Tendsto (fun s: ℝ => (s: ℂ)) (𝓝 (1: ℝ)) (𝓝 (1: ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hcomp: Tendsto (fun s: ℝ => HurwitzZeta.sinZeta x (s: ℂ)) (𝓝 (1: ℝ))
        (𝓝 (HurwitzZeta.sinZeta x 1)):= by
      simpa [Function.comp] using! hcomplex.comp hreal
    exact hcomp.mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hsin_right hsin_cont).symm
theorem rp180 {a: ZMod p} (ha: a ≠ 0) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
      (((Real.pi: ℝ) : ℂ) * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ))):= by
  rw [rp161]
  have hx: (a.val / p: ℝ) ∈ Set.Ioo 0 1:=rp160 (p:=p) ha
  calc
    HurwitzZeta.sinZeta (a.val / p: ℝ) 1 =
        (Real.pi * (1 / 2 - (a.val / p: ℝ)) : ℂ) :=
          rp179 (x:=(a.val / p: ℝ)) hx.1 hx.2
    _ = (((Real.pi: ℝ) : ℂ) * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ))):= by
          have hcast: (((a.val / p: ℝ) : ℂ)) = (a.val: ℂ) / (p: ℂ):= by
            push_cast
            rfl
          simpa using congrArg
            (fun z: ℂ => (((Real.pi: ℝ) : ℂ) * ((1 / 2: ℂ) - z))) hcast
end LValueAtOne
end KummerCriterion
end

section
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p: ℕ) [hp: Fact p.Prime]
noncomputable def rp181 (χ: DirichletCharacter ℂ p) : ℂ :=
  ((((Real.pi: ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N:=p)) / (p: ℂ)) *
    rp18 χ⁻¹ 1
noncomputable def rp182 (χ: DirichletCharacter ℂ p) : ℂ :=
  ∑ a: ZMod p,χ⁻¹ a * ((Real.log ‖(1: ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ)
noncomputable def rp183 (χ: DirichletCharacter ℂ p) : ℂ :=
  -(gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)))⁻¹ * rp182 p χ
theorem rp184
    {χ: DirichletCharacter ℂ p} (hχ_prim: χ.IsPrimitive) (hχ_odd: χ.Odd)
    (hχ0: DirichletCharacter.LFunction χ⁻¹ 0 = -rp18 χ⁻¹ 1) :
    DirichletCharacter.LFunction χ 1 = rp181 p χ:= by
  have hp_ne_one: p ≠ 1:=hp.out.ne_one
  have hp_ne_zero: (p: ℂ) ≠ 0:= by
    exact_mod_cast hp.out.ne_zero
  have hχinv_odd: (χ⁻¹).Odd:= by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv',hχ_odd]
    norm_num
  have hL1: DirichletCharacter.LFunction χ 1 =
      ((Real.pi: ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1:= by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ:=χ) (s:=1)
        (Or.inl one_ne_zero),hχ_odd.gammaFactor_def]
    simp [Complex.Gammaℝ_def,Complex.Gamma_one,Complex.cpow_neg_one,mul_comm]
  have hL0: DirichletCharacter.completedLFunction χ⁻¹ 0 =
      DirichletCharacter.LFunction χ⁻¹ 0:= by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ:=χ⁻¹) (s:=0)
        (Or.inr hp_ne_one),hχinv_odd.gammaFactor_def]
    simp
  have hfe :=
    DirichletCharacter.IsPrimitive.completedLFunction_one_sub (χ:=χ) hχ_prim (0: ℂ)
  rw [DirichletCharacter.rootNumber,if_neg hχ_odd.not_even,pow_one,
    ← mul_comm_div,← mul_comm_div,← Complex.cpow_sub _ _ hp_ne_zero,sub_sub,add_halves,
    hL0,hχ0] at hfe
  have hfe' : DirichletCharacter.completedLFunction χ 1 =
      (p: ℂ) ^ (-1: ℂ) * Complex.I * gaussSum χ (ZMod.stdAddChar (N:=p)) *
        rp18 χ⁻¹ 1:= by
    simpa using hfe
  calc
    DirichletCharacter.LFunction χ 1
        = ((Real.pi: ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1:=hL1
    _ = ((Real.pi: ℝ) : ℂ) *
          (((p: ℂ) ^ (-1: ℂ)) * Complex.I * gaussSum χ (ZMod.stdAddChar (N:=p)) *
            rp18 χ⁻¹ 1):= by rw [hfe']
    _ = ((((Real.pi: ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N:=p)) /
            (p: ℂ)) * rp18 χ⁻¹ 1:= by
      simp [Complex.cpow_neg_one,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
    _ = rp181 p χ:=rfl
end LValueAtOne
end KummerCriterion
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p: ℕ) [hp: Fact p.Prime]
theorem rp185
    {χ: DirichletCharacter ℂ p} (hχ_odd: χ.Odd) :
    DirichletCharacter.LFunction χ 0 =
      (((Real.pi: ℝ) : ℂ)⁻¹) *
        ∑ a: ZMod p,χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1:= by
  have hs: ∀ n: ℕ,(1: ℂ) ≠ -n:= by
    intro n h
    have hre: (1: ℝ) = -(n: ℝ):= by
      simpa using congrArg Complex.re h
    nlinarith
  have hχ_odd_fun: Function.Odd (fun a: ZMod p => χ a) :=
    fun a => DirichletCharacter.Odd.eval_neg (ψ:=χ) a hχ_odd
  rw [DirichletCharacter.LFunction,ZMod.LFunction_def_odd hχ_odd_fun]
  simp only [neg_zero,Complex.cpow_zero,one_mul]
  calc
    ∑ a: ZMod p,χ a * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle a) 0
        = ∑ a: ZMod p,
            χ a *
              ((((Real.pi: ℝ) : ℂ)⁻¹) * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1):= by
              refine Finset.sum_congr rfl fun a _ => ?_
              have hvalue:=HurwitzZeta.hurwitzZetaOdd_one_sub
                (s:=(1: ℂ)) (a:=ZMod.toAddCircle a) hs
              have hsin: Complex.sin (((Real.pi: ℝ) : ℂ) * (2⁻¹: ℂ)) = 1:= by
                simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
                  using Complex.sin_pi_div_two
              simpa [Complex.Gamma_one,Complex.cpow_neg_one,hsin,mul_assoc,mul_left_comm,
                mul_comm,div_eq_mul_inv] using congrArg (fun z: ℂ => χ a * z) hvalue
    _ = ∑ a: ZMod p,
          (((Real.pi: ℝ) : ℂ)⁻¹) * (χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1):= by
            refine Finset.sum_congr rfl fun a _ => by ring
    _ = (((Real.pi: ℝ) : ℂ)⁻¹) *
          ∑ a: ZMod p,χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1:= by
            rw [Finset.mul_sum]
theorem rp186
    {χ: DirichletCharacter ℂ p} (hχ_odd: χ.Odd) (hχ_ne_one: χ ≠ 1)
    (hsin: ∀ a: ZMod p,a ≠ 0 →
      HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
        (((Real.pi: ℝ) : ℂ) * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ)))) :
    DirichletCharacter.LFunction χ 0 = -rp18 χ 1:= by
  have hp_ne_one: p ≠ 1:=hp.out.ne_one
  have hp_ne_zero: (p: ℂ) ≠ 0:= by
    exact_mod_cast hp.out.ne_zero
  have hχ_zero: χ 0 = 0:=χ.map_zero' hp_ne_one
  have hsum_zero: ∑ a: ZMod p,χ a = 0:=MulChar.sum_eq_zero_of_ne_one hχ_ne_one
  have hpi: (((Real.pi: ℝ) : ℂ)⁻¹) * (((Real.pi: ℝ) : ℂ)) = 1:= by
    field_simp [Real.pi_ne_zero]
  calc
    DirichletCharacter.LFunction χ 0
        = (((Real.pi: ℝ) : ℂ)⁻¹) *
            ∑ a: ZMod p,χ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 :=
          rp185 (p:=p) hχ_odd
    _ = (((Real.pi: ℝ) : ℂ)⁻¹) *
          ∑ a: ZMod p,
            χ a *
              ((((Real.pi: ℝ) : ℂ) * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ)))):= by
            refine congrArg (fun z: ℂ => (((Real.pi: ℝ) : ℂ)⁻¹) * z) ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rcases eq_or_ne a 0 with rfl | ha
            · simp [hχ_zero]
            · rw [hsin a ha]
    _ = ∑ a: ZMod p,χ a * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ)):= by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          calc
            (((Real.pi: ℝ) : ℂ)⁻¹) *
                (χ a * (((Real.pi: ℝ) : ℂ) * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ))))
                = ((((Real.pi: ℝ) : ℂ)⁻¹) * (((Real.pi: ℝ) : ℂ))) *
                    (χ a * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ))):= by
                      ring
            _ = χ a * ((1 / 2: ℂ) - (a.val: ℂ) / (p: ℂ)):= by
                  rw [hpi,one_mul]
    _ = -∑ a: ZMod p,χ a * ((a.val: ℂ) / (p: ℂ)):= by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          have hconst: ∑ a: ZMod p,χ a * (1 / 2: ℂ) = 0:= by
            calc
              ∑ a: ZMod p,χ a * (1 / 2: ℂ) = (1 / 2: ℂ) * ∑ a: ZMod p,χ a:= by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by rw [mul_comm]
              _ = 0:= by rw [hsum_zero,mul_zero]
          rw [hconst,zero_sub]
    _ = -rp18 χ 1:= by
          congr 1
          rw [rp19 (R:=ℂ) (N:=p) (χ:=χ) hχ_ne_one]
          refine Finset.sum_congr rfl fun a _ => ?_
          congr 1
          change (a.val: ℂ) / (p: ℂ) = ((((a.val: ℚ) / p: ℚ)) : ℂ)
          rw [Rat.cast_div]
          push_cast
          rfl
theorem rp187
    {χ: DirichletCharacter ℂ p} (hχ_odd: χ.Odd) (hχ_ne_one: χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 = -rp18 χ 1 :=
  rp186 (p:=p)
    hχ_odd hχ_ne_one
    (fun _ ha => rp180 (p:=p) ha)
theorem rp188
    {χ: DirichletCharacter ℂ p} (hχ_prim: χ.IsPrimitive) (hχ_odd: χ.Odd)
    (hχ_ne_one: χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 = rp181 p χ:= by
  have hχinv_odd: (χ⁻¹).Odd:= by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv',hχ_odd]
    norm_num
  have hχinv_ne_one: χ⁻¹ ≠ 1:= by
    intro h
    apply hχ_ne_one
    calc χ = χ⁻¹⁻¹:=(inv_inv χ).symm
      _ = (1: DirichletCharacter ℂ p)⁻¹:= by rw [h]
      _ = 1:=inv_one
  exact rp184 (p:=p) hχ_prim hχ_odd
    (rp187 (p:=p) hχinv_odd hχinv_ne_one)
end LValueAtOne
end KummerCriterion
end

section
noncomputable section
namespace KummerCriterion
section SignInvariant
open scoped BigOperators ComplexConjugate
variable (p: ℕ) [hp: Fact p.Prime]
local instance {α: Type*} : DecidableEq α:=Classical.decEq α
local instance (a: Prop) : Decidable a:=Classical.propDecidable a
theorem rp189 (hp₂: p ≠ 2) :
    (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2:= by
  classical
  let E: Finset (DirichletCharacter ℂ p):=Finset.univ.filter fun χ => χ.Even
  let O: Finset (DirichletCharacter ℂ p):=Finset.univ.filter fun χ => χ.Odd
  have hdisj: Disjoint E O:= by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even: χ.Even:= by simpa [E] using hχE
    have hχ_odd: χ.Odd:= by simpa [O] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion: E ∪ O = (Finset.univ: Finset (DirichletCharacter ℂ p)):= by
    ext χ
    simp only [E,O,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hneg_ne_one: (-1: ZMod p) ≠ 1:= by
    have: Fact (2 < p):=⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp₂)⟩
    exact ZMod.neg_one_ne_one
  have hsum_zero :
      ∑ χ: DirichletCharacter ℂ p,χ (-1: ZMod p) = 0 :=
    DirichletCharacter.sum_characters_eq_zero (R:=ℂ) (n:=p) hneg_ne_one
  have hsum_split :
      (∑ χ: DirichletCharacter ℂ p,χ (-1: ZMod p)) = (E.card: ℂ) - O.card:= by
    have hsum_union :
        (∑ χ: DirichletCharacter ℂ p,χ (-1: ZMod p)) =
          (E ∪ O).sum (fun χ => χ (-1: ZMod p)):= by
      rw [hunion]
    have hsum_E: E.sum (fun χ => χ (-1: ZMod p)) = E.card:= by
      calc
        E.sum (fun χ => χ (-1: ZMod p)) = E.sum (fun _ => (1: ℂ)):= by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_even: χ.Even:= by simpa [E] using hχ
          simpa [DirichletCharacter.Even] using hχ_even
        _ = E.card:= by simp
    have hsum_O: O.sum (fun χ => χ (-1: ZMod p)) = -(O.card: ℂ):= by
      calc
        O.sum (fun χ => χ (-1: ZMod p)) = O.sum (fun _ => (-1: ℂ)):= by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_odd: χ.Odd:= by simpa [O] using hχ
          simpa [DirichletCharacter.Odd] using hχ_odd
        _ = -(O.card: ℂ):= by simp
    calc
      (∑ χ: DirichletCharacter ℂ p,χ (-1: ZMod p)) =
          E.sum (fun χ => χ (-1: ZMod p)) + O.sum (fun χ => χ (-1: ZMod p)):= by
            rw [hsum_union,Finset.sum_union hdisj]
      _ = (E.card: ℂ) - O.card:= by
            rw [hsum_E,hsum_O]
            simp [sub_eq_add_neg]
  have hbalance: (E.card: ℂ) - O.card = 0:= by
    rw [← hsum_split]
    exact hsum_zero
  have hsame: E.card = O.card:= by
    have hsame_real: (E.card: ℝ) = O.card:= by
      have hdiff_real: (E.card: ℝ) - O.card = 0:= by
        simpa using congrArg Complex.re hbalance
      nlinarith
    exact_mod_cast hsame_real
  have hcard_total: E.card + O.card = p - 1:= by
    calc
      E.card + O.card = (E ∪ O).card:= by
        rw [← Finset.card_union_of_disjoint hdisj]
      _ = Fintype.card (DirichletCharacter ℂ p):= by
        rw [hunion,Finset.card_univ]
      _ = p - 1:= by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R:=ℂ) (n:=p),
          Nat.totient_prime hp.out]
  have hcardE: E.card = (p - 1) / 2:= by
    omega
  simpa [E] using hcardE
end SignInvariant
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped BigOperators Pointwise
namespace KummerCriterion
variable (p: ℕ) [hp: Fact p.Prime]
noncomputable def rp190 (ℓ: ℕ) [Fact ℓ.Prime] (hℓp: ℓ ≠ p) : ℕ :=
  let d:=rp94 (p:=p) ℓ hℓp
  if Even d then d / 2 else d
noncomputable def rp191 (ℓ: ℕ) [Fact ℓ.Prime] (hℓp: ℓ ≠ p) : ℕ :=
  let d:=rp94 (p:=p) ℓ hℓp
  let c:=rp95 (p:=p) ℓ hℓp
  if Even d then c else c / 2
lemma rp192 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    (hd_even: Even (rp94 (p:=p) ℓ hℓp)) :
    rp190 (p:=p) ℓ hℓp = rp94 (p:=p) ℓ hℓp / 2:= by
  simp [rp190,hd_even]
lemma rp193 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    (hd_odd: ¬ Even (rp94 (p:=p) ℓ hℓp)) :
    rp190 (p:=p) ℓ hℓp = rp94 (p:=p) ℓ hℓp:= by
  simp [rp190,hd_odd]
lemma rp194
    {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    (((rp93 (p:=p) ℓ hℓp: (ZMod p)ˣ) : ZMod p) ^
        rp190 (p:=p) ℓ hℓp = 1) ∨
      (((rp93 (p:=p) ℓ hℓp: (ZMod p)ˣ) : ZMod p) ^
        rp190 (p:=p) ℓ hℓp = -1):= by
  let u: (ZMod p)ˣ:=rp93 (p:=p) ℓ hℓp
  let d: ℕ:=rp94 (p:=p) ℓ hℓp
  by_cases hd_even: Even d
  · rcases hd_even with ⟨k,hk⟩
    have hsq: (((u: ZMod p) ^ (d / 2)) ^ 2) = 1:= by
      rw [← pow_mul]
      have: (d / 2) * 2 = d:= by omega
      rw [this]
      dsimp [d,rp94]
      change (((u ^ orderOf u: (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x: (ZMod p)ˣ => ((x: ZMod p))) (pow_orderOf_eq_one u)
    have hcases: ((u: ZMod p) ^ (d / 2)) = 1 ∨ ((u: ZMod p) ^ (d / 2)) = -1 :=
      sq_eq_one_iff.mp hsq
    have hnot_one: ((u: ZMod p) ^ (d / 2)) ≠ 1:= by
      intro hpow
      have hpow_units: u ^ (d / 2) = 1:= by
        apply Units.ext
        simpa using hpow
      have hdvd: d ∣ d / 2:= by
        simpa [d,rp94,u] using
          (orderOf_dvd_iff_pow_eq_one (x:=u)).2 hpow_units
      have hk_pos: 0 < k:= by
        have hd_pos: 0 < d:= by
          dsimp [d,rp94]
          exact orderOf_pos u
        omega
      have hle: 2 * k ≤ k:= by
        have hdvd' : 2 * k ∣ k:= by
          rw [hk] at hdvd
          rw [show k + k = 2 * k by omega] at hdvd
          simpa using hdvd
        exact Nat.le_of_dvd hk_pos hdvd'
      omega
    rcases hcases with hpow | hpow
    · exact False.elim (hnot_one hpow)
    · right
      simpa [rp190,d,hk] using hpow
  · left
    have hpow: (u: ZMod p) ^ d = 1:= by
      dsimp [d,rp94]
      change (((u ^ orderOf u: (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x: (ZMod p)ˣ => ((x: ZMod p))) (pow_orderOf_eq_one u)
    simpa [rp190,d,hd_even] using hpow
lemma rp195
    {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    orderOf ((rp93 (p:=p) ℓ hℓp) ^ 2) =
      rp190 (p:=p) ℓ hℓp:= by
  let u: (ZMod p)ˣ:=rp93 (p:=p) ℓ hℓp
  let d: ℕ:=rp94 (p:=p) ℓ hℓp
  have hfin: IsOfFinOrder u:=isOfFinOrder_iff_pow_eq_one.mpr
    ⟨d,by
      dsimp [d,rp94]
      exact orderOf_pos u,
      by
        dsimp [d,rp94]
        exact pow_orderOf_eq_one u⟩
  by_cases hd_even: Even d
  · rcases hd_even with ⟨k,hk⟩
    have hd_even' : Even (rp94 (p:=p) ℓ hℓp) :=
      ⟨k,by simpa [d] using hk⟩
    have hgcd: d.gcd 2 = 2:= by
      apply Nat.dvd_antisymm
      · exact Nat.gcd_dvd_right d 2
      · exact Nat.dvd_gcd ⟨k,by omega⟩ dvd_rfl
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d,rp94]
        rw [hfin.orderOf_pow],hgcd,
      rp192 (p:=p) hℓp hd_even']
  · have hd_odd: Odd d:=Nat.not_even_iff_odd.mp hd_even
    have hgcd: d.gcd 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hd_odd.coprime_two_right
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d,rp94]
        rw [hfin.orderOf_pow],hgcd,
      rp193 (p:=p) hℓp (by simpa [d] using hd_even)]
    simp [d]
local instance {α: Type*} : DecidableEq α:=Classical.decEq α
local instance (a: Prop) : Decidable a:=Classical.propDecidable a
lemma rp196 (hp_odd' : p ≠ 2) :
    (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 :=
  rp189 p hp_odd'
lemma rp197
    (hp_odd' : p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    rp191 (p:=p) ℓ hℓp * rp190 (p:=p) ℓ hℓp =
      (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even).card:= by
  classical
  set d:=rp94 (p:=p) ℓ hℓp with hd
  set c:=rp95 (p:=p) ℓ hℓp with hc
  have hprod_card: c * d = Nat.card (DirichletCharacter ℂ p):= by
    simpa [c,d] using (rp97 (p:=p) hℓp)
  have hprod: c * d = p - 1:= by
    rw [hprod_card,rp77 (p:=p)]
  have hp_odd_nat: Odd p:=hp.out.odd_of_ne_two hp_odd'
  rw [rp196 (p:=p) hp_odd']
  rcases hp_odd_nat with ⟨m,hm⟩
  have hhalf: (p - 1) / 2 = m:= by
    omega
  by_cases hd_even: Even d
  · rcases hd_even with ⟨k,hk⟩
    have hkdiv: (k + k) / 2 = k:= by
      omega
    have hlhs :
        rp191 (p:=p) ℓ hℓp *
            rp190 (p:=p) ℓ hℓp =
          c * k:= by
      simp [rp191,rp190,d,hk,hkdiv,← hc]
    have hck: c * k = m:= by
      have hdouble: c * k + c * k = m + m:= by
        calc
          c * k + c * k = c * (k + k):= by rw [Nat.mul_add]
          _ = p - 1:= by simpa [hk] using hprod
          _ = m + m:= by rw [hm]; omega
      have hdouble' : 2 * (c * k) = 2 * m:= by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide: 0 < 2) hdouble'
    rw [hlhs,hhalf,hck]
  · have hd_odd: Odd d:=Nat.not_even_iff_odd.mp hd_even
    rcases hd_odd with ⟨k,hk⟩
    have hc_even: Even c:= by
      have hprod' : c * (2 * k + 1) = p - 1:= by
        simpa [hk] using hprod
      have h_rhs_even: Even (p - 1):= by
        refine ⟨m,?_⟩
        rw [hm]
        omega
      by_contra hc_not_even
      have hc_odd: Odd c:=Nat.not_even_iff_odd.mp hc_not_even
      have hlhs_odd: Odd (c * (2 * k + 1)) :=
        hc_odd.mul ⟨k,rfl⟩
      have h_lhs_even: Even (c * (2 * k + 1)):= by
        simpa [hprod'] using h_rhs_even
      exact (Nat.not_even_iff_odd.mpr hlhs_odd) h_lhs_even
    rcases hc_even with ⟨j,hj⟩
    have hc_half: rp95 (p:=p) ℓ hℓp / 2 = j:= by
      rw [← hc,hj]
      simpa [two_mul,Nat.mul_comm] using (Nat.mul_div_right j (by decide: 0 < 2))
    have hlhs :
        rp191 (p:=p) ℓ hℓp * rp190 (p:=p) ℓ hℓp =
          j * (2 * k + 1):= by
      simp [rp191,rp190,d,hk,hc_half]
    have hjk: j * (2 * k + 1) = m:= by
      have hdouble: j * (2 * k + 1) + j * (2 * k + 1) = m + m:= by
        calc
          j * (2 * k + 1) + j * (2 * k + 1) = (j + j) * (2 * k + 1):= by
            rw [Nat.add_mul]
          _ = p - 1:= by simpa [hj,hk] using hprod
          _ = m + m:= by rw [hm]; omega
      have hdouble' : 2 * (j * (2 * k + 1)) = 2 * m:= by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide: 0 < 2) hdouble'
    rw [hlhs,hhalf,hjk]
lemma rp198
    (hp_odd' : p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) (T: ℂ) :
    Finset.prod (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even)
      (fun χ => (1 - χ (ℓ: ZMod p) * T)) =
      (1 - T ^ rp190 (p:=p) ℓ hℓp) ^
        rp191 (p:=p) ℓ hℓp:= by
  classical
  let E: Finset (DirichletCharacter ℂ p) :=
    Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even
  set n:=Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units: Fintype.card (ZMod p)ˣ = n:= by
    rw [hn_def,rp77 (p:=p),ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n:= by
    rw [Nat.card_eq_fintype_card,hn_units]
  have hn_pos: 0 < n:= by
    rw [← hn_units]
    exact Fintype.card_pos
  have hp_odd_nat: Odd p:=hp.out.odd_of_ne_two hp_odd'
  have hn_even: Even n:= by
    rcases hp_odd_nat with ⟨m,hm⟩
    refine ⟨m,?_⟩
    rw [hn_def,rp77 (p:=p),hm]
    omega
  rcases hn_even with ⟨n2,hn2⟩
  have hn2' : n = 2 * n2:= by
    omega
  have hn2_pos: 0 < n2:= by
    omega
  have hnp1: n = p - 1:= by
    rw [hn_def,rp77 (p:=p)]
  obtain ⟨g,hg_mon⟩ : ∃ g: (ZMod p)ˣ,∀ x: (ZMod p)ˣ,x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x: (ZMod p)ˣ,∃ m: ℕ,g ^ m = x:=fun x => hg_mon x
  obtain ⟨a,ha⟩:=hg_mon' (rp93 (p:=p) ℓ hℓp)
  have hg_zpow: ∀ x: (ZMod p)ˣ,x ∈ Subgroup.zpowers g:=fun x => by
    obtain ⟨m,hm⟩:=hg_mon' x
    refine ⟨(m: ℤ),?_⟩
    change g ^ (m: ℤ) = x
    rw [zpow_natCast]
    exact hm
  have hg_order: orderOf g = n:= by
    rw [← hn_units']
    exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hfin_g: IsOfFinOrder g:=isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n,hn_pos,by rw [← hg_order]; exact pow_orderOf_eq_one g⟩
  have hgcd2: n.gcd 2 = 2 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right n 2) (Nat.dvd_gcd ⟨n2,hn2'⟩ dvd_rfl)
  have hω: IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω: ℂ:=Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit: IsUnit ω:=hω.isUnit hn_pos.ne'
  set ωu: ℂˣ:=hω_unit.unit with hωu_def
  have hωu_val: (ωu: ℂ) = ω:= by simp [hωu_def]
  have hωu_roots: ∀ k: ℕ,(ωu ^ k: ℂˣ) ∈ rootsOfUnity n ℂ:= by
    intro k
    rw [mem_rootsOfUnity,← pow_mul,mul_comm]
    have h1: (ωu ^ n: ℂˣ) = 1:= by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val,Units.val_one,hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul,h1,one_pow]
  let χAt: ℕ → DirichletCharacter ℂ p:=fun k =>
    MulChar.ofRootOfUnity (M:=ZMod p) (R:=ℂ) (ζ:=ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g: ∀ k: ℕ,χAt k ((g: (ZMod p)ˣ) : ZMod p) = ω ^ k:=fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val,hωu_val]
  have hℓ_eq: (ℓ: ZMod p) = (((g: (ZMod p)ˣ) : ZMod p)) ^ a:= by
    have h1: (((rp93 (p:=p) ℓ hℓp: (ZMod p)ˣ) : ZMod p)) = (ℓ: ZMod p):= by
      simp [rp93]
    rw [← h1,← ha,Units.val_pow_eq_pow_val]
  have hχAt_ℓ: ∀ k: ℕ,χAt k (ℓ: ZMod p) = ω ^ (k * a):=fun k => by
    rw [hℓ_eq,map_pow,hχAt_g,← pow_mul]
  have hg_half_sq: ((((g: (ZMod p)ˣ) : ZMod p) ^ n2) ^ 2) = 1:= by
    rw [← pow_mul]
    have: n2 * 2 = n:= by
      omega
    rw [this]
    simpa [Units.val_pow_eq_pow_val,hg_order] using
      congrArg (fun x: (ZMod p)ˣ => ((x: ZMod p))) (pow_orderOf_eq_one g)
  have hg_half_ne_one: (((g: (ZMod p)ˣ) : ZMod p) ^ n2) ≠ 1:= by
    intro hpow
    have hpow_units: g ^ n2 = 1:= by
      apply Units.ext
      simpa using hpow
    have hdvd: n ∣ n2:= by
      rw [← hg_order]
      exact (orderOf_dvd_iff_pow_eq_one (x:=g)).2 hpow_units
    have hle: n ≤ n2:=Nat.le_of_dvd hn2_pos hdvd
    rw [hn2] at hle
    omega
  have hg_half_eq_neg_one: (((g: (ZMod p)ˣ) : ZMod p) ^ n2) = -1:= by
    rcases sq_eq_one_iff.mp hg_half_sq with h1 | h1
    · exact False.elim (hg_half_ne_one h1)
    · exact h1
  let χEvenAt: ℕ → DirichletCharacter ℂ p:=fun k => χAt (2 * k)
  have hχEven_mem: ∀ k ∈ Finset.range n2,χEvenAt k ∈ E:= by
    intro k hk
    have h_even: χAt (2 * k) (-1: ZMod p) = 1:= by
      rw [← hg_half_eq_neg_one,map_pow,hχAt_g,← pow_mul]
      have: (2 * k) * n2 = k * n:= by
        rw [hn2']
        simp [Nat.mul_left_comm,Nat.mul_comm]
      rw [this,mul_comm,pow_mul,hω.pow_eq_one,one_pow]
    change χAt (2 * k) ∈ E
    rw [show E = Finset.univ.filter (fun χ: DirichletCharacter ℂ p => χ.Even) from rfl,
      Finset.mem_filter]
    simp [DirichletCharacter.Even,h_even]
  have hχEven_inj: Set.InjOn χEvenAt ↑(Finset.range n2):= by
    intro j hj k hk hjk
    simp only [Finset.coe_range,Set.mem_Iio] at hj hk
    have hval: χEvenAt j ((g: (ZMod p)ˣ) : ZMod p) = χEvenAt k ((g: (ZMod p)ˣ) : ZMod p) :=
      congrArg (fun χ: DirichletCharacter ℂ p => χ ((g: (ZMod p)ˣ) : ZMod p)) hjk
    rw [hχAt_g,hχAt_g] at hval
    have hj2: 2 * j < n:= by
      omega
    have hk2: 2 * k < n:= by
      omega
    have h_eq: 2 * j = 2 * k:= by
      simpa [χEvenAt] using hω.pow_inj hj2 hk2 hval
    omega
  have hE_card: E.card = n2:= by
    rw [rp196 (p:=p) hp_odd']
    omega
  have himage_eq: Finset.image χEvenAt (Finset.range n2) = E:= by
    apply Finset.eq_of_subset_of_card_le
    · intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨k,hk,rfl⟩
      exact hχEven_mem k hk
    · rw [hE_card,Finset.card_image_of_injOn hχEven_inj,Finset.card_range]
  have hprod_transfer :
      ∏ χ ∈ E,(1 - χ (ℓ: ZMod p) * T) =
        ∏ k ∈ Finset.range n2,(1 - ω ^ ((2 * k) * a) * T):= by
    calc
      ∏ χ ∈ E,(1 - χ (ℓ: ZMod p) * T)
          = ∏ χ ∈ Finset.image χEvenAt (Finset.range n2),(1 - χ (ℓ: ZMod p) * T):= by
              rw [← himage_eq]
      _ = ∏ k ∈ Finset.range n2,(1 - χEvenAt k (ℓ: ZMod p) * T):= by
            rw [Finset.prod_image hχEven_inj]
      _ = ∏ k ∈ Finset.range n2,(1 - ω ^ ((2 * k) * a) * T):= by
            refine Finset.prod_congr rfl (fun k _ => ?_)
            simpa [χEvenAt] using congrArg (fun z: ℂ => 1 - z * T) (hχAt_ℓ (2 * k))
  have hω_sq_prim' : IsPrimitiveRoot (ω ^ 2) (n / n.gcd 2) :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn_pos 2 hω
  have hω_sq_prim: IsPrimitiveRoot (ω ^ 2) n2:= by
    simpa [hgcd2,hn2'] using hω_sq_prim'
  have hcollapse :
      ∏ k ∈ Finset.range n2,(1 - ω ^ ((2 * k) * a) * T) =
        (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a:= by
    calc
      ∏ k ∈ Finset.range n2,(1 - ω ^ ((2 * k) * a) * T)
          = ∏ k ∈ Finset.range n2,(1 - (ω ^ 2) ^ (k * a) * T):= by
              refine Finset.prod_congr rfl (fun k _ => ?_)
              congr 1
              have hexp: (2 * k) * a = 2 * (k * a):= by
                simp [Nat.mul_assoc,Nat.mul_comm]
              rw [hexp,pow_mul]
      _ = (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a :=
            rp99 hn2_pos a hω_sq_prim T
  have hfin_g2: IsOfFinOrder (g ^ 2):=isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n2,hn2_pos,by
      rw [← pow_mul]
      have: 2 * n2 = n:= by
        omega
      rw [this,← hg_order]
      exact pow_orderOf_eq_one g⟩
  have hg_sq_order: orderOf (g ^ 2) = n2:= by
    rw [hfin_g.orderOf_pow,hg_order,hgcd2,hn2']
    simp
  have hu_sq: (rp93 (p:=p) ℓ hℓp) ^ 2 = (g ^ 2) ^ a:= by
    rw [← ha,← pow_mul]
    have: a * 2 = 2 * a:= by
      omega
    rw [this,pow_mul]
  have horder_u_sq: orderOf ((rp93 (p:=p) ℓ hℓp) ^ 2) = n2 / n2.gcd a:= by
    rw [hu_sq,hfin_g2.orderOf_pow,hg_sq_order]
  have hlocalResidue :
      rp190 (p:=p) ℓ hℓp = n2 / n2.gcd a:= by
    rw [← rp195 (p:=p) hℓp,horder_u_sq]
  have hlocalResiduePlus_pos: 0 < rp190 (p:=p) ℓ hℓp:= by
    rw [← rp195 (p:=p) hℓp]
    exact orderOf_pos _
  have hlocalResidue_pos: 0 < n2 / n2.gcd a:= by
    simpa [hlocalResidue] using hlocalResiduePlus_pos
  have hcount_mul: rp191 (p:=p) ℓ hℓp * (n2 / n2.gcd a) = n2:= by
    have hbase:=rp197 (p:=p) hp_odd' hℓp
    rw [hlocalResidue] at hbase
    simpa [E,hE_card] using hbase
  have hgcd_mul: n2.gcd a * (n2 / n2.gcd a) = n2 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n2 a)
  have hlocalPrimeCount :
      rp191 (p:=p) ℓ hℓp = n2.gcd a:= by
    have hmul :
        (n2 / n2.gcd a) * rp191 (p:=p) ℓ hℓp =
          (n2 / n2.gcd a) * (n2.gcd a):= by
      rw [Nat.mul_comm (n2 / n2.gcd a) (rp191 (p:=p) ℓ hℓp),
        Nat.mul_comm (n2 / n2.gcd a) (n2.gcd a),hcount_mul,hgcd_mul]
    exact Nat.eq_of_mul_eq_mul_left hlocalResidue_pos hmul
  simpa [E] using
    (Eq.trans hprod_transfer (Eq.trans hcollapse (by rw [← hlocalResidue,← hlocalPrimeCount])))
lemma rp199
    (hp_odd' : p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) {s: ℂ} :
    (1 - (ℓ: ℂ) ^ (-s)) * rp86 p ℓ s =
      (1 - (ℓ: ℂ) ^ (-((rp190 (p:=p) ℓ hℓp: ℂ) * s))) ^
        rp191 (p:=p) ℓ hℓp:= by
  classical
  have htriv_even: (1: DirichletCharacter ℂ p).Even:= by
    change (1: DirichletCharacter ℂ p) (-1: ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1: ZMod p) from isUnit_one.neg)]
  have hrewrite :
      rp82 (p:=p) =
        (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even).erase 1:= by
    ext χ
    simp [rp82,and_comm]
  have htrivial_mul :
      (1 - (ℓ: ℂ) ^ (-s)) * rp86 p ℓ s =
        Finset.prod (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even)
          (fun χ => (1 - χ (ℓ: ZMod p) * (ℓ: ℂ) ^ (-s))):= by
    unfold rp86
    rw [hrewrite,← Finset.mul_prod_erase
      (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even)
      (fun χ: DirichletCharacter ℂ p => (1 - χ (ℓ: ZMod p) * (ℓ: ℂ) ^ (-s)))]
    · have hℓ_unit: IsUnit ((ℓ: ZMod p)):= by
        rw [ZMod.isUnit_iff_coprime]
        exact (rp92 (p:=p) hℓp).symm
      rw [MulChar.one_apply hℓ_unit,one_mul]
    · simp [htriv_even]
  calc
    (1 - (ℓ: ℂ) ^ (-s)) * rp86 p ℓ s
        = Finset.prod (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even)
            (fun χ => (1 - χ (ℓ: ZMod p) * (ℓ: ℂ) ^ (-s))):=htrivial_mul
    _ =
        (1 - (((ℓ: ℂ) ^ (-s)) ^ rp190 (p:=p) ℓ hℓp)) ^
          rp191 (p:=p) ℓ hℓp:= by
            simpa using
              rp198 (p:=p) hp_odd' hℓp
                ((ℓ: ℂ) ^ (-s))
    _ =
        (1 - (ℓ: ℂ) ^ (-((rp190 (p:=p) ℓ hℓp: ℂ) * s))) ^
          rp191 (p:=p) ℓ hℓp:= by
            congr 1
            congr 1
            rw [show ((ℓ: ℂ) ^ (-s)) ^ rp190 (p:=p) ℓ hℓp =
                (ℓ: ℂ) ^ ((-s) * ((rp190 (p:=p) ℓ hℓp: ℕ) : ℂ)) by
                  rw [Complex.cpow_mul_nat]]
            congr 1
            ring
end KummerCriterion
end

section
noncomputable section
open NumberField
open NumberField.IsCMField
open scoped BigOperators Pointwise
namespace KummerCriterion
variable (p: ℕ) [hp: Fact p.Prime]
variable {K: Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def rp200 (ℓ: ℕ) : Finset (Ideal (𝓞 ((NumberField.maximalRealSubfield K)))) :=
  IsDedekindDomain.primesOverFinset (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K)))
lemma rp201 (ℓ: ℕ) [Fact ℓ.Prime] :
    (rp200 (K:=K) ℓ).card =
      (Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K)))).ncard:= by
  classical
  have: (rp79 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (rp79 ℓ) ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
  unfold rp200
  rw [← Set.ncard_coe_finset,IsDedekindDomain.coe_primesOverFinset hne]
lemma rp202 {ℓ: ℕ} [Fact ℓ.Prime] {P: Ideal (𝓞 ((NumberField.maximalRealSubfield K)))} :
    P ∈ rp200 (K:=K) ℓ ↔
      P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K))):= by
  have: (rp79 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (rp79 ℓ) ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 ((NumberField.maximalRealSubfield K)))
lemma rp203 {ℓ: ℕ} [Fact ℓ.Prime] {P: Ideal (𝓞 K)}
    (hP: P ∈ rp80 K ℓ) :
    P.under (𝓞 ((NumberField.maximalRealSubfield K))) ∈ rp200 (K:=K) ℓ:= by
  have hP_over: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K) :=
    (rp104 (K:=K) (ℓ:=ℓ)).1 hP
  have: P.IsPrime:=hP_over.1
  rw [rp202]
  refine ⟨Ideal.IsPrime.under (𝓞 ((NumberField.maximalRealSubfield K))) P,?_⟩
  rw [Ideal.liesOver_iff,Ideal.under_under]
  exact (Ideal.liesOver_iff _ _).1 hP_over.2
variable [IsCMField K]
lemma rp204 (σ: K ≃ₐ[(NumberField.maximalRealSubfield K)] K) :
    σ = 1 ∨ σ = complexConj K:= by
  by_cases hσ: σ = 1
  · exact Or.inl hσ
  · right
    have hcard: Nat.card (K ≃ₐ[(NumberField.maximalRealSubfield K)] K) = 2 :=
      (IsGalois.card_aut_eq_finrank (NumberField.maximalRealSubfield K) K).trans (rp65 (K:=K))
    rw [Nat.card_eq_two_iff' (1: K ≃ₐ[(NumberField.maximalRealSubfield K)] K)] at hcard
    exact ExistsUnique.unique hcard hσ (complexConj_ne_one K)
lemma rp205 :
    MulSemiringAction.toRingHom (K ≃ₐ[(NumberField.maximalRealSubfield K)] K) (𝓞 K) (complexConj K) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:= by
  ext x
  change (((complexConj K) • x: 𝓞 K) : K) = ((ringOfIntegersComplexConj K x: 𝓞 K) : K)
  rfl
lemma rp206 (P: Ideal (𝓞 K)) :
    complexConj K • P = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:= by
  rw [Ideal.pointwise_smul_def,rp205 (K:=K)]
lemma rp207 {ℓ: ℕ} [Fact ℓ.Prime]
    {P: Ideal (𝓞 K)} (hP: P ∈ rp80 K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ∈ rp80 K ℓ:= by
  let PPlus: Ideal (𝓞 ((NumberField.maximalRealSubfield K))):=P.under (𝓞 ((NumberField.maximalRealSubfield K)))
  have hP_over: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K) :=
    (rp104 (K:=K) (ℓ:=ℓ)).1 hP
  have hPPlus_mem: PPlus ∈ rp200 (K:=K) ℓ:= by
    simpa [PPlus] using rp203 (K:=K) hP
  have hPPlus_over: PPlus ∈ Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K))) :=
    (rp202 (K:=K) (ℓ:=ℓ)).1 hPPlus_mem
  have: P.IsPrime:=hP_over.1
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  have: PPlus.LiesOver (rp79 ℓ):=hPPlus_over.2
  have hmap_liesOver :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver
        (rp79 ℓ) :=
    Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((NumberField.maximalRealSubfield K))) (C:=𝓞 K)
      (𝔓:=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (P:=PPlus) (p:=rp79 ℓ)
  have: (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrime :=
    Ideal.map_isPrime_of_equiv (ringOfIntegersComplexConj K).toRingEquiv
  rw [rp104 (K:=K) (ℓ:=ℓ)]
  exact ⟨inferInstance,hmap_liesOver⟩
lemma rp208 (P: Ideal (𝓞 K)) :
    (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).under (𝓞 ((NumberField.maximalRealSubfield K))) =
      P.under (𝓞 ((NumberField.maximalRealSubfield K))):= by
  let PPlus: Ideal (𝓞 ((NumberField.maximalRealSubfield K))):=P.under (𝓞 ((NumberField.maximalRealSubfield K)))
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  simpa [PPlus] using
    (Ideal.over_def
      (P:=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (A:=𝓞 ((NumberField.maximalRealSubfield K))) (p:=PPlus)).symm
lemma rp209 {ℓ: ℕ} [Fact ℓ.Prime]
    {P Q: Ideal (𝓞 K)} (hP: P ∈ rp80 K ℓ) (hQ: Q ∈ rp80 K ℓ)
    (hunder: P.under (𝓞 ((NumberField.maximalRealSubfield K))) = Q.under (𝓞 ((NumberField.maximalRealSubfield K)))) :
    Q = P ∨ Q = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:= by
  let PPlus: Ideal (𝓞 ((NumberField.maximalRealSubfield K))):=P.under (𝓞 ((NumberField.maximalRealSubfield K)))
  have hP_over: P ∈ Ideal.primesOver PPlus (𝓞 K):= by
    refine ⟨((rp104 (K:=K) (ℓ:=ℓ)).1 hP).1,
      by simp [Ideal.liesOver_iff,PPlus]⟩
  have hQ_over: Q ∈ Ideal.primesOver PPlus (𝓞 K):= by
    refine ⟨((rp104 (K:=K) (ℓ:=ℓ)).1 hQ).1,
      by simpa [Ideal.liesOver_iff,PPlus] using hunder⟩
  have: P.IsPrime:=hP_over.1
  have: Q.IsPrime:=hQ_over.1
  have: Q.LiesOver PPlus:=hQ_over.2
  let _: MulSemiringAction Gal(K/(NumberField.maximalRealSubfield K)) (𝓞 K):=inferInstance
  have _: IsGaloisGroup Gal(K/(NumberField.maximalRealSubfield K)) (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/(NumberField.maximalRealSubfield K))) (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) ((NumberField.maximalRealSubfield K)) K
  obtain ⟨σ,hσ⟩:=Ideal.exists_smul_eq_of_isGaloisGroup
    (A:=𝓞 ((NumberField.maximalRealSubfield K))) (B:=𝓞 K) (p:=PPlus) (P:=P) (Q:=Q) (G:=Gal(K/(NumberField.maximalRealSubfield K)))
  rcases rp204 (K:=K) σ with rfl | rfl
  · left
    simpa using hσ.symm
  · right
    rw [rp206 (K:=K) P] at hσ
    exact hσ.symm
lemma rp210 {ℓ: ℕ} [Fact ℓ.Prime]
    {P: Ideal (𝓞 K)} (hP: P ∈ rp80 K ℓ) :
    let Pconj:=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
    let fiber:=(rp80 K ℓ).filter
      (fun Q => Q.under (𝓞 ((NumberField.maximalRealSubfield K))) = P.under (𝓞 ((NumberField.maximalRealSubfield K))))
    (Pconj = P ∧ fiber = ({P} : Finset (Ideal (𝓞 K)))) ∨
      (Pconj ≠ P ∧ fiber = {P,Pconj}):= by
  classical
  let Pconj: Ideal (𝓞 K):=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
  let fiber: Finset (Ideal (𝓞 K)):=(rp80 K ℓ).filter
    (fun Q => Q.under (𝓞 ((NumberField.maximalRealSubfield K))) = P.under (𝓞 ((NumberField.maximalRealSubfield K))))
  have hPconj: Pconj ∈ rp80 K ℓ:= by
    simpa [Pconj] using rp207 (K:=K) hP
  have hunder_conj: Pconj.under (𝓞 ((NumberField.maximalRealSubfield K))) = P.under (𝓞 ((NumberField.maximalRealSubfield K))):= by
    simpa [Pconj] using rp208 (K:=K) P
  have hP_fiber: P ∈ fiber:= by
    simp [fiber,hP]
  have hPconj_fiber: Pconj ∈ fiber:= by
    simp [fiber,hPconj,hunder_conj]
  have hfiber_subset {Q: Ideal (𝓞 K)} (hQ: Q ∈ fiber) : Q = P ∨ Q = Pconj:= by
    have hQ_mem: Q ∈ rp80 K ℓ:=(Finset.mem_filter.1 hQ).1
    have hQ_under: Q.under (𝓞 ((NumberField.maximalRealSubfield K))) = P.under (𝓞 ((NumberField.maximalRealSubfield K))):=(Finset.mem_filter.1 hQ).2
    rcases rp209 (K:=K) hP hQ_mem hQ_under.symm with
      hQP | hQconj
    · exact Or.inl hQP
    · exact Or.inr (by simpa [Pconj] using hQconj)
  by_cases hfix: Pconj = P
  · left
    refine ⟨hfix,Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj,hfix]
        simp
    · intro hQ
      have hQP: Q = P:= by simpa using hQ
      subst hQP
      exact hP_fiber
  · right
    refine ⟨hfix,Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj]
        simp [Pconj]
    · intro hQ
      have hQ' : Q = P ∨ Q = Pconj:= by
        simpa [hfix] using! hQ
      rcases hQ' with hQP | hQconj
      · rw [hQP]
        exact hP_fiber
      · rw [hQconj]
        exact hPconj_fiber
noncomputable def rp211 (hp_odd: p ≠ 2) : Gal(K/ℚ):= by
  letI: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
  exact
    { (complexConj K).toRingEquiv with
      commutes':=fun q => by
        exact map_ratCast ((complexConj K).toRingEquiv.toRingHom) q }
@[simp] private lemma complexConjRat_apply (hp_odd: p ≠ 2) (x: K) :
    rp211 (p:=p) (K:=K) hp_odd x = complexConj K x:= by
  rfl
lemma rp212 (hp_odd: p ≠ 2) :
    MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K)
        (rp211 (p:=p) (K:=K) hp_odd) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:= by
  ext x
  change rp211 (p:=p) (K:=K) hp_odd x =
      ((ringOfIntegersComplexConj K x: 𝓞 K) : K)
  simp [complexConjRat_apply,coe_ringOfIntegersComplexConj]
lemma rp213 (hp_odd: p ≠ 2) (P: Ideal (𝓞 K)) :
    (rp211 (p:=p) (K:=K) hp_odd • P) =
      P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:= by
  rw [Ideal.pointwise_smul_def,rp212
    (p:=p) (K:=K) hp_odd]
omit [IsCMField K] in
lemma rp214 (hp_odd: p ≠ 2) :
    IsCyclotomicExtension.Rat.galEquivZMod p K
        (rp211 (p:=p) (K:=K) hp_odd) = -1:= by
  have: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
  let c: Gal(K/ℚ):=rp211 (p:=p) (K:=K) hp_odd
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hc :
      c (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1):= by
    have hc':=congrArg (fun x: 𝓞 K => (x: K)) (rp37 (p:=p) (K:=K))
    rw [coe_ringOfIntegersComplexConj] at hc'
    change (complexConj K) hζ.toInteger.1 =
      hζ.toInteger.1 ^ (p - 1) at hc'
    simpa [c,complexConjRat_apply,hζ.coe_toInteger] using hc'
  have hpow :
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1):= by
    calc
      (IsCyclotomicExtension.zeta p ℚ K) ^ (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val
          = c (IsCyclotomicExtension.zeta p ℚ K):= by
              symm
              exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n:=p) (K:=K) c hζ.pow_eq_one
      _ = (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1):=hc
  apply Units.ext
  have hpow':=hpow
  rw [(hζ.isOfFinOrder (NeZero.ne p)).pow_inj_mod,← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff',ZMod.natCast_val,Nat.cast_sub hp.out.one_le,
    ZMod.natCast_self,zero_sub,Nat.cast_one] at hpow'
  simpa [c] using hpow'
lemma rp215
    {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    (hd_even: Even (rp94 (p:=p) ℓ hℓp)) :
    rp93 (p:=p) ℓ hℓp ^ rp190 (p:=p) ℓ hℓp =
      (-1: (ZMod p)ˣ):= by
  let u: (ZMod p)ˣ:=rp93 (p:=p) ℓ hℓp
  let d: ℕ:=rp94 (p:=p) ℓ hℓp
  rcases rp194 (p:=p) hℓp with hpow | hpow
  · have hpow_units: u ^ rp190 (p:=p) ℓ hℓp = 1:= by
      apply Units.ext
      simpa [u,Units.val_pow_eq_pow_val] using hpow
    have hdvd: d ∣ rp190 (p:=p) ℓ hℓp:= by
      simpa [d,rp94,u] using (orderOf_dvd_iff_pow_eq_one (x:=u)).2 hpow_units
    have hd_pos: 0 < d:= by
      dsimp [d,rp94,u]
      exact orderOf_pos u
    have hhalf: rp190 (p:=p) ℓ hℓp = d / 2:= by
      simpa [d] using rp192 (p:=p) hℓp hd_even
    have hhalf_pos: 0 < d / 2:= by
      rcases hd_even with ⟨k,hk⟩
      rw [show d = 2 * k by omega]
      omega
    have hle: d ≤ d / 2:= by
      rw [hhalf] at hdvd
      exact Nat.le_of_dvd hhalf_pos hdvd
    omega
  · apply Units.ext
    simpa [u,Units.val_pow_eq_pow_val] using hpow
lemma rp216
    (hp_odd: p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    (-1: (ZMod p)ˣ) ∈ Subgroup.zpowers (rp93 (p:=p) ℓ hℓp) ↔
      Even (rp94 (p:=p) ℓ hℓp):= by
  let u: (ZMod p)ˣ:=rp93 (p:=p) ℓ hℓp
  constructor
  · intro hneg
    have htwo: 2 ∣ orderOf u:= by
      have horder_neg: orderOf (-1: (ZMod p)ˣ) = 2:= by
        rw [← orderOf_units,Units.coe_neg_one,orderOf_neg_one,ringChar.eq (ZMod p) p,
          if_neg hp_odd]
      exact horder_neg ▸ orderOf_dvd_of_mem_zpowers hneg
    simpa [u,rp94,even_iff_two_dvd] using htwo
  · intro hd_even
    refine Subgroup.mem_zpowers_iff.mpr ⟨rp190 (p:=p) ℓ hℓp,?_⟩
    rw [zpow_natCast]
    exact rp215 (p:=p) hℓp hd_even
omit [IsCMField K] in
lemma rp217
    (hp_odd: p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    {P: Ideal (𝓞 K)} (hP: P ∈ rp80 K ℓ) :
    (rp211 (p:=p) (K:=K) hp_odd ∈ MulAction.stabilizer Gal(K/ℚ) P) ↔
      Even (rp94 (p:=p) ℓ hℓp):= by
  let c: Gal(K/ℚ):=rp211 (p:=p) (K:=K) hp_odd
  have hP_over: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K) :=
    (rp104 (K:=K) (ℓ:=ℓ)).1 hP
  have: P.LiesOver (Ideal.span {(ℓ: ℤ)}):= by
    simpa [rp79] using hP_over.2
  have: (rp79 ℓ).IsMaximal:= by
    simpa [rp79] using Int.ideal_span_isMaximal_of_prime ℓ
  have: P.IsMaximal:=Ideal.isMaximal_of_mem_primesOver hP_over
  constructor
  · intro hc
    have hmem_map: IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P):=⟨c,hc,rfl⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n:=p) (K:=K) (p:=ℓ) (P:=P)
      ((rp92 (p:=p) hℓp).symm),rp214
      (p:=p) (K:=K) hp_odd] at hmem_map
    simpa [rp93] using
      (rp216
        (p:=p) hp_odd hℓp).1 hmem_map
  · intro h_even
    have hneg_mem: (-1: (ZMod p)ˣ) ∈ Subgroup.zpowers (rp93 (p:=p) ℓ hℓp) :=
      (rp216 (p:=p) hp_odd hℓp).2 h_even
    have hmem_map: IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P):= by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n:=p) (K:=K) (p:=ℓ) (P:=P)
        ((rp92 (p:=p) hℓp).symm),rp214
        (p:=p) (K:=K) hp_odd]
      simpa [rp93] using hneg_mem
    rcases hmem_map with ⟨σ,hσ,hσeq⟩
    have hc_eq: σ = c:=(IsCyclotomicExtension.Rat.galEquivZMod p K).injective hσeq
    subst hc_eq
    exact hσ
lemma rp218
    (hp_odd: p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    {P: Ideal (𝓞 K)} (hP: P ∈ rp80 K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      Even (rp94 (p:=p) ℓ hℓp):= by
  let c: Gal(K/ℚ):=rp211 (p:=p) (K:=K) hp_odd
  constructor
  · intro hmap
    have hsmul: c • P = P:= by
      rw [rp213 (p:=p) (K:=K) hp_odd]
      exact hmap
    have hc: c ∈ MulAction.stabilizer Gal(K/ℚ) P:= by simpa [c] using hsmul
    exact (rp217
      (p:=p) (K:=K) hp_odd hℓp hP).1 hc
  · intro h_even
    have hc: c ∈ MulAction.stabilizer Gal(K/ℚ) P :=
      (rp217
        (p:=p) (K:=K) hp_odd hℓp hP).2 h_even
    have hsmul: c • P = P:= by simpa [c] using hc
    rw [rp213 (p:=p) (K:=K) hp_odd] at hsmul
    exact hsmul
lemma rp219
    (hp_odd: p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    {P: Ideal (𝓞 K)} (hP: P ∈ rp80 K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      rp190 (p:=p) ℓ hℓp = rp94 (p:=p) ℓ hℓp / 2:= by
  rw [rp218
    (p:=p) (K:=K) hp_odd hℓp hP]
  constructor
  · exact rp192 (p:=p) hℓp
  · intro hhalf
    by_contra hodd
    have hself:=rp193 (p:=p) hℓp hodd
    have hpos: 0 < rp94 (p:=p) ℓ hℓp:= by
      unfold rp94 rp93
      exact orderOf_pos _
    rw [hself] at hhalf
    omega
omit [IsCMField K] in
lemma rp220 {ℓ: ℕ} [Fact ℓ.Prime]
    {P: Ideal (𝓞 K)} (hP: P ∈ rp80 K ℓ)
    {PPlus: Ideal (𝓞 ((NumberField.maximalRealSubfield K)))} (hPPlus: P.under (𝓞 ((NumberField.maximalRealSubfield K))) = PPlus) :
    let fiber:=(rp80 K ℓ).filter
      (fun Q => Q.under (𝓞 ((NumberField.maximalRealSubfield K))) = PPlus)
    fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard:= by
  classical
  let fiber: Finset (Ideal (𝓞 K)):=(rp80 K ℓ).filter
    (fun Q => Q.under (𝓞 ((NumberField.maximalRealSubfield K))) = PPlus)
  have hPPlus_mem: PPlus ∈ rp200 (K:=K) ℓ:= by
    simpa [hPPlus] using rp203 (K:=K) hP
  have hPPlus_over: PPlus ∈ Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K))) :=
    (rp202 (K:=K) (ℓ:=ℓ)).1 hPPlus_mem
  have: PPlus.LiesOver (rp79 ℓ):=hPPlus_over.2
  have hfiber: (↑fiber: Set (Ideal (𝓞 K))) = Ideal.primesOver PPlus (𝓞 K):= by
    ext Q
    constructor
    · intro hQ
      rw [Finset.mem_coe,Finset.mem_filter] at hQ
      rcases hQ with ⟨hQ_fin,hQ_under⟩
      have hQ_over: Q ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K) :=
        (rp104 (K:=K) (ℓ:=ℓ)).1 hQ_fin
      have: Q.IsPrime:=hQ_over.1
      exact ⟨inferInstance,(Ideal.liesOver_iff _ _).2 hQ_under.symm⟩
    · intro hQ
      have: Q.IsPrime:=hQ.1
      have: Q.LiesOver PPlus:=hQ.2
      have hQ_over: Q.LiesOver (rp79 ℓ) :=
        Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((NumberField.maximalRealSubfield K))) (C:=𝓞 K)
          (𝔓:=Q) (P:=PPlus) (p:=rp79 ℓ)
      have hQ_fin: Q ∈ rp80 K ℓ:= by
        rw [rp104 (K:=K) (ℓ:=ℓ)]
        exact ⟨inferInstance,hQ_over⟩
      have hQ_under: Q.under (𝓞 ((NumberField.maximalRealSubfield K))) = PPlus :=
        ((Ideal.liesOver_iff _ _).1 (show Q.LiesOver PPlus from inferInstance)).symm
      rw [Finset.mem_coe,Finset.mem_filter]
      exact ⟨hQ_fin,hQ_under⟩
  simpa [fiber] using (show fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard from by
    rw [← Set.ncard_coe_finset,hfiber])
omit [IsCMField K] in
lemma rp221
    (hp_odd: p ≠ 2) {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    (PPlus: Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (hPPlus: PPlus ∈ Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K)))) :
    PPlus.inertiaDeg ℤ = rp190 (p:=p) ℓ hℓp:= by
  classical
  have: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
  have: PPlus.IsPrime:=hPPlus.1
  have: PPlus.LiesOver (rp79 ℓ):=hPPlus.2
  obtain ⟨⟨P,hP_prime,hP_over_PPlus⟩⟩:=PPlus.nonempty_primesOver (S:=𝓞 K)
  have hP_over: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K):= by
    refine ⟨hP_prime,?_⟩
    exact Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((NumberField.maximalRealSubfield K))) (C:=𝓞 K)
      (𝔓:=P) (P:=PPlus) (p:=rp79 ℓ)
  have hP_fin: P ∈ rp80 K ℓ :=
    (rp104 (K:=K) (ℓ:=ℓ)).2 hP_over
  have hℓ_ne: rp79 ℓ ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
  have hPPlus_eq: P.under (𝓞 ((NumberField.maximalRealSubfield K))) = PPlus :=
    ((Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)).symm
  let fiber: Finset (Ideal (𝓞 K)):=(rp80 K ℓ).filter
    (fun Q => Q.under (𝓞 ((NumberField.maximalRealSubfield K))) = PPlus)
  have hfiber_ncard: fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard:= by
    simpa [fiber] using rp220
      (K:=K) hP_fin hPPlus_eq
  have hram_tower :
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ * P.ramificationIdx (𝓞 ((NumberField.maximalRealSubfield K))):= by
    simpa using Ideal.ramificationIdx_tower
      (R:=ℤ) (S:=𝓞 ((NumberField.maximalRealSubfield K))) (T:=𝓞 K) (q:=PPlus) (r:=P)
  have hram_rel: P.ramificationIdx (𝓞 ((NumberField.maximalRealSubfield K))) = 1:= by
    apply Nat.eq_one_of_dvd_one
    refine ⟨PPlus.ramificationIdx ℤ,?_⟩
    rw [mul_comm,← hram_tower,
      rp115 (p:=p) (K:=K) hℓp P hP_over]
  have hPPlus_ne_bot: PPlus ≠ ⊥:= by
    intro hbot
    have hlie: PPlus.LiesOver (rp79 ℓ):=inferInstance
    have hover:=(Ideal.liesOver_iff _ _).1 hlie
    have hcomap_bot :
        Ideal.comap (algebraMap ℤ (𝓞 ((NumberField.maximalRealSubfield K)))) (⊥ : Ideal (𝓞 ((NumberField.maximalRealSubfield K)))) = ⊥:= by
      ext x
      simp
    have hneq: rp79 ℓ ≠ ⊥:= by
      rw [rp79,Ne,Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
    exact hneq (by simpa [Ideal.under_def,hbot,hcomap_bot] using hover)
  have _: IsGaloisGroup Gal(K/(NumberField.maximalRealSubfield K)) (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/(NumberField.maximalRealSubfield K))) (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) ((NumberField.maximalRealSubfield K)) K
  have hquad: (Ideal.primesOver PPlus (𝓞 K)).ncard * P.inertiaDeg (𝓞 ((NumberField.maximalRealSubfield K))) = 2:= by
    have hfund:=Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p:=PPlus)
      (B:=𝓞 K) (G:=Gal(K/(NumberField.maximalRealSubfield K)))
    have hcard_gal: Nat.card Gal(K/(NumberField.maximalRealSubfield K)) = 2 :=
      (IsGalois.card_aut_eq_finrank (NumberField.maximalRealSubfield K) K).trans (rp65 (K:=K))
    rw [hcard_gal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (p:=PPlus) (P:=P) (G:=Gal(K/(NumberField.maximalRealSubfield K))),
      Ideal.inertiaDegIn_eq_inertiaDeg (p:=PPlus) (P:=P) (G:=Gal(K/(NumberField.maximalRealSubfield K))),
      hram_rel] at hfund
    simpa using hfund
  have hinertia_tower :
      P.inertiaDeg ℤ =
        PPlus.inertiaDeg ℤ * P.inertiaDeg (𝓞 ((NumberField.maximalRealSubfield K))):= by
    simpa using Ideal.inertiaDeg_tower
      (R:=ℤ) (S:=𝓞 ((NumberField.maximalRealSubfield K))) (T:=𝓞 K) (q:=PPlus) (r:=P)
  have hP_inertia :
      P.inertiaDeg ℤ = rp94 (p:=p) ℓ hℓp:= by
    exact rp114 (p:=p) (K:=K) hℓp P hP_over
  by_cases hfix: P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P
  · have hfiber_card: fiber.card = 1:= by
      rcases rp210 (K:=K) hP_fin with
        hsingle | hpair
      · have hsingle_fiber: fiber = ({P} : Finset (Ideal (𝓞 K))):= by
          simpa [fiber,hPPlus_eq] using hsingle.2
        rw [hsingle_fiber]
        simp
      · exact (hpair.1 hfix).elim
    have hcard_primes: (Ideal.primesOver PPlus (𝓞 K)).ncard = 1:= by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia: P.inertiaDeg (𝓞 ((NumberField.maximalRealSubfield K))) = 2:= by
      rw [hcard_primes] at hquad
      simpa using hquad
    have hhalf: rp190 (p:=p) ℓ hℓp =
        rp94 (p:=p) ℓ hℓp / 2 :=
      (rp219
        (p:=p) (K:=K) hp_odd hℓp hP_fin).1 hfix
    rw [hhalf]
    rw [hP_inertia,hrel_inertia] at hinertia_tower
    omega
  · have hfiber_card: fiber.card = 2:= by
      rcases rp210 (K:=K) hP_fin with
        hsingle | hpair
      · exact (hfix hsingle.1).elim
      · have hpair_fiber :
            fiber =
              ({P,P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom} :
                Finset (Ideal (𝓞 K))):= by
          simpa [fiber,hPPlus_eq] using hpair.2
        rw [hpair_fiber]
        rw [Finset.card_eq_two]
        exact ⟨P,P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          by simpa [eq_comm] using hpair.1,rfl⟩
    have hcard_primes: (Ideal.primesOver PPlus (𝓞 K)).ncard = 2:= by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia: P.inertiaDeg (𝓞 ((NumberField.maximalRealSubfield K))) = 1:= by
      rw [hcard_primes] at hquad
      omega
    have hnot_even: ¬ Even (rp94 (p:=p) ℓ hℓp):=fun h_even =>
      hfix
        ((rp218
          (p:=p) (K:=K) hp_odd hℓp hP_fin).2 h_even)
    have hself: rp190 (p:=p) ℓ hℓp =
        rp94 (p:=p) ℓ hℓp :=
      rp193 (p:=p) hℓp hnot_even
    rw [hself]
    rw [hP_inertia,hrel_inertia] at hinertia_tower
    omega
omit [IsCMField K] in
lemma rp222 {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p)
    (PPlus: Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (hPPlus: PPlus ∈ Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K)))) :
    PPlus.ramificationIdx ℤ = 1:= by
  have: PPlus.IsPrime:=hPPlus.1
  have: PPlus.LiesOver (rp79 ℓ):=hPPlus.2
  obtain ⟨⟨P,hP_prime,hP_over_PPlus⟩⟩:=PPlus.nonempty_primesOver (S:=𝓞 K)
  have hP_over: P ∈ Ideal.primesOver (rp79 ℓ) (𝓞 K):= by
    refine ⟨hP_prime,?_⟩
    exact Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((NumberField.maximalRealSubfield K))) (C:=𝓞 K)
      (𝔓:=P) (P:=PPlus) (p:=rp79 ℓ)
  have hram_tower :
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ * P.ramificationIdx (𝓞 ((NumberField.maximalRealSubfield K))):= by
    simpa using Ideal.ramificationIdx_tower
      (R:=ℤ) (S:=𝓞 ((NumberField.maximalRealSubfield K))) (T:=𝓞 K) (q:=PPlus) (r:=P)
  have hℓ_ne: rp79 ℓ ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
  have hram_abs: P.ramificationIdx ℤ = 1:= by
    exact KummerCriterion.rp115 (p:=p) (K:=K) hℓp P hP_over
  apply Nat.eq_one_of_dvd_one
  refine ⟨P.ramificationIdx (𝓞 ((NumberField.maximalRealSubfield K))),?_⟩
  rw [← hram_tower,hram_abs]
lemma rp223 (hp_odd: p ≠ 2)
    {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) :
    (Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K)))).ncard =
      rp191 (p:=p) ℓ hℓp:= by
  have: (rp79 ℓ).IsMaximal:= by
    simpa [rp79] using Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (rp79 ℓ) ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out: ℓ.Prime).ne_zero
  have hcoe: ((rp200 (K:=K) ℓ: Finset (Ideal (𝓞 ((NumberField.maximalRealSubfield K))))) :
      Set (Ideal (𝓞 ((NumberField.maximalRealSubfield K))))) = Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K))) :=
    IsDedekindDomain.coe_primesOverFinset hne (𝓞 ((NumberField.maximalRealSubfield K)))
  have hsum :
      ∑ PPlus ∈ rp200 (K:=K) ℓ,
          PPlus.ramificationIdx ℤ * PPlus.inertiaDeg ℤ = Module.finrank ℚ ((NumberField.maximalRealSubfield K)):= by
    rw [← NumberField.RingOfIntegers.rank ((NumberField.maximalRealSubfield K)),
      ← Ideal.sum_ramification_inertia_eq_finrank (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K))),
      ← Finset.sum_coe_sort]
    exact Fintype.sum_equiv (Equiv.setCongr hcoe) _ _ fun _ => rfl
  have hsum_const :
      (rp200 (K:=K) ℓ).card * rp190 (p:=p) ℓ hℓp =
        Module.finrank ℚ ((NumberField.maximalRealSubfield K)):= by
    calc
      (rp200 (K:=K) ℓ).card * rp190 (p:=p) ℓ hℓp
          = ∑ PPlus ∈ rp200 (K:=K) ℓ,
              rp190 (p:=p) ℓ hℓp:= by
              simp
      _ = ∑ PPlus ∈ rp200 (K:=K) ℓ,
              PPlus.ramificationIdx ℤ * PPlus.inertiaDeg ℤ:= by
              refine Finset.sum_congr rfl ?_
              intro PPlus hPPlus_fin
              have hPPlus: PPlus ∈ Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K))) :=
                (rp202 (K:=K) (ℓ:=ℓ)).1 hPPlus_fin
              rw [rp222 (p:=p) (K:=K) hℓp PPlus hPPlus,
                rp221 (p:=p) (K:=K)
                  hp_odd hℓp PPlus hPPlus]
              simp
      _ = Module.finrank ℚ ((NumberField.maximalRealSubfield K)):=hsum
  rw [rp201 (K:=K) (ℓ:=ℓ),
    rp66 (p:=p) (K:=K)] at hsum_const
  have hlocal:=rp197 (p:=p) hp_odd hℓp
  rw [rp196 (p:=p) hp_odd] at hlocal
  have hd_pos: 0 < rp94 (p:=p) ℓ hℓp:= by
    dsimp [rp94]
    exact orderOf_pos (rp93 (p:=p) ℓ hℓp)
  have hfd_pos: 0 < rp190 (p:=p) ℓ hℓp:= by
    by_cases hde: Even (rp94 (p:=p) ℓ hℓp)
    · rcases hde with ⟨k,hk⟩
      rw [rp192 (p:=p) hℓp ⟨k,hk⟩]
      omega
    · rw [rp193 (p:=p) hℓp hde]
      exact hd_pos
  have hmul :
      (Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K)))).ncard *
        rp190 (p:=p) ℓ hℓp =
          rp191 (p:=p) ℓ hℓp * rp190 (p:=p) ℓ hℓp:= by
    omega
  exact Nat.eq_of_mul_eq_mul_right hfd_pos (by simpa [Nat.mul_comm] using hmul)
lemma rp224 (hp_odd: p ≠ 2)
    {ℓ: ℕ} [Fact ℓ.Prime] (hℓp: ℓ ≠ p) {s: ℂ} :
    rp87 (NumberField.maximalRealSubfield K) ℓ s =
      (1 - (ℓ: ℂ) ^ (-(rp190 (p:=p) ℓ hℓp: ℂ) * s)) ^
        rp191 (p:=p) ℓ hℓp:= by
  classical
  have hcard_eq :
      (rp200 (K:=K) ℓ).card =
        rp191 (p:=p) ℓ hℓp:= by
    rw [rp201 (K:=K) (ℓ:=ℓ)]
    exact rp223 (p:=p) (K:=K) hp_odd hℓp
  unfold rp87
  change Finset.prod (rp200 (K:=K) ℓ) (fun PPlus =>
      (1 - (Ideal.absNorm PPlus: ℂ) ^ (-s))) =
        (1 - (ℓ: ℂ) ^ (-(rp190 (p:=p) ℓ hℓp: ℂ) * s)) ^
          rp191 (p:=p) ℓ hℓp
  have hprod_eq: ∀ PPlus ∈ rp200 (K:=K) ℓ,
      (1 - (Ideal.absNorm PPlus: ℂ) ^ (-s)) =
        1 - (ℓ: ℂ) ^ (-(rp190 (p:=p) ℓ hℓp: ℂ) * s):= by
    intro PPlus hP
    have hPmem: PPlus ∈ Ideal.primesOver (rp79 ℓ) (𝓞 ((NumberField.maximalRealSubfield K))) :=
      (rp202 (K:=K) (ℓ:=ℓ)).1 hP
    have: PPlus.LiesOver (rp79 ℓ):=hPmem.2
    have: PPlus.LiesOver (Ideal.span {(ℓ: ℤ)}):=hPmem.2
    have: (rp79 ℓ).IsMaximal:= by
      simpa [rp79] using Int.ideal_span_isMaximal_of_prime ℓ
    have: PPlus.IsMaximal:=Ideal.isMaximal_of_mem_primesOver hPmem
    have habsNorm: Ideal.absNorm PPlus = ℓ ^ (rp190 (p:=p) ℓ hℓp):= by
      rw [← rp221 (p:=p) (K:=K)
        hp_odd hℓp PPlus hPmem,
        ← Ideal.inertiaDeg'_eq_inertiaDeg (p:=rp79 ℓ) (q:=PPlus)]
      simpa [rp79] using Ideal.absNorm_eq_pow_inertiaDeg' PPlus (Fact.out: ℓ.Prime)
    rw [habsNorm]
    push_cast
    have:=Complex.natCast_cpow_natCast_mul ℓ (rp190 (p:=p) ℓ hℓp) (-s)
    rw [show -((rp190 (p:=p) ℓ hℓp: ℂ)) * s =
        ((rp190 (p:=p) ℓ hℓp: ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq,Finset.prod_const,hcard_eq]
omit [IsCMField K] in
lemma rp225 :
    rp34 p K ∈ Ideal.primesOver (rp79 p) (𝓞 K):= by
  refine ⟨zetaPrime_isPrime p K,?_⟩
  have: IsCyclotomicExtension {p ^ (0 + 1)} ℚ K:= by
    simpa using (inferInstance: IsCyclotomicExtension {p} ℚ K)
  simpa [rp34,rp79] using
    (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p:=p) (k:=0)
      (K:=K) (hζ:=IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))
omit [IsCMField K] in
lemma rp226 :
    Ideal.primesOver (rp79 p) (𝓞 K) = {rp34 p K}:= by
  classical
  obtain ⟨P,hP⟩ :=
    Set.ncard_eq_one.mp (rp112 (p:=p) (K:=K))
  have hzeta: rp34 p K = P:= by
    have hzeta_mem:=rp225 (p:=p) (K:=K)
    rw [hP] at hzeta_mem
    simpa using hzeta_mem
  simpa [hzeta] using hP
lemma rp227 :
    rp36 p K ∈ Ideal.primesOver (rp79 p) (𝓞 ((NumberField.maximalRealSubfield K))):= by
  refine ⟨inferInstance,?_⟩
  have: IsCyclotomicExtension {p ^ (0 + 1)} ℚ K:= by
    simpa using (inferInstance: IsCyclotomicExtension {p} ℚ K)
  have hzeta_over: (rp34 p K).LiesOver (rp79 p):= by
    simpa [rp34,rp79] using
      (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p:=p) (k:=0)
        (K:=K) (hζ:=IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))
  rw [Ideal.liesOver_iff,rp36,Ideal.under_under]
  exact Ideal.over_def (P:=rp34 p K) (A:=ℤ) (p:=rp79 p)
lemma rp228 :
    Ideal.primesOver (rp79 p) (𝓞 ((NumberField.maximalRealSubfield K))) = {rp36 p K}:= by
  classical
  ext PPlus
  constructor
  · intro hPPlus
    have: PPlus.IsPrime:=hPPlus.1
    have: PPlus.LiesOver (rp79 p):=hPPlus.2
    obtain ⟨⟨P,hP_prime,hP_over_PPlus⟩⟩:=PPlus.nonempty_primesOver (S:=𝓞 K)
    have hP: P ∈ Ideal.primesOver (rp79 p) (𝓞 K):= by
      refine ⟨hP_prime,?_⟩
      exact Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((NumberField.maximalRealSubfield K))) (C:=𝓞 K)
        (𝔓:=P) (P:=PPlus) (p:=rp79 p)
    have hP_eq: P = rp34 p K:= by
      rw [rp226 (p:=p) (K:=K)] at hP
      simpa using hP
    have hPPlus_eq: PPlus = rp36 p K:= by
      simpa [rp36,hP_eq] using
        (Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)
    simp [hPPlus_eq]
  · intro hPPlus
    rw [Set.mem_singleton_iff] at hPPlus
    simpa [hPPlus] using rp227 (p:=p) (K:=K)
lemma rp229 :
    (Ideal.primesOver (rp79 p) (𝓞 ((NumberField.maximalRealSubfield K)))).ncard = 1:= by
  rw [rp228 (p:=p) (K:=K)]
  simp
lemma rp230 :
    (rp36 p K).inertiaDeg ℤ = 1:= by
  have hinertia_tower :
      (rp34 p K).inertiaDeg ℤ =
        (rp36 p K).inertiaDeg ℤ *
          (rp34 p K).inertiaDeg (𝓞 ((NumberField.maximalRealSubfield K))):= by
    simpa using Ideal.inertiaDeg_tower
      (R:=ℤ) (S:=𝓞 ((NumberField.maximalRealSubfield K))) (T:=𝓞 K) (q:=rp36 p K) (r:=rp34 p K)
  have hzeta_inertia :
      (rp34 p K).inertiaDeg ℤ = 1:= by
    exact rp113 (p:=p) (K:=K) (rp34 p K)
      (rp225 (p:=p) (K:=K))
  rw [hzeta_inertia] at hinertia_tower
  exact Nat.eq_one_of_dvd_one <|
    ⟨(rp34 p K).inertiaDeg (𝓞 ((NumberField.maximalRealSubfield K))),hinertia_tower⟩
lemma rp231 (PPlus: Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (hPPlus: PPlus ∈ Ideal.primesOver (rp79 p) (𝓞 ((NumberField.maximalRealSubfield K)))) :
    PPlus.inertiaDeg ℤ = 1:= by
  have hPPlus_eq: PPlus = rp36 p K:= by
    rw [rp228 (p:=p) (K:=K)] at hPPlus
    simpa using hPPlus
  simpa [hPPlus_eq] using rp230 (p:=p) (K:=K)
lemma rp232 {s: ℂ} :
    rp87 (NumberField.maximalRealSubfield K) p s = 1 - (p: ℂ) ^ (-s):= by
  classical
  unfold rp87 rp80 rp79
  have hne: (Ideal.span {(p: ℤ)} : Ideal ℤ) ≠ ⊥:= by
    rw [Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe :=
    IsDedekindDomain.coe_primesOverFinset (p:=(Ideal.span {(p: ℤ)} : Ideal ℤ)) hne
      (𝓞 ((NumberField.maximalRealSubfield K)))
  have hcard: (IsDedekindDomain.primesOverFinset (Ideal.span {(p: ℤ)} : Ideal ℤ)
      (𝓞 ((NumberField.maximalRealSubfield K)))).card = 1:= by
    have hncard: ((Ideal.span {(p: ℤ)}).primesOver (𝓞 ((NumberField.maximalRealSubfield K)))).ncard = 1:= by
      simpa [rp79] using rp229 (p:=p) (K:=K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨PPlus,hPPlus⟩:=Finset.card_eq_one.mp hcard
  rw [hPPlus,Finset.prod_singleton]
  have hPPlus_mem: PPlus ∈ (Ideal.span {(p: ℤ)}).primesOver (𝓞 ((NumberField.maximalRealSubfield K))):= by
    rw [← hcoe]
    rw [hPPlus]
    exact Finset.mem_singleton_self PPlus
  have: PPlus.LiesOver (Ideal.span {(p: ℤ)}):= by
    simpa [rp79] using hPPlus_mem.2
  have: PPlus.IsMaximal:=Ideal.isMaximal_of_mem_primesOver (by
    simpa [rp79] using hPPlus_mem)
  have habsNorm: Ideal.absNorm PPlus = p ^ (1: ℕ):= by
    rw [← rp231 (p:=p) (K:=K) PPlus]
    · rw [← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p: ℤ)}) PPlus]
      exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
    · simpa [rp79] using hPPlus_mem
  rw [habsNorm]
  push_cast
  rw [pow_one]
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section NumberFieldEulerProduct
variable (L: Type*) [Field L] [NumberField L]
abbrev rp233: Type _:={I: Ideal (𝓞 L) // I ≠ ⊥}
noncomputable def rp234 (n: ℕ) : ℕ :=
  Nat.card {I: rp233 L // Ideal.absNorm I.1 = n}
lemma rp235: rp234 L 0 = 0:= by
  unfold rp234
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I,hI⟩,hnorm⟩
  exact hI (Ideal.absNorm_eq_zero_iff.mp hnorm)
lemma rp236: rp234 L 1 = 1:= by
  have: Unique {I: rp233 L // Ideal.absNorm I.1 = 1} :=
    { default:=⟨⟨⊤,by simp⟩,Ideal.absNorm_top⟩
      uniq:= by
        rintro ⟨⟨I,hI⟩,hnorm⟩
        exact Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique
lemma rp237 {m n: ℕ} (hcop: Nat.Coprime m n) :
    rp234 L (m * n) =
      rp234 L m * rp234 L n:= by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.Coprime,Nat.gcd_zero_left] at hcop
    subst hcop
    simp [rp235,rp236]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.Coprime,Nat.gcd_zero_right] at hcop
    subst hcop
    simp [rp235,rp236]
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  all_goals rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · classical
    have h_cop_spans: (Ideal.span {(m: 𝓞 L)}) ⊔ (Ideal.span {(n: 𝓞 L)}) = ⊤:= by
      rw [← Ideal.isCoprime_iff_sup_eq,Ideal.isCoprime_span_singleton_iff]
      have hZ: IsCoprime (m: ℤ) (n: ℤ):=Nat.Coprime.isCoprime hcop
      simpa using hZ.map (algebraMap ℤ (𝓞 L))
    have h_mul_sup: ∀ (I: Ideal (𝓞 L)),
        (I ⊔ Ideal.span {(m: 𝓞 L)}) * (I ⊔ Ideal.span {(n: 𝓞 L)}) =
          I ⊔ Ideal.span {(m: 𝓞 L) * (n: 𝓞 L)}:=fun I => by
      rw [Ideal.sup_mul,Ideal.mul_sup,Ideal.mul_sup,
        mul_comm (Ideal.span {(m: 𝓞 L)}) I,
        Ideal.span_singleton_mul_span_singleton,
        show I * I ⊔ I * Ideal.span {(n: 𝓞 L)} ⊔
            (I * Ideal.span {(m: 𝓞 L)} ⊔ Ideal.span {(m: 𝓞 L) * (n: 𝓞 L)}) =
            (I * I ⊔ I * Ideal.span {(n: 𝓞 L)} ⊔ I * Ideal.span {(m: 𝓞 L)}) ⊔
              Ideal.span {(m: 𝓞 L) * (n: 𝓞 L)} from by ac_rfl,
        ← Ideal.mul_sup,← Ideal.mul_sup,
        show I ⊔ Ideal.span {(n: 𝓞 L)} ⊔ Ideal.span {(m: 𝓞 L)} = ⊤ from by
          rw [sup_assoc,sup_comm (Ideal.span {(n: 𝓞 L)}) _,h_cop_spans,sup_top_eq],
        Ideal.mul_top]
    have h_sup_absNorm: ∀ (I: Ideal (𝓞 L)),Ideal.absNorm I = m * n →
        I ⊔ Ideal.span {(m: 𝓞 L) * (n: 𝓞 L)} = I:=fun I hI => by
      refine le_antisymm (sup_le le_rfl ?_) le_sup_left
      rw [Ideal.span_le,Set.singleton_subset_iff]
      have: ((m * n: ℕ) : 𝓞 L) ∈ I:= by
        rw [← hI]
        exact Ideal.absNorm_mem I
      push_cast at this
      exact this
    have h_cop_lift: ∀ (I: Ideal (𝓞 L)),
        IsCoprime (I ⊔ Ideal.span {(m: 𝓞 L)}) (I ⊔ Ideal.span {(n: 𝓞 L)}):=fun I => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = (Ideal.span {(m: 𝓞 L)}) ⊔ (Ideal.span {(n: 𝓞 L)}):=h_cop_spans.symm
        _ ≤ (I ⊔ Ideal.span {(m: 𝓞 L)}) ⊔ (I ⊔ Ideal.span {(n: 𝓞 L)}) :=
            sup_le_sup le_sup_right le_sup_right
    have h_abs_span_nat: ∀ (r: ℕ),Ideal.absNorm (Ideal.span {(r: 𝓞 L)}) =
        r ^ Module.finrank ℤ (𝓞 L):=fun r => by
      rw [Ideal.absNorm_span_singleton,
        show ((r: 𝓞 L)) = algebraMap ℤ (𝓞 L) (r: ℤ) from by push_cast; rfl,
        Algebra.norm_algebraMap_of_basis (Module.finBasis ℤ (𝓞 L))]
      simp
    have h_fwd_norms: ∀ (I: Ideal (𝓞 L)),Ideal.absNorm I = m * n →
        Ideal.absNorm (I ⊔ Ideal.span {(m: 𝓞 L)}) = m ∧
          Ideal.absNorm (I ⊔ Ideal.span {(n: 𝓞 L)}) = n:=fun I hI => by
      set a:=Ideal.absNorm (I ⊔ Ideal.span {(m: 𝓞 L)}) with ha_def
      set b:=Ideal.absNorm (I ⊔ Ideal.span {(n: 𝓞 L)}) with hb_def
      have h_prod: (I ⊔ Ideal.span {(m: 𝓞 L)}) * (I ⊔ Ideal.span {(n: 𝓞 L)}) = I:= by
        rw [h_mul_sup I,h_sup_absNorm I hI]
      have h_ab: a * b = m * n:= by
        rw [ha_def,hb_def,← map_mul,h_prod,hI]
      have h_a_dvd_md: a ∣ m ^ Module.finrank ℤ (𝓞 L):= by
        rw [← h_abs_span_nat m]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_b_dvd_nd: b ∣ n ^ Module.finrank ℤ (𝓞 L):= by
        rw [← h_abs_span_nat n]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_cop_an: Nat.Coprime a n :=
        (hcop.pow_left _).coprime_dvd_left h_a_dvd_md
      have h_cop_bm: Nat.Coprime b m :=
        (hcop.symm.pow_left _).coprime_dvd_left h_b_dvd_nd
      have h_a_dvd_m: a ∣ m :=
        h_cop_an.dvd_of_dvd_mul_right ⟨b,h_ab.symm⟩
      have h_b_dvd_n: b ∣ n :=
        h_cop_bm.dvd_of_dvd_mul_right ⟨a,by linarith [h_ab,mul_comm a b,mul_comm m n]⟩
      have ha_le: a ≤ m:=Nat.le_of_dvd hm h_a_dvd_m
      have hb_le: b ≤ n:=Nat.le_of_dvd hn h_b_dvd_n
      have ha_ge: m ≤ a:= by
        have h1: m * n ≤ a * n:= by
          calc
            m * n = a * b:=h_ab.symm
            _ ≤ a * n:=Nat.mul_le_mul_left a hb_le
        exact Nat.le_of_mul_le_mul_right h1 hn
      have hb_ge: n ≤ b:= by
        have h1: m * n ≤ m * b:= by
          calc
            m * n = a * b:=h_ab.symm
            _ ≤ m * b:=Nat.mul_le_mul_right b ha_le
        exact Nat.le_of_mul_le_mul_left h1 hm
      exact ⟨Nat.le_antisymm ha_le ha_ge,Nat.le_antisymm hb_le hb_ge⟩
    have h_cop_m_L: ∀ (L' : Ideal (𝓞 L)),Ideal.absNorm L' = n →
        IsCoprime (Ideal.span {(m: 𝓞 L)}) L':=fun L' hL => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(m: 𝓞 L)} ⊔ Ideal.span {(n: 𝓞 L)}:=h_cop_spans.symm
        _ ≤ Ideal.span {(m: 𝓞 L)} ⊔ L':=sup_le_sup_left (by
            rw [Ideal.span_le,Set.singleton_subset_iff]
            have: ((n: ℕ) : 𝓞 L) ∈ L':= by
              rw [← hL]
              exact Ideal.absNorm_mem L'
            exact_mod_cast this) _
    have h_cop_n_J: ∀ (J: Ideal (𝓞 L)),Ideal.absNorm J = m →
        IsCoprime (Ideal.span {(n: 𝓞 L)}) J:=fun J hJ => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(n: 𝓞 L)} ⊔ Ideal.span {(m: 𝓞 L)}:= by
              rw [sup_comm]
              exact h_cop_spans.symm
        _ ≤ Ideal.span {(n: 𝓞 L)} ⊔ J:=sup_le_sup_left (by
            rw [Ideal.span_le,Set.singleton_subset_iff]
            have: ((m: ℕ) : 𝓞 L) ∈ J:= by
              rw [← hJ]
              exact Ideal.absNorm_mem J
            exact_mod_cast this) _
    have h_inv_m: ∀ (J L' : Ideal (𝓞 L)),Ideal.absNorm J = m → Ideal.absNorm L' = n →
        J * L' ⊔ Ideal.span {(m: 𝓞 L)} = J:=fun J L' hJ hL => by
      have h_cop_mL_sup: Ideal.span {(m: 𝓞 L)} ⊔ L' = ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_m_L L' hL)
      refine le_antisymm (sup_le Ideal.mul_le_left ?_) ?_
      · rw [Ideal.span_le,Set.singleton_subset_iff]
        have: ((m: ℕ) : 𝓞 L) ∈ J:= by
          rw [← hJ]
          exact Ideal.absNorm_mem J
        exact_mod_cast this
      · calc
          J = J * ⊤:=(Ideal.mul_top J).symm
          _ = J * (Ideal.span {(m: 𝓞 L)} ⊔ L'):= by rw [h_cop_mL_sup]
          _ = J * Ideal.span {(m: 𝓞 L)} ⊔ J * L':=Ideal.mul_sup _ _ _
          _ ≤ Ideal.span {(m: 𝓞 L)} ⊔ J * L':=sup_le_sup_right Ideal.mul_le_right _
          _ = J * L' ⊔ Ideal.span {(m: 𝓞 L)}:=sup_comm _ _
    have h_inv_n: ∀ (J L' : Ideal (𝓞 L)),Ideal.absNorm J = m → Ideal.absNorm L' = n →
        J * L' ⊔ Ideal.span {(n: 𝓞 L)} = L':=fun J L' hJ hL => by
      have h_cop_nJ_sup: Ideal.span {(n: 𝓞 L)} ⊔ J = ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_n_J J hJ)
      refine le_antisymm (sup_le Ideal.mul_le_right ?_) ?_
      · rw [Ideal.span_le,Set.singleton_subset_iff]
        have: ((n: ℕ) : 𝓞 L) ∈ L':= by
          rw [← hL]
          exact Ideal.absNorm_mem L'
        exact_mod_cast this
      · calc
          L' = ⊤ * L':=(Ideal.top_mul L').symm
          _ = (Ideal.span {(n: 𝓞 L)} ⊔ J) * L':= by rw [h_cop_nJ_sup]
          _ = Ideal.span {(n: 𝓞 L)} * L' ⊔ J * L':=Ideal.sup_mul _ _ _
          _ ≤ Ideal.span {(n: 𝓞 L)} ⊔ J * L':=sup_le_sup_right Ideal.mul_le_left _
          _ = J * L' ⊔ Ideal.span {(n: 𝓞 L)}:=sup_comm _ _
    let fwd: {I: rp233 L // Ideal.absNorm I.1 = m * n} →
        {J: rp233 L // Ideal.absNorm J.1 = m} ×
          {L' : rp233 L // Ideal.absNorm L'.1 = n} :=
      fun ⟨⟨I,hI_ne⟩,hI_norm⟩ =>
        ⟨⟨⟨I ⊔ Ideal.span {(m: 𝓞 L)},fun h => hI_ne (by
            have: I ≤ I ⊔ Ideal.span {(m: 𝓞 L)}:=le_sup_left
            rw [h,le_bot_iff] at this
            exact this)⟩,
          (h_fwd_norms I hI_norm).1⟩,
         ⟨⟨I ⊔ Ideal.span {(n: 𝓞 L)},fun h => hI_ne (by
            have: I ≤ I ⊔ Ideal.span {(n: 𝓞 L)}:=le_sup_left
            rw [h,le_bot_iff] at this
            exact this)⟩,
          (h_fwd_norms I hI_norm).2⟩⟩
    let bwd: {J: rp233 L // Ideal.absNorm J.1 = m} ×
        {L' : rp233 L // Ideal.absNorm L'.1 = n} →
        {I: rp233 L // Ideal.absNorm I.1 = m * n} :=
      fun ⟨⟨⟨J,hJ_ne⟩,hJ_norm⟩,⟨⟨L',hL_ne⟩,hL_norm⟩⟩ =>
        ⟨⟨J * L',fun h => by
            rcases Ideal.mul_eq_bot.mp h with h1 | h1
            · exact hJ_ne h1
            · exact hL_ne h1⟩,
         by rw [map_mul,hJ_norm,hL_norm]⟩
    have h_equiv :
        {I: rp233 L // Ideal.absNorm I.1 = m * n} ≃
          {J: rp233 L // Ideal.absNorm J.1 = m} ×
            {L' : rp233 L // Ideal.absNorm L'.1 = n} :=
      { toFun:=fwd
        invFun:=bwd
        left_inv:=fun ⟨⟨I,hI_ne⟩,hI_norm⟩ => by
          simp only [fwd,bwd]
          refine Subtype.ext (Subtype.ext ?_)
          simp only
          rw [h_mul_sup,h_sup_absNorm I hI_norm]
        right_inv:=fun ⟨⟨⟨J,hJ_ne⟩,hJ_norm⟩,⟨⟨L',hL_ne⟩,hL_norm⟩⟩ => by
          simp only [fwd,bwd]
          refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
          · exact h_inv_m J L' hJ_norm hL_norm
          · exact h_inv_n J L' hJ_norm hL_norm }
    unfold rp234
    rw [Nat.card_congr h_equiv,Nat.card_prod]
  · interval_cases n
    simp [rp236]
  · interval_cases m
    simp [rp236]
  · interval_cases m
    interval_cases n
    simp [rp236]
lemma rp238 {s: ℂ} (hs: 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n: ℕ,(rp234 L n: ℂ) * (n: ℂ) ^ (-s):= by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n => ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [↓reduceIte]
    rw [rp235]
    push_cast
    rw [Complex.zero_cpow (by
      intro h
      have hs_ne: s ≠ 0:= by
        intro hs_zero
        rw [hs_zero,Complex.zero_re] at hs
        exact absurd hs (by norm_num)
      exact hs_ne (neg_eq_zero.mp h)),mul_zero]
  · simp only [hn.ne',↓reduceIte]
    have hn_ne: (n: ℂ) ≠ 0:= by exact_mod_cast hn.ne'
    rw [Complex.cpow_neg,div_eq_mul_inv]
    congr 1
    unfold rp234
    have hequiv: {I: Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I: rp233 L // Ideal.absNorm I.1 = n}:= by
      refine {
        toFun:=fun ⟨I,hI⟩ => ⟨⟨I,?_⟩,hI⟩
        invFun:=fun ⟨⟨I,_⟩,hI⟩ => ⟨I,hI⟩
        left_inv:=fun _ => rfl
        right_inv:=fun _ => rfl }
      intro h
      rw [h] at hI
      rw [Ideal.absNorm_bot] at hI
      omega
    exact (Nat.card_congr hequiv).symm ▸ rfl
lemma rp239 (α: Type*) [Fintype α] [Finite α] {z: ℂ}
    (hz: ‖z‖ < 1) :
    Summable (fun n: ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n) ∧
      (∑' n: ℕ,(Fintype.card (Sym α n) : ℂ) * z ^ n) =
        ((1 - z)⁻¹) ^ Fintype.card α:= by
  by_cases hα: Fintype.card α = 0
  · have: IsEmpty α:=Fintype.card_eq_zero_iff.mp hα
    let term: ℕ → ℂ:=fun n => (Fintype.card (Sym α n) : ℂ) * z ^ n
    have hzero: ∀ n ≠ 0,term n = 0:= by
      intro n hn
      cases n with
      | zero => contradiction
      | succ n => simp [term,Sym.card_sym_eq_multichoose,Nat.multichoose_zero_succ]
    have hsupport: {n: ℕ | term n ≠ 0}.Finite:= by
      refine Set.Finite.subset ({0} : Set ℕ).toFinite ?_
      intro n hn
      by_contra hne
      exact hn (hzero n hne)
    constructor
    · exact summable_of_hasFiniteSupport hsupport
    · have hcard0: Fintype.card (Sym α 0) = 1:= by
        rw [Sym.card_sym_eq_multichoose,Nat.multichoose_zero_right]
      simpa [term,hcard0,hα] using tsum_eq_single 0 hzero
  · obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero hα
    constructor
    · refine (summable_choose_mul_geometric_of_norm_lt_one k hz).congr ?_
      intro n
      rw [Sym.card_sym_eq_choose,hk,Nat.succ_add_sub_one,Nat.add_comm k n,
        Nat.choose_symm_add]
    · calc
        ∑' n: ℕ,(Fintype.card (Sym α n) : ℂ) * z ^ n
            = ∑' n: ℕ,((n + k).choose k: ℂ) * z ^ n:= by
                apply tsum_congr
                intro n
                rw [Sym.card_sym_eq_choose,hk,Nat.succ_add_sub_one,Nat.add_comm k n,
                  Nat.choose_symm_add]
        _ = 1 / (1 - z) ^ (k + 1):=tsum_choose_mul_geometric_of_norm_lt_one k hz
        _ = ((1 - z)⁻¹) ^ (k + 1):= by simp [one_div]
        _ = ((1 - z)⁻¹) ^ Fintype.card α:= by simp [hk]
lemma rp240 (α: Type*) [Fintype α] [Finite α] {z: ℂ} (hz: ‖z‖ < 1) :
    (∑' n: ℕ,(Fintype.card (Sym α n) : ℂ) * z ^ n) = ((1 - z)⁻¹) ^ Fintype.card α :=
  (rp239 α hz).2
lemma rp241 {s: ℂ} (hs: 1 < s.re) :
    Summable fun n: ℕ => ‖(rp234 L n: ℂ) * (n: ℂ) ^ (-s)‖:= by
  classical
  have h_finite: ∀ (b: ℕ),{I: rp233 L | Ideal.absNorm I.1 = b}.Finite:=fun b => by
    refine Set.Finite.preimage (f:=fun I: rp233 L => I.1) ?_
      (Ideal.finite_setOfPred_absNorm_eq b)
    intro _ _ _ _; exact Subtype.ext
  have h_sum_card: ∀ n: ℕ,∑ k ∈ Finset.Icc 1 n,rp234 L k =
      Nat.card {I: rp233 L // Ideal.absNorm I.1 ≤ n}:=fun n => by
    have key:=Finset.card_preimage_eq_sum_card_image_eq (f:=fun I: rp233 L =>
      Ideal.absNorm I.1) (s:=Finset.Icc 1 n) (fun b _ => h_finite b)
    rw [show ((fun I: rp233 L => Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I: rp233 L | Ideal.absNorm I.1 ≤ n} from by
      ext ⟨I,hI⟩
      simp only [Set.mem_preimage,Finset.coe_Icc,Set.mem_Icc,Set.mem_ofPred_eq]
      exact ⟨fun h => h.2,fun h =>
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI),h⟩⟩] at key
    exact key.symm
  have h_bigO: (fun n: ℕ => ∑ k ∈ Finset.Icc 1 n,(rp234 L k: ℝ))
      =O[Filter.atTop] (fun n: ℕ => (n: ℝ) ^ (1: ℝ)):= by
    have h_card_bridge: ∀ n: ℕ,
        Nat.card {I: rp233 L // Ideal.absNorm I.1 ≤ n} =
        Nat.card {I: (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1: ℕ) : ℝ) ≤ (n: ℝ)} :=
      fun n =>
      Nat.card_congr
        { toFun:=fun ⟨⟨I,hI⟩,hn⟩ =>
            ⟨⟨I,mem_nonZeroDivisors_of_ne_zero hI⟩,by exact_mod_cast hn⟩
          invFun:=fun ⟨⟨I,hI⟩,hn⟩ =>
            ⟨⟨I,mem_nonZeroDivisors_iff_ne_zero.mp hI⟩,by exact_mod_cast hn⟩
          left_inv:=fun _ => rfl
          right_inv:=fun _ => rfl }
    refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
        tendsto_natCast_atTop_atTop).congr' ?_)
    filter_upwards with n
    simp only [Function.comp_apply,Real.rpow_one]
    rw [show (∑ k ∈ Finset.Icc 1 n,(rp234 L k: ℝ)) =
        ((∑ k ∈ Finset.Icc 1 n,rp234 L k: ℕ) : ℝ) from by push_cast; rfl,
      h_sum_card n,h_card_bridge n]
    push_cast
    rfl
  have h_lss: LSeriesSummable (fun n: ℕ => ((rp234 L n: ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f:=fun n => (rp234 L n: ℝ))
      h_bigO (fun _ => Nat.cast_nonneg _) zero_le_one (by exact_mod_cast hs)
  have h_term_eq: LSeries.term (fun n: ℕ => ((rp234 L n: ℝ) : ℂ)) s =
      fun n => (rp234 L n: ℂ) * (n: ℂ) ^ (-s):= by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [rp235]
    · show ((rp234 L n: ℝ) : ℂ) / (n: ℂ) ^ s = _
      rw [Complex.cpow_neg,← div_eq_mul_inv]
      push_cast
      rfl
  exact (h_term_eq ▸ h_lss :
    Summable fun n => (rp234 L n: ℂ) * (n: ℂ) ^ (-s)).norm
lemma rp242 {s: ℂ} (hs: 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q: Nat.Primes,
        (∑' k: ℕ,(rp234 L ((q: ℕ) ^ k) : ℂ) *
          ((((q: ℕ) ^ k: ℕ) : ℂ) ^ (-s))):= by
  let f: ℕ → ℂ:=fun n => (rp234 L n: ℂ) * (n: ℂ) ^ (-s)
  have hf_zero: f 0 = 0:= by simp [f,rp235 L]
  have hf_one: f 1 = 1:= by simp [f,rp236 L]
  have hf_mul: ∀ {m n: ℕ},m.Coprime n → f (m * n) = f m * f n:=fun {m n} hcop => by
    simp only [f]
    rw [rp237 L hcop,Nat.cast_mul,Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hf_sum: Summable fun n => ‖f n‖:=rp241 L hs
  rw [rp238 L hs,
    ← EulerProduct.eulerProduct_tprod hf_one hf_mul hf_sum hf_zero]
end NumberFieldEulerProduct
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section ZetaFactorisation
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
lemma rp243 (k: ℕ) :
    rp234 K (p ^ k) = 1:= by
  classical
  have hne: (rp79 p) ≠ ⊥:= by
    rw [rp79,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have: (rp79 p).IsMaximal:=Int.ideal_span_isMaximal_of_prime p
  have hcoe:=IsDedekindDomain.coe_primesOverFinset (p:=rp79 p) hne (𝓞 K)
  have hcard: (rp80 K p).card = 1:= by
    have hncard: (Ideal.primesOver (rp79 p) (𝓞 K)).ncard = 1 :=
      rp112 (p:=p) (K:=K)
    rw [← hcoe,Set.ncard_coe_finset] at hncard
    simpa [rp80] using hncard
  obtain ⟨P,hP⟩:=Finset.card_eq_one.mp hcard
  have hPmem: P ∈ Ideal.primesOver (rp79 p) (𝓞 K):= by
    have hPfin: P ∈ rp80 K p:= by
      rw [hP]
      exact Finset.mem_singleton_self P
    exact (rp104 (K:=K) (ℓ:=p)).1 hPfin
  have hP_ne: P ≠ ⊥:= by
    intro hP_bot
    have hunder:=hPmem.2
    rw [Ideal.liesOver_iff,Ideal.under_def,hP_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 K))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))] at hunder
    exact hne hunder
  have: P.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hP_ne hPmem.1
  have: P.LiesOver (Ideal.span {(p: ℤ)}):= by
    simpa [rp79] using hPmem.2
  have habsNormP: Ideal.absNorm P = p:= by
    calc
      Ideal.absNorm P = p ^ (1: ℕ):= by
        rw [← rp113 (p:=p) (K:=K) P hPmem,
          ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p: ℤ)}) P]
        exact Ideal.absNorm_eq_pow_inertiaDeg' P hp.out
      _ = p:= by simp
  have: Unique {I: rp233 K // Ideal.absNorm I.1 = p ^ k} :=
    { default:=⟨⟨P ^ k,pow_ne_zero k hP_ne⟩,by
          rw [map_pow,habsNormP]⟩
      uniq:= by
        rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
        let m: ℕ:=Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q,hPQ,hIeq⟩:=Ideal.eq_prime_pow_mul_coprime hI_ne P
        have hQ_top: Q = ⊤:= by
          by_contra hQ_ne_top
          have hQ_ne: Q ≠ ⊥:= by
            intro hQ_bot
            apply hI_ne
            rw [hIeq,hQ_bot,Ideal.mul_bot]
          have hnf_ne: UniqueFactorizationMonoid.normalizedFactors Q ≠ 0:= by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne,hnf]
            simp
          obtain ⟨R,hRmem⟩:=Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac:=(Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime: R.IsPrime:=hRfac.1
          have hQ_le_R: Q ≤ R:=hRfac.2
          have hR_ne: R ≠ ⊥:=fun hR_bot =>
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          have: NeZero R:=⟨hR_ne⟩
          have hI_le_Q: I ≤ Q:= by
            rw [hIeq]
            exact Ideal.mul_le_right
          have hR_dvd_I: Ideal.absNorm R ∣ p ^ k:= by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd: Ideal.absNorm (Ideal.under ℤ R) ∣ p ^ k :=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime: (Ideal.absNorm (Ideal.under ℤ R)).Prime:=Nat.absNorm_under_prime R
          have hunder_dvd_p: Ideal.absNorm (Ideal.under ℤ R) ∣ p :=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p: Ideal.absNorm (Ideal.under ℤ R) = p :=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p: Ideal.under ℤ R = Ideal.span {(p: ℤ)}:= by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies: R.LiesOver (Ideal.span {(p: ℤ)}):= by
            rw [Ideal.liesOver_iff,hunder_eq_span_p]
          have hRmem_p: R ∈ Ideal.primesOver (rp79 p) (𝓞 K):= by
            refine ⟨hRprime,?_⟩
            simpa [rp79] using hR_lies
          have hRmem_fin: R ∈ rp80 K p :=
            (rp104 (K:=K) (ℓ:=p)).2 hRmem_p
          have hR_eq_P: R = P:= by
            rw [hP] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_P: Q ≤ P:= by
            simpa [hR_eq_P] using hQ_le_R
          have htop_le_P: (⊤ : Ideal (𝓞 K)) ≤ P:= by
            calc
              ⊤ = P ⊔ Q:=hPQ.symm
              _ ≤ P:=sup_le le_rfl hQ_le_P
          exact hPmem.1.ne_top (top_le_iff.mp htop_le_P)
        have hI_pow: I = P ^ m:= by
          simpa [m,hQ_top] using hIeq
        have hm: m = k:= by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p ^ m = Ideal.absNorm I:= by
              rw [hI_pow,map_pow,habsNormP]
            _ = p ^ k:=hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m,hm] using hI_pow }
  exact Nat.card_unique
lemma rp244
    {q: Nat.Primes} {I: Ideal (𝓞 K)} (hI_ne: I ≠ ⊥)
    {k: ℕ} (hI_norm: Ideal.absNorm I = (q: ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆ rp80 K (q: ℕ):= by
  classical
  have: Fact (q: ℕ).Prime:=⟨q.2⟩
  intro P hP
  have hP_mem: P ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hP
  have hP_fac:=(Ideal.mem_normalizedFactors_iff hI_ne).1 hP_mem
  have hP_prime: P.IsPrime:=hP_fac.1
  have hI_le_P: I ≤ P:=hP_fac.2
  have hP_ne: P ≠ ⊥:=fun hP_bot =>
    hI_ne (le_bot_iff.mp (hP_bot ▸ hI_le_P))
  have: NeZero P:=⟨hP_ne⟩
  have hP_dvd: Ideal.absNorm P ∣ (q: ℕ) ^ k:= by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_P
  have hunder_dvd: Ideal.absNorm (Ideal.under ℤ P) ∣ (q: ℕ) ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm P) hP_dvd
  have hunder_prime: (Ideal.absNorm (Ideal.under ℤ P)).Prime:=Nat.absNorm_under_prime P
  have hunder_dvd_q: Ideal.absNorm (Ideal.under ℤ P) ∣ (q: ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q: Ideal.absNorm (Ideal.under ℤ P) = (q: ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q: Ideal.under ℤ P = Ideal.span {((q: ℕ) : ℤ)}:= by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P)]
    simp [hunder_eq_q]
  have hP_lies: P.LiesOver (Ideal.span {((q: ℕ) : ℤ)}):= by
    rw [Ideal.liesOver_iff,hunder_eq_span_q]
  have hP_over: P ∈ Ideal.primesOver (rp79 (q: ℕ)) (𝓞 K):= by
    refine ⟨hP_prime,?_⟩
    simpa [rp79] using hP_lies
  exact (rp104 (K:=K) (ℓ:=(q: ℕ))).2 hP_over
lemma rp245
    {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p) {P: Ideal (𝓞 K)}
    (hP: P ∈ rp80 K (q: ℕ)) :
    Ideal.absNorm P = (q: ℕ) ^ rp94 (p:=p) (q: ℕ) hq:= by
  classical
  have hP_over: P ∈ Ideal.primesOver (rp79 (q: ℕ)) (𝓞 K) :=
    (rp104 (K:=K) (ℓ:=(q: ℕ))).1 hP
  have: P.IsPrime:=hP_over.1
  have: P.LiesOver (Ideal.span {((q: ℕ) : ℤ)}):= by
    simpa [rp79] using hP_over.2
  have: P.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {((q: ℕ) : ℤ)})
  rw [← rp114 p K hq P hP_over,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {((q: ℕ) : ℤ)}) P]
  exact Ideal.absNorm_eq_pow_inertiaDeg' P q.2
lemma rp246
    {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p)
    {I: Ideal (𝓞 K)} (hI_ne: I ≠ ⊥)
    {k: ℕ} (hI_norm: Ideal.absNorm I = (q: ℕ) ^ k) :
    rp94 (p:=p) (q: ℕ) hq *
        (UniqueFactorizationMonoid.normalizedFactors I).card = k:= by
  classical
  set d:=rp94 (p:=p) (q: ℕ) hq with hd
  set m:=UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset: m.toFinset ⊆ rp80 K (q: ℕ):= by
    simpa [hm] using
      rp244 (K:=K) hI_ne
        hI_norm
  have hsum_count: ∑ P ∈ rp80 K (q: ℕ),m.count P = m.card :=
    Multiset.sum_count_eq_card fun P hP => hsubset (Multiset.mem_toFinset.2 hP)
  have hnorm_factors: Ideal.absNorm m.prod = (q: ℕ) ^ (d * m.card):= by
    rw [Finset.prod_multiset_count_of_subset m (rp80 K (q: ℕ)) hsubset,
      map_prod]
    calc
      ∏ P ∈ rp80 K (q: ℕ),Ideal.absNorm (P ^ m.count P)
          = ∏ P ∈ rp80 K (q: ℕ),((q: ℕ) ^ d) ^ m.count P:= by
              apply Finset.prod_congr rfl
              intro P hP
              rw [map_pow]
              rw [rp245
                (p:=p) (K:=K) hq hP,hd]
      _ = (q: ℕ) ^ (d * ∑ P ∈ rp80 K (q: ℕ),m.count P):= by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _ = (q: ℕ) ^ (d * m.card):= by rw [hsum_count]
  have hpow: (q: ℕ) ^ (d * m.card) = (q: ℕ) ^ k:= by
    calc
      (q: ℕ) ^ (d * m.card) = Ideal.absNorm m.prod:=hnorm_factors.symm
      _ = Ideal.absNorm I:= by rw [hm,Ideal.prod_normalizedFactors_eq_self hI_ne]
      _ = (q: ℕ) ^ k:=hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow
lemma rp247
    {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p) {k: ℕ}
    (hk: ¬ rp94 (p:=p) (q: ℕ) hq ∣ k) :
    rp234 K ((q: ℕ) ^ k) = 0:= by
  unfold rp234
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card,?_⟩
  simpa [mul_comm] using
    rp246
      (p:=p) (K:=K) hq hI_ne hI_norm |>.symm
lemma rp248
    {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p) (n: ℕ) :
    rp234 K
        ((q: ℕ) ^ (rp94 (p:=p) (q: ℕ) hq * n)) =
      Fintype.card (Sym {P: Ideal (𝓞 K) // P ∈ rp80 K (q: ℕ)} n):= by
  classical
  set d:=rp94 (p:=p) (q: ℕ) hq with hd
  let α: Type _:={P: Ideal (𝓞 K) // P ∈ rp80 K (q: ℕ)}
  let β: Type _:={I: rp233 K // Ideal.absNorm I.1 = (q: ℕ) ^ (d * n)}
  have hd_pos: 0 < d:= by
    rw [hd]
    exact orderOf_pos _
  have hpmap_val :
      ∀ {m: Multiset (Ideal (𝓞 K))}
        (H: ∀ P,P ∈ m → P ∈ rp80 K (q: ℕ)),
        (Multiset.pmap (fun P hP => (⟨P,hP⟩ : α)) m H).map Subtype.val = m:= by
    intro m H
    rw [Multiset.map_pmap,Multiset.pmap_eq_map,Multiset.map_id']
  let toSym: β → Sym α n:=fun ⟨⟨I,hI_ne⟩,hI_norm⟩ =>
    let m:=UniqueFactorizationMonoid.normalizedFactors I
    let H: ∀ P,P ∈ m → P ∈ rp80 K (q: ℕ):= by
      intro P hP
      have hsubset: m.toFinset ⊆ rp80 K (q: ℕ):= by
        simpa [m] using
          rp244 (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hP)
    have hm_card: m.card = n:= by
      have hmul: d * m.card = d * n:= by
        simpa [m,hd] using
          rp246
            (p:=p) (K:=K) hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun P hP => (⟨P,hP⟩ : α)) m H,by
      simp [hm_card]⟩
  let ofSym: Sym α n → β:=fun s =>
    let m: Multiset (Ideal (𝓞 K)):=s.1.map Subtype.val
    have hm_card: m.card = n:= by
      simp [m]
    have hm_subset: m.toFinset ⊆ rp80 K (q: ℕ):= by
      intro P hP
      rcases Multiset.mem_toFinset.1 hP with hP
      rcases Multiset.mem_map.1 hP with ⟨Q,hQ,rfl⟩
      exact Q.2
    have hm_prime: ∀ P ∈ m,Prime P:= by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q,hQ,rfl⟩
      have hQ_ne: (Q: Ideal (𝓞 K)) ≠ ⊥:= by
        intro hQ_bot
        have hQ_norm :=
          rp245
            (p:=p) (K:=K) hq Q.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQ_bot,← hd] at hQ_norm
        exact pow_ne_zero d q.2.ne_zero hQ_norm.symm
      exact (Ideal.prime_iff_isPrime hQ_ne).2
        ((rp104 (K:=K) (ℓ:=(q: ℕ))).1 Q.2).1
    have hm_prod_ne: m.prod ≠ ⊥:=Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm: Ideal.absNorm m.prod = (q: ℕ) ^ (d * n):= by
      have hsum_count: ∑ P ∈ rp80 K (q: ℕ),m.count P = m.card :=
        Multiset.sum_count_eq_card fun P hP => hm_subset (Multiset.mem_toFinset.2 hP)
      rw [Finset.prod_multiset_count_of_subset m (rp80 K (q: ℕ)) hm_subset,
        map_prod]
      calc
        ∏ P ∈ rp80 K (q: ℕ),Ideal.absNorm (P ^ m.count P)
            = ∏ P ∈ rp80 K (q: ℕ),((q: ℕ) ^ d) ^ m.count P:= by
                apply Finset.prod_congr rfl
                intro P hP
                rw [map_pow]
                rw [rp245
                  (p:=p) (K:=K) hq hP,hd]
        _ = (q: ℕ) ^ (d * ∑ P ∈ rp80 K (q: ℕ),m.count P):= by
                rw [Finset.prod_pow_eq_pow_sum]
                simp [Nat.pow_mul]
        _ = (q: ℕ) ^ (d * m.card):= by rw [hsum_count]
        _ = (q: ℕ) ^ (d * n):= by rw [hm_card]
    ⟨⟨m.prod,hm_prod_ne⟩,hm_norm⟩
  have htoSym_map_val: ∀ b: β,
      (toSym b).1.map Subtype.val = UniqueFactorizationMonoid.normalizedFactors b.1.1:= by
    rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
    dsimp [toSym]
    let m:=UniqueFactorizationMonoid.normalizedFactors I
    let H: ∀ P,P ∈ m → P ∈ rp80 K (q: ℕ):= by
      intro P hP
      have hsubset: m.toFinset ⊆ rp80 K (q: ℕ):= by
        simpa [m] using
          rp244 (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hP)
    change (Multiset.pmap (fun P hP => (⟨P,hP⟩ : α)) m H).map Subtype.val = m
    rw [hpmap_val H]
  have hofSym_nfactors :
      ∀ s: Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val:= by
    intro s
    dsimp [ofSym]
    let m: Multiset (Ideal (𝓞 K)):=s.1.map Subtype.val
    have hm_prime: ∀ P ∈ m,Prime P:= by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q,hQ,rfl⟩
      have hQ_ne: (Q: Ideal (𝓞 K)) ≠ ⊥:= by
        intro hQ_bot
        have hQ_norm :=
          rp245
            (p:=p) (K:=K) hq Q.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQ_bot,← hd] at hQ_norm
        exact pow_ne_zero d q.2.ne_zero hQ_norm.symm
      exact (Ideal.prime_iff_isPrime hQ_ne).2
        ((rp104 (K:=K) (ℓ:=(q: ℕ))).1 Q.2).1
    change UniqueFactorizationMonoid.normalizedFactors m.prod = m
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft: Function.LeftInverse ofSym toSym:= by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod = b.1.1
    rw [htoSym_map_val,Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright: Function.RightInverse ofSym toSym:= by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  unfold rp234
  simpa [β,α,hd,Nat.card_eq_fintype_card] using
    Nat.card_congr (⟨toSym,ofSym,hleft,hright⟩ : β ≃ Sym α n)
lemma rp249 {s: ℂ} (hs: 1 < s.re) :
    (∑' k: ℕ,(rp234 K (p ^ k) : ℂ) *
      (((p ^ k: ℕ) : ℂ) ^ (-s))) =
      (rp87 K p s)⁻¹:= by
  have hnorm: ‖(p: ℂ) ^ (-s)‖ < 1:= by
    have hle: ‖(p: ℂ) ^ (-s)‖ ≤ 1 / 2 :=
      Complex.norm_prime_cpow_le_one_half ⟨p,hp.out⟩ hs
    exact hle.trans_lt (by norm_num)
  rw [rp118]
  trans ∑' k: ℕ,((p: ℂ) ^ (-s)) ^ k
  · refine tsum_congr fun k => ?_
    rw [rp243 (p:=p) (K:=K) k]
    simp only [Nat.cast_one,one_mul]
    rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul p k (-s),mul_comm,
      Complex.cpow_mul_nat]
  · simpa using tsum_geometric_of_norm_lt_one hnorm
lemma rp250
    (p: ℕ) [Fact p.Prime] (K: Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {q: Nat.Primes} {s: ℂ} (hs: 1 < s.re) :
    (∑' k: ℕ,(rp234 K ((q: ℕ) ^ k) : ℂ) *
      (((q: ℕ) ^ k: ℕ) : ℂ) ^ (-s)) =
      (rp87 K (q: ℕ) s)⁻¹:= by
  have: Fact (q: ℕ).Prime:=⟨q.2⟩
  by_cases hq: (q: ℕ) = p
  · have hq' : q = ⟨p,Fact.out⟩:= by
      apply Subtype.ext
      simpa using hq
    subst hq'
    simpa using rp249 (p:=p) (K:=K) hs
  · classical
    set d:=rp94 (p:=p) (q: ℕ) hq with hd
    let α: Type _:={P: Ideal (𝓞 K) // P ∈ rp80 K (q: ℕ)}
    let f: ℕ → ℂ:=fun k =>
      (rp234 K ((q: ℕ) ^ k) : ℂ) * ((((q: ℕ) ^ k: ℕ) : ℂ) ^ (-s))
    let g: ℕ → ℂ:=fun n =>
      (rp234 K ((q: ℕ) ^ (d * n)) : ℂ) *
        ((((q: ℕ) ^ (d * n) : ℕ) : ℂ) ^ (-s))
    let z: ℂ:=(q: ℂ) ^ (-((d: ℂ) * s))
    have hd_pos: 0 < d:= by
      rw [hd]
      exact orderOf_pos _
    have hs_d: 1 < (((d: ℂ) * s).re):= by
      rw [Complex.mul_re]
      simp
      have hd_ge: (1: ℝ) ≤ d:= by
        exact_mod_cast Nat.succ_le_of_lt hd_pos
      nlinarith [hs,hd_ge]
    have hz: ‖z‖ < 1:= by
      have hle: ‖z‖ ≤ 1 / 2:= by
        dsimp [z]
        exact Complex.norm_prime_cpow_le_one_half ⟨q,q.2⟩ hs_d
      exact hle.trans_lt (by norm_num)
    have hg_term: ∀ n: ℕ,g n = (Fintype.card (Sym α n) : ℂ) * z ^ n:= by
      intro n
      dsimp [g,z]
      rw [show rp234 K ((q: ℕ) ^ (d * n)) = Fintype.card (Sym α n) by
        simpa [α,hd] using
          rp248
            (p:=p) (K:=K) hq n]
      rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul (q: ℕ) (d * n) (-s)]
      have hexp: (((d * n: ℕ) : ℂ) * (-s)) = (-((d: ℂ) * s)) * n:= by
        push_cast
        ring
      rw [hexp,Complex.cpow_mul_nat]
    have hg_eq: g = fun n: ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n:=funext hg_term
    have hg_hasSum0: HasSum (fun n: ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n)
        (((1 - z)⁻¹) ^ Fintype.card α):= by
      rw [← rp240 α hz]
      exact (rp239 α hz).1.hasSum
    have hg_hasSum: HasSum g (((1 - z)⁻¹) ^ Fintype.card α):= by
      simpa [hg_eq] using hg_hasSum0
    have hf_hasSum: HasSum f (((1 - z)⁻¹) ^ Fintype.card α):= by
      refine (hasSum_iff_hasSum_of_ne_zero_bij
        (f:=f) (g:=g) (i:=fun x: Function.support g => d * x.1) ?_ ?_ ?_).2 hg_hasSum
      · intro x y hxy
        exact Subtype.ext <| Nat.eq_of_mul_eq_mul_left hd_pos hxy
      · intro k hk
        have hk_mult: rp234 K ((q: ℕ) ^ k) ≠ 0:=fun hk_zero =>
          hk (by simp [f,hk_zero])
        have hk_dvd: d ∣ k:= by
          by_contra hk_ndvd
          exact hk_mult <|
            rp247 (p:=p) (K:=K) hq hk_ndvd
        obtain ⟨n,rfl⟩:=hk_dvd
        refine ⟨⟨n,?_⟩,rfl⟩
        simpa [f,g,mul_comm] using hk
      · intro x
        simp [f,g,mul_comm]
    have hcard_finset :
        (rp80 K (q: ℕ)).card = rp95 (p:=p) (q: ℕ) hq:= by
      have: (rp79 (q: ℕ)).IsMaximal :=
        Int.ideal_span_isMaximal_of_prime (q: ℕ)
      have hne: (rp79 (q: ℕ)) ≠ ⊥:= by
        simp [rp79,q.2.ne_zero]
      have hcoe :=
        IsDedekindDomain.coe_primesOverFinset (p:=rp79 (q: ℕ)) hne (𝓞 K)
      have h1:=rp116 (p:=p) (K:=K) hq
      rw [← hcoe,Set.ncard_coe_finset] at h1
      exact h1
    have hα_card: Fintype.card α = rp95 (p:=p) (q: ℕ) hq:= by
      calc
        Fintype.card α = (rp80 K (q: ℕ)).card :=
          Fintype.card_of_finset' (rp80 K (q: ℕ)) fun P => by simp
        _ = rp95 (p:=p) (q: ℕ) hq:=hcard_finset
    have hf_hasSum' : HasSum f ((rp87 K (q: ℕ) s)⁻¹):= by
      rw [rp117 (p:=p) (K:=K) hq,← inv_pow]
      simpa [z,hd,hα_card] using hf_hasSum
    simpa [f] using hf_hasSum'.tsum_eq
lemma rp251 (χ: DirichletCharacter ℂ p) {s: ℂ}
    (hs: 1 < s.re) :
    DirichletCharacter.LFunction χ s =
      ∏' q: Nat.Primes,(1 - χ ((q: ℕ) : ZMod p) * ((q: ℕ) : ℂ) ^ (-s))⁻¹:= by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod χ hs]
omit hp in
lemma rp252 (f: DirichletCharacter ℂ p → Nat.Primes → ℂ)
    (hmul: ∀ χ: DirichletCharacter ℂ p,Multipliable (f χ)) :
    (∏ χ: DirichletCharacter ℂ p,∏' q: Nat.Primes,f χ q) =
      ∏' q: Nat.Primes,∏ χ: DirichletCharacter ℂ p,f χ q :=
  (Multipliable.tprod_finsetProd (fun χ _ => hmul χ)).symm
lemma rp253 {s: ℂ} (hs: 1 < s.re) :
    LProduct (p:=p) s =
      ∏' q: Nat.Primes,∏ χ: DirichletCharacter ℂ p,
        (1 - χ ((q: ℕ) : ZMod p) * ((q: ℕ) : ℂ) ^ (-s))⁻¹:= by
  unfold LProduct
  rw [Finset.prod_congr rfl (fun χ _ => rp251 p χ hs)]
  exact rp252 (p:=p)
    (fun χ q => (1 - χ ((q: ℕ) : ZMod p) * ((q: ℕ) : ℂ) ^ (-s))⁻¹)
    (fun χ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)
lemma rp254 {q: Nat.Primes} (hq: (q: ℕ) ≠ p) {s: ℂ} :
    rp87 K (q: ℕ) s = rp85 (p:=p) (q: ℕ) s:= by
  have: Fact (q: ℕ).Prime:=⟨q.2⟩
  rw [rp117 (p:=p) (K:=K) hq,
    rp102 (p:=p) hq]
lemma rp255 {s: ℂ} (hs: 1 < s.re) :
    LProduct (p:=p) s =
      ∏' q: Nat.Primes,(rp85 (p:=p) (q: ℕ) s)⁻¹:= by
  rw [rp253 p hs]
  refine tprod_congr fun q => ?_
  unfold rp85
  rw [Finset.prod_inv_distrib]
lemma rp256
  (p: ℕ) [Fact p.Prime] (K: Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {s: ℂ} (hs: 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∏' q: Nat.Primes,(rp87 K (q: ℕ) s)⁻¹:= by
  rw [rp242 K hs]
  exact tprod_congr fun _ => rp250 (p:=p) (K:=K) hs
theorem rp257 {s: ℂ} (hs: 1 < s.re) :
    LProduct (p:=p) s = (1 - (p: ℂ) ^ (-s)) * NumberField.dedekindZeta K s:= by
  classical
  have hp_prime: Nat.Prime p:=hp.out
  set p₀: Nat.Primes:=⟨p,hp_prime⟩
  have h_mul_cf :
      Multipliable (fun q: Nat.Primes => (rp85 (p:=p) (q: ℕ) s)⁻¹):= by
    have h1: (fun q: Nat.Primes => (rp85 (p:=p) (q: ℕ) s)⁻¹) =
        (fun q: Nat.Primes => ∏ χ: DirichletCharacter ℂ p,
          (1 - χ ((q: ℕ) : ZMod p) * ((q: ℕ) : ℂ) ^ (-s))⁻¹):= by
      funext q
      unfold rp85
      rw [Finset.prod_inv_distrib]
    rw [h1]
    exact multipliable_prod (s:=Finset.univ) fun χ _ =>
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  let h: Nat.Primes → ℂ:=Pi.mulSingle p₀ ((1 - (p: ℂ) ^ (-s))⁻¹)
  have h_mul_h: Multipliable h:=multipliable_of_hasFiniteMulSupport <|
    Set.Finite.subset (Set.finite_singleton p₀) Pi.mulSupport_mulSingle_subset
  have h_pointwise: ∀ q: Nat.Primes,
      (rp85 (p:=p) (q: ℕ) s)⁻¹ * h q =
        (rp87 K (q: ℕ) s)⁻¹:=fun q => by
    by_cases hq: q = p₀
    · subst hq
      simp only [h,Pi.mulSingle_eq_same]
      rw [rp103,inv_one,one_mul,rp118]
    · simp only [h,Pi.mulSingle_eq_of_ne hq,mul_one]
      have hq' : (q: ℕ) ≠ p:=fun heq => hq (Subtype.ext heq)
      exact (rp254 (p:=p) (K:=K) hq').symm ▸ rfl
  rw [rp255 p hs,rp256 (p:=p) (K:=K) hs]
  have h_combine: ∏' q: Nat.Primes,(rp87 K (q: ℕ) s)⁻¹ =
      (∏' q: Nat.Primes,(rp85 (p:=p) (q: ℕ) s)⁻¹) *
        (1 - (p: ℂ) ^ (-s))⁻¹:= by
    rw [← tprod_pi_single p₀ ((1 - (p: ℂ) ^ (-s))⁻¹),
      ← Multipliable.tprod_mul h_mul_cf h_mul_h]
    exact tprod_congr fun q => (h_pointwise q).symm
  rw [h_combine]
  have h_ne: (1 - (p: ℂ) ^ (-s)) ≠ 0:= by
    rw [sub_ne_zero]
    intro heq
    have hpp: (0: ℝ) < (p: ℝ):= by exact_mod_cast hp_prime.pos
    have hpnorm: ‖(p: ℂ) ^ (-s)‖ < 1:= by
      rw [show ((p: ℂ) ^ (-s)) = ((p: ℝ) : ℂ) ^ (-s) from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpp]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp_prime.one_lt)
        (by simp only [Complex.neg_re]; linarith)
    rw [← heq,norm_one] at hpnorm
    exact lt_irrefl 1 hpnorm
  field_simp
lemma rp258 {s: ℂ} :
    LProduct (p:=p) s =
      DirichletCharacter.LFunctionTrivChar p s * rp88 p s:= by
  classical
  unfold LProduct rp88
  rw [show rp81 (p:=p) = Finset.univ.erase 1 from rfl,
    ← Finset.mul_prod_erase Finset.univ (fun χ => DirichletCharacter.LFunction χ s)
      (Finset.mem_univ 1)]
lemma rp259 {s: ℂ} :
    rp88 p s = rp89 p s * rp90 p s:= by
  classical
  unfold rp88 rp89 rp90
    rp81 rp82 rp83
  have hdisj: Disjoint
      (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1)
      (Finset.univ.filter fun χ: DirichletCharacter ℂ p => χ.Odd):= by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχe hχo
    rw [Finset.mem_filter] at hχe hχo
    exact DirichletCharacter.Odd.not_even χ hχo.2 hχe.2.1
  have hunion: Finset.univ.erase (1: DirichletCharacter ℂ p) =
      Finset.univ.filter (fun χ: DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1) ∪
        Finset.univ.filter (fun χ: DirichletCharacter ℂ p => χ.Odd):= by
    ext χ
    simp only [Finset.mem_erase,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
      and_true,true_and]
    refine ⟨fun hne => ?_,?_⟩
    · rcases DirichletCharacter.even_or_odd χ with he | ho
      · exact Or.inl ⟨he,hne⟩
      · exact Or.inr ho
    · rintro (⟨_,hne⟩ | ho)
      · exact hne
      · rintro rfl
        exact DirichletCharacter.Odd.not_even _ ho (by
          change (1: DirichletCharacter ℂ p) (-1) = 1
          rw [MulChar.one_apply (isUnit_one.neg)])
  rw [hunion,Finset.prod_union hdisj]
theorem rp260 {s: ℂ}
    (hs: 1 < s.re) :
    NumberField.dedekindZeta K s = riemannZeta s * rp88 p s:= by
  have hs_ne: s ≠ 1:=fun h => by
    rw [h] at hs
    simp at hs
  have h1: LProduct (p:=p) s = (1 - (p: ℂ) ^ (-s)) * NumberField.dedekindZeta K s :=
    rp257 p K hs
  have h2: LProduct (p:=p) s =
      (1 - (p: ℂ) ^ (-s)) * (riemannZeta s * rp88 p s):= by
    rw [rp258 p,rp78 p hs_ne,
      mul_assoc]
  have hne: (1 - (p: ℂ) ^ (-s)) ≠ 0:= by
    rw [sub_ne_zero]
    intro heq
    have hpp: (0: ℝ) < (p: ℝ):= by exact_mod_cast hp.out.pos
    have hpnorm: ‖(p: ℂ) ^ (-s)‖ < 1:= by
      rw [show ((p: ℂ) ^ (-s)) = ((p: ℝ) : ℂ) ^ (-s) from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpp]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.out.one_lt)
        (by simp; linarith)
    rw [← heq,norm_one] at hpnorm
    exact lt_irrefl 1 hpnorm
  exact mul_left_cancel₀ hne (h1.symm.trans h2)
end ZetaFactorisation
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped BigOperators Topology nonZeroDivisors
namespace KummerCriterion
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
abbrev rp261 (L: Type*) [Field L] [NumberField L] : Type _:=rp233 L
abbrev rp262 (L: Type*) [Field L] [NumberField L] (n: ℕ) : ℕ :=
  rp234 L n
lemma rp263
    (L: Type*) [Field L] [NumberField L] {s: ℂ} (hs: 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q: Nat.Primes,
        (∑' k: ℕ,(rp262 L ((q: ℕ) ^ k) : ℂ) *
          ((((q: ℕ) ^ k: ℕ) : ℂ) ^ (-s))):= by
  simpa [rp262] using
    (rp242 (L:=L) hs)
lemma rp264 (hp_odd: p ≠ 2) (k: ℕ) :
    rp262 (NumberField.maximalRealSubfield K) (p ^ k) = 1:= by
  classical
  have: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
  have hcard: (rp200 (K:=K) p).card = 1:= by
    rw [rp201 (K:=K) (ℓ:=p)]
    exact rp229 (p:=p) (K:=K)
  obtain ⟨PPlus,hPPlus⟩:=Finset.card_eq_one.mp hcard
  have hPPlusmem: PPlus ∈ Ideal.primesOver (rp79 p) (𝓞 (NumberField.maximalRealSubfield K)):= by
    have hPPlus_fin: PPlus ∈ rp200 (K:=K) p:= by
      rw [hPPlus]
      exact Finset.mem_singleton_self PPlus
    exact (rp202 (K:=K) (ℓ:=p)).1 hPPlus_fin
  have hPPlus_ne: PPlus ≠ ⊥:= by
    intro hPPlus_bot
    have hunder:=hPPlusmem.2
    rw [Ideal.liesOver_iff,Ideal.under_def,hPPlus_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 (NumberField.maximalRealSubfield K)))
        (FaithfulSMul.algebraMap_injective ℤ (𝓞 (NumberField.maximalRealSubfield K)))] at hunder
    have hne: (rp79 p) ≠ ⊥:= by
      rw [rp79,Ne,Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    exact hne hunder
  have: PPlus.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hPPlus_ne hPPlusmem.1
  have: PPlus.LiesOver (Ideal.span {(p: ℤ)}):= by
    simpa [rp79] using hPPlusmem.2
  have habsNormPPlus: Ideal.absNorm PPlus = p:= by
    calc
      Ideal.absNorm PPlus = p ^ (1: ℕ):= by
        rw [← rp231 (p:=p) (K:=K) PPlus hPPlusmem]
        rw [← Ideal.inertiaDeg'_eq_inertiaDeg (p:=Ideal.span {(p: ℤ)}) (q:=PPlus)]
        exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
      _ = p:= by simp
  have: Unique {I: rp261 (NumberField.maximalRealSubfield K) // Ideal.absNorm I.1 = p ^ k} :=
    { default:=⟨⟨PPlus ^ k,pow_ne_zero k hPPlus_ne⟩,by
          rw [map_pow,habsNormPPlus]⟩
      uniq:= by
        rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
        let m: ℕ:=Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q,hPQ,hIeq⟩:=Ideal.eq_prime_pow_mul_coprime hI_ne PPlus
        have hQ_top: Q = ⊤:= by
          by_contra hQ_ne_top
          have hQ_ne: Q ≠ ⊥:= by
            intro hQ_bot
            apply hI_ne
            rw [hIeq,hQ_bot,Ideal.mul_bot]
          have hnf_ne: UniqueFactorizationMonoid.normalizedFactors Q ≠ 0:= by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne,hnf]
            simp
          obtain ⟨R,hRmem⟩:=Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac:=(Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime: R.IsPrime:=hRfac.1
          have hQ_le_R: Q ≤ R:=hRfac.2
          have hR_ne: R ≠ ⊥:=fun hR_bot =>
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          have: NeZero R:=⟨hR_ne⟩
          have hI_le_Q: I ≤ Q:= by
            rw [hIeq]
            exact Ideal.mul_le_right
          have hR_dvd_I: Ideal.absNorm R ∣ p ^ k:= by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd: Ideal.absNorm (Ideal.under ℤ R) ∣ p ^ k :=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime: (Ideal.absNorm (Ideal.under ℤ R)).Prime:=Nat.absNorm_under_prime R
          have hunder_dvd_p: Ideal.absNorm (Ideal.under ℤ R) ∣ p :=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p: Ideal.absNorm (Ideal.under ℤ R) = p :=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p: Ideal.under ℤ R = Ideal.span {(p: ℤ)}:= by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies: R.LiesOver (Ideal.span {(p: ℤ)}):= by
            rw [Ideal.liesOver_iff,hunder_eq_span_p]
          have hRmem_p: R ∈ Ideal.primesOver (rp79 p) (𝓞 (NumberField.maximalRealSubfield K)):= by
            refine ⟨hRprime,?_⟩
            simpa [rp79] using hR_lies
          have hRmem_fin: R ∈ rp200 (K:=K) p :=
            (rp202 (K:=K) (ℓ:=p)).2 hRmem_p
          have hR_eq_PPlus: R = PPlus:= by
            rw [hPPlus] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_PPlus: Q ≤ PPlus:= by
            simpa [hR_eq_PPlus] using hQ_le_R
          have htop_le_PPlus: (⊤ : Ideal (𝓞 (NumberField.maximalRealSubfield K))) ≤ PPlus:= by
            calc
              ⊤ = PPlus ⊔ Q:=hPQ.symm
              _ ≤ PPlus:=sup_le le_rfl hQ_le_PPlus
          exact hPPlusmem.1.ne_top (top_le_iff.mp htop_le_PPlus)
        have hI_pow: I = PPlus ^ m:= by
          simpa [m,hQ_top] using hIeq
        have hm: m = k:= by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p ^ m = Ideal.absNorm I:= by
              rw [hI_pow,map_pow,habsNormPPlus]
            _ = p ^ k:=hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m,hm] using hI_pow }
  exact Nat.card_unique
lemma rp265
    {q: Nat.Primes} {I: Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hI_ne: I ≠ ⊥)
    {k: ℕ} (hI_norm: Ideal.absNorm I = (q: ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆
      rp200 (K:=K) (q: ℕ):= by
  have: Fact (q: ℕ).Prime:=⟨q.2⟩
  intro PPlus hPPlus
  have hPPlus_mem: PPlus ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hPPlus
  have hPPlus_fac:=(Ideal.mem_normalizedFactors_iff hI_ne).1 hPPlus_mem
  have hPPlus_prime: PPlus.IsPrime:=hPPlus_fac.1
  have hI_le_PPlus: I ≤ PPlus:=hPPlus_fac.2
  have hPPlus_ne: PPlus ≠ ⊥:=fun hPPlus_bot =>
    hI_ne (le_bot_iff.mp (hPPlus_bot ▸ hI_le_PPlus))
  have: NeZero PPlus:=⟨hPPlus_ne⟩
  have hPPlus_dvd: Ideal.absNorm PPlus ∣ (q: ℕ) ^ k:= by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_PPlus
  have hunder_dvd: Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q: ℕ) ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm PPlus) hPPlus_dvd
  have hunder_prime: (Ideal.absNorm (Ideal.under ℤ PPlus)).Prime:=Nat.absNorm_under_prime PPlus
  have hunder_dvd_q: Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q: ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q: Ideal.absNorm (Ideal.under ℤ PPlus) = (q: ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q: Ideal.under ℤ PPlus = Ideal.span {((q: ℕ) : ℤ)}:= by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ PPlus)]
    simp [hunder_eq_q]
  have hPPlus_lies: PPlus.LiesOver (Ideal.span {((q: ℕ) : ℤ)}):= by
    rw [Ideal.liesOver_iff,hunder_eq_span_q]
  have hPPlus_over: PPlus ∈ Ideal.primesOver (rp79 (q: ℕ)) (𝓞 (NumberField.maximalRealSubfield K)):= by
    refine ⟨hPPlus_prime,?_⟩
    simpa [rp79] using hPPlus_lies
  exact (rp202 (K:=K) (ℓ:=(q: ℕ))).2 hPPlus_over
lemma rp266
    (hp_odd: p ≠ 2) {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p)
    {PPlus: Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hPPlus: PPlus ∈ rp200 (K:=K) (q: ℕ)) :
    Ideal.absNorm PPlus = (q: ℕ) ^ rp190 (p:=p) (q: ℕ) hq:= by
  have hPPlus_over: PPlus ∈ Ideal.primesOver (rp79 (q: ℕ)) (𝓞 (NumberField.maximalRealSubfield K)) :=
    (rp202 (K:=K) (ℓ:=(q: ℕ))).1 hPPlus
  have: PPlus.LiesOver (Ideal.span {((q: ℕ) : ℤ)}):= by
    simpa [rp79] using hPPlus_over.2
  have: (rp79 (q: ℕ)).IsMaximal:= by
    simpa [rp79] using Int.ideal_span_isMaximal_of_prime (q: ℕ)
  have: PPlus.IsMaximal:=Ideal.isMaximal_of_mem_primesOver hPPlus_over
  rw [← rp221
    (p:=p) (K:=K) hp_odd hq PPlus hPPlus_over]
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    (p:=Ideal.span {((q: ℕ) : ℤ)}) (q:=PPlus)]
  exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus q.2
lemma rp267
    (hp_odd: p ≠ 2) {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p)
    {I: Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hI_ne: I ≠ ⊥) {k: ℕ}
    (hI_norm: Ideal.absNorm I = (q: ℕ) ^ k) :
    rp190 (p:=p) (q: ℕ) hq *
        (UniqueFactorizationMonoid.normalizedFactors I).card = k:= by
  classical
  set d:=rp190 (p:=p) (q: ℕ) hq with hd
  set m:=UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset: m.toFinset ⊆ rp200 (K:=K) (q: ℕ):= by
    simpa [hm] using
      rp265 (K:=K) hI_ne hI_norm
  have hsum_count: ∑ PPlus ∈ rp200 (K:=K) (q: ℕ),m.count PPlus = m.card :=
    Multiset.sum_count_eq_card fun PPlus hPPlus => hsubset (Multiset.mem_toFinset.2 hPPlus)
  have hnorm_factors: Ideal.absNorm m.prod = (q: ℕ) ^ (d * m.card):= by
    rw [Finset.prod_multiset_count_of_subset m (rp200 (K:=K) (q: ℕ)) hsubset,
      map_prod]
    calc
      ∏ PPlus ∈ rp200 (K:=K) (q: ℕ),Ideal.absNorm (PPlus ^ m.count PPlus)
          = ∏ PPlus ∈ rp200 (K:=K) (q: ℕ),
              ((q: ℕ) ^ d) ^ m.count PPlus:= by
              apply Finset.prod_congr rfl
              intro PPlus hPPlus
              rw [map_pow]
              rw [rp266
                (p:=p) (K:=K) hp_odd hq hPPlus,hd]
      _ = (q: ℕ) ^
          (d * ∑ PPlus ∈ rp200 (K:=K) (q: ℕ),m.count PPlus):= by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _ = (q: ℕ) ^ (d * m.card):= by rw [hsum_count]
  have hpow: (q: ℕ) ^ (d * m.card) = (q: ℕ) ^ k:= by
    calc
      (q: ℕ) ^ (d * m.card) = Ideal.absNorm m.prod:=hnorm_factors.symm
      _ = Ideal.absNorm I:= by rw [hm,Ideal.prod_normalizedFactors_eq_self hI_ne]
      _ = (q: ℕ) ^ k:=hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow
lemma rp268
    (hp_odd: p ≠ 2) {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p)
    {k: ℕ} (hk: ¬ rp190 (p:=p) (q: ℕ) hq ∣ k) :
    rp262 (NumberField.maximalRealSubfield K) ((q: ℕ) ^ k) = 0:= by
  unfold rp262 rp234
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card,?_⟩
  simpa [mul_comm] using
    (rp267
      (p:=p) (K:=K) hp_odd hq hI_ne hI_norm).symm
lemma rp269
    (hp_odd: p ≠ 2) {q: Nat.Primes} [Fact (q: ℕ).Prime] (hq: (q: ℕ) ≠ p) (n: ℕ) :
    rp262 (NumberField.maximalRealSubfield K)
        ((q: ℕ) ^ (rp190 (p:=p) (q: ℕ) hq * n)) =
      Fintype.card (Sym {PPlus: Ideal (𝓞 (NumberField.maximalRealSubfield K)) //
        PPlus ∈ rp200 (K:=K) (q: ℕ)} n):= by
  classical
  set d:=rp190 (p:=p) (q: ℕ) hq with hd
  let α: Type _ :=
    {PPlus: Ideal (𝓞 (NumberField.maximalRealSubfield K)) // PPlus ∈ rp200 (K:=K) (q: ℕ)}
  let β: Type _:={I: rp261 (NumberField.maximalRealSubfield K) // Ideal.absNorm I.1 = (q: ℕ) ^ (d * n)}
  have hd_raw_pos: 0 < rp94 (p:=p) (q: ℕ) hq:= by
    dsimp [rp94]
    exact orderOf_pos (rp93 (p:=p) (q: ℕ) hq)
  have hd_pos: 0 < d:= by
    rw [hd]
    by_cases hde: Even (rp94 (p:=p) (q: ℕ) hq)
    · rcases hde with ⟨k,hk⟩
      rw [rp192 (p:=p) hq ⟨k,hk⟩,hk]
      omega
    · rw [rp193 (p:=p) hq hde]
      exact hd_raw_pos
  have hpmap_val :
      ∀ {m: Multiset (Ideal (𝓞 (NumberField.maximalRealSubfield K)))}
        (H: ∀ PPlus,PPlus ∈ m → PPlus ∈ rp200 (K:=K) (q: ℕ)),
        Multiset.map Subtype.val
          (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus,hPPlus⟩ : α)) m H) = m:= by
    intro m H
    rw [Multiset.map_pmap,Multiset.pmap_eq_map,Multiset.map_id']
  let toSym: β → Sym α n:=fun ⟨⟨I,hI_ne⟩,hI_norm⟩ =>
    let m:=UniqueFactorizationMonoid.normalizedFactors I
    let H: ∀ PPlus,PPlus ∈ m → PPlus ∈ rp200 (K:=K) (q: ℕ):= by
      intro PPlus hPPlus
      have hsubset: m.toFinset ⊆ rp200 (K:=K) (q: ℕ):= by
        simpa [m] using
          rp265 (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    have hm_card: m.card = n:= by
      have hmul: d * m.card = d * n:= by
        simpa [m,hd] using
          rp267
            (p:=p) (K:=K) hp_odd hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun PPlus hPPlus => (⟨PPlus,hPPlus⟩ : α)) m H,by
      simp [hm_card]⟩
  let ofSym: Sym α n → β:=fun s =>
    let m: Multiset (Ideal (𝓞 (NumberField.maximalRealSubfield K))):=s.1.map Subtype.val
    have hm_card: m.card = n:= by
      simp [m]
    have hm_subset: m.toFinset ⊆ rp200 (K:=K) (q: ℕ):= by
      intro PPlus hPPlus
      rcases Multiset.mem_toFinset.1 hPPlus with hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus,hQPlus,rfl⟩
      exact QPlus.2
    have hm_prime: ∀ PPlus ∈ m,Prime PPlus:= by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus,hQPlus,rfl⟩
      have hQPlus_ne: (QPlus: Ideal (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊥:= by
        intro hQPlus_bot
        have hQPlus_norm :=
          rp266
            (p:=p) (K:=K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot,← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((rp202 (K:=K) (ℓ:=(q: ℕ))).1 QPlus.2).1
    have hm_prod_ne: m.prod ≠ ⊥:=Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm: Ideal.absNorm m.prod = (q: ℕ) ^ (d * n):= by
      have hsum_count :
          ∑ PPlus ∈ rp200 (K:=K) (q: ℕ),m.count PPlus = m.card :=
        Multiset.sum_count_eq_card fun PPlus hPPlus =>
          hm_subset (Multiset.mem_toFinset.2 hPPlus)
      rw [Finset.prod_multiset_count_of_subset m
        (rp200 (K:=K) (q: ℕ)) hm_subset,map_prod]
      calc
        ∏ PPlus ∈ rp200 (K:=K) (q: ℕ),Ideal.absNorm (PPlus ^ m.count PPlus)
            = ∏ PPlus ∈ rp200 (K:=K) (q: ℕ),
                ((q: ℕ) ^ d) ^ m.count PPlus:= by
                apply Finset.prod_congr rfl
                intro PPlus hPPlus
                rw [map_pow]
                rw [rp266
                  (p:=p) (K:=K) hp_odd hq hPPlus,hd]
        _ = (q: ℕ) ^
            (d * ∑ PPlus ∈ rp200 (K:=K) (q: ℕ),m.count PPlus):= by
                rw [Finset.prod_pow_eq_pow_sum]
                simp [Nat.pow_mul]
        _ = (q: ℕ) ^ (d * m.card):= by rw [hsum_count]
        _ = (q: ℕ) ^ (d * n):= by rw [hm_card]
    ⟨⟨m.prod,hm_prod_ne⟩,hm_norm⟩
  have htoSym_map_val :
      ∀ b: β,
        (toSym b).1.map Subtype.val = UniqueFactorizationMonoid.normalizedFactors b.1.1:= by
    rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
    dsimp [toSym]
    let m:=UniqueFactorizationMonoid.normalizedFactors I
    let H: ∀ PPlus,PPlus ∈ m → PPlus ∈ rp200 (K:=K) (q: ℕ):= by
      intro PPlus hPPlus
      have hsubset: m.toFinset ⊆ rp200 (K:=K) (q: ℕ):= by
        simpa [m] using
          rp265 (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    change (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus,hPPlus⟩ : α)) m H).map Subtype.val = m
    rw [hpmap_val H]
  have hofSym_nfactors :
      ∀ s: Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val:= by
    intro s
    dsimp [ofSym]
    let m: Multiset (Ideal (𝓞 (NumberField.maximalRealSubfield K))):=s.1.map Subtype.val
    have hm_prime: ∀ PPlus ∈ m,Prime PPlus:= by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus,hQPlus,rfl⟩
      have hQPlus_ne: (QPlus: Ideal (𝓞 (NumberField.maximalRealSubfield K))) ≠ ⊥:= by
        intro hQPlus_bot
        have hQPlus_norm :=
          rp266
            (p:=p) (K:=K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot,← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((rp202 (K:=K) (ℓ:=(q: ℕ))).1 QPlus.2).1
    change UniqueFactorizationMonoid.normalizedFactors m.prod = m
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft: Function.LeftInverse ofSym toSym:= by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod = b.1.1
    rw [htoSym_map_val,Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright: Function.RightInverse ofSym toSym:= by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  unfold rp262 rp234
  simpa [β,α,hd,Nat.card_eq_fintype_card] using
    Nat.card_congr (⟨toSym,ofSym,hleft,hright⟩ : β ≃ Sym α n)
lemma rp270
    (hp_odd: p ≠ 2) {s: ℂ} (hs: 1 < s.re) :
    (∑' k: ℕ,(rp262 (NumberField.maximalRealSubfield K) (p ^ k) : ℂ) *
      (((p ^ k: ℕ) : ℂ) ^ (-s))) =
      (rp87 (NumberField.maximalRealSubfield K) p s)⁻¹:= by
  have: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
  have hnorm: ‖(p: ℂ) ^ (-s)‖ < 1:= by
    have hle: ‖(p: ℂ) ^ (-s)‖ ≤ 1 / 2 :=
      Complex.norm_prime_cpow_le_one_half ⟨p,hp.out⟩ hs
    exact hle.trans_lt (by norm_num)
  rw [rp232 (p:=p) (K:=K)]
  trans ∑' k: ℕ,((p: ℂ) ^ (-s)) ^ k
  · refine tsum_congr fun k => ?_
    rw [rp264 (p:=p) (K:=K) hp_odd k]
    simp only [Nat.cast_one,one_mul]
    rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul p k (-s),mul_comm,
      Complex.cpow_mul_nat]
  · simpa using tsum_geometric_of_norm_lt_one hnorm
lemma rp271
    (hp_odd: p ≠ 2) {q: Nat.Primes} {s: ℂ} (hs: 1 < s.re) :
    (∑' k: ℕ,(rp262 (NumberField.maximalRealSubfield K) ((q: ℕ) ^ k) : ℂ) *
      ((((q: ℕ) ^ k: ℕ) : ℂ) ^ (-s))) =
      (rp87 (NumberField.maximalRealSubfield K) (q: ℕ) s)⁻¹:= by
  have: Fact (q: ℕ).Prime:=⟨q.2⟩
  by_cases hq: (q: ℕ) = p
  · have hq' : q = ⟨p,Fact.out⟩:= by
      apply Subtype.ext
      simpa using hq
    subst hq'
    simpa using rp270
      (p:=p) (K:=K) hp_odd hs
  · classical
    have: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
    set d:=rp190 (p:=p) (q: ℕ) hq with hd
    let α: Type _:={PPlus: Ideal (𝓞 (NumberField.maximalRealSubfield K)) //
      PPlus ∈ rp200 (K:=K) (q: ℕ)}
    let f: ℕ → ℂ:=fun k =>
      (rp262 (NumberField.maximalRealSubfield K) ((q: ℕ) ^ k) : ℂ) * ((((q: ℕ) ^ k: ℕ) : ℂ) ^ (-s))
    let g: ℕ → ℂ:=fun n =>
      (rp262 (NumberField.maximalRealSubfield K) ((q: ℕ) ^ (d * n)) : ℂ) *
        ((((q: ℕ) ^ (d * n) : ℕ) : ℂ) ^ (-s))
    let z: ℂ:=(q: ℂ) ^ (-((d: ℂ) * s))
    have hd_raw_pos: 0 < rp94 (p:=p) (q: ℕ) hq:= by
      dsimp [rp94]
      exact orderOf_pos (rp93 (p:=p) (q: ℕ) hq)
    have hd_pos: 0 < d:= by
      rw [hd]
      by_cases hde: Even (rp94 (p:=p) (q: ℕ) hq)
      · rcases hde with ⟨k,hk⟩
        rw [rp192 (p:=p) hq ⟨k,hk⟩,hk]
        omega
      · rw [rp193 (p:=p) hq hde]
        exact hd_raw_pos
    have hs_d: 1 < (((d: ℂ) * s).re):= by
      rw [Complex.mul_re]
      simp
      have hd_ge: (1: ℝ) ≤ d:= by
        exact_mod_cast Nat.succ_le_of_lt hd_pos
      nlinarith [hs,hd_ge]
    have hz: ‖z‖ < 1:= by
      have hle: ‖z‖ ≤ 1 / 2:= by
        dsimp [z]
        exact Complex.norm_prime_cpow_le_one_half ⟨q,q.2⟩ hs_d
      exact hle.trans_lt (by norm_num)
    have hg_term: ∀ n: ℕ,g n = (Fintype.card (Sym α n) : ℂ) * z ^ n:= by
      intro n
      dsimp [g,z]
      rw [show rp262 (NumberField.maximalRealSubfield K) ((q: ℕ) ^ (d * n)) = Fintype.card (Sym α n) by
        simpa [α,hd] using
          rp269
            (p:=p) (K:=K) hp_odd hq n]
      rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul (q: ℕ) (d * n) (-s)]
      have hexp: (((d * n: ℕ) : ℂ) * (-s)) = (-((d: ℂ) * s)) * n:= by
        push_cast
        ring
      rw [hexp,Complex.cpow_mul_nat]
    have hg_eq: g = fun n: ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n:=funext hg_term
    have hg_hasSum0: HasSum (fun n: ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n)
        (((1 - z)⁻¹) ^ Fintype.card α):= by
      rw [← rp240 α hz]
      exact (rp239 α hz).1.hasSum
    have hg_hasSum: HasSum g (((1 - z)⁻¹) ^ Fintype.card α):= by
      simpa [hg_eq] using hg_hasSum0
    have hf_hasSum: HasSum f (((1 - z)⁻¹) ^ Fintype.card α):= by
      refine (hasSum_iff_hasSum_of_ne_zero_bij
        (f:=f) (g:=g) (i:=fun x: Function.support g => d * x.1) ?_ ?_ ?_).2 hg_hasSum
      · intro x y hxy
        exact Subtype.ext <| Nat.eq_of_mul_eq_mul_left hd_pos hxy
      · intro k hk
        have hk_mult: rp262 (NumberField.maximalRealSubfield K) ((q: ℕ) ^ k) ≠ 0:=fun hk_zero =>
          hk (by simp [f,hk_zero])
        have hk_dvd: d ∣ k:= by
          by_contra hk_ndvd
          exact hk_mult <|
            rp268
              (p:=p) (K:=K) hp_odd hq hk_ndvd
        obtain ⟨n,rfl⟩:=hk_dvd
        refine ⟨⟨n,?_⟩,rfl⟩
        simpa [f,g,mul_comm] using hk
      · intro x
        simp [f,g,mul_comm]
    have hcard_finset :
        (rp200 (K:=K) (q: ℕ)).card =
          rp191 (p:=p) (q: ℕ) hq:= by
      rw [rp201 (K:=K) (ℓ:=(q: ℕ))]
      exact rp223 (p:=p) (K:=K) hp_odd hq
    have hα_card: Fintype.card α = rp191 (p:=p) (q: ℕ) hq:= by
      calc
        Fintype.card α = (rp200 (K:=K) (q: ℕ)).card :=
          Fintype.card_of_finset' (rp200 (K:=K) (q: ℕ)) fun PPlus => by simp
        _ = rp191 (p:=p) (q: ℕ) hq:=hcard_finset
    have hf_hasSum' : HasSum f ((rp87 (NumberField.maximalRealSubfield K) (q: ℕ) s)⁻¹):= by
      rw [rp224
        (p:=p) (K:=K) hp_odd hq,← inv_pow]
      simpa [z,hd,hα_card] using hf_hasSum
    simpa [f] using hf_hasSum'.tsum_eq
lemma rp272 (hp_odd: p ≠ 2) {s: ℂ} (hs: 1 < s.re) :
    NumberField.dedekindZeta (NumberField.maximalRealSubfield K) s =
      ∏' q: Nat.Primes,(rp87 (NumberField.maximalRealSubfield K) (q: ℕ) s)⁻¹:= by
  rw [rp263 (L:=(NumberField.maximalRealSubfield K)) hs]
  exact tprod_congr fun q =>
    rp271 (p:=p) (K:=K) hp_odd hs
lemma rp273 {s: ℂ} (hs: 1 < s.re) :
    rp89 p s =
      ∏' q: Nat.Primes,
        ∏ χ ∈ rp82 (p:=p),
          (1 - χ ((q: ℕ) : ZMod p) * ((q: ℕ) : ℂ) ^ (-s))⁻¹:= by
  classical
  unfold rp89
  rw [Finset.prod_congr rfl (fun χ _ => rp251 p χ hs)]
  exact (Multipliable.tprod_finsetProd
    (s:=rp82 (p:=p))
    (fun χ _ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)).symm
lemma rp274 {s: ℂ} (hs: 1 < s.re) :
    rp89 p s =
      ∏' q: Nat.Primes,(rp86 (p:=p) (q: ℕ) s)⁻¹:= by
  classical
  rw [rp273 (p:=p) hs]
  refine tprod_congr fun q => ?_
  unfold rp86
  rw [Finset.prod_inv_distrib]
lemma rp275 {s: ℂ} :
    rp86 (p:=p) p s = 1:= by
  classical
  exact Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self,MulChar.map_nonunit _ not_isUnit_zero,zero_mul,sub_zero]
lemma rp276 (hp_odd: p ≠ 2)
    {q: Nat.Primes} (hq: (q: ℕ) ≠ p) {s: ℂ} :
    rp87 (NumberField.maximalRealSubfield K) (q: ℕ) s =
      (1 - ((q: ℕ) : ℂ) ^ (-s)) * rp86 (p:=p) (q: ℕ) s:= by
  have: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
  have: Fact (q: ℕ).Prime:=⟨q.2⟩
  rw [rp224 (p:=p) (K:=K) hp_odd hq]
  symm
  simpa [neg_mul] using
    (rp199
      (p:=p) hp_odd hq (s:=s))
lemma rp277 (hp_odd: p ≠ 2) {s: ℂ} :
    rp87 (NumberField.maximalRealSubfield K) p s =
      (1 - (p: ℂ) ^ (-s)) * rp86 (p:=p) p s:= by
  have: IsCMField K:=rp64 (p:=p) (K:=K) hp_odd
  rw [rp275 (p:=p),mul_one,rp232 (p:=p) (K:=K)]
lemma rp278 (hp_odd: p ≠ 2) {q: Nat.Primes} {s: ℂ} :
    rp87 (NumberField.maximalRealSubfield K) (q: ℕ) s =
      (1 - ((q: ℕ) : ℂ) ^ (-s)) * rp86 (p:=p) (q: ℕ) s:= by
  by_cases hq: (q: ℕ) = p
  · have hq' : q = ⟨p,Fact.out⟩:= by
      apply Subtype.ext
      simpa using hq
    subst hq'
    exact rp277 (p:=p) (K:=K) hp_odd
  · exact rp276 (p:=p) (K:=K) hp_odd hq
theorem rp279
    (hp_odd: p ≠ 2) {s: ℂ} (hs: 1 < s.re) :
    NumberField.dedekindZeta (NumberField.maximalRealSubfield K) s = riemannZeta s * rp89 p s:= by
  have hmul_riem :
      Multipliable (fun q: Nat.Primes => (1 - ((q: ℕ) : ℂ) ^ (-s))⁻¹) :=
    (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hmul_even :
      Multipliable (fun q: Nat.Primes => (rp86 (p:=p) (q: ℕ) s)⁻¹):= by
    classical
    have h1 :
        (fun q: Nat.Primes => (rp86 (p:=p) (q: ℕ) s)⁻¹) =
          (fun q: Nat.Primes =>
            ∏ χ ∈ rp82 (p:=p),
              (1 - χ ((q: ℕ) : ZMod p) * ((q: ℕ) : ℂ) ^ (-s))⁻¹):= by
      funext q
      unfold rp86
      rw [Finset.prod_inv_distrib]
    rw [h1]
    exact multipliable_prod (s:=rp82 (p:=p)) fun χ _ =>
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  calc
    NumberField.dedekindZeta (NumberField.maximalRealSubfield K) s
        = ∏' q: Nat.Primes,(rp87 (NumberField.maximalRealSubfield K) (q: ℕ) s)⁻¹ :=
            rp272 (p:=p) (K:=K) hp_odd hs
    _ = ∏' q: Nat.Primes,
          ((1 - ((q: ℕ) : ℂ) ^ (-s))⁻¹ *
            (rp86 (p:=p) (q: ℕ) s)⁻¹):= by
            refine tprod_congr fun q => ?_
            rw [rp278 (p:=p) (K:=K) hp_odd,mul_inv_rev,mul_comm]
    _ = (∏' q: Nat.Primes,(1 - ((q: ℕ) : ℂ) ^ (-s))⁻¹) *
          (∏' q: Nat.Primes,(rp86 (p:=p) (q: ℕ) s)⁻¹):= by
            rw [Multipliable.tprod_mul hmul_riem hmul_even]
    _ = riemannZeta s * rp89 p s:= by
            rw [riemannZeta_eulerProduct_tprod hs,rp274 (p:=p) hs]
theorem rp280 :
    Filter.Tendsto
      (fun s: ℝ ↦ (s - 1) * (riemannZeta (s: ℂ) * rp89 p (s: ℂ)))
      (𝓝[>] 1)
      (𝓝 (rp89 p (1: ℂ))):= by
  classical
  have h_cont: Continuous (rp89 p) :=
    continuous_finsetProd _ fun χ hχ =>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_filter.mp hχ).2.2).continuous
  have h_embed :
      Filter.Tendsto (fun s: ℝ => (s: ℂ)) (𝓝[>] (1: ℝ)) (𝓝[≠] (1: ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta: Filter.Tendsto (fun s: ℝ => ((s: ℂ) - 1) * riemannZeta (s: ℂ))
      (𝓝[>] (1: ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod: Filter.Tendsto (fun s: ℝ => rp89 p (s: ℂ))
      (𝓝[>] (1: ℝ)) (𝓝 (rp89 p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod:=h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring
theorem rp281 (hp_odd: p ≠ 2) :
    Filter.Tendsto
      (fun s: ℝ ↦ (s - 1) * NumberField.dedekindZeta (NumberField.maximalRealSubfield K) (s: ℂ))
      (𝓝[>] 1)
      (𝓝 (rp89 p (1: ℂ))):= by
  refine (Filter.tendsto_congr' ?_).mp
    (rp280 (p:=p))
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [rp279
    (p:=p) (K:=K) hp_odd (by exact_mod_cast hs)]
theorem rp282 (hp_odd: p ≠ 2) :
    ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) = rp89 p (1: ℂ) :=
  tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (NumberField.maximalRealSubfield K))
    (rp281 (p:=p) (K:=K) hp_odd)
end KummerCriterion
end

section
noncomputable section
open Filter
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p: ℕ) [hp: Fact p.Prime]
lemma rp283 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) (n: ℕ) :
    ‖∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
  let z: ℂ:=Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one: z ≠ 1:= by
    intro hz
    have hexp: Complex.exp ((2 * Real.pi * x) * Complex.I) = 1:= by simpa [z] using hz
    obtain ⟨m,hm⟩:=Complex.exp_eq_one_iff.mp hexp
    have him: 2 * Real.pi * x = (m: ℝ) * (2 * Real.pi):= by
      simpa using congrArg Complex.im hm
    have hm_pos: (0: ℝ) < m:= by nlinarith [Real.pi_pos,hx₀,him]
    have hm_lt_one: (m: ℝ) < 1:= by nlinarith [Real.pi_pos,hx₁,him]
    have hm_pos_int: 0 < m:= by exact_mod_cast hm_pos
    have hm_lt_one_int: m < 1:= by exact_mod_cast hm_lt_one
    lia
  have hre :
      ((∑ i ∈ Finset.range n,z ^ i).re: ℝ) =
        ∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i):= by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i: ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring,Complex.exp_ofReal_mul_I_re]
  have hgeom: ‖∑ i ∈ Finset.range n,z ^ i‖ ≤ 2 / ‖z - 1‖:= by
    calc
      ‖∑ i ∈ Finset.range n,z ^ i‖ = ‖(z ^ n - 1) / (z - 1)‖:= by
        rw [geom_sum_eq hz_ne_one]
      _ = ‖z ^ n - 1‖ / ‖z - 1‖:= by rw [Complex.norm_div]
      _ ≤ 2 / ‖z - 1‖:= by
        have hden: 0 < ‖z - 1‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
        have hnum: ‖z ^ n - 1‖ ≤ 2:= by
          calc
            ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1: ℂ)‖:=norm_sub_le _ _
            _ = 1 + 1:= by
              rw [norm_pow]
              have hz_norm: ‖z‖ = 1:= by
                simpa [z] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
              rw [hz_norm]
              simp
            _ = 2:= by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n,z ^ i).re: ℝ)‖:= by rw [hre]
    _ ≤ ‖∑ i ∈ Finset.range n,z ^ i‖:= by
      simpa using (RCLike.norm_re_le_norm (∑ i ∈ Finset.range n,z ^ i))
    _ ≤ 2 / ‖z - 1‖:=hgeom
    _ = 2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
      simp [z,norm_sub_rev]
lemma rp284 (x: ℝ) (i: ℕ) :
    Continuous fun s: ℝ =>
      Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)):= by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1
lemma rp285 (x s: ℝ) (hs: 1 < s) :
    HasSum (fun n: ℕ => Real.cos (2 * Real.pi * x * (n + 1)) / ((n + 1: ℂ) ^ (s: ℂ)))
      (HurwitzZeta.cosZeta x s):= by
  let f: ℕ → ℂ:=fun n => Real.cos (2 * Real.pi * x * n) / ((n: ℂ) ^ (s: ℂ))
  have hfull: HasSum f (HurwitzZeta.cosZeta x s):= by
    simpa [f] using HurwitzZeta.hasSum_nat_cosZeta x (show 1 < ((s: ℂ)).re by simpa)
  have hshift: HasSum (fun n: ℕ => f (n + 1)) (∑' n: ℕ,f (n + 1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull' : HasSum f (f 0 + ∑' n: ℕ,f (n + 1)):=hshift.zero_add
  have hvalue: (∑' n: ℕ,f (n + 1)) = HurwitzZeta.cosZeta x s:= by
    have hs0: ((s: ℂ)) ≠ 0:= by
      exact_mod_cast (show s ≠ 0 by linarith)
    have hf0: f 0 = 0:= by
      simp [f,hs0]
    have:=tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [hf0] using this
  exact hvalue ▸ hshift.congr_fun (fun n => by simp [f])
lemma rp286 {x s: ℝ} (hx₀: 0 < x) (hx₁: x < 1) (hs: 1 ≤ s)
    (m n: ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1: ℕ) : ℂ) ^ (s: ℂ))‖ ≤
      (8 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
        (1 / (m + 1: ℝ) ^ s):= by
  let a: ℕ → ℝ:=fun k => 1 / (k + 1: ℝ) ^ s
  let z: ℕ → ℂ:=fun k => Real.cos (2 * Real.pi * x * (k + 1))
  have ha: Antitone a:= by
    intro i j hij
    have hij' : (i + 1: ℝ) ≤ j + 1:= by exact_mod_cast Nat.succ_le_succ hij
    have hi_pos: 0 < (i + 1: ℝ):= by positivity
    have hs_nonneg: 0 ≤ s:=le_trans zero_lt_one.le hs
    have hpow: (i + 1: ℝ) ^ s ≤ (j + 1: ℝ) ^ s :=
      Real.rpow_le_rpow hi_pos.le hij' hs_nonneg
    simpa [a,one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hi_pos _) hpow
  have ha_nonneg: ∀ k,0 ≤ a k:= by
    intro k
    positivity
  have hzbound :
      ∀ k,‖∑ i ∈ Finset.range k,z i‖ ≤
        4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
    intro k
    let f: ℕ → ℝ:=fun i => Real.cos (2 * Real.pi * x * i)
    have hsum0:=Finset.sum_range_add f 1 k
    have hsum :
        ∑ i ∈ Finset.range k,Real.cos (2 * Real.pi * x * (i + 1)) =
          ∑ i ∈ Finset.range (k + 1),Real.cos (2 * Real.pi * x * i) - 1:= by
      rw [Finset.sum_range_one] at hsum0
      calc
        ∑ i ∈ Finset.range k,Real.cos (2 * Real.pi * x * (i + 1))
            = ∑ i ∈ Finset.range k,f (1 + i):= by simp [f,add_comm]
        _ = ∑ i ∈ Finset.range (k + 1),f i - f 0 :=
              eq_sub_iff_add_eq.mpr (by
                simpa [add_comm,add_left_comm,add_assoc,Nat.add_comm] using hsum0.symm)
        _ = ∑ i ∈ Finset.range (k + 1),Real.cos (2 * Real.pi * x * i) - 1:= by simp [f]
    rw [show (∑ i ∈ Finset.range k,z i) =
        ((∑ i ∈ Finset.range k,Real.cos (2 * Real.pi * x * (i + 1)) : ℝ) : ℂ) by
          simp [z,Complex.ofReal_sum]]
    rw [Complex.norm_real,hsum]
    calc
      |∑ i ∈ Finset.range (k + 1),Real.cos (2 * Real.pi * x * i) - 1|
          ≤ |∑ i ∈ Finset.range (k + 1),Real.cos (2 * Real.pi * x * i) - 0| +
              |0 - (1: ℝ)|:= by
              simpa using
                abs_sub_le
                  (∑ i ∈ Finset.range (k + 1),Real.cos (2 * Real.pi * x * i)) 0 1
      _ ≤ |∑ i ∈ Finset.range (k + 1),Real.cos (2 * Real.pi * x * i)| + 1:= by simp
      _ ≤ (2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) + 1:= by
            have hcos :
                |∑ i ∈ Finset.range (k + 1),Real.cos (2 * Real.pi * x * i)| ≤
                  2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
              simpa using rp283 hx₀ hx₁ (k + 1)
            exact add_le_add hcos le_rfl
      _ ≤ 2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ +
            2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
            have hdenom :
                1 ≤ 2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
              have hnorm: ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≤ 2:= by
                calc
                  ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
                      ≤ ‖(1: ℂ)‖ + ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                        norm_sub_le _ _
                  _ = 1 + 1:= by
                        rw [norm_one]
                        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
                  _ = 2:= by norm_num
              have hzero: (1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0:= by
                intro hzero
                have hexp: Complex.exp ((2 * Real.pi * x) * Complex.I) = 1:= by
                  simpa [eq_comm] using sub_eq_zero.mp hzero
                obtain ⟨m,hm⟩:=Complex.exp_eq_one_iff.mp hexp
                have him: 2 * Real.pi * x = (m: ℝ) * (2 * Real.pi):= by
                  simpa using congrArg Complex.im hm
                have hm_pos: (0: ℝ) < m:= by nlinarith [Real.pi_pos,hx₀,him]
                have hm_lt_one: (m: ℝ) < 1:= by nlinarith [Real.pi_pos,hx₁,him]
                have hm_pos_int: 0 < m:= by exact_mod_cast hm_pos
                have hm_lt_one_int: m < 1:= by exact_mod_cast hm_lt_one
                lia
              have hden_pos: 0 < ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                norm_pos_iff.mpr hzero
              simpa using (one_le_div hden_pos).2 hnorm
            linarith
      _ = 4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by ring
  calc
    ‖∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1: ℕ) : ℂ) ^ (s: ℂ))‖
        = ‖∑ i ∈ Finset.range n,a (m + i) • z (m + i)‖:= by
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            have hcpow :
                (((m + i + 1: ℕ) : ℂ) ^ (s: ℂ)) =
                  ((((m + i + 1: ℕ) : ℝ) ^ s: ℝ) : ℂ):= by
              simpa using
                (Complex.ofReal_cpow (x:=(m + i + 1: ℝ)) (by positivity) (y:=s)).symm
            rw [hcpow]
            simp [a,z,div_eq_mul_inv,mul_comm,mul_left_comm]
    _ ≤ (2 * (4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) * a m :=
          rp170 ha ha_nonneg hzbound m n
    _ = (8 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
          (1 / (m + 1: ℝ) ^ s):= by
          have hcoef :
              (2 * (4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) =
                8 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
            ring
          rw [hcoef]
lemma rp287 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    ∃ l: ℝ,
      Tendsto
        (fun n ↦
          ∑ i ∈ Finset.range n,if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
        atTop (𝓝 l):= by
  let f: ℕ → ℝ:=fun n => if n = 0 then 1 else 1 / n
  let z: ℕ → ℝ:=fun n => if n = 0 then 0 else Real.cos (2 * Real.pi * x * n)
  have hf: Antitone f:= by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f,hb.ne']
        have hb1: (1: ℝ) ≤ b:= by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb: 0 < b:=lt_of_lt_of_le ha hab
      simp [f,ha.ne',(Nat.ne_of_gt hb)]
      have ha' : (0: ℝ) < a:= by exact_mod_cast ha
      have hab' : (a: ℝ) ≤ b:= by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0: Tendsto f atTop (𝓝 0):= by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n: ℕ => 1 / (n + 1: ℝ)) atTop (𝓝 0))
  have hbound :
      ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤
        4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · have: 0 ≤ 4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
        positivity
      simpa [z] using this
    · let g: ℕ → ℝ:=fun i => Real.cos (2 * Real.pi * x * i)
      have hz0:=Finset.sum_range_add z 1 (n - 1)
      have hg0:=Finset.sum_range_add g 1 (n - 1)
      have hsum :
          ∑ i ∈ Finset.range n,z i =
            ∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i) - 1:= by
        have hn' : 1 + (n - 1) = n:= by
          simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hn
        have hz0' :
            ∑ x ∈ Finset.range n,z x =
              ∑ x ∈ Finset.range 1,z x + ∑ x ∈ Finset.range (n - 1),z (1 + x):= by
          simpa [hn',add_comm] using hz0
        have hg0' :
            ∑ x ∈ Finset.range n,g x =
              ∑ x ∈ Finset.range 1,g x + ∑ x ∈ Finset.range (n - 1),g (1 + x):= by
          simpa [hn',add_comm] using hg0
        rw [Finset.sum_range_one] at hz0' hg0'
        calc
          ∑ i ∈ Finset.range n,z i = z 0 + ∑ i ∈ Finset.range (n - 1),z (1 + i):= by
            simpa [add_comm,add_left_comm,add_assoc,Nat.add_comm] using hz0'
          _ = ∑ i ∈ Finset.range (n - 1),g (1 + i):= by simp [z,g]
          _ = ∑ i ∈ Finset.range n,g i - g 0 :=
                eq_sub_iff_add_eq.mpr (by
                  simpa [add_comm,add_left_comm,add_assoc,Nat.add_comm] using hg0'.symm)
          _ = ∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i) - 1:= by simp [g]
      rw [hsum]
      calc
        |∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i) - 1|
            ≤ |∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i) - 0| +
                |0 - (1: ℝ)|:= by
                simpa using
                  abs_sub_le
                    (∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i)) 0 1
        _ ≤ |∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i)| + 1:= by simp
        _ ≤ (2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) + 1:= by
              have hcos :
                  |∑ i ∈ Finset.range n,Real.cos (2 * Real.pi * x * i)| ≤
                    2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
                simpa using rp283 hx₀ hx₁ n
              exact add_le_add hcos le_rfl
        _ ≤ 2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ +
              2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
              have hnorm: ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≤ 2:= by
                calc
                  ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
                      ≤ ‖(1: ℂ)‖ + ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                        norm_sub_le _ _
                  _ = 1 + 1:= by
                        rw [norm_one]
                        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
                  _ = 2:= by norm_num
              have hzero: (1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0:= by
                intro hzero
                have hexp: Complex.exp ((2 * Real.pi * x) * Complex.I) = 1:= by
                  simpa [eq_comm] using sub_eq_zero.mp hzero
                obtain ⟨m,hm⟩:=Complex.exp_eq_one_iff.mp hexp
                have him: 2 * Real.pi * x = (m: ℝ) * (2 * Real.pi):= by
                  simpa using congrArg Complex.im hm
                have hm_pos: (0: ℝ) < m:= by nlinarith [Real.pi_pos,hx₀,him]
                have hm_lt_one: (m: ℝ) < 1:= by nlinarith [Real.pi_pos,hx₁,him]
                have hm_pos_int: 0 < m:= by exact_mod_cast hm_pos
                have hm_lt_one_int: m < 1:= by exact_mod_cast hm_lt_one
                lia
              have hden_pos: 0 < ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                norm_pos_iff.mpr hzero
              have hdenom :
                  1 ≤ 2 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
                simpa using (one_le_div hden_pos).2 hnorm
              linarith
        _ = 4 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by ring
  have hcauchy:=hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l,hl⟩:=cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l,?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n,f i • z i) =
        fun n ↦
          ∑ i ∈ Finset.range n,if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i:= by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f,z]
    · simp [f,z,hi.ne',smul_eq_mul,div_eq_mul_inv,mul_comm]
  exact hseries ▸ hl
lemma rp288 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n,if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
      atTop (𝓝 (-Real.log (2 * Real.sin (Real.pi * x)))):= by
  obtain ⟨l,hl⟩:=rp287 hx₀ hx₁
  let coeff: ℕ → ℝ:=fun n =>
    if n = 0 then 0 else Real.cos (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r: ℝ => ∑' n,coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r: ℝ => ∑' n,coeff n * r ^ n)
        (fun r: ℝ =>
          -Real.log ‖(1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (Set.Ioo 0 1):= by
    intro r hr
    have hr₀: 0 ≤ r:=hr.1.le
    have hr₁: r < 1:=hr.2
    calc
      ∑' n: ℕ,coeff n * r ^ n
          = ∑' n: ℕ,(r ^ n / n) * Real.cos (2 * Real.pi * x * n):= by
              refine tsum_congr fun n: ℕ => ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff,hn.ne',div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
      _ = -Real.log ‖(1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
            (rp166 x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r: ℝ =>
          -Real.log ‖(1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hzero :
      (1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0:= by
    intro hzero
    have hexp: Complex.exp ((2 * Real.pi * x) * Complex.I) = 1:= by
      simpa [eq_comm] using sub_eq_zero.mp hzero
    obtain ⟨m,hm⟩:=Complex.exp_eq_one_iff.mp hexp
    have him: 2 * Real.pi * x = (m: ℝ) * (2 * Real.pi):= by
      simpa using congrArg Complex.im hm
    have hm_pos: (0: ℝ) < m:= by nlinarith [Real.pi_pos,hx₀,him]
    have hm_lt_one: (m: ℝ) < 1:= by nlinarith [Real.pi_pos,hx₁,him]
    have hm_pos_int: 0 < m:= by exact_mod_cast hm_pos
    have hm_lt_one_int: m < 1:= by exact_mod_cast hm_lt_one
    lia
  have hcont :
      Tendsto
        (fun r: ℝ =>
          -Real.log ‖(1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1)
        (𝓝 (-Real.log ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)):= by
    have hinner :
        ContinuousAt
          (fun r: ℝ => (1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)) 1 :=
      continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have hnorm :
        ContinuousAt
          (fun r: ℝ =>
            ‖(1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      continuous_norm.continuousAt.comp hinner
    have hnorm_ne :
        ‖(1: ℂ) - ((1: ℝ) : ℂ) *
            Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≠ 0:= by
      simpa using (norm_ne_zero_iff.mpr hzero)
    have hlog :
        ContinuousAt
          (fun r: ℝ =>
            Real.log ‖(1: ℂ) - (r: ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      hnorm.log hnorm_ne
    convert! tendsto_nhdsWithin_of_tendsto_nhds hlog.neg.tendsto using 2
    simp
  have ht₀: 0 < 2 * Real.pi * x:= by nlinarith [hx₀,Real.pi_pos]
  have ht₂π: 2 * Real.pi * x < 2 * Real.pi:= by nlinarith [hx₁,Real.pi_pos]
  have hnorm_value :
      ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ =
        2 * Real.sin (Real.pi * x):= by
    simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using
      rp167 ht₀ ht₂π
  have hl_eq: l = -Real.log (2 * Real.sin (Real.pi * x)) :=
    tendsto_nhds_unique habel' (by simpa [hnorm_value] using hcont)
  simpa [hl_eq] using hl
lemma rp289 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    Tendsto
      (fun n: ℕ => ∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (1: ℂ)))
      atTop (nhds ((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)):= by
  let F: ℕ → ℂ:=fun n =>
    ((∑ i ∈ Finset.range n,
        if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i: ℝ) : ℂ)
  have hbase: Tendsto F atTop (nhds (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))):= by
    simpa [F] using (rp288 hx₀ hx₁).ofReal
  have hshifted: Tendsto (fun n: ℕ => F (n + 1)) atTop
      (nhds (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n => ?_
  have hsum :=
    Finset.sum_range_add
      (fun i: ℕ => (((if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i: ℝ)) : ℂ)) 1 n
  simpa [F,add_comm,add_left_comm,add_assoc] using hsum
lemma rp290 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    UniformCauchySeqOn
      (fun n (s: ℝ) => ∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)))
      atTop (Set.Ici 1):= by
  rw [Metric.uniformCauchySeqOn_iff]
  let B: ℝ :=
    8 / ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
  have hdenom: 0 < ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖:= by
    have ht₀: 0 < 2 * Real.pi * x:= by nlinarith [hx₀,Real.pi_pos]
    have ht₂π: 2 * Real.pi * x < 2 * Real.pi:= by nlinarith [hx₁,Real.pi_pos]
    have hnorm_eq :
        ‖(1: ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ =
          2 * Real.sin (Real.pi * x):= by
      simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using
        rp167 ht₀ ht₂π
    rw [hnorm_eq]
    have hxπ: Real.pi * x ∈ Set.Ioo 0 Real.pi:= by
      constructor <;> nlinarith [hx₀,hx₁,Real.pi_pos]
    have hsin: 0 < Real.sin (Real.pi * x):=Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hB_pos: 0 < B:= by
    positivity
  intro ε hε
  obtain ⟨N,hN⟩:=exists_nat_one_div_lt (div_pos hε hB_pos)
  refine ⟨N,?_⟩
  have htail_bound :
      ∀ ⦃m n: ℕ⦄,N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1: ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)))
            (∑ i ∈ Finset.range n,
              Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ)))
          < ε:= by
    intro m n hm hmn s hs
    let term: ℕ → ℂ:=fun k =>
      Real.cos (2 * Real.pi * x * (k + 1)) / ((k + 1: ℂ) ^ (s: ℂ))
    have hsplit :
        ∑ i ∈ Finset.range n,term i =
          ∑ i ∈ Finset.range m,term i + ∑ i ∈ Finset.range (n - m),term (m + i):= by
      simpa [term,Nat.add_sub_of_le hmn] using Finset.sum_range_add term m (n - m)
    have hs' : 1 ≤ s:=hs
    rw [dist_eq_norm,norm_sub_rev]
    calc
      ‖∑ i ∈ Finset.range n,term i - ∑ i ∈ Finset.range m,term i‖
          = ‖∑ i ∈ Finset.range (n - m),term (m + i)‖:= by
              rw [hsplit]
              ring_nf
      _ ≤ B * (1 / (m + 1: ℝ) ^ s):= by
            simpa [B,term,add_assoc,add_comm,add_left_comm] using
              rp286 (x:=x) hx₀ hx₁ hs' m (n - m)
      _ ≤ B * (1 / (m + 1: ℝ)):= by
            have hm1: 1 ≤ (m + 1: ℝ):= by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow: (m + 1: ℝ) ^ (1: ℝ) ≤ (m + 1: ℝ) ^ s:= by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv: 1 / (m + 1: ℝ) ^ s ≤ 1 / (m + 1: ℝ):= by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m + 1: ℝ) ^ (1: ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hB_pos.le
      _ ≤ B * (1 / (N + 1: ℝ)):= by
            have hm_inv: 1 / (m + 1: ℝ) ≤ 1 / (N + 1: ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N + 1: ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hB_pos.le
      _ < B * (ε / B) :=
            mul_lt_mul_of_pos_left hN hB_pos
      _ = ε:= by
            field_simp [hB_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs
theorem rp291 {x: ℝ} (hx₀: 0 < x) (hx₁: x < 1) :
    HurwitzZeta.cosZeta x 1 = (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)):= by
  let boundary: ℂ:=(((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))
  let S: ℕ → ℝ → ℂ:=fun n s =>
    ∑ i ∈ Finset.range n,
      Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1: ℂ) ^ (s: ℂ))
  let G: ℝ → ℂ:=fun s => if hs: s = 1 then boundary else HurwitzZeta.cosZeta x s
  have hCauchy: UniformCauchySeqOn S atTop (Set.Ici 1):= by
    simpa [S] using rp290 (x:=x) hx₀ hx₁
  have hpoint: ∀ s ∈ Set.Ici (1: ℝ),Tendsto (fun n => S n s) atTop (𝓝 (G s)):= by
    intro s hs
    by_cases hs1: s = 1
    · simpa [S,G,hs1,boundary] using rp289 (x:=x) hx₀ hx₁
    · have hslt: 1 < s:=lt_of_le_of_ne hs (by simpa [eq_comm] using hs1)
      simpa [S,G,hs1] using (rp285 (x:=x) s hslt).tendsto_sum_nat
  have hunif: TendstoUniformlyOn S G atTop (Set.Ici 1) :=
    hCauchy.tendstoUniformlyOn_of_tendsto hpoint
  have hcont: ContinuousOn G (Set.Ici (1: ℝ)):= by
    apply hunif.continuousOn
    refine Frequently.of_forall fun n => ?_
    classical
    dsimp [S]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _ => rp284 x i
  have hG_right: Tendsto G (𝓝[Set.Ioi 1] 1) (𝓝 boundary):= by
    have hG_Ici: Tendsto G (𝓝[Set.Ici 1] 1) (𝓝 boundary):= by
      simpa [G,boundary] using (hcont 1 (by simp)).tendsto
    exact hG_Ici.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hG_eq: G =ᶠ[𝓝[Set.Ioi 1] 1] fun s: ℝ => HurwitzZeta.cosZeta x s:= by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hslt: 1 < s:= by simpa using hs
    simp [G,ne_of_gt hslt]
  have hcos_right: Tendsto (fun s: ℝ => HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    Tendsto.congr' hG_eq hG_right
  have hcos_cont: Tendsto (fun s: ℝ => HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.cosZeta x 1)):= by
    have hxadd: (x: UnitAddCircle) ≠ 0:= by
      intro hxzero
      rw [AddCircle.coe_eq_zero_iff] at hxzero
      rcases hxzero with ⟨n,hn⟩
      have hn' : (n: ℝ) = x:= by simpa using hn
      have hn_pos: (0: ℝ) < n:= by nlinarith [hx₀,hn']
      have hn_lt_one: (n: ℝ) < 1:= by nlinarith [hx₁,hn']
      have hn_pos_int: 0 < n:= by exact_mod_cast hn_pos
      have hn_lt_one_int: n < 1:= by exact_mod_cast hn_lt_one
      lia
    have hcomplex: Tendsto (fun z: ℂ => HurwitzZeta.cosZeta x z) (𝓝 (1: ℂ))
        (𝓝 (HurwitzZeta.cosZeta x 1)) :=
      (HurwitzZeta.differentiableAt_cosZeta (a:=(x: UnitAddCircle)) (s:=(1: ℂ))
        (Or.inr hxadd)).continuousAt.tendsto
    have hreal: Tendsto (fun s: ℝ => (s: ℂ)) (𝓝 (1: ℝ)) (𝓝 (1: ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hcomp: Tendsto (fun s: ℝ => HurwitzZeta.cosZeta x (s: ℂ)) (𝓝 (1: ℝ))
        (𝓝 (HurwitzZeta.cosZeta x 1)):= by
      simpa [Function.comp] using! hcomplex.comp hreal
    exact hcomp.mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hcos_right hcos_cont).symm
theorem rp292 {a: ZMod p} (ha: a ≠ 0) :
    HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
      (((-Real.log (2 * Real.sin (Real.pi * (a.val / p: ℝ))) : ℝ) : ℂ)):= by
  have hx:=rp160 (p:=p) ha
  rw [ZMod.toAddCircle_apply]
  exact rp291 (x:=(a.val / p: ℝ)) hx.1 hx.2
lemma rp293 {a: ZMod p} (ha: a ≠ 0) :
    ‖(1: ℂ) - ZMod.stdAddChar (N:=p) a‖ =
      2 * Real.sin (Real.pi * (a.val / p: ℝ)):= by
  have hx:=rp160 (p:=p) ha
  have ht₀: 0 < 2 * Real.pi * (a.val / p: ℝ):= by
    nlinarith [hx.1,Real.pi_pos]
  have ht₂π: 2 * Real.pi * (a.val / p: ℝ) < 2 * Real.pi:= by
    nlinarith [hx.2,Real.pi_pos]
  rw [ZMod.stdAddChar_apply,ZMod.toCircle_apply]
  have hexp :
      Complex.exp (2 * (Real.pi: ℂ) * Complex.I * (a.val: ℂ) / (p: ℂ)) =
        Complex.exp ((((2 * Real.pi * (a.val / p: ℝ)) : ℝ) : ℂ) * Complex.I):= by
    congr 1
    push_cast
    ring
  rw [hexp]
  convert rp167 ht₀ ht₂π using 1
  ring_nf
end LValueAtOne
end KummerCriterion
end

section
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p: ℕ) [hp: Fact p.Prime]
theorem rp294
    {χ: DirichletCharacter ℂ p} (hχ_prim: χ.IsPrimitive) (hχ_even: χ.Even)
    (hχ_ne_one: χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 = rp183 p χ:= by
  let _:=hχ_prim
  change ZMod.LFunction (fun a: ZMod p => χ a) 1 = rp183 p χ
  have hp_ne_one: p ≠ 1:=hp.out.ne_one
  have hχinv_ne_one: χ⁻¹ ≠ 1:= by
    intro h
    apply hχ_ne_one
    calc
      χ = χ⁻¹⁻¹:=(inv_inv χ).symm
      _ = 1:= by simp [h]
  have hχinv_even: (χ⁻¹).Even:= by
    rw [DirichletCharacter.Even] at hχ_even ⊢
    rw [MulChar.inv_apply_eq_inv',hχ_even]
    simp
  have hχinv_prim: (χ⁻¹).IsPrimitive:= by
    rw [DirichletCharacter.isPrimitive_def]
    have hdiv: (χ⁻¹).conductor ∣ p:=DirichletCharacter.conductor_dvd_level (χ⁻¹)
    rcases (Nat.dvd_prime hp.out).mp hdiv with hcond | hcond
    · exact (hχinv_ne_one <| (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hcond).elim
    · exact hcond
  have hχinv_zero: χ⁻¹ 0 = 0:=(χ⁻¹).map_zero' hp_ne_one
  let χinv: ZMod p → ℂ:=fun a => χ⁻¹ a
  have hdft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1:= by
    simpa using
      (ZMod.LFunction_dft (Φ:=χinv) (s:=(1: ℂ))
        (hs:=Or.inl (by simpa [χinv] using hχinv_zero)))
  have hft :
      ZMod.dft χinv = fun a: ZMod p =>
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * χ a:= by
    funext a
    simpa [χinv,hχ_even.to_fun a,mul_comm] using
      (DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ:=χ⁻¹) hχinv_prim a)
  have hleft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * ZMod.LFunction χ 1:= by
    rw [hft,ZMod.LFunction,ZMod.LFunction]
    calc
      (p: ℂ) ^ (-1: ℂ) *
          ∑ a: ZMod p,
            (gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * χ a) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1
          = (p: ℂ) ^ (-1: ℂ) *
              (gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) *
                ∑ a: ZMod p,χ a * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1):= by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by ring
      _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * ZMod.LFunction χ 1:= by
            rw [ZMod.LFunction]
            ring
  have hsum_sin_zero :
      ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 = 0:= by
    refine (hχinv_even.to_fun.mul_odd fun a => ?_).sum_eq_zero
    simpa using HurwitzZeta.sinZeta_neg (ZMod.toAddCircle a) (1: ℂ)
  have hsum_isin_zero :
      ∑ a: ZMod p,χ⁻¹ a *
          (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) = 0:= by
    calc
      ∑ a: ZMod p,χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)
          = Complex.I *
              ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1:= by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by ring
      _ = 0:= by rw [hsum_sin_zero,mul_zero]
  have hsum_exp :
      ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 =
        ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1:= by
    calc
      ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1
          = ∑ a: ZMod p,
              (χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
                χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)):= by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  have hneg: ZMod.toAddCircle (-a) = -ZMod.toAddCircle a :=
                    map_neg ZMod.toAddCircle a
                  rw [hneg,HurwitzZeta.expZeta,HurwitzZeta.cosZeta_neg,
                    HurwitzZeta.sinZeta_neg]
                  ring
      _ = ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
            ∑ a: ZMod p,
              χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1):= by
            rw [Finset.sum_sub_distrib]
      _ = ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1:= by
            rw [hsum_isin_zero,sub_zero]
  have hboundary :
      ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
        -rp182 p χ:= by
    unfold rp182
    calc
      ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1
          = ∑ a: ZMod p,
              -(χ⁻¹ a *
                ((Real.log ‖(1: ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ)):= by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  rcases eq_or_ne a 0 with rfl | ha
                  · simp [hχinv_zero]
                  · rw [rp292 (p:=p) ha]
                    have hlog :
                        ((Real.log ‖(1: ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ) =
                          ((Real.log
                            (2 * Real.sin (Real.pi * (a.val / p: ℝ))) : ℝ) : ℂ):= by
                      congr 1
                      rw [rp293 (p:=p) ha]
                    rw [hlog]
                    rw [show
                      (((-Real.log (2 * Real.sin (Real.pi * (a.val / p: ℝ))) : ℝ) : ℂ)) =
                        -(((Real.log
                          (2 * Real.sin (Real.pi * (a.val / p: ℝ))) : ℝ) : ℂ)) by simp]
                    exact mul_neg (χ⁻¹ a)
                      (((Real.log (2 * Real.sin (Real.pi * (a.val / p: ℝ))) : ℝ) : ℂ))
      _ = -∑ a: ZMod p,
            χ⁻¹ a * ((Real.log ‖(1: ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ) :=
              Finset.sum_neg_distrib
                (s:=Finset.univ)
                (f:=fun a: ZMod p =>
                  χ⁻¹ a * ((Real.log ‖(1: ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ))
      _ = -rp182 p χ:=rfl
  have hcard_ne: (Fintype.card (ZMod p) : ℂ) ≠ 0:= by
    simpa [ZMod.card] using (show (p: ℂ) ≠ 0 by exact_mod_cast hp.out.ne_zero)
  have hgauss_ne: gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard_ne hχinv_ne_one (ZMod.isPrimitive_stdAddChar p)
  apply (mul_left_cancel₀ hgauss_ne)
  calc
    gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * ZMod.LFunction χ 1
        = ZMod.LFunction (ZMod.dft χinv) 1:=hleft.symm
    _ = ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1:=hdft
    _ = ∑ a: ZMod p,χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1:=hsum_exp
    _ = -rp182 p χ:=hboundary
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * rp183 p χ:= by
          simp [rp183,hgauss_ne,mul_left_comm,mul_comm]
end LValueAtOne
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section LValues
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem rp295 :
    rp90 p (1: ℂ) =
      Finset.prod (rp83 (p:=p)) fun χ => rp181 p χ:= by
  classical
  unfold rp90
  refine Finset.prod_congr rfl fun χ hχ => ?_
  have hχ_odd: χ.Odd:=(Finset.mem_filter.mp hχ).2
  have hχ_ne_one: χ ≠ 1:= by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1: DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  simpa using rp188 (p:=p)
    (hχ_prim:=DirichletCharacter.isPrimitive_of_ne_one (p:=p) hχ_ne_one)
    (hχ_odd:=hχ_odd) (hχ_ne_one:=hχ_ne_one)
theorem rp296 :
    rp89 p (1: ℂ) =
      Finset.prod (rp82 (p:=p)) fun χ => rp183 p χ:= by
  classical
  unfold rp89
  refine Finset.prod_congr rfl fun χ hχ => ?_
  have hχ_mem:=Finset.mem_filter.mp hχ
  have hχ_even: χ.Even:=hχ_mem.2.1
  have hχ_ne_one: χ ≠ 1:=hχ_mem.2.2
  simpa using rp294 (p:=p)
    (hχ_prim:=DirichletCharacter.isPrimitive_of_ne_one (p:=p) hχ_ne_one)
    (hχ_even:=hχ_even) (hχ_ne_one:=hχ_ne_one)
lemma rp297 (hp_odd' : p ≠ 2) :
    (rp83 (p:=p)).card = (p - 1) / 2:= by
  classical
  let E: Finset (DirichletCharacter ℂ p):=Finset.univ.filter fun χ => χ.Even
  let O: Finset (DirichletCharacter ℂ p):=rp83 (p:=p)
  have hdisj: Disjoint E O:= by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even: χ.Even:= by simpa [E] using hχE
    have hχ_odd: χ.Odd:= by simpa [O,rp83] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion: E ∪ O = (Finset.univ: Finset (DirichletCharacter ℂ p)):= by
    ext χ
    simp only [E,O,rp83,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
      true_and,iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hcard_total: E.card + O.card = p - 1:= by
    calc
      E.card + O.card = (E ∪ O).card:= by
        rw [← Finset.card_union_of_disjoint hdisj]
      _ = Nat.card (DirichletCharacter ℂ p):= by
        rw [hunion,Finset.card_univ,Nat.card_eq_fintype_card]
      _ = p - 1:=rp77 (p:=p)
  have hcard_even: E.card = (p - 1) / 2:=rp189 (p:=p) hp_odd'
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨m,hm⟩
  have hhalf: (p - 1) / 2 = m:= by omega
  rw [hhalf] at hcard_even
  have hcard_odd: O.card = m:= by omega
  rw [hhalf]
  simpa [O,rp83] using hcard_odd
theorem rp298
    {χ: DirichletCharacter ℂ p} (hχ_odd: χ.Odd) :
    gaussSum χ (ZMod.stdAddChar (N:=p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) =
      -(p: ℂ):= by
  have hχ_ne_one: χ ≠ 1:= by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1: DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  rw [rp28 (p:=p) (χ:=χ) hχ_ne_one]
  rw [DirichletCharacter.Odd] at hχ_odd
  rw [hχ_odd]
  simp
theorem rp299 (hp_odd' : p ≠ 2) :
    Finset.prod (rp83 (p:=p)) (fun χ =>
      ((((Real.pi: ℝ) : ℂ) * Complex.I) *
        gaussSum χ (ZMod.stdAddChar (N:=p)) / (p: ℂ))) =
      (((((Real.pi: ℝ) : ℂ) * Complex.I) / (p: ℂ)) ^ ((p - 1) / 2)) *
        Finset.prod (rp83 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))):= by
  let C: ℂ:=((((Real.pi: ℝ) : ℂ) * Complex.I) / (p: ℂ))
  have hp_ne: (p: ℂ) ≠ 0:=Nat.cast_ne_zero.mpr hp.out.ne_zero
  calc
    Finset.prod (rp83 (p:=p)) (fun χ =>
        ((((Real.pi: ℝ) : ℂ) * Complex.I) *
          gaussSum χ (ZMod.stdAddChar (N:=p)) / (p: ℂ))) =
      Finset.prod (rp83 (p:=p)) (fun χ =>
        C * gaussSum χ (ZMod.stdAddChar (N:=p))):= by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          dsimp [C]
          field_simp [hp_ne]
    _ =
      (Finset.prod (rp83 (p:=p)) (fun _: DirichletCharacter ℂ p => C)) *
        Finset.prod (rp83 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))):= by
            rw [Finset.prod_mul_distrib]
    _ =
      (C ^ (rp83 (p:=p)).card) *
        Finset.prod (rp83 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))):= by
            rw [Finset.prod_const]
    _ =
      (C ^ ((p - 1) / 2)) *
        Finset.prod (rp83 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))):= by
            rw [rp297 (p:=p) hp_odd']
    _ =
      (((((Real.pi: ℝ) : ℂ) * Complex.I) / (p: ℂ)) ^ ((p - 1) / 2)) *
        Finset.prod (rp83 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))):= by
            rfl
theorem rp300 (hp_odd' : p ≠ 2) :
    ((hPlus K: ℕ) : ℂ) =
      rp150 (K:=K) * rp89 p (1: ℂ) :=
  rp153 (K:=K)
    (KplusResidue:=rp89 p (1: ℂ))
    (rp282 (p:=p) (K:=K) hp_odd')
theorem rp301 (hp_odd' : p ≠ 2) :
    ((hPlus K: ℕ) : ℂ) =
      rp150 (K:=K) *
        Finset.prod (rp82 (p:=p)) (fun χ => rp183 p χ):= by
  calc
    ((hPlus K: ℕ) : ℂ) =
        rp150 (K:=K) * rp89 p (1: ℂ) :=
          rp300 (p:=p) (K:=K) hp_odd'
    _ =
        rp150 (K:=K) *
          Finset.prod (rp82 (p:=p)) (fun χ => rp183 p χ):= by
            rw [rp296 (p:=p)]
theorem rp302 (hp_odd' : p ≠ 2) :
    ((hPlus K: ℕ) : ℂ) =
      rp158 (K:=K) *
        Finset.prod (rp82 (p:=p)) (fun χ => rp183 p χ):= by
  simpa [rp158] using
    (rp301 (p:=p) (K:=K) hp_odd')
theorem rp303 (hp_odd' : p ≠ 2) :
    ((hPlus K: ℕ) : ℂ) =
      rp158 (K:=K) *
        Finset.prod (rp82 (p:=p)) (fun χ => rp183 p χ) :=
  rp302 (p:=p) (K:=K) hp_odd'
theorem rp304 :
    Finset.prod (rp83 (p:=p)) (fun χ => rp181 p χ) =
      Finset.prod (rp83 (p:=p)) (fun χ =>
        ((((Real.pi: ℝ) : ℂ) * Complex.I) *
          gaussSum χ (ZMod.stdAddChar (N:=p)) / (p: ℂ))) *
        Finset.prod (rp83 (p:=p)) (fun χ => rp18 χ⁻¹ 1):= by
  classical
  unfold rp181
  rw [Finset.prod_mul_distrib]
end LValues
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section Assembly
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem rp305
    (hp_odd' : p ≠ 2)
    {coefficient plusFactor: ℂ}
    (hh_formula :
      ((h K: ℕ) : ℂ) =
        ((NumberField.dedekindZeta_residue K: ℝ) : ℂ) * (coefficient * plusFactor))
    (hres :
      ((NumberField.dedekindZeta_residue K: ℝ) : ℂ) =
        Finset.prod (rp82 (p:=p)) (fun χ => rp183 p χ) *
          Finset.prod (rp83 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1))
    (hplus :
      ((hPlus K: ℕ) : ℂ) =
        plusFactor *
          Finset.prod (rp82 (p:=p)) (fun χ => rp183 p χ)) :
    ((hMinus K: ℕ) : ℂ) =
      coefficient *
        Finset.prod (rp83 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1):= by
  let O: ℂ :=
    Finset.prod (rp83 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1)
  have hh: ((h K: ℕ) : ℂ) = ((hPlus K: ℕ) : ℂ) * ((hMinus K: ℕ) : ℂ):= by
    exact_mod_cast (rp75 (p:=p) (hp_odd:=hp_odd') (K:=K))
  have hhplus_ne: ((hPlus K: ℕ) : ℂ) ≠ 0:= by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos: 0 < Fintype.card
      (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
  have hmain: ((hPlus K: ℕ) : ℂ) * ((hMinus K: ℕ) : ℂ) =
      ((hPlus K: ℕ) : ℂ) * (coefficient * O):= by
    rw [← hh,hh_formula,hres,hplus]
    simp [O]
    ring
  exact mul_left_cancel₀ hhplus_ne hmain
end Assembly
end KummerCriterion
end

section
noncomputable section
open NumberField
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section ZetaFactorisation
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem rp306 :
    Filter.Tendsto
      (fun s: ℝ ↦ (s - 1) * (riemannZeta (s: ℂ) * rp88 p (s: ℂ)))
      (𝓝[>] 1)
      (𝓝 (rp88 p (1: ℂ))):= by
  classical
  have h_cont: Continuous (rp88 p) :=
    continuous_finsetProd _ fun χ hχ =>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_erase.mp hχ).1).continuous
  have h_embed :
      Filter.Tendsto (fun s: ℝ ↦ (s: ℂ)) (𝓝[>] (1: ℝ)) (𝓝[≠] (1: ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta: Filter.Tendsto (fun s: ℝ => ((s: ℂ) - 1) * riemannZeta (s: ℂ))
      (𝓝[>] (1: ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod: Filter.Tendsto (fun s: ℝ => rp88 p (s: ℂ))
      (𝓝[>] (1: ℝ)) (𝓝 (rp88 p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod:=h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring
theorem rp307 :
    Filter.Tendsto
      (fun s: ℝ ↦ (s - 1) * NumberField.dedekindZeta K (s: ℂ))
      (𝓝[>] 1)
      (𝓝 (rp88 p (1: ℂ))):= by
  refine (Filter.tendsto_congr' ?_).mp (rp306 p)
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [rp260 p K (by exact_mod_cast hs)]
end ZetaFactorisation
end KummerCriterion
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section Final
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
end Final
end KummerCriterion
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section Teichmuller
variable (p: ℕ) [hp: Fact p.Prime]
lemma rp308: 0 < p - 1 :=
  Nat.sub_pos_of_lt hp.out.one_lt
lemma rp309: p - 1 ≠ 0 :=
  (rp308 (p:=p)).ne'
abbrev rp310:={j: Fin (p - 1) // Odd (j: ℕ)}
omit hp in
theorem rp311 (j: rp310 p) : p ≠ 2:= by
  intro hp_two
  rcases j.2 with ⟨k,hk⟩
  have hj_lt: (j.1: ℕ) < p - 1:=j.1.is_lt
  omega
noncomputable def rp312: (ZMod p)ˣ :=
  (IsCyclic.exists_generator (α:=(ZMod p)ˣ)).choose
theorem rp313 :
    ∀ x: (ZMod p)ˣ,x ∈ Subgroup.zpowers (rp312 p):= by
  simpa [rp312] using
    (IsCyclic.exists_generator (α:=(ZMod p)ˣ)).choose_spec
theorem rp314 :
    orderOf (rp312 p) = p - 1:= by
  rw [orderOf_eq_card_of_forall_mem_zpowers (rp313 (p:=p)),
    Nat.card_eq_fintype_card,ZMod.card_units]
theorem rp315 {m n: ℕ}
    (hm: m < p - 1) (hn: n < p - 1) :
    rp312 p ^ m = rp312 p ^ n ↔ m = n:= by
  constructor
  · intro hmn
    have hmod :
        m ≡ n [MOD orderOf (rp312 p)]:= by
      simpa using (pow_eq_pow_iff_modEq (x:=rp312 p) (n:=m) (m:=n)).mp hmn
    have hmod' : m ≡ n [MOD p - 1]:= by
      simpa [rp314 (p:=p)] using hmod
    have hEq: m % (p - 1) = n:=Nat.mod_eq_of_modEq hmod' hn
    simpa [Nat.mod_eq_of_lt hm] using hEq
  · rintro rfl
    rfl
def rp316 (j: Fin (p - 1)) : ℕ:=(p - 1) - (j: ℕ)
noncomputable def rp317 (m: Fin (p - 1)) : ℚ :=
  ((((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p).val: ℚ)
noncomputable def rp318 (j: Fin (p - 1)) : Polynomial ℚ :=
  ∑ m: Fin (p - 1),
    Polynomial.monomial ((m: ℕ) * rp316 (p:=p) j)
      (rp317 (p:=p) m)
theorem rp319 :
    Function.Bijective fun m: Fin (p - 1) => rp312 p ^ (m: ℕ):= by
  let f: Fin (p - 1) → (ZMod p)ˣ:=fun m => rp312 p ^ (m: ℕ)
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_,?_⟩
  · intro m n hmn
    exact Fin.ext <| (rp315 (p:=p) m.is_lt n.is_lt).mp hmn
  · rw [Fintype.card_fin,ZMod.card_units]
noncomputable def rp320: Fin (p - 1) ≃ (ZMod p)ˣ :=
  Equiv.ofBijective (fun m: Fin (p - 1) => rp312 p ^ (m: ℕ))
    (rp319 (p:=p))
theorem rp321
    {R: Type*} [AddCommMonoid R] (F: ZMod p → R) (hF0: F 0 = 0) :
    ∑ a: ZMod p,F a =
      ∑ m: Fin (p - 1),F (((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p):= by
  have hsplit :
      ∑ a: ZMod p,F a = F 0 + ∑ a: {a: ZMod p // a ≠ 0},F a.1:= by
    simpa using Fintype.sum_eq_add_sum_subtype_ne F (0: ZMod p)
  have hnonzero :
      ∑ a: {a: ZMod p // a ≠ 0},F a.1 =
        ∑ u: (ZMod p)ˣ,F (u: ZMod p):= by
    simpa using
      (Fintype.sum_equiv unitsEquivNeZero
        (fun u: (ZMod p)ˣ => F (u: ZMod p))
        (fun a: {a: ZMod p // a ≠ 0} => F a.1)
        (fun u => rfl)).symm
  have hpowers :
      ∑ u: (ZMod p)ˣ,F (u: ZMod p) =
        ∑ m: Fin (p - 1),F (((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p):= by
    simpa using
      (Fintype.sum_equiv (rp320 (p:=p))
        (fun m: Fin (p - 1) => F (((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p))
        (fun u: (ZMod p)ˣ => F (u: ZMod p))
        (fun m => rfl)).symm
  calc
    ∑ a: ZMod p,F a = F 0 + ∑ a: {a: ZMod p // a ≠ 0},F a.1:=hsplit
    _ = ∑ a: {a: ZMod p // a ≠ 0},F a.1:= by rw [hF0,zero_add]
    _ = ∑ u: (ZMod p)ˣ,F (u: ZMod p):=hnonzero
    _ = ∑ m: Fin (p - 1),
        F (((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p):=hpowers
theorem rp322 {R: Type*} [Field R] [CharZero R] [Algebra ℚ R]
    {χ: DirichletCharacter R p} (hχ_odd: χ.Odd) :
    χ ≠ 1:= by
  rintro rfl
  exact DirichletCharacter.Odd.not_even _ hχ_odd (by
    change (1: DirichletCharacter R p) (-1: ZMod p) = 1
    rw [MulChar.one_apply (isUnit_one.neg)])
theorem rp323 {R: Type*} [Field R] [CharZero R] [Algebra ℚ R]
    {χ: DirichletCharacter R p} (hχ_odd: χ.Odd) :
    (-(1 / 2: R)) * rp18 (χ⁻¹) 1 =
      ((p: R)⁻¹ * (-(1 / 2: R))) *
        ∑ a: ZMod p,(χ⁻¹) a * (a.val: R):= by
  have hpR_ne_zero: (p: R) ≠ 0:=Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hχinv_ne_one: χ⁻¹ ≠ 1:= by
    intro hχinv
    apply rp322 (p:=p) hχ_odd
    simpa using congrArg Inv.inv hχinv
  calc
    (-(1 / 2: R)) * rp18 (χ⁻¹) 1 =
        ((p: R)⁻¹ * (p: R)) * ((-(1 / 2: R)) * rp18 (χ⁻¹) 1):= by
          rw [inv_mul_cancel₀ hpR_ne_zero,one_mul]
    _ = (p: R)⁻¹ * ((-(1 / 2: R)) * ((p: R) * rp18 (χ⁻¹) 1)):= by
          ac_rfl
    _ = (p: R)⁻¹ * ((-(1 / 2: R)) * ∑ a: ZMod p,(χ⁻¹) a * (a.val: R)):= by
          rw [rp20
            (R:=R) (N:=p) (χ:=χ⁻¹) hχinv_ne_one]
    _ = ((p: R)⁻¹ * (-(1 / 2: R))) * ∑ a: ZMod p,(χ⁻¹) a * (a.val: R):= by
          ac_rfl
theorem rp324: IsCyclic (DirichletCharacter ℂ p) :=
  ((rp76 (p:=p)).isCyclic).2 inferInstance
noncomputable def rp325: DirichletCharacter ℂ p:= by
  letI: IsCyclic (DirichletCharacter ℂ p):=rp324 (p:=p)
  exact (IsCyclic.exists_monoid_generator (α:=DirichletCharacter ℂ p)).choose
noncomputable def rp326: ℂ :=
  rp325 p (((rp312 p: (ZMod p)ˣ) : ZMod p))
theorem rp327 :
    ∀ χ: DirichletCharacter ℂ p,χ ∈ Submonoid.powers (rp325 p):= by
  have: IsCyclic (DirichletCharacter ℂ p):=rp324 (p:=p)
  simpa [rp325] using
    (IsCyclic.exists_monoid_generator (α:=DirichletCharacter ℂ p)).choose_spec
theorem rp328 :
    orderOf (rp325 p) = p - 1:= by
  calc
    orderOf (rp325 p) = Nat.card (DirichletCharacter ℂ p) :=
      orderOf_eq_card_of_forall_mem_powers (rp327 (p:=p))
    _ = p - 1:=rp77 (p:=p)
theorem rp329 (m: ℕ) :
    rp325 p (((rp312 p) ^ m: (ZMod p)ˣ) : ZMod p) =
      rp326 p ^ m:= by
  change rp325 p ((((rp312 p: (ZMod p)ˣ) : ZMod p) ^ m)) =
    rp326 p ^ m
  rw [map_pow]
  rfl
theorem rp330 {l: ℕ}
    (hl: rp326 p ^ l = 1) :
    (rp325 p) ^ l = 1:= by
  apply (MulChar.eq_one_iff).2
  intro a
  let m: Fin (p - 1):=(rp320 (p:=p)).symm a
  have hm: ((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) = a :=
    (rp320 (p:=p)).apply_symm_apply a
  rw [← hm,MulChar.pow_apply_coe,rp329]
  rw [← pow_mul,Nat.mul_comm,pow_mul,hl,one_pow]
theorem rp331 :
    IsPrimitiveRoot (rp326 p) (p - 1):= by
  refine ⟨?_,fun l hl => ?_⟩
  · calc
      rp326 p ^ (p - 1) =
          rp325 p
            ((((rp312 p) ^ (p - 1) : (ZMod p)ˣ) : ZMod p)):= by
            symm
            exact rp329 (p:=p) (p - 1)
      _ = rp325 p (1: ZMod p):= by
            rw [show (rp312 p) ^ (p - 1) = (1: (ZMod p)ˣ) by
              rw [← rp314 (p:=p),pow_orderOf_eq_one]]
            simp
      _ = 1:= by
            simp
  · have hpow: (rp325 p) ^ l = 1 :=
      rp330 (p:=p) hl
    have hdiv: orderOf (rp325 p) ∣ l :=
      (orderOf_dvd_iff_pow_eq_one (x:=rp325 p)).2 hpow
    simpa [rp328 (p:=p)] using hdiv
theorem rp332 (j: Fin (p - 1)) :
    (((rp325 p) ^ (j: ℕ))⁻¹: DirichletCharacter ℂ p) =
      (rp325 p) ^ rp316 (p:=p) j:= by
  apply inv_eq_of_mul_eq_one_right
  have hj: (j: ℕ) + rp316 (p:=p) j = p - 1:= by
    dsimp [rp316]
    exact Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)
  rw [← pow_add,hj,← rp328 (p:=p),pow_orderOf_eq_one]
theorem rp333 {i j: ℕ}
    (hi: i < p - 1) (hj: j < p - 1) :
    (rp325 p) ^ i = (rp325 p) ^ j ↔ i = j:= by
  constructor
  · intro hij
    have hmod :
        i ≡ j [MOD orderOf (rp325 p)]:= by
      simpa using (pow_eq_pow_iff_modEq (x:=rp325 p) (n:=i) (m:=j)).mp hij
    have hmod' : i ≡ j [MOD p - 1]:= by
      simpa [rp328 (p:=p)] using hmod
    have hEq: i % (p - 1) = j:=Nat.mod_eq_of_modEq hmod' hj
    simpa [Nat.mod_eq_of_lt hi] using hEq
  · rintro rfl
    rfl
theorem rp334 (hp_odd' : p ≠ 2) :
    ∃ χ: DirichletCharacter ℂ p,χ.Odd:= by
  classical
  have hcard_pos: 0 < (rp83 (p:=p)).card:= by
    rw [rp297 (p:=p) hp_odd']
    have hp_gt_two: 2 < p:=lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')
    omega
  obtain ⟨χ,hχ⟩:=Finset.card_pos.mp hcard_pos
  exact ⟨χ,(Finset.mem_filter.mp hχ).2⟩
theorem rp335 (hp_odd' : p ≠ 2) :
    (rp325 p).Odd:= by
  rcases DirichletCharacter.even_or_odd (rp325 p) with h_even | h_odd
  · exfalso
    obtain ⟨χ,hχ_odd⟩:=rp334 (p:=p) hp_odd'
    rcases (Submonoid.mem_powers_iff χ (rp325 p)).mp
      (rp327 (p:=p) χ) with ⟨n,rfl⟩
    have hpow_even: ((rp325 p) ^ n).Even:= by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · change (1: DirichletCharacter ℂ p) (-1: ZMod p) = 1
        simpa using (MulChar.one_apply (R:=ZMod p) (R':=ℂ) isUnit_one.neg)
      · change ((rp325 p) ^ n) (-1: ZMod p) = 1
        rw [MulChar.pow_apply' _ hn.ne',h_even,one_pow]
    exact DirichletCharacter.Odd.not_even _ hχ_odd hpow_even
  · exact h_odd
theorem rp336 (hp_odd' : p ≠ 2) (i: ℕ) :
    ((rp325 p) ^ i) (-1: ZMod p) = (-1: ℂ) ^ i:= by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using (MulChar.one_apply (R:=ZMod p) (R':=ℂ) isUnit_one.neg)
  · rw [MulChar.pow_apply' _ hi.ne',rp335 (p:=p) hp_odd']
theorem rp337 (hp_odd' : p ≠ 2) (i: ℕ) :
    ((rp325 p) ^ i).Odd ↔ Odd i:= by
  change ((rp325 p) ^ i) (-1: ZMod p) = (-1: ℂ) ↔ Odd i
  rw [rp336 (p:=p) hp_odd' i]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num: (-1: ℂ) ≠ 1)
noncomputable def rp338: Finset (DirichletCharacter ℂ p):= by
  classical
  exact (Finset.univ: Finset (rp310 p)).image
    (fun j => (rp325 p) ^ (j.1: ℕ))
theorem rp339 (hp_odd' : p ≠ 2) :
    rp83 (p:=p) = rp338 (p:=p):= by
  classical
  ext χ
  constructor
  · intro hχ
    have hχ_odd: χ.Odd:=(Finset.mem_filter.mp hχ).2
    rcases (Submonoid.mem_powers_iff χ (rp325 p)).mp
      (rp327 (p:=p) χ) with ⟨j,hj⟩
    let k: Fin (p - 1):=⟨j % (p - 1),Nat.mod_lt j (rp308 (p:=p))⟩
    have hk_eq: (rp325 p) ^ (k: ℕ) = χ:= by
      dsimp [k]
      calc
        (rp325 p) ^ (j % (p - 1)) =
            (rp325 p) ^ (j % orderOf (rp325 p)):= by
              rw [rp328 (p:=p)]
        _ = (rp325 p) ^ j:= by rw [pow_mod_orderOf]
        _ = χ:=hj
    have hk_odd: Odd (k: ℕ):= by
      have hk_odd' : ((rp325 p) ^ (k: ℕ)).Odd:= by
        simpa [hk_eq] using hχ_odd
      exact (rp337 (p:=p) hp_odd' (k: ℕ)).1 hk_odd'
    refine Finset.mem_image.mpr ⟨⟨k,hk_odd⟩,Finset.mem_univ _,?_⟩
    simpa using hk_eq
  · intro hχ
    unfold rp338 at hχ
    rcases Finset.mem_image.mp hχ with ⟨j,-,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      exact (rp337 (p:=p) hp_odd' (j.1: ℕ)).2 j.2⟩
theorem rp340 (hp_odd' : p ≠ 2)
    {α: Type*} [CommMonoid α] (F: DirichletCharacter ℂ p → α) :
    Finset.prod (rp83 (p:=p)) F =
      Finset.prod (Finset.univ: Finset (rp310 p))
        (fun j => F ((rp325 p) ^ (j.1: ℕ))):= by
  classical
  rw [rp339 (p:=p) hp_odd']
  unfold rp338
  exact Finset.prod_image fun a _ b _ hab =>
    Subtype.ext <| Fin.ext <|
      (rp333 (p:=p) a.1.is_lt b.1.is_lt).mp hab
theorem rp341 (j: Fin (p - 1)) :
    ∑ a: ZMod p,((((rp325 p) ^ (j: ℕ))⁻¹) a) * (a.val: ℂ) =
      Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
        (rp318 (p:=p) j):= by
  have hEval :
      Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
        (rp318 (p:=p) j) =
          ∑ m: Fin (p - 1),
            Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
              (Polynomial.monomial ((m: ℕ) * rp316 (p:=p) j)
                (rp317 (p:=p) m)):= by
    simpa [rp318] using
      (Polynomial.eval₂_finsetSum (f:=algebraMap ℚ ℂ) (s:=Finset.univ)
        (g:=fun m: Fin (p - 1) =>
          Polynomial.monomial ((m: ℕ) * rp316 (p:=p) j)
            (rp317 (p:=p) m))
        (x:=rp326 p))
  rw [rp321 (p:=p)
    (F:=fun a => ((((rp325 p) ^ (j: ℕ))⁻¹) a) * (a.val: ℂ))
    (hF0:= by simp),hEval]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hcoeff :
      algebraMap ℚ ℂ (rp317 (p:=p) m) =
        (((((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p).val: ℂ)):= by
    rw [rp317]
    exact map_ratCast (algebraMap ℚ ℂ)
      (((((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p).val: ℚ))
  rw [Polynomial.eval₂_monomial,rp332 (p:=p) j,
    MulChar.pow_apply_coe,rp329]
  rw [hcoeff,pow_mul]
  ac_rfl
theorem rp342 (j: rp310 p) :
    (-(1 / 2: ℂ)) * rp18 (((rp325 p) ^ (j.1: ℕ))⁻¹) 1 =
      ((p: ℂ)⁻¹ * (-(1 / 2: ℂ))) *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
          (rp318 (p:=p) j.1):= by
  rw [rp323 (p:=p)
    (χ:=(rp325 p) ^ (j.1: ℕ))
    ((rp337 (p:=p) (rp311 (p:=p) j)
      (j.1: ℕ)).2 j.2)]
  rw [rp341 (p:=p) j.1]
lemma rp343 :
    Monoid.exponent (ZMod p)ˣ = p - 1:= by
  rw [IsCyclic.exponent_eq_card,Nat.card_eq_fintype_card,ZMod.card_units]
theorem rp344 :
    HasEnoughRootsOfUnity ℚ_[p] (p - 1):= by
  have: NeZero (p - 1):=⟨rp309 (p:=p)⟩
  apply HasEnoughRootsOfUnity.of_card_le (R:=ℚ_[p])
  refine le_of_eq ?_
  rw [eq_comm,card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
  obtain ⟨g,hg_gen⟩:=IsCyclic.exists_generator (α:=(ZMod p)ˣ)
  refine ⟨((rp1 p (g: ZMod p) : ℤ_[p]) : ℚ_[p]),?_⟩
  exact (rp11 (p:=p) hg_gen).map_of_injective
    (f:=PadicInt.Coe.ringHom) (hf:=fun _ _ h => Subtype.coe_injective h)
theorem rp345 :
    Nat.card (DirichletCharacter ℚ_[p] p) = p - 1:= by
  have: HasEnoughRootsOfUnity ℚ_[p] (Monoid.exponent (ZMod p)ˣ):= by
    simpa [rp343 (p:=p)] using
      rp344 (p:=p)
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,Nat.totient_prime hp.out]
noncomputable def rp346: ℚ_[p] :=
  (((rp1 p (((rp312 p: (ZMod p)ˣ) : ZMod p)) : ℤ_[p])) : ℚ_[p])
theorem rp347 :
    IsPrimitiveRoot (rp346 p) (p - 1) :=
  (rp11 (p:=p) (g:=rp312 p)
    (rp313 (p:=p))).map_of_injective
    (f:=PadicInt.Coe.ringHom) (hf:=fun _ _ h => Subtype.coe_injective h)
theorem rp348 (m: ℕ) :
    rp21 p (((rp312 p) ^ m: (ZMod p)ˣ) : ZMod p) =
      rp346 p ^ m:= by
  change rp21 p ((((rp312 p: (ZMod p)ˣ) : ZMod p) ^ m)) =
    rp346 p ^ m
  rw [rp21,MulChar.ringHomComp_apply,rp10,map_pow]
  rfl
theorem rp349 (j: Fin (p - 1)) :
    (((rp21 p) ^ (j: ℕ))⁻¹: DirichletCharacter ℚ_[p] p) =
      (rp21 p) ^ rp316 (p:=p) j:= by
  apply inv_eq_of_mul_eq_one_right
  have hj: (j: ℕ) + rp316 (p:=p) j = p - 1:= by
    dsimp [rp316]
    exact Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)
  rw [← pow_add,hj,← rp24 (p:=p),pow_orderOf_eq_one]
theorem rp350 {i j: ℕ}
    (hi: i < p - 1) (hj: j < p - 1) :
    (rp21 p) ^ i = (rp21 p) ^ j ↔ i = j:= by
  constructor
  · intro hij
    have hmod :
        i ≡ j [MOD orderOf (rp21 p)]:= by
      simpa using (pow_eq_pow_iff_modEq (x:=rp21 p) (n:=i) (m:=j)).mp hij
    have hmod' : i ≡ j [MOD p - 1]:= by
      simpa [rp24 (p:=p)] using hmod
    have hEq: i % (p - 1) = j:=Nat.mod_eq_of_modEq hmod' hj
    simpa [Nat.mod_eq_of_lt hi] using hEq
  · rintro rfl
    rfl
theorem rp351 :
    Function.Bijective fun j: Fin (p - 1) => (rp21 p) ^ (j: ℕ):= by
  let f: Fin (p - 1) → DirichletCharacter ℚ_[p] p:=fun j => (rp21 p) ^ (j: ℕ)
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_,?_⟩
  · intro i j hij
    exact Fin.ext <| (rp350 (p:=p) i.is_lt j.is_lt).mp hij
  · rw [Fintype.card_fin,← Nat.card_eq_fintype_card,rp345 (p:=p)]
theorem rp352 (hp_odd' : p ≠ 2) (i: ℕ) :
    ((rp21 p) ^ i) (-1: ZMod p) = (-1: ℚ_[p]) ^ i:= by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using (MulChar.one_apply (R:=ZMod p) (R':=ℚ_[p]) isUnit_one.neg)
  · rw [rp22 (p:=p) (n:=i),MulChar.ringHomComp_apply,
      rp15 (p:=p) hp_odd' i,map_pow]
    rfl
theorem rp353 (hp_odd' : p ≠ 2) (i: ℕ) :
    ((rp21 p) ^ i).Odd ↔ Odd i:= by
  change ((rp21 p) ^ i) (-1: ZMod p) = (-1: ℚ_[p]) ↔ Odd i
  rw [rp352 (p:=p) hp_odd' i]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num: (-1: ℚ_[p]) ≠ 1)
noncomputable def rp354: Finset ℕ :=
  (Finset.range (p - 1)).filter fun j => Odd j
noncomputable def rp355: Finset (DirichletCharacter ℚ_[p] p):= by
  classical
  exact Finset.univ.filter fun χ => χ.Odd
noncomputable def rp356: Finset (DirichletCharacter ℚ_[p] p):= by
  classical
  exact (rp354 (p:=p)).image fun j => (rp21 p) ^ j
theorem rp357 (hp_odd' : p ≠ 2) :
    rp355 (p:=p) =
      rp356 (p:=p):= by
  classical
  ext χ
  constructor
  · intro hχ
    have hχ_odd: χ.Odd:= by
      simpa [rp355] using hχ
    rcases (rp351 (p:=p)).surjective χ with ⟨j,hj⟩
    have hj_odd: Odd (j: ℕ):= by
      have hj' : ((rp21 p) ^ (j: ℕ)).Odd:= by simpa [hj] using hχ_odd
      exact (rp353 (p:=p) hp_odd' (j: ℕ)).1 hj'
    refine Finset.mem_image.mpr ⟨(j: ℕ),?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.is_lt,hj_odd⟩
    · simpa using hj
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j,hj,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      exact (rp353 (p:=p) hp_odd' j).2
        ((Finset.mem_filter.mp hj).2)⟩
noncomputable def rp358: Finset (DirichletCharacter ℚ_[p] p):= by
  classical
  exact (Finset.univ: Finset (rp310 p)).image
    (fun j => (rp21 p) ^ (j.1: ℕ))
theorem rp359 (hp_odd' : p ≠ 2) :
    rp355 (p:=p) = rp358 (p:=p):= by
  classical
  rw [rp357 (p:=p) hp_odd']
  unfold rp356 rp358
  ext χ
  constructor
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j,hj,rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨⟨j,Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩,
      (Finset.mem_filter.mp hj).2⟩,Finset.mem_univ _,?_⟩
    rfl
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j,-,rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(j.1: ℕ),Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr j.1.is_lt,j.2⟩,?_⟩
    rfl
theorem rp360 (hp_odd' : p ≠ 2)
    {α: Type*} [CommMonoid α] (F: DirichletCharacter ℚ_[p] p → α) :
    Finset.prod (rp355 (p:=p)) F =
      Finset.prod (Finset.univ: Finset (rp310 p))
        (fun j => F ((rp21 p) ^ (j.1: ℕ))):= by
  classical
  rw [rp359 (p:=p) hp_odd']
  unfold rp358
  exact Finset.prod_image fun a _ b _ hab =>
    Subtype.ext <| Fin.ext <|
      (rp350 (p:=p) a.1.is_lt b.1.is_lt).mp hab
theorem rp361 (j: Fin (p - 1)) :
    ∑ a: ZMod p,((((rp21 p) ^ (j: ℕ))⁻¹) a) * (a.val: ℚ_[p]) =
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
        (rp318 (p:=p) j):= by
  have hEval :
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
        (rp318 (p:=p) j) =
          ∑ m: Fin (p - 1),
            Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
              (Polynomial.monomial ((m: ℕ) * rp316 (p:=p) j)
                (rp317 (p:=p) m)):= by
    simpa [rp318] using
      (Polynomial.eval₂_finsetSum (f:=algebraMap ℚ ℚ_[p]) (s:=Finset.univ)
        (g:=fun m: Fin (p - 1) =>
          Polynomial.monomial ((m: ℕ) * rp316 (p:=p) j)
            (rp317 (p:=p) m))
        (x:=rp346 p))
  rw [rp321 (p:=p)
    (F:=fun a => ((((rp21 p) ^ (j: ℕ))⁻¹) a) * (a.val: ℚ_[p]))
    (hF0:= by simp),hEval]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hcoeff :
      algebraMap ℚ ℚ_[p] (rp317 (p:=p) m) =
        (((((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p).val: ℚ_[p])):= by
    rw [rp317]
    exact map_ratCast (algebraMap ℚ ℚ_[p])
      (((((rp312 p) ^ (m: ℕ) : (ZMod p)ˣ) : ZMod p).val: ℚ))
  rw [Polynomial.eval₂_monomial,rp349 (p:=p) j,
    MulChar.pow_apply_coe,rp348]
  rw [hcoeff,pow_mul]
  ac_rfl
theorem rp362 (j: rp310 p) :
    (-(1 / 2: ℚ_[p])) * rp18 (((rp21 p) ^ (j.1: ℕ))⁻¹) 1 =
      ((p: ℚ_[p])⁻¹ * (-(1 / 2: ℚ_[p]))) *
        Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
          (rp318 (p:=p) j.1):= by
  rw [rp323 (p:=p)
    (χ:=(rp21 p) ^ (j.1: ℕ))
    ((rp353 (p:=p) (rp311 (p:=p) j)
      (j.1: ℕ)).2 j.2)]
  rw [rp361 (p:=p) j.1]
theorem rp363 (j: rp310 p) :
    ((-(1 / 2: ℂ)) * rp18 (((rp325 p) ^ (j.1: ℕ))⁻¹) 1 =
        ((p: ℂ)⁻¹ * (-(1 / 2: ℂ))) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
            (rp318 (p:=p) j.1))
      ∧
    ((-(1 / 2: ℚ_[p])) * rp18 (((rp21 p) ^ (j.1: ℕ))⁻¹) 1 =
        ((p: ℚ_[p])⁻¹ * (-(1 / 2: ℚ_[p]))) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
            (rp318 (p:=p) j.1)) :=
  ⟨rp342 (p:=p) j,
    rp362 (p:=p) j⟩
theorem rp364 :
    ((Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
        (-(1 / 2: ℂ)) * rp18 (((rp325 p) ^ (j.1: ℕ))⁻¹) 1) =
      Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
        ((p: ℂ)⁻¹ * (-(1 / 2: ℂ))) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
            (rp318 (p:=p) j.1))
      ∧
    ((Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
        (-(1 / 2: ℚ_[p])) * rp18 (((rp21 p) ^ (j.1: ℕ))⁻¹) 1) =
      Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
        ((p: ℚ_[p])⁻¹ * (-(1 / 2: ℚ_[p]))) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
            (rp318 (p:=p) j.1)):= by
  constructor
  · refine Finset.prod_congr rfl ?_
    intro j hj
    exact (rp363 (p:=p) j).1
  · refine Finset.prod_congr rfl ?_
    intro j hj
    exact (rp363 (p:=p) j).2
noncomputable def rp365: Polynomial ℚ :=
  Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
    Polynomial.C (((p: ℚ)⁻¹) * (-(1 / 2: ℚ))) *
      rp318 (p:=p) j.1
theorem rp366
    {R: Type*} [Field R] [CharZero R] [Algebra ℚ R] (x: R) :
    Polynomial.eval₂ (algebraMap ℚ R) x (rp365 (p:=p)) =
      Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
        ((p: R)⁻¹ * (-(1 / 2: R))) *
          Polynomial.eval₂ (algebraMap ℚ R) x (rp318 (p:=p) j.1):= by
  change (Polynomial.eval₂RingHom (algebraMap ℚ R) x) (rp365 (p:=p)) = _
  rw [rp365,map_prod]
  refine Finset.prod_congr rfl ?_
  intro j hj
  change Polynomial.eval₂ (algebraMap ℚ R) x
      (Polynomial.C (((p: ℚ)⁻¹) * (-(1 / 2: ℚ))) *
        rp318 (p:=p) j.1) = _
  rw [Polynomial.eval₂_mul,Polynomial.eval₂_C]
  congr 1
  simp
theorem rp367 :
    Finset.prod (Finset.univ: Finset (rp310 p)) (fun j =>
      (-(1 / 2: ℂ)) * rp18 (((rp325 p) ^ (j.1: ℕ))⁻¹) 1) =
        Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
          (rp365 (p:=p)):= by
  rw [(rp364 (p:=p)).1,
    rp366 (p:=p) (R:=ℂ) (x:=rp326 p)]
theorem rp368 :
    Finset.prod (Finset.univ: Finset (rp310 p)) (fun j =>
      (-(1 / 2: ℚ_[p])) * rp18 (((rp21 p) ^ (j.1: ℕ))⁻¹) 1) =
        Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
          (rp365 (p:=p)):= by
  rw [(rp364 (p:=p)).2,
    rp366 (p:=p) (R:=ℚ_[p]) (x:=rp346 p)]
end Teichmuller
section FinalTeichmuller
variable (p: ℕ) [hp: Fact p.Prime]
  (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
end FinalTeichmuller
end KummerCriterion
end

section
open NumberField KummerCriterion
namespace SignFree
variable (p: ℕ) [hp: Fact p.Prime]
lemma rp369 (ho: p ≠ 2) :
    (∏ χ ∈ rp83 (p:=p),gaussSum χ (ZMod.stdAddChar (N:=p))) ^ 2 = (-(p: ℂ)) ^ ((p-1)/2):= by
  classical
  let g:=fun χ: DirichletCharacter ℂ p => gaussSum χ (ZMod.stdAddChar (N:=p))
  change (∏ χ ∈ rp83 (p:=p),g χ)^2 = _
  have hinv: (∏ χ ∈ rp83 (p:=p),g χ⁻¹) = ∏ χ ∈ rp83 (p:=p),g χ:= by
    exact Finset.prod_bij (fun χ _ => χ⁻¹) (fun _ => rp84 (p:=p)) (fun _ _ _ _ h => inv_injective h) (fun χ h => ⟨χ⁻¹,rp84 (p:=p) h,inv_inv χ⟩) (fun _ _ => rfl)
  rw [pow_two]
  nth_rw 2 [← hinv]
  rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ _χ ∈ rp83 (p:=p),(-(p: ℂ)):= by
      apply Finset.prod_congr rfl; intro χ hχ
      exact rp298 (p:=p) (Finset.mem_filter.mp hχ).2
    _ = _:= by rw [Finset.prod_const,rp297 (p:=p) ho]
variable (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem coeffSq (hp_odd' : p ≠ 2) :
    (rp155 (p:=p) (K:=K) *
      Finset.prod (rp83 (p:=p)) (fun χ =>
        ((((Real.pi: ℝ) : ℂ) * Complex.I) *
          gaussSum χ (ZMod.stdAddChar (N:=p)) / (p: ℂ)))) ^ 2 =
    (    (2 * p: ℂ) *
      Finset.prod (rp83 (p:=p))
        (fun _: DirichletCharacter ℂ p => (-(1 / 2: ℂ)))) ^ 2:=by
  let n: ℕ:=(p - 1) / 2
  let S: ℂ:=(((Real.sqrt ((p: ℝ) ^ n) : ℝ) : ℂ))
  let G: ℂ :=
    Finset.prod (rp83 (p:=p))
      (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p)))
  have hp_pos: 0 < (p: ℝ):= by
    exact_mod_cast hp.out.pos
  have hp_ne: (p: ℂ) ≠ 0:= by
    exact_mod_cast hp.out.ne_zero
  have hI_ne: Complex.I ^ n ≠ 0 :=
    pow_ne_zero _ Complex.I_ne_zero
  have hS_ne: S ≠ 0:= by
    dsimp [S]
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 <| pow_pos hp_pos _)
  have h2p_ne: (2 * p: ℂ) ≠ 0:= by
    exact_mod_cast Nat.mul_ne_zero two_ne_zero hp.out.ne_zero
  have hpi_ne: (((Real.pi: ℝ) : ℂ)) ≠ 0:= by
    exact_mod_cast Real.pi_ne_zero
  have htwo_pow_ne: ((2: ℂ) ^ n) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hpow_pi_ne: ((((2 * Real.pi) ^ n: ℝ) : ℂ)) ≠ 0:= by
    exact_mod_cast pow_ne_zero n (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hpow_nonneg: 0 ≤ (p: ℝ) ^ n:= by
    positivity
  have hS_sq: S ^ 2 = (p: ℂ) ^ n:= by
    dsimp [S]
    calc
      ((((Real.sqrt ((p: ℝ) ^ n) : ℝ) : ℂ)) ^ 2)
          = ((((p: ℝ) ^ n: ℝ) : ℂ)):= by
              rw [pow_two,← Complex.ofReal_mul]
              simp [hpow_nonneg]
      _ = (p: ℂ) ^ n:= by
              norm_num
  have hneg_half_pow: (-(1 / 2: ℂ)) ^ n = ((-1: ℂ) ^ n) / (2: ℂ) ^ n:= by
    rw [show (-(1 / 2: ℂ)) = (-1: ℂ) / 2 by norm_num,div_pow]
  have hscalar :
      ((((((2 * p: ℕ) : ℝ) * Real.sqrt ((p: ℝ) ^ n)) /
            (2 * Real.pi) ^ n: ℝ) : ℂ) *
          (((((Real.pi: ℝ) : ℂ) * Complex.I) / (p: ℂ)) ^ n)) =
        (((2 * p: ℂ) * (Complex.I ^ n)) / (((2: ℂ) ^ n) * S)):= by
    have hpi_pow_ne: (((Real.pi: ℝ) : ℂ) ^ n) ≠ 0 :=
      pow_ne_zero _ hpi_ne
    have hp_pow_ne: (p: ℂ) ^ n ≠ 0 :=
      pow_ne_zero _ hp_ne
    rw [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,div_pow,mul_pow]
    rw [show (((2 * Real.pi: ℝ) : ℂ)) =
        (2: ℂ) * (((Real.pi: ℝ) : ℂ)) by norm_num,mul_pow]
    rw [← hS_sq]
    field_simp [hS_ne,hp_pow_ne,hpi_pow_ne,htwo_pow_ne]
    simp [S,mul_assoc,mul_comm]
  rw [rp299 (p:=p) hp_odd',rp157 (p:=p) (K:=K) hp_odd',Finset.prod_const,rp297 (p:=p) hp_odd']
  change (_ * (_ * G))^2 = ((2*p: ℂ) * (-(1/2: ℂ))^n)^2
  rw [← mul_assoc,hscalar,mul_pow,show G ^ 2 = (-(p: ℂ))^n from rp369 p hp_odd',hneg_half_pow]
  have hI: (Complex.I ^ n)^2 = (-1: ℂ)^n:= by rw [← pow_mul,Nat.mul_comm,pow_mul,Complex.I_sq]
  rw [div_pow,mul_pow,mul_pow,hI,mul_pow,hS_sq,neg_eq_neg_one_mul (p: ℂ),mul_pow]
  field_simp
theorem rp370 (hp_odd' : p ≠ 2) :
    ((hMinus K: ℕ) : ℂ)^2 = (
      (2 * p: ℂ) *
        Finset.prod (rp83 (p:=p)) (fun χ =>
          (-(1 / 2: ℂ)) * rp18 χ⁻¹ 1))^2:= by
  have hL: ((hMinus K: ℕ) : ℂ) = rp155 (p:=p) (K:=K) * ∏ χ ∈ rp83 p,DirichletCharacter.LFunction χ 1:= by
    apply rp305 (p:=p) (K:=K) hp_odd' (plusFactor:=rp158 (K:=K))
    · calc
        ((h K: ℕ) : ℂ) =
            ((NumberField.dedekindZeta_residue K: ℝ) : ℂ) *
              rp148 (p:=p) (K:=K) :=
              rp149 (p:=p) (K:=K) hp_odd'
        _ = ((NumberField.dedekindZeta_residue K: ℝ) : ℂ) *
              (rp155 (p:=p) (K:=K) *
                rp158 (K:=K)):= by
              rw [rp159
                (p:=p) (K:=K)]
    · calc
        ((NumberField.dedekindZeta_residue K: ℝ) : ℂ) =
            rp88 p (1: ℂ) :=
              tendsto_nhds_unique
                (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
                (rp307 p K)
        _ = rp89 p (1: ℂ) * rp90 p (1: ℂ):= by
              rw [rp259]
        _ =
            Finset.prod (rp82 (p:=p)) (fun χ => rp183 p χ) *
              Finset.prod (rp83 (p:=p))
                (fun χ => DirichletCharacter.LFunction χ 1):= by
              rw [rp296 (p:=p)]
              rfl
    · exact rp303 (p:=p) (K:=K) hp_odd'
  have hodd:=rp295 (p:=p)
  change (∏ χ ∈ rp83 p,DirichletCharacter.LFunction χ 1) = _ at hodd
  rw [hL,hodd,rp304,Finset.prod_mul_distrib,← mul_assoc,← mul_assoc,mul_pow,coeffSq p K hp_odd',← mul_pow]
end SignFree
end

section
open NumberField KummerCriterion
namespace SignFree
variable (p: ℕ) [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem rp371 (hp_odd' : p ≠ 2) :
    ((hMinus K: ℕ) : ℂ)^2 =
      ((2 * p: ℂ) *
        Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
          (-(1 / 2: ℂ)) *
            rp18 (((rp325 p) ^ (j.1: ℕ))⁻¹) 1)^2:= by
  rw [rp370 (p:=p) (K:=K) hp_odd']
  rw [rp340 (p:=p) hp_odd'
    (fun χ => (-(1 / 2: ℂ)) * rp18 (χ⁻¹) 1)]
theorem rp372 (hp_odd' : p ≠ 2) :
    ((hMinus K: ℕ) : ℚ_[p])^2 =
      ((2 * p: ℚ_[p]) *
        Finset.prod (Finset.univ: Finset (rp310 p)) fun j =>
          (-(1 / 2: ℚ_[p])) * rp18 (((rp21 p) ^ (j.1: ℕ))⁻¹) 1)^2:= by
  let Q: Polynomial ℚ :=
    (Polynomial.C (2 * p: ℚ) * rp365 (p:=p))^2 -
      (Polynomial.C ((hMinus K: ℕ) : ℚ))^2
  have hcomplex :
      ((hMinus K: ℕ) : ℂ)^2 =
        ((2 * p: ℂ) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (rp326 p)
            (rp365 (p:=p)))^2:= by
    rw [rp371 (p:=p) (K:=K) hp_odd',
      rp367 (p:=p)]
  have hQ_complex: Polynomial.aeval (rp326 p) Q = 0:= by
    rw [Polynomial.aeval_def,Polynomial.eval₂_sub,Polynomial.eval₂_pow,Polynomial.eval₂_pow,Polynomial.eval₂_mul,Polynomial.eval₂_C]
    simpa only [eq_ratCast,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,map_natCast,
      Polynomial.eval₂_natCast] using sub_eq_zero.mpr hcomplex.symm
  have hdvd: Polynomial.cyclotomic (p - 1) ℚ ∣ Q:= by
    rw [Polynomial.cyclotomic_eq_minpoly_rat
      (rp331 (p:=p)) (rp308 (p:=p))]
    exact minpoly.dvd ℚ (rp326 p) hQ_complex
  have hcycl_qpadic :
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
        (Polynomial.cyclotomic (p - 1) ℚ) = 0:= by
    simpa [Polynomial.eval₂_eq_eval_map,Polynomial.map_cyclotomic,Polynomial.IsRoot.def] using
      (rp347 (p:=p)).isRoot_cyclotomic
      (rp308 (p:=p))
  have hQ_qpadic :
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p) Q = 0 :=
    Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
      (f:=algebraMap ℚ ℚ_[p]) (x:=rp346 p) hdvd hcycl_qpadic
  have hq :
      ((2 * p: ℚ_[p]) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
            (rp365 (p:=p)))^2 -
        ((hMinus K: ℕ) : ℚ_[p])^2 = 0:= by
    simpa [Q,Polynomial.eval₂_sub,Polynomial.eval₂_pow,Polynomial.eval₂_mul,Polynomial.eval₂_C] using hQ_qpadic
  calc
    ((hMinus K: ℕ) : ℚ_[p])^2 =
        ((2 * p: ℚ_[p]) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (rp346 p)
            (rp365 (p:=p)))^2 :=
          (sub_eq_zero.mp hq).symm
    _ = ((2 * p: ℚ_[p]) *
        Finset.prod (Finset.univ: Finset (rp310 p)) (fun j =>
          (-(1 / 2: ℚ_[p])) * rp18 (((rp21 p) ^ (j.1: ℕ))⁻¹) 1))^2:= by
          rw [← rp368 (p:=p)]
theorem rp373 (hp_odd' : p ≠ 2) :
    ((hMinus K: ℕ) : ℚ_[p])^2 =
      ((2 * p: ℚ_[p]) *
        Finset.prod (rp355 (p:=p)) fun χ =>
          (-(1 / 2: ℚ_[p])) * rp18 χ⁻¹ 1)^2:= by
  rw [rp372 (p:=p) (K:=K) hp_odd']
  rw [← rp360 (p:=p) hp_odd'
    (fun χ => (-(1 / 2: ℚ_[p])) * rp18 χ⁻¹ 1)]
theorem rp374 (hp_odd' : p ≠ 2) :
    ((hMinus K: ℕ) : ℚ_[p])^2 =
      ((2 * p: ℚ_[p]) *
        Finset.prod (rp354 (p:=p)) fun j =>
          (-(1 / 2: ℚ_[p])) * rp18 (((rp21 p) ^ j)⁻¹) 1)^2:= by
  classical
  rw [rp373 (p:=p) (K:=K) hp_odd']
  rw [rp357 (p:=p) hp_odd']
  unfold rp356
  rw [Finset.prod_image]
  · intro a ha b hb hab
    exact (rp350 (p:=p)
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)).mp hab
theorem rp375 (hp_odd' : p ≠ 2) :
    ((hMinus K: ℕ) : ℚ_[p])^2 =
      ((2 * p: ℚ_[p]) *
        Finset.prod ((Finset.range (p - 1)).filter fun j => Odd j) fun j =>
          (-(1 / 2: ℚ_[p])) * rp18 ((rp21 p) ^ j) 1)^2:= by
  rw [rp374 (p:=p) (K:=K) hp_odd']
  have hp_even: Even (p - 1):=hp.out.even_sub_one hp_odd'
  have hmem_complement :
      ∀ {j: ℕ},j ∈ (Finset.range (p - 1)).filter (fun j => Odd j) →
        (p - 1) - j ∈ (Finset.range (p - 1)).filter (fun j => Odd j):= by
    intro j hj
    rw [Finset.mem_filter,Finset.mem_range] at hj ⊢
    have hj_pos: 0 < j:= by
      rcases hj.2 with ⟨k,hk⟩
      omega
    have hcomp_odd: Odd ((p - 1) - j) :=
      Nat.Even.sub_odd (Nat.le_of_lt hj.1) hp_even hj.2
    exact ⟨Nat.sub_lt (rp308 (p:=p)) hj_pos,hcomp_odd⟩
  congr 1
  congr 1
  unfold rp354
  refine Finset.prod_bij (fun j _ => (p - 1) - j) ?_ ?_ ?_ ?_
  · intro j hj
    exact hmem_complement hj
  · intro a ha b hb hab
    rw [Finset.mem_filter,Finset.mem_range] at ha hb
    simpa [Nat.sub_sub_self (Nat.le_of_lt ha.1),Nat.sub_sub_self (Nat.le_of_lt hb.1)] using
      congrArg (fun t => (p - 1) - t) hab
  · intro j hj
    have hj_mem: j ∈ (Finset.range (p - 1)).filter (fun j => Odd j):=hj
    rw [Finset.mem_filter,Finset.mem_range] at hj
    refine ⟨(p - 1) - j,hmem_complement hj_mem,?_⟩
    · exact Nat.sub_sub_self (Nat.le_of_lt hj.1)
  · intro j hj
    rw [Finset.mem_filter,Finset.mem_range] at hj
    let j' : Fin (p - 1):=⟨j,hj.1⟩
    simpa [j',rp316] using
      congrArg (fun χ: DirichletCharacter ℚ_[p] p =>
        (-(1 / 2: ℚ_[p])) * rp18 χ 1)
        (rp349 (p:=p) j')
end SignFree
end

section
open NumberField KummerCriterion PadicInt
namespace FiniteMinus
variable (p: ℕ) [hp: Fact p.Prime]
lemma w_dvd (j: ℕ) (hm: p ∈ primes) (hj: j < p-1) (ho: j%2=1) :
    (¬ (p: ℤ_[p])^2 ∣ weighted p j) ∧ ((p: ℤ_[p]) ∣ weighted p j ↔ j+2 ≠ p):= by
  let w:=weighted p j
  let r:=(toZModPow 2 w).val
  obtain ⟨hr,he⟩:=actual p j hm hj ho
  have hsub: (p: ℤ_[p])^2 ∣ w - (r: ℤ_[p]):= by
    rw [← Ideal.mem_span_singleton,← ker_toZModPow,RingHom.mem_ker,map_sub,map_natCast,sub_eq_zero]; exact (ZMod.natCast_zmod_val _).symm
  have hd: (p: ℤ_[p]) ∣ w - (r: ℤ_[p]):=dvd_trans (dvd_pow_self _ (by decide: 2 ≠ 0)) hsub
  have hnat: (p: ℤ_[p]) ∣ (r: ℤ_[p]) ↔ p ∣ r:= by
    rw [← Int.natCast_dvd_natCast]; simpa only [pow_one,Int.cast_natCast] using (pow_p_dvd_int_iff (p:=p) 1 (r: ℤ))
  constructor
  · intro h
    have hz: toZModPow 2 w = 0:= by rwa [← RingHom.mem_ker,ker_toZModPow,Ideal.mem_span_singleton]
    apply hr; change (toZModPow 2 w).val = 0; simp [hz]
  · change (p: ℤ_[p]) ∣ w ↔ _
    rw [← he]; change _ ↔ p ∣ r
    rw [← hnat]; exact dvd_iff_dvd_of_dvd_sub hd
lemma normW (j: ℕ) (hm: p ∈ primes) (hj: j < p-1) (ho: j%2=1) :
    ‖weighted p j‖ = if j+2=p then 1 else ‖(p: ℤ_[p])‖:= by
  obtain ⟨hn,hd⟩:=w_dvd p j hm hj ho
  have unitNorm (x: ℤ_[p]) (h: ¬(p: ℤ_[p]) ∣ x) : ‖x‖ = 1:= by
    exact le_antisymm (norm_le_one x) (not_lt.mp (fun hh => h ((norm_lt_one_iff_dvd x).mp hh)))
  split_ifs with he
  · exact unitNorm _ (fun h => (hd.mp h) he)
  · obtain ⟨a,ha⟩:=hd.mpr he
    have hu: ¬(p: ℤ_[p]) ∣ a:= by
      rintro ⟨b,rfl⟩; apply hn; exact ⟨b,by rw [ha,pow_two,mul_assoc]⟩
    rw [ha,norm_mul,unitNorm _ hu,mul_one]
end FiniteMinus
end

section
open FiniteMinus KummerCriterion NumberField
namespace SignFree
variable (p: ℕ) [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem rp376 (hm: p ∈ primes) (ho: p ≠ 2) : ¬ p ∣ hMinus K:= by
  have hgt: 2 < p:=lt_of_le_of_ne hp.out.two_le ho.symm
  have h2: ‖(2: ℚ_[p])‖ = 1:= by
    exact (Padic.norm_natCast_eq_one_iff (p:=p) (n:=2)).mpr (hp.out.coprime_iff_not_dvd.mpr fun h => (not_le_of_gt hgt) (Nat.le_of_dvd (by decide) h))
  let S:=(Finset.range (p-1)).filter (fun j => Odd j)
  let f:=fun j => (-(1/2: ℚ_[p])) * rp18 ((rp21 p)^j) 1
  have hnorm (j: ℕ) (hj: j ∈ S) : ‖f j‖ = if j=p-2 then ‖(p: ℚ_[p])‖⁻¹ else 1:= by
    obtain ⟨hj,k,hk⟩:=Finset.mem_filter.mp hj
    have hj':=Finset.mem_range.mp hj
    have h:=congrArg norm (rp27 p j (by omega) hj')
    rw [norm_mul,PadicInt.padic_norm_e_of_padicInt,normW p j hm hj' (by omega)] at h
    simp only [f,norm_mul,norm_neg,norm_div,norm_one,h2,div_one,one_mul]
    have hn: 0 < ‖(p: ℚ_[p])‖:=norm_pos_iff.mpr (by exact_mod_cast hp.out.ne_zero)
    split_ifs at h ⊢ <;> first | omega | apply (eq_div_iff (ne_of_gt hn)).2 | skip
    all_goals first | rw [inv_eq_one_div]; exact (eq_div_iff (ne_of_gt hn)).mpr (by linarith) | change ‖(p: ℚ_[p])‖ * _ = ‖(p: ℚ_[p])‖ at h; nlinarith
  have hmem: p-2 ∈ S:= by
    obtain ⟨k,hk⟩:=hp.out.odd_of_ne_two ho
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨k-1,by omega⟩⟩
  have hprod: (∏ j ∈ S,‖f j‖) = ‖(p: ℚ_[p])‖⁻¹:= by
    rw [Finset.prod_congr rfl hnorm]; simp [hmem]
  have hf:=congrArg norm (rp375 p K ho)
  change ‖((hMinus K: ℕ) : ℚ_[p])^2‖ = ‖((2*p: ℚ_[p]) * ∏ j ∈ S,f j)^2‖ at hf
  simp only [norm_pow,norm_mul,h2,one_mul,norm_prod,hprod,mul_inv_cancel₀ (show ‖(p: ℚ_[p])‖ ≠ 0 by simp [hp.out.ne_zero]),one_pow] at hf
  apply hp.out.coprime_iff_not_dvd.mp; apply Padic.norm_natCast_eq_one_iff.mp
  nlinarith [norm_nonneg ((hMinus K: ℕ) : ℚ_[p])]
end SignFree
end

section
namespace SReg.Cert
def mul (a: V) : V → V
| [] => []
| b::bs => add (scale b a) (0 :: mul a bs)
variable {R: Type*} [CommRing R] (x: R)
theorem ev_add (a b: V) : ev x (add a b) = ev x a + ev x b:= by
  induction a generalizing b with
  | nil => simp [add,ev]
  | cons c cs ih => cases b <;> simp [add,ev,ih] <;> ring
theorem ev_scale (n: ℤ) (a: V) : ev x (scale n a) = n * ev x a:= by
  induction a with
  | nil => simp [scale,ev]
  | cons c cs ih => simp [scale,ev] at ih ⊢; rw [ih]; ring
theorem ev_mul (a b: V) : ev x (mul a b) = ev x a * ev x b:= by
  induction b with
  | nil => simp [ev,mul]
  | cons c cs ih => simp [mul,ev_add,ev_scale,ev,ih]; ring
theorem step (a b r q phi: V) (h: mul a b = add (mul q phi) r) (hp: ev x phi = 0) : ev x a * ev x b = ev x r:= by
  rw [← ev_mul,h,ev_add,ev_mul,hp]; ring
end SReg.Cert
end

section
namespace SReg.Cert
variable {R: Type*} [CommRing R]
theorem rp377 (x: R) (a b: V) : ev x (a++b) = ev x a + x^a.length * ev x b:= by
  induction a with
  | nil => simp [ev]
  | cons c cs ih => simp [ev,ih,pow_succ]; ring
theorem ev_rot (x: R) (a: V) (h: x^a.length = 1) : ev x (rot a) = x * ev x a:= by
  induction a using List.reverseRecOn with
  | nil => simp [rot,ev]
  | append_singleton a b _ => simp [rot,rp377,ev,pow_succ] at h ⊢; linear_combination -(b: R)*h
theorem len_rot (a: V) (ha: a ≠ []) : (rot a).length = a.length:= by simp [rot]; have:=List.length_pos_iff.mpr ha; omega
theorem rotN_aux (x: R) (k: ℕ) (a: V) (ha: a ≠ []) (h: x^a.length = 1) : (rotN k a).length = a.length ∧ ev x (rotN k a) = x^k * ev x a:= by
  induction k with
  | zero => simp [rotN]
  | succ k ih =>
    change (rot (rotN k a)).length = _ ∧ ev x (rot (rotN k a)) = _
    have hn: rotN k a ≠ []:=fun hc => ha (List.length_eq_zero_iff.mp (by simpa [hc] using ih.1.symm))
    rw [len_rot _ hn,ev_rot _ _ (ih.1.symm ▸ h),ih.1,ih.2,pow_succ]; constructor <;> ring
end SReg.Cert
end

section
namespace SReg.Cert
variable {R: Type*} [CommRing R]
def act (k: ℕ) (a: V) : V → V
| [] => scale 0 a
| c::cs => add (scale c a) (rotN k (act k a cs))
theorem rp378 (a b: V) (h: a.length = b.length) : (add a b).length = a.length:= by
  induction a generalizing b with
  | nil => simpa [add] using h.symm
  | cons c cs ih => cases b <;> simp_all [add]
theorem act_aux (x: R) (k: ℕ) (a b: V) (ha: a ≠ []) (h: x^a.length = 1) : (act k a b).length = a.length ∧ ev x (act k a b) = ev x a * ev (x^k) b:= by
  induction b with
  | nil => simp [act,scale,ev]; simpa [scale] using ev_scale x 0 a
  | cons c cs ih =>
    have hn: act k a cs ≠ []:=fun hc => ha (List.length_eq_zero_iff.mp (by simpa [hc] using ih.1.symm))
    have he:=rotN_aux x k _ hn (ih.1.symm ▸ h)
    constructor
    · rw [act,rp378]; simp [scale]; simpa [scale,he.1] using ih.1.symm
    · rw [act,ev_add,ev_scale,he.2,ih.2,ev]; ring
def initV (p: ℕ) : V:=1 :: List.replicate (p-1) 0
def accum (p: ℕ) (b: V) : ℕ → V
| 0 => initV p
| k+1 => act (k+1) (accum p b k) b
theorem rp379 (x: R) (n: ℕ) : ev x (List.replicate n 0) = 0:= by induction n <;> simp_all [List.replicate_succ,ev]
theorem rp380 (x: R) (p: ℕ) (hp: 0 < p) (hx: x^p = 1) (b: V) (k: ℕ) : (accum p b k).length = p ∧ ev x (accum p b k) = ∏ i ∈ Finset.range k,ev (x^(i+1)) b:= by
  induction k with
  | zero => simp [accum,initV,ev,rp379]; omega
  | succ k ih =>
    have hn: accum p b k ≠ []:= by intro hh; simp [hh] at ih; omega
    obtain ⟨hl,he⟩:=act_aux x (k+1) (accum p b k) b hn (ih.1.symm ▸ hx)
    exact ⟨hl.trans ih.1,by rw [accum,he,Finset.prod_range_succ,ih.2]⟩
end SReg.Cert
end

section
namespace SReg.Cert
variable {R: Type*} [CommRing R] [IsDomain R]
theorem rep_ev (x: R) (c: ℤ) (n: ℕ) : ev x (List.replicate n c) = c * ∑ i ∈ Finset.range n,x^i:= by
  induction n with
  | zero => simp [ev]
  | succ n ih => rw [List.replicate_succ,ev,ih,Finset.sum_range_succ']; simp only [pow_zero,pow_succ,← Finset.sum_mul]; ring
theorem certify {p: ℕ} (hp: 1 < p) (n: ℕ) (b: V) (c: ℤ) (h: accum p b (p-1) = add [n] (List.replicate p c)) (x: R) (hx: IsPrimitiveRoot x p) : ∏ i ∈ Finset.range (p-1),ev (x^(i+1)) b = n:= by
  rw [← (rp380 x p (by omega) hx.pow_eq_one b (p-1)).2,h,ev_add,rep_ev,hx.geom_sum_eq_zero hp]; simp [ev]
end SReg.Cert
end

section
open NumberField IsCyclotomicExtension Polynomial Module Nat Ideal
open scoped NumberField
namespace SReg.Cert
lemma ev_map {R S: Type*} [CommRing R] [CommRing S] (e: R →+* S) (x: R) (b: V) : e (ev x b) = ev (e x) b:= by induction b with | nil => simp [ev] | cons a b ih => simp [ev,ih]
variable {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
lemma principalCert (b: V) (hpos: 0 < N)
    (hK: ∏ i ∈ Finset.range (p-1),ev ((zeta p ℚ K)^(i+1)) b = (N: K))
    (hO: ∏ i ∈ Finset.range (p-1),ev ((zeta_spec p ℚ K).toInteger^(i+1)) b = (N: 𝓞 K))
    (P: Ideal (𝓞 K)) [P.IsPrime] (hm: (N: 𝓞 K) ∈ P) (hN: absNorm P = N) : Submodule.IsPrincipal P:= by
  have hp':=hp.out
  have hc (i) (hi: i ∈ Finset.range (p-1)) : (i+1).Coprime p:= by
    rw [Nat.coprime_comm,Nat.Prime.coprime_iff_not_dvd hp']; exact Nat.not_dvd_of_pos_of_lt (by omega) (by have:=Finset.mem_range.mp hi; omega)
  have he (k) (hk: k.Coprime p) : Algebra.norm ℚ (ev ((zeta p ℚ K)^k) b) = Algebra.norm ℚ (ev (zeta p ℚ K) b):= by
    let h:=(zeta_spec p ℚ K).pow_of_coprime k hk
    let hir:=cyclotomic.irreducible_rat hp'.pos
    let e:=fromZetaAut h hir
    have hz: e (zeta p ℚ K) = (zeta p ℚ K)^k:=fromZetaAut_spec h hir
    have hg:=ev_map e.toRingEquiv.toRingHom (zeta p ℚ K) b
    change e (ev (zeta p ℚ K) b) = ev (e (zeta p ℚ K)) b at hg
    rw [← hz,← hg]; exact Algebra.norm_eq_of_algEquiv e _
  have h:=congrArg (Algebra.norm ℚ) hK
  rw [map_prod,Finset.prod_congr rfl (fun k hk => he _ (hc k hk)),Finset.prod_const,Finset.card_range] at h
  have hr: finrank ℚ K = p-1:= by rw [IsCyclotomicExtension.finrank (n:=p) K (cyclotomic.irreducible_rat hp'.pos),Nat.totient_prime hp']
  rw [Algebra.norm_natCast,hr] at h
  have hn: |Algebra.norm ℚ (ev (zeta p ℚ K) b)| = (N:ℚ):=(pow_left_inj₀ (abs_nonneg _) (by positivity) (by have:=hp'.two_le; omega: p-1 ≠ 0)).mp (by simpa [abs_pow] using congrArg abs h)
  rw [← hO] at hm
  obtain ⟨k,hk,hmem⟩:=IsPrime.prod_mem_iff.mp hm
  let a:=ev ((zeta_spec p ℚ K).toInteger^(k+1)) b
  rw [← he _ (hc k hk)] at hn
  have hn' : |Algebra.norm ℚ (algebraMap (𝓞 K) K a)| = N:= by rw [show a = _ from rfl,ev_map,map_pow]; exact hn
  rw [Algebra.norm_localization ℤ (nonZeroDivisors ℤ)] at hn'
  change |((Algebra.norm ℤ a: ℤ) : ℚ)| = N at hn'
  have ha: (Algebra.norm ℤ a).natAbs = N:= by
    have h: |(Algebra.norm ℤ a: ℤ)| = N:= by exact_mod_cast hn'
    exact_mod_cast (Int.natCast_natAbs _).trans h
  have hs: span {a} ≤ P:=(span_singleton_le_iff_mem _).mpr hmem
  obtain ⟨J,hJ⟩:=dvd_iff_le.mpr hs
  have ht:=congrArg absNorm hJ
  rw [absNorm_span_singleton,ha,map_mul,hN] at ht
  have htop: J = ⊤:=absNorm_eq_one_iff.mp (by nlinarith only [ht,hpos])
  exact ⟨a,by simpa [htop] using hJ.symm⟩
end SReg.Cert
end

section
open NumberField IsCyclotomicExtension Polynomial Module Nat Ideal
open scoped NumberField
namespace SReg.Cert
variable {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
lemma rp381 (b: V)
    (hK: ∏ i ∈ Finset.range (p-1),ev ((zeta p ℚ K)^(i+1)) b = (N: K))
    (k: ℕ) (hk: k.Coprime p) : |Algebra.norm ℚ (ev ((zeta p ℚ K)^k) b)| = (N: ℚ):= by
  have hp':=hp.out
  have hc (i) (hi: i ∈ Finset.range (p-1)) : (i+1).Coprime p:= by
    rw [Nat.coprime_comm,Nat.Prime.coprime_iff_not_dvd hp']; exact Nat.not_dvd_of_pos_of_lt (by omega) (by have:=Finset.mem_range.mp hi; omega)
  have he (k) (hk: k.Coprime p) : Algebra.norm ℚ (ev ((zeta p ℚ K)^k) b) = Algebra.norm ℚ (ev (zeta p ℚ K) b):= by
    let h:=(zeta_spec p ℚ K).pow_of_coprime k hk
    let hir:=cyclotomic.irreducible_rat hp'.pos
    let e:=fromZetaAut h hir
    have hz: e (zeta p ℚ K) = (zeta p ℚ K)^k:=fromZetaAut_spec h hir
    have hg:=ev_map e.toRingEquiv.toRingHom (zeta p ℚ K) b
    change e (ev (zeta p ℚ K) b) = ev (e (zeta p ℚ K)) b at hg
    rw [← hz,← hg]; exact Algebra.norm_eq_of_algEquiv e _
  have h:=congrArg (Algebra.norm ℚ) hK
  rw [map_prod,Finset.prod_congr rfl (fun k hk => he _ (hc k hk)),Finset.prod_const,Finset.card_range] at h
  have hr: finrank ℚ K = p-1:= by rw [IsCyclotomicExtension.finrank (n:=p) K (cyclotomic.irreducible_rat hp'.pos),Nat.totient_prime hp']
  rw [Algebra.norm_natCast,hr] at h
  have hn: |Algebra.norm ℚ (ev (zeta p ℚ K) b)| = (N:ℚ):=(pow_left_inj₀ (abs_nonneg _) (by positivity) (by have:=hp'.two_le; omega: p-1 ≠ 0)).mp (by simpa [abs_pow] using congrArg abs h)
  rwa [he _ hk]
end SReg.Cert
end

section
/-! Descend signed norm certificates to a quadratic subfield. -/
open NumberField IsCyclotomicExtension Polynomial Module Nat Ideal
open scoped NumberField
namespace SReg.Cert
variable {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (F: Type*) [Field F] [NumberField F] [Algebra F K] [IsScalarTower ℚ F K] [FiniteDimensional F K]
theorem rp382 (b: V) (hpos: 0 < N) (d: finrank F K = 2)
    (hK: ∏ i ∈ Finset.range (p-1),ev ((zeta p ℚ K)^(i+1)) b = ((N^2: ℕ) : K))
    (a: ℕ → 𝓞 F) (ha: ∀ i ∈ Finset.range (p-1),algebraMap F K (a i: F) = ev ((zeta p ℚ K)^(i+1)) b)
    (P: Ideal (𝓞 F)) [P.IsPrime] (hm: (N: 𝓞 F) ∈ P) (hN: absNorm P = N) : Submodule.IsPrincipal P:= by
  have hO: ∏ i ∈ Finset.range (p-1),a i = ((N^2: ℕ) : 𝓞 F):= by
    apply RingOfIntegers.ext_iff.mpr
    apply (algebraMap F K).injective
    change algebraMap F K (algebraMap (𝓞 F) F _) = algebraMap F K (algebraMap (𝓞 F) F _)
    rw [map_prod,map_prod,map_natCast,map_natCast,← hK]; exact Finset.prod_congr rfl ha
  have hm2: ∏ i ∈ Finset.range (p-1),a i ∈ P:= by rw [hO,Nat.cast_pow]; rw [pow_two]; exact P.mul_mem_left _ hm
  obtain ⟨k,hk,hmem⟩:=IsPrime.prod_mem_iff.mp hm2
  have hc: (k+1).Coprime p:= by rw [Nat.coprime_comm,hp.out.coprime_iff_not_dvd]; exact Nat.not_dvd_of_pos_of_lt (by omega) (by have:=Finset.mem_range.mp hk; omega)
  have h:=rp381 K b hK (k+1) hc
  rw [← ha k hk,← Algebra.norm_norm (S:=F),Algebra.norm_algebraMap,d,map_pow,abs_pow,Nat.cast_pow] at h
  have hn:=(pow_left_inj₀ (abs_nonneg _) (Nat.cast_nonneg _) (by decide: (2:ℕ) ≠ 0)).mp h
  change |Algebra.norm ℚ (algebraMap (𝓞 F) F (a k))| = (N:ℚ) at hn
  rw [Algebra.norm_localization ℤ (nonZeroDivisors ℤ)] at hn
  change |((Algebra.norm ℤ (a k) : ℤ) : ℚ)| = N at hn
  have hZ: |(Algebra.norm ℤ (a k) : ℤ)| = N:= by exact_mod_cast hn
  have hA: (Algebra.norm ℤ (a k)).natAbs = N:= by exact_mod_cast (Int.natCast_natAbs _).trans hZ
  have hs: span {a k} ≤ P:=(span_singleton_le_iff_mem _).mpr hmem
  obtain ⟨J,hJ⟩:=dvd_iff_le.mpr hs
  have ht:=congrArg absNorm hJ
  rw [absNorm_span_singleton,hA,map_mul,hN] at ht
  have htop: J = ⊤:=absNorm_eq_one_iff.mp (by nlinarith only [ht,hpos])
  exact ⟨a k,by simpa [htop] using hJ.symm⟩
end SReg.Cert
end

section
namespace SReg.Cert
theorem rp383 {R: Type*} [CommRing R] (x: R) (k: ℕ) (a: V) (hk: k ≤ a.length) (h: x^a.length = 1) : (shift k a).length = a.length ∧ ev x (shift k a) = x^k * ev x a:= by
  let m:=a.length-k
  have ha:=rp377 x (a.take m) (a.drop m)
  rw [List.take_append_drop] at ha
  have hk' : (a.drop m).length = k:= by simp [m]; omega
  have hm: (a.take m).length = m:= by simp [m]
  have H: x^k * x^m = 1:= by rw [← pow_add,show k+m = a.length by dsimp [m];omega,h]
  constructor
  · simp [shift]
  · change ev x (a.drop m ++ a.take m) = _
    rw [rp377,hk',ha,hm,mul_add,← mul_assoc,H,one_mul,add_comm]
end SReg.Cert
end

section
namespace SReg.Cert.Speed
variable {R: Type*} [CommRing R]
theorem rp378 (a b: V) (h: a.length = b.length) : (add a b).length = a.length:= by
  induction a generalizing b with
  | nil => simpa [add] using h.symm
  | cons c cs ih => cases b <;> simp_all [add]
theorem act_aux (x: R) (k: ℕ) (a b: V) (ha: a ≠ []) (h: x^a.length = 1) : (act k a b).length = a.length ∧ ev x (act k a b) = ev x a * ev (x^k) b:= by
  induction b with
  | nil => simp [act,scale,ev]; simpa [scale] using ev_scale x 0 a
  | cons c cs ih =>
    have hn: act k a cs ≠ []:=fun hc => ha (List.length_eq_zero_iff.mp (by simpa [hc] using ih.1.symm))
    let u:=act k a cs
    have he: (if k ≤ u.length then shift k u else rotN k u).length = u.length ∧ ev x (if k ≤ u.length then shift k u else rotN k u) = x^k * ev x u:= by split <;> rename_i hk; exact rp383 x _ _ hk (ih.1.symm ▸ h); exact rotN_aux x k _ hn (ih.1.symm ▸ h)
    constructor
    · rw [act,rp378]; simp [scale]; exact (by simpa [scale,u] using (ih.1.symm.trans he.1.symm))
    · rw [act,ev_add,ev_scale,he.2,ih.2,ev]; ring
def accum (p: ℕ) (b: V) : ℕ → V
| 0 => initV p
| k+1 => act (k+1) (accum p b k) b
theorem rp379 (x: R) (n: ℕ) : ev x (List.replicate n 0) = 0:= by induction n <;> simp_all [List.replicate_succ,ev]
theorem rp380 (x: R) (p: ℕ) (hp: 0 < p) (hx: x^p = 1) (b: V) (k: ℕ) : (accum p b k).length = p ∧ ev x (accum p b k) = ∏ i ∈ Finset.range k,ev (x^(i+1)) b:= by
  induction k with
  | zero => simp [accum,initV,ev,rp379]; omega
  | succ k ih =>
    have hn: accum p b k ≠ []:= by intro hh; simp [hh] at ih; omega
    obtain ⟨hl,he⟩:=act_aux x (k+1) (accum p b k) b hn (ih.1.symm ▸ hx)
    exact ⟨hl.trans ih.1,by rw [accum,he,Finset.prod_range_succ,ih.2]⟩
end SReg.Cert.Speed
end

section
namespace SReg.Cert.Speed
variable {R: Type*} [CommRing R] [IsDomain R]
theorem rep_ev (x: R) (c: ℤ) (n: ℕ) : ev x (List.replicate n c) = c * ∑ i ∈ Finset.range n,x^i:= by
  induction n with
  | zero => simp [ev]
  | succ n ih => rw [List.replicate_succ,ev,ih,Finset.sum_range_succ']; simp only [pow_zero,pow_succ,← Finset.sum_mul]; ring
theorem certify {p: ℕ} (hp: 1 < p) (n: ℕ) (b: V) (c: ℤ) (h: accum p b (p-1) = add [n] (List.replicate p c)) (x: R) (hx: IsPrimitiveRoot x p) : ∏ i ∈ Finset.range (p-1),ev (x^(i+1)) b = n:= by
  rw [← (rp380 x p (by omega) hx.pow_eq_one b (p-1)).2,h,ev_add,rep_ev,hx.geom_sum_eq_zero hp]; simp [ev]
end SReg.Cert.Speed
end

section
open NumberField IsCyclotomicExtension Module Nat Ideal NumberField.IsCMField
open scoped NumberField
namespace SReg.Cert
variable {p: ℕ} [hp: Fact p.Prime]
lemma rp384 {R: Type*} [CommRing R] (x: R) (hx: x^p=1) (b: V)
    (h: Speed.act (p-1) (Speed.initV p) b = Speed.act 1 (Speed.initV p) b) : ev (x^(p-1)) b = ev x b:= by
  have hlen: (Speed.initV p).length = p:= by simp [Speed.initV]; have:=hp.out.pos; omega
  have hinit: ev x (Speed.initV p) = 1:= by simp [Speed.initV,ev,Speed.rp379]
  have hact k:=(Speed.act_aux x k (Speed.initV p) b (by simp [Speed.initV]) (hlen.symm ▸ hx)).2
  simpa [hinit] using (hact (p-1)).symm.trans ((congrArg (ev x) h).trans (hact 1))
variable (K: Type*) [Field K] [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K]
lemma conjZeta: complexConj K (zeta p ℚ K) = (zeta p ℚ K)^(p-1):= by
  have hz:=(zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  let hu:=hz.isUnit_unit hp.out.ne_zero
  let u: Units.torsion K:=⟨(hz.isUnit hp.out.ne_zero).unit,(CommGroup.mem_torsion _).mpr ⟨p,hp.out.pos,by rw [isPeriodicPt_mul_iff_pow_eq_one]; exact hu.pow_eq_one⟩⟩
  have hc:=complexConj_torsion K u
  have hv: (u.val: K) = (zeta p ℚ K):= by simp [u]; rfl
  rw [hv] at hc; rw [hc]; apply inv_eq_of_mul_eq_one_right; rw [← _root_.pow_succ',Nat.sub_add_cancel hp.out.pos,(zeta_spec p ℚ K).pow_eq_one]
lemma realLift (b: V) (h: Speed.act (p-1) (Speed.initV p) b = Speed.act 1 (Speed.initV p) b) (k: ℕ) : ∃ y: 𝓞 (maximalRealSubfield K),algebraMap (maximalRealSubfield K) K (y: maximalRealSubfield K) = ev ((zeta p ℚ K)^k) b:= by
  let a:=ev ((zeta_spec p ℚ K).toInteger^k) b
  have ha: (a: K) = ev ((zeta p ℚ K)^k) b:= by change algebraMap (𝓞 K) K _ = _; rw [ev_map,map_pow]; rfl
  have hc: complexConj K (a: K) = (a: K):= by
    rw [ha]; change (complexConj K).toRingEquiv.toRingHom _ = _
    rw [ev_map,map_pow]; change ev ((complexConj K (zeta p ℚ K))^k) b = _
    rw [conjZeta,← pow_mul,Nat.mul_comm,pow_mul]; exact rp384 _ (by rw [← pow_mul,Nat.mul_comm,pow_mul,(zeta_spec p ℚ K).pow_eq_one,one_pow]) b h
  obtain ⟨y,hy⟩:=(IsCMField.RingOfIntegers.complexConj_eq_self_iff K a).mp hc
  exact ⟨y,hy.trans ha⟩
end SReg.Cert
end

section
/-! A real subfield discriminant bound via the relative different. -/
open NumberField IsCyclotomicExtension Module Nat
open scoped NumberField
namespace SReg
lemma rp385 {p: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] (F: Type*) [Field F] [NumberField F] [Algebra F K] (h: finrank F K = 2) : (discr F).natAbs ≤ p ^ ((p-2)/2):= by
  have H:=natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K)
  rw [h] at H
  have hK: (discr K).natAbs = p^(p-2):= by rw [IsCyclotomicExtension.Rat.discr_prime p K]; simp [Int.natAbs_mul,Int.natAbs_pow]
  have hd: (discr F).natAbs ^ 2 ∣ p^(p-2):=⟨_,by rw [← hK,H,mul_comm]⟩
  have hd' : (discr F).natAbs ∣ p^(p-2):=(dvd_pow_self _ (by decide: 2 ≠ 0)).trans hd
  obtain ⟨j,_,hj⟩:=(Nat.dvd_prime_pow hp.out).mp hd'
  rw [hj,← pow_mul,pow_dvd_pow_iff_le_right hp.out.one_lt] at hd
  rw [hj]; exact Nat.pow_le_pow_right hp.out.pos (by omega)
end SReg
end

section
open NumberField NumberField.InfinitePlace IsCyclotomicExtension Module Nat Real
open scoped NumberField
namespace SReg
local instance: Fact (Nat.Prime 23):=⟨by decide⟩
theorem rp386 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {23} ℚ K] (F: Type*) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) :
    ⌊(4 / π) ^ nrComplexPlaces F * ((finrank ℚ F)! / (finrank ℚ F) ^ (finrank ℚ F) * √|discr F|)⌋₊ < 901:= by
  have hK:=IsCyclotomicExtension.finrank (n:=23) K (Polynomial.cyclotomic.irreducible_rat (by decide))
  rw [← finrank_mul_finrank ℚ F K,h,Nat.totient_prime (by decide: Nat.Prime 23)] at hK
  have hD:=rp385 (p:=23) K F h
  change (discr F).natAbs ≤ 41426511213649 at hD
  have hR: |((discr F: ℤ) : ℝ)| ≤ 41426511213649:= by exact_mod_cast (Int.natCast_natAbs _).symm.le.trans (Int.ofNat_le.mpr hD)
  have hs: √|((discr F: ℤ) : ℝ)| ≤ 6436344:=(Real.sqrt_le_iff.mpr ⟨by positivity,hR.trans (by norm_num)⟩)
  apply (Nat.floor_lt (by positivity)).mpr
  rw [IsTotallyReal.nrComplexPlaces_eq_zero,pow_zero,one_mul,show finrank ℚ F = 11 by omega]
  norm_num [Nat.factorial] at * <;> linarith only [hs]
local instance: Fact (Nat.Prime 29):=⟨by decide⟩
theorem rp387 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {29} ℚ K] (F: Type*) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) :
    ⌊(4 / π) ^ nrComplexPlaces F * ((finrank ℚ F)! / (finrank ℚ F) ^ (finrank ℚ F) * √|discr F|)⌋₊ < 25131:= by
  have hK:=IsCyclotomicExtension.finrank (n:=29) K (Polynomial.cyclotomic.irreducible_rat (by decide))
  rw [← finrank_mul_finrank ℚ F K,h,Nat.totient_prime (by decide: Nat.Prime 29)] at hK
  have hD:=rp385 (p:=29) K F h
  change (discr F).natAbs ≤ 10260628712958602189 at hD
  have hR: |((discr F: ℤ) : ℝ)| ≤ 10260628712958602189:= by exact_mod_cast (Int.natCast_natAbs _).symm.le.trans (Int.ofNat_le.mpr hD)
  have hs: √|((discr F: ℤ) : ℝ)| ≤ 3203221615:=(Real.sqrt_le_iff.mpr ⟨by positivity,hR.trans (by norm_num)⟩)
  apply (Nat.floor_lt (by positivity)).mpr
  rw [IsTotallyReal.nrComplexPlaces_eq_zero,pow_zero,one_mul,show finrank ℚ F = 14 by omega]
  norm_num [Nat.factorial] at * <;> linarith only [hs]
end SReg
end

section
open NumberField IsCyclotomicExtension Ideal Module Nat
open scoped NumberField
namespace SReg
lemma rp388 {p q: ℕ} [hp: Fact p.Prime] [hq: Fact q.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] (F: Type*) [Field F] [NumberField F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) (P: Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (span {(q:ℤ)})] :
    (q = p ∧ P.inertiaDeg ℤ = 1) ∨ (q ≠ p ∧ ∃ k,0 < k ∧ k ≤ 2 ∧ orderOf (q: ZMod p) = P.inertiaDeg ℤ * k):= by
  have hP: P ≠ ⊥:=Ideal.ne_bot_of_liesOver_of_ne_bot (p:=span {(q:ℤ)}) (by simp [hq.out.ne_zero]) P
  haveI:=(inferInstance: P.IsPrime).isMaximal hP
  obtain ⟨Q,hQ,hQP⟩:=Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=𝓞 K) P
  haveI:=LiesOver.trans Q P (span {(q:ℤ)})
  haveI: NoZeroSMulDivisors (𝓞 F) (𝓞 K):=⟨fun {a b} hab => by
    rw [Algebra.smul_def,_root_.mul_eq_zero] at hab
    exact hab.imp (fun ha => (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (ha.trans (map_zero _).symm)) id⟩
  have ht:=Ideal.inertiaDeg_tower (R:=ℤ) P Q
  by_cases he: q = p
  · subst q; left; refine ⟨rfl,?_⟩
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p K Q] at ht
    exact Nat.eq_one_of_dvd_one ⟨_,ht⟩
  · right; refine ⟨he,Q.inertiaDeg (𝓞 F),Q.inertiaDeg_pos _,?_,?_⟩
    · rw [← h,← Ideal.inertiaDeg'_eq_inertiaDeg P Q]; exact Ideal.inertiaDeg_le_finrank _ F K Q hP
    · rw [← ht]; exact (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m:=p) q K Q (fun hd => ((Nat.dvd_prime hp.out).mp hd).elim hq.out.ne_one he)).symm
end SReg
end

section
open NumberField IsCyclotomicExtension Ideal Module Nat Algebra
open scoped NumberField
namespace SReg.Cert
variable {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def rp389 (b: V) (hN: 0 < N) (hs: Speed.act (p-1) (Speed.initV p) b = Speed.act 1 (Speed.initV p) b)
    (hn: ∏ i ∈ Finset.range (p-1),ev ((zeta p ℚ K)^(i+1)) b = ((N^2: ℕ) : K)) :=
  rp382 K (maximalRealSubfield K) b hN (IsQuadraticExtension.finrank_eq_two _ _) hn
    (fun i => (realLift K b hs (i+1)).choose) (fun i _ => (realLift K b hs (i+1)).choose_spec)
end SReg.Cert
end

section
namespace SReg.Cert.Pack
open SReg.Cert
def Pos (b: V):=∀ c ∈ b,0 ≤ c
lemma pos_cons {a: ℤ} {b: V} : Pos (a::b) ↔ 0 ≤ a ∧ Pos b:= by simp [Pos]
lemma pos_add {a b: V} (ha: Pos a) (hb: Pos b) : Pos (add a b):= by
  induction a generalizing b with
  | nil => exact hb
  | cons a as ih => cases b with
    | nil => exact ha
    | cons b bs => exact pos_cons.mpr ⟨add_nonneg (pos_cons.mp ha).1 (pos_cons.mp hb).1,ih (pos_cons.mp ha).2 (pos_cons.mp hb).2⟩
lemma rp390 {c: ℤ} {a: V} (hc: 0 ≤ c) (ha: Pos a) : Pos (scale c a):= by
  intro n hn; obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hn; exact mul_nonneg hc (ha t ht)
lemma pos_rot {a: V} (h: Pos a) : Pos (rot a):= by
  induction a using List.reverseRecOn with
  | nil => simp [rot,Pos]
  | append_singleton a x _ => simpa [Pos,rot] using (show 0 ≤ x ∧ Pos a from ⟨h x (by simp),fun c hc => h c (by simp [hc])⟩)
lemma pos_rotN {a: V} (h: Pos a) (k) : Pos (rotN k a):= by induction k with | zero => exact h | succ k ih => exact pos_rot ih
lemma pos_act (k) {a b: V} (ha: Pos a) (hb: Pos b) : Pos (act k a b):= by
  induction b with
  | nil => exact rp390 le_rfl ha
  | cons c cs ih => exact pos_add (rp390 (pos_cons.mp hb).1 ha) (pos_rotN (ih (pos_cons.mp hb).2) _)
lemma rp391 (p k) {b: V} (hb: Pos b) : Pos (accum p b k):= by
  induction k with
  | zero => simp [accum,initV,Pos]
  | succ k ih => exact pos_act _ ih hb
lemma eval_one (a: V) : ev (1: ℤ) a = a.sum:= by induction a <;> simp_all [ev]
lemma rp392 {a: V} (ha: Pos a) {x: ℤ} (hx: x ∈ a) : x ≤ a.sum:= by
  induction a with
  | nil => simp at hx
  | cons c cs ih => rcases List.mem_cons.mp hx with rfl|hh
                    · simp only [List.sum_cons,le_add_iff_nonneg_right]; exact List.sum_nonneg (pos_cons.mp ha).2
                    · exact (ih (pos_cons.mp ha).2 hh).trans (by simp [(pos_cons.mp ha).1])
end SReg.Cert.Pack
end

section
namespace SReg.Cert.Pack
open SReg.Cert
lemma rp393 {B: ℤ} (hB: 1 < B) (a: V) (ha: ∀ x ∈ a,0 ≤ x ∧ x < B-1) : 0 ≤ ev B a ∧ ev B a ≤ B^a.length-1 ∧ (a ≠ [] → ev B a < B^a.length-1):= by
  induction a with
  | nil => simp [ev]
  | cons c cs ih =>
    have hc:=ha c (by simp)
    have ht:=ih (fun x hx => ha x (by simp [hx]))
    have hm:=mul_le_mul_of_nonneg_left ht.2.1 (show 0 ≤ B by omega)
    simp only [ev,Int.cast_id,List.length_cons,pow_succ]
    refine ⟨add_nonneg hc.1 (mul_nonneg (by omega) ht.1),?_,fun _ => ?_⟩ <;> nlinarith
lemma ev_inj {B: ℤ} (hB: 1 < B) {a b: V} (hl: a.length=b.length) (ha: ∀ x ∈ a,0 ≤ x ∧ x < B-1) (hb: ∀ x ∈ b,0 ≤ x ∧ x < B-1) (he: ev B a=ev B b) : a=b:= by
  induction a generalizing b with
  | nil => simpa using hl.symm
  | cons c cs ih =>
    cases b with
    | nil => simp at hl
    | cons d ds =>
      simp only [ev,Int.cast_id] at he
      have hc:=ha c (by simp); have hd:=hb d (by simp)
      have hh:=congrArg (· % B) he
      simp only [Int.add_mul_emod_self_left] at hh
      rw [Int.emod_eq_of_lt hc.1 (by omega),Int.emod_eq_of_lt hd.1 (by omega)] at hh
      subst d
      simp only [add_right_inj,mul_right_inj' (show B ≠ 0 by omega)] at he
      exact congrArg (c :: ·) (ih (by simpa using hl) (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])) he)
end SReg.Cert.Pack
end

section
namespace SReg.Cert.Pack
open SReg.Cert
lemma cast_ev (B: ℤ) (M: ℕ) (a: V) : ((ev B a: ℤ) : ZMod M) = ev (B: ZMod M) a:= by induction a <;> simp_all [ev]
lemma packed {p k: ℕ} (hp: 0 < p) (b a: V) (B: ℤ) (M: ℕ) (hB: 1 < B) (hM: (M:ℤ)=B^p-1) (hroot: (B: ZMod M)^p=1) (hb: Pos b) (hl: a.length=p) (ha: ∀ x ∈ a,0 ≤ x ∧ x < B-1) (hs: b.sum^k < B-1) (he: ∏ i ∈ Finset.range k,ev ((B: ZMod M)^(i+1)) b = ev (B: ZMod M) a) : accum p b k = a:= by
  obtain ⟨hlen,hv⟩:=rp380 (B: ZMod M) p hp hroot b k
  have ho:=(rp380 (1:ℤ) p hp (one_pow _) b k).2
  simp only [one_pow,eval_one,Finset.prod_const,Finset.card_range] at ho
  have hpos:=rp391 p k hb
  have hds: ∀ x ∈ accum p b k,0 ≤ x ∧ x < B-1:=fun x hx => ⟨hpos x hx,(rp392 hpos hx).trans_lt (ho.symm ▸ hs)⟩
  apply ev_inj hB (hlen.trans hl.symm) hds ha
  have he' : ((ev B (accum p b k) : ℤ) : ZMod M) = ((ev B a: ℤ) : ZMod M):= by rw [cast_ev,cast_ev,hv,he]
  rw [ZMod.intCast_eq_intCast_iff'] at he'
  obtain ⟨h1,_,h2⟩:=rp393 hB _ hds
  obtain ⟨h3,_,h4⟩:=rp393 hB _ ha
  rw [hlen] at h2
  rw [hl] at h4
  rw [Int.emod_eq_of_lt h1 (by rw [hM]; apply h2; intro hh; simp [hh] at hlen; omega),Int.emod_eq_of_lt h3 (by rw [hM]; apply h4; intro hh; simp [hh] at hl; omega)] at he'
  exact he'
end SReg.Cert.Pack
end

section
namespace SReg.Cert.Pack
lemma run {p: ℕ} (hp: 1 < p) (n: ℕ) (b: V) (c B: ℤ) (M: ℕ) (hB: 1 < B) (hM: (M:ℤ)=B^p-1) (hroot: (B: ZMod M)^p=1) (hb: b.all (fun x => decide (0 ≤ x)) = true) (hl: (target p n c).length=p) (ha: (target p n c).all (fun x => decide (0 ≤ x ∧ x < B-1)) = true) (hs: b.sum^(p-1) < B-1) (he: ∏ i ∈ Finset.range (p-1),ev ((B: ZMod M)^(i+1)) b = ev (B: ZMod M) (target p n c)) {R: Type*} [CommRing R] [IsDomain R] (x: R) (hx: IsPrimitiveRoot x p) : ∏ i ∈ Finset.range (p-1),ev (x^(i+1)) b = (n:R):= by
  apply certify hp n b c _ x hx
  exact packed (by omega) b _ B M hB hM hroot (by simpa [Pos] using hb) hl (by simpa [target] using ha) hs he
end SReg.Cert.Pack
end

section
open NumberField IsCyclotomicExtension Ideal
open scoped NumberField
namespace SReg.Cert.OneTable
/-- A single check for a symmetric element of full-field norm N². -/
theorem sound {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K] (b: V) (hg: good p N b) (P: Ideal (𝓞 (maximalRealSubfield K))) [P.IsPrime] (hm: (N: 𝓞 (maximalRealSubfield K)) ∈ P) (he: absNorm P = N) : Submodule.IsPrincipal P:= by
  simp only [good,decide_eq_true_eq] at hg
  obtain ⟨hn,hs,hB,hM,hr,hb,hl,ha,hsum,hprod⟩:=hg
  exact rp389 K b hn hs (Pack.run hp.out.one_lt _ _ _ _ _ hB hM (rootM_sound _ _ _ hr) hb hl ha hsum (prodM_sound _ _ _ _ _ hprod) _ (zeta_spec p ℚ K)) P hm he
end SReg.Cert.OneTable
end


section
/-! Descend signed norm certificates to a quadratic subfield. -/
open NumberField IsCyclotomicExtension Polynomial Module Nat Ideal
open scoped NumberField
namespace SReg.Cert
variable {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (F: Type*) [Field F] [NumberField F] [Algebra F K] [IsScalarTower ℚ F K] [FiniteDimensional F K]
theorem rp394 (b: V) (hpos: 0 < N) (d: finrank F K = 2)
    (hK: ∏ i ∈ Finset.range (p-1),ev ((zeta p ℚ K)^(i+1)) b = ((N^2: ℕ) : K))
    (a: ℕ → 𝓞 F) (ha: ∀ i ∈ Finset.range (p-1),algebraMap F K (a i: F) = ev ((zeta p ℚ K)^(i+1)) b)
    (P: Ideal (𝓞 F)) [P.IsPrime] (hm: (N: 𝓞 F) ∈ P) (hN: N ≤ absNorm P) : Submodule.IsPrincipal P:= by
  have hO: ∏ i ∈ Finset.range (p-1),a i = ((N^2: ℕ) : 𝓞 F):= by
    apply RingOfIntegers.ext_iff.mpr
    apply (algebraMap F K).injective
    change algebraMap F K (algebraMap (𝓞 F) F _) = algebraMap F K (algebraMap (𝓞 F) F _)
    rw [map_prod,map_prod,map_natCast,map_natCast,← hK]; exact Finset.prod_congr rfl ha
  have hm2: ∏ i ∈ Finset.range (p-1),a i ∈ P:= by rw [hO,Nat.cast_pow]; rw [pow_two]; exact P.mul_mem_left _ hm
  obtain ⟨k,hk,hmem⟩:=IsPrime.prod_mem_iff.mp hm2
  have hc: (k+1).Coprime p:= by rw [Nat.coprime_comm,hp.out.coprime_iff_not_dvd]; exact Nat.not_dvd_of_pos_of_lt (by omega) (by have:=Finset.mem_range.mp hk; omega)
  have h:=rp381 K b hK (k+1) hc
  rw [← ha k hk,← Algebra.norm_norm (S:=F),Algebra.norm_algebraMap,d,map_pow,abs_pow,Nat.cast_pow] at h
  have hn:=(pow_left_inj₀ (abs_nonneg _) (Nat.cast_nonneg _) (by decide: (2:ℕ) ≠ 0)).mp h
  change |Algebra.norm ℚ (algebraMap (𝓞 F) F (a k))| = (N:ℚ) at hn
  rw [Algebra.norm_localization ℤ (nonZeroDivisors ℤ)] at hn
  change |((Algebra.norm ℤ (a k) : ℤ) : ℚ)| = N at hn
  have hZ: |(Algebra.norm ℤ (a k) : ℤ)| = N:= by exact_mod_cast hn
  have hA: (Algebra.norm ℤ (a k)).natAbs = N:= by exact_mod_cast (Int.natCast_natAbs _).trans hZ
  have hs: span {a k} ≤ P:=(span_singleton_le_iff_mem _).mpr hmem
  obtain ⟨J,hJ⟩:=dvd_iff_le.mpr hs
  have ht:=congrArg absNorm hJ
  rw [absNorm_span_singleton,hA,map_mul] at ht
  have hj: absNorm J ≠ 0:= by intro hz; rw [hz,mul_zero] at ht; omega
  have htop: J = ⊤:=absNorm_eq_one_iff.mp (by nlinarith only [ht,hpos,hN,Nat.one_le_iff_ne_zero.mpr hj])
  exact ⟨a k,by simpa [htop] using hJ.symm⟩
end SReg.Cert
end

section
open NumberField IsCyclotomicExtension Ideal Module Nat Algebra
open scoped NumberField
namespace SReg.Cert
variable {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def rp395 (b: V) (hN: 0 < N) (hs: Speed.act (p-1) (Speed.initV p) b = Speed.act 1 (Speed.initV p) b)
    (hn: ∏ i ∈ Finset.range (p-1),ev ((zeta p ℚ K)^(i+1)) b = ((N^2: ℕ) : K)) :=
  rp394 K (maximalRealSubfield K) b hN (IsQuadraticExtension.finrank_eq_two _ _) hn
    (fun i => (realLift K b hs (i+1)).choose) (fun i _ => (realLift K b hs (i+1)).choose_spec)
end SReg.Cert
end

section
open NumberField IsCyclotomicExtension Ideal
open scoped NumberField
namespace SReg.Cert.OneTableLE
/-- A single check for a symmetric element of full-field norm N². -/
def good (p N: ℕ) (b: V) : Bool :=
  let n:=N^2
  let c: ℤ:=(b.sum^(p-1)-n)/p
  let B: ℤ:=b.sum^(p-1)+2
  let M: ℕ:=(b.sum.toNat^(p-1)+2)^p-1
  decide (0 < N ∧ Speed.act (p-1) (Speed.initV p) b = Speed.act 1 (Speed.initV p) b ∧
    1 < B ∧ (M: ℤ) = B^p-1 ∧ B^p%(M:ℤ)=1 ∧ b.all (fun x => decide (0 ≤ x)) = true ∧
    (Pack.target p n c).length=p ∧ (Pack.target p n c).all (fun x => decide (0 ≤ x ∧ x < B-1)) = true ∧
    b.sum^(p-1) < B-1 ∧ prodM M B b (p-1) = valM M B (Pack.target p n c))
theorem sound {p N: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K] (b: V) (hg: good p N b) (P: Ideal (𝓞 (maximalRealSubfield K))) [P.IsPrime] (hm: (N: 𝓞 (maximalRealSubfield K)) ∈ P) (he: N ≤ absNorm P) : Submodule.IsPrincipal P:= by
  simp only [good,decide_eq_true_eq] at hg
  obtain ⟨hn,hs,hB,hM,hr,hb,hl,ha,hsum,hprod⟩:=hg
  exact rp395 K b hn hs (Pack.run hp.out.one_lt _ _ _ _ _ hB hM (rootM_sound _ _ _ hr) hb hl ha hsum (prodM_sound _ _ _ _ _ hprod) _ (zeta_spec p ℚ K)) P hm he
end SReg.Cert.OneTableLE
end

section
open NumberField IsCyclotomicExtension Ideal Module Nat Algebra
open scoped NumberField
namespace SReg.Cert.OneTable
theorem pid {p B: ℕ} [hp: Fact p.Prime] (K: Type*) [Field K] [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K] (rs: List Row)
    (hg: rs.all (fun r => good p r.1 (unpack p r)))
    (hb: ⌊(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces (maximalRealSubfield K) * ((finrank ℚ (maximalRealSubfield K))! / (finrank ℚ (maximalRealSubfield K)) ^ (finrank ℚ (maximalRealSubfield K)) * Real.sqrt |discr (maximalRealSubfield K)|)⌋₊ < B)
    (hc: ∀ q f: ℕ,q.Prime → 0 < f → q^f < B → (q = p ∨ (q: ZMod p)^(f*2)=1) → covers rs q (q^f)) : IsPrincipalIdealRing (𝓞 (maximalRealSubfield K)):= by
  let F:=maximalRealSubfield K
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro q _ hq P hP hle
  haveI: Fact q.Prime:=⟨hq⟩
  haveI: P.IsPrime:=hP.1
  haveI: P.LiesOver (span {(q: ℤ)}):=hP.2
  let f:=P.inertiaDeg ℤ
  have hdeg: q^f = absNorm P:=pow_inertiaDeg q P
  have h:=hc q f hq (P.inertiaDeg_pos _) (hle.trans_lt hb) (by
    rcases rp388 (p:=p) (q:=q) K F (IsQuadraticExtension.finrank_eq_two _ _) P with ⟨he,_⟩|⟨_,k,hk,hk',ho⟩
    · exact Or.inl he
    right
    have hpow:=pow_orderOf_eq_one (q: ZMod p)
    change orderOf (q: ZMod p) = f*k at ho
    rw [ho] at hpow
    rcases (show k = 1 ∨ k = 2 by omega) with h|h
    · rw [h,mul_one] at hpow; simp [pow_mul,hpow]
    · simpa [h] using hpow)
  obtain ⟨r,hr,hv⟩:=List.any_eq_true.mp h
  obtain ⟨hd,hN⟩:=of_decide_eq_true hv
  have hgood:=List.all_eq_true.mp hg r hr
  apply OneTableLE.sound K (unpack p r) hgood P _ (hN.trans_eq hdeg)
  obtain ⟨k,hk⟩:=hd
  rw [hk,Nat.cast_mul]
  apply Ideal.mul_mem_right
  have: (q: ℤ) ∈ P.under ℤ:=(P.over_def (span {(q: ℤ)})) ▸ subset_span (Set.mem_singleton _)
  change algebraMap ℤ (𝓞 F) (q: ℤ) ∈ P at this
  simpa using this
end SReg.Cert.OneTable
end


section
open NumberField NumberField.InfinitePlace IsCyclotomicExtension Module Nat Real
open scoped NumberField
namespace SReg
local instance: Fact (Nat.Prime 31):=⟨by decide⟩
theorem rp476 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {31} ℚ K] (F: Type*) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) :
    ⌊(4 / π) ^ nrComplexPlaces F * ((finrank ℚ F)! / (finrank ℚ F) ^ (finrank ℚ F) * √|discr F|)⌋₊ < 82161:= by
  have hK:=IsCyclotomicExtension.finrank (n:=31) K (Polynomial.cyclotomic.irreducible_rat (by decide))
  rw [← finrank_mul_finrank ℚ F K,h,Nat.totient_prime (by decide: Nat.Prime 31)] at hK
  have hD:=rp385 (p:=31) K F h
  change (discr F).natAbs ≤ 756943935220796320321 at hD
  have hR: |((discr F: ℤ) : ℝ)| ≤ 756943935220796320321:= by exact_mod_cast (Int.natCast_natAbs _).symm.le.trans (Int.ofNat_le.mpr hD)
  have hs: √|((discr F: ℤ) : ℝ)| ≤ 27512614112:=(Real.sqrt_le_iff.mpr ⟨by positivity,hR.trans (by norm_num)⟩)
  apply (Nat.floor_lt (by positivity)).mpr
  rw [IsTotallyReal.nrComplexPlaces_eq_zero,pow_zero,one_mul,show finrank ℚ F = 15 by omega]
  norm_num [Nat.factorial] at * <;> linarith only [hs]
end SReg
end

section
open NumberField NumberField.InfinitePlace IsCyclotomicExtension Module Nat Real
open scoped NumberField
namespace SReg
local instance: Fact (Nat.Prime 17):=⟨by decide⟩
theorem rp477 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {17} ℚ K] (F: Type*) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) :
    ⌊(4 / π) ^ nrComplexPlaces F * ((finrank ℚ F)! / (finrank ℚ F) ^ (finrank ℚ F) * √|discr F|)⌋₊ < 49:= by
  have hK:=IsCyclotomicExtension.finrank (n:=17) K (Polynomial.cyclotomic.irreducible_rat (by decide))
  rw [← finrank_mul_finrank ℚ F K,h,Nat.totient_prime (by decide: Nat.Prime 17)] at hK
  have hD:=rp385 (p:=17) K F h
  change (discr F).natAbs ≤ 410338673 at hD
  have hR: |((discr F: ℤ) : ℝ)| ≤ 410338673:= by exact_mod_cast (Int.natCast_natAbs _).symm.le.trans (Int.ofNat_le.mpr hD)
  have hs: √|((discr F: ℤ) : ℝ)| ≤ 20257:=(Real.sqrt_le_iff.mpr ⟨by positivity,hR.trans (by norm_num)⟩)
  apply (Nat.floor_lt (by positivity)).mpr
  rw [IsTotallyReal.nrComplexPlaces_eq_zero,pow_zero,one_mul,show finrank ℚ F = 8 by omega]
  norm_num [Nat.factorial] at * <;> linarith only [hs]
local instance: Fact (Nat.Prime 19):=⟨by decide⟩
theorem rp478 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {19} ℚ K] (F: Type*) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) :
    ⌊(4 / π) ^ nrComplexPlaces F * ((finrank ℚ F)! / (finrank ℚ F) ^ (finrank ℚ F) * √|discr F|)⌋₊ < 123:= by
  have hK:=IsCyclotomicExtension.finrank (n:=19) K (Polynomial.cyclotomic.irreducible_rat (by decide))
  rw [← finrank_mul_finrank ℚ F K,h,Nat.totient_prime (by decide: Nat.Prime 19)] at hK
  have hD:=rp385 (p:=19) K F h
  change (discr F).natAbs ≤ 16983563041 at hD
  have hR: |((discr F: ℤ) : ℝ)| ≤ 16983563041:= by exact_mod_cast (Int.natCast_natAbs _).symm.le.trans (Int.ofNat_le.mpr hD)
  have hs: √|((discr F: ℤ) : ℝ)| ≤ 130322:=(Real.sqrt_le_iff.mpr ⟨by positivity,hR.trans (by norm_num)⟩)
  apply (Nat.floor_lt (by positivity)).mpr
  rw [IsTotallyReal.nrComplexPlaces_eq_zero,pow_zero,one_mul,show finrank ℚ F = 9 by omega]
  norm_num [Nat.factorial] at * <;> linarith only [hs]
end SReg
end

section
open NumberField NumberField.InfinitePlace IsCyclotomicExtension Module Nat Real Ideal Algebra
open scoped NumberField
namespace SReg
local instance: Fact (Nat.Prime 11):=⟨by decide⟩
theorem rp479 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K] (F: Type*) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) :
    ⌊(4 / π) ^ nrComplexPlaces F * ((finrank ℚ F)! / (finrank ℚ F) ^ (finrank ℚ F) * √|discr F|)⌋₊ < 5:= by
  have hK:=IsCyclotomicExtension.finrank (n:=11) K (Polynomial.cyclotomic.irreducible_rat (by decide))
  rw [← finrank_mul_finrank ℚ F K,h,Nat.totient_prime (by decide: Nat.Prime 11)] at hK
  have hD:=rp385 (p:=11) K F h
  change (discr F).natAbs ≤ 14641 at hD
  have hR: |((discr F: ℤ) : ℝ)| ≤ 14641:= by exact_mod_cast (Int.natCast_natAbs _).symm.le.trans (Int.ofNat_le.mpr hD)
  have hs: √|((discr F: ℤ) : ℝ)| ≤ 122:=(Real.sqrt_le_iff.mpr ⟨by positivity,hR.trans (by norm_num)⟩)
  apply (Nat.floor_lt (by positivity)).mpr
  rw [IsTotallyReal.nrComplexPlaces_eq_zero,pow_zero,one_mul,show finrank ℚ F = 5 by omega]
  norm_num [Nat.factorial] at * <;> linarith only [hs]
theorem rp480 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K] : IsPrincipalIdealRing (𝓞 (maximalRealSubfield K)):= by
  haveI:=IsCyclotomicExtension.Rat.isCMField K (S:={11}) ⟨11,rfl,by decide⟩
  let F:=maximalRealSubfield K
  have hd:=IsQuadraticExtension.finrank_eq_two F K
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro q _ hq P hP hle
  haveI: Fact q.Prime:=⟨hq⟩
  haveI: P.IsPrime:=hP.1
  haveI: P.LiesOver (span {(q: ℤ)}):=hP.2
  have hlt:=lt_of_le_of_lt hle (rp479 K F hd)
  set f:=P.inertiaDeg ℤ with hf
  have hfpos: 0 < f:=P.inertiaDeg_pos ℤ
  exfalso
  exact show False from by
    rcases rp388 (p:=11) (q:=q) K F hd P with ⟨he,hd⟩|⟨_,k,hk,hk',ho⟩
    · rw [he,hf,hd] at hlt; norm_num at hlt
    · have hpow:=pow_orderOf_eq_one (q: ZMod 11)
      change orderOf (q: ZMod 11) = f*k at ho
      have hsq: (q: ZMod 11)^(f*2) = 1:= by
        rw [ho] at hpow
        rcases (show k = 1 ∨ k = 2 by omega) with h|h
        · rw [h,mul_one] at hpow; simp [pow_mul,hpow]
        · simpa [h] using hpow
      have hq' : q < 5:=lt_of_le_of_lt (Nat.le_self_pow hfpos.ne' _) hlt
      have hf' : f < 6:= by by_contra! hh; have:=(Nat.pow_le_pow_left hq.two_le 6).trans (Nat.pow_le_pow_right hq.pos hh); omega
      have C: ∀ a: Fin 5,a.val.Prime → ∀ b: Fin 6,0 < b.val → a.val^b.val < 5 → (a.val: ZMod 11)^(b.val*2)=1 → False:= by decide
      exact C ⟨q,hq'⟩ hq ⟨f,hf'⟩ hfpos hlt hsq

local instance: Fact (Nat.Prime 13):=⟨by decide⟩
theorem rp481 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K] (F: Type*) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F K] [IsScalarTower ℚ F K] (h: finrank F K = 2) :
    ⌊(4 / π) ^ nrComplexPlaces F * ((finrank ℚ F)! / (finrank ℚ F) ^ (finrank ℚ F) * √|discr F|)⌋₊ < 10:= by
  have hK:=IsCyclotomicExtension.finrank (n:=13) K (Polynomial.cyclotomic.irreducible_rat (by decide))
  rw [← finrank_mul_finrank ℚ F K,h,Nat.totient_prime (by decide: Nat.Prime 13)] at hK
  have hD:=rp385 (p:=13) K F h
  change (discr F).natAbs ≤ 371293 at hD
  have hR: |((discr F: ℤ) : ℝ)| ≤ 371293:= by exact_mod_cast (Int.natCast_natAbs _).symm.le.trans (Int.ofNat_le.mpr hD)
  have hs: √|((discr F: ℤ) : ℝ)| ≤ 610:=(Real.sqrt_le_iff.mpr ⟨by positivity,hR.trans (by norm_num)⟩)
  apply (Nat.floor_lt (by positivity)).mpr
  rw [IsTotallyReal.nrComplexPlaces_eq_zero,pow_zero,one_mul,show finrank ℚ F = 6 by omega]
  norm_num [Nat.factorial] at * <;> linarith only [hs]
theorem rp482 (K: Type*) [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K] : IsPrincipalIdealRing (𝓞 (maximalRealSubfield K)):= by
  haveI:=IsCyclotomicExtension.Rat.isCMField K (S:={13}) ⟨13,rfl,by decide⟩
  let F:=maximalRealSubfield K
  have hd:=IsQuadraticExtension.finrank_eq_two F K
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro q _ hq P hP hle
  haveI: Fact q.Prime:=⟨hq⟩
  haveI: P.IsPrime:=hP.1
  haveI: P.LiesOver (span {(q: ℤ)}):=hP.2
  have hlt:=lt_of_le_of_lt hle (rp481 K F hd)
  set f:=P.inertiaDeg ℤ with hf
  have hfpos: 0 < f:=P.inertiaDeg_pos ℤ
  exfalso
  exact show False from by
    rcases rp388 (p:=13) (q:=q) K F hd P with ⟨he,hd⟩|⟨_,k,hk,hk',ho⟩
    · rw [he,hf,hd] at hlt; norm_num at hlt
    · have hpow:=pow_orderOf_eq_one (q: ZMod 13)
      change orderOf (q: ZMod 13) = f*k at ho
      have hsq: (q: ZMod 13)^(f*2) = 1:= by
        rw [ho] at hpow
        rcases (show k = 1 ∨ k = 2 by omega) with h|h
        · rw [h,mul_one] at hpow; simp [pow_mul,hpow]
        · simpa [h] using hpow
      have hq' : q < 10:=lt_of_le_of_lt (Nat.le_self_pow hfpos.ne' _) hlt
      have hf' : f < 6:= by by_contra! hh; have:=(Nat.pow_le_pow_left hq.two_le 6).trans (Nat.pow_le_pow_right hq.pos hh); omega
      have C: ∀ a: Fin 10,a.val.Prime → ∀ b: Fin 6,0 < b.val → a.val^b.val < 10 → (a.val: ZMod 13)^(b.val*2)=1 → False:= by decide
      exact C ⟨q,hq'⟩ hq ⟨f,hf'⟩ hfpos hlt hsq

end SReg
end

open NumberField IsCyclotomicExtension Polynomial Nat
open scoped NumberField
namespace SReg
lemma of_pid (p: ℕ) [hp: Fact p.Prime] (h: IsPrincipalIdealRing (𝓞 (CyclotomicField p ℚ))) : p ∈ RegularPrimes.regularPrimes:= by
  refine ⟨hp.out,?_⟩
  change p.Coprime (classNumber (CyclotomicField p ℚ))
  rw [classNumber_eq_one_iff.mpr h]
  simp
local instance (p: ℕ) [NeZero p] : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ):=CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
local instance: Fact (Nat.Prime 5):=⟨by decide⟩
lemma three: 3 ∈ RegularPrimes.regularPrimes:=of_pid 3 (IsCyclotomicExtension.Rat.three_pid _)
lemma five: 5 ∈ RegularPrimes.regularPrimes:=of_pid 5 (IsCyclotomicExtension.Rat.five_pid _)
lemma two: 2 ∈ RegularPrimes.regularPrimes:= by
  let K:=CyclotomicField 2 ℚ
  apply of_pid
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [IsCyclotomicExtension.Rat.discr_prime 2 K,IsCyclotomicExtension.finrank (n:=2) K (cyclotomic.irreducible_rat (by decide)),IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 2,Nat.totient_prime Nat.prime_two]
  norm_num
open Module NumberField.InfinitePlace Real Ideal
local instance: Fact (Nat.Prime 7):=⟨by decide⟩
lemma seven: 7 ∈ RegularPrimes.regularPrimes:= by
  let K:=CyclotomicField 7 ℚ
  apply of_pid
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hm hp P hP hle
  have hb: ⌊(4 / π) ^ nrComplexPlaces K * ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)⌋₊ < 5:= by
    apply (Nat.floor_lt (by positivity)).mpr
    rw [IsCyclotomicExtension.Rat.discr_prime 7 K,IsCyclotomicExtension.finrank (n:=7) K (cyclotomic.irreducible_rat (by decide)),IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 7,Nat.totient_prime (by decide: Nat.Prime 7)]
    norm_num [Nat.factorial]
    have hπ: 4 / π ≤ (4 / 3: ℝ):= by gcongr; exact pi_gt_three.le
    have hs: √(16807: ℝ) ≤ 130:= by rw [Real.sqrt_le_iff]; norm_num
    nlinarith only [mul_le_mul (pow_le_pow_left₀ (by positivity) hπ 3) (mul_le_mul_of_nonneg_left hs (by positivity: (0:ℝ) ≤ 720 / 46656)) (by positivity: 0 ≤ 720 / 46656 * √(16807:ℝ)) (by positivity: (0:ℝ) ≤ (4/3)^3)]
  have hlt:=lt_of_le_of_lt hle hb
  have hpl:=(Finset.mem_Icc.mp hm).2.trans_lt hb
  haveI: Fact p.Prime:=⟨hp⟩
  haveI: P.IsPrime:=hP.1
  haveI: P.LiesOver (span {(p: ℤ)}):=hP.2
  have h2:=hp.two_le
  have hd: ¬ p ∣ 7:= by interval_cases p <;> decide
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m:=7) p K P hd] at hlt
  have h4: p ≠ 4:= by rintro rfl; exact (by decide: ¬Nat.Prime 4) hp
  have hc: p = 2 ∨ p = 3:= by omega
  rcases hc with rfl | rfl
  · have ho: orderOf (2: ZMod 7) = 3:=orderOf_eq_prime (by decide) (by decide)
    norm_num at hlt
    rw [ho] at hlt; omega
  · have ho: 2 ≤ orderOf (3: ZMod 7):= by
      have hpos:=orderOf_pos_iff.mpr (show IsOfFinOrder (3: ZMod 7) from ⟨6,by decide,by decide⟩)
      have hn: orderOf (3: ZMod 7) ≠ 1:= by rw [Ne,orderOf_eq_one_iff]; decide
      omega
    norm_num at hlt
    have:=Nat.pow_le_pow_right (by decide: 0 < 3) ho
    omega
end SReg

open scoped NumberField
open NumberField KummerCriterion
namespace SReg
lemma rp483 (p: ℕ) [hp: Fact p.Prime] (ho: p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    (hr: IsPrincipalIdealRing (𝓞 (maximalRealSubfield (CyclotomicField p ℚ))))
    (hm: ¬ p ∣ hMinus (CyclotomicField p ℚ)) : p ∈ RegularPrimes.regularPrimes:= by
  let K:=CyclotomicField p ℚ
  have h1: hPlus K = 1:=classNumber_eq_one_iff.mpr hr
  refine ⟨hp.out,hp.out.coprime_iff_not_dvd.mpr ?_⟩
  change ¬ p ∣ h K
  change ¬ p ∣ h K / hPlus K at hm
  simpa [h1] using hm
end SReg

open scoped NumberField
open NumberField KummerCriterion SReg SReg.Cert.OneTable

theorem SReg.regular11: 11 ∈ RegularPrimes.regularPrimes:= by
  letI: Fact (Nat.Prime 11):=⟨by decide⟩
  let K:=CyclotomicField 11 ℚ
  letI: IsCyclotomicExtension {11} ℚ K:=CyclotomicField.isCyclotomicExtension 11 ℚ
  letI: IsCMField K:=rp64 11 (by decide) K
  exact rp483 11 (by decide) (rp480 K) (SignFree.rp376 11 K (by decide) (by decide))

theorem SReg.regular13: 13 ∈ RegularPrimes.regularPrimes:= by
  letI: Fact (Nat.Prime 13):=⟨by decide⟩
  let K:=CyclotomicField 13 ℚ
  letI: IsCyclotomicExtension {13} ℚ K:=CyclotomicField.isCyclotomicExtension 13 ℚ
  letI: IsCMField K:=rp64 13 (by decide) K
  exact rp483 13 (by decide) (rp482 K) (SignFree.rp376 13 K (by decide) (by decide))

theorem SReg.regular17: 17 ∈ RegularPrimes.regularPrimes:= by
  letI: Fact (Nat.Prime 17):=⟨by decide⟩
  let K:=CyclotomicField 17 ℚ
  letI: IsCyclotomicExtension {17} ℚ K:=CyclotomicField.isCyclotomicExtension 17 ℚ
  letI: IsCMField K:=rp64 17 (by decide) K
  exact rp483 17 (by decide) (pid K rows17 all17 (rp477 K _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)) cover17) (SignFree.rp376 17 K (by decide) (by decide))

theorem SReg.regular19: 19 ∈ RegularPrimes.regularPrimes:= by
  letI: Fact (Nat.Prime 19):=⟨by decide⟩
  let K:=CyclotomicField 19 ℚ
  letI: IsCyclotomicExtension {19} ℚ K:=CyclotomicField.isCyclotomicExtension 19 ℚ
  letI: IsCMField K:=rp64 19 (by decide) K
  exact rp483 19 (by decide) (pid K rows19 all19 (rp478 K _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)) cover19) (SignFree.rp376 19 K (by decide) (by decide))

theorem SReg.regular23: 23 ∈ RegularPrimes.regularPrimes:= by
  letI: Fact (Nat.Prime 23):=⟨by decide⟩
  let K:=CyclotomicField 23 ℚ
  letI: IsCyclotomicExtension {23} ℚ K:=CyclotomicField.isCyclotomicExtension 23 ℚ
  letI: IsCMField K:=rp64 23 (by decide) K
  exact rp483 23 (by decide) (pid K rows23 all23 (rp386 K _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)) cover23) (SignFree.rp376 23 K (by decide) (by decide))

theorem SReg.regular29: 29 ∈ RegularPrimes.regularPrimes:= by
  letI: Fact (Nat.Prime 29):=⟨by decide⟩
  let K:=CyclotomicField 29 ℚ
  letI: IsCyclotomicExtension {29} ℚ K:=CyclotomicField.isCyclotomicExtension 29 ℚ
  letI: IsCMField K:=rp64 29 (by decide) K
  exact rp483 29 (by decide) (pid K rows29 all29 (rp387 K _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)) cover29) (SignFree.rp376 29 K (by decide) (by decide))

theorem SReg.regular31: 31 ∈ RegularPrimes.regularPrimes:= by
  letI: Fact (Nat.Prime 31):=⟨by decide⟩
  let K:=CyclotomicField 31 ℚ
  letI: IsCyclotomicExtension {31} ℚ K:=CyclotomicField.isCyclotomicExtension 31 ℚ
  letI: IsCMField K:=rp64 31 (by decide) K
  exact rp483 31 (by decide) (pid K rows31 all31 (rp476 K _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)) cover31) (SignFree.rp376 31 K (by decide) (by decide))

theorem OMA.solution: type_of% @RegularPrimes.small_regular_primes:= by
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact SReg.two
  · exact SReg.three
  · exact SReg.five
  · exact SReg.seven
  · exact SReg.regular11
  · exact SReg.regular13
  · exact SReg.regular17
  · exact SReg.regular19
  · exact SReg.regular23
  · exact SReg.regular29
  · exact SReg.regular31
