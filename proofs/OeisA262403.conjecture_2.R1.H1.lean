import OMAReductions.R_OeisA262403_conjecture_2_R1

/-! Finite direction of hayalows' reduction of Sun's A262403 conjecture.
The table records the prime counts at successive triangular numbers.
Each interval is sieved by testing coprimality with the factorial of 514. -/

namespace A262403Certificate
open OeisA262403

private def factorialBound : ℕ := 91689872723279164740120011363026014166754063738139320893704444853319173667447997136810291975722063324544222780736743356492476638805239937555518421210870638253347861735038853583892986477120019255949333468262022584244140856003583321199240164306469890288696416227026819586929050020407715300718983717120486510447706440976708416806529957661003211458490463358033409242740240165304961394069677598888222390194323316943864821195033595029076934426671394386924031339652499568137566499150062077800373072357030544869298683552560122141912442884871317723472040737580776748552925461908999154972068902826059548512208747716103206188604986153751920092047929770292233550742562802191686218770891478850713050125578646920397101533855306777545020150943551614687330435663308263742699530408500553242014048467649157575305138522114979501196893489612955001986272145678813316437961229020348090966984730532722281294438938323008198816051521516544068058717743445240344357329797679113116014192888934454173281218992722391787543746833743281793585239866353886389514459130101307015168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private theorem factorialBound_eq : factorialBound = Nat.factorial 514 := by decide +kernel

private def smallPrime (n : ℕ) : Bool := Nat.testBit 1703806605896072823853452820875856471690324421502329734630516674131882609769400962334582631898191304282096542762193211716358712101421767999181276463114412 n

private def test (n : ℕ) : Bool :=
  if n ≤ 514 then smallPrime n else decide (n.Coprime factorialBound)

private theorem test_eq (n : ℕ) (hn : n ≤ 264628) : test n = true ↔ n.Prime := by
  unfold test
  split
  next h =>
    have small : ∀ i : Fin 515, smallPrime i.val = true ↔ i.val.Prime := by decide +kernel
    exact small ⟨n, by omega⟩
  next h =>
    rw [decide_eq_true_eq, factorialBound_eq]
    constructor
    · intro hc
      by_contra hnp
      have hs := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
      have hb : n.minFac ≤ 514 := by nlinarith
      have hd := Nat.dvd_factorial (Nat.minFac_pos n) hb
      exact (Nat.minFac_prime (by omega : n ≠ 1)).not_dvd_one
        (hc ▸ Nat.dvd_gcd (Nat.minFac_dvd n) hd)
    · exact fun hp => hp.coprime_iff_not_dvd.mpr (fun hd => h ((hp.dvd_factorial).mp hd))

private def words : Array ℕ := #[19231450782760683968084954268349733401619062436295080381587882633164215245635415496388672697778393296114321757007683919978034582166504754468045952385024, 62399935636153742255816266187534146847141294759489498022690716164469643201386699157889473518824979349722833130919515141311139800917481520206066074648675, 126232020246755364501085771234417470294685376700120615660039400655119421047844779590883296018263831810300144784893745526183339607191929702734773990195512, 209090968727505241937256961086075651041596706132110817214663160879838491244023933446361968281409718480032410386979614594863668545996472788291444260471413, 310567616617471469187386054774031408430716361509475758269111175195954755682428625037649083299233233046574168800554195500261671451049145534773531776713739, 429843597534331617737604283392915910278976999410115267790879994325803856845171000983067618886557789004076240367846331351218782836249705331609397900674556, 564463840426236084662420683224981139171397685626720825082844570667677129299599453379128148791315296928550092694137929769198452112127511689463454554982474, 716678807578419699572871931153293116346464009226202079079137529792462413921706744111793276239507661149174522007871298658853504722679827368115830455995101, 884647219897166111970316288715120146984799025004960148893761602816241716562667441757628290766360178389437953035521600608073502633249209255857775582449093, 1068778257451673628335968369832205279255823636744010591993894145619193831444230339044379176811040611931794330831608845061639889490442393509641837893980416, 1271322366919005949016125061325255164203492172636404091843045024938652516994560084442635556212133499728475523516336329072089337524730445011537025514935430, 1485323565161218102593217908933248725106792978376000256173719910895141535652883714468978845440205501777449899686027415334388804987817303096895046875682915, 1717124049603524298961994694989866285560627682788998034643904968879335160154072118060322384375480283840619770085997279055183375358961689687310646179404927, 1964064218472841147536309007846865644801735617499482333735377967736973859045893513100675186357005043212823074236349522027389499834688589221339489123705069, 2223484373220736969295428998987248887378356922937504173498894555985034286343584176126870384715018778013376992987487456675704051468993080155538223755109801, 2502545161943007215798695785394504720632620932013149082947022064978166137527053086516922646031626434848265387119088391037571537097084509749815969877731997, 2792858415065800111899637534214688720172032311312000194504261433756531334358865137724011757255999130678568349976656309813363510883697271714338576684167151, 3098106743850560830450043677893708079070925168351476643521623561262115360115481470073343149445236407666563909687144270213895104049198348860526426057225597, 3417880965104341868531550900986063023032458497819956016079035690730154604440339199095743216865321443327488389145975195429442710998786139699388850517392209, 3752385665741851572155157988979536670427060663228985131848210961176794305668425990257567633231505334378308245303100109823404130838752462220536749656523125, 4103462159197231222573834864085662185644847644003571527406458594139741327742953269443952865111806834062500484150476130919638243938250214425255412086228951, 4466200281513922509668794415532460509682422281483090599352546990738600640701701755737358229574188679664497027225299705662325393449211586422993744799682193, 13946872725543551478447245258001647701854828592952107912336292839571911025342539161373792434472970350018388440470914]
private def value (i : ℕ) := (words[i/32]! >>> (16*(i%32))) % 65536
private def increment (i : ℕ) :=
  ((List.range (i+1)).countP (fun j => test (Nat.triangular i + 1 + j)))

private theorem count_step (i : ℕ) (hi : i < 727) :
    primeCountTriangular (i+1) = primeCountTriangular i + increment i := by
  have htri : Nat.triangular (i+1) + 1 = Nat.triangular i + 1 + (i+1) := by
    unfold Nat.triangular
    rw [show (i+1)*(i+1+1) = i*(i+1) + (i+1)*2 by ring, Nat.add_mul_div_right _ _ (by decide)]
    omega
  change Nat.count Nat.Prime (Nat.triangular (i+1)+1) = Nat.count Nat.Prime (Nat.triangular i+1) + _
  rw [htri, Nat.count_add]
  congr 1
  unfold increment Nat.count
  apply List.countP_congr
  intro j hj
  have hlt := List.mem_range.mp hj
  have hbound : Nat.triangular i + 1 + j ≤ 264628 := by
    unfold Nat.triangular
    have := Nat.mul_le_mul (show i ≤ 726 by omega) (show i+1 ≤ 727 by omega)
    omega
  simpa only [decide_eq_true_eq] using (test_eq _ hbound).symm

private def verify (i : ℕ) : Bool := decide (value (i+1) = value i + increment i)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block0 : ∀ j : Fin 16, verify (0+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block16 : ∀ j : Fin 16, verify (16+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block32 : ∀ j : Fin 16, verify (32+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block48 : ∀ j : Fin 16, verify (48+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block64 : ∀ j : Fin 16, verify (64+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block80 : ∀ j : Fin 16, verify (80+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block96 : ∀ j : Fin 16, verify (96+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block112 : ∀ j : Fin 16, verify (112+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block128 : ∀ j : Fin 16, verify (128+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block144 : ∀ j : Fin 16, verify (144+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block160 : ∀ j : Fin 16, verify (160+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block176 : ∀ j : Fin 16, verify (176+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block192 : ∀ j : Fin 16, verify (192+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block208 : ∀ j : Fin 16, verify (208+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block224 : ∀ j : Fin 16, verify (224+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block240 : ∀ j : Fin 16, verify (240+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block256 : ∀ j : Fin 16, verify (256+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block272 : ∀ j : Fin 16, verify (272+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block288 : ∀ j : Fin 16, verify (288+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block304 : ∀ j : Fin 16, verify (304+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block320 : ∀ j : Fin 16, verify (320+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block336 : ∀ j : Fin 16, verify (336+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block352 : ∀ j : Fin 16, verify (352+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block368 : ∀ j : Fin 16, verify (368+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block384 : ∀ j : Fin 16, verify (384+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block400 : ∀ j : Fin 16, verify (400+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block416 : ∀ j : Fin 16, verify (416+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block432 : ∀ j : Fin 16, verify (432+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block448 : ∀ j : Fin 16, verify (448+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block464 : ∀ j : Fin 16, verify (464+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block480 : ∀ j : Fin 16, verify (480+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block496 : ∀ j : Fin 16, verify (496+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block512 : ∀ j : Fin 16, verify (512+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block528 : ∀ j : Fin 16, verify (528+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block544 : ∀ j : Fin 16, verify (544+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block560 : ∀ j : Fin 16, verify (560+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block576 : ∀ j : Fin 16, verify (576+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block592 : ∀ j : Fin 16, verify (592+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block608 : ∀ j : Fin 16, verify (608+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block624 : ∀ j : Fin 16, verify (624+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block640 : ∀ j : Fin 16, verify (640+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block656 : ∀ j : Fin 16, verify (656+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block672 : ∀ j : Fin 16, verify (672+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block688 : ∀ j : Fin 16, verify (688+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block704 : ∀ j : Fin 16, verify (704+j.val) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem block720 : ∀ j : Fin 7, verify (720+j.val) = true := by decide +kernel
private theorem verified (i : ℕ) (hi : i < 727) : verify i = true := by
  by_cases h0 : i < 16
  · have e := block0 ⟨i-0, by omega⟩
    simpa only [show 0+(i-0)=i by omega] using e
  by_cases h16 : i < 32
  · have e := block16 ⟨i-16, by omega⟩
    simpa only [show 16+(i-16)=i by omega] using e
  by_cases h32 : i < 48
  · have e := block32 ⟨i-32, by omega⟩
    simpa only [show 32+(i-32)=i by omega] using e
  by_cases h48 : i < 64
  · have e := block48 ⟨i-48, by omega⟩
    simpa only [show 48+(i-48)=i by omega] using e
  by_cases h64 : i < 80
  · have e := block64 ⟨i-64, by omega⟩
    simpa only [show 64+(i-64)=i by omega] using e
  by_cases h80 : i < 96
  · have e := block80 ⟨i-80, by omega⟩
    simpa only [show 80+(i-80)=i by omega] using e
  by_cases h96 : i < 112
  · have e := block96 ⟨i-96, by omega⟩
    simpa only [show 96+(i-96)=i by omega] using e
  by_cases h112 : i < 128
  · have e := block112 ⟨i-112, by omega⟩
    simpa only [show 112+(i-112)=i by omega] using e
  by_cases h128 : i < 144
  · have e := block128 ⟨i-128, by omega⟩
    simpa only [show 128+(i-128)=i by omega] using e
  by_cases h144 : i < 160
  · have e := block144 ⟨i-144, by omega⟩
    simpa only [show 144+(i-144)=i by omega] using e
  by_cases h160 : i < 176
  · have e := block160 ⟨i-160, by omega⟩
    simpa only [show 160+(i-160)=i by omega] using e
  by_cases h176 : i < 192
  · have e := block176 ⟨i-176, by omega⟩
    simpa only [show 176+(i-176)=i by omega] using e
  by_cases h192 : i < 208
  · have e := block192 ⟨i-192, by omega⟩
    simpa only [show 192+(i-192)=i by omega] using e
  by_cases h208 : i < 224
  · have e := block208 ⟨i-208, by omega⟩
    simpa only [show 208+(i-208)=i by omega] using e
  by_cases h224 : i < 240
  · have e := block224 ⟨i-224, by omega⟩
    simpa only [show 224+(i-224)=i by omega] using e
  by_cases h240 : i < 256
  · have e := block240 ⟨i-240, by omega⟩
    simpa only [show 240+(i-240)=i by omega] using e
  by_cases h256 : i < 272
  · have e := block256 ⟨i-256, by omega⟩
    simpa only [show 256+(i-256)=i by omega] using e
  by_cases h272 : i < 288
  · have e := block272 ⟨i-272, by omega⟩
    simpa only [show 272+(i-272)=i by omega] using e
  by_cases h288 : i < 304
  · have e := block288 ⟨i-288, by omega⟩
    simpa only [show 288+(i-288)=i by omega] using e
  by_cases h304 : i < 320
  · have e := block304 ⟨i-304, by omega⟩
    simpa only [show 304+(i-304)=i by omega] using e
  by_cases h320 : i < 336
  · have e := block320 ⟨i-320, by omega⟩
    simpa only [show 320+(i-320)=i by omega] using e
  by_cases h336 : i < 352
  · have e := block336 ⟨i-336, by omega⟩
    simpa only [show 336+(i-336)=i by omega] using e
  by_cases h352 : i < 368
  · have e := block352 ⟨i-352, by omega⟩
    simpa only [show 352+(i-352)=i by omega] using e
  by_cases h368 : i < 384
  · have e := block368 ⟨i-368, by omega⟩
    simpa only [show 368+(i-368)=i by omega] using e
  by_cases h384 : i < 400
  · have e := block384 ⟨i-384, by omega⟩
    simpa only [show 384+(i-384)=i by omega] using e
  by_cases h400 : i < 416
  · have e := block400 ⟨i-400, by omega⟩
    simpa only [show 400+(i-400)=i by omega] using e
  by_cases h416 : i < 432
  · have e := block416 ⟨i-416, by omega⟩
    simpa only [show 416+(i-416)=i by omega] using e
  by_cases h432 : i < 448
  · have e := block432 ⟨i-432, by omega⟩
    simpa only [show 432+(i-432)=i by omega] using e
  by_cases h448 : i < 464
  · have e := block448 ⟨i-448, by omega⟩
    simpa only [show 448+(i-448)=i by omega] using e
  by_cases h464 : i < 480
  · have e := block464 ⟨i-464, by omega⟩
    simpa only [show 464+(i-464)=i by omega] using e
  by_cases h480 : i < 496
  · have e := block480 ⟨i-480, by omega⟩
    simpa only [show 480+(i-480)=i by omega] using e
  by_cases h496 : i < 512
  · have e := block496 ⟨i-496, by omega⟩
    simpa only [show 496+(i-496)=i by omega] using e
  by_cases h512 : i < 528
  · have e := block512 ⟨i-512, by omega⟩
    simpa only [show 512+(i-512)=i by omega] using e
  by_cases h528 : i < 544
  · have e := block528 ⟨i-528, by omega⟩
    simpa only [show 528+(i-528)=i by omega] using e
  by_cases h544 : i < 560
  · have e := block544 ⟨i-544, by omega⟩
    simpa only [show 544+(i-544)=i by omega] using e
  by_cases h560 : i < 576
  · have e := block560 ⟨i-560, by omega⟩
    simpa only [show 560+(i-560)=i by omega] using e
  by_cases h576 : i < 592
  · have e := block576 ⟨i-576, by omega⟩
    simpa only [show 576+(i-576)=i by omega] using e
  by_cases h592 : i < 608
  · have e := block592 ⟨i-592, by omega⟩
    simpa only [show 592+(i-592)=i by omega] using e
  by_cases h608 : i < 624
  · have e := block608 ⟨i-608, by omega⟩
    simpa only [show 608+(i-608)=i by omega] using e
  by_cases h624 : i < 640
  · have e := block624 ⟨i-624, by omega⟩
    simpa only [show 624+(i-624)=i by omega] using e
  by_cases h640 : i < 656
  · have e := block640 ⟨i-640, by omega⟩
    simpa only [show 640+(i-640)=i by omega] using e
  by_cases h656 : i < 672
  · have e := block656 ⟨i-656, by omega⟩
    simpa only [show 656+(i-656)=i by omega] using e
  by_cases h672 : i < 688
  · have e := block672 ⟨i-672, by omega⟩
    simpa only [show 672+(i-672)=i by omega] using e
  by_cases h688 : i < 704
  · have e := block688 ⟨i-688, by omega⟩
    simpa only [show 688+(i-688)=i by omega] using e
  by_cases h704 : i < 720
  · have e := block704 ⟨i-704, by omega⟩
    simpa only [show 704+(i-704)=i by omega] using e
  have e := block720 ⟨i-720, by omega⟩
  simpa only [show 720+(i-720)=i by omega] using e
private theorem table_eq (i : ℕ) (hi : i ≤ 727) : primeCountTriangular i = value i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [count_step _ (by omega), ih (by omega)]
    exact (of_decide_eq_true (verified i (by omega))).symm

private def pairs (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 2 (n-2), ((Finset.Icc (k+1) (n-1)).filter (fun m =>
    value n = value k + value m)).card

private theorem pairs_eq (n : ℕ) (hn : n ≤ 727) : a n = pairs n := by
  unfold a pairs
  apply Finset.sum_congr rfl
  intro k hk
  have h := Finset.mem_Icc.mp hk
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m hm
  have h' := Finset.mem_Icc.mp hm
  rw [table_eq n hn, table_eq k (by omega), table_eq m (by omega)]

private def locate (x : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, l, _ => l
  | fuel+1, l, r =>
    let m := (l+r)/2
    if value m < x then locate x fuel (m+1) r else locate x fuel l m

private def indexOf (x : ℕ) := locate x 10 0 727

set_option maxRecDepth 8000 in
private theorem index_ok : ∀ i : Fin 728, 2 ≤ i.val → indexOf (value i.val) = i.val := by
  decide +kernel

private def uniqueRow (n u v : ℕ) : Prop :=
  ∀ k : Fin n, let m := indexOf (value n - value k.val)
               2 ≤ k.val → k.val < m → m < n → value n = value k.val + value m →
                 k.val = u ∧ m = v

private theorem pair_certificate (n u v : ℕ) (hn : n ≤ 727)
    (hu : 2 ≤ u) (huv : u < v) (hv : v < n) (hw : value n = value u + value v)
    (cert : uniqueRow n u v) : pairs n = 1 := by
  have huniq (k m : ℕ) (hk : 2 ≤ k) (hkm : k < m) (hm : m < n)
      (h : value n = value k + value m) : k = u ∧ m = v := by
    have hi := index_ok ⟨m, by omega⟩ (show 2 ≤ m by omega)
    change indexOf (value m) = m at hi
    have he : indexOf (value n - value k) = m := by rwa [h, Nat.add_sub_cancel_left]
    have hc := cert ⟨k, by omega⟩
    dsimp only at hc
    rw [he] at hc
    exact hc hk hkm hm h
  unfold pairs
  rw [Finset.sum_eq_single u]
  · have he : ((Finset.Icc (u+1) (n-1)).filter (fun m => value n = value u + value m)) = {v} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1,h2⟩, h3⟩
        exact (huniq u m hu (by omega) (by omega) h3).2
      · rintro rfl
        exact ⟨⟨by omega, by omega⟩, hw⟩
    rw [he, Finset.card_singleton]
  · intro k hk hne
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hm
    have h3 := Finset.mem_Icc.mp h1
    exact hne (huniq k m (Finset.mem_Icc.mp hk).1 (by omega) (by omega) h2).1
  · intro h
    exact False.elim (h (Finset.mem_Icc.mpr ⟨hu, by omega⟩))

set_option maxRecDepth 8000 in
private theorem pair5 : pairs 5 = 1 := by
  apply pair_certificate 5 2 4 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair6 : pairs 6 = 1 := by
  apply pair_certificate 6 2 5 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair7 : pairs 7 = 1 := by
  apply pair_certificate 7 3 5 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair10 : pairs 10 = 1 := by
  apply pair_certificate 10 2 9 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair12 : pairs 12 = 1 := by
  apply pair_certificate 12 3 11 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair32 : pairs 32 = 1 := by
  apply pair_certificate 32 7 30 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair38 : pairs 38 = 1 := by
  apply pair_certificate 38 16 32 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair445 : pairs 445 = 1 := by
  apply pair_certificate 445 232 362 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

set_option maxRecDepth 8000 in
private theorem pair727 : pairs 727 = 1 := by
  apply pair_certificate 727 458 532 (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  unfold uniqueRow
  decide +kernel

end A262403Certificate

theorem OMA.solution : OMA.R_OeisA262403_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [A262403Certificate.pairs_eq _ (by decide)]
  · exact A262403Certificate.pair5
  · exact A262403Certificate.pair6
  · exact A262403Certificate.pair7
  · exact A262403Certificate.pair10
  · exact A262403Certificate.pair12
  · exact A262403Certificate.pair32
  · exact A262403Certificate.pair38
  · exact A262403Certificate.pair445
  · exact A262403Certificate.pair727
