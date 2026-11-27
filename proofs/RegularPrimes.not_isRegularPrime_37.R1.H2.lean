import OMAReductions.R_RegularPrimes_not_isRegularPrime_37_R1

-- Credit: @marcusbuffett
-- Port of two public open-math-agents proofs: @chris01-dev's explicit order-37 class
-- certificate (7ec98bdb3374), and @VinnyMo's Bernoulli computation (8f5255d27ddd).
-- At this specific prime the two independent certificates refute both sides of the criterion.

/-!
# 37 is irregular: a direct certificate, without Kummer's criterion

Write `K = ℚ(ζ)` with `ζ` a primitive 37-th root of unity and `R = 𝓞 K = ℤ[ζ]`.
We show that `37` divides the class number of `K` by exhibiting an ideal class of order `37`.

* `al` is an explicit element `α ∈ R` and `I = (149, α)` is a prime above `149`.  The identities
  `α * κ = 149 ^ 37` and `κ * x + α * y = 1` (checked by the kernel as polynomial identities modulo
  the 37-th cyclotomic polynomial) give `I ^ 37 = (α)`.
* If the class number were prime to `37`, then `I = (β)` would be principal and `α = u * β ^ 37`
  for a unit `u`.
* By Kronecker's theorem `u / conj u` is a root of unity, so `u = ± ζ ^ m * conj u`.  Hence, with
  `s : ζ ↦ ζ ^ 2` and `c : ζ ↦ ζ⁻¹`, the unit cancels from
  `s α * (c α) ^ 2` versus `s (c α) * α ^ 2`: their quotient is a `37`-th power in `K`.
* Reducing modulo the prime `(223, ζ - 2)` (note `223 ∣ 2 ^ 37 - 1`) and raising to the power
  `(223 - 1) / 37 = 6` gives an equality in `ZMod 223` which is false by direct computation.
-/

namespace OMA.Irr37

open NumberField

/-- Horner evaluation of an integer coefficient list at `z`. -/
def ev {A : Type*} [CommRing A] (z : A) : List ℤ → A
  | [] => 0
  | a :: L => (a : A) + z * ev z L

/-- Horner evaluation over `ℤ`, for kernel computation. -/
def evZ (r : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: L => a + r * evZ r L

def padd : List ℤ → List ℤ → List ℤ
  | [], M => M
  | a :: L, [] => a :: L
  | a :: L, b :: M => (a + b) :: padd L M

def psmul (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: L => (c * a) :: psmul c L

def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: L, M => padd (psmul a M) (0 :: pmul L M)

lemma ev_padd {A : Type*} [CommRing A] (z : A) :
    ∀ L M : List ℤ, ev z (padd L M) = ev z L + ev z M
  | [], M => by simp [padd, ev]
  | a :: L, [] => by simp [padd, ev]
  | a :: L, b :: M => by
    simp only [padd, ev, ev_padd z L M, Int.cast_add]
    ring

lemma ev_psmul {A : Type*} [CommRing A] (z : A) (c : ℤ) :
    ∀ L : List ℤ, ev z (psmul c L) = (c : A) * ev z L
  | [] => by simp [psmul, ev]
  | a :: L => by
    simp only [psmul, ev, ev_psmul z c L, Int.cast_mul]
    ring

lemma ev_pmul {A : Type*} [CommRing A] (z : A) :
    ∀ L M : List ℤ, ev z (pmul L M) = ev z L * ev z M
  | [], M => by simp [pmul, ev]
  | a :: L, M => by
    simp only [pmul, ev, ev_padd, ev_psmul, ev_pmul z L M, Int.cast_zero]
    ring

lemma map_ev {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (z : A) :
    ∀ L : List ℤ, f (ev z L) = ev (f z) L
  | [] => by simp [ev]
  | a :: L => by simp [ev, map_ev f z L]

lemma ev_cast {A : Type*} [CommRing A] (r : ℤ) :
    ∀ L : List ℤ, ev (r : A) L = ((evZ r L : ℤ) : A)
  | [] => by simp [ev, evZ]
  | a :: L => by simp [ev, evZ, ev_cast r L]

def phi : List ℤ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1]

lemma ev_phi {A : Type*} [CommRing A] (z : A) : ev z phi = ∑ i ∈ Finset.range 37, z ^ i := by
  simp only [phi, ev, Finset.sum_range_succ, Finset.sum_range_zero, Int.cast_one]
  ring

/- ### The certificate -/

def al : List ℤ :=
  [128, -23, 87, 40, 60, 38, 12, 24, 48, 35, 115, 8, 39, 54, 107, 37, 146, -68, 180, 73, 18, 108,
   -43, 59, 155, 49, 96, 46, -38, 145, 20, 55, 65, 44, 21, 102]

def k1 : List ℤ :=
  [1732012057621328699160568164021648971940908298499370938266172707220753172631269,
   3473412641813239207087634040824632780282915847032469472645612335846807734561161,
   1469322449562727578014392708275331896409077011041626837495158739946605831736367,
   238124529887812213020683233104483661282309163630855691216476169865805631454075,
   1925021078456989417017033919410752487030176938348137231616075692250620142910928,
   2451443507837409933628285136743111722306027257544452713448805248823802327503494,
   1442497178049095248422112680368127235510938371227939686787279033545934383737586,
   584008051224441666438146927289180601728435595191854665518665984375782472531390,
   1241456657249235519478964777637535073882674187330713891222501041749695934685220,
   2050696496137804334559624272845732536332342687839520426475425893045375784573749,
   2051715035329447473636312900939468472356936467246185477005206079290417677641514,
   1024441092375254260973219013361823482864673419504635595604888733526174283130032,
   1191352081655003587266102203622404963504957869775122586241235699368629203061714,
   2753109628947098172790255293637107711512918537544635768911685315748623810757436,
   2216163457946015957906258121114067391389123556562299341354137875103506852530302,
   409134927168504302370612747469380211078071413979257073174425476664139768841303,
   551136392836304887839238309372197734495898736402938397121734463902359944127681,
   1952675861525781475368130519941970118149032778402432744344123140857993419841091,
   2657508079667197535776067865167600079920401524728734948516930179590348540760095,
   1426221446708876361586661040877428853007556164965420476348087356462332451585913,
   628963552650011673084176884291905042764616386060564486469918539891970337869827,
   2612132888450127620017548105011013023992310766007098009717863704344781809251150,
   2887079838372179771308456191059874630215668800618729306519980555789841624517077,
   1100488310965828550369943651613327255654516344046697152407207776797942956309120,
   465680170834160595072861793186415787461409750139246392361695593567679721774728,
   2351402286332875075215188897579843953448214205786344156949548188381993258992410,
   2267257444179780835144465709823734633151664945104541736248173167699205687255076,
   762811726869586857145354436778979066941441937002538731943419132633154088974561,
   955246576873148912235051661060617785347766799756088075088157168436265864774198,
   1455043100143388988383151947198002602238941016088089233219959426350730874211964,
   2100069881442214658030648709748177336680972325467773697168244196820879410495464,
   1710388004335125585573567784323667237847389048491194459897701187699748935984904,
   472344831178034245461777963413423486891599941630782614822903002247270641364174,
   904178248775744531006033672410776559005311699438079190593934809394760685054795,
   2622912058631523526704074962993994280073229789126692763069761599954802673184514,
   1878466358504412913026927326760389545316361958101748979804650716200360357873065]

def xl : List ℤ :=
  [-131, -29, -40, 110, -174, 162, -278, 78, -56, -67, -101, 115, -83, 97, -134, -70, -94, 48,
   -107, 180, -180, 49, -104, 7, -67, 24, 21, -48, 39, -185, 59, -81, 1, -52, 119, -151]

def yl : List ℤ :=
  [-1486205895543641839697786550382857974013447310201294511877024819522878062042578,
   1257852155837549177195870386956780255789197254540860089345064617634331133653650,
   2210755439868184092786013976663614350615529491483168653358673884742644727399809,
   608653194993543637238782804208860924940720526567214916031689748821427057813620,
   524315321643938757505032603063991289233125203760304437403163107957576075492238,
   222579578958739826466357685242725705444814689567895016807253985393638332665170,
   338630505624881793850207687830905478183362256784903599791028262552748774196693,
   463415917625368482428584474637375967838676621533914666118640192376899601968913,
   133300747475552400417873675496283780752164027828204371202186708236240460959003,
   -1060005442807282162480471658421829050342628623820609174271855247774570934334828,
   1633997527278407802178283477576961767980850033831096522847639451913088977610348,
   2820162591375187381919994593939290563732057897664794851232106294675482639617772,
   -759358065515984772123544174377815034019030814292727114826431743620952941315060,
   -1489210435799706398972321937963548579767903451231298619742489573920485768688817,
   2016917231290737154551943512961372795293576523970885603158779058340018523457358,
   1726442037529129257915856433266450617431399146352499253226087515085083141568838,
   -1777896804928825303982168515508907047973779850359672026263372532467652607627680,
   -500482335269254746702365447566415493134233064588437541576330095485918714513859,
   2585648233624553535376542112048520328538707534282767529453743787973127698853844,
   1076885676199751046774701040633518327699637720410576505890360699196289239933379,
   -1008154901055698634329127182086720035752135453263222101325241269588405652093914,
   99109311335340143990118587043255706672860462372690761061243259293631604243255,
   1309875885926185605789523232884360197852025350312462420337422278975550612056668,
   1437880451418676908041211589381935999605428997557866696650811826834886515766514,
   71576127152375945622451637426586557102574808430428072932574191589331241979287,
   -590796328365025885545386452917656768917561166121012586070698407658868202926056,
   143982112346663874611763421731256324726371021401127922954702275988650374594333,
   1819765838933044025375136411216336833047936894857797098266778440859314955181142,
   418231960271707659763837227950627428158280561924988835290613084933845583533423,
   -985139322799913807532040220934159696660194734934365715664383296904389324258983,
   632353832485660002484259299816800961171062061336453368760499090594556747103170,
   2554270796161894757933624877927926860061545435629994428161548467795613697241855,
   624682658241583982174907311610542339185889468565816274555194187575503971652929,
   -1463571288084946330391495301564876781495495470893788110345502156996377838492602,
   350016140133100699575751778248947714881843837574065066794427917111996496472065,
   2124203213214382179124036087661750910331582462035173948029837845803037059683304]

def g1 : List ℤ :=
  [-34097386028496935423395642960862661467118321694987178481745572798587113268218117,
   438857926855300993849919732413917730988690659249657739400261979520901180321527538,
   -145890709031423833376727975462895680168858522653643851960828146205419572467040745,
   109283073832921962905567195669490896436262997421565083906447219714659091921988250,
   243461210468539366043732934757761032856753556774342661948616922712084469362284642,
   11606116882989769560667255232663656746400494129222118830016007385430786602571407,
   -77028807794414303493753880379015698938265296019256637874624717092076435306787227,
   -60968435442360296558600079226283466097085679054484578555232685357374004847920374,
   192486620417701427197466980201678912129541985043221569438488820571364695404906268,
   150437499230190010791506827319416692001953584613526419340078415786545491585079295,
   118471679258198527182514939159291704538863693034731665743211158833165369428195422,
   7017104071419337220020786290395510564999780907831594784182963630944029133595858,
   -26310364374552091392806236156678912603595793956870283497521440612313660330862822,
   233887225160643974889544641286281342539812815896923406379242755930638609740861937,
   242218920471690860930805044282840937371166225502424101610179631689401303161098524,
   -20818759768804024057592276692872972575572248431372780427987687374169106949529419,
   57771231304578681187399364845586175909617551250078872992403027396555206381893970,
   82444349797745139445953641201025133086301408506735014770619205709398392285426417,
   124416711694228419711178531722057088498507632087855804779115214568197307606227596,
   323958536910028205506431450819600841852118309950233772280007869747377889970301520,
   11565619991344521732169543557593388735331772776986783146971543477275378895045441,
   -38640536464736379225724425237108390972785165685598355364893898948727591967522275,
   155219588578231411517452430936935720416446438951556815697261017740460048963051861,
   -25043038670755204613662087952743737823521692952373318146494839047871283478292479,
   251915204623157973286258155682713380152165316151739669138395107443514874859040428,
   348961222056404814821139559174686587533208437182236952428706808019622022523556520,
   -164816118425255256674484434595576047854188543943002182051032262587656035551199257,
   11531391797356732134942516908736477844733101187635568721349029693059929759611558,
   161531491645443742521151304811871268624355857316542923668936507342249570237915375,
   13541930763376458261431572076678513126634042190805687078986120854466595935884386,
   193292234484822024989754974385244601107710462751727322718989365016472217834366543,
   74715505506441898313371822813726343276840832661906074400329568507414018928285540,
   -77024969128425966500795308901125368125113494540237809832562372565465138421276049,
   115381254941557953768634532757795863396844119884680994468938975183160683677102163,
   191603568567450117128746587329559733622268919726378395940074373052436756503052630]

def g2 : List ℤ :=
  [-417127934177980215071351107935841835997980242809183290433127801544847057556146224,
   107070339974137403661335072020460727737958462907307897516173418945733982856973826,
   72313088200255506465563817616160367581058122019399008009391533380698677169621208,
   292569797795107850161097601757341463378678520913752812897045789321286351111818055,
   -85385476390308566935848457920608651778299817608295764521307971322650421880666477,
   -341282599699957873148547642883472559354594752197126402582706148618773834731315458,
   157304209881602553828701900509188134337209622692525438767123337280715593595852154,
   -232200570587394559976075057606271514490166749939546952617749185135452078418670115,
   32950705666057032666397101522367493697892852761691986613658659182257915720087827,
   -115269602698082616263357098882403363244479902666393188445088424579289045281155150,
   -352412601952744070698913624843377950452128165258781971875003715515045413287519922,
   611399126589821943263883283168385458102735152261935921413270602795236493998716390,
   105643182983565262914809722805832722207862411212132980463374411477094849932915713,
   -315005017598294688372068252413176630151005962491530700898343365135178952697879957,
   -85269109359938889101682929679124337438057414306535034322359554860536625261533873,
   52184844858637896846929145035392329653273498957003496816898571424517682759661778,
   -433892154882769766784764004792439153948675961518579234084394757897114302817027391,
   646223222648387787389448292560702060758898355549014510468169821655352483934397503,
   -382521808172371671594119186111139079432228637691857404682145954060410471819955754,
   -310418744770481728698086537191480420799639457438414763962974519909208842107927853,
   828636353846653733591872777147355654032938149362847681367611895059113964302029719,
   -320194185132509860608542830803520310659914523274271104405411092089859941947298349,
   -342612616596951977610892482764614467099428755690291040247272134704597578433657479,
   -1801087166510188774147736891135890487189223346008513249258654350769524177683627,
   114527578573039054041236606296145904759128031297833906201949388355528651266828587,
   75350550783131103737573849305515667587060290377846924301512286784627699332188007,
   160973690944021637463122239213650318291787587605376488738199267997085581625757738,
   -260562612935045231067692888356488766801022299383909036037496148760510881530329967,
   102656809918456937414240286148987308989419559484478727106435155927940849837280147,
   -76859221840425002206899702276880952119018638264239723451321973863338437319192131,
   -137987373991435653847944231210349611729165476807824485117270642361286460018043117,
   58770356812396774426329662673463252877388956403813686454335218268443067670231326,
   121658688129604427654868997816762657280528589365801355841652592452693833752483943,
   -25232618033957251167365182905997115874550077462952835653663526183700266219331058,
   -66979692386299367596414345399320228488949244545776353251458797874344633951135807]

lemma cert1 : pmul al k1 = padd [149 ^ 37] (pmul phi g1) := by decide +kernel

lemma cert2 : padd (pmul k1 xl) (pmul al yl) = padd [1] (pmul phi g2) := by decide +kernel

lemma cert3 : evZ 2 phi = 223 * 616318177 := by decide +kernel

def NA : ℤ := evZ (2 ^ 2) al * evZ (2 ^ 36) al ^ 2

def NB : ℤ := evZ ((2 ^ 2) ^ 36) al * evZ 2 al ^ 2

lemma cert4 : NA % 223 ≠ 0 ∧ NB % 223 ≠ 0 ∧ (NA ^ 6 - NB ^ 6) % 223 ≠ 0 := by decide +kernel

/- ### Ideals -/

lemma span_pair_pow_le {R : Type*} [CommRing R] (a b : R) (n : ℕ) :
    Ideal.span {a, b} ^ n ≤ Ideal.span {a ^ n} ⊔ Ideal.span {b} := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hab : Ideal.span {a, b} ≤ Ideal.span {a} ⊔ Ideal.span {b} := (Ideal.span_insert a {b}).le
    have h1 : Ideal.span {a ^ n} * Ideal.span {a} = Ideal.span {a ^ (n + 1)} := by
      rw [Ideal.span_singleton_mul_span_singleton, pow_succ]
    have h2 : Ideal.span {a, b} ^ (n + 1) ≤
        (Ideal.span {a ^ n} ⊔ Ideal.span {b}) * (Ideal.span {a} ⊔ Ideal.span {b}) := by
      rw [pow_succ]
      exact mul_le_mul' ih hab
    have h3 : (Ideal.span {a ^ n} ⊔ Ideal.span {b}) * (Ideal.span {a} ⊔ Ideal.span {b}) =
        Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {a ^ n} * Ideal.span {b} ⊔
            (Ideal.span {b} * Ideal.span {a} ⊔ Ideal.span {b} * Ideal.span {b}) := by
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, h1]
    rw [h3] at h2
    have e1 : Ideal.span {a ^ n} * Ideal.span {b} ≤ Ideal.span {b} := Ideal.mul_le_right
    have e2 : Ideal.span {b} * Ideal.span {a} ≤ Ideal.span {b} := Ideal.mul_le_left
    have e3 : Ideal.span {b} * Ideal.span {b} ≤ Ideal.span {b} := Ideal.mul_le_left
    have e4 : Ideal.span {b} ≤ Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {b} := le_sup_right
    exact h2.trans (sup_le (sup_le le_sup_left (e1.trans e4)) (sup_le (e2.trans e4) (e3.trans e4)))

/-- If the class number is prime to `n`, an element generating the `n`-th power of the ideal
`(l, a)` is a unit times an `n`-th power. -/
lemma key_ideal {R : Type*} [CommRing R] [IsDedekindDomain R] [Fintype (ClassGroup R)] (n : ℕ)
    (h : Nat.Coprime n (Fintype.card (ClassGroup R))) (l a k x y : R) (hl : l ≠ 0)
    (h1 : a * k = l ^ n) (h2 : k * x + a * y = 1) :
    ∃ (b : R) (u : Rˣ), a = u * b ^ n := by
  set I : Ideal R := Ideal.span {l, a} with hI
  have hlI : l ∈ I := Ideal.subset_span (by simp)
  have haI : a ∈ I := Ideal.subset_span (by simp)
  have hI37 : I ^ n = Ideal.span {a} := by
    apply le_antisymm
    · refine (span_pair_pow_le l a n).trans (sup_le ?_ le_rfl)
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨k, h1.symm⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      have hc : IsCoprime k (a ^ n) := IsCoprime.pow_right ⟨x, y, by linear_combination h2⟩
      obtain ⟨s, t, hst⟩ := hc
      have h3 : l ^ n ∈ I ^ n := Ideal.pow_mem_pow hlI n
      have h4 : a ^ n ∈ I ^ n := Ideal.pow_mem_pow haI n
      have h5 : a = l ^ n * s + a ^ n * (a * t) := by linear_combination (-a) * hst + s * h1
      rw [h5]
      exact Ideal.add_mem _ (Ideal.mul_mem_right s _ h3) (Ideal.mul_mem_right (a * t) _ h4)
  have hI0 : I ≠ ⊥ := fun h0 => hl (by simpa [h0] using hlI)
  have hInz : I ∈ nonZeroDivisors (Ideal R) := mem_nonZeroDivisors_of_ne_zero hI0
  have hpow : (ClassGroup.mk0 ⟨I, hInz⟩) ^ n = 1 := by
    rw [← map_pow]
    have h6 : ((⟨I, hInz⟩ : nonZeroDivisors (Ideal R)) ^ n) =
        ⟨I ^ n, pow_mem hInz n⟩ := Subtype.ext (by simp)
    rw [h6, ClassGroup.mk0_eq_one_iff, hI37]
    exact ⟨⟨a, rfl⟩⟩
  have hord : orderOf (ClassGroup.mk0 ⟨I, hInz⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes h (orderOf_dvd_of_pow_eq_one hpow) orderOf_dvd_card
  rw [orderOf_eq_one_iff, ClassGroup.mk0_eq_one_iff] at hord
  obtain ⟨b, hb⟩ := hord.principal
  have hb' : I = Ideal.span {b} := hb
  rw [hb', Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hI37
  obtain ⟨u, hu⟩ := hI37
  exact ⟨b, u, by rw [← hu, mul_comm]⟩

/- ### The cyclotomic ring -/

section Cyc

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K] {ζ : K}

/-- Ring homomorphisms out of `ℤ[ζ]` are given by roots of the 37-th cyclotomic polynomial. -/
lemma exists_hom (hζ : IsPrimitiveRoot ζ 37) {S : Type*} [CommRing S] (y : S)
    (hy : ∑ i ∈ Finset.range 37, y ^ i = 0) : ∃ f : 𝓞 K →+* S, f hζ.toInteger = y := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hmin : minpoly ℤ hζ.integralPowerBasis.gen = Polynomial.cyclotomic 37 ℤ := by
    rw [hζ.integralPowerBasis_gen, Polynomial.cyclotomic_eq_minpoly hζ (by norm_num)]
    exact (minpoly.algebraMap_eq RingOfIntegers.coe_injective hζ.toInteger).symm
  have h0 : Polynomial.aeval y (minpoly ℤ hζ.integralPowerBasis.gen) = 0 := by
    rw [hmin, Polynomial.cyclotomic_prime]
    simpa using hy
  refine ⟨(hζ.integralPowerBasis.lift y h0 : 𝓞 K →ₐ[ℤ] S), ?_⟩
  have h := hζ.integralPowerBasis.lift_gen y h0
  rw [hζ.integralPowerBasis_gen] at h
  exact h

/-- An endomorphism of `ℤ[ζ]` sending `ζ` to `ζ⁻¹` is complex conjugation in every embedding. -/
lemma conj_compat (hζ : IsPrimitiveRoot ζ 37) (c : 𝓞 K →+* 𝓞 K)
    (hc : c hζ.toInteger = hζ.toInteger ^ 36) (τ : K →+* ℂ) (v : 𝓞 K) :
    τ (algebraMap (𝓞 K) K (c v)) = (starRingEnd ℂ) (τ (algebraMap (𝓞 K) K v)) := by
  have hz : τ ζ ^ 37 = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hn : ‖τ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (by norm_num)
  have hne : τ ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have h1 : τ ζ * (starRingEnd ℂ) (τ ζ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have hgen : τ ζ ^ 36 = (starRingEnd ℂ) (τ ζ) := by
    apply mul_left_cancel₀ hne
    rw [h1, ← pow_succ', hz]
  have key : ((τ.comp (algebraMap (𝓞 K) K)).comp c).toIntAlgHom =
      ((starRingEnd ℂ).comp (τ.comp (algebraMap (𝓞 K) K))).toIntAlgHom := by
    apply hζ.integralPowerBasis.algHom_ext
    rw [hζ.integralPowerBasis_gen]
    change τ (algebraMap (𝓞 K) K (c hζ.toInteger)) =
      (starRingEnd ℂ) (τ (algebraMap (𝓞 K) K hζ.toInteger))
    rw [hc, map_pow, map_pow]
    exact hgen
  exact DFunLike.congr_fun key v

/-- Kummer's lemma on units, in the weak form needed here. -/
lemma unit_lemma (hζ : IsPrimitiveRoot ζ 37) (c : 𝓞 K →+* 𝓞 K)
    (hc : c hζ.toInteger = hζ.toInteger ^ 36) (u : (𝓞 K)ˣ) :
    ∃ (e : 𝓞 K) (m : ℕ), (e = 1 ∨ e = -1) ∧ (u : 𝓞 K) = e * hζ.toInteger ^ m * c u := by
  have hcu : c (u : 𝓞 K) * c ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 K, w = u * c ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := ⟨_, rfl⟩
  have hu : (u : 𝓞 K) = w * c u := by
    rw [hw, mul_assoc, mul_comm (c _) (c _), hcu, mul_one]
  have hnorm : ∀ τ : K →+* ℂ, ‖τ (algebraMap (𝓞 K) K w)‖ = 1 := by
    intro τ
    rw [hw, map_mul, map_mul, norm_mul, conj_compat hζ c hc τ, RCLike.norm_conj, ← norm_mul,
      ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ
    (RingOfIntegers.isIntegral_coe w) hnorm
  have hfin : IsOfFinOrder (algebraMap (𝓞 K) K w) := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩
  obtain ⟨r, -, hr⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder (by decide) hfin
  rcases hr with hr | hr
  · refine ⟨1, r, Or.inl rfl, ?_⟩
    have hwr : w = hζ.toInteger ^ r := RingOfIntegers.coe_injective (by rw [hr, map_pow]; rfl)
    rw [one_mul, ← hwr]
    exact hu
  · refine ⟨-1, r, Or.inr rfl, ?_⟩
    have hwr : w = -hζ.toInteger ^ r :=
      RingOfIntegers.coe_injective (by rw [hr, map_neg, map_pow]; rfl)
    rw [neg_one_mul, ← hwr]
    exact hu

end Cyc

/- ### The final computation in `ZMod 223` -/

lemma final_step [Fact (Nat.Prime 223)] (U2 U4 b1 b2 b3 b4 t e A B : ZMod 223)
    (he : e = 1 ∨ e = -1)
    (hA : A = (e * t ^ 2 * U4) * b3 ^ 37 * (U2 * b2 ^ 37) ^ 2)
    (hB : B = U4 * b4 ^ 37 * (e * t * U2 * b1 ^ 37) ^ 2) (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    A ^ 6 = B ^ 6 := by
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hX0 : b4 * b1 ^ 2 ≠ 0 := by
    intro h
    apply hB0
    rw [hB]
    linear_combination (U4 * b4 ^ 36 * e ^ 2 * t ^ 2 * U2 ^ 2 * (b1 ^ 2) ^ 36) * h
  have hY0 : b3 * b2 ^ 2 ≠ 0 := by
    intro h
    apply hA0
    rw [hA]
    linear_combination (e * t ^ 2 * U4 * b3 ^ 36 * U2 ^ 2 * (b2 ^ 2) ^ 36) * h
  have hX : (b4 * b1 ^ 2) ^ 222 = 1 := ZMod.pow_card_sub_one_eq_one hX0
  have hY : (b3 * b2 ^ 2) ^ 222 = 1 := ZMod.pow_card_sub_one_eq_one hY0
  have hA6 : A ^ 6 = (e ^ 2) ^ 3 * (t ^ 2 * U4 * U2 ^ 2) ^ 6 * (b3 * b2 ^ 2) ^ 222 := by
    rw [hA]
    ring
  have hB6 : B ^ 6 = (e ^ 2) ^ 6 * (t ^ 2 * U4 * U2 ^ 2) ^ 6 * (b4 * b1 ^ 2) ^ 222 := by
    rw [hB]
    ring
  rw [hA6, hB6, he2, hX, hY, one_pow, one_pow]

theorem main {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fintype (ClassGroup (𝓞 K))] : ¬ Nat.Coprime 37 (Fintype.card (ClassGroup (𝓞 K))) := by
  intro hcop
  have : Fact (Nat.Prime 223) := ⟨by norm_num⟩
  have hζK := IsCyclotomicExtension.zeta_spec 37 ℚ K
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : 𝓞 K, ζ = hζK.toInteger := ⟨_, rfl⟩
  have hζR : IsPrimitiveRoot ζ 37 := hζdef ▸ hζK.toInteger_isPrimitiveRoot
  have hsum : ∀ j : ℕ, Nat.Coprime j 37 → ∑ i ∈ Finset.range 37, (ζ ^ j) ^ i = 0 :=
    fun j hj => (hζR.pow_of_coprime j hj).geom_sum_eq_zero (by norm_num)
  have hphi : ev ζ phi = 0 := by
    rw [ev_phi]
    exact hζR.geom_sum_eq_zero (by norm_num)
  -- the three ring homomorphisms
  obtain ⟨s, hs⟩ := exists_hom hζK (ζ ^ 2) (hsum 2 (by decide))
  obtain ⟨c, hc⟩ := exists_hom hζK (ζ ^ 36) (hsum 36 (by decide))
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = 2 := ⟨2, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_hom hζK ((r : ℤ) : ZMod 223) (by
    rw [← ev_phi, ev_cast, hr, cert3, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨616318177, by norm_num⟩)
  rw [← hζdef] at hs hc hφ
  -- the ideal certificate
  have h1 : ev ζ al * ev ζ k1 = (149 : 𝓞 K) ^ 37 := by
    have h := congrArg (ev ζ) cert1
    rw [ev_pmul, ev_padd, ev_pmul, hphi] at h
    rw [h]
    simp only [ev, mul_zero, add_zero, zero_mul, Int.cast_pow, Int.cast_ofNat]
  have h2 : ev ζ k1 * ev ζ xl + ev ζ al * ev ζ yl = 1 := by
    have h := congrArg (ev ζ) cert2
    rw [ev_padd, ev_pmul, ev_pmul, ev_padd, ev_pmul, hphi] at h
    rw [h]
    simp only [ev, mul_zero, add_zero, zero_mul, Int.cast_one]
  obtain ⟨b, u, hab⟩ := key_ideal 37 hcop (149 : 𝓞 K) (ev ζ al) (ev ζ k1) (ev ζ xl) (ev ζ yl)
    (by norm_num) h1 h2
  obtain ⟨e, m, he, hu⟩ := unit_lemma hζK c (by rw [← hζdef]; exact hc) u
  rw [← hζdef] at hu
  -- values of the four conjugates of `α` in `ZMod 223`
  have hval : ∀ (ψ : 𝓞 K →+* ZMod 223) (q : ℤ), ψ ζ = (q : ZMod 223) →
      ψ (ev ζ al) = ((evZ q al : ℤ) : ZMod 223) := by
    intro ψ q hq
    rw [map_ev, hq, ev_cast]
  have v1 : φ (ev ζ al) = ((evZ r al : ℤ) : ZMod 223) := hval φ r hφ
  have v2 : φ (c (ev ζ al)) = ((evZ (r ^ 36) al : ℤ) : ZMod 223) :=
    hval (φ.comp c) (r ^ 36) (by simp [hc, hφ])
  have v3 : φ (s (ev ζ al)) = ((evZ (r ^ 2) al : ℤ) : ZMod 223) :=
    hval (φ.comp s) (r ^ 2) (by simp [hs, hφ])
  have v4 : φ (s (c (ev ζ al))) = ((evZ ((r ^ 2) ^ 36) al : ℤ) : ZMod 223) :=
    hval ((φ.comp s).comp c) ((r ^ 2) ^ 36) (by simp [hs, hc, hφ])
  -- the unit relation in `ZMod 223`
  have hE : φ e = 1 ∨ φ e = -1 := by rcases he with rfl | rfl <;> simp
  have hsE : φ (s e) = φ e := by rcases he with rfl | rfl <;> simp
  have hU1 : φ u = φ e * (r : ZMod 223) ^ m * φ (c u) := by
    have h := congrArg φ hu
    rw [map_mul, map_mul, map_pow, hφ] at h
    exact h
  have hU3 : φ (s u) = φ e * ((r : ZMod 223) ^ m) ^ 2 * φ (s (c u)) := by
    have h := congrArg (fun z => φ (s z)) hu
    simp only [map_mul, map_pow, hs, hφ, hsE] at h
    rw [h]
    ring
  have hA : φ (s (ev ζ al)) * φ (c (ev ζ al)) ^ 2 =
      (φ e * ((r : ZMod 223) ^ m) ^ 2 * φ (s (c u))) * φ (s b) ^ 37 *
        (φ (c u) * φ (c b) ^ 37) ^ 2 := by
    rw [← hU3]
    conv_lhs => rw [hab]
    simp only [map_mul, map_pow]
  have hB : φ (s (c (ev ζ al))) * φ (ev ζ al) ^ 2 =
      φ (s (c u)) * φ (s (c b)) ^ 37 *
        (φ e * (r : ZMod 223) ^ m * φ (c u) * φ b ^ 37) ^ 2 := by
    rw [← hU1]
    conv_lhs => rw [hab]
    simp only [map_mul, map_pow]
  -- conclusion
  obtain ⟨c1, c2, c3⟩ := cert4
  rw [v3, v2] at hA
  rw [v4, v1] at hB
  subst hr
  have hNA : ((NA : ℤ) : ZMod 223) =
      ((evZ (2 ^ 2) al : ℤ) : ZMod 223) * ((evZ (2 ^ 36) al : ℤ) : ZMod 223) ^ 2 := by
    rw [NA, Int.cast_mul, Int.cast_pow]
  have hNB : ((NB : ℤ) : ZMod 223) =
      ((evZ ((2 ^ 2) ^ 36) al : ℤ) : ZMod 223) * ((evZ 2 al : ℤ) : ZMod 223) ^ 2 := by
    rw [NB, Int.cast_mul, Int.cast_pow]
  have hA' := hNA.trans hA
  have hB' := hNB.trans hB
  have hA0 : ((NA : ℤ) : ZMod 223) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => c1 (Int.emod_eq_zero_of_dvd h)
  have hB0 : ((NB : ℤ) : ZMod 223) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => c2 (Int.emod_eq_zero_of_dvd h)
  have hfin := final_step _ _ _ _ _ _ _ _ _ _ hE hA' hB' hA0 hB0
  apply c3
  apply Int.emod_eq_zero_of_dvd
  have h6 : (((NA ^ 6 - NB ^ 6 : ℤ)) : ZMod 223) = 0 := by
    rw [Int.cast_sub, Int.cast_pow, Int.cast_pow, hfin, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 223).mp h6

end OMA.Irr37

namespace OMA.BernoulliTable

def entry (n : ℕ) : ℚ :=
  ([1, 1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, 0, -3617/510, 0, 43867/798, 0, -174611/330, 0, 854513/138, 0, -236364091/2730, 0, 8553103/6, 0, -23749461029/870, 0, 8615841276005/14322, 0, -7709321041217/510] : List ℚ)[n]?.getD 0

set_option maxRecDepth 10000 in
private lemma recurrence : ∀ i : Fin 33, entry i = 1 -
    ∑ k ∈ Finset.range i.val, i.val.choose k / (i.val - k + 1) * entry k := by
  decide +kernel

lemma correct (n : ℕ) (hn : n < 33) : bernoulli' n = entry n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [bernoulli'_def, recurrence ⟨n, hn⟩]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k (Finset.mem_range.mp hk) ((Finset.mem_range.mp hk).trans hn)]

end OMA.BernoulliTable

theorem OMA.solution : OMA.R_RegularPrimes_not_isRegularPrime_37_R1.H2 := by
  constructor
  · intro h
    letI : IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ) :=
      CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 37 ℚ
    exact (OMA.Irr37.main h).elim
  · intro h
    have h32 := h 32 (by norm_num) ⟨16, rfl⟩
    apply False.elim
    apply h32
    rw [OMA.BernoulliTable.correct 32 (by decide)]
    exact ⟨-208360028141, by decide +kernel⟩
