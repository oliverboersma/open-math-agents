import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1

/-! Bounded prime-root divisor case. The stored integer brackets and coverage are
replayed by Lean's kernel. -/

namespace A056777Bounded


def cubic (L M C x : ℤ) : ℤ := ((2*x-L)*x+M)*x-C

def slope (L M x y : ℤ) : ℤ := 2*(x*x+x*y+y*y)-L*(x+y)+M

theorem cubic_diff (L M C x y : ℤ) :
    cubic L M C y - cubic L M C x = (y-x)*slope L M x y := by
  unfold cubic slope
  ring

theorem slope_antitone {L M P u v u' v' : ℤ}
    (hL : 6*P ≤ L) (hu : u ≤ u') (hv : v ≤ v') (hu' : u' ≤ P) (hv' : v' ≤ P) :
    slope L M u' v' ≤ slope L M u v := by
  have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu)
    (show 2*(u'+u+v)-L ≤ 0 by linarith)
  have h₂ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv)
    (show 2*(u'+v'+v)-L ≤ 0 by linarith)
  unfold slope
  nlinarith only [h₁,h₂]

theorem no_root_between {L M C P a b x : ℤ} (hL : 6*P ≤ L) (hab : a+1 ≤ b)
    (hb : b+1 ≤ P) (hx : x ≤ P)
    (hfa : cubic L M C a < 0) (hfa' : 0 < cubic L M C (a+1))
    (hfb : 0 < cubic L M C b) (hfb' : cubic L M C (b+1) < 0) :
    cubic L M C x ≠ 0 := by
  have ha' : a+1 ≤ P := by omega
  have hbp : b ≤ P := by omega
  have leftSlope : 0 ≤ slope L M a (a+1) := by linarith [cubic_diff L M C a (a+1)]
  have rightSlope : slope L M b (b+1) ≤ 0 := by linarith [cubic_diff L M C b (b+1)]
  by_cases hxa : x ≤ a
  · have h := slope_antitone (M:=M) hL hxa (show a ≤ a+1 by omega) (by omega) ha'
    have hmul := mul_nonneg (show 0 ≤ a-x by omega) (leftSlope.trans h)
    linarith [cubic_diff L M C x a]
  by_cases hxb : b+1 ≤ x
  · have h := slope_antitone (M:=M) hL (show b ≤ b+1 by omega) hxb hb hx
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x-(b+1) by omega) (h.trans rightSlope)
    linarith [cubic_diff L M C (b+1) x]
  have hax : a+1 ≤ x := by omega
  have hxb' : x ≤ b := by omega
  by_cases hsign : 0 ≤ slope L M (a+1) x
  · have hmul := mul_nonneg (show 0 ≤ x-(a+1) by omega) hsign
    linarith [cubic_diff L M C (a+1) x]
  · have h := slope_antitone (M:=M) hL hax hxb' hx hbp
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ b-x by omega)
      (h.trans (le_of_lt (lt_of_not_ge hsign)))
    linarith [cubic_diff L M C x b]

theorem no_root_below_peak {L M C P a x : ℤ} (hL : 6*P ≤ L)
    (ha : a+1 ≤ P) (hx : x ≤ P)
    (hfa : cubic L M C a < 0) (hleft : 0 ≤ slope L M (a-1) a)
    (hright : slope L M a (a+1) ≤ 0) : cubic L M C x ≠ 0 := by
  obtain hxa|rfl|hax := lt_trichotomy x a
  · have h := slope_antitone (M:=M) hL (show x ≤ a-1 by omega) (le_refl a)
        (by omega) (by omega)
    have hmul := mul_nonneg (show 0 ≤ a-x by omega) (hleft.trans h)
    linarith [cubic_diff L M C x a]
  · exact ne_of_lt hfa
  · have h := slope_antitone (M:=M) hL (le_refl a) (show a+1 ≤ x by omega) (by omega) hx
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x-a by omega) (h.trans hright)
    linarith [cubic_diff L M C a x]

def sumCoeff (p q : ℤ) : ℤ := (p*p+p+1)*(q+1)+2*p^3

def pairCoeff (p q : ℤ) : ℤ := 2*p^3*(p+q-1)+sumCoeff p q-2

def productCoeff (p q : ℤ) : ℤ := 2*(p^4*q+12)



/-- Filtering multiples of these constants reduces the kernel replay cost.
Soundness only needs every constant to be greater than one. -/
def divisors : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]

def possiblePrime (p : ℕ) : Bool :=
  divisors.all fun d => decide (p ≤ d ∨ p % d ≠ 0)

theorem prime_possiblePrime {p : ℕ} (hp : p.Prime) : possiblePrime p = true := by
  apply List.all_eq_true.mpr
  intro d hd
  have h1 : 1 < d := by
    change d ∈ divisors at hd
    unfold divisors at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  apply decide_eq_true
  by_contra! h
  have hdvd : d ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h.2
  rcases hp.eq_one_or_self_of_dvd d hdvd with hbad|hbad <;> omega

def qFromIndex (i : ℕ) : ℕ := 40*i+27

theorem q_index_eq {q : ℕ} (h8 : q%8=3) (h5 : q%5=2) :
    qFromIndex (q/40)=q := by
  have hmod8 : (q%40)%8=q%8 := Nat.mod_mod_of_dvd q (by decide)
  have hmod5 : (q%40)%5=q%5 := Nat.mod_mod_of_dvd q (by decide)
  unfold qFromIndex
  omega

theorem p_mod_twenty {p : ℕ} (h4 : p%4=3) (h5 : p%5=2 ∨ p%5=3) :
    p%20=3 ∨ p%20=7 := by
  have hmod4 : (p%20)%4=p%4 := Nat.mod_mod_of_dvd p (by decide)
  have hmod5 : (p%20)%5=p%5 := Nat.mod_mod_of_dvd p (by decide)
  omega

-- Every index is less than 2^18. A zero upper field represents a negative peak.
def signCertificate (p q data : ℕ) : Bool :=
  let L := sumCoeff p q
  let M := pairCoeff p q
  let C := productCoeff p q
  let a : ℤ := (data % 262144 : ℕ)
  let high := data / 262144
  decide (6*(p:ℤ) ≤ L) &&
    if high = 0 then
      decide (a+1 ≤ p ∧ cubic L M C a < 0 ∧
        0 ≤ slope L M (a-1) a ∧ slope L M a (a+1) ≤ 0)
    else
      let b : ℤ := high
      decide (a+1 ≤ b ∧ b+1 ≤ p ∧ cubic L M C a < 0 ∧ 0 < cubic L M C (a+1) ∧
        0 < cubic L M C b ∧ cubic L M C (b+1) < 0)

theorem signCertificate_sound {p q x data : ℕ} (hc : signCertificate p q data = true)
    (hx : x ≤ p) : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x ≠ 0 := by
  unfold signCertificate at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hL,hc⟩ := hc
  have hxp : (x:ℤ) ≤ (p:ℤ) := by exact_mod_cast hx
  split at hc
  next _ =>
    simp only [decide_eq_true_eq] at hc
    exact no_root_below_peak hL hc.1 hxp hc.2.1 hc.2.2.1 hc.2.2.2
  next _ =>
    simp only [decide_eq_true_eq] at hc
    exact no_root_between hL hc.1 hc.2.1 hxp hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2

def candidateP (q p : ℕ) : Bool :=
  decide (2*q < p ∧ p*p < q^3 ∧ p%3 ≠ q%3) && possiblePrime p

def candidateList (q low count : ℕ) : List ℕ :=
  ((List.range count).flatMap fun i =>
    [20*(low+i)+3,20*(low+i)+7]).filter (candidateP q)

theorem candidateP_mem {p q lo c : ℕ} (hp : p.Prime)
    (hpLo : 2*q < p) (hpHi : p^2 < q^3) (hmod : p%3 ≠ q%3) (hmod20 : p%20=3 ∨ p%20=7)
    (hlo : lo ≤ p/20) (hhi : p/20 < lo+c) : p ∈ candidateList q lo c := by
  unfold candidateList
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨p/20-lo, List.mem_range.mpr (by omega), ?_⟩
    obtain h3|h7 := hmod20
    · have he : 20*(lo+(p/20-lo))+3=p := by omega
      simp [he]
    · have he : 20*(lo+(p/20-lo))+7=p := by omega
      simp [he]
  · unfold candidateP
    simp only [Bool.and_eq_true]
    exact ⟨decide_eq_true ⟨hpLo,by simpa only [pow_two] using hpHi,hmod⟩,
      prime_possiblePrime hp⟩

def expandSign (p q field : ℕ) : ℕ :=
  let lower := q + field % 4096
  let upperOffset := field / 4096
  let upper := if upperOffset = 0 then 0 else p-upperOffset
  lower + 262144*upper

def natQTerm (p q : ℕ) : ℕ := (p*p+p+1)*(q+1)
def natSumCoeff (p q : ℕ) : ℕ := natQTerm p q+2*p*p*p
def natPairPlusTwo (p q : ℕ) : ℕ := 2*p*p*p*(p+q)+natQTerm p q
def natProductCoeff (p q : ℕ) : ℕ := 2*(p*p*p*p*q+12)

def cubicHigh (p q x : ℕ) : ℕ := (2*x*x+natPairPlusTwo p q)*x
def cubicLow (p q x : ℕ) : ℕ := (natSumCoeff p q*x+2)*x+natProductCoeff p q
def slopeHigh (p q x y : ℕ) : ℕ := 2*(x*x+x*y+y*y)+natPairPlusTwo p q
def slopeLow (p q x y : ℕ) : ℕ := natSumCoeff p q*(x+y)+2

theorem natSumCoeff_cast (p q : ℕ) : (natSumCoeff p q : ℤ) = sumCoeff p q := by
  unfold natSumCoeff natQTerm sumCoeff
  push_cast
  ring

theorem cubic_parts (p q x : ℕ) :
    cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x =
      (cubicHigh p q x : ℤ) - cubicLow p q x := by
  simp only [cubic,pairCoeff,sumCoeff,productCoeff,cubicHigh,cubicLow,
    natPairPlusTwo,natSumCoeff,natQTerm,natProductCoeff]
  push_cast
  ring

theorem slope_parts (p q x y : ℕ) :
    slope (sumCoeff p q) (pairCoeff p q) x y =
      (slopeHigh p q x y : ℤ) - slopeLow p q x y := by
  simp only [slope,pairCoeff,sumCoeff,slopeHigh,slopeLow,natPairPlusTwo,natSumCoeff,natQTerm]
  push_cast
  ring

/-- Evaluate the same signs using only nonnegative literal arithmetic. -/
def fastSign (p q field : ℕ) : Bool :=
  let a := q+field%4096
  let offset := field/4096
  decide (6*p ≤ natSumCoeff p q ∧ a < 262144) &&
    if offset = 0 then
      decide (1 ≤ a ∧ a+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        slopeLow p q (a-1) a ≤ slopeHigh p q (a-1) a ∧
        slopeHigh p q a (a+1) ≤ slopeLow p q a (a+1))
    else
      let b := p-offset
      decide (a+1 ≤ b ∧ b+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        cubicLow p q (a+1) < cubicHigh p q (a+1) ∧
        cubicLow p q b < cubicHigh p q b ∧
        cubicHigh p q (b+1) < cubicLow p q (b+1))

theorem fastSign_sound {p q field : ℕ} (h : fastSign p q field = true) :
    signCertificate p q (expandSign p q field) = true := by
  let a := q+field%4096
  let o := field/4096
  let b := if o=0 then 0 else p-o
  have hbase : 6*p ≤ natSumCoeff p q ∧ a<262144 := by
    have hh := (show decide (6*p ≤ natSumCoeff p q ∧ a < 262144) = true ∧ _ by
      simpa only [fastSign,a,Bool.and_eq_true] using h).1
    exact decide_eq_true_eq.mp hh
  have hL : 6*(p:ℤ) ≤ sumCoeff p q := by
    rw [← natSumCoeff_cast]
    exact_mod_cast hbase.1
  have hmod : (a+262144*b)%262144 = a := by omega
  have hdiv : (a+262144*b)/262144 = b := by omega
  change signCertificate p q (a+262144*b) = true
  simp only [signCertificate,hmod,hdiv,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨hL,?_⟩
  by_cases ho : o=0
  · have hb : b=0 := by simp [b,ho]
    simp only [hb,if_true,decide_eq_true_eq]
    have hcase : 1 ≤ a ∧ a+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        slopeLow p q (a-1) a ≤ slopeHigh p q (a-1) a ∧
        slopeHigh p q a (a+1) ≤ slopeLow p q a (a+1) := by
      have hh : field/4096=0 := ho
      simp only [fastSign,hh,if_true,Bool.and_eq_true,decide_eq_true_eq] at h
      exact h.2
    obtain ⟨ha,hap,hc,hl,hr⟩ := hcase
    refine ⟨by exact_mod_cast hap,?_,?_,?_⟩
    · rw [cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hc)
    · have hs : ((a-1 : ℕ) : ℤ) = (a:ℤ)-1 := by
        rw [Int.ofNat_sub ha]
        rfl
      rw [← hs,slope_parts]
      exact sub_nonneg.mpr (by exact_mod_cast hl)
    · rw [← Int.natCast_succ,slope_parts]
      exact sub_nonpos.mpr (by exact_mod_cast hr)
  · have hb : b=p-o := if_neg ho
    have hcase : a+1 ≤ b ∧ b+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        cubicLow p q (a+1) < cubicHigh p q (a+1) ∧
        cubicLow p q b < cubicHigh p q b ∧
        cubicHigh p q (b+1) < cubicLow p q (b+1) := by
      have hh : ¬field/4096=0 := ho
      simp only [fastSign,hh,if_false,Bool.and_eq_true,decide_eq_true_eq] at h
      simpa only [a,o,hb] using h.2
    obtain ⟨hab,hbp,hca,hca',hcb,hcb'⟩ := hcase
    have hbn : b≠0 := by omega
    simp only [hbn,if_false,decide_eq_true_eq]
    refine ⟨by exact_mod_cast hab,by exact_mod_cast hbp,?_,?_,?_,?_⟩
    · rw [cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hca)
    · rw [← Int.natCast_succ,cubic_parts]
      exact sub_pos.mpr (by exact_mod_cast hca')
    · rw [cubic_parts]
      exact sub_pos.mpr (by exact_mod_cast hcb)
    · rw [← Int.natCast_succ,cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hcb')

def fastPacked (q : ℕ) : List ℕ → ℕ → Bool
  | [], data => decide (data = 0)
  | p::ps, data =>
    fastSign p q (data % 16777216) &&
      fastPacked q ps (data / 16777216)

theorem fastPacked_sound {q p : ℕ} {ps : List ℕ} {data : ℕ}
    (h : fastPacked q ps data = true) (hp : p ∈ ps) :
    ∃ d, signCertificate p q d = true := by
  induction ps generalizing data with
  | nil => simp at hp
  | cons a as ih =>
    simp only [fastPacked,Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hpas
    · exact ⟨_,fastSign_sound h.1⟩
    · exact ih h.2 hpas

theorem cubic_parts_congr {m p q x p' q' x' : ℕ}
    (hp : p ≡ p' [MOD m]) (hq : q ≡ q' [MOD m]) (hx : x ≡ x' [MOD m]) :
    (cubicHigh p q x ≡ cubicHigh p' q' x' [MOD m]) ∧
      (cubicLow p q x ≡ cubicLow p' q' x' [MOD m]) := by
  have h₁ : 1 ≡ 1 [MOD m] := Nat.ModEq.refl 1
  have h₂ : 2 ≡ 2 [MOD m] := Nat.ModEq.refl 2
  have h₁₂ : 12 ≡ 12 [MOD m] := Nat.ModEq.refl 12
  have hQ : natQTerm p q ≡ natQTerm p' q' [MOD m] :=
    (((hp.mul hp).add hp).add h₁).mul (hq.add h₁)
  have hp3 : 2*p*p*p ≡ 2*p'*p'*p' [MOD m] := ((h₂.mul hp).mul hp).mul hp
  have hL : natSumCoeff p q ≡ natSumCoeff p' q' [MOD m] := hQ.add hp3
  have hM : natPairPlusTwo p q ≡ natPairPlusTwo p' q' [MOD m] :=
    (hp3.mul (hp.add hq)).add hQ
  have hp4 := (((hp.mul hp).mul hp).mul hp).mul hq
  have hC : natProductCoeff p q ≡ natProductCoeff p' q' [MOD m] :=
    h₂.mul (hp4.add h₁₂)
  exact ⟨(((h₂.mul hx).mul hx).add hM).mul hx, (((hL.mul hx).add h₂).mul hx).add hC⟩

def residueRoot (m p q x : ℕ) : Bool :=
  decide (cubicHigh p q x % m = cubicLow p q x % m)

def maskPossible (m mask p q : ℕ) : Bool := mask.testBit (p*m+q)

def checkMask (m mask : ℕ) : Bool :=
  (List.range m).all fun p =>
    (List.range m).all fun q =>
      maskPossible m mask p q ||
        (List.range m).all (fun x => !(residueRoot m p q x))

theorem mask_sound {m mask p q x : ℕ} (hm : 0 < m) (hvalid : checkMask m mask = true)
    (hroot : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x = 0) :
    maskPossible m mask (p%m) (q%m) = true := by
  have he : cubicHigh p q x = cubicLow p q x := by
    rw [cubic_parts] at hroot
    exact_mod_cast (sub_eq_zero.mp hroot)
  have hp : p%m ≡ p [MOD m] := Nat.mod_mod p m
  have hq : q%m ≡ q [MOD m] := Nat.mod_mod q m
  have hx : x%m ≡ x [MOD m] := Nat.mod_mod x m
  obtain ⟨hhi,hlo⟩ := cubic_parts_congr hp hq hx
  have hme : residueRoot m (p%m) (q%m) (x%m) = true := by
    unfold residueRoot
    apply decide_eq_true
    change _ % m = _ % m at hhi hlo
    rw [hhi,hlo,he]
  have hrp := List.mem_range.mpr (Nat.mod_lt p hm)
  have hrq := List.mem_range.mpr (Nat.mod_lt q hm)
  have hrx := List.mem_range.mpr (Nat.mod_lt x hm)
  unfold checkMask at hvalid
  have h := List.all_eq_true.mp (List.all_eq_true.mp hvalid _ hrp) _ hrq
  cases hmask : maskPossible m mask (p%m) (q%m) with
  | false =>
    simp only [hmask,Bool.false_or] at h
    have hf := List.all_eq_true.mp h _ hrx
    simp [hme] at hf
  | true => rfl

def mask7 : ℕ := 0x1fcd766efba0b
def mask11 : ℕ := 0x1f38e2dc3d1f777760ec3fc1b7ffeba
def mask13 : ℕ := 0x15bb7717ffd1d30ff756d47ae6edbf79c6bcfd84ccd
def mask17 : ℕ := 0x11bbaf9c9f0f6d9e7f17db3339bef557bc3523b7dbf1ed95d61cf9b6e274bff61bb5a74dc
def mask19 : ℕ := 0x171ff6da78dbabcbed6bbcfa7fffff7f62dba2ebd77777da79b79fa9dc51debfe3b07defcf76abecf9e7ff13ecc
def mask23 : ℕ := 0x19fcbdf7959cf7bee7f77e7755f9c7f2753cf291fc76f7d78bebe61edfd9a9bb318f7662e5fcff5e3eda7ab0becffffffe9bd4fec5cdcedbc4e24ffdfafdacad4cdb
def mask29 : ℕ := 0x1f1f83ea39f6e26ffdc3f3b2f9ab34eb5e89be7d37fb5df5773bffc9bce8e97f1d9c76f4293bff9fdeafe9b4bdaae7e6ffff0b4f72ffefff2d351b77ce17ad8fae7aa977ddef1b4f6deac74df5f1fceffbfa3e77bfe245ffece73af95a9ffdfb5fadffffffffe67eabf
def mask31 : ℕ := 0x193b8e727fffffffbbdf2ff3f77ad7bb7ddf3b3b3cbfbd7dfdf7d4ca6b5f5c61ebdeda427af5dbdb8b3e3bdb1e57ff0ff4d5dfd9acdffea9ffbb797ea6fbf27976dcf6baf9d837f7aadf2aebfdbfe76dfdc97fed6de3ead1aee55b9abf3f7fb4d1bb3e7392ffffffff2a7adff6c77b6f53bcf9b5eed6594f8
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask7 : checkMask 7 mask7=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask11 : checkMask 11 mask11=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask13 : checkMask 13 mask13=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask17 : checkMask 17 mask17=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask19 : checkMask 19 mask19=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask23 : checkMask 23 mask23=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask29 : checkMask 29 mask29=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask31 : checkMask 31 mask31=true := by decide +kernel

def residueMasks : List (ℕ × ℕ) := [(7,mask7), (11,mask11), (13,mask13), (17,mask17), (19,mask19), (23,mask23), (29,mask29), (31,mask31)]

private theorem mask_in_list (v : ℕ × ℕ) (h : v ∈ residueMasks) :
    0<v.1 ∧ checkMask v.1 v.2=true := by
  simp only [residueMasks,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, validMask7⟩
  · exact ⟨by decide, validMask11⟩
  · exact ⟨by decide, validMask13⟩
  · exact ⟨by decide, validMask17⟩
  · exact ⟨by decide, validMask19⟩
  · exact ⟨by decide, validMask23⟩
  · exact ⟨by decide, validMask29⟩
  · exact ⟨by decide, validMask31⟩

def sieveCubic (p q : ℕ) : Bool :=
  residueMasks.all fun v => maskPossible v.1 v.2 (p%v.1) (q%v.1)

theorem sieveCubic_sound {p q x : ℕ}
    (h : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x=0) :
    sieveCubic p q = true := by
  apply List.all_eq_true.mpr
  intro v hv
  exact mask_sound (mask_in_list v hv).1 (mask_in_list v hv).2 h

def maskedCandidates (q lo size : ℕ) : List ℕ :=
  (candidateList q lo size).filter fun p => sieveCubic p q

theorem candidate_mem_masked {p q lo c : ℕ} (hp : p.Prime)
    (hpLo : 2*q < p) (hpHi : p^2 < q^3) (hmod : p%3 ≠ q%3) (hmod20 : p%20=3 ∨ p%20=7)
    (hpass : sieveCubic p q=true) (hlo : lo ≤ p/20) (hhi : p/20 < lo+c) :
    p ∈ maskedCandidates q lo c :=
  List.mem_filter.mpr ⟨candidateP_mem hp hpLo hpHi hmod hmod20 hlo hhi, hpass⟩


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked01 {p : ℕ} (hp : p.Prime) (hlo : 2*67 < p)
    (hhi : p^2 < 67^3) (hmod : p%3 ≠ 67%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 67 = true) :
    ∃ d, signCertificate p 67 d = true := by
  have replay1_0 : fastPacked 67 (maskedCandidates 67 0 28)
      0 = true := by decide +kernel
  have hs : p*p ≤ 67^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 28 := by
    have hc : (67^3 : ℕ).sqrt = 548 := by decide +kernel
    rw [hc] at hpBound
    omega
  exact fastPacked_sound replay1_0 (candidate_mem_masked hp hlo hhi hmod hres hpass (by omega) (by omega))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked02 {p : ℕ} (hp : p.Prime) (hlo : 2*107 < p)
    (hhi : p^2 < 107^3) (hmod : p%3 ≠ 107%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 107 = true) :
    ∃ d, signCertificate p 107 d = true := by
  have replay2_0 : fastPacked 107 (maskedCandidates 107 0 56)
      0x3a000040004 = true := by decide +kernel
  have hs : p*p ≤ 107^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 56 := by
    have hc : (107^3 : ℕ).sqrt = 1106 := by decide +kernel
    rw [hc] at hpBound
    omega
  exact fastPacked_sound replay2_0 (candidate_mem_masked hp hlo hhi hmod hres hpass (by omega) (by omega))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked05 {p : ℕ} (hp : p.Prime) (hlo : 2*227 < p)
    (hhi : p^2 < 227^3) (hmod : p%3 ≠ 227%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 227 = true) :
    ∃ d, signCertificate p 227 d = true := by
  have replay5_0 : fastPacked 227 (maskedCandidates 227 0 172)
      0x85007 = true := by decide +kernel
  have hs : p*p ≤ 227^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 172 := by
    have hc : (227^3 : ℕ).sqrt = 3420 := by decide +kernel
    rw [hc] at hpBound
    omega
  exact fastPacked_sound replay5_0 (candidate_mem_masked hp hlo hhi hmod hres hpass (by omega) (by omega))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked07 {p : ℕ} (hp : p.Prime) (hlo : 2*307 < p)
    (hhi : p^2 < 307^3) (hmod : p%3 ≠ 307%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 307 = true) :
    ∃ d, signCertificate p 307 d = true := by
  have replay7_0 : fastPacked 307 (maskedCandidates 307 0 256)
      0xb3009 = true := by decide +kernel
  have replay7_1 : fastPacked 307 (maskedCandidates 307 256 13)
      0 = true := by decide +kernel
  have hs : p*p ≤ 307^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 269 := by
    have hc : (307^3 : ℕ).sqrt = 5379 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 2 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay7_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay7_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked08 {p : ℕ} (hp : p.Prime) (hlo : 2*347 < p)
    (hhi : p^2 < 347^3) (hmod : p%3 ≠ 347%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 347 = true) :
    ∃ d, signCertificate p 347 d = true := by
  have replay8_0 : fastPacked 347 (maskedCandidates 347 0 256)
      0xb60010b70010be0040c10050cc00b = true := by decide +kernel
  have replay8_1 : fastPacked 347 (maskedCandidates 347 256 68)
      0 = true := by decide +kernel
  have hs : p*p ≤ 347^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 324 := by
    have hc : (347^3 : ℕ).sqrt = 6463 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 2 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay8_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay8_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked11 {p : ℕ} (hp : p.Prime) (hlo : 2*467 < p)
    (hhi : p^2 < 467^3) (hmod : p%3 ≠ 467%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 467 = true) :
    ∃ d, signCertificate p 467 d = true := by
  have replay11_0 : fastPacked 467 (maskedCandidates 467 0 256)
      0xf7002 = true := by decide +kernel
  have replay11_1 : fastPacked 467 (maskedCandidates 467 256 249)
      0xf30000f50010f5001 = true := by decide +kernel
  have hs : p*p ≤ 467^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 505 := by
    have hc : (467^3 : ℕ).sqrt = 10091 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 2 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay11_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay11_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked13 {p : ℕ} (hp : p.Prime) (hlo : 2*547 < p)
    (hhi : p^2 < 547^3) (hmod : p%3 ≠ 547%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 547 = true) :
    ∃ d, signCertificate p 547 d = true := by
  have replay13_0 : fastPacked 547 (maskedCandidates 547 0 256)
      0x12500312600412a00613300a1a806900009d = true := by decide +kernel
  have replay13_1 : fastPacked 547 (maskedCandidates 547 256 256)
      0x11b00011b00011b00111e00111e001124003 = true := by decide +kernel
  have replay13_2 : fastPacked 547 (maskedCandidates 547 512 128)
      0x11900011900011a00011a00011a000 = true := by decide +kernel
  have hs : p*p ≤ 547^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 640 := by
    have hc : (547^3 : ℕ).sqrt = 12793 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 3 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay13_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay13_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay13_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked14 {p : ℕ} (hp : p.Prime) (hlo : 2*587 < p)
    (hhi : p^2 < 587^3) (hmod : p%3 ≠ 587%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 587 = true) :
    ∃ d, signCertificate p 587 d = true := by
  have replay14_0 : fastPacked 587 (maskedCandidates 587 0 256)
      0 = true := by decide +kernel
  have replay14_1 : fastPacked 587 (maskedCandidates 587 256 256)
      0x139003 = true := by decide +kernel
  have replay14_2 : fastPacked 587 (maskedCandidates 587 512 200)
      0 = true := by decide +kernel
  have hs : p*p ≤ 587^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 712 := by
    have hc : (587^3 : ℕ).sqrt = 14221 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 3 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay14_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay14_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay14_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked19 {p : ℕ} (hp : p.Prime) (hlo : 2*787 < p)
    (hhi : p^2 < 787^3) (hmod : p%3 ≠ 787%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 787 = true) :
    ∃ d, signCertificate p 787 d = true := by
  have replay19_0 : fastPacked 787 (maskedCandidates 787 0 256)
      0x1c301400012a = true := by decide +kernel
  have replay19_1 : fastPacked 787 (maskedCandidates 787 256 256)
      0x19d00219e0031a6006 = true := by decide +kernel
  have replay19_2 : fastPacked 787 (maskedCandidates 787 512 256)
      0x19500119800119800119900119900119b002 = true := by decide +kernel
  have replay19_3 : fastPacked 787 (maskedCandidates 787 768 256)
      0x194000195001195001 = true := by decide +kernel
  have replay19_4 : fastPacked 787 (maskedCandidates 787 1024 80)
      0x192000 = true := by decide +kernel
  have hs : p*p ≤ 787^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1104 := by
    have hc : (787^3 : ℕ).sqrt = 22078 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 5 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay19_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay19_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay19_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay19_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay19_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked20 {p : ℕ} (hp : p.Prime) (hlo : 2*827 < p)
    (hhi : p^2 < 827^3) (hmod : p%3 ≠ 827%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 827 = true) :
    ∃ d, signCertificate p 827 d = true := by
  have replay20_0 : fastPacked 827 (maskedCandidates 827 0 256)
      0x1de0181f30262a70c4 = true := by decide +kernel
  have replay20_1 : fastPacked 827 (maskedCandidates 827 256 256)
      0x1b40031b80051b90051bb006 = true := by decide +kernel
  have replay20_2 : fastPacked 827 (maskedCandidates 827 512 256)
      0x1ab0011ab0011ac0011ad0011ae0011af0021b1002 = true := by decide +kernel
  have replay20_3 : fastPacked 827 (maskedCandidates 827 768 256)
      0 = true := by decide +kernel
  have replay20_4 : fastPacked 827 (maskedCandidates 827 1024 166)
      0x1a70001a7000 = true := by decide +kernel
  have hs : p*p ≤ 827^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1190 := by
    have hc : (827^3 : ℕ).sqrt = 23782 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 5 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay20_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay20_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay20_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay20_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay20_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked22 {p : ℕ} (hp : p.Prime) (hlo : 2*907 < p)
    (hhi : p^2 < 907^3) (hmod : p%3 ≠ 907%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 907 = true) :
    ∃ d, signCertificate p 907 d = true := by
  have replay22_0 : fastPacked 907 (maskedCandidates 907 0 256)
      0x21d02623a03b = true := by decide +kernel
  have replay22_1 : fastPacked 907 (maskedCandidates 907 256 256)
      0x1f300c = true := by decide +kernel
  have replay22_2 : fastPacked 907 (maskedCandidates 907 512 256)
      0x1da002 = true := by decide +kernel
  have replay22_3 : fastPacked 907 (maskedCandidates 907 768 256)
      0x1d20011d30011d40011d5001 = true := by decide +kernel
  have replay22_4 : fastPacked 907 (maskedCandidates 907 1024 256)
      0x1cf0001d00001d0000 = true := by decide +kernel
  have replay22_5 : fastPacked 907 (maskedCandidates 907 1280 86)
      0x1cf0001cf000 = true := by decide +kernel
  have hs : p*p ≤ 907^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1366 := by
    have hc : (907^3 : ℕ).sqrt = 27315 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 6 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay22_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay22_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay22_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay22_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay22_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay22_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked23 {p : ℕ} (hp : p.Prime) (hlo : 2*947 < p)
    (hhi : p^2 < 947^3) (hmod : p%3 ≠ 947%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 947 = true) :
    ∃ d, signCertificate p 947 d = true := by
  have replay23_0 : fastPacked 947 (maskedCandidates 947 0 256)
      0x218014232025 = true := by decide +kernel
  have replay23_1 : fastPacked 947 (maskedCandidates 947 256 256)
      0x212011 = true := by decide +kernel
  have replay23_2 : fastPacked 947 (maskedCandidates 947 512 256)
      0x1ec0021ed0021ed0021ed0021ef002 = true := by decide +kernel
  have replay23_3 : fastPacked 947 (maskedCandidates 947 768 256)
      0x1e60011e80011e9001 = true := by decide +kernel
  have replay23_4 : fastPacked 947 (maskedCandidates 947 1024 256)
      0x1e40001e40001e50001e5000 = true := by decide +kernel
  have replay23_5 : fastPacked 947 (maskedCandidates 947 1280 178)
      0x1e3000 = true := by decide +kernel
  have hs : p*p ≤ 947^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 1458 := by
    have hc : (947^3 : ℕ).sqrt = 29142 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 6 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay23_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay23_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay23_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay23_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay23_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay23_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked29 {p : ℕ} (hp : p.Prime) (hlo : 2*1187 < p)
    (hhi : p^2 < 1187^3) (hmod : p%3 ≠ 1187%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1187 = true) :
    ∃ d, signCertificate p 1187 d = true := by
  have replay29_0 : fastPacked 1187 (maskedCandidates 1187 0 256)
      0x2db0422df0452f805834e0a23760c600019a0000f2 = true := by decide +kernel
  have replay29_1 : fastPacked 1187 (maskedCandidates 1187 256 256)
      0x27e00928300b28400c28600d28600d28700d28f01129001229c0182a001a2b1024 = true := by decide +kernel
  have replay29_2 : fastPacked 1187 (maskedCandidates 1187 512 256)
      0x26d00326e00426f00427500627a008 = true := by decide +kernel
  have replay29_3 : fastPacked 1187 (maskedCandidates 1187 768 256)
      0x26600226600226a00326c003 = true := by decide +kernel
  have replay29_4 : fastPacked 1187 (maskedCandidates 1187 1024 256)
      0x262001262001263001263001264001265001265002 = true := by decide +kernel
  have replay29_5 : fastPacked 1187 (maskedCandidates 1187 1280 256)
      0x25f001260001260001260001260001260001261001261001 = true := by decide +kernel
  have replay29_6 : fastPacked 1187 (maskedCandidates 1187 1536 256)
      0x25d00025d00025e00025e00025e00025e00025e00025e000 = true := by decide +kernel
  have replay29_7 : fastPacked 1187 (maskedCandidates 1187 1792 253)
      0x25c00025c00025c00025c00025c00025c00025c00025c00025d00025d00025d000 = true := by decide +kernel
  have hs : p*p ≤ 1187^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 2045 := by
    have hc : (1187^3 : ℕ).sqrt = 40895 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 8 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay29_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay29_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay29_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay29_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay29_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay29_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay29_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay29_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked32 {p : ℕ} (hp : p.Prime) (hlo : 2*1307 < p)
    (hhi : p^2 < 1307^3) (hmod : p%3 ≠ 1307%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1307 = true) :
    ∃ d, signCertificate p 1307 d = true := by
  have replay32_0 : fastPacked 1307 (maskedCandidates 1307 0 256)
      0x332052000193 = true := by decide +kernel
  have replay32_1 : fastPacked 1307 (maskedCandidates 1307 256 256)
      0x2c300c2c400d2c400d2cf0122d90172f102530102f = true := by decide +kernel
  have replay32_2 : fastPacked 1307 (maskedCandidates 1307 512 256)
      0x2b00052b10062b20062b70072b70082bb0092bf00a = true := by decide +kernel
  have replay32_3 : fastPacked 1307 (maskedCandidates 1307 768 256)
      0x2a60022a70032a8003 = true := by decide +kernel
  have replay32_4 : fastPacked 1307 (maskedCandidates 1307 1024 256)
      0x2a10012a4002 = true := by decide +kernel
  have replay32_5 : fastPacked 1307 (maskedCandidates 1307 1280 256)
      0x29e00129e00129e00129f00129f001 = true := by decide +kernel
  have replay32_6 : fastPacked 1307 (maskedCandidates 1307 1536 256)
      0x29c00029c00029c00129c00129c00129d001 = true := by decide +kernel
  have replay32_7 : fastPacked 1307 (maskedCandidates 1307 1792 256)
      0x29a00029b00029b00029b00029b000 = true := by decide +kernel
  have replay32_8 : fastPacked 1307 (maskedCandidates 1307 2048 256)
      0x298000298000298000298000299000299000299000299000299000 = true := by decide +kernel
  have replay32_9 : fastPacked 1307 (maskedCandidates 1307 2304 59)
      0x298000 = true := by decide +kernel
  have hs : p*p ≤ 1307^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 2363 := by
    have hc : (1307^3 : ℕ).sqrt = 47251 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 10 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay32_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay32_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked35 {p : ℕ} (hp : p.Prime) (hlo : 2*1427 < p)
    (hhi : p^2 < 1427^3) (hmod : p%3 ≠ 1427%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1427 = true) :
    ∃ d, signCertificate p 1427 d = true := by
  have replay35_0 : fastPacked 1427 (maskedCandidates 1427 0 256)
      0 = true := by decide +kernel
  have replay35_1 : fastPacked 1427 (maskedCandidates 1427 256 256)
      0 = true := by decide +kernel
  have replay35_2 : fastPacked 1427 (maskedCandidates 1427 512 256)
      0x2f10062f90092fb00a = true := by decide +kernel
  have replay35_3 : fastPacked 1427 (maskedCandidates 1427 768 256)
      0x2e70032e80042e80042ef006 = true := by decide +kernel
  have replay35_4 : fastPacked 1427 (maskedCandidates 1427 1024 256)
      0 = true := by decide +kernel
  have replay35_5 : fastPacked 1427 (maskedCandidates 1427 1280 256)
      0x2de0012e0002 = true := by decide +kernel
  have replay35_6 : fastPacked 1427 (maskedCandidates 1427 1536 256)
      0x2db001 = true := by decide +kernel
  have replay35_7 : fastPacked 1427 (maskedCandidates 1427 1792 256)
      0x2d80002d80002d8001 = true := by decide +kernel
  have replay35_8 : fastPacked 1427 (maskedCandidates 1427 2048 256)
      0x2d60002d70002d8000 = true := by decide +kernel
  have replay35_9 : fastPacked 1427 (maskedCandidates 1427 2304 256)
      0 = true := by decide +kernel
  have replay35_10 : fastPacked 1427 (maskedCandidates 1427 2560 136)
      0x2d50002d5000 = true := by decide +kernel
  have hs : p*p ≤ 1427^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 2696 := by
    have hc : (1427^3 : ℕ).sqrt = 53905 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 11 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay35_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay35_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked40 {p : ℕ} (hp : p.Prime) (hlo : 2*1627 < p)
    (hhi : p^2 < 1627^3) (hmod : p%3 ≠ 1627%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1627 = true) :
    ∃ d, signCertificate p 1627 d = true := by
  have replay40_0 : fastPacked 1627 (maskedCandidates 1627 0 256)
      0x4870de000261 = true := by decide +kernel
  have replay40_1 : fastPacked 1627 (maskedCandidates 1627 256 256)
      0 = true := by decide +kernel
  have replay40_2 : fastPacked 1627 (maskedCandidates 1627 512 256)
      0x36400b36800c36b00d = true := by decide +kernel
  have replay40_3 : fastPacked 1627 (maskedCandidates 1627 768 256)
      0x35d008 = true := by decide +kernel
  have replay40_4 : fastPacked 1627 (maskedCandidates 1627 1024 256)
      0x34e004 = true := by decide +kernel
  have replay40_5 : fastPacked 1627 (maskedCandidates 1627 1280 256)
      0 = true := by decide +kernel
  have replay40_6 : fastPacked 1627 (maskedCandidates 1627 1536 256)
      0 = true := by decide +kernel
  have replay40_7 : fastPacked 1627 (maskedCandidates 1627 1792 256)
      0x340001341001341001 = true := by decide +kernel
  have replay40_8 : fastPacked 1627 (maskedCandidates 1627 2048 256)
      0 = true := by decide +kernel
  have replay40_9 : fastPacked 1627 (maskedCandidates 1627 2304 256)
      0x33c00033d000 = true := by decide +kernel
  have replay40_10 : fastPacked 1627 (maskedCandidates 1627 2560 256)
      0x33b00033b000 = true := by decide +kernel
  have replay40_11 : fastPacked 1627 (maskedCandidates 1627 2816 256)
      0 = true := by decide +kernel
  have replay40_12 : fastPacked 1627 (maskedCandidates 1627 3072 210)
      0x33900033a000 = true := by decide +kernel
  have hs : p*p ≤ 1627^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3282 := by
    have hc : (1627^3 : ℕ).sqrt = 65626 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 13 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay40_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay40_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked41 {p : ℕ} (hp : p.Prime) (hlo : 2*1667 < p)
    (hhi : p^2 < 1667^3) (hmod : p%3 ≠ 1667%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1667 = true) :
    ∃ d, signCertificate p 1667 d = true := by
  have replay41_0 : fastPacked 1667 (maskedCandidates 1667 0 256)
      0x49e0de65d28b0002a7000257 = true := by decide +kernel
  have replay41_1 : fastPacked 1667 (maskedCandidates 1667 256 256)
      0x3ab0233ad0243bc02c3c30313e404742f080 = true := by decide +kernel
  have replay41_2 : fastPacked 1667 (maskedCandidates 1667 512 256)
      0x37900b37b00b37f00d38501038b01238c01339401739601739601839c01b = true := by decide +kernel
  have replay41_3 : fastPacked 1667 (maskedCandidates 1667 768 256)
      0x36900636a00636e007370008370008372008375009 = true := by decide +kernel
  have replay41_4 : fastPacked 1667 (maskedCandidates 1667 1024 256)
      0x361003361004361004362004365004366005368005368005368005 = true := by decide +kernel
  have replay41_5 : fastPacked 1667 (maskedCandidates 1667 1280 256)
      0x35b00235b00235c00235d00235d00235d00335e00335f00335f003360003360003360003 = true := by decide +kernel
  have replay41_6 : fastPacked 1667 (maskedCandidates 1667 1536 256)
      0x35800135800135800135800235800235800235900235900235900235a00235a00235a00235a00235b00235b002 = true := by decide +kernel
  have replay41_7 : fastPacked 1667 (maskedCandidates 1667 1792 256)
      0x355001355001356001356001356001357001 = true := by decide +kernel
  have replay41_8 : fastPacked 1667 (maskedCandidates 1667 2048 256)
      0x352001353001353001353001353001354001354001354001354001 = true := by decide +kernel
  have replay41_9 : fastPacked 1667 (maskedCandidates 1667 2304 256)
      0x351000351000351000351000351000351000351000351000351001352001352001352001352001 = true := by decide +kernel
  have replay41_10 : fastPacked 1667 (maskedCandidates 1667 2560 256)
      0x34f000350000350000350000350000350000350000350000350000351000351000 = true := by decide +kernel
  have replay41_11 : fastPacked 1667 (maskedCandidates 1667 2816 256)
      0x34f00034f00034f00034f00034f00034f00034f00034f000 = true := by decide +kernel
  have replay41_12 : fastPacked 1667 (maskedCandidates 1667 3072 256)
      0x34d00034d00034d00034e00034e00034e00034e00034e00034e00034e00034e000 = true := by decide +kernel
  have replay41_13 : fastPacked 1667 (maskedCandidates 1667 3328 76)
      0x34d00034d000 = true := by decide +kernel
  have hs : p*p ≤ 1667^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3404 := by
    have hc : (1667^3 : ℕ).sqrt = 68061 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 14 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay41_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay41_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked43 {p : ℕ} (hp : p.Prime) (hlo : 2*1747 < p)
    (hhi : p^2 < 1747^3) (hmod : p%3 ≠ 1747%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1747 = true) :
    ∃ d, signCertificate p 1747 d = true := by
  have replay43_0 : fastPacked 1747 (maskedCandidates 1747 0 256)
      0x5271320001eb = true := by decide +kernel
  have replay43_1 : fastPacked 1747 (maskedCandidates 1747 256 256)
      0x3d10203db0263e702d3f00334650874850a2 = true := by decide +kernel
  have replay43_2 : fastPacked 1747 (maskedCandidates 1747 512 256)
      0x3ae0103b30123b40123c601a3c801c = true := by decide +kernel
  have replay43_3 : fastPacked 1747 (maskedCandidates 1747 768 256)
      0x39700739b00839b00839d0093a300b = true := by decide +kernel
  have replay43_4 : fastPacked 1747 (maskedCandidates 1747 1024 256)
      0x38c00438e00538e005 = true := by decide +kernel
  have replay43_5 : fastPacked 1747 (maskedCandidates 1747 1280 256)
      0x38600338600338600338b004 = true := by decide +kernel
  have replay43_6 : fastPacked 1747 (maskedCandidates 1747 1536 256)
      0x382002382002383002 = true := by decide +kernel
  have replay43_7 : fastPacked 1747 (maskedCandidates 1747 1792 256)
      0x37f001380001380001 = true := by decide +kernel
  have replay43_8 : fastPacked 1747 (maskedCandidates 1747 2048 256)
      0x37c00137d00137d00137e001 = true := by decide +kernel
  have replay43_9 : fastPacked 1747 (maskedCandidates 1747 2304 256)
      0x37b00137c001 = true := by decide +kernel
  have replay43_10 : fastPacked 1747 (maskedCandidates 1747 2560 256)
      0x37900037a00037a00137a001 = true := by decide +kernel
  have replay43_11 : fastPacked 1747 (maskedCandidates 1747 2816 256)
      0x378000379000 = true := by decide +kernel
  have replay43_12 : fastPacked 1747 (maskedCandidates 1747 3072 256)
      0x377000377000377000377000 = true := by decide +kernel
  have replay43_13 : fastPacked 1747 (maskedCandidates 1747 3328 256)
      0x376000376000376000376000376000376000376000 = true := by decide +kernel
  have replay43_14 : fastPacked 1747 (maskedCandidates 1747 3584 67)
      0x375000 = true := by decide +kernel
  have hs : p*p ≤ 1747^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3651 := by
    have hc : (1747^3 : ℕ).sqrt = 73019 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 15 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay43_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay43_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked44 {p : ℕ} (hp : p.Prime) (hlo : 2*1787 < p)
    (hhi : p^2 < 1787^3) (hmod : p%3 ≠ 1787%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1787 = true) :
    ∃ d, signCertificate p 1787 d = true := by
  have replay44_0 : fastPacked 1787 (maskedCandidates 1787 0 256)
      0 = true := by decide +kernel
  have replay44_1 : fastPacked 1787 (maskedCandidates 1787 256 256)
      0x41a040 = true := by decide +kernel
  have replay44_2 : fastPacked 1787 (maskedCandidates 1787 512 256)
      0x3c60113d3017 = true := by decide +kernel
  have replay44_3 : fastPacked 1787 (maskedCandidates 1787 768 256)
      0x3ac0073b3009 = true := by decide +kernel
  have replay44_4 : fastPacked 1787 (maskedCandidates 1787 1024 256)
      0x3a50053ab007 = true := by decide +kernel
  have replay44_5 : fastPacked 1787 (maskedCandidates 1787 1280 256)
      0x39e003 = true := by decide +kernel
  have replay44_6 : fastPacked 1787 (maskedCandidates 1787 1536 256)
      0x39900239a003 = true := by decide +kernel
  have replay44_7 : fastPacked 1787 (maskedCandidates 1787 1792 256)
      0x396002 = true := by decide +kernel
  have replay44_8 : fastPacked 1787 (maskedCandidates 1787 2048 256)
      0 = true := by decide +kernel
  have replay44_9 : fastPacked 1787 (maskedCandidates 1787 2304 256)
      0 = true := by decide +kernel
  have replay44_10 : fastPacked 1787 (maskedCandidates 1787 2560 256)
      0x38e00038e00038f001 = true := by decide +kernel
  have replay44_11 : fastPacked 1787 (maskedCandidates 1787 2816 256)
      0x38d00038d000 = true := by decide +kernel
  have replay44_12 : fastPacked 1787 (maskedCandidates 1787 3072 256)
      0x38b00038b000 = true := by decide +kernel
  have replay44_13 : fastPacked 1787 (maskedCandidates 1787 3328 256)
      0x38a00038b000 = true := by decide +kernel
  have replay44_14 : fastPacked 1787 (maskedCandidates 1787 3584 194)
      0x38a000 = true := by decide +kernel
  have hs : p*p ≤ 1787^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 3778 := by
    have hc : (1787^3 : ℕ).sqrt = 75541 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 15 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay44_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay44_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked46 {p : ℕ} (hp : p.Prime) (hlo : 2*1867 < p)
    (hhi : p^2 < 1867^3) (hmod : p%3 ≠ 1867%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1867 = true) :
    ∃ d, signCertificate p 1867 d = true := by
  have replay46_0 : fastPacked 1867 (maskedCandidates 1867 0 256)
      0 = true := by decide +kernel
  have replay46_1 : fastPacked 1867 (maskedCandidates 1867 256 256)
      0x42002942102a43503647e069 = true := by decide +kernel
  have replay46_2 : fastPacked 1867 (maskedCandidates 1867 512 256)
      0x3f50133f50133fc01641102141302241c027 = true := by decide +kernel
  have replay46_3 : fastPacked 1867 (maskedCandidates 1867 768 256)
      0x3db0093de00a3df00a3e100b3e400c3e600d3eb00f3eb00f = true := by decide +kernel
  have replay46_4 : fastPacked 1867 (maskedCandidates 1867 1024 256)
      0x3cd0053cd0053d40073d40073d70083d7008 = true := by decide +kernel
  have replay46_5 : fastPacked 1867 (maskedCandidates 1867 1280 256)
      0x3c60033ca0043cb004 = true := by decide +kernel
  have replay46_6 : fastPacked 1867 (maskedCandidates 1867 1536 256)
      0x3c10023c10023c20023c30033c30033c40033c50033c6003 = true := by decide +kernel
  have replay46_7 : fastPacked 1867 (maskedCandidates 1867 1792 256)
      0x3be0023be0023bf0023c0002 = true := by decide +kernel
  have replay46_8 : fastPacked 1867 (maskedCandidates 1867 2048 256)
      0x3bb0013bc0013bd0013bd002 = true := by decide +kernel
  have replay46_9 : fastPacked 1867 (maskedCandidates 1867 2304 256)
      0x3b90013b90013ba0013ba0013ba001 = true := by decide +kernel
  have replay46_10 : fastPacked 1867 (maskedCandidates 1867 2560 256)
      0x3b70013b70013b70013b80013b80013b8001 = true := by decide +kernel
  have replay46_11 : fastPacked 1867 (maskedCandidates 1867 2816 256)
      0x3b50003b60003b60003b60003b60003b60013b70013b7001 = true := by decide +kernel
  have replay46_12 : fastPacked 1867 (maskedCandidates 1867 3072 256)
      0x3b40003b40003b50003b50003b50003b50003b5000 = true := by decide +kernel
  have replay46_13 : fastPacked 1867 (maskedCandidates 1867 3328 256)
      0x3b30003b30003b40003b40003b40003b4000 = true := by decide +kernel
  have replay46_14 : fastPacked 1867 (maskedCandidates 1867 3584 256)
      0x3b20003b20003b20003b20003b30003b30003b30003b3000 = true := by decide +kernel
  have replay46_15 : fastPacked 1867 (maskedCandidates 1867 3840 194)
      0x3b2000 = true := by decide +kernel
  have hs : p*p ≤ 1867^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4034 := by
    have hc : (1867^3 : ℕ).sqrt = 80670 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 16 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay46_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay46_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked47 {p : ℕ} (hp : p.Prime) (hlo : 2*1907 < p)
    (hhi : p^2 < 1907^3) (hmod : p%3 ≠ 1907%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1907 = true) :
    ∃ d, signCertificate p 1907 d = true := by
  have replay47_0 : fastPacked 1907 (maskedCandidates 1907 0 256)
      0 = true := by decide +kernel
  have replay47_1 : fastPacked 1907 (maskedCandidates 1907 256 256)
      0 = true := by decide +kernel
  have replay47_2 : fastPacked 1907 (maskedCandidates 1907 512 256)
      0 = true := by decide +kernel
  have replay47_3 : fastPacked 1907 (maskedCandidates 1907 768 256)
      0x3f0009 = true := by decide +kernel
  have replay47_4 : fastPacked 1907 (maskedCandidates 1907 1024 256)
      0x3e40063e70063ea007 = true := by decide +kernel
  have replay47_5 : fastPacked 1907 (maskedCandidates 1907 1280 256)
      0 = true := by decide +kernel
  have replay47_6 : fastPacked 1907 (maskedCandidates 1907 1536 256)
      0x3d7002 = true := by decide +kernel
  have replay47_7 : fastPacked 1907 (maskedCandidates 1907 1792 256)
      0 = true := by decide +kernel
  have replay47_8 : fastPacked 1907 (maskedCandidates 1907 2048 256)
      0x3d00013d0001 = true := by decide +kernel
  have replay47_9 : fastPacked 1907 (maskedCandidates 1907 2304 256)
      0 = true := by decide +kernel
  have replay47_10 : fastPacked 1907 (maskedCandidates 1907 2560 256)
      0x3cc001 = true := by decide +kernel
  have replay47_11 : fastPacked 1907 (maskedCandidates 1907 2816 256)
      0x3cb0013cb0013cb001 = true := by decide +kernel
  have replay47_12 : fastPacked 1907 (maskedCandidates 1907 3072 256)
      0x3c90003ca0003ca000 = true := by decide +kernel
  have replay47_13 : fastPacked 1907 (maskedCandidates 1907 3328 256)
      0 = true := by decide +kernel
  have replay47_14 : fastPacked 1907 (maskedCandidates 1907 3584 256)
      0 = true := by decide +kernel
  have replay47_15 : fastPacked 1907 (maskedCandidates 1907 3840 256)
      0 = true := by decide +kernel
  have replay47_16 : fastPacked 1907 (maskedCandidates 1907 4096 68)
      0 = true := by decide +kernel
  have hs : p*p ≤ 1907^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4164 := by
    have hc : (1907^3 : ℕ).sqrt = 83277 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 17 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay47_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay47_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked49 {p : ℕ} (hp : p.Prime) (hlo : 2*1987 < p)
    (hhi : p^2 < 1987^3) (hmod : p%3 ≠ 1987%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 1987 = true) :
    ∃ d, signCertificate p 1987 d = true := by
  have replay49_0 : fastPacked 1987 (maskedCandidates 1987 0 256)
      0 = true := by decide +kernel
  have replay49_1 : fastPacked 1987 (maskedCandidates 1987 256 256)
      0x4cd07350309d5470d6 = true := by decide +kernel
  have replay49_2 : fastPacked 1987 (maskedCandidates 1987 512 256)
      0x43701543f01944601c44f021 = true := by decide +kernel
  have replay49_3 : fastPacked 1987 (maskedCandidates 1987 768 256)
      0x42100c42700e42b010 = true := by decide +kernel
  have replay49_4 : fastPacked 1987 (maskedCandidates 1987 1024 256)
      0x40e006411007415008418009 = true := by decide +kernel
  have replay49_5 : fastPacked 1987 (maskedCandidates 1987 1280 256)
      0x40700440a00540b005 = true := by decide +kernel
  have replay49_6 : fastPacked 1987 (maskedCandidates 1987 1536 256)
      0x401003 = true := by decide +kernel
  have replay49_7 : fastPacked 1987 (maskedCandidates 1987 1792 256)
      0x3fd0023fe0023ff002 = true := by decide +kernel
  have replay49_8 : fastPacked 1987 (maskedCandidates 1987 2048 256)
      0x3fb0023fb0023fc002 = true := by decide +kernel
  have replay49_9 : fastPacked 1987 (maskedCandidates 1987 2304 256)
      0x3f80013f80013f8001 = true := by decide +kernel
  have replay49_10 : fastPacked 1987 (maskedCandidates 1987 2560 256)
      0x3f60013f60013f70013f7001 = true := by decide +kernel
  have replay49_11 : fastPacked 1987 (maskedCandidates 1987 2816 256)
      0x3f40013f40013f50013f5001 = true := by decide +kernel
  have replay49_12 : fastPacked 1987 (maskedCandidates 1987 3072 256)
      0x3f20003f20003f20003f20003f30013f30013f3001 = true := by decide +kernel
  have replay49_13 : fastPacked 1987 (maskedCandidates 1987 3328 256)
      0x3f10003f10003f10003f20003f20003f2000 = true := by decide +kernel
  have replay49_14 : fastPacked 1987 (maskedCandidates 1987 3584 256)
      0x3f00003f1000 = true := by decide +kernel
  have replay49_15 : fastPacked 1987 (maskedCandidates 1987 3840 256)
      0x3ef0003ef0003ef0003f00003f0000 = true := by decide +kernel
  have replay49_16 : fastPacked 1987 (maskedCandidates 1987 4096 256)
      0x3ee0003ee0003ee0003ef0003ef000 = true := by decide +kernel
  have replay49_17 : fastPacked 1987 (maskedCandidates 1987 4352 77)
      0x3ee000 = true := by decide +kernel
  have hs : p*p ≤ 1987^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4429 := by
    have hc : (1987^3 : ℕ).sqrt = 88572 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 18 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay49_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay49_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked50 {p : ℕ} (hp : p.Prime) (hlo : 2*2027 < p)
    (hhi : p^2 < 2027^3) (hmod : p%3 ≠ 2027%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 2027 = true) :
    ∃ d, signCertificate p 2027 d = true := by
  have replay50_0 : fastPacked 2027 (maskedCandidates 2027 0 256)
      0 = true := by decide +kernel
  have replay50_1 : fastPacked 2027 (maskedCandidates 2027 256 256)
      0x49403c4b004f4b5052 = true := by decide +kernel
  have replay50_2 : fastPacked 2027 (maskedCandidates 2027 512 256)
      0x44a01444e01645401945c01d46c02547802c47e02f = true := by decide +kernel
  have replay50_3 : fastPacked 2027 (maskedCandidates 2027 768 256)
      0x43100b43500c43c00e442011446013447013447013 = true := by decide +kernel
  have replay50_4 : fastPacked 2027 (maskedCandidates 2027 1024 256)
      0x42500742b00942d00943100b = true := by decide +kernel
  have replay50_5 : fastPacked 2027 (maskedCandidates 2027 1280 256)
      0x41c00441f00541f005 = true := by decide +kernel
  have replay50_6 : fastPacked 2027 (maskedCandidates 2027 1536 256)
      0x41800341900441900441a00441b00441b00441c004 = true := by decide +kernel
  have replay50_7 : fastPacked 2027 (maskedCandidates 2027 1792 256)
      0x412002413002413002413002414003414003414003416003 = true := by decide +kernel
  have replay50_8 : fastPacked 2027 (maskedCandidates 2027 2048 256)
      0x410002410002411002411002412002 = true := by decide +kernel
  have replay50_9 : fastPacked 2027 (maskedCandidates 2027 2304 256)
      0x40c00140c00140d00140d001 = true := by decide +kernel
  have replay50_10 : fastPacked 2027 (maskedCandidates 2027 2560 256)
      0x40a00140a00140b00140c001 = true := by decide +kernel
  have replay50_11 : fastPacked 2027 (maskedCandidates 2027 2816 256)
      0x408001409001409001 = true := by decide +kernel
  have replay50_12 : fastPacked 2027 (maskedCandidates 2027 3072 256)
      0x407001407001408001408001 = true := by decide +kernel
  have replay50_13 : fastPacked 2027 (maskedCandidates 2027 3328 256)
      0x405000406000406000406000406000406000406000406000407000 = true := by decide +kernel
  have replay50_14 : fastPacked 2027 (maskedCandidates 2027 3584 256)
      0x404000405000405000405000405000405000405000405000405000405000405000 = true := by decide +kernel
  have replay50_15 : fastPacked 2027 (maskedCandidates 2027 3840 256)
      0x404000404000404000404000 = true := by decide +kernel
  have replay50_16 : fastPacked 2027 (maskedCandidates 2027 4096 256)
      0x403000403000403000403000403000 = true := by decide +kernel
  have replay50_17 : fastPacked 2027 (maskedCandidates 2027 4352 212)
      0x402000402000402000403000403000403000403000 = true := by decide +kernel
  have hs : p*p ≤ 2027^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 4564 := by
    have hc : (2027^3 : ℕ).sqrt = 91260 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 18 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay50_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay50_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked56 {p : ℕ} (hp : p.Prime) (hlo : 2*2267 < p)
    (hhi : p^2 < 2267^3) (hmod : p%3 ≠ 2267%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 2267 = true) :
    ∃ d, signCertificate p 2267 d = true := by
  have replay56_0 : fastPacked 2267 (maskedCandidates 2267 0 256)
      0 = true := by decide +kernel
  have replay56_1 : fastPacked 2267 (maskedCandidates 2267 256 256)
      0 = true := by decide +kernel
  have replay56_2 : fastPacked 2267 (maskedCandidates 2267 512 256)
      0 = true := by decide +kernel
  have replay56_3 : fastPacked 2267 (maskedCandidates 2267 768 256)
      0x4bb010 = true := by decide +kernel
  have replay56_4 : fastPacked 2267 (maskedCandidates 2267 1024 256)
      0x4ad00b4b000c = true := by decide +kernel
  have replay56_5 : fastPacked 2267 (maskedCandidates 2267 1280 256)
      0x4a10074a3008 = true := by decide +kernel
  have replay56_6 : fastPacked 2267 (maskedCandidates 2267 1536 256)
      0x49800549a00549b006 = true := by decide +kernel
  have replay56_7 : fastPacked 2267 (maskedCandidates 2267 1792 256)
      0x495004495004 = true := by decide +kernel
  have replay56_8 : fastPacked 2267 (maskedCandidates 2267 2048 256)
      0x48d00248f003490003 = true := by decide +kernel
  have replay56_9 : fastPacked 2267 (maskedCandidates 2267 2304 256)
      0 = true := by decide +kernel
  have replay56_10 : fastPacked 2267 (maskedCandidates 2267 2560 256)
      0x488002489002 = true := by decide +kernel
  have replay56_11 : fastPacked 2267 (maskedCandidates 2267 2816 256)
      0x485001487001 = true := by decide +kernel
  have replay56_12 : fastPacked 2267 (maskedCandidates 2267 3072 256)
      0x484001 = true := by decide +kernel
  have replay56_13 : fastPacked 2267 (maskedCandidates 2267 3328 256)
      0x482001482001 = true := by decide +kernel
  have replay56_14 : fastPacked 2267 (maskedCandidates 2267 3584 256)
      0 = true := by decide +kernel
  have replay56_15 : fastPacked 2267 (maskedCandidates 2267 3840 256)
      0x47f000 = true := by decide +kernel
  have replay56_16 : fastPacked 2267 (maskedCandidates 2267 4096 256)
      0x47e00047e000 = true := by decide +kernel
  have replay56_17 : fastPacked 2267 (maskedCandidates 2267 4352 256)
      0 = true := by decide +kernel
  have replay56_18 : fastPacked 2267 (maskedCandidates 2267 4608 256)
      0x47d000 = true := by decide +kernel
  have replay56_19 : fastPacked 2267 (maskedCandidates 2267 4864 256)
      0x47c000 = true := by decide +kernel
  have replay56_20 : fastPacked 2267 (maskedCandidates 2267 5120 256)
      0x47b00047b000 = true := by decide +kernel
  have replay56_21 : fastPacked 2267 (maskedCandidates 2267 5376 21)
      0 = true := by decide +kernel
  have hs : p*p ≤ 2267^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 5397 := by
    have hc : (2267^3 : ℕ).sqrt = 107938 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 22 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay56_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay56_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked58 {p : ℕ} (hp : p.Prime) (hlo : 2*2347 < p)
    (hhi : p^2 < 2347^3) (hmod : p%3 ≠ 2347%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 2347 = true) :
    ∃ d, signCertificate p 2347 d = true := by
  have replay58_0 : fastPacked 2347 (maskedCandidates 2347 0 256)
      0 = true := by decide +kernel
  have replay58_1 : fastPacked 2347 (maskedCandidates 2347 256 256)
      0x5ff0ca63c0fd = true := by decide +kernel
  have replay58_2 : fastPacked 2347 (maskedCandidates 2347 512 256)
      0x51c029 = true := by decide +kernel
  have replay58_3 : fastPacked 2347 (maskedCandidates 2347 768 256)
      0x50a020 = true := by decide +kernel
  have replay58_4 : fastPacked 2347 (maskedCandidates 2347 1024 256)
      0x4d700b4dc00d4e300f = true := by decide +kernel
  have replay58_5 : fastPacked 2347 (maskedCandidates 2347 1280 256)
      0x4cb0074ce0084d1009 = true := by decide +kernel
  have replay58_6 : fastPacked 2347 (maskedCandidates 2347 1536 256)
      0x4c10054c30054c30054c4006 = true := by decide +kernel
  have replay58_7 : fastPacked 2347 (maskedCandidates 2347 1792 256)
      0x4be0044bf004 = true := by decide +kernel
  have replay58_8 : fastPacked 2347 (maskedCandidates 2347 2048 256)
      0x4b80034bb004 = true := by decide +kernel
  have replay58_9 : fastPacked 2347 (maskedCandidates 2347 2304 256)
      0 = true := by decide +kernel
  have replay58_10 : fastPacked 2347 (maskedCandidates 2347 2560 256)
      0x4b20024b20024b30024b3002 = true := by decide +kernel
  have replay58_11 : fastPacked 2347 (maskedCandidates 2347 2816 256)
      0x4ae0014af0014b0002 = true := by decide +kernel
  have replay58_12 : fastPacked 2347 (maskedCandidates 2347 3072 256)
      0x4ac0014ad0014ae001 = true := by decide +kernel
  have replay58_13 : fastPacked 2347 (maskedCandidates 2347 3328 256)
      0x4ab001 = true := by decide +kernel
  have replay58_14 : fastPacked 2347 (maskedCandidates 2347 3584 256)
      0x4a90014aa0014aa0014aa0014aa001 = true := by decide +kernel
  have replay58_15 : fastPacked 2347 (maskedCandidates 2347 3840 256)
      0 = true := by decide +kernel
  have replay58_16 : fastPacked 2347 (maskedCandidates 2347 4096 256)
      0x4a70004a70004a80004a8000 = true := by decide +kernel
  have replay58_17 : fastPacked 2347 (maskedCandidates 2347 4352 256)
      0x4a7000 = true := by decide +kernel
  have replay58_18 : fastPacked 2347 (maskedCandidates 2347 4608 256)
      0x4a50004a50004a6000 = true := by decide +kernel
  have replay58_19 : fastPacked 2347 (maskedCandidates 2347 4864 256)
      0x4a5000 = true := by decide +kernel
  have replay58_20 : fastPacked 2347 (maskedCandidates 2347 5120 256)
      0x4a40004a40004a40004a40004a4000 = true := by decide +kernel
  have replay58_21 : fastPacked 2347 (maskedCandidates 2347 5376 256)
      0x4a30004a40004a40004a4000 = true := by decide +kernel
  have replay58_22 : fastPacked 2347 (maskedCandidates 2347 5632 54)
      0 = true := by decide +kernel
  have hs : p*p ≤ 2347^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 5686 := by
    have hc : (2347^3 : ℕ).sqrt = 113702 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 23 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay58_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay58_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked61 {p : ℕ} (hp : p.Prime) (hlo : 2*2467 < p)
    (hhi : p^2 < 2467^3) (hmod : p%3 ≠ 2467%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 2467 = true) :
    ∃ d, signCertificate p 2467 d = true := by
  have replay61_0 : fastPacked 2467 (maskedCandidates 2467 0 256)
      0 = true := by decide +kernel
  have replay61_1 : fastPacked 2467 (maskedCandidates 2467 256 256)
      0x3e2 = true := by decide +kernel
  have replay61_2 : fastPacked 2467 (maskedCandidates 2467 512 256)
      0x55902856302e568031584041 = true := by decide +kernel
  have replay61_3 : fastPacked 2467 (maskedCandidates 2467 768 256)
      0x53901954401e = true := by decide +kernel
  have replay61_4 : fastPacked 2467 (maskedCandidates 2467 1024 256)
      0x51f00f51f00f52201052601152801252c014 = true := by decide +kernel
  have replay61_5 : fastPacked 2467 (maskedCandidates 2467 1280 256)
      0 = true := by decide +kernel
  have replay61_6 : fastPacked 2467 (maskedCandidates 2467 1536 256)
      0 = true := by decide +kernel
  have replay61_7 : fastPacked 2467 (maskedCandidates 2467 1792 256)
      0x4fc0044fd0054fe005 = true := by decide +kernel
  have replay61_8 : fastPacked 2467 (maskedCandidates 2467 2048 256)
      0x4f70034f80044fb004 = true := by decide +kernel
  have replay61_9 : fastPacked 2467 (maskedCandidates 2467 2304 256)
      0x4f40034f50034f6003 = true := by decide +kernel
  have replay61_10 : fastPacked 2467 (maskedCandidates 2467 2560 256)
      0x4f00024f10024f10024f2002 = true := by decide +kernel
  have replay61_11 : fastPacked 2467 (maskedCandidates 2467 2816 256)
      0x4ed0024ee002 = true := by decide +kernel
  have replay61_12 : fastPacked 2467 (maskedCandidates 2467 3072 256)
      0x4eb0014ec0014ec0014ec002 = true := by decide +kernel
  have replay61_13 : fastPacked 2467 (maskedCandidates 2467 3328 256)
      0x4e90014ea001 = true := by decide +kernel
  have replay61_14 : fastPacked 2467 (maskedCandidates 2467 3584 256)
      0x4e70014e80014e8001 = true := by decide +kernel
  have replay61_15 : fastPacked 2467 (maskedCandidates 2467 3840 256)
      0x4e60014e70014e70014e7001 = true := by decide +kernel
  have replay61_16 : fastPacked 2467 (maskedCandidates 2467 4096 256)
      0x4e50014e50014e60014e6001 = true := by decide +kernel
  have replay61_17 : fastPacked 2467 (maskedCandidates 2467 4352 256)
      0x4e40004e40004e5000 = true := by decide +kernel
  have replay61_18 : fastPacked 2467 (maskedCandidates 2467 4608 256)
      0x4e3000 = true := by decide +kernel
  have replay61_19 : fastPacked 2467 (maskedCandidates 2467 4864 256)
      0x4e20004e2000 = true := by decide +kernel
  have replay61_20 : fastPacked 2467 (maskedCandidates 2467 5120 256)
      0x4e10004e10004e2000 = true := by decide +kernel
  have replay61_21 : fastPacked 2467 (maskedCandidates 2467 5376 256)
      0x4e10004e1000 = true := by decide +kernel
  have replay61_22 : fastPacked 2467 (maskedCandidates 2467 5632 256)
      0x4e00004e0000 = true := by decide +kernel
  have replay61_23 : fastPacked 2467 (maskedCandidates 2467 5888 239)
      0x4df0004df0004df0004e0000 = true := by decide +kernel
  have hs : p*p ≤ 2467^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 6127 := by
    have hc : (2467^3 : ℕ).sqrt = 122533 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 24 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay61_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay61_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked67 {p : ℕ} (hp : p.Prime) (hlo : 2*2707 < p)
    (hhi : p^2 < 2707^3) (hmod : p%3 ≠ 2707%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 2707 = true) :
    ∃ d, signCertificate p 2707 d = true := by
  have replay67_0 : fastPacked 2707 (maskedCandidates 2707 0 256)
      0 = true := by decide +kernel
  have replay67_1 : fastPacked 2707 (maskedCandidates 2707 256 256)
      0x68709b6f20ef72d1218141f188225900033a = true := by decide +kernel
  have replay67_2 : fastPacked 2707 (maskedCandidates 2707 512 256)
      0x606043626057 = true := by decide +kernel
  have replay67_3 : fastPacked 2707 (maskedCandidates 2707 768 256)
      0x5e70315ec0345ec034 = true := by decide +kernel
  have replay67_4 : fastPacked 2707 (maskedCandidates 2707 1024 256)
      0x5a10115a40125b701a5b901b = true := by decide +kernel
  have replay67_5 : fastPacked 2707 (maskedCandidates 2707 1280 256)
      0x59000b59400d59d010 = true := by decide +kernel
  have replay67_6 : fastPacked 2707 (maskedCandidates 2707 1536 256)
      0x58600858c00a = true := by decide +kernel
  have replay67_7 : fastPacked 2707 (maskedCandidates 2707 1792 256)
      0x57e00657f007580007580007 = true := by decide +kernel
  have replay67_8 : fastPacked 2707 (maskedCandidates 2707 2048 256)
      0x57b00657b006 = true := by decide +kernel
  have replay67_9 : fastPacked 2707 (maskedCandidates 2707 2304 256)
      0x575004 = true := by decide +kernel
  have replay67_10 : fastPacked 2707 (maskedCandidates 2707 2560 256)
      0x570003571003571003 = true := by decide +kernel
  have replay67_11 : fastPacked 2707 (maskedCandidates 2707 2816 256)
      0x56c00356d00356e003 = true := by decide +kernel
  have replay67_12 : fastPacked 2707 (maskedCandidates 2707 3072 256)
      0x56800256900256a00256a002 = true := by decide +kernel
  have replay67_13 : fastPacked 2707 (maskedCandidates 2707 3328 256)
      0x566002566002 = true := by decide +kernel
  have replay67_14 : fastPacked 2707 (maskedCandidates 2707 3584 256)
      0x564001564001564001 = true := by decide +kernel
  have replay67_15 : fastPacked 2707 (maskedCandidates 2707 3840 256)
      0x562001563001563001563001563001564001 = true := by decide +kernel
  have replay67_16 : fastPacked 2707 (maskedCandidates 2707 4096 256)
      0 = true := by decide +kernel
  have replay67_17 : fastPacked 2707 (maskedCandidates 2707 4352 256)
      0x560001560001 = true := by decide +kernel
  have replay67_18 : fastPacked 2707 (maskedCandidates 2707 4608 256)
      0x55f00155f00155f00155f001 = true := by decide +kernel
  have replay67_19 : fastPacked 2707 (maskedCandidates 2707 4864 256)
      0x55d00055d00155e00155e00155e001 = true := by decide +kernel
  have replay67_20 : fastPacked 2707 (maskedCandidates 2707 5120 256)
      0x55c00055d00055d00055d00055d000 = true := by decide +kernel
  have replay67_21 : fastPacked 2707 (maskedCandidates 2707 5376 256)
      0x55c00055c00055c000 = true := by decide +kernel
  have replay67_22 : fastPacked 2707 (maskedCandidates 2707 5632 256)
      0x55b00055b000 = true := by decide +kernel
  have replay67_23 : fastPacked 2707 (maskedCandidates 2707 5888 256)
      0x55a00055a00055a00055a000 = true := by decide +kernel
  have replay67_24 : fastPacked 2707 (maskedCandidates 2707 6144 256)
      0x55a000 = true := by decide +kernel
  have replay67_25 : fastPacked 2707 (maskedCandidates 2707 6400 256)
      0x559000559000559000559000559000 = true := by decide +kernel
  have replay67_26 : fastPacked 2707 (maskedCandidates 2707 6656 256)
      0x558000558000 = true := by decide +kernel
  have replay67_27 : fastPacked 2707 (maskedCandidates 2707 6912 131)
      0x558000 = true := by decide +kernel
  have hs : p*p ≤ 2707^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 7043 := by
    have hc : (2707^3 : ℕ).sqrt = 140842 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 28 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay67_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay67_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked76 {p : ℕ} (hp : p.Prime) (hlo : 2*3067 < p)
    (hhi : p^2 < 3067^3) (hmod : p%3 ≠ 3067%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3067 = true) :
    ∃ d, signCertificate p 3067 d = true := by
  have replay76_0 : fastPacked 3067 (maskedCandidates 3067 0 256)
      0 = true := by decide +kernel
  have replay76_1 : fastPacked 3067 (maskedCandidates 3067 256 256)
      0x9d22d50003eb0003cc = true := by decide +kernel
  have replay76_2 : fastPacked 3067 (maskedCandidates 3067 512 256)
      0 = true := by decide +kernel
  have replay76_3 : fastPacked 3067 (maskedCandidates 3067 768 256)
      0x6bd03f6cd048 = true := by decide +kernel
  have replay76_4 : fastPacked 3067 (maskedCandidates 3067 1024 256)
      0x67a01e = true := by decide +kernel
  have replay76_5 : fastPacked 3067 (maskedCandidates 3067 1280 256)
      0x66601666b018 = true := by decide +kernel
  have replay76_6 : fastPacked 3067 (maskedCandidates 3067 1536 256)
      0x65000e657010 = true := by decide +kernel
  have replay76_7 : fastPacked 3067 (maskedCandidates 3067 1792 256)
      0x64800b = true := by decide +kernel
  have replay76_8 : fastPacked 3067 (maskedCandidates 3067 2048 256)
      0x63b008 = true := by decide +kernel
  have replay76_9 : fastPacked 3067 (maskedCandidates 3067 2304 256)
      0x635006 = true := by decide +kernel
  have replay76_10 : fastPacked 3067 (maskedCandidates 3067 2560 256)
      0x62d005630005631005 = true := by decide +kernel
  have replay76_11 : fastPacked 3067 (maskedCandidates 3067 2816 256)
      0x628004 = true := by decide +kernel
  have replay76_12 : fastPacked 3067 (maskedCandidates 3067 3072 256)
      0 = true := by decide +kernel
  have replay76_13 : fastPacked 3067 (maskedCandidates 3067 3328 256)
      0x622003 = true := by decide +kernel
  have replay76_14 : fastPacked 3067 (maskedCandidates 3067 3584 256)
      0x620002621002621002 = true := by decide +kernel
  have replay76_15 : fastPacked 3067 (maskedCandidates 3067 3840 256)
      0x61d00261f002 = true := by decide +kernel
  have replay76_16 : fastPacked 3067 (maskedCandidates 3067 4096 256)
      0 = true := by decide +kernel
  have replay76_17 : fastPacked 3067 (maskedCandidates 3067 4352 256)
      0x61a00161a00161b001 = true := by decide +kernel
  have replay76_18 : fastPacked 3067 (maskedCandidates 3067 4608 256)
      0x618001619001619001 = true := by decide +kernel
  have replay76_19 : fastPacked 3067 (maskedCandidates 3067 4864 256)
      0x617001617001 = true := by decide +kernel
  have replay76_20 : fastPacked 3067 (maskedCandidates 3067 5120 256)
      0x616001616001 = true := by decide +kernel
  have replay76_21 : fastPacked 3067 (maskedCandidates 3067 5376 256)
      0x614001614001615001 = true := by decide +kernel
  have replay76_22 : fastPacked 3067 (maskedCandidates 3067 5632 256)
      0x614001 = true := by decide +kernel
  have replay76_23 : fastPacked 3067 (maskedCandidates 3067 5888 256)
      0x613001 = true := by decide +kernel
  have replay76_24 : fastPacked 3067 (maskedCandidates 3067 6144 256)
      0x612000 = true := by decide +kernel
  have replay76_25 : fastPacked 3067 (maskedCandidates 3067 6400 256)
      0x611000611000 = true := by decide +kernel
  have replay76_26 : fastPacked 3067 (maskedCandidates 3067 6656 256)
      0x610000 = true := by decide +kernel
  have replay76_27 : fastPacked 3067 (maskedCandidates 3067 6912 256)
      0x610000610000 = true := by decide +kernel
  have replay76_28 : fastPacked 3067 (maskedCandidates 3067 7168 256)
      0x60f000 = true := by decide +kernel
  have replay76_29 : fastPacked 3067 (maskedCandidates 3067 7424 256)
      0x60e00060e00060f000 = true := by decide +kernel
  have replay76_30 : fastPacked 3067 (maskedCandidates 3067 7680 256)
      0x60e000 = true := by decide +kernel
  have replay76_31 : fastPacked 3067 (maskedCandidates 3067 7936 256)
      0x60d000 = true := by decide +kernel
  have replay76_32 : fastPacked 3067 (maskedCandidates 3067 8192 256)
      0x60d000 = true := by decide +kernel
  have replay76_33 : fastPacked 3067 (maskedCandidates 3067 8448 45)
      0 = true := by decide +kernel
  have hs : p*p ≤ 3067^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 8493 := by
    have hc : (3067^3 : ℕ).sqrt = 169851 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 34 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay76_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay76_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked79 {p : ℕ} (hp : p.Prime) (hlo : 2*3187 < p)
    (hhi : p^2 < 3187^3) (hmod : p%3 ≠ 3187%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3187 = true) :
    ∃ d, signCertificate p 3187 d = true := by
  have replay79_0 : fastPacked 3187 (maskedCandidates 3187 0 256)
      0 = true := by decide +kernel
  have replay79_1 : fastPacked 3187 (maskedCandidates 3187 256 256)
      0x84c13485e1438731558e11b5 = true := by decide +kernel
  have replay79_2 : fastPacked 3187 (maskedCandidates 3187 512 256)
      0x75207477308b = true := by decide +kernel
  have replay79_3 : fastPacked 3187 (maskedCandidates 3187 768 256)
      0x6df0306e00306e9035 = true := by decide +kernel
  have replay79_4 : fastPacked 3187 (maskedCandidates 3187 1024 256)
      0x6b701d6c10226c20226d00296d602b6dc02f = true := by decide +kernel
  have replay79_5 : fastPacked 3187 (maskedCandidates 3187 1280 256)
      0x6a20156a30156ab018 = true := by decide +kernel
  have replay79_6 : fastPacked 3187 (maskedCandidates 3187 1536 256)
      0x68e00e69401069801169c013 = true := by decide +kernel
  have replay79_7 : fastPacked 3187 (maskedCandidates 3187 1792 256)
      0x68200a68300b68500b68700c68800c68800c = true := by decide +kernel
  have replay79_8 : fastPacked 3187 (maskedCandidates 3187 2048 256)
      0x67800867a00867b00867c00967d00967f009 = true := by decide +kernel
  have replay79_9 : fastPacked 3187 (maskedCandidates 3187 2304 256)
      0x672006673007673007676007 = true := by decide +kernel
  have replay79_10 : fastPacked 3187 (maskedCandidates 3187 2560 256)
      0x66e005670006671006 = true := by decide +kernel
  have replay79_11 : fastPacked 3187 (maskedCandidates 3187 2816 256)
      0x66700466700466c005 = true := by decide +kernel
  have replay79_12 : fastPacked 3187 (maskedCandidates 3187 3072 256)
      0x664003665004665004666004666004666004667004667004 = true := by decide +kernel
  have replay79_13 : fastPacked 3187 (maskedCandidates 3187 3328 256)
      0x661003662003662003663003 = true := by decide +kernel
  have replay79_14 : fastPacked 3187 (maskedCandidates 3187 3584 256)
      0x65e00265f00365f003660003660003 = true := by decide +kernel
  have replay79_15 : fastPacked 3187 (maskedCandidates 3187 3840 256)
      0x65c00265c002 = true := by decide +kernel
  have replay79_16 : fastPacked 3187 (maskedCandidates 3187 4096 256)
      0x65a00265b002 = true := by decide +kernel
  have replay79_17 : fastPacked 3187 (maskedCandidates 3187 4352 256)
      0x658002658002659002659002659002659002 = true := by decide +kernel
  have replay79_18 : fastPacked 3187 (maskedCandidates 3187 4608 256)
      0x656001656001657001657001657001 = true := by decide +kernel
  have replay79_19 : fastPacked 3187 (maskedCandidates 3187 4864 256)
      0x655001656001 = true := by decide +kernel
  have replay79_20 : fastPacked 3187 (maskedCandidates 3187 5120 256)
      0x653001654001654001 = true := by decide +kernel
  have replay79_21 : fastPacked 3187 (maskedCandidates 3187 5376 256)
      0x653001 = true := by decide +kernel
  have replay79_22 : fastPacked 3187 (maskedCandidates 3187 5632 256)
      0x651001651001651001651001652001652001652001 = true := by decide +kernel
  have replay79_23 : fastPacked 3187 (maskedCandidates 3187 5888 256)
      0x650001650001650001651001 = true := by decide +kernel
  have replay79_24 : fastPacked 3187 (maskedCandidates 3187 6144 256)
      0x64f00164f001650001650001650001 = true := by decide +kernel
  have replay79_25 : fastPacked 3187 (maskedCandidates 3187 6400 256)
      0x64f00064f00064f00064f000 = true := by decide +kernel
  have replay79_26 : fastPacked 3187 (maskedCandidates 3187 6656 256)
      0x64e00064e00064e00064e00064e00064e000 = true := by decide +kernel
  have replay79_27 : fastPacked 3187 (maskedCandidates 3187 6912 256)
      0x64d00064d00064d00064d00064d000 = true := by decide +kernel
  have replay79_28 : fastPacked 3187 (maskedCandidates 3187 7168 256)
      0x64c00064d00064d000 = true := by decide +kernel
  have replay79_29 : fastPacked 3187 (maskedCandidates 3187 7424 256)
      0x64c00064c00064c000 = true := by decide +kernel
  have replay79_30 : fastPacked 3187 (maskedCandidates 3187 7680 256)
      0x64b00064b000 = true := by decide +kernel
  have replay79_31 : fastPacked 3187 (maskedCandidates 3187 7936 256)
      0x64b00064b00064b000 = true := by decide +kernel
  have replay79_32 : fastPacked 3187 (maskedCandidates 3187 8192 256)
      0x64a00064a00064a00064a00064a00064a00064a00064a000 = true := by decide +kernel
  have replay79_33 : fastPacked 3187 (maskedCandidates 3187 8448 256)
      0x64a00064a00064a000 = true := by decide +kernel
  have replay79_34 : fastPacked 3187 (maskedCandidates 3187 8704 256)
      0x649000649000649000649000 = true := by decide +kernel
  have replay79_35 : fastPacked 3187 (maskedCandidates 3187 8960 36)
      0x649000 = true := by decide +kernel
  have hs : p*p ≤ 3187^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 8996 := by
    have hc : (3187^3 : ℕ).sqrt = 179917 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 36 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay79_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_34 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay79_35 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked82 {p : ℕ} (hp : p.Prime) (hlo : 2*3307 < p)
    (hhi : p^2 < 3307^3) (hmod : p%3 ≠ 3307%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3307 = true) :
    ∃ d, signCertificate p 3307 d = true := by
  have replay82_0 : fastPacked 3307 (maskedCandidates 3307 0 256)
      0 = true := by decide +kernel
  have replay82_1 : fastPacked 3307 (maskedCandidates 3307 256 256)
      0x94c1d9a522cc000497 = true := by decide +kernel
  have replay82_2 : fastPacked 3307 (maskedCandidates 3307 512 256)
      0x79007379c07b7a107e7ab0857ae0877be0927c909a7e20ac82d0e587511f89d140 = true := by decide +kernel
  have replay82_3 : fastPacked 3307 (maskedCandidates 3307 768 256)
      0x72b03774204374e04a76f05d777063 = true := by decide +kernel
  have replay82_4 : fastPacked 3307 (maskedCandidates 3307 1024 256)
      0x727034 = true := by decide +kernel
  have replay82_5 : fastPacked 3307 (maskedCandidates 3307 1280 256)
      0x6e30166e60176ed01a6ee01b6f301c6f601e = true := by decide +kernel
  have replay82_6 : fastPacked 3307 (maskedCandidates 3307 1536 256)
      0x6d00106d70126d90126e1015 = true := by decide +kernel
  have replay82_7 : fastPacked 3307 (maskedCandidates 3307 1792 256)
      0x6c400c6c800d6cd00f = true := by decide +kernel
  have replay82_8 : fastPacked 3307 (maskedCandidates 3307 2048 256)
      0x6bc0096bd00a6bd00a = true := by decide +kernel
  have replay82_9 : fastPacked 3307 (maskedCandidates 3307 2304 256)
      0x6b40076b40086b40086b50086b60086b7008 = true := by decide +kernel
  have replay82_10 : fastPacked 3307 (maskedCandidates 3307 2560 256)
      0x6ae0066ae0066af0066b2007 = true := by decide +kernel
  have replay82_11 : fastPacked 3307 (maskedCandidates 3307 2816 256)
      0x6a80056a90056ab005 = true := by decide +kernel
  have replay82_12 : fastPacked 3307 (maskedCandidates 3307 3072 256)
      0x6a30046a40046a40046a50046a50046a5004 = true := by decide +kernel
  have replay82_13 : fastPacked 3307 (maskedCandidates 3307 3328 256)
      0x6a00036a10036a20046a2004 = true := by decide +kernel
  have replay82_14 : fastPacked 3307 (maskedCandidates 3307 3584 256)
      0x69d00369d00369d00369e00369e00369f00369f003 = true := by decide +kernel
  have replay82_15 : fastPacked 3307 (maskedCandidates 3307 3840 256)
      0x69b00269c00369c003 = true := by decide +kernel
  have replay82_16 : fastPacked 3307 (maskedCandidates 3307 4096 256)
      0x69800269900269a00269a002 = true := by decide +kernel
  have replay82_17 : fastPacked 3307 (maskedCandidates 3307 4352 256)
      0x696002696002696002697002 = true := by decide +kernel
  have replay82_18 : fastPacked 3307 (maskedCandidates 3307 4608 256)
      0x694001695002 = true := by decide +kernel
  have replay82_19 : fastPacked 3307 (maskedCandidates 3307 4864 256)
      0x693001694001694001 = true := by decide +kernel
  have replay82_20 : fastPacked 3307 (maskedCandidates 3307 5120 256)
      0x691001 = true := by decide +kernel
  have replay82_21 : fastPacked 3307 (maskedCandidates 3307 5376 256)
      0x690001690001691001691001691001691001 = true := by decide +kernel
  have replay82_22 : fastPacked 3307 (maskedCandidates 3307 5632 256)
      0x68f001690001690001690001 = true := by decide +kernel
  have replay82_23 : fastPacked 3307 (maskedCandidates 3307 5888 256)
      0x68e00168e00168f001 = true := by decide +kernel
  have replay82_24 : fastPacked 3307 (maskedCandidates 3307 6144 256)
      0x68d00168d00168d00168d00168d00168e001 = true := by decide +kernel
  have replay82_25 : fastPacked 3307 (maskedCandidates 3307 6400 256)
      0x68c00168c00168c001 = true := by decide +kernel
  have replay82_26 : fastPacked 3307 (maskedCandidates 3307 6656 256)
      0x68b00068b00168b00168c00168c00168c001 = true := by decide +kernel
  have replay82_27 : fastPacked 3307 (maskedCandidates 3307 6912 256)
      0x68a00068a00068b00068b000 = true := by decide +kernel
  have replay82_28 : fastPacked 3307 (maskedCandidates 3307 7168 256)
      0x68a00068a00068a00068a00068a000 = true := by decide +kernel
  have replay82_29 : fastPacked 3307 (maskedCandidates 3307 7424 256)
      0x689000689000689000689000689000 = true := by decide +kernel
  have replay82_30 : fastPacked 3307 (maskedCandidates 3307 7680 256)
      0x688000689000689000689000 = true := by decide +kernel
  have replay82_31 : fastPacked 3307 (maskedCandidates 3307 7936 256)
      0x688000688000 = true := by decide +kernel
  have replay82_32 : fastPacked 3307 (maskedCandidates 3307 8192 256)
      0x687000687000687000688000688000 = true := by decide +kernel
  have replay82_33 : fastPacked 3307 (maskedCandidates 3307 8448 256)
      0x687000687000687000687000687000 = true := by decide +kernel
  have replay82_34 : fastPacked 3307 (maskedCandidates 3307 8704 256)
      0x686000686000687000687000 = true := by decide +kernel
  have replay82_35 : fastPacked 3307 (maskedCandidates 3307 8960 256)
      0x686000686000686000686000 = true := by decide +kernel
  have replay82_36 : fastPacked 3307 (maskedCandidates 3307 9216 256)
      0x685000685000685000686000686000686000686000 = true := by decide +kernel
  have replay82_37 : fastPacked 3307 (maskedCandidates 3307 9472 37)
      0x685000685000 = true := by decide +kernel
  have hs : p*p ≤ 3307^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 9509 := by
    have hc : (3307^3 : ℕ).sqrt = 190174 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 38 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay82_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_34 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_35 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_36 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay82_37 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked83 {p : ℕ} (hp : p.Prime) (hlo : 2*3347 < p)
    (hhi : p^2 < 3347^3) (hmod : p%3 ≠ 3347%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3347 = true) :
    ∃ d, signCertificate p 3347 d = true := by
  have replay83_0 : fastPacked 3347 (maskedCandidates 3347 0 256)
      0 = true := by decide +kernel
  have replay83_1 : fastPacked 3347 (maskedCandidates 3347 256 256)
      0x4fc0003ba = true := by decide +kernel
  have replay83_2 : fastPacked 3347 (maskedCandidates 3347 512 256)
      0x8080b88280d08490ea = true := by decide +kernel
  have replay83_3 : fastPacked 3347 (maskedCandidates 3347 768 256)
      0x76504b = true := by decide +kernel
  have replay83_4 : fastPacked 3347 (maskedCandidates 3347 1024 256)
      0x719024720027721028725029725029738033 = true := by decide +kernel
  have replay83_5 : fastPacked 3347 (maskedCandidates 3347 1280 256)
      0x6fa01770801d = true := by decide +kernel
  have replay83_6 : fastPacked 3347 (maskedCandidates 3347 1536 256)
      0x6ec0126ef0136f00136f1014 = true := by decide +kernel
  have replay83_7 : fastPacked 3347 (maskedCandidates 3347 1792 256)
      0x6dc00d6e000e6e100e6e50106e5010 = true := by decide +kernel
  have replay83_8 : fastPacked 3347 (maskedCandidates 3347 2048 256)
      0x6cf0096d00096d100a = true := by decide +kernel
  have replay83_9 : fastPacked 3347 (maskedCandidates 3347 2304 256)
      0x6c80076c80076cd0096cd0096cd009 = true := by decide +kernel
  have replay83_10 : fastPacked 3347 (maskedCandidates 3347 2560 256)
      0x6c30066c5007 = true := by decide +kernel
  have replay83_11 : fastPacked 3347 (maskedCandidates 3347 2816 256)
      0x6be0056be0056be0056c00066c1006 = true := by decide +kernel
  have replay83_12 : fastPacked 3347 (maskedCandidates 3347 3072 256)
      0x6b80046b90046ba0046ba0046bb005 = true := by decide +kernel
  have replay83_13 : fastPacked 3347 (maskedCandidates 3347 3328 256)
      0x6b50036b7004 = true := by decide +kernel
  have replay83_14 : fastPacked 3347 (maskedCandidates 3347 3584 256)
      0x6b20036b30036b30036b4003 = true := by decide +kernel
  have replay83_15 : fastPacked 3347 (maskedCandidates 3347 3840 256)
      0 = true := by decide +kernel
  have replay83_16 : fastPacked 3347 (maskedCandidates 3347 4096 256)
      0x6ad0026ad0026ae0026ae002 = true := by decide +kernel
  have replay83_17 : fastPacked 3347 (maskedCandidates 3347 4352 256)
      0x6ac0026ac002 = true := by decide +kernel
  have replay83_18 : fastPacked 3347 (maskedCandidates 3347 4608 256)
      0x6a90026a90026aa0026aa0026ab0026ab002 = true := by decide +kernel
  have replay83_19 : fastPacked 3347 (maskedCandidates 3347 4864 256)
      0x6a8001 = true := by decide +kernel
  have replay83_20 : fastPacked 3347 (maskedCandidates 3347 5120 256)
      0x6a60016a70016a7001 = true := by decide +kernel
  have replay83_21 : fastPacked 3347 (maskedCandidates 3347 5376 256)
      0x6a50016a50016a5001 = true := by decide +kernel
  have replay83_22 : fastPacked 3347 (maskedCandidates 3347 5632 256)
      0x6a40016a40016a40016a40016a40016a40016a4001 = true := by decide +kernel
  have replay83_23 : fastPacked 3347 (maskedCandidates 3347 5888 256)
      0x6a20016a30016a30016a3001 = true := by decide +kernel
  have replay83_24 : fastPacked 3347 (maskedCandidates 3347 6144 256)
      0x6a10016a10016a20016a20016a20016a20016a20016a2001 = true := by decide +kernel
  have replay83_25 : fastPacked 3347 (maskedCandidates 3347 6400 256)
      0x6a10016a10016a10016a1001 = true := by decide +kernel
  have replay83_26 : fastPacked 3347 (maskedCandidates 3347 6656 256)
      0x6a00016a00016a00016a00016a00016a0001 = true := by decide +kernel
  have replay83_27 : fastPacked 3347 (maskedCandidates 3347 6912 256)
      0x69f00069f00069f0006a0001 = true := by decide +kernel
  have replay83_28 : fastPacked 3347 (maskedCandidates 3347 7168 256)
      0x69e00069e00069f000 = true := by decide +kernel
  have replay83_29 : fastPacked 3347 (maskedCandidates 3347 7424 256)
      0x69d00069d00069e00069e000 = true := by decide +kernel
  have replay83_30 : fastPacked 3347 (maskedCandidates 3347 7680 256)
      0x69d00069d00069d000 = true := by decide +kernel
  have replay83_31 : fastPacked 3347 (maskedCandidates 3347 7936 256)
      0x69c00069d00069d000 = true := by decide +kernel
  have replay83_32 : fastPacked 3347 (maskedCandidates 3347 8192 256)
      0x69c00069c00069c00069c000 = true := by decide +kernel
  have replay83_33 : fastPacked 3347 (maskedCandidates 3347 8448 256)
      0x69b00069b00069c000 = true := by decide +kernel
  have replay83_34 : fastPacked 3347 (maskedCandidates 3347 8704 256)
      0x69b00069b00069b00069b00069b000 = true := by decide +kernel
  have replay83_35 : fastPacked 3347 (maskedCandidates 3347 8960 256)
      0x69a00069a00069a00069a000 = true := by decide +kernel
  have replay83_36 : fastPacked 3347 (maskedCandidates 3347 9216 256)
      0x69a00069a00069a00069a00069a00069a000 = true := by decide +kernel
  have replay83_37 : fastPacked 3347 (maskedCandidates 3347 9472 210)
      0x69900069900069a00069a000 = true := by decide +kernel
  have hs : p*p ≤ 3347^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 9682 := by
    have hc : (3347^3 : ℕ).sqrt = 193634 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 38 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay83_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_34 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_35 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_36 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay83_37 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked86 {p : ℕ} (hp : p.Prime) (hlo : 2*3467 < p)
    (hhi : p^2 < 3467^3) (hmod : p%3 ≠ 3467%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3467 = true) :
    ∃ d, signCertificate p 3467 d = true := by
  have replay86_0 : fastPacked 3467 (maskedCandidates 3467 0 256)
      0 = true := by decide +kernel
  have replay86_1 : fastPacked 3467 (maskedCandidates 3467 256 256)
      0x9ad1e0 = true := by decide +kernel
  have replay86_2 : fastPacked 3467 (maskedCandidates 3467 512 256)
      0x7f507d = true := by decide +kernel
  have replay86_3 : fastPacked 3467 (maskedCandidates 3467 768 256)
      0x79d0477b9057 = true := by decide +kernel
  have replay86_4 : fastPacked 3467 (maskedCandidates 3467 1024 256)
      0 = true := by decide +kernel
  have replay86_5 : fastPacked 3467 (maskedCandidates 3467 1280 256)
      0 = true := by decide +kernel
  have replay86_6 : fastPacked 3467 (maskedCandidates 3467 1536 256)
      0x72b013 = true := by decide +kernel
  have replay86_7 : fastPacked 3467 (maskedCandidates 3467 1792 256)
      0x727011 = true := by decide +kernel
  have replay86_8 : fastPacked 3467 (maskedCandidates 3467 2048 256)
      0x71200b71400b71600c = true := by decide +kernel
  have replay86_9 : fastPacked 3467 (maskedCandidates 3467 2304 256)
      0x70b009 = true := by decide +kernel
  have replay86_10 : fastPacked 3467 (maskedCandidates 3467 2560 256)
      0x704007706008 = true := by decide +kernel
  have replay86_11 : fastPacked 3467 (maskedCandidates 3467 2816 256)
      0x6fc0056fc005701006 = true := by decide +kernel
  have replay86_12 : fastPacked 3467 (maskedCandidates 3467 3072 256)
      0x6f80046fb005 = true := by decide +kernel
  have replay86_13 : fastPacked 3467 (maskedCandidates 3467 3328 256)
      0x6f50046f60046f6004 = true := by decide +kernel
  have replay86_14 : fastPacked 3467 (maskedCandidates 3467 3584 256)
      0x6f2003 = true := by decide +kernel
  have replay86_15 : fastPacked 3467 (maskedCandidates 3467 3840 256)
      0x6ef003 = true := by decide +kernel
  have replay86_16 : fastPacked 3467 (maskedCandidates 3467 4096 256)
      0 = true := by decide +kernel
  have replay86_17 : fastPacked 3467 (maskedCandidates 3467 4352 256)
      0x6e90026eb0026eb002 = true := by decide +kernel
  have replay86_18 : fastPacked 3467 (maskedCandidates 3467 4608 256)
      0x6e9002 = true := by decide +kernel
  have replay86_19 : fastPacked 3467 (maskedCandidates 3467 4864 256)
      0x6e70026e7002 = true := by decide +kernel
  have replay86_20 : fastPacked 3467 (maskedCandidates 3467 5120 256)
      0x6e40016e5001 = true := by decide +kernel
  have replay86_21 : fastPacked 3467 (maskedCandidates 3467 5376 256)
      0 = true := by decide +kernel
  have replay86_22 : fastPacked 3467 (maskedCandidates 3467 5632 256)
      0x6e10016e20016e2001 = true := by decide +kernel
  have replay86_23 : fastPacked 3467 (maskedCandidates 3467 5888 256)
      0 = true := by decide +kernel
  have replay86_24 : fastPacked 3467 (maskedCandidates 3467 6144 256)
      0x6df0016e00016e0001 = true := by decide +kernel
  have replay86_25 : fastPacked 3467 (maskedCandidates 3467 6400 256)
      0x6df0016df001 = true := by decide +kernel
  have replay86_26 : fastPacked 3467 (maskedCandidates 3467 6656 256)
      0x6de001 = true := by decide +kernel
  have replay86_27 : fastPacked 3467 (maskedCandidates 3467 6912 256)
      0x6dd0016dd001 = true := by decide +kernel
  have replay86_28 : fastPacked 3467 (maskedCandidates 3467 7168 256)
      0x6dc0006dc001 = true := by decide +kernel
  have replay86_29 : fastPacked 3467 (maskedCandidates 3467 7424 256)
      0x6db0006db0006db0006db000 = true := by decide +kernel
  have replay86_30 : fastPacked 3467 (maskedCandidates 3467 7680 256)
      0 = true := by decide +kernel
  have replay86_31 : fastPacked 3467 (maskedCandidates 3467 7936 256)
      0x6da0006da0006da000 = true := by decide +kernel
  have replay86_32 : fastPacked 3467 (maskedCandidates 3467 8192 256)
      0x6d9000 = true := by decide +kernel
  have replay86_33 : fastPacked 3467 (maskedCandidates 3467 8448 256)
      0 = true := by decide +kernel
  have replay86_34 : fastPacked 3467 (maskedCandidates 3467 8704 256)
      0x6d8000 = true := by decide +kernel
  have replay86_35 : fastPacked 3467 (maskedCandidates 3467 8960 256)
      0x6d70006d70006d80006d80006d8000 = true := by decide +kernel
  have replay86_36 : fastPacked 3467 (maskedCandidates 3467 9216 256)
      0x6d7000 = true := by decide +kernel
  have replay86_37 : fastPacked 3467 (maskedCandidates 3467 9472 256)
      0x6d60006d7000 = true := by decide +kernel
  have replay86_38 : fastPacked 3467 (maskedCandidates 3467 9728 256)
      0x6d6000 = true := by decide +kernel
  have replay86_39 : fastPacked 3467 (maskedCandidates 3467 9984 224)
      0x6d6000 = true := by decide +kernel
  have hs : p*p ≤ 3467^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 10208 := by
    have hc : (3467^3 : ℕ).sqrt = 204141 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 40 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay86_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_34 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_35 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_36 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_37 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_38 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay86_39 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked88 {p : ℕ} (hp : p.Prime) (hlo : 2*3547 < p)
    (hhi : p^2 < 3547^3) (hmod : p%3 ≠ 3547%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3547 = true) :
    ∃ d, signCertificate p 3547 d = true := by
  have replay88_0 : fastPacked 3547 (maskedCandidates 3547 0 256)
      0 = true := by decide +kernel
  have replay88_1 : fastPacked 3547 (maskedCandidates 3547 256 256)
      0 = true := by decide +kernel
  have replay88_2 : fastPacked 3547 (maskedCandidates 3547 512 256)
      0x8420958530a090d13092013f = true := by decide +kernel
  have replay88_3 : fastPacked 3547 (maskedCandidates 3547 768 256)
      0x7df055 = true := by decide +kernel
  have replay88_4 : fastPacked 3547 (maskedCandidates 3547 1024 256)
      0x79a030 = true := by decide +kernel
  have replay88_5 : fastPacked 3547 (maskedCandidates 3547 1280 256)
      0x76e01c77201e77501f77a021 = true := by decide +kernel
  have replay88_6 : fastPacked 3547 (maskedCandidates 3547 1536 256)
      0x75801475c01575d016762017765019 = true := by decide +kernel
  have replay88_7 : fastPacked 3547 (maskedCandidates 3547 1792 256)
      0x74700e74e010 = true := by decide +kernel
  have replay88_8 : fastPacked 3547 (maskedCandidates 3547 2048 256)
      0x74000c74100c74400d = true := by decide +kernel
  have replay88_9 : fastPacked 3547 (maskedCandidates 3547 2304 256)
      0x73300973300973600973900a = true := by decide +kernel
  have replay88_10 : fastPacked 3547 (maskedCandidates 3547 2560 256)
      0x72e007731008733009 = true := by decide +kernel
  have replay88_11 : fastPacked 3547 (maskedCandidates 3547 2816 256)
      0x72800672900672a00772b007 = true := by decide +kernel
  have replay88_12 : fastPacked 3547 (maskedCandidates 3547 3072 256)
      0x722005 = true := by decide +kernel
  have replay88_13 : fastPacked 3547 (maskedCandidates 3547 3328 256)
      0x720004722005722005 = true := by decide +kernel
  have replay88_14 : fastPacked 3547 (maskedCandidates 3547 3584 256)
      0x71c00471d004 = true := by decide +kernel
  have replay88_15 : fastPacked 3547 (maskedCandidates 3547 3840 256)
      0x71800371800371900371900371a003 = true := by decide +kernel
  have replay88_16 : fastPacked 3547 (maskedCandidates 3547 4096 256)
      0x717003 = true := by decide +kernel
  have replay88_17 : fastPacked 3547 (maskedCandidates 3547 4352 256)
      0x713002713002 = true := by decide +kernel
  have replay88_18 : fastPacked 3547 (maskedCandidates 3547 4608 256)
      0x711002712002712002 = true := by decide +kernel
  have replay88_19 : fastPacked 3547 (maskedCandidates 3547 4864 256)
      0x70f002710002 = true := by decide +kernel
  have replay88_20 : fastPacked 3547 (maskedCandidates 3547 5120 256)
      0x70e00270f002 = true := by decide +kernel
  have replay88_21 : fastPacked 3547 (maskedCandidates 3547 5376 256)
      0x70c00170d00170d00170d00170d001 = true := by decide +kernel
  have replay88_22 : fastPacked 3547 (maskedCandidates 3547 5632 256)
      0x70b00170b00170b001 = true := by decide +kernel
  have replay88_23 : fastPacked 3547 (maskedCandidates 3547 5888 256)
      0x70900170a00170a001 = true := by decide +kernel
  have replay88_24 : fastPacked 3547 (maskedCandidates 3547 6144 256)
      0x708001709001709001709001 = true := by decide +kernel
  have replay88_25 : fastPacked 3547 (maskedCandidates 3547 6400 256)
      0x708001 = true := by decide +kernel
  have replay88_26 : fastPacked 3547 (maskedCandidates 3547 6656 256)
      0x706001707001707001707001 = true := by decide +kernel
  have replay88_27 : fastPacked 3547 (maskedCandidates 3547 6912 256)
      0x705001706001 = true := by decide +kernel
  have replay88_28 : fastPacked 3547 (maskedCandidates 3547 7168 256)
      0x705001705001705001705001 = true := by decide +kernel
  have replay88_29 : fastPacked 3547 (maskedCandidates 3547 7424 256)
      0x704000704000704000 = true := by decide +kernel
  have replay88_30 : fastPacked 3547 (maskedCandidates 3547 7680 256)
      0x703000703000703000704000 = true := by decide +kernel
  have replay88_31 : fastPacked 3547 (maskedCandidates 3547 7936 256)
      0x703000703000703000 = true := by decide +kernel
  have replay88_32 : fastPacked 3547 (maskedCandidates 3547 8192 256)
      0x702000702000702000 = true := by decide +kernel
  have replay88_33 : fastPacked 3547 (maskedCandidates 3547 8448 256)
      0x701000702000702000 = true := by decide +kernel
  have replay88_34 : fastPacked 3547 (maskedCandidates 3547 8704 256)
      0x701000701000701000 = true := by decide +kernel
  have replay88_35 : fastPacked 3547 (maskedCandidates 3547 8960 256)
      0x700000700000701000 = true := by decide +kernel
  have replay88_36 : fastPacked 3547 (maskedCandidates 3547 9216 256)
      0x700000700000700000700000 = true := by decide +kernel
  have replay88_37 : fastPacked 3547 (maskedCandidates 3547 9472 256)
      0x6ff0006ff0006ff0006ff000 = true := by decide +kernel
  have replay88_38 : fastPacked 3547 (maskedCandidates 3547 9728 256)
      0x6ff0006ff0006ff0006ff000 = true := by decide +kernel
  have replay88_39 : fastPacked 3547 (maskedCandidates 3547 9984 256)
      0x6fe0006ff0006ff000 = true := by decide +kernel
  have replay88_40 : fastPacked 3547 (maskedCandidates 3547 10240 256)
      0x6fe0006fe000 = true := by decide +kernel
  have replay88_41 : fastPacked 3547 (maskedCandidates 3547 10496 67)
      0x6fe0006fe000 = true := by decide +kernel
  have hs : p*p ≤ 3547^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 10563 := by
    have hc : (3547^3 : ℕ).sqrt = 211247 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 42 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay88_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_34 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_35 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_36 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_37 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_38 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_39 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_40 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay88_41 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked97 {p : ℕ} (hp : p.Prime) (hlo : 2*3907 < p)
    (hhi : p^2 < 3907^3) (hmod : p%3 ≠ 3907%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3907 = true) :
    ∃ d, signCertificate p 3907 d = true := by
  have replay97_0 : fastPacked 3907 (maskedCandidates 3907 0 256)
      0 = true := by decide +kernel
  have replay97_1 : fastPacked 3907 (maskedCandidates 3907 256 256)
      0xbf43140004560003ec0003ba000312 = true := by decide +kernel
  have replay97_2 : fastPacked 3907 (maskedCandidates 3907 512 256)
      0x9550cf95c0d496e0e29770e898e0fa9c31239c8127a14165a21171b6b294 = true := by decide +kernel
  have replay97_3 : fastPacked 3907 (maskedCandidates 3907 768 256)
      0x8b20618bd0688bf0698c706e8d30758dc07b8e30808f00888f208a8fd0918ff09390109490309591109f9190a491d0a792b0b0 = true := by decide +kernel
  have replay97_4 : fastPacked 3907 (maskedCandidates 3907 1024 256)
      0x86803887503f88004588904a89204f8960518980528a505a8a705b = true := by decide +kernel
  have replay97_5 : fastPacked 3907 (maskedCandidates 3907 1280 256)
      0x84102684502884702984802984802a84a02b84b02b84f02d85002d85202e85d03385d033864037 = true := by decide +kernel
  have replay97_6 : fastPacked 3907 (maskedCandidates 3907 1536 256)
      0x82301a82301a82601b82801c82901c82901d83002083202083302083602283602283702283702283b024 = true := by decide +kernel
  have replay97_7 : fastPacked 3907 (maskedCandidates 3907 1792 256)
      0x81001381101481101481201481301581601681701681a01781c01881c01881e01981f019 = true := by decide +kernel
  have replay97_8 : fastPacked 3907 (maskedCandidates 3907 2048 256)
      0x80200f80200f80401080501080901180901180a01180b01280c01280d01380e01380e013 = true := by decide +kernel
  have replay97_9 : fastPacked 3907 (maskedCandidates 3907 2304 256)
      0x7f700c7f700c7f800c7f900d7fa00d7fa00d7fa00d7fb00d7fb00d7fc00d7ff00e7ff00e80000f80100f = true := by decide +kernel
  have replay97_10 : fastPacked 3907 (maskedCandidates 3907 2560 256)
      0x7ef00a7ef00a7ef00a7f000a7f100a7f300b7f500c7f600c = true := by decide +kernel
  have replay97_11 : fastPacked 3907 (maskedCandidates 3907 2816 256)
      0x7e70087e80087e80087e80087e90087e90087ea0097ea0097ec0097ec0097ed0097ee0097ee00a = true := by decide +kernel
  have replay97_12 : fastPacked 3907 (maskedCandidates 3907 3072 256)
      0x7e20077e30077e30077e40077e40077e60087e70087e7008 = true := by decide +kernel
  have replay97_13 : fastPacked 3907 (maskedCandidates 3907 3328 256)
      0x7dd0067de0067de0067df0067df0067e00067e00067e00067e1007 = true := by decide +kernel
  have replay97_14 : fastPacked 3907 (maskedCandidates 3907 3584 256)
      0x7d90057d90057d90057d90057da0057da0057da0057db0057db0057db0057db0057dc006 = true := by decide +kernel
  have replay97_15 : fastPacked 3907 (maskedCandidates 3907 3840 256)
      0x7d50047d60047d60047d60047d60047d60047d70057d70057d80057d80057d8005 = true := by decide +kernel
  have replay97_16 : fastPacked 3907 (maskedCandidates 3907 4096 256)
      0x7d20047d20047d20047d20047d20047d20047d20047d30047d30047d30047d40047d40047d40047d40047d4004 = true := by decide +kernel
  have replay97_17 : fastPacked 3907 (maskedCandidates 3907 4352 256)
      0x7cf0037cf0037cf0037cf0037d00037d00037d10037d10047d10047d10047d1004 = true := by decide +kernel
  have replay97_18 : fastPacked 3907 (maskedCandidates 3907 4608 256)
      0x7cc0037cd0037cd0037cd0037cd0037ce0037ce0037ce0037ce0037cf003 = true := by decide +kernel
  have replay97_19 : fastPacked 3907 (maskedCandidates 3907 4864 256)
      0x7ca0027ca0027cb0037cb0037cb0037cb0037cc0037cc0037cc003 = true := by decide +kernel
  have replay97_20 : fastPacked 3907 (maskedCandidates 3907 5120 256)
      0x7c80027c80027c80027c90027c90027c90027c90027c90027ca0027ca0027ca002 = true := by decide +kernel
  have replay97_21 : fastPacked 3907 (maskedCandidates 3907 5376 256)
      0x7c60027c70027c70027c70027c70027c70027c70027c70027c80027c80027c8002 = true := by decide +kernel
  have replay97_22 : fastPacked 3907 (maskedCandidates 3907 5632 256)
      0x7c50027c50027c50027c50027c50027c60027c60027c60027c60027c60027c60027c60027c6002 = true := by decide +kernel
  have replay97_23 : fastPacked 3907 (maskedCandidates 3907 5888 256)
      0x7c30027c40027c40027c40027c40027c40027c40027c40027c40027c5002 = true := by decide +kernel
  have replay97_24 : fastPacked 3907 (maskedCandidates 3907 6144 256)
      0x7c20017c20017c20017c20017c20017c20017c20017c30017c30017c30027c30027c30027c3002 = true := by decide +kernel
  have replay97_25 : fastPacked 3907 (maskedCandidates 3907 6400 256)
      0x7c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c2001 = true := by decide +kernel
  have replay97_26 : fastPacked 3907 (maskedCandidates 3907 6656 256)
      0x7bf0017c00017c00017c00017c00017c00017c00017c00017c00017c00017c0001 = true := by decide +kernel
  have replay97_27 : fastPacked 3907 (maskedCandidates 3907 6912 256)
      0x7be0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf001 = true := by decide +kernel
  have replay97_28 : fastPacked 3907 (maskedCandidates 3907 7168 256)
      0x7bd0017bd0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be001 = true := by decide +kernel
  have replay97_29 : fastPacked 3907 (maskedCandidates 3907 7424 256)
      0x7bc0017bc0017bc0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd001 = true := by decide +kernel
  have replay97_30 : fastPacked 3907 (maskedCandidates 3907 7680 256)
      0x7bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc001 = true := by decide +kernel
  have replay97_31 : fastPacked 3907 (maskedCandidates 3907 7936 256)
      0x7bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb001 = true := by decide +kernel
  have replay97_32 : fastPacked 3907 (maskedCandidates 3907 8192 256)
      0x7ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017bb0017bb0017bb001 = true := by decide +kernel
  have replay97_33 : fastPacked 3907 (maskedCandidates 3907 8448 256)
      0x7b90017b90017b90017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba001 = true := by decide +kernel
  have replay97_34 : fastPacked 3907 (maskedCandidates 3907 8704 256)
      0x7b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90017b90017b9001 = true := by decide +kernel
  have replay97_35 : fastPacked 3907 (maskedCandidates 3907 8960 256)
      0x7b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b8000 = true := by decide +kernel
  have replay97_36 : fastPacked 3907 (maskedCandidates 3907 9216 256)
      0x7b70007b70007b80007b80007b80007b80007b80007b80007b8000 = true := by decide +kernel
  have replay97_37 : fastPacked 3907 (maskedCandidates 3907 9472 256)
      0x7b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b7000 = true := by decide +kernel
  have replay97_38 : fastPacked 3907 (maskedCandidates 3907 9728 256)
      0x7b60007b60007b60007b60007b60007b60007b70007b70007b70007b7000 = true := by decide +kernel
  have replay97_39 : fastPacked 3907 (maskedCandidates 3907 9984 256)
      0x7b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b6000 = true := by decide +kernel
  have replay97_40 : fastPacked 3907 (maskedCandidates 3907 10240 256)
      0x7b50007b50007b50007b50007b50007b50007b50007b50007b50007b60007b60007b60007b60007b60007b60007b6000 = true := by decide +kernel
  have replay97_41 : fastPacked 3907 (maskedCandidates 3907 10496 256)
      0x7b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b5000 = true := by decide +kernel
  have replay97_42 : fastPacked 3907 (maskedCandidates 3907 10752 256)
      0x7b40007b40007b40007b50007b50007b50007b50007b50007b50007b50007b50007b5000 = true := by decide +kernel
  have replay97_43 : fastPacked 3907 (maskedCandidates 3907 11008 256)
      0x7b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b4000 = true := by decide +kernel
  have replay97_44 : fastPacked 3907 (maskedCandidates 3907 11264 256)
      0x7b30007b40007b40007b40007b40007b40007b4000 = true := by decide +kernel
  have replay97_45 : fastPacked 3907 (maskedCandidates 3907 11520 256)
      0x7b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b3000 = true := by decide +kernel
  have replay97_46 : fastPacked 3907 (maskedCandidates 3907 11776 256)
      0x7b30007b30007b30007b30007b30007b30007b30007b3000 = true := by decide +kernel
  have replay97_47 : fastPacked 3907 (maskedCandidates 3907 12032 179)
      0x7b30007b30007b30007b30007b30007b3000 = true := by decide +kernel
  have hs : p*p ≤ 3907^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 12211 := by
    have hc : (3907^3 : ℕ).sqrt = 244210 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 48 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay97_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_34 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_35 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_36 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_37 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_38 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_39 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_40 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_41 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_42 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_43 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_44 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_45 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_46 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay97_47 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem checked98 {p : ℕ} (hp : p.Prime) (hlo : 2*3947 < p)
    (hhi : p^2 < 3947^3) (hmod : p%3 ≠ 3947%3) (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p 3947 = true) :
    ∃ d, signCertificate p 3947 d = true := by
  have replay98_0 : fastPacked 3947 (maskedCandidates 3947 0 256)
      0 = true := by decide +kernel
  have replay98_1 : fastPacked 3947 (maskedCandidates 3947 256 256)
      0 = true := by decide +kernel
  have replay98_2 : fastPacked 3947 (maskedCandidates 3947 512 256)
      0xb7728b = true := by decide +kernel
  have replay98_3 : fastPacked 3947 (maskedCandidates 3947 768 256)
      0x8c405f8d2068 = true := by decide +kernel
  have replay98_4 : fastPacked 3947 (maskedCandidates 3947 1024 256)
      0 = true := by decide +kernel
  have replay98_5 : fastPacked 3947 (maskedCandidates 3947 1280 256)
      0x85602786402d86602e = true := by decide +kernel
  have replay98_6 : fastPacked 3947 (maskedCandidates 3947 1536 256)
      0x84301f84e023 = true := by decide +kernel
  have replay98_7 : fastPacked 3947 (maskedCandidates 3947 1792 256)
      0x82c016 = true := by decide +kernel
  have replay98_8 : fastPacked 3947 (maskedCandidates 3947 2048 256)
      0x821012822013 = true := by decide +kernel
  have replay98_9 : fastPacked 3947 (maskedCandidates 3947 2304 256)
      0x81600f = true := by decide +kernel
  have replay98_10 : fastPacked 3947 (maskedCandidates 3947 2560 256)
      0x80400a80500a80b00c = true := by decide +kernel
  have replay98_11 : fastPacked 3947 (maskedCandidates 3947 2816 256)
      0 = true := by decide +kernel
  have replay98_12 : fastPacked 3947 (maskedCandidates 3947 3072 256)
      0 = true := by decide +kernel
  have replay98_13 : fastPacked 3947 (maskedCandidates 3947 3328 256)
      0x7f3006 = true := by decide +kernel
  have replay98_14 : fastPacked 3947 (maskedCandidates 3947 3584 256)
      0x7ef0057f1006 = true := by decide +kernel
  have replay98_15 : fastPacked 3947 (maskedCandidates 3947 3840 256)
      0 = true := by decide +kernel
  have replay98_16 : fastPacked 3947 (maskedCandidates 3947 4096 256)
      0x7e80047e9004 = true := by decide +kernel
  have replay98_17 : fastPacked 3947 (maskedCandidates 3947 4352 256)
      0 = true := by decide +kernel
  have replay98_18 : fastPacked 3947 (maskedCandidates 3947 4608 256)
      0x7e3003 = true := by decide +kernel
  have replay98_19 : fastPacked 3947 (maskedCandidates 3947 4864 256)
      0 = true := by decide +kernel
  have replay98_20 : fastPacked 3947 (maskedCandidates 3947 5120 256)
      0x7dd0027de0027de002 = true := by decide +kernel
  have replay98_21 : fastPacked 3947 (maskedCandidates 3947 5376 256)
      0x7db0027db0027dc0027dc0027dd0027dd002 = true := by decide +kernel
  have replay98_22 : fastPacked 3947 (maskedCandidates 3947 5632 256)
      0x7d9002 = true := by decide +kernel
  have replay98_23 : fastPacked 3947 (maskedCandidates 3947 5888 256)
      0x7d8002 = true := by decide +kernel
  have replay98_24 : fastPacked 3947 (maskedCandidates 3947 6144 256)
      0 = true := by decide +kernel
  have replay98_25 : fastPacked 3947 (maskedCandidates 3947 6400 256)
      0x7d60017d60017d6001 = true := by decide +kernel
  have replay98_26 : fastPacked 3947 (maskedCandidates 3947 6656 256)
      0x7d5001 = true := by decide +kernel
  have replay98_27 : fastPacked 3947 (maskedCandidates 3947 6912 256)
      0x7d30017d4001 = true := by decide +kernel
  have replay98_28 : fastPacked 3947 (maskedCandidates 3947 7168 256)
      0x7d20017d3001 = true := by decide +kernel
  have replay98_29 : fastPacked 3947 (maskedCandidates 3947 7424 256)
      0x7d10017d1001 = true := by decide +kernel
  have replay98_30 : fastPacked 3947 (maskedCandidates 3947 7680 256)
      0 = true := by decide +kernel
  have replay98_31 : fastPacked 3947 (maskedCandidates 3947 7936 256)
      0 = true := by decide +kernel
  have replay98_32 : fastPacked 3947 (maskedCandidates 3947 8192 256)
      0 = true := by decide +kernel
  have replay98_33 : fastPacked 3947 (maskedCandidates 3947 8448 256)
      0 = true := by decide +kernel
  have replay98_34 : fastPacked 3947 (maskedCandidates 3947 8704 256)
      0x7cd0017cd001 = true := by decide +kernel
  have replay98_35 : fastPacked 3947 (maskedCandidates 3947 8960 256)
      0x7cd000 = true := by decide +kernel
  have replay98_36 : fastPacked 3947 (maskedCandidates 3947 9216 256)
      0x7cc000 = true := by decide +kernel
  have replay98_37 : fastPacked 3947 (maskedCandidates 3947 9472 256)
      0x7cc0007cc000 = true := by decide +kernel
  have replay98_38 : fastPacked 3947 (maskedCandidates 3947 9728 256)
      0 = true := by decide +kernel
  have replay98_39 : fastPacked 3947 (maskedCandidates 3947 9984 256)
      0x7ca0007cb0007cb000 = true := by decide +kernel
  have replay98_40 : fastPacked 3947 (maskedCandidates 3947 10240 256)
      0x7ca000 = true := by decide +kernel
  have replay98_41 : fastPacked 3947 (maskedCandidates 3947 10496 256)
      0x7c90007c9000 = true := by decide +kernel
  have replay98_42 : fastPacked 3947 (maskedCandidates 3947 10752 256)
      0 = true := by decide +kernel
  have replay98_43 : fastPacked 3947 (maskedCandidates 3947 11008 256)
      0x7c8000 = true := by decide +kernel
  have replay98_44 : fastPacked 3947 (maskedCandidates 3947 11264 256)
      0x7c8000 = true := by decide +kernel
  have replay98_45 : fastPacked 3947 (maskedCandidates 3947 11520 256)
      0x7c8000 = true := by decide +kernel
  have replay98_46 : fastPacked 3947 (maskedCandidates 3947 11776 256)
      0x7c7000 = true := by decide +kernel
  have replay98_47 : fastPacked 3947 (maskedCandidates 3947 12032 256)
      0x7c7000 = true := by decide +kernel
  have replay98_48 : fastPacked 3947 (maskedCandidates 3947 12288 111)
      0 = true := by decide +kernel
  have hs : p*p ≤ 3947^3 := by simpa only [pow_two] using le_of_lt hhi
  have hpBound := Nat.le_sqrt.mpr hs
  have hb : p/20 < 12399 := by
    have hc : (3947^3 : ℕ).sqrt = 247970 := by decide +kernel
    rw [hc] at hpBound
    omega
  set j := p/20/256 with hj
  have jBound : j < 49 := by omega
  have hbase : 256*j ≤ p/20 := by omega
  have hend : p/20 < 256*(j+1) := by omega
  interval_cases j
  · exact fastPacked_sound replay98_0 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_1 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_2 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_3 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_4 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_5 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_6 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_7 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_8 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_9 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_10 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_11 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_12 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_13 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_14 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_15 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_16 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_17 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_18 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_19 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_20 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_21 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_22 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_23 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_24 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_25 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_26 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_27 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_28 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_29 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_30 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_31 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_32 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_33 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_34 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_35 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_36 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_37 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_38 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_39 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_40 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_41 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_42 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_43 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_44 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_45 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_46 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_47 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hend)
  · exact fastPacked_sound replay98_48 (candidate_mem_masked hp hlo hhi hmod hres hpass hbase hb)

private def validIndices : List ℕ := [1, 2, 5, 7, 8, 11, 13, 14, 19, 20, 22, 23, 29, 32, 35, 40, 41, 43, 44, 46, 47, 49, 50, 56, 58, 61, 67, 76, 79, 82, 83, 86, 88, 97, 98]

private theorem checkedIndices : (List.range 100).all
    (fun i => !possiblePrime (qFromIndex i) || validIndices.contains i) = true := by
  decide +kernel

private theorem index_mem {i : ℕ} (hi : i<100) (hq : (qFromIndex i).Prime) :
    i ∈ validIndices := by
  have h := List.all_eq_true.mp checkedIndices i (List.mem_range.mpr hi)
  have hs := prime_possiblePrime hq
  simpa [hs] using h

private theorem check_for_index {p i : ℕ} (hp : p.Prime) (hi : i<100)
    (hq : (qFromIndex i).Prime) (hlo : 2*qFromIndex i<p)
    (hhi : p^2<(qFromIndex i)^3) (hmod : p%3≠qFromIndex i%3)
    (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p (qFromIndex i) = true) :
    ∃ d, signCertificate p (qFromIndex i) d = true := by
  have hvalid := index_mem hi hq
  simp only [validIndices, List.mem_cons, List.not_mem_nil, or_false] at hvalid
  rcases hvalid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked01 hp hlo hhi hmod hres hpass
  · exact checked02 hp hlo hhi hmod hres hpass
  · exact checked05 hp hlo hhi hmod hres hpass
  · exact checked07 hp hlo hhi hmod hres hpass
  · exact checked08 hp hlo hhi hmod hres hpass
  · exact checked11 hp hlo hhi hmod hres hpass
  · exact checked13 hp hlo hhi hmod hres hpass
  · exact checked14 hp hlo hhi hmod hres hpass
  · exact checked19 hp hlo hhi hmod hres hpass
  · exact checked20 hp hlo hhi hmod hres hpass
  · exact checked22 hp hlo hhi hmod hres hpass
  · exact checked23 hp hlo hhi hmod hres hpass
  · exact checked29 hp hlo hhi hmod hres hpass
  · exact checked32 hp hlo hhi hmod hres hpass
  · exact checked35 hp hlo hhi hmod hres hpass
  · exact checked40 hp hlo hhi hmod hres hpass
  · exact checked41 hp hlo hhi hmod hres hpass
  · exact checked43 hp hlo hhi hmod hres hpass
  · exact checked44 hp hlo hhi hmod hres hpass
  · exact checked46 hp hlo hhi hmod hres hpass
  · exact checked47 hp hlo hhi hmod hres hpass
  · exact checked49 hp hlo hhi hmod hres hpass
  · exact checked50 hp hlo hhi hmod hres hpass
  · exact checked56 hp hlo hhi hmod hres hpass
  · exact checked58 hp hlo hhi hmod hres hpass
  · exact checked61 hp hlo hhi hmod hres hpass
  · exact checked67 hp hlo hhi hmod hres hpass
  · exact checked76 hp hlo hhi hmod hres hpass
  · exact checked79 hp hlo hhi hmod hres hpass
  · exact checked82 hp hlo hhi hmod hres hpass
  · exact checked83 hp hlo hhi hmod hres hpass
  · exact checked86 hp hlo hhi hmod hres hpass
  · exact checked88 hp hlo hhi hmod hres hpass
  · exact checked97 hp hlo hhi hmod hres hpass
  · exact checked98 hp hlo hhi hmod hres hpass


theorem bounded : OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H1 := by
  intro p q x hp hq _ hp4 hq8 _ hlo hmod hhi hp5 hq5 hqBound _ _ hx _
  dsimp only
  intro _ hrec _
  have hroot : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x=0 := by
    simp only [cubic,pairCoeff,sumCoeff,productCoeff]
    linear_combination -hrec
  have hqValue := q_index_eq hq8 hq5
  have hi : q/40 < 100 := by omega
  have hqPrime : (qFromIndex (q/40)).Prime := by rwa [hqValue]
  have hlo' : 2*qFromIndex (q/40)<p := by rwa [hqValue]
  have hhi' : p^2<(qFromIndex (q/40))^3 := by rwa [hqValue]
  have hmod' : p%3≠qFromIndex (q/40)%3 := by rwa [hqValue]
  have hpass : sieveCubic p (qFromIndex (q/40))=true := by
    rw [hqValue]
    exact sieveCubic_sound hroot
  obtain ⟨d, hd⟩ := check_for_index hp hi hqPrime hlo' hhi' hmod'
    (p_mod_twenty hp4 hp5) hpass
  rw [hqValue] at hd
  exact signCertificate_sound hd (le_of_lt hx) hroot

end A056777Bounded

theorem OMA.solution : OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H1 :=
  A056777Bounded.bounded
