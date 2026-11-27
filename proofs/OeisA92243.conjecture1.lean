import FormalConjectures.OEIS.«92243»

/-! A finite certificate for the prime-gap score. A number in the scan range is
composite precisely when it has a prime divisor at most 1920, apart from the
small prime cases handled directly. Each block verifies its ending prime
index, last prime, last gap, and cumulative score in the Lean kernel. -/

open OeisA92243

namespace OMA.PrimeGap

structure State where
  index : ℕ
  last : ℕ
  gap : ℕ
  score : ℤ
  deriving DecidableEq

def next (s : State) (p : ℕ) : State :=
  let gap := p - s.last
  ⟨s.index + 1, p, gap, s.score + ((gap : ℤ) - s.gap).sign⟩

def Valid (b : ℕ) (s : State) : Prop :=
  2 ≤ s.index ∧ Nat.count Nat.Prime b = s.index + 1 ∧
  Nat.nth Nat.Prime s.index = s.last ∧ OeisA92243.primeGap s.index = s.gap ∧ a s.index = s.score

lemma score_succ {i : ℕ} (hi : 2 ≤ i) :
    a (i + 1) = a i + ((OeisA92243.primeGap (i + 1) : ℤ) - OeisA92243.primeGap i).sign := by
  simp only [a, if_neg (show ¬ i + 1 ≤ 1 by omega), if_neg (show ¬ i ≤ 1 by omega)]
  exact Finset.sum_Icc_succ_top (by omega : 2 ≤ i + 1) _

lemma valid_next {b : ℕ} {s : State} (hs : Valid b s) (hp : b.Prime) :
    Valid (b+1) (next s b) := by
  obtain ⟨hi, hc, hl, hg, ha⟩ := hs
  have hn : Nat.nth Nat.Prime (s.index + 1) = b := hc ▸ Nat.nth_count hp
  have hgap : OeisA92243.primeGap (s.index+1) = b - s.last := by simp [OeisA92243.primeGap, hn, hl]
  exact ⟨by dsimp [next]; omega, by simp [next, Nat.count_succ, hc, hp],
    hn, hgap, by simp [next, score_succ hi, hgap, hg, ha]⟩

lemma valid_skip {b : ℕ} {s : State} (hs : Valid b s) (hp : ¬ b.Prime) :
    Valid (b+1) s :=
  ⟨hs.1, by simpa only [Nat.count_succ, if_neg hp, add_zero] using hs.2.1,
    hs.2.2⟩


-- All possible composite scan entries have a prime factor at most 1920.
def sieveProduct : ℕ := 330299814997665459752503875936311543658654867563977165754682006007076789023726298028755353475271999414453764134871401945863424316247498974525140884502213619463897242701793280976314619522940952707678656355866315555813453709146270396483864711972590100553162544989477344756108882470964672146103057849578011704570100638149372613055636349494040526380005363336573870322107486828807474961912982325253455883323020690855949007426633568611938908672810913185726817817735856245280443222830596087494005801000571579740438132076783124492309104396505888935213078665394872422903777412625904361394221872967927700481448076066485794738700362833072432132949703400435636025207134810624436376055618005498163855585536582182713434179261367383522239622181965584795602707040077669355630046755401445847804541645846120576194385396822416810

set_option maxRecDepth 16384 in
lemma product_dvd_fact : sieveProduct ∣ Nat.factorial 1920 :=
  Nat.dvd_of_mod_eq_zero (by rfl)

set_option maxRecDepth 16384 in
lemma small_divisors : ((List.range 1920).all fun i => sieveProduct ^ 10 % (i+1) == 0) = true := by
  decide +kernel

lemma divides_sieve {q : ℕ} (hq : q.Prime) (hle : q ≤ 1920) : q ∣ sieveProduct := by
  have hem : q-1 ∈ List.range 1920 := List.mem_range.mpr (by have := hq.two_le; omega)
  have h := List.all_eq_true.mp small_divisors (q-1) hem
  apply hq.dvd_of_dvd_pow (n := 10)
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.sub_add_cancel hq.one_le] using h

def smallTest (n : ℕ) : Bool :=
  if n ≤ 43 then decide n.Prime else Nat.gcd n 60415263063373835637355132068513997507264512000000000 == 1

lemma small_spec (n : ℕ) (hle : n ≤ 1920) : smallTest n = true ↔ n.Prime := by
  unfold smallTest
  split_ifs with h
  · simp
  have hf : Nat.factorial 43 = 60415263063373835637355132068513997507264512000000000 := by rfl
  rw [← hf, beq_iff_eq]
  change n.Coprime (Nat.factorial 43) ↔ n.Prime
  constructor
  · intro hc
    by_contra hnp
    have hm := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    have hmin := (Nat.coprime_factorial_iff (by omega : n ≠ 1)).mp hc
    nlinarith
  · intro hp
    exact hp.coprime_factorial_of_lt (by omega)

def test (n : ℕ) : Bool :=
  if n ≤ 1920 then smallTest n else
    n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && Nat.gcd n sieveProduct == 1

lemma test_spec (n : ℕ) (hn : n < 3666582) : test n = true ↔ n.Prime := by
  unfold test
  split_ifs with hsmall
  · exact small_spec n hsmall
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  constructor
  · intro h
    by_contra hnp
    have hfac := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have hbound : n.minFac ≤ 1920 := by nlinarith
    have bad := Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd n)
      (divides_sieve hp hbound)
    exact bad h.2
  · intro hp
    have hm (q : ℕ) (hq : q.Prime) (hle : q ≤ 1920) : n % q ≠ 0 := by
      intro h
      exact (hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h)).elim
        hq.ne_one (by omega)
    exact ⟨⟨⟨hm 2 (by decide) (by decide), hm 3 (by decide) (by decide)⟩,
      hm 5 (by decide) (by decide)⟩, by
      exact hp.coprime_iff_not_dvd.mpr fun hd => hsmall (hp.dvd_factorial.mp (hd.trans product_dvd_fact))⟩

def scan : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ → State
  | 0, _, i, last, gap, score => ⟨i, last, gap, score⟩
  | k+1, b, i, last, gap, score =>
    if test b then
      scan k (b+1) (i+1) b (b-last) (score + ((b-last : ℕ) - (gap : ℤ)).sign)
    else scan k (b+1) i last gap score

lemma scan_valid (k b : ℕ) (s : State) (hs : Valid b s) (hbound : b+k ≤ 3666582) :
    Valid (b+k) (scan k b s.index s.last s.gap s.score) := by
  induction k generalizing b s with
  | zero => simpa [scan] using hs
  | succ k ih =>
    have hlt : b < 3666582 := by omega
    have he : b+(k+1) = (b+1)+k := by omega
    rw [he]
    by_cases hp : b.Prime
    · simpa only [scan, (test_spec b hlt).mpr hp, if_true, next] using
        ih (b+1) (next s b) (valid_next hs hp) (by omega)
    · have hno : test b = false := Bool.eq_false_iff.mpr (mt (test_spec b hlt).mp hp)
      simpa only [scan, hno, Bool.false_eq_true, if_false] using
        ih (b+1) s (valid_skip hs hp) (by omega)

lemma initial : Valid 6 ⟨2,5,2,1⟩ := by
  refine ⟨by decide, by decide +kernel, Nat.nth_prime_two_eq_five, ?_, OeisA92243.a_2⟩
  simp [OeisA92243.primeGap, Nat.nth_prime_two_eq_five, Nat.nth_prime_one_eq_three]

lemma advance {b k : ℕ} {s t : State}
    (hs : Valid b s) (hb : b + k ≤ 3666582)
    (hscan : scan k b s.index s.last s.gap s.score = t) : Valid (b+k) t :=
  hscan ▸ scan_valid k b s hs hb

def scanOdd : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ → State
  | 0, _, i, last, gap, score => ⟨i, last, gap, score⟩
  | k+1, b, i, last, gap, score =>
    if test b then
      scanOdd k (b+2) (i+1) b (b-last) (score + ((b-last : ℕ) - (gap : ℤ)).sign)
    else scanOdd k (b+2) i last gap score

lemma odd_valid (k b : ℕ) (s : State) (hs : Valid b s) (hodd : Odd b)
    (hlo : 5 ≤ b) (hbound : b+2*k ≤ 3666583) :
    Valid (b+2*k) (scanOdd k b s.index s.last s.gap s.score) := by
  induction k generalizing b s with
  | zero => simpa [scanOdd] using hs
  | succ k ih =>
    obtain ⟨j, hj⟩ := hodd
    have heven : ¬ (b+1).Prime := by
      intro hp
      obtain ⟨z, hz⟩ := hp.odd_of_ne_two (by omega)
      omega
    have hn : Odd (b+2) := ⟨j+1, by omega⟩
    have he : b+2*(k+1) = b+2+2*k := by omega
    have hlt : b < 3666582 := by omega
    rw [he]
    by_cases hp : b.Prime
    · simpa only [scanOdd, (test_spec b hlt).mpr hp, if_true, next] using
        ih (b+2) (next s b) (valid_skip (valid_next hs hp) heven) hn (by omega) (by omega)
    · have hno : test b = false := Bool.eq_false_iff.mpr (mt (test_spec b hlt).mp hp)
      simpa only [scanOdd, hno, Bool.false_eq_true, if_false] using
        ih (b+2) s (valid_skip (valid_skip hs hp) heven) hn (by omega) (by omega)

lemma odd_advance {b k : ℕ} {s t : State} (hs : Valid b s)
    (ho : Odd b) (hl : 5 ≤ b) (hb : b + 2*k ≤ 3666583)
    (hscan : scanOdd k b s.index s.last s.gap s.score = t) : Valid (b+2*k) t :=
  hscan ▸ odd_valid k b s hs ho hl hb


lemma block0 : Valid 7 ⟨2, 5, 2, 1⟩ := valid_skip initial (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block1 : Valid 16391 ⟨1899, 16381, 12, 35⟩ :=
  odd_advance (k := 8192) block0 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block2 : Valid 32775 ⟨3512, 32771, 22, 37⟩ :=
  odd_advance (k := 8192) block1 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block3 : Valid 49159 ⟨5051, 49157, 18, 32⟩ :=
  odd_advance (k := 8192) block2 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block4 : Valid 65543 ⟨6543, 65539, 2, 38⟩ :=
  odd_advance (k := 8192) block3 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block5 : Valid 81927 ⟨8008, 81919, 18, 53⟩ :=
  odd_advance (k := 8192) block4 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block6 : Valid 98311 ⟨9438, 98299, 2, 66⟩ :=
  odd_advance (k := 8192) block5 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block7 : Valid 114695 ⟨10847, 114691, 2, 51⟩ :=
  odd_advance (k := 8192) block6 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block8 : Valid 131079 ⟨12250, 131071, 8, 68⟩ :=
  odd_advance (k := 8192) block7 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block9 : Valid 147463 ⟨13631, 147457, 6, 69⟩ :=
  odd_advance (k := 8192) block8 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block10 : Valid 163847 ⟨14999, 163841, 22, 83⟩ :=
  odd_advance (k := 8192) block9 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block11 : Valid 180231 ⟨16356, 180221, 10, 54⟩ :=
  odd_advance (k := 8192) block10 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block12 : Valid 196615 ⟨17704, 196613, 16, 61⟩ :=
  odd_advance (k := 8192) block11 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block13 : Valid 212999 ⟨19044, 212987, 6, 47⟩ :=
  odd_advance (k := 8192) block12 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block14 : Valid 229383 ⟨20378, 229373, 22, 49⟩ :=
  odd_advance (k := 8192) block13 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block15 : Valid 245767 ⟨21694, 245759, 6, 39⟩ :=
  odd_advance (k := 8192) block14 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block16 : Valid 262151 ⟨23000, 262147, 8, 54⟩ :=
  odd_advance (k := 8192) block15 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block17 : Valid 278535 ⟨24317, 278503, 2, 13⟩ :=
  odd_advance (k := 8192) block16 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block18 : Valid 294919 ⟨25606, 294911, 18, 37⟩ :=
  odd_advance (k := 8192) block17 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block19 : Valid 311303 ⟨26899, 311299, 6, 39⟩ :=
  odd_advance (k := 8192) block18 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block20 : Valid 327687 ⟨28222, 327673, 6, 42⟩ :=
  odd_advance (k := 8192) block19 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block21 : Valid 344071 ⟨29503, 344053, 14, 33⟩ :=
  odd_advance (k := 8192) block20 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block22 : Valid 360455 ⟨30788, 360439, 18, 27⟩ :=
  odd_advance (k := 8192) block21 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block23 : Valid 376839 ⟨32055, 376837, 14, 57⟩ :=
  odd_advance (k := 8192) block22 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block24 : Valid 393223 ⟨33334, 393209, 6, 26⟩ :=
  odd_advance (k := 8192) block23 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block25 : Valid 409607 ⟨34578, 409597, 8, 28⟩ :=
  odd_advance (k := 8192) block24 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block26 : Valid 425991 ⟨35852, 425989, 2, 25⟩ :=
  odd_advance (k := 8192) block25 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block27 : Valid 442375 ⟨37125, 442367, 4, 29⟩ :=
  odd_advance (k := 8192) block26 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block28 : Valid 458759 ⟨38367, 458747, 18, 33⟩ :=
  odd_advance (k := 8192) block27 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block29 : Valid 475143 ⟨39627, 475141, 32, 18⟩ :=
  odd_advance (k := 8192) block28 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block30 : Valid 491527 ⟨40882, 491503, 2, 17⟩ :=
  odd_advance (k := 8192) block29 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block31 : Valid 507911 ⟨42132, 507907, 6, -1⟩ :=
  odd_advance (k := 8192) block30 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block32 : Valid 524295 ⟨43389, 524287, 18, 5⟩ :=
  odd_advance (k := 8192) block31 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block33 : Valid 540679 ⟨44622, 540677, 48, 21⟩ :=
  odd_advance (k := 8192) block32 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block34 : Valid 557063 ⟨45859, 557059, 2, 33⟩ :=
  odd_advance (k := 8192) block33 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block35 : Valid 573447 ⟨47087, 573437, 28, 29⟩ :=
  odd_advance (k := 8192) block34 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block36 : Valid 589831 ⟨48340, 589829, 18, 58⟩ :=
  odd_advance (k := 8192) block35 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block37 : Valid 606215 ⟨49568, 606181, 8, 51⟩ :=
  odd_advance (k := 8192) block36 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block38 : Valid 622599 ⟨50804, 622577, 6, 71⟩ :=
  odd_advance (k := 8192) block37 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block39 : Valid 638983 ⟨51999, 638977, 6, 40⟩ :=
  odd_advance (k := 8192) block38 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block40 : Valid 655367 ⟨53227, 655357, 6, 38⟩ :=
  odd_advance (k := 8192) block39 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block41 : Valid 671751 ⟨54438, 671743, 14, 49⟩ :=
  odd_advance (k := 8192) block40 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block42 : Valid 688135 ⟨55672, 688133, 22, 41⟩ :=
  odd_advance (k := 8192) block41 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block43 : Valid 704519 ⟨56883, 704507, 30, 58⟩ :=
  odd_advance (k := 8192) block42 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block44 : Valid 720903 ⟨58097, 720901, 2, 66⟩ :=
  odd_advance (k := 8192) block43 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block45 : Valid 737287 ⟨59323, 737281, 2, 53⟩ :=
  odd_advance (k := 8192) block44 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block46 : Valid 753671 ⟨60508, 753659, 12, 12⟩ :=
  odd_advance (k := 8192) block45 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block47 : Valid 770055 ⟨61737, 770053, 6, 20⟩ :=
  odd_advance (k := 8192) block46 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block48 : Valid 786439 ⟨62946, 786433, 2, 42⟩ :=
  odd_advance (k := 8192) block47 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block49 : Valid 802823 ⟨64161, 802811, 12, 60⟩ :=
  odd_advance (k := 8192) block48 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block50 : Valid 819207 ⟨65347, 819187, 14, 53⟩ :=
  odd_advance (k := 8192) block49 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block51 : Valid 835591 ⟨66569, 835559, 6, 44⟩ :=
  odd_advance (k := 8192) block50 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block52 : Valid 851975 ⟨67763, 851971, 14, 46⟩ :=
  odd_advance (k := 8192) block51 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block53 : Valid 868359 ⟨68969, 868349, 12, 66⟩ :=
  odd_advance (k := 8192) block52 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block54 : Valid 884743 ⟨70168, 884717, 18, 71⟩ :=
  odd_advance (k := 8192) block53 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block55 : Valid 901127 ⟨71356, 901111, 14, 82⟩ :=
  odd_advance (k := 8192) block54 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block56 : Valid 917511 ⟨72546, 917503, 32, 86⟩ :=
  odd_advance (k := 8192) block55 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block57 : Valid 933895 ⟨73747, 933893, 10, 64⟩ :=
  odd_advance (k := 8192) block56 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block58 : Valid 950279 ⟨74927, 950269, 18, 66⟩ :=
  odd_advance (k := 8192) block57 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block59 : Valid 966663 ⟨76115, 966661, 2, 47⟩ :=
  odd_advance (k := 8192) block58 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block60 : Valid 983047 ⟨77278, 982981, 8, 73⟩ :=
  odd_advance (k := 8192) block59 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block61 : Valid 999431 ⟨78459, 999389, 12, 55⟩ :=
  odd_advance (k := 8192) block60 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block62 : Valid 1015815 ⟨79667, 1015813, 44, 69⟩ :=
  odd_advance (k := 8192) block61 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block63 : Valid 1032199 ⟨80844, 1032193, 2, 87⟩ :=
  odd_advance (k := 8192) block62 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block64 : Valid 1048583 ⟨82024, 1048573, 2, 92⟩ :=
  odd_advance (k := 8192) block63 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block65 : Valid 1064967 ⟨83183, 1064957, 4, 81⟩ :=
  odd_advance (k := 8192) block64 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block66 : Valid 1081351 ⟨84378, 1081337, 6, 118⟩ :=
  odd_advance (k := 8192) block65 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block67 : Valid 1097735 ⟨85557, 1097729, 12, 122⟩ :=
  odd_advance (k := 8192) block66 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block68 : Valid 1114119 ⟨86756, 1114117, 6, 165⟩ :=
  odd_advance (k := 8192) block67 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block69 : Valid 1130503 ⟨87918, 1130501, 4, 144⟩ :=
  odd_advance (k := 8192) block68 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block70 : Valid 1146887 ⟨89082, 1146881, 4, 145⟩ :=
  odd_advance (k := 8192) block69 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block71 : Valid 1163271 ⟨90287, 1163263, 6, 134⟩ :=
  odd_advance (k := 8192) block70 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block72 : Valid 1179655 ⟨91465, 1179649, 8, 152⟩ :=
  odd_advance (k := 8192) block71 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block73 : Valid 1196039 ⟨92654, 1196033, 4, 118⟩ :=
  odd_advance (k := 8192) block72 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block74 : Valid 1212423 ⟨93793, 1212401, 4, 101⟩ :=
  odd_advance (k := 8192) block73 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block75 : Valid 1228807 ⟨94963, 1228789, 6, 103⟩ :=
  odd_advance (k := 8192) block74 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block76 : Valid 1245191 ⟨96113, 1245187, 18, 126⟩ :=
  odd_advance (k := 8192) block75 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block77 : Valid 1261575 ⟨97291, 1261571, 4, 152⟩ :=
  odd_advance (k := 8192) block76 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block78 : Valid 1277959 ⟨98460, 1277957, 46, 126⟩ :=
  odd_advance (k := 8192) block77 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block79 : Valid 1294343 ⟨99627, 1294339, 30, 137⟩ :=
  odd_advance (k := 8192) block78 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block80 : Valid 1310727 ⟨100786, 1310723, 4, 134⟩ :=
  odd_advance (k := 8192) block79 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block81 : Valid 1327111 ⟨101952, 1327099, 8, 146⟩ :=
  odd_advance (k := 8192) block80 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block82 : Valid 1343495 ⟨103109, 1343491, 12, 99⟩ :=
  odd_advance (k := 8192) block81 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block83 : Valid 1359879 ⟨104247, 1359871, 12, 130⟩ :=
  odd_advance (k := 8192) block82 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block84 : Valid 1376263 ⟨105407, 1376257, 20, 115⟩ :=
  odd_advance (k := 8192) block83 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block85 : Valid 1392647 ⟨106564, 1392631, 12, 117⟩ :=
  odd_advance (k := 8192) block84 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block86 : Valid 1409031 ⟨107738, 1409027, 10, 128⟩ :=
  odd_advance (k := 8192) block85 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block87 : Valid 1425415 ⟨108869, 1425371, 4, 121⟩ :=
  odd_advance (k := 8192) block86 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block88 : Valid 1441799 ⟨110055, 1441771, 14, 127⟩ :=
  odd_advance (k := 8192) block87 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block89 : Valid 1458183 ⟨111213, 1458179, 10, 123⟩ :=
  odd_advance (k := 8192) block88 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block90 : Valid 1474567 ⟨112362, 1474559, 10, 118⟩ :=
  odd_advance (k := 8192) block89 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block91 : Valid 1490951 ⟨113527, 1490941, 8, 107⟩ :=
  odd_advance (k := 8192) block90 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block92 : Valid 1507335 ⟨114699, 1507321, 20, 96⟩ :=
  odd_advance (k := 8192) block91 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block93 : Valid 1523719 ⟨115841, 1523707, 6, 82⟩ :=
  odd_advance (k := 8192) block92 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block94 : Valid 1540103 ⟨116972, 1540087, 8, 76⟩ :=
  odd_advance (k := 8192) block93 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block95 : Valid 1556487 ⟨118119, 1556473, 20, 65⟩ :=
  odd_advance (k := 8192) block94 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block96 : Valid 1572871 ⟨119268, 1572869, 16, 58⟩ :=
  odd_advance (k := 8192) block95 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block97 : Valid 1589255 ⟨120391, 1589251, 2, 35⟩ :=
  odd_advance (k := 8192) block96 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block98 : Valid 1605639 ⟨121549, 1605631, 2, -7⟩ :=
  odd_advance (k := 8192) block97 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block99 : Valid 1622023 ⟨122681, 1622009, 16, -18⟩ :=
  odd_advance (k := 8192) block98 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block100 : Valid 1638407 ⟨123840, 1638353, 4, -20⟩ :=
  odd_advance (k := 8192) block99 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block101 : Valid 1654791 ⟨124973, 1654789, 2, -14⟩ :=
  odd_advance (k := 8192) block100 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block102 : Valid 1671175 ⟨126128, 1671161, 22, -14⟩ :=
  odd_advance (k := 8192) block101 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block103 : Valid 1687559 ⟨127264, 1687549, 18, -1⟩ :=
  odd_advance (k := 8192) block102 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block104 : Valid 1703943 ⟨128413, 1703941, 38, 2⟩ :=
  odd_advance (k := 8192) block103 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block105 : Valid 1720327 ⟨129549, 1720321, 14, -31⟩ :=
  odd_advance (k := 8192) block104 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block106 : Valid 1736711 ⟨130665, 1736701, 12, -32⟩ :=
  odd_advance (k := 8192) block105 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block107 : Valid 1753095 ⟨131836, 1753093, 24, -33⟩ :=
  odd_advance (k := 8192) block106 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block108 : Valid 1769479 ⟨132937, 1769473, 32, -61⟩ :=
  odd_advance (k := 8192) block107 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block109 : Valid 1785863 ⟨134085, 1785857, 4, -47⟩ :=
  odd_advance (k := 8192) block108 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block110 : Valid 1802247 ⟨135226, 1802239, 8, -67⟩ :=
  odd_advance (k := 8192) block109 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block111 : Valid 1818631 ⟨136360, 1818617, 6, -71⟩ :=
  odd_advance (k := 8192) block110 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block112 : Valid 1835015 ⟨137523, 1835003, 4, -62⟩ :=
  odd_advance (k := 8192) block111 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block113 : Valid 1851399 ⟨138629, 1851391, 18, -72⟩ :=
  odd_advance (k := 8192) block112 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block114 : Valid 1867783 ⟨139801, 1867771, 2, -93⟩ :=
  odd_advance (k := 8192) block113 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block115 : Valid 1884167 ⟨140929, 1884133, 12, -91⟩ :=
  odd_advance (k := 8192) block114 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block116 : Valid 1900551 ⟨142070, 1900543, 2, -57⟩ :=
  odd_advance (k := 8192) block115 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block117 : Valid 1916935 ⟨143209, 1916921, 4, -59⟩ :=
  odd_advance (k := 8192) block116 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block118 : Valid 1933319 ⟨144347, 1933301, 12, -64⟩ :=
  odd_advance (k := 8192) block117 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block119 : Valid 1949703 ⟨145480, 1949657, 18, -104⟩ :=
  odd_advance (k := 8192) block118 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block120 : Valid 1966087 ⟨146604, 1966079, 30, -92⟩ :=
  odd_advance (k := 8192) block119 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block121 : Valid 1982471 ⟨147705, 1982467, 20, -66⟩ :=
  odd_advance (k := 8192) block120 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block122 : Valid 1998855 ⟨148857, 1998839, 12, -80⟩ :=
  odd_advance (k := 8192) block121 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block123 : Valid 2015239 ⟨150004, 2015213, 10, -81⟩ :=
  odd_advance (k := 8192) block122 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block124 : Valid 2031623 ⟨151127, 2031611, 12, -78⟩ :=
  odd_advance (k := 8192) block123 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block125 : Valid 2048007 ⟨152252, 2048003, 10, -105⟩ :=
  odd_advance (k := 8192) block124 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block126 : Valid 2064391 ⟨153384, 2064389, 10, -113⟩ :=
  odd_advance (k := 8192) block125 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block127 : Valid 2080775 ⟨154498, 2080763, 4, -90⟩ :=
  odd_advance (k := 8192) block126 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block128 : Valid 2097159 ⟨155610, 2097143, 10, -121⟩ :=
  odd_advance (k := 8192) block127 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block129 : Valid 2113543 ⟨156741, 2113523, 10, -140⟩ :=
  odd_advance (k := 8192) block128 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block130 : Valid 2129927 ⟨157879, 2129903, 12, -132⟩ :=
  odd_advance (k := 8192) block129 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block131 : Valid 2146311 ⟨159005, 2146307, 4, -111⟩ :=
  odd_advance (k := 8192) block130 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block132 : Valid 2162695 ⟨160143, 2162681, 18, -143⟩ :=
  odd_advance (k := 8192) block131 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block133 : Valid 2179079 ⟨161260, 2179063, 14, -141⟩ :=
  odd_advance (k := 8192) block132 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block134 : Valid 2195463 ⟨162373, 2195461, 18, -117⟩ :=
  odd_advance (k := 8192) block133 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block135 : Valid 2211847 ⟨163487, 2211821, 4, -102⟩ :=
  odd_advance (k := 8192) block134 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block136 : Valid 2228231 ⟨164597, 2228221, 12, -121⟩ :=
  odd_advance (k := 8192) block135 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block137 : Valid 2244615 ⟨165704, 2244611, 22, -141⟩ :=
  odd_advance (k := 8192) block136 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block138 : Valid 2260999 ⟨166848, 2260967, 6, -155⟩ :=
  odd_advance (k := 8192) block137 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block139 : Valid 2277383 ⟨167986, 2277377, 10, -171⟩ :=
  odd_advance (k := 8192) block138 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block140 : Valid 2293767 ⟨169083, 2293757, 6, -169⟩ :=
  odd_advance (k := 8192) block139 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block141 : Valid 2310151 ⟨170207, 2310137, 30, -164⟩ :=
  odd_advance (k := 8192) block140 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block142 : Valid 2326535 ⟨171291, 2326517, 10, -133⟩ :=
  odd_advance (k := 8192) block141 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block143 : Valid 2342919 ⟨172409, 2342869, 30, -113⟩ :=
  odd_advance (k := 8192) block142 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block144 : Valid 2359303 ⟨173513, 2359267, 6, -143⟩ :=
  odd_advance (k := 8192) block143 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block145 : Valid 2375687 ⟨174620, 2375671, 30, -145⟩ :=
  odd_advance (k := 8192) block144 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block146 : Valid 2392071 ⟨175761, 2392067, 10, -134⟩ :=
  odd_advance (k := 8192) block145 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block147 : Valid 2408455 ⟨176860, 2408437, 6, -137⟩ :=
  odd_advance (k := 8192) block146 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block148 : Valid 2424839 ⟨177974, 2424833, 6, -129⟩ :=
  odd_advance (k := 8192) block147 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block149 : Valid 2441223 ⟨179082, 2441221, 12, -150⟩ :=
  odd_advance (k := 8192) block148 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block150 : Valid 2457607 ⟨180196, 2457569, 6, -137⟩ :=
  odd_advance (k := 8192) block149 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block151 : Valid 2473991 ⟨181310, 2473979, 12, -157⟩ :=
  odd_advance (k := 8192) block150 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block152 : Valid 2490375 ⟨182419, 2490337, 8, -191⟩ :=
  odd_advance (k := 8192) block151 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block153 : Valid 2506759 ⟨183535, 2506729, 6, -232⟩ :=
  odd_advance (k := 8192) block152 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block154 : Valid 2523143 ⟨184634, 2523139, 6, -239⟩ :=
  odd_advance (k := 8192) block153 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block155 : Valid 2539527 ⟨185765, 2539519, 6, -242⟩ :=
  odd_advance (k := 8192) block154 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block156 : Valid 2555911 ⟨186865, 2555897, 4, -212⟩ :=
  odd_advance (k := 8192) block155 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block157 : Valid 2572295 ⟨187974, 2572289, 10, -242⟩ :=
  odd_advance (k := 8192) block156 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block158 : Valid 2588679 ⟨189110, 2588671, 2, -253⟩ :=
  odd_advance (k := 8192) block157 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block159 : Valid 2605063 ⟨190209, 2605039, 18, -243⟩ :=
  odd_advance (k := 8192) block158 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block160 : Valid 2621447 ⟨191307, 2621431, 44, -277⟩ :=
  odd_advance (k := 8192) block159 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block161 : Valid 2637831 ⟨192425, 2637799, 2, -295⟩ :=
  odd_advance (k := 8192) block160 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block162 : Valid 2654215 ⟨193541, 2654213, 4, -291⟩ :=
  odd_advance (k := 8192) block161 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block163 : Valid 2670599 ⟨194641, 2670589, 18, -274⟩ :=
  odd_advance (k := 8192) block162 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block164 : Valid 2686983 ⟨195746, 2686979, 6, -245⟩ :=
  odd_advance (k := 8192) block163 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block165 : Valid 2703367 ⟨196860, 2703347, 6, -231⟩ :=
  odd_advance (k := 8192) block164 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block166 : Valid 2719751 ⟨198007, 2719747, 6, -235⟩ :=
  odd_advance (k := 8192) block165 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block167 : Valid 2736135 ⟨199062, 2736131, 42, -211⟩ :=
  odd_advance (k := 8192) block166 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block168 : Valid 2752519 ⟨200168, 2752517, 4, -235⟩ :=
  odd_advance (k := 8192) block167 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block169 : Valid 2768903 ⟨201277, 2768897, 4, -252⟩ :=
  odd_advance (k := 8192) block168 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block170 : Valid 2785287 ⟨202375, 2785273, 12, -244⟩ :=
  odd_advance (k := 8192) block169 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block171 : Valid 2801671 ⟨203469, 2801641, 20, -208⟩ :=
  odd_advance (k := 8192) block170 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block172 : Valid 2818055 ⟨204612, 2818043, 10, -217⟩ :=
  odd_advance (k := 8192) block171 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block173 : Valid 2834439 ⟨205730, 2834417, 4, -228⟩ :=
  odd_advance (k := 8192) block172 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block174 : Valid 2850823 ⟨206842, 2850811, 14, -232⟩ :=
  odd_advance (k := 8192) block173 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block175 : Valid 2867207 ⟨207936, 2867107, 8, -253⟩ :=
  odd_advance (k := 8192) block174 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block176 : Valid 2883591 ⟨209013, 2883577, 14, -250⟩ :=
  odd_advance (k := 8192) block175 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block177 : Valid 2899975 ⟨210105, 2899943, 12, -238⟩ :=
  odd_advance (k := 8192) block176 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block178 : Valid 2916359 ⟨211204, 2916343, 6, -249⟩ :=
  odd_advance (k := 8192) block177 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block179 : Valid 2932743 ⟨212304, 2932711, 8, -234⟩ :=
  odd_advance (k := 8192) block178 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block180 : Valid 2949127 ⟨213389, 2949119, 6, -232⟩ :=
  odd_advance (k := 8192) block179 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block181 : Valid 2965511 ⟨214491, 2965499, 16, -237⟩ :=
  odd_advance (k := 8192) block180 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block182 : Valid 2981895 ⟨215593, 2981887, 14, -237⟩ :=
  odd_advance (k := 8192) block181 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block183 : Valid 2998279 ⟨216702, 2998253, 10, -222⟩ :=
  odd_advance (k := 8192) block182 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block184 : Valid 3014663 ⟨217807, 3014659, 6, -220⟩ :=
  odd_advance (k := 8192) block183 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block185 : Valid 3031047 ⟨218882, 3031043, 12, -218⟩ :=
  odd_advance (k := 8192) block184 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block186 : Valid 3047431 ⟨219972, 3047423, 4, -196⟩ :=
  odd_advance (k := 8192) block185 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block187 : Valid 3063815 ⟨221050, 3063803, 4, -185⟩ :=
  odd_advance (k := 8192) block186 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block188 : Valid 3080199 ⟨222164, 3080167, 8, -180⟩ :=
  odd_advance (k := 8192) block187 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block189 : Valid 3096583 ⟨223283, 3096571, 18, -205⟩ :=
  odd_advance (k := 8192) block188 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block190 : Valid 3112967 ⟨224357, 3112943, 10, -200⟩ :=
  odd_advance (k := 8192) block189 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block191 : Valid 3129351 ⟨225463, 3129323, 34, -188⟩ :=
  odd_advance (k := 8192) block190 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block192 : Valid 3145735 ⟨226548, 3145721, 10, -194⟩ :=
  odd_advance (k := 8192) block191 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block193 : Valid 3162119 ⟨227640, 3162101, 34, -189⟩ :=
  odd_advance (k := 8192) block192 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block194 : Valid 3178503 ⟨228754, 3178499, 10, -164⟩ :=
  odd_advance (k := 8192) block193 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block195 : Valid 3194887 ⟨229861, 3194881, 2, -165⟩ :=
  odd_advance (k := 8192) block194 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block196 : Valid 3211271 ⟨230983, 3211213, 6, -144⟩ :=
  odd_advance (k := 8192) block195 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block197 : Valid 3227655 ⟨232076, 3227641, 2, -166⟩ :=
  odd_advance (k := 8192) block196 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block198 : Valid 3244039 ⟨233181, 3244013, 4, -198⟩ :=
  odd_advance (k := 8192) block197 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block199 : Valid 3260423 ⟨234274, 3260417, 10, -196⟩ :=
  odd_advance (k := 8192) block198 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block200 : Valid 3276807 ⟨235370, 3276803, 4, -203⟩ :=
  odd_advance (k := 8192) block199 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block201 : Valid 3293191 ⟨236465, 3293183, 6, -180⟩ :=
  odd_advance (k := 8192) block200 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block202 : Valid 3309575 ⟨237544, 3309571, 8, -168⟩ :=
  odd_advance (k := 8192) block201 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block203 : Valid 3325959 ⟨238636, 3325957, 14, -182⟩ :=
  odd_advance (k := 8192) block202 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block204 : Valid 3342343 ⟨239725, 3342341, 10, -150⟩ :=
  odd_advance (k := 8192) block203 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block205 : Valid 3358727 ⟨240777, 3358723, 20, -157⟩ :=
  odd_advance (k := 8192) block204 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block206 : Valid 3375111 ⟨241873, 3375109, 26, -141⟩ :=
  odd_advance (k := 8192) block205 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block207 : Valid 3391495 ⟨242977, 3391489, 12, -177⟩ :=
  odd_advance (k := 8192) block206 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block208 : Valid 3407879 ⟨244068, 3407857, 6, -186⟩ :=
  odd_advance (k := 8192) block207 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block209 : Valid 3424263 ⟨245167, 3424261, 12, -185⟩ :=
  odd_advance (k := 8192) block208 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block210 : Valid 3440647 ⟨246281, 3440627, 6, -165⟩ :=
  odd_advance (k := 8192) block209 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block211 : Valid 3457031 ⟨247364, 3457019, 12, -141⟩ :=
  odd_advance (k := 8192) block210 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block212 : Valid 3473415 ⟨248428, 3473399, 16, -144⟩ :=
  odd_advance (k := 8192) block211 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block213 : Valid 3489799 ⟨249467, 3489793, 12, -132⟩ :=
  odd_advance (k := 8192) block212 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block214 : Valid 3506183 ⟨250562, 3506179, 8, -132⟩ :=
  odd_advance (k := 8192) block213 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block215 : Valid 3522567 ⟨251627, 3522559, 8, -147⟩ :=
  odd_advance (k := 8192) block214 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block216 : Valid 3538951 ⟨252687, 3538949, 16, -125⟩ :=
  odd_advance (k := 8192) block215 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block217 : Valid 3555335 ⟨253763, 3555311, 42, -113⟩ :=
  odd_advance (k := 8192) block216 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block218 : Valid 3571719 ⟨254866, 3571699, 18, -94⟩ :=
  odd_advance (k := 8192) block217 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block219 : Valid 3588103 ⟨255943, 3588097, 20, -70⟩ :=
  odd_advance (k := 8192) block218 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block220 : Valid 3604487 ⟨257024, 3604481, 30, -25⟩ :=
  odd_advance (k := 8192) block219 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block221 : Valid 3620871 ⟨258141, 3620843, 4, -14⟩ :=
  odd_advance (k := 8192) block220 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block222 : Valid 3637255 ⟨259243, 3637223, 6, -10⟩ :=
  odd_advance (k := 8192) block221 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block223 : Valid 3653639 ⟨260284, 3653603, 4, -24⟩ :=
  odd_advance (k := 8192) block222 (by decide) (by decide) (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma block224 : Valid 3666583 ⟨261150, 3666581, 42, 1⟩ :=
  odd_advance (k := 6472) block223 (by decide) (by decide) (by decide) (by decide +kernel)

end OMA.PrimeGap

theorem OMA.solution : type_of% @OeisA92243.conjecture1 := by
  refine ⟨261150, by decide, ?_⟩
  have h : OeisA92243.a 261150 = 1 := OMA.PrimeGap.block224.2.2.2.2
  omega
