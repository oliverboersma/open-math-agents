import OMAStatements.S_oeis_a257231
-- Credit: @physbuzz. The prime-gap observation is due to Chris Boyd in OEIS A257231.
namespace OMA.R_oeis_a257231_R1
open OMA.S_oeis_a257231
/-- Gaps between consecutive primes with a perfect square strictly inside. -/
def H1 : Prop := ∀ p : ℕ, 1000003 ≤ p → p.Prime →
    (∃ k : ℕ, p < k^2 ∧ k^2 < nextPrime p) → (nextPrime p-p)^2 < nextPrime p

/-- Gaps between consecutive primes lying in one interval between successive squares. -/
def H2 : Prop := ∀ k p : ℕ, 1000003 ≤ p → p.Prime →
    k^2 ≤ p → nextPrime p ≤ (k+1)^2 → (nextPrime p-p)^2 < nextPrime p

lemma roots (p n : ℕ) (hp : p.Prime) (hn : 0 < n) (hnp : n < p) :
    (0 < n^2%p ∧ IsSquare (n^2%p)) ↔ n^2 < p ∨ (p-n)^2 < p := by
  let : Fact p.Prime := ⟨hp⟩
  have negn : ((p-n : ℕ) : ZMod p) = -(n : ZMod p) := by simp [Nat.cast_sub hnp.le]
  have congr : n^2 ≡ (p-n)^2 [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simp [Nat.cast_pow,negn]
  constructor
  · rintro ⟨_,r,hr⟩
    have hrem : n^2%p = r^2 := by simpa only [pow_two] using hr
    have bound : r^2 < p := by rw [← hrem]; exact Nat.mod_lt _ hp.pos
    have rp : r < p := by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) r]
    have e : (r : ZMod p)^2 = (n : ZMod p)^2 := by
      rw [← Nat.cast_pow,← Nat.cast_pow,ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt bound,hrem]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with h | h
    · rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt hnp] at h
      exact Or.inl (h ▸ bound)
    · rw [← negn,ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt rp,Nat.mod_eq_of_lt (by omega)] at h
      exact Or.inr (h ▸ bound)
  · rintro (direct | reflected)
    · rw [Nat.mod_eq_of_lt direct]
      exact ⟨by positivity,⟨n,pow_two n⟩⟩
    · have eq : n^2%p = (p-n)^2 := Eq.trans congr (Nat.mod_eq_of_lt reflected)
      rw [eq]
      exact ⟨pow_pos (by omega) _,⟨_,pow_two _⟩⟩


lemma prime_spec (n : ℕ) : n < nextPrime n ∧ (nextPrime n).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (n+1))

lemma prime_min (n q : ℕ) (hq : q.Prime) (hnq : n < q) : nextPrime n ≤ q :=
  Nat.find_min' (Nat.exists_infinite_primes (n+1)) ⟨hnq,hq⟩

lemma term (n : ℕ) (hn : 0 < n) :
    (0 < a n ∧ IsSquare (a n)) ↔ n^2 < nextPrime n ∨ (nextPrime n - n)^2 < nextPrime n :=
  roots _ _ (prime_spec n).2 hn (prime_spec n).1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma small_input (n : ℕ) (hn : 0 < n) (small : n < 127) :
    (0 < a n ∧ IsSquare (a n)) ↔ n ∉ ({7,23,113,114,115} : Finset ℕ) := by
  let qs : List ℕ := [
    2, 2, 3, 5, 5, 7, 7, 11, 11, 11, 11, 13, 13, 17, 17, 17,
    17, 19, 19, 23, 23, 23, 23, 29, 29, 29, 29, 29, 29, 31, 31, 37,
    37, 37, 37, 37, 37, 41, 41, 41, 41, 43, 43, 47, 47, 47, 47, 53,
    53, 53, 53, 53, 53, 59, 59, 59, 59, 59, 59, 61, 61, 67, 67, 67,
    67, 67, 67, 71, 71, 71, 71, 73, 73, 79, 79, 79, 79, 79, 79, 83,
    83, 83, 83, 89, 89, 89, 89, 89, 89, 97, 97, 97, 97, 97, 97, 97,
    97, 101, 101, 101, 101, 103, 103, 107, 107, 107, 107, 109, 109, 113, 113, 113,
    113, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127]
  have cases : ∀ i : Fin 127, 0 < i.val → let q := qs[i.val]!
      q.Prime ∧ i.val < q ∧ (∀ t : Fin (q-i.val-1), ¬ (i.val+1+t.val).Prime) ∧
      ((i.val^2 < q ∨ (q-i.val)^2 < q) ↔ i.val ∉ ({7,23,113,114,115} : Finset ℕ)) := by
    decide +kernel
  let q := qs[n]!
  obtain ⟨hp,hlt,skip,result⟩ := cases ⟨n,small⟩ hn
  change q.Prime at hp
  change n < q at hlt
  have e : nextPrime n = q := by
    apply Nat.le_antisymm (prime_min n q hp hlt)
    by_contra! bad
    have lower := (prime_spec n).1
    have bound : nextPrime n - (n+1) < q-n-1 := by omega
    have nope := skip ⟨_,bound⟩
    change ¬ (n+1+(nextPrime n-(n+1))).Prime at nope
    rw [show n+1+(nextPrime n-(n+1))=nextPrime n by omega] at nope
    exact nope (prime_spec n).2
  rw [term n hn,e]
  exact result

lemma sieve_prime (v : ℕ)
    (h : if v ≤ 1000 then v.Prime else v < 1001^2 ∧ v.Coprime (Nat.factorial 1000)) : v.Prime := by
  split at h
  · exact h
  · rename_i big
    have cut := (Nat.coprime_factorial_iff (by omega : v ≠ 1)).mp h.2
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega,?_⟩
    intro t ht hs dv
    have bound : v.sqrt < 1001 := Nat.sqrt_lt.mpr (by simpa only [pow_two] using h.1)
    have le := Nat.minFac_le_of_dvd ht dv
    omega

lemma cover (a n : ℕ) (ps : List ℕ)
    (hc : (a::ps).IsChain (fun u v => (if v ≤ 1000 then v.Prime else v < 1001^2 ∧ v.Coprime (Nat.factorial 1000)) ∧ (v-u)^2 < u))
    (start : a ≤ n) (stop : n < (a::ps).getLastD 0) :
    (nextPrime n - n)^2 < nextPrime n := by
  induction ps generalizing a with
  | nil => simp at stop; omega
  | cons b bs ih =>
    obtain ⟨⟨prime,gap⟩,rest⟩ := List.isChain_cons_cons.mp hc
    by_cases h : n < b
    · have qb := prime_min n b (sieve_prime b prime) h
      have le : nextPrime n - n ≤ b-a := by omega
      exact ((Nat.pow_le_pow_left le 2).trans_lt gap).trans_le (start.trans (prime_spec n).1.le)
    · exact ih b rest (by omega) (by simpa using stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_127 (n : ℕ) (start : 127 ≤ n) (stop : n < 1327) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    137, 139, 149, 157, 167, 179, 191, 199, 211, 223, 233, 241,
    251, 263, 277, 293, 307, 317, 331, 349, 367, 383, 401, 421,
    439, 457, 467, 487, 509, 523, 541, 563, 577, 601, 619, 643,
    661, 683, 709, 733, 757, 773, 797, 823, 839, 863, 887, 911,
    941, 971, 997, 1021, 1051, 1069, 1097, 1129, 1153, 1181, 1213, 1237,
    1259, 1291, 1321, 1327]
  exact cover 127 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_1327 (n : ℕ) (start : 1327 ≤ n) (stop : n < 4139) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    1361, 1381, 1409, 1439, 1471, 1499, 1531, 1567, 1601, 1637, 1669, 1709,
    1747, 1787, 1823, 1861, 1901, 1933, 1973, 2017, 2053, 2089, 2131, 2161,
    2207, 2251, 2297, 2341, 2389, 2437, 2477, 2521, 2557, 2593, 2633, 2683,
    2731, 2777, 2819, 2861, 2909, 2957, 3011, 3061, 3109, 3163, 3217, 3271,
    3323, 3373, 3413, 3469, 3527, 3583, 3637, 3697, 3739, 3797, 3853, 3911,
    3967, 4027, 4079, 4139]
  exact cover 1327 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_4139 (n : ℕ) (start : 4139 ≤ n) (stop : n < 8783) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    4201, 4261, 4297, 4357, 4423, 4483, 4549, 4603, 4663, 4729, 4793, 4861,
    4919, 4987, 5051, 5119, 5189, 5261, 5333, 5399, 5471, 5531, 5591, 5659,
    5717, 5791, 5867, 5939, 6011, 6079, 6151, 6229, 6301, 6379, 6451, 6529,
    6607, 6679, 6737, 6803, 6883, 6961, 7043, 7121, 7193, 7253, 7333, 7417,
    7499, 7583, 7669, 7753, 7841, 7927, 8011, 8093, 8179, 8269, 8353, 8443,
    8527, 8609, 8699, 8783]
  exact cover 4139 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_8783 (n : ℕ) (start : 8783 ≤ n) (stop : n < 15377) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    8867, 8951, 9043, 9137, 9227, 9323, 9419, 9511, 9601, 9697, 9791, 9887,
    9973, 10069, 10169, 10267, 10357, 10457, 10559, 10657, 10753, 10853, 10957, 11059,
    11161, 11261, 11353, 11447, 11551, 11657, 11743, 11839, 11941, 12049, 12157, 12263,
    12373, 12479, 12589, 12697, 12809, 12919, 13009, 13121, 13229, 13339, 13451, 13553,
    13669, 13781, 13883, 13999, 14107, 14221, 14327, 14437, 14557, 14669, 14783, 14897,
    15017, 15139, 15259, 15377]
  exact cover 8783 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_15377 (n : ℕ) (start : 15377 ≤ n) (stop : n < 23761) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    15497, 15619, 15739, 15859, 15973, 16097, 16223, 16349, 16453, 16573, 16699, 16823,
    16943, 17053, 17183, 17299, 17419, 17539, 17669, 17791, 17923, 18049, 18181, 18313,
    18443, 18553, 18679, 18803, 18919, 19051, 19183, 19319, 19457, 19583, 19717, 19853,
    19993, 20129, 20269, 20411, 20551, 20693, 20809, 20947, 21089, 21227, 21347, 21493,
    21617, 21757, 21893, 22039, 22171, 22307, 22453, 22573, 22721, 22871, 23021, 23167,
    23311, 23459, 23609, 23761]
  exact cover 15377 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_23761 (n : ℕ) (start : 23761 ≤ n) (stop : n < 34039) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    23911, 24061, 24203, 24337, 24481, 24631, 24781, 24923, 25073, 25229, 25373, 25523,
    25679, 25819, 25969, 26119, 26267, 26423, 26573, 26731, 26893, 27043, 27197, 27361,
    27509, 27673, 27827, 27983, 28123, 28289, 28447, 28607, 28771, 28933, 29101, 29269,
    29437, 29599, 29761, 29927, 30097, 30269, 30431, 30593, 30763, 30937, 31091, 31267,
    31397, 31573, 31741, 31907, 32083, 32261, 32429, 32609, 32789, 32969, 33149, 33331,
    33503, 33679, 33857, 34039]
  exact cover 23761 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_34039 (n : ℕ) (start : 34039 ≤ n) (stop : n < 46237) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    34217, 34381, 34549, 34729, 34913, 35099, 35281, 35461, 35617, 35803, 35983, 36161,
    36343, 36529, 36713, 36901, 37087, 37277, 37463, 37649, 37831, 38011, 38201, 38393,
    38569, 38749, 38933, 39119, 39313, 39511, 39709, 39901, 40099, 40289, 40487, 40639,
    40829, 41023, 41221, 41413, 41611, 41813, 42017, 42221, 42409, 42611, 42797, 43003,
    43207, 43411, 43613, 43801, 43997, 44203, 44389, 44587, 44797, 45007, 45197, 45403,
    45613, 45823, 46027, 46237]
  exact cover 34039 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_46237 (n : ℕ) (start : 46237 ≤ n) (stop : n < 60449) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    46451, 46663, 46877, 47093, 47309, 47521, 47737, 47951, 48163, 48371, 48589, 48809,
    49019, 49223, 49433, 49639, 49853, 50069, 50291, 50513, 50723, 50929, 51151, 51361,
    51581, 51803, 52027, 52253, 52457, 52673, 52901, 53129, 53359, 53569, 53791, 54013,
    54217, 54449, 54679, 54907, 55127, 55351, 55579, 55813, 56041, 56269, 56503, 56737,
    56963, 57193, 57427, 57653, 57881, 58111, 58337, 58573, 58789, 59029, 59263, 59497,
    59729, 59971, 60209, 60449]
  exact cover 46237 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_60449 (n : ℕ) (start : 60449 ≤ n) (stop : n < 76537) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    60689, 60923, 61169, 61409, 61651, 61879, 62119, 62351, 62597, 62827, 63073, 63317,
    63559, 63809, 64037, 64283, 64513, 64763, 65011, 65257, 65497, 65731, 65983, 66239,
    66491, 66739, 66977, 67231, 67489, 67741, 67993, 68239, 68491, 68749, 69011, 69263,
    69499, 69761, 70019, 70271, 70529, 70793, 71059, 71317, 71569, 71821, 72077, 72341,
    72577, 72823, 73091, 73361, 73613, 73883, 74149, 74419, 74687, 74959, 75227, 75479,
    75743, 76003, 76261, 76537]
  exact cover 60449 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_76537 (n : ℕ) (start : 76537 ≤ n) (stop : n < 94727) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    76801, 77069, 77339, 77617, 77893, 78167, 78439, 78713, 78989, 79259, 79537, 79817,
    80077, 80347, 80629, 80911, 81181, 81463, 81737, 82021, 82307, 82591, 82847, 83117,
    83401, 83689, 83969, 84247, 84533, 84811, 85093, 85381, 85669, 85933, 86209, 86501,
    86783, 87071, 87359, 87649, 87943, 88237, 88523, 88819, 89113, 89399, 89689, 89983,
    90281, 90547, 90847, 91141, 91433, 91733, 92033, 92333, 92627, 92927, 93229, 93529,
    93827, 94121, 94427, 94727]
  exact cover 76537 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_94727 (n : ℕ) (start : 94727 ≤ n) (stop : n < 114889) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    95027, 95327, 95633, 95929, 96233, 96527, 96827, 97127, 97429, 97729, 98041, 98347,
    98641, 98953, 99259, 99571, 99881, 100193, 100501, 100811, 101119, 101429, 101747, 102061,
    102367, 102679, 102983, 103291, 103591, 103903, 104207, 104527, 104849, 105167, 105491, 105769,
    106087, 106411, 106727, 107053, 107377, 107699, 108023, 108347, 108649, 108971, 109297, 109621,
    109943, 110273, 110603, 110933, 111263, 111593, 111919, 112253, 112583, 112913, 113233, 113567,
    113903, 114229, 114553, 114889]
  exact cover 94727 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_114889 (n : ℕ) (start : 114889 ≤ n) (stop : n < 136999) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    115223, 115561, 115891, 116201, 116539, 116867, 117203, 117541, 117883, 118219, 118549, 118891,
    119233, 119569, 119891, 120233, 120577, 120919, 121259, 121607, 121951, 122299, 122611, 122957,
    123307, 123653, 124001, 124351, 124703, 125053, 125399, 125753, 126107, 126461, 126781, 127133,
    127487, 127843, 128189, 128521, 128879, 129229, 129587, 129937, 130279, 130639, 130987, 131321,
    131671, 132019, 132371, 132721, 133073, 133417, 133781, 134129, 134489, 134851, 135211, 135571,
    135937, 136303, 136657, 136999]
  exact cover 114889 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_136999 (n : ℕ) (start : 136999 ≤ n) (stop : n < 161149) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    137369, 137737, 138107, 138469, 138841, 139201, 139571, 139943, 140317, 140689, 141061, 141413,
    141773, 142123, 142469, 142841, 143197, 143573, 143947, 144323, 144701, 145069, 145441, 145819,
    146197, 146563, 146941, 147319, 147689, 148073, 148457, 148829, 149213, 149579, 149953, 150329,
    150707, 151091, 151477, 151849, 152231, 152617, 153001, 153379, 153763, 154153, 154543, 154933,
    155317, 155707, 156089, 156467, 156841, 157231, 157627, 158017, 158407, 158803, 159199, 159589,
    159979, 160373, 160757, 161149]
  exact cover 136999 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_161149 (n : ℕ) (start : 161149 ≤ n) (stop : n < 187081) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    161543, 161923, 162293, 162691, 163063, 163433, 163819, 164209, 164599, 165001, 165397, 165799,
    166189, 166571, 166979, 167381, 167779, 168151, 168559, 168943, 169343, 169753, 170141, 170551,
    170957, 171341, 171733, 172147, 172561, 172973, 173359, 173773, 174169, 174583, 174991, 175403,
    175811, 176227, 176641, 177043, 177433, 177841, 178261, 178681, 179099, 179519, 179939, 180361,
    180779, 181201, 181619, 182041, 182467, 182893, 183319, 183713, 184133, 184559, 184969, 185371,
    185797, 186227, 186653, 187081]
  exact cover 161149 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_187081 (n : ℕ) (start : 187081 ≤ n) (stop : n < 215197) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    187513, 187931, 188359, 188791, 189223, 189653, 190063, 190471, 190901, 191299, 191717, 192149,
    192587, 193013, 193451, 193883, 194323, 194749, 195163, 195599, 196039, 196477, 196919, 197359,
    197803, 198241, 198673, 199109, 199523, 199967, 200407, 200843, 201287, 201731, 202129, 202577,
    203023, 203461, 203911, 204361, 204803, 205253, 205703, 206153, 206603, 207041, 207491, 207941,
    208393, 208843, 209299, 209743, 210193, 210643, 211097, 211543, 211997, 212453, 212909, 213361,
    213821, 214283, 214741, 215197]
  exact cover 187081 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_215197 (n : ℕ) (start : 215197 ≤ n) (stop : n < 245279) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    215659, 216119, 216577, 217033, 217489, 217937, 218401, 218857, 219313, 219767, 220217, 220681,
    221101, 221567, 222029, 222499, 222967, 223439, 223903, 224363, 224831, 225299, 225769, 226241,
    226697, 227167, 227629, 228103, 228577, 229037, 229507, 229981, 230453, 230933, 231409, 231877,
    232357, 232823, 233297, 233777, 234259, 234743, 235211, 235679, 236153, 236627, 237091, 237571,
    238039, 238519, 238991, 239461, 239947, 240433, 240913, 241393, 241883, 242371, 242863, 243343,
    243829, 244313, 244787, 245279]
  exact cover 215197 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_245279 (n : ℕ) (start : 245279 ≤ n) (stop : n < 277373) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    245771, 246251, 246739, 247229, 247717, 248203, 248701, 249199, 249677, 250169, 250643, 251143,
    251639, 252139, 252641, 253133, 253633, 254119, 254623, 255127, 255617, 256121, 256609, 257107,
    257611, 258113, 258617, 259123, 259631, 260137, 260647, 261127, 261637, 262147, 262657, 263167,
    263677, 264179, 264659, 265169, 265621, 266129, 266641, 267143, 267649, 268153, 268661, 269179,
    269683, 270191, 270709, 271217, 271729, 272249, 272761, 273283, 273803, 274301, 274817, 275339,
    275837, 276359, 276883, 277373]
  exact cover 245279 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_277373 (n : ℕ) (start : 277373 ≤ n) (stop : n < 311473) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    277897, 278413, 278917, 279443, 279967, 280487, 280997, 281527, 282053, 282577, 283099, 283631,
    284161, 284689, 285221, 285749, 286249, 286777, 287297, 287821, 288349, 288877, 289397, 289897,
    290429, 290963, 291491, 292027, 292561, 293099, 293639, 294179, 294703, 295237, 295777, 296299,
    296843, 297377, 297911, 298451, 298993, 299539, 300073, 300593, 301141, 301681, 302227, 302767,
    303313, 303859, 304393, 304943, 305489, 306041, 306589, 307129, 307669, 308219, 308773, 309317,
    309857, 310397, 310949, 311473]
  exact cover 277373 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_311473 (n : ℕ) (start : 311473 ≤ n) (stop : n < 347591) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    312031, 312589, 313147, 313699, 314257, 314813, 315373, 315907, 316469, 317029, 317591, 318137,
    318701, 319259, 319819, 320377, 320941, 321469, 322013, 322573, 323137, 323699, 324251, 324811,
    325379, 325943, 326503, 327071, 327629, 328177, 328721, 329293, 329863, 330433, 330997, 331553,
    332117, 332687, 333253, 333821, 334393, 334963, 335539, 336113, 336689, 337261, 337837, 338413,
    338993, 339557, 340129, 340709, 341287, 341863, 342421, 342989, 343561, 344117, 344693, 345271,
    345853, 346441, 347003, 347591]
  exact cover 311473 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_347591 (n : ℕ) (start : 347591 ≤ n) (stop : n < 385663) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    348163, 348739, 349313, 349903, 350459, 351047, 351599, 352181, 352771, 353359, 353939, 354533,
    355127, 355721, 356311, 356893, 357473, 358069, 358667, 359263, 359851, 360439, 361033, 361577,
    362177, 362759, 363361, 363959, 364543, 365137, 365699, 366293, 366889, 367469, 368059, 368653,
    369253, 369851, 370451, 371057, 371663, 372271, 372881, 373489, 374093, 374701, 375311, 375923,
    376531, 377137, 377749, 378361, 378967, 379579, 380189, 380803, 381419, 382021, 382631, 383221,
    383839, 384437, 385057, 385663]
  exact cover 347591 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_385663 (n : ℕ) (start : 385663 ≤ n) (stop : n < 425641) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    386279, 386891, 387509, 388117, 388727, 389303, 389923, 390539, 391163, 391757, 392363, 392983,
    393593, 394211, 394837, 395459, 396079, 396703, 397303, 397921, 398549, 399173, 399793, 400417,
    401039, 401671, 402299, 402923, 403553, 404177, 404783, 405413, 406037, 406673, 407299, 407923,
    408553, 409187, 409823, 410461, 411101, 411739, 412343, 412967, 413597, 414221, 414857, 415489,
    416107, 416719, 417337, 417983, 418603, 419249, 419893, 420521, 421163, 421807, 422453, 423097,
    423727, 424351, 424997, 425641]
  exact cover 385663 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_425641 (n : ℕ) (start : 425641 ≤ n) (stop : n < 467749) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    426287, 426931, 427579, 428231, 428873, 429521, 430147, 430799, 431449, 432097, 432749, 433399,
    434039, 434689, 435343, 435997, 436651, 437293, 437953, 438611, 439273, 439919, 440581, 441229,
    441887, 442537, 443189, 443851, 444517, 445183, 445847, 446503, 447137, 447793, 448451, 449117,
    449783, 450451, 451109, 451771, 452443, 453107, 453757, 454417, 455053, 455717, 456377, 457049,
    457711, 458377, 459047, 459703, 460379, 461053, 461717, 462377, 463033, 463711, 464383, 465061,
    465739, 466409, 467083, 467749]
  exact cover 425641 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_467749 (n : ℕ) (start : 467749 ≤ n) (stop : n < 511897) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    468421, 469099, 469769, 470453, 471137, 471817, 472477, 473159, 473839, 474503, 475169, 475841,
    476519, 477209, 477899, 478589, 479267, 479957, 480647, 481307, 481997, 482689, 483377, 484067,
    484751, 485447, 486139, 486833, 487507, 488203, 488897, 489571, 490267, 490967, 491653, 492319,
    493013, 493711, 494413, 495113, 495799, 496499, 497197, 497899, 498599, 499283, 499979, 500677,
    501383, 502087, 502787, 503483, 504187, 504893, 505601, 506291, 506999, 507697, 508393, 509101,
    509801, 510481, 511193, 511897]
  exact cover 467749 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_511897 (n : ℕ) (start : 511897 ≤ n) (stop : n < 557927) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    512609, 513319, 514021, 514733, 515429, 516127, 516839, 517553, 518261, 518953, 519667, 520381,
    521063, 521777, 522497, 523219, 523937, 524633, 525353, 526073, 526781, 527489, 528197, 528911,
    529637, 530359, 531079, 531799, 532523, 533249, 533971, 534697, 535399, 536111, 536839, 537569,
    538301, 539009, 539743, 540469, 541201, 541927, 542603, 543313, 544031, 544759, 545497, 546233,
    546967, 547681, 548417, 549149, 549883, 550621, 551363, 552103, 552841, 553583, 554317, 555053,
    555767, 556487, 557201, 557927]
  exact cover 511897 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_557927 (n : ℕ) (start : 557927 ≤ n) (stop : n < 606037) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    558661, 559397, 560137, 560873, 561607, 562351, 563099, 563837, 564533, 565283, 566023, 566767,
    567499, 568241, 568991, 569731, 570467, 571211, 571939, 572687, 573437, 574183, 574939, 575693,
    576439, 577193, 577939, 578693, 579451, 580201, 580939, 581701, 582457, 583213, 583969, 584723,
    585467, 586213, 586973, 587737, 588503, 589243, 589997, 590753, 591509, 592261, 593029, 593783,
    594551, 595319, 596083, 596851, 597613, 598379, 599149, 599899, 600673, 601439, 602201, 602977,
    603749, 604517, 605261, 606037]
  exact cover 557927 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_606037 (n : ℕ) (start : 606037 ≤ n) (stop : n < 656153) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    606811, 607583, 608359, 609113, 609887, 610667, 611441, 612217, 612977, 613759, 614531, 615313,
    616079, 616849, 617587, 618361, 619139, 619921, 620693, 621473, 622249, 623023, 623803, 624577,
    625367, 626147, 626929, 627709, 628499, 629281, 630067, 630841, 631619, 632393, 633187, 633967,
    634759, 635533, 636319, 637097, 637883, 638669, 639451, 640249, 640993, 641791, 642581, 643373,
    644173, 644951, 645751, 646549, 647341, 648133, 648937, 649739, 650543, 651347, 652153, 652957,
    653761, 654553, 655357, 656153]
  exact cover 606037 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_656153 (n : ℕ) (start : 656153 ≤ n) (stop : n < 708293) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    656959, 657743, 658549, 659353, 660157, 660949, 661741, 662551, 663359, 664151, 664949, 665761,
    666559, 667367, 668179, 668989, 669791, 670597, 671401, 672209, 673019, 673837, 674647, 675463,
    676279, 677081, 677891, 678659, 679463, 680263, 681067, 681883, 682699, 683513, 684337, 685141,
    685963, 686789, 687593, 688411, 689237, 690059, 690889, 691709, 692539, 693359, 694189, 695021,
    695843, 696659, 697481, 698311, 699133, 699967, 700801, 701629, 702451, 703277, 704111, 704947,
    705781, 706621, 707459, 708293]
  exact cover 656153 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_708293 (n : ℕ) (start : 708293 ≤ n) (stop : n < 762491) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    709123, 709963, 710791, 711629, 712447, 713287, 714113, 714949, 715789, 716633, 717463, 718303,
    719149, 719989, 720829, 721663, 722509, 723353, 724187, 725009, 725827, 726659, 727501, 728333,
    729173, 730021, 730867, 731719, 732541, 733393, 734233, 735083, 735937, 736793, 737641, 738499,
    739351, 740191, 741043, 741883, 742723, 743579, 744431, 745273, 746129, 746989, 747853, 748717,
    749557, 750419, 751277, 752137, 753001, 753859, 754723, 755569, 756433, 757297, 758159, 759029,
    759893, 760759, 761623, 762491]
  exact cover 708293 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_762491 (n : ℕ) (start : 762491 ≤ n) (stop : n < 818621) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    763349, 764209, 765059, 765931, 766793, 767647, 768503, 769357, 770233, 771109, 771973, 772847,
    773723, 774601, 775477, 776357, 777221, 778097, 778979, 779837, 780719, 781601, 782473, 783337,
    784219, 785101, 785963, 786833, 787711, 788569, 789443, 790331, 791209, 792073, 792959, 793843,
    794711, 795601, 796487, 797359, 798251, 799103, 799993, 800879, 801761, 802651, 803519, 804409,
    805297, 806177, 807071, 807949, 808837, 809729, 810587, 811469, 812363, 813251, 814139, 815033,
    815933, 816821, 817723, 818621]
  exact cover 762491 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_818621 (n : ℕ) (start : 818621 ≤ n) (stop : n < 876677) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    819523, 820427, 821329, 822233, 823129, 824029, 824933, 825829, 826729, 827633, 828523, 829399,
    830309, 831217, 832123, 833033, 833933, 834829, 835739, 836623, 837533, 838447, 839353, 840269,
    841157, 842071, 842987, 843901, 844777, 845683, 846589, 847507, 848423, 849311, 850229, 851131,
    852037, 852959, 853873, 854771, 855683, 856571, 857471, 858373, 859297, 860143, 861059, 861979,
    862907, 863833, 864757, 865681, 866581, 867511, 868423, 869339, 870271, 871181, 872107, 873017,
    873913, 874847, 875779, 876677]
  exact cover 818621 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_876677 (n : ℕ) (start : 876677 ≤ n) (stop : n < 936739) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    877609, 878539, 879457, 880367, 881273, 882199, 883121, 884057, 884987, 885923, 886859, 887759,
    888691, 889631, 890563, 891493, 892433, 893363, 894301, 895243, 896167, 897103, 898033, 898951,
    899893, 900821, 901751, 902687, 903613, 904559, 905507, 906431, 907369, 908321, 909253, 910201,
    911147, 912089, 913039, 913981, 914897, 915851, 916787, 917737, 918683, 919631, 920561, 921517,
    922463, 923411, 924361, 925307, 926251, 927191, 928153, 929113, 930073, 931013, 931967, 932927,
    933883, 934837, 935791, 936739]
  exact cover 876677 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_936739 (n : ℕ) (start : 936739 ≤ n) (stop : n < 998969) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    937693, 938659, 939623, 940573, 941537, 942479, 943429, 944399, 945367, 946331, 947299, 948263,
    949213, 950179, 951151, 952123, 953093, 954067, 955039, 956003, 956953, 957917, 958883, 959831,
    960809, 961789, 962747, 963719, 964697, 965677, 966659, 967627, 968593, 969569, 970549, 971521,
    972493, 973459, 974443, 975427, 976411, 977369, 978349, 979337, 980321, 981311, 982301, 983267,
    984253, 985219, 986207, 987199, 988157, 989123, 990053, 991043, 992023, 993011, 993997, 994991,
    995987, 996979, 997973, 998969]
  exact cover 936739 n ps (by decide +kernel) start (by exact stop)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma cover_998969 (n : ℕ) (start : 998969 ≤ n) (stop : n < 1000003) :
    (nextPrime n - n)^2 < nextPrime n := by
  let ps : List ℕ := [
    999961, 1000003]
  exact cover 998969 n ps (by decide +kernel) start (by exact stop)

lemma finite_gap (n : ℕ) (start : 127 ≤ n) (stop : n < 1000003) :
    (nextPrime n - n)^2 < nextPrime n := by
  by_cases h1327 : n < 1327
  · exact cover_127 n (by omega) h1327
  by_cases h4139 : n < 4139
  · exact cover_1327 n (by omega) h4139
  by_cases h8783 : n < 8783
  · exact cover_4139 n (by omega) h8783
  by_cases h15377 : n < 15377
  · exact cover_8783 n (by omega) h15377
  by_cases h23761 : n < 23761
  · exact cover_15377 n (by omega) h23761
  by_cases h34039 : n < 34039
  · exact cover_23761 n (by omega) h34039
  by_cases h46237 : n < 46237
  · exact cover_34039 n (by omega) h46237
  by_cases h60449 : n < 60449
  · exact cover_46237 n (by omega) h60449
  by_cases h76537 : n < 76537
  · exact cover_60449 n (by omega) h76537
  by_cases h94727 : n < 94727
  · exact cover_76537 n (by omega) h94727
  by_cases h114889 : n < 114889
  · exact cover_94727 n (by omega) h114889
  by_cases h136999 : n < 136999
  · exact cover_114889 n (by omega) h136999
  by_cases h161149 : n < 161149
  · exact cover_136999 n (by omega) h161149
  by_cases h187081 : n < 187081
  · exact cover_161149 n (by omega) h187081
  by_cases h215197 : n < 215197
  · exact cover_187081 n (by omega) h215197
  by_cases h245279 : n < 245279
  · exact cover_215197 n (by omega) h245279
  by_cases h277373 : n < 277373
  · exact cover_245279 n (by omega) h277373
  by_cases h311473 : n < 311473
  · exact cover_277373 n (by omega) h311473
  by_cases h347591 : n < 347591
  · exact cover_311473 n (by omega) h347591
  by_cases h385663 : n < 385663
  · exact cover_347591 n (by omega) h385663
  by_cases h425641 : n < 425641
  · exact cover_385663 n (by omega) h425641
  by_cases h467749 : n < 467749
  · exact cover_425641 n (by omega) h467749
  by_cases h511897 : n < 511897
  · exact cover_467749 n (by omega) h511897
  by_cases h557927 : n < 557927
  · exact cover_511897 n (by omega) h557927
  by_cases h606037 : n < 606037
  · exact cover_557927 n (by omega) h606037
  by_cases h656153 : n < 656153
  · exact cover_606037 n (by omega) h656153
  by_cases h708293 : n < 708293
  · exact cover_656153 n (by omega) h708293
  by_cases h762491 : n < 762491
  · exact cover_708293 n (by omega) h762491
  by_cases h818621 : n < 818621
  · exact cover_762491 n (by omega) h818621
  by_cases h876677 : n < 876677
  · exact cover_818621 n (by omega) h876677
  by_cases h936739 : n < 936739
  · exact cover_876677 n (by omega) h936739
  by_cases h998969 : n < 998969
  · exact cover_936739 n (by omega) h998969
  exact cover_998969 n (by omega) stop

/-- At a prime input, a positive square is equivalent to the gap bound. -/
lemma at_prime (p : ℕ) (hp : p.Prime) :
    (0 < a p ∧ IsSquare (a p)) ↔ (nextPrime p-p)^2 < nextPrime p := by
  rw [term p hp.pos]
  obtain ⟨q,hq,above,below⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have lim := (prime_min p q hq above).trans below
  have large : 2*p ≤ p^2 := by have h := hp.two_le; nlinarith [Nat.mul_le_mul_right p h]
  exact or_iff_right (by omega)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a257231.main := by
  intro across inside n hn
  by_cases small : n < 127
  · exact small_input n hn small
  have good : (nextPrime n-n)^2 < nextPrime n := by
    by_cases finite : n < 1000003
    · exact finite_gap n (by omega) finite
    let p := Nat.findGreatest Nat.Prime n
    have base : Nat.Prime 1000003 := sieve_prime _ (by decide +kernel)
    have big : 1000003 ≤ p := Nat.le_findGreatest (by omega) base
    have hp : p.Prime := Nat.findGreatest_spec (by omega : 1000003 ≤ n) base
    have pn : p ≤ n := Nat.findGreatest_le _
    have nq : n < nextPrime p := by
      by_contra! h
      have bound : nextPrime p ≤ p := Nat.le_findGreatest h (prime_spec p).2
      have lower := (prime_spec p).1
      omega
    have e : nextPrime n = nextPrime p :=
      Nat.le_antisymm (prime_min n _ (prime_spec p).2 nq)
        (prime_min p _ (prime_spec n).2 (pn.trans_lt (prime_spec n).1))
    have gap : (nextPrime p-p)^2 < nextPrime p := by
      by_cases cross : ∃ k : ℕ, p < k^2 ∧ k^2 < nextPrime p
      · exact across p big hp cross
      apply inside p.sqrt p big hp
      · simpa only [pow_two] using Nat.sqrt_le p
      · by_contra! h
        exact cross ⟨p.sqrt+1,by simpa only [pow_two] using Nat.lt_succ_sqrt p,h⟩
    rw [e]
    exact (Nat.pow_le_pow_left (Nat.sub_le_sub_left pn _) 2).trans_lt gap
  have sq := (term n hn).mpr (Or.inr good)
  refine ⟨fun _ => ?_,fun _ => sq⟩
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

end OMA.R_oeis_a257231_R1
