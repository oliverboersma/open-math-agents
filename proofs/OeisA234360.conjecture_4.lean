import FormalConjectures.OEIS.«234360»

/-!
# Disproof of `OeisA234360.conjecture_4`

We refute `OeisA234360.conjecture_4` using the explicit counterexample `n = 3998 > 3`:
there do not exist `0 < k < 3998` and a prime `p` such that
`(p + 1) ^ 2 = k ^ 2 * (k + 1) ^ (3998 - k).totient`.

All finite checks are verified inside the Lean 4 kernel by pure `rfl` without `native_decide`:
1. `k ∈ {3996, 3997}` fail because `Nat.totient 1 = Nat.totient 2 = 1` and `63 ^ 2 < 3997 < 3998 < 64 ^ 2`.
2. For `1 ≤ k ≤ 3995`, `3998 - k ≥ 3` has even totient `2 * m_k` (certified by `fastTotient`),
   forcing `p = k * (k + 1) ^ m_k - 1`.
3. 3,755 cases are eliminated by an explicit proper divisor `q_k ∣ p` checked via modular
   exponentiation and capped-growth lower bounds.
4. The remaining 240 cases are eliminated by Fermat's Little Theorem base 2 (`2 ^ (p - 1) % p ≠ 1`)
   using 8-bit windowed, 64-bit chunked GMP modular exponentiation with strict chunk forcing.
-/

namespace OeisA234360Disproof

/- ### Section 1: Certified Euler totient on [1, 3997] -/

def findOddFacAux (d : Nat) : Nat → Nat → Nat
  | 0, _ => d
  | fuel + 1, f =>
    if f * f > d then d
    else if d % f == 0 then f
    else findOddFacAux d fuel (f + 2)

def findFac (d : Nat) : Nat :=
  if d % 2 == 0 then 2 else findOddFacAux d 32 3

def fastTotAux : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, d =>
    if d ≤ 1 then 1
    else
      let p := findFac d
      let q := d / p
      if q % p == 0 then p * fastTotAux fuel q
      else (p - 1) * fastTotAux fuel q

def fastTotient (d : Nat) : Nat := fastTotAux 13 d

private lemma prime_of_no_small_dvd (n B : Nat) (hn : 2 ≤ n)
    (hB : n < B * B) (hno : ∀ g, 2 ≤ g → g < B → ¬ (g ∣ n)) : Nat.Prime n := by
  by_contra hnp
  have hne1 : n ≠ 1 := by omega
  have hmf_prime : Nat.Prime n.minFac := Nat.minFac_prime hne1
  have hmf_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hmf_ge2 : 2 ≤ n.minFac := hmf_prime.two_le
  have hmf_sq : n.minFac * n.minFac ≤ n := by
    have := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    simpa [sq] using this
  have hmf_lt : n.minFac < B := by nlinarith
  exact hno n.minFac hmf_ge2 hmf_lt hmf_dvd

private lemma findOddFacAux_spec (d : Nat) (hd2 : 2 ≤ d) (hdodd : d % 2 = 1) :
    ∀ fuel f, f % 2 = 1 → 3 ≤ f →
      (∀ g, 2 ≤ g → g < f → ¬ (g ∣ d)) →
      d < (f + 2 * fuel) * (f + 2 * fuel) →
      Nat.Prime (findOddFacAux d fuel f) ∧ findOddFacAux d fuel f ∣ d
  | 0, f, _, _, hno, hlt => by
    unfold findOddFacAux
    have hff : d < f * f := by simpa using hlt
    exact ⟨prime_of_no_small_dvd d f hd2 hff hno, dvd_refl d⟩
  | fuel + 1, f, hfodd, hf3, hno, hlt => by
    unfold findOddFacAux
    by_cases hstop : f * f > d
    · rw [if_pos hstop]
      exact ⟨prime_of_no_small_dvd d f hd2 hstop hno, dvd_refl d⟩
    · rw [if_neg hstop]
      by_cases hdvd : d % f == 0
      · rw [if_pos hdvd]
        have hfdvd : f ∣ d := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hdvd)
        have hfprime : Nat.Prime f := by
          refine prime_of_no_small_dvd f f (by omega) (by nlinarith) ?_
          intro g hg2 hgf hgf_dvd
          exact hno g hg2 hgf (dvd_trans hgf_dvd hfdvd)
        exact ⟨hfprime, hfdvd⟩
      · rw [if_neg hdvd]
        have hnotf : ¬ (f ∣ d) := by
          intro h
          have : (d % f == 0) = true := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd h)
          exact hdvd this
        have hnotf1 : ¬ (f + 1 ∣ d) := by
          rintro ⟨q, hq⟩
          have hev : (f + 1) % 2 = 0 := by omega
          have : d % 2 = 0 := by
            rw [hq, Nat.mul_mod, hev]; simp
          omega
        have hno' : ∀ g, 2 ≤ g → g < f + 2 → ¬ (g ∣ d) := by
          intro g hg2 hglt
          by_cases hltf : g < f
          · exact hno g hg2 hltf
          · by_cases heq : g = f
            · subst heq; exact hnotf
            · have heq1 : g = f + 1 := by omega
              subst heq1; exact hnotf1
        have hlt' : d < (f + 2 + 2 * fuel) * (f + 2 + 2 * fuel) := by
          have : f + 2 + 2 * fuel = f + 2 * (fuel + 1) := by ring
          rwa [this]
        exact findOddFacAux_spec d hd2 hdodd fuel (f + 2) (by omega) (by omega) hno' hlt'

private lemma findFac_spec (d : Nat) (hd2 : 2 ≤ d) (hdle : d ≤ 3997) :
    Nat.Prime (findFac d) ∧ findFac d ∣ d := by
  unfold findFac
  by_cases hev : (d % 2 == 0) = true
  · rw [if_pos hev]
    exact ⟨Nat.prime_two, Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hev)⟩
  · rw [if_neg hev]
    have hodd : d % 2 = 1 := by
      have : d % 2 ≠ 0 := fun h => hev (beq_iff_eq.mpr h)
      omega
    have hno3 : ∀ g, 2 ≤ g → g < 3 → ¬ (g ∣ d) := by
      intro g hg2 hg3 hgd
      have hg : g = 2 := by omega
      subst hg
      have := Nat.mod_eq_zero_of_dvd hgd
      omega
    exact findOddFacAux_spec d hd2 hodd 32 3 (by omega) (by omega) hno3 (by omega)

private lemma fastTotAux_eq :
    ∀ fuel d, 1 ≤ d → d ≤ 3997 → d < 2 ^ fuel → fastTotAux fuel d = Nat.totient d
  | 0, d, hd1, _, hlt => by
    simp at hlt; omega
  | fuel + 1, d, hd1, hdle, hlt => by
    unfold fastTotAux
    by_cases hdle1 : d ≤ 1
    · rw [if_pos hdle1]
      have hdeq : d = 1 := by omega
      subst hdeq; rfl
    · rw [if_neg hdle1]
      have hd2 : 2 ≤ d := by omega
      rcases findFac_spec d hd2 hdle with ⟨hp, hpdvd⟩
      set p := findFac d
      set q := d / p
      have hp2 : 2 ≤ p := hp.two_le
      have hpq : p * q = d := Nat.mul_div_cancel' hpdvd
      have hq1 : 1 ≤ q := by nlinarith
      have hq_le : q ≤ 3997 := by
        have : q ≤ d := Nat.div_le_self d p
        omega
      have hq_lt : q < 2 ^ fuel := by
        have h2q : 2 * q ≤ d := by nlinarith
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      have hih : fastTotAux fuel q = Nat.totient q := fastTotAux_eq fuel q hq1 hq_le hq_lt
      by_cases hqp : (q % p == 0) = true
      · rw [if_pos hqp, hih]
        have hdvd_q : p ∣ q := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hqp)
        rw [← hpq, Nat.totient_mul_of_prime_of_dvd hp hdvd_q]
      · rw [if_neg hqp, hih]
        have hndvd : ¬ (p ∣ q) := by
          intro h
          exact hqp (beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd h))
        have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hndvd
        rw [← hpq, Nat.totient_mul hcop, Nat.totient_prime hp]

private lemma fastTotient_eq (d : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 3997) :
    fastTotient d = Nat.totient d := by
  unfold fastTotient
  exact fastTotAux_eq 13 d hd1 hd (by omega)

/- ### Section 2: Modular-divisor verifier and soundness -/

def powModAux : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, acc, _, _, _ => acc
  | fuel + 1, acc, b, e, q =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then (acc * b) % q else acc
      powModAux fuel acc' ((b * b) % q) (e / 2) q

def capPowAux : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, acc, _, _, _ => acc
  | fuel + 1, acc, b, e, cap =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then min (acc * b) cap else acc
      capPowAux fuel acc' (min (b * b) cap) (e / 2) cap

def divCheck (k q : Nat) : Bool :=
  let m := fastTotient (3998 - k) / 2
  q ≥ 2 &&
    ((k % q) * powModAux 12 1 ((k + 1) % q) m q) % q == 1 &&
    min (k * capPowAux 12 1 (k + 1) m (q + 2)) (q + 2) == q + 2

private lemma powModAux_eq (q : Nat) :
    ∀ fuel acc b e, e < 2 ^ fuel →
      powModAux fuel acc b e q % q = (acc * b ^ e) % q
  | 0, acc, b, e, he => by
    have he0 : e = 0 := by simp at he; omega
    subst he0; simp [powModAux]
  | fuel + 1, acc, b, e, he => by
    unfold powModAux
    by_cases he0 : (e == 0) = true
    · rw [if_pos he0]
      have h0 : e = 0 := beq_iff_eq.mp he0
      subst h0; simp
    · rw [if_neg he0]
      have hdiv : e / 2 < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      rw [powModAux_eq q fuel _ _ (e / 2) hdiv]
      have hsq : ((b * b) % q) ^ (e / 2) % q = (b ^ (2 * (e / 2))) % q := by
        rw [← Nat.pow_mod, show b * b = b ^ 2 by ring, ← pow_mul]
      by_cases hodd : (e % 2 == 1) = true
      · rw [if_pos hodd]
        have he1 : e % 2 = 1 := beq_iff_eq.mp hodd
        have heeq : 2 * (e / 2) + 1 = e := by omega
        calc (((acc * b) % q) * ((b * b) % q) ^ (e / 2)) % q
            = (((acc * b) % q) % q * (((b * b) % q) ^ (e / 2) % q)) % q := by
                rw [Nat.mul_mod]
          _ = (((acc * b) % q) * (b ^ (2 * (e / 2)) % q)) % q := by
                rw [Nat.mod_mod, hsq]
          _ = (acc * b * b ^ (2 * (e / 2))) % q := by
                rw [← Nat.mul_mod]
          _ = (acc * b ^ e) % q := by
                rw [mul_assoc, ← pow_succ', heeq]
      · rw [if_neg hodd]
        have he0' : e % 2 = 0 := by
          have : e % 2 ≠ 1 := fun h => hodd (beq_iff_eq.mpr h)
          omega
        have heeq : 2 * (e / 2) = e := by omega
        calc (acc * ((b * b) % q) ^ (e / 2)) % q
            = (acc % q * (((b * b) % q) ^ (e / 2) % q)) % q := by
                rw [Nat.mul_mod]
          _ = (acc % q * (b ^ (2 * (e / 2)) % q)) % q := by
                rw [hsq]
          _ = (acc * b ^ (2 * (e / 2))) % q := by
                rw [← Nat.mul_mod]
          _ = (acc * b ^ e) % q := by
                rw [heeq]

private lemma capPowAux_le (cap : Nat) :
    ∀ fuel acc b e, 1 ≤ b → capPowAux fuel acc b e cap ≤ acc * b ^ e
  | 0, acc, b, e, hb => by
    unfold capPowAux
    have h1 : 1 ≤ b ^ e := Nat.one_le_pow e b (by omega)
    calc acc = acc * 1 := (mul_one acc).symm
      _ ≤ acc * b ^ e := Nat.mul_le_mul_left acc h1
  | fuel + 1, acc, b, e, hb => by
    unfold capPowAux
    by_cases he0 : (e == 0) = true
    · rw [if_pos he0]
      have h0 : e = 0 := beq_iff_eq.mp he0
      subst h0; simp
    · rw [if_neg he0]
      have hbb_le : min (b * b) cap ≤ b * b := Nat.min_le_left _ _
      by_cases hcap0 : cap = 0
      · subst hcap0
        have hzero : ∀ f a bb ee, capPowAux f a bb ee 0 ≤ a := by
          intro f
          induction f with
          | zero => intro a bb ee; simp [capPowAux]
          | succ f ih =>
            intro a bb ee
            unfold capPowAux
            split_ifs
            · exact le_refl a
            · exact le_trans (ih _ _ _) (by simp)
            · exact ih _ _ _
        have h1 : 1 ≤ b ^ e := Nat.one_le_pow e b (by omega)
        by_cases hodd : (e % 2 == 1) = true
        · rw [if_pos hodd]
          dsimp only
          have hle0 := hzero fuel (min (acc * b) 0) (min (b * b) 0) (e / 2)
          rw [Nat.min_zero] at hle0 ⊢
          exact le_trans hle0 (Nat.zero_le _)
        · rw [if_neg hodd]
          calc capPowAux fuel acc (min (b * b) 0) (e / 2) 0
              ≤ acc := hzero fuel acc _ (e / 2)
            _ = acc * 1 := (mul_one acc).symm
            _ ≤ acc * b ^ e := Nat.mul_le_mul_left acc h1
      · have hbb_ge1 : 1 ≤ min (b * b) cap := by
          have h1 : 1 ≤ b * b := by nlinarith
          omega
        have hpow_le : (min (b * b) cap) ^ (e / 2) ≤ b ^ (2 * (e / 2)) := by
          calc (min (b * b) cap) ^ (e / 2)
              ≤ (b * b) ^ (e / 2) := Nat.pow_le_pow_left hbb_le _
            _ = (b ^ 2) ^ (e / 2) := by rw [sq]
            _ = b ^ (2 * (e / 2)) := (pow_mul b 2 _).symm
        by_cases hodd : (e % 2 == 1) = true
        · rw [if_pos hodd]
          have he1 : e % 2 = 1 := beq_iff_eq.mp hodd
          have heeq : 2 * (e / 2) + 1 = e := by omega
          calc capPowAux fuel (min (acc * b) cap) (min (b * b) cap) (e / 2) cap
              ≤ min (acc * b) cap * (min (b * b) cap) ^ (e / 2) :=
                capPowAux_le cap fuel (min (acc * b) cap) (min (b * b) cap) (e / 2) hbb_ge1
            _ ≤ (acc * b) * b ^ (2 * (e / 2)) :=
                Nat.mul_le_mul (Nat.min_le_left _ _) hpow_le
            _ = acc * b ^ e := by rw [mul_assoc, ← pow_succ', heeq]
        · rw [if_neg hodd]
          have he0' : e % 2 = 0 := by
            have : e % 2 ≠ 1 := fun h => hodd (beq_iff_eq.mpr h)
            omega
          have heeq : 2 * (e / 2) = e := by omega
          calc capPowAux fuel acc (min (b * b) cap) (e / 2) cap
              ≤ acc * (min (b * b) cap) ^ (e / 2) :=
                capPowAux_le cap fuel acc (min (b * b) cap) (e / 2) hbb_ge1
            _ ≤ acc * b ^ (2 * (e / 2)) := Nat.mul_le_mul_left acc hpow_le
            _ = acc * b ^ e := by rw [heeq]

private lemma not_prime_of_divCheck (k q : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 3995)
    (hcheck : divCheck k q = true) :
    ¬ Nat.Prime (k * (k + 1) ^ ((3998 - k).totient / 2) - 1) := by
  dsimp only [divCheck] at hcheck
  have htot : fastTotient (3998 - k) = (3998 - k).totient :=
    fastTotient_eq (3998 - k) (by omega) (by omega)
  rw [htot] at hcheck
  set m := (3998 - k).totient / 2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
  rcases hcheck with ⟨⟨hq2, hmod⟩, hgrow⟩
  have hm_lt : m < 2 ^ 12 := by
    have hle : (3998 - k).totient ≤ 3998 - k := Nat.totient_le (3998 - k)
    omega
  have hpm : powModAux 12 1 ((k + 1) % q) m q % q = ((k + 1) ^ m) % q := by
    rw [powModAux_eq q 12 1 ((k + 1) % q) m hm_lt, one_mul, ← Nat.pow_mod]
  have hNmod : (k * (k + 1) ^ m) % q = 1 := by
    calc (k * (k + 1) ^ m) % q
        = ((k % q) * ((k + 1) ^ m % q)) % q := Nat.mul_mod _ _ _
      _ = ((k % q) * (powModAux 12 1 ((k + 1) % q) m q % q)) % q := by rw [hpm]
      _ = ((k % q % q) * (powModAux 12 1 ((k + 1) % q) m q % q)) % q := by rw [Nat.mod_mod]
      _ = ((k % q) * powModAux 12 1 ((k + 1) % q) m q) % q := (Nat.mul_mod _ _ _).symm
      _ = 1 := hmod
  have hcap_le : q + 2 ≤ k * (k + 1) ^ m := by
    have h1 : q + 2 ≤ k * capPowAux 12 1 (k + 1) m (q + 2) := by
      have := Nat.min_le_left (k * capPowAux 12 1 (k + 1) m (q + 2)) (q + 2)
      omega
    have h2 : capPowAux 12 1 (k + 1) m (q + 2) ≤ 1 * (k + 1) ^ m :=
      capPowAux_le (q + 2) 12 1 (k + 1) m (by omega)
    rw [one_mul] at h2
    exact le_trans h1 (Nat.mul_le_mul_left k h2)
  have hq_lt : q < k * (k + 1) ^ m - 1 := by omega
  have hq_dvd : q ∣ k * (k + 1) ^ m - 1 := by
    have hdiv := Nat.div_add_mod (k * (k + 1) ^ m) q
    rw [hNmod] at hdiv
    refine ⟨(k * (k + 1) ^ m) / q, ?_⟩
    omega
  intro hp
  rcases hp.eq_one_or_self_of_dvd q hq_dvd with h1 | hself
  · omega
  · omega

/- ### Section 3: Strict 8-bit windowed GMP Fermat base-2 verifier and soundness -/

def powMulAux : Nat → Nat → Nat → Nat → Nat
  | 0, acc, _, _ => acc
  | fuel + 1, acc, b, e =>
    if e == 0 then acc
    else
      let acc' := if e % 2 == 1 then acc * b else acc
      powMulAux fuel acc' (b * b) (e / 2)

def powNat (b e : Nat) : Nat := powMulAux 15 1 b e

def splitChunksAux (base : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, e, acc =>
    if e == 0 then acc
    else splitChunksAux base fuel (e / base) ((e % base) :: acc)

def pow2Win8 (acc n w : Nat) : Nat :=
  let a1 := (acc * acc) % n
  let a2 := (a1 * a1) % n
  let a3 := (a2 * a2) % n
  let a4 := (a3 * a3) % n
  let a5 := (a4 * a4) % n
  let a6 := (a5 * a5) % n
  let a7 := (a6 * a6) % n
  let a8 := (a7 * a7) % n
  (a8 * (2 ^ w)) % n

def pow2Chunk64 (acc n c : Nat) : Nat :=
  let a0 := pow2Win8 acc n (c / 72057594037927936)
  let c1 := c % 72057594037927936
  let a1 := pow2Win8 a0 n (c1 / 281474976710656)
  let c2 := c1 % 281474976710656
  let a2 := pow2Win8 a1 n (c2 / 1099511627776)
  let c3 := c2 % 1099511627776
  let a3 := pow2Win8 a2 n (c3 / 4294967296)
  let c4 := c3 % 4294967296
  let a4 := pow2Win8 a3 n (c4 / 16777216)
  let c5 := c4 % 16777216
  let a5 := pow2Win8 a4 n (c5 / 65536)
  let c6 := c5 % 65536
  let a6 := pow2Win8 a5 n (c6 / 256)
  pow2Win8 a6 n (c6 % 256)

def pow2ModChunks64 (n : Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | c :: cs, acc =>
    let acc' := pow2Chunk64 acc n c
    if acc' == 0 then 0 else pow2ModChunks64 n cs acc'

def fermat2Fail (k : Nat) : Bool :=
  let m := fastTotient (3998 - k) / 2
  let n := k * powNat (k + 1) m - 1
  let chunks := splitChunksAux 18446744073709551616 375 (n - 1) []
  n ≥ 3 && (pow2ModChunks64 n chunks 1 % n != 1)

private lemma powMulAux_eq :
    ∀ fuel acc b e, e < 2 ^ fuel → powMulAux fuel acc b e = acc * b ^ e
  | 0, acc, b, e, he => by
    have he0 : e = 0 := by simp at he; omega
    subst he0; simp [powMulAux]
  | fuel + 1, acc, b, e, he => by
    unfold powMulAux
    by_cases he0 : (e == 0) = true
    · rw [if_pos he0]
      have h0 : e = 0 := beq_iff_eq.mp he0
      subst h0; simp
    · rw [if_neg he0]
      have hdiv : e / 2 < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      rw [powMulAux_eq fuel _ (b * b) (e / 2) hdiv]
      have hsq : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
        rw [show b * b = b ^ 2 by ring, ← pow_mul]
      by_cases hodd : (e % 2 == 1) = true
      · rw [if_pos hodd, hsq]
        have he1 : e % 2 = 1 := beq_iff_eq.mp hodd
        have heeq : 2 * (e / 2) + 1 = e := by omega
        rw [mul_assoc, ← pow_succ', heeq]
      · rw [if_neg hodd, hsq]
        have he0' : e % 2 = 0 := by
          have : e % 2 ≠ 1 := fun h => hodd (beq_iff_eq.mpr h)
          omega
        have heeq : 2 * (e / 2) = e := by omega
        rw [heeq]

private lemma powNat_eq (b e : Nat) (he : e < 2 ^ 15) : powNat b e = b ^ e := by
  unfold powNat
  rw [powMulAux_eq 15 1 b e he, one_mul]

private def evalChunks (base : Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => evalChunks base cs (acc * base + c)

private lemma evalChunks_acc (base : Nat) :
    ∀ cs x, evalChunks base cs x = x * base ^ cs.length + evalChunks base cs 0
  | [], x => by simp [evalChunks]
  | c :: cs, x => by
    simp only [evalChunks, List.length_cons, zero_mul, zero_add]
    rw [evalChunks_acc base cs (x * base + c), evalChunks_acc base cs c]
    have hpow : base ^ (cs.length + 1) = base * base ^ cs.length := by
      rw [pow_succ, mul_comm]
    rw [hpow]
    ring

private lemma splitChunksAux_eval (base : Nat) (hbase : 2 ≤ base) :
    ∀ fuel e acc, e < base ^ fuel →
      evalChunks base (splitChunksAux base fuel e acc) 0 =
        e * base ^ acc.length + evalChunks base acc 0
  | 0, e, acc, he => by
    have he0 : e = 0 := by simp at he; omega
    subst he0; simp [splitChunksAux]
  | fuel + 1, e, acc, he => by
    unfold splitChunksAux
    by_cases he0 : (e == 0) = true
    · rw [if_pos he0]
      have h0 : e = 0 := beq_iff_eq.mp he0
      subst h0; simp
    · rw [if_neg he0]
      have hdiv_lt : e / base < base ^ fuel := by
        have hpow : base ^ (fuel + 1) = base * base ^ fuel := by
          rw [pow_succ, mul_comm]
        rw [hpow] at he
        exact Nat.div_lt_of_lt_mul he
      rw [splitChunksAux_eval base hbase fuel (e / base) ((e % base) :: acc) hdiv_lt]
      simp only [List.length_cons, evalChunks, zero_mul, zero_add]
      rw [evalChunks_acc base acc (e % base)]
      have hpow : base ^ (acc.length + 1) = base * base ^ acc.length := by
        rw [pow_succ, mul_comm]
      have hdm : base * (e / base) + e % base = e := Nat.div_add_mod e base
      rw [hpow]
      calc e / base * (base * base ^ acc.length) + (e % base * base ^ acc.length + evalChunks base acc 0)
          = (base * (e / base) + e % base) * base ^ acc.length + evalChunks base acc 0 := by ring
        _ = e * base ^ acc.length + evalChunks base acc 0 := by rw [hdm]

private lemma sq_mod_step (a b k n : Nat) (h : a % n = b ^ k % n) :
    ((a * a) % n) % n = b ^ (2 * k) % n := by
  rw [Nat.mod_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← pow_add, show k + k = 2 * k by ring]

private lemma pow2Win8_mod (acc n w : Nat) :
    pow2Win8 acc n w % n = (acc ^ 256 * 2 ^ w) % n := by
  dsimp only [pow2Win8]
  have h0 : acc % n = acc ^ 1 % n := by simp
  have h1 := sq_mod_step _ acc 1 n h0
  have h2 := sq_mod_step _ acc 2 n h1
  have h3 := sq_mod_step _ acc 4 n h2
  have h4 := sq_mod_step _ acc 8 n h3
  have h5 := sq_mod_step _ acc 16 n h4
  have h6 := sq_mod_step _ acc 32 n h5
  have h7 := sq_mod_step _ acc 64 n h6
  have h8 := sq_mod_step _ acc 128 n h7
  rw [Nat.mod_mod, Nat.mul_mod, h8, ← Nat.mul_mod]

private lemma pow2Win8_compose (a acc A E w n : Nat)
    (h : a % n = (acc ^ A * 2 ^ E) % n) :
    pow2Win8 a n w % n = (acc ^ (A * 256) * 2 ^ (E * 256 + w)) % n := by
  rw [pow2Win8_mod]
  calc (a ^ 256 * 2 ^ w) % n
      = ((a ^ 256 % n) * (2 ^ w % n)) % n := Nat.mul_mod _ _ _
    _ = (((a % n) ^ 256 % n) * (2 ^ w % n)) % n := by rw [Nat.pow_mod]
    _ = ((((acc ^ A * 2 ^ E) % n) ^ 256 % n) * (2 ^ w % n)) % n := by rw [h]
    _ = (((acc ^ A * 2 ^ E) ^ 256 % n) * (2 ^ w % n)) % n := by rw [← Nat.pow_mod]
    _ = ((acc ^ A * 2 ^ E) ^ 256 * 2 ^ w) % n := (Nat.mul_mod _ _ _).symm
    _ = (acc ^ (A * 256) * 2 ^ (E * 256 + w)) % n := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]

private lemma pow2Chunk64_mod (acc n c : Nat) :
    pow2Chunk64 acc n c % n = (acc ^ (2 ^ 64) * 2 ^ c) % n := by
  dsimp only [pow2Chunk64]
  have h0 : acc % n = (acc ^ 1 * 2 ^ 0) % n := by simp
  have h1 := pow2Win8_compose _ acc 1 0 (c / 72057594037927936) n h0
  have h2 := pow2Win8_compose _ acc _ _ (c % 72057594037927936 / 281474976710656) n h1
  have h3 := pow2Win8_compose _ acc _ _ (c % 72057594037927936 % 281474976710656 / 1099511627776) n h2
  have h4 := pow2Win8_compose _ acc _ _ (c % 72057594037927936 % 281474976710656 % 1099511627776 / 4294967296) n h3
  have h5 := pow2Win8_compose _ acc _ _ (c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 / 16777216) n h4
  have h6 := pow2Win8_compose _ acc _ _ (c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 % 16777216 / 65536) n h5
  have h7 := pow2Win8_compose _ acc _ _ (c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 % 16777216 % 65536 / 256) n h6
  have h8 := pow2Win8_compose _ acc _ _ (c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 % 16777216 % 65536 % 256) n h7
  rw [h8]
  have hexpA : 1 * 256 * 256 * 256 * 256 * 256 * 256 * 256 * 256 = 2 ^ 64 := by decide
  have hexpE :
      (((((((0 * 256 + c / 72057594037927936) * 256 +
        c % 72057594037927936 / 281474976710656) * 256 +
        c % 72057594037927936 % 281474976710656 / 1099511627776) * 256 +
        c % 72057594037927936 % 281474976710656 % 1099511627776 / 4294967296) * 256 +
        c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 / 16777216) * 256 +
        c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 % 16777216 / 65536) * 256 +
        c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 % 16777216 % 65536 / 256) * 256 +
        c % 72057594037927936 % 281474976710656 % 1099511627776 % 4294967296 % 16777216 % 65536 % 256 = c := by
    omega
  rw [hexpA, hexpE]

private lemma pow2ModChunks64_mod (n : Nat) :
    ∀ cs acc e, acc % n = 2 ^ e % n →
      pow2ModChunks64 n cs acc % n = 2 ^ (evalChunks (2 ^ 64) cs e) % n
  | [], acc, e, hacc => by simpa [pow2ModChunks64, evalChunks] using hacc
  | c :: cs, acc, e, hacc => by
    unfold pow2ModChunks64
    have hstep : pow2Chunk64 acc n c % n = 2 ^ (e * 2 ^ 64 + c) % n := by
      rw [pow2Chunk64_mod]
      calc (acc ^ (2 ^ 64) * 2 ^ c) % n
          = ((acc ^ (2 ^ 64) % n) * (2 ^ c % n)) % n := Nat.mul_mod _ _ _
        _ = (((acc % n) ^ (2 ^ 64) % n) * (2 ^ c % n)) % n := by rw [Nat.pow_mod]
        _ = (((2 ^ e % n) ^ (2 ^ 64) % n) * (2 ^ c % n)) % n := by rw [hacc]
        _ = (((2 ^ e) ^ (2 ^ 64) % n) * (2 ^ c % n)) % n := by rw [← Nat.pow_mod]
        _ = ((2 ^ e) ^ (2 ^ 64) * 2 ^ c) % n := (Nat.mul_mod _ _ _).symm
        _ = 2 ^ (e * 2 ^ 64 + c) % n := by rw [← pow_mul, ← pow_add]
    by_cases h0 : (pow2Chunk64 acc n c == 0) = true
    · rw [if_pos h0]
      have hzero : pow2Chunk64 acc n c = 0 := beq_iff_eq.mp h0
      rw [hzero, Nat.zero_mod] at hstep
      simp only [evalChunks]
      rw [evalChunks_acc (2 ^ 64) cs (e * 2 ^ 64 + c)]
      have hpow_pos : 1 ≤ (2 ^ 64) ^ cs.length := Nat.one_le_pow _ _ (by positivity)
      have h2zero : (2 ^ (e * 2 ^ 64 + c)) ^ ((2 ^ 64) ^ cs.length) % n = 0 := by
        rw [Nat.pow_mod, ← hstep, zero_pow (by omega), Nat.zero_mod]
      rw [pow_add, pow_mul, Nat.mul_mod, h2zero, zero_mul, Nat.zero_mod]
    · rw [if_neg h0]
      exact pow2ModChunks64_mod n cs (pow2Chunk64 acc n c) (e * 2 ^ 64 + c) hstep

private lemma not_prime_of_fermat2_fail (n : Nat) (hn3 : 3 ≤ n)
    (hfail : 2 ^ (n - 1) % n ≠ 1) : ¬ n.Prime := by
  intro hp
  have : Fact n.Prime := ⟨hp⟩
  have h2ne : ((2 : Nat) : ZMod n) ≠ 0 := by
    intro h0
    have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp h0
    have hle : n ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hflt : ((2 : Nat) : ZMod n) ^ (n - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hcast : ((2 ^ (n - 1) : Nat) : ZMod n) = ((1 : Nat) : ZMod n) := by
    simpa using hflt
  have hmodeq : 2 ^ (n - 1) ≡ 1 [MOD n] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hmod : 2 ^ (n - 1) % n = 1 % n := hmodeq
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hmod
  exact hfail hmod

private lemma not_prime_of_fermat2Fail (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 3995)
    (hcheck : fermat2Fail k = true) :
    ¬ Nat.Prime (k * (k + 1) ^ ((3998 - k).totient / 2) - 1) := by
  dsimp only [fermat2Fail] at hcheck
  have htot : fastTotient (3998 - k) = (3998 - k).totient :=
    fastTotient_eq (3998 - k) (by omega) (by omega)
  rw [htot] at hcheck
  set m := (3998 - k).totient / 2
  have hm_le : m ≤ 1998 := by
    have hle : (3998 - k).totient ≤ 3998 - k := Nat.totient_le (3998 - k)
    omega
  have hm_lt : m < 2 ^ 15 := by omega
  rw [powNat_eq (k + 1) m hm_lt] at hcheck
  set n := k * (k + 1) ^ m - 1
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hcheck
  rcases hcheck with ⟨hn3, hne1⟩
  have hbase_eq : (18446744073709551616 : Nat) = 2 ^ 64 := by decide
  rw [hbase_eq] at hne1
  have hn_lt : n - 1 < (2 ^ 64) ^ 375 := by
    have hk_lt : k < 2 ^ 12 := by omega
    have hk1_lt : k + 1 < 2 ^ 12 := by omega
    have hpow_le : (k + 1) ^ m ≤ (2 ^ 12) ^ 1998 :=
      le_trans (Nat.pow_le_pow_left (Nat.le_of_lt hk1_lt) m)
        (Nat.pow_le_pow_right (Nat.two_pow_pos 12) hm_le)
    have hprod : k * (k + 1) ^ m < 2 ^ 12 * (2 ^ 12) ^ 1998 := by
      calc k * (k + 1) ^ m < 2 ^ 12 * (k + 1) ^ m := Nat.mul_lt_mul_of_pos_right hk_lt (by positivity)
        _ ≤ 2 ^ 12 * (2 ^ 12) ^ 1998 := Nat.mul_le_mul_left _ hpow_le
    have hexp_le : 2 ^ 12 * (2 ^ 12) ^ 1998 ≤ (2 ^ 64) ^ 375 := by
      rw [← pow_mul, ← pow_add, ← pow_mul]
      exact Nat.pow_le_pow_right Nat.zero_lt_two (by decide)
    have hn_lt_prod : n - 1 < k * (k + 1) ^ m := by
      have hpos : 0 < k * (k + 1) ^ m := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
      dsimp [n]; omega
    exact lt_of_lt_of_le (lt_trans hn_lt_prod hprod) hexp_le
  have heval := splitChunksAux_eval (2 ^ 64) (by decide) 375 (n - 1) [] hn_lt
  simp only [List.length_nil, pow_zero, mul_one, evalChunks, add_zero] at heval
  have hmod := pow2ModChunks64_mod n (splitChunksAux (2 ^ 64) 375 (n - 1) []) 1 0 (by simp)
  rw [heval] at hmod
  rw [hmod] at hne1
  exact not_prime_of_fermat2_fail n hn3 hne1

/- ### Section 4: Certificate data (all defs grouped before parallel theorems) -/

def fermatBucket_0 : List Nat := [
  609, 2469, 2279, 1278, 2544, 2903, 3755, 3917
]

def fermatBucket_1 : List Nat := [
  459, 420, 1494, 1668, 3105, 3240, 3759
]

def fermatBucket_2 : List Nat := [
  439, 612, 1164, 1638, 200, 3651, 3170, 3794
]

def fermatBucket_3 : List Nat := [
  367, 516, 132, 452, 1244, 2778, 3038
]

def fermatBucket_4 : List Nat := [
  789, 773, 1050, 740, 3201, 2348, 3110, 3618
]

def fermatBucket_5 : List Nat := [
  811, 1649, 984, 842, 2819, 38, 2918, 3903
]

def fermatBucket_6 : List Nat := [
  339, 2163, 462, 284, 1878, 3483, 3020
]

def fermatBucket_7 : List Nat := [
  835, 1685, 654, 3135, 2352, 2762, 3288, 3656
]

def fermatBucket_8 : List Nat := [
  279, 2421, 1264, 1008, 3093, 2252, 3362
]

def fermatBucket_9 : List Nat := [
  399, 2499, 972, 3057, 3261, 2790, 3761
]

def fermatBucket_10 : List Nat := [
  681, 2349, 390, 1554, 3367, 2330, 3847
]

def fermatBucket_11 : List Nat := [
  765, 2139, 2081, 2459, 1850, 2824, 3783
]

def fermatBucket_12 : List Nat := [
  801, 2431, 1104, 2985, 1832, 3, 3332
]

def fermatBucket_13 : List Nat := [
  285, 2397, 2607, 482, 3237, 3084, 3699, 3828
]

def fermatBucket_14 : List Nat := [
  1119, 2379, 2015, 356, 2344, 3204, 3575, 3869
]

def fermatBucket_15 : List Nat := [
  195, 2361, 1144, 1980, 1904, 1754, 3684
]

def fermatBucket_16 : List Nat := [
  1005, 605, 1805, 1950, 1424, 2856, 3582
]

def fermatBucket_17 : List Nat := [
  249, 839, 2715, 2405, 2680, 1838, 2
]

def fermatBucket_18 : List Nat := [
  1305, 1803, 1283, 1512, 2334, 2628, 3380
]

def fermatBucket_19 : List Nat := [
  1327, 1109, 33, 1620, 3279, 3167, 3188
]

def fermatBucket_20 : List Nat := [
  1167, 2007, 264, 1883, 2484, 2174, 3338
]

def fermatBucket_21 : List Nat := [
  1447, 875, 1937, 1662, 2208, 2538, 3825
]

def fermatBucket_22 : List Nat := [
  1557, 305, 1925, 678, 350, 2238, 3098
]

def fermatBucket_23 : List Nat := [
  1599, 881, 2529, 2799, 2183, 2813, 3304, 3524
]

def fermatBucket_24 : List Nat := [
  159, 857, 304, 2911, 2244, 2298, 2936
]

def fermatBucket_25 : List Nat := [
  1687, 515, 784, 528, 1082, 1910, 3156, 3002
]

def fermatBucket_26 : List Nat := [
  1689, 1563, 880, 1656, 2555, 2736, 2450, 3544
]

def fermatBucket_27 : List Nat := [
  1629, 2131, 1847, 2403, 2273, 1578, 3619, 3727, 3428
]

def fermatBucket_28 : List Nat := [
  1707, 737, 1829, 2583, 138, 2909, 2072, 3713
]

def fermatBucket_29 : List Nat := [
  2011, 2121, 2505, 863, 3087, 2370, 3089, 3779
]

def fermatBucket_30 : List Nat := [
  1383, 551, 563, 720, 2032, 248, 3149, 3701
]

def fermatBucket_31 : List Nat := [
  1827, 2097, 2103, 2027, 2104, 2424, 3519, 3140
]

def fermatBuckets : List (List Nat) := [fermatBucket_0, fermatBucket_1, fermatBucket_2, fermatBucket_3, fermatBucket_4, fermatBucket_5, fermatBucket_6, fermatBucket_7, fermatBucket_8, fermatBucket_9, fermatBucket_10, fermatBucket_11, fermatBucket_12, fermatBucket_13, fermatBucket_14, fermatBucket_15, fermatBucket_16, fermatBucket_17, fermatBucket_18, fermatBucket_19, fermatBucket_20, fermatBucket_21, fermatBucket_22, fermatBucket_23, fermatBucket_24, fermatBucket_25, fermatBucket_26, fermatBucket_27, fermatBucket_28, fermatBucket_29, fermatBucket_30, fermatBucket_31]

def inFermatBuckets (k : Nat) : Bool := fermatBuckets.any (fun b => b.contains k)

def checkDivChunk : Nat → List Nat → Bool
  | _, [] => true
  | k, w :: ws =>
    (if w == 0 then inFermatBuckets k else divCheck k w) && checkDivChunk (k + 1) ws

def divChunk_0 : List Nat := [
  3, 0, 0, 3, 19, 5, 3, 7, 17, 3, 967, 64811, 3, 11, 7, 3, 41413, 17, 3, 19,
  5, 3, 11, 67, 3, 5, 73, 3, 7, 839, 13, 31, 0, 3, 17, 7, 3, 0, 19, 179,
  1723, 3023, 3, 7, 41, 3, 1773791, 71, 3, 7, 97, 3, 7, 19, 263, 5, 7, 3, 8221, 17,
  3, 23, 81649, 3, 167, 313, 5, 13, 19309, 3, 5, 17, 3, 73, 41, 3, 17, 7, 81129577, 6481,
  149, 3, 47, 49429, 3, 5, 6211, 3, 97, 8191, 15733, 7, 89, 3, 7, 13, 3, 97, 7, 3
]

def divChunk_1 : List Nat := [
  5, 43, 3, 23, 13, 3, 67, 13163, 3, 109, 5, 3, 7, 7, 3, 7, 23, 3, 347, 7,
  3, 24631, 61, 3, 29, 5, 3, 127, 113, 3, 5, 0, 3, 7, 11, 13, 17, 0, 3, 23,
  5, 3, 113, 11, 3, 5, 5, 3, 7, 53, 137, 13, 191, 3, 7, 5, 3, 11, 0, 3,
  83, 7, 3, 241817, 238789, 3, 613, 29, 3, 373, 5, 3, 467, 31, 37, 5, 11, 3, 89, 11,
  3, 103, 7, 83, 757, 5, 3, 17, 1637, 3, 11, 349, 3, 16899041, 0, 3, 7, 67, 3, 0
]

def divChunk_2 : List Nat := [
  103, 3, 491, 7, 3, 5, 80231, 3, 13, 73, 3, 47, 11, 3, 103, 5, 3, 7, 23, 3,
  7, 17, 3, 107, 7, 3, 179, 16729, 3, 1951, 17, 3, 7, 17, 3, 5, 19, 3, 7, 359,
  3, 23, 11, 3, 79, 5, 3, 0, 0, 3, 5, 55469, 3, 113, 23, 12589, 419, 19, 19, 7,
  5, 3, 929, 0, 3, 5, 7, 3, 13, 7, 135118913, 229589, 17, 3, 113, 11, 3, 40093, 0, 3,
  5, 7, 3, 0, 0, 3, 13, 7, 3, 11, 5, 3, 73, 313, 3, 5, 709, 3, 2843, 4603
]

def divChunk_3 : List Nat := [
  3, 7, 257, 0, 0, 5, 5, 230729, 7, 3, 5, 701, 3, 29, 2897, 3, 43, 43, 3, 199,
  276251, 3, 7, 311, 3, 5, 8951, 3, 31, 7, 3, 9277, 70843, 3, 43207, 23, 3, 199, 0, 3,
  5, 53, 3, 7, 43, 3, 7, 167, 3, 0, 5, 971, 17, 7, 11, 0, 89, 3, 223, 163,
  3, 137, 83, 3, 7, 5, 0, 29, 701, 3, 5, 7, 3, 23, 59, 191, 31, 13, 3, 31,
  5, 3, 359, 850177, 3, 5, 6897929, 3, 97, 0, 11, 17, 7, 3, 907, 5, 3, 1879, 0, 3
]

def divChunk_4 : List Nat := [
  5, 239, 3, 19, 141319, 3, 7, 2593, 3, 307, 5, 3, 61, 7, 173, 79, 2903, 3, 13, 0,
  3, 7, 15131, 11, 937, 5, 5, 7, 1409, 3, 5, 11, 3, 709, 7, 3, 277, 23, 0, 61,
  23, 3, 11, 461, 3, 5, 1429, 3, 7, 7, 23, 0, 179, 3, 17, 5, 3, 2663, 0, 3,
  17, 0, 3, 3583, 11, 3, 19, 3389, 3, 7, 2333, 3, 401, 11, 3, 11, 7, 3, 2089, 287919481,
  3, 0, 137, 3, 11, 5, 59, 11, 59219, 3, 5, 281, 3, 17, 13, 3, 47, 7, 1091, 3469
]

def divChunk_5 : List Nat := [
  5, 3, 13, 109, 3, 5, 5, 3, 23, 157, 3, 7, 29, 3, 0, 0, 19, 23, 7, 3,
  5, 521, 3, 127, 383, 3, 821, 0, 3, 37, 109, 3, 7, 13, 11, 5, 12589, 3, 271, 7,
  3, 11, 4211, 3, 211, 31, 3, 347, 474137, 3, 0, 5, 3, 7, 1489, 3, 773, 67, 3, 397,
  7, 3, 0, 23, 3, 5, 167, 3, 251, 271, 3, 571, 11, 3, 7, 5, 3, 577, 1861, 3,
  5, 7, 3, 857, 67, 3, 53, 71, 3, 31, 19, 3, 101, 2161, 3, 7, 17, 3, 13, 60601
]

def divChunk_6 : List Nat := [
  3, 4603, 7, 3, 0, 5, 1471, 43, 0, 3, 5, 0, 3, 23, 9544109, 3, 7, 7366379, 3, 7,
  17, 3, 307, 7, 3, 5, 5, 3, 163, 17, 3, 47, 1567333, 3, 47, 5, 3, 7, 263, 3,
  5, 412807, 3, 523, 7, 3, 19, 271, 3, 11, 379, 3, 3919, 0, 13, 5, 72341, 3, 7, 41,
  3, 349, 137, 61, 73, 5, 5, 119611, 140663, 3, 5, 43, 3, 59, 109, 3, 13, 0, 3650583691, 7,
  0, 3, 53, 839, 3, 5, 7, 3, 19, 7, 281, 69061, 653, 3, 397, 5, 3, 13, 37, 3
]

def divChunk_7 : List Nat := [
  5, 151, 3, 19, 3209, 3, 11, 7, 3, 19, 5, 3, 888773, 19, 3, 17, 23, 3, 11, 0,
  3, 7, 7, 3, 7, 5, 29, 353, 7, 3, 73, 43, 3, 608483, 53, 3, 0, 26863, 1277, 0,
  5, 3, 7, 113, 3, 5, 5, 3, 23, 7, 3, 941, 1021, 3, 570781, 151, 3, 5881, 47, 13,
  5, 281, 3, 7, 0, 3, 17, 13, 3, 3505457, 5, 3, 0, 29, 3, 79, 13, 3, 172307, 599,
  3, 6288077, 31, 0, 7, 5, 3, 7, 0, 3, 5, 7, 3, 13, 11, 3, 587, 23, 3, 17
]

def divChunk_8 : List Nat := [
  0, 3, 20483, 643, 3, 5, 17, 3, 109, 43, 0, 197, 7, 3, 11, 5, 3, 61, 113, 3,
  5, 31, 3, 83, 17191, 3, 7, 107, 3, 997, 11, 11, 13, 7, 0, 5, 19, 3, 0, 23,
  3, 0, 421, 3, 211, 5, 3, 7, 859, 3, 5, 23, 3, 13, 7, 22729481, 0, 461, 3, 95364179,
  5, 3, 0, 11, 3, 5, 227, 3, 7, 149, 3, 7, 43, 3, 0, 7, 3, 5197, 2832950551, 0,
  0, 71, 3, 13697, 67, 3, 23, 109, 3, 7, 5, 3, 29, 173, 3, 5, 7, 3, 109, 6133
]

def divChunk_9 : List Nat := [
  3, 17, 103, 3, 7, 5, 3, 257, 19, 3, 7, 1166057, 3, 179, 2333, 3, 619, 7, 37, 4789,
  5, 3, 37197833, 1487, 3, 5, 11, 3, 61027, 4349, 619, 7, 23, 3, 883, 659, 3, 31, 7, 3,
  811, 7, 3, 691, 107, 3, 23, 97, 3, 13, 5, 5, 7, 7, 3, 5, 89, 3, 69233, 7,
  3, 31, 13, 3, 241, 5, 3, 7, 3761, 3, 5, 0, 3, 7, 11, 23, 90353, 53, 26357, 19,
  7, 3, 11, 0, 3, 5, 5, 3, 7, 52147, 3, 131, 29, 3, 7, 1033, 3, 7, 234681844433, 1931
]

def divChunk_10 : List Nat := [
  5, 7, 3, 197, 0, 3, 17, 0, 3, 61, 5, 3, 23, 7321, 3, 5, 157, 3, 4799, 199,
  3, 17299, 7, 258031, 113, 7, 5, 13, 131, 3, 5, 5, 3, 277, 107, 3, 7, 17, 3, 7,
  2087, 3, 13, 7, 3, 5, 199, 3, 11, 0, 3, 7, 8693, 3, 12781, 547, 3, 7, 13, 3,
  5, 201121, 3, 532607, 7, 3, 1139557, 29, 3, 296990443, 5261, 3, 79, 29, 3, 3559, 1361, 3, 7, 48179,
  3, 0, 110603, 3, 379, 5, 3, 53, 13, 3, 5, 11, 3, 1565041, 59, 16759, 37057, 251, 3, 7
]

def divChunk_11 : List Nat := [
  5, 3, 20749, 0, 3, 5, 7, 3, 0, 131, 17, 137, 907, 3, 17681, 2797, 3, 1381, 0, 71,
  5, 7, 3, 7, 359, 3, 1361, 7, 3, 19, 5, 3, 1284823, 13, 3, 5, 20886265511, 3, 337, 56667187,
  3, 7, 17, 0, 13, 5, 5, 31, 7, 3, 5, 156749, 3, 8893, 67, 3, 7, 28961, 3, 17,
  383, 3, 7, 0, 3, 5, 0, 3, 349, 7, 3, 191, 7, 3, 151, 5, 3, 43, 283207, 3,
  5, 19, 3, 7, 83, 3, 83, 46727, 3, 154097, 5, 3, 167, 7, 11, 31, 1787, 3, 1987, 17
]

def divChunk_12 : List Nat := [
  3, 67061, 102769, 3, 7, 5, 203789, 17, 17, 3, 5, 7, 3, 23, 7, 3, 19, 569, 3, 23,
  5, 3, 13, 107, 3, 5, 521, 3, 523, 107, 23, 73, 7, 3, 953, 571, 3, 13, 63248719, 3,
  29, 17, 3, 0, 61, 3, 7, 313, 3, 79, 5, 3, 293, 7, 3, 5, 79, 3, 131, 173,
  3, 13, 3684047, 0, 19, 23, 5, 7, 587, 3, 5, 149, 3, 37, 7, 3, 47, 0, 13, 6944299,
  5, 3, 0, 13, 3, 5, 67, 3, 7, 7, 823, 7, 17, 3, 1678321, 5, 3, 641, 4903, 3
]

def divChunk_13 : List Nat := [
  5, 11, 3, 7, 0, 3, 751, 19, 3, 7, 4783, 3, 7, 13, 73, 5, 7, 3, 80207, 479,
  3, 17, 4583, 3, 331, 5, 0, 41, 14021158891, 3, 5, 11, 3, 127, 23, 89, 19, 7, 383, 389,
  5, 3, 45817, 13, 3, 5, 167, 3, 31, 1009, 17, 7, 7, 3, 7, 5, 3, 103, 7, 57493,
  5, 7, 3, 79, 37, 3, 11, 4576889, 3, 23, 5, 3, 7, 7, 3, 5, 59, 3, 13, 7,
  3, 18313, 0, 13, 1627, 5, 3, 23, 83, 3, 5, 4177, 3, 7, 17, 3, 31, 11, 3, 179
]

def divChunk_14 : List Nat := [
  5, 3, 373, 673, 3, 5, 191, 3, 7, 463, 3, 43, 3229, 3, 7, 17, 3, 13, 33617, 3,
  457, 7, 3, 0, 3313, 3, 331, 1272991, 3, 7, 5, 5, 853, 2057791, 3, 5, 2087, 3, 3733, 701,
  3, 11, 7, 3, 11, 5, 0, 47629, 881, 3, 103, 107, 3, 155181599, 11, 3, 7, 479, 285179, 3761,
  23, 3, 17, 7, 3, 5, 5, 3, 661, 13, 3, 2657, 2171203, 3, 17, 5, 3, 7, 787, 2341,
  7, 151, 3, 2617, 7, 3, 47331827, 911, 3, 23, 5, 3, 7, 0, 4397, 31, 11, 3, 7, 12713
]

def divChunk_15 : List Nat := [
  3, 59, 23, 3, 47, 5, 3, 19, 101, 3, 5, 0, 3, 89, 5851, 3, 13, 41, 3, 7,
  37, 3, 71, 54131059, 3, 5, 7, 3, 233, 7, 29, 6582461, 48590551, 3, 7, 1120081, 3, 11909, 691, 3,
  5, 35550703, 3, 10687, 719, 3, 461, 7, 3, 463, 1831, 719, 193, 0, 3, 5, 0, 3, 19, 17,
  3, 7, 0, 3, 967, 5, 3, 17, 7, 3, 5, 397, 3, 11, 79, 3, 5512627, 0, 3, 353,
  5, 3, 7, 53, 3, 5, 5, 3, 83, 7, 3, 2536057, 23, 3, 345996271, 5, 5, 20871131, 0, 3
]

def divChunk_16 : List Nat := [
  5, 13, 3, 7, 19, 3, 7, 509, 3, 137, 5, 3, 13, 7, 739, 5, 347, 3, 108541, 0,
  3, 23, 241, 167, 7, 5, 5, 31, 0, 3, 11, 7, 3, 181, 23, 3, 353, 0, 3, 11,
  17, 3, 877, 31, 3, 5, 1093, 3, 0, 359, 251, 193, 7, 3, 59, 0, 3, 937, 11783, 3,
  5, 0, 3, 19, 6203, 3, 7, 0, 3, 151, 5, 5, 11, 7, 3, 97, 179, 3, 19, 73,
  3, 31, 29, 3, 0, 5, 0, 7, 0, 3, 5, 19, 3, 233, 7, 43, 11, 43, 3, 1583
]

def divChunk_17 : List Nat := [
  5, 3, 37, 13, 3, 5, 0, 3, 7, 315421, 11, 793553, 41759, 3, 19, 7, 3, 17, 22064993, 3,
  5, 1471, 3, 79, 113, 3, 2707, 599, 3, 7, 1151, 3, 23, 311, 3, 5, 7, 3, 11, 377339,
  3, 419, 23, 3, 139, 3050263, 5, 379, 1867, 3, 5, 5, 3, 0, 3739, 3, 5003, 7, 103, 59,
  239, 3, 79, 751, 3, 5, 137, 3, 43, 2347, 3, 7, 7, 3, 1872108663071, 5, 3, 347, 7, 3,
  71, 13, 3, 52697, 11, 3, 59, 6691, 11, 13, 23, 41, 7, 941, 101, 11, 1567, 3, 199, 7
]

def divChunk_18 : List Nat := [
  3, 947, 0, 3, 0, 5, 3, 13, 157, 3, 419, 103, 3, 7, 9661, 37, 277, 193, 288767, 997201,
  7, 3, 17971, 839, 3, 5, 0, 3, 0, 31, 3, 0, 912763, 3, 7, 29, 3, 0, 281, 3,
  3391123, 7, 3, 151, 389, 3, 0, 569, 3, 0, 5, 3, 43, 17, 11, 5, 251, 3, 19889, 43,
  3, 13, 7, 3, 29, 5, 5, 13, 359, 3, 5, 3266491094561, 3, 3767, 673, 3, 7, 0, 3, 7,
  5, 3, 0, 7, 3, 5, 15139, 3, 2381, 23, 3, 212701, 11, 3, 107, 126457, 3, 7, 29, 3
]

def divChunk_19 : List Nat := [
  5, 3619507, 3, 0, 7, 3, 13, 89, 3, 0, 1099741, 3, 43, 13, 33083, 31, 23, 3, 7, 269,
  3, 17, 19, 3, 0, 5, 3, 479, 1223, 3, 5, 26981, 3, 18448571, 19, 9479, 0, 13, 3, 7,
  5, 3, 7, 565661, 3, 5, 7, 3, 19, 0, 3, 139, 369168941, 3, 1618613, 43, 3, 31, 19, 2677,
  5, 7, 3, 13, 827, 3, 223, 7, 3, 113, 3084203, 3, 739, 3162839, 3, 5, 1097, 3, 43, 0,
  3, 7, 149, 3, 31, 659, 5, 3678517, 7, 3, 25111609, 19, 3, 23, 13, 3, 7, 13, 103, 880519
]

def divChunk_20 : List Nat := [
  6079, 3, 7, 97, 3, 5, 0, 3, 139, 7, 0, 197, 1997, 3, 0, 31, 3, 103, 89, 3,
  19, 59, 3, 7, 13, 3, 0, 11, 3, 19, 5, 0, 677813, 7, 3, 5, 5457229, 3, 7, 20345293,
  3, 13, 9679, 3, 7, 5, 31, 121063, 419, 3, 5, 7, 3, 31, 13, 89, 13, 17, 3, 11519,
  5, 3, 680203, 19, 3, 5, 5, 3, 103, 1523, 3, 0, 7, 3, 17, 313, 3, 19, 6863, 3,
  0, 19, 3, 421, 401981, 3, 7, 37, 3, 883, 227, 3, 653, 7, 3, 5, 0, 3, 173, 185681
]

def divChunk_21 : List Nat := [
  3, 23, 0, 0, 557, 5, 3, 7, 17, 3, 5, 103, 3, 137, 7, 3, 76713803, 19, 67, 13,
  0, 3, 569, 23, 3, 5, 1276049, 3, 7, 7, 0, 7, 13, 3, 773, 7, 3, 31817, 0, 3,
  79, 9721, 3, 17, 23, 3, 29, 19, 478791419, 7, 11, 3, 103, 13, 3, 421, 7, 3, 13, 79,
  3, 1538311, 0, 3, 107, 5, 17, 11, 47, 3, 5, 4937, 3, 0, 146921, 157, 107, 7, 3, 421,
  97, 3, 0, 11, 3, 5, 5, 3, 28669, 223, 3, 7, 61, 3, 9932207, 5, 3, 13, 7, 3
]

def divChunk_22 : List Nat := [
  347, 7, 3, 163, 19, 3, 149, 0, 3, 64019279, 61, 3, 7, 1101058835941, 13, 23, 367, 3, 13, 7,
  3, 349471, 7, 186437, 5167, 11, 3, 7, 719, 3, 5, 5, 3, 7, 2013533, 3, 7, 0, 73, 67,
  7, 3, 19, 0, 3, 5, 11, 3, 7, 13, 29, 0, 77587, 3, 7, 5, 3, 47363, 821, 3,
  5, 7, 3, 89, 89, 3, 2176877, 61403, 3, 23, 5, 167, 0, 673, 241, 5, 19, 3, 0, 37,
  3, 3137, 7, 3, 109, 5, 3, 541, 19, 3, 5, 4603517, 3, 823, 31, 3, 7, 0, 281, 29
]

def divChunk_23 : List Nat := [
  5, 3, 2080961, 7, 3, 5, 47, 3, 557, 83, 3, 7, 17, 3, 13, 617, 3, 7, 19, 17,
  5, 103, 3, 71601259, 7, 3, 29, 73, 3, 0, 26111, 3, 57037, 0, 11, 5, 743, 3, 7, 88936577,
  3, 283, 571, 0, 10605227, 5, 3, 0, 0, 3, 5, 0, 3, 5441, 11, 3, 11, 44729, 3, 7,
  0, 3, 137, 18913, 3, 5, 7, 3, 37, 0, 11, 463, 157667, 3, 929, 2381, 3, 397, 0, 3,
  5, 7, 3, 7, 199, 3, 29, 7, 3, 409, 1531, 3, 79, 23, 3, 5, 0, 3, 11, 241
]

def divChunk_24 : List Nat := [
  3, 7, 0, 3, 0, 5, 3, 13, 7, 3, 2531, 983, 3, 907297, 2621, 3, 151, 139, 17, 19,
  0, 3, 7, 0, 3, 5, 5, 3, 1009741, 7, 0, 13, 23, 3, 9613, 3863, 3, 59009, 17, 3,
  5, 41, 3, 7, 11, 3, 7, 157, 3, 0, 5, 3, 1583, 467, 173, 5, 5936509, 3, 0, 151,
  3, 19, 11677, 3, 7, 7, 5, 11, 0, 3, 5, 7, 3, 61, 23, 3, 175519, 3559, 3, 7,
  5, 3, 17, 0, 3, 5, 23, 3, 7, 23, 3, 13, 7, 3, 4472113, 29, 3, 11, 0, 3
]

def divChunk_25 : List Nat := [
  17, 41, 3, 59, 0, 3, 7, 23740743787, 3, 13, 523, 37, 83, 7, 11, 5, 71, 3, 19, 271,
  3, 173, 6368053, 3, 13, 5, 13, 7, 0, 3, 1673279, 29, 3, 17, 7, 3, 53, 0, 43, 13,
  43, 3, 29, 0, 3, 5, 5, 3, 7, 389, 131, 4813, 19, 3, 0, 7, 3, 31, 45994001, 113,
  29, 6566407, 3, 7, 59, 3, 41, 17, 3, 7, 20100877, 3, 10137329, 257, 53, 17, 7, 3, 251, 79,
  3, 181, 0, 3, 19, 5, 3, 23, 8123, 3, 5, 281, 3, 28621, 79, 3, 131, 7, 563851, 11
]

def divChunk_26 : List Nat := [
  73, 3, 113, 1621, 3, 5, 0, 3, 16127, 11, 3, 7, 304069, 3, 7, 757, 3, 769, 7, 3,
  5, 15817, 3, 1222513, 2383, 3, 13, 0, 3, 29, 9211117, 5, 7, 375227, 3, 7, 2857, 3, 53, 7,
  3, 379, 367, 3, 1129, 5, 3, 547, 331, 3, 5, 241, 3, 7, 397, 3, 281, 57689, 3, 302971,
  7, 3, 53, 254675541464977, 3, 5, 5, 3, 7, 17, 5737, 154247, 67, 3, 7, 1523, 3, 7, 24469, 0,
  29, 7, 3, 2693, 11, 3, 11, 19, 3, 266993, 103, 3, 61, 48017, 47, 5, 37, 3, 11, 23
]

def divChunk_27 : List Nat := [
  3, 37, 7, 139, 19, 5, 5, 45281, 87313, 3, 5, 5, 3, 19, 0, 3, 7, 7, 6089, 1258469,
  431, 3, 79060427, 7, 3, 5, 53, 3, 317, 59, 3, 131, 683, 3, 173, 0, 3, 7, 773, 3,
  7, 467, 3, 13, 7, 3, 73, 7, 3, 29, 5, 3, 7, 2161, 3, 19, 13, 3, 7, 29,
  3, 0, 41, 3, 179, 5, 31189, 23, 443, 3, 5, 42719, 3, 3209, 11, 3, 1753, 0, 3, 7,
  5, 3, 13, 593, 3, 5, 7, 3, 17, 0, 3, 673, 5124754247, 3, 7, 5, 3, 13, 0, 580231
]

def divChunk_28 : List Nat := [
  5, 311, 3, 6912539, 45267359, 3, 23, 7, 3, 821, 11, 3, 0, 97, 3, 5, 11, 3, 0, 73,
  3, 7, 7, 0, 7, 5, 5, 257, 7, 3, 5, 23, 3, 1991929, 71, 3, 349, 23, 3, 17,
  5, 3, 7, 8863, 3, 5, 29, 3, 8119651, 7, 3, 367, 101, 3, 31563127, 0, 3, 107747, 1301, 3,
  23, 8193907, 3, 7, 1709, 3, 608213, 643, 3, 23, 7, 5, 17980103, 7, 31, 5, 1787, 3, 239, 709,
  3, 1783, 47, 3, 7, 5, 3, 3023, 193, 3, 5, 7, 3, 29, 53, 3, 55579, 43, 3, 13
]

def divChunk_29 : List Nat := [
  5, 3, 0, 823841, 3, 5, 5, 3, 0, 67, 0, 41, 7, 3, 773, 11, 3, 0, 11, 3,
  7, 257, 3, 29, 17, 3, 7, 17, 3, 1069, 5, 3, 19, 7, 5879, 0, 23, 3, 31, 19,
  3, 7, 199, 3, 17, 79, 5, 7, 29, 3, 5, 5, 3, 1097, 7, 3, 53, 5591, 4561, 13,
  5, 3, 317, 37, 3, 5, 311, 3, 7, 7, 3, 4591, 13, 3, 911, 5, 3, 1361, 71, 3,
  5, 1279, 3, 11, 0, 3, 71, 733, 3, 7, 5, 59, 17, 19, 3, 103, 7, 3, 1879, 23
]

def divChunk_30 : List Nat := [
  3, 0, 19, 3, 318289, 5, 2676481039, 31, 3251, 3, 5, 419, 3, 7, 3919, 113, 13, 7, 3, 0,
  5, 3, 991, 71551, 3, 2377, 5, 3, 23, 71, 11, 7, 373, 3, 2063, 5, 5, 0, 7, 7003943,
  5, 7, 3, 8957771, 193, 3, 7, 11, 3, 11, 101, 3, 7, 7, 3, 5, 0, 3, 103, 7,
  3, 307, 53, 11, 457, 5, 3, 29, 59, 3, 31, 11, 3, 7, 23, 3, 67, 17, 197, 283,
  7, 3, 100517, 0, 3, 5, 0, 3, 0, 13, 67, 11, 0, 3, 7, 5, 3, 0, 479, 3
]

def divChunk_31 : List Nat := [
  5, 7, 3, 19, 0, 3, 991, 101, 3, 0, 193, 5, 811, 1259, 5584421, 7, 41, 3, 7, 3083,
  3, 521, 7, 3, 131, 5, 3, 11, 168179471, 3, 5, 23, 3, 13, 0, 23, 7, 418459, 17, 0,
  5, 3, 11827, 7, 3, 5, 13, 3, 0, 211, 3, 239, 23, 3, 13, 0, 3, 7, 149, 6311,
  5717, 109, 3, 6197, 7, 3, 0, 29, 3, 0, 131, 3, 53, 4219, 11, 5, 336792431, 3, 7, 23,
  3, 31, 17, 3, 73, 5, 5, 0, 26423, 3, 5, 397, 3, 11, 4572679, 3, 17, 31, 3, 7
]

def divChunk_32 : List Nat := [
  0, 3, 7, 0, 3, 5, 7, 3, 181, 7, 23689, 59, 113, 3, 911, 5, 3, 7576761697, 1301, 3,
  5, 167, 3, 61, 487, 3, 13, 7, 3, 26597, 5, 19, 163, 19, 3, 733, 0, 3, 103, 0,
  3, 7, 17, 3, 7, 5, 367, 577, 7, 3, 28081667, 6761, 3, 4569811, 17, 3, 31, 36497, 41, 857,
  0, 3, 7, 7511341, 3, 5, 107, 3, 107, 7, 167, 42160578301, 7, 3, 15076931, 929, 3, 23, 0, 653,
  1831, 23, 3, 7, 79, 3, 379, 0, 3, 13567, 5, 3, 73, 7, 3, 5, 53, 3, 7, 115987
]

def divChunk_33 : List Nat := [
  3, 47, 11, 0, 7, 5, 5, 7, 89, 3, 5, 7, 3, 4621, 2213, 3, 17, 2089, 3, 7,
  13931, 3, 11, 421, 3, 5, 43, 3, 107, 19, 3, 0, 7, 3, 11339921, 23, 3, 0, 59, 3,
  5, 31, 3, 41, 569, 3, 7, 24103, 3, 131, 279329, 3, 47, 7, 41, 37, 71, 3, 359, 19,
  3, 0, 6938081, 3, 593, 5, 0, 7, 47, 3, 5, 25178053, 3, 565069, 7, 17, 103, 11, 127, 0,
  5, 3, 7, 137, 3, 5, 17, 3, 7, 47, 6282607, 7, 19, 3, 19157, 7, 3, 367, 3850254251, 3
]

def divChunk_34 : List Nat := [
  47, 13, 3, 421, 47, 3, 755767, 353, 3, 7, 307, 3, 41, 89, 3, 5, 7, 3, 41, 7,
  3, 23, 2311, 3, 7, 5, 5, 0, 59, 3, 7, 5, 3, 26813, 11, 3, 59, 7, 3, 19,
  59, 3, 1867, 31431319, 3, 5, 11, 3, 1381451, 19, 431, 7, 23, 3, 11, 120163, 3, 11, 7, 3,
  13, 83, 3, 191, 103, 3, 63533, 73, 76521223, 127, 5, 11, 7, 7, 183191443, 5, 11, 3, 4877, 7,
  3, 151, 0, 3, 23, 5, 3, 7, 29, 3, 5, 2239, 3, 7, 17, 17, 7, 337, 23, 13
]

def divChunk_35 : List Nat := [
  7, 3, 17, 29, 3, 5, 5, 3, 3659, 11, 193272613931, 5, 11, 3, 7, 5, 3, 7, 0, 1621,
  5, 7, 3, 0, 571, 3, 277, 23, 3, 23559896237, 61, 3, 52163, 787, 428349707, 5, 2381, 3, 2549, 89,
  3, 41, 7, 0, 23, 5, 3, 67, 58111, 3, 5, 557, 3, 17, 13, 3, 7, 409, 349, 1117,
  89, 3, 1759, 7, 3, 5, 4957, 3, 31531, 31, 3, 7, 23, 3, 0, 778559, 3, 7, 373, 3,
  10957, 0, 3, 47, 7, 3, 3469, 17, 3, 29, 5, 3, 179, 499, 3, 29423, 31, 3, 7, 311
]

def divChunk_36 : List Nat := [
  3, 13, 617, 3, 43, 5, 3, 2017, 83, 3, 11, 14879, 3, 7, 11, 8059, 94304237, 0, 0, 7,
  5, 3, 7, 23, 3, 5, 7, 3, 127, 7, 21943, 45971021, 2843, 3, 23, 97, 11, 439, 167, 43,
  5, 7, 3, 7, 19, 3, 173, 7, 3, 137, 0, 3, 1249, 13, 7, 0, 2273071, 3, 19, 479749,
  3, 7, 62633, 233, 293, 307, 5, 181, 7, 3, 5, 5, 3, 151, 56843, 3, 7, 19, 3, 643,
  53, 3, 7, 0, 3, 5, 383, 3, 11, 7, 11, 244479580159, 13, 3, 13, 1091, 3, 7, 0, 3
]

def divChunk_37 : List Nat := [
  0, 1378561, 3, 7, 92669, 3, 17, 41, 3, 67, 5, 3, 0, 7, 4517, 19, 540948349, 3, 11, 17837,
  3, 109, 283, 3, 7, 5, 0, 9349, 97, 3, 5, 7, 3, 13, 241, 23244427, 479263, 419, 3, 1733,
  5, 3, 613, 67, 3, 5, 5, 3, 7, 64871, 3, 11, 7, 3, 0, 73, 3, 17, 0, 3,
  0, 23, 3, 29, 11, 3, 7, 131, 3, 349, 59, 3, 41, 7, 13, 5, 89, 3, 0, 131,
  3, 19, 0, 40059919, 11, 5, 5, 7, 107, 3, 1609, 34110283, 3, 0, 7, 3, 503, 7, 17, 171403
]

def divChunk_38 : List Nat := [
  53, 3, 131, 23, 3, 5, 743, 3, 7, 7, 3, 224211223, 1399, 3, 4957, 5, 3, 146617, 59, 3,
  37, 23, 3, 7, 0, 3, 14843, 0, 3, 7, 17, 5, 7, 151, 11, 281357, 7, 3, 179, 13,
  3, 127, 199, 3, 233, 5, 0, 29, 4973, 3, 7, 61, 3, 27793, 17, 681409, 13, 7, 2791, 73,
  5, 3, 17, 83, 3, 5, 5, 3, 0, 41, 1583, 7, 11, 3, 7, 23, 4397, 109, 7, 13,
  5, 7, 3, 593, 138661, 3, 23993, 109, 3, 23, 359, 3, 7, 17, 1889, 5, 13, 3, 23, 7
]

def divChunk_39 : List Nat := [
  3, 19, 0, 1307, 23, 19, 3, 67, 59, 3, 5, 5, 3, 7, 1741, 3, 0, 15354643, 227, 11,
  7, 3, 1288697, 275963, 3, 5, 41, 3, 7, 11, 47, 37, 44111, 3, 7, 329591329, 3, 29, 103, 3,
  41, 7, 3, 12095741401, 718657, 3, 1543, 13, 7, 2860457, 61169, 11, 11, 293, 701, 7, 8761, 3, 12781, 419,
  3, 23, 7, 3, 15725191, 5, 29, 13, 23, 3, 79, 43, 3, 13, 29, 51043907, 7, 7, 1601, 4111,
  5, 3, 827, 7, 3, 11, 5, 3, 41, 8867, 7, 5, 184969, 19, 89
]

/- ### Section 5: Parallel kernel rfl verification (32 Fermat buckets + 40 Div chunks) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_0_ok : fermatBucket_0.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_1_ok : fermatBucket_1.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_2_ok : fermatBucket_2.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_3_ok : fermatBucket_3.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_4_ok : fermatBucket_4.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_5_ok : fermatBucket_5.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_6_ok : fermatBucket_6.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_7_ok : fermatBucket_7.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_8_ok : fermatBucket_8.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_9_ok : fermatBucket_9.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_10_ok : fermatBucket_10.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_11_ok : fermatBucket_11.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_12_ok : fermatBucket_12.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_13_ok : fermatBucket_13.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_14_ok : fermatBucket_14.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_15_ok : fermatBucket_15.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_16_ok : fermatBucket_16.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_17_ok : fermatBucket_17.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_18_ok : fermatBucket_18.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_19_ok : fermatBucket_19.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_20_ok : fermatBucket_20.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_21_ok : fermatBucket_21.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_22_ok : fermatBucket_22.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_23_ok : fermatBucket_23.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_24_ok : fermatBucket_24.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_25_ok : fermatBucket_25.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_26_ok : fermatBucket_26.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_27_ok : fermatBucket_27.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_28_ok : fermatBucket_28.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_29_ok : fermatBucket_29.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_30_ok : fermatBucket_30.all fermat2Fail = true := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem fermatBucket_31_ok : fermatBucket_31.all fermat2Fail = true := rfl

private theorem divChunk_0_len : divChunk_0.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_0_ok : checkDivChunk 1 divChunk_0 = true := rfl

private theorem divChunk_1_len : divChunk_1.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_1_ok : checkDivChunk 101 divChunk_1 = true := rfl

private theorem divChunk_2_len : divChunk_2.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_2_ok : checkDivChunk 201 divChunk_2 = true := rfl

private theorem divChunk_3_len : divChunk_3.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_3_ok : checkDivChunk 301 divChunk_3 = true := rfl

private theorem divChunk_4_len : divChunk_4.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_4_ok : checkDivChunk 401 divChunk_4 = true := rfl

private theorem divChunk_5_len : divChunk_5.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_5_ok : checkDivChunk 501 divChunk_5 = true := rfl

private theorem divChunk_6_len : divChunk_6.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_6_ok : checkDivChunk 601 divChunk_6 = true := rfl

private theorem divChunk_7_len : divChunk_7.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_7_ok : checkDivChunk 701 divChunk_7 = true := rfl

private theorem divChunk_8_len : divChunk_8.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_8_ok : checkDivChunk 801 divChunk_8 = true := rfl

private theorem divChunk_9_len : divChunk_9.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_9_ok : checkDivChunk 901 divChunk_9 = true := rfl

private theorem divChunk_10_len : divChunk_10.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_10_ok : checkDivChunk 1001 divChunk_10 = true := rfl

private theorem divChunk_11_len : divChunk_11.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_11_ok : checkDivChunk 1101 divChunk_11 = true := rfl

private theorem divChunk_12_len : divChunk_12.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_12_ok : checkDivChunk 1201 divChunk_12 = true := rfl

private theorem divChunk_13_len : divChunk_13.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_13_ok : checkDivChunk 1301 divChunk_13 = true := rfl

private theorem divChunk_14_len : divChunk_14.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_14_ok : checkDivChunk 1401 divChunk_14 = true := rfl

private theorem divChunk_15_len : divChunk_15.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_15_ok : checkDivChunk 1501 divChunk_15 = true := rfl

private theorem divChunk_16_len : divChunk_16.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_16_ok : checkDivChunk 1601 divChunk_16 = true := rfl

private theorem divChunk_17_len : divChunk_17.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_17_ok : checkDivChunk 1701 divChunk_17 = true := rfl

private theorem divChunk_18_len : divChunk_18.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_18_ok : checkDivChunk 1801 divChunk_18 = true := rfl

private theorem divChunk_19_len : divChunk_19.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_19_ok : checkDivChunk 1901 divChunk_19 = true := rfl

private theorem divChunk_20_len : divChunk_20.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_20_ok : checkDivChunk 2001 divChunk_20 = true := rfl

private theorem divChunk_21_len : divChunk_21.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_21_ok : checkDivChunk 2101 divChunk_21 = true := rfl

private theorem divChunk_22_len : divChunk_22.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_22_ok : checkDivChunk 2201 divChunk_22 = true := rfl

private theorem divChunk_23_len : divChunk_23.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_23_ok : checkDivChunk 2301 divChunk_23 = true := rfl

private theorem divChunk_24_len : divChunk_24.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_24_ok : checkDivChunk 2401 divChunk_24 = true := rfl

private theorem divChunk_25_len : divChunk_25.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_25_ok : checkDivChunk 2501 divChunk_25 = true := rfl

private theorem divChunk_26_len : divChunk_26.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_26_ok : checkDivChunk 2601 divChunk_26 = true := rfl

private theorem divChunk_27_len : divChunk_27.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_27_ok : checkDivChunk 2701 divChunk_27 = true := rfl

private theorem divChunk_28_len : divChunk_28.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_28_ok : checkDivChunk 2801 divChunk_28 = true := rfl

private theorem divChunk_29_len : divChunk_29.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_29_ok : checkDivChunk 2901 divChunk_29 = true := rfl

private theorem divChunk_30_len : divChunk_30.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_30_ok : checkDivChunk 3001 divChunk_30 = true := rfl

private theorem divChunk_31_len : divChunk_31.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_31_ok : checkDivChunk 3101 divChunk_31 = true := rfl

private theorem divChunk_32_len : divChunk_32.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_32_ok : checkDivChunk 3201 divChunk_32 = true := rfl

private theorem divChunk_33_len : divChunk_33.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_33_ok : checkDivChunk 3301 divChunk_33 = true := rfl

private theorem divChunk_34_len : divChunk_34.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_34_ok : checkDivChunk 3401 divChunk_34 = true := rfl

private theorem divChunk_35_len : divChunk_35.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_35_ok : checkDivChunk 3501 divChunk_35 = true := rfl

private theorem divChunk_36_len : divChunk_36.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_36_ok : checkDivChunk 3601 divChunk_36 = true := rfl

private theorem divChunk_37_len : divChunk_37.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_37_ok : checkDivChunk 3701 divChunk_37 = true := rfl

private theorem divChunk_38_len : divChunk_38.length = 100 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_38_ok : checkDivChunk 3801 divChunk_38 = true := rfl

private theorem divChunk_39_len : divChunk_39.length = 95 := rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem divChunk_39_ok : checkDivChunk 3901 divChunk_39 = true := rfl

/- ### Section 6: Combining buckets, chunks, boundary cases, and main disproof -/

private lemma fermatBuckets_all_ok : fermatBuckets.all (fun b => b.all fermat2Fail) = true := by
  unfold fermatBuckets
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨fermatBucket_0_ok, fermatBucket_1_ok, fermatBucket_2_ok, fermatBucket_3_ok, fermatBucket_4_ok, fermatBucket_5_ok, fermatBucket_6_ok, fermatBucket_7_ok, fermatBucket_8_ok, fermatBucket_9_ok, fermatBucket_10_ok, fermatBucket_11_ok, fermatBucket_12_ok, fermatBucket_13_ok, fermatBucket_14_ok, fermatBucket_15_ok, fermatBucket_16_ok, fermatBucket_17_ok, fermatBucket_18_ok, fermatBucket_19_ok, fermatBucket_20_ok, fermatBucket_21_ok, fermatBucket_22_ok, fermatBucket_23_ok, fermatBucket_24_ok, fermatBucket_25_ok, fermatBucket_26_ok, fermatBucket_27_ok, fermatBucket_28_ok, fermatBucket_29_ok, fermatBucket_30_ok, fermatBucket_31_ok⟩

private lemma inFermatBuckets_sound (k : Nat) (hk : inFermatBuckets k = true) :
    fermat2Fail k = true := by
  unfold inFermatBuckets at hk
  rcases List.any_eq_true.mp hk with ⟨b, hb_mem, hk_b⟩
  have hall := (List.all_eq_true.mp fermatBuckets_all_ok) b hb_mem
  exact (List.all_eq_true.mp hall) k (List.contains_iff_mem.mp hk_b)

private lemma checkDivChunk_sound :
    ∀ ws k0 k,
      checkDivChunk k0 ws = true →
      1 ≤ k0 → k0 + ws.length ≤ 3996 →
      k0 ≤ k → k < k0 + ws.length →
      ¬ Nat.Prime (k * (k + 1) ^ ((3998 - k).totient / 2) - 1)
  | [], k0, k, _, _, _, hk1, hk2 => by simp at hk2; omega
  | w :: ws, k0, k, hchk, hk0_1, hlen, hk1, hk2 => by
    unfold checkDivChunk at hchk
    simp only [Bool.and_eq_true] at hchk
    rcases hchk with ⟨hhead, htail⟩
    by_cases heq : k = k0
    · subst heq
      have hk_le : k ≤ 3995 := by simp at hlen; omega
      by_cases hw : (w == 0) = true
      · rw [if_pos hw] at hhead
        exact not_prime_of_fermat2Fail k hk0_1 hk_le (inFermatBuckets_sound k hhead)
      · rw [if_neg hw] at hhead
        exact not_prime_of_divCheck k w hk0_1 hk_le hhead
    · have hk1' : k0 + 1 ≤ k := by omega
      have hk2' : k < (k0 + 1) + ws.length := by simp at hk2; omega
      have hlen' : (k0 + 1) + ws.length ≤ 3996 := by simp at hlen; omega
      exact checkDivChunk_sound ws (k0 + 1) k htail (by omega) hlen' hk1' hk2'

private lemma not_prime_all_range (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 3995) :
    ¬ Nat.Prime (k * (k + 1) ^ ((3998 - k).totient / 2) - 1) := by
  if h0 : k ≤ 100 then
    exact checkDivChunk_sound divChunk_0 1 k divChunk_0_ok (by omega) (by have := divChunk_0_len; omega) (by omega) (by have := divChunk_0_len; omega)
  else
  if h1 : k ≤ 200 then
    exact checkDivChunk_sound divChunk_1 101 k divChunk_1_ok (by omega) (by have := divChunk_1_len; omega) (by omega) (by have := divChunk_1_len; omega)
  else
  if h2 : k ≤ 300 then
    exact checkDivChunk_sound divChunk_2 201 k divChunk_2_ok (by omega) (by have := divChunk_2_len; omega) (by omega) (by have := divChunk_2_len; omega)
  else
  if h3 : k ≤ 400 then
    exact checkDivChunk_sound divChunk_3 301 k divChunk_3_ok (by omega) (by have := divChunk_3_len; omega) (by omega) (by have := divChunk_3_len; omega)
  else
  if h4 : k ≤ 500 then
    exact checkDivChunk_sound divChunk_4 401 k divChunk_4_ok (by omega) (by have := divChunk_4_len; omega) (by omega) (by have := divChunk_4_len; omega)
  else
  if h5 : k ≤ 600 then
    exact checkDivChunk_sound divChunk_5 501 k divChunk_5_ok (by omega) (by have := divChunk_5_len; omega) (by omega) (by have := divChunk_5_len; omega)
  else
  if h6 : k ≤ 700 then
    exact checkDivChunk_sound divChunk_6 601 k divChunk_6_ok (by omega) (by have := divChunk_6_len; omega) (by omega) (by have := divChunk_6_len; omega)
  else
  if h7 : k ≤ 800 then
    exact checkDivChunk_sound divChunk_7 701 k divChunk_7_ok (by omega) (by have := divChunk_7_len; omega) (by omega) (by have := divChunk_7_len; omega)
  else
  if h8 : k ≤ 900 then
    exact checkDivChunk_sound divChunk_8 801 k divChunk_8_ok (by omega) (by have := divChunk_8_len; omega) (by omega) (by have := divChunk_8_len; omega)
  else
  if h9 : k ≤ 1000 then
    exact checkDivChunk_sound divChunk_9 901 k divChunk_9_ok (by omega) (by have := divChunk_9_len; omega) (by omega) (by have := divChunk_9_len; omega)
  else
  if h10 : k ≤ 1100 then
    exact checkDivChunk_sound divChunk_10 1001 k divChunk_10_ok (by omega) (by have := divChunk_10_len; omega) (by omega) (by have := divChunk_10_len; omega)
  else
  if h11 : k ≤ 1200 then
    exact checkDivChunk_sound divChunk_11 1101 k divChunk_11_ok (by omega) (by have := divChunk_11_len; omega) (by omega) (by have := divChunk_11_len; omega)
  else
  if h12 : k ≤ 1300 then
    exact checkDivChunk_sound divChunk_12 1201 k divChunk_12_ok (by omega) (by have := divChunk_12_len; omega) (by omega) (by have := divChunk_12_len; omega)
  else
  if h13 : k ≤ 1400 then
    exact checkDivChunk_sound divChunk_13 1301 k divChunk_13_ok (by omega) (by have := divChunk_13_len; omega) (by omega) (by have := divChunk_13_len; omega)
  else
  if h14 : k ≤ 1500 then
    exact checkDivChunk_sound divChunk_14 1401 k divChunk_14_ok (by omega) (by have := divChunk_14_len; omega) (by omega) (by have := divChunk_14_len; omega)
  else
  if h15 : k ≤ 1600 then
    exact checkDivChunk_sound divChunk_15 1501 k divChunk_15_ok (by omega) (by have := divChunk_15_len; omega) (by omega) (by have := divChunk_15_len; omega)
  else
  if h16 : k ≤ 1700 then
    exact checkDivChunk_sound divChunk_16 1601 k divChunk_16_ok (by omega) (by have := divChunk_16_len; omega) (by omega) (by have := divChunk_16_len; omega)
  else
  if h17 : k ≤ 1800 then
    exact checkDivChunk_sound divChunk_17 1701 k divChunk_17_ok (by omega) (by have := divChunk_17_len; omega) (by omega) (by have := divChunk_17_len; omega)
  else
  if h18 : k ≤ 1900 then
    exact checkDivChunk_sound divChunk_18 1801 k divChunk_18_ok (by omega) (by have := divChunk_18_len; omega) (by omega) (by have := divChunk_18_len; omega)
  else
  if h19 : k ≤ 2000 then
    exact checkDivChunk_sound divChunk_19 1901 k divChunk_19_ok (by omega) (by have := divChunk_19_len; omega) (by omega) (by have := divChunk_19_len; omega)
  else
  if h20 : k ≤ 2100 then
    exact checkDivChunk_sound divChunk_20 2001 k divChunk_20_ok (by omega) (by have := divChunk_20_len; omega) (by omega) (by have := divChunk_20_len; omega)
  else
  if h21 : k ≤ 2200 then
    exact checkDivChunk_sound divChunk_21 2101 k divChunk_21_ok (by omega) (by have := divChunk_21_len; omega) (by omega) (by have := divChunk_21_len; omega)
  else
  if h22 : k ≤ 2300 then
    exact checkDivChunk_sound divChunk_22 2201 k divChunk_22_ok (by omega) (by have := divChunk_22_len; omega) (by omega) (by have := divChunk_22_len; omega)
  else
  if h23 : k ≤ 2400 then
    exact checkDivChunk_sound divChunk_23 2301 k divChunk_23_ok (by omega) (by have := divChunk_23_len; omega) (by omega) (by have := divChunk_23_len; omega)
  else
  if h24 : k ≤ 2500 then
    exact checkDivChunk_sound divChunk_24 2401 k divChunk_24_ok (by omega) (by have := divChunk_24_len; omega) (by omega) (by have := divChunk_24_len; omega)
  else
  if h25 : k ≤ 2600 then
    exact checkDivChunk_sound divChunk_25 2501 k divChunk_25_ok (by omega) (by have := divChunk_25_len; omega) (by omega) (by have := divChunk_25_len; omega)
  else
  if h26 : k ≤ 2700 then
    exact checkDivChunk_sound divChunk_26 2601 k divChunk_26_ok (by omega) (by have := divChunk_26_len; omega) (by omega) (by have := divChunk_26_len; omega)
  else
  if h27 : k ≤ 2800 then
    exact checkDivChunk_sound divChunk_27 2701 k divChunk_27_ok (by omega) (by have := divChunk_27_len; omega) (by omega) (by have := divChunk_27_len; omega)
  else
  if h28 : k ≤ 2900 then
    exact checkDivChunk_sound divChunk_28 2801 k divChunk_28_ok (by omega) (by have := divChunk_28_len; omega) (by omega) (by have := divChunk_28_len; omega)
  else
  if h29 : k ≤ 3000 then
    exact checkDivChunk_sound divChunk_29 2901 k divChunk_29_ok (by omega) (by have := divChunk_29_len; omega) (by omega) (by have := divChunk_29_len; omega)
  else
  if h30 : k ≤ 3100 then
    exact checkDivChunk_sound divChunk_30 3001 k divChunk_30_ok (by omega) (by have := divChunk_30_len; omega) (by omega) (by have := divChunk_30_len; omega)
  else
  if h31 : k ≤ 3200 then
    exact checkDivChunk_sound divChunk_31 3101 k divChunk_31_ok (by omega) (by have := divChunk_31_len; omega) (by omega) (by have := divChunk_31_len; omega)
  else
  if h32 : k ≤ 3300 then
    exact checkDivChunk_sound divChunk_32 3201 k divChunk_32_ok (by omega) (by have := divChunk_32_len; omega) (by omega) (by have := divChunk_32_len; omega)
  else
  if h33 : k ≤ 3400 then
    exact checkDivChunk_sound divChunk_33 3301 k divChunk_33_ok (by omega) (by have := divChunk_33_len; omega) (by omega) (by have := divChunk_33_len; omega)
  else
  if h34 : k ≤ 3500 then
    exact checkDivChunk_sound divChunk_34 3401 k divChunk_34_ok (by omega) (by have := divChunk_34_len; omega) (by omega) (by have := divChunk_34_len; omega)
  else
  if h35 : k ≤ 3600 then
    exact checkDivChunk_sound divChunk_35 3501 k divChunk_35_ok (by omega) (by have := divChunk_35_len; omega) (by omega) (by have := divChunk_35_len; omega)
  else
  if h36 : k ≤ 3700 then
    exact checkDivChunk_sound divChunk_36 3601 k divChunk_36_ok (by omega) (by have := divChunk_36_len; omega) (by omega) (by have := divChunk_36_len; omega)
  else
  if h37 : k ≤ 3800 then
    exact checkDivChunk_sound divChunk_37 3701 k divChunk_37_ok (by omega) (by have := divChunk_37_len; omega) (by omega) (by have := divChunk_37_len; omega)
  else
  if h38 : k ≤ 3900 then
    exact checkDivChunk_sound divChunk_38 3801 k divChunk_38_ok (by omega) (by have := divChunk_38_len; omega) (by omega) (by have := divChunk_38_len; omega)
  else
    exact checkDivChunk_sound divChunk_39 3901 k divChunk_39_ok (by omega) (by have := divChunk_39_len; omega) (by omega) (by have := divChunk_39_len; omega)

private lemma not_sq_3997 (r : Nat) : r ^ 2 ≠ 3997 := by
  intro h
  by_cases h63 : r ≤ 63
  · nlinarith
  · nlinarith

private lemma not_sq_3998 (r : Nat) : r ^ 2 ≠ 3998 := by
  intro h
  by_cases h63 : r ≤ 63
  · nlinarith
  · nlinarith

private lemma no_witness_3998 :
    ¬ ∃ k, 0 < k ∧ k < 3998 ∧
      ∃ p : Nat, p.Prime ∧ (p + 1) ^ 2 = k ^ 2 * (k + 1) ^ (3998 - k).totient := by
  rintro ⟨k, hk0, hkn, p, hp, heq⟩
  by_cases hk3997 : k = 3997
  · subst hk3997
    have htot1 : Nat.totient (3998 - 3997) = 1 := rfl
    rw [htot1, pow_one] at heq
    have hdvd2 : 3997 ^ 2 ∣ (p + 1) ^ 2 := ⟨3998, heq⟩
    have hdvd : 3997 ∣ p + 1 := (Nat.pow_dvd_pow_iff (by omega : 2 ≠ 0)).mp hdvd2
    rcases hdvd with ⟨r, hr⟩
    rw [hr, mul_pow] at heq
    have hr2 : r ^ 2 = 3998 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3997 ^ 2) heq
    exact not_sq_3998 r hr2
  · by_cases hk3996 : k = 3996
    · subst hk3996
      have htot2 : Nat.totient (3998 - 3996) = 1 := rfl
      rw [htot2, pow_one] at heq
      have hdvd2 : 3996 ^ 2 ∣ (p + 1) ^ 2 := ⟨3997, heq⟩
      have hdvd : 3996 ∣ p + 1 := (Nat.pow_dvd_pow_iff (by omega : 2 ≠ 0)).mp hdvd2
      rcases hdvd with ⟨r, hr⟩
      rw [hr, mul_pow] at heq
      have hr2 : r ^ 2 = 3997 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3996 ^ 2) heq
      exact not_sq_3997 r hr2
    · have hk1 : 1 ≤ k := by omega
      have hk2 : k ≤ 3995 := by omega
      have hev : Even (3998 - k).totient := Nat.totient_even (by omega)
      rcases hev with ⟨m', hm'⟩
      set m := (3998 - k).totient / 2
      have htot_eq : (3998 - k).totient = 2 * m := by omega
      rw [htot_eq] at heq
      have hrhs : k ^ 2 * (k + 1) ^ (2 * m) = (k * (k + 1) ^ m) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm m 2]
      rw [hrhs] at heq
      have hbase : p + 1 = k * (k + 1) ^ m := Nat.pow_left_injective (by omega : 2 ≠ 0) heq
      have hp_eq : p = k * (k + 1) ^ m - 1 := by omega
      rw [hp_eq] at hp
      exact not_prime_all_range k hk1 hk2 hp

end OeisA234360Disproof

theorem OMA.disproof : ¬ (type_of% @OeisA234360.conjecture_4) := by
  intro h
  exact OeisA234360Disproof.no_witness_3998 (h 3998 (by omega))
