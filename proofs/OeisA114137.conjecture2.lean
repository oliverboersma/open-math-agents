import FormalConjectures.OEIS.«114137»

/-! Two disjoint covering systems yield an odd offset that never gives a semiprime. -/

namespace A114137Cover

open scoped ArithmeticFunction.Omega

private def gap : ℕ := 540116963086372950416020252444056834834397468153870722613808923758552325258329600015195536434316150865047256177271991511611230912655965897541633233537969

private theorem power_square {d a p u : ℕ}
    (hd : d = a * 2) (ha : 2 ^ a ≡ u [MOD p]) : 2 ^ d ≡ u ^ 2 [MOD p] := by
  rw [hd, pow_mul]
  exact ha.pow 2

private theorem row_divides {n p d r : ℕ}
    (hn : n % d = r) (hp : 2 ^ d ≡ 1 [MOD p])
    (hr : 2 ^ r + gap ≡ 0 [MOD p]) : p ∣ 2 ^ n + gap := by
  have hsplit : d * (n / d) + r = n := by
    simpa only [hn] using Nat.div_add_mod n d
  have hpower : 2 ^ n ≡ 2 ^ r [MOD p] := calc
    2 ^ n = (2 ^ d) ^ (n / d) * 2 ^ r := by rw [← pow_mul, ← pow_add, hsplit]
    _ ≡ 1 ^ (n / d) * 2 ^ r [MOD p] := (hp.pow _).mul_right _
    _ = 2 ^ r := by simp
  exact Nat.modEq_zero_iff_dvd.mp ((hpower.add_right gap).trans hr)

private def primesA : List ℕ :=
  [5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 109, 151, 241, 331]

private theorem coverA (n : ℕ) :
    ∃ p ∈ primesA, p ∣ 2 ^ n + gap := by
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · have h4 : n % 4 = 0 ∨ n % 4 = 2 := by omega
    rcases h4 with h4 | h4
    · exact ⟨5, by decide, row_divides (d := 4) (r := 0) (by omega) (by decide) (by decide)⟩
    · have h8 : n % 8 = 2 ∨ n % 8 = 6 := by omega
      rcases h8 with h8 | h8
      · exact ⟨17, by decide, row_divides (d := 8) (r := 2) (by omega) (by decide) (by decide)⟩
      · have h24 : n % 24 = 6 ∨ n % 24 = 14 ∨ n % 24 = 22 := by omega
        rcases h24 with h24 | h24 | h24
        · exact ⟨241, by decide, row_divides (d := 24) (r := 6) (by omega) (by decide) (by decide)⟩
        · exact ⟨7, by decide, row_divides (d := 3) (r := 2) (by omega) (by decide) (by decide)⟩
        · exact ⟨13, by decide, row_divides (d := 12) (r := 10) (by omega) (by decide) (by decide)⟩
  · have h6 : n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5 := by omega
    rcases h6 with h6 | h6 | h6
    · have h18 : n % 18 = 1 ∨ n % 18 = 7 ∨ n % 18 = 13 := by omega
      rcases h18 with h18 | h18 | h18
      · have h36 : n % 36 = 1 ∨ n % 36 = 19 := by omega
        rcases h36 with h36 | h36
        · exact ⟨109, by decide, row_divides (d := 36) (r := 1) (by omega) (by decide) (by decide)⟩
        · exact ⟨37, by decide, row_divides (d := 36) (r := 19) (by omega) (by decide) (by decide)⟩
      · exact ⟨19, by decide, row_divides (d := 18) (r := 7) (by omega) (by decide) (by decide)⟩
      · exact ⟨73, by decide, row_divides (d := 9) (r := 4) (by omega) (by decide) (by decide)⟩
    · have h30 : n % 30 = 3 ∨ n % 30 = 9 ∨ n % 30 = 15 ∨ n % 30 = 21 ∨ n % 30 = 27 := by omega
      rcases h30 with h30 | h30 | h30 | h30 | h30
      · have h60 : n % 60 = 3 ∨ n % 60 = 33 := by omega
        rcases h60 with h60 | h60
        · exact ⟨61, by decide, row_divides (d := 60) (r := 3) (by omega) (by decide) (by decide)⟩
        · exact ⟨41, by decide, row_divides (d := 20) (r := 13) (by omega) (by decide) (by decide)⟩
      · exact ⟨331, by decide, row_divides (d := 30) (r := 9) (by omega) (by decide) (by decide)⟩
      · exact ⟨11, by decide, row_divides (d := 10) (r := 5) (by omega) (by decide) (by decide)⟩
      · exact ⟨31, by decide, row_divides (d := 5) (r := 1) (by omega) (by decide) (by decide)⟩
      · exact ⟨151, by decide, row_divides (d := 15) (r := 12) (by omega) (by decide) (by decide)⟩
    · exact ⟨7, by decide, row_divides (d := 3) (r := 2) (by omega) (by decide) (by decide)⟩

private def primesB : List ℕ :=
  [3, 23, 29, 43, 67, 71, 89, 97, 113, 127, 257, 281, 337, 353, 397, 433, 449, 577, 641, 673, 683, 1153, 1429, 2113, 2689, 5153, 5419, 6337, 7393, 20857, 38737, 65537, 86171, 122921, 312709, 599479, 6700417, 7416361, 15790321]

private theorem coverB (n : ℕ) :
    ∃ p ∈ primesB, p ∣ 2 ^ n + gap := by
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h2 with h2 | h2
  · have h4 : n % 4 = 0 ∨ n % 4 = 2 := by omega
    rcases h4 with h4 | h4
    · have h28 : n % 28 = 0 ∨ n % 28 = 4 ∨ n % 28 = 8 ∨ n % 28 = 12 ∨ n % 28 = 16 ∨ n % 28 = 20 ∨ n % 28 = 24 := by omega
      rcases h28 with h28 | h28 | h28 | h28 | h28 | h28 | h28
      · have h140 : n % 140 = 0 ∨ n % 140 = 28 ∨ n % 140 = 56 ∨ n % 140 = 84 ∨ n % 140 = 112 := by omega
        rcases h140 with h140 | h140 | h140 | h140 | h140
        · exact ⟨7416361, by decide, row_divides (d := 140) (r := 0) (by omega) (by decide) (by decide)⟩
        · exact ⟨71, by decide, row_divides (d := 35) (r := 28) (by omega) (by decide) (by decide)⟩
        · exact ⟨281, by decide, row_divides (d := 70) (r := 56) (by omega) (by decide) (by decide)⟩
        · exact ⟨86171, by decide, row_divides (d := 70) (r := 14) (by omega) (by decide) (by decide)⟩
        · exact ⟨122921, by decide, row_divides (d := 35) (r := 7) (by omega) (by decide) (by decide)⟩
      · exact ⟨29, by decide, row_divides (d := 28) (r := 4) (by omega) (by decide) (by decide)⟩
      · exact ⟨43, by decide, row_divides (d := 14) (r := 8) (by omega) (by decide) (by decide)⟩
      · exact ⟨113, by decide, row_divides (d := 28) (r := 12) (by omega) (by decide) (by decide)⟩
      · exact ⟨127, by decide, row_divides (d := 7) (r := 2) (by omega) (by decide) (by decide)⟩
      · have h84 : n % 84 = 20 ∨ n % 84 = 48 ∨ n % 84 = 76 := by omega
        rcases h84 with h84 | h84 | h84
        · exact ⟨337, by decide, row_divides (d := 21) (r := 20) (by omega) (by decide) (by decide)⟩
        · exact ⟨1429, by decide, row_divides (d := 84) (r := 48) (by omega) (by decide) (by decide)⟩
        · exact ⟨5419, by decide, row_divides (d := 42) (r := 34) (by omega) (by decide) (by decide)⟩
      · have h56 : n % 56 = 24 ∨ n % 56 = 52 := by omega
        rcases h56 with h56 | h56
        · exact ⟨15790321, by decide, row_divides (d := 56) (r := 24) (by omega) (by decide) (by decide)⟩
        · have h112 : n % 112 = 52 ∨ n % 112 = 108 := by omega
          rcases h112 with h112 | h112
          · exact ⟨5153, by decide, row_divides (d := 112) (r := 52) (by omega) (by decide) (by decide)⟩
          · have h224 : n % 224 = 108 ∨ n % 224 = 220 := by omega
            rcases h224 with h224 | h224
            · exact ⟨449, by decide, row_divides (d := 224) (r := 108) (by omega) (by decide) (by decide)⟩
            · exact ⟨2689, by decide, row_divides (d := 224) (r := 220) (by omega) (by decide) (by decide)⟩
    · have h8 : n % 8 = 2 ∨ n % 8 = 6 := by omega
      rcases h8 with h8 | h8
      · have h16 : n % 16 = 2 ∨ n % 16 = 10 := by omega
        rcases h16 with h16 | h16
        · exact ⟨257, by decide, row_divides (d := 16) (r := 2) (by omega) (by decide) (by decide)⟩
        · have h32 : n % 32 = 10 ∨ n % 32 = 26 := by omega
          rcases h32 with h32 | h32
          · exact ⟨65537, by decide, row_divides (d := 32) (r := 10) (by omega) (by decide) (by decide)⟩
          · have h64 : n % 64 = 26 ∨ n % 64 = 58 := by omega
            rcases h64 with h64 | h64
            · exact ⟨641, by decide, row_divides (d := 64) (r := 26) (by omega) (by decide) (by decide)⟩
            · exact ⟨6700417, by decide, row_divides (d := 64) (r := 58) (by omega) (by decide) (by decide)⟩
      · have h24 : n % 24 = 6 ∨ n % 24 = 14 ∨ n % 24 = 22 := by omega
        rcases h24 with h24 | h24 | h24
        · have h48 : n % 48 = 6 ∨ n % 48 = 30 := by omega
          rcases h48 with h48 | h48
          · exact ⟨97, by decide, row_divides (d := 48) (r := 6) (by omega) (by decide) (by decide)⟩
          · exact ⟨673, by decide, row_divides (d := 48) (r := 30) (by omega) (by decide) (by decide)⟩
        · have h72 : n % 72 = 14 ∨ n % 72 = 38 ∨ n % 72 = 62 := by omega
          rcases h72 with h72 | h72 | h72
          · exact ⟨433, by decide, row_divides (d := 72) (r := 14) (by omega) (by decide) (by decide)⟩
          · exact ⟨38737, by decide, row_divides (d := 72) (r := 38) (by omega) (by decide) (by decide)⟩
          · have h144 : n % 144 = 62 ∨ n % 144 = 134 := by omega
            rcases h144 with h144 | h144
            · exact ⟨577, by decide, row_divides (d := 144) (r := 62) (by omega) (by decide) (by decide)⟩
            · have h288 : n % 288 = 134 ∨ n % 288 = 278 := by omega
              rcases h288 with h288 | h288
              · exact ⟨1153, by decide, row_divides (d := 288) (r := 134) (by omega) ((power_square (d := 288) (a := 144) (p := 1153) (u := 1152) (by decide) (by decide)).trans (by decide)) (by decide)⟩
              · exact ⟨6337, by decide, row_divides (d := 288) (r := 278) (by omega) ((power_square (d := 288) (a := 144) (p := 6337) (u := 6336) (by decide) (by decide)).trans (by decide)) ((power_square (d := 278) (a := 139) (p := 6337) (u := 198) (by decide) (by decide)).add_right gap |>.trans (by decide))⟩
        · have h264 : n % 264 = 22 ∨ n % 264 = 46 ∨ n % 264 = 70 ∨ n % 264 = 94 ∨ n % 264 = 118 ∨ n % 264 = 142 ∨ n % 264 = 166 ∨ n % 264 = 190 ∨ n % 264 = 214 ∨ n % 264 = 238 ∨ n % 264 = 262 := by omega
          rcases h264 with h264 | h264 | h264 | h264 | h264 | h264 | h264 | h264 | h264 | h264 | h264
          · exact ⟨23, by decide, row_divides (d := 11) (r := 0) (by omega) (by decide) (by decide)⟩
          · exact ⟨67, by decide, row_divides (d := 66) (r := 46) (by omega) (by decide) (by decide)⟩
          · exact ⟨89, by decide, row_divides (d := 11) (r := 4) (by omega) (by decide) (by decide)⟩
          · exact ⟨353, by decide, row_divides (d := 88) (r := 6) (by omega) (by decide) (by decide)⟩
          · exact ⟨397, by decide, row_divides (d := 44) (r := 30) (by omega) (by decide) (by decide)⟩
          · exact ⟨683, by decide, row_divides (d := 22) (r := 10) (by omega) (by decide) (by decide)⟩
          · exact ⟨2113, by decide, row_divides (d := 44) (r := 34) (by omega) (by decide) (by decide)⟩
          · exact ⟨7393, by decide, row_divides (d := 264) (r := 190) (by omega) ((power_square (d := 264) (a := 132) (p := 7393) (u := 7392) (by decide) (by decide)).trans (by decide)) (by decide)⟩
          · exact ⟨20857, by decide, row_divides (d := 66) (r := 16) (by omega) (by decide) (by decide)⟩
          · exact ⟨312709, by decide, row_divides (d := 132) (r := 106) (by omega) (by decide) (by decide)⟩
          · exact ⟨599479, by decide, row_divides (d := 33) (r := 31) (by omega) (by decide) (by decide)⟩
  · exact ⟨3, by decide, row_divides (d := 2) (r := 1) (by omega) (by decide) (by decide)⟩

private theorem factor_bounds : ∀ p ∈ primesA, ∀ q ∈ primesB,
    1 < p ∧ 1 < q ∧ Nat.Coprime p q ∧ p * q < gap := by decide

private theorem cardFactors_pos {m : ℕ} (hm : 1 < m) : 1 ≤ Ω m := by
  by_contra! h
  have hh : Ω m = 0 := by omega
  obtain hh | hh := ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hh <;> omega

private theorem no_semiprime (n : ℕ) : ¬ (2 ^ n + gap).IsSemiprime := by
  intro h
  obtain ⟨p, hpa, hp⟩ := coverA n
  obtain ⟨q, hqb, hq⟩ := coverB n
  obtain ⟨hp', hq', hc, hlt⟩ := factor_bounds p hpa q hqb
  obtain ⟨d, hd⟩ := hc.mul_dvd_of_dvd_of_dvd hp hq
  have hd' : 1 < d := by
    by_contra! hd'
    interval_cases d
    · exact h.1 (by simpa only [Nat.mul_zero] using hd)
    · have hg : gap ≤ 2 ^ n + gap := Nat.le_add_left _ _
      rw [Nat.mul_one] at hd
      omega
  have hd0 : d ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  have hq0 : q ≠ 0 := by omega
  have hf := h.2
  change Ω (2 ^ n + gap) = 2 at hf
  rw [hd, ArithmeticFunction.cardFactors_mul (mul_ne_zero hp0 hq0) hd0,
    ArithmeticFunction.cardFactors_mul hp0 hq0] at hf
  have hpF := cardFactors_pos hp'
  have hqF := cardFactors_pos hq'
  have hdF := cardFactors_pos hd'
  omega

theorem disproof : ¬ (∀ k : ℕ, Odd k → ∃ n : ℕ, OeisA114137.a n = k) := by
  intro h
  obtain ⟨n, hn⟩ := h gap (by decide)
  let s : Set ℕ := {v | 2 ^ n < v ∧ v.IsSemiprime ∧ Odd v}
  change sInf s - 2 ^ n = gap at hn
  have hgap : 0 < gap := by decide
  have hnonempty : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty, Nat.zero_sub] at hn
    omega
  have hv := Nat.sInf_mem hnonempty
  have heq : sInf s = 2 ^ n + gap := by omega
  exact no_semiprime n (heq ▸ hv.2.1)

end A114137Cover

theorem OMA.disproof : ¬ (type_of% @OeisA114137.conjecture2) := A114137Cover.disproof
