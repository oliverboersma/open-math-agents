import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1

/-! A kernel-checked certificate for the range from 30000 to 60183. Primes are counted in
blocks with a gcd test against the product of the primes below 246, which every prime from
246 on passes. On a geometric grid of ratio 1.004 starting at 30000 the logarithm is at most
10.32 + 0.004 j at the j-th grid point, and on each grid interval the count at its right end
times this bound is at most its left end. -/

namespace OMA930b

/-- The primes below 246. -/
def SP : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241]

/-- The product of the primes below 246. -/
def Q : ℕ := 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730

def isP (n : ℕ) : Bool := if n < 246 then SP.contains n else Nat.beq (Nat.gcd n Q) 1

def blkCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (isP n).toNat + blkCount k (n + 1)

lemma SP_static : SP.all (fun a => decide (0 < a) && decide (a < 246)) = true := by
  decide +kernel

lemma Q_eq : Q = SP.prod := by decide +kernel

lemma small_static : (List.range 246).all (fun n => SP.contains n || decide (n < 2) ||
    (List.range n).any (fun d => decide (2 ≤ d) && decide (n % d = 0))) = true := by
  decide +kernel

lemma prime_isP {n : ℕ} (hp : n.Prime) : isP n = true := by
  unfold isP
  by_cases h : n < 246
  · rw [if_pos h]
    have hs := small_static
    rw [List.all_eq_true] at hs
    have h1 := hs n (List.mem_range.2 h)
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      Bool.and_eq_true] at h1
    rcases h1 with (h1 | h1) | ⟨d, hd, hd2, hd3⟩
    · exact h1
    · exact absurd hp.two_le (not_le.2 h1)
    · have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hd3
      rcases (Nat.dvd_prime hp).1 hdvd with h2 | h2
      · omega
      · omega
  · rw [if_neg h]
    have hnd : ¬ n ∣ Q := by
      rw [Q_eq, (Nat.Prime.prime hp).dvd_prod_iff]
      rintro ⟨a, ha, hna⟩
      have hs := SP_static
      rw [List.all_eq_true] at hs
      have h1 := hs a ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      have h2 := Nat.le_of_dvd h1.1 hna
      omega
    have hcop : Nat.gcd n Q = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    rw [hcop]
    rfl

lemma count_add_le : ∀ len b,
    Nat.count Nat.Prime (b + len) ≤ Nat.count Nat.Prime b + blkCount len b := by
  intro len
  induction len with
  | zero =>
    intro b
    simp [blkCount]
  | succ len ih =>
    intro b
    have h1 := ih (b + 1)
    have h2 : b + (len + 1) = b + 1 + len := by omega
    rw [h2, blkCount]
    have h3 : Nat.count Nat.Prime (b + 1) ≤ Nat.count Nat.Prime b + (isP b).toNat := by
      rw [Nat.count_succ]
      by_cases hp : Nat.Prime b
      · rw [if_pos hp, prime_isP hp]
        exact le_of_eq rfl
      · rw [if_neg hp]
        omega
    omega

def Cnt (b c : ℕ) : Prop := Nat.count Nat.Prime b ≤ c

lemma cstep (b len c d : ℕ) (h : Cnt b c) (hd : blkCount len b = d) :
    Cnt (b + len) (c + d) := by
  have h1 := count_add_le len b
  unfold Cnt at *
  omega

lemma log_30000 : Real.log 30000 ≤ 10.32 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 10.32 = Real.exp 1 ^ 10 * Real.exp 0.32 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [h1]
  have h2 : (2.7182818283:ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 10
  have h3 : (1.3712:ℝ) ≤ Real.exp 0.32 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.32)
    exact le_trans (by norm_num) h
  have h4 : (22026:ℝ) ≤ (2.7182818283:ℝ) ^ 10 := by norm_num
  calc (30000:ℝ) ≤ 22026 * 1.3712 := by norm_num
    _ ≤ Real.exp 1 ^ 10 * Real.exp 0.32 :=
        mul_le_mul (h4.trans h2) h3 (by norm_num) (by positivity)

lemma log_grid (a' j : ℕ) (hpos : 0 < a') (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) :
    Real.log a' ≤ 10.32 + 0.004 * j := by
  have hR : (a':ℝ) * 1000 ^ j ≤ 30000 * 1004 ^ j := by exact_mod_cast hgrid
  have ha : (0:ℝ) < a' := by exact_mod_cast hpos
  have h := Real.log_le_log (by positivity) hR
  rw [Real.log_mul ha.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow] at h
  have h1 : Real.log 1004 - Real.log 1000 ≤ 0.004 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1004 / 1000)).trans (by norm_num)
  have h2 := log_30000
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have h3 := mul_le_mul_of_nonneg_left h1 hj
  linarith

lemma interval (a a' P j : ℕ) (ha : 30000 ≤ a) (hc : Cnt a' P)
    (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) (hnum : P * (9120 + 4 * j) ≤ 1000 * a)
    (k : ℕ) (hak : a ≤ k) (hka : k < a') :
    (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k := by
  have hk3 : (30000:ℝ) ≤ k := by exact_mod_cast (by omega : 30000 ≤ k)
  have hkpos : (0:ℝ) < k := by linarith
  have hcard : (k.primesBelow.card : ℝ) ≤ P := by
    have h1 : k.primesBelow.card ≤ P := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      show Nat.count Nat.Prime k ≤ P
      exact le_trans (Nat.count_monotone _ hka.le) hc
    exact_mod_cast h1
  have hlogk : Real.log k ≤ 10.32 + 0.004 * j :=
    (Real.log_le_log hkpos (by exact_mod_cast hka.le)).trans (log_grid a' j (by omega) hgrid)
  have hlog0 : (6/5 : ℝ) ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hkpos]
    have h2 : Real.exp (6/5) ≤ Real.exp (1 + 1) := Real.exp_le_exp.2 (by norm_num)
    rw [Real.exp_add] at h2
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos 1
    have h5 := mul_lt_mul'' h3 h3 h4.le h4.le
    linarith
  have hnumR : (P:ℝ) * (9120 + 4 * j) ≤ 1000 * a := by exact_mod_cast hnum
  have hakR : (a:ℝ) ≤ k := by exact_mod_cast hak
  have hP0 : (0:ℝ) ≤ P := Nat.cast_nonneg P
  calc (k.primesBelow.card : ℝ) * (Real.log k - 6/5)
      ≤ P * (Real.log k - 6/5) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ ≤ P * (10.32 + 0.004 * j - 6/5) := mul_le_mul_of_nonneg_left (by linarith) hP0
    _ = (P * (9120 + 4 * j)) / 1000 := by ring
    _ ≤ (1000 * a) / 1000 := div_le_div_of_nonneg_right hnumR (by norm_num)
    _ = a := by ring
    _ ≤ k := hakR

def Good (b : ℕ) : Prop :=
  ∀ k : ℕ, 30000 ≤ k → k < b → (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k

lemma extend (a a' P j : ℕ) (hg : Good a) (ha : 30000 ≤ a) (hc : Cnt a' P)
    (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) (hnum : P * (9120 + 4 * j) ≤ 1000 * a) :
    Good a' := by
  intro k hk hlt
  by_cases h : k < a
  · exact hg k hk h
  · exact interval a a' P j ha hc hgrid hnum k (not_lt.1 h) hlt

lemma p_0 : Cnt 0 0 := by
  unfold Cnt
  simp

lemma p_1 : Cnt 1000 168 := cstep 0 1000 0 168 p_0 (by decide +kernel)

lemma p_2 : Cnt 2000 303 := cstep 1000 1000 168 135 p_1 (by decide +kernel)

lemma p_3 : Cnt 3000 430 := cstep 2000 1000 303 127 p_2 (by decide +kernel)

lemma p_4 : Cnt 4000 550 := cstep 3000 1000 430 120 p_3 (by decide +kernel)

lemma p_5 : Cnt 5000 669 := cstep 4000 1000 550 119 p_4 (by decide +kernel)

lemma p_6 : Cnt 6000 783 := cstep 5000 1000 669 114 p_5 (by decide +kernel)

lemma p_7 : Cnt 7000 900 := cstep 6000 1000 783 117 p_6 (by decide +kernel)

lemma p_8 : Cnt 8000 1007 := cstep 7000 1000 900 107 p_7 (by decide +kernel)

lemma p_9 : Cnt 9000 1117 := cstep 8000 1000 1007 110 p_8 (by decide +kernel)

lemma p_10 : Cnt 10000 1229 := cstep 9000 1000 1117 112 p_9 (by decide +kernel)

lemma p_11 : Cnt 11000 1335 := cstep 10000 1000 1229 106 p_10 (by decide +kernel)

lemma p_12 : Cnt 12000 1438 := cstep 11000 1000 1335 103 p_11 (by decide +kernel)

lemma p_13 : Cnt 13000 1547 := cstep 12000 1000 1438 109 p_12 (by decide +kernel)

lemma p_14 : Cnt 14000 1652 := cstep 13000 1000 1547 105 p_13 (by decide +kernel)

lemma p_15 : Cnt 15000 1754 := cstep 14000 1000 1652 102 p_14 (by decide +kernel)

lemma p_16 : Cnt 16000 1862 := cstep 15000 1000 1754 108 p_15 (by decide +kernel)

lemma p_17 : Cnt 17000 1960 := cstep 16000 1000 1862 98 p_16 (by decide +kernel)

lemma p_18 : Cnt 18000 2064 := cstep 17000 1000 1960 104 p_17 (by decide +kernel)

lemma p_19 : Cnt 19000 2158 := cstep 18000 1000 2064 94 p_18 (by decide +kernel)

lemma p_20 : Cnt 20000 2262 := cstep 19000 1000 2158 104 p_19 (by decide +kernel)

lemma p_21 : Cnt 21000 2360 := cstep 20000 1000 2262 98 p_20 (by decide +kernel)

lemma p_22 : Cnt 22000 2464 := cstep 21000 1000 2360 104 p_21 (by decide +kernel)

lemma p_23 : Cnt 23000 2564 := cstep 22000 1000 2464 100 p_22 (by decide +kernel)

lemma p_24 : Cnt 24000 2668 := cstep 23000 1000 2564 104 p_23 (by decide +kernel)

lemma p_25 : Cnt 25000 2762 := cstep 24000 1000 2668 94 p_24 (by decide +kernel)

lemma p_26 : Cnt 26000 2860 := cstep 25000 1000 2762 98 p_25 (by decide +kernel)

lemma p_27 : Cnt 27000 2961 := cstep 26000 1000 2860 101 p_26 (by decide +kernel)

lemma p_28 : Cnt 28000 3055 := cstep 27000 1000 2961 94 p_27 (by decide +kernel)

lemma p_29 : Cnt 29000 3153 := cstep 28000 1000 3055 98 p_28 (by decide +kernel)

lemma p_30 : Cnt 30000 3245 := cstep 29000 1000 3153 92 p_29 (by decide +kernel)

lemma p_31 : Cnt 30120 3258 := cstep 30000 120 3245 13 p_30 (by decide +kernel)

lemma p_32 : Cnt 30240 3269 := cstep 30120 120 3258 11 p_31 (by decide +kernel)

lemma p_33 : Cnt 30361 3281 := cstep 30240 121 3269 12 p_32 (by decide +kernel)

lemma p_34 : Cnt 30482 3290 := cstep 30361 121 3281 9 p_33 (by decide +kernel)

lemma p_35 : Cnt 30604 3302 := cstep 30482 122 3290 12 p_34 (by decide +kernel)

lemma p_36 : Cnt 30727 3314 := cstep 30604 123 3302 12 p_35 (by decide +kernel)

lemma p_37 : Cnt 30850 3325 := cstep 30727 123 3314 11 p_36 (by decide +kernel)

lemma p_38 : Cnt 30973 3338 := cstep 30850 123 3325 13 p_37 (by decide +kernel)

lemma p_39 : Cnt 31097 3350 := cstep 30973 124 3338 12 p_38 (by decide +kernel)

lemma p_40 : Cnt 31221 3363 := cstep 31097 124 3350 13 p_39 (by decide +kernel)

lemma p_41 : Cnt 31346 3379 := cstep 31221 125 3363 16 p_40 (by decide +kernel)

lemma p_42 : Cnt 31472 3386 := cstep 31346 126 3379 7 p_41 (by decide +kernel)

lemma p_43 : Cnt 31597 3399 := cstep 31472 125 3386 13 p_42 (by decide +kernel)

lemma p_44 : Cnt 31724 3411 := cstep 31597 127 3399 12 p_43 (by decide +kernel)

lemma p_45 : Cnt 31851 3422 := cstep 31724 127 3411 11 p_44 (by decide +kernel)

lemma p_46 : Cnt 31978 3430 := cstep 31851 127 3422 8 p_45 (by decide +kernel)

lemma p_47 : Cnt 32106 3445 := cstep 31978 128 3430 15 p_46 (by decide +kernel)

lemma p_48 : Cnt 32235 3457 := cstep 32106 129 3445 12 p_47 (by decide +kernel)

lemma p_49 : Cnt 32363 3471 := cstep 32235 128 3457 14 p_48 (by decide +kernel)

lemma p_50 : Cnt 32493 3486 := cstep 32363 130 3471 15 p_49 (by decide +kernel)

lemma p_51 : Cnt 32623 3502 := cstep 32493 130 3486 16 p_50 (by decide +kernel)

lemma p_52 : Cnt 32753 3512 := cstep 32623 130 3502 10 p_51 (by decide +kernel)

lemma p_53 : Cnt 32884 3524 := cstep 32753 131 3512 12 p_52 (by decide +kernel)

lemma p_54 : Cnt 33016 3539 := cstep 32884 132 3524 15 p_53 (by decide +kernel)

lemma p_55 : Cnt 33148 3551 := cstep 33016 132 3539 12 p_54 (by decide +kernel)

lemma p_56 : Cnt 33281 3562 := cstep 33148 133 3551 11 p_55 (by decide +kernel)

lemma p_57 : Cnt 33414 3579 := cstep 33281 133 3562 17 p_56 (by decide +kernel)

lemma p_58 : Cnt 33547 3590 := cstep 33414 133 3579 11 p_57 (by decide +kernel)

lemma p_59 : Cnt 33682 3608 := cstep 33547 135 3590 18 p_58 (by decide +kernel)

lemma p_60 : Cnt 33816 3622 := cstep 33682 134 3608 14 p_59 (by decide +kernel)

lemma p_61 : Cnt 33952 3635 := cstep 33816 136 3622 13 p_60 (by decide +kernel)

lemma p_62 : Cnt 34087 3644 := cstep 33952 135 3635 9 p_61 (by decide +kernel)

lemma p_63 : Cnt 34224 3656 := cstep 34087 137 3644 12 p_62 (by decide +kernel)

lemma p_64 : Cnt 34361 3671 := cstep 34224 137 3656 15 p_63 (by decide +kernel)

lemma p_65 : Cnt 34498 3684 := cstep 34361 137 3671 13 p_64 (by decide +kernel)

lemma p_66 : Cnt 34636 3699 := cstep 34498 138 3684 15 p_65 (by decide +kernel)

lemma p_67 : Cnt 34775 3714 := cstep 34636 139 3699 15 p_66 (by decide +kernel)

lemma p_68 : Cnt 34914 3726 := cstep 34775 139 3714 12 p_67 (by decide +kernel)

lemma p_69 : Cnt 35053 3735 := cstep 34914 139 3726 9 p_68 (by decide +kernel)

lemma p_70 : Cnt 35194 3751 := cstep 35053 141 3735 16 p_69 (by decide +kernel)

lemma p_71 : Cnt 35334 3764 := cstep 35194 140 3751 13 p_70 (by decide +kernel)

lemma p_72 : Cnt 35476 3777 := cstep 35334 142 3764 13 p_71 (by decide +kernel)

lemma p_73 : Cnt 35618 3793 := cstep 35476 142 3777 16 p_72 (by decide +kernel)

lemma p_74 : Cnt 35760 3800 := cstep 35618 142 3793 7 p_73 (by decide +kernel)

lemma p_75 : Cnt 35903 3814 := cstep 35760 143 3800 14 p_74 (by decide +kernel)

lemma p_76 : Cnt 36047 3829 := cstep 35903 144 3814 15 p_75 (by decide +kernel)

lemma p_77 : Cnt 36191 3841 := cstep 36047 144 3829 12 p_76 (by decide +kernel)

lemma p_78 : Cnt 36336 3855 := cstep 36191 145 3841 14 p_77 (by decide +kernel)

lemma p_79 : Cnt 36481 3868 := cstep 36336 145 3855 13 p_78 (by decide +kernel)

lemma p_80 : Cnt 36627 3882 := cstep 36481 146 3868 14 p_79 (by decide +kernel)

lemma p_81 : Cnt 36773 3898 := cstep 36627 146 3882 16 p_80 (by decide +kernel)

lemma p_82 : Cnt 36921 3915 := cstep 36773 148 3898 17 p_81 (by decide +kernel)

lemma p_83 : Cnt 37068 3931 := cstep 36921 147 3915 16 p_82 (by decide +kernel)

lemma p_84 : Cnt 37217 3942 := cstep 37068 149 3931 11 p_83 (by decide +kernel)

lemma p_85 : Cnt 37365 3957 := cstep 37217 148 3942 15 p_84 (by decide +kernel)

lemma p_86 : Cnt 37515 3971 := cstep 37365 150 3957 14 p_85 (by decide +kernel)

lemma p_87 : Cnt 37665 3990 := cstep 37515 150 3971 19 p_86 (by decide +kernel)

lemma p_88 : Cnt 37816 4000 := cstep 37665 151 3990 10 p_87 (by decide +kernel)

lemma p_89 : Cnt 37967 4012 := cstep 37816 151 4000 12 p_88 (by decide +kernel)

lemma p_90 : Cnt 38119 4024 := cstep 37967 152 4012 12 p_89 (by decide +kernel)

lemma p_91 : Cnt 38271 4038 := cstep 38119 152 4024 14 p_90 (by decide +kernel)

lemma p_92 : Cnt 38424 4052 := cstep 38271 153 4038 14 p_91 (by decide +kernel)

lemma p_93 : Cnt 38578 4064 := cstep 38424 154 4052 12 p_92 (by decide +kernel)

lemma p_94 : Cnt 38732 4082 := cstep 38578 154 4064 18 p_93 (by decide +kernel)

lemma p_95 : Cnt 38887 4096 := cstep 38732 155 4082 14 p_94 (by decide +kernel)

lemma p_96 : Cnt 39043 4110 := cstep 38887 156 4096 14 p_95 (by decide +kernel)

lemma p_97 : Cnt 39199 4126 := cstep 39043 156 4110 16 p_96 (by decide +kernel)

lemma p_98 : Cnt 39356 4142 := cstep 39199 157 4126 16 p_97 (by decide +kernel)

lemma p_99 : Cnt 39513 4158 := cstep 39356 157 4142 16 p_98 (by decide +kernel)

lemma p_100 : Cnt 39671 4170 := cstep 39513 158 4158 12 p_99 (by decide +kernel)

lemma p_101 : Cnt 39830 4186 := cstep 39671 159 4170 16 p_100 (by decide +kernel)

lemma p_102 : Cnt 39989 4202 := cstep 39830 159 4186 16 p_101 (by decide +kernel)

lemma p_103 : Cnt 40149 4216 := cstep 39989 160 4202 14 p_102 (by decide +kernel)

lemma p_104 : Cnt 40310 4231 := cstep 40149 161 4216 15 p_103 (by decide +kernel)

lemma p_105 : Cnt 40471 4241 := cstep 40310 161 4231 10 p_104 (by decide +kernel)

lemma p_106 : Cnt 40633 4258 := cstep 40471 162 4241 17 p_105 (by decide +kernel)

lemma p_107 : Cnt 40795 4270 := cstep 40633 162 4258 12 p_106 (by decide +kernel)

lemma p_108 : Cnt 40959 4288 := cstep 40795 164 4270 18 p_107 (by decide +kernel)

lemma p_109 : Cnt 41122 4302 := cstep 40959 163 4288 14 p_108 (by decide +kernel)

lemma p_110 : Cnt 41287 4323 := cstep 41122 165 4302 21 p_109 (by decide +kernel)

lemma p_111 : Cnt 41452 4335 := cstep 41287 165 4323 12 p_110 (by decide +kernel)

lemma p_112 : Cnt 41618 4353 := cstep 41452 166 4335 18 p_111 (by decide +kernel)

lemma p_113 : Cnt 41784 4369 := cstep 41618 166 4353 16 p_112 (by decide +kernel)

lemma p_114 : Cnt 41952 4385 := cstep 41784 168 4369 16 p_113 (by decide +kernel)

lemma p_115 : Cnt 42119 4403 := cstep 41952 167 4385 18 p_114 (by decide +kernel)

lemma p_116 : Cnt 42288 4420 := cstep 42119 169 4403 17 p_115 (by decide +kernel)

lemma p_117 : Cnt 42457 4439 := cstep 42288 169 4420 19 p_116 (by decide +kernel)

lemma p_118 : Cnt 42627 4455 := cstep 42457 170 4439 16 p_117 (by decide +kernel)

lemma p_119 : Cnt 42797 4475 := cstep 42627 170 4455 20 p_118 (by decide +kernel)

lemma p_120 : Cnt 42969 4492 := cstep 42797 172 4475 17 p_119 (by decide +kernel)

lemma p_121 : Cnt 43140 4506 := cstep 42969 171 4492 14 p_120 (by decide +kernel)

lemma p_122 : Cnt 43313 4518 := cstep 43140 173 4506 12 p_121 (by decide +kernel)

lemma p_123 : Cnt 43486 4532 := cstep 43313 173 4518 14 p_122 (by decide +kernel)

lemma p_124 : Cnt 43660 4549 := cstep 43486 174 4532 17 p_123 (by decide +kernel)

lemma p_125 : Cnt 43835 4564 := cstep 43660 175 4549 15 p_124 (by decide +kernel)

lemma p_126 : Cnt 44010 4579 := cstep 43835 175 4564 15 p_125 (by decide +kernel)

lemma p_127 : Cnt 44186 4598 := cstep 44010 176 4579 19 p_126 (by decide +kernel)

lemma p_128 : Cnt 44363 4614 := cstep 44186 177 4598 16 p_127 (by decide +kernel)

lemma p_129 : Cnt 44540 4630 := cstep 44363 177 4614 16 p_128 (by decide +kernel)

lemma p_130 : Cnt 44719 4648 := cstep 44540 179 4630 18 p_129 (by decide +kernel)

lemma p_131 : Cnt 44897 4665 := cstep 44719 178 4648 17 p_130 (by decide +kernel)

lemma p_132 : Cnt 45077 4679 := cstep 44897 180 4665 14 p_131 (by decide +kernel)

lemma p_133 : Cnt 45257 4694 := cstep 45077 180 4679 15 p_132 (by decide +kernel)

lemma p_134 : Cnt 45438 4713 := cstep 45257 181 4694 19 p_133 (by decide +kernel)

lemma p_135 : Cnt 45620 4728 := cstep 45438 182 4713 15 p_134 (by decide +kernel)

lemma p_136 : Cnt 45803 4743 := cstep 45620 183 4728 15 p_135 (by decide +kernel)

lemma p_137 : Cnt 45986 4760 := cstep 45803 183 4743 17 p_136 (by decide +kernel)

lemma p_138 : Cnt 46170 4775 := cstep 45986 184 4760 15 p_137 (by decide +kernel)

lemma p_139 : Cnt 46354 4794 := cstep 46170 184 4775 19 p_138 (by decide +kernel)

lemma p_140 : Cnt 46540 4809 := cstep 46354 186 4794 15 p_139 (by decide +kernel)

lemma p_141 : Cnt 46726 4828 := cstep 46540 186 4809 19 p_140 (by decide +kernel)

lemma p_142 : Cnt 46913 4846 := cstep 46726 187 4828 18 p_141 (by decide +kernel)

lemma p_143 : Cnt 47101 4858 := cstep 46913 188 4846 12 p_142 (by decide +kernel)

lemma p_144 : Cnt 47289 4875 := cstep 47101 188 4858 17 p_143 (by decide +kernel)

lemma p_145 : Cnt 47478 4893 := cstep 47289 189 4875 18 p_144 (by decide +kernel)

lemma p_146 : Cnt 47668 4914 := cstep 47478 190 4893 21 p_145 (by decide +kernel)

lemma p_147 : Cnt 47859 4933 := cstep 47668 191 4914 19 p_146 (by decide +kernel)

lemma p_148 : Cnt 48050 4950 := cstep 47859 191 4933 17 p_147 (by decide +kernel)

lemma p_149 : Cnt 48242 4965 := cstep 48050 192 4950 15 p_148 (by decide +kernel)

lemma p_150 : Cnt 48435 4981 := cstep 48242 193 4965 16 p_149 (by decide +kernel)

lemma p_151 : Cnt 48629 5002 := cstep 48435 194 4981 21 p_150 (by decide +kernel)

lemma p_152 : Cnt 48824 5022 := cstep 48629 195 5002 20 p_151 (by decide +kernel)

lemma p_153 : Cnt 49019 5037 := cstep 48824 195 5022 15 p_152 (by decide +kernel)

lemma p_154 : Cnt 49215 5060 := cstep 49019 196 5037 23 p_153 (by decide +kernel)

lemma p_155 : Cnt 49412 5077 := cstep 49215 197 5060 17 p_154 (by decide +kernel)

lemma p_156 : Cnt 49609 5095 := cstep 49412 197 5077 18 p_155 (by decide +kernel)

lemma p_157 : Cnt 49808 5115 := cstep 49609 199 5095 20 p_156 (by decide +kernel)

lemma p_158 : Cnt 50007 5133 := cstep 49808 199 5115 18 p_157 (by decide +kernel)

lemma p_159 : Cnt 50207 5153 := cstep 50007 200 5133 20 p_158 (by decide +kernel)

lemma p_160 : Cnt 50408 5172 := cstep 50207 201 5153 19 p_159 (by decide +kernel)

lemma p_161 : Cnt 50610 5191 := cstep 50408 202 5172 19 p_160 (by decide +kernel)

lemma p_162 : Cnt 50812 5204 := cstep 50610 202 5191 13 p_161 (by decide +kernel)

lemma p_163 : Cnt 51015 5223 := cstep 50812 203 5204 19 p_162 (by decide +kernel)

lemma p_164 : Cnt 51219 5241 := cstep 51015 204 5223 18 p_163 (by decide +kernel)

lemma p_165 : Cnt 51424 5260 := cstep 51219 205 5241 19 p_164 (by decide +kernel)

lemma p_166 : Cnt 51630 5283 := cstep 51424 206 5260 23 p_165 (by decide +kernel)

lemma p_167 : Cnt 51837 5303 := cstep 51630 207 5283 20 p_166 (by decide +kernel)

lemma p_168 : Cnt 52044 5322 := cstep 51837 207 5303 19 p_167 (by decide +kernel)

lemma p_169 : Cnt 52252 5341 := cstep 52044 208 5322 19 p_168 (by decide +kernel)

lemma p_170 : Cnt 52461 5358 := cstep 52252 209 5341 17 p_169 (by decide +kernel)

lemma p_171 : Cnt 52671 5376 := cstep 52461 210 5358 18 p_170 (by decide +kernel)

lemma p_172 : Cnt 52882 5395 := cstep 52671 211 5376 19 p_171 (by decide +kernel)

lemma p_173 : Cnt 53093 5416 := cstep 52882 211 5395 21 p_172 (by decide +kernel)

lemma p_174 : Cnt 53305 5437 := cstep 53093 212 5416 21 p_173 (by decide +kernel)

lemma p_175 : Cnt 53519 5454 := cstep 53305 214 5437 17 p_174 (by decide +kernel)

lemma p_176 : Cnt 53733 5476 := cstep 53519 214 5454 22 p_175 (by decide +kernel)

lemma p_177 : Cnt 53948 5496 := cstep 53733 215 5476 20 p_176 (by decide +kernel)

lemma p_178 : Cnt 54164 5514 := cstep 53948 216 5496 18 p_177 (by decide +kernel)

lemma p_179 : Cnt 54380 5532 := cstep 54164 216 5514 18 p_178 (by decide +kernel)

lemma p_180 : Cnt 54598 5556 := cstep 54380 218 5532 24 p_179 (by decide +kernel)

lemma p_181 : Cnt 54816 5575 := cstep 54598 218 5556 19 p_180 (by decide +kernel)

lemma p_182 : Cnt 55035 5593 := cstep 54816 219 5575 18 p_181 (by decide +kernel)

lemma p_183 : Cnt 55255 5614 := cstep 55035 220 5593 21 p_182 (by decide +kernel)

lemma p_184 : Cnt 55477 5631 := cstep 55255 222 5614 17 p_183 (by decide +kernel)

lemma p_185 : Cnt 55698 5653 := cstep 55477 221 5631 22 p_184 (by decide +kernel)

lemma p_186 : Cnt 55921 5675 := cstep 55698 223 5653 22 p_185 (by decide +kernel)

lemma p_187 : Cnt 56145 5696 := cstep 55921 224 5675 21 p_186 (by decide +kernel)

lemma p_188 : Cnt 56369 5713 := cstep 56145 224 5696 17 p_187 (by decide +kernel)

lemma p_189 : Cnt 56595 5738 := cstep 56369 226 5713 25 p_188 (by decide +kernel)

lemma p_190 : Cnt 56821 5761 := cstep 56595 226 5738 23 p_189 (by decide +kernel)

lemma p_191 : Cnt 57049 5785 := cstep 56821 228 5761 24 p_190 (by decide +kernel)

lemma p_192 : Cnt 57277 5809 := cstep 57049 228 5785 24 p_191 (by decide +kernel)

lemma p_193 : Cnt 57506 5828 := cstep 57277 229 5809 19 p_192 (by decide +kernel)

lemma p_194 : Cnt 57736 5849 := cstep 57506 230 5828 21 p_193 (by decide +kernel)

lemma p_195 : Cnt 57967 5870 := cstep 57736 231 5849 21 p_194 (by decide +kernel)

lemma p_196 : Cnt 58199 5893 := cstep 57967 232 5870 23 p_195 (by decide +kernel)

lemma p_197 : Cnt 58432 5916 := cstep 58199 233 5893 23 p_196 (by decide +kernel)

lemma p_198 : Cnt 58665 5935 := cstep 58432 233 5916 19 p_197 (by decide +kernel)

lemma p_199 : Cnt 58900 5951 := cstep 58665 235 5935 16 p_198 (by decide +kernel)

lemma p_200 : Cnt 59136 5979 := cstep 58900 236 5951 28 p_199 (by decide +kernel)

lemma p_201 : Cnt 59372 6001 := cstep 59136 236 5979 22 p_200 (by decide +kernel)

lemma p_202 : Cnt 59610 6023 := cstep 59372 238 6001 22 p_201 (by decide +kernel)

lemma p_203 : Cnt 59848 6047 := cstep 59610 238 6023 24 p_202 (by decide +kernel)

lemma p_204 : Cnt 60087 6064 := cstep 59848 239 6047 17 p_203 (by decide +kernel)

lemma p_205 : Cnt 60184 6076 := cstep 60087 97 6064 12 p_204 (by decide +kernel)

lemma g_0 : Good 30000 := fun k hk hlt => absurd hk (not_le.2 hlt)

lemma g_1 : Good 30120 :=
  extend 30000 30120 3258 1 g_0 (by norm_num) p_31 (by decide +kernel) (by decide +kernel)

lemma g_2 : Good 30240 :=
  extend 30120 30240 3269 2 g_1 (by norm_num) p_32 (by decide +kernel) (by decide +kernel)

lemma g_3 : Good 30361 :=
  extend 30240 30361 3281 3 g_2 (by norm_num) p_33 (by decide +kernel) (by decide +kernel)

lemma g_4 : Good 30482 :=
  extend 30361 30482 3290 4 g_3 (by norm_num) p_34 (by decide +kernel) (by decide +kernel)

lemma g_5 : Good 30604 :=
  extend 30482 30604 3302 5 g_4 (by norm_num) p_35 (by decide +kernel) (by decide +kernel)

lemma g_6 : Good 30727 :=
  extend 30604 30727 3314 6 g_5 (by norm_num) p_36 (by decide +kernel) (by decide +kernel)

lemma g_7 : Good 30850 :=
  extend 30727 30850 3325 7 g_6 (by norm_num) p_37 (by decide +kernel) (by decide +kernel)

lemma g_8 : Good 30973 :=
  extend 30850 30973 3338 8 g_7 (by norm_num) p_38 (by decide +kernel) (by decide +kernel)

lemma g_9 : Good 31097 :=
  extend 30973 31097 3350 9 g_8 (by norm_num) p_39 (by decide +kernel) (by decide +kernel)

lemma g_10 : Good 31221 :=
  extend 31097 31221 3363 10 g_9 (by norm_num) p_40 (by decide +kernel) (by decide +kernel)

lemma g_11 : Good 31346 :=
  extend 31221 31346 3379 11 g_10 (by norm_num) p_41 (by decide +kernel) (by decide +kernel)

lemma g_12 : Good 31472 :=
  extend 31346 31472 3386 12 g_11 (by norm_num) p_42 (by decide +kernel) (by decide +kernel)

lemma g_13 : Good 31597 :=
  extend 31472 31597 3399 13 g_12 (by norm_num) p_43 (by decide +kernel) (by decide +kernel)

lemma g_14 : Good 31724 :=
  extend 31597 31724 3411 14 g_13 (by norm_num) p_44 (by decide +kernel) (by decide +kernel)

lemma g_15 : Good 31851 :=
  extend 31724 31851 3422 15 g_14 (by norm_num) p_45 (by decide +kernel) (by decide +kernel)

lemma g_16 : Good 31978 :=
  extend 31851 31978 3430 16 g_15 (by norm_num) p_46 (by decide +kernel) (by decide +kernel)

lemma g_17 : Good 32106 :=
  extend 31978 32106 3445 17 g_16 (by norm_num) p_47 (by decide +kernel) (by decide +kernel)

lemma g_18 : Good 32235 :=
  extend 32106 32235 3457 18 g_17 (by norm_num) p_48 (by decide +kernel) (by decide +kernel)

lemma g_19 : Good 32363 :=
  extend 32235 32363 3471 19 g_18 (by norm_num) p_49 (by decide +kernel) (by decide +kernel)

lemma g_20 : Good 32493 :=
  extend 32363 32493 3486 20 g_19 (by norm_num) p_50 (by decide +kernel) (by decide +kernel)

lemma g_21 : Good 32623 :=
  extend 32493 32623 3502 21 g_20 (by norm_num) p_51 (by decide +kernel) (by decide +kernel)

lemma g_22 : Good 32753 :=
  extend 32623 32753 3512 22 g_21 (by norm_num) p_52 (by decide +kernel) (by decide +kernel)

lemma g_23 : Good 32884 :=
  extend 32753 32884 3524 23 g_22 (by norm_num) p_53 (by decide +kernel) (by decide +kernel)

lemma g_24 : Good 33016 :=
  extend 32884 33016 3539 24 g_23 (by norm_num) p_54 (by decide +kernel) (by decide +kernel)

lemma g_25 : Good 33148 :=
  extend 33016 33148 3551 25 g_24 (by norm_num) p_55 (by decide +kernel) (by decide +kernel)

lemma g_26 : Good 33281 :=
  extend 33148 33281 3562 26 g_25 (by norm_num) p_56 (by decide +kernel) (by decide +kernel)

lemma g_27 : Good 33414 :=
  extend 33281 33414 3579 27 g_26 (by norm_num) p_57 (by decide +kernel) (by decide +kernel)

lemma g_28 : Good 33547 :=
  extend 33414 33547 3590 28 g_27 (by norm_num) p_58 (by decide +kernel) (by decide +kernel)

lemma g_29 : Good 33682 :=
  extend 33547 33682 3608 29 g_28 (by norm_num) p_59 (by decide +kernel) (by decide +kernel)

lemma g_30 : Good 33816 :=
  extend 33682 33816 3622 30 g_29 (by norm_num) p_60 (by decide +kernel) (by decide +kernel)

lemma g_31 : Good 33952 :=
  extend 33816 33952 3635 31 g_30 (by norm_num) p_61 (by decide +kernel) (by decide +kernel)

lemma g_32 : Good 34087 :=
  extend 33952 34087 3644 32 g_31 (by norm_num) p_62 (by decide +kernel) (by decide +kernel)

lemma g_33 : Good 34224 :=
  extend 34087 34224 3656 33 g_32 (by norm_num) p_63 (by decide +kernel) (by decide +kernel)

lemma g_34 : Good 34361 :=
  extend 34224 34361 3671 34 g_33 (by norm_num) p_64 (by decide +kernel) (by decide +kernel)

lemma g_35 : Good 34498 :=
  extend 34361 34498 3684 35 g_34 (by norm_num) p_65 (by decide +kernel) (by decide +kernel)

lemma g_36 : Good 34636 :=
  extend 34498 34636 3699 36 g_35 (by norm_num) p_66 (by decide +kernel) (by decide +kernel)

lemma g_37 : Good 34775 :=
  extend 34636 34775 3714 37 g_36 (by norm_num) p_67 (by decide +kernel) (by decide +kernel)

lemma g_38 : Good 34914 :=
  extend 34775 34914 3726 38 g_37 (by norm_num) p_68 (by decide +kernel) (by decide +kernel)

lemma g_39 : Good 35053 :=
  extend 34914 35053 3735 39 g_38 (by norm_num) p_69 (by decide +kernel) (by decide +kernel)

lemma g_40 : Good 35194 :=
  extend 35053 35194 3751 40 g_39 (by norm_num) p_70 (by decide +kernel) (by decide +kernel)

lemma g_41 : Good 35334 :=
  extend 35194 35334 3764 41 g_40 (by norm_num) p_71 (by decide +kernel) (by decide +kernel)

lemma g_42 : Good 35476 :=
  extend 35334 35476 3777 42 g_41 (by norm_num) p_72 (by decide +kernel) (by decide +kernel)

lemma g_43 : Good 35618 :=
  extend 35476 35618 3793 43 g_42 (by norm_num) p_73 (by decide +kernel) (by decide +kernel)

lemma g_44 : Good 35760 :=
  extend 35618 35760 3800 44 g_43 (by norm_num) p_74 (by decide +kernel) (by decide +kernel)

lemma g_45 : Good 35903 :=
  extend 35760 35903 3814 45 g_44 (by norm_num) p_75 (by decide +kernel) (by decide +kernel)

lemma g_46 : Good 36047 :=
  extend 35903 36047 3829 46 g_45 (by norm_num) p_76 (by decide +kernel) (by decide +kernel)

lemma g_47 : Good 36191 :=
  extend 36047 36191 3841 47 g_46 (by norm_num) p_77 (by decide +kernel) (by decide +kernel)

lemma g_48 : Good 36336 :=
  extend 36191 36336 3855 48 g_47 (by norm_num) p_78 (by decide +kernel) (by decide +kernel)

lemma g_49 : Good 36481 :=
  extend 36336 36481 3868 49 g_48 (by norm_num) p_79 (by decide +kernel) (by decide +kernel)

lemma g_50 : Good 36627 :=
  extend 36481 36627 3882 50 g_49 (by norm_num) p_80 (by decide +kernel) (by decide +kernel)

lemma g_51 : Good 36773 :=
  extend 36627 36773 3898 51 g_50 (by norm_num) p_81 (by decide +kernel) (by decide +kernel)

lemma g_52 : Good 36921 :=
  extend 36773 36921 3915 52 g_51 (by norm_num) p_82 (by decide +kernel) (by decide +kernel)

lemma g_53 : Good 37068 :=
  extend 36921 37068 3931 53 g_52 (by norm_num) p_83 (by decide +kernel) (by decide +kernel)

lemma g_54 : Good 37217 :=
  extend 37068 37217 3942 54 g_53 (by norm_num) p_84 (by decide +kernel) (by decide +kernel)

lemma g_55 : Good 37365 :=
  extend 37217 37365 3957 55 g_54 (by norm_num) p_85 (by decide +kernel) (by decide +kernel)

lemma g_56 : Good 37515 :=
  extend 37365 37515 3971 56 g_55 (by norm_num) p_86 (by decide +kernel) (by decide +kernel)

lemma g_57 : Good 37665 :=
  extend 37515 37665 3990 57 g_56 (by norm_num) p_87 (by decide +kernel) (by decide +kernel)

lemma g_58 : Good 37816 :=
  extend 37665 37816 4000 58 g_57 (by norm_num) p_88 (by decide +kernel) (by decide +kernel)

lemma g_59 : Good 37967 :=
  extend 37816 37967 4012 59 g_58 (by norm_num) p_89 (by decide +kernel) (by decide +kernel)

lemma g_60 : Good 38119 :=
  extend 37967 38119 4024 60 g_59 (by norm_num) p_90 (by decide +kernel) (by decide +kernel)

lemma g_61 : Good 38271 :=
  extend 38119 38271 4038 61 g_60 (by norm_num) p_91 (by decide +kernel) (by decide +kernel)

lemma g_62 : Good 38424 :=
  extend 38271 38424 4052 62 g_61 (by norm_num) p_92 (by decide +kernel) (by decide +kernel)

lemma g_63 : Good 38578 :=
  extend 38424 38578 4064 63 g_62 (by norm_num) p_93 (by decide +kernel) (by decide +kernel)

lemma g_64 : Good 38732 :=
  extend 38578 38732 4082 64 g_63 (by norm_num) p_94 (by decide +kernel) (by decide +kernel)

lemma g_65 : Good 38887 :=
  extend 38732 38887 4096 65 g_64 (by norm_num) p_95 (by decide +kernel) (by decide +kernel)

lemma g_66 : Good 39043 :=
  extend 38887 39043 4110 66 g_65 (by norm_num) p_96 (by decide +kernel) (by decide +kernel)

lemma g_67 : Good 39199 :=
  extend 39043 39199 4126 67 g_66 (by norm_num) p_97 (by decide +kernel) (by decide +kernel)

lemma g_68 : Good 39356 :=
  extend 39199 39356 4142 68 g_67 (by norm_num) p_98 (by decide +kernel) (by decide +kernel)

lemma g_69 : Good 39513 :=
  extend 39356 39513 4158 69 g_68 (by norm_num) p_99 (by decide +kernel) (by decide +kernel)

lemma g_70 : Good 39671 :=
  extend 39513 39671 4170 70 g_69 (by norm_num) p_100 (by decide +kernel) (by decide +kernel)

lemma g_71 : Good 39830 :=
  extend 39671 39830 4186 71 g_70 (by norm_num) p_101 (by decide +kernel) (by decide +kernel)

lemma g_72 : Good 39989 :=
  extend 39830 39989 4202 72 g_71 (by norm_num) p_102 (by decide +kernel) (by decide +kernel)

lemma g_73 : Good 40149 :=
  extend 39989 40149 4216 73 g_72 (by norm_num) p_103 (by decide +kernel) (by decide +kernel)

lemma g_74 : Good 40310 :=
  extend 40149 40310 4231 74 g_73 (by norm_num) p_104 (by decide +kernel) (by decide +kernel)

lemma g_75 : Good 40471 :=
  extend 40310 40471 4241 75 g_74 (by norm_num) p_105 (by decide +kernel) (by decide +kernel)

lemma g_76 : Good 40633 :=
  extend 40471 40633 4258 76 g_75 (by norm_num) p_106 (by decide +kernel) (by decide +kernel)

lemma g_77 : Good 40795 :=
  extend 40633 40795 4270 77 g_76 (by norm_num) p_107 (by decide +kernel) (by decide +kernel)

lemma g_78 : Good 40959 :=
  extend 40795 40959 4288 78 g_77 (by norm_num) p_108 (by decide +kernel) (by decide +kernel)

lemma g_79 : Good 41122 :=
  extend 40959 41122 4302 79 g_78 (by norm_num) p_109 (by decide +kernel) (by decide +kernel)

lemma g_80 : Good 41287 :=
  extend 41122 41287 4323 80 g_79 (by norm_num) p_110 (by decide +kernel) (by decide +kernel)

lemma g_81 : Good 41452 :=
  extend 41287 41452 4335 81 g_80 (by norm_num) p_111 (by decide +kernel) (by decide +kernel)

lemma g_82 : Good 41618 :=
  extend 41452 41618 4353 82 g_81 (by norm_num) p_112 (by decide +kernel) (by decide +kernel)

lemma g_83 : Good 41784 :=
  extend 41618 41784 4369 83 g_82 (by norm_num) p_113 (by decide +kernel) (by decide +kernel)

lemma g_84 : Good 41952 :=
  extend 41784 41952 4385 84 g_83 (by norm_num) p_114 (by decide +kernel) (by decide +kernel)

lemma g_85 : Good 42119 :=
  extend 41952 42119 4403 85 g_84 (by norm_num) p_115 (by decide +kernel) (by decide +kernel)

lemma g_86 : Good 42288 :=
  extend 42119 42288 4420 86 g_85 (by norm_num) p_116 (by decide +kernel) (by decide +kernel)

lemma g_87 : Good 42457 :=
  extend 42288 42457 4439 87 g_86 (by norm_num) p_117 (by decide +kernel) (by decide +kernel)

lemma g_88 : Good 42627 :=
  extend 42457 42627 4455 88 g_87 (by norm_num) p_118 (by decide +kernel) (by decide +kernel)

lemma g_89 : Good 42797 :=
  extend 42627 42797 4475 89 g_88 (by norm_num) p_119 (by decide +kernel) (by decide +kernel)

lemma g_90 : Good 42969 :=
  extend 42797 42969 4492 90 g_89 (by norm_num) p_120 (by decide +kernel) (by decide +kernel)

lemma g_91 : Good 43140 :=
  extend 42969 43140 4506 91 g_90 (by norm_num) p_121 (by decide +kernel) (by decide +kernel)

lemma g_92 : Good 43313 :=
  extend 43140 43313 4518 92 g_91 (by norm_num) p_122 (by decide +kernel) (by decide +kernel)

lemma g_93 : Good 43486 :=
  extend 43313 43486 4532 93 g_92 (by norm_num) p_123 (by decide +kernel) (by decide +kernel)

lemma g_94 : Good 43660 :=
  extend 43486 43660 4549 94 g_93 (by norm_num) p_124 (by decide +kernel) (by decide +kernel)

lemma g_95 : Good 43835 :=
  extend 43660 43835 4564 95 g_94 (by norm_num) p_125 (by decide +kernel) (by decide +kernel)

lemma g_96 : Good 44010 :=
  extend 43835 44010 4579 96 g_95 (by norm_num) p_126 (by decide +kernel) (by decide +kernel)

lemma g_97 : Good 44186 :=
  extend 44010 44186 4598 97 g_96 (by norm_num) p_127 (by decide +kernel) (by decide +kernel)

lemma g_98 : Good 44363 :=
  extend 44186 44363 4614 98 g_97 (by norm_num) p_128 (by decide +kernel) (by decide +kernel)

lemma g_99 : Good 44540 :=
  extend 44363 44540 4630 99 g_98 (by norm_num) p_129 (by decide +kernel) (by decide +kernel)

lemma g_100 : Good 44719 :=
  extend 44540 44719 4648 100 g_99 (by norm_num) p_130 (by decide +kernel) (by decide +kernel)

lemma g_101 : Good 44897 :=
  extend 44719 44897 4665 101 g_100 (by norm_num) p_131 (by decide +kernel) (by decide +kernel)

lemma g_102 : Good 45077 :=
  extend 44897 45077 4679 102 g_101 (by norm_num) p_132 (by decide +kernel) (by decide +kernel)

lemma g_103 : Good 45257 :=
  extend 45077 45257 4694 103 g_102 (by norm_num) p_133 (by decide +kernel) (by decide +kernel)

lemma g_104 : Good 45438 :=
  extend 45257 45438 4713 104 g_103 (by norm_num) p_134 (by decide +kernel) (by decide +kernel)

lemma g_105 : Good 45620 :=
  extend 45438 45620 4728 105 g_104 (by norm_num) p_135 (by decide +kernel) (by decide +kernel)

lemma g_106 : Good 45803 :=
  extend 45620 45803 4743 106 g_105 (by norm_num) p_136 (by decide +kernel) (by decide +kernel)

lemma g_107 : Good 45986 :=
  extend 45803 45986 4760 107 g_106 (by norm_num) p_137 (by decide +kernel) (by decide +kernel)

lemma g_108 : Good 46170 :=
  extend 45986 46170 4775 108 g_107 (by norm_num) p_138 (by decide +kernel) (by decide +kernel)

lemma g_109 : Good 46354 :=
  extend 46170 46354 4794 109 g_108 (by norm_num) p_139 (by decide +kernel) (by decide +kernel)

lemma g_110 : Good 46540 :=
  extend 46354 46540 4809 110 g_109 (by norm_num) p_140 (by decide +kernel) (by decide +kernel)

lemma g_111 : Good 46726 :=
  extend 46540 46726 4828 111 g_110 (by norm_num) p_141 (by decide +kernel) (by decide +kernel)

lemma g_112 : Good 46913 :=
  extend 46726 46913 4846 112 g_111 (by norm_num) p_142 (by decide +kernel) (by decide +kernel)

lemma g_113 : Good 47101 :=
  extend 46913 47101 4858 113 g_112 (by norm_num) p_143 (by decide +kernel) (by decide +kernel)

lemma g_114 : Good 47289 :=
  extend 47101 47289 4875 114 g_113 (by norm_num) p_144 (by decide +kernel) (by decide +kernel)

lemma g_115 : Good 47478 :=
  extend 47289 47478 4893 115 g_114 (by norm_num) p_145 (by decide +kernel) (by decide +kernel)

lemma g_116 : Good 47668 :=
  extend 47478 47668 4914 116 g_115 (by norm_num) p_146 (by decide +kernel) (by decide +kernel)

lemma g_117 : Good 47859 :=
  extend 47668 47859 4933 117 g_116 (by norm_num) p_147 (by decide +kernel) (by decide +kernel)

lemma g_118 : Good 48050 :=
  extend 47859 48050 4950 118 g_117 (by norm_num) p_148 (by decide +kernel) (by decide +kernel)

lemma g_119 : Good 48242 :=
  extend 48050 48242 4965 119 g_118 (by norm_num) p_149 (by decide +kernel) (by decide +kernel)

lemma g_120 : Good 48435 :=
  extend 48242 48435 4981 120 g_119 (by norm_num) p_150 (by decide +kernel) (by decide +kernel)

lemma g_121 : Good 48629 :=
  extend 48435 48629 5002 121 g_120 (by norm_num) p_151 (by decide +kernel) (by decide +kernel)

lemma g_122 : Good 48824 :=
  extend 48629 48824 5022 122 g_121 (by norm_num) p_152 (by decide +kernel) (by decide +kernel)

lemma g_123 : Good 49019 :=
  extend 48824 49019 5037 123 g_122 (by norm_num) p_153 (by decide +kernel) (by decide +kernel)

lemma g_124 : Good 49215 :=
  extend 49019 49215 5060 124 g_123 (by norm_num) p_154 (by decide +kernel) (by decide +kernel)

lemma g_125 : Good 49412 :=
  extend 49215 49412 5077 125 g_124 (by norm_num) p_155 (by decide +kernel) (by decide +kernel)

lemma g_126 : Good 49609 :=
  extend 49412 49609 5095 126 g_125 (by norm_num) p_156 (by decide +kernel) (by decide +kernel)

lemma g_127 : Good 49808 :=
  extend 49609 49808 5115 127 g_126 (by norm_num) p_157 (by decide +kernel) (by decide +kernel)

lemma g_128 : Good 50007 :=
  extend 49808 50007 5133 128 g_127 (by norm_num) p_158 (by decide +kernel) (by decide +kernel)

lemma g_129 : Good 50207 :=
  extend 50007 50207 5153 129 g_128 (by norm_num) p_159 (by decide +kernel) (by decide +kernel)

lemma g_130 : Good 50408 :=
  extend 50207 50408 5172 130 g_129 (by norm_num) p_160 (by decide +kernel) (by decide +kernel)

lemma g_131 : Good 50610 :=
  extend 50408 50610 5191 131 g_130 (by norm_num) p_161 (by decide +kernel) (by decide +kernel)

lemma g_132 : Good 50812 :=
  extend 50610 50812 5204 132 g_131 (by norm_num) p_162 (by decide +kernel) (by decide +kernel)

lemma g_133 : Good 51015 :=
  extend 50812 51015 5223 133 g_132 (by norm_num) p_163 (by decide +kernel) (by decide +kernel)

lemma g_134 : Good 51219 :=
  extend 51015 51219 5241 134 g_133 (by norm_num) p_164 (by decide +kernel) (by decide +kernel)

lemma g_135 : Good 51424 :=
  extend 51219 51424 5260 135 g_134 (by norm_num) p_165 (by decide +kernel) (by decide +kernel)

lemma g_136 : Good 51630 :=
  extend 51424 51630 5283 136 g_135 (by norm_num) p_166 (by decide +kernel) (by decide +kernel)

lemma g_137 : Good 51837 :=
  extend 51630 51837 5303 137 g_136 (by norm_num) p_167 (by decide +kernel) (by decide +kernel)

lemma g_138 : Good 52044 :=
  extend 51837 52044 5322 138 g_137 (by norm_num) p_168 (by decide +kernel) (by decide +kernel)

lemma g_139 : Good 52252 :=
  extend 52044 52252 5341 139 g_138 (by norm_num) p_169 (by decide +kernel) (by decide +kernel)

lemma g_140 : Good 52461 :=
  extend 52252 52461 5358 140 g_139 (by norm_num) p_170 (by decide +kernel) (by decide +kernel)

lemma g_141 : Good 52671 :=
  extend 52461 52671 5376 141 g_140 (by norm_num) p_171 (by decide +kernel) (by decide +kernel)

lemma g_142 : Good 52882 :=
  extend 52671 52882 5395 142 g_141 (by norm_num) p_172 (by decide +kernel) (by decide +kernel)

lemma g_143 : Good 53093 :=
  extend 52882 53093 5416 143 g_142 (by norm_num) p_173 (by decide +kernel) (by decide +kernel)

lemma g_144 : Good 53305 :=
  extend 53093 53305 5437 144 g_143 (by norm_num) p_174 (by decide +kernel) (by decide +kernel)

lemma g_145 : Good 53519 :=
  extend 53305 53519 5454 145 g_144 (by norm_num) p_175 (by decide +kernel) (by decide +kernel)

lemma g_146 : Good 53733 :=
  extend 53519 53733 5476 146 g_145 (by norm_num) p_176 (by decide +kernel) (by decide +kernel)

lemma g_147 : Good 53948 :=
  extend 53733 53948 5496 147 g_146 (by norm_num) p_177 (by decide +kernel) (by decide +kernel)

lemma g_148 : Good 54164 :=
  extend 53948 54164 5514 148 g_147 (by norm_num) p_178 (by decide +kernel) (by decide +kernel)

lemma g_149 : Good 54380 :=
  extend 54164 54380 5532 149 g_148 (by norm_num) p_179 (by decide +kernel) (by decide +kernel)

lemma g_150 : Good 54598 :=
  extend 54380 54598 5556 150 g_149 (by norm_num) p_180 (by decide +kernel) (by decide +kernel)

lemma g_151 : Good 54816 :=
  extend 54598 54816 5575 151 g_150 (by norm_num) p_181 (by decide +kernel) (by decide +kernel)

lemma g_152 : Good 55035 :=
  extend 54816 55035 5593 152 g_151 (by norm_num) p_182 (by decide +kernel) (by decide +kernel)

lemma g_153 : Good 55255 :=
  extend 55035 55255 5614 153 g_152 (by norm_num) p_183 (by decide +kernel) (by decide +kernel)

lemma g_154 : Good 55477 :=
  extend 55255 55477 5631 154 g_153 (by norm_num) p_184 (by decide +kernel) (by decide +kernel)

lemma g_155 : Good 55698 :=
  extend 55477 55698 5653 155 g_154 (by norm_num) p_185 (by decide +kernel) (by decide +kernel)

lemma g_156 : Good 55921 :=
  extend 55698 55921 5675 156 g_155 (by norm_num) p_186 (by decide +kernel) (by decide +kernel)

lemma g_157 : Good 56145 :=
  extend 55921 56145 5696 157 g_156 (by norm_num) p_187 (by decide +kernel) (by decide +kernel)

lemma g_158 : Good 56369 :=
  extend 56145 56369 5713 158 g_157 (by norm_num) p_188 (by decide +kernel) (by decide +kernel)

lemma g_159 : Good 56595 :=
  extend 56369 56595 5738 159 g_158 (by norm_num) p_189 (by decide +kernel) (by decide +kernel)

lemma g_160 : Good 56821 :=
  extend 56595 56821 5761 160 g_159 (by norm_num) p_190 (by decide +kernel) (by decide +kernel)

lemma g_161 : Good 57049 :=
  extend 56821 57049 5785 161 g_160 (by norm_num) p_191 (by decide +kernel) (by decide +kernel)

lemma g_162 : Good 57277 :=
  extend 57049 57277 5809 162 g_161 (by norm_num) p_192 (by decide +kernel) (by decide +kernel)

lemma g_163 : Good 57506 :=
  extend 57277 57506 5828 163 g_162 (by norm_num) p_193 (by decide +kernel) (by decide +kernel)

lemma g_164 : Good 57736 :=
  extend 57506 57736 5849 164 g_163 (by norm_num) p_194 (by decide +kernel) (by decide +kernel)

lemma g_165 : Good 57967 :=
  extend 57736 57967 5870 165 g_164 (by norm_num) p_195 (by decide +kernel) (by decide +kernel)

lemma g_166 : Good 58199 :=
  extend 57967 58199 5893 166 g_165 (by norm_num) p_196 (by decide +kernel) (by decide +kernel)

lemma g_167 : Good 58432 :=
  extend 58199 58432 5916 167 g_166 (by norm_num) p_197 (by decide +kernel) (by decide +kernel)

lemma g_168 : Good 58665 :=
  extend 58432 58665 5935 168 g_167 (by norm_num) p_198 (by decide +kernel) (by decide +kernel)

lemma g_169 : Good 58900 :=
  extend 58665 58900 5951 169 g_168 (by norm_num) p_199 (by decide +kernel) (by decide +kernel)

lemma g_170 : Good 59136 :=
  extend 58900 59136 5979 170 g_169 (by norm_num) p_200 (by decide +kernel) (by decide +kernel)

lemma g_171 : Good 59372 :=
  extend 59136 59372 6001 171 g_170 (by norm_num) p_201 (by decide +kernel) (by decide +kernel)

lemma g_172 : Good 59610 :=
  extend 59372 59610 6023 172 g_171 (by norm_num) p_202 (by decide +kernel) (by decide +kernel)

lemma g_173 : Good 59848 :=
  extend 59610 59848 6047 173 g_172 (by norm_num) p_203 (by decide +kernel) (by decide +kernel)

lemma g_174 : Good 60087 :=
  extend 59848 60087 6064 174 g_173 (by norm_num) p_204 (by decide +kernel) (by decide +kernel)

lemma g_175 : Good 60184 :=
  extend 60087 60184 6076 175 g_174 (by norm_num) p_205 (by decide +kernel) (by decide +kernel)

end OMA930b

theorem OMA.solution :
    OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1.H2 :=
  fun k hk hlt => OMA930b.g_175 k hk hlt
