import OMAReductions.R_oeis_a227864_R1
import Mathlib

set_option maxHeartbeats 80000000 in
theorem OMA.solution : OMA.R_oeis_a227864_R1.H1 := by
  intro p hp3 hple hpp
  have hk : (p - 3) / 100 ≤ 19 := by omega
  interval_cases k : (p - 3) / 100
  · have hlo : 3 ≤ p := by omega
    have hhi : p ≤ 102 := by omega
    interval_cases p
    · refine ⟨6, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 3 6 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨7, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 5 7 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨9, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 7 9 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨13, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 11 13 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨15, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 13 15 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨21, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 17 21 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨21, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 19 21 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨30, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 23 30 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨31, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 29 31 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨35, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 31 35 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨39, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 37 39 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨43, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 41 43 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨49, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 43 49 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨49, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 47 49 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨55, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 53 55 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨63, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 59 63 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨63, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 61 63 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨73, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 67 73 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨77, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 71 77 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨77, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 73 77 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨81, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 79 81 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨85, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 83 85 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨99, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 89 99 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨99, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 97 99 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨105, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 101 105 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 103 ≤ p := by omega
    have hhi : p ≤ 202 := by omega
    interval_cases p
    · refine ⟨105, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 103 105 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨109, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 107 109 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨113, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 109 113 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨115, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 113 115 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨129, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 127 129 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨133, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 131 133 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨139, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 137 139 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨141, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 139 141 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨151, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 149 151 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨153, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 151 153 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨161, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 157 161 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨165, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 163 165 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨173, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 167 173 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨177, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 173 177 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨185, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 179 185 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨183, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 181 183 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨195, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 191 195 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨195, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 193 195 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨199, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 197 199 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨205, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 199 205 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 203 ≤ p := by omega
    have hhi : p ≤ 302 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨213, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 211 213 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨227, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 223 227 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨231, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 227 231 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨231, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 229 231 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨235, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 233 235 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨241, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 239 241 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨245, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 241 245 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨255, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 251 255 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨259, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 257 259 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨265, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 263 265 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨275, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 269 275 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨273, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 271 273 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨283, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 277 283 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨287, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 281 287 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨287, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 283 287 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨295, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 293 295 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 303 ≤ p := by omega
    have hhi : p ≤ 402 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨311, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 307 311 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨315, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 311 315 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨315, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 313 315 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨321, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 317 321 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨337, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 331 337 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨345, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 337 345 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨349, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 347 349 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨357, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 349 357 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨363, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 353 363 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨361, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 359 361 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨371, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 367 371 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨375, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 373 375 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨381, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 379 381 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨387, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 383 387 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨391, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 389 391 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨405, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 397 405 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨403, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 401 403 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 403 ≤ p := by omega
    have hhi : p ≤ 502 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨413, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 409 413 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨427, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 419 427 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨423, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 421 423 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨433, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 431 433 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨439, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 433 439 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨443, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 439 443 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨445, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 443 445 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨451, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 449 451 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨461, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 457 461 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨463, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 461 463 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨469, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 463 469 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨469, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 467 469 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨489, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 479 489 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨489, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 487 489 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨501, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 491 501 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨503, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 499 503 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 503 ≤ p := by omega
    have hhi : p ≤ 602 := by omega
    interval_cases p
    · refine ⟨505, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 503 505 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨511, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 509 511 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨529, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 521 529 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨525, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 523 525 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨543, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 541 543 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨549, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 547 549 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨559, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 557 559 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨567, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 563 567 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨571, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 569 571 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨573, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 571 573 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨583, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 577 583 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨591, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 587 591 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨595, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 593 595 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨601, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 599 601 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨603, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 601 603 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 603 ≤ p := by omega
    have hhi : p ≤ 702 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨609, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 607 609 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨623, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 613 623 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨623, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 617 623 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨627, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 619 627 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨637, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 631 637 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨645, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 641 645 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨645, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 643 645 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨651, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 647 651 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨655, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 653 655 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨661, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 659 661 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨671, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 661 671 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨675, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 673 675 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨679, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 677 679 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨701, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 683 701 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨693, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 691 693 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨703, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 701 703 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 703 ≤ p := by omega
    have hhi : p ≤ 802 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨713, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 709 713 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨725, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 719 725 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨733, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 727 733 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨735, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 733 735 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨741, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 739 741 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨749, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 743 749 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨753, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 751 753 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨763, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 757 763 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨773, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 761 773 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨771, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 769 771 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨783, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 773 783 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨795, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 787 795 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨809, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 797 809 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 803 ≤ p := by omega
    have hhi : p ≤ 902 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨811, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 809 811 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨823, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 811 823 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨823, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 821 823 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨827, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 823 827 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨833, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 827 833 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨833, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 829 833 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨841, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 839 841 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨855, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 853 855 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨861, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 857 861 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨871, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 859 871 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨867, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 863 867 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨879, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 877 879 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨893, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 881 893 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨885, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 883 885 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨889, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 887 889 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 903 ≤ p := by omega
    have hhi : p ≤ 1002 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨913, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 907 913 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨913, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 911 913 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨923, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 919 923 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨931, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 929 931 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨939, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 937 939 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨945, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 941 945 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨965, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 947 965 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨965, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 953 965 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨979, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 967 979 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨973, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 971 973 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨987, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 977 987 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨991, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 983 991 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨997, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 991 997 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1005, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 997 1005 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 1003 ≤ p := by omega
    have hhi : p ≤ 1102 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1011, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1009 1011 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1019, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1013 1019 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1021, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1019 1021 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1025, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1021 1025 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1045, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1031 1045 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1035, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1033 1035 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1045, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1039 1045 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1055, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1049 1055 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1053, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1051 1053 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1065, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1061 1065 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1067, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1063 1067 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1071, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1069 1071 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1089, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1087 1089 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1097, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1091 1097 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1095, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1093 1095 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1105, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1097 1105 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 1103 ≤ p := by omega
    have hhi : p ≤ 1202 := by omega
    interval_cases p
    · refine ⟨1105, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1103 1105 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1113, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1109 1113 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1119, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1117 1119 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1129, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1123 1129 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1131, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1129 1131 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1157, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1151 1157 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1157, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1153 1157 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1165, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1163 1165 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1173, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1171 1173 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1189, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1181 1189 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1193, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1187 1193 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1197, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1193 1197 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1203, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1201 1203 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 1203 ≤ p := by omega
    have hhi : p ≤ 1302 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1217, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1213 1217 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1219, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1217 1219 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1225, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1223 1225 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1231, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1229 1231 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1237, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1231 1237 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1241, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1237 1241 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1257, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1249 1257 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1261, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1259 1261 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1283, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1277 1283 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1283, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1279 1283 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1285, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1283 1285 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1291, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1289 1291 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1297, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1291 1297 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1299, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1297 1299 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1319, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1301 1319 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 1303 ≤ p := by omega
    have hhi : p ≤ 1402 := by omega
    interval_cases p
    · refine ⟨1305, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1303 1305 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1311, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1307 1311 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1323, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1319 1323 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1329, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1321 1329 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1331, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1327 1331 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1365, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1361 1365 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1369, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1367 1369 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1375, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1373 1375 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1383, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1381 1383 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1401, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1399 1401 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 1403 ≤ p := by omega
    have hhi : p ≤ 1502 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1421, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1409 1421 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1425, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1423 1425 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1439, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1427 1439 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1431, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1429 1431 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1437, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1433 1437 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1445, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1439 1445 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1451, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1447 1451 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1457, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1451 1457 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1461, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1453 1461 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1465, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1459 1465 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1481, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1471 1481 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1483, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1481 1483 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1495, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1483 1495 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1491, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1487 1491 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1491, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1489 1491 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1501, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1493 1501 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1505, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1499 1505 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 1503 ≤ p := by omega
    have hhi : p ≤ 1602 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1513, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1511 1513 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1525, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1523 1525 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1537, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1531 1537 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1549, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1543 1549 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1553, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1549 1553 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1561, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1553 1561 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1567, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1559 1567 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1569, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1567 1569 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1577, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1571 1577 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1581, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1579 1581 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1591, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1583 1591 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1605, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1597 1605 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1603, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1601 1603 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 1603 ≤ p := by omega
    have hhi : p ≤ 1702 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1613, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1607 1613 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1615, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1609 1615 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1617, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1613 1617 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1621, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1619 1621 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1623, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1621 1623 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1637, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1627 1637 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1639, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1637 1639 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1659, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1657 1659 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1681, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1663 1681 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1679, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1667 1679 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1673, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1669 1673 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1699, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1693 1699 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1701, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1697 1701 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1701, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1699 1701 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
  · have hlo : 1703 ≤ p := by omega
    have hhi : p ≤ 1802 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1715, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1709 1715 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1733, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1721 1733 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1733, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1723 1733 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1741, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1733 1741 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1747, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1741 1747 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1749, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1747 1749 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1759, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1753 1759 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1765, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1759 1765 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1781, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1777 1781 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1799, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1783 1799 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1789, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1787 1789 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1791, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1789 1791 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1803, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1801 1803 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 1803 ≤ p := by omega
    have hhi : p ≤ 1902 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1817, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1811 1817 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1827, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1823 1827 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1833, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1831 1833 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1849, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1847 1849 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1863, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1861 1863 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1869, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1867 1869 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1881, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1871 1881 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1875, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1873 1875 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1879, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1877 1879 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1883, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1879 1883 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1893, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1889 1893 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1903, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1901 1903 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
  · have hlo : 1903 ≤ p := by omega
    have hhi : p ≤ 2000 := by omega
    interval_cases p
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1911, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1907 1911 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1919, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1913 1919 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1933, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1931 1933 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1945, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1933 1945 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1957, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1949 1957 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨1965, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1951 1965 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1975, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1973 1975 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1981, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1979 1981 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1989, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1987 1989 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨1997, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1993 1997 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · norm_num at hpp
    · norm_num at hpp
    · refine ⟨2003, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1997 2003 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
    · refine ⟨2007, by decide, ?_⟩
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal 1999 2007 (by decide) (by decide) (by decide)]
      norm_num
    · norm_num at hpp
