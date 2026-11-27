import OMAReductions.R_OeisA238568_conjecture_2_R1

-- Step OeisA238568.conjecture_2.R1.H1
-- Credit: @caa1982

private lemma pc_step (a b c d : ℕ) (ha : Nat.primeCounting a = c)
    (hb : Nat.count (fun j => Nat.Prime (a + 1 + j)) b = d) :
    Nat.primeCounting (a + b) = c + d := by
  unfold Nat.primeCounting Nat.primeCounting' at ha ⊢
  rw [show a + b + 1 = (a + 1) + b by omega, Nat.count_add, ha, hb]

set_option maxHeartbeats 2000000 in
private lemma a_41 : OeisA238568.a 41 = 1 := by
  have h0 : Nat.primeCounting 0 = 0 := by decide
  have h1 : Nat.primeCounting 41 = 13 := pc_step 0 41 0 13 h0 (by decide +kernel)
  have h2 : Nat.primeCounting 82 = 22 := pc_step 41 41 13 9 h1 (by decide +kernel)
  have h3 : Nat.primeCounting 123 = 30 := pc_step 82 41 22 8 h2 (by decide +kernel)
  have h4 : Nat.primeCounting 164 = 38 := pc_step 123 41 30 8 h3 (by decide +kernel)
  have h5 : Nat.primeCounting 205 = 46 := pc_step 164 41 38 8 h4 (by decide +kernel)
  have h6 : Nat.primeCounting 246 = 53 := pc_step 205 41 46 7 h5 (by decide +kernel)
  have h7 : Nat.primeCounting 287 = 61 := pc_step 246 41 53 8 h6 (by decide +kernel)
  have h8 : Nat.primeCounting 328 = 66 := pc_step 287 41 61 5 h7 (by decide +kernel)
  have h9 : Nat.primeCounting 369 = 73 := pc_step 328 41 66 7 h8 (by decide +kernel)
  have h10 : Nat.primeCounting 410 = 80 := pc_step 369 41 73 7 h9 (by decide +kernel)
  have h11 : Nat.primeCounting 451 = 87 := pc_step 410 41 80 7 h10 (by decide +kernel)
  have h12 : Nat.primeCounting 492 = 94 := pc_step 451 41 87 7 h11 (by decide +kernel)
  have h13 : Nat.primeCounting 533 = 99 := pc_step 492 41 94 5 h12 (by decide +kernel)
  have h14 : Nat.primeCounting 574 = 105 := pc_step 533 41 99 6 h13 (by decide +kernel)
  have h15 : Nat.primeCounting 615 = 112 := pc_step 574 41 105 7 h14 (by decide +kernel)
  have h16 : Nat.primeCounting 656 = 119 := pc_step 615 41 112 7 h15 (by decide +kernel)
  have h17 : Nat.primeCounting 697 = 125 := pc_step 656 41 119 6 h16 (by decide +kernel)
  have h18 : Nat.primeCounting 738 = 130 := pc_step 697 41 125 5 h17 (by decide +kernel)
  have h19 : Nat.primeCounting 779 = 137 := pc_step 738 41 130 7 h18 (by decide +kernel)
  have h20 : Nat.primeCounting 820 = 141 := pc_step 779 41 137 4 h19 (by decide +kernel)
  have h21 : Nat.primeCounting 861 = 149 := pc_step 820 41 141 8 h20 (by decide +kernel)
  have h22 : Nat.primeCounting 902 = 154 := pc_step 861 41 149 5 h21 (by decide +kernel)
  have h23 : Nat.primeCounting 943 = 160 := pc_step 902 41 154 6 h22 (by decide +kernel)
  have h24 : Nat.primeCounting 984 = 166 := pc_step 943 41 160 6 h23 (by decide +kernel)
  have h25 : Nat.primeCounting 1025 = 172 := pc_step 984 41 166 6 h24 (by decide +kernel)
  have h26 : Nat.primeCounting 1066 = 179 := pc_step 1025 41 172 7 h25 (by decide +kernel)
  have h27 : Nat.primeCounting 1107 = 185 := pc_step 1066 41 179 6 h26 (by decide +kernel)
  have h28 : Nat.primeCounting 1148 = 189 := pc_step 1107 41 185 4 h27 (by decide +kernel)
  have h29 : Nat.primeCounting 1189 = 195 := pc_step 1148 41 189 6 h28 (by decide +kernel)
  have h30 : Nat.primeCounting 1230 = 201 := pc_step 1189 41 195 6 h29 (by decide +kernel)
  have h31 : Nat.primeCounting 1271 = 205 := pc_step 1230 41 201 4 h30 (by decide +kernel)
  have h32 : Nat.primeCounting 1312 = 214 := pc_step 1271 41 205 9 h31 (by decide +kernel)
  have h33 : Nat.primeCounting 1353 = 217 := pc_step 1312 41 214 3 h32 (by decide +kernel)
  have h34 : Nat.primeCounting 1394 = 221 := pc_step 1353 41 217 4 h33 (by decide +kernel)
  have h35 : Nat.primeCounting 1435 = 227 := pc_step 1394 41 221 6 h34 (by decide +kernel)
  have h36 : Nat.primeCounting 1476 = 233 := pc_step 1435 41 227 6 h35 (by decide +kernel)
  have h37 : Nat.primeCounting 1517 = 240 := pc_step 1476 41 233 7 h36 (by decide +kernel)
  have h38 : Nat.primeCounting 1558 = 245 := pc_step 1517 41 240 5 h37 (by decide +kernel)
  have h39 : Nat.primeCounting 1599 = 251 := pc_step 1558 41 245 6 h38 (by decide +kernel)
  have h40 : Nat.primeCounting 1640 = 259 := pc_step 1599 41 251 8 h39 (by decide +kernel)
  unfold OeisA238568.a
  have hfilt : (Finset.Ico 1 41).filter (fun k => Nat.Prime (41 ^ 2 - Nat.primeCounting (k * 41))) = {10} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hp⟩
      interval_cases k
      · exfalso; rw [show 1 * 41 = 41 by rfl, h1] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 2 * 41 = 82 by rfl, h2] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 3 * 41 = 123 by rfl, h3] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 4 * 41 = 164 by rfl, h4] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 5 * 41 = 205 by rfl, h5] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 6 * 41 = 246 by rfl, h6] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 7 * 41 = 287 by rfl, h7] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 8 * 41 = 328 by rfl, h8] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 9 * 41 = 369 by rfl, h9] at hp; exact absurd hp (by decide +kernel)
      · rfl
      · exfalso; rw [show 11 * 41 = 451 by rfl, h11] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 12 * 41 = 492 by rfl, h12] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 13 * 41 = 533 by rfl, h13] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 14 * 41 = 574 by rfl, h14] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 15 * 41 = 615 by rfl, h15] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 16 * 41 = 656 by rfl, h16] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 17 * 41 = 697 by rfl, h17] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 18 * 41 = 738 by rfl, h18] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 19 * 41 = 779 by rfl, h19] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 20 * 41 = 820 by rfl, h20] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 21 * 41 = 861 by rfl, h21] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 22 * 41 = 902 by rfl, h22] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 23 * 41 = 943 by rfl, h23] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 24 * 41 = 984 by rfl, h24] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 25 * 41 = 1025 by rfl, h25] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 26 * 41 = 1066 by rfl, h26] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 27 * 41 = 1107 by rfl, h27] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 28 * 41 = 1148 by rfl, h28] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 29 * 41 = 1189 by rfl, h29] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 30 * 41 = 1230 by rfl, h30] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 31 * 41 = 1271 by rfl, h31] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 32 * 41 = 1312 by rfl, h32] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 33 * 41 = 1353 by rfl, h33] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 34 * 41 = 1394 by rfl, h34] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 35 * 41 = 1435 by rfl, h35] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 36 * 41 = 1476 by rfl, h36] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 37 * 41 = 1517 by rfl, h37] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 38 * 41 = 1558 by rfl, h38] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 39 * 41 = 1599 by rfl, h39] at hp; exact absurd hp (by decide +kernel)
      · exfalso; rw [show 40 * 41 = 1640 by rfl, h40] at hp; exact absurd hp (by decide +kernel)
    · rintro rfl
      refine ⟨by decide, ?_⟩
      rw [show 10 * 41 = 410 by rfl, h10]; decide +kernel
  rw [hfilt, Finset.card_singleton]

theorem OMA.solution : OMA.R_OeisA238568_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact a_41
