import OMAStatements.S_oeis_a061062

-- Complete refutation (counterexample p = 20879) of OEIS A061062 via chunked modular verification
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a061062

private def stepMod (m : ℕ) : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | (k, f, s) =>
    let k' := k + 1
    let f' := (f * k') % m
    let s' := (s + f' * f') % m
    (k', f', s')

private def iterPow {α : Type} (f : α → α) : ℕ → α → α
  | 0, x => f x
  | d + 1, x => iterPow f d (iterPow f d x)

private def ModInv (m : ℕ) (st : ℕ × ℕ × ℕ) : Prop :=
  st.2.1 = st.1.factorial % m ∧
    st.2.2 = (∑ j ∈ Finset.range (st.1 + 1), j.factorial ^ 2) % m

private lemma stepMod_inv (m : ℕ) {st : ℕ × ℕ × ℕ} (h : ModInv m st) :
    ModInv m (stepMod m st) := by
  rcases st with ⟨k, f, s⟩
  obtain ⟨hf, hs⟩ := h
  dsimp only [ModInv, stepMod] at hf hs ⊢
  have hfac : f * (k + 1) % m = (k + 1).factorial % m := by
    rw [hf, Nat.factorial_succ, mul_comm (k + 1), Nat.mod_mul_mod]
  refine ⟨hfac, ?_⟩
  rw [Finset.sum_range_succ, sq, hs, hfac]
  simp [Nat.add_mod, Nat.mul_mod]

private lemma iterPow_inv (m : ℕ) (d : ℕ) :
    ∀ st, ModInv m st → ModInv m (iterPow (stepMod m) d st) := by
  induction d with
  | zero => intro st h; exact stepMod_inv m h
  | succ d ih => intro st h; exact ih _ (ih st h)

private lemma chunk_step {d : ℕ} {a b : ℕ × ℕ × ℕ}
    (ha : ModInv 20879 a) (heq : iterPow (stepMod 20879) d a = b) : ModInv 20879 b := by
  rw [← heq]
  exact iterPow_inv 20879 d a ha

private lemma inv_0 : ModInv 20879 (0, 1, 1) := by unfold ModInv; simp

private lemma inv_blk_1 : ModInv 20879 (512, 20645, 15793) := by
  have h0 := inv_0
  have h1 : ModInv 20879 (32, 19209, 7621) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (64, 206, 14905) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (96, 7779, 4560) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (128, 1967, 8650) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (160, 12950, 17024) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (192, 5954, 12127) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (224, 16735, 3751) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (256, 20859, 8388) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (288, 18876, 6706) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (320, 8564, 12898) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (352, 12116, 11508) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (384, 8998, 7930) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (416, 17045, 1363) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (448, 12957, 13522) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (480, 8813, 11833) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (512, 20645, 15793) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_2 : ModInv 20879 (1024, 9046, 13568) := by
  have h0 := inv_blk_1
  have h1 : ModInv 20879 (544, 9505, 9363) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (576, 20323, 3537) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (608, 15109, 11059) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (640, 2316, 1667) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (672, 16328, 12031) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (704, 3311, 10034) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (736, 14466, 18710) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (768, 16063, 14115) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (800, 20123, 14050) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (832, 19356, 17204) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (864, 9247, 11208) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (896, 14160, 4576) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (928, 2490, 5465) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (960, 15534, 20047) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (992, 19497, 3764) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (1024, 9046, 13568) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_3 : ModInv 20879 (1536, 422, 11993) := by
  have h0 := inv_blk_2
  have h1 : ModInv 20879 (1056, 18981, 10219) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (1088, 16411, 13590) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (1120, 17757, 16802) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (1152, 10335, 7565) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (1184, 245, 2463) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (1216, 1693, 114) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (1248, 4497, 6212) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (1280, 13565, 8245) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (1312, 10261, 5965) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (1344, 16269, 7447) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (1376, 16349, 18327) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (1408, 2503, 2493) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (1440, 5988, 22) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (1472, 10528, 2169) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (1504, 20536, 9843) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (1536, 422, 11993) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_4 : ModInv 20879 (2048, 17526, 16933) := by
  have h0 := inv_blk_3
  have h1 : ModInv 20879 (1568, 18439, 8057) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (1600, 5781, 17918) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (1632, 15516, 16430) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (1664, 18928, 2170) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (1696, 1938, 17732) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (1728, 1103, 10631) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (1760, 257, 2619) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (1792, 4969, 19198) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (1824, 12130, 12676) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (1856, 18527, 16551) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (1888, 7626, 6667) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (1920, 1479, 15712) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (1952, 19464, 5720) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (1984, 20464, 13983) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (2016, 3911, 3726) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (2048, 17526, 16933) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_5 : ModInv 20879 (2560, 7831, 20575) := by
  have h0 := inv_blk_4
  have h1 : ModInv 20879 (2080, 5349, 16628) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (2112, 11021, 15384) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (2144, 10638, 19374) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (2176, 19135, 18958) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (2208, 2181, 1726) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (2240, 13958, 13274) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (2272, 4718, 10275) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (2304, 1677, 2886) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (2336, 4246, 13026) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (2368, 18035, 459) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (2400, 3983, 14367) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (2432, 3161, 20421) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (2464, 15755, 1874) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (2496, 4548, 9283) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (2528, 2469, 6830) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (2560, 7831, 20575) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_6 : ModInv 20879 (3072, 5563, 20553) := by
  have h0 := inv_blk_5
  have h1 : ModInv 20879 (2592, 1391, 4130) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (2624, 1813, 6304) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (2656, 6413, 1759) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (2688, 5733, 2190) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (2720, 16373, 11717) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (2752, 5774, 17497) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (2784, 9464, 5102) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (2816, 3804, 18708) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (2848, 2796, 19208) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (2880, 12011, 201) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (2912, 12280, 19778) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (2944, 4326, 4752) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (2976, 7009, 4109) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (3008, 2673, 19448) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (3040, 17963, 17268) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (3072, 5563, 20553) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_7 : ModInv 20879 (3584, 1465, 18810) := by
  have h0 := inv_blk_6
  have h1 : ModInv 20879 (3104, 12547, 1573) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (3136, 2, 1259) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (3168, 12166, 5640) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (3200, 9644, 19802) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (3232, 9783, 8348) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (3264, 10634, 16117) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (3296, 15417, 6866) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (3328, 10638, 19131) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (3360, 19433, 17601) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (3392, 13444, 14020) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (3424, 7296, 20036) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (3456, 14044, 8389) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (3488, 5124, 17108) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (3520, 6087, 14549) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (3552, 3704, 7509) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (3584, 1465, 18810) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_8 : ModInv 20879 (4096, 8127, 18976) := by
  have h0 := inv_blk_7
  have h1 : ModInv 20879 (3616, 907, 7224) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (3648, 19333, 10103) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (3680, 6562, 12568) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (3712, 12683, 12808) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (3744, 6846, 8273) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (3776, 14076, 16720) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (3808, 19037, 14739) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (3840, 11132, 19833) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (3872, 12059, 7058) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (3904, 11393, 11416) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (3936, 11407, 3996) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (3968, 12780, 17716) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (4000, 15853, 15276) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (4032, 20325, 17546) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (4064, 19970, 10095) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (4096, 8127, 18976) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_9 : ModInv 20879 (4608, 14266, 3592) := by
  have h0 := inv_blk_8
  have h1 : ModInv 20879 (4128, 19186, 5563) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (4160, 8620, 14107) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (4192, 16391, 13894) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (4224, 18710, 20560) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (4256, 12408, 12823) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (4288, 4547, 3976) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (4320, 2231, 522) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (4352, 13714, 16303) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (4384, 1409, 19575) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (4416, 14840, 15586) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (4448, 14330, 2204) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (4480, 19000, 17207) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (4512, 8899, 16185) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (4544, 12931, 240) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (4576, 199, 9692) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (4608, 14266, 3592) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_10 : ModInv 20879 (5120, 4252, 763) := by
  have h0 := inv_blk_9
  have h1 : ModInv 20879 (4640, 12218, 5304) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (4672, 538, 17574) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (4704, 2816, 16275) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (4736, 11085, 11646) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (4768, 5488, 16819) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (4800, 18394, 4626) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (4832, 2184, 18255) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (4864, 7089, 20491) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (4896, 10863, 19019) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (4928, 18863, 12593) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (4960, 17323, 2542) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (4992, 13760, 12343) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (5024, 4940, 10232) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (5056, 12212, 17281) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (5088, 12607, 3681) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (5120, 4252, 763) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_11 : ModInv 20879 (5632, 13641, 17465) := by
  have h0 := inv_blk_10
  have h1 : ModInv 20879 (5152, 14323, 18624) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (5184, 16443, 3978) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (5216, 14004, 12212) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (5248, 4077, 4093) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (5280, 5845, 9015) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (5312, 5219, 13426) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (5344, 12656, 1959) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (5376, 8402, 9614) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (5408, 19487, 20231) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (5440, 2981, 2563) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (5472, 5456, 2340) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (5504, 2325, 3709) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (5536, 13406, 5641) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (5568, 6465, 8738) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (5600, 14095, 5970) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (5632, 13641, 17465) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_12 : ModInv 20879 (6144, 15667, 20276) := by
  have h0 := inv_blk_11
  have h1 : ModInv 20879 (5664, 20060, 8802) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (5696, 3245, 20324) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (5728, 6170, 11251) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (5760, 11466, 14333) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (5792, 20050, 4910) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (5824, 12342, 12044) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (5856, 17048, 20817) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (5888, 17982, 4227) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (5920, 15806, 14562) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (5952, 8638, 7058) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (5984, 4114, 19902) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (6016, 19042, 8397) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (6048, 1855, 2998) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (6080, 17225, 988) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (6112, 697, 7735) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (6144, 15667, 20276) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_13 : ModInv 20879 (6656, 4177, 5855) := by
  have h0 := inv_blk_12
  have h1 : ModInv 20879 (6176, 2029, 2657) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (6208, 7679, 1144) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (6240, 17777, 15070) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (6272, 11570, 1697) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (6304, 11175, 12992) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (6336, 2672, 7469) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (6368, 14964, 9536) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (6400, 12522, 13491) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (6432, 2695, 13023) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (6464, 10176, 12238) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (6496, 7377, 19126) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (6528, 19752, 6865) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (6560, 17387, 14321) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (6592, 1779, 4590) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (6624, 8416, 7280) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (6656, 4177, 5855) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_14 : ModInv 20879 (7168, 2341, 6864) := by
  have h0 := inv_blk_13
  have h1 : ModInv 20879 (6688, 20766, 10031) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (6720, 10373, 3716) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (6752, 2492, 16808) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (6784, 3563, 2222) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (6816, 1502, 13038) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (6848, 15538, 14978) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (6880, 9278, 9703) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (6912, 18790, 4285) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (6944, 2639, 1259) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (6976, 5994, 11731) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (7008, 3196, 20177) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (7040, 1321, 8994) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (7072, 7602, 7683) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (7104, 8946, 15170) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (7136, 7302, 12306) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (7168, 2341, 6864) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_15 : ModInv 20879 (7680, 18849, 12075) := by
  have h0 := inv_blk_14
  have h1 : ModInv 20879 (7200, 8461, 7972) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (7232, 12546, 18064) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (7264, 14135, 1561) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (7296, 6075, 7047) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (7328, 11524, 1813) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (7360, 10736, 10030) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (7392, 9645, 10533) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (7424, 10880, 5668) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (7456, 19075, 11652) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (7488, 19854, 8149) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (7520, 18344, 1014) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (7552, 17049, 20531) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (7584, 9468, 1437) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (7616, 19534, 3505) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (7648, 8731, 5129) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (7680, 18849, 12075) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_16 : ModInv 20879 (8192, 1196, 1460) := by
  have h0 := inv_blk_15
  have h1 : ModInv 20879 (7712, 14463, 10445) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (7744, 13800, 5547) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (7776, 17297, 16219) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (7808, 9612, 6763) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (7840, 319, 4846) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (7872, 8440, 11616) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (7904, 10327, 12468) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (7936, 426, 16822) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (7968, 4478, 2984) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (8000, 16072, 7064) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (8032, 13683, 18817) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (8064, 14925, 6175) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (8096, 16266, 13435) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (8128, 10410, 5153) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (8160, 19340, 18589) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (8192, 1196, 1460) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_17 : ModInv 20879 (8704, 17194, 14953) := by
  have h0 := inv_blk_16
  have h1 : ModInv 20879 (8224, 4277, 12386) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (8256, 11955, 17842) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (8288, 15581, 16303) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (8320, 6217, 6589) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (8352, 10586, 18744) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (8384, 7490, 18526) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (8416, 17940, 10259) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (8448, 17722, 488) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (8480, 6511, 4896) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (8512, 1398, 9310) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (8544, 5618, 14591) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (8576, 16536, 753) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (8608, 14690, 3701) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (8640, 2089, 16455) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (8672, 751, 11252) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (8704, 17194, 14953) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_18 : ModInv 20879 (9216, 3999, 7252) := by
  have h0 := inv_blk_17
  have h1 : ModInv 20879 (8736, 15203, 19755) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (8768, 3684, 1621) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (8800, 8028, 17352) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (8832, 18579, 18302) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (8864, 17789, 15022) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (8896, 5049, 15293) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (8928, 6942, 6396) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (8960, 1969, 19068) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (8992, 4959, 1318) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (9024, 68, 3550) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (9056, 16020, 9934) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (9088, 3623, 17745) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (9120, 5232, 13870) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (9152, 17534, 5943) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (9184, 11549, 1163) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (9216, 3999, 7252) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_19 : ModInv 20879 (9728, 13618, 9209) := by
  have h0 := inv_blk_18
  have h1 : ModInv 20879 (9248, 16049, 16174) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (9280, 10297, 10125) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (9312, 8544, 20579) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (9344, 5147, 11425) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (9376, 17689, 10598) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (9408, 8928, 16055) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (9440, 14200, 1009) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (9472, 11981, 3710) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (9504, 10266, 17153) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (9536, 19718, 8194) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (9568, 14356, 12148) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (9600, 236, 6243) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (9632, 12710, 1338) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (9664, 19076, 20306) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (9696, 6092, 12754) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (9728, 13618, 9209) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_20 : ModInv 20879 (10240, 8924, 7855) := by
  have h0 := inv_blk_19
  have h1 : ModInv 20879 (9760, 2858, 12987) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (9792, 744, 18765) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (9824, 18265, 9795) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (9856, 2623, 7864) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (9888, 19890, 13342) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (9920, 13798, 6525) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (9952, 8258, 20201) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (9984, 3827, 984) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (10016, 20094, 8934) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (10048, 8751, 19036) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (10080, 13837, 18987) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (10112, 8015, 9991) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (10144, 2193, 10193) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (10176, 17173, 12091) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (10208, 2795, 8630) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (10240, 8924, 7855) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_21 : ModInv 20879 (10752, 2925, 11075) := by
  have h0 := inv_blk_20
  have h1 : ModInv 20879 (10272, 7600, 15477) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (10304, 1864, 17544) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (10336, 3790, 9310) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (10368, 11486, 19082) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (10400, 3191, 853) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (10432, 307, 4376) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (10464, 14413, 5708) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (10496, 2174, 3984) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (10528, 7298, 8798) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (10560, 13683, 9559) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (10592, 13326, 15434) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (10624, 17666, 15877) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (10656, 13294, 8750) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (10688, 16451, 19248) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (10720, 17429, 13622) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (10752, 2925, 11075) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_22 : ModInv 20879 (11264, 6454, 1893) := by
  have h0 := inv_blk_21
  have h1 : ModInv 20879 (10784, 69, 4737) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (10816, 13523, 2401) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (10848, 4921, 16427) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (10880, 14333, 20839) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (10912, 8765, 10224) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (10944, 4014, 8465) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (10976, 13888, 7190) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (11008, 16149, 2242) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (11040, 6176, 12962) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (11072, 1047, 12438) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (11104, 19162, 19247) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (11136, 1286, 6616) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (11168, 17604, 4489) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (11200, 8081, 14436) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (11232, 18561, 17118) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (11264, 6454, 1893) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_23 : ModInv 20879 (11776, 16119, 1504) := by
  have h0 := inv_blk_22
  have h1 : ModInv 20879 (11296, 14160, 2996) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (11328, 3845, 5340) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (11360, 2174, 9149) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (11392, 8248, 6986) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (11424, 16063, 20683) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (11456, 19785, 13346) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (11488, 20285, 9197) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (11520, 825, 16029) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (11552, 18040, 13021) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (11584, 16376, 4789) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (11616, 3137, 3055) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (11648, 15621, 10789) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (11680, 7, 11479) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (11712, 17731, 11934) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (11744, 16631, 4912) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (11776, 16119, 1504) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_24 : ModInv 20879 (12288, 9905, 8101) := by
  have h0 := inv_blk_23
  have h1 : ModInv 20879 (11808, 7163, 10635) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (11840, 12237, 2632) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (11872, 7090, 14590) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (11904, 19288, 17162) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (11936, 147, 20380) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (11968, 16781, 17237) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (12000, 17587, 3490) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (12032, 5473, 19468) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (12064, 2983, 9984) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (12096, 14485, 6320) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (12128, 19787, 7241) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (12160, 8011, 13881) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (12192, 11010, 1851) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (12224, 13662, 1174) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (12256, 15114, 9125) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (12288, 9905, 8101) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_25 : ModInv 20879 (12800, 6172, 3576) := by
  have h0 := inv_blk_24
  have h1 : ModInv 20879 (12320, 13635, 10098) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (12352, 1010, 19197) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (12384, 15282, 5383) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (12416, 19047, 13394) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (12448, 7478, 8834) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (12480, 10532, 11790) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (12512, 5557, 12608) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (12544, 13039, 1755) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (12576, 3187, 12063) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (12608, 1836, 6612) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (12640, 10417, 18433) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (12672, 17200, 9839) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (12704, 13391, 17324) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (12736, 2219, 11865) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (12768, 20012, 5846) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (12800, 6172, 3576) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_26 : ModInv 20879 (13312, 9572, 17792) := by
  have h0 := inv_blk_25
  have h1 : ModInv 20879 (12832, 6206, 13440) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (12864, 5995, 9474) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (12896, 12182, 8613) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (12928, 15042, 3028) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (12960, 18256, 7828) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (12992, 9615, 15769) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (13024, 13694, 13586) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (13056, 8132, 19413) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (13088, 10626, 582) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (13120, 18925, 13855) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (13152, 10782, 12372) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (13184, 9759, 15763) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (13216, 14585, 12221) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (13248, 14764, 10081) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (13280, 12528, 8077) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (13312, 9572, 17792) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_27 : ModInv 20879 (13824, 17803, 10847) := by
  have h0 := inv_blk_26
  have h1 : ModInv 20879 (13344, 18304, 11757) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (13376, 12626, 8900) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (13408, 11350, 14400) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (13440, 13950, 12273) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (13472, 653, 1051) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (13504, 20696, 2828) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (13536, 15923, 11983) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (13568, 11009, 9875) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (13600, 6908, 9089) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (13632, 14652, 19950) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (13664, 4431, 3131) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (13696, 18784, 3024) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (13728, 12624, 16459) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (13760, 11045, 7208) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (13792, 14614, 5491) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (13824, 17803, 10847) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_28 : ModInv 20879 (14336, 5736, 15084) := by
  have h0 := inv_blk_27
  have h1 : ModInv 20879 (13856, 7521, 1228) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (13888, 14999, 17147) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (13920, 19966, 5262) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (13952, 16852, 15417) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (13984, 613, 17135) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (14016, 14568, 13742) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (14048, 8943, 2899) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (14080, 550, 13305) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (14112, 15280, 5152) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (14144, 12622, 13047) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (14176, 6536, 2782) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (14208, 13252, 13864) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (14240, 14662, 6984) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (14272, 13923, 1258) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (14304, 20523, 1410) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (14336, 5736, 15084) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_29 : ModInv 20879 (14848, 13785, 20103) := by
  have h0 := inv_blk_28
  have h1 : ModInv 20879 (14368, 16423, 9470) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (14400, 7618, 18694) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (14432, 10992, 728) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (14464, 8952, 7345) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (14496, 7036, 18696) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (14528, 6740, 17238) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (14560, 8996, 14702) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (14592, 5319, 19800) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (14624, 5130, 16404) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (14656, 15590, 7819) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (14688, 5909, 5499) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (14720, 14312, 2673) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (14752, 14914, 7532) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (14784, 14990, 4242) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (14816, 20765, 1939) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (14848, 13785, 20103) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_30 : ModInv 20879 (15360, 15369, 3998) := by
  have h0 := inv_blk_29
  have h1 : ModInv 20879 (14880, 15474, 20638) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (14912, 7553, 9311) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (14944, 8849, 2369) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (14976, 10971, 9748) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (15008, 9297, 12805) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (15040, 18439, 504) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (15072, 6335, 19650) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (15104, 12066, 12382) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (15136, 5247, 1718) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (15168, 12140, 2117) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (15200, 20585, 13536) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (15232, 9620, 19723) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (15264, 9612, 14945) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (15296, 16895, 17162) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (15328, 9518, 509) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (15360, 15369, 3998) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_31 : ModInv 20879 (15872, 20188, 8925) := by
  have h0 := inv_blk_30
  have h1 : ModInv 20879 (15392, 2390, 12235) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (15424, 5948, 14650) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (15456, 15992, 7602) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (15488, 20663, 5005) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (15520, 11503, 17201) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (15552, 12663, 4366) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (15584, 15077, 6466) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (15616, 9723, 8508) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (15648, 12436, 7621) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (15680, 6674, 16704) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (15712, 19007, 17145) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (15744, 4065, 19699) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (15776, 18377, 17500) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (15808, 1260, 7816) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (15840, 4751, 3229) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (15872, 20188, 8925) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_32 : ModInv 20879 (16384, 64, 14317) := by
  have h0 := inv_blk_31
  have h1 : ModInv 20879 (15904, 19512, 18000) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (15936, 13615, 10471) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (15968, 9029, 19812) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (16000, 7262, 6409) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (16032, 2707, 9361) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (16064, 176, 7288) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (16096, 8483, 9731) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (16128, 5328, 20820) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (16160, 9168, 9091) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (16192, 12813, 6142) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (16224, 4580, 675) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (16256, 2603, 3000) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (16288, 11168, 10861) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (16320, 14383, 15298) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (16352, 5328, 12130) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (16384, 64, 14317) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_33 : ModInv 20879 (16896, 8686, 17410) := by
  have h0 := inv_blk_32
  have h1 : ModInv 20879 (16416, 438, 13342) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (16448, 2058, 18209) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (16480, 12029, 17106) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (16512, 17992, 17912) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (16544, 4002, 16494) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (16576, 6157, 12031) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (16608, 632, 7390) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (16640, 6893, 1670) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (16672, 10660, 10575) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (16704, 5753, 12276) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (16736, 17774, 14803) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (16768, 16173, 7235) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (16800, 11251, 11914) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (16832, 18541, 11597) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (16864, 16271, 5715) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (16896, 8686, 17410) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_34 : ModInv 20879 (17408, 14668, 2371) := by
  have h0 := inv_blk_33
  have h1 : ModInv 20879 (16928, 10215, 13621) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (16960, 9613, 6673) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (16992, 2754, 320) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (17024, 7768, 9790) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (17056, 6412, 4560) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (17088, 8737, 6718) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (17120, 18156, 19766) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (17152, 13546, 16026) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (17184, 10800, 20509) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (17216, 16665, 11062) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (17248, 12913, 7997) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (17280, 3830, 2906) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (17312, 11276, 17181) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (17344, 5449, 14394) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (17376, 20707, 19464) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (17408, 14668, 2371) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_35 : ModInv 20879 (17920, 8255, 18171) := by
  have h0 := inv_blk_34
  have h1 : ModInv 20879 (17440, 6227, 11029) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (17472, 10361, 8877) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (17504, 7625, 16536) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (17536, 53, 15159) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (17568, 9435, 20071) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (17600, 8612, 5575) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (17632, 1753, 9723) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (17664, 10890, 17540) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (17696, 10866, 15664) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (17728, 18806, 14337) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (17760, 949, 1253) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (17792, 17551, 12154) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (17824, 10496, 3296) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (17856, 19744, 14152) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (17888, 6883, 10232) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (17920, 8255, 18171) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_36 : ModInv 20879 (18432, 980, 18743) := by
  have h0 := inv_blk_35
  have h1 : ModInv 20879 (17952, 17836, 16369) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (17984, 19566, 18363) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (18016, 13377, 15241) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (18048, 15365, 15024) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (18080, 19381, 16397) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (18112, 15310, 17133) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (18144, 10352, 15792) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (18176, 875, 14915) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (18208, 15437, 20184) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (18240, 10104, 17433) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (18272, 11621, 11352) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (18304, 5956, 5507) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (18336, 9636, 11786) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (18368, 10939, 3218) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (18400, 13304, 7830) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (18432, 980, 18743) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_37 : ModInv 20879 (18944, 11444, 13632) := by
  have h0 := inv_blk_36
  have h1 : ModInv 20879 (18464, 5666, 18) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (18496, 10441, 8597) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (18528, 8383, 6402) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (18560, 7687, 13276) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (18592, 12121, 3359) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (18624, 20168, 4489) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (18656, 15729, 12430) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (18688, 18617, 15667) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (18720, 17872, 19927) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (18752, 19385, 9286) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (18784, 20540, 12055) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (18816, 1822, 18117) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (18848, 8033, 129) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (18880, 20425, 10876) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (18912, 277, 18713) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (18944, 11444, 13632) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_38 : ModInv 20879 (19456, 2147, 14623) := by
  have h0 := inv_blk_37
  have h1 : ModInv 20879 (18976, 13069, 16290) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (19008, 17155, 9300) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (19040, 12906, 7275) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (19072, 3292, 1237) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (19104, 18879, 5167) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (19136, 6177, 15047) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (19168, 3312, 10945) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (19200, 19828, 9086) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (19232, 17379, 13598) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (19264, 6039, 9140) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (19296, 16775, 19161) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (19328, 3922, 7595) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (19360, 3069, 13605) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (19392, 8149, 19795) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (19424, 19572, 5128) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (19456, 2147, 14623) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_39 : ModInv 20879 (19968, 10159, 8790) := by
  have h0 := inv_blk_38
  have h1 : ModInv 20879 (19488, 2199, 643) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (19520, 692, 14153) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (19552, 17857, 20816) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (19584, 480, 1779) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (19616, 15934, 17222) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (19648, 681, 10279) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (19680, 14608, 3624) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (19712, 7446, 8774) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (19744, 4626, 5005) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (19776, 1188, 12397) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (19808, 4382, 6363) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (19840, 4820, 13071) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (19872, 8345, 16220) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (19904, 19341, 1258) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (19936, 18582, 10281) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (19968, 10159, 8790) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_40 : ModInv 20879 (20480, 10295, 20046) := by
  have h0 := inv_blk_39
  have h1 : ModInv 20879 (20000, 8392, 2758) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (20032, 13023, 15885) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (20064, 3496, 17816) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (20096, 14586, 2550) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (20128, 1286, 16774) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (20160, 4584, 14172) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (20192, 14298, 12560) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (20224, 2978, 15205) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (20256, 13484, 3621) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (20288, 1605, 7956) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (20320, 20112, 4251) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (20352, 7892, 833) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (20384, 17411, 9614) := chunk_step (d := 5) h12 rfl
  have h14 : ModInv 20879 (20416, 7911, 2582) := chunk_step (d := 5) h13 rfl
  have h15 : ModInv 20879 (20448, 1839, 7400) := chunk_step (d := 5) h14 rfl
  have h16 : ModInv 20879 (20480, 10295, 20046) := chunk_step (d := 5) h15 rfl
  exact h16

private lemma inv_blk_41 : ModInv 20879 (20878, 20878, 0) := by
  have h0 := inv_blk_40
  have h1 : ModInv 20879 (20512, 13530, 426) := chunk_step (d := 5) h0 rfl
  have h2 : ModInv 20879 (20544, 12972, 14066) := chunk_step (d := 5) h1 rfl
  have h3 : ModInv 20879 (20576, 19392, 18497) := chunk_step (d := 5) h2 rfl
  have h4 : ModInv 20879 (20608, 11196, 13747) := chunk_step (d := 5) h3 rfl
  have h5 : ModInv 20879 (20640, 5155, 331) := chunk_step (d := 5) h4 rfl
  have h6 : ModInv 20879 (20672, 9407, 16252) := chunk_step (d := 5) h5 rfl
  have h7 : ModInv 20879 (20704, 4659, 19116) := chunk_step (d := 5) h6 rfl
  have h8 : ModInv 20879 (20736, 9365, 1064) := chunk_step (d := 5) h7 rfl
  have h9 : ModInv 20879 (20768, 13920, 14815) := chunk_step (d := 5) h8 rfl
  have h10 : ModInv 20879 (20800, 8627, 15384) := chunk_step (d := 5) h9 rfl
  have h11 : ModInv 20879 (20832, 8681, 4909) := chunk_step (d := 5) h10 rfl
  have h12 : ModInv 20879 (20864, 17184, 16906) := chunk_step (d := 5) h11 rfl
  have h13 : ModInv 20879 (20872, 20850, 424) := chunk_step (d := 3) h12 rfl
  have h14 : ModInv 20879 (20876, 10439, 20877) := chunk_step (d := 2) h13 rfl
  have h15 : ModInv 20879 (20878, 20878, 0) := chunk_step (d := 1) h14 rfl
  exact h15

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a061062.main) := by
  intro hmain
  have hp : Nat.Prime 20879 := by norm_num
  have hnot := hmain 20879 hp (by decide)
  have hdvd : 20879 ∣ a 20878 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa [a] using inv_blk_41.2.symm
  exact hnot hdvd
