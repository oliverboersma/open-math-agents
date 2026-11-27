import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1

/-! For a prime input q we test the progression kq−2, with k chosen modulo
six. A candidate up to 16384² is prime if it is coprime to the product of
the primes up to 16384 and exceeds 16384. The mask below is that product,
written in hexadecimal. Its only required property is independently checked:
every integer from 2 through 16384 shares a factor with it. -/

private def wheel : Nat := 0x8c8adb36af6569a95372224afa6da5e9f7501a21daf44994283fd93c9928ff0472b37b16bd0f2938b4c7a7074b686bb867da86dc734fd61429733b6502c3789c29a37c433893c067b34c9cebb7cbf10e1d522c8c6743ab6b89b086d703cd88b3ae7627078e12a50f457af020bf21024dc42651e6116efcd649c122ec536dbbaff3289118d8c5a30d4e689a12e829b711ec7571e4702a79d15e52ea9cabe7cb7ad77f016d16db34bb559c53a1a6fe088c18a0d2b252a40f70a1a891f54e9c078d4447cf31b1aec3e49b95db90047e3b6ddd1d5b8f672e72c6cdbca823b35267959a71c0ee8774347c2892d6b4052f05ad3d4f7ccb469f114e4182da9eff9e61a9ebec0cf963430ebdd89296e941a547eda6ef7b814d202d4f5cf61d4d1c0f4b67cb9d13b53148151848762f3b5ca0a067c3e93a5a5b33b3808b19c61e81d571b79deeaa6245ac6fb91299b7b73705cfa16580b4ee9dc6fe1a158b662e6679050a5fb25752872516aff93f840e95d2f1a68b8d499ecef4521d7069b6a2ef0c45fa8f2cfbeaf2beec4a0b0787ea11b529adfdc3828124aac248571edd2f337b6918bfd2bdd3ed24897bcd1970b13ae244d644bdb9a06c7f800cef01aed1393aa63b93477593f54226e80a824104dc5ac72440be06ea0e2bb67fdca846f83410d2ec825f660d813e733c1cc68ea0d0865d4cad4e38c99897f54ed628e6f801624549ec72b171eabf9af5b9b227a2dcc73bfdabbf48147bfaed86fdcceb94a5c8abd392fc04dca04dc799bd5276616c36e3626abfa8ced9a685dc65dd231eab0e57f5a60ee2fc46bb0a3cd2b5ff170de6c80e91854cf8e1a2c79f2395965c33a1e23996d9a91fb8dc5f838f099e8c0327d45f08670c28b9e520b32c15a81dc62a245ded473078720a6a9a595c76a40ab87ca792a09f2c4f564267708bfde96fa7acc97744010619736afd70a44158cbac991ad0364ebb3887d5a72a2b0e3c0fa2df5d4f0249dff1379a482a66899ff8c73cc33d195a2b2916f1941df16cb2d5d57cc4a27646012656b6b5c1e096d919118df5a0adca81b6c08d570da1f8c23a110c4e12765b8b037ee785347452636cbb93ebcf5c650e551a559615b40a791040aeec4a695117dc1c4e2b426e60d1be5494aba0f9bcaeaa1a324891f07b2d23bf64dcacb23d329e2f3c5166ef502d4289284b2f4b13afd7eb97849d26250adaf96e6b850c315bf9a7df0fb8765ccc8a05d198a6e510c47fd515d1b2e98a52cd40b1ea231cd9e34218f3bc3b4c2d8cdcf3ae60c2cbebb8a50d7f41c2fe5f9269ca4b967d38aba99f7972948d3d8bf801af18224dd4d6af8645eea822523ed4e50126e62048cbd4f029ed89a058d0a937e761cb9d9d8633a35f6a87fc85653ddaf880a6a29a4ca100f2891b5162c5c7fd45fef2393997fb9a3c2d3f1d46f599a376a6a3676af79387ef4a6d8cd7d6171785eb8d42291531afcc0942899fdaa9ca8b70fb960c7967fc7537a3cffb2b426e0f3fc9b0eb4694a5ff6365a481c6133c0acb3c20e262cfcd3e0707b0407f5266d09bb2626190c28db2ccffa0254f6a21c16d9efae081bf0d9b9e70a4b78fc226e8f6805db9466ac4fb8747d4eaabbeb1a4dfd9b2f8d8fc4b733807bbd4054fbdff024780a7a1de8b476dd165250286a22d2563f6d786957489807f5200a4e4493f239555bf93ca515d5f183ff08c5c12eda23f9887a655a312bed9d3ad969add6fdb8e34e4bed5d1567b44f45a0057307021aabbef3929cf8996576f0029785dda3718cb7481e897f348fa4efc445de15533c3502104eda177c96da11748422ba332502f7d5dffcb944f53be3623c87e8d6131d8922161220d4af7dcb59236ad663e7a85d6dd49390f7b702233f9be052f7e659d9fae62dc1041744681d2fd4671abb7666b03641cd8367f9c514c58eaefd5410198d89a31773f8b45a710f99008a7c595195b518cec9ff3ee02e91e493069c6e91c8f73ca350e3ef3a4f7f4bc854b370b0c6293ba0c8777e6b4c55afb46c82ef1bf0174bc99b16a8e91fb663f8feb31209ea35a2f3c36ab972ed4e11c4fd3a3a43333a86f4f4bb10576d1f14ff81f4d3d22063e4c4313893f487d404518e04fe771ba18f10597ee160e1a4dc8ad0ea329ab5cfa3d2ba1a06b413c6de8fcdc182b2452e3ac895afef18c62d3e4b4d2c134500515990def467cf31d6a47d86e22dd9aed7a6ab778618cf70a9673e159442002933d0cfb0d77b8105a7a24ac83db9cfc5dc2826bd7c4c22395180c289d65badb31a6d690ade53bae43de95b6ed9302e7cc0382d145dbdc764d3beadb48a31b9040f5a53629bad66ec5b116f3277c95f667ccc8ac8b49373cdffdec8256d62fa392f39cd863aa39582f9ef082054f8b7115c5fa772f4322e371b1d82c4f086ed1b1d879c56762bf361cbfb2cf30fcad2f6a1b3825011d7019cd3e238706f50e5fe77103c5e7175e5d99736e26cf63bf7e29740d9089ef78c90cb60f882fb9a1e417a16de56f3a5d2395e83bd658708a4d0299814070a2961bbade9138a1fc4936f74adad188dc24cb28e57e6009149987301bd4bb49b9ceeb633891e93a17a8b185f454ac197c38cb12429c5a38d2280fae3bf39d80353247d94046a1fcb64873843d7a57dcdac1caae98ba0c5123dac69c942792b73b85472822680a51aaeac2b9542ef0a51f5e93c8ec4a0e967f32c8a0c5e350446b127ce528d6538f567a689d6cb8a14a528c21af79ccc0aa0b7606dfb768f46ddfe5f9581b578b4a26ea15008e633175ae2bfb98ace643a9d60064b808949861482b147a3adc400fb3acbe59d65314e8b0391f747c70a3d220cb046ce4ca60c41f4e9f0a63d5bea3181ef83cbab20b74f1a7cfe7dce0e57f2e930a53c2599cf10686711aa29c59cfb8dcf3c2bfbc7c2809a6e5ca277902bcc1d1defff69875199411e42e808e8cb3563791022962ae7dc0ba55f7d9a025b1fb6f4833129c2356ac954edb3b8b161b514b79af81a4867e2ae25c7fff1bae251b41c1386f1506e9902c30e938b7578444726f20998c01dcdf64c4d61bb4046a51522e82a283298da25f010f36b162750ea6ff241c8bc4fd49dc8aefe21f556cd4c8e20c57ba044135e4e2599c2aea0306161962f07eb1fec12819940c4cddb6b4a56cf891c75198f94a2392d2cd04edb49280c32a25ff21b70401f93bed118e9107b7acdf4a3e51d78cb5deb321d14aaef369232b4c92b917c1a39f1a31b8d6abe215bb793cfdb2dd5c696290b6dde0332cf5fcdf5a28570481329c77fa35047393544d290dc16ed5f6132aaef70b4e6035b7966aa0456897ca756d421c9776d08ed3b296fcf98b711aa4790ec9ce5d412217386f09cb27819ba4f45864b0857d3c0bbd4e022a65ccff7d0777a619a082375f1d243b831d13c433f6ffff4448728ecc81b0951e9d966edc4dd6bb0c546dba09258b3558cc25147ae8270ed39a365845174afe674acb687be74f28478ce1a956f34f0acc02a43be894f98287b782fe5e3a0203cd9b9523b9a29cffbbd9c5317543cba6333543f9315765b78f3f9c4914d46795b2d6bf9e523d70cc4036fef44d7cd82668b8b2b3bf1a93eeb7d866745f95767fe38f14e8fdcaad7657cfbf40718e6946f2384b8b3fb89f02cc5247e4604dc01a0694366605af6f493ef83d1841590908a3168c8a359732f4e8c3ca7dbc07344a234f93888c13781516853bc26859bde283e7ba8a0bdab01a8f75329a6fb43331a26cb127c54db43d22dfad4e0c5a2872e625e8ceefe4069422964194a4e11c339763abb1718f4571682ff140624686978f61b4620dac0ce274069bd2d8d05cd88fa455166cf4183ca988f8bbb1f76fc45e296d95ab4184ee17df540ec720f8e6d95cdacfadeddd1a8a284a2a5a3498332839f9058da07f9a481c1a920398b06d76ce432d760af696a4a1b07b70dca2e31cad5a3ffd83ab5b6db2766927617df5c8ffb90f6e145256e85e76a3f62d06e2c862f9678084a6afbd061519f77267a7367abc67c3392aca512497e68a307844faf07879902f95e10984c64aa741561742aa4620d99676380a1f5dc7a0386af6a2bdc767b8085762da40a334c35e4ecfb78b7d931159ddae4462e44d293f2

private def looksPrime (r : Nat) : Bool :=
  if r ≤ 16384 then r.minFac == r
  else r ≤ 16384 ^ 2 && Nat.gcd r (wheel % r) == 1

private def search (q : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n+1, k =>
    let r := k*q-2
    (5 < r && r < q*q && r % 3 == 2 && looksPrime r) || search q n (k+6)

private def good (q : Nat) : Bool :=
  if 1000000 < q || q < 5 || q % 2 == 0 || q % 3 == 0 then true
  else if q ≤ 1000 then q.minFac != q || search q 48 (if q % 3 == 1 then 1 else 5)
  else Nat.gcd q (Nat.factorial 1000 % q) != 1 || search q 48 (if q % 3 == 1 then 1 else 5)

private def block (f : Nat → Bool) : Nat → Nat → Bool
  | 0, a => f a
  | d+1, a => block f d a && block f d (a + 2^d)

private lemma block_at {f : Nat → Bool} {d a x : Nat} (h : block f d a = true)
    (lo : a ≤ x) (hi : x < a + 2 ^ d) : f x = true := by
  induction d generalizing a with
  | zero =>
    have : x = a := by simp at hi; omega
    exact this ▸ h
  | succ d ih =>
    have hh := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at hi
    by_cases hmid : x < a + 2^d
    · exact ih hh.1 lo hmid
    · exact ih hh.2 (by omega) (by omega)

private lemma gcd_remainder (n w : ℕ) : n.gcd (w % n) = n.gcd w := by
  rw [Nat.gcd_comm n (w % n), ← Nat.gcd_rec]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private lemma checkWheel (j : Fin 16) :
    block (fun n => Nat.gcd n (wheel % n) != 1) 10 (2 + 1024*j.val) = true := by
  fin_cases j <;> as_aux_lemma => decide +kernel

private lemma looksPrime_sound {r : ℕ} (hr : 5 < r) (h : looksPrime r = true) : r.Prime := by
  unfold looksPrime at h
  split at h
  · exact Nat.prime_def_minFac.mpr ⟨by omega, beq_iff_eq.mp h⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, gcd_remainder] at h
    have cop : Nat.Coprime r wheel := h.2
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨by omega, ?_⟩
    intro d hd hds hdvd
    have hdB : d ≤ 16384 := by
      rw [← Nat.sqrt_eq' 16384]; exact hds.trans (Nat.sqrt_le_sqrt h.1)
    let j : Fin 16 := ⟨(d - 2) / 1024, by omega⟩
    have ht := block_at (checkWheel j) (x := d) (by dsimp [j]; omega) (by dsimp [j]; omega)
    have hcop := cop.coprime_dvd_left hdvd
    simp only [bne_iff_ne, gcd_remainder] at ht
    exact ht hcop

private def GoalAt (q : ℕ) : Prop :=
  ∃ r : ℕ, r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r + 2

private lemma search_sound (q n k : ℕ) (h : search q n k = true) : GoalAt q := by
  induction n generalizing k with
  | zero => simp [search] at h
  | succ n ih =>
    simp only [search, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨⟨⟨hr, hsq⟩, hmod⟩, hp⟩ | h
    · refine ⟨k*q-2, looksPrime_sound hr hp, hr, by simpa [sq] using hsq, hmod, k, ?_⟩
      rw [Nat.mul_comm q k]; omega
    · exact ih _ h

private lemma good_sound {q : ℕ} (hp : q.Prime) (hq : 5 ≤ q) (hB : q ≤ 1000000)
    (h : good q = true) : GoalAt q := by
  have nd (d : ℕ) (h1 : 1 < d) (h2 : d < q) : q % d ≠ 0 := by
    intro hz
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hz) with e | e <;> omega
  have h2 := nd 2 (by decide) (by omega)
  have h3 := nd 3 (by decide) (by omega)
  simp [good, not_lt.mpr hB, not_lt.mpr hq, h2, h3] at h
  split at h
  · simp [hp.minFac_eq] at h
    exact search_sound _ _ _ h
  · rename_i hlarge
    have cop : Nat.Coprime q (Nat.factorial 1000) := hp.coprime_factorial_of_lt (by omega)
    simp [gcd_remainder, show Nat.gcd q (Nat.factorial 1000) = 1 from cop] at h
    exact search_sound _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
private lemma checked (i j : Fin 32) :
    block good 10 (1024 * (32 * i.val + j.val)) = true := by
  fin_cases i <;> fin_cases j <;> as_aux_lemma => decide +kernel

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1_H2_R1.H1 := by
  intro q hp hq hB
  let i : Fin 32 := ⟨q / 1024 / 32, by omega⟩
  let j : Fin 32 := ⟨q / 1024 % 32, Nat.mod_lt _ (by decide)⟩
  apply good_sound hp hq hB
  apply block_at (checked i j)
  · dsimp [i, j]; omega
  · dsimp [i, j]; omega

