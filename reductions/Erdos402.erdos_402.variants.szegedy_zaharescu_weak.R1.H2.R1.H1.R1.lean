import OMAReductions.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1

namespace OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1_H1_R1
open Filter Finset Real Chebyshev

private lemma dense (h1 : ∃ c : ℝ, 0<c ∧ ∀ᶠ t : ℕ in atTop,
  ∀ x ∈ Icc (t^24) (2*(t+1)^24),
    c*(t:ℝ)^17 ≤ psi x - psi ((x-t^17 : ℕ) : ℝ)) (h2 : ∃ C : ℝ, 0<C ∧ ∀ x y : ℕ, y≤x →
  psi x - psi y ≤ C*sqrt x + (((Ioc y x).filter Nat.Prime).card : ℝ)*log x) : ∀ᶠ t : ℕ in atTop,
    ∀ x ∈ Icc (t^24) (2*(t+1)^24),
      (t+1)^15 ≤ ((Ioc (x-t^17) x).filter Nat.Prime).card := by
  obtain ⟨c,hc,hmain⟩ := h1
  obtain ⟨C,hC,hcount⟩ := h2
  obtain ⟨T,hT⟩ := exists_nat_gt ((C*8192+32768*50)/c)
  filter_upwards [hmain,eventually_ge_atTop T,eventually_ge_atTop 2] with t hm ht ht2
  intro x hx
  obtain ⟨hxlo,hxhi⟩ := mem_Icc.mp hx
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast (by omega : 1≤t)
  have htpos : (0:ℝ)<t := by linarith
  have hxpos : 0<x := lt_of_lt_of_le (pow_pos (by omega : 0<t) _) hxlo
  have hb : (x:ℝ) ≤ 2*(2*(t:ℝ))^24 := by
    have h : (x:ℝ) ≤ 2*((t:ℝ)+1)^24 := by exact_mod_cast hxhi
    exact h.trans (by gcongr; linarith)
  have hs : sqrt (x:ℝ) ≤ 8192*(t:ℝ)^12 := by
    apply (sqrt_le_iff).mpr
    refine ⟨by positivity, hb.trans ?_⟩
    ring_nf
    nlinarith only [pow_nonneg htpos.le 24]
  have hl : log (x:ℝ) ≤ 50*t := by
    calc
      log (x:ℝ) ≤ log (2*(2*(t:ℝ))^24) := log_le_log (by exact_mod_cast hxpos) hb
      _ = log 2+24*(log 2+log t) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
          Real.log_mul (by norm_num) htpos.ne']
        norm_num
      _ ≤ 50*t := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),Real.log_le_sub_one_of_pos htpos]
  by_contra! hn
  let a := ((Ioc (x-t^17) x).filter Nat.Prime).card
  have ha : (a:ℝ) ≤ 32768*(t:ℝ)^15 := calc
    (a:ℝ) ≤ ((t:ℝ)+1)^15 := by exact_mod_cast hn.le
    _ ≤ (2*(t:ℝ))^15 := by gcongr; linarith
    _ = _ := by ring
  have hpow : (t:ℝ)^12 ≤ (t:ℝ)^16 := pow_le_pow_right₀ ht' (by decide)
  have hd := (hm x hx).trans (hcount x (x-t^17) (Nat.sub_le ..))
  change c*(t:ℝ)^17 ≤ C*sqrt x+(a:ℝ)*log x at hd
  have he : c*(t:ℝ)^17 ≤ (C*8192+32768*50)*(t:ℝ)^16 := calc
    _ ≤ _ := hd
    _ ≤ C*(8192*(t:ℝ)^16)+(32768*(t:ℝ)^15)*(50*t) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hC.le
        exact hs.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
      · exact mul_le_mul ha hl (log_natCast_nonneg _) (by positivity)
    _ = _ := by ring
  have hz : C*8192+32768*50 < (t:ℝ)*c :=
    (div_lt_iff₀ hc).mp (hT.trans_le (by exact_mod_cast ht))
  have := mul_lt_mul_of_pos_right hz (pow_pos htpos 16)
  nlinarith only [this,he]

private lemma scales (n t : ℕ) (lo : t^24 ≤ n) (hi : n < (t+1)^24) :
    t^18 ≤ n.sqrt*n.sqrt.sqrt ∧ n.sqrt*n.sqrt.sqrt ≤ (t+1)^18 ∧
    n.sqrt*n.sqrt.sqrt.sqrt ≤ (t+1)^15 := by
  have a : t^12 ≤ n.sqrt := Nat.le_sqrt'.mpr (by convert lo using 1 <;> ring)
  have b : t^6 ≤ n.sqrt.sqrt := Nat.le_sqrt'.mpr (by convert a using 1 <;> ring)
  have u : n.sqrt < (t+1)^12 := Nat.sqrt_lt'.mpr (by convert hi using 1 <;> ring)
  have v : n.sqrt.sqrt < (t+1)^6 := Nat.sqrt_lt'.mpr (by convert u using 1 <;> ring)
  have w : n.sqrt.sqrt.sqrt < (t+1)^3 := Nat.sqrt_lt'.mpr (by convert v using 1 <;> ring)
  refine ⟨?_,?_,?_⟩
  · convert Nat.mul_le_mul a b using 1 <;> ring
  · convert Nat.mul_le_mul u.le v.le using 1 <;> ring
  · convert Nat.mul_le_mul u.le w.le using 1 <;> ring

-- Uniform short-interval mass from the prime number theorem in intervals of
-- length x^(17/24). This exponent is strictly above Ingham's 5/8.
def H1 : Prop := ∃ c : ℝ, 0<c ∧ ∀ᶠ t : ℕ in atTop,
  ∀ x ∈ Icc (t^24) (2*(t+1)^24),
    c*(t:ℝ)^17 ≤ psi x - psi ((x-t^17 : ℕ) : ℝ)

-- An elementary conversion from von Mangoldt mass to the count of primes.
def H2 : Prop := ∃ C : ℝ, 0<C ∧ ∀ x y : ℕ, y≤x →
  psi x - psi y ≤ C*sqrt x + (((Ioc y x).filter Nat.Prime).card : ℝ)*log x

set_option maxHeartbeats 1200000 in
theorem main : H1 → H2 → OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1.H1 := by
  intro h1 h2
  obtain ⟨T,hT⟩ := eventually_atTop.mp (dense h1 h2)
  filter_upwards [eventually_ge_atTop ((max T (8*2^18))^24)] with n hn
  intro _
  let t := Nat.nthRoot 24 n
  have lo : t^24≤n := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hi : n<(t+1)^24 := Nat.lt_pow_nthRoot_add_one (by decide) n
  have hb : max T (8*2^18) ≤ t := (Nat.le_nthRoot_iff (by decide : 24≠0)).mpr hn
  have hTt : T≤t := le_trans (le_max_left ..) hb
  have ht : 8*2^18 ≤ t := le_trans (le_max_right ..) hb
  have ht1 : 1≤t := by omega
  let g := n.sqrt*n.sqrt.sqrt
  obtain ⟨hlo,hhi,hcnt⟩ := scales n t lo hi
  change t^18≤g at hlo
  change g≤(t+1)^18 at hhi
  have hg : 8*g ≤ n := calc
    _ ≤ 8*(2*t)^18 := Nat.mul_le_mul_left _ (hhi.trans (Nat.pow_le_pow_left (by omega) _))
    _ = (8*2^18)*t^18 := by ring
    _ ≤ t^6*t^18 := by
      gcongr
      exact ht.trans (by simpa using (Nat.pow_le_pow_right ht1 (show 1≤6 by decide)))
    _ = t^24 := by ring
    _ ≤ n := lo
  have hw : 2*t^17 ≤ g := calc
    _ ≤ t*t^17 := Nat.mul_le_mul_right _ (by omega)
    _ = t^18 := by ring
    _ ≤ g := hlo
  let x := 2*n-g
  have nx : n≤x := by dsimp [x]; omega
  have hxI : x∈Icc (t^24) (2*(t+1)^24) := mem_Icc.mpr ⟨lo.trans nx,by dsimp [x]; omega⟩
  have hnI : n∈Icc (t^24) (2*(t+1)^24) := mem_Icc.mpr ⟨lo,by omega⟩
  have hpcount := hT t hTt x hxI
  have hpos : 0 < (t+1)^15 := pow_pos (Nat.succ_pos t) _
  obtain ⟨p,hp⟩ := card_pos.mp (hpos.trans_le hpcount)
  obtain ⟨hrange,hp⟩ := mem_filter.mp hp
  obtain ⟨hp1,hp2⟩ := mem_Ioc.mp hrange
  change 2*n-g-t^17<p at hp1
  change p≤2*n-g at hp2
  have npos : 0<n := lt_of_lt_of_le (pow_pos (by omega : 0<t) _) lo
  have hpn : 3*n≤2*p := by omega
  have hsq := Nat.pow_le_pow_left hpn 2
  change ∃ p : ℕ, p.Prime ∧ n<p ∧ 2*n≤p+2*g ∧ p+g≤2*n ∧ 2*n^2<p^2 ∧ _
  refine ⟨p,hp,by omega,by omega,by omega,by nlinarith only [hsq, sq_pos_of_pos npos],?_⟩
  apply hcnt.trans ((hT t hTt n hnI).trans (card_le_card ?_))
  intro y hy
  obtain ⟨hyr,hyp⟩ := mem_filter.mp hy
  obtain ⟨hyl,hyu⟩ := mem_Ioc.mp hyr
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hyu⟩,hyp⟩

end OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1_H1_R1
