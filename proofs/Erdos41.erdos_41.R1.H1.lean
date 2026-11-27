import OMAReductions.R_Erdos41_erdos_41_R1

-- Credit: @Iraeeee
-- Smooth-gap argument following the crossing-count approach recorded by @ysanatomic.

open Filter Set

namespace Erdos41Smooth

lemma dyadic_gaps {f : ℕ → ℕ}
    (h : (fun i : ℕ => ((f (i+1)-f i : ℕ) : ℝ)) =o[atTop]
      (fun i : ℕ => (i : ℝ)^2 * Real.log (i+2))) (E : ℕ) (hE : 0 < E) :
    ∀ᶠ m : ℕ in atTop, ∀ j ≤ m, let L := 2^(3*m+j)
      ∀ i : ℕ, L ≤ i → i ≤ E*L → 8*(f (i+1)-f i) ≤ m*L^2 := by
  have hb := (Asymptotics.isLittleO_iff_nat_mul_le.mp h) (40*E^2)
  obtain ⟨n₀, hn⟩ := eventually_atTop.1 hb
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop (E+2)] with m hm hmE
  intro j hj L i hLi hi
  have hLp : 0 < L := by dsimp [L]; positivity
  have hmL : m ≤ L := (show m < 2^m from Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega : m ≤ 3*m+j))
  have h1 := hn i (hm.trans (hmL.trans hLi))
  have hlog0 : 0 ≤ Real.log ((i : ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) i])
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (f (i+1)-f i)),
    abs_of_nonneg (mul_nonneg (sq_nonneg _) hlog0), Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow] at h1
  have hbig : i+2 ≤ 2^(5*m) := calc
    i+2 ≤ (E+2)*L := by nlinarith only [hi, hLp]
    _ ≤ 2^m * 2^(4*m) := Nat.mul_le_mul (hmE.trans (show m < 2^m from Nat.lt_two_pow_self).le)
      (Nat.pow_le_pow_right (by decide) (by omega : 3*m+j ≤ 4*m))
    _ = 2^(5*m) := by rw [← pow_add]; congr 1; omega
  have hbr : (i : ℝ)+2 ≤ (2:ℝ)^(5*m) := by exact_mod_cast hbig
  have hlog := Real.log_le_log (by positivity) hbr
  rw [Real.log_pow] at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hlog' : Real.log ((i:ℝ)+2) ≤ 5*(m:ℝ) := by
    push_cast at hlog
    nlinarith only [hlog, mul_nonneg (Nat.cast_nonneg m) (show 0 ≤ 1 - Real.log 2 by linarith)]
  have hisq : (i:ℝ)^2 ≤ ((E:ℝ)*L)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hi
  have hboth := mul_le_mul hisq hlog' hlog0 (sq_nonneg _)
  have hcancel : (E:ℝ)^2*(8*((f (i+1)-f i : ℕ):ℝ)) ≤ (E:ℝ)^2*((m:ℝ)*L^2) := by
    nlinarith only [h1,hboth]
  exact_mod_cast (le_of_mul_le_mul_left hcancel (by positivity : 0 < (E:ℝ)^2))

lemma crossing {f : ℕ → ℕ} (hf : StrictMono f) {a b u : ℕ}
    (hu : f a + f b < f u) :
    ∃ d, b ≤ d ∧ d < u ∧ f d ≤ f a + f b ∧ f a + f b < f (d+1) := by
  classical
  have he : ∃ i, f a + f b < f i := ⟨u,hu⟩
  have hmin := Nat.find_min' he hu
  have hspec := Nat.find_spec he
  have hb : b < Nat.find he := by
    by_contra! hh
    have := hf.monotone hh
    omega
  refine ⟨Nat.find he - 1, by omega, by omega, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min he (by omega))
  · rwa [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find he)]

lemma accumulate {f : ℕ → ℕ} {d q G : ℕ}
    (hg : ∀ k < q, 8*(f (d+k+1)-f (d+k)) ≤ G) :
    8*f (d+q) ≤ 8*f d + q*G := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hprev := ih (fun k hk => hg k (by omega))
    have hnext := hg q (by omega)
    change 8*f (d+q+1) ≤ 8*f d + (q+1)*G
    rw [Nat.add_mul q 1, one_mul]
    omega


/-- Count indices on disjoint dyadic shells and send each triple to its overshoot. -/
lemma packing {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (range f) 3)
    {m D : ℕ} (hm : 3 ≤ m)
    (hc : ∀ j < m, let L := 2^(3*m+j); 2*f (3*L) < f (D*L))
    (hg : ∀ j < m, let L := 2^(3*m+j)
      ∀ i : ℕ, L ≤ i → i ≤ (D+1)*L → 8*(f (i+1)-f i) ≤ m*L^2) : False := by
  classical
  let L (j : ℕ) := 2^(3*m+j)
  let Q (j : ℕ) := 8*(2^(m-j))^2
  let H := m*(2^(4*m))^2
  have hweight (j : Fin m) : L j^2 * Q j = 8*(2^(4*m))^2 := by
    dsimp [L,Q]
    rw [show (2^(3*m+j.val))^2 * (8*(2^(m-j.val))^2) =
      8*(2^(3*m+j.val) * 2^(m-j.val))^2 by ring, ← pow_add]
    congr 3; omega
  have hQ (j : Fin m) : Q j ≤ L j := by
    dsimp [Q,L]
    rw [← pow_mul, show 8 = 2^3 by decide, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hex (a b : ℕ) : ∃ d, b ≤ d ∧ f d ≤ f a+f b ∧ f a+f b < f (d+1) := by
    have hu : f a+f b+1 ≤ f (f a+f b+1) := hf.id_le _
    obtain ⟨d, h1, _, h2, h3⟩ := crossing hf (a := a) (b := b) (u := f a+f b+1) (Nat.lt_of_succ_le hu)
    exact ⟨d,h1,h2,h3⟩
  choose d hd using hex
  let T := (j : Fin m) × (Fin (L j) × Fin (L j) × Fin (Q j))
  let a (t : T) := L t.1 + t.2.1.val
  let b (t : T) := 2*L t.1 + t.2.2.1.val
  let c (t : T) := d (a t) (b t) + (t.2.2.2.val + 1)
  have hab (t : T) : a t < b t ∧ b t ≤ 3*L t.1 := by
    have := t.2.1.isLt
    have := t.2.2.1.isLt
    dsimp [a,b]
    omega
  have hbc (t : T) : b t < c t := by
    have := (hd (a t) (b t)).1
    dsimp [c]
    omega
  have hsum (t : T) : f (a t)+f (b t) < f (c t) :=
    (hd (a t) (b t)).2.2.trans_le (hf.monotone (by dsimp [c]; omega))
  have hupper (t : T) : f (c t) - (f (a t)+f (b t)) ≤ H := by
    let j := t.1
    let g := d (a t) (b t)
    let k := t.2.2.2.val + 1
    have hk : k ≤ Q j := t.2.2.2.isLt
    have hfar := hc j j.isLt
    change 2*f (3*L j) < f (D*L j) at hfar
    have ha := hf.monotone ((hab t).1.le.trans (hab t).2)
    have hb := hf.monotone (hab t).2
    have hd₀ := (hd (a t) (b t)).1
    have hd₁ := (hd (a t) (b t)).2.1
    have hge : L j ≤ g := by
      apply le_trans (b := b t) _ hd₀
      change L j ≤ 2*L j + _
      omega
    have hlt : g < D*L j := hf.lt_iff_lt.mp (by
      change f (d (a t) (b t)) < f (D*L j)
      dsimp [j] at hfar ⊢
      omega)
    have ha' := accumulate (f := f) (d := g) (q := k) (G := m * L j^2) (by
      intro r hr
      apply hg j j.isLt
      · change L j ≤ g+r
        omega
      · change g+r ≤ (D+1)*L j
        have := hQ j
        rw [Nat.add_mul, one_mul]
        omega)
    have hmass : k*(m*L j^2) ≤ 8*H := calc
      _ ≤ Q j*(m*L j^2) := Nat.mul_le_mul_right _ hk
      _ = m*(L j^2*Q j) := by ring
      _ = 8*H := by rw [hweight]; dsimp [H]; ring
    change 8*f (c t) ≤ 8*f (d (a t) (b t)) + k*(m*L j^2) at ha'
    omega
  let F (t : T) : Fin (H+1) := ⟨f (c t)-(f (a t)+f (b t)), Nat.lt_succ_of_le (hupper t)⟩
  have hinj : Function.Injective F := by
    intro t u heq
    have hv := congrArg Fin.val heq
    change f (c t) - (f (a t)+f (b t)) = f (c u) - (f (a u)+f (b u)) at hv
    have ht := hsum t
    have hu := hsum u
    have htr := OMA.R_Erdos41_erdos_41_R1.reduced_signed_eq hB
      (mem_range_self (a t)) (mem_range_self (b t)) (mem_range_self (c t))
      (mem_range_self (a u)) (mem_range_self (b u)) (mem_range_self (c u))
      (hf (hab t).1).le (hf (hab u).1).le
      (hf ((hab t).1.trans (hbc t))).ne' (hf (hbc t)).ne' (by omega)
    obtain ⟨h1,h2,h3⟩ := htr
    replace h1 := hf.injective h1
    replace h2 := hf.injective h2
    replace h3 := hf.injective h3
    have hsep (s v : Fin m) (hsv : s.val < v.val) : 2*L s ≤ L v := by
      dsimp [L]
      rw [Nat.mul_comm, ← pow_succ]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨j,x,y,z⟩ := t
    obtain ⟨j',x',y',z'⟩ := u
    change L j + x.val = L j' + x'.val at h1
    have hj : j = j' := by
      apply Fin.ext
      rcases lt_trichotomy j.val j'.val with hh | hh | hh
      · have := hsep j j' hh
        have := x.isLt
        omega
      · exact hh
      · have := hsep j' j hh
        have := x'.isLt
        omega
    subst j'
    obtain rfl : x = x' := Fin.ext (Nat.add_left_cancel h1)
    change 2*L j+y.val = 2*L j+y'.val at h2
    obtain rfl : y = y' := Fin.ext (Nat.add_left_cancel h2)
    change d _ _ + (z.val+1) = d _ _ + (z'.val+1) at h3
    have hz : z = z' := Fin.ext (by simpa [a,b] using h3)
    subst z'
    rfl
  have hn := Fintype.card_le_of_injective F hinj
  simp only [T, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] at hn
  have hw (j : Fin m) : L j * (L j * Q j) = 8*(2^(4*m))^2 := by
    rw [← mul_assoc, ← sq, hweight]
  simp only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hn
  have hp : 0 < (2^(4*m) : ℕ)^2 := by positivity
  dsimp [H] at hn
  rw [show m*(8*(2^(4*m))^2) = 8*(m*(2^(4*m))^2) by ring] at hn
  have := Nat.mul_pos (show 0 < m by omega) hp
  omega


lemma upper_cubic {f : ℕ → ℕ} (hf : StrictMono f)
    (hpos : 0 < atTop.liminf (fun n : ℕ =>
      ((Set.range f ∩ Icc 1 n).ncard : ℝ) / (n : ℝ)^(1/3 : ℝ))) :
    ∃ K n₀ : ℕ, ∀ n ≥ n₀, f n ≤ K*(n+1)^3 := by
  obtain ⟨K,n₀,_,h⟩ := OMA.R_Erdos41_erdos_41_R1.eventual_cubic_of_pos _ hpos
  refine ⟨K,n₀,fun n hn => ?_⟩
  have hsub : Set.range f ∩ Icc 1 (f n) ⊆ f '' Iic n := by
    rintro x ⟨⟨i,rfl⟩,hx⟩
    exact ⟨i,hf.le_iff_le.mp hx.2,rfl⟩
  have hh := Set.ncard_le_ncard hsub ((Set.finite_Iic n).image f)
  have hh' : (Set.range f ∩ Icc 1 (f n)).ncard ≤ n+1 := by
    simpa [Set.ncard_image_of_injective _ hf.injective] using hh
  exact (h (f n) (hn.trans (hf.id_le n))).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hh' 3))

lemma far_endpoint {f : ℕ → ℕ} (hf : StrictMono f) (hB : Erdos41.NtupleCondition (range f) 3)
    {K n₀ : ℕ} (hk : ∀ n ≥ n₀, f n ≤ K*(n+1)^3) {L : ℕ} (hL : 0 < L) (hn : n₀ ≤ L) :
    2*f (3*L) < f ((4000*(K+1))*L) := by
  let D := 4000*(K+1)
  have hl := OMA.R_Erdos41_erdos_41_R1.inverse_growth hf hB (D*L)
  have hsmall := hk (3*L) (by omega)
  have hsize := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (show 3*L+1 ≤ 4*L by omega) 3)
  have hlarge : 24*(2*K*(4*L)^3+1) < (D*L)^3 := by
    rw [mul_pow]
    have hD : 3072*K+24 < D^3 := by
      dsimp [D]
      nlinarith only [Nat.zero_le (K^2),Nat.zero_le (K^3)]
    have hscale := Nat.mul_lt_mul_of_pos_right hD (Nat.pow_pos (n := 3) hL)
    nlinarith only [hscale, show 1 ≤ L^3 from Nat.pow_pos hL]
  rw [Nat.mul_assoc 2 K] at hlarge
  change 2*f (3*L) < f (D*L)
  omega

end Erdos41Smooth

theorem OMA.solution : OMA.R_Erdos41_erdos_41_R1.H1 := by
  intro f hf hB hg
  by_contra hne
  have hnn := le_liminf_of_le (OMA.R_Erdos41_erdos_41_R1.upper_ratio (range f) hB)
    (Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg ((range f ∩ Icc 1 n).ncard)) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  obtain ⟨K,n₀,hk⟩ := Erdos41Smooth.upper_cubic hf (lt_of_le_of_ne hnn (Ne.symm hne))
  let D := 4000*(K+1)
  obtain ⟨m,hm,hn,hgap⟩ := ((eventually_ge_atTop 3).and
    ((eventually_ge_atTop n₀).and (Erdos41Smooth.dyadic_gaps hg (D+1) (by omega)))).exists
  apply Erdos41Smooth.packing hf hB (m := m) (D := D) hm
  · intro j hj L
    apply Erdos41Smooth.far_endpoint hf hB hk (by dsimp [L]; positivity)
    exact hn.trans ((show m < 2^m from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  · exact fun j hj => hgap j hj.le
