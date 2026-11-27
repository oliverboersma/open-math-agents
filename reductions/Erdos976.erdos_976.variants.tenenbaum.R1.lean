import FormalConjectures.ErdosProblems.«976»

/-! Tenenbaum, Sur une question d'Erdős et Schinzel II, Invent. Math. 99 (1990).
The three inputs specialize the root-density estimate (2.4), the Hooley moment
estimate (Theorem 3, t = 3/2), and the Erdős–Schinzel inequality (1.3).
The degree-independent exponent obtained here is 1/8. -/
namespace OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1
open Filter Real Finset Asymptotics
open scoped Classical

/-- Mean number of roots over moduli between n/2 and n. -/
def H1 : Prop :=
  let band (n : ℕ) := Ioc (n/2) n
  let roots (f : Polynomial ℤ) (d : ℕ) :=
    ((Icc 1 d).filter fun m : ℕ => (d : ℤ) ∣ f.eval (m : ℤ)).card
  ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree →
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, A*n ≤ ∑ d ∈ band n, (roots f d : ℝ)

/-- Tenenbaum's fixed 3/2 moment, with arbitrarily small logarithmic slack. -/
def H2 : Prop :=
  let delta (b : ℕ) : ℕ :=
    sSup (Set.range fun u : ℝ => (b.divisors.filter (fun d : ℕ => u < d ∧ (d : ℝ) ≤ exp 1*u)).card)
  ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree → ∀ η : ℝ, 0 < η →
    ∀ᶠ n : ℕ in atTop, ∑ m ∈ Icc 1 n, (delta (f.eval (m:ℤ)).natAbs : ℝ)^(3/2 : ℝ)
      ≤ n * (log n)^(2*sqrt 2 - 5/2 + η)

/-- Erdős–Schinzel's transfer from divisors in the band to a large prime. -/
def H3 : Prop :=
  let band (n : ℕ) := Ioc (n/2) n
  let localDivisors (f : Polynomial ℤ) (n m : ℕ) :=
    ((band n).filter fun d : ℕ => (d : ℤ) ∣ f.eval (m : ℤ)).card
  let hits (f : Polynomial ℤ) (n : ℕ) :=
    ((Icc 1 n).filter fun m : ℕ => 0 < localDivisors f n m).card
  ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree →
    ∀ᶠ n : ℕ in atTop, n * exp (log n * hits f n / (f.natDegree*n)) ≤ Erdos976.F f n

theorem main : H1 → H2 → H3 → type_of% @Erdos976.erdos_976.variants.tenenbaum := by
  intro rootsAvg moments transfer f hf hd
  let band (n : ℕ) := Ioc (n/2) n
  let localDivisors (f : Polynomial ℤ) (n m : ℕ) :=
    ((band n).filter fun d : ℕ => (d : ℤ) ∣ f.eval (m : ℤ)).card
  let roots (f : Polynomial ℤ) (d : ℕ) :=
    ((Icc 1 d).filter fun m : ℕ => (d : ℤ) ∣ f.eval (m : ℤ)).card
  let hits (f : Polynomial ℤ) (n : ℕ) :=
    ((Icc 1 n).filter fun m : ℕ => 0 < localDivisors f n m).card
  let scale (n : ℕ) : ℝ := (log n) ^ (1/24 : ℝ)
  let delta (b : ℕ) : ℕ :=
    sSup (Set.range fun u : ℝ => (b.divisors.filter (fun d : ℕ => u < d ∧ (d : ℝ) ≤ exp 1*u)).card)
  have local_le_delta (f : Polynomial ℤ) (hf : Irreducible f) (hd : 2≤f.natDegree)
      (n m : ℕ) : localDivisors f n m ≤ delta (f.eval (m:ℤ)).natAbs := by
    classical
    let b := (f.eval (m:ℤ)).natAbs
    let pieces (u : ℝ) := b.divisors.filter (fun d : ℕ => u < d ∧ (d : ℝ) ≤ exp 1*u)
    have hb : b ≠ 0 := by
      apply Int.natAbs_ne_zero.mpr
      exact hf.not_isRoot_of_natDegree_ne_one (by omega)
    change _ ≤ sSup (Set.range (fun u => (pieces u).card))
    refine le_trans (b:=(pieces ((n:ℝ)/2)).card) ?_ (le_csSup ?_ ⟨(n:ℝ)/2,rfl⟩)
    · unfold localDivisors
      apply card_le_card
      intro d h
      obtain ⟨hdv,hfd⟩ := mem_filter.mp h
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hdv
      have hlow : n < 2*d := by omega
      have hlow' : (n:ℝ) < 2*d := by exact_mod_cast hlow
      have hu' : (d:ℝ) ≤ n := by exact_mod_cast hu
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hfd,hb⟩,by linarith,
        by nlinarith [mul_le_mul_of_nonneg_right exp_one_gt_two.le (show 0≤(n:ℝ) by positivity)]⟩
    · refine ⟨b.divisors.card,?_⟩
      rintro _ ⟨u,rfl⟩
      exact card_le_card (filter_subset _ _)
  have incidence (f : Polynomial ℤ) (n : ℕ) :
      (∑ d ∈ band n, (roots f d : ℝ)) ≤ ∑ m ∈ Icc 1 n, (localDivisors f n m : ℝ) := by
    classical
    have h (d : ℕ) (hd : d ∈ band n) : (roots f d : ℝ) ≤
        ∑ m ∈ Icc 1 n, (if (d : ℤ) ∣ f.eval (m : ℤ) then (1:ℝ) else 0) := by
      rw [sum_boole]
      apply Nat.cast_le.mpr
      unfold roots
      apply card_le_card
      intro m hm
      obtain ⟨hr,hf⟩ := mem_filter.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hr).1,(mem_Icc.mp hr).2.trans (mem_Ioc.mp hd).2⟩,hf⟩
    refine (sum_le_sum h).trans_eq ?_
    rw [sum_comm]
    simp [localDivisors, sum_boole]
  have clipped (a : ℕ) (L : ℝ) (hL : 0<L) :
      (a : ℝ) ≤ (if 0<a then L^18 else 0) + (a : ℝ)^(3/2 : ℝ) / L^9 := by
    by_cases ha : 0<a
    · rw [if_pos ha]
      by_cases h : (a : ℝ) ≤ L^18
      · exact h.trans (le_add_of_nonneg_right (by positivity))
      · have hs : L^9 ≤ (a : ℝ)^(1/2 : ℝ) := by
          calc
            L^9 = (L^18)^(1/2 : ℝ) := by
              rw [← Real.rpow_natCast L 18,← Real.rpow_mul hL.le]
              norm_num
            _ ≤ _ := Real.rpow_le_rpow (by positivity) (le_of_not_ge h) (by norm_num)
        have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (a:ℝ) by positivity)
        have he : (a:ℝ)^(3/2 : ℝ) = a*(a:ℝ)^(1/2 : ℝ) := by
          rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add (by exact_mod_cast ha),Real.rpow_one]
        rw [he]
        have hd := (le_div_iff₀ (show 0<L^9 by positivity)).mpr hm
        linarith [show 0≤L^18 by positivity]
    · have hz : a=0 := by omega
      simp [hz]
  have clippedSum (f : Polynomial ℤ) (n : ℕ) (L : ℝ) (hL : 0<L) :
      (∑ m ∈ Icc 1 n, (localDivisors f n m : ℝ)) ≤
        hits f n * L^18 + (∑ m ∈ Icc 1 n, (localDivisors f n m : ℝ)^(3/2 : ℝ))/L^9 := by
    have h := sum_le_sum (s:=Icc 1 n) (fun m _ => clipped (localDivisors f n m) L hL)
    simpa [sum_add_distrib, ← sum_filter, hits, ← sum_div] using h
  have scale_pow (n : ℕ) (hn : 1≤n) (k : ℕ) :
      (scale n)^k = (log n)^((1/24 : ℝ)*k) := by
    dsimp only [scale]
    rw [← Real.rpow_natCast _ k, ← Real.rpow_mul (log_nonneg (by exact_mod_cast hn))]
  have scale_tendsto : Tendsto scale atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/24)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have localizedMoment (hm : H2) (f : Polynomial ℤ) (hf : Irreducible f)
      (hd : 2≤f.natDegree) : ∀ᶠ n : ℕ in atTop,
        ∑ m ∈ Icc 1 n, (localDivisors f n m : ℝ)^(3/2 : ℝ) ≤ n*(scale n)^8 := by
    have logbound := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    filter_upwards [hm f hf hd (1/1000) (by norm_num),logbound,eventually_ge_atTop (1:ℕ)] with n h hn hn1
    have hs : sqrt 2 < 1415/1000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    have ex : 2*sqrt 2-5/2+1/1000 ≤ (1/24 : ℝ)*(8:ℕ) := by linarith
    refine (sum_le_sum (s := Icc 1 n) (fun m _ => Real.rpow_le_rpow (by positivity)
      (show (localDivisors f n m : ℝ) ≤ delta (f.eval (m:ℤ)).natAbs by exact_mod_cast local_le_delta f hf hd n m)
      (by norm_num : (0:ℝ) ≤ 3/2)) ).trans (h.trans ?_)
    rw [scale_pow n hn1]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn ex) (by positivity)
  obtain ⟨A,hA,hroots⟩ := rootsAvg f hf hd
  refine ⟨1/8, by norm_num, Asymptotics.IsBigO.of_bound 1 ?_⟩
  filter_upwards [hroots,localizedMoment moments f hf hd,transfer f hf hd,eventually_gt_atTop (1:ℕ),
    scale_tendsto.eventually_ge_atTop (max 1 (max (2/A) (2*f.natDegree/A)))] with n hr hm ht hn hlarge
  let L := scale n
  have h1 : 1≤L := (le_max_left ..).trans hlarge
  have hL : 0<L := by linarith
  have hlA : 2/A ≤ L := ((le_max_left ..).trans (le_max_right ..)).trans hlarge
  have hlg : (2*(f.natDegree:ℝ))/A ≤ L := ((le_max_right ..).trans (le_max_right ..)).trans hlarge
  have gpos : (0:ℝ)<f.natDegree := by exact_mod_cast (show 0<f.natDegree by omega)
  have npos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have htail : (∑ m ∈ Icc 1 n, (localDivisors f n m : ℝ)^(3/2 : ℝ))/L^9 ≤ (n:ℝ)/L := by
    apply (div_le_div_of_nonneg_right hm (by positivity : 0 ≤ L^9)).trans_eq
    change (n:ℝ) * L^8 / L^9 = _
    field_simp
  have clip := clippedSum f n L hL
  have cnt := (hr.trans (incidence f n)).trans clip
  have hsmall : (n:ℝ)/L ≤ A*n/2 := by
    apply (div_le_iff₀ hL).mpr
    have e := (div_le_iff₀ hA).mp hlA
    nlinarith [mul_le_mul_of_nonneg_left e npos.le]
  have hmass : A*n/2 ≤ hits f n * L^18 := by linarith
  have hg : 2*(f.natDegree:ℝ) ≤ A*L^3 := by
    have e := (div_le_iff₀ hA).mp hlg
    have hp : L ≤ L^3 := by simpa using (pow_le_pow_right₀ h1 (by decide : 1≤3))
    nlinarith [mul_le_mul_of_nonneg_left hp hA.le]
  have hfinal : L^3 ≤ log n * hits f n / ((f.natDegree:ℝ)*n) := by
    apply (le_div_iff₀ (mul_pos gpos npos)).mpr
    have hb : (f.natDegree:ℝ)*n ≤ hits f n * L^21 := by
      nlinarith only [mul_le_mul_of_nonneg_right hg npos.le,
        mul_le_mul_of_nonneg_right hmass (show 0≤L^3 by positivity)]
    have hk : L^24 = log n := by simp [L,scale_pow n hn.le]
    rw [← hk]
    nlinarith only [mul_le_mul_of_nonneg_right hb (show 0≤L^3 by positivity)]
  have hk : L^3 = (log n)^(1/8 : ℝ) := by
    rw [show L=scale n from rfl,scale_pow n hn.le]
    norm_num
  rw [hk] at hfinal
  have goal := (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hfinal) npos.le).trans ht
  simpa [Real.norm_eq_abs, abs_of_nonneg, npos.le] using goal

end OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1
