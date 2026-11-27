import OMAReductions.R_Erdos647_erdos_647_variants_infinite_R1

theorem two_mul_divisor_count_le {j : ℕ} (hj : 0 < j) :
    2 * j.divisors.card ≤ j + 2 := by
  have hsub : j.properDivisors ⊆ Finset.Icc 1 (j / 2) := by
    intro d hd
    refine Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_properDivisors hd, ?_⟩
    obtain ⟨k, hk, hjk⟩ := (Nat.mem_properDivisors_iff_exists hj.ne').mp hd
    have := Nat.mul_le_mul_left d (show 2 ≤ k from hk)
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  rw [← Nat.insert_self_properDivisors hj.ne', Finset.card_insert_of_notMem
    Nat.self_notMem_properDivisors]
  omega

theorem divisor_count_mul_prime_le (j : ℕ) {p : ℕ} (hp : p.Prime) :
    (j * p).divisors.card ≤ 2 * j.divisors.card := by
  by_cases hj : j = 0
  · simp [hj]
  let scaled := j.divisors.image (p * ·)
  have hsub : (j * p).divisors ⊆ j.divisors ∪ scaled := by
    intro d hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
    apply Finset.mem_union.mpr
    by_cases hpd : p ∣ d
    · obtain ⟨k, rfl⟩ := hpd
      have hk : k ∣ j := (mul_dvd_mul_iff_left hp.ne_zero).mp (by
        simpa only [mul_comm j p] using hdvd)
      exact Or.inr (Finset.mem_image.mpr ⟨k, Nat.mem_divisors.mpr ⟨hk, hj⟩, rfl⟩)
    · exact Or.inl (Nat.mem_divisors.mpr
        ⟨(hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_right hdvd, hj⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hscaled : scaled.card ≤ j.divisors.card := Finset.card_image_le
  omega

/- A necessary prime-pair condition for the three-term window of Erdős problem 647. -/

open ArithmeticFunction.sigma
namespace Erdos647Partial

lemma four_divisors {a b n : ℕ} (ha : 1 < a) (hb : 1 < b) (han : a < n)
    (hbn : b < n) (hab : a ≠ b) (da : a ∣ n) (db : b ∣ n) : 4 ≤ n.divisors.card := by
  have hn : n ≠ 0 := by omega
  have hs : ({1,a,b,n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [Nat.mem_divisors, *]
  have hc := Finset.card_le_card hs
  simpa (disch := simp <;> omega) only [Finset.card_insert_of_notMem, Finset.card_singleton] using hc

lemma five_divisors {d q : ℕ} (hd : 2 < d) (hdq : d < q) (dd : d ∣ 2*q) :
    5 ≤ (2*q).divisors.card := by
  have hq : 2 < q := by omega
  have hn : 2*q ≠ 0 := by omega
  have hs : ({1,2,d,q,2*q} : Finset ℕ) ⊆ (2*q).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [Nat.mem_divisors, *]
  have hc := Finset.card_le_card hs
  simpa (disch := simp <;> omega) only [Finset.card_insert_of_notMem, Finset.card_singleton] using hc

lemma k3_prime_pair {n : ℕ} (hn : 10 < n)
    (h : (⨆ m : Set.Ioo (n - 3) n, (m : ℕ) + σ 0 m) ≤ n + 2) :
    ∃ q : ℕ, q.Prime ∧ (2*q+1).Prime ∧ n = 2*q+2 := by
  have hshift (m : ℕ) (hm : m ∈ Set.Ioo (n-3) n) : m + m.divisors.card ≤ n+2 := by
    let f := fun x : Set.Ioo (n-3) n => (x : ℕ) + σ 0 x
    have hbound := le_ciSup (f := f) (Set.finite_range f).bddAbove (⟨m, hm⟩ : Set.Ioo (n-3) n)
    simpa [f, ArithmeticFunction.sigma_zero_apply] using hbound.trans h
  have h1 := hshift (n-1) (by constructor <;> omega)
  have h2 := hshift (n-2) (by constructor <;> omega)
  have heven : n % 2 = 0 := by
    by_contra hodd
    let t := (n-1)/2
    have ht : 2 < t := by dsimp [t]; omega
    have he : n-1 = 2*t := by dsimp [t]; omega
    have hc := four_divisors (a := 2) (b := t) (n := n-1) (by decide) (by omega)
      (by omega) (by omega) (by omega) (he ▸ dvd_mul_right 2 t) (he ▸ dvd_mul_left t 2)
    omega
  let q := (n-2)/2
  have hq : 4 < q := by dsimp [q]; omega
  have eqn : n = 2*q+2 := by dsimp [q]; omega
  have hq' : (2*q).divisors.card ≤ 4 := by
    have he : n-2=2*q := by omega
    rw [he] at h2
    omega
  have hpq : q.Prime := by
    by_contra hnp
    obtain ⟨d,hd,hd2,hdq⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 2 ≤ q) hnp
    by_cases hdeq : d = 2
    · subst d
      have hfour : 4 ∣ 2*q := by simpa using Nat.mul_dvd_mul_left 2 hd
      have := five_divisors (d:=4) (q:=q) (by decide) hq hfour
      omega
    · have := five_divisors (d:=d) (q:=q) (by omega) hdq (hd.trans (dvd_mul_left q 2))
      omega
  refine ⟨q, hpq, ?_, eqn⟩
  by_contra hnp
  obtain ⟨a,b,ha,hb,hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ 2*q+1)).mp hnp
  have ha1 : 1 < a := by
    by_contra hna
    interval_cases a <;> simp_all
  have hb1 : 1 < b := by
    by_contra hnb
    interval_cases b <;> simp_all
  have hne : a ≠ b := by
    intro he
    subst b
    have hmod := congrArg (· % 4) hab
    rw [Nat.mul_mod] at hmod
    obtain ⟨s,hs⟩ := hpq.odd_iff.mpr (by omega : 3 ≤ q)
    have : a % 4 < 4 := Nat.mod_lt _ (by decide)
    have hright : (2*q+1)%4=3 := by omega
    change (a%4*(a%4))%4 = (2*q+1)%4 at hmod
    rw [hright] at hmod
    interval_cases a % 4 <;> norm_num at hmod
  have hc := four_divisors ha1 hb1 ha hb hne (hab ▸ dvd_mul_right a b) (hab ▸ dvd_mul_left b a)
  have he : n-1=2*q+1 := by omega
  rw [he] at h1
  omega

end Erdos647Partial

/- The four- and five-term windows in Erdős 647 force three and four simultaneous primes. -/

open ArithmeticFunction ArithmeticFunction.sigma
namespace Erdos647Partial

lemma sigma_at_shift {k n : ℕ}
    (h : (⨆ x : Set.Ioo (n-k) n, (x : ℕ) + σ 0 x) ≤ n+2) {m : ℕ}
    (hm : m ∈ Set.Ioo (n-k) n) : m + σ 0 m ≤ n+2 := by
  let f := fun x : Set.Ioo (n-k) n => (x : ℕ) + σ 0 x
  exact (le_ciSup (f := f) (Set.finite_range f).bddAbove (⟨m,hm⟩ : Set.Ioo (n-k) n)).trans h

lemma prime_of_sigma_le_two {m : ℕ} (hm : 2 ≤ m) (h : σ 0 m ≤ 2) : m.Prime := by
  by_contra hnp
  obtain ⟨d,hd,hd2,hdm⟩ := Nat.exists_dvd_of_not_prime2 hm hnp
  have hn : m ≠ 0 := by omega
  have hs : ({1,d,m} : Finset ℕ) ⊆ m.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [Nat.mem_divisors, *]
  have hc := Finset.card_le_card hs
  simp (disch := simp <;> omega) only [Finset.card_insert_of_notMem,Finset.card_singleton] at hc
  rw [sigma_zero_apply] at h
  omega

lemma large_nine_multiple {s : ℕ} (hs : 9 < s) : 6 ≤ σ 0 (9*s) := by
  have hn : 9*s ≠ 0 := by omega
  have hd3 : 3 ∣ 9*s := (by decide : 3 ∣ 9).trans (dvd_mul_right 9 s)
  have hd3s : 3*s ∣ 9*s := Nat.mul_dvd_mul (by decide : 3 ∣ 9) (dvd_refl s)
  have hsub : ({1,3,9,s,3*s,9*s} : Finset ℕ) ⊆ (9*s).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Nat.mem_divisors, *]
  rw [sigma_zero_apply]
  simpa (disch := simp <;> omega) only [Finset.card_insert_of_notMem,Finset.card_singleton]
    using Finset.card_le_card hsub

lemma large_eight_multiple {s : ℕ} (hs : 8 < s) : 7 ≤ σ 0 (8*s) := by
  have hn : 8*s ≠ 0 := by omega
  have hd2 : 2 ∣ 8*s := (by decide : 2 ∣ 8).trans (dvd_mul_right 8 s)
  have hd4 : 4 ∣ 8*s := (by decide : 4 ∣ 8).trans (dvd_mul_right 8 s)
  have hd2s : 2*s ∣ 8*s := Nat.mul_dvd_mul (by decide : 2 ∣ 8) (dvd_refl s)
  have hd4s : 4*s ∣ 8*s := Nat.mul_dvd_mul (by decide : 4 ∣ 8) (dvd_refl s)
  have hsub : ({1,2,4,8,s,2*s,4*s} : Finset ℕ) ⊆ (8*s).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Nat.mem_divisors, *]
  rw [sigma_zero_apply]
  simpa (disch := simp <;> omega) only [Finset.card_insert_of_notMem,Finset.card_singleton]
    using Finset.card_le_card hsub

lemma prime_of_three_mul_sigma {r : ℕ} (hr : 27 < r) (h : σ 0 (3*r) ≤ 5) : r.Prime := by
  by_cases hd : 3 ∣ r
  · obtain ⟨s,hs⟩ := hd
    have hc := large_nine_multiple (s:=s) (by omega)
    have he : 3*r=9*s := by omega
    rw [he] at h
    omega
  · have hc := (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hd
    rw [isMultiplicative_sigma.map_mul_of_coprime hc] at h
    have ht : σ 0 3 = 2 := by simpa using sigma_zero_apply_prime_pow (i:=1) (by decide : Nat.Prime 3)
    rw [ht] at h
    exact prime_of_sigma_le_two (by omega) (by omega)

lemma prime_of_four_mul_sigma {r : ℕ} (hr : 16 < r) (h : σ 0 (4*r) ≤ 6) : r.Prime := by
  by_cases hd : 2 ∣ r
  · obtain ⟨s,hs⟩ := hd
    have hc := large_eight_multiple (s:=s) (by omega)
    have he : 4*r=8*s := by omega
    rw [he] at h
    omega
  · have hc : Nat.Coprime 4 r := (Nat.prime_two.coprime_iff_not_dvd.mpr hd).pow_left 2
    rw [isMultiplicative_sigma.map_mul_of_coprime hc] at h
    have ht : σ 0 4 = 3 := sigma_zero_apply_prime_pow (i:=2) Nat.prime_two
    rw [ht] at h
    exact prime_of_sigma_le_two (by omega) (by omega)

lemma k4_prime_triple_from_offsets {k n : ℕ} (hk : 4 ≤ k) (hn : 100 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), j < k → (n-j).divisors.card ≤ j+2) :
    ∃ q r : ℕ, q.Prime ∧ (2*q+1).Prime ∧ r.Prime ∧ n = 2*q+2 ∧ n = 3*r+3 := by
  have : Nonempty (Set.Ioo (n-3) n) := ⟨⟨n-1, by constructor <;> omega⟩⟩
  have h3 : (⨆ m : Set.Ioo (n-3) n, (m : ℕ) + σ 0 m) ≤ n+2 := by
    apply ciSup_le
    intro m
    obtain ⟨hm1,hm2⟩ := m.property
    have one := h 1 (by decide) (by omega)
    have two := h 2 (by decide) (by omega)
    rcases (by omega : m.val = n-1 ∨ m.val = n-2) with hm | hm <;>
      change m.val + σ 0 m.val ≤ n + 2 <;> rw [hm, sigma_zero_apply] <;> omega
  obtain ⟨q,hq,hpair,he⟩ := k3_prime_pair (by omega) h3
  have nq : ¬ 3 ∣ q := Nat.prime_def_lt'.mp hq |>.2 3 (by decide) (by omega)
  have nq' : ¬ 3 ∣ 2*q+1 := Nat.prime_def_lt'.mp hpair |>.2 3 (by decide) (by omega)
  have rem : q % 3 = 2 := by
    have hrem := Nat.mod_lt q (by decide : 0 < 3)
    by_contra hbad
    rcases (by omega : q%3=0 ∨ q%3=1) with h0 | h1
    · exact nq ⟨q/3, by omega⟩
    · exact nq' ⟨2*(q/3)+1, by omega⟩
  let r := 2*(q/3)+1
  have hr : n = 3*r+3 := by dsimp [r]; omega
  have hz := h 3 (by decide) (by omega)
  rw [show n-3=3*r by omega, ← sigma_zero_apply] at hz
  exact ⟨q,r,hq,hpair,prime_of_three_mul_sigma (by omega) (by omega),he,hr⟩

lemma k5_prime_quadruple_from_offsets {k n : ℕ} (hk : 5 ≤ k) (hn : 100 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), j < k → (n-j).divisors.card ≤ j+2) :
    ∃ q r s : ℕ, q.Prime ∧ (2*q+1).Prime ∧ r.Prime ∧ s.Prime ∧
      n = 2*q+2 ∧ n = 3*r+3 ∧ n = 4*s+4 ∧ q % 4 = 3 ∧ 120 ∣ n := by
  obtain ⟨q,r,hq,hpair,hr,he,he'⟩ := k4_prime_triple_from_offsets (by omega) hn h
  obtain ⟨v,hv⟩ := hq.odd_iff.mpr (by omega : 3 ≤ q)
  let s := (n-4)/4
  have hs : n = 4*s+4 := by dsimp [s]; omega
  have hz := h 4 (by decide) (by omega)
  rw [show n-4=4*s by omega, ← sigma_zero_apply] at hz
  have hps : s.Prime := prime_of_four_mul_sigma (by omega) (by omega)
  obtain ⟨w,hw⟩ := hps.odd_iff.mpr (by omega : 3 ≤ s)
  have a : ¬ 5 ∣ q := Nat.prime_def_lt'.mp hq |>.2 5 (by decide) (by omega)
  have b : ¬ 5 ∣ 2*q+1 := Nat.prime_def_lt'.mp hpair |>.2 5 (by decide) (by omega)
  have c : ¬ 5 ∣ r := Nat.prime_def_lt'.mp hr |>.2 5 (by decide) (by omega)
  have d : ¬ 5 ∣ s := Nat.prime_def_lt'.mp hps |>.2 5 (by decide) (by omega)
  refine ⟨q,r,s,hq,hpair,hr,hps,he,he',hs,by omega,?_⟩
  have hn8 : 8 ∣ n := ⟨w+1, by omega⟩
  have hn3 : 3 ∣ n := ⟨r+1, by omega⟩
  have hn24 : 24 ∣ n := (by decide : Nat.Coprime 3 8).mul_dvd_of_dvd_of_dvd hn3 hn8
  obtain ⟨t,ht⟩ := hn24
  have ht' : t % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases hrem : t%5
  · exact ⟨t/5,by omega⟩
  · exact (d ⟨6*(t/5)+1,by omega⟩).elim
  · exact (c ⟨8*(t/5)+3,by omega⟩).elim
  · exact (a ⟨12*(t/5)+7,by omega⟩).elim
  · exact (b ⟨24*(t/5)+19,by omega⟩).elim

lemma k7_extra_prime_from_offsets {k n : ℕ} (hk : 7 ≤ k) (hn : 100 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), j < k → (n-j).divisors.card ≤ j+2) :
    ∃ r : ℕ, r.Prime ∧ n=6*r+6 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,t,ht⟩ := k5_prime_quadruple_from_offsets (by omega) hn h
  let r := 20*t-1
  have he : n=6*r+6 := by dsimp [r]; omega
  have htpos : 0 < t := by omega
  have hz := h 6 (by decide) (by omega)
  rw [show n-6=2*(3*r) by omega, ← sigma_zero_apply] at hz
  have hc : Nat.Coprime 2 (3*r) := Nat.prime_two.coprime_iff_not_dvd.mpr (by dsimp [r]; omega)
  rw [isMultiplicative_sigma.map_mul_of_coprime hc] at hz
  have htau : σ 0 2 = 2 := by simpa using sigma_zero_apply_prime_pow (i:=1) Nat.prime_two
  rw [htau] at hz
  by_cases hr : 27 < r
  · exact ⟨r, prime_of_three_mul_sigma hr (by omega), he⟩
  · have hsmall : r = 19 := by dsimp [r] at *; omega
    exact ⟨r, hsmall ▸ (by decide : Nat.Prime 19), he⟩

lemma k13_search_necessary_from_offsets {k n : ℕ} (hk : 13 ≤ k) (hn : 100 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), j < k → (n-j).divisors.card ≤ j+2) :
    ∃ u : ℕ, 0 < u ∧ n = 840*u ∧
      ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), ((840/j)*u-1).Prime := by
  obtain ⟨q,r,s,hq,h2q,hr,hs,he1,he3,he4,_,t,ht⟩ := k5_prime_quadruple_from_offsets (by omega) hn h
  obtain ⟨v,hv,he6⟩ := k7_extra_prime_from_offsets (by omega) hn h
  let w := 10*t-1
  have he12 : n = 12*w+12 := by dsimp [w]; omega
  have hz := h 12 (by decide) (by omega)
  rw [show n-12=4*(3*w) by omega, ← sigma_zero_apply] at hz
  have hc' : Nat.Coprime 2 (3*w) := Nat.prime_two.coprime_iff_not_dvd.mpr (by dsimp [w]; omega)
  have hc : Nat.Coprime 4 (3*w) := hc'.pow_left 2
  rw [isMultiplicative_sigma.map_mul_of_coprime hc] at hz
  have htau : σ 0 4 = 3 := sigma_zero_apply_prime_pow (i:=2) Nat.prime_two
  rw [htau] at hz
  have hw : w.Prime := by
    by_cases hl : 27 < w
    · exact prime_of_three_mul_sigma hl (by omega)
    · have hsmall : w = 9 ∨ w = 19 := by dsimp [w] at *; omega
      rcases hsmall with h9 | h19
      · have bad : 2*q+1=119 := by omega
        rw [bad] at h2q
        exact ((by decide : ¬ Nat.Prime 119) h2q).elim
      · exact h19 ▸ (by decide : Nat.Prime 19)
  have a : ¬ 7 ∣ 2*q+1 := Nat.prime_def_lt'.mp h2q |>.2 7 (by decide) (by omega)
  have b : ¬ 7 ∣ q := Nat.prime_def_lt'.mp hq |>.2 7 (by decide) (by omega)
  have c : ¬ 7 ∣ r := Nat.prime_def_lt'.mp hr |>.2 7 (by decide) (by omega)
  have d : ¬ 7 ∣ s := Nat.prime_def_lt'.mp hs |>.2 7 (by decide) (by omega)
  have e : ¬ 7 ∣ w := Nat.prime_def_lt'.mp hw |>.2 7 (by decide) (by omega)
  have f : ¬ 7 ∣ v := Nat.prime_def_lt'.mp hv |>.2 7 (by decide) (by omega)
  have ht7 : 7 ∣ t := by
    have hrem' : t%7 < 7 := Nat.mod_lt _ (by decide)
    interval_cases hrem : t%7
    · exact ⟨t/7, by omega⟩
    · exact (a ⟨120*(t/7)+17,by omega⟩).elim
    · exact (b ⟨60*(t/7)+17,by omega⟩).elim
    · exact (c ⟨40*(t/7)+17,by omega⟩).elim
    · exact (d ⟨30*(t/7)+17,by omega⟩).elim
    · exact (e ⟨10*(t/7)+7,by omega⟩).elim
    · exact (f ⟨20*(t/7)+17,by omega⟩).elim
  obtain ⟨u,hu⟩ := ht7
  refine ⟨u, by omega, by omega, ?_⟩
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num only [Nat.reduceDiv]
  · rwa [show 840*u-1 = 2*q+1 by omega]
  · rwa [show 420*u-1 = q by omega]
  · rwa [show 280*u-1 = r by omega]
  · rwa [show 210*u-1 = s by omega]
  · rwa [show 140*u-1 = v by omega]
  · rwa [show 70*u-1 = w by omega]

lemma k13_sparse_necessary {n : ℕ} (hn : 100 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), (n-j).divisors.card ≤ j+2) :
    ∃ u : ℕ, 0 < u ∧ n = 840*u ∧
      ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), ((840/j)*u-1).Prime := by
  exact k13_search_necessary_from_offsets (k:=13) (by decide) hn (fun j hj _ => h j hj)

lemma k13_sparse_necessary_2520 {n : ℕ} (hn : 100 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), (n-j).divisors.card ≤ j+2) :
    ∃ u : ℕ, 0 < u ∧ n = 2520*u ∧
      ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), ((2520/j)*u-1).Prime := by
  obtain ⟨t, ht, hn', hpr⟩ := k13_sparse_necessary hn h
  have hp := hpr 3 (by decide)
  have hq := hpr 6 (by decide)
  norm_num only [Nat.reduceDiv] at hp hq
  have h1 : ¬ 3 ∣ 280*t-1 := Nat.prime_def_lt'.mp hp |>.2 3 (by decide) (by omega)
  have h2 : ¬ 3 ∣ 140*t-1 := Nat.prime_def_lt'.mp hq |>.2 3 (by decide) (by omega)
  have h3 : 3 ∣ t := by
    have hrem' : t%3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hrem : t%3
    · exact ⟨t/3, by omega⟩
    · exact (h1 ⟨280*(t/3)+93,by omega⟩).elim
    · exact (h2 ⟨140*(t/3)+93,by omega⟩).elim
  obtain ⟨u,hu⟩ := h3
  refine ⟨u, by omega, by omega, ?_⟩
  intro j hj
  have hp' := hpr j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num only [Nat.reduceDiv] at * <;> convert hp' using 1 <;> omega

lemma divisor_count_at_offset {k n : ℕ} (hn : 100 < n)
    (h : (⨆ m : Set.Ioo (n-k) n, (m : ℕ) + σ 0 m) ≤ n+2) :
    ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), j < k → (n-j).divisors.card ≤ j+2 := by
  intro j hj hjk
  have hjrange : 1 ≤ j ∧ j ≤ 12 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  have hz := sigma_at_shift h (m:=n-j) (by constructor <;> omega)
  rw [sigma_zero_apply] at hz
  omega

lemma k4_prime_triple {k n : ℕ} (hk : 4 ≤ k) (hn : 100 < n)
    (h : (⨆ m : Set.Ioo (n-k) n, (m : ℕ) + σ 0 m) ≤ n+2) :
    ∃ q r : ℕ, q.Prime ∧ (2*q+1).Prime ∧ r.Prime ∧ n = 2*q+2 ∧ n = 3*r+3 := by
  exact k4_prime_triple_from_offsets hk hn (divisor_count_at_offset hn h)

lemma k5_prime_quadruple {k n : ℕ} (hk : 5 ≤ k) (hn : 100 < n)
    (h : (⨆ m : Set.Ioo (n-k) n, (m : ℕ) + σ 0 m) ≤ n+2) :
    ∃ q r s : ℕ, q.Prime ∧ (2*q+1).Prime ∧ r.Prime ∧ s.Prime ∧
      n = 2*q+2 ∧ n = 3*r+3 ∧ n = 4*s+4 ∧ q % 4 = 3 ∧ 120 ∣ n := by
  exact k5_prime_quadruple_from_offsets hk hn (divisor_count_at_offset hn h)

lemma k7_extra_prime {k n : ℕ} (hk : 7 ≤ k) (hn : 100 < n)
    (h : (⨆ m : Set.Ioo (n-k) n, (m : ℕ) + σ 0 m) ≤ n+2) :
    ∃ r : ℕ, r.Prime ∧ n=6*r+6 := by
  exact k7_extra_prime_from_offsets hk hn (divisor_count_at_offset hn h)

lemma k13_search_necessary {k n : ℕ} (hk : 13 ≤ k) (hn : 100 < n)
    (h : (⨆ m : Set.Ioo (n-k) n, (m : ℕ) + σ 0 m) ≤ n+2) :
    ∃ u : ℕ, 0 < u ∧ n = 840*u ∧
      ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), ((840/j)*u-1).Prime := by
  exact k13_search_necessary_from_offsets hk hn (divisor_count_at_offset hn h)

end Erdos647Partial

/- Remove small exceptions with a finite kernel certificate. -/

namespace Erdos647Partial

lemma sparse_witness_above_hundred {n : ℕ} (hn : 24 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), (n-j).divisors.card ≤ j+2) : 100 < n := by
  by_contra hsmall
  have excluded : ∀ i : Fin 76, ∃ j ∈ ({1,2,3,4,6,12} : Finset ℕ),
      j+2 < (i.val+25-j).divisors.card := by decide
  obtain ⟨j,hj,hh⟩ := excluded ⟨n-25,by omega⟩
  change j+2 < ((n-25)+25-j).divisors.card at hh
  rw [show n-25+25=n by omega] at hh
  exact (Nat.not_lt_of_ge (h j hj)) hh

lemma sparse_necessary_above_24 {n : ℕ} (hn : 24 < n)
    (h : ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), (n-j).divisors.card ≤ j+2) :
    ∃ u : ℕ, 0 < u ∧ n = 2520*u ∧
      ∀ j ∈ ({1,2,3,4,6,12} : Finset ℕ), ((2520/j)*u-1).Prime :=
  k13_sparse_necessary_2520 (sparse_witness_above_hundred hn h) h

end Erdos647Partial

/- Divisor bounds for offsets where the remaining cofactor is prime. -/

namespace Erdos647Partial

lemma divisor_bound_of_prime_cofactor {L j t : ℕ} (hj : 0 < j) (hd : j ∣ L)
    (hp : ((L / j) * t - 1).Prime) :
    (L * t - j).divisors.card ≤ j + 2 := by
  have he : j * ((L / j) * t - 1) = L * t - j := by
    rw [Nat.mul_sub, ← Nat.mul_assoc, Nat.mul_div_cancel' hd, Nat.mul_one]
  rw [← he]
  exact (divisor_count_mul_prime_le j hp).trans (two_mul_divisor_count_le hj)

lemma six_short_offset_bounds {t : ℕ}
    (hprime : ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), ((2520 / j) * t - 1).Prime) :
    ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), (2520 * t - j).divisors.card ≤ j + 2 := by
  intro j hj
  apply divisor_bound_of_prime_cofactor _ _ (hprime j hj)
  · have : ∀ i ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), 0 < i := by decide
    exact this j hj
  · have : ∀ i ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), i ∣ 2520 := by decide
    exact this j hj

end Erdos647Partial


theorem OMA.solution : OMA.R_Erdos647_erdos_647_variants_infinite_R1.H2 := by
  intro n hn
  constructor
  · exact Erdos647Partial.sparse_necessary_above_24 hn
  · rintro ⟨t, _, rfl, hp⟩
    exact Erdos647Partial.six_short_offset_bounds hp


