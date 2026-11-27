import OMAStatements.S_oeis_a331234

namespace OMA.R_oeis_a331234_R1

/-- Prime coordinates of a negative Pell solution arise at prime indices. -/
def H1 : Prop := ∀ x y : ℕ, x.Prime → y.Prime → x^2+1=2*y^2 →
    ∃ n : ℕ, n.Prime ∧
      (fun a : ℕ × ℕ => (a.1+2*a.2,a.1+a.2))^[n] (1,0) = (x,y)

/-- No prime index past 59 has both Pell coordinates prime. -/
def H2 : Prop := ∀ n : ℕ, n.Prime → 59 < n →
    let a := (fun t : ℕ × ℕ => (t.1+2*t.2,t.1+t.2))^[n] (1,0)
    ¬(a.1.Prime ∧ a.2.Prime)

lemma three_divisors {n : ℕ} (hn : 1 < n) (hc : n.divisors.card = 3) :
    ∃ p : ℕ, p.Prime ∧ n = p^2 := by
  classical
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ n := Nat.minFac_dvd _
  have hpn : p ≠ n := by
    intro he
    have hnpr : n.Prime := he ▸ hp
    rw [hnpr.divisors, Finset.card_insert_of_notMem (by simpa using hnpr.ne_one.symm), Finset.card_singleton] at hc
    omega
  obtain ⟨q, hq⟩ := hd
  have hp2 := hp.two_le
  have hq2 : 1 < q := by
    by_contra! h
    interval_cases q <;> simp_all
  have hlt : q < n := by nlinarith
  have hplt : p < n := by nlinarith
  have hqp : q = p := by
    by_contra h
    have incl : ({1,p,q,n} : Finset ℕ) ⊆ n.divisors := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl|rfl|rfl
      · exact Nat.mem_divisors.mpr ⟨one_dvd _,by omega⟩
      · exact Nat.mem_divisors.mpr ⟨Nat.minFac_dvd _,by omega⟩
      · exact Nat.mem_divisors.mpr ⟨hq ▸ dvd_mul_left _ _,by omega⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_rfl,by omega⟩
    have hk := Finset.card_le_card incl
    have hs : ({1,p,q,n} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega), Finset.card_singleton]
    omega
  exact ⟨p,hp,by rw [hq,hqp,pow_two]⟩

lemma two_divisors_min {n : ℕ} (hn : 1 < n) : 2 ≤ n.divisors.card := by
  have hs : ({1,n} : Finset ℕ) ⊆ n.divisors := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,by omega⟩
    · simp only [Finset.mem_singleton] at hz
      subst z
      exact Nat.mem_divisors.mpr ⟨dvd_rfl,by omega⟩
  have h := Finset.card_le_card hs
  simpa [show (1:ℕ) ≠ n by omega] using h

lemma prime_pair {a b : ℕ} (ha : 1 < a) (hb : 1 < b) (hp : a.Coprime b)
    (hm : (a*b).divisors.card = 9) :
    ∃ u v : ℕ, u.Prime ∧ v.Prime ∧ a = u^2 ∧ b = v^2 := by
  rw [hp.card_divisors_mul] at hm
  have h1 := two_divisors_min ha
  have h2 := two_divisors_min hb
  have h3 : a.divisors.card ≤ 4 := by nlinarith
  have h4 : b.divisors.card ≤ 4 := by nlinarith
  have hh : a.divisors.card = 3 ∧ b.divisors.card = 3 := by
    interval_cases h : a.divisors.card <;> omega
  obtain ⟨u,hu,eu⟩ := three_divisors ha hh.1
  obtain ⟨v,hv,ev⟩ := three_divisors hb hh.2
  exact ⟨u,v,hu,hv,eu,ev⟩

lemma certified {p a : ℕ} (fs : List ℕ) (hf : fs.prod = p-1)
    (hpr : ∀ q ∈ fs, q.Prime) (ht : (a : ZMod p)^(p-1)=1)
    (hw : ∀ q ∈ fs, (a : ZMod p)^((p-1)/q) ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p) ht
  intro q hq hd
  rw [← hf] at hd
  obtain ⟨r,hr,hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  have e := (Nat.prime_dvd_prime_iff_eq hq (hpr r hr)).mp hqr
  exact hw q (e ▸ hr)

set_option maxRecDepth 12000 in
lemma prime63018038201 : Nat.Prime 63018038201 := by
  apply certified (a := 6) [2,2,2,5,5,13,13,29,239,269] (by decide)
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals first | exact prime63018038201 | norm_num
  · simp only [Nat.reduceSub]; reduce_mod_char
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Nat.reduceSub,Nat.reduceDiv] <;> reduce_mod_char <;> decide

set_option maxRecDepth 12000 in
lemma prime13558774610046711780701 : Nat.Prime 13558774610046711780701 := by
  apply certified (a := 3) [2,2,5,5,7,29,31,31,41,269,63018038201] (by decide)
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals first | exact prime63018038201 | norm_num
  · simp only [Nat.reduceSub]; reduce_mod_char
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Nat.reduceSub,Nat.reduceDiv] <;> reduce_mod_char <;> decide

set_option maxRecDepth 12000 in
lemma prime19175002942688032928599 : Nat.Prime 19175002942688032928599 := by
  apply certified (a := 3) [2,3,3,11,19,59,601,2281,63018038201] (by decide)
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals first | exact prime63018038201 | norm_num
  · simp only [Nat.reduceSub]; reduce_mod_char
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Nat.reduceSub,Nat.reduceDiv] <;> reduce_mod_char <;> decide

lemma pell_bound (param : H1) (upper : H2) {x y : ℕ} (hx : x.Prime) (hy : y.Prime)
    (he : x^2+1=2*y^2) : x*y ≤ 19175002942688032928599*13558774610046711780701 := by
  let step (a : ℕ × ℕ) := (a.1+2*a.2,a.1+a.2)
  let seq (n : ℕ) := step^[n] (1,0)
  obtain ⟨n, hn, hxy⟩ := param x y hx hy he
  change seq n = (x,y) at hxy
  have hn' : n ≤ 59 := by
    by_contra! h
    have hh := upper n hn h
    change ¬((seq n).1.Prime ∧ (seq n).2.Prime) at hh
    exact hh (hxy ▸ And.intro hx hy)
  have mono : Monotone seq := by
    apply monotone_nat_of_le_succ
    intro m
    change seq m ≤ step^[m+1] (1,0)
    rw [Function.iterate_succ_apply']
    exact ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  have last : seq 59 = (19175002942688032928599,13558774610046711780701) := by decide +kernel
  have lo := mono hn'
  rw [hxy,last] at lo
  exact Nat.mul_le_mul lo.1 lo.2

lemma even_case {p q : ℕ} (hp : p.Prime) (he : q^2 = 2*p^2+1) : p = 2 := by
  have hm : ∀ a b : ZMod 8, b^2 = 2*a^2+1 → a.val % 2 = 0 := by decide
  have hh : (q : ZMod 8)^2 = 2*(p : ZMod 8)^2+1 := by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using congrArg (fun z : ℕ => (z : ZMod 8)) he
  have h := hm p q hh
  rw [ZMod.val_natCast] at h
  rcases hp.eq_two_or_odd with h' | h'
  · exact h'
  · omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a331234.main := by
  intro param upper
  have ha := prime13558774610046711780701
  have hb := prime19175002942688032928599
  have hc := Nat.coprime_pow_primes 2 2 ha hb (by decide)
  constructor
  · constructor
    · exact ⟨19175002942688032928599^2, by decide +kernel⟩
    · rw [mul_pow, hc.card_divisors_mul, Nat.divisors_prime_pow ha, Nat.divisors_prime_pow hb]
      simp
  · rintro _ ⟨⟨k,rfl⟩, hdiv⟩
    by_cases hsmall : k ≤ 3
    · interval_cases k <;> decide
    have hco : k.Coprime (k+1) := by simp
    rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t,ht⟩
    · have ek : k = 2*t := by omega
      have et : k*(k+1)/2 = t*(k+1) := by
        have he : k*(k+1) = t*(k+1)*2 := by rw [ek]; ring
        rw [he, Nat.mul_div_cancel _ (by decide : 0 < 2)]
      rw [et] at hdiv ⊢
      have hp := Nat.Coprime.of_dvd_left (show t ∣ k from ⟨2, by omega⟩) hco
      obtain ⟨p,q,hp,hq,ep,eq⟩ := prime_pair (by omega) (by omega) hp hdiv
      have he : q^2 = 2*p^2+1 := by omega
      have htwo := even_case hp he
      rw [htwo] at ep
      have ht4 : t=4 := by omega
      rw [ht4] at ek
      rw [ht4,ek]
      decide
    · have ek : k = 2*t+1 := by omega
      have et : k*(k+1)/2 = k*(t+1) := by
        have he : k*(k+1) = k*(t+1)*2 := by rw [ek]; ring
        rw [he, Nat.mul_div_cancel _ (by decide : 0 < 2)]
      rw [et] at hdiv ⊢
      have hp := Nat.Coprime.of_dvd_right (show t+1 ∣ k+1 from ⟨2,by omega⟩) hco
      obtain ⟨q,p,hq,hp,eq,ep⟩ := prime_pair (by omega) (by omega) hp hdiv
      have he : q^2+1 = 2*p^2 := by omega
      have cap := Nat.pow_le_pow_left (pell_bound param upper hq hp he) 2
      rw [eq,ep,←mul_pow]
      simpa only [mul_comm 19175002942688032928599 13558774610046711780701] using cap

end OMA.R_oeis_a331234_R1

