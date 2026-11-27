import OMAReductions.R_Erdos940_erdos_940_variants_three_powerful_R1

/-! Heath-Brown's fixed-coefficient form x²+y²+125z² is obtained from
representations of 5n by three squares with a coordinate divisible by 25.
We only need distribution in this congruence class when 25 does not
divide n. In the other case an ordinary representation of 5(n/25)
suffices because one coordinate vanishes modulo 5. The analytic
estimates are the three-square class number lower bound and the fixed
level theta-series bound of Blomer, Acta Arith. 114 (2004), Theorem 1. -/
namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R1
open Finset Filter Real
open scoped Classical

private lemma divide_pair {a b m:ℕ} (he:5*m=a^2+b^2) : ∃ u v:ℕ,m=u^2+v^2 := by
  apply Nat.eq_sq_add_sq_iff.mpr
  intro p hp h4
  obtain ⟨pp,pd,m0⟩ := Nat.mem_primeFactors.mp hp
  let : Fact p.Prime := ⟨pp⟩
  have h5 : ¬p∣5 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp h
    omega
  have pm : p∈(5*m).primeFactors := Nat.mem_primeFactors.mpr ⟨pp,dvd_mul_of_dvd_right pd _,mul_ne_zero (by decide) m0⟩
  have ev := Nat.eq_sq_add_sq_iff.mp ⟨a,b,he⟩ p pm h4
  simpa [padicValNat.mul (by decide : (5:ℕ)≠0) m0,padicValNat.eq_zero_of_not_dvd h5] using ev

private lemma descend {a b t n:ℕ} (he:5*n=a^2+b^2+(5*t)^2) :
    ∃ u v:ℕ,n=u^2+v^2+5*t^2 := by
  have le : 5*t^2≤n := by nlinarith only [he,Nat.zero_le (a^2+b^2)]
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le le
  obtain ⟨u,v,eq⟩ := divide_pair (a:=a) (b:=b) (m:=m) (by nlinarith only [hm,he])
  exact ⟨u,v,by omega⟩

private lemma ordinary {a b c n:ℕ} (he:5*n=a^2+b^2+c^2) :
    ∃ u v t:ℕ,n=u^2+v^2+5*t^2 := by
  have tab : ∀ x y z:ZMod 5,x^2+y^2+z^2=0 → x=0 ∨ y=0 ∨ z=0 := by decide +kernel
  have hz := congrArg (fun j:ℕ => (j:ZMod 5)) he
  push_cast at hz
  have hit := tab a b c (by simpa [show (5:ZMod 5)=0 by decide] using hz.symm)
  rcases hit with ha | hb | hc
  · obtain ⟨t,ta⟩ := (ZMod.natCast_eq_zero_iff ..).mp ha
    obtain ⟨u,v,e⟩ := descend (a:=b) (b:=c) (t:=t) (n:=n) (by rw [ta] at he; nlinarith only [he])
    exact ⟨u,v,t,e⟩
  · obtain ⟨t,tb⟩ := (ZMod.natCast_eq_zero_iff ..).mp hb
    obtain ⟨u,v,e⟩ := descend (a:=a) (b:=c) (t:=t) (n:=n) (by rw [tb] at he; nlinarith only [he])
    exact ⟨u,v,t,e⟩
  · obtain ⟨t,tc⟩ := (ZMod.natCast_eq_zero_iff ..).mp hc
    obtain ⟨u,v,e⟩ := descend (a:=a) (b:=b) (t:=t) (n:=n) (by rwa [←tc])
    exact ⟨u,v,t,e⟩

private lemma full125 (t:ℕ) : Nat.Full 2 (125*t^2) := by
  intro p hp
  obtain ⟨pp,div,_⟩ := Nat.mem_primeFactors.mp hp
  rcases pp.dvd_mul.mp div with h | h
  · change p ∣ 5^3 at h
    have eq := (Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp (pp.dvd_of_dvd_pow h)
    subst p
    exact dvd_mul_of_dvd_left (by decide : 5^2∣125) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (pp.dvd_of_dvd_pow h) 2) _

private lemma finish {u v t n:ℕ} (eq:n=u^2+v^2+125*t^2) :
    ∃ x y z:ℕ,Nat.Full 2 x ∧ Nat.Full 2 y ∧ Nat.Full 2 z ∧ n=x+y+z :=
  ⟨_,_,_,OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.sq_full u,
    OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.sq_full v,full125 t,eq⟩

-- The three-square class number lower bound at 5n, including square factors.
def H1 : Prop :=
  let S := fun n:ℕ => ((range (5*n+1)) ×ˢ ((range (5*n+1)) ×ˢ (range (5*n+1)))).filter
    (fun v:ℕ×ℕ×ℕ => 5*n=v.1^2+v.2.1^2+v.2.2^2)
  ∀ᶠ n:ℕ in atTop,n%8=7 → (n:ℝ)^(49/100:ℝ)≤(S n).card

-- A fixed-level congruence class occupies positive mass on the sphere.
-- Its local density ratio is bounded below for v_5(n) at most one.
-- The spinor error n^(13/28+epsilon) is smaller than n^(47/100).
def H2 : Prop :=
  let S := fun n:ℕ => ((range (5*n+1)) ×ˢ ((range (5*n+1)) ×ˢ (range (5*n+1)))).filter
    (fun v:ℕ×ℕ×ℕ => 5*n=v.1^2+v.2.1^2+v.2.2^2)
  ∃ c C:ℝ, 0<c ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop, n%8=7 → ¬25∣n →
    c*((S n).card:ℝ) ≤ (((S n).filter (fun v => 25∣v.2.2)).card:ℝ)+C*(n:ℝ)^(47/100:ℝ)

theorem main : H1 → H2 → OMA.R_Erdos940_erdos_940_variants_three_powerful_R1.H2 := by
  classical
  intro count balanced
  let S := fun n:ℕ => ((range (5*n+1)) ×ˢ ((range (5*n+1)) ×ˢ (range (5*n+1)))).filter
    (fun v:ℕ×ℕ×ℕ => 5*n=v.1^2+v.2.1^2+v.2.2^2)
  change ∀ᶠ n:ℕ in atTop,n%8=7 → (n:ℝ)^(49/100:ℝ)≤(S n).card at count
  obtain ⟨N,hN⟩ := eventually_atTop.mp count
  obtain ⟨c,C,cp,_,hb⟩ := balanced
  have lim := (tendsto_rpow_atTop (show 0<(2/100:ℝ) by norm_num)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hb,lim.eventually_gt_atTop (C/c),eventually_ge_atTop (25*(N+1))] with n bal big large
  intro seven
  have pos : 0<n := by omega
  have rp : 0<(n:ℝ) := by exact_mod_cast pos
  by_cases m25 : 25∣n
  · obtain ⟨m,rfl⟩ := m25
    have mp : 0<(m:ℝ) := by exact_mod_cast (show 0 < m by omega)
    have ct := hN m (by omega) (by simpa [Nat.mul_mod] using seven)
    obtain ⟨v,hv⟩ := (card_pos.mp (show 0<(S m).card by
      exact_mod_cast (rpow_pos_of_pos mp (49/100:ℝ)).trans_le ct))
    obtain ⟨a,b,t,eq⟩ := ordinary (mem_filter.mp hv).2
    exact finish (u:=5*a) (v:=5*b) (t:=t) (by nlinarith only [eq])
  · have ct := hN n (by omega) seven
    have h := bal seven m25
    let G := (S n).filter (fun v => 25∣v.2.2)
    change c*((S n).card:ℝ) ≤ (G.card:ℝ)+C*(n:ℝ)^(47/100:ℝ) at h
    change C/c<(n:ℝ)^(2/100:ℝ) at big
    have gain := mul_lt_mul_of_pos_right ((div_lt_iff₀ cp).mp big) (rpow_pos_of_pos rp (47/100:ℝ))
    have power : (n:ℝ)^(2/100:ℝ)*(n:ℝ)^(47/100:ℝ)=(n:ℝ)^(49/100:ℝ) := by rw [← rpow_add rp];norm_num
    have gpos : 0<(G.card:ℝ) := by
      nlinarith only [gain,mul_le_mul_of_nonneg_left ct cp.le,h,congrArg (c*·) power]
    obtain ⟨v,hv⟩ := card_pos.mp (show 0<G.card by exact_mod_cast gpos)
    obtain ⟨hv,⟨t,et⟩⟩ := mem_filter.mp hv
    have eq := (mem_filter.mp hv).2
    obtain ⟨a,b,he⟩ := descend (a:=v.1) (b:=v.2.1) (t:=5*t) (n:=n) (by
      change 5*n=v.1^2+v.2.1^2+v.2.2^2 at eq; rw [et] at eq; nlinarith only [eq])
    exact finish (u:=a) (v:=b) (t:=t) (by nlinarith only [he])

end OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R1
