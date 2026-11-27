import OMAReductions.R_Erdos694_erdos_694_variants_inf_unique_R1

/-!
A large prime factor of p−1 detects every competing totient preimage. A divisor
cutoff and a three-linear-form sieve bound the number of competing primes.
Ford, The distribution of totients, Section 1.2, describes the original result
of Erdős that motivates this reduction. Lemmas 2.5 and 2.6 there provide the
linear-form sieve and shifted-prime normal-order estimates used below.
-/

namespace OMA.R_Erdos694_erdos_694_variants_inf_unique_R1_H1_R1
open Finset Filter
open scoped Classical BigOperators

/-- Supply of shifted primes with a large prime factor, weaker than Fouvry's
positive-proportion theorem. Here log X is a constant times k to the tenth. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
  let X : ℕ := 2^(k^10)
  c*(X:ℝ) ≤ (((Ioc k X).filter fun p => p.Prime ∧
    ∃ s q : ℕ, 0 < s ∧ q.Prime ∧ p=s*q+1 ∧ n*s+1 < q).card:ℝ)*(k:ℝ)^10

/-- Normal order of the divisor function on shifted primes, with threshold
(log X) to the power 4/5, above the normal exponent log 2. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
  let X : ℕ := 2^(k^10)
  (((Ioc k X).filter fun p => p.Prime ∧ k^8 < (p-1).divisors.card).card:ℝ)*(k:ℝ)^10 ≤ ε*X

/-- Uniform upper-bound sieve for q, sq+1 and aq+1 with distinct positive slopes.
The exponent 29 leaves a power of k for the singular series. -/
def H3 : Prop := ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
  let X : ℕ := 2^(k^10)
  ∀ s a : ℕ, 0 < s → s^2 ≤ X → a ∈ (n*s).divisors → a ≠ s →
    (((Icc 1 (X/s)).filter fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime).card:ℝ)
 ≤ C*X/((s:ℝ)*(k:ℝ)^29)


/-- A prime divisor of a totient comes from a square divisor or a prime congruent
to one modulo that prime. -/
theorem factorSource {q x : ℕ} (hp : q.Prime) (hx : x ≠ 0) (h : q ∣ x.totient) :
    q^2 ∣ x ∨ ∃ r : ℕ, r.Prime ∧ r ∣ x ∧ q ∣ r-1 := by
  rw [Nat.totient_eq_prod_factorization hx] at h
  change q ∣ ∏ r ∈ x.primeFactors, r^(x.factorization r-1)*(r-1) at h
  obtain ⟨r,hr,div⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
  have pr := Nat.prime_of_mem_primeFactors hr
  rcases hp.dvd_mul.mp div with power|step
  · have qr := hp.dvd_of_dvd_pow power
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp pr).mp qr
    left
    apply (hp.pow_dvd_iff_le_factorization hx).mpr
    by_contra! small
    have zero : x.factorization q-1=0 := by omega
    rw [zero,pow_zero] at power
    exact hp.not_dvd_one power
  · exact Or.inr ⟨r,pr,Nat.dvd_of_mem_primeFactors hr,step⟩

/-- With p=sq+1 and q>ns+1, a preimage not divisible by p forces a second
prime aq+1, where a is a divisor of ns different from s. -/
theorem competitor {n s q x : ℕ} (hn : 0 < n) (hs : 0 < s) (hq : q.Prime)
    (large : n*s+1 < q) (phi : x.totient=n*s*q) (miss : ¬ s*q+1 ∣ x) :
    ∃ a ∈ (n*s).divisors, a ≠ s ∧ (a*q+1).Prime := by
  have xp : x ≠ 0 := by intro e; rw [e,Nat.totient_zero] at phi; have := Nat.mul_pos (Nat.mul_pos hn hs) hq.pos; omega
  rcases factorSource hq xp (phi ▸ dvd_mul_left q (n*s)) with square|⟨r,pr,rx,qr⟩
  · have d := Nat.totient_dvd_of_dvd square
    rw [Nat.totient_prime_pow_succ hq 1,pow_one,phi] at d
    have bound := Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos hn hs) hq.pos) d
    rw [Nat.mul_comm] at bound
    have := Nat.le_of_mul_le_mul_right bound hq.pos
    omega
  obtain ⟨a,ha⟩ := qr
  have eq : a*q+1=r := by rw [Nat.mul_comm]; have := pr.pos; omega
  have dv := Nat.totient_dvd_of_dvd rx
  rw [Nat.totient_prime pr,phi,ha,Nat.mul_comm q a] at dv
  have aDiv : a ∣ n*s := (Nat.mul_dvd_mul_iff_right hq.pos).mp dv
  refine ⟨a,Nat.mem_divisors.mpr ⟨aDiv,(Nat.mul_pos hn hs).ne'⟩,?_,eq ▸ pr⟩
  intro e
  subst a
  exact miss (eq.symm ▸ rx)

/-- Submultiplicativity needs no coprimality of the coefficient and the cofactor. -/
private theorem divisorsProduct {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a*b).divisors.card ≤ a.divisors.card*b.divisors.card := by
  have sub : (a*b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun z => z.1*z.2) := by
    intro v hv
    obtain ⟨c,d,hc,hd,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hv)
    exact mem_image.mpr ⟨(c,d),mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hc,ha.ne'⟩,Nat.mem_divisors.mpr ⟨hd,hb.ne'⟩⟩,rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (le_of_eq (card_product _ _)))


/-- Charge every exceptional prime to a slope pair. The sum over the cofactor s
is harmonic; the number of possible second slopes is bounded by the divisor cutoff. -/
private theorem countOverlap (n k X : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (Xdef : X=2^(k^10))
    (C : ℝ) (hC : 0 < C) (B : Finset ℕ)
    (cover : ∀ p∈B, ∃ s ∈ Icc 1 X, s^2 ≤ X ∧ s.divisors.card ≤ k^8 ∧
      ∃ a ∈ (n*s).divisors, a≠s ∧ ∃ q ∈ Icc 1 (X/s),
        q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime ∧ p=s*q+1)
    (sieve : ∀ s a : ℕ, 0 < s → s^2 ≤ X → a ∈ (n*s).divisors → a≠s →
      (((Icc 1 (X/s)).filter fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime).card:ℝ)
 ≤ C*X/((s:ℝ)*(k:ℝ)^29)) :
    (B.card:ℝ)*(k:ℝ)^10 ≤ 2*(n.divisors.card:ℝ)*C*X/k := by
  classical
  let D := (Icc 1 X).filter (fun s => s^2 ≤ X ∧ s.divisors.card ≤ k^8)
  let E (s : ℕ) := (n*s).divisors.erase s
  let Q (s a : ℕ) := (Icc 1 (X/s)).filter (fun q => q.Prime ∧ (s*q+1).Prime ∧ (a*q+1).Prime)
  let row (s) := (E s).biUnion (fun a => (Q s a).image (fun q => s*q+1))
  have sub : B ⊆ D.biUnion row := by
    intro p hp
    obtain ⟨s,hs,sq,div,a,da,ne,q,hq,pq,pp,pa,rfl⟩ := cover p hp
    exact mem_biUnion.mpr ⟨s,mem_filter.mpr ⟨hs,sq,div⟩,mem_biUnion.mpr
      ⟨a,mem_erase.mpr ⟨ne,da⟩,mem_image.mpr ⟨q,mem_filter.mpr ⟨hq,pq,pp,pa⟩,rfl⟩⟩⟩
  let W := (n.divisors.card:ℝ)*(k:ℝ)^8*(C*X/(k:ℝ)^29)
  have nonW : 0 ≤ W := by dsimp [W]; positivity
  have bound (s : ℕ) (mem : s ∈ D) : ((row s).card:ℝ) ≤ W*(s:ℝ)⁻¹ := by
    obtain ⟨hs,sq,div⟩ := mem_filter.mp mem
    have spos : 0 < s := (mem_Icc.mp hs).1
    have kids : (E s).card ≤ n.divisors.card*k^8 :=
      (card_le_card (erase_subset ..)).trans ((divisorsProduct hn spos).trans (Nat.mul_le_mul_left _ div))
    have sz : (row s).card ≤ ∑ a ∈ E s,(Q s a).card :=
      card_biUnion_le.trans (sum_le_sum fun a _ => card_image_le)
    calc ((row s).card:ℝ) ≤ ∑ a ∈ E s,((Q s a).card:ℝ) := by exact_mod_cast sz
      _ ≤ ∑ a ∈ E s,(C*X/((s:ℝ)*(k:ℝ)^29)) := sum_le_sum fun a ha =>
        sieve s a spos sq (mem_erase.mp ha).2 (mem_erase.mp ha).1
      _ = ((E s).card:ℝ)*(C*X/((s:ℝ)*(k:ℝ)^29)) := by simp
      _ ≤ ((n.divisors.card:ℝ)*(k:ℝ)^8)*(C*X/((s:ℝ)*(k:ℝ)^29)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast kids) (by positivity)
      _ = W*(s:ℝ)⁻¹ := by dsimp [W]; ring
  have harm : ∑ s ∈ Icc 1 X,(s:ℝ)⁻¹ ≤ 2*(k:ℝ)^10 := by
    have lim := harmonic_le_one_add_log X
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at lim
    apply lim.trans
    rw [Xdef,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    have z := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    have p : 1 ≤ (k:ℝ)^10 := one_le_pow₀ (by exact_mod_cast hk)
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)^10 by positivity) (show 0 ≤ 1-Real.log 2 by linarith)]
  have agg : (B.card:ℝ) ≤ W*(2*(k:ℝ)^10) := by
    have card := (card_le_card sub).trans card_biUnion_le
    calc (B.card:ℝ) ≤ ∑ s ∈ D,((row s).card:ℝ) := by exact_mod_cast card
      _ ≤ ∑ s ∈ D,W*(s:ℝ)⁻¹ := sum_le_sum bound
      _ ≤ ∑ s ∈ Icc 1 X,W*(s:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)
      _ = W*(∑ s ∈ Icc 1 X,(s:ℝ)⁻¹) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left harm nonW
  have kpos : (0:ℝ) < k := by exact_mod_cast hk
  calc (B.card:ℝ)*(k:ℝ)^10 ≤ W*(2*(k:ℝ)^10)*(k:ℝ)^10 :=
      mul_le_mul_of_nonneg_right agg (by positivity)
    _ = _ := by dsimp [W]; field_simp


theorem main : H1 → H2 → H3 → OMA.R_Erdos694_erdos_694_variants_inf_unique_R1.H1 := by
  classical
  intro supply atypical triple n hn _
  obtain ⟨c,hc,many⟩ := supply n hn
  obtain ⟨C,hC,tr⟩ := triple n hn
  apply Set.infinite_of_forall_exists_gt
  intro b
  let D : ℝ := n.divisors.card
  obtain ⟨k,low,high,rows,cut,big⟩ := (many.and ((atypical (c/3) (by positivity)).and
    (tr.and ((eventually_ge_atTop (max (n+1) (max b 1))).and
      (eventually_ge_atTop ⌈6*D*C/c⌉₊))))).exists
  let X : ℕ := 2^(k^10)
  let A := (Ioc k X).filter (fun p => p.Prime ∧ ∃ s q : ℕ, 0 < s ∧ q.Prime ∧ p=s*q+1 ∧ n*s+1 < q)
  let E := (Ioc k X).filter (fun p => p.Prime ∧ k^8 < (p-1).divisors.card)
  change c*(X:ℝ) ≤ (A.card:ℝ)*(k:ℝ)^10 at low
  change (E.card:ℝ)*(k:ℝ)^10 ≤ c/3*X at high
  have hk : 1 ≤ k := le_trans (le_trans (le_max_right b 1) (le_max_right ..)) cut
  have bk : b ≤ k := le_trans (le_trans (le_max_left b 1) (le_max_right ..)) cut
  have nk : n+1 ≤ k := (le_max_left ..).trans cut
  have lower : 6*D*C/c ≤ (k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast big)
  have mulBound : 6*D*C ≤ c*k := by have := (div_le_iff₀ hc).mp lower; linarith
  have xn : 0 < X := pow_pos (by decide) _
  have xr : (0:ℝ) < X := by exact_mod_cast xn
  by_contra none
  have est := countOverlap n k X hn hk rfl C hC (A \ E) (by
    intro p hp
    obtain ⟨ha,he⟩ := mem_sdiff.mp hp
    obtain ⟨hw,prime,s,q,hs,hq,eq,huge⟩ := mem_filter.mp ha
    obtain ⟨kp,px⟩ := mem_Ioc.mp hw
    have tame : (p-1).divisors.card ≤ k^8 := by
      by_contra! h
      exact he (mem_filter.mpr ⟨hw,prime,h⟩)
    have prod : p-1=s*q := by omega
    have nsle : s ≤ n*s := Nat.le_mul_of_pos_left _ hn
    have sq : s^2 ≤ X := by
      have := Nat.mul_le_mul_left s (show s ≤ q by omega)
      rw [pow_two]; omega
    have ss : s ≤ X := by nlinarith [sq,hs]
    have existsBad : ∃ x : ℕ, x.totient=n*(p-1) ∧ ¬p∣x := by
      by_contra h
      apply none
      refine ⟨p,⟨prime,by omega,fun x hit => ?_⟩,by omega⟩
      by_contra nd
      exact h ⟨x,hit,nd⟩
    obtain ⟨x,phi,absent⟩ := existsBad
    have vp : x.totient=n*s*q := by rw [phi,prod,Nat.mul_assoc]
    have miss : ¬s*q+1∣x := eq ▸ absent
    obtain ⟨a,da,ne,aq⟩ := competitor hn hs hq huge vp miss
    have dsub : s.divisors ⊆ (p-1).divisors :=
      Nat.divisors_subset_of_dvd (by have := prime.two_le; omega) (prod ▸ Nat.dvd_mul_right s q)
    refine ⟨s,mem_Icc.mpr ⟨hs,ss⟩,sq,(card_le_card dsub).trans tame,a,da,ne,q,
      mem_Icc.mpr ⟨hq.pos,(Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; omega)⟩,
      hq,eq ▸ prime,aq,eq⟩) rows
  have small : ((A \ E).card:ℝ)*(k:ℝ)^10 ≤ c/3*X := by
    apply est.trans
    apply (div_le_iff₀ (show (0:ℝ) < k by exact_mod_cast hk)).mpr
    have scaled := mul_le_mul_of_nonneg_right mulBound xr.le
    dsimp [D] at scaled
    linarith only [scaled]
  have combo : A.card ≤ E.card+(A \ E).card := by
    have sub : A ⊆ E ∪ (A \ E) := by intro p hp; by_cases h : p∈E <;> simp [h,hp]
    exact (card_le_card sub).trans (card_union_le _ _)
  have all := mul_le_mul_of_nonneg_right (show (A.card:ℝ) ≤ (E.card:ℝ)+((A \ E).card:ℝ) by
    exact_mod_cast combo) (show (0:ℝ) ≤ (k:ℝ)^10 by positivity)
  nlinarith only [low,high,small,all,mul_pos hc xr]

end OMA.R_Erdos694_erdos_694_variants_inf_unique_R1_H1_R1
