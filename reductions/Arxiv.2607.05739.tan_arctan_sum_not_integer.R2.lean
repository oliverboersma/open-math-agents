import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

/-! An effective exponential barrier and one candidate per fourfold interval.

The product of k²+1 dominates the factorial squared. Its small-prime
valuations have at most two endpoint errors per prime power. An explicit
collection of inert primes divides the factorial but never divides the
product. Elementary primorial bounds therefore force the factor left after
removing any square to be exponentially large at n at least 2^64. This
argument follows Cilleruelo's method for the nonsquare product, with
explicit estimates aimed at a lower bound for every integer quotient.

The complementary arctangent sum locates a possible integer near a multiple
of half-pi. A fourfold interval contains at most one candidate satisfying
the indicated coordinate inequality. This reduces the conjecture to a
bounded-index or bounded-value statement and one candidate per interval
at larger indices. The remaining candidate assertion stays open.

References: Amdeberhan, Medina and Moll (2008);
Cilleruelo, Squares in (1²+1)⋯(n²+1), https://matematicas.uam.es/~franciscojavier.cilleruelo/Papers/squares-sinlogo.pdf;
Ono, Integer values of an arctangent sum are rare, https://arxiv.org/abs/2607.05739.
-/

namespace ArctanCert.Valuations

open Finset

/-- For an odd prime power, any two square roots of minus one agree up to sign. -/
theorem root_eq_or_neg {p j : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hj : 0<j)
    {x y : ZMod (p^j)} (hx : x^2 = -1) (hy : y^2 = -1) : x=y ∨ x= -y := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let _ : NeZero (p^j) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let red := ZMod.castHom (show p ∣ p^j by exact dvd_pow_self _ hj.ne') (ZMod p)
  have liftUnit (z : ZMod (p^j)) (hz : red z ≠ 0) : IsUnit z := by
    rw [← ZMod.natCast_zmod_val z]
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp hj).mpr
    intro he
    apply hz
    rw [← ZMod.natCast_zmod_val z, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr he
  have hx₀ : red x ≠ 0 := by
    intro he
    have h := congrArg red hx
    simp [map_pow, he] at h
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using he)
    have := Nat.le_of_dvd (by decide) hd
    have := hp.two_le
    omega
  have hprod : (x-y)*(x+y)=0 := by linear_combination hx-hy
  by_cases hm : red x = red y
  · have hu : IsUnit (x+y) := by
      apply liftUnit
      rw [map_add, ← hm, ← two_mul]
      exact mul_ne_zero htwo hx₀
    exact Or.inl (sub_eq_zero.mp (hu.mul_left_inj.mp (by simpa using hprod)))
  · have hu : IsUnit (x-y) := liftUnit _ (by simpa using sub_ne_zero.mpr hm)
    exact Or.inr (eq_neg_of_add_eq_zero_left (hu.mul_right_inj.mp (by simpa using hprod)))

private lemma class_count (n q : ℕ) (v : ZMod q) :
    ((Icc 1 n).filter fun k : ℕ => (k : ZMod q)=v).card ≤ n/q+1 := by
  let S := (Icc 1 n).filter fun k : ℕ => (k : ZMod q)=v
  have in_range : Set.MapsTo (fun k : ℕ => k/q) (S : Set ℕ) (range (n/q+1)) := by
    intro k hk
    have hkn := (mem_Icc.mp (mem_filter.mp hk).1).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hkn))
  have inj : (S : Set ℕ).InjOn (fun k : ℕ => k/q) := by
    intro k hk l hl he
    have hke : (k : ZMod q)=v := (mem_filter.mp hk).2
    have hle : (l : ZMod q)=v := (mem_filter.mp hl).2
    have hr := (ZMod.natCast_eq_natCast_iff' k l q).mp (hke.trans hle.symm)
    exact (Nat.div_add_mod k q).symm.trans ((congrArg₂ (fun d r : ℕ => q*d+r) he hr).trans
      (Nat.div_add_mod l q))
  exact (card_le_card_of_injOn _ in_range inj).trans_eq (card_range _)

/-- Each positive prime power dividing k²+1 accounts for at most two
residue classes among k from 1 through n. -/
theorem power_count {p j : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hj : 0<j) (n : ℕ) :
    ((Icc 1 n).filter fun k => p^j ∣ k^2+1).card ≤ 2*(n/p^j+1) := by
  let q := p^j
  let S := (Icc 1 n).filter fun k => q ∣ k^2+1
  change S.card ≤ 2*(n/q+1)
  rcases S.eq_empty_or_nonempty with he | ⟨v,hv⟩
  · simp [he]
  have root {k : ℕ} (hk : k∈S) : (k:ZMod q)^2 = -1 := by
    have hd : q ∣ k^2+1 := (mem_filter.mp hk).2
    have hs := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at hs
    exact eq_neg_of_add_eq_zero_left hs
  let C (z : ZMod q) := (Icc 1 n).filter fun k : ℕ => (k:ZMod q)=z
  have hc : S ⊆ C (v:ZMod q) ∪ C (-(v:ZMod q)) := by
    intro k hk
    have hk' := (mem_filter.mp hk).1
    rcases root_eq_or_neg hp hodd hj (root hk) (root hv) with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hk',h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hk',h⟩)
  calc
    S.card ≤ _ := card_le_card hc
    _ ≤ (C (v:ZMod q)).card + (C (-(v:ZMod q))).card := card_union_le _ _
    _ ≤ (n/q+1)+(n/q+1) := Nat.add_le_add (class_count n q _) (class_count n q _)
    _ = _ := by omega

/-- The local valuation is at most twice the factorial valuation plus
one endpoint contribution for each of two residue classes per power. -/
theorem product_bound (n : ℕ) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*Nat.log p (n^2+1) := by
  let L := Nat.log p (n^2+1)
  let J := Ico 1 (L+1)
  have hn : n ≤ n^2+1 := by nlinarith [Nat.le_mul_self n]
  have hlog : Nat.log p n < L+1 := Nat.lt_succ_of_le (Nat.log_mono_right hn)
  have hk (k : ℕ) (h : k∈Icc 1 n) :
      (k^2+1).factorization p = ∑ j ∈ J, (if p^j ∣ k^2+1 then 1 else 0) := by
    have hle : k^2+1 ≤ n^2+1 := Nat.add_le_add_right (Nat.pow_le_pow_left (mem_Icc.mp h).2 _) _
    have hlt : k^2+1 < p^(L+1) := hle.trans_lt (Nat.lt_pow_of_log_lt hp.one_lt (by dsimp [L]; omega))
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega) hlt]
    simp [J, sum_boole]
  calc
    _ = ∑ k ∈ Icc 1 n, (k^2+1).factorization p := Nat.factorization_prod_apply (fun k _ => Nat.succ_ne_zero (k^2))
    _ = ∑ k ∈ Icc 1 n, ∑ j ∈ J, if p^j ∣ k^2+1 then 1 else 0 := sum_congr rfl hk
    _ = ∑ j ∈ J, ((Icc 1 n).filter fun k => p^j ∣ k^2+1).card := by rw [sum_comm]; simp [sum_boole]
    _ ≤ ∑ j ∈ J, 2*(n/p^j+1) := sum_le_sum fun j hj => power_count hp hodd (mem_Ico.mp hj).1 n
    _ = _ := by
      rw [Nat.factorization_factorial hp hlog]
      simp [J, L, Nat.mul_add, sum_add_distrib, mul_sum]
      exact Nat.mul_comm _ _

end ArctanCert.Valuations

namespace ArctanCert.Valuations

open Finset

private lemma valuation_at_two (k : ℕ) : (k^2+1).factorization 2 = k%2 := by
  by_cases he : k%2=0
  · rw [he]
    apply Nat.factorization_eq_zero_of_not_dvd
    obtain ⟨m,rfl⟩ : ∃ m, k=2*m := ⟨k/2,by omega⟩
    rw [show (2*m)^2+1 = 2*(2*m*m)+1 by ring]
    omega
  · have ho : k%2=1 := by omega
    rw [ho]
    obtain ⟨m,rfl⟩ : ∃ m, k=2*m+1 := ⟨k/2,by omega⟩
    let u := 2*(m*m+m)+1
    have hprod : (2*m+1)^2+1 = 2*u := by dsimp [u]; ring
    have hodd : ¬2∣u := by dsimp [u]; omega
    have hu : u≠0 := by dsimp [u]; omega
    rw [hprod, Nat.factorization_mul (by decide : 2≠0) hu, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, Nat.add_zero]
    exact Nat.prime_two.factorization_self

/-- Exactly the odd indices contribute to the valuation at two, once each. -/
theorem product_two (n : ℕ) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization 2 = (n+1)/2 := by
  rw [Nat.factorization_prod_apply (fun k _ => Nat.succ_ne_zero (k^2))]
  simp_rw [valuation_at_two]
  induction n with
  | zero => decide
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1≤n+1), ih]
    omega

/-- Beyond the first index the dyadic valuation already lies below twice
the factorial valuation, without a logarithmic allowance. -/
theorem product_two_le {n : ℕ} (hn : 2≤n) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization 2 ≤ 2*n.factorial.factorization 2 := by
  rw [product_two]
  let L := Nat.log 2 n+2
  have hb : Nat.log 2 n<L := by dsimp [L]; omega
  have hm : 1∈Ico 1 L := mem_Ico.mpr ⟨le_rfl, by dsimp [L]; omega⟩
  have h₁ := single_le_sum (f:=fun j : ℕ => n/2^j) (fun _ _ => Nat.zero_le _) hm
  rw [pow_one, ← Nat.factorization_factorial Nat.prime_two hb] at h₁
  omega

/-- The same local upper bound holds throughout the prime support. -/
theorem product_bound_all (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (∏ k ∈ Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*Nat.log p (n^2+1) := by
  by_cases h : p=2
  · subst p
    by_cases hn : 2≤n
    · exact (product_two_le hn).trans (Nat.le_add_right _ _)
    · rw [product_two]
      interval_cases n <;> norm_num [Nat.log]
  · exact product_bound n hp h

end ArctanCert.Valuations

namespace ArctanGlobal

open Arxiv.«2607.05739»

/-- The natural product is the squared norm of the original Gaussian integer. -/
lemma product_norm (n : ℕ) : (∏ k ∈ Finset.Icc 1 n, (k^2+1)) = (A n).natAbs^2+(B n).natAbs^2 := by
  have eqn : ((∏ k ∈ Finset.Icc 1 n, (k^2+1) : ℕ):ℤ) = (gaussProd n).norm := by
    let φ : GaussianInt →* ℤ := Zsqrtd.normMonoidHom
    change _ = φ (gaussProd n)
    rw [gaussProd,map_prod,Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    change ((k^2+1:ℕ):ℤ) = 1*1-(-1)*(k:ℤ)*k
    push_cast
    ring
  calc
    _ = (gaussProd n).norm.natAbs := congrArg Int.natAbs eqn
    _ = _ := by simpa only [A,B,pow_two] using GaussianInt.natAbs_norm_eq (gaussProd n)

lemma product_norm_int (n : ℕ) : ((∏ k ∈ Finset.Icc 1 n, (k^2+1) : ℕ):ℤ) = A n^2+B n^2 := by
  simp only [product_norm,Nat.cast_add,Nat.cast_pow,Int.natCast_natAbs,sq_abs]

lemma factorial_sq_le_product (n : ℕ) : n.factorial^2 ≤ ∏ k ∈ Finset.Icc 1 n, (k^2+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.factorial_succ,mul_pow,mul_comm ((n+1)^2),Finset.prod_Icc_succ_top (by omega : 1 ≤ n+1)]
    exact Nat.mul_le_mul ih (Nat.le_succ _)

private lemma root_of_divisor {p j : ℕ} (h : p ∣ j^2+1) : (j:ZMod p)^2 = -1 := by
  have hz : (j:ZMod p)^2+1=0 := by
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using (ZMod.natCast_eq_zero_iff (j^2+1) p).mpr h
  exact eq_neg_of_add_eq_zero_left hz

/-- Inert primes divide none of the norm factors. -/
lemma inert_order_zero (n : ℕ) {p : ℕ} (hp : p.Prime) (hmod : p%4=3) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p=0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  apply Nat.factorization_eq_zero_of_not_dvd
  apply hp.prime.not_dvd_finsetProd
  intro k _ hk
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (root_of_divisor hk) hmod

/-- For `p>2n` at most one entry is a square root of minus one modulo `p`.
That entry has positive norm smaller than `p²`. -/
lemma large_order_le_one (n : ℕ) {p : ℕ} (hp : p.Prime) (hbig : 2*n<p) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤ 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_prod_apply (fun k _ => by positivity)]
  by_cases hit : ∃ k ∈ Finset.Icc 1 n, p ∣ k^2+1
  · obtain ⟨k,hk,hpk⟩ := hit
    obtain ⟨hk₁,hkn⟩ := Finset.mem_Icc.mp hk
    have unique (j : ℕ) (hj : j ∈ Finset.Icc 1 n) (hpj : p ∣ j^2+1) : j=k := by
      obtain ⟨hj₁,hjn⟩ := Finset.mem_Icc.mp hj
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((root_of_divisor hpj).trans (root_of_divisor hpk).symm) with eq|neg
      · simpa only [ZMod.val_natCast_of_lt (by omega : j<p),ZMod.val_natCast_of_lt (by omega : k<p)]
          using congrArg ZMod.val eq
      · have hz : ((j+k:ℕ):ZMod p)=0 := by rw [Nat.cast_add,neg,neg_add_cancel]
        exact False.elim ((Nat.not_dvd_of_pos_of_lt (by omega : 0<j+k) (by omega : j+k<p))
          ((ZMod.natCast_eq_zero_iff (j+k) p).mp hz))
    rw [Finset.sum_eq_single k]
    · have hlt : k^2+1 < p^2 := by
        have h := Nat.pow_le_pow_left (by omega : k+1 ≤ p) 2
        nlinarith only [h,hk₁]
      by_contra! hv
      exact Nat.not_dvd_of_pos_of_lt (by positivity) hlt
        ((hp.pow_dvd_iff_le_factorization (by positivity : k^2+1 ≠ 0)).mpr (by omega : 2≤(k^2+1).factorization p))
    · intro j hj hne
      exact Nat.factorization_eq_zero_of_not_dvd fun hpj => hne (unique j hj hpj)
    · exact fun h => (h hk).elim
  · have h : (∑ k ∈ Finset.Icc 1 n, (k^2+1).factorization p)=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact Nat.factorization_eq_zero_of_not_dvd fun h => hit ⟨k,hk,h⟩
    rw [h]
    decide

lemma large_square_not_dvd (n : ℕ) {p : ℕ} (hp : p.Prime) (hbig : 2*n<p) :
    ¬p^2 ∣ (∏ k ∈ Finset.Icc 1 n, (k^2+1)) := by
  intro h
  have hpos : 0 < ∏ k ∈ Finset.Icc 1 n, (k^2+1) := Finset.prod_pos fun _ _ => by positivity
  have htwo := (hp.pow_dvd_iff_le_factorization hpos.ne').mp h
  have hone := large_order_le_one n hp hbig
  omega

/-- A large prime occurring in the product must divide the remaining factor after any square is removed. -/
lemma large_prime_square_factor {n p b W : ℕ} (hp : p.Prime) (hbig : 2*n<p)
    (hdiv : p ∣ (∏ k ∈ Finset.Icc 1 n, (k^2+1))) (hPW : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2*W) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p=1 ∧ p ∣ W := by
  let P := ∏ k ∈ Finset.Icc 1 n, (k^2+1)
  have hpos : 0<P := Finset.prod_pos fun _ _ => by positivity
  refine ⟨le_antisymm (large_order_le_one n hp hbig) ((hp.dvd_iff_one_le_factorization hpos.ne').mp hdiv),?_⟩
  have hn : ¬ p ∣ b^2 := by
    intro hh
    apply large_square_not_dvd n hp hbig
    rw [hPW]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hh) 2) _
  exact (hp.dvd_mul.mp (hPW ▸ hdiv)).resolve_left hn

/-- For an integer quotient, the large prime divides its norm `1+|m|²`. -/
lemma large_prime_quotient {n p : ℕ} {m : ℤ} (hp : p.Prime) (hbig : 2*n<p)
    (hdiv : p ∣ (∏ k ∈ Finset.Icc 1 n, (k^2+1))) (hm : B n=A n*m) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p=1 ∧ p ∣ 1+m.natAbs^2 := by
  apply large_prime_square_factor (b:=(A n).natAbs) hp hbig hdiv
  rw [product_norm,hm,Int.natAbs_mul]
  ring

/-- A square factorization of the product and the small-prime estimates give both divisibility
and a lower bound on the remaining factor, using any inert divisor of the factorial. -/
lemma aggregate_square_bound {n I E b W : ℕ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hW : 0<W) (hPW : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2*W) :
    ((∏ k ∈ Finset.Icc 1 n, (k^2+1))*I^2 ∣ n.factorial^2*E^2*W) ∧ I^2 ≤ E^2*W := by
  let P := ∏ k ∈ Finset.Icc 1 n, (k^2+1)
  have hF : 0<n.factorial := lt_of_lt_of_le (by omega : 0<n) (Nat.self_le_factorial n)
  have hP : 0<P := Finset.prod_pos fun _ _ => by positivity
  have mul_val (x y : ℕ) (hx : 0<x) (hy : 0<y) (p : ℕ) :
      (x*y).factorization p = x.factorization p+y.factorization p := by rw [Nat.factorization_mul hx.ne' hy.ne']; rfl
  have sq_val (x p : ℕ) : (x^2).factorization p = 2*x.factorization p := by
    simp [Nat.factorization_pow,Finsupp.smul_apply]
  have divides : P*I^2 ∣ n.factorial^2*E^2*W := by
    apply (Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)).mp
    intro p hp
    rw [mul_val _ _ hP (by positivity),mul_val _ _ (by positivity) hW,
      mul_val _ _ (by positivity : 0<n.factorial^2) (by positivity : 0<E^2)]
    simp only [sq_val]
    by_cases pi : p ∣ I
    · have hz : P.factorization p=0 := inert_order_zero n hp (hIsupp p hp pi)
      have hle := (Nat.factorization_prime_le_iff_dvd hI.ne' hF.ne').mpr hIfact p hp
      omega
    · have hiz := Nat.factorization_eq_zero_of_not_dvd pi
      by_cases small : p≤2*n
      · have h := hsmall p hp small
        change P.factorization p ≤ _ at h
        omega
      · by_cases hit : p ∣ P
        · obtain ⟨hv,hq⟩ := large_prime_square_factor hp (by omega : 2*n<p) hit hPW
          change P.factorization p=1 at hv
          have hqv := (hp.dvd_iff_one_le_factorization hW.ne').mp hq
          omega
        · have hz := Nat.factorization_eq_zero_of_not_dvd hit
          omega
  refine ⟨divides,?_⟩
  apply Nat.le_of_mul_le_mul_left (c:=n.factorial^2) _ (by positivity)
  have hl := (Nat.mul_le_mul_right (I^2) (factorial_sq_le_product n)).trans (Nat.le_of_dvd (by positivity) divides)
  simpa only [Nat.mul_assoc] using hl

/-- An integral tangent quotient gives the square factor `|A n|²`. -/
lemma aggregate_bound {n I E : ℕ} {m : ℤ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hm : B n=A n*m) :
    ((∏ k ∈ Finset.Icc 1 n, (k^2+1))*I^2 ∣ n.factorial^2*E^2*(1+m.natAbs^2)) ∧
      I^2 ≤ E^2*(1+m.natAbs^2) := by
  apply aggregate_square_bound (b:=(A n).natAbs) hn hI hE hIfact hIsupp hsmall (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

/-- The reciprocal integral quotient gives the square factor `|B n|²`. -/
lemma aggregate_reciprocal_bound {n I E : ℕ} {m : ℤ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hm : A n=B n*m) :
    ((∏ k ∈ Finset.Icc 1 n, (k^2+1))*I^2 ∣ n.factorial^2*E^2*(1+m.natAbs^2)) ∧
      I^2 ≤ E^2*(1+m.natAbs^2) := by
  apply aggregate_square_bound (b:=(B n).natAbs) hn hI hE hIfact hIsupp hsmall (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

/-- If the product is a square, the inert divisor cannot exceed the small-prime allowance. -/
lemma square_forces_le {n I E b : ℕ} (hn : 1≤n) (hI : 0<I) (hE : 0<E)
    (hIfact : I ∣ n.factorial) (hIsupp : ∀ p : ℕ, p.Prime → p ∣ I → p%4=3)
    (hsmall : ∀ p : ℕ, p.Prime → p≤2*n → (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
      2*n.factorial.factorization p + 2*E.factorization p)
    (hP : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2) : I ≤ E := by
  have h := (aggregate_square_bound (b:=b) (W:=1) hn hI hE hIfact hIsupp hsmall (by decide)
    (by simpa only [mul_one] using hP)).2
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by simpa only [mul_one] using h)

end ArctanGlobal

namespace ArctanInertLemmas

/-- A kernel-computed prime weight for the explicit finite set. -/
lemma weight_exact :
    (∑ p ∈ (Finset.range 50001).filter (fun q : ℕ => q.Prime ∧ q%4=3),p.log2*(1048576/p))=6591956 := by
  let wheel : ℕ := 249873185435436430377698987059663362395086628984728391823112288166942630559511819124255704981537449930570629002821280463185334406128048989132838398791636205678208673855202473444935869602342296488442348182529563060454306401874514103425982529680729837954985416328663177512069858595443931833472658803081894351725778122546461871134622081830651613340173985723024483556319497604300800000000000000000000000000000000000000000000000000000
  have wheel_factorial : wheel=Nat.factorial 223 := by decide +kernel

  let primeCheck (p : ℕ) : Bool :=
    if p≤223 then decide p.Prime else p.gcd wheel == 1

  have primeCheck_iff {p : ℕ} (hp : p≤50000) : primeCheck p=true ↔ p.Prime := by
    unfold primeCheck
    split
    · simp
    · rename_i hbig
      rw [beq_iff_eq,wheel_factorial,← Nat.coprime_iff_gcd_eq_one]
      constructor
      · intro hc
        apply Nat.prime_def_le_sqrt.mpr
        refine ⟨by omega,?_⟩
        intro d h₂ hs hd
        have hs' := Nat.sqrt_le_sqrt hp
        have h224 : Nat.sqrt 50000 < 224 := Nat.sqrt_lt.mpr (by decide)
        have h223 : d≤223 := by omega
        have hdiv := Nat.dvd_gcd hd (Nat.dvd_factorial (by omega : 0<d) h223)
        rw [hc.gcd_eq_one] at hdiv
        have := Nat.le_of_dvd (by decide : 0<1) hdiv
        omega
      · intro pp
        exact pp.coprime_factorial_of_lt (by omega)

  let weight (p : ℕ) := p.log2*(1048576/p)
  let score (p : ℕ) := if p%4=3 then
    (if primeCheck p then weight p else 0) else 0

  have score_eq {p : ℕ} (hp : p≤50000) :
      score p = if p.Prime ∧ p%4=3 then weight p else 0 := by
    by_cases hm : p%4=3 <;> simp [score,hm,primeCheck_iff hp]
  let subtotal (lo count : ℕ) := Nat.rec (motive:=fun _ => ℕ) 0 (fun k t => t+score (lo+k)) count
  have subtotal_add (start len : ℕ) :
      (∑ p ∈ Finset.range (start+len),score p) =
        (∑ p ∈ Finset.range start,score p) + subtotal start len := by
    induction len with
    | zero => simp [subtotal]
    | succ k ih =>
      rw [Nat.add_succ,Finset.sum_range_succ,ih]
      exact Nat.add_assoc _ _ _
  have next {n old new : ℕ} (prev : (∑ p ∈ Finset.range n,score p)=old) (len : ℕ)
      (h : old+subtotal n len=new) : (∑ p ∈ Finset.range (n+len),score p)=new := by
    rw [subtotal_add,prev,h]
  have zero : (∑ p ∈ Finset.range 0,score p)=0 := by simp
  have c1000 : (∑ p ∈ Finset.range 1000,score p)=3773075 := next zero 1000 (by decide +kernel)
  have c2000 : (∑ p ∈ Finset.range 2000,score p)=4265756 := next c1000 1000 (by decide +kernel)
  have c3000 : (∑ p ∈ Finset.range 3000,score p)=4558723 := next c2000 1000 (by decide +kernel)
  have c4000 : (∑ p ∈ Finset.range 4000,score p)=4763521 := next c3000 1000 (by decide +kernel)
  have c5000 : (∑ p ∈ Finset.range 5000,score p)=4927188 := next c4000 1000 (by decide +kernel)
  have c6000 : (∑ p ∈ Finset.range 6000,score p)=5064756 := next c5000 1000 (by decide +kernel)
  have c7000 : (∑ p ∈ Finset.range 7000,score p)=5176692 := next c6000 1000 (by decide +kernel)
  have c8000 : (∑ p ∈ Finset.range 8000,score p)=5260512 := next c7000 1000 (by decide +kernel)
  have c9000 : (∑ p ∈ Finset.range 9000,score p)=5346871 := next c8000 1000 (by decide +kernel)
  have c10000 : (∑ p ∈ Finset.range 10000,score p)=5428303 := next c9000 1000 (by decide +kernel)
  have c11000 : (∑ p ∈ Finset.range 11000,score p)=5500791 := next c10000 1000 (by decide +kernel)
  have c12000 : (∑ p ∈ Finset.range 12000,score p)=5565596 := next c11000 1000 (by decide +kernel)
  have c13000 : (∑ p ∈ Finset.range 13000,score p)=5619702 := next c12000 1000 (by decide +kernel)
  have c14000 : (∑ p ∈ Finset.range 14000,score p)=5672911 := next c13000 1000 (by decide +kernel)
  have c15000 : (∑ p ∈ Finset.range 15000,score p)=5723195 := next c14000 1000 (by decide +kernel)
  have c16000 : (∑ p ∈ Finset.range 16000,score p)=5770242 := next c15000 1000 (by decide +kernel)
  have c17000 : (∑ p ∈ Finset.range 17000,score p)=5814086 := next c16000 1000 (by decide +kernel)
  have c18000 : (∑ p ∈ Finset.range 18000,score p)=5858970 := next c17000 1000 (by decide +kernel)
  have c19000 : (∑ p ∈ Finset.range 19000,score p)=5892808 := next c18000 1000 (by decide +kernel)
  have c20000 : (∑ p ∈ Finset.range 20000,score p)=5927836 := next c19000 1000 (by decide +kernel)
  have c21000 : (∑ p ∈ Finset.range 21000,score p)=5964054 := next c20000 1000 (by decide +kernel)
  have c22000 : (∑ p ∈ Finset.range 22000,score p)=5999894 := next c21000 1000 (by decide +kernel)
  have c23000 : (∑ p ∈ Finset.range 23000,score p)=6032948 := next c22000 1000 (by decide +kernel)
  have c24000 : (∑ p ∈ Finset.range 24000,score p)=6063314 := next c23000 1000 (by decide +kernel)
  have c25000 : (∑ p ∈ Finset.range 25000,score p)=6092350 := next c24000 1000 (by decide +kernel)
  have c26000 : (∑ p ∈ Finset.range 26000,score p)=6119006 := next c25000 1000 (by decide +kernel)
  have c27000 : (∑ p ∈ Finset.range 27000,score p)=6143604 := next c26000 1000 (by decide +kernel)
  have c28000 : (∑ p ∈ Finset.range 28000,score p)=6170414 := next c27000 1000 (by decide +kernel)
  have c29000 : (∑ p ∈ Finset.range 29000,score p)=6196860 := next c28000 1000 (by decide +kernel)
  have c30000 : (∑ p ∈ Finset.range 30000,score p)=6220926 := next c29000 1000 (by decide +kernel)
  have c31000 : (∑ p ∈ Finset.range 31000,score p)=6241296 := next c30000 1000 (by decide +kernel)
  have c32000 : (∑ p ∈ Finset.range 32000,score p)=6264284 := next c31000 1000 (by decide +kernel)
  have c33000 : (∑ p ∈ Finset.range 33000,score p)=6288266 := next c32000 1000 (by decide +kernel)
  have c34000 : (∑ p ∈ Finset.range 34000,score p)=6310466 := next c33000 1000 (by decide +kernel)
  have c35000 : (∑ p ∈ Finset.range 35000,score p)=6333401 := next c34000 1000 (by decide +kernel)
  have c36000 : (∑ p ∈ Finset.range 36000,score p)=6354716 := next c35000 1000 (by decide +kernel)
  have c37000 : (∑ p ∈ Finset.range 37000,score p)=6374981 := next c36000 1000 (by decide +kernel)
  have c38000 : (∑ p ∈ Finset.range 38000,score p)=6393866 := next c37000 1000 (by decide +kernel)
  have c39000 : (∑ p ∈ Finset.range 39000,score p)=6411161 := next c38000 1000 (by decide +kernel)
  have c40000 : (∑ p ∈ Finset.range 40000,score p)=6431831 := next c39000 1000 (by decide +kernel)
  have c41000 : (∑ p ∈ Finset.range 41000,score p)=6449636 := next c40000 1000 (by decide +kernel)
  have c42000 : (∑ p ∈ Finset.range 42000,score p)=6468326 := next c41000 1000 (by decide +kernel)
  have c43000 : (∑ p ∈ Finset.range 43000,score p)=6485966 := next c42000 1000 (by decide +kernel)
  have c44000 : (∑ p ∈ Finset.range 44000,score p)=6500546 := next c43000 1000 (by decide +kernel)
  have c45000 : (∑ p ∈ Finset.range 45000,score p)=6517796 := next c44000 1000 (by decide +kernel)
  have c46000 : (∑ p ∈ Finset.range 46000,score p)=6530981 := next c45000 1000 (by decide +kernel)
  have c47000 : (∑ p ∈ Finset.range 47000,score p)=6546821 := next c46000 1000 (by decide +kernel)
  have c48000 : (∑ p ∈ Finset.range 48000,score p)=6561461 := next c47000 1000 (by decide +kernel)
  have c49000 : (∑ p ∈ Finset.range 49000,score p)=6575636 := next c48000 1000 (by decide +kernel)
  have c50000 : (∑ p ∈ Finset.range 50000,score p)=6591956 := next c49000 1000 (by decide +kernel)
  have c50001 : (∑ p ∈ Finset.range 50001,score p)=6591956 := next c50000 1 (by decide +kernel)
  rw [Finset.sum_filter]
  apply Eq.trans _ c50001
  apply Finset.sum_congr rfl
  intro p hp
  exact (score_eq (by have := Finset.mem_range.mp hp; omega)).symm

/-- The explicit inert part of n! has only prime divisors congruent to three modulo
four and is large on the entire indicated tail. -/
lemma inert_factorial (n : ℕ) (hn : 2^64≤n) :
    let J := (Finset.range 50001).filter (fun p : ℕ => p.Prime ∧ p%4=3)
    let I := ∏ p ∈ J, p^((n/1048576)*(1048576/p))
    0<I ∧ I∣n.factorial ∧
      (∀ p : ℕ, p.Prime → p∣I → p≤50000 ∧ p%4=3) ∧
      2^((n/1048576)*6590000)≤I ∧ 25*n≤4*((n/1048576)*6590000) ∧ 2^(25*n/4)≤I := by
  let J : Finset ℕ := (Finset.range 50001).filter (fun p : ℕ => p.Prime ∧ p%4=3)

  have mem_J {p : ℕ} : p∈J ↔ p≤50000 ∧ p.Prime ∧ p%4=3 := by
    change p ∈ (Finset.range (50000+1)).filter (fun q : ℕ => q.Prime ∧ q%4=3) ↔ _
    rw [Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

  let exponent (n p : ℕ) := (n/1048576)*(1048576/p)
  let I (n : ℕ) := ∏ p ∈ J,p^(exponent n p)

  have I_pos (n : ℕ) : 0<I n :=
    Finset.prod_pos fun _ hp => pow_pos (mem_J.mp hp).2.1.pos _

  have factorization_I (n p : ℕ) :
      (I n).factorization p = if p∈J then exponent n p else 0 := by
    dsimp only [I]
    rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (mem_J.mp hq).2.1.ne_zero)]
    calc
      _ = ∑ q ∈ J, if p=q then exponent n q else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(mem_J.mp hq).2.1.factorization_pow]
        simp [Finsupp.single_apply,eq_comm]
      _ = _ := Finset.sum_ite_eq _ _ _

  have I_dvd_factorial (n : ℕ) : I n ∣ n.factorial := by
    apply (Nat.factorization_le_iff_dvd (I_pos n).ne' n.factorial_ne_zero).mp
    intro p
    rw [factorization_I]
    split
    · rename_i hp
      have prime := (mem_J.mp hp).2.1
      have div : exponent n p ≤ n/p := by
        apply (Nat.le_div_iff_mul_le prime.pos).mpr
        calc
          exponent n p*p = (n/1048576)*((1048576/p)*p) := by unfold exponent; ring
          _ ≤ (n/1048576)*1048576 := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
          _ ≤ n := Nat.div_mul_le_self _ _
      apply div.trans
      rw [Nat.factorization_factorial prime (show Nat.log p n<Nat.log p n+2 by omega)]
      have h₁ : 1 ∈ Finset.Ico 1 (Nat.log p n+2) := Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩
      simpa only [pow_one] using
        (Finset.single_le_sum (f:=fun i => n/p^i) (fun _ _ => Nat.zero_le _) h₁)
    · exact Nat.zero_le _

  have prime_dvd_I {n p : ℕ} (hp : p.Prime) (hd : p ∣ I n) : p∈J := by
    by_contra hn
    have h := hp.factorization_pos_of_dvd (I_pos n).ne' hd
    rw [factorization_I,if_neg hn] at h
    exact (Nat.lt_irrefl 0) h
  have finite_weight : (∑ p ∈ J,p.log2*(1048576/p))=6591956 := weight_exact
  have block_lower (n : ℕ) : 2^((n/1048576)*6590000) ≤ I n := by
    calc
      _ ≤ 2^((n/1048576)*6591956) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by decide))
      _ = ∏ p ∈ J,(2^p.log2)^(exponent n p) := by
        rw [← finite_weight,Finset.mul_sum,← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro p _
        rw [← pow_mul]
        apply congrArg (fun e : ℕ => 2^e)
        dsimp only [exponent]
        ring
      _ ≤ I n := by
        apply Finset.prod_le_prod'
        intro p hp
        apply Nat.pow_le_pow_left
        exact (Nat.le_log2 (mem_J.mp hp).2.1.ne_zero).mp le_rfl

  have exponent_bound {n : ℕ} (hn : 2^64≤n) : 25*n ≤ 4*((n/1048576)*6590000) := by
    norm_num at hn
    omega

  have dyadic_lower {n : ℕ} (hn : 2^64≤n) : 2^(25*n/4) ≤ I n := by
    apply le_trans _ (block_lower n)
    apply Nat.pow_le_pow_right (by decide)
    have h := exponent_bound hn
    omega
  refine ⟨I_pos n,I_dvd_factorial n,?_,block_lower n,exponent_bound hn,dyadic_lower hn⟩
  intro p hp hd
  obtain ⟨hlo,_,hmod⟩ := mem_J.mp (prime_dvd_I hp hd)
  exact ⟨hlo,hmod⟩

end ArctanInertLemmas

namespace ArctanGlobal

/-- Beyond the 64-bit boundary, the logarithmic contribution from primes up to the
square root fits into a small fraction of the linear exponent. -/
lemma sqrt_log_budget {n : ℕ} (hn : 2^64 ≤ n) : 256*n.sqrt*(2*n.log2+3) ≤ n := by
  have hn0 : n ≠ 0 := by omega
  have hlog : 64 ≤ n.log2 := (Nat.le_log2 hn0).mpr hn
  have dyadic (k : ℕ) (hk : 64 ≤ k) : (256*(2*k+3))^2 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      rw [pow_succ]
      calc
        (256*(2*(k+1)+3))^2 ≤ (256*(2*k+3))^2*2 := by
          nlinarith only [hk,Nat.zero_le (k*k)]
        _ ≤ 2^k*2 := Nat.mul_le_mul_right _ ih
  have pow_le : 2^n.log2 ≤ n := (Nat.le_log2 hn0).mp le_rfl
  have square := (dyadic n.log2 hlog).trans pow_le
  have root : 256*(2*n.log2+3) ≤ n.sqrt :=
    Nat.le_sqrt.mpr (by simpa only [pow_two] using square)
  calc
    256*n.sqrt*(2*n.log2+3) = (256*(2*n.log2+3))*n.sqrt := by ring
    _ ≤ n.sqrt*n.sqrt := Nat.mul_le_mul_right _ root
    _ ≤ n := Nat.sqrt_le _

lemma quadratic_dyadic {n : ℕ} (hn : 2^64 ≤ n) : n^2+1 ≤ 2^(2*n.log2+3) := by
  have h : n < 2^(n.log2+1) := (Nat.log2_lt (by omega : n≠0)).mp (by omega)
  have hh := Nat.mul_lt_mul_of_pos_left h (by omega : 0<n)
  have hsq : n*n < 2^(n.log2+1)*2^(n.log2+1) :=
    hh.trans_le (Nat.mul_le_mul_right _ h.le)
  have expand : 2^(2*n.log2+3) = 2^(n.log2+1)*2^(n.log2+1)*2 := by
    rw [← pow_add]
    rw [← pow_succ]
    congr 1
    omega
  rw [expand,pow_two]
  omega

end ArctanGlobal

namespace ArctanPrimeErrorLemmas

/-- The maximal power is controlled using the three prime cutoffs and one small-prime factor. -/
private lemma prime_weight {n p : ℕ} (hn : 2^64 ≤ n) (hp : p.Prime) :
    p^(Nat.log p (n^2+1)) ≤ p*(if p≤n then p else 1)*(if p≤n/256 then p else 1)*
      (if p≤n.sqrt then n^2+1 else 1) := by
  have hn0 : 0<n := by omega
  have hbase : n^2+1 < (n+1)^2 := by nlinarith
  have pow_le (j : ℕ) (hh : n^2+1 < p^(j+1)) : p^(Nat.log p (n^2+1)) ≤ p^j :=
    Nat.pow_le_pow_right hp.pos (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by positivity) hh))
  by_cases hs : p≤n.sqrt
  · rw [if_pos hs]
    apply (Nat.pow_log_le_self p (by positivity : n^2+1≠0)).trans
    have ht : 1≤p*(if p≤n then p else 1)*(if p≤n/256 then p else 1) := by
      have hpos := hp.pos
      change 0 < p*(if p≤n then p else 1)*(if p≤n/256 then p else 1)
      split <;> split <;> positivity
    simpa only [one_mul] using Nat.mul_le_mul_right (n^2+1) ht
  rw [if_neg hs,mul_one]
  have hs' : n < p^2 := Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hs)
  by_cases hm : p≤n/256
  · have hl : p≤n := hm.trans (Nat.div_le_self _ _)
    rw [if_pos hl,if_pos hm]
    have h4 : n^2+1 < p^4 := by
      calc
        _ < (n+1)^2 := hbase
        _ ≤ (p^2)^2 := Nat.pow_le_pow_left (by omega) _
        _ = _ := by ring
    simpa only [pow_succ,pow_zero,one_mul] using pow_le 3 h4
  rw [if_neg hm,mul_one]
  by_cases hl : p≤n
  · rw [if_pos hl]
    have hpn : n < 256*p := by omega
    have hsize : 65536 ≤ p := by omega
    have h3 : n^2+1 < p^3 := by
      calc
        _ < (n+1)^2 := hbase
        _ ≤ (256*p)^2 := Nat.pow_le_pow_left (by omega) _
        _ ≤ p^3 := by nlinarith only [Nat.mul_le_mul_right (p*p) hsize]
    simpa only [pow_two] using pow_le 2 h3
  · rw [if_neg hl,mul_one]
    have hh : n^2+1 < p^2 := hbase.trans_le (Nat.pow_le_pow_left (by omega) _)
    simpa only [pow_one] using pow_le 1 hh

private lemma product_le_primorial (n : ℕ) (hn : 2^64≤n) :
    (∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime,p^(Nat.log p (n^2+1))) ≤ primorial (2*n)*primorial n*primorial (n/256)*(n^2+1)^n.sqrt := by
  classical
  let P (k : ℕ) := (Finset.Icc 1 k).filter Nat.Prime
  have same (k : ℕ) : P k = (Finset.range (k+1)).filter Nat.Prime := by
    ext p
    simp only [P,Finset.mem_filter,Finset.mem_Icc,Finset.mem_range,Nat.lt_succ_iff]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.one_le,h.1⟩,h.2⟩⟩
  have base (k : ℕ) : (∏ p ∈ P k,p) = primorial k := by rw [same]; rfl
  have cut (k : ℕ) (h : k≤2*n) : (P (2*n)).filter (fun p => p≤k)=P k := by
    ext p
    simp only [P,Finset.mem_filter,Finset.mem_Icc]
    exact ⟨fun f => ⟨⟨f.1.1.1,f.2⟩,f.1.2⟩,fun f => ⟨⟨⟨f.1.1,f.1.2.trans h⟩,f.2⟩,f.1.2⟩⟩
  have piece (k : ℕ) (h : k≤2*n) : (∏ p ∈ P (2*n),if p≤k then p else 1)=primorial k := by
    rw [← Finset.prod_filter,cut k h,base]
  have small : (∏ p ∈ P (2*n), if p≤n.sqrt then n^2+1 else 1) ≤ (n^2+1)^n.sqrt := by
    have hcard : (P n.sqrt).card ≤ n.sqrt := by
      have h := Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.Icc 1 n.sqrt))
      simpa only [P,Nat.card_Icc,Nat.add_sub_cancel] using h
    rw [← Finset.prod_filter,cut n.sqrt (by have := Nat.sqrt_le_self n; omega),Finset.prod_const]
    exact Nat.pow_le_pow_right (by positivity) hcard
  change (∏ p ∈ P (2*n),p^(Nat.log p (n^2+1))) ≤ _
  calc
    _ ≤ ∏ p ∈ P (2*n), p*(if p≤n then p else 1)*(if p≤n/256 then p else 1)*
        (if p≤n.sqrt then n^2+1 else 1) := Finset.prod_le_prod' fun p hp => prime_weight hn (Finset.mem_filter.mp hp).2
    _ ≤ _ := by
      simp only [Finset.prod_mul_distrib,base,piece n (by omega),piece (n/256) (by omega)]
      exact Nat.mul_le_mul_left _ small

/-- Every relevant prime-power cost divides the same positive integer, whose size is
bounded uniformly beyond the unsigned 64-bit range. -/
lemma error_product (n : ℕ) (hn : 2^64 ≤ n) :
    let E := ∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime,p^(Nat.log p (n^2+1))
    0 < E ∧ (∀ p : ℕ, p.Prime → p≤2*n → p^(Nat.log p (n^2+1)) ∣ E) ∧ E ≤ 2^(49*n/8) := by
  let E := ∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime,p^(Nat.log p (n^2+1))
  change 0<E ∧ (∀ p : ℕ, p.Prime → p≤2*n → p^(Nat.log p (n^2+1)) ∣ E) ∧ E≤2^(49*n/8)
  refine ⟨?_,?_,?_⟩
  · exact Finset.prod_pos (fun _ hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
  · intro p hp hle
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le,hle⟩,hp⟩)
  · have hsmall := ArctanGlobal.sqrt_log_budget hn
    have hpow := ArctanGlobal.quadratic_dyadic hn
    let L := 2*n.log2+3
    have he : 256*(L*n.sqrt) ≤ n := by simpa only [L,mul_assoc,mul_comm,mul_left_comm] using hsmall
    calc
      _ ≤ primorial (2*n)*primorial n*primorial (n/256)*(n^2+1)^n.sqrt := product_le_primorial n hn
      _ ≤ 4^(2*n)*4^n*4^(n/256)*(2^L)^n.sqrt := by
        gcongr <;> apply primorial_le_four_pow
      _ = 2^(4*n+2*n+2*(n/256)+L*n.sqrt) := by
        rw [show (4:ℕ)=2^2 by decide]
        simp only [← pow_mul,← pow_add]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

end ArctanPrimeErrorLemmas

namespace ArctanGlobal

open Arxiv.«2607.05739»

/-- Removing any square from the Gaussian norm leaves an exponentially large positive factor. -/
theorem square_factor_large {n b W : ℕ} (hn : 2^64 ≤ n) (hW : 0<W)
    (hP : (∏ k ∈ Finset.Icc 1 n, (k^2+1))=b^2*W) : (2^(n/8))^2 ≤ W := by
  classical
  let J := (Finset.range 50001).filter (fun p : ℕ => p.Prime ∧ p%4=3)
  let I := ∏ p ∈ J, p^((n/1048576)*(1048576/p))
  let E := ∏ p ∈ (Finset.Icc 1 (2*n)).filter Nat.Prime, p^(Nat.log p (n^2+1))
  obtain ⟨hI, hIfact, hIsupp, _, _, lower⟩ := ArctanInertLemmas.inert_factorial n hn
  obtain ⟨hE, powers, upper⟩ := ArctanPrimeErrorLemmas.error_product n hn
  change 0<I at hI
  change 0<E at hE
  change 2^(25*n/4) ≤ I at lower
  change E ≤ 2^(49*n/8) at upper
  have ord (p : ℕ) (hp : p.Prime) (hle : p≤2*n) :
      (∏ k ∈ Finset.Icc 1 n, (k^2+1)).factorization p ≤
        2*n.factorial.factorization p + 2*E.factorization p := by
    have he := (hp.pow_dvd_iff_le_factorization hE.ne').mp (powers p hp hle)
    exact (ArctanCert.Valuations.product_bound_all n hp).trans (by omega)
  have aggregate := (aggregate_square_bound (n:=n) (I:=I) (E:=E) (by omega) hI hE hIfact
    (fun p hp hd => (hIsupp p hp hd).2) ord hW hP).2
  let L : ℕ := 2^(n/8)
  have gain : E*L ≤ I := calc
    E*L ≤ 2^(49*n/8)*L := Nat.mul_le_mul_right _ upper
    _ = 2^(49*n/8+n/8) := (pow_add _ _ _).symm
    _ ≤ 2^(25*n/4) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ I := lower
  have scaled : E^2*L^2 ≤ E^2*W := calc
    _ = (E*L)^2 := (mul_pow E L 2).symm
    _ ≤ I^2 := Nat.pow_le_pow_left gain _
    _ ≤ _ := aggregate
  exact Nat.le_of_mul_le_mul_left scaled (pow_pos hE 2)

private lemma exponential_of_square {n u : ℕ} (hn : 2^64 ≤ n)
    (small : (2^(n/8))^2 ≤ 1+u^2) : 2^(n/8) ≤ u := by
  let L : ℕ := 2^(n/8)
  change L^2 ≤ 1+u^2 at small
  have two : 2 ≤ L := by
    change 2^1 ≤ 2^(n/8)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change L ≤ u
  by_contra! bad
  have sq := Nat.pow_le_pow_left (show u+1≤L by omega) 2
  by_cases zero : u=0
  · rw [zero] at small
    have hh := Nat.pow_le_pow_left two 2
    omega
  · have pos : 0 < u := Nat.pos_of_ne_zero zero
    nlinarith only [small,sq,pos]

/-- A hypothetical integer value past the word-size boundary has exponential magnitude. -/
theorem quotient_exponential {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : B n=A n*m) :
    2^(n/8) ≤ m.natAbs := by
  apply exponential_of_square hn
  apply square_factor_large (b:=(A n).natAbs) hn (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

theorem reciprocal_exponential {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : A n=B n*m) :
    2^(n/8) ≤ m.natAbs := by
  apply exponential_of_square hn
  apply square_factor_large (b:=(B n).natAbs) hn (by positivity)
  rw [product_norm,hm,Int.natAbs_mul]
  ring

theorem norm_not_square_large {n b : ℕ} (hn : 2^64 ≤ n) :
    (∏ k ∈ Finset.Icc 1 n, (k^2+1)) ≠ b^2 := by
  intro hs
  have large := square_factor_large (b:=b) (W:=1) hn (by decide) (by simpa only [mul_one] using hs)
  have two : 2^1 ≤ 2^(n/8) := Nat.pow_le_pow_right (by decide) (by omega)
  have sq := Nat.pow_le_pow_left two 2
  omega

/-- A prescribed integer value permits only finitely many indices; this gives
the explicit search limit above the certified finite range. -/
theorem index_lt_bit_bound {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : B n=A n*m) :
    n < 8*(m.natAbs.log2+1) := by
  have big := quotient_exponential hn hm
  have positive : 0 < m.natAbs := (by positivity : 0 < 2^(n/8)).trans_le big
  have bits := (Nat.le_log2 positive.ne').mpr big
  omega

private lemma eight_mul_le_exp {n : ℕ} (hn : 2^64 ≤ n) : 8*n ≤ 2^(n/8) := by
  have enough (k : ℕ) (hk : 64≤k) : 64*(k+1) ≤ 2^k := by
    induction k,hk using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  exact (show 8*n ≤ 64*(n/8+1) by omega).trans (enough _ (by omega))

theorem quotient_large_linear {n : ℕ} {m : ℤ} (hn : 2^64 ≤ n) (hm : B n=A n*m) :
    8*(n:ℤ) ≤ |m| := by
  have h := (eight_mul_le_exp hn).trans (quotient_exponential hn hm)
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

end ArctanGlobal

namespace ArctanGlobal.WordPrimes

/-- Binary modular powering, reducing after each square and multiply. -/
private lemma pow_bits (p a n : ℕ) :
    ((n.bits.foldr (fun b v => (if b then v*v*a else v*v)%p) 1 : ℕ) : ZMod p) = (a : ZMod p)^n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb,List.foldr_cons,ZMod.natCast_mod]
    cases b <;> simp [Nat.bit_val,Nat.cast_mul,ih,two_mul,pow_add]

/-- Lucas's criterion with the factors of the square root of `p-1` supplied explicitly. -/
private lemma from_witness (p k a : ℕ) (factors : List ℕ) (hs : p-1=k^2) (hf : factors.prod=k)
    (hp : ∀ q ∈ factors, q.Prime)
    (hc : let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
      v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true) : p.Prime := by
  let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
  change v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true at hc
  have hpow (n : ℕ) : (v n : ZMod p)=(a : ZMod p)^n := pow_bits p a n
  apply lucas_primality p (a : ZMod p)
  · rw [← hpow,hc.1,Nat.cast_one]
  · intro q hq hd
    have hmem : q ∈ factors := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
      (fun b hb => Nat.prime_iff.mp (hp b hb)) (hf ▸ hq.dvd_of_dvd_pow (hs ▸ hd))
    have hv := of_decide_eq_true (List.all_eq_true.mp hc.2 q hmem)
    rwa [hpow] at hv

lemma bridge : Nat.Prime 2005057 := by
  apply from_witness 2005057 1416 5 [2, 2, 2, 3, 59]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma million : Nat.Prime 999920001601 := by
  apply from_witness 999920001601 999960 17 [2, 2, 2, 3, 5, 13, 641]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma word : Nat.Prime 63999977760001932101 := by
  apply from_witness 63999977760001932101 7999998610 2 [2, 5, 53, 193, 197, 397]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

end ArctanGlobal.WordPrimes

namespace ArctanGlobal

/-- A factor k²+1 divisible by a prime exceeding twice the upper endpoint
gives that prime valuation exactly one throughout the product. -/
theorem norm_simple_prime {n k p : ℕ} (hk : k ∈ Finset.Icc 1 n) (hp : p.Prime)
    (hbig : 2*n<p) (hkdiv : p ∣ k^2+1) :
    (∏ i ∈ Finset.Icc 1 n, (i^2+1)).factorization p = 1 ∧
      ¬IsSquare (∏ i ∈ Finset.Icc 1 n, (i^2+1)) := by
  let P := ∏ i ∈ Finset.Icc 1 n, (i^2+1)
  have hpos : 0<P := Finset.prod_pos fun i _ => Nat.succ_pos (i^2)
  have hd : p∣P := hkdiv.trans (Finset.dvd_prod_of_mem (fun i => i^2+1) hk)
  have h₁ : P.factorization p=1 :=
    le_antisymm (large_order_le_one n hp hbig) ((hp.dvd_iff_one_le_factorization hpos.ne').mp hd)
  refine ⟨h₁,?_⟩
  rintro ⟨b,hb⟩
  change P=b*b at hb
  have hbn : b≠0 := by rintro rfl; simp [hb] at hpos
  rw [hb, Nat.factorization_mul hbn hbn, Finsupp.add_apply] at h₁
  omega

/-- A short chain of overlapping ranges supplies a prime factor k²+1
larger than 2n for every index below 2⁶⁴ starting at four. -/
theorem word_large_prime {n : ℕ} (lo : 4≤n) (hi : n<2^64) :
    ∃ k ∈ Finset.Icc 1 n, (k^2+1).Prime ∧ 2*n<k^2+1 := by
  by_cases h₆ : n<6
  · exact ⟨4, Finset.mem_Icc.mpr ⟨by decide,lo⟩, by decide, by omega⟩
  by_cases h₁₀ : n<10
  · exact ⟨6, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by decide, by omega⟩
  by_cases h₃₆ : n<36
  · exact ⟨10, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by decide, by omega⟩
  by_cases h₂₅₆ : n<256
  · exact ⟨36, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by norm_num, by omega⟩
  by_cases hbridge : n<1416
  · exact ⟨256, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, by norm_num, by omega⟩
  by_cases hmillion : n<999960
  · exact ⟨1416, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, WordPrimes.bridge, by omega⟩
  by_cases hword : n<7999998610
  · exact ⟨999960, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, WordPrimes.million, by omega⟩
  exact ⟨7999998610, Finset.mem_Icc.mpr ⟨by decide,by omega⟩, WordPrimes.word, by omega⟩

theorem norm_not_square_word {n : ℕ} (lo : 4≤n) (hi : n<2^64) :
    ¬IsSquare (∏ k ∈ Finset.Icc 1 n, (k^2+1)) := by
  obtain ⟨k,hk,hp,hbig⟩ := word_large_prime lo hi
  exact (norm_simple_prime hk hp hbig dvd_rfl).2

end ArctanGlobal

/- The scaled-coordinate proof was contributed by HudZah in Left to Solve PR #327.
   https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/327 -/
namespace ArctanTrigBridge
open Arxiv.«2607.05739» Finset

-- The cosine and sine are the two integer coordinates times the same positive factor.
lemma scaled_coordinates (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      Real.cos (∑ k ∈ Icc 1 n, Real.arctan k) = c * (A n : ℝ) ∧
      Real.sin (∑ k ∈ Icc 1 n, Real.arctan k) = c * (B n : ℝ) := by
  induction n with
  | zero =>
    exact ⟨1, zero_lt_one, by norm_num [A, gaussProd], by norm_num [B, gaussProd]⟩
  | succ n ih =>
    obtain ⟨c, hc, hcos, hsin⟩ := ih
    let t : ℝ := (n + 1 : ℕ)
    have ht := Real.cos_arctan_pos t
    have hs : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
      apply (div_eq_iff ht.ne').mp
      rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
    have hp : gaussProd (n + 1) = gaussProd n * (⟨1, (n + 1 : ℕ)⟩ : GaussianInt) := by
      unfold gaussProd
      rw [prod_Icc_succ_top (by omega)]
    have ha : (A (n + 1) : ℝ) = A n - t * B n := by
      simp [A, B, hp, t, sub_eq_add_neg]
      ring
    have hb : (B (n + 1) : ℝ) = t * A n + B n := by
      simp [A, B, hp, t]
      ring
    refine ⟨c * Real.cos (Real.arctan t), mul_pos hc ht, ?_, ?_⟩
    · rw [sum_Icc_succ_top (by omega), Real.cos_add, hcos, hsin, ha]
      change _ - _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring
    · rw [sum_Icc_succ_top (by omega), Real.sin_add, hcos, hsin, hb]
      change _ + _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring

end ArctanTrigBridge

namespace ArctanGlobalSpacing

open Arxiv.«2607.05739» Finset

private lemma arctan_upper {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr ht) (Real.arctan_lt_pi_div_two t)

private lemma arctan_abs (t : ℝ) : |Real.arctan t| ≤ |t| := by
  rcases le_or_gt 0 t with h | h
  · simpa [abs_of_nonneg h, abs_of_nonneg (Real.arctan_nonneg.mpr h)] using arctan_upper h
  · simpa [abs_of_nonpos h.le, abs_of_nonpos (Real.arctan_le_zero.mpr h.le)] using
      arctan_upper (neg_nonneg.mpr h.le)

private lemma arctan_lower {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) : t/2 ≤ Real.arctan t := by
  have hs : 0 < Real.sqrt (1+t^2) := by positivity
  have hb : Real.sqrt (1+t^2) ≤ 2 := Real.sqrt_le_iff.mpr
    ⟨by norm_num, by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]⟩
  calc
    t/2 ≤ t/Real.sqrt (1+t^2) := div_le_div_of_nonneg_left h₀ hs hb
    _ = Real.sin (Real.arctan t) := (Real.sin_arctan t).symm
    _ ≤ Real.arctan t := Real.sin_le (Real.arctan_nonneg.mpr h₀)

private lemma complementary_angles (n : ℕ) :
    (∑ j ∈ Icc 1 n, Real.arctan j) + angleSum n = (n:ℝ)*(Real.pi/2) := by
  unfold angleSum
  rw [← sum_add_distrib]
  calc
    _ = ∑ _j ∈ Icc 1 n, Real.pi/2 := by
      apply sum_congr rfl
      intro j hj
      have hp : 0 < (j:ℝ) := by exact_mod_cast (mem_Icc.mp hj).1
      rw [one_div,Real.arctan_inv_of_pos hp]
      ring
    _ = _ := by simp [Nat.card_Icc,nsmul_eq_mul]

/-- The complementary angle sum lies within the reciprocal of the absolute
slope of an integral multiple of a half-period. -/
lemma angle_near_grid {n : ℕ} {m : ℤ} (hm : B n = A n*m) (hm₀ : m ≠ 0) :
    ∃ j : ℤ, |angleSum n - (j:ℝ)*(Real.pi/2)| ≤ 1/|(m:ℝ)| := by
  let θ := ∑ k ∈ Icc 1 n, Real.arctan k
  let ε := Real.arctan (1/(m:ℝ))
  obtain ⟨c,_hc,hcos,hsin⟩ := ArctanTrigBridge.scaled_coordinates n
  have hε : Real.sin ε = (1/(m:ℝ)) * Real.cos ε := by
    apply (div_eq_iff (Real.cos_arctan_pos _).ne').mp
    exact (Real.tan_eq_sin_div_cos _).symm.trans (Real.tan_arctan _)
  have zm : (m:ℝ) ≠ 0 := by exact_mod_cast hm₀
  have hzero : Real.cos (θ+ε) = 0 := by
    rw [Real.cos_add,hε]
    dsimp only [θ]
    rw [hcos,hsin,hm,Int.cast_mul]
    field_simp
    ring
  obtain ⟨j,hj⟩ := Real.cos_eq_zero_iff.mp hzero
  refine ⟨(n:ℤ)-(2*j+1),?_⟩
  have hs := complementary_angles n
  change θ+angleSum n = _ at hs
  have he : angleSum n - (((n:ℤ)-(2*j+1):ℤ):ℝ)*(Real.pi/2) = ε := by
    push_cast
    linarith only [hs,hj]
  rw [he]
  simpa only [ε,abs_div,abs_one] using arctan_abs (1/(m:ℝ))

private lemma angle_succ (n : ℕ) :
    angleSum (n+1) = angleSum n + Real.arctan (1/((n:ℝ)+1)) := by
  unfold angleSum
  rw [sum_Icc_succ_top (by omega),Nat.cast_succ]

private lemma angle_mono : Monotone angleSum :=
  monotone_nat_of_le_succ fun j => by
    rw [angle_succ]
    exact le_add_of_nonneg_right (Real.arctan_nonneg.mpr (by positivity))

private lemma angle_advance_lower {n k : ℕ} (hnk : n < k) :
    (1/((n:ℝ)+1))/2 ≤ angleSum k - angleSum n := by
  have hh := angle_mono (show n+1 ≤ k from hnk)
  rw [angle_succ] at hh
  have hb : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  linarith only [hh, arctan_lower (by positivity : 0 ≤ 1/((n:ℝ)+1)) hb]

private lemma angle_advance_upper {n k : ℕ} (hn : 0 < n) (hk : n ≤ k) :
    angleSum k - angleSum n ≤ Real.log (k:ℝ) - Real.log (n:ℝ) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hp : 0 < (k:ℝ) := by exact_mod_cast hn.trans_le hk
    have hp' : 0 < (k:ℝ)+1 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hp hp')
    rw [Real.log_div hp.ne' hp'.ne'] at hlog
    have he : (k:ℝ)/((k:ℝ)+1) - 1 = -1/((k:ℝ)+1) := by field_simp; ring
    rw [he,neg_div] at hlog
    rw [angle_succ,Nat.cast_succ]
    linarith only [ih,hlog,arctan_upper (by positivity : 0 ≤ 1/((k:ℝ)+1))]

/-- Two integral values, each at least eight times its index in absolute
value, force an index gap of more than a factor of four. -/
theorem spacing_of_slopes {n k : ℕ} {m u : ℤ} (nmin : 4 ≤ n) (hnk : n < k)
    (hm : B n = A n*m) (hu : B k = A k*u)
    (hm_large : 8*(n:ℤ) ≤ |m|) (hu_large : 8*(k:ℤ) ≤ |u|) : 4*n < k := by
  by_contra! hkn
  have npos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have kle : (n:ℝ) ≤ k := by exact_mod_cast hnk.le
  have nfour : (4:ℝ) ≤ n := by exact_mod_cast nmin
  have lm : 8*(n:ℝ) ≤ |(m:ℝ)| := by exact_mod_cast hm_large
  have lu : 8*(n:ℝ) ≤ |(u:ℝ)| := by
    have hh : 8*(k:ℝ) ≤ |(u:ℝ)| := by exact_mod_cast hu_large
    linarith
  have ep : 0 < 8*(n:ℝ) := by positivity
  obtain ⟨a,ha⟩ := angle_near_grid hm (fun he => by subst m; simp at lm; linarith)
  obtain ⟨b,hb⟩ := angle_near_grid hu (fun he => by subst u; simp at lu; linarith)
  have pa := abs_le.mp (ha.trans (one_div_le_one_div_of_le ep lm))
  have pb := abs_le.mp (hb.trans (one_div_le_one_div_of_le ep lu))
  have ma := angle_advance_lower hnk
  have mb := angle_advance_upper (show 0<n by omega) hnk.le
  have hlog : Real.log (k:ℝ) - Real.log n ≤ Real.log 4 := by
    rw [← Real.log_div (npos.trans_le kle).ne' npos.ne']
    apply Real.strictMonoOn_log.monotoneOn (div_pos (npos.trans_le kle) npos) (by norm_num)
    exact (div_le_iff₀ npos).mpr (by exact_mod_cast hkn)
  have hlog4 : Real.log 4 < 7/5 := by
    rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    linarith only [Real.log_two_lt_d9]
  have eupper : 1/(8*(n:ℝ)) ≤ 1/32 := by gcongr; linarith
  have elower : 1/(8*(n:ℝ)) + 1/(8*(n:ℝ)) < (1/((n:ℝ)+1))/2 := by
    field_simp
    linarith
  rcases le_or_gt b a with ba | ab
  · have zab : (b:ℝ) ≤ a := by exact_mod_cast ba
    have hg := mul_le_mul_of_nonneg_right zab (by positivity : 0 ≤ Real.pi/2)
    linarith only [hg,pa.1,pb.2,elower,ma]
  · have zab : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
    have hg := mul_le_mul_of_nonneg_right zab (by positivity : 0 ≤ Real.pi/2)
    linarith only [hg,pa.2,pb.1,mb,hlog,hlog4,eupper,Real.pi_gt_three]

/-- A uniform slope bound beyond 2⁶⁴ implies uniform multiplicative spacing
of all integral indices there. -/
theorem integer_spacing
    (large : ∀ n : ℕ, 2^64 ≤ n → ∀ m : ℤ, B n = A n*m → 8*(n:ℤ) ≤ |m|)
    {n k : ℕ} (hn : 2^64 ≤ n) (hnk : n < k)
    (hin : IsIntegerValue n) (hik : IsIntegerValue k) : 4*n < k := by
  obtain ⟨m,hm⟩ := hin
  obtain ⟨u,hu⟩ := hik
  exact spacing_of_slopes (by omega) hnk hm hu (large n hn m hm) (large k (hn.trans hnk.le) u hu)

end ArctanGlobalSpacing

namespace ArctanGlobalSpacing

open Arxiv.«2607.05739» Finset

/-- The coordinate inequality puts the complementary angle within 1/(8n)
of a half-period. At a pole, A n vanishes and the displacement is zero. -/
lemma candidate_near_grid {n : ℕ} (hn : 0<n) (candidate : 8*(n:ℤ)*|A n| ≤ |B n|) :
    ∃ j : ℤ, |angleSum n - (j:ℝ)*(Real.pi/2)| ≤ 1/(8*(n:ℝ)) := by
  let θ := ∑ k ∈ Icc 1 n, Real.arctan k
  let ε := Real.arctan ((A n:ℝ)/(B n:ℝ))
  obtain ⟨c,_hc,hcos,hsin⟩ := ArctanTrigBridge.scaled_coordinates n
  have hp : 0 < 8*(n:ℝ) := by exact_mod_cast (show 0 < 8*n by omega)
  have hr : 8*(n:ℝ)*|(A n:ℝ)| ≤ |(B n:ℝ)| := by exact_mod_cast candidate
  have hb : (B n:ℝ) ≠ 0 := by
    intro hb
    have ha : (A n:ℝ) = 0 := by
      by_contra ha
      have pos := mul_pos hp (abs_pos.mpr ha)
      rw [hb,abs_zero] at hr
      exact pos.not_ge hr
    have hunit := Real.sin_sq_add_cos_sq θ
    dsimp only [θ] at hunit
    rw [hsin,hcos,ha,hb] at hunit
    norm_num at hunit
  have hε : Real.sin ε = ((A n:ℝ)/(B n:ℝ)) * Real.cos ε := by
    apply (div_eq_iff (Real.cos_arctan_pos _).ne').mp
    exact (Real.tan_eq_sin_div_cos _).symm.trans (Real.tan_arctan _)
  have hzero : Real.cos (θ+ε) = 0 := by
    rw [Real.cos_add,hε]
    dsimp only [θ]
    rw [hcos,hsin]
    field_simp
    ring
  obtain ⟨j,hj⟩ := Real.cos_eq_zero_iff.mp hzero
  refine ⟨(n:ℤ)-(2*j+1),?_⟩
  have hs := complementary_angles n
  change θ+angleSum n = _ at hs
  have he : angleSum n - (((n:ℤ)-(2*j+1):ℤ):ℝ)*(Real.pi/2) = ε := by
    push_cast
    linarith only [hs,hj]
  rw [he]
  calc
    |ε| ≤ |(A n:ℝ)/(B n:ℝ)| := arctan_abs _
    _ = |(A n:ℝ)|/|(B n:ℝ)| := abs_div _ _
    _ ≤ 1/(8*(n:ℝ)) := (div_le_div_iff₀ (abs_pos.mpr hb) hp).mpr (by
      rw [one_mul,mul_comm]
      exact hr)

/-- Candidates separated in index are separated by more than a factor of four.
The criterion uses integer arithmetic and includes exact poles. -/
theorem candidate_spacing {n k : ℕ} (hn : 4≤n) (hnk : n<k)
    (cn : 8*(n:ℤ)*|A n| ≤ |B n|) (ck : 8*(k:ℤ)*|A k| ≤ |B k|) : 4*n<k := by
  by_contra! hkn
  have npos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have kle : (n:ℝ) ≤ k := by exact_mod_cast hnk.le
  have nfour : (4:ℝ) ≤ n := by exact_mod_cast hn
  have ep : 0 < 8*(n:ℝ) := by positivity
  obtain ⟨a,ha⟩ := candidate_near_grid (by omega) cn
  obtain ⟨b,hb⟩ := candidate_near_grid (by omega) ck
  have pa := abs_le.mp ha
  have pb := abs_le.mp (hb.trans (one_div_le_one_div_of_le ep (by gcongr : 8*(n:ℝ) ≤ 8*(k:ℝ))))
  have ma := angle_advance_lower hnk
  have mb := angle_advance_upper (show 0<n by omega) hnk.le
  have hlog : Real.log (k:ℝ) - Real.log n ≤ Real.log 4 := by
    rw [← Real.log_div (npos.trans_le kle).ne' npos.ne']
    apply Real.strictMonoOn_log.monotoneOn (div_pos (npos.trans_le kle) npos) (by norm_num)
    exact (div_le_iff₀ npos).mpr (by exact_mod_cast hkn)
  have hlog4 : Real.log 4 < 7/5 := by
    rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    linarith only [Real.log_two_lt_d9]
  have eupper : 1/(8*(n:ℝ)) ≤ 1/32 := by gcongr; linarith
  have elower : 1/(8*(n:ℝ)) + 1/(8*(n:ℝ)) < (1/((n:ℝ)+1))/2 := by
    field_simp
    linarith
  rcases le_or_gt b a with ba | ab
  · have zab : (b:ℝ) ≤ a := by exact_mod_cast ba
    have hg := mul_le_mul_of_nonneg_right zab (by positivity : 0 ≤ Real.pi/2)
    linarith only [hg,pa.1,pb.2,elower,ma]
  · have zab : (a:ℝ)+1 ≤ b := by exact_mod_cast (show a+1≤b by omega)
    have hg := mul_le_mul_of_nonneg_right zab (by positivity : 0 ≤ Real.pi/2)
    linarith only [hg,pa.2,pb.1,mb,hlog,hlog4,eupper,Real.pi_gt_three]

/-- Every half-open block [N,4N) contains at most one candidate. -/
theorem candidate_card_le_one (N : ℕ) (hN : 4≤N) :
    ((Ico N (4*N)).filter (fun n : ℕ => 8*(n:ℤ)*|A n| ≤ |B n|)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro n hn k hk
  obtain ⟨⟨nlo,nhi⟩,cn⟩ := (Finset.mem_filter.mp hn).imp_left Finset.mem_Ico.mp
  obtain ⟨⟨klo,khi⟩,ck⟩ := (Finset.mem_filter.mp hk).imp_left Finset.mem_Ico.mp
  rcases lt_trichotomy n k with h | h | h
  · have := candidate_spacing (hN.trans nlo) h cn ck
    omega
  · exact h
  · have := candidate_spacing (hN.trans klo) h ck cn
    omega

/-- A large integral quotient satisfies the integer candidate test. -/
lemma candidate_of_large_quotient {n : ℕ} {m : ℤ} (hm : B n = A n*m) (large : 8*(n:ℤ) ≤ |m|) :
    8*(n:ℤ)*|A n| ≤ |B n| := by
  rw [hm,abs_mul,mul_comm |A n|]
  exact mul_le_mul_of_nonneg_right large (abs_nonneg _)

end ArctanGlobalSpacing

namespace ArctanCert

open Arxiv.«2607.05739»

/-- Substitution for the Gaussian unit transfers divisibility to an ordinary integer product. -/
private lemma split_evaluation (n q : ℕ) (u : ℤ) (hr : (q:ℤ) ∣ 1+u^2) :
    (q:ℤ) ∣ (∏ j ∈ Finset.Icc 1 n, (1+u*(j:ℤ))) ↔ (q:ℤ) ∣ A n+u*B n := by
  have hzero : (1 + (u:ZMod q)^2 : ZMod q)=0 := by
    simpa only [Int.cast_add,Int.cast_one,Int.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hr
  let φ : GaussianInt →+* ZMod q := Zsqrtd.lift ⟨(u:ZMod q),by
    simp only [Int.cast_neg,Int.cast_one]
    linear_combination hzero⟩
  have eqn : ((A n+u*B n : ℤ):ZMod q) = ((∏ j ∈ Finset.Icc 1 n, (1+u*(j:ℤ)) : ℤ):ZMod q) := by
    push_cast
    rw [mul_comm (u:ZMod q) (B n:ZMod q)]
    change φ (gaussProd n) = _
    rw [gaussProd,map_prod]
    apply Finset.prod_congr rfl
    intro j _
    change ((1:ℤ):ZMod q) + ((j:ℤ):ZMod q)*(u:ZMod q) = _
    simp [mul_comm]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd _ q,← ZMod.intCast_zmod_eq_zero_iff_dvd _ q,eqn]

private lemma remove_prime_power {p x y : ℤ} (hp : Prime p) (e d : ℕ)
    (hx : ¬p^(e+1) ∣ x) (hxy : p^(e+d) ∣ x*y) : p^d ∣ y := by
  induction e generalizing x with
  | zero => exact hp.pow_dvd_of_dvd_mul_left d (by simpa using hx) (by simpa using hxy)
  | succ e ih =>
    by_cases h : p ∣ x
    · obtain ⟨x,rfl⟩ := h
      apply ih (x:=x)
      · intro hz
        apply hx
        simpa only [pow_succ' p (e+1)] using mul_dvd_mul_left p hz
      · apply (mul_dvd_mul_iff_left hp.ne_zero).mp
        simpa only [Nat.succ_add,pow_succ',mul_assoc] using hxy
    · exact hp.pow_dvd_of_dvd_mul_left d h ((pow_dvd_pow p (by omega : d≤e+1+d)).trans hxy)

/-- An excess of `d` powers of a split prime on the positive signed product
forces an integral quotient to equal the chosen root modulo `p^d`. -/
lemma signed_prime_power {n p e d : ℕ} (hp : p.Prime) (hd : 0 < d) {u m : ℤ}
    (hroot : (p:ℤ)^(e+d) ∣ 1+u^2)
    (hplus : (p:ℤ)^(e+d) ∣ (∏ j ∈ Finset.Icc 1 n, (1+u*(j:ℤ))))
    (hminus : ¬(p:ℤ)^(e+1) ∣ (∏ j ∈ Finset.Icc 1 n, (1-u*(j:ℤ))))
    (hm : B n = A n*m) : (p:ℤ)^d ∣ m-u := by
  have plus : (p:ℤ)^(e+d) ∣ A n*(1+u*m) := by
    have hr : ((p^(e+d):ℕ):ℤ) ∣ 1+u^2 := by simpa only [Nat.cast_pow] using hroot
    have h := (split_evaluation n (p^(e+d)) u hr).mp (by simpa only [Nat.cast_pow] using hplus)
    simpa only [Nat.cast_pow,show A n+u*B n=A n*(1+u*m) by rw [hm]; ring] using h
  have hA : ¬(p:ℤ)^(e+1) ∣ A n := by
    intro ha
    apply hminus
    have hs := (pow_dvd_pow (p:ℤ) (by omega : e+1≤e+d)).trans hroot
    have hr : ((p^(e+1):ℕ):ℤ) ∣ 1+(-u)^2 := by simpa only [Nat.cast_pow,neg_sq] using hs
    have hb : ((p^(e+1):ℕ):ℤ) ∣ A n+(-u)*B n := by
      rw [Nat.cast_pow,show A n+(-u)*B n=A n*(1-u*m) by rw [hm]; ring]
      exact dvd_mul_of_dvd_left ha _
    simpa only [Nat.cast_pow,neg_mul,← sub_eq_add_neg] using (split_evaluation n (p^(e+1)) (-u) hr).mpr hb
  have hu := remove_prime_power (Nat.prime_iff_prime_int.mp hp) e d hA plus
  have hs := (pow_dvd_pow (p:ℤ) (by omega : d≤e+d)).trans hroot
  rw [show m-u = m*(1+u^2)-u*(1+u*m) by ring]
  exact dvd_sub (dvd_mul_of_dvd_right hs m) (dvd_mul_of_dvd_right hu u)

end ArctanCert

namespace ArctanGlobal

open Arxiv.«2607.05739»

/-- Cilleruelo's non-square theorem, with an explicit large-index estimate and
a short finite chain of odd primes covering the remaining indices. -/
theorem norm_ne_square {n : ℕ} (hn : 4≤n) :
    ¬ IsSquare (∏ k ∈ Finset.Icc 1 n, (k^2+1)) := by
  by_cases small : n<2^64
  · exact norm_not_square_word hn small
  rintro ⟨b,hb⟩
  exact norm_not_square_large (n:=n) (b:=b) (by omega) (by simpa only [pow_two] using hb)

/-- The factorial Gaussian product has nonzero real part at every natural index. -/
theorem real_ne_zero (n : ℕ) : A n≠0 := by
  by_cases early : n≤3
  · interval_cases n <;> decide
  intro h
  apply norm_ne_square (n:=n) (by omega)
  refine ⟨(B n).natAbs,?_⟩
  rw [product_norm,h]
  simp [pow_two]

/-- The ordinary real tangent has no poles at any of these arctangent sums. -/
theorem cosine_ne_zero (n : ℕ) : Real.cos (∑ j ∈ Finset.Icc 1 n, Real.arctan j) ≠ 0 := by
  obtain ⟨c,hc,cosine,_⟩ := ArctanTrigBridge.scaled_coordinates n
  rw [cosine]
  exact mul_ne_zero hc.ne' (by exact_mod_cast real_ne_zero n)

/-- Distinct integral indices above the word-size range must be more than a factor of four apart. -/
theorem exceptional_spacing {n k : ℕ} (hn : 2^64 ≤ n) (hnk : n<k)
    (hin : IsIntegerValue n) (hik : IsIntegerValue k) : 4*n < k :=
  ArctanGlobalSpacing.integer_spacing (fun _ h _ eq => quotient_large_linear h eq) hn hnk hin hik

end ArctanGlobal

namespace OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R2

open Arxiv.«2607.05739» Finset

section BoundedIndicesOrQuotients

/-- All nonexceptional indices within a word, and all quotients of fewer than
the threshold number of binary digits at arbitrary indices. -/
def H1 : Prop :=
  ∀ n : ℕ, 5≤n → ∀ m : ℤ, (n<2^64 ∨ m.natAbs.log2<2^61) → B n ≠ A n*m

end BoundedIndicesOrQuotients

section CandidateIndices

/-- At most one explicitly defined integer per fourfold interval can remain.
A surviving integer quotient must pass every signed prime-power test. -/
def H2 : Prop :=
  ∀ j : ℕ, 32≤j →
    let N := 4^j
    let C := (Ico N (4*N)).filter (fun n : ℕ => 8*(n:ℤ)*|A n| ≤ |B n|)
    ∀ hC : C.Nonempty,
      let n := C.max' hC
      ∀ m : ℤ, 2^(n/8) ≤ m.natAbs →
        (∀ (p e d : ℕ) (u : ℤ), p.Prime → 0<d → (p:ℤ)^(e+d) ∣ 1+u^2 →
          (p:ℤ)^(e+d) ∣ (∏ k ∈ Icc 1 n, (1+u*(k:ℤ))) →
          (¬ (p:ℤ)^(e+1) ∣ (∏ k ∈ Icc 1 n, (1-u*(k:ℤ)))) → (p:ℤ)^d ∣ m-u) →
        B n ≠ A n*m

end CandidateIndices

/-- The finite word-size result also excludes small integer quotients at every
larger index, by the effective exponential barrier. -/
lemma bounded_of_word (finite : ∀ n : ℕ, 5≤n → n<2^64 → ¬IsIntegerValue n) : H1 := by
  intro n hn m region hm
  by_cases first : n<2^64
  · exact finite n hn first ⟨m,hm⟩
  have small := region.resolve_left first
  have idx := ArctanGlobal.index_lt_bit_bound (by omega) hm
  omega

theorem main : H1 → H2 → type_of% @Arxiv.«2607.05739».tan_arctan_sum_not_integer := by
  intro bounded candidates n hn integral
  obtain ⟨m,hm⟩ := integral
  by_cases small : n<2^64
  · exact bounded n hn m (Or.inl small) hm
  have large : 2^64 ≤ n := by omega
  let j := Nat.log 4 n
  let N := 4^j
  have hj : 32≤j := (Nat.le_log_iff_pow_le (by decide : 1<4) (by omega : n≠0)).mpr
    (by exact large : 4^32≤n)
  have lower : N≤n := Nat.pow_log_le_self _ (by omega)
  have upper : n<4*N := by
    simpa only [j,N,pow_succ,Nat.mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1<4) n)
  let C := (Ico N (4*N)).filter (fun k : ℕ => 8*(k:ℤ)*|A k| ≤ |B k|)
  have member : n ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨lower,upper⟩,
    ArctanGlobalSpacing.candidate_of_large_quotient hm (ArctanGlobal.quotient_large_linear large hm)⟩
  have nonempty : C.Nonempty := ⟨n,member⟩
  have four : 4≤N := Nat.pow_le_pow_right (by decide : 0<4) (show 1≤j by omega)
  have card : C.card ≤ 1 := ArctanGlobalSpacing.candidate_card_le_one N four
  have same : C.max' nonempty = n :=
    (Finset.card_le_one.mp card) _ (C.max'_mem nonempty) _ member
  have eqn : B (C.max' nonempty)=A (C.max' nonempty)*m := by simpa only [same] using hm
  have index : 2^64≤C.max' nonempty := by simpa only [same] using large
  exact candidates j hj nonempty m (ArctanGlobal.quotient_exponential index eqn)
    (fun _ _ _ _ hp hd root plus minus => ArctanCert.signed_prime_power hp hd root plus minus eqn) eqn

/-- Both tests are necessary: every tested candidate really is an index in the specified tail. -/
lemma necessary (all_indices : type_of% @Arxiv.«2607.05739».tan_arctan_sum_not_integer) : H1 ∧ H2 := by
  constructor
  · intro n hn m _ hm
    exact all_indices n hn ⟨m,hm⟩
  · intro j hj
    let N := 4^j
    let C := (Ico N (4*N)).filter (fun n : ℕ => 8*(n:ℤ)*|A n| ≤ |B n|)
    dsimp only
    intro hC m _ _ hm
    have mem : C.max' hC ∈ C := C.max'_mem hC
    have start := (Finset.mem_Ico.mp (Finset.mem_filter.mp mem).1).1
    have lo : 4^32≤N := Nat.pow_le_pow_right (by decide) hj
    exact all_indices (C.max' hC) (by omega) ⟨m,hm⟩

lemma iff_bounded_and_candidates :
    (type_of% @Arxiv.«2607.05739».tan_arctan_sum_not_integer) ↔ H1 ∧ H2 :=
  ⟨necessary, fun h => main h.1 h.2⟩

end OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R2
