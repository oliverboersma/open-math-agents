import OMAReductions.R_OeisA224_conjecture_R1_H2_R1
import Mathlib

/-!
The prime-power count, product identity, and square-quotient gap are
adapted from @HudZah's reduction OeisA224.conjecture.R1.H2.R1.H2.R1.
The coprime product formula is used from the parent reduction. A gap in
the combined list of primes and prime powers bounds the denominator of a
rational approximation to the product of their count ratios.
-/

open Finset Function OeisA224

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R3

theorem count_step (p e : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    a (p^(e+2)) = a (p^e) + (p^(e+1)*(p-1))/2 := by
  classical
  let residues (n : ℕ) : Finset ℕ :=
    (Finset.range n).image (fun k => k^2 % n)

  have mem_res {n r : ℕ} (hn : 0 < n) :
      r ∈ residues n ↔ ∃ k : ℕ, k^2 % n = r := by
    constructor
    · intro hr
      obtain ⟨k, _, h⟩ := Finset.mem_image.mp hr
      exact ⟨k, h⟩
    · rintro ⟨k, rfl⟩
      exact Finset.mem_image.mpr ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt _ hn), (Nat.pow_mod ..).symm⟩

  let unitSq (n : ℕ) [NeZero n] : Finset ℕ := by
    classical
    exact Finset.univ.image (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
      (u.val.val).val)

  have mem_unitSq {n x : ℕ} [NeZero n] :
      x ∈ unitSq n ↔ ∃ u : (ZMod n)ˣ, ((u : ZMod n)^2).val = x := by
    classical
    constructor
    · intro hx
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv⟩ := u.property
      exact ⟨v, by simpa [← hv] using hu⟩
    · rintro ⟨u, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨u ^ 2, u, rfl⟩, Finset.mem_univ _, rfl⟩

  have unitSq_card (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] (hn : 2 < n) :
      (unitSq n).card = n.totient / 2 := by
    classical
    unfold unitSq
    have hi : Function.Injective (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
        u.val.val.val) := fun _ _ h => Subtype.ext (Units.ext (ZMod.val_injective n h))
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.gcd_eq_right (even_iff_two_dvd.mp (Nat.totient_even hn))]

  let N := p^(e+2)
  have hp0 := hp.pos
  have hn0 : 0 < N := pow_pos hp0 _
  have : NeZero N := ⟨hn0.ne'⟩
  have : IsCyclic (ZMod N)ˣ := ZMod.isCyclic_units_of_prime_pow p hp hne (e+2)
  have fact (u : ℕ) : (p*u)^2 % N = p^2 * (u^2 % p^e) := by
    rw [show N = p^2*p^e by dsimp [N]; ring, mul_pow, Nat.mul_mod_mul_left]
  let M := (residues (p^e)).image (fun t => p^2*t)
  have split : residues N = M ∪ unitSq N := by
    ext r
    constructor
    · intro hr
      obtain ⟨k, rfl⟩ := (mem_res hn0).mp hr
      by_cases hpk : p ∣ k
      · obtain ⟨u, rfl⟩ := hpk
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨u^2 % p^e, (mem_res (pow_pos hp0 _)).mpr ⟨u, rfl⟩, (fact u).symm⟩)
      · have hu : IsUnit (k : ZMod N) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hpk
        apply Finset.mem_union_right
        apply mem_unitSq.mpr
        exact ⟨hu.unit, by rw [IsUnit.unit_spec, ← Nat.cast_pow, ZMod.val_natCast]⟩
    · intro hr
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨u, rfl⟩ := (mem_res (pow_pos hp0 _)).mp ht
        exact (mem_res hn0).mpr ⟨p*u, fact u⟩
      · obtain ⟨u, rfl⟩ := mem_unitSq.mp hr
        exact (mem_res hn0).mpr ⟨u.val.val, by rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]⟩
  have disj : Disjoint M (unitSq N) := by
    apply Finset.disjoint_left.mpr
    rintro r hr hunit
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, hu⟩ := mem_unitSq.mp hunit
    have hU : IsUnit (((p^2*t : ℕ) : ZMod N)) := by
      rw [← hu, ZMod.natCast_zmod_val]
      exact u.isUnit.pow 2
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0 < e+2 by omega)).mp hU
      ((dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _))
  have high : 2 < N := lt_of_lt_of_le (lt_of_le_of_ne hp.two_le (Ne.symm hne))
    (Nat.le_pow (by omega : 0 < e+2))
  have hcnt : (unitSq N).card = _ := unitSq_card N high
  have hcard : (residues (p^e)).card = a (p^e) := by rw [a, if_neg (pow_ne_zero _ hp.ne_zero)]
  change a N = _
  rw [a, if_neg hn0.ne']
  change (residues N).card = _
  rw [split, Finset.card_union_of_disjoint disj, hcnt]
  dsimp only [M]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h), hcard]
  dsimp only [N]
  rw [Nat.totient_prime_pow_succ hp]

private theorem prime_count {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : a p = p / 2 + 1 := by
  rw [OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp hodd]
  have := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  omega

private theorem count_formula (p : ℕ) (hp : p.Prime) (po : Odd p) (e : ℕ) :
    2*(p+1)*(a (p^e)-1) + (if Even e then p else 1) = p^(e+1) := by
  have hne : p ≠ 2 := by rintro rfl; norm_num at po
  induction e using Nat.twoStepInduction with
  | zero => simp [a_1]
  | one =>
    simp only [pow_one, prime_count hp hne, Nat.add_sub_cancel]
    obtain ⟨k, hk⟩ := po
    have hhalf : p/2 = k := by omega
    rw [hhalf, hk]
    simp
    ring
  | more e ih _ =>
    let x := p^(e+1)
    let q := x*(p-1)/2
    have hdouble : 2*q = x*(p-1) := by
      apply Nat.mul_div_cancel'
      apply dvd_mul_of_dvd_right
      have hh := Nat.odd_iff.mp po
      omega
    have ha : 1 ≤ a (p^e) := by
      rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
      exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
    have hadd : a (p^(e+2)) - 1 = (a (p^e) - 1) + q := by
      rw [count_step p e hp hne]
      change a (p^e) + q - 1 = _
      omega
    have ev : Even (e+2) ↔ Even e := by simp only [Nat.even_iff]; omega
    rw [hadd, if_congr ev rfl rfl]
    calc
      _ = (2*(p+1)*(a (p^e)-1) + (if Even e then p else 1)) + (p+1)*(2*q) := by ring
      _ = x + (p+1)*(x*(p-1)) := by rw [ih, hdouble]
      _ = p^((e+2)+1) := by
        rw [show e+2+1 = (e+1)+2 by omega, pow_add]
        change x + (p+1)*(x*(p-1)) = x*p^2
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
        rw [hj]
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        ring

private theorem cleared (p e : ℕ) (hp : p.Prime) (hpo : Odd p) :
    2*(p+1)*a (p^e) = p*p^e + (if Even e then p+2 else 2*p+1) := by
  have h := count_formula p hp hpo e
  have ha : 1 ≤ a (p^e) := by
    rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
    exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
  have restore := congrArg (fun x => 2*(p+1)*x) (Nat.sub_add_cancel ha)
  by_cases hEven : Even e <;> simp only [hEven, if_true, if_false, pow_succ] at * <;> nlinarith only [h, restore]

private theorem base_bounds {p e r : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : 0 < e) (hc : r ≤ p) :
    r*p^e ≤ 2*(r+1)*a (p^e) ∧ 2*r*a (p^e) ≤ (r+1)*p^e := by
  have eqn := cleared p e hp ho
  have ck : (if Even e then p+2 else 2*p+1) ≤ 2*p+1 := by
    split <;> have := hp.one_lt <;> omega
  have pn : p ≤ p^e := Nat.le_pow he
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := p+1) _ (by omega)
    have hmul := Nat.mul_le_mul_right (p^e) hc
    nlinarith only [congrArg (fun x => (r+1)*x) eqn, hmul,
      Nat.zero_le ((r+1)*(if Even e then p+2 else 2*p+1))]
  · apply Nat.le_of_mul_le_mul_left (c := p+1) _ (by omega)
    have small := Nat.mul_le_mul_left r ck
    have h1 := Nat.mul_le_mul_left r pn
    have h2 := Nat.mul_le_mul_right (p+1) (hc.trans pn)
    nlinarith only [congrArg (fun x => r*x) eqn, small, h1, h2]

private theorem impossible_square {n a t k : ℕ} (ha : 0 < a)
    (hk : t^2=k) (kbig : 4<k) (ksmall : k<4*n+5)
    (eqn : n^2 = a*(a-1)*k+1) : False := by
  have ha' : a-1+1=a := Nat.sub_add_cancel ha
  have id : (t*(2*(a-1)+1))^2 + 4 = (2*n)^2+k := by
    rw [mul_pow, hk]
    nlinarith only [eqn,congrArg (fun x => x*(a-1)*k) ha']
  rcases le_or_gt (t*(2*(a-1)+1)) (2*n) with h|h
  · nlinarith only [id,kbig,Nat.pow_le_pow_left h 2]
  · have := Nat.pow_le_pow_left (show 2*n+1 ≤ t*(2*(a-1)+1) by omega) 2
    nlinarith only [id,ksmall,this]



private theorem prod_counts (n : ℕ) (hz : n ≠ 0) :
    a n = ∏ p ∈ n.primeFactors, a (p^(n.factorization p)) := by
  apply Nat.multiplicative_factorization a _ OeisA224.a_1 hz
  intro x y hc
  by_cases hx : x = 0
  · subst x
    have hy : y = 1 := by simpa using hc
    simp [hy,OeisA224.a_1]
  by_cases hy : y = 0
  · subst y
    have hx1 : x = 1 := by simpa using hc
    simp [hx1,OeisA224.a_1]
  exact OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) hc

private theorem empty_band (s : Finset ℕ) (b : ℕ → ℕ) (hb : Monotone b)
    (r : ℕ) (hc : s.card ≤ r) :
    ∃ i ≤ r, ∀ x ∈ s, x ≤ b i ∨ b (i+1) < x := by
  classical
  by_contra! h
  choose f hmem hlow hhigh using h
  have hmap : Set.MapsTo (fun i : ℕ => if h : i ≤ r then f i h else 0)
      (range (r+1)) s := by
    intro i hi
    have hir : i ≤ r := Nat.le_of_lt_succ (mem_range.mp hi)
    simpa only [dif_pos hir, Finset.mem_coe] using hmem i hir
  obtain ⟨i, hi, j, hj, hij, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (show s.card < (range (r+1)).card by simpa using Nat.lt_succ_of_le hc) hmap
  have hir : i ≤ r := Nat.le_of_lt_succ (mem_range.mp hi)
  have hjr : j ≤ r := Nat.le_of_lt_succ (mem_range.mp hj)
  simp only [dif_pos hir, dif_pos hjr] at he
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact (not_lt_of_ge ((hhigh i hir).trans (hb hlt))) (he ▸ hlow j hjr)
  · exact (not_lt_of_ge ((hhigh j hjr).trans (hb hlt))) (he ▸ hlow i hir)

private theorem product_bounds {α : Type*} (s : Finset α) (f : α → ℚ)
    (hf : ∀ p ∈ s, 3/2 ≤ f p ∧ f p ≤ 3) :
    (3/2 : ℚ)^s.card ≤ ∏ p ∈ s, f p ∧ ∏ p ∈ s, f p ≤ (3 : ℚ)^s.card := by
  have hf0 (p : α) (hp : p ∈ s) : 0 ≤ f p :=
    (by norm_num : (0 : ℚ) ≤ 3/2).trans (hf p hp).1
  constructor
  · simpa only [Finset.prod_const] using
      (Finset.prod_le_prod (fun _ _ => by norm_num : ∀ p ∈ s, (0 : ℚ) ≤ 3/2)
        (fun p hp => (hf p hp).1))
  · simpa only [Finset.prod_const] using Finset.prod_le_prod hf0 (fun p hp => (hf p hp).2)

private theorem product_approx {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → ℚ) (ε : ℚ)
    (he : 0 ≤ ε) (hf : ∀ p ∈ s, 0 ≤ f p ∧ f p ≤ 3)
    (hg : ∀ p ∈ s, 0 ≤ g p ∧ g p ≤ 3)
    (hfg : ∀ p ∈ s, |f p - g p| ≤ ε) :
    |(∏ p ∈ s, f p) - ∏ p ∈ s, g p| ≤ (6 : ℚ)^s.card * ε := by
  induction s using Finset.induction_on with
  | empty => simpa using he
  | @insert p s hp ih =>
    have sf (q : α) (hq : q ∈ s) := hf q (mem_insert_of_mem hq)
    have sg (q : α) (hq : q ∈ s) := hg q (mem_insert_of_mem hq)
    have pd := ih sf sg (fun q hq => hfg q (mem_insert_of_mem hq))
    let F := ∏ q ∈ s, f q
    let G := ∏ q ∈ s, g q
    have hf' := hf p (by simp)
    have g0 : 0 ≤ G := Finset.prod_nonneg (fun q hq => (sg q hq).1)
    have g3 : G ≤ (3 : ℚ)^s.card := by
      simpa only [Finset.prod_const] using
        Finset.prod_le_prod (fun q hq => (sg q hq).1) (fun q hq => (sg q hq).2)
    have g6 : G ≤ (6 : ℚ)^s.card := g3.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
    simp only [Finset.prod_insert hp, Finset.card_insert_of_notMem hp, pow_succ]
    change |f p * F - g p * G| ≤ (6 : ℚ)^s.card * 6 * ε
    rw [show f p * F - g p * G = f p * (F-G) + (f p-g p) * G by ring]
    calc
      _ ≤ f p * |F-G| + |f p-g p| * G := by
        simpa only [abs_mul, abs_of_nonneg hf'.1, abs_of_nonneg g0] using
          abs_add_le (f p * (F-G)) ((f p-g p) * G)
      _ ≤ 3 * (6 : ℚ)^s.card * ε + ε * (6 : ℚ)^s.card := by
        apply add_le_add
        · have := mul_le_mul hf'.2 pd (abs_nonneg _) (by norm_num : (0 : ℚ) ≤ 3)
          linarith only [this]
        · exact mul_le_mul (hfg p (by simp)) g6 g0 he
      _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ (6 : ℚ)^s.card by positivity) he]

private theorem atomic_ratios {p e B C : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : 0 < e) (hB : 1 ≤ B) (hC : 0 < C)
    (prime_band : p ≤ B ∨ C < p) (power_band : p^e ≤ B ∨ C < p^e) :
    ∃ u v : ℕ, 0 < v ∧ v ≤ B ∧
      (3/2 : ℚ) ≤ (p^e : ℕ)/(a (p^e) : ℚ) ∧ (p^e : ℕ)/(a (p^e) : ℚ) ≤ 3 ∧
      (3/2 : ℚ) ≤ (u : ℚ)/v ∧ (u : ℚ)/v ≤ 3 ∧
      |(p^e : ℕ)/(a (p^e) : ℚ) - (u : ℚ)/v| ≤ 12/(C : ℚ) := by
  have p3 : 3 ≤ p := by
    have hn := hp.two_le
    obtain ⟨i, hi⟩ := ho
    omega
  let x := p^e
  let d := a x
  let c := if Even e then p+2 else 2*p+1
  have x0 : 0 < x := pow_pos hp.pos e
  have d1 : 2 ≤ d := OMA.R_OeisA224_conjecture_R1.two_le_a x
    (hp.two_le.trans (Nat.le_pow he))
  have cover : (2 : ℚ)*((p : ℚ)+1)*d = p*x+c := by
    exact_mod_cast cleared p e hp ho
  have ppos : 0 < (p:ℚ) := by exact_mod_cast hp.pos
  have dpos : 0 < (d:ℚ) := by exact_mod_cast (show 0 < d by omega)
  have cnonneg : 0 ≤ (c:ℚ) := by positivity
  have c3 : (c:ℚ) ≤ 3*p := by
    have : c ≤ 3*p := by dsimp [c]; split <;> omega
    exact_mod_cast this
  have p3' : 3 ≤ (p:ℚ) := by exact_mod_cast p3
  have x3d : (x:ℚ) ≤ 3*d := by
    have := (base_bounds hp ho he p3).1
    have h : (3:ℚ)*x ≤ 8*d := by exact_mod_cast this
    linarith
  have fbound : (3/2 : ℚ) ≤ (x:ℚ)/d ∧ (x:ℚ)/d ≤ 3 := by
    constructor
    · apply (le_div_iff₀ dpos).mpr
      have h : (6:ℚ)*d ≤ 4*x := by exact_mod_cast (base_bounds hp ho he p3).2
      linarith
    · exact (div_le_iff₀ dpos).mpr x3d
  have xpos : 0 < (x:ℚ) := by exact_mod_cast x0
  have Cpos : 0 < (C:ℚ) := by exact_mod_cast hC
  have one_error : |(x:ℚ)/d - 2*((p:ℚ)+1)/p| ≤ 9/(x:ℚ) := by
    have eq : (x:ℚ)/d - 2*((p:ℚ)+1)/p = -((c:ℚ)/p/d) := by
      field_simp
      linarith only [cover]
    rw [eq, abs_neg, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 3/(d:ℚ) := div_le_div_of_nonneg_right ((div_le_iff₀ ppos).mpr c3) dpos.le
      _ ≤ 9/(x:ℚ) := (div_le_div_iff₀ dpos xpos).mpr (by linarith only [x3d])
  rcases power_band with small | large
  · have dle : d ≤ x := by
      change a x ≤ x
      rw [a, if_neg x0.ne']
      exact Finset.card_image_le.trans_eq (Finset.card_range x)
    exact ⟨x, d, by omega, dle.trans small, fbound.1, fbound.2, fbound.1,
      fbound.2, by rw [sub_self, abs_zero]; positivity⟩
  · have short : 9/(x:ℚ) ≤ 9/(C:ℚ) := by
      apply div_le_div_of_nonneg_left (by norm_num) Cpos
      exact_mod_cast large.le
    rcases prime_band with smallp | largep
    · refine ⟨2*(p+1), p, hp.pos, smallp, fbound.1, fbound.2, ?_, ?_, ?_⟩
      · push_cast
        apply (le_div_iff₀ ppos).mpr
        linarith only [ppos]
      · push_cast
        apply (div_le_iff₀ ppos).mpr
        linarith only [p3']
      · push_cast
        simpa only [x, d, Nat.cast_pow] using
          one_error.trans (short.trans (div_le_div_of_nonneg_right (show (9:ℚ) ≤ 12 by norm_num) Cpos.le))
    · refine ⟨2, 1, by decide, hB, fbound.1, fbound.2, by norm_num, by norm_num, ?_⟩
      norm_num only [Nat.cast_ofNat, Nat.cast_one, div_one]
      have close_two : 2*((p:ℚ)+1)/p - 2 = 2/(p:ℚ) := by field_simp; ring
      rw [show (x:ℚ)/d - 2 = ((x:ℚ)/d - 2*((p:ℚ)+1)/p) +
        (2*((p:ℚ)+1)/p - 2) by ring]
      have small_two : 2/(p:ℚ) ≤ 2/(C:ℚ) := by
        apply div_le_div_of_nonneg_left (by norm_num) Cpos
        exact_mod_cast largep.le
      calc
        _ ≤ |(x:ℚ)/d - 2*((p:ℚ)+1)/p| + |2*((p:ℚ)+1)/p - 2| := abs_add_le _ _
        _ ≤ 9/(C:ℚ) + 2/(C:ℚ) := by
          rw [close_two, abs_of_nonneg (show 0 ≤ (2:ℚ)/p by positivity)]
          exact add_le_add (one_error.trans short) small_two
        _ ≤ _ := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by norm_num) Cpos.le

private theorem nearby_square {k u v : ℕ} (hv : 0 < v)
    (h : |(k:ℚ) - ((u:ℚ)/v)^2| < 1/(v:ℚ)^2) : IsSquare k := by
  have vpos : 0 < (v:ℚ)^2 := by positivity
  have prod := (lt_div_iff₀ vpos).mp h
  rw [← abs_of_pos vpos, ← abs_mul, sub_mul, div_pow,
    div_mul_cancel₀ _ vpos.ne'] at prod
  have eq : k*v^2 = u^2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hgap : ((k:ℚ)*v^2)+1 ≤ (u:ℚ)^2 := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      linarith only [prod, hgap, neg_le_abs ((k:ℚ)*v^2-(u:ℚ)^2)]
    · have hgap : (u:ℚ)^2+1 ≤ (k:ℚ)*v^2 := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      linarith only [prod, hgap, le_abs_self ((k:ℚ)*v^2-(u:ℚ)^2)]
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(u:ℚ)/v, ?_⟩
  rw [← pow_two, div_pow, eq_div_iff vpos.ne']
  exact_mod_cast eq

private theorem quotient_estimate {n A k r C : ℕ} (hr : 3 ≤ r)
    (hn : C < n) (hc : 0 < C) (ha : 2 ≤ A)
    (hlo : (3/2 : ℚ)^r ≤ (n:ℚ)/A) (hhi : (n:ℚ)/A ≤ (3:ℚ)^r)
    (eqn : n^2 = A*(A-1)*k+1) :
    4 < k ∧ k ≤ 2*9^r ∧ |(k:ℚ)-((n:ℚ)/A)^2| ≤ (2*27^r)/(C:ℚ) := by
  have hA : 2 ≤ (A:ℚ) := by exact_mod_cast ha
  have Ap : 0 < (A:ℚ) := by positivity
  have Asq : 0 < (A:ℚ)^2 := by positivity
  have Cp : 0 < (C:ℚ) := by positivity
  have hk : 1 ≤ k := by
    by_contra! h
    have hsq := Nat.pow_le_pow_left (show 2 ≤ n by omega) 2
    simp [show k=0 by omega] at eqn
    omega
  have k1 : 1 ≤ (k:ℚ) := by exact_mod_cast hk
  have heq : (n:ℚ)^2 = (A:ℚ)*((A:ℚ)-1)*k+1 := by
    have lifted := congrArg (fun x : ℕ => (x:ℚ)) eqn
    push_cast [Nat.cast_sub (show 1 ≤ A by omega)] at lifted
    exact lifted
  have ident : (k:ℚ)-((n:ℚ)/A)^2 = ((k:ℚ)*A-1)/(A:ℚ)^2 := by
    field_simp
    nlinarith only [heq]
  have num0 : 0 ≤ (k:ℚ)*A-1 := by
    nlinarith only [mul_le_mul_of_nonneg_right k1 Ap.le, hA]
  have kmin : 4 < k := by
    have base := pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 3/2) hr
    have ratio : (2:ℚ) < (n:ℚ)/A := by
      have := base.trans hlo
      norm_num at this
      linarith
    have weight := mul_self_lt_mul_self (by norm_num : (0:ℚ) ≤ 2) ratio
    have tail : 0 ≤ (k:ℚ)-((n:ℚ)/A)^2 := by
      rw [ident]
      positivity
    exact_mod_cast (show (4:ℚ) < k by nlinarith only [weight, tail])
  have hnsq : ((n:ℚ)/A)^2 ≤ (9:ℚ)^r := calc
    _ ≤ ((3:ℚ)^r)^2 := pow_le_pow_left₀ (by positivity) hhi _
    _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have half : (A:ℚ)^2/2 ≤ (A:ℚ)*((A:ℚ)-1) := by
    nlinarith only [mul_nonneg Ap.le (sub_nonneg.mpr hA)]
  have klow : (k:ℚ)/2 ≤ ((n:ℚ)/A)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ Asq).mpr
    nlinarith only [heq, mul_le_mul_of_nonneg_left half (show 0 ≤ (k:ℚ) by positivity)]
  have kup : (k:ℚ) ≤ 2*9^r := by linarith only [klow, hnsq]
  refine ⟨kmin, by exact_mod_cast kup, ?_⟩
  rw [ident, abs_of_nonneg (div_nonneg num0 Asq.le)]
  calc
    _ ≤ (k:ℚ)/A := by
      apply (div_le_iff₀ Asq).mpr
      rw [show (k:ℚ)/A * (A:ℚ)^2 = (k:ℚ)*A by field_simp]
      linarith
    _ ≤ (2*9^r)/(A:ℚ) := div_le_div_of_nonneg_right kup Ap.le
    _ ≤ _ := by
      have size : (C:ℚ) ≤ (3:ℚ)^r*A :=
        (show (C:ℚ) ≤ n by exact_mod_cast hn.le).trans ((div_le_iff₀ Ap).mp hhi)
      apply (div_le_div_iff₀ Ap Cp).mpr
      have hlim := mul_le_mul_of_nonneg_left size (show 0 ≤ (2:ℚ)*9^r by positivity)
      calc
        _ ≤ (2*9^r)*((3:ℚ)^r*A) := hlim
        _ = _ := by rw [← show ((9:ℚ)*3)^r = 27^r by norm_num]; rw [mul_pow]; ring

private theorem count_square_ge (n : ℕ) (hn : 0 < n) : n ≤ (a n)^2 := by
  by_contra! h
  let f (i : ℕ) := i^2
  have inj : Function.Injective f := by
    intro i j he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)).ne he
    · exact (Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)).ne he.symm
  have sub : ((range (a n+1)).image f) ⊆ (range n).image (fun k : ℕ => k^2 % n) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hle : i ≤ a n := Nat.le_of_lt_succ (mem_range.mp hi)
    have hisq := (Nat.pow_le_pow_left hle 2).trans_lt h
    have hin : i < n := (Nat.le_pow (by decide : 0 < 2)).trans_lt hisq
    exact mem_image.mpr ⟨i, mem_range.mpr hin, Nat.mod_eq_of_lt hisq⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj, Finset.card_range] at count
  have eq : ((range n).image (fun k : ℕ => k^2 % n)).card = a n := by
    rw [a, if_neg hn.ne']
  rw [eq] at count
  omega

private theorem ratio_bounds (n : ℕ) (hn : 0 < n) (ho : Odd n) :
    let r := n.primeFactors.card
    (3/2:ℚ)^r ≤ (n:ℚ)/a n ∧ (n:ℚ)/a n ≤ (3:ℚ)^r := by
  let f (p : ℕ) := ((p^(n.factorization p) : ℕ):ℚ)/a (p^(n.factorization p))
  have eq : (∏ p ∈ n.primeFactors, f p) = (n:ℚ)/a n := by
    simp only [f, Finset.prod_div_distrib, ← Nat.cast_prod]
    rw [← prod_counts n hn.ne', ← Nat.prod_primeFactors_pow_factorization hn.ne']
  rw [← eq]
  apply product_bounds
  intro p hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have po : Odd p := by
    by_contra! bad
    exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp bad)).trans pd)
  obtain ⟨_, _, _, _, hlo, hhi, _⟩ :=
    atomic_ratios pp po (pp.factorization_pos_of_dvd hn.ne' pd) hn (by decide : 0 < 1)
      (Or.inl (Nat.le_of_dvd hn pd)) (Or.inl (Nat.le_of_dvd hn (Nat.ordProj_dvd n p)))
  exact ⟨hlo, hhi⟩

/-- The quotient in any counterexample is a nonsquare below twice the modulus. -/
theorem counterexample_quotient (n : ℕ) (ho : Odd n) (hr : 3 ≤ n.primeFactors.card)
    (ht : n^2 ≡ 1 [MOD a n*(a n-1)]) :
    ∃ k : ℕ, 4 < k ∧ k ≤ 2*9^n.primeFactors.card ∧ k < 2*n ∧ ¬ IsSquare k ∧
      n^2 = a n*(a n-1)*k+1 := by
  have hn : 1 < n := by
    by_contra! h
    interval_cases n <;> simp at hr
  have npos : 0 < n := by omega
  have n2pos : 0 < n^2 := pow_pos npos _
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt n2pos)).mp ht.symm
  have eqn : n^2 = a n*(a n-1)*k+1 := by omega
  have ha := OMA.R_OeisA224_conjecture_R1.two_le_a n hn
  obtain ⟨lo, hi⟩ := ratio_bounds n npos ho
  obtain ⟨kbig, kbound, _⟩ := quotient_estimate hr hn Nat.one_pos ha lo hi eqn
  have doubled : (a n)^2 ≤ 2*(a n*(a n-1)) := by
    have hm := Nat.mul_le_mul_left (a n) (show a n ≤ 2*(a n-1) by omega)
    rw [pow_two, ← mul_left_comm (a n) 2 (a n-1)]
    exact hm
  have size := Nat.mul_le_mul_right k ((count_square_ge n npos).trans doubled)
  have kn : k < 2*n := by
    apply (Nat.mul_lt_mul_left npos).mp
    nlinarith only [size, eqn]
  refine ⟨k, kbig, kbound, kn, ?_, eqn⟩
  rintro ⟨t, he⟩
  exact impossible_square (by omega) (by simpa only [pow_two] using he.symm) kbig (by omega) eqn

private theorem band_fails (n B C : ℕ) (ho : Odd n) (hr : 3 ≤ n.primeFactors.card)
    (hB : 1 ≤ B) (hC : C = 64*27^n.primeFactors.card*B^(2*n.primeFactors.card))
    (hnC : C < n)
    (hsplit : ∀ p ∈ n.primeFactors,
      (p ≤ B ∨ C < p) ∧ (p^(n.factorization p) ≤ B ∨ C < p^(n.factorization p))) :
    ¬ n^2 ≡ 1 [MOD a n*(a n-1)] := by
  classical
  intro ht
  let r := n.primeFactors.card
  let s := n.primeFactors
  let X (p : ℕ) := p^(n.factorization p)
  let D (p : ℕ) := a (X p)
  have Cpos : 0 < C := by rw [hC]; positivity
  have Cp : 0 < (C:ℚ) := by exact_mod_cast Cpos
  have hn : 2 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hA : 2 ≤ a n := OMA.R_OeisA224_conjecture_R1.two_le_a n hn
  obtain ⟨k, _, _, _, nonsquare, eqn⟩ := counterexample_quotient n ho hr ht
  have atoms (p : ℕ) (hp : p ∈ s) :
      ∃ u v : ℕ, 0 < v ∧ v ≤ B ∧ (3/2:ℚ) ≤ (X p:ℚ)/D p ∧ (X p:ℚ)/D p ≤ 3 ∧
        (3/2:ℚ) ≤ (u:ℚ)/v ∧ (u:ℚ)/v ≤ 3 ∧ |(X p:ℚ)/D p - (u:ℚ)/v| ≤ 12/(C:ℚ) := by
    have pp := Nat.prime_of_mem_primeFactors hp
    have pd := Nat.dvd_of_mem_primeFactors hp
    have po : Odd p := by
      by_contra! bad
      exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp bad)).trans pd)
    exact atomic_ratios pp po (pp.factorization_pos_of_dvd hn0 pd) hB Cpos
      (hsplit p hp).1 (hsplit p hp).2
  choose u v hv vB flo fhi glo ghi diff using atoms
  let U := ∏ p ∈ s.attach, u p p.property
  let V := ∏ p ∈ s.attach, v p p.property
  let F (p : s) : ℚ := (X p:ℚ)/D p
  let G (p : s) : ℚ := (u p p.property:ℚ)/v p p.property
  have vpos : 0 < V := Finset.prod_pos fun p _ => hv p p.property
  have vbound : V ≤ B^r := by
    simpa only [Finset.prod_const, Finset.card_attach] using
      (Finset.prod_le_prod' (fun p _ => vB p p.property) :
        (∏ p ∈ s.attach, v p p.property) ≤ ∏ _p ∈ s.attach, B)
  have Feq : (∏ p ∈ s.attach, F p) = (n:ℚ)/a n := by
    rw [show (∏ p ∈ s.attach, F p) = ∏ p ∈ s, (X p:ℚ)/D p from Finset.prod_attach s (fun p => (X p:ℚ)/D p)]
    simp only [Finset.prod_div_distrib, ← Nat.cast_prod]
    rw [← prod_counts n hn0]
    congr 2
    exact (Nat.prod_primeFactors_pow_factorization hn0).symm
  have Geq : (∏ p ∈ s.attach, G p) = (U:ℚ)/V := by
    simp only [G, Finset.prod_div_distrib, ← Nat.cast_prod, U, V]
  have fbd : (3/2:ℚ)^r ≤ (n:ℚ)/a n ∧ (n:ℚ)/a n ≤ (3:ℚ)^r := by
    rw [← Feq]
    simpa only [Finset.card_attach] using
      product_bounds s.attach F (fun p _ => ⟨flo p p.property, fhi p p.property⟩)
  have gbd : (3/2:ℚ)^r ≤ (U:ℚ)/V ∧ (U:ℚ)/V ≤ (3:ℚ)^r := by
    rw [← Geq]
    simpa only [Finset.card_attach] using
      product_bounds s.attach G (fun p _ => ⟨glo p p.property, ghi p p.property⟩)
  have err : |(n:ℚ)/a n - (U:ℚ)/V| ≤ (6:ℚ)^r * (12/(C:ℚ)) := by
    rw [← Feq, ← Geq]
    simpa only [Finset.card_attach] using product_approx s.attach F G (12/(C:ℚ))
      (by positivity)
      (fun p _ => ⟨(by norm_num : (0:ℚ) ≤ 3/2).trans (flo p p.property), fhi p p.property⟩)
      (fun p _ => ⟨(by norm_num : (0:ℚ) ≤ 3/2).trans (glo p p.property), ghi p p.property⟩)
      (fun p _ => diff p p.property)
  obtain ⟨_, _, qerr⟩ := quotient_estimate (r := r) hr hnC Cpos hA fbd.1 fbd.2 eqn
  let f : ℚ := (n:ℚ)/a n
  let g : ℚ := (U:ℚ)/V
  have sum0 : 0 ≤ f+g := by positivity
  have sum_bd : f+g ≤ 2*(3:ℚ)^r := by linarith only [fbd.2, gbd.2]
  have square_err : |f^2-g^2| ≤ (24*27^r)/(C:ℚ) := by
    rw [show f^2-g^2=(f-g)*(f+g) by ring, abs_mul, abs_of_nonneg sum0]
    calc
      _ ≤ (6:ℚ)^r * (12/(C:ℚ)) * (2*(3:ℚ)^r) := by
        exact mul_le_mul err sum_bd sum0 (by positivity)
      _ = (24*18^r)/(C:ℚ) := by rw [← show ((6:ℚ)*3)^r = 18^r by norm_num, mul_pow]; ring
      _ ≤ _ := by gcongr; norm_num
  have err_total : |(k:ℚ)-g^2| ≤ (26*27^r)/(C:ℚ) := by
    rw [show (k:ℚ)-g^2=((k:ℚ)-f^2)+(f^2-g^2) by ring]
    exact (abs_add_le _ _).trans ((add_le_add qerr square_err).trans (by ring_nf; rfl))
  have Ceq : (C:ℚ) = 64*(27:ℚ)^r*((B:ℚ)^r)^2 := by
    rw [← pow_mul, Nat.mul_comm r 2]
    exact_mod_cast hC
  have under_one : (26*27^r)/(C:ℚ) < 1/(V:ℚ)^2 := by
    apply (div_lt_div_iff₀ Cp (by positivity)).mpr
    have vb : (V:ℚ) ≤ (B:ℚ)^r := by exact_mod_cast vbound
    have vb2 := pow_le_pow_left₀ (show (0:ℚ) ≤ V by positivity) vb 2
    rw [Ceq, one_mul]
    calc
      _ ≤ (26*(27:ℚ)^r)*((B:ℚ)^r)^2 := mul_le_mul_of_nonneg_left vb2 (by positivity)
      _ < _ := by gcongr; norm_num
  exact nonsquare (nearby_square vpos (err_total.trans_lt under_one))

/-- For a fixed number of distinct prime factors, the possible counterexamples
lie below an explicit bound independent of the primes and their exponents. -/
theorem counterexample_le (n : ℕ) (ho : Odd n) (hr : 3 ≤ n.primeFactors.card)
    (ht : n^2 ≡ 1 [MOD a n*(a n-1)]) :
    let r := n.primeFactors.card
    n ≤ (fun b : ℕ => 64*27^r*b^(2*r))^[2*r+1] 1 := by
  let r := n.primeFactors.card
  let step (b : ℕ) := 64*27^r*b^(2*r)
  let b (i : ℕ) := step^[i] 1
  change n ≤ b (2*r+1)
  by_contra! large
  have b_succ (i : ℕ) : b (i+1) = 64*27^r*(b i)^(2*r) :=
    Function.iterate_succ_apply' step i 1
  have bpos (i : ℕ) : 0 < b i := by
    induction i with
    | zero => exact Nat.one_pos
    | succ i ih => rw [b_succ]; positivity
  have mono : Monotone b := monotone_nat_of_le_succ fun i => by
    rw [b_succ]
    have hpow : b i ≤ (b i)^(2*r) := Nat.le_pow (by
      change 3 ≤ r at hr
      omega)
    exact hpow.trans (Nat.le_mul_of_pos_left _ (by positivity))
  let s := n.primeFactors
  let values := s ∪ s.image (fun p => p^(n.factorization p))
  have hcard : values.card ≤ 2*r := by
    refine (Finset.card_union_le _ _).trans ?_
    have hi : (s.image (fun p => p^(n.factorization p))).card ≤ r := Finset.card_image_le
    have hs : s.card = r := rfl
    omega
  obtain ⟨i, hi, clean⟩ := empty_band values b mono (2*r) hcard
  have hnC : b (i+1) < n := (mono (Nat.succ_le_succ hi)).trans_lt large
  apply band_fails n (b i) (b (i+1)) ho hr (bpos i) (b_succ i) hnC _ ht
  intro p hp
  exact ⟨clean p (mem_union_left _ hp), clean _ (mem_union_right _ (mem_image_of_mem _ hp))⟩

def H1 : Prop :=
  ∀ n k : ℕ, let r := n.primeFactors.card
    Odd n → 3 ≤ r → r ≤ 4 → n ≤ (fun b : ℕ => 64*27^r*b^(2*r))^[2*r+1] 1 →
      4 < k → k ≤ 2*9^r → k < 2*n → ¬ IsSquare k →
      n^2 ≠ a n*(a n-1)*k+1

def H2 : Prop :=
  ∀ n k : ℕ, let r := n.primeFactors.card
    Odd n → 5 ≤ r → n ≤ (fun b : ℕ => 64*27^r*b^(2*r))^[2*r+1] 1 →
      4 < k → k ≤ 2*9^r → k < 2*n → ¬ IsSquare k →
      n^2 ≠ a n*(a n-1)*k+1

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1.H2 := by
  intro hsmall hlarge n ho hr ht
  have hbound := counterexample_le n ho hr ht
  obtain ⟨k, klo, khi, kn, hns, heq⟩ := counterexample_quotient n ho hr ht
  by_cases h : n.primeFactors.card ≤ 4
  · exact hsmall n k ho hr h hbound klo khi kn hns heq
  · exact hlarge n k ho (by omega) hbound klo khi kn hns heq

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R3
