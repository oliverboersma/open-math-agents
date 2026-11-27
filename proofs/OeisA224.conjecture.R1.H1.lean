import OMAReductions.R_OeisA224_conjecture_R1
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
Square residues modulo powers of odd primes.
Credit: @HudZah

Separate the unit squares from the multiples of the square of the prime.
For odd exponent the test would force its modulus factor to divide a smaller
positive integer. For even exponent the prime itself obstructs the test.
-/

open Finset OeisA224

namespace OMA.PowerCount

private def residues (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun k => k^2 % n)

private theorem mem_res {n r : ℕ} (hn : 0 < n) :
    r ∈ residues n ↔ ∃ k : ℕ, k^2 % n = r := by
  constructor
  · intro hr
    obtain ⟨k, _, h⟩ := Finset.mem_image.mp hr
    exact ⟨k, h⟩
  · rintro ⟨k, rfl⟩
    exact Finset.mem_image.mpr ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt _ hn), (Nat.pow_mod ..).symm⟩

private noncomputable def unitSq (n : ℕ) [NeZero n] : Finset ℕ := by
  classical
  exact Finset.univ.image (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
    (u.val.val).val)

private theorem mem_unitSq {n x : ℕ} [NeZero n] :
    x ∈ unitSq n ↔ ∃ u : (ZMod n)ˣ, ((u : ZMod n)^2).val = x := by
  classical
  constructor
  · intro hx
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv⟩ := u.property
    exact ⟨v, by simpa [← hv] using hu⟩
  · rintro ⟨u, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨u ^ 2, u, rfl⟩, Finset.mem_univ _, rfl⟩

private theorem unitSq_card (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] (hn : 2 < n) :
    (unitSq n).card = n.totient / 2 := by
  classical
  unfold unitSq
  have hi : Function.Injective (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
      u.val.val.val) := fun _ _ h => Subtype.ext (Units.ext (ZMod.val_injective n h))
  rw [Finset.card_image_of_injective _ hi, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.gcd_eq_right (even_iff_two_dvd.mp (Nat.totient_even hn))]

theorem count_step (p e : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    a (p^(e+2)) = a (p^e) + (p^(e+1)*(p-1))/2 := by
  classical
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
  have hcard : (residues (p^e)).card = a (p^e) := by rw [a, if_neg (pow_ne_zero _ hp.ne_zero)]; rfl
  change a N = _
  rw [a, if_neg hn0.ne']
  change (residues N).card = _
  rw [split, Finset.card_union_of_disjoint disj, hcnt]
  dsimp only [M]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h), hcard]
  dsimp only [N]
  rw [Nat.totient_prime_pow_succ hp]

theorem prime_count {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : a p = p / 2 + 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hop := hp.odd_of_ne_two hodd
  let sq := fun k : ℕ => k^2 % p
  have inj : Set.InjOn sq (Finset.range (p / 2 + 1) : Set ℕ) := by
    intro x hx y hy hxy
    have hxt : x < p / 2 + 1 := Finset.mem_range.mp hx
    have hyt : y < p / 2 + 1 := Finset.mem_range.mp hy
    have hpodd := Nat.odd_iff.mp hop
    have hxp : x < p := by omega
    have hyp : y < p := by omega
    have hsq : (x : ZMod p)^2 = (y : ZMod p)^2 := by
      simpa using (ZMod.natCast_eq_natCast_iff' _ _ p).mpr hxy
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hxp, Nat.mod_eq_of_lt hyp] using congrArg ZMod.val h
    · have hz : ((x + y : ℕ) : ZMod p) = 0 := by simp [h]
      have hmod : (x + y) % p = 0 := Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hz)
      rw [Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  have himage : (Finset.range p).image sq = (Finset.range (p / 2 + 1)).image sq := by
    apply Finset.Subset.antisymm
    · intro r hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      have hkp := Finset.mem_range.mp hk
      by_cases hsmall : k < p / 2 + 1
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hsmall, rfl⟩
      refine Finset.mem_image.mpr ⟨p-k, Finset.mem_range.mpr (by omega), ?_⟩
      apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
      push_cast [Nat.cast_sub (le_of_lt hkp)]
      simp
    · apply Finset.image_subset_image
      apply Finset.range_mono
      have := hp.two_le
      omega
  change (if p = 0 then 1 else ((Finset.range p).image sq).card) = _
  rw [if_neg hp.ne_zero, himage, Finset.card_image_of_injOn inj, Finset.card_range]


theorem count_formula (p : ℕ) (hp : p.Prime) (po : Odd p) (e : ℕ) :
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

theorem reject_power {p e : ℕ} (hp : p.Prime) (po : Odd p) (he : 2 ≤ e)
    (test : (p^e)^2 ≡ 1 [MOD a (p^e) * (a (p^e) - 1)]) : False := by
  let d := a (p^e) - 1
  have testD : (p^e)^2 ≡ 1 [MOD d] := test.of_mul_left _
  have form := count_formula p hp po e
  change 2 * (p + 1) * d + (if Even e then p else 1) = p^(e+1) at form
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (by intro h; subst p; norm_num at po)
  by_cases ev : Even e
  · rw [if_pos ev] at form
    have pdiv : p ∣ 2 * (p+1) * d := by
      apply (Nat.dvd_add_iff_left (dvd_refl p)).mpr
      rw [form]
      exact dvd_pow_self _ (by omega)
    have pd : p ∣ d := by
      rcases hp.dvd_mul.mp pdiv with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact (not_le.mpr hp2 (Nat.le_of_dvd (by decide) h)).elim
        · have : p ∣ 1 := by simpa using (Nat.dvd_sub h (dvd_refl p))
          exact (hp.not_dvd_one this).elim
      · exact h
    have zero : (p^e)^2 ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr ((dvd_pow_self p (by omega : e ≠ 0)).trans (dvd_pow_self _ (by decide)))
    have bad : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp ((testD.of_dvd pd).symm.trans zero)
    exact hp.not_dvd_one bad
  · rw [if_neg ev] at form
    have he3 : 3 ≤ e := by
      by_contra! h
      have : e = 2 := by omega
      simp_all
    have hp4 : p^4 ≤ p^(e+1) := Nat.pow_le_pow_right hp.pos (by omega)
    have hd : p^2 < d := by
      by_contra! h
      have b := Nat.mul_le_mul_left (2*(p+1)) h
      have strict : 2*(p+1)*p^2+1 < p^4 := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 3 ≤ p by omega)
        rw [hk]
        nlinarith only [Nat.zero_le k, Nat.zero_le (k^2), Nat.zero_le (k^3), Nat.zero_le (k^4)]
      omega
    have r : (p^e * p) ≡ 1 [MOD d] := by
      rw [← pow_succ, ← form]
      simp [Nat.ModEq, Nat.add_mod]
    have r2 := r.pow 2
    have te := testD.mul_right (p^2)
    have eq : p^2 ≡ 1 [MOD d] := by
      simpa [mul_pow] using te.symm.trans (by simpa [mul_pow] using r2)
    change p^2 % d = 1 % d at eq
    have hpSq : 1 < p^2 := by nlinarith
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt (by omega)] at eq
    omega


end OMA.PowerCount

theorem OMA.solution : OMA.R_OeisA224_conjecture_R1.H1 := by
  intro p e hp hne he test
  exact OMA.PowerCount.reject_power hp (hp.odd_of_ne_two hne) he test
