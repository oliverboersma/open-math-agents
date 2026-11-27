import OMAReductions.R_OeisA224_conjecture_R1_H2_R1
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
Ordowski's square-residue test fails on every product of powers of two distinct odd primes.
All positive exponents and all prime bases are covered. The proof combines exact counts,
rational interval bounds, a gap between consecutive squares, and kernel-checked finite tables.

Thomas Ordowski posed the conjecture in https://oeis.org/A000224 in 2017.
The August 2026 agentic-conjectures note covered prime powers and products of two primes.
Daniel Puri's October 2026 report https://aixiv.online/pdf/2610.03026v1 treated p^e q and left
the case with both exponents at least two open. The construction below includes that case.
Credit: @HudZah, with Codex.
-/

open Finset OeisA224

namespace OMA.OrdowskiPairCount

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

private theorem relative_count {p e : ℕ} (hp : p.Prime) (po : Odd p) (big : 201 ≤ p) (he : 0 < e) :
    99 * p^e ≤ 200 * a (p^e) ∧ 200 * a (p^e) ≤ 101 * p^e := by
  have form := count_formula p hp po e
  have ha : 1 ≤ a (p^e) := by
    rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
    exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
  let N := p^e
  let A := a N
  change 99*N ≤ 200*A ∧ 200*A ≤ 101*N
  have small : p ≤ N := Nat.le_pow he
  have hf : 2*(p+1)*A + (if Even e then p else 1) = p*N + 2*(p+1) := by
    change 2*(p+1)*(A-1)+(if Even e then p else 1)=_ at form
    rw [pow_succ, mul_comm (p^e)] at form
    have hA : A-1+1=A := Nat.sub_add_cancel ha
    change 2*(p+1)*(A-1)+(if Even e then p else 1) = p*N at form
    nlinarith only [form, congrArg (fun t => 2*(p+1)*t) hA]
  constructor
  · by_contra! bad
    have hm := Nat.mul_le_mul_left (p+1) (show 200*A+1 ≤ 99*N by omega)
    by_cases ev : Even e <;> simp [ev] at hf <;>
      nlinarith [Nat.mul_le_mul_right N (show 99 ≤ p by omega)]
  · by_contra! bad
    have hm := Nat.mul_le_mul_left (p+1) (show 101*N+1 ≤ 200*A by omega)
    by_cases ev : Even e <;> simp [ev] at hf <;>
      nlinarith only [hm,hf,small,big,Nat.mul_le_mul_right N big]

private theorem no_square16 {n A : ℕ} (ha : 2 ≤ A) : n^2 ≠ 16*(A*(A-1))+1 := by
  intro eq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp at eq
  rcases le_or_gt n (4*k+5) with h | h
  · nlinarith [Nat.pow_le_pow_left h 2]
  · nlinarith [Nat.pow_le_pow_left (show 4*k+6 ≤ n by omega) 2]

theorem large_pair_fails {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) (pb : 201 ≤ p) (qb : 201 ≤ q)
    (he : 0 < e) (hf : 0 < f) :
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f) * (a (p^e*q^f)-1)] := by
  intro test
  obtain ⟨pl, pu⟩ := relative_count hp hpo pb he
  obtain ⟨ql, qu⟩ := relative_count hq hqo qb hf
  let N := p^e*q^f
  let A := a (p^e) * a (q^f)
  have hc := (Nat.coprime_primes hp hq).mpr hne
  rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (pow_pos hp.pos _) (pow_pos hq.pos _) ((hc.pow_left _).pow_right _)] at test
  change N^2 ≡ 1 [MOD A*(A-1)] at test
  have lower : 9801*N ≤ 40000*A := by
    dsimp [N,A]; nlinarith only [Nat.mul_le_mul pl ql]
  have upper : 40000*A ≤ 10201*N := by
    dsimp [N,A]; nlinarith only [Nat.mul_le_mul pu qu]
  have nb : 201*201 ≤ N := Nat.mul_le_mul (pb.trans (Nat.le_pow he)) (qb.trans (Nat.le_pow hf))
  have ab : 9000 ≤ A := by omega
  have ha : A-1+1 = A := by omega
  have hn : 1 ≤ N^2 := by nlinarith
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hn).mp test.symm
  have heq : N^2 = (A*(A-1))*k+1 := by omega
  rcases lt_trichotomy k 16 with h | rfl | h
  · have b := Nat.mul_le_mul_left (A*(A-1)) (show k ≤ 15 by omega)
    nlinarith only [heq,b,Nat.pow_le_pow_left upper 2, congrArg (A * ·) ha, ab, Nat.zero_le (A^2)]
  · exact no_square16 (A:=A) (n:=N) (by omega) (by simpa [mul_comm] using heq)
  · have b := Nat.mul_le_mul_left (A*(A-1)) (show 17 ≤ k by omega)
    have aa := Nat.mul_le_mul_left A ab
    nlinarith only [heq,b,Nat.pow_le_pow_left lower 2, congrArg (A * ·) ha, ab, aa]


end OMA.OrdowskiPairCount

/- Integer interval certificates for the two-prime part of the Ordowski conjecture. -/

open OeisA224
namespace OMA.OrdowskiBoxes

inductive Cell
  | point (p e : ℕ)
  | exponents (p e : ℕ)
  | bases (p : ℕ)

structure Box where
  size : ℕ
  ln : ℕ
  ld : ℕ
  un : ℕ
  ud : ℕ

def correction (p e : ℕ) := if Even e then p+2 else 2*p+1
def count (p e : ℕ) := (p * p^e + correction p e) / (2*(p+1))

def box : Cell → Box
  | .point p e => ⟨p^e, count p e, p^e, count p e, p^e⟩
  | .exponents p e =>
    let b := p^e
    let d := 2*(p+1)
    ⟨b, p, d, p*b+d, d*b⟩
  | .bases p => ⟨p, p, 2*(p+1), p+1, 2*p⟩

def Covers : Cell → ℕ → ℕ → Prop
  | .point r i, p, e => r=p ∧ i=e
  | .exponents r i, p, e => r=p ∧ i≤e
  | .bases r, p, _ => r≤p

def Box.Bounds (b : Box) (n a : ℕ) : Prop :=
  b.size ≤ n ∧ b.ln * n ≤ b.ld * a ∧ b.ud * a ≤ b.un * n

theorem cleared (p e : ℕ) (hp : p.Prime) (hpo : Odd p) :
    2*(p+1)*a (p^e) = p*p^e + correction p e := by
  have h := OMA.OrdowskiPairCount.count_formula p hp hpo e
  have ha : 1 ≤ a (p^e) := by
    rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
    exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
  have restore := congrArg (fun x => 2*(p+1)*x) (Nat.sub_add_cancel ha)
  by_cases hEven : Even e <;> simp only [correction, hEven, if_true, if_false, pow_succ] at * <;> nlinarith only [h, restore]

theorem count_eq (p e : ℕ) (hp : p.Prime) (ho : Odd p) : count p e = a (p^e) := by
  unfold count
  rw [← cleared p e hp ho, Nat.mul_div_cancel_left _ (by positivity)]

theorem cell_bounds (c : Cell) {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hc : Covers c p e) : (box c).Bounds (p^e) (a (p^e)) := by
  have eqn := cleared p e hp ho
  have ck : correction p e ≤ 2*p+1 := by
    unfold correction
    split <;> have := hp.one_lt <;> omega
  have pn : p ≤ p^e := Nat.le_pow he
  cases c with
  | point r i =>
    obtain ⟨rfl,rfl⟩ := hc
    simp [Box.Bounds,box,count_eq r i hp ho,mul_comm]
  | exponents r i =>
    obtain ⟨rfl,hi⟩ := hc
    have hb : r^i ≤ r^e := Nat.pow_le_pow_right hp.pos hi
    refine ⟨hb, by simpa only [box] using (show r*r^e ≤ 2*(r+1)*a (r^e) by omega), ?_⟩
    change 2*(r+1)*r^i*a (r^e) ≤ (r*r^i+2*(r+1))*r^e
    have hmul := Nat.mul_le_mul (show correction r e ≤ 2*(r+1) by omega) hb
    nlinarith only [congrArg (fun x => r^i*x) eqn, hmul]
  | bases r =>
    change r ≤ p at hc
    refine ⟨hc.trans pn, ?_, ?_⟩
    · change r*p^e ≤ 2*(r+1)*a (p^e)
      apply Nat.le_of_mul_le_mul_left (c := p+1) _ (by omega)
      have hmul := Nat.mul_le_mul_right (p^e) hc
      nlinarith only [congrArg (fun x => (r+1)*x) eqn, hmul,
        Nat.zero_le ((r+1)*correction p e)]
    · change 2*r*a (p^e) ≤ (r+1)*p^e
      apply Nat.le_of_mul_le_mul_left (c := p+1) _ (by omega)
      have small := Nat.mul_le_mul_left r ck
      have h1 := Nat.mul_le_mul_left r pn
      have h2 := Nat.mul_le_mul_right (p+1) (hc.trans pn)
      nlinarith only [congrArg (fun x => r*x) eqn, small, h1, h2]

def product (x y : Box) : Box :=
  ⟨x.size*y.size,x.ln*y.ln,x.ld*y.ld,x.un*y.un,x.ud*y.ud⟩

theorem product_bounds {x y : Box} {m b n c : ℕ} (hx : x.Bounds m b) (hy : y.Bounds n c) :
    (product x y).Bounds (m*n) (b*c) := by
  obtain ⟨xm,xl,xu⟩ := hx
  obtain ⟨ym,yl,yu⟩ := hy
  refine ⟨Nat.mul_le_mul xm ym, ?_, ?_⟩
  · simpa only [product,mul_mul_mul_comm] using (Nat.mul_le_mul xl yl)
  · simpa only [product,mul_mul_mul_comm] using (Nat.mul_le_mul xu yu)

theorem impossible_square {n a t k : ℕ} (_hn : 0 < n) (ha : 0 < a)
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

def candidateRoot (j : ℕ) : ℕ :=
  if j ≤ 9 then 3 else if j ≤ 16 then 4 else if j ≤ 25 then 5 else if j ≤ 36 then 6 else 7

def gapCheck (b : Box) : Bool :=
  let d := b.ln*b.size-b.ld
  let v := (b.ld*b.size)^2
  let j := (b.ud^2 + b.un^2-1)/b.un^2
  decide (0<b.ld ∧ 0<b.size ∧ b.ld<b.ln*b.size ∧ 0<j ∧
    (j-1)*b.un^2 < b.ud^2 ∧
    (v ≤ j*d^2 ∨ (v ≤ (j+1)*d^2 ∧ (candidateRoot j)^2=j ∧ 4<j ∧ j<4*b.size+5)))

theorem gap_sound {b : Box} {n a k : ℕ} (hb : b.Bounds n a) (hn : 0 < n)
    (ha : 0 < a) (hk : 0 < k) (eqn : n^2 = a*(a-1)*k+1) (test : gapCheck b) : False := by
  unfold gapCheck at test
  simp only [decide_eq_true_eq] at test
  let j := (b.ud^2+b.un^2-1)/b.un^2
  let d := b.ln*b.size-b.ld
  obtain ⟨ld0,b0,db,j0,cut,endpt⟩ := test
  obtain ⟨mn,lo,hi⟩ := hb
  have ha' := Nat.sub_add_cancel ha
  have hrest := congrArg (fun x => a*x*k) ha'
  have hm : n^2 ≤ k*a^2 := by nlinarith only [eqn,hrest,Nat.mul_pos ha hk]
  have hm' : k*(a-1)^2 < n^2 := by
    nlinarith only [eqn,congrArg (fun x => x*(a-1)*k) ha', Nat.zero_le ((a-1)*k)]
  have below : b.ud^2 ≤ k*b.un^2 := by
    apply Nat.le_of_mul_le_mul_right (c := n^2) _ (by positivity)
    have h1 := Nat.mul_le_mul_left (b.ud^2) hm
    have h2 := Nat.mul_le_mul_left k (Nat.pow_le_pow_left hi 2)
    nlinarith only [h1,h2]
  have hdelta : d*n ≤ (b.ld*b.size)*(a-1) := by
    have dh : d+b.ld=b.ln*b.size := Nat.sub_add_cancel db.le
    nlinarith only [congrArg (fun x => x*n) dh, Nat.mul_le_mul_left b.size lo,
      Nat.mul_le_mul_left b.ld mn, congrArg (fun x => b.ld*b.size*x) ha']
  have above : k*d^2 < (b.ld*b.size)^2 := by
    have h1 := Nat.mul_le_mul_left k (Nat.pow_le_pow_left hdelta 2)
    have h2 := Nat.mul_lt_mul_of_pos_left hm' (show 0 < (b.ld*b.size)^2 by positivity)
    by_contra! bad
    nlinarith only [h1,h2,Nat.mul_le_mul_right (n^2) bad]
  have jk : j ≤ k := by
    by_contra! h
    have hmul := Nat.mul_le_mul_right (b.un^2) (show k ≤ j-1 by omega)
    change (j-1)*b.un^2 < b.ud^2 at cut
    omega
  change (b.ld*b.size)^2 ≤ j*d^2 ∨
    ((b.ld*b.size)^2 ≤ (j+1)*d^2 ∧ (candidateRoot j)^2=j ∧ 4<j ∧ j<4*b.size+5) at endpt
  rcases endpt with h | ⟨h,sq,big,small⟩
  · have := Nat.mul_le_mul_right (d^2) jk
    omega
  · by_cases hkj : k=j
    · subst k
      exact impossible_square hn ha sq big (by omega) eqn
    · have := Nat.mul_le_mul_right (d^2) (show j+1 ≤ k by omega)
      omega


def Impossible (c d : Cell) : Prop :=
  ∀ p q e f : ℕ, p.Prime → q.Prime → p ≠ q → Odd p → Odd q →
    0 < e → 0 < f → Covers c p e → Covers d q f →
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f)*(a (p^e*q^f)-1)]

def exactCheck : Cell → Cell → Bool
  | .point p e, .point q f =>
    let a := count p e * count q f
    decide (¬ (p^e*q^f)^2 ≡ 1 [MOD a*(a-1)])
  | _, _ => false

theorem exact_sound {c d : Cell} (h : exactCheck c d) : Impossible c d := by
  intro p q e f hp hq hn po qo he hf hc hd test
  cases c <;> cases d <;> simp only [exactCheck, Bool.false_eq_true, decide_eq_true_eq] at h
  obtain ⟨rfl,rfl⟩ := hc
  obtain ⟨rfl,rfl⟩ := hd
  rw [count_eq _ _ hp po, count_eq _ _ hq qo] at h
  rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (pow_pos hp.pos _) (pow_pos hq.pos _)
    ((((Nat.coprime_primes hp hq).mpr hn).pow_left _).pow_right _)] at test
  exact h test

theorem interval_sound {c d : Cell} (h : gapCheck (product (box c) (box d))) : Impossible c d := by
  intro p q e f hp hq hn po qo he hf hc hd test
  let n := p^e*q^f
  let A := a (p^e)*a (q^f)
  have hcop := OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (pow_pos hp.pos e) (pow_pos hq.pos f)
    ((((Nat.coprime_primes hp hq).mpr hn).pow_left e).pow_right f)
  rw [hcop] at test
  have nb : 1 < n := (Nat.one_lt_pow he.ne' hp.one_lt).trans_le (Nat.le_mul_of_pos_right _ (pow_pos hq.pos _))
  have ns : 1 < n^2 := Nat.one_lt_pow (by decide) nb
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' ns.le).mp test.symm
  change n^2-1 = A*(A-1)*k at hk
  have eqn : n^2 = A*(A-1)*k+1 := by omega
  have kpos : 0 < k := by
    by_contra! hk0
    rw [show k=0 by omega] at eqn
    simp only [Nat.mul_zero,Nat.zero_add] at eqn
    omega
  have apos : 0 < A := by
    by_contra! ha0
    rw [show A=0 by omega] at eqn
    simp only [Nat.zero_mul,Nat.zero_add] at eqn
    omega
  exact gap_sound (product_bounds (cell_bounds c hp po he hc) (cell_bounds d hq qo hf hd))
    (by omega : 0<n) apos kpos eqn h

def leaf (c d : Cell) := exactCheck c d || gapCheck (product (box c) (box d))

theorem leaf_sound {c d : Cell} (h : leaf c d) : Impossible c d := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact exact_sound h
  · exact interval_sound h

def splitLeft (step : Cell → Cell → Bool) : Cell → Cell → Bool
  | .exponents p e, d => step (.point p e) d && step (.exponents p (e+1)) d
  | _, _ => false

def splitRight (step : Cell → Cell → Bool) : Cell → Cell → Bool
  | c, .exponents p e => step c (.point p e) && step c (.exponents p (e+1))
  | _, _ => false

def preferLeft : Cell → Cell → Bool
  | .exponents p e, .exponents q f => decide (p^e ≤ q^f)
  | .exponents _ _, _ => true
  | _, _ => false

def check : ℕ → Cell → Cell → Bool
  | 0, c, d => leaf c d
  | t+1, c, d =>
    if leaf c d then true else if preferLeft c d then splitLeft (check t) c d else splitRight (check t) c d

theorem check_sound (t : ℕ) (c d : Cell) (h : check t c d) : Impossible c d := by
  induction t generalizing c d with
  | zero => exact leaf_sound h
  | succ t ih =>
    by_cases hl : leaf c d
    · exact leaf_sound hl
    simp only [check,hl, Bool.false_eq_true, if_false] at h
    split at h
    · cases c <;> simp only [splitLeft,Bool.false_eq_true,Bool.and_eq_true] at h
      rename_i r i _side
      intro p q e f hp hq hn po qo he hf hc hd
      obtain ⟨rfl,hi⟩ := hc
      by_cases eq : i=e
      · exact ih _ _ h.1 _ _ _ _ hp hq hn po qo he hf ⟨rfl,eq⟩ hd
      · exact ih _ _ h.2 _ _ _ _ hp hq hn po qo he hf ⟨rfl,by omega⟩ hd
    · cases d <;> simp only [splitRight,Bool.false_eq_true,Bool.and_eq_true] at h
      rename_i r i _side
      intro p q e f hp hq hn po qo he hf hc hd
      obtain ⟨rfl,hi⟩ := hd
      by_cases eq : i=f
      · exact ih _ _ h.1 _ _ _ _ hp hq hn po qo he hf hc ⟨rfl,eq⟩
      · exact ih _ _ h.2 _ _ _ _ hp hq hn po qo he hf hc ⟨rfl,by omega⟩


-- These thresholds give one interval for every larger second prime.
def threshold : ℕ → ℕ
  | 3 | 7 | 17 | 29 => 807
  | 5 => 6463
  | 11 | 31 => 3231
  | 37 => 403
  | _ => 201

-- Every odd prime passes these trial divisions. The argument needs only this direction.
def passes (n : ℕ) : Bool :=
  decide (3 ≤ n) && [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79].all
    (fun t => decide (t ≤ 1 ∨ n ≤ t ∨ n % t ≠ 0))

theorem prime_passes {n : ℕ} (hp : n.Prime) (ho : Odd n) : passes n = true := by
  have ge := hp.two_le
  have h3 : 3 ≤ n := by obtain ⟨k,hk⟩ := ho; omega
  simp only [passes,h3,decide_true,Bool.true_and,List.all_eq_true]
  intro t _
  rw [decide_eq_true_eq]
  by_contra! h
  have hh := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h.2.2)
  omega

def baseCheck (p q : ℕ) : Bool :=
  if p < q ∧ passes q = true then check 16 (.exponents p 1) (.exponents q 1) else true

def Block (p start width : ℕ) : Prop :=
  ∀ q, start ≤ q → q < start + width → p < q → passes q = true →
    check 16 (.exponents p 1) (.exponents q 1) = true

def table (p start width : ℕ) : ℕ → Prop
  | 0 => (List.range width).all (fun i => baseCheck p (start+i)) = true
  | d+1 => table p start (width/2) d ∧ table p (start+width/2) (width-width/2) d

theorem table_sound (d p start width : ℕ) (h : table p start width d) : Block p start width := by
  induction d generalizing start width with
  | zero =>
    intro q hlo hhi hp hq
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hlo
    have hh := List.all_eq_true.mp h i (List.mem_range.mpr (by omega))
    simpa only [baseCheck,hp,hq,and_self,if_true] using hh
  | succ d ih =>
    intro q hlo hhi hp hq
    by_cases low : q < start + width / 2
    · exact ih _ _ h.1 q hlo low hp hq
    · exact ih _ _ h.2 q (by omega) (by omega) hp hq

def Row (p : ℕ) : Prop :=
  check 16 (.exponents p 1) (.bases (threshold p)) = true ∧ Block p 0 (threshold p)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row3 : Row 3 := by
  refine ⟨by decide +kernel, table_sound 5 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row5 : Row 5 := by
  refine ⟨by decide +kernel, table_sound 8 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row7 : Row 7 := by
  refine ⟨by decide +kernel, table_sound 5 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row11 : Row 11 := by
  refine ⟨by decide +kernel, table_sound 7 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row13 : Row 13 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row17 : Row 17 := by
  refine ⟨by decide +kernel, table_sound 5 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row19 : Row 19 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row23 : Row 23 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row29 : Row 29 := by
  refine ⟨by decide +kernel, table_sound 5 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row31 : Row 31 := by
  refine ⟨by decide +kernel, table_sound 7 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row37 : Row 37 := by
  refine ⟨by decide +kernel, table_sound 4 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row41 : Row 41 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row43 : Row 43 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row47 : Row 47 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row53 : Row 53 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row59 : Row 59 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row61 : Row 61 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row67 : Row 67 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row71 : Row 71 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row73 : Row 73 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row79 : Row 79 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row83 : Row 83 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row89 : Row 89 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row97 : Row 97 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row101 : Row 101 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row103 : Row 103 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row107 : Row 107 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row109 : Row 109 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row113 : Row 113 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row127 : Row 127 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row131 : Row 131 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row137 : Row 137 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row139 : Row 139 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row149 : Row 149 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row151 : Row 151 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row157 : Row 157 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row163 : Row 163 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row167 : Row 167 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row173 : Row 173 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row179 : Row 179 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row181 : Row 181 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row191 : Row 191 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row193 : Row 193 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row197 : Row 197 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem row199 : Row 199 := by
  refine ⟨by decide +kernel, table_sound 3 _ _ _ ?_⟩
  simp only [table]
  repeat' apply And.intro
  all_goals decide +kernel

def smallPrimes : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]

theorem smallRows (p : ℕ) (pb : p < 201) (hp : p.Prime) (po : Odd p) : Row p := by
  have enumerated : (List.range 201).all (fun i => !passes i || smallPrimes.contains i) = true := by
    decide +kernel
  have hm := List.all_eq_true.mp enumerated p (List.mem_range.mpr pb)
  simp only [prime_passes hp po,Bool.not_true,Bool.false_or,List.contains_iff_mem] at hm
  simp only [smallPrimes,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3
  · exact row5
  · exact row7
  · exact row11
  · exact row13
  · exact row17
  · exact row19
  · exact row23
  · exact row29
  · exact row31
  · exact row37
  · exact row41
  · exact row43
  · exact row47
  · exact row53
  · exact row59
  · exact row61
  · exact row67
  · exact row71
  · exact row73
  · exact row79
  · exact row83
  · exact row89
  · exact row97
  · exact row101
  · exact row103
  · exact row107
  · exact row109
  · exact row113
  · exact row127
  · exact row131
  · exact row137
  · exact row139
  · exact row149
  · exact row151
  · exact row157
  · exact row163
  · exact row167
  · exact row173
  · exact row179
  · exact row181
  · exact row191
  · exact row193
  · exact row197
  · exact row199

theorem small_first {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : Odd p) (qo : Odd q)
    (pq : p<q) (pb : p<201) (he : 0<e) (hf : 0<f) :
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f)*(a (p^e*q^f)-1)] := by
  have hpcheck := smallRows p pb hp po
  by_cases qb : q < threshold p
  · have hqcheck := hpcheck.2 q (Nat.zero_le _) (by simpa using qb) pq (prime_passes hq qo)
    exact check_sound 16 _ _ hqcheck p q e f hp hq pq.ne po qo he hf ⟨rfl,he⟩ ⟨rfl,hf⟩
  · exact check_sound 16 _ _ hpcheck.1 p q e f hp hq pq.ne po qo he hf ⟨rfl,he⟩ (by
      change threshold p ≤ q
      omega)

theorem two_prime_factors {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : Odd p) (qo : Odd q)
    (hne : p≠q) (he : 0<e) (hf : 0<f) :
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f)*(a (p^e*q^f)-1)] := by
  have ord {x y i j : ℕ} (hx : x.Prime) (hy : y.Prime) (ox : Odd x) (oy : Odd y)
      (xy : x<y) (hi : 0 < i) (hj : 0 < j) :
      ¬ (x^i*y^j)^2 ≡ 1 [MOD a (x^i*y^j)*(a (x^i*y^j)-1)] := by
    by_cases xs : x<201
    · exact small_first hx hy ox oy xy xs hi hj
    · exact OMA.OrdowskiPairCount.large_pair_fails hx hy ox oy xy.ne
        (by omega) (by omega) hi hj
  rcases lt_or_gt_of_ne hne with h | h
  · exact ord hp hq po qo h he hf
  · simpa only [mul_comm (q^f) (p^e)] using ord hq hp qo po h hf he

end OMA.OrdowskiBoxes

theorem OMA.solution : OMA.R_OeisA224_conjecture_R1_H2_R1.H1 := by
  intro p q e f hp hq hne po qo he hf _
  exact OMA.OrdowskiBoxes.two_prime_factors hp hq po qo hne he hf
