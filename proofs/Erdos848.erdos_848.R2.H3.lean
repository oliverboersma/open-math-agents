import OMAReductions.R_Erdos848_erdos_848_R2
import Mathlib

/-! # The asymptotic bound for squarefree products

Sawhney's stability theorem implies the conjectured bound for every sufficiently
large N. This port adapts Raymond Jung's Apache-2.0 Lean formalization, with
the original contributors Claude Opus 4.5, GPT-5.2 Pro/xHigh, Gemini 3.0 and
Aristotle. Source: https://github.com/The-Obstacle-Is-The-Way/erdos-banger
at 1cc2ac8e9d70516e979733c6ea5c4d2eb652d1f5, formal/lean/Erdos/848.lean.
Port, certified finite prime sums, elementary large-prime estimates, and optimized
stability parameters by @Deldor14. For p>N/10000 we bound the possible square divisors using the gap between
solutions to a Pell equation or the Vandermonde determinant for three distinct roots.
The diagonal sieve counts the two opposite
roots together; when p² ≥ 2N, at most one lies in [0,N). With δ = 1/2300,
the critical density is at most 46/1795 + 326/25000 + 3δ + 1/10000000.
-/
open scoped BigOperators

open scoped Finset

open scoped Nat.Prime

namespace Erdos848Gap

/-- Two different positive solutions of x² + 1 = d p² cannot have
their p-coordinates in the same multiplicative interval [p,2p]. -/
theorem diagonal_gap {d n m p q : ℕ} (pp : 2 ≤ p) (pq : p < q) (narrow : q ≤ 2*p)
    (hn : n^2+1=d*p^2) (hm : m^2+1=d*q^2) : False := by
  have dp : 0 < d := by
    cases d with
    | zero => simp at hn
    | succ d => omega
  have coord {k t : ℕ} (hk : 2 ≤ k) (eq : t^2+1=d*k^2) : k ≤ t := by
    have pd : k^2 ≤ d*k^2 := by simpa using Nat.mul_le_mul_right (k^2) dp
    have sq2 : 4 ≤ k^2 := Nat.pow_le_pow_left hk 2
    have pos : 0 < t := by
      cases t with
      | zero => simp at eq; omega
      | succ t => omega
    by_contra! h
    have sq := Nat.pow_le_pow_left (show t+1 ≤ k by omega) 2
    nlinarith only [sq,pd,eq,pos]
  have pm := coord pp hn
  have prod : (m*p)^2+ p^2 = (n*q)^2+ q^2 := by
    have a := congrArg (· * p^2) hm
    have b := congrArg (· * q^2) hn
    nlinarith only [a,b]
  have sq_lt := Nat.pow_lt_pow_left pq (by decide : 2 ≠ 0)
  have det : n*q < m*p := by
    by_contra! h
    have leq := Nat.pow_le_pow_left h 2
    omega
  have detsq := Nat.pow_le_pow_left (show n*q + 1 ≤ m*p by omega) 2
  have hmul := Nat.mul_le_mul_right q pm
  have qt := Nat.mul_le_mul_right q narrow
  nlinarith only [detsq,prod,qt,hmul]

private theorem count_keys (S : Finset ℕ) (key : ℕ → ℕ × ℕ) (cols rows : ℕ)
    (bound : ∀ n∈S, (key n).1 < cols ∧ (key n).2 < rows) (injective : Set.InjOn key S) :
    S.card ≤ cols*rows := by
  let labels := (Finset.range cols) ×ˢ (Finset.range rows)
  have maps : (S : Set ℕ).MapsTo key labels := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (bound n hn).1,Finset.mem_range.mpr (bound n hn).2⟩
  simpa [labels] using Finset.card_le_card_of_injOn key maps injective

/-- For p>N/10000 the quotient is below 10⁸, and the block index
⌊10000p/N⌋ is at most 10000. The gap lemma makes this key injective. -/
theorem large_diagonal {N : ℕ} (big : 10^45 ≤ N) (S : Finset ℕ)
    (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 10000*p ∧ p^2 ∣ n^2+1) :
    4000*S.card ≤ N := by
  classical
  let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
  let d (n : ℕ) := (n^2+1)/(p n)^2
  have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 10000*p n ∧ (p n)^2 ∣ n^2+1 := by
    simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
  have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = n^2+1 := Nat.div_mul_cancel (info n hn).2.2
  have divisorBound (n : ℕ) (hn : n∈S) : d n < 100000000 := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right ((p n)^2) h
    have h2 := Nat.pow_lt_pow_left (choosePrime n hn).1 (by decide : 2≠0)
    have h3 := Nat.pow_lt_pow_left (info n hn).2.1 (by decide : 2≠0)
    nlinarith only [h1,eq n hn,h2,h3]
  let key (n : ℕ) := (d n,(10000*p n)/N)
  have positive : 0 < N := by norm_num at big; omega
  have labels (n : ℕ) (hn : n∈S) : (key n).1 < 100000000 ∧ (key n).2 < 10001 := by
    refine ⟨divisorBound n hn,?_⟩
    change 10000*p n/N < 10001
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    have m := (info n hn).1
    omega
  have pair {x y : ℕ} (hx : x∈S) (hy : y∈S) (k : key x=key y) (lt : p x < p y) : False := by
    have de := congrArg Prod.fst k
    change d x = d y at de
    have label := congrArg Prod.snd k
    change 10000*p x/N = 10000*p y/N at label
    have rx := Nat.mod_add_div (10000*p x) N
    have ry := Nat.mod_add_div (10000*p y) N
    have upper := Nat.mod_lt (10000*p y) positive
    rw [label] at rx
    have lox := (info x hx).2.1
    norm_num at big
    have sm : 2 ≤ p x := by omega
    have gap : p y ≤ 2*p x := by omega
    exact diagonal_gap sm lt gap (eq x hx).symm (de ▸ (eq y hy).symm)
  have inj : Set.InjOn key S := by
    intro x hx y hy hk
    rcases lt_trichotomy (p x) (p y) with h | h | h
    · exact (pair hx hy hk h).elim
    · have de := congrArg Prod.fst hk
      change d x = d y at de
      have xx := eq x hx
      have yy := eq y hy
      rw [de,h] at xx
      have sq : x^2=y^2 := by omega
      exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp sq
    · exact (pair hy hx hk.symm h).elim
  have bound := count_keys S key 100000000 10001 labels inj
  norm_num at big
  omega

end Erdos848Gap

namespace Erdos848Gap

/-- Three equal quadratic residues in an interval shorter than the cube root
of the modulus contradict the divisibility of their Vandermonde product. -/
theorem mixed_gap {b d H x y z n m l : ℕ} (xy : x < y) (yz : y < z) (close : z < x+H)
    (large : H^3 ≤ b) (hx : d*x^2=b*n+1) (hy : d*y^2=b*m+1) (hz : d*z^2=b*l+1) :
    False := by
  have root (u t : ℕ) (h : d*u^2=b*t+1) : (d:ZMod b)*(u:ZMod b)^2=1 := by
    have same := congrArg (fun j : ℕ => (j:ZMod b)) h
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,
      ZMod.natCast_self,zero_mul,zero_add] using same
  have X := root x n hx
  have Y := root y m hy
  have Z := root z l hz
  have eqsq (u : ZMod b) (h : (d:ZMod b)*u^2=1) : u^2=(x:ZMod b)^2 := by
    calc u^2 = ((d:ZMod b)*(x:ZMod b)^2)*u^2 := by rw [X,one_mul]
         _ = ((d:ZMod b)*u^2)*(x:ZMod b)^2 := by ring
         _ = (x:ZMod b)^2 := by rw [h,one_mul]
  have V : ((y:ZMod b)-x)*(z-x)*(z-y) = 0 := by
    calc _ = ((y:ZMod b)-x)*((z:ZMod b)^2-(x:ZMod b)^2) -
               ((z:ZMod b)-x)*((y:ZMod b)^2-(x:ZMod b)^2) := by ring
         _ = 0 := by rw [eqsq _ Y,eqsq _ Z]; ring
  have dvd : b ∣ (y-x)*(z-x)*(z-y) := by
    apply (ZMod.natCast_eq_zero_iff _ b).mp
    simpa only [Nat.cast_mul,Nat.cast_sub xy.le,Nat.cast_sub (xy.trans yz).le,Nat.cast_sub yz.le] using V
  have a : 0 < y-x := by omega
  have c : 0 < z-x := by omega
  have e : 0 < z-y := by omega
  have prodpos : 0 < (y-x)*(z-x)*(z-y) := Nat.mul_pos (Nat.mul_pos a c) e
  have h1 : (y-x)*(z-x) < H*H := Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
  have h2 : (y-x)*(z-x)*(z-y) < (H*H)*H := Nat.mul_lt_mul_of_lt_of_lt h1 (by omega)
  rw [show H*H*H=H^3 by ring] at h2
  exact (not_lt_of_ge (Nat.le_of_dvd prodpos dvd)) (h2.trans_le large)

/-- Count large linear-product exceptions, indexed by their quotient and by
a short interval of the square divisor's base. -/
theorem count_mixed {N b H D : ℕ} (bpos : 0 < b) (hpos : 0 < H) (large : H^3 ≤ b)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n ∈ S, d n*(p n)^2=b*n+1)
    (pr : ∀ n ∈ S, p n ≤ N) (dr : ∀ n ∈ S, d n < D) :
    S.card ≤ 2*D*(N/H+1) := by
  classical
  let key (n : ℕ) := (d n,p n/H)
  let labels := (Finset.range D).product (Finset.range (N/H+1))
  have maps : (S : Set ℕ).MapsTo key labels := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (dr n hn),
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (pr n hn)))⟩
  have close {i j : ℕ} (h : i/H=j/H) : j < i+H := by
    have m := Nat.mod_lt j hpos
    have qi := Nat.mod_add_div i H
    have qj := Nat.mod_add_div j H
    rw [h] at qi
    omega
  have per (label : ℕ × ℕ) : (S.filter (fun n => key n=label)).card ≤ 2 := by
    by_contra! high
    obtain ⟨i,j,k,hi,hj,hk,ij,ik,jk⟩ := Finset.two_lt_card_iff.mp high
    have data (x : ℕ) (hx : x∈S.filter (fun n => key n=label)) :
        label.1*(p x)^2 = b*x+1 ∧ p x/H=label.2 := by
      obtain ⟨xs,keyEq⟩ := Finset.mem_filter.mp hx
      have e := congrArg Prod.fst keyEq
      change d x = label.1 at e
      exact ⟨e ▸ eq x xs,congrArg Prod.snd keyEq⟩
    have impossible {x y z : ℕ}
        (hx : x∈S.filter (fun n => key n=label))
        (hy : y∈S.filter (fun n => key n=label))
        (hz : z∈S.filter (fun n => key n=label)) :
        p x < p y → p y < p z → False := by
      obtain ⟨xe,xkey⟩ := data x hx
      obtain ⟨ye,_⟩ := data y hy
      obtain ⟨ze,zkey⟩ := data z hz
      intro xy yz
      exact mixed_gap xy yz (close (xkey.trans zkey.symm)) large xe ye ze
    have dif {x y : ℕ} (hx : x∈S.filter (fun n => key n=label))
        (hy : y∈S.filter (fun n => key n=label)) (hxy : x≠y) : p x ≠ p y := by
      intro e
      have xx := (data x hx).1
      have yy := (data y hy).1
      rw [e] at xx
      exact hxy (Nat.eq_of_mul_eq_mul_left bpos (by omega))
    have eij := dif hi hj ij
    have eik := dif hi hk ik
    have ejk := dif hj hk jk
    have a := impossible hi hj hk
    have c := impossible hi hk hj
    have e := impossible hj hi hk
    have f := impossible hj hk hi
    have g := impossible hk hi hj
    have h := impossible hk hj hi
    rcases lt_or_gt_of_ne eij with less | more <;>
      rcases lt_or_gt_of_ne eik with less' | more' <;>
      rcases lt_or_gt_of_ne ejk with less'' | more'' <;>
      first | exact a (by omega) (by omega) | exact c (by omega) (by omega) |
        exact e (by omega) (by omega) | exact f (by omega) (by omega) |
        exact g (by omega) (by omega) | exact h (by omega) (by omega)
  rw [Finset.card_eq_sum_card_fiberwise maps]
  calc ∑ z ∈ labels, (S.filter (fun n => key n = z)).card ≤ ∑ _ ∈ labels, 2 :=
         Finset.sum_le_sum (fun z _ => per z)
       _ = _ := by simp [labels]; ring

/-- Beyond N/10000 the linear sieve has few exceptional n. A large square
factor fixes a quotient below 10⁸; Vandermonde gives two solutions per
quotient and 10¹²-term window. -/
theorem large_mixed {N b : ℕ} (big : 10^45 ≤ N) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 10000*p ∧ p^2 ∣ b*n+1) :
    4000*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 10000*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have root (n : ℕ) (hn : n∈S) :
        N^2 < 100000000*(p n)^2 := by
      have sq := Nat.pow_lt_pow_left (info n hn).2.1 (by decide : 2≠0)
      nlinarith only [sq]
    have divisorBound (n : ℕ) (hn : n∈S) : d n < 100000000 := by
      by_contra! h
      have h1 := Nat.mul_le_mul_right ((p n)^2) h
      have h2 := Nat.mul_le_mul_right N bN.le
      nlinarith only [h1,eq n hn,bound n hn,h2,root n hn]
    have large : 1000000000000^3 ≤ b := by
      have dv := (info v hv).2.2
      have h1 := Nat.le_of_dvd (Nat.succ_pos _) dv
      have base : (p v)^2 ≤ b*N := h1.trans (bound v hv)
      have h2 := Nat.mul_le_mul_left 100000000 base
      have h3 : N*N < (100000000*b)*N := by nlinarith only [root v hv,h2]
      have h4 : N < 100000000*b := Nat.lt_of_mul_lt_mul_right h3
      norm_num at big ⊢
      omega
    have count := count_mixed (H := 1000000000000) (D := 100000000) bp
      (by decide) large S p d eq (fun n hn => (info n hn).1) divisorBound
    norm_num at big
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp


end Erdos848Gap

namespace Erdos848Port

def NonSquarefreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

def A₇ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 7)

def A₁₈ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 18)

lemma dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv
    {p a b : ℕ} (hp : Nat.Prime p) (ha : ¬p ∣ a) :
    p ^ 2 ∣ (a * b + 1) ↔ (b : ZMod (p ^ 2)) = -((a : ZMod (p ^ 2))⁻¹) := by
  set n : ℕ := p ^ 2
  have hcop : Nat.Coprime a n := by
    simpa [n] using hp.coprime_pow_of_not_dvd (m := 2) ha
  have haUnit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).2 hcop
  constructor
  · intro hdiv
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff (a * b + 1) n).2 hdiv
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz
    have hprod : (a : ZMod n) * (b : ZMod n) = (-1 : ZMod n) := by
      simpa using (eq_neg_of_add_eq_zero_left hz')
    have hb : (b : ZMod n) = (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
      have hb0 := congrArg (fun x : ZMod n => (a : ZMod n)⁻¹ * x) hprod
      have hb1 :
          ((a : ZMod n)⁻¹ * (a : ZMod n)) * (b : ZMod n) =
            (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
        simpa [mul_assoc] using hb0
      simpa [ZMod.inv_mul_of_unit (a : ZMod n) haUnit] using hb1
    simpa [n, mul_comm, mul_left_comm, mul_assoc] using hb
  · intro hb
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simp [hb, ZMod.mul_inv_of_unit (a : ZMod n) haUnit]
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz'
    exact (ZMod.natCast_eq_zero_iff (a * b + 1) n).1 hz

lemma prime_sq_divides_implies_one_mod_four (p n : ℕ) (hp : Nat.Prime p) (hp2 : p > 2)
    (hdiv : p ^ 2 ∣ n ^ 2 + 1) : p % 4 = 1 := by
  have hp_ne_two : p ≠ 2 := by omega
  have hp_dvd : p ∣ n ^ 2 + 1 := by
    have hp_div_p2 : p ∣ p ^ 2 := by simp [pow_two]
    exact Nat.dvd_trans hp_div_p2 hdiv
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hp_dvd
  have hsq : (n : ZMod p) ^ 2 = (-1 : ZMod p) := by
    have : (n : ZMod p) ^ 2 + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
    simpa using (eq_neg_of_add_eq_zero_left this)
  have hne3 : p % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := p) (y := (n : ZMod p)) hsq
  have hp_mod2 : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp_ne_two
  have hp_mod4 : p % 4 = 1 ∨ p % 4 = 3 := (Nat.odd_mod_four_iff).1 hp_mod2
  cases hp_mod4 with
  | inl h1 => exact h1
  | inr h3 => exact (hne3 h3).elim

lemma two_roots_mod_p_squared (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    ∃ r₁ r₂ : ZMod (p ^ 2),
      r₂ = -r₁ ∧ r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧
        ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ZMod (p ^ 2), r₁ ^ 2 = -1 := by
    have h_quad_res : ∃ x : ℕ, x ^ 2 ≡ -1 [ZMOD p ^ 2] := by
      have h_hensel : ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 → ∃ x : ℕ, x ^ 2 ≡ -1 [ZMOD p] := by
        intro p hp hmod
        have := Fact.mk hp
        norm_num [← ZMod.intCast_eq_intCast_iff]
        obtain ⟨x, hx⟩ := ZMod.exists_sq_eq_neg_one_iff (p := p)
        exact Exists.elim (hx (by rw [hmod]; decide)) fun x hx =>
          ⟨x.val, by simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm⟩
      obtain ⟨x, hx⟩ := @h_hensel p hp hmod
      obtain ⟨k, hk⟩ : ∃ k : ℤ, x ^ 2 = k * p - 1 := by
        exact hx.symm.dvd.imp fun k hk => by linarith
      obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * x * y ≡ -k [ZMOD p] := by
        obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * x * y ≡ 1 [ZMOD p] := by
          have h_inv : Int.gcd (2 * x) p = 1 := by
            refine' Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr _)
            norm_num [Int.natAbs_mul, Nat.Prime.dvd_mul hp]
            exact
              ⟨Nat.not_dvd_of_pos_of_lt (by norm_num) (by
                    contrapose! hmod
                    interval_cases p <;> trivial),
                fun h => by
                  have :=
                    Int.modEq_zero_iff_dvd.mp
                      (hx.symm.trans
                        (Int.modEq_zero_iff_dvd.mpr <| dvd_pow (Int.natCast_dvd_natCast.mpr h) two_ne_zero))
                  norm_num at this
                  norm_cast at this
                  have := Nat.le_of_dvd (by norm_num) this
                  interval_cases p <;> trivial⟩
          exact Int.mod_coprime h_inv
        exact ⟨y * -k, by simpa [mul_assoc] using hy.mul_right (-k)⟩
      use Int.natAbs (x + y * p)
      rw [Int.modEq_iff_dvd] at *
      obtain ⟨z, hz⟩ := hy
      use z - y ^ 2
      cases abs_cases (x + y * p : ℤ) <;> push_cast [*] <;> nlinarith
    obtain ⟨x, hx⟩ := h_quad_res
    refine ⟨x, ?_⟩
    erw [← ZMod.intCast_eq_intCast_iff] at hx
    simpa using hx
  refine' ⟨r₁, -r₁, rfl, _, _, _, _⟩ <;> simp_all +decide [sq]
  · rw [eq_neg_iff_add_eq_zero]
    by_contra h_contra
    have h_r1_zero : r₁ = 0 := by
      have h_r1_zero : (2 : ℕ) * r₁.val ≡ 0 [MOD p ^ 2] := by
        simp_all +decide [← ZMod.natCast_eq_natCast_iff]
        grind
      have h_r1_zero : p ^ 2 ∣ r₁.val := by
        exact
          (Nat.Coprime.dvd_of_dvd_mul_left
              (show Nat.Coprime (p ^ 2) 2 from by
                exact
                  Nat.Coprime.pow_left 2 <|
                    hp.coprime_iff_not_dvd.mpr fun h => by
                      have := Nat.le_of_dvd (by decide) h
                      interval_cases p <;> trivial)
              <| Nat.dvd_of_mod_eq_zero h_r1_zero)
      have := Fact.mk hp
      rw [← ZMod.natCast_eq_zero_iff] at h_r1_zero
      aesop
    norm_num [h_r1_zero] at hr₁
    rcases p with (_ | _ | _ | p) <;>
      (cases hr₁; all_goals contradiction)
  · have h_solutions : ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = -r₁ := by
      intro r hr
      have h_eq : (r - r₁) * (r + r₁) = 0 := by grind
      have h_coprime :
          Nat.gcd (p ^ 2) (r - r₁).val = 1 ∨ Nat.gcd (p ^ 2) (r + r₁).val = 1 := by
        have h_coprime : ¬(p ∣ (r - r₁).val ∧ p ∣ (r + r₁).val) := by
          have := Fact.mk hp
          simp_all +decide [← ZMod.natCast_eq_zero_iff]
          intro h
          have := Fact.mk hp
          simp_all +decide [sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg]
          rw [eq_neg_iff_add_eq_zero]
          have := congr_arg (fun x : ZMod (p ^ 2) => x.val) hr₁
          norm_num [ZMod.val_add, ZMod.val_mul] at this ⊢
          replace this := congr_arg (· % p) this
          norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at this
          simp_all +decide [← sq, ← ZMod.natCast_eq_natCast_iff']
          intro H
          rw [← two_mul] at H
          replace H := congr_arg (fun x : ZMod p => x ^ 2) H
          simp_all +decide [mul_pow]
          rcases p with (_ | _ | _ | p) <;> cases H <;> contradiction
        simp_all +decide [Nat.Prime.coprime_iff_not_dvd]
        tauto
      have h_div : (p ^ 2 : ℕ) ∣ (r - r₁).val ∨ (p ^ 2 : ℕ) ∣ (r + r₁).val := by
        have h_div : (p ^ 2 : ℕ) ∣ ((r - r₁).val * (r + r₁).val) := by
          have := Fact.mk hp
          simp_all +decide [← ZMod.natCast_eq_zero_iff]
        cases h_coprime with
        | inl hc => exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left hc h_div)
        | inr hc => exact Or.inl (Nat.Coprime.dvd_of_dvd_mul_right hc h_div)
      have := Fact.mk hp
      simp_all +decide [← ZMod.natCast_eq_zero_iff, sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg]
    simpa only [sq] using h_solutions

lemma cross_residue_not_div_25_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 ≠ r) : ¬ (25 ∣ a * b + 1) := by
  intro hdiv
  have hr_lt : r < 25 := by
    have : a % 25 < 25 := Nat.mod_lt a (by decide : 0 < 25)
    simpa [ha] using this
  have h0 : ((a * b + 1 : ℕ) : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff (a * b + 1) 25).2 hdiv
  have haZ : (a : ZMod 25) = (r : ZMod 25) := by
    have ha_mod : a % 25 = r % 25 := by
      have h := congrArg (fun x => x % 25) ha
      have hleft : (a % 25) % 25 = a % 25 :=
        Nat.mod_eq_of_lt (Nat.mod_lt a (by decide : 0 < 25))
      simpa [hleft] using h
    exact (ZMod.natCast_eq_natCast_iff' a r 25).2 ha_mod
  have h1 : (r : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
    have : (a : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h0
    simpa [haZ] using this
  have h2 : (r : ZMod 25) * (b : ZMod 25) = (-1 : ZMod 25) := by
    simpa using (eq_neg_of_add_eq_zero_left h1)
  have hrZ : (r : ZMod 25) * (r : ZMod 25) = (-1 : ZMod 25) := by
    have hrr : ((r * r : ℕ) : ZMod 25) = (24 : ZMod 25) := by
      have : (r * r) % 25 = 24 % 25 := by
        simpa [Nat.mod_eq_of_lt (by decide : 24 < 25)] using hr
      exact (ZMod.natCast_eq_natCast_iff' (r * r) 24 25).2 this
    have hrr' : (r : ZMod 25) * (r : ZMod 25) = (24 : ZMod 25) := by simpa using hrr
    exact hrr'.trans (by decide : (24 : ZMod 25) = (-1 : ZMod 25))
  have hr_inv : (-(r : ZMod 25)) * (r : ZMod 25) = (1 : ZMod 25) := by
    calc
      (-(r : ZMod 25)) * (r : ZMod 25) = -((r : ZMod 25) * (r : ZMod 25)) := by simp
      _ = -(-1 : ZMod 25) := by simp [hrZ]
      _ = (1 : ZMod 25) := by simp
  have hbZ : (b : ZMod 25) = (r : ZMod 25) := by
    have hmul : (-(r : ZMod 25)) * ((r : ZMod 25) * (b : ZMod 25)) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using congrArg (fun x => (-(r : ZMod 25)) * x) h2
    have hmul' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using hmul
    have hmul'' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa using hmul'
    have : (1 : ZMod 25) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa [hr_inv] using hmul''
    simpa using this
  have hbmod : b % 25 = r := by
    have hb' : b % 25 = r % 25 := (ZMod.natCast_eq_natCast_iff' b r 25).1 hbZ
    simpa [Nat.mod_eq_of_lt hr_lt] using hb'
  exact hb hbmod

lemma cross_residue_not_div_25 (a b : ℕ) (ha : a % 25 = 7)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) : ¬ (25 ∣ a * b + 1) := by
  exact cross_residue_not_div_25_of_residue 7 a b (by norm_num) ha hb.1

lemma cross_residue_not_div_25_18 (a b : ℕ) (ha : a % 25 = 18)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) : ¬ (25 ∣ a * b + 1) := by
  exact cross_residue_not_div_25_of_residue 18 a b (by norm_num) ha hb.2

lemma must_have_other_prime_square_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 ≠ r) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ a * b + 1 := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬p * p ∣ a * b + 1 := by
    intro hall
    exact hnsq ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push Not at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  have h25 : ¬ (25 ∣ a * b + 1) := cross_residue_not_div_25_of_residue r a b hr ha hb
  have hp2 : p ^ 2 ∣ a * b + 1 := by simpa [pow_two] using hpp
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ a * b + 1 := by simpa [pow_two] using hp2
  exact (h25 this).elim

lemma must_have_other_prime_square (a b : ℕ) (ha : a % 25 = 7)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p^2 ∣ a * b + 1 := by
  exact must_have_other_prime_square_of_residue 7 a b (by norm_num) ha hb.1 hnsq

lemma must_have_other_prime_square_18 (a b : ℕ) (ha : a % 25 = 18)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ a * b + 1 := by
  exact must_have_other_prime_square_of_residue 18 a b (by norm_num) ha hb.2 hnsq

noncomputable section DensityLemmas

lemma card_filter_mod_eq_le (N m r : ℕ) :
    ((Finset.range N).filter (fun n => n ≡ r [MOD m])).card ≤ N / m + 1 := by
  have h_set :
      Finset.filter (fun n => n ≡ r [MOD m]) (Finset.range N) ⊆
        Finset.image (fun q => q * m + (r % m)) (Finset.range (N / m + 1)) := by
    intro n hn
    obtain ⟨hnlt,heq⟩ := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp hnlt
    refine Finset.mem_image.mpr ⟨n/m, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le)), ?_⟩
    change n % m = r % m at heq
    rw [← heq, Nat.mul_comm (n/m) m, Nat.add_comm, Nat.mod_add_div]
  exact le_trans (Finset.card_le_card h_set) (Finset.card_image_le.trans (by norm_num))

lemma card_filter_modEq_and_modEq_le (N m n a b : ℕ) (hcop : Nat.Coprime m n) :
    ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤ N / (m * n) + 1 := by
  classical
  have hsub :
      (Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n]) ⊆
        (Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n]) := by
    intro x hx
    simp [Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨hx.1, ?_⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop) hx.2.1 hx.2.2
  have hcard :
      ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤
        ((Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n])).card :=
    Finset.card_le_card hsub
  exact le_trans hcard (card_filter_mod_eq_le N (m * n) (Nat.chineseRemainder hcop a b))

end DensityLemmas

lemma zmod25_sq_eq_neg_one_iff :
    ∀ x : ZMod 25, x ^ 2 = (-1 : ZMod 25) ↔ x = (7 : ZMod 25) ∨ x = (18 : ZMod 25) := by
  decide

lemma mod25_eq_7_or_18_of_dvd_sq_add_one {n : ℕ} (h : 25 ∣ n ^ 2 + 1) :
    n % 25 = 7 ∨ n % 25 = 18 := by
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 25).2 h
  have hsq : (n : ZMod 25) ^ 2 = (-1 : ZMod 25) := by
    have : (n : ZMod 25) ^ 2 + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
    simpa using (eq_neg_of_add_eq_zero_left this)
  have hx : (n : ZMod 25) = (7 : ZMod 25) ∨ (n : ZMod 25) = (18 : ZMod 25) :=
    (zmod25_sq_eq_neg_one_iff (n : ZMod 25)).1 hsq
  cases hx with
  | inl h7 =>
      left
      have hn : n % 25 = 7 % 25 := (ZMod.natCast_eq_natCast_iff' n 7 25).1 h7
      simpa [Nat.mod_eq_of_lt (by decide : 7 < 25)] using hn
  | inr h18 =>
      right
      have hn : n % 25 = 18 % 25 := (ZMod.natCast_eq_natCast_iff' n 18 25).1 h18
      simpa [Nat.mod_eq_of_lt (by decide : 18 < 25)] using hn

lemma not_dvd_25_sq_add_one_of_mod_ne (n : ℕ) (h : n % 25 ≠ 7 ∧ n % 25 ≠ 18) :
    ¬ (25 ∣ n ^ 2 + 1) := by
  intro h25
  have := mod25_eq_7_or_18_of_dvd_sq_add_one (n := n) h25
  cases this with
  | inl h7 => exact h.1 h7
  | inr h18 => exact h.2 h18

lemma not_dvd_four_sq_add_one (n : ℕ) : ¬ (4 ∣ n ^ 2 + 1) := by
  intro h4
  have hmod : (n ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  have hrewrite : (n ^ 2 + 1) % 4 = ((n % 4) ^ 2 + 1) % 4 := by
      calc
      (n ^ 2 + 1) % 4 = (n ^ 2 % 4 + 1 % 4) % 4 := by
        simp [Nat.add_mod]
      _ = (((n % 4) ^ 2 % 4) + 1) % 4 := by
        simp [Nat.pow_mod]
      _ = ((n % 4) ^ 2 + 1) % 4 := by
        simp [Nat.add_mod]
  have hmod' : ((n % 4) ^ 2 + 1) % 4 = 0 := by simpa [hrewrite] using hmod
  have hn4 : n % 4 ≤ 3 := by
    have hn4lt : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
    have : n % 4 < 3 + 1 := by simpa using hn4lt
    exact (Nat.lt_succ_iff).1 this
  interval_cases hcase : n % 4 <;> simp at hmod'

def SawhneyMainAt (η : ℝ) (N₀ : ℕ) : Prop :=
  0 < η ∧ η < (1 / 25 : ℝ) ∧
    ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.range N →
      NonSquarefreeProductProp A →
      (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) →
      (A ⊆ A₇ N ∨ A ⊆ A₁₈ N)

def Problem848Statement (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.range N → NonSquarefreeProductProp A →
    A.card ≤ (A₇ N).card

lemma card_range_filter_mod25_eq (r : ℕ) (hr : r ≤ 24) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 25 = r)).card = (N + (24 - r)) / 25 := by
  classical
  have hr_lt : r < 25 := lt_of_le_of_lt hr (by decide : 24 < 25)
  set K : ℕ := (N + (24 - r)) / 25
  have hbij :
      ((Finset.range N).filter (fun n => n % 25 = r)).card = (Finset.range K).card := by
    refine (Finset.card_bij (s := Finset.range K) (t := (Finset.range N).filter (fun n => n % 25 = r))
      (i := fun k _hk => 25 * k + r) ?_ ?_ ?_).symm
    · intro k hk
      have hk' : k < K := by simpa [Finset.mem_range] using hk
      have hk1 : k + 1 ≤ K := Nat.succ_le_iff.2 hk'
      have hmul : 25 * (k + 1) ≤ 25 * K := Nat.mul_le_mul_left 25 hk1
      have hK : 25 * K ≤ N + (24 - r) := by
        simpa [K] using Nat.mul_div_le (N + (24 - r)) 25
      have hmul' : 25 * (k + 1) ≤ N + (24 - r) := le_trans hmul hK
      have hlt : 25 * k + r < N := by omega
      simp [Finset.mem_filter, Finset.mem_range, hlt, Nat.add_mod, hr_lt]
    · intro k₁ _hk₁ k₂ _hk₂ h
      have h' : 25 * k₁ = 25 * k₂ := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by decide : 0 < 25) h'
    · intro a ha
      have ha' : a < N ∧ a % 25 = r := by
        simpa [Finset.mem_filter, Finset.mem_range] using ha
      have ha_eq : 25 * (a / 25) + r = a := by
        have h := Nat.mod_add_div a 25
        simpa [ha'.2, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      refine ⟨a / 25, ?_, ?_⟩
      · have hlt : 25 * (a / 25) + r < N := by simpa [ha_eq] using ha'.1
        have hmul : 25 * ((a / 25) + 1) ≤ N + (24 - r) := by omega
        have hle : a / 25 + 1 ≤ K := by
          have hmul' : (a / 25 + 1) * 25 ≤ N + (24 - r) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
          have := (Nat.le_div_iff_mul_le (k0 := (by decide : 0 < 25))).2 hmul'
          simpa [K] using this
        have hltK : a / 25 < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle
        simpa [Finset.mem_range] using hltK
      · exact ha_eq
  simpa [Finset.card_range, K] using hbij

lemma A₇_card (N : ℕ) : (A₇ N).card = (N + 17) / 25 := by
  simpa [A₇, Nat.sub_sub] using (card_range_filter_mod25_eq 7 (by decide) N)

lemma A₁₈_card (N : ℕ) : (A₁₈ N).card = (N + 6) / 25 := by
  simpa [A₁₈, Nat.sub_sub] using (card_range_filter_mod25_eq 18 (by decide) N)

lemma A₁₈_card_le_A₇ (N : ℕ) : (A₁₈ N).card ≤ (A₇ N).card := by
  have h : N + 6 ≤ N + 17 := Nat.add_le_add_left (by decide : 6 ≤ 17) N
  simpa [A₇_card, A₁₈_card] using Nat.div_le_div_right h

lemma card_gt_A₇_implies_dense {η : ℝ} (hη : 0 < η) {N : ℕ} {A : Finset ℕ}
    (hgt : (A₇ N).card < A.card) :
    (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) := by
  have hsucc : (A₇ N).card + 1 ≤ A.card := Nat.succ_le_iff.2 hgt
  have hA : ((A₇ N).card + 1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hsucc
  have hA7 : ((N + 17 : ℝ) / 25) < ((A₇ N).card + 1 : ℝ) := by
    have hq : (25 : ℝ) * ((A₇ N).card + 1 : ℝ) > (N + 17 : ℝ) := by
      have hq_nat : 25 * ((A₇ N).card + 1) > N + 17 := by
        have hcard : (A₇ N).card = (N + 17) / 25 := A₇_card N
        have hdiv : 25 * ((N + 17) / 25) + (N + 17) % 25 = N + 17 := Nat.div_add_mod (N + 17) 25
        have hmod : (N + 17) % 25 < 25 := Nat.mod_lt _ (by decide : 0 < 25)
        omega
      exact_mod_cast hq_nat
    nlinarith
  have hN17 : (N + 17 : ℝ) / 25 ≥ (1 / 25 - η) * (N : ℝ) := by nlinarith
  have : (A.card : ℝ) ≥ (N + 17 : ℝ) / 25 := by
    have : (N + 17 : ℝ) / 25 ≤ (A.card : ℝ) := le_trans hA7.le hA
    exact this
  exact le_trans hN17 this

theorem problem_848_large_of_sawhney {η : ℝ} {N₀ : ℕ} (h : SawhneyMainAt η N₀) :
    ∀ N ≥ N₀, Problem848Statement N := by
  classical
  rcases h with ⟨hη, _hηsmall, hmain⟩
  intro N hN A hAsub hAprop
  by_contra hle
  have hgt : (A₇ N).card < A.card := lt_of_not_ge hle
  have hdense : (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) := card_gt_A₇_implies_dense hη hgt
  have hstruct := hmain N hN A hAsub hAprop hdense
  cases hstruct with
  | inl hsub7 => exact (not_le_of_gt hgt) (Finset.card_le_card hsub7)
  | inr hsub18 =>
      have hcard18 : A.card ≤ (A₁₈ N).card := Finset.card_le_card hsub18
      have h18le7 : (A₁₈ N).card ≤ (A₇ N).card := A₁₈_card_le_A₇ N
      exact (not_le_of_gt hgt) (le_trans hcard18 h18le7)

open Filter Finset

def primeCutoff : ℕ := 2000

lemma primeCutoff_pos : 0 < primeCutoff := by decide

def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

def diagPrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p % 4 = 1 ∧ 13 ≤ p)

def offPrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 5)

/-- Each prime passes all trial divisions, including trial division by itself. -/
private def sievePass (p : ℕ) : Bool :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43].all fun d =>
    decide (d = 1 ∨ d = p ∨ ¬ d ∣ p)

private theorem prime_sievePass {p : ℕ} (hp : p.Prime) : sievePass p = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply decide_eq_true
  by_cases hd : d ∣ p
  · rcases (Nat.dvd_prime hp).mp hd with eq | eq
    · exact Or.inl eq
    · exact Or.inr (Or.inl eq)
  · exact Or.inr (Or.inr hd)

/-- Round each reciprocal square upward in units of 10⁻¹⁰. -/
private def upperWeight (p : ℕ) : ℕ := 10000000000 / (p*p) + 1

private def sieveTerm (keep : ℕ → Bool) (p : ℕ) : ℕ :=
  if 2 ≤ p ∧ keep p = true ∧ sievePass p = true then upperWeight p else 0

private def accumulate (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => accumulate f i + f i

private theorem accumulate_eq (f : ℕ → ℕ) (n : ℕ) :
    accumulate f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih => rw [accumulate, Finset.sum_range_succ, ih]

private theorem sum_reciprocal_bound (P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p) :
    ∑ p ∈ P, (1:ℚ)/(p:ℚ)^2 ≤ ((∑ p ∈ P, upperWeight p : ℕ):ℚ) / 10000000000 := by
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have strict := Nat.lt_mul_div_succ 10000000000 (Nat.mul_pos (pos p hp) (pos p hp))
  have h : (10000000000 : ℚ) ≤ ((p*p:ℕ):ℚ) * (upperWeight p : ℚ) := by
    exact_mod_cast strict.le
  push_cast at h
  apply (div_le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast pos p hp)) (by norm_num)).mpr
  linarith only [show (10000000000 : ℚ) ≤ (p:ℚ)^2 * (upperWeight p : ℚ) by simpa [sq] using h]

private theorem sieve_bound (P : Finset ℕ) (keep : ℕ → Bool)
    (member : ∀ p ∈ P, p ∈ Finset.range 2001 ∧ p.Prime ∧ keep p = true) :
    (∑ p ∈ P, (1:ℚ)/(p:ℚ)^2) ≤ (accumulate (sieveTerm keep) 2001 : ℚ) / 10000000000 := by
  have subset : P ⊆ Finset.range 2001 := fun p hp => (member p hp).1
  have total : ∑ p ∈ P, upperWeight p ≤ accumulate (sieveTerm keep) 2001 := by
    rw [accumulate_eq]
    calc
      ∑ p ∈ P, upperWeight p = ∑ p ∈ P, sieveTerm keep p := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨_, pr, hkeep⟩ := member p hp
        simp only [sieveTerm, pr.two_le, hkeep, prime_sievePass pr, and_self, if_true]
      _ ≤ ∑ p ∈ Finset.range 2001, sieveTerm keep p :=
        Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
  apply (sum_reciprocal_bound P (fun p hp => (member p hp).2.1.pos)).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast total) (by norm_num)

private def diagKeep (p : ℕ) : Bool := decide (p % 4 = 1 ∧ 13 ≤ p)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem diagSumCertificate :
    accumulate (sieveTerm diagKeep) 2001 = 137847261 := by decide +kernel

private def diagPrimeSumCoarse : ℚ :=
  ∑ p ∈ diagPrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem diagPrimesCoarse_sum_eq :
    (∑ p ∈ diagPrimesCoarse, (1:ℚ)/(p:ℚ)^2) = diagPrimeSumCoarse := rfl

private theorem diagPrimeSumCoarse_bound :
    diagPrimeSumCoarse + (1:ℚ)/7984 ≤ (1:ℚ) / (359/5) := by
  have estimate := sieve_bound diagPrimesCoarse diagKeep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [diagSumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/7984) : _).trans (by norm_num [primeCutoff])

private def offKeep (p : ℕ) : Bool := decide (p ≠ 2 ∧ p ≠ 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem offSumCertificate :
    accumulate (sieveTerm offKeep) 2001 = 1621891203 := by decide +kernel

private def offPrimeSumCoarse : ℚ :=
  ∑ p ∈ offPrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem offPrimesCoarse_sum_eq :
    (∑ p ∈ offPrimesCoarse, (1:ℚ)/(p:ℚ)^2) = offPrimeSumCoarse := rfl

private theorem offPrimeSumCoarse_bound :
    offPrimeSumCoarse + (1:ℚ)/primeCutoff ≤ (163:ℚ) / 1000 := by
  have estimate := sieve_bound offPrimesCoarse offKeep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [offSumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/2000) : _).trans (by norm_num [primeCutoff])

private def no5Keep (p : ℕ) : Bool := decide (p ≠ 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem no5SumCertificate :
    accumulate (sieveTerm no5Keep) 2001 = 4121891204 := by decide +kernel

private def no5PrimeSumCoarse : ℚ :=
  ∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem no5PrimesCoarse_sum_eq :
    (∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2) = no5PrimeSumCoarse := rfl

private theorem no5PrimeSumCoarse_bound :
    no5PrimeSumCoarse + (1:ℚ)/primeCutoff ≤ (413:ℚ) / 1000 := by
  have estimate := sieve_bound no5PrimesCoarse no5Keep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [no5SumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/2000) : _).trans (by norm_num [primeCutoff])

lemma sum_Ioc_inv_sq_le_inv (B N : ℕ) (hB : B ≠ 0) :
    (∑ i ∈ Finset.Ioc B N, (1 : ℚ) / (i ^ 2 : ℚ)) ≤ (1 : ℚ) / B := by
  by_cases hBN : B < N
  · have hle : B ≤ N := Nat.le_of_lt hBN
    have hsub := sum_Ioc_inv_sq_le_sub (α := ℚ) (k := B) (n := N) hB hle
    have hnonneg : 0 ≤ (N : ℚ)⁻¹ := by positivity
    have hsub' : (B : ℚ)⁻¹ - (N : ℚ)⁻¹ ≤ (B : ℚ)⁻¹ := sub_le_self _ hnonneg
    simpa [one_div] using hsub.trans hsub'
  · have hIoc : (Finset.Ioc B N) = ∅ := by
      apply Finset.Ioc_eq_empty
      exact not_lt.2 (Nat.le_of_not_gt hBN)
    simp [hIoc, one_div]

def diagPrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p % 4 = 1 ∧ 13 ≤ p)

def offPrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 5)

lemma sq_pred_add_one_lt_sq (N : ℕ) (hN : 100 ≤ N) : (N - 1) * (N - 1) + 1 < N ^ 2 := by
  have h2 : 2 ≤ N := le_trans (by norm_num : 2 ≤ 100) hN
  have h1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2) h2
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel h1
  have hpos : 0 < N - 1 := by omega
  calc (N - 1) * (N - 1) + 1
      < (N - 1) * (N - 1) + 2 * (N - 1) + 1 := by omega
    _ = (N - 1 + 1) * (N - 1 + 1) := by ring
    _ = N * N := by rw [hsub]
    _ = N ^ 2 := by rw [Nat.pow_two]

/-- Only one out of four integers can occur in the diagonal prime tail.
Send 4j+1 to j and majorize its reciprocal square by 1/(16j²). -/
private theorem diag_progression_tail (N : ℕ) :
    (∑ p ∈ (Finset.Ioc primeCutoff N).filter (fun p => p%4=1), (1 : ℚ)/(p:ℚ)^2)
      ≤ 1/7984 := by
  classical
  let P := (Finset.Ioc primeCutoff N).filter (fun p => p%4=1)
  let f (j : ℕ) : ℚ := 1/(j:ℚ)^2
  have bounds (p : ℕ) (hp : p ∈ P) : 2000<p ∧ p≤N ∧ p%4=1 := by
    obtain ⟨hr,hm⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_Ioc.mp hr).1,(Finset.mem_Ioc.mp hr).2,hm⟩
  have inj : Set.InjOn (fun p : ℕ => p/4) P := by
    intro i hi j hj eq
    have bi := bounds i hi
    have bj := bounds j hj
    dsimp at eq
    omega
  have sub : P.image (·/4) ⊆ Finset.Ioc 499 N := by
    rintro j hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    have b := bounds p hp
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  have point (p : ℕ) (hp : p ∈ P) : f p ≤ (1/16 : ℚ)*f (p/4) := by
    have b := bounds p hp
    have pos : 0 < ((p/4:ℕ):ℚ) := by exact_mod_cast (show 0 < p/4 by omega)
    have ppos : 0 < (p:ℚ) := by exact_mod_cast (show 0 < p by omega)
    have ord : 4*((p/4:ℕ):ℚ) ≤ (p:ℚ) := by exact_mod_cast (show 4*(p/4)≤p by omega)
    dsimp [f]
    have square := mul_le_mul ord ord (by positivity) ppos.le
    field_simp
    nlinarith only [square]
  have major := Finset.sum_le_sum point
  rw [← Finset.mul_sum,← Finset.sum_image inj] at major
  have mon : ∑ j ∈ P.image (·/4), f j ≤ ∑ j ∈ Finset.Ioc 499 N, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => by dsimp [f]; positivity)
  have tail : ∑ j ∈ Finset.Ioc 499 N, f j ≤ 1/499 := sum_Ioc_inv_sq_le_inv 499 N (by decide)
  change (∑ p ∈ P, f p) ≤ _
  linarith only [major,mon,tail]

set_option maxRecDepth 10000 in
lemma sum_diagPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (1 : ℚ) / (359/5) := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  let tailP := (Finset.Ioc primeCutoff N).filter (fun p => p%4=1)
  have hsubset : diagPrimesUpTo N ⊆ diagPrimesCoarse ∪ tailP := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p % 4 = 1 ∧ 13 ≤ p := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ diagPrimesCoarse := by
        simp [diagPrimesCoarse, hp_mem_cutoff, hp_cond.1, hp_cond.2]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.mpr ⟨this,hp_cond.1⟩))
  have hdisj : Disjoint diagPrimesCoarse tailP := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 (Finset.mem_filter.mp hp_Ioc).1).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤ ∑ p ∈ diagPrimesCoarse ∪ tailP, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤
        diagPrimeSumCoarse + (∑ i ∈ tailP, f i) := by
    calc
      (∑ p ∈ diagPrimesUpTo N, f p) ≤
          ∑ p ∈ diagPrimesCoarse ∪ tailP, f p := hsum_le_union
      _ = (∑ p ∈ diagPrimesCoarse, f p) + (∑ i ∈ tailP, f i) := by
          simp [Finset.sum_union hdisj]
      _ = diagPrimeSumCoarse + (∑ i ∈ tailP, f i) := by
          simp only [f, diagPrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ tailP, f i) ≤ (1 : ℚ) / 7984 := by
    exact diag_progression_tail N
  have hsum_le' :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤ diagPrimeSumCoarse + (1 : ℚ) / 7984 := by
    exact hsum_le.trans (add_le_add_right htail diagPrimeSumCoarse)
  exact hsum_le'.trans diagPrimeSumCoarse_bound

set_option maxRecDepth 10000 in
lemma sum_offPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (163 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : offPrimesUpTo N ⊆ offPrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 2 ∧ p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ offPrimesCoarse := by
        simp [offPrimesCoarse, hp_mem_cutoff, hp_cond.1, hp_cond.2]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint offPrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ offPrimesUpTo N, f p) ≤
        offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ offPrimesUpTo N, f p) ≤
          ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ offPrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, offPrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ offPrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail offPrimeSumCoarse)
  exact hsum_le'.trans offPrimeSumCoarse_bound

set_option maxRecDepth 10000 in
lemma sum_no5PrimesUpTo_le (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (413 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : no5PrimesUpTo N ⊆ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ no5PrimesCoarse := by
        simp [no5PrimesCoarse, hp_mem_cutoff, hp_cond]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint no5PrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
        no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
          ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ no5PrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, no5PrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ no5PrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail no5PrimeSumCoarse)
  exact hsum_le'.trans no5PrimeSumCoarse_bound

def residues25 : Finset ℕ :=
  (Finset.range 25).filter (fun t => t ≠ 7 ∧ t ≠ 18)

lemma residues25_card : residues25.card = 23 := by
  decide

def residues50odd : Finset ℕ :=
  (Finset.range 50).filter (fun t => t % 2 = 1 ∧ t % 25 ≠ 7 ∧ t % 25 ≠ 18)

lemma residues50odd_card : residues50odd.card = 23 := by
  decide

lemma primesUpTo_card (B : ℕ) : (primesUpTo B).card = B.primeCounting := by
  classical
  simp [primesUpTo, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

lemma prime_eq_of_dvd_2 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 2) : p = 2 := by
  have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  omega

lemma prime_eq_of_dvd_5 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 5) : p = 5 := by
  have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  interval_cases p <;> simp_all

lemma coprime_25_pow_two_of_prime_ne5 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    Nat.Coprime 25 (p ^ 2) := by
  have hnot : ¬ p ∣ 25 := by
    intro h
    have hpow : p ∣ 5 ^ 2 := by
      have : (5 ^ 2 : ℕ) = 25 := by rfl
      simpa [this] using h
    have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
    exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 25) (m := 2) hnot

lemma coprime_100_pow_two_of_prime_ne2_ne5 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    Nat.Coprime 100 (p ^ 2) := by
  have hnot : ¬ p ∣ 100 := by
    intro h
    have hpow : p ∣ 10 ^ 2 := by
      have : (10 ^ 2 : ℕ) = 100 := by rfl
      simpa [this] using h
    have h10 : p ∣ 10 := hp.dvd_of_dvd_pow hpow
    have hmul : p ∣ 2 ∨ p ∣ 5 := by
      have : 10 = 2 * 5 := by rfl
      simpa [this] using (hp.dvd_mul.1 (by simpa [this] using h10))
    cases hmul with
    | inl h2 => exact hp2 (prime_eq_of_dvd_2 p hp h2)
    | inr h5 => exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 100) (m := 2) hnot

lemma prime_square_exists {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬ p * p ∣ n := by
    intro hall
    exact hn ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push Not at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  refine ⟨p, hp, ?_⟩
  simpa [pow_two] using hpp

lemma prime_square_exists_ne5 {n : ℕ} (hn : ¬ Squarefree n) (h25 : ¬ 25 ∣ n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ n := by
  obtain ⟨p, hp, hp2⟩ := prime_square_exists (n := n) hn
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ n := by simpa [pow_two] using hp2
  exact (h25 this).elim

lemma cross_residue_7_18_not_div_25 (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) :
    ¬ (25 ∣ a * b + 1) := by
  have hb_ne : b % 25 ≠ 7 := by
    intro hb7
    have : (18 : ℕ) = 7 := hb.symm.trans hb7
    exact (by decide : (18 : ℕ) ≠ 7) this
  exact cross_residue_not_div_25_of_residue 7 a b (by norm_num) ha hb_ne

lemma cross_residue_18_7_not_div_25 (a b : ℕ) (ha : a % 25 = 18) (hb : b % 25 = 7) :
    ¬ (25 ∣ a * b + 1) := by
  simpa [Nat.mul_comm] using cross_residue_7_18_not_div_25 b a hb ha

lemma off_count_modEq25_le (N p b t : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    have : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset :
      (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard := Finset.card_le_card hsubset
  exact le_trans hcard (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r hcop)

private lemma not_sq_dvd_mul_add_one_of_prime_dvd_left
    {p b a : ℕ} (hp : Nat.Prime p) (hb : p ∣ b) : ¬ p ^ 2 ∣ b * a + 1 := by
  intro hp2
  have hp1 : p ∣ b * a + 1 := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2
  have hpa : p ∣ b * a := dvd_mul_of_dvd_left hb a
  have : p ∣ 1 := (Nat.dvd_add_right hpa).mp hp1
  exact hp.not_dvd_one this

lemma filter_empty_of_prime_dvd_left_of_pred
    {N p b : ℕ} (hp : Nat.Prime p) (hb : p ∣ b)
    (pred : ℕ → Prop) [DecidablePred pred] :
    (Finset.range N).filter (fun a => pred a ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
  classical
  ext a
  simp [not_sq_dvd_mul_add_one_of_prime_dvd_left (p := p) (b := b) (a := a) hp hb]

lemma off_count_modEq25_le' (N p b t : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · 
    have hempty :
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t [MOD 25]))
    simp [hempty]
  · exact off_count_modEq25_le N p b t hp hb hp5

lemma off_count_modEq100_le (N p b t25 t4 : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (100 * p ^ 2) + 1 := by
  classical
  have hcop25_4 : Nat.Coprime 25 4 := by decide
  have hsub :
      (Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ?_, ha.2.2.2⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop25_4) ha.2.1 ha.2.2.1
  have hcard :
      ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1)).card :=
    Finset.card_le_card hsub
  have hcop : Nat.Coprime 100 (p ^ 2) := coprime_100_pow_two_of_prime_ne2_ne5 p hp hp2 hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    have : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset2 :
      (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard2 :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2])).card :=
    Finset.card_le_card hsubset2
  have hfinal :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2])).card ≤
        N / (100 * p ^ 2) + 1 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 100 (p ^ 2) (Nat.chineseRemainder hcop25_4 t25 t4) r hcop)
  exact le_trans (le_trans hcard hcard2) hfinal

lemma off_count_modEq100_le' (N p b t25 t4 : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (100 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · 
    have hempty :
        (Finset.range N).filter
            (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa [and_assoc] using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4]))
    simp [hempty]
  · exact off_count_modEq100_le N p b t25 t4 hp hb hp2 hp5

lemma prime_ge_13_of_mod4_one_ne5 (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    13 ≤ p := by
  have hp_ge2 : 2 ≤ p := hp.two_le
  by_contra h
  have hp_le12 : p ≤ 12 := by
    have hp_lt13 : p < 13 := lt_of_not_ge h
    have : p < 12 + 1 := by simpa using hp_lt13
    exact (Nat.lt_succ_iff).1 this
  interval_cases p <;> simp_all +decide

lemma coprime_50_pow_two_of_prime_ne2_ne5 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    Nat.Coprime 50 (p ^ 2) := by
  have hnot : ¬ p ∣ 50 := by
    intro h
    have hmul : p ∣ 2 * 25 := by
      have : 2 * 25 = 50 := by rfl
      simpa [this] using h
    have hdiv : p ∣ 2 ∨ p ∣ 25 := hp.dvd_mul.1 hmul
    cases hdiv with
    | inl h2 => exact hp2 (prime_eq_of_dvd_2 p hp h2)
    | inr h25 =>
        have hpow : p ∣ 5 ^ 2 := by
          have : (5 ^ 2 : ℕ) = 25 := by rfl
          simpa [this] using h25
        have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
        exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 50) (m := 2) hnot

lemma diag_count_modEq25_le (N p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (25 * p ^ 2) + 1) := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    obtain ⟨r,t,_,rest⟩ := two_roots_mod_p_squared p hp hmod
    exact ⟨r,t,rest⟩
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (25 * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (25 * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (25 * p ^ 2) + 1) + (N / (25 * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

lemma diag_count_modEq50_le (N p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (50 * p ^ 2) + 1) := by
  classical
  have hcop : Nat.Coprime 50 (p ^ 2) := coprime_50_pow_two_of_prime_ne2_ne5 p hp hp2 hp5
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    obtain ⟨r,t,_,rest⟩ := two_roots_mod_p_squared p hp hmod
    exact ⟨r,t,rest⟩
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (50 * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 50 (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (50 * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 50 (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (50 * p ^ 2) + 1) + (N / (50 * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

lemma diag_count_mod25_ne_7_18_le (N p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      46 * (N / (25 * p ^ 2) + 1) := by
  classical
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  have hsubset :
      S ⊆ residues25.biUnion (fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
    intro n hn
    simp [S, Finset.mem_filter, Finset.mem_range] at hn
    set t : ℕ := n % 25
    have ht : t ∈ residues25 := by
      have htlt : t < 25 := Nat.mod_lt n (by decide : 0 < 25)
      have htne : t ≠ 7 ∧ t ≠ 18 := by
        refine ⟨?_, ?_⟩
        · simpa [t] using hn.2.1
        · simpa [t] using hn.2.2.1
      simp [residues25, Finset.mem_filter, Finset.mem_range, t, htlt, htne]
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨t, ht, ?_⟩
    simp [Finset.mem_filter, Finset.mem_range, hn.1, hn.2.2.2]
    simpa [t] using (Nat.mod_modEq n 25).symm
  have hcard : S.card ≤ (residues25.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_le_card hsubset
  have hsum :
      (residues25.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
        ∑ t ∈ residues25,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_biUnion_le
  have hper :
      ∀ t ∈ residues25,
        ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
          2 * (N / (25 * p ^ 2) + 1) := by
    intro t ht
    exact diag_count_modEq25_le N p t hp hmod hp5
  have hsum' :
      (∑ t ∈ residues25,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card) ≤
        ∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1) :=
    Finset.sum_le_sum fun t ht => hper t ht
  have hconst :
      (∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1)) = 46 * (N / (25 * p ^ 2) + 1) := by
    classical
    have h46 : (46 : ℕ) = 23 * 2 := by rfl
    calc
      (∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1)) = residues25.card * (2 * (N / (25 * p ^ 2) + 1)) := by
        simp
      _ = 23 * (2 * (N / (25 * p ^ 2) + 1)) := by
        simp [residues25_card]
      _ = (23 * 2) * (N / (25 * p ^ 2) + 1) := by
        exact (mul_assoc 23 2 (N / (25 * p ^ 2) + 1)).symm
      _ = 46 * (N / (25 * p ^ 2) + 1) := by
        simp [h46.symm]
  exact le_trans (le_trans hcard hsum) (le_trans hsum' (le_of_eq hconst))

lemma diag_count_mod50odd_ne_7_18_le (N p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      46 * (N / (50 * p ^ 2) + 1) := by
  classical
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  have hsubset :
      S ⊆ residues50odd.biUnion (fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
    intro n hn
    simp [S, Finset.mem_filter, Finset.mem_range] at hn
    set t : ℕ := n % 50
    have ht : t ∈ residues50odd := by
      have htlt : t < 50 := Nat.mod_lt n (by decide : 0 < 50)
      have htodd : t % 2 = 1 := by
        have : (n % 50) % 2 = n % 2 := by
          simp [show 50 = 25 * 2 by rfl]
        simpa [t, this] using hn.2.1
      have htne7 : t % 25 ≠ 7 := by
        have : (n % 50) % 25 = n % 25 := by
          simp [show 50 = 25 * 2 by rfl]
        have hnne7 : n % 25 ≠ 7 := hn.2.2.1
        simpa [t, this] using hnne7
      have htne18 : t % 25 ≠ 18 := by
        have : (n % 50) % 25 = n % 25 := by
          simp [show 50 = 25 * 2 by rfl]
        have hnne18 : n % 25 ≠ 18 := hn.2.2.2.1
        simpa [t, this] using hnne18
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, ?_⟩
      · exact Finset.mem_range.2 htlt
      · exact ⟨htodd, htne7, htne18⟩
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨t, ht, ?_⟩
    simp [Finset.mem_filter, Finset.mem_range, hn.1, hn.2.2.2.2]
    simpa [t] using (Nat.mod_modEq n 50).symm
  have hcard : S.card ≤ (residues50odd.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_le_card hsubset
  have hsum :
      (residues50odd.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
        ∑ t ∈ residues50odd,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_biUnion_le
  have hper :
      ∀ t ∈ residues50odd,
        ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
          2 * (N / (50 * p ^ 2) + 1) := by
    intro t ht
    exact diag_count_modEq50_le N p t hp hmod hp2 hp5
  have hsum' :
      (∑ t ∈ residues50odd,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card) ≤
        ∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1) :=
    Finset.sum_le_sum fun t ht => hper t ht
  have hconst :
      (∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1)) = 46 * (N / (50 * p ^ 2) + 1) := by
    classical
    have h46 : (46 : ℕ) = 23 * 2 := by rfl
    calc
      (∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1)) = residues50odd.card * (2 * (N / (50 * p ^ 2) + 1)) := by
        simp
      _ = 23 * (2 * (N / (50 * p ^ 2) + 1)) := by
        simp [residues50odd_card]
      _ = (23 * 2) * (N / (50 * p ^ 2) + 1) := by
        exact (mul_assoc 23 2 (N / (50 * p ^ 2) + 1)).symm
      _ = 46 * (N / (50 * p ^ 2) + 1) := by
        simp [h46.symm]
  exact le_trans (le_trans hcard hsum) (le_trans hsum' (le_of_eq hconst))

lemma prime_le_of_sq_dvd_lt_sq {p N X : ℕ} (hXpos : 0 < X) (hXlt : X < N ^ 2) (hp2 : p ^ 2 ∣ X) : p ≤ N := by
  have hp2_le : p ^ 2 ≤ X := Nat.le_of_dvd hXpos hp2
  have hp2_lt : p ^ 2 < N ^ 2 := lt_of_le_of_lt hp2_le hXlt
  by_contra hp_le
  have hNp : N ≤ p := le_of_lt (Nat.not_le.mp hp_le)
  have hN2le : N ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hNp 2
  exact (not_lt_of_ge hN2le) hp2_lt

lemma prime_ne_two_of_sq_dvd_odd {p n : ℕ} (hn : n % 2 = 1) (hp2 : p ^ 2 ∣ n) : p ≠ 2 := by
  intro hp
  subst hp
  have h4 : 4 ∣ n := by simpa using hp2
  have h2 : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
  have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  omega

lemma sum_div_add_one_le_real (N : ℕ) (P : Finset ℕ) (k : ℕ) :
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hsplit :
      ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := by
    have :
        (∑ p ∈ P, (N / (k * p ^ 2) + 1 : ℕ)) =
          (∑ p ∈ P, (N / (k * p ^ 2) : ℕ)) + P.card := by
      simp [Finset.sum_add_distrib]
    exact_mod_cast this
  have hterm :
      ∀ p ∈ P, ((N / (k * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    intro p hp
    have h := (Nat.cast_div_le (α := ℝ) (m := N) (n := k * p ^ 2))
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h
  have hdiv' :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        ∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    exact_mod_cast (Finset.sum_le_sum fun p hp => hterm p hp)
  have hdiv :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
    have :
        (∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2)) =
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
      simp [div_eq_mul_inv, mul_sum, mul_comm]
    exact hdiv'.trans (le_of_eq this)
  have h := add_le_add_right hdiv (P.card : ℝ)
  calc
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := hsplit
    _ ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using h

lemma sieve_set_card_bound
    (N k : ℕ) (P S : Finset ℕ) (pred : ℕ → ℕ → Prop) [∀ p, DecidablePred (pred p)]
    (hsubset :
      S ⊆ P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n)))
    (hper : ∀ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card ≤ N / (k * p ^ 2) + 1) :
    (S.card : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hcard : S.card ≤ (∑ p ∈ P, (N / (k * p ^ 2) + 1)) := by
    calc
      S.card ≤
          ((P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n))).card) :=
        Finset.card_le_card hsubset
      _ ≤ ∑ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ P, (N / (k * p ^ 2) + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hper p hp
  have hcard_real :
      (S.card : ℝ) ≤ ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hcard_real.trans (sum_div_add_one_le_real (N := N) (P := P) (k := k))

/-- For p² ≥ 2N, distinct square roots of −1 cannot both be in [0,N).
The two roots are opposites, and the sum of two representatives is below p². -/
private theorem at_most_one_large_diagonal_root (N p : ℕ) (hp : p.Prime) (hmod : p%4=1)
    (large : 2*N ≤ p^2) (S : Finset ℕ) (inside : ∀ n ∈ S, n < N ∧ p^2 ∣ n^2+1) :
    S.card ≤ 1 := by
  obtain ⟨r,t,opposite,_,_,_,allRoots⟩ := two_roots_mod_p_squared p hp hmod
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have root (n : ℕ) (hn : n ∈ S) : (n : ZMod (p^2)) = r ∨ (n : ZMod (p^2)) = -r := by
    have eq0 := (ZMod.natCast_eq_zero_iff (n^2+1) (p^2)).mpr (inside n hn).2
    have eq1 : (n : ZMod (p^2))^2+1 = 0 := by exact_mod_cast eq0
    simpa only [opposite] using allRoots _ (eq_neg_of_add_eq_zero_left eq1)
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have xb := (inside x hx).1
  have yb := (inside y hy).1
  have cases : (x : ZMod (p^2)) = y ∨ (x : ZMod (p^2)) + y = 0 := by
    rcases root x hx with h | h <;> rcases root y hy with g | g <;> simp [h,g]
  rcases cases with h | h
  · have eq := (ZMod.natCast_eq_natCast_iff x y (p^2)).mp h
    change x%(p^2)=y%(p^2) at eq
    simpa only [Nat.mod_eq_of_lt (show x<p^2 by omega),
      Nat.mod_eq_of_lt (show y<p^2 by omega)] using eq
  · have eq : (p^2) ∣ x+y := (ZMod.natCast_eq_zero_iff (x+y) (p^2)).mp (by simpa using h)
    have h0 := Nat.mod_eq_zero_of_dvd eq
    rw [Nat.mod_eq_of_lt (by omega)] at h0
    omega

private theorem diagonal_partial (N k : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, (B p).card ≤ 46*(N/(k*p^2)+1))
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ 46*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/(k*(p:ℝ)^2))) +
      (P.card : ℝ) + 46*((2*N).sqrt : ℝ) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ (46*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (46 : ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      have denom := Nat.cast_div_le (α := ℝ) (m := N) (n := k*p^2)
      push_cast at denom
      have o : ((B p).card : ℝ) ≤ 46*(((N/(k*p^2) : ℕ):ℝ)+1) := by exact_mod_cast old p hp
      simp only [div_eq_mul_inv,one_mul] at denom ⊢
      linarith only [o,denom]
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ (46*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (46 : ℝ) else 0) = (small.card : ℝ)*46 := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ Finset.Icc 1 (2*N).sqrt := by
    intro p hp
    obtain ⟨hprime,hle⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨((Finset.mem_filter.mp (Finset.mem_filter.mp (primes hprime)).1).2 : p.Prime).pos,hle⟩
  have cs : small.card ≤ (2*N).sqrt := by simpa using Finset.card_le_card sub
  have csr : (small.card : ℝ) ≤ ((2*N).sqrt : ℝ) := by exact_mod_cast cs
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,csr]


private theorem truncate_sieve (N : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (c err : ℝ) (cpos : 0≤c) (weight : ℕ → ℝ) (nonneg : ∀ p, 0≤weight p)
    (pos : ∀p∈P, 0<p) (covered : S ⊆ P.biUnion B)
    (small : ∀ Q ⊆ P, ((Q.biUnion B).card : ℝ) ≤ c * (N * ∑ p ∈ Q, weight p) + Q.card + err)
    (large : 4000*((P.filter (fun p => N < 10000*p)).biUnion B).card ≤ N) :
    (S.card : ℝ) ≤ c * (N * ∑ p ∈ P, weight p) + (N:ℝ)/2300 + err := by
  classical
  let Q := P.filter (fun p => 10000*p ≤ N)
  let R := P.filter (fun p => N < 10000*p)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,hnp⟩ := Finset.mem_biUnion.mp (covered hn)
    by_cases h : 10000*p ≤ N
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,h⟩,hnp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,by omega⟩,hnp⟩)
  have counts : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (Finset.card_le_card cover).trans (Finset.card_union_le ..)
  have boundQ : Q ⊆ Finset.Icc 1 (N/10000) := by
    intro p hp
    obtain ⟨hp,h⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨pos p hp,by omega⟩
  have cardQ : Q.card ≤ N/10000 := by simpa using Finset.card_le_card boundQ
  have cardQN : 10000*Q.card ≤ N := by omega
  have cq : 10000*(Q.card:ℝ) ≤ N := by exact_mod_cast cardQN
  have cr : 4000*((R.biUnion B).card:ℝ) ≤ N := by exact_mod_cast large
  have st : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast counts
  have sub : Q ⊆ P := Finset.filter_subset .. 
  have m := Finset.sum_le_sum_of_subset_of_nonneg (f := weight) sub (fun p _ _ => nonneg p)
  have ml := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m (show (0:ℝ) ≤ N by positivity)) cpos
  have low := small Q sub
  have hN : (0:ℝ) ≤ N := by positivity
  linarith only [cq,cr,st,ml,low,hN]

private theorem diagonal_polynomial (N k : ℕ) (S : Finset ℕ) (B : ℕ → Finset ℕ)
    (big : 10^45 ≤ N) (covered : S ⊆ (diagPrimesUpTo N).biUnion B)
    (old : ∀ p ∈ diagPrimesUpTo N, (B p).card ≤ 46*(N/(k*p^2)+1))
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ 46*((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ)/(k*(p:ℝ)^2))) +
      (N:ℝ)/2300 + 46*((2*N).sqrt : ℝ) := by
  refine truncate_sieve N (diagPrimesUpTo N) S B 46 (46*((2*N).sqrt : ℝ)) (by norm_num)
    (fun p => (1:ℝ)/(k*(p:ℝ)^2)) (fun _ => by positivity) ?_ covered ?_ ?_
  · intro p hp
    exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2 : p.Prime).pos
  · intro Q sub
    exact diagonal_partial N k Q (Q.biUnion B) B sub (fun _ h => h)
      (fun p hp => old p (sub hp)) inside
  · apply Erdos848Gap.large_diagonal big
    intro n hn
    obtain ⟨p,hp,hnp⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨inP,large⟩ := Finset.mem_filter.mp hp
    have range := (Finset.mem_filter.mp (Finset.mem_filter.mp inP).1).1
    have up := Finset.mem_range.mp range
    exact ⟨(inside p n hnp).1,p,by omega,large,(inside p n hnp).2⟩

private theorem mixed_polynomial (N k b : ℕ) (P S : Finset ℕ) (pred : ℕ → ℕ → Prop)
    [∀p, DecidablePred (pred p)] (big : 10^45 ≤ N) (bN : b < N)
    (covered : S ⊆ P.biUnion (fun p => (Finset.range N).filter (pred p)))
    (old : ∀ p ∈ P, ((Finset.range N).filter (pred p)).card ≤ N/(k*p^2)+1)
    (inside : ∀p n, pred p n → p^2 ∣ b*n+1) (primes : P ⊆ primesUpTo N) :
    (S.card : ℝ) ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ)/(k*(p:ℝ)^2)) + (N:ℝ)/2300 := by
  let B (p : ℕ) := (Finset.range N).filter (pred p)
  have h := truncate_sieve N P S B 1 0 (by norm_num) (fun p => (1:ℝ)/(k*(p:ℝ)^2))
    (fun _ => by positivity) (fun p hp => ((Finset.mem_filter.mp (primes hp)).2 : p.Prime).pos)
    covered
  simp only [one_mul,add_zero] at h
  apply h
  · intro Q sub
    exact sieve_set_card_bound N k Q (Q.biUnion B) pred (fun _ h => h) (fun p hp => old p (sub hp))
  · apply Erdos848Gap.large_mixed big bN
    intro n hn
    obtain ⟨p,hp,hnp⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨inP,large⟩ := Finset.mem_filter.mp hp
    have upper := Finset.mem_range.mp (Finset.mem_filter.mp (primes inP)).1
    obtain ⟨nr,dv⟩ := Finset.mem_filter.mp hnp
    exact ⟨Finset.mem_range.mp nr,p,by omega,large,inside p n dv⟩

private theorem diagonal_sqrt_error (N : ℕ) (big : 10^18 ≤ N) :
    46*((2*N).sqrt : ℝ) ≤ (N : ℝ)/10000000 := by
  have big2 : 1000000000^2 ≤ 2*N := by norm_num at big ⊢; omega
  have hs := Nat.le_sqrt'.mpr big2
  have sq := Nat.sqrt_le' (2*N)
  have bound : 1000000000*(2*N).sqrt ≤ 2*N := by
    calc _ ≤ (2*N).sqrt * (2*N).sqrt := Nat.mul_le_mul_right _ hs
         _ ≤ _ := by simpa [pow_two] using sq
  have r : 1000000000*((2*N).sqrt : ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have n0 : 0 ≤ (N:ℝ) := by positivity
  linarith only [r,n0]

set_option maxHeartbeats 2000000 in
private theorem sawhney_effective_at (T : ℕ) (hT : 10^45 ≤ T)
    :
    SawhneyMainAt (1 / 1000000 : ℝ) T := by
  classical
  let δ : ℝ := (1 / 2300 : ℝ)
  let C_diag : ℝ := (1 : ℝ) / 1795
  let C_off : ℝ := 163 / 25000
  let C_no5 : ℝ := 413 / 25000
  refine ⟨?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro N hN A hAsub hAprop hdense
    have hsize : 10^45 ≤ N := hT.trans hN
    have hthreshold : 10^18 ≤ N := (by decide : 10^18 ≤ 10^45).trans hsize
    have hNbig : 2300 ≤ N := (by decide : 2300 ≤ 10^18).trans hthreshold
    have hsqrt := diagonal_sqrt_error N hthreshold
    have hN100 : 100 ≤ N := (by decide : 100 ≤ 2300).trans hNbig
    have hNpos_nat : 0 < N := lt_of_lt_of_le (by decide : 0 < 100) hN100
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat
    have herror : ((N : ℝ) / 2300) ≤ δ * (N : ℝ) := by dsimp [δ]; ring_nf; rfl
    have residue_class_card_bound_of_subset
        (t b : ℕ) (P S : Finset ℕ) (bN : b < N)
        (hsubset :
          S ⊆ P.biUnion (fun p =>
            (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)))
        (hP_sub : P ⊆ primesUpTo N) (hP_ne5 : ∀ p ∈ P, p ≠ 5) :
        (S.card : ℝ) ≤
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
      apply mixed_polynomial N 25 b P S _ hsize bN hsubset _ (fun p n h => h.2) hP_sub
      intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp (hP_sub hp)).2
      exact off_count_modEq25_le' N p b t hpPrime (hP_ne5 p hp)
    have residue_class_card_bound100_of_subset
        (t25 t4 b : ℕ) (P S : Finset ℕ) (bN : b < N)
        (hsubset :
          S ⊆ P.biUnion (fun p =>
            (Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)))
        (hP_sub : P ⊆ primesUpTo N) (hP_ne2 : ∀ p ∈ P, p ≠ 2) (hP_ne5 : ∀ p ∈ P, p ≠ 5) :
        (S.card : ℝ) ≤
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
      apply mixed_polynomial N 100 b P S _ hsize bN hsubset _ (fun p n h => h.2.2) hP_sub
      intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp (hP_sub hp)).2
      exact off_count_modEq100_le' N p b t25 t4 hpPrime (hP_ne2 p hp) (hP_ne5 p hp)
    let A7A : Finset ℕ := A.filter (fun a => a % 25 = 7)
    let A18A : Finset ℕ := A.filter (fun a => a % 25 = 18)
    let Astar : Finset ℕ := A.filter (fun a => a % 25 ≠ 7 ∧ a % 25 ≠ 18)
    have hA7A_sub_A : A7A ⊆ A := by
      intro a ha
      exact (Finset.mem_filter.1 ha).1
    have hA18A_sub_A : A18A ⊆ A := by
      intro a ha
      exact (Finset.mem_filter.1 ha).1
    have hAstar_sub_A : Astar ⊆ A := by
      intro a ha
      exact (Finset.mem_filter.1 ha).1
    have hA7A_sub_range : A7A ⊆ Finset.range N := Finset.Subset.trans hA7A_sub_A hAsub
    have hA18A_sub_range : A18A ⊆ Finset.range N := Finset.Subset.trans hA18A_sub_A hAsub
    have hAstar_sub_range : Astar ⊆ Finset.range N := Finset.Subset.trans hAstar_sub_A hAsub
    have hA_decomp : A ⊆ A7A ∪ A18A ∪ Astar := by
      intro a ha
      by_cases h7 : a % 25 = 7
      · have : a ∈ A7A := by
          simp [A7A, ha, h7]
        exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl this)))
      · by_cases h18 : a % 25 = 18
        · have : a ∈ A18A := by
            simp [A18A, ha, h18]
          exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr this)))
        · have : a ∈ Astar := by
            simp [Astar, ha, h7, h18]
          exact Finset.mem_union.2 (Or.inr this)
    have hA_card_le_parts_nat : A.card ≤ A7A.card + A18A.card + Astar.card := by
      have hsubset : A ⊆ A7A ∪ A18A ∪ Astar := hA_decomp
      have hcard : A.card ≤ (A7A ∪ A18A ∪ Astar).card := Finset.card_le_card hsubset
      have hunion1 : (A7A ∪ A18A ∪ Astar).card ≤ (A7A ∪ A18A).card + Astar.card := by
        simpa [Finset.union_assoc] using (Finset.card_union_le (A7A ∪ A18A) Astar)
      have hunion2 : (A7A ∪ A18A).card ≤ A7A.card + A18A.card := Finset.card_union_le _ _
      have : A.card ≤ (A7A.card + A18A.card) + Astar.card := by
        have h1 : (A7A ∪ A18A).card + Astar.card ≤ (A7A.card + A18A.card) + Astar.card := by omega
        exact le_trans (le_trans hcard hunion1) h1
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    have Astar_bound_mod25 :
        (Astar.card : ℝ) ≤
          (46 : ℝ) * ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2))) + ((N : ℝ) / 2300) + 46*((2*N).sqrt : ℝ) := by
      classical
      have hsubset :
          Astar ⊆ (diagPrimesUpTo N).biUnion (fun p =>
            (Finset.range N).filter (fun n =>
              n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
        intro x hx
        have hxA : x ∈ A := hAstar_sub_A hx
        have hx_lt : x < N := by simpa [Finset.mem_range] using hAsub hxA
        have hx_mod_ne : x % 25 ≠ 7 ∧ x % 25 ≠ 18 := by
          simpa [Astar] using (Finset.mem_filter.1 hx).2
        have hnsq : ¬ Squarefree (x ^ 2 + 1) := by
          simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hAprop x hxA x hxA
        obtain ⟨p, hp, hp2div⟩ := prime_square_exists (n := x ^ 2 + 1) hnsq
        have hp_ne2 : p ≠ 2 := by
          intro hp2
          subst hp2
          have : 4 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_four_sq_add_one x) this
        have hp_gt2 : p > 2 := lt_of_le_of_ne hp.two_le (Ne.symm hp_ne2)
        have hp_mod4 : p % 4 = 1 :=
          prime_sq_divides_implies_one_mod_four p x hp hp_gt2 (by simpa [pow_two] using hp2div)
        have hp_ne5 : p ≠ 5 := by
          intro hp5
          subst hp5
          have : 25 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_25_sq_add_one_of_mod_ne x hx_mod_ne) this
        have hp_ge13 : 13 ≤ p := prime_ge_13_of_mod4_one_ne5 p hp hp_mod4 hp_ne5
        have hp_le : p ≤ N := by
          have hxx_lt : x ^ 2 + 1 < N ^ 2 := by
            have hx_le : x ≤ N - 1 := Nat.le_pred_of_lt hx_lt
            have hxx_le : x ^ 2 ≤ (N - 1) ^ 2 := Nat.pow_le_pow_left hx_le 2
            have : x ^ 2 + 1 ≤ (N - 1) ^ 2 + 1 := Nat.add_le_add_right hxx_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            exact lt_of_le_of_lt this hlt
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := x ^ 2 + 1) (Nat.succ_pos _) hxx_lt hp2div
        have hp_mem : p ∈ diagPrimesUpTo N := by
          have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
          simp [diagPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_mod4, hp_ge13]
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
        have : x ∈ (Finset.range N).filter (fun n =>
            n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1) := by
          simp [Finset.mem_filter, Finset.mem_range, hx_lt, hx_mod_ne, hp2div]
        exact this
      apply diagonal_polynomial N 25 Astar _ hsize hsubset
      · intro p hp
        have hp_prime : p.Prime := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
        have hp_mod4 : p % 4 = 1 := (Finset.mem_filter.1 hp).2.1
        have hp_ne5 : p ≠ 5 := by
          have hp_ge13 : 13 ≤ p := (Finset.mem_filter.1 hp).2.2
          omega
        exact diag_count_mod25_ne_7_18_le N p hp_prime hp_mod4 hp_ne5
      · intro p n hn
        obtain ⟨hlt,rest⟩ := Finset.mem_filter.mp hn
        exact ⟨Finset.mem_range.mp hlt,rest.2.2⟩
    have Astar_bound_mod50
        (hAstar_all_odd : ∀ x ∈ Astar, x % 2 = 1) :
        (Astar.card : ℝ) ≤
          (46 : ℝ) * ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2))) + ((N : ℝ) / 2300) + 46*((2*N).sqrt : ℝ) := by
      classical
      have hsubset :
          Astar ⊆ (diagPrimesUpTo N).biUnion (fun p =>
            (Finset.range N).filter (fun n =>
              n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
        intro x hx
        have hxA : x ∈ A := hAstar_sub_A hx
        have hx_lt : x < N := by simpa [Finset.mem_range] using hAsub hxA
        have hx_mod_ne : x % 25 ≠ 7 ∧ x % 25 ≠ 18 := by
          simpa [Astar] using (Finset.mem_filter.1 hx).2
        have hx_odd : x % 2 = 1 := hAstar_all_odd x hx
        have hnsq : ¬ Squarefree (x ^ 2 + 1) := by
          simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hAprop x hxA x hxA
        obtain ⟨p, hp, hp2div⟩ := prime_square_exists (n := x ^ 2 + 1) hnsq
        have hp_ne2 : p ≠ 2 := by
          intro hp2
          subst hp2
          have : 4 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_four_sq_add_one x) this
        have hp_gt2 : p > 2 := lt_of_le_of_ne hp.two_le (Ne.symm hp_ne2)
        have hp_mod4 : p % 4 = 1 :=
          prime_sq_divides_implies_one_mod_four p x hp hp_gt2 (by simpa [pow_two] using hp2div)
        have hp_ne5 : p ≠ 5 := by
          intro hp5
          subst hp5
          have : 25 ∣ x ^ 2 + 1 := by simpa [pow_two] using hp2div
          exact (not_dvd_25_sq_add_one_of_mod_ne x hx_mod_ne) this
        have hp_ge13 : 13 ≤ p := prime_ge_13_of_mod4_one_ne5 p hp hp_mod4 hp_ne5
        have hp_le : p ≤ N := by
          have hxx_lt : x ^ 2 + 1 < N ^ 2 := by
            have hx_le : x ≤ N - 1 := Nat.le_pred_of_lt hx_lt
            have hxx_le : x ^ 2 ≤ (N - 1) ^ 2 := Nat.pow_le_pow_left hx_le 2
            have : x ^ 2 + 1 ≤ (N - 1) ^ 2 + 1 := Nat.add_le_add_right hxx_le 1
            have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
            exact lt_of_le_of_lt this hlt
          exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := x ^ 2 + 1) (Nat.succ_pos _) hxx_lt hp2div
        have hp_mem : p ∈ diagPrimesUpTo N := by
          have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
          simp [diagPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_mod4, hp_ge13]
        refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
        have : x ∈ (Finset.range N).filter (fun n =>
            n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1) := by
          simp [Finset.mem_filter, Finset.mem_range, hx_lt, hx_odd, hx_mod_ne, hp2div]
        exact this
      apply diagonal_polynomial N 50 Astar _ hsize hsubset
      · intro p hp
        have hp_prime : p.Prime := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
        have hp_mod4 : p % 4 = 1 := (Finset.mem_filter.1 hp).2.1
        have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; omega
        have hp_ge13 : 13 ≤ p := (Finset.mem_filter.1 hp).2.2
        have hp_ne5 : p ≠ 5 := by omega
        exact diag_count_mod50odd_ne_7_18_le N p hp_prime hp_mod4 hp_ne2 hp_ne5
      · intro p n hn
        obtain ⟨hlt,rest⟩ := Finset.mem_filter.mp hn
        exact ⟨Finset.mem_range.mp hlt,rest.2.2.2⟩
    have case_Astar_empty (hAstar_empty : Astar = ∅) : A ⊆ A₇ N ∨ A ⊆ A₁₈ N := by
      have hA_sub_78 : A ⊆ A7A ∪ A18A := by
        intro a ha
        have : a ∈ A7A ∪ A18A ∪ Astar := hA_decomp ha
        simpa [hAstar_empty] using this
      by_cases hA7_empty : A7A = ∅
      · 
        right
        intro a ha
        have ha78 : a ∈ A7A ∪ A18A := hA_sub_78 ha
        have ha18 : a ∈ A18A := by
          rcases Finset.mem_union.1 ha78 with ha7 | ha18
          · simp [hA7_empty] at ha7
          · exact ha18
        have ha_range : a ∈ Finset.range N := hA18A_sub_range ha18
        have ha_mod : a % 25 = 18 := by
          simpa [A18A] using (Finset.mem_filter.1 ha18).2
        simp [A₁₈, ha_range, ha_mod]
      · by_cases hA18_empty : A18A = ∅
        · 
          left
          intro a ha
          have ha78 : a ∈ A7A ∪ A18A := hA_sub_78 ha
          have ha7 : a ∈ A7A := by
            rcases Finset.mem_union.1 ha78 with ha7 | ha18
            · exact ha7
            · simp [hA18_empty] at ha18
          have ha_range : a ∈ Finset.range N := hA7A_sub_range ha7
          have ha_mod : a % 25 = 7 := by
            simpa [A7A] using (Finset.mem_filter.1 ha7).2
          simp [A₇, ha_range, ha_mod]
        · 
          have hA7_nonempty : A7A.Nonempty := Finset.nonempty_iff_ne_empty.2 hA7_empty
          have hA18_nonempty : A18A.Nonempty := Finset.nonempty_iff_ne_empty.2 hA18_empty
          rcases hA7_nonempty with ⟨b7, hb7⟩
          rcases hA18_nonempty with ⟨b18, hb18⟩
          have hA7A_le :
              (A7A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
            have hb18A : b18 ∈ A := hA18A_sub_A hb18
            have hb18_lt : b18 < N := by simpa [Finset.mem_range] using hAsub hb18A
            have hb18_mod : b18 % 25 = 18 := by
              simpa [A18A] using (Finset.mem_filter.1 hb18).2
            have hsubset :
                A7A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA7A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod7 : a % 25 = 7 := by
                simpa [A7A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b18 * a + 1) := by
                have := hAprop b18 hb18A a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b18 * a + 1) := by
                exact cross_residue_18_7_not_div_25 b18 a hb18_mod ha_mod7
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b18 * a + 1) hnsq h25
              have hp_lt : p ≤ N := by
                have hab_lt : b18 * a + 1 < N ^ 2 := by
                  have hb18_le : b18 ≤ N - 1 := Nat.le_pred_of_lt hb18_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b18 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb18_le ha_le
                  have : b18 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b18 * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ no5PrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1) := by
                exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod7, hp2div⟩
              exact this
            have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2
            exact
              residue_class_card_bound_of_subset
                (t := 7)
                (b := b18)
                (P := no5PrimesUpTo N)
                (S := A7A)
                (by assumption)
                hsubset
                hP_sub
                hP_ne5
          have hA18A_le :
              (A18A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
            have hb7A : b7 ∈ A := hA7A_sub_A hb7
            have hb7_lt : b7 < N := by simpa [Finset.mem_range] using hAsub hb7A
            have hb7_mod : b7 % 25 = 7 := by
              simpa [A7A] using (Finset.mem_filter.1 hb7).2
            have hsubset :
                A18A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA18A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod18 : a % 25 = 18 := by
                simpa [A18A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b7 * a + 1) := by
                have := hAprop b7 hb7A a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b7 * a + 1) := by
                exact cross_residue_7_18_not_div_25 b7 a hb7_mod ha_mod18
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b7 * a + 1) hnsq h25
              have hp_lt : p ≤ N := by
                have hab_lt : b7 * a + 1 < N ^ 2 := by
                  have hb7_le : b7 ≤ N - 1 := Nat.le_pred_of_lt hb7_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b7 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb7_le ha_le
                  have : b7 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b7 * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ no5PrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1) := by
                exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod18, hp2div⟩
              exact this
            have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2
            exact
              residue_class_card_bound_of_subset
                (t := 18)
                (b := b7)
                (P := no5PrimesUpTo N)
                (S := A18A)
                (by assumption)
                hsubset
                hP_sub
                hP_ne5
          have hA_le : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) := by
            have hcard : A.card ≤ (A7A ∪ A18A).card := Finset.card_le_card hA_sub_78
            have : (A.card : ℝ) ≤ ((A7A ∪ A18A).card : ℝ) := by exact_mod_cast hcard
            have hunion : ((A7A ∪ A18A).card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) := by
              exact_mod_cast (Finset.card_union_le A7A A18A)
            exact le_trans this hunion
          have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 1000000 : ℝ)) * (N : ℝ) := by
            have hno5 : (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (413 : ℚ) / 1000 :=
              sum_no5PrimesUpTo_le N
            have hno5R : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ (413 : ℝ) / 25000 := by
              have hcast' : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (413 : ℝ) / 1000 := by
                have := Rat.cast_le (K := ℝ).mpr hno5
                simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
                exact this
              have heq : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
                  (1 / 25 : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
                simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
              have hmul : (1 / 25 : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (1 / 25 : ℝ) * ((413 : ℝ) / 1000) :=
                mul_le_mul_of_nonneg_left hcast' (by positivity)
              have hsum_nonneg : (0 : ℝ) ≤ (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) :=
                Finset.sum_nonneg (fun p _ => by positivity)
              nlinarith [hmul, hsum_nonneg]
            have herror' : ((N : ℝ) / 2300) ≤ δ * (N : ℝ) := herror
            have hA7 := hA7A_le
            have hA18 := hA18A_le
            have hsum_bound : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_no5 := by
              simpa [C_no5] using hno5R
            have hN_times_sum : (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                (N : ℝ) * C_no5 :=
              mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hNpos)
            have hA7_bound : (A7A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
              have h1 : (A7A.card : ℝ) ≤ (N : ℝ) * C_no5 + ((N : ℝ) / 2300) :=
                le_trans hA7 (add_le_add hN_times_sum (le_refl _))
              exact le_trans h1 (add_le_add (le_refl _) herror')
            have hA18_bound : (A18A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
              have h1 : (A18A.card : ℝ) ≤ (N : ℝ) * C_no5 + ((N : ℝ) / 2300) :=
                le_trans hA18 (add_le_add hN_times_sum (le_refl _))
              exact le_trans h1 (add_le_add (le_refl _) herror')
            have hA7_bound_num :
                (A7A.card : ℝ) ≤ (N : ℝ) * (413 / 25000 : ℝ) + δ * (N : ℝ) := by
              simpa [C_no5] using hA7_bound
            have hA18_bound_num :
                (A18A.card : ℝ) ≤ (N : ℝ) * (413 / 25000 : ℝ) + δ * (N : ℝ) := by
              simpa [C_no5] using hA18_bound
            nlinarith [hA_le, hA7_bound_num, hA18_bound_num, hNpos]
          exfalso
          exact (not_lt_of_ge hdense) hA_lt
    by_cases hAstar_empty : Astar = ∅
    · exact case_Astar_empty hAstar_empty
    · 
      have hAstar_nonempty : Astar.Nonempty := by
        exact Finset.nonempty_iff_ne_empty.2 hAstar_empty
      have case_Astar_nonempty_exists_even (hEven : ∃ b ∈ Astar, b % 2 = 0) : False := by
        rcases hEven with ⟨b, hbAstar, hbEven⟩
        have hbA : b ∈ A := hAstar_sub_A hbAstar
        have hb_lt : b < N := by simpa [Finset.mem_range] using hAsub hbA
        have hb_mod_ne : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := by
          simpa [Astar] using (Finset.mem_filter.1 hbAstar).2
        have hAstar_bound :
            (Astar.card : ℝ) ≤
              (46 : ℝ) * ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2))) + ((N : ℝ) / 2300) + 46*((2*N).sqrt : ℝ) :=
          Astar_bound_mod25
        have hA78_bound :
            ((A7A.card : ℝ) + (A18A.card : ℝ)) ≤
              2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300) := by
          have hbEven' : b % 2 = 0 := hbEven
          have hb_mod_ne' : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
          have hA7A_le :
              (A7A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
            have hsubset :
                A7A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA7A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod7 : a % 25 = 7 := by
                simpa [A7A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b * a + 1) := by
                have := hAprop b hbA a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b * a + 1) := by
                have := cross_residue_not_div_25 a b ha_mod7 hb_mod_ne'
                simp only [Nat.mul_comm a b] at this
                exact this
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b * a + 1) hnsq h25
              have hp_ne2 : p ≠ 2 := by
                have hodd : (b * a + 1) % 2 = 1 := by
                  have : 2 ∣ b * a := dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hbEven') a
                  have : (b * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                  omega
                exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
              have hp_lt : p ≤ N := by
                have hab_lt : b * a + 1 < N ^ 2 := by
                  have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                  have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ offPrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod7, hp2div⟩
              exact this
            have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2.2
            exact
              residue_class_card_bound_of_subset
                (t := 7)
                (b := b)
                (P := offPrimesUpTo N)
                (S := A7A)
                (by assumption)
                hsubset
                hP_sub
                hP_ne5
          have hA18A_le :
              (A18A.card : ℝ) ≤
                (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
            have hsubset :
                A18A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                  (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
              intro a ha
              have haA : a ∈ A := hA18A_sub_A ha
              have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
              have ha_mod18 : a % 25 = 18 := by
                simpa [A18A] using (Finset.mem_filter.1 ha).2
              have hnsq : ¬ Squarefree (b * a + 1) := by
                have := hAprop b hbA a haA
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
              have h25 : ¬ (25 ∣ b * a + 1) := by
                have := cross_residue_not_div_25_18 a b ha_mod18 hb_mod_ne'
                simp only [Nat.mul_comm a b] at this
                exact this
              obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b * a + 1) hnsq h25
              have hp_ne2 : p ≠ 2 := by
                have hodd : (b * a + 1) % 2 = 1 := by
                  have : 2 ∣ b * a := dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hbEven') a
                  have : (b * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                  omega
                exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
              have hp_lt : p ≤ N := by
                have hab_lt : b * a + 1 < N ^ 2 := by
                  have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                  have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                  have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                  have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                  have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                  exact lt_of_le_of_lt this hlt
                exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
              have hp_mem : p ∈ offPrimesUpTo N := by
                have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_lt
                simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
              refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
              have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod18, hp2div⟩
              exact this
            have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
              intro p hp
              exact (Finset.mem_filter.1 hp).1
            have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
              intro p hp
              exact (Finset.mem_filter.1 hp).2.2
            exact
              residue_class_card_bound_of_subset
                (t := 18)
                (b := b)
                (P := offPrimesUpTo N)
                (S := A18A)
                (by assumption)
                hsubset
                hP_sub
                hP_ne5
          nlinarith [hA7A_le, hA18A_le]
        have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
          exact_mod_cast hA_card_le_parts_nat
        have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_diag := by
          have hdiagQ : (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (1 : ℚ) / (359/5) :=
            sum_diagPrimesUpTo_le N
          have hcast' : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (1 : ℝ) / (359/5) := by
            have := Rat.cast_le (K := ℝ).mpr hdiagQ
            simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
            exact this
          have : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
              (1 / 25 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
            simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
          have hmul : (1 / 25 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
              (1 / 25 : ℝ) * ((1 : ℝ) / (359/5)) :=
            mul_le_mul_of_nonneg_left hcast' (by positivity)
          have : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ (1 : ℝ) / 1795 := by
            nlinarith [hmul]
          simpa [C_diag] using this
        have hoff : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_off := by
          have hoffQ : (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (163 : ℚ) / 1000 :=
            sum_offPrimesUpTo_le N
          have hcast' : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (163 : ℝ) / 1000 := by
            have := Rat.cast_le (K := ℝ).mpr hoffQ
            simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
            exact this
          have : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
              (1 / 25 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
            simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
          have hmul : (1 / 25 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
              (1 / 25 : ℝ) * ((163 : ℝ) / 1000) :=
            mul_le_mul_of_nonneg_left hcast' (by positivity)
          have : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ (163 : ℝ) / 25000 := by
            nlinarith [hmul]
          simpa [C_off] using this
        have herror' : ((N : ℝ) / 2300) ≤ δ * (N : ℝ) := herror
        have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 1000000 : ℝ)) * (N : ℝ) := by
          have hNdiag :
              (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                (N : ℝ) * C_diag :=
            mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
          have hNoff :
              (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                (N : ℝ) * C_off :=
            mul_le_mul_of_nonneg_left hoff (le_of_lt hNpos)
          have hAstar_explicit : (Astar.card : ℝ) ≤ 46 * ((N : ℝ) * C_diag) + δ * (N : ℝ) + (N : ℝ)/10000000 := by
            exact hAstar_bound.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hNdiag (by norm_num)) herror') hsqrt)
          have hA78_explicit :
              (A7A.card : ℝ) + (A18A.card : ℝ) ≤ 2 * (N : ℝ) * C_off + 2 * δ * (N : ℝ) := by
            have h1 := hA78_bound
            have h4 : 2 * ((N : ℝ) / 2300) ≤ 2 * δ * (N : ℝ) := by nlinarith [herror']
            have h3 :
                2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                  2 * (N : ℝ) * C_off := by
              have hmul :
                  (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                    (N : ℝ) * C_off :=
                hNoff
              have h2mul := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ 2 by norm_num)
              calc 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2))
                  = 2 * ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2))) := by ring
                _ ≤ 2 * ((N : ℝ) * C_off) := h2mul
                _ = 2 * (N : ℝ) * C_off := by ring
            have h5 : 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300) ≤
                      2 * (N : ℝ) * C_off + 2 * δ * (N : ℝ) := add_le_add h3 h4
            exact le_trans h1 h5
          have hAstar_explicit_num :
              (Astar.card : ℝ) ≤ 46 * ((N : ℝ) * ((1 : ℝ) / 1795)) + δ * (N : ℝ) + (N : ℝ)/10000000 := by
            simpa [C_diag] using hAstar_explicit
          have hA78_explicit_num :
              (A7A.card : ℝ) + (A18A.card : ℝ) ≤ 2 * (N : ℝ) * ((163 : ℝ) / 25000) + 2 * δ * (N : ℝ) := by
            simpa [C_off] using hA78_explicit
          nlinarith [hA_le_parts, hAstar_explicit_num, hA78_explicit_num, hNpos]
        exact (not_lt_of_ge hdense) hA_lt
      by_cases hEven : ∃ b ∈ Astar, b % 2 = 0
      · exfalso
        exact case_Astar_nonempty_exists_even hEven
      · 
        have hAstar_all_odd : ∀ b ∈ Astar, b % 2 = 1 := by
          intro b hb
          have hb2 : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
          cases hb2 with
          | inl h0 =>
              exfalso
              apply hEven
              exact ⟨b, hb, h0⟩
          | inr h1 => exact h1
        have case_Astar_all_odd_exists_even_in_A78
            (hAstar_all_odd : ∀ b ∈ Astar, b % 2 = 1)
            (hEven78 : (∃ b ∈ A7A, b % 2 = 0) ∨ (∃ b ∈ A18A, b % 2 = 0)) : False := by
          rcases hAstar_nonempty with ⟨b, hbAstar⟩
          have hbA : b ∈ A := hAstar_sub_A hbAstar
          have hb_lt : b < N := by simpa [Finset.mem_range] using hAsub hbA
          have hb_odd : b % 2 = 1 := hAstar_all_odd b hbAstar
          have hb_mod_ne : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := by
            simpa [Astar] using (Finset.mem_filter.1 hbAstar).2
          have hAstar_bound :
              (Astar.card : ℝ) ≤
                (46 : ℝ) * ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2))) + ((N : ℝ) / 2300) + 46*((2*N).sqrt : ℝ) :=
            Astar_bound_mod50 hAstar_all_odd
          cases hEven78 with
          | inl hA7_even =>
              rcases hA7_even with ⟨b7, hb7, hb7Even⟩
              have hb7A : b7 ∈ A := hA7A_sub_A hb7
              have hb7_lt : b7 < N := by simpa [Finset.mem_range] using hAsub hb7A
              have hb7_mod : b7 % 25 = 7 := by
                simpa [A7A] using (Finset.mem_filter.1 hb7).2
              have hA7_bound :
                  (A7A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset :
                    A7A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA7A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod7 : a % 25 = 7 := by
                    simpa [A7A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have hnsq' : ¬ Squarefree (a * b + 1) := by simp only [Nat.mul_comm b a] at hnsq; exact hnsq
                  obtain ⟨p, hp, hp5, hp2div'⟩ := must_have_other_prime_square a b ha_mod7 hb_mod_ne hnsq'
                  have hp2div : p ^ 2 ∣ b * a + 1 := by simp only [Nat.mul_comm a b] at hp2div'; exact hp2div'
                  have hp_le : p ≤ N := by
                    have hab_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ no5PrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod7, hp2div⟩
                  exact this
                have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2
                exact
                  residue_class_card_bound_of_subset
                    (t := 7)
                    (b := b)
                    (P := no5PrimesUpTo N)
                    (S := A7A)
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne5
              have hA18_bound :
                  (A18A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset :
                    A18A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA18A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod18 : a % 25 = 18 := by
                    simpa [A18A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b7 * a + 1) := by
                    have := hAprop b7 hb7A a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have h25 : ¬ (25 ∣ b7 * a + 1) := cross_residue_7_18_not_div_25 b7 a hb7_mod ha_mod18
                  obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b7 * a + 1) hnsq h25
                  have hp_ne2 : p ≠ 2 := by
                    have hodd : (b7 * a + 1) % 2 = 1 := by
                      have : 2 ∣ b7 := Nat.dvd_of_mod_eq_zero hb7Even
                      have : 2 ∣ b7 * a := dvd_mul_of_dvd_left this a
                      have : (b7 * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                      omega
                    exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
                  have hp_le : p ≤ N := by
                    have hab_lt : b7 * a + 1 < N ^ 2 := by
                      have hb7_le : b7 ≤ N - 1 := Nat.le_pred_of_lt hb7_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b7 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb7_le ha_le
                      have : b7 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b7 * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b7 * a + 1) := by
                    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod18, hp2div⟩
                  exact this
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound_of_subset
                    (t := 18)
                    (b := b7)
                    (P := offPrimesUpTo N)
                    (S := A18A)
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne5
              have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
                exact_mod_cast hA_card_le_parts_nat
              have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (1 : ℝ) / 3590 := by
                have hdiagQ : (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (1 : ℚ) / (359/5) :=
                  sum_diagPrimesUpTo_le N
                have hcast' : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (1 : ℝ) / (359/5) := by
                  have := Rat.cast_le (K := ℝ).mpr hdiagQ
                  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
                  exact this
                have : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) =
                    (1 / 50 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
                  simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
                have : (1 / 50 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                    (1 / 50 : ℝ) * ((1 : ℝ) / (359/5)) := by
                  exact mul_le_mul_of_nonneg_left hcast' (by positivity)
                nlinarith [this]
              have hno5 : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_no5 := by
                have hno5Q : (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (413 : ℚ) / 1000 :=
                  sum_no5PrimesUpTo_le N
                have hcast' : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (413 : ℝ) / 1000 := by
                  have := Rat.cast_le (K := ℝ).mpr hno5Q
                  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
                  exact this
                have : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
                    (1 / 25 : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
                  simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
                have : (1 / 25 : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                    (1 / 25 : ℝ) * ((413 : ℝ) / 1000) := by
                  exact mul_le_mul_of_nonneg_left hcast' (by positivity)
                have : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ (413 : ℝ) / 25000 := by
                  nlinarith [this]
                simpa [C_no5] using this
              have hoff : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_off := by
                have hoffQ : (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (163 : ℚ) / 1000 :=
                  sum_offPrimesUpTo_le N
                have hcast' : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (163 : ℝ) / 1000 := by
                  have := Rat.cast_le (K := ℝ).mpr hoffQ
                  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
                  exact this
                have : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
                    (1 / 25 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
                  simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
                have : (1 / 25 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                    (1 / 25 : ℝ) * ((163 : ℝ) / 1000) := by
                  exact mul_le_mul_of_nonneg_left hcast' (by positivity)
                have : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ (163 : ℝ) / 25000 := by
                  nlinarith [this]
                simpa [C_off] using this
              have herror' : ((N : ℝ) / 2300) ≤ δ * (N : ℝ) := herror
              have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 1000000 : ℝ)) * (N : ℝ) := by
                have hNdiag : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (N : ℝ) / 3590 := by
                  have := mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
                  simp only [one_div] at this ⊢
                  exact this
                have hNno5 :
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_no5 :=
                  mul_le_mul_of_nonneg_left hno5 (le_of_lt hNpos)
                have hNoff :
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_off :=
                  mul_le_mul_of_nonneg_left hoff (le_of_lt hNpos)
                have hAstar_explicit : (Astar.card : ℝ) ≤ 46 * ((N : ℝ) / 3590) + δ * (N : ℝ) + (N : ℝ)/10000000 := by
                  exact hAstar_bound.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hNdiag (by norm_num)) herror') hsqrt)
                have hA7_explicit : (A7A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) ≤
                            (N : ℝ) * C_no5 + δ * (N : ℝ) := add_le_add hNno5 herror'
                  exact le_trans hA7_bound h2
                have hA18_explicit : (A18A.card : ℝ) ≤ (N : ℝ) * C_off + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) ≤
                            (N : ℝ) * C_off + δ * (N : ℝ) := add_le_add hNoff herror'
                  exact le_trans hA18_bound h2
                have hA7_explicit_num :
                    (A7A.card : ℝ) ≤ (N : ℝ) * (413 / 25000 : ℝ) + δ * (N : ℝ) := by
                  simpa [C_no5] using hA7_explicit
                have hA18_explicit_num :
                    (A18A.card : ℝ) ≤ (N : ℝ) * ((163 : ℝ) / 25000) + δ * (N : ℝ) := by
                  simpa [C_off] using hA18_explicit
                nlinarith [hA_le_parts, hAstar_explicit, hA7_explicit_num, hA18_explicit_num, hNpos]
              exact (not_lt_of_ge hdense) hA_lt
          | inr hA18_even =>
              rcases hA18_even with ⟨b18, hb18, hb18Even⟩
              have hb18A : b18 ∈ A := hA18A_sub_A hb18
              have hb18_lt : b18 < N := by simpa [Finset.mem_range] using hAsub hb18A
              have hb18_mod : b18 % 25 = 18 := by
                simpa [A18A] using (Finset.mem_filter.1 hb18).2
              have hA18_bound :
                  (A18A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset :
                    A18A ⊆ (no5PrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA18A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod18 : a % 25 = 18 := by
                    simpa [A18A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have hnsq' : ¬ Squarefree (a * b + 1) := by simp only [Nat.mul_comm b a] at hnsq; exact hnsq
                  obtain ⟨p, hp, hp5, hp2div'⟩ := must_have_other_prime_square_18 a b ha_mod18 hb_mod_ne hnsq'
                  have hp2div : p ^ 2 ∣ b * a + 1 := by simp only [Nat.mul_comm a b] at hp2div'; exact hp2div'
                  have hp_le : p ≤ N := by
                    have hab_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ no5PrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [no5PrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ p ^ 2 ∣ b * a + 1) := by
                    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod18, hp2div⟩
                  exact this
                have hP_sub : no5PrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ no5PrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2
                exact
                  residue_class_card_bound_of_subset
                    (t := 18)
                    (b := b)
                    (P := no5PrimesUpTo N)
                    (S := A18A)
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne5
              have hA7_bound :
                  (A7A.card : ℝ) ≤
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset :
                    A7A ⊆ (offPrimesUpTo N).biUnion (fun p =>
                      (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1)) := by
                  intro a ha
                  have haA : a ∈ A := hA7A_sub_A ha
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha_mod7 : a % 25 = 7 := by
                    simpa [A7A] using (Finset.mem_filter.1 ha).2
                  have hnsq : ¬ Squarefree (b18 * a + 1) := by
                    have := hAprop b18 hb18A a haA
                    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                  have h25 : ¬ (25 ∣ b18 * a + 1) := cross_residue_18_7_not_div_25 b18 a hb18_mod ha_mod7
                  obtain ⟨p, hp, hp5, hp2div⟩ := prime_square_exists_ne5 (n := b18 * a + 1) hnsq h25
                  have hp_ne2 : p ≠ 2 := by
                    have hodd : (b18 * a + 1) % 2 = 1 := by
                      have : 2 ∣ b18 := Nat.dvd_of_mod_eq_zero hb18Even
                      have : 2 ∣ b18 * a := dvd_mul_of_dvd_left this a
                      have : (b18 * a) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
                      omega
                    exact prime_ne_two_of_sq_dvd_odd (hn := hodd) hp2div
                  have hp_le : p ≤ N := by
                    have hab_lt : b18 * a + 1 < N ^ 2 := by
                      have hb18_le : b18 ≤ N - 1 := Nat.le_pred_of_lt hb18_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hab_le : b18 * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb18_le ha_le
                      have : b18 * a + 1 ≤ (N - 1) * (N - 1) + 1 := Nat.add_le_add_right hab_le 1
                      have hlt : (N - 1) * (N - 1) + 1 < N ^ 2 := sq_pred_add_one_lt_sq N hN100
                      exact lt_of_le_of_lt this hlt
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b18 * a + 1) (Nat.succ_pos _) hab_lt hp2div
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    have hp_range : p < N + 1 := Nat.lt_succ_of_le hp_le
                    simp [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range, hp, hp_range, hp_ne2, hp5]
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, ?_⟩
                  have : a ∈ (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ p ^ 2 ∣ b18 * a + 1) := by
                    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha_mod7, hp2div⟩
                  exact this
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound_of_subset
                    (t := 7)
                    (b := b18)
                    (P := offPrimesUpTo N)
                    (S := A7A)
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne5
              have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
                exact_mod_cast hA_card_le_parts_nat
              have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (1 : ℝ) / 3590 := by
                have hdiagQ : (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (1 : ℚ) / (359/5) :=
                  sum_diagPrimesUpTo_le N
                have hcast' : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (1 : ℝ) / (359/5) := by
                  have := Rat.cast_le (K := ℝ).mpr hdiagQ
                  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
                  exact this
                have : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) =
                    (1 / 50 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
                  simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
                have : (1 / 50 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                    (1 / 50 : ℝ) * ((1 : ℝ) / (359/5)) := by
                  exact mul_le_mul_of_nonneg_left hcast' (by positivity)
                nlinarith [this]
              have hno5 : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_no5 := by
                have hno5Q : (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (413 : ℚ) / 1000 :=
                  sum_no5PrimesUpTo_le N
                have hcast' : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (413 : ℝ) / 1000 := by
                  have := Rat.cast_le (K := ℝ).mpr hno5Q
                  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
                  exact this
                have : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
                    (1 / 25 : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
                  simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
                have : (1 / 25 : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                    (1 / 25 : ℝ) * ((413 : ℝ) / 1000) := by
                  exact mul_le_mul_of_nonneg_left hcast' (by positivity)
                have : (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ (413 : ℝ) / 25000 := by
                  nlinarith [this]
                simpa [C_no5] using this
              have hoff : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ C_off := by
                have hoffQ : (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (163 : ℚ) / 1000 :=
                  sum_offPrimesUpTo_le N
                have hcast' : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (163 : ℝ) / 1000 := by
                  have := Rat.cast_le (K := ℝ).mpr hoffQ
                  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
                  exact this
                have : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) =
                    (1 / 25 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
                  simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
                have : (1 / 25 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                    (1 / 25 : ℝ) * ((163 : ℝ) / 1000) := by
                  exact mul_le_mul_of_nonneg_left hcast' (by positivity)
                have : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤ (163 : ℝ) / 25000 := by
                  nlinarith [this]
                simpa [C_off] using this
              have herror' : ((N : ℝ) / 2300) ≤ δ * (N : ℝ) := herror
              have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 1000000 : ℝ)) * (N : ℝ) := by
                have hNdiag : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (N : ℝ) / 3590 := by
                  have := mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
                  simp only [one_div] at this ⊢
                  exact this
                have hNno5 :
                    (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_no5 :=
                  mul_le_mul_of_nonneg_left hno5 (le_of_lt hNpos)
                have hNoff :
                    (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) ≤
                      (N : ℝ) * C_off :=
                  mul_le_mul_of_nonneg_left hoff (le_of_lt hNpos)
                have hAstar_explicit : (Astar.card : ℝ) ≤ 46 * ((N : ℝ) / 3590) + δ * (N : ℝ) + (N : ℝ)/10000000 := by
                  exact hAstar_bound.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hNdiag (by norm_num)) herror') hsqrt)
                have hA7_explicit : (A7A.card : ℝ) ≤ (N : ℝ) * C_off + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) ≤
                            (N : ℝ) * C_off + δ * (N : ℝ) := add_le_add hNoff herror'
                  exact le_trans hA7_bound h2
                have hA18_explicit : (A18A.card : ℝ) ≤ (N : ℝ) * C_no5 + δ * (N : ℝ) := by
                  have h2 : (N : ℝ) * (∑ p ∈ no5PrimesUpTo N, (1 : ℝ) / (25 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) ≤
                            (N : ℝ) * C_no5 + δ * (N : ℝ) := add_le_add hNno5 herror'
                  exact le_trans hA18_bound h2
                have hA7_explicit_num :
                    (A7A.card : ℝ) ≤ (N : ℝ) * ((163 : ℝ) / 25000) + δ * (N : ℝ) := by
                  simpa [C_off] using hA7_explicit
                have hA18_explicit_num :
                    (A18A.card : ℝ) ≤ (N : ℝ) * (413 / 25000 : ℝ) + δ * (N : ℝ) := by
                  simpa [C_no5] using hA18_explicit
                nlinarith [hA_le_parts, hAstar_explicit, hA7_explicit_num, hA18_explicit_num, hNpos]
              exact (not_lt_of_ge hdense) hA_lt
        have case_all_odd
            (hAstar_all_odd : ∀ b ∈ Astar, b % 2 = 1)
            (hEven78 : ¬((∃ b ∈ A7A, b % 2 = 0) ∨ (∃ b ∈ A18A, b % 2 = 0))) : False := by
          rcases hAstar_nonempty with ⟨b, hbAstar⟩
          have hbA : b ∈ A := hAstar_sub_A hbAstar
          have hb_lt : b < N := by simpa [Finset.mem_range] using hAsub hbA
          have hb_odd : b % 2 = 1 := hAstar_all_odd b hbAstar
          have hb_mod_ne : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := by
            simpa [Astar] using (Finset.mem_filter.1 hbAstar).2
          have hAstar_bound :
              (Astar.card : ℝ) ≤
                (46 : ℝ) * ((N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2))) + ((N : ℝ) / 2300) + 46*((2*N).sqrt : ℝ) :=
            Astar_bound_mod50 hAstar_all_odd
          set_option maxHeartbeats 1600000 in
          have hA78_bound : (A7A.card : ℝ) + (A18A.card : ℝ) ≤ (N : ℝ) / 50 + 2 +
              2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300) := by
            push Not at hEven78
            have hA7_all_odd : ∀ a ∈ A7A, a % 2 = 1 := fun a ha => by
              have hne := hEven78.1 a ha; omega
            have hA18_all_odd : ∀ a ∈ A18A, a % 2 = 1 := fun a ha => by
              have hne := hEven78.2 a ha; omega
            have hb_mod4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
            let S7 := (Finset.range N).filter (fun a => a % 100 = 7)
            let S57 := (Finset.range N).filter (fun a => a % 100 = 57)
            let S43 := (Finset.range N).filter (fun a => a % 100 = 43)
            let S93 := (Finset.range N).filter (fun a => a % 100 = 93)
            have hA7_sub : A7A ⊆ S7 ∪ S57 := by
              intro a ha
              have h25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 ha).2
              have hodd : a % 2 = 1 := hA7_all_odd a ha
              have ha_range : a ∈ Finset.range N := hA7A_sub_range ha
              have ha_lt : a < N := Finset.mem_range.1 ha_range
              have hmod : a % 100 = 7 ∨ a % 100 = 57 := by omega
              rcases hmod with h | h
              · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
            have hA18_sub : A18A ⊆ S43 ∪ S93 := by
              intro a ha
              have h25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 ha).2
              have hodd : a % 2 = 1 := hA18_all_odd a ha
              have ha_range : a ∈ Finset.range N := hA18A_sub_range ha
              have ha_lt : a < N := Finset.mem_range.1 ha_range
              have hmod : a % 100 = 43 ∨ a % 100 = 93 := by omega
              rcases hmod with h | h
              · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, h⟩)
            rcases hb_mod4 with hb1 | hb3
            · 
              have hfree7 : ((A7A.filter (·%100=7)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
                have hsub : A7A.filter (·%100=7) ⊆ S7 := Finset.filter_subset_filter _ (fun _ h => hA7A_sub_range h)
                have hS7_card : S7.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 7
                calc ((A7A.filter (·%100=7)).card : ℝ)
                    ≤ (S7.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
                  _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS7_card
                  _ ≤ (N : ℝ) / 100 + 1 := by
                      have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
                      rw [this]
                      have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
                      linarith
              have hfree43 : ((A18A.filter (·%100=43)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
                have hsub : A18A.filter (·%100=43) ⊆ S43 := Finset.filter_subset_filter _ (fun _ h => hA18A_sub_range h)
                have hS43_card : S43.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 43
                calc ((A18A.filter (·%100=43)).card : ℝ)
                    ≤ (S43.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
                  _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS43_card
                  _ ≤ (N : ℝ) / 100 + 1 := by
                      have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
                      rw [this]
                      have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
                      linarith
              have hfree_bound : (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) ≤ (N : ℝ) / 50 + 2 := by
                linarith [hfree7, hfree43]
              have hsieve7_bound : ((A7A.filter (·%100=57)).card : ℝ) ≤
                  (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset : A7A.filter (·%100=57) ⊆ (offPrimesUpTo N).biUnion (fun p =>
                    (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ a ≡ 1 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA7 : a ∈ A7A := (Finset.mem_filter.1 ha).1
                  have ha100 : a % 100 = 57 := (Finset.mem_filter.1 ha).2
                  have haA : a ∈ A := hA7A_sub_A haA7
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 haA7).2
                  have ha4 : a % 4 = 1 := by omega
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA
                    simpa [mul_comm] using this
                  have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
                    intro hdvd
                    have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
                    have h1_mod4 : (b * a + 1) % 4 = 2 := by omega
                    have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
                    omega
                  obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
                  have hp_ne2 : p ≠ 2 := by
                    intro hp2; subst hp2
                    exact h4_ndvd hp2_dvd
                  have hp_ne5 : p ≠ 5 := by
                    intro hp5; subst hp5
                    have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
                    have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
                    have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
                    have ha_mod : Nat.ModEq 25 a 7 := by unfold Nat.ModEq; simp [ha25]
                    have heq : Nat.ModEq 25 (b * a) (b * 7) := Nat.ModEq.mul_left b ha_mod
                    have hb7 : (b * 7 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
                    have hb_mod25 : b % 25 = 7 := by omega
                    exact hb25.1 hb_mod25
                  have hp_gt2 : p > 2 := lt_of_le_of_ne hp_prime.two_le (Ne.symm hp_ne2)
                  have hp_le : p ≤ N := by
                    have hba_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
                      have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
                      omega
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
                    exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound100_of_subset
                    (t25 := 7)
                    (t4 := 1)
                    (b := b)
                    (P := offPrimesUpTo N)
                    (S := A7A.filter (· % 100 = 57))
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne2
                    hP_ne5
              have hsieve18_bound : ((A18A.filter (·%100=93)).card : ℝ) ≤
                  (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset : A18A.filter (·%100=93) ⊆ (offPrimesUpTo N).biUnion (fun p =>
                    (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ a ≡ 1 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA18 : a ∈ A18A := (Finset.mem_filter.1 ha).1
                  have ha100 : a % 100 = 93 := (Finset.mem_filter.1 ha).2
                  have haA : a ∈ A := hA18A_sub_A haA18
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 haA18).2
                  have ha4 : a % 4 = 1 := by omega
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA
                    simpa [mul_comm] using this
                  have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
                    intro hdvd
                    have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
                    have h1_mod4 : (b * a + 1) % 4 = 2 := by omega
                    have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
                    omega
                  obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
                  have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; exact h4_ndvd hp2_dvd
                  have hp_ne5 : p ≠ 5 := by
                    intro hp5; subst hp5
                    have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
                    have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
                    have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
                    have ha_mod : Nat.ModEq 25 a 18 := by unfold Nat.ModEq; simp [ha25]
                    have heq : Nat.ModEq 25 (b * a) (b * 18) := Nat.ModEq.mul_left b ha_mod
                    have hb18 : (b * 18 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
                    have hb_mod25 : b % 25 = 18 := by omega
                    exact hb25.2 hb_mod25
                  have hp_gt2 : p > 2 := lt_of_le_of_ne hp_prime.two_le (Ne.symm hp_ne2)
                  have hp_le : p ≤ N := by
                    have hba_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
                      have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
                      omega
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
                    exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound100_of_subset
                    (t25 := 18)
                    (t4 := 1)
                    (b := b)
                    (P := offPrimesUpTo N)
                    (S := A18A.filter (· % 100 = 93))
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne2
                    hP_ne5
              have hA7_split : A7A.card ≤ (A7A.filter (·%100=7)).card + (A7A.filter (·%100=57)).card := by
                have h_union : A7A = A7A.filter (·%100=7) ∪ A7A.filter (·%100=57) := by
                  ext a; simp only [Finset.mem_union, Finset.mem_filter]
                  constructor
                  · intro ha
                    have h25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 ha).2
                    have hodd : a % 2 = 1 := hA7_all_odd a ha
                    have hmod : a % 100 = 7 ∨ a % 100 = 57 := by omega
                    rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
                  · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
                have hcard_eq : A7A.card = (A7A.filter (·%100=7) ∪ A7A.filter (·%100=57)).card := by
                  conv_lhs => rw [h_union]
                rw [hcard_eq]
                exact Finset.card_union_le (A7A.filter (· % 100 = 7)) (A7A.filter (· % 100 = 57))
              have hA18_split : A18A.card ≤ (A18A.filter (·%100=43)).card + (A18A.filter (·%100=93)).card := by
                have h_union : A18A = A18A.filter (·%100=43) ∪ A18A.filter (·%100=93) := by
                  ext a; simp only [Finset.mem_union, Finset.mem_filter]
                  constructor
                  · intro ha
                    have h25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 ha).2
                    have hodd : a % 2 = 1 := hA18_all_odd a ha
                    have hmod : a % 100 = 43 ∨ a % 100 = 93 := by omega
                    rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
                  · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
                have hcard_eq : A18A.card = (A18A.filter (·%100=43) ∪ A18A.filter (·%100=93)).card := by
                  conv_lhs => rw [h_union]
                rw [hcard_eq]
                exact Finset.card_union_le (A18A.filter (· % 100 = 43)) (A18A.filter (· % 100 = 93))
              have hA7_real : (A7A.card : ℝ) ≤ ((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ) := by
                exact_mod_cast hA7_split
              have hA18_real : (A18A.card : ℝ) ≤ ((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ) := by
                exact_mod_cast hA18_split
              calc (A7A.card : ℝ) + (A18A.card : ℝ)
                  ≤ (((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ)) +
                    (((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by linarith
                _ = (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) +
                    (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by ring
                _ ≤ ((N : ℝ) / 50 + 2) + (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by linarith [hfree_bound]
                _ ≤ ((N : ℝ) / 50 + 2) + ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300)) +
                    ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300)) := by linarith [hsieve7_bound, hsieve18_bound]
                _ = (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300) := by ring
            · 
              set_option maxHeartbeats 1600000 in
              have hfree_bound : (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) ≤ (N : ℝ) / 50 + 2 := by
                have h57_le : ((A7A.filter (·%100=57)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
                  have hS57_card : S57.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 57
                  have hsub : A7A.filter (·%100=57) ⊆ S57 := Finset.filter_subset_filter _ (fun _ h => hA7A_sub_range h)
                  calc ((A7A.filter (·%100=57)).card : ℝ)
                      ≤ (S57.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
                    _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS57_card
                    _ ≤ (N : ℝ) / 100 + 1 := by
                        have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
                        rw [this]
                        have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
                        linarith
                have h93_le : ((A18A.filter (·%100=93)).card : ℝ) ≤ (N : ℝ) / 100 + 1 := by
                  have hS93_card : S93.card ≤ N / 100 + 1 := card_filter_mod_eq_le N 100 93
                  have hsub : A18A.filter (·%100=93) ⊆ S93 := Finset.filter_subset_filter _ (fun _ h => hA18A_sub_range h)
                  calc ((A18A.filter (·%100=93)).card : ℝ)
                      ≤ (S93.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
                    _ ≤ (N / 100 + 1 : ℕ) := by exact_mod_cast hS93_card
                    _ ≤ (N : ℝ) / 100 + 1 := by
                        have : ((N / 100 + 1 : ℕ) : ℝ) = ((N / 100 : ℕ) : ℝ) + 1 := by simp
                        rw [this]
                        have hdiv : ((N / 100 : ℕ) : ℝ) ≤ (N : ℝ) / 100 := Nat.cast_div_le
                        linarith
                linarith [h57_le, h93_le]
              set_option maxHeartbeats 1600000 in
              have hsieve7_bound : ((A7A.filter (·%100=7)).card : ℝ) ≤
                  (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset : A7A.filter (·%100=7) ⊆ (offPrimesUpTo N).biUnion (fun p =>
                    (Finset.range N).filter (fun a => a ≡ 7 [MOD 25] ∧ a ≡ 3 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA7 : a ∈ A7A := (Finset.mem_filter.1 ha).1
                  have ha100 : a % 100 = 7 := (Finset.mem_filter.1 ha).2
                  have haA : a ∈ A := hA7A_sub_A haA7
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 haA7).2
                  have ha4 : a % 4 = 3 := by omega
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA; simpa [mul_comm] using this
                  have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
                    intro hdvd
                    have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
                    have h_mod4 : (b * a + 1) % 4 = 2 := by omega
                    have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
                    omega
                  obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
                  have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; exact h4_ndvd hp2_dvd
                  have hp_ne5 : p ≠ 5 := by
                    intro hp5; subst hp5
                    have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
                    have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
                    have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
                    have ha_mod : Nat.ModEq 25 a 7 := by unfold Nat.ModEq; simp [ha25]
                    have heq : Nat.ModEq 25 (b * a) (b * 7) := Nat.ModEq.mul_left b ha_mod
                    have hb7 : (b * 7 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
                    have hb_mod25 : b % 25 = 7 := by omega
                    exact hb25.1 hb_mod25
                  have hp_le : p ≤ N := by
                    have hba_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
                      have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
                      omega
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
                    exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound100_of_subset
                    (t25 := 7)
                    (t4 := 3)
                    (b := b)
                    (P := offPrimesUpTo N)
                    (S := A7A.filter (· % 100 = 7))
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne2
                    hP_ne5
              have hsieve18_bound : ((A18A.filter (·%100=43)).card : ℝ) ≤
                  (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300) := by
                have hsubset : A18A.filter (·%100=43) ⊆ (offPrimesUpTo N).biUnion (fun p =>
                    (Finset.range N).filter (fun a => a ≡ 18 [MOD 25] ∧ a ≡ 3 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)) := by
                  intro a ha
                  have haA18 : a ∈ A18A := (Finset.mem_filter.1 ha).1
                  have ha100 : a % 100 = 43 := (Finset.mem_filter.1 ha).2
                  have haA : a ∈ A := hA18A_sub_A haA18
                  have ha_lt : a < N := by simpa [Finset.mem_range] using hAsub haA
                  have ha25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 haA18).2
                  have ha4 : a % 4 = 3 := by omega
                  have hnsq : ¬ Squarefree (b * a + 1) := by
                    have := hAprop b hbA a haA; simpa [mul_comm] using this
                  have h4_ndvd : ¬ (4 ∣ b * a + 1) := by
                    intro hdvd
                    have hba_mod4 : (b * a) % 4 = 1 := by rw [Nat.mul_mod]; simp_all
                    have h_mod4 : (b * a + 1) % 4 = 2 := by omega
                    have h0_mod4 : (b * a + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.1 hdvd
                    omega
                  obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_square_exists hnsq
                  have hp_ne2 : p ≠ 2 := by intro hp2; subst hp2; exact h4_ndvd hp2_dvd
                  have hp_ne5 : p ≠ 5 := by
                    intro hp5; subst hp5
                    have h25_dvd : 25 ∣ b * a + 1 := hp2_dvd
                    have hb25 : b % 25 ≠ 7 ∧ b % 25 ≠ 18 := hb_mod_ne
                    have h0 : (b * a + 1) % 25 = 0 := Nat.dvd_iff_mod_eq_zero.1 h25_dvd
                    have ha_mod : Nat.ModEq 25 a 18 := by unfold Nat.ModEq; simp [ha25]
                    have heq : Nat.ModEq 25 (b * a) (b * 18) := Nat.ModEq.mul_left b ha_mod
                    have hb18 : (b * 18 + 1) % 25 = 0 := by rw [← heq.add_right 1]; exact h0
                    have hb_mod25 : b % 25 = 18 := by omega
                    exact hb25.2 hb_mod25
                  have hp_le : p ≤ N := by
                    have hba_lt : b * a + 1 < N ^ 2 := by
                      have hb_le : b ≤ N - 1 := Nat.le_pred_of_lt hb_lt
                      have ha_le : a ≤ N - 1 := Nat.le_pred_of_lt ha_lt
                      have hba_le : b * a ≤ (N - 1) * (N - 1) := Nat.mul_le_mul hb_le ha_le
                      have : b * a + 1 ≤ (N - 1) ^ 2 + 1 := by simpa [pow_two] using Nat.add_le_add_right hba_le 1
                      have hlt : (N - 1) ^ 2 + 1 < N ^ 2 := by simpa [pow_two] using sq_pred_add_one_lt_sq N hN100
                      omega
                    exact prime_le_of_sq_dvd_lt_sq (p := p) (N := N) (X := b * a + 1) (Nat.succ_pos _) hba_lt hp2_dvd
                  have hp_mem : p ∈ offPrimesUpTo N := by
                    simp only [offPrimesUpTo, primesUpTo, Finset.mem_filter, Finset.mem_range]
                    exact ⟨⟨Nat.lt_succ_of_le hp_le, hp_prime⟩, hp_ne2, hp_ne5⟩
                  refine Finset.mem_biUnion.2 ⟨p, hp_mem, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha_lt, ?_, ?_, hp2_dvd⟩⟩ <;> simp [Nat.ModEq, ha25, ha4]
                have hP_sub : offPrimesUpTo N ⊆ primesUpTo N := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).1
                have hP_ne2 : ∀ p ∈ offPrimesUpTo N, p ≠ 2 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.1
                have hP_ne5 : ∀ p ∈ offPrimesUpTo N, p ≠ 5 := by
                  intro p hp
                  exact (Finset.mem_filter.1 hp).2.2
                exact
                  residue_class_card_bound100_of_subset
                    (t25 := 18)
                    (t4 := 3)
                    (b := b)
                    (P := offPrimesUpTo N)
                    (S := A18A.filter (· % 100 = 43))
                    (by assumption)
                    hsubset
                    hP_sub
                    hP_ne2
                    hP_ne5
              have hA7_split : A7A.card ≤ (A7A.filter (·%100=7)).card + (A7A.filter (·%100=57)).card := by
                have h_union : A7A = A7A.filter (·%100=7) ∪ A7A.filter (·%100=57) := by
                  ext a; simp only [Finset.mem_union, Finset.mem_filter]
                  constructor
                  · intro ha
                    have h25 : a % 25 = 7 := by simpa [A7A] using (Finset.mem_filter.1 ha).2
                    have hodd : a % 2 = 1 := hA7_all_odd a ha
                    have hmod : a % 100 = 7 ∨ a % 100 = 57 := by omega
                    rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
                  · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
                have hcard_eq : A7A.card = (A7A.filter (·%100=7) ∪ A7A.filter (·%100=57)).card := by
                  conv_lhs => rw [h_union]
                rw [hcard_eq]
                exact Finset.card_union_le (A7A.filter (· % 100 = 7)) (A7A.filter (· % 100 = 57))
              have hA18_split : A18A.card ≤ (A18A.filter (·%100=43)).card + (A18A.filter (·%100=93)).card := by
                have h_union : A18A = A18A.filter (·%100=43) ∪ A18A.filter (·%100=93) := by
                  ext a; simp only [Finset.mem_union, Finset.mem_filter]
                  constructor
                  · intro ha
                    have h25 : a % 25 = 18 := by simpa [A18A] using (Finset.mem_filter.1 ha).2
                    have hodd : a % 2 = 1 := hA18_all_odd a ha
                    have hmod : a % 100 = 43 ∨ a % 100 = 93 := by omega
                    rcases hmod with h | h <;> [left; right] <;> exact ⟨ha, h⟩
                  · intro ha; rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
                have hcard_eq : A18A.card = (A18A.filter (·%100=43) ∪ A18A.filter (·%100=93)).card := by
                  conv_lhs => rw [h_union]
                rw [hcard_eq]
                exact Finset.card_union_le (A18A.filter (· % 100 = 43)) (A18A.filter (· % 100 = 93))
              have hA7_real : (A7A.card : ℝ) ≤ ((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ) := by
                exact_mod_cast hA7_split
              have hA18_real : (A18A.card : ℝ) ≤ ((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ) := by
                exact_mod_cast hA18_split
              calc (A7A.card : ℝ) + (A18A.card : ℝ)
                  ≤ (((A7A.filter (·%100=7)).card : ℝ) + ((A7A.filter (·%100=57)).card : ℝ)) +
                    (((A18A.filter (·%100=43)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) := by linarith
                _ = (((A7A.filter (·%100=57)).card : ℝ) + ((A18A.filter (·%100=93)).card : ℝ)) +
                    (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) := by ring
                _ ≤ ((N : ℝ) / 50 + 2) + (((A7A.filter (·%100=7)).card : ℝ) + ((A18A.filter (·%100=43)).card : ℝ)) := by linarith [hfree_bound]
                _ ≤ ((N : ℝ) / 50 + 2) + ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300)) +
                    ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + ((N : ℝ) / 2300)) := by linarith [hsieve7_bound, hsieve18_bound]
                _ = (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300) := by ring
          set_option maxHeartbeats 1600000 in
          have hA_le_parts : (A.card : ℝ) ≤ (A7A.card : ℝ) + (A18A.card : ℝ) + (Astar.card : ℝ) := by
            exact_mod_cast hA_card_le_parts_nat
          set_option maxHeartbeats 1600000 in
          have hdiag : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (1 : ℝ) / 3590 := by
            have hdiagQ : (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (1 : ℚ) / (359/5) :=
              sum_diagPrimesUpTo_le N
            have hcast' : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (1 : ℝ) / (359/5) := by
              have := Rat.cast_le (K := ℝ).mpr hdiagQ
              simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
              exact this
            have : (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) =
                (1 / 50 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
              simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
            have : (1 / 50 : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                (1 / 50 : ℝ) * ((1 : ℝ) / (359/5)) := by
              exact mul_le_mul_of_nonneg_left hcast' (by positivity)
            nlinarith [this]
          have hoff100 : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) ≤ (163 : ℝ) / 100000 := by
            have hoffQ : (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ) : ℚ) ≤ (163 : ℚ) / 1000 :=
              sum_offPrimesUpTo_le N
            have hcast' : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (163 : ℝ) / 1000 := by
              have := Rat.cast_le (K := ℝ).mpr hoffQ
              simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast] at this
              exact this
            have : (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) =
                (1 / 100 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
              simp [div_eq_mul_inv, mul_sum, mul_left_comm, mul_comm]
            have : (1 / 100 : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
                (1 / 100 : ℝ) * ((163 : ℝ) / 1000) := by
              exact mul_le_mul_of_nonneg_left hcast' (by positivity)
            nlinarith [this]
          have herror' : ((N : ℝ) / 2300) ≤ δ * (N : ℝ) := herror
          have hA_lt : (A.card : ℝ) < (1 / 25 - (1 / 1000000 : ℝ)) * (N : ℝ) := by
            have hNdiag : (N : ℝ) * (∑ p ∈ diagPrimesUpTo N, (1 : ℝ) / (50 * (p : ℝ) ^ 2)) ≤ (N : ℝ) / 3590 := by
              have := mul_le_mul_of_nonneg_left hdiag (le_of_lt hNpos)
              simp only [one_div] at this ⊢
              exact this
            have hNoff100 : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) ≤ (N : ℝ) * (163 / 100000) :=
              mul_le_mul_of_nonneg_left hoff100 (le_of_lt hNpos)
            have hAstar_explicit : (Astar.card : ℝ) ≤ 46 * ((N : ℝ) / 3590) + δ * (N : ℝ) + (N : ℝ)/10000000 := by
              exact hAstar_bound.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hNdiag (by norm_num)) herror') hsqrt)
            have hA78_explicit : (A7A.card : ℝ) + (A18A.card : ℝ) ≤ (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by
              have herror2 : 2 * ((N : ℝ) / 2300) ≤ 2 * δ * (N : ℝ) := by nlinarith [herror']
              have h2 : 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300) ≤
                        2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by
                have hmul : (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) ≤ (N : ℝ) * (163 / 100000) := hNoff100
                have h2mul := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ 2 by norm_num)
                calc 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300)
                    = 2 * ((N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2))) + 2 * ((N : ℝ) / 2300) := by ring
                  _ ≤ 2 * ((N : ℝ) * (163 / 100000)) + 2 * δ * (N : ℝ) := add_le_add h2mul herror2
                  _ = 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by ring
              calc (A7A.card : ℝ) + (A18A.card : ℝ)
                  ≤ (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (∑ p ∈ offPrimesUpTo N, (1 : ℝ) / (100 * (p : ℝ) ^ 2)) + 2 * ((N : ℝ) / 2300) := hA78_bound
                _ ≤ (N : ℝ) / 50 + 2 + (2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ)) := by linarith [h2]
                _ = (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by ring
            have h2_small : (2 : ℝ) ≤ 2 * δ * (N : ℝ) := by
              have hN' : (2300 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNbig
              nlinarith [hN']
            have hA78_explicit' : (A7A.card : ℝ) + (A18A.card : ℝ) ≤ (N : ℝ) / 50 + 2 * (N : ℝ) * (163 / 100000) + 4 * δ * (N : ℝ) := by
              have hrw : (N : ℝ) / 50 + 2 * (N : ℝ) * (163 / 100000) + 4 * δ * (N : ℝ) =
                         (N : ℝ) / 50 + (2 * δ * (N : ℝ)) + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by ring
              rw [hrw]
              have hstep : (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) ≤
                           (N : ℝ) / 50 + (2 * δ * (N : ℝ)) + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by
                calc (N : ℝ) / 50 + 2 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ)
                    = ((N : ℝ) / 50 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ)) + 2 := by ring
                  _ ≤ ((N : ℝ) / 50 + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ)) + (2 * δ * (N : ℝ)) :=
                      add_le_add_right h2_small _
                  _ = (N : ℝ) / 50 + (2 * δ * (N : ℝ)) + 2 * (N : ℝ) * (163 / 100000) + 2 * δ * (N : ℝ) := by ring
              exact le_trans hA78_explicit hstep
            nlinarith [hA_le_parts, hAstar_explicit, hA78_explicit', hNpos]
          exact (not_lt_of_ge hdense) hA_lt
        by_cases hEven78 : (∃ b ∈ A7A, b % 2 = 0) ∨ (∃ b ∈ A18A, b % 2 = 0)
        · 
          exfalso
          exact case_Astar_all_odd_exists_even_in_A78 hAstar_all_odd hEven78
        · 
          exfalso
          exact case_all_odd hAstar_all_odd hEven78

theorem effective_bound : ∀ N ≥ 10^45, Problem848Statement N :=
  problem_848_large_of_sawhney (sawhney_effective_at (10^45) le_rfl)

end Erdos848Port

theorem Erdos848.erdos_848_oltre_soglia : ∀ N : ℕ, 10^45 ≤ N → Erdos848.Erdos848For N :=
  Erdos848Port.effective_bound

theorem OMA.solution : OMA.R_Erdos848_erdos_848_R2.H3 := by
  intro N hN
  have cutoff : (10:ℕ)^45 ≤ 2^150 := by decide
  have grow : (2:ℕ)^150 ≤ 2^4651 := pow_le_pow_right' (by decide) (by decide)
  exact Erdos848.erdos_848_oltre_soglia N (cutoff.trans (grow.trans hN))
