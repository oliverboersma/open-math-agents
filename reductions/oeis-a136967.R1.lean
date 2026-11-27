import OMAStatements.S_oeis_a136967
import Mathlib.Tactic

/-!
The two-digit endings of any new solution must be 11, 21, 12 or 32.
There is a second restriction at every block width. In base t = 10^d = 9u+1,
a full block of admissible digits is between u and 4u. If the root ends
in four copies of a block b, write b² = a + t*h. Its low square blocks
must then be a, 2a+h, 3a+2h, 4a+3h: carrying across t would leave a block
below u. The last block's upper bound forces a=u and h=0. Since b≥u,
this leaves only the one-digit block 1.
-/

namespace OMA.R_oeis_a136967_R1
open OMA.S_oeis_a136967

/-- Nine times a block of ones is the corresponding block of nines. -/
lemma base_eq (n : ℕ) : 10 ^ n = 9 * ((10^n-1)/9) + 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ]; omega

lemma repunit_succ (n : ℕ) :
    (10^(n+1)-1)/9 = 10*((10^n-1)/9)+1 := by
  have h := base_eq n
  have h' := base_eq (n+1)
  rw [pow_succ] at h'
  omega

/-- Strip a whole block of valid decimal digits, preserving validity of the quotient. -/
lemma split_digits (d n : ℕ) (hd : 10^d ≤ n) (hn : UsesDigits n) :
    ∃ a q : ℕ, n = a + 10^d*q ∧ ((10^d-1)/9) ≤ a ∧ a ≤ 4*((10^d-1)/9) ∧ UsesDigits q := by
  induction d generalizing n with
  | zero => exact ⟨0, n, by simp, by decide, by decide, hn⟩
  | succ d ih =>
    have hpow := Nat.pow_pos (by decide : 0 < 10) (n := d)
    rw [pow_succ] at hd
    have hpos : 0 < n := by omega
    have hds := Nat.digits_def' (by decide : 1 < 10) hpos
    have hh := hn (n % 10) (by rw [hds]; simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    have hq : UsesDigits (n/10) := by
      intro e he
      apply hn
      rw [hds]
      exact List.mem_cons_of_mem _ he
    obtain ⟨a,q,he,ha,hb,hq'⟩ := ih (n/10) (by omega) hq
    refine ⟨n%10+10*a,q,?_,?_,?_,hq'⟩
    · calc n = n%10 + 10*(n/10) := (Nat.mod_add_div _ _).symm
           _ = _ := by rw [he, pow_succ]; ring
    · rw [repunit_succ]; omega
    · rw [repunit_succ]; omega

/-- Two positional representations with low coefficients closer than one base agree. -/
lemma lock {x c y z t : ℕ} (_ht : 0 < t) (h : x+t*y = c+t*z)
    (h1 : x < c+t) (h2 : c < x+t) : x = c ∧ y = z := by
  have hy : y = z := by
    rcases lt_trichotomy y z with hy|hy|hy
    · have := Nat.mul_le_mul_left t (show y+1 ≤ z by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · exact hy
    · have := Nat.mul_le_mul_left t (show z+1 ≤ y by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  subst z
  exact ⟨by omega, rfl⟩

/-- Four identical low blocks force the block and the lower output digit to be the minimum. -/
lemma four_blocks {t u b k j c₀ c₁ c₂ c₃ z : ℕ}
    (ht : t = 9*u+1) (hu : 0 < u) (bu : b ≤ 4*u)
    (hk : k = b*(1+t+t^2+t^3)+t^4*j)
    (hs : k^2 = c₀+t*(c₁+t*(c₂+t*(c₃+t*z))))
    (h₀ : u ≤ c₀ ∧ c₀ ≤ 4*u) (h₁ : u ≤ c₁ ∧ c₁ ≤ 4*u)
    (h₂ : u ≤ c₂ ∧ c₂ ≤ 4*u) (h₃ : u ≤ c₃ ∧ c₃ ≤ 4*u) :
    b^2 = u := by
  let h := b^2 / t
  let a := b^2 % t
  have htpos : 0 < t := by omega
  have ha : a < t := Nat.mod_lt _ htpos
  have e : a+t*h = b^2 := Nat.mod_add_div _ _
  have hb2 : b^2 ≤ (4*u)^2 := Nat.pow_le_pow_left bu 2
  have hsmall : h < 2*u := by
    apply (Nat.div_lt_iff_lt_mul htpos).2
    rw [ht]
    nlinarith
  let w := b^2*(3+2*t+t^2)+2*(b*(1+t+t^2+t^3))*j+t^4*j^2
  have expansion : k^2 = b^2+t*(2*b^2+t*(3*b^2+t*(4*b^2+t*w))) := by
    rw [hk]; dsimp [w]; ring
  have digits : a+t*((2*a+h)+t*((3*a+2*h)+t*((4*a+3*h)+t*(w+4*h)))) =
      c₀+t*(c₁+t*(c₂+t*(c₃+t*z))) := by
    rw [← hs, expansion, ← e]; ring
  obtain ⟨l₀,u₀⟩ := h₀
  obtain ⟨l₁,u₁⟩ := h₁
  obtain ⟨l₂,u₂⟩ := h₂
  obtain ⟨l₃,u₃⟩ := h₃
  have advance {v c y z : ℕ} (hv : v ≤ 4*u) (hc : u ≤ c ∧ c ≤ 4*u)
      (step : v+(a+h)+t*y = c+t*z) (amax : a ≤ 4*u) :
      v+(a+h) = c ∧ y = z := by
    obtain ⟨cl,cu⟩ := hc
    apply lock htpos step
    · clear step digits expansion hs hk hb2 e; omega
    · exact lt_of_lt_of_le (by omega : c<t) (Nat.le_add_left _ _)
  obtain ⟨eq₀,r₁⟩ := lock htpos digits (by omega) (by omega)
  have amax : a ≤ 4*u := eq₀ ▸ u₀
  have a1 : a+(a+h) = 2*a+h := by omega
  have a2 : 2*a+h+(a+h) = 3*a+2*h := by omega
  have a3 : 3*a+2*h+(a+h) = 4*a+3*h := by omega
  rw [← a1] at r₁
  obtain ⟨eq₁,r₂⟩ := advance amax ⟨l₁,u₁⟩ r₁ amax
  rw [a1] at eq₁
  rw [← a2] at r₂
  obtain ⟨eq₂,r₃⟩ := advance (eq₁ ▸ u₁) ⟨l₂,u₂⟩ r₂ amax
  rw [a2] at eq₂
  rw [← a3] at r₃
  obtain ⟨eq₃,_⟩ := advance (eq₂ ▸ u₂) ⟨l₃,u₃⟩ r₃ amax
  rw [a3] at eq₃
  have hz : h=0 := by omega
  rw [← e, hz, Nat.mul_zero, Nat.add_zero]
  omega

/-- If a solution ends in four copies of a full decimal block, the block is the
single digit 1. The prefix j is arbitrary. -/
theorem repeated_suffix {d b k j : ℕ} (hd : 0 < d)
    (hb : 0 < b ∧ b < 10^d)
    (hk : k = b*(1+10^d+(10^d)^2+(10^d)^3)+(10^d)^4*j)
    (hroot : UsesDigits k) (hsquare : UsesDigits (k^2)) : d = 1 ∧ b = 1 := by
  let t := 10^d
  let u := ((10^d-1)/9)
  have ht : t = 9*u+1 := base_eq d
  have ht10 : 10 ≤ t := by
    exact Nat.pow_le_pow_right (by decide : 0 < 10) (show 1 ≤ d by omega)
  have hu : 0 < u := by omega
  change k = b*(1+t+t^2+t^3)+t^4*j at hk
  change 0 < b ∧ b < t at hb
  have hkt : t^2 ≤ k := by
    calc t^2 ≤ 1+t+t^2+t^3 := by omega
         _ ≤ b*(1+t+t^2+t^3) := Nat.le_mul_of_pos_left _ hb.1
         _ ≤ k := by omega
  have h4 : t^4 ≤ k^2 := by
    calc t^4 = (t^2)^2 := by ring
         _ ≤ _ := Nat.pow_le_pow_left hkt _
  have ht1 : t ≤ t^2 := Nat.le_self_pow (by decide) _
  obtain ⟨a,q,eqk,al,au,_⟩ := split_digits d k (ht1.trans hkt) hroot
  change k = a+t*q at eqk
  have ek : b + t*(b*(1+t+t^2)+t^3*j) = a+t*q := by rw [← eqk,hk]; ring
  obtain ⟨ba,_⟩ := lock (by omega) ek (by omega) (by change a ≤ 4*u at au; omega)
  have strip (n m : ℕ) (hm : t*m ≤ n) (hv : UsesDigits n) (hn : t ≤ n) :
      ∃ c q, n=c+t*q ∧ u ≤ c ∧ c ≤ 4*u ∧ UsesDigits q ∧ m ≤ q := by
    obtain ⟨c,q,he,hc,hC,hv'⟩ := split_digits d n hn hv
    change n = c+t*q at he
    change c ≤ 4*u at hC
    refine ⟨c,q,he,hc,hC,hv',?_⟩
    by_contra! hlt
    have hmul := Nat.mul_le_mul_left t (show q+1 ≤ m by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have h23 : t^2 ≤ t^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h34 : t^3 ≤ t^4 := Nat.pow_le_pow_right (by omega) (by decide)
  obtain ⟨c₀,q₁,e₀,l₀,u₀,v₁,s₁⟩ := strip _ (t^3) (by simpa [pow_succ, Nat.mul_comm] using h4) hsquare (by omega)
  obtain ⟨c₁,q₂,e₁,l₁,u₁,v₂,s₂⟩ := strip _ (t^2) (by simpa [pow_succ, Nat.mul_comm] using s₁) v₁ (by omega)
  obtain ⟨c₂,q₃,e₂,l₂,u₂,v₃,s₃⟩ := strip _ t (by simpa [pow_two] using s₂) v₂ (by omega)
  obtain ⟨c₃,q₄,e₃,l₃,u₃,_⟩ := split_digits d q₃ s₃ v₃
  have he := four_blocks ht hu (ba ▸ au) hk (by rw [e₀,e₁,e₂,e₃])
    ⟨l₀,u₀⟩ ⟨l₁,u₁⟩ ⟨l₂,u₂⟩ ⟨l₃,u₃⟩
  change u ≤ a at al
  have hbu : u ≤ b := by omega
  have bone : b = 1 := by
    by_contra! hn
    have htwo : 2 ≤ b := by omega
    have hprod := Nat.mul_le_mul_right b htwo
    rw [pow_two] at he
    omega
  have uone : u = 1 := by simpa [bone] using he.symm
  have tten : t=10 := by omega
  refine ⟨?_,bone⟩
  by_contra! hx
  have hw : 10^2 ≤ t := Nat.pow_le_pow_right (by decide : 0<10) (show 2 ≤ d by omega)
  omega

lemma strip_one {n : ℕ} (hn : UsesDigits n) :
    n%10 < 5 ∧ UsesDigits (n/10) := by
  by_cases h : n=0
  · subst n; exact ⟨by decide,hn⟩
  have hd := Nat.digits_def' (by decide : 1<10) (show 0<n by omega)
  have hmem := hn _ (by rw [hd]; exact List.mem_cons_self)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  refine ⟨by omega, ?_⟩
  intro d he
  apply hn
  rw [hd]
  exact List.mem_cons_of_mem _ he

lemma test_digits (n : ℕ) : UsesDigits n ↔
    (Nat.digits 10 n).all (fun d => decide (d ∈ ({1,2,3,4} : Finset ℕ))) = true := by
  simp [UsesDigits, List.all_eq_true]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2400000 in
/-- Independent exhaustive check of four decimal positions. Leading zeroes
are allowed only in the encoding of a shorter integer. -/
lemma small_table : ∀ a b c d : Fin 5,
    let k : ℕ := a.val+10*(b.val+10*(c.val+10*d.val))
    0<k → (Nat.digits 10 k).all (fun i => decide (i ∈ ({1,2,3,4} : Finset ℕ))) = true →
    (Nat.digits 10 (k^2)).all (fun i => decide (i ∈ ({1,2,3,4} : Finset ℕ))) = true →
    k ∈ ({1,2,11,12,21,111,1111} : Finset ℕ) := by decide +kernel

lemma small {k : ℕ} (hk : 0<k) (bound : k<10000)
    (hv : UsesDigits k) (hs : UsesDigits (k^2)) :
    k ∈ ({1,2,11,12,21,111,1111} : Finset ℕ) := by
  obtain ⟨ha,v₁⟩ := strip_one hv
  obtain ⟨hb,v₂⟩ := strip_one v₁
  obtain ⟨hc,v₃⟩ := strip_one v₂
  obtain ⟨hd,_⟩ := strip_one v₃
  have e : k%10+10*((k/10)%10+10*((k/10/10)%10+10*((k/10/10/10)%10)))=k := by omega
  have h := small_table ⟨_,ha⟩ ⟨_,hb⟩ ⟨_,hc⟩ ⟨_,hd⟩
  dsimp only at h
  rw [e] at h
  exact h hk ((test_digits _).mp hv) ((test_digits _).mp hs)

lemma low_pair {n : ℕ} (hn : 10 ≤ n) (hv : UsesDigits n) :
    (1 ≤ n%10 ∧ n%10 ≤ 4) ∧ (1 ≤ n/10%10 ∧ n/10%10 ≤ 4) := by
  have one {x : ℕ} (hx : 0<x) (v : UsesDigits x) : 1 ≤ x%10 ∧ x%10 ≤ 4 := by
    have hm := v _ (by rw [Nat.digits_def' (by decide : 1<10) hx]; exact List.mem_cons_self)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  exact ⟨one (by omega) hv, one (by omega) (strip_one hv).2⟩

lemma endings {k : ℕ} (hk : 10000 ≤ k) (hv : UsesDigits k) (hs : UsesDigits (k^2)) :
    (k%100=11 ∨ k%100=21) ∨ (k%100=12 ∨ k%100=32) := by
  have table : ∀ r : Fin 100, let x := r.val; let y := x^2%100
               (1 ≤ x%10 ∧ x%10 ≤ 4) ∧ (1 ≤ x/10 ∧ x/10 ≤ 4) →
               (1 ≤ y%10 ∧ y%10 ≤ 4) ∧ (1 ≤ y/10 ∧ y/10 ≤ 4) →
               (x=11 ∨ x=21) ∨ (x=12 ∨ x=32) := by decide +kernel
  have x := low_pair (by omega) hv
  have y := low_pair (by nlinarith : 10 ≤ k^2) hs
  have modpow : (k%100)^2%100=k^2%100 := (Nat.pow_mod _ _ _).symm
  have ht := table ⟨k%100,Nat.mod_lt _ (by decide)⟩
  dsimp only at ht
  rw [modpow] at ht
  apply ht <;> omega

/-- A fifth terminal 1 puts a 5 in the square, since 11111² ends in 54321. -/
lemma not_five_ones {k : ℕ} (hv : UsesDigits (k^2)) : k%100000 ≠ 11111 := by
  intro h
  have he : k^2%100000 = 54321 := by rw [Nat.pow_mod, h]
  obtain ⟨_,v₁⟩ := strip_one hv
  obtain ⟨_,v₂⟩ := strip_one v₁
  obtain ⟨_,v₃⟩ := strip_one v₂
  obtain ⟨_,v₄⟩ := strip_one v₃
  have hd := (strip_one v₄).1
  omega

/-- Branch with roots ending in 11 or 21. A counterexample must be large,
and the suffix obstruction rules out four equal multi-digit blocks. -/
def H1 : Prop := ∀ k : ℕ, 10000 ≤ k → (k%100=11 ∨ k%100=21) → k%100000 ≠ 11111 →
    UsesDigits k → UsesDigits (k^2) →
    (∀ d b j : ℕ, 2 ≤ d → 0 < b → b < 10^d →
      k ≠ b*(1+10^d+(10^d)^2+(10^d)^3)+(10^d)^4*j) → False

/-- Independent branch with roots ending in 12 or 32. -/
def H2 : Prop := ∀ k : ℕ, 10000 ≤ k → (k%100=12 ∨ k%100=32) →
    UsesDigits k → UsesDigits (k^2) →
    (∀ d b j : ℕ, 2 ≤ d → 0 < b → b < 10^d →
      k ≠ b*(1+10^d+(10^d)^2+(10^d)^3)+(10^d)^4*j) → False

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a136967.main := by
  intro h1 h2
  ext k
  change (0<k ∧ UsesDigits k ∧ UsesDigits (k^2)) ↔ _
  constructor
  · rintro ⟨hk,hv,hs⟩
    by_cases bound : k<10000
    · have := small hk bound hv hs
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton] using this
    have big : 10000 ≤ k := by omega
    have free : ∀ d b j : ℕ, 2 ≤ d → 0<b → b<10^d →
        k ≠ b*(1+10^d+(10^d)^2+(10^d)^3)+(10^d)^4*j := by
      intro d b j hd hb hb' e
      have h := (repeated_suffix (by omega) ⟨hb,hb'⟩ e hv hs).1
      omega
    rcases endings big hv hs with h | h
    · exact (h1 k big h (not_five_ones hs) hv hs free).elim
    · exact (h2 k big h hv hs free).elim
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rintro (rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> rw [test_digits,test_digits] <;> decide +kernel

end OMA.R_oeis_a136967_R1
