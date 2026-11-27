import OMAReductions.R_Erdos1191_erdos_1191_parts_ii_R2

/-!
# An additive code retaining the dyadic indices in Erdős 1191(ii)

For an input a, write j = floor(log₂ a). Split the binary expansion of a into
blocks of lengths 1, 2, 4, 8, ... . In block t, store the corresponding
data digit, the t-th binary digit of j, and the t-th base-four digit of j².
The radix 128 times the data radix leaves enough space to add two encodings
without any carry into the next block or neighboring field. Thus an equality
of sums recovers the sum of the original data, the sum of the two indices,
and the sum of their squares. The latter two determine the unordered indices.

There are at most floor(log₂(j+1))+1 occupied blocks. The resulting code has
E(a) ≤ 2^j (j+2)^16 on the j-th dyadic interval.

Reduction and formulation of the target by @mucoucah in #7467.
Nicholas Wierenga used the same index-and-square principle in #3944 for
the related R1.H2 eventual cutoff, with exponent 30. The mixed-radix code
and explicit exponent 16 here were developed independently for R2.H2 by
@anmolspace with OpenAI Codex.
-/

namespace OMA.Erdos1191Code

structure Digits where
  data : ℕ
  index : ℕ
  square : ℕ
  deriving DecidableEq

def weight (x : Digits) : ℕ := x.data + x.index + x.square

def base (t : ℕ) : ℕ := 2 ^ (2 ^ t)

lemma one_lt_base (t : ℕ) : 1 < base t := by
  exact one_lt_pow₀ (by decide) (by positivity)

def tail (t : ℕ) (x : Digits) : Digits :=
  ⟨x.data / base t, x.index / 2, x.square / 4⟩

def digit (t : ℕ) (x : Digits) : ℕ :=
  64 * (x.data % base t) + 8 * (x.square % 4) + x.index % 2

lemma weight_tail_le (t : ℕ) (x : Digits) : weight (tail t x) ≤ weight x := by
  unfold weight tail
  dsimp
  exact Nat.add_le_add (Nat.add_le_add (Nat.div_le_self ..) (Nat.div_le_self ..)) (Nat.div_le_self ..)

lemma weight_tail_lt (t : ℕ) (x : Digits) (h : weight x ≠ 0) :
    weight (tail t x) < weight x := by
  unfold weight tail at *
  dsimp
  have hd := Nat.div_le_self x.data (base t)
  have hi := Nat.div_le_self x.index 2
  have hs := Nat.div_le_self x.square 4
  by_cases ha : 0 < x.data
  · have := Nat.div_lt_self ha (one_lt_base t)
    omega
  by_cases hb : 0 < x.index
  · have := Nat.div_lt_self hb (by decide : 1 < 2)
    omega
  have hc : 0 < x.square := by omega
  have := Nat.div_lt_self hc (by decide : 1 < 4)
  omega

def pack (t : ℕ) (x : Digits) : ℕ :=
  if h : weight x = 0 then 0 else digit t x + (128 * base t) * pack (t+1) (tail t x)
termination_by weight x
decreasing_by exact weight_tail_lt t x h

lemma pack_zero (t : ℕ) : pack t ⟨0,0,0⟩ = 0 := by rw [pack]; rfl

lemma pack_eq (t : ℕ) (x : Digits) :
    pack t x = digit t x + (128 * base t) * pack (t+1) (tail t x) := by
  rw [pack]
  split
  · next h =>
      rcases x with ⟨a,b,c⟩
      change a+b+c=0 at h
      have ha : a=0 := by omega
      have hb : b=0 := by omega
      have hc : c=0 := by omega
      subst_vars
      simp [digit,tail,pack_zero]
  · rfl

lemma sumdigit_lt (t : ℕ) (x y : Digits) : digit t x + digit t y < 128 * base t := by
  have h := one_lt_base t
  have hx := Nat.mod_lt x.data (by omega : 0 < base t)
  have hy := Nat.mod_lt y.data (by omega : 0 < base t)
  unfold digit
  omega

lemma split_sum (r u v u' v' : ℕ) (hr : 0 < r) (hu : u < r) (hu' : u' < r)
    (h : u + r*v = u' + r*v') : u = u' ∧ v = v' := by
  have hmod := congrArg (· % r) h
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hu'] at hmod
  exact ⟨hmod, Nat.eq_of_mul_eq_mul_left hr (by omega)⟩

lemma restore (r a b c d : ℕ)
    (hmod : a % r + b % r = c % r + d % r)
    (hdiv : a / r + b / r = c / r + d / r) : a + b = c + d := by
  have hmul := congrArg (r * ·) hdiv
  simp only [Nat.mul_add] at hmul
  have ha := Nat.mod_add_div a r
  have hb := Nat.mod_add_div b r
  have hc := Nat.mod_add_div c r
  have hd := Nat.mod_add_div d r
  omega

lemma sums_injective (t : ℕ) (x y z w : Digits)
    (h : pack t x + pack t y = pack t z + pack t w) :
    x.data+y.data=z.data+w.data ∧ x.index+y.index=z.index+w.index ∧
    x.square+y.square=z.square+w.square := by
  by_cases small : weight x + weight y + weight z + weight w = 0
  · unfold weight at small
    omega
  have hr : 0 < 128 * base t := Nat.mul_pos (by decide) (lt_trans Nat.zero_lt_one (one_lt_base t))
  rw [pack_eq t x, pack_eq t y, pack_eq t z, pack_eq t w] at h
  let r := 128 * base t
  have h' : (digit t x + digit t y) + r*(pack (t+1) (tail t x) + pack (t+1) (tail t y)) =
      (digit t z + digit t w) + r*(pack (t+1) (tail t z) + pack (t+1) (tail t w)) := by
    dsimp [r]
    simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  obtain ⟨hmod,hquot⟩ := split_sum r _ _ _ _ hr (sumdigit_lt t x y) (sumdigit_lt t z w) h'
  obtain ⟨ha,hb,hc⟩ := sums_injective (t+1) (tail t x) (tail t y) (tail t z) (tail t w) hquot
  simp only [tail] at ha hb hc
  unfold digit at hmod
  exact ⟨restore (base t) _ _ _ _ (by omega) ha,
    restore 2 _ _ _ _ (by omega) hb, restore 4 _ _ _ _ (by omega) hc⟩
termination_by weight x + weight y + weight z + weight w
decreasing_by
  have hx := weight_tail_le t x
  have hy := weight_tail_le t y
  have hz := weight_tail_le t z
  have hw := weight_tail_le t w
  by_cases h₁ : weight x = 0
  · by_cases h₂ : weight y = 0
    · by_cases h₃ : weight z = 0
      · have := weight_tail_lt t w (by omega)
        omega
      · have := weight_tail_lt t z h₃
        omega
    · have := weight_tail_lt t y h₂
      omega
  · have := weight_tail_lt t x h₁
    omega

def capacity (t : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => base t * capacity (t+1) n

lemma capacity_formula (t n : ℕ) : capacity t n = 2 ^ (2 ^ t * (2 ^ n - 1)) := by
  induction n generalizing t with
  | zero => simp [capacity]
  | succ n ih =>
    rw [capacity, ih, base, ← pow_add]
    congr 1
    have hn : 0 < 2^n := by positivity
    have h : 2^(n+1)-1 = 1+2*(2^n-1) := by rw [pow_succ]; omega
    rw [h, pow_succ (2:ℕ) t]
    ring

lemma bound (t n : ℕ) (x : Digits) (ha : x.data < capacity t (n+1))
    (hb : x.index < 2^(n+1)) (hc : x.square < 4^(n+1)) :
    pack t x < 128^(n+1) * (x.data + capacity t n) := by
  induction n generalizing t x with
  | zero =>
    simp only [capacity, Nat.mul_one] at ha
    simp only [Nat.zero_add, pow_one] at hb hc
    have htail : tail t x = ⟨0,0,0⟩ := by
      simp [tail, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hc]
    rw [pack_eq, htail, pack_zero]
    simp [digit, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, capacity]
    omega
  | succ n ih =>
    have hv := lt_trans Nat.zero_lt_one (one_lt_base t)
    have ha' : (tail t x).data < capacity (t+1) (n+1) := by
      exact (Nat.div_lt_iff_lt_mul hv).mpr (by simpa [capacity, Nat.mul_comm] using ha)
    have hb' : (tail t x).index < 2^(n+1) :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by simpa only [pow_succ (2:ℕ) (n+1)] using hb)
    have hc' : (tail t x).square < 4^(n+1) :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr (by simpa only [pow_succ (4:ℕ) (n+1)] using hc)
    have ht := ih (t+1) (tail t x) ha' hb' hc'
    have hd : digit t x < 128*base t := by
      have := sumdigit_lt t x ⟨0,0,0⟩
      omega
    have htail : pack (t+1) (tail t x) + 1 ≤ 128^(n+1)*(x.data / base t + capacity (t+1) n) := ht
    rw [pack_eq]
    calc
      _ < 128 * base t * (pack (t+1) (tail t x) + 1) := by rw [Nat.mul_add]; omega
      _ ≤ 128 * base t * (128^(n+1)*(x.data / base t + capacity (t+1) n)) :=
        Nat.mul_le_mul_left _ htail
      _ = 128^((n+1)+1)*(x.data / base t * base t + capacity t (n+1)) := by rw [capacity, pow_succ (128:ℕ) (n+1)]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.div_mul_le_self ..) _)

def E (a : ℕ) : ℕ := pack 0 ⟨a, Nat.log 2 a, (Nat.log 2 a)^2⟩

lemma pair_power_sums {i j k l : ℕ} (h₁ : i+j=k+l) (h₂ : i^2+j^2=k^2+l^2) :
    (i=k ∧ j=l) ∨ (i=l ∧ j=k) := by
  have h₁' := congrArg (fun n : ℕ => n^2) h₁
  have hprod : i*j=k*l := by nlinarith
  have hz : ((i:ℤ)-k)*((i:ℤ)-l) = 0 := by
    have u : (i:ℤ)+j=k+l := by exact_mod_cast h₁
    have v : (i:ℤ)*j=k*l := by exact_mod_cast hprod
    linear_combination (i:ℤ) * u - v
  rcases mul_eq_zero.mp hz with q | q
  · left; constructor <;> omega
  · right; constructor <;> omega

theorem E_sums (a b u v : ℕ) (h : E a + E b = E u + E v) :
    a+b=u+v ∧ ((Nat.log 2 a=Nat.log 2 u ∧ Nat.log 2 b=Nat.log 2 v) ∨
               (Nat.log 2 a=Nat.log 2 v ∧ Nat.log 2 b=Nat.log 2 u)) := by
  obtain ⟨ha,hb,hc⟩ := sums_injective 0 _ _ _ _ h
  exact ⟨ha,pair_power_sums hb hc⟩

lemma E_zero : E 0 = 0 := by simpa [E] using pack_zero 0

theorem E_bounds (j a : ℕ) (ha : a ∈ Finset.Ico (2^j) (2^(j+1))) :
    1 ≤ E a ∧ E a ≤ 2^j*(j+2)^16 := by
  obtain ⟨halo,hahi⟩ := Finset.mem_Ico.mp ha
  have hap : 0 < a := (by positivity : 0 < 2^j).trans_le halo
  have hj := Nat.log_eq_of_pow_le_of_lt_pow halo hahi
  constructor
  · by_contra! he
    have hh : E a + E 0 = E 0 + E 0 := by rw [E_zero]; omega
    have hz := (E_sums a 0 0 0 hh).1
    omega
  let k := Nat.log 2 (j+1)
  have hkl : 2^k ≤ j+1 := Nat.pow_log_le_self 2 (by omega)
  have hku : j+1 < 2^(k+1) := Nat.lt_pow_succ_log_self (by decide) (j+1)
  have haja : a < capacity 0 (k+1) := by
    rw [capacity_formula]
    simp only [pow_zero, one_mul]
    exact hahi.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hjc : j^2 < 4^(k+1) := by
    calc
      j^2 < (2^(k+1))^2 := Nat.pow_lt_pow_left (by omega) (by decide)
      _ = 4^(k+1) := by rw [← pow_mul, Nat.mul_comm (k+1) 2, pow_mul]; rfl
  have hz := bound 0 k ⟨a,j,j^2⟩ haja (by dsimp; omega) hjc
  change pack 0 ⟨a,Nat.log 2 a,(Nat.log 2 a)^2⟩ ≤ _
  rw [hj]
  have hcap : capacity 0 k ≤ 2^j := by
    rw [capacity_formula]
    simp only [pow_zero, one_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hsum : a+capacity 0 k ≤ 3*2^j := by rw [pow_succ] at hahi; omega
  have hp : 128^(k+1) = 128*(2^k)^7 := by
    rw [pow_succ, show (128:ℕ) = 2^7 by decide, ← pow_mul, ← pow_mul, Nat.mul_comm 7 k]
    ring
  have hpoly : 384 ≤ (j+2)^9 := by
    have := Nat.pow_le_pow_left (by omega : 2 ≤ j+2) 9
    omega
  calc
    _ ≤ 128^(k+1)*(a+capacity 0 k) := hz.le
    _ ≤ 128^(k+1)*(3*2^j) := Nat.mul_le_mul_left _ hsum
    _ = 2^j*(384*(2^k)^7) := by rw [hp]; ring
    _ ≤ 2^j*((j+2)^9 * (j+2)^7) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hpoly
      (Nat.pow_le_pow_left (by omega) 7))
    _ = _ := by rw [← pow_add]

theorem code_exists :
    ∃ (f : ℕ → ℕ) (e : ℕ),
    (∀ a b u v, f a + f b = f u + f v → a + b = u + v ∧
      ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
       (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
    ∀ j, ∀ a ∈ Finset.Ico (2^j) (2^(j+1)), 1 ≤ f a ∧ f a ≤ 2^j*(j+2)^e :=
  ⟨E,16,E_sums,E_bounds⟩

end OMA.Erdos1191Code

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_ii_R2.H2 := OMA.Erdos1191Code.code_exists
