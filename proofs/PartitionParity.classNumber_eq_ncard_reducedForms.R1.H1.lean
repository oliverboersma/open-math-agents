import OMAReductions.R_PartitionParity_classNumber_eq_ncard_reducedForms_R1

/-! The form–ideal correspondence for negative fundamental discriminants.
Ported from @ItsNotTheGabs's public proof of the parent theorem in open-math-agents
(commit 68fa9943dbeb). This step uses the ring of integers and ideal-class calculations. -/
-- Credit: @marcusbuffett

namespace PartitionParityProof

structure QuadInt (k : ℤ) where
  x : ℤ
  y : ℤ
deriving DecidableEq, Repr

namespace QuadInt

theorem ext {k : ℤ} {z w : QuadInt k} (hx : z.x = w.x) (hy : z.y = w.y) : z = w := by
  cases z; cases w; simp_all

variable {k : ℤ}

/-- The canonical identification of `QuadInt k` with the standard model `ℤ[ω]`, `ω² = ω - k`. -/
def equiv (k : ℤ) : QuadInt k ≃ QuadraticAlgebra ℤ (-k) 1 where
  toFun z := ⟨z.x, z.y⟩
  invFun q := ⟨q.re, q.im⟩
  left_inv z := by cases z; rfl
  right_inv q := by cases q; rfl

instance commRing : CommRing (QuadInt k) := (equiv k).commRing

instance nontrivial : Nontrivial (QuadInt k) := (equiv k).nontrivial

@[simp] theorem equiv_re (z : QuadInt k) : (equiv k z).re = z.x := rfl
@[simp] theorem equiv_im (z : QuadInt k) : (equiv k z).im = z.y := rfl

theorem equiv_add (z w : QuadInt k) : equiv k (z + w) = equiv k z + equiv k w := rfl
theorem equiv_mul (z w : QuadInt k) : equiv k (z * w) = equiv k z * equiv k w := rfl
theorem equiv_zero : equiv k (0 : QuadInt k) = 0 := rfl
theorem equiv_one : equiv k (1 : QuadInt k) = 1 := rfl
theorem equiv_neg (z : QuadInt k) : equiv k (-z) = -equiv k z := rfl
theorem equiv_sub (z w : QuadInt k) : equiv k (z - w) = equiv k z - equiv k w := rfl

@[simp] theorem add_x (z w : QuadInt k) : (z + w).x = z.x + w.x := rfl
@[simp] theorem add_y (z w : QuadInt k) : (z + w).y = z.y + w.y := rfl
@[simp] theorem neg_x (z : QuadInt k) : (-z).x = -z.x := rfl
@[simp] theorem neg_y (z : QuadInt k) : (-z).y = -z.y := rfl
@[simp] theorem sub_x (z w : QuadInt k) : (z - w).x = z.x - w.x := rfl
@[simp] theorem sub_y (z w : QuadInt k) : (z - w).y = z.y - w.y := rfl
@[simp] theorem zero_x : (0 : QuadInt k).x = 0 := rfl
@[simp] theorem zero_y : (0 : QuadInt k).y = 0 := rfl
@[simp] theorem one_x : (1 : QuadInt k).x = 1 := rfl
@[simp] theorem one_y : (1 : QuadInt k).y = 0 := rfl
@[simp] theorem natCast_x (n : ℕ) : ((n : QuadInt k)).x = n := rfl
@[simp] theorem natCast_y (n : ℕ) : ((n : QuadInt k)).y = 0 := rfl
@[simp] theorem intCast_x (n : ℤ) : ((n : QuadInt k)).x = n := rfl
@[simp] theorem intCast_y (n : ℤ) : ((n : QuadInt k)).y = 0 := rfl

@[simp] theorem mul_x (z w : QuadInt k) :
    (z * w).x = z.x * w.x - k * z.y * w.y := by
  have h := congrArg QuadraticAlgebra.re (equiv_mul (k := k) z w)
  simp only [QuadraticAlgebra.re_mul, equiv_re, equiv_im] at h
  rw [h]; ring

@[simp] theorem mul_y (z w : QuadInt k) :
    (z * w).y = z.x * w.y + z.y * w.x + z.y * w.y := by
  have h := congrArg QuadraticAlgebra.im (equiv_mul (k := k) z w)
  simp only [QuadraticAlgebra.im_mul, equiv_re, equiv_im] at h
  rw [h]; ring

/-- The norm form `N(x + yω) = x² + xy + ky²`. -/
def norm (z : QuadInt k) : ℤ := z.x ^ 2 + z.x * z.y + k * z.y ^ 2

/-- The conjugate of `x + yω` is `x + y(1-ω) = (x+y) - yω`. -/
def conj (z : QuadInt k) : QuadInt k := ⟨z.x + z.y, -z.y⟩

/-- The determinant form. -/
def det (z w : QuadInt k) : ℤ := z.x * w.y - z.y * w.x

@[simp] theorem norm_x (z : QuadInt k) : z.norm = z.x ^ 2 + z.x * z.y + k * z.y ^ 2 := rfl
@[simp] theorem conj_x (z : QuadInt k) : z.conj.x = z.x + z.y := rfl
@[simp] theorem conj_y (z : QuadInt k) : z.conj.y = -z.y := rfl
@[simp] theorem det_apply (z w : QuadInt k) : det z w = z.x * w.y - z.y * w.x := rfl

@[simp] theorem norm_zero : (0 : QuadInt k).norm = 0 := by simp [norm]
@[simp] theorem norm_one : (1 : QuadInt k).norm = 1 := by simp [norm]

theorem conj_mul (z w : QuadInt k) : (z * w).conj = z.conj * w.conj := by
  apply QuadInt.ext <;> simp [conj] <;> ring

@[simp] theorem conj_zero : (0 : QuadInt k).conj = 0 := by apply QuadInt.ext <;> simp [conj]
@[simp] theorem conj_one : (1 : QuadInt k).conj = 1 := by apply QuadInt.ext <;> simp [conj]

/-- `z * conj z = (norm z, 0)`. -/
theorem mul_conj (z : QuadInt k) : z * z.conj = ⟨z.norm, 0⟩ := by
  apply QuadInt.ext <;> simp [conj, norm] <;> ring

theorem conj_mul_conj (z : QuadInt k) : z.conj * z = ⟨z.norm, 0⟩ := by
  apply QuadInt.ext <;> simp [conj, norm] <;> ring

theorem norm_mul (z w : QuadInt k) : (z * w).norm = z.norm * w.norm := by
  have h : (z * w) * (z * w).conj = (z * z.conj) * (w * w.conj) := by
    rw [conj_mul]; ring
  simp only [mul_conj] at h
  have hx := congrArg QuadInt.x h
  simpa [mul_x] using hx

/-- The key numerical identity `4 * N(z) = (2x+y)² + (4k-1) y²`. -/
theorem four_mul_norm (z : QuadInt k) :
    4 * z.norm = (2 * z.x + z.y) ^ 2 + (4 * k - 1) * z.y ^ 2 := by
  simp only [norm]; ring

/-- With `D = 4k-1 > 0`, the norm is positive on nonzero elements. -/
theorem norm_pos {D : ℕ} (hk : 4 * k - 1 = (D : ℤ)) (hD : 0 < D) {z : QuadInt k}
    (hz : z ≠ 0) : 0 < z.norm := by
  have h4 : (4 : ℤ) * z.norm = (2 * z.x + z.y) ^ 2 + (D : ℤ) * z.y ^ 2 := by
    rw [four_mul_norm, hk]
  have hsq : 0 < (2 * z.x + z.y) ^ 2 + (D : ℤ) * z.y ^ 2 := by
    rcases eq_or_ne z.y 0 with hy | hy
    · have hx : z.x ≠ 0 := by
        intro hx; apply hz; apply QuadInt.ext <;> simp [hx, hy]
      have : (2 * z.x + z.y) ^ 2 = (2 * z.x) ^ 2 := by rw [hy]; ring
      rw [this, hy]; nlinarith [sq_nonneg (2 * z.x), sq_pos_of_ne_zero (by exact mul_ne_zero two_ne_zero hx : 2 * z.x ≠ 0)]
    · have hDy : 0 < (D : ℤ) * z.y ^ 2 :=
        mul_pos (by exact_mod_cast hD) (sq_pos_of_ne_zero hy)
      nlinarith [sq_nonneg (2 * z.x + z.y)]
  nlinarith [h4, hsq]

/-- `norm_mul` and positivity make `QuadInt k` a domain. -/
theorem noZeroDivisors {D : ℕ} (hk : 4 * k - 1 = (D : ℤ)) (hD : 0 < D) :
    NoZeroDivisors (QuadInt k) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro z w hzw
    by_contra h
    rw [not_or] at h
    have hz := norm_pos hk hD h.1
    have hw := norm_pos hk hD h.2
    have : (z * w).norm = 0 := by rw [hzw]; simp [norm]
    rw [norm_mul] at this
    nlinarith [mul_pos hz hw]

theorem isDomain {D : ℕ} (hk : 4 * k - 1 = (D : ℤ)) (hD : 0 < D) :
    IsDomain (QuadInt k) := by
  have := noZeroDivisors hk hD
  exact NoZeroDivisors.to_isDomain (QuadInt k)

/- ## The determinant identities -/

@[simp] theorem zsmul_x (u : ℤ) (z : QuadInt k) : (u • z).x = u * z.x := by
  rw [zsmul_eq_mul]; simp [mul_x]

@[simp] theorem zsmul_y (u : ℤ) (z : QuadInt k) : (u • z).y = u * z.y := by
  rw [zsmul_eq_mul]; simp [mul_y]

theorem det_antisymm (z w : QuadInt k) : det z w = - det w z := by
  simp [det]; ring

theorem det_self (z : QuadInt k) : det z z = 0 := by simp [det]; ring

theorem det_add_left (α β γ : QuadInt k) : det (α + β) γ = det α γ + det β γ := by
  simp [det]; ring

theorem det_add_right (α β γ : QuadInt k) : det α (β + γ) = det α β + det α γ := by
  simp [det]; ring

/-- `det (λ*α) (λ*β) = N λ * det α β`. -/
theorem det_mul_left (l α β : QuadInt k) :
    det (l * α) (l * β) = l.norm * det α β := by
  simp [det, norm]; ring

/-- The determinant is `ℤ`-bilinear with the stated expansion. -/
theorem det_linear_comb (u v w t : ℤ) (α β : QuadInt k) :
    det (u • α + w • β) (v • α + t • β) = (u * t - v * w) * det α β := by
  simp only [det, zsmul_x, zsmul_y, add_x, add_y]
  ring

/-- The `y`-coordinate of `β * conj α` is the determinant. -/
theorem mul_conj_y (α β : QuadInt k) : (β * α.conj).y = det α β := by
  simp [conj, det]; ring

/-- The trace-type identity `2*(β conj α).x + (β conj α).y = N(α+β) - Nα - Nβ`. -/
theorem two_mul_mul_conj_x_add_y (α β : QuadInt k) :
    2 * (β * α.conj).x + (β * α.conj).y = (α + β).norm - α.norm - β.norm := by
  simp [conj, norm]; ring

end QuadInt

namespace QuadFormReduction

abbrev Form (D : ℕ) := {f : ℤ × ℤ × ℤ // 0 < f.1 ∧ f.2.1 ^ 2 - 4 * f.1 * f.2.2 = -(D : ℤ) ∧ Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1}

def evaluate {D : ℕ} (f : Form D) (x y : ℤ) : ℤ := f.val.1 * x ^ 2 + f.val.2.1 * x * y + f.val.2.2 * y ^ 2

def proper {D : ℕ} (f g : Form D) : Prop := ∃ u v w z : ℤ, u * z - v * w = 1 ∧ ∀ x y : ℤ, evaluate f x y = evaluate g (u * x + v * y) (w * x + z * y)

theorem auto_primitive {D : ℕ} (hsq : Squarefree D) {a b c : ℤ}
    (hdisc : b ^ 2 - 4 * a * c = -(D : ℤ)) : Int.gcd (Int.gcd a b) c = 1 := by
  set g : ℕ := Int.gcd (Int.gcd a b) c with hgdef
  have hgab : (g : ℤ) ∣ (Int.gcd a b : ℤ) := by
    rw [hgdef]; exact Int.gcd_dvd_left _ _
  have hga : (g : ℤ) ∣ a := hgab.trans (Int.gcd_dvd_left a b)
  have hgb : (g : ℤ) ∣ b := hgab.trans (Int.gcd_dvd_right a b)
  have hgc : (g : ℤ) ∣ c := by rw [hgdef]; exact Int.gcd_dvd_right _ _
  have hdvd : (g : ℤ) * g ∣ (D : ℤ) := by
    have h1 : (g : ℤ) * g ∣ b ^ 2 := by
      obtain ⟨m, hm⟩ := hgb
      exact ⟨m ^ 2, by rw [hm]; ring⟩
    have h2 : (g : ℤ) * g ∣ 4 * a * c := by
      obtain ⟨m, hm⟩ := hga
      obtain ⟨n, hn⟩ := hgc
      exact ⟨4 * m * n, by rw [hm, hn]; ring⟩
    have h3 : (g : ℤ) * g ∣ b ^ 2 - 4 * a * c := dvd_sub h1 h2
    rw [hdisc] at h3
    exact (Int.dvd_neg).mp h3
  have hgg : g * g ∣ D := by
    rw [← Int.natCast_dvd_natCast]
    push_cast
    exact hdvd
  exact Nat.isUnit_iff.mp (hsq g hgg)

/- ### 4. The middle coefficient is odd -/

theorem b_odd_of_disc {D : ℕ} (h3 : D % 4 = 3) {k a b c : ℤ} (hk : 4 * k - 1 = (D : ℤ))
    (hdisc : b ^ 2 - 4 * a * c = -(D : ℤ)) :
    ∃ t : ℤ, b = 2 * t + 1 ∧ a * c = t ^ 2 + t + k := by
  have hbmod : b % 2 = 1 := by
    have hb0 : 0 ≤ b % 2 := Int.emod_nonneg b (by norm_num)
    have hb1 : b % 2 < 2 := Int.emod_lt_of_pos b (by norm_num)
    rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with h | h
    · exfalso
      have h2dvd : (2 : ℤ) ∣ b := Int.dvd_of_emod_eq_zero h
      have h4dvd : (4 : ℤ) ∣ b ^ 2 := by
        obtain ⟨m, hm⟩ := h2dvd
        exact ⟨m ^ 2, by rw [hm]; ring⟩
      have h4D : (4 : ℤ) ∣ (D : ℤ) := by
        have hD : (D : ℤ) = 4 * a * c - b ^ 2 := by linarith [hdisc]
        rw [hD]
        exact dvd_sub ⟨a * c, by ring⟩ h4dvd
      have hDm : (D : ℤ) % 4 = 0 := Int.emod_eq_zero_of_dvd h4D
      have hcast' : ((D : ℤ) % 4) = 3 := by
        have h2 : ((D : ℤ) % 4) = ((D % 4 : ℕ) : ℤ) := by simp
        rw [h2, h3]; norm_num
      rw [hDm] at hcast'
      norm_num at hcast'
    · exact h
  refine ⟨b / 2, ?_, ?_⟩
  · have := Int.ediv_mul_add_emod b 2
    rw [hbmod] at this
    linarith
  · have hb : b = 2 * (b / 2) + 1 := by
      have := Int.ediv_mul_add_emod b 2
      rw [hbmod] at this
      linarith
    have h1 : 4 * (a * c) = 4 * ((b / 2) ^ 2 + (b / 2) + k) := by
      nlinarith [hdisc, hk, hb]
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h1


end QuadFormReduction

/- ## 5. Hermite normal form for ideals of `QuadInt k` -/

def IdealHasHNF (k : ℤ) (I : Ideal (QuadInt k)) : Prop :=
  ∃ (d a t : ℤ), 0 < d ∧ 0 < a ∧ a ∣ t ^ 2 + t + k ∧
    ∀ z : QuadInt k, z ∈ I ↔ ∃ x y : ℤ, z = ⟨d * (a * x + t * y), d * y⟩

theorem ideal_has_hnf {D : ℕ} {k : ℤ} (hk : 4 * k - 1 = (D : ℤ)) (hD : 0 < D)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) : IdealHasHNF k I := by
  classical
  obtain ⟨z0, hz0I, hz0ne⟩ := (Submodule.ne_bot_iff I).mp hI
  -- ### Step 1: the least positive `x` with `(x,0) ∈ I`
  have hex1 : ∃ n : ℕ, 0 < n ∧ ((n : ℤ) : QuadInt k) ∈ I := by
    have hnorm : 0 < z0.norm := QuadInt.norm_pos hk hD hz0ne
    have hmem : ((z0.norm : ℤ) : QuadInt k) ∈ I := by
      have h := I.mul_mem_left z0.conj hz0I
      rwa [QuadInt.conj_mul_conj] at h
    refine ⟨z0.norm.toNat, ?_, ?_⟩
    · omega
    · have hc : ((z0.norm.toNat : ℕ) : ℤ) = z0.norm := Int.toNat_of_nonneg (le_of_lt hnorm)
      rw [hc]; exact hmem
  set d1 : ℕ := Nat.find hex1 with hd1def
  have hd1pos : 0 < d1 := (Nat.find_spec hex1).1
  have hd1mem : ((d1 : ℤ) : QuadInt k) ∈ I := (Nat.find_spec hex1).2
  have hd1min : ∀ m : ℕ, 0 < m → ((m : ℤ) : QuadInt k) ∈ I → d1 ≤ m := by
    intro m hm hmem
    exact Nat.find_min' hex1 ⟨hm, hmem⟩
  have hd1Z : (0 : ℤ) < (d1 : ℤ) := by exact_mod_cast hd1pos
  -- `(x,0) ∈ I ↔ d1 ∣ x`
  have hS1 : ∀ x : ℤ, ((x : QuadInt k) ∈ I) ↔ (d1 : ℤ) ∣ x := by
    intro x
    constructor
    · intro hx
      have hdiv := Int.mul_ediv_add_emod x (d1 : ℤ)
      set r : ℤ := x % (d1 : ℤ) with hr
      have hr0 : 0 ≤ r := Int.emod_nonneg x (ne_of_gt hd1Z)
      have hrlt : r < (d1 : ℤ) := Int.emod_lt_of_pos x hd1Z
      have hqmem : (((x / (d1 : ℤ) : ℤ) : QuadInt k) * ((d1 : ℤ) : QuadInt k)) ∈ I :=
        I.mul_mem_left _ hd1mem
      have hrmem : (r : QuadInt k) ∈ I := by
        have hsub := I.sub_mem hx hqmem
        have heq : (x : QuadInt k) - (((x / (d1 : ℤ) : ℤ) : QuadInt k) * ((d1 : ℤ) : QuadInt k))
            = (r : QuadInt k) := by
          apply QuadInt.ext
          · simp only [QuadInt.sub_x, QuadInt.mul_x, QuadInt.intCast_x, QuadInt.intCast_y, hr]
            linear_combination -hdiv
          · simp only [QuadInt.sub_y, QuadInt.mul_y, QuadInt.intCast_y, hr]
            ring
        rwa [heq] at hsub
      have hr_eq : r = 0 := by
        by_contra hne
        have hpos : 0 < r := by omega
        have hnat : 0 < r.natAbs := by omega
        have hmemNat : ((r.natAbs : ℤ) : QuadInt k) ∈ I := by
          have hc : ((r.natAbs : ℕ) : ℤ) = r := Int.natAbs_of_nonneg hr0
          rw [hc]; exact hrmem
        have := hd1min r.natAbs hnat hmemNat
        omega
      rw [hr_eq] at hdiv
      exact ⟨x / (d1 : ℤ), by linarith⟩
    · intro hdvd
      obtain ⟨m, hm⟩ := hdvd
      have heq : ((x : ℤ) : QuadInt k) = ((m : ℤ) : QuadInt k) * ((d1 : ℤ) : QuadInt k) := by
        rw [hm, Int.cast_mul, mul_comm]
      rw [heq]
      exact I.mul_mem_left _ hd1mem
  -- ### Step 2: the least positive `y` with `(x,y) ∈ I`
  have hex2 : ∃ n : ℕ, 0 < n ∧ ∃ x : ℤ, (⟨x, (n : ℤ)⟩ : QuadInt k) ∈ I := by
    refine ⟨d1, hd1pos, 0, ?_⟩
    have heq : (⟨0, (d1 : ℤ)⟩ : QuadInt k) = ((d1 : ℤ) : QuadInt k) * ⟨0, 1⟩ := by
      apply QuadInt.ext <;> simp [QuadInt.mul_x, QuadInt.mul_y]
    rw [heq]
    exact I.mul_mem_right _ hd1mem
  set d2 : ℕ := Nat.find hex2 with hd2def
  have hd2pos : 0 < d2 := (Nat.find_spec hex2).1
  obtain ⟨r, hrmem⟩ := (Nat.find_spec hex2).2
  have hd2min : ∀ m : ℕ, 0 < m → (∃ x : ℤ, (⟨x, (m : ℤ)⟩ : QuadInt k) ∈ I) → d2 ≤ m := by
    intro m hm hmem
    exact Nat.find_min' hex2 ⟨hm, hmem⟩
  have hd2Z : (0 : ℤ) < (d2 : ℤ) := by exact_mod_cast hd2pos
  -- `(∃ x, (x,y) ∈ I) ↔ d2 ∣ y`
  have hS2 : ∀ y : ℤ, (∃ x : ℤ, (⟨x, y⟩ : QuadInt k) ∈ I) ↔ (d2 : ℤ) ∣ y := by
    intro y
    constructor
    · rintro ⟨x, hx⟩
      have hdiv := Int.mul_ediv_add_emod y (d2 : ℤ)
      set s : ℤ := y % (d2 : ℤ) with hs
      have hs0 : 0 ≤ s := Int.emod_nonneg y (ne_of_gt hd2Z)
      have hslt : s < (d2 : ℤ) := Int.emod_lt_of_pos y hd2Z
      have hqmem : (((y / (d2 : ℤ) : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k)) ∈ I :=
        I.mul_mem_left _ hrmem
      have hs_mem : (⟨x - (y / (d2 : ℤ)) * r, s⟩ : QuadInt k) ∈ I := by
        have hsub := I.sub_mem hx hqmem
        have heq : (⟨x, y⟩ : QuadInt k) - (((y / (d2 : ℤ) : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k))
            = (⟨x - (y / (d2 : ℤ)) * r, s⟩ : QuadInt k) := by
          apply QuadInt.ext
          · simp only [QuadInt.sub_x, QuadInt.mul_x, QuadInt.intCast_x, QuadInt.intCast_y]
            ring
          · simp only [QuadInt.sub_y, QuadInt.mul_y, QuadInt.intCast_x, QuadInt.intCast_y, hs]
            linear_combination -hdiv
        rwa [heq] at hsub
      have hs_eq : s = 0 := by
        by_contra hne
        have hpos : 0 < s := by omega
        have hnat : 0 < s.natAbs := by omega
        have hmemNat : (⟨x - (y / (d2 : ℤ)) * r, (s.natAbs : ℤ)⟩ : QuadInt k) ∈ I := by
          have hc : ((s.natAbs : ℕ) : ℤ) = s := Int.natAbs_of_nonneg hs0
          rw [hc]; exact hs_mem
        have := hd2min s.natAbs hnat ⟨_, hmemNat⟩
        omega
      rw [hs_eq] at hdiv
      exact ⟨y / (d2 : ℤ), by linarith⟩
    · intro hdvd
      obtain ⟨m, hm⟩ := hdvd
      refine ⟨m * r, ?_⟩
      have heq : (⟨m * r, y⟩ : QuadInt k) = ((m : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k) := by
        apply QuadInt.ext
        · simp [QuadInt.mul_x, QuadInt.mul_y]
        · simp [QuadInt.mul_x, QuadInt.mul_y, hm, mul_comm]
      rw [heq]
      exact I.mul_mem_left _ hrmem
  -- ### Step 3: `d2 ∣ d1`, write `d1 = d2 * a`
  have hd2dvd1 : (d2 : ℤ) ∣ (d1 : ℤ) := by
    have hmem : (⟨0, (d1 : ℤ)⟩ : QuadInt k) ∈ I := by
      have heq : (⟨0, (d1 : ℤ)⟩ : QuadInt k) = ((d1 : ℤ) : QuadInt k) * ⟨0, 1⟩ := by
        apply QuadInt.ext <;> simp [QuadInt.mul_x, QuadInt.mul_y]
      rw [heq]
      exact I.mul_mem_right _ hd1mem
    exact (hS2 (d1 : ℤ)).mp ⟨0, hmem⟩
  set a : ℤ := (d1 : ℤ) / (d2 : ℤ) with hadef
  have hd1eq : (d2 : ℤ) * a = (d1 : ℤ) := by
    have hdiv := Int.mul_ediv_add_emod (d1 : ℤ) (d2 : ℤ)
    have hrem : (d1 : ℤ) % (d2 : ℤ) = 0 := Int.emod_eq_zero_of_dvd hd2dvd1
    rw [hrem] at hdiv
    rw [hadef]
    linarith
  have hapos : 0 < a := by nlinarith [hd1Z, hd2Z, hd1eq]
  -- ### Step 4: `d2 ∣ r`, write `r = d2 * t`
  have hd2r : (d2 : ℤ) ∣ r := by
    have hmem : (⟨-(k * (d2 : ℤ)), r + (d2 : ℤ)⟩ : QuadInt k) ∈ I := by
      have heq : (⟨-(k * (d2 : ℤ)), r + (d2 : ℤ)⟩ : QuadInt k)
          = (⟨r, (d2 : ℤ)⟩ : QuadInt k) * ⟨0, 1⟩ := by
        apply QuadInt.ext <;> simp [QuadInt.mul_x, QuadInt.mul_y]
      rw [heq]
      exact I.mul_mem_right _ hrmem
    have hdvd : (d2 : ℤ) ∣ r + (d2 : ℤ) := (hS2 _).mp ⟨_, hmem⟩
    have hdvd' : (d2 : ℤ) ∣ (d2 : ℤ) + r := by rw [add_comm]; exact hdvd
    exact (dvd_add_right (dvd_refl (d2 : ℤ))).mp hdvd'
  set t : ℤ := r / (d2 : ℤ) with htdef
  have hreq : r = (d2 : ℤ) * t := by
    have hdiv := Int.mul_ediv_add_emod r (d2 : ℤ)
    have hrem : r % (d2 : ℤ) = 0 := Int.emod_eq_zero_of_dvd hd2r
    rw [hrem] at hdiv
    rw [htdef]
    linarith
  -- ### Step 5: the classification of the elements of `I`
  have hclass : ∀ z : QuadInt k, z ∈ I ↔ ∃ x y : ℤ, z = ⟨(d2 : ℤ) * (a * x + t * y), (d2 : ℤ) * y⟩ := by
    intro z
    constructor
    · intro hz
      have hy : (d2 : ℤ) ∣ z.y := (hS2 z.y).mp ⟨z.x, by simpa using hz⟩
      obtain ⟨y, hyeq⟩ := hy
      have hmem1 : (((y : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k)) ∈ I :=
        I.mul_mem_left _ hrmem
      have hsub := I.sub_mem hz hmem1
      have hz1 : z - (((y : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k))
          = (⟨z.x - y * r, 0⟩ : QuadInt k) := by
        apply QuadInt.ext
        · simp [QuadInt.mul_x, QuadInt.mul_y]
        · simp [QuadInt.mul_x, QuadInt.mul_y, hyeq]
          ring
      have hd1dvd : (d1 : ℤ) ∣ z.x - y * r := by
        have hcast : ((z.x - y * r : ℤ) : QuadInt k) = ⟨z.x - y * r, 0⟩ := by apply QuadInt.ext <;> simp
        have hmem2 : ((z.x - y * r : ℤ) : QuadInt k) ∈ I := by
          rw [hcast, ← hz1]; exact hsub
        exact (hS1 _).mp hmem2
      obtain ⟨x, hxeq⟩ := hd1dvd
      refine ⟨x, y, ?_⟩
      apply QuadInt.ext
      · linear_combination hxeq + y * hreq - x * hd1eq
      · exact hyeq
    · rintro ⟨x, y, rfl⟩
      have hmem1 : (((x : ℤ) : QuadInt k) * ((d1 : ℤ) : QuadInt k)) ∈ I :=
        I.mul_mem_left _ hd1mem
      have hmem2 : (((y : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k)) ∈ I :=
        I.mul_mem_left _ hrmem
      have hsum := I.add_mem hmem1 hmem2
      have heq : (((x : ℤ) : QuadInt k) * ((d1 : ℤ) : QuadInt k)
            + ((y : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k))
          = (⟨(d2 : ℤ) * (a * x + t * y), (d2 : ℤ) * y⟩ : QuadInt k) := by
        apply QuadInt.ext
        · simp only [QuadInt.add_x, QuadInt.mul_x, QuadInt.intCast_x, QuadInt.intCast_y]
          linear_combination -x * hd1eq + y * hreq
        · simp only [QuadInt.add_y, QuadInt.mul_y, QuadInt.intCast_x, QuadInt.intCast_y]
          ring
      rwa [heq] at hsum
  -- ### Step 6: `a ∣ t^2 + t + k`
  have hadvd : a ∣ t ^ 2 + t + k := by
    have hmem : (⟨-(d2 : ℤ) * (t ^ 2 + t + k), 0⟩ : QuadInt k) ∈ I := by
      have hb1 : ((⟨r, (d2 : ℤ)⟩ : QuadInt k) * ⟨0, 1⟩) ∈ I :=
        I.mul_mem_right _ hrmem
      have hb2 : (((t + 1 : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k)) ∈ I :=
        I.mul_mem_left _ hrmem
      have hsub := I.sub_mem hb1 hb2
      have heq : ((⟨r, (d2 : ℤ)⟩ : QuadInt k) * ⟨0, 1⟩
            - ((t + 1 : ℤ) : QuadInt k) * (⟨r, (d2 : ℤ)⟩ : QuadInt k))
          = (⟨-(d2 : ℤ) * (t ^ 2 + t + k), 0⟩ : QuadInt k) := by
        apply QuadInt.ext
        · simp only [QuadInt.sub_x, QuadInt.mul_x, QuadInt.intCast_x, QuadInt.intCast_y, hreq]
          ring
        · simp only [QuadInt.sub_y, QuadInt.mul_y, QuadInt.intCast_x, QuadInt.intCast_y, hreq]
          ring
      rwa [heq] at hsub
    have hcast2 : ((-(d2 : ℤ) * (t ^ 2 + t + k) : ℤ) : QuadInt k) =
        ⟨-(d2 : ℤ) * (t ^ 2 + t + k), 0⟩ := by
      apply QuadInt.ext <;> simp only [QuadInt.intCast_x, QuadInt.intCast_y]
    have hd1dvd : (d1 : ℤ) ∣ -(d2 : ℤ) * (t ^ 2 + t + k) := (hS1 _).mp (by rwa [hcast2])
    have h1 : (d2 : ℤ) * a ∣ (d2 : ℤ) * (-(t ^ 2 + t + k)) := by
      rw [hd1eq]
      have heq : -(d2 : ℤ) * (t ^ 2 + t + k) = (d2 : ℤ) * (-(t ^ 2 + t + k)) := by ring
      rw [heq] at hd1dvd
      exact hd1dvd
    have h2 : a ∣ -(t ^ 2 + t + k) := (Int.mul_dvd_mul_iff_left (ne_of_gt hd2Z)).mp h1
    exact Int.dvd_neg.mp h2
  exact ⟨(d2 : ℤ), a, t, hd2Z, hapos, hadvd, hclass⟩

/-- Membership in the product `span {c} * I` of a principal ideal with `I`. -/
theorem mem_span_singleton_mul_iff {R : Type*} [CommRing R] (c : R) (I : Ideal R) (z : R) :
    z ∈ Ideal.span {c} * I ↔ ∃ w ∈ I, c * w = z := by
  constructor
  · intro hz
    let S : Submodule R R :=
      { carrier := {z : R | ∃ w ∈ I, c * w = z}
        zero_mem' := ⟨0, I.zero_mem, by rw [mul_zero]⟩
        add_mem' := by
          rintro p q ⟨wp, hwp, rfl⟩ ⟨wq, hwq, rfl⟩
          exact ⟨wp + wq, I.add_mem hwp hwq, by rw [mul_add]⟩
        smul_mem' := by
          rintro r p ⟨wp, hwp, rfl⟩
          exact ⟨r * wp, I.mul_mem_left r hwp, by rw [smul_eq_mul]; ring⟩ }
    have hle : Ideal.span {c} * I ≤ S := by
      rw [Ideal.mul_le]
      intro p hp q hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hp
      exact ⟨r * q, I.mul_mem_left r hq, by ring⟩
    exact hle hz
  · rintro ⟨w, hw, rfl⟩
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton c)) hw

/-- The middle coefficient of a form of discriminant `-D` in terms of its half. -/
theorem coeff_eq {D : ℕ} {k : ℤ} (h3 : D % 4 = 3) (hk : 4 * k - 1 = (D : ℤ))
    (f : QuadFormReduction.Form D) :
    f.val.2.1 = 2 * ((f.val.2.1 - 1) / 2) + 1 ∧
    f.val.1 * f.val.2.2 = ((f.val.2.1 - 1) / 2) ^ 2 + ((f.val.2.1 - 1) / 2) + k := by
  obtain ⟨t, hbt, hac⟩ := QuadFormReduction.b_odd_of_disc h3 hk f.property.2.1
  have ht : (f.val.2.1 - 1) / 2 = t := by
    rw [hbt]
    rw [show (2 * t + 1 - 1 : ℤ) = 2 * t by ring]
    exact Int.mul_ediv_cancel_left t (by norm_num : (2 : ℤ) ≠ 0)
  exact ⟨by rw [ht, hbt], by rw [ht, hac]⟩

/-- The ideal attached to a primitive positive-definite form of discriminant `-D`. -/
def formToIdeal {D : ℕ} {k : ℤ} (h3 : D % 4 = 3) (hk : 4 * k - 1 = (D : ℤ))
    (f : QuadFormReduction.Form D) : Ideal (QuadInt k) where
  carrier := {z : QuadInt k | ∃ x y : ℤ, z = ⟨f.val.1 * x + ((f.val.2.1 - 1) / 2) * y, y⟩}
  zero_mem' := ⟨0, 0, by apply QuadInt.ext <;> simp⟩
  add_mem' := by
    rintro p q ⟨xp, yp, rfl⟩ ⟨xq, yq, rfl⟩
    exact ⟨xp + xq, yp + yq, by apply QuadInt.ext <;> simp <;> ring⟩
  smul_mem' := by
    intro r z hz
    obtain ⟨x, y, rfl⟩ := hz
    obtain ⟨p, s⟩ := r
    obtain ⟨hbt, hac⟩ := coeff_eq h3 hk f
    refine ⟨p * x - s * ((f.val.2.1 - 1) / 2) * x - s * f.val.2.2 * y,
            p * y + s * f.val.1 * x + s * ((f.val.2.1 - 1) / 2) * y + s * y, ?_⟩
    apply QuadInt.ext
    · simp only [smul_eq_mul, QuadInt.mul_x, QuadInt.mul_y]
      linear_combination s * y * hac
    · simp only [smul_eq_mul, QuadInt.mul_x, QuadInt.mul_y]
      ring

theorem formToIdeal_mem_iff {D : ℕ} {k : ℤ} (h3 : D % 4 = 3) (hk : 4 * k - 1 = (D : ℤ))
    (f : QuadFormReduction.Form D) (z : QuadInt k) :
    z ∈ formToIdeal h3 hk f ↔
      ∃ x y : ℤ, z = ⟨f.val.1 * x + ((f.val.2.1 - 1) / 2) * y, y⟩ :=
  Iff.rfl

theorem formToIdeal_ne_bot {D : ℕ} {k : ℤ} (h3 : D % 4 = 3) (hk : 4 * k - 1 = (D : ℤ))
    (f : QuadFormReduction.Form D) : formToIdeal h3 hk f ≠ ⊥ := by
  intro hbot
  have hmem : (⟨f.val.1, 0⟩ : QuadInt k) ∈ formToIdeal h3 hk f := by
    rw [formToIdeal_mem_iff]
    exact ⟨1, 0, by apply QuadInt.ext <;> simp⟩
  rw [hbot] at hmem
  simp only [Submodule.mem_bot] at hmem
  have hx : f.val.1 = 0 := by
    have := congrArg QuadInt.x hmem
    simpa using this
  linarith [f.property.1]

theorem formToIdeal_proper_equiv {D : ℕ} {k : ℤ} (h3 : D % 4 = 3) (hk : 4 * k - 1 = (D : ℤ))
    {f g : QuadFormReduction.Form D} (hfg : QuadFormReduction.proper f g) :
    ∃ l m : QuadInt k, l ≠ 0 ∧ m ≠ 0 ∧
      Ideal.span {l} * formToIdeal h3 hk f = Ideal.span {m} * formToIdeal h3 hk g := by
  classical
  obtain ⟨u, v, w, zz, hdet, heval⟩ := hfg
  obtain ⟨hbtf, hacf⟩ := coeff_eq h3 hk f
  obtain ⟨hbtg, hacg⟩ := coeff_eq h3 hk g
  set tf : ℤ := (f.val.2.1 - 1) / 2 with htf
  set tg : ℤ := (g.val.2.1 - 1) / 2 with htg
  set α : QuadInt k := ⟨f.val.1, 0⟩ with hα
  set β : QuadInt k := ⟨tf, 1⟩ with hβ
  set α' : QuadInt k := ⟨g.val.1, 0⟩ with hα'
  set β' : QuadInt k := ⟨tg, 1⟩ with hβ'
  set α₁ : QuadInt k := u • α' + w • β' with hα₁
  set β₁ : QuadInt k := v • α' + zz • β' with hβ₁
  -- basic combination identities
  have hfcomb : ∀ x y : ℤ, x • α + y • β = (⟨f.val.1 * x + tf * y, y⟩ : QuadInt k) := by
    intro x y
    apply QuadInt.ext <;>
      simp only [hα, hβ, QuadInt.zsmul_x, QuadInt.zsmul_y, QuadInt.add_x, QuadInt.add_y] <;> ring
  have hα'β' : ∀ X Y : ℤ, X • α' + Y • β' = (⟨g.val.1 * X + tg * Y, Y⟩ : QuadInt k) := by
    intro X Y
    apply QuadInt.ext <;>
      simp only [hα', hβ', QuadInt.zsmul_x, QuadInt.zsmul_y, QuadInt.add_x, QuadInt.add_y] <;> ring
  have hα₁β₁ : ∀ x y : ℤ, x • α₁ + y • β₁ =
      (u * x + v * y) • α' + (w * x + zz * y) • β' := by
    intro x y
    rw [hα₁, hβ₁]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  -- membership descriptions
  have hfcar : ∀ z : QuadInt k, z ∈ formToIdeal h3 hk f ↔ ∃ x y : ℤ, z = x • α + y • β := by
    intro z
    rw [formToIdeal_mem_iff]
    constructor
    · rintro ⟨x, y, hxy⟩
      refine ⟨x, y, ?_⟩
      rw [hxy, hfcomb x y, ← htf]
    · rintro ⟨x, y, hxy⟩
      refine ⟨x, y, ?_⟩
      rw [hxy, hfcomb x y, ← htf]
  have hgcar : ∀ z : QuadInt k, z ∈ formToIdeal h3 hk g ↔ ∃ x y : ℤ, z = x • α₁ + y • β₁ := by
    intro z
    rw [formToIdeal_mem_iff]
    constructor
    · rintro ⟨X, Y, hXY⟩
      refine ⟨zz * X - v * Y, -w * X + u * Y, ?_⟩
      have hXu : u * (zz * X - v * Y) + v * (-w * X + u * Y) = X := by
        linear_combination X * hdet
      have hYw : w * (zz * X - v * Y) + zz * (-w * X + u * Y) = Y := by
        linear_combination Y * hdet
      rw [hXY, hα₁β₁, hXu, hYw, hα'β' X Y, ← htg]
    · rintro ⟨x, y, hxy⟩
      refine ⟨u * x + v * y, w * x + zz * y, ?_⟩
      rw [hxy, hα₁β₁ x y, hα'β' (u * x + v * y) (w * x + zz * y), ← htg]
  -- norm computations
  have hnorm : ∀ X Y : ℤ, (X • α' + Y • β').norm = g.val.1 * QuadFormReduction.evaluate g X Y := by
    intro X Y
    rw [hα'β' X Y]
    simp only [QuadInt.norm_x, QuadFormReduction.evaluate]
    linear_combination -g.val.1 * X * Y * hbtg - Y ^ 2 * hacg
  have hnorm2 : ∀ x y : ℤ, (x • α₁ + y • β₁).norm = g.val.1 * QuadFormReduction.evaluate f x y := by
    intro x y
    rw [hα₁β₁ x y, hnorm (u * x + v * y) (w * x + zz * y), ← heval x y]
  have hα₁norm : α₁.norm = g.val.1 * f.val.1 := by
    have h : (1 : ℤ) • α₁ + (0 : ℤ) • β₁ = α₁ := by simp
    rw [← h, hnorm2 1 0]
    simp only [QuadFormReduction.evaluate]
    ring
  have hβ₁norm : β₁.norm = g.val.1 * f.val.2.2 := by
    have h : (0 : ℤ) • α₁ + (1 : ℤ) • β₁ = β₁ := by simp
    rw [← h, hnorm2 0 1]
    simp only [QuadFormReduction.evaluate]
    ring
  have hsum_norm : (α₁ + β₁).norm = g.val.1 * QuadFormReduction.evaluate f 1 1 := by
    have h : (1 : ℤ) • α₁ + (1 : ℤ) • β₁ = α₁ + β₁ := by simp
    rw [← h, hnorm2 1 1]
  -- (iii)
  have hiii : α₁ * α₁.conj = α' * α := by
    rw [QuadInt.mul_conj, hα₁norm, hα', hα]
    apply QuadInt.ext <;> simp [QuadInt.mul_x, QuadInt.mul_y]
  -- (iv)
  have hdet_y : (β₁ * α₁.conj).y = g.val.1 := by
    rw [QuadInt.mul_conj_y, hα₁, hβ₁, QuadInt.det_linear_comb u v w zz α' β', hdet, one_mul]
    simp [QuadInt.det_apply, hα', hβ']
  have hiv : β₁ * α₁.conj = α' * β := by
    apply QuadInt.ext
    · rw [show (α' * β).x = g.val.1 * tf from by
            rw [hα', hβ]; simp only [QuadInt.mul_x, QuadInt.mul_y]; ring]
      have hxy := QuadInt.two_mul_mul_conj_x_add_y α₁ β₁
      rw [hdet_y, hsum_norm, hα₁norm, hβ₁norm] at hxy
      have hE : QuadFormReduction.evaluate f 1 1 = f.val.1 + f.val.2.1 + f.val.2.2 := by
        simp only [QuadFormReduction.evaluate]; ring
      rw [hE, hbtf] at hxy
      linarith
    · rw [hdet_y, hα', hβ]; simp only [QuadInt.mul_x, QuadInt.mul_y]; ring
  -- (v)
  refine ⟨α', α₁.conj, ?_, ?_, ?_⟩
  · intro h
    have : g.val.1 = 0 := by simpa [hα'] using congrArg QuadInt.x h
    linarith [g.property.1]
  · intro hconj
    have hα₁0 : α₁ = 0 := by
      have h1 : α₁.x + α₁.y = 0 := by
        have := congrArg QuadInt.x hconj
        simpa [QuadInt.conj] using this
      have h2 : α₁.y = 0 := by
        have := congrArg QuadInt.y hconj
        simpa [QuadInt.conj] using this
      apply QuadInt.ext <;> simp only [QuadInt.zero_x, QuadInt.zero_y]
      · linarith [h1, h2]
      · exact h2
    have hnorm0 : α₁.norm = 0 := by rw [hα₁0]; simp [QuadInt.norm]
    rw [hα₁norm] at hnorm0
    nlinarith [f.property.1, g.property.1, hnorm0]
  · have hkey : ∀ x y : ℤ, α₁.conj * (x • α₁ + y • β₁) = α' * (x • α + y • β) := by
      intro x y
      have h1 : α₁.conj * α₁ = α' * α := by rw [mul_comm α₁.conj α₁]; exact hiii
      have h2 : α₁.conj * β₁ = α' * β := by rw [mul_comm α₁.conj β₁]; exact hiv
      simp only [zsmul_eq_mul]
      linear_combination (x : QuadInt k) * h1 + (y : QuadInt k) * h2
    ext q
    rw [mem_span_singleton_mul_iff, mem_span_singleton_mul_iff]
    constructor
    · rintro ⟨wf, hwf, hwfq⟩
      rw [hfcar] at hwf
      obtain ⟨x, y, rfl⟩ := hwf
      refine ⟨x • α₁ + y • β₁, ?_, ?_⟩
      · rw [hgcar]; exact ⟨x, y, rfl⟩
      · rw [hkey x y]; exact hwfq
    · rintro ⟨wg, hwg, hwgq⟩
      rw [hgcar] at hwg
      obtain ⟨x, y, rfl⟩ := hwg
      refine ⟨x • α + y • β, ?_, ?_⟩
      · rw [hfcar]; exact ⟨x, y, rfl⟩
      · rw [← hkey x y]; exact hwgq

section ClassGroupEquiv
open QuadFormReduction

/-- For `D ≡ 3 (mod 4)` a form of discriminant `-D` has `b = 2 t + 1` with `t = (b-1)/2`
and `a * c = t² + t + k`. -/
theorem b_odd_of_disc_half {D : ℕ} (h3 : D % 4 = 3) {k a b c : ℤ} (hk : 4 * k - 1 = (D : ℤ))
    (hdisc : b ^ 2 - 4 * a * c = -(D : ℤ)) :
    b = 2 * ((b - 1) / 2) + 1 ∧ a * c = ((b - 1) / 2) ^ 2 + ((b - 1) / 2) + k := by
  have hodd : Odd b := by
    rw [Int.not_even_iff_odd.symm]
    intro hev
    obtain ⟨m, rfl⟩ := hev
    have h4 : (4 : ℤ) ∣ (D : ℤ) := by
      have : (D : ℤ) = 4 * (a * c - m ^ 2) := by nlinarith [hdisc]
      exact ⟨a * c - m ^ 2, by rw [this]⟩
    have h0 : D % 4 = 0 := by
      have := Int.emod_eq_zero_of_dvd h4
      omega
    omega
  obtain ⟨m, hm⟩ := hodd
  have hb2 : (2 : ℤ) ∣ (b - 1) := ⟨m, by omega⟩
  have hbt : b = 2 * ((b - 1) / 2) + 1 := by
    have := Int.ediv_mul_cancel hb2
    omega
  refine ⟨hbt, ?_⟩
  nlinarith [hdisc, hk, hbt]

/- ## Hermite normal forms of ideals -/

/-- The data of a Hermite normal form of an ideal. -/
structure HNFData (k : ℤ) (I : Ideal (QuadInt k)) where
  d : ℤ
  a : ℤ
  t : ℤ
  hd : 0 < d
  ha : 0 < a
  hdiv : a ∣ t ^ 2 + t + k
  hmem : ∀ z : QuadInt k, z ∈ I ↔ ∃ x y : ℤ, z = ⟨d * (a * x + t * y), d * y⟩

noncomputable def HNFData.of {k : ℤ} {I : Ideal (QuadInt k)} (h : IdealHasHNF k I) :
    HNFData k I :=
  let hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  ⟨Classical.choose h,
   Classical.choose (Classical.choose_spec h),
   Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
   hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩

variable {D : ℕ} {k : ℤ}

/-- The `c` coefficient attached to the HNF of an ideal. -/
noncomputable def hnfC (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) : ℤ :=
  ((HNFData.of (hHNF I hI)).t ^ 2 + (HNFData.of (hHNF I hI)).t + k) / (HNFData.of (hHNF I hI)).a

theorem hnfC_mul (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (HNFData.of (hHNF I hI)).a * hnfC hHNF I hI =
      (HNFData.of (hHNF I hI)).t ^ 2 + (HNFData.of (hHNF I hI)).t + k := by
  rw [hnfC, mul_comm]
  exact Int.ediv_mul_cancel (HNFData.of (hHNF I hI)).hdiv

/-- The positive definite binary quadratic form attached to the HNF of an ideal. -/
noncomputable def hnfForm
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hk : 4 * k - 1 = (D : ℤ))
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) : Form D :=
  ⟨((HNFData.of (hHNF I hI)).a, 2 * (HNFData.of (hHNF I hI)).t + 1, hnfC hHNF I hI), by
    have hc := hnfC_mul hHNF I hI
    have hdisc : (2 * (HNFData.of (hHNF I hI)).t + 1) ^ 2 -
        4 * (HNFData.of (hHNF I hI)).a * hnfC hHNF I hI = -(D : ℤ) := by
      nlinarith [hc, hk]
    exact ⟨(HNFData.of (hHNF I hI)).ha, hdisc, hAutoPrim _ _ _ hdisc⟩⟩

@[simp] theorem hnfForm_val₁ {D : ℕ} {k : ℤ}
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hk : 4 * k - 1 = (D : ℤ))
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (hnfForm hAutoPrim hk hHNF I hI).val.1 = (HNFData.of (hHNF I hI)).a := rfl

@[simp] theorem hnfForm_val₂₁ {D : ℕ} {k : ℤ}
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hk : 4 * k - 1 = (D : ℤ))
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (hnfForm hAutoPrim hk hHNF I hI).val.2.1 = 2 * (HNFData.of (hHNF I hI)).t + 1 := rfl

@[simp] theorem hnfForm_val₂₂ {D : ℕ} {k : ℤ}
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hk : 4 * k - 1 = (D : ℤ))
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (hnfForm hAutoPrim hk hHNF I hI).val.2.2 = hnfC hHNF I hI := rfl

/- ## The ideal–form correspondence -/


noncomputable def hnfAlpha
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) : QuadInt k :=
  ⟨(HNFData.of (hHNF I hI)).d * (HNFData.of (hHNF I hI)).a, 0⟩

noncomputable def hnfBeta
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) : QuadInt k :=
  ⟨(HNFData.of (hHNF I hI)).d * (HNFData.of (hHNF I hI)).t, (HNFData.of (hHNF I hI)).d⟩

@[simp] theorem hnfAlpha_x
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (hnfAlpha hHNF I hI).x = (HNFData.of (hHNF I hI)).d * (HNFData.of (hHNF I hI)).a := rfl

@[simp] theorem hnfAlpha_y
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (hnfAlpha hHNF I hI).y = 0 := rfl

@[simp] theorem hnfBeta_x
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (hnfBeta hHNF I hI).x = (HNFData.of (hHNF I hI)).d * (HNFData.of (hHNF I hI)).t := rfl

@[simp] theorem hnfBeta_y
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    (hnfBeta hHNF I hI).y = (HNFData.of (hHNF I hI)).d := rfl

theorem two_mul_add_one_sub_one_div_two (t : ℤ) : (2 * t + 1 - 1) / 2 = t := by
  have h : (2 : ℤ) * t + 1 - 1 = 2 * t := by ring
  rw [h, Int.mul_ediv_cancel_left t (show (2 : ℤ) ≠ 0 by norm_num)]

theorem hnf_det_pos
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    0 < QuadInt.det (hnfAlpha hHNF I hI) (hnfBeta hHNF I hI) := by
  have hd : 0 < (HNFData.of (hHNF I hI)).d := (HNFData.of (hHNF I hI)).hd
  have ha : 0 < (HNFData.of (hHNF I hI)).a := (HNFData.of (hHNF I hI)).ha
  have hdet : QuadInt.det (hnfAlpha hHNF I hI) (hnfBeta hHNF I hI)
      = (HNFData.of (hHNF I hI)).d * (HNFData.of (hHNF I hI)).a
        * (HNFData.of (hHNF I hI)).d := by
    simp [QuadInt.det_apply]
  rw [hdet]
  exact mul_pos (mul_pos hd ha) hd

theorem hnf_mem
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) (z : QuadInt k) :
    z ∈ I ↔ ∃ x y : ℤ, z = x • hnfAlpha hHNF I hI + y • hnfBeta hHNF I hI := by
  rw [(HNFData.of (hHNF I hI)).hmem z]
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, y, by apply QuadInt.ext <;> simp <;> ring⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, y, by apply QuadInt.ext <;> simp <;> ring⟩

theorem hnf_norm
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hk : 4 * k - 1 = (D : ℤ))
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) (x y : ℤ) :
    (x • hnfAlpha hHNF I hI + y • hnfBeta hHNF I hI).norm
      = QuadInt.det (hnfAlpha hHNF I hI) (hnfBeta hHNF I hI)
        * evaluate (hnfForm hAutoPrim hk hHNF I hI) x y := by
  have hc := hnfC_mul hHNF I hI
  simp only [QuadInt.norm_x, QuadInt.det_apply, QuadInt.zsmul_x, QuadInt.zsmul_y,
    QuadInt.add_x, QuadInt.add_y, hnfAlpha_x, hnfAlpha_y, hnfBeta_x, hnfBeta_y,
    hnfForm_val₁, hnfForm_val₂₁, hnfForm_val₂₂, evaluate]
  linear_combination -((HNFData.of (hHNF I hI)).d ^ 2 * y ^ 2) * hc

theorem proper_of_same_lattice {D : ℕ} {k : ℤ}
    (α₁ β₁ α₂ β₂ : QuadInt k) (f₁ f₂ : Form D)
    (hd1 : 0 < QuadInt.det α₁ β₁) (hd2 : 0 < QuadInt.det α₂ β₂)
    (hn1 : ∀ x y : ℤ, (x • α₁ + y • β₁).norm = QuadInt.det α₁ β₁ * evaluate f₁ x y)
    (hn2 : ∀ x y : ℤ, (x • α₂ + y • β₂).norm = QuadInt.det α₂ β₂ * evaluate f₂ x y)
    (h12 : ∀ x y : ℤ, ∃ X Y : ℤ, x • α₁ + y • β₁ = X • α₂ + Y • β₂)
    (h21 : ∀ X Y : ℤ, ∃ x y : ℤ, X • α₂ + Y • β₂ = x • α₁ + y • β₁) :
    proper f₁ f₂ := by
  obtain ⟨u, w, huw⟩ := h12 1 0
  obtain ⟨v, z, hvz⟩ := h12 0 1
  obtain ⟨u', w', hu'w'⟩ := h21 1 0
  obtain ⟨v', z', hv'z'⟩ := h21 0 1
  have hα₁ : α₁ = u • α₂ + w • β₂ := by simpa using huw
  have hβ₁ : β₁ = v • α₂ + z • β₂ := by simpa using hvz
  have hα₂ : α₂ = u' • α₁ + w' • β₁ := by simpa using hu'w'
  have hβ₂ : β₂ = v' • α₁ + z' • β₁ := by simpa using hv'z'
  have e1 : QuadInt.det α₁ β₁ = (u * z - v * w) * QuadInt.det α₂ β₂ := by
    rw [hα₁, hβ₁]
    exact QuadInt.det_linear_comb u v w z α₂ β₂
  have e2 : QuadInt.det α₂ β₂ = (u' * z' - v' * w') * QuadInt.det α₁ β₁ := by
    rw [hα₂, hβ₂]
    exact QuadInt.det_linear_comb u' v' w' z' α₁ β₁
  have hs : u * z - v * w = 1 := by
    have hpos : 0 < u * z - v * w :=
      pos_of_mul_pos_left (e1 ▸ hd1) (le_of_lt hd2)
    have hprod : (u * z - v * w) * (u' * z' - v' * w') = 1 := by
      have h12' : ((u * z - v * w) * (u' * z' - v' * w')) * QuadInt.det α₁ β₁ =
          1 * QuadInt.det α₁ β₁ := by
        linear_combination -e1 - (u * z - v * w) * e2
      exact mul_right_cancel₀ (ne_of_gt hd1) h12'
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h | h <;> omega
  have hdet : QuadInt.det α₁ β₁ = QuadInt.det α₂ β₂ := by
    rw [hs] at e1
    simpa using e1
  refine ⟨u, v, w, z, hs, ?_⟩
  intro x y
  have hlin : x • α₁ + y • β₁ = (x * u + y * v) • α₂ + (x * w + y * z) • β₂ := by
    rw [hα₁, hβ₁]
    apply QuadInt.ext <;> simp <;> ring
  have h1 := hn1 x y
  have h2 := hn2 (x * u + y * v) (x * w + y * z)
  rw [hlin] at h1
  rw [hdet] at h1
  have heq : QuadInt.det α₂ β₂ * evaluate f₁ x y
      = QuadInt.det α₂ β₂ * evaluate f₂ (x * u + y * v) (x * w + y * z) := by
    rw [← h1, h2]
  have hc := mul_left_cancel₀ (ne_of_gt hd2) heq
  rw [show x * u + y * v = u * x + v * y by ring,
      show x * w + y * z = w * x + z * y by ring] at hc
  exact hc

theorem hnfForm_proper_of_mk0_eq {D : ℕ} {k : ℤ} [IsDedekindDomain (QuadInt k)]
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hk : 4 * k - 1 = (D : ℤ)) (hD : 0 < D)
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (I J : nonZeroDivisors (Ideal (QuadInt k)))
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    proper (hnfForm hAutoPrim hk hHNF (I : Ideal (QuadInt k)) (mem_nonZeroDivisors_iff_ne_zero.mp I.2))
      (hnfForm hAutoPrim hk hHNF (J : Ideal (QuadInt k)) (mem_nonZeroDivisors_iff_ne_zero.mp J.2)) := by
  have hI : (I : Ideal (QuadInt k)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hJ : (J : Ideal (QuadInt k)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp J.2
  obtain ⟨l, m, hl, hm, hspan⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  have hLn : 0 < l.norm := QuadInt.norm_pos hk hD hl
  have hMn : 0 < m.norm := QuadInt.norm_pos hk hD hm
  have hd1 : 0 < QuadInt.det (l * hnfAlpha hHNF (I : Ideal (QuadInt k)) hI)
      (l * hnfBeta hHNF (I : Ideal (QuadInt k)) hI) := by
    rw [QuadInt.det_mul_left]
    exact mul_pos hLn (hnf_det_pos hHNF (I : Ideal (QuadInt k)) hI)
  have hd2 : 0 < QuadInt.det (m * hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ)
      (m * hnfBeta hHNF (J : Ideal (QuadInt k)) hJ) := by
    rw [QuadInt.det_mul_left]
    exact mul_pos hMn (hnf_det_pos hHNF (J : Ideal (QuadInt k)) hJ)
  have hL : ∀ x y : ℤ, x • (l * hnfAlpha hHNF (I : Ideal (QuadInt k)) hI)
      + y • (l * hnfBeta hHNF (I : Ideal (QuadInt k)) hI)
      = l * (x • hnfAlpha hHNF (I : Ideal (QuadInt k)) hI
        + y • hnfBeta hHNF (I : Ideal (QuadInt k)) hI) := by
    intro x y; apply QuadInt.ext <;> simp <;> ring
  have hM : ∀ x y : ℤ, x • (m * hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ)
      + y • (m * hnfBeta hHNF (J : Ideal (QuadInt k)) hJ)
      = m * (x • hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ
        + y • hnfBeta hHNF (J : Ideal (QuadInt k)) hJ) := by
    intro x y; apply QuadInt.ext <;> simp <;> ring
  have hn1 : ∀ x y : ℤ,
      (x • (l * hnfAlpha hHNF (I : Ideal (QuadInt k)) hI)
        + y • (l * hnfBeta hHNF (I : Ideal (QuadInt k)) hI)).norm
      = QuadInt.det (l * hnfAlpha hHNF (I : Ideal (QuadInt k)) hI)
          (l * hnfBeta hHNF (I : Ideal (QuadInt k)) hI)
        * evaluate (hnfForm hAutoPrim hk hHNF (I : Ideal (QuadInt k)) hI) x y := by
    intro x y
    rw [hL x y, QuadInt.norm_mul, hnf_norm hAutoPrim hk hHNF (I : Ideal (QuadInt k)) hI x y,
      QuadInt.det_mul_left]
    ring
  have hn2 : ∀ x y : ℤ,
      (x • (m * hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ)
        + y • (m * hnfBeta hHNF (J : Ideal (QuadInt k)) hJ)).norm
      = QuadInt.det (m * hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ)
          (m * hnfBeta hHNF (J : Ideal (QuadInt k)) hJ)
        * evaluate (hnfForm hAutoPrim hk hHNF (J : Ideal (QuadInt k)) hJ) x y := by
    intro x y
    rw [hM x y, QuadInt.norm_mul, hnf_norm hAutoPrim hk hHNF (J : Ideal (QuadInt k)) hJ x y,
      QuadInt.det_mul_left]
    ring
  have h12 : ∀ x y : ℤ, ∃ X Y : ℤ,
      x • (l * hnfAlpha hHNF (I : Ideal (QuadInt k)) hI)
        + y • (l * hnfBeta hHNF (I : Ideal (QuadInt k)) hI)
      = X • (m * hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ)
        + Y • (m * hnfBeta hHNF (J : Ideal (QuadInt k)) hJ) := by
    intro x y
    have hwI : x • hnfAlpha hHNF (I : Ideal (QuadInt k)) hI
        + y • hnfBeta hHNF (I : Ideal (QuadInt k)) hI ∈ (I : Ideal (QuadInt k)) :=
      (hnf_mem hHNF (I : Ideal (QuadInt k)) hI _).mpr ⟨x, y, rfl⟩
    have hmem1 : l * (x • hnfAlpha hHNF (I : Ideal (QuadInt k)) hI
        + y • hnfBeta hHNF (I : Ideal (QuadInt k)) hI) ∈
        Ideal.span {l} * (I : Ideal (QuadInt k)) :=
      (mem_span_singleton_mul_iff l (I : Ideal (QuadInt k)) _).mpr ⟨_, hwI, rfl⟩
    rw [hspan] at hmem1
    obtain ⟨w, hwJ, hweq⟩ := (mem_span_singleton_mul_iff m (J : Ideal (QuadInt k)) _).mp hmem1
    obtain ⟨X, Y, hXY⟩ := (hnf_mem hHNF (J : Ideal (QuadInt k)) hJ w).mp hwJ
    refine ⟨X, Y, ?_⟩
    rw [hL x y, ← hweq, hXY]
    apply QuadInt.ext <;> simp <;> ring
  have h21 : ∀ X Y : ℤ, ∃ x y : ℤ,
      X • (m * hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ)
        + Y • (m * hnfBeta hHNF (J : Ideal (QuadInt k)) hJ)
      = x • (l * hnfAlpha hHNF (I : Ideal (QuadInt k)) hI)
        + y • (l * hnfBeta hHNF (I : Ideal (QuadInt k)) hI) := by
    intro X Y
    have hwJ : X • hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ
        + Y • hnfBeta hHNF (J : Ideal (QuadInt k)) hJ ∈ (J : Ideal (QuadInt k)) :=
      (hnf_mem hHNF (J : Ideal (QuadInt k)) hJ _).mpr ⟨X, Y, rfl⟩
    have hmem2 : m * (X • hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ
        + Y • hnfBeta hHNF (J : Ideal (QuadInt k)) hJ) ∈
        Ideal.span {m} * (J : Ideal (QuadInt k)) :=
      (mem_span_singleton_mul_iff m (J : Ideal (QuadInt k)) _).mpr ⟨_, hwJ, rfl⟩
    rw [← hspan] at hmem2
    obtain ⟨w, hwI, hweq⟩ := (mem_span_singleton_mul_iff l (I : Ideal (QuadInt k)) _).mp hmem2
    obtain ⟨x, y, hxy⟩ := (hnf_mem hHNF (I : Ideal (QuadInt k)) hI w).mp hwI
    refine ⟨x, y, ?_⟩
    rw [hM X Y, ← hweq, hxy]
    apply QuadInt.ext <;> simp <;> ring
  exact proper_of_same_lattice
    (l * hnfAlpha hHNF (I : Ideal (QuadInt k)) hI) (l * hnfBeta hHNF (I : Ideal (QuadInt k)) hI)
    (m * hnfAlpha hHNF (J : Ideal (QuadInt k)) hJ) (m * hnfBeta hHNF (J : Ideal (QuadInt k)) hJ)
    (hnfForm hAutoPrim hk hHNF (I : Ideal (QuadInt k)) hI)
    (hnfForm hAutoPrim hk hHNF (J : Ideal (QuadInt k)) hJ)
    hd1 hd2 hn1 hn2 h12 h21

theorem hnf_span_formToIdeal {D : ℕ} {k : ℤ}
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hk : 4 * k - 1 = (D : ℤ))
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (formToIdeal : Form D → Ideal (QuadInt k))
    (hFormMem : ∀ (f : Form D) (z : QuadInt k),
      z ∈ formToIdeal f ↔ ∃ x y : ℤ, z = ⟨f.val.1 * x + ((f.val.2.1 - 1) / 2) * y, y⟩)
    (I : Ideal (QuadInt k)) (hI : I ≠ ⊥) :
    Ideal.span {(⟨(HNFData.of (hHNF I hI)).d, 0⟩ : QuadInt k)}
      * formToIdeal (hnfForm hAutoPrim hk hHNF I hI) = I := by
  ext z
  rw [mem_span_singleton_mul_iff, (HNFData.of (hHNF I hI)).hmem z]
  constructor
  · rintro ⟨w, hw, hzw⟩
    obtain ⟨x, y, hxy⟩ := (hFormMem _ w).mp hw
    refine ⟨x, y, ?_⟩
    rw [← hzw, hxy]
    apply QuadInt.ext <;> simp only [QuadInt.mul_x, QuadInt.mul_y, hnfForm_val₁, hnfForm_val₂₁,
      two_mul_add_one_sub_one_div_two] <;> ring
  · rintro ⟨x, y, hxy⟩
    refine ⟨(⟨(HNFData.of (hHNF I hI)).a * x + (HNFData.of (hHNF I hI)).t * y, y⟩ : QuadInt k),
      (hFormMem _ _).mpr ⟨x, y, ?_⟩, ?_⟩
    · apply QuadInt.ext <;> simp only [hnfForm_val₁, hnfForm_val₂₁,
        two_mul_add_one_sub_one_div_two]
    · rw [hxy]
      apply QuadInt.ext <;> simp only [QuadInt.mul_x, QuadInt.mul_y] <;> ring

theorem classGroup_equiv_quot_proper_of_parts
    (D : ℕ) (_hsq : Squarefree D) (h3 : D % 4 = 3) (k : ℤ) (hk : 4 * k - 1 = (D : ℤ))
    [IsDedekindDomain (QuadInt k)]
    (hAutoPrim : ∀ a b c : ℤ, b ^ 2 - 4 * a * c = -(D : ℤ) → Int.gcd (Int.gcd a b) c = 1)
    (hHNF : ∀ I : Ideal (QuadInt k), I ≠ ⊥ → IdealHasHNF k I)
    (formToIdeal : Form D → Ideal (QuadInt k))
    (hFormMem : ∀ (f : Form D) (z : QuadInt k), z ∈ formToIdeal f ↔ ∃ x y : ℤ, z = ⟨f.val.1 * x + ((f.val.2.1 - 1) / 2) * y, y⟩)
    (hFormNeBot : ∀ f : Form D, formToIdeal f ≠ ⊥)
    (hProperFwd : ∀ f g : Form D, proper f g → ∃ l m : QuadInt k, l ≠ 0 ∧ m ≠ 0 ∧ Ideal.span {l} * formToIdeal f = Ideal.span {m} * formToIdeal g) :
    Nonempty (ClassGroup (QuadInt k) ≃ Quot (@proper D)) := by
  have hD : 0 < D := by omega
  have hsurj : Function.Surjective (ClassGroup.mk0 : nonZeroDivisors (Ideal (QuadInt k)) → ClassGroup (QuadInt k)) :=
    ClassGroup.mk0_surjective
  let toFun : ClassGroup (QuadInt k) → Quot (@proper D) := fun C =>
    Quot.mk (@proper D)
      (hnfForm hAutoPrim hk hHNF (Classical.choose (hsurj C)).1
        (mem_nonZeroDivisors_iff_ne_zero.mp (Classical.choose (hsurj C)).2))
  let invFun : Quot (@proper D) → ClassGroup (QuadInt k) :=
    Quot.lift
      (fun f : Form D => ClassGroup.mk0 ⟨formToIdeal f, mem_nonZeroDivisors_of_ne_zero (hFormNeBot f)⟩)
      (by
        intro f g hfg
        obtain ⟨l, m, hl, hm, hspan⟩ := hProperFwd f g hfg
        exact ClassGroup.mk0_eq_mk0_iff.mpr ⟨l, m, hl, hm, hspan⟩)
  have invFun_mk : ∀ f : Form D, invFun (Quot.mk (@proper D) f) =
      ClassGroup.mk0 ⟨formToIdeal f, mem_nonZeroDivisors_of_ne_zero (hFormNeBot f)⟩ := fun f => rfl
  have toFun_mk0 : ∀ I : nonZeroDivisors (Ideal (QuadInt k)), toFun (ClassGroup.mk0 I) =
      Quot.mk (@proper D)
        (hnfForm hAutoPrim hk hHNF (I : Ideal (QuadInt k)) (mem_nonZeroDivisors_iff_ne_zero.mp I.2)) := by
    intro I
    have hspec := Classical.choose_spec (hsurj (ClassGroup.mk0 I))
    exact Quot.sound (hnfForm_proper_of_mk0_eq hAutoPrim hk hD hHNF
      (Classical.choose (hsurj (ClassGroup.mk0 I))) I hspec)
  have left_inv : Function.LeftInverse invFun toFun := by
    intro C
    obtain ⟨I, hImk⟩ := hsurj C
    rw [← hImk, toFun_mk0 I, invFun_mk]
    have hI : (I : Ideal (QuadInt k)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
    refine ClassGroup.mk0_eq_mk0_iff.mpr
      ⟨(⟨(HNFData.of (hHNF (I : Ideal (QuadInt k)) hI)).d, 0⟩ : QuadInt k), 1, ?_, one_ne_zero, ?_⟩
    · intro hzero
      have hx : (HNFData.of (hHNF (I : Ideal (QuadInt k)) hI)).d = 0 := by
        have hxc := congrArg QuadInt.x hzero
        simpa using hxc
      exact absurd hx (ne_of_gt (HNFData.of (hHNF (I : Ideal (QuadInt k)) hI)).hd)
    · rw [hnf_span_formToIdeal hAutoPrim hk hHNF formToIdeal hFormMem (I : Ideal (QuadInt k)) hI,
          Ideal.span_singleton_one, Ideal.top_mul]
  have right_inv : Function.RightInverse invFun toFun := by
    intro q
    induction q using Quot.ind with
    | _ f =>
      rw [invFun_mk f, toFun_mk0 ⟨formToIdeal f, mem_nonZeroDivisors_of_ne_zero (hFormNeBot f)⟩]
      apply Quot.sound
      have hIf : (formToIdeal f) ≠ ⊥ :=
        mem_nonZeroDivisors_iff_ne_zero.mp (mem_nonZeroDivisors_of_ne_zero (hFormNeBot f))
      show proper (hnfForm hAutoPrim hk hHNF (formToIdeal f) hIf) f
      have hb := b_odd_of_disc_half h3 hk f.property.2.1
      have hd1 : 0 < QuadInt.det (hnfAlpha hHNF (formToIdeal f) hIf)
          (hnfBeta hHNF (formToIdeal f) hIf) := hnf_det_pos hHNF (formToIdeal f) hIf
      have hd2 : 0 < QuadInt.det (⟨f.val.1, 0⟩ : QuadInt k)
          (⟨(f.val.2.1 - 1) / 2, 1⟩ : QuadInt k) := by
        simpa [QuadInt.det_apply] using f.property.1
      have hn1 : ∀ x y : ℤ,
          (x • hnfAlpha hHNF (formToIdeal f) hIf + y • hnfBeta hHNF (formToIdeal f) hIf).norm
          = QuadInt.det (hnfAlpha hHNF (formToIdeal f) hIf) (hnfBeta hHNF (formToIdeal f) hIf)
            * evaluate (hnfForm hAutoPrim hk hHNF (formToIdeal f) hIf) x y := fun x y =>
        hnf_norm hAutoPrim hk hHNF (formToIdeal f) hIf x y
      have hn2 : ∀ x y : ℤ,
          (x • (⟨f.val.1, 0⟩ : QuadInt k) + y • (⟨(f.val.2.1 - 1) / 2, 1⟩ : QuadInt k)).norm
          = QuadInt.det (⟨f.val.1, 0⟩ : QuadInt k) (⟨(f.val.2.1 - 1) / 2, 1⟩ : QuadInt k)
            * evaluate f x y := by
        intro x y
        simp only [QuadInt.norm_x, QuadInt.det_apply, QuadInt.zsmul_x, QuadInt.zsmul_y,
          QuadInt.add_x, QuadInt.add_y, evaluate]
        linear_combination -(f.val.1 * x * y) * hb.1 - y ^ 2 * hb.2
      have h12 : ∀ x y : ℤ, ∃ X Y : ℤ,
          x • hnfAlpha hHNF (formToIdeal f) hIf + y • hnfBeta hHNF (formToIdeal f) hIf
          = X • (⟨f.val.1, 0⟩ : QuadInt k) + Y • (⟨(f.val.2.1 - 1) / 2, 1⟩ : QuadInt k) := by
        intro x y
        have hmem : x • hnfAlpha hHNF (formToIdeal f) hIf
            + y • hnfBeta hHNF (formToIdeal f) hIf ∈ formToIdeal f :=
          (hnf_mem hHNF (formToIdeal f) hIf _).mpr ⟨x, y, rfl⟩
        obtain ⟨X, Y, hXY⟩ := (hFormMem f _).mp hmem
        refine ⟨X, Y, ?_⟩
        rw [hXY]
        apply QuadInt.ext <;> simp <;> ring
      have h21 : ∀ X Y : ℤ, ∃ x y : ℤ,
          X • (⟨f.val.1, 0⟩ : QuadInt k) + Y • (⟨(f.val.2.1 - 1) / 2, 1⟩ : QuadInt k)
          = x • hnfAlpha hHNF (formToIdeal f) hIf + y • hnfBeta hHNF (formToIdeal f) hIf := by
        intro X Y
        have hmem : X • (⟨f.val.1, 0⟩ : QuadInt k)
            + Y • (⟨(f.val.2.1 - 1) / 2, 1⟩ : QuadInt k) ∈ formToIdeal f :=
          (hFormMem f _).mpr ⟨X, Y, by apply QuadInt.ext <;> simp <;> ring⟩
        obtain ⟨x, y, hxy⟩ := (hnf_mem hHNF (formToIdeal f) hIf _).mp hmem
        exact ⟨x, y, hxy⟩
      exact proper_of_same_lattice
        (hnfAlpha hHNF (formToIdeal f) hIf) (hnfBeta hHNF (formToIdeal f) hIf)
        (⟨f.val.1, 0⟩ : QuadInt k) (⟨(f.val.2.1 - 1) / 2, 1⟩ : QuadInt k)
        (hnfForm hAutoPrim hk hHNF (formToIdeal f) hIf) f
        hd1 hd2 hn1 hn2 h12 h21
  exact ⟨{ toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv }⟩

end ClassGroupEquiv

open Polynomial
open scoped NumberField

section Aux

variable (D : ℕ) (hsq : Squarefree D) (h3 : D % 4 = 3)
  [Fact (Irreducible (X ^ 2 + C (D : ℚ)))]

noncomputable abbrev QuadK : Type := AdjoinRoot (X ^ 2 + C (D : ℚ))

noncomputable abbrev QuadDelta : QuadK D := AdjoinRoot.root (X ^ 2 + C (D : ℚ))

theorem quadDelta_sq : QuadDelta D ^ 2 = -(D : QuadK D) := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + C (D : ℚ) : ℚ[X])
  rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  rw [eq_neg_iff_add_eq_zero]
  simpa [map_natCast] using h

noncomputable abbrev QuadOmega : QuadK D := (1 + QuadDelta D) / 2

theorem two_mul_quadOmega : (2 : QuadK D) * QuadOmega D = 1 + QuadDelta D := by
  rw [QuadOmega]; field_simp

theorem quadOmega_sq (k : ℤ) (hk : 4 * k = (D : ℤ) + 1) :
    QuadOmega D ^ 2 = QuadOmega D - (k : QuadK D) := by
  have hδ := quadDelta_sq D
  have h2ω := two_mul_quadOmega D
  have h4k : (4 : QuadK D) * (k : QuadK D) = (D : QuadK D) + 1 := by
    have h : ((4 * k : ℤ) : QuadK D) = (((D : ℤ) + 1 : ℤ) : QuadK D) := by rw [hk]
    push_cast at h ⊢
    exact h
  have key : (4 : QuadK D) * (QuadOmega D ^ 2 - QuadOmega D + (k : QuadK D)) = 0 := by
    have e1 : (4 : QuadK D) * QuadOmega D ^ 2 = (1 + QuadDelta D) ^ 2 := by
      rw [← h2ω]; ring
    have e2 : (4 : QuadK D) * QuadOmega D = 2 * (1 + QuadDelta D) := by
      rw [← h2ω]; ring
    linear_combination e1 - e2 + h4k + hδ
  have hzero : QuadOmega D ^ 2 - QuadOmega D + (k : QuadK D) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by norm_num)
    · exact h
  linear_combination hzero

theorem quadOmega_isIntegral (k : ℤ) (hk : 4 * k = (D : ℤ) + 1) :
    IsIntegral ℤ (QuadOmega D) := by
  refine ⟨X ^ 2 - X + C k, ?_, ?_⟩
  · monicity!
  · have h := quadOmega_sq D k hk
    simp only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
    have hg : (algebraMap ℤ (QuadK D)) k = (k : QuadK D) :=
      map_intCast (algebraMap ℤ (QuadK D)) k
    rw [hg]
    linear_combination h

noncomputable def quadHom (k : ℤ) (hk : 4 * k = (D : ℤ) + 1) :
    QuadInt k →+* 𝓞 (QuadK D) where
  toFun z :=
    ⟨(z.x : QuadK D) + (z.y : QuadK D) * QuadOmega D,
      IsIntegral.add (isIntegral_intCast z.x)
        (IsIntegral.mul (isIntegral_intCast z.y) (quadOmega_isIntegral D k hk))⟩
  map_one' := by
    apply Subtype.ext
    change ((1 : QuadInt k).x : QuadK D) + ((1 : QuadInt k).y : QuadK D) * QuadOmega D = 1
    simp
  map_mul' z w := by
    apply Subtype.ext
    change ((z * w).x : QuadK D) + ((z * w).y : QuadK D) * QuadOmega D =
      ((z.x : QuadK D) + (z.y : QuadK D) * QuadOmega D) *
      ((w.x : QuadK D) + (w.y : QuadK D) * QuadOmega D)
    simp only [QuadInt.mul_x, QuadInt.mul_y]
    push_cast
    linear_combination -(z.y : QuadK D) * (w.y : QuadK D) * quadOmega_sq D k hk
  map_zero' := by
    apply Subtype.ext
    change ((0 : QuadInt k).x : QuadK D) + ((0 : QuadInt k).y : QuadK D) * QuadOmega D = 0
    simp
  map_add' z w := by
    apply Subtype.ext
    change ((z + w).x : QuadK D) + ((z + w).y : QuadK D) * QuadOmega D =
      ((z.x : QuadK D) + (z.y : QuadK D) * QuadOmega D) +
      ((w.x : QuadK D) + (w.y : QuadK D) * QuadOmega D)
    simp only [QuadInt.add_x, QuadInt.add_y]
    push_cast
    ring

theorem exists_rat_coords (α : QuadK D) :
    ∃ r s : ℚ, α = algebraMap ℚ (QuadK D) r + algebraMap ℚ (QuadK D) s * QuadDelta D := by
  let P : ℚ[X] := X ^ 2 + C (D : ℚ)
  have hPm : P.Monic := Polynomial.monic_X_pow_add_C (D : ℚ) (by norm_num)
  have hPdeg : P.degree = 2 := by
    have h1 : (X ^ 2 : ℚ[X]).degree = 2 := Polynomial.degree_X_pow 2
    have h2 : (C (D : ℚ) : ℚ[X]).degree < (X ^ 2 : ℚ[X]).degree := by
      rw [h1]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
    rw [Polynomial.degree_add_eq_left_of_degree_lt h2, h1]
  induction α using AdjoinRoot.induction_on with
  | ih p =>
    let q : ℚ[X] := p %ₘ P
    have hqlt : q.degree < 2 := by
      rw [← hPdeg]
      exact Polynomial.degree_modByMonic_lt p hPm
    have hqeq : q = C (q.coeff 0) + C (q.coeff 1) * X := by
      ext i
      rcases i with _ | _ | i
      · simp
      · simp
      · have hci : q.coeff (i + 2) = 0 := by
          apply Polynomial.coeff_eq_zero_of_degree_lt
          exact lt_of_lt_of_le hqlt (by norm_cast; omega)
        rw [hci]
        simp
    have hmk : AdjoinRoot.mk P p = AdjoinRoot.mk P q := by
      have hdiv := Polynomial.modByMonic_add_div p P
      have h1 := congrArg (AdjoinRoot.mk P) hdiv
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero] at h1
      exact h1.symm
    refine ⟨q.coeff 0, q.coeff 1, ?_⟩
    change AdjoinRoot.mk P p = AdjoinRoot.of P (q.coeff 0) + AdjoinRoot.of P (q.coeff 1) * AdjoinRoot.root P
    rw [hmk]
    conv_lhs => rw [hqeq]
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

theorem rat_coords_inj (hD : 0 < D) {r s : ℚ}
    (h : algebraMap ℚ (QuadK D) r + algebraMap ℚ (QuadK D) s * QuadDelta D = 0) :
    r = 0 ∧ s = 0 := by
  have hs : s = 0 := by
    by_contra hs0
    have hδ : QuadDelta D = algebraMap ℚ (QuadK D) (-r / s) := by
      have hsK : algebraMap ℚ (QuadK D) s ≠ 0 := by
        intro h0
        exact hs0 ((algebraMap ℚ (QuadK D)).injective (by rwa [map_zero]))
      have h1 : algebraMap ℚ (QuadK D) s * QuadDelta D = algebraMap ℚ (QuadK D) (-r) := by
        rw [map_neg]
        linear_combination h
      have h2 : algebraMap ℚ (QuadK D) s * algebraMap ℚ (QuadK D) (-r / s) =
          algebraMap ℚ (QuadK D) (-r) := by
        rw [← map_mul, mul_div_cancel₀ (-r) hs0]
      exact mul_left_cancel₀ hsK (h1.trans h2.symm)
    have hsqK : algebraMap ℚ (QuadK D) ((-r / s) ^ 2) = algebraMap ℚ (QuadK D) (-(D : ℚ)) := by
      simp only [map_pow, ← hδ, quadDelta_sq D, map_neg, map_natCast]
    have hsqQ : (-r / s) ^ 2 = -(D : ℚ) := (algebraMap ℚ (QuadK D)).injective hsqK
    have hDpos : (0 : ℚ) < (D : ℚ) := Nat.cast_pos.mpr hD
    nlinarith [sq_nonneg (-r / s), hsqQ, hDpos]
  subst hs
  simp only [map_zero, zero_mul, add_zero] at h
  have hr : r = 0 := (algebraMap ℚ (QuadK D)).injective (by rwa [map_zero])
  exact ⟨hr, rfl⟩

noncomputable def quadConj : QuadK D →+* QuadK D :=
  AdjoinRoot.lift (algebraMap ℚ (QuadK D)) (-QuadDelta D) (by
    simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_C, neg_sq, quadDelta_sq]
    simp [map_natCast])

theorem quadConj_algebraMap (r : ℚ) :
    quadConj D (algebraMap ℚ (QuadK D) r) = algebraMap ℚ (QuadK D) r :=
  AdjoinRoot.lift_of _

theorem quadConj_delta : quadConj D (QuadDelta D) = -QuadDelta D :=
  AdjoinRoot.lift_root _

theorem quadConj_isIntegral {x : QuadK D} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (quadConj D x) := by
  obtain ⟨p, hp, hev⟩ := hx
  refine ⟨p, hp, ?_⟩
  have h1 := congrArg (quadConj D) hev
  rw [map_zero, Polynomial.hom_eval₂] at h1
  have hcomp : (quadConj D).comp (algebraMap ℤ (QuadK D)) = algebraMap ℤ (QuadK D) :=
    RingHom.ext_int _ _
  rwa [hcomp] at h1

theorem rat_of_isIntegral_quadK {q : ℚ} (hq : IsIntegral ℤ (algebraMap ℚ (QuadK D) q)) :
    ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨p, hp, hev⟩ := hq
  have hqint : IsIntegral ℤ q := by
    refine ⟨p, hp, ?_⟩
    apply (algebraMap ℚ (QuadK D)).injective
    rw [map_zero, Polynomial.hom_eval₂]
    have hcomp : (algebraMap ℚ (QuadK D)).comp (algebraMap ℤ ℚ) = algebraMap ℤ (QuadK D) :=
      RingHom.ext_int _ _
    rwa [hcomp]
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hqint
  exact ⟨z, hz⟩

end Aux

noncomputable def quadIntEquivRingOfIntegers (D : ℕ) (hsq : Squarefree D) (h3 : D % 4 = 3)
    [Fact (Irreducible (X ^ 2 + C (D : ℚ)))] :
    QuadInt (((D + 1) / 4 : ℕ) : ℤ) ≃+* 𝓞 (AdjoinRoot (X ^ 2 + C (D : ℚ))) := by
  have hD : 0 < D := by omega
  let k : ℤ := (((D + 1) / 4 : ℕ) : ℤ)
  have hk : 4 * k = (D : ℤ) + 1 := by omega
  refine RingEquiv.ofBijective (quadHom D k hk) ⟨?_, ?_⟩
  · -- Injectivity
    intro z w hzw
    have hval := congrArg Subtype.val hzw
    change (z.x : QuadK D) + (z.y : QuadK D) * QuadOmega D =
      (w.x : QuadK D) + (w.y : QuadK D) * QuadOmega D at hval
    have h2 : algebraMap ℚ (QuadK D) (2 * (z.x - w.x : ℚ) + (z.y - w.y : ℚ)) +
        algebraMap ℚ (QuadK D) (z.y - w.y : ℚ) * QuadDelta D = 0 := by
      have hω := two_mul_quadOmega D
      have hmul : (2 : QuadK D) * (((z.x : QuadK D) + (z.y : QuadK D) * QuadOmega D) -
          ((w.x : QuadK D) + (w.y : QuadK D) * QuadOmega D)) = 0 := by
        rw [hval, sub_self, mul_zero]
      simp only [map_add, map_sub, map_mul, map_intCast, map_ofNat]
      linear_combination hmul - ((z.y : QuadK D) - (w.y : QuadK D)) * hω
    obtain ⟨h1, h2'⟩ := rat_coords_inj D hD h2
    have hy : z.y = w.y := by exact_mod_cast sub_eq_zero.mp h2'
    have hx : z.x = w.x := by
      have : (z.x : ℚ) = (w.x : ℚ) := by linarith [h1, h2']
      exact_mod_cast this
    apply QuadInt.ext <;> assumption
  · -- Surjectivity
    rintro ⟨α, hα⟩
    obtain ⟨r, s, hrseq⟩ := exists_rat_coords D α
    have hσα : IsIntegral ℤ (quadConj D α) := quadConj_isIntegral D hα
    have hσα_eq : quadConj D α = algebraMap ℚ (QuadK D) r - algebraMap ℚ (QuadK D) s * QuadDelta D := by
      rw [hrseq, map_add, map_mul, quadConj_algebraMap, quadConj_algebraMap, quadConj_delta]
      ring
    have htr_int : IsIntegral ℤ (algebraMap ℚ (QuadK D) (2 * r)) := by
      have hsum : α + quadConj D α = algebraMap ℚ (QuadK D) (2 * r) := by
        rw [hσα_eq, hrseq, map_mul, map_ofNat]
        ring
      rw [← hsum]
      exact hα.add hσα
    have hnm_int : IsIntegral ℤ (algebraMap ℚ (QuadK D) (r ^ 2 + (D : ℚ) * s ^ 2)) := by
      have hprod : α * quadConj D α = algebraMap ℚ (QuadK D) (r ^ 2 + (D : ℚ) * s ^ 2) := by
        rw [hσα_eq, hrseq]
        simp only [map_add, map_mul, map_pow, map_natCast]
        linear_combination -(algebraMap ℚ (QuadK D) s) ^ 2 * quadDelta_sq D
      rw [← hprod]
      exact hα.mul hσα
    obtain ⟨t, ht⟩ := rat_of_isIntegral_quadK D htr_int
    obtain ⟨n, hn⟩ := rat_of_isIntegral_quadK D hnm_int
    let q : ℚ := 2 * s
    have hDq2 : (D : ℚ) * q ^ 2 = 4 * (n : ℚ) - (t : ℚ) ^ 2 := by
      rw [ht, hn]
      change (D : ℚ) * (2 * s) ^ 2 = 4 * (r ^ 2 + (D : ℚ) * s ^ 2) - (2 * r) ^ 2
      ring
    have hqden_eq : (q.den : ℤ) ^ 2 * (4 * n - t ^ 2) = (D : ℤ) * q.num ^ 2 := by
      have hden0 : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
      have hqrat : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden0).mp (Rat.num_div_den q)
      have hQ : ((q.den : ℤ) ^ 2 * (4 * n - t ^ 2) : ℚ) = ((D : ℤ) * q.num ^ 2 : ℚ) := by
        push_cast
        rw [← hDq2, hqrat]
        ring
      exact_mod_cast hQ
    have hden_sq_dvd : q.den * q.den ∣ D := by
      have h1 : (q.den : ℤ) ^ 2 ∣ (D : ℤ) * q.num ^ 2 := ⟨4 * n - t ^ 2, hqden_eq.symm⟩
      have h2 : q.den * q.den ∣ D * q.num.natAbs ^ 2 := by
        rw [← Int.natCast_dvd_natCast]
        push_cast
        rw [sq_abs]
        simpa [sq] using h1
      have hcop : Nat.Coprime (q.den * q.den) (q.num.natAbs ^ 2) := by
        have hc := q.reduced.symm
        simpa [sq] using hc.pow 2 2
      exact hcop.dvd_of_dvd_mul_right h2
    have hden1 : q.den = 1 := Nat.isUnit_iff.mp (hsq q.den hden_sq_dvd)
    let u : ℤ := q.num
    have hu : (u : ℚ) = 2 * s := by
      have hnd := Rat.num_div_den q
      rw [hden1] at hnd
      simpa [u, q] using hnd
    have h4n : t ^ 2 + (D : ℤ) * u ^ 2 = 4 * n := by
      have hQ : ((t ^ 2 + (D : ℤ) * u ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
        push_cast
        rw [ht, hu, hn]
        ring
      exact_mod_cast hQ
    have hpar : (t - u) % 2 = 0 := by
      have ht2 : t % 2 = 0 ∨ t % 2 = 1 := Int.emod_two_eq_zero_or_one t
      have hu2 : u % 2 = 0 ∨ u % 2 = 1 := Int.emod_two_eq_zero_or_one u
      rcases ht2 with ht0 | ht1 <;> rcases hu2 with hu0 | hu1
      · omega
      · exfalso
        obtain ⟨a, ha⟩ : ∃ a, t = 2 * a := ⟨t / 2, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, u = 2 * b + 1 := ⟨u / 2, by omega⟩
        rw [ha, hb] at h4n
        have hdiv4 : (4 : ℤ) ∣ (D : ℤ) :=
          ⟨n - a ^ 2 - (D : ℤ) * (b ^ 2 + b), by linarith⟩
        have hmod0 : (D : ℤ) % 4 = 0 := Int.emod_eq_zero_of_dvd hdiv4
        omega
      · exfalso
        obtain ⟨a, ha⟩ : ∃ a, t = 2 * a + 1 := ⟨t / 2, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, u = 2 * b := ⟨u / 2, by omega⟩
        rw [ha, hb] at h4n
        have hdiv4 : (4 : ℤ) ∣ (1 : ℤ) :=
          ⟨n - a ^ 2 - a - (D : ℤ) * b ^ 2, by linarith⟩
        have hmod0 : (1 : ℤ) % 4 = 0 := Int.emod_eq_zero_of_dvd hdiv4
        omega
      · omega
    let x : ℤ := (t - u) / 2
    have h2x : 2 * x = t - u := by omega
    refine ⟨⟨x, u⟩, ?_⟩
    apply Subtype.ext
    change (x : QuadK D) + (u : QuadK D) * QuadOmega D = α
    have h2eq : (2 : QuadK D) * ((x : QuadK D) + (u : QuadK D) * QuadOmega D) =
        (2 : QuadK D) * α := by
      have hω := two_mul_quadOmega D
      have htrK : (t : QuadK D) = algebraMap ℚ (QuadK D) (2 * r) := by
        rw [← ht]; simp
      have huK : (u : QuadK D) = algebraMap ℚ (QuadK D) (2 * s) := by
        rw [← hu]; simp
      have h2xK : (2 : QuadK D) * (x : QuadK D) = (t : QuadK D) - (u : QuadK D) := by
        exact_mod_cast h2x
      rw [hrseq]
      simp only [map_mul, map_ofNat] at htrK huK
      linear_combination h2xK + (u : QuadK D) * hω + htrK + huK * QuadDelta D
    exact mul_left_cancel₀ (by norm_num : (2 : QuadK D) ≠ 0) h2eq


section Glue

open Polynomial
open scoped NumberField

theorem isDedekindRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsDedekindRing R]
    (e : R ≃+* S) : IsDedekindRing S := by
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  have : Ring.DimensionLEOne S := Ring.DimensionLEOne.of_ringEquiv e.symm
  have : IsIntegrallyClosed S := IsIntegrallyClosed.of_equiv e
  refine (isDedekindRing_iff S (FractionRing S)).mpr
    ⟨inferInstance, inferInstance, fun {x} hx =>
      (IsIntegrallyClosed.isIntegral_iff (R := S) (K := FractionRing S)).mp hx⟩

theorem isDedekindDomain_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R]
    (e : R ≃+* S) : IsDedekindDomain S := by
  have : IsDedekindRing S := isDedekindRing_of_ringEquiv e
  have : IsDomain S := MulEquiv.isDomain R e.symm.toMulEquiv
  exact inferInstance

end Glue

end PartitionParityProof

theorem OMA.solution : OMA.R_PartitionParity_classNumber_eq_ncard_reducedForms_R1.H1 := by
  intro D inst hsq h3
  have hD : 0 < D := by omega
  let k : ℤ := (((D + 1) / 4 : ℕ) : ℤ)
  have hk : 4 * k - 1 = (D : ℤ) := by omega
  let e1 := PartitionParityProof.quadIntEquivRingOfIntegers D hsq h3
  have : IsDedekindDomain (PartitionParityProof.QuadInt k) :=
    PartitionParityProof.isDedekindDomain_of_ringEquiv e1.symm
  obtain ⟨e2⟩ := PartitionParityProof.classGroup_equiv_quot_proper_of_parts
    D hsq h3 k hk
    (fun _ _ _ hd => PartitionParityProof.QuadFormReduction.auto_primitive hsq hd)
    (fun I hI => PartitionParityProof.ideal_has_hnf hk hD I hI)
    (PartitionParityProof.formToIdeal h3 hk)
    (PartitionParityProof.formToIdeal_mem_iff h3 hk)
    (PartitionParityProof.formToIdeal_ne_bot h3 hk)
    (fun _ _ hfg => PartitionParityProof.formToIdeal_proper_equiv h3 hk hfg)
  change NumberField.classNumber (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) =
    Nat.card (Quot (@PartitionParityProof.QuadFormReduction.proper D))
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (ClassGroup.mulEquiv e1).toEquiv).symm.trans (Nat.card_congr e2)
