import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

/-!
Saye's ternary suffix tree has period twice a power of three. At the next
digit, the three possible lifts realize three different digits. We isolate
a sufficient growth condition for the least exponents with long zero-free
suffixes and distinguish genuine digits from leading padding.
-/
namespace OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1

/-- The leading unit in the period increment is one modulo three. -/
theorem periodLift (s : ℕ) : ∃ c : ℕ,
    2^(2*3^s) = 1 + 3^(s+1)*(1+3*c) := by
  induction s with
  | zero => exact ⟨0,by decide⟩
  | succ s ih =>
    obtain ⟨c,h⟩ := ih
    let t := 1+3*c
    refine ⟨c + 3^s*t^2 + (3^s)^2*t^3,?_⟩
    rw [show 2*3^(s+1) = (2*3^s)*3 by ring,pow_mul,h]
    simp only [pow_succ 3]
    dsimp [t]
    ring

/-- Adding a period advances the next digit by a nonzero step mod three. -/
theorem nextDigit (s k : ℕ) :
    (2^(k+2*3^s) / 3^(s+1))%3 = (2^k / 3^(s+1) + 2^k)%3 := by
  obtain ⟨c,h⟩ := periodLift s
  rw [pow_add,h]
  rw [show 2^k*(1+3^(s+1)*(1+3*c)) =
    2^k + (2^k*(1+3*c))*3^(s+1) by ring]
  rw [Nat.add_mul_div_right _ _ (by positivity)]
  simp [Nat.add_mod,Nat.mul_mod]

/-- At each node exactly two of the three children avoid zero. -/
theorem zeroLift (s k : ℕ) : ∃! j : Fin 3,
    (2^(k + j.val*(2*3^s)) / 3^(s+1)) % 3 = 0 := by
  let P := 2*3^s
  let A := 2^k / 3^(s+1)
  have inc : 2^(k+P) % 3 = 2^k % 3 := by
    obtain ⟨c,h⟩ := periodLift s
    simp [P,pow_add,h,pow_succ,Nat.mul_mod,Nat.add_mod]
  have first := nextDigit s k
  change 2^(k+P)/3^(s+1)%3 = (A+2^k)%3 at first
  have second := nextDigit s (k+P)
  change 2^(k+P+P)/3^(s+1)%3 = (2^(k+P)/3^(s+1)+2^(k+P))%3 at second
  rw [Nat.add_mod,first,inc] at second
  have nz : 2^k%3 ≠ 0 := by
    intro h
    exact (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h))
  have table : ∀ a b : Fin 3, b.val ≠ 0 →
      ∃! j : Fin 3, (a.val+j.val*b.val)%3 = 0 := by unfold ExistsUnique; decide
  obtain ⟨j,hj,unique⟩ := table
    ⟨A%3,Nat.mod_lt _ (by decide)⟩ ⟨2^k%3,Nat.mod_lt _ (by decide)⟩ nz
  have shift (u : Fin 3) :
      (2^(k+u.val*(2*3^s))/3^(s+1))%3 = (A%3+u.val*(2^k%3))%3 := by
    fin_cases u
    · simp [A]
    · simpa [P,Nat.add_mod] using first
    · change 2^(k+2*(2*3^s))/3^(s+1)%3 = (A%3+2*(2^k%3))%3
      rw [show k+2*(2*3^s)=k+P+P by dsimp [P]; omega,second]
      rw [Nat.add_mod A (2^k)]
      have assoc3 : ∀ a b : Fin 3, ((a.val+b.val)%3+b.val)%3 = (a.val+2*b.val)%3 := by decide
      exact assoc3 ⟨A%3,Nat.mod_lt _ (by decide)⟩ ⟨2^k%3,Nat.mod_lt _ (by decide)⟩
  refine ⟨j,(shift j).trans hj,?_⟩
  intro u hu
  exact unique u (by change (A%3+u.val*(2^k%3))%3=0; rwa [←shift])


private theorem digitPeriodic (r k i : ℕ) (hi : i < r) :
    (2^(k % (2*3^(r-1))) / 3^i)%3 = (2^k / 3^i)%3 := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.add_one_sub_one]
  let P := 2*3^s
  obtain ⟨c,h⟩ := periodLift s
  have per : 2^P ≡ 1 [MOD 3^(s+1)] := by simp [P,h,Nat.ModEq]
  have full : 2^(k%P) ≡ 2^k [MOD 3^(s+1)] := by
    calc 2^(k%P) = 2^(k%P)*1^(k/P) := by simp
      _ ≡ 2^(k%P)*(2^P)^(k/P) [MOD 3^(s+1)] := (per.symm.pow _).mul_left _
      _ = 2^k := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
  have dm := full.of_dvd (pow_dvd_pow 3 (by omega : i+1 ≤ s+1))
  change 2^(k%P) % 3^(i+1) = 2^k % 3^(i+1) at dm
  rw [pow_succ] at dm
  have dd := congrArg (fun z => z/3^i) dm
  change 2^(k%P) % (3^i*3) / 3^i = 2^k % (3^i*3) / 3^i at dd
  simpa only [Nat.mod_mul_right_div_self] using dd

private theorem actualDigit (n i : ℕ) (h : 3^i ≤ n) :
    n / 3^i % 3 ∈ Nat.digits 3 n := by
  induction i generalizing n with
  | zero =>
    have hn : n ≠ 0 := by simp only [pow_zero] at h; omega
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hn]
    simp
  | succ i ih =>
    have hi : 3^i ≤ n/3 := (Nat.le_div_iff_mul_le (by decide)).mpr (by simpa [pow_succ] using h)
    have hn : n ≠ 0 := by
      have hp : 0 < 3^(i+1) := by positivity
      omega
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hn]
    apply List.mem_cons_of_mem
    simpa [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using ih (n/3) hi


/-- A finite certificate for all exponents below 4096, expressed in base 64
to keep the kernel evaluation shallow. Digits are padded on the left by zero. -/
def H1 : Prop := ∀ a b : Fin 64, ∃ i : Fin 32,
    (2^(64*a.val+b.val)/3^i.val)%3 = 0

/-- A sufficient lower-growth condition on Saye's first-survivor statistic.
Only canonical first-period exponents with no surviving half-size predecessor
need examination, and only the new half of the digit window needs a zero. -/
def H2 : Prop := ∀ j k : ℕ, 5 ≤ j → 4096 ≤ k →
    let r := 2^j
    k < 2*3^(r-1) →
    (∀ i < r, (2^k / 3^i)%3 ≠ 0) →
    (∀ l, 2*l ≤ k → ∃ i < r, (2^l / 3^i)%3 = 0) →
    ∃ i, r ≤ i ∧ i < 2*r ∧ (2^k / 3^i)%3 = 0


set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
theorem finiteSeed : H1 := by unfold H1; decide +kernel

private theorem seedFails (seed : H1) {k : ℕ} (hk : k < 4096) :
    ∃ i < 32, (2^k / 3^i)%3 = 0 := by
  have q : k/64 < 64 := by omega
  obtain ⟨i,hi⟩ := seed ⟨k/64,q⟩ ⟨k%64,Nat.mod_lt _ (by decide)⟩
  refine ⟨i.val,i.isLt,?_⟩
  simpa only [show 64*(k/64)+k%64=k by omega] using hi

/-- Every long survivor has a shorter survivor at no more than half its exponent. -/
theorem predecessor (seed : H1) (gap : H2) {j k : ℕ} (hj : 5 ≤ j)
    (good : ∀ i < 2*(2^j), (2^k / 3^i)%3 ≠ 0) :
    ∃ l, 2*l ≤ k ∧ ∀ i < 2^j, (2^l / 3^i)%3 ≠ 0 := by
  let r := 2^j
  have minR : 32 ≤ r := Nat.pow_le_pow_right (by decide : 0 < 2) hj
  have base : ∀ i < r, (2^k / 3^i)%3 ≠ 0 := by
    intro i hi
    exact good i (by change i < 2*r; omega)
  by_cases small : k < 4096
  · obtain ⟨i,hi,hz⟩ := seedFails seed small
    exact (base i (hi.trans_le minR) hz).elim
  let P := 2*3^(r-1)
  by_cases per : P ≤ k
  · have hp : 0 < P := by dsimp [P]; positivity
    have m := Nat.mod_lt k hp
    have q : 1 ≤ k/P := (Nat.le_div_iff_mul_le hp).mpr (by simpa using per)
    have p := Nat.mul_le_mul_left P q
    have sum := Nat.mod_add_div k P
    refine ⟨k%P,by omega,?_⟩
    intro i hi
    rw [show (2^(k%P)/3^i)%3 = (2^k/3^i)%3 from digitPeriodic r k i hi]
    exact base i hi
  by_contra! none
  obtain ⟨i,_,hi,hz⟩ := gap j k hj (by omega) (by exact lt_of_not_ge per) base none
  exact good i hi hz

theorem main : H1 → H2 → OMA.R_Erdos406_erdos_406_variants_one_two_R1.H2 := by
  intro seed gap k hk admissible
  have growth : ∀ j : ℕ, 5 ≤ j → ∀ b : ℕ,
      (∀ i < 2^j, (2^b/3^i)%3 ≠ 0) → 4*(2^j) ≤ b := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro b h
      by_contra! little
      obtain ⟨i,hi,hz⟩ := seedFails seed (k := b) (by norm_num at little; omega)
      exact h i (by exact hi) hz
    | succ j hj ih =>
      intro b h
      have h' : ∀ i < 2*(2^j), (2^b/3^i)%3 ≠ 0 := by simpa [pow_succ,Nat.mul_comm] using h
      obtain ⟨l,half,short⟩ := predecessor seed gap hj h'
      have bound := ih l short
      rw [pow_succ]
      omega
  let e := Nat.log 2 k
  have six : 6 ≤ e := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
  let j := e-1
  have ej : e=j+1 := by dsimp [j]; omega
  have middle : 2*(2^j) ≤ k := by
    have v := Nat.pow_log_le_self 2 (by omega : k ≠ 0)
    change 2^e ≤ k at v
    simpa [ej,pow_succ,Nat.mul_comm] using v
  have top : k < 4*(2^j) := by
    have v := Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
    change k < 2^(e+1) at v
    rw [ej,pow_succ,pow_succ] at v
    omega
  have long (i : ℕ) (hi : i < 2^j) : (2^k/3^i)%3 ≠ 0 := by
    have hp : 3^i ≤ 2^k := calc
      3^i ≤ 4^i := Nat.pow_le_pow_left (by decide) _
      _ = 2^(2*i) := by rw [pow_mul]; rfl
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    have mem := admissible (actualDigit (2^k) i hp)
    intro hz
    simp [hz] at mem
  have := growth j (by dsimp [j]; omega) k long
  omega

end OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1
