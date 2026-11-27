import OMAReductions.R_Erdos890_erdos_890_parts_a_R1

/-! Finite admissibility of the factorial family. At p ≤ k choose t = 1.
For p > k choose (k!)²t = 1, so the consecutive integers reduce to
1, ..., k. The Chinese remainder theorem combines the choices. -/
-- Credit: @marcusbuffett
open Finset

theorem OMA.solution : OMA.R_Erdos890_erdos_890_parts_a_R1.H2 := by
  classical
  intro k hk B
  let F := k.factorial
  let L := F^2
  let P := (range (B+1)).filter Nat.Prime
  let r (p : ℕ) : ZMod p := if p ≤ k then 1 else (L : ZMod p)⁻¹
  let b (p : ℕ) : ℕ := (r p).val
  obtain ⟨a,ha⟩ := Nat.chineseRemainderOfFinset b id P
    (fun p hp => (mem_filter.mp hp).2.ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).2 hpq)
  refine ⟨a,B.factorial,Nat.factorial_pos _,?_⟩
  intro j p hp hB
  letI : Fact p.Prime := ⟨hp⟩
  let t := a+B.factorial*j
  have hmod : (t : ZMod p) = r p := by
    have he := (ZMod.natCast_eq_natCast_iff a (b p) p).2 (ha p (mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩))
    have hd := (ZMod.natCast_eq_zero_iff _ p).2 (hp.dvd_factorial.mpr hB)
    simpa [t, hd,b] using he
  change ¬p ∣ t ∧ _
  by_cases hsmall : p ≤ k
  · have ht : (t : ZMod p) = 1 := hmod.trans (if_pos hsmall)
    refine ⟨fun h => one_ne_zero (ht.symm.trans ((ZMod.natCast_eq_zero_iff _ p).2 h)),?_⟩
    intro i hi hik hdiv
    have hif : i ∣ F := Nat.dvd_factorial hi hik.le
    have hco : F^2 / i = F * (F/i) := by rw [pow_two,Nat.mul_div_assoc _ hif]
    have hpd : p ∣ F^2/i := hco ▸ (hp.dvd_factorial.mpr hsmall).trans (dvd_mul_right _ _)
    have hz := (ZMod.natCast_eq_zero_iff _ p).2 hdiv
    change (((F^2/i)*t+1 : ℕ) : ZMod p) = 0 at hz
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,(ZMod.natCast_eq_zero_iff _ p).2 hpd,zero_mul,zero_add] at hz
    exact one_ne_zero hz
  · have hL : (L : ZMod p) ≠ 0 := fun h =>
      hsmall (hp.dvd_factorial.mp (hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff L p).1 h)))
    have ht : (t : ZMod p) = (L : ZMod p)⁻¹ := hmod.trans (if_neg hsmall)
    have hprod : (L : ZMod p)*(t : ZMod p) = 1 := by rw [ht,mul_inv_cancel₀ hL]
    refine ⟨fun h => (inv_ne_zero hL) (ht.symm.trans ((ZMod.natCast_eq_zero_iff _ p).2 h)),?_⟩
    intro i hi hik hdiv
    have hif : i ∣ L := (Nat.dvd_factorial hi hik.le).trans (dvd_pow_self _ (by decide : 2 ≠ 0))
    have he : i*((L/i)*t+1) = L*t+i := by rw [mul_add,←mul_assoc,Nat.mul_div_cancel' hif,mul_one]
    have hd : p ∣ L*t+i := he ▸ hdiv.trans (dvd_mul_left _ _)
    have hz := (ZMod.natCast_eq_zero_iff _ p).2 hd
    rw [Nat.cast_add,Nat.cast_mul,hprod] at hz
    have hd' : p ∣ i+1 := (ZMod.natCast_eq_zero_iff _ p).1 (by simpa [add_comm] using hz)
    have := Nat.le_of_dvd (Nat.succ_pos i) hd'
    omega
