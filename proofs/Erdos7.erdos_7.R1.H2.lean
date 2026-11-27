import OMAReductions.R_Erdos7_erdos_7_R1
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-! A conditional construction for the odd covering systems problem. -/

namespace OddLift

/-- An integer either has a zero prefix of length n in base p, or has a first
nonzero digit somewhere in that prefix. The statement works for negative integers. -/
theorem first_digit (p : ℕ) (hp : 0 < p) (z : ℤ) (n : ℕ) :
    (p : ℤ)^n ∣ z ∨ ∃ j < n, ∃ r : Fin p, 0 < r.val ∧
      (p : ℤ)^j * (r.val : ℤ) ≡ z [ZMOD (p : ℤ)^(j+1)] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases ih with ⟨q, hq⟩ | ⟨j, hj, r, hr, hz⟩
    · by_cases hd : (p : ℤ) ∣ q
      · obtain ⟨k, hk⟩ := hd
        exact Or.inl ⟨k, by rw [hq, hk, pow_succ, mul_assoc]⟩
      · have hpos : (0 : ℤ) < p := by exact_mod_cast hp
        have h0 := Int.emod_nonneg q (ne_of_gt hpos)
        have hlt := Int.emod_lt_of_pos q hpos
        have hn := mt Int.dvd_iff_emod_eq_zero.mpr hd
        let r : Fin p := ⟨(q % p).toNat, by omega⟩
        have hr : (r.val : ℤ) = q % p := Int.toNat_of_nonneg h0
        refine Or.inr ⟨n, Nat.lt_succ_self _, r, ?_, ?_⟩
        · change 0 < (q % p).toNat
          omega
        · rw [hr, hq, pow_succ]
          exact (Int.mod_modEq q p).mul_left'
    · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, r, hr, hz⟩

/-- Natural-number CRT representatives give integer congruences, even when the
integer to be covered is negative. -/
theorem crt_spot (n d s u : ℕ) (cop : n.Coprime d) (z : ℤ)
    (h₁ : (s : ℤ) ≡ z [ZMOD (n : ℤ)]) (h₂ : (u : ℤ) ≡ z [ZMOD (d : ℤ)]) :
    ((n * d : ℕ) : ℤ) ∣ z - ((Nat.chineseRemainder cop s u).val : ℤ) := by
  let a := Nat.chineseRemainder cop s u
  have h := a.property
  rw [Nat.cast_mul, ← Int.modEq_iff_dvd]
  apply (Int.modEq_and_modEq_iff_modEq_mul (by simpa using cop)).mp
  exact ⟨(Int.natCast_modEq_iff.mpr h.1).trans h₁,
    (Int.natCast_modEq_iff.mpr h.2).trans h₂⟩

/-- The exponent is recovered uniquely because the auxiliary multiplier is
coprime to p. -/
theorem exponent_of_class (p d j : ℕ) (prime : p.Prime) (hd : 0 < d)
    (cop : p.Coprime d) : (p^j * d).factorization p = j := by
  have hn : ¬p ∣ d := prime.coprime_iff_not_dvd.mp cop
  rw [Nat.factorization_mul (pow_ne_zero _ prime.ne_zero) hd.ne',
    Finsupp.add_apply, prime.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hn]
  simp

/- The inner option distinguishes the zero-digit repair from the tagged
hole/digit repairs. The outer option reserves multiplier 1 for the free digit. -/
private abbrev Slot (p h : ℕ) := Option (Fin (p-2) × Fin h)
private abbrev Label (p h : ℕ) := Option (Slot p h)

private def multiplier {M p h : ℕ} (E : Slot p h ↪ ↥(M.divisors.erase 1)) :
    Label p h → ℕ
  | none => 1
  | some s => (E s).val

private theorem multiplier_dvd {M p h : ℕ} (E : Slot p h ↪ ↥(M.divisors.erase 1))
    (l : Label p h) : multiplier E l ∣ M := by
  cases l with
  | none => exact one_dvd _
  | some s => exact (Nat.mem_divisors.mp (Finset.mem_of_mem_erase (E s).property)).1

private theorem multiplier_injective {M p h : ℕ} (E : Slot p h ↪ ↥(M.divisors.erase 1)) :
    Function.Injective (multiplier E) := by
  intro l r eq
  cases l with
  | none =>
    cases r with
    | none => rfl
    | some t => exact False.elim ((Finset.mem_erase.mp (E t).property).1 eq.symm)
  | some s =>
    cases r with
    | none => exact False.elim ((Finset.mem_erase.mp (E s).property).1 eq)
    | some t => exact congrArg some (E.injective (Subtype.ext eq))

private def digit {p h : ℕ} : Label p h → ℕ
  | none => p-1
  | some none => 0
  | some (some (d, _)) => d.val+1

private def target {p h : ℕ} (u : Fin h → ℕ) (j : Fin h) : Label p h → ℕ
  | none => 0
  | some none => u j
  | some (some (_, i)) => u i

/-- Cover the full preimage of any h residues modulo M by distinct odd
multiples of p, provided the proper-divisor budget buys (p−2)h+1 mixed
classes at each level. The construction uses h levels. -/
theorem repair (M p h : ℕ) (u : Fin h → ℕ) (prime : p.Prime) (hp : 3 ≤ p)
    (oddM : Odd M) (cop : p.Coprime M) (budget : (p-2)*h < (M.divisors.erase 1).card) :
    ∃ S : Finset ℕ, ∃ a : ℕ → ℤ, (∀ d ∈ S, 1 < d ∧ Odd d ∧ p ∣ d) ∧
      ∀ z : ℤ, (∃ i, (M : ℤ) ∣ z - (u i : ℤ)) → ∃ d ∈ S, (d : ℤ) ∣ z - a d := by
  classical
  have capacity : Fintype.card (Slot p h) ≤ Fintype.card ↥(M.divisors.erase 1) := by
    simpa [Slot, Fintype.card_option, Fintype.card_prod] using budget
  obtain ⟨E⟩ := Function.Embedding.nonempty_of_card_le capacity
  have mpos : 0 < M := by obtain ⟨v, hv⟩ := oddM; omega
  have multpos (l : Label p h) := Nat.pos_of_dvd_of_pos (multiplier_dvd E l) mpos
  have multcop (l : Label p h) := cop.of_dvd_right (multiplier_dvd E l)
  let modulus (L : Fin h × Label p h) := p^(L.1.val+1) * multiplier E L.2
  have inject : Function.Injective modulus := by
    rintro ⟨i, s⟩ ⟨j, t⟩ he
    change p^(i.val+1) * multiplier E s = p^(j.val+1) * multiplier E t at he
    have hj := congrArg (fun d : ℕ => d.factorization p) he
    simp only [exponent_of_class _ _ _ prime (multpos _) (multcop _)] at hj
    have hij : i = j := Fin.ext (by omega)
    subst j
    have hs := Nat.eq_of_mul_eq_mul_left (pow_pos prime.pos (i.val+1)) he
    exact congrArg (Prod.mk i) (multiplier_injective E hs)
  let residue (L : Fin h × Label p h) : ℤ :=
    (Nat.chineseRemainder ((multcop L.2).pow_left (L.1.val+1))
      (p^L.1.val * digit L.2) (target u L.1 L.2)).val
  let a := Function.extend modulus residue (fun _ => 0)
  refine ⟨Finset.univ.image modulus, a, ?_, ?_⟩
  · intro m hm
    obtain ⟨⟨j, l⟩, _, rfl⟩ := Finset.mem_image.mp hm
    change 1 < p^(j.val+1) * multiplier E l ∧ Odd (p^(j.val+1) * multiplier E l) ∧ _
    have pd : p ∣ p^(j.val+1) * multiplier E l :=
      dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero _)) _
    have bound := Nat.le_of_dvd (Nat.mul_pos (pow_pos prime.pos _) (multpos l)) pd
    exact ⟨by omega, (prime.odd_of_ne_two (by omega)).pow.mul
      (oddM.of_dvd_nat (multiplier_dvd E l)), pd⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hz
    have hit (j : Fin h) (l : Label p h)
        (h₁ : (p : ℤ)^j.val * (digit l : ℤ) ≡ z [ZMOD (p : ℤ)^(j.val+1)])
        (h₂ : (target u j l : ℤ) ≡ z [ZMOD (multiplier E l : ℤ)]) :
        ∃ d ∈ Finset.univ.image modulus, (d : ℤ) ∣ z - a d := by
      refine ⟨modulus (j,l), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      rw [show a (modulus (j,l)) = residue (j,l) from inject.extend_apply _ _ _]
      exact crt_spot _ _ _ _ ((multcop l).pow_left (j.val+1)) z (by push_cast; exact h₁) h₂
    have base (l : Label p h) : (u i : ℤ) ≡ z [ZMOD (multiplier E l : ℤ)] :=
      (Int.modEq_iff_dvd.mpr hi).of_dvd (Int.natCast_dvd_natCast.mpr (multiplier_dvd E l))
    rcases first_digit p prime.pos z (i.val+1) with allzero | ⟨j, hj, r, hr, first⟩
    · apply hit i (some none)
      · simpa [digit] using allzero.modEq_zero_int.symm
      · exact base _
    · let t : Fin h := ⟨j, by omega⟩
      by_cases last : r.val = p-1
      · apply hit t none
        · simpa [t, digit, last] using first
        · exact Int.modEq_one
      · let k : Fin (p-2) := ⟨r.val-1, by omega⟩
        have hk : k.val + 1 = r.val := by dsimp [k]; omega
        apply hit t (some (some (k,i)))
        · simpa only [digit, hk, t] using first
        · exact base _

end OddLift

/-- Repair each exceptional residue by distinct odd multiples of the new prime. -/
theorem OMA.solution : OMA.R_Erdos7_erdos_7_R1.H2 := OddLift.repair
