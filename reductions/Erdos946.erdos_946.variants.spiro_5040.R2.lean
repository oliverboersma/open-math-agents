import FormalConjectures.ErdosProblems.«946»
import Mathlib

/-!
Two forms in an admissible triplet take values that are products of two
distinct odd primes, by the basic theorem of Goldston, Graham, Pintz and
Yildirim. The specialization below is also supplied by the public Lean
theorem Erdos964.admissible_semiprime_triples in plby/lean-proofs.
Three equally spaced translates suffice for every positive shift divisible
by twelve. Their spacing absorbs the whole shift, or half of it.
-/
namespace OMA.R_Erdos946_erdos_946_variants_spiro_5040_R2

open scoped ArithmeticFunction.sigma

/-- The common-slope-one, prime-factor cutoff two specialization of the
published admissible triplet theorem. -/
def H1 : Prop := ∀ b : Fin 3 → ℕ, (∀ i, 0 < b i) → Function.Injective b →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ t+b i) →
    ∃ i j : Fin 3, i<j ∧
      {t : ℕ | (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 2 < p ∧ 2 < q ∧ t+b i = p*q) ∧
               (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 2 < p ∧ 2 < q ∧ t+b j = p*q)}.Infinite

/-- For this family two explicit translations suffice to exclude any given
prime divisor from all three forms. -/
def H2 : Prop := ∀ h : ℕ, 0 < h → 6 ∣ h → ∀ p : ℕ, p.Prime →
    ∃ t : ℕ, (t=0 ∨ t=h-1) ∧ ∀ i : Fin 3, ¬p ∣ t+(1+h*i.val)

/-- Reading E2 as its defining set, this premise is the statement of
Erdos964.admissible_semiprime_triples in the published Lean development. -/
theorem ofPublishedTriplet (g : ∀ A B : Fin 3 → ℕ,
    (∀ i, 0 < A i) → (∀ i, 0 < B i) →
    (∀ i j, i ≠ j → A i * B j ≠ A j * B i) →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬p ∣ A i*t+B i) →
    ∀ C : ℕ, ∃ i j : Fin 3, i<j ∧
      {t : ℕ | (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ C<p ∧ C<q ∧ A i*t+B i=p*q) ∧
               (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ C<p ∧ C<q ∧ A j*t+B j=p*q)}.Infinite) : H1 := by
  intro b hb distinct localCondition
  have cross (i j : Fin 3) (hij : i≠j) : 1*b j ≠ 1*b i := by
    simpa only [one_mul] using (show b j ≠ b i from fun eqn => hij (distinct eqn.symm))
  simpa only [one_mul] using g (fun _ => 1) b (by simp) hb cross
    (by simpa only [one_mul] using localCondition) 2

theorem localWitnesses : H2 := by
  intro h hh six p pp
  by_cases ph : p ∣ h
  · refine ⟨0,Or.inl rfl,?_⟩
    intro i bad
    have mul : p ∣ h*i.val := dvd_mul_of_dvd_left ph _
    exact pp.not_dvd_one ((Nat.dvd_add_iff_left mul).mpr (by simpa using bad))
  · have p4 : 3 < p := by
      have p2 := pp.two_le
      by_contra! small
      interval_cases p <;> exact ph ((by decide : _ ∣ 6).trans six)
    refine ⟨h-1,Or.inr rfl,?_⟩
    intro i bad
    have eqn : h-1+(1+h*i.val) = h*(1+i.val) := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [eqn] at bad
    have dvd := (pp.dvd_mul.mp bad).resolve_left ph
    have low := Nat.le_of_dvd (by omega : 0 < 1+i.val) dvd
    omega

/-- An odd product of distinct primes has four divisors, and doubling it
adds exactly one independent prime factor. -/
theorem semiprimeCounts {x : ℕ}
    (hx : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ 2<p ∧ 2<q ∧ x=p*q) :
    σ 0 x = 4 ∧ σ 0 (2*x) = 8 := by
  obtain ⟨p,q,hp,hq,diff,p2,q2,rfl⟩ := hx
  have primeCount {r : ℕ} (hr : r.Prime) : σ 0 r = 2 := by
    simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) hr
  have pq := (Nat.coprime_primes hp hq).mpr diff
  have cp : Nat.Coprime 2 p := (Nat.coprime_primes (by decide) hp).mpr (by omega)
  have cq : Nat.Coprime 2 q := (Nat.coprime_primes (by decide) hq).mpr (by omega)
  have first : σ 0 (p*q)=4 := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pq,primeCount hp,primeCount hq]
    decide
  refine ⟨first,?_⟩
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (cp.mul_right cq),
    primeCount (by decide : Nat.Prime 2),first]
  decide

/-- For each allowed shift one fixed divisor count, either four or eight,
occurs at both ends of infinitely many pairs. -/
theorem fixedCount (sieve : H1) (admissible : H2) (h : ℕ) (hh : 0<h) (six : 6∣h) :
    ∃ d : ℕ, (d=4 ∨ d=8) ∧ {n : ℕ | σ 0 n=d ∧ σ 0 (n+2*h)=d}.Infinite := by
  let b (i : Fin 3) := 1+h*i.val
  have inj : Function.Injective b := by
    intro i j eqn
    apply Fin.ext
    have eqm : h*i.val=h*j.val := Nat.add_left_cancel eqn
    exact Nat.eq_of_mul_eq_mul_left hh eqm
  obtain ⟨i,j,lt,inf⟩ := sieve b (fun _ => by dsimp [b]; omega) inj (by
    intro p hp
    obtain ⟨t,_,ok⟩ := admissible h hh six p hp
    exact ⟨t,ok⟩)
  have step : j.val=i.val+1 ∨ j.val=i.val+2 := by
    change i.val<j.val at lt
    omega
  rcases step with near | far
  · refine ⟨8,Or.inr rfl,Set.infinite_iff_exists_gt.mpr ?_⟩
    intro T
    obtain ⟨t,ht,big⟩ := Set.infinite_iff_exists_gt.mp inf T
    have left := (semiprimeCounts ht.1).2
    have right := (semiprimeCounts ht.2).2
    have eqn : 2*(t+b i)+2*h=2*(t+b j) := by dsimp [b]; rw [near]; ring
    refine ⟨2*(t+b i),⟨left,eqn ▸ right⟩,by omega⟩
  · refine ⟨4,Or.inl rfl,Set.infinite_iff_exists_gt.mpr ?_⟩
    intro T
    obtain ⟨t,ht,big⟩ := Set.infinite_iff_exists_gt.mp inf T
    have left := (semiprimeCounts ht.1).1
    have right := (semiprimeCounts ht.2).1
    have eqn : t+b i+2*h=t+b j := by dsimp [b]; rw [far]; ring
    refine ⟨t+b i,⟨left,eqn ▸ right⟩,by omega⟩

theorem main : H1 → H2 → type_of% @Erdos946.erdos_946.variants.spiro_5040 := by
  intro h1 h2
  obtain ⟨d,_,inf⟩ := fixedCount h1 h2 2520 (by decide) (by decide)
  apply inf.mono
  intro n hn
  exact hn.1.trans hn.2.symm

end OMA.R_Erdos946_erdos_946_variants_spiro_5040_R2
