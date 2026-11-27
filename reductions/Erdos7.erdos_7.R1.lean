import FormalConjectures.ErdosProblems.«7»

/-!
# Repairing the holes of an incomplete odd covering system

Choose an odd period and one residue for each of its nontrivial divisors. The first
hypothesis asks for such a choice with a nonempty, sufficiently small uncovered set.
The second supplies congruence classes to cover that set. Divisibility by the fresh
prime keeps the moduli used in the two parts disjoint.
-/

namespace OMA.R_Erdos7_erdos_7_R1

open scoped Pointwise

/-- An incomplete cover with at most `h` exceptional residue classes modulo `M`. -/
def H1 : Prop :=
  ∃ (M p h : ℕ) (u : Fin h → ℕ) (r : ℕ → ℤ),
    p.Prime ∧ 3 ≤ p ∧ Odd M ∧ p.Coprime M ∧
    (p - 2) * h < (M.divisors.erase 1).card ∧
    (∃ z : ℤ, ∀ d ∈ M.divisors.erase 1, ¬ (d : ℤ) ∣ z - r d) ∧
    ∀ z : ℤ, (∃ d ∈ M.divisors.erase 1, (d : ℤ) ∣ z - r d) ∨
      ∃ i, (M : ℤ) ∣ z - (u i : ℤ)

/-- Any list of holes within the divisor budget can be covered by distinct odd
moduli divisible by the fresh prime. -/
def H2 : Prop :=
  ∀ (M p h : ℕ) (u : Fin h → ℕ), p.Prime → 3 ≤ p → Odd M → p.Coprime M →
    (p - 2) * h < (M.divisors.erase 1).card →
    ∃ S : Finset ℕ, ∃ a : ℕ → ℤ,
      (∀ d ∈ S, 1 < d ∧ Odd d ∧ p ∣ d) ∧
      ∀ z : ℤ, (∃ i, (M : ℤ) ∣ z - (u i : ℤ)) →
        ∃ d ∈ S, (d : ℤ) ∣ z - a d

/-- Congruence classes with distinct positive moduli define a strict ideal
covering system. Oddness of a modulus is exactly the required parity condition. -/
lemma integer_cover (S : Finset ℕ) (r : ℕ → ℤ)
    (valid : ∀ d ∈ S, 1 < d ∧ Odd d)
    (cover : ∀ z : ℤ, ∃ d ∈ S, (d : ℤ) ∣ z - r d) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i, ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  classical
  let I : S → Ideal ℤ := fun i => Ideal.span {(i.val : ℤ)}
  have gen (i : S) : (i.val : ℤ) ∈ I i := Ideal.subset_span (Set.mem_singleton _)
  have proper (i : S) : I i ≠ ⊤ := by
    intro heq
    have hmem : (1 : ℤ) ∈ I i := by rw [heq]; trivial
    have hInt : (i.val : ℤ) ∣ 1 := Ideal.mem_span_singleton.mp hmem
    have hNat : i.val ∣ 1 := by exact_mod_cast hInt
    exact (ne_of_gt (valid i i.property).1) (Nat.dvd_one.mp hNat)
  refine ⟨{
    ι := S
    residue := fun i => r i
    moduli := I
    unionCovers := ?_
    ne_bot := ?_
    ne_top := proper
    injective_moduli := ?_
  }, ?_⟩
  · apply Set.eq_univ_of_forall
    intro z
    obtain ⟨d, hd, hdiv⟩ := cover z
    refine Set.mem_iUnion.mpr ⟨⟨d, hd⟩, ?_⟩
    refine ⟨r d, rfl, z - r d, Ideal.mem_span_singleton.mpr hdiv, ?_⟩
    change r d + (z - r d) = z
    omega
  · intro i heq
    have hmem := gen i
    rw [heq] at hmem
    have hz : (i.val : ℤ) = 0 := hmem
    have hn : i.val = 0 := by exact_mod_cast hz
    have := (valid i i.property).1
    omega
  · intro i j heq
    apply Subtype.ext
    have hi : (i.val : ℤ) ∈ I j := heq ▸ gen i
    have hj : (j.val : ℤ) ∈ I i := heq.symm ▸ gen j
    have hij : (i.val : ℤ) ∣ (j.val : ℤ) := Ideal.mem_span_singleton.mp hj
    have hji : (j.val : ℤ) ∣ (i.val : ℤ) := Ideal.mem_span_singleton.mp hi
    exact Nat.dvd_antisymm (by exact_mod_cast hij) (by exact_mod_cast hji)
  · intro i
    refine ⟨?_, proper i⟩
    intro hle
    have hInt : (2 : ℤ) ∣ (i.val : ℤ) := Ideal.mem_span_singleton.mp (hle (gen i))
    have hNat : 2 ∣ i.val := by exact_mod_cast hInt
    obtain ⟨k, hk⟩ := (valid i i.property).2
    obtain ⟨l, hl⟩ := hNat
    omega

theorem main : H1 → H2 → type_of% @Erdos7.erdos_7 := by
  classical
  rintro ⟨M, p, h, u, r, hp, hp3, hodd, hcop, budget, _, seed⟩ repair
  obtain ⟨S, a, valid, cover⟩ := repair M p h u hp hp3 hodd hcop budget
  let D := M.divisors.erase 1
  have mem_dvd {d : ℕ} (hd : d ∈ D) : d ∣ M :=
    (Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2).1
  have disjoint {d : ℕ} (hd : d ∈ S) : d ∉ D := by
    intro hD
    exact (hp.coprime_iff_not_dvd.mp hcop) (dvd_trans (valid d hd).2.2 (mem_dvd hD))
  apply integer_cover (D ∪ S) (fun d => if d ∈ D then r d else a d)
  · intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · have hpos := Nat.pos_of_dvd_of_pos (mem_dvd hd) hodd.pos
      have hne := (Finset.mem_erase.mp hd).1
      exact ⟨by omega, hodd.of_dvd_nat (mem_dvd hd)⟩
    · exact ⟨(valid d hd).1, (valid d hd).2.1⟩
  · intro z
    rcases seed z with ⟨d, hd, hz⟩ | holes
    · change d ∈ D at hd
      exact ⟨d, Finset.mem_union_left _ hd, by simpa only [if_pos hd] using hz⟩
    · obtain ⟨d, hd, hz⟩ := cover z holes
      exact ⟨d, Finset.mem_union_right _ hd, by simpa only [if_neg (disjoint hd)] using hz⟩

end OMA.R_Erdos7_erdos_7_R1
