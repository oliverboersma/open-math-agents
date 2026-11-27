import FormalConjectures.ErdosProblems.«7»

/-!
# Two-prime disjoint hole repair for odd covering systems

Split the uncovered residue classes of an incomplete odd divisor cover into two
families modulo an odd base `M`. Using two distinct odd primes `p` and `q`
coprime to `M`, the primary holes are repaired by odd multiples of `p` not
divisible by `q`, and the secondary holes are repaired by odd multiples of `q`.
Divisibility by `p` and `q` keeps all three modulus sets pairwise disjoint.
-/

-- Credit: @LiJiaHua1024

namespace OMA.R_Erdos7_erdos_7_R2

open scoped Pointwise

/-- An incomplete odd divisor cover modulo `M` whose uncovered integers split
into two finite families of residue classes modulo `M` within divisor budgets,
together with two distinct odd primes `p` and `q` coprime to `M`. -/
def H1 : Prop :=
  ∃ (M p q h₁ h₂ : ℕ) (u : Fin h₁ → ℤ) (v : Fin h₂ → ℤ) (r : ℕ → ℤ),
    p.Prime ∧ q.Prime ∧ 3 ≤ p ∧ 3 ≤ q ∧ p ≠ q ∧
    Odd M ∧ p.Coprime M ∧ q.Coprime M ∧
    (p - 2) * h₁ < (M.divisors.erase 1).card ∧
    (q - 2) * h₂ < (M.divisors.erase 1).card ∧
    (∃ z : ℤ, ∀ d ∈ M.divisors.erase 1, ¬ (d : ℤ) ∣ z - r d) ∧
    ∀ z : ℤ,
      (∃ d ∈ M.divisors.erase 1, (d : ℤ) ∣ z - r d) ∨
      (∃ i : Fin h₁, (M : ℤ) ∣ z - u i) ∨
      (∃ j : Fin h₂, (M : ℤ) ∣ z - v j)

/-- Primary holes modulo `M` within the `p`-budget can be covered by distinct
odd moduli greater than `1` divisible by `p` and not divisible by `q`. -/
def H2 : Prop :=
  ∀ (M p q h₁ : ℕ) (u : Fin h₁ → ℤ),
    p.Prime → q.Prime → 3 ≤ p → 3 ≤ q → p ≠ q →
    Odd M → p.Coprime M → q.Coprime M →
    (p - 2) * h₁ < (M.divisors.erase 1).card →
    ∃ S₁ : Finset ℕ, ∃ a₁ : ℕ → ℤ,
      (∀ d ∈ S₁, 1 < d ∧ Odd d ∧ p ∣ d ∧ ¬ q ∣ d) ∧
      ∀ z : ℤ, (∃ i : Fin h₁, (M : ℤ) ∣ z - u i) →
        ∃ d ∈ S₁, (d : ℤ) ∣ z - a₁ d

/-- Secondary holes modulo `M` within the `q`-budget can be covered by distinct
odd moduli greater than `1` divisible by `q`. -/
def H3 : Prop :=
  ∀ (M p q h₂ : ℕ) (v : Fin h₂ → ℤ),
    p.Prime → q.Prime → 3 ≤ p → 3 ≤ q → p ≠ q →
    Odd M → p.Coprime M → q.Coprime M →
    (q - 2) * h₂ < (M.divisors.erase 1).card →
    ∃ S₂ : Finset ℕ, ∃ a₂ : ℕ → ℤ,
      (∀ d ∈ S₂, 1 < d ∧ Odd d ∧ q ∣ d) ∧
      ∀ z : ℤ, (∃ j : Fin h₂, (M : ℤ) ∣ z - v j) →
        ∃ d ∈ S₂, (d : ℤ) ∣ z - a₂ d

/-- Congruence classes with distinct odd positive moduli define a strict ideal
covering system avoiding `Ideal.span {2}`. -/
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

theorem main : H1 → H2 → H3 → type_of% @Erdos7.erdos_7 := by
  classical
  rintro ⟨M, p, q, h₁, h₂, u, v, r, hp, hq, hp3, hq3, hpq, hodd, hcopP, hcopQ,
    budget₁, budget₂, _, seed⟩ repair₁ repair₂
  obtain ⟨S₁, a₁, valid₁, cover₁⟩ :=
    repair₁ M p q h₁ u hp hq hp3 hq3 hpq hodd hcopP hcopQ budget₁
  obtain ⟨S₂, a₂, valid₂, cover₂⟩ :=
    repair₂ M p q h₂ v hp hq hp3 hq3 hpq hodd hcopP hcopQ budget₂
  let D := M.divisors.erase 1
  have mem_dvd {d : ℕ} (hd : d ∈ D) : d ∣ M :=
    (Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2).1
  have disjoint₁ {d : ℕ} (hd : d ∈ S₁) : d ∉ D := by
    intro hD
    exact (hp.coprime_iff_not_dvd.mp hcopP) (dvd_trans (valid₁ d hd).2.2.1 (mem_dvd hD))
  have disjoint₂ {d : ℕ} (hd : d ∈ S₂) : d ∉ D := by
    intro hD
    exact (hq.coprime_iff_not_dvd.mp hcopQ) (dvd_trans (valid₂ d hd).2.2 (mem_dvd hD))
  have disjoint₁₂ {d : ℕ} (hd : d ∈ S₂) : d ∉ S₁ := by
    intro hS₁
    exact (valid₁ d hS₁).2.2.2 (valid₂ d hd).2.2
  apply integer_cover ((D ∪ S₁) ∪ S₂)
    (fun d => if d ∈ D then r d else if d ∈ S₁ then a₁ d else a₂ d)
  · intro d hd
    rcases Finset.mem_union.mp hd with hd₁ | hd₂
    · rcases Finset.mem_union.mp hd₁ with hdD | hdS₁
      · have hpos := Nat.pos_of_dvd_of_pos (mem_dvd hdD) hodd.pos
        have hne := (Finset.mem_erase.mp hdD).1
        exact ⟨by omega, hodd.of_dvd_nat (mem_dvd hdD)⟩
      · exact ⟨(valid₁ d hdS₁).1, (valid₁ d hdS₁).2.1⟩
    · exact ⟨(valid₂ d hd₂).1, (valid₂ d hd₂).2.1⟩
  · intro z
    rcases seed z with ⟨d, hd, hz⟩ | holes₁ | holes₂
    · change d ∈ D at hd
      refine ⟨d, Finset.mem_union_left _ (Finset.mem_union_left _ hd), ?_⟩
      simpa only [if_pos hd] using hz
    · obtain ⟨d, hd, hz⟩ := cover₁ z holes₁
      refine ⟨d, Finset.mem_union_left _ (Finset.mem_union_right _ hd), ?_⟩
      simpa only [if_neg (disjoint₁ hd), if_pos hd] using hz
    · obtain ⟨d, hd, hz⟩ := cover₂ z holes₂
      refine ⟨d, Finset.mem_union_right _ hd, ?_⟩
      simpa only [if_neg (disjoint₂ hd), if_neg (disjoint₁₂ hd)] using hz

end OMA.R_Erdos7_erdos_7_R2
