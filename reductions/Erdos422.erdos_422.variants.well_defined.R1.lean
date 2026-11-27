import FormalConjectures.ErdosProblems.«422»

/-!
A natural-valued recurrence returns zero when it would refer outside its
already-computed positive terms. Once the finite prefix is verified, a bound
by the index prevents the first invalid reference from occurring.
-/

namespace OMA.R_Erdos422_erdos_422_variants_well_defined_R1

def H1 : Prop :=
  ∃ q : ℕ → ℕ, q 1 = 1 ∧ q 2 = 1 ∧
    (∀ n : ℕ, 2 < n → q n =
      if 0 < q (n - 1) ∧ q (n - 1) < n ∧ 0 < q (n - 2) ∧ q (n - 2) < n then
        q (n - q (n - 1)) + q (n - q (n - 2)) else 0) ∧
    (∀ n : ℕ, 0 < n → n ≤ 512 → 0 < q n)

def H2 : Prop :=
  ∀ q : ℕ → ℕ, q 1 = 1 → q 2 = 1 →
    (∀ n : ℕ, 2 < n → q n =
      if 0 < q (n - 1) ∧ q (n - 1) < n ∧ 0 < q (n - 2) ∧ q (n - 2) < n then
        q (n - q (n - 1)) + q (n - q (n - 2)) else 0) →
    ∀ n : ℕ, 512 ≤ n → q n ≤ n

section Proof

theorem main : H1 → H2 → type_of% @Erdos422.erdos_422.variants.well_defined := by
  rintro ⟨q, q1, q2, hrec, hprefix⟩ htail
  have hle (n : ℕ) (hn : 0 < n) : q n ≤ n := by
    by_cases hlarge : 512 ≤ n
    · exact htail q q1 q2 hrec n hlarge
    by_cases hsmall : n = 1
    · subst n
      simp [q1]
    have hpos := hprefix (n + 1) (by omega) (by omega)
    have hstep := hrec (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at hstep
    split at hstep
    · rename_i hvalid
      omega
    · omega
  have hpos (n : ℕ) (hn : 0 < n) : 0 < q n := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hsmall : n ≤ 512
      · exact hprefix n hn hsmall
      have hv : 0 < q (n - 1) ∧ q (n - 1) < n ∧
          0 < q (n - 2) ∧ q (n - 2) < n :=
        ⟨ih _ (by omega) (by omega), (hle _ (by omega)).trans_lt (by omega),
          ih _ (by omega) (by omega), (hle _ (by omega)).trans_lt (by omega)⟩
      obtain ⟨ha0, ha, hb0, hb⟩ := hv
      rw [hrec n (by omega), if_pos ⟨ha0, ha, hb0, hb⟩]
      exact Nat.add_pos_left (ih _ (by omega) (by omega)) _
  let f (n : ℕ+) : ℕ+ := ⟨q n, hpos n n.pos⟩
  refine ⟨f, Subtype.ext q1, Subtype.ext q2, ?_⟩
  intro n hn
  have hN : 2 < (n : ℕ) := by exact_mod_cast hn
  have hn1 : ((n - 1 : ℕ+) : ℕ) = (n : ℕ) - 1 := by
    rw [PNat.sub_coe, if_pos (by exact_mod_cast (by omega : 1 < (n : ℕ)))]
    rfl
  have hn2 : ((n - 2 : ℕ+) : ℕ) = (n : ℕ) - 2 := by
    rw [PNat.sub_coe, if_pos hn]
    rfl
  have hlt1 : f (n - 1) < n := by
    rw [← PNat.coe_lt_coe]
    change q ((n - 1 : ℕ+) : ℕ) < (n : ℕ)
    rw [hn1]
    exact (hle _ (by omega)).trans_lt (by omega)
  have hlt2 : f (n - 2) < n := by
    rw [← PNat.coe_lt_coe]
    change q ((n - 2 : ℕ+) : ℕ) < (n : ℕ)
    rw [hn2]
    exact (hle _ (by omega)).trans_lt (by omega)
  refine ⟨hlt1, hlt2, Subtype.ext ?_⟩
  change q n = q ((n - f (n - 1) : ℕ+) : ℕ) + q ((n - f (n - 2) : ℕ+) : ℕ)
  rw [PNat.sub_coe, if_pos hlt1, PNat.sub_coe, if_pos hlt2]
  change q n = q ((n : ℕ) - q ((n - 1 : ℕ+) : ℕ)) + q ((n : ℕ) - q ((n - 2 : ℕ+) : ℕ))
  rw [hn1, hn2, hrec n hN]
  have ha := hle ((n : ℕ) - 1) (by omega)
  have hb := hle ((n : ℕ) - 2) (by omega)
  rw [if_pos ⟨hpos _ (by omega), by omega, hpos _ (by omega), by omega⟩]

end Proof

end OMA.R_Erdos422_erdos_422_variants_well_defined_R1
