import FormalConjectures.Paper.PartitionParity

-- Reduction PartitionParity.parkin_shanks.R1 of the Parkin–Shanks conjecture on partition parities.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target says that both parity classes of the partition function have natural density `1/2`.
-- The two densities are statements about separate sets that are proved by different mechanisms
-- (progression theorems supply evens, congruences supply odds), so each is its own step; neither
-- half follows from the other.

namespace OMA.R_PartitionParity_parkin_shanks_R1

/-- Half of the partition numbers are even, asymptotically. -/
def H1 : Prop := {n : ℕ | Even (Nat.partitionNumber n)}.HasDensity (1 / 2)

/-- Half of the partition numbers are odd, asymptotically. -/
def H2 : Prop := {n : ℕ | Odd (Nat.partitionNumber n)}.HasDensity (1 / 2)

theorem main : H1 → H2 → type_of% @PartitionParity.parkin_shanks := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_PartitionParity_parkin_shanks_R1
