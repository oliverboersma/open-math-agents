import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1

/-!
Reduce the write-0 first-transition upper bound into the Coq-BB5 pipeline shape:

* H1 — LOOP1: a repeated blank-tape configuration within 107 steps implies nonhalting
* H2 — early halt mono: a halt by step 107 upgrades to HaltsAfter 107
* H3 — survivors: 107 live steps with pairwise-distinct configs imply nonhalting

Donors: @Halldon BeaverBound / BB_4.R1.H2.R1, @henry10101001 BB_4.R2,
@steveDOTdigital, Coq-BB5 BB4 enumeration (LOOP1 / NGRAM / REPWL),
Prove2Me BB5.no_halt_RA (self-loop invariant).
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

open Turing Turing.BusyBeaver

def H1 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)),
    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
    (∃ i j : ℕ, i < j ∧ j ≤ 107 ∧ ∃ c : Cfg (Fin 2) (Fin 4),
      M.multiStep (Machine.init []) i = some c ∧ c.q.isSome ∧
      M.multiStep (Machine.init []) j = some c ∧ c.q.isSome) →
    ¬ M.IsHalting

def H2 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)),
    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
    (∃ k : ℕ, k ≤ 107 ∧ M.HaltsAfter (Machine.init []) k) →
    M.HaltsAfter (Machine.init []) 107

def H3 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)),
    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
    (∀ k : ℕ, k ≤ 107 → ¬ M.HaltsAfter (Machine.init []) k) →
    (∀ i j : ℕ, i < j → j ≤ 107 → ∀ c : Cfg (Fin 2) (Fin 4),
      M.multiStep (Machine.init []) i = some c → c.q.isSome →
      M.multiStep (Machine.init []) j = some c → c.q.isSome → False) →
    ¬ M.IsHalting

theorem main : H1 → H2 → H3 → OMA.R_BusyBeaver_BB_4_R1_H2_R1.H1 := by
  intro hLoop hMono hHard M hFirst halts
  by_cases hEarly : ∃ k : ℕ, k ≤ 107 ∧ M.HaltsAfter (Machine.init []) k
  · exact hMono M hFirst hEarly
  · have noEarly : ∀ k : ℕ, k ≤ 107 → ¬ M.HaltsAfter (Machine.init []) k := by
      intro k hk he
      exact hEarly ⟨k, hk, he⟩
    by_cases hCyc : ∃ i j : ℕ, i < j ∧ j ≤ 107 ∧ ∃ c : Cfg (Fin 2) (Fin 4),
        M.multiStep (Machine.init []) i = some c ∧ c.q.isSome ∧
        M.multiStep (Machine.init []) j = some c ∧ c.q.isSome
    · exact (hLoop M hFirst hCyc halts).elim
    · have noCyc : ∀ i j : ℕ, i < j → j ≤ 107 → ∀ c : Cfg (Fin 2) (Fin 4),
          M.multiStep (Machine.init []) i = some c → c.q.isSome →
          M.multiStep (Machine.init []) j = some c → c.q.isSome → False := by
        intro i j hij hj c hi hs1 hjlive hs2
        exact hCyc ⟨i, j, hij, hj, c, hi, hs1, hjlive, hs2⟩
      exact (hHard M hFirst noEarly noCyc halts).elim

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1
