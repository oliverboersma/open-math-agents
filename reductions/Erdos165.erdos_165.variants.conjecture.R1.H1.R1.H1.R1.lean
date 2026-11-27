import OMAReductions.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1

/-!
Copyright 2026 Wesley Pegden. Licensed under the Apache License, Version 2.0.
Source: wpegden/twobites, commit d9d2f5562c4b15e50a9baa2a597357cb4ea87a23.
https://github.com/wpegden/twobites/tree/d9d2f5562c4b15e50a9baa2a597357cb4ea87a23
Formalization: Trellis autoformalization, with Codex-directed manual repairs.
Mathematics: Zion Hefty, Paul Horn, Dylan King, and Florian Pfender,
"Improving R(3,k) in just two bites", arXiv:2510.19718.
Adaptation, native construction interface, and Lean 4.33.1 compatibility:
Hanan Beer (@hananzlt). Ancestor reduction: @skytracker404.
This proves deterministic triangle deletion; the independence estimate remains separate.
-/

namespace OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ m : ℕ, ∃ R S : SimpleGraph (Fin m), ∃ f : Fin n ↪ (Fin m × Fin m),
  let q (a b : Fin m) := min a.val b.val * m + max a.val b.val
  let A := R.comap (fun v => (f v).1)
  let B := S.comap (fun v => (f v).2)
  let cut (X Y : SimpleGraph (Fin n)) (r : Fin n → Fin m) :=
    let d (u v : Fin n) :=
      (∃ w, X.Adj u v ∧ X.Adj u w ∧ X.Adj v w ∧
        q (r u) (r w) < q (r u) (r v) ∧ q (r v) (r w) < q (r u) (r v)) ∨
      (∃ w, Y.Adj w u ∧ Y.Adj w v ∧ X.Adj u v)
    SimpleGraph.fromRel (fun u v => X.Adj u v ∧ ¬ (d u v ∨ d v u))
  let C := cut A B (fun v => (f v).1)
  let D := cut B A (fun v => (f v).2)
  let G := SimpleGraph.fromRel (fun u v => C.Adj u v ∨ D.Adj u v)
  ∀ I : Finset (Fin n), G.IsIndepSet (↑I : Set (Fin n)) →
    (I.card : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))

def H2 : Prop :=
  ∀ (n m : ℕ) (R S : SimpleGraph (Fin m)) (f : Fin n ↪ (Fin m × Fin m)),
  let q (a b : Fin m) := min a.val b.val * m + max a.val b.val
  let A := R.comap (fun v => (f v).1)
  let B := S.comap (fun v => (f v).2)
  let cut (X Y : SimpleGraph (Fin n)) (r : Fin n → Fin m) :=
    let d (u v : Fin n) :=
      (∃ w, X.Adj u v ∧ X.Adj u w ∧ X.Adj v w ∧
        q (r u) (r w) < q (r u) (r v) ∧ q (r v) (r w) < q (r u) (r v)) ∨
      (∃ w, Y.Adj w u ∧ Y.Adj w v ∧ X.Adj u v)
    SimpleGraph.fromRel (fun u v => X.Adj u v ∧ ¬ (d u v ∨ d v u))
  let C := cut A B (fun v => (f v).1)
  let D := cut B A (fun v => (f v).2)
  let G := SimpleGraph.fromRel (fun u v => C.Adj u v ∨ D.Adj u v)
  G.CliqueFree 3

theorem main : H1 → H2 → OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1.H1 := by
  intro h1 h2 ε hε
  obtain ⟨n0, hn0⟩ := h1 ε hε
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨m, R, S, f, hf⟩ := hn0 n hn
  exact ⟨_, h2 n m R S f, hf⟩

end OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1_H1_R1
