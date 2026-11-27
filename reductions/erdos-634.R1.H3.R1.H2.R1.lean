import OMAReductions.R_erdos_634_R1_H3_R1

/-!
# Erdos 634, reduction R1.H3.R1.H2.R1

H2 of R1.H3.R1 (tile angles a k * pi / n in lowest terms, some prime at least 7 divides n), split
into geometry and number theory. S (n, a) below is Laczkovich's condition that the only rational
relations among the sawtooth values ((k a i / n)) over k coprime to n are the trivial ones (equal
angles, right angles). H1: the geometric step, a scalene target is similar to the tile when S holds
(Laczkovich 1995, Lemma 9). H2: S holds when some prime at least 7 divides n (Lemma S).
-/

namespace OMA.R_erdos_634_R1_H3_R1_H2_R1

def H1 : Prop := ∀ (p : ℕ) (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → ((∀ i, 0 < a i) → ∑ i, a i = n → ∀ e : Fin 3 → ℚ, (∀ k : ℕ, k.Coprime n → ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0 else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0) → e ∈ Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})) → ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))

def H2 : Prop := ∀ (n : ℕ) (a : Fin 3 → ℕ), (∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ l ∣ n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ i, 0 < a i) → ∑ i, a i = n → ∀ e : Fin 3 → ℚ, (∀ k : ℕ, k.Coprime n → ∑ i, (if Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) = 0 then 0 else Int.fract (((k * a i : ℕ) : ℚ) / (n : ℚ)) - 1 / 2) * e i = 0) → e ∈ Submodule.span ℚ ({v | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H3_R1.H2 :=
  fun h1 h2 p _ _ T Ts hc hd hu t hi n a hn ha hg hl =>
    h1 p T Ts hc hd hu t hi n a hn ha hg (h2 n a hl hg)

end OMA.R_erdos_634_R1_H3_R1_H2_R1
