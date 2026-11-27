import OMAReductions.R_erdos_634_R1_H2_R1

/-!
# Erdos 634, reduction R1.H2.R1.H2.R1

Laczkovich's classification of tilings by a tile whose angles are rational multiples of pi
(Laczkovich 1995, Theorem 5.3 and its tables, as formalized by Bonfioli), split by the denominator:
* H1: the tile angles are a k * pi / n with a k positive, a 0 + a 1 + a 2 = n and gcd 1;
* H2 (number theory, Lemma S): either the rational relation space of (n, a) is trivial, or n > 200
  is 5-smooth, or n is one of 3, 4, 6, 8, 10, 12, 18, 24, 30, 60;
* H3: in the first two cases T is similar to the tile or the RightRow case holds (Lemma 9);
* H4: the exceptional denominators.
The relation space of (n, a) is the intersection over k coprime to n of the kernels of
x ↦ Σ saw(k a i / n) x i, where saw t is 0 when t is an integer and fract t - 1/2 otherwise; it is
trivial when it is spanned by the e i - e j with a i = a j and the e i with 2 a i = n.
A and B are the angle functions of T and of the tile t (A k is the angle at vertex k).
-/

namespace OMA.R_erdos_634_R1_H2_R1_H2_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, ∃ q : ℚ, B k = q * Real.pi) → ∃ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) ∧ ∑ i, a i = n ∧ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 ∧ ∀ k, B k = (a k : ℝ) * Real.pi / n

def H2 : Prop := ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (⨅ (k : ℕ) (_ : k.Coprime n), LinearMap.ker (∑ i, (if Int.fract ((k * a i : ℕ) / (n : ℚ)) = 0 then 0 else Int.fract ((k * a i : ℕ) / (n : ℚ)) - 1 / 2) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)) = Submodule.span ℚ ({v : Fin 3 → ℚ | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v : Fin 3 → ℚ | ∃ i, 2 * a i = n ∧ v = Pi.single i 1}) ∨ (200 < n ∧ (∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5)) ∨ (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 18 ∨ n = 24 ∨ n = 30 ∨ n = 60)

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, B k = (a k : ℝ) * Real.pi / n) → ((⨅ (k : ℕ) (_ : k.Coprime n), LinearMap.ker (∑ i, (if Int.fract ((k * a i : ℕ) / (n : ℚ)) = 0 then 0 else Int.fract ((k * a i : ℕ) / (n : ℚ)) - 1 / 2) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)) = Submodule.span ℚ ({v : Fin 3 → ℚ | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v : Fin 3 → ℚ | ∃ i, 2 * a i = n ∧ v = Pi.single i 1}) ∨ (200 < n ∧ (∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5))) → (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) ∨ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l)

def H4 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, B k = (a k : ℝ) * Real.pi / n) → (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 18 ∨ n = 24 ∨ n = 30 ∨ n = 60) → (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) ∨ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) ∨ ((∀ k, A k = Real.pi / 3) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30])

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_634_R1_H2_R1.H2 := by
  intro g1 g2 g3 g4 p hp hp3 T Ts hc hd hu t A B hA hB hr
  obtain ⟨n, a, hpos, hsum, hg, ha⟩ := g1 p hp hp3 T Ts hc hd hu t A B hA hB hr
  rcases g2 n a hpos hsum hg with hS | h200 | hexc
  · exact Or.imp_right Or.inl (g3 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inl hS))
  · exact Or.imp_right Or.inl (g3 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha (Or.inr h200))
  · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB n a hpos hsum hg ha hexc

end OMA.R_erdos_634_R1_H2_R1_H2_R1
