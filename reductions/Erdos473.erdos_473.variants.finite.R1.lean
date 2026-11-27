import FormalConjectures.ErdosProblems.«473»

/-!
# Finite prime paths from two classes of even prime circles

Cut a circle at its closing edge for paths of even size. For odd sizes,
rotate a circle of the next even size and delete its largest entry.
Explicit prime paths cover sizes 2 through 16.
-/

namespace OMA.R_Erdos473_erdos_473_variants_finite_R1
/-- Removing the final vertex from a prime circle produces a prime path, provided the
circle has been rotated so that this vertex is last. -/
private theorem finite_of_cycle_with_last_fixed {n : ℕ}
    (a : Fin (n + 1) ≃ Fin (n + 1))
    (hlast : a (Fin.last n) = Fin.last n)
    (hcycle : ∀ k : Fin (n + 1),
      ((a k).val + 1 +
        (a ⟨(k.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩).val + 1).Prime) :
    ∃ b : Fin n ≃ Fin n, ∀ k : Fin n, ∀ hk : k.val + 1 < n,
      ((b k).val + 1 + (b ⟨k.val + 1, hk⟩).val + 1).Prime := by
  let f : Fin n → Fin n := fun i =>
    ⟨(a i.castSucc).val, by
      have hi := (a i.castSucc).isLt
      by_contra hnot
      have hval : (a i.castSucc).val = n := by omega
      have heq : a i.castSucc = Fin.last n := Fin.ext hval
      have hi' : i.castSucc = Fin.last n := a.injective (heq.trans hlast.symm)
      have : i.val = n := congrArg Fin.val hi'
      omega⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hv : (a i.castSucc).val = (a j.castSucc).val := by
      have hv := congrArg (fun x : Fin n => x.val) hij
      change (a i.castSucc).val = (a j.castSucc).val at hv
      exact hv
    have ha : a i.castSucc = a j.castSucc := Fin.ext hv
    have hij' : i.castSucc = j.castSucc := a.injective ha
    have hval : i.val = j.val := by
      have hvij := congrArg (fun z : Fin (n + 1) => z.val) hij'
      simpa using hvij
    exact Fin.ext hval
  let b : Fin n ≃ Fin n := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨b, ?_⟩
  intro k hk
  have hmod : (k.castSucc.val + 1) % (n + 1) = k.val + 1 := by
    rw [Fin.val_castSucc]
    exact Nat.mod_eq_of_lt (by omega)
  have hidx : (⟨(k.castSucc.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)) =
      (⟨k.val + 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    exact hmod
  have hp := hcycle k.castSucc
  rw [hidx] at hp
  have hnext : (⟨k.val + 1, hk⟩ : Fin n).castSucc =
      (⟨k.val + 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [← hnext] at hp
  have hb (i : Fin n) : (b i).val = (f i).val := rfl
  rw [hb k, hb ⟨k.val + 1, hk⟩]
  simpa [f, Fin.val_castSucc] using hp


private theorem finite_of_cycle {n : ℕ} (a : Fin (n + 1) ≃ Fin (n + 1))
    (ha : ∀ k : Fin (n + 1),
      ((a k).val + 1 +
        (a ⟨(k.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩).val + 1).Prime) :
    ∃ b : Fin n ≃ Fin n, ∀ k : Fin n, ∀ hk : k.val + 1 < n,
      ((b k).val + 1 + (b ⟨k.val + 1, hk⟩).val + 1).Prime := by
  let d := a.symm (Fin.last n) - Fin.last n
  let b : Fin (n + 1) ≃ Fin (n + 1) := (Equiv.addRight d).trans a
  have hnext (k : Fin (n + 1)) :
      (⟨(k.val + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)) = k + 1 := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp_rw [hnext] at ha
  apply finite_of_cycle_with_last_fixed b
  · change a (Fin.last n + (a.symm (Fin.last n) - Fin.last n)) = Fin.last n
    have harg : Fin.last n + (a.symm (Fin.last n) - Fin.last n) =
        a.symm (Fin.last n) := by abel
    exact (congrArg a harg).trans (a.apply_symm_apply _)
  · intro k
    rw [hnext]
    change ((a (k + d)).val + 1 + (a ((k + 1) + d)).val + 1).Prime
    rw [add_right_comm k 1 d]
    exact ha (k + d)

private theorem checked_path {n : ℕ} (f : Fin n → Fin n) (hb : Function.Bijective f)
    (hp : ∀ k : Fin n, ∀ h : k.val + 1 < n,
      ((f k).val + 1 + ((f ⟨k.val + 1, h⟩).val + 1)).Prime) :
    ∃ a : Fin n ≃ Fin n, ∀ k : Fin n, ∀ h : k.val + 1 < n,
      ((a k).val + 1 + ((a ⟨k.val + 1, h⟩).val + 1)).Prime :=
  ⟨Equiv.ofBijective f hb, hp⟩

-- Certificates for the small cases of the finite prime-sum ordering, n = 2 through 16.
-- Search space per order: simple paths on 1..n, extending only by a prime sum.
-- Dense bipartite prime-sum graphs at these orders make backtracking practical.
-- Stop at the first witness per order or after 100000 search nodes per order.
theorem small_path (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 16) :
    ∃ a : Fin n ≃ Fin n, ∀ k : Fin n, ∀ h : k.val + 1 < n,
      ((a k).val + 1 + ((a ⟨k.val + 1, h⟩).val + 1)).Prime := by
  interval_cases n
  · exact checked_path ![0, 1] (by decide) (by decide)
  · exact checked_path ![0, 1, 2] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3] (by decide) (by decide)
  · exact checked_path ![0, 3, 2, 1, 4] (by decide) (by decide)
  · exact checked_path ![0, 3, 2, 1, 4, 5] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4, 7] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4, 7, 8] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4, 7, 8, 9] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 9, 8, 7, 4, 5, 10] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4, 11, 10, 7, 8, 9] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4, 11, 10, 7, 8, 9, 12] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 12, 9, 8, 7, 10, 11, 4, 13] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4, 11, 10, 7, 14, 13, 8, 9, 12] (by decide) (by decide)
  · exact checked_path ![0, 1, 2, 3, 6, 5, 4, 11, 10, 7, 8, 9, 12, 15, 14, 13] (by decide) (by decide)


/-- Prime circles of order divisible by four, beyond the verified small cases. -/
def H1 : Prop :=
  ∀ n : ℕ, (hn : 18 ≤ n) → n % 4 = 0 → ∃ a : Fin n ≃ Fin n, ∀ k : Fin n,
    ((a k).val + 1 + (a ⟨(k.val + 1) % n, Nat.mod_lt _ (by omega)⟩).val + 1).Prime

/-- Prime circles of order two modulo four, beyond the verified small cases. -/
def H2 : Prop :=
  ∀ n : ℕ, (hn : 18 ≤ n) → n % 4 = 2 → ∃ a : Fin n ≃ Fin n, ∀ k : Fin n,
    ((a k).val + 1 + (a ⟨(k.val + 1) % n, Nat.mod_lt _ (by omega)⟩).val + 1).Prime

theorem main : H1 → H2 → type_of% @Erdos473.erdos_473.variants.finite := by
  intro hzero htwo n hn
  by_cases hsmall : n ≤ 16
  · exact small_path n hn hsmall
  have cycles (m : ℕ) (hm : 18 ≤ m) (he : m % 2 = 0) :
      ∃ a : Fin m ≃ Fin m, ∀ k : Fin m,
        ((a k).val + 1 + (a ⟨(k.val + 1) % m, Nat.mod_lt _ (by omega)⟩).val + 1).Prime := by
    by_cases h : m % 4 = 0
    · exact hzero m hm h
    · exact htwo m hm (by omega)
  by_cases he : n % 2 = 0
  · obtain ⟨a, ha⟩ := cycles n (by omega) he
    refine ⟨a, ?_⟩
    intro k hk
    simpa [Nat.mod_eq_of_lt hk, Nat.add_assoc] using ha k
  · obtain ⟨a, ha⟩ := cycles (n + 1) (by omega) (by omega)
    simpa only [Nat.add_assoc] using finite_of_cycle a ha

end OMA.R_Erdos473_erdos_473_variants_finite_R1
