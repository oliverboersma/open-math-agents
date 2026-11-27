import OMAReductions.R_Erdos551_erdos_551_variants_sufficiently_large_R2

-- Step Erdos551.erdos_551.variants.sufficiently_large.R2.H1: hypothesis H1 of reduction Erdos551.erdos_551.variants.sufficiently_large.R2
-- Credit: @ishaanzee
-- Proof: n - 1 disjoint cliques of size k - 1 have no k-cycle and no independent n-set, so every
-- N in the Ramsey set exceeds (k-1)(n-1); the set is nonempty by the Erdos-Szekeres bound
-- (Combinatorics.Diagonal.hasRamseyProperty_choose: a k-clique contains a k-cycle).

open SimpleGraph Filter

namespace E551Aux

-- The three lemmas below are copied from the merged reduction
-- Erdos551.erdos_551.variants.sufficiently_large.R1 (credit to its author).
/-- The disjoint union of cliques `{u | u / (k-1) = b}` contains no cycle of length `k`. -/
lemma no_cycle (k N : ℕ) (hk : 3 ≤ k) :
    ¬ (cycleGraph k).IsContained
      (SimpleGraph.fromRel fun u v : Fin N => u.val / (k - 1) = v.val / (k - 1)) := by
  rintro ⟨f⟩
  have hblk : ∀ j (hj : j < k),
      (f.toHom ⟨j, hj⟩).val / (k - 1) = (f.toHom ⟨0, by omega⟩).val / (k - 1) := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      have hadj : (cycleGraph k).Adj ⟨j, by omega⟩ ⟨j + 1, hj⟩ :=
        pathGraph_le_cycleGraph (pathGraph_adj.2 (Or.inl rfl))
      have h := f.toHom.map_adj hadj
      rw [SimpleGraph.fromRel_adj] at h
      rw [← ih (by omega)]
      rcases h.2 with h' | h'
      · exact h'.symm
      · exact h'
  let φ : Fin k → Fin (k - 1) := fun i => ⟨(f.toHom i).val % (k - 1), Nat.mod_lt _ (by omega)⟩
  have hinj : Function.Injective φ := by
    intro i j hij
    have h1 : (f.toHom i).val % (k - 1) = (f.toHom j).val % (k - 1) := congrArg Fin.val hij
    have hi := hblk i.1 i.2
    have hj := hblk j.1 j.2
    simp only [Fin.eta] at hi hj
    have h2 : (f.toHom i).val / (k - 1) = (f.toHom j).val / (k - 1) := by rw [hi, hj]
    apply f.injective
    apply Fin.ext
    calc (f.toHom i).val = (k - 1) * ((f.toHom i).val / (k - 1)) + (f.toHom i).val % (k - 1) :=
          (Nat.div_add_mod _ _).symm
      _ = (k - 1) * ((f.toHom j).val / (k - 1)) + (f.toHom j).val % (k - 1) := by rw [h1, h2]
      _ = (f.toHom j).val := Nat.div_add_mod _ _
  have := Fintype.card_le_of_injective φ hinj
  simp only [Fintype.card_fin] at this
  omega

/-- The complement of `n - 1` disjoint cliques (on at most `(k-1)(n-1)` vertices) has no `K_n`. -/
lemma no_clique (n k N : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hN : N ≤ (k - 1) * (n - 1)) :
    ¬ (completeGraph (Fin n)).IsContained
      (SimpleGraph.fromRel fun u v : Fin N => u.val / (k - 1) = v.val / (k - 1))ᶜ := by
  rintro ⟨g⟩
  have hlt : ∀ i, (g.toHom i).val / (k - 1) < n - 1 := by
    intro i
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact lt_of_lt_of_le (g.toHom i).isLt (hN.trans (le_of_eq (Nat.mul_comm _ _)))
  let ψ : Fin n → Fin (n - 1) := fun i => ⟨(g.toHom i).val / (k - 1), hlt i⟩
  have hinj : Function.Injective ψ := by
    intro i j hij
    by_contra hne
    have hadj : (completeGraph (Fin n)).Adj i j := (SimpleGraph.top_adj i j).2 hne
    have h := g.toHom.map_adj hadj
    rw [SimpleGraph.compl_adj, SimpleGraph.fromRel_adj] at h
    have hval : (g.toHom i).val / (k - 1) = (g.toHom j).val / (k - 1) := congrArg Fin.val hij
    exact h.2 ⟨h.1, Or.inl hval⟩
  have := Fintype.card_le_of_injective ψ hinj
  simp only [Fintype.card_fin] at this
  omega

/-- Lower bound: below `(k-1)(n-1)+1` vertices there is a colouring with no red `C_k` and no blue `K_n`. -/
lemma lower_bound (n k N : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (hN : N ≤ (k - 1) * (n - 1)) :
    ∃ C : SimpleGraph (Fin N),
      ¬ (cycleGraph k).IsContained C ∧ ¬ (completeGraph (Fin n)).IsContained Cᶜ :=
  ⟨_, no_cycle k N hk, no_clique n k N hn (by omega) hN⟩


open Classical in
/-- A finite Ramsey bound: on `C(n + k, n)` vertices every graph contains a `k`-clique (hence a
`k`-cycle) or an independent `n`-set (hence a `K_n` in the complement). -/
lemma ramsey_exists (k n : ℕ) : ∀ C : SimpleGraph (Fin (Nat.choose (n + k) n)),
    (cycleGraph k).IsContained C ∨ (completeGraph (Fin n)).IsContained Cᶜ := by
  intro C
  let c : Finset (Fin (Nat.choose (n + k) n)) → Bool :=
    fun e => decide (∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ C.Adj u v)
  have hpair : ∀ u v, u ≠ v → (c {u, v} = true ↔ C.Adj u v) := by
    intro u v huv
    simp only [c, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨a, ha, b, hb, hab, hadj⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hab
    · intro h
      exact ⟨u, Or.inl rfl, v, Or.inr rfl, huv, h⟩
  have hsub : ∀ (S : Finset (Fin (Nat.choose (n + k) n))) (u v : Fin (Nat.choose (n + k) n)),
      u ∈ S → v ∈ S → ({u, v} : Finset _) ⊆ S := by
    intro S u v hu hv x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose n k c Finset.univ (by simp) with
    ⟨S, -, hS, hfalse⟩ | ⟨S, -, hS, htrue⟩
  · right
    let e := S.orderIsoOfFin hS
    let f : Fin n → Fin (Nat.choose (n + k) n) := fun i => (e i).val
    have hinj : Function.Injective f := fun i j h => e.injective (Subtype.ext h)
    refine ⟨Hom.toCopy ⟨f, fun {i j} hij => ?_⟩ hinj⟩
    have hne : f i ≠ f j := fun h => hij.ne (hinj h)
    rw [compl_adj]
    refine ⟨hne, fun hadj => ?_⟩
    have h1 := hfalse {f i, f j} (hsub S _ _ (e i).prop (e j).prop) (Finset.card_pair hne)
    rw [(hpair _ _ hne).2 hadj] at h1
    exact Bool.noConfusion h1
  · left
    let e := S.orderIsoOfFin hS
    let f : Fin k → Fin (Nat.choose (n + k) n) := fun i => (e i).val
    have hinj : Function.Injective f := fun i j h => e.injective (Subtype.ext h)
    refine ⟨Hom.toCopy ⟨f, fun {i j} hij => ?_⟩ hinj⟩
    have hne : f i ≠ f j := fun h => hij.ne (hinj h)
    exact (hpair _ _ hne).1 (htrue {f i, f j} (hsub S _ _ (e i).prop (e j).prop) (Finset.card_pair hne))

end E551Aux

open E551Aux

theorem OMA.solution : OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R2.H1 := by
  unfold OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R2.H1
  filter_upwards [eventually_ge_atTop 3] with n hn k hk
  unfold graphRamsey
  refine le_csInf ?_ ?_
  · exact ⟨Nat.choose (n + k) n, ramsey_exists k n⟩
  intro N hN
  by_contra hlt
  push Not at hlt
  obtain ⟨C, h1, h2⟩ := lower_bound n k N (by omega) (by omega) (by omega)
  rcases hN C with h | h
  · exact h1 h
  · exact h2 h
