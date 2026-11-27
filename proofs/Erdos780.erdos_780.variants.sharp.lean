import FormalConjectures.ErdosProblems.«780»

-- Problem: Erdős Problem 780 — sharp
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/780.lean:61 (declaration Erdos780.erdos_780.variants.sharp)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős Problem 780, sharpness of the bound

The colouring. Write n = (t - 1) * (k - 1) + (k * r - 1). The first (t - 1) * (k - 1) vertices
are cut into t - 1 consecutive blocks of size k - 1; the remaining k * r - 1 vertices form the
big part. An edge whose least vertex lies in block b gets colour b, and an edge whose least
vertex (hence every vertex) lies in the big part gets the last colour t - 1. Both cases are the
single formula min (least vertex / (k - 1)) (t - 1).

Why no colour has k pairwise disjoint edges:
* if every least vertex is in the big part, the k edges are k * r distinct vertices of the big
  part, which has only k * r - 1 vertices;
* otherwise some least vertex is in a block, the common colour is that block, so all k least
  vertices lie in one block of size k - 1, and two of them coincide: those two edges meet.
-/

theorem OMA.solution : type_of% @Erdos780.erdos_780.variants.sharp := by
  intro k r t hk hr ht
  have hne : ∀ e : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r},
      e.1.Nonempty := fun e => Finset.card_pos.mp (by rw [e.2]; exact hr)
  refine ⟨fun e => ⟨min ((e.1.min' (hne e)).val / (k - 1)) (t - 1),
    lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩, ?_⟩
  rintro ⟨i, e, hc, hd⟩
  let least (j : Fin k) := (e j).1.min' (hne (e j))
  -- all k edges have colour i
  have hval : ∀ j, min ((least j).val / (k - 1)) (t - 1) = i.val :=
    fun j => congrArg Fin.val (hc j)
  by_cases hA : ∀ j, (t - 1) * (k - 1) ≤ (least j).val
  · -- Case 1: every edge lies inside the big part.
    have hcard : ∀ j, (e j).1.card = r := fun j => (e j).2
    have hpd : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun j => (e j).1) := fun a _ b _ hab => hd hab
    have hU : (Finset.univ.biUnion fun j => (e j).1).card = k * r := by
      rw [Finset.card_biUnion hpd]
      simp [hcard]
    have hle : (Finset.univ.biUnion fun j => (e j).1).card ≤ (Finset.range (k * r - 1)).card := by
      refine Finset.card_le_card_of_injOn (fun v => v.val - (t - 1) * (k - 1)) ?_ ?_
      · intro v hv
        obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hv)
        have h1 : (least j).val ≤ v.val :=
          Fin.le_def.mp (Finset.min'_le _ v hj)
        have h2 := hA j
        have h3 := v.isLt
        have h4 : v.val - (t - 1) * (k - 1) < k * r - 1 := by omega
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr h4)
      · intro v hv w hw hvw
        obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hv)
        obtain ⟨j', -, hj'⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hw)
        have h1 : (least j).val ≤ v.val :=
          Fin.le_def.mp (Finset.min'_le _ v hj)
        have h1' : (least j').val ≤ w.val :=
          Fin.le_def.mp (Finset.min'_le _ w hj')
        have h2 := hA j
        have h2' := hA j'
        have hvw' : v.val - (t - 1) * (k - 1) = w.val - (t - 1) * (k - 1) := hvw
        exact Fin.ext (by omega)
    rw [hU, Finset.card_range] at hle
    have hpos : 0 < k * r := Nat.mul_pos hk hr
    omega
  · -- Case 2: some edge starts in a block, hence all of them start in that same block.
    obtain ⟨j₀, hj₀'⟩ := not_forall.mp hA
    have hj₀ : (least j₀).val < (t - 1) * (k - 1) := not_le.mp hj₀'
    have hq : 0 < k - 1 := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
      · have h5 : (t - 1) * (k - 1) = 0 := by rw [h0, Nat.mul_zero]
        omega
      · exact h0
    have hi : i.val < t - 1 := by
      rw [← hval j₀]
      exact lt_of_le_of_lt (Nat.min_le_left _ _) ((Nat.div_lt_iff_lt_mul hq).mpr hj₀)
    have hdiv : ∀ j, (least j).val / (k - 1) = i.val := by
      intro j
      have h := hval j
      rcases le_total ((least j).val / (k - 1)) (t - 1) with hle | hle
      · rwa [min_eq_left hle] at h
      · rw [min_eq_right hle] at h
        omega
    -- k least vertices, only k - 1 residues modulo k - 1: two of them agree
    obtain ⟨a, b, hab, hres⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun j : Fin k =>
        (⟨(least j).val % (k - 1), Nat.mod_lt _ hq⟩ : Fin (k - 1)))
      (by rw [Fintype.card_fin, Fintype.card_fin]; omega)
    have hmod : (least a).val % (k - 1)
        = (least b).val % (k - 1) := congrArg Fin.val hres
    -- same quotient and same residue: the two least vertices are equal
    have heq : least a = least b := by
      apply Fin.ext
      rw [← Nat.div_add_mod (least a).val (k - 1),
        ← Nat.div_add_mod (least b).val (k - 1), hdiv a, hdiv b, hmod]
    have hmem : least a ∈ (e b).1 := by
      rw [heq]
      exact Finset.min'_mem _ _
    exact Finset.disjoint_left.mp (hd hab) (Finset.min'_mem _ _) hmem
