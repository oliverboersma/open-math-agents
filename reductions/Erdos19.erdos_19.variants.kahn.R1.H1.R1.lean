import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1

-- Reduction Erdos19.erdos_19.variants.kahn.R1.H1.R1 of step Erdos19.erdos_19.variants.kahn.R1.H1
-- Credit: @mucoucah
-- q = 1 is greedy. For q >= 2: regularise (H2: embed into a D-regular linear hypergraph of the
-- same rank bound), run the nibble on the regular hypergraph (H1: a partial list colouring whose
-- uncoloured part has maximum degree <= D/k while every uncoloured edge keeps >= D/s free colours,
-- s depending only on q), pull the partial colouring back, finish greedily with the free colours.

open Finset

namespace OMA.R_Erdos19_erdos_19_variants_kahn_R1_H1_R1

theorem meet_le {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (d : ℕ) (hd : ∀ i ∈ A, (H.filter (fun A => i ∈ A)).card ≤ d) :
    (H.filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * d := by
  have heq : H.filter (fun B => (A ∩ B).Nonempty) =
      A.biUnion (fun i => H.filter (fun A => i ∈ A)) := by
    ext B
    simp only [mem_filter, mem_biUnion, Finset.Nonempty, mem_inter]
    constructor
    · rintro ⟨hB, i, hiA, hiB⟩
      exact ⟨i, hiA, hB, hiB⟩
    · rintro ⟨i, hiA, hB, hiB⟩
      exact ⟨hB, i, hiA, hiB⟩
  rw [heq]
  calc (A.biUnion (fun i => H.filter (fun A => i ∈ A))).card
      ≤ ∑ i ∈ A, (H.filter (fun A => i ∈ A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, d := Finset.sum_le_sum hd
    _ = A.card * d := by simp

/-- Greedy list colouring. -/
theorem greedy {n m : ℕ} (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hm : 0 < m)
    (hL : ∀ A ∈ H, ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card < (L A).card) :
    ∃ c : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    by_cases hH : H.Nonempty
    · obtain ⟨A, hA⟩ := hH
      let K := H.erase A
      have hKH : K ⊆ H := Finset.erase_subset _ _
      obtain ⟨c, hc, hcL⟩ := ih K (Finset.erase_ssubset hA) (by
        intro B hB
        refine lt_of_le_of_lt ?_ (hL B (hKH hB))
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        exact Finset.erase_subset_erase _ hKH)
      let blocked := (K.filter (fun B => (A ∩ B).Nonempty)).image c
      have hblocked : blocked.card < (L A).card :=
        lt_of_le_of_lt Finset.card_image_le (hL A hA)
      have hfree : (L A \ blocked).Nonempty := by
        apply Finset.card_pos.mp
        have := Finset.le_card_sdiff blocked (L A)
        omega
      obtain ⟨w, hw⟩ := hfree
      have hne : ∀ B ∈ K, (A ∩ B).Nonempty → w ≠ c B := by
        intro B hB hi he
        exact (mem_sdiff.mp hw).2 (he ▸ mem_image_of_mem c (mem_filter.mpr ⟨hB, hi⟩))
      refine ⟨fun B => if B = A then w else c B, ?_, ?_⟩
      · intro B hB D hD hBD hi
        by_cases hBA : B = A
        · subst B
          have hDA := Ne.symm hBD
          simpa only [if_pos rfl, if_true, if_neg hDA] using hne D (mem_erase.mpr ⟨hDA, hD⟩) hi
        by_cases hDA : D = A
        · subst D
          have hi' : (A ∩ B).Nonempty := by simpa only [Finset.inter_comm] using hi
          simpa only [if_pos rfl, if_true, if_neg hBA] using
            (hne B (mem_erase.mpr ⟨hBA, hB⟩) hi').symm
        simpa only [if_neg hBA, if_neg hDA] using
          hc B (mem_erase.mpr ⟨hBA, hB⟩) D (mem_erase.mpr ⟨hDA, hD⟩) hBD hi
      · intro B hB
        by_cases hBA : B = A
        · subst B; simpa using (mem_sdiff.mp hw).1
        · simpa only [if_neg hBA] using hcL B (mem_erase.mpr ⟨hBA, hB⟩)
    · exact ⟨fun _ => ⟨0, hm⟩, fun A hA => (hH ⟨A, hA⟩).elim, fun A hA => (hH ⟨A, hA⟩).elim⟩

/-- Neighbourhood bound in a hypergraph of maximum degree D. -/
theorem nbhd_le {n : ℕ} (H : Finset (Finset (Fin n))) (D : ℕ) (A : Finset (Fin n)) (hA : A ∈ H)
    (hdeg : ∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) :
    ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * (D - 1) := by
  apply meet_le
  intro i hi
  have : (H.erase A).filter (fun B => i ∈ B) = (H.filter (fun B => i ∈ B)).erase A := by
    ext B; simp [mem_filter, mem_erase]; tauto
  rw [this, Finset.card_erase_of_mem (mem_filter.mpr ⟨hA, hi⟩)]
  have := hdeg i
  omega

/-- The case q = 1 (rank at most 2): greedy works with lists of size 2D. -/
theorem case_one : ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
    ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ 2 * 1) →
      (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) → (∀ A ∈ H, D + D / 1 ≤ (L A).card) →
      ∃ c : Finset (Fin n) → Fin m,
        (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  refine ⟨1, fun n D m hD hm H L _ hsize hdeg hL => greedy H L hm ?_⟩
  intro A hA
  have h1 := nbhd_le H D A hA hdeg
  have h2 := hsize A hA
  have h3 := hL A hA
  rw [Nat.div_one] at h3
  have h4 : A.card * (D - 1) ≤ 2 * (D - 1) := Nat.mul_le_mul_right _ h2.2
  omega

/-- A bipartite matching principle, with one demand vertex and at most r resource
vertices per edge. Edges are indexed, and codegrees count indices. -/

theorem greedy_residual {n m r d : ℕ} (hm : 0 < m) (K : Finset (Finset (Fin n)))
    (R : Finset (Fin n) → Finset (Fin m))
    (hsize : ∀ A ∈ K, A.card ≤ r)
    (hdeg : ∀ v, (K.filter (fun A => v ∈ A)).card ≤ d)
    (hR : ∀ A ∈ K, r * (d - 1) < (R A).card) :
    ∃ c : Finset (Fin n) → Fin m,
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ K, c A ∈ R A := by
  apply greedy K R hm
  intro A hA
  exact ((nbhd_le K d A hA hdeg).trans (Nat.mul_le_mul_right _ (hsize A hA))).trans_lt (hR A hA)

/-- A colouring of the already covered edges extends if the unused lists are
large enough for the maximum degree of the uncovered edges. -/
theorem finish_with_reserve {n m r d : ℕ} (hm : 0 < m) (H K : Finset (Finset (Fin n)))
    (L R : Finset (Fin n) → Finset (Fin m)) (c : Finset (Fin n) → Fin m)
    (hproper : ∀ A ∈ H \ K, ∀ B ∈ H \ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)
    (hc : ∀ A ∈ H \ K, c A ∈ L A)
    (hsize : ∀ A ∈ K, A.card ≤ r)
    (hdeg : ∀ v, (K.filter (fun A => v ∈ A)).card ≤ d)
    (hR : ∀ A ∈ K, r * (d - 1) < (R A).card ∧ R A ⊆ L A)
    (hfree : ∀ A ∈ K, ∀ B ∈ H \ K, (A ∩ B).Nonempty → c B ∉ R A) :
    ∃ f : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → f A ≠ f B) ∧ ∀ A ∈ H, f A ∈ L A := by
  obtain ⟨g, hg, hgR⟩ := greedy_residual hm K R hsize hdeg (fun A hA => (hR A hA).1)
  refine ⟨fun A => if A ∈ K then g A else c A, ?_, ?_⟩
  · intro A hA B hB hAB hi
    by_cases hAK : A ∈ K <;> by_cases hBK : B ∈ K <;> simp only [hAK, hBK, if_true, if_false]
    · exact hg A hAK B hBK hAB hi
    · exact fun he => hfree A hAK B (mem_sdiff.mpr ⟨hB, hBK⟩) hi (he ▸ hgR A hAK)
    · have hi' : (B ∩ A).Nonempty := by simpa only [Finset.inter_comm] using hi
      exact fun he => hfree B hBK A (mem_sdiff.mpr ⟨hA, hAK⟩) hi' (he.symm ▸ hgR B hBK)
    · exact hproper A (mem_sdiff.mpr ⟨hA, hAK⟩) B (mem_sdiff.mpr ⟨hB, hBK⟩) hAB hi
  · intro A hA
    by_cases hAK : A ∈ K
    · simpa only [if_pos hAK] using (hR A hAK).2 (hgR A hAK)
    · simpa only [if_neg hAK] using hc A (mem_sdiff.mpr ⟨hA, hAK⟩)

theorem arith_finish (q s D R : ℕ) (hq : 0 < q) (hs : 0 < s) (hD : 1 ≤ D) (hR : D ≤ s * R) :
    2 * q * (D / (2 * q * s) - 1) < R := by
  have hk : 0 < 2 * q * s := by positivity
  have ht : D / (2 * q * s) * (2 * q * s) ≤ D := Nat.div_mul_le_self _ _
  set t := D / (2 * q * s)
  have h1 : (2 * q * t) * s ≤ R * s := by nlinarith
  have h2 : 2 * q * t ≤ R := Nat.le_of_mul_le_mul_right h1 hs
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · rw [h0]; simp
    rcases Nat.eq_zero_or_pos R with hR0 | hR0
    · rw [hR0] at hR; omega
    · exact hR0
  · have : 2 * q * (t - 1) + 2 * q = 2 * q * t := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

/-- Nibble on regular hypergraphs (Kahn 1996, wasteful nibble with a constant number of rounds):
a partial proper list colouring whose uncoloured edges K have maximum degree at most D / k, while
every uncoloured edge keeps at least D / s colours of its list unused by its coloured neighbours,
where s depends only on q (not on k). -/
def H1 : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∃ s : ℕ, 0 < s ∧ ∀ k : ℕ, 0 < k → ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D →
    ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ 2 * q) →
      (∀ i, (H.filter (fun A => i ∈ A)).card = D) → (∀ A ∈ H, D + D / q ≤ (L A).card) →
      ∃ K ⊆ H, ∃ c : Finset (Fin n) → Fin m,
        (∀ A ∈ H \ K, ∀ B ∈ H \ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧
        (∀ A ∈ H \ K, c A ∈ L A) ∧
        (∀ i, k * (K.filter (fun A => i ∈ A)).card ≤ D) ∧
        ∀ A ∈ K, D ≤ s * ((L A).filter
          (fun x => ∀ B ∈ H \ K, (A ∩ B).Nonempty → c B ≠ x)).card

/-- Regularisation: a linear hypergraph with edge sizes in [2, r] and maximum degree at most D
embeds into one with the same properties in which every vertex has degree exactly D. -/
def H2 : Prop :=
  ∀ r D n : ℕ, 2 ≤ r → ∀ H : Finset (Finset (Fin n)),
    (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r) →
    (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) →
    ∃ n' : ℕ, ∃ f : Fin n ↪ Fin n', ∃ H' : Finset (Finset (Fin n')),
      (∀ A ∈ H, A.map f ∈ H') ∧
      (∀ A ∈ H', ∀ B ∈ H', A ≠ B → (A ∩ B).card ≤ 1) ∧
      (∀ A ∈ H', 2 ≤ A.card ∧ A.card ≤ r) ∧
      ∀ i, (H'.filter (fun A => i ∈ A)).card = D

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1 := by
  intro h1 h2
  unfold OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1
  intro q hq
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have : q = 1 := by omega
    subst this
    exact case_one
  classical
  obtain ⟨s, hs, hk⟩ := h1 q hq2
  obtain ⟨D₀, hD₀⟩ := hk (2 * q * s) (by positivity)
  refine ⟨max D₀ 1, ?_⟩
  intro n D m hD hm H L hlin hsize hdeg hL
  have hD0 : D₀ ≤ D := le_trans (le_max_left _ _) hD
  have hD1 : 1 ≤ D := le_trans (le_max_right _ _) hD
  by_cases hH : H = ∅
  · subst hH
    exact ⟨fun _ => ⟨0, hm⟩, by simp, by simp⟩
  obtain ⟨A₀, hA₀⟩ := Finset.nonempty_iff_ne_empty.mpr hH
  have hmD : D + D / q ≤ m := by
    have := (hL A₀ hA₀).trans (Finset.card_le_univ (L A₀))
    simpa using this
  obtain ⟨n', f, H', hmap, hlin', hsize', hreg⟩ := h2 (2 * q) D n (by omega) H hlin hsize hdeg
  have hpre : ∀ A : Finset (Fin n), (A.map f).preimage f f.injective.injOn = A := by
    intro A; ext x; simp
  let L' : Finset (Fin n') → Finset (Fin m) := fun B =>
    if B.preimage f f.injective.injOn ∈ H ∧ (B.preimage f f.injective.injOn).map f = B
    then L (B.preimage f f.injective.injOn) else univ
  have hL'map : ∀ A ∈ H, L' (A.map f) = L A := by
    intro A hA
    simp [L', hpre A, hA]
  have hL' : ∀ B ∈ H', D + D / q ≤ (L' B).card := by
    intro B _
    simp only [L']
    split_ifs with h
    · exact hL _ h.1
    · simpa using hmD
  obtain ⟨K', hK', c', hprop', hcL', hdegK', hfree'⟩ :=
    hD₀ n' D m hD0 H' L' hlin' hsize' hreg hL'
  have hmapinj : ∀ A B : Finset (Fin n), A.map f = B.map f → A = B :=
    fun A B h => Finset.map_injective f h
  have hmapne : ∀ A B : Finset (Fin n), (A ∩ B).Nonempty → (A.map f ∩ B.map f).Nonempty := by
    intro A B ⟨x, hx⟩
    exact ⟨f x, by rw [← Finset.map_inter]; exact Finset.mem_map_of_mem f hx⟩
  let K := H.filter (fun A => A.map f ∈ K')
  let c : Finset (Fin n) → Fin m := fun A => c' (A.map f)
  have hdiff : ∀ A ∈ H \ K, A.map f ∈ H' \ K' := by
    intro A hA
    obtain ⟨hAH, hAK⟩ := mem_sdiff.mp hA
    refine mem_sdiff.mpr ⟨hmap A hAH, fun h => hAK (mem_filter.mpr ⟨hAH, h⟩)⟩
  let R : Finset (Fin n) → Finset (Fin m) := fun A =>
    (L A).filter (fun x => ∀ B ∈ H \ K, (A ∩ B).Nonempty → c B ≠ x)
  apply finish_with_reserve (r := 2 * q) (d := D / (2 * q * s)) hm H K L R c
  · intro A hA B hB hAB hi
    exact hprop' _ (hdiff A hA) _ (hdiff B hB) (fun h => hAB (hmapinj A B h)) (hmapne A B hi)
  · intro A hA
    have := hcL' _ (hdiff A hA)
    rwa [hL'map A (mem_sdiff.mp hA).1] at this
  · intro A hA
    exact (hsize A (mem_filter.mp hA).1).2
  · intro v
    rw [Nat.le_div_iff_mul_le (by positivity), Nat.mul_comm]
    refine le_trans (Nat.mul_le_mul_left _ ?_) (hdegK' (f v))
    apply Finset.card_le_card_of_injOn (fun A => A.map f)
    · intro A hA
      obtain ⟨hAK, hvA⟩ := mem_filter.mp hA
      exact mem_filter.mpr ⟨(mem_filter.mp hAK).2, Finset.mem_map_of_mem f hvA⟩
    · intro A _ B _ h
      exact hmapinj A B h
  · intro A hA
    obtain ⟨hAH, hAK⟩ := mem_filter.mp hA
    refine ⟨?_, filter_subset _ _⟩
    apply arith_finish q s D _ (by omega) hs hD1
    refine le_trans (hfree' _ hAK) (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    intro x hx
    rw [hL'map A hAH] at hx
    obtain ⟨hxL, hxf⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hxL, ?_⟩
    intro B hB hi
    exact hxf _ (hdiff B hB) (hmapne A B hi)
  · intro A _ B hB hi hcB
    exact (mem_filter.mp hcB).2 B hB hi rfl

end OMA.R_Erdos19_erdos_19_variants_kahn_R1_H1_R1
