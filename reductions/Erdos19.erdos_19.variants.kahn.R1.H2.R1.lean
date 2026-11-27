import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1

-- Reduction Erdos19.erdos_19.variants.kahn.R1.H2.R1 of step Erdos19.erdos_19.variants.kahn.R1.H2
-- Credit: @mucoucah
-- Ranks r <= 2 are greedy. For r >= 3: pad edges to r-uniform, regularize by layering
-- (r disjoint copies plus transversals of deficient points), then pass to the assignment
-- hypergraph (one (r+1)-edge per edge and colour: the edge vertex plus the r point-colour
-- slots), which is linear and D-regular. A matching that misses at most D/r edge vertices
-- through every point colours all but a max-degree-D/r subfamily with D colours; greedy
-- colours the rest with D more. H1/H2 are that locally covering matching (s odd / even).

namespace OMA.R_Erdos19_erdos_19_variants_kahn_R1_H2_R1

theorem greedy_color {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (hsymm : ∀ a b, R a b → R b a) (m k : ℕ) (hk : k < m) :
    ∀ H : Finset α, (∀ A ∈ H, (H.filter (fun B => B ≠ A ∧ R A B)).card ≤ k) →
    ∃ c : α → Fin m, ∀ A ∈ H, ∀ B ∈ H, A ≠ B → R A B → c A ≠ c B := by
  intro H
  induction H using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => ⟨0, by omega⟩, by simp⟩
  | insert a s ha ih =>
    intro hdeg
    obtain ⟨c, hc⟩ := ih (fun A hA => by
      refine le_trans (Finset.card_le_card ?_) (hdeg A (Finset.mem_insert_of_mem hA))
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_insert_of_mem hx.1, hx.2⟩)
    let N := (s.filter (fun B => R a B)).image c
    have hN : N.card < m := by
      have h1 : N.card ≤ (s.filter (fun B => R a B)).card := Finset.card_image_le
      have h2 : (s.filter (fun B => R a B)).card ≤ k := by
        refine le_trans (Finset.card_le_card ?_) (hdeg a (Finset.mem_insert_self a s))
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_insert_of_mem hx.1, fun h => ha (h ▸ hx.1), hx.2⟩
      omega
    have hex : ∃ x : Fin m, x ∉ N := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ : Finset (Fin m)) ⊆ N := fun x _ => hcon x
      have := Finset.card_le_card this
      simp at this
      omega
    obtain ⟨x, hx⟩ := hex
    refine ⟨Function.update c a x, ?_⟩
    intro A hA B hB hAB hR
    have hne : ∀ y ∈ s, y ≠ a := fun y hy h => ha (h ▸ hy)
    rcases Finset.mem_insert.1 hA with hAa | hA'
    · subst hAa
      rcases Finset.mem_insert.1 hB with hBa | hB'
      · exact absurd hBa.symm hAB
      · rw [Function.update_self, Function.update_of_ne (hne B hB')]
        intro h
        exact hx (Finset.mem_image.2 ⟨B, Finset.mem_filter.2 ⟨hB', hR⟩, h.symm⟩)
    · rcases Finset.mem_insert.1 hB with hBa | hB'
      · subst hBa
        rw [Function.update_self, Function.update_of_ne (hne A hA')]
        intro h
        exact hx (Finset.mem_image.2 ⟨A, Finset.mem_filter.2 ⟨hA', hsymm _ _ hR⟩, h⟩)
      · rw [Function.update_of_ne (hne A hA'), Function.update_of_ne (hne B hB')]
        exact hc A hA' B hB' hAB hR


theorem nbr_card_le {n D : ℕ} (H : Finset (Finset (Fin n)))
    (hdeg : ∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) (A : Finset (Fin n)) (hA : A ∈ H) :
    (H.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty)).card ≤ A.card * (D - 1) := by
  have hsub : H.filter (fun B => B ≠ A ∧ (A ∩ B).Nonempty) ⊆
      A.biUnion (fun i => (H.filter (fun B => i ∈ B)).erase A) := by
    intro B hB
    simp only [Finset.mem_filter] at hB
    obtain ⟨hBH, hBA, ⟨i, hi⟩⟩ := hB
    rw [Finset.mem_inter] at hi
    exact Finset.mem_biUnion.2 ⟨i, hi.1, Finset.mem_erase.2 ⟨hBA, Finset.mem_filter.2 ⟨hBH, hi.2⟩⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have : ∀ i ∈ A, ((H.filter (fun B => i ∈ B)).erase A).card ≤ D - 1 := by
    intro i hi
    rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hA, hi⟩)]
    have := hdeg i
    omega
  simpa using Finset.sum_le_sum this

theorem color_small_rank {n D r : ℕ} (H : Finset (Finset (Fin n)))
    (hrank : ∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r)
    (hdeg : ∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) (m : ℕ) (hm : r * (D - 1) < m) :
    ∃ c : Finset (Fin n) → Fin m,
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  refine greedy_color (fun A B : Finset (Fin n) => (A ∩ B).Nonempty)
    (fun a b h => by rwa [Finset.inter_comm]) m (r * (D - 1)) hm H ?_
  intro A hA
  exact le_trans (nbr_card_le H hdeg A hA) (Nat.mul_le_mul_right _ (hrank A hA).2)

open Finset
variable {α : Type*} [DecidableEq α]





omit [DecidableEq α] in
@[simp] theorem mem_copyEdge {r : ℕ} {i j : Fin r} {A : Finset α} {x : α} :
    (j, x) ∈ (Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (A)) ↔ i = j ∧ x ∈ A := by
  rw [Finset.mem_map]
  change (∃ a ∈ A, (i, a) = (j, x)) ↔ _
  simp [and_left_comm]

omit [DecidableEq α] in
@[simp] theorem mem_fillEdge {r : ℕ} {i : Fin r} {x y : α} :
    (i, y) ∈ ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, x), fun _ _ h => congrArg Prod.fst h⟩) ↔ x = y := by
  rw [Finset.mem_map]
  change (∃ a ∈ (univ : Finset (Fin r)), (a, x) = (i, y)) ↔ _
  simp

omit [DecidableEq α] in
@[simp] theorem card_copyEdge {r : ℕ} (i : Fin r) (A : Finset α) :
    ((Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (A))).card = A.card := card_map _

omit [DecidableEq α] in
@[simp] theorem card_fillEdge (r : ℕ) (x : α) :
    (((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, x), fun _ _ h => congrArg Prod.fst h⟩)).card = r := by simp

omit [DecidableEq α] in
theorem copyEdge_injective {r : ℕ} (i : Fin r) :
    Function.Injective ((fun (ζA : Finset α) => (Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (ζA)))) := by
  intro A B h
  exact Finset.map_injective _ h



theorem mem_layers {r : ℕ} {H : Finset (Finset α)} {A : Finset (Fin r × α)} :
    A ∈ ((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA))))) ↔ ∃ i B, B ∈ H ∧ (Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (B)) = A := by
  simp

theorem mem_fills [Fintype α] {r D : ℕ} {H : Finset (Finset α)}
    {A : Finset (Fin r × α)} :
    A ∈ ((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩)))) ↔ ∃ x, ((H).filter fun ζA => x ∈ ζA).card < D ∧ ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, x), fun _ _ h => congrArg Prod.fst h⟩) = A := by
  simp

theorem disjoint_layers_fills [Fintype α] {r : ℕ} (hr : 2 ≤ r)
    (D : ℕ) (H : Finset (Finset α)) : Disjoint (((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA)))))) (((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))))) := by
  rw [Finset.disjoint_left]
  intro A hA hA'
  obtain ⟨i, B, _, rfl⟩ := mem_layers.mp hA
  obtain ⟨x, _, hEq⟩ := mem_fills.mp hA'
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1, by omega⟩
  have hz : (z, x) ∈ (Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (B)) := hEq ▸ mem_fillEdge.mpr rfl
  have ho : (o, x) ∈ (Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (B)) := hEq ▸ mem_fillEdge.mpr rfl
  have he := (mem_copyEdge.mp hz).1.symm.trans (mem_copyEdge.mp ho).1
  have := congrArg Fin.val he
  simp [z, o] at this

theorem linear_layers_fills [Fintype α] {r D : ℕ} {H : Finset (Finset α)}
    (hH : (∀ ζA ∈ H, ∀ ζB ∈ H, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1)) : (∀ ζA ∈ (((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA))))) ∪ ((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))))), ∀ ζB ∈ (((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA))))) ∪ ((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))))), ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1) := by
  have cross (i : Fin r) (A : Finset α) (x : α) :
      ((Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (A)) ∩ ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, x), fun _ _ h => congrArg Prod.fst h⟩)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    rintro ⟨j, y⟩ hp ⟨k, z⟩ hq
    simp only [Finset.mem_inter, mem_copyEdge, mem_fillEdge] at hp hq
    exact Prod.ext (hp.1.1.symm.trans hq.1.1) (hp.2.symm.trans hq.2)
  intro A hA B hB hne
  rcases Finset.mem_union.mp hA with hA | hA <;> rcases Finset.mem_union.mp hB with hB | hB
  · obtain ⟨i, A, hA0, rfl⟩ := mem_layers.mp hA
    obtain ⟨j, B, hB0, rfl⟩ := mem_layers.mp hB
    apply Finset.card_le_one.mpr
    rintro ⟨k, x⟩ hp ⟨l, y⟩ hq
    simp only [Finset.mem_inter, mem_copyEdge] at hp hq
    have hij : i = j := hp.1.1.trans hp.2.1.symm
    subst j
    have hAB : A ≠ B := fun he => hne (congrArg ((fun ζA => (Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (ζA)))) he)
    exact Prod.ext (hp.1.1.symm.trans hq.1.1)
      (Finset.card_le_one.mp (hH A hA0 B hB0 hAB) x
        (Finset.mem_inter.mpr ⟨hp.1.2, hp.2.2⟩) y
        (Finset.mem_inter.mpr ⟨hq.1.2, hq.2.2⟩))
  · obtain ⟨i, A, _, rfl⟩ := mem_layers.mp hA
    obtain ⟨x, _, rfl⟩ := mem_fills.mp hB
    exact cross i A x
  · obtain ⟨x, _, rfl⟩ := mem_fills.mp hA
    obtain ⟨i, B, _, rfl⟩ := mem_layers.mp hB
    rw [Finset.inter_comm]
    exact cross i B x
  · obtain ⟨x, _, rfl⟩ := mem_fills.mp hA
    obtain ⟨y, _, rfl⟩ := mem_fills.mp hB
    apply Finset.card_le_one.mpr
    rintro ⟨i, z⟩ hp q hq
    simp only [Finset.mem_inter, mem_fillEdge] at hp
    exact False.elim (hne (congrArg ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))) (hp.1.trans hp.2.symm)))

theorem deg_layers {r : ℕ} (H : Finset (Finset α)) (i : Fin r) (x : α) :
    (((((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA))))))).filter fun ζA => (i, x) ∈ ζA).card = ((H).filter fun ζA => x ∈ ζA).card := by
  have heq : (((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA)))))).filter (fun A => (i, x) ∈ A) =
      (H.filter fun A => x ∈ A).image ((fun ζA => (Finset.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩ (ζA)))) := by
    ext A
    simp only [Finset.mem_filter, mem_layers, Finset.mem_image]
    constructor
    · rintro ⟨⟨j, B, hB, rfl⟩, hmem⟩
      obtain ⟨rfl, hx⟩ := mem_copyEdge.mp hmem
      exact ⟨B, ⟨hB, hx⟩, rfl⟩
    · rintro ⟨B, ⟨hB, hx⟩, rfl⟩
      exact ⟨⟨i, B, hB, rfl⟩, mem_copyEdge.mpr ⟨rfl, hx⟩⟩
  skip
  rw [heq, Finset.card_image_of_injective _ (copyEdge_injective i)]

theorem deg_fills [Fintype α] {r D : ℕ} (H : Finset (Finset α)) (i : Fin r) (x : α) :
    (((((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩)))))).filter fun ζA => (i, x) ∈ ζA).card = if ((H).filter fun ζA => x ∈ ζA).card < D then 1 else 0 := by
  skip
  have hm (A : Finset (Fin r × α)) :
      A ∈ (((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))))).filter (fun A => (i, x) ∈ A) ↔
        (H.filter fun A => x ∈ A).card < D ∧ A = ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, x), fun _ _ h => congrArg Prod.fst h⟩) := by
    simp only [Finset.mem_filter, mem_fills]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, him⟩
      simpa only [mem_fillEdge.mp him, and_true] using hy
    · rintro ⟨hx, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, mem_fillEdge.mpr rfl⟩
  split_ifs with hx
  · have heq : (((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))))).filter (fun A => (i, x) ∈ A) = {((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, x), fun _ _ h => congrArg Prod.fst h⟩)} := by
      ext A
      simp [hm, hx]
    simp [heq]
  · have heq : (((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))))).filter (fun A => (i, x) ∈ A) = ∅ := by
      ext A
      simp [hm, hx]
    simp [heq]

theorem deg_regular_step [Fintype α] {r : ℕ} (hr : 2 ≤ r)
    (D : ℕ) (H : Finset (Finset α)) (i : Fin r) (x : α) :
    (((((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA))))) ∪ ((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩)))))).filter fun ζA => (i, x) ∈ ζA).card =
      ((H).filter fun ζA => x ∈ ζA).card + if ((H).filter fun ζA => x ∈ ζA).card < D then 1 else 0 := by
  have hd := disjoint_layers_fills hr D H
  skip
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  · exact congrArg₂ (· + ·) (deg_layers H i x) (deg_fills H i x)
  · exact hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem uniform_layers_fills [Fintype α] {r D : ℕ} {H : Finset (Finset α)}
    (hH : ∀ A ∈ H, A.card = r) :
    ∀ A ∈ ((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA))))) ∪ ((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩)))), A.card = r := by
  intro A hA
  rcases Finset.mem_union.mp hA with hA | hA
  · obtain ⟨i, B, hB, rfl⟩ := mem_layers.mp hA
    simpa using hH B hB
  · obtain ⟨x, _, rfl⟩ := mem_fills.mp hA
    exact card_fillEdge r x

theorem linear_mapFamily {β : Type*} [DecidableEq β]
    (f : α ↪ β) {H : Finset (Finset α)} (hH : (∀ ζA ∈ H, ∀ ζB ∈ H, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1)) :
    (∀ ζA ∈ (H.image (Finset.map f)), ∀ ζB ∈ (H.image (Finset.map f)), ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1) := by
  intro A hA B hB hAB
  obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
  rw [← Finset.map_inter, Finset.card_map]
  exact hH A₀ hA₀ B₀ hB₀ (fun he => hAB (congrArg (Finset.map f) he))

theorem deg_mapFamily {β : Type*} [DecidableEq β]
    (f : α ↪ β) (H : Finset (Finset α)) (x : α) :
    (((H.image (Finset.map f))).filter fun ζA => (f x) ∈ ζA).card = ((H).filter fun ζA => x ∈ ζA).card := by
  skip
  rw [Finset.filter_image, Finset.card_image_of_injective _ (Finset.map_injective f)]
  simp [Finset.mem_map']

/-- Extend a uniform linear family to a regular uniform linear family. -/
theorem regularize (r D k : ℕ) (hr : 2 ≤ r) :
    ∀ {α : Type} [Fintype α] [DecidableEq α] (H : Finset (Finset α)),
    (∀ ζA ∈ H, ∀ ζB ∈ H, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1) → (∀ A ∈ H, A.card = r) →
    (∀ x, ((H).filter fun ζA => x ∈ ζA).card ≤ D ∧ D ≤ ((H).filter fun ζA => x ∈ ζA).card + k) →
    ∃ (N : ℕ) (f : α ↪ Fin N) (K : Finset (Finset (Fin N))),
      (∀ A ∈ H, A.map f ∈ K) ∧ (∀ ζA ∈ K, ∀ ζB ∈ K, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1) ∧
      (∀ A ∈ K, A.card = r) ∧ (∀ x, ((K).filter fun ζA => x ∈ ζA).card = D) := by
  induction k with
  | zero =>
    intro α _ _ H hlin hu hd
    let e := Fintype.equivFin α
    let K := H.image (Finset.map e.toEmbedding)
    refine ⟨Fintype.card α, e.toEmbedding, K, ?_, linear_mapFamily _ hlin, ?_, ?_⟩
    · intro A hA
      exact Finset.mem_image_of_mem _ hA
    · intro A hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      simpa using hu B hB
    · intro x
      obtain ⟨x, rfl⟩ := e.surjective x
      change ((K).filter fun ζA => (e.toEmbedding x) ∈ ζA).card = D
      rw [deg_mapFamily]
      have := hd x
      omega
  | succ k ih =>
    intro α _ _ H hlin hu hd
    let L := ((univ : Finset (Fin r)).biUnion fun ζi => (H).image ((fun ζA => (Finset.map ⟨Prod.mk ζi, fun _ _ h => congrArg Prod.snd h⟩ (ζA))))) ∪ ((univ.filter fun ζx => ((H).filter fun ζA => ζx ∈ ζA).card < D).image ((fun ζx => ((univ : Finset (Fin r)).map ⟨fun ζi => (ζi, ζx), fun _ _ h => congrArg Prod.fst h⟩))))
    have hd' : ∀ v, ((L).filter fun ζA => v ∈ ζA).card ≤ D ∧ D ≤ ((L).filter fun ζA => v ∈ ζA).card + k := by
      rintro ⟨i, x⟩
      rw [deg_regular_step hr]
      have := hd x
      split_ifs <;> omega
    obtain ⟨N, f, K, hf, hlin', hu', hd''⟩ :=
      ih L (linear_layers_fills hlin) (uniform_layers_fills hu) hd'
    let i : Fin r := ⟨0, by omega⟩
    let g : α ↪ Fin r × α := ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩
    refine ⟨N, g.trans f, K, ?_, hlin', hu', hd''⟩
    intro A hA
    rw [← Finset.map_map]
    apply hf
    exact Finset.mem_union_left _ (mem_layers.mpr ⟨i, A, hA, rfl⟩)



@[simp] theorem inl_mem_padEdge {r : ℕ} {A : Finset α} {x : α} :
    Sum.inl x ∈ (Finset.map Function.Embedding.inl (A) ∪ ((univ : Finset (Fin (r - (A).card))).map ⟨fun ζi => Sum.inr (A, Fin.castLE (Nat.sub_le r (A).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)) ↔ x ∈ A := by
  rw [Finset.mem_union, Finset.mem_map, Finset.mem_map]
  change (∃ a ∈ A, Sum.inl a = Sum.inl x) ∨
    (∃ i ∈ (univ : Finset (Fin (r - A.card))),
      Sum.inr (A, Fin.castLE (Nat.sub_le r A.card) i) = Sum.inl x) ↔ _
  simp

theorem eq_of_inr_mem_padEdge {r : ℕ} {A B : Finset α} {j : Fin r}
    (h : Sum.inr (B, j) ∈ (Finset.map Function.Embedding.inl (A) ∪ ((univ : Finset (Fin (r - (A).card))).map ⟨fun ζi => Sum.inr (A, Fin.castLE (Nat.sub_le r (A).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))) : A = B := by
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
    exact (Sum.inl_ne_inr ha).elim
  · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
    exact congrArg Prod.fst (Sum.inr.inj hi)

theorem card_padEdge {r : ℕ} {A : Finset α} (hA : A.card ≤ r) :
    ((Finset.map Function.Embedding.inl (A) ∪ ((univ : Finset (Fin (r - (A).card))).map ⟨fun ζi => Sum.inr (A, Fin.castLE (Nat.sub_le r (A).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))).card = r := by
  have hd : Disjoint (A.map (Function.Embedding.inl (β := Finset α × Fin r)))
      (((univ : Finset (Fin (r - (A).card))).map ⟨fun ζi => Sum.inr (A, Fin.castLE (Nat.sub_le r (A).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)) := by
    rw [Finset.disjoint_left]
    rintro (x | ⟨B, j⟩) hx hy
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hy
      exact Sum.inr_ne_inl hi
    · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx
      exact Sum.inl_ne_inr ha
  rw [Finset.card_union_of_disjoint hd]
  simp [Nat.add_sub_of_le hA]

theorem padEdge_injective (r : ℕ) : Function.Injective ((fun (ζA : Finset α) => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)))) := by
  intro A B h
  ext x
  have hm : Sum.inl x ∈ (Finset.map Function.Embedding.inl (A) ∪ ((univ : Finset (Fin (r - (A).card))).map ⟨fun ζi => Sum.inr (A, Fin.castLE (Nat.sub_le r (A).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)) ↔ Sum.inl x ∈ (Finset.map Function.Embedding.inl (B) ∪ ((univ : Finset (Fin (r - (B).card))).map ⟨fun ζi => Sum.inr (B, Fin.castLE (Nat.sub_le r (B).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)) := by beta_reduce at h; rw [h]
  simpa using hm

theorem linear_padded {r : ℕ} {H : Finset (Finset α)} (hH : (∀ ζA ∈ H, ∀ ζB ∈ H, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1)) :
    (∀ ζA ∈ (H.image ((fun ζA => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))))), ∀ ζB ∈ (H.image ((fun ζA => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))))), ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1) := by
  intro A hA B hB hne
  obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
  have hne₀ : A₀ ≠ B₀ := fun he => hne (congrArg ((fun ζA => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)))) he)
  have hshared {v : α ⊕ (Finset α × Fin r)}
      (hv : v ∈ (Finset.map Function.Embedding.inl (A₀) ∪ ((univ : Finset (Fin (r - (A₀).card))).map ⟨fun ζi => Sum.inr (A₀, Fin.castLE (Nat.sub_le r (A₀).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)) ∩ (Finset.map Function.Embedding.inl (B₀) ∪ ((univ : Finset (Fin (r - (B₀).card))).map ⟨fun ζi => Sum.inr (B₀, Fin.castLE (Nat.sub_le r (B₀).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))) : ∃ x ∈ A₀ ∩ B₀, v = Sum.inl x := by
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
    rcases v with x | ⟨C, j⟩
    · exact ⟨x, Finset.mem_inter.mpr ⟨inl_mem_padEdge.mp h1, inl_mem_padEdge.mp h2⟩, rfl⟩
    · exact (hne₀ ((eq_of_inr_mem_padEdge h1).trans (eq_of_inr_mem_padEdge h2).symm)).elim
  apply Finset.card_le_one.mpr
  intro v hv w hw
  obtain ⟨x, hx, rfl⟩ := hshared hv
  obtain ⟨y, hy, rfl⟩ := hshared hw
  exact congrArg Sum.inl (Finset.card_le_one.mp (hH A₀ hA₀ B₀ hB₀ hne₀) x hx y hy)

theorem deg_padded_inl (r : ℕ) (H : Finset (Finset α)) (x : α) :
    (((H.image ((fun ζA => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)))))).filter fun ζA => (Sum.inl x) ∈ ζA).card = ((H).filter fun ζA => x ∈ ζA).card := by
  skip
  rw [Finset.filter_image, Finset.card_image_of_injective _ (padEdge_injective r)]
  simp

theorem deg_padded_inr_le_one {r : ℕ} (H : Finset (Finset α)) (B : Finset α) (j : Fin r) :
    (((H.image ((fun ζA => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)))))).filter fun ζA => (Sum.inr (B, j)) ∈ ζA).card ≤ 1 := by
  skip
  apply Finset.card_le_one.mpr
  have heq (A) (hA : A ∈ (H.image ((fun ζA => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))))).filter (fun A => Sum.inr (B, j) ∈ A)) :
      A = (Finset.map Function.Embedding.inl (B) ∪ ((univ : Finset (Fin (r - (B).card))).map ⟨fun ζi => Sum.inr (B, Fin.castLE (Nat.sub_le r (B).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩)) := by
    obtain ⟨hA, hm⟩ := Finset.mem_filter.mp hA
    obtain ⟨A₀, _, rfl⟩ := Finset.mem_image.mp hA
    rw [eq_of_inr_mem_padEdge hm]
  exact fun A hA C hC => (heq A hA).trans (heq C hC).symm

/-- Bounded rank and maximum degree reduce to uniform regular instances. -/
theorem color_from_uniform_regular {r D m : ℕ} (hr : 2 ≤ r) (hD : 1 ≤ D)
    (hcolor : ∀ N (K : Finset (Finset (Fin N))), (∀ ζA ∈ K, ∀ ζB ∈ K, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1) →
      (∀ A ∈ K, A.card = r) → (∀ x, ((K).filter fun ζA => x ∈ ζA).card = D) →
      ∃ c : Finset (Fin N) → Fin m,
        ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B)
    {n : ℕ} (H : Finset (Finset (Fin n))) (hlin : (∀ ζA ∈ H, ∀ ζB ∈ H, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1))
    (hrank : ∀ A ∈ H, A.card ≤ r) (hdeg : ∀ x, ((H).filter fun ζA => x ∈ ζA).card ≤ D) :
    ∃ c : Finset (Fin n) → Fin m,
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  let J := H.image ((fun ζA => (Finset.map Function.Embedding.inl (ζA) ∪ ((univ : Finset (Fin (r - (ζA).card))).map ⟨fun ζi => Sum.inr (ζA, Fin.castLE (Nat.sub_le r (ζA).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))))
  have hu : ∀ A ∈ J, A.card = r := by
    intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
    exact card_padEdge (hrank A₀ hA₀)
  have hd : ∀ x, ((J).filter fun ζA => x ∈ ζA).card ≤ D ∧ D ≤ ((J).filter fun ζA => x ∈ ζA).card + D := by
    intro x
    refine ⟨?_, by omega⟩
    rcases x with x | ⟨B, j⟩
    · rw [deg_padded_inl]
      exact hdeg x
    · exact (deg_padded_inr_le_one H B j).trans hD
  obtain ⟨N, f, K, hf, hlin', hu', hd'⟩ :=
    regularize r D D hr J (linear_padded hlin) hu hd
  obtain ⟨c, hc⟩ := hcolor N K hlin' hu' hd'
  refine ⟨fun A => c (((Finset.map Function.Embedding.inl (A) ∪ ((univ : Finset (Fin (r - (A).card))).map ⟨fun ζi => Sum.inr (A, Fin.castLE (Nat.sub_le r (A).card) ζi), fun _ _ h => Fin.ext <| congrArg (fun p : Finset _ × Fin r => p.2.val) (Sum.inr.inj h)⟩))).map f), ?_⟩
  intro A hA B hB hne hmeet
  apply hc _ (hf _ (Finset.mem_image_of_mem _ hA)) _ (hf _ (Finset.mem_image_of_mem _ hB))
  · exact fun he => hne (padEdge_injective r (Finset.map_injective f he))
  · obtain ⟨x, hx⟩ := hmeet
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
    exact ⟨f (Sum.inl x), Finset.mem_inter.mpr
      ⟨Finset.mem_map_of_mem f (inl_mem_padEdge.mpr hxA),
        Finset.mem_map_of_mem f (inl_mem_padEdge.mpr hxB)⟩⟩



@[simp] theorem inl_mem_assignmentEdge {H : Finset (Finset α)} {D : ℕ}
    {A B : H} {j : Fin D} :
    Sum.inl B ∈ (insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val)) ↔ B = A := by
  rw [Finset.mem_insert, Finset.mem_map]
  change Sum.inl B = Sum.inl A ∨ (∃ x ∈ A.val, Sum.inr (x, j) = Sum.inl B) ↔ _
  simp

@[simp] theorem inr_mem_assignmentEdge {H : Finset (Finset α)} {D : ℕ}
    {A : H} {j k : Fin D} {x : α} :
    Sum.inr (x, k) ∈ (insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val)) ↔ k = j ∧ x ∈ A.val := by
  rw [Finset.mem_insert, Finset.mem_map]
  change Sum.inr (x, k) = Sum.inl A ∨
    (∃ y ∈ A.val, Sum.inr (y, j) = Sum.inr (x, k)) ↔ _
  simp only [Sum.inr_ne_inl, false_or, Sum.inr.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, rfl, hjk⟩
    exact ⟨hjk.symm, hy⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, hx, rfl, rfl⟩

theorem card_assignmentEdge {H : Finset (Finset α)} {D : ℕ} (A : H) (j : Fin D) :
    ((insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val))).card = A.val.card + 1 := by
  skip
  rw [Finset.card_insert_of_notMem, Finset.card_map]
  rintro h
  obtain ⟨x, _, hx⟩ := Finset.mem_map.mp h
  exact Sum.inr_ne_inl hx

theorem assignmentEdge_injective {H : Finset (Finset α)} {D : ℕ}
    (hH : ∀ A ∈ H, A.Nonempty) :
    Function.Injective (fun p : H × Fin D => (insert (Sum.inl p.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, p.2) : type_of% p.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (p.1).val))) := by
  rintro ⟨A, j⟩ ⟨B, k⟩ h
  change (insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val)) = (insert (Sum.inl B) (Finset.map ⟨fun ζx => (Sum.inr (ζx, k) : type_of% B ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (B).val)) at h
  have hA : Sum.inl A ∈ (insert (Sum.inl B) (Finset.map ⟨fun ζx => (Sum.inr (ζx, k) : type_of% B ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (B).val)) := h ▸ inl_mem_assignmentEdge.mpr rfl
  have hAB := inl_mem_assignmentEdge.mp hA
  subst B
  obtain ⟨x, hx⟩ := hH A.val A.prop
  have hj : Sum.inr (x, j) ∈ (insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, k) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val)) := h ▸ inr_mem_assignmentEdge.mpr ⟨rfl, hx⟩
  exact Prod.ext rfl (inr_mem_assignmentEdge.mp hj).1


theorem mem_assignments {H : Finset (Finset α)} {D : ℕ} {E : Finset (((↥(H)) ⊕ (α × Fin D)))} :
    E ∈ ((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val)))) ↔ ∃ (A : H) (j : Fin D), (insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val)) = E := by
  simp [Prod.exists]

theorem linear_assignments {H : Finset (Finset α)} (hH : (∀ ζA ∈ H, ∀ ζB ∈ H, ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1)) (D : ℕ) :
    (∀ ζA ∈ (((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))), ∀ ζB ∈ (((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))), ζA ≠ ζB → (ζA ∩ ζB).card ≤ 1) := by
  intro E hE F hF hne
  obtain ⟨A, j, rfl⟩ := mem_assignments.mp hE
  obtain ⟨B, k, rfl⟩ := mem_assignments.mp hF
  apply Finset.card_le_one.mpr
  rintro (C | ⟨x, l⟩) hp (C' | ⟨y, m⟩) hq
  · simp only [Finset.mem_inter, inl_mem_assignmentEdge] at hp hq
    exact congrArg Sum.inl (hp.1.trans hq.1.symm)
  · simp only [Finset.mem_inter, inl_mem_assignmentEdge] at hp
    simp only [Finset.mem_inter, inr_mem_assignmentEdge] at hq
    exact (hne (congrArg₂ (fun ζa ζb => (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζb) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val))) (hp.1.symm.trans hp.2)
      (hq.1.1.symm.trans hq.2.1))).elim
  · simp only [Finset.mem_inter, inr_mem_assignmentEdge] at hp
    simp only [Finset.mem_inter, inl_mem_assignmentEdge] at hq
    exact (hne (congrArg₂ (fun ζa ζb => (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζb) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val))) (hq.1.symm.trans hq.2)
      (hp.1.1.symm.trans hp.2.1))).elim
  · simp only [Finset.mem_inter, inr_mem_assignmentEdge] at hp hq
    have hjk : j = k := hp.1.1.symm.trans hp.2.1
    have hAB : A.val ≠ B.val := fun h => hne (congrArg₂ (fun ζa ζb => (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζb) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val))) (Subtype.ext h) hjk)
    have hxy := Finset.card_le_one.mp (hH A.val A.prop B.val B.prop hAB) x
      (Finset.mem_inter.mpr ⟨hp.1.2, hp.2.2⟩) y
      (Finset.mem_inter.mpr ⟨hq.1.2, hq.2.2⟩)
    exact congrArg Sum.inr (Prod.ext hxy (hp.1.1.trans hq.1.1.symm))

theorem deg_assignments_inl {H : Finset (Finset α)} {D : ℕ}
    (hH : ∀ A ∈ H, A.Nonempty) (A : H) :
    (((((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val)))))).filter fun ζA => (Sum.inl A) ∈ ζA).card = D := by
  have heq : (((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))).filter (fun E => Sum.inl A ∈ E) =
      univ.image ((fun ζj => (insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val)))) := by
    ext E
    simp only [Finset.mem_filter, mem_assignments, Finset.mem_image, Prod.exists, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨B, j, rfl⟩, h⟩
      obtain rfl := inl_mem_assignmentEdge.mp h
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨A, j, rfl⟩, inl_mem_assignmentEdge.mpr rfl⟩
  skip
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact congrArg Prod.snd (assignmentEdge_injective hH
      (a₁ := (A, j)) (a₂ := (A, k)) h)


theorem card_incident (H : Finset (Finset α)) (x : α) :
    (((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).card = ((H).filter fun ζA => x ∈ ζA).card := by
  have heq : (((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).image Subtype.val = H.filter (fun A => x ∈ A) := by
    ext A
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨B, hx, rfl⟩
      exact ⟨B.prop, hx⟩
    · rintro ⟨hA, hx⟩
      exact ⟨⟨A, hA⟩, hx, rfl⟩
  skip
  rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]

theorem deg_assignments_inr {H : Finset (Finset α)} {D : ℕ}
    (hH : ∀ A ∈ H, A.Nonempty) (x : α) (j : Fin D) :
    (((((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val)))))).filter fun ζA => (Sum.inr (x, j)) ∈ ζA).card = ((H).filter fun ζA => x ∈ ζA).card := by
  have heq : (((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))).filter (fun E => Sum.inr (x, j) ∈ E) =
      (((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).image (fun A => (insert (Sum.inl A) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% A ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (A).val))) := by
    ext E
    simp only [Finset.mem_filter, mem_assignments, Finset.mem_image, Prod.exists, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨A, k, rfl⟩, h⟩
      obtain ⟨rfl, hx⟩ := inr_mem_assignmentEdge.mp h
      exact ⟨A, hx, rfl⟩
    · rintro ⟨A, hx, rfl⟩
      exact ⟨⟨A, j, rfl⟩, inr_mem_assignmentEdge.mpr ⟨rfl, hx⟩⟩
  skip
  rw [heq, Finset.card_image_of_injective]
  · exact card_incident H x
  · intro A B h
    exact congrArg Prod.fst (assignmentEdge_injective hH
      (a₁ := (A, j)) (a₂ := (B, j)) h)


@[simp] theorem inl_mem_target {H : Finset (Finset α)} {D : ℕ} {A : H} {x : α} :
    (Sum.inl A : ((↥(H)) ⊕ (α × Fin D))) ∈ ((((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).map (Function.Embedding.inl (β := α × Fin D))) ↔ x ∈ A.val := by
  change Function.Embedding.inl A ∈ (((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).map Function.Embedding.inl ↔ _
  rw [Finset.mem_map']
  simp

@[simp] theorem inr_not_mem_target {H : Finset (Finset α)} {D : ℕ} {x y : α} {j : Fin D} :
    Sum.inr (y, j) ∉ ((((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).map (Function.Embedding.inl (β := α × Fin D))) := by
  intro h
  obtain ⟨A, _, hA⟩ := Finset.mem_map.mp h
  exact Sum.inl_ne_inr hA

theorem card_target (H : Finset (Finset α)) (D : ℕ) (x : α) :
    (((((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).map (Function.Embedding.inl (β := α × Fin D)))).card = ((H).filter fun ζA => x ∈ ζA).card := by
  rw [Finset.card_map, card_incident]

theorem deg_targets_le [Fintype α] {H : Finset (Finset α)} {D r : ℕ}
    (hr : ∀ A ∈ H, A.card ≤ r) (x : ((↥(H)) ⊕ (α × Fin D))) :
    (((univ.image ((fun ζx => ((((univ : Finset ↥(H)).filter (fun ζA => ζx ∈ ζA.val))).map (Function.Embedding.inl (β := α × Fin D))))))).filter fun ζA => x ∈ ζA).card ≤ r := by
  skip
  rw [Finset.filter_image]
  refine Finset.card_image_le.trans ?_
  rcases x with A | ⟨x, j⟩
  · simpa using hr A.val A.prop
  · simp



theorem mem_cover_iff {H : Finset (Finset α)} {D : ℕ}
    {M : Finset (Finset (((↥(H)) ⊕ (α × Fin D))))} (hM : M ⊆ ((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))) (a : H) :
    Sum.inl a ∈ M.biUnion id ↔ (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = a.val ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M) := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨E, hE, hm⟩
    obtain ⟨b, j, rfl⟩ := mem_assignments.mp (hM hE)
    have hab : a = b := inl_mem_assignmentEdge.mp hm
    subst b
    exact ⟨j, a, rfl, hE⟩
  · rintro ⟨j, b, hb, hm⟩
    exact ⟨(insert (Sum.inl b) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% b ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (b).val)), hm, inl_mem_assignmentEdge.mpr (Subtype.ext hb.symm)⟩

open scoped Classical in
theorem deg_unassigned {H : Finset (Finset α)} {D : ℕ}
    {M : Finset (Finset (((↥(H)) ⊕ (α × Fin D))))} (hM : M ⊆ ((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))) (x : α) :
    (((H.filter fun A => ¬ (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = A ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M))).filter fun ζA => x ∈ ζA).card =
      (((((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).map (Function.Embedding.inl (β := α × Fin D))) \ M.biUnion id).card := by
  let t := univ.filter (fun a : H => x ∈ a.val ∧ ¬ (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = a.val ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M))
  have hleft : t.image Subtype.val = (H.filter fun A => ¬ (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = A ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M)).filter
      (fun A => x ∈ A) := by
    ext A
    simp only [t, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ⟨hx, hna⟩, rfl⟩
      exact ⟨⟨a.prop, hna⟩, hx⟩
    · rintro ⟨⟨hA, hnA⟩, hx⟩
      exact ⟨⟨A, hA⟩, ⟨hx, hnA⟩, rfl⟩
  have hright : t.map Function.Embedding.inl = ((((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).map (Function.Embedding.inl (β := α × Fin D))) \ M.biUnion id := by
    ext v
    rcases v with a | ⟨y, j⟩
    · change Function.Embedding.inl a ∈ t.map Function.Embedding.inl ↔ _
      simp [t, mem_cover_iff hM]
    · simp only [Finset.mem_sdiff, inr_not_mem_target, false_and, iff_false]
      intro h
      obtain ⟨A, _, hA⟩ := Finset.mem_map.mp h
      exact Sum.inl_ne_inr hA
  skip
  rw [← hleft, ← hright, Finset.card_map, Finset.card_image_of_injective _ Subtype.val_injective]

/-- Color the matched (fun ζH ζD => ((univ : Finset (↥(ζH) × Fin ζD)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))), and greedily color the remainder with a second palette. -/
theorem color_from_assignment_matching {n r D : ℕ} (hr : 0 < r) (hD : 0 < D)
    (H : Finset (Finset (Fin n))) (hrank : ∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r)
    (M : Finset (Finset (((↥(H)) ⊕ (Fin n × Fin D))))) (hsub : M ⊆ ((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val)))))
    (hM : (∀ ζE ∈ M, ∀ ζF ∈ M, ζE ≠ ζF → Disjoint ζE ζF)) (hcover : ∀ x, (((((univ : Finset ↥(H)).filter (fun ζA => x ∈ ζA.val))).map (Function.Embedding.inl (β := Fin n × Fin D))) \ M.biUnion id).card ≤ D / r) :
    ∃ c : Finset (Fin n) → Fin (2 * D),
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  let R := H.filter fun A => ¬ (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = A ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M)
  have hm : r * (D / r - 1) < D := by
    by_cases hq : D / r = 0
    · simp [hq, hD]
    · calc
        _ < r * (D / r) := Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (Nat.pos_of_ne_zero hq) Nat.zero_lt_one) hr
        _ ≤ D := by simpa [Nat.mul_comm] using Nat.div_mul_le_self D r
  obtain ⟨d, hd⟩ := color_small_rank R
    (fun A hA => hrank A (Finset.mem_filter.mp hA).1)
    (fun x => (deg_unassigned hsub x).trans_le (hcover x)) D hm
  let c : Finset (Fin n) → Fin (D + D) := fun A =>
    if h : (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = A ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M) then Fin.castAdd D (Classical.choose h) else Fin.natAdd D (d A)
  have hcast : D + D = 2 * D := by omega
  refine ⟨fun A => Fin.cast hcast (c A), ?_⟩
  intro A hA B hB hAB hmeet heq
  have hc := Fin.cast_injective hcast heq
  by_cases hMA : (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = A ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M) <;> by_cases hMB : (∃ ζj : Fin D, ∃ ζa : ↥H, ζa.val = B ∧ (insert (Sum.inl ζa) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζj) : type_of% ζa ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζa).val)) ∈ M)
  · simp only [c, dif_pos hMA, dif_pos hMB] at hc
    have hj : Classical.choose hMA = Classical.choose hMB := Fin.castAdd_injective D D hc
    obtain ⟨a, ha, hma⟩ := Classical.choose_spec hMA
    obtain ⟨b, hb, hmb⟩ := Classical.choose_spec hMB
    rw [← hj] at hmb
    let j := Classical.choose hMA
    have hne : (insert (Sum.inl a) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% a ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (a).val)) ≠ (insert (Sum.inl b) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% b ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (b).val)) := by
      intro h
      have hleft : Sum.inl a ∈ (insert (Sum.inl b) (Finset.map ⟨fun ζx => (Sum.inr (ζx, j) : type_of% b ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (b).val)) :=
        h ▸ inl_mem_assignmentEdge.mpr rfl
      exact hAB (ha.symm.trans ((congrArg Subtype.val (inl_mem_assignmentEdge.mp hleft)).trans hb))
    obtain ⟨x, hx⟩ := hmeet
    obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
    exact (Finset.disjoint_left.mp (hM _ hma _ hmb hne))
      (inr_mem_assignmentEdge.mpr ⟨rfl, ha.symm ▸ hxA⟩)
      (inr_mem_assignmentEdge.mpr ⟨rfl, hb.symm ▸ hxB⟩)
  · simp only [c, dif_pos hMA, dif_neg hMB] at hc
    have he := congrArg Fin.val hc
    simp at he
    omega
  · simp only [c, dif_neg hMA, dif_pos hMB] at hc
    have he := congrArg Fin.val hc
    simp at he
    omega
  · simp only [c, dif_neg hMA, dif_neg hMB] at hc
    exact hd A (Finset.mem_filter.mpr ⟨hA, hMA⟩) B (Finset.mem_filter.mpr ⟨hB, hMB⟩)
      hAB hmeet (Fin.natAdd_injective D D hc)


theorem core_uniform_regular_of (r : ℕ) (hr : 3 ≤ r)
    (hc0 : ∃ D₀ : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (D : ℕ), D₀ ≤ D →
    ∀ (G T : Finset (Finset α)), (∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ E ∈ G, E.card = r + 1) → (∀ x, (G.filter fun E => x ∈ E).card = D) →
    (∀ U ∈ T, U.card ≤ D) → (∀ x, (T.filter fun U => x ∈ U).card ≤ r + 1) →
    ∃ M : Finset (Finset α), M ⊆ G ∧ (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
      ∀ U ∈ T, (U \ M.biUnion id).card ≤ D / r) :
    ∃ D₀ : ℕ, ∀ n D : ℕ, D₀ ≤ D → ∀ H : Finset (Finset (Fin n)),
    (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) → (∀ A ∈ H, A.card = r) →
    (∀ x, (H.filter fun A => x ∈ A).card = D) →
    ∃ c : Finset (Fin n) → Fin (2 * D),
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  obtain ⟨D₀, hc⟩ := hc0
  refine ⟨max 1 D₀, ?_⟩
  intro n D hD H hlin hu hd
  have hne : ∀ A ∈ H, A.Nonempty := by
    intro A hA
    rw [← Finset.card_pos, hu A hA]
    omega
  let G := ((univ : Finset (↥(H) × Fin D)).image (fun ζp => (insert (Sum.inl ζp.1) (Finset.map ⟨fun ζx => (Sum.inr (ζx, ζp.2) : type_of% ζp.1 ⊕ _), fun _ _ h => congrArg Prod.fst (Sum.inr.inj h)⟩ (ζp.1).val))))
  let T := (univ : Finset (Fin n)).image ((fun ζx => ((((univ : Finset ↥(H)).filter (fun ζA => ζx ∈ ζA.val))).map (Function.Embedding.inl (β := Fin n × Fin D)))))
  have hdeg (x : ((↥(H)) ⊕ (Fin n × Fin D))) : (G.filter fun ζA => x ∈ ζA).card = D := by
    rcases x with A | ⟨x, j⟩
    · exact deg_assignments_inl hne A
    · rw [deg_assignments_inr hne, hd]
  have hlinG : ∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1 := linear_assignments hlin D
  have huG : ∀ E ∈ G, E.card = r + 1 := fun E hE => by
      obtain ⟨A, j, rfl⟩ := mem_assignments.mp hE
      rw [card_assignmentEdge, hu A.val A.prop]
  have hTU : ∀ U ∈ T, U.card ≤ D := fun U hU => by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hU
      rw [card_target, hd]
  have hTd : ∀ x, (T.filter fun U => x ∈ U).card ≤ r + 1 := fun x =>
    (deg_targets_le (fun A hA => (hu A hA).le) x).trans (Nat.le_succ r)
  obtain ⟨M, hsub, hM, hcover⟩ := hc (((↥(H)) ⊕ (Fin n × Fin D))) D (by omega) G T hlinG huG hdeg hTU hTd
  exact color_from_assignment_matching (r := r) (by omega) (by omega) H
    (fun A hA => by rw [hu A hA]; omega) M hsub hM
    (fun x => hcover _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))


theorem rank_ge3_of (hcore : ∀ s : ℕ, 3 ≤ s → ∃ D₀ : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (D : ℕ), D₀ ≤ D →
      ∀ (G T : Finset (Finset α)), (∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ E ∈ G, E.card = s + 1) → (∀ x, (G.filter fun E => x ∈ E).card = D) →
      (∀ U ∈ T, U.card ≤ D) → (∀ x, (T.filter fun U => x ∈ U).card ≤ s + 1) →
      ∃ M : Finset (Finset α), M ⊆ G ∧ (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ U ∈ T, (U \ M.biUnion id).card ≤ D / s) (r : ℕ) (hr : 3 ≤ r) :
    ∃ D₀ : ℕ, ∀ n D : ℕ, D₀ ≤ D →
    ∀ H : Finset (Finset (Fin n)),
    (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ r) →
    (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) →
    ∃ c : Finset (Fin n) → Fin (2 * D),
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  obtain ⟨D₀, h⟩ := core_uniform_regular_of r hr (hcore r hr)
  refine ⟨max 1 D₀, ?_⟩
  intro n D hD H hlin hrank hdeg
  apply color_from_uniform_regular (by omega) (by omega : 1 ≤ D)
    (fun N K => h N D (by omega) K) H hlin (fun A hA => (hrank A hA).2) hdeg

/-- Locally covering matchings (odd rank parameter s): for fixed s and large D, an
(s+1)-uniform D-regular linear hypergraph has a matching missing at most D/s points of every
target U, when the targets have size at most D and each point lies in at most s+1 targets. -/
def H1 : Prop :=
  ∀ s : ℕ, 3 ≤ s → s % 2 = 1 →
    ∃ D₀ : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (D : ℕ), D₀ ≤ D →
      ∀ (G T : Finset (Finset α)), (∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ E ∈ G, E.card = s + 1) → (∀ x, (G.filter fun E => x ∈ E).card = D) →
      (∀ U ∈ T, U.card ≤ D) → (∀ x, (T.filter fun U => x ∈ U).card ≤ s + 1) →
      ∃ M : Finset (Finset α), M ⊆ G ∧ (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ U ∈ T, (U \ M.biUnion id).card ≤ D / s

/-- Locally covering matchings, even rank parameter s. -/
def H2 : Prop :=
  ∀ s : ℕ, 3 ≤ s → s % 2 = 0 →
    ∃ D₀ : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α] (D : ℕ), D₀ ≤ D →
      ∀ (G T : Finset (Finset α)), (∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ E ∈ G, E.card = s + 1) → (∀ x, (G.filter fun E => x ∈ E).card = D) →
      (∀ U ∈ T, U.card ≤ D) → (∀ x, (T.filter fun U => x ∈ U).card ≤ s + 1) →
      ∃ M : Finset (Finset α), M ⊆ G ∧ (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ U ∈ T, (U \ M.biUnion id).card ≤ D / s

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_variants_kahn_R1.H2 := by
  intro h1 h2 r
  by_cases hr : r ≤ 2
  · refine ⟨1, fun n D hD H _ hrank hdeg => ?_⟩
    refine color_small_rank H hrank hdeg (2 * D) ?_
    have : r * (D - 1) ≤ 2 * (D - 1) := Nat.mul_le_mul_right _ hr
    omega
  · refine rank_ge3_of (fun s hs => ?_) r (by omega)
    rcases Nat.mod_two_eq_zero_or_one s with h | h
    · exact h2 s hs h
    · exact h1 s hs h

end OMA.R_Erdos19_erdos_19_variants_kahn_R1_H2_R1
