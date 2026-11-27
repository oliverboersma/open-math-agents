import OMAReductions.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! The bipartite case of WOWII 199 and a five-cycle condition for the triangle-free residual. -/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1_H2_R1

open SimpleGraph Finset
open scoped BigOperators
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1

section

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem connectivity_le_neighbor_card [DecidableRel G.Adj] (v : V) :
    vertexConnectivity G ≤ (G.neighborFinset v).card := by
  classical
  let N := G.neighborFinset v
  let K := G.induce ((N : Set V)ᶜ)
  let x : ↥((N : Set V)ᶜ) := ⟨v, by simp [N]⟩
  unfold vertexConnectivity
  split_ifs
  · omega
  apply csInf_le'
  refine ⟨N, rfl, ?_⟩
  by_cases hK : K.Connected
  · right
    have hx (y : ↥((N : Set V)ᶜ)) : x = y := by
      have hreach := (K.reachable_iff_reflTransGen x y).mp (hK x y)
      induction hreach with
      | refl => rfl
      | tail _ he ih =>
        rename_i a b hab
        rw [← ih] at he
        have hadj : G.Adj v b.val := he
        exact (b.property ((G.mem_neighborFinset v b.val).mpr hadj)).elim
    have hset : insert v N = univ := by
      ext y
      simp only [mem_insert, mem_univ, iff_true]
      by_cases hy : y ∈ N
      · exact Or.inr hy
      · exact Or.inl (congrArg Subtype.val (hx ⟨y,hy⟩)).symm
    have hv : v ∉ N := by simp [N]
    have hcard := congrArg Finset.card hset
    rw [card_insert_of_notMem hv, card_univ] at hcard
    omega
  · exact Or.inl hK

omit [Fintype V] [DecidableEq V] in
private theorem singleton_tree (v : V) : (G.induce ({v} : Set V)).IsTree := by
  let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
  let _ : Subsingleton ↥({v} : Set V) := ⟨fun x y => Subtype.ext
    ((Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm)⟩
  exact IsTree.of_subsingleton


private theorem private_neighbors_bound [DecidableRel G.Adj]
    {u v z : V} (huv : u ≠ v) (hno : ¬ G.Adj u v)
    (huz : G.Adj u z) (hvz : G.Adj v z)
    (hind : G.IsIndepSet (G.neighborSet u ∪ G.neighborSet v)) :
    ((G.neighborFinset u \ G.neighborFinset v).card +
        (G.neighborFinset v \ G.neighborFinset u).card) + 3 ≤ largestInducedTreeSize G := by
  classical
  have hC : (G.induce ({z} : Set V)).Connected := (singleton_tree z).connected
  obtain ⟨C,hcard,hCu,hCv,hcover,htree⟩ :=
    connector_tree_of_common_component u v {z} huv hno hC
      ⟨z,Set.mem_singleton _,huz⟩ ⟨z,Set.mem_singleton _,hvz⟩
  let S := G.neighborFinset u \ G.neighborFinset v
  let T := G.neighborFinset v \ G.neighborFinset u
  have hS (x : V) (hx : x ∈ S) : G.Adj u x ∧ ¬G.Adj v x := by simpa [S] using hx
  have hT (x : V) (hx : x ∈ T) : G.Adj v x ∧ ¬G.Adj u x := by simpa [T] using hx
  have hleaves {a b : V} {Z : Finset V} (hno' : ¬ G.Adj a b)
      (hbz : G.Adj b z) (hcover' : ∀ x ∈ C, x = a ∨ x = b ∨ x ∈ ({z} : Set V))
      (hZ : ∀ x ∈ Z, G.Adj a x ∧ ¬G.Adj b x)
      (hZi : ∀ x ∈ Z, x ∈ G.neighborSet u ∪ G.neighborSet v) :
      Disjoint Z C ∧ G.IsIndepSet (Z : Set V) ∧ (∀ x ∈ Z, G.Adj x a) ∧
        (∀ x ∈ Z, ∀ y ∈ C, G.Adj x y → y = a) := by
    refine ⟨Finset.disjoint_left.mpr ?_, ?_, fun x hx => (hZ x hx).1.symm, ?_⟩
    · intro x hx hxC
      rcases hcover' x hxC with he | he | he
      · exact (hZ x hx).1.ne he.symm
      · exact hno' (he ▸ (hZ x hx).1)
      · exact (hZ x hx).2 ((Set.mem_singleton_iff.mp he).symm ▸ hbz)
    · exact fun x hx y hy => hind (hZi x hx) (hZi y hy)
    · intro x hx y hy he
      rcases hcover' y hy with rfl | rfl | hyz
      · rfl
      · exact ((hZ x hx).2 he.symm).elim
      · have hy' : y ∈ G.neighborSet u ∪ G.neighborSet v :=
          Or.inl ((Set.mem_singleton_iff.mp hyz).symm ▸ huz)
        exact (hind (hZi x hx) hy' he.ne he).elim
  obtain ⟨hSC,hSi,hSa,hSu⟩ := hleaves hno hvz hcover hS (fun x hx => Or.inl (hS x hx).1)
  obtain ⟨hTC,hTi,hTa,hTv⟩ := hleaves (fun he => hno he.symm) huz (by
    intro x hx
    rcases hcover x hx with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)) hT (fun x hx => Or.inr (hT x hx).1)
  have hST (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) :
      x ≠ y ∧ ¬G.Adj x y := by
    have hne : x ≠ y := fun he => (hS x hx).2 (he.symm ▸ (hT y hy).1)
    exact ⟨hne,hind (Or.inl (hS x hx).1) (Or.inr (hT y hy).1) hne⟩
  have h := leaf_sets_on_induced_tree C S T u v htree hCu hCv hSC hTC hSi hTi
    hST hSa hTa hSu hTv
  change S.card + T.card + 3 ≤ _
  omega

/-- A common neighbor relation is transitive if all rows have size at least k
and overlapping rows have symmetric difference less than k. -/
private theorem row_overlap_trans {U C : Type} [DecidableEq C]
    (R : U → Finset C) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ u, k ≤ (R u).card)
    (hdist : ∀ u v, u ≠ v → (R u ∩ R v).Nonempty →
      (R u \ R v).card + (R v \ R u).card < k)
    {u v w : U} (huv : (R u ∩ R v).Nonempty) (hvw : (R v ∩ R w).Nonempty) :
    (R u ∩ R w).Nonempty := by
  have hinter (a b : U) (h : (R a ∩ R b).Nonempty) :
      (R a).card + (R b).card < k + 2 * (R a ∩ R b).card := by
    by_cases e : a = b
    · subst b
      rw [inter_self]
      omega
    have h1 := card_sdiff_add_card_inter (R a) (R b)
    have h2 := card_sdiff_add_card_inter (R b) (R a)
    rw [inter_comm (R b)] at h2
    have h3 := hdist a b e h
    omega
  have h1 := hinter u v huv
  have h2 := hinter v w hvw
  have h3 := hcard u
  have h4 := hcard w
  have hlt : (R v).card < (R u ∩ R v).card + (R v ∩ R w).card := by omega
  obtain ⟨i,hi⟩ := inter_nonempty_of_card_lt_card_add_card inter_subset_right inter_subset_left hlt
  exact ⟨i,mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hi).1).1,
    (mem_inter.mp (mem_inter.mp hi).2).2⟩⟩

private theorem all_rows_overlap {U C : Type} [DecidableEq C]
    (R : U → Finset C) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ u, k ≤ (R u).card)
    (hdist : ∀ u v, u ≠ v → (R u ∩ R v).Nonempty →
      (R u \ R v).card + (R v \ R u).card < k)
    (hreach : ∀ u v, Relation.ReflTransGen (fun u v => (R u ∩ R v).Nonempty) u v) :
    ∀ u v, (R u ∩ R v).Nonempty := by
  intro u w
  induction hreach u w with
  | refl =>
    rw [inter_self]
    exact card_pos.mp (hk.trans_le (hcard u))
  | tail _ hvw huv => exact row_overlap_trans R k hk hcard hdist huv hvw

/-- Count ordered pairs of rows that differ in each column. The strict
row-distance bound forces the larger side to have size below twice k. -/
private theorem larger_part_card {U C : Type} [Fintype U] [Fintype C]
    [DecidableEq C] [Nonempty U] (R : U → Finset C) (k : ℕ) (hk : 1 < k)
    (hsize : Fintype.card U ≤ Fintype.card C)
    (hcol : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (hrow : ∀ u, (R u).card ≤ k + 1)
    (hdist : ∀ u v, u ≠ v → (R u \ R v).card + (R v \ R u).card < k) :
    Fintype.card C < 2 * k := by
  classical
  let m : ℤ := Fintype.card U
  let n : ℤ := Fintype.card C
  let I (u : U) (i : C) : ℤ := if i ∈ R u then 1 else 0
  let D (i : C) : ℤ := (univ.filter fun u => i ∈ R u).card
  let E : ℤ := ∑ i : C, D i
  let F (u v : U) : ℤ := ((R u \ R v).card : ℤ) + ((R v \ R u).card : ℤ)
  let T : ℤ := ∑ u : U, ∑ v : U, F u v
  have hD (i : C) : ∑ u : U, I u i = D i := by
    simp [I, D]
  have hrowI (u : U) : ∑ i : C, I u i = (R u).card := by
    rw [show (∑ i : C, I u i) = ((univ.filter fun i => i ∈ R u).card : ℤ) by
      simp [I]]
    simp
  have hE : E = ∑ u : U, ((R u).card : ℤ) := by
    simp only [E, ← hD, ← hrowI]
    exact Finset.sum_comm
  have he : E ≤ m * ((k : ℤ) + 1) := by
    rw [hE]
    calc
      _ ≤ ∑ _u : U, ((k : ℤ) + 1) := sum_le_sum fun u _ => by exact_mod_cast hrow u
      _ = _ := by simp [m]
  have hF (u v : U) : F u v =
      ∑ i : C, (I u i * (1 - I v i) + (1 - I u i) * I v i) := by
    let known (A : Finset C) : (∑ i : C, if i ∈ A then (1 : ℤ) else 0) = A.card := by
      simp
    rw [show F u v = ((R u \ R v).card : ℤ) + ((R v \ R u).card : ℤ) from rfl,
      ← known, ← known, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hu : i ∈ R u <;> by_cases hv : i ∈ R v <;> simp [I, hu, hv]
  have hnotI (i : C) : (∑ u : U, (1 - I u i)) = m - D i := by
    rw [sum_sub_distrib, hD]
    simp [m]
  have hT : T = ∑ i : C, 2 * D i * (m - D i) := by
    calc
      T = ∑ u : U, ∑ v : U, ∑ i : C,
          (I u i * (1 - I v i) + (1 - I u i) * I v i) := by simp only [T, hF]
      _ = ∑ i : C, ∑ u : U, ∑ v : U,
          (I u i * (1 - I v i) + (1 - I u i) * I v i) := by
        calc
          _ = ∑ u : U, ∑ i : C, ∑ v : U,
              (I u i * (1 - I v i) + (1 - I u i) * I v i) :=
            sum_congr rfl (fun _ _ => sum_comm)
          _ = _ := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro i _
        simp only [sum_add_distrib, ← mul_sum, hnotI, hD]
        rw [← sum_mul, ← sum_mul, hD, hnotI]
        ring
  have hlower : 2 * (k : ℤ) * n * m ≤ T + 2 * (k : ℤ) * E := by
    change _ ≤ T + 2 * (k : ℤ) * (∑ i : C, D i)
    rw [hT, mul_sum, ← sum_add_distrib]
    calc
      _ = ∑ _i : C, 2 * (k : ℤ) * m := by
        simp only [sum_const, nsmul_eq_mul, card_univ, n]
        ring
      _ ≤ _ := by
        apply sum_le_sum
        intro i _
        have hlo : (k : ℤ) ≤ D i := by
          change (k : ℤ) ≤ ((univ.filter fun u => i ∈ R u).card : ℤ)
          exact_mod_cast hcol i
        have hhi : D i ≤ m := by
          change ((univ.filter fun u => i ∈ R u).card : ℤ) ≤ (Fintype.card U : ℤ)
          exact_mod_cast card_le_univ (univ.filter fun u : U => i ∈ R u)
        nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  have hk' : (1 : ℤ) < k := by exact_mod_cast hk
  have hinner (u : U) : (∑ v : U, F u v) < ((k : ℤ) - 1) * m := by
    rw [show ((k : ℤ) - 1) * m = ∑ _v : U, ((k : ℤ) - 1) by simp [m]; ring]
    apply sum_lt_sum
    · intro v _
      by_cases h : u = v
      · subst v
        simpa [F] using (show (0 : ℤ) ≤ k - 1 by omega)
      · have h' : F u v < (k : ℤ) := by
          dsimp [F]
          exact_mod_cast hdist u v h
        omega
    · exact ⟨u, mem_univ _, by simpa [F] using (show (0 : ℤ) < k - 1 by omega)⟩
  have hupper : T < ((k : ℤ) - 1) * m * m := by
    rw [show ((k : ℤ) - 1) * m * m = ∑ _u : U, ((k : ℤ) - 1) * m by
      simp [m]; ring]
    exact sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun u _ => hinner u)
  have hm : 0 < m := by
    change (0 : ℤ) < (Fintype.card U : ℤ)
    exact_mod_cast Fintype.card_pos (α := U)
  have hmn : m ≤ n := by
    dsimp [m, n]
    exact_mod_cast hsize
  have hc : 2 * (k : ℤ) * n * m <
      (((k : ℤ) - 1) * m + 2 * (k : ℤ) * ((k : ℤ) + 1)) * m := by
    have hmE := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * (k : ℤ) by positivity)
    linarith
  have hcancel := (mul_lt_mul_iff_of_pos_right hm).mp hc
  have hkmono := mul_le_mul_of_nonneg_left hmn (show 0 ≤ (k : ℤ) - 1 by omega)
  have hlt : n * ((k : ℤ) + 1) < (2 * (k : ℤ)) * ((k : ℤ) + 1) := by
    linarith
  have hh := (mul_lt_mul_iff_of_pos_right (show 0 < (k : ℤ) + 1 by positivity)).mp hlt
  dsimp [n] at hh
  exact_mod_cast hh

omit [DecidableEq V] in
private theorem part_card_le_of_scattering (A B : Finset V)
    (hdis : Disjoint A B) (hind : G.IsIndepSet (B : Set V))
    (hcover : ∀ x : V, x ∈ A ∨ x ∈ B)
    (hscatter : Nat.card (G.induce ((A : Set V)ᶜ)).ConnectedComponent ≤ A.card + 1) :
    B.card ≤ A.card + 1 := by
  let S := ↥((A : Set V)ᶜ)
  let K := G.induce ((A : Set V)ᶜ)
  let f : B → S := fun x => ⟨x.val, fun hx => Finset.disjoint_left.mp hdis hx x.property⟩
  have hK : K = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u v huv
    have he : G.Adj u.val v.val := huv
    have hu := (hcover u.val).resolve_left u.property
    have hv := (hcover v.val).resolve_left v.property
    exact (hind hu hv he.ne he).elim
  have hinj : Function.Injective (fun x : B => K.connectedComponentMk (f x)) := by
    intro x y hxy
    have hr := ConnectedComponent.eq.mp hxy
    rw [hK, reachable_bot] at hr
    exact Subtype.ext (congrArg (fun z : S => z.val) hr)
  let _ : Finite K.ConnectedComponent :=
    Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  have hc := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  exact hc.trans hscatter

private theorem bipartite_larger_part_lt [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) (hk : 1 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (A B : Finset V) (hcross : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hsize : A.card ≤ B.card) :
    B.card < 2 * vertexConnectivity G := by
  classical
  let k := vertexConnectivity G
  let R (a : A) : Finset B := univ.filter (fun b : B => G.Adj a.val b.val)
  have hR (a : A) (b : B) : b ∈ R a ↔ G.Adj a.val b.val := by simp [R]
  let embB : B ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let embA : A ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap (a : A) : (R a).map embB = G.neighborFinset a.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hx
      exact (G.mem_neighborFinset a.val b.val).mpr ((hR a b).mp hb)
    · intro hx
      have hadj := (G.mem_neighborFinset _ _).mp hx
      exact mem_map.mpr ⟨⟨x,hcross.mem_of_mem_adj a.property hadj⟩,(hR _ _).mpr hadj,rfl⟩
  have hcol (b : B) : k ≤ (univ.filter fun a : A => b ∈ R a).card := by
    have hmap' : (univ.filter fun a : A => b ∈ R a).map embA = G.neighborFinset b.val := by
      ext x
      constructor
      · intro hx
        obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
        exact (G.mem_neighborFinset b.val a.val).mpr ((hR a b).mp (mem_filter.mp ha).2).symm
      · intro hx
        have hadj := (G.mem_neighborFinset _ _).mp hx
        refine mem_map.mpr ⟨⟨x,hcross.symm.mem_of_mem_adj b.property hadj⟩,?_,rfl⟩
        exact mem_filter.mpr ⟨mem_univ _,(hR _ _).mpr hadj.symm⟩
    rw [← card_map embA, hmap']
    exact connectivity_le_neighbor_card b.val
  have hrowLower (a : A) : k ≤ (R a).card := by
    rw [← card_map embB, hmap]
    exact connectivity_le_neighbor_card a.val
  have hrowUpper (a : A) : (R a).card ≤ k + 1 := by
    have hind : G.IsIndepSet (↑(G.neighborFinset a.val) : Set V) := by
      intro x hx y hy _
      have hxB := hcross.mem_of_mem_adj a.property ((G.mem_neighborFinset _ _).mp hx)
      have hyB := hcross.mem_of_mem_adj a.property ((G.mem_neighborFinset _ _).mp hy)
      exact fun he => Set.disjoint_left.mp hcross.disjoint
        (hcross.symm.mem_of_mem_adj hxB he) hyB
    have h := star_bound a.val _ hind (fun x hx => (G.mem_neighborFinset _ _).mp hx)
    rw [← hmap, card_map] at h
    change _ - 2 ≤ k at ht
    omega
  have hdist (a a' : A) (hne : a ≠ a') (hover : (R a ∩ R a').Nonempty) :
      (R a \ R a').card + (R a' \ R a).card < k := by
    obtain ⟨b,hb⟩ := hover
    obtain ⟨hb,hb'⟩ := mem_inter.mp hb
    have hno : ¬ G.Adj a.val a'.val := fun he => Set.disjoint_left.mp hcross.disjoint
      a'.property (hcross.mem_of_mem_adj a.property he)
    have hN : G.neighborSet a.val ∪ G.neighborSet a'.val ⊆ (B : Set V) := by
      intro x hx
      rcases hx with hx | hx
      · exact hcross.mem_of_mem_adj a.property hx
      · exact hcross.mem_of_mem_adj a'.property hx
    have hInd : G.IsIndepSet (G.neighborSet a.val ∪ G.neighborSet a'.val) := by
      intro x hx y hy _ he
      exact Set.disjoint_left.mp hcross.disjoint (hcross.symm.mem_of_mem_adj (hN hx) he) (hN hy)
    have h := private_neighbors_bound (fun he => hne (Subtype.ext he))
      hno ((hR _ _).mp hb) ((hR _ _).mp hb') hInd
    rw [← hmap a, ← hmap a', ← Finset.map_sdiff, ← Finset.map_sdiff, card_map, card_map] at h
    change _ - 2 ≤ k at ht
    omega
  have label (x : V) : ∃ a : A, (x ∈ A → a.val = x) ∧ (x ∈ B → G.Adj a.val x) := by
    by_cases hx : x ∈ A
    · exact ⟨⟨x,hx⟩,fun _ => rfl,
        fun hb => (Set.disjoint_left.mp hcross.disjoint hx hb).elim⟩
    · obtain ⟨y,hy⟩ := hG.preconnected.exists_adj_of_nontrivial x
      obtain ⟨hx',hyA⟩ := (hcross.mem_of_adj hy).resolve_left (fun h => hx h.1)
      exact ⟨⟨y,hyA⟩,fun h => (hx h).elim,fun _ => hy.symm⟩
  obtain ⟨x⟩ := hG.nonempty
  have : Nonempty A := by obtain ⟨a,_⟩ := label x; exact ⟨a⟩
  choose f hf using label
  have hedge {x y : V} (hxy : G.Adj x y) : (R (f x) ∩ R (f y)).Nonempty := by
    rcases hcross.mem_of_adj hxy with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact ⟨⟨y,hy⟩,mem_inter.mpr ⟨(hR _ _).mpr (by rwa [(hf x).1 hx]),
        (hR _ _).mpr ((hf y).2 hy)⟩⟩
    · exact ⟨⟨x,hx⟩,mem_inter.mpr ⟨(hR _ _).mpr ((hf x).2 hx),
        (hR _ _).mpr (by rw [(hf y).1 hy]; exact hxy.symm)⟩⟩
  have hwalk {x y : V} (h : Relation.ReflTransGen G.Adj x y) :
      Relation.ReflTransGen (fun a a' => (R a ∩ R a').Nonempty) (f x) (f y) := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ he ih => exact ih.tail (hedge he)
  have hreach (a a' : A) :
      Relation.ReflTransGen (fun u v => (R u ∩ R v).Nonempty) a a' := by
    have h := hwalk ((G.reachable_iff_reflTransGen _ _).mp (hG a.val a'.val))
    have hfix (u : A) : f u.val = u := Subtype.ext ((hf u.val).1 u.property)
    rwa [hfix, hfix] at h
  have hover := all_rows_overlap R k (by omega) hrowLower hdist hreach
  have hs : Fintype.card A ≤ Fintype.card B := by simpa using hsize
  simpa using larger_part_card R k hk hs hcol hrowUpper
    (fun a a' h => hdist a a' h (hover a a'))

omit [Fintype V] in
private theorem chain_predecessors (L : List V) (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (S : Finset V) (hS : ∀ y ∈ S, y ∈ L ∧ L.head? ≠ some y) :
    ∃ R : Finset V, R.card = S.card ∧
      ∀ x ∈ R, ∃ y ∈ S, G.Adj x y ∧ ∃ P Q : List V, L = P ++ x :: y :: Q := by
  classical
  have hpred (y : S) : ∃ x, ∃ P Q : List V, L = P ++ x :: y.val :: Q := by
    obtain ⟨P,Q,hL⟩ := List.append_of_mem (hS y.val y.property).1
    rcases P.eq_nil_or_concat' with h | ⟨P',x,h⟩
    · exact ((hS y.val y.property).2 (by simp [hL,h])).elim
    · exact ⟨x,P',Q,by simp [hL,h,List.append_assoc]⟩
  choose f P Q h using hpred
  have hindex (y : S) : L.idxOf y.val = L.idxOf (f y) + 1 := by
    have hn' := List.nodup_append.mp (h y ▸ hn : (P y ++ f y :: y.val :: Q y).Nodup)
    have hx : f y ∉ P y := fun hx => hn'.2.2 _ hx _ (by simp) rfl
    have hy : y.val ∉ P y := fun hy => hn'.2.2 _ hy _ (by simp) rfl
    have hxy : y.val ≠ f y := by
      intro e
      exact (List.nodup_cons.mp hn'.2.1).1 (by simp [e])
    rw [h y,List.idxOf_append_of_notMem hx,List.idxOf_append_of_notMem hy]
    simp [List.idxOf_cons_ne _ hxy.symm]
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hidx : L.idxOf x.val = L.idxOf y.val := by rw [hindex, hindex,hxy]
    have hx := List.getElem?_idxOf (hS x.val x.property).1
    have hy := List.getElem?_idxOf (hS y.val y.property).1
    rw [hidx,hy] at hx
    exact (Option.some.inj hx).symm
  refine ⟨S.attach.image f,by simp [card_image_of_injective _ hfi],?_⟩
  intro x hx
  obtain ⟨y,_,rfl⟩ := mem_image.mp hx
  have hc' : (P y ++ f y :: y.val :: Q y).IsChain G.Adj := h y ▸ hc
  exact ⟨y.val,y.property,List.isChain_cons_cons.mp hc'.right_of_append |>.1,P y,Q y,h y⟩

private theorem longest_chain_contains_other_part [DecidableRel G.Adj]
    (A B : Finset V) (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (k : ℕ) (hsize : A.card < 2 * k) (hdeg : ∀ v, k ≤ (G.neighborFinset v).card)
    (L : List V) (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    {a : V} (ha : L.head? = some a) (haA : a ∈ A) :
    ∀ c ∈ B, c ∈ L := by
  classical
  intro c hcB
  by_contra hco
  let S := G.neighborFinset a
  have hS (y : V) (hy : y ∈ S) : y ∈ L ∧ L.head? ≠ some y := by
    have hay := (G.mem_neighborFinset a y).mp hy
    refine ⟨?_,fun h => hay.ne (Option.some.inj (ha.symm.trans h))⟩
    by_contra hyo
    exact (longest_chain_endpoints hn hc hm hyo).1 a (by simp [ha]) hay
  obtain ⟨R,hcard,hR⟩ := chain_predecessors L hn hc S hS
  have hRA : R ⊆ A := by
    intro x hx
    obtain ⟨y,hy,hxy,_,_,_⟩ := hR x hx
    have hyB := hAB.mem_of_mem_adj haA ((G.mem_neighborFinset a y).mp hy)
    exact hAB.symm.mem_of_mem_adj hyB hxy.symm
  let T := G.neighborFinset c
  have hTA : T ⊆ A := fun x hx => hAB.symm.mem_of_mem_adj hcB ((G.mem_neighborFinset c x).mp hx)
  have hd : Disjoint R T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxT
    obtain ⟨y,hy,_,P,Q,hL⟩ := hR x hx
    have hxc := ((G.mem_neighborFinset c x).mp hxT).symm
    have hNO := longest_chain_head_misses_successor P Q a x y c
      (hL ▸ ha) (hL ▸ hn) (hL ▸ hc)
      (fun M hMn hMc => hL ▸ hm M hMn hMc) (hL ▸ hco) hxc
    exact hNO ((G.mem_neighborFinset a y).mp hy)
  have hsum := card_le_card (union_subset hRA hTA)
  rw [card_union_of_disjoint hd,hcard] at hsum
  have haMin : k ≤ S.card := hdeg a
  have hcMin : k ≤ T.card := hdeg c
  omega

private theorem traceable_of_small_bipartition [DecidableRel G.Adj] [Nonempty V]
    (A B : Finset V) (hAB : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : ∀ x : V, x ∈ A ∨ x ∈ B) (k : ℕ)
    (hAsize : A.card < 2 * k) (hBsize : B.card < 2 * k)
    (hBA : B.card ≤ A.card + 1) (hAB' : A.card ≤ B.card + 1)
    (hdeg : ∀ v, k ≤ (G.neighborFinset v).card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨L,hL,hn,hc,hm⟩ := exists_longest_chain (G := G)
  let a := L.head hL
  let b := L.getLast hL
  have ha : L.head? = some a := List.head?_eq_some_head hL
  have hb : L.getLast? = some b := List.getLast?_eq_some_getLast hL
  have hfinish (X Y : Finset V) (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V))
      (hX : X.card < 2 * k) (hY : Y.card < 2 * k)
      (hXY' : X.card ≤ Y.card + 1) (haX : a ∈ X) (hcover' : ∀ x : V, x ∈ X ∨ x ∈ Y) :
      ∀ z : V, z ∈ L := by
    have hyMem := longest_chain_contains_other_part X Y hXY k hX hdeg L hn hc hm ha haX
    have hxMem : ∀ x ∈ X, x ∈ L := by
      by_cases hbY : b ∈ Y
      · have hn' := List.nodup_reverse.mpr hn
        have hc' := List.isChain_reverse.mpr (hc.imp fun _ _ h => h.symm)
        have hm' (Q : List V) (hQn : Q.Nodup) (hQc : Q.IsChain G.Adj) : Q.length ≤ L.reverse.length := by
          simpa using hm Q.reverse (List.nodup_reverse.mpr hQn) (List.isChain_reverse.mpr (hQc.imp fun _ _ h => h.symm))
        have hb' : L.reverse.head? = some b := by rwa [List.head?_reverse]
        intro x hx
        exact List.mem_reverse.mp
          (longest_chain_contains_other_part Y X hXY.symm k hY hdeg L.reverse hn' hc' hm' hb' hbY x hx)
      · have hbX := (hcover' b).resolve_right hbY
        have hS (y : V) (hy : y ∈ Y) : y ∈ L ∧ L.head? ≠ some y := by
          refine ⟨hyMem y hy,?_⟩
          rw [ha]
          exact fun e => Set.disjoint_left.mp hXY.disjoint (Option.some.inj e ▸ haX) hy
        obtain ⟨R,hRcard,hR⟩ := chain_predecessors L hn hc Y hS
        have hXR : insert b R ⊆ X := by
          intro x hx
          rcases mem_insert.mp hx with rfl | hx
          · exact hbX
          · obtain ⟨y,hy,hxy,_,_,_⟩ := hR x hx
            exact hXY.symm.mem_of_mem_adj hy hxy.symm
        have hbR : b ∉ R := by
          intro hbR
          obtain ⟨y,hy,_,P,Q,he⟩ := hR b hbR
          have hn' : (P ++ b :: y :: Q).Nodup := he ▸ hn
          refine (List.nodup_cons.mp hn'.of_append_right).1 ?_
          have he' : (y :: Q).getLast? = some b := by
            simpa [he,List.getLast?_append,List.getLast?_cons] using hb
          exact List.mem_of_mem_getLast? he'
        have he : insert b R = X := eq_of_subset_of_card_le hXR (by
          rwa [card_insert_of_notMem hbR,hRcard])
        intro x hx
        rw [← he] at hx
        rcases mem_insert.mp hx with rfl | hx
        · exact List.mem_of_mem_getLast? hb
        · obtain ⟨y,_,_,P,Q,hL'⟩ := hR x hx
          simp [hL']
    intro z
    rcases hcover' z with hz | hz
    · exact hxMem z hz
    · exact hyMem z hz
  have all : ∀ x, x ∈ L := by
    rcases hcover a with he | he
    · exact hfinish A B hAB hAsize hBsize hAB' he hcover
    · exact hfinish B A hAB.symm hBsize hAsize hBA he (fun x => (hcover x).symm)
  let p := Walk.ofSupport L hL hc
  have hp := Walk.support_ofSupport hL hc
  have hpath : p.IsPath := Walk.IsPath.mk' (hp.symm ▸ hn)
  exact ⟨_,_,p,hpath.isHamiltonian_of_mem (fun x => hp.symm ▸ all x)⟩

set_option maxHeartbeats 1200000 in
/-- In the absence of triangles and five-cycles, the overlap argument gives
a bipartition by whether a vertex shares a neighbor with a fixed vertex. -/
private theorem bipartite_of_no_triangle_or_five_cycle [DecidableRel G.Adj]
    (hG : G.Connected) (hk : 0 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (htri : G.CliqueFree 3)
    (hno5 : ¬ ∃ a : V, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 5) :
    G.IsBipartite := by
  classical
  let N (v : V) : Finset V := G.neighborFinset v
  let same (u v : V) := (N u ∩ N v).Nonempty
  have hdeg (v : V) : vertexConnectivity G ≤ (N v).card := connectivity_le_neighbor_card v
  have hsame (u v : V) :
      same u v ↔ ∃ z, G.Adj u z ∧ G.Adj v z := by
    constructor
    · rintro ⟨z,hz⟩
      obtain ⟨hu,hv⟩ := mem_inter.mp hz
      exact ⟨z,(G.mem_neighborFinset u z).mp hu,(G.mem_neighborFinset v z).mp hv⟩
    · rintro ⟨z,hu,hv⟩
      exact ⟨z,mem_inter.mpr ⟨(G.mem_neighborFinset u z).mpr hu,(G.mem_neighborFinset v z).mpr hv⟩⟩
  have no_adj_of_same {u v : V} (hs : same u v) : ¬ G.Adj u v := by
    obtain ⟨z,huz,hvz⟩ := (hsame u v).mp hs
    intro huv
    exact isIndepSet_neighborSet_of_triangleFree G htri u huv huz hvz.ne hvz
  have hdist (u v : V) (hne : u ≠ v) (hs : same u v) :
      (N u \ N v).card + (N v \ N u).card < vertexConnectivity G := by
    obtain ⟨z,huz,hvz⟩ := (hsame u v).mp hs
    have hnot := no_adj_of_same hs
    have huInd := isIndepSet_neighborSet_of_triangleFree G htri u
    have hvInd := isIndepSet_neighborSet_of_triangleFree G htri v
    have hcross {x y : V} (hux : G.Adj u x) (hvy : G.Adj v y) : ¬ G.Adj x y := by
      intro hxy
      have hzx : z ≠ x := by
        intro he
        exact hvInd (he ▸ hvz) hvy hxy.ne hxy
      have hzy : z ≠ y := by
        intro he
        exact huInd hux (he ▸ huz) hxy.ne hxy
      have hvx : v ≠ x := fun he => hnot (he.symm ▸ hux)
      have hyu : y ≠ u := fun he => hnot (he ▸ hvy).symm
      let p : G.Walk u u :=
        .cons huz (.cons hvz.symm (.cons hvy (.cons hxy.symm (.cons hux.symm .nil))))
      have hp : p.IsCycle := by
        apply (Walk.isCycle_iff_isPath_tail_and_le_length).mpr
        refine ⟨Walk.IsPath.mk' ?_, by change 3 ≤ 5; decide⟩
        change [z,v,y,x,u].Nodup
        simp [hvz.ne.symm,hzy,hzx,huz.ne.symm,hvy.ne,hvx,hne.symm,hxy.ne.symm,hyu,hux.ne.symm]
      exact hno5 ⟨u,p,hp,rfl⟩
    have hind : G.IsIndepSet (G.neighborSet u ∪ G.neighborSet v) := by
      intro x hx y hy hne'
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact huInd hx hy hne'
      · exact hcross hx hy
      · exact fun h => hcross hy hx h.symm
      · exact hvInd hx hy hne'
    have h := private_neighbors_bound hne hnot huz hvz hind
    change (N u \ N v).card + (N v \ N u).card + 3 ≤ _ at h
    omega
  have htrans {u v w : V} (huv : same u v) (hvw : same v w) : same u w := by
    change (N u ∩ N v).Nonempty at huv
    change (N v ∩ N w).Nonempty at hvw
    change (N u ∩ N w).Nonempty
    exact @row_overlap_trans V V (inferInstance : DecidableEq V) N (vertexConnectivity G)
      hk hdeg hdist u v w huv hvw
  obtain ⟨a⟩ := hG.nonempty
  let S : Set V := {x | same a x}
  have ha : a ∈ S := by
    change (N a ∩ N a).Nonempty
    rw [inter_self]
    exact card_pos.mp (hk.trans_le (hdeg a))
  have step {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) : same u w :=
    (hsame u w).mpr ⟨v,huv,hvw.symm⟩
  have hreach {x : V} (hr : Relation.ReflTransGen G.Adj a x) :
      x ∈ S ∨ ∃ y ∈ S, G.Adj y x := by
    induction hr with
    | refl => exact Or.inl ha
    | tail _ he ih =>
      rcases ih with hx | ⟨y,hy,hyx⟩
      · exact Or.inr ⟨_,hx,he⟩
      · exact Or.inl (htrans hy (step hyx he))
  have hbi : G.IsBipartiteWith S Sᶜ := by
    refine ⟨Set.disjoint_left.mpr (fun _ hx hy => hy hx),?_⟩
    intro u v he
    by_cases hu : u ∈ S
    · have hv : v ∉ S := by
        intro hv
        have hua : same u a := by
          change (N a ∩ N u).Nonempty at hu
          change (N u ∩ N a).Nonempty
          rwa [inter_comm]
        exact no_adj_of_same (htrans hua hv) he
      exact Or.inl ⟨hu,hv⟩
    · have hv : v ∈ S := by
        obtain ⟨y,hy,hyu⟩ := (hreach ((G.reachable_iff_reflTransGen _ _).mp (hG a u))).resolve_left hu
        exact htrans hy (step hyu he)
      exact Or.inr ⟨hu,hv⟩
  exact hbi.isBipartite

end

/-- Find a spanning path in the triangle-free nonbipartite case with a five-cycle. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → Gᶜ.Connected → 3 ≤ vertexConnectivity G →
    vertexConnectivity G + 2 ≤ G.indepNum →
    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →
    (∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) →
    ¬ G.IsBipartite → G.CliqueFree 3 →
    (∃ a : V, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 5) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Find a spanning path when the graph contains a triangle. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → Gᶜ.Connected → 3 ≤ vertexConnectivity G →
    vertexConnectivity G + 2 ≤ G.indepNum →
    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →
    (∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) →
    ¬ G.CliqueFree 3 →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1.H2 := by
  classical
  intro hfree htriangle V _ _ G hG hGc hk halpha ht hscatter
  by_cases hbi : G.IsBipartite
  · have : Nontrivial V := by
      rcases subsingleton_or_nontrivial V with hs | hn
      · let _ := hs
        simp at hk
      · exact hn
    have : Nonempty V := hG.nonempty
    obtain ⟨S,T,hST⟩ := hbi.exists_isBipartiteWith
    let A := S.toFinset
    let B := T.toFinset
    have hAB : G.IsBipartiteWith (A : Set V) (B : Set V) := by
      simpa [A, B] using hST
    have hdense (X Y : Finset V)
        (hXY : G.IsBipartiteWith (X : Set V) (Y : Set V)) (hle : X.card ≤ Y.card) :
        ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
      have hcover (x : V) : x ∈ X ∨ x ∈ Y := by
        obtain ⟨y,hy⟩ := hG.preconnected.exists_adj_of_nontrivial x
        rcases hXY.mem_of_adj hy with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
      have hind : G.IsIndepSet (Y : Set V) := by
        intro x hx y hy _ he
        exact Set.disjoint_left.mp hXY.disjoint (hXY.symm.mem_of_mem_adj hx he) hy
      have hdis : Disjoint X Y := Finset.disjoint_left.mpr
        (fun _ hx hy => Set.disjoint_left.mp hXY.disjoint hx hy)
      have hYlt := bipartite_larger_part_lt hG (by omega) ht X Y hXY hle
      exact traceable_of_small_bipartition X Y hXY hcover (vertexConnectivity G)
        (hle.trans_lt hYlt) hYlt (part_card_le_of_scattering X Y hdis hind hcover (hscatter X))
        (hle.trans (Nat.le_succ _)) (connectivity_le_neighbor_card (G := G))
    rcases le_total A.card B.card with h | h
    · exact hdense A B hAB h
    · exact hdense B A hAB.symm h
  · by_cases htf : G.CliqueFree 3
    · have h5 : ∃ a : V, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 5 := by
        by_contra h
        exact hbi (bipartite_of_no_triangle_or_five_cycle hG (by omega) ht htf h)
      exact hfree G hG hGc hk halpha ht hscatter hbi htf h5
    · exact htriangle G hG hGc hk halpha ht hscatter htf

end OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1_H2_R1

