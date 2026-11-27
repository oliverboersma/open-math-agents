import OMAReductions.R_Erdos617_erdos_617_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The extremal lemma of Erdős and Gyárfás, *Split and balanced colorings of complete
graphs* (1999), Lemma 2. We work directly with induced neighborhoods. -/
namespace Graph617
open Finset
abbrev V := Fin 17
abbrev Vertices := Finset V
variable (G : SimpleGraph V)
open scoped Classical
noncomputable section

private def rel (b : Bool) (x y : V) : Prop := if b then G.Adj x y else ¬ G.Adj x y
private lemma rel_sym {b x y} (h : rel G b x y) : rel G b y x := by
  cases b <;> simp_all [rel, G.adj_comm]
private def homogeneous (b : Bool) (S : Vertices) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → rel G b x y
private def bound (b : Bool) (S : Vertices) (k : ℕ) : Prop :=
  ∀ T ⊆ S, homogeneous G b T → T.card ≤ k
private def part (b : Bool) (S : Vertices) (x : V) : Vertices :=
  S.filter (fun y => y ≠ x ∧ rel G b x y)
private lemma in_part {b S x y} :
    y ∈ part G b S x ↔ y ∈ S ∧ y ≠ x ∧ rel G b x y := mem_filter
private lemma part_sub (b S x) : part G b S x ⊆ S := filter_subset _ _
private lemma self_out (b S x) : x ∉ part G b S x := by simp [part]
private lemma bound_mono {b S T k} (h : bound G b S k) (ht : T ⊆ S) :
    bound G b T k := fun U hu => h U (hu.trans ht)
private lemma homog_mono {b S T} (h : homogeneous G b S) (ht : T ⊆ S) :
    homogeneous G b T := fun x hx y hy => h x (ht hx) y (ht hy)
private lemma homog_insert {b S x} (h : homogeneous G b S) (hx : ∀ y ∈ S, rel G b x y) :
    homogeneous G b (insert x S) := by
  intro u hu v hv hn
  rcases mem_insert.mp hu with rfl | huS <;> rcases mem_insert.mp hv with rfl | hvS
  · exact (hn rfl).elim
  · exact hx v hvS
  · exact rel_sym G (hx u huS)
  · exact h u huS v hvS hn
private lemma bound_part {b S k x} (h : bound G b S (k+1)) (hx : x ∈ S) :
    bound G b (part G b S x) k := by
  intro T ht hh
  have hs : x ∉ T := fun hxt => self_out G b S x (ht hxt)
  have h₁ := h (insert x T) (insert_subset hx (ht.trans (part_sub G b S x)))
    (homog_insert G hh (fun y hy => (in_part G |>.mp (ht hy)).2.2))
  rw [card_insert_of_notMem hs] at h₁
  omega
private lemma homog_of_bound_one {b S} (h : bound G (!b) S 1) : homogeneous G b S := by
  intro x hx y hy hn
  by_contra hf
  have h' : rel G (!b) x y := by cases b <;> simp_all [rel]
  have hs : homogeneous G (!b) {y} := by
    intro i hi j hj hij
    simp only [mem_singleton] at hi hj
    exact (hij (hi.trans hj.symm)).elim
  have hh := h {x,y} (insert_subset hx (singleton_subset_iff.mpr hy))
    (homog_insert G hs (by simpa using h'))
  simp [hn] at hh
private lemma part_sizes {S x} (hx : x ∈ S) :
    (part G true S x).card + (part G false S x).card + 1 = S.card := by
  have hdis : Disjoint (part G true S x) (part G false S x) := by
    rw [disjoint_left]
    intro y h₁ h₂
    exact ((in_part G |>.mp h₂).2.2 : ¬ G.Adj x y) ((in_part G |>.mp h₁).2.2)
  have hu : part G true S x ∪ part G false S x = S.erase x := by
    ext y
    simp only [mem_union, in_part, mem_erase, rel, Bool.false_eq_true, if_false, if_true]
    tauto
  rw [← card_union_of_disjoint hdis, hu, card_erase_of_mem hx]
  have := card_pos.mpr (show S.Nonempty from ⟨x,hx⟩)
  omega
private lemma ramsey33 {S} (hc : bound G true S 2) (hi : bound G false S 2) :
    S.card ≤ 5 := by
  by_contra! h
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < S.card by omega)
  have hN : homogeneous G false (part G true S x) :=
    homog_of_bound_one G (b := false) (bound_part G hc hx)
  have hA : homogeneous G true (part G false S x) :=
    homog_of_bound_one G (b := true) (bound_part G hi hx)
  have := hi _ (part_sub G _ _ _) hN
  have := hc _ (part_sub G _ _ _) hA
  have := part_sizes G hx
  omega

private def arcs (S T : Vertices) : ℕ := ∑ x ∈ S, (part G true T x).card
private lemma part_true_eq (T x) : part G true T x = T.filter (G.Adj x) := by
  ext y
  simp only [in_part, mem_filter, rel, if_true]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.ne.symm,h.2⟩⟩
private lemma arcs_sum (S T) :
    arcs G S T = ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
  simp only [arcs, part_true_eq, card_eq_sum_ones, sum_filter]
private lemma arcs_sym (S T) : arcs G S T = arcs G T S := by
  rw [arcs_sum, arcs_sum, sum_comm]
  simp only [G.adj_comm]
private lemma arcs_add_left {S T : Vertices} (h : Disjoint S T) (U) :
    arcs G (S ∪ T) U = arcs G S U + arcs G T U := sum_union h
private lemma arcs_add_right {S T : Vertices} (h : Disjoint S T) (U) :
    arcs G U (S ∪ T) = arcs G U S + arcs G U T := by
  rw [arcs_sym, arcs_add_left G h, arcs_sym G S, arcs_sym G T]
private lemma arcs_floor {S T : Vertices} {k : ℕ}
    (h : ∀ x ∈ S, k ≤ (part G true T x).card) : S.card * k ≤ arcs G S T := by
  simpa [arcs] using (sum_le_sum h)
private lemma arcs_ceiling {S T : Vertices} {k : ℕ}
    (h : ∀ x ∈ S, (part G true T x).card ≤ k) : arcs G S T ≤ S.card * k := by
  simpa [arcs] using (sum_le_sum h)
private lemma arcs_card (S T) :
    arcs G S T = ((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card := by
  rw [arcs_sum, card_eq_sum_ones, sum_filter, sum_product]
private lemma arcs_even (S) : Even (arcs G S S) := by
  have H := (G.induce (↑S : Set V)).two_mul_card_edgeFinset
  rw [arcs_card]
  let f : ((↑S : Set V) × (↑S : Set V)) → (V × V) := fun p => (p.1.1, p.2.1)
  have hcard : (univ.filter (fun p : (↑S : Set V) × (↑S : Set V) =>
      (G.induce (↑S : Set V)).Adj p.1 p.2)).card =
      ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card := by
    apply card_bij (fun p _ => f p)
    · intro p hp
      exact mem_filter.mpr ⟨mem_product.mpr ⟨p.1.2,p.2.2⟩,(mem_filter.mp hp).2⟩
    · intro p hp q hq h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
    · rintro ⟨x,y⟩ h
      obtain ⟨hm,ha⟩ := mem_filter.mp h
      obtain ⟨hx,hy⟩ := mem_product.mp hm
      exact ⟨(⟨x,hx⟩,⟨y,hy⟩),mem_filter.mpr ⟨mem_univ _,ha⟩,rfl⟩
  rw [← hcard, ← H]
  exact even_two_mul _

private lemma part_mono {S T} (h : S ⊆ T) (b x) : part G b S x ⊆ part G b T x := by
  intro y hy
  obtain ⟨hy,hn,hr⟩ := (in_part G).mp hy
  exact (in_part G).mpr ⟨h hy,hn,hr⟩
private lemma part_sizes_out {S x} (hx : x ∉ S) :
    (part G true S x).card + (part G false S x).card = S.card := by
  have he (b) : part G b (insert x S) x = part G b S x := by
    ext y
    simp only [in_part, mem_insert]
    tauto
  have h := part_sizes G (mem_insert_self x S)
  rw [he, he, card_insert_of_notMem hx] at h
  omega
private lemma local_degree_bounds {S} (hc : bound G true S 3) (hi : bound G false S 2)
    {x} (hx : x ∈ S) :
    (part G true S x).card ≤ 5 ∧ (part G false S x).card ≤ 3 :=
  ⟨ramsey33 G (bound_part G hc hx) (bound_mono G hi (part_sub G _ _ _)),
   hc _ (part_sub G _ _ _) (homog_of_bound_one G (b := true) (bound_part G hi hx))⟩

private lemma ramsey43 {S} (hc : bound G true S 3) (hi : bound G false S 2) :
    S.card ≤ 8 := by
  by_contra! h
  obtain ⟨T,ht,hn⟩ := exists_subset_card_eq (show 9 ≤ S.card by omega)
  have he (x) (hx : x ∈ T) : (part G true T x).card = 5 := by
    obtain ⟨ha,hb⟩ := local_degree_bounds G (bound_mono G hc ht) (bound_mono G hi ht) hx
    have := part_sizes G hx
    omega
  have hh : arcs G T T = 45 := by
    unfold arcs
    calc
      _ = ∑ _ ∈ T, 5 := sum_congr rfl he
      _ = _ := by simp [hn]
  obtain ⟨n,hne⟩ := arcs_even G T
  omega

private def sparseFive : Prop := ∀ S : Vertices, S.card = 5 → arcs G S S ≤ 14

private lemma clique_arcs {S} (hs : homogeneous G true S) :
    arcs G S S = S.card * (S.card - 1) := by
  unfold arcs
  calc
    _ = ∑ _ ∈ S, (S.card - 1) := by
      apply sum_congr rfl
      intro x hx
      have h : part G true S x = S.erase x := by
        ext y
        constructor
        · intro hy
          obtain ⟨hm, hn, _⟩ := (in_part G).mp hy
          exact mem_erase.mpr ⟨hn,hm⟩
        · intro hy
          obtain ⟨hn,hm⟩ := mem_erase.mp hy
          exact (in_part G).mpr ⟨hm,hn,hs x hx y hm hn.symm⟩
      rw [h,card_erase_of_mem hx]
    _ = _ := by simp
private lemma no_five_clique (hf : sparseFive G) (S) : bound G true S 4 := by
  intro T _ hh
  by_contra! h
  obtain ⟨Y,hy,hn⟩ := exists_subset_card_eq (show 5 ≤ T.card by omega)
  have := hf Y hn
  rw [clique_arcs G (homog_mono G hh hy), hn] at this
  omega
private lemma arcs_singleton (x T) : arcs G {x} T = (part G true T x).card := by simp [arcs]
private lemma arcs_diag_single (x) : arcs G {x} {x} = 0 := by simp [arcs_singleton,part]
private lemma arcs_partition {S T : Vertices} (h : Disjoint S T) :
    arcs G (S ∪ T) (S ∪ T) = arcs G S S + arcs G T T + 2 * arcs G S T := by
  rw [arcs_add_left G h,arcs_add_right G h,arcs_add_right G h,arcs_sym G T S]
  omega
private lemma clique_exit {Y} (hf : sparseFive G) (hy : Y.card = 4)
    (hcl : homogeneous G true Y) {x} (hx : x ∉ Y) : (part G true Y x).card ≤ 1 := by
  have hdis : Disjoint {x} Y := disjoint_singleton_left.mpr hx
  have hsize : ({x} ∪ Y).card = 5 := by rw [card_union_of_disjoint hdis, card_singleton, hy]
  have h := hf _ hsize
  rw [arcs_partition G hdis,arcs_diag_single,arcs_singleton,clique_arcs G hcl,hy] at h
  omega
private lemma avoid_two {Y} (hf : sparseFive G) (hy : Y.card = 4)
    (hcl : homogeneous G true Y) {u v} (hu : u ∉ Y) (hv : v ∉ Y) :
    2 ≤ (part G false (part G false Y u) v).card := by
  have hau := clique_exit G hf hy hcl hu
  have hav := clique_exit G hf hy hcl hv
  have h₁ := part_sizes_out G hu
  have h₂ := part_sizes_out G (S := part G false Y u)
    (fun hm => hv (part_sub G _ _ _ hm))
  have h₃ := card_le_card (part_mono G (part_sub G false Y u) true v)
  omega
private lemma split_cliques {S Y} (hf : sparseFive G) (hi : bound G false S 2)
    (hY : Y ⊆ S) (hy : Y.card = 4) (hcl : homogeneous G true Y) :
    homogeneous G true (S \ Y) := by
  intro u hu v hv hn
  obtain ⟨hus,huo⟩ := mem_sdiff.mp hu
  obtain ⟨hvs,hvo⟩ := mem_sdiff.mp hv
  by_contra hna
  have hn₁ : v ∈ part G false S u := (in_part G).mpr ⟨hvs,hn.symm,hna⟩
  have hpart := bound_part G hi hus
  have hpart' : bound G false (part G false (part G false S u) v) 0 :=
    bound_part G hpart hn₁
  obtain ⟨z,hz⟩ := card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2)
    (avoid_two G hf hy hcl huo hvo))
  have hz' := part_mono G (part_mono G hY false u) false v hz
  have hh := hpart' {z} (singleton_subset_iff.mpr hz') (by
    intro i hi j hj hij
    simp only [mem_singleton] at hi hj
    exact (hij (hi.trans hj.symm)).elim)
  simp at hh

private lemma local_ramsey {S} (hf : sparseFive G) (hi : bound G false S 2) :
    S.card ≤ 8 := by
  by_cases hc : bound G true S 3
  · exact ramsey43 G hc hi
  unfold bound at hc
  push Not at hc
  obtain ⟨T,ht,hT,hn⟩ := hc
  obtain ⟨Y,hy,hY⟩ := exists_subset_card_eq (show 4 ≤ T.card by omega)
  have hsub := hy.trans ht
  have hz := no_five_clique G hf S _ sdiff_subset
    (split_cliques G hf hi hsub hY (homog_mono G hT hy))
  rw [card_sdiff_of_subset hsub, hY] at hz
  omega

private lemma partition (S : Vertices) {x} (hx : x ∈ S) :
    Disjoint (insert x (part G true S x)) (part G false S x) ∧
      insert x (part G true S x) ∪ part G false S x = S := by
  constructor
  · rw [disjoint_left]
    intro y hy hy'
    obtain ⟨_,hn,hna⟩ := (in_part G).mp hy'
    rcases mem_insert.mp hy with rfl | hm
    · exact hn rfl
    · exact hna ((in_part G).mp hm).2.2
  · ext y
    simp only [mem_union,mem_insert,in_part,rel,if_true,Bool.false_eq_true,if_false]
    by_cases he : y = x
    · subst y
      simp [hx]
    · tauto

private lemma parts_disj (S x) : Disjoint (part G true S x) (part G false S x) := by
  rw [disjoint_left]
  intro y hy hz
  exact ((in_part G).mp hz).2.2 ((in_part G).mp hy).2.2
private lemma whole_edges {A B S : Vertices} (h : Disjoint A B) (hu : A ∪ B = S) :
    arcs G A S + arcs G B B ≤ arcs G S S := by
  subst S
  rw [arcs_partition G h, arcs_add_right G h]
  omega
private lemma cap_add (S x) : (insert x (part G true S x)).card = (part G true S x).card+1 :=
  card_insert_of_notMem (self_out G true S x)
private lemma star_count (S x) :
    arcs G {x} (part G true S x) = (part G true S x).card := by
  rw [arcs_singleton]
  congr 1
  ext y
  simp only [in_part]
  tauto
private lemma splits_at {S x} (hx : x ∈ S) :
    arcs G S S =
      (2 * (part G true S x).card + arcs G (part G true S x) (part G true S x)) +
      arcs G (part G false S x) (part G false S x) +
      2 * arcs G (part G true S x) (part G false S x) := by
  obtain ⟨hd,he⟩ := partition G S hx
  have hdis : Disjoint {x} (part G true S x) := disjoint_singleton_left.mpr (self_out G true S x)
  have hz : arcs G {x} (part G false S x) = 0 := by
    rw [arcs_singleton]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨hm,_,ha⟩ := (in_part G).mp hy
    exact ((in_part G).mp hm).2.2 ha
  have h := arcs_partition G hd
  rw [he, ← singleton_union, arcs_partition G hdis, arcs_add_left G hdis,
      arcs_diag_single, star_count, hz] at h
  omega
private lemma row_split {S x} (hx : x ∈ S) :
    arcs G (part G true S x) S = (part G true S x).card +
      arcs G (part G true S x) (part G true S x) +
      arcs G (part G true S x) (part G false S x) := by
  obtain ⟨hd,he⟩ := partition G S hx
  have h := arcs_add_right G hd (part G true S x)
  have hdis : Disjoint {x} (part G true S x) := disjoint_singleton_left.mpr (self_out G true S x)
  rw [he, ← singleton_union, arcs_add_right G hdis, arcs_sym G _ {x},star_count] at h
  omega
private lemma star_cap {S x} (hf : sparseFive G) (hn : (part G true S x).card = 4) :
    arcs G (part G true S x) (part G true S x) ≤ 6 := by
  have hd : Disjoint {x} (part G true S x) := disjoint_singleton_left.mpr (self_out G true S x)
  have he : ({x} ∪ part G true S x).card = 5 := by rw [card_union_of_disjoint hd,card_singleton, hn]
  have h := hf _ he
  rw [arcs_partition G hd,arcs_diag_single, star_count,hn] at h
  omega
private lemma no_split_eight {A y} (hy : y ∈ A) (hf : sparseFive G) (hi : bound G false A 3)
    (hn : (part G true A y).card = 4) (hx : (part G false A y).card = 8) :
    bound G true (part G false A y) 3 := by
  let N := part G true A y
  let X := part G false A y
  have hd : Disjoint N X := parts_disj G A y
  by_contra hc
  unfold bound at hc
  push Not at hc
  obtain ⟨T,ht,hcl,hsize⟩ := hc
  obtain ⟨Y,hY,h₄⟩ := exists_subset_card_eq (show 4 ≤ T.card by omega)
  have hyX : Y ⊆ X := hY.trans ht
  have hYcl := homog_mono G hcl hY
  let Z := X \ Y
  have hZcl : homogeneous G true Z :=
    split_cliques G hf (bound_part G hi hy) hyX h₄ hYcl
  have hZ : Z.card = 4 := by
    change (X \ Y).card = 4
    rw [card_sdiff_of_subset hyX,h₄]
    change X.card = 8 at hx
    omega
  have hzc : Z ⊆ X := sdiff_subset
  have hnc : ¬ homogeneous G true N := by
    intro hh
    have h := star_cap G hf hn
    change arcs G N N ≤ 6 at h
    rw [clique_arcs G hh] at h
    change N.card = 4 at hn
    rw [hn] at h
    omega
  unfold homogeneous at hnc
  push Not at hnc
  obtain ⟨u,hu,v,hv,huv,hna⟩ := hnc
  have out (w) (hw : w ∈ N) : w ∉ X := disjoint_left.mp hd hw
  have aY := avoid_two G hf h₄ hYcl (fun h => out u hu (hyX h)) (fun h => out v hv (hyX h))
  have aZ := avoid_two G hf hZ hZcl (fun h => out u hu (hzc h)) (fun h => out v hv (hzc h))
  obtain ⟨w,hw⟩ := card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) aY)
  have hwY := part_sub G _ _ _ (part_sub G _ _ _ hw)
  have hwZ : w ∉ Z := fun hh => (mem_sdiff.mp hh).2 hwY
  have hvn : v ∈ part G false A u := (in_part G).mpr ⟨part_sub G _ _ _ hv,huv.symm,hna⟩
  have hb : bound G false (part G false (part G false A u) v) 1 :=
    bound_part G (bound_part G hi (part_sub G _ _ _ hu)) hvn
  have h₁ := homog_of_bound_one G (b := true) hb
  have liftSet (U : Vertices) (hh : U ⊆ X) :
      part G false (part G false U u) v ⊆ part G false (part G false A u) v :=
    part_mono G (part_mono G (hh.trans (part_sub G false A y)) false u) false v
  have h₂ : part G false (part G false Z u) v ⊆ part G true Z w := by
    intro z hz
    have hzZ : z ∈ Z := part_sub G _ _ _ (part_sub G _ _ _ hz)
    have hne : w ≠ z := fun he => hwZ (he ▸ hzZ)
    exact (in_part G).mpr ⟨hzZ,hne.symm,h₁ w (liftSet Y hyX hw) z (liftSet Z hzc hz) hne⟩
  have := card_le_card h₂
  have := clique_exit G hf hZ hZcl hwZ
  omega

private lemma low_degree {x} (hf : sparseFive G) (hi : bound G false univ 4)
    (edges : arcs G univ univ ≤ 68) (low : (part G true univ x).card ≤ 3)
    (minimum : ∀ z ∈ univ, (part G true univ x).card ≤ (part G true univ z).card) : False := by
  let M := part G true univ x
  let A := part G false univ x
  let B := insert x M
  have h₁ : M.card + A.card + 1 = 17 := by simpa [M,A] using part_sizes G (mem_univ x)
  have h₂ : B.card = M.card+1 := cap_add G _ _
  have h₃ : M.card ≤ 3 := low
  have hne : A.Nonempty := card_pos.mp (by omega)
  obtain ⟨y,hy,hymin⟩ := exists_min_image A (fun z => (part G true A z).card) hne
  let N := part G true A y
  let X := part G false A y
  have h₄ : N.card + X.card + 1 = A.card := part_sizes G hy
  have h₅ : bound G false A 3 := bound_part G hi (mem_univ x)
  have h₆ : bound G false X 2 := bound_part G h₅ hy
  have h₇ : X.card ≤ 8 := local_ramsey G hf h₆
  have hd := partition G univ (mem_univ x)
  have hcut : arcs G B univ + arcs G A A ≤ arcs G univ univ := whole_edges G hd.1 hd.2
  have hB : B.card * M.card ≤ arcs G B univ := arcs_floor G (fun z _ => minimum z (mem_univ z))
  have hA : A.card * N.card ≤ arcs G A A := arcs_floor G hymin
  have h₈ : N.card ≤ 4 := by
    by_contra! hn'
    have hh := Nat.mul_le_mul_left A.card hn'
    interval_cases k : M.card <;> simp_all +arith <;> omega
  have hM : M.card = 3 := by omega
  have hN : N.card = 4 := by omega
  have hX : X.card = 8 := by omega
  have hc := no_split_eight G hy hf h₅ hN hX
  have hXX : X.card * 4 ≤ arcs G X X := by
    apply arcs_floor
    intro z hz
    have h : (part G false X z).card ≤ 3 := (local_degree_bounds G hc h₆ hz).2
    have := part_sizes G hz
    omega
  have hNN : arcs G N N ≤ 6 := star_cap G hf hN
  have hNA : N.card * N.card ≤ arcs G N A :=
    arcs_floor G (fun z hz => hymin z (part_sub G true A y hz))
  have hrow : arcs G N A = N.card + arcs G N N + arcs G N X := row_split G hy
  have hall : arcs G A A = (2*N.card + arcs G N N) + arcs G X X + 2*arcs G N X :=
    splits_at G hy
  rw [hM] at h₂ hB
  rw [h₂] at hB
  rw [hN] at hNA hrow hall
  rw [hX] at hXX
  omega

private lemma extract {b S k} (h : ¬ bound G b S k) :
    ∃ T ⊆ S, T.card = k+1 ∧ homogeneous G b T := by
  unfold bound at h
  push Not at h
  obtain ⟨U,hu,hh,hn⟩ := h
  obtain ⟨T,ht,htn⟩ := exists_subset_card_eq (show k+1 ≤ U.card by omega)
  exact ⟨T,ht.trans hu,htn,homog_mono G hh ht⟩
private lemma degrees_eq {k : ℕ} (reg : ∀ x, (part G true univ x).card = k) (S) :
    arcs G S univ = S.card * k := by
  apply Nat.le_antisymm
  · exact arcs_ceiling G (fun x _ => (reg x).le)
  · exact arcs_floor G (fun x _ => (reg x).ge)
private lemma row_le {S T x} (hx : x ∈ S) : (part G true T x).card ≤ arcs G S T :=
  single_le_sum (f := fun z => (part G true T z).card) (fun _ _ => Nat.zero_le _) hx
private lemma no_cross {S T} (h : arcs G S T = 0) {x y} (hx : x ∈ S) (hy : y ∈ T) :
    ¬ G.Adj x y := by
  intro ha
  have hh : y ∈ part G true T x := (in_part G).mpr ⟨hy,ha.ne.symm,ha⟩
  have := card_pos.mpr (show (part G true T x).Nonempty from ⟨y,hh⟩)
  have := row_le G (T := T) hx
  omega
private lemma anti_union {S T} (hs : homogeneous G false S) (ht : homogeneous G false T)
    (h : ∀ x ∈ S, ∀ y ∈ T, ¬G.Adj x y) : homogeneous G false (S ∪ T) := by
  intro x hx y hy hn
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · exact hs x hx y hy hn
  · exact h x hx y hy
  · exact fun ha => h y hy x hx ha.symm
  · exact ht x hx y hy hn
private lemma union_compl (S : Vertices) : S ∪ (univ \ S) = univ := by
  ext x
  simp only [mem_union,mem_sdiff,mem_univ,true_and,iff_true]
  exact Classical.em _
private lemma regular_no_clique (hf : sparseFive G) (hi : bound G false univ 4)
    (reg : ∀ x, (part G true univ x).card = 4) (hc : bound G true univ 3) : False := by
  let x : V := 0
  let A := part G false univ x
  let B := insert x (part G true univ x)
  have hB : B.card = 5 := by rw [show B.card = _ from cap_add G univ x,reg]
  have hA : A.card = 12 := by
    have h := part_sizes G (mem_univ x)
    rw [reg,card_univ,Fintype.card_fin] at h
    change 4 + A.card + 1 = 17 at h
    omega
  have hd := partition G univ (mem_univ x)
  have hbl : arcs G B univ = arcs G B B + arcs G B A := hd.2 ▸ arcs_add_right G hd.1 B
  have hal : arcs G A univ = arcs G A B + arcs G A A := hd.2 ▸ arcs_add_right G hd.1 A
  rw [degrees_eq G reg B,hB] at hbl
  rw [degrees_eq G reg A,hA,arcs_sym G A B] at hal
  have hbcap := hf B hB
  have hlow : ∃ y ∈ A, (part G true A y).card ≤ 3 := by
    by_contra! hn
    have hh := arcs_floor G (k := 4) (fun y hy => hn y hy)
    rw [hA] at hh
    omega
  obtain ⟨y,hy,hl⟩ := hlow
  let X := part G false A y
  have hiX : bound G false X 2 := bound_part G (bound_part G hi (mem_univ x)) hy
  have hcX := bound_mono G hc (subset_univ X)
  have hX : X.card = 8 := by
    have hu := local_ramsey G hf hiX
    have hp : (part G true A y).card + X.card + 1 = A.card := part_sizes G hy
    omega
  have hXX : X.card * 4 ≤ arcs G X X := by
    apply arcs_floor
    intro z hz
    have hh : (part G false X z).card ≤ 3 := (local_degree_bounds G hcX hiX hz).2
    have := part_sizes G hz
    omega
  let Z := univ \ X
  have hZ : Z.card = 9 := by
    change (univ \ X).card = 9
    rw [card_sdiff_of_subset (subset_univ X), card_univ, Fintype.card_fin, hX]
  have hu : X ∪ Z = univ := union_compl X
  have hdXZ : Disjoint X Z := disjoint_sdiff_self_right
  have h0 := arcs_add_right G hdXZ X
  rw [hu,degrees_eq G reg] at h0
  have hcross : arcs G X Z = 0 := by omega
  have he₁ : ¬ bound G false X 1 := by
    intro h
    have := hcX X (Subset.rfl) (homog_of_bound_one G (b := true) h)
    omega
  have he₂ : ¬ bound G false Z 2 := fun h => by have := local_ramsey G hf h; omega
  obtain ⟨U,hU,huN,hUc⟩ := extract G he₁
  obtain ⟨W,hW,hwN,hWc⟩ := extract G he₂
  have hcl := anti_union G hUc hWc (fun a ha b hb => no_cross G hcross (hU ha) (hW hb))
  have hh := hi _ (subset_univ _) hcl
  rw [card_union_of_disjoint (hdXZ.mono hU hW), huN, hwN] at hh
  omega

private lemma dominates {S} (hi : bound G false univ 4) (hs : S.card = 4)
    (hc : homogeneous G false S) {y} (hy : y ∉ S) : 1 ≤ (part G true S y).card := by
  by_contra! h
  have hz : arcs G {y} S = 0 := by rw [arcs_singleton]; omega
  have hh := homog_insert G hc (fun a ha => no_cross G hz (mem_singleton_self _) ha)
  have hbad := hi _ (subset_univ _) hh
  rw [card_insert_of_notMem hy, hs] at hbad
  omega

private lemma regular_clique {Y} (hf : sparseFive G) (hi : bound G false univ 4)
    (reg : ∀ x, (part G true univ x).card = 4) (hY : Y.card = 4)
    (hYc : homogeneous G true Y) : False := by
  let Z := univ \ Y
  have hu : Y ∪ Z = univ := union_compl Y
  have hd : Disjoint Y Z := disjoint_sdiff_self_right
  have hZ : Z.card = 13 := by
    change (univ \ Y).card = 13
    rw [card_sdiff_of_subset (subset_univ Y), card_univ, Fintype.card_fin, hY]
  have h₁ := arcs_add_right G hd Y
  rw [hu,degrees_eq G reg,clique_arcs G hYc,hY] at h₁
  have hYZ : arcs G Y Z = 4 := by omega
  have h₂ := arcs_add_right G hd Z
  rw [hu,degrees_eq G reg,hZ, arcs_sym G Z Y,hYZ] at h₂
  have hiZ : ¬ bound G false Z 3 := by
    intro h
    have hh : Z.card * 4 ≤ arcs G Z Z := by
      apply arcs_floor
      intro z hz
      have hloc : (part G false Z z).card ≤ 8 := local_ramsey G hf (bound_part G h hz)
      have := part_sizes G hz
      omega
    omega
  obtain ⟨T,hTZ,hnT,hTc⟩ := extract G hiZ
  change T.card = 4 at hnT
  let W := Z \ T
  have hW : W.card = 9 := by
    change (Z \ T).card = 9
    rw [card_sdiff_of_subset hTZ,hnT,hZ]
  have hdTW : Disjoint T W := disjoint_sdiff_self_right
  have hun : T ∪ W = Z := union_sdiff_of_subset hTZ
  have hYT : Y.card * 1 ≤ arcs G Y T := by
    apply arcs_floor
    intro a ha
    exact dominates G hi hnT hTc (fun hat => disjoint_left.mp hd ha (hTZ hat))
  have hsplit := arcs_add_right G hdTW Y
  rw [hun,hYZ] at hsplit
  rw [hY] at hYT
  have hYW : arcs G Y W = 0 := by omega
  have hYT' : arcs G Y T = 4 := by omega
  have hmin (w) (hw : w ∈ W) : 2 ≤ (part G true T w).card := by
    by_contra! hsmall
    have hwT : w ∉ T := (mem_sdiff.mp hw).2
    have hcount := part_sizes_out G hwT
    obtain ⟨Q,hQ,hQn⟩ := exists_subset_card_eq
      (show 3 ≤ (part G false T w).card by omega)
    have hQT : Q ⊆ T := hQ.trans (part_sub G _ _ _)
    have hwQ : w ∉ Q := fun h => hwT (hQT h)
    have hQZ : Q ⊆ Z := hQT.trans hTZ
    have hQcl := homog_insert G (homog_mono G hTc hQT) (fun v hv => ((in_part G).mp (hQ hv)).2.2)
    have h4 : (insert w Q).card = 4 := by rw [card_insert_of_notMem hwQ,hQn]
    have hIZ : insert w Q ⊆ Z := insert_subset (mem_sdiff.mp hw).1 hQZ
    have hdom : Y.card * 1 ≤ arcs G Y (insert w Q) := by
      apply arcs_floor
      intro a ha
      exact dominates G hi h4 hQcl (fun h => disjoint_left.mp hd ha (hIZ h))
    have hcap : arcs G Q Y ≤ Q.card * 1 := by
      apply arcs_ceiling
      intro a ha
      exact clique_exit G hf hY hYc (fun hm => disjoint_left.mp hd hm (hQZ ha))
    have hwy : arcs G {w} Y = 0 := by
      rw [arcs_singleton]
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨hy,_,ha⟩ := (in_part G).mp hy
      exact no_cross G hYW hy hw ha.symm
    have hdis : Disjoint {w} Q := disjoint_singleton_left.mpr hwQ
    rw [hY,arcs_sym G Y, ← singleton_union, arcs_add_left G hdis,hwy] at hdom
    rw [hQn] at hcap
    omega
  have hlow := arcs_floor G hmin
  rw [hW,arcs_sym G W T] at hlow
  have hrow := arcs_add_right G hd T
  rw [hu,degrees_eq G reg,hnT,arcs_sym G T Y,hYT'] at hrow
  have hrest := arcs_add_right G hdTW T
  rw [hun] at hrest
  omega

private lemma graph_result (hf : sparseFive G) (hi : bound G false univ 4)
    (edges : arcs G univ univ ≤ 68) : False := by
  obtain ⟨x,_,hm⟩ := exists_min_image univ (fun z => (part G true univ z).card)
    (show (univ : Vertices).Nonempty from ⟨0,mem_univ _⟩)
  by_cases low : (part G true univ x).card ≤ 3
  · exact low_degree G hf hi edges low hm
  have hmin (z : V) (_ : z ∈ univ) : 4 ≤ (part G true univ z).card := by
    have := hm z (mem_univ z)
    omega
  have reg (z : V) : (part G true univ z).card = 4 := by
    by_contra hn
    have hz := hmin z (mem_univ _)
    have h := sum_lt_sum hmin ⟨z, mem_univ _, (show 4 < (part G true univ z).card by omega)⟩
    change (∑ _ ∈ (univ : Vertices), 4) < arcs G univ univ at h
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at h
    omega
  by_cases hc : bound G true univ 3
  · exact regular_no_clique G hf hi reg hc
  obtain ⟨Y,_,hn,hcl⟩ := extract G hc
  exact regular_clique G hf hi reg hn hcl

private def fromBool (adj : Sym2 V → Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ adj s(x,y) = true
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma edge_account (adj : Sym2 V → Bool) (S : Vertices) :
    arcs (fromBool adj) S S +
      ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card =
        S.card * S.card - S.card := by
  have h := card_filter_add_card_filter_not (s := S.offDiag)
    (fun p : V × V => adj s(p.1,p.2) = true)
  have h₁ : S.offDiag.filter (fun p => adj s(p.1,p.2) = true) =
      (S ×ˢ S).filter (fun p => (fromBool adj).Adj p.1 p.2) := by
    ext p
    rw [mem_filter, mem_filter, mem_offDiag, mem_product]
    change (_ ∧ _) ↔ _ ∧ p.1 ≠ p.2 ∧ adj s(p.1,p.2) = true
    tauto
  have h₂ : S.offDiag.filter (fun p => ¬ adj s(p.1,p.2) = true) =
      (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false) := by
    ext p
    simp only [mem_filter, mem_offDiag, mem_product, Bool.not_eq_true]
    tauto
  rw [h₁,h₂,offDiag_card] at h
  rwa [arcs_card]

private theorem completeGraphLemma : OMA.R_Erdos617_erdos_617_R1.H1 := by
  intro adj hedges
  let G := fromBool adj
  by_contra hbad
  have avoid (S : Vertices) (hn : S.card = 5) :
      ¬ ((∀ x ∈ S, ∀ y ∈ S, x ≠ y → adj s(x,y) = false) ∨
       ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card < 6) :=
    fun h => hbad ⟨S,hn,h⟩
  have hi : bound G false univ 4 := by
    by_contra h
    obtain ⟨S,_,hn,hh⟩ := extract G h
    apply avoid S hn
    left
    intro x hx y hy hne
    have ha : ¬ (x ≠ y ∧ adj s(x,y) = true) := hh x hx y hy hne
    cases he : adj s(x,y)
    · rfl
    · exact (ha ⟨hne,he⟩).elim
  have hf : sparseFive G := by
    intro S hn
    have h₁ := edge_account adj S
    change arcs G S S + _ = _ at h₁
    rw [hn] at h₁
    have h₂ : 6 ≤ ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card :=
      Nat.le_of_not_gt (fun h => avoid S hn (Or.inr h))
    omega
  apply graph_result G hf hi
  rw [arcs_card]
  rw [univ_product_univ]
  have heq : (univ.filter (fun p : V × V => G.Adj p.1 p.2)) =
      (univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = true)) := by
    ext p
    rw [mem_filter, mem_filter]
    rfl
  rwa [heq]

end
end Graph617

theorem OMA.solution : OMA.R_Erdos617_erdos_617_R1.H1 := Graph617.completeGraphLemma
