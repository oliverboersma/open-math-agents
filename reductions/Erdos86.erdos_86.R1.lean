import FormalConjectures.ErdosProblems.«86»
/-!
# Finite matching certificates for square-free hypercubes

A dart of a cube of dimension n+1 is counted in exactly n codimension-one faces.
This gives the classical monotonicity of the extremal edge density (see Rahil
Baber, Turán densities of hypercubes, arXiv:1201.3587). We give the counting proof
and a two-layer certificate for the open limiting density. A common edge of the
layers cannot have vertical edges at both endpoints, since that gives a square.
A matching of t common edges therefore excludes at least t vertical edges.

The finite matching estimate H2 is the remaining open step. For each precision it
requires one finite dimension and only inclusion-maximal square-free layers.
Deleting an edge from either layer can destroy at most one edge of a matching.
-/
namespace OMA.R_Erdos86_erdos_86_R1
open Finset SimpleGraph Filter
open scoped Classical


private lemma restore {n : ℕ} (i : Fin (n+1)) (v : Fin (n+1) → Bool) :
    i.insertNth (v i) (i.removeNth v) = v := by simp

private lemma count_face {n : ℕ} (G : SimpleGraph (Fin (n+1) → Bool)) (i : Fin (n+1)) (b : Bool) :
    Fintype.card (G.comap (i.insertNth (α := fun _ => Bool) b)).Dart =
      (univ.filter (fun d : G.Dart => d.fst i = b ∧ d.snd i = b)).card := by
  classical
  let ins := i.insertNth (α := fun _ => Bool) b
  let F := G.comap ins
  let T := univ.filter (fun d : G.Dart => d.fst i = b ∧ d.snd i = b)
  let send (d : F.Dart) : G.Dart := ⟨(ins d.fst,ins d.snd),d.adj⟩
  have inj : Function.Injective send := by
    intro d e h
    apply Dart.ext
    apply Prod.ext
    · exact Fin.insertNth_right_injective (α := fun _ => Bool) (p := i) b (congrArg (fun z : G.Dart => z.fst) h)
    · exact Fin.insertNth_right_injective (α := fun _ => Bool) (p := i) b (congrArg (fun z : G.Dart => z.snd) h)
  have onto (d : G.Dart) (hd : d ∈ T) : ∃ e : F.Dart, send e = d := by
    obtain ⟨hx,hy⟩ := (mem_filter.mp hd).2
    have rx : ins (i.removeNth d.fst) = d.fst := by simpa only [ins,← hx] using restore i d.fst
    have ry : ins (i.removeNth d.snd) = d.snd := by simpa only [ins,← hy] using restore i d.snd
    have ha : F.Adj (i.removeNth d.fst) (i.removeNth d.snd) := by
      change G.Adj (ins _) (ins _)
      rw [rx,ry]; exact d.adj
    exact ⟨⟨(i.removeNth d.fst,i.removeNth d.snd),ha⟩, Dart.ext _ _ (Prod.ext rx ry)⟩
  change Fintype.card F.Dart = T.card
  rw [← card_univ]
  apply card_bij (fun d _ => send d)
  · intro d _
    exact mem_filter.mpr ⟨mem_univ _, by simp [send,ins]⟩
  · exact fun _ _ _ _ h => inj h
  · intro d hd
    obtain ⟨e,he⟩ := onto d hd
    exact ⟨e,mem_univ _,he⟩
private lemma count_fixed {n : ℕ} (G : SimpleGraph (Fin (n+1) → Bool)) (i : Fin (n+1)) :
    (∑ b : Bool, Fintype.card (G.comap (i.insertNth (α := fun _ => Bool) b)).Dart) =
      ∑ d : G.Dart, if d.fst i = d.snd i then 1 else 0 := by
  classical
  rw [Fintype.sum_bool]
  simp only [count_face,card_eq_sum_ones,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  cases d.fst i <;> cases d.snd i <;> decide

private lemma face_edges {n : ℕ} (G : SimpleGraph (Fin (n+1) → Bool)) (hg : G ≤ hypercube (n+1)) :
    (∑ i : Fin (n+1), ∑ b : Bool, (G.comap (i.insertNth (α := fun _ => Bool) b)).edgeSet.ncard)
      = n * G.edgeSet.ncard := by
  classical
  have fixed (d : G.Dart) : (∑ i : Fin (n+1), if d.fst i = d.snd i then 1 else 0) = n := by
    have diff := (hypercube_adj.mp (hg d.adj))
    have partition := card_filter_add_card_filter_not (s := (univ : Finset (Fin (n+1)))) (fun i => d.fst i = d.snd i)
    rw [card_univ,Fintype.card_fin] at partition
    rw [← card_filter]
    change (univ.filter (fun j => ¬ d.fst j = d.snd j)).card = 1 at diff
    omega
  have total : (∑ i : Fin (n+1), ∑ b : Bool, Fintype.card (G.comap (i.insertNth (α := fun _ => Bool) b)).Dart) =
      Fintype.card G.Dart * n := by
    simp_rw [count_fixed]
    rw [sum_comm]
    simp [fixed]
  have cv {V : Type} [Fintype V] (J : SimpleGraph V) : Fintype.card J.Dart = 2*J.edgeSet.ncard := by
    rw [dart_card_eq_twice_card_edges,edgeFinset_card,Set.ncard_eq_toFinset_card']
    simp
  have localCard (i : Fin (n+1)) (b : Bool) :
      Fintype.card (G.comap (i.insertNth (α := fun _ => Bool) b)).Dart =
      2 * (G.comap (i.insertNth (α := fun _ => Bool) b)).edgeSet.ncard := by
    exact cv _
  simp only [localCard,cv,← mul_sum] at total
  nlinarith only [total]


private lemma face_sub {n : ℕ} (G : SimpleGraph (Fin (n+1) → Bool)) (hg : G ≤ hypercube (n+1))
    (i : Fin (n+1)) (b : Bool) : G.comap (i.insertNth (α := fun _ => Bool) b) ≤ hypercube n := by
  classical
  intro x y h
  have h' := hypercube_adj.mp (hg h)
  rw [hypercube_adj,← h']
  apply card_bij (fun j _ => i.succAbove j)
  · intro j hj
    simpa using hj
  · intro a _ b _ h
    exact i.succAbove_right_injective h
  · intro k hk
    have ne : k ≠ i := by
      rintro rfl
      simpa using hk
    obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq ne
    exact ⟨j,by simpa using hk,rfl⟩

private lemma propagate {m : ℕ} (hm : 0 < m) (c : ℝ)
    (bound : ∀ G : SimpleGraph (Fin m → Bool), G ≤ hypercube m → ¬cycleGraph 4 ⊑ G →
      2 * (G.edgeSet.ncard : ℝ) ≤ c * m * 2^m) :
    ∀ n ≥ m, ∀ G : SimpleGraph (Fin n → Bool), G ≤ hypercube n → ¬cycleGraph 4 ⊑ G →
      2 * (G.edgeSet.ncard : ℝ) ≤ c * n * 2^n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact bound
  | succ n hn ih =>
    intro G hg free
    let F (i : Fin (n+1)) (b : Bool) := G.comap (i.insertNth (α := fun _ => Bool) b)
    have each (i : Fin (n+1)) (b : Bool) := ih (F i b) (face_sub G hg i b)
      (fun cyc => free (cyc.trans ((SimpleGraph.Embedding.comap
        ⟨_,Fin.insertNth_right_injective (p := i) (α := fun _ => Bool) b⟩ G).isContained)))
    have total := sum_le_sum (s := (univ : Finset (Fin (n+1)))) (fun i _ =>
      sum_le_sum (s := (univ : Finset Bool)) (fun b _ => each i b))
    simp only [← mul_sum] at total
    have cnt : (∑ i : Fin (n+1), ∑ b : Bool, ((F i b).edgeSet.ncard : ℝ)) =
        (n:ℝ)*G.edgeSet.ncard := by exact_mod_cast face_edges G hg
    rw [cnt] at total
    simp at total
    have pos : (0:ℝ) < n := by exact_mod_cast hm.trans_le hn
    push_cast
    rw [pow_succ]
    apply le_of_mul_le_mul_left (a := (n:ℝ)) _ pos
    nlinarith only [total]


private lemma other_bits {n : ℕ} {x y : Fin (n+1) → Bool} (h : (hypercube _).Adj x y)
    {i : Fin (n+1)} (hi : x i ≠ y i) : i.removeNth x = i.removeNth y := by
  classical
  obtain ⟨k,hk⟩ := card_eq_one.mp (hypercube_adj.mp h)
  have unique (j) (hj : x j ≠ y j) : j = k := by
    have hh : j ∈ univ.filter (fun z => x z ≠ y z) := mem_filter.mpr ⟨mem_univ _,hj⟩
    simpa [hk] using hh
  funext a
  by_contra bad
  exact Fin.succAbove_ne i a ((unique _ bad).trans (unique i hi).symm)

private lemma split_edges {n : ℕ} (G : SimpleGraph (Fin (n+1) → Bool)) (hg : G ≤ hypercube _)
    (i : Fin (n+1)) :
    let ins := i.insertNth (α := fun _ => Bool)
    let C := univ.filter fun z => G.Adj (ins false z) (ins true z)
    G.edgeSet.ncard ≤ (G.comap (ins false)).edgeSet.ncard + (G.comap (ins true)).edgeSet.ncard + C.card := by
  classical
  let ins := i.insertNth (α := fun _ => Bool)
  let C := univ.filter fun z => G.Adj (ins false z) (ins true z)
  let D := univ.filter fun d : G.Dart => d.fst i ≠ d.snd i
  let f (d : G.Dart) := (d.fst i,i.removeNth d.fst)
  have restore' (v : Fin (n+1) → Bool) : ins (v i) (i.removeNth v) = v := restore i v
  have cross (d : G.Dart) (hd : d ∈ D) : i.removeNth d.fst = i.removeNth d.snd :=
    other_bits (hg d.adj) (mem_filter.mp hd).2
  have opp (d : G.Dart) (hd : d ∈ D) : d.snd i = !(d.fst i) := by
    have h := (mem_filter.mp hd).2
    change d.fst i ≠ d.snd i at h
    have lemmaB (a b : Bool) (hh : a ≠ b) : b = !a := by cases a <;> cases b <;> simp_all
    exact lemmaB _ _ h
  have bound : D.card ≤ (univ ×ˢ C : Finset (Bool × (Fin n → Bool))).card := by
    apply card_le_card_of_injOn f
    · intro d hd
      refine mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      have h : G.Adj (ins (d.fst i) (i.removeNth d.fst)) (ins (!(d.fst i)) (i.removeNth d.fst)) := by
        rw [restore',← opp d hd,cross d hd,restore']; exact d.adj
      cases hbit : d.fst i
      · simpa only [hbit,Bool.not_false,f] using h
      · simpa only [hbit,Bool.not_true,f] using h.symm
    · intro a ha b hb he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      change a.fst i = b.fst i at h₁
      change i.removeNth a.fst = i.removeNth b.fst at h₂
      apply Dart.ext
      apply Prod.ext
      · calc
          _ = ins (a.fst i) (i.removeNth a.fst) := (restore' _).symm
          _ = _ := by rw [h₁,h₂,restore']
      · calc
          _ = ins (a.snd i) (i.removeNth a.snd) := (restore' _).symm
          _ = _ := by rw [opp a ha,← cross a ha,h₁,h₂,← opp b hb,cross b hb,restore']
  simp only [card_product,card_univ,Fintype.card_bool] at bound
  have parts := card_filter_add_card_filter_not (s := (univ : Finset G.Dart)) (fun d => d.fst i = d.snd i)
  have fixed := count_fixed G i
  rw [Fintype.sum_bool,← card_filter] at fixed
  have cv {V : Type} [Fintype V] (J : SimpleGraph V) : Fintype.card J.Dart = 2*J.edgeSet.ncard := by
    rw [dart_card_eq_twice_card_edges,edgeFinset_card,Set.ncard_eq_toFinset_card']; simp
  rw [card_univ,cv] at parts
  have layer (b : Bool) : Fintype.card (G.comap (i.insertNth (α := fun _ => Bool) b)).Dart = 2*(G.comap (ins b)).edgeSet.ncard := cv _
  rw [layer,layer] at fixed
  change _ + D.card = _ at parts
  change G.edgeSet.ncard ≤ (G.comap (ins false)).edgeSet.ncard + (G.comap (ins true)).edgeSet.ncard + C.card
  change 2*(G.comap (ins true)).edgeSet.ncard + 2*(G.comap (ins false)).edgeSet.ncard = _ at fixed
  omega
private lemma four_cycle {V : Type} (G : SimpleGraph V) {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : (cycleGraph 4).IsContained G := by
  let f : Fin 4 → V := fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d
  have ne₁ := ab.ne
  have ne₂ := bc.ne
  have ne₃ := cd.ne
  have ne₄ := da.ne
  exact ⟨⟨⟨f,by
    intro i j e
    fin_cases i <;> fin_cases j <;> first
      | exact ab | exact bc | exact cd | exact da
      | exact ab.symm | exact bc.symm | exact cd.symm | exact da.symm
      | exfalso; revert e; decide⟩,by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]⟩⟩


private lemma matching_cost {n t : ℕ} (G : SimpleGraph (Fin (n+1) → Bool)) (i : Fin (n+1))
    (free : ¬cycleGraph 4 ⊑ G) (u v : Fin t → (Fin n → Bool))
    (injective : Function.Injective (fun p : Bool × Fin t => if p.1 then u p.2 else v p.2))
    (edges : ∀ j b, (G.comap (i.insertNth (α := fun _ => Bool) b)).Adj (u j) (v j)) :
    let ins := i.insertNth (α := fun _ => Bool)
    let C := univ.filter fun z => G.Adj (ins false z) (ins true z)
    C.card + t ≤ 2^n := by
  classical
  let ins := i.insertNth (α := fun _ => Bool)
  let C := univ.filter fun z => G.Adj (ins false z) (ins true z)
  have apart (x y : Fin n → Bool) : ins false x ≠ ins true y := by
    intro h
    have := congrFun h i
    simpa [ins] using this
  have miss (j : Fin t) : u j ∉ C ∨ v j ∉ C := by
    by_contra! h
    exact free (four_cycle G (edges j false) ((mem_filter.mp h.2).2) (edges j true).symm
      ((mem_filter.mp h.1).2.symm) (apart _ _) (apart _ _))
  let side (j : Fin t) : Bool := decide (u j ∉ C)
  let f (j : Fin t) := if side j then u j else v j
  have maps (j : Fin t) : f j ∈ (univ \ C) := by
    rcases miss j with hu|hv
    · simp [f,side,hu]
    · by_cases hu : u j ∈ C <;> simp [f,side,hu,hv]
  have inj : Function.Injective f := by
    intro a b e
    have eq : (side a,a) = (side b,b) := injective e
    exact congrArg Prod.snd eq
  have cnt := card_le_card_of_injOn (s := (univ : Finset (Fin t))) f (fun j _ => maps j) inj.injOn
  rw [card_univ,Fintype.card_fin,card_sdiff_of_subset (subset_univ _)] at cnt
  have cap := card_le_card (subset_univ C)
  simp at cnt cap
  change C.card + t ≤ _
  omega

private lemma maximal_layer {n : ℕ} (G : SimpleGraph (Fin n → Bool)) (hg : G ≤ hypercube n)
    (fr : ¬cycleGraph 4 ⊑ G) : ∃ L : SimpleGraph (Fin n → Bool),
      G ≤ L ∧ L ≤ hypercube n ∧ ¬cycleGraph 4 ⊑ L ∧
      ∀ J : SimpleGraph (Fin n → Bool), L ≤ J → J ≤ hypercube n → ¬cycleGraph 4 ⊑ J → J = L := by
  classical
  let Z := univ.filter (fun J : SimpleGraph (Fin n → Bool) => G ≤ J ∧ J ≤ hypercube n ∧ ¬cycleGraph 4 ⊑ J)
  obtain ⟨L,hL,opt⟩ := Z.exists_max_image (fun J => J.edgeFinset.card)
    ⟨G,mem_filter.mpr ⟨mem_univ _,le_rfl,hg,fr⟩⟩
  obtain ⟨sub,lc,lf⟩ := (mem_filter.mp hL).2
  refine ⟨L,sub,lc,lf,?_⟩
  intro J inc cub free
  have best := opt J (mem_filter.mpr ⟨mem_univ _,sub.trans inc,cub,free⟩)
  have eq := eq_of_subset_of_card_le (edgeFinset_mono inc) best
  exact le_antisymm (edgeFinset_subset_edgeFinset.mp eq.ge) inc

private lemma restrict_matching {V : Type} [Fintype V] {t : ℕ}
    (L R L' R' : SimpleGraph V) (hl : L ≤ L') (hr : R ≤ R') (u v : Fin t → V)
    (inj : Function.Injective (fun p : Bool × Fin t => if p.1 then u p.2 else v p.2))
    (h : ∀ j, L'.Adj (u j) (v j) ∧ R'.Adj (u j) (v j)) :
    ∃ (s : ℕ) (a b : Fin s → V),
      Function.Injective (fun p : Bool × Fin s => if p.1 then a p.2 else b p.2) ∧
      (∀ j, L.Adj (a j) (b j) ∧ R.Adj (a j) (b j)) ∧
      L.edgeSet.ncard + R.edgeSet.ncard + t ≤ L'.edgeSet.ncard + R'.edgeSet.ncard + s := by
  classical
  let K := univ.filter (fun j => L.Adj (u j) (v j) ∧ R.Adj (u j) (v j))
  let e := K.orderEmbOfFin rfl
  let edge (j : Fin t) := s(u j,v j)
  have edge_inj : Function.Injective edge := by
    intro i j hij
    rcases Sym2.eq_iff.mp hij with same|swap
    · exact congrArg Prod.snd (inj (show (if true then u i else v i) = (if true then u j else v j) from same.1) :
          (true,i) = (true,j))
    · have he : (true,i) = (false,j) := inj (show (if true then u i else v i) = (if false then u j else v j) from swap.1)
      exact congrArg Prod.snd he
  have cost (G J : SimpleGraph V) (sub : G ≤ J) (all : ∀ j, J.Adj (u j) (v j)) :
      (univ.filter fun j => ¬ G.Adj (u j) (v j)).card + G.edgeFinset.card ≤ J.edgeFinset.card := by
    have map : (univ.filter fun j => ¬ G.Adj (u j) (v j)).card ≤ (J.edgeFinset \ G.edgeFinset).card := by
      refine card_le_card_of_injOn edge (fun j hj => mem_sdiff.mpr ⟨mem_edgeFinset.mpr (all j),?_⟩) edge_inj.injOn
      exact fun hj' => (mem_filter.mp hj).2 (mem_edgeFinset.mp hj')
    rw [card_sdiff_of_subset (edgeFinset_mono sub)] at map
    have := card_le_card (edgeFinset_mono sub)
    omega
  have holes : univ \ K ⊆ (univ.filter fun j => ¬L.Adj (u j) (v j)) ∪
                            (univ.filter fun j => ¬R.Adj (u j) (v j)) := by
    intro j hj
    simp [K] at hj ⊢
    tauto
  have shortage := (card_le_card holes).trans (card_union_le _ _)
  rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin] at shortage
  refine ⟨K.card,fun j => u (e j),fun j => v (e j),?_,?_,?_⟩
  · rintro ⟨b,i⟩ ⟨c,j⟩ he
    have eq : (b,e i) = (c,e j) := inj he
    exact Prod.ext (congrArg (fun p : Bool × Fin t => p.1) eq) (e.injective (congrArg (fun p : Bool × Fin t => p.2) eq))
  · intro j
    exact (mem_filter.mp (K.orderEmbOfFin_mem rfl j)).2
  · have hl' := cost L L' hl (fun j => (h j).1)
    have hr' := cost R R' hr (fun j => (h j).2)
    have cv (G : SimpleGraph V) : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [edgeFinset_card,Set.ncard_eq_toFinset_card']; simp
    simp only [cv]
    omega

/-- A fixed-dimensional upper bound on square-free edge density propagates to every
larger cube. A proof by face averaging is included below. -/
def H1 : Prop := ∀ m : ℕ, 0 < m → ∀ c : ℝ,
  (∀ G : SimpleGraph (Fin m → Bool), G ≤ hypercube m → ¬cycleGraph 4 ⊑ G →
    2 * (G.edgeSet.ncard : ℝ) ≤ c * m * 2^m) →
  ∀ n ≥ m, ∀ G : SimpleGraph (Fin n → Bool), G ≤ hypercube n → ¬cycleGraph 4 ⊑ G →
    2 * (G.edgeSet.ncard : ℝ) ≤ c * n * 2^n

/-- A finite matching certificate. In some dimension, for every square-free pair of
layers one must exhibit enough disjoint common edges to pay for its excess. -/
def H2 : Prop := ∀ δ : ℝ, 0 < δ → ∃ m : ℕ,
  ∀ L R : SimpleGraph (Fin m → Bool), L ≤ hypercube m → R ≤ hypercube m →
    ¬cycleGraph 4 ⊑ L → ¬cycleGraph 4 ⊑ R →
    (∀ J : SimpleGraph (Fin m → Bool), L ≤ J → J ≤ hypercube m → ¬cycleGraph 4 ⊑ J → J = L) →
    (∀ J : SimpleGraph (Fin m → Bool), R ≤ J → J ≤ hypercube m → ¬cycleGraph 4 ⊑ J → J = R) →
    ∃ (t : ℕ) (u v : Fin t → (Fin m → Bool)),
      Function.Injective (fun p : Bool × Fin t => if p.1 then u p.2 else v p.2) ∧
      (∀ j, L.Adj (u j) (v j) ∧ R.Adj (u j) (v j)) ∧
      (L.edgeSet.ncard : ℝ) + R.edgeSet.ncard + 2^m ≤
        (1/2+δ) * ((m:ℝ)+1) * 2^m + t


theorem face_averaging : H1 := fun _ hm c => propagate hm c

theorem main : H1 → H2 → type_of% @Erdos86.erdos_86 := by
  intro lift cert ε he
  obtain ⟨m,compute⟩ := cert (ε/2) (by positivity)
  have cap (G : SimpleGraph (Fin (m+1) → Bool)) (hg : G ≤ hypercube _) (fr : ¬cycleGraph 4 ⊑ G) :
      2*(G.edgeSet.ncard : ℝ) ≤ (1/2 + ε/2) * (m+1 : ℕ) * 2^(m+1) := by
    let i : Fin (m+1) := 0
    let ins := i.insertNth (α := fun _ => Bool)
    let F := fun b => G.comap (ins b)
    have ffree (b) : ¬cycleGraph 4 ⊑ F b := fun cyc => fr (cyc.trans
      ((SimpleGraph.Embedding.comap ⟨_,Fin.insertNth_right_injective (p := i) (α := fun _ => Bool) b⟩ G).isContained))
    obtain ⟨L,extL,cubL,freeL,maxL⟩ := maximal_layer (F false) (face_sub G hg i false) (ffree false)
    obtain ⟨R,extR,cubR,freeR,maxR⟩ := maximal_layer (F true) (face_sub G hg i true) (ffree true)
    obtain ⟨k,P,Q,disj,pairs,price⟩ := compute L R cubL cubR freeL freeR maxL maxR
    obtain ⟨t,u,v,inj,hj,loss⟩ := restrict_matching (F false) (F true) L R extL extR P Q disj pairs
    have loss' : ((F false).edgeSet.ncard : ℝ) + (F true).edgeSet.ncard + k ≤
        (L.edgeSet.ncard : ℝ) + R.edgeSet.ncard + t := by exact_mod_cast loss
    have edges (j) (b : Bool) : (F b).Adj (u j) (v j) := by cases b <;> first | exact (hj j).1 | exact (hj j).2
    let C := univ.filter fun z => G.Adj (ins false z) (ins true z)
    have cost : C.card + t ≤ 2^m := matching_cost G i fr u v inj edges
    have split : G.edgeSet.ncard ≤ (F false).edgeSet.ncard + (F true).edgeSet.ncard + C.card := split_edges G hg i
    have hc : (C.card : ℝ)+t ≤ 2^m := by exact_mod_cast cost
    have hs : (G.edgeSet.ncard : ℝ) ≤ (F false).edgeSet.ncard + ((F true).edgeSet.ncard : ℝ) + C.card := by exact_mod_cast split
    push_cast
    rw [pow_succ]
    linarith
  filter_upwards [eventually_ge_atTop (m+1)] with n hn G hg hG
  by_contra free
  have bd := lift (m+1) (by omega) (1/2+ε/2) cap n hn G hg free
  have hn' : 0 < n := by omega
  have p : (2:ℝ)^n = 2 * (2:ℝ)^(n-1) := by
    conv_lhs => rw [show n = (n-1)+1 by omega,pow_succ]
    ring
  rw [p] at bd
  have pos : 0 < ε*(n:ℝ)*(2:ℝ)^(n-1) := by positivity
  nlinarith only [bd,hG,pos]

end OMA.R_Erdos86_erdos_86_R1
