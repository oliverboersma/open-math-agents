import FormalConjectures.ErdosProblems.«159»

/-!
# Degree pruning and triangle packings for the four-cycle versus clique Ramsey problem

In a four-cycle-free graph, a neighbourhood induces a matching and isolated vertices.
Picking an independent set there bounds every degree by twice the independence number.
Greedily pick low-degree vertices and delete their closed neighbourhoods. The chosen
vertices are independent, so few vertices are lost before the minimum-degree condition
holds. In the remaining core take a maximal packing of vertex-disjoint triangles.
If it covers less than half the core, prune the triangle-free remainder once more.
Otherwise keep the core and packing. At most one edge joins any two packed triangles:
two edges with different endpoints give a four-cycle, and a common endpoint would
have two neighbours in a triangle to which it does not belong.

Thus a polynomial gain in the two restricted classes suffices. The current classical
upper estimate of Szemerédi has a logarithmic gain; neither new hypothesis assumes
that it already gives a fixed positive power saving.
-/
namespace OMA.R_Erdos159_erdos_159_R1
open SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ A ∧
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (∀ x ∈ S, S.card ≤ 16*n*((S.filter (G.Adj x)).card+1) ∧
        (S.filter (G.Adj x)).card ≤ 2*(n-1)) →
      (∀ B ⊆ S, ¬ G.IsNClique 3 B) →
      (S.card : ℝ) ≤ A*(n:ℝ)^(2-ε)

def H2 : Prop :=
  ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ A ∧
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (∀ x ∈ S, S.card ≤ 16*n*((S.filter (G.Adj x)).card+1) ∧
        (S.filter (G.Adj x)).card ≤ 2*(n-1)) →
      (∃ F : Finset (Finset (Fin m)), S.card ≤ 2*(F.biUnion id).card ∧
        (∀ B ∈ F, B ⊆ S ∧ G.IsNClique 3 B) ∧
        (∀ U ∈ F, ∀ W ∈ F, U ≠ W → Disjoint U W ∧
          ∀ a ∈ U, ∀ c ∈ U, ∀ b ∈ W, ∀ d ∈ W,
            G.Adj a b → G.Adj c d → a = c ∧ b = d)) →
      (S.card : ℝ) ≤ A*(n:ℝ)^(2-ε)

variable {V : Type} [Fintype V]

private lemma four_cycle (G : SimpleGraph V) {a b c d : V}
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
    fin_cases i <;> fin_cases j <;> simp_all [f] <;> grind⟩⟩

private lemma no_second (G : SimpleGraph V) (free : ¬ (cycleGraph 4).IsContained G)
    {v x y z : V} (vy : G.Adj v y) (vz : G.Adj v z) (xv : x ≠ v)
    (xy : G.Adj x y) (xz : G.Adj x z) : y = z := by
  by_contra ne
  exact free (four_cycle G xy vy.symm vz xz.symm xv ne)

private lemma peel (G : SimpleGraph V) (S : Finset V) (d : ℕ) :
    ∃ I T : Finset V, I ⊆ S ∧ T ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      (∀ x ∈ T, d < (T.filter (G.Adj x)).card) ∧
      S.card ≤ T.card + (d+1)*I.card := by
  classical
  by_cases h : ∀ x ∈ S, d < (S.filter (G.Adj x)).card
  · exact ⟨∅,S,by simp,le_rfl,by simp,h,by simp⟩
  push Not at h
  obtain ⟨x,hx,small⟩ := h
  let B := insert x (S.filter (G.Adj x))
  let U := S \ B
  have xb : x ∈ B := Finset.mem_insert_self _ _
  have sub : U ⊆ S := Finset.sdiff_subset
  have xu : x ∉ U := fun h => (Finset.mem_sdiff.mp h).2 xb
  have lt : U.card < S.card := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr
    ⟨sub, fun eq => xu (eq ▸ hx)⟩)
  obtain ⟨I,T,iS,tS,ind,dense,card⟩ := peel G U d
  have split : S = U ∪ B := (Finset.sdiff_union_of_subset
    (show B ⊆ S from Finset.insert_subset hx (Finset.filter_subset _ _))).symm
  have bc : B.card ≤ d+1 := (Finset.card_insert_le x _).trans (by omega)
  have all := Finset.card_union_le U B
  rw [← split] at all
  refine ⟨insert x I,T,Finset.insert_subset hx (iS.trans sub),tS.trans sub,?_,dense,?_⟩
  · intro a ha b hb hab
    change a ∈ insert x I at ha
    change b ∈ insert x I at hb
    have av (y) (hy : y ∈ I) : ¬ G.Adj x y := fun e =>
      (Finset.mem_sdiff.mp (iS hy)).2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨sub (iS hy),e⟩))
    rcases Finset.mem_insert.mp ha with eax | ha'
    · subst a
      rcases Finset.mem_insert.mp hb with ebx | hb'
      · exact (hab ebx.symm).elim
      · exact av _ hb'
    · rcases Finset.mem_insert.mp hb with ebx | hb'
      · subst b; exact fun e => av _ ha' e.symm
      · exact ind ha' hb' hab
  · rw [Finset.card_insert_of_notMem (fun h => xu (iS h)),Nat.mul_succ]
    omega
termination_by S.card

private lemma indep_lt (G : SimpleGraph V) (n : ℕ)
    (free : ¬ (completeGraph (Fin n)).IsContained Gᶜ) (I : Finset V)
    (hi : G.IsIndepSet (I : Set V)) : I.card < n := by
  by_contra! h
  obtain ⟨J,sub,card⟩ := Finset.exists_subset_card_eq h
  apply free
  apply ((Gᶜ).not_cliqueFree_iff_top_isContained n).mp
  intro cf
  rw [← isClique_compl] at hi
  exact cf J ⟨SimpleGraph.IsClique.subset sub hi,card⟩

private lemma degree_bound (G : SimpleGraph V) (n : ℕ)
    (free : ¬ (cycleGraph 4).IsContained G) (ind : ¬ (completeGraph (Fin n)).IsContained Gᶜ)
    (x : V) : G.degree x ≤ 2*(n-1) := by
  classical
  obtain ⟨I,T,isub,tsub,indep,dense,card⟩ := peel G (G.neighborFinset x) 1
  have empty : T = ∅ := by
    by_contra h
    obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have card₂ := dense v hv
    obtain ⟨y,hy,z,hz,ne⟩ := Finset.one_lt_card.mp card₂
    obtain ⟨yt,vy⟩ := Finset.mem_filter.mp hy
    obtain ⟨zt,vz⟩ := Finset.mem_filter.mp hz
    exact ne (no_second G free ((G.mem_neighborFinset _ _).mp (tsub yt))
      ((G.mem_neighborFinset _ _).mp (tsub zt)) ((G.mem_neighborFinset _ _).mp (tsub hv)).ne.symm vy vz)
  have hi := indep_lt G n ind I indep
  rw [empty,Finset.card_empty,zero_add,G.card_neighborFinset_eq_degree] at card
  omega

private lemma packing (G : SimpleGraph V) (T : Finset V) :
    ∃ F : Finset (Finset V), (∀ B ∈ F, B ⊆ T ∧ G.IsNClique 3 B) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧
      ∀ B ⊆ T \ F.biUnion id, ¬ G.IsNClique 3 B := by
  classical
  let pool := (T.powerset.filter (G.IsNClique 3)).powerset.filter
    (fun F => ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
  obtain ⟨F,hF,maxF⟩ := Finset.exists_max_image pool Finset.card
    (show pool.Nonempty from ⟨∅,by simp [pool]⟩)
  obtain ⟨good,sep⟩ := Finset.mem_filter.mp hF
  have all (B) (hb : B ∈ F) := Finset.mem_filter.mp (Finset.mem_powerset.mp good hb)
  refine ⟨F,fun B hb => ⟨Finset.mem_powerset.mp (all B hb).1,(all B hb).2⟩,sep,?_⟩
  intro B sub triangle
  have dis (A) (ha : A ∈ F) : Disjoint B A := by
    apply Finset.disjoint_left.mpr
    intro x hx hxa
    exact (Finset.mem_sdiff.mp (sub hx)).2 (Finset.mem_biUnion.mpr ⟨A,ha,hxa⟩)
  have fresh : B ∉ F := by
    intro hb
    have hcard := triangle.card_eq
    obtain ⟨b,hb'⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
    exact Finset.disjoint_left.mp (dis _ hb) hb' hb'
  have hInsert : insert B F ∈ pool := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      apply Finset.insert_subset _ (Finset.mem_powerset.mp good)
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (sub.trans Finset.sdiff_subset),triangle⟩
    · intro a ha b hb ne
      rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact (ne rfl).elim
      · exact dis _ hb'
      · exact (dis _ ha').symm
      · exact sep _ ha' _ hb' ne
  have bound := maxF _ hInsert
  rw [Finset.card_insert_of_notMem fresh] at bound
  omega

private lemma outside (G : SimpleGraph V) (free : ¬ (cycleGraph 4).IsContained G)
    {B : Finset V} (tri : G.IsNClique 3 B) {x u v : V} (hx : x ∉ B)
    (hu : u ∈ B) (hv : v ∈ B) (xu : G.Adj x u) (xv : G.Adj x v) : u = v := by
  classical
  by_contra ne
  have hv' : v ∈ B.erase u := Finset.mem_erase.mpr ⟨Ne.symm ne,hv⟩
  have h1 := Finset.card_erase_add_one hu
  have h2 := Finset.card_erase_add_one hv'
  obtain ⟨w,hw⟩ := Finset.card_pos.mp
    (show 0 < ((B.erase u).erase v).card by have := tri.card_eq; omega)
  obtain ⟨wv,hw'⟩ := Finset.mem_erase.mp hw
  obtain ⟨wu,wb⟩ := Finset.mem_erase.mp hw'
  exact ne (no_second G free (tri.isClique wb hu wu) (tri.isClique wb hv wv)
    (fun (e : x = w) => hx (by simpa [e] using wb)) xu xv)

private lemma cross_unique (G : SimpleGraph V) (free : ¬ (cycleGraph 4).IsContained G)
    {A B : Finset V} (ta : G.IsNClique 3 A) (tb : G.IsNClique 3 B) (sep : Disjoint A B)
    {a c b d : V} (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) (hd : d ∈ B)
    (ab : G.Adj a b) (cd : G.Adj c d) : a = c ∧ b = d := by
  have apart := Finset.disjoint_left.mp sep
  by_cases h : a = c
  · subst c; exact ⟨rfl,outside G free tb (apart ha) hb hd ab cd⟩
  by_cases j : b = d
  · subst d
    exact (h (outside G free ta (fun e => apart e hb) ha hc ab.symm cd.symm)).elim
  exact (free (four_cycle G ab (tb.isClique hb hd j) cd.symm (ta.isClique hc ha (Ne.symm h))
    (fun e => apart ha (e ▸ hd)) (fun e => apart hc (e ▸ hb)))).elim

private lemma fragment (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n)
    (big : 16*n ≤ Fintype.card V) (free : ¬ (cycleGraph 4).IsContained G)
    (ind : ¬ (completeGraph (Fin n)).IsContained Gᶜ) :
    ∃ S : Finset V, Fintype.card V ≤ 4*S.card ∧
      (∀ x ∈ S, S.card ≤ 16*n*((S.filter (G.Adj x)).card+1) ∧
        (S.filter (G.Adj x)).card ≤ 2*(n-1)) ∧
      ((∀ B ⊆ S, ¬ G.IsNClique 3 B) ∨
       ∃ F : Finset (Finset V), S.card ≤ 2*(F.biUnion id).card ∧
         (∀ B ∈ F, B ⊆ S ∧ G.IsNClique 3 B) ∧
         (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B ∧
           ∀ a ∈ A, ∀ c ∈ A, ∀ b ∈ B, ∀ d ∈ B, G.Adj a b → G.Adj c d → a = c ∧ b = d)) := by
  classical
  let N := Fintype.card V
  let d := N/(16*n)
  have den : 0 < 16*n := by omega
  have hdl : d*(16*n) ≤ N := Nat.div_mul_le_self _ _
  have hdr : N < (d+1)*(16*n) := by
    have hmod := Nat.mod_lt N den
    have hdiv := Nat.mod_add_div N (16*n)
    change N < (N/(16*n)+1)*(16*n)
    rw [Nat.add_mul,one_mul,Nat.mul_comm (N/(16*n))]
    omega
  have loss (I : Finset V) (hi : G.IsIndepSet I) : 8*((d+1)*I.card) ≤ N := by
    have hlt := indep_lt G n ind I hi
    have hmul := Nat.mul_le_mul_left (d+1) hlt.le
    change 16*n ≤ N at big
    nlinarith only [hmul,hdl,big]
  have window (S : Finset V) (dense : ∀ x ∈ S, d < (S.filter (G.Adj x)).card) (x) (hx : x ∈ S) :
      S.card ≤ 16*n*((S.filter (G.Adj x)).card+1) ∧ (S.filter (G.Adj x)).card ≤ 2*(n-1) := by
    have sN : S.card ≤ N := Finset.card_le_univ _
    have hi := Nat.mul_le_mul_left (16*n) (Nat.succ_le_succ (dense _ hx).le)
    have inc : S.filter (G.Adj x) ⊆ G.neighborFinset x :=
      fun y hy => (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hy).2
    refine ⟨?_, (Finset.card_le_card inc).trans (degree_bound G n free ind x)⟩
    rw [Nat.mul_comm (d+1)] at hdr
    exact sN.trans (hdr.le.trans hi)
  obtain ⟨I,T,_,_,hI,dense,card⟩ := peel G Finset.univ d
  rw [Finset.card_univ] at card
  change N ≤ _ at card
  have lost := loss I hI
  obtain ⟨F,tri,sep,rest⟩ := packing G T
  by_cases many : T.card ≤ 2*(F.biUnion id).card
  · refine ⟨T,by change N ≤ _; omega,window T dense,Or.inr ⟨F,many,tri,?_⟩⟩
    intro A ha B hb ne
    refine ⟨sep _ ha _ hb ne,?_⟩
    intro a aA c cA b bB d dB ab cd
    exact cross_unique G free (tri A ha).2 (tri B hb).2 (sep _ ha _ hb ne) aA cA bB dB ab cd
  · let R := T \ F.biUnion id
    have count : T.card ≤ R.card + (F.biUnion id).card := Finset.card_le_card_sdiff_add_card
    obtain ⟨J,U,_,sub,hJ,denseU,cardU⟩ := peel G R d
    have lost' := loss J hJ
    refine ⟨U,by change N ≤ _; omega,window U denseU,Or.inl ?_⟩
    intro B inc
    exact rest _ (inc.trans sub)

private lemma ramsey_cap (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (cap : ∀ m : ℕ, ∀ G : SimpleGraph (Fin m),
      ¬ (cycleGraph 4).IsContained G → ¬ (completeGraph (Fin n)).IsContained Gᶜ → (m : ℝ) ≤ L) :
    (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) ≤ L+2 := by
  let m := ⌈L⌉₊+1
  have large : L < (m : ℝ) := by
    have := Nat.le_ceil L
    dsimp [m]; push_cast; linarith
  have good (G : SimpleGraph (Fin m)) : (cycleGraph 4).IsContained G ∨
      (completeGraph (Fin n)).IsContained Gᶜ := by
    by_cases hc : (cycleGraph 4).IsContained G
    · exact Or.inl hc
    · apply Or.inr
      by_contra hn
      exact large.not_ge (cap m G hc hn)
  have hr : graphRamsey (cycleGraph 4) (completeGraph (Fin n)) ≤ m := Nat.sInf_le good
  have lower : (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) ≤ (m:ℝ) := by exact_mod_cast hr
  apply lower.trans
  dsimp [m]; push_cast
  have := Nat.ceil_lt_add_one hL
  linarith

theorem main : H1 → H2 → type_of% @Erdos159.erdos_159 := by
  rintro ⟨e,A,ep,eu,hA,first⟩ ⟨f,B,fp,fu,hB,second⟩
  let c := min e f
  have hc : 0 < c := lt_min ep fp
  refine ⟨c,hc,18+4*(A+B),?_⟩
  intro n hn
  let X := (n:ℝ)^(2-c)
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have cu : c ≤ 1 := (min_le_left _ _).trans eu
  have nx : (n:ℝ) ≤ X := by
    calc
      (n:ℝ) = (n:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le n1 (by linarith)
  have px : 0 ≤ X := (Nat.cast_nonneg _).trans nx
  have cap := ramsey_cap n ((16+4*(A+B))*X) (mul_nonneg (by linarith) px) (by
    intro m G free ind
    by_cases large : 16*n ≤ m
    · obtain ⟨S,size,window,cases⟩ := fragment G n hn (by simpa using large) free ind
      have size' : (m:ℝ) ≤ 4*(S.card:ℝ) := by
        have h : m ≤ 4*S.card := by simpa using size
        exact_mod_cast h
      have small : (S.card:ℝ) ≤ (A+B)*X := by
        rcases cases with low | packed
        · have p : (n:ℝ)^(2-e) ≤ X :=
            Real.rpow_le_rpow_of_exponent_le n1 (sub_le_sub_left (min_le_left _ _) _)
          exact (first n m G S hn free ind window low).trans
            ((mul_le_mul_of_nonneg_left p (by linarith)).trans (mul_le_mul_of_nonneg_right (by linarith) px))
        · have p : (n:ℝ)^(2-f) ≤ X :=
            Real.rpow_le_rpow_of_exponent_le n1 (sub_le_sub_left (min_le_right _ _) _)
          obtain ⟨F,hF,tri,sep⟩ := packed
          have key : S.card ≤ 2*(F.biUnion id).card := by
            convert hF using 4 <;> apply Subsingleton.elim
          exact (second n m G S hn free ind window ⟨F,key,tri,sep⟩).trans
            ((mul_le_mul_of_nonneg_left p (by linarith)).trans (mul_le_mul_of_nonneg_right (by linarith) px))
      nlinarith only [size',small,px]
    · have h : (m:ℝ) ≤ 16*(n:ℝ) := by exact_mod_cast Nat.le_of_not_ge large
      calc
        (m:ℝ) ≤ 16*X := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) px)
  change _ ≤ (18+4*(A+B))*X
  nlinarith only [cap,n1,nx]

end OMA.R_Erdos159_erdos_159_R1
