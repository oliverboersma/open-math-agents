import OMAReductions.R_Erdos599_erdos_599_R1

-- Step Erdos599.erdos_599.R1.H1: hypothesis H1 of reduction Erdos599.erdos_599.R1
-- Reduction credit: @dk8827. This proof: @koolkao (original).

/-!
Informal plan (existence of a maximal wave, after Aharoni and Berger 2009, Section 3).

* A wave is a family of disjoint finite paths (lists of vertices), one from each vertex of a
  subset `D ⊆ A`, whose set `ter W` of last vertices separates `A` from `B` (every walk).
* `Qs X` is the set of vertices reachable from `A` by a walk that avoids `X`; its complement is
  the part of the graph after `X`. Every non-terminal vertex of a wave path lies in `Qs (ter W)`.
* `W ≤ W'` when `W'` keeps some paths of `W` and extends each kept path by vertices that lie
  after `ter W` and outside `ter W`. This relation is reflexive and transitive.
* Zorn: a chain of waves is bounded by the wave made of the paths that eventually stop
  changing. The terminals of this limit separate: a walk from `A` to `B` is finite, so one of
  its vertices is terminal in cofinally many waves of the chain, and a path whose end is
  terminal later in the chain is never extended in between.
* Take a maximal wave `M`, `S = ter M` and `R = (Qs S)ᶜ`. If a wave `Q` from `S` in `G[R]`
  missed a vertex of `S`, gluing `Q` onto `M` would give a wave strictly above `M` (it drops a
  path), contradicting maximality. Its terminals separate because every walk from `A` to `B`
  has a final segment that starts in `S` and stays in `R`.
-/

open SimpleGraph

namespace OMA.Erdos599H1

/-! ## Waves

A pre-wave is a set `D` of start vertices together with a list `P a` for each `a ∈ D`.
Its terminal set `ter W` is the set of last vertices.  For a vertex set `X`, `Qs X` is the
set of vertices reachable from `A` by a walk that avoids `X`; its complement is the part of
the graph "after" `X`. -/

structure PW (V : Type) where
  D : Set V
  P : V → List V

variable {V : Type}

def ter (W : PW V) : Set V := {x | ∃ a ∈ W.D, (W.P a).getLast? = some x}

def Qs (G : SimpleGraph V) (A X : Set V) : Set V :=
  {y | ∃ a ∈ A, ∃ w : G.Walk a y, ∀ z ∈ w.support, z ∉ X}

def Sep (G : SimpleGraph V) (A B X : Set V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, ∀ w : G.Walk u v, ∃ x ∈ w.support, x ∈ X

structure IsWave (G : SimpleGraph V) (A B : Set V) (W : PW V) : Prop where
  sub : W.D ⊆ A
  head : ∀ a ∈ W.D, (W.P a).head? = some a
  chain : ∀ a ∈ W.D, (W.P a).IsChain G.Adj
  nodup : ∀ a ∈ W.D, (W.P a).Nodup
  disj : ∀ a ∈ W.D, ∀ a' ∈ W.D, a ≠ a' → ∀ x ∈ W.P a, x ∉ W.P a'
  sep : Sep G A B (ter W)

/-- `W'` continues `W`: it keeps some of the paths of `W` and extends them beyond `ter W`. -/
def Le (G : SimpleGraph V) (A : Set V) (W W' : PW V) : Prop :=
  W'.D ⊆ W.D ∧ ∀ a ∈ W'.D, ∃ e, W'.P a = W.P a ++ e ∧
    ∀ v ∈ e, v ∉ Qs G A (ter W) ∧ v ∉ ter W

variable (G : SimpleGraph V) (A B : Set V)

lemma exists_walk : ∀ (l : List V) (u v : V), l.head? = some u → l.getLast? = some v →
    l.IsChain G.Adj → ∃ w : G.Walk u v, w.support = l := by
  intro l
  induction l with
  | nil => intro u v h; simp at h
  | cons x l ih =>
    intro u v hu hv hc
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hv
      subst hv
      exact ⟨Walk.nil, rfl⟩
    | cons y l =>
      rw [List.isChain_cons_cons] at hc
      rw [List.getLast?_cons_cons] at hv
      obtain ⟨w, hw⟩ := ih y v rfl hv hc.2
      exact ⟨Walk.cons hc.1 w, by simp [hw]⟩

lemma not_mem_Qs {X : Set V} {x : V} (hx : x ∈ X) : x ∉ Qs G A X := by
  rintro ⟨a, -, w, hw⟩
  exact hw x w.end_mem_support hx

lemma Qs_step {X : Set V} {y y₁ : V} (hy : y ∈ Qs G A X) (h : G.Adj y y₁) (hy₁ : y₁ ∉ X) :
    y₁ ∈ Qs G A X := by
  obtain ⟨a, ha, w, hw⟩ := hy
  refine ⟨a, ha, w.concat h, fun z hz => ?_⟩
  rw [Walk.support_concat, List.mem_append] at hz
  rcases hz with hz | hz
  · exact hw z hz
  · rw [List.mem_singleton] at hz
    subst hz
    exact hy₁

/-- Every vertex of a wave path other than its last one is reachable from `A` avoiding `ter W`. -/
lemma interior {W : PW V} (hW : IsWave G A B W) {a y : V} (ha : a ∈ W.D) (hy : y ∈ W.P a)
    (hyQ : y ∉ Qs G A (ter W)) : (W.P a).getLast? = some y := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hy
  by_cases ht : t = []
  · subst ht
    rw [hst]
    exact List.getLast?_concat
  exfalso
  apply hyQ
  have hst' : W.P a = (s ++ [y]) ++ t := by simp [hst]
  have hhead : (s ++ [y]).head? = some a := by
    have h := hW.head a ha
    rw [hst] at h
    cases s <;> simp_all
  have hchain : (s ++ [y]).IsChain G.Adj := by
    have h := hW.chain a ha
    rw [hst'] at h
    exact (List.isChain_append.1 h).1
  obtain ⟨w, hw⟩ := exists_walk G (s ++ [y]) a y hhead List.getLast?_concat hchain
  refine ⟨a, hW.sub ha, w, fun z hz hzX => ?_⟩
  rw [hw] at hz
  obtain ⟨a', ha', hla'⟩ := hzX
  have hzP : z ∈ W.P a := by rw [hst']; exact List.mem_append_left _ hz
  have haa : a' = a := by
    by_contra hne
    exact hW.disj a' ha' a ha hne z (List.mem_of_getLast? hla') hzP
  subst haa
  have hnd := hW.nodup a' ha
  rw [hst', List.nodup_append] at hnd
  rw [hst', List.getLast?_append] at hla'
  cases hlt : t.getLast? with
  | none => exact ht (List.getLast?_eq_none_iff.1 hlt)
  | some e =>
    rw [hlt] at hla'
    simp only [Option.some_or, Option.some.injEq] at hla'
    subst hla'
    exact hnd.2.2 e hz e (List.mem_of_getLast? hlt) rfl

lemma ter_after {W W' : PW V} (h : Le G A W W') {x : V} (hx : x ∈ ter W') :
    x ∉ Qs G A (ter W) := by
  obtain ⟨a', ha', hla'⟩ := hx
  obtain ⟨e, he, hev⟩ := h.2 a' ha'
  rw [he, List.getLast?_append] at hla'
  cases hle : e.getLast? with
  | none =>
    rw [hle] at hla'
    simp only [Option.none_or] at hla'
    exact not_mem_Qs G A ⟨a', h.1 ha', hla'⟩
  | some z =>
    rw [hle] at hla'
    simp only [Option.some_or, Option.some.injEq] at hla'
    subst hla'
    exact (hev z (List.mem_of_getLast? hle)).1

lemma Qs_mono {X X' : Set V} (h : ∀ x ∈ X', x ∉ Qs G A X) : Qs G A X ⊆ Qs G A X' := by
  classical
  rintro y ⟨a, ha, w, hw⟩
  refine ⟨a, ha, w, fun z hz hzX' => h z hzX' ?_⟩
  exact ⟨a, ha, w.takeUntil z hz, fun z' hz' => hw z' (w.support_takeUntil_subset_support hz hz')⟩

lemma ter_keep {W W' : PW V} (hW : IsWave G A B W) (h : Le G A W W') {v : V} (hv : v ∈ ter W)
    (hvQ : v ∉ Qs G A (ter W')) : v ∈ ter W' := by
  obtain ⟨a0, ha0, hla⟩ := hv
  obtain ⟨w, hw⟩ := exists_walk G (W.P a0) a0 v (hW.head a0 ha0) hla (hW.chain a0 ha0)
  by_contra hv'
  apply hvQ
  refine ⟨a0, hW.sub ha0, w, fun z hz hzX' => ?_⟩
  rw [hw] at hz
  have hz1 := interior G A B hW ha0 hz (ter_after G A h hzX')
  rw [hla, Option.some.injEq] at hz1
  subst hz1
  exact hv' hzX'

lemma Le_refl (W : PW V) : Le G A W W :=
  ⟨subset_rfl, fun _ _ => ⟨[], by simp, by simp⟩⟩

lemma Le_trans {W W' W'' : PW V} (hW : IsWave G A B W) (h₁ : Le G A W W') (h₂ : Le G A W' W'') :
    Le G A W W'' := by
  refine ⟨h₂.1.trans h₁.1, fun a ha => ?_⟩
  obtain ⟨e₂, he₂, hv₂⟩ := h₂.2 a ha
  obtain ⟨e₁, he₁, hv₁⟩ := h₁.2 a (h₂.1 ha)
  refine ⟨e₁ ++ e₂, by rw [he₂, he₁, List.append_assoc], fun v hv => ?_⟩
  rcases List.mem_append.1 hv with hv | hv
  · exact hv₁ v hv
  · obtain ⟨hvQ, hvX⟩ := hv₂ v hv
    refine ⟨fun hQ => hvQ (Qs_mono G A (fun x hx => ter_after G A h₁ hx) hQ), fun hX => ?_⟩
    exact hvX (ter_keep G A B hW h₁ hX hvQ)

/-- The trivial wave: every vertex of `A` is a one-vertex path. -/
def triv (A : Set V) : PW V := ⟨A, fun a => [a]⟩

lemma triv_wave : IsWave G A B (triv A) where
  sub := subset_rfl
  head := fun _ _ => rfl
  chain := fun _ _ => List.isChain_singleton _
  nodup := fun _ _ => List.nodup_singleton _
  disj := by
    intro a _ a' _ hne x hx hx'
    simp only [triv, List.mem_singleton] at hx hx'
    exact hne (hx.symm.trans hx')
  sep := fun u hu _ _ w => ⟨u, w.start_mem_support, u, hu, rfl⟩

/-- If a path of `W` ends at a vertex that is still terminal in a continuation `W'`, then
`W'` keeps that path unchanged. -/
lemma keep_path {W W' : PW V} (hW : IsWave G A B W) (h : Le G A W W') {a x : V} (ha : a ∈ W.D)
    (hla : (W.P a).getLast? = some x) (hx : x ∈ ter W') : a ∈ W'.D ∧ W'.P a = W.P a := by
  obtain ⟨a', ha', hla'⟩ := hx
  obtain ⟨e, he, hev⟩ := h.2 a' ha'
  have hxt : x ∈ ter W := ⟨a, ha, hla⟩
  have hx' : x ∈ W'.P a' := List.mem_of_getLast? hla'
  rw [he, List.mem_append] at hx'
  rcases hx' with hx' | hx'
  · have haa : a' = a := by
      by_contra hne
      exact hW.disj a' (h.1 ha') a ha hne x hx' (List.mem_of_getLast? hla)
    subst haa
    refine ⟨ha', ?_⟩
    rw [he]
    cases hle : e.getLast? with
    | none => rw [List.getLast?_eq_none_iff.1 hle, List.append_nil]
    | some z =>
      rw [he, List.getLast?_append, hle] at hla'
      simp only [Option.some_or, Option.some.injEq] at hla'
      subst hla'
      exact absurd hxt (hev z (List.mem_of_getLast? hle)).2
  · exact absurd hxt (hev x hx').2

lemma list_ub {α : Type} (r : α → α → Prop) (c : Set α)
    (hup : ∀ i ∈ c, ∀ j ∈ c, ∃ m ∈ c, r i m ∧ r j m)
    (htrans : ∀ {i j k}, i ∈ c → r i j → r j k → r i k)
    (hne : c.Nonempty) (φ : V → α → Prop) :
    ∀ l : List V, (∀ x ∈ l, ∃ j ∈ c, φ x j) → ∃ m ∈ c, ∀ x ∈ l, ∃ j ∈ c, φ x j ∧ r j m := by
  intro l
  induction l with
  | nil => intro _; exact ⟨hne.some, hne.some_mem, by simp⟩
  | cons x l ih =>
    intro h
    obtain ⟨m, hm, hml⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    obtain ⟨j, hj, hφ⟩ := h x List.mem_cons_self
    obtain ⟨m', hm', hmm, hjm⟩ := hup m hm j hj
    refine ⟨m', hm', fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨j, hj, hφ, hjm⟩
    · obtain ⟨j', hj', hφ', hr⟩ := hml y hy
      exact ⟨j', hj', hφ', htrans hj' hr hmm⟩

/-- Every chain of waves has an upper bound: take the paths that eventually stop changing. -/
lemma chain_ub (c : Set {W // IsWave G A B W})
    (hc : IsChain (fun W W' : {W // IsWave G A B W} => Le G A W.1 W'.1) c) :
    ∃ ub : {W // IsWave G A B W}, ∀ W ∈ c, Le G A W.1 ub.1 := by
  classical
  by_cases hne : c.Nonempty
  swap
  · exact ⟨⟨triv A, triv_wave G A B⟩, fun W hW => absurd ⟨W, hW⟩ hne⟩
  have hcmp : ∀ i ∈ c, ∀ j ∈ c, Le G A i.1 j.1 ∨ Le G A j.1 i.1 := by
    intro i hi j hj
    by_cases hij : i = j
    · subst hij; exact Or.inl (Le_refl G A _)
    · exact hc hi hj hij
  have hup : ∀ i ∈ c, ∀ j ∈ c, ∃ m ∈ c, Le G A i.1 m.1 ∧ Le G A j.1 m.1 := by
    intro i hi j hj
    rcases hcmp i hi j hj with h | h
    · exact ⟨j, hj, h, Le_refl G A _⟩
    · exact ⟨i, hi, Le_refl G A _, h⟩
  have htr : ∀ {i j k : {W // IsWave G A B W}}, i ∈ c → Le G A i.1 j.1 → Le G A j.1 k.1 →
      Le G A i.1 k.1 := fun {i _ _} _ h₁ h₂ => Le_trans G A B i.2 h₁ h₂
  let stable (a : V) (i : {W // IsWave G A B W}) : Prop :=
    i ∈ c ∧ a ∈ i.1.D ∧ ∀ j ∈ c, Le G A i.1 j.1 → a ∈ j.1.D ∧ j.1.P a = i.1.P a
  let L : PW V := ⟨{a | ∃ i, stable a i},
    fun a => if h : ∃ i, stable a i then (Classical.choose h).1.P a else []⟩
  have hLP : ∀ a i, stable a i → L.P a = i.1.P a := by
    intro a i hi
    have h : ∃ i, stable a i := ⟨i, hi⟩
    show (if h : ∃ i, stable a i then (Classical.choose h).1.P a else []) = i.1.P a
    rw [dif_pos h]
    have hw := Classical.choose_spec h
    obtain ⟨m, hm, hwm, him⟩ := hup _ hw.1 i hi.1
    rw [← (hw.2.2 m hm hwm).2, (hi.2.2 m hm him).2]
  have hLD : ∀ a ∈ L.D, ∀ j ∈ c, a ∈ j.1.D := by
    rintro a ⟨i, hi⟩ j hj
    rcases hcmp i hi.1 j hj with h | h
    · exact (hi.2.2 j hj h).1
    · exact h.1 hi.2.1
  have hLm : ∀ a ∈ L.D, ∀ j ∈ c, ∃ m ∈ c, Le G A j.1 m.1 ∧ m.1.P a = L.P a := by
    rintro a ⟨i, hi⟩ j hj
    obtain ⟨m, hm, hjm, him⟩ := hup j hj i hi.1
    exact ⟨m, hm, hjm, by rw [hLP a i hi, (hi.2.2 m hm him).2]⟩
  have hLwave : IsWave G A B L := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro a ⟨i, hi⟩
      exact i.2.sub hi.2.1
    · rintro a ⟨i, hi⟩
      rw [hLP a i hi]
      exact i.2.head a hi.2.1
    · rintro a ⟨i, hi⟩
      rw [hLP a i hi]
      exact i.2.chain a hi.2.1
    · rintro a ⟨i, hi⟩
      rw [hLP a i hi]
      exact i.2.nodup a hi.2.1
    · rintro a ⟨i, hi⟩ a' ⟨i', hi'⟩ hne'
      obtain ⟨m, hm, him, hi'm⟩ := hup i hi.1 i' hi'.1
      rw [hLP a i hi, hLP a' i' hi', ← (hi.2.2 m hm him).2, ← (hi'.2.2 m hm hi'm).2]
      exact m.2.disj a (hi.2.2 m hm him).1 a' (hi'.2.2 m hm hi'm).1 hne'
    · intro u hu v hv w
      have hcof : ∃ x ∈ w.support, ∀ j ∈ c, ∃ k ∈ c, Le G A j.1 k.1 ∧ x ∈ ter k.1 := by
        by_contra hno
        simp only [not_exists, not_and, not_forall] at hno
        have hno' : ∀ x ∈ w.support, ∃ j ∈ c, ∀ k ∈ c, Le G A j.1 k.1 → x ∉ ter k.1 := by
          intro x hx
          obtain ⟨j, hj, hk⟩ := hno x hx
          exact ⟨j, hj, fun k hk' hjk hxk => hk k hk' hjk hxk⟩
        obtain ⟨m, hm, hml⟩ := list_ub (fun i j : {W // IsWave G A B W} => Le G A i.1 j.1) c
          hup htr hne (fun x j => ∀ k ∈ c, Le G A j.1 k.1 → x ∉ ter k.1) w.support hno'
        obtain ⟨x, hx, hxm⟩ := m.2.sep u hu v hv w
        obtain ⟨j, -, hφ, hjm⟩ := hml x hx
        exact hφ m hm hjm hxm
      obtain ⟨x, hxw, hx⟩ := hcof
      obtain ⟨k₀, hk₀, -, hxk₀⟩ := hx hne.some hne.some_mem
      obtain ⟨a, ha, hla⟩ := hxk₀
      have hst : stable a k₀ := by
        refine ⟨hk₀, ha, fun j hj hkj => ?_⟩
        obtain ⟨k, hk, hjk, hxk⟩ := hx j hj
        obtain ⟨hak, hPk⟩ := keep_path G A B k₀.2 (htr hk₀ hkj hjk) ha hla hxk
        refine ⟨hjk.1 hak, ?_⟩
        obtain ⟨e₁, he₁, -⟩ := hkj.2 a (hjk.1 hak)
        obtain ⟨e₂, he₂, -⟩ := hjk.2 a hak
        rw [hPk, he₁, List.append_assoc] at he₂
        have : e₁ ++ e₂ = [] := by simpa using he₂
        rw [he₁, (List.append_eq_nil_iff.1 this).1, List.append_nil]
      exact ⟨x, hxw, a, ⟨k₀, hst⟩, by rw [hLP a k₀ hst]; exact hla⟩
  refine ⟨⟨L, hLwave⟩, fun i hi => ⟨fun a ha => hLD a ha i hi, fun a ha => ?_⟩⟩
  obtain ⟨m, hm, him, hmP⟩ := hLm a ha i hi
  obtain ⟨e, he, hev⟩ := him.2 a (hLD a ha m hm)
  exact ⟨e, by rw [← hmP]; exact he, hev⟩

/-- A walk that ends after `X` has a final segment that starts in `X` (or at its first vertex,
if that is already after `X`) and stays after `X`. -/
lemma suffix (X : Set V) {v : V} (hvR : v ∉ Qs G A X) :
    ∀ {y : V} (w : G.Walk y v),
      (y ∈ Qs G A X → ∃ x ∈ X, ∃ (hx : x ∉ Qs G A X)
        (w₂ : (G.induce (Qs G A X)ᶜ).Walk ⟨x, hx⟩ ⟨v, hvR⟩), ∀ z ∈ w₂.support, z.1 ∈ w.support) ∧
      (y ∉ Qs G A X → ∃ x, (x = y ∨ x ∈ X) ∧ ∃ (hx : x ∉ Qs G A X)
        (w₂ : (G.induce (Qs G A X)ᶜ).Walk ⟨x, hx⟩ ⟨v, hvR⟩), ∀ z ∈ w₂.support, z.1 ∈ w.support) := by
  intro y w
  induction w with
  | nil =>
    refine ⟨fun h => absurd h hvR, fun _ => ⟨_, Or.inl rfl, hvR, Walk.nil, ?_⟩⟩
    intro z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz ⊢
    rw [hz]
  | @cons y y₁ v' h w₁ ih =>
    have lift : ∀ x (hx : x ∉ Qs G A X) (w₂ : (G.induce (Qs G A X)ᶜ).Walk ⟨x, hx⟩ ⟨v', hvR⟩),
        (∀ z ∈ w₂.support, z.1 ∈ w₁.support) → ∀ z ∈ w₂.support, z.1 ∈ (Walk.cons h w₁).support :=
      fun _ _ _ h' z hz => by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ (h' z hz)
    constructor
    · intro hy
      by_cases hy₁ : y₁ ∈ Qs G A X
      · obtain ⟨x, hxX, hx, w₂, hw₂⟩ := (ih hvR).1 hy₁
        exact ⟨x, hxX, hx, w₂, lift x hx w₂ hw₂⟩
      · have hy₁X : y₁ ∈ X := by
          by_contra hn
          exact hy₁ (Qs_step G A hy h hn)
        obtain ⟨x, hxy, hx, w₂, hw₂⟩ := (ih hvR).2 hy₁
        refine ⟨x, ?_, hx, w₂, lift x hx w₂ hw₂⟩
        rcases hxy with rfl | hxX
        · exact hy₁X
        · exact hxX
    · intro hy
      by_cases hy₁ : y₁ ∈ Qs G A X
      · have hyX : y ∈ X := by
          by_contra hn
          exact hy (Qs_step G A hy₁ h.symm hn)
        obtain ⟨x, hxX, hx, w₂, hw₂⟩ := (ih hvR).1 hy₁
        exact ⟨x, Or.inr hxX, hx, w₂, lift x hx w₂ hw₂⟩
      · obtain ⟨x, hxy, hx, w₂, hw₂⟩ := (ih hvR).2 hy₁
        rcases hxy with rfl | hxX
        · refine ⟨y, Or.inl rfl, hy, Walk.cons (show (G.induce (Qs G A X)ᶜ).Adj ⟨y, hy⟩ ⟨x, hx⟩
            from h) w₂, ?_⟩
          intro z hz
          rw [Walk.support_cons, List.mem_cons] at hz
          rw [Walk.support_cons, List.mem_cons]
          rcases hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (hw₂ z hz)
        · exact ⟨x, Or.inr hxX, hx, w₂, lift x hx w₂ hw₂⟩

lemma suffix_main (X : Set V) (hX : Sep G A B X) {u v : V} (hu : u ∈ A) (hv : v ∈ B)
    (w : G.Walk u v) : ∃ x ∈ X, ∃ (hx : x ∉ Qs G A X) (hvR : v ∉ Qs G A X)
      (w₂ : (G.induce (Qs G A X)ᶜ).Walk ⟨x, hx⟩ ⟨v, hvR⟩), ∀ z ∈ w₂.support, z.1 ∈ w.support := by
  have hvR : v ∉ Qs G A X := by
    rintro ⟨a, ha, w', hw'⟩
    obtain ⟨x, hx, hxX⟩ := hX a ha v hv w'
    exact hw' x hx hxX
  by_cases huQ : u ∈ Qs G A X
  · obtain ⟨x, hxX, hx, w₂, hw₂⟩ := (suffix G A X hvR w).1 huQ
    exact ⟨x, hxX, hx, hvR, w₂, hw₂⟩
  · obtain ⟨x, hxy, hx, w₂, hw₂⟩ := (suffix G A X hvR w).2 huQ
    refine ⟨x, ?_, hx, hvR, w₂, hw₂⟩
    rcases hxy with rfl | hxX
    · by_contra hn
      exact huQ ⟨x, hu, Walk.nil, by simpa using hn⟩
    · exact hxX

lemma last_append {l r : List V} {z e : V} (hl : l.getLast? = some z)
    (hr : (z :: r).getLast? = some e) : (l ++ r).getLast? = some e := by
  rw [List.getLast?_append]
  cases hle : r.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff.1 hle] at hr
    simp only [List.getLast?_singleton, Option.some.injEq] at hr
    subst hr
    simpa using hl
  | some e' =>
    rw [List.getLast?_cons, hle] at hr
    simpa using hr

end OMA.Erdos599H1

open OMA.Erdos599H1 in
theorem OMA.solution : OMA.R_Erdos599_erdos_599_R1.H1 := by
  intro V G A B _
  classical
  obtain ⟨M, hM⟩ := exists_maximal_of_chains_bounded
    (r := fun W W' : {W // IsWave G A B W} => Le G A W.1 W'.1) (chain_ub G A B)
    (fun {a _ _} h₁ h₂ => Le_trans G A B a.2 h₁ h₂)
  set X := ter M.1 with hXdef
  set Q := Qs G A X with hQdef
  have hS : ∀ s : {r : (Qᶜ : Set V) | r.1 ∈ X}, ∃ a, a ∈ M.1.D ∧ (M.1.P a).getLast? = some s.1.1 :=
    fun s => s.2
  let aOf : {r : (Qᶜ : Set V) | r.1 ∈ X} → V := fun s => Classical.choose (hS s)
  have haOf : ∀ s, aOf s ∈ M.1.D ∧ (M.1.P (aOf s)).getLast? = some s.1.1 :=
    fun s => Classical.choose_spec (hS s)
  have hwalk : ∀ s, ∃ w : G.Walk (aOf s) s.1.1, w.support = M.1.P (aOf s) := fun s =>
    exists_walk G _ _ _ (M.2.head _ (haOf s).1) (haOf s).2 (M.2.chain _ (haOf s).1)
  let pOf : ∀ s, G.Walk (aOf s) s.1.1 := fun s => Classical.choose (hwalk s)
  have hpOf : ∀ s, (pOf s).support = M.1.P (aOf s) := fun s => Classical.choose_spec (hwalk s)
  refine ⟨Qᶜ, {r | r.1 ∈ X}, aOf, pOf, fun s => M.2.sub (haOf s).1, ?_, ?_, ?_, ?_⟩
  · intro s v hv hvR
    rw [hpOf] at hv
    have h := interior G A B M.2 (haOf s).1 hv hvR
    rw [(haOf s).2, Option.some.injEq] at h
    exact h.symm
  · intro s t hst
    rw [Set.disjoint_left]
    intro v hvs hvt
    have hvs' : v ∈ M.1.P (aOf s) := by rw [← hpOf]; exact hvs
    have hvt' : v ∈ M.1.P (aOf t) := by rw [← hpOf]; exact hvt
    have hne : aOf s ≠ aOf t := by
      intro heq
      apply hst
      have h1 := (haOf s).2
      rw [heq, (haOf t).2, Option.some.injEq] at h1
      exact Subtype.ext (Subtype.ext h1.symm)
    exact M.2.disj _ (haOf s).1 _ (haOf t).1 hne v hvs' hvt'
  · intro u hu v hv w _
    obtain ⟨x, hxw, hxX⟩ := M.2.sep u hu v hv w
    exact ⟨x, hxw, ⟨x, not_mem_Qs G A hxX⟩, hxX, rfl⟩
  · intro H B' T b q hbS hpath hcond hdisj hsep x₀ hx₀
    by_contra hno
    obtain ⟨tl, htl⟩ : ∃ tl : T → List V, ∀ t, tl t = (q t).support.tail.map Subtype.val :=
      ⟨_, fun _ => rfl⟩
    have hcons : ∀ t, (b t).1 :: tl t = (q t).support.map Subtype.val := by
      intro t
      rw [htl, ← List.map_cons, Walk.cons_tail_support]
    have tl1 : ∀ t, ((b t).1 :: tl t).IsChain G.Adj := by
      intro t
      rw [hcons]
      exact List.isChain_map_of_isChain Subtype.val (fun _ _ h => h) (q t).isChain_adj_support
    have tl2 : ∀ t, ((b t).1 :: tl t).Nodup := by
      intro t
      rw [hcons]
      exact ((Walk.isPath_def _).1 (hpath t)).map Subtype.val_injective
    have tl3 : ∀ t, ((b t).1 :: tl t).getLast? = some t.1.1 := by
      intro t
      rw [hcons, List.getLast?_map, List.getLast?_eq_some_getLast (q t).support_ne_nil,
        Walk.getLast_support]
      rfl
    have tl4 : ∀ t, ∀ y ∈ tl t, y ∉ Q ∧ y ∉ X := by
      intro t y hy
      rw [htl, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z.2, (hcond t).1 z hz⟩
    have tl5 : ∀ t t', t ≠ t' → ∀ y ∈ (b t).1 :: tl t, y ∉ (b t').1 :: tl t' := by
      intro t t' hne y hy hy'
      rw [hcons, List.mem_map] at hy hy'
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨z', hz', hzz⟩ := hy'
      have : z' = z := Subtype.ext hzz
      subst this
      exact Set.disjoint_left.1 (hdisj hne) hz hz'
    have tuniq : ∀ t t' : T, (b t).1 = (b t').1 → t = t' := by
      intro t t' h
      by_contra hne
      exact tl5 t t' hne (b t).1 List.mem_cons_self (by rw [h]; exact List.mem_cons_self)
    let D' : Set V := {a | a ∈ M.1.D ∧ ∃ t : T, (M.1.P a).getLast? = some (b t).1}
    let W' : PW V := ⟨D', fun a => if h : ∃ t : T, (M.1.P a).getLast? = some (b t).1 then
      M.1.P a ++ tl (Classical.choose h) else []⟩
    have hP' : ∀ a t, (M.1.P a).getLast? = some (b t).1 → W'.P a = M.1.P a ++ tl t := by
      intro a t ht
      have h : ∃ t : T, (M.1.P a).getLast? = some (b t).1 := ⟨t, ht⟩
      show (if h : ∃ t : T, (M.1.P a).getLast? = some (b t).1 then
        M.1.P a ++ tl (Classical.choose h) else []) = _
      rw [dif_pos h]
      have hc : (M.1.P a).getLast? = some (b (Classical.choose h)).1 := Classical.choose_spec h
      rw [tuniq _ _ (Option.some.inj (hc.symm.trans ht))]
    have hW' : IsWave G A B W' := by
      refine ⟨fun a ha => M.2.sub ha.1, ?_, ?_, ?_, ?_, ?_⟩
      · rintro a ⟨ha, t, ht⟩
        rw [hP' a t ht, List.head?_append, M.2.head a ha]
        rfl
      · rintro a ⟨ha, t, ht⟩
        rw [hP' a t ht]
        refine (M.2.chain a ha).append (tl1 t).tail (fun x hx y hy => ?_)
        rw [ht, Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact (tl1 t).rel_head? hy
      · rintro a ⟨ha, t, ht⟩
        rw [hP' a t ht, List.nodup_append]
        refine ⟨M.2.nodup a ha, (List.nodup_cons.1 (tl2 t)).2, fun x hx y hy hxy => ?_⟩
        subst hxy
        have h1 := interior G A B M.2 ha hx (tl4 t x hy).1
        rw [ht, Option.some.injEq] at h1
        rw [← h1] at hy
        exact (List.nodup_cons.1 (tl2 t)).1 hy
      · rintro a ⟨ha, t, ht⟩ a' ⟨ha', t', ht'⟩ hne x hx hx'
        rw [hP' a t ht, List.mem_append] at hx
        rw [hP' a' t' ht', List.mem_append] at hx'
        have htt : t ≠ t' := by
          rintro rfl
          exact M.2.disj a ha a' ha' hne _ (List.mem_of_getLast? ht)
            (List.mem_of_getLast? ht')
        rcases hx with hx | hx <;> rcases hx' with hx' | hx'
        · exact M.2.disj a ha a' ha' hne x hx hx'
        · exact (tl4 t' x hx').2 ⟨a, ha, interior G A B M.2 ha hx (tl4 t' x hx').1⟩
        · exact (tl4 t x hx).2 ⟨a', ha', interior G A B M.2 ha' hx' (tl4 t x hx).1⟩
        · exact tl5 t t' htt x (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hx')
      · intro u hu v hv w
        obtain ⟨x, hxX, hx, hvR, w₂, hw₂⟩ := suffix_main G A B X M.2.sep hu hv w
        obtain ⟨y, hy, hyT⟩ := hsep ⟨x, hx⟩ hxX ⟨v, hvR⟩ hv w₂.bypass w₂.bypass_isPath
        refine ⟨y.1, hw₂ y (w₂.support_bypass_subset_support hy), ?_⟩
        obtain ⟨a, ha, hla⟩ := hbS ⟨y, hyT⟩
        refine ⟨a, ⟨ha, ⟨y, hyT⟩, hla⟩, ?_⟩
        rw [hP' a ⟨y, hyT⟩ hla]
        exact last_append hla (tl3 ⟨y, hyT⟩)
    have hLe : Le G A M.1 W' := by
      refine ⟨fun a ha => ha.1, ?_⟩
      rintro a ⟨ha, t, ht⟩
      exact ⟨tl t, hP' a t ht, tl4 t⟩
    have hback := hM ⟨W', hW'⟩ hLe
    obtain ⟨a₀, ha₀, hla₀⟩ := hx₀
    obtain ⟨-, t, ht⟩ := hback.1 ha₀
    rw [hla₀, Option.some.injEq] at ht
    exact hno ⟨t, Subtype.ext ht.symm⟩

