import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1
import Mathlib

/-
Port of the rank-three upper bound of Erdos Problem 643 from
Yilin Liu, icekylinx/jsp-000523-proof, commit 59d41a6a1f3b8f99f148fa21b21e834525eed3a5
(registered as PALOMAR-2026-11-23-000012). Mathematical proof and Lean formalization by Yilin Liu.
Used under the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
Changes: the modules reachable from JSP523.Rank3.PartIICorollary were concatenated into one file,
comments were removed, unused declarations were dropped, file-level options were attached to
declarations, and lemma names were adapted to the pinned Mathlib. The final bridge to the
pinned statement is new.
-/

theorem Ζie {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem Ζdp {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := if_neg h
theorem Ζom {α : Sort _} {c : Prop} [Decidable c] {a : c → α} {b : ¬ c → α} (h : c) :
    dite c a b = a h := dif_pos h
section
namespace JSP523
abbrev Edge (α : Type*) := Finset α
abbrev Family (α : Type*) := Finset (Edge α)
section Basic
variable {α : Type*} [DecidableEq α]
def Uniform (r : ℕ) (F : Family α) : Prop :=
  ∀ ⦃E : Edge α⦄, E ∈ F → E.card = r
structure Ζvn (A B C D : Edge α) : Prop where
  ab : A ≠ B
  ac : A ≠ C
  ad : A ≠ D
  bc : B ≠ C
  bd : B ≠ D
  cd : C ≠ D
structure Ζvv (A B C D : Edge α) : Prop where
  distinct : Ζvn A B C D
  disjAB : Disjoint A B
  disjCD : Disjoint C D
  sameUnion : A ∪ B = C ∪ D
def Admissible (F : Family α) : Prop :=
  ∀ ⦃A B C D : Edge α⦄,
    A ∈ F → B ∈ F → C ∈ F → D ∈ F →
    Ζvv A B C D → False
theorem Ζvd {F G : Family α}
    (hGF : G ⊆ F) (hF : Admissible F) : Admissible G := by
  intro A B C D hA hB hC hD hq
  exact hF (hGF hA) (hGF hB) (hGF hC) (hGF hD) hq
end Basic
end JSP523
end
section
namespace JSP523.Rank3
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section Supports
variable {α : Type*} [DecidableEq α]
def Ζbp (H : Family α) (V : Finset α) : Family α := by
  exact (V.powersetCard 2).filter (fun p => ∃ E ∈ H, p ⊆ E)
def Ζc (H : Family α) (V : Finset α) (q : Edge α) : Family α := by
  exact (V.powersetCard 2).filter (fun p =>
    ∃ x ∈ q, ∃ y ∈ q,
      x ≠ y ∧ Disjoint p q ∧
      p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H)
def Ζac (H : Family α) (V : Finset α) : Family α := by
  exact (V.powersetCard 2).filter (fun q =>
    ∃ p ∈ V.powersetCard 2, ∃ x ∈ q, ∃ y ∈ q,
      x ≠ y ∧ Disjoint p q ∧
      p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H)
theorem Ζhj (H : Family α) (V : Finset α) :
    Ζbp H V ⊆ V.powersetCard 2 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1
theorem Ζbr (H : Family α) (V : Finset α) :
    Ζac H V ⊆ V.powersetCard 2 := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1
theorem Ζas
    (H : Family α) (V : Finset α) (q : Edge α) :
    q ∈ Ζac H V ↔
      q ∈ V.powersetCard 2 ∧ (Ζc H V q).Nonempty := by
  constructor
  · intro hq
    obtain ⟨hqV, p, hpV, x, hx, y, hy, hxy, hpq, hpx, hpy⟩ :=
      Finset.mem_filter.mp hq
    refine ⟨hqV, ⟨p, ?_⟩⟩
    exact Finset.mem_filter.mpr
      ⟨hpV, ⟨x, hx, y, hy, hxy, hpq, hpx, hpy⟩⟩
  · rintro ⟨hqV, ⟨p, hp⟩⟩
    obtain ⟨hpV, hcert⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hqV, ⟨p, hpV, hcert⟩⟩
end Supports
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section CommonLink
variable {α : Type*} [DecidableEq α]
private theorem Ζsc
    {p q : Edge α} {u v : α}
    (hpq : Disjoint p q)
    (huq : u ∉ q) (hvp : v ∉ p) (huv : u ≠ v) :
    Disjoint (p ∪ {u}) (q ∪ {v}) := by
  apply Finset.disjoint_left.mpr
  intro t htL htR
  rcases Finset.mem_union.mp htL with htp | htu
  · rcases Finset.mem_union.mp htR with htq | htv
    · exact (Finset.disjoint_left.mp hpq) htp htq
    · have htv' : t = v := Finset.mem_singleton.mp htv
      exact hvp (htv' ▸ htp)
  · have htu' : t = u := Finset.mem_singleton.mp htu
    rcases Finset.mem_union.mp htR with htq | htv
    · exact huq (htu' ▸ htq)
    · have htv' : t = v := Finset.mem_singleton.mp htv
      exact huv (htu'.symm.trans htv')
private theorem Ζif
    {p q : Edge α} {u v : α}
    (huq : u ∉ q) (huv : u ≠ v) :
    p ∪ {u} ≠ q ∪ {v} := by
  intro heq
  have huL : u ∈ p ∪ {u} := by simp
  have huR : u ∈ q ∪ {v} := heq ▸ huL
  rcases Finset.mem_union.mp huR with huq' | huv'
  · exact huq huq'
  · exact huv (Finset.mem_singleton.mp huv')
private theorem Ζpt
    {p q : Edge α} {u v t : α}
    (htp : t ∈ p) (htq : t ∉ q) (htv : t ≠ v) :
    p ∪ {u} ≠ q ∪ {v} := by
  intro heq
  have htL : t ∈ p ∪ {u} := Finset.mem_union.mpr (Or.inl htp)
  have htR : t ∈ q ∪ {v} := heq ▸ htL
  rcases Finset.mem_union.mp htR with htq' | htv'
  · exact htq htq'
  · exact htv (Finset.mem_singleton.mp htv')
theorem Ζkn
    {H : Family α} {p q : Edge α} {x y : α}
    (hH : Admissible H)
    (hxy : x ≠ y)
    (hpq : Disjoint p q)
    (hpNonempty : p.Nonempty) (hqNonempty : q.Nonempty)
    (hxp : x ∉ p) (hyp : y ∉ p)
    (hxq : x ∉ q) (hyq : y ∉ q)
    (hpx : p ∪ {x} ∈ H) (hpy : p ∪ {y} ∈ H)
    (hqx : q ∪ {x} ∈ H) (hqy : q ∪ {y} ∈ H) :
    False := by
  obtain ⟨t, htp⟩ := hpNonempty
  obtain ⟨s, hsq⟩ := hqNonempty
  have htq : t ∉ q := by
    intro htq
    exact (Finset.disjoint_left.mp hpq) htp htq
  have hsp : s ∉ p := by
    intro hsp
    exact (Finset.disjoint_left.mp hpq) hsp hsq
  have htx : t ≠ x := by
    intro heq
    exact hxp (heq ▸ htp)
  have hsy : s ≠ y := by
    intro heq
    exact hyq (heq ▸ hsq)
  have hdistinct : Ζvn
      (p ∪ {x}) (q ∪ {y}) (p ∪ {y}) (q ∪ {x}) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Ζif hxq hxy
    · exact Ζif hxp hxy
    · exact Ζpt htp htq htx
    · exact Ζpt hsq hsp hsy
    · exact Ζif hyq (Ne.symm hxy)
    · exact Ζif hyq (Ne.symm hxy)
  have hAB : Disjoint (p ∪ {x}) (q ∪ {y}) :=
    Ζsc hpq hxq hyp hxy
  have hCD : Disjoint (p ∪ {y}) (q ∪ {x}) :=
    Ζsc hpq hyq hxp (Ne.symm hxy)
  have hunion : (p ∪ {x}) ∪ (q ∪ {y}) =
      (p ∪ {y}) ∪ (q ∪ {x}) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with (hpz | hzx) | (hqz | hzy)
      · exact Or.inl (Or.inl hpz)
      · exact Or.inr (Or.inr hzx)
      · exact Or.inr (Or.inl hqz)
      · exact Or.inl (Or.inr hzy)
    · intro h
      rcases h with (hpz | hzy) | (hqz | hzx)
      · exact Or.inl (Or.inl hpz)
      · exact Or.inr (Or.inr hzy)
      · exact Or.inr (Or.inl hqz)
      · exact Or.inl (Or.inr hzx)
  exact hH hpx hqy hpy hqx ⟨hdistinct, hAB, hCD, hunion⟩
def Ζe
    (H : Family α) (V : Edge α) (x y : α) : Family α := by
  exact (V.powersetCard 2).filter (fun p =>
    Disjoint p ({x, y} : Edge α) ∧
      p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H)
theorem Ζdu
    {H : Family α} {V : Edge α} {x y : α}
    (hH : Admissible H) (hxy : x ≠ y)
    {p q : Edge α}
    (hp : p ∈ Ζe H V x y)
    (hq : q ∈ Ζe H V x y) :
    ¬ Disjoint p q := by
  intro hpq
  obtain ⟨hpV, hpOut, hpx, hpy⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqV, hqOut, hqx, hqy⟩ := Finset.mem_filter.mp hq
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpV).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp hqV).2
  have hpNonempty : p.Nonempty := Finset.card_pos.mp (by omega)
  have hqNonempty : q.Nonempty := Finset.card_pos.mp (by omega)
  have hxp : x ∉ p := by
    intro hx
    exact (Finset.disjoint_left.mp hpOut) hx (by simp)
  have hyp : y ∉ p := by
    intro hy
    exact (Finset.disjoint_left.mp hpOut) hy (by simp)
  have hxq : x ∉ q := by
    intro hx
    exact (Finset.disjoint_left.mp hqOut) hx (by simp)
  have hyq : y ∉ q := by
    intro hy
    exact (Finset.disjoint_left.mp hqOut) hy (by simp)
  exact Ζkn hH hxy hpq
    hpNonempty hqNonempty hxp hyp hxq hyq hpx hpy hqx hqy
theorem Ζr
    (H : Family α) (V : Edge α) {x y : α}
    (hxy : x ≠ y) (p : Edge α) :
    p ∈ Ζc H V ({x, y} : Edge α) ↔
      p ∈ Ζe H V x y := by
  constructor
  · intro hp
    obtain ⟨hpV, u, hu, v, hv, huv, hout, hpu, hpv⟩ :=
      Finset.mem_filter.mp hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    have hedges : p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H := by
      rcases hu with hux | huy
      · rcases hv with hvx | hvy
        · exact False.elim (huv (hux.trans hvx.symm))
        · constructor
          · simpa only [hux] using hpu
          · simpa only [hvy] using hpv
      · rcases hv with hvx | hvy
        · constructor
          · simpa only [hvx] using hpv
          · simpa only [huy] using hpu
        · exact False.elim (huv (huy.trans hvy.symm))
    exact Finset.mem_filter.mpr ⟨hpV, hout, hedges.1, hedges.2⟩
  · intro hp
    obtain ⟨hpV, hout, hpx, hpy⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨hpV, ⟨x, by simp, y, by simp, hxy, hout, hpx, hpy⟩⟩
theorem Ζfn
    {H : Family α} {V : Edge α} {x y : α}
    (hH : Admissible H) (hxy : x ≠ y)
    {p q : Edge α}
    (hp : p ∈ Ζc H V ({x, y} : Edge α))
    (hq : q ∈ Ζc H V ({x, y} : Edge α)) :
    ¬ Disjoint p q := by
  have hp' := (Ζr H V hxy p).mp hp
  have hq' := (Ζr H V hxy q).mp hq
  exact Ζdu hH hxy hp' hq'
end CommonLink
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section Incidence
variable {α : Type*} [DecidableEq α]
def Ζb (H : Family α) (V p : Edge α) : Edge α := by
  exact V.filter (fun x => x ∉ p ∧ p ∪ {x} ∈ H)
def Ζis (H : Family α) (V p : Edge α) : Family α :=
  (Ζb H V p).powersetCard 2
theorem Ζgg (H : Family α) (V p : Edge α) :
    Ζb H V p ⊆ V := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1
theorem Ζsd (H : Family α) (V p : Edge α) :
    Ζis H V p ⊆ V.powersetCard 2 := by
  intro q hq
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hq
  exact Finset.mem_powersetCard.mpr
    ⟨hsub.trans (Ζgg H V p), hcard⟩
theorem Ζha
    (H : Family α) (V q p : Edge α)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ V.powersetCard 2) :
    p ∈ Ζc H V q ↔ q ∈ Ζis H V p := by
  constructor
  · intro hlink
    obtain ⟨_, x, hx, y, hy, hxy, hdis, hpx, hpy⟩ :=
      Finset.mem_filter.mp hlink
    have hqcard : q.card = 2 := (Finset.mem_powersetCard.mp hq).2
    have hqsub : q ⊆ V := (Finset.mem_powersetCard.mp hq).1
    have hpair : ({x, y} : Edge α) = q := by
      apply Finset.eq_of_subset_of_card_le
      · intro t ht
        rcases Finset.mem_insert.mp ht with htx | hty
        · exact htx ▸ hx
        · exact (Finset.mem_singleton.mp hty) ▸ hy
      · rw [Finset.card_pair hxy, hqcard]
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      have ht' : t ∈ ({x, y} : Edge α) := hpair.symm ▸ ht
      rcases Finset.mem_insert.mp ht' with htx | hty
      · subst t
        apply Finset.mem_filter.mpr
        refine ⟨hqsub hx, ?_, hpx⟩
        intro hxp
        exact (Finset.disjoint_left.mp hdis) hxp hx
      · have hty' : t = y := Finset.mem_singleton.mp hty
        subst t
        apply Finset.mem_filter.mpr
        refine ⟨hqsub hy, ?_, hpy⟩
        intro hyp
        exact (Finset.disjoint_left.mp hdis) hyp hy
    · exact hqcard
  · intro hcell
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hcell
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hx := Finset.mem_filter.mp (hsub (by simp : x ∈ ({x, y} : Edge α)))
    have hy := Finset.mem_filter.mp (hsub (by simp : y ∈ ({x, y} : Edge α)))
    obtain ⟨_, hxp, hpx⟩ := hx
    obtain ⟨_, hyp, hpy⟩ := hy
    have hdis : Disjoint p ({x, y} : Edge α) := by
      apply Finset.disjoint_left.mpr
      intro t htp htq
      rcases Finset.mem_insert.mp htq with htx | hty
      · exact hxp (htx ▸ htp)
      · exact hyp ((Finset.mem_singleton.mp hty) ▸ htp)
    exact Finset.mem_filter.mpr
      ⟨hp, ⟨x, by simp, y, by simp, hxy, hdis, hpx, hpy⟩⟩
theorem Ζdw
    {H : Family α} {V q p t : Edge α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ Ζc H V q)
    (ht : t ∈ Ζc H V q) :
    ¬ Disjoint p t := by
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  exact Ζfn hH hxy hp ht
private theorem Ζmc
    {β : Type*} [DecidableEq β] (s t : Finset β) (hsub : t ⊆ s) :
    t.card = ∑ x ∈ s, if x ∈ t then (1 : ℕ) else 0 := by
  have hfilter : s.filter (fun x => x ∈ t) = t := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨hsub hx, hx⟩
  calc
    t.card = (s.filter (fun x => x ∈ t)).card :=
      congrArg Finset.card hfilter.symm
    _ = ∑ x ∈ s, if x ∈ t then (1 : ℕ) else 0 :=
      Finset.card_filter (fun x => x ∈ t) s
theorem Ζrr
    (H : Family α) (V : Edge α) :
    (∑ q ∈ V.powersetCard 2, (Ζc H V q).card) =
      ∑ p ∈ V.powersetCard 2,
        (Ζb H V p).card.choose 2 := by
  classical
  let P : Family α := V.powersetCard 2
  calc
    (∑ q ∈ P, (Ζc H V q).card) =
        ∑ q ∈ P, ∑ p ∈ P,
          if p ∈ Ζc H V q then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      exact Ζmc P (Ζc H V q)
        (fun p hp => (Finset.mem_filter.mp hp).1)
    _ = ∑ p ∈ P, ∑ q ∈ P,
          if p ∈ Ζc H V q then (1 : ℕ) else 0 :=
      Finset.sum_comm
    _ = ∑ p ∈ P, ∑ q ∈ P,
          if q ∈ Ζis H V p then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact if_congr
        (Ζha H V q p hq hp) rfl rfl
    _ = ∑ p ∈ P, (Ζis H V p).card := by
      apply Finset.sum_congr rfl
      intro p _
      exact (Ζmc P (Ζis H V p)
        (Ζsd H V p)).symm
    _ = ∑ p ∈ P,
          (Ζb H V p).card.choose 2 := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.card_powersetCard 2 (Ζb H V p)
end Incidence
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section PositiveSupports
variable {α : Type*} [DecidableEq α]
theorem Ζjw
    {p E : Edge α} {x : α}
    (hp2 : p.card = 2) (hE3 : E.card = 3)
    (hpE : p ⊆ E) (hxE : x ∈ E) (hxp : x ∉ p) :
    p ∪ {x} = E := by
  have hsub : p ∪ {x} ⊆ E := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyp | hyx
    · exact hpE hyp
    · exact (Finset.mem_singleton.mp hyx) ▸ hxE
  have hUnion : p ∪ {x} = insert x p := by
    ext y
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · intro hy
      rcases hy with hyp | hyx
      · exact Or.inr hyp
      · exact Or.inl hyx
    · intro hy
      rcases hy with hyx | hyp
      · exact Or.inr hyx
      · exact Or.inl hyp
  have hcard : (p ∪ {x}).card = 3 := by
    rw [hUnion, Finset.card_insert_of_notMem hxp, hp2]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hE3, hcard])
theorem Ζmd
    {p E : Edge α}
    (hp2 : p.card = 2) (hE3 : E.card = 3)
    (_hpE : p ⊆ E) :
    ∃ x ∈ E, x ∉ p := by
  by_contra h
  have hsub : E ⊆ p := by
    intro x hx
    by_contra hxp
    exact h ⟨x, hx, hxp⟩
  have hbound := Finset.card_le_card hsub
  omega
theorem Ζod
    (H : Family α) (V p : Edge α)
    (hp : p ∈ V.powersetCard 2)
    (hnon : (Ζb H V p).Nonempty) :
    p ∈ Ζbp H V := by
  obtain ⟨x, hx⟩ := hnon
  obtain ⟨_, _, hpx⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hp, ⟨p ∪ {x}, hpx, ?_⟩⟩
  intro y hy
  exact Finset.mem_union.mpr (Or.inl hy)
theorem Ζon
    (H : Family α) (V p : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hp : p ∈ Ζbp H V) :
    (Ζb H V p).Nonempty := by
  obtain ⟨hpV, E, hEH, hpE⟩ := Finset.mem_filter.mp hp
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpV).2
  have hE3 : E.card = 3 := hUniform hEH
  have hthird : ∃ x ∈ E, x ∉ p :=
    Ζmd hp2 hE3 hpE
  obtain ⟨x, hxE, hxp⟩ := hthird
  have hEq : p ∪ {x} = E :=
    Ζjw hp2 hE3 hpE hxE hxp
  refine ⟨x, Finset.mem_filter.mpr ⟨hground E hEH hxE, hxp, ?_⟩⟩
  exact hEq.symm ▸ hEH
theorem Ζfg
    (H : Family α) (V p : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hp : p ∈ V.powersetCard 2) :
    p ∈ Ζbp H V ↔ (Ζb H V p).Nonempty := by
  constructor
  · exact Ζon H V p hUniform hground
  · exact Ζod H V p hp
end PositiveSupports
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section FirstMoment
variable {α : Type*} [DecidableEq α]
def Ζeg (H : Family α) (p : Edge α) : Family α :=
  H.filter (fun E => p ⊆ E)
theorem Ζgh
    (H : Family α) (V p : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hp : p ∈ V.powersetCard 2) :
    (Ζb H V p).card = (Ζeg H p).card := by
  apply Finset.card_bij (fun x _ => p ∪ {x})
  · intro x hx
    obtain ⟨_, _, hxH⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hxH, ?_⟩
    intro y hy
    exact Finset.mem_union.mpr (Or.inl hy)
  · intro x hx y hy heq
    have hxp : x ∉ p := (Finset.mem_filter.mp hx).2.1
    have hxUnion : x ∈ p ∪ ({x} : Edge α) := by simp
    have hxY : x ∈ p ∪ ({y} : Edge α) := heq ▸ hxUnion
    rcases Finset.mem_union.mp hxY with hxP | hxSingle
    · exact False.elim (hxp hxP)
    · exact Finset.mem_singleton.mp hxSingle
  · intro E hE
    obtain ⟨hEH, hpE⟩ := Finset.mem_filter.mp hE
    have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
    have hE3 : E.card = 3 := hUniform hEH
    obtain ⟨x, hxE, hxp⟩ :=
      Ζmd hp2 hE3 hpE
    have heq : p ∪ {x} = E :=
      Ζjw hp2 hE3 hpE hxE hxp
    refine ⟨x, Finset.mem_filter.mpr ⟨hground E hEH hxE, hxp, ?_⟩, heq⟩
    exact heq.symm ▸ hEH
theorem Ζsq
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ V.powersetCard 2, (Ζeg H p).card) =
      3 * H.card := by
  classical
  let P : Family α := V.powersetCard 2
  calc
    (∑ p ∈ P, (Ζeg H p).card) =
        ∑ p ∈ P, ∑ E ∈ H, if p ⊆ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.card_filter (fun E : Edge α => p ⊆ E) H
    _ = ∑ E ∈ H, ∑ p ∈ P,
          if p ⊆ E then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ E ∈ H, (E.powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro E hEH
      have hfilter : P.filter (fun p => p ⊆ E) =
          E.powersetCard 2 := by
        ext p
        constructor
        · intro hp
          obtain ⟨hpP, hpE⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_powersetCard.mpr
            ⟨hpE, (Finset.mem_powersetCard.mp hpP).2⟩
        · intro hp
          obtain ⟨hpE, hp2⟩ := Finset.mem_powersetCard.mp hp
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_powersetCard.mpr
            ⟨hpE.trans (hground E hEH), hp2⟩, hpE⟩
      calc
        (∑ p ∈ P, if p ⊆ E then (1 : ℕ) else 0) =
            (P.filter (fun p => p ⊆ E)).card :=
          (Finset.card_filter (fun p => p ⊆ E) P).symm
        _ = (E.powersetCard 2).card := congrArg Finset.card hfilter
    _ = ∑ E ∈ H, (3 : ℕ) := by
      apply Finset.sum_congr rfl
      intro E hEH
      rw [Finset.card_powersetCard, hUniform hEH]
      decide
    _ = 3 * H.card := by simp [mul_comm]
theorem Ζrd
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ V.powersetCard 2,
        (Ζb H V p).card) = 3 * H.card := by
  calc
    (∑ p ∈ V.powersetCard 2,
        (Ζb H V p).card) =
      ∑ p ∈ V.powersetCard 2, (Ζeg H p).card := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Ζgh
          H V p hUniform hground hp
    _ = 3 * H.card := Ζsq H V hUniform hground
theorem Ζpx
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ Ζbp H V,
        (Ζb H V p).card) = 3 * H.card := by
  calc
    (∑ p ∈ Ζbp H V,
        (Ζb H V p).card) =
      ∑ p ∈ V.powersetCard 2,
        (Ζb H V p).card := by
        apply Finset.sum_subset (Ζhj H V)
        intro p hp hnot
        by_cases hz : (Ζb H V p).card = 0
        · exact hz
        · have hpos : 0 < (Ζb H V p).card :=
            Nat.pos_of_ne_zero hz
          have hnon : (Ζb H V p).Nonempty :=
            Finset.card_pos.mp hpos
          exact False.elim (hnot
            ((Ζfg H V p
              hUniform hground hp).mpr hnon))
    _ = 3 * H.card := Ζrd H V hUniform hground
theorem Ζoy
    (H : Family α) (V : Edge α) :
    (∑ q ∈ Ζac H V, (Ζc H V q).card) =
      ∑ p ∈ V.powersetCard 2,
        (Ζb H V p).card.choose 2 := by
  calc
    (∑ q ∈ Ζac H V, (Ζc H V q).card) =
      ∑ q ∈ V.powersetCard 2, (Ζc H V q).card := by
        apply Finset.sum_subset (Ζbr H V)
        intro q hq hnot
        by_cases hz : (Ζc H V q).card = 0
        · exact hz
        · have hpos : 0 < (Ζc H V q).card :=
            Nat.pos_of_ne_zero hz
          have hnon : (Ζc H V q).Nonempty :=
            Finset.card_pos.mp hpos
          exact False.elim (hnot
            ((Ζas H V q).mpr ⟨hq, hnon⟩))
    _ = ∑ p ∈ V.powersetCard 2,
          (Ζb H V p).card.choose 2 :=
      Ζrr H V
end FirstMoment
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section CellDegreeLedger
variable {α : Type*} [DecidableEq α]
def Ζcb (H : Family α) (V : Edge α) : Family α :=
  (Ζac H V).filter (fun q => (Ζc H V q).card = 1)
end CellDegreeLedger
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section ExactSupportLedger
variable {α : Type*} [DecidableEq α]
def Ζcm (d : ℕ) : ℚ :=
  if 4 ≤ d then ((d : ℚ) - 2) * ((d : ℚ) - 3) else 0
def Ζbb (c : ℕ) : ℚ :=
  if 3 < c then (c : ℚ) - 3 else 0
def Ζdx (H : Family α) (V : Edge α) : ℚ :=
  ∑ p ∈ Ζbp H V, Ζcm (Ζb H V p).card
def Ζgb (H : Family α) (V : Edge α) : ℚ :=
  ∑ q ∈ Ζac H V, Ζbb (Ζc H V q).card
def Ζca (H : Family α) (V : Edge α) : Family α :=
  (Ζbp H V).filter (fun p => (Ζb H V p).card = 1)
def Ζau (H : Family α) (V : Edge α) : Family α :=
  (Ζac H V).filter (fun q => (Ζc H V q).card = 2)
private theorem Ζvf (d : ℕ) (hd : 0 < d) :
    2 * (d.choose 2 : ℚ) - Ζcm d =
      4 * (d : ℚ) - 6 + (if d = 1 then 2 else 0) := by
  rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ 4 ≤ d) with h | h | h | h
  · subst d; norm_num [Ζcm]
  · subst d; norm_num [Ζcm]
  · subst d; norm_num [Ζcm]
  · have hne : d ≠ 1 := by omega
    simp [Ζcm, h, hne]
    rw [Nat.cast_choose_two ℚ d]
    ring
private theorem Ζve (c : ℕ) (hc : 0 < c) :
    Ζbb c = (c : ℚ) - 3 +
      (if c = 1 then 2 else 0) + (if c = 2 then 1 else 0) := by
  rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3 ∨ 3 < c) with h | h | h | h
  · subst c; norm_num [Ζbb]
  · subst c; norm_num [Ζbb]
  · subst c; norm_num [Ζbb]
  · have hne1 : c ≠ 1 := by omega
    have hne2 : c ≠ 2 := by omega
    simp [Ζbb, h, hne1, hne2]
theorem Ζoz
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ p ∈ Ζbp H V,
        (Ζb H V p).card.choose 2) =
      ∑ q ∈ Ζac H V, (Ζc H V q).card := by
  calc
    (∑ p ∈ Ζbp H V,
        (Ζb H V p).card.choose 2) =
        ∑ p ∈ V.powersetCard 2,
          (Ζb H V p).card.choose 2 := by
      apply Finset.sum_subset (Ζhj H V)
      intro p hp hnot
      by_cases hz : (Ζb H V p).card = 0
      · simp [hz]
      · have hnon : (Ζb H V p).Nonempty :=
          Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
        exact False.elim (hnot
          ((Ζfg H V p
            hUniform hground hp).mpr hnon))
    _ = ∑ q ∈ Ζac H V, (Ζc H V q).card :=
      (Ζoy H V).symm
private theorem Ζhv
    {β : Type*} [DecidableEq β]
    (s : Finset β) (P : β → Prop) [DecidablePred P] :
    ((s.filter P).card : ℚ) =
      ∑ x ∈ s, if P x then (1 : ℚ) else 0 := by
  simpa using
    congrArg (fun n : ℕ => (n : ℚ)) (Finset.card_filter P s)
theorem Ζug
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    2 * (∑ q ∈ Ζac H V, ((Ζc H V q).card : ℚ)) -
      Ζdx H V =
      12 * (H.card : ℚ) - 6 * ((Ζbp H V).card : ℚ) +
        2 * ((Ζca H V).card : ℚ) := by
  let U := Ζbp H V
  let d : Edge α → ℕ := fun p => (Ζb H V p).card
  have hfirst : (∑ p ∈ U, (d p : ℚ)) = 3 * (H.card : ℚ) := by
    simpa [U, d] using
      congrArg (fun n : ℕ => (n : ℚ))
        (Ζpx H V hUniform hground)
  have hsecond : (∑ p ∈ U, ((d p).choose 2 : ℚ)) =
      ∑ q ∈ Ζac H V, ((Ζc H V q).card : ℚ) := by
    simpa [U, d] using
      congrArg (fun n : ℕ => (n : ℚ))
        (Ζoz H V hUniform hground)
  have hK : (∑ p ∈ U, if d p = 1 then (1 : ℚ) else 0) =
      ((Ζca H V).card : ℚ) := by
    exact (Ζhv U (fun p => d p = 1)).symm
  have hpoint :
      (∑ p ∈ U, (2 * ((d p).choose 2 : ℚ) - Ζcm (d p))) =
        ∑ p ∈ U, (4 * (d p : ℚ) - 6 +
          (if d p = 1 then (2 : ℚ) else 0)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hnon : (Ζb H V p).Nonempty :=
      Ζon H V p hUniform hground hp
    exact Ζvf (d p) (Finset.card_pos.mpr hnon)
  have hL :
      (∑ p ∈ U, (2 * ((d p).choose 2 : ℚ) - Ζcm (d p))) =
        2 * (∑ p ∈ U, ((d p).choose 2 : ℚ)) -
          Ζdx H V := by
    simp [Ζdx, U, d, Finset.sum_sub_distrib, Finset.mul_sum]
  have hR :
      (∑ p ∈ U, (4 * (d p : ℚ) - 6 +
        (if d p = 1 then (2 : ℚ) else 0))) =
      4 * (∑ p ∈ U, (d p : ℚ)) - 6 * (U.card : ℚ) +
        2 * (∑ p ∈ U, if d p = 1 then (1 : ℚ) else 0) := by
    have htwo :
        (∑ p ∈ U, if d p = 1 then (2 : ℚ) else 0) =
          2 * (∑ p ∈ U, if d p = 1 then (1 : ℚ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, htwo]
    simp [Finset.mul_sum]
    ring
  rw [hL, hR, hfirst, hsecond, hK] at hpoint
  dsimp [U] at hpoint
  nlinarith
theorem Ζts (H : Family α) (V : Edge α) :
    Ζgb H V =
      (∑ q ∈ Ζac H V, ((Ζc H V q).card : ℚ)) -
        3 * ((Ζac H V).card : ℚ) +
        2 * ((Ζcb H V).card : ℚ) +
        ((Ζau H V).card : ℚ) := by
  let C := Ζac H V
  let c : Edge α → ℕ := fun q => (Ζc H V q).card
  have hOne : (∑ q ∈ C, if c q = 1 then (1 : ℚ) else 0) =
      ((Ζcb H V).card : ℚ) := by
    exact (Ζhv C (fun q => c q = 1)).symm
  have hTwo : (∑ q ∈ C, if c q = 2 then (1 : ℚ) else 0) =
      ((Ζau H V).card : ℚ) := by
    exact (Ζhv C (fun q => c q = 2)).symm
  have hpoint :
      (∑ q ∈ C, Ζbb (c q)) =
        ∑ q ∈ C, ((c q : ℚ) - 3 +
          (if c q = 1 then (2 : ℚ) else 0) +
          (if c q = 2 then (1 : ℚ) else 0)) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hnon : (Ζc H V q).Nonempty :=
      ((Ζas H V q).mp hq).2
    exact Ζve (c q) (Finset.card_pos.mpr hnon)
  have htwice :
      (∑ q ∈ C, if c q = 1 then (2 : ℚ) else 0) =
        2 * (∑ q ∈ C, if c q = 1 then (1 : ℚ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    split_ifs <;> ring
  have hR :
      (∑ q ∈ C, ((c q : ℚ) - 3 +
        (if c q = 1 then (2 : ℚ) else 0) +
        (if c q = 2 then (1 : ℚ) else 0))) =
      (∑ q ∈ C, (c q : ℚ)) - 3 * (C.card : ℚ) +
        2 * (∑ q ∈ C, if c q = 1 then (1 : ℚ) else 0) +
        (∑ q ∈ C, if c q = 2 then (1 : ℚ) else 0) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, htwice]
    simp
    ring
  rw [hR, hOne, hTwo] at hpoint
  simpa only [Ζgb, C, c] using hpoint
theorem Ζvg
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    6 * (2 * (H.card : ℚ) - ((Ζbp H V).card : ℚ) -
      ((Ζac H V).card : ℚ)) =
      2 * Ζgb H V - Ζdx H V -
        2 * ((Ζca H V).card : ℚ) -
        4 * ((Ζcb H V).card : ℚ) -
        2 * ((Ζau H V).card : ℚ) := by
  have hdegree := Ζug H V hUniform hground
  have hcell := Ζts H V
  linarith
end ExactSupportLedger
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
def Ζfq (H : Family α) (A : Edge α) : Family α :=
  H.filter fun E => E ⊆ A
def Ζdo (H : Family α) (A : Edge α) : Family α :=
  A.powersetCard 3 \ H
def Ζar (H : Family α) (A : Edge α) : Prop :=
  A.card = 5 ∧ 9 ≤ (Ζfq H A).card
theorem Ζrs
    (H : Family α) (A : Edge α) (hU : Uniform 3 H) :
    Ζfq H A = A.powersetCard 3 ∩ H := by
  ext E
  simp only [Ζfq, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hEH, hEA⟩
    exact ⟨⟨hEA, hU hEH⟩, hEH⟩
  · rintro ⟨⟨hEA, _⟩, hEH⟩
    exact ⟨hEH, hEA⟩
theorem Ζql
    (H : Family α) (A : Edge α) (hU : Uniform 3 H)
    (hA : Ζar H A) :
    (Ζdo H A).card ≤ 1 := by
  obtain ⟨hAcard, hDense⟩ := hA
  have hAll : (A.powersetCard 3).card = 10 := by
    rw [Finset.card_powersetCard, hAcard]
    decide
  have hPart := Finset.card_sdiff_add_card_inter
    (A.powersetCard 3) H
  rw [← Ζrs H A hU] at hPart
  change (Ζdo H A).card +
    (Ζfq H A).card = (A.powersetCard 3).card at hPart
  omega
theorem Ζhw
    (H : Family α) (A : Edge α) (hU : Uniform 3 H)
    (hA : Ζar H A)
    {S T : Edge α}
    (hS : S ∈ Ζdo H A)
    (hT : T ∈ Ζdo H A) : S = T := by
  exact (Finset.card_le_one.mp
    (Ζql H A hU hA)) S hS T hT
theorem Ζer
    (H : Family α) (A : Edge α) (hU : Uniform 3 H)
    (hA : Ζar H A)
    {S T : Edge α}
    (hS : S ∈ A.powersetCard 3)
    (hT : T ∈ A.powersetCard 3)
    (hST : S ≠ T) : S ∈ H ∨ T ∈ H := by
  by_contra h
  have hs : S ∈ Ζdo H A :=
    Finset.mem_sdiff.mpr ⟨hS, fun hSH => h (Or.inl hSH)⟩
  have ht : T ∈ Ζdo H A :=
    Finset.mem_sdiff.mpr ⟨hT, fun hTH => h (Or.inr hTH)⟩
  exact hST (Ζhw H A hU hA hs ht)
def Ζcz (H : Family α) (A : Edge α) (x : α) : Family α :=
  (A.powersetCard 2).filter fun p => p ∪ {x} ∈ H
def Ζaw
    (H : Family α) (A p : Edge α) : Edge α :=
  (A \ p).filter fun y => p ∪ {y} ∈ H
private theorem Ζcp
    (A p : Edge α) (hp : p ∈ A.powersetCard 2)
    {y : α} (hy : y ∈ A \ p) :
    p ∪ {y} ∈ A.powersetCard 3 := by
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hp
  obtain ⟨hyA, hyp⟩ := Finset.mem_sdiff.mp hy
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.union_subset hpA (Finset.singleton_subset_iff.mpr hyA)
  · rw [Finset.union_singleton, Finset.card_insert_of_notMem hyp, hp2]
private theorem Ζsr
    (p : Edge α) {y z : α} (hy : y ∉ p) (_hz : z ∉ p)
    (h : p ∪ {y} = p ∪ {z}) : y = z := by
  have hyMem : y ∈ p ∪ {z} := h ▸ (by simp : y ∈ p ∪ {y})
  rcases Finset.mem_union.mp hyMem with hP | hZ
  · exact False.elim (hy hP)
  · simpa using hZ
theorem Ζib
    (H : Family α) (A p : Edge α)
    (hU : Uniform 3 H)
    (hA : Ζar H A)
    (hp : p ∈ A.powersetCard 2) :
    2 ≤ (Ζaw H A p).card := by
  let C := A \ p
  let Bad := C.filter fun y => p ∪ {y} ∉ H
  have hCcard : C.card = 3 := by
    rw [Finset.card_sdiff_of_subset
      (Finset.mem_powersetCard.mp hp).1,
      hA.1, (Finset.mem_powersetCard.mp hp).2]
  have hBad : Bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    have hyC : y ∈ C := (Finset.mem_filter.mp hy).1
    have hzC : z ∈ C := (Finset.mem_filter.mp hz).1
    have hyNot : p ∪ {y} ∉ H := (Finset.mem_filter.mp hy).2
    have hzNot : p ∪ {z} ∉ H := (Finset.mem_filter.mp hz).2
    have hyMissing : p ∪ {y} ∈ Ζdo H A :=
      Finset.mem_sdiff.mpr
        ⟨Ζcp A p hp hyC, hyNot⟩
    have hzMissing : p ∪ {z} ∈ Ζdo H A :=
      Finset.mem_sdiff.mpr
        ⟨Ζcp A p hp hzC, hzNot⟩
    have hEq := Ζhw H A hU hA hyMissing hzMissing
    exact Ζsr p
      (Finset.mem_sdiff.mp hyC).2
      (Finset.mem_sdiff.mp hzC).2 hEq
  have hPartition := Finset.card_filter_add_card_filter_not
    (s := C) (p := fun y => p ∪ {y} ∈ H)
  change (Ζaw H A p).card + Bad.card = C.card
    at hPartition
  omega
private theorem Ζnx
    (A p q : Edge α) (hp : p ⊆ A) (hq : q ⊆ A)
    (h : A \ p = A \ q) : p = q := by
  have h' := congrArg (fun S : Edge α => A \ S) h
  simpa [Finset.sdiff_sdiff_eq_self hp,
    Finset.sdiff_sdiff_eq_self hq] using h'
private theorem Ζit
    (A p : Edge α) (x : α) (hx : x ∉ A) :
    Disjoint (p ∪ {x}) (A \ p) := by
  apply Finset.disjoint_left.mpr
  intro v hv hComp
  obtain ⟨hvA, hvp⟩ := Finset.mem_sdiff.mp hComp
  rcases Finset.mem_union.mp hv with hP | hX
  · exact hvp hP
  · exact hx ((Finset.mem_singleton.mp hX) ▸ hvA)
private theorem Ζjx
    (A p : Edge α) (x : α) (hp : p ⊆ A) :
    (p ∪ {x}) ∪ (A \ p) = A ∪ {x} := by
  calc
    (p ∪ {x}) ∪ (A \ p) = (p ∪ (A \ p)) ∪ {x} := by ac_rfl
    _ = A ∪ {x} := by rw [Finset.union_sdiff_of_subset hp]
theorem Ζjy
    (H : Family α) (A : Edge α) (x : α)
    (hAdm : Admissible H) (hxA : x ∉ A)
    {p q : Edge α}
    (hp : p ∈ Ζcz H A x)
    (hq : q ∈ Ζcz H A x)
    (hpq : p ≠ q)
    (hpComp : A \ p ∈ H)
    (hqComp : A \ q ∈ H) : False := by
  obtain ⟨hpCand, hpEdge⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqCand, hqEdge⟩ := Finset.mem_filter.mp hq
  have hpA := (Finset.mem_powersetCard.mp hpCand).1
  have hqA := (Finset.mem_powersetCard.mp hqCand).1
  have hxp : x ∉ p := fun h => hxA (hpA h)
  have hxq : x ∉ q := fun h => hxA (hqA h)
  have hExtNe : p ∪ {x} ≠ q ∪ {x} := by
    intro h
    have h' := congrArg (fun S : Edge α => S.erase x) h
    rw [Finset.union_singleton, Finset.erase_insert hxp,
      Finset.union_singleton, Finset.erase_insert hxq] at h'
    exact hpq h'
  have hCompNe : A \ p ≠ A \ q :=
    fun h => hpq (Ζnx A p q hpA hqA h)
  have hExtPNeCompP : p ∪ {x} ≠ A \ p := by
    intro h
    have hx : x ∈ A \ p := h ▸ (by simp : x ∈ p ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hExtPNeCompQ : p ∪ {x} ≠ A \ q := by
    intro h
    have hx : x ∈ A \ q := h ▸ (by simp : x ∈ p ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hExtQNeCompP : q ∪ {x} ≠ A \ p := by
    intro h
    have hx : x ∈ A \ p := h ▸ (by simp : x ∈ q ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hExtQNeCompQ : q ∪ {x} ≠ A \ q := by
    intro h
    have hx : x ∈ A \ q := h ▸ (by simp : x ∈ q ∪ {x})
    exact hxA (Finset.mem_sdiff.mp hx).1
  have hEqUnion :
      (p ∪ {x}) ∪ (A \ p) =
        (q ∪ {x}) ∪ (A \ q) := by
    rw [Ζjx A p x hpA,
      Ζjx A q x hqA]
  apply hAdm hpEdge hpComp hqEdge hqComp
  refine ⟨?_, Ζit A p x hxA,
    Ζit A q x hxA, hEqUnion⟩
  exact ⟨hExtPNeCompP, hExtNe, hExtPNeCompQ,
    hExtQNeCompP.symm, hCompNe, hExtQNeCompQ⟩
private theorem Ζgm
    (A p : Edge α)
    (hA : A.card = 5)
    (hp : p ∈ A.powersetCard 2) :
    A \ p ∈ A.powersetCard 3 := by
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hp
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.sdiff_subset
  · rw [Finset.card_sdiff_of_subset hpA, hA, hp2]
theorem Ζuz
    (H : Family α) (A : Edge α) (x : α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : Ζar H A) (hxA : x ∉ A) :
    (Ζcz H A x).card ≤ 2 := by
  let T := Ζcz H A x
  let Good := T.filter fun p => A \ p ∈ H
  let Bad := T.filter fun p => A \ p ∉ H
  have hGood : Good.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
    have hqT : q ∈ T := (Finset.mem_filter.mp hq).1
    have hpH : A \ p ∈ H := (Finset.mem_filter.mp hp).2
    have hqH : A \ q ∈ H := (Finset.mem_filter.mp hq).2
    exact Ζjy H A x hAdm hxA
      hpT hqT hpq hpH hqH
  have hBad : Bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
    have hqT : q ∈ T := (Finset.mem_filter.mp hq).1
    have hpCand := (Finset.mem_filter.mp hpT).1
    have hqCand := (Finset.mem_filter.mp hqT).1
    have hpMissing : A \ p ∈ Ζdo H A :=
      Finset.mem_sdiff.mpr
        ⟨Ζgm A p hA.1 hpCand,
          (Finset.mem_filter.mp hp).2⟩
    have hqMissing : A \ q ∈ Ζdo H A :=
      Finset.mem_sdiff.mpr
        ⟨Ζgm A q hA.1 hqCand,
          (Finset.mem_filter.mp hq).2⟩
    exact Ζnx A p q
      (Finset.mem_powersetCard.mp hpCand).1
      (Finset.mem_powersetCard.mp hqCand).1
      (Ζhw H A hU hA hpMissing hqMissing)
  have hPart := Finset.card_filter_add_card_filter_not
    (s := T) (p := fun p => A \ p ∈ H)
  change Good.card + Bad.card = T.card at hPart
  change T.card ≤ 2
  omega
theorem Ζnj
    (H : Family α) (A p : Edge α)
    (hU : Uniform 3 H) (hA : Ζar H A)
    (hp : p ∈ A.powersetCard 2)
    (hMissing : A \ p ∉ H) :
    Ζaw H A p = A \ p := by
  obtain ⟨t, ht⟩ : p.Nonempty := by
    apply Finset.card_pos.mp
    have hp2 := (Finset.mem_powersetCard.mp hp).2
    omega
  have hCompCand := Ζgm A p hA.1 hp
  apply Finset.ext
  intro y
  constructor
  · intro hy
    exact (Finset.mem_filter.mp hy).1
  · intro hy
    apply Finset.mem_filter.mpr
    refine ⟨hy, ?_⟩
    have hCandidate := Ζcp A p hp hy
    have hneq : p ∪ {y} ≠ A \ p := by
      intro heq
      have htComp : t ∈ A \ p := heq ▸
        (Finset.mem_union_left {y} ht)
      exact (Finset.mem_sdiff.mp htComp).2 ht
    exact (Ζer H A hU hA hCandidate
      hCompCand hneq).resolve_right hMissing
theorem Ζhb
    (H : Family α) (A p q : Edge α)
    (hU : Uniform 3 H) (hA : Ζar H A)
    (hp : p ∈ A.powersetCard 2)
    (hq : q ∈ A.powersetCard 2)
    (hpq : p ≠ q)
    (hMissing : A \ p ∉ H) :
    4 ≤ (Ζaw H A p ∪
      Ζaw H A q).card := by
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hp
  obtain ⟨hqA, hq2⟩ := Finset.mem_powersetCard.mp hq
  have hNotSub : ¬ p ⊆ q := by
    intro hsub
    exact hpq (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hDiff : (p \ q).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hEmpty
    exact hNotSub (Finset.sdiff_eq_empty_iff_subset.mp hEmpty)
  obtain ⟨y, hyDiff⟩ := hDiff
  obtain ⟨hyP, hyQ⟩ := Finset.mem_sdiff.mp hyDiff
  have hyA : y ∈ A := hpA hyP
  have hyC : y ∈ A \ q := Finset.mem_sdiff.mpr ⟨hyA, hyQ⟩
  have hqCandidate := Ζcp A q hq hyC
  have hpCompCandidate := Ζgm A p hA.1 hp
  have hneq : q ∪ {y} ≠ A \ p := by
    intro heq
    have hyComp : y ∈ A \ p := heq ▸ (by simp : y ∈ q ∪ {y})
    exact (Finset.mem_sdiff.mp hyComp).2 hyP
  have hqy : q ∪ {y} ∈ H :=
    (Ζer H A hU hA hqCandidate
      hpCompCandidate hneq).resolve_right hMissing
  have hyNq : y ∈ Ζaw H A q :=
    Finset.mem_filter.mpr ⟨hyC, hqy⟩
  have hNp := Ζnj H A p
    hU hA hp hMissing
  have hyNotNp : y ∉ A \ p :=
    fun h => (Finset.mem_sdiff.mp h).2 hyP
  have hsub : insert y (A \ p) ⊆
      Ζaw H A p ∪
        Ζaw H A q := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_union_right _ hyNq
    · exact Finset.mem_union_left _ (hNp.symm ▸ hv)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hyNotNp,
    Finset.card_sdiff_of_subset hpA, hA.1, hp2] at hcard
  omega
theorem Ζss
    (H : Family α) (A : Edge α) (x : α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : Ζar H A) (hxA : x ∉ A) :
    2 * (Ζcz H A x).card ≤
      ((Ζcz H A x).biUnion
        (Ζaw H A)).card := by
  let T := Ζcz H A x
  have hTle := Ζuz H A x hU hAdm hA hxA
  have hCases : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by
    change T.card ≤ 2 at hTle
    omega
  rcases hCases with hZero | hOne | hTwo
  · have hEmpty : T = ∅ := Finset.card_eq_zero.mp hZero
    simp [T, hEmpty]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hOne
    have hpTrace : p ∈ Ζcz H A x := by
      change p ∈ T
      simp [hp]
    have hpCand := (Finset.mem_filter.mp hpTrace).1
    have hN := Ζib H A p hU hA hpCand
    change 2 * T.card ≤
      (T.biUnion (Ζaw H A)).card
    simp [hp]
    exact hN
  · obtain ⟨p, q, hpq, hT⟩ := Finset.card_eq_two.mp hTwo
    have hpTrace : p ∈ Ζcz H A x := by
      change p ∈ T
      simp [hT]
    have hqTrace : q ∈ Ζcz H A x := by
      change q ∈ T
      simp [hT]
    have hpCand := (Finset.mem_filter.mp hpTrace).1
    have hqCand := (Finset.mem_filter.mp hqTrace).1
    have hUnion : 4 ≤
        (Ζaw H A p ∪
          Ζaw H A q).card := by
      by_cases hpPresent : A \ p ∈ H
      · have hqMissing : A \ q ∉ H := by
          intro hqPresent
          exact Ζjy H A x hAdm hxA
            hpTrace hqTrace hpq hpPresent hqPresent
        simpa only [Finset.union_comm] using
          Ζhb H A q p
            hU hA hqCand hpCand hpq.symm hqMissing
      · exact Ζhb H A p q
          hU hA hpCand hqCand hpq hpPresent
    change 2 * T.card ≤
      (T.biUnion (Ζaw H A)).card
    rw [hTwo, hT]
    simpa only [Finset.biUnion_insert, Finset.singleton_biUnion,
      Finset.union_empty] using hUnion
def Ζbu (H : Family α) (A : Edge α) : Family α :=
  H.filter fun E => (E ∩ A).card ≤ 1
theorem Ζco (H : Family α) (A : Edge α) :
    Ζbu H A ⊆ H := by
  intro E hE
  exact (Finset.mem_filter.mp hE).1
theorem Ζtt
    (H : Family α) (A : Edge α) (hAdm : Admissible H) :
    Admissible (Ζbu H A) :=
  Ζvd (Ζco H A) hAdm
theorem Ζva
    (H : Family α) (A : Edge α) (hU : Uniform 3 H) :
    Uniform 3 (Ζbu H A) := by
  intro E hE
  exact hU (Ζco H A hE)
theorem Ζvq
    (H K : Family α) (V : Edge α) (hHK : H ⊆ K) :
    Ζbp H V ⊆ Ζbp K V := by
  intro p hp
  obtain ⟨hpV, E, hEH, hpE⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpV, ⟨E, hHK hEH, hpE⟩⟩
theorem Ζvr
    (H K : Family α) (V : Edge α) (hHK : H ⊆ K) :
    Ζac H V ⊆ Ζac K V := by
  intro q hq
  obtain ⟨hqV, p, hpV, x, hx, y, hy, hxy, hDisj, hpx, hpy⟩ :=
    Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr
    ⟨hqV, ⟨p, hpV, x, hx, y, hy, hxy, hDisj,
      hHK hpx, hHK hpy⟩⟩
def Ζda
    (H : Family α) (A : Edge α) (x : α) : Edge α :=
  (Ζcz H A x).biUnion (Ζaw H A)
def Ζec
    (H : Family α) (V A : Edge α) : Family α :=
  (V \ A).biUnion fun x =>
    (Ζda H A x).image fun y => ({x, y} : Edge α)
theorem Ζgc
    (H : Family α) (A : Edge α) (x y : α) :
    y ∈ Ζda H A x ↔
      ∃ p ∈ Ζcz H A x,
        y ∈ Ζaw H A p := by
  simp [Ζda]
theorem Ζgi
    (H : Family α) (A : Edge α) (x : α) :
    Ζda H A x ⊆ A := by
  intro y hy
  obtain ⟨p, _, hyp⟩ := (Ζgc H A x y).mp hy
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyp).1).1
theorem Ζrt
    (H : Family α) (V A : Edge α)
    (hAV : A ⊆ V)
    {x y : α}
    (hx : x ∈ V \ A)
    (hy : y ∈ Ζda H A x) :
    ({x, y} : Edge α) ∈ Ζac H V := by
  obtain ⟨hxV, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨p, hpTrace, hyN⟩ :=
    (Ζgc H A x y).mp hy
  obtain ⟨hpCand, hpx⟩ := Finset.mem_filter.mp hpTrace
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hpCand
  obtain ⟨hyC, hpy⟩ := Finset.mem_filter.mp hyN
  obtain ⟨hyA, hyp⟩ := Finset.mem_sdiff.mp hyC
  have hxy : x ≠ y := fun h => hxA (h ▸ hyA)
  have hCell : ({x, y} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hxV
      · exact hAV (Finset.mem_singleton.mp hv ▸ hyA)
    · exact Finset.card_pair hxy
  have hpV : p ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hpA.trans hAV, hp2⟩
  have hDisj : Disjoint p ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro v hvp hvCell
    rcases Finset.mem_insert.mp hvCell with hvx | hvy
    · exact hxA (hpA (hvx ▸ hvp))
    · exact hyp (Finset.mem_singleton.mp hvy ▸ hvp)
  exact Finset.mem_filter.mpr
    ⟨hCell, ⟨p, hpV, x, by simp, y, by simp, hxy,
      hDisj, hpx, hpy⟩⟩
theorem Ζmo
    (H : Family α) (V A : Edge α) (hAV : A ⊆ V) :
    Ζec H V A ⊆ Ζac H V := by
  intro q hq
  obtain ⟨x, hx, hqX⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqX
  exact Ζrt H V A hAV hx hy
private theorem Ζst
    (H : Family α) (V A p : Edge α)
    (hAV : A ⊆ V)
    {x y : α}
    (hx : x ∈ V \ A)
    (hp : p ∈ Ζcz H A x)
    (hy : y ∈ Ζaw H A p) :
    p ∈ Ζe H V x y := by
  obtain ⟨_, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hpCand, hpx⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpA, hp2⟩ := Finset.mem_powersetCard.mp hpCand
  obtain ⟨hyC, hpy⟩ := Finset.mem_filter.mp hy
  have hyNotP := (Finset.mem_sdiff.mp hyC).2
  have hDisj : Disjoint p ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro v hvp hvPair
    rcases Finset.mem_insert.mp hvPair with hvx | hvy
    · exact hxA (hpA (hvx ▸ hvp))
    · exact hyNotP (Finset.mem_singleton.mp hvy ▸ hvp)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard.mpr
      ⟨hpA.trans hAV, hp2⟩, hDisj, hpx, hpy⟩
theorem Ζmp
    (H : Family α) (V A : Edge α)
    (hAdm : Admissible H) (hAV : A ⊆ V)
    {x y : α}
    (hx : x ∈ V \ A)
    (hy : y ∈ Ζda H A x) :
    ({x, y} : Edge α) ∉ Ζac (Ζbu H A) V := by
  obtain ⟨_, hxA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨p, hpTrace, hyN⟩ :=
    (Ζgc H A x y).mp hy
  obtain ⟨hpCand, _⟩ := Finset.mem_filter.mp hpTrace
  have hpA := (Finset.mem_powersetCard.mp hpCand).1
  have hyA : y ∈ A :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyN).1).1
  have hyNotP : y ∉ p :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyN).1).2
  have hxy : x ≠ y := fun h => hxA (h ▸ hyA)
  have hpOrig := Ζst H V A p
    hAV hx hpTrace hyN
  intro hCell
  obtain ⟨_, ⟨r, hrClean⟩⟩ :=
    (Ζas
      (Ζbu H A) V ({x, y} : Edge α)).mp hCell
  have hrClean' := (Ζr
    (Ζbu H A) V hxy r).mp hrClean
  obtain ⟨hrV, hrDisj, hrxClean, hryClean⟩ :=
    Finset.mem_filter.mp hrClean'
  have hrOrig : r ∈ Ζe H V x y :=
    Finset.mem_filter.mpr
      ⟨hrV, hrDisj,
        Ζco H A hrxClean,
        Ζco H A hryClean⟩
  have hMeet : ¬ Disjoint p r :=
    Ζdu hAdm hxy hpOrig hrOrig
  have hInter : (p ∩ r).Nonempty := by
    by_contra h
    exact hMeet (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨t, ht⟩ := hInter
  obtain ⟨htP, htR⟩ := Finset.mem_inter.mp ht
  have htA : t ∈ A := hpA htP
  have hty : t ≠ y := fun h => hyNotP (h ▸ htP)
  have hSub : ({t, y} : Edge α) ⊆ (r ∪ {y}) ∩ A := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ htR, htA⟩
    · have hvy : v = y := Finset.mem_singleton.mp hv
      subst v
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (by simp), hyA⟩
  have hTwo : 2 ≤ ((r ∪ {y}) ∩ A).card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_pair hty] at h
    exact h
  have hOne := (Finset.mem_filter.mp hryClean).2
  exact (by omega : False)
private theorem Ζoo
    (p q : Edge α) (x : α)
    (hxp : x ∉ p) (hxq : x ∉ q)
    (h : p ∪ {x} = q ∪ {x}) : p = q := by
  have he := congrArg (fun S : Edge α => S.erase x) h
  simpa [Finset.union_singleton, Finset.erase_insert hxp,
    Finset.erase_insert hxq] using he
private theorem Ζtk
    (p q : Edge α) {x y : α}
    (hxq : x ∉ q) (hxy : x ≠ y) :
    p ∪ {x} ≠ q ∪ {y} := by
  intro h
  have hx : x ∈ q ∪ {y} := h ▸ (by simp : x ∈ p ∪ {x})
  rcases Finset.mem_union.mp hx with hxq' | hxy'
  · exact hxq hxq'
  · exact hxy (Finset.mem_singleton.mp hxy')
theorem Ζjf
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : Ζar H A)
    (hAV : A ⊆ V)
    {x y : α} (hxy : x ≠ y)
    (hq : ({x, y} : Edge α) ∈ A.powersetCard 2) :
    ∃ p : Edge α,
      p ⊆ A \ ({x, y} : Edge α) ∧
      p ∈ Ζe H V x y := by
  let B := A \ ({x, y} : Edge α)
  have hqA := (Finset.mem_powersetCard.mp hq).1
  have hBcard : B.card = 3 := by
    rw [Finset.card_sdiff_of_subset hqA, hA.1,
      (Finset.mem_powersetCard.mp hq).2]
  have hPairs : (B.powersetCard 2).card = 3 := by
    rw [Finset.card_powersetCard, hBcard]
    decide
  have hTwo : 1 < (B.powersetCard 2).card := by omega
  obtain ⟨p, hp, r, hr, hpr⟩ := Finset.one_lt_card.mp hTwo
  have hpB := (Finset.mem_powersetCard.mp hp).1
  have hrB := (Finset.mem_powersetCard.mp hr).1
  have hpA : p ∈ A.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hpB.trans Finset.sdiff_subset,
        (Finset.mem_powersetCard.mp hp).2⟩
  have hrA : r ∈ A.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨hrB.trans Finset.sdiff_subset,
        (Finset.mem_powersetCard.mp hr).2⟩
  have hxA : x ∈ A := hqA (by simp)
  have hyA : y ∈ A := hqA (by simp)
  have hxp : x ∉ p := by
    intro hx
    exact (Finset.mem_sdiff.mp (hpB hx)).2 (by simp)
  have hyp : y ∉ p := by
    intro hy
    exact (Finset.mem_sdiff.mp (hpB hy)).2 (by simp)
  have hxr : x ∉ r := by
    intro hx
    exact (Finset.mem_sdiff.mp (hrB hx)).2 (by simp)
  have hyr : y ∉ r := by
    intro hy
    exact (Finset.mem_sdiff.mp (hrB hy)).2 (by simp)
  have hpxC := Ζcp A p hpA
    (Finset.mem_sdiff.mpr ⟨hxA, hxp⟩)
  have hpyC := Ζcp A p hpA
    (Finset.mem_sdiff.mpr ⟨hyA, hyp⟩)
  have hrxC := Ζcp A r hrA
    (Finset.mem_sdiff.mpr ⟨hxA, hxr⟩)
  have hryC := Ζcp A r hrA
    (Finset.mem_sdiff.mpr ⟨hyA, hyr⟩)
  have hrxNeP : r ∪ {x} ≠ p ∪ {x} :=
    fun h => hpr (Ζoo r p x hxr hxp h).symm
  have hryNeP : r ∪ {y} ≠ p ∪ {y} :=
    fun h => hpr (Ζoo r p y hyr hyp h).symm
  have hrxNePY : r ∪ {x} ≠ p ∪ {y} :=
    Ζtk r p hxp hxy
  have hryNePX : r ∪ {y} ≠ p ∪ {x} :=
    Ζtk r p hyp hxy.symm
  have hDisjP : Disjoint p ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro a ha haxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at haxy
    rcases haxy with h | h
    · exact hxp (h ▸ ha)
    · exact hyp (h ▸ ha)
  have hDisjR : Disjoint r ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro a ha haxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at haxy
    rcases haxy with h | h
    · exact hxr (h ▸ ha)
    · exact hyr (h ▸ ha)
  have hpV : p ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hpA).1.trans hAV,
        (Finset.mem_powersetCard.mp hpA).2⟩
  have hrV : r ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hrA).1.trans hAV,
        (Finset.mem_powersetCard.mp hrA).2⟩
  by_cases hPX : p ∪ {x} ∈ H
  · by_cases hPY : p ∪ {y} ∈ H
    · exact ⟨p, hpB, Finset.mem_filter.mpr
        ⟨hpV, hDisjP, hPX, hPY⟩⟩
    · have hRX : r ∪ {x} ∈ H :=
        (Ζer H A hU hA hrxC hpyC hrxNePY).resolve_right hPY
      have hRY : r ∪ {y} ∈ H :=
        (Ζer H A hU hA hryC hpyC hryNeP).resolve_right hPY
      exact ⟨r, hrB, Finset.mem_filter.mpr
        ⟨hrV, hDisjR, hRX, hRY⟩⟩
  · have hRX : r ∪ {x} ∈ H :=
      (Ζer H A hU hA hrxC hpxC hrxNeP).resolve_right hPX
    have hRY : r ∪ {y} ∈ H :=
      (Ζer H A hU hA hryC hpxC hryNePX).resolve_right hPX
    exact ⟨r, hrB, Finset.mem_filter.mpr
      ⟨hrV, hDisjR, hRX, hRY⟩⟩
theorem Ζls
    (H : Family α) (V A p : Edge α)
    (hAdm : Admissible H)
    {x y : α} (hxy : x ≠ y)
    (hyA : y ∈ A) (hpA : p ⊆ A) (hyNotP : y ∉ p)
    (hpOrig : p ∈ Ζe H V x y) :
    ({x, y} : Edge α) ∉ Ζac (Ζbu H A) V := by
  intro hCell
  obtain ⟨_, ⟨r, hrClean⟩⟩ :=
    (Ζas
      (Ζbu H A) V ({x, y} : Edge α)).mp hCell
  have hrClean' := (Ζr
    (Ζbu H A) V hxy r).mp hrClean
  obtain ⟨hrV, hrDisj, hrxClean, hryClean⟩ :=
    Finset.mem_filter.mp hrClean'
  have hrOrig : r ∈ Ζe H V x y :=
    Finset.mem_filter.mpr
      ⟨hrV, hrDisj,
        Ζco H A hrxClean,
        Ζco H A hryClean⟩
  have hMeet : ¬ Disjoint p r :=
    Ζdu hAdm hxy hpOrig hrOrig
  have hInter : (p ∩ r).Nonempty := by
    by_contra h
    exact hMeet (Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨t, ht⟩ := hInter
  obtain ⟨htP, htR⟩ := Finset.mem_inter.mp ht
  have htA : t ∈ A := hpA htP
  have hty : t ≠ y := fun h => hyNotP (h ▸ htP)
  have hSub : ({t, y} : Edge α) ⊆ (r ∪ {y}) ∩ A := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ htR, htA⟩
    · have hvy : v = y := Finset.mem_singleton.mp hv
      subst v
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (by simp), hyA⟩
  have hTwo : 2 ≤ ((r ∪ {y}) ∩ A).card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_pair hty] at h
    exact h
  have hOne := (Finset.mem_filter.mp hryClean).2
  omega
theorem Ζlt
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : Ζar H A) (hAV : A ⊆ V)
    {x y : α} (hxy : x ≠ y)
    (hq : ({x, y} : Edge α) ∈ A.powersetCard 2) :
    ({x, y} : Edge α) ∉ Ζac (Ζbu H A) V := by
  obtain ⟨p, hpB, hpLink⟩ :=
    Ζjf H V A hU hA hAV hxy hq
  have hqA := (Finset.mem_powersetCard.mp hq).1
  have hyA : y ∈ A := hqA (by simp)
  have hpA : p ⊆ A := hpB.trans Finset.sdiff_subset
  have hyNotP : y ∉ p := by
    intro hy
    exact (Finset.mem_sdiff.mp (hpB hy)).2 (by simp)
  exact Ζls H V A p
    hAdm hxy hyA hpA hyNotP hpLink
theorem Ζqm
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : Ζar H A)
    (hAV : A ⊆ V)
    {x y : α} (hxy : x ≠ y)
    (hq : ({x, y} : Edge α) ∈ A.powersetCard 2) :
    ({x, y} : Edge α) ∈ Ζac H V := by
  obtain ⟨p, _, hpLink⟩ :=
    Ζjf H V A hU hA hAV hxy hq
  exact (Ζas H V ({x, y} : Edge α)).mpr
    ⟨Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hq).1.trans hAV,
        (Finset.mem_powersetCard.mp hq).2⟩,
      ⟨p, (Ζr H V hxy p).mpr hpLink⟩⟩
theorem Ζlu
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : Ζar H A)
    (hAV : A ⊆ V) :
    A.powersetCard 2 ⊆ Ζac H V := by
  intro q hq
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  exact Ζqm H V A hU hA hAV hxy hq
theorem Ζjj
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : Ζar H A) (hAV : A ⊆ V)
    {q : Edge α} (hq : q ∈ A.powersetCard 2) :
    q ∉ Ζac (Ζbu H A) V := by
  obtain ⟨x, y, hxy, rfl⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  exact Ζlt H V A
    hU hAdm hA hAV hxy hq
theorem Ζlv
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : Ζar H A)
    (hAV : A ⊆ V) :
    A.powersetCard 2 ⊆ Ζbp H V := by
  intro q hq
  have hN := Ζib H A q hU hA hq
  obtain ⟨z, hz⟩ : (Ζaw H A q).Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hzH : q ∪ {z} ∈ H := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hq).1.trans hAV,
        (Finset.mem_powersetCard.mp hq).2⟩,
      ⟨q ∪ {z}, hzH, Finset.subset_union_left⟩⟩
theorem Ζjk
    (H : Family α) (V A : Edge α)
    {q : Edge α} (hq : q ∈ A.powersetCard 2) :
    q ∉ Ζbp (Ζbu H A) V := by
  intro hqClean
  obtain ⟨_, E, hEClean, hqE⟩ := Finset.mem_filter.mp hqClean
  have hqA := (Finset.mem_powersetCard.mp hq).1
  have hqSub : q ⊆ E ∩ A := Finset.subset_inter hqE hqA
  have hTwo : 2 ≤ (E ∩ A).card := by
    have h := Finset.card_le_card hqSub
    rw [(Finset.mem_powersetCard.mp hq).2] at h
    exact h
  have hOne := (Finset.mem_filter.mp hEClean).2
  omega
private theorem Ζvk
    (A : Edge α) {x : α} (hxA : x ∉ A) :
    Set.InjOn (fun y : α => ({x, y} : Edge α)) A := by
  intro y hy z hz h
  change ({x, y} : Edge α) = ({x, z} : Edge α) at h
  have hyx : y ≠ x := fun e => hxA (e ▸ hy)
  have hymem : y ∈ ({x, z} : Edge α) := h ▸ (by simp)
  rcases Finset.mem_insert.mp hymem with e | e
  · exact False.elim (hyx e)
  · exact Finset.mem_singleton.mp e
private theorem Ζtf
    (A : Edge α) {x x' : α}
    (hx : x ∉ A) (hxx' : x ≠ x')
    (Y Z : Edge α) (hZA : Z ⊆ A) :
    Disjoint (Y.image fun y => ({x, y} : Edge α))
      (Z.image fun z => ({x', z} : Edge α)) := by
  apply Finset.disjoint_left.mpr
  intro q hqY hqZ
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqY
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hqZ
  have hxmem : x ∈ ({x', z} : Edge α) := heq ▸ (by simp)
  rcases Finset.mem_insert.mp hxmem with e | e
  · exact hxx' e
  · have hxz : x = z := Finset.mem_singleton.mp e
    exact hx (hxz.symm ▸ hZA hz)
theorem Ζpa
    (H : Family α) (V A : Edge α) :
    (Ζec H V A).card =
      ∑ x ∈ V \ A, (Ζda H A x).card := by
  unfold Ζec
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.card_image_of_injOn
    intro y hy z hz heq
    exact Ζvk A (Finset.mem_sdiff.mp hx).2
      (Ζgi H A x hy)
      (Ζgi H A x hz) heq
  · intro x hx x' hx' hxx'
    exact Ζtf A
      (Finset.mem_sdiff.mp hx).2 hxx'
      (Ζda H A x)
      (Ζda H A x')
      (Ζgi H A x')
theorem Ζky
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : Ζar H A) :
    2 * (∑ x ∈ V \ A, (Ζcz H A x).card) ≤
      (Ζec H V A).card := by
  rw [Ζpa]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  exact Ζss H A x hU hAdm hA
    (Finset.mem_sdiff.mp hx).2
theorem Ζlj
    (H : Family α) (V A : Edge α) :
    Disjoint (Ζec H V A) (A.powersetCard 2) := by
  apply Finset.disjoint_left.mpr
  intro q hq hqA
  obtain ⟨x, hx, hqX⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hqX
  exact (Finset.mem_sdiff.mp hx).2
    ((Finset.mem_powersetCard.mp hqA).1 (by simp))
private theorem Ζrp
    {β : Type*} [DecidableEq β]
    (S T B : Finset β) (hT : T ⊆ S) (hB : B ⊆ S)
    (hDisj : Disjoint B T) :
    B.card + T.card ≤ S.card := by
  rw [← Finset.card_union_of_disjoint hDisj]
  exact Finset.card_le_card (Finset.union_subset hB hT)
theorem Ζoe
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hA : Ζar H A)
    (hAV : A ⊆ V) :
    10 + (Ζbp (Ζbu H A) V).card ≤
      (Ζbp H V).card := by
  have hCount : (A.powersetCard 2).card = 10 := by
    rw [Finset.card_powersetCard, hA.1]
    decide
  rw [← hCount]
  apply Ζrp
  · exact Ζvq _ _ V (Ζco H A)
  · exact Ζlv H V A hU hA hAV
  · apply Finset.disjoint_left.mpr
    intro q hq
    exact Ζjk H V A hq
theorem Ζof
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hA : Ζar H A) (hAV : A ⊆ V) :
    10 + (Ζec H V A).card +
        (Ζac (Ζbu H A) V).card ≤
      (Ζac H V).card := by
  have hCount : (A.powersetCard 2).card = 10 := by
    rw [Finset.card_powersetCard, hA.1]
    decide
  have hDisj :=
    Ζlj H V A
  have hUnionCard :
      (A.powersetCard 2 ∪ Ζec H V A).card =
        10 + (Ζec H V A).card := by
    rw [Finset.card_union_of_disjoint hDisj.symm, hCount]
  rw [← hUnionCard]
  apply Ζrp
  · exact Ζvr _ _ V (Ζco H A)
  · exact Finset.union_subset
      (Ζlu H V A hU hA hAV)
      (Ζmo H V A hAV)
  · apply Finset.disjoint_left.mpr
    intro q hq
    rcases Finset.mem_union.mp hq with hqA | hqCert
    · exact Ζjj
        H V A hU hAdm hA hAV hqA
    · obtain ⟨x, hx, hqX⟩ := Finset.mem_biUnion.mp hqCert
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqX
      exact Ζmp
        H V A hAdm hAV hx hy
def Ζij
    (H : Family α) (V A : Edge α) : Family α :=
  (V \ A).biUnion fun x =>
    (Ζcz H A x).image fun p => p ∪ {x}
theorem Ζuh
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    H \ Ζbu H A ⊆
      Ζfq H A ∪ Ζij H V A := by
  intro E hRemoved
  obtain ⟨hEH, hNotClean⟩ := Finset.mem_sdiff.mp hRemoved
  have hAtLeast : 2 ≤ (E ∩ A).card := by
    by_contra h
    have hOne : (E ∩ A).card ≤ 1 := by omega
    exact hNotClean (Finset.mem_filter.mpr ⟨hEH, hOne⟩)
  by_cases hEA : E ⊆ A
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hEH, hEA⟩)
  · have hOutNonempty : (E \ A).Nonempty := by
      by_contra h
      exact hEA (Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp h))
    have hCardSplit := Finset.card_sdiff_add_card_inter E A
    have hCardE := hU hEH
    have hOutCard : (E \ A).card = 1 := by
      have hPos := Finset.card_pos.mpr hOutNonempty
      omega
    obtain ⟨x, hOutEq⟩ := Finset.card_eq_one.mp hOutCard
    have hxOut : x ∈ E \ A := hOutEq.symm ▸ (by simp)
    have hxV : x ∈ V \ A :=
      Finset.mem_sdiff.mpr
        ⟨hGround E hEH (Finset.mem_sdiff.mp hxOut).1,
          (Finset.mem_sdiff.mp hxOut).2⟩
    have hCoreCard : (E ∩ A).card = 2 := by omega
    have hCore : E ∩ A ∈ A.powersetCard 2 :=
      Finset.mem_powersetCard.mpr
        ⟨Finset.inter_subset_right, hCoreCard⟩
    have hEdgeEq : E = (E ∩ A) ∪ {x} := by
      calc
        E = (E \ A) ∪ (E ∩ A) :=
          (Finset.sdiff_union_inter E A).symm
        _ = (E ∩ A) ∪ {x} := by rw [hOutEq]; ac_rfl
    have hTrace : E ∩ A ∈ Ζcz H A x :=
      Finset.mem_filter.mpr ⟨hCore, hEdgeEq ▸ hEH⟩
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr
        ⟨x, hxV, Finset.mem_image.mpr
          ⟨E ∩ A, hTrace, hEdgeEq.symm⟩⟩)
theorem Ζui
    (H : Family α) (A : Edge α)
    (hU : Uniform 3 H) (hA : A.card = 5) :
    (Ζfq H A).card ≤ 10 := by
  have hSub : Ζfq H A ⊆ A.powersetCard 3 := by
    intro E hE
    obtain ⟨hEH, hEA⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_powersetCard.mpr ⟨hEA, hU hEH⟩
  have hCard := Finset.card_le_card hSub
  rwa [Finset.card_powersetCard, hA] at hCard
theorem Ζno
    (H : Family α) (V A : Edge α) :
    (Ζij H V A).card ≤
      ∑ x ∈ V \ A, (Ζcz H A x).card := by
  unfold Ζij
  calc
    ((V \ A).biUnion fun x =>
        (Ζcz H A x).image fun p => p ∪ {x}).card
      ≤ ∑ x ∈ V \ A,
          ((Ζcz H A x).image fun p => p ∪ {x}).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ x ∈ V \ A, (Ζcz H A x).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_image_le
theorem Ζtl
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hA : A.card = 5) :
    (H \ Ζbu H A).card ≤
      10 + ∑ x ∈ V \ A, (Ζcz H A x).card := by
  have hCover := Ζuh H V A hU hGround
  have hInternal := Ζui H A hU hA
  have hExternal := Ζno H V A
  calc
    (H \ Ζbu H A).card
      ≤ (Ζfq H A ∪ Ζij H V A).card :=
        Finset.card_le_card hCover
    _ ≤ (Ζfq H A).card +
        (Ζij H V A).card := Finset.card_union_le _ _
    _ ≤ 10 + ∑ x ∈ V \ A, (Ζcz H A x).card := by omega
theorem Ζnk
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hA : A.card = 5) :
    H.card ≤ (Ζbu H A).card +
      10 + ∑ x ∈ V \ A, (Ζcz H A x).card := by
  have hRemoved := Ζtl H V A hU hGround hA
  have hPartition := Finset.card_sdiff_add_card_eq_card
    (Ζco H A)
  omega
theorem Ζlk
    (H : Family α) (V A : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hA : Ζar H A) (hAV : A ⊆ V) :
    2 * H.card +
        (Ζbp (Ζbu H A) V).card +
        (Ζac (Ζbu H A) V).card ≤
      2 * (Ζbu H A).card +
        (Ζbp H V).card + (Ζac H V).card := by
  have hEdges := Ζnk H V A
    hU hGround hA.1
  have hPairs := Ζoe H V A
    hU hA hAV
  have hCells := Ζof H V A
    hU hAdm hA hAV
  have hCert := Ζky
    H V A hU hAdm hA
  omega
theorem Ζvb
    (H : Family α) (A : Edge α)
    (hU : Uniform 3 H)
    (hA : Ζar H A) :
    (Ζbu H A).card < H.card := by
  have hPos : 0 < (Ζfq H A).card := by
    have hDense := hA.2
    omega
  obtain ⟨E, hE⟩ := Finset.card_pos.mp hPos
  obtain ⟨hEH, hEA⟩ := Finset.mem_filter.mp hE
  have hNotClean : E ∉ Ζbu H A := by
    intro hEClean
    have hOne := (Finset.mem_filter.mp hEClean).2
    have hInter : E ∩ A = E := Finset.inter_eq_left.mpr hEA
    rw [hInter, hU hEH] at hOne
    omega
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset
    (Ζco H A)).mpr
  exact ⟨E, hEH, hNotClean⟩
private theorem Ζur
    (V : Edge α) (n : ℕ) :
    ∀ H : Family α, H.card = n →
      Uniform 3 H → Admissible H →
      (∀ E ∈ H, E ⊆ V) →
      ∃ H₀ : Family α,
        H₀ ⊆ H ∧
        (∀ A : Edge α, A ⊆ V → ¬ Ζar H₀ A) ∧
        2 * H.card + (Ζbp H₀ V).card +
            (Ζac H₀ V).card ≤
          2 * H₀.card + (Ζbp H V).card +
            (Ζac H V).card := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hCard hU hAdm hGround
    by_cases hExists : ∃ A : Edge α, A ⊆ V ∧ Ζar H A
    · obtain ⟨A, hAV, hA⟩ := hExists
      let H₁ := Ζbu H A
      have hH₁sub : H₁ ⊆ H := Ζco H A
      have hH₁lt : H₁.card < n := by
        change (Ζbu H A).card < n
        rw [← hCard]
        exact Ζvb H A hU hA
      have hH₁ground : ∀ E ∈ H₁, E ⊆ V := by
        intro E hEH₁
        exact hGround E (hH₁sub hEH₁)
      obtain ⟨H₀, hH₀sub, hFree, hBal₁⟩ :=
        ih H₁.card hH₁lt H₁ rfl
          (Ζva H A hU)
          (Ζtt H A hAdm)
          hH₁ground
      have hBal₀ :=
        Ζlk
          H V A hU hAdm hGround hA hAV
      change 2 * H.card + (Ζbp H₁ V).card +
          (Ζac H₁ V).card ≤
        2 * H₁.card + (Ζbp H V).card +
          (Ζac H V).card at hBal₀
      refine ⟨H₀, hH₀sub.trans hH₁sub, hFree, ?_⟩
      omega
    · refine ⟨H, Finset.Subset.refl H, ?_, ?_⟩
      · intro A hAV hNear
        exact hExists ⟨A, hAV, hNear⟩
      · omega
theorem Ζtm
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    ∃ H₀ : Family α,
      H₀ ⊆ H ∧
      (∀ A : Edge α, A ⊆ V → ¬ Ζar H₀ A) ∧
      2 * H.card + (Ζbp H₀ V).card +
          (Ζac H₀ V).card ≤
        2 * H₀.card + (Ζbp H V).card +
          (Ζac H V).card :=
  Ζur V H.card H rfl hU hAdm hGround
theorem Ζqn
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hBase : ∀ K : Family α,
      Uniform 3 K → Admissible K →
      (∀ E ∈ K, E ⊆ V) →
      (∀ A : Edge α, A ⊆ V → ¬ Ζar K A) →
      2 * K.card ≤ (Ζbp K V).card + (Ζac K V).card) :
    2 * H.card ≤ (Ζbp H V).card + (Ζac H V).card := by
  obtain ⟨H₀, hSub, hFree, hBalance⟩ :=
    Ζtm H V hU hAdm hGround
  have hBase₀ := hBase H₀
    (fun E hE => hU (hSub hE))
    (Ζvd hSub hAdm)
    (fun E hE => hGround E (hSub hE))
    hFree
  omega
end JSP523.Rank3
end
section
namespace JSP523.Rank3
def Ζg (d : ℕ) : ℚ :=
  if d ≤ 3 then 0 else ((d : ℚ) - 3) / (d : ℚ)
def Ζal (d : ℕ) : ℚ :=
  if d = 0 then 0 else Ζcm d / (d : ℚ)
def Ζfx (d e : ℕ) : ℚ :=
  Ζg d + Ζg e -
    ((d : ℚ) - (e : ℚ)) * (Ζg d - Ζg e)
theorem Ζek (d : ℕ) : 0 ≤ Ζg d := by
  by_cases hsmall : d ≤ 3
  · simp [Ζg, hsmall]
  · have hd : 4 ≤ d := by omega
    have hdpos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnum : (0 : ℚ) ≤ (d : ℚ) - 3 := by
      have : (4 : ℚ) ≤ d := by exact_mod_cast hd
      linarith
    simp only [Ζg, Ζdp hsmall]
    exact div_nonneg hnum hdpos.le
theorem Ζqo (d : ℕ) : Ζg d < 1 := by
  by_cases hsmall : d ≤ 3
  · simp [Ζg, hsmall]
  · have hd : 4 ≤ d := by omega
    have hdpos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    simp only [Ζg, Ζdp hsmall]
    apply (div_lt_iff₀ hdpos).mpr
    linarith
theorem Ζdk
    {d : ℕ} (hd : d ≤ 3) : Ζg d = 0 := by
  simp [Ζg, hd]
theorem Ζmu (d : ℕ) :
    (d : ℚ) * Ζg d = Ζbb d := by
  by_cases hsmall : d ≤ 3
  · have hsurplus : ¬ 3 < d := by omega
    simp [Ζg, Ζbb, hsmall, hsurplus]
  · have hlarge : 3 < d := by omega
    have hdne : (d : ℚ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    simp only [Ζg, Ζdp hsmall,
      Ζbb, Ζie hlarge]
    field_simp
theorem Ζdi {d e : ℕ} (hde : d ≤ e) :
    Ζg d ≤ Ζg e := by
  by_cases hdsmall : d ≤ 3
  · rw [Ζdk hdsmall]
    exact Ζek e
  · have hesmall : ¬ e ≤ 3 := by omega
    have hdpos : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    have hepos : (0 : ℚ) < e := by exact_mod_cast (by omega : 0 < e)
    have hcast : (d : ℚ) ≤ (e : ℚ) := by exact_mod_cast hde
    simp only [Ζg, Ζdp hdsmall,
      Ζdp hesmall]
    apply (div_le_div_iff₀ hdpos hepos).mpr
    nlinarith
theorem Ζme (d : ℕ) :
    Ζal d = ((d : ℚ) - 2) * Ζg d := by
  by_cases hd0 : d = 0
  · subst d; norm_num [Ζal, Ζg]
  by_cases hsmall : d ≤ 3
  · have hcases : d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hcases with h | h | h
    · subst d; norm_num [Ζal, Ζcm, Ζg]
    · subst d; norm_num [Ζal, Ζcm, Ζg]
    · subst d; norm_num [Ζal, Ζcm, Ζg]
  · have hd : 4 ≤ d := by omega
    have hdq : (d : ℚ) ≠ 0 := by
      exact_mod_cast (by omega : d ≠ 0)
    simp [Ζal, Ζcm, Ζg, hd, hsmall, hd0]
    rw [mul_div_assoc]
theorem Ζgs (d : ℕ) :
    (d : ℚ) * Ζal d = Ζcm d := by
  by_cases hd0 : d = 0
  · subst d
    norm_num [Ζal, Ζcm]
  · have hdne : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    simp only [Ζal, Ζdp hd0]
    field_simp
theorem Ζvp (d e : ℕ) : Ζfx d e = Ζfx e d := by
  unfold Ζfx
  ring
private theorem Ζny
    {d e : ℕ} (hde : d ≤ e) :
    Ζfx d e ≤ 2 * Ζg d := by
  by_cases heq : d = e
  · subst e
    unfold Ζfx
    nlinarith
  · have hgapNat : d + 1 ≤ e := by omega
    have hgap : (0 : ℚ) ≤ (e : ℚ) - (d : ℚ) - 1 := by
      have hcast : (d : ℚ) + 1 ≤ (e : ℚ) := by
        exact_mod_cast hgapNat
      linarith
    have hfgap : (0 : ℚ) ≤ Ζg e - Ζg d := by
      have hf := Ζdi hde
      linarith
    have hprod := mul_nonneg hgap hfgap
    unfold Ζfx
    nlinarith
theorem Ζfr (d e : ℕ) :
    Ζfx d e ≤ 2 * min (Ζg d) (Ζg e) := by
  by_cases hde : d ≤ e
  · have hf := Ζdi hde
    rw [min_eq_left hf]
    exact Ζny hde
  · have hed : e ≤ d := by omega
    have hf := Ζdi hed
    rw [min_eq_right hf, Ζvp]
    exact Ζny hed
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section PairGraphs
variable {α : Type*} [DecidableEq α]
private theorem Ζel
    {p : Edge α} {a b : α}
    (hp : p.card = 2) (ha : a ∈ p) (hb : b ∈ p)
    (hab : a ≠ b) : p = {a, b} := by
  have hsub : ({a, b} : Edge α) ⊆ p := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hxb
    · exact hxa ▸ ha
    · exact (Finset.mem_singleton.mp hxb) ▸ hb
  have hcard : p.card ≤ ({a, b} : Edge α).card := by
    rw [hp, Finset.card_pair hab]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
private theorem Ζhk
    {W : Edge α} {a b : α}
    (hmeet : ¬ Disjoint W ({a, b} : Edge α)) :
    a ∈ W ∨ b ∈ W := by
  by_cases ha : a ∈ W
  · exact Or.inl ha
  · right
    by_contra hb
    apply hmeet
    apply Finset.disjoint_left.mpr
    intro x hxW hxpair
    rcases Finset.mem_insert.mp hxpair with hxa | hxb
    · exact ha (hxa ▸ hxW)
    · exact hb ((Finset.mem_singleton.mp hxb) ▸ hxW)
theorem Ζre
    (G : Family α)
    (hG : G.Nonempty)
    (hpair : ∀ p ∈ G, p.card = 2)
    (hmeet : ∀ p ∈ G, ∀ q ∈ G, ¬ Disjoint p q)
    (hnocenter : ¬ ∃ x : α, ∀ p ∈ G, x ∈ p) :
    ∃ a b c : α, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      G ⊆ ({({a, b} : Edge α), ({b, c} : Edge α),
        ({a, c} : Edge α)} : Family α) := by
  obtain ⟨E, hE⟩ := hG
  obtain ⟨a, b, hab, hEpair⟩ := Finset.card_eq_two.mp (hpair E hE)
  have habG : ({a, b} : Edge α) ∈ G := hEpair ▸ hE
  have hFexists : ∃ F ∈ G, a ∉ F := by
    by_contra h
    apply hnocenter
    refine ⟨a, ?_⟩
    intro F hFG
    by_contra haF
    exact h ⟨F, hFG, haF⟩
  obtain ⟨F, hFG, haF⟩ := hFexists
  have hbF : b ∈ F := by
    rcases Ζhk (hmeet F hFG _ habG) with haF' | hbF'
    · exact False.elim (haF haF')
    · exact hbF'
  have hFcard : F.card = 2 := hpair F hFG
  have hFrest : (F.erase b).Nonempty := by
    apply Finset.card_pos.mp
    have hcardErase := Finset.card_erase_add_one hbF
    omega
  obtain ⟨c, hcErase⟩ := hFrest
  have hcb : c ≠ b := (Finset.mem_erase.mp hcErase).1
  have hcF : c ∈ F := (Finset.mem_erase.mp hcErase).2
  have hca : c ≠ a := by
    intro hca
    exact haF (hca ▸ hcF)
  have hbc : b ≠ c := Ne.symm hcb
  have hac : a ≠ c := Ne.symm hca
  have hFpair : F = {b, c} :=
    Ζel hFcard hbF hcF hbc
  have hbcG : ({b, c} : Edge α) ∈ G := hFpair ▸ hFG
  have hTexists : ∃ T ∈ G, b ∉ T := by
    by_contra h
    apply hnocenter
    refine ⟨b, ?_⟩
    intro T hTG
    by_contra hbT
    exact h ⟨T, hTG, hbT⟩
  obtain ⟨T, hTG, hbT⟩ := hTexists
  have haT : a ∈ T := by
    rcases Ζhk (hmeet T hTG _ habG) with haT' | hbT'
    · exact haT'
    · exact False.elim (hbT hbT')
  have hcT : c ∈ T := by
    rcases Ζhk (hmeet T hTG _ hbcG) with hbT' | hcT'
    · exact False.elim (hbT hbT')
    · exact hcT'
  have hTpair : T = {a, c} :=
    Ζel (hpair T hTG) haT hcT hac
  have hacG : ({a, c} : Edge α) ∈ G := hTpair ▸ hTG
  refine ⟨a, b, c, hab, hbc, hac, ?_⟩
  intro W hWG
  have hWcard : W.card = 2 := hpair W hWG
  have hWab : a ∈ W ∨ b ∈ W :=
    Ζhk (hmeet W hWG _ habG)
  have hWbc : b ∈ W ∨ c ∈ W :=
    Ζhk (hmeet W hWG _ hbcG)
  have hWac : a ∈ W ∨ c ∈ W :=
    Ζhk (hmeet W hWG _ hacG)
  rcases hWab with haW | hbW
  · rcases hWbc with hbW | hcW
    · have heq : W = {a, b} :=
        Ζel hWcard haW hbW hab
      simp [heq]
    · have heq : W = {a, c} :=
        Ζel hWcard haW hcW hac
      simp [heq]
  · rcases hWac with haW | hcW
    · have heq : W = {a, b} :=
        Ζel hWcard haW hbW hab
      simp [heq]
    · have heq : W = {b, c} :=
        Ζel hWcard hbW hcW hbc
      simp [heq]
theorem Ζic
    (G : Family α)
    (hpair : ∀ p ∈ G, p.card = 2)
    (hmeet : ∀ p ∈ G, ∀ q ∈ G, ¬ Disjoint p q) :
    (∃ x : α, ∀ p ∈ G, x ∈ p) ∨ G.card ≤ 3 := by
  by_cases hG : G.Nonempty
  · by_cases hcenter : ∃ x : α, ∀ p ∈ G, x ∈ p
    · exact Or.inl hcenter
    · right
      obtain ⟨a, b, c, _, _, _, hsub⟩ :=
        Ζre G hG hpair hmeet hcenter
      exact (Finset.card_le_card hsub).trans (Finset.card_le_three)
  · right
    have hEmpty : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    simp [hEmpty]
theorem Ζog
    (G : Family α)
    (hpair : ∀ p ∈ G, p.card = 2)
    (hlarge : 1 < G.card)
    {a b : α}
    (ha : ∀ p ∈ G, a ∈ p)
    (hb : ∀ p ∈ G, b ∈ p) :
    a = b := by
  by_contra hab
  have hsub : G ⊆ ({({a, b} : Edge α)} : Family α) := by
    intro p hp
    have heq : p = {a, b} :=
      Ζel (hpair p hp) (ha p hp) (hb p hp) hab
    exact Finset.mem_singleton.mpr heq
  have hbound := Finset.card_le_card hsub
  have hsingle : ({({a, b} : Edge α)} : Family α).card = 1 := by simp
  omega
theorem Ζrf
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2) :
    (∃ x : α, ∀ p ∈ Ζc H V q, x ∈ p) ∨
      (Ζc H V q).card ≤ 3 := by
  apply Ζic (Ζc H V q)
  · intro p hp
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp t ht
    exact Ζdw hH hq hp ht
theorem Ζgu
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hlarge : 3 < (Ζc H V q).card) :
    ∃ x : α, (∀ p ∈ Ζc H V q, x ∈ p) ∧
      ∀ y : α, (∀ p ∈ Ζc H V q, y ∈ p) → y = x := by
  rcases Ζrf hH hq with ⟨x, hx⟩ | hsmall
  · refine ⟨x, hx, ?_⟩
    intro y hy
    have hpair : ∀ p ∈ Ζc H V q, p.card = 2 := by
      intro p hp
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
    have htwo : 1 < (Ζc H V q).card := by omega
    exact (Ζog
      (Ζc H V q) hpair htwo hx hy).symm
  · omega
end PairGraphs
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section LinkFiberBound
variable {α : Type*} [DecidableEq α]
def Ζcu (H : Family α) (V q : Edge α) (z : α) : Edge α :=
  V.filter (fun t => ({z, t} : Edge α) ∈ Ζc H V q)
theorem Ζhn
    {H : Family α} {V q p : Edge α} {z : α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ Ζc H V q)
    (hzp : z ∉ p) :
    Ζcu H V q z ⊆ p := by
  intro t ht
  have hzt : ({z, t} : Edge α) ∈ Ζc H V q :=
    (Finset.mem_filter.mp ht).2
  have hmeet : ¬ Disjoint p ({z, t} : Edge α) :=
    Ζdw hH hq hp hzt
  by_contra htp
  apply hmeet
  apply Finset.disjoint_left.mpr
  intro x hx hxzt
  rcases Finset.mem_insert.mp hxzt with hzx | hxt
  · exact hzp (hzx ▸ hx)
  · exact htp ((Finset.mem_singleton.mp hxt) ▸ hx)
theorem Ζsu
    {H : Family α} {V q p : Edge α} {z : α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ Ζc H V q)
    (hzp : z ∉ p) :
    (Ζcu H V q z).card ≤ 2 := by
  have hsub := Ζhn hH hq hp hzp
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  exact (Finset.card_le_card hsub).trans_eq hp2
theorem Ζbk
    (H : Family α) (V : Edge α)
    {z v x y u : α}
    (hvV : v ∈ V)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxyLink : ({x, y} : Edge α) ∈ Ζe H V z v)
    (hxuLink : ({x, u} : Edge α) ∈ Ζe H V z v) :
    ({v, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
  obtain ⟨hxyV, hxyOut, _, hxyv⟩ := Finset.mem_filter.mp hxyLink
  obtain ⟨_, hxuOut, _, hxuv⟩ := Finset.mem_filter.mp hxuLink
  have hxV : x ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
  have hvNotXY : v ∉ ({x, y} : Edge α) := by
    intro hv
    exact (Finset.disjoint_left.mp hxyOut) hv (by simp)
  have hvNotXU : v ∉ ({x, u} : Edge α) := by
    intro hv
    exact (Finset.disjoint_left.mp hxuOut) hv (by simp)
  have hvx : v ≠ x := by
    intro h
    exact hvNotXY (by simp [h])
  have hvy : v ≠ y := by
    intro h
    exact hvNotXY (by simp [h])
  have hvu : v ≠ u := by
    intro h
    exact hvNotXU (by simp [h])
  have hpV : ({v, x} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      have hw' : w = v ∨ w = x := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
      rcases hw' with rfl | rfl
      · exact hvV
      · exact hxV
    · exact Finset.card_pair hvx
  have hpOut : Disjoint ({v, x} : Edge α) ({y, u} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro w hw hcell
    have hw' : w = v ∨ w = x := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
    have hcell' : w = y ∨ w = u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcell
    rcases hw' with hwv | hwx
    · rcases hcell' with hwy | hwu
      · exact hvy (hwv.symm.trans hwy)
      · exact hvu (hwv.symm.trans hwu)
    · rcases hcell' with hwy | hwu
      · exact hxy (hwx.symm.trans hwy)
      · exact hxu (hwx.symm.trans hwu)
  have hpy : ({v, x} : Edge α) ∪ {y} ∈ H := by
    have heq : ({v, x} : Edge α) ∪ {y} =
        ({x, y} : Edge α) ∪ {v} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hxyv
  have hpu : ({v, x} : Edge α) ∪ {u} ∈ H := by
    have heq : ({v, x} : Edge α) ∪ {u} =
        ({x, u} : Edge α) ∪ {v} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hxuv
  have hpOrient : ({v, x} : Edge α) ∈ Ζe H V y u :=
    Finset.mem_filter.mpr ⟨hpV, hpOut, hpy, hpu⟩
  exact (Ζr H V hyu _).mpr hpOrient
def Ζm
    (H : Family α) (V : Edge α) (z y u : α) : Edge α :=
  V.filter (fun t => t ≠ z ∧ t ≠ y ∧ t ≠ u ∧
    ({y, t} : Edge α) ∪ {z} ∈ H ∧
    ({u, t} : Edge α) ∪ {z} ∈ H)
theorem Ζfz
    (H : Family α) (V : Edge α)
    {z y u : α}
    (hzV : z ∈ V) (hzy : z ≠ y) (hzu : z ≠ u) (hyu : y ≠ u) :
    Ζm H V z y u ⊆
      Ζcu H V ({y, u} : Edge α) z := by
  intro t ht
  obtain ⟨htV, htz, hty, htu, htyz, htuz⟩ := Finset.mem_filter.mp ht
  have hztV : ({z, t} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      have hw' : w = z ∨ w = t := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
      rcases hw' with rfl | rfl
      · exact hzV
      · exact htV
    · exact Finset.card_pair (Ne.symm htz)
  have hdis : Disjoint ({z, t} : Edge α) ({y, u} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro w hw hcell
    have hw' : w = z ∨ w = t := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
    have hcell' : w = y ∨ w = u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcell
    rcases hw' with hwz | hwt
    · rcases hcell' with hwy | hwu
      · exact hzy (hwz.symm.trans hwy)
      · exact hzu (hwz.symm.trans hwu)
    · rcases hcell' with hwy | hwu
      · exact hty (hwt.symm.trans hwy)
      · exact htu (hwt.symm.trans hwu)
  have hzyEdge : ({z, t} : Edge α) ∪ {y} ∈ H := by
    have heq : ({z, t} : Edge α) ∪ {y} =
        ({y, t} : Edge α) ∪ {z} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ htyz
  have hzuEdge : ({z, t} : Edge α) ∪ {u} ∈ H := by
    have heq : ({z, t} : Edge α) ∪ {u} =
        ({u, t} : Edge α) ∪ {z} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ htuz
  have hOrient : ({z, t} : Edge α) ∈ Ζe H V y u :=
    Finset.mem_filter.mpr ⟨hztV, hdis, hzyEdge, hzuEdge⟩
  exact Finset.mem_filter.mpr
    ⟨htV, (Ζr H V hyu _).mpr hOrient⟩
theorem Ζjg
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxyLink : ({x, y} : Edge α) ∈ Ζe H V z v)
    (hxuLink : ({x, u} : Edge α) ∈ Ζe H V z v) :
    (Ζm H V z y u).card ≤ 2 := by
  have hrecip : ({v, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α) :=
    Ζbk H V hvV hxy hxu hyu hxyLink hxuLink
  obtain ⟨_, hxyOut, _, _⟩ := Finset.mem_filter.mp hxyLink
  obtain ⟨_, hxuOut, _, _⟩ := Finset.mem_filter.mp hxuLink
  have hzNotXY : z ∉ ({x, y} : Edge α) := by
    intro hz
    exact (Finset.disjoint_left.mp hxyOut) hz (by simp)
  have hzNotXU : z ∉ ({x, u} : Edge α) := by
    intro hz
    exact (Finset.disjoint_left.mp hxuOut) hz (by simp)
  have hzx : z ≠ x := by
    intro h
    exact hzNotXY (by simp [h])
  have hzy : z ≠ y := by
    intro h
    exact hzNotXY (by simp [h])
  have hzu : z ≠ u := by
    intro h
    exact hzNotXU (by simp [h])
  have hzNotVX : z ∉ ({v, x} : Edge α) := by
    simp [hzv, hzx]
  have hcell : ({y, u} : Edge α) ∈ V.powersetCard 2 := by
    have hxyV : ({x, y} : Edge α) ∈ V.powersetCard 2 :=
      (Finset.mem_filter.mp hxyLink).1
    have hxuV : ({x, u} : Edge α) ∈ V.powersetCard 2 :=
      (Finset.mem_filter.mp hxuLink).1
    have hyV : y ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
    have huV : u ∈ V := (Finset.mem_powersetCard.mp hxuV).1 (by simp)
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      have hw' : w = y ∨ w = u := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
      rcases hw' with rfl | rfl
      · exact hyV
      · exact huV
    · exact Finset.card_pair hyu
  have hfiber : (Ζcu H V ({y, u} : Edge α) z).card ≤ 2 :=
    Ζsu hH hcell hrecip hzNotVX
  exact (Finset.card_le_card
    (Ζfz H V hzV hzy hzu hyu)).trans hfiber
end LinkFiberBound
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section RootedSignedWeights
variable {α : Type*} [DecidableEq α]
def Ζaf (H : Family α) (V : Edge α) (z : α) : Family α :=
  (V.powersetCard 2).filter (fun p => z ∉ p ∧ p ∪ {z} ∈ H)
def Ζk (H : Family α) (V : Edge α) (z x : α) : Edge α :=
  Ζb H V ({z, x} : Edge α)
theorem Ζhx
    (H : Family α) (V : Edge α) (z x : α) :
    Ζk H V z x ⊆ V :=
  Ζgg H V _
theorem Ζvc
    (H : Family α) (V : Edge α) (z x : α) :
    z ∉ Ζk H V z x := by
  intro hz
  exact (Finset.mem_filter.mp hz).2.1 (by simp)
theorem Ζpu
    (H : Family α) (V : Edge α) (z x : α) :
    x ∉ Ζk H V z x := by
  intro hx
  exact (Finset.mem_filter.mp hx).2.1 (by simp)
theorem Ζpv
    (H : Family α) (V : Edge α) {z x y : α}
    (hxV : x ∈ V) (hzx : z ≠ x)
    (hy : y ∈ Ζk H V z x) :
    x ∈ Ζk H V z y := by
  obtain ⟨_, hyOut, htrip⟩ := Finset.mem_filter.mp hy
  have hyz : y ≠ z := by
    intro h
    exact hyOut (by simp [h])
  have hyx : y ≠ x := by
    intro h
    exact hyOut (by simp [h])
  apply Finset.mem_filter.mpr
  refine ⟨hxV, ?_, ?_⟩
  · simp [Ne.symm hzx, Ne.symm hyx]
  · have heq : ({z, y} : Edge α) ∪ {x} =
        ({z, x} : Edge α) ∪ {y} := by
      ext t
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ htrip
private theorem Ζkx (a b c : α) :
    ({a, b} : Edge α) ∪ {c} = ({b, c} : Edge α) ∪ {a} := by
  ext w
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto
theorem Ζbc
    (H : Family α) (V : Edge α) (z x u : α) :
    Ζm H V z x u ⊆ Ζk H V z x := by
  intro t ht
  obtain ⟨htV, htz, htx, _, hxtz, _⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨htV, ?_, ?_⟩
  · simp [htz, htx]
  · rw [Ζkx z x t]
    exact hxtz
theorem Ζju
    (H : Family α) (V : Edge α) (z x u : α) :
    Ζm H V z x u ⊆ Ζk H V z u := by
  intro t ht
  obtain ⟨htV, htz, _, htu, _, hutz⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨htV, ?_, ?_⟩
  · simp [htz, htu]
  · rw [Ζkx z u t]
    exact hutz
theorem Ζge
    (H : Family α) (V : Edge α) (z x u : α) :
    Ζm H V z x u =
      Ζk H V z x ∩ Ζk H V z u := by
  ext t
  constructor
  · intro ht
    exact Finset.mem_inter.mpr
      ⟨Ζbc H V z x u ht,
        Ζju H V z x u ht⟩
  · intro ht
    obtain ⟨htx, htu⟩ := Finset.mem_inter.mp ht
    obtain ⟨htV, htNotZX, hxtz⟩ := Finset.mem_filter.mp htx
    obtain ⟨_, htNotZU, hutz⟩ := Finset.mem_filter.mp htu
    have htz : t ≠ z := by
      intro h
      exact htNotZX (by simp [h])
    have htx' : t ≠ x := by
      intro h
      exact htNotZX (by simp [h])
    have htu' : t ≠ u := by
      intro h
      exact htNotZU (by simp [h])
    apply Finset.mem_filter.mpr
    refine ⟨htV, htz, htx', htu', ?_, ?_⟩
    · rw [← Ζkx z x t]
      exact hxtz
    · rw [← Ζkx z u t]
      exact hutz
def Ζo
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  (∑ u ∈ (Ζk H V z y).erase x,
      Ζg (Ζm H V z x u).card) +
    (∑ v ∈ (Ζk H V z x).erase y,
      Ζg (Ζm H V z y v).card) -
    Ζal (Ζk H V z x).card -
    Ζal (Ζk H V z y).card
theorem Ζfk
    (H : Family α) (V : Edge α) (z x y : α) :
    Ζo H V z x y =
      Ζo H V z y x := by
  unfold Ζo
  ring
def Ζeq
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  (∑ u ∈ (Ζk H V z y).erase x,
      (Ζg (Ζk H V z x).card -
        Ζg (Ζm H V z x u).card)) +
    (∑ v ∈ (Ζk H V z x).erase y,
      (Ζg (Ζk H V z y).card -
        Ζg (Ζm H V z y v).card))
theorem Ζtg
    (H : Family α) (V : Edge α) (z x y : α) :
    0 ≤ Ζeq H V z x y := by
  unfold Ζeq
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro u hu
    apply sub_nonneg.mpr
    exact Ζdi (Finset.card_le_card
      (Ζbc H V z x u))
  · apply Finset.sum_nonneg
    intro v hv
    apply sub_nonneg.mpr
    exact Ζdi (Finset.card_le_card
      (Ζbc H V z y v))
theorem Ζeh
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y) :
    y ∈ Ζk H V z x ∧ x ∈ Ζk H V z y := by
  obtain ⟨hxyV, hzOut, hxyz⟩ := Finset.mem_filter.mp hxy
  have hxV : x ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
  have hyV : y ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
  have hzx : z ≠ x := by
    intro h
    exact hzOut (by simp [h])
  have hzy : z ≠ y := by
    intro h
    exact hzOut (by simp [h])
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨hyV, ?_, ?_⟩
    · simp [Ne.symm hzy, Ne.symm hxyNe]
    · rw [Ζkx z x y]
      exact hxyz
  · apply Finset.mem_filter.mpr
    refine ⟨hxV, ?_, ?_⟩
    · simp [Ne.symm hzx, hxyNe]
    · have heq : ({z, y} : Edge α) ∪ {x} =
          ({x, y} : Edge α) ∪ {z} := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq.symm ▸ hxyz
theorem Ζik
    (H : Family α) (V : Edge α) {z x y : α}
    (hxV : x ∈ V) (hzx : z ≠ x) :
    y ∈ Ζk H V z x ↔
      ({x, y} : Edge α) ∈ Ζaf H V z := by
  constructor
  · intro hy
    obtain ⟨hyV, hyOut, htrip⟩ := Finset.mem_filter.mp hy
    have hyz : y ≠ z := by
      intro h
      exact hyOut (by simp [h])
    have hyx : y ≠ x := by
      intro h
      exact hyOut (by simp [h])
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro t ht
        rcases Finset.mem_insert.mp ht with htx | hty
        · exact htx ▸ hxV
        · exact (Finset.mem_singleton.mp hty) ▸ hyV
      · exact Finset.card_pair (Ne.symm hyx)
    · constructor
      · simp [hzx, Ne.symm hyz]
      · rw [← Ζkx z x y]
        exact htrip
  · intro hxy
    have hxyNe : x ≠ y := by
      intro h
      have hp2 : ({x, y} : Edge α).card = 2 :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hxy).1).2
      simp [h] at hp2
    exact (Ζeh H V hxy hxyNe).1
theorem Ζdr
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y) :
    Ζo H V z x y =
      Ζfx (Ζk H V z x).card
        (Ζk H V z y).card -
      Ζeq H V z x y := by
  obtain ⟨hyNx, hxNy⟩ := Ζeh H V hxy hxyNe
  let Nx := Ζk H V z x
  let Ny := Ζk H V z y
  let dx := Nx.card
  let dy := Ny.card
  have hxCard : ((Ny.erase x).card : ℚ) = (dy : ℚ) - 1 := by
    have hNat : (Ny.erase x).card + 1 = Ny.card :=
      Finset.card_erase_add_one hxNy
    have hQ : ((Ny.erase x).card : ℚ) + 1 = (Ny.card : ℚ) := by
      exact_mod_cast hNat
    dsimp [dy]
    linarith
  have hyCard : ((Nx.erase y).card : ℚ) = (dx : ℚ) - 1 := by
    have hNat : (Nx.erase y).card + 1 = Nx.card :=
      Finset.card_erase_add_one hyNx
    have hQ : ((Nx.erase y).card : ℚ) + 1 = (Nx.card : ℚ) := by
      exact_mod_cast hNat
    dsimp [dx]
    linarith
  have hSumX :
      (∑ u ∈ Ny.erase x, Ζg dx) =
        ((dy : ℚ) - 1) * Ζg dx := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hxCard]
  have hSumY :
      (∑ v ∈ Nx.erase y, Ζg dy) =
        ((dx : ℚ) - 1) * Ζg dy := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hyCard]
  have hBudgetX := Ζme dx
  have hBudgetY := Ζme dy
  have hsum : Ζo H V z x y +
      Ζeq H V z x y = Ζfx dx dy := by
    simp only [Ζo, Ζeq,
      Finset.sum_sub_distrib]
    change
      ((∑ u ∈ Ny.erase x,
          Ζg (Ζm H V z x u).card) +
        (∑ v ∈ Nx.erase y,
          Ζg (Ζm H V z y v).card) -
        Ζal dx - Ζal dy) +
        ((∑ u ∈ Ny.erase x, Ζg dx) -
          (∑ u ∈ Ny.erase x,
            Ζg (Ζm H V z x u).card) +
          ((∑ v ∈ Nx.erase y, Ζg dy) -
            (∑ v ∈ Nx.erase y,
              Ζg (Ζm H V z y v).card))) =
        Ζfx dx dy
    rw [hSumX, hSumY, hBudgetX, hBudgetY]
    unfold Ζfx
    ring
  dsimp [Nx, Ny, dx, dy] at hsum
  linarith
theorem Ζjr
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y) :
    Ζo H V z x y ≤
      2 * min (Ζg (Ζk H V z x).card)
        (Ζg (Ζk H V z y).card) := by
  have hEq := Ζdr H V hxy hxyNe
  have hDef := Ζtg H V z x y
  have hBase := Ζfr
    (Ζk H V z x).card (Ζk H V z y).card
  linarith
theorem Ζmf
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y)
    (hpositive : 0 < Ζo H V z x y) :
    4 ≤ (Ζk H V z x).card ∧
      4 ≤ (Ζk H V z y).card := by
  have hbound := Ζjr H V hxy hxyNe
  have hminpos : 0 < min
      (Ζg (Ζk H V z x).card)
      (Ζg (Ζk H V z y).card) := by
    linarith
  have hxpos : 0 < Ζg (Ζk H V z x).card :=
    lt_of_lt_of_le hminpos (min_le_left _ _)
  have hypos : 0 < Ζg (Ζk H V z y).card :=
    lt_of_lt_of_le hminpos (min_le_right _ _)
  constructor
  · by_contra h
    have hsmall : (Ζk H V z x).card ≤ 3 := by omega
    rw [Ζdk hsmall] at hxpos
    exact (not_lt_of_ge le_rfl) hxpos
  · by_contra h
    have hsmall : (Ζk H V z y).card ≤ 3 := by omega
    rw [Ζdk hsmall] at hypos
    exact (not_lt_of_ge le_rfl) hypos
theorem Ζtn
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y) :
    Ζo H V z x y < 2 := by
  have hbound := Ζjr H V hxy hxyNe
  have hxlt := Ζqo (Ζk H V z x).card
  have hminlt : min
      (Ζg (Ζk H V z x).card)
      (Ζg (Ζk H V z y).card) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) hxlt
  linarith
def Ζbs
    (H : Family α) (V : Edge α) (z x y : α) : Edge α :=
  ((Ζk H V z y).erase x).filter
    (fun u => (Ζm H V z x u).card ≤ 3)
def Ζav
    (H : Family α) (V : Edge α) (z x y : α) : Edge α :=
  ((Ζk H V z x).erase y).filter
    (fun v => (Ζm H V z y v).card ≤ 3)
private theorem Ζqp
    {β : Type*} [DecidableEq β]
    (S : Finset β) (d : ℕ) (degree : β → ℕ)
    (hdegree : ∀ t ∈ S, degree t ≤ d)
    (m : ℚ) (hm : m ≤ Ζg d) :
    ((S.filter (fun t => degree t ≤ 3)).card : ℚ) * m ≤
      ∑ t ∈ S, (Ζg d - Ζg (degree t)) := by
  let W := S.filter (fun t => degree t ≤ 3)
  have hWsub : W ⊆ S := Finset.filter_subset _ _
  have hweak : (∑ t ∈ W, m) ≤
      ∑ t ∈ W, (Ζg d - Ζg (degree t)) := by
    apply Finset.sum_le_sum
    intro t ht
    have hsmall : degree t ≤ 3 := (Finset.mem_filter.mp ht).2
    rw [Ζdk hsmall]
    linarith
  have hrest :
      (∑ t ∈ W, (Ζg d - Ζg (degree t))) ≤
        ∑ t ∈ S, (Ζg d - Ζg (degree t)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hWsub
    intro t htS htW
    exact sub_nonneg.mpr (Ζdi (hdegree t htS))
  have hconst : ((W.card : ℚ) * m) = ∑ t ∈ W, m := by
    simp [Finset.sum_const, nsmul_eq_mul]
  exact hconst.trans_le (hweak.trans hrest)
theorem Ζiu
    (H : Family α) (V : Edge α) (z x y : α) :
    (((Ζbs H V z x y).card : ℚ) +
      ((Ζav H V z x y).card : ℚ)) *
        min (Ζg (Ζk H V z x).card)
          (Ζg (Ζk H V z y).card) ≤
      Ζeq H V z x y := by
  let dx := (Ζk H V z x).card
  let dy := (Ζk H V z y).card
  let m := min (Ζg dx) (Ζg dy)
  have hleft : ((Ζbs H V z x y).card : ℚ) * m ≤
      ∑ u ∈ (Ζk H V z y).erase x,
        (Ζg dx -
          Ζg (Ζm H V z x u).card) := by
    exact Ζqp _ dx
      (fun u => (Ζm H V z x u).card)
      (by
        intro u hu
        exact Finset.card_le_card
          (Ζbc H V z x u))
      m (min_le_left _ _)
  have hright : ((Ζav H V z x y).card : ℚ) * m ≤
      ∑ v ∈ (Ζk H V z x).erase y,
        (Ζg dy -
          Ζg (Ζm H V z y v).card) := by
    exact Ζqp _ dy
      (fun v => (Ζm H V z y v).card)
      (by
        intro v hv
        exact Finset.card_le_card
          (Ζbc H V z y v))
      m (min_le_right _ _)
  change _ ≤ _ + _
  nlinarith [hleft, hright]
theorem Ζfc
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y)
    (hweak : 2 ≤ (Ζbs H V z x y).card +
      (Ζav H V z x y).card) :
    Ζo H V z x y ≤ 0 := by
  let m := min (Ζg (Ζk H V z x).card)
    (Ζg (Ζk H V z y).card)
  have hm : 0 ≤ m :=
    le_min (Ζek _) (Ζek _)
  have hcount : (2 : ℚ) ≤
      ((Ζbs H V z x y).card : ℚ) +
        ((Ζav H V z x y).card : ℚ) := by
    exact_mod_cast hweak
  have hdef := Ζiu H V z x y
  have hbase := Ζfr
    (Ζk H V z x).card (Ζk H V z y).card
  have hEq := Ζdr H V hxy hxyNe
  have hmul := mul_le_mul_of_nonneg_right hcount hm
  dsimp [m] at hm hmul
  nlinarith
theorem Ζkh
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y)
    (hpositive : 0 < Ζo H V z x y) :
    (Ζbs H V z x y).card +
      (Ζav H V z x y).card ≤ 1 := by
  by_contra h
  have htwo : 2 ≤ (Ζbs H V z x y).card +
      (Ζav H V z x y).card := by omega
  have hnonpos := Ζfc
    H V hxy hxyNe htwo
  linarith
theorem Ζki
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y)
    (hweak : 1 ≤ (Ζbs H V z x y).card +
      (Ζav H V z x y).card) :
    Ζo H V z x y < 1 := by
  let m := min (Ζg (Ζk H V z x).card)
    (Ζg (Ζk H V z y).card)
  have hm : 0 ≤ m :=
    le_min (Ζek _) (Ζek _)
  have hcount : (1 : ℚ) ≤
      ((Ζbs H V z x y).card : ℚ) +
        ((Ζav H V z x y).card : ℚ) := by
    exact_mod_cast hweak
  have hdef := Ζiu H V z x y
  have hbase := Ζfr
    (Ζk H V z x).card (Ζk H V z y).card
  have hEq := Ζdr H V hxy hxyNe
  have hmul := mul_le_mul_of_nonneg_right hcount hm
  have hmlt : m < 1 :=
    lt_of_le_of_lt (min_le_left _ _)
      (Ζqo (Ζk H V z x).card)
  dsimp [m] at hm hmul hmlt
  nlinarith
theorem Ζat
    (H : Family α) (V : Edge α) {z v x y : α}
    (hxy : ({x, y} : Edge α) ∈ Ζe H V z v) :
    ({x, y} : Edge α) ∈ Ζaf H V z := by
  obtain ⟨hxyV, hdis, hxz, _⟩ := Finset.mem_filter.mp hxy
  have hzNot : z ∉ ({x, y} : Edge α) := by
    intro hz
    exact (Finset.disjoint_left.mp hdis) hz (by simp)
  exact Finset.mem_filter.mpr ⟨hxyV, hzNot, hxz⟩
theorem Ζdj
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxyLink : ({x, y} : Edge α) ∈ Ζe H V z v)
    (hxuLink : ({x, u} : Edge α) ∈ Ζe H V z v) :
    u ∈ Ζav H V z x y := by
  have hxuRoot := Ζat H V hxuLink
  have huNeighbor :=
    (Ζeh H V hxuRoot hxu).1
  have hmu := Ζjg
    hH hzV hvV hzv hxy hxu hyu hxyLink hxuLink
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_erase.mpr ⟨Ne.symm hyu, huNeighbor⟩
  · omega
end RootedSignedWeights
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section ReceiverExclusion
variable {α : Type*} [DecidableEq α]
private theorem Ζhc
    {p : Edge α} {a b : α}
    (hp : p.card = 2) (ha : a ∈ p) (hb : b ∈ p)
    (hab : a ≠ b) : p = {a, b} := by
  have hsub : ({a, b} : Edge α) ⊆ p := by
    intro t ht
    rcases Finset.mem_insert.mp ht with hta | htb
    · exact hta ▸ ha
    · exact (Finset.mem_singleton.mp htb) ▸ hb
  have hcard : p.card ≤ ({a, b} : Edge α).card := by
    rw [hp, Finset.card_pair hab]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
private theorem Ζus
    {p : Edge α} {x y : α}
    (hp : p.card = 2) (hxy : x ≠ y)
    (hne : p ≠ ({x, y} : Edge α))
    (hmeets : ¬ Disjoint p ({x, y} : Edge α)) :
    (∃ u : α, x ≠ u ∧ y ≠ u ∧ p = {x, u}) ∨
      (∃ u : α, y ≠ u ∧ x ≠ u ∧ p = {y, u}) := by
  have hxyMem : x ∈ p ∨ y ∈ p := by
    by_contra h
    have hx : x ∉ p := fun hpx => h (Or.inl hpx)
    have hy : y ∉ p := fun hpy => h (Or.inr hpy)
    apply hmeets
    apply Finset.disjoint_left.mpr
    intro t ht hpSource
    rcases Finset.mem_insert.mp hpSource with htx | hty
    · exact hx (htx ▸ ht)
    · exact hy ((Finset.mem_singleton.mp hty) ▸ ht)
  rcases hxyMem with hx | hy
  · have hyNot : y ∉ p := by
      intro hyMem
      exact hne (Ζhc hp hx hyMem hxy)
    have hmore : (p.erase x).Nonempty := by
      apply Finset.card_pos.mp
      have hErase := Finset.card_erase_add_one hx
      omega
    obtain ⟨u, huErase⟩ := hmore
    have hux : u ≠ x := (Finset.mem_erase.mp huErase).1
    have hu : u ∈ p := (Finset.mem_erase.mp huErase).2
    have hyu : y ≠ u := by
      intro h
      exact hyNot (h ▸ hu)
    exact Or.inl ⟨u, Ne.symm hux, hyu,
      Ζhc hp hx hu (Ne.symm hux)⟩
  · have hxNot : x ∉ p := by
      intro hxMem
      exact hne (Ζhc hp hxMem hy hxy)
    have hmore : (p.erase y).Nonempty := by
      apply Finset.card_pos.mp
      have hErase := Finset.card_erase_add_one hy
      omega
    obtain ⟨u, huErase⟩ := hmore
    have huy : u ≠ y := (Finset.mem_erase.mp huErase).1
    have hu : u ∈ p := (Finset.mem_erase.mp huErase).2
    have hxu : x ≠ u := by
      intro h
      exact hxNot (h ▸ hu)
    exact Or.inr ⟨u, Ne.symm huy, hxu,
      Ζhc hp hy hu (Ne.symm huy)⟩
theorem Ζds
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ Ζe H V z v) :
    ((Ζe H V z v).erase ({x, y} : Edge α)) ⊆
      ((Ζav H V z x y).image
        (fun u => ({x, u} : Edge α))) ∪
      ((Ζbs H V z x y).image
        (fun u => ({y, u} : Edge α))) := by
  intro p hp
  have hpLink : p ∈ Ζe H V z v :=
    (Finset.mem_erase.mp hp).2
  have hpNe : p ≠ ({x, y} : Edge α) :=
    (Finset.mem_erase.mp hp).1
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpLink).1).2
  have hmeet := Ζdu hH hzv hpLink hsource
  rcases Ζus hp2 hxy hpNe hmeet with
    ⟨u, hxu, hyu, hpair⟩ | ⟨u, hyu, hxu, hpair⟩
  · have hxuLink : ({x, u} : Edge α) ∈ Ζe H V z v := by
      rw [← hpair]
      exact hpLink
    have huWeak := Ζdj
      hH hzV hvV hzv hxy hxu hyu hsource hxuLink
    apply Finset.mem_union.mpr
    left
    rw [hpair]
    exact Finset.mem_image_of_mem _ huWeak
  · have hyxSource : ({y, x} : Edge α) ∈ Ζe H V z v := by
      simpa only [Finset.pair_comm] using hsource
    have hyuLink : ({y, u} : Edge α) ∈ Ζe H V z v := by
      rw [← hpair]
      exact hpLink
    have huWeak : u ∈ Ζav H V z y x :=
      Ζdj
        hH hzV hvV hzv (Ne.symm hxy) hyu hxu hyxSource hyuLink
    have huWeakLeft : u ∈ Ζbs H V z x y := huWeak
    apply Finset.mem_union.mpr
    right
    rw [hpair]
    exact Finset.mem_image_of_mem _ huWeakLeft
theorem Ζkz
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ Ζe H V z v)
    (hlarge : 3 ≤ (Ζe H V z v).card) :
    2 ≤ (Ζbs H V z x y).card +
      (Ζav H V z x y).card := by
  have hcover := Ζds
    hH hzV hvV hzv hxy hsource
  have hErase := Finset.card_erase_add_one hsource
  have hcard := Finset.card_le_card hcover
  have hUnion := Finset.card_union_le
    ((Ζav H V z x y).image
      (fun u => ({x, u} : Edge α)))
    ((Ζbs H V z x y).image
      (fun u => ({y, u} : Edge α)))
  have hright := Finset.card_image_le
    (s := Ζav H V z x y)
    (f := fun u => ({x, u} : Edge α))
  have hleft := Finset.card_image_le
    (s := Ζbs H V z x y)
    (f := fun u => ({y, u} : Edge α))
  omega
theorem Ζjh
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ Ζe H V z v)
    (hlarge : 3 ≤ (Ζe H V z v).card) :
    Ζo H V z x y ≤ 0 := by
  have htwo := Ζkz
    hH hzV hvV hzv hxy hsource hlarge
  exact Ζfc H V
    (Ζat H V hsource) hxy htwo
theorem Ζfd
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ Ζe H V z v)
    (hdouble : (Ζe H V z v).card = 2) :
    Ζo H V z x y < 1 := by
  have hcover := Ζds
    hH hzV hvV hzv hxy hsource
  have hErase := Finset.card_erase_add_one hsource
  have hnonempty :
      ((Ζe H V z v).erase ({x, y} : Edge α)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hnonempty
  have hcovered := hcover hp
  have hcount : 1 ≤ (Ζbs H V z x y).card +
      (Ζav H V z x y).card := by
    rcases Finset.mem_union.mp hcovered with hright | hleft
    · obtain ⟨u, hu, _⟩ := Finset.mem_image.mp hright
      have hpos := Finset.card_pos.mpr ⟨u, hu⟩
      omega
    · obtain ⟨u, hu, _⟩ := Finset.mem_image.mp hleft
      have hpos := Finset.card_pos.mpr ⟨u, hu⟩
      omega
  exact Ζki H V
    (Ζat H V hsource) hxy hcount
theorem Ζhd
    (H : Family α) (V : Edge α) {z v x y : α}
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hv : v ∈ Ζb H V ({x, y} : Edge α)) :
    ({x, y} : Edge α) ∈ Ζe H V z v := by
  obtain ⟨hxyV, hzOut, hxz⟩ := Finset.mem_filter.mp hsource
  obtain ⟨_, hvOut, hxv⟩ := Finset.mem_filter.mp hv
  have hdis : Disjoint ({x, y} : Edge α) ({z, v} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro t ht htv
    rcases Finset.mem_insert.mp htv with htz | htv'
    · exact hzOut (htz ▸ ht)
    · exact hvOut ((Finset.mem_singleton.mp htv') ▸ ht)
  exact Finset.mem_filter.mpr ⟨hxyV, hdis, hxz, hxv⟩
theorem Ζmg
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ Ζb H V ({x, y} : Edge α))
    (hzv : z ≠ v)
    (hpositive : 0 < Ζo H V z x y) :
    (Ζc H V ({z, v} : Edge α)).card ≤ 2 := by
  have hvV : v ∈ V := (Finset.mem_filter.mp hv).1
  have hsourceLink := Ζhd H V hsource hv
  have hcardEq :
      (Ζc H V ({z, v} : Edge α)).card =
      (Ζe H V z v).card := by
    congr 1
    ext p
    exact Ζr H V hzv p
  by_contra h
  have hlarge : 3 ≤ (Ζe H V z v).card := by omega
  have hnonpos := Ζjh
    hH hzV hvV hzv hxy hsourceLink hlarge
  linarith
end ReceiverExclusion
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section LargeLinkCenters
variable {α : Type*} [DecidableEq α]
def Ζpb (H : Family α) (V : Edge α) : Family α :=
  (Ζac H V).filter (fun q => 3 < (Ζc H V q).card)
theorem Ζpy (H : Family α) (V : Edge α) :
    Ζpb H V ⊆ Ζac H V := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1
theorem Ζop (H : Family α) (V : Edge α) :
    Ζpb H V ⊆ V.powersetCard 2 := by
  intro q hq
  exact Ζbr H V (Ζpy H V hq)
theorem Ζpz
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ Ζpb H V) :
    ∃ x ∈ V, x ∉ q ∧
      (∀ p ∈ Ζc H V q, x ∈ p) ∧
      ∀ y : α, (∀ p ∈ Ζc H V q, y ∈ p) → y = x := by
  have hqP : q ∈ V.powersetCard 2 :=
    Ζop H V hq
  have hlarge : 3 < (Ζc H V q).card :=
    (Finset.mem_filter.mp hq).2
  obtain ⟨x, hx, hunique⟩ :=
    Ζgu hH hqP hlarge
  have hpos : 0 < (Ζc H V q).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  obtain ⟨hpP, hcert⟩ := Finset.mem_filter.mp hp
  have hxV : x ∈ V := (Finset.mem_powersetCard.mp hpP).1 (hx p hp)
  obtain ⟨_, _, _, _, _, hdis, _, _⟩ := hcert
  have hxq : x ∉ q := by
    intro hxq
    exact (Finset.disjoint_left.mp hdis) (hx p hp) hxq
  exact ⟨x, hxV, hxq, hx, hunique⟩
end LargeLinkCenters
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section RootCommonLinkFibers
variable {α : Type*} [DecidableEq α]
theorem Ζaq
    (H : Family α) (V : Edge α)
    {z x u : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u) :
    Ζm H V z x u =
      Ζcu H V ({x, u} : Edge α) z := by
  apply Finset.Subset.antisymm
  · exact Ζfz H V
      hzV hzx hzu hxu
  · intro t ht
    obtain ⟨htV, hztLink⟩ := Finset.mem_filter.mp ht
    have hztOrient : ({z, t} : Edge α) ∈ Ζe H V x u :=
      (Ζr H V hxu _).mp hztLink
    obtain ⟨_, hdis, hzxEdge, hzuEdge⟩ :=
      Finset.mem_filter.mp hztOrient
    have htz : t ≠ z := by
      intro h
      have hcard : ({z, t} : Edge α).card = 2 :=
        (Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp hztOrient).1).2
      simp [h] at hcard
    have htx : t ≠ x := by
      intro h
      subst t
      have hxL : x ∈ ({z, x} : Edge α) := by simp
      have hxR : x ∈ ({x, u} : Edge α) := by simp
      exact (Finset.disjoint_left.mp hdis) hxL hxR
    have htu : t ≠ u := by
      intro h
      subst t
      have huL : u ∈ ({z, u} : Edge α) := by simp
      have huR : u ∈ ({x, u} : Edge α) := by simp
      exact (Finset.disjoint_left.mp hdis) huL huR
    have hxTriple : ({x, t} : Edge α) ∪ {z} ∈ H := by
      have heq : ({x, t} : Edge α) ∪ {z} =
          ({z, t} : Edge α) ∪ {x} := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq.symm ▸ hzxEdge
    have huTriple : ({u, t} : Edge α) ∪ {z} ∈ H := by
      have heq : ({u, t} : Edge α) ∪ {z} =
          ({z, t} : Edge α) ∪ {u} := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq.symm ▸ hzuEdge
    exact Finset.mem_filter.mpr ⟨htV, htz, htx, htu, hxTriple, huTriple⟩
private theorem Ζgo
    (H : Family α) (V q : Edge α) (z : α)
    {t : α} (ht : t ∈ Ζcu H V q z) : t ≠ z := by
  intro h
  have hzt : ({z, t} : Edge α) ∈ Ζc H V q :=
    (Finset.mem_filter.mp ht).2
  have hcard : ({z, t} : Edge α).card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hzt).1).2
  simp [h] at hcard
theorem Ζpc
    (H : Family α) (V q : Edge α) (z : α)
    (hcenter : ∀ p ∈ Ζc H V q, z ∈ p) :
    (Ζcu H V q z).card = (Ζc H V q).card := by
  apply Finset.card_bij (fun t _ => ({z, t} : Edge α))
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro t ht u hu heq
    have htz := Ζgo H V q z ht
    have huz := Ζgo H V q z hu
    have htMem : t ∈ ({z, t} : Edge α) := by simp
    have htOther : t ∈ ({z, u} : Edge α) := heq ▸ htMem
    rcases Finset.mem_insert.mp htOther with htz' | htu
    · exact False.elim (htz htz')
    · exact Finset.mem_singleton.mp htu
  · intro p hp
    have hp2 : p.card = 2 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
    have hz : z ∈ p := hcenter p hp
    have hmore : (p.erase z).Nonempty := by
      apply Finset.card_pos.mp
      have hErase := Finset.card_erase_add_one hz
      omega
    obtain ⟨t, htErase⟩ := hmore
    have htz : t ≠ z := (Finset.mem_erase.mp htErase).1
    have ht : t ∈ p := (Finset.mem_erase.mp htErase).2
    have heq : ({z, t} : Edge α) = p := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwz | hwt
        · exact hwz ▸ hz
        · exact (Finset.mem_singleton.mp hwt) ▸ ht
      · rw [Finset.card_pair (Ne.symm htz), hp2]
    have htV : t ∈ V :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).1 ht
    refine ⟨t, Finset.mem_filter.mpr ⟨htV, ?_⟩, heq⟩
    exact heq.symm ▸ hp
theorem Ζcv
    (H : Family α) (V q : Edge α) (z : α) :
    (Ζcu H V q z).card ≤ (Ζc H V q).card := by
  apply Finset.card_le_card_of_injOn
    (fun t => ({z, t} : Edge α))
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro t ht u hu heq
    have htz := Ζgo H V q z ht
    have htMem : t ∈ ({z, t} : Edge α) := by simp
    change ({z, t} : Edge α) = ({z, u} : Edge α) at heq
    have htOther : t ∈ ({z, u} : Edge α) := heq ▸ htMem
    rcases Finset.mem_insert.mp htOther with htz' | htu
    · exact False.elim (htz htz')
    · exact Finset.mem_singleton.mp htu
theorem Ζhy
    (H : Family α) (V : Edge α)
    {z x u : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u)
    (hcenter : ∀ p ∈ Ζc H V ({x, u} : Edge α), z ∈ p) :
    (Ζm H V z x u).card =
      (Ζc H V ({x, u} : Edge α)).card := by
  rw [Ζaq H V hzV hzx hzu hxu]
  exact Ζpc H V _ z hcenter
theorem Ζkq
    (H : Family α) (V : Edge α)
    {z x u : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u) :
    (Ζm H V z x u).card ≤
      (Ζc H V ({x, u} : Edge α)).card := by
  rw [Ζaq H V hzV hzx hzu hxu]
  exact Ζcv H V _ z
theorem Ζjv
    (H : Family α) (V : Edge α)
    {z x u c : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u)
    (hzc : z ≠ c)
    (hcenter : ∀ p ∈ Ζc H V ({x, u} : Edge α), c ∈ p) :
    (Ζm H V z x u).card ≤ 1 := by
  have hsub : Ζcu H V ({x, u} : Edge α) z ⊆ ({c} : Edge α) := by
    intro t ht
    have hzt : ({z, t} : Edge α) ∈ Ζc H V ({x, u} : Edge α) :=
      (Finset.mem_filter.mp ht).2
    have hc : c ∈ ({z, t} : Edge α) := hcenter _ hzt
    rcases Finset.mem_insert.mp hc with hcz | hct
    · exact False.elim (hzc hcz.symm)
    · exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp hct).symm
  rw [Ζaq H V hzV hzx hzu hxu]
  exact (Finset.card_le_card hsub).trans (by simp)
theorem Ζoh
    {H : Family α} {V : Edge α} {x u : α}
    (hH : Admissible H)
    (hxV : x ∈ V) (huV : u ∈ V) (hxu : x ≠ u) :
    (∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
      Ζbb (Ζm H V z x u).card) =
      Ζbb (Ζc H V ({x, u} : Edge α)).card := by
  let q : Edge α := {x, u}
  have hqV : q ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htx | htu
      · exact htx ▸ hxV
      · exact (Finset.mem_singleton.mp htu) ▸ huV
    · exact Finset.card_pair hxu
  by_cases hlarge : 3 < (Ζc H V q).card
  · have hqUsed : q ∈ Ζac H V :=
      (Ζas H V q).mpr
        ⟨hqV, Finset.card_pos.mp (by omega)⟩
    have hqLarge : q ∈ Ζpb H V :=
      Finset.mem_filter.mpr ⟨hqUsed, hlarge⟩
    obtain ⟨c, hcV, hcNot, hcenter, _⟩ :=
      Ζpz hH hqLarge
    have hcx : c ≠ x := by
      intro h
      exact hcNot (by simp [q, h])
    have hcu : c ≠ u := by
      intro h
      exact hcNot (by simp [q, h])
    have hcFiltered : c ∈ V.filter (fun z => z ≠ x ∧ z ≠ u) :=
      Finset.mem_filter.mpr ⟨hcV, hcx, hcu⟩
    have hsingle :
        (∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
          Ζbb (Ζm H V z x u).card) =
        Ζbb (Ζm H V c x u).card := by
      apply Finset.sum_eq_single_of_mem c hcFiltered
      intro z hz hzc
      obtain ⟨hzV, hzx, hzu⟩ := Finset.mem_filter.mp hz
      have hsmall := Ζjv
        H V hzV hzx hzu hxu hzc hcenter
      simp [Ζbb, show ¬ 3 < (Ζm H V z x u).card by omega]
    rw [hsingle, Ζhy
      H V hcV hcx hcu hxu hcenter]
  · have hzero : Ζbb (Ζc H V q).card = 0 := by
      simp [Ζbb, hlarge]
    rw [hzero]
    apply Finset.sum_eq_zero
    intro z hz
    obtain ⟨hzV, hzx, hzu⟩ := Finset.mem_filter.mp hz
    have hbound := Ζkq
      H V hzV hzx hzu hxu
    dsimp [q] at hlarge
    have hsmall : ¬ 3 < (Ζm H V z x u).card := by
      omega
    simp [Ζbb, hsmall]
end RootCommonLinkFibers
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section ChargeTransfer
variable {α : Type*} [DecidableEq α]
def Ζq
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  max (Ζo H V z x y) 0
def Ζao
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  Ζq H V z x y /
    (((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1)
theorem Ζv
    (H : Family α) (V : Edge α) {z x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z) :
    z ∈ Ζb H V ({x, y} : Edge α) := by
  obtain ⟨_, hzOut, hxz⟩ := Finset.mem_filter.mp hsource
  exact Finset.mem_filter.mpr ⟨hzV, hzOut, hxz⟩
theorem Ζth
    (H : Family α) (V : Edge α) {z x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hdegree : 2 ≤
      (Ζb H V ({x, y} : Edge α)).card) :
    (∑ _v ∈ (Ζb H V ({x, y} : Edge α)).erase z,
      Ζao H V z x y) =
      Ζq H V z x y := by
  let N := Ζb H V ({x, y} : Edge α)
  have hzN : z ∈ N := Ζv H V hzV hsource
  have hCardNat := Finset.card_erase_add_one hzN
  have hCardQ : ((N.erase z).card : ℚ) = (N.card : ℚ) - 1 := by
    have hCast : ((N.erase z).card : ℚ) + 1 = (N.card : ℚ) := by
      exact_mod_cast hCardNat
    linarith
  have hDen : (N.card : ℚ) - 1 ≠ 0 := by
    have hCast : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  change (∑ _v ∈ N.erase z,
    Ζq H V z x y / ((N.card : ℚ) - 1)) = _
  rw [Finset.sum_const, nsmul_eq_mul, hCardQ]
  field_simp
theorem Ζoq
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hpositive : 0 < Ζq H V z x y) :
    (Ζc H V ({z, v} : Edge α)).card ≤ 2 := by
  have hvComp : v ∈ Ζb H V ({x, y} : Edge α) :=
    (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hwPos : 0 < Ζo H V z x y := by
    simpa [Ζq] using hpositive
  exact Ζmg
    hH hzV hsource hxy hvComp hzv hwPos
theorem Ζrg
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hdouble : (Ζc H V ({z, v} : Edge α)).card = 2) :
    Ζao H V z x y < 1 := by
  let N := Ζb H V ({x, y} : Edge α)
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hvV : v ∈ V := (Finset.mem_filter.mp hvN).1
  have hzN : z ∈ N := Ζv H V hzV hsource
  have hpair : ({z, v} : Edge α) ⊆ N := by
    intro t ht
    rcases Finset.mem_insert.mp ht with htz | htv
    · exact htz ▸ hzN
    · exact (Finset.mem_singleton.mp htv) ▸ hvN
  have hdegree : 2 ≤ N.card := by
    have hbound := Finset.card_le_card hpair
    rw [Finset.card_pair hzv] at hbound
    exact hbound
  have hden : (1 : ℚ) ≤ (N.card : ℚ) - 1 := by
    have hcast : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  have hsourceLink := Ζhd H V hsource hvN
  have hdoubleOrient : (Ζe H V z v).card = 2 := by
    have heq : Ζc H V ({z, v} : Edge α) =
        Ζe H V z v := by
      ext p
      exact Ζr H V hzv p
    rw [← heq]
    exact hdouble
  have hweight := Ζfd
    hH hzV hvV hzv hxy hsourceLink hdoubleOrient
  have hpositive : Ζq H V z x y < 1 := by
    by_cases hw : Ζo H V z x y ≤ 0
    · simp [Ζq, max_eq_right hw]
    · have hwNonneg : 0 ≤ Ζo H V z x y :=
        le_of_lt (lt_of_not_ge hw)
      simpa [Ζq, max_eq_left hwNonneg] using hweight
  have hpNonneg : 0 ≤ Ζq H V z x y := by
    unfold Ζq
    exact le_max_right _ _
  have hchargeLe : Ζao H V z x y ≤
      Ζq H V z x y := by
    unfold Ζao
    change Ζq H V z x y / ((N.card : ℚ) - 1) ≤ _
    apply (div_le_iff₀ (by linarith : 0 < (N.card : ℚ) - 1)).mpr
    nlinarith [mul_nonneg hpNonneg (by linarith : 0 ≤ (N.card : ℚ) - 2)]
  exact lt_of_le_of_lt hchargeLe hpositive
end ChargeTransfer
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section RootedWeightSum
variable {α : Type*} [DecidableEq α]
private theorem Ζpw
    (U : Finset α) (N : α → Finset α)
    (hN : ∀ x ∈ U, N x ⊆ U)
    (hSym : ∀ x ∈ U, ∀ y ∈ U, y ∈ N x ↔ x ∈ N y)
    (g : α → α → ℚ) :
    (∑ x ∈ U, ∑ y ∈ N x, g x y) =
      ∑ x ∈ U, ∑ y ∈ N x, g y x := by
  have hExpand (f : α → α → ℚ) :
      (∑ x ∈ U, ∑ y ∈ N x, f x y) =
        ∑ x ∈ U, ∑ y ∈ U,
          if y ∈ N x then f x y else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hFilter : U.filter (fun y => y ∈ N x) = N x := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨hN x hx h, h⟩
    calc
      (∑ y ∈ N x, f x y) =
          ∑ y ∈ U.filter (fun y => y ∈ N x), f x y := by rw [hFilter]
      _ = ∑ y ∈ U, if y ∈ N x then f x y else 0 := by
        simp only [Finset.sum_filter]
  rw [hExpand g, hExpand (fun x y => g y x)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [(hSym x hx y hy)]
private theorem Ζvs
    (U : Finset α) (N : α → Finset α)
    (hN : ∀ x ∈ U, N x ⊆ U)
    (hSym : ∀ x ∈ U, ∀ y ∈ U, y ∈ N x ↔ x ∈ N y) :
    (∑ x ∈ U, ∑ y ∈ N x,
      ∑ u ∈ (N y).erase x,
        Ζg (N x ∩ N u).card) =
      ∑ x ∈ U, ∑ u ∈ U.erase x,
        Ζbb (N x ∩ N u).card := by
  apply Finset.sum_congr rfl
  intro x hx
  have hInner (y : α) (hy : y ∈ N x) :
      (∑ u ∈ (N y).erase x,
        Ζg (N x ∩ N u).card) =
        ∑ u ∈ U.erase x,
          if u ∈ N y then Ζg (N x ∩ N u).card else 0 := by
    have hyU : y ∈ U := hN x hx hy
    have hFilter : (U.erase x).filter (fun u => u ∈ N y) =
        (N y).erase x := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hux, _⟩, huN⟩
        exact ⟨hux, huN⟩
      · rintro ⟨hux, huN⟩
        exact ⟨⟨hux, hN y hyU huN⟩, huN⟩
    calc
      (∑ u ∈ (N y).erase x,
          Ζg (N x ∩ N u).card) =
          ∑ u ∈ (U.erase x).filter (fun u => u ∈ N y),
            Ζg (N x ∩ N u).card := by rw [hFilter]
      _ = ∑ u ∈ U.erase x,
            if u ∈ N y then Ζg (N x ∩ N u).card else 0 := by
          simp only [Finset.sum_filter]
  calc
    (∑ y ∈ N x,
      ∑ u ∈ (N y).erase x,
        Ζg (N x ∩ N u).card) =
        ∑ y ∈ N x, ∑ u ∈ U.erase x,
          if u ∈ N y then Ζg (N x ∩ N u).card else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hInner y hy
    _ = ∑ u ∈ U.erase x, ∑ y ∈ N x,
          if u ∈ N y then Ζg (N x ∩ N u).card else 0 :=
      Finset.sum_comm
    _ = ∑ u ∈ U.erase x,
          Ζbb (N x ∩ N u).card := by
      apply Finset.sum_congr rfl
      intro u hu
      have huU : u ∈ U := (Finset.mem_erase.mp hu).2
      have hSymInner :
          (∑ y ∈ N x,
            if u ∈ N y then Ζg (N x ∩ N u).card else 0) =
          ∑ y ∈ N x,
            if y ∈ N u then Ζg (N x ∩ N u).card else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyU : y ∈ U := hN x hx hy
        simp only [(hSym y hyU u huU)]
      rw [hSymInner]
      have hFilter : (N x).filter (fun y => y ∈ N u) = N x ∩ N u := by
        ext y
        simp
      calc
        (∑ y ∈ N x,
            if y ∈ N u then Ζg (N x ∩ N u).card else 0) =
            ∑ y ∈ N x ∩ N u,
              Ζg (N x ∩ N u).card := by
          rw [← hFilter]
          simp only [Finset.sum_filter]
        _ = Ζbb (N x ∩ N u).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact Ζmu _
def Ζcw
    (H : Family α) (V : Edge α) (z : α) : ℚ :=
  ∑ x ∈ V.erase z,
    ∑ y ∈ Ζk H V z x,
      Ζo H V z x y
theorem Ζtu
    (H : Family α) (V : Edge α) (z : α) :
    Ζcw H V z =
      2 * (∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
        Ζbb (Ζm H V z x u).card) -
      2 * (∑ x ∈ V.erase z,
        Ζcm (Ζk H V z x).card) := by
  let U := V.erase z
  let N : α → Edge α := fun x => Ζk H V z x
  have hN : ∀ x ∈ U, N x ⊆ U := by
    intro x hx y hy
    apply Finset.mem_erase.mpr
    constructor
    · intro hyz
      subst y
      exact Ζvc H V z x hy
    · exact Ζhx H V z x hy
  have hSym : ∀ x ∈ U, ∀ y ∈ U, y ∈ N x ↔ x ∈ N y := by
    intro x hx y hy
    constructor
    · exact Ζpv H V
        (Finset.mem_erase.mp hx).2
        (Ne.symm (Finset.mem_erase.mp hx).1)
    · exact Ζpv H V
        (Finset.mem_erase.mp hy).2
        (Ne.symm (Finset.mem_erase.mp hy).1)
  let A : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    ∑ u ∈ (N y).erase x,
      Ζg (Ζm H V z x u).card
  let B : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    ∑ u ∈ (N x).erase y,
      Ζg (Ζm H V z y u).card
  let C : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    Ζal (N x).card
  let D : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    Ζal (N y).card
  have hB : B = A := by
    exact Ζpw U N hN hSym
      (fun x y => ∑ u ∈ (N x).erase y,
        Ζg (Ζm H V z y u).card)
  have hD : D = C := by
    exact Ζpw U N hN hSym
      (fun x y => Ζal (N y).card)
  have hC : C = ∑ x ∈ U, Ζcm (N x).card := by
    dsimp [C]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_const, nsmul_eq_mul]
    exact Ζgs _
  have hA : A = ∑ x ∈ U, ∑ u ∈ U.erase x,
      Ζbb (Ζm H V z x u).card := by
    have hWedge := Ζvs U N hN hSym
    dsimp [A, N] at hWedge ⊢
    calc
      (∑ x ∈ U, ∑ y ∈ Ζk H V z x,
        ∑ u ∈ (Ζk H V z y).erase x,
          Ζg (Ζm H V z x u).card) =
          ∑ x ∈ U, ∑ y ∈ Ζk H V z x,
            ∑ u ∈ (Ζk H V z y).erase x,
              Ζg
                (Ζk H V z x ∩ Ζk H V z u).card := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          apply Finset.sum_congr rfl
          intro u hu
          rw [Ζge]
      _ = ∑ x ∈ U, ∑ u ∈ U.erase x,
            Ζbb
              (Ζk H V z x ∩ Ζk H V z u).card :=
          hWedge
      _ = ∑ x ∈ U, ∑ u ∈ U.erase x,
            Ζbb (Ζm H V z x u).card := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro u hu
          rw [Ζge]
  have hExpand : Ζcw H V z = A + B - C - D := by
    simp only [Ζcw, Ζo,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    dsimp [A, B, C, D, U, N]
  rw [hExpand, hB, hD, hC, hA]
  ring
private theorem Ζut
    (V : Finset α) (f : α → α → α → ℚ) :
    (∑ z ∈ V, ∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
      f z x u) =
      ∑ x ∈ V, ∑ u ∈ V.erase x,
        ∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
          f z x u := by
  calc
    (∑ z ∈ V, ∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
        f z x u) =
        ∑ x ∈ V, ∑ z ∈ V.erase x, ∑ u ∈ (V.erase z).erase x,
          f z x u := by
      apply Finset.sum_comm'
      intro z x
      constructor
      · rintro ⟨hz, hx⟩
        have h := Finset.mem_erase.mp hx
        exact ⟨Finset.mem_erase.mpr ⟨Ne.symm h.1, hz⟩, h.2⟩
      · rintro ⟨hz, hx⟩
        have h := Finset.mem_erase.mp hz
        exact ⟨h.2, Finset.mem_erase.mpr ⟨Ne.symm h.1, hx⟩⟩
    _ = ∑ x ∈ V, ∑ u ∈ V.erase x,
          ∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
            f z x u := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_comm'
      intro z u
      constructor
      · rintro ⟨hz, hu⟩
        obtain ⟨hzNeX, hzV⟩ := Finset.mem_erase.mp hz
        obtain ⟨huNeX, huEraseZ⟩ := Finset.mem_erase.mp hu
        obtain ⟨huNeZ, huV⟩ := Finset.mem_erase.mp huEraseZ
        exact ⟨Finset.mem_filter.mpr
          ⟨hzV, hzNeX, Ne.symm huNeZ⟩,
          Finset.mem_erase.mpr ⟨huNeX, huV⟩⟩
      · rintro ⟨hz, hu⟩
        obtain ⟨hzV, hzNeX, hzNeU⟩ := Finset.mem_filter.mp hz
        obtain ⟨huNeX, huV⟩ := Finset.mem_erase.mp hu
        exact ⟨Finset.mem_erase.mpr ⟨hzNeX, hzV⟩,
          Finset.mem_erase.mpr
            ⟨huNeX, Finset.mem_erase.mpr ⟨Ne.symm hzNeU, huV⟩⟩⟩
theorem Ζem
    (V : Edge α) (F : Edge α → ℚ) :
    (∑ x ∈ V, ∑ u ∈ V.erase x, F ({x, u} : Edge α)) =
      2 * (∑ p ∈ V.powersetCard 2, F p) := by
  let P := V.powersetCard 2
  have hInner (x : α) (hx : x ∈ V) :
      (∑ u ∈ V.erase x, F ({x, u} : Edge α)) =
        ∑ p ∈ P.filter (fun p => x ∈ p), F p := by
    apply Finset.sum_bij (fun u _ => ({x, u} : Edge α))
    · intro u hu
      obtain ⟨hux, huV⟩ := Finset.mem_erase.mp hu
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro t ht
          rcases Finset.mem_insert.mp ht with htx | htu
          · exact htx ▸ hx
          · exact (Finset.mem_singleton.mp htu) ▸ huV
        · exact Finset.card_pair (Ne.symm hux)
      · simp
    · intro u hu v hv heq
      have hux : u ≠ x := (Finset.mem_erase.mp hu).1
      have huMem : u ∈ ({x, u} : Edge α) := by simp
      have huOther : u ∈ ({x, v} : Edge α) := heq ▸ huMem
      rcases Finset.mem_insert.mp huOther with hux' | huv
      · exact False.elim (hux hux')
      · exact Finset.mem_singleton.mp huv
    · intro p hp
      obtain ⟨hpP, hxP⟩ := Finset.mem_filter.mp hp
      have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpP).2
      have hmore : (p.erase x).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one hxP
        omega
      obtain ⟨u, huErase⟩ := hmore
      have hux : u ≠ x := (Finset.mem_erase.mp huErase).1
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpP).1 huP
      have heq : ({x, u} : Edge α) = p := by
        apply Finset.eq_of_subset_of_card_le
        · intro t ht
          rcases Finset.mem_insert.mp ht with htx | htu
          · exact htx ▸ hxP
          · exact (Finset.mem_singleton.mp htu) ▸ huP
        · rw [Finset.card_pair (Ne.symm hux), hp2]
      exact ⟨u, Finset.mem_erase.mpr ⟨hux, huV⟩, heq⟩
    · intro u hu
      rfl
  calc
    (∑ x ∈ V, ∑ u ∈ V.erase x, F ({x, u} : Edge α)) =
        ∑ x ∈ V, ∑ p ∈ P.filter (fun p => x ∈ p), F p := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hInner x hx
    _ = ∑ p ∈ P, ∑ x ∈ p, F p := by
      apply Finset.sum_comm'
      intro x p
      constructor
      · rintro ⟨hxV, hp⟩
        exact ⟨(Finset.mem_filter.mp hp).2,
          (Finset.mem_filter.mp hp).1⟩
      · rintro ⟨hxP, hpP⟩
        have hxV : x ∈ V := (Finset.mem_powersetCard.mp hpP).1 hxP
        exact ⟨hxV, Finset.mem_filter.mpr ⟨hpP, hxP⟩⟩
    _ = 2 * (∑ p ∈ P, F p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_const, nsmul_eq_mul]
      have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
      rw [hp2]
      norm_num
theorem Ζsv
    {H : Family α} (V : Edge α) (hH : Admissible H) :
    (∑ z ∈ V, Ζcw H V z) =
      2 * (∑ x ∈ V, ∑ u ∈ V.erase x,
        Ζbb (Ζc H V ({x, u} : Edge α)).card) -
      2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
        Ζcm (Ζk H V z x).card) := by
  have hSum := Ζut V
    (fun z x u => Ζbb (Ζm H V z x u).card)
  calc
    (∑ z ∈ V, Ζcw H V z) =
        ∑ z ∈ V,
          (2 * (∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
            Ζbb (Ζm H V z x u).card) -
           2 * (∑ x ∈ V.erase z,
             Ζcm (Ζk H V z x).card)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact Ζtu H V z
    _ = 2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            ∑ u ∈ (V.erase z).erase x,
              Ζbb (Ζm H V z x u).card) -
          2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            Ζcm (Ζk H V z x).card) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ x ∈ V, ∑ u ∈ V.erase x,
            ∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
              Ζbb (Ζm H V z x u).card) -
          2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            Ζcm (Ζk H V z x).card) := by rw [hSum]
    _ = 2 * (∑ x ∈ V, ∑ u ∈ V.erase x,
            Ζbb (Ζc H V ({x, u} : Edge α)).card) -
          2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            Ζcm (Ζk H V z x).card) := by
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro u hu
      have huV : u ∈ V := (Finset.mem_erase.mp hu).2
      have hxu : x ≠ u := Ne.symm (Finset.mem_erase.mp hu).1
      exact Ζoh hH hx huV hxu
private theorem Ζll
    (H : Family α) (V : Edge α) :
    (∑ q ∈ V.powersetCard 2,
      Ζbb (Ζc H V q).card) =
      Ζgb H V := by
  unfold Ζgb
  symm
  apply Finset.sum_subset (Ζbr H V)
  intro q hq hnot
  have hEmpty : Ζc H V q = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hnot ((Ζas H V q).mpr
      ⟨hq, hn⟩)
  simp [hEmpty, Ζbb]
theorem Ζid
    (H : Family α) (V : Edge α) :
    (∑ p ∈ V.powersetCard 2,
      Ζcm (Ζb H V p).card) =
      Ζdx H V := by
  unfold Ζdx
  symm
  apply Finset.sum_subset (Ζhj H V)
  intro p hp hnot
  have hEmpty : Ζb H V p = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    obtain ⟨_, _, hxEdge⟩ := Finset.mem_filter.mp hx
    have hUsed : p ∈ Ζbp H V := by
      apply Finset.mem_filter.mpr
      exact ⟨hp, ⟨p ∪ {x}, hxEdge, Finset.subset_union_left⟩⟩
    exact hnot hUsed
  simp [hEmpty, Ζcm]
theorem Ζkj
    {H : Family α} (V : Edge α) (hH : Admissible H) :
    (∑ z ∈ V, Ζcw H V z) =
      4 * Ζgb H V - 4 * Ζdx H V := by
  have hGlobal := Ζsv V hH
  have hLinkPairs := Ζem V
    (fun q => Ζbb (Ζc H V q).card)
  have hBudgetPairs := Ζem V
    (fun p => Ζcm (Ζb H V p).card)
  have hL := Ζll H V
  have hB := Ζid H V
  simp only [Ζk] at hGlobal
  rw [hLinkPairs, hBudgetPairs, hL, hB] at hGlobal
  nlinarith
end RootedWeightSum
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section LocalPaymentLedger
variable {α : Type*} [DecidableEq α]
theorem Ζlw
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ E ∈ H, ∑ p ∈ E.powersetCard 2,
      Ζal (Ζb H V p).card) =
      Ζdx H V := by
  let P : Family α := V.powersetCard 2
  have hSwap :
      (∑ E ∈ H, ∑ p ∈ E.powersetCard 2,
        Ζal (Ζb H V p).card) =
      ∑ p ∈ P, ∑ E ∈ Ζeg H p,
        Ζal (Ζb H V p).card := by
    apply Finset.sum_comm'
    intro E p
    constructor
    · rintro ⟨hE, hpE⟩
      obtain ⟨hpSub, hpCard⟩ := Finset.mem_powersetCard.mp hpE
      have hpP : p ∈ P :=
        Finset.mem_powersetCard.mpr
          ⟨hpSub.trans (hground E hE), hpCard⟩
      exact ⟨Finset.mem_filter.mpr ⟨hE, hpSub⟩, hpP⟩
    · rintro ⟨hContain, hpP⟩
      obtain ⟨hE, hpSub⟩ := Finset.mem_filter.mp hContain
      have hpCard : p.card = 2 := (Finset.mem_powersetCard.mp hpP).2
      exact ⟨hE, Finset.mem_powersetCard.mpr ⟨hpSub, hpCard⟩⟩
  calc
    (∑ E ∈ H, ∑ p ∈ E.powersetCard 2,
      Ζal (Ζb H V p).card) =
        ∑ p ∈ P, ∑ E ∈ Ζeg H p,
          Ζal (Ζb H V p).card := hSwap
    _ = ∑ p ∈ P,
          Ζcm (Ζb H V p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard := Ζgh
        H V p hUniform hground hp
      rw [← hcard]
      exact Ζgs _
    _ = Ζdx H V :=
      Ζid H V
theorem Ζti
    (H : Family α) (V : Edge α) {z x : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hzx : z ≠ x)
    (f : α → ℚ) :
    (∑ E ∈ Ζeg H ({z, x} : Edge α),
      ∑ y ∈ (E.erase z).erase x, f y) =
      ∑ y ∈ Ζk H V z x, f y := by
  let p : Edge α := {z, x}
  have hp2 : p.card = 2 := Finset.card_pair hzx
  calc
    (∑ E ∈ Ζeg H p,
      ∑ y ∈ (E.erase z).erase x, f y) =
        ∑ y ∈ Ζk H V z x,
          ∑ E ∈ ({p ∪ {y}} : Family α), f y := by
      apply Finset.sum_comm'
      intro E y
      constructor
      · rintro ⟨hContain, hyErase⟩
        obtain ⟨hEH, hpE⟩ := Finset.mem_filter.mp hContain
        obtain ⟨hyNeX, hyEraseZ⟩ := Finset.mem_erase.mp hyErase
        obtain ⟨hyNeZ, hyE⟩ := Finset.mem_erase.mp hyEraseZ
        have hyNotP : y ∉ p := by simp [p, hyNeZ, hyNeX]
        have hEq : p ∪ {y} = E :=
          Ζjw hp2 (hUniform hEH) hpE hyE hyNotP
        have hyNeighbor : y ∈ Ζk H V z x :=
          Finset.mem_filter.mpr
            ⟨hground E hEH hyE, hyNotP, hEq.symm ▸ hEH⟩
        exact ⟨Finset.mem_singleton.mpr hEq.symm, hyNeighbor⟩
      · rintro ⟨hSingle, hyNeighbor⟩
        have hEq : E = p ∪ {y} := Finset.mem_singleton.mp hSingle
        obtain ⟨_, hyNotP, hExt⟩ := Finset.mem_filter.mp hyNeighbor
        have hyNeZ : y ≠ z := by
          intro h
          exact hyNotP (by simp [h])
        have hyNeX : y ≠ x := by
          intro h
          exact hyNotP (by simp [h])
        have hContain : E ∈ Ζeg H p := by
          apply Finset.mem_filter.mpr
          constructor
          · exact hEq.symm ▸ hExt
          · intro t ht
            rw [hEq]
            exact Finset.mem_union.mpr (Or.inl ht)
        have hyErase : y ∈ (E.erase z).erase x := by
          apply Finset.mem_erase.mpr
          refine ⟨hyNeX, Finset.mem_erase.mpr ⟨hyNeZ, ?_⟩⟩
          rw [hEq]
          simp
        exact ⟨hContain, hyErase⟩
    _ = ∑ y ∈ Ζk H V z x, f y := by simp
theorem Ζqq
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (f : α → α → α → ℚ) :
    (∑ E ∈ H, ∑ z ∈ E, ∑ x ∈ E.erase z,
      ∑ y ∈ (E.erase z).erase x, f z x y) =
      ∑ z ∈ V, ∑ x ∈ V.erase z,
        ∑ y ∈ Ζk H V z x, f z x y := by
  have hRootSwap :
      (∑ E ∈ H, ∑ z ∈ E, ∑ x ∈ E.erase z,
        ∑ y ∈ (E.erase z).erase x, f z x y) =
        ∑ z ∈ V, ∑ E ∈ H.filter (fun E => z ∈ E),
          ∑ x ∈ E.erase z,
            ∑ y ∈ (E.erase z).erase x, f z x y := by
    apply Finset.sum_comm'
    intro E z
    constructor
    · rintro ⟨hE, hzE⟩
      exact ⟨Finset.mem_filter.mpr ⟨hE, hzE⟩,
        hground E hE hzE⟩
    · rintro ⟨hzFilter, _⟩
      exact Finset.mem_filter.mp hzFilter
  have hPairSwap (z : α) :
      (∑ E ∈ H.filter (fun E => z ∈ E),
        ∑ x ∈ E.erase z,
          ∑ y ∈ (E.erase z).erase x, f z x y) =
        ∑ x ∈ V.erase z,
          ∑ E ∈ Ζeg H ({z, x} : Edge α),
            ∑ y ∈ (E.erase z).erase x, f z x y := by
    apply Finset.sum_comm'
    intro E x
    constructor
    · rintro ⟨hEFilter, hxErase⟩
      obtain ⟨hE, hzE⟩ := Finset.mem_filter.mp hEFilter
      obtain ⟨hxNeZ, hxE⟩ := Finset.mem_erase.mp hxErase
      have hpair : ({z, x} : Edge α) ⊆ E := by
        intro t ht
        rcases Finset.mem_insert.mp ht with htz | htx
        · exact htz ▸ hzE
        · exact (Finset.mem_singleton.mp htx) ▸ hxE
      exact ⟨Finset.mem_filter.mpr ⟨hE, hpair⟩,
        Finset.mem_erase.mpr ⟨hxNeZ, hground E hE hxE⟩⟩
    · rintro ⟨hContain, hxErase⟩
      obtain ⟨hE, hpair⟩ := Finset.mem_filter.mp hContain
      have hzE : z ∈ E := hpair (by simp)
      have hxE : x ∈ E := hpair (by simp)
      exact ⟨Finset.mem_filter.mpr ⟨hE, hzE⟩,
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxErase).1, hxE⟩⟩
  calc
    (∑ E ∈ H, ∑ z ∈ E, ∑ x ∈ E.erase z,
      ∑ y ∈ (E.erase z).erase x, f z x y) =
        ∑ z ∈ V, ∑ E ∈ H.filter (fun E => z ∈ E),
          ∑ x ∈ E.erase z,
            ∑ y ∈ (E.erase z).erase x, f z x y := hRootSwap
    _ = ∑ z ∈ V, ∑ x ∈ V.erase z,
          ∑ E ∈ Ζeg H ({z, x} : Edge α),
            ∑ y ∈ (E.erase z).erase x, f z x y := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hPairSwap z
    _ = ∑ z ∈ V, ∑ x ∈ V.erase z,
          ∑ y ∈ Ζk H V z x, f z x y := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro x hx
      exact Ζti H V hUniform hground
        (Ne.symm (Finset.mem_erase.mp hx).1) (fun y => f z x y)
def Ζbx
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  max (-Ζo H V z x y) 0
def Ζbv
    (H : Family α) (V : Edge α) : ℚ :=
  ∑ z ∈ V, ∑ x ∈ V.erase z,
    ∑ y ∈ Ζk H V z x,
      Ζq H V z x y
def Ζex
    (H : Family α) (V : Edge α) : ℚ :=
  ∑ z ∈ V, ∑ x ∈ V.erase z,
    ∑ y ∈ Ζk H V z x,
      Ζbx H V z x y
def Ζdv
    (H : Family α) (V E : Edge α) : ℚ :=
  ∑ z ∈ E, ∑ x ∈ E.erase z,
    ∑ y ∈ (E.erase z).erase x,
      Ζbx H V z x y
def Ζax
    (H : Family α) (V E : Edge α) : ℚ :=
  Ζdv H V E / 2 -
    ∑ p ∈ E.powersetCard 2,
      Ζal (Ζb H V p).card
theorem Ζoi
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ E ∈ H, Ζdv H V E) =
      Ζex H V := by
  exact Ζqq H V hUniform hground
    (fun z x y => Ζbx H V z x y)
theorem Ζkr
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ E ∈ H, Ζax H V E) =
      Ζex H V / 2 -
        Ζdx H V := by
  have hNegative := Ζoi
    H V hUniform hground
  have hBudget := Ζlw
    H V hUniform hground
  have hHalf :
      (∑ E ∈ H, Ζdv H V E / 2) =
        (∑ E ∈ H, Ζdv H V E) / 2 := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simp only [Ζax, Finset.sum_sub_distrib]
  rw [hHalf, hNegative, hBudget]
private theorem Ζru (w : ℚ) :
    w = max w 0 - max (-w) 0 := by
  by_cases hw : w ≤ 0
  · rw [max_eq_right hw, max_eq_left (by linarith : 0 ≤ -w)]
    ring
  · have hwNonneg : 0 ≤ w := le_of_lt (lt_of_not_ge hw)
    rw [max_eq_left hwNonneg,
      max_eq_right (by linarith : -w ≤ 0)]
    ring
theorem Ζmv
    (H : Family α) (V : Edge α) :
    (∑ z ∈ V, Ζcw H V z) =
      Ζbv H V -
        Ζex H V := by
  calc
    (∑ z ∈ V, Ζcw H V z) =
        ∑ z ∈ V, ∑ x ∈ V.erase z,
          ∑ y ∈ Ζk H V z x,
            (Ζq H V z x y -
              Ζbx H V z x y) := by
      apply Finset.sum_congr rfl
      intro z hz
      unfold Ζcw
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Ζru _
    _ = Ζbv H V -
          Ζex H V := by
      simp only [Ζbv, Ζex,
        Finset.sum_sub_distrib]
theorem Ζmh
    {H : Family α} (V : Edge α)
    (hH : Admissible H)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    2 * Ζgb H V - Ζdx H V =
      Ζbv H V / 2 -
        ∑ E ∈ H, Ζax H V E := by
  have hSigned := Ζkj V hH
  have hSplit := Ζmv H V
  have hDefect := Ζkr
    H V hUniform hground
  linarith
end LocalPaymentLedger
end JSP523.Rank3
end
section
namespace JSP523.Rank3
def Ζl (n : ℕ) : ℚ := Ζg (n + 1)
def Ζa (n : ℕ) : ℚ := ((n : ℚ) - 1) * Ζl n
theorem Ζdy (n : ℕ) : 0 ≤ Ζl n :=
  Ζek (n + 1)
theorem Ζdl {m n : ℕ} (hmn : m ≤ n) :
    Ζl m ≤ Ζl n :=
  Ζdi (Nat.add_le_add_right hmn 1)
theorem Ζey {m n : ℕ} (hmn : m ≤ n) :
    Ζa m ≤ Ζa n := by
  by_cases hm : m = 0
  · subst m
    have hZero : Ζa 0 = 0 := by
      norm_num [Ζa, Ζl, Ζg]
    rw [hZero]
    by_cases hn : n = 0
    · subst n; norm_num [Ζa, Ζl, Ζg]
    · have hnPos : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hnCast : (1 : ℚ) ≤ n := by exact_mod_cast hnPos
      unfold Ζa
      exact mul_nonneg (by linarith) (Ζdy n)
  · have hmPos : 1 ≤ m := Nat.pos_of_ne_zero hm
    have hmCast : (1 : ℚ) ≤ m := by exact_mod_cast hmPos
    have hCast : (m : ℚ) ≤ n := by exact_mod_cast hmn
    have hPhi : Ζl m ≤ Ζl n := Ζdl hmn
    have hFirst := mul_le_mul_of_nonneg_left hPhi
      (show 0 ≤ (m : ℚ) - 1 by linarith)
    have hSecond := mul_le_mul_of_nonneg_right
      (show (m : ℚ) - 1 ≤ (n : ℚ) - 1 by linarith)
      (Ζdy n)
    unfold Ζa
    linarith
theorem Ζew (n : ℕ) :
    Ζa n = Ζal (n + 1) := by
  rw [Ζme]
  unfold Ζa Ζl
  push_cast
  ring
theorem Ζfa {n : ℕ} (hn : 2 ≤ n) :
    Ζl n = ((n : ℚ) - 2) / ((n : ℚ) + 1) := by
  by_cases hn2 : n = 2
  · subst n
    norm_num [Ζl, Ζg]
  · have hlarge : ¬ n + 1 ≤ 3 := by omega
    simp only [Ζl, Ζg, Ζdp hlarge]
    push_cast
    ring
theorem Ζde {n : ℕ} (hn : 2 ≤ n) :
    Ζa n =
      (((n : ℚ) - 1) * ((n : ℚ) - 2)) / ((n : ℚ) + 1) := by
  rw [Ζa, Ζfa hn]
  ring
theorem Ζmi
    {n : ℕ} (hn : 2 ≤ n) :
    Ζl (n + 1) - Ζl n =
      3 / (((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
  rw [Ζfa (by omega : 2 ≤ n + 1),
    Ζfa hn]
  have hn1Pos : (0 : ℚ) < (n : ℚ) + 1 := by
    have : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
    linarith
  have hn2Pos : (0 : ℚ) < (n : ℚ) + 2 := by linarith
  push_cast
  field_simp
  ring
theorem Ζlq (n : ℕ) :
    Ζl (n + 1) - Ζl n ≤ (1 : ℚ) / 4 := by
  by_cases hn : n ≤ 1
  · rcases (by omega : n = 0 ∨ n = 1) with h | h
    · subst n; norm_num [Ζl, Ζg]
    · subst n; norm_num [Ζl, Ζg]
  · have hn2 : 2 ≤ n := by omega
    rw [Ζmi hn2]
    have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    have hden : 0 < ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
      apply mul_pos <;> linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith
theorem Ζmw (x y : ℕ) :
    (x : ℚ) * Ζl y + (y : ℚ) * Ζl x -
      Ζa x - Ζa y =
      Ζfx (x + 1) (y + 1) := by
  unfold Ζa Ζl Ζfx
  push_cast
  ring
theorem Ζfh (x y : ℕ) :
    (x : ℚ) * Ζl y + (y : ℚ) * Ζl x -
      Ζa x - Ζa y ≤
      2 * min (Ζl x) (Ζl y) := by
  rw [Ζmw]
  exact Ζfr (x + 1) (y + 1)
theorem Ζla
    {x u : ℕ} (hx : 2 ≤ x) (hu : 2 ≤ u) :
    Ζa (x + u) - Ζa x -
        Ζa u =
      2 * Ζl x + 2 * Ζl u +
        6 / (((x + u : ℕ) : ℚ) + 1) := by
  have hxu : 2 ≤ x + u := by omega
  rw [Ζde hxu,
    Ζde hx,
    Ζde hu,
    Ζfa hx, Ζfa hu]
  have hxPos : (0 : ℚ) < (x : ℚ) + 1 := by
    have : (0 : ℚ) ≤ x := by exact_mod_cast (Nat.zero_le x)
    linarith
  have huPos : (0 : ℚ) < (u : ℚ) + 1 := by
    have : (0 : ℚ) ≤ u := by exact_mod_cast (Nat.zero_le u)
    linarith
  have hxuPos : (0 : ℚ) < ((x + u : ℕ) : ℚ) + 1 := by
    have : (0 : ℚ) ≤ (x + u : ℕ) := by
      exact_mod_cast (Nat.zero_le (x + u))
    linarith
  push_cast
  field_simp
  ring
theorem Ζmj
    {u : ℕ} (hu : 2 ≤ u) :
    Ζa (1 + u) - Ζa 1 -
      Ζa u - Ζl 1 - Ζl u =
      (3 * (u : ℚ)) / (((u : ℚ) + 1) * ((u : ℚ) + 2)) := by
  have hplus : 2 ≤ 1 + u := by omega
  rw [Ζde hplus,
    Ζde hu, Ζfa hu]
  have hOneBudget : Ζa 1 = 0 := by
    norm_num [Ζa]
  have hOnePhi : Ζl 1 = 0 := by
    norm_num [Ζl, Ζg]
  rw [hOneBudget, hOnePhi]
  have hu1Pos : (0 : ℚ) < (u : ℚ) + 1 := by
    have : (0 : ℚ) ≤ u := by exact_mod_cast (Nat.zero_le u)
    linarith
  have hu2Pos : (0 : ℚ) < (u : ℚ) + 2 := by linarith
  push_cast
  field_simp
  ring
theorem Ζhe
    {x u : ℕ} (hx : 0 < x) (hu : 0 < u) :
    Ζa (x + u) ≥ Ζa x +
      Ζa u + Ζl x + Ζl u := by
  rcases (by omega : x = 1 ∨ 2 ≤ x) with hx1 | hx2
  · subst x
    rcases (by omega : u = 1 ∨ 2 ≤ u) with hu1 | hu2
    · subst u
      norm_num [Ζa, Ζl, Ζg]
    · have hExact := Ζmj hu2
      have huq : (0 : ℚ) ≤ u := by exact_mod_cast (Nat.zero_le u)
      have hden : 0 < ((u : ℚ) + 1) * ((u : ℚ) + 2) := by
        apply mul_pos <;> linarith
      have hNonneg : 0 ≤ (3 * (u : ℚ)) /
          (((u : ℚ) + 1) * ((u : ℚ) + 2)) :=
        div_nonneg (by positivity) hden.le
      linarith
  · rcases (by omega : u = 1 ∨ 2 ≤ u) with hu1 | hu2
    · subst u
      have hExact := Ζmj hx2
      have hxq : (0 : ℚ) ≤ x := by exact_mod_cast (Nat.zero_le x)
      have hden : 0 < ((x : ℚ) + 1) * ((x : ℚ) + 2) := by
        apply mul_pos <;> linarith
      have hNonneg : 0 ≤ (3 * (x : ℚ)) /
          (((x : ℚ) + 1) * ((x : ℚ) + 2)) :=
        div_nonneg (by positivity) hden.le
      have hsum : x + 1 = 1 + x := Nat.add_comm x 1
      rw [hsum]
      linarith
    · have hExact := Ζla hx2 hu2
      have hPhiX := Ζdy x
      have hPhiU := Ζdy u
      have hDen : (0 : ℚ) < ((x + u : ℕ) : ℚ) + 1 := by
        have : (0 : ℚ) ≤ (x + u : ℕ) := by
          exact_mod_cast (Nat.zero_le (x + u))
        linarith
      have hFrac : 0 ≤ 6 / (((x + u : ℕ) : ℚ) + 1) :=
        div_nonneg (by norm_num) hDen.le
      linarith
theorem Ζlb
    {a : ℕ} (ha : 2 ≤ a) :
    Ζa (a + 1) - Ζa a =
      1 - 6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) := by
  rw [Ζde (by omega : 2 ≤ a + 1),
    Ζde ha]
  have ha1Pos : (0 : ℚ) < (a : ℚ) + 1 := by
    have : (0 : ℚ) ≤ a := by exact_mod_cast (Nat.zero_le a)
    linarith
  have ha2Pos : (0 : ℚ) < (a : ℚ) + 2 := by linarith
  push_cast
  field_simp
  ring
theorem Ζpd
    {a : ℕ} (ha : 2 ≤ a) :
    (1 : ℚ) / 2 ≤ Ζa (a + 1) -
      Ζa a := by
  rw [Ζlb ha]
  have haq : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have hden : 0 < ((a : ℚ) + 1) * ((a : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hdenBound : (12 : ℚ) ≤
      ((a : ℚ) + 1) * ((a : ℚ) + 2) := by nlinarith
  have hFrac : 6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) ≤
      (1 : ℚ) / 2 :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  linarith
theorem Ζei
    {d : ℕ} (hd : d ≤ 1) :
    Ζl (d + 1) - Ζl d = 0 := by
  rcases (by omega : d = 0 ∨ d = 1) with h | h
  · subst d; norm_num [Ζl, Ζg]
  · subst d; norm_num [Ζl, Ζg]
theorem Ζmk
    (a d₁ d₂ : ℕ)
    (hd₁ : d₁ ≤ a) (hd₂ : d₂ ≤ a) :
    (Ζl (d₁ + 1) - Ζl d₁) +
      (Ζl (d₂ + 1) - Ζl d₂) ≤
      Ζa (a + 1) - Ζa a := by
  by_cases ha : a ≤ 1
  · have hd₁' : d₁ ≤ 1 := hd₁.trans ha
    have hd₂' : d₂ ≤ 1 := hd₂.trans ha
    rw [Ζei hd₁',
      Ζei hd₂']
    rcases (by omega : a = 0 ∨ a = 1) with h | h
    · subst a; norm_num [Ζa, Ζl, Ζg]
    · subst a; norm_num [Ζa, Ζl, Ζg]
  · have ha2 : 2 ≤ a := by omega
    have h₁ := Ζlq d₁
    have h₂ := Ζlq d₂
    have hBudget := Ζpd ha2
    linarith
def Ζbt (x y : ℕ) : ℚ :=
  (x : ℚ) * Ζl y + (y : ℚ) * Ζl x
theorem Ζfe (x y : ℕ) :
    Ζbt x y ≤
      Ζa x + Ζa y +
        Ζl x + Ζl y := by
  have hExcess := Ζfh x y
  have hMinX : min (Ζl x) (Ζl y) ≤ Ζl x := min_le_left _ _
  have hMinY : min (Ζl x) (Ζl y) ≤ Ζl y := min_le_right _ _
  dsimp [Ζbt]
  linarith
theorem Ζnp
    {n : ℕ} (hn : 0 < n) :
    Ζl n ≤ Ζa n := by
  rcases (by omega : n = 1 ∨ 2 ≤ n) with hOne | hTwo
  · subst n
    norm_num [Ζl, Ζa, Ζg]
  · have hcast : (0 : ℚ) ≤ (n : ℚ) - 2 := by
      have hq : (2 : ℚ) ≤ n := by exact_mod_cast hTwo
      linarith
    have hprod := mul_nonneg hcast (Ζdy n)
    unfold Ζa
    nlinarith
theorem Ζed (n : ℕ) :
    Ζl n ≤ Ζa n := by
  by_cases hn : n = 0
  · subst n
    norm_num [Ζl, Ζa, Ζg]
  · exact Ζnp (Nat.pos_of_ne_zero hn)
theorem Ζml (y : ℕ) :
    Ζbt 1 y = Ζl y := by
  norm_num [Ζbt, Ζl, Ζg]
theorem Ζmq
    {a₁ a₂ b₁ b₂ c₁ c₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    Ζbt a₁ b₁ +
      Ζbt a₂ c₁ +
      Ζbt b₂ c₂ ≤
      Ζa (a₁ + a₂) +
      Ζa (b₁ + b₂) +
      Ζa (c₁ + c₂) := by
  have hAB := Ζfe a₁ b₁
  have hAC := Ζfe a₂ c₁
  have hBC := Ζfe b₂ c₂
  have hA := Ζhe ha₁ ha₂
  have hB := Ζhe hb₁ hb₂
  have hC := Ζhe hc₁ hc₂
  linarith
theorem Ζlc
    {x u y v : ℕ} (hx : 2 ≤ x) (hu : 2 ≤ u) :
    Ζbt x y + Ζbt u v ≤
      Ζa (x + u) +
      Ζa y + Ζa v := by
  have hXY := Ζfh x y
  have hUV := Ζfh u v
  have hMinX : min (Ζl x) (Ζl y) ≤ Ζl x := min_le_left _ _
  have hMinU : min (Ζl u) (Ζl v) ≤ Ζl u := min_le_left _ _
  have hMerge := Ζla hx hu
  have hDen : (0 : ℚ) < (((x + u : ℕ) : ℚ) + 1) := by
    have hNat : (0 : ℚ) ≤ (x + u : ℕ) := by
      exact_mod_cast (Nat.zero_le (x + u))
    linarith
  have hFrac : 0 ≤ 6 / (((x + u : ℕ) : ℚ) + 1) :=
    div_nonneg (by norm_num) hDen.le
  dsimp [Ζbt]
  linarith
theorem Ζcx (n : ℕ) :
    0 ≤ Ζa n := by
  by_cases hn : n = 0
  · subst n
    norm_num [Ζa, Ζl, Ζg]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hcast : (0 : ℚ) ≤ (n : ℚ) - 1 := by
      have : (1 : ℚ) ≤ n := by exact_mod_cast hnPos
      linarith
    exact mul_nonneg hcast (Ζdy n)
def Ζy
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) : ℚ :=
  max (Ζa nA + Ζa nB - tAB) 0 +
  max (Ζa nA + Ζa nC - tAC) 0 +
  max (Ζa nB + Ζa nC - tBC) 0
theorem Ζdd
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) :
    Ζy nA nB nC tAB tAC tBC =
      Ζy nB nA nC tAB tBC tAC := by
  unfold Ζy
  ac_rfl
theorem Ζbj
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) :
    Ζy nA nB nC tAB tAC tBC =
      Ζy nA nC nB tAC tAB tBC := by
  unfold Ζy
  ac_rfl
theorem Ζgt (budget score : ℚ) :
    max (budget - score) 0 = budget - min score budget := by
  by_cases h : score ≤ budget
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
  · have h' : budget ≤ score := le_of_not_ge h
    rw [min_eq_right h', max_eq_right (sub_nonpos.mpr h')]
    ring
theorem Ζdb
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) :
    Ζa nA + Ζa nB +
        Ζa nC ≤
      Ζy nA nB nC tAB tAC tBC ↔
    min tAB (Ζa nA + Ζa nB) +
      min tAC (Ζa nA + Ζa nC) +
      min tBC (Ζa nB + Ζa nC) ≤
        Ζa nA + Ζa nB +
          Ζa nC := by
  unfold Ζy
  rw [Ζgt,
    Ζgt,
    Ζgt]
  constructor <;> intro h <;> linarith
theorem Ζil
    (nA nB nC : ℕ) (tAB : ℚ) :
    Ζa nA + Ζa nB +
        Ζa nC ≤
      Ζy nA nB nC tAB 0 0 := by
  rw [Ζdb]
  have hAC : 0 ≤ Ζa nA + Ζa nC :=
    add_nonneg (Ζcx nA) (Ζcx nC)
  have hBC : 0 ≤ Ζa nB + Ζa nC :=
    add_nonneg (Ζcx nB) (Ζcx nC)
  rw [min_eq_left hAC, min_eq_left hBC]
  have hAB := min_le_right tAB
    (Ζa nA + Ζa nB)
  have hC := Ζcx nC
  linarith
theorem Ζse
    (nA nB nC : ℕ) (tAC : ℚ) :
    Ζa nA + Ζa nB +
        Ζa nC ≤
      Ζy nA nB nC 0 tAC 0 := by
  rw [Ζbj nA nB nC 0 tAC 0]
  have h := Ζil nA nC nB tAC
  convert h using 1
  ring
theorem Ζsf
    (nA nB nC : ℕ) (tBC : ℚ) :
    Ζa nA + Ζa nB +
        Ζa nC ≤
      Ζy nA nB nC 0 0 tBC := by
  rw [Ζdd nA nB nC 0 0 tBC,
    Ζbj nB nA nC 0 tBC 0]
  have h := Ζil nB nC nA tBC
  convert h using 1
  ring
theorem Ζjl
    {x u y v nA nB nC : ℕ} {tAB tAC : ℚ}
    (hx : 0 < x) (hu : 0 < u)
    (hA : x + u ≤ nA) (hB : y ≤ nB) (hC : v ≤ nC)
    (hAB : tAB ≤ Ζbt x y)
    (hAC : tAC ≤ Ζbt u v) :
    Ζa nA + Ζa nB +
        Ζa nC ≤
      Ζy nA nB nC tAB tAC 0 := by
  rw [Ζdb]
  have hBC : 0 ≤ Ζa nB + Ζa nC :=
    add_nonneg (Ζcx nB) (Ζcx nC)
  rw [min_eq_left hBC]
  have hBudgetA := Ζey hA
  have hBudgetB := Ζey hB
  have hBudgetC := Ζey hC
  rcases (by omega : x = 1 ∨ 2 ≤ x) with hxOne | hxLarge
  · subst x
    have hFirst : tAB ≤ Ζa nB := by
      calc
        tAB ≤ Ζbt 1 y := hAB
        _ = Ζl y := Ζml y
        _ ≤ Ζa y := Ζed y
        _ ≤ Ζa nB := hBudgetB
    have hMinFirst := min_le_left tAB
      (Ζa nA + Ζa nB)
    have hMinSecond := min_le_right tAC
      (Ζa nA + Ζa nC)
    linarith
  · rcases (by omega : u = 1 ∨ 2 ≤ u) with huOne | huLarge
    · subst u
      have hSecond : tAC ≤ Ζa nC := by
        calc
          tAC ≤ Ζbt 1 v := hAC
          _ = Ζl v := Ζml v
          _ ≤ Ζa v := Ζed v
          _ ≤ Ζa nC := hBudgetC
      have hMinFirst := min_le_right tAB
        (Ζa nA + Ζa nB)
      have hMinSecond := min_le_left tAC
        (Ζa nA + Ζa nC)
      linarith
    · have hTotal := Ζlc
        hxLarge huLarge (y := y) (v := v)
      have hMinFirst := min_le_left tAB
        (Ζa nA + Ζa nB)
      have hMinSecond := min_le_left tAC
        (Ζa nA + Ζa nC)
      linarith
theorem Ζjc
    {a₁ a₂ b₁ b₂ c₁ c₂ nA nB nC : ℕ}
    {tAB tAC tBC : ℚ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hA : a₁ + a₂ ≤ nA)
    (hB : b₁ + b₂ ≤ nB)
    (hC : c₁ + c₂ ≤ nC)
    (hAB : tAB ≤ Ζbt a₁ b₁)
    (hAC : tAC ≤ Ζbt a₂ c₁)
    (hBC : tBC ≤ Ζbt b₂ c₂) :
    Ζa nA + Ζa nB +
        Ζa nC ≤
      Ζy nA nB nC tAB tAC tBC := by
  rw [Ζdb]
  have hTotal := Ζmq
    ha₁ ha₂ hb₁ hb₂ hc₁ hc₂
  have hBudgetA := Ζey hA
  have hBudgetB := Ζey hB
  have hBudgetC := Ζey hC
  have hMinAB := min_le_left tAB
    (Ζa nA + Ζa nB)
  have hMinAC := min_le_left tAC
    (Ζa nA + Ζa nC)
  have hMinBC := min_le_left tBC
    (Ζa nB + Ζa nC)
  linarith
end JSP523.Rank3
end
section
namespace JSP523.Rank3
end JSP523.Rank3
end
section
namespace JSP523.Rank3
theorem Ζbe
    {d : ℕ} (hd : d ≤ 1) : Ζl d = 0 := by
  rcases (by omega : d = 0 ∨ d = 1) with h | h
  · subst d; norm_num [Ζl, Ζg]
  · subst d; norm_num [Ζl, Ζg]
theorem Ζuu
    (a b : ℕ) :
    ((a : ℚ) - 2) * Ζl b +
      (b : ℚ) * Ζl a ≤
        Ζa a + Ζa b := by
  have hGap : Ζa a + Ζa b -
      (((a : ℚ) - 2) * Ζl b +
        (b : ℚ) * Ζl a) =
      ((a : ℚ) - b - 1) * (Ζl a - Ζl b) := by
    unfold Ζa
    ring
  rw [← sub_nonneg, hGap]
  by_cases h : b + 1 ≤ a
  · have hCast : (b : ℚ) + 1 ≤ a := by exact_mod_cast h
    have hPhi : Ζl b ≤ Ζl a :=
      Ζdl (by omega : b ≤ a)
    exact mul_nonneg (by linarith) (by linarith)
  · have hNat : a ≤ b := by omega
    have hCast : (a : ℚ) ≤ b := by exact_mod_cast hNat
    have hPhi : Ζl a ≤ Ζl b := Ζdl hNat
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
theorem Ζsw
    (a b : ℕ) :
    ((a : ℚ) - 1) * Ζl b +
      ((b : ℚ) - 1) * Ζl a ≤
        Ζa a + Ζa b := by
  have hGap : Ζa a + Ζa b -
      (((a : ℚ) - 1) * Ζl b +
        ((b : ℚ) - 1) * Ζl a) =
      ((a : ℚ) - b) * (Ζl a - Ζl b) := by
    unfold Ζa
    ring
  rw [← sub_nonneg, hGap]
  rcases le_total a b with hab | hba
  · have hCast : (a : ℚ) ≤ b := by exact_mod_cast hab
    have hPhi : Ζl a ≤ Ζl b := Ζdl hab
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have hCast : (b : ℚ) ≤ a := by exact_mod_cast hba
    have hPhi : Ζl b ≤ Ζl a := Ζdl hba
    exact mul_nonneg (by linarith) (by linarith)
section BipartiteGraph
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
def Ζi (G : Finset (α × β)) (B : Finset β) (x : α) : ℕ :=
  (B.filter fun y => (x, y) ∈ G).card
def Ζf (G : Finset (α × β)) (A : Finset α) (y : β) : ℕ :=
  (A.filter fun x => (x, y) ∈ G).card
def Ζd
    (G : Finset (α × β)) (A : Finset α) (B : Finset β) : ℚ :=
  (∑ x ∈ A, Ζl (Ζi G B x)) +
    ∑ y ∈ B, Ζl (Ζf G A y)
def Ζbn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) : Finset (β × α) :=
  G.image Prod.swap
theorem Ζgd {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (y : β) (x : α) :
    (y, x) ∈ Ζbn G ↔ (x, y) ∈ G := by
  simp [Ζbn, Finset.mem_image]
theorem Ζcl {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (A : Finset α) (y : β) :
    Ζi (Ζbn G) A y =
      Ζf G A y := by
  simp [Ζi, Ζf, Ζgd]
theorem Ζef {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (B : Finset β) (x : α) :
    Ζf (Ζbn G) B x =
      Ζi G B x := by
  simp [Ζi, Ζf, Ζgd]
theorem Ζcq {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (A : Finset α) (B : Finset β) :
    Ζd (Ζbn G) B A =
      Ζd G A B := by
  have hLeft (y : β) :
      Ζi (Ζbn G) A y =
        Ζf G A y := by
    exact Ζcl G A y
  have hRight (x : α) :
      Ζf (Ζbn G) B x =
        Ζi G B x := by
    exact Ζef G B x
  simp only [Ζd, hLeft, hRight]
  ac_rfl
theorem Ζai
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (hNo : ∀ x ∈ A, ∀ y ∈ B, (x, y) ∉ G) :
    Ζd G A B = 0 := by
  have hLeft (x : α) (hx : x ∈ A) :
      Ζi G B x = 0 := by
    unfold Ζi
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro y hyB hxy
    exact hNo x hx y hyB hxy
  have hRight (y : β) (hy : y ∈ B) :
      Ζf G A y = 0 := by
    unfold Ζf
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x hxA hxy
    exact hNo x hxA y hy hxy
  unfold Ζd
  have hL : (∑ x ∈ A, Ζl (Ζi G B x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hLeft x hx]
    exact Ζbe (by omega)
  have hR : (∑ y ∈ B, Ζl (Ζf G A y)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [hRight y hy]
    exact Ζbe (by omega)
  rw [hL, hR]
  ring
theorem Ζnl
    (G : Finset (α × β)) (A : Finset α) (B : Finset β) :
    0 ≤ Ζd G A B := by
  unfold Ζd
  apply add_nonneg <;> apply Finset.sum_nonneg
  · intro x hx
    exact Ζdy _
  · intro y hy
    exact Ζdy _
theorem Ζks
    (G : Finset (α × β)) (B : Finset β) (x : α) :
    Ζi G B x ≤ B.card :=
  Finset.card_filter_le _ _
theorem Ζor
    (G : Finset (α × β)) (A : Finset α) (y : β) :
    Ζf G A y ≤ A.card :=
  Finset.card_filter_le _ _
theorem Ζbz
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (A' : Finset α) (B' : Finset β)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hEdges : ∀ x ∈ A, ∀ y ∈ B,
      (x, y) ∈ G → x ∈ A' ∧ y ∈ B') :
    Ζd G A B ≤
      Ζbt A'.card B'.card := by
  have hLeftDeg (x : α) (hx : x ∈ A) :
      Ζi G B x ≤ B'.card := by
    unfold Ζi
    apply Finset.card_le_card
    intro y hy
    exact (hEdges x hx y (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hy).2).2
  have hRightDeg (y : β) (hy : y ∈ B) :
      Ζf G A y ≤ A'.card := by
    unfold Ζf
    apply Finset.card_le_card
    intro x hx
    exact (hEdges x (Finset.mem_filter.mp hx).1 y hy
      (Finset.mem_filter.mp hx).2).1
  have hLeftZero (x : α) (hx : x ∈ A) (hxNot : x ∉ A') :
      Ζl (Ζi G B x) = 0 := by
    have hDeg : Ζi G B x = 0 := by
      by_contra hNe
      have hPos : 0 < (B.filter fun y => (x, y) ∈ G).card :=
        Nat.pos_of_ne_zero hNe
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hPos
      exact hxNot ((hEdges x hx y (Finset.mem_filter.mp hy).1
        (Finset.mem_filter.mp hy).2).1)
    rw [hDeg]
    exact Ζbe (by omega)
  have hRightZero (y : β) (hy : y ∈ B) (hyNot : y ∉ B') :
      Ζl (Ζf G A y) = 0 := by
    have hDeg : Ζf G A y = 0 := by
      by_contra hNe
      have hPos : 0 < (A.filter fun x => (x, y) ∈ G).card :=
        Nat.pos_of_ne_zero hNe
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hPos
      exact hyNot ((hEdges x (Finset.mem_filter.mp hx).1 y hy
        (Finset.mem_filter.mp hx).2).2)
    rw [hDeg]
    exact Ζbe (by omega)
  have hLeftSplit :
      (∑ x ∈ A, Ζl (Ζi G B x)) =
      ∑ x ∈ A', Ζl (Ζi G B x) := by
    symm
    apply Finset.sum_subset hA'
    intro x hxA hxNot
    exact hLeftZero x hxA hxNot
  have hRightSplit :
      (∑ y ∈ B, Ζl (Ζf G A y)) =
      ∑ y ∈ B', Ζl (Ζf G A y) := by
    symm
    apply Finset.sum_subset hB'
    intro y hyB hyNot
    exact hRightZero y hyB hyNot
  have hLeftBound :
      (∑ x ∈ A', Ζl (Ζi G B x)) ≤
      (A'.card : ℚ) * Ζl B'.card := by
    calc
      (∑ x ∈ A', Ζl (Ζi G B x)) ≤
          ∑ _x ∈ A', Ζl B'.card := by
            apply Finset.sum_le_sum
            intro x hx
            exact Ζdl (hLeftDeg x (hA' hx))
      _ = (A'.card : ℚ) * Ζl B'.card := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hRightBound :
      (∑ y ∈ B', Ζl (Ζf G A y)) ≤
      (B'.card : ℚ) * Ζl A'.card := by
    calc
      (∑ y ∈ B', Ζl (Ζf G A y)) ≤
          ∑ _y ∈ B', Ζl A'.card := by
            apply Finset.sum_le_sum
            intro y hy
            exact Ζdl (hRightDeg y (hB' hy))
      _ = (B'.card : ℚ) * Ζl A'.card := by
            simp [Finset.sum_const, nsmul_eq_mul]
  unfold Ζd Ζbt
  rw [hLeftSplit, hRightSplit]
  linarith
theorem Ζmt
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {x y : α}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hdx : Ζi G B x ≤ 1)
    (hdy : Ζi G B y ≤ 1) :
    Ζd G A B ≤
      Ζa A.card + Ζa B.card := by
  let f : α → ℚ := fun z => Ζl (Ζi G B z)
  let g : β → ℚ := fun z => Ζl (Ζf G A z)
  have hfx : f x = 0 := Ζbe hdx
  have hfy : f y = 0 := Ζbe hdy
  have hyErase : y ∈ A.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hLeftSplit : (∑ z ∈ A, f z) =
      ∑ z ∈ (A.erase x).erase y, f z := by
    calc
      (∑ z ∈ A, f z) = (∑ z ∈ A.erase x, f z) + f x :=
        (Finset.sum_erase_add A f hx).symm
      _ = ((∑ z ∈ (A.erase x).erase y, f z) + f y) + f x := by
        rw [← Finset.sum_erase_add (A.erase x) f hyErase]
      _ = ∑ z ∈ (A.erase x).erase y, f z := by rw [hfx, hfy]; ring
  have hLeftBound : (∑ z ∈ (A.erase x).erase y, f z) ≤
      (((A.erase x).erase y).card : ℚ) * Ζl B.card := by
    calc
      (∑ z ∈ (A.erase x).erase y, f z) ≤
          ∑ _z ∈ (A.erase x).erase y, Ζl B.card := by
            apply Finset.sum_le_sum
            intro z hz
            exact Ζdl (Ζks G B z)
      _ = (((A.erase x).erase y).card : ℚ) * Ζl B.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hRightBound : (∑ z ∈ B, g z) ≤
      (B.card : ℚ) * Ζl A.card := by
    calc
      (∑ z ∈ B, g z) ≤ ∑ _z ∈ B, Ζl A.card := by
        apply Finset.sum_le_sum
        intro z hz
        exact Ζdl (Ζor G A z)
      _ = (B.card : ℚ) * Ζl A.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hCardX := Finset.card_erase_add_one hx
  have hCardY := Finset.card_erase_add_one hyErase
  have hCardQ : (((A.erase x).erase y).card : ℚ) =
      (A.card : ℚ) - 2 := by
    have hNat : ((A.erase x).erase y).card + 2 = A.card := by omega
    have hRat : (((A.erase x).erase y).card : ℚ) + 2 =
        (A.card : ℚ) := by exact_mod_cast hNat
    linarith
  have hScalar := Ζuu A.card B.card
  unfold Ζd
  change (∑ z ∈ A, f z) + (∑ z ∈ B, g z) ≤ _
  rw [hLeftSplit]
  rw [hCardQ] at hLeftBound
  linarith
theorem Ζgp
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {x : α} {y : β}
    (hx : x ∈ A) (hy : y ∈ B)
    (hdx : Ζi G B x ≤ 1)
    (hdy : Ζf G A y ≤ 1) :
    Ζd G A B ≤
      Ζa A.card + Ζa B.card := by
  let f : α → ℚ := fun z => Ζl (Ζi G B z)
  let g : β → ℚ := fun z => Ζl (Ζf G A z)
  have hfx : f x = 0 := Ζbe hdx
  have hgy : g y = 0 := Ζbe hdy
  have hLeftSplit : (∑ z ∈ A, f z) = ∑ z ∈ A.erase x, f z := by
    calc
      (∑ z ∈ A, f z) = (∑ z ∈ A.erase x, f z) + f x :=
        (Finset.sum_erase_add A f hx).symm
      _ = ∑ z ∈ A.erase x, f z := by rw [hfx]; ring
  have hRightSplit : (∑ z ∈ B, g z) = ∑ z ∈ B.erase y, g z := by
    calc
      (∑ z ∈ B, g z) = (∑ z ∈ B.erase y, g z) + g y :=
        (Finset.sum_erase_add B g hy).symm
      _ = ∑ z ∈ B.erase y, g z := by rw [hgy]; ring
  have hLeftBound : (∑ z ∈ A.erase x, f z) ≤
      ((A.erase x).card : ℚ) * Ζl B.card := by
    calc
      (∑ z ∈ A.erase x, f z) ≤
          ∑ _z ∈ A.erase x, Ζl B.card := by
            apply Finset.sum_le_sum
            intro z hz
            exact Ζdl (Ζks G B z)
      _ = ((A.erase x).card : ℚ) * Ζl B.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hRightBound : (∑ z ∈ B.erase y, g z) ≤
      ((B.erase y).card : ℚ) * Ζl A.card := by
    calc
      (∑ z ∈ B.erase y, g z) ≤
          ∑ _z ∈ B.erase y, Ζl A.card := by
            apply Finset.sum_le_sum
            intro z hz
            exact Ζdl (Ζor G A z)
      _ = ((B.erase y).card : ℚ) * Ζl A.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hCardX := Finset.card_erase_add_one hx
  have hCardY := Finset.card_erase_add_one hy
  have hCardAQ : ((A.erase x).card : ℚ) = (A.card : ℚ) - 1 := by
    have hRat : ((A.erase x).card : ℚ) + 1 = (A.card : ℚ) := by
      exact_mod_cast hCardX
    linarith
  have hCardBQ : ((B.erase y).card : ℚ) = (B.card : ℚ) - 1 := by
    have hRat : ((B.erase y).card : ℚ) + 1 = (B.card : ℚ) := by
      exact_mod_cast hCardY
    linarith
  have hScalar := Ζsw A.card B.card
  unfold Ζd
  change (∑ z ∈ A, f z) + (∑ z ∈ B, g z) ≤ _
  rw [hLeftSplit, hRightSplit]
  rw [hCardAQ] at hLeftBound
  rw [hCardBQ] at hRightBound
  linarith
def Ζcn (G : Finset (α × β)) : Finset (β × α) :=
  G.image fun e => (e.2, e.1)
theorem Ζfs
    (G : Finset (α × β)) (x : α) (y : β) :
    (y, x) ∈ Ζcn G ↔ (x, y) ∈ G := by
  classical
  constructor
  · intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    rcases e with ⟨u, v⟩
    cases Prod.mk.inj heq with
    | intro hv hu =>
      change u = x at hu
      change v = y at hv
      simpa only [hu, hv] using he
  · intro h
    exact Finset.mem_image.mpr ⟨(x, y), h, rfl⟩
theorem Ζdt
    (G : Finset (α × β)) (A : Finset α)
    (y : β) :
    Ζi (Ζcn G) A y =
      Ζf G A y := by
  unfold Ζi Ζf
  congr 1
  ext x
  simp [Ζfs]
theorem Ζvh
    (G : Finset (α × β)) (B : Finset β) (x : α) :
    Ζf (Ζcn G) B x =
      Ζi G B x := by
  unfold Ζi Ζf
  congr 1
  ext y
  simp [Ζfs]
theorem Ζuv
    (G : Finset (α × β)) (A : Finset α)
    (B : Finset β) :
    Ζd (Ζcn G) B A =
      Ζd G A B := by
  unfold Ζd
  simp_rw [Ζdt, Ζvh]
  ring
theorem Ζqr
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {x y : β}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y)
    (hdx : Ζf G A x ≤ 1)
    (hdy : Ζf G A y ≤ 1) :
    Ζd G A B ≤
      Ζa A.card + Ζa B.card := by
  have hFlip := Ζmt
    (Ζcn G) B A hx hy hxy
    (by rw [Ζdt]; exact hdx)
    (by rw [Ζdt]; exact hdy)
  rw [Ζuv] at hFlip
  linarith
def Ζig
    (A : Finset α) (B : Finset β) : Sum α β → Prop
  | Sum.inl x => x ∈ A
  | Sum.inr y => y ∈ B
def Ζiv
    (G : Finset (α × β)) (A : Finset α)
    (B : Finset β) : Sum α β → ℕ
  | Sum.inl x => Ζi G B x
  | Sum.inr y => Ζf G A y
theorem Ζtv
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (u v : Sum α β)
    (hu : Ζig A B u)
    (hv : Ζig A B v)
    (huv : u ≠ v)
    (hdu : Ζiv G A B u ≤ 1)
    (hdv : Ζiv G A B v ≤ 1) :
    Ζd G A B ≤
      Ζa A.card + Ζa B.card := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      have hxy : x ≠ y := by
        intro h
        exact huv (by rw [h])
      exact Ζmt G A B hu hv hxy hdu hdv
    | inr y =>
      exact Ζgp G A B hu hv hdu hdv
  | inr x =>
    cases v with
    | inl y =>
      exact Ζgp G A B hv hu hdv hdu
    | inr y =>
      have hxy : x ≠ y := by
        intro h
        exact huv (by rw [h])
      exact Ζqr G A B hu hv hxy hdu hdv
theorem Ζdq
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (hPositive : Ζa A.card + Ζa B.card <
      Ζd G A B)
    {u v : Sum α β}
    (hu : Ζig A B u)
    (hv : Ζig A B v)
    (hdu : Ζiv G A B u ≤ 1)
    (hdv : Ζiv G A B v ≤ 1) :
    u = v := by
  by_contra hNe
  have hBound := Ζtv G A B
    u v hu hv hNe hdu hdv
  exact (not_le.mpr hPositive) hBound
theorem Ζdz
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (hZero : ∀ x ∈ A, Ζi G B x = 0) :
    Ζd G A B = 0 := by
  have hRightZero : ∀ y ∈ B, Ζf G A y = 0 := by
    intro y hy
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
    have hxy : (x, y) ∈ G := (Finset.mem_filter.mp hx).2
    have hLeftPos : 0 < Ζi G B x := by
      apply Finset.card_pos.mpr
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
    have hLeftZero := hZero x hxA
    omega
  unfold Ζd
  have hLeftSum : (∑ x ∈ A, Ζl (Ζi G B x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hZero x hx]
    exact Ζbe (by omega)
  have hRightSum : (∑ y ∈ B, Ζl (Ζf G A y)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [hRightZero y hy]
    exact Ζbe (by omega)
  rw [hLeftSum, hRightSum]
  ring
theorem Ζjs
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {c : α} (hc : c ∈ A)
    (hStar : ∀ x ∈ A, x ≠ c → Ζi G B x = 0) :
    Ζd G A B ≤ Ζl B.card := by
  have hRightOne : ∀ y ∈ B, Ζf G A y ≤ 1 := by
    intro y hy
    have hsub : A.filter (fun x => (x, y) ∈ G) ⊆ ({c} : Finset α) := by
      intro x hx
      have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
      have hxy : (x, y) ∈ G := (Finset.mem_filter.mp hx).2
      by_contra hxNotC
      have hxc : x ≠ c := by
        intro h
        exact hxNotC (by simp [h])
      have hLeftPos : 0 < Ζi G B x := by
        apply Finset.card_pos.mpr
        exact ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
      have hLeftZero := hStar x hxA hxc
      omega
    exact (Finset.card_le_card hsub).trans (by simp)
  have hLeftSum : (∑ x ∈ A, Ζl (Ζi G B x)) =
      Ζl (Ζi G B c) := by
    apply Finset.sum_eq_single_of_mem c hc
    intro x hx hxc
    rw [hStar x hx hxc]
    exact Ζbe (by omega)
  have hRightSum :
      (∑ y ∈ B, Ζl (Ζf G A y)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    exact Ζbe (hRightOne y hy)
  have hCenterBound : Ζl (Ζi G B c) ≤
      Ζl B.card := Ζdl (Ζks G B c)
  unfold Ζd
  rw [hLeftSum, hRightSum]
  simpa using hCenterBound
end BipartiteGraph
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section TripartitePositive
variable {α : Type*} [DecidableEq α]
structure Ζs (α : Type*) where
  ab : Finset (α × α)
  ac : Finset (α × α)
  bc : Finset (α × α)
def Ζz
    (G : Ζs α)
    (A B C : Finset α) : Prop :=
  (∀ a ∈ A,
    0 < Ζi G.ab B a →
    0 < Ζi G.ac C a →
      Ζi G.ab B a = 1 ∧
        Ζi G.ac C a = 1) ∧
  (∀ b ∈ B,
    0 < Ζf G.ab A b →
    0 < Ζi G.bc C b →
      Ζf G.ab A b = 1 ∧
        Ζi G.bc C b = 1) ∧
  (∀ c ∈ C,
    0 < Ζf G.ac A c →
    0 < Ζf G.bc B c →
      Ζf G.ac A c = 1 ∧
        Ζf G.bc B c = 1)
theorem Ζfo
    {G : Ζs α} {A B C : Finset α}
    (hMixed : Ζz G A B C)
    {a : α} (ha : a ∈ A)
    (hAC : 0 < Ζi G.ac C a) :
    Ζi G.ab B a ≤ 1 := by
  by_cases hAB : Ζi G.ab B a = 0
  · omega
  · have hABPos : 0 < Ζi G.ab B a := Nat.pos_of_ne_zero hAB
    exact (hMixed.1 a ha hABPos hAC).1.le
theorem Ζho
    {G : Ζs α} {A B C : Finset α}
    (hMixed : Ζz G A B C)
    {b : α} (hb : b ∈ B)
    (hBC : 0 < Ζi G.bc C b) :
    Ζf G.ab A b ≤ 1 := by
  by_cases hAB : Ζf G.ab A b = 0
  · omega
  · have hABPos : 0 < Ζf G.ab A b := Nat.pos_of_ne_zero hAB
    exact (hMixed.2.1 b hb hABPos hBC).1.le
theorem Ζgq
    (G : Ζs α)
    (A B C : Finset α)
    (hMixed : Ζz G A B C)
    (hPositive : Ζa A.card + Ζa B.card <
      Ζd G.ab A B) :
    Ζd G.ac A C +
      Ζd G.bc B C ≤
        Ζl C.card := by
  by_cases hA : ∃ a ∈ A, 0 < Ζi G.ac C a
  · obtain ⟨a, haA, haAC⟩ := hA
    have haLow : Ζi G.ab B a ≤ 1 :=
      Ζfo hMixed haA haAC
    have hOnlyA : ∀ a' ∈ A, a' ≠ a →
        Ζi G.ac C a' = 0 := by
      intro a' ha'A hNe
      by_contra hNotZero
      have ha'AC : 0 < Ζi G.ac C a' :=
        Nat.pos_of_ne_zero hNotZero
      have ha'Low : Ζi G.ab B a' ≤ 1 :=
        Ζfo hMixed ha'A ha'AC
      have hEq : (Sum.inl a' : Sum α α) = Sum.inl a :=
        Ζdq G.ab A B
          hPositive ha'A haA ha'Low haLow
      exact hNe (Sum.inl.inj hEq)
    have hBZero : ∀ b ∈ B, Ζi G.bc C b = 0 := by
      intro b hbB
      by_contra hNotZero
      have hbBC : 0 < Ζi G.bc C b :=
        Nat.pos_of_ne_zero hNotZero
      have hbLow : Ζf G.ab A b ≤ 1 :=
        Ζho hMixed hbB hbBC
      have hEq : (Sum.inr b : Sum α α) = Sum.inl a :=
        Ζdq G.ab A B
          hPositive hbB haA hbLow haLow
      cases hEq
    have hACBound := Ζjs
      G.ac A C haA hOnlyA
    have hBCZero := Ζdz
      G.bc B C hBZero
    rw [hBCZero]
    simpa using hACBound
  · have hAZero : ∀ a ∈ A, Ζi G.ac C a = 0 := by
      intro a haA
      by_contra hNotZero
      exact hA ⟨a, haA, Nat.pos_of_ne_zero hNotZero⟩
    have hACZero := Ζdz
      G.ac A C hAZero
    rw [hACZero]
    by_cases hB : ∃ b ∈ B, 0 < Ζi G.bc C b
    · obtain ⟨b, hbB, hbBC⟩ := hB
      have hbLow : Ζf G.ab A b ≤ 1 :=
        Ζho hMixed hbB hbBC
      have hOnlyB : ∀ b' ∈ B, b' ≠ b →
          Ζi G.bc C b' = 0 := by
        intro b' hb'B hNe
        by_contra hNotZero
        have hb'BC : 0 < Ζi G.bc C b' :=
          Nat.pos_of_ne_zero hNotZero
        have hb'Low : Ζf G.ab A b' ≤ 1 :=
          Ζho hMixed hb'B hb'BC
        have hEq : (Sum.inr b' : Sum α α) = Sum.inr b :=
          Ζdq G.ab A B
            hPositive hb'B hbB hb'Low hbLow
        exact hNe (Sum.inr.inj hEq)
      have hBCBound := Ζjs
        G.bc B C hbB hOnlyB
      simpa using hBCBound
    · have hBZero : ∀ b ∈ B, Ζi G.bc C b = 0 := by
        intro b hbB
        by_contra hNotZero
        exact hB ⟨b, hbB, Nat.pos_of_ne_zero hNotZero⟩
      have hBCZero := Ζdz
        G.bc B C hBZero
      rw [hBCZero]
      simpa using Ζdy C.card
theorem Ζjm
    (G : Ζs α)
    (A B C : Finset α)
    (hMixed : Ζz G A B C)
    (hPositive : Ζa A.card + Ζa B.card <
      Ζd G.ab A B) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  have hOther := Ζgq
    G A B C hMixed hPositive
  have hPhiBudget := Ζed C.card
  have hACnonneg := Ζnl G.ac A C
  have hBCnonneg := Ζnl G.bc B C
  have hA := Ζcx A.card
  have hB := Ζcx B.card
  have hAC : 0 ≤ Ζa A.card + Ζa C.card -
      Ζd G.ac A C := by linarith
  have hBC : 0 ≤ Ζa B.card + Ζa C.card -
      Ζd G.bc B C := by linarith
  have hAB : Ζa A.card + Ζa B.card -
      Ζd G.ab A B ≤ 0 := by linarith
  unfold Ζy
  rw [max_eq_right hAB, max_eq_left hAC, max_eq_left hBC]
  linarith
end TripartitePositive
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
theorem Ζji
    (G : Ζs α)
    (A B C : Finset α)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, (a, c) ∉ G.ac)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  rw [Ζai
      G.ac A C hAC,
    Ζai
      G.bc B C hBC]
  exact Ζil A.card B.card C.card
    (Ζd G.ab A B)
theorem Ζnq
    (G : Ζs α)
    (A B C Aab Aac Bab Cac : Finset α)
    (hA : Aab ∪ Aac ⊆ A)
    (hADisj : Disjoint Aab Aac)
    (hB : Bab ⊆ B) (hC : Cac ⊆ C)
    (hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ Bab)
    (hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ Cac)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc)
    (haAB : 0 < Aab.card) (haAC : 0 < Aac.card) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  have hAabSub : Aab ⊆ A := by
    exact Finset.subset_union_left.trans hA
  have hAacSub : Aac ⊆ A := by
    exact Finset.subset_union_right.trans hA
  have hABBound := Ζbz
    G.ab A B Aab Bab hAabSub hB hAB
  have hACBound := Ζbz
    G.ac A C Aac Cac hAacSub hC hAC
  have hCardA := Finset.card_le_card hA
  rw [Finset.card_union_of_disjoint hADisj] at hCardA
  have hCardB := Finset.card_le_card hB
  have hCardC := Finset.card_le_card hC
  have hPay := Ζjl
    haAB haAC hCardA hCardB hCardC hABBound hACBound
  rw [Ζai
    G.bc B C hBC]
  exact hPay
theorem Ζmx
    (G : Ζs α)
    (A B C Aab Aac Bab Bbc Cac Cbc : Finset α)
    (hA : Aab ∪ Aac ⊆ A) (hADisj : Disjoint Aab Aac)
    (hB : Bab ∪ Bbc ⊆ B) (hBDisj : Disjoint Bab Bbc)
    (hC : Cac ∪ Cbc ⊆ C) (hCDisj : Disjoint Cac Cbc)
    (hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ Bab)
    (hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ Cac)
    (hBC : ∀ b ∈ B, ∀ c ∈ C,
      (b, c) ∈ G.bc → b ∈ Bbc ∧ c ∈ Cbc)
    (haAB : 0 < Aab.card) (haAC : 0 < Aac.card)
    (hbAB : 0 < Bab.card) (hbBC : 0 < Bbc.card)
    (hcAC : 0 < Cac.card) (hcBC : 0 < Cbc.card) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  have hAabSub : Aab ⊆ A := by
    exact Finset.subset_union_left.trans hA
  have hAacSub : Aac ⊆ A := by
    exact Finset.subset_union_right.trans hA
  have hBabSub : Bab ⊆ B := by
    exact Finset.subset_union_left.trans hB
  have hBbcSub : Bbc ⊆ B := by
    exact Finset.subset_union_right.trans hB
  have hCacSub : Cac ⊆ C := by
    exact Finset.subset_union_left.trans hC
  have hCbcSub : Cbc ⊆ C := by
    exact Finset.subset_union_right.trans hC
  have hABBound := Ζbz
    G.ab A B Aab Bab hAabSub hBabSub hAB
  have hACBound := Ζbz
    G.ac A C Aac Cac hAacSub hCacSub hAC
  have hBCBound := Ζbz
    G.bc B C Bbc Cbc hBbcSub hCbcSub hBC
  have hCardA := Finset.card_le_card hA
  rw [Finset.card_union_of_disjoint hADisj] at hCardA
  have hCardB := Finset.card_le_card hB
  rw [Finset.card_union_of_disjoint hBDisj] at hCardB
  have hCardC := Finset.card_le_card hC
  rw [Finset.card_union_of_disjoint hCDisj] at hCardC
  have hPay := Ζjc
    haAB haAC hbAB hbBC hcAC hcBC
    hCardA hCardB hCardC hABBound hACBound hBCBound
  exact hPay
theorem Ζpe
    (G : Ζs α) (A B C : Finset α)
    (hPureA : ∀ a ∈ A,
      Ζi G.ab B a = 0 ∨ Ζi G.ac C a = 0)
    (hPureB : ∀ b ∈ B,
      Ζf G.ab A b = 0 ∨ Ζi G.bc C b = 0)
    (hPureC : ∀ c ∈ C,
      Ζf G.ac A c = 0 ∨ Ζf G.bc B c = 0)
    (hABedge : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab)
    (hACedge : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac)
    (hBCedge : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  let Aab := A.filter fun a => 0 < Ζi G.ab B a
  let Aac := A.filter fun a => 0 < Ζi G.ac C a
  let Bab := B.filter fun b => 0 < Ζf G.ab A b
  let Bbc := B.filter fun b => 0 < Ζi G.bc C b
  let Cac := C.filter fun c => 0 < Ζf G.ac A c
  let Cbc := C.filter fun c => 0 < Ζf G.bc B c
  have hA : Aab ∪ Aac ⊆ A := by
    intro a ha
    rcases Finset.mem_union.mp ha with hAB | hAC
    · exact (Finset.mem_filter.mp hAB).1
    · exact (Finset.mem_filter.mp hAC).1
  have hB : Bab ∪ Bbc ⊆ B := by
    intro b hb
    rcases Finset.mem_union.mp hb with hAB | hBC
    · exact (Finset.mem_filter.mp hAB).1
    · exact (Finset.mem_filter.mp hBC).1
  have hC : Cac ∪ Cbc ⊆ C := by
    intro c hc
    rcases Finset.mem_union.mp hc with hAC | hBC
    · exact (Finset.mem_filter.mp hAC).1
    · exact (Finset.mem_filter.mp hBC).1
  have hADisj : Disjoint Aab Aac := by
    apply Finset.disjoint_left.mpr
    intro a haAB haAC
    have ha := (Finset.mem_filter.mp haAB).1
    have hAB := (Finset.mem_filter.mp haAB).2
    have hAC := (Finset.mem_filter.mp haAC).2
    rcases hPureA a ha with hZero | hZero <;> omega
  have hBDisj : Disjoint Bab Bbc := by
    apply Finset.disjoint_left.mpr
    intro b hbAB hbBC
    have hb := (Finset.mem_filter.mp hbAB).1
    have hAB := (Finset.mem_filter.mp hbAB).2
    have hBC := (Finset.mem_filter.mp hbBC).2
    rcases hPureB b hb with hZero | hZero <;> omega
  have hCDisj : Disjoint Cac Cbc := by
    apply Finset.disjoint_left.mpr
    intro c hcAC hcBC
    have hc := (Finset.mem_filter.mp hcAC).1
    have hAC := (Finset.mem_filter.mp hcAC).2
    have hBC := (Finset.mem_filter.mp hcBC).2
    rcases hPureC c hc with hZero | hZero <;> omega
  have hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ Bab := by
    intro a ha b hb hab
    have hda : 0 < Ζi G.ab B a := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
    have hdb : 0 < Ζf G.ab A b := by
      unfold Ζf
      exact Finset.card_pos.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩,
      Finset.mem_filter.mpr ⟨hb, hdb⟩⟩
  have hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ Cac := by
    intro a ha c hc hac
    have hda : 0 < Ζi G.ac C a := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hc, hac⟩⟩
    have hdc : 0 < Ζf G.ac A c := by
      unfold Ζf
      exact Finset.card_pos.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hac⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩,
      Finset.mem_filter.mpr ⟨hc, hdc⟩⟩
  have hBC : ∀ b ∈ B, ∀ c ∈ C,
      (b, c) ∈ G.bc → b ∈ Bbc ∧ c ∈ Cbc := by
    intro b hb c hc hbc
    have hdb : 0 < Ζi G.bc C b := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hc, hbc⟩⟩
    have hdc : 0 < Ζf G.bc B c := by
      unfold Ζf
      exact Finset.card_pos.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hbc⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨hb, hdb⟩,
      Finset.mem_filter.mpr ⟨hc, hdc⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hABedge
  obtain ⟨a', ha', c, hc, hac⟩ := hACedge
  obtain ⟨b', hb', c', hc', hbc⟩ := hBCedge
  have haAB : 0 < Aab.card :=
    Finset.card_pos.mpr ⟨a, (hAB a ha b hb hab).1⟩
  have hbAB : 0 < Bab.card :=
    Finset.card_pos.mpr ⟨b, (hAB a ha b hb hab).2⟩
  have haAC : 0 < Aac.card :=
    Finset.card_pos.mpr ⟨a', (hAC a' ha' c hc hac).1⟩
  have hcAC : 0 < Cac.card :=
    Finset.card_pos.mpr ⟨c, (hAC a' ha' c hc hac).2⟩
  have hbBC : 0 < Bbc.card :=
    Finset.card_pos.mpr ⟨b', (hBC b' hb' c' hc' hbc).1⟩
  have hcBC : 0 < Cbc.card :=
    Finset.card_pos.mpr ⟨c', (hBC b' hb' c' hc' hbc).2⟩
  exact Ζmx G
    A B C Aab Aac Bab Bbc Cac Cbc
    hA hADisj hB hBDisj hC hCDisj
    hAB hAC hBC haAB haAC hbAB hbBC hcAC hcBC
theorem Ζgj
    (G : Ζs α) (A B C : Finset α)
    (hPureA : ∀ a ∈ A,
      Ζi G.ab B a = 0 ∨ Ζi G.ac C a = 0)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc)
    (hABedge : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab)
    (hACedge : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  let Aab := A.filter fun a => 0 < Ζi G.ab B a
  let Aac := A.filter fun a => 0 < Ζi G.ac C a
  have hA : Aab ∪ Aac ⊆ A := by
    intro a ha
    rcases Finset.mem_union.mp ha with hAB | hAC
    · exact (Finset.mem_filter.mp hAB).1
    · exact (Finset.mem_filter.mp hAC).1
  have hADisj : Disjoint Aab Aac := by
    apply Finset.disjoint_left.mpr
    intro a haAB haAC
    have ha := (Finset.mem_filter.mp haAB).1
    have hAB := (Finset.mem_filter.mp haAB).2
    have hAC := (Finset.mem_filter.mp haAC).2
    rcases hPureA a ha with hZero | hZero <;> omega
  have hAB : ∀ a ∈ A, ∀ b ∈ B,
      (a, b) ∈ G.ab → a ∈ Aab ∧ b ∈ B := by
    intro a ha b hb hab
    have hda : 0 < Ζi G.ab B a := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩, hb⟩
  have hAC : ∀ a ∈ A, ∀ c ∈ C,
      (a, c) ∈ G.ac → a ∈ Aac ∧ c ∈ C := by
    intro a ha c hc hac
    have hda : 0 < Ζi G.ac C a := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨c, Finset.mem_filter.mpr ⟨hc, hac⟩⟩
    exact ⟨Finset.mem_filter.mpr ⟨ha, hda⟩, hc⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hABedge
  obtain ⟨a', ha', c, hc, hac⟩ := hACedge
  have haAB : 0 < Aab.card :=
    Finset.card_pos.mpr ⟨a, (hAB a ha b hb hab).1⟩
  have haAC : 0 < Aac.card :=
    Finset.card_pos.mpr ⟨a', (hAC a' ha' c hc hac).1⟩
  exact Ζnq G
    A B C Aab Aac B C hA hADisj subset_rfl subset_rfl
    hAB hAC hBC haAB haAC
private def Ζqs (G : Ζs α) :
    Ζs α :=
  ⟨Ζbn G.ab, G.bc, G.ac⟩
private def Ζpf (G : Ζs α) :
    Ζs α :=
  ⟨Ζbn G.ac, Ζbn G.bc, G.ab⟩
theorem Ζpg
    (G : Ζs α) (A B C : Finset α)
    (hPureB : ∀ b ∈ B,
      Ζf G.ab A b = 0 ∨ Ζi G.bc C b = 0)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, (a, c) ∉ G.ac)
    (hABedge : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab)
    (hBCedge : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  let G' := Ζqs G
  have hPure : ∀ b ∈ B,
      Ζi G'.ab A b = 0 ∨
        Ζi G'.ac C b = 0 := by
    intro b hb
    simpa [G', Ζqs, Ζi, Ζf,
      Ζgd] using hPureB b hb
  have hAB' : ∃ b ∈ B, ∃ a ∈ A, (b, a) ∈ G'.ab := by
    obtain ⟨a, ha, b, hb, hab⟩ := hABedge
    exact ⟨b, hb, a, ha, (Ζgd G.ab b a).2 hab⟩
  have hAC' : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G'.ac := by
    simpa [G', Ζqs] using hBCedge
  have h := Ζgj G' B A C
    hPure (by simpa [G', Ζqs] using hAC) hAB' hAC'
  have h' :
      Ζa B.card + Ζa A.card +
          Ζa C.card ≤
        Ζy B.card A.card C.card
          (Ζd G.ab A B)
          (Ζd G.bc B C) 0 := by
    simpa [G', Ζqs, Ζcq,
      Ζai
        G.ac A C hAC] using h
  rw [Ζdd B.card A.card C.card
    (Ζd G.ab A B)
    (Ζd G.bc B C) 0] at h'
  rw [Ζai
    G.ac A C hAC]
  convert h' using 1
  ring
theorem Ζph
    (G : Ζs α) (A B C : Finset α)
    (hPureC : ∀ c ∈ C,
      Ζf G.ac A c = 0 ∨ Ζf G.bc B c = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∉ G.ab)
    (hACedge : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac)
    (hBCedge : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  let G' := Ζpf G
  have hPure : ∀ c ∈ C,
      Ζi G'.ab A c = 0 ∨
        Ζi G'.ac B c = 0 := by
    intro c hc
    simpa [G', Ζpf, Ζi, Ζf,
      Ζgd] using hPureC c hc
  have hAB' : ∃ c ∈ C, ∃ a ∈ A, (c, a) ∈ G'.ab := by
    obtain ⟨a, ha, c, hc, hac⟩ := hACedge
    exact ⟨c, hc, a, ha, (Ζgd G.ac c a).2 hac⟩
  have hAC' : ∃ c ∈ C, ∃ b ∈ B, (c, b) ∈ G'.ac := by
    obtain ⟨b, hb, c, hc, hbc⟩ := hBCedge
    exact ⟨c, hc, b, hb, (Ζgd G.bc c b).2 hbc⟩
  have h := Ζgj G' C A B
    hPure (by simpa [G', Ζpf] using hAB) hAB' hAC'
  have h' :
      Ζa C.card + Ζa A.card +
          Ζa B.card ≤
        Ζy C.card A.card B.card
          (Ζd G.ac A C)
          (Ζd G.bc B C) 0 := by
    simpa [G', Ζpf, Ζcq,
      Ζai
        G.ab A B hAB] using h
  rw [Ζdd C.card A.card B.card
    (Ζd G.ac A C)
    (Ζd G.bc B C) 0,
    Ζbj A.card C.card B.card
      (Ζd G.ac A C) 0
      (Ζd G.bc B C)] at h'
  rw [Ζai
    G.ab A B hAB]
  convert h' using 1
  ring
theorem Ζsx
    (G : Ζs α) (A B C : Finset α)
    (hPureA : ∀ a ∈ A,
      Ζi G.ab B a = 0 ∨ Ζi G.ac C a = 0)
    (hPureB : ∀ b ∈ B,
      Ζf G.ab A b = 0 ∨ Ζi G.bc C b = 0)
    (hPureC : ∀ c ∈ C,
      Ζf G.ac A c = 0 ∨ Ζf G.bc B c = 0) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  have noAB (h : ¬ ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab) :
      ∀ a ∈ A, ∀ b ∈ B, (a, b) ∉ G.ab := by
    intro a ha b hb hab
    exact h ⟨a, ha, b, hb, hab⟩
  have noAC (h : ¬ ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac) :
      ∀ a ∈ A, ∀ c ∈ C, (a, c) ∉ G.ac := by
    intro a ha c hc hac
    exact h ⟨a, ha, c, hc, hac⟩
  have noBC (h : ¬ ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc) :
      ∀ b ∈ B, ∀ c ∈ C, (b, c) ∉ G.bc := by
    intro b hb c hc hbc
    exact h ⟨b, hb, c, hc, hbc⟩
  by_cases hAB : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∈ G.ab
  · by_cases hAC : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · exact Ζpe G A B C
          hPureA hPureB hPureC hAB hAC hBC
      · exact Ζgj G A B C
          hPureA (noBC hBC) hAB hAC
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · exact Ζpg G A B C
          hPureB (noAC hAC) hAB hBC
      · exact Ζji G A B C
          (noAC hAC) (noBC hBC)
  · by_cases hAC : ∃ a ∈ A, ∃ c ∈ C, (a, c) ∈ G.ac
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · exact Ζph G A B C
          hPureC (noAB hAB) hAC hBC
      · rw [Ζai
          G.ab A B (noAB hAB),
          Ζai
          G.bc B C (noBC hBC)]
        exact Ζse A.card B.card C.card
          (Ζd G.ac A C)
    · by_cases hBC : ∃ b ∈ B, ∃ c ∈ C, (b, c) ∈ G.bc
      · rw [Ζai
          G.ab A B (noAB hAB),
          Ζai
          G.ac A C (noAC hAC)]
        exact Ζsf A.card B.card C.card
          (Ζd G.bc B C)
      · exact Ζji G A B C
          (noAC hAC) (noBC hBC)
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
def Ζev (G : Ζs α) :
    Ζs α :=
  ⟨G.ac, G.ab, Ζbn G.bc⟩
theorem Ζen
    (G : Ζs α) (A B C : Finset α)
    (hMixed : Ζz G A B C) :
    Ζz (Ζev G) A C B := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha hAC hAB
    have h := hMixed.1 a ha hAB hAC
    exact ⟨h.2, h.1⟩
  · intro c hc hAC hBC
    have hBC' : 0 < Ζf G.bc B c := by
      change 0 < Ζi (Ζbn G.bc) B c at hBC
      rw [Ζcl] at hBC
      exact hBC
    have h := hMixed.2.2 c hc hAC hBC'
    change Ζf G.ac A c = 1 ∧
      Ζi (Ζbn G.bc) B c = 1
    rw [Ζcl]
    exact h
  · intro b hb hAB hBC
    have hBC' : 0 < Ζi G.bc C b := by
      change 0 < Ζf (Ζbn G.bc) C b at hBC
      rw [Ζef] at hBC
      exact hBC
    have h := hMixed.2.1 b hb hAB hBC'
    change Ζf G.ab A b = 1 ∧
      Ζf (Ζbn G.bc) C b = 1
    rw [Ζef]
    exact h
theorem Ζrh
    (G : Ζs α) (A B C : Finset α)
    (hMixed : Ζz G A B C)
    (hPositive :
      Ζa A.card + Ζa C.card <
        Ζd G.ac A C) :
    Ζd G.ab A B +
        Ζd G.bc B C ≤ Ζl B.card := by
  have h := Ζgq
    (Ζev G) A C B
    (Ζen G A B C hMixed) hPositive
  simpa [Ζev, Ζcq, add_comm]
    using h
theorem Ζuj
    (G : Ζs α) (A B C : Finset α)
    (hMixed : Ζz G A B C)
    (hPositive :
      Ζa A.card + Ζa C.card <
        Ζd G.ac A C) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  have h := Ζjm
    (Ζev G) A C B
    (Ζen G A B C hMixed) hPositive
  have h' :
      Ζa A.card + Ζa C.card +
          Ζa B.card ≤
        Ζy A.card C.card B.card
          (Ζd G.ac A C)
          (Ζd G.ab A B)
          (Ζd G.bc B C) := by
    simpa [Ζev, Ζcq] using h
  rw [← Ζbj A.card B.card C.card
    (Ζd G.ab A B)
    (Ζd G.ac A C)
    (Ζd G.bc B C)] at h'
  convert h' using 1
  ring
def Ζhz (G : Ζs α) :
    Ζs α :=
  ⟨G.bc, Ζbn G.ab, Ζbn G.ac⟩
theorem Ζfi
    (G : Ζs α) (A B C : Finset α)
    (hMixed : Ζz G A B C) :
    Ζz (Ζhz G) B C A := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb hBC hBA
    change 0 < Ζi (Ζbn G.ab) A b at hBA
    rw [Ζcl] at hBA
    have h := hMixed.2.1 b hb hBA hBC
    change Ζi G.bc C b = 1 ∧
      Ζi (Ζbn G.ab) A b = 1
    rw [Ζcl]
    exact ⟨h.2, h.1⟩
  · intro c hc hBC hCA
    change 0 < Ζi (Ζbn G.ac) A c at hCA
    rw [Ζcl] at hCA
    have h := hMixed.2.2 c hc hCA hBC
    change Ζf G.bc B c = 1 ∧
      Ζi (Ζbn G.ac) A c = 1
    rw [Ζcl]
    exact ⟨h.2, h.1⟩
  · intro a ha hBA hCA
    change 0 < Ζf (Ζbn G.ab) B a at hBA
    change 0 < Ζf (Ζbn G.ac) C a at hCA
    rw [Ζef] at hBA hCA
    have h := hMixed.1 a ha hBA hCA
    change Ζf (Ζbn G.ab) B a = 1 ∧
      Ζf (Ζbn G.ac) C a = 1
    rw [Ζef, Ζef]
    exact h
theorem Ζuk
    (G : Ζs α) (A B C : Finset α)
    (hMixed : Ζz G A B C)
    (hPositive :
      Ζa B.card + Ζa C.card <
        Ζd G.bc B C) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  have h := Ζjm
    (Ζhz G) B C A
    (Ζfi G A B C hMixed) hPositive
  have h' :
      Ζa B.card + Ζa C.card +
          Ζa A.card ≤
        Ζy B.card C.card A.card
          (Ζd G.bc B C)
          (Ζd G.ab A B)
          (Ζd G.ac A C) := by
    simpa [Ζhz, Ζcq] using h
  have hPay :
      Ζy A.card B.card C.card
          (Ζd G.ab A B)
          (Ζd G.ac A C)
          (Ζd G.bc B C) =
        Ζy B.card C.card A.card
          (Ζd G.bc B C)
          (Ζd G.ab A B)
          (Ζd G.ac A C) := by
    calc
      _ = Ζy B.card A.card C.card
          (Ζd G.ab A B)
          (Ζd G.bc B C)
          (Ζd G.ac A C) :=
        Ζdd _ _ _ _ _ _
      _ = _ := Ζbj _ _ _ _ _ _
  rw [hPay]
  convert h' using 1
  ring
def Ζbm
    (G : Ζs α) (A B C : Finset α) : Prop :=
  Ζa A.card + Ζa B.card +
      Ζa C.card ≤
    Ζy A.card B.card C.card
      (Ζd G.ab A B)
      (Ζd G.ac A C)
      (Ζd G.bc B C)
theorem Ζnr
    (G : Ζs α) (A B C : Finset α) :
    Ζbm (Ζev G) A C B ↔
      Ζbm G A B C := by
  unfold Ζbm
  simp only [Ζev, Ζcq]
  constructor
  · intro h
    rw [← Ζbj A.card B.card C.card
      (Ζd G.ab A B)
      (Ζd G.ac A C)
      (Ζd G.bc B C)] at h
    linarith
  · intro h
    rw [Ζbj A.card B.card C.card
      (Ζd G.ab A B)
      (Ζd G.ac A C)
      (Ζd G.bc B C)] at h
    linarith
theorem Ζgv
    (G : Ζs α) (A B C : Finset α) :
    Ζbm (Ζhz G) B C A ↔
      Ζbm G A B C := by
  unfold Ζbm
  simp only [Ζhz, Ζcq]
  constructor
  · intro h
    rw [← Ζbj B.card A.card C.card
      (Ζd G.ab A B)
      (Ζd G.bc B C)
      (Ζd G.ac A C),
      ← Ζdd A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C)] at h
    linarith
  · intro h
    rw [Ζdd A.card B.card C.card
      (Ζd G.ab A B)
      (Ζd G.ac A C)
      (Ζd G.bc B C),
      Ζbj B.card A.card C.card
        (Ζd G.ab A B)
        (Ζd G.bc B C)
        (Ζd G.ac A C)] at h
    linarith
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
theorem Ζnm
    (G : Finset (α × β)) {A' A : Finset α}
    (hSub : A' ⊆ A) (y : β) :
    Ζf G A' y ≤ Ζf G A y := by
  unfold Ζf
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxA, hxy⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hSub hxA, hxy⟩
theorem Ζdm
    (G : Ζs α)
    {A' A : Finset α} (B C : Finset α)
    (hSub : A' ⊆ A)
    (hMixed : Ζz G A B C) :
    Ζz G A' B C := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha hAB hAC
    exact hMixed.1 a (hSub ha) hAB hAC
  · intro b hb hAB hBC
    have hMono := Ζnm G.ab hSub b
    have hABFull : 0 < Ζf G.ab A b := by omega
    have hFull := hMixed.2.1 b hb hABFull hBC
    exact ⟨by omega, hFull.2⟩
  · intro c hc hAC hBC
    have hMono := Ζnm G.ac hSub c
    have hACFull : 0 < Ζf G.ac A c := by omega
    have hFull := hMixed.2.2 c hc hACFull hBC
    exact ⟨by omega, hFull.2⟩
theorem Ζch
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (v : α) (y : β)
    (hv : v ∈ A) (hy : y ∈ B)
    (hNbr : B.filter (fun z => (v, z) ∈ G) = {y}) :
    Ζd G A B =
      Ζd G (A.erase v) B +
        (Ζl (Ζf G A y) -
          Ζl (Ζf G (A.erase v) y)) := by
  have hLeftOne : Ζi G B v = 1 := by
    simp [Ζi, hNbr]
  have hLeftPhi : Ζl (Ζi G B v) = 0 := by
    rw [hLeftOne]
    exact Ζbe (by omega)
  have hLeft :
      (∑ x ∈ A, Ζl (Ζi G B x)) =
        ∑ x ∈ A.erase v, Ζl (Ζi G B x) := by
    have hSum := Finset.sum_erase_add A
      (fun x => Ζl (Ζi G B x)) hv
    rw [hLeftPhi, add_zero] at hSum
    exact hSum.symm
  have hNoOther (z : β) (hz : z ∈ B.erase y) :
      (v, z) ∉ G := by
    intro hEdgeZ
    have hzB : z ∈ B := (Finset.mem_erase.mp hz).2
    have hzFilter : z ∈ B.filter (fun t => (v, t) ∈ G) :=
      Finset.mem_filter.mpr ⟨hzB, hEdgeZ⟩
    rw [hNbr] at hzFilter
    exact (Finset.mem_erase.mp hz).1 (Finset.mem_singleton.mp hzFilter)
  have hRightOther (z : β) (hz : z ∈ B.erase y) :
      Ζf G A z =
        Ζf G (A.erase v) z := by
    unfold Ζf
    rw [Finset.filter_erase]
    have hvNot : v ∉ A.filter (fun x => (x, z) ∈ G) := by
      simp [hNoOther z hz]
    simp [Finset.erase_eq_of_notMem hvNot]
  have hRight :
      (∑ z ∈ B, Ζl (Ζf G A z)) =
        (∑ z ∈ B, Ζl
          (Ζf G (A.erase v) z)) +
          (Ζl (Ζf G A y) -
            Ζl (Ζf G (A.erase v) y)) := by
    have hSumA := Finset.sum_erase_add B
      (fun z => Ζl (Ζf G A z)) hy
    have hSumErase := Finset.sum_erase_add B
      (fun z => Ζl (Ζf G (A.erase v) z)) hy
    have hOther :
        (∑ z ∈ B.erase y, Ζl (Ζf G A z)) =
          ∑ z ∈ B.erase y,
            Ζl (Ζf G (A.erase v) z) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hRightOther z hz]
    rw [← hSumA, ← hSumErase]
    rw [hOther]
    ring
  unfold Ζd
  rw [hLeft, hRight]
  ring
theorem Ζbw
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (v : α) (y : β)
    (hv : v ∈ A)
    (hNbr : B.filter (fun z => (v, z) ∈ G) = {y}) :
    Ζf G A y =
      Ζf G (A.erase v) y + 1 := by
  have hEdge : (v, y) ∈ G := by
    have hyFilter : y ∈ B.filter (fun z => (v, z) ∈ G) := by
      rw [hNbr]
      simp
    exact (Finset.mem_filter.mp hyFilter).2
  have hvFilter : v ∈ A.filter (fun x => (x, y) ∈ G) :=
    Finset.mem_filter.mpr ⟨hv, hEdge⟩
  unfold Ζf
  rw [Finset.filter_erase]
  exact (Finset.card_erase_add_one hvFilter).symm
theorem Ζld
    (GAB : Finset (α × β)) (GAC : Finset (α × β))
    (A : Finset α) (B C : Finset β)
    (v : α) (y z : β)
    (hv : v ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hNbrAB : B.filter (fun t => (v, t) ∈ GAB) = {y})
    (hNbrAC : C.filter (fun t => (v, t) ∈ GAC) = {z}) :
    Ζd GAB A B +
        Ζd GAC A C ≤
      Ζd GAB (A.erase v) B +
        Ζd GAC (A.erase v) C +
          (Ζa A.card -
            Ζa (A.erase v).card) := by
  let a := (A.erase v).card
  let d₁ := Ζf GAB (A.erase v) y
  let d₂ := Ζf GAC (A.erase v) z
  have hd₁ : d₁ ≤ a :=
    Finset.card_filter_le (A.erase v) (fun x => (x, y) ∈ GAB)
  have hd₂ : d₂ ≤ a :=
    Finset.card_filter_le (A.erase v) (fun x => (x, z) ∈ GAC)
  have hNum := Ζmk
    a d₁ d₂ hd₁ hd₂
  have hCard : A.card = a + 1 := by
    have h := Finset.card_erase_add_one hv
    omega
  have hAB := Ζch
    GAB A B v y hv hy hNbrAB
  have hAC := Ζch
    GAC A C v z hv hz hNbrAC
  rw [Ζbw GAB A B v y hv hNbrAB] at hAB
  rw [Ζbw GAC A C v z hv hNbrAC] at hAC
  rw [hAB, hAC, hCard]
  dsimp [d₁, d₂, a] at hNum ⊢
  linarith
theorem Ζfw
    {γ : Type*} [DecidableEq γ]
    (G₁ : Finset (α × β)) (G₂ : Finset (α × γ))
    (A : Finset α) (B : Finset β) (v : α) (z : γ)
    (hPositive :
      Ζa (A.erase v).card + Ζa B.card <
        Ζd G₁ (A.erase v) B)
    (hLow : ∀ x ∈ A.erase v, (x, z) ∈ G₂ →
      Ζi G₁ B x ≤ 1) :
    Ζf G₂ (A.erase v) z ≤ 1 := by
  by_contra hNot
  have hTwo : 1 < Ζf G₂ (A.erase v) z := by omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hNe⟩ :=
    Finset.one_lt_card.mp hTwo
  have hx₁A : x₁ ∈ A.erase v := (Finset.mem_filter.mp hx₁).1
  have hx₂A : x₂ ∈ A.erase v := (Finset.mem_filter.mp hx₂).1
  have hx₁G : (x₁, z) ∈ G₂ := (Finset.mem_filter.mp hx₁).2
  have hx₂G : (x₂, z) ∈ G₂ := (Finset.mem_filter.mp hx₂).2
  have hEq : (Sum.inl x₁ : Sum α β) = Sum.inl x₂ :=
    Ζdq G₁ (A.erase v) B
      hPositive hx₁A hx₂A
      (hLow x₁ hx₁A hx₁G) (hLow x₂ hx₂A hx₂G)
  exact hNe (Sum.inl.inj hEq)
theorem Ζqa
    (G : Ζs α)
    (A B C : Finset α) (v z : α)
    (hv : v ∈ A) (hz : z ∈ C)
    (hMixed : Ζz G A B C)
    (hNbrAC : C.filter (fun t => (v, t) ∈ G.ac) = {z})
    (hPositiveOld :
      Ζa (A.erase v).card + Ζa B.card <
        Ζd G.ab (A.erase v) B) :
    Ζd G.ac A C =
      Ζd G.ac (A.erase v) C := by
  have hLow : ∀ x ∈ A.erase v, (x, z) ∈ G.ac →
      Ζi G.ab B x ≤ 1 := by
    intro x hx hzEdge
    have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
    have hACpos : 0 < Ζi G.ac C x := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨z, Finset.mem_filter.mpr ⟨hz, hzEdge⟩⟩
    exact Ζfo hMixed hxA hACpos
  have hDegLe := Ζfw
    G.ab G.ac A B v z hPositiveOld hLow
  have hScore := Ζch
    G.ac A C v z hv hz hNbrAC
  rw [Ζbw G.ac A C v z hv hNbrAC]
    at hScore
  have hZero := Ζei hDegLe
  rw [hZero, add_zero] at hScore
  exact hScore
theorem Ζqb
    (G : Ζs α)
    (A B C : Finset α) (v y : α)
    (hv : v ∈ A) (hy : y ∈ B)
    (hMixed : Ζz G A B C)
    (hNbrAB : B.filter (fun t => (v, t) ∈ G.ab) = {y})
    (hPositiveOld :
      Ζa (A.erase v).card + Ζa C.card <
        Ζd G.ac (A.erase v) C) :
    Ζd G.ab A B =
      Ζd G.ab (A.erase v) B := by
  have hLow : ∀ x ∈ A.erase v, (x, y) ∈ G.ab →
      Ζi G.ac C x ≤ 1 := by
    intro x hx hyEdge
    have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
    have hABpos : 0 < Ζi G.ab B x := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨y, Finset.mem_filter.mpr ⟨hy, hyEdge⟩⟩
    by_cases hACzero : Ζi G.ac C x = 0
    · omega
    · have hACpos : 0 < Ζi G.ac C x :=
        Nat.pos_of_ne_zero hACzero
      exact (hMixed.1 x hxA hABpos hACpos).2.le
  have hDegLe := Ζfw
    G.ac G.ab A C v y hPositiveOld hLow
  have hScore := Ζch
    G.ab A B v y hv hy hNbrAB
  rw [Ζbw G.ab A B v y hv hNbrAB]
    at hScore
  have hZero := Ζei hDegLe
  rw [hZero, add_zero] at hScore
  exact hScore
theorem Ζsy
    (G : Ζs α)
    (A B C : Finset α) (v y z : α)
    (hv : v ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hMixed : Ζz G A B C)
    (hNbrAB : B.filter (fun t => (v, t) ∈ G.ab) = {y})
    (hNbrAC : C.filter (fun t => (v, t) ∈ G.ac) = {z})
    (hOld :
      Ζa (A.erase v).card +
          Ζa B.card + Ζa C.card ≤
        Ζy (A.erase v).card B.card C.card
          (Ζd G.ab (A.erase v) B)
          (Ζd G.ac (A.erase v) C)
          (Ζd G.bc B C)) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  let hA := Ζa A.card
  let hA₀ := Ζa (A.erase v).card
  let hB := Ζa B.card
  let hC := Ζa C.card
  let pAB := Ζd G.ab A B
  let pAC := Ζd G.ac A C
  let pBC := Ζd G.bc B C
  let pAB₀ := Ζd G.ab (A.erase v) B
  let pAC₀ := Ζd G.ac (A.erase v) C
  have hMixedOld : Ζz G (A.erase v) B C :=
    Ζdm G B C
      (Finset.erase_subset v A) hMixed
  have hInc : pAB + pAC ≤ pAB₀ + pAC₀ + (hA - hA₀) :=
    Ζld
      G.ab G.ac A B C v y z hv hy hz hNbrAB hNbrAC
  change hA + hB + hC ≤
    Ζy A.card B.card C.card pAB pAC pBC
  by_cases hPAB : hA + hB < pAB
  · exact Ζjm G A B C hMixed hPAB
  by_cases hPAC : hA + hC < pAC
  · exact Ζuj G A B C hMixed hPAC
  by_cases hPBC : hB + hC < pBC
  · exact Ζuk G A B C hMixed hPBC
  have hABBound : pAB ≤ hA + hB := le_of_not_gt hPAB
  have hACBound : pAC ≤ hA + hC := le_of_not_gt hPAC
  have hBCBound : pBC ≤ hB + hC := le_of_not_gt hPBC
  have hTotal : pAB + pAC + pBC ≤ hA + hB + hC := by
    by_cases hOldPAB : hA₀ + hB < pAB₀
    · have hOther : pAC₀ + pBC ≤ Ζl C.card :=
        Ζgq G (A.erase v) B C
          hMixedOld hOldPAB
      have hACeq : pAC = pAC₀ :=
        Ζqa G A B C v z
          hv hz hMixed hNbrAC hOldPAB
      have hPhi := Ζed C.card
      linarith
    by_cases hOldPAC : hA₀ + hC < pAC₀
    · have hOther : pAB₀ + pBC ≤ Ζl B.card :=
        Ζrh G (A.erase v) B C
          hMixedOld hOldPAC
      have hABeq : pAB = pAB₀ :=
        Ζqb G A B C v y
          hv hy hMixed hNbrAB hOldPAC
      have hPhi := Ζed B.card
      linarith
    · have hOldABBound : pAB₀ ≤ hA₀ + hB :=
        le_of_not_gt hOldPAB
      have hOldACBound : pAC₀ ≤ hA₀ + hC :=
        le_of_not_gt hOldPAC
      have hOldTotal : pAB₀ + pAC₀ + pBC ≤ hA₀ + hB + hC := by
        have h := (Ζdb
          (A.erase v).card B.card C.card pAB₀ pAC₀ pBC).mp hOld
        rw [min_eq_left hOldABBound,
          min_eq_left hOldACBound,
          min_eq_left hBCBound] at h
        exact h
      linarith
  apply (Ζdb
    A.card B.card C.card pAB pAC pBC).mpr
  rw [min_eq_left hABBound,
    min_eq_left hACBound,
    min_eq_left hBCBound]
  exact hTotal
theorem Ζft
    (G : Ζs α)
    (A B C : Finset α) (v : α)
    (hv : v ∈ A)
    (hMixed : Ζz G A B C)
    (hAB : 0 < Ζi G.ab B v)
    (hAC : 0 < Ζi G.ac C v)
    (hOld :
      Ζa (A.erase v).card +
          Ζa B.card + Ζa C.card ≤
        Ζy (A.erase v).card B.card C.card
          (Ζd G.ab (A.erase v) B)
          (Ζd G.ac (A.erase v) C)
          (Ζd G.bc B C)) :
    Ζa A.card + Ζa B.card +
        Ζa C.card ≤
      Ζy A.card B.card C.card
        (Ζd G.ab A B)
        (Ζd G.ac A C)
        (Ζd G.bc B C) := by
  obtain ⟨hABOne, hACOne⟩ := hMixed.1 v hv hAB hAC
  obtain ⟨y, hNbrAB⟩ := Finset.card_eq_one.mp hABOne
  obtain ⟨z, hNbrAC⟩ := Finset.card_eq_one.mp hACOne
  have hy : y ∈ B := by
    have hyFilter : y ∈ B.filter (fun t => (v, t) ∈ G.ab) := by
      rw [hNbrAB]
      simp
    exact (Finset.mem_filter.mp hyFilter).1
  have hz : z ∈ C := by
    have hzFilter : z ∈ C.filter (fun t => (v, t) ∈ G.ac) := by
      rw [hNbrAC]
      simp
    exact (Finset.mem_filter.mp hzFilter).1
  exact Ζsy G A B C v y z
    hv hy hz hMixed hNbrAB hNbrAC hOld
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
private theorem Ζsg
    (G : Ζs α) (A B C : Finset α)
    (hNot : ¬ ∀ a ∈ A,
      Ζi G.ab B a = 0 ∨
        Ζi G.ac C a = 0) :
    ∃ a ∈ A, 0 < Ζi G.ab B a ∧
      0 < Ζi G.ac C a := by
  simp only [not_forall, not_or] at hNot
  obtain ⟨a, ha, hAB, hAC⟩ := hNot
  exact ⟨a, ha, Nat.pos_of_ne_zero hAB, Nat.pos_of_ne_zero hAC⟩
private theorem Ζsh :
    ∀ n : ℕ, ∀ (G : Ζs α) (A B C : Finset α),
      A.card + B.card + C.card ≤ n →
      Ζz G A B C →
      Ζbm G A B C := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G A B C hSize hMixed
    by_cases hPureA : ∀ a ∈ A,
        Ζi G.ab B a = 0 ∨
          Ζi G.ac C a = 0
    · by_cases hPureB : ∀ b ∈ B,
          Ζf G.ab A b = 0 ∨
            Ζi G.bc C b = 0
      · by_cases hPureC : ∀ c ∈ C,
            Ζf G.ac A c = 0 ∨
              Ζf G.bc B c = 0
        · exact Ζsx G A B C
            hPureA hPureB hPureC
        · obtain ⟨c, hc, hAC, hBC⟩ := by
            simpa only [not_forall, not_or] using hPureC
          let G' := Ζhz (Ζev G)
          have hMixedSwap : Ζz
              (Ζev G) A C B :=
            Ζen G A B C hMixed
          have hMixed' : Ζz G' C B A :=
            Ζfi
              (Ζev G) A C B hMixedSwap
          have hFirstAB : 0 < Ζi G'.ab B c := by
            change 0 < Ζi (Ζbn G.bc) B c
            rw [Ζcl]
            exact Nat.pos_of_ne_zero hBC
          have hFirstAC : 0 < Ζi G'.ac A c := by
            change 0 < Ζi (Ζbn G.ac) A c
            rw [Ζcl]
            exact Nat.pos_of_ne_zero hAC
          have hMixedOld : Ζz G'
              (C.erase c) B A :=
            Ζdm G' B A
              (Finset.erase_subset c C) hMixed'
          have hLess : (C.erase c).card + B.card + A.card < n := by
            have hCard := Finset.card_erase_add_one hc
            omega
          have hOld : Ζbm G' (C.erase c) B A :=
            ih _ hLess G' (C.erase c) B A le_rfl hMixedOld
          have hNew : Ζbm G' C B A :=
            Ζft G' C B A c
              hc hMixed' hFirstAB hFirstAC hOld
          exact (Ζnr G A B C).mp
            ((Ζgv
              (Ζev G) A C B).mp hNew)
      · obtain ⟨b, hb, hAB, hBC⟩ := by
          simpa only [not_forall, not_or] using hPureB
        let G' := Ζhz G
        have hMixed' : Ζz G' B C A :=
          Ζfi G A B C hMixed
        have hFirstAB : 0 < Ζi G'.ab C b :=
          Nat.pos_of_ne_zero hBC
        have hFirstAC : 0 < Ζi G'.ac A b := by
          change 0 < Ζi (Ζbn G.ab) A b
          rw [Ζcl]
          exact Nat.pos_of_ne_zero hAB
        have hMixedOld : Ζz G'
            (B.erase b) C A :=
          Ζdm G' C A
            (Finset.erase_subset b B) hMixed'
        have hLess : (B.erase b).card + C.card + A.card < n := by
          have hCard := Finset.card_erase_add_one hb
          omega
        have hOld : Ζbm G' (B.erase b) C A :=
          ih _ hLess G' (B.erase b) C A le_rfl hMixedOld
        have hNew : Ζbm G' B C A :=
          Ζft G' B C A b
            hb hMixed' hFirstAB hFirstAC hOld
        exact (Ζgv G A B C).mp hNew
    · obtain ⟨a, ha, hAB, hAC⟩ :=
        Ζsg G A B C hPureA
      have hMixedOld : Ζz G (A.erase a) B C :=
        Ζdm G B C
          (Finset.erase_subset a A) hMixed
      have hLess : (A.erase a).card + B.card + C.card < n := by
        have hCard := Finset.card_erase_add_one ha
        omega
      have hOld : Ζbm G (A.erase a) B C :=
        ih _ hLess G (A.erase a) B C le_rfl hMixedOld
      exact Ζft G A B C a
        ha hMixed hAB hAC hOld
theorem Ζos
    (G : Ζs α) (A B C : Finset α)
    (hMixed : Ζz G A B C) :
    Ζbm G A B C :=
  Ζsh
    (A.card + B.card + C.card) G A B C le_rfl hMixed
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section ActualTripartite
variable {α : Type*} [DecidableEq α]
def Ζn
    (H : Family α) (V : Edge α) (a b c : α) : Edge α :=
  V.filter fun x => x ≠ a ∧ x ≠ b ∧ x ≠ c ∧
    ({b, c, x} : Edge α) ∈ H
def Ζu
    (H : Family α) (V : Edge α) (a b c : α) : Edge α :=
  V.filter fun y => y ≠ a ∧ y ≠ b ∧ y ≠ c ∧
    ({a, c, y} : Edge α) ∈ H
def Ζae
    (H : Family α) (V : Edge α) (a b c : α) : Edge α :=
  V.filter fun z => z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
    ({a, b, z} : Edge α) ∈ H
theorem Ζcd
    {H : Family α} {V : Edge α} {a b c x : α} :
    x ∈ Ζn H V a b c ↔
      x ∈ V ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧
        ({b, c, x} : Edge α) ∈ H := by
  simp [Ζn]
theorem Ζbi
    {H : Family α} {V : Edge α} {a b c y : α} :
    y ∈ Ζu H V a b c ↔
      y ∈ V ∧ y ≠ a ∧ y ≠ b ∧ y ≠ c ∧
        ({a, c, y} : Edge α) ∈ H := by
  simp [Ζu]
theorem Ζdf
    {H : Family α} {V : Edge α} {a b c z : α} :
    z ∈ Ζae H V a b c ↔
      z ∈ V ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
        ({a, b, z} : Edge α) ∈ H := by
  simp [Ζae]
theorem Ζap
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζn H V a b c =
      (Ζb H V ({b, c} : Edge α)).erase a := by
  ext x
  have hEdgeEq : ({b, c} : Edge α) ∪ {x} =
      ({b, c, x} : Edge α) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp only [Ζcd, Finset.mem_erase,
    Ζb, Finset.mem_filter]
  rw [hEdgeEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
theorem Ζbd
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζu H V a b c =
      (Ζb H V ({a, c} : Edge α)).erase b := by
  ext y
  have hEdgeEq : ({a, c} : Edge α) ∪ {y} =
      ({a, c, y} : Edge α) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp only [Ζbi, Finset.mem_erase,
    Ζb, Finset.mem_filter]
  rw [hEdgeEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
theorem Ζcg
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζae H V a b c =
      (Ζb H V ({a, b} : Edge α)).erase c := by
  ext z
  have hEdgeEq : ({a, b} : Edge α) ∪ {z} =
      ({a, b, z} : Edge α) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp only [Ζdf, Finset.mem_erase,
    Ζb, Finset.mem_filter]
  rw [hEdgeEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
def Ζj
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζs α :=
  let A := Ζn H V a b c
  let B := Ζu H V a b c
  let C := Ζae H V a b c
  ⟨(A.product B).filter (fun e =>
      ({c, e.1, e.2} : Edge α) ∈ H),
   (A.product C).filter (fun e =>
      ({b, e.1, e.2} : Edge α) ∈ H),
   (B.product C).filter (fun e =>
      ({a, e.1, e.2} : Edge α) ∈ H)⟩
theorem Ζcc
    {H : Family α} {V : Edge α} {a b c x y : α} :
    (x, y) ∈ (Ζj H V a b c).ab ↔
      x ∈ Ζn H V a b c ∧
      y ∈ Ζu H V a b c ∧
      ({c, x, y} : Edge α) ∈ H := by
  simp only [Ζj, Finset.mem_filter]
  constructor
  · rintro ⟨hxy, hEdge⟩
    exact ⟨(Finset.mem_product.mp hxy).1,
      (Finset.mem_product.mp hxy).2, hEdge⟩
  · rintro ⟨hx, hy, hEdge⟩
    exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hEdge⟩
theorem Ζcy
    {H : Family α} {V : Edge α} {a b c x z : α} :
    (x, z) ∈ (Ζj H V a b c).ac ↔
      x ∈ Ζn H V a b c ∧
      z ∈ Ζae H V a b c ∧
      ({b, x, z} : Edge α) ∈ H := by
  simp only [Ζj, Finset.mem_filter]
  constructor
  · rintro ⟨hxz, hEdge⟩
    exact ⟨(Finset.mem_product.mp hxz).1,
      (Finset.mem_product.mp hxz).2, hEdge⟩
  · rintro ⟨hx, hz, hEdge⟩
    exact ⟨Finset.mem_product.mpr ⟨hx, hz⟩, hEdge⟩
theorem Ζhq
    {H : Family α} {V : Edge α} {a b c y z : α} :
    (y, z) ∈ (Ζj H V a b c).bc ↔
      y ∈ Ζu H V a b c ∧
      z ∈ Ζae H V a b c ∧
      ({a, y, z} : Edge α) ∈ H := by
  simp only [Ζj, Finset.mem_filter]
  constructor
  · rintro ⟨hyz, hEdge⟩
    exact ⟨(Finset.mem_product.mp hyz).1,
      (Finset.mem_product.mp hyz).2, hEdge⟩
  · rintro ⟨hy, hz, hEdge⟩
    exact ⟨Finset.mem_product.mpr ⟨hy, hz⟩, hEdge⟩
theorem Ζia
    {H : Family α} {u v s t y z : α}
    (hH : Admissible H)
    (huv : u ≠ v)
    (hst : s ≠ t)
    (hys : y ≠ s) (hyt : y ≠ t)
    (hzs : z ≠ s) (hzt : z ≠ t)
    (huOut : u ∉ ({s, t, y, z} : Edge α))
    (hvOut : v ∉ ({s, t, y, z} : Edge α))
    (hsyu : ({s, y} : Edge α) ∪ {u} ∈ H)
    (hsyv : ({s, y} : Edge α) ∪ {v} ∈ H)
    (htzu : ({t, z} : Edge α) ∪ {u} ∈ H)
    (htzv : ({t, z} : Edge α) ∪ {v} ∈ H) :
    y = z := by
  by_contra hyz
  have hpq : Disjoint ({s, y} : Edge α) ({t, z} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro w hwP hwQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwP hwQ
    rcases hwP with rfl | rfl <;> rcases hwQ with rfl | rfl
    · exact hst rfl
    · exact hzs rfl
    · exact hyt rfl
    · exact hyz rfl
  have huP : u ∉ ({s, y} : Edge α) := by
    intro h
    exact huOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  have hvP : v ∉ ({s, y} : Edge α) := by
    intro h
    exact hvOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  have huQ : u ∉ ({t, z} : Edge α) := by
    intro h
    exact huOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  have hvQ : v ∉ ({t, z} : Edge α) := by
    intro h
    exact hvOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  exact Ζkn hH huv hpq
    (by simp) (by simp) huP hvP huQ hvQ
    hsyu hsyv htzu htzv
private theorem Ζce
    {H : Family α} {s x y : α}
    (hUniform : Uniform 3 H)
    (hEdge : ({s, x, y} : Edge α) ∈ H)
    (hsx : s ≠ x) :
    x ≠ y := by
  intro hxy
  subst y
  have hCard := hUniform hEdge
  have hEq : ({s, x, x} : Edge α) = ({s, x} : Edge α) := by simp
  rw [hEq, Finset.card_pair hsx] at hCard
  omega
theorem Ζjt
    {H : Family α} {V : Edge α} {a b c x y z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hAB : (x, y) ∈ (Ζj H V a b c).ab)
    (hAC : (x, z) ∈ (Ζj H V a b c).ac) :
    y = z := by
  obtain ⟨hxA, hyB, hCXY⟩ := Ζcc.mp hAB
  obtain ⟨_, hzC, hBXZ⟩ := Ζcy.mp hAC
  obtain ⟨_, hxa, hxb, hxc, _⟩ := Ζcd.mp hxA
  obtain ⟨_, hya, hyb, hyc, hACY⟩ := Ζbi.mp hyB
  obtain ⟨_, hza, hzb, hzc, hABZ⟩ := Ζdf.mp hzC
  have hxy : x ≠ y :=
    Ζce hUniform hCXY hxc.symm
  have hxz : x ≠ z :=
    Ζce hUniform hBXZ hxb.symm
  have haOut : a ∉ ({c, b, y, z} : Edge α) := by
    simp [hac, hab, Ne.symm hya, Ne.symm hza]
  have hxOut : x ∉ ({c, b, y, z} : Edge α) := by
    simp [hxc, hxb, hxy, hxz]
  have hCY_A : ({c, y} : Edge α) ∪ {a} ∈ H := by
    have hEq : ({c, y} : Edge α) ∪ {a} =
        ({a, c, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hACY
  have hCY_X : ({c, y} : Edge α) ∪ {x} ∈ H := by
    have hEq : ({c, y} : Edge α) ∪ {x} =
        ({c, x, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hCXY
  have hBZ_A : ({b, z} : Edge α) ∪ {a} ∈ H := by
    have hEq : ({b, z} : Edge α) ∪ {a} =
        ({a, b, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hABZ
  have hBZ_X : ({b, z} : Edge α) ∪ {x} ∈ H := by
    have hEq : ({b, z} : Edge α) ∪ {x} =
        ({b, x, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBXZ
  exact Ζia hH (Ne.symm hxa)
    hbc.symm hyc hyb hzc hzb haOut hxOut
    hCY_A hCY_X hBZ_A hBZ_X
theorem Ζtw
    {H : Family α} {V : Edge α} {a b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hABpos : 0 < Ζi
      (Ζj H V a b c).ab
      (Ζu H V a b c) x)
    (hACpos : 0 < Ζi
      (Ζj H V a b c).ac
      (Ζae H V a b c) x) :
    Ζi (Ζj H V a b c).ab
        (Ζu H V a b c) x = 1 ∧
      Ζi (Ζj H V a b c).ac
        (Ζae H V a b c) x = 1 := by
  let G := Ζj H V a b c
  let B := Ζu H V a b c
  let C := Ζae H V a b c
  change 0 < (B.filter fun y => (x, y) ∈ G.ab).card at hABpos
  change 0 < (C.filter fun z => (x, z) ∈ G.ac).card at hACpos
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hABpos
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hACpos
  have hAB : (x, y) ∈ G.ab := (Finset.mem_filter.mp hy).2
  have hAC : (x, z) ∈ G.ac := (Finset.mem_filter.mp hz).2
  have hABsub : B.filter (fun y' => (x, y') ∈ G.ab) ⊆
      ({z} : Edge α) := by
    intro y' hy'
    have hAB' : (x, y') ∈ G.ab := (Finset.mem_filter.mp hy').2
    have hy'z := Ζjt
      hH hUniform hab hac hbc hAB' hAC
    exact Finset.mem_singleton.mpr hy'z
  have hACsub : C.filter (fun z' => (x, z') ∈ G.ac) ⊆
      ({y} : Edge α) := by
    intro z' hz'
    have hAC' : (x, z') ∈ G.ac := (Finset.mem_filter.mp hz').2
    have hyz' := Ζjt
      hH hUniform hab hac hbc hAB hAC'
    exact Finset.mem_singleton.mpr hyz'.symm
  have hABle : (B.filter fun y' => (x, y') ∈ G.ab).card ≤ 1 :=
    (Finset.card_le_card hABsub).trans (by simp)
  have hACle : (C.filter fun z' => (x, z') ∈ G.ac).card ≤ 1 :=
    (Finset.card_le_card hACsub).trans (by simp)
  change (B.filter fun y' => (x, y') ∈ G.ab).card = 1 ∧
    (C.filter fun z' => (x, z') ∈ G.ac).card = 1
  constructor <;> omega
theorem Ζqt
    {H : Family α} {V : Edge α} {a b c x y z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hAB : (x, y) ∈ (Ζj H V a b c).ab)
    (hBC : (y, z) ∈ (Ζj H V a b c).bc) :
    z = x := by
  obtain ⟨hxA, hyB, hCXY⟩ := Ζcc.mp hAB
  obtain ⟨_, hzC, hAYZ⟩ := Ζhq.mp hBC
  obtain ⟨_, hxa, hxb, hxc, hBCX⟩ := Ζcd.mp hxA
  obtain ⟨_, hya, hyb, hyc, _⟩ := Ζbi.mp hyB
  obtain ⟨_, hza, hzb, hzc, hABZ⟩ := Ζdf.mp hzC
  have hxy : x ≠ y :=
    Ζce hUniform hCXY hxc.symm
  have hyz : y ≠ z :=
    Ζce hUniform hAYZ hya.symm
  have hbOut : b ∉ ({a, c, z, x} : Edge α) := by
    simp [Ne.symm hab, hbc, Ne.symm hzb, Ne.symm hxb]
  have hyOut : y ∉ ({a, c, z, x} : Edge α) := by
    simp [hya, hyc, hyz, Ne.symm hxy]
  have hAZ_B : ({a, z} : Edge α) ∪ {b} ∈ H := by
    have hEq : ({a, z} : Edge α) ∪ {b} =
        ({a, b, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hABZ
  have hAZ_Y : ({a, z} : Edge α) ∪ {y} ∈ H := by
    have hEq : ({a, z} : Edge α) ∪ {y} =
        ({a, y, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hAYZ
  have hCX_B : ({c, x} : Edge α) ∪ {b} ∈ H := by
    have hEq : ({c, x} : Edge α) ∪ {b} =
        ({b, c, x} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBCX
  have hCX_Y : ({c, x} : Edge α) ∪ {y} ∈ H := by
    have hEq : ({c, x} : Edge α) ∪ {y} =
        ({c, x, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hCXY
  exact Ζia hH (Ne.symm hyb)
    hac hza hzc hxa hxc hbOut hyOut
    hAZ_B hAZ_Y hCX_B hCX_Y
theorem Ζqu
    {H : Family α} {V : Edge α} {a b c x y z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hAC : (x, z) ∈ (Ζj H V a b c).ac)
    (hBC : (y, z) ∈ (Ζj H V a b c).bc) :
    x = y := by
  obtain ⟨hxA, hzC, hBXZ⟩ := Ζcy.mp hAC
  obtain ⟨hyB, _, hAYZ⟩ := Ζhq.mp hBC
  obtain ⟨_, hxa, hxb, hxc, hBCX⟩ := Ζcd.mp hxA
  obtain ⟨_, hya, hyb, hyc, hACY⟩ := Ζbi.mp hyB
  obtain ⟨_, hza, hzb, hzc, _⟩ := Ζdf.mp hzC
  have hxz : x ≠ z :=
    Ζce hUniform hBXZ hxb.symm
  have hyz : y ≠ z :=
    Ζce hUniform hAYZ hya.symm
  have hcOut : c ∉ ({b, a, x, y} : Edge α) := by
    simp [Ne.symm hbc, Ne.symm hac, Ne.symm hxc, Ne.symm hyc]
  have hzOut : z ∉ ({b, a, x, y} : Edge α) := by
    simp [hzb, hza, Ne.symm hxz, Ne.symm hyz]
  have hBX_C : ({b, x} : Edge α) ∪ {c} ∈ H := by
    have hEq : ({b, x} : Edge α) ∪ {c} =
        ({b, c, x} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBCX
  have hBX_Z : ({b, x} : Edge α) ∪ {z} ∈ H := by
    have hEq : ({b, x} : Edge α) ∪ {z} =
        ({b, x, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBXZ
  have hAY_C : ({a, y} : Edge α) ∪ {c} ∈ H := by
    have hEq : ({a, y} : Edge α) ∪ {c} =
        ({a, c, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hACY
  have hAY_Z : ({a, y} : Edge α) ∪ {z} ∈ H := by
    have hEq : ({a, y} : Edge α) ∪ {z} =
        ({a, y, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hAYZ
  exact Ζia hH (Ne.symm hzc)
    hab.symm hxb hxa hyb hya hcOut hzOut
    hBX_C hBX_Z hAY_C hAY_Z
private theorem Ζiw
    (G₁ G₂ : Finset (α × α)) (B C : Edge α) (x : α)
    (h₁ : 0 < Ζi G₁ B x)
    (h₂ : 0 < Ζi G₂ C x)
    (hCross : ∀ y z, (x, y) ∈ G₁ → (x, z) ∈ G₂ → y = z) :
    Ζi G₁ B x = 1 ∧
      Ζi G₂ C x = 1 := by
  change 0 < (B.filter fun y => (x, y) ∈ G₁).card at h₁
  change 0 < (C.filter fun z => (x, z) ∈ G₂).card at h₂
  obtain ⟨y, hy⟩ := Finset.card_pos.mp h₁
  obtain ⟨z, hz⟩ := Finset.card_pos.mp h₂
  have hEdge₁ : (x, y) ∈ G₁ := (Finset.mem_filter.mp hy).2
  have hEdge₂ : (x, z) ∈ G₂ := (Finset.mem_filter.mp hz).2
  have hSub₁ : B.filter (fun y' => (x, y') ∈ G₁) ⊆
      ({z} : Edge α) := by
    intro y' hy'
    exact Finset.mem_singleton.mpr
      (hCross y' z (Finset.mem_filter.mp hy').2 hEdge₂)
  have hSub₂ : C.filter (fun z' => (x, z') ∈ G₂) ⊆
      ({y} : Edge α) := by
    intro z' hz'
    exact Finset.mem_singleton.mpr
      (hCross y z' hEdge₁ (Finset.mem_filter.mp hz').2).symm
  have hLe₁ : (B.filter fun y' => (x, y') ∈ G₁).card ≤ 1 :=
    (Finset.card_le_card hSub₁).trans (by simp)
  have hLe₂ : (C.filter fun z' => (x, z') ∈ G₂).card ≤ 1 :=
    (Finset.card_le_card hSub₂).trans (by simp)
  change (B.filter fun y' => (x, y') ∈ G₁).card = 1 ∧
    (C.filter fun z' => (x, z') ∈ G₂).card = 1
  constructor <;> omega
theorem Ζtx
    {H : Family α} {V : Edge α} {a b c y : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hABpos : 0 < Ζf
      (Ζj H V a b c).ab
      (Ζn H V a b c) y)
    (hBCpos : 0 < Ζi
      (Ζj H V a b c).bc
      (Ζae H V a b c) y) :
    Ζf (Ζj H V a b c).ab
        (Ζn H V a b c) y = 1 ∧
      Ζi (Ζj H V a b c).bc
        (Ζae H V a b c) y = 1 := by
  let G := Ζj H V a b c
  let A := Ζn H V a b c
  let C := Ζae H V a b c
  have hFlipPos : 0 < Ζi (Ζcn G.ab) A y := by
    rw [Ζdt]
    exact hABpos
  have hCross : ∀ z x,
      (y, z) ∈ G.bc →
      (y, x) ∈ Ζcn G.ab → z = x := by
    intro z x hBC hFlip
    have hAB : (x, y) ∈ G.ab :=
      (Ζfs G.ab x y).mp hFlip
    exact Ζqt
      hH hUniform hab hac hbc hAB hBC
  have hPair := Ζiw
    G.bc (Ζcn G.ab) C A y hBCpos hFlipPos hCross
  rw [Ζdt] at hPair
  exact ⟨hPair.2, hPair.1⟩
theorem Ζty
    {H : Family α} {V : Edge α} {a b c z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hACpos : 0 < Ζf
      (Ζj H V a b c).ac
      (Ζn H V a b c) z)
    (hBCpos : 0 < Ζf
      (Ζj H V a b c).bc
      (Ζu H V a b c) z) :
    Ζf (Ζj H V a b c).ac
        (Ζn H V a b c) z = 1 ∧
      Ζf (Ζj H V a b c).bc
        (Ζu H V a b c) z = 1 := by
  let G := Ζj H V a b c
  let A := Ζn H V a b c
  let B := Ζu H V a b c
  have hFlipAC : 0 < Ζi (Ζcn G.ac) A z := by
    rw [Ζdt]
    exact hACpos
  have hFlipBC : 0 < Ζi (Ζcn G.bc) B z := by
    rw [Ζdt]
    exact hBCpos
  have hCross : ∀ x y,
      (z, x) ∈ Ζcn G.ac →
      (z, y) ∈ Ζcn G.bc → x = y := by
    intro x y hFlipACEdge hFlipBCEdge
    have hAC : (x, z) ∈ G.ac :=
      (Ζfs G.ac x z).mp hFlipACEdge
    have hBC : (y, z) ∈ G.bc :=
      (Ζfs G.bc y z).mp hFlipBCEdge
    exact Ζqu
      hH hUniform hab hac hbc hAC hBC
  have hPair := Ζiw
    (Ζcn G.ac) (Ζcn G.bc)
    A B z hFlipAC hFlipBC hCross
  rw [Ζdt, Ζdt] at hPair
  exact hPair
theorem Ζdc
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Ζz (Ζj H V a b c)
      (Ζn H V a b c)
      (Ζu H V a b c)
      (Ζae H V a b c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hAB hAC
    exact Ζtw hH hUniform hab hac hbc hAB hAC
  · intro y hy hAB hBC
    exact Ζtx hH hUniform hab hac hbc hAB hBC
  · intro z hz hAC hBC
    exact Ζty hH hUniform hab hac hbc hAC hBC
theorem Ζvi
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Ζbm
      (Ζj H V a b c)
      (Ζn H V a b c)
      (Ζu H V a b c)
      (Ζae H V a b c) :=
  Ζos
    (Ζj H V a b c)
    (Ζn H V a b c)
    (Ζu H V a b c)
    (Ζae H V a b c)
    (Ζdc
      hH hUniform hab hac hbc)
theorem Ζrv
    {H : Family α} {V : Edge α} {a b c x : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hxA : x ∈ Ζn H V a b c) :
    Ζm H V c a x =
      insert b ((Ζu H V a b c).filter fun y =>
        (x, y) ∈ (Ζj H V a b c).ab) := by
  obtain ⟨_, _, hxb, hxc, hBCX⟩ := Ζcd.mp hxA
  have hbV : b ∈ V := hground _ hE (by simp)
  have hbRoot : b ∈ Ζm H V c a x := by
    apply Finset.mem_filter.mpr
    refine ⟨hbV, hbc, Ne.symm hab, Ne.symm hxb, ?_, ?_⟩
    · have hEq : ({a, b} : Edge α) ∪ {c} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
    · have hEq : ({x, b} : Edge α) ∪ {c} =
          ({b, c, x} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hBCX
  ext t
  constructor
  · intro htRoot
    by_cases htb : t = b
    · subst t
      exact Finset.mem_insert_self b _
    · obtain ⟨htV, htc, hta, htx, hACT, hXCT⟩ :=
        Finset.mem_filter.mp htRoot
      have hACY : ({a, c, t} : Edge α) ∈ H := by
        have hEq : ({a, t} : Edge α) ∪ {c} =
            ({a, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hACT
      have hCXT : ({c, x, t} : Edge α) ∈ H := by
        have hEq : ({x, t} : Edge α) ∪ {c} =
            ({c, x, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hXCT
      have htB : t ∈ Ζu H V a b c :=
        Ζbi.mpr ⟨htV, hta, htb, htc, hACY⟩
      have hAB : (x, t) ∈ (Ζj H V a b c).ab :=
        Ζcc.mpr ⟨hxA, htB, hCXT⟩
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨htB, hAB⟩))
  · intro ht
    rcases Finset.mem_insert.mp ht with htb | htTail
    · exact htb ▸ hbRoot
    · obtain ⟨htB, hAB⟩ := Finset.mem_filter.mp htTail
      obtain ⟨htV, hta, _, htc, hACT⟩ := Ζbi.mp htB
      have hCXT : ({c, x, t} : Edge α) ∈ H :=
        (Ζcc.mp hAB).2.2
      have hxt : x ≠ t :=
        Ζce hUniform hCXT hxc.symm
      apply Finset.mem_filter.mpr
      refine ⟨htV, htc, hta, hxt.symm, ?_, ?_⟩
      · have hEq : ({a, t} : Edge α) ∪ {c} =
            ({a, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hACT
      · have hEq : ({x, t} : Edge α) ∪ {c} =
            ({c, x, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hCXT
theorem Ζri
    {H : Family α} {V : Edge α} {a b c y : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hyB : y ∈ Ζu H V a b c) :
    Ζm H V c b y =
      insert a ((Ζn H V a b c).filter fun x =>
        (x, y) ∈ (Ζj H V a b c).ab) := by
  obtain ⟨_, hya, _, hyc, hACY⟩ := Ζbi.mp hyB
  have haV : a ∈ V := hground _ hE (by simp)
  have haRoot : a ∈ Ζm H V c b y := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, hac, hab, Ne.symm hya, ?_, ?_⟩
    · have hEq : ({b, a} : Edge α) ∪ {c} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
    · have hEq : ({y, a} : Edge α) ∪ {c} =
          ({a, c, y} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hACY
  ext t
  constructor
  · intro htRoot
    by_cases hta : t = a
    · subst t
      exact Finset.mem_insert_self a _
    · obtain ⟨htV, htc, htb, hty, hBCT, hYCT⟩ :=
        Finset.mem_filter.mp htRoot
      have hBCX : ({b, c, t} : Edge α) ∈ H := by
        have hEq : ({b, t} : Edge α) ∪ {c} =
            ({b, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hBCT
      have hCXT : ({c, t, y} : Edge α) ∈ H := by
        have hEq : ({y, t} : Edge α) ∪ {c} =
            ({c, t, y} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hYCT
      have htA : t ∈ Ζn H V a b c :=
        Ζcd.mpr ⟨htV, hta, htb, htc, hBCX⟩
      have hAB : (t, y) ∈ (Ζj H V a b c).ab :=
        Ζcc.mpr ⟨htA, hyB, hCXT⟩
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨htA, hAB⟩))
  · intro ht
    rcases Finset.mem_insert.mp ht with hta | htTail
    · exact hta ▸ haRoot
    · obtain ⟨htA, hAB⟩ := Finset.mem_filter.mp htTail
      obtain ⟨htV, _, htb, htc, hBCT⟩ := Ζcd.mp htA
      have hCTY : ({c, t, y} : Edge α) ∈ H :=
        (Ζcc.mp hAB).2.2
      have hty : t ≠ y :=
        Ζce hUniform hCTY (Ne.symm htc)
      apply Finset.mem_filter.mpr
      refine ⟨htV, htc, htb, hty, ?_, ?_⟩
      · have hEq : ({b, t} : Edge α) ∪ {c} =
            ({b, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hBCT
      · have hEq : ({y, t} : Edge α) ∪ {c} =
            ({c, t, y} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hCTY
theorem Ζnn
    {H : Family α} {V : Edge α} {a b c x : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hxA : x ∈ Ζn H V a b c) :
    Ζg (Ζm H V c a x).card =
      Ζl (Ζi
        (Ζj H V a b c).ab
        (Ζu H V a b c) x) := by
  rw [Ζrv hUniform hground hab hbc hE hxA]
  have hbNot : b ∉
      (Ζu H V a b c).filter
        (fun y => (x, y) ∈ (Ζj H V a b c).ab) := by
    intro hb
    have hbPart := (Finset.mem_filter.mp hb).1
    obtain ⟨_, _, hbb, _, _⟩ := Ζbi.mp hbPart
    exact hbb rfl
  rw [Finset.card_insert_of_notMem hbNot]
  rfl
theorem Ζmy
    {H : Family α} {V : Edge α} {a b c y : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hyB : y ∈ Ζu H V a b c) :
    Ζg (Ζm H V c b y).card =
      Ζl (Ζf
        (Ζj H V a b c).ab
        (Ζn H V a b c) y) := by
  rw [Ζri hUniform hground hab hac hE hyB]
  have haNot : a ∉
      (Ζn H V a b c).filter
        (fun x => (x, y) ∈ (Ζj H V a b c).ab) := by
    intro ha
    have haPart := (Finset.mem_filter.mp ha).1
    obtain ⟨_, haa, _, _, _⟩ := Ζcd.mp haPart
    exact haa rfl
  rw [Finset.card_insert_of_notMem haNot]
  rfl
theorem Ζix
    (H : Family α) (V : Edge α) (a b c : α) :
    (Ζk H V c b).erase a =
      Ζn H V a b c := by
  change (Ζb H V ({c, b} : Edge α)).erase a = _
  have hPair : ({c, b} : Edge α) = ({b, c} : Edge α) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]
  exact (Ζap H V a b c).symm
theorem Ζim
    (H : Family α) (V : Edge α) (a b c : α) :
    (Ζk H V c a).erase b =
      Ζu H V a b c := by
  change (Ζb H V ({c, a} : Edge α)).erase b = _
  have hPair : ({c, a} : Edge α) = ({a, c} : Edge α) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]
  exact (Ζbd H V a b c).symm
theorem Ζqc
    {H : Family α} {V : Edge α} {a b c : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    (Ζk H V c b).card =
      (Ζn H V a b c).card + 1 := by
  have haV : a ∈ V := hground _ hE (by simp)
  have haRoot : a ∈ Ζk H V c b := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, ?_, ?_⟩
    · simp [hac, hab]
    · have hEq : ({c, b} : Edge α) ∪ {a} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
  have hCard := Finset.card_erase_add_one haRoot
  rw [Ζix] at hCard
  exact hCard.symm
theorem Ζpi
    {H : Family α} {V : Edge α} {a b c : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    (Ζk H V c a).card =
      (Ζu H V a b c).card + 1 := by
  have hbV : b ∈ V := hground _ hE (by simp)
  have hbRoot : b ∈ Ζk H V c a := by
    apply Finset.mem_filter.mpr
    refine ⟨hbV, ?_, ?_⟩
    · simp [hab.symm, hbc]
    · have hEq : ({c, a} : Edge α) ∪ {b} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
  have hCard := Finset.card_erase_add_one hbRoot
  rw [Ζim] at hCard
  exact hCard.symm
theorem Ζeb
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζo H V c a b =
      Ζd (Ζj H V a b c).ab
        (Ζn H V a b c)
        (Ζu H V a b c) -
      Ζa (Ζn H V a b c).card -
      Ζa (Ζu H V a b c).card := by
  let A := Ζn H V a b c
  let B := Ζu H V a b c
  let G := Ζj H V a b c
  have hLeftSum :
      (∑ x ∈ A,
        Ζg (Ζm H V c a x).card) =
      ∑ x ∈ A, Ζl (Ζi G.ab B x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact Ζnn
      hUniform hground hab hbc hE hx
  have hRightSum :
      (∑ y ∈ B,
        Ζg (Ζm H V c b y).card) =
      ∑ y ∈ B, Ζl (Ζf G.ab A y) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact Ζmy
      hUniform hground hab hac hE hy
  have hBudgetA : Ζal (Ζk H V c b).card =
      Ζa A.card := by
    rw [Ζqc hground hab hac hE]
    exact (Ζew A.card).symm
  have hBudgetB : Ζal (Ζk H V c a).card =
      Ζa B.card := by
    rw [Ζpi hground hab hbc hE]
    exact (Ζew B.card).symm
  unfold Ζo Ζd
  rw [Ζix,
    Ζim,
    hLeftSum, hRightSum, hBudgetA, hBudgetB]
  ring
private theorem Ζrq
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζn H V a c b = Ζn H V a b c := by
  rw [Ζap,
    Ζap]
  have hPair : ({c, b} : Edge α) = ({b, c} : Edge α) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]
private theorem Ζqv
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζu H V a c b = Ζae H V a b c := by
  rw [Ζbd,
    Ζcg]
private theorem Ζul
    (H : Family α) (V : Edge α) (a b c : α) :
    (Ζj H V a c b).ab =
      (Ζj H V a b c).ac := by
  ext p
  rcases p with ⟨x, z⟩
  rw [Ζcc, Ζcy,
    Ζrq H V a b c,
    Ζqv H V a b c]
private theorem Ζqw
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζn H V b c a = Ζu H V a b c := by
  rw [Ζap,
    Ζbd]
  have hPair : ({c, a} : Edge α) = ({a, c} : Edge α) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]
private theorem Ζqx
    (H : Family α) (V : Edge α) (a b c : α) :
    Ζu H V b c a = Ζae H V a b c := by
  rw [Ζbd,
    Ζcg]
  have hPair : ({b, a} : Edge α) = ({a, b} : Edge α) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]
private theorem Ζum
    (H : Family α) (V : Edge α) (a b c : α) :
    (Ζj H V b c a).ab =
      (Ζj H V a b c).bc := by
  ext p
  rcases p with ⟨y, z⟩
  rw [Ζcc, Ζhq,
    Ζqw H V a b c,
    Ζqx H V a b c]
theorem Ζhr
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζo H V b a c =
      Ζd (Ζj H V a b c).ac
        (Ζn H V a b c)
        (Ζae H V a b c) -
      Ζa (Ζn H V a b c).card -
      Ζa (Ζae H V a b c).card := by
  have hPerm : ({a, c, b} : Edge α) ∈ H := by
    have hEq : ({a, c, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hE
  have hAB := Ζeb
    hUniform hground hac hab hbc.symm hPerm
  rw [Ζrq H V a b c,
    Ζqv H V a b c,
    Ζul H V a b c] at hAB
  exact hAB
theorem Ζhs
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζo H V a b c =
      Ζd (Ζj H V a b c).bc
        (Ζu H V a b c)
        (Ζae H V a b c) -
      Ζa (Ζu H V a b c).card -
      Ζa (Ζae H V a b c).card := by
  have hPerm : ({b, c, a} : Edge α) ∈ H := by
    have hEq : ({b, c, a} : Edge α) = ({a, b, c} : Edge α) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hE
  have hAB := Ζeb
    hUniform hground hbc hab.symm hac.symm hPerm
  rw [Ζqw H V a b c,
    Ζqx H V a b c,
    Ζum H V a b c] at hAB
  exact hAB
theorem Ζqd
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζa (Ζn H V a b c).card +
        Ζa (Ζu H V a b c).card +
        Ζa (Ζae H V a b c).card ≤
      Ζbx H V c a b +
        Ζbx H V b a c +
        Ζbx H V a b c := by
  have hPay := Ζvi
    (V := V) (a := a) (b := b) (c := c)
    hH hUniform hab hac hbc
  have hAB := Ζeb
    hUniform hground hab hac hbc hE
  have hAC := Ζhr
    hUniform hground hab hac hbc hE
  have hBC := Ζhs
    hUniform hground hab hac hbc hE
  unfold Ζbm Ζy at hPay
  unfold Ζbx
  rw [hAB, hAC, hBC]
  convert hPay using 1
  ring_nf
end ActualTripartite
end JSP523.Rank3
end
section
namespace JSP523.Rank3
private theorem Ζvl (r : ℚ) (hr : 3 ≤ r) :
    (r - 2) / (r + 1) +
      6 / ((2 * r - 1) * (2 * r)) +
      6 / (r * (r + 1)) ≤ 1 := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r + 1 := by linarith
  have hr2 : 0 < 2 * r - 1 := by linarith
  have hpoly : 0 ≤ 2 * r * (r - 3) + 1 := by nlinarith
  have hBase : (r - 2) / (r + 1) + 6 / (r * (r + 1)) =
      1 - 3 * (r - 2) / (r * (r + 1)) := by
    field_simp [ne_of_gt hr0, ne_of_gt hr1]
    ring
  have hDen₁ : 0 < (2 * r - 1) * (2 * r) := by
    exact mul_pos hr2 (by linarith)
  have hDen₂ : 0 < r * (r + 1) := mul_pos hr0 hr1
  have hBound : 6 / ((2 * r - 1) * (2 * r)) ≤
      3 * (r - 2) / (r * (r + 1)) := by
    apply (div_le_div_iff₀ hDen₁ hDen₂).mpr
    nlinarith [mul_nonneg hr0.le hpoly]
  linarith only [hBase, hBound]
theorem Ζun
    (a r s : ℕ) (hr : 2 ≤ r) (hrs : r ≤ s)
    (ha : r + s ≤ a) :
    Ζl (r + 1) ≤
      (Ζa (a + 1) - Ζa a) -
      ((Ζl (r + 1) - Ζl r) +
        (Ζl (s + 1) - Ζl s)) := by
  have hs : 2 ≤ s := hr.trans hrs
  rw [Ζlb (by omega : 2 ≤ a),
    Ζmi hr,
    Ζmi hs,
    Ζfa (by omega : 2 ≤ r + 1)]
  push_cast
  have hrq : (3 : ℚ) ≤ (r : ℚ) + 1 := by exact_mod_cast (by omega : 3 ≤ r + 1)
  have hsrq : (r : ℚ) ≤ s := by exact_mod_cast hrs
  have harq : (r : ℚ) + s ≤ a := by exact_mod_cast ha
  let R : ℚ := (r : ℚ) + 1
  have hAden : 0 < ((a : ℚ) + 1) * ((a : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hRden : 0 < ((r : ℚ) + 1) * ((r : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hSden : 0 < ((s : ℚ) + 1) * ((s : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hAmin : (2 * R - 1) * (2 * R) ≤
      ((a : ℚ) + 1) * ((a : ℚ) + 2) := by
    dsimp [R]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (a : ℚ) - 2 * (r : ℚ))
      (by linarith : 0 ≤ (a : ℚ) + 2 * (r : ℚ) + 3)]
  have hSmin : ((r : ℚ) + 1) * ((r : ℚ) + 2) ≤
      ((s : ℚ) + 1) * ((s : ℚ) + 2) := by nlinarith
  have hAminPos : 0 < (2 * R - 1) * (2 * R) := by
    apply mul_pos <;> dsimp [R] <;> linarith
  have hAfrac : 6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) ≤
      6 / ((2 * R - 1) * (2 * R)) := by
    apply (div_le_div_iff₀ hAden hAminPos).mpr
    nlinarith
  have hSfrac : 3 / (((s : ℚ) + 1) * ((s : ℚ) + 2)) ≤
      3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
    apply (div_le_div_iff₀ hSden hRden).mpr
    nlinarith
  have hCore := Ζvl R hrq
  dsimp [R] at hCore hAfrac
  have hCore' : (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
      6 / ((2 * ((r : ℚ) + 1) - 1) * (2 * ((r : ℚ) + 1))) +
      6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) ≤ 1 := by
    convert hCore using 1
    ring
  have hGoal : (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
      6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) +
      3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) +
      3 / (((s : ℚ) + 1) * ((s : ℚ) + 2)) ≤ 1 := by
    have hHalf : 3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) +
        3 / (((s : ℚ) + 1) * ((s : ℚ) + 2)) ≤
        6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
      calc
        _ ≤ 3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) +
            3 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) :=
              add_le_add_right hSfrac _
        _ = _ := by ring
    calc
      _ ≤ (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
          6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) +
          6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
            convert add_le_add_left hHalf
              ((((r : ℚ) - 1) / ((r : ℚ) + 2)) +
                6 / (((a : ℚ) + 1) * ((a : ℚ) + 2))) using 1 <;> ring
      _ ≤ (((r : ℚ) - 1) / ((r : ℚ) + 2)) +
          6 / ((2 * ((r : ℚ) + 1) - 1) * (2 * ((r : ℚ) + 1))) +
          6 / (((r : ℚ) + 1) * ((r : ℚ) + 2)) := by
            convert add_le_add_right
              (add_le_add_left hAfrac (((r : ℚ) - 1) / ((r : ℚ) + 2)))
              (6 / (((r : ℚ) + 1) * ((r : ℚ) + 2))) using 1 <;> ring
      _ ≤ 1 := hCore'
  have hPhiEq : (((r : ℚ) + 1) - 2) / (((r : ℚ) + 1) + 1) =
      (((r : ℚ) - 1) / ((r : ℚ) + 2)) := by ring
  rw [hPhiEq]
  linarith only [hGoal]
def Ζci {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α) : ℚ :=
  Ζy A.card B.card C.card
      (Ζd G.ab A B)
      (Ζd G.ac A C)
      (Ζd G.bc B C) -
    (Ζa A.card + Ζa B.card +
      Ζa C.card)
def Ζjn {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α) : Prop :=
  Ζd G.ab A B ≤
      Ζa A.card + Ζa B.card ∧
  Ζd G.ac A C ≤
      Ζa A.card + Ζa C.card ∧
  Ζd G.bc B C ≤
      Ζa B.card + Ζa C.card
theorem Ζfm
    {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α)
    (h : Ζjn G A B C) :
    Ζci G A B C =
      Ζa A.card + Ζa B.card +
        Ζa C.card -
      (Ζd G.ab A B +
        Ζd G.ac A C +
        Ζd G.bc B C) := by
  obtain ⟨hAB, hAC, hBC⟩ := h
  unfold Ζci Ζy
  rw [max_eq_left (sub_nonneg.mpr hAB),
    max_eq_left (sub_nonneg.mpr hAC),
    max_eq_left (sub_nonneg.mpr hBC)]
  ring
private theorem Ζfu
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (G₁ : Finset (α × β)) (G₂ : Finset (α × γ))
    (A : Finset α) (B : Finset β) (z : γ)
    (hTwo : 2 ≤ Ζf G₂ A z)
    (hLow : ∀ x ∈ A, (x, z) ∈ G₂ → Ζi G₁ B x ≤ 1) :
    Ζd G₁ A B ≤
      Ζa A.card + Ζa B.card := by
  by_contra h
  have hPositive : Ζa A.card + Ζa B.card <
      Ζd G₁ A B := lt_of_not_ge h
  have hOne : 1 < (A.filter (fun x => (x, z) ∈ G₂)).card := by
    dsimp [Ζf] at hTwo
    omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hNe⟩ :=
    Finset.one_lt_card.mp hOne
  have hx₁A : x₁ ∈ A := (Finset.mem_filter.mp hx₁).1
  have hx₂A : x₂ ∈ A := (Finset.mem_filter.mp hx₂).1
  have hx₁G : (x₁, z) ∈ G₂ := (Finset.mem_filter.mp hx₁).2
  have hx₂G : (x₂, z) ∈ G₂ := (Finset.mem_filter.mp hx₂).2
  have hEq : (Sum.inl x₁ : Sum α β) = Sum.inl x₂ :=
    Ζdq G₁ A B hPositive
      hx₁A hx₂A (hLow x₁ hx₁A hx₁G)
      (hLow x₂ hx₂A hx₂G)
  exact hNe (Sum.inl.inj hEq)
theorem Ζhf
    {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α)
    (y z : α)
    (hMixed : Ζz G A B C)
    (hy : y ∈ B) (hz : z ∈ C)
    (hyDegree : 2 ≤ Ζf G.ab A y)
    (hzDegree : 2 ≤ Ζf G.ac A z) :
    Ζjn G A B C := by
  have hAB : Ζd G.ab A B ≤
      Ζa A.card + Ζa B.card := by
    apply Ζfu
      G.ab G.ac A B z hzDegree
    intro x hxA hxAC
    have hPos : 0 < Ζi G.ac C x := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨z, Finset.mem_filter.mpr ⟨hz, hxAC⟩⟩
    exact Ζfo hMixed hxA hPos
  have hAC : Ζd G.ac A C ≤
      Ζa A.card + Ζa C.card := by
    apply Ζfu
      G.ac G.ab A C y hyDegree
    intro x hxA hxAB
    have hABPos : 0 < Ζi G.ab B x := by
      unfold Ζi
      exact Finset.card_pos.mpr
        ⟨y, Finset.mem_filter.mpr ⟨hy, hxAB⟩⟩
    by_cases hACZero : Ζi G.ac C x = 0
    · omega
    · exact (hMixed.1 x hxA hABPos
        (Nat.pos_of_ne_zero hACZero)).2.le
  have hYZero : Ζi G.bc C y = 0 := by
    by_contra hNonzero
    have hOne := (hMixed.2.1 y hy (by omega :
      0 < Ζf G.ab A y)
      (Nat.pos_of_ne_zero hNonzero)).1
    omega
  have hZZero : Ζf G.bc B z = 0 := by
    by_contra hNonzero
    have hOne := (hMixed.2.2 z hz (by omega :
      0 < Ζf G.ac A z)
      (Nat.pos_of_ne_zero hNonzero)).1
    omega
  have hBC := Ζgp
    G.bc B C hy hz (by omega : Ζi G.bc C y ≤ 1)
      (by omega : Ζf G.bc B z ≤ 1)
  exact ⟨hAB, hAC, hBC⟩
theorem Ζmz
    {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α)
    (x y z : α) (r s : ℕ)
    (hMixed : Ζz G A B C)
    (hx : x ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hAB : B.filter (fun t => (x, t) ∈ G.ab) = {y})
    (hAC : C.filter (fun t => (x, t) ∈ G.ac) = {z})
    (hrDegree : Ζf G.ab (A.erase x) y = r)
    (hsDegree : Ζf G.ac (A.erase x) z = s)
    (hr : 2 ≤ r) (hrs : r ≤ s)
    (hSize : r + s ≤ (A.erase x).card) :
    Ζl (r + 1) ≤ Ζci G A B C := by
  have hMixedOld : Ζz G (A.erase x) B C :=
    Ζdm G B C
      (Finset.erase_subset x A) hMixed
  have hABDegree := Ζbw
    G.ab A B x y hx hAB
  have hACDegree := Ζbw
    G.ac A C x z hx hAC
  have hCurrent : Ζjn G A B C :=
    Ζhf G A B C y z
      hMixed hy hz (by rw [hABDegree, hrDegree]; omega)
        (by rw [hACDegree, hsDegree]; omega)
  have hOld : Ζjn G (A.erase x) B C :=
    Ζhf G (A.erase x) B C y z
      hMixedOld hy hz (by rw [hrDegree]; omega)
        (by rw [hsDegree]; omega)
  have hOldPay := Ζos G (A.erase x) B C hMixedOld
  have hOldNonneg : 0 ≤ Ζci G (A.erase x) B C := by
    unfold Ζci
    exact sub_nonneg.mpr hOldPay
  have hABInc := Ζch
    G.ab A B x y hx hy hAB
  rw [hABDegree, hrDegree] at hABInc
  have hACInc := Ζch
    G.ac A C x z hx hz hAC
  rw [hACDegree, hsDegree] at hACInc
  have hCard : A.card = (A.erase x).card + 1 := by
    have h := Finset.card_erase_add_one hx
    omega
  have hGain := Ζun
    (A.erase x).card r s hr hrs hSize
  have hCurrentLinear := Ζfm
    G A B C hCurrent
  have hOldLinear := Ζfm
    G (A.erase x) B C hOld
  rw [hCard] at hCurrentLinear
  linarith only [hOldNonneg, hGain, hCurrentLinear,
    hOldLinear, hABInc, hACInc]
theorem Ζns
    {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α) :
    Ζci (Ζev G) A C B =
      Ζci G A B C := by
  unfold Ζci
  simp only [Ζev, Ζcq]
  rw [Ζbj]
  ring
theorem Ζfv
    {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α)
    (x y z : α) (r s : ℕ)
    (hMixed : Ζz G A B C)
    (hx : x ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hAB : B.filter (fun t => (x, t) ∈ G.ab) = {y})
    (hAC : C.filter (fun t => (x, t) ∈ G.ac) = {z})
    (hrDegree : Ζf G.ab (A.erase x) y = r)
    (hsDegree : Ζf G.ac (A.erase x) z = s)
    (hr : 2 ≤ r) (hrs : r ≤ s)
    (hDisj : Disjoint
      ((A.erase x).filter (fun t => (t, y) ∈ G.ab))
      ((A.erase x).filter (fun t => (t, z) ∈ G.ac))) :
    Ζl (r + 1) ≤ Ζci G A B C := by
  have hSub :
      ((A.erase x).filter (fun t => (t, y) ∈ G.ab)) ∪
        ((A.erase x).filter (fun t => (t, z) ∈ G.ac)) ⊆
        A.erase x :=
    Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  have hCard := Finset.card_le_card hSub
  rw [Finset.card_union_of_disjoint hDisj] at hCard
  have hSize : r + s ≤ (A.erase x).card := by
    change Ζf G.ab (A.erase x) y +
      Ζf G.ac (A.erase x) z ≤ (A.erase x).card at hCard
    rw [hrDegree, hsDegree] at hCard
    exact hCard
  exact Ζmz
    G A B C x y z r s hMixed hx hy hz hAB hAC
      hrDegree hsDegree hr hrs hSize
theorem Ζtz
    {α : Type*} [DecidableEq α]
    (G : Ζs α) (A B C : Finset α)
    (x y z : α) (r s : ℕ)
    (hMixed : Ζz G A B C)
    (hx : x ∈ A) (hy : y ∈ B) (hz : z ∈ C)
    (hAB : B.filter (fun t => (x, t) ∈ G.ab) = {y})
    (hAC : C.filter (fun t => (x, t) ∈ G.ac) = {z})
    (hrDegree : Ζf G.ab (A.erase x) y = r)
    (hsDegree : Ζf G.ac (A.erase x) z = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hDisj : Disjoint
      ((A.erase x).filter (fun t => (t, y) ∈ G.ab))
      ((A.erase x).filter (fun t => (t, z) ∈ G.ac))) :
    min (Ζl (r + 1)) (Ζl (s + 1)) ≤
      Ζci G A B C := by
  by_cases hrs : r ≤ s
  · rw [min_eq_left (Ζdl (by omega : r + 1 ≤ s + 1))]
    exact Ζfv
      G A B C x y z r s hMixed hx hy hz hAB hAC
        hrDegree hsDegree hr hrs hDisj
  · have hsr : s ≤ r := by omega
    have hMixedSwap := Ζen G A B C hMixed
    have hSwap := Ζfv
      (Ζev G) A C B x z y s r hMixedSwap hx hz hy
        hAC hAB hsDegree hrDegree hs hsr hDisj.symm
    rw [Ζns] at hSwap
    rw [min_eq_right (Ζdl (by omega : s + 1 ≤ r + 1))]
    exact hSwap
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
private theorem Ζnz
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b} : Edge α) ≠ {a, c} ∧
      ({a, b} : Edge α) ≠ {b, c} ∧
      ({a, c} : Edge α) ≠ {b, c} := by
  constructor
  · intro h
    have hb : b ∈ ({a, c} : Edge α) := by rw [← h]; simp
    simp [hab.symm, hbc] at hb
  constructor
  · intro h
    have ha : a ∈ ({b, c} : Edge α) := by rw [← h]; simp
    simp [hab, hac] at ha
  · intro h
    have ha : a ∈ ({b, c} : Edge α) := by rw [← h]; simp
    simp [hab, hac] at ha
private theorem Ζuw
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Edge α).powersetCard 2 =
      ({{a, b}, {a, c}, {b, c}} : Family α) := by
  classical
  have hSub :
      ({{a, b}, {a, c}, {b, c}} : Family α) ⊆
        ({a, b, c} : Edge α).powersetCard 2 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Finset.mem_powersetCard.mpr
        ⟨by simp, Finset.card_pair hab⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨by simp, Finset.card_pair hac⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨by simp, Finset.card_pair hbc⟩
  have hTriple : ({a, b, c} : Edge α).card = 3 := by
    simp [hab, hac, hbc]
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    Ζnz a b c hab hac hbc
  have hRight :
      ({{a, b}, {a, c}, {b, c}} : Family α).card = 3 := by
    simp [hABAC, hABBC, hACBC]
  symm
  apply Finset.eq_of_subset_of_card_le hSub
  rw [hRight, Finset.card_powersetCard, hTriple]
  norm_num
private theorem Ζto
    (H : Family α) (V : Edge α) (z x y : α) :
    Ζbx H V z x y =
      Ζbx H V z y x := by
  unfold Ζbx
  rw [Ζfk]
private theorem Ζjz
    (H : Family α) (V : Edge α) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Ζdv H V ({a, b, c} : Edge α) / 2 =
      Ζbx H V a b c +
        Ζbx H V b a c +
        Ζbx H V c a b := by
  have hEraseBC : (({a, b, c} : Edge α).erase b).erase c = {a} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxc, hxb, hxa | hxb' | hxc'⟩
      · exact hxa
      · exact False.elim (hxb hxb')
      · exact False.elim (hxc hxc')
    · intro hxa
      subst x
      exact ⟨hac, hab, Or.inl rfl⟩
  simp [Ζdv, hab, hac, hbc,
    Finset.sum_insert, hEraseBC, Ζto]
  ring_nf
private theorem Ζfb
    (H : Family α) (V p : Edge α) (x : α)
    (hx : x ∈ Ζb H V p) :
    Ζal (Ζb H V p).card =
      Ζa ((Ζb H V p).erase x).card := by
  have hCard := Finset.card_erase_add_one hx
  rw [show (Ζb H V p).card =
    ((Ζb H V p).erase x).card + 1 by omega]
  exact (Ζew _).symm
private theorem Ζrw
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζal
        (Ζb H V ({b, c} : Edge α)).card =
      Ζa (Ζn H V a b c).card := by
  have haV : a ∈ V := hground _ hE (by simp)
  have haComp : a ∈ Ζb H V ({b, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, ?_, ?_⟩
    · simp [hab, hac]
    · have hEq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      rw [hEq]
      exact hE
  have h := Ζfb
    H V ({b, c} : Edge α) a haComp
  rw [← Ζap H V a b c]
    at h
  exact h
private theorem Ζrx
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζal
        (Ζb H V ({a, c} : Edge α)).card =
      Ζa (Ζu H V a b c).card := by
  have hbV : b ∈ V := hground _ hE (by simp)
  have hbComp : b ∈ Ζb H V ({a, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨hbV, ?_, ?_⟩
    · simp [hab.symm, hbc]
    · have hEq : ({a, c} : Edge α) ∪ {b} = {a, b, c} := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      rw [hEq]
      exact hE
  have h := Ζfb
    H V ({a, c} : Edge α) b hbComp
  rw [← Ζbd H V a b c]
    at h
  exact h
private theorem Ζry
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζal
        (Ζb H V ({a, b} : Edge α)).card =
      Ζa (Ζae H V a b c).card := by
  have hcV : c ∈ V := hground _ hE (by simp)
  have hcComp : c ∈ Ζb H V ({a, b} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨hcV, ?_, ?_⟩
    · simp [hac.symm, hbc.symm]
    · have hEq : ({a, b} : Edge α) ∪ {c} = {a, b, c} := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      rw [hEq]
      exact hE
  have h := Ζfb
    H V ({a, b} : Edge α) c hcComp
  rw [← Ζcg H V a b c]
    at h
  exact h
private theorem Ζgw
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    (∑ p ∈ ({a, b, c} : Edge α).powersetCard 2,
      Ζal (Ζb H V p).card) =
      Ζa (Ζn H V a b c).card +
        Ζa (Ζu H V a b c).card +
        Ζa (Ζae H V a b c).card := by
  rw [Ζuw a b c hab hac hbc]
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    Ζnz a b c hab hac hbc
  have hAB :
      Ζal
          (Ζb H V ({a, b} : Edge α)).card =
        Ζa (Ζae H V a b c).card :=
    Ζry H V a b c hground hac hbc hE
  have hAC :
      Ζal
          (Ζb H V ({a, c} : Edge α)).card =
        Ζa (Ζu H V a b c).card :=
    Ζrx H V a b c hground hab hbc hE
  have hBC :
      Ζal
          (Ζb H V ({b, c} : Edge α)).card =
        Ζa (Ζn H V a b c).card :=
    Ζrw H V a b c hground hab hac hE
  simp [hABAC, hABBC, hACBC, hAB, hAC, hBC]
  ring
theorem Ζot
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    Ζax H V ({a, b, c} : Edge α) =
      Ζci (Ζj H V a b c)
        (Ζn H V a b c)
        (Ζu H V a b c)
        (Ζae H V a b c) := by
  have hOrient := Ζjz
    H V a b c hab hac hbc
  have hBudget := Ζgw
    H V a b c hground hab hac hbc hE
  have hAB := Ζeb
    hUniform hground hab hac hbc hE
  have hAC := Ζhr
    hUniform hground hab hac hbc hE
  have hBC := Ζhs
    hUniform hground hab hac hbc hE
  unfold Ζax Ζci
  rw [hOrient, hBudget]
  unfold Ζbx
  rw [hAB, hAC, hBC]
  unfold Ζy
  ring_nf
theorem Ζna
    {H : Family α} {V : Edge α} {a b c x y z : α}
    {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hx : x ∈ Ζn H V a b c)
    (hy : y ∈ Ζu H V a b c)
    (hz : z ∈ Ζae H V a b c)
    (hAB : (Ζu H V a b c).filter
      (fun t => (x, t) ∈ (Ζj H V a b c).ab) = {y})
    (hAC : (Ζae H V a b c).filter
      (fun t => (x, t) ∈ (Ζj H V a b c).ac) = {z})
    (hrDegree : Ζf (Ζj H V a b c).ab
      ((Ζn H V a b c).erase x) y = r)
    (hsDegree : Ζf (Ζj H V a b c).ac
      ((Ζn H V a b c).erase x) z = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hDisj : Disjoint
      (((Ζn H V a b c).erase x).filter
        (fun t => (t, y) ∈ (Ζj H V a b c).ab))
      (((Ζn H V a b c).erase x).filter
        (fun t => (t, z) ∈ (Ζj H V a b c).ac))) :
    min (Ζl (r + 1)) (Ζl (s + 1)) ≤
      Ζax H V ({a, b, c} : Edge α) := by
  rw [Ζot hUniform hground
    hab hac hbc hE]
  exact Ζtz
    (Ζj H V a b c)
    (Ζn H V a b c)
    (Ζu H V a b c)
    (Ζae H V a b c)
    x y z r s
    (Ζdc
      hH hUniform hab hac hbc)
    hx hy hz hAB hAC hrDegree hsDegree hr hs hDisj
theorem Ζkk
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    0 ≤ Ζax H V ({a, b, c} : Edge α) := by
  have hPay := Ζqd
    hH hUniform hground hab hac hbc hE
  have hOrient := Ζjz
    H V a b c hab hac hbc
  have hBudget := Ζgw
    H V a b c hground hab hac hbc hE
  unfold Ζax
  rw [hOrient, hBudget]
  linarith
theorem Ζua
    {H : Family α} {V : Edge α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    {E : Edge α} (hE : E ∈ H) :
    0 ≤ Ζax H V E := by
  obtain ⟨a, b, c, hab, hac, hbc, hEq⟩ :=
    Finset.card_eq_three.mp (hUniform hE)
  rw [hEq]
  exact Ζkk
    hH hUniform hground hab hac hbc (hEq ▸ hE)
end JSP523.Rank3
end
section
namespace JSP523.Rank3
theorem Ζrj
    (h₁ h₂ : ℕ) (hh₁ : h₁ ≤ 2) (hh₂ : h₂ ≤ 2) :
    (h₁ : ℚ) * (2 - 2 * (h₂ : ℚ) / 3) +
      (h₂ : ℚ) * (2 - 2 * (h₁ : ℚ) / 3) ≤ 4 := by
  interval_cases h₁ <;> interval_cases h₂ <;> norm_num
theorem Ζsz
    (a b c d : ℚ)
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c) (hd₀ : 0 ≤ d)
    (ha₁ : a ≤ 1) (hb₁ : b ≤ 1) (hc₁ : c ≤ 1) (hd₁ : d ≤ 1) :
    max (a + b + c + d - 2) 0 ≤ min a b + min c d := by
  have hAB : a + b - 1 ≤ min a b :=
    le_min (by linarith) (by linarith)
  have hCD : c + d - 1 ≤ min c d :=
    le_min (by linarith) (by linarith)
  have hNonneg : 0 ≤ min a b + min c d := by
    have hMinAB : 0 ≤ min a b := le_min ha₀ hb₀
    have hMinCD : 0 ≤ min c d := le_min hc₀ hd₀
    linarith
  exact max_le_iff.mpr ⟨by linarith, hNonneg⟩
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section ReceiverCapacity
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 300000 in
def Ζh (H : Family α) (V : Edge α) (z x y v : α) : ℚ :=
  if v ∈ (Ζb H V ({x, y} : Edge α)).erase z then
    Ζao H V z x y else 0
set_option maxHeartbeats 300000 in
noncomputable def Ζcf (p : Edge α) (hp : p.card = 2) : α × α :=
  Classical.choose (show ∃ e : α × α, e.1 ≠ e.2 ∧ p = ({e.1, e.2} : Edge α) from by
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp
    exact ⟨(x, y), hxy, rfl⟩)
set_option maxHeartbeats 300000 in
theorem Ζbq (p : Edge α) (hp : p.card = 2) :
    (Ζcf p hp).1 ≠ (Ζcf p hp).2 ∧
      p = ({(Ζcf p hp).1, (Ζcf p hp).2} : Edge α) :=
  Classical.choose_spec (show ∃ e : α × α, e.1 ≠ e.2 ∧
    p = ({e.1, e.2} : Edge α) from by
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp
      exact ⟨(x, y), hxy, rfl⟩)
set_option maxHeartbeats 300000 in
noncomputable def Ζw
    (H : Family α) (V : Edge α) (z v : α) (p : Edge α) : ℚ := by
  classical
  by_cases hp : p.card = 2
  · let e := Ζcf p hp
    exact Ζh H V z e.1 e.2 v
  · exact 0
set_option maxHeartbeats 300000 in
noncomputable def Ζea
    (H : Family α) (V : Edge α) (z v : α) (p : Edge α) : ℚ := by
  classical
  exact if hp : p ∈ Ζaf H V z then
    if hv : v ∈ (Ζb H V p).erase z then
      Ζw H V z v p
    else 0
  else 0
set_option maxHeartbeats 300000 in
noncomputable def Ζez
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ p ∈ Ζaf H V z, ∑ v ∈ V.erase z,
    Ζea H V z v p
set_option maxHeartbeats 300000 in
noncomputable def Ζhp
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ v ∈ V.erase z, ∑ p ∈ Ζaf H V z,
    Ζea H V z v p
set_option maxHeartbeats 300000 in
theorem Ζuo
    (H : Family α) (V : Edge α) :
    Ζez H V = Ζhp H V := by
  classical
  unfold Ζez Ζhp
  apply Finset.sum_congr rfl
  intro z hz
  exact Finset.sum_comm
set_option maxHeartbeats 300000 in
theorem Ζlr
    (H : Family α) (V : Edge α) {z x y : α}
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y) :
    Ζq H V z x y < 2 := by
  have hlt := Ζtn H V hsource hxy
  by_cases hnonpos : Ζo H V z x y ≤ 0
  · simp [Ζq, max_eq_right hnonpos]
  · have hpos : 0 < Ζo H V z x y := lt_of_not_ge hnonpos
    simpa [Ζq, max_eq_left (le_of_lt hpos)] using hlt
set_option maxHeartbeats 300000 in
theorem Ζtp
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hpositive : 0 < Ζq H V z x y) :
    (Ζc H V ({z, v} : Edge α)).card ≤ 2 :=
  Ζoq hH hzV hsource hxy hv hpositive
set_option maxHeartbeats 300000 in
theorem Ζsi
    (H : Family α) (V : Edge α) {z v x y : α}
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hdegree : 2 ≤ (Ζb H V ({x, y} : Edge α)).card) :
    Ζh H V z x y v ≤ Ζq H V z x y := by
  have hvN : v ∈ Ζb H V ({x, y} : Edge α) :=
    (Finset.mem_erase.mp hv).2
  have hcharge := Ζao H V z x y
  have hden : 1 ≤
      (Ζb H V ({x, y} : Edge α)).card - 1 := by omega
  have hdenQ : (1 : ℚ) ≤
      ((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1 := by
    have hcast : (2 : ℚ) ≤
        (Ζb H V ({x, y} : Edge α)).card := by
      exact_mod_cast hdegree
    linarith
  have hpos : 0 ≤ Ζq H V z x y := by
    unfold Ζq
    exact le_max_right _ _
  have hdiv : Ζao H V z x y ≤
      Ζq H V z x y := by
    unfold Ζao
    apply (div_le_iff₀ (by linarith :
      0 < ((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1)).mpr
    nlinarith
  simp [Ζh, hv]
  exact hdiv
set_option maxHeartbeats 300000 in
theorem Ζsj
    (H : Family α) (V : Edge α) {z v x y : α}
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hdegree : 2 ≤ (Ζb H V ({x, y} : Edge α)).card) :
    Ζh H V z x y v < 2 := by
  have hle := Ζsi H V hv hdegree
  have hweight := Ζlr H V hsource hxy
  exact lt_of_le_of_lt hle hweight
set_option maxHeartbeats 300000 in
theorem Ζqe (d : ℕ) (hd : 2 ≤ d) :
    1 / ((d : ℚ) - 1) ≤ if 4 ≤ d then (1 : ℚ) / 3 else 1 := by
  by_cases hhigh : 4 ≤ d
  · simp [hhigh]
    have hcast : (4 : ℚ) ≤ d := by exact_mod_cast hhigh
    have hden : (3 : ℚ) ≤ (d : ℚ) - 1 := by linarith
    exact (inv_le_inv₀ (by linarith : (0 : ℚ) < (d : ℚ) - 1)
      (by norm_num : (0 : ℚ) < 3)).2 hden
  · have hlow : d = 2 ∨ d = 3 := by omega
    rcases hlow with h | h
    · subst d
      norm_num
    · subst d
      norm_num
set_option maxHeartbeats 300000 in
theorem Ζnb
    (H : Family α) (V : Edge α) {z v x y : α}
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hlow : (Ζb H V ({z, x} : Edge α)).card < 4) :
    Ζh H V z x y v = 0 := by
  have hxy : x ≠ y := Finset.card_pair_eq_two_iff.mp
    ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hsource).1).2)
  have hnonpos : Ζo H V z x y ≤ 0 := by
    by_contra h
    have hpos : 0 < Ζo H V z x y := lt_of_not_ge h
    have hhigh := Ζmf H V
      hsource hxy hpos
    have hdeg : 4 ≤ (Ζb H V ({z, x} : Edge α)).card := hhigh.1
    omega
  have hzero : Ζq H V z x y = 0 := by
    simp [Ζq, max_eq_right hnonpos]
  simp [Ζh, hv, Ζao, hzero]
set_option maxHeartbeats 300000 in
theorem Ζdg
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H) (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hdouble : (Ζc H V ({z, v} : Edge α)).card = 2) :
    Ζh H V z x y v <
      1 / (((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1) := by
  let N := Ζb H V ({x, y} : Edge α)
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hvV : v ∈ V := (Finset.mem_filter.mp hvN).1
  have hzN : z ∈ N := Ζv H V hzV hsource
  have hpair : ({z, v} : Edge α) ⊆ N := by
    intro t ht
    rcases Finset.mem_insert.mp ht with htz | htv
    · exact htz ▸ hzN
    · exact (Finset.mem_singleton.mp htv) ▸ hvN
  have hdegree : 2 ≤ N.card := by
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hsourceLink := Ζhd H V hsource hvN
  have heq : Ζc H V ({z, v} : Edge α) =
      Ζe H V z v := by
    ext p
    exact Ζr H V hzv p
  have hdoubleOrient : (Ζe H V z v).card = 2 := by
    rw [← heq]
    exact hdouble
  have hweight := Ζfd
    hH hzV hvV hzv hxy hsourceLink hdoubleOrient
  have hpositive : Ζq H V z x y < 1 := by
    by_cases hw : Ζo H V z x y ≤ 0
    · simp [Ζq, max_eq_right hw]
    · have hwpos : 0 < Ζo H V z x y := lt_of_not_ge hw
      simpa [Ζq, max_eq_left (le_of_lt hwpos)] using hweight
  have hden : 0 < (N.card : ℚ) - 1 := by
    have hc : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  have hdiv := div_lt_div_of_pos_right hpositive hden
  have hcharge : Ζh H V z x y v =
      Ζq H V z x y / ((N.card : ℚ) - 1) := by
    simp [Ζh, Ζao, hv, N]
  rw [hcharge]
  exact hdiv
set_option maxHeartbeats 300000 in
theorem Ζaz
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H) (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hdouble : (Ζc H V ({z, v} : Edge α)).card = 2) :
    Ζh H V z x y v ≤
      (if 4 ≤ (Ζb H V ({z, x} : Edge α)).card then
        if 4 ≤ (Ζb H V ({x, y} : Edge α)).card then
          (1 : ℚ) / 3 else 1 else 0) := by
  let N := Ζb H V ({x, y} : Edge α)
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hzN : z ∈ N := Ζv H V hzV hsource
  have hpair : ({z, v} : Edge α) ⊆ N := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzN
    · exact (Finset.mem_singleton.mp hav) ▸ hvN
  have hdegree : 2 ≤ N.card := by
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hchargeInv := Ζdg
    hH hzV hsource hxy hv hdouble
  by_cases hroot : 4 ≤ (Ζb H V ({z, x} : Edge α)).card
  · have hInv := Ζqe N.card hdegree
    have hInv' : 1 / ((N.card : ℚ) - 1) ≤
        if 4 ≤ N.card then (1 : ℚ) / 3 else 1 := hInv
    have hle := (le_of_lt hchargeInv).trans hInv'
    simpa [hroot, N] using hle
  · have hzero := Ζnb
      H V hsource hv (by omega :
        (Ζb H V ({z, x} : Edge α)).card < 4)
    simp [hzero, hroot]
set_option maxHeartbeats 300000 in
theorem Ζhl
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z)
    (hdouble : (Ζc H V ({z, v} : Edge α)).card = 2) :
    Ζh H V z x y v < 1 := by
  have hlt := Ζrg
    hH hzV hsource hxy hv hdouble
  simp [Ζh, hv]
  exact hlt
set_option maxHeartbeats 300000 in
theorem Ζqy
    (H : Family α) (V : Edge α) {z x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hdegree : 2 ≤ (Ζb H V ({x, y} : Edge α)).card) :
    (∑ v ∈ (Ζb H V ({x, y} : Edge α)).erase z,
      Ζh H V z x y v) =
      Ζq H V z x y := by
  have heq :
      (∑ v ∈ (Ζb H V ({x, y} : Edge α)).erase z,
        Ζh H V z x y v) =
      ∑ v ∈ (Ζb H V ({x, y} : Edge α)).erase z,
        Ζao H V z x y := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [Ζh, hv]
  rw [heq]
  exact Ζth H V hzV hsource hdegree
set_option maxHeartbeats 300000 in
theorem Ζam
    {H : Family α} {V p : Edge α} {z v : α}
    (_hzv : z ≠ v)
    (hp : p ∈ Ζc H V ({z, v} : Edge α)) :
    p ∈ Ζaf H V z ∧ p ∈ Ζaf H V v := by
  obtain ⟨hpV, a, ha, b, hb, hab, hpq, hpa, hpb⟩ :=
    Finset.mem_filter.mp hp
  have ha' : a = z ∨ a = v := by
    simpa using ha
  have hb' : b = z ∨ b = v := by
    simpa using hb
  have hza : z ∉ p := by
    intro hzp
    have hmeet := (Finset.disjoint_left.mp hpq) hzp (by simp)
    exact hmeet
  have hva : v ∉ p := by
    intro hvp
    have hmeet := (Finset.disjoint_left.mp hpq) hvp (by simp)
    exact hmeet
  have hpz : p ∪ {z} ∈ H := by
    rcases ha' with haZ | haV
    · simpa [haZ] using hpa
    · rcases hb' with hbZ | hbV
      · simpa [hbZ] using hpb
      · exact False.elim (hab (haV.trans hbV.symm))
  have hpv : p ∪ {v} ∈ H := by
    rcases ha' with haZ | haV
    · rcases hb' with hbZ | hbV
      · exact False.elim (hab (haZ.trans hbZ.symm))
      · simpa [hbV] using hpb
    · simpa [haV] using hpa
  exact ⟨Finset.mem_filter.mpr ⟨hpV, hza, hpz⟩,
    Finset.mem_filter.mpr ⟨hpV, hva, hpv⟩⟩
set_option maxHeartbeats 300000 in
theorem Ζqz
    (H : Family α) (V : Edge α) {z v x y : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v) (hxy : x ≠ y)
    (hsourceZ : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hsourceV : ({x, y} : Edge α) ∈ Ζaf H V v) :
    Ζh H V z x y v +
      Ζh H V v x y z < 4 := by
  have hvComp : v ∈ Ζb H V ({x, y} : Edge α) :=
    Ζv H V hvV hsourceV
  have hzComp : z ∈ Ζb H V ({x, y} : Edge α) :=
    Ζv H V hzV hsourceZ
  have hvErase : v ∈ (Ζb H V ({x, y} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv, hvComp⟩
  have hzErase : z ∈ (Ζb H V ({x, y} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, hzComp⟩
  have hdeg : 2 ≤ (Ζb H V ({x, y} : Edge α)).card := by
    have hp : ({z, v} : Edge α) ⊆ Ζb H V ({x, y} : Edge α) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with h | h
      · exact h ▸ hzComp
      · exact (Finset.mem_singleton.mp h) ▸ hvComp
    have hc := Finset.card_le_card hp
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hfirst := Ζsj H V hsourceZ hxy hvErase hdeg
  have hsecond := Ζsj H V hsourceV hxy hzErase hdeg
  linarith
set_option maxHeartbeats 300000 in
theorem Ζff
    (H : Family α) (V : Edge α) {p : Edge α} {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v) :
    (p ∈ Ζaf H V z ∧
      v ∈ (Ζb H V p).erase z) ↔
    p ∈ Ζc H V ({z, v} : Edge α) := by
  constructor
  · rintro ⟨hsource, hv⟩
    have hpV := (Finset.mem_filter.mp hsource).1
    have hzComp : z ∈ Ζb H V p := by
      obtain ⟨_, hznot, hpz⟩ := Finset.mem_filter.mp hsource
      exact Finset.mem_filter.mpr ⟨hzV, hznot, hpz⟩
    have hvComp := Finset.mem_erase.mp hv |>.2
    have hqV : ({z, v} : Edge α) ∈ V.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      exact ⟨by
        intro a ha
        rcases Finset.mem_insert.mp ha with haz | hav
        · exact haz ▸ hzV
        · exact (Finset.mem_singleton.mp hav) ▸ hvV,
        Finset.card_pair hzv⟩
    have hpCells : ({z, v} : Edge α) ∈ Ζis H V p := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hzv⟩
      intro a ha
      rcases Finset.mem_insert.mp ha with haz | hav
      · exact haz ▸ hzComp
      · exact (Finset.mem_singleton.mp hav) ▸ hvComp
    exact (Ζha H V _ _ hqV hpV).2 hpCells
  · intro hp
    have hsrc := Ζam hzv hp
    have hvComp : v ∈ Ζb H V p := by
      obtain ⟨_, hvnot, hpv⟩ := Finset.mem_filter.mp hsrc.2
      exact Finset.mem_filter.mpr ⟨hvV, hvnot, hpv⟩
    exact ⟨hsrc.1, Finset.mem_erase.mpr ⟨Ne.symm hzv, hvComp⟩⟩
set_option maxHeartbeats 300000 in
noncomputable def Ζoa
    (H : Family α) (V : Edge α) (z v : α) : ℚ := by
  classical
  exact ∑ p ∈ Ζaf H V z, Ζea H V z v p
set_option maxHeartbeats 300000 in
theorem Ζmm
    (H : Family α) (V : Edge α) {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v) :
    Ζoa H V z v =
      ∑ p ∈ Ζc H V ({z, v} : Edge α),
        Ζw H V z v p := by
  classical
  let S := Ζaf H V z
  let P : Edge α → Prop := fun p =>
    v ∈ (Ζb H V p).erase z
  have hfilter : S.filter P = Ζc H V ({z, v} : Edge α) := by
    ext p
    simp only [Finset.mem_filter, S, P]
    exact Ζff H V hzV hvV hzv
  unfold Ζoa
  change (∑ p ∈ S, Ζea H V z v p) = _
  calc
    (∑ p ∈ S, Ζea H V z v p) =
        ∑ p ∈ S, if P p then Ζw H V z v p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [Ζea, S, P, hp]
    _ = ∑ p ∈ S.filter P, Ζw H V z v p := by
      rw [← Finset.sum_filter]
    _ = ∑ p ∈ Ζc H V ({z, v} : Edge α),
        Ζw H V z v p := by rw [hfilter]
set_option maxHeartbeats 300000 in
noncomputable def Ζbo
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ v ∈ V.erase z,
    ∑ p ∈ Ζc H V ({z, v} : Edge α),
      Ζw H V z v p
set_option maxHeartbeats 300000 in
theorem Ζpj
    (H : Family α) (V : Edge α) :
    Ζhp H V = Ζbo H V := by
  classical
  unfold Ζhp Ζbo
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro v hv
  have hvV : v ∈ V := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  exact Ζmm H V hz hvV hzv
set_option maxHeartbeats 300000 in
theorem Ζpk
    (H : Family α) (V : Edge α) :
    Ζez H V = Ζbo H V := by
  rw [← Ζpj H V]
  exact Ζuo H V
set_option maxHeartbeats 300000 in
theorem Ζtq
    (H : Family α) (V : Edge α) (z v x y : α) :
    Ζh H V z x y v =
      Ζh H V z y x v := by
  have hcomp : Ζb H V ({x, y} : Edge α) =
      Ζb H V ({y, x} : Edge α) := by
    simp only [Finset.pair_comm]
  simp only [Ζh, hcomp, Ζao,
    Ζq, Ζfk]
set_option maxHeartbeats 300000 in
theorem Ζaa
    (H : Family α) (V p : Edge α) (z v x y : α)
    (hp : p.card = 2) (hpair : p = ({x, y} : Edge α)) :
    Ζw H V z v p = Ζh H V z x y v := by
  classical
  let e := Ζcf p hp
  have he := Ζbq p hp
  have heq : ({e.1, e.2} : Edge α) = ({x, y} : Edge α) :=
    he.2.symm.trans hpair
  have he1 : e.1 = x ∨ e.1 = y := by
    have hm : e.1 ∈ ({x, y} : Edge α) := by
      rw [← heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hcases : (e.1 = x ∧ e.2 = y) ∨ (e.1 = y ∧ e.2 = x) := by
    rcases he1 with h1 | h1
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact False.elim (he.1 (h1.trans h2.symm))
      · exact Or.inl ⟨h1, h2⟩
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact False.elim (he.1 (h1.trans h2.symm))
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [Ζw, hp, e, h1, h2]
  · rw [Ζtq]
    simp [Ζw, hp, e, h1, h2]
set_option maxHeartbeats 300000 in
noncomputable def Ζak
    (H : Family α) (V : Edge α) (z v : α) : ℚ := by
  classical
  exact ∑ p ∈ Ζc H V ({z, v} : Edge α),
    (Ζw H V z v p + Ζw H V v z p)
set_option maxHeartbeats 300000 in
theorem Ζra
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (_hzV : z ∈ V) (_hvV : v ∈ V) (hzv : z ≠ v) :
    (∃ x : α, ∀ p ∈ Ζc H V ({z, v} : Edge α), x ∈ p) ∨
      (Ζc H V ({z, v} : Edge α)).card ≤ 3 := by
  apply Ζic
  · intro p hp
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq
    exact Ζfn hH hzv hp hq
set_option maxHeartbeats 300000 in
theorem Ζle
    {H : Family α} {V p : Edge α} {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hp : p ∈ Ζc H V ({z, v} : Edge α)) :
    Ζw H V z v p + Ζw H V v z p < 4 := by
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp
    (Finset.mem_filter.mp hp).1).2
  let e := Ζcf p hp2
  have he := Ζbq p hp2
  have hsrc := Ζam hzv hp
  have hsrcZ : ({e.1, e.2} : Edge α) ∈ Ζaf H V z := by
    rw [← he.2]
    exact hsrc.1
  have hsrcV : ({e.1, e.2} : Edge α) ∈ Ζaf H V v := by
    rw [← he.2]
    exact hsrc.2
  have hbound := Ζqz
    H V hzV hvV hzv he.1 hsrcZ hsrcV
  simpa [Ζw, hp2, e] using hbound
set_option maxHeartbeats 300000 in
theorem Ζee
    (H : Family α) (V : Edge α) {z v : α} {p₁ p₂ : Edge α}
    (hp₁ : p₁ ∈ Ζc H V ({z, v} : Edge α))
    (hp₂ : p₂ ∈ Ζc H V ({z, v} : Edge α))
    (hne : p₁ ≠ p₂)
    (hcard : (Ζc H V ({z, v} : Edge α)).card = 2) :
    Ζak H V z v =
      (Ζw H V z v p₁ + Ζw H V v z p₁) +
      (Ζw H V z v p₂ + Ζw H V v z p₂) := by
  classical
  have hsub : ({p₁, p₂} : Finset (Edge α)) ⊆
      Ζc H V ({z, v} : Edge α) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · simpa [h] using hp₁
    · exact (Finset.mem_singleton.mp h) ▸ hp₂
  have hpairCard : ({p₁, p₂} : Finset (Edge α)).card = 2 :=
    Finset.card_pair hne
  have hset' : ({p₁, p₂} : Finset (Edge α)) =
      Ζc H V ({z, v} : Edge α) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hpairCard])
  have hset : Ζc H V ({z, v} : Edge α) = {p₁, p₂} := hset'.symm
  unfold Ζak
  rw [hset]
  simp [hne]
set_option maxHeartbeats 300000 in
theorem Ζpl
    (H : Family α) (V : Edge α) {z v : α}
    (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hcard : (Ζc H V ({z, v} : Edge α)).card = 1) :
    Ζak H V z v < 4 := by
  classical
  unfold Ζak
  obtain ⟨p₀, hp₀⟩ := Finset.card_eq_one.mp hcard
  have hp₀mem : p₀ ∈ Ζc H V ({z, v} : Edge α) := by
    rw [hp₀]
    exact Finset.mem_singleton_self _
  rw [hp₀]
  simp only [Finset.sum_singleton]
  exact Ζle hzV hvV hzv hp₀mem
set_option maxHeartbeats 300000 in
theorem Ζdn
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hcard : (Ζc H V ({z, v} : Edge α)).card = 2) :
    ∃ x y u : α, x ≠ y ∧ x ≠ u ∧ y ≠ u ∧ y ∈ V ∧ u ∈ V ∧
      ((({x, y} : Edge α) ∈ Ζc H V ({z, v} : Edge α) ∧
       ({x, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α) ∧
       ({v, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α) ∧
       ({z, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α)) ∨
       (({x, y} : Edge α) ∈ Ζc H V ({z, v} : Edge α) ∧
       ({y, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α) ∧
       ({v, y} : Edge α) ∈ Ζc H V ({x, u} : Edge α) ∧
       ({z, y} : Edge α) ∈ Ζc H V ({x, u} : Edge α))) := by
  have htwo := Finset.card_eq_two.mp hcard
  obtain ⟨p, t, hpt, hcells⟩ := htwo
  have hp : p ∈ Ζc H V ({z, v} : Edge α) := by
    rw [hcells]
    simp
  have ht : t ∈ Ζc H V ({z, v} : Edge α) := by
    rw [hcells]
    simp
  have hpOrient := (Ζr H V hzv p).mp hp
  have htOrient := (Ζr H V hzv t).mp ht
  have hpSwap : p ∈ Ζc H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using hp
  have htSwap : t ∈ Ζc H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using ht
  have hpRev := (Ζr H V (Ne.symm hzv) p).mp hpSwap
  have htRev := (Ζr H V (Ne.symm hzv) t).mp htSwap
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpOrient).1).2
  obtain ⟨x, y, hxy, hpEq⟩ := Finset.card_eq_two.mp hp2
  subst p
  have hyV : y ∈ V := by
    have hsubset := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hpOrient).1).1
    exact hsubset (by simp)
  have htErase : t ∈ (Ζe H V z v).erase ({x, y} : Edge α) :=
    Finset.mem_erase.mpr ⟨by
      intro heq
      exact hpt heq.symm, htOrient⟩
  have hcovered := Ζds
    hH hzV hvV hzv hxy hpOrient htErase
  rcases Finset.mem_union.mp hcovered with hright | hleft
  · obtain ⟨u, huWeak, htu⟩ := Finset.mem_image.mp hright
    change u ∈ ((Ζk H V z x).erase y).filter _ at huWeak
    have huMem := (Finset.mem_filter.mp huWeak).1
    have huy : u ≠ y := (Finset.mem_erase.mp huMem).1
    have hxu : x ≠ u := by
      intro h
      subst u
      exact Ζpu H V z x (Finset.mem_erase.mp huMem).2
    have h_yu : y ≠ u := Ne.symm huy
    have huV : u ∈ V := Ζhx H V z x
      (Finset.mem_erase.mp huMem).2
    have hxuLink : ({x, u} : Edge α) ∈ Ζe H V z v := by
      rw [htu]
      exact htOrient
    have hrecip := Ζbk H V hvV
      hxy hxu h_yu hpOrient hxuLink
    have hxuLinkRev : ({x, u} : Edge α) ∈ Ζe H V v z := by
      rw [htu]
      exact htRev
    have hrecipRev := Ζbk H V hzV
      hxy hxu h_yu hpRev hxuLinkRev
    have hxuCore : ({x, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α) := by
      rw [htu]
      exact ht
    exact ⟨x, y, u, hxy, hxu, h_yu, hyV, huV,
      Or.inl ⟨hp, hxuCore, hrecip, hrecipRev⟩⟩
  · obtain ⟨u, huWeak, htu⟩ := Finset.mem_image.mp hleft
    change u ∈ ((Ζk H V z y).erase x).filter _ at huWeak
    have huMem := (Finset.mem_filter.mp huWeak).1
    have hux : u ≠ x := (Finset.mem_erase.mp huMem).1
    have hyu : y ≠ u := by
      intro h
      subst u
      exact Ζpu H V z y (Finset.mem_erase.mp huMem).2
    have hxu : x ≠ u := Ne.symm hux
    have huV : u ∈ V := Ζhx H V z y
      (Finset.mem_erase.mp huMem).2
    have hyxSource : ({y, x} : Edge α) ∈ Ζe H V z v := by
      simpa only [Finset.pair_comm] using hpOrient
    have hyuLink : ({y, u} : Edge α) ∈ Ζe H V z v := by
      rw [htu]
      exact htOrient
    have hrecip := Ζbk H V hvV
      (Ne.symm hxy) hyu hxu hyxSource hyuLink
    have hyxSourceRev : ({y, x} : Edge α) ∈ Ζe H V v z := by
      simpa only [Finset.pair_comm] using hpRev
    have hyuLinkRev : ({y, u} : Edge α) ∈ Ζe H V v z := by
      rw [htu]
      exact htRev
    have hrecipRev := Ζbk H V hzV
      (Ne.symm hxy) hyu hxu hyxSourceRev hyuLinkRev
    have hyuCore : ({y, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α) := by
      rw [htu]
      exact ht
    exact ⟨x, y, u, hxy, hxu, hyu, hyV, huV,
      Or.inr ⟨hp, hyuCore, hrecip, hrecipRev⟩⟩
set_option maxHeartbeats 300000 in
theorem Ζpm
    (d₁ d₂ d₃ d₄ : ℕ) :
    (if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
    (if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
    (if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) +
    (if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
        (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) ≤ 4 := by
  let h₁ : ℕ := (if 4 ≤ d₁ then 1 else 0) + (if 4 ≤ d₂ then 1 else 0)
  let h₂ : ℕ := (if 4 ≤ d₃ then 1 else 0) + (if 4 ≤ d₄ then 1 else 0)
  have hh₁ : h₁ ≤ 2 := by dsimp [h₁]; split_ifs <;> omega
  have hh₂ : h₂ ≤ 2 := by dsimp [h₂]; split_ifs <;> omega
  have hformula :
      (if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
      (if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0) +
      (if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) +
      (if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) +
          (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) =
        (h₁ : ℚ) * (2 - 2 * (h₂ : ℚ) / 3) +
          (h₂ : ℚ) * (2 - 2 * (h₁ : ℚ) / 3) := by
    simp only [h₁, h₂]
    split_ifs <;> norm_num
  rw [hformula]
  exact Ζrj h₁ h₂ hh₁ hh₂
set_option maxHeartbeats 300000 in
theorem Ζnc
    (d₁ d₂ d₃ d₄ : ℕ)
    (c₁₃ c₁₄ c₂₃ c₂₄ c₃₁ c₃₂ c₄₁ c₄₂ : ℚ)
    (h₁₃ : c₁₃ ≤ if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0)
    (h₁₄ : c₁₄ ≤ if 4 ≤ d₁ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0)
    (h₂₃ : c₂₃ ≤ if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0)
    (h₂₄ : c₂₄ ≤ if 4 ≤ d₂ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0)
    (h₃₁ : c₃₁ ≤ if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0)
    (h₃₂ : c₃₂ ≤ if 4 ≤ d₃ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0)
    (h₄₁ : c₄₁ ≤ if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0)
    (h₄₂ : c₄₂ ≤ if 4 ≤ d₄ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0) :
    c₁₃ + c₁₄ + c₂₃ + c₂₄ + c₃₁ + c₃₂ + c₄₁ + c₄₂ ≤ 4 := by
  have hmatrix := Ζpm d₁ d₂ d₃ d₄
  by_cases h₁ : 4 ≤ d₁ <;> by_cases h₂ : 4 ≤ d₂ <;>
    by_cases h₃ : 4 ≤ d₃ <;> by_cases h₄ : 4 ≤ d₄ <;>
    simp_all <;> linarith
set_option maxHeartbeats 300000 in
theorem Ζga
    {H : Family α} {V : Edge α} {x y u z v : α}
    (hH : Admissible H)
    (hyV : y ∈ V) (huV : u ∈ V)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hxy : x ≠ y) (hxu : x ≠ u) (hxv : x ≠ v) (hxz : x ≠ z)
    (hzv : z ≠ v) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (h₃ : ({x, v} : Edge α) ∈ Ζc H V ({y, u} : Edge α))
    (h₄ : ({x, z} : Edge α) ∈ Ζc H V ({y, u} : Edge α))
    (hc₁ : (Ζc H V ({z, v} : Edge α)).card = 2)
    (hc₂ : (Ζc H V ({y, u} : Edge α)).card = 2) :
    Ζak H V z v + Ζak H V y u ≤ 4 := by
  have hs₁ := Ζam hzv h₁
  have hs₂ := Ζam hzv h₂
  have hs₃ := Ζam hyu h₃
  have hs₄ := Ζam hyu h₄
  have hne₁ : ({x, y} : Edge α) ≠ {x, u} := by
    intro heq
    have hyMem : y ∈ ({x, u} : Edge α) := by rw [← heq]; simp
    rcases Finset.mem_insert.mp hyMem with h | h
    · exact hxy h.symm
    · exact hyu (Finset.mem_singleton.mp h)
  have hne₂ : ({x, v} : Edge α) ≠ {x, z} := by
    intro heq
    have hvMem : v ∈ ({x, z} : Edge α) := by rw [← heq]; simp
    rcases Finset.mem_insert.mp hvMem with h | h
    · exact hxv h.symm
    · exact hzv (Finset.mem_singleton.mp h).symm
  have hcell₁ := Ζee H V h₁ h₂ hne₁ hc₁
  have hcell₂ := Ζee H V h₃ h₄ hne₂ hc₂
  have hcard₁ : ({x, y} : Edge α).card = 2 := Finset.card_pair hxy
  have hcard₂ : ({x, u} : Edge α).card = 2 := Finset.card_pair hxu
  have hcard₃ : ({x, v} : Edge α).card = 2 := Finset.card_pair hxv
  have hcard₄ : ({x, z} : Edge α).card = 2 := Finset.card_pair hxz
  have hv₁ : v ∈ (Ζb H V ({x, y} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      Ζv H V hvV hs₁.2⟩
  have hz₁ : z ∈ (Ζb H V ({x, y} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, Ζv H V hzV hs₁.1⟩
  have hv₂ : v ∈ (Ζb H V ({x, u} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      Ζv H V hvV hs₂.2⟩
  have hz₂ : z ∈ (Ζb H V ({x, u} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, Ζv H V hzV hs₂.1⟩
  have hu₃ : u ∈ (Ζb H V ({x, v} : Edge α)).erase y :=
    Finset.mem_erase.mpr ⟨Ne.symm hyu,
      Ζv H V huV hs₃.2⟩
  have hy₃ : y ∈ (Ζb H V ({x, v} : Edge α)).erase u :=
    Finset.mem_erase.mpr ⟨hyu, Ζv H V hyV hs₃.1⟩
  have hu₄ : u ∈ (Ζb H V ({x, z} : Edge α)).erase y :=
    Finset.mem_erase.mpr ⟨Ne.symm hyu,
      Ζv H V huV hs₄.2⟩
  have hy₄ : y ∈ (Ζb H V ({x, z} : Edge α)).erase u :=
    Finset.mem_erase.mpr ⟨hyu, Ζv H V hyV hs₄.1⟩
  let d₁ := (Ζb H V ({x, z} : Edge α)).card
  let d₂ := (Ζb H V ({x, v} : Edge α)).card
  let d₃ := (Ζb H V ({x, y} : Edge α)).card
  let d₄ := (Ζb H V ({x, u} : Edge α)).card
  have c₁₃ := Ζaz
    hH hzV hs₁.1 hxy hv₁ hc₁
  have c₁₄ := Ζaz
    hH hzV hs₂.1 hxu hv₂ hc₁
  have c₂₃ := Ζaz
    hH hvV hs₁.2 hxy hz₁ (by simpa [Finset.pair_comm] using hc₁)
  have c₂₄ := Ζaz
    hH hvV hs₂.2 hxu hz₂ (by simpa [Finset.pair_comm] using hc₁)
  have c₃₂ := Ζaz
    hH hyV hs₃.1 hxv hu₃ hc₂
  have c₃₁ := Ζaz
    hH hyV hs₄.1 hxz hu₄ hc₂
  have c₄₂ := Ζaz
    hH huV hs₃.2 hxv hy₃ (by simpa [Finset.pair_comm] using hc₂)
  have c₄₁ := Ζaz
    hH huV hs₄.2 hxz hy₄ (by simpa [Finset.pair_comm] using hc₂)
  have c₁₃' : Ζh H V z x y v ≤
      if 4 ≤ d₁ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₁, d₃, Finset.pair_comm] using c₁₃
  have c₁₄' : Ζh H V z x u v ≤
      if 4 ≤ d₁ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₁, d₄, Finset.pair_comm] using c₁₄
  have c₂₃' : Ζh H V v x y z ≤
      if 4 ≤ d₂ then (if 4 ≤ d₃ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₂, d₃, Finset.pair_comm] using c₂₃
  have c₂₄' : Ζh H V v x u z ≤
      if 4 ≤ d₂ then (if 4 ≤ d₄ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₂, d₄, Finset.pair_comm] using c₂₄
  have c₃₂' : Ζh H V y x v u ≤
      if 4 ≤ d₃ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₃, d₂, Finset.pair_comm] using c₃₂
  have c₃₁' : Ζh H V y x z u ≤
      if 4 ≤ d₃ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₃, d₁, Finset.pair_comm] using c₃₁
  have c₄₂' : Ζh H V u x v y ≤
      if 4 ≤ d₄ then (if 4 ≤ d₂ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₄, d₂, Finset.pair_comm] using c₄₂
  have c₄₁' : Ζh H V u x z y ≤
      if 4 ≤ d₄ then (if 4 ≤ d₁ then (1 : ℚ) / 3 else 1) else 0 := by
    simpa [d₄, d₁, Finset.pair_comm] using c₄₁
  have hscalar := Ζnc
    d₁ d₂ d₃ d₄ _ _ _ _ _ _ _ _ c₁₃' c₁₄' c₂₃' c₂₄' c₃₁' c₃₂' c₄₁' c₄₂'
  have hrep₁ := Ζaa H V
    ({x, y} : Edge α) z v x y hcard₁ rfl
  have hrep₂ := Ζaa H V
    ({x, u} : Edge α) z v x u hcard₂ rfl
  have hrep₃ := Ζaa H V
    ({x, v} : Edge α) y u x v hcard₃ rfl
  have hrep₄ := Ζaa H V
    ({x, z} : Edge α) y u x z hcard₄ rfl
  have hrep₁b := Ζaa H V
    ({x, y} : Edge α) v z x y hcard₁ rfl
  have hrep₂b := Ζaa H V
    ({x, u} : Edge α) v z x u hcard₂ rfl
  have hrep₃b := Ζaa H V
    ({x, v} : Edge α) u y x v hcard₃ rfl
  have hrep₄b := Ζaa H V
    ({x, z} : Edge α) u y x z hcard₄ rfl
  rw [hcell₁, hcell₂, hrep₁, hrep₂, hrep₃, hrep₄,
    hrep₁b, hrep₂b, hrep₃b, hrep₄b]
  linarith
set_option maxHeartbeats 300000 in
theorem Ζta (H : Family α) (V : Edge α) (z v : α) :
    Ζak H V z v = Ζak H V v z := by
  classical
  unfold Ζak
  simp only [Finset.pair_comm]
  rw [Finset.sum_congr rfl]
  intro p hp
  ring
set_option maxHeartbeats 300000 in
noncomputable def Ζp
    (H : Family α) (V : Edge α) (q : Edge α) : ℚ := by
  classical
  if hq : q.card = 2 then
    let e := Ζcf q hq
    exact Ζak H V e.1 e.2
  else exact 0
set_option maxHeartbeats 300000 in
def Ζad
    (H : Family α) (V : Edge α) (q : Edge α) : Prop :=
  ∃ z v x y u : α, z ∈ V ∧ v ∈ V ∧ x ∈ V ∧ y ∈ V ∧ u ∈ V ∧
    q = ({z, v} : Edge α) ∧
    Ζc H V q = ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α) ∧
    Ζc H V ({y, u} : Edge α) =
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α)
set_option maxHeartbeats 300000 in
noncomputable def Ζgr (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ q ∈ Ζac H V,
    if Ζad H V q then
      max (Ζp H V q - 2) 0 else 0
set_option maxHeartbeats 300000 in
theorem Ζht {β : Type*} [DecidableEq β]
    (s : Finset β) {a b : β} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    2 ≤ s.card := by
  have hsub : ({a, b} : Finset β) ⊆ s := by
    intro t ht
    rcases Finset.mem_insert.mp ht with h | h
    · simpa [h] using ha
    · exact (Finset.mem_singleton.mp h) ▸ hb
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hle
  exact hle
end ReceiverCapacity
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
noncomputable def Ζbf
    (H : Family α) (V : Edge α) (z : α) (p : Edge α) : ℚ := by
  classical
  by_cases hp : p.card = 2
  · let e := Ζcf p hp
    exact Ζq H V z e.1 e.2
  · exact 0
theorem Ζin
    (H : Family α) (V : Edge α) (z x y : α) :
    Ζq H V z x y =
      Ζq H V z y x := by
  unfold Ζq
  rw [Ζfk]
theorem Ζfj
    (H : Family α) (V p : Edge α) (z x y : α)
    (hp : p.card = 2) (hpair : p = ({x, y} : Edge α)) :
    Ζbf H V z p =
      Ζq H V z x y := by
  classical
  let e := Ζcf p hp
  have he := Ζbq p hp
  have heq : ({e.1, e.2} : Edge α) = ({x, y} : Edge α) :=
    he.2.symm.trans hpair
  have he1 : e.1 = x ∨ e.1 = y := by
    have hm : e.1 ∈ ({x, y} : Edge α) := by
      rw [← heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hcases : (e.1 = x ∧ e.2 = y) ∨ (e.1 = y ∧ e.2 = x) := by
    rcases he1 with h1 | h1
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact False.elim (he.1 (h1.trans h2.symm))
      · exact Or.inl ⟨h1, h2⟩
    · have hm : e.2 ∈ ({x, y} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = x ∨ e.2 = y by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact False.elim (he.1 (h1.trans h2.symm))
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [Ζbf, hp, e, h1, h2]
  · rw [Ζin]
    simp [Ζbf, hp, e, h1, h2]
private theorem Ζtb
    (H : Family α) (V : Edge α) (z : α) :
    Ζaf H V z ⊆ (V.erase z).powersetCard 2 := by
  intro p hp
  obtain ⟨hpV, hzNot, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpSub, hpCard⟩ := Finset.mem_powersetCard.mp hpV
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro t ht
    exact Finset.mem_erase.mpr
      ⟨fun htz => hzNot (htz ▸ ht), hpSub ht⟩
  · exact hpCard
private theorem Ζou
    (H : Family α) (V : Edge α) {z x : α}
    (hx : x ∈ V.erase z) :
    Ζk H V z x =
      ((V.erase z).erase x).filter
        (fun y => ({x, y} : Edge α) ∈ Ζaf H V z) := by
  ext y
  have hxV := (Finset.mem_erase.mp hx).2
  have hzx : z ≠ x := Ne.symm (Finset.mem_erase.mp hx).1
  constructor
  · intro hy
    have hLink := (Ζik H V hxV hzx).mp hy
    obtain ⟨hyV, hyNot, _⟩ := Finset.mem_filter.mp hy
    have hyz : y ≠ z := by
      intro h
      exact hyNot (by simp [h])
    have hyx : y ≠ x := by
      intro h
      exact hyNot (by simp [h])
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr
        ⟨hyx, Finset.mem_erase.mpr ⟨hyz, hyV⟩⟩,
        hLink⟩
  · intro hy
    exact (Ζik H V hxV hzx).mpr
      (Finset.mem_filter.mp hy).2
theorem Ζqf
    (H : Family α) (V : Edge α) :
    Ζbv H V / 2 =
      ∑ z ∈ V, ∑ p ∈ Ζaf H V z,
        Ζbf H V z p := by
  have hRoot (z : α) (hz : z ∈ V) :
      (∑ x ∈ V.erase z,
        ∑ y ∈ Ζk H V z x,
          Ζq H V z x y) =
        2 * (∑ p ∈ Ζaf H V z,
          Ζbf H V z p) := by
    let F : Edge α → ℚ := fun p =>
      if p ∈ Ζaf H V z then Ζbf H V z p else 0
    have hOrdered := Ζem
      (V.erase z) F
    have hLeft :
        (∑ x ∈ V.erase z,
          ∑ y ∈ Ζk H V z x,
            Ζq H V z x y) =
          ∑ x ∈ V.erase z,
            ∑ y ∈ (V.erase z).erase x,
              F ({x, y} : Edge α) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Ζou H V hx]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxyLink :
          ({x, y} : Edge α) ∈ Ζaf H V z
      · have hxy : x ≠ y := Ne.symm (Finset.mem_erase.mp hy).1
        simp only [F, hxyLink, ↓reduceIte]
        rw [Ζfj H V
          ({x, y} : Edge α) z x y (Finset.card_pair hxy) rfl]
      · simp [F, hxyLink]
    have hRight :
        (∑ p ∈ (V.erase z).powersetCard 2, F p) =
          ∑ p ∈ Ζaf H V z, Ζbf H V z p := by
      have hSub := Ζtb H V z
      calc
        (∑ p ∈ (V.erase z).powersetCard 2, F p) =
            ∑ p ∈ Ζaf H V z, F p := by
          symm
          apply Finset.sum_subset hSub
          intro p hp hnot
          simp [F, hnot]
        _ = ∑ p ∈ Ζaf H V z,
              Ζbf H V z p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [F, hp]
    rw [← hLeft, hRight] at hOrdered
    exact hOrdered
  have hSum :
      Ζbv H V =
        2 * (∑ z ∈ V, ∑ p ∈ Ζaf H V z,
          Ζbf H V z p) := by
    unfold Ζbv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    exact hRoot z hz
  rw [hSum]
  ring
theorem Ζnd
    (H : Family α) (V p : Edge α) {z : α}
    (hp : p ∈ Ζaf H V z) :
    (∑ v ∈ V.erase z, Ζea H V z v p) =
      ∑ v ∈ (Ζb H V p).erase z,
        Ζw H V z v p := by
  classical
  have hSub : (Ζb H V p).erase z ⊆ V.erase z := by
    intro v hv
    obtain ⟨hvz, hvN⟩ := Finset.mem_erase.mp hv
    exact Finset.mem_erase.mpr
      ⟨hvz, Ζgg H V p hvN⟩
  calc
    (∑ v ∈ V.erase z, Ζea H V z v p) =
        ∑ v ∈ V.erase z,
          if v ∈ (Ζb H V p).erase z then
            Ζw H V z v p else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [Ζea, hp]
    _ = ∑ v ∈ (Ζb H V p).erase z,
          Ζw H V z v p := by
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp only [Finset.mem_filter]
      constructor
      · intro hv
        exact hv.2
      · intro hv
        exact ⟨hSub hv, hv⟩
theorem Ζub
    (H : Family α) (V p : Edge α) {z : α}
    (hzV : z ∈ V) (hp : p ∈ Ζaf H V z) :
    Ζbf H V z p =
      (if (Ζb H V p).card = 1 then
        Ζbf H V z p else 0) +
      ∑ v ∈ V.erase z, Ζea H V z v p := by
  classical
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  let e := Ζcf p hp2
  have he := Ζbq p hp2
  have hsource : ({e.1, e.2} : Edge α) ∈ Ζaf H V z := by
    rw [← he.2]
    exact hp
  have hzN : z ∈ Ζb H V p := by
    rw [he.2]
    exact Ζv H V hzV hsource
  have hPos : 0 < (Ζb H V p).card :=
    Finset.card_pos.mpr ⟨z, hzN⟩
  have hSent := Ζnd H V p hp
  by_cases hOne : (Ζb H V p).card = 1
  · have hEraseCard : ((Ζb H V p).erase z).card = 0 := by
      have hCard := Finset.card_erase_add_one hzN
      omega
    have hEraseEmpty : (Ζb H V p).erase z = ∅ :=
      Finset.card_eq_zero.mp hEraseCard
    rw [hSent, hEraseEmpty]
    simp [hOne]
  · have hAtLeastTwo : 2 ≤ (Ζb H V p).card := by omega
    have hAtLeastTwo' :
        2 ≤ (Ζb H V ({e.1, e.2} : Edge α)).card := by
      exact he.2 ▸ hAtLeastTwo
    have hConserve := Ζqy
      H V hzV hsource hAtLeastTwo'
    have hWeight : Ζbf H V z p =
        Ζq H V z e.1 e.2 :=
      Ζfj H V p z e.1 e.2 hp2 he.2
    have hCharges :
        (∑ v ∈ (Ζb H V p).erase z,
          Ζw H V z v p) =
        ∑ v ∈ (Ζb H V ({e.1, e.2} : Edge α)).erase z,
          Ζh H V z e.1 e.2 v := by
      have hN : Ζb H V p =
          Ζb H V ({e.1, e.2} : Edge α) := by
        rw [he.2]
      rw [hN]
      apply Finset.sum_congr rfl
      intro v hv
      exact Ζaa
        H V p z v e.1 e.2 hp2 he.2
    rw [hSent, hCharges, hConserve, hWeight]
    simp [hOne]
noncomputable def Ζdh
    (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ z ∈ V, ∑ p ∈ Ζaf H V z,
    if (Ζb H V p).card = 1 then
      Ζbf H V z p else 0
theorem Ζnt
    (H : Family α) (V : Edge α) :
    (∑ z ∈ V, ∑ p ∈ Ζaf H V z,
      Ζbf H V z p) =
      Ζdh H V +
        Ζez H V := by
  classical
  calc
    (∑ z ∈ V, ∑ p ∈ Ζaf H V z,
      Ζbf H V z p) =
        ∑ z ∈ V, ∑ p ∈ Ζaf H V z,
          ((if (Ζb H V p).card = 1 then
              Ζbf H V z p else 0) +
            ∑ v ∈ V.erase z, Ζea H V z v p) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro p hp
      exact Ζub H V p hz hp
    _ = Ζdh H V +
          Ζez H V := by
      simp [Ζdh, Ζez,
        Finset.sum_add_distrib]
theorem Ζpn
    (H : Family α) (V : Edge α) :
    Ζbv H V / 2 =
      Ζdh H V +
        Ζbo H V := by
  rw [Ζqf,
    Ζnt,
    Ζpk]
theorem Ζne
    (H : Family α) (V p : Edge α) {z : α}
    (hp : p ∈ Ζaf H V z) :
    Ζbf H V z p < 2 := by
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  let e := Ζcf p hp2
  have he := Ζbq p hp2
  have hsource : ({e.1, e.2} : Edge α) ∈ Ζaf H V z := by
    rw [← he.2]
    exact hp
  rw [Ζfj H V p z e.1 e.2 hp2 he.2]
  exact Ζlr H V hsource he.1
theorem Ζkt
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    Ζdh H V ≤
      2 * ((Ζca H V).card : ℚ) := by
  classical
  have hSwap :
      Ζdh H V =
        ∑ p ∈ V.powersetCard 2,
          ∑ z ∈ Ζb H V p,
            if (Ζb H V p).card = 1 then
              Ζbf H V z p else 0 := by
    unfold Ζdh
    apply Finset.sum_comm'
    intro z p
    simp only [Ζaf, Ζb, Finset.mem_filter]
    tauto
  have hFilter :
      (V.powersetCard 2).filter
        (fun p => (Ζb H V p).card = 1) =
          Ζca H V := by
    ext p
    simp only [Finset.mem_filter, Ζca]
    constructor
    · rintro ⟨hpV, hd1⟩
      have hPos : 0 < (Ζb H V p).card := by omega
      have hNonempty : (Ζb H V p).Nonempty :=
        Finset.card_pos.mp hPos
      exact ⟨(Ζfg
        H V p hU hGround hpV).mpr hNonempty, hd1⟩
    · rintro ⟨hpUsed, hd1⟩
      exact ⟨Ζhj H V hpUsed, hd1⟩
  calc
    Ζdh H V =
        ∑ p ∈ V.powersetCard 2,
          if (Ζb H V p).card = 1 then
            ∑ z ∈ Ζb H V p,
              Ζbf H V z p else 0 := by
        rw [hSwap]
        apply Finset.sum_congr rfl
        intro p hp
        split_ifs <;> simp_all
    _ = ∑ p ∈ Ζca H V,
          ∑ z ∈ Ζb H V p,
            Ζbf H V z p := by
        rw [← Finset.sum_filter, hFilter]
    _ ≤ ∑ p ∈ Ζca H V, (2 : ℚ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpV : p ∈ V.powersetCard 2 :=
          Ζhj H V (Finset.mem_filter.mp hp).1
        have hd1 : (Ζb H V p).card = 1 :=
          (Finset.mem_filter.mp hp).2
        obtain ⟨z, hN⟩ :=
          Finset.card_eq_one.mp hd1
        have hzN : z ∈ Ζb H V p := hN.symm ▸ (by simp)
        have hroot : p ∈ Ζaf H V z :=
          Finset.mem_filter.mpr
            ⟨hpV, (Finset.mem_filter.mp hzN).2⟩
        rw [hN]
        simp
        exact (Ζne H V p hroot).le
    _ = 2 * ((Ζca H V).card : ℚ) := by
        simp
        ring
theorem Ζlm
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hIncoming :
      Ζbo H V ≤
        4 * ((Ζcb H V).card : ℚ) +
        2 * ((Ζau H V).card : ℚ) +
        Ζgr H V) :
    Ζbv H V / 2 ≤
      2 * ((Ζca H V).card : ℚ) +
      4 * ((Ζcb H V).card : ℚ) +
      2 * ((Ζau H V).card : ℚ) +
      Ζgr H V := by
  have hConserve := Ζpn H V
  have hRetained :=
    Ζkt H V hU hGround
  linarith
theorem Ζcj
    (H : Family α) (V : Edge α) {z v : α}
    (hzv : z ≠ v) :
    Ζp H V ({z, v} : Edge α) =
      Ζak H V z v := by
  classical
  let q : Edge α := {z, v}
  have hq2 : q.card = 2 := Finset.card_pair hzv
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have heq : ({e.1, e.2} : Edge α) = ({z, v} : Edge α) := by
    simpa [q] using he.2.symm
  have he1 : e.1 = z ∨ e.1 = v := by
    have hm : e.1 ∈ ({z, v} : Edge α) := by
      rw [← heq]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hcases : (e.1 = z ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = z) := by
    rcases he1 with h1 | h1
    · have hm : e.2 ∈ ({z, v} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = z ∨ e.2 = v by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact False.elim (he.1 (h1.trans h2.symm))
      · exact Or.inl ⟨h1, h2⟩
    · have hm : e.2 ∈ ({z, v} : Edge α) := by
        rw [← heq]
        simp
      rcases (show e.2 = z ∨ e.2 = v by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · exact False.elim (he.1 (h1.trans h2.symm))
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [Ζp, hq2, q, e, h1, h2]
  · have hComm := Ζta H V v z
    simp [Ζp, hq2, q, e, h1, h2] at hComm ⊢
    exact hComm
theorem Ζqg
    (H : Family α) (V : Edge α) :
    Ζbo H V =
      ∑ q ∈ Ζac H V, Ζp H V q := by
  classical
  let F : α → α → ℚ := fun z v =>
    ∑ p ∈ Ζc H V ({z, v} : Edge α),
      Ζw H V z v p
  let G : Edge α → ℚ := Ζp H V
  have hPair (z v : α) (hzv : z ≠ v) :
      G ({z, v} : Edge α) = F z v + F v z := by
    change Ζp H V ({z, v} : Edge α) =
      (∑ p ∈ Ζc H V ({z, v} : Edge α),
        Ζw H V z v p) +
      (∑ p ∈ Ζc H V ({v, z} : Edge α),
        Ζw H V v z p)
    rw [Ζcj H V hzv]
    unfold Ζak
    rw [Finset.sum_add_distrib]
    simp only [Finset.pair_comm]
  have hOrdered := Ζem V G
  have hSwap :
      (∑ z ∈ V, ∑ v ∈ V.erase z, F v z) =
        ∑ z ∈ V, ∑ v ∈ V.erase z, F z v := by
    apply Finset.sum_comm'
    intro z v
    constructor
    · rintro ⟨hzV, hv⟩
      obtain ⟨hvz, hvV⟩ := Finset.mem_erase.mp hv
      exact ⟨Finset.mem_erase.mpr ⟨hvz.symm, hzV⟩, hvV⟩
    · rintro ⟨hz, hvV⟩
      obtain ⟨hzv, hzV⟩ := Finset.mem_erase.mp hz
      exact ⟨hzV, Finset.mem_erase.mpr ⟨hzv.symm, hvV⟩⟩
  have hExpand :
      (∑ z ∈ V, ∑ v ∈ V.erase z,
        G ({z, v} : Edge α)) =
        2 * (∑ z ∈ V, ∑ v ∈ V.erase z, F z v) := by
    calc
      (∑ z ∈ V, ∑ v ∈ V.erase z,
        G ({z, v} : Edge α)) =
          ∑ z ∈ V, ∑ v ∈ V.erase z,
            (F z v + F v z) := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro v hv
        exact hPair z v (Ne.symm (Finset.mem_erase.mp hv).1)
      _ = 2 * (∑ z ∈ V, ∑ v ∈ V.erase z, F z v) := by
        simp only [Finset.sum_add_distrib, ← hSwap]
        ring
  have hAll :
      Ζbo H V =
        ∑ q ∈ V.powersetCard 2, G q := by
    unfold Ζbo
    change (∑ z ∈ V, ∑ v ∈ V.erase z, F z v) = _
    rw [hExpand] at hOrdered
    linarith
  calc
    Ζbo H V =
        ∑ q ∈ V.powersetCard 2, G q := hAll
    _ = ∑ q ∈ Ζac H V, G q := by
      symm
      apply Finset.sum_subset (Ζbr H V)
      intro q hqV hqNot
      have hEmpty : Ζc H V q = ∅ := by
        by_contra h
        have hNonempty : (Ζc H V q).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr h
        exact hqNot ((Ζas H V q).mpr
          ⟨hqV, hNonempty⟩)
      have hq2 := (Finset.mem_powersetCard.mp hqV).2
      let e := Ζcf q hq2
      have he := Ζbq q hq2
      have hLinkEmpty :
          Ζc H V ({e.1, e.2} : Edge α) = ∅ :=
        he.2.symm ▸ hEmpty
      simp only [G, Ζp, Ζom hq2]
      change Ζak H V e.1 e.2 = 0
      simp [Ζak, hLinkEmpty]
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
theorem Ζlx
    (H : Family α) (V : Edge α) (Ξ : ℚ)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hCapacity :
      Ζbv H V / 2 ≤
        2 * ((Ζca H V).card : ℚ) +
        4 * ((Ζcb H V).card : ℚ) +
        2 * ((Ζau H V).card : ℚ) + Ξ) :
    6 * (2 * (H.card : ℚ) -
      ((Ζbp H V).card : ℚ) -
      ((Ζac H V).card : ℚ)) ≤
      Ξ - ∑ E ∈ H, Ζax H V E := by
  have hLedger := Ζvg H V hU hGround
  have hPayment := Ζmh
    V hAdm hU hGround
  linarith
theorem Ζlf
    (H : Family α) (V : Edge α) (Ξ : ℚ)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hCapacity :
      Ζbv H V / 2 ≤
        2 * ((Ζca H V).card : ℚ) +
        4 * ((Ζcb H V).card : ℚ) +
        2 * ((Ζau H V).card : ℚ) + Ξ)
    (hPaid : Ξ ≤ ∑ E ∈ H, Ζax H V E) :
    2 * H.card ≤
      (Ζbp H V).card + (Ζac H V).card := by
  have hDefect := Ζlx
    H V Ξ hU hAdm hGround hCapacity
  have hRational : 2 * (H.card : ℚ) ≤
      ((Ζbp H V).card : ℚ) +
      ((Ζac H V).card : ℚ) := by
    linarith
  exact_mod_cast hRational
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section ReceiverCapacityExtended
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 500000 in
theorem Ζov
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (hcard : (Ζc H V ({z, v} : Edge α)).card = 2)
    (hrecipStar : ∀ p ∈ Ζc H V ({y, u} : Edge α), x ∈ p)
    (hrecipLarge : 3 ≤ (Ζc H V ({y, u} : Edge α)).card) :
    Ζak H V z v ≤ 2 := by
  have h₁rev : ({x, y} : Edge α) ∈ Ζc H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₁
  have h₂rev : ({x, u} : Edge α) ∈ Ζc H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₂
  have h₁or := (Ζr H V hzv _).mp h₁
  have h₂or := (Ζr H V hzv _).mp h₂
  have h₁revOr := (Ζr H V (Ne.symm hzv) _).mp h₁rev
  have h₂revOr := (Ζr H V (Ne.symm hzv) _).mp h₂rev
  have hpv := Ζbk H V hvV hxy hxu hyu h₁or h₂or
  have hpz := Ζbk H V hzV hxy hxu hyu h₁revOr h₂revOr
  have hpv' : ({x, v} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpv
  have hpz' : ({x, z} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpz
  have hpvNePz : ({x, v} : Edge α) ≠ ({x, z} : Edge α) := by
    intro he
    have hv : v ∈ ({x, z} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hv with hvx | hvz
    · have hxv : x ≠ v := Finset.card_pair_eq_two_iff.mp
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpv').1).2
      exact hxv hvx.symm
    · exact hzv (Finset.mem_singleton.mp hvz).symm
  have hnotSub : ¬ Ζc H V ({y, u} : Edge α) ⊆
      ({({x, v} : Edge α), ({x, z} : Edge α)} : Family α) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hpvNePz] at hle
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.not_subset.mp hnotSub
  have hpneqv : p ≠ ({x, v} : Edge α) := by
    intro he
    apply hpnot
    rw [he]
    simp
  have hpneqz : p ≠ ({x, z} : Edge α) := by
    intro he
    apply hpnot
    rw [he]
    simp
  have hpx : x ∈ p := hrecipStar p hp
  obtain ⟨a, b, hab, hpEq⟩ :=
    Finset.card_eq_two.mp ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2)
  have hxa : x = a ∨ x = b := by
    have hxmem : x ∈ ({a, b} : Edge α) := by simpa [hpEq] using hpx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxmem
  let t : α := if x = a then b else a
  have hxt : x ≠ t := by
    dsimp [t]
    split_ifs with h
    · intro hxb
      exact hab (h.symm.trans hxb)
    · exact h
  have hpPair : p = ({x, t} : Edge α) := by
    rw [hpEq]
    dsimp [t]
    split_ifs with h
    · simp [h]
    · have hb : x = b := by
        rcases hxa with h' | h'
        · exact (h h').elim
        · exact h'
      simp [Finset.pair_comm, h, hb]
  obtain ⟨_, _, _, _, _, hdis, _, _⟩ := (Finset.mem_filter.mp hp).2
  have hty : t ≠ y := by
    intro h
    have htmem : t ∈ p := by rw [hpPair]; simp
    exact (Finset.disjoint_left.mp hdis) htmem (by simp [h])
  have htu : t ≠ u := by
    intro h
    have htmem : t ∈ p := by rw [hpPair]; simp
    exact (Finset.disjoint_left.mp hdis) htmem (by simp [h])
  have htv : t ≠ v := by
    intro h
    apply hpneqv
    rw [hpPair, h]
  have htz : t ≠ z := by
    intro h
    apply hpneqz
    rw [hpPair, h]
  have hs₁ := Ζam hzv h₁
  have hs₂ := Ζam hzv h₂
  have htSource : ({x, t} : Edge α) ∈ Ζaf H V y := by
    have hroot := Ζam hyu hp
    simpa only [hpPair] using hroot.1
  have hrootT := Finset.mem_filter.mp htSource
  have htV : t ∈ V :=
    (Finset.mem_powersetCard.mp hrootT.1).1 (by simp)
  have hTriple : ({x, y} : Edge α) ∪ {t} ∈ H := by
    have heq : ({x, y} : Edge α) ∪ {t} = ({x, t} : Edge α) ∪ {y} := by
      ext w
      simp [Finset.mem_union, Finset.mem_insert, or_comm, or_left_comm, or_assoc]
    rw [heq]
    exact hrootT.2.2
  have htXY : t ∈ Ζb H V ({x, y} : Edge α) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact htV
    · constructor
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        intro ht
        rcases (show t = x ∨ t = y by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using ht) with htx | hty'
        · exact hxt htx.symm
        · exact hty hty'
      · exact hTriple
  have hTripleU : ({x, u} : Edge α) ∪ {t} ∈ H := by
    have hrootU := Ζam hyu hp
    have hm := Finset.mem_filter.mp hrootU.2
    rw [hpPair] at hm
    have heq : ({x, u} : Edge α) ∪ {t} = ({x, t} : Edge α) ∪ {u} := by
      ext w
      simp [Finset.mem_union, Finset.mem_insert, or_comm, or_left_comm, or_assoc]
    rw [heq]
    exact hm.2.2
  have htXU : t ∈ Ζb H V ({x, u} : Edge α) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact htV
    · constructor
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        intro ht
        rcases (show t = x ∨ t = u by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using ht) with htx | htu'
        · exact hxt htx.symm
        · exact htu htu'
      · exact hTripleU
  have hdegXY : 3 ≤ (Ζb H V ({x, y} : Edge α)).card := by
    have hsub : ({z, v, t} : Finset α) ⊆ Ζb H V ({x, y} : Edge α) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact Ζv H V hzV hs₁.1
      · exact Ζv H V hvV hs₁.2
      · exact htXY
    have hcard3 : ({z, v, t} : Finset α).card = 3 := by
      simp [hzv, Ne.symm hzv, htz, Ne.symm htz, htv, Ne.symm htv]
    rw [← hcard3]
    exact Finset.card_le_card hsub
  have hdegXU : 3 ≤ (Ζb H V ({x, u} : Edge α)).card := by
    have hsub : ({z, v, t} : Finset α) ⊆ Ζb H V ({x, u} : Edge α) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact Ζv H V hzV hs₂.1
      · exact Ζv H V hvV hs₂.2
      · exact htXU
    have hcard3 : ({z, v, t} : Finset α).card = 3 := by
      simp [hzv, Ne.symm hzv, htz, Ne.symm htz, htv, Ne.symm htv]
    rw [← hcard3]
    exact Finset.card_le_card hsub
  have hvXY : v ∈ (Ζb H V ({x, y} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      Ζv H V hvV hs₁.2⟩
  have hzXY : z ∈ (Ζb H V ({x, y} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, Ζv H V hzV hs₁.1⟩
  have hvXU : v ∈ (Ζb H V ({x, u} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      Ζv H V hvV hs₂.2⟩
  have hzXU : z ∈ (Ζb H V ({x, u} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, Ζv H V hzV hs₂.1⟩
  have hcharge₁ := Ζdg hH hzV hs₁.1 hxy hvXY hcard
  have hcharge₂ := Ζdg hH hvV hs₁.2 hxy hzXY
    (by simpa only [Finset.pair_comm] using hcard)
  have hcharge₃ := Ζdg hH hzV hs₂.1 hxu hvXU hcard
  have hcharge₄ := Ζdg hH hvV hs₂.2 hxu hzXU
    (by simpa only [Finset.pair_comm] using hcard)
  have hdenXY : 1 / (((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1) ≤ 1 / 2 := by
    have hd : (3 : ℚ) ≤ (Ζb H V ({x, y} : Edge α)).card := by exact_mod_cast hdegXY
    have hdpos : (0 : ℚ) < ((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1 := by linarith
    apply (div_le_iff₀ hdpos).2
    norm_num
    linarith
  have hdenXU : 1 / (((Ζb H V ({x, u} : Edge α)).card : ℚ) - 1) ≤ 1 / 2 := by
    have hd : (3 : ℚ) ≤ (Ζb H V ({x, u} : Edge α)).card := by exact_mod_cast hdegXU
    have hdpos : (0 : ℚ) < ((Ζb H V ({x, u} : Edge α)).card : ℚ) - 1 := by linarith
    apply (div_le_iff₀ hdpos).2
    norm_num
    linarith
  have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
    intro he
    have hyMem : y ∈ ({x, u} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hyMem with h | h
    · exact hxy h.symm
    · exact hyu (Finset.mem_singleton.mp h)
  have hcell := Ζee H V h₁ h₂ hne hcard
  have hxyCard : ({x, y} : Edge α).card = 2 := Finset.card_pair hxy
  have hxuCard : ({x, u} : Edge α).card = 2 := Finset.card_pair hxu
  have hrep₁ := Ζaa H V
    ({x, y} : Edge α) z v x y hxyCard rfl
  have hrep₂ := Ζaa H V
    ({x, y} : Edge α) v z x y hxyCard rfl
  have hrep₃ := Ζaa H V
    ({x, u} : Edge α) z v x u hxuCard rfl
  have hrep₄ := Ζaa H V
    ({x, u} : Edge α) v z x u hxuCard rfl
  rw [hcell, hrep₁, hrep₂, hrep₃, hrep₄]
  linarith [hcharge₁, hcharge₂, hcharge₃, hcharge₄, hdenXY, hdenXU]
set_option maxHeartbeats 500000 in
theorem Ζkl
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hyV : y ∈ V) (huV : u ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (hcard : (Ζc H V ({z, v} : Edge α)).card = 2)
    (hrecipLarge : 3 ≤ (Ζc H V ({y, u} : Edge α)).card)
    (hnocenter : ¬ ∃ a : α, ∀ p ∈ Ζc H V ({y, u} : Edge α), a ∈ p) :
    Ζad H V ({z, v} : Edge α) := by
  have h₁rev : ({x, y} : Edge α) ∈ Ζc H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₁
  have h₂rev : ({x, u} : Edge α) ∈ Ζc H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₂
  have h₁or := (Ζr H V hzv _).mp h₁
  have h₂or := (Ζr H V hzv _).mp h₂
  have h₁revOr := (Ζr H V (Ne.symm hzv) _).mp h₁rev
  have h₂revOr := (Ζr H V (Ne.symm hzv) _).mp h₂rev
  have hpv := Ζbk H V hvV hxy hxu hyu h₁or h₂or
  have hpz := Ζbk H V hzV hxy hxu hyu h₁revOr h₂revOr
  have hpv' : ({x, v} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpv
  have hpz' : ({x, z} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpz
  have hxv : x ≠ v := by
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpv').1).2
    exact Finset.card_pair_eq_two_iff.mp hc
  have hxz : x ≠ z := by
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpz').1).2
    exact Finset.card_pair_eq_two_iff.mp hc
  have hthird : ∃ p ∈ Ζc H V ({y, u} : Edge α), x ∉ p := by
    by_contra h
    apply hnocenter
    refine ⟨x, ?_⟩
    intro p hp
    by_contra hpx
    exact h ⟨p, hp, hpx⟩
  obtain ⟨p, hp, hpx⟩ := hthird
  have hpy : y ≠ u := hyu
  have hpCard : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  have hvp : v ∈ p := by
    by_contra hvp
    apply Ζfn hH hyu hp hpv'
    apply Finset.disjoint_left.mpr
    intro a ha hpair
    rcases Finset.mem_insert.mp hpair with hax | hav
    · exact hpx (hax ▸ ha)
    · exact hvp ((Finset.mem_singleton.mp hav) ▸ ha)
  have hzp : z ∈ p := by
    by_contra hzp
    apply Ζfn hH hyu hp hpz'
    apply Finset.disjoint_left.mpr
    intro a ha hpair
    rcases Finset.mem_insert.mp hpair with hax | haz
    · exact hpx (hax ▸ ha)
    · exact hzp ((Finset.mem_singleton.mp haz) ▸ ha)
  have hsub : ({z, v} : Edge α) ⊆ p := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzp
    · exact (Finset.mem_singleton.mp hav) ▸ hvp
  have hpEq : p = ({z, v} : Edge α) := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_pair hzv, hpCard]
  have hp3 : ({z, v} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
    rw [← hpEq]
    exact hp
  have hpair₁ : ({x, z} : Edge α) ≠ ({x, v} : Edge α) := by
    intro he
    have hzm : z ∈ ({x, v} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hzm with hzx | hzv'
    · exact hxz hzx.symm
    · exact hzv (Finset.mem_singleton.mp hzv')
  have hpair₂ : ({z, v} : Edge α) ≠ ({x, z} : Edge α) := by
    intro he
    have hvm : v ∈ ({x, z} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hvm with hvx | hvz
    · exact hxv hvx.symm
    · exact hzv (Finset.mem_singleton.mp hvz).symm
  have hpair₃ : ({z, v} : Edge α) ≠ ({x, v} : Edge α) := by
    intro he
    have hzm : z ∈ ({x, v} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hzm with hzx | hzv'
    · exact hxz hzx.symm
    · exact hzv (Finset.mem_singleton.mp hzv')
  have htriCard :
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α).card = 3 := by
    have houter : ({x, z} : Edge α) ∉
        ({({x, v} : Edge α), ({z, v} : Edge α)} : Family α) := by
      simp [hpair₁, Ne.symm hpair₂]
    have hinner : ({x, v} : Edge α) ∉ ({({z, v} : Edge α)} : Family α) := by
      simp [Ne.symm hpair₃]
    rw [Finset.card_insert_of_notMem houter,
      Finset.card_insert_of_notMem hinner]
    simp
  have hCLCard : (Ζc H V ({y, u} : Edge α)).card = 3 := by
    have hclass := Ζra hH hyV huV hyu
    rcases hclass with ⟨a, hstar⟩ | hsmall
    · exact False.elim (hnocenter ⟨a, hstar⟩)
    · omega
  have htriSub :
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α) ⊆
        Ζc H V ({y, u} : Edge α) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq
    · simpa [hq] using hpz'
    · simpa [hq] using hpv'
    · simpa [hq] using hp3
  have htriEq : Ζc H V ({y, u} : Edge α) =
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α) := by
    symm
    apply Finset.eq_of_subset_of_card_le htriSub
    rw [htriCard, hCLCard]
  have hneCores : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
    intro he
    have hyMem : y ∈ ({x, u} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hyMem with h | h
    · exact hxy h.symm
    · exact hyu (Finset.mem_singleton.mp h)
  have hsourceCard :
      ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α).card = 2 :=
    Finset.card_pair hneCores
  have hsourceSub :
      ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α) ⊆
        Ζc H V ({z, v} : Edge α) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp
    · simpa [hp] using h₁
    · simpa [hp] using h₂
  have hsourceEq : Ζc H V ({z, v} : Edge α) =
      ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α) := by
    symm
    apply Finset.eq_of_subset_of_card_le hsourceSub
    rw [hsourceCard, hcard]
  have hxV : x ∈ V := by
    have hpV := (Finset.mem_filter.mp h₁).1
    exact (Finset.mem_powersetCard.mp hpV).1 (by simp)
  exact ⟨z, v, x, y, u, hzV, hvV, hxV, hyV, huV, rfl, hsourceEq, htriEq⟩
end ReceiverCapacityExtended
end JSP523.Rank3
end
section
namespace JSP523.Rank3
theorem Ζnf
    {β : Type*} [DecidableEq β]
    (S : Finset β) (R : β → β) (f : β → ℚ)
    (hMap : ∀ q ∈ S, R q ∈ S)
    (hInv : ∀ q ∈ S, R (R q) = q)
    (hPair : ∀ q ∈ S, f q + f (R q) ≤ 4) :
    ∑ q ∈ S, f q ≤ 2 * (S.card : ℚ) := by
  have hSwap : (∑ q ∈ S, f (R q)) = ∑ q ∈ S, f q := by
    apply Finset.sum_bij (fun q _ => R q)
    · intro q hq
      exact hMap q hq
    · intro q hq r hr heq
      calc
        q = R (R q) := (hInv q hq).symm
        _ = R (R r) := by rw [heq]
        _ = r := hInv r hr
    · intro r hr
      exact ⟨R r, hMap r hr, hInv r hr⟩
    · intro q hq
      rfl
  have hSum : (∑ q ∈ S, (f q + f (R q))) ≤
      ∑ q ∈ S, (4 : ℚ) := by
    apply Finset.sum_le_sum
    intro q hq
    exact hPair q hq
  rw [Finset.sum_add_distrib, hSwap] at hSum
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  nlinarith
end JSP523.Rank3
end
section
open scoped symmDiff
namespace JSP523.Rank3
section ReceiverGlobalCapacity
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 500000 in
theorem Ζhm
    {H : Family α} {V : Edge α} {z v x y : α}
    (hzV : z ∈ V) (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hrecv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z) :
    0 ≤ Ζh H V z x y v := by
  have hzcomp := Ζv H V hzV hsource
  have hrecv' := (Finset.mem_erase.mp hrecv).2
  have hne := (Finset.mem_erase.mp hrecv).1
  have hsub : ({z, v} : Edge α) ⊆ Ζb H V ({x, y} : Edge α) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzcomp
    · exact (Finset.mem_singleton.mp hav) ▸ hrecv'
  have hdegree := Finset.card_le_card hsub
  have htwo : 2 ≤ ({z, v} : Edge α).card := by simp [Ne.symm hne]
  have hdegree' : 2 ≤ (Ζb H V ({x, y} : Edge α)).card := htwo.trans hdegree
  have hden : (0 : ℚ) < ((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (Ζb H V ({x, y} : Edge α)).card := by exact_mod_cast hdegree'
    linarith
  simp [Ζh, hrecv, Ζao]
  exact div_nonneg (le_max_right _ _) (le_of_lt hden)
set_option maxHeartbeats 500000 in
theorem Ζsk
    {p r a b : Edge α} (hpr : p ≠ r) (_hab : a ≠ b)
    (hset : ({p, r} : Family α) = {a, b}) :
    p ∆ r = a ∆ b := by
  have hp : p = a ∨ p = b := by
    have hm : p ∈ ({a, b} : Family α) := by rw [← hset]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hp with hpa | hpb
  · have hr : r = b := by
      have hm : r ∈ ({a, b} : Family α) := by rw [← hset]; simp
      rcases (show r = a ∨ r = b by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h | h
      · exact False.elim (hpr (hpa.trans h.symm))
      · exact h
    simp [hpa, hr]
  · have hr : r = a := by
      have hm : r ∈ ({a, b} : Family α) := by rw [← hset]; simp
      rcases (show r = a ∨ r = b by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hm) with h | h
      · exact h
      · exact False.elim (hpr (hpb.trans h.symm))
    ext w
    simp [Finset.mem_symmDiff, hpb, hr, or_comm]
set_option maxHeartbeats 500000 in
noncomputable def Ζab (H : Family α) (V : Edge α) (q : Edge α) : Edge α := by
  classical
  if hc : (Ζc H V q).card = 2 then
    let e := Ζcf (Ζc H V q) hc
    exact e.1 ∆ e.2
  else exact ∅
set_option maxHeartbeats 500000 in
theorem Ζaj
    (H : Family α) (V q : Edge α)
    (hc : (Ζc H V q).card = 2)
    {p r : Edge α} (hp : p ∈ Ζc H V q)
    (hr : r ∈ Ζc H V q) (hpr : p ≠ r) :
    Ζab H V q = p ∆ r := by
  classical
  have hset : ({p, r} : Family α) = Ζc H V q := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rcases Finset.mem_insert.mp ht with h | h
      · simpa [h] using hp
      · exact (Finset.mem_singleton.mp h) ▸ hr
    · rw [Finset.card_pair hpr, hc]
  let e := Ζcf (Ζc H V q) hc
  have he := Ζbq (Ζc H V q) hc
  have hpair : ({p, r} : Family α) = ({e.1, e.2} : Family α) := by
    rw [hset, he.2]
  have hresult := Ζsk hpr he.1 hpair
  simpa [Ζab, hc, e] using hresult.symm
set_option maxHeartbeats 500000 in
theorem Ζay {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, c} : Edge α) ∆ ({b, c} : Edge α) = {a, b} := by
  ext w
  by_cases hwa : w = a
  · subst w
    simp [Finset.mem_symmDiff, hab, hac]
  · by_cases hwb : w = b
    · subst w
      simp [Finset.mem_symmDiff, hab.symm, hbc]
    · by_cases hwc : w = c
      · subst w
        simp [Finset.mem_symmDiff, hac.symm, hbc.symm]
      · simp [Finset.mem_symmDiff, hwa, hwb, hwc]
set_option maxHeartbeats 500000 in
theorem Ζhg
    {H : Family α} {V q : Edge α}
    (hH : Admissible H) (hq : q ∈ Ζau H V)
    (hrecip : Ζab H V q ∈ Ζau H V) :
    Ζab H V (Ζab H V q) = q := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 :=
    (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).2
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have hqCardRep :
      (Ζc H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hzv : e.1 ≠ e.2 := he.1
  have hrecipCard := (Finset.mem_filter.mp hrecip).2
  have hrecipUsed := (Finset.mem_filter.mp hrecip).1
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    Ζdn hH heV.1 heV.2 hzv
      hqCardRep
  have hcaseMap :
      Ζab H V q = ({y, u} : Edge α) ∨
      Ζab H V q = ({x, u} : Edge α) := by
    rcases hcases with ⟨hp, hr, _, _⟩ | ⟨hp, hr, _, _⟩
    ·
      have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
        intro hh
        have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hyMem with hyx | hyu'
        · exact hxy hyx.symm
        · exact hyu (Finset.mem_singleton.mp hyu')
      have hmap := Ζaj H V
        ({e.1, e.2} : Edge α) hqCardRep hp hr hne
      left
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hyu (Ne.symm hxy) (Ne.symm hxu))
    ·
      have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
        intro hh
        have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
        · exact hxy hxy'
        · exact hxu (Finset.mem_singleton.mp hxu')
      have hmap := Ζaj H V
        ({e.1, e.2} : Edge α) hqCardRep hp hr hne
      right
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hxu hxy (Ne.symm hyu))
  rcases hcaseMap with hq' | hq'
  ·
    have htargetCard : (Ζc H V ({y, u} : Edge α)).card = 2 := by
      rw [← hq']
      exact hrecipCard
    rcases hcases with ⟨_, _, hp, hr⟩ | ⟨hpOther, hrOther, _, _⟩
    · have hpc : ({e.2, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hp
      have hrc : ({e.1, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hr
      have hne : ({e.2, x} : Edge α) ≠ ({e.1, x} : Edge α) := by
        intro hh
        have hvMem : e.2 ∈ ({e.1, x} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hvMem with hvz | hvx
        · exact hzv hvz.symm
        · have hxv : x ≠ e.2 := by
            have hc := (Finset.mem_powersetCard.mp
              (Finset.mem_filter.mp hpc).1).2
            exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
          exact hxv (Finset.mem_singleton.mp hvx).symm
      have hback := Ζaj H V
        ({y, u} : Edge α) htargetCard hpc hrc hne
      rw [hq', hback]
      have he2x : e.2 ≠ x := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpc).1).2)
      have he1x : e.1 ≠ x := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hrc).1).2)
      calc
        ({e.2, x} : Edge α) ∆ {e.1, x} = {e.2, e.1} :=
          Ζay (Ne.symm hzv) he2x he1x
        _ = ({e.1, e.2} : Edge α) := Finset.pair_comm e.2 e.1
        _ = q := he.2.symm
    · have hother : Ζab H V q = ({x, u} : Edge α) := by
        have hne' : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
          intro hh
          have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
          rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
          · exact hxy hxy'
          · exact hxu (Finset.mem_singleton.mp hxu')
        have hm := Ζaj H V
          ({e.1, e.2} : Edge α) hqCardRep hpOther hrOther hne'
        rw [he.2, hm]
        simpa only [Finset.pair_comm] using
          (Ζay hxu hxy (Ne.symm hyu))
      have : False := by
        have htarget : ({x, u} : Edge α) = ({y, u} : Edge α) := hother.symm.trans hq'
        have hxMem : x ∈ ({y, u} : Edge α) := by rw [← htarget]; simp
        rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
        · exact hxy hxy'
        · exact hxu (Finset.mem_singleton.mp hxu')
      exact this.elim
  ·
    have htargetCard : (Ζc H V ({x, u} : Edge α)).card = 2 := by
      rw [← hq']
      exact hrecipCard
    rcases hcases with ⟨hpOther, hrOther, _, _⟩ | ⟨_, _, hp, hr⟩
    · have hother : Ζab H V q = ({y, u} : Edge α) := by
        have hne' : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
          intro hh
          have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
          rcases Finset.mem_insert.mp hyMem with hxy' | hyu'
          · exact hxy hxy'.symm
          · exact hyu (Finset.mem_singleton.mp hyu')
        have hm := Ζaj H V
          ({e.1, e.2} : Edge α) hqCardRep hpOther hrOther hne'
        rw [he.2, hm]
        simpa only [Finset.pair_comm] using
          (Ζay hyu (Ne.symm hxy) (Ne.symm hxu))
      have : False := by
        have htarget : ({y, u} : Edge α) = ({x, u} : Edge α) := hother.symm.trans hq'
        have hyMem : y ∈ ({x, u} : Edge α) := by rw [← htarget]; simp
        rcases Finset.mem_insert.mp hyMem with hxy' | hyu'
        · exact hxy hxy'.symm
        · exact hyu (Finset.mem_singleton.mp hyu')
      exact this.elim
    · have hpc : ({e.2, y} : Edge α) ∈ Ζc H V ({x, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hp
      have hrc : ({e.1, y} : Edge α) ∈ Ζc H V ({x, u} : Edge α) := by
        simpa only [Finset.pair_comm] using hr
      have hne : ({e.2, y} : Edge α) ≠ ({e.1, y} : Edge α) := by
        intro hh
        have hvMem : e.2 ∈ ({e.1, y} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hvMem with hvz | hvy
        · exact hzv hvz.symm
        · have hyv : y ≠ e.2 := by
            have hc := (Finset.mem_powersetCard.mp
              (Finset.mem_filter.mp hpc).1).2
            exact Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
          exact hyv (Finset.mem_singleton.mp hvy).symm
      have hback := Ζaj H V
        ({x, u} : Edge α) htargetCard hpc hrc hne
      rw [hq', hback]
      have he2y : e.2 ≠ y := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpc).1).2)
      have he1y : e.1 ≠ y := Finset.card_pair_eq_two_iff.mp
        ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hrc).1).2)
      calc
        ({e.2, y} : Edge α) ∆ {e.1, y} = {e.2, e.1} :=
          Ζay (Ne.symm hzv) he2y he1y
        _ = ({e.1, e.2} : Edge α) := Finset.pair_comm e.2 e.1
        _ = q := he.2.symm
set_option maxHeartbeats 500000 in
theorem Ζgx
    {H : Family α} {V q : Edge α} (hH : Admissible H)
    (hq : q ∈ Ζau H V) :
    2 ≤ (Ζc H V (Ζab H V q)).card := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (Ζbr H V hqUsed)).2
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have hqCardRep :
      (Ζc H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    Ζdn hH heV.1 heV.2 he.1 hqCardRep
  rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
      intro hh
      have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hyMem with hyx | hyu'
      · exact hxy hyx.symm
      · exact hyu (Finset.mem_singleton.mp hyu')
    have hmap := Ζaj H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : Ζab H V q = ({y, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hyu (Ne.symm hxy) (Ne.symm hxu))
    have hp : ({e.2, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have hr : ({e.1, x} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hne' : ({e.2, x} : Edge α) ≠ ({e.1, x} : Edge α) := by
      intro hh
      have he2mem : e.2 ∈ ({e.1, x} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp he2mem with heq | heq
      · exact he.1 heq.symm
      · have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
        have hxne : x ≠ e.2 := Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
        exact hxne (Finset.mem_singleton.mp heq).symm
    have hcard := Ζht
      (Ζc H V ({y, u} : Edge α)) hp hr hne'
    rw [htarget]
    exact hcard
  · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
      intro hh
      have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
      · exact hxy hxy'
      · exact hxu (Finset.mem_singleton.mp hxu')
    have hmap := Ζaj H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : Ζab H V q = ({x, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hxu hxy (Ne.symm hyu))
    have hp : ({e.2, y} : Edge α) ∈ Ζc H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have hr : ({e.1, y} : Edge α) ∈ Ζc H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hne' : ({e.2, y} : Edge α) ≠ ({e.1, y} : Edge α) := by
      intro hh
      have he2mem : e.2 ∈ ({e.1, y} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp he2mem with heq | heq
      · exact he.1 heq.symm
      · have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
        have hyne : y ≠ e.2 := Ne.symm (Finset.card_pair_eq_two_iff.mp hc)
        exact hyne (Finset.mem_singleton.mp heq).symm
    have hcard := Ζht
      (Ζc H V ({x, u} : Edge α)) hp hr hne'
    rw [htarget]
    exact hcard
set_option maxHeartbeats 500000 in
noncomputable def Ζba
    (H : Family α) (V : Edge α) : Family α := by
  classical
  exact (Ζau H V).filter
    (fun q => Ζab H V q ∈ Ζau H V)
set_option maxHeartbeats 500000 in
theorem Ζuc
    {H : Family α} {V : Edge α} (hH : Admissible H) (q : Edge α)
    (hq : q ∈ Ζba H V) :
    Ζab H V q ∈ Ζba H V := by
  classical
  have hdouble := (Finset.mem_filter.mp hq).1
  have htarget := (Finset.mem_filter.mp hq).2
  have hback := Ζhg hH hdouble htarget
  apply Finset.mem_filter.mpr
  exact ⟨htarget, hback.symm ▸ hdouble⟩
set_option maxHeartbeats 500000 in
theorem Ζrb
    {H : Family α} {V : Edge α} (hH : Admissible H) (q : Edge α)
    (hq : q ∈ Ζba H V) :
    Ζab H V (Ζab H V q) = q := by
  classical
  exact Ζhg
    hH (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
set_option maxHeartbeats 500000 in
theorem Ζow
    {H : Family α} {V q : Edge α} (hH : Admissible H)
    (hq : q ∈ Ζba H V) :
    Ζp H V q +
      Ζp H V (Ζab H V q) ≤ 4 := by
  classical
  have hdouble := (Finset.mem_filter.mp hq).1
  have hrecipDouble := (Finset.mem_filter.mp hq).2
  have hqUsed := (Finset.mem_filter.mp hdouble).1
  have hqCard := (Finset.mem_filter.mp hdouble).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (Ζbr H V hqUsed)).2
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have hqCardRep :
      (Ζc H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hchargeQ : Ζp H V q =
      Ζak H V e.1 e.2 := by
    rw [he.2]
    exact Ζcj H V he.1
  have hrecipCard := (Finset.mem_filter.mp hrecipDouble).2
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    Ζdn hH heV.1 heV.2 he.1 hqCardRep
  rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
  · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
      intro hh
      have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hyMem with hyx | hyu'
      · exact hxy hyx.symm
      · exact hyu (Finset.mem_singleton.mp hyu')
    have hmap := Ζaj H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : Ζab H V q = ({y, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hyu (Ne.symm hxy) (Ne.symm hxu))
    have htargetCard : (Ζc H V ({y, u} : Edge α)).card = 2 := by
      rw [← htarget]
      exact hrecipCard
    have h₃ : ({x, e.2} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have h₄ : ({x, e.1} : Edge α) ∈ Ζc H V ({y, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hxv : x ≠ e.2 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₃).1).2)
    have hxz : x ≠ e.1 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₄).1).2)
    have hxV : x ∈ V := by
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1 (by simp)
    have hcap := Ζga hH
      hyV huV heV.1 heV.2 hxy hxu hxv hxz he.1 hyu h₁ h₂ h₃ h₄
      hqCardRep htargetCard
    have hchargeR : Ζp H V (Ζab H V q) =
        Ζak H V y u := by
      rw [htarget]
      exact Ζcj H V hyu
    rw [hchargeQ, hchargeR]
    exact hcap
  · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
      intro hh
      have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
      rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
      · exact hxy hxy'
      · exact hxu (Finset.mem_singleton.mp hxu')
    have hmap := Ζaj H V
      ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
    have htarget : Ζab H V q = ({x, u} : Edge α) := by
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hxu hxy (Ne.symm hyu))
    have htargetCard : (Ζc H V ({x, u} : Edge α)).card = 2 := by
      rw [← htarget]
      exact hrecipCard
    have h₃ : ({y, e.2} : Edge α) ∈ Ζc H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₃
    have h₄ : ({y, e.1} : Edge α) ∈ Ζc H V ({x, u} : Edge α) := by
      simpa only [Finset.pair_comm] using h₄
    have hyv : y ≠ e.2 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₃).1).2)
    have hyz : y ≠ e.1 := Finset.card_pair_eq_two_iff.mp
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₄).1).2)
    have hxV : x ∈ V := by
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1 (by simp)
    have hcap := Ζga hH
      hxV huV heV.1 heV.2 (Ne.symm hxy) hyu hyv hyz he.1 hxu
      (by simpa only [Finset.pair_comm] using h₁) h₂
      h₃ h₄ hqCardRep htargetCard
    have hchargeR : Ζp H V (Ζab H V q) =
        Ζak H V x u := by
      rw [htarget]
      exact Ζcj H V hxu
    rw [hchargeQ, hchargeR]
    exact hcap
set_option maxHeartbeats 500000 in
theorem Ζmn
    (H : Family α) (V : Edge α) (hH : Admissible H)
    :
    (∑ q ∈ Ζba H V,
      Ζp H V q) ≤
      2 * ((Ζba H V).card : ℚ) := by
  apply Ζnf
    (Ζba H V) (Ζab H V)
    (Ζp H V)
  · exact Ζuc hH
  · exact Ζrb hH
  · intro q hq
    exact Ζow hH hq
set_option maxHeartbeats 500000 in
theorem Ζgn
    {H : Family α} {V : Edge α} {z v : α} {p : Edge α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V) (hzv : z ≠ v)
    (hp : p ∈ Ζc H V ({z, v} : Edge α))
    (hpositive : 0 < Ζw H V z v p) :
    (Ζc H V ({z, v} : Edge α)).card ≤ 2 := by
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp
    (Finset.mem_filter.mp hp).1).2
  let e := Ζcf p hp2
  have he := Ζbq p hp2
  have hpZ : ({e.1, e.2} : Edge α) ∈ Ζaf H V z := by
    rw [← he.2]
    exact (Ζam hzv hp).1
  have hrecv := (Ζff H V hzV hvV hzv).2 hp
  have hrecv' : v ∈ (Ζb H V ({e.1, e.2} : Edge α)).erase z := by
    rw [← he.2]
    exact hrecv.2
  have hcharge : 0 < Ζh H V z e.1 e.2 v := by
    simpa [Ζw, hp2, e] using hpositive
  have hweight : 0 < Ζq H V z e.1 e.2 := by
    have hden : (0 : ℚ) < ((Ζb H V ({e.1, e.2} : Edge α)).card : ℚ) - 1 := by
      have hzcomp := Ζv H V hzV hpZ
      have hvcomp := (Finset.mem_erase.mp hrecv').2
      have hsub : ({z, v} : Edge α) ⊆ Ζb H V ({e.1, e.2} : Edge α) := by
        intro a ha
        rcases Finset.mem_insert.mp ha with haz | hav
        · exact haz ▸ hzcomp
        · exact (Finset.mem_singleton.mp hav) ▸ hvcomp
      have hdegree := Finset.card_le_card hsub
      have htwo : 2 ≤ ({z, v} : Edge α).card := by simp [hzv]
      have hdegree' : 2 ≤ (Ζb H V ({e.1, e.2} : Edge α)).card := htwo.trans hdegree
      have hcast : (2 : ℚ) ≤ (Ζb H V ({e.1, e.2} : Edge α)).card := by
        exact_mod_cast hdegree'
      linarith
    have hcharge' : 0 < Ζao H V z e.1 e.2 := by
      simpa [Ζh, hrecv'] using hcharge
    unfold Ζao at hcharge'
    rcases (div_pos_iff.mp hcharge') with h | h
    · exact h.1
    · linarith
  exact Ζtp hH hzV hpZ he.1 hrecv' hweight
set_option maxHeartbeats 500000 in
theorem Ζjd
    {H : Family α} {V : Edge α} (hH : Admissible H)
    {q : Edge α} (hq : q ∈ Ζac H V)
    (hlarge : 3 ≤ (Ζc H V q).card) :
    Ζp H V q = 0 := by
  classical
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (Ζbr H V hq)).2
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have heV : e.1 ∈ V ∧ e.2 ∈ V := by
    have hsub := (Finset.mem_powersetCard.mp (Ζbr H V hq)).1
    have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by
      rw [← he.2]
      exact hsub
    exact ⟨hsub' (by simp), hsub' (by simp)⟩
  have hcellZero : Ζak H V e.1 e.2 = 0 := by
    unfold Ζak
    apply Finset.sum_eq_zero
    intro p hp
    have h₁ : Ζw H V e.1 e.2 p = 0 := by
      by_contra hne
      have hpos : 0 < Ζw H V e.1 e.2 p := by
        have hnon : 0 ≤ Ζw H V e.1 e.2 p := by
          by_cases hp' : p.card = 2
          · let f := Ζcf p hp'
            have hf := Ζbq p hp'
            have hsource : ({f.1, f.2} : Edge α) ∈ Ζaf H V e.1 := by
              rw [← hf.2]
              exact (Ζam he.1 hp).1
            have hrecv := (Ζff H V heV.1 heV.2 he.1).2 hp
            have hrecv' : e.2 ∈ (Ζb H V ({f.1, f.2} : Edge α)).erase e.1 := by
              rw [← hf.2]
              exact hrecv.2
            simpa [Ζw, hp', f] using
              Ζhm heV.1 hsource hrecv'
          · simp [Ζw, hp']
        have hpositive' : 0 < Ζw H V e.1 e.2 p := lt_of_le_of_ne hnon (Ne.symm hne)
        exact hpositive'
      have hbound := Ζgn hH
        heV.1 heV.2 he.1 hp hpos
      have hlarge' : 3 ≤ (Ζc H V ({e.1, e.2} : Edge α)).card := by
        rw [← he.2]
        exact hlarge
      omega
    have h₂ : Ζw H V e.2 e.1 p = 0 := by
      by_contra hne
      have hpos : 0 < Ζw H V e.2 e.1 p := by
        have hnon : 0 ≤ Ζw H V e.2 e.1 p := by
          by_cases hp' : p.card = 2
          · let f := Ζcf p hp'
            have hf := Ζbq p hp'
            have hsource : ({f.1, f.2} : Edge α) ∈ Ζaf H V e.2 := by
              rw [← hf.2]
              exact (Ζam he.1 hp).2
            have hp'cell : p ∈ Ζc H V ({e.2, e.1} : Edge α) := by
              simpa only [Finset.pair_comm] using hp
            have hrecv := (Ζff H V heV.2 heV.1 (Ne.symm he.1)).2 hp'cell
            have hrecv' : e.1 ∈ (Ζb H V ({f.1, f.2} : Edge α)).erase e.2 := by
              rw [← hf.2]
              exact hrecv.2
            simpa [Ζw, hp', f] using
              Ζhm heV.2 hsource hrecv'
          · simp [Ζw, hp']
        have hpositive' : 0 < Ζw H V e.2 e.1 p := lt_of_le_of_ne hnon (Ne.symm hne)
        exact hpositive'
      have hp' : p ∈ Ζc H V ({e.2, e.1} : Edge α) := by
        simpa only [Finset.pair_comm] using hp
      have hbound := Ζgn hH
        heV.2 heV.1 (Ne.symm he.1) hp' hpos
      have hlarge' : 3 ≤ (Ζc H V ({e.2, e.1} : Edge α)).card := by
        calc
          3 ≤ (Ζc H V q).card := hlarge
          _ = (Ζc H V ({e.2, e.1} : Edge α)).card := by
            rw [he.2, Finset.pair_comm]
      omega
    simp [h₁, h₂]
  simpa [Ζp, hq2, e] using hcellZero
set_option maxHeartbeats 500000 in
def Ζjo (H : Family α) (V : Edge α) : Family α :=
  (Ζac H V).filter (fun q => 3 ≤ (Ζc H V q).card)
set_option maxHeartbeats 500000 in
theorem Ζka
    {H : Family α} {V q : Edge α} (hq : q ∈ Ζcb H V) :
    Ζp H V q < 4 := by
  have hused := (Finset.mem_filter.mp hq).1
  have hc := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp
    (Ζbr H V hused)).2
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have hsub := (Finset.mem_powersetCard.mp (Ζbr H V hused)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hdisplay : Ζp H V q =
      Ζak H V e.1 e.2 := by
    rw [he.2]
    exact Ζcj H V he.1
  rw [hdisplay]
  have hc' : (Ζc H V ({e.1, e.2} : Edge α)).card = 1 := by
    rw [← he.2]
    exact hc
  exact Ζpl H V heV.1 heV.2 he.1 hc'
set_option maxHeartbeats 500000 in
theorem Ζtj
    (H : Family α) (V : Edge α) :
    (∑ q ∈ Ζcb H V, Ζp H V q) ≤
      4 * (Ζcb H V).card := by
  calc
    _ ≤ ∑ q ∈ Ζcb H V, (4 : ℚ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact (Ζka hq).le
    _ = 4 * (Ζcb H V).card := by
      simp
      ring
set_option maxHeartbeats 500000 in
theorem Ζrc
    (H : Family α) (V : Edge α) (hH : Admissible H) :
    (∑ q ∈ Ζjo H V, Ζp H V q) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  exact Ζjd hH
    (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
set_option maxHeartbeats 500000 in
theorem Ζrk
    (H : Family α) (V : Edge α) :
    (∑ q ∈ Ζac H V, Ζp H V q) =
      (∑ q ∈ Ζcb H V, Ζp H V q) +
      (∑ q ∈ Ζau H V, Ζp H V q) +
      (∑ q ∈ Ζjo H V, Ζp H V q) := by
  classical
  have hpoint : ∀ q ∈ Ζac H V,
      Ζp H V q =
        (if (Ζc H V q).card = 1 then Ζp H V q else 0) +
        (if (Ζc H V q).card = 2 then Ζp H V q else 0) +
        (if 3 ≤ (Ζc H V q).card then Ζp H V q else 0) := by
    intro q hq
    have hpos : 0 < (Ζc H V q).card := Finset.card_pos.mpr
      ((Ζas H V q).mp hq).2
    by_cases h1 : (Ζc H V q).card = 1
    · simp [h1]
    · by_cases h2 : (Ζc H V q).card = 2
      · simp [h1, h2]
      · have h3 : 3 ≤ (Ζc H V q).card := by omega
        simp [h1, h2, h3]
  calc
    _ = ∑ q ∈ Ζac H V,
        ((if (Ζc H V q).card = 1 then Ζp H V q else 0) +
         (if (Ζc H V q).card = 2 then Ζp H V q else 0) +
         (if 3 ≤ (Ζc H V q).card then Ζp H V q else 0)) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hpoint q hq
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter,
      Ζcb, Ζau, Ζjo]
set_option maxHeartbeats 500000 in
noncomputable def Ζck
    (H : Family α) (V : Edge α) (q : Edge α) : ℚ := by
  classical
  exact if Ζad H V q then
    max (Ζp H V q - 2) 0 else 0
set_option maxHeartbeats 500000 in
theorem Ζrl
    (H : Family α) (V : Edge α) :
    Ζgr H V = ∑ q ∈ Ζac H V, Ζck H V q := by
  classical
  simp [Ζgr, Ζck]
set_option maxHeartbeats 500000 in
theorem Ζtc
    (H : Family α) (V : Edge α) (q : Edge α) :
    0 ≤ Ζck H V q := by
  classical
  by_cases hq : Ζad H V q
  · simp [Ζck, hq]
  · simp [Ζck, hq]
set_option maxHeartbeats 500000 in
theorem Ζly
    (H : Family α) (V : Edge α) (q : Edge α)
    (hordinary : ¬ Ζad H V q →
      Ζp H V q ≤ 2) :
    Ζp H V q ≤ 2 + Ζck H V q := by
  classical
  by_cases hq : Ζad H V q
  · simp [Ζck, hq]
    have hmax : Ζp H V q - 2 ≤
        max (Ζp H V q - 2) 0 := le_max_left _ _
    linarith
  · have h := hordinary hq
    simpa [Ζck, hq] using h
end ReceiverGlobalCapacity
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
theorem Ζgk
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hyV : y ∈ V) (huV : u ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ Ζc H V ({z, v} : Edge α))
    (hcard : (Ζc H V ({z, v} : Edge α)).card = 2)
    (hlarge : 3 ≤ (Ζc H V ({y, u} : Edge α)).card)
    (hordinary : ¬ Ζad H V ({z, v} : Edge α)) :
    Ζak H V z v ≤ 2 := by
  by_cases hcenter : ∃ a : α,
      ∀ p ∈ Ζc H V ({y, u} : Edge α), a ∈ p
  · obtain ⟨a, ha⟩ := hcenter
    have h₁or := (Ζr H V hzv _).mp h₁
    have h₂or := (Ζr H V hzv _).mp h₂
    have h₁rev : ({x, y} : Edge α) ∈
        Ζc H V ({v, z} : Edge α) := by
      simpa only [Finset.pair_comm] using h₁
    have h₂rev : ({x, u} : Edge α) ∈
        Ζc H V ({v, z} : Edge α) := by
      simpa only [Finset.pair_comm] using h₂
    have h₁revOr := (Ζr H V (Ne.symm hzv) _).mp h₁rev
    have h₂revOr := (Ζr H V (Ne.symm hzv) _).mp h₂rev
    have hpv := Ζbk H V hvV hxy hxu hyu h₁or h₂or
    have hpz := Ζbk H V hzV hxy hxu hyu h₁revOr h₂revOr
    have hav : a ∈ ({x, v} : Edge α) := by
      apply ha
      simpa only [Finset.pair_comm] using hpv
    have haz : a ∈ ({x, z} : Edge α) := by
      apply ha
      simpa only [Finset.pair_comm] using hpz
    have hax : a = x := by
      have hv : a = x ∨ a = v := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hav
      have hz : a = x ∨ a = z := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using haz
      rcases hv with h | h
      · exact h
      · rcases hz with h' | h'
        · exact h'
        · exact False.elim (hzv (h'.symm.trans h))
    have hxCenter : ∀ p ∈ Ζc H V ({y, u} : Edge α), x ∈ p := by
      intro p hp
      rw [← hax]
      exact ha p hp
    exact Ζov hH hzV hvV hzv hxy hxu hyu
      h₁ h₂ hcard hxCenter hlarge
  · exact False.elim (hordinary
      (Ζkl
        hH hzV hvV hyV huV hzv hxy hxu hyu h₁ h₂ hcard hlarge hcenter))
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
theorem Ζln
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hcard : (Ζc H V ({z, v} : Edge α)).card = 2)
    (hlarge : 3 ≤
      (Ζc H V (Ζab H V ({z, v} : Edge α))).card)
    (hordinary : ¬ Ζad H V ({z, v} : Edge α)) :
    Ζak H V z v ≤ 2 := by
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    Ζdn hH hzV hvV hzv hcard
  rcases hcases with ⟨hp, hr, _, _⟩ | ⟨hp, hr, _, _⟩
  · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
      intro he
      have hyMem : y ∈ ({x, u} : Edge α) := by rw [← he]; simp
      rcases Finset.mem_insert.mp hyMem with hyx | hyu'
      · exact hxy hyx.symm
      · exact hyu (Finset.mem_singleton.mp hyu')
    have hmap := Ζaj H V
      ({z, v} : Edge α) hcard hp hr hne
    have hmap' : Ζab H V ({z, v} : Edge α) =
        ({y, u} : Edge α) := by
      rw [hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hyu (Ne.symm hxy) (Ne.symm hxu))
    have hlarge' : 3 ≤ (Ζc H V ({y, u} : Edge α)).card := by
      rw [← hmap']
      exact hlarge
    exact Ζgk hH
      hzV hvV hyV huV hzv hxy hxu hyu hp hr hcard hlarge' hordinary
  · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
      intro he
      have hxMem : x ∈ ({y, u} : Edge α) := by rw [← he]; simp
      rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
      · exact hxy hxy'
      · exact hxu (Finset.mem_singleton.mp hxu')
    have hmap := Ζaj H V
      ({z, v} : Edge α) hcard hp hr hne
    have hmap' : Ζab H V ({z, v} : Edge α) =
        ({x, u} : Edge α) := by
      rw [hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hxu hxy (Ne.symm hyu))
    have hlarge' : 3 ≤ (Ζc H V ({x, u} : Edge α)).card := by
      rw [← hmap']
      exact hlarge
    have hxV : x ∈ V :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).1 (by simp)
    have hp' : ({y, x} : Edge α) ∈ Ζc H V ({z, v} : Edge α) := by
      simpa only [Finset.pair_comm] using hp
    exact Ζgk hH
      hzV hvV hxV huV hzv (Ne.symm hxy) hyu hxu hp' hr hcard
      hlarge' hordinary
theorem Ζlo
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ Ζau H V)
    (hlarge : 3 ≤ (Ζc H V (Ζab H V q)).card)
    (hordinary : ¬ Ζad H V q) :
    Ζp H V q ≤ 2 := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 :=
    (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).2
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have hsub := (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by
    rw [← he.2]
    exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hcard' : (Ζc H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hlarge' : 3 ≤
      (Ζc H V (Ζab H V ({e.1, e.2} : Edge α))).card := by
    rw [← he.2]
    exact hlarge
  have hordinary' : ¬ Ζad H V
      ({e.1, e.2} : Edge α) := by
    rw [← he.2]
    exact hordinary
  have hpoint := Ζln
    hH heV.1 heV.2 he.1 hcard' hlarge' hordinary'
  simpa [Ζp, hq2, e] using hpoint
end JSP523.Rank3
end
section
namespace JSP523.Rank3
section ReciprocalUsedCell
variable {α : Type*} [DecidableEq α]
theorem Ζlp
    {H : Family α} {V q : Edge α} (hH : Admissible H)
    (hq : q ∈ Ζau H V) :
    Ζab H V q ∈ Ζac H V := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 :=
    (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).2
  let e := Ζcf q hq2
  have he := Ζbq q hq2
  have hqCardRep :
      (Ζc H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (Ζbr H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    Ζdn hH heV.1 heV.2 he.1 hqCardRep
  have hxV : x ∈ V := by
    rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · have hpV := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1
      exact hpV (by simp)
    · have hpV := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1
      exact hpV (by simp)
  have htarget : Ζab H V q = ({y, u} : Edge α) ∨
      Ζab H V q = ({x, u} : Edge α) := by
    rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
        intro hh
        have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hyMem with hyx | hyu'
        · exact hxy hyx.symm
        · exact hyu (Finset.mem_singleton.mp hyu')
      have hmap := Ζaj H V
        ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
      left
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hyu (Ne.symm hxy) (Ne.symm hxu))
    · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
        intro hh
        have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
        · exact hxy hxy'
        · exact hxu (Finset.mem_singleton.mp hxu')
      have hmap := Ζaj H V
        ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
      right
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (Ζay hxu hxy (Ne.symm hyu))
  have hcard := Ζgx hH hq
  have hcommon : (Ζc H V (Ζab H V q)).Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  apply (Ζas H V _).mpr
  refine ⟨?_, hcommon⟩
  rcases htarget with htarget | htarget
  · rw [htarget]
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro a ha
      rcases Finset.mem_insert.mp ha with hay | hau
      · exact hay ▸ hyV
      · exact (Finset.mem_singleton.mp hau) ▸ huV
    · simp [hyu]
  · rw [htarget]
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro a ha
      rcases Finset.mem_insert.mp ha with hax | hau
      · exact hax ▸ hxV
      · exact (Finset.mem_singleton.mp hau) ▸ huV
    · simp [hxu]
end ReciprocalUsedCell
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
noncomputable def Ζbh
    (H : Family α) (V : Edge α) : Family α := by
  classical
  exact (Ζau H V).filter
    (fun q => Ζab H V q ∉ Ζau H V)
theorem Ζgy
    (H : Family α) (V : Edge α) :
    Ζbh H V ⊆ Ζau H V := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1
theorem Ζmr
    (H : Family α) (V : Edge α) :
    (∑ q ∈ Ζau H V, Ζp H V q) =
      (∑ q ∈ Ζba H V,
        Ζp H V q) +
      (∑ q ∈ Ζbh H V,
        Ζp H V q) := by
  classical
  simpa only [Ζba,
    Ζbh] using
    (Finset.sum_filter_add_sum_filter_not
      (Ζau H V)
      (fun q => Ζab H V q ∈ Ζau H V)
      (Ζp H V)).symm
theorem Ζpo
    (H : Family α) (V : Edge α) :
    (Ζau H V).card =
      (Ζba H V).card +
      (Ζbh H V).card := by
  classical
  simpa only [Ζba,
    Ζbh] using
    ((Ζau H V).card_filter_add_card_filter_not
      (fun q => Ζab H V q ∈ Ζau H V)).symm
theorem Ζpp
    {H : Family α} {V : Edge α} (hH : Admissible H)
    {q : Edge α} (hq : q ∈ Ζbh H V) :
    3 ≤ (Ζc H V (Ζab H V q)).card := by
  have hdouble := (Finset.mem_filter.mp hq).1
  have hnotDouble := (Finset.mem_filter.mp hq).2
  have htwo := Ζgx hH hdouble
  have hused := Ζlp hH hdouble
  have hnotTwo : (Ζc H V (Ζab H V q)).card ≠ 2 := by
    intro hcard
    exact hnotDouble (Finset.mem_filter.mpr ⟨hused, hcard⟩)
  omega
theorem Ζlg
    (H : Family α) (V : Edge α) (hH : Admissible H)
    (hLarge : ∀ q ∈ Ζbh H V,
      3 ≤ (Ζc H V (Ζab H V q)).card) :
    (∑ q ∈ Ζbh H V,
      Ζp H V q) ≤
      2 * ((Ζbh H V).card : ℚ) +
        Ζgr H V := by
  classical
  let N := Ζbh H V
  have hPoint (q : Edge α) (hq : q ∈ N) :
      Ζp H V q ≤
        2 + Ζck H V q := by
    apply Ζly
    intro hordinary
    have hdouble := Ζgy H V hq
    exact Ζlo
      hH hdouble (hLarge q hq) hordinary
  have hSum : (∑ q ∈ N, Ζp H V q) ≤
      2 * (N.card : ℚ) + ∑ q ∈ N, Ζck H V q := by
    calc
      (∑ q ∈ N, Ζp H V q) ≤
          ∑ q ∈ N, (2 + Ζck H V q) := by
        apply Finset.sum_le_sum
        exact hPoint
      _ = 2 * (N.card : ℚ) + ∑ q ∈ N, Ζck H V q := by
        simp [Finset.sum_add_distrib]
        ring
  have hSub : N ⊆ Ζac H V := by
    exact (Ζgy H V).trans
      (Finset.filter_subset _ _)
  have hExcess : (∑ q ∈ N, Ζck H V q) ≤ Ζgr H V := by
    rw [Ζrl]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun q _ _ => Ζtc H V q)
  linarith
theorem Ζkb
    (H : Family α) (V : Edge α) (hH : Admissible H)
    (hRegular :
      (∑ q ∈ Ζba H V,
        Ζp H V q) ≤
        2 * ((Ζba H V).card : ℚ))
    (hLarge : ∀ q ∈ Ζbh H V,
      3 ≤ (Ζc H V (Ζab H V q)).card) :
    Ζbo H V ≤
      4 * ((Ζcb H V).card : ℚ) +
      2 * ((Ζau H V).card : ℚ) + Ζgr H V := by
  have hPartition := Ζrk H V
  have hIncoming := Ζqg H V
  have hSingleton := Ζtj H V
  have hZero := Ζrc H V hH
  have hDouble := Ζlg
    H V hH hLarge
  have hSplit := Ζmr H V
  have hCard := Ζpo H V
  rw [hIncoming, hPartition, hSplit, hZero]
  rw [hCard]
  norm_num only [Nat.cast_add]
  linarith
theorem Ζqh
    (H : Family α) (V : Edge α) (hH : Admissible H) :
    Ζbo H V ≤
      4 * ((Ζcb H V).card : ℚ) +
      2 * ((Ζau H V).card : ℚ) + Ζgr H V := by
  exact Ζkb H V hH
    (Ζmn H V hH)
    (fun q hq => Ζpp hH hq)
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
private theorem Ζud
    (H : Family α) (V : Edge α) (z x y : α) :
    Ζm H V z x y = Ζm H V z y x := by
  ext t
  simp [Ζm, and_left_comm, and_comm]
def Ζih (H : JSP523.Family α) : Prop :=
  ∀ S : Edge α, S.card = 5 →
    let n := (Finset.filter (fun E : Edge α => E ⊆ S) H).card
    n ≠ 9 ∧ n ≠ 10
def Ζgl (a b c x u : α) : Family α :=
  {{a, b, c}, {a, b, u}, {a, c, x}, {a, x, u}, {b, c, x},
    {b, x, u}, {a, c, u}, {a, b, x}, {c, x, u}}
private def Ζvo : Finset (Finset (Fin 5)) :=
  {{0, 1, 2}, {0, 1, 4}, {0, 2, 3}, {0, 3, 4}, {1, 2, 3},
    {1, 3, 4}, {0, 2, 4}, {0, 1, 3}, {2, 3, 4}}
private theorem Ζvt : Ζvo.card = 9 := by
  decide
private def Ζvu (a b c x u : α) (i : Fin 5) : α :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c
    else if i = 3 then x else u
theorem Ζsl
    {a b c x u : α}
    (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x) (hau : a ≠ u)
    (hbc : b ≠ c) (hbx : b ≠ x) (hbu : b ≠ u)
    (hcx : c ≠ x) (hcu : c ≠ u) (hxu : x ≠ u) :
    (Ζgl a b c x u).card = 9 := by
  let f : Fin 5 → α := Ζvu a b c x u
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Ζvu]
  have hset : Ζgl a b c x u =
      Ζvo.image (fun e => e.image f) := by
    ext e
    simp [Ζgl, Ζvo, f, Ζvu]
  rw [hset, Finset.card_image_of_injective _ (Finset.image_injective hf)]
  exact Ζvt
structure Ζkc (H : JSP523.Family α) (V : Edge α)
    (a b c x u y v : α) : Prop where
  ab : Ζe H V b a = ({{x, c}, {x, u}} : Family α)
  cu : Ζe H V c u = ({{a, b}, {a, x}, {b, x}} : Family α)
  ac : Ζe H V c a = ({{y, b}, {y, v}} : Family α)
  bv : Ζe H V b v = ({{a, c}, {a, y}, {c, y}} : Family α)
private theorem Ζes
    {H : Family α} {V : Edge α} {z v : α} {p : Edge α}
    (hp : p ∈ Ζe H V z v) : p ∪ {z} ∈ H :=
  (Finset.mem_filter.mp hp).2.2.1
private theorem Ζcr
    {H : Family α} {V : Edge α} {z v : α} {p : Edge α}
    (hp : p ∈ Ζe H V z v) : p ∪ {v} ∈ H :=
  (Finset.mem_filter.mp hp).2.2.2
theorem Ζux
    {H : Family α} {V : Edge α} {a b c x u v : α}
    (hH : Admissible H) (hax : a ≠ x)
    (hbc : b ≠ c) (hcu : c ≠ u)
    (hbv : b ≠ v)
    (hbuLink : ({b, u} : Edge α) ∈ Ζe H V a x)
    (hcvLink : ({c, v} : Edge α) ∈ Ζe H V a x) :
    u = v := by
  by_contra huv
  have hmeet := Ζdu hH hax hbuLink hcvLink
  apply hmeet
  apply Finset.disjoint_left.mpr
  intro t htB htC
  have htB' : t = b ∨ t = u := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using htB
  have htC' : t = c ∨ t = v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using htC
  rcases htB' with htb | htu <;> rcases htC' with htc | htv
  · exact hbc (htb.symm.trans htc)
  · exact hbv (htb.symm.trans htv)
  · exact hcu (htc.symm.trans htu)
  · exact huv (htu.symm.trans htv)
theorem Ζrz
    {H : Family α} {V : Edge α} {a b c x u v : α}
    (hH : Admissible H)
    (hBook : Ζkc H V a b c x u x v)
    (hvV : v ∈ V)
    (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x)
    (hbx : b ≠ x) (hcx : c ≠ x) (hbc : b ≠ c)
    (hbu : b ≠ u) (hau : a ≠ u) (hxu : x ≠ u)
    (hcv : c ≠ v) (hav : a ≠ v) (hxv : x ≠ v)
    (hcu : c ≠ u) (hbv : b ≠ v) :
    u = v := by
  have habCu : ({a, b} : Edge α) ∈ Ζe H V c u := by
    rw [hBook.cu]
    simp
  have hxuBa : ({x, u} : Edge α) ∈ Ζe H V b a := by
    rw [hBook.ab]
    simp
  have hacBv : ({a, c} : Edge α) ∈ Ζe H V b v := by
    rw [hBook.bv]
    simp
  have hcxBv : ({c, x} : Edge α) ∈ Ζe H V b v := by
    rw [hBook.bv]
    simp
  have habu : ({a, b} : Edge α) ∪ {u} ∈ H :=
    Ζcr habCu
  have hbxu : ({x, u} : Edge α) ∪ {b} ∈ H :=
    Ζes hxuBa
  have hacv : ({a, c} : Edge α) ∪ {v} ∈ H :=
    Ζcr hacBv
  have hcxv : ({c, x} : Edge α) ∪ {v} ∈ H :=
    Ζcr hcxBv
  have hbV : b ∈ V := by
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp habCu).1).1 (by simp)
  have huV : u ∈ V := by
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hxuBa).1).1 (by simp)
  have hcV : c ∈ V := by
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hacBv).1).1 (by simp)
  have hbuV : ({b, u} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htb | htu
      · exact htb ▸ hbV
      · exact (Finset.mem_singleton.mp htu) ▸ huV
    · exact Finset.card_pair hbu
  have hcvV : ({c, v} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htc | htv
      · exact htc ▸ hcV
      · exact (Finset.mem_singleton.mp htv) ▸ hvV
    · exact Finset.card_pair hcv
  have hdisBu : Disjoint ({b, u} : Edge α) ({a, x} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro t ht hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht hp
    rcases ht with htb | htu <;> rcases hp with hta | htx
    · exact hab (hta.symm.trans htb)
    · exact hbx (htb.symm.trans htx)
    · exact hau (hta.symm.trans htu)
    · exact hxu (htx.symm.trans htu)
  have hdisCv : Disjoint ({c, v} : Edge α) ({a, x} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro t ht hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht hp
    rcases ht with htc | htv <;> rcases hp with hta | htx
    · exact hac (hta.symm.trans htc)
    · exact hcx (htc.symm.trans htx)
    · exact hav (hta.symm.trans htv)
    · exact hxv (htx.symm.trans htv)
  have hbuA : ({b, u} : Edge α) ∪ {a} = ({a, b} : Edge α) ∪ {u} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hbuX : ({b, u} : Edge α) ∪ {x} = ({x, u} : Edge α) ∪ {b} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hcvA : ({c, v} : Edge α) ∪ {a} = ({a, c} : Edge α) ∪ {v} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hcvX : ({c, v} : Edge α) ∪ {x} = ({c, x} : Edge α) ∪ {v} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hbuLink : ({b, u} : Edge α) ∈ Ζe H V a x :=
    Finset.mem_filter.mpr ⟨hbuV, hdisBu,
      hbuA.symm ▸ habu, hbuX.symm ▸ hbxu⟩
  have hcvLink : ({c, v} : Edge α) ∈ Ζe H V a x :=
    Finset.mem_filter.mpr ⟨hcvV, hdisCv,
      hcvA.symm ▸ hacv, hcvX.symm ▸ hcxv⟩
  exact Ζux hH hax hbc hcu hbv hbuLink hcvLink
theorem Ζgz
    {H : Family α} {V : Edge α} {z x y center : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzy : z ≠ y) (hxy : x ≠ y)
    (hmu : 2 ≤ (Ζm H V z x y).card)
    (hcenter : ∀ p ∈ Ζc H V ({x, y} : Edge α), center ∈ p) :
    center = z := by
  have hfiber := Ζaq H V hzV hzx hzy hxy
  have hbig : 1 < (Ζcu H V ({x, y} : Edge α) z).card := by
    rw [← hfiber]
    omega
  obtain ⟨t₁, ht₁, t₂, ht₂, htNe⟩ := Finset.one_lt_card.mp hbig
  have hpair₁ : ({z, t₁} : Edge α) ∈ Ζc H V ({x, y} : Edge α) :=
    (Finset.mem_filter.mp ht₁).2
  have hpair₂ : ({z, t₂} : Edge α) ∈ Ζc H V ({x, y} : Edge α) :=
    (Finset.mem_filter.mp ht₂).2
  have hznot₁ : t₁ ≠ z := by
    intro heq
    have hcard : ({z, t₁} : Edge α).card = 2 := by
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hpair₁).1).2
    simp [heq] at hcard
  have hznot₂ : t₂ ≠ z := by
    intro heq
    have hcard : ({z, t₂} : Edge α).card = 2 := by
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hpair₂).1).2
    simp [heq] at hcard
  have hc₁ := hcenter _ hpair₁
  have hc₂ := hcenter _ hpair₂
  by_contra hcz
  have hct₁ : center = t₁ := by
    have hmem : center = z ∨ center = t₁ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc₁
    rcases hmem with h | h
    · exact False.elim (hcz h)
    · exact h
  have hct₂ : center = t₂ := by
    have hmem : center = z ∨ center = t₂ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc₂
    rcases hmem with h | h
    · exact False.elim (hcz h)
    · exact h
  exact htNe (hct₁.symm.trans hct₂)
theorem Ζrm
    {H : Family α} {V : Edge α} {b c x y : α}
    (hH : Admissible H)
    (hbV : b ∈ V) (hcV : c ∈ V) (hxV : x ∈ V) (hyV : y ∈ V)
    (hbc : b ≠ c) (hbx : b ≠ x) (hby : b ≠ y)
    (hcx : c ≠ x) (hcy : c ≠ y) (hxy : x ≠ y)
    (hB : 4 ≤ (Ζm H V b x y).card)
    (hC : 4 ≤ (Ζm H V c x y).card) : False := by
  have hq : ({x, y} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htx | hty
      · exact htx ▸ hxV
      · exact (Finset.mem_singleton.mp hty) ▸ hyV
    · exact Finset.card_pair hxy
  have hBfiber := Ζaq H V hbV
    hbx hby hxy
  have hClarge : 3 < (Ζc H V ({x, y} : Edge α)).card := by
    have hle := Ζcv
      H V ({x, y} : Edge α) b
    rw [← hBfiber] at hle
    omega
  obtain ⟨center, hcenter, hunique⟩ :=
    Ζgu hH hq hClarge
  have hcenterB := Ζgz
    hbV hbx hby hxy (by omega) hcenter
  have hcenterC := Ζgz
    hcV hcx hcy hxy (by omega) hcenter
  exact hbc (hcenterB.symm.trans hcenterC)
theorem Ζet
    {H : Family α} {V : Edge α} {z x c u y : α}
    (hsource : ({x, c} : Edge α) ∈ Ζaf H V z)
    (hxc : x ≠ c) (hpositive : 0 < Ζo H V z x c)
    (huWeak : u ∈ Ζav H V z x c)
    (hcy : ({c, y} : Edge α) ∈ Ζaf H V z)
    (hyx : y ≠ x) :
    4 ≤ (Ζm H V z x y).card := by
  by_contra hlarge
  have hsmall : (Ζm H V z x y).card ≤ 3 := by omega
  have hcyNe : c ≠ y := by
    intro h
    have hcard : ({c, y} : Edge α).card = 2 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hcy).1).2
    simp [h] at hcard
  have hyNeighbor : y ∈ Ζk H V z c :=
    (Ζeh H V hcy hcyNe).1
  have hyWeak : y ∈ Ζbs H V z x c := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_erase.mpr ⟨hyx, hyNeighbor⟩
    · exact hsmall
  have hleft : 0 < (Ζbs H V z x c).card :=
    Finset.card_pos.mpr ⟨y, hyWeak⟩
  have hright : 0 < (Ζav H V z x c).card :=
    Finset.card_pos.mpr ⟨u, huWeak⟩
  have hcount := Ζkh
    H V hsource hxc hpositive
  omega
theorem Ζoj
    {H : Family α} {V : Edge α} {a b c x u y v : α}
    (hH : Admissible H)
    (hBook : Ζkc H V a b c x u y v)
    (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hxV : x ∈ V) (hyV : y ∈ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxb : x ≠ b) (hxc : x ≠ c)
    (huc : u ≠ c) (hxu : x ≠ u)
    (hyb : y ≠ b) (hyc : y ≠ c) (hxy : x ≠ y)
    (hvb : v ≠ b) (hyv : y ≠ v)
    (hposB : 0 < Ζo H V b x c)
    (hposC : 0 < Ζo H V c y b) : False := by
  have hxcLink : ({x, c} : Edge α) ∈ Ζe H V b a := by
    rw [hBook.ab]
    simp
  have hxuLink : ({x, u} : Edge α) ∈ Ζe H V b a := by
    rw [hBook.ab]
    simp
  have hybLink : ({y, b} : Edge α) ∈ Ζe H V c a := by
    rw [hBook.ac]
    simp
  have hyvLink : ({y, v} : Edge α) ∈ Ζe H V c a := by
    rw [hBook.ac]
    simp
  have hcyLink : ({c, y} : Edge α) ∈ Ζe H V b v := by
    rw [hBook.bv]
    simp
  have hbxLink : ({b, x} : Edge α) ∈ Ζe H V c u := by
    rw [hBook.cu]
    simp
  have hxcRoot : ({x, c} : Edge α) ∈ Ζaf H V b :=
    Ζat H V hxcLink
  have hybRoot : ({y, b} : Edge α) ∈ Ζaf H V c :=
    Ζat H V hybLink
  have hcyRoot : ({c, y} : Edge α) ∈ Ζaf H V b :=
    Ζat H V hcyLink
  have hbxRoot : ({b, x} : Edge α) ∈ Ζaf H V c :=
    Ζat H V hbxLink
  have huWeak : u ∈ Ζav H V b x c :=
    Ζdj hH hbV haV
      (Ne.symm hab) hxc hxu (Ne.symm huc) hxcLink hxuLink
  have hvWeak : v ∈ Ζav H V c y b :=
    Ζdj hH hcV haV
      (Ne.symm hac) hyb hyv (Ne.symm hvb) hybLink hyvLink
  have hmuB : 4 ≤ (Ζm H V b x y).card :=
    Ζet
      hxcRoot hxc hposB huWeak hcyRoot (Ne.symm hxy)
  have hmuC : 4 ≤ (Ζm H V c y x).card :=
    Ζet
      hybRoot hyb hposC hvWeak hbxRoot hxy
  have hmuC' : 4 ≤ (Ζm H V c x y).card := by
    simpa only [Ζud] using hmuC
  exact Ζrm hH hbV hcV hxV hyV
    hbc (Ne.symm hxb) (Ne.symm hyb) (Ne.symm hxc) (Ne.symm hyc)
    hxy hmuB hmuC'
theorem Ζqi
    {H : Family α} {V : Edge α} {a b c x u y v : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hNoBlock : Ζih H)
    (hBook : Ζkc H V a b c x u y v)
    (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hxV : x ∈ V) (_huV : u ∈ V) (hyV : y ∈ V) (hvV : v ∈ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hau : a ≠ u) (hbu : b ≠ u) (hcu : c ≠ u) (hxu : x ≠ u)
    (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c) (hyv : y ≠ v)
    (hposB : 0 < Ζo H V b x c)
    (hposC : 0 < Ζo H V c y b) : False := by
  by_cases hxyEq : x = y
  · subst y
    have huv : u = v := Ζrz hH hBook hvV
      hab hac hax hbx hcx hbc hbu hau hxu (Ne.symm hvc)
      (Ne.symm hva) hyv hcu (Ne.symm hvb)
    subst v
    have hOverlapTripleCard : (Ζgl a b c x u).card = 9 :=
      Ζsl hab hac hax hau hbc hbx hbu hcx hcu hxu
    have h_ab_c : ({a, b} : Edge α) ∈ Ζe H V c u := by
      rw [hBook.cu]
      simp
    have h_ab_u := Ζcr h_ab_c
    have h_ax_c : ({a, x} : Edge α) ∈ Ζe H V c u := by
      rw [hBook.cu]
      simp
    have h_ax_u := Ζcr h_ax_c
    have h_bx_c : ({b, x} : Edge α) ∈ Ζe H V c u := by
      rw [hBook.cu]
      simp
    have h_bx_u := Ζcr h_bx_c
    have h_ac_v : ({a, c} : Edge α) ∈ Ζe H V b u := by
      rw [hBook.bv]
      simp
    have h_ax_v : ({a, x} : Edge α) ∈ Ζe H V b u := by
      rw [hBook.bv]
      simp
    have h_cx_v : ({c, x} : Edge α) ∈ Ζe H V b u := by
      rw [hBook.bv]
      simp
    have h₁ : ({a, b, c} : Edge α) ∈ H := by
      simpa using Ζes h_ab_c
    have h₂ : ({a, b, u} : Edge α) ∈ H := by
      simpa using h_ab_u
    have h₃ : ({a, c, x} : Edge α) ∈ H := by
      have hs : ({a, x} : Edge α) ∪ {c} = {a, c, x} := by
        ext t
        simp [or_comm]
      rw [← hs]
      exact Ζes h_ax_c
    have h₄ : ({a, x, u} : Edge α) ∈ H := by
      simpa using h_ax_u
    have h₅ : ({b, c, x} : Edge α) ∈ H := by
      have hs : ({b, x} : Edge α) ∪ {c} = {b, c, x} := by
        ext t
        simp [or_comm]
      rw [← hs]
      exact Ζes h_bx_c
    have h₆ : ({b, x, u} : Edge α) ∈ H := by
      simpa using h_bx_u
    have h₇ : ({a, c, u} : Edge α) ∈ H := by
      simpa using Ζcr h_ac_v
    have h₈ : ({a, b, x} : Edge α) ∈ H := by
      have hs : ({a, x} : Edge α) ∪ {b} = {a, b, x} := by
        ext t
        simp [or_comm]
      rw [← hs]
      exact Ζes h_ax_v
    have h₉ : ({c, x, u} : Edge α) ∈ H := by
      simpa using Ζcr h_cx_v
    let S : Edge α := {a, b, c, x, u}
    let T : Family α :=
      {{a, b, c}, {a, b, u}, {a, c, x}, {a, x, u}, {b, c, x},
        {b, x, u}, {a, c, u}, {a, b, x}, {c, x, u}}
    have hScard : S.card = 5 := by
      simp [S, hab, hac, hbc, hax, hbx, hcx, hau, hbu, hcu, hxu]
    have hTcard : T.card = 9 := by
      simpa [T, Ζgl] using hOverlapTripleCard
    have tripleSubset (r s t : α) (hr : r ∈ S) (hs : s ∈ S) (ht : t ∈ S) :
        ({r, s, t} : Edge α) ⊆ S := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw
      · exact hw ▸ hr
      · exact hw ▸ hs
      · exact hw ▸ ht
    have hTsub : T ⊆ (Finset.filter (fun E : Edge α => E ⊆ S) H) := by
      intro E hE
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with hE | hE | hE | hE | hE | hE | hE | hE | hE
      · subst E; exact Finset.mem_filter.mpr ⟨h₁, tripleSubset a b c (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₂, tripleSubset a b u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₃, tripleSubset a c x (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₄, tripleSubset a x u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₅, tripleSubset b c x (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₆, tripleSubset b x u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₇, tripleSubset a c u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₈, tripleSubset a b x (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₉, tripleSubset c x u (by simp [S]) (by simp [S]) (by simp [S])⟩
    have hCountLower : 9 ≤ (Finset.filter (fun E : Edge α => E ⊆ S) H).card := by
      rw [← hTcard]
      exact Finset.card_le_card hTsub
    have hFilteredSub : Finset.filter (fun E : Edge α => E ⊆ S) H ⊆
        S.powersetCard 3 := by
      intro E hE
      obtain ⟨hEH, hES⟩ := Finset.mem_filter.mp hE
      exact Finset.mem_powersetCard.mpr ⟨hES, hUniform hEH⟩
    have hCountUpper : (Finset.filter (fun E : Edge α => E ⊆ S) H).card ≤ 10 := by
      calc
        (Finset.filter (fun E : Edge α => E ⊆ S) H).card ≤ (S.powersetCard 3).card :=
          Finset.card_le_card hFilteredSub
        _ = 10 := by rw [Finset.card_powersetCard, hScard]; norm_num [Nat.choose]
    have hne := hNoBlock S hScard
    dsimp at hne
    omega
  · have hxy : x ≠ y := fun heq => hxyEq heq
    exact Ζoj hH hBook haV hbV hcV hxV hyV
      hab hac hbc (Ne.symm hbx) (Ne.symm hcx) (Ne.symm hcu) hxu hyb hyc hxy hvb hyv
      hposB hposC
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 400000 in
private theorem Ζfp
    (H : Family α) (V : Edge α) {z v : α} (hzv : z ≠ v) :
    Ζc H V ({z, v} : Edge α) = Ζe H V z v := by
  ext p
  exact Ζr H V hzv p
set_option maxHeartbeats 400000 in
private theorem Ζtd
    {a b c z v : α}
    (hzv : z ≠ v)
    (hsub : ({z, v} : Edge α) ⊆ {a, b, c})
    (hne : ({z, v} : Edge α) ≠ {a, b}) :
    ({z, v} : Edge α) = {a, c} ∨ ({z, v} : Edge α) = {b, c} := by
  have hz : z = a ∨ z = b ∨ z = c := by
    have hm : z ∈ ({a, b, c} : Edge α) := hsub (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hv : v = a ∨ v = b ∨ v = c := by
    have hm : v ∈ ({a, b, c} : Edge α) := hsub (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hz with hza | hzb | hzc <;>
    rcases hv with hva | hvb | hvc
  · exact False.elim (hzv (hza.trans hva.symm))
  · exact False.elim (hne (by ext t; simp [hza, hvb]))
  · left; ext t; simp [hza, hvc]
  · exact False.elim (hne (by ext t; simp [hzb, hva]; tauto))
  · exact False.elim (hzv (hzb.trans hvb.symm))
  · right; ext t; simp [hzb, hvc]
  · left; ext t; simp [hzc, hva, or_comm]
  · right; ext t; simp [hzc, hvb, or_comm]
  · exact False.elim (hzv (hzc.trans hvc.symm))
set_option maxHeartbeats 400000 in
private theorem Ζuy
    {a b c d : α} (hcd : c ≠ d)
    (hpair : ({a, b} : Edge α) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a = c ∨ a = d := by
    have hm : a ∈ ({c, d} : Edge α) := by rw [← hpair]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with hac | had
  · left
    refine ⟨hac, ?_⟩
    have hm : d ∈ ({a, b} : Edge α) := by rw [hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hda | hdb
    · exact False.elim (hcd (hac ▸ hda).symm)
    · exact hdb.symm
  · right
    refine ⟨had, ?_⟩
    have hm : c ∈ ({a, b} : Edge α) := by rw [hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hca | hcb
    · exact False.elim (hcd (hca.trans had))
    · exact hcb.symm
set_option maxHeartbeats 400000 in
structure Ζt
    (H : Family α) (V : Edge α) (q : Edge α) where
  z : α
  v : α
  x : α
  y : α
  u : α
  hzV : z ∈ V
  hvV : v ∈ V
  hxV : x ∈ V
  hyV : y ∈ V
  huV : u ∈ V
  hq : q = ({z, v} : Edge α)
  hbook : Ζc H V q =
    ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α)
  hreciprocal : Ζc H V ({y, u} : Edge α) =
    ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α)
set_option maxHeartbeats 400000 in
def Ζbg
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    Ζt H V q := by
  refine ⟨d.v, d.z, d.x, d.y, d.u, d.hvV, d.hzV, d.hxV, d.hyV, d.huV, ?_, ?_, ?_⟩
  · simpa [Finset.pair_comm] using d.hq
  · rw [d.hbook]
  · rw [d.hreciprocal]
    ext p
    simp [Finset.pair_comm, or_comm, or_left_comm, or_assoc]
set_option maxHeartbeats 400000 in
def Ζby
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    Ζt H V q := by
  refine ⟨d.z, d.v, d.x, d.u, d.y, d.hzV, d.hvV, d.hxV, d.huV, d.hyV,
    d.hq, ?_, ?_⟩
  · rw [d.hbook]
    ext p
    simp [Finset.pair_comm, or_comm]
  · have hp : ({d.u, d.y} : Edge α) = {d.y, d.u} := by
      simp [Finset.pair_comm]
    rw [hp, d.hreciprocal]
set_option maxHeartbeats 400000 in
noncomputable def Ζah
    (H : Family α) (V : Edge α) (q : Edge α)
    (hq : Ζad H V q) :
    Ζt H V q := by
  classical
  exact Classical.choice (show Nonempty (Ζt H V q) from by
    rcases hq with ⟨z, v, x, y, u, hzV, hvV, hxV, hyV, huV, hqEq,
      hbook, hreciprocal⟩
    exact ⟨⟨z, v, x, y, u, hzV, hvV, hxV, hyV, huV, hqEq,
      hbook, hreciprocal⟩⟩)
set_option maxHeartbeats 400000 in
noncomputable def Ζx
    (H : Family α) (V : Edge α) (q E : Edge α) : ℚ := by
  classical
  by_cases hq : Ζad H V q
  · let d := Ζah H V q hq
    exact if E = ({d.z, d.v, d.y} : Edge α) then
      min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z)
    else if E = ({d.z, d.v, d.u} : Edge α) then
      min (Ζh H V d.z d.x d.u d.v)
        (Ζh H V d.v d.x d.u d.z)
    else 0
  · exact 0
set_option maxHeartbeats 400000 in
theorem Ζag
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    d.z ≠ d.v ∧ d.x ≠ d.y ∧ d.x ≠ d.u ∧ d.y ≠ d.u := by
  have hp : ({d.x, d.y} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  have hpCard : ({d.x, d.y} : Edge α).card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  have hxy : d.x ≠ d.y := Finset.card_pair_eq_two_iff.mp hpCard
  have hqDistinct : d.z ≠ d.v := by
    obtain ⟨s, hs, t, ht, hst, _, _, _⟩ := (Finset.mem_filter.mp hp).2
    have hs' : s = d.z ∨ s = d.v := by
      rw [d.hq] at hs
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
    have ht' : t = d.z ∨ t = d.v := by
      rw [d.hq] at ht
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ht
    rcases hs' with hsZ | hsV <;> rcases ht' with htZ | htV
    · exact False.elim (hst (hsZ.trans htZ.symm))
    · intro hEq
      exact hst (hsZ.trans (hEq.trans htV.symm))
    · intro hEq
      exact hst (hsV.trans (hEq.symm.trans htZ.symm))
    · exact False.elim (hst (hsV.trans htV.symm))
  have hpU : ({d.x, d.u} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  have huCard : ({d.x, d.u} : Edge α).card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpU).1).2
  have hxu : d.x ≠ d.u := Finset.card_pair_eq_two_iff.mp huCard
  have hpRecip : ({d.z, d.v} : Edge α) ∈
      Ζc H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  have hyu : d.y ≠ d.u := by
    obtain ⟨s, hs, t, ht, hst, _, _, _⟩ := (Finset.mem_filter.mp hpRecip).2
    have hs' : s = d.y ∨ s = d.u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
    have ht' : t = d.y ∨ t = d.u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ht
    rcases hs' with hsY | hsU <;> rcases ht' with htY | htU
    · exact False.elim (hst (hsY.trans htY.symm))
    · intro hEq
      exact hst (hsY.trans (hEq.trans htU.symm))
    · intro hEq
      exact hst (hsU.trans (hEq.symm.trans htY.symm))
    · exact False.elim (hst (hsU.trans htU.symm))
  exact ⟨hqDistinct, hxy, hxu, hyu⟩
set_option maxHeartbeats 400000 in
private theorem Ζkg
    {a b c d : α} (h : Disjoint ({a, b} : Edge α) ({c, d} : Edge α)) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have hdis := Finset.disjoint_left.mp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    subst c
    have hna : a ∉ ({a, d} : Edge α) := hdis (a := a) (by simp)
    exact hna (by simp)
  · intro he
    subst d
    have hna : a ∉ ({c, a} : Edge α) := hdis (a := a) (by simp)
    exact hna (by simp)
  · intro he
    subst c
    have hnb : b ∉ ({b, d} : Edge α) := hdis (a := b) (by simp)
    exact hnb (by simp)
  · intro he
    subst d
    have hnb : b ∉ ({c, b} : Edge α) := hdis (a := b) (by simp)
    exact hnb (by simp)
set_option maxHeartbeats 400000 in
theorem Ζan
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    d.z ≠ d.v ∧ d.z ≠ d.x ∧ d.z ≠ d.y ∧ d.z ≠ d.u ∧
    d.v ≠ d.x ∧ d.v ≠ d.y ∧ d.v ≠ d.u ∧
    d.x ≠ d.y ∧ d.x ≠ d.u ∧ d.y ≠ d.u := by
  obtain ⟨hzv, hxy, hxu, hyu⟩ := Ζag d
  have hxyLink : ({d.x, d.y} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  have hxuLink : ({d.x, d.u} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  have hxzRecip : ({d.x, d.z} : Edge α) ∈
      Ζc H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  have hxvRecip : ({d.x, d.v} : Edge α) ∈
      Ζc H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  obtain ⟨_, _, _, _, _, hbookXY, _, _⟩ := (Finset.mem_filter.mp hxyLink).2
  obtain ⟨_, _, _, _, _, hbookXU, _, _⟩ := (Finset.mem_filter.mp hxuLink).2
  obtain ⟨_, _, _, _, _, hrecipXZ, _, _⟩ := (Finset.mem_filter.mp hxzRecip).2
  obtain ⟨_, _, _, _, _, hrecipXV, _, _⟩ := (Finset.mem_filter.mp hxvRecip).2
  have hbookXY' : Disjoint ({d.x, d.y} : Edge α) ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hbookXY
  have hbookXU' : Disjoint ({d.x, d.u} : Edge α) ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hbookXU
  have hbxy := Ζkg hbookXY'
  have hbxu := Ζkg hbookXU'
  have hrxz := Ζkg hrecipXZ
  have hrxv := Ζkg hrecipXV
  exact ⟨hzv, hbxy.1.symm, hrxz.2.2.1, hrxz.2.2.2,
    hbxy.2.1.symm, hrxv.2.2.1, hrxv.2.2.2,
    hxy, hxu, hyu⟩
set_option maxHeartbeats 400000 in
theorem Ζlz
    {H : Family α} {V q₁ q₂ : Edge α}
    (d₁ : Ζt H V q₁)
    (d₂ : Ζt H V q₂)
    (hneq : q₁ ≠ q₂)
    (hsub : q₂ ⊆ ({d₁.z, d₁.v, d₁.y} : Edge α)) :
    ({d₂.z, d₂.v} : Edge α) = {d₁.z, d₁.y} ∨
      ({d₂.z, d₂.v} : Edge α) = {d₁.v, d₁.y} := by
  have hsub' : ({d₂.z, d₂.v} : Edge α) ⊆
      ({d₁.z, d₁.v, d₁.y} : Edge α) := by
    simpa only [d₂.hq] using hsub
  have hne : ({d₂.z, d₂.v} : Edge α) ≠ ({d₁.z, d₁.v} : Edge α) := by
    intro he
    apply hneq
    simpa only [d₁.hq, d₂.hq] using he.symm
  have hzv := (Ζag d₂).1
  exact Ζtd hzv hsub' hne
set_option maxHeartbeats 400000 in
theorem Ζpq
    {H : Family α} {V q₁ q₂ : Edge α}
    (d₁ : Ζt H V q₁)
    (d₂ : Ζt H V q₂)
    (hneq : q₁ ≠ q₂)
    (hsub : q₂ ⊆ ({d₁.z, d₁.v, d₁.y} : Edge α)) :
    (d₂.z = d₁.z ∧ d₂.v = d₁.y) ∨
    (d₂.z = d₁.y ∧ d₂.v = d₁.z) ∨
    (d₂.z = d₁.v ∧ d₂.v = d₁.y) ∨
    (d₂.z = d₁.y ∧ d₂.v = d₁.v) := by
  have hzv := (Ζag d₂).1
  rcases Ζlz d₁ d₂ hneq hsub with hleft | hright
  · have hzy : d₁.z ≠ d₁.y := by
      intro heq
      have hcard := congrArg Finset.card hleft
      rw [heq] at hcard
      simp [Finset.card_pair hzv] at hcard
    rcases Ζuy hzy hleft with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hvy : d₁.v ≠ d₁.y := by
      intro heq
      have hcard := congrArg Finset.card hright
      rw [heq] at hcard
      simp [Finset.card_pair hzv] at hcard
    rcases Ζuy hvy hright with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
set_option maxHeartbeats 400000 in
theorem Ζhh
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    (Ζc H V q).card = 2 := by
  obtain ⟨_, hxy, hxu, hyu⟩ := Ζag d
  rw [d.hbook]
  apply Finset.card_pair
  intro he
  have hyMem : d.y ∈ ({d.x, d.u} : Edge α) := by
    rw [← he]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
  rcases hyMem with hyx | hyu'
  · exact hxy hyx.symm
  · exact hyu hyu'
set_option maxHeartbeats 400000 in
theorem Ζhu
    {H : Family α} {V q₁ q₂ : Edge α} {a b c x u y v : α}
    (d₁ : Ζt H V q₁)
    (d₂ : Ζt H V q₂)
    (hq₁ : q₁ = ({a, b} : Edge α))
    (hq₂ : q₂ = ({a, c} : Edge α))
    (hz₁ : d₁.z = a) (hv₁ : d₁.v = b) (hx₁ : d₁.x = x)
    (hy₁ : d₁.y = c) (hu₁ : d₁.u = u)
    (hz₂ : d₂.z = a) (hv₂ : d₂.v = c) (hx₂ : d₂.x = y)
    (hy₂ : d₂.y = b) (hu₂ : d₂.u = v) :
    Ζkc H V a b c x u y v := by
  have hab : a ≠ b := by
    simpa [hz₁, hv₁] using (Ζan d₁).1
  have hac : a ≠ c := by
    simpa [hz₂, hv₂] using (Ζan d₂).1
  have hcu : c ≠ u := by
    rcases Ζan d₁ with
      ⟨_, _, _, _, _, _, _, _, _, hyu⟩
    simpa [hy₁, hu₁] using hyu
  have h₁ : Ζc H V ({a, b} : Edge α) =
      ({{x, c}, {x, u}} : Family α) := by
    calc
      Ζc H V ({a, b} : Edge α) = Ζc H V q₁ := by rw [← hq₁]
      _ = ({{d₁.x, d₁.y}, {d₁.x, d₁.u}} : Family α) := d₁.hbook
      _ = ({{x, c}, {x, u}} : Family α) := by simp [hx₁, hy₁, hu₁]
  have h₂ : Ζc H V ({c, u} : Edge α) =
      ({{a, b}, {a, x}, {b, x}} : Family α) := by
    calc
      Ζc H V ({c, u} : Edge α) =
          Ζc H V ({d₁.y, d₁.u} : Edge α) := by simp [hy₁, hu₁]
      _ = ({{a, b}, {a, x}, {b, x}} : Family α) := by
        rw [d₁.hreciprocal]
        ext p
        simp [Finset.pair_comm, hz₁, hv₁, hx₁]; tauto
  have h₃ : Ζc H V ({a, c} : Edge α) =
      ({{y, b}, {y, v}} : Family α) := by
    calc
      Ζc H V ({a, c} : Edge α) = Ζc H V q₂ := by rw [← hq₂]
      _ = ({{d₂.x, d₂.y}, {d₂.x, d₂.u}} : Family α) := d₂.hbook
      _ = ({{y, b}, {y, v}} : Family α) := by simp [hx₂, hy₂, hu₂]
  have h₄ : Ζc H V ({b, v} : Edge α) =
      ({{a, c}, {a, y}, {c, y}} : Family α) := by
    calc
      Ζc H V ({b, v} : Edge α) =
          Ζc H V ({d₂.y, d₂.u} : Edge α) := by simp [hy₂, hu₂]
      _ = ({{a, c}, {a, y}, {c, y}} : Family α) := by
        rw [d₂.hreciprocal]
        ext p
        simp [Finset.pair_comm, hz₂, hv₂, hx₂]; tauto
  have hab' : Ζc H V ({a, b} : Edge α) =
      Ζe H V b a := by
    calc
      Ζc H V ({a, b} : Edge α) = Ζc H V ({b, a} : Edge α) := by
        simp [Finset.pair_comm]
      _ = Ζe H V b a := Ζfp H V hab.symm
  have hcu' : Ζc H V ({c, u} : Edge α) =
      Ζe H V c u := Ζfp H V hcu
  have hac' : Ζc H V ({a, c} : Edge α) =
      Ζe H V c a := by
    calc
      Ζc H V ({a, c} : Edge α) = Ζc H V ({c, a} : Edge α) := by
        simp [Finset.pair_comm]
      _ = Ζe H V c a := Ζfp H V hac.symm
  have hbv' : Ζc H V ({b, v} : Edge α) =
    Ζe H V b v := by
    have hne : b ≠ v := by
      rcases Ζan d₂ with
        ⟨_, _, _, _, _, _, _, _, _, hne⟩
      simpa [hy₂, hu₂] using hne
    exact Ζfp H V hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hab']
    exact h₁
  · rw [← hcu']
    simpa [Finset.pair_comm] using h₂
  · rw [← hac']
    exact h₃
  · rw [← hbv']
    exact h₄
set_option maxHeartbeats 400000 in
theorem Ζma
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    Ζp H V q = Ζak H V d.z d.v := by
  obtain ⟨hzv, _, _, _⟩ := Ζag d
  simpa only [d.hq] using Ζcj H V hzv
set_option maxHeartbeats 400000 in
theorem Ζkm
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    Ζak H V d.z d.v =
      (Ζw H V d.z d.v ({d.x, d.y} : Edge α) +
        Ζw H V d.v d.z ({d.x, d.y} : Edge α)) +
      (Ζw H V d.z d.v ({d.x, d.u} : Edge α) +
        Ζw H V d.v d.z ({d.x, d.u} : Edge α)) := by
  obtain ⟨_, hxy, hxu, hyu⟩ := Ζag d
  have hp₁ : ({d.x, d.y} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  have hp₂ : ({d.x, d.u} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  have hpNe : ({d.x, d.y} : Edge α) ≠ ({d.x, d.u} : Edge α) := by
    intro he
    have hyMem : d.y ∈ ({d.x, d.u} : Edge α) := by
      rw [← he]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
    rcases hyMem with hyx | hyu'
    · exact hxy hyx.symm
    · exact hyu hyu'
  have hp₁' : ({d.x, d.y} : Edge α) ∈
      Ζc H V ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hp₁
  have hp₂' : ({d.x, d.u} : Edge α) ∈
      Ζc H V ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hp₂
  have hcard' : (Ζc H V ({d.z, d.v} : Edge α)).card = 2 := by
    simpa only [d.hq] using Ζhh d
  exact Ζee H V hp₁' hp₂' hpNe hcard'
set_option maxHeartbeats 400000 in
theorem Ζjp
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    Ζp H V q =
      (Ζh H V d.z d.x d.y d.v +
        Ζh H V d.v d.x d.y d.z) +
      (Ζh H V d.z d.x d.u d.v +
        Ζh H V d.v d.x d.u d.z) := by
  rw [Ζma,
    Ζkm]
  obtain ⟨_, hxy, hxu, _⟩ := Ζag d
  have h₁ := Ζaa H V
    ({d.x, d.y} : Edge α) d.z d.v d.x d.y (Finset.card_pair hxy) rfl
  have h₂ := Ζaa H V
    ({d.x, d.y} : Edge α) d.v d.z d.x d.y (Finset.card_pair hxy) rfl
  have h₃ := Ζaa H V
    ({d.x, d.u} : Edge α) d.z d.v d.x d.u (Finset.card_pair hxu) rfl
  have h₄ := Ζaa H V
    ({d.x, d.u} : Edge α) d.v d.z d.x d.u (Finset.card_pair hxu) rfl
  rw [h₁, h₂, h₃, h₄]
set_option maxHeartbeats 400000 in
theorem Ζup
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < Ζx H V q E) :
    ∃ d : Ζt H V q,
      (E = ({d.z, d.v, d.y} : Edge α) ∧
        0 < Ζh H V d.z d.x d.y d.v ∧
        0 < Ζh H V d.v d.x d.y d.z) ∨
      (E = ({d.z, d.v, d.u} : Edge α) ∧
        0 < Ζh H V d.z d.x d.u d.v ∧
        0 < Ζh H V d.v d.x d.u d.z) := by
  classical
  by_cases hq : Ζad H V q
  · let d := Ζah H V q hq
    simp only [Ζx, Ζom hq] at hpos
    change 0 < (if E = ({d.z, d.v, d.y} : Edge α) then
      min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z)
      else if E = ({d.z, d.v, d.u} : Edge α) then
        min (Ζh H V d.z d.x d.u d.v)
          (Ζh H V d.v d.x d.u d.z)
      else 0) at hpos
    by_cases hy : E = ({d.z, d.v, d.y} : Edge α)
    · rw [Ζie hy] at hpos
      exact ⟨d, Or.inl ⟨hy, (lt_min_iff.mp hpos).1,
        (lt_min_iff.mp hpos).2⟩⟩
    · by_cases hu : E = ({d.z, d.v, d.u} : Edge α)
      · rw [Ζdp hy, Ζie hu] at hpos
        exact ⟨d, Or.inr ⟨hu, (lt_min_iff.mp hpos).1,
          (lt_min_iff.mp hpos).2⟩⟩
      · rw [Ζdp hy, Ζdp hu] at hpos
        norm_num at hpos
  · simp [Ζx, hq] at hpos
set_option maxHeartbeats 400000 in
theorem Ζng
    (H : Family α) (V : Edge α) (z x y v : α)
    (hpos : 0 < Ζh H V z x y v) :
    0 < Ζq H V z x y := by
  classical
  let N := Ζb H V ({x, y} : Edge α)
  have hv : v ∈ N.erase z := by
    by_contra hvNot
    simp [Ζh, N, hvNot] at hpos
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hcardPos : 0 < N.card := Finset.card_pos.mpr ⟨v, hvN⟩
  have hdegree : 2 ≤ N.card := by
    by_contra h
    have hcardOne : N.card = 1 := by omega
    have hzero : Ζh H V z x y v = 0 := by
      simp [Ζh, Ζao, hv, N, hcardOne]
    rw [hzero] at hpos
    norm_num at hpos
  have hden : 0 < (N.card : ℚ) - 1 := by
    have hcast : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  have hw : 0 < Ζq H V z x y := by
    apply (div_pos_iff_of_pos_right hden).mp
    simpa [Ζh, Ζao, hv, N] using hpos
  exact hw
set_option maxHeartbeats 400000 in
theorem Ζbl
    (H : Family α) (V : Edge α) (z x y v : α)
    (hpos : 0 < Ζh H V z x y v) :
    0 < Ζo H V z x y := by
  have hw := Ζng H V z x y v hpos
  simpa [Ζq, max_eq_left (le_of_lt hw)] using hw
set_option maxHeartbeats 400000 in
theorem Ζrn
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < Ζx H V q E) :
    ∃ d : Ζt H V q,
      (E = ({d.z, d.v, d.y} : Edge α) ∧
        0 < Ζo H V d.z d.x d.y ∧
        0 < Ζo H V d.v d.x d.y) ∨
      (E = ({d.z, d.v, d.u} : Edge α) ∧
        0 < Ζo H V d.z d.x d.u ∧
        0 < Ζo H V d.v d.x d.u) := by
  obtain ⟨d, hcases⟩ := Ζup H V q E hpos
  rcases hcases with ⟨hE, hz, hv⟩ | ⟨hE, hz, hv⟩
  · exact ⟨d, Or.inl ⟨hE,
      Ζbl H V _ _ _ _ hz,
      Ζbl H V _ _ _ _ hv⟩⟩
  · exact ⟨d, Or.inr ⟨hE,
      Ζbl H V _ _ _ _ hz,
      Ζbl H V _ _ _ _ hv⟩⟩
set_option maxHeartbeats 400000 in
theorem Ζio
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hpos : 0 < Ζx H V q E) :
    ∃ d : Ζt H V q,
      E = ({d.z, d.v, d.y} : Edge α) ∧
        0 < Ζo H V d.z d.x d.y ∧
        0 < Ζo H V d.v d.x d.y := by
  obtain ⟨d, hcases⟩ := Ζrn H V q E hpos
  rcases hcases with ⟨hE, hz, hv⟩ | ⟨hE, hz, hv⟩
  · exact ⟨d, hE, hz, hv⟩
  · refine ⟨Ζby d, ?_, ?_, ?_⟩
    · simpa [Ζby] using hE
    · simpa [Ζby] using hz
    · simpa [Ζby] using hv
set_option maxHeartbeats 400000 in
theorem Ζox
    (H : Family α) (V : Edge α) (q₁ q₂ E : Edge α)
    (hpos₁ : 0 < Ζx H V q₁ E)
    (hpos₂ : 0 < Ζx H V q₂ E)
    (hneq : q₁ ≠ q₂) :
    ∃ d₁ : Ζt H V q₁,
    ∃ d₂ : Ζt H V q₂,
      E = ({d₁.z, d₁.v, d₁.y} : Edge α) ∧
      E = ({d₂.z, d₂.v, d₂.y} : Edge α) ∧
      0 < Ζo H V d₁.z d₁.x d₁.y ∧
      0 < Ζo H V d₁.v d₁.x d₁.y ∧
      0 < Ζo H V d₂.z d₂.x d₂.y ∧
      0 < Ζo H V d₂.v d₂.x d₂.y ∧
      ((d₂.z = d₁.z ∧ d₂.v = d₁.y) ∨
       (d₂.z = d₁.y ∧ d₂.v = d₁.z) ∨
       (d₂.z = d₁.v ∧ d₂.v = d₁.y) ∨
       (d₂.z = d₁.y ∧ d₂.v = d₁.v)) := by
  obtain ⟨d₁, hE₁, h₁z, h₁v⟩ :=
    Ζio H V q₁ E hpos₁
  obtain ⟨d₂, hE₂, h₂z, h₂v⟩ :=
    Ζio H V q₂ E hpos₂
  have htriple : ({d₂.z, d₂.v, d₂.y} : Edge α) =
      {d₁.z, d₁.v, d₁.y} := hE₂.symm.trans hE₁
  have hsub' : ({d₂.z, d₂.v} : Edge α) ⊆
      ({d₁.z, d₁.v, d₁.y} : Edge α) := by
    rw [← htriple]
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
    rcases ht with h | h <;> simp [h]
  have hsub : q₂ ⊆ ({d₁.z, d₁.v, d₁.y} : Edge α) := by
    simpa only [d₂.hq] using hsub'
  have hOrient := Ζpq d₁ d₂ hneq hsub
  exact ⟨d₁, d₂, hE₁, hE₂, h₁z, h₁v, h₂z, h₂v, hOrient⟩
set_option maxHeartbeats 400000 in
private theorem Ζgf
    {a b c d e f : α}
    (hab : a ≠ b) (hbc : b ≠ c)
    (hda : d = a) (hec : e = c)
    (htriple : ({a, b, c} : Edge α) = {d, e, f}) : f = b := by
  have hb : b ∈ ({d, e, f} : Edge α) := by rw [← htriple]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hbd | hbe | hbf
  · exact False.elim (hab (hda.symm.trans hbd.symm))
  · exact False.elim (hbc (hbe.trans hec))
  · exact hbf.symm
set_option maxHeartbeats 400000 in
private theorem Ζiy (a b c : α) :
    ({b, a, c} : Edge α) = {a, b, c} := by
  ext t
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto
set_option maxHeartbeats 400000 in
theorem Ζpr
    (H : Family α) (V : Edge α) (q₁ q₂ E : Edge α)
    (hpos₁ : 0 < Ζx H V q₁ E)
    (hpos₂ : 0 < Ζx H V q₂ E)
    (hneq : q₁ ≠ q₂) :
    ∃ d₁ : Ζt H V q₁,
    ∃ d₂ : Ζt H V q₂,
      d₁.z = d₂.z ∧ d₁.y = d₂.v ∧ d₁.v = d₂.y ∧
      0 < Ζo H V d₁.z d₁.x d₁.y ∧
      0 < Ζo H V d₁.v d₁.x d₁.y ∧
      0 < Ζo H V d₂.z d₂.x d₂.y ∧
      0 < Ζo H V d₂.v d₂.x d₂.y := by
  obtain ⟨d₁, d₂, hE₁, hE₂, h₁z, h₁v, h₂z, h₂v, hOrient⟩ :=
    Ζox H V q₁ q₂ E hpos₁ hpos₂ hneq
  rcases hOrient with h₁ | h₂ | h₃ | h₄
  · rcases Ζan d₁ with
      ⟨hab, _, _, _, _, hbc, _, _, _, _⟩
    have hmiss := Ζgf hab hbc h₁.1 h₁.2
      (hE₁.symm.trans hE₂)
    exact ⟨d₁, d₂, h₁.1.symm, h₁.2.symm, hmiss.symm,
      h₁z, h₁v, h₂z, h₂v⟩
  · let e₂ := Ζbg d₂
    have he₂ : E = ({e₂.z, e₂.v, e₂.y} : Edge α) := by
      calc
        E = ({d₂.z, d₂.v, d₂.y} : Edge α) := hE₂
        _ = ({d₂.v, d₂.z, d₂.y} : Edge α) :=
          (Ζiy d₂.z d₂.v d₂.y).symm
    have hda : e₂.z = d₁.z := by
      simpa [e₂, Ζbg] using h₂.2
    have hec : e₂.v = d₁.y := by
      simpa [e₂, Ζbg] using h₂.1
    rcases Ζan d₁ with
      ⟨hab, _, _, _, _, hbc, _, _, _, _⟩
    have hmiss := Ζgf hab hbc hda hec
      (hE₁.symm.trans he₂)
    exact ⟨d₁, e₂, hda.symm, hec.symm, hmiss.symm,
      h₁z, h₁v, h₂v, h₂z⟩
  · let e₁ := Ζbg d₁
    have he₁ : E = ({e₁.z, e₁.v, e₁.y} : Edge α) := by
      calc
        E = ({d₁.z, d₁.v, d₁.y} : Edge α) := hE₁
        _ = ({d₁.v, d₁.z, d₁.y} : Edge α) :=
          (Ζiy d₁.z d₁.v d₁.y).symm
    have hda : d₂.z = e₁.z := by
      simpa [e₁, Ζbg] using h₃.1
    have hec : d₂.v = e₁.y := by
      simpa [e₁, Ζbg] using h₃.2
    rcases Ζan d₁ with
      ⟨hab, _, hAc, _, _, _, _, _, _, _⟩
    have hmiss := Ζgf hab.symm hAc hda hec
      (he₁.symm.trans hE₂)
    exact ⟨e₁, d₂, hda.symm, hec.symm, hmiss.symm,
      h₁v, h₁z, h₂z, h₂v⟩
  · let e₁ := Ζbg d₁
    let e₂ := Ζbg d₂
    have he₁ : E = ({e₁.z, e₁.v, e₁.y} : Edge α) := by
      calc
        E = ({d₁.z, d₁.v, d₁.y} : Edge α) := hE₁
        _ = ({d₁.v, d₁.z, d₁.y} : Edge α) :=
          (Ζiy d₁.z d₁.v d₁.y).symm
    have he₂ : E = ({e₂.z, e₂.v, e₂.y} : Edge α) := by
      calc
        E = ({d₂.z, d₂.v, d₂.y} : Edge α) := hE₂
        _ = ({d₂.v, d₂.z, d₂.y} : Edge α) :=
          (Ζiy d₂.z d₂.v d₂.y).symm
    have hda : e₂.z = e₁.z := by
      simpa [e₁, e₂, Ζbg] using h₄.2
    have hec : e₂.v = e₁.y := by
      simpa [e₁, e₂, Ζbg] using h₄.1
    rcases Ζan d₁ with
      ⟨hab, _, hAc, _, _, _, _, _, _, _⟩
    have hmiss := Ζgf hab.symm hAc hda hec
      (he₁.symm.trans he₂)
    exact ⟨e₁, e₂, hda.symm, hec.symm, hmiss.symm,
      h₁v, h₁z, h₂v, h₂z⟩
set_option maxHeartbeats 400000 in
theorem Ζok
    (H : Family α) (V : Edge α) (q₁ q₂ E : Edge α)
    (hpos₁ : 0 < Ζx H V q₁ E)
    (hpos₂ : 0 < Ζx H V q₂ E)
    (hneq : q₁ ≠ q₂) :
    ∃ d₁ : Ζt H V q₁,
    ∃ d₂ : Ζt H V q₂,
      Ζkc H V d₁.z d₁.v d₁.y d₁.x d₁.u d₂.x d₂.u ∧
      d₁.z = d₂.z ∧ d₁.y = d₂.v ∧ d₁.v = d₂.y ∧
      0 < Ζo H V d₁.v d₁.x d₁.y ∧
      0 < Ζo H V d₂.v d₂.x d₂.y := by
  obtain ⟨d₁, d₂, hza, hyc, hbc, h₁z, h₁v, h₂z, h₂v⟩ :=
    Ζpr H V q₁ q₂ E hpos₁ hpos₂ hneq
  have hq₂ : q₂ = ({d₁.z, d₁.y} : Edge α) := by
    calc
      q₂ = ({d₂.z, d₂.v} : Edge α) := d₂.hq
      _ = ({d₁.z, d₁.y} : Edge α) := by simp [hza, hyc]
  have hBook := Ζhu
    d₁ d₂ d₁.hq hq₂ rfl rfl rfl rfl rfl hza.symm hyc.symm rfl hbc.symm rfl
  exact ⟨d₁, d₂, hBook, hza, hyc, hbc, h₁v, h₂v⟩
set_option maxHeartbeats 400000 in
theorem Ζqj
    {H : Family α} {V : Edge α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hNoBlock : Ζih H)
    {q₁ q₂ E : Edge α}
    (hpos₁ : 0 < Ζx H V q₁ E)
    (hpos₂ : 0 < Ζx H V q₂ E)
    (hneq : q₁ ≠ q₂) : False := by
  obtain ⟨d₁, d₂, hBook, hza, hpage, hbcAlign, hposB, hposC⟩ :=
    Ζok H V q₁ q₂ E hpos₁ hpos₂ hneq
  rcases Ζan d₁ with
    ⟨hab, hax, hac, hau, hbx, hbc, hbu, hcx', hxu, hcu⟩
  have hcx : d₁.y ≠ d₁.x := hcx'.symm
  rcases Ζan d₂ with
    ⟨_, hzx, _, hzu, hvx, _, hvu, hxy, hxu₂, hyu⟩
  have hya : d₂.x ≠ d₂.z := hzx.symm
  have hva : d₂.u ≠ d₂.z := hzu.symm
  have hyb : d₂.x ≠ d₂.y := hxy
  have hyc : d₂.x ≠ d₂.v := hvx.symm
  have hvb : d₂.u ≠ d₂.y := hyu.symm
  have hvc : d₂.u ≠ d₂.v := hvu.symm
  have hyv : d₂.x ≠ d₂.u := hxu₂
  have hposC' : 0 < Ζo H V d₁.y d₂.x d₁.v := by
    simpa only [← hpage, ← hbcAlign] using hposC
  have hya' : d₂.x ≠ d₁.z := by
    intro he
    exact hya (he.trans hza)
  have hyc' : d₂.x ≠ d₁.y := by
    intro he
    exact hyc (he.trans hpage)
  have hva' : d₂.u ≠ d₁.z := by
    intro he
    exact hva (he.trans hza)
  have hyb' : d₂.x ≠ d₁.v := by
    intro he
    exact hyb (he.trans hbcAlign)
  have hvb' : d₂.u ≠ d₁.v := by
    intro he
    exact hvb (he.trans hbcAlign)
  have hvc' : d₂.u ≠ d₁.y := by
    intro he
    exact hvc (he.trans hpage)
  exact Ζqi hH hUniform hNoBlock hBook
    d₁.hzV d₁.hvV d₁.hyV d₁.hxV d₁.huV d₂.hxV d₂.huV
    hab hac hbc hax hbx hcx hau hbu hcu hxu
    hya' hyb' hyc' hva' hvb' hvc' hyv hposB hposC'
set_option maxHeartbeats 400000 in
theorem Ζte
    {H : Family α} {V : Edge α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hNoBlock : Ζih H)
    (E : Edge α) (_hE : E ∈ H)
    (q₁ q₂ : Edge α) (_hq₁ : q₁ ∈ Ζac H V)
    (_hq₂ : q₂ ∈ Ζac H V)
    (hpos₁ : 0 < Ζx H V q₁ E)
    (hpos₂ : 0 < Ζx H V q₂ E) : q₁ = q₂ := by
  by_contra hneq
  exact False.elim (Ζqj hH hUniform hNoBlock
    hpos₁ hpos₂ hneq)
set_option maxHeartbeats 400000 in
noncomputable def Ζfy
    (H : Family α) (V : Edge α) (E : Edge α) : ℚ := by
  classical
  exact ∑ q ∈ Ζac H V, Ζx H V q E
set_option maxHeartbeats 400000 in
noncomputable def Ζmb (H : Family α) (V : Edge α) : ℚ := by
  classical
  exact ∑ E ∈ H, Ζfy H V E
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 800000 in
private theorem Ζob
    {H : Family α} {V : Edge α} {z v x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hrecv : v ∈ (Ζb H V ({x, y} : Edge α)).erase z) :
    0 ≤ Ζh H V z x y v := by
  have hzComp := Ζv H V hzV hsource
  have hvComp := (Finset.mem_erase.mp hrecv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hrecv).1
  have hsub : ({z, v} : Edge α) ⊆ Ζb H V ({x, y} : Edge α) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzComp
    · exact (Finset.mem_singleton.mp hav) ▸ hvComp
  have hdegree : 2 ≤ (Ζb H V ({x, y} : Edge α)).card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hzv] at hc
    exact hc
  have hden : (0 : ℚ) <
      ((Ζb H V ({x, y} : Edge α)).card : ℚ) - 1 := by
    have hc : (2 : ℚ) ≤ (Ζb H V ({x, y} : Edge α)).card := by
      exact_mod_cast hdegree
    linarith
  simp [Ζh, hrecv, Ζao]
  exact div_nonneg (le_max_right _ _) (le_of_lt hden)
set_option maxHeartbeats 800000 in
theorem Ζeo
    {H : Family α} {V q : Edge α}
    (hH : Admissible H) (d : Ζt H V q)
    {w : α} (hxw : d.x ≠ w)
    (hp : ({d.x, w} : Edge α) ∈ Ζc H V q) :
    0 ≤ Ζh H V d.z d.x w d.v ∧
    Ζh H V d.z d.x w d.v ≤ 1 ∧
    0 ≤ Ζh H V d.v d.x w d.z ∧
    Ζh H V d.v d.x w d.z ≤ 1 := by
  obtain ⟨hzv, _, _, _⟩ := Ζag d
  have hp' : ({d.x, w} : Edge α) ∈
      Ζc H V ({d.z, d.v} : Edge α) := by
    simpa only [d.hq] using hp
  have hsrc := Ζam hzv hp'
  have hvComp := Ζv H V d.hvV hsrc.2
  have hzComp := Ζv H V d.hzV hsrc.1
  have hvRecv : d.v ∈
      (Ζb H V ({d.x, w} : Edge α)).erase d.z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv, hvComp⟩
  have hzRecv : d.z ∈
      (Ζb H V ({d.x, w} : Edge α)).erase d.v :=
    Finset.mem_erase.mpr ⟨hzv, hzComp⟩
  have hcard : (Ζc H V ({d.z, d.v} : Edge α)).card = 2 := by
    simpa only [d.hq] using Ζhh d
  have hcardRev : (Ζc H V ({d.v, d.z} : Edge α)).card = 2 := by
    simpa only [Finset.pair_comm] using hcard
  exact ⟨Ζob d.hzV hsrc.1 hvRecv,
    (Ζhl hH d.hzV hsrc.1 hxw hvRecv hcard).le,
    Ζob d.hvV hsrc.2 hzRecv,
    (Ζhl hH d.hvV hsrc.2 hxw hzRecv hcardRev).le⟩
set_option maxHeartbeats 800000 in
theorem Ζsm
    (H : Family α) (V q E : Edge α) (hH : Admissible H) :
    0 ≤ Ζx H V q E := by
  classical
  by_cases hq : Ζad H V q
  · let d := Ζah H V q hq
    obtain ⟨_, hxy, hxu, _⟩ := Ζag d
    have hpY : ({d.x, d.y} : Edge α) ∈ Ζc H V q := by
      rw [d.hbook]
      simp
    have hpU : ({d.x, d.u} : Edge α) ∈ Ζc H V q := by
      rw [d.hbook]
      simp
    obtain ⟨ha0, _, hb0, _⟩ :=
      Ζeo hH d hxy hpY
    obtain ⟨hc0, _, hd0, _⟩ :=
      Ζeo hH d hxu hpU
    have hY : 0 ≤ min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z) := le_min ha0 hb0
    have hU : 0 ≤ min (Ζh H V d.z d.x d.u d.v)
        (Ζh H V d.v d.x d.u d.z) := le_min hc0 hd0
    simp only [Ζx, Ζom hq]
    change 0 ≤ (if E = ({d.z, d.v, d.y} : Edge α) then
      min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z)
      else if E = ({d.z, d.v, d.u} : Edge α) then
        min (Ζh H V d.z d.x d.u d.v)
          (Ζh H V d.v d.x d.u d.z)
      else 0)
    by_cases hEy : E = ({d.z, d.v, d.y} : Edge α)
    · rw [Ζie hEy]
      exact hY
    · rw [Ζdp hEy]
      by_cases hEu : E = ({d.z, d.v, d.u} : Edge α)
      · rw [Ζie hEu]
        exact hU
      · rw [Ζdp hEu]
  · simp [Ζx, hq]
set_option maxHeartbeats 800000 in
theorem Ζko
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    ({d.z, d.v, d.y} : Edge α) ∈ H ∧
    ({d.z, d.v, d.u} : Edge α) ∈ H ∧
    ({d.z, d.v, d.y} : Edge α) ≠ ({d.z, d.v, d.u} : Edge α) := by
  obtain ⟨_, _, _, hyu⟩ := Ζag d
  have hp : ({d.z, d.v} : Edge α) ∈
      Ζc H V ({d.y, d.u} : Edge α) := by
    rw [d.hreciprocal]
    simp
  have hsrc := Ζam hyu hp
  have hY : ({d.z, d.v} : Edge α) ∪ {d.y} ∈ H :=
    (Finset.mem_filter.mp hsrc.1).2.2
  have hU : ({d.z, d.v} : Edge α) ∪ {d.u} ∈ H :=
    (Finset.mem_filter.mp hsrc.2).2.2
  have hdis : Disjoint ({d.z, d.v} : Edge α) ({d.y, d.u} : Edge α) := by
    obtain ⟨_, _, _, _, _, hd, _, _⟩ := (Finset.mem_filter.mp hp).2
    exact hd
  have hyNot : d.y ∉ ({d.z, d.v} : Edge α) := by
    intro hm
    exact (Finset.disjoint_left.mp hdis) hm (by simp)
  have hyNot' : d.y ≠ d.z ∧ d.y ≠ d.v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hyNot
  have hYEq : ({d.z, d.v} : Edge α) ∪ {d.y} =
      ({d.z, d.v, d.y} : Edge α) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hUEq : ({d.z, d.v} : Edge α) ∪ {d.u} =
      ({d.z, d.v, d.u} : Edge α) := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨hYEq ▸ hY, hUEq ▸ hU, ?_⟩
  intro he
  have hyMem : d.y ∈ ({d.z, d.v, d.u} : Edge α) := by
    rw [← he]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
  rcases hyMem with hyz | hyv | hyu'
  · exact hyNot'.1 hyz
  · exact hyNot'.2 hyv
  · exact hyu hyu'
set_option maxHeartbeats 800000 in
theorem Ζms
    (H : Family α) (V q E : Edge α)
    (hq : Ζad H V q)
    (hY : E ≠ ({(Ζah H V q hq).z,
      (Ζah H V q hq).v,
      (Ζah H V q hq).y} : Edge α))
    (hU : E ≠ ({(Ζah H V q hq).z,
      (Ζah H V q hq).v,
      (Ζah H V q hq).u} : Edge α)) :
    Ζx H V q E = 0 := by
  simp [Ζx, hq, hY, hU]
set_option maxHeartbeats 800000 in
theorem Ζnu
    {H : Family α} {V q : Edge α}
    (hH : Admissible H) (d : Ζt H V q) :
    max (Ζp H V q - 2) 0 ≤
      min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z) +
      min (Ζh H V d.z d.x d.u d.v)
        (Ζh H V d.v d.x d.u d.z) := by
  classical
  obtain ⟨_, hxy, hxu, _⟩ := Ζag d
  have hpY : ({d.x, d.y} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  have hpU : ({d.x, d.u} : Edge α) ∈ Ζc H V q := by
    rw [d.hbook]
    simp
  obtain ⟨ha0, ha1, hb0, hb1⟩ :=
    Ζeo hH d hxy hpY
  obtain ⟨hc0, hc1, hd0, hd1⟩ :=
    Ζeo hH d hxu hpU
  rw [Ζjp d]
  let a := Ζh H V d.z d.x d.y d.v
  let b := Ζh H V d.v d.x d.y d.z
  let c := Ζh H V d.z d.x d.u d.v
  let e := Ζh H V d.v d.x d.u d.z
  change max ((a + b) + (c + e) - 2) 0 ≤ min a b + min c e
  have hAssoc : (a + b) + (c + e) - 2 = a + b + c + e - 2 := by ring
  rw [hAssoc]
  exact Ζsz a b c e
    ha0 hb0 hc0 hd0 ha1 hb1 hc1 hd1
set_option maxHeartbeats 800000 in
theorem Ζlh
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : Ζad H V q) :
    let d := Ζah H V q hq
    max (Ζp H V q - 2) 0 ≤
      Ζx H V q ({d.z, d.v, d.y} : Edge α) +
      Ζx H V q ({d.z, d.v, d.u} : Edge α) := by
  classical
  let d := Ζah H V q hq
  have hEne := (Ζko d).2.2
  have hFirst : Ζx H V q ({d.z, d.v, d.y} : Edge α) =
      min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z) := by
    simp only [Ζx, Ζom hq]
    change (if ({d.z, d.v, d.y} : Edge α) = {d.z, d.v, d.y} then
      min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z) else
      if ({d.z, d.v, d.y} : Edge α) = {d.z, d.v, d.u} then
        min (Ζh H V d.z d.x d.u d.v)
          (Ζh H V d.v d.x d.u d.z) else 0) = _
    simp
  have hSecond : Ζx H V q ({d.z, d.v, d.u} : Edge α) =
      min (Ζh H V d.z d.x d.u d.v)
        (Ζh H V d.v d.x d.u d.z) := by
    have hNe : ({d.z, d.v, d.u} : Edge α) ≠
        ({d.z, d.v, d.y} : Edge α) := Ne.symm hEne
    simp only [Ζx, Ζom hq]
    change (if ({d.z, d.v, d.u} : Edge α) = {d.z, d.v, d.y} then
      min (Ζh H V d.z d.x d.y d.v)
        (Ζh H V d.v d.x d.y d.z) else
      if ({d.z, d.v, d.u} : Edge α) = {d.z, d.v, d.u} then
        min (Ζh H V d.z d.x d.u d.v)
          (Ζh H V d.v d.x d.u d.z) else 0) = _
    simp [hNe]
  change max (Ζp H V q - 2) 0 ≤
    Ζx H V q ({d.z, d.v, d.y} : Edge α) +
    Ζx H V q ({d.z, d.v, d.u} : Edge α)
  rw [hFirst, hSecond]
  exact Ζnu hH d
set_option maxHeartbeats 800000 in
theorem Ζnv
    {H : Family α} {V q : Edge α}
    (hq : Ζad H V q) :
    let d := Ζah H V q hq
    (∑ E ∈ H, Ζx H V q E) =
      Ζx H V q ({d.z, d.v, d.y} : Edge α) +
      Ζx H V q ({d.z, d.v, d.u} : Edge α) := by
  classical
  let d := Ζah H V q hq
  obtain ⟨hY, hU, hNe⟩ := Ζko d
  have hSub : ({({d.z, d.v, d.y} : Edge α),
      ({d.z, d.v, d.u} : Edge α)} : Family α) ⊆ H := by
    intro E hE
    rcases Finset.mem_insert.mp hE with h | h
    · exact h ▸ hY
    · exact (Finset.mem_singleton.mp h) ▸ hU
  have hReduce : (∑ E ∈ H, Ζx H V q E) =
      ∑ E ∈ ({({d.z, d.v, d.y} : Edge α),
        ({d.z, d.v, d.u} : Edge α)} : Family α),
        Ζx H V q E := by
    symm
    apply Finset.sum_subset hSub
    intro E hEH hEout
    have hEY : E ≠ ({d.z, d.v, d.y} : Edge α) := by
      intro he
      exact hEout (by simp [he])
    have hEU : E ≠ ({d.z, d.v, d.u} : Edge α) := by
      intro he
      exact hEout (by simp [he])
    exact Ζms H V q E hq hEY hEU
  change (∑ E ∈ H, Ζx H V q E) =
    Ζx H V q ({d.z, d.v, d.y} : Edge α) +
    Ζx H V q ({d.z, d.v, d.u} : Edge α)
  rw [hReduce]
  simp [hNe]
set_option maxHeartbeats 800000 in
theorem Ζro
    (H : Family α) (V : Edge α) (hH : Admissible H) :
    Ζgr H V ≤ Ζmb H V := by
  classical
  have hLocal (q : Edge α) (hqUsed : q ∈ Ζac H V) :
      (if Ζad H V q then
        max (Ζp H V q - 2) 0 else 0) ≤
        ∑ E ∈ H, Ζx H V q E := by
    by_cases hq : Ζad H V q
    · simp only [hq, ↓reduceIte]
      let d := Ζah H V q hq
      have hExcess := Ζlh hH hq
      have hSum := Ζnv hq
      dsimp only at hExcess hSum
      rw [hSum]
      exact hExcess
    · have hZero : ∀ E : Edge α, Ζx H V q E = 0 := by
        intro E
        simp [Ζx, hq]
      simp [hq, hZero]
  calc
    Ζgr H V ≤
        ∑ q ∈ Ζac H V, ∑ E ∈ H, Ζx H V q E := by
      unfold Ζgr
      apply Finset.sum_le_sum
      intro q hq
      exact hLocal q hq
    _ = Ζmb H V := by
      rw [Finset.sum_comm]
      rfl
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
theorem Ζku
    (H : Family α) (V : Edge α)
    (hH : Admissible H) (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hUnique : ∀ E ∈ H, ∀ q₁ ∈ Ζac H V, ∀ q₂ ∈ Ζac H V,
      0 < Ζx H V q₁ E →
      0 < Ζx H V q₂ E → q₁ = q₂)
    (hPaid : ∀ E ∈ H, ∀ q ∈ Ζac H V,
      0 < Ζx H V q E →
      Ζx H V q E ≤ Ζax H V E)
    {E : Edge α} (hE : E ∈ H) :
    Ζfy H V E ≤ Ζax H V E := by
  classical
  by_cases hSome : ∃ q ∈ Ζac H V, 0 < Ζx H V q E
  · obtain ⟨q, hq, hpos⟩ := hSome
    have hOthers (q' : Edge α) (hq' : q' ∈ Ζac H V)
        (hneq : q' ≠ q) : Ζx H V q' E = 0 := by
      have hnon := Ζsm H V q' E hH
      have hnot : ¬ 0 < Ζx H V q' E := by
        intro hpos'
        exact hneq (hUnique E hE q' hq' q hq hpos' hpos)
      linarith
    have hSingle : Ζfy H V E =
        Ζx H V q E := by
      unfold Ζfy
      exact Finset.sum_eq_single_of_mem q hq
        (fun q' hq' hneq => hOthers q' hq' hneq)
    rw [hSingle]
    exact hPaid E hE q hq hpos
  · have hZero (q : Edge α) (hq : q ∈ Ζac H V) :
        Ζx H V q E = 0 := by
      have hnon := Ζsm H V q E hH
      have hnot : ¬ 0 < Ζx H V q E := by
        intro hp
        exact hSome ⟨q, hq, hp⟩
      linarith
    have hDemandZero : Ζfy H V E = 0 := by
      unfold Ζfy
      exact Finset.sum_eq_zero (fun q hq => hZero q hq)
    rw [hDemandZero]
    exact Ζua hH hU hGround hE
theorem Ζii
    (H : Family α) (V : Edge α)
    (hH : Admissible H) (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hUnique : ∀ E ∈ H, ∀ q₁ ∈ Ζac H V, ∀ q₂ ∈ Ζac H V,
      0 < Ζx H V q₁ E →
      0 < Ζx H V q₂ E → q₁ = q₂)
    (hPaid : ∀ E ∈ H, ∀ q ∈ Ζac H V,
      0 < Ζx H V q E →
      Ζx H V q E ≤ Ζax H V E) :
    Ζgr H V ≤ ∑ E ∈ H, Ζax H V E := by
  calc
    Ζgr H V ≤ Ζmb H V :=
      Ζro H V hH
    _ ≤ ∑ E ∈ H, Ζax H V E := by
      unfold Ζmb
      apply Finset.sum_le_sum
      intro E hE
      exact Ζku
        H V hH hU hGround hUnique hPaid hE
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
private theorem Ζsn
    (G : Ζs α) (A B C : Finset α)
    (x y : α) (hMixed : Ζz G A B C)
    (hx : x ∈ A) (hy : y ∈ B)
    (hABEdge : (x, y) ∈ G.ab)
    (hACPos : 0 < Ζi G.ac C x) :
    B.filter (fun t => (x, t) ∈ G.ab) = {y} := by
  have hABPos : 0 < Ζi G.ab B x := by
    exact Finset.card_pos.mpr
      ⟨y, Finset.mem_filter.mpr ⟨hy, hABEdge⟩⟩
  have hOne := (hMixed.1 x hx hABPos hACPos).1
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hOne
  have hyMem : y ∈ B.filter (fun t => (x, t) ∈ G.ab) :=
    Finset.mem_filter.mpr ⟨hy, hABEdge⟩
  rw [hz] at hyMem
  have hyz : y = z := by simpa using hyMem
  simpa [hyz] using hz
private theorem Ζsa
    (G : Ζs α) (A B C : Finset α)
    (x z : α) (hMixed : Ζz G A B C)
    (hx : x ∈ A) (hz : z ∈ C)
    (hACEdge : (x, z) ∈ G.ac)
    (hABPos : 0 < Ζi G.ab B x) :
    C.filter (fun t => (x, t) ∈ G.ac) = {z} := by
  have hACPos : 0 < Ζi G.ac C x := by
    exact Finset.card_pos.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, hACEdge⟩⟩
  have hOne := (hMixed.1 x hx hABPos hACPos).2
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hOne
  have hzMem : z ∈ C.filter (fun t => (x, t) ∈ G.ac) :=
    Finset.mem_filter.mpr ⟨hz, hACEdge⟩
  rw [hw] at hzMem
  have hzw : z = w := by simpa using hzMem
  simpa [hzw] using hw
theorem Ζqk
    {H : Family α} {V : Edge α} {a b c d x : α}
    (hUniform : Uniform 3 H)
    (hBook : Ζe H V b c =
      ({{d, a}, {d, x}} : Family α)) :
    Disjoint
      (((Ζn H V a b c).erase x).filter
        (fun u => (u, d) ∈ (Ζj H V a b c).ab))
      (((Ζn H V a b c).erase x).filter
        (fun u => (u, d) ∈ (Ζj H V a b c).ac)) := by
  apply Finset.disjoint_left.mpr
  intro u huAB huAC
  have huAErase := (Finset.mem_filter.mp huAB).1
  have huA : u ∈ Ζn H V a b c :=
    (Finset.mem_erase.mp huAErase).2
  have hux : u ≠ x := (Finset.mem_erase.mp huAErase).1
  have huData := Ζcd.mp huA
  have hABData := Ζcc.mp (Finset.mem_filter.mp huAB).2
  have hACData := Ζcy.mp (Finset.mem_filter.mp huAC).2
  have hdB := Ζbi.mp hABData.2.1
  have hdC := Ζdf.mp hACData.2.1
  have hdu : d ≠ u := by
    intro hEq
    have hCard := hUniform hABData.2.2
    rw [hEq] at hCard
    have hTwo : ({c, u} : Edge α).card ≤ 2 :=
      Finset.card_insert_le c {u}
    simp at hCard
    omega
  have hPair : ({d, u} : Edge α) ∈ Ζe H V b c := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hdu⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hdB.1
      · exact (Finset.mem_singleton.mp ht) ▸ huData.1
    · refine ⟨?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro t ht hbc
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht hbc
        rcases ht with htd | htu
        · rcases hbc with htb | htc
          · exact hdB.2.2.1 (htd.symm.trans htb)
          · exact hdB.2.2.2.1 (htd.symm.trans htc)
        · rcases hbc with htb | htc
          · exact huData.2.2.1 (htu.symm.trans htb)
          · exact huData.2.2.2.1 (htu.symm.trans htc)
      · have hSet : ({d, u} : Edge α) ∪ {b} = {b, u, d} := by
          ext t
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        rw [hSet]
        exact hACData.2.2
      · have hSet : ({d, u} : Edge α) ∪ {c} = {c, u, d} := by
          ext t
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        rw [hSet]
        exact hABData.2.2
  rw [hBook] at hPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hPair
  rcases hPair with hda | hdx
  · have huIn : u ∈ ({d, a} : Edge α) := by
      rw [← hda]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at huIn
    rcases huIn with hud | hua
    · exact hdu hud.symm
    · exact huData.2.1 hua
  · have huIn : u ∈ ({d, x} : Edge α) := by
      rw [← hdx]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at huIn
    rcases huIn with hud | hux'
    · exact hdu hud.symm
    · exact hux hux'
theorem Ζso
    {H : Family α} {V : Edge α} {a b c d x : α} {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hx : x ∈ Ζn H V a b c)
    (hdB : d ∈ Ζu H V a b c)
    (hdC : d ∈ Ζae H V a b c)
    (hABEdge : (x, d) ∈ (Ζj H V a b c).ab)
    (hACEdge : (x, d) ∈ (Ζj H V a b c).ac)
    (hBook : Ζe H V b c =
      ({{d, a}, {d, x}} : Family α))
    (hrDegree : Ζf (Ζj H V a b c).ab
      ((Ζn H V a b c).erase x) d = r)
    (hsDegree : Ζf (Ζj H V a b c).ac
      ((Ζn H V a b c).erase x) d = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    min (Ζl (r + 1)) (Ζl (s + 1)) ≤
      Ζax H V ({a, b, c} : Edge α) := by
  let G := Ζj H V a b c
  let A := Ζn H V a b c
  let B := Ζu H V a b c
  let C := Ζae H V a b c
  have hMixed : Ζz G A B C :=
    Ζdc hH hUniform hab hac hbc
  have hABPos : 0 < Ζi G.ab B x :=
    Finset.card_pos.mpr
      ⟨d, Finset.mem_filter.mpr ⟨hdB, hABEdge⟩⟩
  have hACPos : 0 < Ζi G.ac C x :=
    Finset.card_pos.mpr
      ⟨d, Finset.mem_filter.mpr ⟨hdC, hACEdge⟩⟩
  have hAB := Ζsn
    G A B C x d hMixed hx hdB hABEdge hACPos
  have hAC := Ζsa
    G A B C x d hMixed hx hdC hACEdge hABPos
  have hDisj := Ζqk
    hUniform hBook
  exact Ζna
    hH hUniform hground hab hac hbc hE
    hx hdB hdC hAB hAC hrDegree hsDegree hr hs hDisj
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
set_option maxHeartbeats 1000000 in
private theorem Ζoc
    {H : Family α} {V : Edge α} {z x y : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hE : ({z, x, y} : Edge α) ∈ H)
    (hzx : z ≠ x) (hzy : z ≠ y) (hxy : x ≠ y) :
    ({x, y} : Edge α) ∈ Ζaf H V z := by
  have hxMem : x ∈ ({z, x, y} : Edge α) := by simp
  have hyMem : y ∈ ({z, x, y} : Edge α) := by simp
  have hxV := hground _ hE hxMem
  have hyV := hground _ hE hyMem
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htx | hty
      · exact htx ▸ hxV
      · exact (Finset.mem_singleton.mp hty) ▸ hyV
    · exact Finset.card_pair (by
        intro h
        exact hxy h)
  · constructor
    · simp [hzx, hzy]
    · have heq : ({x, y} : Edge α) ∪ {z} = {z, x, y} := by
        ext t
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hE
set_option maxHeartbeats 1000000 in
private theorem Ζfl
    {H : Family α} {V : Edge α} {z x y : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hzx : z ≠ x) (hzy : z ≠ y) (hxy : x ≠ y)
    (hE : ({z, x, y} : Edge α) ∈ H) :
    y ∈ Ζk H V z x := by
  have hyV : y ∈ V := hground _ hE (by simp)
  have hyOut : y ∉ ({z, x} : Edge α) := by
    intro hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hyz | hyx
    · exact hzy hyz.symm
    · exact hxy hyx.symm
  apply Finset.mem_filter.mpr
  refine ⟨hyV, hyOut, ?_⟩
  · have heq : ({z, x} : Edge α) ∪ {y} = {z, x, y} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq]
    exact hE
set_option maxHeartbeats 1000000 in
theorem Ζiz
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α)) :
    t ∈ (Ζk H V a c).erase b ∧
      x ∈ (Ζk H V a b).erase c ∧
      ({a, b, c} : Edge α) ∈ H ∧
      ({a, b, x} : Edge α) ∈ H := by
  have hBC : ({b, c} : Edge α) ∈ Ζe H V a t := by
    rw [hBook]
    simp
  have hBX : ({b, x} : Edge α) ∈ Ζe H V a t := by
    rw [hBook]
    simp
  obtain ⟨_, _, hABC, _⟩ := Finset.mem_filter.mp hBC
  obtain ⟨_, _, hABX, _⟩ := Finset.mem_filter.mp hBX
  have hDisj : Disjoint ({b, x} : Edge α) ({a, t} : Edge α) :=
    (Finset.mem_filter.mp hBX).2.1
  have hax : a ≠ x := by
    intro h
    have haP : a ∈ ({b, x} : Edge α) := by simpa [h]
    have haQ : a ∈ ({a, t} : Edge α) := by simp
    exact (Finset.disjoint_left.mp hDisj) haP haQ
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABC
    exact hABC
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABX
    exact hABX
  constructor
  · apply Finset.mem_erase.mpr
    refine ⟨Ne.symm hbt, Ζfl hground hac hat hct hBridge⟩
  constructor
  · apply Finset.mem_erase.mpr
    refine ⟨Ne.symm hcx, Ζfl hground hab hax
      hbx hABX'⟩
  exact ⟨hABC', hABX'⟩
set_option maxHeartbeats 1000000 in
theorem Ζol
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α)) :
    2 ≤ (Ζb H V ({b, c} : Edge α)).card := by
  have hPage : ({b, c} : Edge α) ∈ Ζe H V a t := by
    rw [hBook]
    simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPage
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABC
    exact hABC
  have hTBC' : ({t, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {t} = {t, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hTBC
    exact hTBC
  have hBridgeV := hground _ hBridge
  have haV : a ∈ V := hBridgeV (by simp)
  have htV : t ∈ V := hBridgeV (by simp)
  have haComp : a ∈ Ζb H V ({b, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, ?_, ?_⟩
    · simp [hab, hac]
    · have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
        ext q
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hABC'
  have htComp : t ∈ Ζb H V ({b, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨htV, ?_, ?_⟩
    · simp [hbt.symm, hct.symm]
    · have heq : ({b, c} : Edge α) ∪ {t} = {t, b, c} := by
        ext q
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hTBC'
  have hat' : a ≠ t := hat
  have hpair : ({a, t} : Edge α) ⊆ Ζb H V ({b, c} : Edge α) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqa | hqt
    · exact hqa ▸ haComp
    · exact (Finset.mem_singleton.mp hqt) ▸ htComp
  have hcard := Finset.card_le_card hpair
  rw [Finset.card_pair hat'] at hcard
  exact hcard
set_option maxHeartbeats 1000000 in
theorem Ζja
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H)
    (haV : a ∈ V) (hbV : b ∈ V) (htV : t ∈ V)
    (hcV : c ∈ V) (hxV : x ∈ V)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hac : a ≠ c) (hax : a ≠ x) (hcx : c ≠ x)
    (htc : t ≠ c) (htx : t ≠ x)
    (hBook : Ζe H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α)) :
    (Ζm H V a c x).card = 2 ∧
      (Ζm H V t c x).card = 2 := by
  have hCommon : Ζc H V ({c, x} : Edge α) =
      ({{a, b}, {a, t}, {b, t}} : Family α) := by
    ext p
    exact (Ζr H V hcx p).trans
      (by rw [hBook])
  have hCell : ({c, x} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hcx⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqc | hqx
    · exact hqc ▸ hcV
    · exact (Finset.mem_singleton.mp hqx) ▸ hxV
  have hpbt : ({b, t} : Edge α) ∈ Ζc H V ({c, x} : Edge α) := by
    exact (Ζr H V hcx _).2
      (by rw [hBook]; simp)
  have hpab : ({a, b} : Edge α) ∈ Ζc H V ({c, x} : Edge α) := by
    exact (Ζr H V hcx _).2
      (by rw [hBook]; simp)
  have hpat : ({a, t} : Edge α) ∈ Ζc H V ({c, x} : Edge α) := by
    exact (Ζr H V hcx _).2
      (by rw [hBook]; simp)
  have hFiberA : Ζcu H V ({c, x} : Edge α) a = {b, t} := by
    have haNot : a ∉ ({b, t} : Edge α) := by
      intro ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with hab' | hat'
      · exact hab hab'
      · exact hat hat'
    apply Finset.Subset.antisymm
    · exact Ζhn hH hCell hpbt haNot
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hqb | hqt
      · subst q
        unfold Ζcu
        exact Finset.mem_filter.mpr ⟨hbV, hpab⟩
      · subst q
        unfold Ζcu
        exact Finset.mem_filter.mpr ⟨htV, hpat⟩
  have hFiberT : Ζcu H V ({c, x} : Edge α) t = {a, b} := by
    apply Finset.Subset.antisymm
    · exact Ζhn hH hCell hpab
        (by simp [Ne.symm hat, hbt.symm])
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hqa | hqb
      · subst q
        unfold Ζcu
        exact Finset.mem_filter.mpr
          ⟨haV, by simpa [Finset.pair_comm] using hpat⟩
      · subst q
        unfold Ζcu
        exact Finset.mem_filter.mpr
          ⟨hbV, by simpa [Finset.pair_comm] using hpbt⟩
  have hA := Ζaq H V
    haV hac hax hcx
  have hT := Ζaq H V
    htV htc htx hcx
  rw [hA, hFiberA, hT, hFiberT]
  constructor
  · rw [Finset.card_pair hbt]
  · rw [Finset.card_pair hab]
set_option maxHeartbeats 1000000 in
private theorem Ζcs
    {p : Edge α} {u v : α}
    (hp : p.card = 2) (hu : u ∈ p) (hv : v ∈ p) (huv : u ≠ v) :
  p = {u, v} := by
  have hsub : ({u, v} : Edge α) ⊆ p := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqu | hqv
    · exact hqu ▸ hu
    · exact (Finset.mem_singleton.mp hqv) ▸ hv
  have hcard : p.card ≤ ({u, v} : Edge α).card := by
    rw [hp, Finset.card_pair huv]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
set_option maxHeartbeats 1000000 in
theorem Ζhi
    {H : Family α} {V : Edge α} {a t b c x : α} {r : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hx : x ∈ Ζn H V c a t)
    (hrDegree : Ζf (Ζj H V c a t).ac
      ((Ζn H V c a t).erase x) b = r)
    (hr : 2 ≤ r) :
    (Ζc H V ({b, t} : Edge α)).card ≤ r + 2 := by
  let A := Ζn H V c a t
  let B := Ζu H V c a t
  let C := Ζae H V c a t
  let G := Ζj H V c a t
  have hBCPage : ({b, c} : Edge α) ∈ Ζe H V a t := by
    rw [hBook]
    simp
  have hBXPage : ({b, x} : Edge α) ∈ Ζe H V a t := by
    rw [hBook]
    simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hBCPage
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hBXPage
  have hSrc : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABC
    exact hABC
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hTBX
    exact hTBX
  have hbV : b ∈ V := hground _ hSrc (by simp)
  have hcV : c ∈ V := hground _ hSrc (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have haV : a ∈ V := hground _ hBridge (by simp)
  have hCell : ({b, t} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hbt⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqb | hqt
    · exact hqb ▸ hbV
    · exact (Finset.mem_singleton.mp hqt) ▸ htV
  have hCenter : ({a, c} : Edge α) ∈ Ζc H V ({b, t} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hac⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with hqa | hqc
      · exact hqa ▸ haV
      · exact (Finset.mem_singleton.mp hqc) ▸ hcV
    · refine ⟨b, by simp, t, by simp, hbt, ?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro q hqP hqCell
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqP hqCell
        rcases hqP with hqa | hqc <;>
          rcases hqCell with hqb | hqt
        · exact hab (hqa.symm.trans hqb)
        · exact hat (hqa.symm.trans hqt)
        · exact hbc.symm (hqc.symm.trans hqb)
        · exact hct (hqc.symm.trans hqt)
      · have heq : ({a, c} : Edge α) ∪ {b} = {a, b, c} := by
          ext q
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [heq]
        exact hSrc
      · have heq : ({a, c} : Edge α) ∪ {t} = {a, c, t} := by
          ext q
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [heq]
        exact hBridge
  have hBookNotAB : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABX
    exact hABX
  have hbC : b ∈ C := by
    change b ∈ Ζae H V c a t
    apply Ζdf.mpr
    refine ⟨hbV, ?_, ?_, ?_, ?_⟩
    · exact hbc
    · exact hab.symm
    · exact hbt
    · have heq : ({c, a, b} : Edge α) = ({a, b, c} : Edge α) := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hSrc
  have hbB : b ∈ B := by
    change b ∈ Ζu H V c a t
    apply Ζbi.mpr
    refine ⟨hbV, ?_, ?_, ?_, ?_⟩
    · exact hbc
    · exact hab.symm
    · exact hbt
    · have heq : ({c, t, b} : Edge α) = ({b, c} : Edge α) ∪ {t} := by
        ext q
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hTBC
  have hABedge : (x, b) ∈ G.ab := by
    change (x, b) ∈ (Ζj H V c a t).ab
    apply Ζcc.mpr
    refine ⟨hx, hbB, ?_⟩
    have heq : ({t, b, x} : Edge α) = ({t, x, b} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact hTBX'
  have hACedge : (x, b) ∈ G.ac := by
    change (x, b) ∈ (Ζj H V c a t).ac
    apply Ζcy.mpr
    refine ⟨hx, hbC, ?_⟩
    have heq : ({a, b, x} : Edge α) = ({a, x, b} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact hBookNotAB
  have hMixed : Ζz G A B C :=
    Ζdc hH hUniform
      hac.symm hct hat
  have hABpos : 0 < Ζi G.ab B x := by
    exact Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbB, hABedge⟩⟩
  have hACpos : 0 < Ζi G.ac C x := by
    exact Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbC, hACedge⟩⟩
  have hACone : C.filter (fun z => (x, z) ∈ G.ac) = {b} := by
    have hCard : (C.filter (fun z => (x, z) ∈ G.ac)).card = 1 :=
      (hMixed.1 x hx hABpos hACpos).2
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hCard
    have hbmem : b ∈ C.filter (fun z => (x, z) ∈ G.ac) :=
      Finset.mem_filter.mpr ⟨hbC, hACedge⟩
    rw [hz] at hbmem
    have hbz : b = z := by simpa using hbmem
    simpa [hbz] using hz
  have hFullDegree : Ζf G.ac A b = r + 1 := by
    have h := Ζbw
      G.ac A C x b hx hACone
    rw [hrDegree] at h
    exact h
  have hBCzero : Ζf G.bc B b = 0 := by
    by_contra hne
    have hpos : 0 < Ζf G.bc B b := Nat.pos_of_ne_zero hne
    have hOne := hMixed.2.2 b hbC
      (by rw [hFullDegree]; omega) hpos
    omega
  let N := A.filter (fun u => (u, b) ∈ G.ac)
  let T := insert ({a, c} : Edge α)
    (N.image fun u => ({a, u} : Edge α))
  have hJsub : Ζc H V ({b, t} : Edge α) ⊆ T := by
    intro p hp
    by_cases hpCenter : p = ({a, c} : Edge α)
    · rw [hpCenter]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    · obtain ⟨hpV, hpCert⟩ := Finset.mem_filter.mp hp
      obtain ⟨u, hu, v, hv, huv, hpDisj, hpu, hpv⟩ := hpCert
      have huCases : u = b ∨ u = t := by simpa using hu
      have hvCases : v = b ∨ v = t := by simpa using hv
      have hpb : p ∪ {b} ∈ H := by
        rcases huCases with rfl | rfl
        · rcases hvCases with rfl | rfl
          · exact False.elim (huv rfl)
          · exact hpu
        · rcases hvCases with rfl | rfl
          · exact hpv
          · exact False.elim (huv rfl)
      have hpt : p ∪ {t} ∈ H := by
        rcases huCases with rfl | rfl
        · rcases hvCases with rfl | rfl
          · exact False.elim (huv rfl)
          · exact hpv
        · rcases hvCases with rfl | rfl
          · exact hpu
          · exact False.elim (huv rfl)
      have hhit : ¬ Disjoint p ({a, c} : Edge α) :=
        Ζdw hH hCell hp hCenter
      have hACmem : a ∈ p ∨ c ∈ p := by
        by_contra h
        apply hhit
        apply Finset.disjoint_left.mpr
        intro q hqP hqAC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqAC
        rcases hqAC with hqa | hqc
        · exact (not_or.mp h).1 (hqa ▸ hqP)
        · exact (not_or.mp h).2 (hqc ▸ hqP)
      have hpCard : p.card = 2 :=
        (Finset.mem_powersetCard.mp hpV).2
      have hcNot : c ∉ p := by
        intro hcP
        have haNot : a ∉ p := by
          intro haP
          exact hpCenter (Ζcs hpCard haP hcP hac)
        have hMore : (p.erase c).Nonempty := by
          apply Finset.card_pos.mp
          have hErase := Finset.card_erase_add_one hcP
          omega
        obtain ⟨u, huErase⟩ := hMore
        have hcu : u ≠ c := (Finset.mem_erase.mp huErase).1
        have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
        have huNeA : u ≠ a := by
          intro hEq
          exact hpCenter (by
            rw [Ζcs hpCard hcP huP hcu.symm]
            simp [hEq, Finset.pair_comm])
        have huNeT : u ≠ t := by
          intro hEq
          have htP : t ∈ p := hEq ▸ huP
          exact (Finset.disjoint_left.mp hpDisj) htP (by simp)
        have huNeB : u ≠ b := by
          intro hEq
          have hbP : b ∈ p := hEq ▸ huP
          exact (Finset.disjoint_left.mp hpDisj) hbP (by simp)
        have huV : u ∈ V :=
          (Finset.mem_powersetCard.mp hpV).1 huP
        have huB : u ∈ B := by
          change u ∈ Ζu H V c a t
          apply Ζbi.mpr
          refine ⟨huV, hcu, huNeA, huNeT, ?_⟩
          have hpEq : p = ({c, u} : Edge α) :=
            Ζcs hpCard hcP huP hcu.symm
          have hpT : p ∪ {t} ∈ H := hpt
          have heq' : p ∪ {t} = {c, t, u} := by
            rw [hpEq]
            ext q
            simp [or_comm, or_left_comm, or_assoc]
          rw [← heq']
          exact hpT
        have huBC : (u, b) ∈ G.bc := by
          change (u, b) ∈ (Ζj H V c a t).bc
          apply Ζhq.mpr
          refine ⟨huB, hbC, ?_⟩
          have hpEq : p = ({c, u} : Edge α) :=
            Ζcs hpCard hcP huP hcu.symm
          have heq : p ∪ {b} = ({c, u, b} : Edge α) := by
            rw [hpEq]
            ext q
            simp
          rw [← heq]
          exact hpb
        have hposB : 0 < Ζf G.bc B b := by
          exact Finset.card_pos.mpr
            ⟨u, Finset.mem_filter.mpr ⟨huB, huBC⟩⟩
        exact (Nat.ne_of_gt hposB) hBCzero
      have haP := hACmem.resolve_right hcNot
      have hMore : (p.erase a).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one haP
        omega
      obtain ⟨u, huErase⟩ := hMore
      have hau : a ≠ u := (Finset.mem_erase.mp huErase).1.symm
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huNeC : u ≠ c := by
        intro hEq
        exact hpCenter (by
          rw [Ζcs hpCard haP huP hau]
          simp [hEq, Finset.pair_comm])
      have huNeT : u ≠ t := by
        intro hEq
        have htP : t ∈ p := hEq ▸ huP
        exact (Finset.disjoint_left.mp hpDisj) htP (by simp)
      have huNeB : u ≠ b := by
        intro hEq
        have hbP : b ∈ p := hEq ▸ huP
        exact (Finset.disjoint_left.mp hpDisj) hbP (by simp)
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpV).1 huP
      have huA : u ∈ A := by
        change u ∈ Ζn H V c a t
        apply Ζcd.mpr
        refine ⟨huV, huNeC, Ne.symm hau, huNeT, ?_⟩
        have hpEq : p = ({a, u} : Edge α) :=
          Ζcs hpCard haP huP hau
        have heq : p ∪ {t} = ({a, t, u} : Edge α) := by
          rw [hpEq]
          ext q
          simp [or_comm, or_left_comm]
        rw [← heq]
        exact hpt
      have huAC : (u, b) ∈ G.ac := by
        change (u, b) ∈ (Ζj H V c a t).ac
        apply Ζcy.mpr
        refine ⟨huA, hbC, ?_⟩
        have hpEq : p = ({a, u} : Edge α) :=
          Ζcs hpCard haP huP hau
        have heq : p ∪ {b} = ({a, u, b} : Edge α) := by
          rw [hpEq]
          ext q
          simp
        rw [← heq]
        exact hpb
      have huN : u ∈ N := Finset.mem_filter.mpr ⟨huA, huAC⟩
      have hpEq : p = ({a, u} : Edge α) :=
        Ζcs hpCard haP huP hau
      rw [hpEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨u, huN, rfl⟩))
  have hCard : (Ζc H V ({b, t} : Edge α)).card ≤ T.card :=
    Finset.card_le_card hJsub
  have hTCard : T.card ≤ N.card + 1 := by
    dsimp [T]
    calc
      (insert ({a, c} : Edge α) (N.image fun u => ({a, u} : Edge α))).card ≤
          (N.image fun u => ({a, u} : Edge α)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ N.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
  have hNCard : N.card = r + 1 := by
    change (Finset.filter (fun u => (u, b) ∈ G.ac) A).card = r + 1
    exact hFullDegree
  rw [hNCard] at hTCard
  omega
set_option maxHeartbeats 1000000 in
private theorem Ζuq
    (H : Family α) (V : Edge α) {a t : α} (hat : a ≠ t) :
    Ζe H V t a = Ζe H V a t := by
  unfold Ζe
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpV, hpDisj, hpt, hpa⟩
    refine ⟨hpV, ?_, hpa, hpt⟩
    simpa only [Finset.pair_comm] using hpDisj
  · rintro ⟨hpV, hpDisj, hpa, hpt⟩
    refine ⟨hpV, ?_, hpt, hpa⟩
    simpa only [Finset.pair_comm] using hpDisj
set_option maxHeartbeats 1000000 in
private theorem Ζnw
    (H : Family α) (V : Edge α) (a c t : α) :
    Ζn H V c t a =
      Ζn H V c a t := by
  rw [Ζap,
    Ζap]
  simp [Finset.pair_comm]
set_option maxHeartbeats 1000000 in
private theorem Ζvm
    (H : Family α) (V : Edge α) (a c t : α) :
    Ζae H V c t a =
      Ζu H V c a t := by
  rw [Ζcg,
    Ζbd]
set_option maxHeartbeats 1000000 in
private theorem Ζvj
    (H : Family α) (V : Edge α) (a c t : α) :
    (Ζj H V c t a).ac =
      (Ζj H V c a t).ab := by
  ext e
  rcases e with ⟨u, v⟩
  rw [Ζcy, Ζcc,
    Ζnw H V a c t,
    Ζvm H V a c t]
set_option maxHeartbeats 1000000 in
theorem Ζkv
    {H : Family α} {V : Edge α} {a t b c x : α} {s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hx : x ∈ Ζn H V c a t)
    (hsDegree : Ζf (Ζj H V c a t).ab
      ((Ζn H V c a t).erase x) b = s)
    (hs : 2 ≤ s) :
    (Ζc H V ({a, b} : Edge α)).card ≤ s + 2 := by
  have hBookSwap : Ζe H V t a =
      ({{b, c}, {b, x}} : Family α) := by
    rw [Ζuq H V hat, hBook]
  have hBridgeSwap : ({t, c, a} : Edge α) ∈ H := by
    have heq : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq]
    exact hBridge
  have hxSwap : x ∈ Ζn H V c t a := by
    rw [Ζnw H V a c t]
    exact hx
  have hDegSwap : Ζf (Ζj H V c t a).ac
      ((Ζn H V c t a).erase x) b = s := by
    rw [Ζvj H V a c t,
      Ζnw H V a c t]
    exact hsDegree
  simpa [Finset.pair_comm] using Ζhi
    (H := H) (V := V) (a := t) (t := a) (b := b) (c := c) (x := x)
    (hH := hH) (hUniform := hUniform) (hground := hground)
    (hab := hbt.symm) (hac := hct.symm) (hat := hat.symm)
    (hbc := hbc) (hbt := hab.symm) (hct := hac.symm)
    (hBridge := hBridgeSwap) (hBook := hBookSwap) (hx := hxSwap)
    (hrDegree := hDegSwap) (hr := hs)
set_option maxHeartbeats 1000000 in
theorem Ζej
    (H : Family α) (V : Edge α) {z x y u v : α} {k : ℕ}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y)
    (hu : u ∈ (Ζk H V z y).erase x)
    (hv : v ∈ (Ζk H V z x).erase y)
    (huCount : (Ζm H V z x u).card = 2)
    (hvCount : (Ζm H V z y v).card ≤ k) :
    Ζo H V z x y ≤ Ζg k := by
  let dx := (Ζk H V z x).card
  let dy := (Ζk H V z y).card
  have hDef1 : Ζg dx - Ζg 2 ≤
      (∑ q ∈ (Ζk H V z y).erase x,
        (Ζg dx -
          Ζg (Ζm H V z x q).card)) := by
    have hAt : Ζg dx - Ζg 2 =
        Ζg dx -
          Ζg (Ζm H V z x u).card := by
      rw [huCount]
    rw [hAt]
    exact Finset.single_le_sum
      (f := fun q => Ζg dx -
        Ζg (Ζm H V z x q).card)
      (fun q hq => sub_nonneg.mpr (Ζdi (Finset.card_le_card
        (Ζbc H V z x q)))) hu
  have hDef2 : Ζg dy - Ζg k ≤
      (∑ q ∈ (Ζk H V z x).erase y,
        (Ζg dy -
          Ζg (Ζm H V z y q).card)) := by
    have hAtV : Ζg dy - Ζg k ≤
        Ζg dy -
          Ζg (Ζm H V z y v).card := by
      exact sub_le_sub_left (Ζdi hvCount) _
    exact hAtV.trans (Finset.single_le_sum
      (f := fun q => Ζg dy -
        Ζg (Ζm H V z y q).card)
      (fun q hq => sub_nonneg.mpr (Ζdi
        (Finset.card_le_card
          (Ζbc H V z y q)))) hv)
  have hDef : Ζg dx + Ζg dy -
      (Ζg 2 + Ζg k) ≤
      Ζeq H V z x y := by
    unfold Ζeq
    have := add_le_add hDef1 hDef2
    dsimp [dx, dy] at this ⊢
    linarith
  have hEq := Ζdr H V hxy hxyNe
  have hBase := Ζfr dx dy
  have hMin : 2 * min (Ζg dx) (Ζg dy) ≤
      Ζg dx + Ζg dy := by
    have h₁ := min_le_left (Ζg dx) (Ζg dy)
    have h₂ := min_le_right (Ζg dx) (Ζg dy)
    linarith
  have h2 : Ζg 2 = 0 := by norm_num [Ζg]
  have hkNonneg := Ζek k
  rw [h2] at hDef
  rw [hEq]
  have hTarget : Ζg dx + Ζg dy -
      (Ζg dx + Ζg dy - Ζg k) ≤
      Ζg k := by linarith
  linarith
set_option maxHeartbeats 1000000 in
theorem Ζeu
    (H : Family α) (V : Edge α) {z x y u v : α} {r : ℕ}
    (hxy : ({x, y} : Edge α) ∈ Ζaf H V z)
    (hxyNe : x ≠ y)
    (hu : u ∈ (Ζk H V z y).erase x)
    (hv : v ∈ (Ζk H V z x).erase y)
    (huCount : (Ζm H V z x u).card = 2)
    (hvCount : (Ζm H V z y v).card ≤ r + 2) :
    Ζo H V z x y ≤ Ζl (r + 1) := by
  have h := Ζej
    H V hxy hxyNe hu hv huCount hvCount
  simpa [Ζl, Nat.add_assoc] using h
set_option maxHeartbeats 1000000 in
theorem Ζsp
    {H : Family α} {V : Edge α} {a t b c x : α} {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x)
    (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : Ζe H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ Ζn H V c a t)
    (hrDegree : Ζf (Ζj H V c a t).ac
      ((Ζn H V c a t).erase x) b = r)
    (hsDegree : Ζf (Ζj H V c a t).ab
      ((Ζn H V c a t).erase x) b = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    min
      (Ζq H V a c b /
        (((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1))
      (Ζq H V t c b /
        (((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1))
      ≤ Ζax H V ({a, c, t} : Edge α) := by
  have hAlt := Ζiz hground hab hac hat
    hbc hbt hbx hct hcx htx hBridge hBookAt
  have hPageBC : ({b, c} : Edge α) ∈ Ζe H V a t := by
    rw [hBookAt]
    simp
  have hPageBX : ({b, x} : Edge α) ∈ Ζe H V a t := by
    rw [hBookAt]
    simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hPageBX
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hABC
  have hTBC' : ({t, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {t} = {t, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hTBC
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hABX
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hTBX
  have hxb : x ∈ (Ζk H V a b).erase c := hAlt.2.1
  have hta : t ∈ (Ζk H V a c).erase b := hAlt.1
  have hxt : x ∈ (Ζk H V t b).erase c := by
    apply Finset.mem_erase.mpr
    refine ⟨hcx.symm, ?_⟩
    exact Ζfl hground hbt.symm htx hbx hTBX'
  have hatN : a ∈ (Ζk H V t c).erase b := by
    apply Finset.mem_erase.mpr
    refine ⟨hab, ?_⟩
    have hBridgeTCA : ({t, c, a} : Edge α) ∈ H := by
      have heq : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq ▸ hBridge
    exact Ζfl hground hct.symm hat.symm hac.symm hBridgeTCA
  have haV : a ∈ V := hground _ hBridge (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have hcV : c ∈ V := hground _ hBridge (by simp)
  have hbV : b ∈ V := by
    have hmem := (Finset.mem_filter.mp hPageBC).1
    exact (Finset.mem_powersetCard.mp hmem).1 (by simp)
  have hxV : x ∈ V := by
    have hmem := (Finset.mem_filter.mp hPageBX).1
    exact (Finset.mem_powersetCard.mp hmem).1 (by simp)
  have hCounts := Ζja hH haV hbV htV hcV hxV
    hab hat hbt hac hax hcx hct.symm htx hBookCx
  have hCardBT : (Ζc H V ({b, t} : Edge α)).card ≤ r + 2 := by
    simpa [Finset.pair_comm] using
      Ζhi hH hUniform hground
        hab hac hat hbc hbt hct hBridge hBookAt hx hrDegree hr
  have hCardBA : (Ζc H V ({b, a} : Edge α)).card ≤ s + 2 := by
    simpa [Finset.pair_comm] using
      Ζkv hH hUniform hground
        hab hac hat hbc hbt hct hBridge hBookAt hx hsDegree hs
  have hCommonA : (Ζm H V a b t).card ≤ r + 2 := by
    have heq := Ζaq H V haV hab hat hbt
    rw [heq]
    exact (Ζcv H V {b, t} a).trans hCardBT
  have hCommonT : (Ζm H V t b a).card ≤ s + 2 := by
    have heq := Ζaq H V htV hbt.symm
      hat.symm hab.symm
    rw [heq]
    exact (Ζcv H V {b, a} t).trans hCardBA
  have hACB : ({a, c, b} : Edge α) ∈ H := by
    have heq : ({a, c, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hABC'
  have hTCB : ({t, c, b} : Edge α) ∈ H := by
    have heq : ({t, c, b} : Edge α) = ({t, b, c} : Edge α) := by
      ext q
      simp [or_comm, or_left_comm]
    exact heq ▸ hTBC'
  have hRootA := Ζoc (z := a) (x := c) (y := b)
    hground hACB hac hab hbc.symm
  have hRootT := Ζoc (z := t) (x := c) (y := b)
    hground hTCB hct.symm hbt.symm hbc.symm
  have hWeightA := Ζeu
    H V hRootA hbc.symm hxb hta hCounts.1 hCommonA
  have hWeightT := Ζeu
    H V hRootT hbc.symm hxt hatN hCounts.2 hCommonT
  have hPositiveA : Ζq H V a c b ≤ Ζl (r + 1) := by
    unfold Ζq
    exact max_le hWeightA (Ζdy _)
  have hPositiveT : Ζq H V t c b ≤ Ζl (s + 1) := by
    unfold Ζq
    exact max_le hWeightT (Ζdy _)
  have hdeg := Ζol hground hab hac hat
    hbc hbt hbx hct hcx htx hBridge hBookAt
  have hden : 1 ≤
      ((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1 := by
    have hq : (2 : ℚ) ≤ (Ζb H V ({b, c} : Edge α)).card := by
      exact_mod_cast hdeg
    linarith
  have hPayA : Ζq H V a c b /
      (((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1) ≤
      Ζl (r + 1) := by
    apply (div_le_iff₀ (by linarith : 0 <
      ((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1)).mpr
    have hnonneg : 0 ≤ Ζq H V a c b := by
      unfold Ζq
      exact le_max_right _ _
    nlinarith
  have hPayT : Ζq H V t c b /
      (((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1) ≤
      Ζl (s + 1) := by
    apply (div_le_iff₀ (by linarith : 0 <
      ((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1)).mpr
    have hnonneg : 0 ≤ Ζq H V t c b := by
      unfold Ζq
      exact le_max_right _ _
    nlinarith
  have hPartB : b ∈ Ζu H V c a t := by
    apply Ζbi.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, t, b} : Edge α) = ({t, b, c} : Edge α) := by
      ext q
      simp [or_comm, or_left_comm]
    exact heq ▸ hTBC'
  have hPartC : b ∈ Ζae H V c a t := by
    apply Ζdf.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, a, b} : Edge α) = ({a, c, b} : Edge α) := by
      ext q
      simp [or_comm, or_left_comm]
    exact heq ▸ hACB
  have hTBXCanon : ({t, x, b} : Edge α) ∈ H := by
    have heq : ({t, x, b} : Edge α) = ({t, b, x} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hTBX'
  have hABXCanon : ({a, x, b} : Edge α) ∈ H := by
    have heq : ({a, x, b} : Edge α) = ({a, b, x} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hABX'
  have hBridgeCAT : ({c, a, t} : Edge α) ∈ H := by
    have heq : ({c, a, t} : Edge α) = ({a, c, t} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hBridge
  have hGain := Ζso
    (H := H) (V := V) (a := c) (b := a) (c := t) (d := b) (x := x)
    (r := s) (s := r)
    hH hUniform hground hac.symm hct hat hBridgeCAT hx hPartB hPartC
    (by
      apply Ζcc.mpr
      exact ⟨hx, hPartB, hTBXCanon⟩)
    (by
      apply Ζcy.mpr
      exact ⟨hx, hPartC, hABXCanon⟩)
    hBookAt hsDegree hrDegree hs hr
  have hMin : min (Ζl (r + 1)) (Ζl (s + 1)) ≤
      Ζax H V ({a, c, t} : Edge α) := by
    have hEdge : ({c, a, t} : Edge α) = ({a, c, t} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    simpa [hEdge, min_comm] using hGain
  exact (min_le_min hPayA hPayT).trans hMin
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
private theorem Ζip
    (H : Family α) (V : Edge α) {z v : α} (hzv : z ≠ v) :
    Ζc H V ({z, v} : Edge α) = Ζe H V z v := by
  ext p
  exact Ζr H V hzv p
theorem Ζkp
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    Ζe H V d.z d.v =
        ({{d.x, d.y}, {d.x, d.u}} : Family α) ∧
      Ζe H V d.y d.u =
        ({{d.x, d.z}, {d.x, d.v}, {d.z, d.v}} : Family α) := by
  obtain ⟨hzv, hxy, hxu, hyu⟩ := Ζag d
  have hq' : q = ({d.z, d.v} : Edge α) := d.hq
  constructor
  · calc
      Ζe H V d.z d.v = Ζc H V ({d.z, d.v} : Edge α) :=
        (Ζip H V hzv).symm
      _ = ({{d.x, d.y}, {d.x, d.u}} : Family α) := by simpa [hq'] using d.hbook
  · calc
      Ζe H V d.y d.u = Ζc H V ({d.y, d.u} : Edge α) :=
        (Ζip H V hyu).symm
      _ = ({{d.x, d.z}, {d.x, d.v}, {d.z, d.v}} : Family α) := by
        simpa [Finset.pair_comm] using d.hreciprocal
theorem Ζps
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q) :
    ({d.z, d.v, d.y} : Edge α) ∈ H ∧
      ({d.z, d.v, d.u} : Edge α) ∈ H := by
  obtain ⟨_, _, _, _⟩ := Ζag d
  have hPages := Ζkp d
  have hPage : ({d.z, d.v} : Edge α) ∈ Ζe H V d.y d.u := by
    rw [hPages.2]
    simp
  obtain ⟨_, _, hy, hu⟩ := Finset.mem_filter.mp hPage
  constructor
  · have heq : ({d.z, d.v} : Edge α) ∪ {d.y} =
        ({d.z, d.v, d.y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hy
  · have heq : ({d.z, d.v} : Edge α) ∪ {d.u} =
        ({d.z, d.v, d.u} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hu
theorem Ζli
    (H : Family α) (V : Edge α) {a c b t : α}
    (N₁ N₂ : Finset α)
    (hSplit : ∀ p ∈ Ζc H V ({b, t} : Edge α),
      p ≠ ({a, c} : Edge α) →
        (∃ u ∈ N₁, p = ({a, u} : Edge α)) ∨
        (∃ u ∈ N₂, p = ({c, u} : Edge α))) :
    (Ζc H V ({b, t} : Edge α)).card ≤ N₁.card + N₂.card + 1 := by
  let S := insert ({a, c} : Edge α)
    ((N₁.image fun u => ({a, u} : Edge α)) ∪
      (N₂.image fun u => ({c, u} : Edge α)))
  have hSub : Ζc H V ({b, t} : Edge α) ⊆ S := by
    intro p hp
    by_cases heq : p = ({a, c} : Edge α)
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · rcases hSplit p hp heq with ⟨u, hu, heq⟩ | ⟨u, hu, heq⟩
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_image.mpr
        exact ⟨u, hu, heq.symm⟩
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        exact ⟨u, hu, heq.symm⟩
  have hCard := Finset.card_le_card hSub
  have hS : S.card ≤ N₁.card + N₂.card + 1 := by
    dsimp [S]
    calc
      (insert ({a, c} : Edge α)
        ((N₁.image fun u => ({a, u} : Edge α)) ∪
          (N₂.image fun u => ({c, u} : Edge α)))).card ≤
        ((N₁.image fun u => ({a, u} : Edge α)) ∪
          (N₂.image fun u => ({c, u} : Edge α))).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (N₁.image fun u => ({a, u} : Edge α)).card +
          (N₂.image fun u => ({c, u} : Edge α)).card + 1 := by
          exact Nat.add_le_add_right
            (Finset.card_union_le
              (N₁.image fun u => ({a, u} : Edge α))
              (N₂.image fun u => ({c, u} : Edge α))) 1
      _ ≤ N₁.card + N₂.card + 1 := by
          exact Nat.add_le_add_right
            (Nat.add_le_add Finset.card_image_le Finset.card_image_le) 1
  exact hCard.trans hS
private theorem Ζct
    {p : Edge α} {u v : α}
    (hp : p.card = 2) (hu : u ∈ p) (hv : v ∈ p) (huv : u ≠ v) :
    p = {u, v} := by
  have hsub : ({u, v} : Edge α) ⊆ p := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqu | hqv
    · exact hqu ▸ hu
    · exact (Finset.mem_singleton.mp hqv) ▸ hv
  have hcard : p.card ≤ ({u, v} : Edge α).card := by
    rw [hp, Finset.card_pair huv]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
theorem Ζkw
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hx : x ∈ Ζn H V c a t) :
    (Ζc H V ({b, t} : Edge α)).card ≤
      Ζf (Ζj H V c a t).ac
        (Ζn H V c a t) b +
      Ζf (Ζj H V c a t).bc
        (Ζu H V c a t) b + 1 := by
  let A := Ζn H V c a t
  let B := Ζu H V c a t
  let C := Ζae H V c a t
  let G := Ζj H V c a t
  have hPageBC : ({b, c} : Edge α) ∈ Ζe H V a t := by
    rw [hBook]; simp
  have hPageBX : ({b, x} : Edge α) ∈ Ζe H V a t := by
    rw [hBook]; simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hPageBX
  have hSrc : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq] at hABC; exact hABC
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq] at hTBX; exact hTBX
  have hbV : b ∈ V := hground _ hSrc (by simp)
  have hcV : c ∈ V := hground _ hSrc (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have haV : a ∈ V := hground _ hBridge (by simp)
  have hCell : ({b, t} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hbt⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqb | hqt
    · exact hqb ▸ hbV
    · exact (Finset.mem_singleton.mp hqt) ▸ htV
  have hCenter : ({a, c} : Edge α) ∈ Ζc H V ({b, t} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hac⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with hqa | hqc
      · exact hqa ▸ haV
      · exact (Finset.mem_singleton.mp hqc) ▸ hcV
    · refine ⟨b, by simp, t, by simp, hbt, ?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro q hqP hqCell
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqP hqCell
        rcases hqP with hqa | hqc <;> rcases hqCell with hqb | hqt
        · exact hab (hqa.symm.trans hqb)
        · exact hat (hqa.symm.trans hqt)
        · exact hbc.symm (hqc.symm.trans hqb)
        · exact hct (hqc.symm.trans hqt)
      · have heq : ({a, c} : Edge α) ∪ {b} = {a, b, c} := by
          ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [heq]; exact hSrc
      · have heq : ({a, c} : Edge α) ∪ {t} = {a, c, t} := by
          ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [heq]; exact hBridge
  have hbB : b ∈ B := by
    change b ∈ Ζu H V c a t
    apply Ζbi.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, t, b} : Edge α) = ({b, c} : Edge α) ∪ {t} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hTBC
  have hbC : b ∈ C := by
    change b ∈ Ζae H V c a t
    apply Ζdf.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, a, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hSrc
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq] at hABX; exact hABX
  have hABedge : (x, b) ∈ G.ab := by
    change (x, b) ∈ (Ζj H V c a t).ab
    apply Ζcc.mpr
    refine ⟨hx, hbB, ?_⟩
    have heq : ({t, b, x} : Edge α) = ({t, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hTBX'
  have hACedge : (x, b) ∈ G.ac := by
    change (x, b) ∈ (Ζj H V c a t).ac
    apply Ζcy.mpr
    refine ⟨hx, hbC, ?_⟩
    have heq : ({a, b, x} : Edge α) = ({a, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hABX'
  let N₁ := A.filter (fun u => (u, b) ∈ G.ac)
  let N₂ := B.filter (fun u => (u, b) ∈ G.bc)
  have hSplit : ∀ p ∈ Ζc H V ({b, t} : Edge α),
      p ≠ ({a, c} : Edge α) →
        (∃ u ∈ N₁, p = ({a, u} : Edge α)) ∨
        (∃ u ∈ N₂, p = ({c, u} : Edge α)) := by
    intro p hp hpNe
    obtain ⟨hpV, hpCert⟩ := Finset.mem_filter.mp hp
    obtain ⟨v₁, hv₁, v₂, hv₂, hvne, hpDisj, hpB, hpT⟩ := hpCert
    have hhit : ¬ Disjoint p ({a, c} : Edge α) :=
      Ζdw hH hCell hp hCenter
    have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpV).2
    have hmeet : a ∈ p ∨ c ∈ p := by
      by_contra h
      apply hhit
      apply Finset.disjoint_left.mpr
      intro q hqp hqac
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqac
      rcases hqac with hqa | hqc
      · exact (not_or.mp h).1 (hqa ▸ hqp)
      · exact (not_or.mp h).2 (hqc ▸ hqp)
    have hPB : p ∪ {b} ∈ H := by
      have hc₁ : v₁ = b ∨ v₁ = t := by simpa using hv₁
      have hc₂ : v₂ = b ∨ v₂ = t := by simpa using hv₂
      rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
      · exact False.elim (hvne rfl)
      · exact hpB
      · exact hpT
      · exact False.elim (hvne rfl)
    have hPT : p ∪ {t} ∈ H := by
      have hc₁ : v₁ = b ∨ v₁ = t := by simpa using hv₁
      have hc₂ : v₂ = b ∨ v₂ = t := by simpa using hv₂
      rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
      · exact False.elim (hvne rfl)
      · exact hpT
      · exact hpB
      · exact False.elim (hvne rfl)
    rcases hmeet with haP | hcP
    · have huNeC : c ∉ p := by
        intro hcP'
        exact hpNe (Ζct hp2 haP hcP' hac)
      have hrest : (p.erase a).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one haP
        omega
      obtain ⟨u, huErase⟩ := hrest
      have hau : a ≠ u := (Finset.mem_erase.mp huErase).1.symm
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpV).1 huP
      have huA : u ∈ A := by
        change u ∈ Ζn H V c a t
        apply Ζcd.mpr
        refine ⟨huV, ?_, Ne.symm hau, ?_, ?_⟩
        · intro he; subst u; exact huNeC huP
        · intro he; subst u; exact (Finset.disjoint_left.mp hpDisj) huP (by simp)
        · have heq : p ∪ {t} = ({a, t, u} : Edge α) := by
            rw [Ζct hp2 haP huP hau]
            ext q; simp [or_comm]
          rw [← heq]; exact hPT
      have huAC : (u, b) ∈ G.ac := by
        change (u, b) ∈ (Ζj H V c a t).ac
        apply Ζcy.mpr
        refine ⟨huA, hbC, ?_⟩
        have heq : p ∪ {b} = ({a, u, b} : Edge α) := by
          rw [Ζct hp2 haP huP hau]
          ext q; simp [or_comm]
        rw [heq] at hPB
        simpa [or_comm, or_left_comm] using hPB
      left
      exact ⟨u, by change u ∈ A.filter (fun u => (u, b) ∈ G.ac); exact Finset.mem_filter.mpr ⟨huA, huAC⟩,
        Ζct hp2 haP huP hau⟩
    · have huNeA : a ∉ p := by
        intro haP'
        exact hpNe (by simpa [Finset.pair_comm] using Ζct hp2 hcP haP' hac.symm)
      have hrest : (p.erase c).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one hcP
        omega
      obtain ⟨u, huErase⟩ := hrest
      have hcu : c ≠ u := (Finset.mem_erase.mp huErase).1.symm
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpV).1 huP
      have huB : u ∈ B := by
        change u ∈ Ζu H V c a t
        apply Ζbi.mpr
        refine ⟨huV, Ne.symm hcu, ?_, ?_, ?_⟩
        · intro he; subst u; exact huNeA huP
        · intro he; subst u
          exact (Finset.disjoint_left.mp hpDisj) huP (by simp)
        · have heq : p ∪ {t} = ({c, t, u} : Edge α) := by
            rw [Ζct hp2 hcP huP hcu]
            ext q; simp [or_comm]
          rw [← heq]; exact hPT
      have huBC : (u, b) ∈ G.bc := by
        change (u, b) ∈ (Ζj H V c a t).bc
        apply Ζhq.mpr
        refine ⟨huB, hbC, ?_⟩
        have heq : p ∪ {b} = ({c, u, b} : Edge α) := by
          rw [Ζct hp2 hcP huP hcu]
          ext q; simp [or_comm]
        rw [heq] at hPB
        simpa [or_comm, or_left_comm] using hPB
      right
      exact ⟨u, by change u ∈ B.filter (fun u => (u, b) ∈ G.bc); exact Finset.mem_filter.mpr ⟨huB, huBC⟩,
        Ζct hp2 hcP huP hcu⟩
  have hCard := Ζli H V N₁ N₂ hSplit
  simpa [N₁, N₂, Ζf, Ζi, A, B, G] using hCard
theorem Ζiq
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : Ζe H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ Ζn H V c a t)
    (hpositive : 0 < Ζo H V a c b) :
    3 ≤ Ζf (Ζj H V c a t).ac
        (Ζn H V c a t) b +
      Ζf (Ζj H V c a t).bc
        (Ζu H V c a t) b := by
  have hAlt := Ζiz hground hab hac hat
    hbc hbt hbx hct hcx htx hBridge hBookAt
  have hPageBC : ({b, c} : Edge α) ∈ Ζe H V a t := by
    rw [hBookAt]; simp
  have hPageBX : ({b, x} : Edge α) ∈ Ζe H V a t := by
    rw [hBookAt]; simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hABC
  have haV : a ∈ V := hground _ hBridge (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have hcV : c ∈ V := hground _ hBridge (by simp)
  have hbV : b ∈ V := by
    have hmem := (Finset.mem_filter.mp hPageBC).1
    exact (Finset.mem_powersetCard.mp hmem).1 (by simp)
  have hxV : x ∈ V := by
    have hmem := (Finset.mem_filter.mp hPageBX).1
    exact (Finset.mem_powersetCard.mp hmem).1 (by simp)
  have hCounts := Ζja hH haV hbV htV hcV hxV
    hab hat hbt hac hax hcx hct.symm htx hBookCx
  have hCardBT := Ζkw
    hH hground hab hac hat hbc hbt hct hBridge hBookAt hx
  have hCommonA : (Ζm H V a b t).card ≤
      Ζf (Ζj H V c a t).ac
        (Ζn H V c a t) b +
      Ζf (Ζj H V c a t).bc
        (Ζu H V c a t) b + 1 := by
    have heq := Ζaq H V haV hab hat hbt
    rw [heq]
    exact (Ζcv H V {b, t} a).trans hCardBT
  have hRoot : ({c, b} : Edge α) ∈ Ζaf H V a := by
    simpa [Finset.pair_comm] using Ζat H V hPageBC
  have hWeight := Ζej
    H V hRoot hbc.symm hAlt.2.1 hAlt.1 hCounts.1 hCommonA
  let D := Ζf (Ζj H V c a t).ac
        (Ζn H V c a t) b +
      Ζf (Ζj H V c a t).bc
        (Ζu H V c a t) b
  have hWeightD : Ζo H V a c b ≤ Ζg (D + 1) := by
    dsimp [D] at hWeight ⊢
    exact hWeight
  have hFractionPos : 0 < Ζg (D + 1) := lt_of_lt_of_le hpositive hWeightD
  by_contra hD
  have hSmall : D + 1 ≤ 3 := by omega
  rw [Ζdk hSmall] at hFractionPos
  norm_num at hFractionPos
theorem Ζep
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : Ζe H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ Ζn H V c a t)
    (hpositive : 0 < Ζo H V a c b) :
    2 ≤ Ζf (Ζj H V c a t).ac
      ((Ζn H V c a t).erase x) b := by
  let A := Ζn H V c a t
  let B := Ζu H V c a t
  let C := Ζae H V c a t
  let G := Ζj H V c a t
  have hTotal := Ζiq
    hH hground hab hac hat hbc hbt hbx hct hcx htx hax hBridge
    hBookAt hBookCx hx hpositive
  have hPageBC : ({b, c} : Edge α) ∈ Ζe H V a t := by
    rw [hBookAt]; simp
  have hPageBX : ({b, x} : Edge α) ∈ Ζe H V a t := by
    rw [hBookAt]; simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hPageBX
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hABC
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hTBX
  have hbV : b ∈ V := hground _ hABC' (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have haV : a ∈ V := hground _ hBridge (by simp)
  have hbB : b ∈ B := by
    apply Ζbi.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, t, b} : Edge α) = ({b, c} : Edge α) ∪ {t} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hTBC
  have hbC : b ∈ C := by
    apply Ζdf.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, a, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hABC'
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hABX
  have hABedge : (x, b) ∈ G.ab := by
    apply Ζcc.mpr
    refine ⟨hx, hbB, ?_⟩
    have heq : ({t, b, x} : Edge α) = ({t, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hTBX'
  have hACedge : (x, b) ∈ G.ac := by
    apply Ζcy.mpr
    refine ⟨hx, hbC, ?_⟩
    have heq : ({a, b, x} : Edge α) = ({a, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hABX'
  have hMixed : Ζz G A B C :=
    Ζdc hH hUniform hac.symm hct hat
  have hABpos : 0 < Ζi G.ab B x :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbB, hABedge⟩⟩
  have hACposX : 0 < Ζi G.ac C x :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbC, hACedge⟩⟩
  have hACone : C.filter (fun z => (x, z) ∈ G.ac) = {b} := by
    have hCard : (C.filter (fun z => (x, z) ∈ G.ac)).card = 1 :=
      (hMixed.1 x hx hABpos hACposX).2
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hCard
    have hbmem : b ∈ C.filter (fun z => (x, z) ∈ G.ac) :=
      Finset.mem_filter.mpr ⟨hbC, hACedge⟩
    rw [hz] at hbmem
    have hbz : b = z := by simpa using hbmem
    simpa [hbz] using hz
  have hACpos : 0 < Ζf G.ac A b := by
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hACedge⟩⟩
  have hBCzero : Ζf G.bc B b = 0 := by
    by_contra hzero
    have hBCpos : 0 < Ζf G.bc B b := Nat.pos_of_ne_zero hzero
    have hOne := hMixed.2.2 b hbC hACpos hBCpos
    rcases hOne with ⟨hAConeB, hBConeB⟩
    rw [hAConeB, hBConeB] at hTotal
    omega
  have hACgeThree : 3 ≤ Ζf G.ac A b := by
    rw [hBCzero] at hTotal
    exact hTotal
  have hACerase : Ζf G.ac A b =
      Ζf G.ac (A.erase x) b + 1 :=
    Ζbw G.ac A C x b hx hACone
  rw [hACerase] at hACgeThree
  change 3 ≤ Ζf G.ac (A.erase x) b + 1 at hACgeThree
  change 2 ≤ Ζf G.ac (A.erase x) b
  omega
private theorem Ζje
    (H : Family α) (V : Edge α) (a c t : α) :
    Ζn H V c t a = Ζn H V c a t := by
  rw [Ζap,
    Ζap]
  simp [Finset.pair_comm]
private theorem Ζue
    (H : Family α) (V : Edge α) (a c t : α) :
    Ζae H V c t a = Ζu H V c a t := by
  rw [Ζcg,
    Ζbd]
private theorem Ζtr
    (H : Family α) (V : Edge α) (a c t : α) :
    (Ζj H V c t a).ac =
      (Ζj H V c a t).ab := by
  ext e
  rcases e with ⟨u, v⟩
  rw [Ζcy, Ζcc,
    Ζje H V a c t,
    Ζue H V a c t]
private theorem Ζkd
    (H : Family α) (V : Edge α) {a t : α} :
    Ζe H V t a = Ζe H V a t := by
  unfold Ζe
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpV, hpDisj, hpt, hpa⟩
    refine ⟨hpV, ?_, hpa, hpt⟩
    simpa only [Finset.pair_comm] using hpDisj
  · rintro ⟨hpV, hpDisj, hpa, hpt⟩
    refine ⟨hpV, ?_, hpt, hpa⟩
    simpa only [Finset.pair_comm] using hpDisj
theorem Ζir
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : Ζe H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ Ζn H V c a t)
    (hpositiveA : 0 < Ζo H V a c b)
    (hpositiveT : 0 < Ζo H V t c b) :
    2 ≤ Ζf (Ζj H V c a t).ac
        ((Ζn H V c a t).erase x) b ∧
      2 ≤ Ζf (Ζj H V c a t).ab
        ((Ζn H V c a t).erase x) b := by
  have hA := Ζep
    hH hUniform hground hab hac hat hbc hbt hbx hct hcx htx hax hBridge
    hBookAt hBookCx hx hpositiveA
  have hBookSwap : Ζe H V t a =
      ({{b, c}, {b, x}} : Family α) := by
    rw [Ζkd H V, hBookAt]
  have hBridgeSwap : ({t, c, a} : Edge α) ∈ H := by
    have heq : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
      ext q; simp [or_comm, or_left_comm]
    exact heq ▸ hBridge
  have hxSwap : x ∈ Ζn H V c t a := by
    rw [Ζje H V a c t]
    exact hx
  have hBookCxSwap : Ζe H V c x =
      ({{t, b}, {t, a}, {b, a}} : Family α) := by
    rw [hBookCx]
    ext p
    simp [Finset.pair_comm]
    tauto
  have hT := Ζep
    (H := H) (V := V) (a := t) (t := a) (b := b) (c := c) (x := x)
    hH hUniform hground hbt.symm hct.symm hat.symm hbc hab.symm hbx
    hac.symm hcx hax htx hBridgeSwap hBookSwap hBookCxSwap hxSwap hpositiveT
  constructor
  · exact hA
  · simpa [Ζtr H V a c t,
      Ζje H V a c t] using hT
theorem Ζjq
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : Ζe H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : Ζe H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ Ζn H V c a t)
    (hpositiveA : 0 < Ζo H V a c b)
    (hpositiveT : 0 < Ζo H V t c b) :
    min
      (Ζq H V a c b /
        (((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1))
      (Ζq H V t c b /
        (((Ζb H V ({b, c} : Edge α)).card : ℚ) - 1))
      ≤ Ζax H V ({a, c, t} : Edge α) := by
  have hdeg := Ζir
    hH hUniform hground hab hac hat hbc hbt hbx hct hcx htx hax hBridge
    hBookAt hBookCx hx hpositiveA hpositiveT
  let r := Ζf (Ζj H V c a t).ac
      ((Ζn H V c a t).erase x) b
  let s := Ζf (Ζj H V c a t).ab
      ((Ζn H V c a t).erase x) b
  have hr : 2 ≤ r := by exact hdeg.1
  have hs : 2 ≤ s := by exact hdeg.2
  have hPaid := Ζsp hH hUniform hground
    hab hac hat hbc hbt hbx hct hcx htx hax hBridge hBookAt hBookCx hx
    (by rfl) (by rfl) hr hs
  exact hPaid
theorem Ζjb
    {H : Family α} {V q : Edge α}
    (d : Ζt H V q)
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hpositiveZ : 0 < Ζo H V d.z d.x d.y)
    (hpositiveV : 0 < Ζo H V d.v d.x d.y) :
    min (Ζh H V d.z d.x d.y d.v)
      (Ζh H V d.v d.x d.y d.z) ≤
      Ζax H V ({d.z, d.v, d.y} : Edge α) := by
  obtain ⟨hzv, hxy, hxu, hyu⟩ := Ζag d
  obtain ⟨_, hzx, hzy, hzu, hvx, hvy, hvu, _, _, _⟩ :=
    Ζan d
  have hPages := Ζkp d
  have hBridgePair := Ζps d
  have hBridge := hBridgePair.1
  have hBridgeX := hBridgePair.2
  have hxA : d.u ∈ Ζn H V d.y d.z d.v := by
    apply Ζcd.mpr
    refine ⟨d.huV, ?_, ?_, ?_, hBridgeX⟩
    · exact hyu.symm
    · exact hzu.symm
    · exact hvu.symm
  have hBookAt := hPages.1
  have hBookCx := hPages.2
  have hBridgeY : ({d.z, d.y, d.v} : Edge α) ∈ H := by
    have heq : ({d.z, d.y, d.v} : Edge α) =
        ({d.z, d.v, d.y} : Edge α) := by
      ext q
      simp [or_comm]
    exact heq ▸ hBridge
  have hBookCx' : Ζe H V d.y d.u =
      ({{d.z, d.x}, {d.z, d.v}, {d.x, d.v}} : Family α) := by
    rw [hBookCx]
    ext p
    simp [Finset.pair_comm]
  have hPay := Ζjq
    (H := H) (V := V) (a := d.z) (t := d.v) (b := d.x) (c := d.y) (x := d.u)
    hH hUniform hground hzx hzy hzv hxy hvx.symm hxu
    hvy.symm hyu hvu hzu hBridgeY hBookAt hBookCx' hxA
    (by simpa [Ζfk] using hpositiveZ)
    (by simpa [Ζfk] using hpositiveV)
  have hRootZ : ({d.x, d.y} : Edge α) ∈ Ζaf H V d.z := by
    have hp : ({d.x, d.y} : Edge α) ∈ Ζe H V d.z d.v := by
      rw [hBookAt]; simp
    exact Ζat H V hp
  have hBookSwap : Ζe H V d.v d.z =
      Ζe H V d.z d.v := Ζkd H V
  have hRootV : ({d.x, d.y} : Edge α) ∈ Ζaf H V d.v := by
    have hp : ({d.x, d.y} : Edge α) ∈ Ζe H V d.v d.z := by
      rw [hBookSwap, hBookAt]; simp
    exact Ζat H V hp
  have hzComp : d.z ∈ Ζb H V ({d.x, d.y} : Edge α) :=
    Ζv H V d.hzV hRootZ
  have hvComp : d.v ∈ Ζb H V ({d.x, d.y} : Edge α) :=
    Ζv H V d.hvV hRootV
  have hvErase : d.v ∈
      (Ζb H V ({d.x, d.y} : Edge α)).erase d.z :=
    Finset.mem_erase.mpr ⟨hzv.symm, hvComp⟩
  have hzErase : d.z ∈
      (Ζb H V ({d.x, d.y} : Edge α)).erase d.v :=
    Finset.mem_erase.mpr ⟨hzv, hzComp⟩
  have hChargeZ : Ζh H V d.z d.x d.y d.v =
      Ζq H V d.z d.x d.y /
        (((Ζb H V ({d.x, d.y} : Edge α)).card : ℚ) - 1) := by
    simp [Ζh, hvErase, Ζao]
  have hChargeV : Ζh H V d.v d.x d.y d.z =
      Ζq H V d.v d.x d.y /
        (((Ζb H V ({d.x, d.y} : Edge α)).card : ℚ) - 1) := by
    simp [Ζh, hzErase, Ζao]
  rw [hChargeZ, hChargeV]
  rw [Ζin H V d.z d.x d.y,
    Ζin H V d.v d.x d.y]
  have hEdge : ({d.z, d.y, d.v} : Edge α) =
      ({d.z, d.v, d.y} : Edge α) := by
    ext q
    simp [or_comm]
  rw [hEdge] at hPay
  exact hPay
theorem Ζke
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ F ∈ H, F ⊆ V) (_hE : E ∈ H)
    (hDemand : 0 < Ζx H V q E) :
    Ζx H V q E ≤ Ζax H V E := by
  classical
  by_cases hq : Ζad H V q
  · let d := Ζah H V q hq
    have hFormula : Ζx H V q E =
        if E = ({d.z, d.v, d.y} : Edge α) then
          min (Ζh H V d.z d.x d.y d.v)
            (Ζh H V d.v d.x d.y d.z)
        else if E = ({d.z, d.v, d.u} : Edge α) then
          min (Ζh H V d.z d.x d.u d.v)
            (Ζh H V d.v d.x d.u d.z)
        else 0 := by
      simp [Ζx, hq, d]
    by_cases hEy : E = ({d.z, d.v, d.y} : Edge α)
    · have hMinPos : 0 < min
          (Ζh H V d.z d.x d.y d.v)
          (Ζh H V d.v d.x d.y d.z) := by
        rw [hFormula, Ζie hEy] at hDemand
        exact hDemand
      have hsrcZ : 0 < Ζo H V d.z d.x d.y :=
        Ζbl H V _ _ _ _ (lt_min_iff.mp hMinPos).1
      have hsrcV : 0 < Ζo H V d.v d.x d.y :=
        Ζbl H V _ _ _ _ (lt_min_iff.mp hMinPos).2
      have hPaid := Ζjb d hH hUniform hground
        hsrcZ hsrcV
      have hEdge : ({d.z, d.v, d.y} : Edge α) = E := hEy.symm
      rw [hFormula, Ζie hEy, ← hEdge]
      exact hPaid
    · by_cases hEu : E = ({d.z, d.v, d.u} : Edge α)
      · have hMinPos : 0 < min
            (Ζh H V d.z d.x d.u d.v)
            (Ζh H V d.v d.x d.u d.z) := by
          rw [hFormula, Ζdp hEy, Ζie hEu] at hDemand
          exact hDemand
        let d' := Ζby d
        have hsrcZ : 0 < Ζo H V d'.z d'.x d'.y := by
          simpa [d', Ζby] using
            Ζbl H V d.z d.x d.u d.v
              (lt_min_iff.mp hMinPos).1
        have hsrcV : 0 < Ζo H V d'.v d'.x d'.y := by
          simpa [d', Ζby] using
            Ζbl H V d.v d.x d.u d.z
              (lt_min_iff.mp hMinPos).2
        have hPaid := Ζjb d' hH hUniform hground
          hsrcZ hsrcV
        have hDemandEq : Ζx H V q E =
            min (Ζh H V d'.z d'.x d'.y d'.v)
              (Ζh H V d'.v d'.x d'.y d'.z) := by
          rw [hFormula, Ζdp hEy, Ζie hEu]
          simp [d', Ζby]
        have hEdge : ({d'.z, d'.v, d'.y} : Edge α) = E := by
          simpa [d', Ζby] using hEu.symm
        rw [hDemandEq, ← hEdge]
        exact hPaid
      · rw [hFormula, Ζdp hEy, Ζdp hEu] at hDemand
        norm_num at hDemand
  · simp [Ζx, hq] at hDemand
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
theorem Ζkf
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hFree : ∀ A : Edge α, A ⊆ V → ¬ Ζar H A) :
    Ζih H := by
  intro S hScard
  let B := Ζfq H S
  have hBound : B.card ≤ 8 := by
    by_cases hSV : S ⊆ V
    · have hNot := hFree S hSV
      have hNotDense : ¬ 9 ≤ B.card := by
        intro hDense
        exact hNot ⟨hScard, hDense⟩
      omega
    · have hOut : (S \ V).Nonempty := by
        by_contra h
        exact hSV (Finset.sdiff_eq_empty_iff_subset.mp
          (Finset.not_nonempty_iff_eq_empty.mp h))
      obtain ⟨x, hxOut⟩ := hOut
      have hxS : x ∈ S := (Finset.mem_sdiff.mp hxOut).1
      have hxV : x ∉ V := (Finset.mem_sdiff.mp hxOut).2
      have hEraseCard : (S.erase x).card = 4 := by
        have hCard := Finset.card_erase_add_one hxS
        omega
      have hSub : B ⊆ (S.erase x).powersetCard 3 := by
        intro E hEB
        obtain ⟨hEH, hES⟩ := Finset.mem_filter.mp hEB
        have hxE : x ∉ E := fun h => hxV (hGround E hEH h)
        apply Finset.mem_powersetCard.mpr
        constructor
        · intro y hy
          exact Finset.mem_erase.mpr
            ⟨fun h => hxE (h ▸ hy), hES hy⟩
        · exact hU hEH
      have hCard := Finset.card_le_card hSub
      rw [Finset.card_powersetCard, hEraseCard] at hCard
      norm_num at hCard
      omega
  change B.card ≠ 9 ∧ B.card ≠ 10
  omega
end JSP523.Rank3
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
theorem Ζnh
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V)
    (hFree : ∀ A : Edge α, A ⊆ V → ¬ Ζar H A) :
    Ζgr H V ≤ ∑ E ∈ H, Ζax H V E := by
  have hNoBlock := Ζkf
    H V hU hGround hFree
  apply Ζii
    H V hAdm hU hGround
  · intro E hE q₁ hq₁ q₂ hq₂ hpos₁ hpos₂
    exact Ζte hAdm hU hNoBlock
      E hE q₁ q₂ hq₁ hq₂ hpos₁ hpos₂
  · intro E hE q hq hpos
    exact Ζke
      H V q E hAdm hU hGround hE hpos
theorem Ζsb
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    2 * H.card ≤ (Ζbp H V).card + (Ζac H V).card := by
  apply Ζqn H V hU hAdm hGround
  intro K hUK hAdmK hGroundK hFreeK
  have hIncoming := Ζqh K V hAdmK
  have hCapacity := Ζlm
    K V hUK hGroundK hIncoming
  have hPaid := Ζnh
    K V hUK hAdmK hGroundK hFreeK
  exact Ζlf
    K V (Ζgr K V) hUK hAdmK hGroundK hCapacity hPaid
theorem Ζni
    (H : Family α) (V : Edge α) :
    (Ζbp H V).card + (Ζac H V).card ≤
      2 * V.card.choose 2 := by
  have hPairs := Finset.card_le_card (Ζhj H V)
  have hCells := Finset.card_le_card (Ζbr H V)
  rw [Finset.card_powersetCard] at hPairs hCells
  omega
theorem Ζuf
    (H : Family α) (V : Edge α)
    (hU : Uniform 3 H) (hAdm : Admissible H)
    (hGround : ∀ E ∈ H, E ⊆ V) :
    2 * H.card ≤ (Ζbp H V).card + (Ζac H V).card ∧
    (Ζbp H V).card + (Ζac H V).card ≤
      2 * V.card.choose 2 ∧
    H.card ≤ V.card.choose 2 := by
  have hFirst := Ζsb H V hU hAdm hGround
  have hSecond := Ζni H V
  exact ⟨hFirst, hSecond, by omega⟩
end JSP523.Rank3
end
section
namespace JSP523
variable {α : Type*} [DecidableEq α]
end JSP523
end
section
namespace JSP523.Rank3
variable {α : Type*} [DecidableEq α]
end JSP523.Rank3
end

theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R1.H1 := by
  intro n
  unfold Hypergraph.extremalNumber
  refine Finset.sup_le fun H hH => ?_
  obtain ⟨hsub, hfree⟩ := (@Finset.mem_filter _ (fun H : Finset (Finset (Fin n)) => ¬ H.HasRepeatedDisjointUnion)
    (fun _ => Classical.propDecidable _) _ _).mp hH
  rw [Finset.mem_powerset] at hsub
  have hUniform : JSP523.Uniform 3 H := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hsub hE)).2
  have hGround : ∀ E ∈ H, E ⊆ (Finset.univ : Finset (Fin n)) := fun E _ => Finset.subset_univ E
  have hAdm : JSP523.Admissible H := by
    intro A B C D hA hB hC hD hq
    exact hfree ⟨A, hA, B, hB, C, hC, D, hD, hq.disjAB, hq.disjCD, hq.sameUnion,
      hq.distinct.ab, hq.distinct.cd, hq.distinct.ac, hq.distinct.ad, hq.distinct.bc,
      hq.distinct.bd⟩
  have h := (JSP523.Rank3.Ζuf H (Finset.univ : Finset (Fin n))
    hUniform hAdm hGround).2.2
  simpa using h
