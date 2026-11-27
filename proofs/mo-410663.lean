import OMAStatements.S_mo_410663
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MatchingCount
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
abbrev K33 := completeBipartiteGraph (Fin 3) (Fin 3)

theorem contains_of_triples (A B : Finset V) (ha : A.card = 3) (hb : B.card = 3)
    (edges : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : SimpleGraph.IsContained K33 G := by
  classical
  let l := (Finset.equivFinOfCardEq ha).symm
  let r := (Finset.equivFinOfCardEq hb).symm
  let f : Fin 3 ⊕ Fin 3 → V := Sum.elim (fun i => (l i).val) (fun i => (r i).val)
  have cross (i j : Fin 3) : G.Adj (l i).val (r j).val :=
    edges _ (l i).property _ (r j).property
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro x y h
    cases x with
    | inl x => cases y with
      | inl y => simp [completeBipartiteGraph] at h
      | inr y => exact cross x y
    | inr x => cases y with
      | inl y => exact (cross y x).symm
      | inr y => simp [completeBipartiteGraph] at h
  · intro x y h
    cases x with
    | inl x => cases y with
      | inl y => exact congrArg Sum.inl (l.injective (Subtype.ext h))
      | inr y => exact False.elim ((cross x y).ne h)
    | inr x => cases y with
      | inl y => exact False.elim ((cross y x).ne h.symm)
      | inr y => exact congrArg Sum.inr (r.injective (Subtype.ext h))

noncomputable def neighbors (S : Finset V) (v : V) : Finset V := by
  classical exact S.filter (G.Adj v)

theorem small_degree (hG : ¬ SimpleGraph.IsContained K33 G) (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, (neighbors G S v).card ^ 3 ≤ 16*S.card^2 := by
  classical
  obtain ⟨v,hv,hmin⟩ := S.exists_min_image (fun x => (neighbors G S x).card) hS
  refine ⟨v,hv,?_⟩
  let d := (neighbors G S v).card
  let R := fun (x : V) (T : Finset V) => T ⊆ neighbors G S x
  have lo (x) (hx : x ∈ S) : d.choose 3 ≤ ((S.powersetCard 3).bipartiteAbove R x).card := by
    apply (Nat.choose_le_choose 3 (hmin x hx)).trans
    rw [← Finset.card_powersetCard]
    apply Finset.card_le_card
    intro T hT
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨fun x hx => (Finset.mem_filter.mp (hsub hx)).1,hcard⟩, hsub⟩
  have hi (T) (hT : T ∈ S.powersetCard 3) : (S.bipartiteBelow R T).card ≤ 2 := by
    by_contra! h
    obtain ⟨B,hB,hcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ _ from h)
    apply hG
    apply contains_of_triples G B T hcard (Finset.mem_powersetCard.mp hT).2
    intro b hb a ha
    exact (Finset.mem_filter.mp ((Finset.mem_filter.mp (hB hb)).2 ha)).2
  have count := Finset.card_nsmul_le_card_nsmul R lo hi
  rw [Finset.card_powersetCard, nsmul_eq_mul, nsmul_eq_mul] at count
  have upper : 6 * S.card.choose 3 ≤ S.card^3 := by
    change (Nat.factorial 3) * S.card.choose 3 ≤ _
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have hc : S.card * (6 * d.choose 3) ≤ S.card * (2*S.card^2) := by
    nlinarith only [Nat.mul_le_mul_left 6 count, Nat.mul_le_mul_left 2 upper]
  have hd := Nat.le_of_mul_le_mul_left hc hS.card_pos
  change d^3 ≤ _
  by_cases h : d < 3
  · have hp := hS.card_pos
    have h1 : 1 ≤ S.card^2 := Nat.one_le_pow _ _ hp
    have h2 := Nat.pow_le_pow_left (show d ≤ 2 by omega) 3
    omega
  · obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le (show 3 ≤ d by omega)
    have he : 6 * d.choose 3 = (a+1)*(a+2)*(a+3) := by
      change (Nat.factorial 3) * d.choose 3 = _
      rw [← Nat.descFactorial_eq_factorial_mul_choose, ha, Nat.add_comm 3 a]
      simp [Nat.descFactorial]; ring
    rw [he] at hd
    rw [ha]
    nlinarith [Nat.mul_le_mul_left 8 hd]

abbrev Perfect := {M : G.Subgraph // M.IsPerfectMatching}

noncomputable def mate (M : Perfect G) (v : V) : V :=
  (SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property v).choose

theorem mate_adj (M : Perfect G) (v : V) : M.val.Adj v (mate G M v) :=
  (SimpleGraph.Subgraph.isPerfectMatching_iff.mp M.property v).choose_spec.1

theorem mate_iff (M : Perfect G) (v w : V) : M.val.Adj v w ↔ mate G M v = w := by
  constructor
  · exact M.property.1.eq_of_adj_left (mate_adj G M v)
  · rintro rfl
    exact mate_adj G M v

theorem mate_inv (M : Perfect G) (v : V) : mate G M (mate G M v) = v :=
  (mate_iff G M _ _).mp (mate_adj G M v).symm

theorem mate_ext (M N : Perfect G) (h : ∀ v, mate G M v = mate G N v) : M = N := by
  apply Subtype.ext
  apply SimpleGraph.Subgraph.ext
  · rw [M.property.2.verts_eq_univ, N.property.2.verts_eq_univ]
  · exact funext₂ fun v w => propext (by rw [mate_iff, mate_iff, h v])

theorem family_bound (hG : ¬ SimpleGraph.IsContained K33 G) (n : ℕ)
    (S : Finset V) (F : Finset (Perfect G)) (hs : S.card = 2*n)
    (closed : ∀ M ∈ F, ∀ v ∈ S, mate G M v ∈ S)
    (agree : ∀ M ∈ F, ∀ N ∈ F, ∀ v ∉ S, mate G M v = mate G N v) :
    F.card^3 ≤ (64*n^2)^n := by
  classical
  induction n generalizing S F with
  | zero =>
    have he : S = ∅ := Finset.card_eq_zero.mp (by simpa using hs)
    have h1 : F.card ≤ 1 := Finset.card_le_one.mpr (fun M hm N hn =>
      mate_ext G M N (fun x => agree M hm N hn x (by simp [he])))
    simpa using Nat.pow_le_pow_left h1 3
  | succ n ih =>
    by_cases hF : F.Nonempty
    · obtain ⟨v,hv,hd⟩ := small_degree G hG S (Finset.card_pos.mp (by omega))
      let D := neighbors G S v
      let fiber := fun w => F.filter (fun M => mate G M v = w)
      have lands (M) (hm : M ∈ F) : mate G M v ∈ D :=
        Finset.mem_filter.mpr ⟨closed M hm v hv, M.val.adj_sub (mate_adj G M v)⟩
      obtain ⟨M₀,h₀⟩ := hF
      obtain ⟨w,hw,hmax⟩ := D.exists_max_image (fun y => (fiber y).card) ⟨_,lands M₀ h₀⟩
      have hcard := Finset.card_le_mul_card_image_of_maps_to lands _ hmax
      have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
      have hvw : v ≠ w := (show G.Adj v w from (Finset.mem_filter.mp hw).2).ne
      let S' := (S.erase v).erase w
      have hs' : S'.card = 2*n := by
        dsimp [S']
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvw.symm,hwS⟩),Finset.card_erase_of_mem hv]
        omega
      have at_w (M) (hm : M ∈ fiber w) : mate G M w = v := by
        rw [← (Finset.mem_filter.mp hm).2, mate_inv]
      have cl (M) (hm : M ∈ fiber w) (x) (hx : x ∈ S') : mate G M x ∈ S' := by
        obtain ⟨hxw,hxv,hxs⟩ := (show x ≠ w ∧ x ≠ v ∧ x ∈ S by simpa [S'] using hx)
        have back : mate G M (mate G M x) = x := mate_inv G M x
        have atv := (Finset.mem_filter.mp hm).2
        simp only [S', Finset.mem_erase]
        refine ⟨fun h => hxv ?_, fun h => hxw ?_, closed M (Finset.mem_filter.mp hm).1 x hxs⟩
        · rw [h, at_w M hm] at back
          exact back.symm
        · rw [h, atv] at back
          exact back.symm
      have ag (M) (hm : M ∈ fiber w) (N) (hn : N ∈ fiber w) (x) (hx : x ∉ S') :
          mate G M x = mate G N x := by
        by_cases hxv : x = v
        · subst x
          exact (Finset.mem_filter.mp hm).2.trans (Finset.mem_filter.mp hn).2.symm
        by_cases hxw : x = w
        · subst x
          rw [at_w M hm, at_w N hn]
        · exact agree M (Finset.mem_filter.mp hm).1 N (Finset.mem_filter.mp hn).1 x
            (fun h => hx (Finset.mem_erase.mpr ⟨hxw,Finset.mem_erase.mpr ⟨hxv,h⟩⟩))
      have tail := ih S' (fiber w) hs' cl ag
      have degree : D.card^3 ≤ 64*(n+1)^2 := by
        rw [hs] at hd
        nlinarith only [hd]
      have grow : (64*n^2)^n ≤ (64*(n+1)^2)^n :=
        Nat.pow_le_pow_left (by nlinarith) n
      calc
        F.card^3 ≤ ((fiber w).card * D.card)^3 := Nat.pow_le_pow_left hcard 3
        _ = (fiber w).card^3 * D.card^3 := mul_pow _ _ _
        _ ≤ (64*(n+1)^2)^n * (64*(n+1)^2) := Nat.mul_le_mul (tail.trans grow) degree
        _ = _ := (pow_succ _ _).symm
    · simp [Finset.not_nonempty_iff_eq_empty.mp hF]

theorem uniform_upper : ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin (2 * n))),
    ¬ SimpleGraph.IsContained (completeBipartiteGraph (Fin 3) (Fin 3)) G →
    (Set.ncard {M : G.Subgraph | M.IsPerfectMatching}) ^ 3 ≤ (C * n ^ 2) ^ n := by
  classical
  refine ⟨64, by decide, ?_⟩
  intro n G hG
  let : Fintype (Perfect G) := Fintype.ofFinite _
  have h := family_bound G hG n Finset.univ Finset.univ
    (by simp) (by simp) (by simp)
  change (Nat.card (Perfect G))^3 ≤ _
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using h
end MatchingCount

theorem OMA.solution : type_of% @OMA.S_mo_410663.main := by
  exact MatchingCount.uniform_upper
